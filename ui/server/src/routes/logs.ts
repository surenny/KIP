import fs from 'fs';
import path from 'path';
import type { FastifyInstance } from 'fastify';
import type { ProjectPaths } from '../index.js';
import { parseJsonl } from '../utils.js';

interface LogFileEntry { name: string; path: string; size: number; modified: string; agent?: string; runId?: string }
interface LogGroup { id: string; agent: string; files: LogFileEntry[]; meta?: Record<string, unknown> }

function resolveLogPath(agentsPath: string, logPath: string): string | null {
  const normalized = path.normalize(logPath).replace(/^(\.\.[/\\])+/, '');
  const full = path.join(agentsPath, normalized);
  if (!full.startsWith(agentsPath)) return null;
  if (!full.endsWith('.jsonl')) return full + '.jsonl';
  return full;
}

export function register(fastify: FastifyInstance, paths: ProjectPaths) {
  const { agentsPath } = paths;

  fastify.get('/api/logs', async () => {
    if (!fs.existsSync(agentsPath)) return { flat: [], groups: [] };

    const groups: LogGroup[] = [];

    const agentDirs = fs.readdirSync(agentsPath)
      .filter(d => {
        const logsDir = path.join(agentsPath, d, 'logs');
        return fs.existsSync(logsDir) && fs.statSync(logsDir).isDirectory();
      })
      .sort();

    for (const agentName of agentDirs) {
      const logsDir = path.join(agentsPath, agentName, 'logs');
      const runDirs = fs.readdirSync(logsDir)
        .filter(d => d.startsWith('run-') && fs.statSync(path.join(logsDir, d)).isDirectory())
        .sort();

      for (const runId of runDirs) {
        const runDir = path.join(logsDir, runId);
        const files: LogFileEntry[] = [];

        for (const f of fs.readdirSync(runDir)
          .filter(f => f.endsWith('.jsonl') && !f.endsWith('.raw.jsonl'))) {
          const full = path.join(runDir, f);
          if (!fs.statSync(full).isFile()) continue;
          const stat = fs.statSync(full);
          files.push({
            name: f,
            path: `${agentName}/logs/${runId}/${f}`,
            size: stat.size,
            modified: stat.mtime.toISOString(),
            agent: agentName,
            runId,
          });
        }

        let meta: Record<string, unknown> | undefined;
        const metaFile = path.join(runDir, 'meta.json');
        try { meta = JSON.parse(fs.readFileSync(metaFile, 'utf-8')); } catch { /* skip */ }

        groups.push({ id: `${agentName}/${runId}`, agent: agentName, files, meta });
      }
    }

    return { flat: [], groups: groups.reverse() };
  });

  fastify.get('/api/logs/*', async (req, reply) => {
    const subpath = (req.params as Record<string, string>)['*'];
    if (!subpath) return reply.status(400).send({ error: 'Missing path' });
    const filePath = resolveLogPath(agentsPath, subpath);
    if (!filePath || !fs.existsSync(filePath)) return reply.status(404).send({ error: 'Not found' });
    return parseJsonl(filePath);
  });

  fastify.get('/api/log-stream/*', { websocket: true }, (socket, req) => {
    const subpath = (req.params as Record<string, string>)['*'] || '';
    const filePath = resolveLogPath(agentsPath, subpath);
    if (!filePath || !fs.existsSync(filePath)) {
      socket.send(JSON.stringify({ type: 'error', message: 'Not found' }));
      socket.close();
      return;
    }

    let lastSize = fs.statSync(filePath).size;
    socket.send(JSON.stringify({ type: 'ready', size: lastSize }));

    const watcher = fs.watch(filePath, () => {
      try {
        const newSize = fs.statSync(filePath).size;
        if (newSize <= lastSize) return;
        const stream = fs.createReadStream(filePath, { start: lastSize, end: newSize - 1, encoding: 'utf-8' });
        let buffer = '';
        stream.on('data', (chunk) => {
          buffer += chunk;
          const lines = buffer.split('\n');
          buffer = lines.pop() || '';
          for (const line of lines) {
            if (line.trim()) try { socket.send(line); } catch { /* ignore */ }
          }
        });
        stream.on('end', () => {
          if (buffer.trim()) try { socket.send(buffer); } catch { /* ignore */ }
        });
        lastSize = newSize;
      } catch { /* ignore stat errors during write */ }
    });

    socket.on('close', () => watcher.close());
  });
}
