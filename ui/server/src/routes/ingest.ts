import fs from 'fs';
import path from 'path';
import type { FastifyInstance } from 'fastify';
import type { ProjectPaths } from '../index.js';

const TOKEN = process.env.KIP_INGEST_TOKEN ?? '';

// agent name and runId must be safe path segments
function safeSeg(s: unknown): s is string {
  return typeof s === 'string' && /^[\w.\-:]+$/.test(s) && !s.includes('..');
}

export function register(fastify: FastifyInstance, paths: ProjectPaths) {
  fastify.post('/api/ingest', async (req, reply) => {
    if (TOKEN) {
      const auth = (req.headers.authorization ?? '') as string;
      if (auth !== `Bearer ${TOKEN}`) {
        return reply.code(401).send({ error: 'unauthorized' });
      }
    }

    const { agent, runId, hintFile, row } = req.body as Record<string, unknown>;

    if (!safeSeg(agent) || !safeSeg(runId)) {
      return reply.code(400).send({ error: 'invalid agent or runId' });
    }

    const runDir = path.resolve(paths.agentsPath, agent, 'logs', runId);
    if (!runDir.startsWith(paths.agentsPath + path.sep)) {
      return reply.code(400).send({ error: 'path outside agents directory' });
    }

    fs.mkdirSync(runDir, { recursive: true });

    const metaFile = path.join(runDir, 'meta.json');
    const jsonlFile = path.join(runDir, 'absorber.jsonl');

    // Write meta.json on the first event for this run
    if (!fs.existsSync(metaFile)) {
      const meta = {
        agent,
        hint_file: typeof hintFile === 'string' ? hintFile : null,
        startedAt: (row as Record<string, unknown>)?.ts ?? new Date().toISOString(),
        completedAt: null,
        status: 'running',
        model: null,
      };
      fs.writeFileSync(metaFile, JSON.stringify(meta, null, 2));
    }

    // Update meta on session_end
    if ((row as Record<string, unknown>)?.event === 'session_end') {
      try {
        const meta = JSON.parse(fs.readFileSync(metaFile, 'utf-8'));
        meta.completedAt = (row as Record<string, unknown>).ts ?? new Date().toISOString();
        meta.status = 'done';
        const usage = (row as Record<string, unknown>).model_usage as Record<string, unknown> | undefined;
        if (usage) {
          const first = Object.keys(usage)[0];
          if (first) meta.model = first;
        }
        fs.writeFileSync(metaFile, JSON.stringify(meta, null, 2));
      } catch { /* ignore */ }
    }

    // Append event row to JSONL — fs.watch in logs.ts picks this up automatically
    // and broadcasts to any connected WebSocket clients watching this file
    fs.appendFileSync(jsonlFile, JSON.stringify(row) + '\n');

    return reply.code(204).send();
  });
}
