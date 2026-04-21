import fs from 'fs';
import path from 'path';
import type { FastifyInstance } from 'fastify';
import type { ProjectPaths } from '../index.js';
import type { AgentSummary, AgentRun } from '../types.js';

function listAgents(agentsPath: string): string[] {
  if (!fs.existsSync(agentsPath)) return [];
  return fs.readdirSync(agentsPath)
    .filter(d => {
      const logsDir = path.join(agentsPath, d, 'logs');
      return fs.existsSync(logsDir) && fs.statSync(logsDir).isDirectory();
    })
    .sort();
}

function listRuns(agentsPath: string, agentName: string): AgentRun[] {
  const logsDir = path.join(agentsPath, agentName, 'logs');
  if (!fs.existsSync(logsDir)) return [];

  return fs.readdirSync(logsDir)
    .filter(d => d.startsWith('run-') && fs.statSync(path.join(logsDir, d)).isDirectory())
    .sort()
    .reverse()
    .map(runId => {
      const runDir = path.join(logsDir, runId);
      let meta: Record<string, unknown> = {};
      const metaFile = path.join(runDir, 'meta.json');
      try { meta = JSON.parse(fs.readFileSync(metaFile, 'utf-8')); } catch { /* skip */ }

      const files = fs.readdirSync(runDir)
        .filter(f => f.endsWith('.jsonl') && !f.endsWith('.raw.jsonl'))
        .map(f => {
          const stat = fs.statSync(path.join(runDir, f));
          return {
            name: f,
            path: `${agentName}/${runId}/${f}`,
            size: stat.size,
            modified: stat.mtime.toISOString(),
          };
        });

      return {
        id: runId,
        agent: agentName,
        hint_file: meta.hint_file as string | undefined,
        startedAt: meta.startedAt as string | undefined,
        completedAt: meta.completedAt as string | undefined,
        status: meta.status as string | undefined,
        model: meta.model as string | undefined,
        files,
      };
    });
}

export function register(fastify: FastifyInstance, paths: ProjectPaths) {
  const { agentsPath } = paths;

  fastify.get('/api/agents', async (): Promise<AgentSummary[]> => {
    return listAgents(agentsPath).map(name => {
      const runs = listRuns(agentsPath, name);
      return {
        name,
        runCount: runs.length,
        latestRun: runs[0]?.startedAt,
      };
    });
  });

  fastify.get<{ Params: { name: string } }>('/api/agents/:name/runs', async (req, reply) => {
    const { name } = req.params;
    if (!fs.existsSync(path.join(agentsPath, name, 'logs'))) {
      return reply.status(404).send({ error: 'Agent not found' });
    }
    return listRuns(agentsPath, name);
  });
}
