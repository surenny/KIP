import fs from 'fs';
import path from 'path';
import type { FastifyInstance } from 'fastify';
import type { ProjectPaths } from '../index.js';
import type { LogEntry, AggregatedStats, SessionSummary } from '../types.js';
import { parseJsonl } from '../utils.js';

function calculateStats(logs: LogEntry[]): AggregatedStats {
  const sessions: SessionSummary[] = [];
  let totalCost = 0, totalDuration = 0, totalTokensIn = 0, totalTokensOut = 0;

  for (const entry of logs) {
    if (entry.event !== 'session_end') continue;
    const cost = entry.total_cost_usd || 0;
    const duration = entry.duration_ms || 0;
    const tokIn = entry.input_tokens || 0;
    const tokOut = entry.output_tokens || 0;
    const model = entry.model_usage ? Object.keys(entry.model_usage)[0] || 'unknown' : 'unknown';
    totalCost += cost;
    totalDuration += duration;
    totalTokensIn += tokIn;
    totalTokensOut += tokOut;
    sessions.push({
      cost, duration, tokensIn: tokIn, tokensOut: tokOut,
      model, turns: entry.num_turns || 0, timestamp: entry.ts,
      summary: entry.summary,
    });
  }
  return { totalCost, totalDuration, totalTokensIn, totalTokensOut, sessionCount: sessions.length, sessions };
}

export function register(fastify: FastifyInstance, paths: ProjectPaths) {
  const { agentsPath } = paths;

  fastify.get('/api/summary', async () => {
    if (!fs.existsSync(agentsPath)) return { totalCost: 0, totalDuration: 0, totalTokensIn: 0, totalTokensOut: 0, sessionCount: 0, sessions: [] };
    let allLogs: LogEntry[] = [];
    function walkJsonl(dir: string) {
      for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
        const full = path.join(dir, entry.name);
        if (entry.isDirectory()) walkJsonl(full);
        else if (entry.isFile() && entry.name.endsWith('.jsonl') && !entry.name.endsWith('.raw.jsonl')) {
          allLogs = allLogs.concat(parseJsonl(full));
        }
      }
    }
    const agentDirs = fs.readdirSync(agentsPath)
      .filter(d => fs.existsSync(path.join(agentsPath, d, 'logs')))
      .map(d => path.join(agentsPath, d, 'logs'));
    for (const dir of agentDirs) walkJsonl(dir);
    return calculateStats(allLogs);
  });
}
