import Fastify from 'fastify';
import cors from '@fastify/cors';
import staticFiles from '@fastify/static';
import websocket from '@fastify/websocket';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

import { register as registerProject } from './routes/project.js';
import { register as registerAgents } from './routes/agents.js';
import { register as registerLogs } from './routes/logs.js';
import { register as registerSummary } from './routes/summary.js';
import { register as registerNodes } from './routes/nodes.js';

export interface ProjectPaths {
  projectPath: string;
  agentsPath: string;
}

export interface ProjectInfo {
  name: string;
  path: string;
}

export interface ProjectState {
  paths: ProjectPaths;
  allProjects: ProjectInfo[];
}

function discoverProjects(primaryPath: string): ProjectInfo[] {
  const parent = path.dirname(primaryPath);
  const found: ProjectInfo[] = [];
  try {
    for (const entry of fs.readdirSync(parent, { withFileTypes: true })) {
      if (!entry.isDirectory()) continue;
      const full = path.join(parent, entry.name);
      const hasBarchon = fs.existsSync(path.join(full, '.barchon'));
      const hasAgents = fs.existsSync(path.join(full, 'agents'));
      if (hasBarchon || hasAgents) found.push({ name: entry.name, path: full });
    }
  } catch { /* ignore */ }
  if (!found.find(p => p.path === primaryPath)) {
    found.unshift({ name: path.basename(primaryPath), path: primaryPath });
  }
  found.sort((a, b) => {
    if (a.path === primaryPath) return -1;
    if (b.path === primaryPath) return 1;
    return a.name.localeCompare(b.name);
  });
  return found;
}

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

function parseArgs(): { projectPath: string; port: number } {
  const args = process.argv.slice(2);
  let projectPath = process.cwd();
  let port = 8081;
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--project' && i + 1 < args.length) projectPath = args[++i];
    else if (args[i] === '--port' && i + 1 < args.length) port = parseInt(args[++i], 10);
  }
  return { projectPath, port };
}

export async function createServer(options: { projectPath: string; port: number }) {
  const { projectPath, port } = options;

  const paths: ProjectPaths = {
    projectPath,
    agentsPath: path.join(projectPath, 'agents'),
  };

  const state: ProjectState = {
    paths,
    allProjects: discoverProjects(projectPath),
  };

  const fastify = Fastify({
    logger: false,
    rewriteUrl: (req) => {
      const url = req.url ?? '/';
      const proxyMatch = url.match(/\/proxy\/\d+(\/.*)$/);
      return proxyMatch ? proxyMatch[1] : url;
    },
  });
  await fastify.register(cors);
  await fastify.register(websocket);

  const clientBuildPath = path.join(__dirname, '../../client/dist');
  if (fs.existsSync(clientBuildPath)) {
    await fastify.register(staticFiles, { root: clientBuildPath, prefix: '/' });
    fastify.setNotFoundHandler((req, reply) => {
      if (req.url.startsWith('/api/')) return reply.status(404).send({ error: 'Not found' });
      return reply.sendFile('index.html');
    });
  }

  registerProject(fastify, state);
  registerAgents(fastify, state);
  registerLogs(fastify, state);
  registerSummary(fastify, state);
  registerNodes(fastify, state);

  await fastify.listen({ port, host: '0.0.0.0' });
  return fastify;
}

if (import.meta.url === `file://${process.argv[1]}`) {
  const { projectPath, port } = parseArgs();
  console.log(`KIP Dashboard → http://localhost:${port}  (project: ${projectPath})`);
  createServer({ projectPath, port }).catch(err => { console.error(err); process.exit(1); });
}
