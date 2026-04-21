import path from 'path';
import type { FastifyInstance } from 'fastify';
import type { ProjectPaths } from '../index.js';

export function register(fastify: FastifyInstance, paths: ProjectPaths) {
  fastify.get('/api/project', async () => ({
    name: path.basename(paths.projectPath),
    path: paths.projectPath,
    agentsPath: paths.agentsPath,
  }));
}
