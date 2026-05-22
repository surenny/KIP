import path from 'path';
import type { FastifyInstance } from 'fastify';
import type { ProjectState } from '../index.js';

export function register(fastify: FastifyInstance, state: ProjectState) {
  fastify.get('/api/project', async () => ({
    name: path.basename(state.paths.projectPath),
    path: state.paths.projectPath,
    agentsPath: state.paths.agentsPath,
  }));

  fastify.get('/api/projects', async () => state.allProjects);

  fastify.post<{ Body: { path: string } }>('/api/project/switch', async (req, reply) => {
    const { path: newPath } = req.body ?? {};
    if (!newPath) return reply.status(400).send({ error: 'path required' });
    const found = state.allProjects.find(p => p.path === newPath);
    if (!found) return reply.status(404).send({ error: 'Project not found' });
    state.paths = {
      projectPath: found.path,
      agentsPath: path.join(found.path, 'agents'),
    };
    return { name: found.name, path: found.path, agentsPath: state.paths.agentsPath };
  });
}
