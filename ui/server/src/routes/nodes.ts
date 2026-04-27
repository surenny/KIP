import fs from 'fs';
import path from 'path';
import Database from 'better-sqlite3';
import type { FastifyInstance } from 'fastify';
import type { ProjectPaths } from '../index.js';
import { buildDot, renderSvg, type GraphFilters } from './graph_svg.js';

interface NodeRow {
  id: string;
  kind: string | null;
  chapter: string | null;
  source_file: string | null;
  source_line: number | null;
  lean_decl: string | null;
  leanok: number;
  nl_hash: string | null;
  nl_reviewed: number;
  bound: number;
  aligned: number;
  proved: number;
  nl_reviewer: string | null;
  align_reviewer: string | null;
  aligned_at: string | null;
  last_activity: string | null;
  phase: string;
}

interface EdgeRow {
  from_node: string;
  to_node: string;
  source: string;
  confirmed: number;
}

let dbInstance: Database.Database | null = null;
let dbPath: string | null = null;
let dbMtime: number = 0;

// nodeId → absolute path of the chapter HTML containing it.
// Built lazily (and rebuilt if `blueprint/web` mtime changes).
let renderedIndex: Map<string, string> | null = null;
let renderedIndexBase: string | null = null;
let renderedIndexMtime: number = 0;

function buildRenderedIndex(projectPath: string): Map<string, string> {
  const map = new Map<string, string>();
  const webDir = path.join(projectPath, 'blueprint', 'web');
  if (!fs.existsSync(webDir)) return map;
  const files = fs.readdirSync(webDir).filter(f => f.startsWith('sec-') && f.endsWith('.html'));
  const re = /<div class="[^"]*_thmwrapper[^"]*" id="([^"]+)"/g;
  for (const f of files) {
    const full = path.join(webDir, f);
    let text: string;
    try { text = fs.readFileSync(full, 'utf-8'); } catch { continue; }
    let m: RegExpExecArray | null;
    while ((m = re.exec(text)) !== null) {
      if (!map.has(m[1])) map.set(m[1], full);
    }
  }
  return map;
}

function getRenderedIndex(projectPath: string): Map<string, string> {
  const webDir = path.join(projectPath, 'blueprint', 'web');
  // Use max(mtime) across the actual sec-*.html files. The directory's own
  // mtime only changes on entry add/remove, so rebuilding blueprint web
  // (which rewrites file contents in place) wouldn't otherwise invalidate.
  let mtime = 0;
  if (fs.existsSync(webDir)) {
    try {
      for (const f of fs.readdirSync(webDir)) {
        if (!f.startsWith('sec-') || !f.endsWith('.html')) continue;
        const m = fs.statSync(path.join(webDir, f)).mtimeMs;
        if (m > mtime) mtime = m;
      }
    } catch { mtime = 0; }
  }
  if (renderedIndex && renderedIndexBase === webDir && renderedIndexMtime === mtime) {
    return renderedIndex;
  }
  renderedIndex = buildRenderedIndex(projectPath);
  renderedIndexBase = webDir;
  renderedIndexMtime = mtime;
  return renderedIndex;
}

function escapeRe(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

// Find the matching </div> for a <div...> opened at `openEnd` (one past >).
function findClosingDiv(html: string, openEnd: number): number {
  let i = openEnd;
  let depth = 1;
  while (i < html.length && depth > 0) {
    const next = html.indexOf('<', i);
    if (next === -1) return -1;
    if (html.startsWith('</div', next)) {
      depth--;
      if (depth === 0) return next;
      i = html.indexOf('>', next) + 1;
    } else if (html.startsWith('<div', next)) {
      depth++;
      i = html.indexOf('>', next) + 1;
    } else {
      i = next + 1;
    }
  }
  return -1;
}

interface RenderedNode {
  caption: string;
  label: string;
  contentHtml: string;
}

function extractRenderedNode(html: string, nodeId: string): RenderedNode | null {
  const startRe = new RegExp(`<div class="([^"]*)_thmwrapper[^"]*" id="${escapeRe(nodeId)}">`);
  const sm = startRe.exec(html);
  if (!sm) return null;
  const kindClass = sm[1]; // e.g. "definition" / "theorem" / "remark"
  const wrapperEnd = findClosingDiv(html, sm.index + sm[0].length);
  const wrapper = wrapperEnd === -1 ? html.slice(sm.index) : html.slice(sm.index, wrapperEnd);

  const capRe = new RegExp(`<span class="${kindClass}_thmcaption">\\s*([^<]+?)\\s*</span>`);
  const lblRe = new RegExp(`<span class="${kindClass}_thmlabel">\\s*([^<]+?)\\s*</span>`);
  const contStartRe = new RegExp(`<div class="${kindClass}_thmcontent">`);
  const cm = capRe.exec(wrapper);
  const lm = lblRe.exec(wrapper);
  const csm = contStartRe.exec(wrapper);
  let contentHtml = '';
  if (csm) {
    const innerStart = csm.index + csm[0].length;
    const innerEnd = findClosingDiv(wrapper, innerStart);
    contentHtml = innerEnd === -1 ? wrapper.slice(innerStart) : wrapper.slice(innerStart, innerEnd);
  }
  return {
    caption: cm ? cm[1].trim() : '',
    label: lm ? lm[1].trim() : '',
    contentHtml,
  };
}

function getRenderedNode(projectPath: string, nodeId: string): RenderedNode | null {
  const idx = getRenderedIndex(projectPath);
  const file = idx.get(nodeId);
  if (!file) return null;
  let text: string;
  try { text = fs.readFileSync(file, 'utf-8'); } catch { return null; }
  return extractRenderedNode(text, nodeId);
}

function openDb(projectPath: string): Database.Database | null {
  const candidate = path.join(projectPath, '.kip', 'state.db');
  if (!fs.existsSync(candidate)) return null;
  const stat = fs.statSync(candidate);
  if (dbInstance && dbPath === candidate && dbMtime === stat.mtimeMs) {
    return dbInstance;
  }
  if (dbInstance) {
    try { dbInstance.close(); } catch { /* ignore */ }
  }
  dbInstance = new Database(candidate, { readonly: true, fileMustExist: true });
  dbPath = candidate;
  dbMtime = stat.mtimeMs;
  return dbInstance;
}

function shapeNode(r: NodeRow) {
  return {
    id: r.id,
    kind: r.kind,
    chapter: r.chapter,
    sourceFile: r.source_file,
    sourceLine: r.source_line,
    leanDecl: r.lean_decl,
    leanok: !!r.leanok,
    nlHash: r.nl_hash,
    flags: {
      nlReviewed: !!r.nl_reviewed,
      bound: !!r.bound,
      aligned: !!r.aligned,
      proved: !!r.proved,
    },
    nlReviewer: r.nl_reviewer,
    alignReviewer: r.align_reviewer,
    alignedAt: r.aligned_at,
    lastActivity: r.last_activity,
    phase: r.phase,
  };
}

export function register(fastify: FastifyInstance, paths: ProjectPaths) {
  const { projectPath } = paths;

  fastify.get('/api/state/health', async () => {
    const db = openDb(projectPath);
    if (!db) {
      return {
        ok: false,
        error: 'No .kip/state.db found. Run: python tools/kip-state/index.py',
      };
    }
    const meta = db.prepare("SELECT key, value FROM meta").all() as { key: string; value: string }[];
    const counts = {
      nodes: (db.prepare("SELECT count(*) AS c FROM nodes").get() as { c: number }).c,
      edges: (db.prepare("SELECT count(*) AS c FROM edges").get() as { c: number }).c,
      lean_decls: (db.prepare("SELECT count(*) AS c FROM lean_decls").get() as { c: number }).c,
      agent_runs: (db.prepare("SELECT count(*) AS c FROM agent_runs").get() as { c: number }).c,
    };
    const phases = db.prepare(
      "SELECT phase, count(*) AS c FROM nodes GROUP BY phase"
    ).all() as { phase: string; c: number }[];
    return {
      ok: true,
      meta: Object.fromEntries(meta.map(m => [m.key, m.value])),
      counts,
      phases: Object.fromEntries(phases.map(p => [p.phase, p.c])),
    };
  });

  fastify.get('/api/nodes', async () => {
    const db = openDb(projectPath);
    if (!db) return [];
    const rows = db.prepare(
      "SELECT * FROM nodes ORDER BY phase, id"
    ).all() as NodeRow[];
    return rows.map(shapeNode);
  });

  fastify.get('/api/edges', async () => {
    const db = openDb(projectPath);
    if (!db) return [];
    const rows = db.prepare(
      "SELECT from_node, to_node, source, confirmed FROM edges"
    ).all() as EdgeRow[];
    return rows.map(r => ({
      from: r.from_node,
      to: r.to_node,
      source: r.source,
      confirmed: !!r.confirmed,
    }));
  });

  // Server-rendered SVG of the dependency DAG via Graphviz `dot`. Filters
  // (phases, chapters, q) are honored so the returned SVG only contains the
  // visible subset — keeps client-side payload small and lets layout focus
  // on what's shown.
  fastify.get<{ Querystring: { phases?: string; chapters?: string; q?: string; orphans?: string } }>(
    '/api/graph/svg',
    async (req, reply) => {
      const db = openDb(projectPath);
      if (!db) {
        reply.status(503);
        return { error: 'state.db not built' };
      }
      const nodes = db.prepare("SELECT id, kind, chapter, phase FROM nodes").all() as
        { id: string; kind: string | null; chapter: string | null; phase: string }[];
      const edges = db.prepare("SELECT from_node, to_node, confirmed FROM edges").all() as
        { from_node: string; to_node: string; confirmed: number }[];

      const filters: GraphFilters = {};
      if (req.query.phases) filters.phases = new Set(req.query.phases.split(',').filter(Boolean));
      if (req.query.chapters) filters.chapters = new Set(req.query.chapters.split(',').filter(Boolean));
      if (req.query.q) filters.search = req.query.q;
      if (req.query.orphans === '1') filters.hideOrphans = false;

      const dot = buildDot(nodes, edges, filters);
      try {
        const svg = await renderSvg(dot);
        reply.type('image/svg+xml').header('cache-control', 'no-store');
        return svg;
      } catch (err: unknown) {
        reply.status(500);
        return { error: String((err as Error)?.message || err) };
      }
    },
  );

  // Combined payload sized for one round-trip into the DAG view.
  fastify.get('/api/graph', async () => {
    const db = openDb(projectPath);
    if (!db) return { nodes: [], edges: [] };
    const nodes = (db.prepare("SELECT * FROM nodes ORDER BY id").all() as NodeRow[]).map(shapeNode);
    const edges = (db.prepare("SELECT from_node, to_node, source, confirmed FROM edges").all() as EdgeRow[])
      .map(r => ({ from: r.from_node, to: r.to_node, source: r.source, confirmed: !!r.confirmed }));
    return { nodes, edges };
  });

  fastify.get<{ Params: { id: string } }>('/api/nodes/:id', async (req, reply) => {
    const db = openDb(projectPath);
    if (!db) return reply.status(503).send({ error: 'state.db not built' });
    const id = req.params.id;
    const row = db.prepare("SELECT * FROM nodes WHERE id = ?").get(id) as NodeRow | undefined;
    if (!row) return reply.status(404).send({ error: 'Node not found' });

    const comments = db.prepare(
      "SELECT idx, topic, text, by, at FROM node_comments WHERE node_id = ? ORDER BY idx"
    ).all(id);

    const usesEdges = db.prepare(
      "SELECT to_node, confirmed FROM edges WHERE from_node = ? ORDER BY to_node"
    ).all(id) as { to_node: string; confirmed: number }[];

    const usedByEdges = db.prepare(
      "SELECT from_node, confirmed FROM edges WHERE to_node = ? ORDER BY from_node"
    ).all(id) as { from_node: string; confirmed: number }[];

    const leanDecl = row.lean_decl
      ? db.prepare("SELECT * FROM lean_decls WHERE name = ?").get(row.lean_decl)
      : null;

    const runs = db.prepare(
      `SELECT ar.id, ar.agent, ar.started_at, ar.completed_at, ar.status,
              ar.model, ar.hint_file, ar.cost_usd, ar.duration_ms, ar.num_turns,
              ar.summary, ar.log_path
         FROM agent_runs ar
         JOIN agent_run_nodes arn ON arn.run_id = ar.id
        WHERE arn.node_id = ?
        ORDER BY ar.started_at DESC`
    ).all(id);

    let nlExcerpt: string | null = null;
    if (row.source_file && row.source_line) {
      // source_file comes from the SQLite cache, which itself derives from
      // chapter .tex paths. Refuse anything that resolves outside the project
      // root before touching the filesystem — defends against a poisoned DB.
      const resolved = path.resolve(row.source_file);
      const projectAbs = path.resolve(projectPath);
      const inside = resolved === projectAbs || resolved.startsWith(projectAbs + path.sep);
      if (inside) {
        try {
          const text = fs.readFileSync(resolved, 'utf-8');
          const lines = text.split('\n');
          const start = Math.max(0, row.source_line - 1);
          // Read until matching \end{kind} or 80-line cap, whichever first.
          // Escape kind defensively in case YAML ever contains regex metas.
          const escapedKind = row.kind
            ? row.kind.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
            : '\\w+';
          const endRe = new RegExp(`\\\\end\\{${escapedKind}\\*?\\}`);
          let end = start;
          for (let i = start; i < Math.min(lines.length, start + 80); i++) {
            end = i;
            if (endRe.test(lines[i])) break;
          }
          nlExcerpt = lines.slice(start, end + 1).join('\n');
        } catch {
          nlExcerpt = null;
        }
      }
    }

    const nlRendered = getRenderedNode(projectPath, id);

    return {
      ...shapeNode(row),
      comments,
      uses: usesEdges.map(e => ({ id: e.to_node, confirmed: !!e.confirmed })),
      usedBy: usedByEdges.map(e => ({ id: e.from_node, confirmed: !!e.confirmed })),
      leanDecl,
      runs,
      nlExcerpt,
      nlRendered,
    };
  });
}
