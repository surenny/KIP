import fs from 'fs';
import path from 'path';
import Database from 'better-sqlite3';
import yaml from 'js-yaml';
import type { FastifyInstance } from 'fastify';
import type { ProjectPaths } from '../index.js';
import { buildDot, renderSvg, BLUEPRINT_KINDS, type GraphFilters } from './graph_svg.js';

interface NodeRow {
  id: string;
  kind: string | null;
  chapter: string | null;
  subsection: string | null;
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

// Canonical chapter order is the order of `\input{chapters/X}` lines in
// blueprint/src/content.tex. Cached with mtime invalidation since this file
// rarely changes. Falls back to filename glob (alphabetical) if content.tex
// is missing or has no `\input` lines.
let chapterOrderCache: { base: string; mtime: number; order: string[] } | null = null;

function getChapterOrder(projectPath: string): string[] {
  const contentTex = path.join(projectPath, 'blueprint', 'src', 'content.tex');
  let mtime = 0;
  try { mtime = fs.statSync(contentTex).mtimeMs; } catch { /* not present */ }

  if (chapterOrderCache && chapterOrderCache.base === contentTex && chapterOrderCache.mtime === mtime) {
    return chapterOrderCache.order;
  }

  let order: string[] = [];
  if (mtime > 0) {
    try {
      const text = fs.readFileSync(contentTex, 'utf-8');
      const re = /\\input\s*\{\s*chapters\/([A-Za-z0-9_-]+)\s*\}/g;
      const seen = new Set<string>();
      let m: RegExpExecArray | null;
      while ((m = re.exec(text)) !== null) {
        if (!seen.has(m[1])) { seen.add(m[1]); order.push(m[1]); }
      }
    } catch { /* ignore, fall back below */ }
  }

  if (order.length === 0) {
    // Fallback: sorted filenames in chapters/ — stable but alphabetical.
    const dir = path.join(projectPath, 'blueprint', 'src', 'chapters');
    try {
      order = fs.readdirSync(dir)
        .filter(f => f.endsWith('.tex'))
        .map(f => f.replace(/\.tex$/, ''))
        .sort();
    } catch { /* leave empty */ }
  }

  chapterOrderCache = { base: contentTex, mtime, order };
  return order;
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

// Separate write handle, used only by review actions. Each call opens / closes
// to avoid juggling cache invalidation alongside the readonly handle above.
function openDbForWrite(projectPath: string): Database.Database | null {
  const candidate = path.join(projectPath, '.kip', 'state.db');
  if (!fs.existsSync(candidate)) return null;
  return new Database(candidate, { readonly: false, fileMustExist: true });
}

// ---------- status.yaml read/write -------------------------------------------

interface StatusComment {
  topic?: string;
  text?: string;
  by?: string;
  at?: string;
  [key: string]: unknown;
}

interface StatusEntry {
  lean_decl?: string;
  nl_reviewed?: boolean;
  bound?: boolean;
  aligned?: boolean;
  proved?: boolean;
  kind?: string;
  comments?: StatusComment[];
  nl_reviewer?: string;
  nl_reviewed_at?: string;
  align_reviewer?: string;
  aligned_at?: string;
  nl_hash?: string;
  [key: string]: unknown;
}

interface StatusFile {
  nodes?: Record<string, StatusEntry>;
  [key: string]: unknown;
}

function loadStatus(yamlPath: string): StatusFile {
  if (!fs.existsSync(yamlPath)) return { nodes: {} };
  const text = fs.readFileSync(yamlPath, 'utf-8');
  const data = yaml.load(text);
  if (!data || typeof data !== 'object') return { nodes: {} };
  return data as StatusFile;
}

function saveStatus(yamlPath: string, data: StatusFile): void {
  // Match existing style: dates as quoted strings (yaml.dump quotes any
  // string scalar with quotingType "'" — fine since flags/booleans dump
  // unquoted). lineWidth: -1 disables auto-wrap so long IDs/strings stay
  // on one line.
  const out = yaml.dump(data, {
    lineWidth: -1,
    noRefs: true,
    sortKeys: false,
    quotingType: "'",
    forceQuotes: false,
  });
  const tmp = yamlPath + '.tmp';
  fs.writeFileSync(tmp, out, 'utf-8');
  // Best-effort fsync before rename so a crash mid-write can't leave a
  // half-written status.yaml.
  try {
    const fd = fs.openSync(tmp, 'r');
    fs.fsyncSync(fd);
    fs.closeSync(fd);
  } catch { /* ignore */ }
  fs.renameSync(tmp, yamlPath);
}

// Mirror tools/kip-state/index.py:derive_phase. Keep in sync with that file.
function derivePhase(flags: {
  nl_reviewed?: boolean; bound?: boolean; aligned?: boolean; proved?: boolean;
}): 'drafted' | 'nl_reviewed' | 'bound' | 'aligned' | 'proved' {
  if (flags.proved) return 'proved';
  if (flags.aligned) return 'aligned';
  if (flags.bound) return 'bound';
  if (flags.nl_reviewed) return 'nl_reviewed';
  return 'drafted';
}

function nowIso(): string {
  // Full ISO-8601 instant with UTC marker (e.g. 2026-04-27T08:15:32.123Z).
  // The client renders this in Beijing time and computes relative diffs from
  // it directly — date-only strings like '2026-04-19' (the legacy yaml form)
  // would be off by up to 8h after parsing as UTC midnight.
  return new Date().toISOString();
}

function shapeNode(r: NodeRow) {
  return {
    id: r.id,
    kind: r.kind,
    chapter: r.chapter,
    subsection: r.subsection,
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
      "SELECT from_node, to_node, source FROM edges"
    ).all() as EdgeRow[];
    return rows.map(r => ({
      from: r.from_node,
      to: r.to_node,
      source: r.source,
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
      const allNodes = db.prepare(
        "SELECT id, kind, chapter, subsection, phase FROM nodes"
      ).all() as
        { id: string; kind: string | null; chapter: string | null; subsection: string | null; phase: string }[];
      const nodes = allNodes.filter(n => !n.kind || BLUEPRINT_KINDS.has(n.kind));
      const visibleIds = new Set(nodes.map(n => n.id));
      const edges = (db.prepare("SELECT from_node, to_node FROM edges").all() as
        { from_node: string; to_node: string }[])
        .filter(e => visibleIds.has(e.from_node) && visibleIds.has(e.to_node));

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
    if (!db) return { nodes: [], edges: [], chapters: [] };
    // Restrict to blueprint kinds — remarks/examples/questions are commentary
    // and don't belong on the dependency DAG or sidebar counts. Detail
    // endpoints (/api/nodes/:id) still serve them so deep links keep working.
    const allRows = db.prepare("SELECT * FROM nodes ORDER BY id").all() as NodeRow[];
    const nodes = allRows
      .filter(r => !r.kind || BLUEPRINT_KINDS.has(r.kind))
      .map(shapeNode);
    const visibleIds = new Set(nodes.map(n => n.id));
    const edges = (db.prepare("SELECT from_node, to_node, source FROM edges").all() as EdgeRow[])
      .filter(r => visibleIds.has(r.from_node) && visibleIds.has(r.to_node))
      .map(r => ({ from: r.from_node, to: r.to_node, source: r.source }));
    // Chapters in the order they appear in blueprint/src/content.tex,
    // restricted to chapters that contain at least one node so the sidebar
    // doesn't list empty buckets.
    const present = new Set<string>();
    for (const n of nodes) if (n.chapter) present.add(n.chapter);
    const chapters = getChapterOrder(projectPath).filter(c => present.has(c));
    // Append any chapters that have nodes but aren't listed in content.tex,
    // so we never silently drop a populated bucket.
    for (const c of present) if (!chapters.includes(c)) chapters.push(c);
    return { nodes, edges, chapters };
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
      "SELECT to_node FROM edges WHERE from_node = ? ORDER BY to_node"
    ).all(id) as { to_node: string }[];

    const usedByEdges = db.prepare(
      "SELECT from_node FROM edges WHERE to_node = ? ORDER BY from_node"
    ).all(id) as { from_node: string }[];

    const leanDecl = row.lean_decl
      ? db.prepare("SELECT * FROM lean_decls WHERE name = ?").get(row.lean_decl) as
          { name: string; file: string; line_start: number; line_end: number; sorry_count: number } | undefined
      : null;

    // Slurp the source span so the dashboard can show the Lean code beside
    // the NL statement during alignment review. lean_decls.file is stored as
    // a project-root-relative path (e.g. "KIP/Foundations/Foo.lean"); resolve
    // and refuse anything that escapes the project root, same shape as the
    // NL excerpt below.
    let leanSource: string | null = null;
    if (leanDecl && leanDecl.file && leanDecl.line_start && leanDecl.line_end) {
      const fileAbs = path.isAbsolute(leanDecl.file)
        ? leanDecl.file
        : path.join(projectPath, leanDecl.file);
      const resolved = path.resolve(fileAbs);
      const projectAbs = path.resolve(projectPath);
      const inside = resolved === projectAbs || resolved.startsWith(projectAbs + path.sep);
      if (inside) {
        try {
          const text = fs.readFileSync(resolved, 'utf-8');
          const lines = text.split('\n');
          const start = Math.max(0, leanDecl.line_start - 1);
          // line_end is inclusive in the indexer; cap at file length so a
          // stale cache (file shrunk since last index) doesn't blow up.
          const end = Math.max(start, Math.min(lines.length, leanDecl.line_end));
          leanSource = lines.slice(start, end).join('\n');
        } catch {
          leanSource = null;
        }
      }
    }

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
      uses: usesEdges.map(e => ({ id: e.to_node })),
      usedBy: usedByEdges.map(e => ({ id: e.from_node })),
      leanDecl,
      leanSource,
      runs,
      nlExcerpt,
      nlRendered,
    };
  });

  // Human review actions. Two kinds, both move the node forward in the
  // lifecycle and leave a comment trail:
  //   approve_nl         drafted          → nl_reviewed
  //   confirm_alignment  nl_reviewed+bound → aligned
  // Source of truth is blueprint/status.yaml (what tools/kip-state/index.py
  // reads on rebuild). We mirror the change into .kip/state.db so the dashboard
  // reflects it immediately without re-running the indexer.
  fastify.post<{
    Params: { id: string };
    Body: { action?: string; reviewer?: string; comment?: string };
  }>('/api/nodes/:id/review', async (req, reply) => {
    const id = req.params.id;
    const action = (req.body?.action || '').trim();
    const reviewer = (req.body?.reviewer || '').trim();
    const userComment = (req.body?.comment || '').trim();

    if (action !== 'approve_nl' && action !== 'confirm_alignment') {
      return reply.status(400).send({ error: 'action must be approve_nl or confirm_alignment' });
    }
    if (!reviewer) {
      return reply.status(400).send({ error: 'reviewer is required' });
    }

    const db = openDb(projectPath);
    if (!db) return reply.status(503).send({ error: 'state.db not built' });
    const row = db.prepare("SELECT * FROM nodes WHERE id = ?").get(id) as NodeRow | undefined;
    if (!row) return reply.status(404).send({ error: 'Node not found' });

    const flags = {
      nl_reviewed: !!row.nl_reviewed,
      bound: !!row.bound,
      aligned: !!row.aligned,
      proved: !!row.proved,
    };

    if (action === 'approve_nl') {
      if (flags.nl_reviewed) {
        return reply.status(409).send({ error: 'NL already reviewed' });
      }
    } else { // confirm_alignment
      if (!flags.nl_reviewed) {
        return reply.status(409).send({ error: 'NL not yet reviewed' });
      }
      if (!flags.bound) {
        return reply.status(409).send({ error: 'Lean declaration not bound yet' });
      }
      if (flags.aligned) {
        return reply.status(409).send({ error: 'already aligned' });
      }
    }

    const now = nowIso();
    const yamlPath = path.join(projectPath, 'blueprint', 'status.yaml');
    const status = loadStatus(yamlPath);
    if (!status.nodes) status.nodes = {};
    const entry: StatusEntry = status.nodes[id] || {};

    const commentTopic = action === 'approve_nl' ? 'nl-review' : 'align';
    const defaultText = action === 'approve_nl' ? 'NL approved' : 'Alignment confirmed';
    const newComment: StatusComment = {
      topic: commentTopic,
      text: userComment || defaultText,
      by: reviewer,
      at: now,
    };
    const existingComments = Array.isArray(entry.comments) ? entry.comments : [];
    entry.comments = [...existingComments, newComment];

    if (action === 'approve_nl') {
      entry.nl_reviewed = true;
      entry.nl_reviewer = reviewer;
      entry.nl_reviewed_at = now;
    } else {
      entry.aligned = true;
      entry.align_reviewer = reviewer;
      entry.aligned_at = now;
    }
    status.nodes[id] = entry;

    // Mirror to DB cache. Wrap in a transaction so a crash midway leaves the DB
    // either fully updated or untouched (yaml is already saved at this point —
    // worst case the next index.py run re-derives from yaml and reconciles).
    saveStatus(yamlPath, status);

    const writeDb = openDbForWrite(projectPath);
    if (writeDb) {
      try {
        const newFlags = {
          ...flags,
          nl_reviewed: action === 'approve_nl' ? true : flags.nl_reviewed,
          aligned: action === 'confirm_alignment' ? true : flags.aligned,
        };
        const newPhase = derivePhase(newFlags);
        const tx = writeDb.transaction(() => {
          if (action === 'approve_nl') {
            writeDb.prepare(
              "UPDATE nodes SET nl_reviewed=1, nl_reviewer=?, last_activity=?, phase=? WHERE id=?"
            ).run(reviewer, now, newPhase, id);
          } else {
            writeDb.prepare(
              "UPDATE nodes SET aligned=1, align_reviewer=?, aligned_at=?, last_activity=?, phase=? WHERE id=?"
            ).run(reviewer, now, now, newPhase, id);
          }
          const maxIdx = writeDb.prepare(
            "SELECT COALESCE(MAX(idx), -1) AS m FROM node_comments WHERE node_id=?"
          ).get(id) as { m: number };
          writeDb.prepare(
            "INSERT INTO node_comments(node_id, idx, topic, text, by, at) VALUES (?,?,?,?,?,?)"
          ).run(id, maxIdx.m + 1, commentTopic, newComment.text, reviewer, now);
        });
        tx();
      } finally {
        try { writeDb.close(); } catch { /* ignore */ }
      }
    }

    return { ok: true, id, action, reviewer, at: now };
  });
}
