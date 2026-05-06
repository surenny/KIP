// Render the dependency DAG as SVG by piping a DOT description through the
// system `dot` binary (Graphviz). Mirrors what leanblueprint does at build
// time, except we do it on demand so we can apply UI filters server-side.
import { spawn } from 'child_process';

interface NodeRow {
  id: string;
  kind: string | null;
  chapter: string | null;
  subsection: string | null;
  phase: string;
}

interface EdgeRow {
  from_node: string;
  to_node: string;
}

const PHASE_COLORS: Record<string, string> = {
  drafted:     '#c9ccd1',
  nl_reviewed: '#6f42c1',
  bound:       '#0366d6',
  aligned:     '#e36209',
  proved:      '#28a745',
};

// Three shape buckets only — non-blueprint kinds (remark/example/question) are
// filtered out upstream, so we don't need shapes for them.
const KIND_SHAPES: Record<string, string> = {
  definition:  'ellipse',
  notation:    'ellipse',
  theorem:     'box',          // round-rectangle in DOT terms
  proposition: 'box',
  lemma:       'box',
  corollary:   'box',
  axiom:       'diamond',
};

// Kinds that belong on the formalization roadmap. Remarks, examples, and
// questions are commentary; they're filtered out of the dependency graph and
// sidebar counts (but remain reachable via direct /api/nodes/:id lookups).
export const BLUEPRINT_KINDS: ReadonlySet<string> = new Set([
  'definition', 'notation',
  'theorem', 'proposition', 'lemma', 'corollary',
  'axiom',
]);

// Pick a contrasting label color for a given fill — keep it readable.
function labelColorOn(bg: string): string {
  // simple luminance check
  const r = parseInt(bg.slice(1, 3), 16);
  const g = parseInt(bg.slice(3, 5), 16);
  const b = parseInt(bg.slice(5, 7), 16);
  const lum = (0.299 * r + 0.587 * g + 0.114 * b) / 255;
  return lum > 0.65 ? '#1a1a1a' : '#ffffff';
}

function lastSegment(id: string): string {
  const parts = id.split(':');
  return parts[parts.length - 1] || id;
}

// DOT identifiers must be quoted strings; escape embedded quotes/backslashes.
function escapeDot(s: string): string {
  return '"' + s.replace(/\\/g, '\\\\').replace(/"/g, '\\"') + '"';
}

export interface GraphFilters {
  phases?: Set<string>;
  chapters?: Set<string>;
  search?: string;
  hideOrphans?: boolean;
}

export function buildDot(nodes: NodeRow[], edges: EdgeRow[], filters: GraphFilters = {}): string {
  const phaseFilter = filters.phases;
  const chapterFilter = filters.chapters;
  const q = (filters.search || '').trim().toLowerCase();
  const hideOrphans = filters.hideOrphans !== false;  // default true

  const visible = new Set<string>();
  for (const n of nodes) {
    // Defense in depth — routes already drop non-blueprint kinds, but if a
    // caller bypasses that, the DOT shouldn't suddenly grow remark hexagons.
    if (n.kind && !BLUEPRINT_KINDS.has(n.kind)) continue;
    if (phaseFilter && !phaseFilter.has(n.phase)) continue;
    if (chapterFilter && n.chapter && !chapterFilter.has(n.chapter)) continue;
    if (hideOrphans && !n.chapter && !q) continue;
    if (q) {
      if (!n.id.toLowerCase().includes(q)) continue;
    }
    visible.add(n.id);
  }

  const lines: string[] = [];
  lines.push('digraph G {');
  lines.push('  rankdir=TB;');
  lines.push('  bgcolor="transparent";');
  lines.push('  pad="0.4";');
  lines.push('  nodesep=0.3;');
  lines.push('  ranksep=0.55;');
  lines.push('  splines=spline;');
  lines.push('  node [fontname="Helvetica,Arial,sans-serif", fontsize=11, ' +
             'style="filled,setlinewidth(1)", color="#00000033", penwidth=1, ' +
             'margin="0.18,0.06"];');
  lines.push('  edge [color="#9aa1a9", arrowsize=0.7, penwidth=1.0];');

  // Bucket visible nodes by chapter so we can emit each chapter as a Graphviz
  // cluster (rounded box w/ chapter label). Within a cluster the global
  // rankdir=TB still applies, so the dep→theorem flow is preserved; cross-
  // cluster edges are emitted at top level after all clusters are closed.
  const emitNode = (n: NodeRow) => {
    const fill = PHASE_COLORS[n.phase] || '#bbbbbb';
    const fontcolor = labelColorOn(fill);
    const shape = KIND_SHAPES[n.kind || ''] || 'ellipse';
    const label = lastSegment(n.id);
    const attrs = [
      `id=${escapeDot('node:' + n.id)}`,            // becomes `id` on <g> in SVG
      `label=${escapeDot(label)}`,
      `tooltip=${escapeDot(n.id)}`,
      `shape=${shape}`,
      `fillcolor=${escapeDot(fill)}`,
      `fontcolor=${escapeDot(fontcolor)}`,
      `class=${escapeDot('kip-node phase-' + n.phase + (n.kind ? ' kind-' + n.kind : ''))}`,
    ];
    return `    ${escapeDot(n.id)} [${attrs.join(', ')}];`;
  };

  // Two-level bucketing: chapter → subsection → nodes. A null subsection
  // means the node sits directly under \section (no \subsection layer in that
  // chapter, e.g. leibniz-mahowald.tex), so it's emitted at chapter level
  // rather than in a subsection sub-cluster. Iteration order follows the
  // insertion order of the node list, which matches LaTeX reading order.
  const byChapter = new Map<string, Map<string | null, NodeRow[]>>();
  const orphans: NodeRow[] = [];
  for (const n of nodes) {
    if (!visible.has(n.id)) continue;
    if (!n.chapter) { orphans.push(n); continue; }
    let chapMap = byChapter.get(n.chapter);
    if (!chapMap) { chapMap = new Map(); byChapter.set(n.chapter, chapMap); }
    const key = n.subsection || null;
    const list = chapMap.get(key);
    if (list) list.push(n); else chapMap.set(key, [n]);
  }

  let ci = 0;
  const openCluster = (label: string, indent: string, fill: string, border: string, fontSize: number) => {
    lines.push(`${indent}subgraph cluster_${ci++} {`);
    lines.push(`${indent}  label=${escapeDot(label)};`);
    lines.push(`${indent}  labeljust="l";`);
    lines.push(`${indent}  labelloc="t";`);
    lines.push(`${indent}  style="rounded,filled";`);
    lines.push(`${indent}  fillcolor=${escapeDot(fill)};`);
    lines.push(`${indent}  color=${escapeDot(border)};`);
    lines.push(`${indent}  fontname="Helvetica,Arial,sans-serif";`);
    lines.push(`${indent}  fontsize=${fontSize};`);
    lines.push(`${indent}  fontcolor="#57606a";`);
    lines.push(`${indent}  margin=10;`);
  };

  for (const [chapter, subMap] of byChapter) {
    openCluster(chapter, '  ', '#f6f8fa', '#d0d7de', 12);
    // Direct chapter-level nodes first (no subsection), then each subsection
    // bucket as its own nested cluster. Chapter-direct nodes typically only
    // appear when the chapter file has no \subsection at all.
    const direct = subMap.get(null) || [];
    for (const n of direct) lines.push(emitNode(n));
    for (const [sub, ns] of subMap) {
      if (sub === null) continue;
      openCluster(sub, '    ', '#ffffff', '#bcc4cc', 11);
      for (const n of ns) lines.push(`  ${emitNode(n)}`);
      lines.push(`    }`);
    }
    lines.push(`  }`);
  }
  // Any chapter-less visible nodes (only when hideOrphans is disabled) sit at
  // the top level so they still render.
  for (const n of orphans) lines.push(emitNode(n));

  for (const e of edges) {
    if (!visible.has(e.from_node) || !visible.has(e.to_node)) continue;
    // DB semantic: from_node has \uses{to_node}, i.e. from is upper, to is
    // lower. We flip direction in DOT so low-level definitions land at the
    // top (source rank) and the theorems they feed land at the bottom (sink
    // rank). Visually, arrows point downward in completion order:
    //     definition  ──▶  lemma  ──▶  theorem
    // The `id`/`eid` keeps the DB direction so SVG-side lookups stay
    // consistent with the edges table.
    const eid = `edge:${e.from_node}->${e.to_node}`;
    lines.push(`  ${escapeDot(e.to_node)} -> ${escapeDot(e.from_node)} ` +
               `[id=${escapeDot(eid)}];`);
  }
  lines.push('}');

  return lines.join('\n');
}

// Graphviz emits <title> elements that browsers render as hover tooltips.
// Strip the ones we don't want users to see:
//   * cluster_N — internal subgraph names on chapter / subsection boxes
//   * G        — the digraph name on the root graph group
//   * edge titles (e.g. "from->to") — fine in theory but become a nuisance
//     when zoomed in and the edge path is wide enough to reliably trigger
//     hover; the user explicitly opted out
// Node titles (the actual node id) are kept — those are useful on hover.
function stripInternalTitles(svg: string): string {
  return svg
    .replace(
      /(<g id="clust\d+"[^>]*class="cluster"[^>]*>\s*)<title>[^<]*<\/title>\s*/g,
      '$1',
    )
    .replace(
      /(<g id="graph\d+"[^>]*class="graph"[^>]*>\s*)<title>[^<]*<\/title>\s*/g,
      '$1',
    )
    .replace(
      /(<g id="edge[^"]*"[^>]*class="edge"[^>]*>\s*)<title>[^<]*<\/title>\s*/g,
      '$1',
    );
}

export async function renderSvg(dot: string, timeoutMs = 8000): Promise<string> {
  return new Promise((resolve, reject) => {
    const proc = spawn('dot', ['-Tsvg'], { stdio: ['pipe', 'pipe', 'pipe'] });
    let stdout = '';
    let stderr = '';
    const timer = setTimeout(() => {
      proc.kill('SIGKILL');
      reject(new Error(`dot timed out after ${timeoutMs}ms`));
    }, timeoutMs);
    proc.stdout.on('data', (b) => { stdout += b.toString(); });
    proc.stderr.on('data', (b) => { stderr += b.toString(); });
    proc.on('error', (err) => { clearTimeout(timer); reject(err); });
    proc.on('close', (code) => {
      clearTimeout(timer);
      if (code !== 0) reject(new Error(`dot exited ${code}: ${stderr.slice(0, 400)}`));
      else resolve(stripInternalTitles(stdout));
    });
    proc.stdin.end(dot);
  });
}
