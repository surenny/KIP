import { useEffect, useMemo, useRef, useState } from 'react';
import { useNavigate, useParams } from 'react-router-dom';
import cytoscape from 'cytoscape';
import dagre from 'cytoscape-dagre';
import { useGraph } from '../hooks/useApi';
import { PHASE_COLORS, PHASE_ORDER, PHASE_LABELS, KIND_SHAPES } from '../utils/constants';
import NodeDetail from '../components/NodeDetail';
import type { GraphPayload, NodeData, Phase } from '../types';
import styles from './Nodes.module.css';

cytoscape.use(dagre);

const ALL_PHASES = [...PHASE_ORDER];

function lastSegment(id: string): string {
  const parts = id.split(':');
  return parts[parts.length - 1] || id;
}

function buildElements(graph: GraphPayload, visibleIds: Set<string>) {
  const els: cytoscape.ElementDefinition[] = [];
  for (const n of graph.nodes) {
    if (!visibleIds.has(n.id)) continue;
    els.push({
      data: {
        id: n.id,
        label: lastSegment(n.id),
        color: PHASE_COLORS[n.phase] || '#999',
        shape: KIND_SHAPES[n.kind || ''] || 'ellipse',
        kind: n.kind,
        phase: n.phase,
      },
    });
  }
  for (const e of graph.edges) {
    if (!visibleIds.has(e.from) || !visibleIds.has(e.to)) continue;
    els.push({
      data: {
        id: `${e.from}__${e.to}`,
        source: e.from,
        target: e.to,
        confirmed: e.confirmed ? 1 : 0,
      },
    });
  }
  return els;
}

const CY_STYLE: cytoscape.StylesheetCSS[] = [
  {
    selector: 'node',
    css: {
      'background-color': 'data(color)' as unknown as string,
      'shape': 'data(shape)' as cytoscape.Css.NodeShape,
      'label': 'data(label)',
      'font-size': 9,
      'font-family': "'SF Mono', 'Menlo', monospace",
      'text-valign': 'center',
      'text-halign': 'center',
      'color': '#1a1a1a',
      'text-outline-color': '#fff',
      'text-outline-width': 2,
      'width': 60,
      'height': 28,
      'border-width': 1,
      'border-color': 'rgba(0,0,0,0.18)',
      'text-wrap': 'ellipsis' as 'wrap',
      'text-max-width': '70px',
    },
  },
  {
    selector: 'node:selected',
    css: {
      'border-width': 3,
      'border-color': '#0366d6',
      'border-style': 'solid',
    },
  },
  {
    selector: 'edge',
    css: {
      'width': 1,
      'line-color': '#c9ccd1',
      'target-arrow-color': '#c9ccd1',
      'target-arrow-shape': 'triangle',
      'arrow-scale': 0.8,
      'curve-style': 'bezier',
      'opacity': 0.7,
    },
  },
  {
    selector: 'edge[confirmed = 0]',
    css: {
      'line-style': 'dashed',
    },
  },
  {
    selector: '.faded',
    css: { 'opacity': 0.18 },
  },
  {
    selector: '.highlighted',
    css: { 'opacity': 1, 'z-index': 100 },
  },
  {
    selector: 'edge.highlighted',
    css: { 'line-color': '#0366d6', 'target-arrow-color': '#0366d6', 'width': 2 },
  },
];

export default function Nodes() {
  const { data: graph } = useGraph();
  const { id: routeId } = useParams<{ id?: string }>();
  const navigate = useNavigate();
  const containerRef = useRef<HTMLDivElement | null>(null);
  const cyRef = useRef<cytoscape.Core | null>(null);
  const [selectedId, setSelectedId] = useState<string>('');
  const [search, setSearch] = useState('');
  const [activePhases, setActivePhases] = useState<Set<Phase>>(() => new Set<Phase>(ALL_PHASES));
  const [activeChapters, setActiveChapters] = useState<Set<string>>(() => new Set());
  const [chaptersInitialized, setChaptersInitialized] = useState(false);

  // initialize active chapters once we know what they are
  useEffect(() => {
    if (chaptersInitialized || !graph) return;
    const all = new Set<string>();
    for (const n of graph.nodes) if (n.chapter) all.add(n.chapter);
    setActiveChapters(all);
    setChaptersInitialized(true);
  }, [graph, chaptersInitialized]);

  // route → state sync
  useEffect(() => {
    if (routeId && routeId !== selectedId) setSelectedId(routeId);
  }, [routeId, selectedId]);

  const allChapters = useMemo(() => {
    if (!graph) return [] as string[];
    const set = new Set<string>();
    for (const n of graph.nodes) if (n.chapter) set.add(n.chapter);
    return Array.from(set).sort();
  }, [graph]);

  // counts per phase / chapter
  const phaseCounts = useMemo(() => {
    const counts: Record<string, number> = {};
    if (graph) for (const n of graph.nodes) counts[n.phase] = (counts[n.phase] || 0) + 1;
    return counts;
  }, [graph]);

  const chapterCounts = useMemo(() => {
    const counts: Record<string, number> = {};
    if (graph) for (const n of graph.nodes) if (n.chapter) counts[n.chapter] = (counts[n.chapter] || 0) + 1;
    return counts;
  }, [graph]);

  // visible node set after filters
  const visibleIds = useMemo(() => {
    const set = new Set<string>();
    if (!graph) return set;
    const q = search.trim().toLowerCase();
    for (const n of graph.nodes) {
      if (!activePhases.has(n.phase)) continue;
      // chapter filter only applies to nodes with a chapter; orphans (no source) always shown
      if (n.chapter && !activeChapters.has(n.chapter)) continue;
      if (q) {
        const hay = `${n.id} ${n.leanDecl || ''}`.toLowerCase();
        if (!hay.includes(q)) continue;
      }
      // skip orphans (no source) when not searched explicitly
      if (!n.chapter && !q) continue;
      set.add(n.id);
    }
    return set;
  }, [graph, activePhases, activeChapters, search]);

  // (re)mount cytoscape when graph or filter changes
  useEffect(() => {
    if (!graph || !containerRef.current) return;
    if (cyRef.current) {
      cyRef.current.destroy();
      cyRef.current = null;
    }
    const elements = buildElements(graph, visibleIds);
    const cy = cytoscape({
      container: containerRef.current,
      elements,
      style: CY_STYLE,
      layout: {
        name: 'dagre',
        rankDir: 'TB',
        nodeSep: 14,
        rankSep: 40,
        edgeSep: 8,
      } as unknown as cytoscape.LayoutOptions,
      wheelSensitivity: 1,
      minZoom: 0.1,
      maxZoom: 4,
    });
    // Edges are visual structure only, not interactive targets.
    cy.edges().unselectify();
    cy.on('tap', 'node', (evt) => {
      const id = evt.target.id() as string;
      setSelectedId(id);
      navigate(`/nodes/${encodeURIComponent(id)}`);
    });
    cy.on('tap', (evt) => {
      // treat background AND edge taps as "deselect" so an edge click
      // doesn't leave a stale selection ring or open a drawer.
      if (evt.target === cy || (evt.target.isEdge && evt.target.isEdge())) {
        setSelectedId('');
        navigate('/nodes');
      }
    });
    cyRef.current = cy;
    return () => { cy.destroy(); cyRef.current = null; };
  }, [graph, visibleIds, navigate]);

  // highlight selected + neighborhood
  useEffect(() => {
    const cy = cyRef.current;
    if (!cy) return;
    cy.elements().removeClass('highlighted faded');
    if (!selectedId) return;
    const sel = cy.getElementById(selectedId);
    if (sel.empty()) return;
    const neighborhood = sel.closedNeighborhood();
    cy.elements().difference(neighborhood).addClass('faded');
    neighborhood.addClass('highlighted');
    sel.select();
    // gently bring it into view if it's far off-screen
    const bb = sel.boundingBox({});
    const ext = cy.extent();
    if (bb.x1 < ext.x1 || bb.x2 > ext.x2 || bb.y1 < ext.y1 || bb.y2 > ext.y2) {
      cy.center(sel);
    }
  }, [selectedId, visibleIds]);

  const togglePhase = (p: Phase) => {
    setActivePhases(prev => {
      const next = new Set(prev);
      if (next.has(p)) next.delete(p); else next.add(p);
      return next;
    });
  };
  const toggleChapter = (c: string) => {
    setActiveChapters(prev => {
      const next = new Set(prev);
      if (next.has(c)) next.delete(c); else next.add(c);
      return next;
    });
  };

  if (!graph) {
    return (
      <div className={styles.canvasMissing}>
        Loading graph data…
      </div>
    );
  }

  if (graph.nodes.length === 0) {
    return (
      <div className={styles.canvasMissing}>
        State index is empty.<br/>
        Run <code>python tools/kip-state/index.py</code> from the project root.
      </div>
    );
  }

  return (
    <div className={`${styles.root} ${selectedId ? styles.drawerOpen : ''}`}>
      <aside className={styles.sidebar}>
        <div className={styles.sidebarTitle}>Search</div>
        <input
          className={styles.search}
          type="text"
          placeholder="id or lean decl…"
          value={search}
          onChange={e => setSearch(e.target.value)}
        />

        <div className={styles.sidebarTitle}>Phase</div>
        <div className={styles.chips}>
          {ALL_PHASES.map(p => (
            <span
              key={p}
              className={`${styles.chip} ${activePhases.has(p) ? styles.chipActive : ''}`}
              onClick={() => togglePhase(p)}
              title={PHASE_LABELS[p]}
            >
              <span className={styles.chipDot} style={{ background: PHASE_COLORS[p] }} />
              {PHASE_LABELS[p]}
              <span className={styles.chipCount}>{phaseCounts[p] || 0}</span>
            </span>
          ))}
        </div>

        <div className={styles.sidebarTitle}>Chapter</div>
        <div className={styles.chips}>
          {allChapters.map(c => (
            <span
              key={c}
              className={`${styles.chip} ${activeChapters.has(c) ? styles.chipActive : ''}`}
              onClick={() => toggleChapter(c)}
            >
              {c}
              <span className={styles.chipCount}>{chapterCounts[c] || 0}</span>
            </span>
          ))}
        </div>

        <div className={styles.sidebarTitle}>Shapes</div>
        <div className={styles.legend}>
          <div className={styles.legendRow}><span className={`${styles.legendShape} ${styles.ellipse}`} />definition / notation</div>
          <div className={styles.legendRow}><span className={`${styles.legendShape} ${styles.round}`} />theorem / prop / lemma / cor</div>
          <div className={styles.legendRow}><span className={`${styles.legendShape} ${styles.rect}`} />axiom</div>
          <div className={styles.legendRow}><span className={`${styles.legendShape} ${styles.hex}`} />remark / question / example</div>
        </div>

        <div className={styles.sidebarTitle}>Edges</div>
        <div className={styles.legend}>
          <div className={styles.legendRow}>solid → confirmed dependency</div>
          <div className={styles.legendRow}>dashed → unconfirmed (default)</div>
        </div>
      </aside>

      <div className={styles.canvas}>
        <div className={styles.canvasInner} ref={containerRef} />
        <div className={styles.canvasOverlay}>
          showing {visibleIds.size} / {graph.nodes.length} nodes
        </div>
      </div>

      {selectedId && (
        <div className={styles.drawer}>
          <NodeDetail
            nodeId={selectedId}
            onClose={() => { setSelectedId(''); navigate('/nodes'); }}
            onSelectNode={(id) => { setSelectedId(id); navigate(`/nodes/${encodeURIComponent(id)}`); }}
          />
        </div>
      )}
    </div>
  );
}
