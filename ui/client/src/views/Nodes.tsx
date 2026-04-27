import { useEffect, useMemo, useRef, useState } from 'react';
import { useNavigate, useParams } from 'react-router-dom';
import svgPanZoom from 'svg-pan-zoom';
import { useGraph, useGraphSvg } from '../hooks/useApi';
import { PHASE_COLORS, PHASE_ORDER, PHASE_LABELS } from '../utils/constants';
import NodeDetail from '../components/NodeDetail';
import type { Phase } from '../types';
import styles from './Nodes.module.css';

const ALL_PHASES = [...PHASE_ORDER];

export default function Nodes() {
  const { id: routeId } = useParams<{ id?: string }>();
  const navigate = useNavigate();
  const containerRef = useRef<HTMLDivElement | null>(null);
  const panZoomRef = useRef<SvgPanZoom.Instance | null>(null);
  // navigate's reference may not be perfectly stable across renders (or
  // an upstream provider re-render); keep it behind a ref so the SVG mount
  // effect doesn't fire just because navigate's identity changed —
  // re-initialising svg-pan-zoom with `fit:true,center:true` would reset
  // the user's current zoom/pan on every click.
  const navRef = useRef(navigate);
  useEffect(() => { navRef.current = navigate; }, [navigate]);

  const [selectedId, setSelectedId] = useState('');
  const [search, setSearch] = useState('');
  const [debouncedSearch, setDebouncedSearch] = useState('');
  const [activePhases, setActivePhases] = useState<Set<Phase>>(() => new Set<Phase>(ALL_PHASES));
  const [activeChapters, setActiveChapters] = useState<Set<string>>(() => new Set());
  const [chaptersInit, setChaptersInit] = useState(false);

  const { data: graph } = useGraph();

  // Debounce search → 300 ms before re-fetching SVG
  useEffect(() => {
    const t = setTimeout(() => setDebouncedSearch(search), 300);
    return () => clearTimeout(t);
  }, [search]);

  // Initialize chapter filter to "all chapters" once we know what they are.
  useEffect(() => {
    if (chaptersInit || !graph) return;
    setActiveChapters(new Set(graph.chapters));
    setChaptersInit(true);
  }, [graph, chaptersInit]);

  // URL → state sync (also clears selection when URL drops :id)
  useEffect(() => {
    const next = routeId || '';
    if (next !== selectedId) setSelectedId(next);
  }, [routeId, selectedId]);

  // Chapter chips render in content.tex order (server returns them already
  // sorted). Don't re-sort here.
  const allChapters = graph?.chapters ?? [];

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

  const phasesArr = useMemo(() => Array.from(activePhases), [activePhases]);
  // Preserve content.tex order in the query string so the cache key for
  // /api/graph/svg matches across renders regardless of toggle order.
  const chaptersArr = useMemo(
    () => (chaptersInit ? allChapters.filter(c => activeChapters.has(c)) : []),
    [allChapters, activeChapters, chaptersInit],
  );

  const { data: svgText, isFetching, isError } = useGraphSvg({
    phases: phasesArr,
    chapters: chaptersArr,
    q: debouncedSearch,
    enabled: chaptersInit,
  });

  // Mount the SVG, init pan-zoom, attach click bridging.
  useEffect(() => {
    const container = containerRef.current;
    if (!container || !svgText) return;
    container.innerHTML = svgText;
    const svgEl = container.querySelector('svg') as SVGSVGElement | null;
    if (!svgEl) return;

    // Let it stretch to its parent box; preserve viewBox aspect.
    svgEl.removeAttribute('width');
    svgEl.removeAttribute('height');
    svgEl.style.width = '100%';
    svgEl.style.height = '100%';
    svgEl.style.display = 'block';

    const onClick = (e: MouseEvent) => {
      let target = e.target as Element | null;
      while (target && target !== svgEl) {
        const id = target.getAttribute('id');
        if (id && id.startsWith('node:')) {
          const nodeId = id.slice('node:'.length);
          setSelectedId(nodeId);
          navRef.current(`/nodes/${encodeURIComponent(nodeId)}`);
          return;
        }
        target = target.parentElement;
      }
      // Background click → deselect
      setSelectedId('');
      navRef.current('/nodes');
    };
    svgEl.addEventListener('click', onClick);

    // Init pan-zoom. If a previous instance exists (filter change → new
    // SVG), preserve its pan/zoom across the re-init so users don't lose
    // context. fit/center only fire on the very first mount.
    let preservedZoom: number | null = null;
    let preservedPan: { x: number; y: number } | null = null;
    if (panZoomRef.current) {
      try {
        preservedZoom = panZoomRef.current.getZoom();
        preservedPan = panZoomRef.current.getPan();
      } catch { /* ignore */ }
      try { panZoomRef.current.destroy(); } catch { /* ignore */ }
      panZoomRef.current = null;
    }
    const isFirstMount = preservedZoom == null;
    panZoomRef.current = svgPanZoom(svgEl, {
      zoomEnabled: true,
      controlIconsEnabled: false,
      fit: isFirstMount,
      center: isFirstMount,
      mouseWheelZoomEnabled: true,
      preventMouseEventsDefault: false,
      minZoom: 0.2,
      maxZoom: 8,
      zoomScaleSensitivity: 0.4,
    });
    if (!isFirstMount && preservedZoom != null && preservedPan) {
      try {
        panZoomRef.current.zoom(preservedZoom);
        panZoomRef.current.pan(preservedPan);
      } catch { /* ignore */ }
    }

    return () => {
      svgEl.removeEventListener('click', onClick);
      if (panZoomRef.current) {
        try { panZoomRef.current.destroy(); } catch { /* ignore */ }
        panZoomRef.current = null;
      }
    };
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [svgText]);

  // Highlight selected node in SVG
  useEffect(() => {
    const container = containerRef.current;
    if (!container) return;
    container.querySelectorAll('g.kip-node-selected').forEach(el =>
      el.classList.remove('kip-node-selected'));
    if (!selectedId) return;
    const sel = `#${(window.CSS && CSS.escape) ? CSS.escape('node:' + selectedId) : 'node\\:' + selectedId.replace(/[^a-zA-Z0-9_-]/g, c => '\\' + c)}`;
    const el = container.querySelector(sel);
    if (el) el.classList.add('kip-node-selected');
  }, [selectedId, svgText]);

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

  const totalNodes = graph?.nodes.length ?? 0;

  return (
    <div className={`${styles.root} ${selectedId ? styles.drawerOpen : ''}`}>
      <aside className={styles.sidebar}>
        <div className={styles.sidebarTitle}>Search</div>
        <input
          className={styles.search}
          type="text"
          placeholder="id or substring…"
          value={search}
          onChange={e => setSearch(e.target.value)}
        />

        <div className={styles.sidebarTitle}>Phase</div>
        <div className={styles.chips}>
          {ALL_PHASES.map(p => (
            <button
              key={p}
              type="button"
              className={`${styles.chip} ${activePhases.has(p) ? styles.chipActive : ''}`}
              onClick={() => togglePhase(p)}
              title={PHASE_LABELS[p]}
            >
              <span className={styles.chipDot} style={{ background: PHASE_COLORS[p] }} />
              {PHASE_LABELS[p]}
              <span className={styles.chipCount}>{phaseCounts[p] || 0}</span>
            </button>
          ))}
        </div>

        <div className={styles.sidebarTitle}>Chapter</div>
        <div className={styles.chips}>
          {allChapters.map(c => (
            <button
              key={c}
              type="button"
              className={`${styles.chip} ${activeChapters.has(c) ? styles.chipActive : ''}`}
              onClick={() => toggleChapter(c)}
            >
              {c}
              <span className={styles.chipCount}>{chapterCounts[c] || 0}</span>
            </button>
          ))}
        </div>

        <div className={styles.sidebarTitle}>Shapes</div>
        <div className={styles.legend}>
          <div className={styles.legendRow}>ellipse — definition / notation</div>
          <div className={styles.legendRow}>rounded box — theorem / prop / lemma / cor / axiom</div>
          <div className={styles.legendRow}>hexagon — remark</div>
          <div className={styles.legendRow}>triangles — example / question</div>
        </div>

        <div className={styles.sidebarTitle}>Edges</div>
        <div className={styles.legend}>
          <div className={styles.legendRow}>top → bottom = build order</div>
          <div className={styles.legendRow}>arrow A → B reads "A is used by B"</div>
        </div>
      </aside>

      <div className={styles.canvas}>
        <div className={styles.canvasInner} ref={containerRef} />
        <div className={styles.canvasOverlay}>
          {isFetching && 'rendering… '}
          {isError && 'render failed (check server log)'}
          {!isFetching && !isError && (
            <>graph rendered server-side via <code>dot</code> · {totalNodes} nodes total</>
          )}
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
