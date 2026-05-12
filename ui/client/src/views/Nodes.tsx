import { useEffect, useMemo, useRef, useState } from 'react';
import { useNavigate, useParams } from 'react-router-dom';
import svgPanZoom from 'svg-pan-zoom';
import { useGraph, useGraphSvg } from '../hooks/useApi';
import { PHASE_COLORS, PHASE_ORDER, PHASE_LABELS } from '../utils/constants';
import NodeDetail from '../components/NodeDetail';
import type { Phase } from '../types';
import styles from './Nodes.module.css';

const ALL_PHASES = [...PHASE_ORDER];

const DRAWER_WIDTH_KEY = 'kip:drawerWidth';
const DRAWER_MIN_PX = 320;
const DRAWER_MAX_PX = 1100;
const DRAWER_DEFAULT_PX = 420;

function readSavedDrawerWidth(): number {
  if (typeof window === 'undefined') return DRAWER_DEFAULT_PX;
  const v = parseInt(window.localStorage.getItem(DRAWER_WIDTH_KEY) || '', 10);
  if (Number.isFinite(v) && v >= DRAWER_MIN_PX && v <= DRAWER_MAX_PX) return v;
  return DRAWER_DEFAULT_PX;
}

export default function Nodes() {
  const { id: routeId } = useParams<{ id?: string }>();
  const navigate = useNavigate();
  const containerRef = useRef<HTMLDivElement | null>(null);
  const panZoomRef = useRef<SvgPanZoom.Instance | null>(null);
  const drawerRef = useRef<HTMLDivElement | null>(null);
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
  const [drawerWidth, setDrawerWidth] = useState<number>(readSavedDrawerWidth);
  // Mobile-only: filter sidebar collapses into a slide-in drawer behind a
  // toggle button. Desktop CSS hides the toggle and keeps the sidebar
  // statically docked, so this state has no visual effect there.
  const [mobileSidebarOpen, setMobileSidebarOpen] = useState(false);

  // Persist drawer width across page loads.
  useEffect(() => {
    try { window.localStorage.setItem(DRAWER_WIDTH_KEY, String(drawerWidth)); } catch { /* ignore */ }
  }, [drawerWidth]);

  const startDrawerResize = (e: React.MouseEvent<HTMLDivElement>) => {
    e.preventDefault();
    const startX = e.clientX;
    const startW = drawerWidth;
    const onMove = (ev: MouseEvent) => {
      // Drawer is anchored to the right; dragging the handle leftwards
      // (smaller clientX) grows the drawer. Clamp to avoid degenerate widths.
      const next = Math.max(DRAWER_MIN_PX, Math.min(DRAWER_MAX_PX, startW + (startX - ev.clientX)));
      setDrawerWidth(next);
    };
    const onUp = () => {
      document.removeEventListener('mousemove', onMove);
      document.removeEventListener('mouseup', onUp);
      document.body.style.cursor = '';
      document.body.style.userSelect = '';
    };
    // Lock the cursor + disable text selection while dragging — without
    // these, fast drags pick up arbitrary text on the page.
    document.body.style.cursor = 'col-resize';
    document.body.style.userSelect = 'none';
    document.addEventListener('mousemove', onMove);
    document.addEventListener('mouseup', onUp);
  };

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

  // Close mobile filter drawer whenever a node opens — the detail drawer
  // takes the full screen on mobile and would otherwise overlap the open
  // filter panel.
  useEffect(() => {
    if (selectedId) setMobileSidebarOpen(false);
  }, [selectedId]);

  // On mobile, the user may pinch-zoom the page to read node labels. When
  // the drawer opens, counter-scale it so it renders at 1x regardless of
  // the current browser zoom level.
  useEffect(() => {
    const el = drawerRef.current;
    const vv = window.visualViewport;
    if (!el || !vv || !selectedId) return;

    const sync = () => {
      const scale = vv.scale;
      if (scale > 1.05) {
        el.style.transform = `scale(${1 / scale})`;
        el.style.transformOrigin = 'top left';
        el.style.width = `${vv.width * scale}px`;
        el.style.height = `${vv.height * scale}px`;
        el.style.left = `${vv.offsetLeft}px`;
        el.style.top = `${vv.offsetTop}px`;
      } else {
        el.style.transform = '';
        el.style.transformOrigin = '';
        el.style.width = '';
        el.style.height = '';
        el.style.left = '';
        el.style.top = '';
      }
    };

    sync();
    vv.addEventListener('resize', sync);
    vv.addEventListener('scroll', sync);
    return () => {
      vv.removeEventListener('resize', sync);
      vv.removeEventListener('scroll', sync);
      el.style.transform = '';
      el.style.transformOrigin = '';
      el.style.width = '';
      el.style.height = '';
      el.style.left = '';
      el.style.top = '';
    };
  }, [selectedId]);

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
      // Background click is a no-op: closing the drawer should be an
      // explicit action (the close button or Escape), since users routinely
      // pan the canvas with click-drag and would otherwise lose context.
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
      dblClickZoomEnabled: false,
      fit: isFirstMount,
      center: isFirstMount,
      mouseWheelZoomEnabled: true,
      preventMouseEventsDefault: false,
      minZoom: 0.2,
      maxZoom: 50,
      zoomScaleSensitivity: 0.5,
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

  // Highlight edges incident to the selected node. Edge group ids are emitted
  // by the server as `edge:<from>-><to>` (where the DB direction is preserved
  // even though DOT renders the arrow flipped). Outgoing in the data sense
  // (from === selectedId) means "selectedId uses ..." and incoming
  // (to === selectedId) means "... uses selectedId" — coloured separately so
  // both flow directions are legible at a glance.
  useEffect(() => {
    const container = containerRef.current;
    if (!container) return;
    container.querySelectorAll('g.kip-edge-uses, g.kip-edge-usedby').forEach(el => {
      el.classList.remove('kip-edge-uses');
      el.classList.remove('kip-edge-usedby');
    });
    if (!selectedId) return;
    const edges = container.querySelectorAll<SVGGElement>('g.edge[id^="edge:"]');
    edges.forEach(el => {
      const id = el.getAttribute('id') || '';
      const rest = id.slice('edge:'.length);
      const arrow = rest.indexOf('->');
      if (arrow < 0) return;
      const from = rest.slice(0, arrow);
      const to = rest.slice(arrow + 2);
      if (from === selectedId) {
        el.classList.add('kip-edge-uses');
        // Re-append so the highlighted stroke paints over neighbouring
        // edges instead of being hidden under them.
        el.parentNode?.appendChild(el);
      } else if (to === selectedId) {
        el.classList.add('kip-edge-usedby');
        el.parentNode?.appendChild(el);
      }
    });
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
      {!selectedId && (
        <button
          type="button"
          className={styles.mobileFilterToggle}
          onClick={() => setMobileSidebarOpen(v => !v)}
          aria-expanded={mobileSidebarOpen}
          aria-label="Toggle filters"
        >
          ☰ Filters
        </button>
      )}
      {mobileSidebarOpen && (
        <button
          type="button"
          className={styles.mobileBackdrop}
          onClick={() => setMobileSidebarOpen(false)}
          aria-label="Close filters"
        />
      )}
      <aside className={`${styles.sidebar} ${mobileSidebarOpen ? styles.mobileSidebarOpen : ''}`}>
        <div className={styles.sidebarTitle}>Search</div>
        <input
          className={styles.search}
          type="text"
          placeholder="id or substring…"
          value={search}
          onChange={e => setSearch(e.target.value)}
          autoComplete="off"
          autoCorrect="off"
          autoCapitalize="off"
          spellCheck={false}
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
          <div className={styles.legendRow}>rounded box — theorem / proposition / lemma / corollary</div>
          <div className={styles.legendRow}>diamond — axiom</div>
        </div>

        <div className={styles.sidebarTitle}>Edges</div>
        <div className={styles.legend}>
          <div className={styles.legendRow}>top → bottom = build order</div>
          <div className={styles.legendRow}>arrow A → B reads "A is used by B"</div>
          <div className={styles.legendRow}>
            <span className={styles.legendSwatch} style={{ background: '#0366d6' }} />
            on select: this node's <em>uses</em>
          </div>
          <div className={styles.legendRow}>
            <span className={styles.legendSwatch} style={{ background: '#e36209' }} />
            on select: <em>used by</em> this node
          </div>
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
        <div className={styles.zoomControls}>
          <button type="button" onClick={() => panZoomRef.current?.zoomIn()} aria-label="Zoom in">+</button>
          <button type="button" onClick={() => panZoomRef.current?.zoomOut()} aria-label="Zoom out">−</button>
          <button type="button" onClick={() => { panZoomRef.current?.fit(); panZoomRef.current?.center(); }} aria-label="Fit to view">⤢</button>
        </div>
      </div>

      {selectedId && (
        <div className={styles.drawer} ref={drawerRef} style={{ width: drawerWidth }}>
          <div
            className={styles.drawerResize}
            onMouseDown={startDrawerResize}
            role="separator"
            aria-orientation="vertical"
            aria-label="Resize drawer"
            title="Drag to resize"
          />
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
