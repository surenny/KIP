function getBaseUrl(): string {
  const base = import.meta.env.BASE_URL ?? '/';
  if (base === './' || base === '.') {
    let loc = window.location.pathname;
    const proxyMatch = loc.match(/^(.*\/proxy\/\d+\/)/);
    if (proxyMatch) return proxyMatch[1];
    if (loc.includes('.') && !loc.endsWith('/')) {
      loc = loc.substring(0, loc.lastIndexOf('/') + 1);
    }
    return loc.endsWith('/') ? loc : loc + '/';
  }
  return base.endsWith('/') ? base : base + '/';
}

export const BASE_URL = getBaseUrl();

export function apiUrl(path: string): string {
  const rel = path.startsWith('/') ? path.slice(1) : path;
  return BASE_URL + rel;
}

export function wsUrl(path: string): string {
  const proto = location.protocol === 'https:' ? 'wss:' : 'ws:';
  const rel = path.startsWith('/') ? path.slice(1) : path;
  return `${proto}//${location.host}${BASE_URL}${rel}`;
}

export const STATUS_COLORS: Record<string, string> = {
  done: 'var(--green)',
  running: 'var(--blue)',
  error: 'var(--red)',
  pending: 'var(--orange)',
};

// Phase = node lifecycle stage (drafted → proved). Ordered cool→warm→green.
// nl_reviewed implicitly includes "dependency edges confirmed" — they're not
// tracked separately in status.yaml.
export const PHASE_COLORS: Record<string, string> = {
  drafted:     '#c9ccd1',  // gray — only NL skeleton
  nl_reviewed: '#6f42c1',  // purple — NL + deps signed off
  bound:       '#0366d6',  // blue — Lean decl exists (sorry-stub OK)
  aligned:     '#e36209',  // orange — humans confirm Lean ↔ NL match
  proved:      '#28a745',  // green — sorry filled, build green
};

export const PHASE_ORDER = ['drafted', 'nl_reviewed', 'bound', 'aligned', 'proved'] as const;

export const PHASE_LABELS: Record<string, string> = {
  drafted: 'Drafted',
  nl_reviewed: 'NL reviewed',
  bound: 'Bound',
  aligned: 'Aligned',
  proved: 'Proved',
};

// Cytoscape node shapes per LaTeX kind. Splits things into 3 visual buckets:
// data (definition/notation) · claim (theorem/prop/lemma/corollary) · meta (axiom/remark/...)
export const KIND_SHAPES: Record<string, string> = {
  definition:  'ellipse',
  notation:    'ellipse',
  theorem:     'round-rectangle',
  proposition: 'round-rectangle',
  lemma:       'round-rectangle',
  corollary:   'round-rectangle',
  axiom:       'rectangle',
  remark:      'hexagon',
  question:    'vee',
  example:     'triangle',
};
