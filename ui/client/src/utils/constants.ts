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
