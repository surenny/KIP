// Lazy MathJax v3 loader. Mirrors the config blueprint's web pages use so
// rendered LaTeX blocks coming from blueprint/web/sec-*.html typeset identically.

interface MathJaxV3 {
  startup?: { promise?: Promise<void> };
  typesetPromise?: (elements?: HTMLElement[]) => Promise<void>;
  typesetClear?: (elements?: HTMLElement[]) => void;
}

declare global {
  interface Window {
    MathJax?: MathJaxV3 | Record<string, unknown>;
  }
}

let loadPromise: Promise<void> | null = null;

export function ensureMathJax(): Promise<void> {
  if (loadPromise) return loadPromise;
  if (typeof window === 'undefined') return Promise.resolve();

  loadPromise = new Promise<void>((resolve) => {
    // Configure BEFORE the script loads (this is how MathJax v3 picks up config).
    (window as Window).MathJax = {
      tex: { inlineMath: [['$', '$'], ['\\(', '\\)']] },
      startup: { typeset: false },
    };
    const s = document.createElement('script');
    // Pin to a specific patch (the bare `mathjax@3` tag rolls forward).
    s.src = 'https://cdn.jsdelivr.net/npm/mathjax@3.2.2/es5/tex-chtml.js';
    s.async = true;
    s.onload = () => {
      const mj = window.MathJax as MathJaxV3 | undefined;
      const startup = mj?.startup?.promise;
      if (startup) startup.then(() => resolve()).catch(() => resolve());
      else resolve();
    };
    s.onerror = () => resolve();  // give up silently; raw HTML still shows
    document.head.appendChild(s);
  });
  return loadPromise;
}

export async function typesetMath(el: HTMLElement | null): Promise<void> {
  if (!el) return;
  await ensureMathJax();
  const mj = window.MathJax as MathJaxV3 | undefined;
  if (mj?.typesetPromise) {
    try { await mj.typesetPromise([el]); } catch { /* ignore typeset errors */ }
  }
}
