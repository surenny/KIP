// Tiny Lean-4 highlighter — enough for the dashboard's read-only "Lean
// declaration" preview, not enough to be a real grammar. Comments, strings,
// attributes, numbers, and a curated keyword/tactic list get span-wrapped;
// everything else passes through as plain text.
//
// Known approximations (matching the indexer's regex heuristics):
//   * block comments aren't nested — `/-` and `-/` are treated as a flat pair
//   * unicode identifiers fall through unhighlighted (keyword set is ASCII)
//   * tactic-mode is not distinguished from term-mode; we just colour any
//     occurrence of a known tactic name. False positives in identifier-like
//     positions are tolerated for readability.

const KEYWORDS = new Set<string>([
  // top-level / structuring
  'import', 'open', 'export', 'namespace', 'section', 'end',
  'variable', 'variables', 'universe', 'universes',
  'mutual', 'private', 'protected', 'noncomputable', 'partial', 'unsafe',
  'attribute', 'local', 'scoped', 'syntax', 'macro', 'macro_rules',
  'elab', 'elab_rules',
  // declarations
  'theorem', 'lemma', 'def', 'abbrev', 'axiom',
  'structure', 'class', 'instance', 'inductive', 'coinductive',
  'example', 'opaque',
  // term-level
  'where', 'with', 'match', 'fun', 'if', 'then', 'else',
  'do', 'let', 'in', 'from', 'return',
  'have', 'show', 'suffices',
  // tactics that appear often in our codebase
  'by', 'sorry', 'admit', 'rfl',
  'refine', 'exact', 'apply', 'intro', 'intros',
  'cases', 'induction', 'rcases', 'rintro', 'obtain', 'use',
  'simp', 'rw', 'rewrite', 'calc', 'decide', 'omega', 'linarith',
  'aesop', 'ring', 'field_simp', 'norm_num', 'gcongr', 'positivity',
  'constructor', 'left', 'right', 'split', 'contradiction',
  'first', 'all_goals', 'any_goals', 'try', 'repeat',
  // sorts and well-known constants
  'Type', 'Sort', 'Prop', 'True', 'False',
]);

function escHtml(s: string): string {
  return s
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

// One regex, ordered by priority. Comments and strings come first so a
// keyword-looking word inside them isn't separately matched.
const TOKEN_RE = new RegExp(
  [
    /(\/-[\s\S]*?-\/)/.source,                 // 1: block comment
    /(--[^\n]*)/.source,                       // 2: line comment
    /("(?:[^"\\]|\\.)*")/.source,              // 3: string literal
    /(@\[[^\]]*\])/.source,                    // 4: attribute  e.g. @[simp]
    /(\b[A-Za-z_][A-Za-z_0-9']*\b)/.source,    // 5: ascii ident / keyword
    /(\b\d+(?:\.\d+)?\b)/.source,              // 6: number literal
  ].join('|'),
  'g',
);

export function highlightLean(src: string): string {
  let out = '';
  let last = 0;
  let m: RegExpExecArray | null;
  TOKEN_RE.lastIndex = 0;
  while ((m = TOKEN_RE.exec(src)) !== null) {
    if (m.index > last) out += escHtml(src.slice(last, m.index));
    if (m[1] !== undefined || m[2] !== undefined) {
      out += `<span class="lean-c">${escHtml(m[0])}</span>`;
    } else if (m[3] !== undefined) {
      out += `<span class="lean-s">${escHtml(m[0])}</span>`;
    } else if (m[4] !== undefined) {
      out += `<span class="lean-a">${escHtml(m[0])}</span>`;
    } else if (m[5] !== undefined) {
      const w = m[5];
      out += KEYWORDS.has(w)
        ? `<span class="lean-k">${escHtml(w)}</span>`
        : escHtml(w);
    } else if (m[6] !== undefined) {
      out += `<span class="lean-n">${escHtml(m[0])}</span>`;
    } else {
      out += escHtml(m[0]);
    }
    last = m.index + m[0].length;
  }
  if (last < src.length) out += escHtml(src.slice(last));
  return out;
}
