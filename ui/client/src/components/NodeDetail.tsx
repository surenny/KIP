import { useEffect, useRef, useState } from 'react';
import { useNode, useReviewAction, type ReviewAction } from '../hooks/useApi';
import { PHASE_COLORS, PHASE_LABELS } from '../utils/constants';
import { fmtDuration } from '../utils/format';
import { typesetMath } from '../utils/mathjax';
import { highlightLean } from '../utils/leanHighlight';
import type { NodeDetail as NodeDetailT, NodeFlags } from '../types';
import styles from './NodeDetail.module.css';

const REVIEWER_STORAGE_KEY = 'kip:reviewer';

const FLAG_DISPLAY: { key: keyof NodeFlags; label: string }[] = [
  { key: 'nlReviewed', label: 'NL'     },
  { key: 'bound',      label: 'Bound'  },
  { key: 'aligned',    label: 'Align'  },
  { key: 'proved',     label: 'Proved' },
];

// Render an `at` value in Beijing time. Date-only legacy entries pass through
// unchanged (already read as 'YYYY-MM-DD'); full ISO datetimes are formatted
// as 'YYYY-MM-DD HH:mm' in Asia/Shanghai. `sv-SE` locale gives an unambiguous,
// ISO-shaped output.
const beijingFmt = new Intl.DateTimeFormat('sv-SE', {
  timeZone: 'Asia/Shanghai',
  year: 'numeric', month: '2-digit', day: '2-digit',
  hour: '2-digit', minute: '2-digit', hour12: false,
});
function fmtAt(iso: string | null | undefined): string {
  if (!iso) return '';
  if (!iso.includes('T')) return iso;
  const t = Date.parse(iso);
  if (isNaN(t)) return iso;
  return beijingFmt.format(new Date(t));
}

// Show a relative time when we have a precise instant, otherwise fall back to
// the date string as-is. Date-only legacy entries (like '2026-04-19') lack
// time information — guessing midnight in *any* zone is a lie that misleads
// users by 8–16h, so we just show the date and let them eyeball recency.
function fmtRelTime(iso: string | null | undefined): string {
  if (!iso) return '';
  if (!iso.includes('T')) return iso;
  const t = Date.parse(iso);
  if (isNaN(t)) return iso;
  const diff = Date.now() - t;
  if (diff < 0) return fmtAt(iso);
  const s = Math.floor(diff / 1000);
  if (s < 5) return 'just now';
  if (s < 60) return `${s}s ago`;
  const m = Math.floor(s / 60);
  if (m < 60) return `${m}m ago`;
  const h = Math.floor(m / 60);
  if (h < 48) return `${h}h ago`;
  const d = Math.floor(h / 24);
  // Beyond 72h, "Nd ago" loses the precision needed to compare two old
  // comments — show the absolute Beijing-time stamp instead.
  if (d < 3) return `${d}d ago`;
  return fmtAt(iso);
}

interface Props {
  nodeId: string;
  onClose: () => void;
  onSelectNode: (id: string) => void;
}

export default function NodeDetail({ nodeId, onClose, onSelectNode }: Props) {
  const { data, isLoading, isError } = useNode(nodeId);
  const renderedRef = useRef<HTMLDivElement | null>(null);

  const [reviewer, setReviewer] = useState<string>(() =>
    (typeof window !== 'undefined' && window.localStorage.getItem(REVIEWER_STORAGE_KEY)) || ''
  );
  const [reviewComment, setReviewComment] = useState<string>('');
  const review = useReviewAction();

  // Persist reviewer across reloads (also across drawer reopens for the same
  // browser session). We trim before storing so stray spaces don't follow.
  useEffect(() => {
    const v = reviewer.trim();
    if (v) window.localStorage.setItem(REVIEWER_STORAGE_KEY, v);
  }, [reviewer]);

  // Clear the comment box and mutation state when switching nodes — comments
  // are scoped to a specific approval, never carried across.
  useEffect(() => {
    setReviewComment('');
    review.reset();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [nodeId]);

  // Same reset after a successful submit — but keep the reviewer name.
  useEffect(() => {
    if (review.isSuccess) {
      setReviewComment('');
      const t = setTimeout(() => review.reset(), 1500);
      return () => clearTimeout(t);
    }
  }, [review.isSuccess, review]);

  useEffect(() => {
    // re-run MathJax whenever the rendered block changes
    typesetMath(renderedRef.current);
  }, [data?.nlRendered?.contentHtml]);

  if (isLoading) {
    return <div className={styles.root}><div className={styles.section}>Loading…</div></div>;
  }
  if (isError || !data) {
    return (
      <div className={styles.root}>
        <div className={styles.header}>
          <div className={styles.idRow}>
            <span className={styles.id}>{nodeId}</span>
            <button onClick={onClose} style={{ marginLeft: 'auto', cursor: 'pointer', border: 'none', background: 'transparent', fontSize: 16, color: 'var(--text-muted)' }}>×</button>
          </div>
        </div>
        <div className={styles.section}>Node not found in index. Try re-running <code>python tools/kip-state/index.py</code>.</div>
      </div>
    );
  }

  const d = data as NodeDetailT;
  const phaseColor = PHASE_COLORS[d.phase] || '#999';

  return (
    <div className={styles.root}>
      <div className={styles.header}>
        <div className={styles.idRow}>
          <span className={styles.id}>{d.id}</span>
          <button onClick={onClose}
                  style={{ marginLeft: 'auto', cursor: 'pointer', border: 'none', background: 'transparent', fontSize: 18, color: 'var(--text-muted)', lineHeight: 1 }}
                  aria-label="Close">×</button>
        </div>
        <div className={styles.subline}>
          {d.kind && <span className={styles.kindChip}>{d.kind}</span>}{' '}
          {d.chapter && <span>· {d.chapter}</span>}
          {d.sourceFile && d.sourceLine != null && (
            <span> · {d.sourceFile.split('/').slice(-1)[0]}:{d.sourceLine}</span>
          )}
        </div>
        <div className={styles.phaseBadge} style={{ background: phaseColor }}>
          {PHASE_LABELS[d.phase] || d.phase}
          {d.lastActivity && <span style={{ opacity: 0.85, fontSize: 11, fontWeight: 400 }}>· {fmtRelTime(d.lastActivity)}</span>}
        </div>
      </div>

      <div className={styles.section}>
        <div className={styles.sectionLabel}>Lifecycle</div>
        <div className={styles.flagsGrid}>
          {FLAG_DISPLAY.map(f => {
            const on = d.flags[f.key];
            return (
              <div key={f.key} className={`${styles.flag} ${on ? styles.flagOn : ''}`}>
                <span className={styles.flagMark}>{on ? '✓' : '·'}</span>
                <span className={styles.flagText}>{f.label}</span>
              </div>
            );
          })}
        </div>
        {(d.nlReviewer || d.alignReviewer) && (
          <div className={styles.attribution}>
            {d.nlReviewer && (
              <div>NL reviewed by <b>{d.nlReviewer}</b></div>
            )}
            {d.alignReviewer && (
              <div>
                Aligned by <b>{d.alignReviewer}</b>
                {d.alignedAt ? ` · ${fmtAt(d.alignedAt)}` : ''}
              </div>
            )}
          </div>
        )}
      </div>

      {(() => {
        const canApproveNL = !d.flags.nlReviewed;
        const canConfirmAlign = d.flags.nlReviewed && d.flags.bound && !d.flags.aligned;
        if (!canApproveNL && !canConfirmAlign) return null;
        const action: ReviewAction = canApproveNL ? 'approve_nl' : 'confirm_alignment';
        const title = canApproveNL ? 'Approve NL' : 'Confirm alignment';
        const hint = canApproveNL
          ? 'Confirm the natural-language statement is correct as written. This advances phase from drafted → nl_reviewed.'
          : 'Confirm the Lean declaration faithfully formalizes the NL statement. Advances phase from bound → aligned.';
        const placeholder = canApproveNL
          ? 'optional: notes for the review log (e.g. "matches §3.2 wording")'
          : 'optional: alignment notes (e.g. "types match, p/q convention as in NL")';
        const reviewerOk = reviewer.trim().length > 0;
        const submit = (e: React.FormEvent) => {
          e.preventDefault();
          if (!reviewerOk || review.isPending) return;
          review.mutate({
            nodeId: d.id,
            action,
            reviewer: reviewer.trim(),
            comment: reviewComment.trim() || undefined,
          });
        };
        return (
          <div className={styles.section}>
            <div className={styles.sectionLabel}>Review</div>
            <div className={styles.reviewHint}>{hint}</div>
            <form className={styles.reviewForm} onSubmit={submit}>
              <label className={styles.reviewerLabel}>
                Reviewing as
                <input
                  type="text"
                  className={styles.reviewerInput}
                  placeholder="your name"
                  value={reviewer}
                  onChange={e => setReviewer(e.target.value)}
                />
              </label>
              <textarea
                className={styles.reviewCommentBox}
                placeholder={placeholder}
                value={reviewComment}
                onChange={e => setReviewComment(e.target.value)}
                rows={2}
              />
              <button
                type="submit"
                className={styles.reviewBtn}
                disabled={!reviewerOk || review.isPending}
              >
                {review.isPending ? 'Submitting…' : title}
              </button>
              {review.isError && (
                <div className={styles.reviewError}>
                  {(review.error as Error)?.message || 'Submit failed'}
                </div>
              )}
              {review.isSuccess && (
                <div className={styles.reviewOk}>✓ Recorded</div>
              )}
            </form>
          </div>
        );
      })()}

      {d.leanDecl && (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>
            Lean declaration
            <span
              className={styles.betaBadge}
              title={'Source slice + highlighting are regex-based, not a real Lean parser. ' +
                     'Boundaries follow next-decl-heading; nested block comments and unicode ' +
                     'identifiers may render imperfectly.'}
            >
              beta
            </span>
          </div>
          <div className={styles.leanBox}>
            <div className={styles.leanRow}>
              <span className={styles.leanKey}>name</span>
              <span className={styles.leanVal}>{d.leanDecl.name}</span>
            </div>
            <div className={styles.leanRow}>
              <span className={styles.leanKey}>file</span>
              <span className={styles.leanVal}>{d.leanDecl.file}:{d.leanDecl.line_start}</span>
            </div>
            <div className={styles.leanRow}>
              <span className={styles.leanKey}>sorry</span>
              <span className={styles.leanVal}>
                <span className={`${styles.sorryDot} ${d.leanDecl.sorry_count === 0 ? styles.green : styles.orange}`}></span>
                {d.leanDecl.sorry_count}
              </span>
            </div>
          </div>
          {d.leanSource ? (
            <pre
              className={styles.leanSource}
              dangerouslySetInnerHTML={{ __html: highlightLean(d.leanSource) }}
            />
          ) : (
            <div className={styles.empty}>
              source unavailable (file moved or out-of-range — rebuild state.db)
            </div>
          )}
        </div>
      )}
      {d.leanDecl == null && d.leanDecl !== undefined && d.flags.bound && (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>Lean declaration</div>
          <div className={styles.empty}>Marked bound, but no matching declaration in KIP/. Likely external (mathlib) or stale.</div>
        </div>
      )}

      {d.nlRendered ? (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>
            {d.nlRendered.caption || d.kind || 'NL'}
            {d.nlRendered.label && <> · {d.nlRendered.label}</>}
          </div>
          <div
            ref={renderedRef}
            className={styles.rendered}
            dangerouslySetInnerHTML={{ __html: d.nlRendered.contentHtml }}
          />
        </div>
      ) : d.nlExcerpt ? (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>NL source ({d.kind}) — raw, no rendered HTML found</div>
          <pre className={styles.excerpt}>{d.nlExcerpt}</pre>
        </div>
      ) : null}

      <details className={styles.section}>
        <summary className={styles.sectionLabel}>Uses ({d.uses.length})</summary>
        {d.uses.length === 0 ? <div className={styles.empty}>No outgoing dependencies.</div> :
          d.uses.map(e => (
            <div key={e.id} className={styles.refLine}>
              <a className={styles.refLink} onClick={() => onSelectNode(e.id)}>
                <code>{e.id}</code>
              </a>
            </div>
          ))
        }
      </details>

      <details className={styles.section}>
        <summary className={styles.sectionLabel}>Used by ({d.usedBy.length})</summary>
        {d.usedBy.length === 0 ? <div className={styles.empty}>Leaf node (nothing uses this).</div> :
          d.usedBy.map(e => (
            <div key={e.id} className={styles.refLine}>
              <a className={styles.refLink} onClick={() => onSelectNode(e.id)}>
                <code>{e.id}</code>
              </a>
            </div>
          ))
        }
      </details>

      <div className={styles.section}>
        <div className={styles.sectionLabel}>Comments ({d.comments.length})</div>
        {d.comments.length === 0 ? <div className={styles.empty}>No comments yet.</div> :
          <div className={styles.commentsList}>
            {d.comments.map(c => (
              <div key={c.idx} className={styles.commentItem}>
                <div className={styles.commentMeta}>
                  {c.topic && <span className={styles.commentTopic}>{c.topic}</span>}
                  <span>{c.by || 'anonymous'}{c.at ? ` · ${fmtAt(c.at)}` : ''}</span>
                </div>
                <div className={styles.commentText}>{c.text}</div>
              </div>
            ))}
          </div>
        }
      </div>

      <details className={styles.section}>
        <summary className={styles.sectionLabel}>Agent runs touching this node ({d.runs.length})</summary>
        {d.runs.length === 0 ? <div className={styles.empty}>No agent runs reference this node.</div> :
          <div className={styles.runsList}>
            {d.runs.map(r => {
              const status = (r.status || 'unknown').toLowerCase();
              const statusClass = status === 'done' ? styles.done : status === 'running' ? styles.running : styles.error;
              return (
                <div key={r.id} className={styles.runItem}>
                  <div className={styles.runHeader}>
                    <span className={styles.runAgent}>{r.agent} · {r.model || '—'}</span>
                    <span className={`${styles.runStatus} ${statusClass}`}>{r.status || 'unknown'}</span>
                  </div>
                  <div className={styles.runMeta}>
                    {r.completed_at ? fmtRelTime(r.completed_at) : (r.started_at ? `started ${fmtRelTime(r.started_at)}` : '')}
                    {r.duration_ms ? ` · ${fmtDuration(r.duration_ms)}` : ''}
                    {r.cost_usd != null ? ` · $${r.cost_usd.toFixed(2)}` : ''}
                    {r.num_turns ? ` · ${r.num_turns} turns` : ''}
                  </div>
                  {r.hint_file && <div className={styles.runHint}>{r.hint_file}</div>}
                </div>
              );
            })}
          </div>
        }
      </details>
    </div>
  );
}
