import { useEffect, useRef } from 'react';
import { useNode } from '../hooks/useApi';
import { PHASE_COLORS, PHASE_LABELS } from '../utils/constants';
import { fmtDuration } from '../utils/format';
import { typesetMath } from '../utils/mathjax';
import type { NodeDetail as NodeDetailT, NodeFlags } from '../types';
import styles from './NodeDetail.module.css';

const FLAG_DISPLAY: { key: keyof NodeFlags; label: string }[] = [
  { key: 'nlReviewed', label: 'NL'     },
  { key: 'bound',      label: 'Bound'  },
  { key: 'aligned',    label: 'Align'  },
  { key: 'proved',     label: 'Proved' },
];

function fmtRelTime(iso: string | null | undefined): string {
  if (!iso) return '';
  const t = Date.parse(iso);
  if (isNaN(t)) return iso;
  const diff = Date.now() - t;
  if (diff < 0) return new Date(t).toLocaleString();
  const s = Math.floor(diff / 1000);
  if (s < 60) return `${s}s ago`;
  const m = Math.floor(s / 60);
  if (m < 60) return `${m}m ago`;
  const h = Math.floor(m / 60);
  if (h < 48) return `${h}h ago`;
  const d = Math.floor(h / 24);
  return `${d}d ago`;
}

interface Props {
  nodeId: string;
  onClose: () => void;
  onSelectNode: (id: string) => void;
}

export default function NodeDetail({ nodeId, onClose, onSelectNode }: Props) {
  const { data, isLoading, isError } = useNode(nodeId);
  const renderedRef = useRef<HTMLDivElement | null>(null);

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
      </div>

      {d.leanDecl && (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>Lean declaration</div>
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

      <div className={styles.section}>
        <div className={styles.sectionLabel}>Uses ({d.uses.length})</div>
        {d.uses.length === 0 ? <div className={styles.empty}>No outgoing dependencies.</div> :
          d.uses.map(e => (
            <div key={e.id} className={styles.refLine}>
              <a className={styles.refLink} onClick={() => onSelectNode(e.id)}>
                <code>{e.id}</code>
              </a>
            </div>
          ))
        }
      </div>

      <div className={styles.section}>
        <div className={styles.sectionLabel}>Used by ({d.usedBy.length})</div>
        {d.usedBy.length === 0 ? <div className={styles.empty}>Leaf node (nothing uses this).</div> :
          d.usedBy.map(e => (
            <div key={e.id} className={styles.refLine}>
              <a className={styles.refLink} onClick={() => onSelectNode(e.id)}>
                <code>{e.id}</code>
              </a>
            </div>
          ))
        }
      </div>

      <div className={styles.section}>
        <div className={styles.sectionLabel}>Comments ({d.comments.length})</div>
        {d.comments.length === 0 ? <div className={styles.empty}>No comments yet.</div> :
          <div className={styles.commentsList}>
            {d.comments.map(c => (
              <div key={c.idx} className={styles.commentItem}>
                <div className={styles.commentMeta}>
                  {c.topic && <span className={styles.commentTopic}>{c.topic}</span>}
                  <span>{c.by || 'anonymous'}{c.at ? ` · ${c.at}` : ''}</span>
                </div>
                <div className={styles.commentText}>{c.text}</div>
              </div>
            ))}
          </div>
        }
      </div>

      <div className={styles.section}>
        <div className={styles.sectionLabel}>Agent runs touching this node ({d.runs.length})</div>
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
      </div>
    </div>
  );
}
