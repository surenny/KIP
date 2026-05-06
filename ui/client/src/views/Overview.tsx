import { useNavigate } from 'react-router-dom';
import { useGraph, useStateHealth, useSummary } from '../hooks/useApi';
import { PHASE_COLORS, PHASE_ORDER, PHASE_LABELS } from '../utils/constants';
import { fmtDuration } from '../utils/format';
import type { NodeData, Phase } from '../types';
import styles from './Overview.module.css';

const STALE_DAYS = 14;

function daysAgo(iso: string | null | undefined): number | null {
  if (!iso) return null;
  const t = Date.parse(iso);
  if (isNaN(t)) return null;
  return (Date.now() - t) / 86_400_000;
}

function isStaleInPhase(n: NodeData): boolean {
  if (n.phase === 'proved') return false;
  if (!n.chapter) return false;
  const d = daysAgo(n.lastActivity);
  return d == null || d >= STALE_DAYS;
}

export default function Overview() {
  const navigate = useNavigate();
  const { data: graph } = useGraph();
  const { data: health } = useStateHealth();
  const { data: summary } = useSummary();

  if (!health || !health.ok) {
    return (
      <div className={styles.root}>
        <h2 className={styles.title}>State index unavailable</h2>
        <div className={styles.empty}>
          {health?.error || 'Run python tools/kip-state/index.py to build .kip/state.db.'}
        </div>
      </div>
    );
  }

  const phaseCounts: Record<string, number> = { ...(health.phases || {}) };
  const total = Object.values(phaseCounts).reduce((a, b) => a + b, 0) || 1;

  const stale = (graph?.nodes || []).filter(isStaleInPhase)
    .sort((a, b) => {
      const da = daysAgo(a.lastActivity) ?? Number.POSITIVE_INFINITY;
      const db = daysAgo(b.lastActivity) ?? Number.POSITIVE_INFINITY;
      return db - da;
    })
    .slice(0, 20);

  const indexedAt = health.meta?.indexed_at;

  return (
    <div className={styles.root}>
      <h2 className={styles.title}>KIP — node lifecycle</h2>

      <div className={styles.section}>
        <div className={styles.sectionLabel}>Phase distribution ({total} nodes)</div>
        <div style={{ display: 'flex', height: 24, borderRadius: 4, overflow: 'hidden', border: '1px solid var(--border)' }}>
          {PHASE_ORDER.map(p => {
            const c = phaseCounts[p] || 0;
            const pct = (c / total) * 100;
            if (pct < 0.1) return null;
            return (
              <div key={p}
                   title={`${PHASE_LABELS[p]}: ${c}`}
                   style={{ background: PHASE_COLORS[p], flexBasis: `${pct}%`, display: 'flex',
                            alignItems: 'center', justifyContent: 'center', color: 'white',
                            fontSize: 11, fontWeight: 500, cursor: 'pointer' }}
                   onClick={() => navigate('/nodes')}>
                {pct >= 5 ? `${c}` : ''}
              </div>
            );
          })}
        </div>
        <div style={{ display: 'flex', flexWrap: 'wrap', gap: 12, marginTop: 8, fontSize: 11, color: 'var(--text-secondary)' }}>
          {PHASE_ORDER.map(p => (
            <span key={p} style={{ display: 'inline-flex', alignItems: 'center', gap: 4 }}>
              <span style={{ width: 8, height: 8, borderRadius: '50%', background: PHASE_COLORS[p] }} />
              {PHASE_LABELS[p]} <strong style={{ color: 'var(--text-primary)' }}>{phaseCounts[p] || 0}</strong>
            </span>
          ))}
        </div>
      </div>

      <div className={styles.section}>
        <div className={styles.sectionLabel}>State index</div>
        <div className={styles.statsGrid}>
          <div className={styles.stat}>
            <span className={styles.statValue}>{health.counts?.nodes ?? '—'}</span>
            <span className={styles.statLabel}>nodes</span>
          </div>
          <div className={styles.stat}>
            <span className={styles.statValue}>{health.counts?.edges ?? '—'}</span>
            <span className={styles.statLabel}>edges</span>
          </div>
          <div className={styles.stat}>
            <span className={styles.statValue}>{health.counts?.lean_decls ?? '—'}</span>
            <span className={styles.statLabel}>lean decls</span>
          </div>
          <div className={styles.stat}>
            <span className={styles.statValue}>{health.counts?.agent_runs ?? '—'}</span>
            <span className={styles.statLabel}>agent runs</span>
          </div>
        </div>
        {indexedAt && (
          <div style={{ fontSize: 11, color: 'var(--text-muted)', marginTop: 8 }}>
            Indexed at {new Date(indexedAt).toLocaleString()}
          </div>
        )}
      </div>

      <div className={styles.section}>
        <div className={styles.sectionLabel}>
          Stale backlog · top {stale.length} nodes idle ≥ {STALE_DAYS} days
        </div>
        {stale.length === 0 ? (
          <div className={styles.empty}>No stale nodes. Nice.</div>
        ) : (
          <table className={styles.table}>
            <thead>
              <tr>
                <th>id</th>
                <th>kind</th>
                <th>chapter</th>
                <th>phase</th>
                <th>idle</th>
              </tr>
            </thead>
            <tbody>
              {stale.map(n => {
                const d = daysAgo(n.lastActivity);
                return (
                  <tr key={n.id}
                      style={{ cursor: 'pointer' }}
                      onClick={() => navigate(`/nodes/${encodeURIComponent(n.id)}`)}>
                    <td>{n.id}</td>
                    <td>{n.kind || '—'}</td>
                    <td>{n.chapter || '—'}</td>
                    <td>
                      <span style={{ display: 'inline-flex', alignItems: 'center', gap: 4 }}>
                        <span style={{ width: 8, height: 8, borderRadius: '50%', background: PHASE_COLORS[n.phase] }} />
                        {PHASE_LABELS[n.phase]}
                      </span>
                    </td>
                    <td>{d == null ? '∞' : `${Math.floor(d)}d`}</td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        )}
      </div>

      {summary && summary.sessionCount > 0 && (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>Agent activity totals</div>
          <div className={styles.statsGrid}>
            <div className={styles.stat}>
              <span className={styles.statValue}>{summary.sessionCount}</span>
              <span className={styles.statLabel}>sessions</span>
            </div>
            <div className={styles.stat}>
              <span className={styles.statValue}>{fmtDuration(summary.totalDuration)}</span>
              <span className={styles.statLabel}>duration</span>
            </div>
            <div className={styles.stat}>
              <span className={styles.statValue}>${summary.totalCost.toFixed(2)}</span>
              <span className={styles.statLabel}>cost</span>
            </div>
          </div>
        </div>
      )}
    </div>
  );
}
