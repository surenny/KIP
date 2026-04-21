import { useAgents, useSummary } from '../hooks/useApi';
import { fmtDuration, fmtTokens, fmtTime } from '../utils/format';
import { STATUS_COLORS } from '../utils/constants';
import styles from './Overview.module.css';

export default function Overview() {
  const { data: agents } = useAgents();
  const { data: summary } = useSummary();

  return (
    <div className={styles.root}>
      <h2 className={styles.title}>KIP Agent Dashboard</h2>

      {agents && agents.length > 0 && (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>Agents</div>
          <div className={styles.agentList}>
            {agents.map(a => (
              <div key={a.name} className={styles.agentCard}>
                <span className={styles.agentName}>{a.name}</span>
                <span className={styles.agentRuns}>{a.runCount} run{a.runCount !== 1 ? 's' : ''}</span>
                {a.latestRun && <span className={styles.agentLatest}>latest: {fmtTime(a.latestRun)}</span>}
              </div>
            ))}
          </div>
        </div>
      )}

      {agents && agents.length === 0 && (
        <div className={styles.empty}>No agent logs found. Run an agent to see logs here.</div>
      )}

      {summary && summary.sessionCount > 0 && (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>Totals</div>
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
            <div className={styles.stat}>
              <span className={styles.statValue}>{fmtTokens(summary.totalTokensIn)}</span>
              <span className={styles.statLabel}>tokens in</span>
            </div>
            <div className={styles.stat}>
              <span className={styles.statValue}>{fmtTokens(summary.totalTokensOut)}</span>
              <span className={styles.statLabel}>tokens out</span>
            </div>
          </div>
        </div>
      )}

      {summary?.sessions && summary.sessions.length > 0 && (
        <div className={styles.section}>
          <div className={styles.sectionLabel}>Recent Sessions</div>
          <table className={styles.table}>
            <thead>
              <tr><th>Time</th><th>Model</th><th>Duration</th><th>Turns</th><th>Cost</th></tr>
            </thead>
            <tbody>
              {summary.sessions.slice().reverse().slice(0, 20).map((s, i) => (
                <tr key={i}>
                  <td>{fmtTime(s.timestamp)}</td>
                  <td>{s.model}</td>
                  <td>{fmtDuration(s.duration)}</td>
                  <td>{s.turns}</td>
                  <td>${s.cost.toFixed(3)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
    </div>
  );
}
