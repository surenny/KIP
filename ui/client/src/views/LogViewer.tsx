import { useState, useEffect, useMemo, useRef } from 'react';
import { useLogs } from '../hooks/useApi';
import { useLogDeepLink } from '../hooks/useLogDeepLink';
import { useLogStream } from '../hooks/useLogStream';
import type { LogEntry, LogGroup } from '../types';
import { fmtDuration, fmtTime } from '../utils/format';
import LogEntryLine from '../components/LogEntryLine';
import MarkdownBlock from '../components/MarkdownBlock';
import styles from './LogViewer.module.css';

function RunGroup({ group, selectedFile, onSelect }: {
  group: LogGroup;
  selectedFile: string;
  onSelect: (path: string) => void;
}) {
  const hasSelected = group.files.some(f => f.path === selectedFile);
  const [expanded, setExpanded] = useState(hasSelected);
  const meta = group.meta;

  useEffect(() => { if (hasSelected) setExpanded(true); }, [hasSelected]);

  const status = meta?.status || 'unknown';
  const statusColor = status === 'done' ? 'var(--green)' : status === 'running' ? 'var(--blue)' : status === 'error' ? 'var(--red)' : 'var(--text-muted)';
  const hintName = meta?.hint_file ? String(meta.hint_file).split('/').pop() : '';

  return (
    <div className={styles.group}>
      <div className={styles.groupHeader} onClick={() => setExpanded(!expanded)}>
        <span className={styles.toggle}>{expanded ? '▾' : '▸'}</span>
        <span className={styles.statusDot} style={{ background: statusColor }} />
        <span className={styles.groupTitle}>{hintName || group.id.split('/').pop()}</span>
        {meta?.model && <span className={styles.groupMeta}>{meta.model}</span>}
      </div>

      {expanded && (
        <div className={styles.groupBody}>
          {group.files.map(f => (
            <div
              key={f.path}
              className={`${styles.fileItem} ${f.path === selectedFile ? styles.fileItemActive : ''}`}
              onClick={() => onSelect(f.path)}
            >
              <span className={styles.fileName}>{f.name.replace('.jsonl', '')}</span>
            </div>
          ))}
        </div>
      )}
    </div>
  );
}

const FILTER_OPTIONS = [
  { value: 'shell', label: 'shell' },
  { value: 'thinking', label: 'thinking' },
  { value: 'tool_call', label: 'tool call' },
  { value: 'tool_result', label: 'tool result' },
  { value: 'text', label: 'text' },
  { value: 'session_end', label: 'session end' },
] as const;

type FilterEvent = typeof FILTER_OPTIONS[number]['value'];
const DEFAULT_FILTERS: FilterEvent[] = FILTER_OPTIONS.map(o => o.value);

function RunSummaryBar({ entries }: { entries: LogEntry[] }) {
  const sessionEnd = entries.find(e => e.event === 'session_end');
  if (!sessionEnd) return null;
  const model = sessionEnd.model_usage ? Object.keys(sessionEnd.model_usage)[0]?.replace(/^claude-/, '').replace(/-\d{8}$/, '') : '';
  const parts: string[] = [];
  if (model) parts.push(model);
  if (sessionEnd.duration_ms) parts.push(fmtDuration(sessionEnd.duration_ms));
  if (sessionEnd.num_turns) parts.push(`${sessionEnd.num_turns} turns`);
  if (sessionEnd.total_cost_usd) parts.push(`$${sessionEnd.total_cost_usd.toFixed(2)}`);
  if (sessionEnd.input_tokens) parts.push(`${(sessionEnd.input_tokens / 1000).toFixed(0)}K in`);
  if (sessionEnd.output_tokens) parts.push(`${(sessionEnd.output_tokens / 1000).toFixed(0)}K out`);
  if (!parts.length) return null;
  return <div className={styles.sessionSummary}>{parts.join(' · ')}</div>;
}

export default function LogViewer() {
  const [selectedFile, setSelectedFile] = useState('');
  const [selectedFilters, setSelectedFilters] = useState<FilterEvent[]>(DEFAULT_FILTERS);
  const highlightRef = useRef<HTMLDivElement>(null);

  const { data: logsData } = useLogs();
  const { initialSelectedFile, initialHighlightTs } = useLogDeepLink(logsData);
  const { entries, streaming } = useLogStream(selectedFile);
  const highlightConsumedRef = useRef(false);

  const toggleFilter = (event: FilterEvent) => {
    setSelectedFilters(current => (
      current.includes(event)
        ? current.filter(v => v !== event)
        : [...current, event]
    ));
  };

  const resetFilters = () => setSelectedFilters(DEFAULT_FILTERS);
  const allFiltersSelected = selectedFilters.length === DEFAULT_FILTERS.length;
  const selectedFilterSet = useMemo(() => new Set<FilterEvent>(selectedFilters), [selectedFilters]);

  useEffect(() => {
    if (!selectedFile && initialSelectedFile) setSelectedFile(initialSelectedFile);
  }, [selectedFile, initialSelectedFile]);

  useEffect(() => {
    if (highlightConsumedRef.current) return;
    if (!selectedFile || !initialSelectedFile || selectedFile !== initialSelectedFile) return;
    if (highlightRef.current) {
      highlightRef.current.scrollIntoView({ behavior: 'smooth', block: 'center' });
      highlightConsumedRef.current = true;
    }
  }, [selectedFile, initialSelectedFile, entries]);

  const closestHighlightTs = useMemo(() => {
    if (selectedFile !== initialSelectedFile) return '';
    if (!initialHighlightTs || entries.length === 0) return '';
    const targetTime = new Date(initialHighlightTs).getTime();
    if (isNaN(targetTime)) return '';
    let minDist = Infinity;
    let bestTs = '';
    for (const e of entries) {
      if (!e.ts || e.event === 'session_end') continue;
      const dist = Math.abs(new Date(e.ts).getTime() - targetTime);
      if (dist < minDist) { minDist = dist; bestTs = e.ts; }
    }
    return bestTs;
  }, [entries, initialHighlightTs, selectedFile, initialSelectedFile]);

  // Group runs by agent for sidebar
  const agentGroups = useMemo(() => {
    if (!logsData?.groups) return new Map<string, LogGroup[]>();
    const map = new Map<string, LogGroup[]>();
    for (const g of logsData.groups) {
      const existing = map.get(g.agent) || [];
      existing.push(g);
      map.set(g.agent, existing);
    }
    return map;
  }, [logsData]);

  // Auto-select first file
  useEffect(() => {
    if (!logsData || selectedFile || initialSelectedFile) return;
    if (logsData.groups.length > 0 && logsData.groups[0].files.length > 0) {
      setSelectedFile(logsData.groups[0].files[0].path);
    }
  }, [logsData, selectedFile, initialSelectedFile]);

  const filtered = useMemo(() => entries.filter(e => selectedFilterSet.has(e.event as FilterEvent)), [entries, selectedFilterSet]);
  const visibleEntries = useMemo(() => filtered.filter(e => e.event !== 'session_end'), [filtered]);
  const sessionEnd = useMemo(() => entries.find(e => e.event === 'session_end'), [entries]);
  const showSessionSummary = !!sessionEnd && selectedFilterSet.has('session_end');
  const selectedLabel = selectedFile.replace(/\.jsonl$/, '').replace(/\//g, ' / ');

  return (
    <div className={styles.root}>
      <div className={styles.sidebar}>
        {Array.from(agentGroups.entries()).map(([agentName, groups]) => (
          <div key={agentName} className={styles.agentSection}>
            <div className={styles.agentHeader}>{agentName}</div>
            {groups.map(g => (
              <RunGroup key={g.id} group={g} selectedFile={selectedFile} onSelect={setSelectedFile} />
            ))}
          </div>
        ))}

        {!logsData?.groups.length && (
          <div className={styles.emptyHint}>No logs yet</div>
        )}
      </div>

      <div className={styles.main}>
        <div className={styles.toolbar}>
          <span className={styles.selectedLabel}>{selectedLabel || 'Select a log'}</span>
          <div className={styles.filterBar} aria-label="Event type filters">
            <span className={styles.filterLabel}>Show</span>
            <div className={styles.filterChips}>
              {FILTER_OPTIONS.map(option => {
                const active = selectedFilterSet.has(option.value);
                return (
                  <button
                    key={option.value}
                    type="button"
                    className={`${styles.filterChip} ${active ? styles.filterChipActive : ''}`}
                    onClick={() => toggleFilter(option.value)}
                    aria-pressed={active}
                  >
                    {option.label}
                  </button>
                );
              })}
            </div>
            {!allFiltersSelected && (
              <button type="button" className={styles.resetFiltersBtn} onClick={resetFilters}>Reset</button>
            )}
          </div>
          {streaming && <span className={styles.live}>{'●'} live</span>}
          <span className={styles.count}>{filtered.length} entries</span>
        </div>

        {showSessionSummary && <RunSummaryBar entries={entries} />}

        <div className={styles.container}>
          {showSessionSummary && sessionEnd?.summary && (
            <div className={styles.summaryBlock}>
              <span className={styles.summaryLabel}>Summary</span>
              <MarkdownBlock content={sessionEnd.summary} className={styles.summaryText} />
            </div>
          )}

          {(() => {
            let highlightAttached = false;
            return visibleEntries.slice().reverse().map((e, i) => {
              const isHighlighted = !!(closestHighlightTs && e.ts === closestHighlightTs);
              const attachRef = isHighlighted && !highlightAttached;
              if (attachRef) highlightAttached = true;
              return (
                <div key={e.ts ? `${e.ts}-${e.event}-${i}` : `entry-${i}`}
                     ref={attachRef ? highlightRef : undefined}
                     style={isHighlighted ? { background: 'rgba(3,102,214,0.08)', borderLeft: '3px solid var(--blue)' } : undefined}>
                  <LogEntryLine entry={e} />
                </div>
              );
            });
          })()}

          {selectedFile && filtered.length === 0 && (
            <div className={styles.emptyContent}>No entries match the current filters.</div>
          )}
          {entries.length === 0 && selectedFile && (
            <div className={styles.emptyContent}>No entries in this log file yet.</div>
          )}
        </div>
      </div>
    </div>
  );
}
