import JsonDetail from './JsonDetail';
import styles from './details.module.css';

interface Props { content: string; structuredJson?: boolean; }

function classifyLine(line: string): 'error' | 'warning' | 'success' | 'normal' {
  const lower = line.toLowerCase();
  if (lower.includes('error:') || lower.includes('tool_use_error') || lower.includes('type mismatch') || lower.includes('unknown identifier'))
    return 'error';
  if (lower.includes('warning:') || lower.includes("uses 'sorry'"))
    return 'warning';
  if (lower.includes('successfully') || lower.includes('no errors'))
    return 'success';
  return 'normal';
}

function parseStructuredResult(content: string): unknown | null {
  const trimmed = content.trim();
  if (!trimmed) return null;
  if (!((trimmed.startsWith('{') && trimmed.endsWith('}')) || (trimmed.startsWith('[') && trimmed.endsWith(']')))) return null;
  try { return JSON.parse(trimmed); } catch { return null; }
}

export default function ToolResultDetail({ content, structuredJson = true }: Props) {
  const structured = structuredJson ? parseStructuredResult(content) : null;

  if (structured !== null) {
    return (
      <div className={styles.container}>
        <div className={styles.header}>
          <span className={styles.label}>Structured result</span>
        </div>
        <JsonDetail data={structured} bare />
      </div>
    );
  }

  const lines = content.split('\n');
  const hasError = lines.some(l => classifyLine(l) === 'error');

  return (
    <div className={styles.container}>
      <div className={styles.header}>
        <span className={styles.label}>Result</span>
        <span className={styles.meta}>{lines.length} lines</span>
      </div>
      <div className={styles.resultBlock}>
        {lines.map((line, i) => {
          const cls = classifyLine(line);
          return (
            <div key={i} className={
              cls === 'error' ? styles.resultError :
              cls === 'warning' ? styles.resultWarning :
              cls === 'success' ? styles.resultSuccess :
              styles.resultNormal
            }>
              {line || ' '}
            </div>
          );
        })}
      </div>
    </div>
  );
}
