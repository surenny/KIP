import styles from './details.module.css';

interface Props { input: Record<string, unknown>; tool: string; }

function buildMiniDiff(oldStr: string, newStr: string): string {
  const oldLines = oldStr ? oldStr.split('\n') : [];
  const newLines = newStr ? newStr.split('\n') : [];
  let result = `--- a/old\n+++ b/new\n@@ -1,${oldLines.length} +1,${newLines.length} @@\n`;
  for (const line of oldLines) result += `-${line}\n`;
  for (const line of newLines) result += `+${line}\n`;
  return result;
}

export default function EditDetail({ input, tool }: Props) {
  const filePath = String(input.file_path || '');
  const oldString = String(input.old_string || '');
  const newString = String(input.new_string ?? (tool === 'Write' ? input.content ?? '' : ''));
  const isWrite = tool === 'Write';
  const fileName = filePath.split('/').slice(-2).join('/');

  if (isWrite) {
    const preview = newString.length > 2000 ? newString.slice(0, 2000) + '\n...(truncated)' : newString;
    return (
      <div className={styles.container}>
        <div className={styles.header}>
          <span className={styles.label}>Write</span>
          <span className={styles.path}>{fileName}</span>
        </div>
        <pre className={styles.codeBlock}>{preview}</pre>
      </div>
    );
  }

  if (!oldString && !newString) return null;

  return (
    <div className={styles.container}>
      <div className={styles.header}>
        <span className={styles.label}>Edit</span>
        <span className={styles.path}>{fileName}</span>
      </div>
      <pre className={styles.codeBlock}>
        {oldString.split('\n').map((l, i) => <div key={`r${i}`} className={styles.changeRemove}>- {l}</div>)}
        {newString.split('\n').map((l, i) => <div key={`a${i}`} className={styles.changeAdd}>+ {l}</div>)}
      </pre>
    </div>
  );
}
