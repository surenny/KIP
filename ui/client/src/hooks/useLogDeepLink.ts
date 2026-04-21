import { useMemo, useRef } from 'react';
import { useLocation, useSearchParams } from 'react-router-dom';
import type { LogsResponse } from '../types';

interface FromLocationState {
  from?: { pathname: string; search?: string };
}

export function useLogDeepLink(logsData?: LogsResponse) {
  const [searchParams] = useSearchParams();
  const location = useLocation();
  const consumedRef = useRef(false);

  const target = useMemo(() => ({
    agent: searchParams.get('agent') || '',
    run: searchParams.get('run') || '',
    file: searchParams.get('file') || '',
    ts: searchParams.get('ts') || '',
  }), []);

  const backTarget = (location.state as FromLocationState | null)?.from || null;

  const resolveInitialSelectedFile = useMemo(() => {
    if (!logsData || consumedRef.current) return '';
    if (!target.agent || !target.run) return '';
    for (const g of logsData.groups) {
      if (!g.id.includes(target.run)) continue;
      const match = g.files.find(f => f.name === `${target.file}.jsonl` || f.name === target.file);
      if (match) {
        consumedRef.current = true;
        return match.path;
      }
    }
    return '';
  }, [logsData, target]);

  return {
    initialSelectedFile: resolveInitialSelectedFile,
    initialHighlightTs: target.ts,
    backTarget,
  };
}
