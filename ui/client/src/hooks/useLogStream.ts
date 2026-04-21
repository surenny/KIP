import { useState, useEffect, useRef, useCallback } from 'react';
import { apiUrl, wsUrl as buildWsUrl } from '../utils/constants';
import type { LogEntry } from '../types';

const POLL_INTERVAL = 3000;

interface UseLogStreamResult {
  entries: LogEntry[];
  streaming: boolean;
}

export function useLogStream(selectedFile: string): UseLogStreamResult {
  const [entries, setEntries] = useState<LogEntry[]>([]);
  const [streaming, setStreaming] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);
  const pollRef = useRef<ReturnType<typeof setInterval> | null>(null);
  const entriesRef = useRef<LogEntry[]>([]);

  const updateEntries = useCallback((newEntries: LogEntry[]) => {
    entriesRef.current = newEntries;
    setEntries(newEntries);
  }, []);

  const appendEntries = useCallback((incoming: LogEntry[]) => {
    const updated = [...entriesRef.current, ...incoming];
    entriesRef.current = updated;
    setEntries([...updated]);
  }, []);

  useEffect(() => {
    if (!selectedFile) {
      updateEntries([]);
      setStreaming(false);
      return;
    }

    updateEntries([]);
    setStreaming(false);

    let cancelled = false;

    function fetchLog() {
      return fetch(apiUrl(`/api/logs/${selectedFile}`))
        .then(r => r.json())
        .then((logs: LogEntry[]) => {
          if (cancelled) return;
          updateEntries(logs);
          return logs.length;
        })
        .catch(() => -1);
    }

    let wsConnected = false;
    let wsReady = false;

    function startPolling() {
      if (pollRef.current) return;
      pollRef.current = setInterval(async () => {
        if (cancelled) return;
        await fetchLog();
      }, POLL_INTERVAL);
    }

    const wsUrlStr = buildWsUrl(`/api/log-stream/${selectedFile}`);
    const ws = new WebSocket(wsUrlStr);
    wsRef.current = ws;

    ws.onopen = () => {
      if (cancelled) return;
      wsConnected = true;
    };

    ws.onmessage = (ev) => {
      if (cancelled) return;
      try {
        const raw = JSON.parse(ev.data);
        if (raw.type === 'ready') {
          wsReady = true;
          setStreaming(true);
          fetchLog();
          return;
        }
        if (raw.type === 'error') return;
        if (raw.ts) appendEntries([raw as LogEntry]);
      } catch { /* skip */ }
    };

    ws.onclose = () => {
      if (cancelled) return;
      setStreaming(false);
      if (!wsConnected || !wsReady) startPolling();
    };

    ws.onerror = () => {
      if (cancelled) return;
      setStreaming(false);
      startPolling();
    };

    fetchLog();

    return () => {
      cancelled = true;
      ws.close();
      wsRef.current = null;
      if (pollRef.current) {
        clearInterval(pollRef.current);
        pollRef.current = null;
      }
    };
  }, [selectedFile, updateEntries, appendEntries]);

  return { entries, streaming };
}
