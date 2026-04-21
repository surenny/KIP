import { useQuery } from '@tanstack/react-query';
import { apiUrl } from '../utils/constants';
import type { LogEntry, AggregatedStats, LogsResponse, AgentSummary } from '../types';

async function fetchJson<T>(url: string): Promise<T> {
  const res = await fetch(apiUrl(url));
  if (!res.ok) throw new Error(`API ${res.status}`);
  return res.json();
}

export function useProject() {
  return useQuery<{ name: string; path: string; agentsPath: string }>({
    queryKey: ['project'], queryFn: () => fetchJson('/api/project'), staleTime: Infinity,
  });
}

export function useAgents() {
  return useQuery<AgentSummary[]>({
    queryKey: ['agents'], queryFn: () => fetchJson('/api/agents'), refetchInterval: 10000,
  });
}

export function useSummary() {
  return useQuery<AggregatedStats>({
    queryKey: ['summary'], queryFn: () => fetchJson('/api/summary'), refetchInterval: 10000,
  });
}

export function useLogs() {
  return useQuery<LogsResponse>({
    queryKey: ['logs'], queryFn: () => fetchJson('/api/logs'), refetchInterval: 3000, refetchIntervalInBackground: true,
  });
}

export function useLogContent(filename: string) {
  return useQuery<LogEntry[]>({
    queryKey: ['logContent', filename],
    queryFn: () => fetchJson(`/api/logs/${filename}`),
    enabled: !!filename,
    refetchInterval: false,
  });
}
