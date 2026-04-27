import { useQuery } from '@tanstack/react-query';
import { apiUrl } from '../utils/constants';
import type {
  LogEntry, AggregatedStats, LogsResponse, AgentSummary,
  GraphPayload, NodeDetail, StateHealth,
} from '../types';

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

export function useGraph() {
  return useQuery<GraphPayload>({
    queryKey: ['graph'],
    queryFn: () => fetchJson('/api/graph'),
    refetchInterval: 15000,
  });
}

export function useNode(id: string) {
  return useQuery<NodeDetail>({
    queryKey: ['node', id],
    queryFn: () => fetchJson(`/api/nodes/${encodeURIComponent(id)}`),
    enabled: !!id,
  });
}

export function useStateHealth() {
  return useQuery<StateHealth>({
    queryKey: ['stateHealth'],
    queryFn: () => fetchJson('/api/state/health'),
    refetchInterval: 15000,
  });
}

export function useGraphSvg(params: {
  phases: string[];
  chapters: string[];
  q: string;
  enabled?: boolean;
}) {
  const qs = new URLSearchParams();
  if (params.phases.length) qs.set('phases', params.phases.join(','));
  if (params.chapters.length) qs.set('chapters', params.chapters.join(','));
  if (params.q) qs.set('q', params.q);
  const url = '/api/graph/svg?' + qs.toString();
  return useQuery<string>({
    queryKey: ['graph-svg', params.phases.join(','), params.chapters.join(','), params.q],
    queryFn: async () => {
      const res = await fetch(apiUrl(url));
      if (!res.ok) throw new Error(`API ${res.status}`);
      return res.text();
    },
    enabled: params.enabled !== false,
    staleTime: 5000,
    placeholderData: (prev) => prev,  // keep old SVG visible while re-fetching
  });
}
