export interface LogEntry {
  ts: string;
  event: 'shell' | 'thinking' | 'tool_call' | 'tool_result' | 'text' | 'session_end';
  level?: 'info' | 'warn' | 'error';
  message?: string;
  content?: string;
  tool?: string;
  input?: Record<string, unknown>;
  total_cost_usd?: number;
  duration_ms?: number;
  num_turns?: number;
  input_tokens?: number;
  output_tokens?: number;
  model_usage?: Record<string, { inputTokens: number; outputTokens: number; costUSD: number }>;
  summary?: string;
  session_id?: string;
}

export interface LogFile { name: string; path: string; size: number; modified: string; agent?: string; runId?: string }

export interface LogGroup {
  id: string;
  agent: string;
  files: LogFile[];
  meta?: {
    agent?: string;
    hint_file?: string;
    startedAt?: string;
    completedAt?: string;
    status?: string;
    model?: string;
  };
}

export interface LogsResponse {
  flat: LogFile[];
  groups: LogGroup[];
}

export interface AgentSummary {
  name: string;
  runCount: number;
  latestRun?: string;
}

export interface SessionSummary {
  cost: number;
  duration: number;
  tokensIn: number;
  tokensOut: number;
  model: string;
  turns: number;
  timestamp: string;
  summary?: string;
}

export interface AggregatedStats {
  totalCost: number;
  totalDuration: number;
  totalTokensIn: number;
  totalTokensOut: number;
  sessionCount: number;
  sessions: SessionSummary[];
}
