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

// ===== KIP node-state types =====================================================

export type Phase = 'drafted' | 'nl_reviewed' | 'bound' | 'aligned' | 'proved';

export interface NodeFlags {
  nlReviewed: boolean;
  bound: boolean;
  aligned: boolean;
  proved: boolean;
}

export interface NodeData {
  id: string;
  kind: string | null;
  chapter: string | null;
  subsection: string | null;
  sourceFile: string | null;
  sourceLine: number | null;
  leanDecl: string | null;
  leanok: boolean;
  nlHash: string | null;
  flags: NodeFlags;
  nlReviewer: string | null;
  alignReviewer: string | null;
  alignedAt: string | null;
  lastActivity: string | null;
  phase: Phase;
}

export interface EdgeData {
  from: string;
  to: string;
  source: string;
}

export interface GraphPayload {
  nodes: NodeData[];
  edges: EdgeData[];
  /** Chapters in the order they're \input'd from content.tex (with ≥1 node). */
  chapters: string[];
}

export interface NodeComment {
  idx: number;
  topic: string | null;
  text: string | null;
  by: string | null;
  at: string | null;
}

export interface LeanDeclInfo {
  name: string;
  file: string;
  line_start: number;
  line_end: number;
  sorry_count: number;
}

export interface NodeRunInfo {
  id: string;
  agent: string;
  started_at: string | null;
  completed_at: string | null;
  status: string | null;
  model: string | null;
  hint_file: string | null;
  cost_usd: number | null;
  duration_ms: number | null;
  num_turns: number | null;
  summary: string | null;
  log_path: string | null;
}

export interface RenderedNode {
  caption: string;
  label: string;
  contentHtml: string;
}

export interface NodeDetail extends Omit<NodeData, 'leanDecl'> {
  comments: NodeComment[];
  uses: { id: string }[];
  usedBy: { id: string }[];
  leanDecl: LeanDeclInfo | null;
  leanSource: string | null;
  runs: NodeRunInfo[];
  nlExcerpt: string | null;
  nlRendered: RenderedNode | null;
}

export interface StateHealth {
  ok: boolean;
  error?: string;
  meta?: { indexed_at?: string; schema_version?: string };
  counts?: { nodes: number; edges: number; lean_decls: number; agent_runs: number };
  phases?: Partial<Record<Phase, number>>;
}
