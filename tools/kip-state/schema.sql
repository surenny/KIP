-- KIP project state index. Built from status.yaml + blueprint LaTeX + Lean source + agent logs.
-- This is a derived cache; truth lives in the files. Safe to drop and rebuild anytime.

CREATE TABLE meta (
  key   TEXT PRIMARY KEY,
  value TEXT
);

CREATE TABLE nodes (
  id              TEXT PRIMARY KEY,
  kind            TEXT,                  -- definition / theorem / lemma / proposition / corollary / axiom / notation / remark / question / example
  chapter         TEXT,                  -- chapter file stem
  source_file     TEXT,
  source_line     INTEGER,
  lean_decl       TEXT,                  -- from \lean{...}
  leanok          INTEGER NOT NULL DEFAULT 0,  -- \leanok marker present
  nl_hash         TEXT,
  nl_reviewed     INTEGER NOT NULL DEFAULT 0,
  bound           INTEGER NOT NULL DEFAULT 0,
  aligned         INTEGER NOT NULL DEFAULT 0,
  proved          INTEGER NOT NULL DEFAULT 0,
  nl_reviewer     TEXT,
  align_reviewer  TEXT,
  aligned_at      TEXT,
  last_activity   TEXT,                  -- ISO-8601, computed from comments/runs/aligned_at
  phase           TEXT NOT NULL DEFAULT 'drafted'  -- derived: drafted|nl_reviewed|bound|aligned|proved
);

CREATE TABLE edges (
  from_node TEXT NOT NULL,               -- the node that contains \uses{...}
  to_node   TEXT NOT NULL,               -- the dependency
  source    TEXT NOT NULL DEFAULT 'latex',
  confirmed INTEGER NOT NULL DEFAULT 0,
  PRIMARY KEY (from_node, to_node)
);
CREATE INDEX idx_edges_to ON edges(to_node);

CREATE TABLE node_comments (
  node_id TEXT NOT NULL,
  idx     INTEGER NOT NULL,
  topic   TEXT,
  text    TEXT,
  by      TEXT,
  at      TEXT,
  PRIMARY KEY (node_id, idx)
);

CREATE TABLE lean_decls (
  name        TEXT PRIMARY KEY,          -- fully qualified
  file        TEXT,
  line_start  INTEGER,
  line_end    INTEGER,
  sorry_count INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE agent_runs (
  id            TEXT PRIMARY KEY,        -- run-<ts> directory name
  agent         TEXT,
  started_at    TEXT,
  completed_at  TEXT,
  status        TEXT,
  model         TEXT,
  hint_file     TEXT,
  cost_usd      REAL,
  duration_ms   INTEGER,
  num_turns     INTEGER,
  input_tokens  INTEGER,
  output_tokens INTEGER,
  summary       TEXT,
  log_path      TEXT                     -- path to the .jsonl log
);
CREATE INDEX idx_runs_started ON agent_runs(started_at);

CREATE TABLE agent_run_nodes (
  run_id  TEXT NOT NULL,
  node_id TEXT NOT NULL,
  PRIMARY KEY (run_id, node_id)
);
CREATE INDEX idx_run_nodes_node ON agent_run_nodes(node_id);
