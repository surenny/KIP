#!/usr/bin/env python3
r"""Build .kip/state.db from project sources.

Inputs:
  blueprint/status.yaml          - node lifecycle flags, comments
  blueprint/src/chapters/*.tex   - node IDs, kinds, edges (\uses), Lean bindings (\lean), \leanok
  KIP/**/*.lean                  - declarations + sorry counts (per fully-qualified name)
  agents/*/logs/run-*/           - agent runs (meta.json + .jsonl with session_end)

Output: .kip/state.db (SQLite, gitignored, safe to drop)

Usage:
  python tools/kip-state/index.py [--project PATH] [--db PATH]
"""
from __future__ import annotations

import argparse
import json
import re
import sqlite3
import sys
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path

import yaml

KIND_PATTERN = r"theorem|definition|lemma|proposition|corollary|axiom|notation|remark|question|example"
RE_BEGIN = re.compile(r"\\begin\{(" + KIND_PATTERN + r")\*?\}")
RE_END = re.compile(r"\\end\{(" + KIND_PATTERN + r")\*?\}")
RE_LABEL = re.compile(r"\\label\{([^}]+)\}")
RE_USES = re.compile(r"\\uses\{([^}]+)\}")
RE_LEAN = re.compile(r"\\lean\{([^}]+)\}")
RE_LEANOK = re.compile(r"\\leanok\b")

RE_LEAN_DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*"
                          r"(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*"
                          r"(theorem|lemma|def|abbrev|axiom|structure|class|instance)\s+"
                          r"([A-Za-z_][A-Za-z0-9_'\.]*)")
RE_LEAN_NS = re.compile(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'\.]*)")
RE_LEAN_NS_END = re.compile(r"^\s*end\s+([A-Za-z_][A-Za-z0-9_'\.]*)?\s*$")
RE_SORRY = re.compile(r"\bsorry\b")


@dataclass
class ParsedNode:
    id: str
    kind: str
    chapter: str
    source_file: str
    source_line: int
    lean_decl: str | None = None
    leanok: bool = False
    edges_to: list[str] = field(default_factory=list)


def parse_chapters(chapters_dir: Path) -> tuple[dict[str, ParsedNode], list[tuple[str, str]]]:
    """Walk all chapter .tex files, return (nodes_by_id, edges)."""
    nodes: dict[str, ParsedNode] = {}
    edges: list[tuple[str, str]] = []

    for tex in sorted(chapters_dir.glob("*.tex")):
        chapter = tex.stem
        try:
            lines = tex.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            lines = tex.read_text(encoding="latin-1").splitlines()

        block_kind: str | None = None
        block_start: int = 0
        block_text: list[str] = []

        def finalize(end_line: int) -> None:
            nonlocal block_kind, block_text, block_start
            if block_kind is None:
                return
            text = "\n".join(block_text)
            label_m = RE_LABEL.search(text)
            if not label_m:
                block_kind = None
                block_text = []
                return
            nid = label_m.group(1)
            node = ParsedNode(
                id=nid,
                kind=block_kind,
                chapter=chapter,
                source_file=str(tex),
                source_line=block_start,
            )
            for m in RE_USES.finditer(text):
                for tgt in m.group(1).split(","):
                    tgt = tgt.strip()
                    if tgt:
                        edges.append((nid, tgt))
                        node.edges_to.append(tgt)
            lean_m = RE_LEAN.search(text)
            if lean_m:
                node.lean_decl = lean_m.group(1).strip()
            if RE_LEANOK.search(text):
                node.leanok = True
            nodes[nid] = node  # last definition wins on duplicate
            block_kind = None
            block_text = []

        for idx, line in enumerate(lines, start=1):
            mb = RE_BEGIN.search(line)
            me = RE_END.search(line)
            if mb and block_kind is None:
                block_kind = mb.group(1)
                block_start = idx
                block_text = [line]
                continue
            if block_kind is not None:
                block_text.append(line)
                if me and me.group(1) == block_kind:
                    finalize(idx)

    return nodes, edges


def parse_lean_sources(lean_root: Path) -> dict[str, dict]:
    """Return fully-qualified name → {file, line_start, line_end, sorry_count}."""
    out: dict[str, dict] = {}
    for path in sorted(lean_root.rglob("*.lean")):
        rel = str(path.relative_to(lean_root.parent))
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        ns_stack: list[str] = []
        decls: list[tuple[str, int]] = []  # (qualified_name, line)
        for i, raw in enumerate(lines, start=1):
            line = raw.split("--", 1)[0]  # crude single-line comment strip
            mns = RE_LEAN_NS.match(line)
            if mns:
                ns_stack.append(mns.group(1))
                continue
            mne = RE_LEAN_NS_END.match(line)
            if mne and ns_stack:
                # Only pop if `end <name>` matches the top namespace.
                # `end SectionName` closes a section, not a namespace, and
                # bare `end` (no name) is ambiguous — ignore both.
                end_name = mne.group(1)
                if end_name and end_name == ns_stack[-1]:
                    ns_stack.pop()
                continue
            md = RE_LEAN_DECL.match(line)
            if md:
                name = md.group(2)
                qualified = ".".join(ns_stack + [name]) if ns_stack else name
                decls.append((qualified, i))

        decls.append(("__END__", len(lines) + 1))
        for (name, start), (_, next_start) in zip(decls, decls[1:]):
            body = "\n".join(lines[start - 1 : next_start - 1])
            sorry_count = len(RE_SORRY.findall(body))
            out[name] = {
                "file": rel,
                "line_start": start,
                "line_end": next_start - 1,
                "sorry_count": sorry_count,
            }
    return out


@dataclass
class AgentRun:
    id: str
    agent: str
    started_at: str | None
    completed_at: str | None
    status: str | None
    model: str | None
    hint_file: str | None
    cost_usd: float | None = None
    duration_ms: int | None = None
    num_turns: int | None = None
    input_tokens: int | None = None
    output_tokens: int | None = None
    summary: str | None = None
    log_path: str | None = None
    touched_text: str = ""  # bag for node-id matching


def parse_agent_runs(agents_dir: Path) -> list[AgentRun]:
    runs: list[AgentRun] = []
    if not agents_dir.exists():
        return runs
    for agent_dir in sorted(agents_dir.iterdir()):
        if not agent_dir.is_dir():
            continue
        logs_dir = agent_dir / "logs"
        if not logs_dir.is_dir():
            continue
        for run_dir in sorted(logs_dir.iterdir()):
            if not run_dir.is_dir() or not run_dir.name.startswith("run-"):
                continue
            meta_path = run_dir / "meta.json"
            if not meta_path.exists():
                continue
            try:
                meta = json.loads(meta_path.read_text())
            except json.JSONDecodeError:
                continue
            jsonl_files = sorted(run_dir.glob("*.jsonl"))
            log_path = str(jsonl_files[0]) if jsonl_files else None
            session_end = None
            text_buf: list[str] = []
            for jf in jsonl_files:
                with jf.open() as f:
                    for raw in f:
                        try:
                            ev = json.loads(raw)
                        except json.JSONDecodeError:
                            continue
                        if ev.get("event") == "session_end":
                            session_end = ev
                        for k in ("content", "summary"):
                            v = ev.get(k)
                            if isinstance(v, str):
                                text_buf.append(v)
                            elif isinstance(v, (dict, list)):
                                text_buf.append(json.dumps(v))
            run = AgentRun(
                id=run_dir.name,
                agent=meta.get("agent") or agent_dir.name,
                started_at=meta.get("startedAt"),
                completed_at=meta.get("completedAt"),
                status=meta.get("status"),
                model=meta.get("model"),
                hint_file=meta.get("hint_file"),
                log_path=log_path,
            )
            if session_end:
                run.cost_usd = session_end.get("total_cost_usd")
                run.duration_ms = session_end.get("duration_ms")
                run.num_turns = session_end.get("num_turns")
                run.input_tokens = session_end.get("input_tokens")
                run.output_tokens = session_end.get("output_tokens")
                run.summary = session_end.get("summary")
                if not run.model:
                    mu = session_end.get("model_usage") or {}
                    if mu:
                        run.model = next(iter(mu))
            run.touched_text = "\n".join(text_buf)
            runs.append(run)
    return runs


def derive_phase(row: dict) -> str:
    """Map flag combination to a single phase enum.

    Uses the natural order; later flags imply earlier ones for display purposes,
    but we keep the *deepest* flag set as the phase label.
    nl_reviewed implicitly includes "dependency edges confirmed"."""
    if row.get("proved"):
        return "proved"
    if row.get("aligned"):
        return "aligned"
    if row.get("bound"):
        return "bound"
    if row.get("nl_reviewed"):
        return "nl_reviewed"
    return "drafted"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--project", type=Path, default=Path.cwd(),
                    help="KIP project root (default: cwd)")
    ap.add_argument("--db", type=Path, default=None,
                    help="Output SQLite path (default: <project>/.kip/state.db)")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args(argv)

    project: Path = args.project.resolve()
    db_path: Path = args.db or (project / ".kip" / "state.db")
    db_path.parent.mkdir(parents=True, exist_ok=True)

    log = (lambda *a, **k: None) if args.quiet else (lambda *a, **k: print(*a, **k, file=sys.stderr))

    schema_path = Path(__file__).parent / "schema.sql"
    schema_sql = schema_path.read_text()

    status_path = project / "blueprint" / "status.yaml"
    chapters_dir = project / "blueprint" / "src" / "chapters"
    lean_root = project / "KIP"
    agents_dir = project / "agents"

    log(f"[kip-state] project={project}")
    log(f"[kip-state] db={db_path}")

    if db_path.exists():
        db_path.unlink()
    conn = sqlite3.connect(db_path)
    conn.executescript(schema_sql)

    # ---- chapters: node skeletons + edges --------------------------------
    chapter_nodes, edges = parse_chapters(chapters_dir)
    log(f"[kip-state] chapters: {len(chapter_nodes)} nodes, {len(edges)} edges")

    # ---- status.yaml: lifecycle flags + comments -------------------------
    status_data = yaml.safe_load(status_path.read_text()) if status_path.exists() else {}
    status_nodes = status_data.get("nodes", {}) if isinstance(status_data, dict) else {}
    log(f"[kip-state] status.yaml: {len(status_nodes)} entries")

    # union of node IDs from both sources
    all_ids = set(chapter_nodes.keys()) | set(status_nodes.keys())

    # ---- lean source: declarations + sorries -----------------------------
    lean_decls = parse_lean_sources(lean_root) if lean_root.exists() else {}
    log(f"[kip-state] lean: {len(lean_decls)} declarations")

    # ---- agent runs ------------------------------------------------------
    runs = parse_agent_runs(agents_dir)
    log(f"[kip-state] agent runs: {len(runs)}")

    # =====================================================================
    # write nodes
    # =====================================================================
    cur = conn.cursor()
    for nid in sorted(all_ids):
        cn = chapter_nodes.get(nid)
        sn = status_nodes.get(nid) or {}
        kind = (cn.kind if cn else None) or sn.get("kind")
        chapter = cn.chapter if cn else None
        source_file = cn.source_file if cn else None
        source_line = cn.source_line if cn else None
        lean_decl = (cn.lean_decl if cn else None) or sn.get("lean_decl")
        leanok = 1 if (cn and cn.leanok) else 0

        nl_reviewed = 1 if sn.get("nl_reviewed") else 0
        bound = 1 if sn.get("bound") else 0
        aligned = 1 if sn.get("aligned") else 0
        proved = 1 if sn.get("proved") else 0

        comment_times = [c.get("at") for c in (sn.get("comments") or []) if c.get("at")]
        last_activity_candidates = [t for t in [sn.get("aligned_at"), *comment_times] if t]
        last_activity = max(last_activity_candidates) if last_activity_candidates else None

        row = dict(
            id=nid, kind=kind, chapter=chapter,
            source_file=source_file, source_line=source_line,
            lean_decl=lean_decl, leanok=leanok,
            nl_hash=sn.get("nl_hash"),
            nl_reviewed=nl_reviewed,
            bound=bound, aligned=aligned, proved=proved,
            nl_reviewer=sn.get("nl_reviewer"),
            align_reviewer=sn.get("align_reviewer"),
            aligned_at=sn.get("aligned_at"),
            last_activity=last_activity,
            phase=derive_phase(dict(
                nl_reviewed=nl_reviewed,
                bound=bound, aligned=aligned, proved=proved,
            )),
        )
        cur.execute("""INSERT INTO nodes
            (id, kind, chapter, source_file, source_line, lean_decl, leanok,
             nl_hash, nl_reviewed, bound, aligned, proved,
             nl_reviewer, align_reviewer, aligned_at, last_activity, phase)
            VALUES (:id,:kind,:chapter,:source_file,:source_line,:lean_decl,:leanok,
                    :nl_hash,:nl_reviewed,:bound,:aligned,:proved,
                    :nl_reviewer,:align_reviewer,:aligned_at,:last_activity,:phase)""",
                    row)

        for i, c in enumerate(sn.get("comments") or []):
            cur.execute("""INSERT INTO node_comments(node_id, idx, topic, text, by, at)
                           VALUES(?,?,?,?,?,?)""",
                        (nid, i, c.get("topic"), c.get("text"), c.get("by"), c.get("at")))

    # =====================================================================
    # write edges (only those whose endpoints are known; orphans logged)
    # =====================================================================
    orphan_edges = 0
    for src, dst in edges:
        if src in all_ids and dst in all_ids:
            cur.execute("""INSERT OR IGNORE INTO edges(from_node, to_node, source, confirmed)
                           VALUES(?,?,?,?)""", (src, dst, "latex", 0))
        else:
            orphan_edges += 1
    if orphan_edges:
        log(f"[kip-state] WARN: {orphan_edges} edges reference unknown labels (skipped)")

    # =====================================================================
    # write lean_decls
    # =====================================================================
    for name, d in lean_decls.items():
        cur.execute("""INSERT INTO lean_decls(name, file, line_start, line_end, sorry_count)
                       VALUES(?,?,?,?,?)""",
                    (name, d["file"], d["line_start"], d["line_end"], d["sorry_count"]))

    # =====================================================================
    # write agent_runs + node associations
    # =====================================================================
    for r in runs:
        cur.execute("""INSERT INTO agent_runs
            (id, agent, started_at, completed_at, status, model, hint_file,
             cost_usd, duration_ms, num_turns, input_tokens, output_tokens,
             summary, log_path)
            VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (r.id, r.agent, r.started_at, r.completed_at, r.status, r.model,
             r.hint_file, r.cost_usd, r.duration_ms, r.num_turns,
             r.input_tokens, r.output_tokens, r.summary, r.log_path))

        # match by literal ID occurrence in summary+log content. Naive but effective
        # because labels like `prereq:def:ss-data` are unique and rarely false-positive.
        if r.touched_text:
            for nid in all_ids:
                if nid in r.touched_text:
                    cur.execute("""INSERT OR IGNORE INTO agent_run_nodes(run_id, node_id)
                                   VALUES(?,?)""", (r.id, nid))

    # =====================================================================
    # back-fill last_activity from agent runs
    # =====================================================================
    cur.execute("""
        UPDATE nodes SET last_activity = COALESCE(
            (SELECT MAX(ar.completed_at)
               FROM agent_run_nodes arn
               JOIN agent_runs ar ON ar.id = arn.run_id
              WHERE arn.node_id = nodes.id
                AND ar.completed_at IS NOT NULL
                AND (nodes.last_activity IS NULL
                     OR ar.completed_at > nodes.last_activity)),
            nodes.last_activity)
    """)

    cur.execute("INSERT INTO meta(key,value) VALUES(?,?)",
                ("indexed_at", datetime.now(timezone.utc).isoformat()))
    cur.execute("INSERT INTO meta(key,value) VALUES(?,?)",
                ("schema_version", "1"))

    conn.commit()
    conn.close()

    # summary line for CI / humans
    print(f"[kip-state] OK · {len(all_ids)} nodes · {len(edges)} edges "
          f"· {len(lean_decls)} lean decls · {len(runs)} agent runs · {db_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
