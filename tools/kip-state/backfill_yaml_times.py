#!/usr/bin/env python3
"""One-shot upgrade for legacy date-only timestamps in blueprint/status.yaml.

Older entries store `nl_reviewed_at`, `aligned_at`, and `comments[].at` as
plain dates (e.g. '2026-04-19'). The dashboard wants minute-level precision so
reviewers can compare when each comment landed; the indexer's relative-time
display also needs an unambiguous instant.

This script rewrites every date-only string into noon Beijing of that date —
'2026-04-19T12:00:00+08:00' — which is:

  * minute-precise (so the UI no longer falls back to a bare date),
  * a defensible midpoint that doesn't drift more than 12h in either zone,
  * lexicographically equal to the original date for index.py's `max(...)`
    over `last_activity` (still sorts on day boundaries),
  * idempotent: re-running won't touch already-precise ISO timestamps.

Run from project root:
    python3 tools/kip-state/backfill_yaml_times.py [--dry-run]

Always keep the previous file as `.bak` next to it for trivial rollback.
"""
from __future__ import annotations
import argparse
import re
import shutil
import sys
from pathlib import Path

import yaml

DATE_ONLY = re.compile(r"^\d{4}-\d{2}-\d{2}$")
NOON_BEIJING_SUFFIX = "T12:00:00+08:00"


def upgrade(value: object) -> tuple[object, bool]:
    if isinstance(value, str) and DATE_ONLY.match(value):
        return value + NOON_BEIJING_SUFFIX, True
    return value, False


def walk(data: dict) -> int:
    """Walk known timestamp fields under data['nodes'][*]. Returns change count."""
    changed = 0
    nodes = data.get("nodes") or {}
    for entry in nodes.values():
        if not isinstance(entry, dict):
            continue
        for key in ("nl_reviewed_at", "aligned_at"):
            new, was_changed = upgrade(entry.get(key))
            if was_changed:
                entry[key] = new
                changed += 1
        for c in entry.get("comments") or []:
            if not isinstance(c, dict):
                continue
            new, was_changed = upgrade(c.get("at"))
            if was_changed:
                c["at"] = new
                changed += 1
    return changed


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--project", type=Path, default=Path.cwd())
    ap.add_argument("--dry-run", action="store_true",
                    help="report changes without writing")
    args = ap.parse_args(argv)

    yaml_path = args.project / "blueprint" / "status.yaml"
    if not yaml_path.exists():
        print(f"error: not found: {yaml_path}", file=sys.stderr)
        return 1

    text = yaml_path.read_text()
    data = yaml.safe_load(text) or {}
    n = walk(data)
    print(f"upgraded {n} date-only timestamp(s) in {yaml_path}")
    if args.dry_run or n == 0:
        return 0

    bak = yaml_path.with_suffix(yaml_path.suffix + ".bak")
    shutil.copy2(yaml_path, bak)
    yaml_path.write_text(yaml.safe_dump(
        data, allow_unicode=True, sort_keys=False, default_flow_style=False))
    print(f"wrote new {yaml_path} (backup at {bak})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
