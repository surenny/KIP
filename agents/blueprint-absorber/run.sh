#!/usr/bin/env bash
# Invoke the blueprint-absorber agent on a specific draft-hint file.
#
# Usage:
#   ./agents/blueprint-absorber/run.sh draft-hint/SyntheticNu.md
#   ./agents/blueprint-absorber/run.sh draft-hint/crossing.tex
#   ./agents/blueprint-absorber/run.sh   # process ALL draft-hint files
#
# Options:
#   --dry-run    Show what would be processed without invoking claude
#   --model X    Override model (default: sonnet)
#
# Prerequisites:
#   - claude CLI available on PATH
#   - pip install -e tools/leanblueprint && pip install -e tools/plastexdepgraph

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SYSTEM_PROMPT="$SCRIPT_DIR/SYSTEM.md"
SETTINGS="$SCRIPT_DIR/settings.json"
MODEL="sonnet"
DRY_RUN=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --dry-run) DRY_RUN=true; shift ;;
        --model)   MODEL="$2"; shift 2 ;;
        --)        shift; break ;;
        *)         break ;;
    esac
done

cd "$PROJECT_ROOT"

# Collect target files
if [[ $# -gt 0 ]]; then
    FILES=("$@")
else
    FILES=(draft-hint/*)
fi

for HINT_FILE in "${FILES[@]}"; do
    if [[ ! -f "$HINT_FILE" ]]; then
        echo "ERROR: $HINT_FILE not found" >&2
        continue
    fi

    echo "=== Processing: $HINT_FILE ==="

    if $DRY_RUN; then
        echo "[dry-run] Would invoke claude -p on $HINT_FILE"
        continue
    fi

    HINT_CONTENT="$(cat "$HINT_FILE")"

    STATUS_FILE="$SCRIPT_DIR/STATUS.md"

    claude -p \
        --model "$MODEL" \
        --system-prompt "$(cat "$SYSTEM_PROMPT")" \
        --settings "$SETTINGS" \
        --tools "Read" "Glob" "Grep" "Edit" "Write" "Bash" "WebFetch" "WebSearch" \
        --strict-mcp-config --mcp-config '{"mcpServers":{}}' \
        --allowedTools "Read" "Glob" "Grep" "Edit" "Write" "WebFetch" "WebSearch" "Bash(leanblueprint *)" "Bash(cat *)" "Bash(ls *)" "Bash(wc *)" \
        --disallowedTools "Bash(git *)" "Bash(gh *)" "Bash(lake *)" "Bash(rm *)" "Bash(mv *)" \
        --verbose \
        "Process the following draft-hint file into the blueprint.

File: $HINT_FILE

Content:
$HINT_CONTENT

Instructions:
1. Read the hint above carefully.
2. Identify which blueprint chapter(s) it maps to under blueprint/src/chapters/.
3. Read the relevant chapter TeX and corresponding Lean files.
4. Edit the blueprint TeX to incorporate the mathematician's instructions.
5. Run: cd blueprint && leanblueprint checkdecls
6. If validation passed, update $STATUS_FILE: move this file from Pending to Absorbed with today's date.
7. Report what changed and whether validation passed."

    echo ""
    echo "=== Done: $HINT_FILE ==="
    echo ""
done
