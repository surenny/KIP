#!/usr/bin/env bash
# Invoke the blueprint-absorber agent on a specific draft-hint file.
#
# Usage:
#   ./agents/blueprint-absorber/run.sh draft-hint/SyntheticNu.md
#   ./agents/blueprint-absorber/run.sh draft-hint/crossing.tex
#   ./agents/blueprint-absorber/run.sh   # process ALL draft-hint files
#
# Options:
#   --dry-run        Show what would be processed without invoking claude
#   --model X        Override model (default: sonnet)
#   --verbose-logs   Also save raw stream-json to .raw.jsonl
#
# Prerequisites:
#   - claude CLI available on PATH
#   - pip install -e tools/leanblueprint && pip install -e tools/plastexdepgraph

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
SYSTEM_PROMPT="$SCRIPT_DIR/SYSTEM.md"
SETTINGS="$SCRIPT_DIR/settings.json"
LOGS_DIR="$SCRIPT_DIR/logs"
MODEL="sonnet"
DRY_RUN=false
VERBOSE_LOGS=false

while [[ $# -gt 0 ]]; do
    case "$1" in
        --dry-run)       DRY_RUN=true; shift ;;
        --model)         MODEL="$2"; shift 2 ;;
        --verbose-logs)  VERBOSE_LOGS=true; shift ;;
        --)              shift; break ;;
        *)               break ;;
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

    # --- Log capture setup ---
    RUN_TS="$(date -u +%Y-%m-%dT%H-%M-%SZ)"
    RUN_DIR="$LOGS_DIR/run-${RUN_TS}"
    mkdir -p "$RUN_DIR"

    JSONL_FILE="$RUN_DIR/absorber.jsonl"
    RAW_FILE="$RUN_DIR/absorber.raw.jsonl"
    META_FILE="$RUN_DIR/meta.json"

    # Write initial meta.json
    python3 -c "
import json, sys
meta = {
    'agent': 'blueprint-absorber',
    'hint_file': sys.argv[1],
    'startedAt': sys.argv[2].replace('-', ':', 3).replace('-', ':', 1),
    'completedAt': None,
    'status': 'running',
    'model': sys.argv[3],
}
# Fix timestamp: run-2026-04-21T08-30-00Z -> 2026-04-21T08:30:00Z
ts = sys.argv[2]
parts = ts.split('T')
if len(parts) == 2:
    time_part = parts[1].replace('-', ':', 2)
    meta['startedAt'] = parts[0] + 'T' + time_part
with open(sys.argv[4], 'w') as f:
    json.dump(meta, f, indent=2)
" "$HINT_FILE" "$RUN_TS" "$MODEL" "$META_FILE"

    stderr_dest="/dev/null"
    [[ "$VERBOSE_LOGS" == "true" ]] && stderr_dest="$RAW_FILE"

    # --- Run claude with stream-json output, pipe through log parser ---
    claude -p \
        --model "$MODEL" \
        --system-prompt "$(cat "$SYSTEM_PROMPT")" \
        --settings "$SETTINGS" \
        --tools "Read" "Glob" "Grep" "Edit" "Write" "Bash" "WebFetch" "WebSearch" \
        --strict-mcp-config --mcp-config '{"mcpServers":{}}' \
        --allowedTools "Read" "Glob" "Grep" "Edit" "Write" "WebFetch" "WebSearch" "Bash(leanblueprint *)" "Bash(cat *)" "Bash(ls *)" "Bash(wc *)" \
        --disallowedTools "Bash(git *)" "Bash(gh *)" "Bash(lake *)" "Bash(rm *)" "Bash(mv *)" \
        --verbose --output-format stream-json \
        "Process the following draft-hint file into the blueprint.

File: $HINT_FILE

Content:
$HINT_CONTENT

Instructions:
1. Read the hint above carefully.
2. Identify which blueprint chapter(s) it maps to under blueprint/src/chapters/.
3. Read the relevant chapter TeX and corresponding Lean files.
4. Edit the blueprint TeX to incorporate the mathematician's instructions.
5. IMPORTANT: Re-read the TeX file you just edited to VERIFY your changes are actually present. If the file is unchanged, your edit failed — retry it.
6. Run: cd blueprint && leanblueprint checkdecls
7. If validation passed AND you confirmed the edit persisted (step 5), update $STATUS_FILE:
   - Append the filename under the existing '## Absorbed' section (do NOT create new sections).
   - The format is: - \`filename\` — YYYY-MM-DD
   - If the file was listed under '## Pending', remove it from there.
8. Report what changed and whether validation passed." \
        2>>"$stderr_dest" | python3 -u -c "
import sys, json, datetime, urllib.request, os

VERBOSE = '$VERBOSE_LOGS' == 'true'
RAW = open('$RAW_FILE', 'a') if VERBOSE else None
JSONL = open('$JSONL_FILE', 'a')

_INGEST_URL   = os.getenv('KIP_INGEST_URL', '')
_INGEST_TOKEN = os.getenv('KIP_INGEST_TOKEN', '')
_AGENT        = 'blueprint-absorber'
_RUN_ID       = 'run-$RUN_TS'
_HINT_FILE    = '$HINT_FILE'

def ingest(row):
    if not _INGEST_URL:
        return
    payload = json.dumps({'agent': _AGENT, 'runId': _RUN_ID, 'hintFile': _HINT_FILE, 'row': row}).encode()
    req = urllib.request.Request(_INGEST_URL, data=payload,
        headers={'Content-Type': 'application/json', 'Authorization': 'Bearer ' + _INGEST_TOKEN},
        method='POST')
    try:
        urllib.request.urlopen(req, timeout=3)
    except Exception:
        pass

def emit(event_type, **fields):
    row = {'ts': datetime.datetime.now(datetime.timezone.utc).isoformat().replace('+00:00', 'Z'), 'event': event_type, **fields}
    JSONL.write(json.dumps(row) + '\n')
    JSONL.flush()
    ingest(row)

last_result = ''

for line in sys.stdin:
    line = line.strip()
    if not line:
        continue
    if RAW:
        RAW.write(line + '\n')
        RAW.flush()

    try:
        obj = json.loads(line)
    except json.JSONDecodeError:
        continue

    t = obj.get('type', '')

    if t == 'assistant' and 'message' in obj:
        msg = obj['message']
        if not isinstance(msg, dict):
            continue
        for block in msg.get('content', []):
            bt = block.get('type', '')
            if bt == 'thinking':
                thinking = block.get('thinking', '').strip()
                if thinking:
                    emit('thinking', content=thinking)
            elif bt == 'text':
                text = block.get('text', '').strip()
                if text:
                    emit('text', content=text)
                    last_result = text
            elif bt == 'tool_use':
                name = block.get('name', '?')
                inp = block.get('input', {})
                emit('tool_call', tool=name, input=inp)

    elif t == 'user' and 'message' in obj:
        msg = obj['message']
        if not isinstance(msg, dict):
            continue
        for block in msg.get('content', []):
            if block.get('type') == 'tool_result':
                content = block.get('content', '')
                if isinstance(content, str):
                    emit('tool_result', content=content)
                elif isinstance(content, list):
                    texts = [p.get('text','') for p in content if isinstance(p,dict) and p.get('type')=='text']
                    emit('tool_result', content='\n'.join(texts))

    elif t == 'result':
        cost = obj.get('total_cost_usd', 0) or obj.get('cost_usd', 0) or 0
        duration = obj.get('duration_ms', 0) or 0
        turns = obj.get('num_turns', 0) or 0
        session_id = obj.get('session_id', '') or ''
        result = obj.get('result', '')
        usage = obj.get('usage', {}) or {}
        model_usage = obj.get('modelUsage', {}) or {}
        summary = result if isinstance(result, str) and result else last_result

        emit('session_end',
            session_id=session_id,
            total_cost_usd=cost,
            duration_ms=duration,
            duration_api_ms=usage.get('duration_api_ms', 0) or 0,
            num_turns=turns,
            input_tokens=usage.get('input_tokens', 0) or 0,
            output_tokens=usage.get('output_tokens', 0) or 0,
            cache_read_input_tokens=usage.get('cache_read_input_tokens', 0) or 0,
            cache_creation_input_tokens=usage.get('cache_creation_input_tokens', 0) or 0,
            model_usage=model_usage,
            summary=summary,
        )

        if summary:
            print(summary, flush=True)

        JSONL.close()
        if RAW: RAW.close()
        sys.exit(0)

JSONL.close()
if RAW: RAW.close()
" || true

    # --- Update meta.json with completion status ---
    EXIT_STATUS=$?
    COMPLETED_TS="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    python3 -c "
import json, sys
with open(sys.argv[1]) as f:
    meta = json.load(f)
meta['completedAt'] = sys.argv[2]
meta['status'] = 'done' if int(sys.argv[3]) == 0 else 'error'
with open(sys.argv[1], 'w') as f:
    json.dump(meta, f, indent=2)
" "$META_FILE" "$COMPLETED_TS" "$EXIT_STATUS"

    echo ""
    echo "=== Done: $HINT_FILE (log: $RUN_DIR) ==="
    echo ""
done
