#!/usr/bin/env bash
set -eu

INPUT_JSON=$(cat)

FILE_PATH=$(printf '%s' "$INPUT_JSON" | jq -r '.tool_input.file_path // empty')

PROJECT_DIR="${CLAUDE_PROJECT_DIR:-/inspire/hdd/project/qproject-fundationmodel/czxs25250150/KIP}"
PROJECT_DIR="${PROJECT_DIR%/}"

ALLOWED_DIRS=(
  "$PROJECT_DIR/blueprint/"
  "$PROJECT_DIR/agents/blueprint-absorber/"
)

if [ -z "$FILE_PATH" ]; then
  jq -n '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:"No file_path provided"}}'
  exit 0
fi

for prefix in "${ALLOWED_DIRS[@]}"; do
  case "$FILE_PATH" in
    "$prefix"*)
      jq -n --arg r "Allowed: inside ${prefix#$PROJECT_DIR/}" \
        '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"allow",permissionDecisionReason:$r}}'
      exit 0
      ;;
  esac
done

jq -n --arg r "Denied: edits restricted to blueprint/ and agents/blueprint-absorber/" \
  '{hookSpecificOutput:{hookEventName:"PreToolUse",permissionDecision:"deny",permissionDecisionReason:$r}}'
exit 0
