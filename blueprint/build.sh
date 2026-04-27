#!/usr/bin/env bash
set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

# ── 1. Build Lean project ──────────────────────────────────────────────
echo "==> lake build"
lake build

# ── 2. Generate doc-gen4 API docs (optional, slow) ─────────────────────
if [[ "${SKIP_DOCS:-}" != "1" ]]; then
  echo "==> lake build KIP:docs  (set SKIP_DOCS=1 to skip)"
  lake build KIP:docs
else
  echo "==> Skipping doc-gen4 (SKIP_DOCS=1)"
fi

# ── 3. Blueprint: PDF + web + checkdecls ───────────────────────────────
#    leanblueprint all = mk_pdf + mk_web + lake build + checkdecls
#    Since we already ran lake build in step 1, call subcommands directly
#    to avoid building twice.
# ── 2.5. Inject annotations into LaTeX source (optional) ──────────────
ANNOTATIONS_JSON="$PROJECT_ROOT/blueprint/annotations-export.json"
if [[ -f "$ANNOTATIONS_JSON" ]]; then
  echo "==> Injecting annotations into LaTeX source"
  python3 "$PROJECT_ROOT/blueprint/inject_annotations.py" "$ANNOTATIONS_JSON"
fi

echo "==> leanblueprint pdf"
leanblueprint pdf

# ── Restore LaTeX source after PDF build (undo injected annotations) ──
if [[ -f "$ANNOTATIONS_JSON" ]]; then
  echo "==> Restoring LaTeX source (removing injected annotations)"
  python3 "$PROJECT_ROOT/blueprint/inject_annotations.py" --restore
fi

echo "==> leanblueprint web"
# Pin the in-browser GitHub-Pages review-commit fallback to this repo. Without
# these env vars, the patched plastexdepgraph emits an empty REPO_CONFIG and
# the floating "Commit Reviews" button is hidden.
LEAN_BLUEPRINT_REPO=surenny/KIP \
LEAN_BLUEPRINT_REPO_BRANCH=main \
LEAN_BLUEPRINT_STATUS_PATH=blueprint/status.yaml \
leanblueprint web

echo "==> leanblueprint checkdecls"
leanblueprint checkdecls

# ── 4. Sync web output to docs/blueprint/ for GitHub Pages ─────────────
DOCS_DIR="$PROJECT_ROOT/docs/blueprint"
WEB_DIR="$PROJECT_ROOT/blueprint/web"
if [[ -d "$WEB_DIR" ]]; then
  mkdir -p "$DOCS_DIR"
  rsync -a --delete "$WEB_DIR/" "$DOCS_DIR/"
  echo "==> Synced blueprint web output to docs/blueprint/"
fi

echo "==> Done"
