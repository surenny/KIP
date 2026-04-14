#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
SRC="$ROOT/src"

cd "$SRC"

latexmk -output-directory=../print print.tex

if [[ -f print.bbl ]]; then
  cp -f print.bbl web.bbl
fi

python ../prepare_web_sources.py

if command -v plastex >/dev/null 2>&1; then
  plastex -c plastex.cfg web.tex
else
  "$HOME/.local/bin/plastex" -c plastex.cfg web.tex
fi

# Sync web output to docs/blueprint/ for GitHub Pages
DOCS_DIR="$ROOT/../../../docs/blueprint"
if [[ -d "$DOCS_DIR" ]]; then
  rsync -a --delete "$ROOT/web/" "$DOCS_DIR/"
  echo "Synced blueprint web output to docs/blueprint/"
fi
