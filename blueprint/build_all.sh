#!/usr/bin/env bash
set -euo pipefail

# Full build: PDF + web + Lean
# Usage: cd formal/leanworkspace/blueprint && bash build_all.sh

WORKSPACE="$(cd "$(dirname "$0")/.." && pwd)"
BLUEPRINT="$WORKSPACE/blueprint"

echo "=== Step 1/4: Build PDF ==="
cd "$BLUEPRINT/src"
latexmk -output-directory=../print print.tex
if [[ -f print.bbl ]]; then
  cp -f print.bbl web.bbl
fi

echo "=== Step 2/4: Prepare web sources ==="
python3 "$BLUEPRINT/prepare_web_sources.py"

echo "=== Step 3/4: Build HTML + generate lean_decls ==="
if command -v plastex >/dev/null 2>&1; then
  plastex -c plastex.cfg web.tex
else
  "$HOME/.local/bin/plastex" -c plastex.cfg web.tex
fi

echo "=== Step 4/4: Build Lean ==="
cd "$WORKSPACE"
lake build KervaireInvariant

echo "=== All done ==="
