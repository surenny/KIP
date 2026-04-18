# Extended Node State System — Development Guide

## What this is

This branch implements surenny/KIP#2: a 6-state lifecycle for blueprint nodes to support AI-assisted formalization workflows.

## Branch setup

```bash
git checkout feat/extended-node-states
pip install -e tools/plastexdepgraph
pip install -e tools/leanblueprint
```

## Key files

- `tools/leanblueprint/leanblueprint/Packages/blueprint.py` — colorizer/fillcolorizer/state logic (main target)
- `tools/leanblueprint/leanblueprint/client.py` — CLI entry point, add `status` subcommand here
- `tools/plastexdepgraph/plastexdepgraph/Packages/depgraph.py` — dependency graph structure (already patched for cross-section deps)
- `tools/plastexdepgraph/plastexdepgraph/templates/dep_graph.html` — graph page template, modal popups
- `blueprint/status.yaml` — new file, node state storage

## Architecture

```
blueprint/src/*.tex  →  leanblueprint (reads \lean{}\leanok + status.yaml)  →  blueprint/web/*.html
                              ↑
                    tools/leanblueprint/  (colorizer, fillcolorizer, legend)
                    tools/plastexdepgraph/ (graph structure, templates)
```

leanblueprint delegates graph rendering to plastexdepgraph via callbacks:
- `document.userdata['dep_graph']['colorizer']` → border color function
- `document.userdata['dep_graph']['fillcolorizer']` → fill color function
- `document.userdata['dep_graph']['legend']` → legend entries list

## Testing

```bash
cd /path/to/KIP/blueprint
leanblueprint web          # rebuild HTML
leanblueprint checkdecls   # verify Lean bindings
# Then open blueprint/web/index.html or run: python3 -m http.server 18080 --directory blueprint/web/
```

## Full spec

See surenny/KIP#2 for the complete design: 6 states, YAML schema, color palette, file modification list, implementation order.
