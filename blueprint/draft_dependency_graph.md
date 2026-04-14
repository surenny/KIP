# Draft Dependency Graph

This is a hand-curated first draft of the proof spine for the current blueprint.
It is intentionally smaller than the full `leanblueprint` graph and focuses on the main theorem and the `h_6^2` argument.

```mermaid
graph TD
  main["thm:main"]
  browder["thm:browder"]
  h62["thm:h62"]
  h62proof["thm:126survives"]
  kdim["cor:kervaire-dimensions"]
  twoline["cor:2line"]

  main --> browder
  main --> h62
  h62 --> h62proof
  kdim --> main
  twoline --> h62

  bjmbx["thm:bjmbx"]
  possible["prop:possibleh62"]
  state5["prop:state5false"]
  eq4["lem:equistate4"]
  eq5["lem:equistate5"]
  x1239["lem:x1239"]
  toda["lem:toda2ext"]
  ext2["cor:2ext125"]
  nuext["lem:nuext125"]

  h62proof --> bjmbx
  h62proof --> possible
  h62proof --> state5

  possible --> bjmbx
  possible --> eq4
  possible --> eq5

  toda --> x1239
  ext2 --> toda
  state5 --> ext2
  state5 --> nuext

  onef["prop:1f7950df"]
  thm4114["thm:4114f70c"]
  cor0012["cor:0012nik"]
  cor166["cor:166dc180"]
  cor290["cor:290d35ce"]
  core7["cor:e7b20ae2"]
  coraed["cor:aed3d1a4"]
  leibniz["thm:e73f481e"]
  may["lem:452d218c"]
  mahowald["thm:158d451a"]
  crossdr["prop:cross-dr-En"]
  crossfr["prop:cross-f-Er"]
  p59["prop:59f111f"]
  ef21["prop:ef21f9bc"]
  p4156["prop:41561db2"]
  fhat["prop:fhat-triangle"]
  p6de7["prop:6de7d130"]
  c2a6["cor:2a636737"]
  pdec["prop:dec738d3"]
  cdfc["cor:dfc6043e"]

  thm4114 --> cor0012
  cor0012 --> cor166
  cor0012 --> cor290
  cor0012 --> core7
  cor0012 --> coraed
  leibniz --> p6de7
  leibniz --> cor0012
  leibniz --> crossdr
  leibniz --> crossfr
  mahowald --> may
  mahowald --> crossdr
  mahowald --> crossfr
  mahowald --> p59
  ef21 --> onef
  p4156 --> onef
  p4156 --> ef21
  fhat --> p4156
  c2a6 --> p6de7
  cdfc --> pdec
```

Open the generated full graph at `web/dep_graph_document.html` after running `bash build.sh`.
