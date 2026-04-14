# Blueprint \uses{} Review Prompt Template

Use this prompt template for subagents to review and verify `\uses{}` annotations
in specific sections of `content.tex`.

## Template

```
You are reviewing the leanblueprint annotations for Section N of a paper on
algebraic topology (specifically the Kervaire invariant problem and Adams
spectral sequences).

Your task:
1. Read the specified section of `formal/leanworkspace/blueprint/src/content.tex`
2. For each theorem/lemma/corollary/proposition, verify its `\uses{}` annotation:
   - Does the proof genuinely depend on the listed results?
   - Are any dependencies missing?
   - Are there any "background mentions" incorrectly listed as dependencies?

Rules (from AUTHOR_GUIDE.zh.md):
- `\uses{}` should list results whose proof DEPENDS on them
- External theorems cited from literature (no proof in paper) don't need `\uses{}`
- Definitions that are "root" objects don't need `\uses{}`
- Test: "If this prerequisite were deleted, would the proof still work?"
- Err on the side of omitting uncertain dependencies

Section to review: [SECTION_NAME]
Line range: [START_LINE]-[END_LINE]

File: formal/leanworkspace/blueprint/src/content.tex
```

## Section Ranges (after renaming)

| Section | Name | Lines | Key Results |
|---------|------|-------|-------------|
| Sec 1 | Introduction | 12-190 | thm:main, thm:browder, thm:h62, cor:kervaire-dimensions, cor:2line |
| Sec 2 | Extension Spectral Sequence | 191-617 | def:ess, prop:f-ext-characterization, thm:four-spectra, cor:four-spectra, etc. |
| Sec 3 | HF-synthetic spectra | 618-954 | prop:nu-cofiber, thm:rigid, thm:lambda-bockstein, prop:syn-einfty-nuX, etc. |
| Sec 4 | Synthetic Extensions | 955-1233 | prop:lambda-rho-trivial, prop:delta-ess-adams, cor:delta-ess-general, prop:cross-dr-En |
| Sec 5 | Extensions on E_r-page | 1234-1563 | def:f-Er-extension, def:f-Er-crossing, prop:cross-f-Er, prop:enfty-extension-quotient |
| Sec 6 | Gen. Leibniz & Mahowald | 1564-2067 | thm:gen-leibniz, thm:gen-mahowald, prop:ext-across-pages, cor:stretch-extension |
| Sec 7 | Proof of main theorem | 2068-2755 | thm:126survives, thm:bjmbx, prop:possibleh62, prop:state5false, etc. |
| App | Tables | 2756-3271 | (No theorem-like environments) |

## Checklist per Section

For each theorem-like environment:
- [ ] Has a `\label{}`
- [ ] Label is mathematically meaningful (not a hex code)
- [ ] Has `\uses{}` listing proof dependencies (or is a root definition/external result)
- [ ] No circular dependencies
- [ ] No "background mention" incorrectly listed
