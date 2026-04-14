# Label Mapping: Encoded -> Meaningful

This file documents the label renames applied to `blueprint/src/content.tex`.
All encoded (hex/random) labels are replaced with mathematically meaningful names.

## Section 1 (Introduction) - Already meaningful, no changes needed
- `thm:main` - Main theorem (Kervaire invariant one in dim 126)
- `cor:kervaire-dimensions` - Kervaire dimensions corollary
- `thm:browder` - Browder's theorem
- `thm:h62` - h_6^2 survives
- `cor:2line` - Adams 2-line corollary
- `que:2theta6` - Question on 2*theta_6
- `que:theta5sq` - Question on theta_5^2

## Section 2 (A Spectral Sequence for Extensions)

| Old Label | New Label | Mathematical Meaning |
|-----------|-----------|---------------------|
| `sec:e6be737c` | `sec:ess` | Extension Spectral Sequence section |
| `nota:6fb333a2` | `nota:ess-notation` | Z_f, B_f subgroups and ESS notation |
| `def:768fba8a` | `def:f-extension` | f-extension and essential/inessential |
| `prop:8154e6f1` | `prop:f-ext-characterization` | Characterization of f-extensions via homotopy |
| `def:98skj23` | `def:crossing` | Crossing of an f-extension |
| `prop:i8r47oe` | `prop:no-crossing-iff` | No-crossing iff characterization |
| `thm:4114f70c` | `thm:four-spectra` | Four-spectra commutative square theorem |
| `eq:9d45feac` | `eq:p-representative` | p[x] in {z} |
| `eq:36e72616` | `eq:f-representative` | f[x] in {y} |
| `fig:4f154a8` | `fig:four-spectra` | Four-spectra diagram |
| `cor:0012nik` | `cor:four-spectra` | Four-spectra corollary (no-crossing version) |
| `cor:166dc180` | `cor:triangle-map` | Triangle with map corollary |
| `cor:290d35ce` | `cor:composition-ext` | Composition of extensions corollary |
| `cor:e7b20ae2` | `cor:ess-naturality` | ESS naturality map |
| `cor:aed3d1a4` | `cor:composition-zero` | gf=0 implies permanent g-cycle |
| `prop:cfe810af` | `prop:ess-exactness` | Exact sequence => g-cycles are f-boundaries |
| `eq:8c7eec14` | `eq:exact-chain` | 0->pi_*X->pi_*Y->pi_*Z->0 chain |

## Section 3 (HF-synthetic spectra)

| Old Label | New Label | Mathematical Meaning |
|-----------|-----------|---------------------|
| `prop:1f7950df` | `prop:nu-cofiber` | nu preserves cofiber iff HF-homology short exact |
| `thm:17e90ac0` | `thm:lambda-bockstein` | synASS isomorphic to lambda-Bockstein SS |
| `prop:30e8b746` | `prop:syn-einfty-nuX` | E_infty of synASS for nu X |
| `prop:59f111f` | `prop:syn-einfty-mod-lambda` | E_infty of synASS for nu X/lambda^r |
| `prop:ef21f9bc` | `prop:synthetic-lift` | Synthetic lift of AF=k map |
| `prop:41561db2` | `prop:syn-distinguished-triangle` | Synthetic distinguished triangle with hat-h |

## Section 4 (Synthetic Extensions)

| Old Label | New Label | Mathematical Meaning |
|-----------|-----------|---------------------|
| `prop:9770ae6e` | `prop:lambda-rho-trivial` | lambda^n and rho have only d_0 extensions |
| `eq:d8ee7ffe` | `eq:lambda-rho-exact` | Exactness of lambda^n and rho on E_infty |
| `prop:6de7d130` | `prop:delta-ess-adams` | delta-ESS encodes classical Adams differentials |
| `eq:24e1e3f6` | `eq:delta-induction-ge` | Induction step for r>=n+1 |
| `eq:2f8e024e` | `eq:delta-induction-le` | Induction step for r<=n+1 |
| `cor:2a636737` | `cor:delta-ess-general` | General form of delta-ESS differential |
| `eq:841425e9` | `eq:delta-ess-formula` | d^delta_r(lambda^a x) = lambda^{a+r-n-1} y |
| `rmk:qvoewfj` | `rmk:delta-ess-equiv-classical` | delta-ESS equivalent to classical Adams |
| `fig:f5eae42a` | `fig:crossing-En` | Crossing of d_r on E_{n+1}-page |

## Section 5 (Extensions on a classical E_r-page)

| Old Label | New Label | Mathematical Meaning |
|-----------|-----------|---------------------|
| `eq:eae450fe` | `eq:fhat-ess-source` | Source subgroup of fhat_{r-1}-ESS |
| `eq:334248d2` | `eq:fhat-ess-target` | Target quotient of fhat_{r-1}-ESS |
| `def:6c076a33` | `def:f-Er-extension` | (f,E_r)-extension definition |
| `eq:b98be76a` | `eq:f-Er-ext-classical` | d_n^{f,E_r}(x)=y |
| `eq:a020bad3` | `eq:f-Er-ext-synthetic` | d_n^{fhat_{r-1}}(x)=lambda^{n-e(f)} y |
| `fig:3d966cc4` | `fig:f-Er-extension` | (f,E_r)-extension diagram |
| `def:fErextess` | `def:fErextess` | (kept, already readable) |
| `def:41d51149` | `def:f-Er-crossing` | Crossing of (f,E_r)-extension |
| `fig:66241bf6` | `fig:f-Er-crossing` | Crossing of (f,E_r)-extension diagram |
| `eq:f7a7a418` | `eq:syn-crossing-form` | Synthetic crossing form |
| `eq:5742281` | `eq:syn-crossing-lift` | Lifted synthetic crossing |
| `prop:enfty-extension-quotient` | (keep) | Already meaningful |

## Section 6 (Generalized Leibniz Rule and Mahowald Trick)

| Old Label | New Label | Mathematical Meaning |
|-----------|-----------|---------------------|
| `thm:e73f481e` | `thm:gen-leibniz` | Generalized Leibniz Rule |
| `eq:ca3fdd92` | `eq:leibniz-delta-diff` | delta-differential in Leibniz proof |
| `eq:b2aa5032` | `eq:leibniz-fhat-diff` | fhat-differential in Leibniz proof |
| `eq:886aee9b` | `eq:leibniz-fhat-xinfty` | fhat applied to lambda^{r-n} x_infty |
| `lem:452d218c` | `lem:may-smash` | May's smash product lemma |
| `thm:158d451a` | `thm:gen-mahowald` | Generalized Mahowald Trick |
| `fig:2aa45b21` | `fig:gen-mahowald` | Generalized Mahowald Trick diagram |
| `fig:2d013742` | `fig:smash-homotopy` | Smash product homotopy elements |
| `eq:70327019` | `eq:mahowald-cond-a` | Mahowald trick condition (a) |
| `eq:e129d90c` | `eq:mahowald-cond-b` | Mahowald trick condition (b) |
| `eq:f4848f29` | `eq:mahowald-rho-eq` | rho relation in Mahowald proof |
| `eq:fba35e4e` | `eq:mahowald-fhat-eq` | fhat relation in Mahowald proof |
| `prop:dec738d3` | `prop:ext-across-pages` | Extension across pages |
| `eq:dcd62a19` | `eq:inessential-crossing` | Inessential crossing form |
| `fig:b22d961f` | `fig:ext-across-pages` | Extensions across pages diagram |
| `cor:dfc6043e` | `cor:stretch-extension` | Stretch extension to higher pages |

## Section 7 (Proof of main theorem) - Already mostly meaningful
- `thm:126survives` (keep)
- `thm:bjmbx` (keep)
- `rem:theta5choice` (keep)
- `fact:theta5sqAF` (keep)
- `prop:possibleh62` (keep)
- `prop:state5false` (keep)
- `lem:equistate4` (keep)
- `lem:equistate5` (keep)
- `fact:x1239` (keep)
- `lem:x1239` (keep)
- `fact:h02x1259` (keep)
- `lem:toda2ext` (keep)
- `rem:h02x1259` (keep)
- `cor:2ext125` (keep)
- `fact:h1x1217` (keep)
- `lem:nuext125` (keep)
- `fact:stem122` (keep)
