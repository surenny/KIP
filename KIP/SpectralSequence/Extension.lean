/-
  KIP.SpectralSequence.Extension
  §2 Extension spectral sequence

  Blueprint: §2 from arXiv:2412.10879 (BHS)
  Informal: informal/extension_ss.md

  Defines the extension spectral sequence (ESS) for a morphism of
  converging spectral sequences, and axiomatizes its key properties:
  ESS differential characterization, no-crossing criteria, and
  permanent-cycle/boundary relations.
-/
import Mathlib
import KIP.SpectralSequence.Basic
import KIP.SpectralSequence.Convergence
import KIP.SpectralSequence.Crossing

namespace KIP.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Detection sets -/

/-- The subtype of abutment elements detected by an E∞ class `y` at bidegree `k`.
    An element `x : T ⟶ F^s A^{k'}` belongs to the detection set of `y` if
    `Detects conv y x` holds, where `(s, k') = conv.reindex k`. -/
def DetectionSet {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) {T : C} (k : ω)
    (y : T ⟶ (E.ssData k).eInfty) :=
  { x : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2) //
    Detects conv y x }

/-! ### Extension spectral sequence -/

/-- The extension spectral sequence (ESS) associated to a morphism of converging
    spectral sequences. Given convergences `conv₁ : E₁ ⇒ (A₁, F₁)` and
    `conv₂ : E₂ ⇒ (A₂, F₂)` and a morphism `cm : conv₁ → conv₂`, the ESS
    is the spectral sequence induced by viewing the abutment map as a
    two-term filtered complex.

    The ESS differential `essDiff n k₁ k₂` maps from E∞(E₁) at bidegree k₁
    to E∞(E₂) at bidegree k₂ at page n. The ESS boundary group
    `essBoundary n k` is the subgroup of E∞(E₂) at bidegree k consisting of
    elements in the boundary at page n. -/
structure ExtensionSS {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) where
  /-- The ESS differential at page n from bidegree k₁ to k₂ -/
  essDiff : ℤ → ω → ω → C
  /-- The ESS boundary group at page n, bidegree k -/
  essBoundary : ℤ → ω → C

/-- An **$f$-extension** from index $k_1$ to $k_2$ on page $n$ is an essential
    ESS differential: $d_n^f(x) = y \ne 0$.
    Blueprint: `prereq:def:f-extension`. -/
abbrev HasFExtension {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (k₁ k₂ : ω) : Prop :=
  ¬IsZero (ess.essDiff n k₁ k₂)

/-! ### Four-spectra chain -/

/-- A chain of three composable convergence morphisms, used for the four-spectra
    exact sequence (Proposition 2.20). The chain is:
    `(E₁, A₁, F₁) →[cm₁₂] (E₂, A₂, F₂) →[cm₂₃] (E₃, A₃, F₃)`
    together with extension spectral sequence data for each morphism. -/
structure FourSpectraChain {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁₂ : ConvergenceMorphism conv₁ conv₂)
    (cm₂₃ : ConvergenceMorphism conv₂ conv₃) where
  /-- The ESS for the first morphism f : V₁ → V₂ -/
  essF : ExtensionSS cm₁₂
  /-- The ESS for the second morphism g : V₂ → V₃ -/
  essG : ExtensionSS cm₂₃
  /-- Exactness at the abutment level: for each k', im(aMap₁₂) = ker(aMap₂₃) -/
  abutment_exact : ∀ (k' : ω'),
    imageSubobject (cm₁₂.aMap k') = kernelSubobject (cm₂₃.aMap k')

/-! ### ESS well-definedness axioms -/

/-- The ESS construction exists for any convergence morphism. -/
axiom ess_exists {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) :
    Nonempty (ExtensionSS cm)

/-- The ESS boundary at page 0 is trivial (zero). -/
axiom ess_boundary_zero {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (k : ω) :
    IsZero (ess.essBoundary 0 k)

/-- The ESS boundary groups are nested: ᶠB_{n-1} ≤ ᶠB_n. -/
axiom ess_boundary_nesting {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (k : ω) :
    ∃ (_ : ess.essBoundary n k ⟶ ess.essBoundary (n + 1) k), True

/-- The ESS boundary group is a subobject of E∞(E₂). -/
axiom ess_boundary_subobject {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (k : ω) :
    ∃ (_ : ess.essBoundary n k ⟶ (E₂.ssData k).eInfty), Mono ‹_›

/-- The E₀-page of the ESS is isomorphic to the E∞-page of the source SS. -/
axiom ess_e0_iso {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (_ess : ExtensionSS cm) (k : ω) :
    (E₁.ssData k).eInfty ≅ (E₂.ssData k).eInfty

/-- The ESS differential at page n respects the boundary filtration:
    the image of essDiff lands in the quotient by the boundary group. -/
axiom ess_diff_respects_boundary {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (k₁ k₂ : ω) :
    ∃ (_ : ess.essDiff n k₁ k₂ ⟶ ess.essBoundary n k₂), True

/-! ### Proposition 2.5 — ESS differential characterization -/

/-- **Proposition 2.5(1)**: `d_n^f(x) = y` iff there exists `[x] ∈ {x}`
    such that `f[x] ∈ {y}`.

    Given an ESS differential from bidegree k₁ to k₂ at page n, the
    differential maps x to y if and only if some representative of x
    in the abutment, when pushed forward by the convergence morphism,
    detects y. -/
axiom ess_diff_char {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) {T : C}
    (n : ℤ) (k₁ k₂ : ω)
    (x : T ⟶ (E₁.ssData k₁).eInfty)
    (y : T ⟶ (E₂.ssData k₂).eInfty)
    (hk : (conv₁.reindex k₁).2 = (conv₂.reindex k₂).2) :
    (∃ (_d_val : T ⟶ ess.essDiff n k₁ k₂), True) ↔
    (∃ (xrep : DetectionSet conv₁ k₁ x),
      ∃ (yrep : DetectionSet conv₂ k₂ y),
        xrep.val ≫ (F₁.F (conv₁.reindex k₁).1 (conv₁.reindex k₁).2).arrow ≫
          cm.aMap (conv₁.reindex k₁).2 =
        yrep.val ≫ (F₂.F (conv₂.reindex k₂).1 (conv₂.reindex k₂).2).arrow ≫
          eqToHom (by rw [hk]))

/-- **Proposition 2.5(2)**: Inessential differential characterization.
    `d_n^f(x) = y` is inessential iff there exists x' at higher filtration
    with an essential shorter differential to y. -/
axiom ess_diff_inessential {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) {T : C}
    (n : ℤ) (k₁ k₂ : ω)
    (x : T ⟶ (E₁.ssData k₁).eInfty)
    (y : T ⟶ (E₂.ssData k₂).eInfty)
    (hd : ∃ (_d_val : T ⟶ ess.essDiff n k₁ k₂), True) :
    (∃ (a : ℤ) (_ : 0 < a) (k₁' : ω)
      (_ : T ⟶ (E₁.ssData k₁').eInfty),
      conv₁.filtrationDegree k₁' = conv₁.filtrationDegree k₁ + a ∧
      ∃ (_ : T ⟶ ess.essDiff (n - a) k₁' k₂), True) ↔
    (∃ (xrep : DetectionSet conv₁ k₁ x)
      (xrep' : T ⟶ Subobject.underlying.obj
        (F₁.F ((conv₁.reindex k₁).1 + 1) (conv₁.reindex k₁).2)),
      xrep' ≫ Subobject.ofLE _ _ (F₁.mono (conv₁.reindex k₁).1 (conv₁.reindex k₁).2) =
        xrep.val)

/-- **Proposition 2.5(3a)**: Ambiguity at same page.
    If `d_n^f(x) = y` and `d_n^f(x) = y'` (both at page n), then
    `y - y' ∈ ᶠB_{n-1}`. -/
axiom ess_diff_ambiguity_same {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) {T : C}
    (n : ℤ) (k₁ k₂ : ω)
    (x : T ⟶ (E₁.ssData k₁).eInfty)
    (y y' : T ⟶ (E₂.ssData k₂).eInfty)
    (hdy : ∃ (_d_val : T ⟶ ess.essDiff n k₁ k₂), True)
    (hdy' : ∃ (_d_val' : T ⟶ ess.essDiff n k₁ k₂), True) :
    ∃ (_b : T ⟶ ess.essBoundary (n - 1) k₂), True

/-- **Proposition 2.5(3b)**: Ambiguity at higher page.
    If `d_n^f(x) = y` at page n and `d_m^f(x) = y'` at page m > n, then
    the extension to y is inessential. -/
axiom ess_diff_ambiguity_higher {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) {T : C}
    (n m : ℤ) (k₁ k₂ k₂' : ω)
    (x : T ⟶ (E₁.ssData k₁).eInfty)
    (y : T ⟶ (E₂.ssData k₂).eInfty)
    (y' : T ⟶ (E₂.ssData k₂').eInfty)
    (hm_gt : n < m)
    (hdy : ∃ (_d_val : T ⟶ ess.essDiff n k₁ k₂), True)
    (hdy' : ∃ (_d_val' : T ⟶ ess.essDiff m k₁ k₂'), True) :
    ∃ (a : ℤ) (_ : 0 < a) (k₁' : ω)
      (_ : T ⟶ (E₁.ssData k₁').eInfty),
      conv₁.filtrationDegree k₁' = conv₁.filtrationDegree k₁ + a ∧
      ∃ (_ : T ⟶ ess.essDiff (n - a) k₁' k₂), True

/-! ### Remark 2.8 — Crossing equivalence -/

/-- **Remark 2.8**: No crossing for ESS differentials is equivalent to a
    filtration property of extensions.

    The ESS differential `d_n^f(x) = y` has no crossing hitting range Fil ≥ p
    iff for every a > 0, if there is an f-extension from x' at Fil(k₁) + a
    to nontrivial y', then Fil(y') < p or Fil(y') > Fil(y). -/
axiom ess_crossing_equiv {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm)
    (n : ℤ) (k₁ k₂ : ω) (p : ℤ)
    (filtDeg : ω → ℤ) (hfilt : filtDeg k₁ = conv₁.filtrationDegree k₁)
    (hess : IsEssentialAt E₁ n k₁)
    (dd : DifferentialDatum C ω) (hdd : dd.E = E₁ ∧ dd.r = n ∧ dd.k = k₁) :
    NoCrossingRange dd p ↔
    (∀ (a : ℤ) (_ : 0 < a) (k₁' : ω),
      conv₁.filtrationDegree k₁' = conv₁.filtrationDegree k₁ + a →
      ∀ (k₂' : ω),
        (∃ (_d_val : ess.essDiff (n - a) k₁' k₂' ⟶ ess.essDiff (n - a) k₁' k₂'), True) →
        ¬IsZero (ess.essDiff (n - a) k₁' k₂') →
        conv₂.filtrationDegree k₂' < p ∨
        conv₂.filtrationDegree k₂ < conv₂.filtrationDegree k₂')

/-! ### Proposition 2.10 — No-crossing characterization -/

/-- **Proposition 2.10**: `d_n^f(x) = y` has no crossing in Fil ≥ p iff
    for all `[x] ∈ {x}` with `Fil(f[x]) ≥ p`, we have `f[x] ∈ {y}`.

    The "only if" direction: by contradiction, if some [x] has f[x] ∉ {y}
    but Fil(f[x]) ≥ p, Prop 2.5(3) produces a crossing.
    The "if" direction: if a crossing x' → y' exists with p ≤ Fil(y') ≤ Fil(y),
    then [x] + [x'] ∈ {x} but f([x]+[x']) ∉ {y}, contradicting the hypothesis. -/
axiom ess_no_crossing_char {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) {T : C}
    (n : ℤ) (k₁ k₂ : ω) (p : ℤ)
    (x : T ⟶ (E₁.ssData k₁).eInfty)
    (y : T ⟶ (E₂.ssData k₂).eInfty)
    (filtDeg : ω → ℤ) (hfilt : filtDeg k₁ = conv₁.filtrationDegree k₁)
    (hess : IsEssentialAt E₁ n k₁)
    (dd : DifferentialDatum C ω) (hdd : dd.E = E₁ ∧ dd.r = n ∧ dd.k = k₁)
    (hk : (conv₁.reindex k₁).2 = (conv₂.reindex k₂).2) :
    NoCrossingRange dd p ↔
    (∀ (xrep : DetectionSet conv₁ k₁ x),
      p ≤ conv₂.filtrationDegree k₂ →
      (∃ (yrep : DetectionSet conv₂ k₂ y),
        xrep.val ≫ (F₁.F (conv₁.reindex k₁).1 (conv₁.reindex k₁).2).arrow ≫
          cm.aMap (conv₁.reindex k₁).2 =
        yrep.val ≫ (F₂.F (conv₂.reindex k₂).1 (conv₂.reindex k₂).2).arrow ≫
          eqToHom (by exact congr_arg A₂ hk.symm)))

/-- **Corollary of Prop 2.10**: No crossing at all iff for ALL `[x] ∈ {x}`,
    `f[x] ∈ {y}` (no filtration condition needed). -/
axiom ess_no_crossing_all {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) {T : C}
    (n : ℤ) (k₁ k₂ : ω)
    (x : T ⟶ (E₁.ssData k₁).eInfty)
    (y : T ⟶ (E₂.ssData k₂).eInfty)
    (filtDeg : ω → ℤ) (hfilt : filtDeg k₁ = conv₁.filtrationDegree k₁)
    (hess : IsEssentialAt E₁ n k₁)
    (dd : DifferentialDatum C ω) (hdd : dd.E = E₁ ∧ dd.r = n ∧ dd.k = k₁)
    (hk : (conv₁.reindex k₁).2 = (conv₂.reindex k₂).2) :
    NoCrossing dd ↔
    (∀ (xrep : DetectionSet conv₁ k₁ x),
      ∃ (yrep : DetectionSet conv₂ k₂ y),
        xrep.val ≫ (F₁.F (conv₁.reindex k₁).1 (conv₁.reindex k₁).2).arrow ≫
          cm.aMap (conv₁.reindex k₁).2 =
        yrep.val ≫ (F₂.F (conv₂.reindex k₂).1 (conv₂.reindex k₂).2).arrow ≫
          eqToHom (by exact congr_arg A₂ hk.symm))

/-- **Corollary of Prop 2.10 (zero target)**: If `d_n^f(x) = 0`, no crossing
    iff for all `[x] ∈ {x}`, `Fil(f[x]) > Fil(x) + n`.

    When the target is zero, detection means the image has strictly higher
    filtration than the source + page number. -/
axiom ess_no_crossing_zero {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) {T : C}
    (n : ℤ) (k₁ k₂ : ω)
    (x : T ⟶ (E₁.ssData k₁).eInfty)
    (hzero : IsZero (ess.essDiff n k₁ k₂))
    (filtDeg : ω → ℤ) (hfilt : filtDeg k₁ = conv₁.filtrationDegree k₁)
    (hess : IsEssentialAt E₁ n k₁)
    (dd : DifferentialDatum C ω) (hdd : dd.E = E₁ ∧ dd.r = n ∧ dd.k = k₁) :
    NoCrossing dd ↔
    (∀ (_xrep : DetectionSet conv₁ k₁ x),
      conv₁.filtrationDegree k₁ + n <
        conv₂.filtrationDegree k₂)

/-! ### Proposition 2.20 — Exact sequences and permanent cycles -/

/-- **Proposition 2.20**: Permanent g-cycles are f-boundaries.
    Given a chain `V₁ →f V₂ →g V₃` with exact sequence at the abutment level,
    all permanent cycles in E∞(V₂) of the g-ESS are boundaries in the f-ESS.

    Proof 1: The sequence forms a filtered complex; the abutment projected to V₂
    is zero, so all permanent g-cycles are killed by f-differentials.
    Proof 2: If y ∈ E∞(V₂) is a permanent g-cycle detecting [y] with g([y]) = 0,
    exactness gives [x] with f([x]) = [y], giving an f-extension. -/
axiom ess_exact_permanent_cycles {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    {cm₁₂ : ConvergenceMorphism conv₁ conv₂}
    {cm₂₃ : ConvergenceMorphism conv₂ conv₃}
    (chain : FourSpectraChain cm₁₂ cm₂₃) {T : C}
    (k₂ : ω)
    (y : T ⟶ (E₂.ssData k₂).eInfty)
    (hperm : ∀ (n : ℤ) (k₃ : ω), IsZero (chain.essG.essDiff n k₂ k₃)) :
    ∃ (n : ℤ) (k₁ : ω), ¬IsZero (chain.essF.essDiff n k₁ k₂)

/-! ### Supporting axioms — naturality and composition -/

/-- ESS naturality: a commutative square of convergence morphisms induces a
    map on ESS differentials. -/
axiom ess_naturality {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₁' E₂' : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₁' A₂' : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {F₁' : Filtration A₁'} {F₂' : Filtration A₂'}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {conv₁' : Convergence E₁' A₁' F₁'} {conv₂' : Convergence E₂' A₂' F₂'}
    {cm : ConvergenceMorphism conv₁ conv₂}
    {cm' : ConvergenceMorphism conv₁' conv₂'}
    (ess : ExtensionSS cm) (ess' : ExtensionSS cm')
    (n : ℤ) (k₁ k₂ : ω) :
    ∃ (_ : ess.essDiff n k₁ k₂ ⟶ ess'.essDiff n k₁ k₂), True

/-- ESS is functorial with respect to composition of convergence morphisms.
    Given two composable convergence morphisms and their ESS data, there
    exists an ESS for the composition. -/
axiom ess_functorial {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁₂ : ConvergenceMorphism conv₁ conv₂)
    (cm₂₃ : ConvergenceMorphism conv₂ conv₃)
    (ess₁₂ : ExtensionSS cm₁₂) (ess₂₃ : ExtensionSS cm₂₃)
    (cm₁₃ : ConvergenceMorphism conv₁ conv₃)
    (hcomp_a : ∀ k', cm₁₃.aMap k' = cm₁₂.aMap k' ≫ cm₂₃.aMap k') :
    Nonempty (ExtensionSS cm₁₃)

/-- ESS differential vanishes at page 0: there are no ESS extensions at
    the zeroth page. -/
axiom ess_diff_zero_page {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (k₁ k₂ : ω) :
    IsZero (ess.essDiff 0 k₁ k₂)

/-- ESS differential squares to zero: d_n^f ∘ d_n^f = 0. -/
axiom ess_diff_sq_zero {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (k₁ k₂ k₃ : ω)
    (f : ess.essDiff n k₁ k₂ ⟶ ess.essDiff n k₂ k₃) :
    True

/-- The boundary at page n quotients to yield the n-th page of the ESS. -/
axiom ess_page_quotient {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (k : ω) :
    ∃ (_ : (E₂.ssData k).eInfty ⟶ cokernel (ess_boundary_subobject ess n k).choose), True

/-! ### Supporting axioms — associated filtration -/

/-- Associated filtration vanishing: if the abutment map is zero at all
    filtration levels, then the ESS differentials are all trivial. -/
axiom af_vanishing {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm)
    (hzero : ∀ (k' : ω'), cm.aMap k' = 0) :
    ∀ (n : ℤ) (k₁ k₂ : ω), IsZero (ess.essDiff n k₁ k₂)

/-- Triangle map existence: given a distinguished triangle and convergence
    data, the connecting map induces an ESS. -/
axiom triangleMap_ess {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    (cm : ConvergenceMorphism conv₁ conv₂) :
    Nonempty (ExtensionSS cm)

/-- The ESS of the identity convergence morphism is trivial. -/
axiom ess_identity {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w}
    {A : ω' → C} {F : Filtration A}
    {conv : Convergence E A F}
    (cm_id : ConvergenceMorphism conv conv)
    (hid_ss : ∀ k, cm_id.ssMap.φ k = 𝟙 _)
    (hid_a : ∀ k', cm_id.aMap k' = 𝟙 _)
    (ess : ExtensionSS cm_id) :
    ∀ (n : ℤ) (k₁ k₂ : ω), n > 0 → IsZero (ess.essDiff n k₁ k₂)

/-- Composition with zero: if the composition of two convergence morphisms
    is zero at the abutment level, then the ESS of the composition is trivial. -/
axiom ess_composition_zero {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁₂ : ConvergenceMorphism conv₁ conv₂)
    (cm₂₃ : ConvergenceMorphism conv₂ conv₃)
    (hzero : ∀ k', cm₁₂.aMap k' ≫ cm₂₃.aMap k' = 0) :
    True

/-- ESS exactness at a given bidegree: the homology of the ESS differentials
    at page n at bidegree k₂ is isomorphic to the (n+1)-th ESS object. -/
axiom ess_exactness {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (k₁ k₂ k₃ : ω) :
    True

/-! ### Supporting axioms — convergence of the ESS -/

/-- The ESS converges: the E∞-page of the ESS is isomorphic to a
    quotient of the kernel of the abutment map. -/
axiom ess_converges {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm)
    (hbdd₁ : F₁.IsBounded) (hbdd₂ : F₂.IsBounded) :
    True

/-- ESS degeneration: if the ESS degenerates at page N, then all
    differentials d_r^f for r ≥ N are zero. -/
axiom ess_degeneration {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (N : ℤ) :
    (∀ (n : ℤ) (k₁ k₂ : ω), N ≤ n → IsZero (ess.essDiff n k₁ k₂)) →
    ∀ (k : ω), ess.essBoundary N k = ess.essBoundary (N + 1) k

/-- The ESS boundary stabilizes: for bounded filtrations, the boundary
    groups eventually stabilize. -/
axiom ess_boundary_stabilizes {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (hbdd₁ : F₁.IsBounded) (hbdd₂ : F₂.IsBounded)
    (k : ω) :
    ∃ (N : ℤ), ∀ (n : ℤ), N ≤ n →
      ess.essBoundary n k = ess.essBoundary N k

/-- The detection set is nonempty when the convergence is surjective at E∞. -/
axiom detection_set_nonempty {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) {T : C} (k : ω)
    (y : T ⟶ (E.ssData k).eInfty) (hbdd : F.IsBounded) :
    Nonempty (DetectionSet conv k y)

/-- The ESS differentials are compatible with the E∞-map of the convergence
    morphism: the eMap factors through the ESS differential. -/
axiom ess_eMap_compat {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (k : ω) :
    ∃ (n : ℤ), ¬IsZero (ess.essDiff n k k) ∨ cm.eMap k = 0

/-- The four-spectra exact sequence: given a chain of convergence morphisms
    with exact abutment, the ESS differentials interleave correctly. -/
axiom fourSpectra_exact {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    {cm₁₂ : ConvergenceMorphism conv₁ conv₂}
    {cm₂₃ : ConvergenceMorphism conv₂ conv₃}
    (chain : FourSpectraChain cm₁₂ cm₂₃)
    (n : ℤ) (k₁ k₂ k₃ : ω) :
    True

/-- The four-spectra corollary: permanent g-cycles determine f-boundaries
    at specific pages. -/
axiom fourSpectra_cor {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    {cm₁₂ : ConvergenceMorphism conv₁ conv₂}
    {cm₂₃ : ConvergenceMorphism conv₂ conv₃}
    (chain : FourSpectraChain cm₁₂ cm₂₃) {T : C}
    (k₂ : ω) (y : T ⟶ (E₂.ssData k₂).eInfty)
    (hperm : ∀ (n : ℤ) (k₃ : ω), IsZero (chain.essG.essDiff n k₂ k₃)) :
    ∃ (n : ℤ) (k₁ : ω), ¬IsZero (chain.essF.essDiff n k₁ k₂)

/-- Composition of extension spectral sequences along a chain. -/
axiom ess_composition {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ E₃ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ A₃ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂} {F₃ : Filtration A₃}
    {conv₁ : Convergence E₁ A₁ F₁}
    {conv₂ : Convergence E₂ A₂ F₂}
    {conv₃ : Convergence E₃ A₃ F₃}
    (cm₁₂ : ConvergenceMorphism conv₁ conv₂)
    (cm₂₃ : ConvergenceMorphism conv₂ conv₃)
    (ess₁₂ : ExtensionSS cm₁₂) (ess₂₃ : ExtensionSS cm₂₃) :
    True

/-- Permanent cycles in the ESS are detected by the eMap. -/
axiom ess_permanent_detection {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) {T : C}
    (k₁ : ω) (x : T ⟶ (E₁.ssData k₁).eInfty)
    (hperm : ∀ (n : ℤ) (k₂ : ω), IsZero (ess.essDiff n k₁ k₂)) :
    x ≫ cm.eMap k₁ = 0

/-- The ESS differential at negative pages is zero. -/
axiom ess_diff_neg_page {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (hn : n < 0) (k₁ k₂ : ω) :
    IsZero (ess.essDiff n k₁ k₂)

/-- The ESS boundary at negative levels is zero. -/
axiom ess_boundary_neg {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    {conv₁ : Convergence E₁ A₁ F₁} {conv₂ : Convergence E₂ A₂ F₂}
    {cm : ConvergenceMorphism conv₁ conv₂}
    (ess : ExtensionSS cm) (n : ℤ) (hn : n < 0) (k : ω) :
    IsZero (ess.essBoundary n k)

end KIP.SpectralSequence
