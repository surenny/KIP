/-
  KIP.SpectralSequence.Convergence
  §1.2 Convergence of spectral sequences — filtrations, graded pieces,
  detection, category of converging spectral sequences

  Blueprint: prerequisites.tex §1.2 (filtration through detect-difference)
  Informal:  informal/spectral_sequences.md §Convergence.lean

  All filtrations are decreasing. Convergence is in the weak sense
  (no strong convergence considerations).
-/
import Mathlib
import KIP.SpectralSequence.Basic

namespace KIP.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Filtrations

A decreasing filtration on a graded object `A : ω → C` is a family of
subobjects `F^s A^k ≤ A^k` indexed by `s : ℤ` and `k : ω`, such that
`F^{s+1} A^k ≤ F^s A^k` for all `s`, `k`. -/

/-- A decreasing filtration on a graded object `A : ω → C`.
    `F s k` is the subobject `F^s A^k ≤ A^k`. Monotonicity says
    `F^{s+1} ≤ F^s` (decreasing filtration). -/
structure Filtration {ω : Type w} (A : ω → C) where
  /-- The subobject `F^s A^k` of `A k` at filtration level `s`. -/
  F : ℤ → (k : ω) → Subobject (A k)
  /-- Filtration is decreasing: `F^{s+1} ≤ F^s`. -/
  mono : ∀ (s : ℤ) (k : ω), F (s + 1) k ≤ F s k

/-- A filtration is bounded if for each `k`, there exist bounds `a ≤ b`
    such that `F^s A^k = A^k` for `s ≤ a` and `F^s A^k = 0` for `s ≥ b`. -/
structure Filtration.IsBounded {ω : Type w} {A : ω → C}
    (fil : Filtration A) where
  /-- Lower bound: for `s ≤ lo k`, the filtration is everything. -/
  lo : ω → ℤ
  /-- Upper bound: for `s ≥ hi k`, the filtration is trivial. -/
  hi : ω → ℤ
  /-- `lo ≤ hi`. -/
  lo_le_hi : ∀ (k : ω), lo k ≤ hi k
  /-- `F^s = A` for `s ≤ lo`. -/
  boundedBelow : ∀ (k : ω) (s : ℤ), s ≤ lo k → fil.F s k = ⊤
  /-- `F^s = 0` for `s ≥ hi`. -/
  boundedAbove : ∀ (k : ω) (s : ℤ), hi k ≤ s → fil.F s k = ⊥

/-! ### Associated graded

The associated graded of a filtration is the family of quotients
`gr^s A^k = F^s A^k / F^{s+1} A^k`, defined as the cokernel of the
inclusion `F^{s+1} ↪ F^s` obtained from monotonicity. -/

/-- The associated graded `gr^s A^k = F^s A^k / F^{s+1} A^k`, defined as
    the cokernel of the inclusion `F^{s+1} ↪ F^s`. -/
noncomputable def Filtration.associatedGraded {ω : Type w} {A : ω → C}
    (fil : Filtration A) (s : ℤ) (k : ω) : C :=
  cokernel (Subobject.ofLE (fil.F (s + 1) k) (fil.F s k) (fil.mono s k))

/-- The projection morphism `F^s A^k ⟶ gr^s A^k = F^s / F^{s+1}`. -/
noncomputable def Filtration.toAssociatedGraded {ω : Type w} {A : ω → C}
    (fil : Filtration A) (s : ℤ) (k : ω) :
    Subobject.underlying.obj (fil.F s k) ⟶ fil.associatedGraded s k :=
  cokernel.π (Subobject.ofLE (fil.F (s + 1) k) (fil.F s k) (fil.mono s k))

/-! ### Convergence

A spectral sequence `E` converges to a graded object `A` with filtration `F`
if the E∞-page is isomorphic to the associated graded `gr(A, F)`, up to
a linear reindexing of the grading.

This is *weak convergence* — the project does not consider strong convergence. -/

/-- A spectral sequence `E` converges to a graded object `A` equipped with
    filtration `F`. The `reindex` map specifies how the spectral sequence
    index `ω` maps to `(filtration degree, stem degree)`.
    The E∞-page is `(E.ssData k).eInfty = Z⊤/B⊤` from the SSData. -/
structure Convergence {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    (E : SpectralSequence C ω) {ω' : Type w} (A : ω' → C) (F : Filtration A) where
  /-- Reindexing: spectral sequence index → (filtration degree, stem degree). -/
  reindex : ω → ℤ × ω'
  /-- Convergence isomorphism: `E∞^k ≅ gr^s A^{k'}` where `(s, k') = reindex k`. -/
  iso : ∀ (k : ω),
    (E.ssData k).eInfty ≅ F.associatedGraded (reindex k).1 (reindex k).2

/-! ### Stem and filtration degrees -/

/-- The filtration degree component of the convergence reindexing. -/
def Convergence.filtrationDegree {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ℤ :=
  (conv.reindex k).1

/-- The stem degree component of the convergence reindexing. -/
def Convergence.stemDegree {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ω' :=
  (conv.reindex k).2

/-! ### Induced maps on associated graded

A family of morphisms `aMap : A₁ k' ⟶ A₂ k'` that preserves filtrations
induces a map `gr^s(A₁) ⟶ gr^s(A₂)` on the associated graded pieces. -/

/-- The map induced on associated graded pieces by a filtration-compatible map.
    Given filtrations `F₁` on `A₁` and `F₂` on `A₂`, a family of morphisms
    `aMap : A₁ k' ⟶ A₂ k'` preserving the filtrations induces a map
    `gr^s(A₁, k') ⟶ gr^s(A₂, k')` on the associated graded via the
    universal property of cokernels. -/
noncomputable def Filtration.inducedAssocGradedMap {ω' : Type w} {A₁ A₂ : ω' → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (aMap : ∀ k', A₁ k' ⟶ A₂ k')
    (hcompat : ∀ (s : ℤ) (k' : ω'),
      ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
             Subobject.underlying.obj (F₂.F s k')),
        φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k')
    (s : ℤ) (k' : ω') : F₁.associatedGraded s k' ⟶ F₂.associatedGraded s k' :=
  cokernel.map
    (Subobject.ofLE (F₁.F (s + 1) k') (F₁.F s k') (F₁.mono s k'))
    (Subobject.ofLE (F₂.F (s + 1) k') (F₂.F s k') (F₂.mono s k'))
    (hcompat (s + 1) k').choose
    (hcompat s k').choose
    (by
      apply (cancel_mono ((F₂.F s k').arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(hcompat s k').choose_spec, (hcompat (s + 1) k').choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

/-! ### Category of converging spectral sequences

A morphism of converging spectral sequences consists of a morphism on the
E∞-pages and a morphism on the target graded objects, preserving
filtrations and compatible with convergence isomorphisms. -/

/-- A morphism of converging spectral sequences
    `(E₁, A₁, F₁, conv₁) → (E₂, A₂, F₂, conv₂)`.
    The base data consists of a spectral sequence morphism `ssMap` (SSData maps)
    plus a target map `aMap`, with an explicit E∞-page map derived from `ssMap`. -/
structure ConvergenceMorphism {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : SpectralSequence C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂) where
  /-- The underlying spectral sequence morphism. -/
  ssMap : SpectralSequenceMorphism E₁ E₂
  /-- The map on E∞-pages, derived from ssMap. -/
  eMap : ∀ (k : ω), (E₁.ssData k).eInfty ⟶ (E₂.ssData k).eInfty
  /-- `eMap` equals the E∞-map induced by the spectral sequence morphism `ssMap`. -/
  eMap_eq : ∀ (k : ω), eMap k = ssMap.eInftyMap k
  /-- The map on target graded objects. -/
  aMap : ∀ (k' : ω'), A₁ k' ⟶ A₂ k'
  /-- The reindexings agree (so the morphism is well-defined). -/
  reindex_eq : conv₁.reindex = conv₂.reindex
  /-- `aMap` preserves filtrations: `aMap(F₁^s) ⊆ F₂^s`.
      Formalized as: for each `s, k'`, the restriction of `aMap` to `F₁^s`
      factors through `F₂^s`. -/
  filtration_compat : ∀ (s : ℤ) (k' : ω'),
    ∃ (φ : Subobject.underlying.obj (F₁.F s k') ⟶
           Subobject.underlying.obj (F₂.F s k')),
      φ ≫ (F₂.F s k').arrow = (F₁.F s k').arrow ≫ aMap k'
  /-- Compatibility of `eMap` and `aMap` with the convergence isomorphisms.
      For each `k`, the diagram
      ```
      (E₁.ssData k).eInfty --[eMap k]--> (E₂.ssData k).eInfty
          |                                     |
        iso₁(k)                               iso₂(k)
          v                                     v
      gr^s(A₁, k')      --[grMap]-->      gr^s(A₂, k')
      ```
      commutes, where `(s, k') = reindex k` and `grMap` is the map on
      associated graded pieces induced by `aMap` via `filtration_compat`.
      The `eqToHom` transports `conv₂.iso` from `conv₂.reindex`-indices
      to `conv₁.reindex`-indices using `reindex_eq`. -/
  iso_compat : ∀ (k : ω),
    eMap k ≫ (conv₂.iso k).hom ≫
      eqToHom (by rw [show conv₁.reindex = conv₂.reindex from reindex_eq]) =
    (conv₁.iso k).hom ≫
      Filtration.inducedAssocGradedMap aMap filtration_compat
        (conv₁.reindex k).1 (conv₁.reindex k).2

/-! ### Detection

An element `y ∈ E∞^k` **detects** an element `x` of `A^{k'}` of filtration ≥ s,
meaning: `x` lies in `F^s A^{k'}`, and its image in `gr^s A^{k'} = F^s/F^{s+1}`
corresponds to `y` under the convergence isomorphism.

Elements are modeled as generalized elements (morphisms from a test object `T`). -/

/-- `Detects conv y x` means that the generalized element `y : T ⟶ E∞^k`
    detects the generalized element `x : T ⟶ F^s A^{k'}`, where
    `(s, k') = conv.reindex k`. Concretely:
    `y ≫ iso(k) = x ≫ π` where `π : F^s → gr^s = F^s/F^{s+1}`. -/
def Detects {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ (E.ssData k).eInfty)
    (x : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2))
    : Prop :=
  y ≫ (conv.iso k).hom =
    x ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2

/-! ### Detection propositions -/

/-- **detect_zero** (Blueprint §1.2): An element `x` of filtration ≥ s is detected
    by `0 ∈ E∞` if and only if `x` actually has filtration ≥ s+1.

    That is, `x ∈ F^s A^k` maps to zero in `gr^s = F^s/F^{s+1}` iff `x`
    lifts to `F^{s+1}`. -/
theorem detect_zero {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (x : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2))
    : Detects conv (0 : T ⟶ (E.ssData k).eInfty) x ↔
      ∃ (x' : T ⟶ Subobject.underlying.obj
            (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)),
        x' ≫ Subobject.ofLE
          (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
          (F.F (conv.reindex k).1 (conv.reindex k).2)
          (F.mono (conv.reindex k).1 (conv.reindex k).2) = x := by
  simp only [Detects, Filtration.toAssociatedGraded, Filtration.associatedGraded, Limits.zero_comp]
  constructor
  · intro h
    exact ⟨Abelian.monoLift _ x (by rw [h]), Abelian.monoLift_comp _ x (by rw [h])⟩
  · rintro ⟨x', hx'⟩
    rw [← hx', Category.assoc, cokernel.condition, Limits.comp_zero]

/-- **detect_difference** (Blueprint §1.2): Two elements `x, x'` of filtration ≥ s
    are detected by the same `y ∈ E∞` if and only if their difference `x - x'`
    has filtration ≥ s+1.

    That is, `x` and `x'` project to the same element in `gr^s` iff `x - x'`
    lifts to `F^{s+1}`. -/
theorem detect_difference {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ (E.ssData k).eInfty)
    (x x' : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2))
    : (Detects conv y x ∧ Detects conv y x') ↔
      (Detects conv y x ∧
        ∃ (z : T ⟶ Subobject.underlying.obj
              (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)),
          z ≫ Subobject.ofLE
            (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
            (F.F (conv.reindex k).1 (conv.reindex k).2)
            (F.mono (conv.reindex k).1 (conv.reindex k).2) = x - x') := by
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have key : (x - x') ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2 = 0 := by
      rw [Detects] at hx hx'
      rw [Preadditive.sub_comp, sub_eq_zero]
      exact hx.symm.trans hx'
    simp only [Filtration.toAssociatedGraded] at key
    exact ⟨Abelian.monoLift _ (x - x') key, Abelian.monoLift_comp _ (x - x') key⟩
  · rintro ⟨hx, z, hz⟩
    refine ⟨hx, ?_⟩
    change y ≫ (conv.iso k).hom = x' ≫ F.toAssociatedGraded (conv.reindex k).1 (conv.reindex k).2
    have hd : Detects conv y x := hx
    rw [Detects] at hd
    have hx'eq : x' = x - z ≫ Subobject.ofLE
        (F.F ((conv.reindex k).1 + 1) (conv.reindex k).2)
        (F.F (conv.reindex k).1 (conv.reindex k).2)
        (F.mono (conv.reindex k).1 (conv.reindex k).2) := by
      rw [hz, sub_sub_cancel]
    rw [hx'eq, Preadditive.sub_comp, hd]
    simp only [Category.assoc, Filtration.toAssociatedGraded, cokernel.condition, Limits.comp_zero,
      sub_zero]

/-! ### One-sided filtration conditions

Bounded below and bounded above are the one-sided analogues of `IsBounded`.
A bounded filtration is both bounded below and bounded above. -/

/-- A filtration is **bounded below** if for each `k`, the filtration eventually
    covers everything from below: `∃ s₀, ∀ s ≤ s₀, F^s A^k = ⊤`. -/
structure Filtration.IsBoundedBelow {ω : Type w} {A : ω → C}
    (fil : Filtration A) where
  lo : ω → ℤ
  boundedBelow : ∀ (k : ω) (s : ℤ), s ≤ lo k → fil.F s k = ⊤

/-- A filtration is **bounded above** if for each `k`, the filtration eventually
    becomes trivial from above: `∃ s₀, ∀ s ≥ s₀, F^s A^k = ⊥`. -/
structure Filtration.IsBoundedAbove {ω : Type w} {A : ω → C}
    (fil : Filtration A) where
  hi : ω → ℤ
  boundedAbove : ∀ (k : ω) (s : ℤ), hi k ≤ s → fil.F s k = ⊥

/-- A bounded filtration is bounded below. -/
def Filtration.IsBounded.toIsBoundedBelow {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBounded) : fil.IsBoundedBelow where
  lo := hb.lo
  boundedBelow := hb.boundedBelow

/-- A bounded filtration is bounded above. -/
def Filtration.IsBounded.toIsBoundedAbove {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBounded) : fil.IsBoundedAbove where
  hi := hb.hi
  boundedAbove := hb.boundedAbove

/-! ### True exhaustive and Hausdorff conditions

These are the standard mathematical definitions, weaker than bounded below/above. -/

/-- A filtration is **exhaustive** if for each `k`, every element eventually lies
    in some filtration level: `∀ k, ∃ s, F^s A^k = ⊤`.
    This is weaker than `IsBoundedBelow` (which gives a uniform bound). -/
def Filtration.IsExhaustive {ω : Type w} {A : ω → C}
    (fil : Filtration A) : Prop :=
  ∀ (k : ω), ∃ (s : ℤ), fil.F s k = ⊤

/-- A filtration is **Hausdorff** (separated) if for each `k`, the filtration
    eventually becomes trivial: `∀ k, ∃ s, F^s A^k = ⊥`.
    This is weaker than `IsBoundedAbove` (which gives a uniform bound). -/
def Filtration.IsHausdorff {ω : Type w} {A : ω → C}
    (fil : Filtration A) : Prop :=
  ∀ (k : ω), ∃ (s : ℤ), fil.F s k = ⊥

/-- A filtration bounded below is exhaustive. -/
theorem Filtration.IsBoundedBelow.toIsExhaustive {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBoundedBelow) : fil.IsExhaustive := by
  sorry

/-- A filtration bounded above is Hausdorff. -/
theorem Filtration.IsBoundedAbove.toIsHausdorff {ω : Type w} {A : ω → C}
    {fil : Filtration A} (hb : fil.IsBoundedAbove) : fil.IsHausdorff := by
  sorry

/-! ### Filtered morphisms

A morphism between filtered graded objects that preserves filtration. -/

/-- A filtered morphism between graded objects `A₁` and `A₂` with filtrations
    `F₁` and `F₂` consists of a degreewise map that preserves filtrations:
    the restriction of `map k` to `F₁^s A₁^k` factors through `F₂^s A₂^k`. -/
structure FilteredMorphism {ω : Type w} {A₁ A₂ : ω → C}
    (F₁ : Filtration A₁) (F₂ : Filtration A₂) where
  map : ∀ (k : ω), A₁ k ⟶ A₂ k
  compat : ∀ (s : ℤ) (k : ω),
    ∃ (φ : Subobject.underlying.obj (F₁.F s k) ⟶
           Subobject.underlying.obj (F₂.F s k)),
      φ ≫ (F₂.F s k).arrow = (F₁.F s k).arrow ≫ map k

/-- A filtered morphism induces a map on associated graded pieces. -/
noncomputable def FilteredMorphism.inducedGrMap {ω : Type w} {A₁ A₂ : ω → C}
    {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (f : FilteredMorphism F₁ F₂) (s : ℤ) (k : ω) :
    F₁.associatedGraded s k ⟶ F₂.associatedGraded s k :=
  Filtration.inducedAssocGradedMap f.map f.compat s k

/-! ### Essential differentials

A differential `d_r` is essential at index `k` when it is nonzero.
The primary definition lives in `KIP.SpectralSequence.Crossing` as
`IsEssentialAt`. We do not duplicate it here. -/

end KIP.SpectralSequence
