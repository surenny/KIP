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
  exhaustive : ∀ (k : ω) (s : ℤ), s ≤ lo k → fil.F s k = ⊤
  /-- `F^s = 0` for `s ≥ hi`. -/
  hausdorff : ∀ (k : ω) (s : ℤ), hi k ≤ s → fil.F s k = ⊥

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

/-- A spectral sequence `E` (via its `EInftyData`) converges to a graded object
    `A` equipped with filtration `F`. The `reindex` map specifies how the
    spectral sequence index `ω` maps to `(filtration degree, stem degree)`. -/
structure Convergence {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    (E : EInftyData C ω) {ω' : Type w} (A : ω' → C) (F : Filtration A) where
  /-- Reindexing: spectral sequence index → (filtration degree, stem degree). -/
  reindex : ω → ℤ × ω'
  /-- Convergence isomorphism: `E∞^k ≅ gr^s A^{k'}` where `(s, k') = reindex k`. -/
  iso : ∀ (k : ω),
    E.EInfty k ≅ F.associatedGraded (reindex k).1 (reindex k).2

/-! ### Stem and filtration degrees -/

/-- The filtration degree component of the convergence reindexing. -/
def Convergence.filtrationDegree {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : EInftyData C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ℤ :=
  (conv.reindex k).1

/-- The stem degree component of the convergence reindexing. -/
def Convergence.stemDegree {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : EInftyData C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F) (k : ω) : ω' :=
  (conv.reindex k).2

/-! ### Category of converging spectral sequences

A morphism of converging spectral sequences consists of a morphism on the
E∞-pages and a morphism on the target graded objects, preserving
filtrations and compatible with convergence isomorphisms. -/

/-- A morphism of converging spectral sequences
    `(E₁, A₁, F₁, conv₁) → (E₂, A₂, F₂, conv₂)`. -/
structure ConvergenceMorphism {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E₁ E₂ : EInftyData C ω} {ω' : Type w}
    {A₁ A₂ : ω' → C} {F₁ : Filtration A₁} {F₂ : Filtration A₂}
    (conv₁ : Convergence E₁ A₁ F₁) (conv₂ : Convergence E₂ A₂ F₂) where
  /-- The map on E∞-pages. -/
  eMap : ∀ (k : ω), E₁.EInfty k ⟶ E₂.EInfty k
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
      The diagram E∞^k → gr^s(A₁) → gr^s(A₂) commutes with
      E∞^k → E∞^k → gr^s(A₂). -/
  iso_compat : ∀ (_k : ω), True -- full statement deferred to prover stage
    -- The precise formulation requires transporting across reindex_eq

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
    {E : EInftyData C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ E.EInfty k)
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
    {E : EInftyData C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (x : T ⟶ Subobject.underlying.obj (F.F (conv.reindex k).1 (conv.reindex k).2))
    : Detects conv (0 : T ⟶ E.EInfty k) x ↔
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
    {E : EInftyData C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (conv : Convergence E A F)
    {T : C} {k : ω}
    (y : T ⟶ E.EInfty k)
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

end KIP.SpectralSequence
