/-
  KIP.Synthetic.Basic
  §3.1 HF₂-synthetic spectra — Syn as a pretriangulated category, hSyn as
  homotopy category, bigrading Σ^{m,n}, natural transformation λ: Σ^{0,-1} → Id,
  X/λⁿ as cofiber, Z[λ]-module enrichment

  ROUND 3 CHANGES (cokernel → cofiber):
  - SyntheticCategory now requires Pretriangulated Syn (with HasShift ℤ, etc.)
  - Removed HasFiniteColimits (triangulated ≠ abelian; cokernels don't exist)
  - Added biShift_compat: Σ^{n,0} ≅ shiftFunctor Syn n
  - XModLambda defined via distinguished_cocone_triangle (cofiber), not cokernel
  - xModLambda_cofiberSeq is now a theorem, not an axiom
  - Added XModLambda.incl, .proj, .triangle_distinguished helpers

  DOWNSTREAM IMPACT: Files importing this module need to add instance parameters:
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn]
  Affected: Syn/Nu.lean, Syn/Sphere.lean, Syn/Adams.lean, Syn/Rigidity.lean, Syn/Lift.lean
-/
import Mathlib
import KIP.StableHomotopy.TensorTriangulatedCategory

namespace KIP.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open KIP.StableHomotopy

universe u v

/-! ### Synthetic spectra category

We axiomatize the category of HF₂-synthetic spectra. The key features are:
- It has a bigraded suspension `biShift (m, n)` (functors Σ^{m,n})
- Σ^{1,0} is identified with the ℤ-shift functor (for the triangulated structure)
- There is a natural transformation λ : Σ^{0,-1} → Id
- Cofibers of λ and its powers give the "mod λ" quotients
- The category is pretriangulated (cofiber sequences from distinguished triangles) -/

/-- The category of synthetic spectra, axiomatized as a pretriangulated category
    with bigraded suspension and the λ natural transformation.

    Synthetic spectra form a triangulated category, NOT an abelian category.
    X/λ is defined as a cofiber via `distinguished_cocone_triangle`, not as a cokernel.

    Instance parameters: `Pretriangulated Syn` provides distinguished triangles.
    `biShift_compat` identifies the first-coordinate shift Σ^{n,0} with the
    triangulated ℤ-shift `shiftFunctor Syn n`. -/
class SyntheticCategory (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] where
  /-- Bigraded suspension functors Σ^{m,n} -/
  biShift : ℤ × ℤ → Syn ⥤ Syn
  /-- Composition of biShift is additive: Σ^{a} ∘ Σ^{b} ≅ Σ^{a+b} -/
  biShift_comp : ∀ (a b : ℤ × ℤ), biShift a ⋙ biShift b ≅ biShift (a + b)
  /-- Σ^{0,0} is the identity functor -/
  biShift_zero : biShift (0, 0) ≅ 𝟭 Syn
  /-- Compatibility: Σ^{n,0} ≅ shiftFunctor Syn n (the triangulated ℤ-shift) -/
  biShift_compat : ∀ n : ℤ, biShift (n, 0) ≅ shiftFunctor Syn n
  /-- λ : Σ^{0,-1} → Id  — the key deformation parameter -/
  lam : biShift (0, -1) ⟶ 𝟭 Syn
  /-- BHS §3: biShift commutes with tensor: Σ^p(X ⊗ Y) ≅ Σ^p(X) ⊗ Y -/
  biShift_tensor_comm : ∀ (p : ℤ × ℤ) (X Y : Syn),
    (biShift p).obj (MonoidalCategory.tensorObj X Y) ≅
      MonoidalCategory.tensorObj ((biShift p).obj X) Y

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
  [HasZeroObject Syn] [HasShift Syn ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
  [MonoidalCategory Syn]
  [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### Cofiber of λ

In a triangulated category, cofibers are obtained from distinguished triangles.
For any morphism f : X → Y, there exists a distinguished triangle X →[f] Y → Z → X⟦1⟧.
The object Z is the cofiber (mapping cone) of f.

We apply this to λ_X : Σ^{0,-1}X → X to get X/λ as the cofiber.
The resulting distinguished triangle is:
  Σ^{0,-1}X →[λ_X] X →[incl] X/λ →[proj] (Σ^{0,-1}X)⟦1⟧ -/

/-- BHS §3: Synthetic spectra have functorial cofiber compatible with tensor. -/
axiom syn_functorial_cofiber :
  TensorTriangulatedCatWithFunctorialCofiber Syn

/-- The cofiber of the λ map on an object X.
    This is X/λ = cofiber(λ_X : Σ^{0,-1}X → X).
    Obtained from the distinguished triangle Σ^{0,-1}X →[λ_X] X → X/λ → (Σ^{0,-1}X)⟦1⟧. -/
noncomputable def XModLambda (X : Syn) : Syn :=
  syn_functorial_cofiber.cofib (SyntheticCategory.lam.app X)

/-- The inclusion map X → X/λ from the cofiber distinguished triangle. -/
noncomputable def XModLambda.incl (X : Syn) : X ⟶ XModLambda X :=
  syn_functorial_cofiber.cofibι (SyntheticCategory.lam.app X)

/-- The projection X/λ → (Σ^{0,-1}X)⟦1⟧ from the cofiber distinguished triangle. -/
noncomputable def XModLambda.proj (X : Syn) :
    XModLambda X ⟶ ((SyntheticCategory.biShift (0, -1)).obj X)⟦(1 : ℤ)⟧ :=
  syn_functorial_cofiber.cofibδ (SyntheticCategory.lam.app X)

/-- The cofiber triangle for λ_X is distinguished. -/
theorem XModLambda.triangle_distinguished (X : Syn) :
    Triangle.mk (SyntheticCategory.lam.app X)
      (XModLambda.incl X) (XModLambda.proj X) ∈ distTriang Syn :=
  syn_functorial_cofiber.cofib_distinguished (SyntheticCategory.lam.app X)

/-- The composite λ_X ≫ incl = 0 in the cofiber triangle. -/
theorem XModLambda.lam_comp_incl (X : Syn) :
    SyntheticCategory.lam.app X ≫ XModLambda.incl X = 0 :=
  comp_distTriang_mor_zero₁₂ _ (XModLambda.triangle_distinguished X)

/-! ### λⁿ: iterated λ morphism

BHS §3, Definition 3.3: The n-th power of λ is the composite
  Σ^{0,-n}X → Σ^{0,-(n-1)}X → ⋯ → Σ^{0,-1}X → X
constructed by induction using `biShift_comp` and `lam`. -/

/-- The n-th power of λ: a morphism Σ^{0,-n}X → X defined by induction.
    - `lambdaPow 0 X` = `biShift_zero.hom.app X` (the identity via Σ^{0,0} ≅ Id)
    - `lambdaPow (n+1) X` = biShift_comp⁻¹ ≫ Σ^{0,-n}(λ_X) ≫ lambdaPow n X -/
noncomputable def lambdaPow : (n : ℕ) → (X : Syn) →
    (SyntheticCategory.biShift (0, -(n : ℤ))).obj X ⟶ X
  | 0, X => SyntheticCategory.biShift_zero.hom.app X
  | n + 1, X => by
    have step1 : (SyntheticCategory.biShift ((0 : ℤ), -1) ⋙
        SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ))).obj X ⟶ X :=
      (SyntheticCategory.biShift ((0 : ℤ), -(n : ℤ))).map (SyntheticCategory.lam.app X) ≫
        lambdaPow n X
    have step2 : (SyntheticCategory.biShift ((0, -1) + (0, -(n : ℤ)))).obj X ⟶ X :=
      (SyntheticCategory.biShift_comp (0, -1) (0, -(n : ℤ))).inv.app X ≫ step1
    have heq : ((0 : ℤ), (-1 : ℤ)) + ((0 : ℤ), -(n : ℤ)) = ((0 : ℤ), -(↑(n + 1) : ℤ)) := by
      simp
    exact heq ▸ step2

/-- The cofiber of λⁿ on X, giving X/λⁿ = cofib(lambdaPow n X).
    BHS §3, Definition 3.3. -/
noncomputable def XModLambdaN (X : Syn) (n : ℕ) : Syn :=
  syn_functorial_cofiber.cofib (lambdaPow n X)

/-- The cofiber triangle for λⁿ is distinguished. -/
theorem XModLambdaN.triangle_distinguished (X : Syn) (n : ℕ) :
    Triangle.mk (lambdaPow n X)
      (syn_functorial_cofiber.cofibι (lambdaPow n X))
      (syn_functorial_cofiber.cofibδ (lambdaPow n X)) ∈ distTriang Syn :=
  syn_functorial_cofiber.cofib_distinguished (lambdaPow n X)

/-! ### Z[λ]-module enrichment -/

/-- BHS §3, Proposition 3.2: Syn is enriched over ℤ[λ]-modules.
    Axiomatized: requires graded Hom-set construction or MonoidalClosed infrastructure
    not currently available.
    Blueprint: `synthetic.tex`, §3 (zlambda-enrichment). -/
axiom zlambda_enrichment (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn]
    [SyntheticCategory Syn] : EnrichedCategory (ModuleCat (Polynomial ℤ)) Syn

end KIP.Synthetic
