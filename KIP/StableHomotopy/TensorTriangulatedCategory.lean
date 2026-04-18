/-
  KIP.StableHomotopy.TensorTriangulatedCategory
  Closed symmetric tensor triangulated category structure.

  Blueprint: prerequisites.tex, Definition prereq:def:closed-symmetric-tensor-triangulated
  Reference: Hovey–Palmieri–Strickland, Definition A.2.1
-/
import Mathlib

namespace KIP.StableHomotopy

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory Pretriangulated

universe u v

/-! ## Functorial Cofiber

General classes for a pretriangulated category with a canonical cofiber construction.
These are parameterized by an arbitrary category C (no SH dependency). -/

section FunctorialCofiber

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Limits.HasZeroObject C]
  [Pretriangulated C]

/-- A pretriangulated category has **functorial cofiber** when there is a canonical
    choice of cofiber for every morphism, together with canonical structure maps
    and functoriality from commutative squares.

    Blueprint: prerequisites.tex (functorial cofiber construction). -/
class HasFunctorialCofiber where
  /-- Canonical cofiber object for a morphism f : X ⟶ Y. -/
  cofib : {X Y : C} → (X ⟶ Y) → C
  /-- Canonical inclusion Y ⟶ cofib f. -/
  cofibι : {X Y : C} → (f : X ⟶ Y) → Y ⟶ cofib f
  /-- Canonical connecting map cofib f ⟶ X⟦1⟧. -/
  cofibδ : {X Y : C} → (f : X ⟶ Y) → cofib f ⟶ (shiftFunctor C (1 : ℤ)).obj X
  /-- The cofiber triangle X →[f] Y →[ι] cofib f →[δ] X⟦1⟧ is distinguished. -/
  cofib_distinguished : ∀ {X Y : C} (f : X ⟶ Y),
    Triangle.mk f (cofibι f) (cofibδ f) ∈ distTriang C
  /-- Functoriality: a commutative square α ≫ f₂ = f₁ ≫ β induces a map
      (cofib f₁ ⟶ cofib f₂) on cofibers. -/
  cofibMap : ∀ {X₁ Y₁ X₂ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (α : X₁ ⟶ X₂) (β : Y₁ ⟶ Y₂), α ≫ f₂ = f₁ ≫ β →
    (cofib f₁ ⟶ cofib f₂)

end FunctorialCofiber

section TensorFunctorialCofiber

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Limits.HasZeroObject C]
  [MonoidalCategory C] [Pretriangulated C]

/-- A tensor triangulated category with functorial cofiber extends `HasFunctorialCofiber`
    with the compatibility isomorphism: cofib(f ▷ W) ≅ cofib(f) ⊗ W.

    Blueprint: prerequisites.tex (tensor–cofiber compatibility). -/
class TensorTriangulatedCatWithFunctorialCofiber extends HasFunctorialCofiber C where
  /-- Tensor with W commutes with functorial cofiber:
      cofib(f ▷ W) ≅ cofib(f) ⊗ W. -/
  tensorCofibIso : ∀ {X Y : C} (f : X ⟶ Y) (W : C),
    cofib (f ▷ W) ≅ cofib f ⊗ W

end TensorFunctorialCofiber

/-! ## Closed Symmetric Tensor Triangulated Category -/

/-- A closed symmetric tensor triangulated category
    (prereq:def:closed-symmetric-tensor-triangulated).
    A triangulated category with a closed symmetric monoidal structure
    compatible with the triangulation, following HPS Def A.2.1. -/
class ClosedSymmetricTensorTriangulated (C : Type u)
    [Category.{v} C] [Preadditive C] [HasShift C ℤ]
    [∀ (n : ℤ), (shiftFunctor C n).Additive] [Limits.HasZeroObject C]
    [MonoidalCategory C] [Pretriangulated C] where
  /-- The monoidal structure is symmetric. -/
  symmetricCategory : SymmetricCategory C
  /-- The symmetric monoidal structure is closed (internal hom exists). -/
  monoidalClosed : MonoidalClosed C
  /-- (1) Smash preserves suspensions: `Σ X ∧ Y ≃ Σ(X ∧ Y)`, compatible with
      unit and associativity isomorphisms. -/
  smashSuspIso : ∀ (X Y : C),
    (shiftFunctor C (1 : ℤ)).obj X ⊗ Y ≅ (shiftFunctor C (1 : ℤ)).obj (X ⊗ Y)
  /-- (2) Smash is exact: if `X → Y → Z → Σ X` is distinguished,
      then `X ∧ W → Y ∧ W → Z ∧ W → Σ(X ∧ W)` is distinguished. -/
  smashExact : ∀ (W : C) [_inst : (tensorRight W).CommShift ℤ]
    (T : Triangle C), T ∈ distTriang C →
    (tensorRight W).mapTriangle.obj T ∈ distTriang C
  /-- (3) The internal hom `F(W, -)` is exact in the second variable. -/
  ihomExact : ∀ (W : C),
    letI : MonoidalClosed C := monoidalClosed
    [_inst : (ihom W).CommShift ℤ] →
    (T : Triangle C) → T ∈ distTriang C →
    (ihom W).mapTriangle.obj T ∈ distTriang C

attribute [instance] ClosedSymmetricTensorTriangulated.symmetricCategory
attribute [instance] ClosedSymmetricTensorTriangulated.monoidalClosed

end KIP.StableHomotopy
