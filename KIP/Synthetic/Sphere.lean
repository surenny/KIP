/-
  KIP.Synthetic.Sphere
  §3.2 Synthetic spheres — S^{0,0}, S^{m,n} = Σ^{m,n}S^{0,0},
  bigraded homotopy groups π_{m,n}(X) = [S^{m,n}, X],
  suspension invariance, Z[λ]-module structure on π_{*,*}
-/
import Mathlib
import KIP.Synthetic.Basic

namespace KIP.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### Synthetic spheres -/

/-- BHS §3, Definition 3.5 (bigraded spheres): The synthetic sphere S^{0,0}.
    This is the unit object of the synthetic spectra category. -/
axiom S00 (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] : Syn

/-- The bigraded synthetic sphere S^{m,n} = Σ^{m,n} S^{0,0}. -/
noncomputable def Smn (m n : ℤ) : Syn :=
  (SyntheticCategory.biShift (m, n)).obj (S00 Syn)

/-! ### Bigraded homotopy groups -/

/-- The bigraded homotopy group π_{m,n}(X) = [S^{m,n}, X].
    Axiomatized as an additive abelian group.

    In a preadditive category, Hom-sets already carry an AddCommGroup structure,
    but we wrap this to make the API cleaner. -/
noncomputable def biHomotopyGroup (m n : ℤ) (X : Syn) : AddCommGroup (Smn (Syn := Syn) m n ⟶ X) :=
  inferInstance

/-- The type of bigraded homotopy classes π_{m,n}(X). -/
def BiHom (m n : ℤ) (X : Syn) : Type v := Smn (Syn := Syn) m n ⟶ X

/-! ### Suspension invariance -/

/-- BHS §3, Proposition 3.6 (suspension invariance): Suspension invariance
    for bigraded homotopy groups.
    π_{m,n}(X) ≅ π_{m+k, n+l}(Σ^{k,l} X)
    for any k, l ∈ ℤ. -/
axiom susp_invariance (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (m n k l : ℤ) (X : Syn) :
    (Smn (Syn := Syn) m n ⟶ X) ≃ (Smn (Syn := Syn) (m + k) (n + l) ⟶
      (SyntheticCategory.biShift (k, l)).obj X)

/-! ### Z[λ]-module structure on π_{*,*} -/

/-- BHS §3, Definition 3.7 (Z[λ]-module structure on π_{*,*}): The λ-action
    on bigraded homotopy groups.
    Given f : S^{m,n} → X, precompose with λ to get
    λ · f : S^{m,n-1} → S^{m,n} → X, i.e., a map π_{m,n} → π_{m,n-1}.
    Actually, since λ : Σ^{0,-1} → Id, the λ-action goes
    π_{m,n}(X) → π_{m,n+1}(X) via the natural transformation. -/
axiom lambdaAction (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (m n : ℤ) (X : Syn) :
    (Smn (Syn := Syn) m n ⟶ X) → (Smn (Syn := Syn) m (n + 1) ⟶ X)

end KIP.Synthetic
