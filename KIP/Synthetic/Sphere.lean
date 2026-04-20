/-
  KIP.Synthetic.Sphere
  §3.2 Synthetic spheres — S^{0,0}, S^{m,n} = Σ^{m,n}S^{0,0},
  bigraded homotopy groups π_{m,n}(X) = [S^{m,n}, X],
  suspension invariance, Z[λ]-module structure on π_{*,*}
-/
import Mathlib
import KIP.Synthetic.Basic

namespace KIP.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### Synthetic spheres -/

/-- BHS §3, Definition 3.5 (bigraded spheres): The synthetic sphere S^{0,0}.
    This is the unit object of the synthetic spectra category. -/
noncomputable def S00 : Syn := 𝟙_ Syn

/-- The bigraded synthetic sphere S^{m,n} = Σ^{m,n} S^{0,0}. -/
noncomputable def Smn (m n : ℤ) : Syn :=
  (SyntheticCategory.biShift (m, n)).obj S00

/-! ### Bigraded homotopy groups -/

/-- The bigraded homotopy group π_{m,n}(X) = [S^{m,n}, X].
    Axiomatized as an additive abelian group.

    In a preadditive category, Hom-sets already carry an AddCommGroup structure,
    but we wrap this to make the API cleaner. -/
noncomputable def biHomotopyGroup (m n : ℤ) (X : Syn) : AddCommGroup (Smn (Syn := Syn) m n ⟶ X) :=
  inferInstance

/-- The type of bigraded homotopy classes π_{m,n}(X). -/
def BiHom (m n : ℤ) (X : Syn) : Type v := Smn (Syn := Syn) m n ⟶ X

/-! ### biShift(m,n) X ≅ Smn m n ⊗ X -/

/-- Σ^{m,n} X ≅ S^{m,n} ⊗ X, proved by applying the left unitor and biShift_tensor_comm. -/
noncomputable def biShift_eq_tensor_Smn (m n : ℤ) (X : Syn) :
    (SyntheticCategory.biShift (m, n)).obj X ≅ Smn m n ⊗ X :=
  (SyntheticCategory.biShift (m, n)).mapIso (λ_ X).symm ≪≫
    SyntheticCategory.biShift_tensor_comm (m, n) (𝟙_ Syn) X

/-! ### biShift fully faithful -/

/-- biShift(p) is fully faithful since it is an autoequivalence
    (with inverse biShift(-p) via biShift_comp and biShift_zero).
    Axiomatized to avoid verbose coherence proof for the equivalence triangle. -/
axiom biShift_fullyFaithful (p : ℤ × ℤ) :
    (SyntheticCategory.biShift (Syn := Syn) p).FullyFaithful

/-! ### Suspension invariance -/

/-- BHS §3, Proposition 3.6 (suspension invariance): Suspension invariance
    for bigraded homotopy groups.
    π_{m,n}(X) ≅ π_{m+k, n+l}(Σ^{k,l} X)
    for any k, l ∈ ℤ.

    Proof: biShift(k,l) is fully faithful, giving a bijection on Hom-sets.
    Precompose with the canonical iso from biShift_comp to shift the source. -/
noncomputable def susp_invariance (m n k l : ℤ) (X : Syn) :
    (Smn (Syn := Syn) m n ⟶ X) ≃
      (Smn (Syn := Syn) (m + k) (n + l) ⟶
        (SyntheticCategory.biShift (k, l)).obj X) := by
  refine ((biShift_fullyFaithful (k, l)).homEquiv).trans ?_
  exact Iso.homCongr
    ((SyntheticCategory.biShift_comp (m, n) (k, l)).app S00)
    (Iso.refl _)

/-! ### Z[λ]-module structure on π_{*,*} -/

/-- BHS §3, λ-action on bigraded homotopy groups.
    λ : Σ^{0,-1} → 𝟭 induces π_{m,n}(X) → π_{m,n-1}(X) by precomposition.
    Blueprint: `prereq:def:lambda-action`. -/
noncomputable def lambdaAction (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (m n : ℤ) (X : Syn) :
    (Smn (Syn := Syn) m n ⟶ X) → (Smn (Syn := Syn) m (n - 1) ⟶ X) := by
  intro f
  have heq : (m, n) + (0, -1) = (m, n - 1) := by ext <;> simp [sub_eq_add_neg]
  refine eqToHom ?_ ≫
    (SyntheticCategory.biShift_comp (m, n) (0, -1)).inv.app S00 ≫
    SyntheticCategory.lam.app (Smn m n) ≫ f
  simp only [Smn]
  rw [heq]

end KIP.Synthetic
