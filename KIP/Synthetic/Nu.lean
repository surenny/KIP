/-
  KIP.Synthetic.Nu
  §3.4 ν functor — ν: hS → hSyn, preservation of distinguished triangles
  (condition 3.1), ν(ΣX) ≅ Σ^{1,1}νX
-/
import Mathlib
import KIP.Synthetic.Basic
import KIP.StableHomotopy.Basic
import KIP.StableHomotopy.Cohomology

namespace KIP.Synthetic

open CategoryTheory CategoryTheory.Limits KIP.StableHomotopy

attribute [local instance] HasZeroObject.zero'

universe u v u' v'

/-! ### The ν functor

The ν functor maps from the stable homotopy category 𝒮 to the synthetic
spectra category Syn. It is the key bridge between classical and synthetic
homotopy theory. -/

variable (𝒮 : Type u) [StableHomotopy.StableHomotopyCategory.{u, v} 𝒮]
variable (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- BHS §3.1, Definition 3.8 (the ν functor): The ν functor from the stable
    homotopy category to synthetic spectra.
    Axiomatized: ν preserves finite colimits and is lax symmetric monoidal. -/
axiom nu : 𝒮 ⥤ Syn

/-- BHS §3.1, Definition 3.8: ν is an additive functor. -/
axiom nu_additive : Functor.Additive (nu 𝒮 Syn)

/-- BHS §3.1, Definition 3.8: ν preserves the zero object. -/
axiom nu_zero : (nu 𝒮 Syn).obj 0 ≅ (0 : Syn)

/-! ### Compatibility with suspension -/

/-- BHS §3.1, Remark after Definition 3.8: ν(ΣX) ≅ Σ^{1,1} ν(X). The ν
    functor intertwines the suspension in 𝒮 with the bigraded suspension
    Σ^{1,1} in Syn. -/
axiom nu_susp (X : 𝒮) :
  (nu 𝒮 Syn).obj ((shiftFunctor 𝒮 (1 : ℤ)).obj X) ≅
    (SyntheticCategory.biShift (1, 1)).obj ((nu 𝒮 Syn).obj X)

/-- BHS §3.1: ν intertwines the ℤ-shift with diagonal biShift:
    ν(X⟦n⟧) ≅ Σ^{n,n}(νX). Proved by induction on n; the base case is `nu_susp`.
    Blueprint: `prereq:thm:nu-shift-bishift`. -/
noncomputable def nu_shift_biShift (n : ℤ) (X : 𝒮) :
  (nu 𝒮 Syn).obj ((shiftFunctor 𝒮 n).obj X) ≅
    (SyntheticCategory.biShift (n, n)).obj ((nu 𝒮 Syn).obj X) :=
  Int.inductionOn' n 0
    ((nu 𝒮 Syn).mapIso ((shiftFunctorZero 𝒮 ℤ).app X) ≪≫
      SyntheticCategory.biShift_zero.symm.app ((nu 𝒮 Syn).obj X))
    (fun k _hk ih => by
      have step1 := (nu 𝒮 Syn).mapIso ((shiftFunctorAdd 𝒮 k 1).app X)
      have step2 := nu_susp 𝒮 Syn ((shiftFunctor 𝒮 k).obj X)
      have step3 := (SyntheticCategory.biShift (1, 1)).mapIso ih
      have step4 : (SyntheticCategory.biShift (1, 1)).obj
          ((SyntheticCategory.biShift (k, k)).obj ((nu 𝒮 Syn).obj X)) ≅
          (SyntheticCategory.biShift (k + 1, k + 1)).obj ((nu 𝒮 Syn).obj X) :=
        (SyntheticCategory.biShift_comp (k, k) (1, 1)).app ((nu 𝒮 Syn).obj X) ≪≫
          eqToIso (by simp)
      exact step1 ≪≫ step2 ≪≫ step3 ≪≫ step4)
    (fun k _hk ih => by
      set Y := (shiftFunctor 𝒮 (k - 1)).obj X
      have chain1 := nu_susp 𝒮 Syn Y
      have chain2 : (nu 𝒮 Syn).obj ((shiftFunctor 𝒮 (1 : ℤ)).obj Y) ≅
          (nu 𝒮 Syn).obj ((shiftFunctor 𝒮 k).obj X) :=
        (nu 𝒮 Syn).mapIso ((shiftFunctorAdd 𝒮 (k - 1) 1).symm.app X ≪≫
          eqToIso (by simp))
      have combined : (SyntheticCategory.biShift (1, 1)).obj ((nu 𝒮 Syn).obj Y) ≅
          (SyntheticCategory.biShift (k, k)).obj ((nu 𝒮 Syn).obj X) :=
        chain1.symm ≪≫ chain2 ≪≫ ih
      have cancel := (SyntheticCategory.biShift (-1, -1)).mapIso combined
      have lhs_simp : (SyntheticCategory.biShift (-1, -1)).obj
          ((SyntheticCategory.biShift (1, 1)).obj ((nu 𝒮 Syn).obj Y)) ≅
          (nu 𝒮 Syn).obj Y :=
        (SyntheticCategory.biShift_comp (1, 1) (-1, -1)).app ((nu 𝒮 Syn).obj Y) ≪≫
          eqToIso (by simp) ≪≫ SyntheticCategory.biShift_zero.app ((nu 𝒮 Syn).obj Y)
      have rhs_simp : (SyntheticCategory.biShift (-1, -1)).obj
          ((SyntheticCategory.biShift (k, k)).obj ((nu 𝒮 Syn).obj X)) ≅
          (SyntheticCategory.biShift (k - 1, k - 1)).obj ((nu 𝒮 Syn).obj X) :=
        (SyntheticCategory.biShift_comp (k, k) (-1, -1)).app ((nu 𝒮 Syn).obj X) ≪≫
          eqToIso (by simp [sub_eq_add_neg])
      exact lhs_simp.symm ≪≫ cancel ≪≫ rhs_simp)

/-! ### Preservation of cofiber sequences -/

/-- BHS §3.1, Axiom 3.1 (correct form): ν sends cofiber sequences to
    distinguished triangles when the induced HF₂-homology sequence is
    short exact. This is the forward direction only.
    Blueprint: `prereq:ax:nu-cofiber-ses`. -/
axiom nu_cofiber_ses (T : Pretriangulated.Triangle 𝒮)
    (hT : T ∈ distTriang 𝒮)
    (_hses : ∀ n : ℤ,
      Function.Exact (Mod2Homology.pushforward T.mor₁ n)
                     (Mod2Homology.pushforward T.mor₂ n)) :
    ∃ (T' : Pretriangulated.Triangle Syn),
      T' ∈ distTriang Syn ∧
      T'.obj₁ = (nu 𝒮 Syn).obj T.obj₁ ∧
      T'.obj₂ = (nu 𝒮 Syn).obj T.obj₂ ∧
      T'.obj₃ = (nu 𝒮 Syn).obj T.obj₃

/-- BHS §0.2.3: Exactness of mod 2 cohomology implies exactness of mod 2
    homology. This follows from naturality of the universal coefficient
    theorem and the fact that Hom(−, F₂) reflects exactness for
    F₂-vector spaces. -/
axiom cohom_exact_implies_homol_exact {X Y Z : 𝒮} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℤ)
    (h : Function.Exact (Mod2Cohomology.pullback g n)
                        (Mod2Cohomology.pullback f n)) :
    Function.Exact (Mod2Homology.pushforward f n)
                   (Mod2Homology.pushforward g n)

omit [MonoidalCategory Syn] [SyntheticCategory Syn] in
/-- Cohomological variant of `nu_cofiber_ses`: if the induced mod 2 cohomology
    sequence is short exact, ν sends the cofiber sequence to a distinguished
    triangle. Follows from `nu_cofiber_ses` + universal coefficients.
    Blueprint: `prereq:rem:nu-cofiber-cohomological`. -/
theorem nu_cofiber_ses_cohomological (T : Pretriangulated.Triangle 𝒮)
    (hT : T ∈ distTriang 𝒮)
    (_hses_cohom : ∀ n : ℤ,
      Function.Exact (Mod2Cohomology.pullback T.mor₂ n)
                     (Mod2Cohomology.pullback T.mor₁ n)) :
    ∃ (T' : Pretriangulated.Triangle Syn),
      T' ∈ distTriang Syn ∧
      T'.obj₁ = (nu 𝒮 Syn).obj T.obj₁ ∧
      T'.obj₂ = (nu 𝒮 Syn).obj T.obj₂ ∧
      T'.obj₃ = (nu 𝒮 Syn).obj T.obj₃ :=
  nu_cofiber_ses 𝒮 Syn T hT fun n =>
    cohom_exact_implies_homol_exact (𝒮 := 𝒮) T.mor₁ T.mor₂ n (_hses_cohom n)

end KIP.Synthetic
