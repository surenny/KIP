/-
  KIP.Synthetic.Nu
  §3.4 ν functor — ν: hS → hSyn, preservation of distinguished triangles
  (condition 3.1), ν(ΣX) ≅ Σ^{1,1}νX, comparison map Σ(νX) → ν(ΣX) is λ
-/
import Mathlib
import KIP.Synthetic.Basic
import KIP.StableHomotopy.Basic

namespace KIP.Synthetic

open CategoryTheory CategoryTheory.Limits

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
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- BHS §3.1, Definition 3.8 (the ν functor): The ν functor from the stable
    homotopy category to synthetic spectra.
    Axiomatized: ν preserves finite colimits and is lax symmetric monoidal. -/
axiom nu : 𝒮 ⥤ Syn

/-- BHS §3.1, Definition 3.8: ν preserves the zero object. -/
axiom nu_zero : (nu 𝒮 Syn).obj 0 ≅ (0 : Syn)

/-! ### Compatibility with suspension -/

/-- BHS §3.1, Remark after Definition 3.8: ν(ΣX) ≅ Σ^{1,1} ν(X). The ν
    functor intertwines the suspension in 𝒮 with the bigraded suspension
    Σ^{1,1} in Syn. -/
axiom nu_susp (X : 𝒮) :
  (nu 𝒮 Syn).obj ((shiftFunctor 𝒮 (1 : ℤ)).obj X) ≅
    (SyntheticCategory.biShift (1, 1)).obj ((nu 𝒮 Syn).obj X)

/-- Formalization bridge: ν commutes with the ℤ-shift (suspension):
    ν(X⟦n⟧) ≅ (νX)⟦n⟧. This is the CommShift structure that underlies
    `nu_susp` and is required for `nu_cofiber_iff` (preservation of
    distinguished triangles). Added in Polish R1 to enable
    `Functor.mapTriangle`. -/
axiom nu_commShift : (nu 𝒮 Syn).CommShift ℤ

attribute [local instance] nu_commShift

/-- BHS §3.1, Remark after Definition 3.8: The comparison map Σ(νX) → ν(ΣX)
    corresponds to the λ natural transformation. More precisely, the composite
    Σ^{1,0}(νX) → Σ^{1,1}(νX) ≅ ν(ΣX) is induced by λ. -/
/- TODO: Refine to a morphism equality once biShift composition
   infrastructure is extended. The precise statement requires:
   (1) a counit-like map 𝟭 → biShift(0,1) dual to λ : biShift(0,-1) → 𝟭,
       or equivalently, the section of the fiber sequence for λ, and
   (2) careful tracking of biShift_comp naturality squares.
   The CommShift structure (nu_commShift) captures the iso ν(X⟦n⟧) ≅ (νX)⟦n⟧
   but not its identification with the λ-action on the second bigrading. -/
axiom nu_comparison_is_lambda (X : 𝒮) : True

/-! ### Preservation of cofiber sequences -/

/-- BHS §3.1, Axiom 3.1 (ν preserves cofiber sequences): ν preserves
    distinguished triangles: if T is a distinguished triangle in 𝒮, then
    ν(T) is a distinguished triangle in Syn.
    This is the forward direction of Axiom 3.1 from [BHS]; the converse
    (that T is distinguished iff the induced HF₂-homology sequence is short
    exact) requires cohomological infrastructure not formalized here. -/
axiom nu_cofiber_iff (T : Pretriangulated.Triangle 𝒮)
    (hT : T ∈ distTriang 𝒮) :
    (nu 𝒮 Syn).mapTriangle.obj T ∈ distTriang Syn

/-- BHS §3.1, Definition 3.8: ν is compatible with the monoidal structure:
    ν(X ∧ Y) receives a natural map from ν(X) ⊗ ν(Y)
    (ν is lax symmetric monoidal). -/
/- TODO: Refine to `(nu 𝒮 Syn).LaxMonoidal` once Syn has a
   MonoidalCategory instance. Currently Syn is axiomatized as
   pretriangulated but not monoidal — the smash product on
   synthetic spectra is not formalized. -/
axiom nu_lax_monoidal : True

end KIP.Synthetic
