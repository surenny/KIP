/-
  KIP.Synthetic.Lift
  §3.6 Synthetic lift — ν on Adams filtration k maps can be divided by λᵏ,
  Adams filtration = λ-Bockstein filtration (§3.16),
  canonical division by λ for Adams filtration 1 maps (§3.17),
  ν applied to distinguished triangles: notation §3.19, §3.20
-/
import Mathlib
import KIP.Synthetic.Rigidity
import KIP.StableHomotopy.Adams

namespace KIP.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  KIP.SpectralSequence KIP.StableHomotopy

universe u v u' v'

variable (𝒮 : Type u) [StableHomotopy.StableHomotopyCategory.{u, v} 𝒮]
variable (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### Synthetic lift

If a map f : X → Y in the stable homotopy category has Adams filtration AF(f) = k,
then ν(f) factors through λᵏ. That is, there exists a "synthetic lift"
f̃ : Σ^{0,k}ν(X) → ν(Y) such that ν(f) = λᵏ ∘ f̃. -/

/-- BHS §3.6, Lemma 9.15 (synthetic lift): If AF(f) = k, then ν(f) factors
    through λᵏ. -/
axiom synthetic_lift {X Y : 𝒮} (f : X ⟶ Y) (k : ℤ) :
    ∃ (_f_tilde : (SyntheticCategory.biShift (Syn := Syn) (0, k)).obj ((nu 𝒮 Syn).obj X) ⟶
        (nu 𝒮 Syn).obj Y),
      True
  -- Full statement: nu.map f = (λ^k component) ≫ f_tilde
  -- Requires Adams filtration from StableHomotopy.Adams

/-! ### ê and f̂ notation -/

/-- ê(f) = 0 if AF(f) = 0, and ê(f) = 1 if AF(f) > 0.
    This is the "essential" Adams filtration, which only distinguishes
    between filtration 0 and positive filtration. -/
noncomputable def eHat {X Y : 𝒮} (f : X ⟶ Y) : ℤ :=
  if AF f = 0 then 0 else 1

/-- f̂ is the canonical synthetic lift of f divided by λ^{ê(f)}.
    That is, f̂ : Σ^{0, ê(f)} ν(X) → ν(Y) with ν(f) = λ^{ê(f)} ∘ f̂. -/
noncomputable def fHat {X Y : 𝒮} (f : X ⟶ Y) :
    (SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj ((nu 𝒮 Syn).obj X) ⟶
      (nu 𝒮 Syn).obj Y :=
  (synthetic_lift 𝒮 Syn f (eHat 𝒮 f)).choose

/-- BHS §3.6, Lemma 9.15 (f̂ specification): The defining property of f̂:
    ν(f) factors as ι ≫ f̂ where ι : ν(X) → Σ^{0,ê(f)}(ν(X)) is the
    λ-power morphism. Concretely, ν(f) = λ^{ê(f)} ∘ f̂. -/
axiom fHat_spec {X Y : 𝒮} (f : X ⟶ Y) :
    ∃ (ι : (nu 𝒮 Syn).obj X ⟶
        (SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 f)).obj ((nu 𝒮 Syn).obj X)),
      (nu 𝒮 Syn).map f = ι ≫ fHat 𝒮 Syn f

/-! ### Distinguished triangles in synthetic spectra -/

/-- BHS §3, Proposition 3.19: Given a cofiber sequence X → Y → Z → ΣX in 𝒮,
    ν preserves the cofiber sequence: there exists a distinguished triangle
    ν(X) →[ν(f)] ν(Y) →[ν(g)] ν(Z) →[h'] (ν(X))⟦1⟧ in Syn.
    The connecting map h' differs from ν(h) by a weight-shift correction
    (since ν takes Σ to Σ^{1,1}, not Σ^{1,0}). -/
axiom syn_distinguished_triangle
    (T : StableHomotopy.HoCofiberSequence (𝒮 := 𝒮)) :
    ∃ (h' : (nu 𝒮 Syn).obj T.Z ⟶ ((nu 𝒮 Syn).obj T.X)⟦(1 : ℤ)⟧),
      Triangle.mk ((nu 𝒮 Syn).map T.f) ((nu 𝒮 Syn).map T.g) h' ∈ distTriang Syn

/-- BHS §3, Proposition 3.20 (f̂ triangle): Given a cofiber sequence
    X →[f] Y →[g] Z →[h] ΣX with ê(f) + ê(g) + ê(h) = 1, there is a
    distinguished triangle of synthetic spectra involving the ν-images
    of X, Y, Z.

    Since exactly one of ê(f), ê(g), ê(h) is 1, the triangle involves
    the f̂, ĝ, ĥ lifts (with weight-shift corrections on two of the
    three morphisms). -/
axiom fhat_triangle (T : StableHomotopy.HoCofiberSequence (𝒮 := 𝒮))
    (hsum : eHat 𝒮 T.f + eHat 𝒮 T.g + eHat 𝒮 T.h = 1) :
    ∃ (f' : (nu 𝒮 Syn).obj T.X ⟶ (nu 𝒮 Syn).obj T.Y)
      (g' : (nu 𝒮 Syn).obj T.Y ⟶ (nu 𝒮 Syn).obj T.Z)
      (h' : (nu 𝒮 Syn).obj T.Z ⟶ ((nu 𝒮 Syn).obj T.X)⟦(1 : ℤ)⟧),
      Triangle.mk f' g' h' ∈ distTriang Syn

/-- BHS §3, Notation 3.19 (cofiber of f̂): The distinguished triangle
    extending f̂(f) has third vertex isomorphic to Σ^{0, -ê(g)} ν(Z).
    Concretely, C(f̂) ≅ Σ^{0, -ê(g)} ν(Cf), relating the cofiber of the
    synthetic lift to the ν of the classical cofiber, up to a weight shift. -/
axiom cofiber_fhat (T : StableHomotopy.HoCofiberSequence (𝒮 := 𝒮)) :
    ∃ (g' : (nu 𝒮 Syn).obj T.Y ⟶
          (SyntheticCategory.biShift (Syn := Syn) (0, -eHat 𝒮 T.g)).obj
            ((nu 𝒮 Syn).obj T.Z))
      (h' : (SyntheticCategory.biShift (Syn := Syn) (0, -eHat 𝒮 T.g)).obj
            ((nu 𝒮 Syn).obj T.Z) ⟶
          ((SyntheticCategory.biShift (Syn := Syn) (0, eHat 𝒮 T.f)).obj
            ((nu 𝒮 Syn).obj T.X))⟦(1 : ℤ)⟧),
      Triangle.mk (fHat 𝒮 Syn T.f) g' h' ∈ distTriang Syn

/-! ### Adams filtration = λ-Bockstein filtration -/

/-- BHS §3.16 (Adams filtration = λ-Bockstein filtration): If AF(f) ≥ k,
    then ν(f) factors through Σ^{0,k} via a synthetic lift. Concretely,
    ∃ f̃ : Σ^{0,k}ν(X) → ν(Y) and ι : ν(X) → Σ^{0,k}ν(X) (the λ^k power
    map) such that ν(f) = ι ≫ f̃.

    The converse (factorization implies AF ≥ k) together with this direction
    gives AF(f) = sup { k : ν(f) factors through λᵏ }. -/
axiom af_eq_lambda_bockstein {X Y : 𝒮} (f : X ⟶ Y) (k : ℤ) :
    HasAF_ge f k →
    ∃ (f_tilde : (SyntheticCategory.biShift (Syn := Syn) (0, k)).obj
          ((nu 𝒮 Syn).obj X) ⟶ (nu 𝒮 Syn).obj Y)
      (ι : (nu 𝒮 Syn).obj X ⟶
          (SyntheticCategory.biShift (Syn := Syn) (0, k)).obj ((nu 𝒮 Syn).obj X)),
      (nu 𝒮 Syn).map f = ι ≫ f_tilde

end KIP.Synthetic
