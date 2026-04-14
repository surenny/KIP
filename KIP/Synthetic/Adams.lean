/-
  KIP.Synthetic.Adams
  §3.3 Synthetic Adams spectral sequence — functor from Syn to 3-graded
  converging SS (grading rule per §3.6), Adams filtration on π_{*,*}X,
  convergence, Z[λ]-module spectral sequence

  Blueprint references:
  - `prerequisites.tex` §0.3.3 (Axiom `prereq:ax:syn-adams-ss`)
  - `synthetic-spectra.tex` §3 (synthetic Adams SS definition, Z[λ]-module structure)
  - `synthetic-extensions.tex` §4 (applications to extension spectral sequences)
  - BHS Appendix A, Corollary A.9, A.11 (convergence of synthetic Adams SS)
-/
import Mathlib
import KIP.Synthetic.Sphere
import KIP.SpectralSequence.Convergence

namespace KIP.Synthetic

open CategoryTheory CategoryTheory.Limits KIP.SpectralSequence

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### Synthetic Adams spectral sequence (3-graded)

The synthetic Adams SS is a trigraded spectral sequence with indices (s, t, w):
- s = Adams filtration degree
- t = stem + filtration degree
- w = weight (synthetic grading)
Differentials: d_r : E_r^{s,t,w} → E_r^{s+r, t+r-1, w}. -/

/-- BHS Appendix A (Axiom `prereq:ax:syn-adams-ss`), cf. `synthetic-spectra.tex` §3:
    The synthetic Adams spectral sequence for an object X in Syn.
    This is a spectral sequence with trigrading (s, t, w) ∈ ℤ³,
    converging to π_{*,*}(X) with Adams filtration. -/
axiom SynAdamsSS (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ)

/-- BHS Appendix A (Axiom `prereq:ax:syn-adams-ss`), cf. `synthetic-spectra.tex` §3:
    The differential degree for the synthetic Adams SS:
    d_r has degree (r, r-1, 0) in the trigrading (s, t, w).
    The weight component is zero, reflecting that differentials preserve weight. -/
axiom synAdamsSS_diffDeg (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) (r : ℤ) :
    (SynAdamsSS Syn X).diffDeg r = (r, r - 1, 0)

/-- BHS Appendix A (Axiom `prereq:ax:syn-adams-ss`), cf. `synthetic-spectra.tex` §3:
    The starting page for the synthetic Adams SS is r₀ = 2,
    matching the classical Adams spectral sequence. -/
axiom synAdamsSS_r0 (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) :
    (SynAdamsSS Syn X).r₀ = 2

/-! ### Adams filtration on π_{*,*} -/

/-- BHS §3 (`prereq:def:adams-filtration` in synthetic setting), cf. `synthetic-spectra.tex`:
    The Adams filtration on bigraded homotopy groups π_{m,n}(X).
    This is a decreasing filtration F^s π_{m,n}(X) ⊇ F^{s+1} π_{m,n}(X) ⊇ ⋯
    arising from the synthetic Adams SS. Elements in F^s detect classes
    on the E_∞-page with filtration ≥ s. -/
axiom synAdamsFiltration (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) (m n : ℤ) (s : ℤ) :
    AddSubgroup (Smn (Syn := Syn) m n ⟶ X)

/-- BHS §3 (`prereq:def:adams-filtration`): The filtration is decreasing: F^{s+1} ⊆ F^s.
    This is a standard property of Adams filtrations (cf. `prereq:rem:decreasing-filtration`). -/
axiom synAdamsFiltration_mono (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) (m n : ℤ) (s : ℤ) :
    synAdamsFiltration Syn X m n (s + 1) ≤ synAdamsFiltration Syn X m n s

/-! ### Convergence -/

/-- BHS Corollary A.9/A.11 (Axiom `prereq:ax:syn-adams-ss`),
    cf. `synthetic-spectra.tex` §3 (Propositions `prereq:prop:syn-einfty-nuX`,
    `prereq:prop:syn-einfty-mod-lambda`):
    Convergence of the synthetic Adams SS:
    SynAdamsSS(X) converges to π_{t-s, w}(X) with filtration
    synAdamsFiltration.

    That is, E_∞^{s,t,w}(X) ≅ F^s π_{t-s,w}(X) / F^{s+1} π_{t-s,w}(X).
    The convergence data consists of an `EInftyData` wrapping the SS, a graded
    target object `A : ℤ × ℤ → AddCommGrpCat`, a filtration `F` on `A`, and a
    `Convergence` structure with reindexing `(s, t, w) ↦ (s, (t-s, w))`. -/
axiom synAdamsConvergence (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) :
  ∃ (eData : EInftyData (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ))
    (_ : eData.ss = SynAdamsSS Syn X)
    (A : ℤ × ℤ → AddCommGrpCat.{0})
    (F : Filtration A)
    (conv : Convergence eData A F),
    conv.reindex = fun ⟨s, t, w⟩ => (s, (t - s, w))

/-! ### Functoriality -/

/-- BHS Appendix A (Axiom `prereq:ax:syn-adams-ss`, `prereq:def:ss-morphism`):
    The synthetic Adams SS is functorial in X:
    a map f : X → Y induces a morphism of spectral sequences,
    compatible with differentials and convergence data. -/
axiom synAdamsSS_functorial (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] {X Y : Syn} (f : X ⟶ Y) :
    SpectralSequenceMorphism (SynAdamsSS Syn X) (SynAdamsSS Syn Y)

/-! ### Z[λ]-module structure -/

/-- BHS §3 (`synthetic-spectra.tex` Remark after Axiom `prereq:ax:syn-adams-ss`):
    The synthetic Adams SS lives in the category of Z[λ]-modules.
    This means each page E_r^{*,*,*} carries a Z[λ]-module structure
    compatible with the differentials, where λ acts in tridegree (0,0,-1).
    Cf. `synthetic-extensions.tex` §4 for applications to extension SS. -/
axiom synAdamsSS_zlambda_module (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) :
  ∀ (r : ℤ) (k : ℤ × ℤ × ℤ),
    Module (Polynomial ℤ) ↑((SynAdamsSS Syn X).Page r k)
  -- Each page of the synthetic Adams SS carries a Z[λ]-module structure,
  -- where λ acts by Polynomial.X ∈ Polynomial ℤ.

end KIP.Synthetic
