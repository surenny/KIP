import Mathlib
import KIP.SpectralSequence.Basic
import KIP.SpectralSequence.Convergence

/-!
# Spectral Sequence from a Filtered Chain Complex

BHS Blueprint §0.1.3 (prerequisites.tex, §prereq-filtered-complex).

This file formalizes the spectral sequence associated to a filtered chain complex,
its convergence to homology under bounded filtration hypotheses, and functoriality
with respect to filtration-preserving chain maps.

## Main declarations

* `FilteredChainComplex` — a chain complex with a compatible decreasing filtration
* `FilteredChainComplexHom` — a filtration-preserving chain map
* `filteredComplexSS` — the associated spectral sequence (axiom)
* `filteredComplexEInfty` — E∞-page data for the filtered complex SS
* `filteredComplexConvergence` — convergence under bounded filtration
* `filteredComplexFunctorial` — functoriality of the SS construction
* `filteredComplexSS_E0` — E₀-page description as associated graded
* `filteredComplexSS_diffDeg` — differential degree `d_r : (s,t) ↦ (s+r, t−r+1)`
-/

namespace KIP.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

/-! ### Filtered chain complexes

A filtered chain complex is a chain complex `K` (over ℤ) in an abelian
category `C`, equipped with a compatible decreasing filtration
`F^s K_n ⊇ F^{s+1} K_n` on each component, such that the differential
preserves the filtration. -/

/-- A filtered chain complex in an abelian category `C`.
  - `complex` is the underlying chain complex indexed by `ℤ`.
  - `F s n` is the subobject `F^s K_n ⊆ K_n` (the `s`-th filtration level
    of the `n`-th component).
  - `mono` asserts the filtration is decreasing: `F^{s+1} ≤ F^s`.
  - `differential_compat` asserts the differential `d : K_n → K_{n-1}`
    sends `F^s K_n` into `F^s K_{n-1}`, i.e., the filtration is compatible
    with the chain complex structure.
-/
structure FilteredChainComplex (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The underlying chain complex over ℤ -/
  complex : HomologicalComplex C (ComplexShape.down ℤ)
  /-- Filtration: F^s on the n-th component is a subobject of K_n -/
  F : ℤ → ∀ (n : ℤ), Subobject (complex.X n)
  /-- The filtration is decreasing: F^{s+1} K_n ≤ F^s K_n -/
  mono : ∀ (s n : ℤ), F (s + 1) n ≤ F s n
  /-- The differential preserves the filtration.
      Specifically, d maps F^s K_n into F^s K_{n-1}.
      Stated as: for each s and n, the composite `F^s K_n ↪ K_n →[d] K_{n-1}`
      factors through the inclusion `F^s K_{n-1} ↪ K_{n-1}`. -/
  differential_compat : ∀ (s n : ℤ),
    ∃ (g : Subobject.underlying.obj (F s n) ⟶ Subobject.underlying.obj (F s (n - 1))),
      g ≫ (F s (n - 1)).arrow = (F s n).arrow ≫ complex.d n (n - 1)

/-- A filtration on a chain complex is exhaustive if, for each n,
    `⋃_s F^s K_n = K_n` (everything is eventually in the filtration).
    In terms of subobjects: for each n, there exists s₀ such that
    F^{s₀} K_n = ⊤. -/
def FilteredChainComplex.Exhaustive {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) : Prop :=
  ∀ (n : ℤ), ∃ (s₀ : ℤ), K.F s₀ n = ⊤

/-- A filtration on a chain complex is bounded below if, for each n,
    there exists s₁ such that F^{s₁} K_n = ⊥ (= 0). -/
def FilteredChainComplex.BoundedBelow {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) : Prop :=
  ∀ (n : ℤ), ∃ (s₁ : ℤ), K.F s₁ n = ⊥

/-- A filtration is bounded if it is both exhaustive and bounded below. -/
def FilteredChainComplex.Bounded {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) : Prop :=
  K.Exhaustive ∧ K.BoundedBelow

/-! ### Morphisms of filtered chain complexes -/

/-- A morphism of filtered chain complexes is a chain map that
    preserves the filtration (f(F^s K_n) ⊆ F^s L_n). -/
structure FilteredChainComplexHom {C : Type u} [Category.{v} C] [Abelian C]
    (K L : FilteredChainComplex C) where
  /-- The underlying chain map -/
  f : K.complex ⟶ L.complex
  /-- The chain map preserves the filtration: f maps F^s K_n into F^s L_n.
      Stated as: for each s and n, the composite `F^s K_n ↪ K_n →[f_n] L_n`
      factors through the inclusion `F^s L_n ↪ L_n`. -/
  filtration_compat : ∀ (s n : ℤ),
    ∃ (g : Subobject.underlying.obj (K.F s n) ⟶ Subobject.underlying.obj (L.F s n)),
      g ≫ (L.F s n).arrow = (K.F s n).arrow ≫ f.f n

/-! ### Homology of the underlying chain complex -/

/-- The homology graded object of a filtered chain complex: `n ↦ H_n(K)`. -/
noncomputable def FilteredChainComplex.homologyGraded {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) : ℤ → C :=
  fun n => K.complex.homology n

/-! ### Associated spectral sequence

The fundamental theorem of filtered chain complexes: a filtered chain complex
gives rise to a spectral sequence.  For a filtered chain complex `K` with
filtration `F`, the spectral sequence has:
  - E₀^{s,t} = F^s K_{s+t} / F^{s+1} K_{s+t}  (associated graded)
  - E₁^{s,t} = H_{s+t}(F^s K / F^{s+1} K)     (homology of associated graded)
  - E₂^{s,t}, ...                                (derived by taking homology)

This is axiomatized here; the construction requires significant
homological algebra infrastructure. -/

/-- BHS §0.1.3, Axiom `prereq:ax:filtered-complex-ss`: existence of the spectral
    sequence associated to a filtered chain complex.

    Given a filtered chain complex `K`, produce a spectral sequence with
    bigrading `(s, t) : ℤ × ℤ`, where `s` is the filtration degree and
    `t` is such that `s + t` is the total degree.
    The E₀-page is `E₀^{s,t} = F^s K_{s+t} / F^{s+1} K_{s+t}`.

    Axiomatized because the full construction requires building the exact couple
    and deriving pages, which is substantial homological algebra not yet
    available in Mathlib. -/
axiom filteredComplexSS {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) : SpectralSequence C (ℤ × ℤ)

/-! ### E∞-page data -/

/-- BHS §0.1.2, Definition `prereq:def:einfty-data`: the E∞-page data for the
    filtered complex spectral sequence.

    Packages `filteredComplexSS K` with its limiting E∞-page and natural maps
    from each finite page to E∞. -/
axiom filteredComplexEInfty {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) : EInftyData C (ℤ × ℤ)

/-- Formalization bridge: the E∞-page data is built on `filteredComplexSS K`.

    Records that the underlying spectral sequence of the E∞ package equals the
    one constructed by `filteredComplexSS`. Needed to connect convergence
    statements (which use `EInftyData`) back to the page-level spectral
    sequence. -/
axiom filteredComplexEInfty_ss {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) :
    (filteredComplexEInfty K).ss = filteredComplexSS K

/-! ### Induced filtration on homology -/

/-- BHS §0.1.3, Axiom `prereq:ax:filtered-complex-convergence` (filtration part):
    the induced filtration on the homology of a filtered chain complex.

    `F^s H_n(K) = image(H_n(F^s K) → H_n(K))`, i.e., the image of the
    map on homology induced by the inclusion of the s-th filtration level.
    Equivalently, `F^s H_n(K) = ker(H_n(K) → H_n(K / F^s K))`. -/
axiom inducedHomologyFiltration {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) : Filtration K.homologyGraded

/-! ### Convergence

When the filtration is bounded, the spectral sequence converges to the
homology of the underlying chain complex. -/

/-- BHS §0.1.3, Axiom `prereq:ax:filtered-complex-convergence`: convergence
    of the filtered complex spectral sequence.

    If the filtration on `K` is bounded (exhaustive + bounded below), then
    the spectral sequence `filteredComplexSS K` converges:
      `E_∞^{s,t} ≅ F^s H_{s+t}(K) / F^{s+1} H_{s+t}(K)`
    where the filtration on homology is `inducedHomologyFiltration K`.

    Axiomatized because the proof requires showing the spectral sequence
    degenerates at a finite page for bounded filtrations. -/
axiom filteredComplexConvergence {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) (hK : K.Bounded) :
    Convergence (filteredComplexEInfty K) K.homologyGraded
      (inducedHomologyFiltration K)

/-! ### Functoriality

A morphism of filtered chain complexes induces a morphism of their
associated spectral sequences. -/

/-- BHS §0.1.3, Axiom `prereq:ax:filtered-complex-functoriality`: functoriality
    of the filtered complex spectral sequence construction.

    A morphism `f : K → L` of filtered chain complexes induces a morphism
    of spectral sequences `filteredComplexSS K → filteredComplexSS L`.
    Axiomatized because it follows from naturality of the exact couple
    construction with respect to filtered chain maps, which requires the
    full exact-couple infrastructure not yet available in Mathlib. -/
axiom filteredComplexFunctorial {C : Type u} [Category.{v} C] [Abelian C]
    {K L : FilteredChainComplex C}
    (f : FilteredChainComplexHom K L) :
    SpectralSequenceMorphism (filteredComplexSS K) (filteredComplexSS L)

/-! ### E₀ and E₁ page descriptions

These record what the pages look like, for use in downstream files. -/

/-- BHS §0.1.3, Axiom `prereq:ax:filtered-complex-ss` (E₀ description):
    the E₀-page of the filtered complex spectral sequence at bidegree `(s, t)`
    is the associated graded of the filtration:
    `E₀^{s,t} ≅ F^s K_{s+t} / F^{s+1} K_{s+t}`.

    Here `F^s K_{s+t} / F^{s+1} K_{s+t}` is expressed as the cokernel of the
    inclusion `F^{s+1} K_{s+t} ↪ F^s K_{s+t}`. -/
axiom filteredComplexSS_E0 {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) (s t : ℤ) :
    (filteredComplexSS K).Page (filteredComplexSS K).r₀ (s, t) ≅
    cokernel (Subobject.ofLE (K.F (s + 1) (s + t)) (K.F s (s + t))
      (K.mono s (s + t)))

/-- BHS §0.1.3, Axiom `prereq:ax:filtered-complex-ss` (differential degree):
    for the standard filtered complex spectral sequence, the differential on
    page `r` has bidegree `(r, 1−r)`:
      `d_r : E_r^{s,t} → E_r^{s+r, t−r+1}`.
    In particular the total degree shifts by 1: `(s+t) ↦ (s+t)+1−1 = s+t`. -/
axiom filteredComplexSS_diffDeg {C : Type u} [Category.{v} C] [Abelian C]
    (K : FilteredChainComplex C) (r : ℤ) :
    (filteredComplexSS K).diffDeg r = (r, 1 - r)

end KIP.SpectralSequence
