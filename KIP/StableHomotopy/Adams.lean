import Mathlib
import KIP.StableHomotopy.Cohomology
import KIP.SpectralSequence.Basic
import KIP.SpectralSequence.Convergence

/-!
# KIP.StableHomotopy.Adams

BHS §0.2.3 (prerequisites.tex §prereq-adams): The mod 2 Adams spectral sequence.

Formalizes the HF₂-Adams spectral sequence as a functor from the stable homotopy
category `𝒮` to bigraded converging spectral sequences in `AddCommGrpCat`.
Includes: Adams filtration on `π_*(X)`, convergence for finite spectra,
2-torsion on E₂, Adams filtration for maps, and detection.

## References

- Blueprint `prerequisites.tex`, §0.2.3 "Adams Spectral Sequence"
  (Axioms `prereq:ax:adams-ss`, `prereq:ax:adams-convergence`, `prereq:ax:adams-e2-order2`;
   Definitions `prereq:def:adams-filtration`, `prereq:def:adams-filtration-maps`)
- Blueprint `proof-main-theorem.tex`, §proof (uses Adams filtration and detection
  in the proof of Theorem 1.1)
-/

namespace KIP.StableHomotopy

open CategoryTheory CategoryTheory.Limits KIP.SpectralSequence

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-! ### Adams spectral sequence

The mod 2 Adams spectral sequence is a functor from the stable homotopy category
to bigraded spectral sequences in abelian groups.  The E₂-page is
`Ext^{s,t}_A(H*(X; F₂), F₂)` where `A` is the Steenrod algebra.

Differentials: `d_r : E_r^{s,t} → E_r^{s+r, t+r-1}`.

We axiomatize the existence and key properties of the Adams SS.

Blueprint: `prerequisites.tex`, §0.2.3 (`prereq:ax:adams-ss`). -/

/-- The Adams differential degree: `d_r` shifts bigrading by `(r, r - 1)`.
This means `d_r : E_r^{s,t} → E_r^{s+r, t+r-1}`. -/
def adamsDiffDeg : ℤ → ℤ × ℤ := fun r => (r, r - 1)

/-- BHS §0.2.3, Axiom `prereq:ax:adams-ss`: The HF₂-Adams spectral sequence
for a spectrum `X` in `𝒮`. This is a spectral sequence in `AddCommGrpCat`
with bigrading `ℤ × ℤ`. The `(s,t)`-entry on page `r` is `E_r^{s,t}(X)`.

Construction: From an Adams resolution of `X`, one obtains a filtered object
whose associated spectral sequence is the Adams SS. The E₂-page computes as
`Ext^{s,t}_A(H*(X; F₂), F₂)`. -/
axiom AdamsSS (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]
    (X : 𝒮) : SpectralSequence AddCommGrpCat.{v} (ℤ × ℤ)

/-- BHS §0.2.3, Axiom `prereq:ax:adams-ss`: The Adams spectral sequence starts
at page 2, i.e., `r₀ = 2`. -/
axiom adamsSS_r₀ (X : 𝒮) : (AdamsSS 𝒮 X).r₀ = 2

/-- BHS §0.2.3, Axiom `prereq:ax:adams-ss`: The differential degree on the Adams
SS is `(r, r-1)`, meaning `d_r : E_r^{s,t} → E_r^{s+r, t+r-1}`. -/
axiom adamsSS_diffDeg (X : 𝒮) : (AdamsSS 𝒮 X).diffDeg = adamsDiffDeg

/-- BHS §0.2.3, Axiom `prereq:ax:adams-ss` (functoriality): A map `f : X ⟶ Y`
induces a morphism of spectral sequences `AdamsSS(X) → AdamsSS(Y)`, compatible
with differentials. -/
axiom adamsSS_map {X Y : 𝒮} (f : X ⟶ Y) :
    SpectralSequenceMorphism (AdamsSS 𝒮 X) (AdamsSS 𝒮 Y)

/-- BHS §0.2.3, Axiom `prereq:ax:adams-ss` (functoriality, identity): The Adams SS
functor sends the identity map to the identity morphism of spectral sequences. -/
axiom adamsSS_map_id (X : 𝒮) :
    (adamsSS_map (𝟙 X)).φ = fun _ => 𝟙 _

/-- BHS §0.2.3, Axiom `prereq:ax:adams-ss` (functoriality, composition): The Adams SS
functor preserves composition: `AdamsSS(g ∘ f) = AdamsSS(g) ∘ AdamsSS(f)`. -/
axiom adamsSS_map_comp {X Y Z : 𝒮} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (adamsSS_map (f ≫ g)).φ = fun k =>
      (adamsSS_map f).φ k ≫ (adamsSS_map g).φ k

/-! ### Adams E∞ data

The E∞-page of the Adams spectral sequence, axiomatized via `EInftyData`.

Blueprint: `prerequisites.tex`, Definition `prereq:def:einfty-data` and
Axiom `prereq:ax:adams-convergence`. -/

/-- BHS §0.2.3, Definition `prereq:def:einfty-data` applied to the Adams SS:
The E∞-page data of the Adams spectral sequence for a spectrum `X`.
Packages the E∞-page together with the underlying spectral sequence. -/
axiom AdamsEInfty (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]
    (X : 𝒮) : EInftyData AddCommGrpCat.{v} (ℤ × ℤ)

/-- BHS §0.2.3, Definition `prereq:def:einfty-data`: The E∞ data for `X`
is associated with the Adams spectral sequence `AdamsSS 𝒮 X`. -/
axiom adamsEInfty_ss (X : 𝒮) : (AdamsEInfty 𝒮 X).ss = AdamsSS 𝒮 X

/-! ### Adams filtration on homotopy groups

The Adams spectral sequence provides a natural decreasing filtration on `π_*(X)`.
Adams filtration degree `s` records how deep into the filtration an element lies.

Formally, the Adams filtration on `π_n(X)` is a ℤ-indexed decreasing sequence of
subgroups `F^s π_n(X) ⊇ F^{s+1} π_n(X) ⊇ ⋯` such that the associated graded
pieces are identified with the E∞-page of the Adams SS via convergence.

Blueprint: `prerequisites.tex`, Definition `prereq:def:adams-filtration`. -/

/-- BHS §0.2.3, Definition `prereq:def:adams-filtration`: Predicate that an element
of `π_n(X)` has Adams filtration ≥ `s`. Concretely, `x ∈ F^s π_n(X)` means `x`
is in the image of maps that factor through `s` HF₂-acyclic maps.
Formalization bridge: axiomatized since the Adams tower construction is not
formalized; added in Polish Round 1. -/
axiom InAdamsFiltration (X : 𝒮) (s n : ℤ) (x : HomotopyGroup n X) : Prop

/-- An element of `π_n(X)` together with a witness that it has Adams filtration ≥ s. -/
structure AdamsFiltrationLevel (s n : ℤ) (X : 𝒮) where
  /-- The underlying element of π_n(X) -/
  val : HomotopyGroup n X
  /-- Witness that this element has Adams filtration ≥ s -/
  mem_filtration : InAdamsFiltration X s n val

/-- BHS §0.2.3, Definition `prereq:def:adams-filtration`: The Adams filtration
is decreasing: `F^{s+1} π_n(X) ⊆ F^s π_n(X)`. -/
axiom adamsFiltration_mono (X : 𝒮) (s n : ℤ)
    (x : AdamsFiltrationLevel (s + 1) n X) :
    ∃ y : AdamsFiltrationLevel s n X, y.val = x.val

/-- BHS §0.2.3, Definition `prereq:def:adams-filtration`: Every element of `π_n(X)`
has Adams filtration ≥ 0, i.e., `F^0 π_n(X) = π_n(X)`. -/
axiom adamsFiltration_zero (X : 𝒮) (n : ℤ) (x : HomotopyGroup n X) :
    ∃ y : AdamsFiltrationLevel 0 n X, y.val = x

/-! ### Finiteness and convergence

For finite spectra, the Adams SS converges to π_*(X) in the sense that
`E_∞^{s,t}(X) ≅ F^s π_{t-s}(X) / F^{s+1} π_{t-s}(X)`.

Blueprint: `prerequisites.tex`, Axiom `prereq:ax:adams-convergence`. -/

/-- Formalization bridge: A spectrum `X` is finite (built from finitely many cells).
Used as a hypothesis in the Adams SS convergence theorem (`prereq:ax:adams-convergence`).
The field is `True` because Mathlib does not formalize finite CW-spectra. -/
class IsFiniteSpectrum (X : 𝒮) : Prop where
  /-- Axiom: X is a finite CW-spectrum.
  TODO: Refine to a genuine finiteness condition (e.g., `Finite` on cells
  or a CW-dimension bound) once Mathlib formalizes finite CW-spectra. -/
  finite : True

/-- BHS §0.2.3, Axiom `prereq:ax:adams-convergence`: The Adams spectral sequence
converges to `π_*(X)` for finite `X`. For each `(s, t)`, there is an isomorphism
`E_∞^{s,t}(X) ≅ F^s π_{t-s}(X) / F^{s+1} π_{t-s}(X)`, where the right side
is the `s`-th associated graded piece of the Adams filtration on `π_{t-s}(X)`. -/
axiom adamsConvergence (X : 𝒮) [IsFiniteSpectrum X] :
    ∃ F : Filtration (HomotopyGroups X),
      Nonempty (Convergence (AdamsEInfty 𝒮 X).ss (HomotopyGroups X) F)

/-! ### Adams filtration for maps

The Adams filtration of a map `f : X ⟶ Y` measures the complexity of `f`
in terms of HF₂-acyclic factorizations:
  `AF(f) = sup { k | f factors as k maps each zero on HF₂-homology }`.

Blueprint: `prerequisites.tex`, Definition `prereq:def:adams-filtration-maps`. -/

/-- A map `f : X ⟶ Y` is zero on mod 2 homology if `HF₂_*(f) = 0`.
This means `Mod2Homology.pushforward f n = 0` for all n. -/
def IsZeroOnMod2Homology {X Y : 𝒮} (f : X ⟶ Y) : Prop :=
  ∀ (n : ℤ) (x : Mod2Homology n X), (Mod2Homology.pushforward f n) x = 0

/-- The Adams filtration of a map `f : X ⟶ Y`.
`AF(f) ≥ k` means `f` can be written as a composition of `k` maps,
each of which induces the zero map on mod 2 homology.
`AF(f)` is the supremum of such `k`. -/
structure AdamsFiltrationOfMap {X Y : 𝒮} (f : X ⟶ Y) where
  /-- The Adams filtration value -/
  val : ℤ
  /-- Adams filtration is non-negative -/
  property : val ≥ 0

/-- BHS §0.2.3, Definition `prereq:def:adams-filtration-maps`: Every map
`f : X ⟶ Y` has a well-defined Adams filtration `AF(f) ≥ 0`. -/
axiom adamsFiltration_exists {X Y : 𝒮} (f : X ⟶ Y) :
    AdamsFiltrationOfMap f

/-- Shorthand: the Adams filtration of a map. -/
noncomputable def AF {X Y : 𝒮} (f : X ⟶ Y) : ℤ :=
  (adamsFiltration_exists f).val

/-- `f` has Adams filtration ≥ k: it factors as a composition of k maps,
each zero on HF₂-homology. -/
def HasAF_ge {X Y : 𝒮} (f : X ⟶ Y) (k : ℤ) : Prop :=
  AF f ≥ k

/-- BHS §0.2.3, Definition `prereq:def:adams-filtration-maps` (characterization):
`AF(f) ≥ 1` if and only if `f` is zero on mod 2 homology `HF₂_*`.
More generally, `AF(f) ≥ k` iff `f` factors as `k` HF₂-acyclic maps. -/
axiom af_ge_one_iff_zero_on_homology {X Y : 𝒮} (f : X ⟶ Y) :
    HasAF_ge f 1 ↔ IsZeroOnMod2Homology f

/-- Formalization bridge: The identity map has Adams filtration 0.
Immediate from the definition of `AF` since `𝟙 X` does not factor through
any HF₂-acyclic map nontrivially. -/
axiom af_id (X : 𝒮) : AF (𝟙 X) = 0

/-- BHS §0.2.3, Proposition `prereq:prop:adams-filtration-characterization`
(subadditivity): Adams filtration is subadditive under composition,
`AF(g ∘ f) ≥ AF(f) + AF(g)`. -/
axiom af_comp {X Y Z : 𝒮} (f : X ⟶ Y) (g : Y ⟶ Z) :
    AF (f ≫ g) ≥ AF f + AF g

/-! ### 2-torsion property of E₂ elements

All elements in the E₂-page of the mod 2 Adams spectral sequence have
order dividing 2. This is because `E₂ = Ext_A(H*(X; F₂), F₂)` and
these Ext groups are F₂-vector spaces (A is an F₂-algebra).

Blueprint: `prerequisites.tex`, Axiom `prereq:ax:adams-e2-order2`. -/

/-- BHS §0.2.3, Axiom `prereq:ax:adams-e2-order2`: Every element in the E₂-page
of the Adams spectral sequence is 2-torsion (has order dividing 2), i.e.,
`x + x = 0` for all `x ∈ E₂`. This holds because `E₂^{s,t}(X)` is an
F₂-vector space (`Ext_A` over the F₂-algebra `A`). -/
axiom adams_2torsion (X : 𝒮) (k : ℤ × ℤ) :
    ∀ (x : (AdamsSS 𝒮 X).Page 2 k), x + x = 0

/-! ### Functoriality of Adams filtration on homotopy groups

The Adams filtration is natural with respect to maps of spectra:
a map f : X → Y sends F^s π_n(X) to F^s π_n(Y).

Blueprint: `prerequisites.tex`, Proposition `prereq:prop:adams-filtration-characterization`. -/

/-- BHS §0.2.3, Proposition `prereq:prop:adams-filtration-characterization`
(naturality): A map `f : X ⟶ Y` preserves Adams filtration:
if `x ∈ F^s π_n(X)` then `π_n(f)(x) ∈ F^s π_n(Y)`. -/
axiom adamsFiltration_functorial {X Y : 𝒮} (f : X ⟶ Y) (s n : ℤ)
    (x : AdamsFiltrationLevel s n X) :
    ∃ y : AdamsFiltrationLevel s n Y, y.val = x.val ≫ f

/-- BHS §0.2.3, Definition `prereq:def:detect` (detection): The Adams filtration
of a nonzero map `f` determines its detection in the Adams spectral sequence.
A nonzero map of Adams filtration `s` is detected by a nonzero element
in `E_∞^{s, *}`. Used in `proof-main-theorem.tex` (Proposition `prop:possibleh62`)
to relate Adams filtration of `θ₅²` to E∞-page elements. -/
axiom af_detection {X Y : 𝒮} (f : X ⟶ Y)
    (hf : f ≠ 0) :
    ∃ t : ℤ, ¬ IsZero ((AdamsEInfty 𝒮 Y).EInfty (AF f, t))

end KIP.StableHomotopy
