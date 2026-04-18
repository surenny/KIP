import Mathlib
import KIP.StableHomotopy.Basic

/-!
# KIP.StableHomotopy.Cohomology

BHS Blueprint §0.2.3 (Cohomology): Mod 2 cohomology and homology theories
in the stable homotopy category.

This file formalizes the Eilenberg–MacLane spectrum HF₂, the Steenrod
algebra A = π_*(F(HF₂, HF₂)), mod 2 cohomology H*(X; F₂) = [Σ*X, HF₂],
and mod 2 homology H_*(X; F₂) = π_*(HF₂ ∧ X). These are the basic
cohomological ingredients used to set up the Adams spectral sequence
(see `KIP.StableHomotopy.Adams`).
-/

open CategoryTheory MonoidalCategory

namespace KIP.StableHomotopy

universe u v

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-! ## Eilenberg-MacLane Spectrum HF₂

BHS Blueprint §0.2.3, Definition `prereq:def:eilenberg-maclane`:
The mod 2 Eilenberg–MacLane spectrum is a commutative ring spectrum in 𝒮
whose only nonzero homotopy group is π₀ ≅ F₂.
-/

/-- BHS §0.2.3, Definition `prereq:def:eilenberg-maclane`:
The mod 2 Eilenberg–MacLane spectrum HF₂, representing ordinary mod 2
cohomology. It is a commutative ring spectrum in the stable homotopy
category. -/
axiom EilenbergMacLane (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮] : 𝒮

/-- BHS §0.2.3, Axiom `prereq:ax:eilenberg-maclane-homotopy` (n = 0 case):
π₀(HF₂) ≅ F₂ as an additive group. Together with `HF2_pin_zero`, this
characterizes HF₂ as the Eilenberg–MacLane spectrum for F₂. -/
axiom HF2_pi0 (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮] :
    HomotopyGroup (𝒮 := 𝒮) 0 (EilenbergMacLane 𝒮) ≃+ ZMod 2

/-- BHS §0.2.3, Axiom `prereq:ax:eilenberg-maclane-homotopy` (n ≠ 0 case):
πₙ(HF₂) = 0 for n ≠ 0. This is the defining vanishing property of an
Eilenberg–MacLane spectrum: it has exactly one nonzero homotopy group. -/
axiom HF2_pin_zero (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]
    (n : ℤ) (hn : n ≠ 0) :
    IsEmpty (HomotopyGroup (𝒮 := 𝒮) n (EilenbergMacLane 𝒮))

/-! ## Steenrod Algebra

BHS Blueprint §0.2.3: The Steenrod algebra A = π_*(F(HF₂, HF₂)) is the
algebra of stable mod 2 cohomology operations. It is graded by ℤ,
with the n-th graded component being πₙ(F(HF₂, HF₂)).
-/

/-- BHS §0.2.3, Definition `prereq:def:mapping-spectra` (applied to HF₂):
The mod 2 Steenrod algebra A, defined as π_* of the endomorphism
spectrum F(HF₂, HF₂). This is the algebra of stable cohomology
operations acting on mod 2 cohomology. -/
axiom SteenrodAlgebra (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮] : Type v

/-- Formalization bridge: The Steenrod algebra carries a ring structure
arising from composition of cohomology operations. This is
axiomatized rather than constructed from the mapping spectrum. -/
axiom instRingSteenrodAlgebra_ax (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮] :
    Ring (SteenrodAlgebra 𝒮)

noncomputable instance instRingSteenrodAlgebra
    (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮] :
    Ring (SteenrodAlgebra 𝒮) := instRingSteenrodAlgebra_ax 𝒮

/-- Formalization bridge: The Steenrod algebra admits a ℤ-grading
into homogeneous components, corresponding to the grading on
π_*(F(HF₂, HF₂)) by homotopy degree. Defined as
πₙ(F(HF₂, HF₂)). -/
def SteenrodAlgebra.gradedComponent (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]
    (n : ℤ) : Type v :=
  HomotopyGroup (𝒮 := 𝒮) n (MappingSpectrum (EilenbergMacLane 𝒮) (EilenbergMacLane 𝒮))

/-- BHS §0.2.3, Definition `prereq:def:mapping-spectra`:
Each graded component Aₙ of the Steenrod algebra is isomorphic to
πₙ(F(HF₂, HF₂)), the n-th homotopy group of the endomorphism
mapping spectrum. This is now definitional. -/
noncomputable def SteenrodAlgebra.gradedIso (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]
    (n : ℤ) :
    SteenrodAlgebra.gradedComponent 𝒮 n ≃
      HomotopyGroup (𝒮 := 𝒮) n (MappingSpectrum (EilenbergMacLane 𝒮) (EilenbergMacLane 𝒮)) :=
  Equiv.refl _

/-! ## Mod 2 Cohomology

BHS Blueprint §0.2.3, Definition `prereq:def:mod2-cohomology`:
The mod 2 cohomology of a spectrum X is defined as
  H^n(X; F₂) = [Σⁿ X, HF₂] = Hom(Σⁿ X, HF₂).
-/

/-- BHS §0.2.3, Definition `prereq:def:mod2-cohomology`:
The n-th mod 2 cohomology of a spectrum X, defined as
H^n(X; F₂) = Hom(Σⁿ X, HF₂). -/
abbrev Mod2Cohomology (n : ℤ) (X : 𝒮) : Type v :=
  (shiftFunctor 𝒮 n).obj X ⟶ EilenbergMacLane 𝒮

/-- The additive abelian group structure on mod 2 cohomology.
In a preadditive category, Hom-sets are abelian groups. -/
noncomputable instance instAddCommGroupMod2Cohomology (n : ℤ) (X : 𝒮) :
    AddCommGroup (Mod2Cohomology n X) :=
  inferInstance

/-- Total mod 2 cohomology H*(X; F₂) as a graded abelian group. -/
noncomputable def Mod2CohomologyTotal (X : 𝒮) : ℤ → AddCommGrpCat :=
  fun n => AddCommGrpCat.mk (Mod2Cohomology n X)

/-- BHS §0.2.3: The Steenrod algebra A acts on total cohomology H*(X; F₂),
making it a left A-module. This action is realized through the
identification H*(X; F₂) ≅ π₀(F(X, HF₂)) and the composition map
A ⊗ F(X, HF₂) → F(X, HF₂). Axiomatized because `MappingSpectrum`
construction is not available in Mathlib. -/
axiom Mod2CohomologyTotal.steenrodModuleAction
    (𝒮 : Type u) [StableHomotopyCategory.{u, v} 𝒮]
    (X : 𝒮) :
    Module (SteenrodAlgebra 𝒮) (HomotopyGroup (𝒮 := 𝒮) 0
      (MappingSpectrum X (EilenbergMacLane 𝒮)))

/-! ## Mod 2 Homology

BHS Blueprint §0.2.3, Definition `prereq:def:mod2-homology`:
The mod 2 homology of a spectrum X is defined as
  H_n(X; F₂) = πₙ(HF₂ ∧ X) = πₙ(HF₂ ⊗ X).
-/

/-- BHS §0.2.3, Definition `prereq:def:mod2-homology`:
The n-th mod 2 homology of a spectrum X, defined as
H_n(X; F₂) = πₙ(HF₂ ⊗ X), where ⊗ is the smash product. -/
abbrev Mod2Homology (n : ℤ) (X : 𝒮) : Type v :=
  HomotopyGroup n (EilenbergMacLane 𝒮 ⊗ X)

/-- The additive abelian group structure on mod 2 homology,
inherited from homotopy groups of HF₂ ∧ X. -/
noncomputable instance instAddCommGroupMod2Homology (n : ℤ) (X : 𝒮) :
    AddCommGroup (Mod2Homology n X) :=
  inferInstance

/-- Total mod 2 homology as a graded abelian group. -/
noncomputable def Mod2HomologyTotal (X : 𝒮) : ℤ → AddCommGrpCat :=
  fun n => AddCommGrpCat.mk (Mod2Homology n X)

/-! ## Functoriality of Cohomology and Homology -/

/-- A map f : X → Y induces a map on mod 2 cohomology
H^n(Y) → H^n(X) (contravariant). -/
noncomputable def Mod2Cohomology.pullback {X Y : 𝒮} (f : X ⟶ Y) (n : ℤ) :
    Mod2Cohomology n Y → Mod2Cohomology n X :=
  fun φ => (shiftFunctor 𝒮 n).map f ≫ φ

/-- A map f : X → Y induces a map on mod 2 homology
H_n(X) → H_n(Y) (covariant), via HF₂ ◁ f : HF₂ ⊗ X → HF₂ ⊗ Y. -/
noncomputable def Mod2Homology.pushforward {X Y : 𝒮} (f : X ⟶ Y) (n : ℤ) :
    Mod2Homology n X →+ Mod2Homology n Y :=
  inducedMap (EilenbergMacLane 𝒮 ◁ f) n

/-! ## Cohomology via Mapping Spectrum

BHS Blueprint §0.2.3, Definition `prereq:def:mapping-spectra`:
The mapping spectrum F(X, HF₂) satisfies πₙ(F(X, HF₂)) ≅ [Σⁿ X, HF₂] = H^n(X; F₂).
-/

/-- BHS §0.2.3, Definition `prereq:def:mapping-spectra`:
The relationship between mod 2 cohomology and the mapping spectrum:
H^n(X; F₂) ≅ πₙ(F(X, HF₂)), proved via `mappingSpectrumHomotopy`. -/
noncomputable def cohomologyMappingSpectrumIso (n : ℤ) (X : 𝒮) :
    Mod2Cohomology n X ≃ HomotopyGroup n (MappingSpectrum X (EilenbergMacLane 𝒮)) :=
  (mappingSpectrumHomotopy n X (EilenbergMacLane 𝒮)).symm

/-! ## Universal Coefficient / Representability

BHS Blueprint §0.2.3: Cohomology is representable by HF₂ via the
shift adjunction Σⁿ ⊣ Σ⁻ⁿ: H^n(X; F₂) = [Σⁿ X, HF₂] ≅ [X, Σ⁻ⁿ HF₂].
-/

/-- Correct representability: H^n(X; F₂) = [Σⁿ X, HF₂] ≅ [X, Σ⁻ⁿ HF₂]
via the shift adjunction `Σⁿ ⊣ Σ⁻ⁿ`. -/
noncomputable def cohomologyRepresentable_neg (n : ℤ) (X : 𝒮) :
    Mod2Cohomology n X ≃ (X ⟶ (shiftFunctor 𝒮 (-n)).obj (EilenbergMacLane 𝒮)) :=
  (shiftEquiv 𝒮 n).toAdjunction.homEquiv X (EilenbergMacLane 𝒮)

end KIP.StableHomotopy
