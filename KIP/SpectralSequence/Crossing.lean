/-
  KIP.SpectralSequence.Crossing
  §2.7 Crossing predicates for spectral sequence differentials

  Blueprint: Definition 2.7 from arXiv:2412.10879
  Informal:  informal/crossing.md

  Defines the crossing predicate for spectral sequence differentials.
  All declarations are definitions — no theorems expected.
-/
import Mathlib
import KIP.SpectralSequence.Basic
import KIP.SpectralSequence.Convergence

namespace KIP.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [AddCommGroup ι] [DecidableEq ι]

/-! ### Essential differentials -/

/-- A differential `d r` at index `k` is **essential** if the morphism is nonzero. -/
def IsEssentialAt (E : SpectralSequence C ι) (r : ℤ) (k : ι) : Prop :=
  E.d r k ≠ 0

/-! ### Differential datum -/

/-- Packages a differential in a spectral sequence with its filtration data.
    This bundles a spectral sequence, a page number `r`, a source bidegree `k`,
    a filtration degree function, and a proof that the differential is essential. -/
structure DifferentialDatum (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- The underlying spectral sequence -/
  E : SpectralSequence C ι
  /-- Page number -/
  r : ℤ
  /-- Source bidegree -/
  k : ι
  /-- Filtration degree function assigning a filtration level to each bidegree -/
  filtDeg : ι → ℤ
  /-- The differential at `(r, k)` is essential (nonzero) -/
  is_essential : IsEssentialAt E r k

/-! ### Crossing predicates (Definition 2.7) -/

/-- **Definition 2.7(1)**: The differential `d_r` at `(k, s)` has a **crossing
    hitting filtration `p`**.

    There exists another element at filtration `s + a` (with `a > 0`) whose
    essential differential `d_m` has target at filtration `p = s + a + m`,
    and `p ≤ s + r` (target filtration is at most the original target's). -/
def HasCrossingAt (dd : DifferentialDatum C ι) (p : ℤ) : Prop :=
  let s := dd.filtDeg dd.k
  ∃ (a : ℤ) (_ : 0 < a) (m : ℤ) (k' : ι),
    dd.filtDeg k' = s + a ∧
    IsEssentialAt dd.E m k' ∧
    p = s + a + m ∧
    s + a + m ≤ s + dd.r

/-- **Definition 2.7(2)**: The differential `d_r` at `(k, s)` has **no crossing
    hitting the range Fil ≥ p**.

    There does NOT exist another element at filtration `s + a` (with `a > 0`)
    whose essential differential `d_m` has target filtration in `[p, s + r]`. -/
def NoCrossingRange (dd : DifferentialDatum C ι) (p : ℤ) : Prop :=
  ¬ ∃ (a : ℤ) (_ : 0 < a) (m : ℤ) (k' : ι),
    dd.filtDeg k' = dd.filtDeg dd.k + a ∧
    IsEssentialAt dd.E m k' ∧
    p ≤ dd.filtDeg dd.k + a + m ∧
    dd.filtDeg dd.k + a + m ≤ dd.filtDeg dd.k + dd.r

/-- **Definition 2.7(3)**: The differential `d_r` at `(k, s)` has **no crossing**.

    Equivalent to: no crossing hitting the range `Fil ≥ s + 1`. -/
def NoCrossing (dd : DifferentialDatum C ι) : Prop :=
  NoCrossingRange dd (dd.filtDeg dd.k + 1)

/-! ### SpectralSequence-based constructors -/

/-- Construct a `DifferentialDatum` directly from a spectral sequence, a page `r`,
    a source bidegree `k`, a filtration degree function, and an essentiality proof. -/
def DifferentialDatum.ofSpectralSequence
    (E : SpectralSequence C ι) (r : ℤ) (k : ι)
    (filtDeg : ι → ℤ) (hess : IsEssentialAt E r k) :
    DifferentialDatum C ι :=
  { E := E, r := r, k := k, filtDeg := filtDeg, is_essential := hess }

/-! ### Crossing composed with convergence -/

/-- Crossing predicate relativised to a convergent spectral sequence.
    Given a convergence `conv : Convergence E A F`, this wraps `HasCrossingAt`
    so that the caller does not need to manually extract the filtration degree. -/
def HasCrossingAt_conv {ω : Type w} [AddCommGroup ω] [DecidableEq ω]
    {E : SpectralSequence C ω} {ω' : Type w} {A : ω' → C} {F : Filtration A}
    (_conv : Convergence E A F) (dd : DifferentialDatum C ω) (p : ℤ) : Prop :=
  HasCrossingAt dd p

end KIP.SpectralSequence
