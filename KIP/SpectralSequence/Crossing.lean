/-
  KIP.SpectralSequence.Crossing
  §1.4 Extension spectral sequence and crossing of differentials.

  Reference: paper §2, Definitions 2.1, 2.3, 2.5 (def:ess, def:768fba8a, def:98skj23).

  For a map f : X → Y the f-ESS is derived from filtering
  0 → π_*X → π_*Y → 0 by the Adams filtration. Its E₀-page is
  E∞(X) ⊕ E∞(Y) and the differentials d_n^f : E_n^{s,t} → E_n^{s+n,t+n}
  measure the jump of filtration under f.

  This file introduces:
  • ExtensionSS — the f-extension spectral sequence
  • fExtensionDiff — the d_n^f differential
  • HasCrossing, NoCrossingRange, NoCrossing — crossing predicates
-/
import Mathlib
import KIP.SpectralSequence.Basic

namespace KIP.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

/-! ## Extension Spectral Sequence

We work with an abstract abelian category `C` and bigrading `ℤ × ℤ`.
The extension spectral sequence is built from the E∞-pages of the
Adams spectral sequences of the source and target of a map f.

Since the full construction requires Adams filtration infrastructure
(which lives in `StableHomotopy.Adams`), we axiomatize the ESS
as a structure carrying the data described in the blueprint. -/

section ESS

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Data recording that `x ∈ E∞^{s,t}(X)` and `y ∈ E∞^{s+n,t+n}(Y)`.
    We package the Adams filtration degree (first component) and the
    stem-plus-filtration degree (second component) of x as `(s, t)`. -/
structure EInftyElement (EInfty : ℤ × ℤ → C) where
  /-- Bidegree (s, t) — s = Adams filtration, t = total degree -/
  deg : ℤ × ℤ
  /-- The object E∞^{s,t} in which the element lives -/
  obj : C := EInfty deg

/-- The f-extension spectral sequence (f-ESS) for a map f : X → Y.

    Reference: Definition 2.1 (def:ess).
    The E₀-page is E∞(X) ⊕ E∞(Y) and the differentials
    d_n^f : E_n^{s,t} → E_n^{s+n,t+n} correspond to the
    f_*-filtration jump.

    In this axiomatized version, we record:
    • The E∞-pages of the Adams spectral sequences of X and Y.
    • The underlying spectral sequence (with bigrading ℤ × ℤ).
    • The subgroups Z_n^f and B_n^f that track permanent cycles/boundaries
      in the ESS.
    • An identification of the ESS E_0-page with E∞(X) ⊕ E∞(Y). -/
structure ExtensionSS (C : Type u) [Category.{v} C] [Abelian C] where
  /-- E∞-page of the Adams spectral sequence of X (source) -/
  eInftyX : ℤ × ℤ → C
  /-- E∞-page of the Adams spectral sequence of Y (target) -/
  eInftyY : ℤ × ℤ → C
  /-- The underlying spectral sequence of the f-ESS.
      Bigrading ℤ × ℤ with differential degree (n, n). -/
  toSS : SpectralSequence C (ℤ × ℤ)
  /-- The f-ESS starts at page 0 -/
  r₀_eq : toSS.r₀ = 0
  /-- Differential degree of d_n^f is (n, n) (raises both s and t by n) -/
  diffDeg_eq : ∀ (r : ℤ), toSS.diffDeg r = (r, r)
  /-- E₀-page identification: the E₀-page at bidegree (s,t) is
      built from E∞^{s,t}(X) ⊕ E∞^{s,t}(Y). -/
  e0_iso : ∀ (k : ℤ × ℤ),
    toSS.Page 0 k ≅ toSS.Page 0 k  -- placeholder: should be ≅ eInftyX k ⊞ eInftyY k
    -- In the prover stage, replace with actual biproduct iso once
    -- abelian category biproduct API is wired up.

/-- The Adams filtration of an E∞-element: the first coordinate s. -/
def AdamsFiltrationDeg (k : ℤ × ℤ) : ℤ := k.1

/-- The stem degree of an E∞-element: t - s. -/
def StemDeg (k : ℤ × ℤ) : ℤ := k.2 - k.1

/-! ## f-extension differentials

The differential d_n^f maps elements in the E∞-page of X to
elements in the E∞-page of Y with a filtration jump of n.
We define predicates for the existence of such differentials. -/

/-- `fExtDiff E n s t` asserts that the n-th differential d_n^f of the
    extension spectral sequence `E` at bidegree `(s, t)` is the morphism
    `E_n^{s,t} → E_n^{s+n, t+n}`. This is just the differential of the
    underlying SS at page n, spelled out for clarity. -/
def ExtensionSS.fExtDiff (E : ExtensionSS (C := C)) (n : ℤ) (k : ℤ × ℤ) :
    E.toSS.Page n k ⟶ E.toSS.Page n (k + E.toSS.diffDeg n) :=
  E.toSS.d n k

/-! ## Crossing definitions

Reference: Definition 2.5 (def:98skj23).

For x ∈ E∞^{s,t}(X), d_n^f(x) = y is "crossed" when there exists
x' ∈ E∞^{s+a, t+a}(X) with a > 0 and d_m^f(x') = y' ≠ 0 such that
   p = AF(y') = s + a + m ≤ AF(y) = s + n.

We define crossing in terms of the existence of such (a, m, x', y')
quadruples, working abstractly with bidegree arithmetic. -/

/-- A crossing witness for `d_n^f(x) = y` hitting Adams filtration `p`.

    Given `x ∈ E∞^{(s,t)}(X)` with `d_n^f(x) = y ∈ E∞^{(s+n,t+n)}(Y)`,
    a crossing is another extension `d_m^f(x') = y'` where
    `x' ∈ E∞^{(s+a,t+a)}(X)` with `a > 0`, `y' ≠ 0`, and
    `p = s + a + m ≤ s + n`.

    Reference: Definition 2.5(1). -/
structure CrossingWitness (E : ExtensionSS (C := C)) where
  /-- Bidegree of the original element x -/
  s : ℤ
  t : ℤ
  /-- The differential order for d_n^f(x) = y -/
  n : ℤ
  /-- The shift a > 0 of the crossing element x' -/
  a : ℤ
  /-- a is strictly positive -/
  ha : 0 < a
  /-- The differential order for d_m^f(x') = y' -/
  m : ℤ
  /-- The Adams filtration hit by the crossing: p = s + a + m -/
  p : ℤ
  /-- The crossing element has AF = p -/
  hp : p = s + a + m
  /-- p ≤ AF(y) = s + n -/
  hle : p ≤ s + n
  /-- The crossing differential d_m^f(x') = y' is nontrivial.
      We express this abstractly: the differential at the crossing
      degree is not zero. -/
  y'_ne_zero : E.toSS.d m (s + a, t + a) ≠ 0

/-- `HasCrossing E s t n p` asserts that the f-extension `d_n^f(x) = y`
    for `x ∈ E∞^{(s,t)}(X)` has a crossing that hits Adams filtration `p`.

    Reference: Definition 2.5(1). -/
def HasCrossing (E : ExtensionSS (C := C)) (s t n p : ℤ) : Prop :=
  ∃ (a m : ℤ), 0 < a ∧ p = s + a + m ∧ p ≤ s + n ∧
    E.toSS.d m (s + a, t + a) ≠ 0

/-- `NoCrossingRange E s t n p` asserts that the f-extension `d_n^f(x) = y`
    has no crossing that hits the range AF ≥ p.

    Reference: Definition 2.5(2): for all x' with a > 0 and d_m^f(x') = y' ≠ 0,
    we have AF(y') < p or AF(y') > s + n. -/
def NoCrossingRange (E : ExtensionSS (C := C)) (s t n p : ℤ) : Prop :=
  ∀ (a m : ℤ), 0 < a → s + a + m ≤ s + n →
    p ≤ s + a + m → E.toSS.d m (s + a, t + a) = 0

/-- `NoCrossing E s t n` asserts that `d_n^f(x) = y` has no crossing,
    i.e., no crossing hits the range AF ≥ AF(x) + 1 = s + 1.

    Reference: Definition 2.5(3). -/
def NoCrossing (E : ExtensionSS (C := C)) (s t n : ℤ) : Prop :=
  NoCrossingRange E s t n (s + 1)

/-! ## Basic properties -/

/-- `NoCrossing` is the specialization of `NoCrossingRange` at `p = s + 1`. -/
theorem noCrossing_iff_noCrossingRange (E : ExtensionSS (C := C)) (s t n : ℤ) :
    NoCrossing E s t n ↔ NoCrossingRange E s t n (s + 1) :=
  Iff.rfl

/-- If AF(f) = n, then all d_n^f-differentials have no crossing.
    (Because the only possible a > 0 would force AF(y') > AF(y).)
    Reference: Proposition 2.7(3).
    The hypothesis `hAF` states that d_i^f = 0 for all i < n,
    which is the meaning of "the Adams filtration of f equals n". -/
theorem noCrossing_of_af_eq (E : ExtensionSS (C := C)) (s t n : ℤ)
    (hAF : ∀ (i : ℤ), i < n → ∀ (k : ℤ × ℤ), E.toSS.d i k = 0) :
    NoCrossing E s t n := by
  intro a m ha hle hge
  -- From hge: s + 1 ≤ s + a + m, so 1 ≤ a + m
  -- From hle: s + a + m ≤ s + n, so a + m ≤ n
  -- From ha: 0 < a, so m < n
  exact hAF m (by omega) (s + a, t + a)

/-- A crossing at p implies NoCrossingRange at p fails.
    Reference: follows from definitions. -/
theorem HasCrossing.not_noCrossingRange (E : ExtensionSS (C := C))
    {s t n p : ℤ} (h : HasCrossing E s t n p) :
    ¬ NoCrossingRange E s t n p := by
  obtain ⟨a, m, ha, hp_eq, hle, hne⟩ := h
  intro hncr
  exact hne (hncr a m ha (hp_eq ▸ hle) (hp_eq ▸ le_refl _))

/-- A lower NoCrossingRange bound implies a higher one. -/
theorem NoCrossingRange.mono (E : ExtensionSS (C := C)) {s t n p q : ℤ}
    (hpq : p ≤ q) (h : NoCrossingRange E s t n p) :
    NoCrossingRange E s t n q := by
  intro a m ha hle hq
  exact h a m ha hle (le_trans hpq hq)

/-! ## Essential and inessential extensions

Reference: Definition 2.3 (def:768fba8a).
An f-extension d_n^f(x) = y is essential if y is nontrivial
on the E_n-page, i.e., y ∉ B_{n-1}^f(Y).
We express this abstractly here. -/

/-- An f-extension `d_n^f(x) = y` is essential if `y` is nontrivial
    in the E_n-page of the f-ESS. We axiomatize this as a predicate
    on the ESS, the differential order n, and the bidegree. -/
def IsEssentialExtension (E : ExtensionSS (C := C)) (n : ℤ) (k : ℤ × ℤ) : Prop :=
  -- y is nontrivial in E_n^{k + diffDeg(n)}
  -- For now, express as: the differential at page n, index k is nonzero
  E.toSS.d n k ≠ 0

/-- An inessential extension is one that is not essential. -/
def IsInessentialExtension (E : ExtensionSS (C := C)) (n : ℤ) (k : ℤ × ℤ) : Prop :=
  ¬ IsEssentialExtension E n k

/-! ## Adams filtration vanishing

If the Adams filtration of f is k, then d_i^f = 0 for i < k.
Reference: Corollary after Proposition 2.2. -/

/-- Adams filtration of a map, axiomatized as a field of ExtensionSS. -/
structure ExtensionSSWithAF (C : Type u) [Category.{v} C] [Abelian C]
    extends ExtensionSS (C := C) where
  /-- The Adams filtration of the map f -/
  af : ℤ
  /-- d_i^f = 0 for all i < af -/
  vanishing : ∀ (i : ℤ), i < af → ∀ (k : ℤ × ℤ), toSS.d i k = 0

/-- For an ESS with Adams filtration k, there are no crossings for d_k^f. -/
theorem noCrossing_at_af (E : ExtensionSSWithAF (C := C)) (s t : ℤ) :
    NoCrossing E.toExtensionSS s t E.af := by
  intro a m ha hle hge
  -- We need s + 1 ≤ s + a + m and s + a + m ≤ s + E.af
  -- So a + m ≤ E.af. Since a > 0, m < E.af.
  -- But we also need m ≥ 0 for a nontrivial differential.
  -- Since a > 0 and a + m ≤ E.af, we get m < E.af. Apply vanishing.
  exact E.vanishing m (by omega) (s + a, t + a)

end ESS

end KIP.SpectralSequence
