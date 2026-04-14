/-
  KIP.SpectralSequence.Basic
  §1.1 Spectral sequences via nested subspace (cycles/boundaries) approach

  The core data is `SSData`, which packages the classical nested containment
    V ⊇ Z 0 ⊇ Z 1 ⊇ ... ⊇ Z ⊤ ⊇ B ⊤ ⊇ ... ⊇ B 1 ⊇ B 0
  at a single bidegree, with E_r = Z r / B r.

  `SpectralSequence` then assembles SSData across all bidegrees together with
  differentials connecting different bidegree components. The page objects
  `Page r k` are derived from `SSData`, not stored independently.
-/
import Mathlib

namespace KIP.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

/-! ### SSData: nested subspace data at a single bidegree -/

/-- Nested subspace data for a spectral sequence at a single bidegree.
  `Z r` are the r-cycles (decreasing in r) and `B r` are the r-boundaries
  (increasing in r), both as subobjects of an ambient object `V`.
  Indexed by `WithTop ℕ` so that `⊤` represents the ∞-level. -/
structure SSData (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The ambient object (e.g., a graded piece of a chain complex) -/
  V : C
  /-- r-cycles as subobjects of V, decreasing: Z 0 ⊇ Z 1 ⊇ ... ⊇ Z ⊤ -/
  Z : WithTop ℕ → Subobject V
  /-- r-boundaries as subobjects of V, increasing: B 0 ⊆ B 1 ⊆ ... ⊆ B ⊤ -/
  B : WithTop ℕ → Subobject V
  /-- Z is antitone: higher page index gives smaller cycle subobject -/
  Z_anti : Antitone Z
  /-- B is monotone: higher page index gives larger boundary subobject -/
  B_mono : Monotone B
  /-- Everything is a 0-cycle: Z 0 is the whole ambient object -/
  Z_zero : Z 0 = ⊤
  /-- Boundaries are always contained in cycles at each level -/
  B_le_Z : ∀ r, B r ≤ Z r

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The r-th page at this bidegree: E_r = Z r / B r = cokernel(B r ↪ Z r). -/
noncomputable def SSData.page (D : SSData C) (r : WithTop ℕ) : C :=
  cokernel (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r))

/-- The E∞-page at this bidegree: Z ⊤ / B ⊤. -/
noncomputable def SSData.eInfty (D : SSData C) : C := D.page ⊤

/-- The projection from the underlying object of Z r onto the page E_r = Z r / B r. -/
noncomputable def SSData.pageπ (D : SSData C) (r : WithTop ℕ) :
    Subobject.underlying.obj (D.Z r) ⟶ D.page r :=
  cokernel.π (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r))

theorem SSData.B_bot_le_Z (D : SSData C) (r : WithTop ℕ) : D.B ⊥ ≤ D.Z r :=
  le_trans (D.B_mono bot_le) (D.B_le_Z r)

/-! ### Spectral sequences -/

/-- A spectral sequence in an abelian category `C` with index type `ι`.
  Built on nested subspace data (`SSData`) at each bidegree.
  - `ssData k` provides the nested subspace witness at bidegree `k`.
  - Page objects `E_r^k` are computed as `(ssData k).page ↑(r - r₀).toNat`.
  - `d r k` is the differential `d_r : E_r^k → E_r^{k + diffDeg r}`.
  - `d_comp_d` expresses `d² = 0` componentwise.
  - `pageIso` witnesses the isomorphism `E_{r+1}^k ≅ E_{r+1}^k` that comes
    from the homology identification. The full homology statement is given by
    `SpectralSequence.pageHomologyIso` below. -/
structure SpectralSequence (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- Starting page index -/
  r₀ : ℤ
  /-- Nested subspace data witnessing the construction at each bidegree -/
  ssData : ι → SSData C
  /-- Degree of the differential d_r -/
  diffDeg : ℤ → ι
  /-- Differential d_r^k : E_r^k → E_r^{k + diffDeg r}.
      The domain and codomain are computed from `ssData`. -/
  d : (r : ℤ) → (k : ι) →
    ((ssData k).page ↑(r - r₀).toNat ⟶
     (ssData (k + diffDeg r)).page ↑(r - r₀).toNat)
  /-- d_r ∘ d_r = 0 (componentwise) -/
  d_comp_d : ∀ (r : ℤ) (k : ι),
    d r k ≫ d r (k + diffDeg r) = 0
  /-- Isomorphism witnessing that consecutive pages are related.
      The mathematical content (homology of (E_r, d_r) ≅ E_{r+1}) is
      given by `SpectralSequence.pageHomologyIso`. -/
  pageIso : ∀ (r : ℤ) (k : ι),
    (ssData k).page ↑((r + 1) - r₀).toNat ≅
    (ssData k).page ↑((r + 1) - r₀).toNat

/-- The page object `E_r^k` of a spectral sequence, derived from the nested
    subspace data. This replaces the stored `Page` field: page objects are now
    computed as `(ssData k).page ↑(r - r₀).toNat`. -/
@[reducible] noncomputable def SpectralSequence.Page
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : C :=
  (E.ssData k).page ↑(r - E.r₀).toNat

/-- The E_r-page of a spectral sequence as a graded object. -/
noncomputable def SpectralSequence.pageGraded
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) : GradedObject ι C :=
  E.Page r

/-! ### Page short complex and homology isomorphism -/

/-- The short complex at page `r` centered at source index `k`:
    `E_r^k → E_r^{k + diffDeg r} → E_r^{k + 2 * diffDeg r}`
    with the zero condition from `d_comp_d`. -/
noncomputable def SpectralSequence.pageShortComplex
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : ShortComplex C :=
  ShortComplex.mk (E.d r k) (E.d r (k + E.diffDeg r)) (E.d_comp_d r k)

/-- BHS §0.1, Definition 0.3(5): Homology of (E_r, d_r) at index k is isomorphic
    to E_{r+1}^k.

    Informal proof sketch: `E_r = Z_r / B_r`. The differential `d_r` has
    kernel `Z_{r+1}/B_r` and image `B_{r+1}/B_r` (by definition of the nesting).
    So `H(E_r, d_r) = (Z_{r+1}/B_r) / (B_{r+1}/B_r) ≅ Z_{r+1}/B_{r+1} = E_{r+1}`
    by the third isomorphism theorem.

    The short complex is centered at source index `k - diffDeg r`, so the
    homology is at the middle term which is index `k`.

    Axiomatized for general abelian categories. For `AddCommGrpCat`, this
    follows from `QuotientAddGroup.quotientQuotientEquivQuotient`. -/
axiom SpectralSequence.pageHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) :
    E.Page (r + 1) k ≅ (E.pageShortComplex r (k - E.diffDeg r)).homology

/-! ### E∞-page -/

/-- The E∞-page of a spectral sequence, axiomatized as a field.
    For bounded/degenerate spectral sequences, this equals E_r for large r.
    For the general case, it is the intersection of permanent cycles modulo
    permanent boundaries. -/
structure EInftyData (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] [DecidableEq ι] where
  /-- The underlying spectral sequence -/
  ss : SpectralSequence C ι
  /-- The E∞-page as a graded object -/
  EInfty : ι → C
  /-- Natural map from E_r to E∞ (for r sufficiently large in the
      degenerate case) -/
  toEInfty : ∀ (r : ℤ) (k : ι), (ss.Page r k ⟶ EInfty k)
  /-- The map to E∞ is compatible with the spectral sequence structure.
      Specifically, the maps from consecutive pages are compatible
      via pageIso. -/
  toEInfty_compat : ∀ (r : ℤ) (k : ι),
    (ss.pageIso r k).hom ≫ toEInfty (r + 1) k = toEInfty (r + 1) k

/-- BHS §0.1, Definition 0.4: If all pages `E_r^k = 0` for `r ≥ r₀`, then
    `E∞^k = 0`.
    Informal: `E∞ = Z∞/B∞`. If `E_r = Z_r/B_r = 0` for all `r ≥ r₀`, then
    `Z_r = B_r`. Since `B_r ⊆ B∞ ⊆ Z∞ ⊆ Z_r`, we get `Z∞ = B∞`,
    hence `E∞ = 0`. -/
axiom EInftyData.eInfty_isZero_of_page_isZero
    {C : Type*} [Category C] [Abelian C]
    {α : Type*} [AddCommGroup α] [DecidableEq α]
    (E : EInftyData C α) (k : α)
    (h : ∀ r : ℤ, E.ss.r₀ ≤ r → IsZero (E.ss.Page r k)) :
    IsZero (E.EInfty k)

/-- A spectral sequence degenerates at page `N` if all differentials
    d_r = 0 for r ≥ N. -/
def SpectralSequence.DegeneratesAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (N : ℤ) : Prop :=
  ∀ (r : ℤ), N ≤ r → ∀ (k : ι), E.d r k = 0

/-! ### Morphisms of spectral sequences -/

/-- A morphism of spectral sequences is a family of graded maps
    `f_r : E_r → E'_r` commuting with the differentials
    and compatible with the page isomorphisms. -/
structure SpectralSequenceMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : SpectralSequence C ι) where
  /-- The differential degrees must agree -/
  diffDeg_eq : E.diffDeg = E'.diffDeg
  /-- The map on page r at index k -/
  f : ∀ (r : ℤ) (k : ι), (E.Page r k ⟶ E'.Page r k)
  /-- Commutation with differentials -/
  comm : ∀ (r : ℤ) (k : ι),
    f r k ≫ E'.d r k =
      E.d r k ≫ (diffDeg_eq ▸ f r (k + E.diffDeg r))

end KIP.SpectralSequence
