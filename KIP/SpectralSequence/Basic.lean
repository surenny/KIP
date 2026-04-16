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
  /-- Z ⊤ is the greatest lower bound of all finite Z_i.
      Combined with `Z_anti` (which gives `Z ⊤ ≤ Z ↑i` for all `i`), this says
      `Z ⊤ = ⨅ᵢ Z ↑i`. -/
  Z_top_greatest : ∀ (X : Subobject V), (∀ i : ℕ, X ≤ Z ↑i) → X ≤ Z ⊤
  /-- B ⊤ is the least upper bound of all finite B_i.
      Combined with `B_mono` (which gives `B ↑i ≤ B ⊤` for all `i`), this says
      `B ⊤ = ⨆ᵢ B ↑i`. -/
  B_top_least : ∀ (X : Subobject V), (∀ i : ℕ, B ↑i ≤ X) → B ⊤ ≤ X

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

/-- When B r = Z r, the page E_r = Z r / B r is zero.
    The inclusion B r ↪ Z r is an iso when B r = Z r, hence epi, so its
    cokernel vanishes. -/
theorem SSData.page_isZero_of_eq (D : SSData C) (r : WithTop ℕ) (h : D.B r = D.Z r) :
    IsZero (D.page r) := by
  unfold SSData.page
  have : IsIso (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) := by
    rw [← Subobject.isoOfEq_hom _ _ h]
    infer_instance
  exact isZero_cokernel_of_epi _

/-- The converse: if the page is zero, then B r = Z r. -/
theorem SSData.eq_of_page_isZero (D : SSData C) (r : WithTop ℕ) (h : IsZero (D.page r)) :
    D.B r = D.Z r := by
  unfold SSData.page at h
  have hepi : Epi (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) := by
    rwa [Preadditive.epi_iff_isZero_cokernel]
  haveI : IsIso (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)) := isIso_of_mono_of_epi _
  apply le_antisymm (D.B_le_Z r)
  exact Subobject.le_of_comm (inv (Subobject.ofLE (D.B r) (D.Z r) (D.B_le_Z r)))
    (by simp [Subobject.ofLE_arrow])

/-! ### Graded complexes -/

/-- A graded complex in an abelian category `C` indexed by `ι`.
    Consists of a graded object with a homogeneous differential of a fixed
    degree satisfying d² = 0. -/
structure GradedComplex (C : Type u) [Category.{v} C] [Abelian C]
    (ι : Type w) [AddCommGroup ι] where
  /-- The graded object: `obj k` is the component at index `k`. -/
  obj : ι → C
  /-- The degree of the differential. -/
  d_deg : ι
  /-- The differential: `d k : obj k ⟶ obj (k + d_deg)`. -/
  d : (k : ι) → obj k ⟶ obj (k + d_deg)
  /-- d² = 0: the composite of two consecutive differentials is zero. -/
  d_sq : ∀ k, d k ≫ d (k + d_deg) = 0

/-- The short complex at index `k` of a graded complex:
    `obj (k - d_deg) → obj k → obj (k + d_deg)` with zero condition from d².
    Uses `eqToHom` to handle the reindexing `(k - d_deg) + d_deg = k`. -/
noncomputable def GradedComplex.shortComplex
    {ι : Type w} [AddCommGroup ι]
    (G : GradedComplex C ι) (k : ι) : ShortComplex C :=
  { X₁ := G.obj (k - G.d_deg)
    X₂ := G.obj k
    X₃ := G.obj (k + G.d_deg)
    f := G.d (k - G.d_deg) ≫ eqToHom (show G.obj (k - G.d_deg + G.d_deg) = G.obj k by
      congr 1; abel)
    g := G.d k
    zero := by
      simp only [Category.assoc]
      have key : eqToHom (show G.obj (k - G.d_deg + G.d_deg) = G.obj k by
          congr 1; abel) ≫ G.d k =
        G.d (k - G.d_deg + G.d_deg) ≫ eqToHom (show G.obj (k - G.d_deg + G.d_deg + G.d_deg) =
          G.obj (k + G.d_deg) by congr 1; abel) := by
        rw [eqToHom_comp_iff]; simp
      rw [key, ← Category.assoc, G.d_sq, zero_comp] }

/-- The homology of a graded complex at index `k`. -/
noncomputable def GradedComplex.homology
    {ι : Type w} [AddCommGroup ι]
    (G : GradedComplex C ι) (k : ι) : C :=
  (G.shortComplex k).homology

/-! ### Spectral sequences -/

/-- A spectral sequence in an abelian category `C` with index type `ι`.
  Built on nested subspace data (`SSData`) at each bidegree.
  - `ssData k` provides the nested subspace witness at bidegree `k`.
  - Page objects `E_r^k` are computed as `(ssData k).page ↑(r - r₀).toNat`.
  - `d r k` is the differential `d_r : E_r^k → E_r^{k + diffDeg r}`.
  - `d_comp_d` expresses `d² = 0` componentwise. -/
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
  /-- The canonical quotient map Z_r → E_r = Z_r / B_r.
      This is `(ssData k).pageπ ↑(r - r₀).toNat`. Made a field so that
      Z_succ / B_succ can reference it without circularity issues. -/
  induced_d : (r : ℤ) → (k : ι) →
    (Subobject.underlying.obj ((ssData k).Z ↑(r - r₀).toNat) ⟶
     (ssData k).page ↑(r - r₀).toNat)
  /-- `induced_d` equals the canonical cokernel projection `pageπ`. -/
  induced_d_eq : ∀ (r : ℤ) (k : ι),
    induced_d r k = (ssData k).pageπ ↑(r - r₀).toNat
  /-- The kernel of d_r at bidegree k, viewed as a subobject of the page
      E_r^k = Z_n/B_n, equals the image of Z_{n+1} → Z_n → Z_n/B_n.
      Here n = (r - r₀).toNat.
      Mathematically: ker(d_r) at k = Z_{r+1}/B_r inside E_r^k.
      Only stated for r ≥ r₀ (where pages are meaningful). -/
  Z_succ : ∀ (r : ℤ) (k : ι) (_ : r₀ ≤ r),
    let n := (r - r₀).toNat
    kernelSubobject (d r k) =
      imageSubobject (Subobject.ofLE
        ((ssData k).Z ↑(n + 1)) ((ssData k).Z ↑n)
        ((ssData k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (ssData k).pageπ ↑n)
  /-- The image of d_r at bidegree k, viewed as a subobject of
      E_r^{k + diffDeg r} = Z_n/B_n at (k + diffDeg r), equals the image of
      B_{n+1} → Z_n → Z_n/B_n there.
      Here n = (r - r₀).toNat.
      Mathematically: im(d_r) at k + deg = B_{r+1}/B_r inside E_r^{k+deg}.
      Only stated for r ≥ r₀. -/
  B_succ : ∀ (r : ℤ) (k : ι) (_ : r₀ ≤ r),
    let n := (r - r₀).toNat
    imageSubobject (d r k) =
      imageSubobject (Subobject.ofLE
        ((ssData (k + diffDeg r)).B ↑(n + 1)) ((ssData (k + diffDeg r)).Z ↑n)
        (le_trans ((ssData (k + diffDeg r)).B_le_Z ↑(n + 1))
          ((ssData (k + diffDeg r)).Z_anti (by exact_mod_cast Nat.le_succ n))) ≫
        (ssData (k + diffDeg r)).pageπ ↑n)

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

/-! ### Third isomorphism theorem for subobjects (helper for pageHomologyIso) -/

/-- The canonical surjection `cokernel(P → R) ⟶ cokernel(Q → R)` when `P ≤ Q ≤ R`. -/
noncomputable def Subobject.cokernelDesc_ofLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R) (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P R hPR) ⟶ cokernel (Subobject.ofLE Q R hQR) :=
  cokernel.desc _ (cokernel.π (Subobject.ofLE Q R hQR)) (by
    have : Subobject.ofLE P R hPR = Subobject.ofLE P Q hPQ ≫ Subobject.ofLE Q R hQR :=
      (Subobject.ofLE_comp_ofLE P Q R hPQ hQR).symm
    rw [this, Category.assoc, cokernel.condition, comp_zero])

/-- The canonical injection `cokernel(P → Q) ⟶ cokernel(P → R)` when `P ≤ Q ≤ R`. -/
noncomputable def Subobject.cokernelMap_ofLE {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R) (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.ofLE P Q hPQ) ⟶ cokernel (Subobject.ofLE P R hPR) :=
  cokernel.desc _ (Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR)) (by
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE, cokernel.condition])

/-- Third isomorphism theorem for subobjects: `(R/P) / (Q/P) ≅ R/Q` when `P ≤ Q ≤ R`.
    Built using the abelian category structure. -/
noncomputable def Subobject.thirdIso {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R) (hPR : P ≤ R := le_trans hPQ hQR) :
    cokernel (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR) ≅
      cokernel (Subobject.ofLE Q R hQR) :=
  -- The surjection φ : R/P → R/Q has kernel Q/P, embedded via cokernelMap_ofLE.
  -- So cokernel(cokernelMap_ofLE) = cokernel(Q/P → R/P) ≅ R/Q.
  -- We build this via cokernel.desc on the surjection.
  { hom := cokernel.desc _ (Subobject.cokernelDesc_ofLE P Q R hPQ hQR hPR) (by
      -- cokernelMap_ofLE ≫ cokernelDesc_ofLE = 0
      -- cokernelMap_ofLE : Q/P → R/P
      -- cokernelDesc_ofLE : R/P → R/Q
      -- composition: Q/P → R/Q which sends q to class of q in R/Q = 0
      -- because Q ≤ R so q is in the kernel of R → R/Q.
      ext
      simp only [Subobject.cokernelMap_ofLE, Subobject.cokernelDesc_ofLE,
        cokernel.π_desc_assoc, comp_zero]
      rw [Category.assoc, cokernel.π_desc, cokernel.condition])
    inv := cokernel.desc _ (cokernel.π (Subobject.ofLE P R hPR) ≫
        cokernel.π (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR)) (by
      set f := Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR
      have h1 : cokernel.π (Subobject.ofLE P Q hPQ) ≫ f =
          Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) :=
        cokernel.π_desc _ _ _
      calc Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) ≫ cokernel.π f
          = (Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR)) ≫
              cokernel.π f := by rw [Category.assoc]
        _ = (cokernel.π (Subobject.ofLE P Q hPQ) ≫ f) ≫ cokernel.π f := by rw [h1]
        _ = cokernel.π (Subobject.ofLE P Q hPQ) ≫ (f ≫ cokernel.π f) := by
              rw [Category.assoc]
        _ = cokernel.π (Subobject.ofLE P Q hPQ) ≫ 0 := by rw [cokernel.condition]
        _ = 0 := comp_zero)
    hom_inv_id := by
      ext
      simp only [Category.comp_id, cokernel.π_desc,
        Subobject.cokernelDesc_ofLE, cokernel.π_desc_assoc]
    inv_hom_id := by
      ext
      simp only [Category.comp_id, Category.assoc, cokernel.π_desc_assoc,
        Subobject.cokernelDesc_ofLE, cokernel.π_desc] }

/-! ### Page short complex and homology isomorphism -/

/-- The short complex at page `r` centered at source index `k`:
    `E_r^k → E_r^{k + diffDeg r} → E_r^{k + 2 * diffDeg r}`
    with the zero condition from `d_comp_d`. -/
noncomputable def SpectralSequence.pageShortComplex
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) : ShortComplex C :=
  ShortComplex.mk (E.d r k) (E.d r (k + E.diffDeg r)) (E.d_comp_d r k)

open CategoryTheory.Abelian in
/-- `imageSubobject (e ≫ f) = imageSubobject f` when `e` is epi in an abelian category. -/
private lemma imageSubobject_epi_comp {X₁ X₂ X₃ : C} (e : X₁ ⟶ X₂) [Epi e] (f : X₂ ⟶ X₃) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
    (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm)

/-- `f ≫ g = 0` when `imageSubobject f ≤ kernelSubobject g`. -/
private lemma comp_eq_zero_of_image_le_kernel {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (h : imageSubobject f ≤ kernelSubobject g) : f ≫ g = 0 := by
  rw [← imageSubobject_arrow_comp f, Category.assoc,
    show (imageSubobject f).arrow = Subobject.ofLE _ _ h ≫ (kernelSubobject g).arrow
      from (Subobject.ofLE_arrow h).symm,
    Category.assoc, kernelSubobject_arrow_comp, comp_zero, comp_zero]

/-- Factorization: `ofLE Q R ≫ cokernel.π(P → R) = cokernel.π(P → Q) ≫ cokernelMap_ofLE`. -/
private lemma factor_cokernelMap {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R) (hPR : P ≤ R := le_trans hPQ hQR) :
    Subobject.ofLE Q R hQR ≫ cokernel.π (Subobject.ofLE P R hPR) =
    cokernel.π (Subobject.ofLE P Q hPQ) ≫ Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR := by
  simp [Subobject.cokernelMap_ofLE, cokernel.π_desc]

/-- `cokernelMap_ofLE P Q R : Q/P → R/P` is mono when `P ≤ Q ≤ R` in an abelian category.
    Proved by pseudoelement diagram chase. -/
private instance cokernelMap_ofLE_mono {V : C}
    (P Q R : Subobject V) (hPQ : P ≤ Q) (hQR : Q ≤ R)
    (hPR : P ≤ R := le_trans hPQ hQR) :
    Mono (Subobject.cokernelMap_ofLE P Q R hPQ hQR hPR) := by
  open CategoryTheory.Abelian.Pseudoelement in
  refine mono_of_zero_of_map_zero _ fun a ha => ?_
  obtain ⟨q, hq⟩ := pseudo_surjective_of_epi (cokernel.π (Subobject.ofLE P Q hPQ)) a
  rw [← hq] at ha ⊢
  -- ha : cokernelMap_ofLE(cokernel.π(P→Q)(q)) = 0
  -- Need: cokernel.π(P→R)(ofLE(Q,R)(q)) = 0
  have ha' : pseudoApply (cokernel.π (Subobject.ofLE P R hPR))
    (pseudoApply (Subobject.ofLE Q R hQR) q) = 0 := by
    have h1 := (Abelian.Pseudoelement.comp_apply
      (Subobject.ofLE Q R hQR) (cokernel.π (Subobject.ofLE P R hPR)) q).symm
    rw [h1, factor_cokernelMap P Q R hPQ hQR hPR, Abelian.Pseudoelement.comp_apply]; exact ha
  -- Build exactness of P →[ofLE] R →[cokernel.π] cokernel
  have hexact : (ShortComplex.mk (Subobject.ofLE P R hPR)
    (cokernel.π (Subobject.ofLE P R hPR)) (cokernel.condition _)).Exact :=
    ShortComplex.cokernelSequence_exact (Subobject.ofLE P R hPR)
  obtain ⟨p, hp⟩ := pseudo_exact_of_exact hexact _ ha'
  -- hp : pseudoApply (P.ofLE R hPR) p = pseudoApply (Q.ofLE R hQR) q
  have hp' : pseudoApply (Subobject.ofLE Q R hQR) (pseudoApply (Subobject.ofLE P Q hPQ) p) =
      pseudoApply (Subobject.ofLE Q R hQR) q := by
    rw [← Abelian.Pseudoelement.comp_apply, Subobject.ofLE_comp_ofLE]; exact hp
  have hinj := pseudo_injective_of_mono (Subobject.ofLE Q R hQR) hp'
  -- hinj : ofLE(P,Q)(p) = q. Goal: cokernel.π(P→Q)(q) = 0
  rw [← hinj, ← Abelian.Pseudoelement.comp_apply, cokernel.condition, zero_apply]

/-- Homology of (E_r, d_r) at index k is isomorphic to E_{r+1}^k.

    Informal proof sketch: `E_r = Z_r / B_r`. The differential `d_r` has
    kernel `Z_{r+1}/B_r` and image `B_{r+1}/B_r` (by definition of the nesting).
    So `H(E_r, d_r) = (Z_{r+1}/B_r) / (B_{r+1}/B_r) ≅ Z_{r+1}/B_{r+1} = E_{r+1}`
    by the third isomorphism theorem.

    The short complex is centered at source index `k - diffDeg r`, so the
    homology is at the middle term which is index `k`. -/
noncomputable def SpectralSequence.pageHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (r : ℤ) (k : ι) (hr : E.r₀ ≤ r) :
    E.Page (r + 1) k ≅ (E.pageShortComplex r (k - E.diffDeg r)).homology := by
  set n := (r - E.r₀).toNat with hn_def
  have hn1 : (r + 1 - E.r₀).toNat = n + 1 := by omega
  set S := E.pageShortComplex r (k - E.diffDeg r) with hS_def
  -- Work in D' = ssData(k - diffDeg r + diffDeg r); propositionally equal to ssData k
  set k' := k - E.diffDeg r + E.diffDeg r
  set D' := E.ssData k'
  have hk_eq : k' = k := sub_add_cancel k (E.diffDeg r)
  -- Order facts for D'
  have hBn_le_Bn1 : D'.B ↑n ≤ D'.B ↑(n + 1) := D'.B_mono (by exact_mod_cast Nat.le_succ n)
  have hBn1_le_Zn1 : D'.B ↑(n + 1) ≤ D'.Z ↑(n + 1) := D'.B_le_Z _
  have hZn1_le_Zn : D'.Z ↑(n + 1) ≤ D'.Z ↑n := D'.Z_anti (by exact_mod_cast Nat.le_succ n)
  have hBn_le_Zn1 : D'.B ↑n ≤ D'.Z ↑(n + 1) := le_trans hBn_le_Bn1 hBn1_le_Zn1
  -- Key morphisms for the LeftHomologyData
  -- i : Z_{n+1}/B_n → Z_n/B_n = S.X₂ (injection, the kernel of S.g)
  set i := Subobject.cokernelMap_ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) (D'.Z ↑n)
    hBn_le_Zn1 hZn1_le_Zn with hi_def
  -- π : Z_{n+1}/B_n → Z_{n+1}/B_{n+1} = D'.page(n+1) (surjection, the homology map)
  set π_map := Subobject.cokernelDesc_ofLE (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
    hBn_le_Bn1 hBn1_le_Zn1 with hπ_def
  -- (wi) i ≫ S.g = 0: the injection Z_{n+1}/B_n ↪ Z_n/B_n composed with d_r is zero.
  -- From Z_succ: kernelSubobject(d_r) = imageSubobject(ofLE(Z_{n+1},Z_n) ≫ pageπ).
  -- By factorization: that image equals imageSubobject(i) (epi ≫ i gives same image).
  -- So imageSubobject(i) = kernelSubobject(S.g), hence i ≫ S.g = 0.
  have wi : i ≫ S.g = 0 := by
    apply comp_eq_zero_of_image_le_kernel
    change imageSubobject i ≤ kernelSubobject (E.d r k')
    rw [E.Z_succ r k' hr,
      show Subobject.ofLE (D'.Z ↑(n + 1)) (D'.Z ↑n)
        (D'.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ D'.pageπ ↑n =
        cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1) ≫ i
        from factor_cokernelMap _ _ _ _ _,
      imageSubobject_epi_comp]
  -- (hi) i is the kernel of S.g, proved by transporting from kernelIsKernel via
  -- the subobject equality Subobject.mk i = kernelSubobject(S.g).
  have heq_sub : Subobject.mk i = Subobject.mk (kernel.ι (E.d r k')) := by
    change Subobject.mk i = kernelSubobject (E.d r k')
    rw [E.Z_succ r k' hr,
      show Subobject.ofLE (D'.Z ↑(n + 1)) (D'.Z ↑n)
        (D'.Z_anti (by exact_mod_cast Nat.le_succ n)) ≫ D'.pageπ ↑n =
        cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1) ≫ i
        from factor_cokernelMap _ _ _ _ _,
      imageSubobject_epi_comp, imageSubobject_mono]
  have hi : IsLimit (KernelFork.ofι i wi) := by
    apply (kernelIsKernel (E.d r k')).ofIsoLimit
    exact Fork.ext (Subobject.isoOfMkEqMk i (kernel.ι (E.d r k')) heq_sub).symm
      (Subobject.ofMkLEMk_comp heq_sub.ge)
  -- Shared infrastructure for wπ and hπ:
  -- j : B_{n+1}/B_n → Z_{n+1}/B_n is cokernelMap_ofLE(B_n, B_{n+1}, Z_{n+1})
  set j := Subobject.cokernelMap_ofLE (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
    hBn_le_Bn1 hBn1_le_Zn1 with hj_def
  set f_lift := hi.lift (KernelFork.ofι S.f (by exact S.zero)) with hf_lift_def
  -- j ≫ π_map = 0 by the third isomorphism theorem
  have hj_π : j ≫ π_map = 0 := by
    simp only [j, π_map, Subobject.cokernelMap_ofLE, Subobject.cokernelDesc_ofLE]
    ext
    simp only [cokernel.π_desc_assoc, cokernel.π_desc, comp_zero,
      Category.assoc, cokernel.condition]
  have hBn_le_Zn : D'.B ↑(n + 1) ≤ D'.Z ↑n := le_trans hBn1_le_Zn1 hZn1_le_Zn
  -- Factor ofLE(B_{n+1}, Z_n) ≫ pageπ n = cokernel.π(B_n→B_{n+1}) ≫ j ≫ i
  have hfactor : Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn ≫ D'.pageπ ↑n =
      cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.B ↑(n + 1)) hBn_le_Bn1) ≫ j ≫ i := by
    change Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn ≫
      cokernel.π (Subobject.ofLE (D'.B ↑n) (D'.Z ↑n) (D'.B_le_Z ↑n)) = _
    rw [(Subobject.ofLE_comp_ofLE (D'.B ↑(n + 1)) (D'.Z ↑(n + 1)) (D'.Z ↑n)
      hBn1_le_Zn1 hZn1_le_Zn).symm,
      Category.assoc,
      factor_cokernelMap (D'.B ↑n) (D'.Z ↑(n + 1)) (D'.Z ↑n) hBn_le_Zn1 hZn1_le_Zn,
      ← Category.assoc (Subobject.ofLE (D'.B ↑(n + 1)) (D'.Z ↑(n + 1)) hBn1_le_Zn1),
      factor_cokernelMap (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
        hBn_le_Bn1 hBn1_le_Zn1,
      Category.assoc]
  -- S.f = f_lift ≫ i (from kernel fork lift property)
  have hfi : f_lift ≫ i = S.f :=
    hi.fac (KernelFork.ofι S.f (by exact S.zero)) WalkingParallelPair.zero
  -- From B_succ: imageSubobject(S.f) = imageSubobject(ofLE(B_{n+1},Z_n) ≫ pageπ n)
  have hB := E.B_succ r (k - E.diffDeg r) hr
  -- imageSubobject(f_lift ≫ i) = imageSubobject(j ≫ i)
  have him : imageSubobject (f_lift ≫ i) = imageSubobject (j ≫ i) := by
    rw [hfi]; change imageSubobject (E.d r (k - E.diffDeg r)) = _
    rw [hB, hfactor, imageSubobject_epi_comp]
  -- imageSubobject(j ≫ i) = Subobject.mk(j ≫ i) since j ≫ i is mono
  have hjim : imageSubobject (j ≫ i) = Subobject.mk (j ≫ i) := imageSubobject_mono _
  have hle : imageSubobject (f_lift ≫ i) ≤ Subobject.mk (j ≫ i) := him ▸ hjim ▸ le_refl _
  have hfact_ji : (Subobject.mk (j ≫ i)).Factors (f_lift ≫ i) := by
    apply Subobject.factors_of_le _ hle
    have := imageSubobject_factors_comp_self (f := f_lift ≫ i) (𝟙 _)
    simpa using this
  -- Extract factoring map and show f_lift = (epi thing) ≫ j
  set φ_ji := (Subobject.mk (j ≫ i)).factorThru (f_lift ≫ i) hfact_ji
  have hφ_ji : φ_ji ≫ (Subobject.mk (j ≫ i)).arrow = f_lift ≫ i :=
    Subobject.factorThru_arrow _ _ _
  have harrow_ji : (Subobject.mk (j ≫ i)).arrow =
      (Subobject.underlyingIso (j ≫ i)).hom ≫ (j ≫ i) :=
    (Subobject.underlyingIso_hom_comp_eq_mk (j ≫ i)).symm
  -- ψ ≫ j = f_lift where ψ = φ_ji ≫ underlyingIso.hom
  set ψ := φ_ji ≫ (Subobject.underlyingIso (j ≫ i)).hom with hψ_def
  have hψ_j : ψ ≫ j = f_lift := by
    apply (cancel_mono i).mp
    rw [Category.assoc]
    change ψ ≫ (j ≫ i) = f_lift ≫ i
    change (φ_ji ≫ (Subobject.underlyingIso (j ≫ i)).hom) ≫ (j ≫ i) = f_lift ≫ i
    rw [Category.assoc, ← harrow_ji, hφ_ji]
  -- (wπ) f_lift ≫ π_map = 0
  have wπ : f_lift ≫ π_map = 0 := by
    calc f_lift ≫ π_map
        = (ψ ≫ j) ≫ π_map := by rw [hψ_j]
      _ = ψ ≫ (j ≫ π_map) := by rw [Category.assoc]
      _ = ψ ≫ 0 := by rw [hj_π]
      _ = 0 := comp_zero
  -- (hπ) π_map is the cokernel of f_lift.
  -- Key: ψ factors f_lift through j. For any g with f_lift ≫ g = 0,
  -- we get j ≫ g = 0 (since ψ is epi-ish enough), then use cokernel of j.
  -- Actually: we use factorThruImageSubobject to get the epi factor.
  have hπ : IsColimit (CokernelCofork.ofπ π_map wπ) := by
    -- Strategy: ψ is epi and f_lift = ψ ≫ j, so cokernel(f_lift) ≅ cokernel(j).
    -- Then π_map = cokernel.π(j) ≫ thirdIso.hom gives the cokernel of f_lift.
    -- Step 1: Prove ψ is epi.
    have hφ_eq : φ_ji = factorThruImageSubobject (f_lift ≫ i) ≫
        (Subobject.isoOfEq _ _ (him.trans hjim)).hom := by
      apply (cancel_mono (Subobject.mk (j ≫ i)).arrow).mp
      rw [hφ_ji, Category.assoc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow,
        imageSubobject_arrow_comp]
    have hψ_epi : Epi ψ := by
      rw [hψ_def, hφ_eq, Category.assoc]
      exact epi_comp _ _
    -- Key: cokernel.π(j) ≫ thirdIso.hom = π_map
    have hπ_factor : cokernel.π j ≫
        (Subobject.thirdIso (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
          hBn_le_Bn1 hBn1_le_Zn1).hom = π_map :=
      cokernel.π_desc _ _ _
    set thirdIso := Subobject.thirdIso (D'.B ↑n) (D'.B ↑(n + 1)) (D'.Z ↑(n + 1))
      hBn_le_Bn1 hBn1_le_Zn1 with hthirdIso_def
    -- For any cofork s with f_lift ≫ s.π = 0 ≫ s.π, we have j ≫ s.π = 0
    have hjs : ∀ (s : Cofork f_lift 0), j ≫ Cofork.π s = 0 := by
      intro s
      haveI := hψ_epi
      apply zero_of_epi_comp ψ
      rw [← Category.assoc, hψ_j]
      have := s.condition  -- f_lift ≫ s.π = 0 ≫ s.π
      simp only [zero_comp] at this
      exact this
    -- Step 2: Build the colimit using Cofork.IsColimit.mk
    exact Cofork.IsColimit.mk _
      (fun s => thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s))
      (fun s => by
        -- Need: π_map ≫ (thirdIso.inv ≫ cokernel.desc j (s.π) _) = s.π
        change π_map ≫ thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s) = Cofork.π s
        rw [show π_map = cokernel.π j ≫ thirdIso.hom from hπ_factor.symm,
          Category.assoc, thirdIso.hom_inv_id_assoc, cokernel.π_desc])
      (fun s m hm => by
        -- Need: m = thirdIso.inv ≫ cokernel.desc j (s.π) _
        change m = thirdIso.inv ≫ cokernel.desc j (Cofork.π s) (hjs s)
        rw [← cancel_epi thirdIso.hom, thirdIso.hom_inv_id_assoc]
        -- Goal: thirdIso.hom ≫ m = cokernel.desc j (s.π) _
        apply (cancel_epi (cokernel.π j)).mp
        rw [cokernel.π_desc, ← Category.assoc, hπ_factor]
        exact hm)
  -- Assemble the LeftHomologyData
  set h : S.LeftHomologyData := {
    K := cokernel (Subobject.ofLE (D'.B ↑n) (D'.Z ↑(n + 1)) hBn_le_Zn1)
    H := D'.page ↑(n + 1)
    i := i
    π := π_map
    wi := wi
    hi := hi
    wπ := wπ
    hπ := hπ
  }
  -- The LHS equals h.H via transport: E.Page (r+1) k = D.page ↑(n+1) = D'.page ↑(n+1) = h.H
  have hPageH : E.Page (r + 1) k = h.H := by
    change (E.ssData k).page ↑((r + 1 - E.r₀).toNat) = D'.page ↑(n + 1)
    rw [hn1]; congr 1; exact hk_eq.symm ▸ rfl
  exact eqToIso hPageH ≪≫ h.homologyIso.symm

/-! ### E∞-page -/

/-- If all pages `E_r^k = 0` for `r ≥ r₀`, then `E∞^k = 0`.

    Proof: `E_r = Z_r/B_r = 0` for all `r ≥ r₀` means `Z_r = B_r` (since the
    cokernel of the inclusion `B_r ↪ Z_r` vanishes iff the inclusion is epi,
    which in an abelian category means `B_r = Z_r`).
    Since `Z ⊤ ≤ Z_r = B_r ≤ B ⊤` for all r, and `B ⊤ ≤ Z ⊤` (from `B_le_Z`
    at ⊤), we get `Z ⊤ = B ⊤`, hence `E∞ = Z⊤/B⊤ = 0`. -/
theorem SpectralSequence.eInfty_isZero_of_page_isZero
    {C : Type*} [Category C] [Abelian C]
    {α : Type*} [AddCommGroup α] [DecidableEq α]
    (E : SpectralSequence C α) (k : α)
    (h : ∀ r : ℤ, E.r₀ ≤ r → IsZero (E.Page r k)) :
    IsZero ((E.ssData k).eInfty) := by
  unfold SSData.eInfty
  apply SSData.page_isZero_of_eq
  set D := E.ssData k
  apply le_antisymm
  · exact D.B_le_Z ⊤
  · have hpage0 : IsZero (D.page (↑(0 : ℕ))) := by
      have := h E.r₀ (le_refl _)
      simp only [SpectralSequence.Page, SSData.page] at this
      have hrr : (E.r₀ - E.r₀).toNat = 0 := by omega
      rw [hrr] at this
      exact this
    have hBZ : D.B ↑(0 : ℕ) = D.Z ↑(0 : ℕ) := D.eq_of_page_isZero _ hpage0
    calc D.Z ⊤ ≤ D.Z ↑(0 : ℕ) := D.Z_anti le_top
      _ = D.B ↑(0 : ℕ) := hBZ.symm
      _ ≤ D.B ⊤ := D.B_mono le_top

/-- A spectral sequence degenerates at page `N` if all differentials
    d_r = 0 for r ≥ N. -/
def SpectralSequence.DegeneratesAt
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : SpectralSequence C ι) (N : ℤ) : Prop :=
  ∀ (r : ℤ), N ≤ r → ∀ (k : ι), E.d r k = 0

/-! ### Morphisms of spectral sequences -/

/-- A morphism of spectral sequences is a family of maps on the underlying
    objects `V` at each bidegree, preserving the cycles `Z_r`, boundaries `B_r`,
    and commuting with differentials. -/
structure SpectralSequenceMorphism
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E E' : SpectralSequence C ι) where
  /-- The map on underlying objects at each bidegree -/
  φ : ∀ (k : ι), (E.ssData k).V ⟶ (E'.ssData k).V
  /-- φ preserves Z_r: maps Z_r(E) into Z_r(E') -/
  preserves_Z : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((E.ssData k).Z r) ⟶
              Subobject.underlying.obj ((E'.ssData k).Z r)),
      lift ≫ ((E'.ssData k).Z r).arrow = ((E.ssData k).Z r).arrow ≫ φ k
  /-- φ preserves B_r: maps B_r(E) into B_r(E') -/
  preserves_B : ∀ (k : ι) (r : WithTop ℕ),
    ∃ (lift : Subobject.underlying.obj ((E.ssData k).B r) ⟶
              Subobject.underlying.obj ((E'.ssData k).B r)),
      lift ≫ ((E'.ssData k).B r).arrow = ((E.ssData k).B r).arrow ≫ φ k
  /-- φ commutes with differentials: the induced maps on pages commute
      with the differentials d_r. -/
  comm_d : ∀ (r : ℤ) (k : ι),
    ∃ (f_page_k : E.Page r k ⟶ E'.Page r k)
      (f_page_kd : E.Page r (k + E.diffDeg r) ⟶ E'.Page r (k + E'.diffDeg r)),
      f_page_k ≫ E'.d r k = E.d r k ≫ f_page_kd

/-- A spectral sequence morphism induces maps on E∞ pages via `cokernel.map`. -/
noncomputable def SpectralSequenceMorphism.eInftyMap
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    {E E' : SpectralSequence C ι} (f : SpectralSequenceMorphism E E') (k : ι) :
    (E.ssData k).eInfty ⟶ (E'.ssData k).eInfty := by
  unfold SSData.eInfty SSData.page
  exact cokernel.map
    (Subobject.ofLE ((E.ssData k).B ⊤) ((E.ssData k).Z ⊤) ((E.ssData k).B_le_Z ⊤))
    (Subobject.ofLE ((E'.ssData k).B ⊤) ((E'.ssData k).Z ⊤) ((E'.ssData k).B_le_Z ⊤))
    (f.preserves_B k ⊤).choose
    (f.preserves_Z k ⊤).choose
    (by
      have hB := (f.preserves_B k ⊤).choose_spec
      have hZ := (f.preserves_Z k ⊤).choose_spec
      apply (cancel_mono ((E'.ssData k).Z ⊤).arrow).mp
      simp only [Category.assoc, hZ, Subobject.ofLE_arrow, hB, Subobject.ofLE_arrow_assoc])

end KIP.SpectralSequence
