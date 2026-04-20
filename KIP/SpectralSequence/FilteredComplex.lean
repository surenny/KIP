/-
  KIP.SpectralSequence.FilteredComplex
  Construction of a spectral sequence from a filtered chain complex

  Blueprint: references/filtered谱序列.tex (Wang Guozhen's spectral sequence notes)
  Informal:  informal/filtered_complex.md

  Constructs a spectral sequence from a filtered chain complex and states
  weak convergence to the homology. All filtrations are decreasing.
  The spectral sequence starts at page E_0.
-/
import Mathlib
import KIP.SpectralSequence.Basic
import KIP.SpectralSequence.Convergence

namespace KIP.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v w

set_option linter.dupNamespace false

variable {C : Type u} [Category.{v} C] [Abelian C]

/-! ### Filtered chain complex -/

/-- A filtered chain complex in an abelian category `C`.
    This is a graded object `A : ℤ → C` equipped with a differential `d` of
    degree `-1` satisfying `d² = 0`, together with a decreasing filtration
    preserved by `d`.

    We use a self-contained definition rather than Mathlib's `ChainComplex`,
    following the convention in `Basic.lean`. -/
structure FilteredComplex (C : Type u) [Category.{v} C] [Abelian C] where
  /-- The underlying graded object (degree `k`). -/
  A : ℤ → C
  /-- The differential `d k : A k ⟶ A (k - 1)`. -/
  d : (k : ℤ) → A k ⟶ A (k - 1)
  /-- d² = 0: the composite `A k → A (k-1) → A (k-2)` is zero. -/
  d_comp_d : ∀ k, d k ≫ d (k - 1) = 0
  /-- Decreasing filtration: `fil s k` is the subobject `F^s A^k ≤ A^k`. -/
  fil : ℤ → (k : ℤ) → Subobject (A k)
  /-- Filtration is decreasing: `F^{s+1} ≤ F^s`. -/
  fil_anti : ∀ s k, fil (s + 1) k ≤ fil s k
  /-- `d` preserves the filtration: `d` maps `F^s A^k` into `F^s A^{k-1}`. -/
  d_preserves_fil : ∀ s k,
    ∃ (φ : Subobject.underlying.obj (fil s k) ⟶
           Subobject.underlying.obj (fil s (k - 1))),
      φ ≫ (fil s (k - 1)).arrow = (fil s k).arrow ≫ d k

/-! ### Boundedness -/

/-- A filtered complex has a **bounded** filtration if for each degree `k`,
    there exist bounds `lo k ≤ hi k` such that `F^s = ⊤` for `s ≤ lo k`
    (bounded below) and `F^s = ⊥` for `s ≥ hi k` (bounded above).

    This mirrors `Filtration.IsBounded` in `Convergence.lean`. -/
structure FilteredComplex.IsBounded (FC : FilteredComplex C) where
  /-- Lower bound: for `s ≤ lo k`, the filtration is everything. -/
  lo : ℤ → ℤ
  /-- Upper bound: for `s ≥ hi k`, the filtration is trivial. -/
  hi : ℤ → ℤ
  /-- `lo ≤ hi`. -/
  lo_le_hi : ∀ k, lo k ≤ hi k
  /-- `F^s A^k = A^k` for `s ≤ lo k` (bounded below). -/
  boundedBelow : ∀ k s, s ≤ lo k → FC.fil s k = ⊤
  /-- `F^s A^k = 0` for `s ≥ hi k` (bounded above). -/
  boundedAbove : ∀ k s, hi k ≤ s → FC.fil s k = ⊥

/-! ### Associated graded -/

/-- The associated graded `gr^s A^k = F^s A^k / F^{s+1} A^k`, defined as the
    cokernel of the inclusion `F^{s+1} ↪ F^s`.
    Parallels `Filtration.associatedGraded` in `Convergence.lean:63`. -/
noncomputable def FilteredComplex.assocGraded (FC : FilteredComplex C)
    (s k : ℤ) : C :=
  cokernel (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k))

/-- The induced differential on the associated graded:
    `gr^s A^k → gr^s A^{k-1}`.
    This exists because `d` maps `F^s` into `F^s` and `F^{s+1}` into `F^{s+1}`.
    The construction uses `cokernel.desc`. -/
noncomputable def FilteredComplex.assocGradedDiff (FC : FilteredComplex C)
    (s k : ℤ) : FC.assocGraded s k ⟶ FC.assocGraded s (k - 1) := by
  unfold FilteredComplex.assocGraded
  exact cokernel.desc _
    ((FC.d_preserves_fil s k).choose ≫
      cokernel.π (Subobject.ofLE (FC.fil (s + 1) (k - 1))
        (FC.fil s (k - 1)) (FC.fil_anti s (k - 1))))
    (by
      have factor : Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k) ≫
          (FC.d_preserves_fil s k).choose =
          (FC.d_preserves_fil (s + 1) k).choose ≫
          Subobject.ofLE (FC.fil (s + 1) (k - 1)) (FC.fil s (k - 1))
            (FC.fil_anti s (k - 1)) := by
        have mono_arrow : Mono (FC.fil s (k - 1)).arrow := inferInstance
        have lhs_eq : (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k) ≫
          (FC.d_preserves_fil s k).choose) ≫ (FC.fil s (k - 1)).arrow =
          (FC.fil (s + 1) k).arrow ≫ FC.d k := by
          rw [Category.assoc, (FC.d_preserves_fil s k).choose_spec,
            ← Category.assoc, Subobject.ofLE_arrow]
        have rhs_eq : ((FC.d_preserves_fil (s + 1) k).choose ≫
          Subobject.ofLE (FC.fil (s + 1) (k - 1)) (FC.fil s (k - 1))
            (FC.fil_anti s (k - 1))) ≫ (FC.fil s (k - 1)).arrow =
          (FC.fil (s + 1) k).arrow ≫ FC.d k := by
          rw [Category.assoc, Subobject.ofLE_arrow,
            (FC.d_preserves_fil (s + 1) k).choose_spec]
        exact mono_arrow.right_cancellation _ _ (lhs_eq.trans rhs_eq.symm)
      rw [← Category.assoc, factor, Category.assoc, cokernel.condition, comp_zero])

/-- The induced differential on the associated graded squares to zero:
    `assocGradedDiff ≫ assocGradedDiff = 0`. -/
theorem FilteredComplex.assocGradedDiff_sq (FC : FilteredComplex C)
    (s k : ℤ) : FC.assocGradedDiff s k ≫ FC.assocGradedDiff s (k - 1) = 0 := by
  unfold FilteredComplex.assocGradedDiff FilteredComplex.assocGraded
  apply (cancel_epi (cokernel.π (Subobject.ofLE (FC.fil (s + 1) k)
    (FC.fil s k) (FC.fil_anti s k)))).mp
  simp only [comp_zero, id_eq]
  rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc]
  suffices h : (FC.d_preserves_fil s k).choose ≫ (FC.d_preserves_fil s (k - 1)).choose = 0 by
    rw [← Category.assoc, h, zero_comp]
  have mono_arrow : Mono (FC.fil s (k - 1 - 1)).arrow := inferInstance
  apply mono_arrow.right_cancellation
  rw [zero_comp, Category.assoc, (FC.d_preserves_fil s (k - 1)).choose_spec,
    ← Category.assoc, (FC.d_preserves_fil s k).choose_spec, Category.assoc,
    FC.d_comp_d, comp_zero]

/-! ### Induced filtration on homology -/

/-- The homology graded object `H_k(A)` of the underlying complex.
    `H_k(A) = ker(d_k) / im(d_{k+1})`. Deferred. -/
noncomputable def FilteredComplex.homologyObj (FC : FilteredComplex C)
    (k : ℤ) : C :=
  (ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1)) (FC.d_comp_d (k + 1))).homology

/-- The induced filtration on homology: `F^s H_k(A)` is the image of
    `(F^s A^k ∩ ker d_k)` in `H_k(A)`. Produces a `Filtration` on the
    homology graded object. -/
noncomputable def FilteredComplex.homologyFiltration (FC : FilteredComplex C) :
    Filtration FC.homologyObj where
  F := fun s k =>
    let S := ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1))
              (FC.d_comp_d (k + 1))
    let I := kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1)
    let h_zero : I.arrow ≫ S.g = 0 := by
      rw [show I.arrow = Subobject.ofLE I (kernelSubobject S.g)
          inf_le_left ≫ (kernelSubobject S.g).arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    imageSubobject (S.liftCycles I.arrow h_zero ≫ S.homologyπ)
  mono := fun s k => by
    -- F^{s+1} H_k ≤ F^s H_k because fil (s+1) ≤ fil s
    dsimp only []
    set S := ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1)) (FC.d_comp_d (k + 1))
    set I1 := kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1)
    set I0 := kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1)
    have hle : I1 ≤ I0 := inf_le_inf_left _ (FC.fil_anti s (k + 1 - 1))
    have h_zero_1 : I1.arrow ≫ S.g = 0 := by
      rw [show I1.arrow = Subobject.ofLE I1 (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have h_zero_0 : I0.arrow ≫ S.g = 0 := by
      rw [show I0.arrow = Subobject.ofLE I0 (kernelSubobject S.g) inf_le_left ≫
        (kernelSubobject S.g).arrow from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    have hlift : S.liftCycles I1.arrow h_zero_1 =
        Subobject.ofLE I1 I0 hle ≫ S.liftCycles I0.arrow h_zero_0 := by
      apply (cancel_mono S.iCycles).mp
      rw [S.liftCycles_i, Category.assoc, S.liftCycles_i]
      exact (Subobject.ofLE_arrow hle).symm
    have hlift2 : S.liftCycles I1.arrow h_zero_1 ≫ S.homologyπ =
        Subobject.ofLE I1 I0 hle ≫ (S.liftCycles I0.arrow h_zero_0 ≫ S.homologyπ) := by
      rw [← Category.assoc, hlift]
    conv_lhs => rw [show S.liftCycles I1.arrow _ ≫ S.homologyπ =
      Subobject.ofLE I1 I0 hle ≫ (S.liftCycles I0.arrow _ ≫ S.homologyπ) from hlift2]
    exact imageSubobject_comp_le _ _

/-! ### Filtration general antitonicity -/

/-- The filtration is antitone in `s` for each `k`: if `a ≤ b` then `F^b ≤ F^a`. -/
theorem FilteredComplex.fil_anti_of_le (FC : FilteredComplex C) {a b : ℤ} (k : ℤ)
    (hab : a ≤ b) : FC.fil b k ≤ FC.fil a k := by
  suffices ∀ (n : ℕ), FC.fil (a + ↑n) k ≤ FC.fil a k by
    obtain ⟨n, rfl⟩ := Int.le.dest hab
    exact this n
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have key : FC.fil (a + ↑(n + 1)) k ≤ FC.fil (a + ↑n) k := by
      have h1 : a + ↑(n + 1) = (a + ↑n) + 1 := by omega
      rw [h1]
      exact FC.fil_anti (a + ↑n) k
    exact le_trans key ih

/-! ### Degree transport helper -/

/-- The differential d(k+1) transported to land at degree k instead of (k+1)-1.
    Uses eqToHom to bridge the non-definitional equality (k+1)-1 = k in ℤ. -/
noncomputable def FilteredComplex.dToK (FC : FilteredComplex C)
    (k : ℤ) : FC.A (k + 1) ⟶ FC.A k :=
  FC.d (k + 1) ≫ eqToHom (congr_arg FC.A (show (k + 1) - 1 = k by omega))

/-! ### Cycle and boundary subobjects -/

/-- The r-cycle subobject Z_r of V = gr^s A^k.
    Z_r = image in V of { x ∈ F^s A^k | dx ∈ F^{s+r} A^{k-1} }.
    For r = ⊤, the condition is dx = 0 (i.e., x ∈ ker d). -/
noncomputable def FilteredComplex.cycleSubobject (FC : FilteredComplex C)
    (s k : ℤ) (r : WithTop ℕ) : Subobject (FC.assocGraded s k) :=
  let ι := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
  let πV := cokernel.π ι
  match r with
  | ⊤ =>
    let f := (FC.fil s k).arrow ≫ FC.d k
    imageSubobject ((kernelSubobject f).arrow ≫ πV)
  | (n : ℕ) =>
    let f := (FC.fil s k).arrow ≫ FC.d k ≫
      cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow)
    imageSubobject ((kernelSubobject f).arrow ≫ πV)

/-- The r-boundary subobject B_r of V = gr^s A^k.
    B_r = image in V of { dz | z ∈ F^{s-r} A^{k+1}, dz ∈ F^s A^k }.
    For r = ⊤, the source is all of A^{k+1}. For r = n, it is F^{s-n} A^{k+1}.
    We intersect the image of d with F^s, then project to V. -/
noncomputable def FilteredComplex.boundarySubobject (FC : FilteredComplex C)
    (s k : ℤ) (r : WithTop ℕ) : Subobject (FC.assocGraded s k) :=
  let ι := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
              (FC.fil_anti s k)
  let πV := cokernel.π ι
  match r with
  | ⊤ =>
    let imgD := imageSubobject (FC.dToK k)
    let I := imgD ⊓ FC.fil s k
    imageSubobject (Subobject.ofLE I (FC.fil s k) inf_le_right ≫ πV)
  | (n : ℕ) =>
    let imgD := imageSubobject
                  ((FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k)
    let I := imgD ⊓ FC.fil s k
    imageSubobject (Subobject.ofLE I (FC.fil s k) inf_le_right ≫ πV)

/-! ### SSData from a filtered complex -/

/-- `dToK k ≫ d k = 0`: the transported differential squares to zero. -/
theorem FilteredComplex.dToK_comp_d (FC : FilteredComplex C) (k : ℤ) :
    FC.dToK k ≫ FC.d k = 0 := by
  unfold FilteredComplex.dToK
  have heq : (k + 1) - 1 = k := by omega
  rw [Category.assoc,
    show eqToHom (congr_arg FC.A heq) ≫ FC.d k =
      FC.d ((k + 1) - 1) ≫ eqToHom (congr_arg FC.A
        (show (k + 1) - 1 - 1 = k - 1 by omega))
    from by simp [heq]]
  rw [← Category.assoc, FC.d_comp_d, zero_comp]

set_option maxHeartbeats 800000 in
-- Large case split on WithTop ℕ with deep subobject reasoning
/-- B r ≤ Z r for the filtered complex: boundaries are cycles. -/
theorem FilteredComplex.B_le_Z_aux (FC : FilteredComplex C) (s k : ℤ)
    (r : WithTop ℕ) :
    FC.boundarySubobject s k r ≤ FC.cycleSubobject s k r := by
  rcases r with _ | n
  · -- r = ⊤
    simp only [FilteredComplex.boundarySubobject,
      FilteredComplex.cycleSubobject]
    let ι := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
      (FC.fil_anti s k)
    let πV := cokernel.π ι
    let imgD := imageSubobject (FC.dToK k)
    let I := imgD ⊓ FC.fil s k
    let oI := Subobject.ofLE I (FC.fil s k) inf_le_right
    let f := (FC.fil s k).arrow ≫ FC.d k
    have h_zero : oI ≫ f = 0 := by
      change Subobject.ofLE I (FC.fil s k) inf_le_right ≫
        (FC.fil s k).arrow ≫ FC.d k = 0
      rw [← Category.assoc, Subobject.ofLE_arrow]
      rw [show I.arrow =
          Subobject.ofLE I imgD inf_le_left ≫ imgD.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm,
        Category.assoc]
      have : imgD.arrow ≫ FC.d k = 0 := by
        rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
        rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
        exact FC.dToK_comp_d k
      rw [this, comp_zero]
    have heq : oI ≫ πV = factorThruKernelSubobject f oI h_zero ≫
        (kernelSubobject f).arrow ≫ πV := by
      rw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
    calc imageSubobject (oI ≫ πV)
        = imageSubobject (factorThruKernelSubobject f oI h_zero ≫
            (kernelSubobject f).arrow ≫ πV) := by rw [heq]
      _ ≤ imageSubobject ((kernelSubobject f).arrow ≫ πV) :=
          imageSubobject_comp_le _ _
  · -- r = ↑n
    simp only [FilteredComplex.boundarySubobject,
      FilteredComplex.cycleSubobject]
    let ι := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k)
      (FC.fil_anti s k)
    let πV := cokernel.π ι
    let imgD := imageSubobject
      ((FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k)
    let I := imgD ⊓ FC.fil s k
    let oI := Subobject.ofLE I (FC.fil s k) inf_le_right
    let f := (FC.fil s k).arrow ≫ FC.d k ≫
      cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow)
    have h_zero : oI ≫ f = 0 := by
      change Subobject.ofLE I (FC.fil s k) inf_le_right ≫
        ((FC.fil s k).arrow ≫ FC.d k ≫
          cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow)) = 0
      simp only [← Category.assoc]
      rw [Subobject.ofLE_arrow]
      rw [show I.arrow =
          Subobject.ofLE I imgD inf_le_left ≫ imgD.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      simp only [Category.assoc]
      have hd : imgD.arrow ≫ FC.d k = 0 := by
        rw [← cancel_epi (factorThruImageSubobject
          ((FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k))]
        rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp,
          Category.assoc, FC.dToK_comp_d, comp_zero]
      rw [show imgD.arrow ≫ FC.d k ≫ cokernel.π _ =
        (imgD.arrow ≫ FC.d k) ≫ cokernel.π _
        from (Category.assoc _ _ _).symm,
        hd, zero_comp, comp_zero]
    have heq : oI ≫ πV = factorThruKernelSubobject f oI h_zero ≫
        (kernelSubobject f).arrow ≫ πV := by
      rw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
    calc imageSubobject (oI ≫ πV)
        = imageSubobject (factorThruKernelSubobject f oI h_zero ≫
            (kernelSubobject f).arrow ≫ πV) := by rw [heq]
      _ ≤ imageSubobject ((kernelSubobject f).arrow ≫ πV) :=
          imageSubobject_comp_le _ _

set_option maxHeartbeats 800000 in
-- Complex SSData construction with multiple WithTop ℕ case analyses
/-- Constructs `SSData C` from a filtered complex at bidegree `(s, k)`.
    - `V` is the associated graded `gr^s A^k = F^s / F^{s+1}`.
    - `Z r` are the `r`-cycles (as subobjects of `V`), deferred.
    - `B r` are the `r`-boundaries (as subobjects of `V`), deferred.
    All proof obligations are deferred. -/
noncomputable def FilteredComplex.toSSData (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) : SSData C where
  V := FC.assocGraded s k
  Z := FC.cycleSubobject s k
  B := FC.boundarySubobject s k
  Z_anti := by
    intro r₁ r₂ hr₁₂
    -- Auxiliary: if K₂ ≤ K₁ as subobjects, then
    -- imageSubobject(K₂.arrow ≫ g) ≤ imageSubobject(K₁.arrow ≫ g)
    suffices key : ∀ {X Y : C} {K₁ K₂ : Subobject X} (g : X ⟶ Y)
        (hle : K₂ ≤ K₁),
        imageSubobject (K₂.arrow ≫ g) ≤ imageSubobject (K₁.arrow ≫ g) by
      -- Case split on r₁, r₂ : WithTop ℕ
      rcases r₁ with _ | n₁ <;> rcases r₂ with _ | n₂
      · -- (⊤, ⊤)
        exact le_refl _
      · -- (⊤, ↑n₂): impossible
        exact absurd hr₁₂ (WithTop.not_top_le_coe n₂)
      · -- (↑n₁, ⊤): ker(arrow ≫ d) ≤ ker(arrow ≫ d ≫ cokernel.π)
        change imageSubobject
            ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k)).arrow ≫ _) ≤
          imageSubobject
            ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
              cokernel.π ((FC.fil (s + ↑n₁) (k - 1)).arrow))).arrow ≫ _)
        apply key
        apply le_kernelSubobject
        -- Goal: (kernelSubobject (arrow ≫ d)).arrow ≫ (arrow ≫ d ≫ cokernel.π) = 0
        have h1 : (kernelSubobject ((FC.fil s k).arrow ≫ FC.d k)).arrow ≫
            ((FC.fil s k).arrow ≫ FC.d k) = 0 := kernelSubobject_arrow_comp _
        calc (kernelSubobject ((FC.fil s k).arrow ≫ FC.d k)).arrow ≫
                ((FC.fil s k).arrow ≫ (FC.d k ≫
                  cokernel.π ((FC.fil (s + ↑n₁) (k - 1)).arrow)))
            = ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k)).arrow ≫
                (FC.fil s k).arrow ≫ FC.d k) ≫
                cokernel.π ((FC.fil (s + ↑n₁) (k - 1)).arrow) := by
                simp only [Category.assoc]
          _ = 0 ≫ cokernel.π ((FC.fil (s + ↑n₁) (k - 1)).arrow) := by rw [h1]
          _ = 0 := zero_comp
      · -- (↑n₁, ↑n₂): n₁ ≤ n₂
        change imageSubobject
            ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
              cokernel.π ((FC.fil (s + ↑n₂) (k - 1)).arrow))).arrow ≫ _) ≤
          imageSubobject
            ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
              cokernel.π ((FC.fil (s + ↑n₁) (k - 1)).arrow))).arrow ≫ _)
        have hn : n₁ ≤ n₂ := WithTop.coe_le_coe.mp hr₁₂
        have hfil : FC.fil (s + ↑n₂) (k - 1) ≤ FC.fil (s + ↑n₁) (k - 1) :=
          FC.fil_anti_of_le (k - 1) (by omega)
        have hcomp : (FC.fil (s + ↑n₂) (k - 1)).arrow ≫
            cokernel.π ((FC.fil (s + ↑n₁) (k - 1)).arrow) = 0 := by
          rw [show (FC.fil (s + ↑n₂) (k - 1)).arrow =
            Subobject.ofLE _ _ hfil ≫ (FC.fil (s + ↑n₁) (k - 1)).arrow
            from (Subobject.ofLE_arrow hfil).symm]
          rw [Category.assoc, cokernel.condition, comp_zero]
        -- Show ker(f_n₂) ≤ ker(f_n₁) via le_kernelSubobject
        set f_n₂ := (FC.fil s k).arrow ≫ FC.d k ≫
          cokernel.π ((FC.fil (s + ↑n₂) (k - 1)).arrow) with hf_n₂_def
        set f_n₁ := (FC.fil s k).arrow ≫ FC.d k ≫
          cokernel.π ((FC.fil (s + ↑n₁) (k - 1)).arrow) with hf_n₁_def
        have hker : kernelSubobject f_n₂ ≤ kernelSubobject f_n₁ := by
          apply le_kernelSubobject
          -- Goal: (kernelSubobject f_n₂).arrow ≫ f_n₁ = 0
          -- Construct the cokernel descent map
          set desc := cokernel.desc ((FC.fil (s + ↑n₂) (k - 1)).arrow)
            (cokernel.π ((FC.fil (s + ↑n₁) (k - 1)).arrow)) hcomp
          -- f_n₁ = f_n₂ ≫ desc
          have hfactor : f_n₁ = f_n₂ ≫ desc := by
            simp only [f_n₂, f_n₁, desc, Category.assoc, cokernel.π_desc]
          rw [hfactor, ← Category.assoc, kernelSubobject_arrow_comp, zero_comp]
        exact key _ hker
    -- Proof of the auxiliary lemma
    intro X Y K₁ K₂ g hle
    rw [show K₂.arrow ≫ g = Subobject.ofLE K₂ K₁ hle ≫ K₁.arrow ≫ g by
      rw [← Category.assoc, Subobject.ofLE_arrow]]
    exact imageSubobject_comp_le _ _
  B_mono := by
    intro r₁ r₂ hr₁₂
    -- Auxiliary: K₁ ≤ K₂ → image(K₁.arrow ≫ g) ≤ image(K₂.arrow ≫ g)
    suffices img_mono : ∀ {X Y : C} {K₁ K₂ : Subobject X} (g : X ⟶ Y)
        (hle : K₁ ≤ K₂),
        imageSubobject (K₁.arrow ≫ g) ≤ imageSubobject (K₂.arrow ≫ g) by
      -- Also: I₁ ≤ I₂ ≤ Q → image(ofLE I₁ Q ≫ g) ≤ image(ofLE I₂ Q ≫ g)
      have ofLE_mono : ∀ {X Y : C} {I₁ I₂ Q : Subobject X}
          (h₁ : I₁ ≤ Q) (h₂ : I₂ ≤ Q) (hle : I₁ ≤ I₂)
          (g : Subobject.underlying.obj Q ⟶ Y),
          imageSubobject (Subobject.ofLE I₁ Q h₁ ≫ g) ≤
          imageSubobject (Subobject.ofLE I₂ Q h₂ ≫ g) := by
        intro X Y I₁ I₂ Q h₁ h₂ hle g
        have factored : Subobject.ofLE I₁ Q h₁ =
            Subobject.ofLE I₁ I₂ hle ≫ Subobject.ofLE I₂ Q h₂ := by
          apply (cancel_mono Q.arrow).mp
          simp only [Category.assoc, Subobject.ofLE_arrow]
        rw [factored, Category.assoc]
        exact imageSubobject_comp_le _ _
      simp only [FilteredComplex.boundarySubobject]
      rcases r₁ with _ | n₁ <;> rcases r₂ with _ | n₂
      · exact le_refl _
      · exact absurd hr₁₂ (WithTop.not_top_le_coe n₂)
      · -- (↑n₁, ⊤): image from F^{s-n₁} ≤ image from all of A^{k+1}
        apply ofLE_mono inf_le_right inf_le_right
        apply inf_le_inf_right
        exact imageSubobject_comp_le _ _
      · -- (↑n₁, ↑n₂): F^{s-n₁+1} ≤ F^{s-n₂+1} (since n₁ ≤ n₂, s-n₂+1 ≤ s-n₁+1)
        have hn : n₁ ≤ n₂ := WithTop.coe_le_coe.mp hr₁₂
        have hfil : FC.fil (s - ↑n₁ + 1) (k + 1) ≤ FC.fil (s - ↑n₂ + 1) (k + 1) :=
          FC.fil_anti_of_le (k + 1) (by omega)
        apply ofLE_mono inf_le_right inf_le_right
        apply inf_le_inf_right
        exact img_mono _ hfil
    -- Proof of img_mono
    intro X Y K₁ K₂ g hle
    rw [show K₁.arrow ≫ g = Subobject.ofLE K₁ K₂ hle ≫ K₂.arrow ≫ g by
      rw [← Category.assoc, Subobject.ofLE_arrow]]
    exact imageSubobject_comp_le _ _
  Z_zero := by
    -- Z 0 = ⊤: when r = 0, the cycle condition dx ∈ F^{s+0} = F^s is vacuous
    simp only [FilteredComplex.cycleSubobject]
    -- Step 1: show the cycle map f₀ = 0
    have hf0 : (FC.fil s k).arrow ≫ FC.d k ≫
        cokernel.π ((FC.fil (s + ↑(0 : ℕ)) (k - 1)).arrow) = 0 := by
      obtain ⟨φ, hφ⟩ := FC.d_preserves_fil s k
      simp only [← Category.assoc]
      rw [← hφ]
      simp only [Category.assoc]
      have hle : FC.fil s (k - 1) ≤ FC.fil (s + ↑(0 : ℕ)) (k - 1) :=
        le_of_eq (by congr 1; omega)
      rw [show (FC.fil s (k - 1)).arrow =
        Subobject.ofLE (FC.fil s (k - 1)) (FC.fil (s + ↑(0 : ℕ)) (k - 1)) hle ≫
        (FC.fil (s + ↑(0 : ℕ)) (k - 1)).arrow from (Subobject.ofLE_arrow hle).symm]
      simp only [Category.assoc, cokernel.condition, comp_zero]
    -- Step 2: kernelSubobject(f₀).arrow is an iso (since f₀ = 0)
    haveI : IsIso (kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
        cokernel.π ((FC.fil (s + ↑(0 : ℕ)) (k - 1)).arrow))).arrow := by
      rw [Subobject.isIso_arrow_iff_eq_top]
      simp only [hf0, kernelSubobject_zero]
    -- Step 3: imageSubobject (iso ≫ epi) = imageSubobject epi
    rw [imageSubobject_iso_comp]
    -- Step 4: imageSubobject of epi (cokernel.π) is ⊤
    haveI : Epi (image.ι (cokernel.π (Subobject.ofLE (FC.fil (s + 1) k)
        (FC.fil s k) (FC.fil_anti s k)))) := epi_image_of_epi _
    haveI : IsIso (image.ι (cokernel.π (Subobject.ofLE (FC.fil (s + 1) k)
        (FC.fil s k) (FC.fil_anti s k)))) := isIso_of_mono_of_epi _
    exact Subobject.mk_eq_top_of_isIso _
  B_le_Z := fun r => FC.B_le_Z_aux s k r
  Z_top_greatest := fun X hX => by
    -- Pick N large enough that FC.fil (s + ↑N) (k - 1) = ⊥ (Hausdorff)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, FC.fil (s + ↑N) (k - 1) = ⊥ := by
      use (bnd.hi (k - 1) - s).toNat
      apply bnd.boundedAbove; omega
    -- Key: cokernel.π(0) is iso
    have h_zero : (FC.fil (s + ↑N) (k - 1)).arrow = 0 := by
      rw [hN, Subobject.bot_arrow]
    haveI : IsIso (cokernel.π ((FC.fil (s + ↑N) (k - 1)).arrow)) := by
      rw [h_zero]; exact cokernel.π_zero_isIso
    -- ker(fN) ≤ ker(fTop): since cokernel.π is iso, cancel it
    have hle : kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
        cokernel.π ((FC.fil (s + ↑N) (k - 1)).arrow)) ≤
      kernelSubobject ((FC.fil s k).arrow ≫ FC.d k) := by
      apply le_kernelSubobject
      -- Goal: ker(fN).arrow ≫ (fil.arrow ≫ d) = 0
      -- From h1: ker(fN).arrow ≫ (fil.arrow ≫ d ≫ cokernel.π) = 0
      -- Since cokernel.π is mono (it's iso), cancel it.
      have h1 := kernelSubobject_arrow_comp ((FC.fil s k).arrow ≫ FC.d k ≫
          cokernel.π ((FC.fil (s + ↑N) (k - 1)).arrow))
      -- Reassociate h1
      simp only [] at h1
      -- h1 now: ker.arrow ≫ fil.arrow ≫ d ≫ cokernel.π = 0
      rw [← cancel_mono (cokernel.π ((FC.fil (s + ↑N) (k - 1)).arrow))]
      simp only [Category.assoc, zero_comp]
      exact h1
    -- X ≤ Z_N ≤ Z_⊤
    -- The goal after unfolding cycleSubobject has ↑↑N (Nat → WithTop ℕ → different coercion).
    -- We handle this by converting hle to use the form that appears in the goal.
    have hle' : kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
        cokernel.π ((FC.fil (s + ↑(↑N : ℕ)) (k - 1)).arrow)) ≤
      kernelSubobject ((FC.fil s k).arrow ≫ FC.d k) := hle
    -- cycleSubobject s k ↑N ≤ cycleSubobject s k ⊤
    -- Both are images of (kernelSubobject _).arrow ≫ πV
    -- Key: ker_N ≤ ker_⊤ from hle above
    suffices hsuff : FC.cycleSubobject s k ↑N ≤ FC.cycleSubobject s k ⊤ from
      le_trans (hX N) hsuff
    -- Unfold both sides. The unfolded LHS has a double coercion ↑↑N from
    -- matching (↑N : WithTop ℕ) and then coercing N : ℕ → ℤ inside.
    -- We use `show` to normalize this.
    change imageSubobject
        ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
          cokernel.π ((FC.fil (s + ↑N) (k - 1)).arrow))).arrow ≫
          cokernel.π (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k))) ≤
      imageSubobject
        ((kernelSubobject ((FC.fil s k).arrow ≫ FC.d k)).arrow ≫
          cokernel.π (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)))
    -- Factor: ker_N.arrow = ofLE(ker_N, ker_⊤) ≫ ker_⊤.arrow
    have heq : (kernelSubobject ((FC.fil s k).arrow ≫ FC.d k ≫
        cokernel.π ((FC.fil (s + ↑N) (k - 1)).arrow))).arrow ≫
        cokernel.π (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)) =
      Subobject.ofLE _ _ hle ≫ (kernelSubobject ((FC.fil s k).arrow ≫ FC.d k)).arrow ≫
        cokernel.π (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)) := by
      conv_rhs => rw [← Category.assoc]
      congr 1
      exact (Subobject.ofLE_arrow hle).symm
    rw [heq]
    exact imageSubobject_comp_le _ _
  B_top_least := fun X hX => by
    -- Pick N large enough that FC.fil (s - ↑N + 1) (k + 1) = ⊤ (exhaustive)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, FC.fil (s - ↑N + 1) (k + 1) = ⊤ := by
      use (s + 1 - bnd.lo (k + 1)).toNat
      apply bnd.boundedBelow; omega
    -- When fil = ⊤, its arrow is iso
    haveI : IsIso (FC.fil (s - ↑N + 1) (k + 1)).arrow := by
      rw [Subobject.isIso_arrow_iff_eq_top]; exact hN
    -- Key equality: imageSubobject(fil.arrow ≫ dToK k) = imageSubobject(dToK k)
    have himgD : imageSubobject ((FC.fil (s - ↑N + 1) (k + 1)).arrow ≫ FC.dToK k) =
        imageSubobject (FC.dToK k) :=
      imageSubobject_iso_comp _ _
    -- Therefore B ↑N = B ⊤ (as subobjects)
    suffices hsuff : FC.boundarySubobject s k ⊤ ≤ FC.boundarySubobject s k ↑N from
      le_trans hsuff (hX N)
    -- Unfold both sides
    change imageSubobject (Subobject.ofLE (imageSubobject (FC.dToK k) ⊓ FC.fil s k)
          (FC.fil s k) inf_le_right ≫
          cokernel.π (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k))) ≤
      imageSubobject (Subobject.ofLE
          (imageSubobject ((FC.fil (s - ↑N + 1) (k + 1)).arrow ≫ FC.dToK k) ⊓ FC.fil s k)
          (FC.fil s k) inf_le_right ≫
          cokernel.π (Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)))
    -- Rewrite using himgD to make both sides equal
    rw [himgD]

/-! ### Spectral sequence from a filtered complex -/

/-! #### Induced differential on pages

The differential `d_r` on the page `E_r^{s,k} → E_r^{s+r,k-1}` is induced by
the original differential `d : A^k → A^{k-1}` of the filtered complex.

**Construction sketch**: Given an element of `E_r^{s,k} = Z_r^{s,k} / B_r^{s,k}`:
1. Lift to `Z_r^{s,k}` = { x ∈ F^s A^k | dx ∈ F^{s+r} A^{k-1} }
2. Map `x` to `dx ∈ F^{s+r} A^{k-1}`
3. Project to `gr^{s+r} A^{k-1} = F^{s+r} / F^{s+r+1}`
4. The image lands in `Z_r^{s+r,k-1}` (since d²=0 implies d(dx) = 0 ∈ F^{s+2r})
5. Descend to `E_r^{s+r,k-1} = Z_r / B_r`
6. Show this is well-defined: independent of the lift (B_r maps to 0)

This requires careful bookkeeping with `cokernel.desc` and `factorThruKernelSubobject`. -/

/-! ### eqToHom transport helpers for pageDifferential -/

/-- Transport lemma for `Subobject.arrow` along an integer equality:
    `eqToHom ≫ (FC.fil s b).arrow = (FC.fil s a).arrow ≫ eqToHom`. -/
private theorem FilteredComplex.fil_arrow_eqToHom (FC : FilteredComplex C)
    (s : ℤ) (a b : ℤ) (h : a = b) :
    eqToHom (show Subobject.underlying.obj (FC.fil s a) =
      Subobject.underlying.obj (FC.fil s b) from by subst h; rfl) ≫
    (FC.fil s b).arrow = (FC.fil s a).arrow ≫
    eqToHom (show FC.A a = FC.A b from by subst h; rfl) := by
  subst h; simp

/-- Transport lemma for the differential along an integer equality:
    `eqToHom ≫ FC.d b = FC.d a ≫ eqToHom`. -/
private theorem FilteredComplex.d_eqToHom' (FC : FilteredComplex C)
    (a b : ℤ) (h : a = b) :
    eqToHom (show FC.A a = FC.A b from by subst h; rfl) ≫
    FC.d b = FC.d a ≫
    eqToHom (show FC.A (a - 1) = FC.A (b - 1) from by subst h; rfl) := by
  subst h; simp

/-- `eqToHom ≫ dToK(k-1) = d(k)`: the transported differential composed with eqToHom
    gives the original differential. (Generalized version with free variables.) -/
private theorem FilteredComplex.eqToHom_arrow_dToK_gen (FC : FilteredComplex C)
    (s : ℤ) (m k : ℤ) (hmk : m + 1 = k) :
    eqToHom (show Subobject.underlying.obj (FC.fil s k) =
      Subobject.underlying.obj (FC.fil s (m + 1)) by rw [hmk]) ≫
    ((FC.fil s (m + 1)).arrow ≫ FC.dToK m) =
      (FC.fil s k).arrow ≫ FC.d k ≫
      eqToHom (congr_arg FC.A (show k - 1 = m by omega)) := by
  subst hmk
  simp [FilteredComplex.dToK]

/-- Specialized transport: `eqToHom ≫ F^s((k-1)+1).arrow ≫ dToK(k-1) = F^s(k).arrow ≫ d(k)`. -/
private theorem FilteredComplex.eqToHom_arrow_dToK (FC : FilteredComplex C)
    (s k : ℤ) :
    eqToHom (show Subobject.underlying.obj (FC.fil s k) =
      Subobject.underlying.obj (FC.fil s ((k - 1) + 1)) by
      rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
    ((FC.fil s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
      (FC.fil s k).arrow ≫ FC.d k := by
  rw [FC.eqToHom_arrow_dToK_gen s (k - 1) k (by omega)]
  simp

set_option maxHeartbeats 800000 in
-- Large proof with many kernel/cokernel factoring steps for the induced page differential
/-- The induced differential on pages: `d_r : E_r^{s,k} → E_r^{s+r,k-1}`.
    This maps Z_r-cycles modulo B_r-boundaries at (s,k) to the same at (s+r,k-1),
    using the original differential d of the filtered complex.

    For `r = n : ℕ`:
    - Source: `E_n^{s,k} = Z_n^{s,k} / B_n^{s,k}` where
      `Z_n = { x ∈ F^s | dx ∈ F^{s+n} }` and `B_n = { dz | z ∈ F^{s-n}, dz ∈ F^s }`
    - Target: `E_n^{s+n,k-1} = Z_n^{s+n,k-1} / B_n^{s+n,k-1}`
    - Map: send class of x to class of dx -/
noncomputable def FilteredComplex.pageDifferential (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    (FC.toSSData bnd s k).page ↑n ⟶ (FC.toSSData bnd (s + ↑n) (k - 1)).page ↑n := by
  -- === Source side abbreviations ===
  set ι_s := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k) with hι_s_def
  set πV := cokernel.π ι_s with hπV_def
  set f_n := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) with hf_n_def
  set kerZ := kernelSubobject f_n with hkerZ_def
  -- === Target side abbreviations ===
  set ι_t := Subobject.ofLE (FC.fil (s + ↑n + 1) (k - 1)) (FC.fil (s + ↑n) (k - 1))
    (FC.fil_anti (s + ↑n) (k - 1)) with hι_t_def
  set πV' := cokernel.π ι_t with hπV'_def
  set f_n' := (FC.fil (s + ↑n) (k - 1)).arrow ≫ FC.d (k - 1) ≫
    cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) with hf_n'_def
  set kerZ' := kernelSubobject f_n' with hkerZ'_def
  -- Page types
  -- Source page = cokernel(ofLE(B_n_s, Z_n_s, _)) where Z_n_s = imageSubobject(kerZ.arrow ≫ πV)
  -- Target page = cokernel(ofLE(B_n_t, Z_n_t, _)) where Z_n_t = imageSubobject(kerZ'.arrow ≫ πV')
  -- === Step 1: Lift d-image through F^{s+n}(k-1) ===
  -- kerZ.arrow ≫ f_n = 0, hence kerZ.arrow ≫ F^s.arrow ≫ d ≫ cokernel.π(F^{s+n}.arrow) = 0
  -- So kerZ.arrow ≫ F^s.arrow ≫ d(k) factors through F^{s+n}(k-1).arrow (mono lift)
  have h_ker_fn : kerZ.arrow ≫ f_n = 0 := kernelSubobject_arrow_comp f_n
  have h_factor_zero : (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
      cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc] at h_ker_fn ⊢; exact h_ker_fn
  set lift_n := Abelian.monoLift (FC.fil (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k)
    h_factor_zero with hlift_n_def
  have h_lift_spec : lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow =
      kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k :=
    Abelian.monoLift_comp _ _ _
  -- === Step 2: Show lift_n factors through kerZ' (using d²=0) ===
  have h_lift_in_kerZ' : lift_n ≫ f_n' = 0 := by
    calc lift_n ≫ f_n'
        = lift_n ≫ ((FC.fil (s + ↑n) (k - 1)).arrow ≫ FC.d (k - 1) ≫
            cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow)) := rfl
      _ = ((lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) ≫ FC.d (k - 1)) ≫
            cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          simp only [Category.assoc]
      _ = ((kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫ FC.d (k - 1)) ≫
            cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          rw [h_lift_spec]
      _ = (kerZ.arrow ≫ (FC.fil s k).arrow ≫ (FC.d k ≫ FC.d (k - 1))) ≫
            cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          simp only [Category.assoc]
      _ = 0 := by rw [FC.d_comp_d k]; simp only [comp_zero, zero_comp]
  set lift_to_kerZ' := factorThruKernelSubobject f_n' lift_n h_lift_in_kerZ'
    with hlift_to_kerZ'_def
  -- === Step 3: Build ψ : kerZ.underlying → target page ===
  set to_Z_n_t := lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')
    with hto_Z_n_t_def
  set pageπ' := (FC.toSSData bnd (s + ↑n) (k - 1)).pageπ ↑n with hpageπ'_def
  set ψ := to_Z_n_t ≫ pageπ' with hψ_def
  -- === Step 4: Descend ψ through epi (kerZ → Z_n_s) using Abelian.epiDesc ===
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV) with hp_def
  haveI : Epi p := inferInstance
  -- Need: kernel.ι p ≫ ψ = 0
  have h_ker_p_ψ : kernel.ι p ≫ ψ = 0 := by
    -- Strategy: kernel.ι p ≫ ψ = kernel.ι p ≫ to_Z_n_t ≫ pageπ'.
    -- Show kernel.ι p ≫ to_Z_n_t factors through ofLE(B_n_t, Z_n_t),
    -- then pageπ' = cokernel.π(ofLE(B_n_t, Z_n_t)) kills it.
    -- === Step B: lift_n spec ===
    have h_comp_eq : kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow =
        kernel.ι p ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k := by
      -- ≫ is right-associative, so this is kernel.ι p ≫ (lift_n ≫ arrow) = kernel.ι p ≫ (...)
      -- congr 1 unifies the first argument and h_lift_spec matches the rest
      simp only [h_lift_spec]
    -- === Step C: Factor through imgD ⊓ F^{s+n}(k-1) ===
    -- After boundarySubobject fix, boundary at target uses F^{s+1}, so we use F^{s+1} here.
    set imgD := imageSubobject ((FC.fil (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1))
      with himgD_def
    -- C1: Factors through imgD
    -- Key: kernel.ι p maps into F^{s+1}(k) via kerZ.arrow
    -- (kernel of πV = cokernel.π(F^{s+1} → F^s))
    have h_fac_imgD : imgD.Factors
        (kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) := by
      rw [h_comp_eq]
      -- Goal: imgD.Factors (kernel.ι p ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k)
      -- Step 1: kernel.ι p ≫ kerZ.arrow ≫ πV = 0 (from kernel condition on p)
      have h1 : kernel.ι p ≫ (kerZ.arrow ≫ πV) = 0 := by
        have h_p_Z : p ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow = kerZ.arrow ≫ πV :=
          imageSubobject_arrow_comp (kerZ.arrow ≫ πV)
        calc kernel.ι p ≫ (kerZ.arrow ≫ πV)
            = kernel.ι p ≫ (p ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow) := by rw [h_p_Z]
          _ = (kernel.ι p ≫ p) ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow := by
              simp only [Category.assoc]
          _ = 0 ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow := by rw [kernel.condition]
          _ = 0 := zero_comp
      -- Step 2: kernel.ι p ≫ kerZ.arrow factors through ι_s via Abelian.monoLift
      -- ι_s : F^{s+1}.underlying → F^s.underlying, πV = cokernel.π ι_s
      have h1' : (kernel.ι p ≫ kerZ.arrow) ≫ cokernel.π ι_s = 0 := by
        rw [Category.assoc]; exact h1
      set α := Abelian.monoLift ι_s (kernel.ι p ≫ kerZ.arrow) h1' with hα_def
      have hα_spec : α ≫ ι_s = kernel.ι p ≫ kerZ.arrow := Abelian.monoLift_comp _ _ _
      -- Step 3: α ≫ ι_s ≫ (FC.fil s k).arrow = α ≫ (FC.fil (s+1) k).arrow [by ofLE_arrow]
      have h_ι_arrow : ι_s ≫ (FC.fil s k).arrow = (FC.fil (s + 1) k).arrow := by
        exact Subobject.ofLE_arrow (FC.fil_anti s k)
      -- Step 4: (kernel.ι p ≫ kerZ.arrow ≫ (FC.fil s k).arrow) ≫ FC.d k
      --       = (α ≫ (FC.fil (s+1) k).arrow) ≫ FC.d k
      --       = α ≫ ((FC.fil (s+1) k).arrow ≫ FC.d k)
      -- and (FC.fil (s+1) k).arrow ≫ FC.d k = eqToHom ≫ (FC.fil (s+1)((k-1)+1).arrow ≫ dToK(k-1))
      have h_rewrite : kernel.ι p ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k =
          α ≫ ((FC.fil (s + 1) k).arrow ≫ FC.d k) := by
        conv_lhs => rw [show kernel.ι p ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k =
          ((kernel.ι p ≫ kerZ.arrow) ≫ (FC.fil s k).arrow) ≫ FC.d k from by
          simp only [Category.assoc]]
        rw [← hα_spec, show (α ≫ ι_s) ≫ (FC.fil s k).arrow = α ≫ (ι_s ≫ (FC.fil s k).arrow) from
          Category.assoc _ _ _, h_ι_arrow, Category.assoc]
      rw [h_rewrite]
      apply Subobject.factors_of_factors_right
      -- Goal: imgD.Factors ((FC.fil (s+1) k).arrow ≫ FC.d k)
      have h_transport : eqToHom (show Subobject.underlying.obj (FC.fil (s + 1) k) =
          Subobject.underlying.obj (FC.fil (s + 1) ((k - 1) + 1)) by
          rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
          ((FC.fil (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
          (FC.fil (s + 1) k).arrow ≫ FC.d k :=
        FC.eqToHom_arrow_dToK (s + 1) k
      rw [← h_transport, himgD_def, Subobject.mk_factors_iff]
      exact ⟨eqToHom (by rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
        factorThruImage ((FC.fil (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)), by simp⟩
    -- C2: Factors through F^{s+n}(k-1) (trivially)
    have h_fac_fil : (FC.fil (s + ↑n) (k - 1)).Factors
        (kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) :=
      Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow lift_n)
    -- C3: Factor through I = imgD ⊓ F^{s+n}(k-1)
    set I := imgD ⊓ FC.fil (s + ↑n) (k - 1) with hI_def
    have h_fac_I : I.Factors (kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) :=
      (Subobject.inf_factors _).mpr ⟨h_fac_imgD, h_fac_fil⟩
    set δ := I.factorThru _ h_fac_I with hδ_def
    have hδ_spec : δ ≫ I.arrow = kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow :=
      Subobject.factorThru_arrow _ _ _
    -- === Step D: δ ≫ ofLE(I, F^{s+n}) = kernel.ι p ≫ lift_n ===
    have h_δ_ofLE : δ ≫ Subobject.ofLE I (FC.fil (s + ↑n) (k - 1)) inf_le_right =
        kernel.ι p ≫ lift_n := by
      apply (inferInstance : Mono (FC.fil (s + ↑n) (k - 1)).arrow).right_cancellation
      rw [Category.assoc, Subobject.ofLE_arrow, hδ_spec]
      simp only [Category.assoc]
    -- === Step E: Match boundary definition with I ===
    -- B_n_t = FC.boundarySubobject (s+↑n) (k-1) ↑n uses imgD' at index (s+↑n)-↑n+1 = s+1
    -- imgD' in boundary = imageSubobject(F^{(s+↑n)-↑n+1}((k-1)+1).arrow ≫ dToK(k-1)) = imgD
    have h_imgD_bnd : imageSubobject ((FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) = imgD := by
      rw [show (s : ℤ) + (↑n : ℤ) - (↑n : ℤ) + 1 = s + 1 from by omega]
    -- Therefore: I_bnd = imgD' ⊓ F^{s+↑n}(k-1) = I
    have h_I_bnd : imageSubobject ((FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) ⊓ FC.fil (s + ↑n) (k - 1) = I := by
      rw [h_imgD_bnd]
    -- B_n_t = imageSubobject(ofLE(I_bnd, F^{s+n}, inf_le_right) ≫ πV')
    -- where I_bnd = I (after h_I_bnd). So:
    -- imageSubobject(ofLE(I, F^{s+n}, inf_le_right) ≫ πV') = B_n_t (up to ofLE transport)
    -- The key: ofLE(I, F^{s+n}) ≫ πV' = factorThru(...) ≫ B_n_t.arrow
    -- which means (imageSubobject(ofLE(I, ...) ≫ πV')).Factors (δ ≫ ofLE(I,...) ≫ πV')
    -- But we also need B_n_t.Factors (kernel.ι p ≫ lift_n ≫ πV')

    -- kernel.ι p ≫ lift_n ≫ πV' = δ ≫ ofLE(I, F^{s+n}) ≫ πV' [by h_δ_ofLE]
    -- This factors through imageSubobject(ofLE(I, F^{s+n}) ≫ πV')
    -- via imageSubobject_factors_comp_self.
    -- We need this imageSubobject to equal B_n_t (after matching indices).

    -- === Step F: Show B_n_t.Factors (kernel.ι p ≫ lift_n ≫ πV') ===
    -- The boundary is:
    -- FC.boundarySubobject (s+↑n) (k-1) ↑n
    --   = imageSubobject(ofLE(I_bnd, F^{s+↑n}(k-1), inf_le_right) ≫ πV')
    -- where I_bnd = imgD_bnd ⊓ F^{s+↑n}(k-1) and imgD_bnd uses index (s+↑n)-↑n
    -- After rewriting, I_bnd = I, so:
    -- B_n_t = imageSubobject(ofLE(I_bnd, F^{s+↑n}, inf_le_right) ≫ πV')
    -- and since I_bnd = I (from h_I_bnd), we have B_n_t ≥ imageSubobject(ofLE(I, ...) ≫ πV')
    -- (actually they're equal, but ≥ suffices).
    -- More precisely: ofLE(I_bnd, F^{s+↑n}, _) and ofLE(I, F^{s+↑n}, _) differ only in the
    -- proof argument; the underlying morphisms are the same after subst.
    -- We use factors_of_le to get B_n_t.Factors from the ≤ relation.

    -- Actually, since the ofLE terms differ by the proof of I_bnd ≤ F^{s+↑n} vs I ≤ F^{s+↑n},
    -- and subobjects are quotients of MonoOver, the morphisms are propositionally equal.
    -- Let's show B_n_t.Factors directly.
    have h_bnd_fac : (FC.boundarySubobject (s + ↑n) (k - 1) ↑n).Factors
        (kernel.ι p ≫ lift_n ≫ πV') := by
      -- Rewrite: kernel.ι p ≫ lift_n ≫ πV' = (kernel.ι p ≫ lift_n) ≫ πV' = δ ≫ ofLE ≫ πV'
      rw [show kernel.ι p ≫ lift_n ≫ πV' = (kernel.ι p ≫ lift_n) ≫ πV'
        from (Category.assoc _ _ _).symm,
        ← h_δ_ofLE, Category.assoc]
      -- Now goal: B_n_t.Factors (δ ≫ ofLE(I, F^{s+n}) ≫ πV')
      -- Use Subobject.factors_of_factors_right: P.Factors g → P.Factors (f ≫ g)
      apply Subobject.factors_of_factors_right
      -- Goal: B_n_t.Factors (ofLE(I, F^{s+n}) ≫ πV')
      -- B_n_t = imageSubobject(ofLE(I_bnd, F^{s+n}, inf_le_right) ≫ πV')
      -- and ofLE(I_bnd, ...) = ofLE(I, ...) after h_I_bnd
      -- So ofLE(I, F^{s+n}) ≫ πV' is in the image of the boundary's source map.
      -- Use imageSubobject_factors_comp_self with f = ofLE ≫ πV' and k = 𝟙
      change (FC.boundarySubobject (s + ↑n) (k - 1) ↑n).Factors
        (Subobject.ofLE I (FC.fil (s + ↑n) (k - 1)) inf_le_right ≫ πV')
      -- boundarySubobject = imageSubobject(ofLE(I_bnd, fil, inf_le_right) ≫ πV')
      -- where I_bnd = imgD_bnd ⊓ fil. Since I_bnd = I (h_I_bnd),
      -- boundary ≥ imageSubobject(ofLE(I,...) ≫ πV')
      -- and our morphism factors through boundary.
      -- Key: I ≤ I_bnd (from h_I_bnd.symm), so ofLE(I, fil) = ofLE(I, I_bnd) ≫ ofLE(I_bnd, fil)
      set I_bnd := imageSubobject ((FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) ⊓ FC.fil (s + ↑n) (k - 1) with hI_bnd_def
      have h_I_le_Ibnd : I ≤ I_bnd := le_of_eq h_I_bnd.symm
      -- ofLE(I, fil) = ofLE(I, I_bnd) ≫ ofLE(I_bnd, fil)
      have h_ofLE_factor : Subobject.ofLE I (FC.fil (s + ↑n) (k - 1)) inf_le_right =
          Subobject.ofLE I I_bnd h_I_le_Ibnd ≫
          Subobject.ofLE I_bnd (FC.fil (s + ↑n) (k - 1)) inf_le_right := by
        apply (inferInstance : Mono (FC.fil (s + ↑n) (k - 1)).arrow).right_cancellation
        simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [h_ofLE_factor, Category.assoc]
      -- Goal: boundary.Factors (ofLE(I, I_bnd) ≫ (ofLE(I_bnd, fil) ≫ πV'))
      apply Subobject.factors_of_factors_right
      -- Goal: boundary.Factors (ofLE(I_bnd, fil) ≫ πV')
      -- boundary = imageSubobject(ofLE(I_bnd, fil, inf_le_right) ≫ πV')
      -- So (ofLE(I_bnd, fil) ≫ πV') is the generating morphism. It factors through itself.
      change (imageSubobject
        (Subobject.ofLE I_bnd (FC.fil (s + ↑n) (k - 1)) inf_le_right ≫ πV')).Factors
        (Subobject.ofLE I_bnd (FC.fil (s + ↑n) (k - 1)) inf_le_right ≫ πV')
      rw [Subobject.mk_factors_iff]
      exact ⟨factorThruImage _, by simp⟩
    -- === Step G: Show kernel.ι p ≫ ψ = 0 ===
    -- ψ = to_Z_n_t ≫ pageπ' where pageπ' = cokernel.π(ofLE(B_n_t, Z_n_t, _))
    -- We need to show kernel.ι p ≫ to_Z_n_t factors through ofLE(B_n_t, Z_n_t)
    -- This follows from: (kernel.ι p ≫ to_Z_n_t) ≫ Z_n_t.arrow = kernel.ι p ≫ lift_n ≫ πV'
    -- factors through B_n_t.arrow (h_bnd_fac).
    set B_n_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑n with hB_n_t_def
    set Z_n_t := FC.cycleSubobject (s + ↑n) (k - 1) ↑n with hZ_n_t_def
    have hB_le_Z := FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n
    -- to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV'
    -- (since Z_n_t = imageSubobject(kerZ'.arrow ≫ πV') and
    --  to_Z_n_t = lift_to_kerZ' ≫ factorThruImageSubobject(kerZ'.arrow ≫ πV'))
    have h_to_Z_comp : to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV' := by
      change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
        (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
      simp only [Category.assoc, imageSubobject_arrow_comp]
      -- goal: lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' = lift_n ≫ πV'
      -- Reassociate left to isolate lift_to_kerZ' ≫ kerZ'.arrow
      rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
        (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm]
      rw [show lift_to_kerZ' ≫ kerZ'.arrow = lift_n from by
        rw [hlift_to_kerZ'_def]
        exact factorThruKernelSubobject_comp_arrow f_n' lift_n h_lift_in_kerZ']
    -- kernel.ι p ≫ to_Z_n_t ≫ Z_n_t.arrow factors through B_n_t
    have h_ker_to_Z_fac : B_n_t.Factors (kernel.ι p ≫ to_Z_n_t ≫ Z_n_t.arrow) := by
      rw [h_to_Z_comp]
      exact h_bnd_fac
    -- So kernel.ι p ≫ to_Z_n_t factors through ofLE(B_n_t, Z_n_t)
    set γ := B_n_t.factorThru _ h_ker_to_Z_fac with hγ_def
    have hγ_spec : γ ≫ B_n_t.arrow = kernel.ι p ≫ to_Z_n_t ≫ Z_n_t.arrow :=
      Subobject.factorThru_arrow _ _ _
    -- γ ≫ ofLE(B, Z) ≫ Z.arrow = kernel.ι p ≫ to_Z_n_t ≫ Z.arrow
    -- So γ ≫ ofLE(B, Z) = kernel.ι p ≫ to_Z_n_t (by mono cancellation on Z.arrow)
    have h_factor_B : kernel.ι p ≫ to_Z_n_t =
        γ ≫ Subobject.ofLE B_n_t Z_n_t hB_le_Z := by
      apply (inferInstance : Mono Z_n_t.arrow).right_cancellation
      simp only [Category.assoc]
      rw [Subobject.ofLE_arrow, hγ_spec]
    -- cokernel condition: ofLE(B, Z) ≫ pageπ' = 0
    have h_cok : Subobject.ofLE B_n_t Z_n_t hB_le_Z ≫ pageπ' = 0 := by
      rw [hpageπ'_def]
      change Subobject.ofLE B_n_t Z_n_t hB_le_Z ≫
        cokernel.π (Subobject.ofLE (FC.boundarySubobject (s + ↑n) (k - 1) ↑n)
          (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)
          (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n)) = 0
      exact cokernel.condition _
    -- Final computation
    rw [hψ_def]
    calc kernel.ι p ≫ to_Z_n_t ≫ pageπ'
        = (kernel.ι p ≫ to_Z_n_t) ≫ pageπ' := (Category.assoc _ _ _).symm
      _ = (γ ≫ Subobject.ofLE B_n_t Z_n_t hB_le_Z) ≫ pageπ' := by rw [h_factor_B]
      _ = γ ≫ (Subobject.ofLE B_n_t Z_n_t hB_le_Z ≫ pageπ') := Category.assoc _ _ _
      _ = γ ≫ 0 := by rw [h_cok]
      _ = 0 := comp_zero
  set h_on_Zn := Abelian.epiDesc p ψ h_ker_p_ψ with hh_on_Zn_def
  -- h_on_Zn : Z_n_s.underlying → target page, with p ≫ h_on_Zn = ψ
  -- === Step 5: Descend through source page cokernel ===
  -- Need: ofLE(B_n_s, Z_n_s, _) ≫ h_on_Zn = 0
  -- Source page = (FC.toSSData bnd s k).page ↑n
  --            = cokernel(ofLE(FC.boundarySubobject s k ↑n, FC.cycleSubobject s k ↑n, _))
  -- Z_n_s = FC.cycleSubobject s k ↑n = imageSubobject(kerZ.arrow ≫ πV) ✓
  -- B_n_s = FC.boundarySubobject s k ↑n
  have h_B_zero : Subobject.ofLE (FC.boundarySubobject s k ↑n)
      (FC.cycleSubobject s k ↑n)
      (FC.B_le_Z_aux s k ↑n) ≫ h_on_Zn = 0 := by
    -- Strategy: cancel the epi from the boundary's preimage, then show ψ kills it via d²=0.
    -- === Source boundary setup ===
    set imgD_s := imageSubobject ((FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k)
      with himgD_s_def
    set I_s := imgD_s ⊓ FC.fil s k with hI_s_def
    set oI_s := Subobject.ofLE I_s (FC.fil s k) inf_le_right with hoI_s_def
    -- B_n_s = imageSubobject(oI_s ≫ πV) (definitionally)
    -- Z_n_s = imageSubobject(kerZ.arrow ≫ πV) (definitionally)
    -- === Step 1: oI_s ≫ f_n = 0 (boundary elements satisfy the cycle condition) ===
    have h_zero_s : oI_s ≫ f_n = 0 := by
      change Subobject.ofLE I_s (FC.fil s k) inf_le_right ≫
        ((FC.fil s k).arrow ≫ FC.d k ≫
          cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow)) = 0
      simp only [← Category.assoc]
      rw [Subobject.ofLE_arrow]
      rw [show I_s.arrow =
          Subobject.ofLE I_s imgD_s inf_le_left ≫ imgD_s.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      simp only [Category.assoc]
      have hd : imgD_s.arrow ≫ FC.d k = 0 := by
        rw [← cancel_epi (factorThruImageSubobject
          ((FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k))]
        rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp,
          Category.assoc, FC.dToK_comp_d, comp_zero]
      rw [show imgD_s.arrow ≫ FC.d k ≫ cokernel.π _ =
        (imgD_s.arrow ≫ FC.d k) ≫ cokernel.π _
        from (Category.assoc _ _ _).symm,
        hd, zero_comp, comp_zero]
    -- === Step 2: Lift oI_s to kerZ ===
    set σ_s := factorThruKernelSubobject f_n oI_s h_zero_s with hσ_s_def
    have hσ_s_spec : σ_s ≫ kerZ.arrow = oI_s :=
      factorThruKernelSubobject_comp_arrow f_n oI_s h_zero_s
    -- === Step 3: σ_s ≫ p ≫ Z_n.arrow = oI_s ≫ πV ===
    -- p ≫ Z_n.arrow = kerZ.arrow ≫ πV
    have hp_spec : p ≫ (FC.cycleSubobject s k ↑n).arrow = kerZ.arrow ≫ πV := by
      change factorThruImageSubobject (kerZ.arrow ≫ πV) ≫
        (imageSubobject (kerZ.arrow ≫ πV)).arrow = kerZ.arrow ≫ πV
      exact imageSubobject_arrow_comp (kerZ.arrow ≫ πV)
    -- === Step 4: Cancel epi to reduce to σ_s ≫ ψ = 0 ===
    -- factorThruImageSubobject(oI_s ≫ πV) is epi
    set q := factorThruImageSubobject (oI_s ≫ πV) with hq_def
    haveI : Epi q := inferInstance
    -- q ≫ ofLE(B_n, Z_n) ≫ Z_n.arrow = oI_s ≫ πV = σ_s ≫ kerZ.arrow ≫ πV = σ_s ≫ p ≫ Z_n.arrow
    have hq_ofLE_spec : q ≫ Subobject.ofLE (FC.boundarySubobject s k ↑n)
        (FC.cycleSubobject s k ↑n) (FC.B_le_Z_aux s k ↑n) ≫
        (FC.cycleSubobject s k ↑n).arrow = oI_s ≫ πV := by
      -- q ≫ ofLE ≫ Z_n.arrow = q ≫ B_n.arrow (by ofLE_arrow)
      -- = oI_s ≫ πV (by imageSubobject_arrow_comp)
      simp only [Subobject.ofLE_arrow]
      show q ≫ (FC.boundarySubobject s k ↑n).arrow = oI_s ≫ πV
      exact imageSubobject_arrow_comp (oI_s ≫ πV)
    -- σ_s ≫ p ≫ Z_n.arrow = oI_s ≫ πV (same as q ≫ ofLE ≫ Z_n.arrow)
    have hσ_p_spec : σ_s ≫ p ≫ (FC.cycleSubobject s k ↑n).arrow = oI_s ≫ πV := by
      simp only [hp_spec]
      rw [show σ_s ≫ kerZ.arrow ≫ πV = (σ_s ≫ kerZ.arrow) ≫ πV from by
        simp only [Category.assoc]]
      rw [hσ_s_spec]
    have hσ_factor : q ≫ Subobject.ofLE (FC.boundarySubobject s k ↑n)
        (FC.cycleSubobject s k ↑n) (FC.B_le_Z_aux s k ↑n) = σ_s ≫ p := by
      apply (inferInstance : Mono (FC.cycleSubobject s k ↑n).arrow).right_cancellation
      -- Goal: (q ≫ ofLE) ≫ Z_n.arrow = (σ_s ≫ p) ≫ Z_n.arrow
      simp only [Category.assoc, Subobject.ofLE_arrow]
      -- Now both sides should reduce to oI_s ≫ πV
      rw [hσ_p_spec]
      show q ≫ (FC.boundarySubobject s k ↑n).arrow = oI_s ≫ πV
      exact imageSubobject_arrow_comp (oI_s ≫ πV)
    -- === Step 5: σ_s ≫ lift_n = 0 (key: d² = 0) ===
    have hσ_lift_zero : σ_s ≫ lift_n = 0 := by
      apply (inferInstance : Mono (FC.fil (s + ↑n) (k - 1)).arrow).right_cancellation
      rw [zero_comp]
      simp only [Category.assoc]
      rw [h_lift_spec]
      -- Goal: σ_s ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k = 0
      -- Reassociate to (σ_s ≫ kerZ.arrow) ≫ ...
      rw [show σ_s ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k =
        (σ_s ≫ kerZ.arrow) ≫ (FC.fil s k).arrow ≫ FC.d k from by
        simp only [Category.assoc]]
      rw [hσ_s_spec]
      -- Goal: oI_s ≫ (FC.fil s k).arrow ≫ FC.d k = 0
      rw [show oI_s ≫ (FC.fil s k).arrow ≫ FC.d k =
        (oI_s ≫ (FC.fil s k).arrow) ≫ FC.d k from by simp only [Category.assoc]]
      rw [show oI_s ≫ (FC.fil s k).arrow = I_s.arrow from Subobject.ofLE_arrow inf_le_right]
      rw [show I_s.arrow =
          Subobject.ofLE I_s imgD_s inf_le_left ≫ imgD_s.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      rw [Category.assoc]
      have hd : imgD_s.arrow ≫ FC.d k = 0 := by
        rw [← cancel_epi (factorThruImageSubobject
          ((FC.fil (s - ↑n + 1) (k + 1)).arrow ≫ FC.dToK k))]
        rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp,
          Category.assoc, FC.dToK_comp_d, comp_zero]
      rw [hd, comp_zero]
    -- === Step 6: σ_s ≫ ψ = 0 ===
    have hσ_ψ_zero : σ_s ≫ ψ = 0 := by
      rw [hψ_def, hto_Z_n_t_def, show σ_s ≫ (lift_to_kerZ' ≫
          factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫ pageπ' =
        ((σ_s ≫ lift_to_kerZ') ≫
          factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫ pageπ'
        from by simp only [Category.assoc]]
      -- σ_s ≫ lift_to_kerZ' = 0 since σ_s ≫ lift_n = 0 and lift_to_kerZ' lifts lift_n
      have h_σ_lift_kerZ' : σ_s ≫ lift_to_kerZ' = 0 := by
        apply (inferInstance : Mono kerZ'.arrow).right_cancellation
        rw [zero_comp]
        simp only [Category.assoc]
        rw [hlift_to_kerZ'_def, factorThruKernelSubobject_comp_arrow]
        exact hσ_lift_zero
      rw [h_σ_lift_kerZ', zero_comp, zero_comp]
    -- === Step 7: Cancel epi q to conclude ===
    -- Goal: ofLE(B_n, Z_n) ≫ h_on_Zn = 0
    -- We have: q ≫ ofLE(B_n, Z_n) = σ_s ≫ p (hσ_factor)
    -- and p ≫ h_on_Zn = ψ (comp_epiDesc)
    -- and σ_s ≫ ψ = 0 (hσ_ψ_zero)
    -- So q ≫ ofLE(B_n, Z_n) ≫ h_on_Zn = σ_s ≫ p ≫ h_on_Zn = σ_s ≫ ψ = 0
    -- Since q is epi, ofLE(B_n, Z_n) ≫ h_on_Zn = 0
    have h_comp_zero : q ≫ (Subobject.ofLE (FC.boundarySubobject s k ↑n)
        (FC.cycleSubobject s k ↑n)
        (FC.B_le_Z_aux s k ↑n) ≫ h_on_Zn) = 0 := by
      rw [← Category.assoc, hσ_factor, Category.assoc, hh_on_Zn_def,
        Abelian.comp_epiDesc]
      exact hσ_ψ_zero
    exact (cancel_epi q).mp (by rw [h_comp_zero, comp_zero])
  -- Final: cokernel.desc gives source page → target page
  exact cokernel.desc _ h_on_Zn h_B_zero

set_option maxHeartbeats 800000 in
-- Heavy unification through epi/mono factoring of kernel and image subobjects
/-- The kernel of `Abelian.epiDesc p g hg` (where `p` is epi) is the image of
    `(kernelSubobject g).arrow ≫ p`. This is the epi analogue of
    `kernelSubobject_cokernel_desc'`. -/
private theorem kernelSubobject_epiDesc' {C' : Type*} [Category C'] [Abelian C']
    {A' B' D' : C'} (p : A' ⟶ B') [Epi p] (g : A' ⟶ D')
    (hg : kernel.ι p ≫ g = 0) :
    kernelSubobject (Abelian.epiDesc p g hg) =
      imageSubobject ((kernelSubobject g).arrow ≫ p) := by
  apply le_antisymm
  · -- (≤): ker(epiDesc) ≤ image((ker g).arrow ≫ p)
    set K := kernelSubobject (Abelian.epiDesc p g hg) with hK_def
    -- Form the pullback of p (epi) and K.arrow (mono)
    have hpb_comm : pullback.fst p K.arrow ≫ p = pullback.snd p K.arrow ≫ K.arrow :=
      pullback.condition
    haveI : Mono (pullback.fst p K.arrow) :=
      pullback.fst_of_mono (f := p) (g := K.arrow)
    haveI : Epi (pullback.snd p K.arrow) :=
      Abelian.epi_pullback_of_epi_f p K.arrow
    -- Show pullback.fst ≫ g = 0
    have h_fst_g_zero : pullback.fst p K.arrow ≫ g = 0 := by
      calc pullback.fst p K.arrow ≫ g
          = pullback.fst p K.arrow ≫ (p ≫ Abelian.epiDesc p g hg) :=
            by rw [Abelian.comp_epiDesc]
        _ = (pullback.fst p K.arrow ≫ p) ≫ Abelian.epiDesc p g hg :=
            (Category.assoc _ _ _).symm
        _ = (pullback.snd p K.arrow ≫ K.arrow) ≫ Abelian.epiDesc p g hg :=
            by rw [hpb_comm]
        _ = pullback.snd p K.arrow ≫ (K.arrow ≫ Abelian.epiDesc p g hg) :=
            Category.assoc _ _ _
        _ = pullback.snd p K.arrow ≫ 0 := by rw [kernelSubobject_arrow_comp]
        _ = 0 := comp_zero
    -- Factor through ker(g)
    set φ := factorThruKernelSubobject g (pullback.fst p K.arrow) h_fst_g_zero
    have hφ_spec : φ ≫ (kernelSubobject g).arrow = pullback.fst p K.arrow :=
      factorThruKernelSubobject_comp_arrow g _ _
    -- Key equation: φ ≫ ker(g).arrow ≫ p = pullback.snd ≫ K.arrow
    have h_key_eq : φ ≫ (kernelSubobject g).arrow ≫ p =
        pullback.snd p K.arrow ≫ K.arrow := by
      rw [show φ ≫ (kernelSubobject g).arrow ≫ p =
        (φ ≫ (kernelSubobject g).arrow) ≫ p from (Category.assoc _ _ _).symm,
        hφ_spec, hpb_comm]
    -- image(pullback.snd ≫ K.arrow) = K (since snd is epi, K.arrow is mono)
    have h_img_epi_comp : ∀ {X₁ X₂ X₃ : C'} (e : X₁ ⟶ X₂) [Epi e] (h : X₂ ⟶ X₃),
        imageSubobject (e ≫ h) = imageSubobject h := by
      intro X₁ X₂ X₃ e _ h
      have hle := imageSubobject_comp_le e h
      haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e h
      haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
      exact le_antisymm hle (Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
        (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm))
    have h_img_epi : imageSubobject (pullback.snd p K.arrow ≫ K.arrow) = K := by
      rw [h_img_epi_comp, imageSubobject_mono, Subobject.mk_arrow]
    calc K = imageSubobject (pullback.snd p K.arrow ≫ K.arrow) := h_img_epi.symm
      _ = imageSubobject (φ ≫ (kernelSubobject g).arrow ≫ p) := by rw [h_key_eq]
      _ ≤ imageSubobject ((kernelSubobject g).arrow ≫ p) :=
            imageSubobject_comp_le φ ((kernelSubobject g).arrow ≫ p)
  · -- (≥): image((ker g).arrow ≫ p) ≤ ker(epiDesc)
    apply le_kernelSubobject
    rw [← cancel_epi (factorThruImageSubobject ((kernelSubobject g).arrow ≫ p)),
        comp_zero, ← Category.assoc,
        imageSubobject_arrow_comp ((kernelSubobject g).arrow ≫ p),
        Category.assoc, Abelian.comp_epiDesc, kernelSubobject_arrow_comp]

set_option maxHeartbeats 800000 in
-- Heavy unification through cokernel desc and kernel subobject factoring
private theorem kernelSubobject_cokernel_desc' {C' : Type*} [Category C'] [Abelian C']
    {A' B' D' : C'} (f : A' ⟶ B') (g : B' ⟶ D') (w : f ≫ g = 0) :
    kernelSubobject (cokernel.desc f g w) =
      imageSubobject ((kernelSubobject g).arrow ≫ cokernel.π f) := by
  apply le_antisymm
  · -- (≤): ker(desc) ≤ image(ker(g).arrow ≫ cokernel.π f)
    -- Pullback argument: pull back π (epi) along K.arrow (mono) where K = ker(desc).
    -- The pullback P has:
    --   pullback.fst : P → B' (mono, since K.arrow is mono)
    --   pullback.snd : P → K (epi, since π is epi)
    -- Then fst ≫ g = fst ≫ π ≫ desc = snd ≫ K.arrow ≫ desc = 0,
    -- so fst factors through ker(g). This shows image(ker(g).arrow ≫ π) ⊇ K.
    set K := kernelSubobject (cokernel.desc f g w) with hK_def
    set π := cokernel.π f with hπ_def
    set desc' := cokernel.desc f g w with hdesc'_def
    -- Form the pullback of π and K.arrow
    have hpb_comm : pullback.fst π K.arrow ≫ π = pullback.snd π K.arrow ≫ K.arrow :=
      pullback.condition
    -- pullback.fst is mono (since K.arrow is mono)
    haveI : Mono (pullback.fst π K.arrow) :=
      pullback.fst_of_mono (f := π) (g := K.arrow)
    -- pullback.snd is epi (since π is epi, in abelian category)
    haveI : Epi (pullback.snd π K.arrow) :=
      Abelian.epi_pullback_of_epi_f π K.arrow
    -- Show pullback.fst ≫ g = 0, so it factors through ker(g)
    have h_fst_g_zero : pullback.fst π K.arrow ≫ g = 0 := by
      calc pullback.fst π K.arrow ≫ g
          = pullback.fst π K.arrow ≫ (π ≫ desc') := by rw [hπ_def, cokernel.π_desc]
        _ = (pullback.fst π K.arrow ≫ π) ≫ desc' := (Category.assoc _ _ _).symm
        _ = (pullback.snd π K.arrow ≫ K.arrow) ≫ desc' := by rw [hpb_comm]
        _ = pullback.snd π K.arrow ≫ (K.arrow ≫ desc') := Category.assoc _ _ _
        _ = pullback.snd π K.arrow ≫ 0 := by rw [kernelSubobject_arrow_comp]
        _ = 0 := comp_zero
    -- Factor through ker(g)
    set φ := factorThruKernelSubobject g (pullback.fst π K.arrow) h_fst_g_zero
    have hφ_spec : φ ≫ (kernelSubobject g).arrow = pullback.fst π K.arrow :=
      factorThruKernelSubobject_comp_arrow g _ _
    -- Key equation: φ ≫ ker(g).arrow ≫ π = pullback.snd ≫ K.arrow
    have h_key_eq : φ ≫ (kernelSubobject g).arrow ≫ π = pullback.snd π K.arrow ≫ K.arrow := by
      rw [show φ ≫ (kernelSubobject g).arrow ≫ π =
        (φ ≫ (kernelSubobject g).arrow) ≫ π from (Category.assoc _ _ _).symm,
        hφ_spec, hpb_comm]
    -- Now: image(pullback.snd ≫ K.arrow) = image(K.arrow) since pullback.snd is epi
    -- Use: imageSubobject(e ≫ m) = imageSubobject(m) when e is epi
    -- (inline proof since the helper in Basic.lean is private)
    have h_img_epi_comp : ∀ {X₁ X₂ X₃ : C'} (e : X₁ ⟶ X₂) [Epi e] (h : X₂ ⟶ X₃),
        imageSubobject (e ≫ h) = imageSubobject h := by
      intro X₁ X₂ X₃ e _ h
      have hle := imageSubobject_comp_le e h
      haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e h
      haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
      exact le_antisymm hle (Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
        (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm))
    have h_img_epi : imageSubobject (pullback.snd π K.arrow ≫ K.arrow) = K := by
      rw [h_img_epi_comp, imageSubobject_mono, Subobject.mk_arrow]
    -- Rewrite: image(φ ≫ ker(g).arrow ≫ π) = image(pullback.snd ≫ K.arrow) = K
    -- And: image(φ ≫ ker(g).arrow ≫ π) ≤ image(ker(g).arrow ≫ π) by imageSubobject_comp_le
    calc K = imageSubobject (pullback.snd π K.arrow ≫ K.arrow) := h_img_epi.symm
      _ = imageSubobject (φ ≫ (kernelSubobject g).arrow ≫ π) := by rw [h_key_eq]
      _ ≤ imageSubobject ((kernelSubobject g).arrow ≫ π) :=
            imageSubobject_comp_le φ ((kernelSubobject g).arrow ≫ π)
  · -- (≥): image(ker(g).arrow ≫ cokernel.π f) ≤ ker(desc)
    apply le_kernelSubobject
    rw [← cancel_epi (factorThruImageSubobject ((kernelSubobject g).arrow ≫ cokernel.π f)),
        comp_zero, ← Category.assoc,
        imageSubobject_arrow_comp ((kernelSubobject g).arrow ≫ cokernel.π f),
        Category.assoc, cokernel.π_desc, kernelSubobject_arrow_comp]

set_option maxHeartbeats 6400000 in
-- Long proof: d² = 0 requires nested kernel/image factoring across three filtration levels
theorem FilteredComplex.pageDifferential_comp (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    FC.pageDifferential bnd s k n ≫ FC.pageDifferential bnd (s + ↑n) (k - 1) n = 0 := by
  -- Step 1: Cancel epi cokernel.π(ofLE(B₁, Z₁))
  set f₁ := Subobject.ofLE (FC.boundarySubobject s k ↑n) (FC.cycleSubobject s k ↑n)
    (FC.B_le_Z_aux s k ↑n)
  haveI : Epi (cokernel.π f₁) := inferInstance
  rw [show FC.pageDifferential bnd s k n ≫ FC.pageDifferential bnd (s + ↑n) (k - 1) n =
    FC.pageDifferential bnd s k n ≫ FC.pageDifferential bnd (s + ↑n) (k - 1) n from rfl]
  rw [← cancel_epi (cokernel.π f₁), comp_zero, ← Category.assoc]
  erw [cokernel.π_desc]
  -- Step 2: Cancel epi p₁ = factorThruImageSubobject(kerZ₁.arrow ≫ πV₁)
  set f_n₁ := (FC.fil s k).arrow ≫ FC.d k ≫ cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow)
  set kerZ₁ := kernelSubobject f_n₁
  set ι₁ := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
  set πV₁ := cokernel.π ι₁
  set p₁ := factorThruImageSubobject (kerZ₁.arrow ≫ πV₁)
  haveI : Epi p₁ := inferInstance
  rw [← cancel_epi p₁, comp_zero, ← Category.assoc]
  erw [Abelian.comp_epiDesc]
  -- Step 3: pageπ_mid ≫ pageDiff₂ = h_on_Zn₂ via cokernel.π_desc
  rw [Category.assoc]
  erw [cokernel.π_desc]
  -- Step 4: Cancel epi p₂ via Abelian.comp_epiDesc
  rw [Category.assoc]
  erw [Abelian.comp_epiDesc]
  -- After 4 epi cancellations, the goal has the form:
  --   fTKS₁ ≫ ((fTKS₂ ≫ fTIS₂) ≫ pageπ₃) = 0
  -- Normalize association fully to the right using simp only [Category.assoc]:
  simp only [Category.assoc]
  -- Now goal: fTKS₁ ≫ (fTKS₂ ≫ (fTIS₂ ≫ pageπ₃)) = 0
  -- Strategy: show fTKS₁ ≫ fTKS₂ = 0 (via d²=0), then use reassoc_of%.
  -- fTKS₁ : factorThruKernelSubobject(f_mid, lift_n₁, _)
  -- fTKS₂ : factorThruKernelSubobject(f₃, lift_n₂, _)
  -- fTKS₁ ≫ fTKS₂ ≫ kerZ₃.arrow = fTKS₁ ≫ lift_n₂
  --   = fTKS₁ ≫ monoLift(fil₃, kerZ_mid.arrow ≫ fil_mid.arrow ≫ d(k-1))
  -- fTKS₁ ≫ lift_n₂ ≫ fil₃.arrow = fTKS₁ ≫ kerZ_mid.arrow ≫ fil_mid.arrow ≫ d(k-1)
  --   = lift_n₁ ≫ fil_mid.arrow ≫ d(k-1)
  --   = kerZ₁.arrow ≫ fil₁.arrow ≫ d(k) ≫ d(k-1) = 0 by d_comp_d
  -- After 4 epi cancellations and simp, goal:
  --   fTKS₁ ≫ fTKS₂ ≫ fTIS₂ ≫ pageπ₃ = 0  (fully right-associated)
  -- Reassociate the first two to (fTKS₁ ≫ fTKS₂) ≫ rest using erw:
  erw [show ∀ {A' B' C' D' : C} (f : A' ⟶ B') (g : B' ⟶ C') (h : C' ⟶ D'),
    f ≫ (g ≫ h) = (f ≫ g) ≫ h from fun f g h => (Category.assoc f g h).symm]
  -- Now goal: (fTKS₁ ≫ fTKS₂) ≫ (fTIS₂ ≫ pageπ₃) = 0
  -- Suffices: fTKS₁ ≫ fTKS₂ = 0 (target of fTKS₂ is the same as source of fTIS₂)
  suffices h_zero : _ ≫ _ = (0 : _ ⟶ Subobject.underlying.obj (kernelSubobject
    ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow ≫ FC.d (k - 1 - 1) ≫
      cokernel.π ((FC.fil (s + ↑n + ↑n + ↑n) (k - 1 - 1 - 1)).arrow)))) by
    erw [h_zero, zero_comp]
  -- Goal: fTKS₁ ≫ fTKS₂ = 0
  -- Mono-cancel through (kernelSubobject f₃).arrow
  apply (inferInstance : Mono (kernelSubobject
    ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow ≫ FC.d (k - 1 - 1) ≫
      cokernel.π ((FC.fil (s + ↑n + ↑n + ↑n) (k - 1 - 1 - 1)).arrow))).arrow).right_cancellation
  simp only [zero_comp, Category.assoc]
  erw [factorThruKernelSubobject_comp_arrow]
  -- Goal: fTKS₁ ≫ lift_n₂ = 0 where
  -- lift_n₂ = Abelian.monoLift(fil₃, kerZ_mid.arrow ≫ fil_mid.arrow ≫ d(k-1), _)
  -- Mono-cancel through (FC.fil (s+n+n) (k-1-1)).arrow
  apply (inferInstance : Mono (FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow).right_cancellation
  simp only [zero_comp, Category.assoc]
  erw [Abelian.monoLift_comp]
  -- Goal: fTKS₁ ≫ kerZ_mid.arrow ≫ fil_mid.arrow ≫ d(k-1) = 0
  -- i.e., fTKS₁ ≫ (kerZ_mid.arrow ≫ (fil_mid.arrow ≫ FC.d (k-1))) = 0
  -- After mono cancellation, we need fTKS₁ ≫ kerZ_mid.arrow = lift_n₁
  -- and lift_n₁ ≫ fil_mid.arrow = kerZ₁.arrow ≫ fil.arrow ≫ d(k).
  -- Use conv to reassociate without motive issues:
  -- Step A: Mono-cancel through (kernelSubobject f_mid).arrow
  -- to reduce to showing fTKS₁ ≫ lift_n₁ chain = 0
  -- Actually, erw/rw [← Category.assoc] fails with motive errors.
  -- Instead, directly compose the entire chain via mono cancellation.
  -- After erw [Abelian.monoLift_comp], the fTKS₁ term contains
  -- `factorThruKernelSubobject(f_mid, lift_n₁, _)` and kerZ_mid = kernelSubobject f_mid.
  -- So goal = fTKS₁ ≫ (kerZ_mid.arrow ≫ (fil_mid.arrow ≫ d(k-1))) = 0.
  -- Convert to a single chain using conv + erw:
  conv_lhs => erw [← Category.assoc, factorThruKernelSubobject_comp_arrow]
  -- Goal: lift_n₁ ≫ (fil_mid.arrow ≫ d(k-1)) = 0
  conv_lhs => erw [← Category.assoc, Abelian.monoLift_comp]
  -- Goal: (kerZ₁.arrow ≫ fil.arrow ≫ d(k)) ≫ d(k-1) = 0
  -- = (kerZ₁.arrow ≫ (fil.arrow ≫ d(k))) ≫ d(k-1) = 0
  -- Use erw [Category.assoc] twice to fully right-associate, then d_comp_d k
  erw [Category.assoc, Category.assoc, FC.d_comp_d k, comp_zero, comp_zero]

set_option maxHeartbeats 3200000 in
-- Multi-step proof: Z_{n+1} ↪ Z_n maps to kernel of page differential via index shifting
/-- The ≥ direction of Z_succ: image(ofLE(Z_{n+1}, Z_n) ≫ pageπ n) ≤ kernel(pageDifferential).
    Elements of Z_{n+1} (deeper cycle condition: dx ∈ F^{s+n+1}) map to zero under pageDiff
    because their d-image lands in F^{s+n+1}, hence projects to 0 in gr^{s+n}. -/
theorem pageDifferential_Z_succ_ge (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    imageSubobject (
      Subobject.ofLE ((FC.toSSData bnd s k).Z ↑(n + 1)) ((FC.toSSData bnd s k).Z ↑n)
        ((FC.toSSData bnd s k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
      (FC.toSSData bnd s k).pageπ ↑n) ≤
    kernelSubobject (FC.pageDifferential bnd s k n) := by
  -- It suffices to show: ofLE(Z_{n+1}, Z_n) ≫ pageπ n ≫ pageDiff = 0
  -- Then the imageSubobject of (ofLE ≫ pageπ) has arrow killing pageDiff.
  apply le_kernelSubobject
  -- Goal: (imageSubobject(ofLE ≫ pageπ)).arrow ≫ pageDiff = 0
  -- Factor: imageSubobject(f).arrow = factorThruImage(f)⁻¹ (not quite)
  -- Use: factorThruImage(f) is epi and factorThruImage(f) ≫ imageSubobject(f).arrow = f.
  -- So imageSubobject(f).arrow ≫ g = 0 ↔ (cancel epi factorThruImage(f)) f ≫ g = 0.
  set ofLE_pageπ := Subobject.ofLE ((FC.toSSData bnd s k).Z ↑(n + 1))
    ((FC.toSSData bnd s k).Z ↑n)
    ((FC.toSSData bnd s k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
    (FC.toSSData bnd s k).pageπ ↑n with h_ofLE_pageπ
  rw [← cancel_epi (factorThruImageSubobject ofLE_pageπ), comp_zero,
    ← Category.assoc, imageSubobject_arrow_comp]
  -- Goal: ofLE_pageπ ≫ pageDiff = 0
  -- = ofLE(Z_{n+1}, Z_n) ≫ pageπ n ≫ pageDiff = 0
  rw [h_ofLE_pageπ, Category.assoc]
  -- Use: pageπ n ≫ pageDiff = h_on_Zn (definitionally, since pageDiff = cokernel.desc _ h_on_Zn _)
  erw [cokernel.π_desc]
  -- Goal: ofLE(Z_{n+1}, Z_n) ≫ h_on_Zn = 0
  -- h_on_Zn = Abelian.epiDesc(p, ψ, _). Cancel epi p1 on the left.
  set f_n := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow)
  set kerZ := kernelSubobject f_n
  set ι_s := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
  set πV := cokernel.π ι_s
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV)
  haveI : Epi p := inferInstance
  set f_n1 := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow)
  set kerZ1 := kernelSubobject f_n1
  set p1 := factorThruImageSubobject (kerZ1.arrow ≫ πV)
  haveI : Epi p1 := inferInstance
  rw [← cancel_epi p1, comp_zero]
  -- Goal: p1 ≫ ofLE(Z_{n+1}, Z_n) ≫ h_on_Zn = 0
  -- Key identity: p1 ≫ ofLE(Z_{n+1}, Z_n) = β ≫ p where β = ofLE(kerZ1, kerZ)
  have hkerZ1_le : kerZ1 ≤ kerZ := by
    apply le_kernelSubobject
    have hfil : FC.fil (s + ↑(n + 1)) (k - 1) ≤ FC.fil (s + ↑n) (k - 1) :=
      FC.fil_anti_of_le (k - 1) (by omega)
    -- kerZ1.arrow ≫ f_n = (kerZ1.arrow ≫ F^s.arrow ≫ d k) ≫ cokernel.π(F^{s+n}.arrow)
    -- kerZ1 kills f_n1, so d-image ∈ F^{s+n+1} ≤ F^{s+n}, hence ≫ cokernel.π(F^{s+n}) = 0
    have h1 : kerZ1.arrow ≫ f_n1 = 0 := kernelSubobject_arrow_comp f_n1
    -- d-image of kerZ1 factors through F^{s+n+1}
    have h1' : (kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
        cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      simp only [Category.assoc] at h1 ⊢; exact h1
    set dk_im := kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k
    set lift1 := Abelian.monoLift (FC.fil (s + ↑(n + 1)) (k - 1)).arrow dk_im h1'
    calc kerZ1.arrow ≫ f_n
        = dk_im ≫ cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) := by
          simp only [f_n, dk_im, Category.assoc]
      _ = (lift1 ≫ (FC.fil (s + ↑(n + 1)) (k - 1)).arrow) ≫
            cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) := by
          rw [Abelian.monoLift_comp]
      _ = lift1 ≫ (Subobject.ofLE _ _ hfil ≫ (FC.fil (s + ↑n) (k - 1)).arrow) ≫
            cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) := by
          rw [show (FC.fil (s + ↑(n + 1)) (k - 1)).arrow =
            Subobject.ofLE _ _ hfil ≫ (FC.fil (s + ↑n) (k - 1)).arrow
            from (Subobject.ofLE_arrow hfil).symm]; simp only [Category.assoc]
      _ = 0 := by
          simp only [Category.assoc, cokernel.condition, comp_zero]
  set β := Subobject.ofLE kerZ1 kerZ hkerZ1_le
  -- Prove p1 ≫ ofLE(Z_{n+1}, Z_n) = β ≫ p by mono-cancellation on Z_n.arrow
  have h_factor : p1 ≫ Subobject.ofLE ((FC.toSSData bnd s k).Z ↑(n + 1))
      ((FC.toSSData bnd s k).Z ↑n)
      ((FC.toSSData bnd s k).Z_anti (by exact_mod_cast Nat.le_succ n)) = β ≫ p := by
    apply (inferInstance : Mono ((FC.toSSData bnd s k).Z ↑n).arrow).right_cancellation
    simp only [Category.assoc]
    -- LHS: p1 ≫ ofLE(Z_{n+1}, Z_n) ≫ Z_n.arrow = p1 ≫ Z_{n+1}.arrow = kerZ1.arrow ≫ πV
    -- RHS: β ≫ p ≫ Z_n.arrow = β ≫ kerZ.arrow ≫ πV = kerZ1.arrow ≫ πV
    -- Unfold set-names and use imageSubobject_arrow_comp + ofLE_arrow
    simp only [p1, p, β]
    rw [Subobject.ofLE_arrow]
    erw [imageSubobject_arrow_comp, imageSubobject_arrow_comp]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  -- Now use h_factor: p1 ≫ ofLE = β ≫ p to rewrite
  -- Need reassociated form since the target is fully right-associated
  -- h_factor_assoc: p1 ≫ ofLE ≫ X = β ≫ p ≫ X for any X
  rw [show p1 ≫ _ = (p1 ≫ _) ≫ _ from (Category.assoc _ _ _).symm]
  rw [h_factor]
  rw [Category.assoc]
  -- Goal: β ≫ (p ≫ h_on_Zn) = 0
  -- p ≫ h_on_Zn = ψ (by Abelian.comp_epiDesc)
  -- Don't use erw [Abelian.comp_epiDesc] - erw corrupts internal terms.
  -- Use rw which preserves term structure:
  rw [Abelian.comp_epiDesc]
  -- Goal: β ≫ ψ = 0 where ψ = (to_Z_n_t) ≫ pageπ'
  set ι_t := Subobject.ofLE (FC.fil (s + ↑n + 1) (k - 1)) (FC.fil (s + ↑n) (k - 1))
    (FC.fil_anti (s + ↑n) (k - 1))
  set πV' := cokernel.π ι_t
  -- Suffices: β ≫ to_Z_n_t = 0, then β ≫ ψ = (β ≫ to_Z_n_t) ≫ pageπ' = 0 ≫ pageπ' = 0
  suffices h : β ≫ _ = (0 : _ ⟶ Subobject.underlying.obj
    (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)) by
    rw [show β ≫ (_ ≫ _) = (β ≫ _) ≫ _ from (Category.assoc β _ _).symm]
    rw [h, zero_comp]
  -- Now: β ≫ to_Z_n_t = 0
  apply (inferInstance : Mono (FC.cycleSubobject (s + ↑n) (k - 1) ↑n).arrow).right_cancellation
  rw [zero_comp]
  -- Goal: β ≫ to_Z_n_t ≫ cycleSubobject.arrow = 0
  simp only [Category.assoc]
  unfold FilteredComplex.cycleSubobject
  push_cast
  simp only [imageSubobject_arrow_comp]
  -- factorThruKernelSubobject_comp_arrow fails due to erw pollution from cokernel.π_desc.
  -- The factorThruKernelSubobject and kernelSubobject have the same 'f' in the pretty-printer
  -- but differ internally. Work around by using the unfold approach:
  simp only [factorThruKernelSubobject]
  -- Goal: β ≫ factorThru(P, monoLift, w) ≫ P.arrow ≫ πV' = 0
  -- P = kernelSubobject(f') but the P in factorThru and P in arrow may differ internally.
  -- Since the type of factorThru ≫ arrow typechecks, they share the same underlying obj.
  -- Use Subobject.factorThru_arrow as a have:
  set f' := (FC.fil (s + ↑n) (k - 1)).arrow ≫ FC.d (k - 1) ≫
    cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) with hf'_def
  set ml := Abelian.monoLift (FC.fil (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k)
    (by simp only [Category.assoc]; exact kernelSubobject_arrow_comp f_n) with hml_def
  -- Now β ≫ factorThru(kerSub f', ml, _) ≫ (kerSub f').arrow ≫ πV' = 0
  -- factorThru_arrow: factorThru(kerSub f', ml, _) ≫ (kerSub f').arrow = ml
  -- Try rw with the explicit f':
  -- NOTE: The goal after push_cast + simp [imageSubobject_arrow_comp] is:
  -- β ≫ factorThru(P, ml, w) ≫ P'.arrow ≫ πV' = 0
  -- where P and P' are propositionally equal kernelSubobject instances that differ
  -- internally due to erw [cokernel.π_desc] pollution.
  -- factorThru_arrow cannot be applied by rw/simp/erw because the subobjects don't match.
  -- The mathematical proof: β ≫ ml ≫ πV' = 0 because β ≫ ml factors through
  -- F^{s+n+1} ≤ F^{s+n} and ofLE(F^{s+n+1}, F^{s+n}) ≫ πV' = 0 (cokernel condition).
  -- The goal is:
  -- β ≫ (kernelSubobject f'_expr).factorThru (monoLift ...) ⋯ ≫
  --     (kernelSubobject f'_expr).arrow ≫ πV' = 0
  -- Both kernelSubobject instances use the same f' expression.
  -- factorThru_arrow: P.factorThru h w ≫ P.arrow = h
  -- Try slice_lhs to isolate factorThru ≫ arrow
  -- The goal is β ≫ P.factorThru(ml, w) ≫ P.arrow ≫ πV' = 0
  -- where P = kernelSubobject f'. But erw/rw can't match factorThru_arrow.
  -- Use have + Mono.right_cancellation on P.arrow to replace factorThru with ml.
  -- Actually: P.factorThru(ml, w) is the unique map through P such that
  -- P.factorThru(ml, w) ≫ P.arrow = ml. This holds by factorThru_arrow.
  -- But the P in factorThru and P in .arrow must be the same for this to work.
  -- Since they print the same but erw can't match, they differ in proof terms.
  -- New approach: show the goal by converting to a statement about `ml ≫ πV'` directly.
  -- Use have : P.factorThru(ml, w) ≫ P.arrow = ml for the P that factorThru uses.
  -- Step 1: Extract the factorThru subobject using set
  -- The P in factorThru and P in .arrow differ internally (erw pollution)
  -- but both kernelSubobjects are for the same morphism, so they're propositionally equal.
  -- The goal is: β ≫ P.factorThru(ml, w) ≫ P'.arrow ≫ πV' = 0
  -- Strategy: show it's equal to β ≫ ml ≫ πV' = 0, then prove the latter.
  -- Use `convert` to match against β ≫ ml ≫ πV' = 0.
  suffices h_main : β ≫ ml ≫ πV' = 0 by
    convert h_main using 2
    -- Goal: P.factorThru(ml_expr, w) ≫ P.arrow ≫ πV' = ml ≫ πV'
    rw [show (_ : Subobject.underlying.obj _ ⟶ _) ≫ _ ≫ πV' = (_ ≫ _) ≫ πV'
      from (Category.assoc _ _ _).symm, Subobject.factorThru_arrow]
  -- Now: β ≫ ml ≫ πV' = 0
  -- Strategy: β ≫ ml ≫ F^{s+n}.arrow = kerZ1.arrow ≫ F^s.arrow ≫ d(k)
  -- which factors through F^{s+n+1}(k-1), and then ≫ πV' = 0 by cokernel.condition.
  -- Avoid problematic rw by using Mono.right_cancellation and calc chains.
  --
  -- Step 1: kerZ1.arrow ≫ F^s.arrow ≫ d(k) factors through F^{s+↑(n+1)}(k-1)
  have h_kerZ1_factor : (kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
      cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc]
    exact kernelSubobject_arrow_comp f_n1
  set lift_n1 := Abelian.monoLift (FC.fil (s + ↑(n + 1)) (k - 1)).arrow
    (kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) h_kerZ1_factor
  have h_lift_n1_spec : lift_n1 ≫ (FC.fil (s + ↑(n + 1)) (k - 1)).arrow =
      kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k :=
    Abelian.monoLift_comp _ _ _
  -- Step 2: β ≫ ml ≫ F^{s+n}.arrow = lift_n1 ≫ F^{s+↑(n+1)}.arrow
  have hfil_le_nat : FC.fil (s + ↑(n + 1)) (k - 1) ≤ FC.fil (s + ↑n) (k - 1) :=
    FC.fil_anti_of_le (k - 1) (by omega)
  -- Both sides equal kerZ1.arrow ≫ F^s.arrow ≫ d(k)
  -- Use Mono.right_cancellation on F^{s+n}.arrow to get β ≫ ml = lift_n1 ≫ ofLE
  have h_β_ml_eq : β ≫ ml = lift_n1 ≫ Subobject.ofLE _ _ hfil_le_nat := by
    apply (inferInstance : Mono (FC.fil (s + ↑n) (k - 1)).arrow).right_cancellation
    -- LHS: β ≫ ml ≫ F^{s+n}.arrow
    -- RHS: lift_n1 ≫ ofLE ≫ F^{s+n}.arrow = lift_n1 ≫ F^{s+↑(n+1)}.arrow
    -- Both = kerZ1.arrow ≫ F^s.arrow ≫ d(k)
    -- Compute LHS via monoLift_comp + ofLE_arrow:
    --   β ≫ ml ≫ F^{s+n}.arrow
    --   = β ≫ (kerZ.arrow ≫ F^s.arrow ≫ d(k))    [ml_def + monoLift_comp]
    --   = (β ≫ kerZ.arrow) ≫ F^s.arrow ≫ d(k)    [assoc]
    --   = kerZ1.arrow ≫ F^s.arrow ≫ d(k)           [ofLE_arrow]
    -- Compute RHS:
    --   lift_n1 ≫ ofLE ≫ F^{s+n}.arrow
    --   = lift_n1 ≫ F^{s+↑(n+1)}.arrow             [ofLE_arrow]
    --   = kerZ1.arrow ≫ F^s.arrow ≫ d(k)           [lift_n1_spec]
    -- Instead of rw which may fail due to pollution, use calc:
    have h_ml_arrow : ml ≫ (FC.fil (s + ↑n) (k - 1)).arrow =
        kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k := by
      simp only [hml_def]; exact Abelian.monoLift_comp _ _ _
    calc (β ≫ ml) ≫ (FC.fil (s + ↑n) (k - 1)).arrow
        = β ≫ (ml ≫ (FC.fil (s + ↑n) (k - 1)).arrow) := Category.assoc _ _ _
      _ = β ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) := by rw [h_ml_arrow]
      _ = (β ≫ kerZ.arrow) ≫ (FC.fil s k).arrow ≫ FC.d k := by
          simp only [Category.assoc]
      _ = kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k := by
          rw [Subobject.ofLE_arrow hkerZ1_le]
      _ = lift_n1 ≫ (FC.fil (s + ↑(n + 1)) (k - 1)).arrow := h_lift_n1_spec.symm
      _ = lift_n1 ≫ (Subobject.ofLE _ _ hfil_le_nat ≫
            (FC.fil (s + ↑n) (k - 1)).arrow) := by rw [Subobject.ofLE_arrow]
      _ = (lift_n1 ≫ Subobject.ofLE _ _ hfil_le_nat) ≫
            (FC.fil (s + ↑n) (k - 1)).arrow := (Category.assoc _ _ _).symm
  -- Step 3: (β ≫ ml) ≫ πV' = (lift_n1 ≫ ofLE) ≫ πV' = lift_n1 ≫ ofLE ≫ πV'
  -- and ofLE ≫ πV' = 0 because πV' = cokernel.π(ι_t) and ofLE ≫ F^{s+n}.arrow = ι_t ≫ F^{s+n}.arrow
  -- More directly: Subobject.ofLE(F^{s+↑(n+1)}, F^{s+n}) ≫ πV' = 0
  -- because πV' = cokernel.π of the inclusion of F^{s+↑n+1} into F^{s+n}
  -- and ofLE factors through that inclusion.
  rw [show β ≫ ml ≫ πV' = (β ≫ ml) ≫ πV' from (Category.assoc _ _ _).symm,
    h_β_ml_eq, Category.assoc]
  -- Goal: lift_n1 ≫ Subobject.ofLE(F^{s+↑(n+1)}, F^{s+n}) ≫ πV' = 0
  -- s + ↑(n+1) = s + ↑n + 1, so ofLE factors through ι_t and cokernel kills it.
  suffices h_zero : Subobject.ofLE _ _ hfil_le_nat ≫ πV' = 0 by
    rw [h_zero, comp_zero]
  -- Factor ofLE through ι_t using transitivity
  have h_idx_eq : (s : ℤ) + ↑(n + 1) = s + ↑n + 1 := by push_cast; ring
  have h_le_ι_source : FC.fil (s + ↑(n + 1)) (k - 1) ≤ FC.fil (s + ↑n + 1) (k - 1) := by
    rw [h_idx_eq]
  -- ofLE(hfil_le_nat) = ofLE(h_le_ι_source) ≫ ofLE(fil_anti) = ofLE(h_le_ι_source) ≫ ι_t
  have h_factored : Subobject.ofLE _ _ hfil_le_nat =
      Subobject.ofLE _ _ h_le_ι_source ≫ ι_t := by
    symm
    exact Subobject.ofLE_comp_ofLE (FC.fil (s + ↑(n + 1)) (k - 1))
      (FC.fil (s + ↑n + 1) (k - 1)) (FC.fil (s + ↑n) (k - 1))
      h_le_ι_source (FC.fil_anti (s + ↑n) (k - 1))
  rw [h_factored, Category.assoc, cokernel.condition, comp_zero]

open CategoryTheory.Abelian in
/-- `imageSubobject (e ≫ f) = imageSubobject f` when `e` is epi (in an abelian category). -/
private lemma imageSubobject_epi_comp' {C' : Type*} [Category C'] [Abelian C']
    {X₁ X₂ X₃ : C'} (e : X₁ ⟶ X₂) [Epi e] (f : X₂ ⟶ X₃) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  apply le_antisymm (imageSubobject_comp_le e f)
  have hle := imageSubobject_comp_le e f
  haveI : Epi (Subobject.ofLE _ _ hle) := imageSubobject_comp_le_epi_of_epi e f
  haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi _
  exact Subobject.le_of_comm (inv (Subobject.ofLE _ _ hle))
    (by rw [IsIso.inv_comp_eq]; exact (Subobject.ofLE_arrow hle).symm)

open CategoryTheory.Abelian in
/-- If `e` is epi and `e ≫ f = h ≫ g`, then `imageSubobject f ≤ imageSubobject g`. -/
private lemma imageSubobject_le_of_epi_factor {C' : Type*} [Category C'] [Abelian C']
    {W X Y Z : C'} (e : W ⟶ X) [Epi e] (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Y)
    (hfac : e ≫ f = h ≫ g) :
    imageSubobject f ≤ imageSubobject g := by
  rw [← imageSubobject_epi_comp' e f, hfac]
  exact imageSubobject_comp_le h g

set_option maxHeartbeats 6400000 in
-- Long proof: kernel of page differential ≤ Z_{n+1} via pullback and epi lifting arguments
/-- The ≤ direction of Z_succ: kernel(pageDifferential) ≤ image(ofLE(Z_{n+1}, Z_n) ≫ pageπ n).
    Every element in the kernel of the page differential lies in the image of the deeper
    cycle subobject. Proved by computing the kernel via `kernelSubobject_cokernel_desc'`
    and `kernelSubobject_epiDesc'`, then constructing a factorization through Z_{n+1}
    using pullback + correction. -/
theorem pageDifferential_Z_succ_le (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    kernelSubobject (FC.pageDifferential bnd s k n) ≤
    imageSubobject (
      Subobject.ofLE ((FC.toSSData bnd s k).Z ↑(n + 1)) ((FC.toSSData bnd s k).Z ↑n)
        ((FC.toSSData bnd s k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
      (FC.toSSData bnd s k).pageπ ↑n) := by
  -- Reconstruct the internal abbreviations of pageDifferential
  set ι_s := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k) with hι_s_def
  set πV := cokernel.π ι_s with hπV_def
  set f_n := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) with hf_n_def
  set kerZ := kernelSubobject f_n with hkerZ_def
  set ι_t := Subobject.ofLE (FC.fil (s + ↑n + 1) (k - 1)) (FC.fil (s + ↑n) (k - 1))
    (FC.fil_anti (s + ↑n) (k - 1)) with hι_t_def
  set πV' := cokernel.π ι_t with hπV'_def
  set f_n' := (FC.fil (s + ↑n) (k - 1)).arrow ≫ FC.d (k - 1) ≫
    cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) with hf_n'_def
  set kerZ' := kernelSubobject f_n' with hkerZ'_def
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV) with hp_def
  haveI hp_epi : Epi p := inferInstance
  -- Reconstruct lift_n, lift_to_kerZ', to_Z_n_t, ψ
  have h_ker_fn : kerZ.arrow ≫ f_n = 0 := kernelSubobject_arrow_comp f_n
  have h_factor_zero : (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
      cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc] at h_ker_fn ⊢; exact h_ker_fn
  set lift_n := Abelian.monoLift (FC.fil (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) h_factor_zero with hlift_n_def
  have h_lift_spec : lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow =
      kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k := Abelian.monoLift_comp _ _ _
  have h_lift_in_kerZ' : lift_n ≫ f_n' = 0 := by
    calc lift_n ≫ f_n'
        = ((lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) ≫ FC.d (k - 1)) ≫
            cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          simp only [hf_n'_def, Category.assoc]
      _ = ((kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫ FC.d (k - 1)) ≫
            cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by rw [h_lift_spec]
      _ = 0 := by
          rw [show (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫ FC.d (k - 1) =
            kerZ.arrow ≫ (FC.fil s k).arrow ≫ (FC.d k ≫ FC.d (k - 1)) from by
            simp only [Category.assoc], FC.d_comp_d k]; simp only [comp_zero, zero_comp]
  set lift_to_kerZ' := factorThruKernelSubobject f_n' lift_n h_lift_in_kerZ'
    with hlift_to_kerZ'_def
  have h_ltk_spec : lift_to_kerZ' ≫ kerZ'.arrow = lift_n :=
    factorThruKernelSubobject_comp_arrow f_n' lift_n h_lift_in_kerZ'
  set to_Z_n_t := lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')
    with hto_Z_n_t_def
  set pageπ_t := (FC.toSSData bnd (s + ↑n) (k - 1)).pageπ ↑n with hpageπ_t_def
  set ψ := to_Z_n_t ≫ pageπ_t with hψ_def
  -- Phase A: Establish kernelSubobject(pageDiff) = imageSubobject((ker ψ).arrow ≫ p ≫ pageπ)
  -- Use erw in a have block to contain the pollution
  have h_ker_le : kernelSubobject (FC.pageDifferential bnd s k n) ≤
      imageSubobject ((kernelSubobject ψ).arrow ≫ p ≫ (FC.toSSData bnd s k).pageπ ↑n) := by
    erw [kernelSubobject_cokernel_desc']
    erw [kernelSubobject_epiDesc']
    -- Goal: imageSubobject(imageSubobject(f).arrow ≫ pageπ) ≤ imageSubobject(f ≫ pageπ)
    -- where f = (ker ψ_internal).arrow ≫ p_internal.
    -- These are equal by imageSubobject_epi_comp', so use le_of_eq.
    -- First get: imageSubobject(factorThru ≫ img.arrow ≫ pageπ) = imageSubobject(img.arrow ≫ pageπ)
    -- and factorThru ≫ img.arrow ≫ pageπ = (factorThru ≫ img.arrow) ≫ pageπ = f ≫ pageπ
    -- Use: factorThruImageSubobject(f) is epi, and
    -- imageSubobject_epi_comp'(factorThru, img.arrow ≫ g) gives
    -- imageSubobject(factorThru ≫ img.arrow ≫ g) = imageSubobject(img.arrow ≫ g)
    -- And factorThru ≫ img.arrow = f (imageSubobject_arrow_comp), so
    -- imageSubobject(f ≫ g) = imageSubobject(img.arrow ≫ g)
    -- After erw, the LHS has imageSubobject(img.arrow ≫ g), and the RHS has
    -- imageSubobject(f ≫ g). They're equal, so any ≤ or ≥ holds.
    -- Use the Subobject.le_of_comm approach to avoid rw in polluted context.
    -- imageSubobject(img.arrow ≫ g) ≤ imageSubobject(f ≫ g) because
    -- imageSubobject(f ≫ g) ≤ imageSubobject(img.arrow ≫ g) [from comp_le applied to factorThru]
    -- Wait, imageSubobject(factorThru ≫ (img.arrow ≫ g)) ≤ imageSubobject(img.arrow ≫ g) [comp_le]
    -- and imageSubobject(factorThru ≫ (img.arrow ≫ g)) = imageSubobject(img.arrow ≫ g) [epi_comp]
    -- So both directions hold. For the direction we need:
    -- imageSubobject(img.arrow ≫ g) ≤ imageSubobject(f ≫ g)
    -- = imageSubobject(factorThru ≫ img.arrow ≫ g) [by imageSubobject_arrow_comp on f]
    -- = imageSubobject(img.arrow ≫ g) [by epi_comp]
    -- So it's le_refl. But we can't express this directly due to erw pollution.
    -- Instead, use that mono.arrow ≫ g generates a smaller image: img.arrow is mono
    -- so imageSubobject(img.arrow ≫ g) ≤ imageSubobject(g) [comp_le]
    -- Hmm, that's weaker than what we need.
    -- OK, just try: after the three erw's, does the goal close?
    -- Approach: do all three erw's and hope it results in ≤ le_refl
    erw [← imageSubobject_epi_comp'
      (factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p))
      ((imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow ≫
        (FC.toSSData bnd s k).pageπ ↑n)]
    -- Goal: imageSubobject(factorThru ≫ img.arrow ≫ pageπ) ≤ imageSubobject(f ≫ pageπ)
    -- factorThru ≫ img.arrow ≫ pageπ is parsed as factorThru ≫ (img.arrow ≫ pageπ)
    -- We need: factorThru ≫ (img.arrow ≫ pageπ) = (factorThru ≫ img.arrow) ≫ pageπ = f ≫ pageπ
    erw [show factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p) ≫
      (imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow ≫
      (FC.toSSData bnd s k).pageπ ↑n =
      (factorThruImageSubobject ((kernelSubobject ψ).arrow ≫ p) ≫
      (imageSubobject ((kernelSubobject ψ).arrow ≫ p)).arrow) ≫
      (FC.toSSData bnd s k).pageπ ↑n from (Category.assoc _ _ _).symm,
      imageSubobject_arrow_comp ((kernelSubobject ψ).arrow ≫ p),
      Category.assoc]
  -- Phase B: Show imageSubobject((ker ψ).arrow ≫ p ≫ pageπ) ≤ imageSubobject(ofLE ≫ pageπ)
  apply le_trans h_ker_le
  -- Goal: imageSubobject((ker ψ).arrow ≫ p ≫ pageπ) ≤ imageSubobject(ofLE ≫ pageπ)

  -- === Setup: kerZ1 (deeper cycles), β : kerZ1 → kerZ, p1, h_factor ===
  set f_n1 := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) with hf_n1_def
  set kerZ1 := kernelSubobject f_n1 with hkerZ1_def
  have hkerZ1_le : kerZ1 ≤ kerZ := by
    apply le_kernelSubobject
    have hfil : FC.fil (s + ↑(n + 1)) (k - 1) ≤ FC.fil (s + ↑n) (k - 1) :=
      FC.fil_anti_of_le (k - 1) (by omega)
    have h1' : (kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
        cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      simp only [Category.assoc]; exact kernelSubobject_arrow_comp f_n1
    set lift1 := Abelian.monoLift (FC.fil (s + ↑(n + 1)) (k - 1)).arrow
      (kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) h1'
    calc kerZ1.arrow ≫ f_n
        = (kerZ1.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
            cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) := by
          simp only [f_n, Category.assoc]
      _ = (lift1 ≫ (FC.fil (s + ↑(n + 1)) (k - 1)).arrow) ≫
            cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) := by
          rw [Abelian.monoLift_comp]
      _ = lift1 ≫ (Subobject.ofLE _ _ hfil ≫ (FC.fil (s + ↑n) (k - 1)).arrow) ≫
            cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) := by
          rw [show (FC.fil (s + ↑(n + 1)) (k - 1)).arrow =
            Subobject.ofLE _ _ hfil ≫ (FC.fil (s + ↑n) (k - 1)).arrow
            from (Subobject.ofLE_arrow hfil).symm]; simp only [Category.assoc]
      _ = 0 := by simp only [Category.assoc, cokernel.condition, comp_zero]
  set β := Subobject.ofLE kerZ1 kerZ hkerZ1_le with hβ_def
  set p1 := factorThruImageSubobject (kerZ1.arrow ≫ πV) with hp1_def
  haveI hp1_epi : Epi p1 := inferInstance
  have h_factor : p1 ≫ Subobject.ofLE ((FC.toSSData bnd s k).Z ↑(n + 1))
      ((FC.toSSData bnd s k).Z ↑n)
      ((FC.toSSData bnd s k).Z_anti (by exact_mod_cast Nat.le_succ n)) = β ≫ p := by
    apply (inferInstance : Mono ((FC.toSSData bnd s k).Z ↑n).arrow).right_cancellation
    simp only [Category.assoc, p1, p, β]
    rw [Subobject.ofLE_arrow]
    erw [imageSubobject_arrow_comp, imageSubobject_arrow_comp]
    rw [← Category.assoc, Subobject.ofLE_arrow]
  -- Key abbreviation: h_p_Z
  have h_p_Z : p ≫ ((FC.toSSData bnd s k).Z ↑n).arrow = kerZ.arrow ≫ πV :=
    imageSubobject_arrow_comp (kerZ.arrow ≫ πV)
  -- === Step 1: Factor (ker ψ).arrow ≫ to_Z_n_t through ker(pageπ_t) ===
  have h_to_Z_kills : ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ pageπ_t = 0 := by
    simp only [Category.assoc]; rw [← hψ_def]; exact kernelSubobject_arrow_comp ψ
  -- B_n_t and Z_n_t at the target
  set B_n_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑n with hB_n_t_def
  set Z_n_t := FC.cycleSubobject (s + ↑n) (k - 1) ↑n with hZ_n_t_def
  have hB_le_Z := FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n
  -- to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV'
  have h_to_Z_comp : to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV' := by
    change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
      (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
    simp only [Category.assoc, imageSubobject_arrow_comp]
    rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
      (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm, h_ltk_spec]
  -- (ker ψ).arrow ≫ lift_n ≫ πV' = ((ker ψ).arrow ≫ to_Z_n_t) ≫ Z_n_t.arrow
  have h_lift_πV'_eq : (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
      ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ Z_n_t.arrow := by
    rw [Category.assoc, h_to_Z_comp]
  -- Factor (ker ψ).arrow ≫ lift_n ≫ πV' through B_n_t using exactness + ψ = 0
  have h_bnd_factors : B_n_t.Factors ((kernelSubobject ψ).arrow ≫ lift_n ≫ πV') := by
    rw [h_lift_πV'_eq]
    -- Factor (ker ψ).arrow ≫ to_Z_n_t through ofLE(B_n_t, Z_n_t) using h_to_Z_kills
    set γ₁ := factorThruKernelSubobject pageπ_t
      ((kernelSubobject ψ).arrow ≫ to_Z_n_t) h_to_Z_kills
    -- γ₁ ≫ (ker pageπ_t).arrow = (ker ψ).arrow ≫ to_Z_n_t
    have hγ₁_spec : γ₁ ≫ (kernelSubobject pageπ_t).arrow =
        (kernelSubobject ψ).arrow ≫ to_Z_n_t :=
      factorThruKernelSubobject_comp_arrow _ _ _
    -- By exact_cokernel, imageSubobject(ofLE(B,Z)) = kernelSubobject(pageπ_t)
    have h_exact : (ShortComplex.mk (Subobject.ofLE B_n_t Z_n_t hB_le_Z) pageπ_t
        (by simp only [hpageπ_t_def]; exact cokernel.condition _)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _
        (by simp only [hpageπ_t_def]; exact cokernelIsCokernel _)
    rw [ShortComplex.exact_iff_image_eq_kernel] at h_exact
    change imageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z) = kernelSubobject pageπ_t at h_exact
    -- h_exact : imageSubobject(ofLE(B,Z)) = kernelSubobject(pageπ_t)
    -- Since ofLE(B,Z) is mono, factorThruImage(ofLE(B,Z)) is an iso
    haveI : Mono (Subobject.ofLE B_n_t Z_n_t hB_le_Z) := inferInstance
    haveI h_fti_epi : Epi (factorThruImageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z)) :=
      inferInstance
    haveI h_fti_mono : Mono (factorThruImageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z)) :=
      mono_of_mono_fac (imageSubobject_arrow_comp _)
    haveI : IsIso (factorThruImageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z)) :=
      isIso_of_mono_of_epi _
    -- (ker pageπ_t).arrow ≫ Z.arrow factors through B.arrow
    have h_ker_Z_fac : B_n_t.Factors ((kernelSubobject pageπ_t).arrow ≫ Z_n_t.arrow) := by
      rw [show (kernelSubobject pageπ_t).arrow =
        eqToHom (congr_arg Subobject.underlying.obj h_exact.symm) ≫
        (imageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z)).arrow from
        (Subobject.arrow_congr _ _ h_exact.symm).symm, Category.assoc]
      apply Subobject.factors_of_factors_right
      -- B_n_t.Factors(image(ofLE(B,Z)).arrow ≫ Z.arrow)
      have h_arrow_eq : (imageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z)).arrow ≫
          Z_n_t.arrow =
        inv (factorThruImageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z)) ≫
          B_n_t.arrow := by
        rw [← cancel_epi (factorThruImageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z))]
        -- Goal: factorThruImage ≫ image.arrow ≫ Z.arrow = B_n_t.arrow
        rw [show factorThruImageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z) ≫
          (imageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z)).arrow ≫ Z_n_t.arrow =
          (factorThruImageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z) ≫
          (imageSubobject (Subobject.ofLE B_n_t Z_n_t hB_le_Z)).arrow) ≫ Z_n_t.arrow
          from (Category.assoc _ _ _).symm,
          imageSubobject_arrow_comp, Subobject.ofLE_arrow,
          IsIso.hom_inv_id_assoc]
      rw [h_arrow_eq]
      exact Subobject.factors_comp_arrow _
    -- Combine: ((ker ψ).arrow ≫ to_Z_n_t) ≫ Z_n_t.arrow = γ₁ ≫ (ker pageπ_t).arrow ≫ Z_n_t.arrow
    -- which factors through B_n_t
    rw [show ((kernelSubobject ψ).arrow ≫ to_Z_n_t) ≫ Z_n_t.arrow =
      (γ₁ ≫ (kernelSubobject pageπ_t).arrow) ≫ Z_n_t.arrow from by rw [hγ₁_spec],
      Category.assoc]
    exact Subobject.factors_of_factors_right _ h_ker_Z_fac
  -- α : the factoring morphism (ker ψ) → B_n_t
  set α := B_n_t.factorThru _ h_bnd_factors with hα_def
  have hα_spec : α ≫ B_n_t.arrow = (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' :=
    Subobject.factorThru_arrow _ _ _
  -- imgD_bnd, I_bnd, oI_bnd: the d-image subobject and its intersection with the filtration
  set imgD_bnd := imageSubobject ((FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
    FC.dToK (k - 1)) with himgD_bnd_def
  set I_bnd := imgD_bnd ⊓ FC.fil (s + ↑n) (k - 1) with hI_bnd_def
  set oI_bnd := Subobject.ofLE I_bnd (FC.fil (s + ↑n) (k - 1)) inf_le_right
    with hoI_bnd_def
  -- factorB : I_bnd → B_n_t is epi
  set factorB := factorThruImageSubobject (oI_bnd ≫ πV') with hfactorB_def
  haveI hfactorB_epi : Epi factorB := inferInstance
  have hfactorB_spec : factorB ≫ B_n_t.arrow = oI_bnd ≫ πV' := by
    change factorThruImageSubobject (oI_bnd ≫ πV') ≫
      (imageSubobject (oI_bnd ≫ πV')).arrow = oI_bnd ≫ πV'
    exact imageSubobject_arrow_comp (oI_bnd ≫ πV')
  -- PB1: pullback of factorB (epi) against α
  set pb1_fst := Limits.pullback.fst factorB α
  set pb1_snd := Limits.pullback.snd factorB α
  have hpb1_cond : pb1_fst ≫ factorB = pb1_snd ≫ α := Limits.pullback.condition
  haveI : Epi pb1_snd := Abelian.epi_pullback_of_epi_f factorB α
  -- Key equation from PB1
  have h_pb1_eq_πV' : pb1_snd ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
      pb1_fst ≫ oI_bnd ≫ πV' := by
    calc pb1_snd ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV'
        = pb1_snd ≫ (α ≫ B_n_t.arrow) := by rw [hα_spec]
      _ = (pb1_snd ≫ α) ≫ B_n_t.arrow := (Category.assoc _ _ _).symm
      _ = (pb1_fst ≫ factorB) ≫ B_n_t.arrow := by rw [← hpb1_cond]
      _ = pb1_fst ≫ (factorB ≫ B_n_t.arrow) := Category.assoc _ _ _
      _ = pb1_fst ≫ oI_bnd ≫ πV' := by rw [hfactorB_spec]
  -- PB2: pullback of factorD (epi) against pb1_fst ≫ oI_to_imgD
  set imgD_src := (FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)
    with himgD_src_def
  set factorD := factorThruImageSubobject imgD_src with hfactorD_def
  haveI hfactorD_epi : Epi factorD := inferInstance
  have hfactorD_spec : factorD ≫ imgD_bnd.arrow = imgD_src :=
    imageSubobject_arrow_comp imgD_src
  set oI_to_imgD := Subobject.ofLE I_bnd imgD_bnd inf_le_left with hoI_to_imgD_def
  set pb2_fst := Limits.pullback.fst factorD (pb1_fst ≫ oI_to_imgD)
  set pb2_snd := Limits.pullback.snd factorD (pb1_fst ≫ oI_to_imgD)
  have hpb2_cond : pb2_fst ≫ factorD = pb2_snd ≫ (pb1_fst ≫ oI_to_imgD) :=
    Limits.pullback.condition
  haveI : Epi pb2_snd := Abelian.epi_pullback_of_epi_f factorD _
  -- Composite epi
  set e := pb2_snd ≫ pb1_snd with he_def
  haveI : Epi e := epi_comp _ _
  -- Correction term σ
  set eqH := eqToHom (show Subobject.underlying.obj (FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)) =
    Subobject.underlying.obj (FC.fil (s + 1) k) from by
    rw [show (s : ℤ) + ↑n - ↑n + 1 = s + 1 from by ring,
        show (k : ℤ) - 1 + 1 = k from by ring]) with heqH_def
  set σ := pb2_fst ≫ eqH ≫ ι_s with hσ_def
  -- σ ≫ πV = 0
  have hσ_πV : σ ≫ πV = 0 := by
    simp only [hσ_def, Category.assoc, show ι_s ≫ πV = 0 from cokernel.condition ι_s,
      comp_zero]
  -- w factors through kerZ1
  set w := e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow - σ with hw_def
  have hw_kills : w ≫ f_n1 = 0 := by
    rw [hw_def, Preadditive.sub_comp, sub_eq_zero]
    -- Goal: (e ≫ (ker ψ).arrow ≫ kerZ.arrow) ≫ f_n1 = σ ≫ f_n1
    -- Strategy: show both sides equal pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫ cokernel.π(...)
    --
    -- Key auxiliary facts:
    have h_sn1_eq : (s : ℤ) + ↑n + 1 = s + ↑(n + 1) := by push_cast; ring
    -- (1) e ≫ (ker ψ).arrow ≫ lift_n ≫ πV' = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ πV'
    have h_e_lift_πV' : e ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ πV' =
        pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ πV' := by
      simp only [he_def, Category.assoc, h_pb1_eq_πV']
    -- (2) The difference (e ≫ ... ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd) ≫ πV' = 0
    have h_diff_kills : (e ≫ (kernelSubobject ψ).arrow ≫ lift_n -
        pb2_snd ≫ pb1_fst ≫ oI_bnd) ≫ πV' = 0 := by
      rw [Preadditive.sub_comp]; simp only [Category.assoc]
      rw [h_e_lift_πV', sub_self]
    -- (3) monoLift decomposes the difference
    set γ_diff := Abelian.monoLift ι_t
        (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd)
        (show _ ≫ cokernel.π ι_t = 0 from h_diff_kills) with hγ_diff_def
    have hγ_spec : γ_diff ≫ ι_t =
        e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd :=
      Abelian.monoLift_comp ι_t
        (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd)
        (show _ ≫ cokernel.π ι_t = 0 from h_diff_kills)
    have h_decomp : e ≫ (kernelSubobject ψ).arrow ≫ lift_n =
        pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t := by
      -- hγ_spec: γ_diff ≫ ι_t = (e ≫ ...) - (pb2_snd ≫ ...)
      -- eq_add_of_sub_eq: a - b = c → a = b + c ... wait, sub_eq_iff_eq_add flipped
      -- From c = a - b we get a = c + b (sub_eq_iff_eq_add)
      -- Then a = b + c by add_comm
      -- Actually: hγ_spec.symm : (e ≫ ...) - (pb2_snd ≫ ...) = γ_diff ≫ ι_t
      -- sub_eq_iff_eq_add.mp hγ_spec.symm : e ≫ ... = γ_diff ≫ ι_t + pb2_snd ≫ ...
      -- But sub_eq_iff_eq_add.mp causes motive error.
      -- Direct arithmetic approach:
      have key : e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd =
          γ_diff ≫ ι_t := hγ_spec.symm
      -- a - b = c → a = b + c
      calc e ≫ (kernelSubobject ψ).arrow ≫ lift_n
          = (e ≫ (kernelSubobject ψ).arrow ≫ lift_n - pb2_snd ≫ pb1_fst ≫ oI_bnd) +
            pb2_snd ≫ pb1_fst ≫ oI_bnd := (sub_add_cancel _ _).symm
        _ = γ_diff ≫ ι_t + pb2_snd ≫ pb1_fst ≫ oI_bnd := by rw [key]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t := add_comm _ _
    -- (4) ι_t ≫ F^{s+n}.arrow ≫ cokernel.π(F^{s+↑(n+1)}.arrow) = 0
    have h_ι_t_kills : ι_t ≫ (FC.fil (s + ↑n) (k - 1)).arrow ≫
        cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) = 0 := by
      have h1 : ι_t ≫ (FC.fil (s + ↑n) (k - 1)).arrow =
          (FC.fil (s + ↑n + 1) (k - 1)).arrow :=
        Subobject.ofLE_arrow (FC.fil_anti (s + ↑n) (k - 1))
      have h2 : (FC.fil (s + ↑n + 1) (k - 1)).arrow =
          eqToHom (congr_arg (fun i => Subobject.underlying.obj (FC.fil i (k - 1)))
            h_sn1_eq) ≫ (FC.fil (s + ↑(n + 1)) (k - 1)).arrow := by
        simp [h_sn1_eq]
      calc ι_t ≫ (FC.fil (s + ↑n) (k - 1)).arrow ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow)
          = (ι_t ≫ (FC.fil (s + ↑n) (k - 1)).arrow) ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) := by
            rw [Category.assoc]
        _ = (eqToHom _ ≫ (FC.fil (s + ↑(n + 1)) (k - 1)).arrow) ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) := by
            rw [h1, h2]
        _ = eqToHom _ ≫ ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow)) := by
            rw [Category.assoc]
        _ = eqToHom _ ≫ 0 := by
            rw [cokernel.condition]
        _ = 0 := by rw [comp_zero]
    -- (5) oI_bnd ≫ F^{s+n}.arrow = I_bnd.arrow
    have h_oI_arrow : oI_bnd ≫ (FC.fil (s + ↑n) (k - 1)).arrow = I_bnd.arrow :=
      Subobject.ofLE_arrow inf_le_right
    -- (6) σ ≫ F^s.arrow = pb2_fst ≫ eqH ≫ F^{s+1}.arrow
    have h_σ_arrow : σ ≫ (FC.fil s k).arrow =
        pb2_fst ≫ eqH ≫ (FC.fil (s + 1) k).arrow := by
      simp only [hσ_def, Category.assoc]
      congr 2; exact Subobject.ofLE_arrow (FC.fil_anti s k)
    -- (7) eqH ≫ F^{s+1}.arrow ≫ d(k) = imgD_src
    have h_eqH_d : eqH ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k = imgD_src := by
      conv_lhs => rw [← FC.eqToHom_arrow_dToK (s + 1) k]
      rw [heqH_def]; simp only [← Category.assoc]; rw [eqToHom_trans]
      -- Goal: (eqToHom _ ≫ (FC.fil (s+1)((k-1)+1)).arrow) ≫ FC.dToK (k-1) = imgD_src
      -- imgD_src = (FC.fil (s+↑n-↑n+1) ((k-1)+1)).arrow ≫ FC.dToK (k-1)
      -- Since s+↑n-↑n+1 = s+1, both sides are equal
      rw [himgD_src_def]
      -- Goal: (eqToHom _ ≫ (FC.fil (s+1)((k-1)+1)).arrow) ≫ FC.dToK (k-1) =
      --       (FC.fil (s+↑n-↑n+1) ((k-1)+1)).arrow ≫ FC.dToK (k-1)
      congr 1
      -- Goal: eqToHom _ ≫ (FC.fil (s+1)((k-1)+1)).arrow = (FC.fil (s+↑n-↑n+1) ((k-1)+1)).arrow
      exact Subobject.arrow_congr _ _ (by congr 1; ring)
    -- (8) pb2_fst ≫ imgD_src = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow
    have h_pb2_imgD : pb2_fst ≫ imgD_src = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow := by
      calc pb2_fst ≫ imgD_src
          = pb2_fst ≫ (factorD ≫ imgD_bnd.arrow) := by
            rw [imageSubobject_arrow_comp imgD_src]
        _ = (pb2_fst ≫ factorD) ≫ imgD_bnd.arrow := by rw [Category.assoc]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_to_imgD) ≫ imgD_bnd.arrow := by rw [hpb2_cond]
        _ = pb2_snd ≫ pb1_fst ≫ (oI_to_imgD ≫ imgD_bnd.arrow) := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow := by
            congr 1; congr 1; exact Subobject.ofLE_arrow inf_le_left
    -- === LHS: (e ≫ (ker ψ).arrow ≫ kerZ.arrow) ≫ f_n1 ===
    have h_lhs : (e ≫ (kernelSubobject ψ).arrow ≫ kerZ.arrow) ≫ f_n1 =
        pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫
        cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) := by
      -- Expand and right-associate
      rw [hf_n1_def]; simp only [Category.assoc]
      -- Step 1: Replace kerZ.arrow ≫ F^s.arrow ≫ d k with lift_n ≫ F^{s+n}.arrow
      conv_lhs =>
        rw [show (kernelSubobject ψ).arrow ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) =
            (kernelSubobject ψ).arrow ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [← h_lift_spec]
      simp only [Category.assoc]
      -- Goal: e ≫ (ker ψ).arrow ≫ lift_n ≫ F^{s+n}.arrow ≫ cokernel.π = pb2_snd ≫ ...
      -- Step 2-5: Use calc with explicit left-association
      set F_sn := (FC.fil (s + ↑n) (k - 1)).arrow with hF_sn_def
      set cok := cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) with hcok_def
      calc e ≫ (kernelSubobject ψ).arrow ≫ lift_n ≫ F_sn ≫ cok
          = (e ≫ (kernelSubobject ψ).arrow ≫ lift_n) ≫ F_sn ≫ cok := by
            simp only [Category.assoc]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_bnd + γ_diff ≫ ι_t) ≫ F_sn ≫ cok := by
            rw [h_decomp]
        _ = (pb2_snd ≫ pb1_fst ≫ oI_bnd) ≫ F_sn ≫ cok +
            (γ_diff ≫ ι_t) ≫ F_sn ≫ cok := by
            rw [Preadditive.add_comp]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok +
            γ_diff ≫ ι_t ≫ F_sn ≫ cok := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok + γ_diff ≫ 0 := by
            rw [h_ι_t_kills]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok + 0 := by
            rw [comp_zero]
        _ = pb2_snd ≫ pb1_fst ≫ oI_bnd ≫ F_sn ≫ cok := by
            rw [add_zero]
        _ = pb2_snd ≫ pb1_fst ≫ (oI_bnd ≫ F_sn) ≫ cok := by
            simp only [Category.assoc]
        _ = pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫ cok := by
            rw [h_oI_arrow]
    -- === RHS: σ ≫ f_n1 ===
    have h_rhs : σ ≫ f_n1 =
        pb2_snd ≫ pb1_fst ≫ I_bnd.arrow ≫
        cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) := by
      rw [hf_n1_def]
      -- σ ≫ F^s.arrow ≫ d(k) ≫ cokernel.π = pb2_fst ≫ eqH ≫ F^{s+1}.arrow ≫ d(k) ≫ cokernel.π
      conv_lhs =>
        rw [show σ ≫ (FC.fil s k).arrow ≫ FC.d k ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) =
            (σ ≫ (FC.fil s k).arrow) ≫ FC.d k ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [h_σ_arrow]
      simp only [Category.assoc]
      -- pb2_fst ≫ eqH ≫ F^{s+1}.arrow ≫ d(k) ≫ cokernel.π
      conv_lhs =>
        rw [show pb2_fst ≫ eqH ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) =
            (pb2_fst ≫ (eqH ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k)) ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
        rw [show pb2_fst ≫ (eqH ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k) =
            (pb2_fst ≫ (eqH ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k)) from rfl]
      conv_lhs =>
        rw [show (pb2_fst ≫ (eqH ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k)) ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) =
            pb2_fst ≫ (eqH ≫ (FC.fil (s + 1) k).arrow ≫ FC.d k) ≫
              cokernel.π ((FC.fil (s + ↑(n + 1)) (k - 1)).arrow) from by
            simp only [Category.assoc]]
      rw [h_eqH_d]
      simp only [← Category.assoc]; rw [h_pb2_imgD]; simp only [Category.assoc]
    rw [h_lhs, h_rhs]
  -- w_fac : PB2 → kerZ1
  set w_fac := factorThruKernelSubobject f_n1 w hw_kills with hw_fac_def
  have hw_fac_spec : w_fac ≫ kerZ1.arrow = w :=
    factorThruKernelSubobject_comp_arrow _ _ _
  -- Key equation: w_fac ≫ β ≫ p = e ≫ (ker ψ).arrow ≫ p (by mono cancellation)
  have h_key_eq : w_fac ≫ β ≫ p = e ≫ (kernelSubobject ψ).arrow ≫ p := by
    apply (inferInstance : Mono ((FC.toSSData bnd s k).Z ↑n).arrow).right_cancellation
    simp only [Category.assoc]
    rw [h_p_Z]
    -- Goal: w_fac ≫ β ≫ kerZ.arrow ≫ πV = e ≫ (ker ψ).arrow ≫ kerZ.arrow ≫ πV
    -- Left-associate both sides to peel β ≫ kerZ.arrow and express via hw_fac_spec
    rw [show w_fac ≫ β ≫ kerZ.arrow ≫ πV = (w_fac ≫ (β ≫ kerZ.arrow)) ≫ πV from by
      simp only [Category.assoc]]
    rw [show β ≫ kerZ.arrow = kerZ1.arrow from Subobject.ofLE_arrow hkerZ1_le]
    -- Goal: (w_fac ≫ kerZ1.arrow) ≫ πV = e ≫ (ker ψ).arrow ≫ kerZ.arrow ≫ πV
    rw [hw_fac_spec]
    -- Goal: w ≫ πV = e ≫ (ker ψ).arrow ≫ kerZ.arrow ≫ πV
    rw [hw_def, Preadditive.sub_comp, hσ_πV, sub_zero]
    simp only [Category.assoc]
  -- Conclusion: use epi_comp', h_key_eq, h_factor to show
  --   imageSubobject((ker ψ).arrow ≫ p ≫ pageπ) ≤ imageSubobject(ofLE ≫ pageπ)
  -- Step 1: imageSubobject_epi_comp' removes e
  rw [(imageSubobject_epi_comp' e
    ((kernelSubobject ψ).arrow ≫ p ≫ (FC.toSSData bnd s k).pageπ ↑n)).symm]
  -- Goal: imageSubobject(e ≫ (ker ψ).arrow ≫ p ≫ pageπ) ≤ imageSubobject(ofLE ≫ pageπ)
  -- Step 2: rewrite e ≫ ... = (w_fac ≫ p1) ≫ (ofLE ≫ pageπ)
  have h_rewrite : e ≫ (kernelSubobject ψ).arrow ≫ p ≫ (FC.toSSData bnd s k).pageπ ↑n =
      (w_fac ≫ p1) ≫ (Subobject.ofLE ((FC.toSSData bnd s k).Z ↑(n + 1))
        ((FC.toSSData bnd s k).Z ↑n)
        ((FC.toSSData bnd s k).Z_anti (by exact_mod_cast Nat.le_succ n)) ≫
        (FC.toSSData bnd s k).pageπ ↑n) := by
    -- h_key_eq : w_fac ≫ β ≫ p = e ≫ (ker ψ).arrow ≫ p  (right-assoc on both sides)
    -- h_factor : p1 ≫ ofLE(...) = β ≫ p  (right-assoc)
    -- Use the prefix equation to derive the full equation
    have h_prefix : e ≫ (kernelSubobject ψ).arrow ≫ p =
        w_fac ≫ p1 ≫ Subobject.ofLE ((FC.toSSData bnd s k).Z ↑(n + 1))
        ((FC.toSSData bnd s k).Z ↑n)
        ((FC.toSSData bnd s k).Z_anti (by exact_mod_cast Nat.le_succ n)) := by
      rw [← h_key_eq]; congr 1; exact h_factor.symm
    -- Left-associate everything to use h_prefix as a prefix rewrite
    rw [show e ≫ (kernelSubobject ψ).arrow ≫ p ≫ (FC.toSSData bnd s k).pageπ ↑n =
      (e ≫ (kernelSubobject ψ).arrow ≫ p) ≫ (FC.toSSData bnd s k).pageπ ↑n from by
      simp only [Category.assoc],
      h_prefix]
    simp only [Category.assoc]
  rw [h_rewrite]
  exact imageSubobject_comp_le _ _


set_option maxHeartbeats 6400000 in
-- Long proof: image of page differential = B_{n+1}/B_n via pullback and boundary factoring
/-- The image of the page differential `d_n` at `(s,k)` equals `B_{n+1}/B_n` at the target
    `(s+n, k-1)`. This is the content of the `B_succ` field for the spectral sequence. -/
theorem FilteredComplex.pageDifferential_B_succ (FC : FilteredComplex C)
    (bnd : FC.IsBounded) (s k : ℤ) (n : ℕ) :
    imageSubobject (FC.pageDifferential bnd s k n) =
      imageSubobject (Subobject.ofLE
        ((FC.toSSData bnd (s + ↑n) (k - 1)).B ↑(n + 1))
        ((FC.toSSData bnd (s + ↑n) (k - 1)).Z ↑n)
        (le_trans ((FC.toSSData bnd (s + ↑n) (k - 1)).B_le_Z ↑(n + 1))
          ((FC.toSSData bnd (s + ↑n) (k - 1)).Z_anti
            (by exact_mod_cast Nat.le_succ n))) ≫
        (FC.toSSData bnd (s + ↑n) (k - 1)).pageπ ↑n) := by
  -- === Reconstruct the internal abbreviations of pageDifferential ===
  set ι_s := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k) with hι_s_def
  set πV := cokernel.π ι_s with hπV_def
  set f_n := (FC.fil s k).arrow ≫ FC.d k ≫
    cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) with hf_n_def
  set kerZ := kernelSubobject f_n with hkerZ_def
  set ι_t := Subobject.ofLE (FC.fil (s + ↑n + 1) (k - 1)) (FC.fil (s + ↑n) (k - 1))
    (FC.fil_anti (s + ↑n) (k - 1)) with hι_t_def
  set πV' := cokernel.π ι_t with hπV'_def
  set f_n' := (FC.fil (s + ↑n) (k - 1)).arrow ≫ FC.d (k - 1) ≫
    cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) with hf_n'_def
  set kerZ' := kernelSubobject f_n' with hkerZ'_def
  -- Reconstruct lift_n, lift_to_kerZ', to_Z_n_t, ψ, p, h_on_Zn
  have h_ker_fn : kerZ.arrow ≫ f_n = 0 := kernelSubobject_arrow_comp f_n
  have h_factor_zero : (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫
      cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) = 0 := by
    simp only [Category.assoc] at h_ker_fn ⊢; exact h_ker_fn
  set lift_n := Abelian.monoLift (FC.fil (s + ↑n) (k - 1)).arrow
    (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) h_factor_zero with hlift_n_def
  have h_lift_spec : lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow =
      kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k := Abelian.monoLift_comp _ _ _
  have h_lift_in_kerZ' : lift_n ≫ f_n' = 0 := by
    calc lift_n ≫ f_n'
        = ((lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) ≫ FC.d (k - 1)) ≫
            cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by
          simp only [hf_n'_def, Category.assoc]
      _ = ((kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫ FC.d (k - 1)) ≫
            cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) := by rw [h_lift_spec]
      _ = 0 := by
          rw [show (kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k) ≫ FC.d (k - 1) =
            kerZ.arrow ≫ (FC.fil s k).arrow ≫ (FC.d k ≫ FC.d (k - 1)) from by
            simp only [Category.assoc], FC.d_comp_d k]; simp only [comp_zero, zero_comp]
  set lift_to_kerZ' := factorThruKernelSubobject f_n' lift_n h_lift_in_kerZ'
    with hlift_to_kerZ'_def
  have h_ltk_spec : lift_to_kerZ' ≫ kerZ'.arrow = lift_n :=
    factorThruKernelSubobject_comp_arrow f_n' lift_n h_lift_in_kerZ'
  set to_Z_n_t := lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')
    with hto_Z_n_t_def
  set pageπ_t := (FC.toSSData bnd (s + ↑n) (k - 1)).pageπ ↑n with hpageπ_t_def
  set ψ := to_Z_n_t ≫ pageπ_t with hψ_def
  set p := factorThruImageSubobject (kerZ.arrow ≫ πV) with hp_def
  haveI : Epi p := inferInstance
  -- h_ker_p_ψ : kernel.ι p ≫ ψ = 0 (from pageDifferential construction)
  -- We need this for epiDesc. Reconstruct the proof.
  have h_ker_p_ψ : kernel.ι p ≫ ψ = 0 := by
    -- This follows the same proof as in pageDifferential (lines 699-908).
    -- kernel.ι p ≫ to_Z_n_t factors through ofLE(B_n_t, Z_n_t), and cokernel kills it.
    set B_n_t' := FC.boundarySubobject (s + ↑n) (k - 1) ↑n
    set Z_n_t' := FC.cycleSubobject (s + ↑n) (k - 1) ↑n
    have hB_le_Z' := FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n
    -- to_Z_n_t ≫ Z_n_t'.arrow = lift_n ≫ πV'
    have h_to_Z_comp' : to_Z_n_t ≫ Z_n_t'.arrow = lift_n ≫ πV' := by
      change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
        (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
      simp only [Category.assoc, imageSubobject_arrow_comp]
      rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
        (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm, h_ltk_spec]
    -- kernel.ι p ≫ lift_n ≫ πV' factors through B_n_t'
    have h_comp_eq' : kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow =
        kernel.ι p ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k := by
      simp only [h_lift_spec]
    set imgD' := imageSubobject ((FC.fil (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1))
    have h_fac_imgD' : imgD'.Factors
        (kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) := by
      rw [h_comp_eq']
      have h1 : kernel.ι p ≫ (kerZ.arrow ≫ πV) = 0 := by
        have h_p_Z : p ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow = kerZ.arrow ≫ πV :=
          imageSubobject_arrow_comp (kerZ.arrow ≫ πV)
        calc kernel.ι p ≫ (kerZ.arrow ≫ πV)
            = kernel.ι p ≫ (p ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow) := by rw [h_p_Z]
          _ = (kernel.ι p ≫ p) ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow := by
              simp only [Category.assoc]
          _ = 0 ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow := by rw [kernel.condition]
          _ = 0 := zero_comp
      have h1' : (kernel.ι p ≫ kerZ.arrow) ≫ cokernel.π ι_s = 0 := by
        rw [Category.assoc]; exact h1
      set α' := Abelian.monoLift ι_s (kernel.ι p ≫ kerZ.arrow) h1'
      have hα'_spec : α' ≫ ι_s = kernel.ι p ≫ kerZ.arrow := Abelian.monoLift_comp _ _ _
      have h_ι_arrow' : ι_s ≫ (FC.fil s k).arrow = (FC.fil (s + 1) k).arrow :=
        Subobject.ofLE_arrow (FC.fil_anti s k)
      have h_rewrite' : kernel.ι p ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k =
          α' ≫ ((FC.fil (s + 1) k).arrow ≫ FC.d k) := by
        conv_lhs => rw [show kernel.ι p ≫ kerZ.arrow ≫ (FC.fil s k).arrow ≫ FC.d k =
          ((kernel.ι p ≫ kerZ.arrow) ≫ (FC.fil s k).arrow) ≫ FC.d k from by
          simp only [Category.assoc]]
        rw [← hα'_spec, show (α' ≫ ι_s) ≫ (FC.fil s k).arrow = α' ≫ (ι_s ≫ (FC.fil s k).arrow) from
          Category.assoc _ _ _, h_ι_arrow', Category.assoc]
      rw [h_rewrite']
      apply Subobject.factors_of_factors_right
      have h_transport' : eqToHom (show Subobject.underlying.obj (FC.fil (s + 1) k) =
          Subobject.underlying.obj (FC.fil (s + 1) ((k - 1) + 1)) by
          rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
          ((FC.fil (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
          (FC.fil (s + 1) k).arrow ≫ FC.d k :=
        FC.eqToHom_arrow_dToK (s + 1) k
      rw [← h_transport', Subobject.mk_factors_iff]
      exact ⟨eqToHom (by rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
        factorThruImage ((FC.fil (s + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)), by simp⟩
    have h_fac_fil' : (FC.fil (s + ↑n) (k - 1)).Factors
        (kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) :=
      Subobject.factors_of_factors_right _ (Subobject.factors_comp_arrow lift_n)
    set I' := imgD' ⊓ FC.fil (s + ↑n) (k - 1)
    have h_fac_I' : I'.Factors (kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) :=
      (Subobject.inf_factors _).mpr ⟨h_fac_imgD', h_fac_fil'⟩
    set δ' := I'.factorThru _ h_fac_I'
    have hδ'_spec : δ' ≫ I'.arrow = kernel.ι p ≫ lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow :=
      Subobject.factorThru_arrow _ _ _
    have h_δ'_ofLE : δ' ≫ Subobject.ofLE I' (FC.fil (s + ↑n) (k - 1)) inf_le_right =
        kernel.ι p ≫ lift_n := by
      apply (inferInstance : Mono (FC.fil (s + ↑n) (k - 1)).arrow).right_cancellation
      rw [Category.assoc, Subobject.ofLE_arrow, hδ'_spec]
      simp only [Category.assoc]
    have h_imgD_bnd' : imageSubobject ((FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) = imgD' := by
      rw [show (s : ℤ) + (↑n : ℤ) - (↑n : ℤ) + 1 = s + 1 from by omega]
    have h_I_bnd' : imageSubobject ((FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) ⊓ FC.fil (s + ↑n) (k - 1) = I' := by
      rw [h_imgD_bnd']
    have h_bnd_fac' : B_n_t'.Factors (kernel.ι p ≫ lift_n ≫ πV') := by
      rw [show kernel.ι p ≫ lift_n ≫ πV' = (kernel.ι p ≫ lift_n) ≫ πV'
        from (Category.assoc _ _ _).symm, ← h_δ'_ofLE, Category.assoc]
      apply Subobject.factors_of_factors_right
      set I_bnd' := imageSubobject ((FC.fil (s + ↑n - ↑n + 1) ((k - 1) + 1)).arrow ≫
        FC.dToK (k - 1)) ⊓ FC.fil (s + ↑n) (k - 1)
      have h_I_le_Ibnd' : I' ≤ I_bnd' := le_of_eq h_I_bnd'.symm
      have h_ofLE_factor' : Subobject.ofLE I' (FC.fil (s + ↑n) (k - 1)) inf_le_right =
          Subobject.ofLE I' I_bnd' h_I_le_Ibnd' ≫
          Subobject.ofLE I_bnd' (FC.fil (s + ↑n) (k - 1)) inf_le_right := by
        apply (inferInstance : Mono (FC.fil (s + ↑n) (k - 1)).arrow).right_cancellation
        simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [h_ofLE_factor', Category.assoc]
      apply Subobject.factors_of_factors_right
      change (imageSubobject
        (Subobject.ofLE I_bnd' (FC.fil (s + ↑n) (k - 1)) inf_le_right ≫ πV')).Factors
        (Subobject.ofLE I_bnd' (FC.fil (s + ↑n) (k - 1)) inf_le_right ≫ πV')
      rw [Subobject.mk_factors_iff]
      exact ⟨factorThruImage _, by simp⟩
    -- Factor kernel.ι p ≫ to_Z_n_t through ofLE(B_n_t', Z_n_t')
    have h_ker_to_Z_fac' : B_n_t'.Factors (kernel.ι p ≫ to_Z_n_t ≫ Z_n_t'.arrow) := by
      rw [h_to_Z_comp']; exact h_bnd_fac'
    set γ' := B_n_t'.factorThru _ h_ker_to_Z_fac'
    have hγ'_spec : γ' ≫ B_n_t'.arrow = kernel.ι p ≫ to_Z_n_t ≫ Z_n_t'.arrow :=
      Subobject.factorThru_arrow _ _ _
    have h_factor_B' : kernel.ι p ≫ to_Z_n_t =
        γ' ≫ Subobject.ofLE B_n_t' Z_n_t' hB_le_Z' := by
      apply (inferInstance : Mono Z_n_t'.arrow).right_cancellation
      simp only [Category.assoc]
      rw [Subobject.ofLE_arrow, hγ'_spec]
    have h_cok' : Subobject.ofLE B_n_t' Z_n_t' hB_le_Z' ≫ pageπ_t = 0 := by
      rw [hpageπ_t_def]
      change Subobject.ofLE B_n_t' Z_n_t' hB_le_Z' ≫
        cokernel.π (Subobject.ofLE (FC.boundarySubobject (s + ↑n) (k - 1) ↑n)
          (FC.cycleSubobject (s + ↑n) (k - 1) ↑n)
          (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑n)) = 0
      exact cokernel.condition _
    rw [hψ_def]
    calc kernel.ι p ≫ to_Z_n_t ≫ pageπ_t
        = (kernel.ι p ≫ to_Z_n_t) ≫ pageπ_t := (Category.assoc _ _ _).symm
      _ = (γ' ≫ Subobject.ofLE B_n_t' Z_n_t' hB_le_Z') ≫ pageπ_t := by rw [h_factor_B']
      _ = γ' ≫ (Subobject.ofLE B_n_t' Z_n_t' hB_le_Z' ≫ pageπ_t) := Category.assoc _ _ _
      _ = γ' ≫ 0 := by rw [h_cok']
      _ = 0 := comp_zero
  set h_on_Zn := Abelian.epiDesc p ψ h_ker_p_ψ with hh_on_Zn_def
  -- h_on_Zn : Z_n_s.underlying → target page, with p ≫ h_on_Zn = ψ
  -- === Step 1: Reduce LHS ===
  -- pageDifferential = cokernel.desc(ofLE_source, h_on_Zn, h_B_zero)
  -- pageπ_source ≫ pageDifferential = h_on_Zn (cokernel.π_desc)
  -- pageπ_source is epi, so imageSubobject(pageDifferential) = imageSubobject(h_on_Zn)
  -- p ≫ h_on_Zn = ψ, p is epi, so imageSubobject(h_on_Zn) = imageSubobject(ψ)
  -- Therefore: imageSubobject(pageDifferential) = imageSubobject(ψ)
  -- Step 1a: Show pageDifferential matches cokernel.desc _ h_on_Zn _
  -- Need to reconstruct h_B_zero from pageDifferential definition.
  -- Instead of tracking h_B_zero, use a calc chain:
  -- imageSubobject(pageDiff) = imageSubobject(pageπ_s ≫ pageDiff) [epi_comp']
  --   = imageSubobject(h_on_Zn) [cokernel.π_desc]
  --   = imageSubobject(p ≫ h_on_Zn) [epi_comp']
  --   = imageSubobject(ψ) [comp_epiDesc]
  -- Use the approach: first show imageSubobject(pageDiff) = imageSubobject(ψ) indirectly.
  -- Approach: Use erw to access cokernel.π_desc and Abelian.comp_epiDesc, but
  -- contain pollution in a have block.
  have h_img_pageDiff_eq_ψ : imageSubobject (FC.pageDifferential bnd s k n) =
      imageSubobject ψ := by
    -- Step 1: imageSubobject(pageπ_s ≫ pageDiff) = imageSubobject(pageDiff)
    set pageπ_s := (FC.toSSData bnd s k).pageπ ↑n with hpageπ_s_def
    haveI : Epi pageπ_s := by
      simp only [hpageπ_s_def, SSData.pageπ]; infer_instance
    rw [← imageSubobject_epi_comp' pageπ_s (FC.pageDifferential bnd s k n)]
    -- Goal: imageSubobject(pageπ_s ≫ pageDiff) = imageSubobject(ψ)
    -- Step 2: pageπ_s ≫ pageDiff = h_on_Zn
    erw [cokernel.π_desc]
    -- Goal: imageSubobject(h_on_Zn) = imageSubobject(ψ)
    -- Step 3: imageSubobject(p ≫ h_on_Zn) = imageSubobject(h_on_Zn)
    rw [← imageSubobject_epi_comp' p h_on_Zn]
    -- Goal: imageSubobject(p ≫ h_on_Zn) = imageSubobject(ψ)
    rw [Abelian.comp_epiDesc]
  rw [h_img_pageDiff_eq_ψ]
  -- Now goal: imageSubobject(ψ) = imageSubobject(ofLE(B_{n+1}, Z_n) ≫ pageπ_t)
  -- === Step 2: Prove equality via le_antisymm ===
  apply le_antisymm
  -- === (≤) direction: imageSubobject(ψ) ≤ imageSubobject(ofLE(B_{n+1}, Z_n) ≫ pageπ_t) ===
  · -- ψ = to_Z_n_t ≫ pageπ_t
    -- to_Z_n_t = lift_to_kerZ' ≫ factorThruImageSubobject(kerZ'.arrow ≫ πV')
    -- to_Z_n_t : kerZ.underlying → Z_n_t.underlying
    -- We show: to_Z_n_t factors through ofLE(B_{n+1}, Z_n) via a left factor.
    -- Specifically: to_Z_n_t = γ ≫ ofLE(B_{n+1}, Z_n) where
    -- γ = factorThruImageSubobject(something) ≫ factorThruImage(...) etc.
    -- Actually we need lift_n to factor through I_bnd, then through B_{n+1}.
    -- Key: lift_n ≫ (FC.fil (s+↑n) (k-1)).arrow = kerZ.arrow ≫ (FC.fil s k).arrow ≫ d(k)
    -- The d-image kerZ.arrow ≫ fil(s)(k).arrow ≫ d(k) is in imgD (via transport)
    -- Also lift_n itself witnesses it's in fil(s+n)(k-1).
    -- So lift_n ≫ fil(s+n).arrow factors through I_bnd = imgD ⊓ fil(s+n).
    -- Then lift_n ≫ πV' = factorThru_I ≫ oI_bnd ≫ πV'
    -- and oI_bnd ≫ πV' generates B_{n+1}.
    -- === Setup I_bnd (boundary) at (s+n, k-1) with index n+1 ===
    -- B_{n+1} = boundarySubobject (s+↑n) (k-1) ↑(n+1)
    -- imgD_bnd = imageSubobject(fil((s+↑n) - ↑(n+1) + 1)((k-1)+1).arrow ≫ dToK(k-1))
    -- Note: (s+↑n) - ↑(n+1) + 1 = s, so
    -- imgD_bnd = imageSubobject(fil(s)((k-1)+1).arrow ≫ dToK(k-1))
    set imgD_bnd := imageSubobject ((FC.fil (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫
      FC.dToK (k - 1)) with himgD_bnd_def
    set I_bnd := imgD_bnd ⊓ FC.fil (s + ↑n) (k - 1) with hI_bnd_def
    set oI_bnd := Subobject.ofLE I_bnd (FC.fil (s + ↑n) (k - 1)) inf_le_right
      with hoI_bnd_def
    -- B_{n+1} at target = imageSubobject(oI_bnd ≫ πV')
    -- Z_n at target = imageSubobject(kerZ'.arrow ≫ πV')
    set B_n1_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1) with hB_n1_t_def
    set Z_n_t := FC.cycleSubobject (s + ↑n) (k - 1) ↑n with hZ_n_t_def
    -- lift_n ≫ fil(s+n).arrow = kerZ.arrow ≫ fil(s).arrow ≫ d(k)
    -- This is in imgD_bnd because:
    -- fil(s).arrow ≫ d(k) = eqToHom ≫ fil(s)((k-1)+1).arrow ≫ dToK(k-1)
    -- and (s+↑n) - ↑(n+1) + 1 = s
    have h_idx_eq_s : (s : ℤ) + ↑n - ↑(n + 1) + 1 = s := by push_cast; ring
    -- imgD_bnd = imageSubobject(fil(s)((k-1)+1).arrow ≫ dToK(k-1))
    have h_imgD_eq : imgD_bnd =
        imageSubobject ((FC.fil s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) := by
      rw [himgD_bnd_def, h_idx_eq_s]
    -- lift_n ≫ fil(s+n).arrow is in imgD_bnd
    have h_fac_imgD_bnd : imgD_bnd.Factors
        (lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) := by
      rw [h_lift_spec]
      -- Goal: imgD_bnd.Factors(kerZ.arrow ≫ fil(s)(k).arrow ≫ d(k))
      rw [h_imgD_eq]
      have h_transport_dk : eqToHom (show Subobject.underlying.obj (FC.fil s k) =
          Subobject.underlying.obj (FC.fil s ((k - 1) + 1)) by
          rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
          ((FC.fil s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) =
          (FC.fil s k).arrow ≫ FC.d k :=
        FC.eqToHom_arrow_dToK s k
      rw [← h_transport_dk, Subobject.mk_factors_iff]
      exact ⟨kerZ.arrow ≫ eqToHom (by rw [show (k - 1 : ℤ) + 1 = k from by omega]) ≫
        factorThruImage ((FC.fil s ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)), by simp⟩
    have h_fac_fil_bnd : (FC.fil (s + ↑n) (k - 1)).Factors
        (lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) :=
      Subobject.factors_comp_arrow lift_n
    have h_fac_I_bnd : I_bnd.Factors (lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow) :=
      (Subobject.inf_factors _).mpr ⟨h_fac_imgD_bnd, h_fac_fil_bnd⟩
    set δ_bnd := I_bnd.factorThru _ h_fac_I_bnd with hδ_bnd_def
    have hδ_bnd_spec : δ_bnd ≫ I_bnd.arrow = lift_n ≫ (FC.fil (s + ↑n) (k - 1)).arrow :=
      Subobject.factorThru_arrow _ _ _
    -- δ_bnd ≫ oI_bnd = lift_n (by mono cancellation)
    have h_δ_oI : δ_bnd ≫ oI_bnd = lift_n := by
      apply (inferInstance : Mono (FC.fil (s + ↑n) (k - 1)).arrow).right_cancellation
      rw [Category.assoc, Subobject.ofLE_arrow, hδ_bnd_spec]
    -- lift_n ≫ πV' = δ_bnd ≫ oI_bnd ≫ πV'
    have h_lift_πV' : lift_n ≫ πV' = δ_bnd ≫ oI_bnd ≫ πV' := by
      rw [← Category.assoc, h_δ_oI]
    -- to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV'
    have h_to_Z_comp : to_Z_n_t ≫ Z_n_t.arrow = lift_n ≫ πV' := by
      change (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
        (imageSubobject (kerZ'.arrow ≫ πV')).arrow = lift_n ≫ πV'
      simp only [Category.assoc, imageSubobject_arrow_comp]
      rw [show lift_to_kerZ' ≫ kerZ'.arrow ≫ πV' =
        (lift_to_kerZ' ≫ kerZ'.arrow) ≫ πV' from (Category.assoc _ _ _).symm, h_ltk_spec]
    -- B_{n+1} is in oI_bnd ≫ πV' terms; we need to show to_Z_n_t factors through
    -- ofLE(B_{n+1}, Z_n) (as a map of subobjects of Z_n.underlying).
    -- Equivalently: B_{n+1}.Factors(to_Z_n_t ≫ Z_n_t.arrow), which we know:
    have h_bnd_fac_to_Z : B_n1_t.Factors (to_Z_n_t ≫ Z_n_t.arrow) := by
      rw [h_to_Z_comp, h_lift_πV']
      apply Subobject.factors_of_factors_right
      change (imageSubobject (oI_bnd ≫ πV')).Factors (oI_bnd ≫ πV')
      rw [Subobject.mk_factors_iff]
      exact ⟨factorThruImage _, by simp⟩
    -- Factor to_Z_n_t through ofLE(B_{n+1}, Z_n)
    have hB_le_Z_n1 : B_n1_t ≤ Z_n_t := by
      change FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1) ≤
        FC.cycleSubobject (s + ↑n) (k - 1) ↑n
      exact le_trans (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑(n + 1))
        ((FC.toSSData bnd (s + ↑n) (k - 1)).Z_anti
          (WithTop.coe_le_coe.mpr (Nat.le_succ n)))
    set factorγ := B_n1_t.factorThru _ h_bnd_fac_to_Z with hfactorγ_def
    have hfactorγ_spec : factorγ ≫ B_n1_t.arrow = to_Z_n_t ≫ Z_n_t.arrow :=
      Subobject.factorThru_arrow _ _ _
    have h_to_Z_eq : to_Z_n_t = factorγ ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 := by
      apply (inferInstance : Mono Z_n_t.arrow).right_cancellation
      simp only [Category.assoc, Subobject.ofLE_arrow, hfactorγ_spec]
    -- Now ψ = to_Z_n_t ≫ pageπ_t = factorγ ≫ ofLE(B_{n+1}, Z_n) ≫ pageπ_t
    rw [hψ_def, h_to_Z_eq, Category.assoc]
    exact imageSubobject_comp_le _ _
  -- === (≥) direction: imageSubobject(ofLE(B_{n+1}, Z_n) ≫ pageπ_t) ≤ imageSubobject(ψ) ===
  · -- Strategy: Define σ_bnd (lifting of oI_bnd through kerZ'), cancel factorB (epi),
    -- use pullback to construct w : PB → kerZ with pb_snd ≫ σ_bnd = w ≫ lift_to_kerZ',
    -- then conclude via imageSubobject_epi_comp' and imageSubobject_comp_le.
    -- === Step 0: Reconstruct shared definitions from (≤) direction ===
    set imgD_bnd := imageSubobject ((FC.fil (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫
      FC.dToK (k - 1)) with himgD_bnd_def
    set I_bnd := imgD_bnd ⊓ FC.fil (s + ↑n) (k - 1) with hI_bnd_def
    set oI_bnd := Subobject.ofLE I_bnd (FC.fil (s + ↑n) (k - 1)) inf_le_right
      with hoI_bnd_def
    set B_n1_t := FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1) with hB_n1_t_def
    set Z_n_t := FC.cycleSubobject (s + ↑n) (k - 1) ↑n with hZ_n_t_def
    have hB_le_Z_n1 : B_n1_t ≤ Z_n_t := by
      change FC.boundarySubobject (s + ↑n) (k - 1) ↑(n + 1) ≤
        FC.cycleSubobject (s + ↑n) (k - 1) ↑n
      exact le_trans (FC.B_le_Z_aux (s + ↑n) (k - 1) ↑(n + 1))
        ((FC.toSSData bnd (s + ↑n) (k - 1)).Z_anti
          (WithTop.coe_le_coe.mpr (Nat.le_succ n)))
    -- === Step 1: Define σ_bnd : I_bnd → kerZ' (lifting oI_bnd through kerZ') ===
    -- oI_bnd ≫ f_n' = 0 because d² = 0 on the image of d.
    have h_oI_fn' : oI_bnd ≫ f_n' = 0 := by
      rw [hf_n'_def]
      rw [show oI_bnd ≫ (FC.fil (s + ↑n) (k - 1)).arrow ≫ FC.d (k - 1) ≫
        cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) =
        (oI_bnd ≫ (FC.fil (s + ↑n) (k - 1)).arrow) ≫ FC.d (k - 1) ≫
        cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) from by
        simp only [Category.assoc]]
      rw [show oI_bnd ≫ (FC.fil (s + ↑n) (k - 1)).arrow = I_bnd.arrow
        from Subobject.ofLE_arrow inf_le_right]
      rw [show I_bnd.arrow = Subobject.ofLE I_bnd imgD_bnd inf_le_left ≫ imgD_bnd.arrow
        from (Subobject.ofLE_arrow inf_le_left).symm]
      simp only [Category.assoc]
      have h_imgD_arrow_d : imgD_bnd.arrow ≫ FC.d (k - 1) = 0 := by
        have hfactor : factorThruImageSubobject
            ((FC.fil (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)) ≫
            imgD_bnd.arrow =
            (FC.fil (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1) :=
          imageSubobject_arrow_comp _
        rw [← cancel_epi (factorThruImageSubobject
            ((FC.fil (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫ FC.dToK (k - 1)))]
        rw [comp_zero, ← Category.assoc, hfactor, Category.assoc,
          FC.dToK_comp_d, comp_zero]
      rw [show Subobject.ofLE I_bnd imgD_bnd inf_le_left ≫ imgD_bnd.arrow ≫ FC.d (k - 1) ≫
        cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) =
        (Subobject.ofLE I_bnd imgD_bnd inf_le_left ≫ (imgD_bnd.arrow ≫ FC.d (k - 1))) ≫
        cokernel.π ((FC.fil (s + ↑n + ↑n) (k - 1 - 1)).arrow) from by
        simp only [Category.assoc]]
      rw [h_imgD_arrow_d, comp_zero, zero_comp]
    set σ_bnd := factorThruKernelSubobject f_n' oI_bnd h_oI_fn' with hσ_bnd_def
    have hσ_bnd_spec : σ_bnd ≫ kerZ'.arrow = oI_bnd :=
      factorThruKernelSubobject_comp_arrow f_n' oI_bnd h_oI_fn'
    -- === Step 2: Cancel factorB (epi) ===
    set factorB := factorThruImageSubobject (oI_bnd ≫ πV') with hfactorB_def
    haveI hfactorB_epi : Epi factorB := inferInstance
    -- The goal uses (toSSData ...).B / .Z which are
    -- definitionally boundarySubobject / cycleSubobject.
    -- We need to show the goal matches our local names.
    change imageSubobject (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ pageπ_t) ≤
      imageSubobject ψ
    have h_factorB_ofLE : factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫
        Z_n_t.arrow = oI_bnd ≫ πV' := by
      rw [show factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ Z_n_t.arrow =
        (factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1) ≫ Z_n_t.arrow from
        (Category.assoc _ _ _).symm]
      rw [show (factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1) ≫
        Z_n_t.arrow = factorB ≫ B_n1_t.arrow from by
          rw [Category.assoc, Subobject.ofLE_arrow]]
      exact imageSubobject_arrow_comp (oI_bnd ≫ πV')
    -- === Step 3: Show factorB ≫ ofLE = σ_to_Z via mono cancellation ===
    set σ_to_Z := σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') with hσ_to_Z_def
    have hσ_to_Z_spec : σ_to_Z ≫ Z_n_t.arrow = oI_bnd ≫ πV' := by
      change (σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV')) ≫
        (imageSubobject (kerZ'.arrow ≫ πV')).arrow = oI_bnd ≫ πV'
      simp only [Category.assoc, imageSubobject_arrow_comp]
      rw [show σ_bnd ≫ kerZ'.arrow ≫ πV' = (σ_bnd ≫ kerZ'.arrow) ≫ πV'
        from (Category.assoc _ _ _).symm, hσ_bnd_spec]
    have h_factorB_ofLE_eq : factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 = σ_to_Z := by
      apply (inferInstance : Mono Z_n_t.arrow).right_cancellation
      rw [Category.assoc, h_factorB_ofLE, hσ_to_Z_spec]
    -- Goal (after show): imageSubobject(ofLE(B_n1_t, Z_n_t) ≫ pageπ_t) ≤ imageSubobject(ψ)
    -- Rewrite factorB out:
    -- imageSubobject(factorB ≫ ofLE ≫ pageπ_t) = imageSubobject(ofLE ≫ pageπ_t)
    -- Then factorB ≫ ofLE = σ_to_Z = σ_bnd ≫ q,
    -- and ψ = to_Z_n_t ≫ pageπ_t = lift_to_kerZ' ≫ q ≫ pageπ_t
    -- Use have + calc to avoid rewrite issues with opaque names
    have h_img_ofLE_eq : imageSubobject (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ pageπ_t) =
        imageSubobject (σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t) := by
      rw [← imageSubobject_epi_comp' factorB
        (Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ pageπ_t)]
      congr 1
      rw [show factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1 ≫ pageπ_t =
        (factorB ≫ Subobject.ofLE B_n1_t Z_n_t hB_le_Z_n1) ≫ pageπ_t from
        (Category.assoc _ _ _).symm, h_factorB_ofLE_eq, hσ_to_Z_def, Category.assoc]
    rw [h_img_ofLE_eq]
    -- Goal: imageSubobject(σ_bnd ≫ q ≫ pageπ_t) ≤ imageSubobject(ψ)
    suffices h_le :
        imageSubobject (σ_bnd ≫
          factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t) ≤
        imageSubobject (lift_to_kerZ' ≫
          factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t) by
      calc imageSubobject (σ_bnd ≫
              factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t)
          ≤ imageSubobject (lift_to_kerZ' ≫
              factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫
                pageπ_t) := h_le
        _ = imageSubobject ψ := by rw [hψ_def, hto_Z_n_t_def, Category.assoc]
    -- Goal: imageSubobject(σ_bnd ≫ q ≫ pageπ_t) ≤ imageSubobject(lift_to_kerZ' ≫ q ≫ pageπ_t)
    -- where q = factorThruImageSubobject(kerZ'.arrow ≫ πV')
    -- === Step 4: Pullback of factorD (epi) against oI_to_imgD ===
    have h_idx_eq_s' : (s : ℤ) + ↑n - ↑(n + 1) + 1 = s := by push_cast; ring
    set imgD_src := (FC.fil (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)).arrow ≫
      FC.dToK (k - 1) with himgD_src_def
    set factorD := factorThruImageSubobject imgD_src with hfactorD_def
    haveI hfactorD_epi : Epi factorD := inferInstance
    have hfactorD_spec : factorD ≫ imgD_bnd.arrow = imgD_src :=
      imageSubobject_arrow_comp imgD_src
    set oI_to_imgD := Subobject.ofLE I_bnd imgD_bnd inf_le_left with hoI_to_imgD_def
    set pb_fst := Limits.pullback.fst factorD oI_to_imgD
    set pb_snd := Limits.pullback.snd factorD oI_to_imgD
    have hpb_cond : pb_fst ≫ factorD = pb_snd ≫ oI_to_imgD := Limits.pullback.condition
    haveI : Epi pb_snd := Abelian.epi_pullback_of_epi_f factorD oI_to_imgD
    -- === Step 5: Transport eqH and prove eqH ≫ fil(s)(k).arrow ≫ d(k) = imgD_src ===
    set eqH := eqToHom (show Subobject.underlying.obj
        (FC.fil (s + ↑n - ↑(n + 1) + 1) ((k - 1) + 1)) =
        Subobject.underlying.obj (FC.fil s k) from by
      rw [h_idx_eq_s', show (k - 1 : ℤ) + 1 = k from by ring]) with heqH_def
    have h_eqH_d : eqH ≫ (FC.fil s k).arrow ≫ FC.d k = imgD_src := by
      conv_lhs => rw [← FC.eqToHom_arrow_dToK s k]
      rw [heqH_def]; simp only [← Category.assoc]; rw [eqToHom_trans]
      rw [himgD_src_def]; congr 1
      exact (Subobject.arrow_congr _ _ (by congr 1))
    -- pb_fst ≫ imgD_src = pb_snd ≫ I_bnd.arrow
    have h_pb_imgD : pb_fst ≫ imgD_src = pb_snd ≫ I_bnd.arrow := by
      calc pb_fst ≫ imgD_src
          = pb_fst ≫ (factorD ≫ imgD_bnd.arrow) := by rw [imageSubobject_arrow_comp imgD_src]
        _ = (pb_fst ≫ factorD) ≫ imgD_bnd.arrow := by rw [Category.assoc]
        _ = (pb_snd ≫ oI_to_imgD) ≫ imgD_bnd.arrow := by rw [hpb_cond]
        _ = pb_snd ≫ (oI_to_imgD ≫ imgD_bnd.arrow) := by simp only [Category.assoc]
        _ = pb_snd ≫ I_bnd.arrow := by congr 1; exact Subobject.ofLE_arrow inf_le_left
    -- === Step 6: (pb_fst ≫ eqH) ≫ f_n = 0 ===
    have h_pb_fn : (pb_fst ≫ eqH) ≫ f_n = 0 := by
      rw [hf_n_def]; simp only [Category.assoc]
      rw [show pb_fst ≫ eqH ≫ (FC.fil s k).arrow ≫ FC.d k ≫
        cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) =
        (pb_fst ≫ (eqH ≫ (FC.fil s k).arrow ≫ FC.d k)) ≫
        cokernel.π ((FC.fil (s + ↑n) (k - 1)).arrow) from by simp only [Category.assoc]]
      rw [h_eqH_d]
      -- Goal: (pb_fst ≫ imgD_src) ≫ cokernel.π(fil(s+n)(k-1).arrow) = 0
      rw [h_pb_imgD]
      -- Goal: (pb_snd ≫ I_bnd.arrow) ≫ cokernel.π(fil(s+n)(k-1).arrow) = 0
      simp only [Category.assoc]
      rw [show I_bnd.arrow = oI_bnd ≫ (FC.fil (s + ↑n) (k - 1)).arrow
        from (Subobject.ofLE_arrow inf_le_right).symm]
      simp only [Category.assoc]
      rw [cokernel.condition, comp_zero, comp_zero]
    -- === Step 7: Factor through kerZ ===
    set w := factorThruKernelSubobject f_n (pb_fst ≫ eqH) h_pb_fn with hw_def
    have hw_spec : w ≫ kerZ.arrow = pb_fst ≫ eqH :=
      factorThruKernelSubobject_comp_arrow f_n (pb_fst ≫ eqH) h_pb_fn
    -- === Step 8: pb_snd ≫ σ_bnd = w ≫ lift_to_kerZ' (mono cancellation on kerZ'.arrow) ===
    have h_pb_snd_σ_eq : pb_snd ≫ σ_bnd = w ≫ lift_to_kerZ' := by
      apply (inferInstance : Mono kerZ'.arrow).right_cancellation
      rw [Category.assoc, hσ_bnd_spec, Category.assoc, h_ltk_spec]
      -- Goal: pb_snd ≫ oI_bnd = w ≫ lift_n
      -- Both sides map to fil(s+n)(k-1).underlying. Use mono cancellation on fil(s+n)(k-1).arrow.
      apply (inferInstance : Mono (FC.fil (s + ↑n) (k - 1)).arrow).right_cancellation
      simp only [Category.assoc]
      rw [h_lift_spec, ← Category.assoc w kerZ.arrow, hw_spec,
        Category.assoc, h_eqH_d, h_pb_imgD]
      -- LHS: pb_snd ≫ oI_bnd ≫ fil(s+n)(k-1).arrow  RHS: pb_snd ≫ I_bnd.arrow
      congr 1; exact Subobject.ofLE_arrow inf_le_right
    -- === Step 9: Conclude ===
    rw [← imageSubobject_epi_comp' pb_snd
      (σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t)]
    rw [show pb_snd ≫ σ_bnd ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t =
      (pb_snd ≫ σ_bnd) ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t from by
      simp only [Category.assoc]]
    rw [h_pb_snd_σ_eq]
    rw [show (w ≫ lift_to_kerZ') ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t =
      w ≫ (lift_to_kerZ' ≫ factorThruImageSubobject (kerZ'.arrow ≫ πV') ≫ pageπ_t) from by
      simp only [Category.assoc]]
    exact imageSubobject_comp_le _ _

set_option maxHeartbeats 6400000 in
-- Assembling all fields requires heavy unification of subobject and page computations
/-- Assembles a `SpectralSequence C (ℤ × ℤ)` from a filtered complex.
    The index type `ℤ × ℤ` has `(s, k)` = (filtration degree, homological degree).
    The differential `d_r` on the page `E_r` is induced by the original differential
    on the complex. Z_succ and B_succ encode how cycles and boundaries evolve. -/
noncomputable def FilteredComplex.toSpectralSequence (FC : FilteredComplex C)
    (bnd : FC.IsBounded) : SpectralSequence C (ℤ × ℤ) where
  r₀ := 0
  ssData := fun ⟨s, k⟩ => FC.toSSData bnd s k
  diffDeg := fun r => (r, -1)
  -- The differential d_r on page E_r is induced by the original differential d
  -- of the filtered complex. It maps E_r^{s,k} → E_r^{s+r,k-1}.
  -- The construction sends the class of x ∈ Z_r^{s,k} to the class of dx in
  -- Z_r^{s+r,k-1}/B_r^{s+r,k-1}, using d_preserves_fil and d²=0.
  d := fun r ⟨s, k⟩ =>
    -- d r (s,k) : page ↑(r-0).toNat at (s,k) ⟶ page ↑(r-0).toNat at (s+r, k+(-1))
    -- Use dite on (0 ≤ r). When r ≥ 0: pageDiff ≫ eqToHom; when r < 0: 0.
    -- Note: (r - 0).toNat = r.toNat and ↑r.toNat = r when 0 ≤ r.
    if hr : 0 ≤ r then
      eqToHom (by simp [sub_zero]) ≫
        FC.pageDifferential bnd s k r.toNat ≫
        eqToHom (by simp [sub_zero, Int.toNat_of_nonneg hr]; ring_nf)
    else 0
  d_comp_d := fun r ⟨s, k⟩ => by
    -- d² = 0: follows from pageDifferential_comp and eqToHom transport.
    dsimp only []
    split_ifs with hr
    · -- Positive case: substitute r = ↑n to make r.toNat = n definitionally
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
      -- Now (↑n).toNat = n definitionally. Goal has eqToHom transports around
      -- pageDifferential's. Collapse adjacent eqToHom's and simplify.
      simp only [Int.toNat_natCast, eqToHom_refl, Category.id_comp, Category.comp_id]
      exact FC.pageDifferential_comp bnd s k n
    · exact zero_comp
  induced_d := fun r ⟨s, k⟩ =>
    (FC.toSSData bnd s k).pageπ ↑(r - 0).toNat
  induced_d_eq := fun r ⟨s, k⟩ => by
    simp
  Z_succ := fun r ⟨s, k⟩ hr => by
    -- === Z_succ: ker(d_r) at (s,k) = Z_{n+1}/B_n inside E_n^{s,k} ===
    -- Phase 1: Eliminate dite and eqToHom
    dsimp only []
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    simp only [Int.toNat_natCast,
      dif_pos (Int.natCast_nonneg n), eqToHom_refl, Category.id_comp, Category.comp_id]
    -- Goal: kernelSubobject(pageDifferential bnd s k n) =
    --       imageSubobject(ofLE(Z_{n+1}, Z_n) ≫ pageπ n)
    -- Phase 2: le_antisymm
    have hsub : (↑n : ℤ) - 0 = ↑n := sub_zero _
    apply le_antisymm
    · -- (≤): kernelSubobject(pageDiff) ≤ imageSubobject(ofLE(Z_{n+1}, Z_n) ≫ pageπ n)
      exact pageDifferential_Z_succ_le FC bnd s k n
    · -- (≥): imageSubobject(ofLE(Z_{n+1}, Z_n) ≫ pageπ n) ≤ kernelSubobject(pageDiff)
      exact pageDifferential_Z_succ_ge FC bnd s k n
  B_succ := fun r ⟨s, k⟩ hr => by
    -- Phase 1: Eliminate dite and eqToHom
    dsimp only []
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    simp only [Int.toNat_natCast,
      dif_pos (Int.natCast_nonneg n), eqToHom_refl, Category.id_comp, Category.comp_id]
    -- Goal: imageSubobject(pageDifferential bnd s k n) =
    --       imageSubobject(ofLE(B_{n+1}, Z_n, _) ≫ pageπ n) at target (s+↑n, k-1)
    exact FC.pageDifferential_B_succ bnd s k n

/-! ### Weak convergence -/

/-- The spectral sequence of a bounded filtered complex converges weakly to
    the homology `H(A)`: provides a `Convergence` structure relating the
    `E∞`-page to the associated graded of the homology filtration. -/
noncomputable def FilteredComplex.weakConvergence (FC : FilteredComplex C)
    (bnd : FC.IsBounded) :
    Convergence (FC.toSpectralSequence bnd) FC.homologyObj FC.homologyFiltration where
  -- The natural reindexing: (s, k) ↦ (s, k) (identity on bidegrees)
  reindex := fun k => k
  -- TODO: The convergence isomorphism E∞^{s,k} ≅ gr^s H_k(A) requires
  -- the correct Z/B in toSSData and correct F in homologyFiltration.
  -- With the current placeholder definitions (Z=⊤, B=⊥, F=⊤), this iso
  -- cannot be constructed meaningfully. Deferred to next round.
  iso := fun ⟨s, k⟩ => by
    change (FC.toSSData bnd s k).eInfty ≅ FC.homologyFiltration.associatedGraded s k
    unfold SSData.eInfty SSData.page Filtration.associatedGraded
    -- Goal: cokernel(ofLE (B⊤) (Z⊤) _) ≅ cokernel(ofLE (F_{s+1}H_k) (F_sH_k) _)
    -- Abbreviations
    let S := ShortComplex.mk (FC.d (k + 1)) (FC.d (k + 1 - 1)) (FC.d_comp_d (k + 1))
    let e_deg : FC.A k = FC.A (k + 1 - 1) := congr_arg FC.A (show k = k + 1 - 1 by omega)
    let ι_fil := Subobject.ofLE (FC.fil (s + 1) k) (FC.fil s k) (FC.fil_anti s k)
    let πV := cokernel.π ι_fil
    let f_Z := (FC.fil s k).arrow ≫ FC.d k
    let kerZ := kernelSubobject f_Z
    -- φ_to_X2 : kerZ.underlying → S.X₂ (= FC.A(k+1-1))
    let φ_to_X2 := kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg
    have h_lift : φ_to_X2 ≫ S.g = 0 := by
      change (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) ≫ S.g = 0
      simp only [Category.assoc]
      have : eqToHom e_deg ≫ S.g =
          FC.d k ≫ eqToHom (congr_arg FC.A (show k - 1 = (k + 1 - 1) - 1 by omega)) := by
        simp [S]
      rw [this, ← Category.assoc, ← Category.assoc,
        show (kerZ.arrow ≫ (FC.fil s k).arrow) ≫ FC.d k = kerZ.arrow ≫ f_Z
          from by simp only [f_Z, Category.assoc],
        kernelSubobject_arrow_comp, zero_comp]
    -- φ_pre : kerZ.underlying → S.homology
    let φ_pre := S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ
    -- I_s for the homologyFiltration
    let I_s := kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1)
    have h_zero_s : I_s.arrow ≫ S.g = 0 := by
      rw [show I_s.arrow = Subobject.ofLE I_s (kernelSubobject S.g)
          inf_le_left ≫ (kernelSubobject S.g).arrow
        from (Subobject.ofLE_arrow inf_le_left).symm,
        Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    let gen_s := S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ
    -- Show φ_to_X2 factors through I_s.arrow, so φ_pre factors through gen_s
    -- This means imageSubobject(φ_pre) ≤ imageSubobject(gen_s) = F_s
    have h_factors_I : I_s.Factors φ_to_X2 := by
      rw [show I_s = kernelSubobject S.g ⊓ FC.fil s (k + 1 - 1) from rfl,
          Subobject.inf_factors φ_to_X2]
      refine ⟨kernelSubobject_factors S.g φ_to_X2 h_lift, ?_⟩
      -- Need: (FC.fil s (k+1-1)).Factors φ_to_X2
      -- φ_to_X2 = kerZ.arrow ≫ (fil s k).arrow ≫ eqToHom(e_deg)
      -- We use: (fil s k).arrow ≫ eqToHom = eqToHom_sub ≫ (fil s (k+1-1)).arrow
      -- so φ_to_X2 = (kerZ.arrow ≫ eqToHom_sub) ≫ (fil s (k+1-1)).arrow
      let e_sub := congr_arg (fun j => Subobject.underlying.obj (FC.fil s j))
          (show k = k + 1 - 1 by omega)
      have h_transport : (FC.fil s k).arrow ≫ eqToHom e_deg = eqToHom e_sub ≫
          (FC.fil s (k + 1 - 1)).arrow := by
        -- Use the Mono property: compose both sides with the identity on A(k+1-1)
        -- and show they agree. Actually, we can use eqToHom_naturality.
        -- eqToHom at object level is functorial, so the naturality square commutes.
        -- For `FC.fil s` applied to equal indices, the arrow commutes with eqToHom.
        -- We prove this by induction on the proof of equality.
        -- Since we can't subst directly, use proof irrelevance + a general lemma.
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil s a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j)) h) ≫
            (FC.fil s b).arrow := by
          intro a b h; subst h; simp
        exact this k (k + 1 - 1) (by omega)
      have h_φ_eq : φ_to_X2 = (kerZ.arrow ≫ eqToHom e_sub) ≫
          (FC.fil s (k + 1 - 1)).arrow := by
        change kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg =
          (kerZ.arrow ≫ eqToHom e_sub) ≫ (FC.fil s (k + 1 - 1)).arrow
        rw [Category.assoc, h_transport, ← Category.assoc]
      rw [h_φ_eq]
      exact Subobject.factors_comp_arrow _
    -- Factor: kerZ → I_s
    let kerZ_to_Is := Subobject.factorThru I_s φ_to_X2 h_factors_I
    -- Key property: kerZ_to_Is ≫ I_s.arrow = φ_to_X2
    have h_kerZ_to_Is : kerZ_to_Is ≫ I_s.arrow = φ_to_X2 :=
      Subobject.factorThru_arrow I_s φ_to_X2 h_factors_I
    -- liftCycles is functorial: kerZ_to_Is ≫ gen_s = φ_pre
    have h_func : kerZ_to_Is ≫ gen_s = φ_pre := by
      change kerZ_to_Is ≫ (S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ) =
        S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ
      rw [← Category.assoc]
      congr 1
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.liftCycles_i, S.liftCycles_i, h_kerZ_to_Is]
    -- imageSubobject(φ_pre) ≤ imageSubobject(gen_s) = F_s
    have h_img_le : imageSubobject φ_pre ≤ imageSubobject gen_s := by
      rw [show φ_pre = kerZ_to_Is ≫ gen_s from h_func.symm]
      exact imageSubobject_comp_le _ _
    -- φ_pre factors through F_s = imageSubobject(gen_s)
    have h_fac_Fs : (imageSubobject gen_s).Factors φ_pre := by
      have : φ_pre = (kerZ_to_Is ≫ factorThruImageSubobject gen_s) ≫
          (imageSubobject gen_s).arrow := by
        rw [Category.assoc, imageSubobject_arrow_comp]
        exact h_func.symm
      rw [this]
      exact Subobject.factors_comp_arrow _
    let φ_to_Fs := Subobject.factorThru (imageSubobject gen_s) φ_pre h_fac_Fs
    have h_φ_to_Fs : φ_to_Fs ≫ (imageSubobject gen_s).arrow = φ_pre :=
      Subobject.factorThru_arrow _ _ h_fac_Fs
    -- Compose with cokernel projection to get kerZ → RHS
    -- RHS = cokernel(ofLE F_{s+1} F_s _)
    -- We need the cokernel.π for the RHS
    -- But first, F_s and F_{s+1} are from homologyFiltration, not our local gen_s/gen_s1.
    -- They should be definitionally equal (or propositionally equal)
    -- to imageSubobject gen_s / gen_s1.
    -- Let's show they match.
    -- ======================================
    -- CONSTRUCTION OF THE CONVERGENCE ISOMORPHISM
    -- E_∞ = Z_⊤/B_⊤ ≅ gr^s H_k = F_s H_k / F_{s+1} H_k
    --
    -- Forward: E_∞ → gr^s H_k via φ_to_Fs
    -- Inverse: gr^s H_k → E_∞ via kerZ.arrow ≫ πV
    -- ======================================
    -- Step 1: Forward map on Z_⊤
    -- We build fwd_Z : Z_⊤.underlying → gr^s H_k (the RHS)
    -- by descending φ_to_Fs ≫ cokernel.π through the epi
    -- factorThruImageSubobject(kerZ.arrow ≫ πV) : kerZ → Z_⊤
    -- The RHS cokernel projection
    let πRHS := cokernel.π (Subobject.ofLE
      (FC.homologyFiltration.F (s + 1) k)
      (FC.homologyFiltration.F s k)
      (FC.homologyFiltration.mono s k))
    -- The composed map kerZ → gr^s H_k
    let fwd_kerZ := φ_to_Fs ≫ πRHS
    -- The epi from kerZ to Z_⊤
    let e_Z := factorThruImageSubobject (kerZ.arrow ≫ πV)
    -- Descent condition: kernel.ι(e_Z) ≫ fwd_kerZ = 0
    -- This says: if x ∈ kerZ with kerZ.arrow(x) ∈ F^{s+1}, then φ_to_Fs(x) ∈ F_{s+1} H_k
    have h_desc_fwd : kernel.ι e_Z ≫ fwd_kerZ = 0 := by
      -- kernel.ι e_Z ≫ (kerZ.arrow ≫ πV) = 0 (kernel condition + image factorization)
      have h_ker_πV : kernel.ι e_Z ≫ kerZ.arrow ≫ πV = 0 := by
        have h0 : kernel.ι e_Z ≫ e_Z = 0 := kernel.condition e_Z
        have h1 : factorThruImageSubobject (kerZ.arrow ≫ πV) ≫
            (imageSubobject (kerZ.arrow ≫ πV)).arrow =
            kerZ.arrow ≫ πV := by simp [imageSubobject_arrow_comp]
        calc kernel.ι e_Z ≫ kerZ.arrow ≫ πV
            = kernel.ι e_Z ≫ (e_Z ≫
                (imageSubobject (kerZ.arrow ≫ πV)).arrow) := by rw [h1]
          _ = (kernel.ι e_Z ≫ e_Z) ≫ (imageSubobject (kerZ.arrow ≫ πV)).arrow :=
                (Category.assoc _ _ _).symm
          _ = 0 ≫ _ := by rw [h0]
          _ = 0 := zero_comp
      -- Lift through ι_fil
      have h_ker_πV' : (kernel.ι e_Z ≫ kerZ.arrow) ≫ cokernel.π ι_fil = 0 := by
        rw [Category.assoc]; exact h_ker_πV
      set lift_s1 := Abelian.monoLift ι_fil (kernel.ι e_Z ≫ kerZ.arrow) h_ker_πV'
      have h_lift_s1 : lift_s1 ≫ ι_fil = kernel.ι e_Z ≫ kerZ.arrow :=
        Abelian.monoLift_comp _ _ _
      -- kernel.ι e_Z ≫ φ_to_X2 factors through I_{s+1} = ker(S.g) ∩ fil(s+1, k+1-1)
      set I_s1 := kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1)
      have h_zero_s1 : I_s1.arrow ≫ S.g = 0 := by
        rw [show I_s1.arrow = Subobject.ofLE I_s1 (kernelSubobject S.g)
            inf_le_left ≫ (kernelSubobject S.g).arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc, kernelSubobject_arrow_comp, comp_zero]
      set gen_s1 := S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ
      -- Key factorization: kernel.ι e_Z ≫ φ_to_X2 lies in I_{s+1}
      -- φ_to_X2 = kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg
      -- kernel.ι e_Z ≫ kerZ.arrow = lift_s1 ≫ ι_fil (h_lift_s1)
      -- So kernel.ι e_Z ≫ φ_to_X2 = lift_s1 ≫ ι_fil ≫ (fil s k).arrow ≫ eqToHom
      --   = lift_s1 ≫ (fil(s+1,k)).arrow ≫ eqToHom
      --   = (lift_s1 ≫ eqToHom_sub) ≫ (fil(s+1,k+1-1)).arrow
      -- which factors through fil(s+1,k+1-1).
      -- Also kernel.ι e_Z ≫ φ_to_X2 ≫ S.g = 0 (from h_lift).
      -- So it's in ker(S.g) ∩ fil(s+1,k+1-1) = I_{s+1}.
      -- Then kernel.ι e_Z ≫ φ_pre = α ≫ gen_s1 (liftCycles functoriality)
      -- = (α ≫ fTI gen_s1) ≫ (F_{s+1}).arrow
      -- And kernel.ι e_Z ≫ φ_to_Fs ≫ (F_s).arrow = kernel.ι e_Z ≫ φ_pre
      -- So kernel.ι e_Z ≫ φ_to_Fs = (α ≫ fTI gen_s1) ≫ ofLE(F_{s+1}, F_s) (mono cancel)
      -- Step B: factor kernel.ι e_Z ≫ φ_to_X2 through I_{s+1}
      have h_ι_arrow : ι_fil ≫ (FC.fil s k).arrow = (FC.fil (s + 1) k).arrow :=
        Subobject.ofLE_arrow (FC.fil_anti s k)
      have h_transport_s1 : (FC.fil (s + 1) k).arrow ≫ eqToHom e_deg =
          eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
            (show k = k + 1 - 1 by omega)) ≫
          (FC.fil (s + 1) (k + 1 - 1)).arrow := by
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil (s + 1) a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j)) h) ≫
            (FC.fil (s + 1) b).arrow := by
          intro a b h; subst h; simp
        exact this k (k + 1 - 1) (by omega)
      have h_ker_lift_sg : (kernel.ι e_Z ≫ φ_to_X2) ≫ S.g = 0 := by
        rw [Category.assoc]; exact (h_lift ▸ comp_zero)
      have h_ker_in_fil_s1 :
          (FC.fil (s + 1) (k + 1 - 1)).Factors (kernel.ι e_Z ≫ φ_to_X2) := by
        have h_eq : kernel.ι e_Z ≫ φ_to_X2 =
            (lift_s1 ≫ eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
              (show k = k + 1 - 1 by omega))) ≫
            (FC.fil (s + 1) (k + 1 - 1)).arrow := by
          change kernel.ι e_Z ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) = _
          rw [show kernel.ι e_Z ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
              (kernel.ι e_Z ≫ kerZ.arrow) ≫ ((FC.fil s k).arrow ≫ eqToHom e_deg) by
            simp only [Category.assoc]]
          rw [h_lift_s1.symm]
          rw [show (lift_s1 ≫ ι_fil) ≫ ((FC.fil s k).arrow ≫ eqToHom e_deg) =
              lift_s1 ≫ (ι_fil ≫ (FC.fil s k).arrow) ≫ eqToHom e_deg by
            simp only [Category.assoc]]
          rw [h_ι_arrow, h_transport_s1]
          simp only [Category.assoc]
        rw [h_eq]; exact Subobject.factors_comp_arrow _
      have h_fac_I_s1 : I_s1.Factors (kernel.ι e_Z ≫ φ_to_X2) := by
        rw [show I_s1 = kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1) from rfl,
            Subobject.inf_factors]
        exact ⟨kernelSubobject_factors S.g _ h_ker_lift_sg, h_ker_in_fil_s1⟩
      let ker_to_I_s1 := Subobject.factorThru I_s1 (kernel.ι e_Z ≫ φ_to_X2) h_fac_I_s1
      have h_ker_to_I_s1 : ker_to_I_s1 ≫ I_s1.arrow = kernel.ι e_Z ≫ φ_to_X2 :=
        Subobject.factorThru_arrow _ _ _
      -- Step C: liftCycles functoriality
      have h_func_s1 : ker_to_I_s1 ≫ gen_s1 = kernel.ι e_Z ≫ φ_pre := by
        change ker_to_I_s1 ≫ (S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ) =
          kernel.ι e_Z ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ)
        rw [← Category.assoc, ← Category.assoc]; congr 1
        apply (cancel_mono S.iCycles).mp
        rw [Category.assoc, S.liftCycles_i, Category.assoc, S.liftCycles_i, h_ker_to_I_s1]
      -- Step D: factor through ofLE(F_{s+1}, F_s)
      have h_Fs1_le_Fs : FC.homologyFiltration.F (s + 1) k ≤
          FC.homologyFiltration.F s k :=
        FC.homologyFiltration.mono s k
      have h_ofLE_arrow : Subobject.ofLE (FC.homologyFiltration.F (s + 1) k)
          (FC.homologyFiltration.F s k) h_Fs1_le_Fs ≫
          (FC.homologyFiltration.F s k).arrow =
          (FC.homologyFiltration.F (s + 1) k).arrow :=
        Subobject.ofLE_arrow h_Fs1_le_Fs
      have h_factor_ofLE : kernel.ι e_Z ≫ φ_to_Fs =
          (ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
          Subobject.ofLE (FC.homologyFiltration.F (s + 1) k)
            (FC.homologyFiltration.F s k) h_Fs1_le_Fs := by
        apply (cancel_mono (imageSubobject gen_s).arrow).mp
        rw [Category.assoc, h_φ_to_Fs]
        -- LHS: kernel.ι e_Z ≫ φ_pre
        -- RHS: ((ker_to_I_s1 ≫ fTI gen_s1) ≫ ofLE) ≫ (imageSubobject gen_s).arrow
        -- Rewrite RHS to ker_to_I_s1 ≫ gen_s1 = kernel.ι e_Z ≫ φ_pre
        have h_rhs : ((ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
            Subobject.ofLE (FC.homologyFiltration.F (s + 1) k)
              (FC.homologyFiltration.F s k) h_Fs1_le_Fs) ≫
            (imageSubobject gen_s).arrow =
            ker_to_I_s1 ≫ gen_s1 := by
          -- (imageSubobject gen_s).arrow = (FC.homologyFiltration.F s k).arrow definitionally
          change ((ker_to_I_s1 ≫ factorThruImageSubobject gen_s1) ≫
            Subobject.ofLE (FC.homologyFiltration.F (s + 1) k)
              (FC.homologyFiltration.F s k) h_Fs1_le_Fs) ≫
            (FC.homologyFiltration.F s k).arrow = ker_to_I_s1 ≫ gen_s1
          simp only [Category.assoc]
          rw [h_ofLE_arrow]
          -- Now: ker_to_I_s1 ≫ fTI gen_s1 ≫ (imageSubobject gen_s1).arrow
          -- = ker_to_I_s1 ≫ gen_s1
          -- (FC.homologyFiltration.F (s+1) k).arrow = (imageSubobject gen_s1).arrow definitionally
          change ker_to_I_s1 ≫ factorThruImageSubobject gen_s1 ≫
            (imageSubobject gen_s1).arrow = ker_to_I_s1 ≫ gen_s1
          rw [imageSubobject_arrow_comp]
        rw [h_rhs]
        exact h_func_s1.symm
      -- Step E: compose with πRHS = cokernel.π → 0
      change kernel.ι e_Z ≫ (φ_to_Fs ≫ πRHS) = 0
      rw [← Category.assoc, h_factor_ofLE, Category.assoc, Category.assoc]
      rw [show Subobject.ofLE (FC.homologyFiltration.F (s + 1) k)
            (FC.homologyFiltration.F s k) h_Fs1_le_Fs ≫ πRHS = 0
        from cokernel.condition _]
      rw [comp_zero, comp_zero]
    -- Descended map on Z_⊤
    let fwd_Z := Abelian.epiDesc e_Z fwd_kerZ h_desc_fwd
    -- Property: e_Z ≫ fwd_Z = fwd_kerZ
    have h_fwd_Z : e_Z ≫ fwd_Z = fwd_kerZ := Abelian.comp_epiDesc _ _ _
    -- Step 2: Show fwd_Z kills B_⊤
    -- Need: ofLE(B_⊤, Z_⊤, _) ≫ fwd_Z = 0
    have h_fwd_kills_B : Subobject.ofLE
        ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
        ((FC.toSSData bnd s k).B_le_Z ⊤) ≫ fwd_Z = 0 := by
      -- === Proof that fwd_Z kills B_⊤ ===
      -- Local boundary notation
      let imgD := imageSubobject (FC.dToK k)
      let I_B := imgD ⊓ FC.fil s k
      let oI := Subobject.ofLE I_B (FC.fil s k) inf_le_right
      -- oI ≫ f_Z = 0 (boundary elements are cycles)
      have h_oI_zero : oI ≫ f_Z = 0 := by
        change Subobject.ofLE I_B (FC.fil s k) inf_le_right ≫
          (FC.fil s k).arrow ≫ FC.d k = 0
        rw [← Category.assoc, Subobject.ofLE_arrow]
        rw [show I_B.arrow =
            Subobject.ofLE I_B imgD inf_le_left ≫ imgD.arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, comp_zero]
      -- Factor oI through kerZ
      let oI_lift := factorThruKernelSubobject f_Z oI h_oI_zero
      have h_oI_lift : oI_lift ≫ kerZ.arrow = oI :=
        factorThruKernelSubobject_comp_arrow f_Z oI h_oI_zero
      -- Step A: factorThruImageSubobject(oI ≫ πV) ≫ ofLE(B,Z) = oI_lift ≫ e_Z
      have h_fti_ofLE : factorThruImageSubobject (oI ≫ πV) ≫
          Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
          ((FC.toSSData bnd s k).B_le_Z ⊤) = oI_lift ≫ e_Z := by
        apply (cancel_mono ((FC.toSSData bnd s k).Z ⊤).arrow).mp
        rw [Category.assoc, Subobject.ofLE_arrow]
        change factorThruImageSubobject (oI ≫ πV) ≫
          ((FC.toSSData bnd s k).B ⊤).arrow = (oI_lift ≫ e_Z) ≫ _
        rw [show ((FC.toSSData bnd s k).B ⊤).arrow =
            (imageSubobject (oI ≫ πV)).arrow from rfl]
        rw [imageSubobject_arrow_comp]
        rw [Category.assoc]
        rw [show e_Z ≫ ((FC.toSSData bnd s k).Z ⊤).arrow =
          kerZ.arrow ≫ πV from imageSubobject_arrow_comp (kerZ.arrow ≫ πV)]
        rw [← Category.assoc, h_oI_lift]
      -- Step B: Cancel epi
      rw [← cancel_epi (factorThruImageSubobject (oI ≫ πV))]
      rw [comp_zero, ← Category.assoc, h_fti_ofLE]
      -- Goal: (oI_lift ≫ e_Z) ≫ fwd_Z = 0
      rw [Category.assoc, h_fwd_Z]
      -- Goal: oI_lift ≫ fwd_kerZ = 0
      change oI_lift ≫ (φ_to_Fs ≫ πRHS) = 0
      rw [← Category.assoc]
      -- Step C: Show oI_lift ≫ φ_to_Fs = 0
      suffices h_oI_φ_to_Fs : oI_lift ≫ φ_to_Fs = 0 by
        rw [h_oI_φ_to_Fs, zero_comp]
      apply (cancel_mono (imageSubobject gen_s).arrow).mp
      rw [Category.assoc, h_φ_to_Fs, zero_comp]
      -- Goal: oI_lift ≫ φ_pre = 0
      change oI_lift ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ) = 0
      rw [← Category.assoc]
      -- Step D: oI_lift ≫ φ_to_X2 = I_B.arrow ≫ eqToHom e_deg
      have h_comp_φ : oI_lift ≫ φ_to_X2 = I_B.arrow ≫ eqToHom e_deg := by
        change oI_lift ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
          I_B.arrow ≫ eqToHom e_deg
        rw [← Category.assoc, ← Category.assoc,
          show oI_lift ≫ kerZ.arrow = oI from h_oI_lift,
          show oI ≫ (FC.fil s k).arrow = I_B.arrow
            from Subobject.ofLE_arrow inf_le_right]
      -- Step E: I_B.arrow ≫ eqToHom = ofLE(I_B, imgD, _) ≫ imgD.arrow ≫ eqToHom
      have h_IB_factor : I_B.arrow ≫ eqToHom e_deg =
          Subobject.ofLE I_B imgD inf_le_left ≫ (imgD.arrow ≫ eqToHom e_deg) := by
        rw [← Category.assoc, Subobject.ofLE_arrow]
      -- Step F: imgD.arrow ≫ eqToHom ≫ S.g = 0
      have h_imgD_sg : (imgD.arrow ≫ eqToHom e_deg) ≫ S.g = 0 := by
        rw [Category.assoc]
        have h_eqToHom_sg : eqToHom e_deg ≫ S.g =
            FC.d k ≫ eqToHom (congr_arg FC.A (show k - 1 = (k + 1 - 1) - 1 by omega)) := by
          suffices h : ∀ (n : ℤ) (hn : n = k),
              eqToHom (show FC.A k = FC.A n from congr_arg FC.A hn.symm) ≫ FC.d n =
              FC.d k ≫ eqToHom (show FC.A (k - 1) = FC.A (n - 1) from
                congr_arg FC.A (show k - 1 = n - 1 by omega)) by
            convert h (k + 1 - 1) (by omega) using 1
          intro n hn; subst hn; simp [eqToHom_refl, Category.id_comp, Category.comp_id]
        rw [h_eqToHom_sg, ← Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, zero_comp]
      -- Step G: S.liftCycles(imgD.arrow ≫ eqToHom) ≫ S.homologyπ = 0
      have h_imgD_homologyπ :
          S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg ≫ S.homologyπ = 0 := by
        rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
        rw [comp_zero, ← Category.assoc]
        have h_fti_lc : factorThruImageSubobject (FC.dToK k) ≫
            S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg = S.toCycles := by
          apply (cancel_mono S.iCycles).mp
          rw [Category.assoc, S.liftCycles_i, S.toCycles_i]
          rw [← Category.assoc, imageSubobject_arrow_comp]
          change FC.dToK k ≫ eqToHom e_deg = S.f
          simp only [FilteredComplex.dToK, S, Category.assoc, eqToHom_trans,
            eqToHom_refl, Category.comp_id]
        rw [h_fti_lc, S.toCycles_comp_homologyπ]
      -- Step H: liftCycles functoriality chain
      have h_comp_sg : (oI_lift ≫ φ_to_X2) ≫ S.g = 0 := by
        rw [Category.assoc]; exact h_lift ▸ comp_zero
      have h_IB_sg : (I_B.arrow ≫ eqToHom e_deg) ≫ S.g = 0 := by
        rw [h_comp_φ.symm]; exact h_comp_sg
      have h_lc_func : oI_lift ≫ S.liftCycles φ_to_X2 h_lift =
          S.liftCycles (oI_lift ≫ φ_to_X2) h_comp_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [Category.assoc, S.liftCycles_i, S.liftCycles_i]
      rw [h_lc_func]
      have h_lc_eq : S.liftCycles (oI_lift ≫ φ_to_X2) h_comp_sg =
          S.liftCycles (I_B.arrow ≫ eqToHom e_deg) h_IB_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, S.liftCycles_i, h_comp_φ]
      rw [h_lc_eq]
      have h_lc_factor : S.liftCycles (I_B.arrow ≫ eqToHom e_deg) h_IB_sg =
          Subobject.ofLE I_B imgD inf_le_left ≫
          S.liftCycles (imgD.arrow ≫ eqToHom e_deg) h_imgD_sg := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, Category.assoc, S.liftCycles_i, h_IB_factor]
      rw [h_lc_factor, Category.assoc, h_imgD_homologyπ, comp_zero]
    -- Step 3: Forward map E_∞ → gr^s H_k
    let fwd := cokernel.desc _ fwd_Z h_fwd_kills_B
    -- Step 4: Inverse map on F_s H_k
    -- We build inv_Fs : F_s.underlying → E_∞ (the LHS)
    -- by descending through the epi factorThruImageSubobject(gen_s) : I_s → F_s
    -- The LHS cokernel projection
    let πLHS := cokernel.π (Subobject.ofLE
      ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
      ((FC.toSSData bnd s k).B_le_Z ⊤))
    -- The epi from I_s to F_s H_k
    let e_Fs := factorThruImageSubobject gen_s
    -- The composed map I_s → E_∞
    -- We need: I_s → kerZ → Z_⊤ → E_∞
    -- The map I_s → Z_⊤ is: kerZ_to_Is ≫ e_Z
    -- (but kerZ_to_Is : kerZ → I_s, wrong direction!)
    -- Instead: we need the map I_s → kerZ, which requires eqToHom transport.
    -- Use: e_Z ≫ πLHS composed with the factorization through kerZ_to_Is
    -- Alternative: compose directly. We know kerZ_to_Is ≫ gen_s = φ_pre = h_func
    -- So kerZ_to_Is ≫ e_Fs ≫ ... But this still goes kerZ → I_s → F_s, not I_s → kerZ.
    -- The right approach: the map I_s → E_∞ goes through the arrow:
    -- I_s.arrow : I_s.underlying → A(k+1-1)
    -- Transport to A(k) via eqToHom⁻¹ to get an element in (fil s k) ∩ ker(d k)
    -- Then project to V and down to E_∞.
    -- This is complex, so we abstract it.
    -- Map: I_s → Z_⊤ using the factorization I_s → kerZ → Z_⊤
    -- For I_s → kerZ: since I_s is a subobject of A(k+1-1) in ker(S.g) ∩ fil s (k+1-1),
    -- and kerZ is a subobject of (fil s k).underlying in ker(d k),
    -- we need to transport and factor.
    -- For now, construct the inverse using the abstract approach:
    -- inv_Is : I_s → E_∞ will be defined, then descended through e_Fs.
    -- The map I_s → kerZ.underlying
    -- I_s.arrow = (ofLE I_s (ker S.g) inf_le_left ≫ (ker S.g).arrow) needs to go to kerZ
    -- via eqToHom transport. Factor through (fil s k).
    -- Since φ_to_X2 = kerZ.arrow ≫ (fil s k).arrow ≫ eqToHom e_deg
    -- and I_s.arrow has I_s ≤ fil s (k+1-1),
    -- the key is that kerZ_to_Is ≫ I_s.arrow = φ_to_X2
    -- = kerZ.arrow ≫ (fil s k).arrow ≫ eqToHom e_deg
    -- The inverse map I_s.underlying → E_∞:
    -- Use kerZ_to_Is in the reverse: we cannot directly invert it.
    -- Instead, build a different composition.
    -- Alternative cleaner approach: since kerZ_to_Is ≫ gen_s = φ_pre (h_func),
    -- we have kerZ_to_Is ≫ e_Fs = kerZ_to_Is ≫ factorThruImageSubobject gen_s
    -- And e_Z = factorThruImageSubobject (kerZ.arrow ≫ πV)
    -- Both are related via the commutative square.
    -- Let's build the inverse differently:
    -- inv_Is : I_s.underlying → E_∞ is defined below
    -- and then descended through the epi e_Fs.
    -- The inverse I_s → E_∞ goes through:
    -- I_s →[ofLE I_s (fil s (k+1-1)) inf_le_right] (fil s (k+1-1)).underlying
    -- →[eqToHom⁻¹] (fil s k).underlying →[needs: in ker(d k)] kerZ.underlying
    -- →[kerZ.arrow] (fil s k).underlying →[πV] V →[into Z_⊤]
    -- But this is circular (we go to fil s k then back).
    -- Actually simpler: define inv_Is using factorThruKernelSubobject:
    -- From I_s we get an element of A(k+1-1) that's in ker(S.g) ∩ fil s (k+1-1).
    -- This element is in ker(S.g) means S.g(x) = 0, i.e., d(k+1-1)(x) = 0.
    -- Transport: eqToHom(e_deg)⁻¹(x) ∈ A(k), and d(k)(eqToHom⁻¹(x)) = 0 (up to transport).
    -- Also eqToHom⁻¹(x) ∈ fil s k. So eqToHom⁻¹ factors through (fil s k).arrow.
    -- The factored element y satisfies (fil s k).arrow(y) ≫ d k = 0, so y ∈ kerZ.
    -- Let's define the transport map:
    let e_deg_inv : FC.A (k + 1 - 1) = FC.A k :=
      congr_arg FC.A (show k + 1 - 1 = k by omega)
    -- I_s.arrow ≫ eqToHom(e_deg_inv) : I_s.underlying → A(k)
    -- This factors through (fil s k).arrow because
    -- I_s ≤ fil s (k+1-1) and eqToHom transports fil.
    -- Then it's in ker(d k) because I_s ≤ ker(S.g) and S.g ≈ d(k+1-1) which transports to d(k).
    -- Construct map I_s → (fil s k).underlying
    have h_Is_to_fil : (FC.fil s k).Factors (I_s.arrow ≫ eqToHom e_deg_inv) := by
      -- I_s ≤ fil s (k+1-1), and eqToHom transports fil s (k+1-1) to fil s k
      have h_le : I_s ≤ FC.fil s (k + 1 - 1) := inf_le_right
      have h_arrow : I_s.arrow = Subobject.ofLE I_s (FC.fil s (k + 1 - 1)) h_le ≫
          (FC.fil s (k + 1 - 1)).arrow := (Subobject.ofLE_arrow h_le).symm
      rw [h_arrow, Category.assoc]
      -- Now need: (fil s (k+1-1)).arrow ≫ eqToHom e_deg_inv = eqToHom(...) ≫ (fil s k).arrow
      have h_transport2 : (FC.fil s (k + 1 - 1)).arrow ≫ eqToHom e_deg_inv =
          eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j))
            (show k + 1 - 1 = k by omega)) ≫ (FC.fil s k).arrow := by
        have : ∀ (a b : ℤ) (h : a = b),
            (FC.fil s a).arrow ≫ eqToHom (congr_arg FC.A h) =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil s j)) h) ≫
            (FC.fil s b).arrow := by
          intro a b h; subst h; simp
        exact this (k + 1 - 1) k (by omega)
      rw [h_transport2, ← Category.assoc]
      exact Subobject.factors_comp_arrow _
    let Is_to_fil := Subobject.factorThru (FC.fil s k) (I_s.arrow ≫ eqToHom e_deg_inv) h_Is_to_fil
    have h_Is_to_fil_eq : Is_to_fil ≫ (FC.fil s k).arrow = I_s.arrow ≫ eqToHom e_deg_inv :=
      Subobject.factorThru_arrow _ _ _
    -- Show Is_to_fil ∈ ker(f_Z)
    have h_Is_in_kerZ : Is_to_fil ≫ f_Z = 0 := by
      change Is_to_fil ≫ ((FC.fil s k).arrow ≫ FC.d k) = 0
      rw [← Category.assoc,
        show (Is_to_fil ≫ (FC.fil s k).arrow) =
          I_s.arrow ≫ eqToHom e_deg_inv
        from h_Is_to_fil_eq, Category.assoc]
      -- Need: eqToHom e_deg_inv ≫ d k = S.g ≫ eqToHom(...)
      -- Since S.g = d(k+1-1) and e_deg_inv : A(k+1-1) = A(k),
      -- eqToHom(e_deg_inv) ≫ d k = d(k+1-1) ≫ eqToHom(...) (up to degree transport)
      -- But actually: S.g = d(k+1-1) with source A(k+1-1) and target A((k+1-1)-1).
      -- d k has source A(k) and target A(k-1).
      -- eqToHom e_deg_inv : A(k+1-1) ⟶ A(k). So eqToHom ≫ d k : A(k+1-1) → A(k-1).
      -- S.g = d(k+1-1) : A(k+1-1) → A((k+1-1)-1) = A(k-1-1+1) ... this needs care.
      -- Actually S = ShortComplex.mk (d(k+1)) (d(k+1-1)) _, so S.g = d(k+1-1).
      -- S.g : S.X₂ → S.X₃ where S.X₂ = A(k+1-1), S.X₃ = A((k+1-1)-1).
      -- Now d k : A(k) → A(k-1) and (k+1-1)-1 = k-1, so S.X₃ = A(k-1).
      -- eqToHom(e_deg_inv) : A(k+1-1) → A(k). So eqToHom ≫ d k : A(k+1-1) → A(k-1).
      -- S.g = d(k+1-1) : A(k+1-1) → A((k+1-1)-1). Now (k+1-1)-1 = k-1 (by omega).
      -- So eqToHom ≫ d k and S.g both go A(k+1-1) → A(k-1) (up to eqToHom on target).
      -- More precisely: eqToHom(e_deg_inv) ≫ d k = S.g ≫ eqToHom(A((k+1-1)-1) = A(k-1)).
      -- So I_s.arrow ≫ eqToHom ≫ d k
      -- = I_s.arrow ≫ S.g ≫ eqToHom = 0 (since I_s ≤ ker S.g).
      have h_transport_d : eqToHom e_deg_inv ≫ FC.d k =
          S.g ≫ eqToHom (congr_arg FC.A (show (k + 1 - 1) - 1 = k - 1 by omega)) := by
        simp [S]
      rw [h_transport_d, ← Category.assoc]
      -- I_s.arrow ≫ S.g = 0 (since I_s ≤ ker S.g)
      have h_Is_ker : I_s.arrow ≫ S.g = 0 := h_zero_s
      rw [h_Is_ker, zero_comp]
    -- Factor Is_to_fil through kerZ
    let Is_to_kerZ := factorThruKernelSubobject f_Z Is_to_fil h_Is_in_kerZ
    -- Property: Is_to_kerZ ≫ kerZ.arrow = Is_to_fil
    have h_Is_to_kerZ : Is_to_kerZ ≫ kerZ.arrow = Is_to_fil :=
      factorThruKernelSubobject_comp_arrow _ _ _
    -- The composed map I_s → E_∞
    let inv_Is := Is_to_kerZ ≫ e_Z ≫ πLHS
    -- Descent condition for the inverse: kernel.ι(e_Fs) ≫ inv_Is = 0
    have h_desc_inv : kernel.ι e_Fs ≫ inv_Is = 0 := by
      -- ═══ Step 1: kernel.ι e_Fs ≫ gen_s = 0 ═══
      have h_ker_gen : kernel.ι e_Fs ≫ gen_s = 0 := by
        -- gen_s = e_Fs ≫ (imageSubobject gen_s).arrow, and kernel.ι e_Fs ≫ e_Fs = 0
        have h_assoc : kernel.ι e_Fs ≫ e_Fs ≫ (imageSubobject gen_s).arrow = 0 := by
          rw [kernel.condition_assoc, zero_comp]
        rwa [imageSubobject_arrow_comp] at h_assoc
      have h_lc_π : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫ S.homologyπ = 0 := by
        rw [Category.assoc]; exact h_ker_gen
      -- Step 2: kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom
      -- ≫ cokernel.π(dToK k) = 0
      have h_Sf_dToK : S.f ≫ eqToHom e_deg_inv = FC.dToK k := by
        simp only [FilteredComplex.dToK, S]
      have h_comp_cok_dToK : (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) ≫
          cokernel.π (FC.dToK k) = 0 := by
        -- Transfer h_lc_π to cokernel.π(S.toCycles)
        have h_φ_lHπ : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫
            S.leftHomologyπ = 0 := by
          have hπ_eq : S.homologyπ = S.leftHomologyπ ≫ S.leftHomologyIso.hom := by
            rw [← Category.comp_id S.homologyπ,
                ← Iso.inv_hom_id S.leftHomologyIso, ← Category.assoc,
                S.homologyπ_comp_leftHomologyIso_inv]
          rw [← cancel_mono S.leftHomologyIso.hom, Category.assoc, zero_comp, ← hπ_eq]
          exact h_lc_π
        have h_φ_cok_tC : (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) ≫
            cokernel.π S.toCycles = 0 := by
          let σ := IsColimit.coconePointUniqueUpToIso S.leftHomologyIsCokernel
              (cokernelIsCokernel S.toCycles)
          have : S.leftHomologyπ ≫ σ.hom = cokernel.π S.toCycles :=
            IsColimit.comp_coconePointUniqueUpToIso_hom S.leftHomologyIsCokernel
              (cokernelIsCokernel S.toCycles) WalkingParallelPair.one
          rw [← this, ← Category.assoc, h_φ_lHπ, zero_comp]
        -- Factor through kernel(cokernel.π S.toCycles) = Abelian.image(S.toCycles)
        let κ := kernel.lift (cokernel.π S.toCycles)
            (kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s) h_φ_cok_tC
        have hκ : κ ≫ kernel.ι (cokernel.π S.toCycles) =
            kernel.ι e_Fs ≫ S.liftCycles I_s.arrow h_zero_s := kernel.lift_ι _ _ _
        -- kernel.ι e_Fs ≫ I_s.arrow = κ ≫ kernel.ι(cokernel.π S.toCycles) ≫ S.iCycles
        have hκ_arrow : κ ≫ (kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles) =
            kernel.ι e_Fs ≫ I_s.arrow := by
          rw [← Category.assoc, hκ, Category.assoc, S.liftCycles_i]
        -- Abelian.factorThruImage ≫ kernel.ι(cokernel.π S.toCycles) = S.toCycles
        have h_img_fac : Abelian.factorThruImage S.toCycles ≫
            kernel.ι (cokernel.π S.toCycles) = S.toCycles := Abelian.image.fac S.toCycles
        -- kernel.ι(cokernel.π S.toCycles) ≫ S.iCycles ≫ eqToHom ≫ cokernel.π(dToK k) = 0
        have h_mid_zero : kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles ≫
            eqToHom e_deg_inv ≫ cokernel.π (FC.dToK k) = 0 := by
          rw [← cancel_epi (Abelian.factorThruImage S.toCycles), comp_zero]
          simp only [← Category.assoc]
          rw [h_img_fac, S.toCycles_i, h_Sf_dToK, cokernel.condition]
        -- Conclude
        -- Goal: (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv)
        -- ≫ cokernel.π (FC.dToK k) = 0
        -- Rewrite kernel.ι e_Fs ≫ I_s.arrow using hκ_arrow (left-associated)
        have h_sub : kernel.ι e_Fs ≫ I_s.arrow =
            κ ≫ (kernel.ι (cokernel.π S.toCycles) ≫ S.iCycles) := hκ_arrow.symm
        -- Left-associate everything so kernel.ι e_Fs ≫ I_s.arrow is a subterm
        simp only [← Category.assoc] at h_sub ⊢
        rw [h_sub]
        simp only [Category.assoc]
        rw [h_mid_zero, comp_zero]
      -- ═══ Step 3: Factor through imageSubobject(dToK k) ═══
      -- In abelian categories, imageSubobject f = kernelSubobject(cokernel.π f)
      -- So factoring through imageSubobject reduces to: comp with cokernel.π = 0
      have h_imgD_eq_kerCok : imageSubobject (FC.dToK k) =
          kernelSubobject (cokernel.π (FC.dToK k)) := by
        have hex := ShortComplex.exact_cokernel (FC.dToK k)
        rwa [ShortComplex.exact_iff_image_eq_kernel] at hex
      have h_in_imgD : (imageSubobject (FC.dToK k)).Factors
          (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [h_imgD_eq_kerCok, kernelSubobject_factors_iff]
        exact h_comp_cok_dToK
      -- ═══ Step 4: Also in fil s k (trivial) ═══
      have h_in_fil : (FC.fil s k).Factors
          (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [show kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv =
          (kernel.ι e_Fs ≫ Is_to_fil) ≫ (FC.fil s k).arrow from by
          rw [Category.assoc, h_Is_to_fil_eq]]
        exact Subobject.factors_comp_arrow _
      -- ═══ Step 5: Factor through I_B = imgD ⊓ fil s k ═══
      let imgD := imageSubobject (FC.dToK k)
      let I_B := imgD ⊓ FC.fil s k
      have h_in_IB : I_B.Factors (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) := by
        rw [show I_B = imgD ⊓ FC.fil s k from rfl, Subobject.inf_factors]
        exact ⟨h_in_imgD, h_in_fil⟩
      let ker_to_IB := I_B.factorThru (kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv) h_in_IB
      have h_ker_to_IB : ker_to_IB ≫ I_B.arrow =
          kernel.ι e_Fs ≫ I_s.arrow ≫ eqToHom e_deg_inv :=
        Subobject.factorThru_arrow _ _ _
      -- ═══ Step 6: Local oI and oI_lift ═══
      let oI := Subobject.ofLE I_B (FC.fil s k) inf_le_right
      have h_oI_zero : oI ≫ f_Z = 0 := by
        change Subobject.ofLE I_B (FC.fil s k) inf_le_right ≫
          (FC.fil s k).arrow ≫ FC.d k = 0
        rw [← Category.assoc, Subobject.ofLE_arrow]
        rw [show I_B.arrow = Subobject.ofLE I_B imgD inf_le_left ≫ imgD.arrow
          from (Subobject.ofLE_arrow inf_le_left).symm, Category.assoc]
        have : imgD.arrow ≫ FC.d k = 0 := by
          rw [← cancel_epi (factorThruImageSubobject (FC.dToK k))]
          rw [comp_zero, ← Category.assoc, imageSubobject_arrow_comp]
          exact FC.dToK_comp_d k
        rw [this, comp_zero]
      let oI_lift := factorThruKernelSubobject f_Z oI h_oI_zero
      have h_oI_lift : oI_lift ≫ kerZ.arrow = oI :=
        factorThruKernelSubobject_comp_arrow f_Z oI h_oI_zero
      -- ═══ Step 7: kernel.ι e_Fs ≫ Is_to_kerZ = ker_to_IB ≫ oI_lift ═══
      have h_factor_kerZ : kernel.ι e_Fs ≫ Is_to_kerZ = ker_to_IB ≫ oI_lift := by
        apply (cancel_mono kerZ.arrow).mp
        simp only [Category.assoc]
        rw [h_oI_lift, h_Is_to_kerZ]
        apply (cancel_mono (FC.fil s k).arrow).mp
        simp only [Category.assoc]
        rw [Subobject.ofLE_arrow, h_ker_to_IB, h_Is_to_fil_eq]
      -- ═══ Step 8: oI_lift ≫ e_Z ≫ πLHS = 0 ═══
      have h_fti_ofLE : factorThruImageSubobject (oI ≫ πV) ≫
          Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
          ((FC.toSSData bnd s k).B_le_Z ⊤) = oI_lift ≫ e_Z := by
        apply (cancel_mono ((FC.toSSData bnd s k).Z ⊤).arrow).mp
        rw [Category.assoc, Subobject.ofLE_arrow]
        change factorThruImageSubobject (oI ≫ πV) ≫
          ((FC.toSSData bnd s k).B ⊤).arrow = (oI_lift ≫ e_Z) ≫ _
        rw [show ((FC.toSSData bnd s k).B ⊤).arrow =
            (imageSubobject (oI ≫ πV)).arrow from rfl]
        rw [imageSubobject_arrow_comp, Category.assoc]
        rw [show e_Z ≫ ((FC.toSSData bnd s k).Z ⊤).arrow =
          kerZ.arrow ≫ πV from imageSubobject_arrow_comp (kerZ.arrow ≫ πV)]
        rw [← Category.assoc, h_oI_lift]
      have h_oI_kill : oI_lift ≫ e_Z ≫ πLHS = 0 := by
        rw [← Category.assoc, ← h_fti_ofLE, Category.assoc]
        rw [show Subobject.ofLE ((FC.toSSData bnd s k).B ⊤) ((FC.toSSData bnd s k).Z ⊤)
            ((FC.toSSData bnd s k).B_le_Z ⊤) ≫ πLHS = 0 from cokernel.condition _]
        rw [comp_zero]
      -- ═══ Step 9: Conclude ═══
      change kernel.ι e_Fs ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = 0
      rw [← Category.assoc, ← Category.assoc, h_factor_kerZ,
          Category.assoc, Category.assoc, h_oI_kill, comp_zero]
    -- Descended map on F_s H_k
    let inv_Fs := Abelian.epiDesc e_Fs inv_Is h_desc_inv
    have h_inv_Fs : e_Fs ≫ inv_Fs = inv_Is := Abelian.comp_epiDesc _ _ _
    -- Show inv_Fs kills F_{s+1} H_k
    have h_inv_kills_Fs1 : Subobject.ofLE
        (FC.homologyFiltration.F (s + 1) k)
        (FC.homologyFiltration.F s k)
        (FC.homologyFiltration.mono s k) ≫ inv_Fs = 0 := by
      -- Setup: redefine I_s1, gen_s1 (these were local to h_desc_fwd's scope)
      set I_s1 := kernelSubobject S.g ⊓ FC.fil (s + 1) (k + 1 - 1)
      have h_zero_s1 : I_s1.arrow ≫ S.g = 0 := by
        rw [show I_s1.arrow = Subobject.ofLE I_s1 (kernelSubobject S.g)
            inf_le_left ≫ (kernelSubobject S.g).arrow
          from (Subobject.ofLE_arrow inf_le_left).symm,
          Category.assoc, kernelSubobject_arrow_comp, comp_zero]
      set gen_s1 := S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ
      -- The inclusion I_s1 ≤ I_s
      have hle : I_s1 ≤ I_s := inf_le_inf_left _ (FC.fil_anti s (k + 1 - 1))
      -- Key factorization: gen_s1 = ofLE(I_s1, I_s) ≫ gen_s
      have hlift_s : S.liftCycles I_s1.arrow h_zero_s1 =
          Subobject.ofLE I_s1 I_s hle ≫ S.liftCycles I_s.arrow h_zero_s := by
        apply (cancel_mono S.iCycles).mp
        rw [S.liftCycles_i, Category.assoc, S.liftCycles_i]
        exact (Subobject.ofLE_arrow hle).symm
      have h_gen_factor : gen_s1 =
          Subobject.ofLE I_s1 I_s hle ≫ gen_s := by
        change S.liftCycles I_s1.arrow h_zero_s1 ≫ S.homologyπ =
          Subobject.ofLE I_s1 I_s hle ≫ (S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ)
        rw [← Category.assoc, hlift_s]
      -- Step 1: reduce via zero_of_epi_comp with factorThruImageSubobject gen_s1
      apply zero_of_epi_comp (factorThruImageSubobject gen_s1)
      -- Goal: factorThruImageSubobject gen_s1 ≫ ofLE(F_{s+1}, F_s) ≫ inv_Fs = 0
      -- Step 2: relate fTI gen_s1 ≫ ofLE(F_{s+1}, F_s) to ofLE(I_s1, I_s) ≫ fTI gen_s
      have h_fTI_ofLE : factorThruImageSubobject gen_s1 ≫
          Subobject.ofLE (FC.homologyFiltration.F (s + 1) k)
            (FC.homologyFiltration.F s k) (FC.homologyFiltration.mono s k) =
          Subobject.ofLE I_s1 I_s hle ≫ factorThruImageSubobject gen_s := by
        -- Both sides are morphisms I_s1.underlying → (F_s).underlying
        -- (F_s).arrow is mono, cancel it
        apply (cancel_mono (FC.homologyFiltration.F s k).arrow).mp
        -- LHS: fTI gen_s1 ≫ ofLE(F_{s+1}, F_s) ≫ (F_s).arrow
        --     = fTI gen_s1 ≫ (F_{s+1}).arrow  (by ofLE_arrow)
        --     = gen_s1                          (by imageSubobject_arrow_comp)
        rw [Category.assoc, Subobject.ofLE_arrow (FC.homologyFiltration.mono s k)]
        change factorThruImageSubobject gen_s1 ≫ (imageSubobject gen_s1).arrow =
          (Subobject.ofLE I_s1 I_s hle ≫ factorThruImageSubobject gen_s) ≫
            (imageSubobject gen_s).arrow
        rw [imageSubobject_arrow_comp, Category.assoc, imageSubobject_arrow_comp]
        exact h_gen_factor
      -- Step 3: substitute and rewrite
      -- Goal: fTI gen_s1 ≫ ofLE(F_{s+1}, F_s) ≫ inv_Fs = 0
      -- Reassociate to (fTI gen_s1 ≫ ofLE(F_{s+1}, F_s)) ≫ inv_Fs
      rw [← Category.assoc, h_fTI_ofLE, Category.assoc]
      -- Goal: ofLE(I_s1, I_s) ≫ (factorThruImageSubobject gen_s ≫ inv_Fs) = 0
      -- factorThruImageSubobject gen_s = e_Fs
      change Subobject.ofLE I_s1 I_s hle ≫ (e_Fs ≫ inv_Fs) = 0
      rw [h_inv_Fs]
      -- Goal: ofLE(I_s1, I_s) ≫ inv_Is = 0
      -- inv_Is = Is_to_kerZ ≫ e_Z ≫ πLHS
      change Subobject.ofLE I_s1 I_s hle ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = 0
      rw [← Category.assoc, ← Category.assoc]
      -- Suffices: (ofLE(I_s1, I_s) ≫ Is_to_kerZ) ≫ e_Z = 0
      suffices h_zero : (Subobject.ofLE I_s1 I_s hle ≫ Is_to_kerZ) ≫ e_Z = 0 by
        rw [h_zero, zero_comp]
      -- Cancel mono: (imageSubobject (kerZ.arrow ≫ πV)).arrow is mono
      apply (cancel_mono (imageSubobject (kerZ.arrow ≫ πV)).arrow).mp
      rw [Category.assoc, imageSubobject_arrow_comp, zero_comp]
      -- Goal: (ofLE(I_s1, I_s) ≫ Is_to_kerZ) ≫ kerZ.arrow ≫ πV = 0
      -- Reassociate: ((ofLE ≫ Is_to_kerZ) ≫ kerZ.arrow) ≫ πV = 0
      simp only [Category.assoc]
      -- Now: ofLE ≫ (Is_to_kerZ ≫ (kerZ.arrow ≫ πV)) = 0
      -- Rewrite Is_to_kerZ ≫ kerZ.arrow = Is_to_fil (need left-association)
      conv_lhs => rw [← Category.assoc Is_to_kerZ kerZ.arrow πV,
                       h_Is_to_kerZ]
      -- Goal: ofLE(I_s1, I_s) ≫ (Is_to_fil ≫ πV) = 0
      -- Show ofLE(I_s1, I_s) ≫ Is_to_fil factors through ι_fil
      -- First, show I_s1.arrow ≫ eqToHom e_deg_inv factors through (fil(s+1,k)).arrow
      have h_I_s1_factors : (FC.fil (s + 1) k).Factors (I_s1.arrow ≫ eqToHom e_deg_inv) := by
        have h_le_s1 : I_s1 ≤ FC.fil (s + 1) (k + 1 - 1) := inf_le_right
        have h_arrow_s1 : I_s1.arrow = Subobject.ofLE I_s1 (FC.fil (s + 1) (k + 1 - 1)) h_le_s1 ≫
            (FC.fil (s + 1) (k + 1 - 1)).arrow := (Subobject.ofLE_arrow h_le_s1).symm
        rw [h_arrow_s1, Category.assoc]
        have h_transport_s1 : (FC.fil (s + 1) (k + 1 - 1)).arrow ≫ eqToHom e_deg_inv =
            eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j))
              (show k + 1 - 1 = k by omega)) ≫ (FC.fil (s + 1) k).arrow := by
          have : ∀ (a b : ℤ) (h : a = b),
              (FC.fil (s + 1) a).arrow ≫ eqToHom (congr_arg FC.A h) =
              eqToHom (congr_arg (fun j => Subobject.underlying.obj (FC.fil (s + 1) j)) h) ≫
              (FC.fil (s + 1) b).arrow := by
            intro a b h; subst h; simp
          exact this (k + 1 - 1) k (by omega)
        rw [h_transport_s1, ← Category.assoc]
        exact Subobject.factors_comp_arrow _
      -- Factor: I_s1.arrow ≫ eqToHom e_deg_inv = lift_s1' ≫ (fil(s+1,k)).arrow
      let lift_s1' := Subobject.factorThru (FC.fil (s + 1) k) (I_s1.arrow ≫ eqToHom e_deg_inv)
          h_I_s1_factors
      have h_lift_s1' : lift_s1' ≫ (FC.fil (s + 1) k).arrow =
          I_s1.arrow ≫ eqToHom e_deg_inv :=
        Subobject.factorThru_arrow _ _ _
      -- Show: ofLE(I_s1, I_s) ≫ Is_to_fil = lift_s1' ≫ ι_fil
      have h_ofLE_Is_to_fil :
          Subobject.ofLE I_s1 I_s hle ≫ Is_to_fil = lift_s1' ≫ ι_fil := by
        apply (cancel_mono (FC.fil s k).arrow).mp
        rw [Category.assoc, h_Is_to_fil_eq]
        rw [← Category.assoc, Subobject.ofLE_arrow hle]
        rw [Category.assoc,
          show ι_fil ≫ (FC.fil s k).arrow = (FC.fil (s + 1) k).arrow
            from Subobject.ofLE_arrow (FC.fil_anti s k)]
        exact h_lift_s1'.symm
      rw [← Category.assoc, h_ofLE_Is_to_fil, Category.assoc]
      -- Goal: lift_s1' ≫ (ι_fil ≫ πV) = 0
      rw [show ι_fil ≫ πV = 0 from cokernel.condition ι_fil, comp_zero]
    -- Inverse map gr^s H_k → E_∞
    let inv := cokernel.desc _ inv_Fs h_inv_kills_Fs1
    -- Round-trip identities
    have h_hom_inv : fwd ≫ inv = 𝟙 _ := by
      -- Goal: fwd ≫ inv = 𝟙 (cokernel (ofLE(B_⊤, Z_⊤)))
      -- fwd = cokernel.desc _ fwd_Z h_fwd_kills_B
      -- inv = cokernel.desc _ inv_Fs h_inv_kills_Fs1
      -- πLHS = cokernel.π (ofLE(B_⊤, Z_⊤))
      -- Strategy: cancel_epi πLHS, then cancel_epi e_Z, then algebraic manipulations.
      -- Step 1: It suffices to show πLHS ≫ (fwd ≫ inv) = πLHS (cancel_epi πLHS)
      apply (cancel_epi πLHS).mp
      rw [Category.comp_id]
      -- Now: πLHS ≫ (fwd ≫ inv) = πLHS
      -- πLHS ≫ fwd = fwd_Z by cokernel.π_desc
      have h_πLHS_fwd : πLHS ≫ fwd = fwd_Z := cokernel.π_desc _ _ _
      rw [← Category.assoc, h_πLHS_fwd]
      -- Now: fwd_Z ≫ inv = πLHS
      -- Step 2: cancel_epi e_Z (e_Z is epi as factorThruImageSubobject)
      apply (cancel_epi e_Z).mp
      -- Now: e_Z ≫ (fwd_Z ≫ inv) = e_Z ≫ πLHS
      rw [← Category.assoc, h_fwd_Z]
      -- Now: fwd_kerZ ≫ inv = e_Z ≫ πLHS
      -- fwd_kerZ = φ_to_Fs ≫ πRHS
      change (φ_to_Fs ≫ πRHS) ≫ inv = e_Z ≫ πLHS
      rw [Category.assoc]
      -- πRHS ≫ inv = cokernel.π _ ≫ cokernel.desc _ inv_Fs _ = inv_Fs
      have h_πRHS_inv : πRHS ≫ inv = inv_Fs := cokernel.π_desc _ _ _
      rw [h_πRHS_inv]
      -- Now: φ_to_Fs ≫ inv_Fs = e_Z ≫ πLHS
      -- Step 3: show kerZ_to_Is ≫ e_Fs = φ_to_Fs (via cancel_mono)
      have h_compat : kerZ_to_Is ≫ e_Fs = φ_to_Fs := by
        apply (cancel_mono (imageSubobject gen_s).arrow).mp
        rw [Category.assoc, imageSubobject_arrow_comp]
        -- LHS: kerZ_to_Is ≫ gen_s = φ_pre (by h_func)
        rw [h_func, h_φ_to_Fs]
      -- Step 4: φ_to_Fs ≫ inv_Fs = kerZ_to_Is ≫ e_Fs ≫ inv_Fs
      rw [← h_compat, Category.assoc, h_inv_Fs]
      -- Now: kerZ_to_Is ≫ inv_Is = e_Z ≫ πLHS
      -- inv_Is = Is_to_kerZ ≫ e_Z ≫ πLHS
      change kerZ_to_Is ≫ (Is_to_kerZ ≫ e_Z ≫ πLHS) = e_Z ≫ πLHS
      -- Step 5: show kerZ_to_Is ≫ Is_to_kerZ = 𝟙
      have h_round : kerZ_to_Is ≫ Is_to_kerZ = 𝟙 _ := by
        -- Use cancel_mono kerZ.arrow
        apply (cancel_mono kerZ.arrow).mp
        rw [Category.id_comp, Category.assoc, h_Is_to_kerZ]
        -- Now: kerZ_to_Is ≫ Is_to_fil = kerZ.arrow
        -- Use cancel_mono (FC.fil s k).arrow
        apply (cancel_mono (FC.fil s k).arrow).mp
        rw [Category.assoc, h_Is_to_fil_eq]
        -- Now: kerZ_to_Is ≫ I_s.arrow ≫ eqToHom e_deg_inv = kerZ.arrow ≫ (FC.fil s k).arrow
        rw [← Category.assoc, h_kerZ_to_Is]
        -- Now: φ_to_X2 ≫ eqToHom e_deg_inv = kerZ.arrow ≫ (FC.fil s k).arrow
        -- φ_to_X2 = kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg
        change (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) ≫ eqToHom e_deg_inv =
          kerZ.arrow ≫ (FC.fil s k).arrow
        rw [Category.assoc, Category.assoc]
        congr 1
        -- eqToHom e_deg ≫ eqToHom e_deg_inv = 𝟙
        simp [eqToHom_trans]
      rw [← Category.assoc, ← Category.assoc, h_round, Category.id_comp]
    have h_inv_hom : inv ≫ fwd = 𝟙 _ := by
      -- Goal: inv ≫ fwd = 𝟙 (cokernel (ofLE(F_{s+1}, F_s)))
      -- Strategy: cancel_epi πRHS, then cancel_epi e_Fs, then algebraic manipulations.
      -- Step 1: cancel_epi πRHS
      apply (cancel_epi πRHS).mp
      rw [Category.comp_id, ← Category.assoc]
      -- Goal: (πRHS ≫ inv) ≫ fwd = πRHS
      have h_πRHS_inv' : πRHS ≫ inv = inv_Fs := cokernel.π_desc _ _ _
      rw [h_πRHS_inv']
      -- Now: inv_Fs ≫ fwd = πRHS
      -- Step 2: cancel_epi e_Fs
      apply (cancel_epi e_Fs).mp
      rw [← Category.assoc, h_inv_Fs]
      -- Now: inv_Is ≫ fwd = e_Fs ≫ πRHS
      -- inv_Is = Is_to_kerZ ≫ e_Z ≫ πLHS
      change (Is_to_kerZ ≫ e_Z ≫ πLHS) ≫ fwd = e_Fs ≫ πRHS
      rw [Category.assoc, Category.assoc]
      have h_πLHS_fwd' : πLHS ≫ fwd = fwd_Z := cokernel.π_desc _ _ _
      rw [h_πLHS_fwd', h_fwd_Z]
      -- Now: Is_to_kerZ ≫ (φ_to_Fs ≫ πRHS) = e_Fs ≫ πRHS
      change Is_to_kerZ ≫ (φ_to_Fs ≫ πRHS) = e_Fs ≫ πRHS
      rw [← Category.assoc]
      -- Now: (Is_to_kerZ ≫ φ_to_Fs) ≫ πRHS = e_Fs ≫ πRHS
      congr 1
      -- Step 3: show Is_to_kerZ ≫ φ_to_Fs = e_Fs
      apply (cancel_mono (imageSubobject gen_s).arrow).mp
      rw [Category.assoc, h_φ_to_Fs, imageSubobject_arrow_comp]
      -- Now: Is_to_kerZ ≫ φ_pre = gen_s
      change Is_to_kerZ ≫ (S.liftCycles φ_to_X2 h_lift ≫ S.homologyπ) =
        S.liftCycles I_s.arrow h_zero_s ≫ S.homologyπ
      rw [← Category.assoc]
      congr 1
      apply (cancel_mono S.iCycles).mp
      rw [Category.assoc, S.liftCycles_i, S.liftCycles_i]
      -- Now: Is_to_kerZ ≫ φ_to_X2 = I_s.arrow
      change Is_to_kerZ ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) = I_s.arrow
      rw [show Is_to_kerZ ≫ (kerZ.arrow ≫ (FC.fil s k).arrow ≫ eqToHom e_deg) =
          (Is_to_kerZ ≫ kerZ.arrow) ≫ (FC.fil s k).arrow ≫ eqToHom e_deg by
        simp only [Category.assoc]]
      rw [h_Is_to_kerZ, show Is_to_fil ≫ (FC.fil s k).arrow ≫ eqToHom e_deg =
          (Is_to_fil ≫ (FC.fil s k).arrow) ≫ eqToHom e_deg by rw [Category.assoc]]
      rw [h_Is_to_fil_eq, Category.assoc]
      -- Now: I_s.arrow ≫ eqToHom e_deg_inv ≫ eqToHom e_deg = I_s.arrow
      simp [eqToHom_trans]
    exact ⟨fwd, inv, h_hom_inv, h_inv_hom⟩
end KIP.SpectralSequence
