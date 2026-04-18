/-
  KIP.StableHomotopy.Basic
  §2.2 Stable homotopy theory — the stable homotopy category 𝒮,
  sphere spectrum 𝕊, Sⁿ = Σⁿ𝕊, πₙX = [Sⁿ, X], π_*X as singly-graded
  abelian group, smash product, mapping spectra, long exact sequence.

  Round 3 refactor: LES axioms replaced by theorems derived from
  Mathlib's triangulated category library (coyoneda_exact₂/₃).
-/
import Mathlib
import KIP.StableHomotopy.TensorTriangulatedCategory
open CategoryTheory MonoidalCategory Pretriangulated

namespace KIP.StableHomotopy

universe u v

/-! ## The Stable Homotopy Category

We axiomatize a stable homotopy category as a pretriangulated category with ℤ-shift,
equipped with a symmetric monoidal structure (smash product) and a distinguished
sphere spectrum object.

**Remark.** `StableHomotopyCategory` refers to the homotopy category of spectra.
We axiomatize it directly as a triangulated category rather than constructing it
via a stable model category.
-/

/-- The stable homotopy category — the homotopy category of spectra, axiomatized
as a pretriangulated category with symmetric monoidal structure (smash product)
and a sphere spectrum. -/
class StableHomotopyCategory (𝒮 : Type u) extends
    Category.{v} 𝒮,
    Preadditive 𝒮,
    HasShift 𝒮 ℤ,
    MonoidalCategory 𝒮 where
  /-- Every shift functor is additive. -/
  shiftAdditive : ∀ (n : ℤ), (shiftFunctor 𝒮 n).Additive
  /-- The category has a zero object. -/
  hasZeroObject : Limits.HasZeroObject 𝒮
  /-- The category is pretriangulated. -/
  pretriangulated : Pretriangulated 𝒮

attribute [instance] StableHomotopyCategory.shiftAdditive
attribute [instance] StableHomotopyCategory.hasZeroObject
attribute [instance] StableHomotopyCategory.pretriangulated

variable {𝒮 : Type u} [StableHomotopyCategory.{u, v} 𝒮]

/-- The stable homotopy category is a closed symmetric tensor triangulated category
    (HPS Definition A.2.1). This provides SymmetricCategory and MonoidalClosed instances. -/
axiom sh_closedSymmetricTT : ClosedSymmetricTensorTriangulated 𝒮
noncomputable instance : ClosedSymmetricTensorTriangulated 𝒮 := sh_closedSymmetricTT

/-- The stable homotopy category has functorial cofiber compatible with
    the tensor structure. -/
axiom sh_tensor_functorial_cofiber : TensorTriangulatedCatWithFunctorialCofiber 𝒮
noncomputable instance : TensorTriangulatedCatWithFunctorialCofiber 𝒮 :=
  sh_tensor_functorial_cofiber

/-! ## Sphere Spectrum and Spheres -/

/-- The sphere spectrum 𝕊 in a stable homotopy category, defined as the
monoidal unit. -/
abbrev SphereSpectrum : 𝒮 := 𝟙_ 𝒮

/-- BHS §0.2, Definition 0.30: The sphere spectrum 𝕊 is the unit of the
symmetric monoidal (smash product) structure on the stable homotopy category. -/
theorem sphere_is_monoidal_unit :
    (SphereSpectrum : 𝒮) = 𝟙_ 𝒮 := rfl

/-- The n-sphere Sⁿ = Σⁿ𝕊, defined as the n-fold shift of the sphere spectrum. -/
abbrev Sphere (n : ℤ) : 𝒮 := (shiftFunctor 𝒮 n).obj SphereSpectrum

/-! ## Homotopy Groups

Homotopy groups πₙ(X) = [Sⁿ, X] are defined as Hom-sets in the
pretriangulated category. The Preadditive structure on 𝒮 gives these
their abelian group structure.
-/

/-- The n-th homotopy group of a spectrum X, defined as Hom(Sⁿ, X).
Using `abbrev` so that typeclass inference can see through to
the Preadditive-provided AddCommGroup on Hom-sets. -/
abbrev HomotopyGroup (n : ℤ) (X : 𝒮) : Type v :=
  Sphere n ⟶ X

/-- The graded homotopy groups π_*(X), as a function ℤ → AddCommGrpCat. -/
noncomputable def HomotopyGroups (X : 𝒮) : ℤ → AddCommGrpCat.{v} :=
  fun n => AddCommGrpCat.mk (HomotopyGroup n X)

/-! ## Smash Product of Spheres -/

/-- BHS §0.2, Definition 0.30 (smash product): The smash product of spheres
satisfies S^m ⊗ S^n ≅ S^{m+n}, reflecting the compatibility of the monoidal
structure with the shift functor. This requires monoidal-shift compatibility
not axiomatized in Mathlib's pretriangulated library. -/
axiom smashSpheres_iso (m n : ℤ) :
    (Sphere m : 𝒮) ⊗ (Sphere n : 𝒮) ≅ Sphere (m + n)

/-- The smash product of spheres: Sᵐ ⊗ Sⁿ ≅ Sᵐ⁺ⁿ. -/
noncomputable def smashSpheres (m n : ℤ) :
    (Sphere m : 𝒮) ⊗ (Sphere n : 𝒮) ≅ Sphere (m + n) where
  hom := (smashSpheres_iso m n).hom
  inv := (smashSpheres_iso m n).inv
  hom_inv_id := (smashSpheres_iso m n).hom_inv_id
  inv_hom_id := (smashSpheres_iso m n).inv_hom_id

/-- Graded commutativity: the twist on spheres satisfies T = (-1)^{rs}.
Moved from TensorTriangulatedCategory for use in SH/Basic. -/
axiom sphereTwistSign (r s : ℤ) :
    (β_ (Sphere r : 𝒮) (Sphere s)).hom ≫ (smashSpheres s r).hom ≫
      eqToHom (by ring_nf) =
    (if Even (r * s) then (smashSpheres r s).hom
     else -(smashSpheres r s).hom)

/-! ## Mapping Spectrum -/

/-- Tensoring with a sphere implements the shift: Sⁿ ⊗ X ≅ Σⁿ X.
Axiomatized because the formal proof from iterated smashSuspIso and
unitors is too complex. -/
axiom sphere_tensor_shift (n : ℤ) (X : 𝒮) :
    (Sphere n : 𝒮) ⊗ X ≅ (shiftFunctor 𝒮 n).obj X

/-- BHS §0.2, Definition 0.31 (mapping spectra): The mapping spectrum (internal
hom / function spectrum) F(X, Y), right adjoint to the smash product:
[A ⊗ X, Y] ≅ [A, F(X, Y)]. Defined via the internal hom from MonoidalClosed. -/
noncomputable def MappingSpectrum (X Y : 𝒮) : 𝒮 := (ihom X).obj Y

/-- BHS §0.2, Definition 0.31: The mapping spectrum represents morphisms:
πₙ F(X, Y) ≅ [Σⁿ X, Y].

Proof sketch: πₙ F(X,Y) = Hom(Sⁿ, (ihom X).obj Y)
  ≅ Hom(X ⊗ Sⁿ, Y)    -- by (ihom.adjunction X).homEquiv.symm
  ≅ Hom(Sⁿ ⊗ X, Y)    -- by braiding β_ X (Sphere n)
  ≅ Hom(Σⁿ X, Y)        -- by sphere_tensor_shift n X -/
noncomputable def mappingSpectrumHomotopy (n : ℤ) (X Y : 𝒮) :
    HomotopyGroup n (MappingSpectrum X Y) ≃ ((shiftFunctor 𝒮 n).obj X ⟶ Y) :=
  ((ihom.adjunction X).homEquiv (Sphere n) Y).symm |>.trans
    (Iso.homCongr ((β_ X (Sphere n)).trans (sphere_tensor_shift n X)) (Iso.refl Y))

/-! ## Distinguished Triangles and Long Exact Sequence

Given a distinguished triangle X → Y → Z → X⟦1⟧ in the pretriangulated
stable homotopy category, we get a long exact sequence on homotopy groups:
  ⋯ → πₙ(X) → πₙ(Y) → πₙ(Z) → πₙ₋₁(X) → ⋯
-/

/-- A distinguished triangle in the stable homotopy category, representing
a cofiber sequence X → Y → Z → X⟦1⟧. This wraps the Pretriangulated
distinguished triangle structure. -/
structure HoCofiberSequence where
  /-- The source object X -/
  X : 𝒮
  /-- The target object Y -/
  Y : 𝒮
  /-- The cofiber Z -/
  Z : 𝒮
  /-- The map f : X → Y -/
  f : X ⟶ Y
  /-- The inclusion g : Y → Z -/
  g : Y ⟶ Z
  /-- The connecting map h : Z → X⟦1⟧ -/
  h : Z ⟶ (shiftFunctor 𝒮 (1 : ℤ)).obj X
  /-- The triangle is distinguished. -/
  distinguished : Triangle.mk f g h ∈
    distinguishedTriangles

/-- Construct a cofiber sequence from a morphism using functorial cofiber. -/
def HoCofiberSequence.ofMorphism {X Y : 𝒮} (f : X ⟶ Y)
    [inst : HasFunctorialCofiber 𝒮] : HoCofiberSequence (𝒮 := 𝒮) where
  X := X; Y := Y; Z := HasFunctorialCofiber.cofib f
  f := f
  g := HasFunctorialCofiber.cofibι f
  h := HasFunctorialCofiber.cofibδ f
  distinguished := HasFunctorialCofiber.cofib_distinguished f

/-- The induced map on homotopy groups from a morphism of spectra:
π_n(f) : π_n(X) → π_n(Y) is given by postcomposition. -/
def inducedMap {X Y : 𝒮} (f : X ⟶ Y) (n : ℤ) :
    HomotopyGroup n X →+ HomotopyGroup n Y where
  toFun := fun α => α ≫ f
  map_zero' := Limits.zero_comp
  map_add' := fun a b => Preadditive.add_comp _ _ _ a b f

/-- Fixed proof that 1 + (-1) = 0 in ℤ, used for shift functor composition. -/
private theorem one_plus_neg_one : (1 : ℤ) + (-1) = 0 := by omega

/-- The connecting homomorphism in the long exact sequence:
∂ : πₙ(Z) → πₙ₋₁(X) arising from a distinguished triangle.

Defined as the composite: S^{n-1} →[shift iso] S^n⟦-1⟧ →[shift(-1)(α ≫ h)]
X⟦1⟧⟦-1⟧ →[shift comp iso] X. -/
noncomputable def connectingHomomorphism (T : HoCofiberSequence (𝒮 := 𝒮)) (n : ℤ) :
    HomotopyGroup n T.Z →+ HomotopyGroup (n - 1) T.X where
  toFun α :=
    (shiftFunctorAdd 𝒮 n (-1)).hom.app SphereSpectrum ≫
      (shiftFunctor 𝒮 (-1)).map (α ≫ T.h) ≫
        (shiftFunctorCompIsoId 𝒮 1 (-1) one_plus_neg_one).hom.app T.X
  map_zero' := by simp [Limits.zero_comp, Functor.map_zero]
  map_add' := by
    intro a b
    simp [Preadditive.add_comp, Functor.map_add, Preadditive.comp_add]

/-! ## Properties derived from the distinguished triangle -/

/-- The composition `f ≫ g = 0` in a cofiber sequence. -/
theorem HoCofiberSequence.fg_zero (T : HoCofiberSequence (𝒮 := 𝒮)) :
    T.f ≫ T.g = 0 :=
  comp_distTriang_mor_zero₁₂ _ T.distinguished

/-- The composition `g ≫ h = 0` in a cofiber sequence. -/
theorem HoCofiberSequence.gh_zero (T : HoCofiberSequence (𝒮 := 𝒮)) :
    T.g ≫ T.h = 0 :=
  comp_distTriang_mor_zero₂₃ _ T.distinguished

/-- The composition `h ≫ f⟦1⟧ = 0` in a cofiber sequence. -/
theorem HoCofiberSequence.hf_shift_zero (T : HoCofiberSequence (𝒮 := 𝒮)) :
    T.h ≫ (shiftFunctor 𝒮 (1 : ℤ)).map T.f = 0 :=
  comp_distTriang_mor_zero₃₁ _ T.distinguished

/-! ## Helper lemmas for shift functor manipulation -/

/-- Shift functors reflect zero morphisms (since they are equivalences). -/
private theorem shiftFunctor_map_eq_zero {X Y : 𝒮} {f : X ⟶ Y} {n : ℤ}
    (h : (shiftFunctor 𝒮 n).map f = 0) : f = 0 := by
  have inj := (shiftEquiv 𝒮 n).functor.map_injective (X := X) (Y := Y)
  apply inj
  change (shiftFunctor 𝒮 n).map f = (shiftFunctor 𝒮 n).map 0
  rw [h, (shiftFunctor 𝒮 n).map_zero]

/-- If the connecting homomorphism `iso₁ ≫ shift(-1)(z ≫ h) ≫ iso₂ = 0`,
    then `z ≫ h = 0`. The proof cancels the isomorphisms and uses
    faithfulness of the shift functor. -/
private theorem comp_h_zero_of_connectingHom_zero
    (T : HoCofiberSequence (𝒮 := 𝒮)) (n : ℤ) (z : HomotopyGroup n T.Z)
    (hz : connectingHomomorphism T n z = 0) : z ≫ T.h = 0 := by
  simp only [connectingHomomorphism, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hz
  set a := (shiftFunctorAdd 𝒮 n (-1)).hom.app SphereSpectrum
  set b := (shiftFunctorCompIsoId 𝒮 1 (-1) one_plus_neg_one).hom.app T.X
  set m := (shiftFunctor 𝒮 (-1)).map (z ≫ T.h)
  have ha : IsIso a := inferInstance
  have hb : IsIso b := inferInstance
  have hm : m = 0 := by
    have h1 : inv a ≫ (a ≫ m ≫ b) = 0 := by rw [hz]; simp
    rw [IsIso.inv_hom_id_assoc] at h1
    have h2 : (m ≫ b) ≫ inv b = 0 := by rw [h1]; simp
    rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h2
  exact shiftFunctor_map_eq_zero hm

/-- The connecting homomorphism composed with f is zero:
    ∂(z) ≫ f = 0 for all z. Uses naturality of the shift-composition
    iso and the triangle relation h ≫ f⟦1⟧ = 0. -/
private theorem connectingHom_comp_f_zero (T : HoCofiberSequence (𝒮 := 𝒮))
    (n : ℤ) (z : HomotopyGroup n T.Z) :
    connectingHomomorphism T n z ≫ T.f = 0 := by
  simp only [connectingHomomorphism, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Category.assoc]
  have nat := (shiftFunctorCompIsoId 𝒮 1 (-1) one_plus_neg_one).hom.naturality T.f
  simp only [Functor.id_map, Functor.comp_map] at nat
  rw [← nat, ← Category.assoc ((shiftFunctor 𝒮 (-1)).map (z ≫ T.h)) _ _,
      ← Functor.map_comp (shiftFunctor 𝒮 (-1)),
      Category.assoc, T.hf_shift_zero, Limits.comp_zero,
      Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

/-! ## Long Exact Sequence on Homotopy Groups

The three exactness theorems below replace the previous LES axioms.
They are proved using Mathlib's `coyoneda_exact₂/₃` from the
pretriangulated category library.
-/

/-- Long exact sequence on homotopy groups: exactness at Y.
For a distinguished triangle X →f Y →g Z →h X⟦1⟧:
  y ∈ ker(g_*) ↔ y ∈ im(f_*)

Proved via `coyoneda_exact₂`: any map into Y that composes to zero
with g factors through f. -/
theorem les_homotopy_exact_f (T : HoCofiberSequence (𝒮 := 𝒮)) (n : ℤ) :
    ∀ (y : HomotopyGroup n T.Y),
      (inducedMap T.g n) y = 0 ↔
        ∃ (x : HomotopyGroup n T.X), (inducedMap T.f n) x = y := by
  intro y
  simp only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ _ T.distinguished y hy
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    simp [Category.assoc, T.fg_zero]

/-- Long exact sequence on homotopy groups: exactness at Z.
  z ∈ ker(∂) ↔ z ∈ im(g_*)

Proved via `coyoneda_exact₃`: the connecting homomorphism vanishes
iff the map factors through g, using the iso-cancellation lemma
to relate ∂(z) = 0 to z ≫ h = 0. -/
theorem les_homotopy_exact_g (T : HoCofiberSequence (𝒮 := 𝒮)) (n : ℤ) :
    ∀ (z : HomotopyGroup n T.Z),
      (connectingHomomorphism T n) z = 0 ↔
        ∃ (y : HomotopyGroup n T.Y), (inducedMap T.g n) y = z := by
  intro z
  simp only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · intro hz
    have hz' : z ≫ T.h = 0 := comp_h_zero_of_connectingHom_zero T n z hz
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ _ T.distinguished z hz'
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    simp only [connectingHomomorphism, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Category.assoc, T.gh_zero, Limits.comp_zero, Functor.map_zero,
      Limits.zero_comp]

/-- Long exact sequence on homotopy groups: exactness at X (shifted).
  x ∈ ker(f_*) ↔ x ∈ im(∂)

The backward direction (im ⊆ ker) is proved using naturality of
the shift-composition iso and h ≫ f⟦1⟧ = 0.
The forward direction (ker ⊆ im) uses `coyoneda_exact₁` on the
shifted map, requiring shift-functor iso manipulation to convert
between π_{n-1}(X) and maps into X⟦1⟧. -/
theorem les_homotopy_exact_h (T : HoCofiberSequence (𝒮 := 𝒮)) (n : ℤ) :
    ∀ (x : HomotopyGroup (n - 1) T.X),
      (inducedMap T.f (n - 1)) x = 0 ↔
        ∃ (z : HomotopyGroup n T.Z), (connectingHomomorphism T n) z = x := by
  intro x
  constructor
  · -- Forward: x ≫ T.f = 0 → ∃ z, connectingHomomorphism T n z = x
    -- Strategy: lift x : S^{n-1} → T.X to x' : S^n → T.X⟦1⟧ via shift isos,
    -- apply coyoneda_exact₁ to get z : S^n → T.Z with x' = z ≫ T.h,
    -- then show the connecting homomorphism applied to z equals x
    -- by coherence of the shift functor natural isos.
    intro hx
    simp only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hx
    -- Lift x to x' : S^n → T.X⟦1⟧
    let x' : Sphere n ⟶ (shiftFunctor 𝒮 (1 : ℤ)).obj T.X :=
      eqToHom (by
          change (shiftFunctor 𝒮 n).obj SphereSpectrum =
            (shiftFunctor 𝒮 (n - 1 + (1 : ℤ))).obj SphereSpectrum
          congr 2; omega) ≫
        (shiftFunctorAdd 𝒮 (n - 1) (1 : ℤ)).hom.app SphereSpectrum ≫
        (shiftFunctor 𝒮 (1 : ℤ)).map x
    -- x' ≫ shift(1)(T.f) = 0 because x ≫ T.f = 0
    have hx' : x' ≫ (shiftFunctor 𝒮 (1 : ℤ)).map T.f = 0 := by
      simp only [x', Category.assoc, ← Functor.map_comp, hx, Functor.map_zero,
        Limits.comp_zero]
    -- Apply coyoneda_exact₁ to get z : S^n → T.Z with x' = z ≫ T.h
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₁ _ T.distinguished x' hx'
    -- Show connectingHomomorphism T n z = x
    -- The proof structure is:
    --   ∂(z) = shift_add_iso ≫ shift(-1)(z ≫ T.h) ≫ shift_comp_iso
    --   z ≫ T.h = x' = eqToHom ≫ shiftAdd(n-1,1).hom ≫ shift(1)(x)
    -- After substituting and composing shift coherence isos, the result
    -- is x by MacLane's coherence for the shift functor system.
    -- The remaining proof is shift-functor iso bookkeeping.
    exact ⟨z, by
      simp only [connectingHomomorphism, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      -- hz : x' = z ≫ T.h (since Triangle.mk.mor₃ = T.h)
      -- Substitute z ≫ T.h = x' in the goal
      have hz' : z ≫ T.h = x' := hz.symm
      rw [hz']
      -- Goal: shiftFunctorAdd(n,-1).hom.app S ≫ F(-1)(x') ≫
      --        shiftFunctorCompIsoId(1,-1).hom.app T.X = x
      -- Step 1: Unfold x' and distribute F(-1).map, simplify eqToHom
      simp only [x', Functor.map_comp, eqToHom_map, Category.assoc]
      -- Step 2: Fold eqToHom back under F(-1) and combine with shiftFunctorAdd(n-1,1)
      rw [← eqToHom_map (shiftFunctor 𝒮 (-1 : ℤ)),
          ← Functor.map_comp_assoc (shiftFunctor 𝒮 (-1 : ℤ))]
      -- Step 3: Consolidate eqToHom ≫ shiftFunctorAdd → shiftFunctorAdd'
      -- Prove: eqToHom ≫ shiftFunctorAdd(n-1,1).hom.app S = shiftFunctorAdd'(n-1,1,n,⋯).hom.app S
      · have heq : ∀ (e : (shiftFunctor 𝒮 n).obj SphereSpectrum =
                  (shiftFunctor 𝒮 (n - 1 + 1)).obj SphereSpectrum),
                (shiftFunctor 𝒮 (-1 : ℤ)).map
                  (eqToHom e ≫ (shiftFunctorAdd 𝒮 (n - 1) 1).hom.app
                    SphereSpectrum) =
                (shiftFunctor 𝒮 (-1 : ℤ)).map
                  ((shiftFunctorAdd' 𝒮 (n - 1) 1 n (by omega)).hom.app
                    SphereSpectrum) := by
            intro e; congr 1; simp [shiftFunctorAdd']
        rw [heq]
        -- Step 4: Rewrite shiftFunctorAdd as shiftFunctorAdd'
        rw [← shiftFunctorAdd'_eq_shiftFunctorAdd 𝒮 n (-1 : ℤ)]
        -- Step 5: Apply shiftFunctorAdd'_assoc_hom_app_assoc
        rw [shiftFunctorAdd'_assoc_hom_app_assoc (n - 1) 1 (-1) n 0 (n + (-1))
            (by omega) one_plus_neg_one (by omega) SphereSpectrum]
        -- Step 6: Use shiftFunctorAdd'_add_zero_hom_app to simplify first term
        -- The third arg of shiftFunctorAdd' is (n + -1) but we need (n - 1);
        -- these are defeq, so use show/change to normalize
        change (shiftFunctorAdd' 𝒮 (n - 1) 0 (n - 1) _).hom.app SphereSpectrum ≫ _ = _
        rw [shiftFunctorAdd'_add_zero_hom_app]
        -- Step 7: Expand shiftFunctorCompIsoId into shiftFunctorAdd'.inv ≫ shiftFunctorZero.hom
        simp only [shiftFunctorCompIsoId, Iso.trans_hom, Iso.symm_hom,
          NatTrans.comp_app]
        -- Goal (using Sphere abbreviation): shiftFunctorZero.inv.app(Sphere(n-1)) ≫
        --   shiftFunctorAdd'(1,-1,0).hom.app(Sphere(n-1)) ≫
        --   F(-1)(F(1)(x)) ≫ shiftFunctorAdd'(1,-1,0).inv.app(T.X) ≫
        --   shiftFunctorZero.hom.app(T.X) = x
        -- Use show to normalize Sphere(n-1) = (shiftFunctor..).obj SphereSpectrum
        change (shiftFunctorZero 𝒮 ℤ).inv.app (Sphere (n - 1)) ≫
          (shiftFunctorAdd' 𝒮 1 (-1) 0 one_plus_neg_one).hom.app (Sphere (n - 1)) ≫
          (shiftFunctor 𝒮 (-1)).map ((shiftFunctor 𝒮 1).map x) ≫
          (shiftFunctorAdd' 𝒮 1 (-1) 0 one_plus_neg_one).inv.app T.X ≫
          (shiftFunctorZero 𝒮 ℤ).hom.app T.X = x
        -- Step 8: Use naturality of shiftFunctorAdd'.hom to rewrite
        -- .hom.app(Sphere(n-1)) ≫ F(-1)(F(1)(x)) = F(0)(x) ≫ .hom.app T.X
        have nat_hom := (shiftFunctorAdd' 𝒮 1 (-1) 0 one_plus_neg_one).hom.naturality x
        simp only [Functor.comp_map] at nat_hom
        -- Left-associate to expose the pattern, then rewrite, then clean up
        rw [← Category.assoc
              ((shiftFunctorAdd' 𝒮 1 (-1) 0 one_plus_neg_one).hom.app
                (Sphere (n - 1)))
              ((shiftFunctor 𝒮 (-1)).map ((shiftFunctor 𝒮 1).map x)),
            ← nat_hom]
        -- Right-associate, then cancel .hom ≫ .inv
        simp only [Category.assoc]
        rw [← Category.assoc ((shiftFunctorAdd' 𝒮 1 (-1) 0 one_plus_neg_one).hom.app T.X)
              ((shiftFunctorAdd' 𝒮 1 (-1) 0 one_plus_neg_one).inv.app T.X),
            Iso.hom_inv_id_app, Category.id_comp]
        -- Goal: shiftFunctorZero.inv.app(Sphere(n-1)) ≫ F(0)(x) ≫ shiftFunctorZero.hom.app(T.X) = x
        -- Step 9: Use naturality of shiftFunctorZero and cancel inv ≫ hom
        have nat_zero := (shiftFunctorZero 𝒮 ℤ).hom.naturality x
        simp only [Functor.id_map] at nat_zero
        rw [nat_zero, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
      · congr 2; omega⟩
  · -- Backward: ∃ z, connectingHomomorphism T n z = x → x ≫ T.f = 0
    rintro ⟨z, rfl⟩
    simp only [inducedMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    exact connectingHom_comp_f_zero T n z

/-! ## Functoriality of Homotopy Groups -/

/-- Homotopy groups are functorial: a map f : X → Y induces
a group homomorphism π_n(f) : π_n(X) → π_n(Y). -/
noncomputable def homotopyGroupFunctor (n : ℤ) :
    𝒮 ⥤ AddCommGrpCat.{v} where
  obj := fun X => AddCommGrpCat.mk (HomotopyGroup n X)
  map := fun f => AddCommGrpCat.ofHom (inducedMap f n)
  map_id := by
    intro X
    apply AddCommGrpCat.hom_ext
    ext x
    simp [inducedMap]
  map_comp := by
    intro X Y Z f g
    apply AddCommGrpCat.hom_ext
    ext x
    simp [inducedMap, Category.assoc]

end KIP.StableHomotopy
