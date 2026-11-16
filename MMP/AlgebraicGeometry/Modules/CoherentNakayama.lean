module

public import MMP.Attr
public import MMP.AlgebraicGeometry.ProjectiveBundle.VectorBundles
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# Nakayama's lemma for a map of coherent sheaves

Let `u : 𝒢 ⟶ ℱ` be a homomorphism of `𝒪_Y`-modules with `ℱ` coherent. If `u` is surjective on
the fibres `𝒢(y) ⟶ ℱ(y)` at a point `y`, then `u` is surjective on an open neighbourhood of `y`;
in particular, if `𝔪_y ℱ_y = ℱ_y`, i.e. the fibre `ℱ(y) = ℱ_y / 𝔪_y ℱ_y` vanishes, then `ℱ`
vanishes near `y` (Stacks 01Y3).

## Implementation notes

* Coherence is the class `SheafOfModules.IsCoherent` used throughout the library
  (Stacks 01BW). Only the target needs it; no hypothesis on the source `𝒢` is required.
* The sheaves of the source live on an open neighbourhood of `y`; an open subscheme is a scheme, so
  the statement is made on `Y` itself.
* The fibre `ℱ(y) = ℱ_y ⊗ κ(y)` and the fibre map `u(y)` are
  `MMP.Intersection.Scheme.Modules.fiber` and `MMP.Intersection.Scheme.Modules.fiberMap`.
  Surjectivity of `u` on an open `V` is that its restriction to `V` is an epimorphism; vanishing
  of `ℱ` on `V` is that its restriction to `V` is a zero object.
-/

@[expose] public section

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped ZeroObject

namespace MMP.Resolution.Bridges

open MMP.Intersection.Scheme.Modules (fiber fiberMap)

open TensorProduct in
/-- If `1 ⊗ₜ n = 0` in `B ⊗[A] N`, where `A → B` is surjective, then `n` lies in `I • N` for `I`
the kernel of `A → B`. -/
private theorem mem_ker_smul_top_of_one_tmul_eq_zero {A B N : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] (hs : Function.Surjective (algebraMap A B)) (n : N)
    (h : (1 : B) ⊗ₜ[A] n = 0) :
    n ∈ (RingHom.ker (Algebra.ofId A B)) • (⊤ : Submodule A N) := by
  let e : (A ⧸ RingHom.ker (Algebra.ofId A B)) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hs
  have key : (e.toLinearEquiv.rTensor N).symm ((1 : B) ⊗ₜ[A] n)
      = ((1 : A ⧸ RingHom.ker (Algebra.ofId A B)) ⊗ₜ[A] n :
        (A ⧸ RingHom.ker (Algebra.ofId A B)) ⊗[A] N) := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e]
  have h2 : (TensorProduct.quotTensorEquivQuotSMul N (RingHom.ker (Algebra.ofId A B)))
      ((1 : A ⧸ RingHom.ker (Algebra.ofId A B)) ⊗ₜ[A] n) = 0 := by
    rw [← key, h]
    simp
  exact (Submodule.Quotient.mk_eq_zero _).1 (by simpa using h2)

open TensorProduct in
/-- Nakayama: over a local ring, a linear map to a finite module whose base change to a
local quotient `B` is surjective is surjective. -/
private theorem surjective_of_lTensor_surjective {A B M N : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Algebra A B] [Nontrivial B]
    [AddCommGroup M] [instM : Module A M] [AddCommGroup N] [instN : Module A N]
    [Module.Finite A N]
    (hs : Function.Surjective (algebraMap A B)) (u : M →ₗ[A] N)
    (hu : Function.Surjective (u.lTensor B)) : Function.Surjective u := by
  have claim : ∀ t : B ⊗[A] M, ∃ w : M, u.lTensor B t = (1 : B) ⊗ₜ[A] (u w) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul b m =>
      obtain ⟨a, rfl⟩ := hs b
      refine ⟨a • m, ?_⟩
      simp [TensorProduct.smul_tmul', Algebra.smul_def]
    | add x y hx hy =>
      obtain ⟨w1, h1⟩ := hx
      obtain ⟨w2, h2⟩ := hy
      exact ⟨w1 + w2, by simp [h1, h2, TensorProduct.tmul_add]⟩
  rw [← LinearMap.range_eq_top, ← IsLocalRing.map_mkQ_eq_top, Submodule.map_mkQ_eq_top,
    eq_top_iff]
  intro x _
  obtain ⟨t, ht⟩ := hu ((1 : B) ⊗ₜ[A] x)
  obtain ⟨w, hw⟩ := claim t
  have hm := mem_ker_smul_top_of_one_tmul_eq_zero hs (x - u w)
    (by rw [TensorProduct.tmul_sub, ← ht, hw, sub_self])
  simpa using Submodule.add_mem_sup
    (Submodule.smul_mono_left (IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)) hm)
    (LinearMap.mem_range_self u w)

open TensorProduct in
/-- If a surjective `B`-linear map `ψ : M' → N'`, where `M' ≅ B ⊗ M` and `N' ≅ B ⊗ N`, sends
`1 ⊗ m` to `1 ⊗ σ m`, then `σ.lTensor B` is surjective. -/
private theorem lTensor_surjective_of_one_tmul {A B M N M' N' : Type*} [CommSemiring A]
    [Semiring B] [Algebra A B] [AddCommMonoid M] [instM : Module A M] [AddCommMonoid N]
    [instN : Module A N] [AddCommMonoid M'] [instM' : Module B M'] [AddCommMonoid N']
    [instN' : Module B N']
    (eM : M' ≃ₗ[B] TensorProduct A B M) (eN : N' ≃ₗ[B] TensorProduct A B N)
    (ψ : M' →ₗ[B] N') (σ : M →ₗ[A] N)
    (hkey : ∀ m : M, eN (ψ (eM.symm ((1 : B) ⊗ₜ[A] m))) = (1 : B) ⊗ₜ[A] σ m)
    (hsurj : Function.Surjective ψ) :
    Function.Surjective (σ.lTensor B) := by
  have hF : ∀ t, eN (ψ (eM.symm t)) = σ.baseChange B t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b m =>
      rw [TensorProduct.tmul_eq_smul_one_tmul b m]
      simp only [map_smul, hkey, LinearMap.baseChange_tmul]
    | add s t hs ht => simp only [map_add, hs, ht]
  intro t
  obtain ⟨a, ha⟩ := hsurj (eN.symm t)
  refine ⟨eM a, ?_⟩
  have := hF (eM a)
  rw [eM.symm_apply_apply, ha, eN.apply_symm_apply] at this
  exact this.symm

open TopologicalSpace Opposite in
/-- The stalk map of `φ` sends the germ of a section `t` to the germ of `φ t`. -/
@[simp]
theorem _root_.AlgebraicGeometry.stalkMapLinear_germ {X : TopCat.{u}}
    {R : X.Presheaf CommRingCat.{u}}
    {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (φ : M ⟶ N) (p : X)
    (V : Opens X) (hp : p ∈ V) (t : M.obj (op V)) :
    AlgebraicGeometry.stalkMapLinear M N φ p (TopCat.Presheaf.germ M.presheaf V p hp t) =
      TopCat.Presheaf.germ N.presheaf V p hp (φ.app (op V) t) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply V p hp ((PresheafOfModules.toPresheaf _).map φ) t

open RingedSpaceModuleAdjunction Opposite in
/-- Surjectivity of the stalk map of `g^* u` at `z` descends to surjectivity of the stalk map of
`u` at `g z`, for a preimmersion `g` and a target `F` of finite type (Stacks 0098, Nakayama). -/
private theorem stalk_surjective_of_pullback {S' S : Scheme.{u}} (g : S' ⟶ S) [IsPreimmersion g]
    {G F : S.Modules} [F.IsFiniteType] (u : G ⟶ F) (z : S')
    (h : Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z).map
        ((PresheafOfModules.toPresheaf _).map ((Scheme.Modules.pullback g).map u).val)))) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (g z)).map
        ((PresheafOfModules.toPresheaf _).map u.val))) := by
  classical
  letI : Algebra (S.presheaf.stalk (g.toLRSHom.toShHom.hom.base z)) (S'.presheaf.stalk z) :=
    (g.stalkMap z).hom.toAlgebra
  letI instF : Module (S.presheaf.stalk (g.toLRSHom.toShHom.hom.base z))
      (F.presheaf.stalk (g.toLRSHom.toShHom.hom.base z)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.presheaf) F.val (g.toLRSHom.toShHom.hom.base z)
  letI instG : Module (S.presheaf.stalk (g.toLRSHom.toShHom.hom.base z))
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) G.val.presheaf
        (g.toLRSHom.toShHom.hom.base z)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := S.presheaf) G.val (g.toLRSHom.toShHom.hom.base z)
  haveI : Module.Finite (S.presheaf.stalk (g.toLRSHom.toShHom.hom.base z))
      (F.presheaf.stalk (g.toLRSHom.toShHom.hom.base z)) :=
    _root_.SheafOfModules.finite_stalk S.sheaf F (g.toLRSHom.toShHom.hom.base z)
  have hs : Function.Surjective
      (algebraMap (S.presheaf.stalk (g.toLRSHom.toShHom.hom.base z)) (S'.presheaf.stalk z)) :=
    g.stalkMap_surjective z
  obtain ⟨eG, heG⟩ := exists_modulePullbackStalkLinearEquiv g.toLRSHom.toShHom G z
  obtain ⟨eF, heF⟩ := exists_modulePullbackStalkLinearEquiv g.toLRSHom.toShHom F z
  refine surjective_of_lTensor_surjective (instM := instG) (instN := instF) hs
    (AlgebraicGeometry.stalkMapLinear (R := S.presheaf) G.val F.val u.val
      (g.toLRSHom.toShHom.hom.base z))
    (lTensor_surjective_of_one_tmul (instM := instG) (instN := instF)
      (instM' := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := S'.presheaf) ((modulePullback g.toLRSHom.toShHom).obj G).val z)
      (instN' := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := S'.presheaf) ((modulePullback g.toLRSHom.toShHom).obj F).val z) eG eF
      (AlgebraicGeometry.stalkMapLinear (R := S'.presheaf) _ _
        ((Scheme.Modules.pullback g).map u).val z) _ (fun m => ?_) h)
  obtain ⟨V, hx, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.val.presheaf m
  have hunit := congrArg (fun k => k.val.app (op V) t)
    ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.naturality u)
  change ((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app F).val.app (op V)
      (u.val.app (op V) t) =
    ((modulePullback g.toLRSHom.toShHom).map u).val.app
      (op ((opensMap g.toLRSHom.toShHom).obj V))
      (((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app G).val.app (op V) t)
    at hunit
  have stepA := (congrArg eG.symm (heG V hx t)).symm.trans
    (eG.symm_apply_apply
      (TopCat.Presheaf.germ ((modulePullback g.toLRSHom.toShHom).obj G).val.presheaf
      ((opensMap g.toLRSHom.toShHom).obj V) z hx
      ((((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app G).val.app (op V)) t)))
  have stepB : AlgebraicGeometry.stalkMapLinear (R := S'.presheaf)
        ((modulePullback g.toLRSHom.toShHom).obj G).val
        ((modulePullback g.toLRSHom.toShHom).obj F).val
        ((modulePullback g.toLRSHom.toShHom).map u).val z
        (TopCat.Presheaf.germ ((modulePullback g.toLRSHom.toShHom).obj G).val.presheaf
          ((opensMap g.toLRSHom.toShHom).obj V) z hx
          ((((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app G).val.app
            (op V)) t)) =
      TopCat.Presheaf.germ ((modulePullback g.toLRSHom.toShHom).obj F).val.presheaf
        ((opensMap g.toLRSHom.toShHom).obj V) z hx
        ((((modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).unit.app F).val.app (op V))
          (u.val.app (op V) t)) := by
    refine (stalkMapLinear_germ (((modulePullback g.toLRSHom.toShHom).map u).val) z
      ((opensMap g.toLRSHom.toShHom).obj V) hx _).trans ?_
    congr 1
    exact hunit.symm
  refine (congrArg (fun w => eF (AlgebraicGeometry.stalkMapLinear (R := S'.presheaf)
      ((modulePullback g.toLRSHom.toShHom).obj G).val
      ((modulePullback g.toLRSHom.toShHom).obj F).val
      ((modulePullback g.toLRSHom.toShHom).map u).val z w)) stepA).trans
    ((congrArg eF stepB).trans ((heF V hx (u.val.app (op V) t)).trans ?_))
  congr 1
  exact (stalkMapLinear_germ u.val (g.toLRSHom.toShHom.hom.base z) V hx t).symm

/-- Surjectivity of the fibre map at `y` gives surjectivity of the stalk map at `y`. -/
private theorem stalk_surjective_of_fiberMap {Y : Scheme.{u}} {G F : Y.Modules}
    [F.IsFiniteType] (u : G ⟶ F) (y : Y) (hu : Function.Surjective (fiberMap u y)) :
    Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((PresheafOfModules.toPresheaf _).map u.val))) := by
  let g := Y.fromSpecResidueField y
  let z : Spec (Y.residueField y) := ⟨(⊥ : Ideal (Y.residueField y)), inferInstance⟩
  rw [← Scheme.fromSpecResidueField_apply y z]
  refine stalk_surjective_of_pullback g u z fun s => ?_
  obtain ⟨U, hzU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.Modules.pullback g).obj F).val.presheaf s
  obtain rfl : U = ⊤ := eq_top_iff.2 fun w _ => Subsingleton.elim z w ▸ hzU
  obtain ⟨w, hw⟩ := hu t
  exact ⟨TopCat.Presheaf.germ ((Scheme.Modules.pullback g).obj G).val.presheaf ⊤ z hzU w,
    (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ z hzU
      ((PresheafOfModules.toPresheaf _).map ((Scheme.Modules.pullback g).map u).val) w).trans
      (congrArg _ hw)⟩

/-- Surjectivity of `u` on the stalks at the points of `V` makes its restriction to `V` an
epimorphism. -/
private theorem epi_restrict_of_forall_stalk_surjective {Y : Scheme.{u}} {G F : Y.Modules}
    (u : G ⟶ F) (V : Y.Opens)
    (h : ∀ w ∈ V, Function.Surjective (ConcreteCategory.hom
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} w).map
        ((PresheafOfModules.toPresheaf _).map u.val)))) :
    Epi ((Scheme.Modules.restrictFunctor V.ι).map u) := by
  refine (AlgebraicGeometry.epi_iff_stalk_surjective V.toScheme.ringCatSheaf _).2 fun w s => ?_
  let e := Scheme.Modules.restrictStalkNatIso V.ι w
  obtain ⟨a, ha⟩ := h (V.ι w) w.2 (ConcreteCategory.hom (e.hom.app F) s)
  refine ⟨ConcreteCategory.hom (e.inv.app G) a, ?_⟩
  have h2 := (ConcreteCategory.congr_hom (e.inv.naturality u) a).symm
  simp only [Functor.comp_map, ConcreteCategory.comp_apply] at h2
  exact h2.trans <| (congrArg (ConcreteCategory.hom (e.inv.app F)) ha).trans
    (ConcreteCategory.congr_hom (e.hom_inv_id_app F) s)

/-- **Nakayama for a map of coherent sheaves.** Let `Y` be a scheme, `y ∈ Y` and `u : 𝒢 ⟶ ℱ` a
homomorphism of `𝒪_Y`-modules with `ℱ` coherent, such that `u ⊗ κ(y) : 𝒢 ⊗ κ(y) ⟶ ℱ ⊗ κ(y)` is
surjective. Then `u` is surjective on an open neighbourhood of `y`. -/
@[mmp "lem_mmp_foundation_coherent_nakayama"]
theorem exists_epi_restrict_of_surjective_fiberMap {Y : Scheme.{u}} {G F : Y.Modules}
    [F.IsCoherent] (u : G ⟶ F) (y : Y) (hu : Function.Surjective (fiberMap u y)) :
    ∃ V : Y.Opens, y ∈ V ∧ Epi ((Scheme.Modules.restrictFunctor V.ι).map u) := by
  have hfin : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType (M := F)
  obtain ⟨U, hyU, hU⟩ := Stacks.SheafOfModules.LocallySurjective.main_theorem
    (X := Y.toRingedSpace) u hfin y (stalk_surjective_of_fiberMap u y hu)
  exact ⟨U, hyU, epi_restrict_of_forall_stalk_surjective u U hU⟩

/-- **Nakayama for a coherent sheaf.** If `ℱ` is a coherent `𝒪_Y`-module with
`𝔪_y ℱ_y = ℱ_y`, i.e. with zero fibre `ℱ ⊗ κ(y) = ℱ_y / 𝔪_y ℱ_y`, then `ℱ = 0` on an open
neighbourhood of `y`. -/
@[mmp "lem_mmp_foundation_coherent_nakayama"]
theorem exists_isZero_restrict_of_subsingleton_fiber {Y : Scheme.{u}} (F : Y.Modules)
    [F.IsCoherent] (y : Y) (hF : Subsingleton (fiber F y)) :
    ∃ V : Y.Opens, y ∈ V ∧ IsZero (F.restrict V.ι) := by
  obtain ⟨V, hyV, hV⟩ := exists_epi_restrict_of_surjective_fiberMap
    (0 : (0 : Y.Modules) ⟶ F) y (fun _ => ⟨0, Subsingleton.elim _ _⟩)
  refine ⟨V, hyV, (IsZero.iff_id_eq_zero _).2 ?_⟩
  refine (cancel_epi ((Scheme.Modules.restrictFunctor V.ι).map (0 : (0 : Y.Modules) ⟶ F))).1 ?_
  exact ((Scheme.Modules.restrictFunctor V.ι).map_isZero (isZero_zero _)).eq_of_src _ _

end MMP.Resolution.Bridges
