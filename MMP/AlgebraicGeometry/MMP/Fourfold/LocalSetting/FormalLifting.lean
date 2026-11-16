module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.AdaptedOpen
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FibreH2Vanishing
import MMP.AlgebraicGeometry.Modules.SquareZeroInvertibleLift
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle

/-!
# Formal lifting of line bundles on the generic fibre

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`), `A = 𝒪_{Y,η_T}` the
local ring of `Y` at the generic point of `T`, with maximal ideal `𝔪`, `Z = Ỹ ×_Y Spec A`
(`MMP.Fourfold.pointSettingLocalization`) and `F_n = Z ×_A A/𝔪^{n+1}`
(`MMP.Fourfold.pointSettingThickening`). Every line bundle `L` on `F_0` extends to a compatible
system of line bundles `L⁽ⁿ⁾` on the thickenings `F_n`: `L⁽⁰⁾ = L`, and the restriction of
`L⁽ⁿ⁺¹⁾` to `F_n` along the closed immersion `F_n ⟶ F_{n+1}` is isomorphic to `L⁽ⁿ⁾`.

## Main results

* `MMP.Fourfold.IsLocalSetting.exists_isInvertible_pullback_thickening_iso`

## Implementation notes

* The closed immersion `F_n ⟶ F_{n+1}` is the identity on `Z` and, on the second factor, the
  spectrum of the projection `A/𝔪^{n+2} ⟶ A/𝔪^{n+1}` (`Ideal.Quotient.factor`); the
  restriction of a module to `F_n` is its pull-back along that map.
* A line bundle is an invertible module (`SheafOfModules.IsInvertible`). Since the family
  `n ↦ L⁽ⁿ⁾` is dependent on `n`, the condition `L⁽⁰⁾ = L` is stated as an equality of modules
  on `F_0`.
-/

@[expose] public section

namespace MMP.Fourfold.FormalLifting

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Mori MMP.Fourfold

universe u

section Step

open Stacks.FormalCurve RingedSpaceModuleAdjunction Stacks.ClosedImmersion

attribute [local instance] HasDerivedCategory.standard

private theorem isZero_rightDerived_three {Y : Scheme.{u}} [NoetherianSpace Y]
    (hdim : topologicalKrullDim (Y : Type u) ≤ 2) (F : Y.Modules) :
    IsZero (((moduleGlobalSections Y).rightDerived 3).obj F) := by
  have h : IsZero (Hgroup Y.ringCatSheaf ⊤ 3 F) := by
    rw [Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH]
    exact Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le
      (d := 2) (by exact_mod_cast hdim) (by norm_num) _
  exact Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
    Y.ringCatSheaf ⊤ 3 F h

private theorem isZero_rightDerived_two_step {Y Z : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i] [NoetherianSpace Y] (hdim : topologicalKrullDim (Y : Type u) ≤ 2)
    {r : ℕ} (g : Fin r → Γ(Y, ⊤)) (hg : ∀ k, (i.appTop (g k)) = 0)
    (hgen : ∀ U : Y.affineOpens,
      RingHom.ker (i.app U.1).hom ≤
        Ideal.span (Set.range fun j => Stacks.Thickenings.globalRestrict Y (g j) U.1))
    (hsq : ∀ j k, g j * g k = 0)
    (hZ : IsZero (((moduleGlobalSections Z).rightDerived 2).obj
      (SheafOfModules.unit (structureSheafRing Z.toSheafedSpace)))) :
    IsZero (((moduleGlobalSections Y).rightDerived 2).obj (idealSheaf i.toLRSHom.toShHom)) ∧
    IsZero (((moduleGlobalSections Y).rightDerived 2).obj
      (SheafOfModules.unit (structureSheafRing Y.toSheafedSpace))) := by
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (moduleGlobalSections Y)
  have hpush : IsZero (((moduleGlobalSections Y).rightDerived 2).obj
      ((modulePushforward i.toLRSHom.toShHom).obj
        (SheafOfModules.unit (structureSheafRing Z.toSheafedSpace)))) :=
    ((ModuleCat.restrictScalars i.appTop.hom).map_isZero hZ).of_iso
      (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward i _ 2)
  have hE := epi_generatorsDesc i g hg hgen hsq
  set φ := generatorsDesc i g hg hgen hsq
  have hS : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).ShortExact :=
    { exact := ShortComplex.exact_kernel φ }
  let G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) ⥤
      ModuleCat.{u} Γ(Y, ⊤) := (moduleGlobalSections Y).rightDerived 2
  haveI : G.Additive := D.additive 2
  have hsum : IsZero (G.obj (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).X₂) :=
    isZero_map_biproduct G _ fun _ => hpush
  have hideal : IsZero (((moduleGlobalSections Y).rightDerived 2).obj
      (idealSheaf i.toLRSHom.toShHom)) :=
    (D.exact_δ₁ hS 2).isZero_X₂ (hsum.eq_of_src _ _)
      ((isZero_rightDerived_three hdim _).eq_of_tgt _ _)
  exact ⟨hideal, (D.exact_map (Stacks.Cohomology.AmpleH1.shortExact_idealSheaf i) 2).isZero_X₂
    (hideal.eq_of_src _ _) (hpush.eq_of_tgt _ _)⟩

/-- Vanishing of a derived global sections module makes the abelian sheaf cohomology vanish. -/
private theorem subsingleton_sheafH_of_isZero_rightDerived {Y : Scheme.{u}} {n : ℕ}
    {F : Y.Modules} (h : IsZero (((moduleGlobalSections Y).rightDerived n).obj F)) :
    Subsingleton (Sheaf.H.{u} ((SheafOfModules.toSheaf Y.ringCatSheaf).obj F) n) := by
  rw [← Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH]
  obtain ⟨-, -, hopen⟩ := ModuleSheafCohomology.moduleSheafCohomologyIsoUnderlying
    (Opens.grothendieckTopology Y) Y.ringCatSheaf
  obtain ⟨eU, -⟩ := hopen ⊤
  have hforget : IsZero ((forget₂ (ModuleCat.{u} (Y.ringCatSheaf.obj.obj (Opposite.op ⊤)))
      AddCommGrpCat.{u}).obj
      (((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op ⊤)).rightDerived n).obj F)) :=
    (forget₂ _ AddCommGrpCat.{u}).map_isZero h
  exact (hforget.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso
    Y.ringCatSheaf ⊤ n).app F).symm).of_iso ((eU n).app F)

end Step

section Tower

open Stacks.FormalCurve Stacks.Thickenings RingedSpaceModuleAdjunction Stacks.ClosedImmersion

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {Xn : ℕ → Scheme.{u}}
  (q : ∀ n, Xn n ⟶ adicThickening A I n) (i : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (i n) (q n) (q (n + 1)) (adicThickeningSucc A I n))

include hcart in
/-- The ideal of `Xₙ ⊆ Xₙ₊₁` is generated, on affine opens, by finitely many global functions
coming from `Iⁿ⁺¹`; they vanish on `Xₙ` and multiply to zero. -/
private theorem exists_generators (n : ℕ) :
    ∃ (r : ℕ) (g : Fin r → Γ(Xn (n + 1), ⊤)), (∀ k, (i n).appTop (g k) = 0) ∧
      (∀ U : (Xn (n + 1)).affineOpens, RingHom.ker ((i n).app U.1).hom ≤
        Ideal.span (Set.range fun j => globalRestrict (Xn (n + 1)) (g j) U.1)) ∧
      ∀ j k, g j * g k = 0 := by
  obtain ⟨r, a, ha⟩ : ∃ (r : ℕ) (a : Fin r → A), Ideal.span (Set.range a) = I ^ (n + 1) :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian _)
  have hmem : ∀ k, a k ∈ I ^ (n + 1) := fun k => ha ▸ Ideal.subset_span ⟨k, rfl⟩
  refine ⟨r, fun k => baseFunction I n (q (n + 1)) (a k),
    fun k => appTop_baseFunction I n (q n) (q (n + 1)) (i n) (hcart n) _ (hmem k),
    ker_app_le_span I n (q n) (q (n + 1)) (i n) (hcart n) a ha, fun j k => ?_⟩
  rw [← baseFunction_mul]
  exact baseFunction_eq_zero I n (q (n + 1)) _ (Ideal.pow_le_pow_right (by omega)
    (pow_add I (n + 1) (n + 1) ▸ Ideal.mul_mem_mul (hmem j) (hmem k)))

include hcart in
/-- The ideal of `Xₙ ⊆ Xₙ₊₁` has square zero. -/
private theorem ker_sq_eq_bot (n : ℕ) :
    haveI : IsClosedImmersion (i n) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart n).flip inferInstance
    (i n).ker ^ 2 = ⊥ := by
  haveI : IsClosedImmersion (i n) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart n).flip inferInstance
  obtain ⟨r, g, -, hgen, hsq⟩ := exists_generators A I q i hcart n
  apply Scheme.IdealSheafData.ext
  rw [pow_two, Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_bot]
  funext U
  rw [Pi.mul_apply, Scheme.Hom.ker_apply, Pi.bot_apply, eq_bot_iff]
  refine (Ideal.mul_mono (hgen U) (hgen U)).trans ?_
  rw [Ideal.span_mul_span', Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_bot]
  change ((Xn (n + 1)).presheaf.map _).hom (g j) * ((Xn (n + 1)).presheaf.map _).hom (g k) = 0
  rw [← map_mul, hsq, map_zero]

include hcart in
/-- `H²(Xₙ, 𝒪) = 0` for every member of the tower, if it holds for `X₀` and every member is a
Noetherian space of dimension at most two. -/
private theorem isZero_rightDerived_two_tower [∀ n, NoetherianSpace (Xn n)]
    (hdim : ∀ n, topologicalKrullDim (Xn n) ≤ 2)
    (h0 : IsZero (((moduleGlobalSections (Xn 0)).rightDerived 2).obj
      (SheafOfModules.unit (structureSheafRing (Xn 0).toSheafedSpace)))) (n : ℕ) :
    IsZero (((moduleGlobalSections (Xn n)).rightDerived 2).obj
      (SheafOfModules.unit (structureSheafRing (Xn n).toSheafedSpace))) := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    haveI : IsClosedImmersion (i n) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart n).flip inferInstance
    obtain ⟨r, g, hg, hgen, hsq⟩ := exists_generators A I q i hcart n
    exact (isZero_rightDerived_two_step (i n) (hdim (n + 1)) g hg hgen hsq ih).2

include hcart in
/-- Every invertible module on `Xₙ` extends to `Xₙ₊₁`. -/
private theorem liftsInvertible_tower [∀ n, NoetherianSpace (Xn n)]
    (hdim : ∀ n, topologicalKrullDim (Xn n) ≤ 2)
    (h0 : IsZero (((moduleGlobalSections (Xn 0)).rightDerived 2).obj
      (SheafOfModules.unit (structureSheafRing (Xn 0).toSheafedSpace)))) (n : ℕ) :
    MMP.Fourfold.LiftsInvertible (i n) := by
  haveI : IsClosedImmersion (i n) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hcart n).flip inferInstance
  obtain ⟨r, g, hg, hgen, hsq⟩ := exists_generators A I q i hcart n
  have h := (isZero_rightDerived_two_step (i n) (hdim (n + 1)) g hg hgen hsq
    (isZero_rightDerived_two_tower A I q i hcart hdim h0 n)).1
  have hsub := subsingleton_sheafH_of_isZero_rightDerived h
  intro L _
  exact MMP.Resolution.Bridges.exists_isInvertibleModule_pullback_iso_of_ker_sq_eq_bot (i n)
    (ker_sq_eq_bot A I q i hcart n) (fun x => @Subsingleton.elim _ hsub x 0) L

end Tower

section Curve

variable {Y : Scheme.{0}}

/-- The image of the closed immersion `T ⟶ Y` is `T`. -/
private theorem range_curveι (T : IrreducibleCloseds Y) :
    Set.range (curveι T) = (T : Set Y) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The closed immersion `T ⟶ Y` sends the generic point of the curve to `η_T`. -/
private theorem curveι_genericPoint (T : IrreducibleCloseds Y) [IrreducibleSpace (curveScheme T)] :
    curveι T (genericPoint (curveScheme T)) = localSettingGenericPoint T := by
  have h := (genericPoint_spec (curveScheme T)).image (curveι T).continuous
  rw [Set.image_univ, range_curveι, T.isClosed.closure_eq] at h
  exact h.eq (isGenericPoint_localSettingGenericPoint T)

/-- The fibre of a local setting over the generic point of the curve has dimension at most two. -/
private theorem topologicalKrullDim_pointSettingFibre_le
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) :
    topologicalKrullDim (pointSettingFibre π (localSettingGenericPoint T)) ≤ 2 := by
  obtain ⟨To, hTo⟩ := h.exists_isAdaptedOpen_and_isAdaptedOpen_of_le.1
  haveI hirr : IrreducibleSpace (curveScheme T) :=
    MMP.Intersection.Scheme.IdealSheafData.irreducibleSpace_subscheme_vanishingIdeal
      T.isIrreducible
  haveI : Nonempty (curveScheme T) := hirr.toNonempty
  have hmem : genericPoint (curveScheme T) ∈ To :=
    ((genericPoint_spec (curveScheme T)).mem_open_set_iff To.isOpen).2
      (by simpa using hTo.dense.nonempty)
  have hle := hTo.topologicalKrullDim_fibre_le ⟨_, hmem⟩
  rwa [curveι_genericPoint] at hle

/-- The fibre of a local setting over the generic point of the curve is a Noetherian space. -/
private theorem noetherianSpace_pointSettingFibre
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π) :
    NoetherianSpace (pointSettingFibre π (localSettingGenericPoint T)) := by
  haveI : IsProper π := isProper_of_isProjectiveMorphism _ h.isResolution.2.2.2.1
  haveI : IsLocallyNoetherian Yt := LocallyOfFiniteType.isLocallyNoetherian π
  haveI : IsNoetherian (pointSettingFibre π (localSettingGenericPoint T)) := ⟨⟩
  infer_instance

end Curve

end MMP.Fourfold.FormalLifting

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MMP.Mori

namespace MMP.Fourfold.IsLocalSetting

open FormalLifting in
/-- In a local setting `(Y, Θ, T, π)`, with `A = 𝒪_{Y,η_T}`, `Z = Ỹ ×_Y Spec A` and
`F_n = Z ×_A A/𝔪^{n+1}`, every line bundle `L` on `F_0` admits line bundles `L⁽ⁿ⁾` on `F_n`
with `L⁽⁰⁾ = L` and `L⁽ⁿ⁺¹⁾|_{F_n} ≅ L⁽ⁿ⁾` for all `n`, the restriction being along the
closed immersion `F_n ⟶ F_{n+1}` induced by `A/𝔪^{n+2} ⟶ A/𝔪^{n+1}`. -/
@[mmp "lem_oai4_c2_formal_lifting"]
public theorem exists_isInvertible_pullback_thickening_iso
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (h : IsLocalSetting sY Θ T π)
    (L : (pointSettingThickening π (localSettingGenericPoint T) 0).Modules)
    [SheafOfModules.IsInvertible (pointSettingThickening π (localSettingGenericPoint T) 0).presheaf
      (pointSettingThickening π (localSettingGenericPoint T) 0).ringCatSheaf.2 L] :
    let A := Y.presheaf.stalk (localSettingGenericPoint T)
    let 𝔪 := IsLocalRing.maximalIdeal A
    let ι : ∀ n : ℕ, pointSettingThickening π (localSettingGenericPoint T) n ⟶
        pointSettingThickening π (localSettingGenericPoint T) (n + 1) := fun n ↦
      pullback.map _ _ _ _ (𝟙 _)
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : 𝔪 ^ (n + 1 + 1) ≤ 𝔪 ^ (n + 1)))))
        (𝟙 _) (by simp) (by
          rw [Category.comp_id]
          exact (congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ ↦ rfl) :
            CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1))) =
              CommRingCat.ofHom (Ideal.Quotient.mk (𝔪 ^ (n + 1 + 1))) ≫
                CommRingCat.ofHom (Ideal.Quotient.factor
                  (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))).trans
            (Spec.map_comp _ _))
    ∃ (Ls : ∀ n : ℕ, (pointSettingThickening π (localSettingGenericPoint T) n).Modules)
      (_ : ∀ n, SheafOfModules.IsInvertible
        (pointSettingThickening π (localSettingGenericPoint T) n).presheaf
        (pointSettingThickening π (localSettingGenericPoint T) n).ringCatSheaf.2 (Ls n)),
      Ls 0 = L ∧ ∀ n, Nonempty ((Scheme.Modules.pullback (ι n)).obj (Ls (n + 1)) ≅ Ls n) := by
  intro A 𝔪 ι
  let η := localSettingGenericPoint T
  let fX := pullback.snd π (Y.fromSpecStalk η)
  have hι : ∀ n, ι n = adicBaseChangeSucc A 𝔪 fX n := by
    intro n
    apply pullback.hom_ext
    · simp only [ι, pullback.lift_fst, Category.comp_id, pullback.map]
      exact (pullback.lift_fst _ _ _).symm
    · simp only [ι, pullback.lift_snd, pullback.map]
      exact (pullback.lift_snd _ _ _).symm
  have hdimF : topologicalKrullDim (pointSettingFibre π η) ≤ 2 :=
    topologicalKrullDim_pointSettingFibre_le h
  haveI : NoetherianSpace (pointSettingFibre π η) := noetherianSpace_pointSettingFibre h
  let e := pointSettingFibreIsoThickeningZero π η
  have hhomeo : IsHomeomorph e.hom.base := (Scheme.Hom.homeomorph e.hom).isHomeomorph
  haveI : NoetherianSpace (adicBaseChange A 𝔪 fX 0) :=
    noetherianSpace_of_surjective _ e.hom.continuous hhomeo.surjective
  have hdim0 : topologicalKrullDim (adicBaseChange A 𝔪 fX 0) ≤ 2 :=
    (hhomeo.topologicalKrullDim_eq).symm.le.trans hdimF
  let i := adicBaseChangeSucc A 𝔪 fX
  have hcart := isPullback_adicBaseChangeSucc A 𝔪 fX
  have hi : ∀ n, Function.Surjective (i n) := fun n =>
    (bijective_base_adicBaseChangeSucc A 𝔪 fX n).2
  haveI := noetherianSpace_tower i hi
  have hdim : ∀ n, topologicalKrullDim (adicBaseChange A 𝔪 fX n) ≤ 2 := fun n =>
    (topologicalKrullDim_tower i hi n).trans_le hdim0
  have h0 : IsZero (((moduleGlobalSections (adicBaseChange A 𝔪 fX 0)).rightDerived 2).obj
      (SheafOfModules.unit (structureSheafRing (adicBaseChange A 𝔪 fX 0).toSheafedSpace))) := by
    haveI : NoetherianSpace (pointSettingThickening π η 0) :=
      ‹NoetherianSpace (adicBaseChange A 𝔪 fX 0)›
    have hsub := h.subsingleton_H_two_pointSettingFibre hdimF
    have hH : IsZero (Hgroup (pointSettingFibre π η).ringCatSheaf ⊤ 2
        (SheafOfModules.unit (pointSettingFibre π η).ringCatSheaf)) :=
      (Stacks.Cohomology.ModuleComparison.isZero_schemeHgroupTop_iff_subsingleton_sheafH _ _ _).2
        hsub
    have hZ := Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
      (pointSettingFibre π η).ringCatSheaf ⊤ 2 _ hH
    refine (isZero_rightDerived_two_step e.hom hdim0 (r := 0) Fin.elim0 (fun k => k.elim0)
      (fun U => ?_) (fun j => j.elim0) hZ).2
    exact ((RingHom.injective_iff_ker_eq_bot _).1
      (ConcreteCategory.bijective_of_isIso (e.hom.app U.1)).1).le.trans bot_le
  have hlift := liftsInvertible_tower A 𝔪 (fun n => pullback.snd fX (adicThickeningι A 𝔪 n)) i
    hcart hdim h0
  let stage : ∀ n, InvertibleTowerStage (adicBaseChange A 𝔪 fX) n := fun n =>
    Nat.rec ⟨L, ‹_›⟩ (fun n S => ⟨(@hlift n S.obj S.isInvertible).choose,
      (@hlift n S.obj S.isInvertible).choose_spec.choose⟩) n
  refine ⟨fun n => (stage n).obj, fun n => (stage n).isInvertible, rfl, fun n => ?_⟩
  rw [hι]
  exact (@hlift n (stage n).obj (stage n).isInvertible).choose_spec.choose_spec

end MMP.Fourfold.IsLocalSetting
