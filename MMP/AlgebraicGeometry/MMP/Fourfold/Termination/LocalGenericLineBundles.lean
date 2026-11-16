module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.NormChernAverage
import MMP.AlgebraicGeometry.Singularities.Surface.SingularPointMldBound
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveRankShrinking
import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
import MMP.AlgebraicGeometry.Analytic.SmoothHolomorphicCharts
import MMP.AlgebraicGeometry.Analytic.SchemeManifoldDescent
import MMP.AlgebraicGeometry.Analytic.ComplexRealizationHausdorff
import MMP.AlgebraicGeometry.Resolution.TransformRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FibreChernClassSpan
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurvePuncturedRestrictionSplit
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.AdaptedOpen

/-!
# Generic line bundles in a local setting

Let `(Y, Θ, T, π)` be a local setting: `Y` a normal projective `ℚ`-factorial complex fourfold,
`(Y, Θ)` terminal, `T ⊆ Sing Y` an irreducible curve and `π : Ỹ ⟶ Y` a projective resolution
which is an isomorphism over `Y_reg`. Write `b_T` for the rank of the punctured local system
`𝒱_T = (R²j_* ℚ_{Y_reg})|_{T°}`, the dimension of `H²_c(T°, 𝒱_T)` on a local-system open `T°`.
Then there are `b_T` line bundles on the generic scheme fibre `F_{η_T} = Ỹ ×_Y Spec K_T`
forming a punctured-independent family: they spread out to line bundles on `Ỹ ×_Y T¹` over a
`π`-adapted open `T¹` whose first Chern classes at every closed point `t ∈ T¹` have linearly
independent images in `𝒱_{T,t}`.

## Main results

* `MMP.Fourfold.IsLocalSetting.exists_isPuncturedIndependent`: for every local-system open
  `T°`, a punctured-independent family of `MMP.Fourfold.curveLocalSystemRank sY T°` line bundles
  on `MMP.Fourfold.genericFibre π T`.

## Implementation notes

The integer `b_T` does not depend on the local-system open on which it is computed, so the
result is stated for every local-system open `T°`, with `b_T = curveLocalSystemRank sY T°`.
A line bundle is an invertible sheaf of modules, `SheafOfModules.IsInvertible`.
-/

@[expose] public noncomputable section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite

namespace Proof_lem_oai4_local_generic_lines

open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open Topology MMP MMP.UnderlyingSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Germs of inverse images -/

section Transport

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)

/-- The inverse-image sheaf `f⁻¹ F` on `X`. -/
private abbrev pullbackSheaf : TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F

/-- The section of `f^* F` over `f⁻¹(W)` attached to a section of `F` over `W`. -/
private def unitSec {W : Opens Y} (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) :
    ToType (((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).obj (op ((Opens.map f).obj W))) :=
  (((TopCat.Sheaf.forget _ Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
      (op W)).hom r

private theorem stalkToPullbackStalk_germ {W : Opens Y}
    (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (x : X) (hx : f x ∈ W) :
    (stalkToPullbackStalk f F x).hom (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx r) =
      ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ ((Opens.map f).obj W) x hx
        (unitSec f F r) := by
  have h : ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx ≫ stalkToPullbackStalk f F x =
      ((TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
          (op W) ≫ ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ
            ((Opens.map f).obj W) x hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun φ => φ.hom r) h

private theorem exists_section_of_local
    (y : ∀ x : X, ToType (((TopCat.Sheaf.forget _ Y).obj F).stalk (f x)))
    (hy : ∀ x₀ : X, ∃ (W : Opens Y) (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W)))
      (N : Opens X) (_ : x₀ ∈ N) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), y x = ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) (hNW hx) r) :
    ∃ s : ToType (((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).obj (op ⊤)), ∀ x,
      ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ ⊤ x trivial s =
        (stalkToPullbackStalk f F x).hom (y x) := by
  choose W r N hN hNW hloc using hy
  set P := (TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)
  let sf : ∀ i : X, ToType (P.obj (op (N i))) := fun i =>
    P.map (homOfLE (hNW i)).op (unitSec f F (r i))
  have hgerm : ∀ i x (hx : x ∈ N i), P.germ (N i) x hx (sf i) =
      (stalkToPullbackStalk f F x).hom (y x) := by
    intro i x hx
    rw [TopCat.Presheaf.germ_res_apply, hloc i x hx]
    exact (stalkToPullbackStalk_germ f F (r i) x _).symm
  have hcompat : TopCat.Presheaf.IsCompatible P N sf := by
    intro i j
    refine TopCat.Presheaf.section_ext (pullbackSheaf f F) _ _ _ fun x hx => ?_
    change P.germ _ x hx _ = P.germ _ x hx _
    rw [TopCat.Presheaf.germ_res_apply P ((N i).infLELeft (N j)) x hx (sf i),
      TopCat.Presheaf.germ_res_apply P ((N i).infLERight (N j)) x hx (sf j), hgerm, hgerm]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (pullbackSheaf f F) N ⊤
    (fun i => homOfLE le_top) (fun x _ => Opens.mem_iSup.2 ⟨x, hN x⟩) sf hcompat
  refine ⟨s, fun x => ?_⟩
  rw [← hgerm x x (hN x), ← hs x]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

omit F in
private theorem stalkCongr_germ (P : TopCat.Presheaf (ModuleCat.{0} ℚ) Y) {p q : Y}
    (e : Inseparable p q)
    {U : Opens Y} (hp : p ∈ U) (hq : q ∈ U) (r : ToType (P.obj (op U))) :
    (P.stalkCongr e).hom.hom (P.germ U p hp r) = P.germ U q hq r :=
  TopCat.Presheaf.germ_stalkSpecializes_apply P hp e.ge r

omit F in
private theorem stalkCongr_stalkCongr (P : TopCat.Presheaf (ModuleCat.{0} ℚ) Y) {p q u : Y}
    (e : Inseparable p q) (e' : Inseparable q u) (y : ToType (P.stalk p)) :
    (P.stalkCongr e').hom.hom ((P.stalkCongr e).hom.hom y) =
      (P.stalkCongr (e.trans e')).hom.hom y :=
  TopCat.Presheaf.stalkSpecializes_comp_apply P e'.ge e.ge y

omit F in
private theorem stalkCongr_self (P : TopCat.Presheaf (ModuleCat.{0} ℚ) Y) {p : Y}
    (e : Inseparable p p) (y : ToType (P.stalk p)) : (P.stalkCongr e).hom.hom y = y := by
  change (P.stalkSpecializes e.ge).hom y = y
  rw [show e.ge = specializes_refl p from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

end Transport

/-! ### Sheets of a family over a base change -/

/-- The sheet `F_t × {t''} ⟶ 𝓕' = 𝓕 ×_{T°} T'` over a `ℂ`-point `t''` of `T'` above `t`: its
components are the inclusion `F_t ⟶ 𝓕` and `F_t ⟶ Spec ℂ ⟶ T'` through `t''`. -/
private def sheetι {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}
    {π : Yt ⟶ Y} {To : (curveScheme T).Opens} {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)}
    {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}
    (t'' : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}) :
    pointFibre sY π To t ⟶ pullback (pullback.snd π (To.ι ≫ curveι T)) φ :=
  pullback.lift (pointFibreToFamily sY π To t) (pointFibreSnd sY π To t ≫ t''.1.hom) (by
    rw [Category.assoc, t''.2]
    exact pullback.lift_snd _ _ _)

/-- The sheet `F_t × {t''}` lies over the inclusion `F_t ⟶ 𝓕`. -/
private theorem sheetι_comp_fst {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {To : (curveScheme T).Opens}
    {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)} {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}
    (s : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}) :
    sheetι s ≫ pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ = pointFibreToFamily sY π To t :=
  pullback.lift_fst _ _ _

section AnalyticInputs

/-- The structure morphism of a Zariski-open `T°` of the curve `T` of a local setting is locally of
finite type, quasi-compact and separated. -/
private theorem curveOpen_structure {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (Θ : QDivisor Y) (T : IrreducibleCloseds Y)
    (π : Yt ⟶ Y) (hS : IsLocalSetting sY Θ T π) (To : (curveScheme T).Opens) :
    LocallyOfFiniteType (To.ι ≫ curveι T ≫ sY) ∧ QuasiCompact (To.ι ≫ curveι T ≫ sY) ∧
      IsSeparated (To.ι ≫ curveι T ≫ sY) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  haveI : CompactSpace (curveScheme T) :=
    QuasiCompact.compactSpace_of_compactSpace (curveι T ≫ sY)
  haveI : IsNoetherian (curveScheme T) := ⟨⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end AnalyticInputs

/-! ### The sheet classes form a flat family over the cover -/

section SheetFamily

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}
  {To : (curveScheme T).Opens} {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}

/-- The point `φ(u') ∈ T°(ℂ)` under a point `u' ∈ T'(ℂ)`. -/
private abbrev coverPt (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    ComplexPoints (To.ι ≫ curveι T ≫ sY) :=
  analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl u'

/-- The sheet `F_{φ(u')} × {u'} ⟶ 𝓕' = 𝓕 ×_{T°} T'` through a point `u' ∈ T'(ℂ)`. -/
private abbrev sheetAt (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    pointFibre sY π To (coverPt u') ⟶ pullback (pullback.snd π (To.ι ≫ curveι T)) φ :=
  sheetι (t := coverPt u') ⟨u', rfl⟩

private theorem sheetAt_fst_fst (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    sheetAt π u' ≫ pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T) =
      pointFibreFst sY π To (coverPt u') := by
  rw [← Category.assoc, sheetι_comp_fst]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem sheetAt_snd (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    sheetAt π u' ≫ pullback.snd _ φ = pointFibreSnd sY π To (coverPt u') ≫ u'.hom :=
  pullback.lift_snd _ _ _

private theorem fam_comm (π : Yt ⟶ Y) :
    (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ ≫ pullback.fst π (To.ι ≫ curveι T)) ≫ π =
      pullback.snd _ φ ≫ φ ≫ To.ι ≫ curveι T := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]

/-- The fibre `F_{φ(u')}` is the fibre of `𝓕' ⟶ T'` over `u'`, through the sheet at `u'`. -/
private theorem isPullback_sheetAt (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    IsPullback (sheetAt π u') (pointFibreSnd sY π To (coverPt u'))
      (pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ) u'.hom := by
  have t := (IsPullback.of_hasPullback (pullback.snd π (To.ι ≫ curveι T)) φ).paste_horiz
    (IsPullback.of_hasPullback π (To.ι ≫ curveι T))
  have e2 : (coverPt u').hom ≫ To.ι ≫ curveι T = u'.hom ≫ φ ≫ To.ι ≫ curveι T :=
    Category.assoc _ _ _
  have s : IsPullback (sheetAt π u' ≫ pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T))
      (pointFibreSnd sY π To (coverPt u')) π (u'.hom ≫ φ ≫ To.ι ≫ curveι T) := by
    rw [sheetAt_fst_fst, ← e2]
    exact IsPullback.of_hasPullback _ _
  exact s.of_right (sheetAt_snd π u') t

private theorem sheetAt_w (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    sheetAt π u' ≫ pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ ≫
      φ ≫ To.ι ≫ curveι T ≫ sY = pointFibreSnd sY π To (coverPt u') :=
  fibreIncl_w _ _ u' _ _ (isPullback_sheetAt π u').w

/-- The class `c₁(𝓛') ∈ H²(𝓕'(ℂ); ℚ)`. -/
private def famClass (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0}))
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L'] :
    rationalCohomology (analyticSpace (pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ ≫
      φ ≫ To.ι ≫ curveι T ≫ sY)) 2 :=
  letI : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Over (Spec (.of ℂ)) :=
    ⟨pullback.snd _ φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY⟩
  singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L')

/-- The class of `𝓛'` restricts on each sheet to the class of the restriction of `𝓛'`. -/
private theorem rationalCohomologyMap_famClass (π : Yt ⟶ Y)
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L']
    (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    (rationalCohomologyMap (analyticMap (sheetAt π u') (sheetAt_w π u')) 2).hom
        (famClass π φ L') =
      pointFibreChernClass sY π To (coverPt u')
        ((Scheme.Modules.pullback (sheetAt π u')).obj L') := by
  letI : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Over (Spec (.of ℂ)) :=
    ⟨pullback.snd _ φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY⟩
  unfold pointFibreChernClass
  rw [algebraicFirstChernClass_pullback (sheetAt π u')
    (analyticMap (sheetAt π u') (sheetAt_w π u')) (fun _ => rfl) L']
  exact (mapCoeff_rationalCohomologyMap _ 2 _).symm

/-- The germ in `𝒲_u` of a class on `π⁻¹(V)`, for `V ∋ u`. -/
private abbrev germOf (π : Yt ⟶ Y) (u : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To u ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    resolutionLocalSystemFibre sY π To u :=
  (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2) u).hom
    ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)

/-- The germ of a class is the germ of the section of `𝒲` it defines. -/
private theorem germOf_eq_germ (π : Yt ⟶ Y) {V : Opens (analyticSpace sY)}
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2)
    (u : ComplexPoints (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To u ∈ V) :
    germOf π u hV α = ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).germ
      ((Opens.map (curveOpenInclusion sY To)).obj V) u hV
      (unitSec (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
        (((CategoryTheory.toSheafify _ (directImagePresheaf (resolutionAnalyticMap sY π) 2)).app
          (op V)).hom α)) := by
  have h1 : (higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α =
      ((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY π 2)).germ V _ hV
        (((CategoryTheory.toSheafify _
          (directImagePresheaf (resolutionAnalyticMap sY π) 2)).app (op V)).hom α) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply
      (F := directImagePresheaf (resolutionAnalyticMap sY π) 2) V _ hV
      (CategoryTheory.toSheafify _ (directImagePresheaf (resolutionAnalyticMap sY π) 2)) α
  exact (congrArg (stalkToPullbackStalk (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY π 2) u).hom h1).trans
    (stalkToPullbackStalk_germ (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY π 2) (((CategoryTheory.toSheafify _
      (directImagePresheaf (resolutionAnalyticMap sY π) 2)).app (op V)).hom α) u hV)

/-- The family `𝓕' = 𝓕 ×_{T°} T' ⟶ T'`. -/
private abbrev famMap (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) :
    pullback (pullback.snd π (To.ι ≫ curveι T)) φ ⟶ T' :=
  pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ

/-- The inverse image in `T'(ℂ)` of an open `V ⊆ Y(ℂ)`. -/
private abbrev coverOpen (φ : T' ⟶ (To : Scheme.{0})) (V : Opens (analyticSpace sY)) :
    Opens (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY)) :=
  (Opens.map (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl ≫ curveOpenInclusion sY To)).obj V

private theorem famToRes_w (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) :
    (pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T)) ≫ π ≫ sY =
      famMap π φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY := by
  rw [← Category.assoc _ π sY, fam_comm]
  simp only [Category.assoc]

/-- The realization `𝓕'(ℂ) ⟶ Ỹ(ℂ)` of `𝓕' ⟶ Ỹ`. -/
private abbrev famToResolution (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) :
    analyticSpace (famMap π φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY) ⟶ analyticSpace (π ≫ sY) :=
  analyticMap (pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T)) (famToRes_w π φ)

private theorem famToResolution_mem (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0}))
    (V : Opens (analyticSpace sY))
    (x : preimageSpace (analyticMap (famMap π φ) (sY := φ ≫ To.ι ≫ curveι T ≫ sY) rfl)
      (coverOpen φ V)) :
    famToResolution π φ x.1 ∈ resolutionAnalyticMap sY π ⁻¹' (V : Set (analyticSpace sY)) := by
  have e : resolutionAnalyticMap sY π (famToResolution π φ x.1) =
      curveOpenInclusion sY To (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl
        (analyticMap (famMap π φ) (sY := φ ≫ To.ι ≫ curveι T ≫ sY) rfl x.1)) := by
    ext1
    change (x.1.hom ≫ (pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T))) ≫ π =
      ((x.1.hom ≫ famMap π φ) ≫ φ) ≫ To.ι ≫ curveι T
    rw [Category.assoc, fam_comm]
    simp only [Category.assoc]
  rw [Set.mem_preimage, e]
  exact x.2

/-- The map `𝓕'(ℂ) ⊇ f'⁻¹(O) ⟶ π⁻¹(V)` induced by `𝓕' ⟶ Ỹ`, `O` the inverse image of `V`. -/
private def famToRes (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) (V : Opens (analyticSpace sY)) :
    preimageSpace (analyticMap (famMap π φ) (sY := φ ≫ To.ι ≫ curveι T ≫ sY) rfl)
      (coverOpen φ V) ⟶ preimageSpace (resolutionAnalyticMap sY π) V :=
  TopCat.ofHom ⟨fun x => ⟨famToResolution π φ x.1, famToResolution_mem π φ V x⟩,
    ((famToResolution π φ).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The inclusion `f'⁻¹(O) ⟶ 𝓕'(ℂ)`. -/
private def famIncl (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) (V : Opens (analyticSpace sY)) :
    preimageSpace (analyticMap (famMap π φ) (sY := φ ≫ To.ι ≫ curveι T ≫ sY) rfl)
      (coverOpen φ V) ⟶ analyticSpace (famMap π φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- **Local flatness of the sheet classes.** Near every point `u₀ ∈ T'(ℂ)` the classes of the
restrictions of `𝓛'` to the sheets are the restrictions of one class on a neighbourhood of the
fibre in `Ỹ(ℂ)`: a class realizing the sheet class at `u₀` (proper base change for `π`) and the
class of `𝓛'` agree on `F_{u₀}`, hence (proper base change for `𝓕' ⟶ T'`) on the part of `𝓕'` over
a neighbourhood of `u₀`. -/
private theorem exists_local_class (π : Yt ⟶ Y) [IsProper π] [LocallyOfFiniteType sY]
    [IsSeparated sY] [IsProper (famMap π φ)]
    [LocallyOfFiniteType (φ ≫ To.ι ≫ curveι T ≫ sY)] [IsSeparated (φ ≫ To.ι ≫ curveι T ≫ sY)]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L']
    (u₀ : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    ∃ (V : Opens (analyticSpace sY))
      (β : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2)
      (N : Opens (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY))) (hN : N ≤ coverOpen φ V), u₀ ∈ N ∧
      ∀ u' (hu' : u' ∈ N), (rationalCohomologyMap (pointFibreInclusion sY π To (coverPt u')
          (hN hu')) 2).hom β =
        pointFibreChernClass sY π To (coverPt u')
          ((Scheme.Modules.pullback (sheetAt π u')).obj L') := by
  obtain ⟨V, hV, β, hβ⟩ := (fibre_comparison π sY (curveOpenInclusion sY To (coverPt u₀))
    (pointFibreFst sY π To (coverPt u₀)) (pointFibreSnd sY π To (coverPt u₀))
    (IsPullback.of_hasPullback _ _) 2).1
    (pointFibreChernClass sY π To (coverPt u₀) ((Scheme.Modules.pullback (sheetAt π u₀)).obj L'))
  have hu₀ : u₀ ∈ coverOpen φ V := hV
  let δ := (rationalCohomologyMap (famToRes π φ V) 2).hom β -
    (rationalCohomologyMap (famIncl π φ V) 2).hom (famClass π φ L')
  have key : ∀ u' (hu' : u' ∈ coverOpen φ V),
      (rationalCohomologyMap (fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu')
          2).hom δ =
      (rationalCohomologyMap (pointFibreInclusion sY π To (coverPt u') hu') 2).hom β -
        pointFibreChernClass sY π To (coverPt u')
          ((Scheme.Modules.pullback (sheetAt π u')).obj L') := by
    intro u' hu'
    have e1 : fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu' ≫
          famToRes π φ V = pointFibreInclusion sY π To (coverPt u') hu' := by
      ext x
      change x.hom ≫ sheetAt π u' ≫ pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T) =
        x.hom ≫ pointFibreFst sY π To (coverPt u')
      rw [sheetAt_fst_fst]
    have e2 : fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu' ≫
          famIncl π φ V = analyticMap (sheetAt π u') (sheetAt_w π u') := rfl
    have k1 := congrArg (fun m => (rationalCohomologyMap m 2).hom β) e1
    have k2 := congrArg (fun m => (rationalCohomologyMap m 2).hom (famClass π φ L')) e2
    simp only [rationalCohomologyMap_comp, ModuleCat.comp_apply] at k2
    rw [rationalCohomologyMap_famClass] at k2
    refine (map_sub _ _ _).trans (congrArg₂ (· - ·) ?_ k2)
    refine Eq.trans ?_ k1
    exact (congrArg (fun m : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2 ⟶
        rationalCohomology (analyticSpace (pointFibreSnd sY π To (coverPt u'))) 2 => m.hom β)
      (rationalCohomologyMap_comp (fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu')
        (famToRes π φ V) 2)).symm
  obtain ⟨W, hWV, hW0, hz⟩ := (fibre_comparison (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u₀
    (sheetAt π u₀) (pointFibreSnd sY π To (coverPt u₀)) (isPullback_sheetAt π u₀) 2).2
      (coverOpen φ V) hu₀ δ ((key u₀ hu₀).trans (sub_eq_zero.2 hβ))
  refine ⟨V, β, W, hWV, hW0, fun u' hu' => ?_⟩
  have e3 : fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
      (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w (hWV hu') =
      fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu' ≫
          preimageInclusion _ hWV := rfl
  have hz' : (rationalCohomologyMap (fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
      (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w
        (hWV hu')) 2).hom δ = 0 := by
    rw [e3, rationalCohomologyMap_comp, ModuleCat.comp_apply, hz, map_zero]
  exact sub_eq_zero.1 ((key u' (hWV hu')).symm.trans hz')

/-- **The flat family of sheet classes.** The germs in `𝒲` realizing the classes of `𝓛'` on the
sheets through the points of `T'(ℂ)` form a family along `T'(ℂ) ⟶ T°(ℂ)` which is locally given by
sections of `𝒲`. -/
private theorem exists_flat_family (π : Yt ⟶ Y) [IsProper π] [LocallyOfFiniteType sY]
    [IsSeparated sY] [IsProper (famMap π φ)]
    [LocallyOfFiniteType (φ ≫ To.ι ≫ curveι T ≫ sY)] [IsSeparated (φ ≫ To.ι ≫ curveι T ≫ sY)]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L'] :
    ∃ Ef : ∀ u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY),
        resolutionLocalSystemFibre sY π To (coverPt u'),
      (∀ u', IsRealized (sY := sY) (π := π) (To := To) (t := coverPt u')
        (pointFibreChernClass sY π To (coverPt u')
          ((Scheme.Modules.pullback (sheetAt π u')).obj L')) (Ef u')) ∧
      ∀ e₀, ∃ (W : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY)))
        (r : ToType (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).obj (op W)))
        (N : Opens (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY))) (_ : e₀ ∈ N)
        (hNW : N ≤ (Opens.map (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl)).obj W),
        ∀ e (he : e ∈ N), Ef e =
          ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).germ W
            (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl e) (hNW he) r := by
  have hex : ∀ u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY), ∃ y,
      IsRealized (sY := sY) (π := π) (To := To) (t := coverPt u')
        (pointFibreChernClass sY π To (coverPt u')
          ((Scheme.Modules.pullback (sheetAt π u')).obj L')) y := by
    intro u'
    obtain ⟨V, hV, α, hα⟩ := (fibre_comparison π sY (curveOpenInclusion sY To (coverPt u'))
      (pointFibreFst sY π To (coverPt u')) (pointFibreSnd sY π To (coverPt u'))
      (IsPullback.of_hasPullback _ _) 2).1 (pointFibreChernClass sY π To (coverPt u')
        ((Scheme.Modules.pullback (sheetAt π u')).obj L'))
    exact ⟨_, V, hV, α, hα, rfl⟩
  choose Ef hEf using hex
  refine ⟨Ef, hEf, fun e₀ => ?_⟩
  obtain ⟨V, β, N, hN, he₀, hloc⟩ := exists_local_class π L' e₀
  refine ⟨(Opens.map (curveOpenInclusion sY To)).obj V,
    unitSec (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
      (((CategoryTheory.toSheafify _ (directImagePresheaf (resolutionAnalyticMap sY π) 2)).app
        (op V)).hom β), N, he₀, hN, fun e he => ?_⟩
  exact ((hEf e).unique ⟨V, hN he, β, hloc e he, rfl⟩).trans (germOf_eq_germ π β _ (hN he))

private theorem isRealized_transport {π : Yt ⟶ Y}
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L']
    {u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)}
    {y : resolutionLocalSystemFibre sY π To (coverPt u')}
    (hy : IsRealized (sY := sY) (π := π) (To := To) (t := coverPt u')
      (pointFibreChernClass sY π To (coverPt u')
        ((Scheme.Modules.pullback (sheetAt π u')).obj L')) y)
    {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)} (h : coverPt u' = t) (h' : u'.hom ≫ φ = t.hom) :
    IsRealized (sY := sY) (π := π) (To := To) (t := t)
      (pointFibreChernClass sY π To t ((Scheme.Modules.pullback (sheetι (π := π) ⟨u', h'⟩)).obj L'))
      ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
        (.of_eq h)).hom.hom y) := by
  subst h
  rw [stalkCongr_self]
  exact hy

private theorem stalkCongr_congr_point {Z E : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)
    (p : E ⟶ Z) (Ef : ∀ e : E, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (p e)))
    {e₁ e₂ : E} (he : e₁ = e₂) {t : Z} (h₁ : p e₁ = t) (h₂ : p e₂ = t) :
    (((TopCat.Sheaf.forget _ Z).obj F).stalkCongr (.of_eq h₁)).hom.hom (Ef e₁) =
      (((TopCat.Sheaf.forget _ Z).obj F).stalkCongr (.of_eq h₂)).hom.hom (Ef e₂) := by
  subst he
  rfl

end SheetFamily

/-! ### Parallel transport as a graph -/

section TransportGraph

/-- `stalkPushforward` is natural in the presheaf. -/
private lemma stalkPushforward_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F G : TopCat.Presheaf (ModuleCat.{0} ℚ) X} (g : F ⟶ G) (x : X) :
    TopCat.Presheaf.stalkPushforward _ f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map g =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map g) ≫
        TopCat.Presheaf.stalkPushforward _ f G x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
  rfl

variable {V : TopCat.{0}} (E : ModuleCat.{0} ℚ)

/-- The constant section `e` of the constant sheaf with value `E`. -/
private def constSection (e : E) :
    ToType (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).obj (op ⊤)) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology V)
    ((Functor.const (Opens V)ᵒᵖ).obj E)).app (op ⊤)).hom e

/-- Every germ of a constant sheaf is the germ of a constant section. -/
private theorem constantSheaf_exists_constSection_germ (p : V)
    (c : ToType (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ
          ⊤ p (Opens.mem_top p) (constSection E e) = c := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) V := (Functor.const (Opens V)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K))).2 c
  obtain ⟨U, hU, e, rfl⟩ := K.exists_germ_eq c'
  refine ⟨e, ?_⟩
  have this : K.germ U p hU e = K.germ ⊤ p (Opens.mem_top p) e :=
    TopCat.Presheaf.germ_res_apply K (homOfLE (le_top : U ≤ ⊤)) p hU e
  rw [← hc', this]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K) e).symm

omit E in
/-- On a sheaf isomorphic to a constant sheaf, every germ is the germ of the global section
corresponding to a constant section. -/
private theorem exists_constSection_germ_eq_of_iso {G : TopCat.Sheaf (ModuleCat.{0} ℚ) V}
    {E : ModuleCat.{0} ℚ}
    (ψ : G ≅ (constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E) (p : V)
    (z : ToType (((TopCat.Sheaf.forget _ V).obj G).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ V).obj G).germ ⊤ p (Opens.mem_top p)
      ((((TopCat.Sheaf.forget _ V).mapIso ψ).inv.app (op ⊤)).hom (constSection E e)) = z := by
  let φ := (TopCat.Sheaf.forget _ V).mapIso ψ
  obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E p
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map φ.hom z)
  refine ⟨e, ?_⟩
  rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply, he]
  exact ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).mapIso φ).hom_inv_id_apply z

variable {M : TopCat.{0}} (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M)

/-- `v` is the parallel transport of `w` along `γ`: some global section of `γ^* 𝓛` has germ `w`
at `0` and germ `v` at `1`. -/
private def IsTransportOf {x y : M} (γ : Path x y)
    (w : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x)
    (v : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y) : Prop :=
  ∃ s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
      (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛).obj.obj (op ⊤)),
    (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap) 𝓛 0).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.source.symm)).hom.hom w) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛)).germ
          ⊤ 0 trivial).hom s ∧
    (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap) 𝓛 1).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.target.symm)).hom.hom v) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛)).germ
          ⊤ 1 trivial).hom s

/-- The stalk map along an equality of points is a cast. -/
private theorem stalkCongr_eq_cast {a b : M} (h : a = b)
    (x : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk a)
    (e : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk a) =
      ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk b)) :
    (((TopCat.Sheaf.forget _ M).obj 𝓛).stalkCongr (.of_eq h)).hom.hom x = cast e x := by
  subst h
  rw [stalkCongr_self]
  rfl

/-- **Parallel transport.** A local system on a locally path connected space has a transport
`T_γ : 𝓛_x ≅ 𝓛_y` on homotopy classes of paths, compatible with concatenation, whose graph is
the transport relation `MMP.Fourfold.IsTransportOf`. -/
private theorem exists_transport [LocallyPathConnectedSpace M] (h𝓛 : IsLocalSystem 𝓛) :
    ∃ Tr : ∀ {x y : M}, Path.Homotopic.Quotient x y →
        (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x ≅ ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y),
      (∀ {x y : M} (γ : Path x y) w v,
        IsTransportOf 𝓛 γ w v ↔ (Tr (Path.Homotopic.Quotient.mk γ)).hom w = v) ∧
      (∀ {x y z : M} (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z),
        Tr (γ.trans δ) = Tr γ ≪≫ Tr δ) := by
  refine ⟨h𝓛.parallelTransport, fun {x y} γ w v => ?_, h𝓛.parallelTransport_trans⟩
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  haveI := isIso_stalkToPullbackStalk Γ 𝓛 1
  have hinj : Function.Injective (stalkToPullbackStalk Γ 𝓛 1).hom :=
    (ConcreteCategory.bijective_of_isIso (stalkToPullbackStalk Γ 𝓛 1)).1
  constructor
  · rintro ⟨s, h0, h1⟩
    have h1' := h𝓛.parallelTransport_germ γ s w
      (by rwa [← stalkCongr_eq_cast 𝓛 γ.source.symm])
    rw [← stalkCongr_eq_cast 𝓛 γ.target.symm] at h1'
    exact (((TopCat.Sheaf.forget _ M).obj 𝓛).stalkCongr
      (.of_eq γ.target.symm)).toLinearEquiv.injective (hinj (h1'.trans h1.symm))
  · rintro rfl
    obtain ⟨ψ⟩ := h𝓛.nonempty_pullback_path_iso_constantSheaf γ
    obtain ⟨e, hs⟩ := exists_constSection_germ_eq_of_iso ψ 0
      ((stalkToPullbackStalk Γ 𝓛 0).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.source.symm)).hom.hom w))
    set s := ((((TopCat.Sheaf.forget _ _).mapIso ψ).inv.app (op ⊤)).hom
      (constSection (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x) e))
    refine ⟨s, hs.symm, ?_⟩
    have h1' := h𝓛.parallelTransport_germ γ s w
      (by rwa [← stalkCongr_eq_cast 𝓛 γ.source.symm, eq_comm])
    rwa [← stalkCongr_eq_cast 𝓛 γ.target.symm] at h1'

end TransportGraph

/-! ### Consequences of functoriality, and transport along lifts -/

section TransportAlgebra

variable {M : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}
  {Tr : ∀ {x y : M}, Path.Homotopic.Quotient x y →
    (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x ≅ ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y)}

/-- A functorial transport is trivial along constant paths. -/
private theorem tr_refl
    (htrans : ∀ {x y z : M} (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z),
      Tr (γ.trans δ) = Tr γ ≪≫ Tr δ) (x : M) :
    Tr (Path.Homotopic.Quotient.refl x) = Iso.refl _ := by
  have h := congrArg Iso.hom (htrans (Path.Homotopic.Quotient.refl x)
    (Path.Homotopic.Quotient.refl x))
  rw [Path.Homotopic.Quotient.refl_trans, Iso.trans_hom] at h
  ext1
  have h2 := congrArg (· ≫ (Tr (Path.Homotopic.Quotient.refl x)).inv) h
  simp only [Iso.hom_inv_id, Category.assoc, Category.comp_id] at h2
  exact h2.symm

/-- A functorial transport inverts along reversed paths. -/
private theorem tr_symm
    (htrans : ∀ {x y z : M} (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z),
      Tr (γ.trans δ) = Tr γ ≪≫ Tr δ) {x y : M} (γ : Path.Homotopic.Quotient x y) :
    Tr γ.symm = (Tr γ).symm := by
  have h := congrArg Iso.hom (htrans γ γ.symm)
  rw [Path.Homotopic.Quotient.trans_symm, tr_refl htrans, Iso.trans_hom, Iso.refl_hom] at h
  ext1
  calc (Tr γ.symm).hom = (Tr γ).inv ≫ ((Tr γ).hom ≫ (Tr γ.symm).hom) := by simp
    _ = _ := by
      rw [← h]
      simp

/-- Transport along a loop is conjugate to transport along the conjugated loop. -/
private theorem tr_eq_conj
    (htrans : ∀ {x y z : M} (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z),
      Tr (γ.trans δ) = Tr γ ≪≫ Tr δ) {x y : M} (q : Path.Homotopic.Quotient x x)
    (δ : Path.Homotopic.Quotient x y) :
    Tr q = Tr δ ≪≫ Tr (δ.symm.trans (q.trans δ)) ≪≫ (Tr δ).symm := by
  rw [htrans, htrans, tr_symm htrans]
  ext1
  simp

end TransportAlgebra

section TransportLift

variable {M : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}

/-- **Transport along a lifted path.** Let `p : E ⟶ M` be continuous and `Ef` a family of germs
of `𝓛` along `p` which is locally given by sections of `𝓛`. Along a path `γ` lifted by `Γ'`, the
value of `Ef` at the start of `Γ'` is transported to its value at the end. -/
private theorem isTransportOf_of_lift {E : TopCat.{0}} {p : E ⟶ M}
    (Ef : ∀ e : E, ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk (p e)))
    (hEf : ∀ e₀, ∃ (W : Opens M) (r : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).obj (op W)))
      (N : Opens E) (_ : e₀ ∈ N) (hNW : N ≤ (Opens.map p).obj W), ∀ e (he : e ∈ N),
        Ef e = ((TopCat.Sheaf.forget _ M).obj 𝓛).germ W (p e) (hNW he) r)
    {x y : M} (γ : Path x y) (Γ' : C(unitInterval, E)) (hΓ' : ∀ s, p (Γ' s) = γ s)
    (h0 : p (Γ' 0) = x) (h1 : p (Γ' 1) = y) :
    IsTransportOf 𝓛 γ
      ((((TopCat.Sheaf.forget _ M).obj 𝓛).stalkCongr (.of_eq h0)).hom.hom (Ef (Γ' 0)))
      ((((TopCat.Sheaf.forget _ M).obj 𝓛).stalkCongr (.of_eq h1)).hom.hom (Ef (Γ' 1))) := by
  let PF := (TopCat.Sheaf.forget _ M).obj 𝓛
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let Y : ∀ s : unitInterval, ToType (PF.stalk (Γ s)) := fun s =>
    (PF.stalkCongr (.of_eq (hΓ' s))).hom.hom (Ef (Γ' s))
  obtain ⟨s, hs⟩ := exists_section_of_local Γ 𝓛 Y (fun x₀ => by
    obtain ⟨W, r, N, hN, hNW, hloc⟩ := hEf (Γ' x₀)
    refine ⟨W, r, ⟨Γ' ⁻¹' N, N.isOpen.preimage Γ'.continuous⟩, hN, fun x hx => ?_,
      fun x hx => ?_⟩
    · change γ x ∈ W
      rw [← hΓ' x]
      exact hNW hx
    · change (PF.stalkCongr _).hom.hom (Ef (Γ' x)) = _
      rw [hloc (Γ' x) hx]
      exact stalkCongr_germ PF _ _ _ r)
  refine ⟨s, ?_, ?_⟩
  · rw [stalkCongr_stalkCongr]
    exact (hs 0).symm
  · rw [stalkCongr_stalkCongr]
    exact (hs 1).symm

end TransportLift

/-! ### Linear combinations of realized classes -/

section RealizedLinear

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
  {To : (curveScheme T).Opens} {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)}

/-- Every germ of `𝒲` at `t` is the germ of a class on the preimage of a neighbourhood. -/
private theorem exists_germOf_eq (w : resolutionLocalSystemFibre sY π To t) :
    ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2),
      (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
        t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α) = w := by
  haveI := isIso_stalkToPullbackStalk (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY π 2) t
  obtain ⟨w', rfl⟩ := (ConcreteCategory.bijective_of_isIso (stalkToPullbackStalk
    (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2) t)).2 w
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso
    (curveOpenInclusion sY To t) (ModuleCat.{0} ℚ)
    (directImagePresheaf (resolutionAnalyticMap sY π) 2)
  obtain ⟨w'', rfl⟩ := (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor
    (ModuleCat.{0} ℚ) (curveOpenInclusion sY To t)).map (CategoryTheory.toSheafify
      (Opens.grothendieckTopology _) (directImagePresheaf (resolutionAnalyticMap sY π) 2)))).2 w'
  obtain ⟨V, hV, α, rfl⟩ := (directImagePresheaf (resolutionAnalyticMap sY π) 2).exists_germ_eq w''
  exact ⟨V, hV, α, rfl⟩

end RealizedLinear

/-! ### Complex points of a smooth curve avoiding countably many proper closed subsets -/

section GoodPoint

open MMP.Analytic

/-- In a neighbourhood homeomorphic to the ball of an avoidance chart, with `S` corresponding to
the complement of the excluded set, every open set meeting the neighbourhood meets `S`. -/
private theorem exists_mem_inter_of_avoidanceChart {X : Type*} [TopologicalSpace X] (S : Set X)
    {W : Set X} {n : ℕ}
    (C : MMP.Fourfold.AnalyticAvoidanceChart n) (e : W ≃ₜ C.ball)
    (hS : ∀ w : W, (w : X) ∈ S ↔ (e w : EuclideanSpace ℂ (Fin n)) ∉ C.excludedSet)
    {x : X} (hx : x ∈ W) {O : Set X} (hO : IsOpen O) (hxO : x ∈ O) : ∃ s ∈ S, s ∈ O := by
  set g : C.ball → X := fun y => (e.symm y : X)
  have hg : Continuous g := continuous_subtype_val.comp e.symm.continuous
  set y0 := e ⟨x, hx⟩
  have hgy0 : g y0 = x := by simp [g, y0]
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 (hO.preimage hg)
  have hy0t : (y0 : EuclideanSpace ℂ (Fin n)) ∈ t := by
    have : y0 ∈ g ⁻¹' O := by rwa [Set.mem_preimage, hgy0]
    rwa [← hte] at this
  obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 (ht.inter C.isOpen_ball) _ ⟨hy0t, y0.2⟩
  have hcl : (y0 : EuclideanSpace ℂ (Fin n)) ∈ closure (C.ball \ C.excludedSet) :=
    MMP.Fourfold.AnalyticAvoidanceChart.ball_subset_closure_ball_diff_excludedSet C y0.2
  obtain ⟨z, hz, hdz⟩ := (@Metric.mem_closure_iff (EuclideanSpace ℂ (Fin n)) _ _ _).1 hcl ε hε
  have hzb : z ∈ Metric.ball (y0 : EuclideanSpace ℂ (Fin n)) ε := by
    rwa [Metric.mem_ball, dist_comm]
  refine ⟨g ⟨z, hz.1⟩, (hS (e.symm ⟨z, hz.1⟩)).2 (by simpa using hz.2), ?_⟩
  have : (⟨z, hz.1⟩ : C.ball) ∈ Subtype.val ⁻¹' t := (hεt hzb).1
  rwa [hte] at this

/-- For a dense open `U` of a smooth complex variety `V`, the complex points over `U` form a dense
open subset of `V(ℂ)`. -/
private theorem isOpen_dense_setOf_toScheme_mem {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (hV : MMP.Mori.IsVariety ℂ sV) [Smooth sV] (U : V.Opens) (hU : Dense (U : Set V)) :
    IsOpen {x : ComplexPoints sV | x.toScheme ∈ U} ∧
      Dense {x : ComplexPoints sV | x.toScheme ∈ U} := by
  obtain ⟨hemb, hrange⟩ := isOpenEmbedding_realize_ι_and_range sV hV U
  refine ⟨hrange ▸ hemb.isOpen_range, ?_⟩
  rw [dense_iff_inter_open]
  rintro O hO ⟨x, hxO⟩
  obtain ⟨W, n, C, e, -, hxW, hiff⟩ :=
    MMP.Analytic.exists_analyticAvoidanceChart_of_dense sV hV U hU x
  obtain ⟨s, hs, hsO⟩ := exists_mem_inter_of_avoidanceChart {x : ComplexPoints sV | x.toScheme ∈ U}
    C e (fun w => (not_iff_comm.1 (hiff w)).symm) hxW hO hxO
  exact ⟨s, hsO, hs⟩

/-- **A very general complex point.** On a smooth complex variety `V` with a complex point, there
is a complex point outside any countable union of proper closed subsets. -/
private theorem exists_complexPoint_notMem_sUnion {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (hV : MMP.Mori.IsVariety ℂ sV) [Smooth sV] (t : ComplexPoints sV)
    (Ω : Set (Set V)) (hΩ : Ω.Countable) (hΩc : ∀ Z ∈ Ω, IsClosed Z ∧ Z ≠ Set.univ) :
    ∃ t₀ : ComplexPoints sV, t₀.hom.base default ∉ ⋃₀ Ω := by
  haveI := hV.toIsIntegral
  haveI := hV.toLocallyOfFiniteType
  haveI := hV.toQuasiCompact
  haveI := hV.toIsSeparated
  haveI : T2Space (ComplexPoints sV) := ComplexPoints.t2Space_of_locallyOfFiniteType
  haveI : BaireSpace (ComplexPoints sV) := BaireSpace.of_t2Space_locallyCompactSpace
  let U : ∀ Z ∈ Ω, V.Opens := fun Z hZ => ⟨Zᶜ, (hΩc Z hZ).1.isOpen_compl⟩
  have hU : ∀ Z (hZ : Z ∈ Ω), Dense ((U Z hZ : V.Opens) : Set V) := fun Z hZ =>
    (hΩc Z hZ).1.isOpen_compl.dense (Set.nonempty_compl.2 (hΩc Z hZ).2)
  let A : Set V → Set (ComplexPoints sV) := fun Z => {x | x.toScheme ∉ Z}
  have hA : ∀ Z (hZ : Z ∈ Ω), A Z = {x : ComplexPoints sV | x.toScheme ∈ U Z hZ} :=
    fun _ _ => rfl
  have hd : Dense (⋂ Z ∈ Ω, A Z) := dense_biInter_of_isOpen
    (fun Z hZ => hA Z hZ ▸ (isOpen_dense_setOf_toScheme_mem sV hV _ (hU Z hZ)).1) hΩ
    (fun Z hZ => hA Z hZ ▸ (isOpen_dense_setOf_toScheme_mem sV hV _ (hU Z hZ)).2)
  haveI : Nonempty (ComplexPoints sV) := ⟨t⟩
  obtain ⟨t₀, ht₀⟩ := hd.nonempty
  refine ⟨t₀, fun h => ?_⟩
  obtain ⟨Z, hZ, hmem⟩ := Set.mem_sUnion.1 h
  exact Set.mem_iInter₂.1 ht₀ Z hZ hmem

end GoodPoint

/-! ### Finiteness of fibres and of stalks -/

section Finiteness

/-- The fibre of the realization of a finite morphism over a complex point is finite. -/
private theorem finite_fibre_realize {X B : Scheme.{0}} {sB : B ⟶ Spec (.of ℂ)}
    {sX : X ⟶ Spec (.of ℂ)} (φ : X ⟶ B) [IsFinite φ] (hφ : φ ≫ sB = sX) (b : ComplexPoints sB) :
    Finite {e : ComplexPoints sX // ComplexPoints.realize φ hφ e = b} := by
  haveI := finite_sections (pullback.fst b.hom φ)
  have hw : ∀ e : {e : ComplexPoints sX // ComplexPoints.realize φ hφ e = b},
      𝟙 _ ≫ b.hom = e.1.hom ≫ φ := fun e => by
    rw [Category.id_comp, ← ComplexPoints.realize_hom φ hφ e.1, e.2]
  refine Finite.of_injective
    (fun e ↦ (⟨pullback.lift (𝟙 _) e.1.hom (hw e), pullback.lift_fst _ _ _⟩ :
      {σ : Spec (.of ℂ) ⟶ pullback b.hom φ // σ ≫ pullback.fst b.hom φ = 𝟙 _})) ?_
  intro a c hac
  have := congrArg (fun σ ↦ σ.1 ≫ pullback.snd b.hom φ) hac
  simp only [pullback.lift_snd] at this
  exact Subtype.ext (ComplexPoints.ext this)

/-- The stalks of a local system are finite-dimensional. -/
private theorem finiteDimensional_stalk_of_isLocalSystem {M : TopCat.{0}}
    {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (h𝓛 : IsLocalSystem 𝓛) (x : M) :
    FiniteDimensional ℚ (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x) := by
  obtain ⟨V, hxV, E, hE, ⟨ψ⟩⟩ := h𝓛 x
  haveI := hE
  let p : (Opens.toTopCat M).obj V := ⟨x, hxV⟩
  haveI := isIso_stalkToPullbackStalk V.inclusion' 𝓛 p
  let G := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) V.inclusion').obj 𝓛
  let L : E →ₗ[ℚ] ((TopCat.Sheaf.forget _ _).obj G).stalk p :=
    (((TopCat.Sheaf.forget _ _).obj G).germ ⊤ p (Opens.mem_top p)).hom.comp
      (((((TopCat.Sheaf.forget _ _).mapIso ψ).inv.app (op ⊤)).hom).comp
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology ((Opens.toTopCat M).obj V))
          ((Functor.const (Opens ((Opens.toTopCat M).obj V))ᵒᵖ).obj E)).app (op ⊤)).hom)
  have hL : Function.Surjective L := fun z => exists_constSection_germ_eq_of_iso ψ p z
  haveI : Module.Finite ℚ (((TopCat.Sheaf.forget _ _).obj G).stalk p) :=
    Module.Finite.of_surjective L hL
  exact Module.Finite.equiv (asIso (stalkToPullbackStalk V.inclusion' 𝓛 p)).toLinearEquiv.symm

end Finiteness

/-! ### First Chern classes span the second cohomology of `F_t` -/

section Spanning

open MMP.Analytic

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- A `ℂ`-point `x` of a scheme over `ℂ` factors through `Spec κ(y)`, `y` its image, by an
isomorphism `Spec ℂ ≅ Spec κ(y)`. -/
private theorem isIso_SpecToEquivOfField_snd {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (x : Spec (.of ℂ) ⟶ X) (hx : x ≫ sX = 𝟙 _) :
    IsIso ((Scheme.SpecToEquivOfField ℂ X x).2) := by
  set σ := Scheme.SpecToEquivOfField ℂ X x
  have hfac : Spec.map σ.2 ≫ X.fromSpecResidueField σ.1 = x :=
    (Scheme.SpecToEquivOfField ℂ X).symm_apply_apply x
  set ψ := Spec.preimage (X.fromSpecResidueField σ.1 ≫ sX)
  have hψ : ψ ≫ σ.2 = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc, hfac, hx, Spec.map_id]
  have hsurj : Function.Surjective σ.2.hom := fun c => ⟨ψ.hom c, by
    rw [← CommRingCat.comp_apply, hψ]; rfl⟩
  have hbij : Function.Bijective σ.2.hom := ⟨σ.2.hom.injective, hsurj⟩
  exact (RingEquiv.ofBijective σ.2.hom hbij).toCommRingCatIso.isIso_hom

/-- The span of the rational first Chern classes of invertible modules is all of `H²(X; ℚ)` on
`X'` as soon as it is on an isomorphic scheme `X` over `ℂ`. -/
private theorem span_chernClass_eq_top_of_iso {X' X : Scheme.{0}} [X'.Over (Spec (.of ℂ))]
    [X.Over (Spec (.of ℂ))] (e : X' ≅ X)
    (he : e.hom ≫ (X ↘ Spec (.of ℂ)) = X' ↘ Spec (.of ℂ))
    (h : Submodule.span ℚ {c : rationalCohomology (analyticSpace (X ↘ Spec (.of ℂ))) 2 |
        ∃ (M : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M),
          singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M) = c} = ⊤) :
    Submodule.span ℚ {c : rationalCohomology (analyticSpace (X' ↘ Spec (.of ℂ))) 2 |
        ∃ (M : X'.Modules) (_ : SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2 M),
          singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M) = c} =
      ⊤ := by
  have he' : e.inv ≫ (X' ↘ Spec (.of ℂ)) = X ↘ Spec (.of ℂ) := by
    rw [← he, Iso.inv_hom_id_assoc]
  let g := analyticMap (sX := X' ↘ Spec (.of ℂ)) (sY := X ↘ Spec (.of ℂ)) e.hom he
  let ginv := analyticMap (sX := X ↘ Spec (.of ℂ)) (sY := X' ↘ Spec (.of ℂ)) e.inv he'
  have hgg : g ≫ ginv = 𝟙 _ := by
    ext p
    change (p.hom ≫ e.hom) ≫ e.inv = p.hom
    simp
  have hsurj : ∀ c, (rationalCohomologyMap g 2).hom ((rationalCohomologyMap ginv 2).hom c) = c :=
    fun c => by
      rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hgg, rationalCohomologyMap_id]
      rfl
  have hchern : ∀ (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M],
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (@algebraicFirstChernClass X' _ ((Scheme.Modules.pullback e.hom).obj M)
            (MMP.Mori.isInvertible_pullback_obj e.hom M)) =
        (rationalCohomologyMap g 2).hom
          (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M)) := by
    intro M _
    haveI := MMP.Mori.isInvertible_pullback_obj e.hom M
    rw [algebraicFirstChernClass_pullback e.hom g (fun _ => rfl) M]
    exact mapCoeff_rationalCohomologyMap g 2 (algebraicFirstChernClass M)
  rw [eq_top_iff]
  intro c _
  have hmem : (rationalCohomologyMap ginv 2).hom c ∈ Submodule.span ℚ
      {c : rationalCohomology (analyticSpace (X ↘ Spec (.of ℂ))) 2 |
        ∃ (M : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M),
          singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M) = c} := by
    rw [h]; trivial
  have hmap := Submodule.mem_map_of_mem (f := (rationalCohomologyMap g 2).hom) hmem
  rw [← Submodule.span_image, hsurj] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨c', ⟨M, hM, rfl⟩, rfl⟩
  exact ⟨_, MMP.Mori.isInvertible_pullback_obj e.hom M, hchern M⟩

/-- **First Chern classes span `H²(F_t; ℚ)`.** For a `ℂ`-point `t` of a `π`-adapted open `T°`, the
rational first Chern classes of invertible modules on the fibre `F_t` span `H²(F_t; ℚ)`. -/
private theorem span_pointFibreChernClass_eq_top (hS : IsLocalSetting sY Θ T π)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    Submodule.span ℚ {c | ∃ (M : (pointFibre sY π To t).Modules)
        (_ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
          (pointFibre sY π To t).ringCatSheaf.2 M),
        pointFibreChernClass sY π To t M = c} = ⊤ := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
  set x : Spec (.of ℂ) ⟶ Y := t.hom ≫ To.ι ≫ curveι T with hxdef
  have hxs : x ≫ sY = 𝟙 _ := by simpa only [x, Category.assoc] using t.2
  set σ := Scheme.SpecToEquivOfField ℂ Y x
  set p₀ : Spec (.of ℂ) := IsLocalRing.closedPoint ℂ
  have hσ : σ.1 = x.base p₀ := rfl
  have hfac : Spec.map σ.2 ≫ Y.fromSpecResidueField σ.1 = x :=
    (Scheme.SpecToEquivOfField ℂ Y).symm_apply_apply x
  haveI := isIso_SpecToEquivOfField_snd sY x hxs
  -- `σ.1` is a closed point
  have hy : IsClosed {σ.1} := by
    haveI : IsClosedImmersion (x ≫ sY) := by
      rw [hxs]
      infer_instance
    haveI : IsClosedImmersion x := IsClosedImmersion.of_comp x sY
    have hr : Set.range x.base = {σ.1} := by
      ext q
      constructor
      · rintro ⟨p, rfl⟩
        rw [Subsingleton.elim p p₀, hσ]
        rfl
      · rintro rfl
        exact ⟨p₀, hσ.symm⟩
    exact hr ▸ x.isClosedEmbedding.isClosed_range
  -- the fibre over `σ.1` has dimension at most two
  have hdim : topologicalKrullDim (pointSettingFibre π σ.1) ≤ 2 := by
    have h := hTo.topologicalKrullDim_fibre_le (t.hom.base p₀)
    have he : (curveι T).base (t.hom.base p₀).1 = σ.1 := by
      rw [hσ, hxdef, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact congrArg (curveι T).base (Scheme.Opens.ι_apply To _).symm
    rwa [he] at h
  letI : (pointSettingFibre π σ.1).Over (Spec (.of ℂ)) := ⟨pullback.fst π _ ≫ π ≫ sY⟩
  have key := hS.span_firstChernClass_pointSettingFibre_eq_top hy hdim
  -- the isomorphism `F_t ≅ Ỹ ×_Y Spec κ(σ.1)`
  let m : pointFibre sY π To t ⟶ pointSettingFibre π σ.1 :=
    pullback.map π x π (Y.fromSpecResidueField σ.1) (𝟙 Yt) (Spec.map σ.2) (𝟙 Y) (by simp)
      (by rw [Category.comp_id, hfac])
  haveI : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  let e : pointFibre sY π To t ≅ pointSettingFibre π σ.1 := asIso m
  have hcomp : e.hom ≫ (pointSettingFibre π σ.1 ↘ Spec (.of ℂ)) =
      pointFibre sY π To t ↘ Spec (.of ℂ) := by
    change m ≫ pullback.fst π _ ≫ π ≫ sY = _
    rw [← pointFibreFst_comp_structure]
    simp only [m, pullback.map, Category.comp_id]
    exact pullback.lift_fst_assoc _ _ _ _
  exact span_chernClass_eq_top_of_iso e hcomp key

end Spanning

/-! ### Finite monodromy -/

section Monodromy

open MMP.Analytic

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- **Realized germs span `𝒲_t`.** The germs in `𝒲_t` realizing first Chern classes of invertible
modules on `F_t` span `𝒲_t`. -/
private theorem span_isRealized_eq_top (hS : IsLocalSetting sY Θ T π)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY)) :
    Submodule.span ℚ {y : resolutionLocalSystemFibre sY π To t |
      ∃ (M : (pointFibre sY π To t).Modules)
        (_ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
          (pointFibre sY π To t).ringCatSheaf.2 M),
        IsRealized (sY := sY) (π := π) (To := To) (t := t)
          (pointFibreChernClass sY π To t M) y} = ⊤ := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hS.isResolution.2.2.2.1
  have hex : ∀ x, ∃ y, IsRealized (sY := sY) (π := π) (To := To) (t := t) x y := fun x => by
    obtain ⟨V, hV, α, hα⟩ := (fibre_comparison π sY (curveOpenInclusion sY To t)
      (pointFibreFst sY π To t) (pointFibreSnd sY π To t) (IsPullback.of_hasPullback _ _) 2).1 x
    exact ⟨_, V, hV, α, hα, rfl⟩
  have hspan : ∀ x ∈ Submodule.span ℚ {c | ∃ (M : (pointFibre sY π To t).Modules)
        (_ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
          (pointFibre sY π To t).ringCatSheaf.2 M),
        pointFibreChernClass sY π To t M = c},
      ∃ y ∈ Submodule.span ℚ {y : resolutionLocalSystemFibre sY π To t |
        ∃ (M : (pointFibre sY π To t).Modules)
          (_ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
            (pointFibre sY π To t).ringCatSheaf.2 M),
          IsRealized (sY := sY) (π := π) (To := To) (t := t)
            (pointFibreChernClass sY π To t M) y},
        IsRealized (sY := sY) (π := π) (To := To) (t := t) x y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨M, hM, rfl⟩ := hx
      obtain ⟨y, hy⟩ := hex (pointFibreChernClass sY π To t M)
      exact ⟨y, Submodule.subset_span ⟨M, hM, hy⟩, hy⟩
    | zero => exact ⟨0, zero_mem _, isRealized_zero⟩
    | add x x' _ _ ihx ihx' =>
      obtain ⟨y, hy, hxy⟩ := ihx
      obtain ⟨y', hy', hxy'⟩ := ihx'
      exact ⟨y + y', add_mem hy hy', hxy.add hxy'⟩
    | smul c x _ ih =>
      obtain ⟨y, hy, hxy⟩ := ih
      exact ⟨c • y, Submodule.smul_mem _ c hy, hxy.smul c⟩
  rw [eq_top_iff]
  intro w _
  obtain ⟨V, hV, α, rfl⟩ := exists_germOf_eq (sY := sY) (π := π) (To := To) (t := t) w
  have hw : IsRealized (sY := sY) (π := π) (To := To) (t := t)
      ((rationalCohomologyMap (pointFibreInclusion sY π To t hV) 2).hom α)
      ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
        t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)) :=
    ⟨V, hV, α, rfl, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hspan _ (by rw [span_pointFibreChernClass_eq_top hS hTo t]; trivial)
  rw [hw.unique hxy]
  exact hy

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The two components of the sheet `F_{t₁} × {t'} ⟶ 𝓕 ×_{T°} T'` agree over `T°`. -/
private theorem sheet_w {To : (curveScheme T).Opens} {T₁ : (To : Scheme.{0}).Opens}
    {T' : Scheme.{0}} {φ : T' ⟶ (T₁ : Scheme.{0})}
    {t' : ComplexPoints (φ ≫ T₁.ι ≫ To.ι ≫ curveι T ≫ sY)}
    {t₁ : ComplexPoints (To.ι ≫ curveι T ≫ sY)} (ht' : t'.hom ≫ φ ≫ T₁.ι = t₁.hom) :
    pointFibreToFamily sY π To t₁ ≫ pullback.snd π (To.ι ≫ curveι T) =
      (pointFibreSnd sY π To t₁ ≫ t'.hom) ≫ φ ≫ T₁.ι := by
  rw [Category.assoc, ht']
  exact pullback.lift_snd _ _ _

end Monodromy

/-! ### Naturality of transport under morphisms of sheaves -/

section TransportNaturality

/-- The comparison `F_{f(x)} ⟶ (f^* F)_x` is natural in the sheaf `F`. -/
private theorem stalkToPullbackStalk_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (m : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Sheaf.forget _ Y).map m) ≫
        stalkToPullbackStalk f G x =
      stalkToPullbackStalk f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map
        ((TopCat.Sheaf.forget _ X).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map m)) := by
  unfold stalkToPullbackStalk
  have h := congrArg (TopCat.Sheaf.forget _ Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.naturality m)
  rw [Functor.map_comp, Functor.map_comp] at h
  have h2 := congrArg (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) (f x)).map h
  rw [Functor.map_comp, Functor.map_comp] at h2
  have h3 := stalkPushforward_naturality f
    ((TopCat.Sheaf.forget _ X).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map m)) x
  erw [reassoc_of% h2, Category.assoc]
  exact congrArg (fun k => _ ≫ k) h3.symm

variable {M : TopCat.{0}}

/-- A morphism of sheaves carries the transport relation of its source to that of its
target. -/
private theorem IsTransportOf.map {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (m : F ⟶ G)
    {x y : M} {γ : Path x y} {w v} (h : IsTransportOf F γ w v) :
    IsTransportOf G γ
      ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ M).map m) w)
      ((TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ M).map m) v) := by
  obtain ⟨s, h0, h1⟩ := h
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let m' := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) Γ).map m
  have key : ∀ (p : unitInterval) {z : M} (hz : z = Γ p)
      (u : ((TopCat.Sheaf.forget _ M).obj F).stalk z),
      (stalkToPullbackStalk Γ G p).hom ((((TopCat.Sheaf.forget _ _).obj G).stalkCongr
          (.of_eq hz)).hom.hom
        ((TopCat.Presheaf.stalkFunctor _ z).map ((TopCat.Sheaf.forget _ M).map m) u)) =
      (TopCat.Presheaf.stalkFunctor _ p).map ((TopCat.Sheaf.forget _ _).map m')
        ((stalkToPullbackStalk Γ F p).hom ((((TopCat.Sheaf.forget _ _).obj F).stalkCongr
          (.of_eq hz)).hom.hom u)) := by
    intro p z hz u
    subst hz
    erw [stalkCongr_self, stalkCongr_self]
    exact congrArg (fun φ => φ.hom u) (stalkToPullbackStalk_naturality Γ m p)
  refine ⟨((TopCat.Sheaf.forget _ _).map m').app (op ⊤) |>.hom s, ?_, ?_⟩
  · rw [key 0 γ.source.symm, h0]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _
  · rw [key 1 γ.target.symm, h1]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _

end TransportNaturality

/-! ### Rational first Chern classes under pullback -/

section ChernPullback

/-- The rational first Chern class is natural under pullback. -/
private theorem mapCoeff_algebraicFirstChernClass_pullback {X' X : Scheme.{0}}
    [X'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] (f : X' ⟶ X)
    (hf : f ≫ (X ↘ Spec (.of ℂ)) = X' ↘ Spec (.of ℂ)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass ((Scheme.Modules.pullback f).obj L)) =
      (rationalCohomologyMap (analyticMap f hf) 2).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)) := by
  rw [algebraicFirstChernClass_pullback f (analyticMap f hf) (fun _ => rfl) L]
  exact mapCoeff_rationalCohomologyMap _ 2 _

/-- The rational first Chern class of an iterated pullback is the pullback along the
composite. -/
private theorem mapCoeff_algebraicFirstChernClass_pullback_pullback {W Z X : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] (f : W ⟶ Z)
    (g : Z ⟶ X) (hf : f ≫ (Z ↘ Spec (.of ℂ)) = W ↘ Spec (.of ℂ))
    (hg : g ≫ (X ↘ Spec (.of ℂ)) = Z ↘ Spec (.of ℂ)) (k : W ⟶ X) (hk : f ≫ g = k)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass ((Scheme.Modules.pullback f).obj
          ((Scheme.Modules.pullback g).obj L))) =
      (rationalCohomologyMap (analyticMap k (by rw [← hk, Category.assoc, hg, hf])) 2).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L)) := by
  rw [mapCoeff_algebraicFirstChernClass_pullback f hf,
    mapCoeff_algebraicFirstChernClass_pullback g hg, ← ModuleCat.comp_apply,
    ← rationalCohomologyMap_comp]
  congr 3
  ext x
  change (x.hom ≫ f) ≫ g = x.hom ≫ k
  rw [Category.assoc, hk]

end ChernPullback

/-! ### Linear algebra -/

section LinearAlgebra

/-- A finite family whose span contains a subspace of dimension `b` has a linearly independent
subfamily of `b` members. -/
private theorem exists_linearIndependent_comp_of_le_span {V ι : Type*} [AddCommGroup V]
    [Module ℚ V] [Finite ι] (v : ι → V) (W : Submodule ℚ V) [FiniteDimensional ℚ W]
    (hW : W ≤ Submodule.span ℚ (Set.range v)) :
    ∃ f : Fin (Module.finrank ℚ W) → ι, LinearIndependent ℚ (v ∘ f) := by
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range v)
  have hsfin : s.Finite := (Set.finite_range v).subset hs
  haveI : Fintype s := hsfin.fintype
  have hle : Module.finrank ℚ W ≤ Fintype.card s := by
    haveI : FiniteDimensional ℚ (Submodule.span ℚ (Set.range v)) :=
      FiniteDimensional.span_of_finite ℚ (Set.finite_range v)
    have h1 : Module.finrank ℚ W ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range v)) :=
      Submodule.finrank_mono hW
    rw [← hspan, finrank_span_set_eq_card hli, Set.toFinset_card] at h1
    exact h1
  obtain ⟨e⟩ : Nonempty (Fin (Module.finrank ℚ W) ↪ s) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hle)
  have hpre : ∀ z : s, ∃ i, v i = z := fun z => hs z.2
  choose g hg using hpre
  refine ⟨fun k => g (e k), ?_⟩
  have : v ∘ (fun k => g (e k)) = (Subtype.val : s → V) ∘ e := funext fun k => hg (e k)
  rw [this]
  exact hli.comp e e.injective

end LinearAlgebra

/-! ### Transport of sheet classes along paths -/

section SheetTransport

open MMP.Analytic

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- **Transport of a sheet class along a path.** Let `φ : T' ⟶ T¹` be finite étale over a dense
open `T¹ ⊆ T°`, `𝓛'` an invertible module on `𝓕 ×_{T°} T'`, and `β` a class near `F_{t₁}`
restricting to the class of `𝓛'` on the sheet through a point `t'` over `t₁`. Let `E` be the flat
family of germs realizing the classes of `𝓛'` on the sheets. Every path in `T°(ℂ)` from `t₁` to
a point `x` of `T¹(ℂ)` is homotopic to the image of a path in `T¹(ℂ)`; lifting it to `T'(ℂ)`
through `t'`, the transport of the germ of `β` is the value of `E` at the end of the lift. -/
private theorem exists_sheet_transport (hS : IsLocalSetting sY Θ T π)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    {Tr : ∀ {x y : analyticSpace (To.ι ≫ curveι T ≫ sY)}, Path.Homotopic.Quotient x y →
      (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk x ≅
        ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk y)}
    (hgraph : ∀ {x y : analyticSpace (To.ι ≫ curveι T ≫ sY)} (γ : Path x y) w v,
      IsTransportOf (resolutionLocalSystem sY π To) γ w v ↔
        (Tr (Path.Homotopic.Quotient.mk γ)).hom w = v)
    (T₁ : (To : Scheme.{0}).Opens) (hT₁ : Dense (T₁ : Set (To : Scheme.{0})))
    {T' : Scheme.{0}} (φ : T' ⟶ (T₁ : Scheme.{0})) [IsFinite φ] [Etale φ]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).ringCatSheaf.2 L']
    (t' : ComplexPoints (φ ≫ T₁.ι ≫ To.ι ≫ curveι T ≫ sY))
    (t₁ : ComplexPoints (To.ι ≫ curveι T ≫ sY)) (ht' : t'.hom ≫ φ ≫ T₁.ι = t₁.hom)
    (V₁ : Opens (analyticSpace sY)) (hV₁ : curveOpenInclusion sY To t₁ ∈ V₁)
    (β : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V₁) 2)
    [SheafOfModules.IsInvertible (pointFibre sY π To t₁).presheaf
      (pointFibre sY π To t₁).ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π To t₁)
        (pointFibreSnd sY π To t₁ ≫ t'.hom)
        (sheet_w ht'))).obj L')]
    (hβ : (rationalCohomologyMap (pointFibreInclusion sY π To t₁ hV₁) 2).hom β =
      pointFibreChernClass sY π To t₁
        ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π To t₁)
          (pointFibreSnd sY π To t₁ ≫ t'.hom)
          (sheet_w ht'))).obj L')) :
    ∃ Ef : ∀ e : ComplexPoints ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY),
        resolutionLocalSystemFibre sY π To (coverPt e),
      (∀ e, IsRealized (sY := sY) (π := π) (To := To) (t := coverPt e)
        (pointFibreChernClass sY π To (coverPt e)
          ((Scheme.Modules.pullback (sheetAt π e)).obj L')) (Ef e)) ∧
      ∀ (xu : ComplexPoints (T₁.ι ≫ To.ι ≫ curveι T ≫ sY))
        {x : ComplexPoints (To.ι ≫ curveι T ≫ sY)} (hxu : xu.hom ≫ T₁.ι = x.hom)
        (q : Path.Homotopic.Quotient t₁ x),
        ∃ (e : ComplexPoints ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY))
          (_ : ComplexPoints.realize φ (Category.assoc _ _ _).symm e = xu)
          (hx : coverPt e = x),
          (Tr q).hom (germOf π t₁ hV₁ β) =
            (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
              (.of_eq hx)).hom.hom (Ef e) := by
  classical
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hS.isResolution.2.2.2.1
  haveI : IsProper (pullback.snd π (To.ι ≫ curveι T)) :=
    isProper_of_isProjectiveMorphism _ hTo.isProjectiveMorphism
  obtain ⟨hlft, hqc, hsep⟩ := curveOpen_structure sY Θ T π hS To
  haveI : Smooth (To.ι ≫ curveι T ≫ sY) := hTo.smooth
  haveI : ConnectedSpace To := hTo.connectedSpace
  haveI : IsIntegral (To : Scheme.{0}) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (To.ι ≫ curveι T ≫ sY)
  have hV : MMP.Mori.IsVariety ℂ (To.ι ≫ curveι T ≫ sY) := ⟨⟩
  haveI : CompactSpace (To : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (To.ι ≫ curveι T ≫ sY)
  haveI : IsLocallyNoetherian (To : Scheme.{0}) :=
    LocallyOfFiniteType.isLocallyNoetherian (To.ι ≫ curveι T ≫ sY)
  haveI : IsNoetherian (To : Scheme.{0}) := ⟨⟩
  haveI : CompactSpace T₁ := isCompact_iff_compactSpace.1 (NoetherianSpace.isCompact _)
  haveI : QuasiCompact (T₁.ι ≫ To.ι ≫ curveι T ≫ sY) :=
    (quasiCompact_iff_compactSpace _).2 inferInstance
  haveI : Nonempty (T₁ : Scheme.{0}) := ⟨(t'.hom ≫ φ).base default⟩
  haveI : IsIntegral (T₁ : Scheme.{0}) := isIntegral_of_isOpenImmersion T₁.ι
  -- the flat family of sheet classes over `T'(ℂ)`
  haveI : LocallyOfFiniteType ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY) := by
    rw [Category.assoc]; infer_instance
  haveI : IsSeparated ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY) := by
    rw [Category.assoc]; infer_instance
  obtain ⟨Ef, hEf, hloc⟩ := @exists_flat_family Y Yt sY T To T' (φ ≫ T₁.ι) π _ _ _ _ _ _ L' _
  let e' : ComplexPoints ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY) :=
    ⟨t'.hom, by simpa only [Category.assoc] using t'.2⟩
  have hc : coverPt e' = t₁ := ComplexPoints.ext ht'
  have hrel : (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
      (.of_eq hc)).hom.hom (Ef e') = germOf π t₁ hV₁ β :=
    (isRealized_transport L' (hEf e') hc ht').unique ⟨V₁, hV₁, β, hβ, rfl⟩
  refine ⟨Ef, hEf, fun xu x hxu q => ?_⟩
  -- the covering `T'(ℂ) ⟶ T¹(ℂ)`
  have hφ : φ ≫ (T₁.ι ≫ To.ι ≫ curveι T ≫ sY) = (φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY :=
    (Category.assoc _ _ _).symm
  have hcov := ComplexPoints.isCoveringMap_realize_of_isFinite_of_etale φ hφ
  let p := ComplexPoints.realize φ hφ
  let u : ComplexPoints (T₁.ι ≫ To.ι ≫ curveι T ≫ sY) := p e'
  let f : C(ComplexPoints (T₁.ι ≫ To.ι ≫ curveι T ≫ sY), ComplexPoints (To.ι ≫ curveι T ≫ sY)) :=
    ⟨ComplexPoints.realize T₁.ι rfl, ComplexPoints.continuous_realize T₁.ι rfl⟩
  have hu : f u = t₁ := ComplexPoints.ext (by
    change (t'.hom ≫ φ) ≫ T₁.ι = t₁.hom
    rw [Category.assoc]
    exact ht')
  have hx : f xu = x := ComplexPoints.ext hxu
  have hsurj := surjective_fundamentalGroupMap_realize_ι_of_dense
    (To.ι ≫ curveι T ≫ sY) hV T₁ hT₁ u
  subst hu hx
  -- `T¹(ℂ)` is path connected
  haveI := locallyPathConnectedSpace_analyticSpace (T₁.ι ≫ To.ι ≫ curveι T ≫ sY)
  haveI := connectedSpace_analyticSpace (T₁.ι ≫ To.ι ≫ curveι T ≫ sY)
  haveI : PathConnectedSpace (analyticSpace (T₁.ι ≫ To.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 inferInstance
  let δ₀ : Path u xu := PathConnectedSpace.somePath u xu
  -- a path in `T¹(ℂ)` whose image is homotopic to `q`
  let ℓ : Path.Homotopic.Quotient (f u) (f u) :=
    q.trans (Path.Homotopic.Quotient.mk (δ₀.map f.continuous)).symm
  obtain ⟨h, hh⟩ := hsurj (FundamentalGroup.fromPath ℓ)
  obtain ⟨δ₁, hδ₁⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath h)
  have hℓ : Path.Homotopic.Quotient.mk (δ₁.map f.continuous) = ℓ := by
    have : FundamentalGroup.map f u (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ₁)) =
        FundamentalGroup.fromPath ℓ := by
      rwa [hδ₁]
    exact congrArg FundamentalGroup.toPath this
  let δ : Path u xu := δ₁.trans δ₀
  have hq : q = Path.Homotopic.Quotient.mk (δ.map f.continuous) := by
    rw [Path.map_trans, Path.Homotopic.Quotient.mk_trans, hℓ, Path.Homotopic.Quotient.trans_assoc,
      Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.trans_refl]
  -- its lift to `T'(ℂ)` through `t'`
  obtain ⟨Γ, hΓp, hΓ0⟩ := hcov.exists_path_lifts δ.toContinuousMap e' δ.source
  have hΓ' : ∀ s, analyticMap (φ ≫ T₁.ι) (sY := To.ι ≫ curveι T ≫ sY) rfl (Γ s) =
      (δ.map f.continuous) s := fun s => by
    have hs : p (Γ s) = δ s := congrFun hΓp s
    apply ComplexPoints.ext
    change (Γ s).hom ≫ φ ≫ T₁.ι = (δ s).hom ≫ T₁.ι
    rw [← hs]
    exact (Category.assoc _ _ _).symm
  have h0 : analyticMap (φ ≫ T₁.ι) (sY := To.ι ≫ curveι T ≫ sY) rfl (Γ 0) = f u :=
    (hΓ' 0).trans (δ.map f.continuous).source
  have h1 : analyticMap (φ ≫ T₁.ι) (sY := To.ι ≫ curveι T ≫ sY) rfl (Γ 1) = f xu :=
    (hΓ' 1).trans (δ.map f.continuous).target
  have htr := (hgraph _ _ _).1 (isTransportOf_of_lift (𝓛 := resolutionLocalSystem sY π To)
    (E := analyticSpace ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY))
    (p := analyticMap (φ ≫ T₁.ι) (sY := To.ι ≫ curveι T ≫ sY) rfl) Ef hloc
    (δ.map f.continuous) Γ hΓ' h0 h1)
  have hstart : (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
      (.of_eq h0)).hom.hom (Ef (Γ 0)) = germOf π (f u) hV₁ β :=
    (stalkCongr_congr_point _ _ Ef hΓ0 h0 hc).trans hrel
  refine ⟨Γ 1, (congrFun hΓp 1).trans δ.target, h1, ?_⟩
  rw [hq, ← hstart, htr]

/-- The transport of the germ of `β` along a path from `t₁` to a point `x` of `T¹(ℂ)` realizes
the class of `𝓛'` on some sheet over `x`. -/
private theorem exists_sheet_isRealized_transport (hS : IsLocalSetting sY Θ T π)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    {Tr : ∀ {x y : analyticSpace (To.ι ≫ curveι T ≫ sY)}, Path.Homotopic.Quotient x y →
      (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk x ≅
        ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk y)}
    (hgraph : ∀ {x y : analyticSpace (To.ι ≫ curveι T ≫ sY)} (γ : Path x y) w v,
      IsTransportOf (resolutionLocalSystem sY π To) γ w v ↔
        (Tr (Path.Homotopic.Quotient.mk γ)).hom w = v)
    (T₁ : (To : Scheme.{0}).Opens) (hT₁ : Dense (T₁ : Set (To : Scheme.{0})))
    {T' : Scheme.{0}} (φ : T' ⟶ (T₁ : Scheme.{0})) [IsFinite φ] [Etale φ]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).ringCatSheaf.2 L']
    (t' : ComplexPoints (φ ≫ T₁.ι ≫ To.ι ≫ curveι T ≫ sY))
    (t₁ : ComplexPoints (To.ι ≫ curveι T ≫ sY)) (ht' : t'.hom ≫ φ ≫ T₁.ι = t₁.hom)
    (V₁ : Opens (analyticSpace sY)) (hV₁ : curveOpenInclusion sY To t₁ ∈ V₁)
    (β : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V₁) 2)
    [SheafOfModules.IsInvertible (pointFibre sY π To t₁).presheaf
      (pointFibre sY π To t₁).ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π To t₁)
        (pointFibreSnd sY π To t₁ ≫ t'.hom)
        (sheet_w ht'))).obj L')]
    (hβ : (rationalCohomologyMap (pointFibreInclusion sY π To t₁ hV₁) 2).hom β =
      pointFibreChernClass sY π To t₁
        ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π To t₁)
          (pointFibreSnd sY π To t₁ ≫ t'.hom)
          (sheet_w ht'))).obj L'))
    (xu : ComplexPoints (T₁.ι ≫ To.ι ≫ curveι T ≫ sY)) (x : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (hxu : xu.hom ≫ T₁.ι = x.hom) (q : Path.Homotopic.Quotient t₁ x) :
    ∃ (x' : ComplexPoints (φ ≫ T₁.ι ≫ To.ι ≫ curveι T ≫ sY))
      (hx' : x'.hom ≫ φ ≫ T₁.ι = x.hom),
      IsRealized (sY := sY) (π := π) (To := To) (t := x)
        (pointFibreChernClass sY π To x
          ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π To x)
            (pointFibreSnd sY π To x ≫ x'.hom) (sheet_w hx'))).obj L'))
        ((Tr q).hom (germOf π t₁ hV₁ β)) := by
  obtain ⟨Ef, hEf, htr⟩ := exists_sheet_transport hS hTo hgraph T₁ hT₁ φ L' t' t₁ ht' V₁ hV₁ β hβ
  obtain ⟨e, -, hx, he⟩ := htr xu hxu q
  have hx' : e.hom ≫ φ ≫ T₁.ι = x.hom := congrArg ComplexPoints.hom hx
  refine ⟨⟨e.hom, by simpa only [Category.assoc] using e.2⟩, hx', ?_⟩
  rw [he]
  exact isRealized_transport L' (hEf e) hx hx'

end SheetTransport

/-! ### Comparison between a smaller and a larger open of the curve -/

section OpenComparison

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
  {A U : (curveScheme T).Opens} (hUA : U ≤ A)

/-- The inclusion `U ⟶ A` of Zariski-opens of the curve. -/
private abbrev openIncl : (U : Scheme.{0}) ⟶ (A : Scheme.{0}) := (curveScheme T).homOfLE hUA

private theorem openIncl_ι : openIncl hUA ≫ A.ι = U.ι := Scheme.homOfLE_ι _ _

private theorem openIncl_structure :
    openIncl hUA ≫ A.ι ≫ curveι T ≫ sY = U.ι ≫ curveι T ≫ sY := by
  rw [← Category.assoc, openIncl_ι]

/-- A `ℂ`-point of `U`, read as a `ℂ`-point of `A`. -/
private abbrev toA (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    ComplexPoints (A.ι ≫ curveι T ≫ sY) :=
  ComplexPoints.realize (openIncl hUA) (openIncl_structure hUA) u

private theorem toA_hom_comp (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    (toA hUA u).hom ≫ A.ι ≫ curveι T = u.hom ≫ U.ι ≫ curveι T := by
  change (u.hom ≫ openIncl hUA) ≫ A.ι ≫ curveι T = _
  rw [Category.assoc, ← Category.assoc (openIncl hUA), openIncl_ι]

private theorem curveOpenInclusion_toA (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    curveOpenInclusion sY A (toA hUA u) = curveOpenInclusion sY U u :=
  ComplexPoints.ext (toA_hom_comp hUA u)

variable (π) in
/-- The comparison `F_u ⟶ F_u` of the fibre over `u` computed in `U` and in `A`. -/
private def fibreToA (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    pointFibre sY π U u ⟶ pointFibre sY π A (toA hUA u) :=
  pullback.map π (u.hom ≫ U.ι ≫ curveι T) π ((toA hUA u).hom ≫ A.ι ≫ curveι T) (𝟙 _) (𝟙 _)
    (𝟙 _) (by simp) (by rw [toA_hom_comp]; simp)

private theorem fibreToA_fst (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    fibreToA π hUA u ≫ pointFibreFst sY π A (toA hUA u) = pointFibreFst sY π U u := by
  unfold fibreToA pointFibreFst pullback.map
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem fibreToA_snd (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    fibreToA π hUA u ≫ pointFibreSnd sY π A (toA hUA u) = pointFibreSnd sY π U u := by
  unfold fibreToA pointFibreSnd pullback.map
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem fibreToA_over (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    fibreToA π hUA u ≫ (pointFibre sY π A (toA hUA u) ↘ Spec (.of ℂ)) =
      pointFibre sY π U u ↘ Spec (.of ℂ) :=
  fibreToA_snd hUA u

private theorem pointFibreInclusion_toA (u : ComplexPoints (U.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY U u ∈ V) :
    pointFibreInclusion sY π U u hV =
      analyticMap (fibreToA π hUA u) (fibreToA_over hUA u) ≫
        pointFibreInclusion sY π A (toA hUA u) (by rwa [curveOpenInclusion_toA]) := by
  refine TopCat.ext fun x ↦ ?_
  apply Subtype.ext
  apply ComplexPoints.ext
  change x.hom ≫ pointFibreFst sY π U u = (x.hom ≫ fibreToA π hUA u) ≫ pointFibreFst sY π A _
  rw [Category.assoc, fibreToA_fst]

variable (π) in
/-- The identification `𝒲_u ≅ 𝒲_u` of the fibres of the resolution local system of `A` and of
`U` at a point of `U`, both being the stalk of `R²π_* ℚ` at the image of `u`. -/
private def fibreEquivToA (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    resolutionLocalSystemFibre sY π A (toA hUA u) ≃ₗ[ℚ] resolutionLocalSystemFibre sY π U u :=
  haveI := isIso_stalkToPullbackStalk (curveOpenInclusion sY A)
    (resolutionHigherDirectImage sY π 2) (toA hUA u)
  haveI := isIso_stalkToPullbackStalk (curveOpenInclusion sY U)
    (resolutionHigherDirectImage sY π 2) u
  ((asIso (stalkToPullbackStalk (curveOpenInclusion sY A) _ (toA hUA u))).symm ≪≫
    ((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY π 2)).stalkCongr
      (.of_eq (curveOpenInclusion_toA hUA u)) ≪≫
    asIso (stalkToPullbackStalk (curveOpenInclusion sY U) _ u)).toLinearEquiv

private theorem stalkCongr_higherDirectImageGerm {y y' : analyticSpace sY} (h : y = y')
    {V : Opens (analyticSpace sY)} (hy : y ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    (((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY π 2)).stalkCongr
        (.of_eq h)).hom.hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 y hy).hom α) =
      (higherDirectImageGerm (resolutionAnalyticMap sY π) 2 y' (h ▸ hy)).hom α := by
  subst h
  exact stalkCongr_self _ _ _

private theorem germOf_toA (u : ComplexPoints (U.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY U u ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    germOf π u hV α = fibreEquivToA π hUA u
      (germOf π (toA hUA u) (by rwa [curveOpenInclusion_toA]) α) := by
  haveI := isIso_stalkToPullbackStalk (curveOpenInclusion sY A)
    (resolutionHigherDirectImage sY π 2) (toA hUA u)
  change _ = (stalkToPullbackStalk (curveOpenInclusion sY U) _ u).hom
    ((((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY π 2)).stalkCongr
      (.of_eq (curveOpenInclusion_toA hUA u))).hom.hom
        ((inv (stalkToPullbackStalk (curveOpenInclusion sY A) _ (toA hUA u))).hom
          ((stalkToPullbackStalk (curveOpenInclusion sY A) _ (toA hUA u)).hom
            ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ _).hom α))))
  rw [← ModuleCat.comp_apply (stalkToPullbackStalk _ _ _), IsIso.hom_inv_id, ModuleCat.id_apply,
    stalkCongr_higherDirectImageGerm (curveOpenInclusion_toA hUA u)]

/-- A realized pair at `u ∈ U` computed in `A` gives a realized pair computed in `U`. -/
private theorem IsRealized.of_toA {u : ComplexPoints (U.ι ≫ curveι T ≫ sY)} {x w}
    (h : IsRealized (sY := sY) (π := π) (To := A) (t := toA hUA u) x w) :
    IsRealized (sY := sY) (π := π) (To := U) (t := u)
      ((rationalCohomologyMap (analyticMap (fibreToA π hUA u) (fibreToA_over hUA u)) 2).hom x)
      (fibreEquivToA π hUA u w) := by
  obtain ⟨V, hV, α, rfl, rfl⟩ := h
  have hV' : curveOpenInclusion sY U u ∈ V := by rwa [← curveOpenInclusion_toA hUA u]
  refine ⟨V, hV', α, ?_, germOf_toA hUA u hV' α⟩
  rw [pointFibreInclusion_toA hUA u hV', rationalCohomologyMap_comp, ModuleCat.comp_apply]

end OpenComparison

/-! ### Base change of a cover to a smaller open -/

section CoverBaseChange

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
  {A U : (curveScheme T).Opens} (hUA : U ≤ A) {T₁ : (A : Scheme.{0}).Opens} {T' : Scheme.{0}}
  (φ : T' ⟶ (T₁ : Scheme.{0})) {jT : (U : Scheme.{0}) ⟶ (T₁ : Scheme.{0})}
  (hjT : jT ≫ T₁.ι = (curveScheme T).homOfLE hUA)

variable (π) in
/-- The map `𝓕_U ⟶ 𝓕_A` of the families over `U ⊆ A`. -/
private def familyToA : adaptedFamily π U ⟶ adaptedFamily π A :=
  pullback.map π (U.ι ≫ curveι T) π (A.ι ≫ curveι T) (𝟙 _) (openIncl hUA) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Category.assoc, openIncl_ι])

private theorem familyToA_fst :
    familyToA π hUA ≫ pullback.fst π (A.ι ≫ curveι T) = pullback.fst π (U.ι ≫ curveι T) := by
  unfold familyToA pullback.map
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem familyToA_snd :
    familyToA π hUA ≫ pullback.snd π (A.ι ≫ curveι T) =
      pullback.snd π (U.ι ≫ curveι T) ≫ openIncl hUA :=
  pullback.lift_snd _ _ _

include hjT in
private theorem coverFamilyToA_w :
    (pullback.fst (pullback.snd π (U.ι ≫ curveι T)) (pullback.snd φ jT) ≫ familyToA π hUA) ≫
      pullback.snd π (A.ι ≫ curveι T) =
    (pullback.snd (pullback.snd π (U.ι ≫ curveι T)) (pullback.snd φ jT) ≫ pullback.fst φ jT) ≫
      φ ≫ T₁.ι := by
  have hjT' : jT ≫ T₁.ι = openIncl hUA := hjT
  rw [Category.assoc, familyToA_snd, ← Category.assoc, pullback.condition, Category.assoc,
    ← hjT', ← Category.assoc (pullback.snd φ jT) jT, ← pullback.condition]
  simp only [Category.assoc]

variable (π) in
/-- The map `𝓕_U ×_U (T' ×_{T¹} U) ⟶ 𝓕_A ×_A T'` of families over the covers. -/
private def coverFamilyToA :
    pullback (pullback.snd π (U.ι ≫ curveι T)) (pullback.snd φ jT) ⟶
      pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι) :=
  pullback.lift _ _ (coverFamilyToA_w hUA φ hjT)

variable {hUA} in
include hjT in
private theorem sheetPoint_w {u : ComplexPoints (U.ι ≫ curveι T ≫ sY)}
    {x' : ComplexPoints (φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY)}
    (hx' : x'.hom ≫ φ ≫ T₁.ι = (toA hUA u).hom) : x'.hom ≫ φ = u.hom ≫ jT := by
  apply (cancel_mono T₁.ι).1
  rw [Category.assoc, hx', Category.assoc, hjT]
  rfl

/-- The point of `T' ×_{T¹} U` given by a point `x'` of `T'` over a point `u` of `U`. -/
private def sheetPoint {u : ComplexPoints (U.ι ≫ curveι T ≫ sY)}
    (x' : ComplexPoints (φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY))
    (hx' : x'.hom ≫ φ ≫ T₁.ι = (toA hUA u).hom) :
    ComplexPoints (pullback.snd φ jT ≫ U.ι ≫ curveι T ≫ sY) :=
  ⟨pullback.lift x'.hom u.hom (sheetPoint_w φ hjT hx'), by
    rw [← Category.assoc, pullback.lift_snd]; exact u.2⟩

private theorem sheetPoint_snd {u : ComplexPoints (U.ι ≫ curveι T ≫ sY)}
    (x' : ComplexPoints (φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY))
    (hx' : x'.hom ≫ φ ≫ T₁.ι = (toA hUA u).hom) :
    (sheetPoint hUA φ hjT x' hx').hom ≫ pullback.snd φ jT = u.hom :=
  pullback.lift_snd _ _ _

private theorem sheetPoint_fst {u : ComplexPoints (U.ι ≫ curveι T ≫ sY)}
    (x' : ComplexPoints (φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY))
    (hx' : x'.hom ≫ φ ≫ T₁.ι = (toA hUA u).hom) :
    (sheetPoint hUA φ hjT x' hx').hom ≫ pullback.fst φ jT = x'.hom :=
  pullback.lift_fst _ _ _

/-- The sheet through `x'` of the family over `T'`, at the point `toA u` of `A`. -/
private abbrev sheetOfPoint {B : (curveScheme T).Opens} {B₁ : (B : Scheme.{0}).Opens}
    {S : Scheme.{0}} {ψ : S ⟶ (B₁ : Scheme.{0})} {b : ComplexPoints (B.ι ≫ curveι T ≫ sY)}
    (x' : ComplexPoints (ψ ≫ B₁.ι ≫ B.ι ≫ curveι T ≫ sY)) (hx' : x'.hom ≫ ψ ≫ B₁.ι = b.hom) :
    pointFibre sY π B b ⟶ pullback (pullback.snd π (B.ι ≫ curveι T)) (ψ ≫ B₁.ι) :=
  pullback.lift (pointFibreToFamily sY π B b) (pointFibreSnd sY π B b ≫ x'.hom) (sheet_w hx')

private theorem pointFibreToFamily_fst (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    pointFibreToFamily sY π U u ≫ pullback.fst π (U.ι ≫ curveι T) = pointFibreFst sY π U u := by
  unfold pointFibreToFamily pullback.map
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem pointFibreToFamily_snd (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    pointFibreToFamily sY π U u ≫ pullback.snd π (U.ι ≫ curveι T) =
      pointFibreSnd sY π U u ≫ u.hom :=
  pullback.lift_snd _ _ _

private theorem pointFibreToFamily_familyToA (u : ComplexPoints (U.ι ≫ curveι T ≫ sY)) :
    pointFibreToFamily sY π U u ≫ familyToA π hUA =
      fibreToA π hUA u ≫ pointFibreToFamily sY π A (toA hUA u) := by
  apply pullback.hom_ext
  · rw [Category.assoc, familyToA_fst, Category.assoc, pointFibreToFamily_fst,
      pointFibreToFamily_fst, fibreToA_fst]
  · rw [Category.assoc, familyToA_snd, ← Category.assoc, pointFibreToFamily_snd, Category.assoc,
      Category.assoc, pointFibreToFamily_snd, ← Category.assoc (fibreToA π hUA u), fibreToA_snd]
    rfl

private theorem sheetι_coverFamilyToA {u : ComplexPoints (U.ι ≫ curveι T ≫ sY)}
    (x' : ComplexPoints (φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY))
    (hx' : x'.hom ≫ φ ≫ T₁.ι = (toA hUA u).hom) :
    sheetι (π := π) (To := U) (t := u) (φ := pullback.snd φ jT)
        ⟨sheetPoint hUA φ hjT x' hx', sheetPoint_snd hUA φ hjT x' hx'⟩ ≫
      coverFamilyToA π hUA φ hjT =
    fibreToA π hUA u ≫ sheetOfPoint (π := π) x' hx' := by
  apply pullback.hom_ext
  · rw [Category.assoc, coverFamilyToA, pullback.lift_fst, ← Category.assoc, sheetι_comp_fst,
      pointFibreToFamily_familyToA, Category.assoc, sheetOfPoint, pullback.lift_fst]
  · rw [Category.assoc, coverFamilyToA, pullback.lift_snd, ← Category.assoc, sheetι,
      pullback.lift_snd, Category.assoc, sheetPoint_fst, Category.assoc, sheetOfPoint,
      pullback.lift_snd]
    exact congrArg (· ≫ x'.hom) (fibreToA_snd hUA u).symm |>.trans (Category.assoc _ _ _)

/-- The class of the pulled-back line bundle on the sheet over `u` is the pullback of the class
on the sheet over `toA u`. -/
private theorem pointFibreChernClass_sheet_toA {u : ComplexPoints (U.ι ≫ curveι T ≫ sY)}
    (x' : ComplexPoints (φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY))
    (hx' : x'.hom ≫ φ ≫ T₁.ι = (toA hUA u).hom)
    (L' : (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι)).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι)).presheaf
      (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι)).ringCatSheaf.2 L'] :
    pointFibreChernClass sY π U u ((Scheme.Modules.pullback (sheetι (π := π) (To := U) (t := u)
        (φ := pullback.snd φ jT)
          ⟨sheetPoint hUA φ hjT x' hx', sheetPoint_snd hUA φ hjT x' hx'⟩)).obj
          ((Scheme.Modules.pullback (coverFamilyToA π hUA φ hjT)).obj L')) =
      (rationalCohomologyMap (analyticMap (fibreToA π hUA u) (fibreToA_over hUA u)) 2).hom
        (pointFibreChernClass sY π A (toA hUA u)
          ((Scheme.Modules.pullback (sheetOfPoint (π := π) x' hx')).obj L')) := by
  letI iA : (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι)).Over (Spec (.of ℂ)) :=
    ⟨pullback.snd _ _ ≫ φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY⟩
  letI iU : (pullback (pullback.snd π (U.ι ≫ curveι T)) (pullback.snd φ jT)).Over
      (Spec (.of ℂ)) :=
    ⟨pullback.snd _ _ ≫ pullback.snd φ jT ≫ U.ι ≫ curveι T ≫ sY⟩
  have hι : sheetι (π := π) (To := U) (t := u) (φ := pullback.snd φ jT)
      ⟨sheetPoint hUA φ hjT x' hx', sheetPoint_snd hUA φ hjT x' hx'⟩ ≫
        (pullback (pullback.snd π (U.ι ≫ curveι T)) (pullback.snd φ jT) ↘ Spec (.of ℂ)) =
      pointFibre sY π U u ↘ Spec (.of ℂ) := by
    change sheetι _ ≫ pullback.snd _ _ ≫ _ = pointFibreSnd sY π U u
    rw [← Category.assoc, sheetι, pullback.lift_snd, Category.assoc,
      (sheetPoint hUA φ hjT x' hx').hom_comp_structure, Category.comp_id]
  have hk : coverFamilyToA π hUA φ hjT ≫
        (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι) ↘ Spec (.of ℂ)) =
      pullback (pullback.snd π (U.ι ≫ curveι T)) (pullback.snd φ jT) ↘ Spec (.of ℂ) := by
    change coverFamilyToA π hUA φ hjT ≫ pullback.snd _ _ ≫ φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY =
      pullback.snd _ _ ≫ pullback.snd φ jT ≫ U.ι ≫ curveι T ≫ sY
    rw [← Category.assoc, coverFamilyToA, pullback.lift_snd, Category.assoc,
      ← Category.assoc (pullback.fst φ jT), pullback.condition, Category.assoc,
      ← Category.assoc jT, hjT, ← openIncl_structure hUA]
  have hs : sheetOfPoint (π := π) x' hx' ≫
        (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι) ↘ Spec (.of ℂ)) =
      pointFibre sY π A (toA hUA u) ↘ Spec (.of ℂ) := by
    change sheetOfPoint x' hx' ≫ pullback.snd _ _ ≫ _ = pointFibreSnd sY π A (toA hUA u)
    rw [← Category.assoc, sheetOfPoint, pullback.lift_snd, Category.assoc, x'.hom_comp_structure,
      Category.comp_id]
  unfold pointFibreChernClass
  rw [mapCoeff_algebraicFirstChernClass_pullback_pullback _ _ hι hk _ rfl L',
    mapCoeff_algebraicFirstChernClass_pullback _ hs L', ← ModuleCat.comp_apply,
    ← rationalCohomologyMap_comp]
  congr 3
  refine TopCat.ext fun x ↦ ComplexPoints.ext ?_
  change x.hom ≫ (sheetι _ ≫ coverFamilyToA π hUA φ hjT) =
    (x.hom ≫ fibreToA π hUA u) ≫ sheetOfPoint x' hx'
  rw [sheetι_coverFamilyToA, Category.assoc]

end CoverBaseChange

/-! ### The generic fibre -/

section GenericFibre

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- A closed immersion induces isomorphisms of residue fields. -/
private theorem isIso_residueFieldMap_of_isClosedImmersion {X Z : Scheme.{0}} (f : X ⟶ Z)
    [IsClosedImmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  have hs : Function.Surjective (f.stalkMap x) := f.stalkMap_surjective x
  have : Function.Surjective (f.residueFieldMap x) := by
    intro y
    obtain ⟨b, rfl⟩ := X.residue_surjective x y
    obtain ⟨a, rfl⟩ := hs b
    refine ⟨Z.residue (f x) a, ?_⟩
    rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
  have hb : Function.Bijective (f.residueFieldMap x) :=
    ⟨(f.residueFieldMap x).hom.injective, this⟩
  exact (ConcreteCategory.isIso_iff_bijective _).2 hb

/-- A dense integral Zariski-open of the curve contains a point over the generic point `η_T`. -/
private theorem exists_eq_localSettingGenericPoint (To : (curveScheme T).Opens)
    [IsIntegral (To : Scheme.{0})] (hd : Dense (To : Set (curveScheme T))) :
    ∃ ξ : (To : Scheme.{0}), (To.ι ≫ curveι T).base ξ = localSettingGenericPoint T := by
  refine ⟨genericPoint (To : Scheme.{0}), ?_⟩
  set f := (To.ι ≫ curveι T).base
  have hrange : Set.range (curveι T).base = (T : Set Y) :=
    Scheme.IdealSheafData.range_subschemeι _
  have hZT : closure (f '' Set.univ) = (T : Set Y) := by
    apply subset_antisymm
    · refine closure_minimal ?_ T.isClosed
      rintro _ ⟨p, -, rfl⟩
      rw [← hrange]
      exact ⟨To.ι.base p, rfl⟩
    · intro y hy
      rw [← hrange] at hy
      obtain ⟨q, rfl⟩ := hy
      have hpre : IsClosed ((curveι T).base ⁻¹' closure (f '' Set.univ)) :=
        isClosed_closure.preimage (curveι T).base.hom.continuous
      have hsub : (To : Set (curveScheme T)) ⊆ (curveι T).base ⁻¹' closure (f '' Set.univ) :=
        fun p hp => subset_closure ⟨⟨p, hp⟩, trivial, rfl⟩
      have h := closure_minimal hsub hpre
      rw [hd.closure_eq] at h
      exact h (Set.mem_univ q)
  have h1 := (genericPoint_spec (To : Scheme.{0})).image (f := f) f.hom.continuous
  rw [hZT] at h1
  have h2 := T.isIrreducible.isGenericPoint_genericPoint_closure
  rw [T.isClosed.closure_eq] at h2
  exact h1.eq h2

/-- Over a point of the open lying over `η_T`, the fibre of the family is the generic fibre. -/
private theorem isIso_curveOpenFibreToGenericFibre (To : (curveScheme T).Opens)
    (ξ : (To : Scheme.{0})) (e : (To.ι ≫ curveι T).base ξ = localSettingGenericPoint T) :
    IsIso (curveOpenFibreToGenericFibre π To ξ e) := by
  haveI : IsIso ((To.ι ≫ curveι T).residueFieldMap ξ) := by
    rw [Scheme.residueFieldMap_comp]
    have h1 := isIso_residueFieldMap_of_isClosedImmersion (curveι T) (To.ι ξ)
    have h2 : IsIso (To.ι.residueFieldMap ξ) := inferInstance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  unfold curveOpenFibreToGenericFibre
  infer_instance

/-- An invertible module on the family over `T°` has a generic fibre. -/
private theorem exists_genericFibre_iso (To : (curveScheme T).Opens) (ξ : (To : Scheme.{0}))
    (e : (To.ι ≫ curveι T).base ξ = localSettingGenericPoint T)
    (𝓛 : (adaptedFamily π To).Modules)
    [SheafOfModules.IsInvertible (adaptedFamily π To).presheaf
      (adaptedFamily π To).ringCatSheaf.2 𝓛] :
    ∃ L : (genericFibre π T).Modules,
      SheafOfModules.IsInvertible (genericFibre π T).presheaf
        (genericFibre π T).ringCatSheaf.2 L ∧
      Nonempty ((Scheme.Modules.pullback (curveOpenFibreToFamily π To ξ)).obj 𝓛 ≅
        (Scheme.Modules.pullback (curveOpenFibreToGenericFibre π To ξ e)).obj L) := by
  haveI := isIso_curveOpenFibreToGenericFibre (π := π) To ξ e
  set g := curveOpenFibreToGenericFibre π To ξ e
  refine ⟨(Scheme.Modules.pullback (inv g)).obj
    ((Scheme.Modules.pullback (curveOpenFibreToFamily π To ξ)).obj 𝓛), inferInstance, ⟨?_⟩⟩
  exact ((Scheme.Modules.pullbackId _).app _).symm ≪≫
    ((Scheme.Modules.pullbackCongr (IsIso.hom_inv_id g)).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp g (inv g)).app _).symm

end GenericFibre

/-! ### Independence at one point gives independence at every point -/

section Flatness

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The class of `𝓝` on the sheet of the trivial cover is its class on the fibre. -/
private theorem pointFibreChernClass_sheetι_id {To : (curveScheme T).Opens}
    (N : (adaptedFamily π To).Modules)
    [SheafOfModules.IsInvertible (adaptedFamily π To).presheaf
      (adaptedFamily π To).ringCatSheaf.2 N]
    (u : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (s : {t'' : ComplexPoints (𝟙 (To : Scheme.{0}) ≫ To.ι ≫ curveι T ≫ sY) //
      t''.hom ≫ 𝟙 _ = u.hom}) :
    pointFibreChernClass sY π To u ((Scheme.Modules.pullback (sheetι (π := π) s)).obj
        ((Scheme.Modules.pullback
          (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) (𝟙 _))).obj N)) =
      pointFibreChernClass sY π To u
        ((Scheme.Modules.pullback (pointFibreToFamily sY π To u)).obj N) := by
  letI : (adaptedFamily π To).Over (Spec (.of ℂ)) :=
    ⟨pullback.snd _ _ ≫ To.ι ≫ curveι T ≫ sY⟩
  letI : (pullback (pullback.snd π (To.ι ≫ curveι T)) (𝟙 (To : Scheme.{0}))).Over
      (Spec (.of ℂ)) :=
    ⟨pullback.snd _ _ ≫ 𝟙 _ ≫ To.ι ≫ curveι T ≫ sY⟩
  have hs : sheetι (π := π) s ≫
      (pullback (pullback.snd π (To.ι ≫ curveι T)) (𝟙 (To : Scheme.{0})) ↘ Spec (.of ℂ)) =
      pointFibre sY π To u ↘ Spec (.of ℂ) := by
    change sheetι s ≫ pullback.snd _ _ ≫ _ = pointFibreSnd sY π To u
    rw [← Category.assoc, sheetι, pullback.lift_snd, Category.assoc, s.1.hom_comp_structure,
      Category.comp_id]
  have hf : pullback.fst (pullback.snd π (To.ι ≫ curveι T)) (𝟙 (To : Scheme.{0})) ≫
      (adaptedFamily π To ↘ Spec (.of ℂ)) =
      pullback (pullback.snd π (To.ι ≫ curveι T)) (𝟙 (To : Scheme.{0})) ↘ Spec (.of ℂ) := by
    change pullback.fst _ _ ≫ pullback.snd _ _ ≫ _ = pullback.snd _ _ ≫ 𝟙 _ ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have hp : pointFibreToFamily sY π To u ≫ (adaptedFamily π To ↘ Spec (.of ℂ)) =
      pointFibre sY π To u ↘ Spec (.of ℂ) := by
    change pointFibreToFamily sY π To u ≫ pullback.snd _ _ ≫ _ = pointFibreSnd sY π To u
    rw [← Category.assoc, pointFibreToFamily_snd, Category.assoc, u.hom_comp_structure,
      Category.comp_id]
  unfold pointFibreChernClass
  rw [mapCoeff_algebraicFirstChernClass_pullback_pullback _ _ hs hf _ (sheetι_comp_fst s) N,
    mapCoeff_algebraicFirstChernClass_pullback _ hp N]

/-- **Independence spreads along the curve.** Let `𝓝_1, …, 𝓝_b` be line bundles on the family
over a `π`-adapted open `T°`, and suppose that at one point `t₀` the germs realizing their classes
on `F_{t₀}` have linearly independent images in `𝒱_{T,t₀}`. Then the same holds at every point
`t`: the realizing germs form flat sections of `𝒲`, their images flat sections of `𝒱_T`, and
transport along a path from `t₀` to `t` is a linear isomorphism. -/
private theorem exists_linearIndependent_at (hS : IsLocalSetting sY Θ T π)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To) {b : ℕ}
    (N : Fin b → (adaptedFamily π To).Modules)
    [hN : ∀ k, SheafOfModules.IsInvertible (adaptedFamily π To).presheaf
      (adaptedFamily π To).ringCatSheaf.2 (N k)]
    (t₀ t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (n : Fin b → resolutionLocalSystemFibre sY π To t₀)
    (hn : ∀ k, IsRealized (sY := sY) (π := π) (To := To) (t := t₀)
      (pointFibreChernClass sY π To t₀
        ((Scheme.Modules.pullback (pointFibreToFamily sY π To t₀)).obj (N k))) (n k))
    (hli : LinearIndependent ℚ fun k =>
      (localSystemRestrictionFibre sY hS.isBiregular To t₀).hom (n k)) :
    ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
      (α : Fin b → rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2),
      (∀ i, ∃ _ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
          (pointFibre sY π To t).ringCatSheaf.2
          ((Scheme.Modules.pullback (pointFibreToFamily sY π To t)).obj (N i)),
        (rationalCohomologyMap (pointFibreInclusion sY π To t hV) 2).hom (α i) =
          pointFibreChernClass sY π To t
            ((Scheme.Modules.pullback (pointFibreToFamily sY π To t)).obj (N i))) ∧
      LinearIndependent ℚ fun i ↦ (localSystemRestrictionFibre sY hS.isBiregular To t).hom
        ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
          t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom (α i))) := by
  classical
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hS.isResolution.2.2.2.1
  haveI : IsProper (pullback.snd π (To.ι ≫ curveι T)) :=
    isProper_of_isProjectiveMorphism _ hTo.isProjectiveMorphism
  obtain ⟨hlft, hqc, hsep⟩ := curveOpen_structure sY Θ T π hS To
  haveI : Smooth (To.ι ≫ curveι T ≫ sY) := hTo.smooth
  haveI : ConnectedSpace To := hTo.connectedSpace
  haveI : IsIntegral (To : Scheme.{0}) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (To.ι ≫ curveι T ≫ sY)
  haveI : LocallyOfFiniteType (𝟙 (To : Scheme.{0}) ≫ To.ι ≫ curveι T ≫ sY) := by
    rw [Category.id_comp]; infer_instance
  haveI : IsSeparated (𝟙 (To : Scheme.{0}) ≫ To.ι ≫ curveι T ≫ sY) := by
    rw [Category.id_comp]; infer_instance
  haveI : IsProper (famMap π (𝟙 (To : Scheme.{0}))) := by
    unfold famMap; infer_instance
  -- the flat families of classes
  have hfam := fun k => @exists_flat_family Y Yt sY T To To (𝟙 _) π _ _ _ _ _ _
    ((Scheme.Modules.pullback (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) (𝟙 _))).obj
      (N k)) _
  choose Ef hEf hloc using hfam
  -- a path from `t₀` to `t`
  haveI := locallyPathConnectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  haveI := connectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  haveI : PathConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 inferInstance
  let δ : Path t₀ t := PathConnectedSpace.somePath t₀ t
  have hq : 𝟙 (To : Scheme.{0}) ≫ 𝟙 (To : Scheme.{0}) ≫ To.ι ≫ curveι T ≫ sY =
      To.ι ≫ curveι T ≫ sY := by simp
  let Γ : C(unitInterval, analyticSpace (𝟙 (To : Scheme.{0}) ≫ To.ι ≫ curveι T ≫ sY)) :=
    ⟨fun s => ComplexPoints.realize (𝟙 _) hq (δ s),
      (ComplexPoints.continuous_realize _ hq).comp δ.continuous⟩
  have hΓ : ∀ s, analyticMap (𝟙 (To : Scheme.{0})) (sY := To.ι ≫ curveι T ≫ sY) rfl (Γ s) =
      δ s := fun s => ComplexPoints.ext (by
    change ((δ s).hom ≫ 𝟙 _) ≫ 𝟙 _ = (δ s).hom
    simp)
  have h0 : analyticMap (𝟙 (To : Scheme.{0})) (sY := To.ι ≫ curveι T ≫ sY) rfl (Γ 0) = t₀ :=
    (hΓ 0).trans δ.source
  have h1 : analyticMap (𝟙 (To : Scheme.{0})) (sY := To.ι ≫ curveι T ≫ sY) rfl (Γ 1) = t :=
    (hΓ 1).trans δ.target
  have htr := fun k => isTransportOf_of_lift (𝓛 := resolutionLocalSystem sY π To) (Ef k)
    (hloc k) δ Γ hΓ h0 h1
  -- the transported germs realize the classes
  have hr : ∀ k (s : unitInterval) {x : ComplexPoints (To.ι ≫ curveι T ≫ sY)}
      (hx : coverPt (Γ s) = x),
      IsRealized (sY := sY) (π := π) (To := To) (t := x)
        (pointFibreChernClass sY π To x
          ((Scheme.Modules.pullback (pointFibreToFamily sY π To x)).obj (N k)))
        ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
          (.of_eq hx)).hom.hom (Ef k (Γ s))) := by
    intro k s x hx
    have h' : (Γ s).hom ≫ 𝟙 _ = x.hom := congrArg ComplexPoints.hom hx
    have := isRealized_transport _ (hEf k (Γ s)) hx h'
    rwa [pointFibreChernClass_sheetι_id] at this
  have hn' : ∀ k, (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
      (.of_eq h0)).hom.hom (Ef k (Γ 0)) = n k := fun k => (hr k 0 h0).unique (hn k)
  -- transport in `𝒱_T`
  obtain ⟨TrV, hgV, -⟩ := exists_transport (curveLocalSystem sY To) hTo.isLocalSystem
  have hVk : ∀ k, (TrV (Path.Homotopic.Quotient.mk δ)).hom
      ((localSystemRestrictionFibre sY hS.isBiregular To t₀).hom (n k)) =
      (localSystemRestrictionFibre sY hS.isBiregular To t).hom
        ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
          (.of_eq h1)).hom.hom (Ef k (Γ 1))) := fun k => by
    refine (hgV δ _ _).1 ?_
    rw [← hn' k]
    exact (htr k).map (localSystemRestriction sY hS.isBiregular To)
  -- classes at `t` on one neighbourhood
  choose W hW α hα hgerm using fun k => hr k 1 h1
  let V : Opens (analyticSpace sY) := ⨅ k, W k
  have hVt : curveOpenInclusion sY To t ∈ V := by
    show curveOpenInclusion sY To t ∈ (V : Set (analyticSpace sY))
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.2 hW
  refine ⟨V, hVt, fun k => (rationalCohomologyMap (preimageInclusion _ (iInf_le W k)) 2).hom
    (α k), fun k => ⟨inferInstance, ?_⟩, ?_⟩
  · rw [rationalCohomologyMap_pointFibreInclusion_preimageInclusion (iInf_le W k) hVt (α k),
      hα k]
  · have e : (fun k => (localSystemRestrictionFibre sY hS.isBiregular To t).hom
        ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
          t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hVt).hom
            ((rationalCohomologyMap (preimageInclusion _ (iInf_le W k)) 2).hom (α k))))) =
        (TrV (Path.Homotopic.Quotient.mk δ)).toLinearEquiv.toLinearMap ∘
          fun k => (localSystemRestrictionFibre sY hS.isBiregular To t₀).hom (n k) := by
      funext k
      rw [Function.comp_apply, higherDirectImageGerm_preimageInclusion (iInf_le W k) hVt (α k),
        hgerm k]
      exact (hVk k).symm
    rw [e]
    exact hli.map' _ (LinearEquiv.ker _)

end Flatness

/-! ### Shrinking the adapted open -/

section Shrinking

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- A finite intersection of dense open sets is dense. -/
private theorem dense_iInter_of_isOpen_of_finite {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {U : ι → Set X} (ho : ∀ i, IsOpen (U i)) (hd : ∀ i, Dense (U i)) : Dense (⋂ i, U i) := by
  classical
  cases nonempty_fintype ι
  have key : ∀ s : Finset ι, Dense (⋂ i ∈ s, U i) ∧ IsOpen (⋂ i ∈ s, U i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.set_biInter_insert]
      exact ⟨(hd a).inter_of_isOpen_left ih.1 (ho a), (ho a).inter ih.2⟩
  simpa using (key Finset.univ).1

/-- The image in `T` of a dense open of a `π`-adapted open is a `π`-adapted open. -/
private theorem isAdaptedOpen_image
    (hshrink : ∀ To U : (curveScheme T).Opens, IsAdaptedOpen sY π To → U ≤ To →
      ConnectedSpace U → Dense (U : Set (curveScheme T)) → IsAdaptedOpen sY π U)
    {A : (curveScheme T).Opens} (hA : IsAdaptedOpen sY π A) [IrreducibleSpace (A : Scheme.{0})]
    (U : (A : Scheme.{0}).Opens) (hU : Dense (U : Set (A : Scheme.{0}))) :
    A.ι ''ᵁ U ≤ A ∧ IsAdaptedOpen sY π (A.ι ''ᵁ U) := by
  have hle : A.ι ''ᵁ U ≤ A :=
    (Scheme.Hom.image_le_opensRange _ _).trans_eq (Scheme.Opens.opensRange_ι A)
  have hcoe : ((A.ι ''ᵁ U : (curveScheme T).Opens) : Set (curveScheme T)) =
      A.ι.base '' (U : Set (A : Scheme.{0})) := Scheme.Hom.coe_image _
  refine ⟨hle, hshrink A _ hA hle ?_ ?_⟩
  · have hne : (U : Set (A : Scheme.{0})).Nonempty := hU.nonempty
    have hirr : IsIrreducible (U : Set (A : Scheme.{0})) :=
      ⟨hne, (IrreducibleSpace.isIrreducible_univ (A : Scheme.{0})).isPreirreducible.open_subset
        U.isOpen (Set.subset_univ _)⟩
    have h := (hirr.image A.ι.base A.ι.base.hom.continuous.continuousOn).isConnected
    rw [← hcoe] at h
    exact isConnected_iff_connectedSpace.1 h
  · rw [hcoe]
    have hdr : DenseRange A.ι.base := by
      rw [DenseRange, Scheme.Opens.range_ι]
      exact hA.dense
    exact hdr.dense_image A.ι.base.hom.continuous hU

/-- The inclusion of the image of `U ≤ T₁` into `T₁`. -/
private theorem exists_lift_image {A : (curveScheme T).Opens} (U T₁ : (A : Scheme.{0}).Opens)
    (hUT : U ≤ T₁) (hle : A.ι ''ᵁ U ≤ A) :
    ∃ jT : ((A.ι ''ᵁ U : (curveScheme T).Opens) : Scheme.{0}) ⟶ (T₁ : Scheme.{0}),
      jT ≫ T₁.ι = (curveScheme T).homOfLE hle := by
  have hr : Set.range ((curveScheme T).homOfLE hle).base ⊆ Set.range T₁.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h1 : A.ι.base (((curveScheme T).homOfLE hle).base p) = (A.ι ''ᵁ U).ι.base p := by
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    have h2 : (A.ι ''ᵁ U).ι.base p ∈ ((A.ι ''ᵁ U : (curveScheme T).Opens) :
        Set (curveScheme T)) := by
      have h3 : (A.ι ''ᵁ U).ι.base p ∈ Set.range (A.ι ''ᵁ U).ι.base := ⟨p, rfl⟩
      rwa [Scheme.Opens.range_ι] at h3
    rw [Scheme.Hom.coe_image] at h2
    obtain ⟨q, hq, hqe⟩ := h2
    rw [← h1] at hqe
    exact hUT (A.ι.isOpenEmbedding.injective hqe ▸ hq)
  exact ⟨IsOpenImmersion.lift T₁.ι _ hr, IsOpenImmersion.lift_fac _ _ _⟩

/-- The base change of a connected finite étale cover to a nonempty open is connected. -/
private theorem connectedSpace_pullback_of_etale {A : (curveScheme T).Opens}
    {T₁ : (A : Scheme.{0}).Opens} {T' P : Scheme.{0}} (φ : T' ⟶ (T₁ : Scheme.{0}))
    (jT : P ⟶ (T₁ : Scheme.{0})) [IsOpenImmersion jT] [Etale φ] [ConnectedSpace T']
    [Smooth (A.ι ≫ curveι T ≫ sY)] [Nonempty (pullback φ jT : Scheme.{0})] :
    ConnectedSpace (pullback φ jT : Scheme.{0}) := by
  haveI : IsIntegral T' :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY)
  haveI : IsIntegral (pullback φ jT : Scheme.{0}) :=
    isIntegral_of_isOpenImmersion (pullback.fst φ jT)
  infer_instance

end Shrinking

/-! ### Norms of sheet classes -/

section Norms

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- **A norm class.** In the situation of `exists_sheet_isRealized_transport`, let `S ⊆ T¹` be a
smaller `π`-adapted open. For a `ℂ`-point `t*` of `S` and the monodromy `G` of `𝒲` on `S` at
`t*`, there is a line bundle on the family over `S` (the norm of the base change of `𝓛'`) whose
class on `F_{t*}` is realized by a nonzero multiple of the `G`-average of the transported class. -/
private theorem exists_norm_class (hS : IsLocalSetting sY Θ T π)
    {A : (curveScheme T).Opens} (hA : IsAdaptedOpen sY π A)
    {S : (curveScheme T).Opens} (hSA : S ≤ A) (hS2 : IsAdaptedOpen sY π S)
    (tS : ComplexPoints (S.ι ≫ curveι T ≫ sY))
    (G : Set (Module.End ℚ (resolutionLocalSystemFibre sY π S tS)))
    (hG : ∀ g, g ∈ G ↔ ∃ γ : Path tS tS,
      ∀ (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
            (resolutionLocalSystem sY π S)).obj.obj (op ⊤)))
        (w v : resolutionLocalSystemFibre sY π S tS),
        (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
            (resolutionLocalSystem sY π S) 0).hom
            ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π S)).stalkCongr
              (.of_eq γ.source.symm)).hom.hom w) =
          (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (resolutionLocalSystem sY π S))).germ ⊤ 0 trivial).hom s →
        (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
            (resolutionLocalSystem sY π S) 1).hom
            ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π S)).stalkCongr
              (.of_eq γ.target.symm)).hom.hom v) =
          (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (resolutionLocalSystem sY π S))).germ ⊤ 1 trivial).hom s →
        g w = v)
    (hGfin : G.Finite)
    {Tr : ∀ {x y : analyticSpace (A.ι ≫ curveι T ≫ sY)}, Path.Homotopic.Quotient x y →
      (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π A)).stalk x ≅
        ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π A)).stalk y)}
    (hgraph : ∀ {x y : analyticSpace (A.ι ≫ curveι T ≫ sY)} (γ : Path x y) w v,
      IsTransportOf (resolutionLocalSystem sY π A) γ w v ↔
        (Tr (Path.Homotopic.Quotient.mk γ)).hom w = v)
    (T₁ : (A : Scheme.{0}).Opens) (hT₁ : Dense (T₁ : Set (A : Scheme.{0})))
    {T' : Scheme.{0}} (φ : T' ⟶ (T₁ : Scheme.{0})) [IsFinite φ] [Etale φ] [ConnectedSpace T']
    (L' : (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι)).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι)).presheaf
      (pullback (pullback.snd π (A.ι ≫ curveι T)) (φ ≫ T₁.ι)).ringCatSheaf.2 L']
    (t' : ComplexPoints (φ ≫ T₁.ι ≫ A.ι ≫ curveι T ≫ sY))
    (t₁ : ComplexPoints (A.ι ≫ curveι T ≫ sY)) (ht' : t'.hom ≫ φ ≫ T₁.ι = t₁.hom)
    (V₁ : Opens (analyticSpace sY)) (hV₁ : curveOpenInclusion sY A t₁ ∈ V₁)
    (β : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V₁) 2)
    [SheafOfModules.IsInvertible (pointFibre sY π A t₁).presheaf
      (pointFibre sY π A t₁).ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π A t₁)
        (pointFibreSnd sY π A t₁ ≫ t'.hom)
        (sheet_w ht'))).obj L')]
    (hβ : (rationalCohomologyMap (pointFibreInclusion sY π A t₁ hV₁) 2).hom β =
      pointFibreChernClass sY π A t₁
        ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π A t₁)
          (pointFibreSnd sY π A t₁ ≫ t'.hom)
          (sheet_w ht'))).obj L'))
    (jT : (S : Scheme.{0}) ⟶ (T₁ : Scheme.{0})) (hjT : jT ≫ T₁.ι = (curveScheme T).homOfLE hSA)
    (q : Path.Homotopic.Quotient t₁ (toA hSA tS)) :
    ∃ (N : (adaptedFamily π S).Modules)
      (_ : SheafOfModules.IsInvertible (adaptedFamily π S).presheaf
        (adaptedFamily π S).ringCatSheaf.2 N)
      (n : resolutionLocalSystemFibre sY π S tS) (d : ℚ), d ≠ 0 ∧
      IsRealized (sY := sY) (π := π) (To := S) (t := tS)
        (pointFibreChernClass sY π S tS
          ((Scheme.Modules.pullback (pointFibreToFamily sY π S tS)).obj N)) n ∧
      n = d • ((Nat.card G : ℚ)⁻¹ • ∑ᶠ g ∈ G,
        g (fibreEquivToA π hSA tS ((Tr q).hom (germOf π t₁ hV₁ β)))) := by
  classical
  have hjT' : jT ≫ T₁.ι = openIncl hSA := hjT
  -- the sheet over `tS`, computed in `A`
  let xu : ComplexPoints (T₁.ι ≫ A.ι ≫ curveι T ≫ sY) :=
    ⟨tS.hom ≫ jT, by
      rw [Category.assoc, ← Category.assoc jT, hjT', openIncl_structure]
      exact tS.2⟩
  have hxu : xu.hom ≫ T₁.ι = (toA hSA tS).hom := by
    change (tS.hom ≫ jT) ≫ T₁.ι = tS.hom ≫ openIncl hSA
    rw [Category.assoc, hjT']
  obtain ⟨x', hx', hreal⟩ := exists_sheet_isRealized_transport hS hA hgraph T₁ hT₁ φ L' t' t₁
    ht' V₁ hV₁ β hβ xu (toA hSA tS) hxu q
  have hreal2 := IsRealized.of_toA hSA hreal
  rw [← pointFibreChernClass_sheet_toA hSA φ hjT' x' hx' L'] at hreal2
  -- the base-changed cover
  haveI : IsOpenImmersion jT := by
    haveI : IsOpenImmersion (jT ≫ T₁.ι) := by rw [hjT']; infer_instance
    exact IsOpenImmersion.of_comp jT T₁.ι
  haveI : Smooth (A.ι ≫ curveι T ≫ sY) := hA.smooth
  let u'' := sheetPoint hSA φ hjT' x' hx'
  haveI : Nonempty (pullback φ jT : Scheme.{0}) := ⟨u''.hom.base default⟩
  haveI := connectedSpace_pullback_of_etale (sY := sY) φ jT
  obtain ⟨W0, hW0, α0, h1, h2⟩ := hreal2
  obtain ⟨V, hV, α, ⟨hinv, hres⟩, hgerm⟩ :=
    pointFibreChernClass_normInvertible_eq_smul_average sY Θ T π hS S hS2 tS G hG hGfin
      (pullback.snd φ jT) u'' (sheetPoint_snd hSA φ hjT' x' hx')
      ((Scheme.Modules.pullback (coverFamilyToA π hSA φ hjT')).obj L') inferInstance
      (sheetι (π := π) (To := S) (t := tS) (φ := pullback.snd φ jT)
        ⟨u'', sheetPoint_snd hSA φ hjT' x' hx'⟩)
      (sheetι_comp_fst _) (pullback.lift_snd _ _ _) _ ⟨W0, hW0, α0, ⟨inferInstance, h1⟩, h2⟩
  -- the sheets over `tS` form a finite nonempty set
  have hfin : Finite {t'' : ComplexPoints (pullback.snd φ jT ≫ S.ι ≫ curveι T ≫ sY) //
      t''.hom ≫ pullback.snd φ jT = tS.hom} := by
    haveI := finite_fibre_realize (pullback.snd φ jT) (sB := S.ι ≫ curveι T ≫ sY) rfl tS
    exact Finite.of_injective (fun e => (⟨e.1, ComplexPoints.ext e.2⟩ :
      {e : ComplexPoints (pullback.snd φ jT ≫ S.ι ≫ curveι T ≫ sY) //
        ComplexPoints.realize (pullback.snd φ jT) rfl e = tS}))
      fun _ _ h => Subtype.ext (congrArg Subtype.val h :)
  haveI : Nonempty {t'' : ComplexPoints (pullback.snd φ jT ≫ S.ι ≫ curveι T ≫ sY) //
      t''.hom ≫ pullback.snd φ jT = tS.hom} := ⟨⟨u'', sheetPoint_snd hSA φ hjT' x' hx'⟩⟩
  refine ⟨_, ?_, _, _, Nat.cast_ne_zero.2 Nat.card_pos.ne', ⟨V, hV, α, hres, rfl⟩, hgerm⟩
  exact @Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible _ _ _ _ _ _
    (Stacks.Divisors.isInvertible_normInvertible _ _ _
      (@Stacks.Divisors.hasTrivializingTargetCover_of_isFinite _ _ _ _ _
        Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible))

end Norms

/-! ### Finite monodromy of the resolution local system -/

section FiniteMonodromy

open MMP.Analytic

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- **Finite orbits of sheet classes.** Let `φ : T' ⟶ T¹` be finite étale over a dense open
`T¹ ⊆ T°`, `𝓛'` an invertible module on `𝓕 ×_{T°} T'`, and `β` a class near `F_{t₁}` restricting
to the class of `𝓛'` on the sheet through a point `t'` over `t₁`. Then the monodromy orbit of the
germ of `β` in `𝒲_{t₁}` is finite: it consists of the classes of `𝓛'` on the sheets over `t₁`. -/
private theorem finite_orbit_sheetClass (hS : IsLocalSetting sY Θ T π)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    {Tr : ∀ {x y : analyticSpace (To.ι ≫ curveι T ≫ sY)}, Path.Homotopic.Quotient x y →
      (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk x ≅
        ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk y)}
    (hgraph : ∀ {x y : analyticSpace (To.ι ≫ curveι T ≫ sY)} (γ : Path x y) w v,
      IsTransportOf (resolutionLocalSystem sY π To) γ w v ↔
        (Tr (Path.Homotopic.Quotient.mk γ)).hom w = v)
    (T₁ : (To : Scheme.{0}).Opens) (hT₁ : Dense (T₁ : Set (To : Scheme.{0})))
    {T' : Scheme.{0}} (φ : T' ⟶ (T₁ : Scheme.{0})) [IsFinite φ] [Etale φ]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) (φ ≫ T₁.ι)).ringCatSheaf.2 L']
    (t' : ComplexPoints (φ ≫ T₁.ι ≫ To.ι ≫ curveι T ≫ sY))
    (t₁ : ComplexPoints (To.ι ≫ curveι T ≫ sY)) (ht' : t'.hom ≫ φ ≫ T₁.ι = t₁.hom)
    (V₁ : Opens (analyticSpace sY)) (hV₁ : curveOpenInclusion sY To t₁ ∈ V₁)
    (β : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V₁) 2)
    [SheafOfModules.IsInvertible (pointFibre sY π To t₁).presheaf
      (pointFibre sY π To t₁).ringCatSheaf.2
      ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π To t₁)
        (pointFibreSnd sY π To t₁ ≫ t'.hom)
        (sheet_w ht'))).obj L')]
    (hβ : (rationalCohomologyMap (pointFibreInclusion sY π To t₁ hV₁) 2).hom β =
      pointFibreChernClass sY π To t₁
        ((Scheme.Modules.pullback (pullback.lift (pointFibreToFamily sY π To t₁)
          (pointFibreSnd sY π To t₁ ≫ t'.hom)
          (sheet_w ht'))).obj L')) :
    {z | ∃ q : Path.Homotopic.Quotient t₁ t₁, (Tr q).hom (germOf π t₁ hV₁ β) = z}.Finite := by
  obtain ⟨Ef, -, htr⟩ := exists_sheet_transport hS hTo hgraph T₁ hT₁ φ L' t' t₁ ht' V₁ hV₁ β hβ
  let u : ComplexPoints (T₁.ι ≫ To.ι ≫ curveι T ≫ sY) :=
    ⟨t'.hom ≫ φ, by simpa only [Category.assoc] using t'.2⟩
  have hu : u.hom ≫ T₁.ι = t₁.hom := (Category.assoc _ _ _).trans ht'
  let F := {e : ComplexPoints ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY) //
    ComplexPoints.realize φ (Category.assoc _ _ _).symm e = u}
  have hF : ∀ e : F, coverPt e.1 = t₁ := fun e => ComplexPoints.ext <| by
    change e.1.hom ≫ φ ≫ T₁.ι = t₁.hom
    rw [← Category.assoc, ← hu]
    exact congrArg (fun z : ComplexPoints (T₁.ι ≫ To.ι ≫ curveι T ≫ sY) => z.hom ≫ T₁.ι) e.2
  haveI : Finite F := finite_fibre_realize φ _ u
  refine (Set.finite_range fun e : F => (((TopCat.Sheaf.forget _ _).obj
    (resolutionLocalSystem sY π To)).stalkCongr (.of_eq (hF e))).hom.hom (Ef e.1)).subset ?_
  rintro _ ⟨q, rfl⟩
  obtain ⟨e, he, hx, hq⟩ := htr u hu q
  exact ⟨⟨e, he⟩, hq.symm⟩

/-- **Finite monodromy at a very general point, hence everywhere.** The set of parallel
transports of `𝒲` along loops at any point `t ∈ T°(ℂ)` is finite. -/
private theorem finite_range_transport (hS : IsLocalSetting sY Θ T π)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    {Tr : ∀ {x y : analyticSpace (To.ι ≫ curveι T ≫ sY)}, Path.Homotopic.Quotient x y →
      (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk x ≅
        ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalk y)}
    (hgraph : ∀ {x y : analyticSpace (To.ι ≫ curveι T ≫ sY)} (γ : Path x y) w v,
      IsTransportOf (resolutionLocalSystem sY π To) γ w v ↔
        (Tr (Path.Homotopic.Quotient.mk γ)).hom w = v)
    (htrans : ∀ {x y z : analyticSpace (To.ι ≫ curveι T ≫ sY)} (γ : Path.Homotopic.Quotient x y)
      (δ : Path.Homotopic.Quotient y z), Tr (γ.trans δ) = Tr γ ≪≫ Tr δ)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    (Set.range fun q : Path.Homotopic.Quotient t t => (Tr q).hom.hom).Finite := by
  classical
  obtain ⟨hlft, hqc, hsep⟩ := curveOpen_structure sY Θ T π hS To
  haveI : Smooth (To.ι ≫ curveι T ≫ sY) := hTo.smooth
  haveI : ConnectedSpace To := hTo.connectedSpace
  haveI : IsIntegral (To : Scheme.{0}) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (To.ι ≫ curveι T ≫ sY)
  have hV : MMP.Mori.IsVariety ℂ (To.ι ≫ curveι T ≫ sY) := ⟨⟩
  haveI := locallyPathConnectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  haveI := connectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  haveI : PathConnectedSpace (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 inferInstance
  obtain ⟨Ω, hΩc, hΩcl, hΩ⟩ :=
    exists_finiteEtaleCover_pointFibreChernClass_transport sY Θ T π hS To hTo
  obtain ⟨t₀, ht₀⟩ := exists_complexPoint_notMem_sUnion (To.ι ≫ curveι T ≫ sY) hV t Ω hΩc hΩcl
  -- finiteness at `t₀` gives finiteness at `t`, by conjugation
  suffices h₀ : (Set.range fun q : Path.Homotopic.Quotient t₀ t₀ => (Tr q).hom.hom).Finite by
    let δ := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath t t₀)
    refine (h₀.image (fun g => (Tr δ).inv.hom ∘ₗ g ∘ₗ (Tr δ).hom.hom)).subset ?_
    rintro _ ⟨q, rfl⟩
    refine ⟨_, ⟨δ.symm.trans (q.trans δ), rfl⟩, ?_⟩
    dsimp only
    rw [tr_eq_conj htrans q δ]
    rfl
  -- the realized germs at `t₀` span; a finite independent subfamily spans
  haveI := finiteDimensional_stalk_of_isLocalSystem hTo.isLocalSystem_resolution t₀
  obtain ⟨b, hbC, hbspan, hbli⟩ :=
    exists_linearIndependent ℚ {y : resolutionLocalSystemFibre sY π To t₀ |
      ∃ (M : (pointFibre sY π To t₀).Modules)
        (_ : SheafOfModules.IsInvertible (pointFibre sY π To t₀).presheaf
          (pointFibre sY π To t₀).ringCatSheaf.2 M),
        IsRealized (sY := sY) (π := π) (To := To) (t := t₀)
          (pointFibreChernClass sY π To t₀ M) y}
  rw [span_isRealized_eq_top hS hTo t₀] at hbspan
  have hbfin : b.Finite := hbli.setFinite
  haveI : Finite b := hbfin.to_subtype
  -- each realized germ has a finite orbit
  have horb : ∀ c ∈ b, {z | ∃ q : Path.Homotopic.Quotient t₀ t₀, (Tr q).hom c = z}.Finite := by
    intro c hc
    obtain ⟨M, hM, hcM⟩ := hbC hc
    obtain ⟨T₁, hT₁, T', φ, hφf, hφe, hT'c, L', hL', t', t₁, ht', γ, V, hV, α, V₁, hV₁, β, hinv, s,
      hα, hβ, h3, h4⟩ := hΩ t₀ ht₀ M hM
    haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
    haveI : IsProper π := isProper_of_isProjectiveMorphism π hS.isResolution.2.2.2.1
    have hcα : c = germOf π t₀ hV α := hcM.unique ⟨V, hV, α, hα, rfl⟩
    have hγ : (Tr (Path.Homotopic.Quotient.mk γ)).hom c = germOf π t₁ hV₁ β := by
      rw [hcα]
      exact (hgraph γ _ _).1 ⟨s, h3, h4⟩
    have hfin₁ := finite_orbit_sheetClass hS hTo hgraph T₁ hT₁ φ L' t' t₁ ht' V₁ hV₁ β hβ
    refine (hfin₁.image (Tr (Path.Homotopic.Quotient.mk γ)).inv.hom).subset ?_
    rintro _ ⟨q, rfl⟩
    refine ⟨_, ⟨(Path.Homotopic.Quotient.mk γ).symm.trans (q.trans (Path.Homotopic.Quotient.mk γ)),
      rfl⟩, ?_⟩
    dsimp only
    rw [tr_eq_conj htrans q (Path.Homotopic.Quotient.mk γ), ← hγ]
    rfl
  -- a transport is determined by its values on `b`
  have hinj : Set.InjOn (fun (g : resolutionLocalSystemFibre sY π To t₀ →ₗ[ℚ]
      resolutionLocalSystemFibre sY π To t₀) (c : b) => g c)
      (Set.range fun q : Path.Homotopic.Quotient t₀ t₀ => (Tr q).hom.hom) :=
    fun g _ g' _ h => LinearMap.ext_on hbspan fun c hc => congrFun h ⟨c, hc⟩
  refine Set.Finite.of_finite_image ?_ hinj
  refine (Set.Finite.pi (t := fun c : b => {z | ∃ q : Path.Homotopic.Quotient t₀ t₀,
    (Tr q).hom c = z}) fun c => horb c c.2).subset ?_
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  exact fun c _ => ⟨q, rfl⟩

end FiniteMonodromy

/-! ### Assembly -/

section Assembly

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- **Punctured independence from independence at one point.** -/
private theorem isPuncturedIndependent_of_linearIndependent (hS : IsLocalSetting sY Θ T π)
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To) {b : ℕ}
    (N : Fin b → (adaptedFamily π To).Modules)
    [hN : ∀ k, SheafOfModules.IsInvertible (adaptedFamily π To).presheaf
      (adaptedFamily π To).ringCatSheaf.2 (N k)]
    (t₀ : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (n : Fin b → resolutionLocalSystemFibre sY π To t₀)
    (hn : ∀ k, IsRealized (sY := sY) (π := π) (To := To) (t := t₀)
      (pointFibreChernClass sY π To t₀
        ((Scheme.Modules.pullback (pointFibreToFamily sY π To t₀)).obj (N k))) (n k))
    (hli : LinearIndependent ℚ fun k =>
      (localSystemRestrictionFibre sY hS.isBiregular To t₀).hom (n k)) :
    ∃ L : Fin b → (genericFibre π T).Modules,
      (∀ i, SheafOfModules.IsInvertible (genericFibre π T).presheaf
        (genericFibre π T).ringCatSheaf.2 (L i)) ∧
      IsPuncturedIndependent sY hS.isBiregular L := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
  haveI : Smooth (To.ι ≫ curveι T ≫ sY) := hTo.smooth
  haveI : ConnectedSpace To := hTo.connectedSpace
  obtain ⟨hlft, hqc, hsep⟩ := curveOpen_structure sY Θ T π hS To
  haveI : IsIntegral (To : Scheme.{0}) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (To.ι ≫ curveι T ≫ sY)
  obtain ⟨ξ, e⟩ := exists_eq_localSettingGenericPoint To hTo.dense
  choose L hL hiso using fun k => exists_genericFibre_iso (π := π) To ξ e (N k)
  exact ⟨L, hL, To, hTo, N, hN, ⟨ξ, e, hiso⟩,
    fun t => exists_linearIndependent_at hS hTo N t₀ t n hn hli⟩

end Assembly

/-! ### Averaging over a finite monodromy group -/

section Averaging

/-- If a surjection `r` sends every vector of a subspace `I` to the `r`-image of each `G`-translate
of any lift, then `I` lies in the span of the images of the `G`-averages of a spanning family. -/
private theorem le_span_of_average {W V ι : Type*} [AddCommGroup W] [Module ℚ W]
    [AddCommGroup V] [Module ℚ V] (r : W →ₗ[ℚ] V) (hr : Function.Surjective r)
    (G : Set (Module.End ℚ W)) (hGfin : G.Finite) (hGne : G.Nonempty) (c : ι → W)
    (hc : Submodule.span ℚ (Set.range c) = ⊤) (n : ι → W) (d : ι → ℚ) (hd : ∀ i, d i ≠ 0)
    (hn : ∀ i, n i = d i • ((Nat.card G : ℚ)⁻¹ • ∑ᶠ g ∈ G, g (c i)))
    (I : Submodule ℚ V) (hI : ∀ v ∈ I, ∀ w, r w = v → ∀ g ∈ G, r (g w) = v) :
    I ≤ Submodule.span ℚ (Set.range (r ∘ n)) := by
  classical
  let Av : Module.End ℚ W := (Nat.card G : ℚ)⁻¹ • ∑ g ∈ hGfin.toFinset, g
  have hAv : ∀ x, Av x = (Nat.card G : ℚ)⁻¹ • ∑ᶠ g ∈ G, g x := fun x => by
    rw [finsum_mem_eq_finite_toFinset_sum _ hGfin]
    simp [Av, LinearMap.sum_apply]
  have hcard : (Nat.card G : ℚ) ≠ 0 := by
    haveI : Finite G := hGfin.to_subtype
    haveI : Nonempty G := hGne.to_subtype
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hAvc : ∀ i, Av (c i) = (d i)⁻¹ • n i := fun i => by
    rw [hn i, smul_smul, inv_mul_cancel₀ (hd i), one_smul, hAv]
  have hspan : ∀ w, Av w ∈ Submodule.span ℚ (Set.range n) := by
    intro w
    have hw : w ∈ Submodule.span ℚ (Set.range c) := hc ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rw [hAvc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx => simpa using Submodule.smul_mem _ a hx
  intro v hv
  obtain ⟨w, rfl⟩ := hr v
  have hrAv : r (Av w) = r w := by
    simp only [Av, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
    rw [Finset.sum_congr rfl fun g hg => hI _ hv w rfl g (hGfin.mem_toFinset.1 hg),
      Finset.sum_const, ← Nat.card_eq_card_finite_toFinset hGfin, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [← hrAv, Set.range_comp, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem (hspan w)

/-- A set of automorphisms of `V`, each intertwining through a surjection `r` with a member of a
finite set of automorphisms of `W`, is finite. -/
private theorem finite_of_intertwining {W V : Type*} [AddCommGroup W] [Module ℚ W]
    [AddCommGroup V] [Module ℚ V] (r : W →ₗ[ℚ] V) (hr : Function.Surjective r)
    (GW : Set (W ≃ₗ[ℚ] W)) (hGW : GW.Finite) (GV : Set (V ≃ₗ[ℚ] V))
    (h : ∀ g ∈ GV, ∃ g₀ ∈ GW, ∀ w, g (r w) = r (g₀ w)) : GV.Finite := by
  refine (hGW.biUnion (t := fun g₀ => {g : V ≃ₗ[ℚ] V | ∀ w, g (r w) = r (g₀ w)})
    fun g₀ _ => Set.Subsingleton.finite fun g hg g' hg' => ?_).subset fun g hg => ?_
  · refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, rfl⟩ := hr v
    rw [hg w, hg' w]
  · obtain ⟨g₀, hg₀, hgg⟩ := h g hg
    exact Set.mem_biUnion hg₀ hgg

end Averaging

/-- The parallel transports of `𝒲` along loops at a point form a finite set. -/
private theorem exists_finite_monodromy
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hS : IsLocalSetting sY Θ T π) {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    ∃ G : Set (resolutionLocalSystemFibre sY π To t ≃ₗ[ℚ] resolutionLocalSystemFibre sY π To t),
      G.Finite ∧ ∀ γ : Path t t, ∃ g ∈ G, ∀ w v : resolutionLocalSystemFibre sY π To t,
        (∃ s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (resolutionLocalSystem sY π To)).obj.obj (op ⊤)),
          (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
              (resolutionLocalSystem sY π To) 0).hom
            ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
              (.of_eq γ.source.symm)).hom.hom w) =
            (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
              (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                (resolutionLocalSystem sY π To))).germ ⊤ 0 trivial).hom s ∧
          (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
              (resolutionLocalSystem sY π To) 1).hom
            ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
              (.of_eq γ.target.symm)).hom.hom v) =
            (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
              (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                (resolutionLocalSystem sY π To))).germ ⊤ 1 trivial).hom s) ↔
        g w = v := by
  classical
  obtain ⟨hlft, hqc, hsep⟩ := curveOpen_structure sY Θ T π hS To
  haveI := locallyPathConnectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  obtain ⟨Tr, hgraph, htrans⟩ :=
    exists_transport (resolutionLocalSystem sY π To) hTo.isLocalSystem_resolution
  have hfin := finite_range_transport hS hTo hgraph htrans t
  refine ⟨{e | ∃ γ : Path t t, e = (Tr (Path.Homotopic.Quotient.mk γ)).toLinearEquiv}, ?_,
    fun γ => ⟨_, ⟨γ, rfl⟩, fun w v => hgraph γ w v⟩⟩
  refine Set.Finite.subset (Set.Finite.preimage
    (f := fun e : resolutionLocalSystemFibre sY π To t ≃ₗ[ℚ] resolutionLocalSystemFibre sY π To t =>
      (e : resolutionLocalSystemFibre sY π To t →ₗ[ℚ] resolutionLocalSystemFibre sY π To t))
    (fun a _ b _ hab => LinearEquiv.toLinearMap_injective hab) hfin) ?_
  rintro _ ⟨γ, rfl⟩
  exact ⟨Path.Homotopic.Quotient.mk γ, rfl⟩

/-- The monodromy of `𝒲` at a point, as a set of endomorphisms in the form used by the norm
average, is finite, nonempty, and consists of parallel transports. -/
private theorem exists_monodromy_endSet {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {To : (curveScheme T).Opens}
    (tS : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (Gfin : Set (resolutionLocalSystemFibre sY π To tS ≃ₗ[ℚ] resolutionLocalSystemFibre sY π To tS))
    (hGfinite : Gfin.Finite)
    (hGfin : ∀ γ : Path tS tS, ∃ g ∈ Gfin, ∀ w v,
      IsTransportOf (resolutionLocalSystem sY π To) γ w v ↔ g w = v) :
    ∃ G : Set (Module.End ℚ (resolutionLocalSystemFibre sY π To tS)),
      (∀ g, g ∈ G ↔ ∃ γ : Path tS tS,
        ∀ (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (resolutionLocalSystem sY π To)).obj.obj (op ⊤)))
          (w v : resolutionLocalSystemFibre sY π To tS),
          (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
              (resolutionLocalSystem sY π To) 0).hom
              ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
                (.of_eq γ.source.symm)).hom.hom w) =
            (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
              (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                (resolutionLocalSystem sY π To))).germ ⊤ 0 trivial).hom s →
          (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
              (resolutionLocalSystem sY π To) 1).hom
              ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
                (.of_eq γ.target.symm)).hom.hom v) =
            (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
              (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                (resolutionLocalSystem sY π To))).germ ⊤ 1 trivial).hom s →
          g w = v) ∧
      G.Finite ∧ G.Nonempty ∧
      ∀ g ∈ G, ∃ γ : Path tS tS, ∀ w, IsTransportOf (resolutionLocalSystem sY π To) γ w (g w) := by
  refine ⟨{g | _}, fun g => Iff.rfl, ?_, ?_, ?_⟩
  · refine (hGfinite.image fun e => e.toLinearMap).subset ?_
    rintro g ⟨γ, hγ⟩
    obtain ⟨g₀, hg₀, h⟩ := hGfin γ
    refine ⟨g₀, hg₀, (LinearMap.ext fun w => ?_).symm⟩
    obtain ⟨s, h0, h1⟩ := (h w (g₀ w)).2 rfl
    exact hγ s w (g₀ w) h0 h1
  · obtain ⟨g₀, -, h⟩ := hGfin (Path.refl tS)
    exact ⟨g₀.toLinearMap, Path.refl tS, fun s w v h0 h1 => (h w v).1 ⟨s, h0, h1⟩⟩
  · rintro g ⟨γ, hγ⟩
    obtain ⟨g₀, -, h⟩ := hGfin γ
    refine ⟨γ, fun w => ?_⟩
    obtain ⟨s, h0, h1⟩ := (h w (g₀ w)).2 rfl
    rw [hγ s w (g₀ w) h0 h1]
    exact ⟨s, h0, h1⟩

/-- A split epimorphism of sheaves is surjective on stalks. -/
private theorem surjective_stalk_of_isSplitEpi {X : TopCat.{0}}
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (m : F ⟶ G) [IsSplitEpi m] (x : X) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
        ((TopCat.Sheaf.forget _ _).map m)) := by
  intro v
  refine ⟨((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
    ((TopCat.Sheaf.forget _ _).map (section_ m))).hom v, ?_⟩
  change ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      ((TopCat.Sheaf.forget _ _).map (section_ m)) ≫
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      ((TopCat.Sheaf.forget _ _).map m)).hom v = v
  rw [← Functor.map_comp, ← Functor.map_comp, IsSplitEpi.id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- A complex variety has a complex point. -/
private lemma nonempty_complexPoints {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sX] : Nonempty (ComplexPoints sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety ℂ sX›.toIsIntegral
  have : CompactSpace X :=
    ⟨QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := X) isClosed_univ Set.univ_nonempty
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := show LocallyOfFiniteType sX from inferInstance
  obtain ⟨p⟩ : Nonempty (MMP.UnderlyingSpace ℂ X) :=
    ⟨(MMP.UnderlyingSpace.equivClosedPoints X).symm ⟨x, hx⟩⟩
  exact ⟨(ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm p⟩

private theorem solution {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hLS : IsLocalSetting sY Θ T π)
    (To : (curveScheme T).Opens) (hTo : IsLocalSystemOpen sY To) :
    ∃ L : Fin (curveLocalSystemRank sY To) → (genericFibre π T).Modules,
      (∀ i, SheafOfModules.IsInvertible (genericFibre π T).presheaf
        (genericFibre π T).ringCatSheaf.2 (L i)) ∧
      IsPuncturedIndependent sY hLS.isBiregular L := by
  classical
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hLS.isProjectiveVariety.toIsVariety
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hLS.isResolution.2.2.2.1
  -- a `π`-adapted open `A`
  obtain ⟨⟨A, hA⟩, hshrink⟩ := hLS.exists_isAdaptedOpen_and_isAdaptedOpen_of_le
  obtain ⟨hlftA, hqcA, hsepA⟩ := curveOpen_structure sY Θ T π hLS A
  haveI : Smooth (A.ι ≫ curveι T ≫ sY) := hA.smooth
  haveI : ConnectedSpace A := hA.connectedSpace
  haveI : IsIntegral (A : Scheme.{0}) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (A.ι ≫ curveι T ≫ sY)
  have hVA : MMP.Mori.IsVariety ℂ (A.ι ≫ curveι T ≫ sY) := ⟨⟩
  haveI : AlgebraicGeometry.IsVariety ℂ (A.ι ≫ curveι T ≫ sY) := hVA
  -- a very general point `t` of `A`
  obtain ⟨Ω, hΩc, hΩcl, hΩ⟩ :=
    exists_finiteEtaleCover_pointFibreChernClass_transport sY Θ T π hLS A hA
  obtain ⟨t₀⟩ := nonempty_complexPoints (A.ι ≫ curveι T ≫ sY)
  obtain ⟨t, ht⟩ := exists_complexPoint_notMem_sUnion (A.ι ≫ curveι T ≫ sY) hVA t₀ Ω hΩc hΩcl
  haveI := locallyPathConnectedSpace_analyticSpace (A.ι ≫ curveι T ≫ sY)
  haveI := connectedSpace_analyticSpace (A.ι ≫ curveι T ≫ sY)
  haveI : PathConnectedSpace (analyticSpace (A.ι ≫ curveι T ≫ sY)) :=
    pathConnectedSpace_iff_connectedSpace.2 inferInstance
  obtain ⟨TrA, hgraphA, htransA⟩ :=
    exists_transport (resolutionLocalSystem sY π A) hA.isLocalSystem_resolution
  -- a finite basis of `𝒲_t` of germs realizing first Chern classes
  haveI := finiteDimensional_stalk_of_isLocalSystem hA.isLocalSystem_resolution t
  obtain ⟨B, hBC, hBspan, hBli⟩ := exists_linearIndependent ℚ
    {y : resolutionLocalSystemFibre sY π A t |
      ∃ (M : (pointFibre sY π A t).Modules)
        (_ : SheafOfModules.IsInvertible (pointFibre sY π A t).presheaf
          (pointFibre sY π A t).ringCatSheaf.2 M),
        IsRealized (sY := sY) (π := π) (To := A) (t := t) (pointFibreChernClass sY π A t M) y}
  rw [span_isRealized_eq_top hLS hA t] at hBspan
  haveI : Finite B := hBli.setFinite.to_subtype
  choose M hM hMc using fun c : B => hBC c.2
  -- each line bundle spreads over a finite étale cover
  choose T₁ hT₁ T' φ hφf hφe hT'c L' hL' t' t₁ ht' γ V hV α V₁ hV₁ β hinv s hα hβ h3 h4 using
    fun c : B => hΩ t ht (M c) (hM c)
  have hγ : ∀ c : B, (TrA (Path.Homotopic.Quotient.mk (γ c))).hom c =
      germOf π (t₁ c) (hV₁ c) (β c) := fun c => by
    have hcα : (c : resolutionLocalSystemFibre sY π A t) = germOf π t (hV c) (α c) :=
      (hMc c).unique ⟨V c, hV c, α c, hα c, rfl⟩
    rw [hcα]
    exact (hgraphA (γ c) _ _).1 ⟨s c, h3 c, h4 c⟩
  -- the common open `S` over which all the covers live
  let U : (A : Scheme.{0}).Opens := ⨅ c, T₁ c
  have hUd : Dense (U : Set (A : Scheme.{0})) := by
    show Dense ((⨅ c, T₁ c : (A : Scheme.{0}).Opens) : Set (A : Scheme.{0}))
    rw [Opens.coe_iInf]
    exact dense_iInter_of_isOpen_of_finite (fun c => (T₁ c).isOpen) hT₁
  obtain ⟨hSA, hS2⟩ := isAdaptedOpen_image hshrink hA U hUd
  choose jT hjT using fun c : B => exists_lift_image U (T₁ c) (iInf_le T₁ c) hSA
  obtain ⟨hlftS, hqcS, hsepS⟩ := curveOpen_structure sY Θ T π hLS (A.ι ''ᵁ U)
  haveI : Smooth ((A.ι ''ᵁ U).ι ≫ curveι T ≫ sY) := hS2.smooth
  haveI : ConnectedSpace (A.ι ''ᵁ U) := hS2.connectedSpace
  haveI : IsIntegral ((A.ι ''ᵁ U : (curveScheme T).Opens) : Scheme.{0}) :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth ((A.ι ''ᵁ U).ι ≫ curveι T ≫ sY)
  have hVS : MMP.Mori.IsVariety ℂ ((A.ι ''ᵁ U).ι ≫ curveι T ≫ sY) := ⟨⟩
  haveI : AlgebraicGeometry.IsVariety ℂ ((A.ι ''ᵁ U).ι ≫ curveι T ≫ sY) := hVS
  haveI := locallyPathConnectedSpace_analyticSpace ((A.ι ''ᵁ U).ι ≫ curveι T ≫ sY)
  obtain ⟨tS⟩ := nonempty_complexPoints ((A.ι ''ᵁ U).ι ≫ curveι T ≫ sY)
  let ρ : Path t (toA hSA tS) := PathConnectedSpace.somePath _ _
  -- the monodromy of `𝒲` on `S` at `tS`
  obtain ⟨Gfin, hGfinite, hGfin⟩ := exists_finite_monodromy hLS hS2 tS
  obtain ⟨G, hG, hGf, hGne, hGtr⟩ := exists_monodromy_endSet tS Gfin hGfinite hGfin
  -- the transported basis, read in `S`, spans `𝒲_{tS}`
  let Φ : resolutionLocalSystemFibre sY π A t ≃ₗ[ℚ]
      resolutionLocalSystemFibre sY π (A.ι ''ᵁ U) tS :=
    (TrA (Path.Homotopic.Quotient.mk ρ)).toLinearEquiv.trans (fibreEquivToA π hSA tS)
  have hcc : ∀ c : B, fibreEquivToA π hSA tS
      ((TrA ((Path.Homotopic.Quotient.mk (γ c)).symm.trans (Path.Homotopic.Quotient.mk ρ))).hom
        (germOf π (t₁ c) (hV₁ c) (β c))) = Φ c := by
    intro c
    change _ = fibreEquivToA π hSA tS ((TrA (Path.Homotopic.Quotient.mk ρ)).hom c)
    rw [htransA, tr_symm htransA, ← hγ c]
    simp
  have hspanS : Submodule.span ℚ (Set.range fun c : B => Φ c) = ⊤ := by
    have e : (Set.range fun c : B => Φ c) = (Φ.toLinearMap : _ → _) '' B := by
      ext x
      simp
    rw [e, Submodule.span_image, hBspan, Submodule.map_top]
    exact LinearEquiv.range Φ
  -- the norm classes
  have hnorm := fun c : B => by
    haveI := hφf c
    haveI := hφe c
    haveI := hT'c c
    haveI := hL' c
    haveI := hinv c
    exact exists_norm_class hLS hA hSA hS2 tS G hG hGf hgraphA (T₁ c) (hT₁ c) (φ c) (L' c)
      (t' c) (t₁ c) (ht' c) (V₁ c) (hV₁ c) (β c) (hβ c) (jT c) (hjT c)
      ((Path.Homotopic.Quotient.mk (γ c)).symm.trans (Path.Homotopic.Quotient.mk ρ))
  choose N hN n d hd hnreal hneq using hnorm
  -- the restriction `r` and the monodromy of `𝒱_T`
  let r := (localSystemRestrictionFibre sY hLS.isBiregular (A.ι ''ᵁ U) tS).hom
  have hrs : Function.Surjective r := by
    haveI := isSplitEpi_localSystemRestriction hLS hS2
    exact surjective_stalk_of_isSplitEpi
      (localSystemRestriction sY hLS.isBiregular (A.ι ''ᵁ U)) tS
  obtain ⟨TrV, hgV, -⟩ :=
    exists_transport (curveLocalSystem sY (A.ι ''ᵁ U)) hS2.isLocalSystem
  let GV : Set (curveLocalSystemFibre sY (A.ι ''ᵁ U) tS ≃ₗ[ℚ]
      curveLocalSystemFibre sY (A.ι ''ᵁ U) tS) :=
    {g | ∃ γ : Path tS tS, ∀ w v,
      IsTransportOf (curveLocalSystem sY (A.ι ''ᵁ U)) γ w v ↔ g w = v}
  have hGVfin : GV.Finite := by
    refine finite_of_intertwining r hrs Gfin hGfinite GV fun g hg => ?_
    obtain ⟨γ', hγ'⟩ := hg
    obtain ⟨g₀, hg₀, h⟩ := hGfin γ'
    refine ⟨g₀, hg₀, fun w => (hγ' (r w) (r (g₀ w))).1 ?_⟩
    exact IsTransportOf.map (localSystemRestriction sY hLS.isBiregular (A.ι ''ᵁ U))
      ((h w (g₀ w)).2 rfl)
  have hY : MMP.Mori.IsVariety ℂ sY := hLS.isProjectiveVariety.toIsVariety
  have hrank := (IsLocalSystemOpen.curveLocalSystemRank_eq hY hLS.topologicalKrullDim_eq
    hLS.topologicalKrullDim_curve hLS.subset_singularLocus hTo hS2.toIsLocalSystemOpen).1.trans
    (IsLocalSystemOpen.curveLocalSystemRank_eq_finrank_invariants hY hLS.topologicalKrullDim_eq
      hLS.topologicalKrullDim_curve hLS.subset_singularLocus hS2.toIsLocalSystemOpen tS GV
      (fun g => Iff.rfl) hGVfin)
  -- the invariants lie in the span of the images of the norm classes
  have hI := le_span_of_average r hrs G hGf hGne (fun c : B => Φ c) hspanS n d hd
    (fun c => (hneq c).trans (by rw [hcc c]))
    (⨅ g ∈ GV, LinearMap.ker ((g : curveLocalSystemFibre sY (A.ι ''ᵁ U) tS →ₗ[ℚ]
      curveLocalSystemFibre sY (A.ι ''ᵁ U) tS) - LinearMap.id)) (by
      intro v hv w hw g hg
      obtain ⟨γ', hγ'⟩ := hGtr g hg
      have h1 := (hgV γ' _ _).1 ((hγ' w).map (localSystemRestriction sY hLS.isBiregular
        (A.ι ''ᵁ U)))
      have hmem : (TrV (Path.Homotopic.Quotient.mk γ')).toLinearEquiv ∈ GV :=
        ⟨γ', fun w v => hgV γ' w v⟩
      have h2 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hv _) hmem
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
      have h1' : (TrV (Path.Homotopic.Quotient.mk γ')).hom (r w) = r (g w) := h1
      change r (g w) = v
      rw [← h1', hw]
      exact h2)
  haveI := finiteDimensional_stalk_of_isLocalSystem hS2.isLocalSystem tS
  obtain ⟨f, hf⟩ := exists_linearIndependent_comp_of_le_span (fun c : B => r (n c)) _ hI
  rw [hrank]
  haveI : ∀ k, SheafOfModules.IsInvertible (adaptedFamily π (A.ι ''ᵁ U)).presheaf
      (adaptedFamily π (A.ι ''ᵁ U)).ringCatSheaf.2 (N (f k)) := fun k => hN (f k)
  exact isPuncturedIndependent_of_linearIndependent hLS hS2 (fun k => N (f k)) tS
    (fun k => n (f k)) (fun k => hnreal (f k)) hf

end Proof_lem_oai4_local_generic_lines

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- **Generic line bundles.** In a local setting `(Y, Θ, T, π)`, for every local-system open
`T°` of `T` there is a punctured-independent family of `b_T = curveLocalSystemRank sY T°` line
bundles on the generic scheme fibre `F_{η_T} = genericFibre π T`. -/
@[mmp "lem_oai4_local_generic_lines"]
public theorem IsLocalSetting.exists_isPuncturedIndependent (hLS : IsLocalSetting sY Θ T π)
    (To : (curveScheme T).Opens) (hTo : IsLocalSystemOpen sY To) :
    ∃ L : Fin (curveLocalSystemRank sY To) → (genericFibre π T).Modules,
      (∀ i, SheafOfModules.IsInvertible (genericFibre π T).presheaf
        (genericFibre π T).ringCatSheaf.2 (L i)) ∧
      IsPuncturedIndependent sY hLS.isBiregular L :=
  Proof_lem_oai4_local_generic_lines.solution hLS To hTo

end MMP.Fourfold
