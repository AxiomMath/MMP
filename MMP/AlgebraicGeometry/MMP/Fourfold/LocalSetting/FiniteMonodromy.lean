module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles
public import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
public import MMP.AlgebraicGeometry.Analytic.Curve.TopCompactCohomology
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.NormChernAverage
public import MMP.AlgebraicGeometry.Analytic.SmoothHolomorphicCharts
public import MMP.AlgebraicGeometry.Analytic.SchemeManifoldDescent
public import MMP.AlgebraicGeometry.Analytic.ComplexRealizationHausdorff
public import MMP.AlgebraicGeometry.Resolution.TransformRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FibreChernClassSpan

/-!
# Finite monodromy of the resolution local system

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`) and `T° ⊆ T` a
`π`-adapted open (`MMP.Fourfold.IsAdaptedOpen`), so that `𝒲 = (R²π_* ℚ_Ỹ)|_{T°}`
(`MMP.Fourfold.resolutionLocalSystem`) is a local system on `T°(ℂ)`. For every point
`t ∈ T°(ℂ)` the image `G` of the monodromy representation `π₁(T°, t) ⟶ GL(𝒲_t)` is finite.

The proof moves the base point off a countable union `Ω` of proper closed subsets of `T°`,
spans `𝒲_t` by first Chern classes of line bundles on the fibre `F_t`, spreads each line bundle
over a connected finite étale cover of a dense open of `T°`, and observes that the finite-index
subgroup of loops lifting to closed loops fixes the corresponding class; the intersection of
these finitely many finite-index stabilizers acts trivially on `𝒲_t`.

## Main results

* `MMP.Fourfold.IsAdaptedOpen.resolutionMonodromy`: the monodromy of `𝒲` at `t`, sending a loop
  class to the linear automorphism of `𝒲_t` given by parallel transport along it.
* `MMP.Fourfold.IsLocalSetting.finite_range_resolutionMonodromy_and_isTransportOf_iff`: the
  monodromy has finite range, and along every loop it is parallel transport.

## Implementation notes

* The action of a loop `γ` at `t` on `𝒲_t` is parallel transport: `γ·w = v` exactly when some
  global section of the inverse image `γ^* 𝒲` on `[0, 1]` has germ `w` at `0` and germ `v` at
  `1`, fibres of `γ^* 𝒲` being identified with those of `𝒲` by
  `MMP.Fourfold.stalkToPullbackStalk`, as in
  `MMP.Fourfold.IsLocalSystemOpen.curveLocalSystemRank_eq`.
* Finiteness of the image in `GL(𝒲_t)` is stated as finiteness of the range of the monodromy,
  together with the fact that along every loop the transport relation is the graph of the
  monodromy of its class.
* The closed points of `T°` are its `ℂ`-points, the points of `T°(ℂ)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite

namespace MMP.Fourfold

/-! ## Line bundles on very general fibres spread over finite étale covers -/

section CoverLineBundle

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open Topology MMP MMP.UnderlyingSpace

/-! ### Germs of inverse images -/

section Transport

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)

private theorem exists_section_of_local
    (y : ∀ x : X, ToType (((TopCat.Sheaf.forget _ Y).obj F).stalk (f x)))
    (hy : ∀ x₀ : X, ∃ (W : Opens Y) (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W)))
      (N : Opens X) (_ : x₀ ∈ N) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), y x = ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) (hNW hx) r) :
    ∃ s : ToType (((TopCat.Sheaf.forget _ X).obj (Pb f F)).obj (op ⊤)), ∀ x,
      ((TopCat.Sheaf.forget _ X).obj (Pb f F)).germ ⊤ x trivial s =
        (stalkToPullbackStalk f F x).hom (y x) := by
  choose W r N hN hNW hloc using hy
  set P := (TopCat.Sheaf.forget _ X).obj (Pb f F)
  let sf : ∀ i : X, ToType (P.obj (op (N i))) := fun i =>
    P.map (homOfLE (hNW i)).op (unitSec f F (r i))
  have hgerm : ∀ i x (hx : x ∈ N i), P.germ (N i) x hx (sf i) =
      (stalkToPullbackStalk f F x).hom (y x) := by
    intro i x hx
    rw [TopCat.Presheaf.germ_res_apply, hloc i x hx]
    exact (stalkToPullbackStalk_germ f F (r i) x _).symm
  have hcompat : TopCat.Presheaf.IsCompatible P N sf := by
    intro i j
    refine TopCat.Presheaf.section_ext (Pb f F) _ _ _ fun x hx => ?_
    change P.germ _ x hx _ = P.germ _ x hx _
    have h1 := TopCat.Presheaf.germ_res_apply P ((N i).infLELeft (N j)) x hx (sf i)
    have h2 := TopCat.Presheaf.germ_res_apply P ((N i).infLERight (N j)) x hx (sf j)
    rw [h1, h2, hgerm, hgerm]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (Pb f F) N ⊤ (fun i => homOfLE le_top)
    (fun x _ => Opens.mem_iSup.2 ⟨x, hN x⟩) sf hcompat
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

variable {V : TopCat.{0}}

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
  refine ⟨e, (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map φ.hom)).1 ?_⟩
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := (TopCat.Sheaf.forget _ V).obj G) ⊤ p
    (Opens.mem_top p) φ.hom _).trans (Eq.trans ?_ he)
  change (ConcreteCategory.hom (((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ ⊤ p _))
    ((φ.inv.app (op ⊤) ≫ φ.hom.app (op ⊤)).hom (constSection E e)) = _
  rw [← NatTrans.comp_app, φ.inv_hom_id]
  rfl

variable {M : TopCat.{0}} (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M)

/-- `v` is the parallel transport of `w` along `γ`: some global section of `γ^* 𝓛` has germ `w`
at `0` and germ `v` at `1`, fibres of `γ^* 𝓛` being identified with those of `𝓛` by
`MMP.Fourfold.stalkToPullbackStalk`. -/
def IsTransportOf {x y : M} (γ : Path x y)
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

/-- **Graph of parallel transport.** On a locally path connected space, `v` is the transport of
`w` along `γ` (`MMP.Fourfold.IsTransportOf`) exactly when the parallel transport
`IsLocalSystem.parallelTransport` along the class of `γ` sends `w` to `v`. -/
private theorem isTransportOf_iff_parallelTransport [LocallyPathConnectedSpace M]
    (h𝓛 : IsLocalSystem 𝓛) {x y : M} (γ : Path x y) (w : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x)
    (v : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk y) :
    IsTransportOf 𝓛 γ w v ↔ (h𝓛.parallelTransport (Path.Homotopic.Quotient.mk γ)).hom w = v := by
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  haveI := isIso_stalkToPullbackStalk Γ 𝓛 1
  have hinj : Function.Injective (stalkToPullbackStalk Γ 𝓛 1).hom :=
    (ConcreteCategory.bijective_of_isIso (stalkToPullbackStalk Γ 𝓛 1)).1
  constructor
  · rintro ⟨s, h0, h1⟩
    have h1' := h𝓛.parallelTransport_germ γ s w
      (by rw [← stalkCongr_eq_cast (L := 𝓛) γ.source.symm]; exact h0)
    rw [← stalkCongr_eq_cast (L := 𝓛) γ.target.symm] at h1'
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
      (by rw [← stalkCongr_eq_cast (L := 𝓛) γ.source.symm]; exact hs.symm)
    rwa [← stalkCongr_eq_cast (L := 𝓛) γ.target.symm] at h1'

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
    _ = _ := by rw [← h]; simp

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
    haveI : IsClosedImmersion (x ≫ sY) := by rw [hxs]; infer_instance
    haveI : IsClosedImmersion x := IsClosedImmersion.of_comp x sY
    have hr : Set.range x.base = {σ.1} := by
      ext q
      constructor
      · rintro ⟨p, rfl⟩
        rw [Subsingleton.elim p p₀, hσ]
        rfl
      · rintro rfl
        exact ⟨p₀, hσ.symm⟩
    rw [← hr]
    exact x.isClosedEmbedding.isClosed_range
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
  have eq₂ : x ≫ 𝟙 Y = Spec.map σ.2 ≫ Y.fromSpecResidueField σ.1 := by
    rw [Category.comp_id, hfac]
  let m : pointFibre sY π To t ⟶ pointSettingFibre π σ.1 :=
    pullback.map π x π (Y.fromSpecResidueField σ.1) (𝟙 Yt) (Spec.map σ.2) (𝟙 Y) (by simp) eq₂
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

/-- The two components of the sheet `F_{t₁} × {t'} ⟶ 𝓕 ×_{T°} T'` agree over `T°`. -/
private theorem sheet_w {To : (curveScheme T).Opens} {T₁ : (To : Scheme.{0}).Opens}
    {T' : Scheme.{0}} {φ : T' ⟶ (T₁ : Scheme.{0})}
    {t' : ComplexPoints (φ ≫ T₁.ι ≫ To.ι ≫ curveι T ≫ sY)}
    {t₁ : ComplexPoints (To.ι ≫ curveι T ≫ sY)} (ht' : t'.hom ≫ φ ≫ T₁.ι = t₁.hom) :
    pointFibreToFamily sY π To t₁ ≫ pullback.snd π (To.ι ≫ curveι T) =
      (pointFibreSnd sY π To t₁ ≫ t'.hom) ≫ φ ≫ T₁.ι := by
  rw [Category.assoc, ht']
  exact pullback.lift_snd _ _ _

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
  have hsurj := surjective_fundamentalGroupMap_realize_ι_of_dense
    (To.ι ≫ curveι T ≫ sY) hV T₁ hT₁ u
  subst hu
  -- the sheets over `t₁`
  have hF : ∀ e'' : {e'' : ComplexPoints ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY) // p e'' = u},
      analyticMap (φ ≫ T₁.ι) (sY := To.ι ≫ curveι T ≫ sY) rfl e''.1 = f u := fun e'' =>
    ComplexPoints.ext (by
      change e''.1.hom ≫ φ ≫ T₁.ι = u.hom ≫ T₁.ι
      rw [← Category.assoc]
      exact congrArg (fun z : ComplexPoints (T₁.ι ≫ To.ι ≫ curveι T ≫ sY) => z.hom ≫ T₁.ι) e''.2)
  haveI := finite_fibre_realize φ hφ u
  refine (Set.finite_range (fun e'' : {e'' : ComplexPoints ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY) //
      p e'' = u} => (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
        (.of_eq (hF e''))).hom.hom (Ef e''.1))).subset ?_
  rintro _ ⟨q, rfl⟩
  -- a loop in `T¹(ℂ)` homotopic to `q`
  obtain ⟨h, hh⟩ := hsurj (FundamentalGroup.fromPath q)
  obtain ⟨δ, hδ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath h)
  have hq : q = Path.Homotopic.Quotient.mk (δ.map f.continuous) := by
    have : FundamentalGroup.map f u (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)) =
        FundamentalGroup.fromPath q := by
      rwa [hδ]
    exact (congrArg FundamentalGroup.toPath this).symm
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
  have h1 : analyticMap (φ ≫ T₁.ι) (sY := To.ι ≫ curveι T ≫ sY) rfl (Γ 1) = f u :=
    (hΓ' 1).trans (δ.map f.continuous).target
  have htr := (hgraph _ _ _).1 (isTransportOf_of_lift (𝓛 := resolutionLocalSystem sY π To)
    (E := analyticSpace ((φ ≫ T₁.ι) ≫ To.ι ≫ curveι T ≫ sY))
    (p := analyticMap (φ ≫ T₁.ι) (sY := To.ι ≫ curveι T ≫ sY) rfl) Ef hloc
    (δ.map f.continuous) Γ hΓ' h0 h1)
  have hstart : (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
      (.of_eq h0)).hom.hom (Ef (Γ 0)) = germOf π (f u) hV₁ β :=
    (stalkCongr_congr_point _ _ Ef hΓ0 h0 hc).trans hrel
  refine ⟨⟨Γ 1, (congrFun hΓp 1).trans δ.target⟩, ?_⟩
  rw [hq, ← hstart]
  exact htr.symm

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
  obtain ⟨b, hbC, hbspan, hbli⟩ := exists_linearIndependent ℚ
    {y : resolutionLocalSystemFibre sY π To t₀ |
      ∃ (M : (pointFibre sY π To t₀).Modules)
        (_ : SheafOfModules.IsInvertible (pointFibre sY π To t₀).presheaf
          (pointFibre sY π To t₀).ringCatSheaf.2 M),
        IsRealized (sY := sY) (π := π) (To := To) (t := t₀)
          (pointFibreChernClass sY π To t₀ M) y}
  rw [span_isRealized_eq_top hS hTo t₀] at hbspan
  haveI : Finite b := hbli.setFinite.to_subtype
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

end Monodromy

end CoverLineBundle

end MMP.Fourfold

end

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic.ComplexPoints

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
  {To : (curveScheme T).Opens}

/-- **Monodromy of `𝒲`.** For `t ∈ T°(ℂ)`, the linear automorphism of the fibre `𝒲_t` of
`𝒲 = (R²π_* ℚ_Ỹ)|_{T°}` by which a homotopy class `q` of loops at `t` acts: parallel transport
`IsLocalSystem.parallelTransport` along `q`. Along a loop `γ` its graph is the transport relation
`MMP.Fourfold.IsTransportOf`
(`MMP.Fourfold.IsLocalSetting.isTransportOf_iff_resolutionMonodromy_apply_eq`). -/
public noncomputable def IsAdaptedOpen.resolutionMonodromy (hTo : IsAdaptedOpen sY π To)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (q : Path.Homotopic.Quotient t t) :
    resolutionLocalSystemFibre sY π To t ≃ₗ[ℚ] resolutionLocalSystemFibre sY π To t :=
  (hTo.isLocalSystem_resolution.parallelTransport q).toLinearEquiv

/-- The monodromy of `𝒲` along a loop `γ` is parallel transport along `γ`: `v` is the transport
of `w` along `γ` exactly when the monodromy of the class of `γ` sends `w` to `v`. -/
public theorem IsLocalSetting.isTransportOf_iff_resolutionMonodromy_apply_eq
    (hS : IsLocalSetting sY Θ T π) (hTo : IsAdaptedOpen sY π To)
    {t : analyticSpace (To.ι ≫ curveι T ≫ sY)} (γ : Path t t)
    (w v : resolutionLocalSystemFibre sY π To t) :
    IsTransportOf (resolutionLocalSystem sY π To) γ w v ↔
      hTo.resolutionMonodromy t (Path.Homotopic.Quotient.mk γ) w = v := by
  obtain ⟨hlft, hqc, hsep⟩ := curveOpen_structure sY Θ T π hS To
  haveI := locallyPathConnectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  exact isTransportOf_iff_parallelTransport _ hTo.isLocalSystem_resolution γ w v

/-- The monodromy of `𝒲` at `t ∈ T°(ℂ)` has finite image in `GL(𝒲_t)`. -/
public theorem IsLocalSetting.finite_range_resolutionMonodromy (hS : IsLocalSetting sY Θ T π)
    (hTo : IsAdaptedOpen sY π To) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    (Set.range (hTo.resolutionMonodromy t)).Finite := by
  obtain ⟨hlft, hqc, hsep⟩ := curveOpen_structure sY Θ T π hS To
  haveI := locallyPathConnectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  have hfin := finite_range_transport hS hTo
    (isTransportOf_iff_parallelTransport _ hTo.isLocalSystem_resolution)
    hTo.isLocalSystem_resolution.parallelTransport_trans t
  refine Set.Finite.of_finite_image (f := fun e : resolutionLocalSystemFibre sY π To t ≃ₗ[ℚ]
      resolutionLocalSystemFibre sY π To t =>
      (e : resolutionLocalSystemFibre sY π To t →ₗ[ℚ] resolutionLocalSystemFibre sY π To t))
    (hfin.subset ?_) (fun a _ b _ hab => LinearEquiv.toLinearMap_injective hab)
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  exact ⟨q, rfl⟩

end MMP.Fourfold

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic.ComplexPoints

/-- **Finite monodromy.** Let `(Y, Θ, T, π)` be a local setting and `T° ⊆ T` a `π`-adapted open.
For every point `t ∈ T°(ℂ)` the monodromy of `𝒲 = (R²π_* ℚ_Ỹ)|_{T°}` at `t`
(`MMP.Fourfold.IsAdaptedOpen.resolutionMonodromy`) has finite range, and along every loop `γ`
at `t` it is parallel transport: `v` is the transport of `w` along `γ` (some global section of
`γ^* 𝒲` has germs `w` at `0` and `v` at `1`) if and only if the monodromy of `[γ]` sends `w` to
`v`. That is, the image of `π₁(T°, t)` in `GL(𝒲_t)` is finite. -/
@[mmp "lem_oai4_local_generic_lines_b"]
public theorem IsLocalSetting.finite_range_resolutionMonodromy_and_isTransportOf_iff
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hS : IsLocalSetting sY Θ T π) {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    (Set.range (hTo.resolutionMonodromy t)).Finite ∧
      ∀ (γ : Path t t) (w v : resolutionLocalSystemFibre sY π To t),
        IsTransportOf (resolutionLocalSystem sY π To) γ w v ↔
          hTo.resolutionMonodromy t (Path.Homotopic.Quotient.mk γ) w = v :=
  ⟨hS.finite_range_resolutionMonodromy hTo t,
    hS.isTransportOf_iff_resolutionMonodromy_apply_eq hTo⟩

end MMP.Fourfold
