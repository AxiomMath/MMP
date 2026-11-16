module

import MMP.AlgebraicGeometry.Pullbacks.Over
import MMP.AlgebraicGeometry.Analytic.ComplexScheme.OfProjective
import MMP.AlgebraicGeometry.Curves.NormalizationSmooth
import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible
import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
import MMP.AlgebraicTopology.SingularCohomology.PairSequence.Supports
import MMP.AlgebraicTopology.ComplexProjectiveSpace.Cohomology
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFamilyTriviality
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ExceptionalFibreGeneric
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.AdaptedOpen
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurvePuncturedRestrictionSurjective
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.GenericLocalSystems
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.DualityAntiampleFibre
import MMP.AlgebraicTopology.FundamentalClass.Exists
import MMP.AlgebraicGeometry.Chow.CycleClassTopDegree
import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Iterate
import MMP.AlgebraicTopology.BorelMoore.TopHomologyRestriction
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicTopology.BorelMoore.Connecting
import MMP.AlgebraicGeometry.Analytic.SchemeManifold
import MMP.AlgebraicTopology.BorelMoore.LongExactQuasiIso
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.VerticalKernelBlowup
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SncFibreHomologyThree
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreVanishing
import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Morphisms.Smooth.SmoothFlagParameters
import MMP.AlgebraicGeometry.Singularities.Semismooth.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Divisor.Cartier
import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.PushforwardSmooth
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Divisor.RegularWeilCartier
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.Divisor.SmoothWeilCartier
import MMP.AlgebraicGeometry.Analytic.CartierDivisorDictionary
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import MMP.AlgebraicGeometry.Dimension.HeightCoheight
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# The exact divisor-class sequence at a generic singular curve

Let `r : Z ⟶ Y` be a curve-and-point exceptional model of a normal projective `ℚ`-factorial
terminal complex fourfold, with exceptional divisor `F = ∑ Fᵢ`, and let `T ⊆ Sing Y` be a curve.
Over a small enough adapted open `T° ⊆ T`, the restriction map `r : 𝒲 ⟶ 𝒱_T` from the resolution
local system `𝒲 = (R²r_* ℚ_Z)|_{T°}` (fibre `H²(F_t, ℚ)`) to the punctured local system `𝒱_T`
is onto, and its kernel is a local system `𝒫_T` of permutation type: the stalk at `t` has a basis
indexed by the irreducible components `S` of the fibre `F_t`, the bases at nearby points are
matched by local sections, and the basis vector of `S` maps to the germ of the class of the
exceptional component through `S`, the local piece of `c₁(𝒪_Z(Fᵢ))` for the `Fᵢ` containing `S`.
Dually, `𝒱_T^*` is the annihilator of these classes in `𝒲^*`.

## Main results

* `MMP.Fourfold.IsCurvePointExceptionalModel.exists_exact_localSystemRestriction`.

## Implementation notes

* The class of the exceptional component through `S` is described on a neighbourhood
  `r⁻¹(V)` of `F_t`: it is a class `α ∈ H²(r⁻¹(V); ℚ)` vanishing off a relatively clopen piece
  `G` of `Fᵢ ∩ r⁻¹(V)` which meets `F_t` exactly in `S`, and agreeing with `c₁(𝒪_Z(Fᵢ))` off the
  rest `(Fᵢ ∩ r⁻¹(V)) ∖ G`. By the Thom isomorphism and the injectivity of the sequence this
  determines the germ of `α` at `t`.
* Exactness of the sequence of local systems is stated stalkwise, at every point of `T°(ℂ)`.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MMP Limits
open MMP MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints MMP.Fourfold

namespace Proof_lem_mmp_conductor_curve_local_exact_sequence

section Stalks

variable {X Y : TopCat.{0}}

/-- Naturality of `stalkPushforward` in the presheaf. -/
private theorem stalkPushforward_naturality (f : X ⟶ Y) {F G : X.Presheaf (ModuleCat.{0} ℚ)}
    (φ : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map φ) ≫
        G.stalkPushforward _ f x =
      F.stalkPushforward _ f x ≫ (TopCat.Presheaf.stalkFunctor _ x).map φ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

private theorem higherDirectImageGerm_apply (f : X ⟶ Y) (q : ℕ) {V : Opens Y} (y : Y)
    (hy : y ∈ V) (c : rationalCohomology (preimageSpace f V) q) :
    (higherDirectImageGerm f q y hy).hom c =
      (TopCat.Presheaf.stalkFunctor _ y).map
        (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q))
        ((directImagePresheaf f q).germ V y hy c) := rfl

/-- The germ of a restricted class is the germ of the class. -/
private theorem higherDirectImageGerm_res (f : X ⟶ Y) (q : ℕ) {V W : Opens Y} (hWV : W ≤ V)
    (y : Y) (hy : y ∈ W) (c : rationalCohomology (preimageSpace f V) q) :
    (higherDirectImageGerm f q y hy).hom
        ((rationalCohomologyMap (preimageInclusion f hWV) q).hom c) =
      (higherDirectImageGerm f q y (hWV hy)).hom c := by
  rw [higherDirectImageGerm_apply, higherDirectImageGerm_apply]
  congr 1
  exact TopCat.Presheaf.germ_res_apply (directImagePresheaf f q) (homOfLE hWV) y hy c

/-- A class whose germ in `R^q f_* ℚ` vanishes restricts to zero on a smaller neighbourhood. -/
private theorem exists_res_eq_zero_of_germ_eq_zero (f : X ⟶ Y) (q : ℕ) {V : Opens Y} (y : Y)
    (hy : y ∈ V) (c : rationalCohomology (preimageSpace f V) q)
    (hc : (higherDirectImageGerm f q y hy).hom c = 0) :
    ∃ (W : Opens Y) (_ : y ∈ W) (hWV : W ≤ V),
      (rationalCohomologyMap (preimageInclusion f hWV) q).hom c = 0 := by
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (C := ModuleCat.{0} ℚ)
    (𝓕 := directImagePresheaf f q) (p₀ := y)
  have hinj : Function.Injective ((TopCat.Presheaf.stalkFunctor _ y).map
      (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q))) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have h0 : (directImagePresheaf f q).germ V y hy c = (directImagePresheaf f q).germ V y hy 0 := by
    apply hinj
    rw [higherDirectImageGerm_apply] at hc
    rw [hc, map_zero]
    exact (map_zero (ModuleCat.Hom.hom ((TopCat.Presheaf.stalkFunctor _ y).map
      (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q))))).symm
  obtain ⟨W, hyW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq (directImagePresheaf f q) y hy hy c 0 h0
  refine ⟨W, hyW, iU.le, ?_⟩
  exact e.trans (map_zero _)

/-- Naturality of `stalkToPullbackStalk` in the sheaf. -/
private theorem stalkToPullbackStalk_naturality (f : X ⟶ Y)
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (φ : F ⟶ G) (x : X) :
    stalkToPullbackStalk f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map
        ((TopCat.Sheaf.forget _ X).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ)) =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Sheaf.forget _ Y).map φ) ≫
        stalkToPullbackStalk f G x := by
  have hn := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.naturality φ
  have hn' : (TopCat.Sheaf.forget _ Y).map φ ≫ (TopCat.Sheaf.forget _ Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app G) =
      (TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F) ≫
        (TopCat.Presheaf.pushforward _ f).map ((TopCat.Sheaf.forget _ X).map
          ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ)) := by
    have := congrArg (fun m ↦ (TopCat.Sheaf.forget _ Y).map m) hn
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at this
    exact this
  unfold stalkToPullbackStalk
  erw [Category.assoc, ← stalkPushforward_naturality f, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← hn', CategoryTheory.Functor.map_comp, Category.assoc]

/-- The map on stalks induced by the sheafification of a morphism of the presheaves
`V ↦ H^q(f⁻¹(V); ℚ)`, on germs of classes. -/
private theorem stalkFunctor_map_presheafToSheaf_germ {X X' : TopCat.{0}} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (q : ℕ) (ψ : directImagePresheaf p q ⟶ directImagePresheaf p' q)
    {V : Opens Y} (y : Y) (hy : y ∈ V) (c : rationalCohomology (preimageSpace p V) q) :
    (TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ Y).map
        ((presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).map ψ))
        ((higherDirectImageGerm p q y hy).hom c) =
      (higherDirectImageGerm p' q y hy).hom (ψ.app (Opposite.op V) c) := by
  have hm : higherDirectImageGerm p q y hy ≫ (TopCat.Presheaf.stalkFunctor _ y).map
      ((TopCat.Sheaf.forget _ Y).map
        ((presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).map ψ)) =
      ψ.app (Opposite.op V) ≫ higherDirectImageGerm p' q y hy := by
    unfold higherDirectImageGerm
    have h := toSheafify_naturality (Opens.grothendieckTopology Y) ψ
    erw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← h, CategoryTheory.Functor.map_comp,
      ← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
  exact ConcreteCategory.congr_hom hm c

end Stalks

/-- The restriction map `r_t` on the germ at `t` of a class on `π⁻¹(V)` is the germ of its
restriction to `π⁻¹(V) ∩ π⁻¹(Y_reg) ≅ j⁻¹(V)`. -/
private theorem localSystemRestrictionFibre_germ {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (hπ : IsBiregular π (smoothLocus sY))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    (localSystemRestrictionFibre sY hπ To t).hom
        ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
          t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)) =
      (stalkToPullbackStalk (curveOpenInclusion sY To) (regularHigherDirectImage sY 2) t).hom
        ((higherDirectImageGerm (regularInclusion sY) 2 _ hV).hom
          ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
            (analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]))
            (regularSection_analyticMap_comp sY hπ) V) 2).hom α)) := by
  have h := ConcreteCategory.congr_hom (stalkToPullbackStalk_naturality
    (curveOpenInclusion sY To) (resolutionRestriction sY hπ 2) t)
    ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  unfold localSystemRestrictionFibre localSystemRestriction
  erw [h]
  exact congrArg (fun z ↦ (stalkToPullbackStalk (curveOpenInclusion sY To)
    (regularHigherDirectImage sY 2) t).hom z)
    (stalkFunctor_map_presheafToSheaf_germ _ _ 2 _ _ hV α)

/-- `stalkPushforward` absorbs a morphism into the pushforward on either side. -/
private lemma stalkPushforward_comp_naturality {X Y : TopCat.{0}} {f : X ⟶ Y}
    {F' : TopCat.Presheaf (ModuleCat.{0} ℚ) Y} {G G' : TopCat.Presheaf (ModuleCat.{0} ℚ) X}
    (u : F' ⟶ (TopCat.Presheaf.pushforward _ f).obj G) (v : G ⟶ G') (x : X) :
    ((TopCat.Presheaf.stalkFunctor _ (f x)).map u ≫ TopCat.Presheaf.stalkPushforward _ f G x) ≫
        (TopCat.Presheaf.stalkFunctor _ x).map v =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map (u ≫ (TopCat.Presheaf.pushforward _ f).map v) ≫
        TopCat.Presheaf.stalkPushforward _ f G' x := by
  refine (Category.assoc _ _ _).trans ?_
  erw [(stalkPushforward_naturality f v x).symm, Functor.map_comp, Category.assoc]
  rfl

/-- The canonical map `F_{f(x)} ⟶ (f⁻¹F)_x` is an isomorphism. -/
private lemma isIso_stalkToPullbackStalk {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) (x : X) : IsIso (stalkToPullbackStalk f F x) := by
  let ι := (TopCat.Sheaf.pullbackIso (ModuleCat.{0} ℚ) f).app F
  have hunit : (TopCat.Sheaf.forget _ Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F ≫
      (TopCat.Sheaf.pushforward _ f).map ι.hom) =
      (TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.forget _ Y).obj F) ≫
        (TopCat.Presheaf.pushforward _ f).map (toSheafify _ _) := by
    have := Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) (ModuleCat.{0} ℚ)
        _ _) F
    have h2 := (sheafToPresheaf _ _).congr_map this
    erw [h2]
    unfold Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    erw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Adjunction.comp_unit_app, Iso.refl_hom, NatTrans.id_app, Functor.map_id,
      Category.comp_id]
    rfl
  have hst : stalkToPullbackStalk f F x ≫
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ι.hom) =
      TopCat.Presheaf.stalkPullbackHom _ f ((TopCat.Sheaf.forget _ Y).obj F) x ≫
        (TopCat.Presheaf.stalkFunctor _ x).map (toSheafify _ _) := by
    have hunit' : (TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F) ≫
        (TopCat.Presheaf.pushforward _ f).map ((TopCat.Sheaf.forget _ X).map ι.hom) =
        (TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.forget _ Y).obj F) ≫
        (TopCat.Presheaf.pushforward _ f).map (toSheafify _ _) := by
      rw [← hunit, Functor.map_comp]
      rfl
    unfold stalkToPullbackStalk TopCat.Presheaf.stalkPullbackHom
    refine (stalkPushforward_comp_naturality _ _ x).trans
      (Eq.trans ?_ (stalkPushforward_comp_naturality _ _ x).symm)
    exact congrArg (fun g ↦ (TopCat.Presheaf.stalkFunctor _ (f x)).map g ≫
      TopCat.Presheaf.stalkPushforward _ f _ x) hunit'
  have h1 : IsIso (TopCat.Presheaf.stalkPullbackHom _ f ((TopCat.Sheaf.forget _ Y).obj F) x) :=
    (TopCat.Presheaf.stalkPullbackIso _ f ((TopCat.Sheaf.forget _ Y).obj F) x).isIso_hom
  have h2 := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ)
    ((TopCat.Presheaf.pullback _ f).obj ((TopCat.Sheaf.forget _ Y).obj F))
  have h3 : IsIso ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ι.hom)) :=
    ((TopCat.Presheaf.stalkFunctor _ x).mapIso ((TopCat.Sheaf.forget _ X).mapIso ι)).isIso_hom
  have : IsIso (stalkToPullbackStalk f F x ≫
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ι.hom)) := by
    rw [hst]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h3 this

/-- The canonical map from the stalk of a sheaf to the stalk of its inverse image is
injective. -/
private theorem injective_stalkToPullbackStalk {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) (x : X) :
    Function.Injective (stalkToPullbackStalk f F x) :=
  haveI := isIso_stalkToPullbackStalk f F x
  ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1

/-! ### Local dimension of smooth schemes -/

universe u in
/-- A smooth morphism is smooth of some relative dimension near every point of the source. -/
private theorem exists_smoothOfRelativeDimension_nbhd {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    letI := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  have h : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  refine ⟨V, hx, n, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

universe u in
/-- A scheme smooth of relative dimension `N` over a field has local dimension `N` everywhere. -/
private theorem topologicalKrullDimAt_eq_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {T : Scheme.{u}} (s : T ⟶ Spec (.of k)) (N : ℕ) [SmoothOfRelativeDimension N s] (t : T) :
    topologicalKrullDimAt T t = N := by
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hpre : s.base ⁻¹' {s.base t} = (Set.univ : Set T) := by
    ext y; simp [Subsingleton.elim (s.base y) (s.base t)]
  let e : s.fiber (s.base t) ≃ₜ T :=
    (s.fiberHomeo _).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ T))
  have he : e (s.asFiber t) = t := s.fiberι_asFiber t
  rw [← he, e.isOpenEmbedding.topologicalKrullDimAt_eq]
  exact fiberDimensionAt_eq_of_smoothOfRelativeDimension s N t

/-- **Fibres of a smooth map between smooth `ℂ`-schemes.** If `W` is smooth of relative
dimension `n + 1` over `ℂ`, `B` smooth of relative dimension one, and `g : W ⟶ B` smooth, then the
fibre of `g` over a `ℂ`-point of `B` has local dimension `n` everywhere: near every point `g` has
some relative dimension `e`, and `e + 1 = n + 1` by comparing local dimensions of `W`. -/
private theorem topologicalKrullDimAt_eq_of_isPullback {W B M₀ : Scheme.{0}}
    (sW : W ⟶ Spec (.of ℂ)) (sB : B ⟶ Spec (.of ℂ)) (g : W ⟶ B) (hg : g ≫ sB = sW) [Smooth g]
    (n : ℕ) [SmoothOfRelativeDimension (n + 1) sW] [SmoothOfRelativeDimension 1 sB]
    (i₀ : M₀ ⟶ W) (s₀ : M₀ ⟶ Spec (.of ℂ)) (b₀ : Spec (.of ℂ) ⟶ B)
    (hpb : IsPullback i₀ s₀ g b₀) (x : M₀) :
    topologicalKrullDimAt M₀ x = n := by
  obtain ⟨V, hxV, e, he⟩ := exists_smoothOfRelativeDimension_nbhd g (i₀ x)
  obtain ⟨v, hv⟩ : i₀ x ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hxV
  have h1 : topologicalKrullDimAt V.toScheme v = ((e + 1 : ℕ) : WithBot ℕ∞) := by
    haveI : SmoothOfRelativeDimension (e + 1) ((V.ι ≫ g) ≫ sB) := inferInstance
    exact topologicalKrullDimAt_eq_of_smoothOfRelativeDimension ((V.ι ≫ g) ≫ sB) (e + 1) v
  have h2 : topologicalKrullDimAt V.toScheme v = ((0 + (n + 1) : ℕ) : WithBot ℕ∞) := by
    haveI : SmoothOfRelativeDimension (0 + (n + 1)) (V.ι ≫ sW) := inferInstance
    exact topologicalKrullDimAt_eq_of_smoothOfRelativeDimension (V.ι ≫ sW) (0 + (n + 1)) v
  have hen : e = n := by
    have := h1.symm.trans h2
    have : (e + 1 : ℕ) = 0 + (n + 1) := by exact_mod_cast this
    omega
  subst hen
  have sqV : IsPullback (i₀ ∣_ V) ((i₀ ⁻¹ᵁ V).ι ≫ s₀) (V.ι ≫ g) b₀ :=
    (isPullback_morphismRestrict i₀ V).paste_vert hpb
  have hdL : SmoothOfRelativeDimension e ((i₀ ⁻¹ᵁ V).ι ≫ s₀) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange e).of_isPullback sqV he
  obtain ⟨z, hz⟩ : x ∈ Set.range (i₀ ⁻¹ᵁ V).ι := by rw [Scheme.Opens.range_ι]; exact hxV
  rw [← hz, (i₀ ⁻¹ᵁ V).ι.isOpenEmbedding.topologicalKrullDimAt_eq z]
  haveI := hdL
  exact topologicalKrullDimAt_eq_of_smoothOfRelativeDimension ((i₀ ⁻¹ᵁ V).ι ≫ s₀) e z

/-- A smooth `ℂ`-scheme of local dimension `n` at every point is smooth of relative
dimension `n`: its fibre over the point of `Spec ℂ` is the whole scheme. -/
private theorem smoothOfRelativeDimension_of_forall_topologicalKrullDimAt {M : Scheme.{0}}
    (s : M ⟶ Spec (.of ℂ)) [Smooth s] (n : ℕ)
    (h : ∀ x, topologicalKrullDimAt M x = ((n : ℕ) : WithBot ℕ∞)) :
    SmoothOfRelativeDimension n s := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq s n fun x ↦ ?_
  have heq : (s ⁻¹' {s x}) = (Set.univ : Set M) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  let e : s.fiber (s x) ≃ₜ M :=
    (s.fiberHomeo (s x)).trans ((Homeomorph.setCongr heq).trans (Homeomorph.Set.univ M))
  rw [topologicalKrullDimAt_eq_of_homeomorph e]
  exact h _

section DegreeRelations

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints MMP.Fourfold

private theorem rationalCohomologyMap_mapCoeff {X' X : TopCat.{0}} (g : X' ⟶ X) (n : ℕ)
    (x : singularCohomology ℤ X n) :
    (rationalCohomologyMap g n).hom (singularCohomology.mapCoeff (Int.castRingHom ℚ) n x) =
      singularCohomology.mapCoeff (Int.castRingHom ℚ) n
        ((relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g
          (fun _ hx ↦ (hx (Set.mem_univ _)).elim) n).hom x) := by
  apply (SingularCochain.relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set X') n).injective
  refine (SingularCochain.relativeSingularCohomologyEquiv_map (R := ℚ) g
    (A := (Set.univᶜ : Set X)) (A' := (Set.univᶜ : Set X'))
    (fun _ hx ↦ (hx (Set.mem_univ _)).elim) n _).trans ?_
  simp only [singularCohomology.mapCoeff, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, LinearEquiv.apply_symm_apply]
  refine Eq.trans ?_ (congrArg _ (SingularCochain.relativeSingularCohomologyEquiv_map (R := ℤ) g
    (A := (Set.univᶜ : Set X)) (A' := (Set.univᶜ : Set X'))
    (fun _ hx ↦ (hx (Set.mem_univ _)).elim) n x).symm)
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective _
    (SingularCochain.relativeSingularCohomologyEquiv ℤ (Set.univᶜ : Set X) n x)
  rw [← hφ]
  rfl

/-- A finite family of rationals has a common positive denominator. -/
private theorem exists_nat_mul_eq_int {ι : Type*} [Fintype ι] (q : ι → ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, ∃ n : ℤ, (n : ℚ) = N * q i := by
  classical
  refine ⟨∏ j, (q j).den, Finset.prod_pos fun j _ ↦ (q j).den_pos, fun i ↦ ?_⟩
  refine ⟨(q i).num * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℤ), ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ (q j).den) (Finset.mem_univ i)]
  push_cast
  rw [← Rat.mul_den_eq_num]
  ring

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X]

/-- The rational first Chern class `D ↦ c₁(𝒪_X(D)) ∈ H²(X^an; ℚ)`, additive on a scheme all of
whose divisors are Cartier. -/
private noncomputable def rationalChernHom (hcart : ∀ D : Divisor X, D.IsCartier) :
    Divisor X →+ singularCohomology ℚ (analyticSpace (X ↘ Spec (.of ℂ))) 2 :=
  AddMonoidHom.mk' (fun B ↦
    haveI := (hcart B).isInvertibleModule_divisorialSheaf
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass B.divisorialSheaf))
    (fun B B' ↦ by
      haveI := (hcart B).isInvertibleModule_divisorialSheaf
      haveI := (hcart B').isInvertibleModule_divisorialSheaf
      haveI := (hcart (B + B')).isInvertibleModule_divisorialSheaf
      haveI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
            B.divisorialSheaf).obj B'.divisorialSheaf) :=
        (hcart B).isInvertibleModule_tensorSheaf (hcart B')
      have e := algebraicFirstChernClass_eq_of_iso ((hcart B).divisorialSheafTensorIso (hcart B'))
      rw [algebraicFirstChernClass_sheafTensor] at e
      simp only [← e, map_add])

private theorem rationalChernHom_apply (hcart : ∀ D : Divisor X, D.IsCartier) (B : Divisor X) :
    haveI := (hcart B).isInvertibleModule_divisorialSheaf
    rationalChernHom hcart B =
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass B.divisorialSheaf) :=
  rfl

/-- The degree `D ↦ deg_ν 𝒪_X(D)` along a curve, additive on a scheme all of whose divisors are
Cartier. -/
private noncomputable def degreeOnHom (hcart : ∀ D : Divisor X, D.IsCartier) {C : Scheme.{0}}
    [QuasiCompact (X ↘ Spec (.of ℂ))] (ν : C ⟶ X) [IsProper (ν ≫ X ↘ Spec (.of ℂ))]
    (hdim : topologicalKrullDim C ≤ 1) : Divisor X →+ ℤ :=
  AddMonoidHom.mk' (fun B ↦ B.degreeOn ℂ (X ↘ Spec (.of ℂ)) ν hdim (hcart B))
    (fun B B' ↦ Divisor.degreeOn_add ℂ _ ν hdim B B' (hcart B) (hcart B'))

/-- **Rational Chern relations on a curve are degree relations.** Let `ν : Γ ⟶ X` be a smooth
projective complex curve mapping to a scheme `X` all of whose divisors are Cartier. If the
pullbacks to `Γ^an` of the rational first Chern classes of `𝒪_X(Bᵢ)` satisfy `∑ qᵢ ν^* c₁ = 0`,
then `∑ qᵢ deg_ν 𝒪_X(Bᵢ) = 0`. -/
private theorem sum_mul_degreeOn_eq_zero (hcart : ∀ D : Divisor X, D.IsCartier)
    [QuasiCompact (X ↘ Spec (.of ℂ))] {Γ : Scheme.{0}} [Γ.Over (Spec (.of ℂ))]
    [IsComplexScheme Γ] [IsIntegral Γ] [IsProper (Γ ↘ Spec (.of ℂ))]
    (hsm : IsSmoothScheme (Γ ↘ Spec (.of ℂ))) (hdim1 : topologicalKrullDim Γ = 1)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (Γ ↘ Spec (.of ℂ))) (ν : Γ ⟶ X)
    (hν : ν ≫ X ↘ Spec (.of ℂ) = Γ ↘ Spec (.of ℂ)) {ι : Type*} [Fintype ι] (B : ι → Divisor X)
    (q : ι → ℚ)
    (h : ∑ i, q i • (rationalCohomologyMap (analyticMap ν hν) 2).hom
      (rationalChernHom hcart (B i)) = 0) :
    haveI : IsProper (ν ≫ X ↘ Spec (.of ℂ)) := by rw [hν]; infer_instance
    ∑ i, q i * (degreeOnHom hcart ν hdim1.le (B i) : ℚ) = 0 := by
  classical
  haveI : IsProper (ν ≫ X ↘ Spec (.of ℂ)) := by rw [hν]; infer_instance
  obtain ⟨N, hN, hn⟩ := exists_nat_mul_eq_int q
  choose n hn using hn
  set B' := ∑ i, n i • B i
  haveI := (hcart B').isInvertibleModule_divisorialSheaf
  -- the Chern class of `ν^* 𝒪(B')` vanishes
  have hc : singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass ((Scheme.Modules.pullback ν).obj B'.divisorialSheaf)) = 0 := by
    rw [algebraicFirstChernClass_pullback ν (analyticMap ν hν) (fun _ ↦ rfl)]
    refine Eq.trans (rationalCohomologyMap_mapCoeff (analyticMap ν hν) 2 _).symm ?_
    change (rationalCohomologyMap (analyticMap ν hν) 2).hom (rationalChernHom hcart B') = 0
    simp only [B', map_sum, map_zsmul]
    have : ∀ i, n i • (rationalCohomologyMap (analyticMap ν hν) 2).hom
        (rationalChernHom hcart (B i)) = (N : ℚ) • (q i • (rationalCohomologyMap
          (analyticMap ν hν) 2).hom (rationalChernHom hcart (B i))) := by
      intro i
      rw [← Int.cast_smul_eq_zsmul ℚ, hn i, smul_smul]
    simp only [this, ← Finset.smul_sum, h, smul_zero]
  have h0 := invertibleCurveDegree_eq_zero_of_mapCoeff_algebraicFirstChernClass_eq_zero hsm hdim1
    hproj _ hc
  have hdeg : degreeOnHom hcart ν hdim1.le B' = 0 := by
    change Mori.degreeOn ℂ (X ↘ Spec (.of ℂ)) ν hdim1.le B'.divisorialSheaf = 0
    rw [Mori.degreeOn_eq_invertibleCurveDegree, invertibleCurveDegree_congr_structure hν]
    exact h0
  simp only [B', map_sum, map_zsmul, smul_eq_mul] at hdeg
  have hdeg' : ((∑ i, n i * degreeOnHom hcart ν hdim1.le (B i) : ℤ) : ℚ) = 0 := by
    exact_mod_cast hdeg
  push_cast at hdeg'
  simp only [hn, mul_assoc, ← Finset.mul_sum] at hdeg'
  rcases mul_eq_zero.1 hdeg' with h | h
  · exact absurd h (by exact_mod_cast hN.ne')
  · exact h

end DegreeRelations

section TestCurve

open MMP.Mori MMP.Fourfold

/-- **Smooth projective test curves.** Let `X` be a locally Noetherian projective scheme over
`ℂ`, `η ⤳ p` a generization of a closed point `p` and `Z ∋ p` a closed set not containing `η`.
There is a smooth projective complex curve `Γ` with a finite morphism `ν : Γ ⟶ X` over `ℂ`,
not constant, whose image lies in `{η}⁻` and is not contained in `Z`: the normalization of a
proper curve through `p` in `{η}⁻` not contained in `Z`. -/
private theorem exists_smooth_projective_curve {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsProper (X ↘ Spec (.of ℂ))] (hproj : IsProjectiveMorphism (X ↘ Spec (.of ℂ)))
    [IsLocallyNoetherian X] {η p : X} (hηp : η ⤳ p) (hp : IsClosed ({p} : Set X)) {Zc : Set X}
    (hZ : IsClosed Zc) (hpZ : p ∈ Zc) (hηZ : η ∉ Zc) :
    ∃ (Γ : Scheme.{0}) (_ : Γ.Over (Spec (.of ℂ))) (ν : Γ ⟶ X),
      ν ≫ X ↘ Spec (.of ℂ) = Γ ↘ Spec (.of ℂ) ∧ IsComplexScheme Γ ∧ IsIntegral Γ ∧
      IsProper (Γ ↘ Spec (.of ℂ)) ∧ IsSmoothScheme (Γ ↘ Spec (.of ℂ)) ∧
      topologicalKrullDim Γ = 1 ∧ MMP.Mori.IsProjectiveVariety ℂ (Γ ↘ Spec (.of ℂ)) ∧
      IsFinite ν ∧ (∀ c, η ⤳ ν c) ∧ (∃ c, ν c ∉ Zc) ∧ ¬ ∃ x : X, Set.range ν = {x} := by
  obtain ⟨y, hηy, -, hyZ, hy⟩ := exists_isProperCurve_of_specializes (X ↘ Spec (.of ℂ)) hηp hp hZ
    hpZ hηZ
  set ι := curveSubschemeAtι y
  haveI : IsIntegral (curveSubschemeAt y) :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
      isIrreducible_singleton.closure
  haveI : IsProper (ι ≫ X ↘ Spec (.of ℂ)) := hy.isProper
  haveI : AlgebraicGeometry.IsCurve ℂ (ι ≫ X ↘ Spec (.of ℂ)) :=
    { toIsIntegral := inferInstance
      toIsSeparated := inferInstance
      toLocallyOfFiniteType := inferInstance
      toQuasiCompact := inferInstance
      topologicalKrullDim_eq_one := hy.dim_eq }
  obtain ⟨Γ, _, ν₀, hfin, hsurj, hν₀, hcur, hsm, hpr⟩ :=
    MMP.exists_smoothOfRelativeDimension_isFinite_surjective_of_isCurve ℂ (ι ≫ X ↘ Spec (.of ℂ))
  have hdim := hcur.topologicalKrullDim_eq_one
  haveI := hfin
  have hpr' := hpr (by
    obtain ⟨n, i, hi, h⟩ := hproj
    haveI := hi
    exact ⟨n, ι ≫ i, inferInstance, by rw [Category.assoc, h]⟩)
  haveI : IsIntegral Γ := hcur.toIsIntegral
  have hrange : Set.range ι = closure ({y} : Set X) := by
    simp only [ι, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_closure]
  haveI : SmoothOfRelativeDimension 1 (Γ ↘ Spec (.of ℂ)) := hsm
  haveI : Smooth (Γ ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 1 _
  haveI : IsProper (Γ ↘ Spec (.of ℂ)) := by rw [← hν₀]; infer_instance
  refine ⟨Γ, inferInstance, ν₀ ≫ ι, by rw [Category.assoc, hν₀],
    MMP.Analytic.isComplexScheme_of_isProjective Γ
      ((isProjective_iff_isProjectiveMorphism_of_isAffine _).2 hpr'), inferInstance, inferInstance, (MMP.Mori.isSmoothScheme_iff _).2 inferInstance, ?_, ?_,
    inferInstance, ?_, ?_, ?_⟩
  · exact_mod_cast hdim
  · rw [MMP.Mori.isProjectiveVariety_iff]
    exact ⟨(MMP.Mori.isVariety_iff ℂ _).2 ⟨inferInstance, inferInstance, inferInstance,
      inferInstance⟩, hpr'⟩
  · intro c
    have : ι (ν₀ c) ∈ closure ({y} : Set X) := hrange ▸ ⟨_, rfl⟩
    exact hηy.trans (specializes_iff_mem_closure.2 this)
  · obtain ⟨c₀, hc₀⟩ : y ∈ Set.range ι := hrange ▸ subset_closure rfl
    obtain ⟨c, hc⟩ := hsurj.surj c₀
    exact ⟨c, by rw [Scheme.Hom.comp_apply, hc, hc₀]; exact hyZ⟩
  · rintro ⟨x, hx⟩
    have hsub : Subsingleton (curveSubschemeAt y) := by
      refine ⟨fun a b ↦ ι.isClosedEmbedding.injective ?_⟩
      obtain ⟨a', rfl⟩ := hsurj.surj a
      obtain ⟨b', rfl⟩ := hsurj.surj b
      have ha : (ν₀ ≫ ι) a' ∈ Set.range (ν₀ ≫ ι) := ⟨a', rfl⟩
      have hb : (ν₀ ≫ ι) b' ∈ Set.range (ν₀ ≫ ι) := ⟨b', rfl⟩
      rw [hx] at ha hb
      exact (ha.trans hb.symm)
    have h0 : topologicalKrullDim (curveSubschemeAt y) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hy.dim_eq] at h0
    exact absurd h0 (by decide)

end TestCurve

section RelativelyAmple

open MMP.Mori RingedSpaceModuleAdjunction

/-- A morphism whose composite with a separated morphism is finite is finite. -/
private theorem isFinite_of_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) [h : IsFinite (f ≫ g)]
    [IsSeparated g] : IsFinite f := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType] at h ⊢
  obtain ⟨h1, h2⟩ := h
  exact ⟨IsIntegralHom.of_comp f g, locallyOfFiniteType_of_comp f g⟩

/-- **A relatively ample sheaf is positive along a finite map from a contracted curve.** Let
`g : X ⟶ Y` be a morphism, `L` a `g`-ample invertible sheaf and `ν : Γ ⟶ X` a finite morphism
from a proper complex curve whose image lies in one fibre of `g`. Then `deg_ν L > 0`: `ν` factors
through `g⁻¹(V)` for an affine `V`, where `L` is ample, and the finite pullback of an ample sheaf
to a proper curve is ample. -/
private theorem degreeOn_pos_of_isRelativelyAmple_of_isFinite {X Y Γ : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} (g : X ⟶ Y) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hamp : Mori.IsRelativelyAmple g L) (ν : Γ ⟶ X) [IsFinite ν] [IsProper (ν ≫ sX)]
    [AlgebraicGeometry.IsCurve ℂ (ν ≫ sX)] (hdim : topologicalKrullDim Γ ≤ 1) {y : Y}
    (hcon : ∀ c, g (ν c) = y) : 0 < Mori.degreeOn ℂ sX ν hdim L := by
  obtain ⟨V, -, hyV, hampV⟩ := hamp y
  have hrange : Set.range ν ⊆ Set.range (g ⁻¹ᵁ V).ι := by
    rintro _ ⟨c, rfl⟩
    rw [Scheme.Opens.range_ι]
    show g (ν c) ∈ V
    rw [hcon]
    exact hyV
  set j := IsOpenImmersion.lift (g ⁻¹ᵁ V).ι ν hrange with hjdef
  have hj : j ≫ (g ⁻¹ᵁ V).ι = ν := IsOpenImmersion.lift_fac _ _ _
  haveI : IsFinite (j ≫ (g ⁻¹ᵁ V).ι) := by rw [hj]; infer_instance
  haveI : IsFinite j := isFinite_of_comp j (g ⁻¹ᵁ V).ι
  set M := (modulePullback (g ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj L with hM
  haveI hMinv : SheafOfModules.IsInvertible (g ⁻¹ᵁ V).toScheme.presheaf
      (g ⁻¹ᵁ V).toScheme.ringCatSheaf.2 M :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
      (g ⁻¹ᵁ V).ι.toLRSHom.toShHom _ inferInstance
  have h1 : Scheme.Modules.IsAmple (g ⁻¹ᵁ V).toScheme M :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr hampV
  have h2 := isAmple_pullback_of_isFinite j M h1
  haveI := MMP.Mori.isInvertible_pullback_obj j M
  have h3 := invertibleCurveDegree_pos_of_isAmple_of_isCurve ℂ (ν ≫ sX) hdim _ h2
  let e : (Scheme.Modules.pullback j).obj M ≅ (Scheme.Modules.pullback ν).obj L :=
    (Scheme.Modules.pullback j).mapIso
        ((AlgebraicGeometry.modulePullbackIsoSchemePullback
          (g ⁻¹ᵁ V).ι).app L) ≪≫
      (Scheme.Modules.pullbackComp j (g ⁻¹ᵁ V).ι).app L ≪≫ eqToIso (by rw [hj])
  rw [Mori.degreeOn_eq_invertibleCurveDegree, ← invertibleCurveDegree_eq_of_iso ℂ _ _ e]
  exact h3

end RelativelyAmple

section PrimeDivisors

open MMP.Mori

/-- **Surfaces in a threefold are prime divisors.** On an integral scheme `M` locally of finite
type over `ℂ` of dimension three, a closed irreducible subset of dimension two is the support of
a prime divisor: its generic point has coheight one. -/
private theorem exists_primeDivisor_support_eq {M : Scheme.{0}} (sM : M ⟶ Spec (.of ℂ))
    [IsIntegral M] [LocallyOfFiniteType sM]
    (hM3 : topologicalKrullDim M = ((3 : ℕ) : WithBot ℕ∞)) {A : Set M} (hA : IsClosed A)
    (hirr : IsIrreducible A) (h2 : topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞)) :
    ∃ P : Mori.PrimeDivisor M, (P.support : Set M) = A := by
  have hgen := hirr.isGenericPoint_genericPoint_closure
  rw [hA.closure_eq] at hgen
  set η := hirr.genericPoint
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sM η
  rw [hgen.def, h2, hM3] at h
  have hη : Order.coheight η = 1 := by
    generalize Order.coheight η = c at h ⊢
    induction c using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      have h' : (((2 + n : ℕ) : ℕ∞) : WithBot ℕ∞) = (((3 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [Nat.cast_add, WithBot.coe_add]; exact h
      have : 2 + n = 3 := Nat.cast_injective (WithBot.coe_injective h')
      have hn : n = 1 := by omega
      subst hn
      rfl
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hη, ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact hgen.def

end PrimeDivisors

section PullbackCoefficients

open MMP.Mori

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) (E : Mori.PrimeDivisor Y)
  (hE : Stacks.Divisors.IsEffectiveCartierDivisor E.idealSheaf)
  (hEc : Divisor.IsCartier (Finsupp.single E (1 : ℤ)))
  (hB : ∀ Z : irreducibleComponents X,
    f (componentGenericPoint X Z) ∉ DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ)))

include hE in
/-- **Multiplicities of a pulled-back prime divisor.** The coefficient of a prime divisor `P` in
`f^*E` is positive when `f` maps the generic point of `P` into `E`. -/
private theorem one_le_coeff_pullback_single (P : Mori.PrimeDivisor X)
    (hP : f P.genericPoint ∈ (E.support : Set Y)) :
    1 ≤ (Divisor.pullback (f := f) (Finsupp.single E (1 : ℤ)) hEc hB).coeff P := by
  obtain ⟨n, hn, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder E hE
    (Divisor.isPullback_pullback hEc hB) P
  rw [hc]
  have hle : IdealSheafData.stalk (E.idealSheaf.comap f) P.genericPoint ≤
      IsLocalRing.maximalIdeal _ := by
    rw [AlgebraicGeometry.IdealSheafData.stalk_comap, Ideal.map_le_iff_le_comap]
    have hne : IdealSheafData.stalk E.idealSheaf (f P.genericPoint) ≠ ⊤ := fun h ↦
      ((Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).1 h) hP
    refine (IsLocalRing.le_maximalIdeal hne).trans ?_
    intro a ha
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ (IsLocalRing.mem_maximalIdeal _).1 ha ((isUnit_map_iff _ _).1 hu)
  have h1 : (1 : ℕ∞) ≤ MMP.Resolution.idealOrder
      (IdealSheafData.stalk (E.idealSheaf.comap f) P.genericPoint) :=
    le_iSup₂_of_le (f := fun (j : ℕ) (_ : _ ≤ IsLocalRing.maximalIdeal _ ^ j) ↦ (j : ℕ∞)) 1
      (by rw [pow_one]; exact hle) (by norm_num)
  rw [hn] at h1
  exact_mod_cast h1

include hE in
/-- The coefficient of a prime divisor `P` in `f^*E` vanishes when `f` maps the generic point of
`P` outside `E`. -/
private theorem coeff_pullback_single_eq_zero (P : Mori.PrimeDivisor X)
    (hP : f P.genericPoint ∉ (E.support : Set Y)) :
    (Divisor.pullback (f := f) (Finsupp.single E (1 : ℤ)) hEc hB).coeff P = 0 := by
  obtain ⟨n, hn, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder E hE
    (Divisor.isPullback_pullback hEc hB) P
  rw [hc]
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap,
    (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).2 hP, Ideal.map_top,
    MMP.Threefold.Resolution.idealOrder_top] at hn
  exact_mod_cast hn.symm

include hE in
/-- The pull-back of a prime divisor is effective. -/
private theorem coeff_pullback_single_nonneg (P : Mori.PrimeDivisor X) :
    0 ≤ (Divisor.pullback (f := f) (Finsupp.single E (1 : ℤ)) hEc hB).coeff P := by
  obtain ⟨n, -, hc⟩ := MMP.Threefold.Resolution.coeff_isPullback_single_eq_idealOrder E hE
    (Divisor.isPullback_pullback hEc hB) P
  rw [hc]
  exact Int.natCast_nonneg n

end PullbackCoefficients

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z]
  [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- On stalks, the kernel of a morphism of sheaves of `ℚ`-vector spaces is the kernel of the
stalk map: the inclusion of the kernel is injective on stalks, with image the kernel. -/
private theorem stalk_kernel_ι {X : TopCat.{0}} {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (f : A ⟶ B) (t : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
      ((TopCat.Sheaf.forget _ _).map (Limits.kernel.ι f))).hom ∧
    LinearMap.range ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
      ((TopCat.Sheaf.forget _ _).map (Limits.kernel.ι f))).hom =
    LinearMap.ker ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
      ((TopCat.Sheaf.forget _ _).map f)).hom := by
  let G := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X ⋙ TopCat.Presheaf.stalkFunctor _ t
  let S := ShortComplex.mk (Limits.kernel.ι f) f (Limits.kernel.condition f)
  have hS : Limits.IsLimit (Limits.KernelFork.ofι (S.map G).f (S.map G).zero) :=
    Limits.isLimitForkMapOfIsLimit' G S.zero (Limits.kernelIsKernel f)
  obtain ⟨he, hm⟩ := (S.map G).exact_and_mono_f_iff_f_is_kernel.2 ⟨hS⟩
  exact ⟨(ModuleCat.mono_iff_injective _).1 hm,
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 he⟩

/-! ### Kernels of maps of local systems -/

section ConstantSheaf

variable {X' Y' Z' : TopCat.{0}}

/-- On a nonempty open, the map from a constant presheaf to its sheafification is injective. -/
private theorem toSheafify_const_app_injective (E : ModuleCat.{0} ℚ) {W : Opens X'}
    (hW : (W : Set X').Nonempty) :
    Function.Injective ((toSheafify (Opens.grothendieckTopology X')
      ((Functor.const (Opens X')ᵒᵖ).obj E)).app (op W)) := by
  intro a b hab
  obtain ⟨x, hx⟩ := hW
  obtain ⟨V, f, hf, -⟩ := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X')
    (toSheafify (Opens.grothendieckTopology X') ((Functor.const (Opens X')ᵒᵖ).obj E)) a b hab x hx
  simpa using hf

/-- Restriction of the image of a constant section is the image of the same constant. -/
private theorem toSheafify_const_app_restrict (E : ModuleCat.{0} ℚ) {V U : Opens X'}
    (i : V ⟶ U) (a : E) :
    (sheafify (Opens.grothendieckTopology X') ((Functor.const (Opens X')ᵒᵖ).obj E)).map i.op
        ((toSheafify (Opens.grothendieckTopology X')
          ((Functor.const (Opens X')ᵒᵖ).obj E)).app (op U) a) =
      (toSheafify (Opens.grothendieckTopology X')
        ((Functor.const (Opens X')ᵒᵖ).obj E)).app (op V) a := by
  have := ConcreteCategory.congr_hom
    ((toSheafify (Opens.grothendieckTopology X')
      ((Functor.const (Opens X')ᵒᵖ).obj E)).naturality i.op) a
  simpa using this.symm

/-- On a connected space, every global section of a constant sheaf is constant. -/
private theorem toSheafify_const_app_top_surjective [ConnectedSpace X'] (E : ModuleCat.{0} ℚ) :
    Function.Surjective
      ((toSheafify (Opens.grothendieckTopology X')
        ((Functor.const (Opens X')ᵒᵖ).obj E)).app (op ⊤)) := by
  set P := (Functor.const (Opens X')ᵒᵖ).obj E
  set φ := toSheafify (Opens.grothendieckTopology X') P
  intro s
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology X') φ s
  choose V f hV hxV using fun x : X' => hS x trivial
  choose e he using hV
  have key : ∀ x, ∀ y ∈ V x, e y = e x := by
    intro x y hy
    apply toSheafify_const_app_injective E (W := V x ⊓ V y) ⟨y, hy, hxV y⟩
    have h1 := toSheafify_const_app_restrict E (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)) (e x)
    have h2 := toSheafify_const_app_restrict E (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)) (e y)
    rw [← h1, ← h2, he, he, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  let g : X' → E := fun x => e x
  have hloc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    exact ⟨V x, (V x).isOpen, hxV x, fun y hy => key x y hy⟩
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X')
  refine ⟨g x₀, ?_⟩
  let F : TopCat.Sheaf (ModuleCat.{0} ℚ) X' :=
    (presheafToSheaf (Opens.grothendieckTopology X') _).obj P
  refine (TopCat.Sheaf.eq_of_locally_eq' F V ⊤ f
    (fun x _ => Opens.mem_iSup.2 ⟨x, hxV x⟩) _ _ fun x => ?_)
  change (sheafify (Opens.grothendieckTopology X') P).map (f x).op (φ.app (op ⊤) (g x₀)) =
    (sheafify (Opens.grothendieckTopology X') P).map (f x).op s
  rw [toSheafify_const_app_restrict, ← he x, hloc.apply_eq_of_preconnectedSpace x₀ x]

/-- The unit of the constant sheaf adjunction is the sheafification map on global sections. -/
private theorem constantSheafAdj_unit_app (E : ModuleCat.{0} ℚ) :
    (constantSheafAdj (Opens.grothendieckTopology X') (ModuleCat.{0} ℚ) isTerminalTop).unit.app
        E =
      (toSheafify (Opens.grothendieckTopology X')
        ((Functor.const (Opens X')ᵒᵖ).obj E)).app (op ⊤) := by
  simp [constantSheafAdj, Adjunction.comp_unit_app]
  rfl

/-- On a connected space, the constant sheaf functor is fully faithful. -/
private noncomputable def fullyFaithfulConstantSheaf [ConnectedSpace X'] :
    (constantSheaf (Opens.grothendieckTopology X') (ModuleCat.{0} ℚ)).FullyFaithful :=
  haveI : ∀ E, IsIso ((constantSheafAdj (Opens.grothendieckTopology X') (ModuleCat.{0} ℚ)
      isTerminalTop).unit.app E) :=
    fun E => by
      obtain ⟨x⟩ := (inferInstance : Nonempty X')
      rw [constantSheafAdj_unit_app]
      exact (ConcreteCategory.isIso_iff_bijective _).2
        ⟨toSheafify_const_app_injective E ⟨x, trivial⟩, toSheafify_const_app_top_surjective E⟩
  haveI := NatIso.isIso_of_isIso_app
    (constantSheafAdj (Opens.grothendieckTopology X') (ModuleCat.{0} ℚ) isTerminalTop).unit
  (constantSheafAdj (Opens.grothendieckTopology X') (ModuleCat.{0} ℚ)
    isTerminalTop).fullyFaithfulLOfIsIsoUnit

/-- Global sections of a pushforward are global sections. -/
private noncomputable def pushforwardTopIso (f : X' ⟶ Y') :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        (sheafSections (Opens.grothendieckTopology Y') (ModuleCat.{0} ℚ)).obj (op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology X') (ModuleCat.{0} ℚ)).obj (op ⊤) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The inverse image of a constant sheaf is constant. -/
private noncomputable def pullbackConstIso (f : X' ⟶ Y') :
    constantSheaf (Opens.grothendieckTopology Y') (ModuleCat.{0} ℚ) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ≅
      constantSheaf (Opens.grothendieckTopology X') (ModuleCat.{0} ℚ) :=
  (((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)).ofNatIsoRight
      (pushforwardTopIso f)).leftAdjointUniq
        (constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop)

/-- Direct images compose. -/
private noncomputable def pushforwardCompIso (g : X' ⟶ Y') (f : Y' ⟶ Z') :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g ⋙
        TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ≅
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (g ≫ f) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Inverse images compose. -/
private noncomputable def pullbackCompIso (g : X' ⟶ Y') (f : Y' ⟶ Z') :
    TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (g ≫ f) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g)).ofNatIsoRight
      (pushforwardCompIso g f)).leftAdjointUniq
        (TopCat.Sheaf.pullbackPushforwardAdjunction _ (g ≫ f))

attribute [local instance] reflectsLimits_of_reflectsIsomorphisms in
/-- Inverse images of sheaves of `ℚ`-vector spaces preserve finite limits. -/
private theorem preservesFiniteLimits_pullback (f : X' ⟶ Y') :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f) := by
  unfold TopCat.Sheaf.pullback
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

end ConstantSheaf

/-- On a locally connected space, the kernel of a morphism of local systems is a local system:
near every point both are constant on a connected open set, where the constant sheaf functor
is fully faithful, so the morphism is the constant sheaf of a linear map `f₀`; inverse images
and constant sheaves preserve kernels, so the kernel is constant there with fibre `ker f₀`. -/
private theorem isLocalSystem_kernel {X' : TopCat.{0}} [LocallyConnectedSpace X']
    {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X'} (f : A ⟶ B) (hA : IsLocalSystem A)
    (hB : IsLocalSystem B) : IsLocalSystem (Limits.kernel f) := by
  intro x
  obtain ⟨V₁, hx₁, E, hE, ⟨e₁⟩⟩ := hA x
  obtain ⟨V₂, hx₂, E', hE', ⟨e₂⟩⟩ := hB x
  have hxV : x ∈ ((V₁ ⊓ V₂ : Opens X') : Set X') := ⟨hx₁, hx₂⟩
  let U : Opens X' := ⟨connectedComponentIn (V₁ ⊓ V₂ : Opens X') x,
    (V₁ ⊓ V₂).isOpen.connectedComponentIn⟩
  haveI : ConnectedSpace ((Opens.toTopCat X').obj U) :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr hxV)
  let g₁ : (Opens.toTopCat X').obj U ⟶ (Opens.toTopCat X').obj V₁ :=
    (Opens.toTopCat X').map (homOfLE ((connectedComponentIn_subset _ _).trans
      (inf_le_left : ((V₁ ⊓ V₂ : Opens X') : Set X') ⊆ V₁)))
  let g₂ : (Opens.toTopCat X').obj U ⟶ (Opens.toTopCat X').obj V₂ :=
    (Opens.toTopCat X').map (homOfLE ((connectedComponentIn_subset _ _).trans
      (inf_le_right : ((V₁ ⊓ V₂ : Opens X') : Set X') ⊆ V₂)))
  let P := TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) U.inclusion'
  let L := constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X').obj U))
    (ModuleCat.{0} ℚ)
  let a : P.obj A ≅ L.obj E :=
    (pullbackCompIso g₁ V₁.inclusion').symm.app A ≪≫
      (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g₁).mapIso e₁ ≪≫ (pullbackConstIso g₁).app E
  let b : P.obj B ≅ L.obj E' :=
    (pullbackCompIso g₂ V₂.inclusion').symm.app B ≪≫
      (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g₂).mapIso e₂ ≪≫ (pullbackConstIso g₂).app E'
  let hL : L.FullyFaithful := fullyFaithfulConstantSheaf
  let f₀ : E ⟶ E' := hL.preimage (a.inv ≫ P.map f ≫ b.hom)
  have hf : L.map f₀ = a.inv ≫ P.map f ≫ b.hom := hL.map_preimage _
  haveI : PreservesFiniteLimits P := preservesFiniteLimits_pullback _
  haveI : PreservesFiniteLimits L := by unfold L constantSheaf; infer_instance
  have hw : P.map f ≫ b.hom = a.hom ≫ L.map f₀ := by
    erw [hf, Iso.hom_inv_id_assoc]
  let i : P.obj (Limits.kernel f) ≅ L.obj (Limits.kernel f₀) :=
    PreservesKernel.iso P f ≪≫ Limits.kernel.mapIso (P.map f) (L.map f₀) a b hw ≪≫
        (PreservesKernel.iso L f₀).symm
  refine ⟨U, mem_connectedComponentIn hxV, Limits.kernel f₀, ?_, ⟨i⟩⟩
  exact LinearEquiv.finiteDimensional (ModuleCat.kernelIsoKer f₀).toLinearEquiv.symm

/-- The complex points of a scheme locally of finite type over `ℂ` form a locally connected
space: every point has a basis of open contractible neighbourhoods. -/
private theorem locallyConnectedSpace_analyticSpace {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] : LocallyConnectedSpace (analyticSpace sX) := by
  let : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  have H : MMP.HasOpenContractibleBasis (analyticSpace sX) :=
    (MMP.UnderlyingSpace.hasOpenContractibleBasis X).of_homeomorph
      (homeomorphUnderlyingSpace (X := X)).symm
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected.2 fun x N hN ↦ ?_
  obtain ⟨V, ⟨hV, hxV, hc⟩, hVN⟩ := (H x).mem_iff.1 hN
  exact ⟨V, hVN, hV, hxV, ⟨⟨x, hxV⟩, (haveI := hc; isPreconnected_iff_preconnectedSpace.2
    inferInstance)⟩⟩

/-- **Rigidity of classes supported on a closed piece.** Let `G` be closed in `W` with
`H²(W, W ∖ G; ℚ)` of rank at most one, and `K ⊆ W`. Two classes of `H²(W; ℚ)` vanishing on
`W ∖ G` and with the same nonzero restriction to `W ∖ K` are equal: both come from the line
`H²(W, W ∖ G; ℚ)`, and the restriction to `W ∖ K` distinguishes the multiples. -/
private theorem eq_of_rationalCohomologyMap_eq_of_rank_le_one {W : TopCat.{0}} {G K : Set W}
    (hrank : Module.rank ℚ (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) W G 2) ≤ 1)
    {α α' : rationalCohomology W 2}
    (h₀ : rationalCohomologyMap (X' := TopCat.of (Gᶜ : Set W))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2 α = 0)
    (h₀' : rationalCohomologyMap (X' := TopCat.of (Gᶜ : Set W))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2 α' = 0)
    (h₁ : rationalCohomologyMap (X' := TopCat.of (Kᶜ : Set W))
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2 α =
      rationalCohomologyMap (X' := TopCat.of (Kᶜ : Set W))
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2 α')
    (hne : rationalCohomologyMap (X' := TopCat.of (Kᶜ : Set W))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2 α ≠ 0) : α = α' := by
  obtain ⟨u, rfl⟩ := (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ W G 2 α).1 h₀
  obtain ⟨u', rfl⟩ := (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ W G 2 α').1 h₀'
  obtain ⟨v, hv⟩ := rank_le_one_iff.1 hrank
  obtain ⟨a, rfl⟩ := hv u
  obtain ⟨a', rfl⟩ := hv u'
  simp only [map_smul] at h₁ hne ⊢
  rw [smul_left_injective ℚ (right_ne_zero_of_smul hne) h₁]
/-- The rational cohomology of the point `(Spec ℂ)^an` vanishes in positive degrees. -/
private theorem subsingleton_rationalCohomology_spec (n : ℕ) :
    Subsingleton (singularCohomology ℚ (analyticSpace (𝟙 (Spec (.of ℂ)))) (n + 1 : ℕ)) := by
  haveI : Unique (analyticSpace (𝟙 (Spec (.of ℂ)))) :=
    { default := ⟨𝟙 _, Category.comp_id _⟩
      uniq := fun a ↦ ComplexPoints.ext <| by simpa using a.hom_comp_structure }
  exact MMP.Topology.subsingleton_cohomology_of_unique ℚ _ n

/-- The first Chern class of the trivial module vanishes rationally: `𝒪_X` is pulled back from
the point `Spec ℂ`, whose rational cohomology vanishes in degree two. -/
private theorem mapCoeff_firstChernClass_unit_eq_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf)] :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass (SheafOfModules.unit X.ringCatSheaf)) = 0 := by
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  let s : X ⟶ Spec (.of ℂ) := X ↘ Spec (.of ℂ)
  let : (SheafOfModules.pushforward.{0} s.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction s).isRightAdjoint
  let eunit : (Scheme.Modules.pullback s).obj (SheafOfModules.unit (Spec (.of ℂ)).ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    @asIso _ _ _ _ _ (SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal.{0} s.toRingCatSheafHom)
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of ℂ))
  haveI := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback s
    (SheafOfModules.unit (Spec (.of ℂ)).ringCatSheaf)
  let ρ : Analytification.space (X ↘ Spec (.of ℂ)) ⟶
      Analytification.space (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    analyticMap (sY := 𝟙 _) s (Category.comp_id _)
  rw [← algebraicFirstChernClass_eq_of_iso eunit]
  refine (congrArg _ (algebraicFirstChernClass_pullback s ρ (fun _ ↦ rfl)
    (SheafOfModules.unit (Spec (.of ℂ)).ringCatSheaf))).trans ?_
  refine (rationalCohomologyMap_mapCoeff ρ 2 _).symm.trans ?_
  have : Subsingleton (singularCohomology ℚ
      (Analytification.space (Spec (.of ℂ) ↘ Spec (.of ℂ))) (1 + 1 : ℕ)) :=
    subsingleton_rationalCohomology_spec 1
  rw [Subsingleton.elim (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 _) 0, map_zero]

/-- **`c₁(𝒪_Z(E))` vanishes off `E`.** For a prime divisor `E` of `Z` with `𝒪_Z(E)` invertible,
the rational first Chern class of `𝒪_Z(E)` pulls back to zero along any continuous map into
`Z^an` avoiding `E`: the map factors through `(Z ∖ E)^an`, where `𝒪_Z(E)` is trivial. -/
private theorem rationalCohomologyMap_firstChernClass_eq_zero (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))]
    {X' : TopCat.{0}} (g : X' ⟶ analyticSpace (Z ↘ Spec (.of ℂ)))
    (hg : ∀ x, (g x).hom.base (IsLocalRing.closedPoint ℂ) ∉ (E.support : Set Z)) :
    (rationalCohomologyMap g 2).hom (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
      (algebraicFirstChernClass
        (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)))) = 0 := by
  let U : Z.Opens := ⟨(E.support : Set Z)ᶜ, E.idealSheaf.support.isClosed.isOpen_compl⟩
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ Z ↘ Spec (.of ℂ)⟩
  have hemb := isOpenEmbedding_realize_ι (sX := Z ↘ Spec (.of ℂ)) U
  have hmem : ∀ x, g x ∈ Set.range (realize (sX := U.ι ≫ Z ↘ Spec (.of ℂ)) U.ι rfl) := by
    rw [range_realize_ι]
    intro x
    change (g x).hom (default : Spec (.of ℂ)) ∉ (E.support : Set Z)
    rw [Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)]
    exact hg x
  let g' : X' ⟶ analyticSpace (U.ι ≫ Z ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨fun x ↦ hemb.isEmbedding.toHomeomorph.symm ⟨g x, hmem x⟩,
      hemb.isEmbedding.toHomeomorph.symm.continuous.comp
        (g.hom.continuous.subtype_mk _)⟩
  have hfac : g = g' ≫ analyticMap U.ι rfl := by
    ext x
    exact congrArg (fun p : ComplexPoints (Z ↘ Spec (.of ℂ)) ↦ p.hom) (congrArg Subtype.val
      (hemb.isEmbedding.toHomeomorph.apply_symm_apply ⟨g x, hmem x⟩)).symm
  let L := Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)
  have hcoeff : ∀ Γ : Mori.PrimeDivisor Z, (Γ.support ∩ (U : Set Z)).Nonempty →
      DivisorWithCoeffs.coeff (Finsupp.single E 1 : Divisor Z) Γ =
        DivisorWithCoeffs.coeff (0 : Divisor Z) Γ := by
    rintro Γ ⟨z, hzΓ, hzU⟩
    have hne : E ≠ Γ := by
      rintro rfl
      exact hzU hzΓ
    classical
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, if_neg hne,
      DivisorWithCoeffs.coeff_zero]
  let e : (Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm ≪≫
      Divisor.restrictDivisorialSheafIsoOfEqOn hcoeff ≪≫
      (Scheme.Modules.restrictFunctor U.ι).mapIso Divisor.divisorialSheafZeroIso ≪≫
      Scheme.Modules.restrictUnitIso U.ι
  haveI := Stacks.InvertiblePullback.isInvertibleModule_schemeModulesPullback U.ι L
  haveI := Stacks.Ample.isInvertibleModule_unit U.toScheme
  rw [hfac, rationalCohomologyMap_comp, ModuleCat.comp_apply,
    rationalCohomologyMap_mapCoeff (analyticMap U.ι rfl)]
  refine (congrArg (fun c ↦ (rationalCohomologyMap g' 2).hom
    (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c))
    (algebraicFirstChernClass_pullback U.ι (analyticMap U.ι rfl) (fun _ ↦ rfl) L).symm).trans ?_
  refine (congrArg (fun c ↦ (rationalCohomologyMap g' 2).hom
    (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 c))
    (algebraicFirstChernClass_eq_of_iso e)).trans ?_
  exact (congrArg (rationalCohomologyMap g' 2).hom
    mapCoeff_firstChernClass_unit_eq_zero).trans (map_zero _)

/-! ### A Z-matrix lemma -/

private theorem eq_zero_of_sum_mul_eq_zero_aux {ι : Type*} [Fintype ι] (A : ι → ι → ℚ)
    (m : ι → ℚ) (hm : ∀ i, 0 < m i) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j * m j < 0) (l : ι → ℚ) (h : ∀ i, ∑ j, A i j * l j = 0) :
    ∀ j, l j / m j ≤ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨j₀, hj₀⟩ := hc
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun j ↦ l j / m j)
    ⟨j₀, Finset.mem_univ _⟩
  set M := l i₀ / m i₀
  have hM : 0 < M := hj₀.trans_le (hi₀ j₀ (Finset.mem_univ _))
  have hle : ∀ j, A i₀ j * l j ≤ A i₀ j * m j * M := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      have : l j = m j * M := by simp only [M]; field_simp [(hm j).ne']
      rw [this]; ring_nf; exact le_refl _
    · have h1 : l j / m j ≤ M := hi₀ j (Finset.mem_univ _)
      have h2 : l j ≤ m j * M := by
        rwa [div_le_iff₀ (hm j), mul_comm] at h1
      calc A i₀ j * l j ≤ A i₀ j * (m j * M) :=
            mul_le_mul_of_nonneg_left h2 (hoff i₀ j (Ne.symm hj))
        _ = A i₀ j * m j * M := by ring
  have hsum : ∑ j, A i₀ j * l j ≤ (∑ j, A i₀ j * m j) * M := by
    rw [Finset.sum_mul]; exact Finset.sum_le_sum fun j _ ↦ hle j
  rw [h i₀] at hsum
  have := mul_neg_of_neg_of_pos (hrow i₀) hM
  linarith

/-- **A matrix with nonnegative off-diagonal entries and negative weighted row sums has trivial
kernel**: if `A m < 0` for a positive vector `m`, then `A l = 0` forces `l = 0`. At an index
maximising `l / m`, the row of `A l` is bounded by that maximum times the row of `A m`. -/
private theorem eq_zero_of_sum_mul_eq_zero {ι : Type*} [Fintype ι] (A : ι → ι → ℚ)
    (m : ι → ℚ) (hm : ∀ i, 0 < m i) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hrow : ∀ i, ∑ j, A i j * m j < 0) (l : ι → ℚ) (h : ∀ i, ∑ j, A i j * l j = 0) :
    l = 0 := by
  have h₁ := eq_zero_of_sum_mul_eq_zero_aux A m hm hoff hrow l h
  have h₂ := eq_zero_of_sum_mul_eq_zero_aux A m hm hoff hrow (-l)
    (fun i ↦ by simp [Finset.sum_neg_distrib, h i])
  funext j
  have a := h₁ j
  have b := h₂ j
  simp only [Pi.neg_apply, neg_div] at b
  have : l j / m j = 0 := le_antisymm a (by linarith)
  rcases div_eq_zero_iff.1 this with h | h
  · exact h
  · exact absurd h (hm j).ne'

/-! ### Borel–Moore homology of a union -/

open borelMooreHomology in
/-- In the Borel–Moore sequence of a closed `X ⊆ Y`,
`rank H_k Y ≤ rank H_k X + rank H_k (Y ∖ X)`. -/
private theorem rank_borelMooreHomology_le_add {Y : TopCat.{0}} [T2Space Y] {X : Set Y}
    (hX : IsClosed X) (h : IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hX) (k : ℤ) :
    Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) Y k) ≤
      Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of X) k) +
      Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (complOpens hX)) k) := by
  have hex := exact_pushforward_restrict h k
  set f := (pushforward ℚ (ModuleCat.of ℚ ℚ) (subspaceInclusion Y X)
    (isProperMap_subspaceInclusion hX) k).hom
  set g := (restrict ℚ (ModuleCat.of ℚ ℚ) (complOpens hX) k).hom
  rw [← LinearMap.rank_range_add_rank_ker g, add_comm]
  have hk : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.1 hex
  rw [hk]
  exact add_le_add (rank_range_le f) (Submodule.rank_le _)

open borelMooreHomology in
/-- Restriction to `Y ∖ X` is onto in degree `k + 1` when `H_k X` vanishes. -/
private theorem surjective_restrict_of_subsingleton {Y : TopCat.{0}} [T2Space Y] {X : Set Y}
    (hX : IsClosed X) (h : IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hX) (k : ℤ)
    (hk : Subsingleton (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of X) k)) :
    Function.Surjective (restrict ℚ (ModuleCat.of ℚ ℚ) (complOpens hX) (k + 1)).hom := by
  have hex := exact_restrict_connecting h k
  intro y
  exact (hex y).1 (Subsingleton.elim _ _)

section PointsOver

open UnderlyingSpace borelMooreHomology

variable {Q : Scheme.{0}} [Q.Over (Spec (.of ℂ))] [IsComplexScheme Q]

/-- For closed `C ⊆ C'` of a complex scheme, the points of `C` inside the points of `C'` are
homeomorphic to the points of `C`. -/
private noncomputable def pointsOverSubsetHomeomorph {C C' : Set Q} (h : C ⊆ C') :
    ((Subtype.val : pointsOver (K := ℂ) C' → UnderlyingSpace ℂ Q) ⁻¹' pointsOver (K := ℂ) C) ≃ₜ
      pointsOver (K := ℂ) C :=
  (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (by
      ext x
      exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.2, fun hx ↦ ⟨⟨⟨x, pointsOver_mono h hx⟩, hx⟩, rfl⟩⟩))

/-- The Borel–Moore sequence applies to the points of `C ⊆ C'`, closed in a complex scheme. -/
private theorem isRelativeQuasiIso_pointsOver_subset {C C' : Set Q} (hC : IsClosed C)
    (hC' : IsClosed C') (h : C ⊆ C') :
    IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) (Y := TopCat.of (pointsOver (K := ℂ) C'))
      (X := (Subtype.val : pointsOver (K := ℂ) C' → UnderlyingSpace ℂ Q) ⁻¹'
        pointsOver (K := ℂ) C)
      ((isClosed_pointsOver hC).preimage continuous_subtype_val) := by
  obtain ⟨-, n, F, hF⟩ := hasBasis_contractible_and_exists_isClosedEmbedding Q
  have hF' : Topology.IsClosedEmbedding (F ∘ (Subtype.val : pointsOver (K := ℂ) C' → _)) :=
    hF.comp (isClosed_pointsOver hC').isClosedEmbedding_subtypeVal
  exact isRelativeQuasiIso_of_isClosedEmbedding ℚ (ModuleCat.of ℚ ℚ) hF' _
    ((hasOpenContractibleBasis_pointsOver Q ⟨C, hC⟩).of_homeomorph
      (pointsOverSubsetHomeomorph h).symm)
    (hasOpenContractibleBasis_pointsOver Q ⟨C', hC'⟩)

/-- Borel–Moore homology of the points of a closed `C` vanishes above twice its dimension. -/
private theorem subsingleton_borelMooreHomology_pointsOver' {C : Set Q} (hC : IsClosed C)
    {m : ℕ} (hdim : topologicalKrullDim C ≤ m) {i : ℤ} (hi : 2 * (m : ℤ) < i) :
    Subsingleton (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (pointsOver (K := ℂ) C)) i) := by
  refine MMP.Fourfold.ConductorBlowup.subsingleton_borelMooreHomology_pointsOver Q hC rfl ?_ hi
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩).subschemeι.base = C := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  change topologicalKrullDim _ ≤ _
  rw [((Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)).isHomeomorph.topologicalKrullDim_eq]
  exact hdim

/-- A dimension below `n + 1` is at most `n`. -/
private theorem le_of_lt_natCast_succ {x : WithBot ℕ∞} {n : ℕ}
    (h : x < ((n + 1 : ℕ) : WithBot ℕ∞)) : x ≤ ((n : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    refine WithBot.coe_le_coe.2 (Order.le_of_lt_succ ?_)
    simpa [ENat.succ_def] using WithBot.coe_lt_coe.1 h

/-- On an irreducible complex scheme of dimension at most `n`, `H_{2n}` has rank at most one: it is
spanned by the cycle classes of the generic points of the components of delta-dimension `n`
(`MMP.Chow.linearIndependent_and_span_eq_top_pointCycleClass`), and there is one component. -/
private theorem rank_borelMooreHomology_le_one_of_irreducibleSpace {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IrreducibleSpace X] {n : ℕ}
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞)) :
    Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace ℂ X)) ((2 * n : ℕ) : ℤ)) ≤ 1 := by
  have hspan := (MMP.Chow.linearIndependent_and_span_eq_top_pointCycleClass ℚ (X := X) hX).2
  haveI : Subsingleton (irreducibleComponents X) := by
    have hc : ∀ C ∈ irreducibleComponents X, C = Set.univ := fun C hC ↦
      Set.eq_univ_of_univ_subset (hC.2 (IrreducibleSpace.isIrreducible_univ X)
        (Set.subset_univ C))
    exact ⟨fun a b ↦ Subtype.ext ((hc a.1 a.2).trans (hc b.1 b.2).symm)⟩
  calc _ = Module.rank ℚ (⊤ : Submodule ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (UnderlyingSpace ℂ X)) ((2 * n : ℕ) : ℤ))) := Submodule.topEquiv.rank_eq.symm
    _ ≤ _ := by
      rw [← hspan]
      exact (rank_span_le _).trans ((Cardinal.mk_range_le).trans
        (Cardinal.le_one_iff_subsingleton.2 inferInstance))

/-- The points of an irreducible closed subset of dimension at most two have rank at most one
in Borel–Moore degree four: the fundamental class generates when the dimension is two, and the
group vanishes otherwise. -/
private theorem rank_borelMooreHomology_pointsOver_le_one {C : Set Q} (hC : IsClosed C)
    (hirr : IsIrreducible C) (hdim : topologicalKrullDim C ≤ ((2 : ℕ) : WithBot ℕ∞)) :
    Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (pointsOver (K := ℂ) C)) ((2 * 2 : ℕ) : ℤ)) ≤ 1 := by
  by_cases h2 : topologicalKrullDim C = ((2 : ℕ) : WithBot ℕ∞)
  · let I := Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩
    letI : I.subscheme.Over (Spec (.of ℂ)) := ⟨I.subschemeι ≫ Q ↘ Spec (.of ℂ)⟩
    haveI : I.subschemeι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
    haveI : IsComplexScheme I.subscheme := IsComplexScheme.of_isClosedImmersion I.subschemeι
    haveI : IsIntegral I.subscheme := MMP.Fourfold.isIntegral_subscheme_vanishingIdeal ⟨C, hC⟩ hirr
    have hrange : Set.range I.subschemeι.base = C := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hdimS : ((2 : ℕ) : WithBot ℕ∞) = topologicalKrullDim I.subscheme := by
      rw [← h2]
      exact (I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr hrange)).isHomeomorph.topologicalKrullDim_eq.symm
    have h1 := rank_borelMooreHomology_le_one_of_irreducibleSpace (X := I.subscheme) hdimS.symm.le
    have he := isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) I.subschemeι
    have hr : Set.range (map (K := ℂ) I.subschemeι) = pointsOver C := by
      rw [range_map_of_isClosedImmersion, hrange]
    have hb := bijective_pushforward_homeomorph ℚ
      (Y := TopCat.of (UnderlyingSpace ℂ I.subscheme))
      (Y' := TopCat.of (pointsOver (K := ℂ) C))
      (he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)) ((2 * 2 : ℕ) : ℤ)
    have h3 := (LinearEquiv.ofBijective _ hb).rank_eq
    exact h3.symm.le.trans h1
  · haveI := subsingleton_borelMooreHomology_pointsOver' hC
      (le_of_lt_natCast_succ (lt_of_le_of_ne hdim h2))
      (i := ((2 * 2 : ℕ) : ℤ)) (by norm_num)
    rw [rank_zero_iff.2 inferInstance]
    exact zero_le_one

/-- **One more surface.** For closed `A, B` with `B` irreducible of dimension at most two and
`A ∩ B` of dimension at most one, adding `B` raises the rank of `H_4` of the points by at most
one: in the sequence of `A ⊆ A ∪ B` the complement is that of `A ∩ B` in `B`, onto which
`H_4(B)` restricts surjectively since `H_3(A ∩ B) = 0`. -/
private theorem rank_borelMooreHomology_pointsOver_union_le {A B : Set Q} (hA : IsClosed A)
    (hB : IsClosed B) (hirr : IsIrreducible B)
    (hdimB : topologicalKrullDim B ≤ ((2 : ℕ) : WithBot ℕ∞))
    (hdimAB : topologicalKrullDim (A ∩ B : Set Q) ≤ ((1 : ℕ) : WithBot ℕ∞)) :
    Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (pointsOver (K := ℂ) (A ∪ B))) ((2 * 2 : ℕ) : ℤ)) ≤
      Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (pointsOver (K := ℂ) A)) ((2 * 2 : ℕ) : ℤ)) + 1 := by
  have hX := (isClosed_pointsOver (K := ℂ) hA).preimage
    (continuous_subtype_val (p := (· ∈ pointsOver (K := ℂ) (A ∪ B))))
  have hrel := isRelativeQuasiIso_pointsOver_subset hA (hA.union hB) Set.subset_union_left
  have h1 := rank_borelMooreHomology_le_add hX hrel ((2 * 2 : ℕ) : ℤ)
  -- `H_4` of the points of `A`
  have h2 := (LinearEquiv.ofBijective _ (bijective_pushforward_homeomorph ℚ
    (Y := TopCat.of ((Subtype.val : pointsOver (K := ℂ) (A ∪ B) → UnderlyingSpace ℂ Q) ⁻¹'
      pointsOver (K := ℂ) A)) (Y' := TopCat.of (pointsOver (K := ℂ) A))
    (pointsOverSubsetHomeomorph Set.subset_union_left) ((2 * 2 : ℕ) : ℤ))).rank_eq
  -- the complement, read in `B`
  have hX' := (isClosed_pointsOver (K := ℂ) (hA.inter hB)).preimage
    (continuous_subtype_val (p := (· ∈ pointsOver (K := ℂ) B)))
  have hrel' := isRelativeQuasiIso_pointsOver_subset (hA.inter hB) hB Set.inter_subset_right
  have hsub : Subsingleton (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of ((Subtype.val : pointsOver (K := ℂ) B → UnderlyingSpace ℂ Q) ⁻¹'
        pointsOver (K := ℂ) (A ∩ B))) 3) := by
    haveI := subsingleton_borelMooreHomology_pointsOver' (hA.inter hB) hdimAB (i := 3)
      (by norm_num)
    exact (bijective_pushforward_homeomorph ℚ
      (Y := TopCat.of (pointsOver (K := ℂ) (A ∩ B)))
      (Y' := TopCat.of ((Subtype.val : pointsOver (K := ℂ) B → UnderlyingSpace ℂ Q) ⁻¹'
        pointsOver (K := ℂ) (A ∩ B)))
      (pointsOverSubsetHomeomorph Set.inter_subset_right).symm 3).2.subsingleton
  have hsurj := surjective_restrict_of_subsingleton hX' hrel' 3 hsub
  have h3 := LinearMap.rank_le_of_surjective _ hsurj
  have h4 := rank_borelMooreHomology_pointsOver_le_one hB hirr hdimB
  -- the two complements are homeomorphic
  let U₁ := complOpens (Y := TopCat.of (pointsOver (K := ℂ) (A ∪ B))) hX
  let U₂ := complOpens (Y := TopCat.of (pointsOver (K := ℂ) B)) hX'
  let e : U₁ ≃ₜ U₂ :=
    ((Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr (by
        ext x
        constructor
        · rintro ⟨⟨⟨y, hy⟩, hyA⟩, rfl⟩
          have hyA' : y ∉ pointsOver (K := ℂ) A := hyA
          refine ⟨⟨⟨y, ?_⟩, fun h ↦ hyA' (show y ∈ pointsOver (K := ℂ) (A ∩ B) from h).1⟩, rfl⟩
          rcases hy with hy | hy
          · exact absurd hy hyA'
          · exact hy
        · rintro ⟨⟨⟨y, hy⟩, hyAB⟩, rfl⟩
          have hyAB' : y ∉ pointsOver (K := ℂ) (A ∩ B) := hyAB
          exact ⟨⟨⟨y, Or.inr hy⟩, fun h ↦ hyAB' ⟨h, hy⟩⟩, rfl⟩))).trans
      ((Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.symm)
  have h5 := (LinearEquiv.ofBijective _ (bijective_pushforward_homeomorph ℚ
    (Y := TopCat.of U₁) (Y' := TopCat.of U₂) e
    ((2 * 2 : ℕ) : ℤ))).rank_eq
  have h6 : Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of U₁) ((2 * 2 : ℕ) : ℤ)) ≤ 1 := by
    rw [h5]
    have h3' : Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of U₂) ((2 * 2 : ℕ) : ℤ)) ≤
        Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
          (TopCat.of (pointsOver (K := ℂ) B)) ((2 * 2 : ℕ) : ℤ)) := h3
    exact h3'.trans h4
  calc _ ≤ _ := h1
    _ ≤ _ := add_le_add h2.le h6

/-- **Top Borel–Moore homology of a union of surfaces.** For finitely many pairwise
incomparable irreducible closed subsets of dimension at most two, `H_4` of the points of their
union has rank at most their number. -/
private theorem rank_borelMooreHomology_pointsOver_biUnion_le (s : Finset (Set Q))
    (hcl : ∀ S ∈ s, IsClosed S) (hirr : ∀ S ∈ s, IsIrreducible S)
    (hdim : ∀ S ∈ s, topologicalKrullDim S ≤ ((2 : ℕ) : WithBot ℕ∞))
    (hinc : ∀ S ∈ s, ∀ S' ∈ s, S ⊆ S' → S = S') :
    Module.rank ℚ (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (pointsOver (K := ℂ) (⋃ S ∈ s, S))) ((2 * 2 : ℕ) : ℤ)) ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hE : IsEmpty (pointsOver (K := ℂ) (⋃ S ∈ (∅ : Finset (Set Q)), S)) :=
      ⟨fun ⟨p, hp⟩ ↦ by
        have : p.toHom (IsLocalRing.closedPoint ℂ) ∈ (⋃ S ∈ (∅ : Finset (Set Q)), S) := hp
        simp at this⟩
    haveI : Subsingleton (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.of (pointsOver (K := ℂ) (⋃ S ∈ (∅ : Finset (Set Q)), S))) ((2 * 2 : ℕ) : ℤ)) :=
      (ModuleCat.isZero_iff_subsingleton).1 (borelMooreHomology.isZero_of_isEmpty ℚ (by norm_num))
    rw [rank_zero_iff.2 inferInstance]
    exact zero_le
  | insert B s hBs ih =>
    have hcl' : ∀ S ∈ s, IsClosed S := fun S hS ↦ hcl S (Finset.mem_insert_of_mem hS)
    have hA : IsClosed (⋃ S ∈ s, S) := s.finite_toSet.isClosed_biUnion hcl'
    have hB := hcl B (Finset.mem_insert_self _ _)
    have hBirr := hirr B (Finset.mem_insert_self _ _)
    have hBdim := hdim B (Finset.mem_insert_self _ _)
    have hunion : (⋃ S ∈ insert B s, S) = (⋃ S ∈ s, S) ∪ B := by
      rw [Finset.set_biUnion_insert, Set.union_comm]
    -- `B` is not contained in the union of the others
    have hnot : ¬ B ⊆ ⋃ S ∈ s, S := by
      intro hsub
      obtain ⟨S, hS, hBS⟩ : ∃ S ∈ s, B ⊆ S := by
        have := (isIrreducible_iff_sUnion_isClosed.1 hBirr) (s.image id) (by
          intro z hz
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hz
          exact hcl' S hS) (by
          intro x hx
          obtain ⟨S, hS, hxS⟩ := Set.mem_iUnion₂.1 (hsub hx)
          exact Set.mem_sUnion.2 ⟨S, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hS), hxS⟩)
        obtain ⟨z, hz, hBz⟩ := this
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hz
        exact ⟨S, hS, hBz⟩
      have := hinc B (Finset.mem_insert_self _ _) S (Finset.mem_insert_of_mem hS) hBS
      exact hBs (this ▸ hS)
    have hdimAB : topologicalKrullDim ((⋃ S ∈ s, S) ∩ B : Set Q) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
      have hne : ((⋃ S ∈ s, S) ∩ B : Set Q) ≠ B := fun h ↦ hnot (h ▸ Set.inter_subset_left)
      have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hBirr (hA.inter hB)
        Set.inter_subset_right hne (ne_top_of_le_ne_top (by decide) hBdim)
      exact le_of_lt_natCast_succ (hlt.trans_le hBdim)
    have hstep := rank_borelMooreHomology_pointsOver_union_le hA hB hBirr hBdim hdimAB
    have ih' := ih hcl' (fun S hS ↦ hirr S (Finset.mem_insert_of_mem hS))
      (fun S hS ↦ hdim S (Finset.mem_insert_of_mem hS))
      (fun S hS S' hS' ↦ hinc S (Finset.mem_insert_of_mem hS) S' (Finset.mem_insert_of_mem hS'))
    rw [hunion, Finset.card_insert_of_notMem hBs]
    calc _ ≤ _ := hstep
      _ ≤ (s.card : Cardinal) + 1 := add_le_add ih' le_rfl
      _ = ((s.card + 1 : ℕ) : Cardinal) := by push_cast; rfl

end PointsOver

/-! ### Supported cohomology along a surface in a smooth threefold -/

open UnderlyingSpace borelMooreHomology in
/-- **One generator of supported cohomology along an irreducible surface.** Let `M` be a smooth
quasi-projective complex threefold, `P ⊆ M` an irreducible proper closed surface and `U` an
open neighbourhood of `P(ℂ)` in `M(ℂ)`. Then `H²(U, U ∖ P(ℂ); ℚ)` has rank at most one: by
supported duality it is `H_4(P(ℂ); ℚ)`, which the fundamental class of `P` freely generates. -/
private theorem rank_cohomologyWithSupports_le_one {M : Scheme.{0}} [M.Over (Spec (.of ℂ))]
    [IsComplexScheme M] [IsIntegral M]
    (hqp : IsQuasiProjectiveVariety ℂ (M ↘ Spec (.of ℂ)))
    [SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ))]
    (P : Closeds M) (hP : IsIrreducible (P : Set M))
    (hP2 : topologicalKrullDim (P : Set M) = ((2 : ℕ) : WithBot ℕ∞))
    (hPp : IsProper ((Scheme.IdealSheafData.vanishingIdeal P).subschemeι ≫ (M ↘ Spec (.of ℂ))))
    (U : Opens (TopCat.of (UnderlyingSpace ℂ M))) (hPU : pointsOver (K := ℂ) (P : Set M) ⊆ U) :
    Module.rank ℚ (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of U)
      ((inclHom U) ⁻¹' pointsOver (K := ℂ) (P : Set M)) 2) ≤ 1 := by
  haveI : IsSeparated (M ↘ Spec (.of ℂ)) := hqp.toIsVariety.toIsSeparated
  have hdual := ((MMP.Analytic.supportedDuality_of_isQuasiProjectiveVariety (d := 3) hqp rfl P hPp).2.2.2
    U hPU 4).1
  have h1 := (LinearEquiv.ofBijective _ hdual).rank_eq
  -- the reduced subscheme on `P`
  let I := Scheme.IdealSheafData.vanishingIdeal P
  letI : I.subscheme.Over (Spec (.of ℂ)) := ⟨I.subschemeι ≫ M ↘ Spec (.of ℂ)⟩
  haveI : I.subschemeι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsComplexScheme I.subscheme := IsComplexScheme.of_isClosedImmersion I.subschemeι
  haveI : IsIntegral I.subscheme := MMP.Fourfold.isIntegral_subscheme_vanishingIdeal P hP
  have hrange : Set.range I.subschemeι.base = (P : Set M) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hdimS : ((2 : ℕ) : WithBot ℕ∞) = topologicalKrullDim I.subscheme := by
    rw [← hP2]
    exact (I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)).isHomeomorph.topologicalKrullDim_eq.symm
  have h2 := rank_borelMooreHomology_le_one_of_irreducibleSpace (X := I.subscheme) hdimS.symm.le
  -- `A ≅ P(ℂ) ≅ I.subscheme(ℂ)`
  have he := isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) I.subschemeι
  have hr : Set.range (map (K := ℂ) I.subschemeι) = pointsOver (P : Set M) := by
    rw [range_map_of_isClosedImmersion, hrange]
  have hA : Set.range (fun a : ((inclHom U) ⁻¹' pointsOver (K := ℂ) (P : Set M) : Set U) ↦
      (a.1.1 : UnderlyingSpace ℂ M)) = pointsOver (P : Set M) := by
    ext x
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.2, fun hx ↦ ⟨⟨⟨x, hPU hx⟩, hx⟩, rfl⟩⟩
  let φ : UnderlyingSpace ℂ I.subscheme ≃ₜ
      ((inclHom U) ⁻¹' pointsOver (K := ℂ) (P : Set M) : Set U) :=
    (he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)).trans
      (((Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
        (Homeomorph.setCongr hA)).symm)
  have hb := bijective_pushforward_homeomorph ℚ
    (Y := TopCat.of (UnderlyingSpace ℂ I.subscheme))
    (Y' := TopCat.of ((inclHom U) ⁻¹' pointsOver (K := ℂ) (P : Set M) : Set U)) φ
    ((2 * 2 : ℕ) : ℤ)
  have h3 := (LinearEquiv.ofBijective _ hb).rank_eq
  rw [show ((2 : ℤ)) = ((2 * 3 : ℕ) : ℤ) - 4 by norm_num, h1]
  exact h3.symm.le.trans h2

open UnderlyingSpace borelMooreHomology in
/-- **Supported cohomology along a projective surface in a smooth threefold.** Let `M` be a
smooth quasi-projective complex threefold and `j : Q ⟶ M` a closed immersion of a proper scheme
of dimension at most two. On every open neighbourhood `U` of `j(Q)(ℂ)`, `H²(U, U ∖ j(Q)(ℂ); ℚ)`
has rank at most the number of irreducible components of `Q`: by supported duality it is
`H_4(j(Q)(ℂ); ℚ)`, which is bounded by the components. -/
private theorem rank_cohomologyWithSupports_range_le {M Q : Scheme.{0}} [M.Over (Spec (.of ℂ))]
    [IsComplexScheme M] [IsIntegral M] [IsSeparated (M ↘ Spec (.of ℂ))]
    (hqp : IsQuasiProjectiveVariety ℂ (M ↘ Spec (.of ℂ)))
    [SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ))]
    (j : Q ⟶ M) [IsClosedImmersion j] [IsProper (j ≫ M ↘ Spec (.of ℂ))]
    [Finite (irreducibleComponents Q)]
    (hdim : topologicalKrullDim Q ≤ ((2 : ℕ) : WithBot ℕ∞))
    (U : Opens (TopCat.of (UnderlyingSpace ℂ M)))
    (hDU : pointsOver (K := ℂ) (Set.range j.base) ⊆ U) :
    Module.rank ℚ (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of U)
      ((inclHom U) ⁻¹' pointsOver (K := ℂ) (Set.range j.base)) 2) ≤
      Nat.card (irreducibleComponents Q) := by
  classical
  let D : Closeds M := ⟨Set.range j.base, j.isClosedEmbedding.isClosed_range⟩
  -- the reduced subscheme on `j(Q)` is proper
  have hD : IsProper ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫ M ↘ Spec (.of ℂ)) := by
    set I := Scheme.IdealSheafData.vanishingIdeal D
    have hker : j.ker ≤ I.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
      intro x hx
      rw [← SetLike.mem_coe, Scheme.Hom.support_ker]
      exact subset_closure hx
    let l := IsClosedImmersion.lift j I.subschemeι hker
    have hl : l ≫ j = I.subschemeι := IsClosedImmersion.lift_fac _ _ _
    rw [← hl, Category.assoc]
    haveI : IsClosedImmersion (l ≫ j) := hl ▸ inferInstance
    haveI : IsClosedImmersion l := IsClosedImmersion.of_comp l j
    infer_instance
  have hdual := ((MMP.Analytic.supportedDuality_of_isQuasiProjectiveVariety (d := 3) hqp rfl D hD).2.2.2
    U hDU 4).1
  have h1 := (LinearEquiv.ofBijective _ hdual).rank_eq
  have hA : Set.range (fun a : ((inclHom U) ⁻¹' pointsOver (K := ℂ) (Set.range j.base) : Set U) ↦
      (a.1.1 : UnderlyingSpace ℂ M)) = pointsOver (Set.range j.base) := by
    ext x
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.2, fun hx ↦ ⟨⟨⟨x, hDU hx⟩, hx⟩, rfl⟩⟩
  have hb := bijective_pushforward_homeomorph ℚ
    (Y := TopCat.of ((inclHom U) ⁻¹' pointsOver (K := ℂ) (Set.range j.base) : Set U))
    (Y' := TopCat.of (pointsOver (K := ℂ) (Set.range j.base)))
    ((Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr hA)) ((2 * 2 : ℕ) : ℤ)
  have h2 := (LinearEquiv.ofBijective _ hb).rank_eq
  -- the images of the components
  let s : Finset (Set M) := (irreducibleComponents Q).toFinite.toFinset.image (j.base '' ·)
  have hs : (⋃ S ∈ s, S) = Set.range j.base := by
    ext x
    simp only [s, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_, ⟨C, -, rfl⟩, y, -, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨C, hC, hyC⟩ := Set.mem_sUnion.1 ((sUnion_irreducibleComponents (X := Q)).symm ▸
        Set.mem_univ y)
      exact ⟨_, ⟨C, hC, rfl⟩, y, hyC, rfl⟩
  have hbound := rank_borelMooreHomology_pointsOver_biUnion_le s
    (by
      intro S hS
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hS
      exact j.isClosedEmbedding.isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ ((Set.Finite.mem_toFinset _).1 hC)))
    (by
      intro S hS
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hS
      exact ((Set.Finite.mem_toFinset _).1 hC).1.image _ j.continuous.continuousOn)
    (by
      intro S hS
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hS
      have e := (j.isClosedEmbedding.isEmbedding.comp
        (Topology.IsEmbedding.subtypeVal (p := (· ∈ C)))).toHomeomorph.trans
          (Homeomorph.setCongr (by rw [Set.range_comp, Subtype.range_coe]))
      rw [← e.isHomeomorph.topologicalKrullDim_eq]
      exact (topologicalKrullDim_subspace_le Q C).trans hdim)
    (by
      intro S hS S' hS' hSS'
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hS
      obtain ⟨C', hC', rfl⟩ := Finset.mem_image.1 hS'
      have hC₁ := (Set.Finite.mem_toFinset _).1 hC
      have hC₁' := (Set.Finite.mem_toFinset _).1 hC'
      have hsub : C ⊆ C' := fun y hy ↦ by
        obtain ⟨y', hy', hyy'⟩ := hSS' ⟨y, hy, rfl⟩
        exact j.isClosedEmbedding.injective hyy' ▸ hy'
      rw [hC₁.2 hC₁'.1 hsub |>.antisymm hsub])
  rw [show ((2 : ℤ)) = ((2 * 3 : ℕ) : ℤ) - 4 by norm_num]
  refine h1.trans_le (h2.trans_le ?_)
  have hcard : (s.card : Cardinal) ≤ Nat.card (irreducibleComponents Q) := by
    have : s.card ≤ (irreducibleComponents Q).toFinite.toFinset.card := Finset.card_image_le
    rw [← Set.ncard_eq_toFinset_card _ (irreducibleComponents Q).toFinite,
      ← Nat.card_coe_set_eq] at this
    exact_mod_cast this
  refine le_trans (le_of_eq ?_) (hbound.trans hcard)
  rw [hs]

/-! ### Local classes of exceptional components -/

section LocalClass

variable {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}

/-- On the smooth resolution `Z` of a curve-and-point exceptional model, `𝒪_Z(E)` is invertible
for every prime divisor `E`: every divisor of a smooth scheme is Cartier. -/
private theorem isInvertible_divisorialSheaf_single (hM : IsCurvePointExceptionalModel sY r F D)
    (E : Mori.PrimeDivisor Z) :
    SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)) := by
  haveI : QuasiCompact (r ≫ sY) := inferInstance
  have hC := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hM.isResolution.2.2.1
    (Finsupp.single E 1 : Divisor Z)
  haveI := hC.isInvertible_divisorialSheaf
  exact Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible

/-! ### Canonical local classes -/

/-- Composites of maps of relative cohomology. -/
private theorem relMap_apply {Y'' Y' Y : TopCat.{0}} (g : Y'' ⟶ Y') (f : Y' ⟶ Y)
    {A'' : Set Y''} {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A') (hf : A' ⊆ f ⁻¹' A) (j : ℤ)
    (x : relativeSingularCohomology ℚ (ModuleCat.of ℚ ℚ) Y A j) :
    (relativeSingularCohomology.map ℚ _ g hg j).hom
        ((relativeSingularCohomology.map ℚ _ f hf j).hom x) =
      (relativeSingularCohomology.map ℚ _ (g ≫ f) (fun _ hx ↦ hf (hg hx)) j).hom x := by
  rw [relativeSingularCohomology.map_comp ℚ _ g f hg hf j]
  rfl

/-- Maps of relative cohomology along equal continuous maps are equal. -/
private theorem relMap_congr {Y' Y : TopCat.{0}} {f f' : Y' ⟶ Y} (e : f = f') {A' : Set Y'}
    {A : Set Y} (h : A' ⊆ f ⁻¹' A) (h' : A' ⊆ f' ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f h j =
      relativeSingularCohomology.map ℚ _ f' h' j := by
  subst e
  rfl

/-- The complex points of `Z` lying on a prime divisor `E`. -/
private abbrev analyticSupport (E : Mori.PrimeDivisor Z) :
    Set (analyticSpace (Z ↘ Spec (.of ℂ))) :=
  {x | x.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)}

/-- `c₁(𝒪_Z(E))` lifts to `H²(Z^an, Z^an ∖ E^an; ℚ)`: it vanishes off `E`. -/
private theorem exists_thomLift (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))] :
    ∃ τ : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (analyticSpace (Z ↘ Spec (.of ℂ)))
        (analyticSupport E) 2,
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom τ =
        singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (algebraicFirstChernClass (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))) :=
  (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ _ _ 2 _).1
    (rationalCohomologyMap_firstChernClass_eq_zero E _ fun x ↦ x.2)

/-- A chosen lift `τ_E ∈ H²(Z^an, Z^an ∖ E^an; ℚ)` of `c₁(𝒪_Z(E))`. -/
private noncomputable def thomLift (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))] :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (analyticSpace (Z ↘ Spec (.of ℂ)))
      (analyticSupport E) 2 :=
  (exists_thomLift E).choose

private theorem toCohomology_thomLift (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))] :
    (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom (thomLift E) =
      singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
        (algebraicFirstChernClass (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))) :=
  (exists_thomLift E).choose_spec

/-- Supported cohomology is invariant under homeomorphisms. -/
private noncomputable def cohomologyWithSupportsHomeomorphIso {X X' : TopCat.{0}} (h : X ≃ₜ X')
    (A : Set X') (n : ℤ) :
    cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X' A n ≅
      cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) X (h ⁻¹' A) n where
  hom := cohomologyWithSupports.pullback ℚ _ (TopCat.ofHom ⟨h, h.continuous⟩) A n
  inv := relativeSingularCohomology.map ℚ _ (TopCat.ofHom ⟨h.symm, h.symm.continuous⟩)
    (A' := Aᶜ) (A := (h ⁻¹' A)ᶜ) (fun x hx hx' ↦ hx (by simpa using hx')) n
  hom_inv_id := by
    refine (relativeSingularCohomology.map_comp ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨h.symm, h.symm.continuous⟩) (TopCat.ofHom ⟨h, h.continuous⟩)
      (A'' := Aᶜ) (A' := (h ⁻¹' A)ᶜ) (A := Aᶜ) (fun x hx hx' ↦ hx (by simpa using hx'))
      (fun _ hx ↦ hx) n).symm.trans ?_
    refine (relMap_congr (f' := 𝟙 X') (by ext x; exact h.apply_symm_apply x) _
      (fun _ hx ↦ hx) n).trans ?_
    exact relativeSingularCohomology.map_id _ _ _ _ _
  inv_hom_id := by
    refine (relativeSingularCohomology.map_comp ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom ⟨h, h.continuous⟩) (TopCat.ofHom ⟨h.symm, h.symm.continuous⟩)
      (A'' := (h ⁻¹' A)ᶜ) (A' := Aᶜ) (A := (h ⁻¹' A)ᶜ) (fun _ hx ↦ hx)
      (fun x hx hx' ↦ hx (by simpa using hx')) n).symm.trans ?_
    refine (relMap_congr (f' := 𝟙 X) (by ext x; exact h.symm_apply_apply x) _
      (fun _ hx ↦ hx) n).trans ?_
    exact relativeSingularCohomology.map_id _ _ _ _ _

open UnderlyingSpace in
/-- `rank_cohomologyWithSupports_range_le`, read on the complex points `M^an`. -/
private theorem rank_cohomologyWithSupports_range_le' {M Q : Scheme.{0}} [M.Over (Spec (.of ℂ))]
    [IsComplexScheme M] [IsIntegral M] [IsSeparated (M ↘ Spec (.of ℂ))]
    (hqp : IsQuasiProjectiveVariety ℂ (M ↘ Spec (.of ℂ)))
    [SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ))]
    (j : Q ⟶ M) [IsClosedImmersion j] [IsProper (j ≫ M ↘ Spec (.of ℂ))]
    [Finite (irreducibleComponents Q)]
    (hdim : topologicalKrullDim Q ≤ ((2 : ℕ) : WithBot ℕ∞))
    (U' : Opens (analyticSpace (M ↘ Spec (.of ℂ))))
    (hU' : ∀ x : analyticSpace (M ↘ Spec (.of ℂ)),
      x.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range j.base → x ∈ U') :
    Module.rank ℚ (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of U')
      {x : U' | x.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range j.base} 2) ≤
      Nat.card (irreducibleComponents Q) := by
  let e := ComplexPoints.homeomorphUnderlyingSpace (X := M)
  let U : Opens (TopCat.of (UnderlyingSpace ℂ M)) := ⟨e '' U', e.isOpenMap _ U'.isOpen⟩
  have hDU : pointsOver (K := ℂ) (Set.range j.base) ⊆ U := by
    intro p hp
    refine ⟨e.symm p, hU' _ ?_, e.apply_symm_apply p⟩
    exact hp
  let h : (U' : Set (analyticSpace (M ↘ Spec (.of ℂ)))) ≃ₜ (U : Set (UnderlyingSpace ℂ M)) :=
    e.image (U' : Set (analyticSpace (M ↘ Spec (.of ℂ))))
  have hb := rank_cohomologyWithSupports_range_le hqp j hdim U hDU
  have hiso := (cohomologyWithSupportsHomeomorphIso (X := TopCat.of U') (X' := TopCat.of U) h
    ((borelMooreHomology.inclHom U) ⁻¹' pointsOver (K := ℂ) (Set.range j.base)) 2).toLinearEquiv.rank_eq
  refine le_of_eq_of_le ?_ (hiso.symm.le.trans hb)
  rfl

/-- Forgetting supports commutes with pullback. -/
private theorem relMap_comp_toCohomology {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) {X' : Set Y'}
    {X : Set Y} (h : X'ᶜ ⊆ f ⁻¹' Xᶜ) (g : Y' ⟶ Y) (hfg : f = g) :
    relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f h 2 ≫
        cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y' X' 2 =
      cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) Y X 2 ≫
        rationalCohomologyMap g 2 := by
  subst hfg
  exact ((relativeSingularCohomology.map_comp ℚ _ (𝟙 Y') f
    (fun _ hx ↦ (hx (Set.mem_univ _)).elim) h 2).symm.trans
      (relMap_congr (by rw [Category.id_comp, Category.comp_id]) _ _ 2)).trans
    (relativeSingularCohomology.map_comp ℚ _ f (𝟙 Y) (A'' := (Set.univ : Set Y')ᶜ)
      (A' := (Set.univ : Set Y)ᶜ) (fun _ hx ↦ (hx (Set.mem_univ _)).elim)
      (fun _ hx ↦ (hx (Set.mem_univ _)).elim) 2)

/-- Restricting the class of `(excision)⁻¹ τ` to the excised open gives the class of `τ`. -/
private theorem rationalCohomologyMap_toCohomology_excisionIso_inv {W : TopCat.{0}}
    {G A : Set W} (hA : IsOpen A) (hG : IsClosed G) (hGA : G ⊆ A)
    (τ : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A)
      ((subspaceInclusion W A) ⁻¹' G) 2) :
    (rationalCohomologyMap (X' := TopCat.of A)
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom
      ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) W G 2).hom
        ((cohomologyWithSupports.excisionIso ℚ hA hG hGA 2).inv τ)) =
      (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ _ 2).hom τ := by
  have key := relMap_comp_toCohomology (subspaceInclusion W A) (X := G)
    (X' := (subspaceInclusion W A) ⁻¹' G) (fun _ hx ↦ hx)
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) rfl
  have e := congrArg (fun φ ↦ φ.hom ((cohomologyWithSupports.excisionIso ℚ hA hG hGA 2).inv τ))
    key
  simp only [ModuleCat.comp_apply] at e
  rw [← e]
  congr 1
  have hu := Iso.inv_hom_id_apply (cohomologyWithSupports.excisionIso ℚ hA hG hGA 2) τ
  rw [cohomologyWithSupports.excisionIso_hom] at hu
  exact hu

/-- The realization of a proper morphism to a scheme locally of finite type over `ℂ` is a proper
map: under `homeomorphUnderlyingSpace` it is the induced map of underlying spaces. -/
private theorem isProperMap_analyticMap {X B : Scheme.{0}} (f : X ⟶ B) (sB : B ⟶ Spec (.of ℂ))
    [IsProper f] [LocallyOfFiniteType sB] :
    IsProperMap (analyticMap f (sY := sB) rfl) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨f ≫ sB⟩
  letI : B.Over (Spec (.of ℂ)) := ⟨sB⟩
  haveI : f.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : LocallyOfFiniteType (B ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sB›
  have heq : (analyticMap f (sY := sB) rfl : analyticSpace (f ≫ sB) → analyticSpace sB) =
      ComplexPoints.homeomorphUnderlyingSpace.symm ∘ UnderlyingSpace.map (K := ℂ) f ∘
        ComplexPoints.homeomorphUnderlyingSpace := by
    funext x
    exact ComplexPoints.homeomorphUnderlyingSpace.eq_symm_apply.mpr (UnderlyingSpace.ext rfl)
  rw [heq]
  exact ComplexPoints.homeomorphUnderlyingSpace.symm.isProperMap.comp
    ((UnderlyingSpace.isProperMap_map (K := ℂ) f).comp
      ComplexPoints.homeomorphUnderlyingSpace.isProperMap)

/-- The realization of a closed immersion of schemes locally of finite type over `ℂ` is a closed
embedding. -/
private theorem isClosedEmbedding_analyticMap {X B : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sB : B ⟶ Spec (.of ℂ)} (f : X ⟶ B) (hf : f ≫ sB = sX) [IsClosedImmersion f]
    [LocallyOfFiniteType sB] :
    Topology.IsClosedEmbedding (analyticMap f hf) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : B.Over (Spec (.of ℂ)) := ⟨sB⟩
  haveI : f.IsOver (Spec (.of ℂ)) := ⟨hf⟩
  haveI : LocallyOfFiniteType (B ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sB›
  have heq : (analyticMap f hf : analyticSpace sX → analyticSpace sB) =
      ComplexPoints.homeomorphUnderlyingSpace.symm ∘ UnderlyingSpace.map (K := ℂ) f ∘
        ComplexPoints.homeomorphUnderlyingSpace := by
    funext x
    exact ComplexPoints.homeomorphUnderlyingSpace.eq_symm_apply.mpr (UnderlyingSpace.ext rfl)
  rw [heq]
  exact ComplexPoints.homeomorphUnderlyingSpace.symm.isClosedEmbedding.comp
    ((UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).comp
      ComplexPoints.homeomorphUnderlyingSpace.isClosedEmbedding)

section Canonical

variable {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}

/-- The map `r⁻¹(V) ⟶ Z^an` of a tube. -/
private noncomputable def tubeMap (hM : IsCurvePointExceptionalModel sY r F D)
    (V : Opens (analyticSpace sY)) :
    preimageSpace (resolutionAnalyticMap sY r) V ⟶ analyticSpace (Z ↘ Spec (.of ℂ)) :=
  TopCat.ofHom (X := preimageSpace (resolutionAnalyticMap sY r) V) (Y := analyticSpace (r ≫ sY))
      ⟨Subtype.val, continuous_subtype_val⟩ ≫
    analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)

/-- The points of the tube `r⁻¹(V)` on `E`. -/
private abbrev tubeSupport (V : Opens (analyticSpace sY)) (E : Mori.PrimeDivisor Z) :
    Set (preimageSpace (resolutionAnalyticMap sY r) V) :=
  {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)}

private theorem tubeMap_preimage (hM : IsCurvePointExceptionalModel sY r F D)
    (V : Opens (analyticSpace sY)) (E : Mori.PrimeDivisor Z) :
    tubeMap hM V ⁻¹' analyticSupport E = tubeSupport V E := by
  ext z
  change (z.1.hom ≫ 𝟙 Z).base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z) ↔ _
  rw [Category.comp_id]
  exact Iff.rfl

/-- On `r⁻¹V ∖ K`, the points off `G` lie off `E`. -/
private theorem canonicalClass_subset (hM : IsCurvePointExceptionalModel sY r F D)
    (E : Mori.PrimeDivisor Z) (V : Opens (analyticSpace sY))
    (G : Set (preimageSpace (resolutionAnalyticMap sY r) V)) :
    ((subspaceInclusion _ (tubeSupport V E \ G)ᶜ) ⁻¹' G)ᶜ ⊆
      (subspaceInclusion _ (tubeSupport V E \ G)ᶜ ≫ tubeMap hM V) ⁻¹' (analyticSupport E)ᶜ :=
  fun x hx hxE ↦ hx (by
    by_contra hxG
    exact x.2 ⟨(Set.ext_iff.1 (tubeMap_preimage hM V E) x.1).1 hxE, hxG⟩)

/-- **The canonical local class.** For a closed piece `G ⊆ E^an ∩ r⁻¹(V)` whose complement
`K = (E^an ∩ r⁻¹V) ∖ G` in `E^an ∩ r⁻¹V` is closed: restrict `τ_E` to `r⁻¹V ∖ K`, where its
support is `G`, excise back to `r⁻¹V` and forget the supports. -/
private noncomputable def canonicalClass (hM : IsCurvePointExceptionalModel sY r F D)
    (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))]
    (V : Opens (analyticSpace sY)) (G : Set (preimageSpace (resolutionAnalyticMap sY r) V))
    (hG : IsClosed G) (hK : IsClosed (tubeSupport V E \ G)) :
    rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2 :=
  (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ G 2).hom
    ((cohomologyWithSupports.excisionIso ℚ hK.isOpen_compl hG
      (fun x hx hx' ↦ hx'.2 hx) 2).inv
      ((relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ)
        (subspaceInclusion _ (tubeSupport V E \ G)ᶜ ≫ tubeMap hM V)
        (canonicalClass_subset hM E V G) 2).hom (thomLift E)))

private theorem canonicalClass_compl_eq_zero (hM : IsCurvePointExceptionalModel sY r F D)
    (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))]
    (V : Opens (analyticSpace sY)) (G : Set (preimageSpace (resolutionAnalyticMap sY r) V))
    (hG : IsClosed G) (hK : IsClosed (tubeSupport V E \ G)) :
    (rationalCohomologyMap (X' := TopCat.of (Gᶜ : Set _))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom
        (canonicalClass hM E V G hG hK) = 0 :=
  (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ _ G 2).apply_apply_eq_zero _

private theorem canonicalClass_restrict (hM : IsCurvePointExceptionalModel sY r F D)
    (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))]
    (V : Opens (analyticSpace sY)) (G : Set (preimageSpace (resolutionAnalyticMap sY r) V))
    (hG : IsClosed G) (hK : IsClosed (tubeSupport V E \ G)) :
    (rationalCohomologyMap (X' := TopCat.of ((tubeSupport V E \ G)ᶜ : Set _))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom
        (canonicalClass hM E V G hG hK) =
      (rationalCohomologyMap
        (TopCat.ofHom (X := TopCat.of ((tubeSupport V E \ G)ᶜ :
            Set (preimageSpace (resolutionAnalyticMap sY r) V)))
          (Y := analyticSpace (r ≫ sY))
          ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
          analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) 2).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (algebraicFirstChernClass
            (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)))) := by
  unfold canonicalClass
  refine (rationalCohomologyMap_toCohomology_excisionIso_inv _ hG _ _).trans ?_
  rw [← toCohomology_thomLift E]
  have key := relMap_comp_toCohomology
    (subspaceInclusion _ (tubeSupport V E \ G)ᶜ ≫ tubeMap hM V)
    (X' := ((subspaceInclusion _ (tubeSupport V E \ G)ᶜ) ⁻¹' G)) (X := analyticSupport E)
    (canonicalClass_subset hM E V G)
    (TopCat.ofHom (X := TopCat.of ((tubeSupport V E \ G)ᶜ :
            Set (preimageSpace (resolutionAnalyticMap sY r) V)))
          (Y := analyticSpace (r ≫ sY))
          ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
          analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) rfl
  exact congrArg (fun φ ↦ φ.hom (thomLift E)) key

/-- **Restriction of canonical classes.** For `V' ≤ V`, the canonical class of `G` restricts on
`r⁻¹V'` to the canonical class of `G ∩ r⁻¹V'`. -/
private theorem canonicalClass_preimageInclusion (hM : IsCurvePointExceptionalModel sY r F D)
    (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))]
    {V V' : Opens (analyticSpace sY)} (hle : V' ≤ V)
    (G : Set (preimageSpace (resolutionAnalyticMap sY r) V))
    (hG : IsClosed G) (hK : IsClosed (tubeSupport V E \ G))
    (hG' : IsClosed (preimageInclusion (resolutionAnalyticMap sY r) hle ⁻¹' G))
    (hK' : IsClosed (tubeSupport V' E \ preimageInclusion (resolutionAnalyticMap sY r) hle ⁻¹' G)) :
    (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) hle) 2).hom
        (canonicalClass hM E V G hG hK) =
      canonicalClass hM E V' _ hG' hK' := by
  let ι := preimageInclusion (resolutionAnalyticMap sY r) hle
  let A := (tubeSupport V E \ G)ᶜ
  let A' := (tubeSupport V' E \ ι ⁻¹' G)ᶜ
  let ιA : TopCat.of A' ⟶ TopCat.of A :=
    TopCat.ofHom ⟨fun x ↦ ⟨ι x.1, x.2⟩, (ι.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let e := cohomologyWithSupports.excisionIso ℚ hK.isOpen_compl hG (fun x hx hx' ↦ hx'.2 hx) 2
  let e' := cohomologyWithSupports.excisionIso ℚ hK'.isOpen_compl hG' (fun x hx hx' ↦ hx'.2 hx) 2
  let τ := (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ)
    (subspaceInclusion _ A ≫ tubeMap hM V) (canonicalClass_subset hM E V G) 2).hom (thomLift E)
  let τ' := (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ)
    (subspaceInclusion _ A' ≫ tubeMap hM V') (canonicalClass_subset hM E V' (ι ⁻¹' G)) 2).hom
      (thomLift E)
  show (rationalCohomologyMap ι 2).hom
      ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ G 2).hom (e.inv.hom τ)) =
    (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ (ι ⁻¹' G) 2).hom (e'.inv.hom τ')
  have k1 := relMap_comp_toCohomology ι (X := G) (X' := ι ⁻¹' G) (fun _ hx ↦ hx) ι rfl
  rw [← ModuleCat.comp_apply, ← k1, ModuleCat.comp_apply]
  refine congrArg (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) _ (ι ⁻¹' G) 2).hom ?_
  refine (Iso.hom_inv_id_apply e' _).symm.trans (congrArg e'.inv.hom ?_)
  have hu : (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (subspaceInclusion _ A)
      (fun _ hx ↦ hx) 2).hom (e.inv.hom τ) = τ := Iso.inv_hom_id_apply e τ
  change (relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) (subspaceInclusion _ A')
      (fun _ hx ↦ hx) 2).hom ((relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) ι
        (fun _ hx ↦ hx) 2).hom (e.inv.hom τ)) = τ'
  refine (relMap_apply _ _ _ _ 2 _).trans ?_
  refine (congrArg (fun φ ↦ φ.hom (e.inv.hom τ))
    (relMap_congr (f' := ιA ≫ subspaceInclusion _ A) rfl _ (fun x hx ↦ hx) 2)).trans ?_
  refine (relMap_apply ιA (subspaceInclusion _ A) (fun x hx ↦ hx) (fun x hx ↦ hx) 2 _).symm.trans ?_
  refine (congrArg (relativeSingularCohomology.map ℚ _ ιA (fun x hx ↦ hx) 2).hom hu).trans ?_
  refine (relMap_apply _ _ _ _ 2 _).trans ?_
  exact congrArg (fun φ ↦ φ.hom (thomLift E))
    (relMap_congr (f := ιA ≫ subspaceInclusion _ A ≫ tubeMap hM V)
      (f' := subspaceInclusion _ A' ≫ tubeMap hM V') rfl _
      (canonicalClass_subset hM E V' (ι ⁻¹' G)) 2)

/-- The canonical class depends only on the set `G`. -/
private theorem canonicalClass_congr (hM : IsCurvePointExceptionalModel sY r F D)
    (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))]
    (V : Opens (analyticSpace sY)) {G G' : Set (preimageSpace (resolutionAnalyticMap sY r) V)}
    (e : G = G') (hG : IsClosed G) (hK : IsClosed (tubeSupport V E \ G)) (hG' : IsClosed G')
    (hK' : IsClosed (tubeSupport V E \ G')) :
    canonicalClass hM E V G hG hK = canonicalClass hM E V G' hG' hK' := by
  subst e
  rfl

/-- The realization `r^an` of the resolution is a proper map. -/
private theorem isProperMap_resolutionAnalyticMap (hM : IsCurvePointExceptionalModel sY r F D) :
    IsProperMap (resolutionAnalyticMap sY r) := by
  haveI : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI : LocallyOfFiniteType sY := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType (f := sY)
  haveI := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
  exact isProperMap_analyticMap r sY

/-- **The tube lemma.** A closed subset `C` of the tube `r⁻¹V` missing the fibre over `y ∈ V`
misses a smaller tube `r⁻¹V'`, `y ∈ V' ≤ V`. -/
private theorem exists_le_forall_notMem (hM : IsCurvePointExceptionalModel sY r F D)
    {V : Opens (analyticSpace sY)} {y : analyticSpace sY} (hy : y ∈ V)
    (C : Set (preimageSpace (resolutionAnalyticMap sY r) V)) (hC : IsClosed C)
    (hCy : ∀ z ∈ C, resolutionAnalyticMap sY r z.1 ≠ y) :
    ∃ (V' : Opens (analyticSpace sY)) (hle : V' ≤ V), y ∈ V' ∧
      ∀ z, preimageInclusion (resolutionAnalyticMap sY r) hle z ∉ C := by
  have hp := (isProperMap_resolutionAnalyticMap hM).restrictPreimage (V : Set (analyticSpace sY))
  set K := (Set.restrictPreimage (V : Set (analyticSpace sY)) (resolutionAnalyticMap sY r)) '' C
  have hK : IsClosed K := hp.isClosedMap _ hC
  refine ⟨⟨Subtype.val '' Kᶜ, V.isOpen.isOpenMap_subtype_val _ hK.isOpen_compl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨w, -, rfl⟩
    exact w.2
  · refine ⟨⟨y, hy⟩, fun ⟨z, hz, hzy⟩ ↦ hCy z hz ?_, rfl⟩
    exact congrArg Subtype.val hzy
  · intro z hz
    obtain ⟨w, hw, hwz⟩ := z.2
    exact hw ⟨_, hz, Subtype.ext hwz.symm⟩

end Canonical

/-- A class `α ∈ H²(r⁻¹V; ℚ)` is a *local class of `E` along the component `S` of `F_t`* if it
is the canonical class of a relatively clopen piece `G = O ∩ E^an` of `E^an ∩ r⁻¹V` meeting `F_t`
exactly in `S`. -/
private def IsLocalClass (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z)
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2) : Prop :=
  ∃ (G : Set (preimageSpace (resolutionAnalyticMap sY r) V)) (hG : IsClosed G)
    (hK : IsClosed (tubeSupport V E \ G)),
    (∃ O : Set (preimageSpace (resolutionAnalyticMap sY r) V), IsOpen O ∧
      G = O ∩ tubeSupport V E) ∧
    (∀ y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
      pointFibreInclusion sY r To t hV y ∈ G ↔
        y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t))) ∧
    α = @canonicalClass _ _ _ _ _ _ _ _ _ _ _ _ _ hM E (isInvertible_divisorialSheaf_single hM E)
      V G hG hK

/-- A local class vanishes off its piece `G` and agrees with `c₁(𝒪_Z(E))` off the rest. -/
private theorem IsLocalClass.properties {hM : IsCurvePointExceptionalModel sY r F D}
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    {t : analyticSpace (To.ι ≫ curveι T ≫ sY)} {S : irreducibleComponents (pointFibre sY r To t)}
    {E : Mori.PrimeDivisor Z} {V : Opens (analyticSpace sY)} {hV : curveOpenInclusion sY To t ∈ V}
    {α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2}
    (h : IsLocalClass hM To t S E hV α) :
    ∃ G : Set (preimageSpace (resolutionAnalyticMap sY r) V),
      IsClosed G ∧
      (∃ O : Set (preimageSpace (resolutionAnalyticMap sY r) V), IsOpen O ∧
        G = O ∩ {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)}) ∧
      (∀ y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
        pointFibreInclusion sY r To t hV y ∈ G ↔
          y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t))) ∧
      (rationalCohomologyMap (X' := TopCat.of (Gᶜ : Set _))
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α = 0 ∧
      ∃ _ : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
          (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)),
        (rationalCohomologyMap
            (X' := TopCat.of (({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈
              (E.support : Set Z)} \ G)ᶜ :
                Set (preimageSpace (resolutionAnalyticMap sY r) V)))
            (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α =
          (rationalCohomologyMap
            (TopCat.ofHom (X := TopCat.of (({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈
              (E.support : Set Z)} \ G)ᶜ :
                Set (preimageSpace (resolutionAnalyticMap sY r) V)))
              (Y := analyticSpace (r ≫ sY))
              ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
              analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) 2).hom
            (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
              (algebraicFirstChernClass
                (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)))) := by
  obtain ⟨G, hG, hK, hGO, hfib, rfl⟩ := h
  haveI := isInvertible_divisorialSheaf_single hM E
  exact ⟨G, hG, hGO, hfib, canonicalClass_compl_eq_zero hM E V G hG hK, inferInstance,
    canonicalClass_restrict hM E V G hG hK⟩

/-- The points of a tube on a prime divisor form a closed set. -/
private theorem isClosed_tubeSupport (V : Opens (analyticSpace sY)) (E : Mori.PrimeDivisor Z) :
    IsClosed (tubeSupport (r := r) V E) := by
  have h : tubeSupport (r := r) V E = Subtype.val ⁻¹'
      {x : ComplexPoints (r ≫ sY) | x.toScheme ∈ (E.support : Set Z)} := by
    ext z
    change _ ↔ z.1.hom (default : Spec (.of ℂ)) ∈ (E.support : Set Z)
    rw [Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)]
    rfl
  rw [h]
  exact (isClosed_setOf_toScheme_mem E.idealSheaf.support.isClosed).preimage
    continuous_subtype_val

/-- **Local classes from a clopen piece.** If `G` is a closed piece `O ∩ E^an` of `E^an ∩ r⁻¹V`,
then its canonical class is a local class of `E` along every component `S` of every fibre `F_t`
which `G` meets exactly in `S`. -/
private theorem exists_forall_isLocalClass (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens) (E : Mori.PrimeDivisor Z)
    {V : Opens (analyticSpace sY)}
    (G : Set (preimageSpace (resolutionAnalyticMap sY r) V)) (hG : IsClosed G)
    (O : Set (preimageSpace (resolutionAnalyticMap sY r) V)) (hO : IsOpen O)
    (hGO : G = O ∩ {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)}) :
    ∃ α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2,
      ∀ (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
        (S : irreducibleComponents (pointFibre sY r To t)) (hV : curveOpenInclusion sY To t ∈ V),
        (∀ y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
          pointFibreInclusion sY r To t hV y ∈ G ↔
            y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t))) →
        IsLocalClass hM To t S E hV α := by
  have hEG : IsClosed (tubeSupport V E \ G) := by
    rw [hGO, Set.diff_inter_self_eq_diff, Set.diff_eq]
    exact (isClosed_tubeSupport V E).inter hO.isClosed_compl
  exact ⟨_, fun t S hV hfib ↦ ⟨G, hG, hEG, ⟨O, hO, hGO⟩, hfib, rfl⟩⟩

variable (sY r) in
/-- The germ in `𝒲_t` of a class `α ∈ H²(r⁻¹V; ℚ)`, for `V` a neighbourhood of `t` in `Y^an`. -/
private noncomputable abbrev classGerm {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2) :
    resolutionLocalSystemFibre sY r To t :=
  (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY r 2) t).hom
    ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α)

variable (sY r) in
/-- The germ of a class is the germ of its restriction to a smaller tube. -/
private theorem classGerm_restrict {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V V' : Opens (analyticSpace sY)} (hle : V' ≤ V)
    (hV' : curveOpenInclusion sY To t ∈ V')
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2) :
    classGerm sY r To t (hle hV') α = classGerm sY r To t hV'
      ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) hle) 2).hom α) := by
  have h := (directImagePresheaf (resolutionAnalyticMap sY r) 2).germ_res_apply (homOfLE hle) _
    hV' α
  unfold classGerm higherDirectImageGerm
  exact congrArg (fun x ↦ (stalkToPullbackStalk (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY r 2) t).hom
      (((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) _).map
        (toSheafify _ (directImagePresheaf (resolutionAnalyticMap sY r) 2))).hom x)) h.symm

variable (sY r) in
/-- *Proper base change on germs* over a Zariski-open `T° ⊆ T`: a class on a tube `r⁻¹(V)`
whose restriction to the fibre `r⁻¹(t)` vanishes has zero germ in `𝒲_t`. -/
private def BaseChangeInjective {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens) : Prop :=
  ∀ (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
    (rationalCohomologyMap (TopCat.ofHom (X := TopCat.of
        (resolutionAnalyticMap sY r ⁻¹' {curveOpenInclusion sY To t}))
      ⟨Set.inclusion (Set.preimage_mono (Set.singleton_subset_iff.2 hV)),
        continuous_inclusion _⟩) 2).hom α = 0 →
    classGerm sY r To t hV α = 0

/-- Every point of `r⁻¹(V)` over the image of `t` comes from the fibre `F_t`. -/
private theorem exists_pointFibreInclusion_eq {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (z : preimageSpace (resolutionAnalyticMap sY r) V)
    (hz : resolutionAnalyticMap sY r z.1 = curveOpenInclusion sY To t) :
    ∃ y, pointFibreInclusion sY r To t hV y = z := by
  have h : z.1.hom ≫ r = 𝟙 _ ≫ t.hom ≫ To.ι ≫ curveι T := by
    rw [Category.id_comp]
    exact congrArg ComplexPoints.hom hz
  exact ⟨⟨pullback.lift z.1.hom (𝟙 _) h, pullback.lift_snd _ _ _⟩,
    Subtype.ext (ComplexPoints.ext (pullback.lift_fst _ _ _))⟩

/-- **Base change on germs, through the scheme fibre.** Under `BaseChangeInjective`, a class on a
tube whose restriction to `F_t(ℂ)` vanishes has zero germ: `F_t(ℂ)` is homeomorphic to the
topological fibre `r⁻¹(t)`. -/
private theorem classGerm_eq_zero_of_pointFibreInclusion (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens} (hbc : BaseChangeInjective sY r To)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
    (h : (rationalCohomologyMap (pointFibreInclusion sY r To t hV) 2).hom α = 0) :
    classGerm sY r To t hV α = 0 := by
  apply hbc t hV α
  haveI : MMP.Mori.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  haveI : LocallyOfFiniteType (r ≫ sY) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  have hb : (t.hom ≫ To.ι ≫ curveι T) ≫ sY = 𝟙 _ := by
    simpa [Category.assoc] using t.hom_comp_structure
  haveI : IsClosedImmersion (t.hom ≫ To.ι ≫ curveι T) := isClosedImmersion_of_comp_eq_id sY _ hb
  haveI : IsClosedImmersion (pointFibreFst sY r To t) := by
    change IsClosedImmersion (pullback.fst r (t.hom ≫ To.ι ≫ curveι T))
    infer_instance
  have hce := isClosedEmbedding_analyticMap (pointFibreFst sY r To t)
    (pointFibreFst_comp_structure sY r To t)
  let fib := resolutionAnalyticMap sY r ⁻¹' {curveOpenInclusion sY To t}
  have hmem : ∀ x, pointFibreAnalyticMap sY r To t x ∈ fib := fun x ↦
    resolutionAnalyticMap_pointFibreAnalyticMap sY r To t x
  have hrange : Set.range (pointFibreAnalyticMap sY r To t) = fib := by
    refine Set.Subset.antisymm (Set.range_subset_iff.2 hmem) fun z hz ↦ ?_
    obtain ⟨y, hy⟩ := exists_pointFibreInclusion_eq To t (V := ⊤) trivial ⟨z, trivial⟩ hz
    exact ⟨y, congrArg Subtype.val hy⟩
  let e : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)) ≃ₜ fib :=
    hce.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let ψ : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)) ⟶ TopCat.of fib :=
    TopCat.ofHom ⟨e, e.continuous⟩
  let ψ' : TopCat.of fib ⟶ analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hψ : ψ' ≫ ψ = 𝟙 _ := TopCat.ext fun x ↦ e.apply_symm_apply x
  let incl : TopCat.of fib ⟶ preimageSpace (resolutionAnalyticMap sY r) V :=
    TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono (Set.singleton_subset_iff.2 hV)),
      continuous_inclusion _⟩
  have hfac : ψ ≫ incl = pointFibreInclusion sY r To t hV := TopCat.ext fun x ↦ rfl
  have hinj : Function.Injective (rationalCohomologyMap ψ 2).hom := by
    intro a b hab
    have key : ∀ c, (rationalCohomologyMap ψ' 2).hom ((rationalCohomologyMap ψ 2).hom c) = c := by
      intro c
      rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hψ, rationalCohomologyMap_id]
      rfl
    rw [← key a, ← key b, hab]
  apply hinj
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hfac, h, map_zero]

/-- **Uniqueness of canonical germs.** Two canonical classes of `E` on closed pieces meeting
`F_t` in the same component `S` have the same germ in `𝒲_t`: the pieces agree over a smaller
tube by the tube lemma, and canonical classes restrict to canonical classes. -/
private theorem classGerm_canonicalClass_eq (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (S : Set (pointFibre sY r To t))
    (E : Mori.PrimeDivisor Z)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))]
    {V V' : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (hV' : curveOpenInclusion sY To t ∈ V')
    (G : Set (preimageSpace (resolutionAnalyticMap sY r) V))
    (G' : Set (preimageSpace (resolutionAnalyticMap sY r) V'))
    (hG : IsClosed G) (hK : IsClosed (tubeSupport V E \ G))
    (hG' : IsClosed G') (hK' : IsClosed (tubeSupport V' E \ G'))
    (hGE : G ⊆ tubeSupport V E) (hGE' : G' ⊆ tubeSupport V' E)
    (hfib : ∀ y, pointFibreInclusion sY r To t hV y ∈ G ↔
      y.hom.base (IsLocalRing.closedPoint ℂ) ∈ S)
    (hfib' : ∀ y, pointFibreInclusion sY r To t hV' y ∈ G' ↔
      y.hom.base (IsLocalRing.closedPoint ℂ) ∈ S) :
    classGerm sY r To t hV (canonicalClass hM E V G hG hK) =
      classGerm sY r To t hV' (canonicalClass hM E V' G' hG' hK') := by
  let ι₁ := preimageInclusion (resolutionAnalyticMap sY r) (inf_le_left : V ⊓ V' ≤ V)
  let ι₂ := preimageInclusion (resolutionAnalyticMap sY r) (inf_le_right : V ⊓ V' ≤ V')
  let G₁ := ι₁ ⁻¹' G
  let G₂ := ι₂ ⁻¹' G'
  have hG₁ : IsClosed G₁ := hG.preimage ι₁.hom.continuous
  have hG₂ : IsClosed G₂ := hG'.preimage ι₂.hom.continuous
  have hK₁ : IsClosed (tubeSupport (V ⊓ V') E \ G₁) := hK.preimage ι₁.hom.continuous
  have hK₂ : IsClosed (tubeSupport (V ⊓ V') E \ G₂) := hK'.preimage ι₂.hom.continuous
  have htV : curveOpenInclusion sY To t ∈ V ⊓ V' := ⟨hV, hV'⟩
  let C := (G₁ ∩ (tubeSupport (V ⊓ V') E \ G₂)) ∪ (G₂ ∩ (tubeSupport (V ⊓ V') E \ G₁))
  have hC : IsClosed C := (hG₁.inter hK₂).union (hG₂.inter hK₁)
  have hCt : ∀ z ∈ C, resolutionAnalyticMap sY r z.1 ≠ curveOpenInclusion sY To t := by
    intro z hzC hz
    obtain ⟨y, rfl⟩ := exists_pointFibreInclusion_eq To t htV z hz
    have e₁ : pointFibreInclusion sY r To t htV y ∈ G₁ ↔
        y.hom.base (IsLocalRing.closedPoint ℂ) ∈ S := hfib y
    have e₂ : pointFibreInclusion sY r To t htV y ∈ G₂ ↔
        y.hom.base (IsLocalRing.closedPoint ℂ) ∈ S := hfib' y
    rcases hzC with ⟨h₁, -, h₂⟩ | ⟨h₂, -, h₁⟩
    · exact h₂ (e₂.2 (e₁.1 h₁))
    · exact h₁ (e₁.2 (e₂.1 h₂))
  obtain ⟨V'', hle, htV'', hC''⟩ := exists_le_forall_notMem hM htV C hC hCt
  have hle₁ : V'' ≤ V := hle.trans inf_le_left
  have hle₂ : V'' ≤ V' := hle.trans inf_le_right
  have hsets : preimageInclusion (resolutionAnalyticMap sY r) hle₁ ⁻¹' G =
      preimageInclusion (resolutionAnalyticMap sY r) hle₂ ⁻¹' G' := by
    ext z
    have hz := hC'' z
    let w := preimageInclusion (resolutionAnalyticMap sY r) hle z
    have hw₁ : w ∈ G₁ ↔ preimageInclusion (resolutionAnalyticMap sY r) hle₁ z ∈ G := Iff.rfl
    have hw₂ : w ∈ G₂ ↔ preimageInclusion (resolutionAnalyticMap sY r) hle₂ z ∈ G' := Iff.rfl
    have hE₁ : w ∈ G₁ → w ∈ tubeSupport (V ⊓ V') E := fun h ↦ hGE h
    have hE₂ : w ∈ G₂ → w ∈ tubeSupport (V ⊓ V') E := fun h ↦ hGE' h
    rw [Set.mem_preimage, Set.mem_preimage, ← hw₁, ← hw₂]
    constructor
    · intro h
      by_contra h'
      exact hz (Or.inl ⟨h, hE₁ h, h'⟩)
    · intro h
      by_contra h'
      exact hz (Or.inr ⟨h, hE₂ h, h'⟩)
  rw [classGerm_restrict sY r To t hle₁ htV'', classGerm_restrict sY r To t hle₂ htV'',
    canonicalClass_preimageInclusion hM E hle₁ G hG hK
      (hG.preimage (preimageInclusion (resolutionAnalyticMap sY r) hle₁).hom.continuous)
      (hK.preimage (preimageInclusion (resolutionAnalyticMap sY r) hle₁).hom.continuous),
    canonicalClass_preimageInclusion hM E hle₂ G' hG' hK'
      (hG'.preimage (preimageInclusion (resolutionAnalyticMap sY r) hle₂).hom.continuous)
      (hK'.preimage (preimageInclusion (resolutionAnalyticMap sY r) hle₂).hom.continuous)]
  exact congrArg _ (canonicalClass_congr hM E V'' hsets _ _ _ _)

/-- Two closed subsets of a scheme locally of finite type over `ℂ` with the same complex points
are equal: closed points are dense in closed subsets of a Jacobson scheme, and over `ℂ` they are
the complex points. -/
private theorem eq_of_pointsOver_eq {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B)
    (h : UnderlyingSpace.pointsOver (K := ℂ) A = UnderlyingSpace.pointsOver (K := ℂ) B) : A = B := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace (X ↘ Spec (.of ℂ))
  have key : ∀ {A B : Set X}, IsClosed A → IsClosed B →
      UnderlyingSpace.pointsOver (K := ℂ) A ⊆ UnderlyingSpace.pointsOver (K := ℂ) B → A ⊆ B := by
    intro A B hA hB h
    rw [← closure_inter_closedPoints hA]
    refine closure_minimal (fun a ⟨ha, hac⟩ ↦ ?_) hB
    obtain ⟨p, rfl⟩ : ∃ p : UnderlyingSpace ℂ X, p.toHom (IsLocalRing.closedPoint ℂ) = a :=
      ⟨(UnderlyingSpace.equivClosedPoints (K := ℂ) X).symm ⟨a, hac⟩, by
        rw [← UnderlyingSpace.equivClosedPoints_apply, Equiv.apply_symm_apply]⟩
    exact h ha
  exact (key hA hB h.subset).antisymm (key hB hA h.symm.subset)

/-- A trivialization `Φ : A × Δ ≃ₜ B` over `Δ` restricts, over each `d ∈ Δ`, to a homeomorphism
of `A` onto the fibre of `B` over `d`. -/
private noncomputable def fibreHomeomorph {A B Δ : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace Δ] (π : B → Δ) (Φ : A × Δ ≃ₜ B)
    (hΦ : ∀ p, π (Φ p) = p.2) (d : Δ) : A ≃ₜ {w : B // π w = d} where
  toFun a := ⟨Φ (a, d), hΦ _⟩
  invFun w := (Φ.symm w.1).1
  left_inv a := by simp
  right_inv w := by
    apply Subtype.ext
    have h : (Φ.symm w.1).2 = d := by
      have := hΦ (Φ.symm w.1)
      rw [Homeomorph.apply_symm_apply] at this
      exact this.symm.trans w.2
    have e : ((Φ.symm w.1).1, d) = Φ.symm w.1 := Prod.ext rfl h.symm
    change Φ ((Φ.symm w.1).1, d) = w.1
    rw [e, Homeomorph.apply_symm_apply]
  continuous_toFun := (Φ.continuous.comp (Continuous.prodMk_left d)).subtype_mk _
  continuous_invFun := continuous_fst.comp (Φ.symm.continuous.comp continuous_subtype_val)

/-- Connected components inside a subspace `P` are computed in `P`: for `Q ⊆ P`, the connected
component of `Q` through `w` is the image of that of `Q ∩ P`, read in `P`. -/
private theorem connectedComponentIn_eq_image_val {X' : Type*} [TopologicalSpace X']
    {P Q : Set X'} (hQP : Q ⊆ P) (w : P) (hw : (w : X') ∈ Q) :
    connectedComponentIn Q (w : X') =
      Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' Q : Set P) w := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxP : x ∈ P := hQP (connectedComponentIn_subset _ _ hx)
    have hpre : IsPreconnected (Subtype.val ⁻¹' connectedComponentIn Q (w : X') : Set P) := by
      rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, Set.image_preimage_eq_of_subset]
      · exact isPreconnected_connectedComponentIn
      · rw [Subtype.range_coe]; exact (connectedComponentIn_subset _ _).trans hQP
    have hsub : (Subtype.val ⁻¹' connectedComponentIn Q (w : X') : Set P) ⊆
        Subtype.val ⁻¹' Q := Set.preimage_mono (connectedComponentIn_subset _ _)
    exact ⟨⟨x, hxP⟩, hpre.subset_connectedComponentIn (x := w) (mem_connectedComponentIn hw)
      hsub hx, rfl⟩
  · rw [Set.image_subset_iff]
    intro y hy
    have h1 : IsPreconnected
        (Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' Q : Set P) w) :=
      isPreconnected_connectedComponentIn.image _ continuous_subtype_val.continuousOn
    have hsub : Subtype.val '' connectedComponentIn (Subtype.val ⁻¹' Q : Set P) w ⊆ Q := by
      rw [Set.image_subset_iff]; exact connectedComponentIn_subset _ _
    exact h1.subset_connectedComponentIn ⟨w, mem_connectedComponentIn hw, rfl⟩
      hsub ⟨y, hy, rfl⟩

/-- A closed surface maximal among the irreducible subsets of `Q ⊆ R`, with `R` closed of
dimension at most two, is maximal among the irreducible subsets of `R`. -/
private theorem maximal_of_maximal_of_subset {X' : Type*} [TopologicalSpace X']
    {Q R A : Set X'} (hQR : Q ⊆ R) (hR : IsClosed R)
    (hRdim : topologicalKrullDim R ≤ ((2 : ℕ) : WithBot ℕ∞))
    (hA : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) A) (hAcl : IsClosed A)
    (hAdim : topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞)) :
    Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ R) A := by
  refine ⟨⟨hA.1.1, hA.1.2.trans hQR⟩, fun B ⟨hB, hBR⟩ hAB ↦ ?_⟩
  have hC : IsIrreducible (closure B) := hB.closure
  have hCR : closure B ⊆ R := closure_minimal hBR hR
  have hAC : A ⊆ closure B := hAB.trans subset_closure
  by_cases hne : A = closure B
  · exact hne ▸ subset_closure
  · exfalso
    have hCdim : topologicalKrullDim (closure B) ≤ ((2 : ℕ) : WithBot ℕ∞) :=
      (topologicalKrullDim_le_of_subset hCR).trans hRdim
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hC hAcl hAC hne
      (ne_top_of_le_ne_top (by decide) hCdim)
    rw [hAdim] at hlt
    exact absurd (hlt.trans_le hCdim) (lt_irrefl _)

/-- The fibre over `d` of `π : B → Δ`, for `B ⊆ W`, is homeomorphic to the subset `B'` of `W`
with the same points. -/
private noncomputable def fibreSubtypeHomeomorph {W Δ : Type*} [TopologicalSpace W]
    {B : Set W} (π : B → Δ) (d : Δ) (B' : Set W)
    (hB' : ∀ w : W, w ∈ B' ↔ ∃ h : w ∈ B, π ⟨w, h⟩ = d) :
    {w : B // π w = d} ≃ₜ B' :=
  ((Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).toHomeomorph).trans
    (Homeomorph.setCongr (by
      ext w
      rw [hB']
      constructor
      · rintro ⟨⟨u, hu⟩, rfl⟩; exact ⟨u.2, hu⟩
      · rintro ⟨h, hd⟩; exact ⟨⟨⟨w, h⟩, hd⟩, rfl⟩))

/-- Over a closed subset `P`, the points where a continuous map on `P` lands in a closed set form
a closed set. -/
private theorem isClosed_setOf_exists_mem {W B : Type*} [TopologicalSpace W] [TopologicalSpace B]
    {P : Set W} (hP : IsClosed P) (ψ : P → B) (hψ : Continuous ψ) {C : Set B}
    (hC : IsClosed C) : IsClosed {z | ∃ hz : z ∈ P, ψ ⟨z, hz⟩ ∈ C} := by
  have h : {z | ∃ hz : z ∈ P, ψ ⟨z, hz⟩ ∈ C} = Subtype.val '' (ψ ⁻¹' C) := by
    ext z
    exact ⟨fun ⟨hz, hzC⟩ ↦ ⟨⟨z, hz⟩, hzC, rfl⟩, fun ⟨w, hw, hwz⟩ ↦ hwz ▸ ⟨w.2, hw⟩⟩
  rw [h]
  exact hP.isClosedEmbedding_subtypeVal.isClosedMap _ (hC.preimage hψ)

/-- The preimage of an irreducible set inside the range of an inducing map is irreducible. -/
private theorem isIrreducible_preimage_of_isInducing {X' Y' : Type*} [TopologicalSpace X']
    [TopologicalSpace Y'] {e : X' → Y'} (he : Topology.IsInducing e) {A : Set Y'}
    (hA : IsIrreducible A) (hAr : A ⊆ Set.range e) : IsIrreducible (e ⁻¹' A) := by
  refine ⟨?_, fun u v hu hv ⟨x, hxA, hxu⟩ ⟨y, hyA, hyv⟩ ↦ ?_⟩
  · obtain ⟨a, ha⟩ := hA.nonempty
    obtain ⟨x, rfl⟩ := hAr ha
    exact ⟨x, ha⟩
  · obtain ⟨u', hu', rfl⟩ := he.isOpen_iff.1 hu
    obtain ⟨v', hv', rfl⟩ := he.isOpen_iff.1 hv
    obtain ⟨a, haA, hau, hav⟩ := hA.2 u' v' hu' hv' ⟨_, hxA, hxu⟩ ⟨_, hyA, hyv⟩
    obtain ⟨z, rfl⟩ := hAr haA
    exact ⟨z, haA, hau, hav⟩

/-- An embedding matches the maximal irreducible subsets of `Q` with those of its image. -/
private theorem maximal_image_iff_of_isEmbedding {X' Y' : Type*} [TopologicalSpace X']
    [TopologicalSpace Y'] {e : X' → Y'} (he : Topology.IsEmbedding e) {Q A : Set X'} :
    Maximal (fun B ↦ IsIrreducible B ∧ B ⊆ e '' Q) (e '' A) ↔
      Maximal (fun B ↦ IsIrreducible B ∧ B ⊆ Q) A := by
  have hpre : ∀ B : Set X', e ⁻¹' (e '' B) = B := fun B ↦ Set.preimage_image_eq B he.injective
  constructor
  · rintro ⟨⟨hA, hAQ⟩, hmax⟩
    have hA' : IsIrreducible A := by
      simpa [hpre] using isIrreducible_preimage_of_isInducing he.isInducing hA
        (Set.image_subset_range _ _)
    refine ⟨⟨hA', fun x hx ↦ ?_⟩, fun B ⟨hB, hBQ⟩ hAB ↦ ?_⟩
    · obtain ⟨y, hy, hyx⟩ := hAQ ⟨x, hx, rfl⟩
      exact he.injective hyx ▸ hy
    · have := hmax ⟨hB.image e he.continuous.continuousOn, Set.image_mono hBQ⟩
        (Set.image_mono hAB)
      rw [← hpre B, ← hpre A]
      exact Set.preimage_mono this
  · rintro ⟨⟨hA, hAQ⟩, hmax⟩
    refine ⟨⟨hA.image e he.continuous.continuousOn, Set.image_mono hAQ⟩,
      fun B ⟨hB, hBQ⟩ hAB ↦ ?_⟩
    have hBr : B ⊆ Set.range e := hBQ.trans (Set.image_subset_range _ _)
    have h1 := hmax ⟨isIrreducible_preimage_of_isInducing he.isInducing hB hBr,
      fun x hx ↦ by
        obtain ⟨y, hy, hyx⟩ := hBQ hx
        exact he.injective hyx ▸ hy⟩ (by rw [← hpre A]; exact Set.preimage_mono hAB)
    intro b hb
    obtain ⟨x, rfl⟩ := hBr hb
    exact ⟨x, h1 hb, rfl⟩

/-- Under an inducing map, an irreducible component of the source goes to a maximal irreducible
subset of the range. -/
private theorem maximal_image_of_mem_irreducibleComponents {X' Y' : Type*} [TopologicalSpace X']
    [TopologicalSpace Y'] {e : X' → Y'} (he : Topology.IsInducing e) {S : Set X'}
    (hS : S ∈ irreducibleComponents X') :
    Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Set.range e) (e '' S) := by
  refine ⟨⟨hS.1.image e he.continuous.continuousOn, Set.image_subset_range _ _⟩,
    fun A ⟨hA, hAr⟩ hSA ↦ ?_⟩
  have h := hS.2 (isIrreducible_preimage_of_isInducing he hA hAr)
    (fun x hx ↦ hSA ⟨x, hx, rfl⟩)
  intro a ha
  obtain ⟨x, rfl⟩ := hAr ha
  exact ⟨x, h ha, rfl⟩

/-- The fibre `F_t` over a `ℂ`-point `t` of `T°` is a closed subspace of `Z`: its projection is a
closed embedding onto the preimage of the point underlying `t`. -/
private theorem isClosedEmbedding_pointFibreFst {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    Topology.IsClosedEmbedding (pointFibreFst sY r To t) ∧
      Set.range (pointFibreFst sY r To t) =
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))} := by
  have hb : (t.hom ≫ To.ι ≫ curveι T) ≫ sY = 𝟙 _ := by
    simpa [Category.assoc] using t.hom_comp_structure
  have : IsClosedImmersion (t.hom ≫ To.ι ≫ curveι T) :=
    isClosedImmersion_of_comp_eq_id sY _ hb
  refine ⟨(pullback.fst r (t.hom ≫ To.ι ≫ curveι T)).isClosedEmbedding, ?_⟩
  change Set.range (pullback.fst r (t.hom ≫ To.ι ≫ curveι T)) = _
  rw [Scheme.Pullback.range_fst]
  congr 1
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    rfl
  · rintro rfl
    exact ⟨default, rfl⟩

/-- A component `S` of the fibre `F_t` lying in an exceptional component `E` is a component of
`E_t`: its image in `Z` is a maximal irreducible subset of `E ∩ r⁻¹(y)`. -/
private theorem maximal_image_pointFibreFst {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z)
    (hS : (S : Set (pointFibre sY r To t)) ⊆
      (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z)) :
    Maximal (fun A : Set Z ↦ IsIrreducible A ∧ A ⊆ (E.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))})
      ((pointFibreFst sY r To t) '' S) := by
  obtain ⟨hemb, hrange⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
  have hmax := maximal_image_of_mem_irreducibleComponents hemb.isInducing S.2
  rw [hrange] at hmax
  refine ⟨⟨hmax.1.1, fun z ⟨x, hx, hxz⟩ ↦ ⟨hxz ▸ hS hx, hmax.1.2 ⟨x, hx, hxz⟩⟩⟩,
    fun A ⟨hA, hAE⟩ hSA ↦ hmax.2 ⟨hA, hAE.trans Set.inter_subset_right⟩ hSA⟩

/-- Components of a fibre `F_t` with the same complex points are equal. -/
private theorem eq_of_forall_mem_iff_irreducibleComponents
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {S S' : irreducibleComponents (pointFibre sY r To t)}
    (h : ∀ y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
      y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t)) ↔
        y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S' : Set (pointFibre sY r To t))) :
    S = S' := by
  haveI : LocallyOfFiniteType r := by
    have : LocallyOfFiniteType (r ≫ sY) := hM.isResolution.2.1.toLocallyOfFiniteType
    exact LocallyOfFiniteType.of_comp (g := sY) this
  haveI : LocallyOfFiniteType (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (pullback.snd r (t.hom ≫ To.ι ≫ curveι T))
    infer_instance
  refine Subtype.ext (eq_of_pointsOver_eq (isClosed_of_mem_irreducibleComponents _ S.2)
    (isClosed_of_mem_irreducibleComponents _ S'.2) (Set.ext fun p ↦ ?_))
  exact h ((ComplexPoints.homeomorphUnderlyingSpace (X := pointFibre sY r To t)).symm p)

/-- An integral, separated, quasi-compact `ℂ`-scheme smooth of relative dimension `n` is a
smooth variety, hence a complex scheme. -/
private theorem isComplexScheme_of_smoothOfRelativeDimension {M : Scheme.{0}}
    [M.Over (Spec (.of ℂ))] [IsIntegral M] [IsSeparated (M ↘ Spec (.of ℂ))]
    [QuasiCompact (M ↘ Spec (.of ℂ))] (n : ℕ) [SmoothOfRelativeDimension n (M ↘ Spec (.of ℂ))] :
    IsComplexScheme M ∧ IsIntegral M := by
  haveI : Smooth (M ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth n _
  haveI : LocallyOfFiniteType (M ↘ Spec (.of ℂ)) := inferInstance
  haveI : IsSmoothVariety ℂ (M ↘ Spec (.of ℂ)) := { }
  exact ⟨IsComplexScheme.of_isSmoothVariety M, inferInstance⟩

/-- The resolution `Z` of a curve-and-point exceptional model is smooth of relative dimension
four over `ℂ`. -/
private theorem smoothOfRelativeDimension_four (hM : IsCurvePointExceptionalModel sY r F D) :
    SmoothOfRelativeDimension 4 (Z ↘ Spec (.of ℂ)) := by
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  haveI : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI : Smooth (r ≫ sY) := (MMP.Mori.isSmoothScheme_iff _).1 hM.isResolution.2.2.1
  have hdim : topologicalKrullDim Z = (4 : ℕ) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
      hM.isResolution.2.2.2.2).symm.trans hM.topologicalKrullDim_eq
  rw [← hM.comp_eq]
  exact MMP.Intersection.smoothOfRelativeDimension_of_isVariety (r ≫ sY) 4 hdim

/-- The resolution `Z` of a curve-and-point exceptional model is a complex scheme: it is a
non-singular variety, closed in itself. -/
private theorem isComplexScheme_of_isCurvePointExceptionalModel
    (hM : IsCurvePointExceptionalModel sY r F D) : IsComplexScheme Z := by
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  haveI : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI := smoothOfRelativeDimension_four hM
  haveI : IsSeparated (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact hZv.toIsSeparated
  haveI : QuasiCompact (Z ↘ Spec (.of ℂ)) := by
    rw [← hM.comp_eq]; exact inferInstance
  haveI : IsIntegral Z := hZv.toIsIntegral
  exact (isComplexScheme_of_smoothOfRelativeDimension 4).1

open UnderlyingSpace in
/-- **The product germ of the exceptional family**, in this file's setting: over a general open
`U₀` of `T`, near every `b ∈ (U₀ ∩ T)(ℂ)` the exceptional family is a product `F_b × Δ`, over
`Δ`, the identity over `b`, preserving every component of `F`. -/
private theorem exists_open_homeomorph_prod (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∃ U₀ : Y.Opens, ((U₀ : Set Y) ∩ T).Nonempty ∧
      ∀ b ∈ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T), ∀ N ∈ nhds b,
        ∃ Δ : Set (UnderlyingSpace ℂ Y), Δ ⊆ N ∧
          (∃ O, IsOpen O ∧ Δ = O ∩ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T)) ∧
          IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ,
          ∃ Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
              ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ),
            (∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) ∧
            (∀ z, (Φ (z, ⟨b, hbΔ⟩) : UnderlyingSpace ℂ Z) = z) ∧
            ∀ E ∈ F.support, ∀ p, (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
              (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI := isComplexScheme_of_isCurvePointExceptionalModel hM
  exact exists_homeomorph_prod_exceptionalFibre hM T hT hdim

/-- **Disjoint fibre components, in `Z`.** Over a general open `U` of `T`, for every component
`E` of `F` and every `y ∈ U ∩ T`, the maximal irreducible subsets of `E ∩ r⁻¹(y)` are pairwise
disjoint surfaces. -/
private theorem exists_open_disjoint_maximal_fibre (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hdim : topologicalKrullDim (T : Set Y) = 1) (E : F.support) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧ ∀ y ∈ (U : Set Y) ∩ T,
      (∀ A B : Set Z,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩ r ⁻¹' {y}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩ r ⁻¹' {y}) B →
        A ≠ B → Disjoint A B) ∧
      ∀ A : Set Z,
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩ r ⁻¹' {y}) A →
        topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞) := by
  haveI := isComplexScheme_of_isCurvePointExceptionalModel hM
  obtain ⟨U, hU, H⟩ := exists_disjoint_maximal_fibre_of_mem hM T hdim E
  refine ⟨U, hU, fun y hy ↦ ?_⟩
  obtain ⟨hdisj, hdim2⟩ := H y hy
  set ι := E.1.idealSheaf.subschemeι
  have hemb : Topology.IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
  have hrange : Set.range ι = (E.1.support : Set Z) := E.1.idealSheaf.range_subschemeι
  have himg : (E.1.support : Set Z) ∩ r ⁻¹' {y} = ι '' ((ι ≫ r).base ⁻¹' {y}) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq_inter_range,
      hrange, Set.inter_comm]
  have hpull : ∀ A : Set Z, Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ (E.1.support : Set Z) ∩ r ⁻¹' {y}) A →
      A = ι '' (ι ⁻¹' A) ∧ Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (ι ≫ r).base ⁻¹' {y})
        (ι ⁻¹' A) := by
    intro A hA
    have hAr : A ⊆ Set.range ι := hrange ▸ (hA.1.2.trans Set.inter_subset_left)
    have hA' : A = ι '' (ι ⁻¹' A) := (Set.image_preimage_eq_of_subset hAr).symm
    refine ⟨hA', (maximal_image_iff_of_isEmbedding hemb).1 ?_⟩
    rw [← hA', ← himg]
    exact hA
  refine ⟨fun A B hA hB hAB ↦ ?_, fun A hA ↦ ?_⟩
  · obtain ⟨hA', hAm⟩ := hpull A hA
    obtain ⟨hB', hBm⟩ := hpull B hB
    rw [hA', hB']
    exact (Set.disjoint_image_iff hemb.injective).2
      (hdisj _ _ hAm hBm fun h ↦ hAB (by rw [hA', hB', h]))
  · obtain ⟨hA', hAm⟩ := hpull A hA
    rw [← hdim2 _ hAm]
    conv_lhs => rw [hA']
    exact ((hemb.comp Topology.IsEmbedding.subtypeVal).toHomeomorph.trans
      (Homeomorph.setCongr (by rw [Set.range_comp, Subtype.range_coe]))).isHomeomorph
        |>.topologicalKrullDim_eq.symm

open UnderlyingSpace in
/-- **Components and connected components.** If the maximal irreducible subsets of a closed set
`Q` of a Noetherian complex scheme are pairwise disjoint, the complex points of each of them form
a connected component of the complex points of `Q`. -/
private theorem connectedComponentIn_pointsOver_eq {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] [NoetherianSpace X] {Q : Set X} (hQ : IsClosed Q)
    (hdisj : ∀ A B : Set X, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) B → A ≠ B → Disjoint A B)
    {A : Set X} (hA : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) A)
    {p : UnderlyingSpace ℂ X} (hp : p ∈ pointsOver (K := ℂ) A) :
    connectedComponentIn (pointsOver (K := ℂ) Q) p = pointsOver (K := ℂ) A := by
  classical
  set M := {A : Set X | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) A}
  have hMfin : M.Finite := finite_setOf_maximal Q
  have hcl : ∀ B ∈ M, IsClosed B := fun B hB ↦ isClosed_of_maximal hQ hB
  refine connectedComponentIn_eq_of_pairwiseDisjoint (Ps := pointsOver (K := ℂ) '' M)
    (hMfin.image _) ?_ ?_ ?_ ?_ ⟨A, hA, rfl⟩ hp
  · rintro _ ⟨B, hB, rfl⟩
    exact isClosed_pointsOver (hcl B hB)
  · rintro _ ⟨B, hB, rfl⟩
    exact (isConnected_pointsOver_of_isIrreducible (hcl B hB) hB.1.1).isPreconnected
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨C, hC, rfl⟩ hne
    have hBC : B ≠ C := fun h ↦ hne (by rw [h])
    exact Set.disjoint_left.2 fun q hqB hqC ↦
      Set.disjoint_left.1 (hdisj B C hB hC hBC) hqB hqC
  · ext q
    refine ⟨fun ⟨_, ⟨B, hB, rfl⟩, hqB⟩ ↦ hB.1.2 hqB, fun hq ↦ ?_⟩
    obtain ⟨B, hqB, hB⟩ := exists_subset_maximal_of_isIrreducible isIrreducible_singleton
      (Set.singleton_subset_iff.2 (show q.toHom (IsLocalRing.closedPoint ℂ) ∈ Q from hq))
    exact ⟨_, ⟨B, hB, rfl⟩, hqB rfl⟩

open UnderlyingSpace in
/-- **Transport of components.** Let `h : P ≃ₜ P'` be a homeomorphism of sets of complex points
carrying the complex points of a closed `Q` onto those of a closed `Q'`, both with pairwise
disjoint components. Then `h` carries the complex points of every component of `Q` onto those
of a component of `Q'`. -/
private theorem exists_maximal_forall_mem_iff {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] [NoetherianSpace X] {P P' : Set (UnderlyingSpace ℂ X)} (h : P ≃ₜ P')
    {Q Q' : Set X} (hQ : IsClosed Q) (hQ' : IsClosed Q')
    (hQP : pointsOver (K := ℂ) Q ⊆ P) (hQP' : pointsOver (K := ℂ) Q' ⊆ P')
    (hh : ∀ w : P, ((h w : P') : UnderlyingSpace ℂ X) ∈ pointsOver (K := ℂ) Q' ↔
      (w : UnderlyingSpace ℂ X) ∈ pointsOver (K := ℂ) Q)
    (hdisj : ∀ A B : Set X, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) B → A ≠ B → Disjoint A B)
    (hdisj' : ∀ A B : Set X, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q') A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q') B → A ≠ B → Disjoint A B)
    {A : Set X} (hA : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) A) :
    ∃ A', Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q') A' ∧ ∀ w : P,
      ((h w : P') : UnderlyingSpace ℂ X) ∈ pointsOver (K := ℂ) A' ↔
        (w : UnderlyingSpace ℂ X) ∈ pointsOver (K := ℂ) A := by
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := inferInstance
  have hAcl : IsClosed A := isClosed_of_maximal hQ hA
  -- a complex point of `A`
  obtain ⟨x, hxA, hxcl⟩ := hAcl.exists_closed_singleton hA.1.1.nonempty
  obtain ⟨p, hp⟩ : ∃ p : UnderlyingSpace ℂ X, p.toHom (IsLocalRing.closedPoint ℂ) = x :=
    ⟨(equivClosedPoints (K := ℂ) X).symm ⟨x, hxcl⟩, by
      rw [← equivClosedPoints_apply, Equiv.apply_symm_apply]⟩
  have hpA : p ∈ pointsOver (K := ℂ) A := by rw [mem_pointsOver, hp]; exact hxA
  have hpQ : p ∈ pointsOver (K := ℂ) Q := hA.1.2 hpA
  set w : P := ⟨p, hQP hpQ⟩
  have hwQ' : ((h w : P') : UnderlyingSpace ℂ X) ∈ pointsOver (K := ℂ) Q' := (hh w).2 hpQ
  -- the component of `Q'` through `h w`
  obtain ⟨A', hqA', hA'⟩ := exists_subset_maximal_of_isIrreducible isIrreducible_singleton
    (Set.singleton_subset_iff.2 (show ((h w : P') : UnderlyingSpace ℂ X).toHom
      (IsLocalRing.closedPoint ℂ) ∈ Q' from hwQ'))
  have hqA'' : ((h w : P') : UnderlyingSpace ℂ X) ∈ pointsOver (K := ℂ) A' := hqA' rfl
  refine ⟨A', hA', fun w' ↦ ?_⟩
  have hS : h '' (Subtype.val ⁻¹' pointsOver (K := ℂ) Q : Set P) =
      (Subtype.val ⁻¹' pointsOver (K := ℂ) Q' : Set P') := by
    ext v
    refine ⟨fun ⟨u, hu, huv⟩ ↦ huv ▸ (hh u).2 hu, fun hv ↦ ⟨h.symm v, (hh _).1 ?_, by simp⟩⟩
    rw [h.apply_symm_apply]
    exact hv
  have e1 := connectedComponentIn_pointsOver_eq hQ hdisj hA hpA
  rw [connectedComponentIn_eq_image_val hQP w hpQ] at e1
  have e2 := connectedComponentIn_pointsOver_eq hQ' hdisj' hA' hqA''
  rw [connectedComponentIn_eq_image_val hQP' (h w) hwQ', ← hS,
    ← h.image_connectedComponentIn
      (show w ∈ (Subtype.val ⁻¹' pointsOver (K := ℂ) Q : Set P) from hpQ)] at e2
  rw [← e1, ← e2]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, huv⟩
    have : u = w' := h.injective (Subtype.ext huv)
    exact ⟨w', this ▸ hu, rfl⟩
  · rintro ⟨u, hu, huv⟩
    have : u = w' := Subtype.ext huv
    exact ⟨h w', ⟨w', this ▸ hu, rfl⟩, rfl⟩

open UnderlyingSpace in
/-- **The general open of `T`.** One open `U` of `Y` meeting `T` over which: the exceptional
family has product germs at every `b ∈ (U ∩ T)(ℂ)`; for every component `E` of `F` the
components of the fibres `E_y`, `y ∈ U ∩ T`, are pairwise disjoint surfaces; and the singular
locus of `Y` meets `U` in `T`. -/
private theorem exists_open_general (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∃ U₀ U : Y.Opens, U ≤ U₀ ∧ ((U : Set Y) ∩ T).Nonempty ∧
      (∀ b ∈ pointsOver (K := ℂ) ((U : Set Y) ∩ T), ∀ N ∈ nhds b,
        ∃ Δ : Set (UnderlyingSpace ℂ Y), Δ ⊆ N ∧
          (∃ O, IsOpen O ∧ Δ = O ∩ pointsOver (K := ℂ) ((U₀ : Set Y) ∩ T)) ∧
          IsPreconnected Δ ∧ ∃ hbΔ : b ∈ Δ,
          ∃ Φ : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' {b}) × Δ ≃ₜ
              ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹' Δ),
            (∀ p, mapFun r (Φ p : UnderlyingSpace ℂ Z) = p.2) ∧
            (∀ z, (Φ (z, ⟨b, hbΔ⟩) : UnderlyingSpace ℂ Z) = z) ∧
            ∀ E ∈ F.support, ∀ p, (Φ p : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
              (p.1 : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z)) ∧
      (∀ y ∈ (U : Set Y) ∩ T, ∀ E : F.support,
        (∀ A B : Set Z,
          Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩ r ⁻¹' {y}) A →
          Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩ r ⁻¹' {y}) B →
          A ≠ B → Disjoint A B) ∧
        ∀ A : Set Z,
          Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩ r ⁻¹' {y}) A →
          topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞)) ∧
      (U : Set Y) ∩ (singularLocus sY : Set Y) = (U : Set Y) ∩ T := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI := isComplexScheme_of_isCurvePointExceptionalModel hM
  obtain ⟨U₀, hU₀, HΦ⟩ := exists_open_homeomorph_prod hM hT hdim
  obtain ⟨U₁, hU₁, HE⟩ := exists_forall_of_finite T _
    (fun E : F.support ↦ exists_open_disjoint_maximal_fibre hM hdim E)
  obtain ⟨U₂, hU₂, HS⟩ := exists_open_singularLocus_inter_eq hM T hT hdim
  have h₀₁ := inter_inter_nonempty_of_irreducibleCloseds T hU₀ hU₁
  refine ⟨U₀, U₀ ⊓ U₁ ⊓ U₂, inf_le_left.trans inf_le_left,
    inter_inter_nonempty_of_irreducibleCloseds T h₀₁ hU₂, fun b hb ↦ HΦ b ⟨hb.1.1.1, hb.2⟩,
    fun y hy E ↦ HE y ⟨hy.1.1.2, hy.2⟩ E, ?_⟩
  ext y
  constructor
  · rintro ⟨hyU, hyS⟩
    exact ⟨hyU, ((Set.ext_iff.1 HS y).1 ⟨hyU.2, hyS⟩).2⟩
  · rintro ⟨hyU, hyT⟩
    exact ⟨hyU, ((Set.ext_iff.1 HS y).2 ⟨hyU.2, hyT⟩).2⟩

/-- A prime divisor is determined by its support. -/
private theorem primeDivisor_eq_of_support_eq {X : Scheme.{0}} {P Q : Mori.PrimeDivisor X}
    (h : (P.support : Set X) = Q.support) : P = Q := by
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  exact (inseparable_iff_closure_eq.2 h).eq

/-- The prime divisors of the resolution `Z` of a curve-and-point exceptional model are
threefolds. -/
private theorem topologicalKrullDim_primeDivisor_support
    (hM : IsCurvePointExceptionalModel sY r F D) (E : Mori.PrimeDivisor Z) :
    topologicalKrullDim (E.support : Set Z) = ((3 : ℕ) : WithBot ℕ∞) := by
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  haveI : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : LocallyOfFiniteType (r ≫ sY) := hZv.toLocallyOfFiniteType
  have hdim : topologicalKrullDim Z = (4 : ℕ) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY)
      hM.isResolution.2.2.2.2).symm.trans hM.topologicalKrullDim_eq
  exact (MMP.Spreading.topologicalKrullDim_support (r ≫ sY) hdim E).2

private theorem isIrreducible_primeDivisor_support {X : Scheme.{0}} (E : Mori.PrimeDivisor X) :
    IsIrreducible (E.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact isIrreducible_singleton.closure

/-- A closed subset of the intersection of two distinct prime divisors of `Z` has dimension at
most two. -/
private theorem topologicalKrullDim_le_two_of_subset_inter
    (hM : IsCurvePointExceptionalModel sY r F D) {E E' : Mori.PrimeDivisor Z} (hne : E ≠ E')
    {C : Set Z} (hC : IsClosed C) (hCE : C ⊆ (E.support : Set Z) ∩ E'.support) :
    topologicalKrullDim C ≤ ((2 : ℕ) : WithBot ℕ∞) := by
  have h3 := topologicalKrullDim_primeDivisor_support hM E
  have h3' := topologicalKrullDim_primeDivisor_support hM E'
  have hCne : C ≠ E.support := by
    rintro rfl
    have hsub : (E.support : Set Z) ⊆ E'.support := hCE.trans Set.inter_subset_right
    have hne' : (E.support : Set Z) ≠ E'.support := fun h ↦ hne (primeDivisor_eq_of_support_eq h)
    have := MMP.topologicalKrullDim_lt_of_subset_of_ne
      (isIrreducible_primeDivisor_support E') hC hsub hne' (by rw [h3']; decide)
    rw [h3, h3'] at this
    exact lt_irrefl _ this
  have := MMP.topologicalKrullDim_lt_of_subset_of_ne
    (isIrreducible_primeDivisor_support E) hC (hCE.trans Set.inter_subset_left) hCne
    (by rw [h3]; decide)
  rw [h3] at this
  exact le_of_lt_natCast_succ this

/-- **The component of a smooth scheme through a connected set.** In a quasi-compact scheme `M₀`
smooth over `ℂ`, a nonempty preconnected set `A` lies in an open subscheme which is integral: the
irreducible component through a point of `A`, which is open and closed since `M₀` is normal. -/
private theorem exists_opens_isIntegral_of_smooth {M₀ : Scheme.{0}} (s₀ : M₀ ⟶ Spec (.of ℂ))
    [Smooth s₀] [CompactSpace M₀] {A : Set M₀} (hA : _root_.IsPreconnected A) (hAne : A.Nonempty) :
    ∃ M : M₀.Opens, A ⊆ (M : Set M₀) ∧ IsClosed (M : Set M₀) ∧ IsIntegral M.toScheme := by
  classical
  haveI : IsLocallyNoetherian M₀ := LocallyOfFiniteType.isLocallyNoetherian s₀
  haveI : IsNormal M₀ := isNormal_of_smooth_over_field s₀
  haveI : IsNoetherian M₀ := {}
  obtain ⟨a, haA⟩ := hAne
  let C : irreducibleComponents M₀ :=
    ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a⟩
  have : Finite (irreducibleComponents M₀) :=
    (NoetherianSpace.finite_irreducibleComponents (α := M₀)).to_subtype
  have hcl : IsClosed (⋃ D ∈ {D : irreducibleComponents M₀ | D ≠ C}, (D.1 : Set M₀)) :=
    (Set.toFinite {D : irreducibleComponents M₀ | D ≠ C}).isClosed_biUnion fun D _ ↦
      isClosed_of_mem_irreducibleComponents _ D.2
  have hCeq : (C.1 : Set M₀) = (⋃ D ∈ {D : irreducibleComponents M₀ | D ≠ C}, (D.1 : Set M₀))ᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, not_exists,
      not_and]
    refine ⟨fun hx D hD hxD ↦ hD (MMP.Mori.eq_of_mem_irreducibleComponents hxD hx), fun h ↦ ?_⟩
    by_contra hx
    exact h ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
      (fun hD ↦ hx (hD ▸ mem_irreducibleComponent)) mem_irreducibleComponent
  have hCo : IsOpen (C.1 : Set M₀) := hCeq ▸ hcl.isOpen_compl
  have hCc : IsClopen (C.1 : Set M₀) := ⟨isClosed_of_mem_irreducibleComponents _ C.2, hCo⟩
  let M : M₀.Opens := ⟨C.1, hCo⟩
  have hAM : A ⊆ (M : Set M₀) := hA.subset_isClopen hCc ⟨a, haA, mem_irreducibleComponent⟩
  refine ⟨M, hAM, hCc.1, ?_⟩
  haveI : IrreducibleSpace M.toScheme := by
    have h : IsIrreducible (C.1 : Set M₀) := C.2.1
    exact isIrreducible_iff_irreducibleSpace.1 h
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The scheme fibre `F_t` of the resolution is connected (Zariski's connectedness theorem). -/
private theorem connectedSpace_pointFibre (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) : ConnectedSpace (pointFibre sY r To t) := by
  haveI hZv : MMP.Mori.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
  have hc := MMP.Fourfold.SNCWeight.Subtraction.isConnected_fibre_of_isBirational r
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hM.isResolution.2.2.2.2)
    ((t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)))
  obtain ⟨hemb, hrange⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
  have e := hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  haveI : ConnectedSpace (r.base ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) :=
    isConnected_iff_connectedSpace.1 hc
  exact e.symm.surjective.connectedSpace e.symm.continuous

open UnderlyingSpace in
/-- **The fibre of an algebraic chart through `F_t`.** For an algebraic exceptional chart
`φ : X ⟶ B` whose open `X` contains the point under `t`, the fibre `M₀` of `ρ ≫ φ : W ⟶ B` over
the image `b₀` of that point is smooth over `ℂ`, closed in the smooth open `W ⊆ Z`, and contains
the scheme fibre `F_t`. -/
private theorem exists_chartFibre (hM : IsCurvePointExceptionalModel sY r F D) [IsComplexScheme Z]
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b),
      (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∈ (Ch.X : Set Y) →
      ∃ (M₀ : Scheme.{0}) (s₀ : M₀ ⟶ Spec (.of ℂ)) (i₀ : M₀ ⟶ Ch.W.toScheme)
        (j₀ : pointFibre sY r To t ⟶ M₀) (b₀ : Spec (.of ℂ) ⟶ Ch.B),
        Smooth (Ch.ρ ≫ Ch.φ) ∧ Smooth s₀ ∧ IsClosedImmersion i₀ ∧ i₀ ≫ Ch.W.ι ≫ r ≫ sY = s₀ ∧
        j₀ ≫ i₀ ≫ Ch.W.ι = pointFibreFst sY r To t ∧ IsPullback i₀ s₀ (Ch.ρ ≫ Ch.φ) b₀ ∧
        b₀ ≫ Ch.sB = 𝟙 _ := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch hb
  have hr : Set.range (t.hom ≫ To.ι ≫ curveι T).base ⊆ Set.range Ch.X.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim p (IsLocalRing.closedPoint ℂ)]
    exact hb
  let t' := IsOpenImmersion.lift Ch.X.ι (t.hom ≫ To.ι ≫ curveι T) hr
  have ht' : t' ≫ Ch.X.ι = t.hom ≫ To.ι ≫ curveι T := IsOpenImmersion.lift_fac _ _ _
  let b₀ : Spec (.of ℂ) ⟶ Ch.B := t' ≫ Ch.φ
  have hb₀ : b₀ ≫ Ch.sB = 𝟙 _ := by
    change (t' ≫ Ch.φ) ≫ Ch.sB = _
    rw [Category.assoc, Ch.hφ, ← Category.assoc, ht', Category.assoc, Category.assoc]
    exact t.hom_comp_structure
  haveI := Ch.sep
  haveI : IsClosedImmersion b₀ := isClosedImmersion_of_comp_eq_id Ch.sB _ hb₀
  -- `ρ ≫ φ` is smooth: the stratum of the empty set of components
  haveI : Smooth (Ch.ρ ≫ Ch.φ) := by
    have h := Ch.smooth_strata ∅ (Finset.empty_subset _)
    have hbot : (⨆ E ∈ (∅ : Finset (Mori.PrimeDivisor Ch.W)), E.idealSheaf) = ⊥ := by simp
    haveI : IsIso (⨆ E ∈ (∅ : Finset (Mori.PrimeDivisor Ch.W)), E.idealSheaf).subschemeι :=
      (Scheme.isIso_subschemeι_iff_eq_bot _).2 hbot
    have : Ch.ρ ≫ Ch.φ = inv (⨆ E ∈ (∅ : Finset (Mori.PrimeDivisor Ch.W)), E.idealSheaf).subschemeι ≫
        ((⨆ E ∈ (∅ : Finset (Mori.PrimeDivisor Ch.W)), E.idealSheaf).subschemeι ≫ Ch.ρ ≫ Ch.φ) :=
      (IsIso.inv_hom_id_assoc _ _).symm
    rw [this]
    infer_instance
  -- the scheme fibre `F_t` lies in `W`
  have hF : Set.range (pointFibreFst sY r To t).base ⊆ Set.range Ch.W.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hrx : r.base ((pointFibreFst sY r To t).base x) =
        (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) := by
      rw [← Scheme.Hom.comp_apply, pointFibreFst_comp, Scheme.Hom.comp_apply,
        Subsingleton.elim ((pointFibreSnd sY r To t).base x) (IsLocalRing.closedPoint ℂ)]
    apply Ch.supp_subset_W
    refine ⟨show r.base _ ∈ (Ch.X : Set Y) from hrx ▸ hb, ?_⟩
    rw [hM.supp_eq_preimage_singularLocus]
    change r.base _ ∈ (singularLocus sY : Set Y)
    rw [hrx]
    apply hT
    have hrange : Set.range (curveι T).base = (T : Set Y) := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    exact hrange ▸ ⟨_, rfl⟩
  let lft := IsOpenImmersion.lift Ch.W.ι (pointFibreFst sY r To t) hF
  have hlft : lft ≫ Ch.W.ι = pointFibreFst sY r To t := IsOpenImmersion.lift_fac _ _ _
  have hcomm : lft ≫ Ch.ρ ≫ Ch.φ = pointFibreSnd sY r To t ≫ b₀ := by
    have h1 : lft ≫ Ch.ρ = pointFibreSnd sY r To t ≫ t' := by
      rw [← cancel_mono Ch.X.ι, Category.assoc, Ch.hρ, ← Category.assoc, hlft,
        pointFibreFst_comp, Category.assoc, ht']
    rw [← Category.assoc, h1, Category.assoc]
  refine ⟨pullback (Ch.ρ ≫ Ch.φ) b₀, pullback.snd _ _, pullback.fst _ _,
    pullback.lift lft (pointFibreSnd sY r To t) hcomm, b₀, inferInstance, inferInstance,
    inferInstance, ?_,
    by rw [← Category.assoc, pullback.lift_fst]; exact hlft, IsPullback.of_hasPullback _ _, hb₀⟩
  have hφ' : Ch.X.ι ≫ sY = Ch.φ ≫ Ch.sB := Ch.hφ.symm
  rw [← Category.assoc (Ch.W.ι), ← Ch.hρ, Category.assoc, hφ']
  calc pullback.fst (Ch.ρ ≫ Ch.φ) b₀ ≫ Ch.ρ ≫ Ch.φ ≫ Ch.sB
      = (pullback.fst (Ch.ρ ≫ Ch.φ) b₀ ≫ Ch.ρ ≫ Ch.φ) ≫ Ch.sB := by simp only [Category.assoc]
    _ = (pullback.snd (Ch.ρ ≫ Ch.φ) b₀ ≫ b₀) ≫ Ch.sB := by rw [pullback.condition]
    _ = pullback.snd (Ch.ρ ≫ Ch.φ) b₀ := by rw [Category.assoc, hb₀, Category.comp_id]

open UnderlyingSpace in
/-- **The slice through `F_t`.** For an algebraic exceptional chart whose open `X` contains the
point under `t`, the irreducible component through `F_t` of the fibre of `ρ ≫ φ : W ⟶ B` over the
image `b₀` of that point is an integral, quasi-compact, smooth `ℂ`-scheme `M`, closed in `W`, and
`F_t` is a closed subscheme of `M`. -/
private theorem exists_slice (hM : IsCurvePointExceptionalModel sY r F D) [IsComplexScheme Z]
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b),
      (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∈ (Ch.X : Set Y) →
      ∃ (M : Scheme.{0}) (sM : M ⟶ Spec (.of ℂ)) (iW : M ⟶ Ch.W.toScheme)
        (j : pointFibre sY r To t ⟶ M) (b₀ : Spec (.of ℂ) ⟶ Ch.B),
        Smooth sM ∧ IsIntegral M ∧ CompactSpace M ∧ IsClosedImmersion iW ∧
        iW ≫ Ch.W.ι ≫ r ≫ sY = sM ∧ j ≫ iW ≫ Ch.W.ι = pointFibreFst sY r To t ∧
        IsClosedImmersion j ∧ iW ≫ Ch.ρ ≫ Ch.φ = sM ≫ b₀ ∧ b₀ ≫ Ch.sB = 𝟙 _ ∧
        ∀ x : M, topologicalKrullDimAt M x = ((3 : ℕ) : WithBot ℕ∞) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch hb
  obtain ⟨M₀, s₀, i₀, j₀, b₀, hg₀, hs₀, hi₀, hcomp, hj₀, hpb, hb₀⟩ :=
    exists_chartFibre hM hT To t Ch hb
  haveI := hg₀
  haveI := hs₀
  haveI := hi₀
  haveI := Ch.qcW
  haveI : CompactSpace Ch.W.toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (Ch.W.ι ≫ Z ↘ Spec (.of ℂ))
  haveI : CompactSpace M₀ := i₀.isClosedEmbedding.compactSpace
  -- `F_t` is a closed subscheme of `M₀`
  haveI : IsClosedImmersion (j₀ ≫ i₀ ≫ Ch.W.ι) := by
    rw [hj₀]
    obtain ⟨hemb, -⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
    have hb' : (t.hom ≫ To.ι ≫ curveι T) ≫ sY = 𝟙 _ := by
      simpa [Category.assoc] using t.hom_comp_structure
    haveI : IsClosedImmersion (t.hom ≫ To.ι ≫ curveι T) :=
      isClosedImmersion_of_comp_eq_id sY _ hb'
    change IsClosedImmersion (pullback.fst r (t.hom ≫ To.ι ≫ curveι T))
    infer_instance
  haveI : IsClosedImmersion j₀ := IsClosedImmersion.of_comp j₀ (i₀ ≫ Ch.W.ι)
  haveI := connectedSpace_pointFibre hM To t
  haveI : Nonempty (pointFibre sY r To t) := ConnectedSpace.toNonempty
  obtain ⟨M, hAM, hMcl, hMint⟩ := exists_opens_isIntegral_of_smooth s₀
    (isPreconnected_range j₀.continuous) (Set.range_nonempty _)
  haveI : IsClosedImmersion M.ι :=
    IsClosedImmersion.iff_isPreimmersion.2 ⟨inferInstance, by rw [Scheme.Opens.range_ι]; exact hMcl⟩
  let j := IsOpenImmersion.lift M.ι j₀ (by rw [Scheme.Opens.range_ι]; exact hAM)
  have hj : j ≫ M.ι = j₀ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion (j ≫ M.ι) := hj ▸ inferInstance
  haveI : IsClosedImmersion j := IsClosedImmersion.of_comp j M.ι
  have hdim : ∀ x : M.toScheme, topologicalKrullDimAt M.toScheme x = ((3 : ℕ) : WithBot ℕ∞) := by
    intro x
    haveI := smoothOfRelativeDimension_four hM
    haveI : SmoothOfRelativeDimension (3 + 1) (Ch.W.ι ≫ Z ↘ Spec (.of ℂ)) :=
      inferInstanceAs (SmoothOfRelativeDimension (0 + 4) _)
    haveI := Ch.smooth
    have hg : (Ch.ρ ≫ Ch.φ) ≫ Ch.sB = Ch.W.ι ≫ Z ↘ Spec (.of ℂ) := by
      have hφ' : Ch.φ ≫ Ch.sB = Ch.X.ι ≫ sY := Ch.hφ
      rw [Category.assoc, hφ', ← Category.assoc, Ch.hρ, Category.assoc, hM.comp_eq]
    exact (M.ι.isOpenEmbedding.topologicalKrullDimAt_eq x).symm.trans
      (topologicalKrullDimAt_eq_of_isPullback _ Ch.sB (Ch.ρ ≫ Ch.φ) hg 3 i₀ s₀ b₀ hpb _)
  refine ⟨M, M.ι ≫ s₀, M.ι ≫ i₀, j, b₀, inferInstance, hMint,
    M.ι.isClosedEmbedding.compactSpace, inferInstance, ?_, ?_, inferInstance, ?_, hb₀, hdim⟩
  · rw [Category.assoc, hcomp]
  · simp only [Category.assoc]
    rw [reassoc_of% hj]
    exact hj₀
  · rw [Category.assoc, hpb.w, Category.assoc]

open UnderlyingSpace in
/-- **The slice is a smooth quasi-projective threefold.** The slice `M` of `exists_slice` is a
non-singular quasi-projective complex variety of dimension three containing `F_t`. -/
private theorem exists_slice_variety (hM : IsCurvePointExceptionalModel sY r F D)
    [IsComplexScheme Z]
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b),
      (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∈ (Ch.X : Set Y) →
      ∃ (M : Scheme.{0}) (sM : M ⟶ Spec (.of ℂ)) (iW : M ⟶ Ch.W.toScheme)
        (j : pointFibre sY r To t ⟶ M) (b₀ : Spec (.of ℂ) ⟶ Ch.B),
        (letI : M.Over (Spec (.of ℂ)) := ⟨sM⟩;
          IsComplexScheme M ∧ IsIntegral M ∧
          IsSeparated sM ∧ IsQuasiProjectiveVariety ℂ sM ∧
          SmoothOfRelativeDimension 3 sM) ∧
        IsClosedImmersion iW ∧ iW ≫ Ch.W.ι ≫ r ≫ sY = sM ∧
        j ≫ iW ≫ Ch.W.ι = pointFibreFst sY r To t ∧
        IsClosedImmersion j ∧ iW ≫ Ch.ρ ≫ Ch.φ = sM ≫ b₀ ∧ b₀ ≫ Ch.sB = 𝟙 _ := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch hb
  obtain ⟨M, sM, iW, j, b₀, hsm, hint, hcpt, hiW, hcomp, hj, hjc, hpb, hb₀, hdim⟩ :=
    exists_slice hM hT To t Ch hb
  refine ⟨M, sM, iW, j, b₀, ?_, hiW, hcomp, hj, hjc, hpb, hb₀⟩
  letI : M.Over (Spec (.of ℂ)) := ⟨sM⟩
  haveI := hsm
  haveI := hint
  haveI := hiW
  haveI : SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ)) :=
    smoothOfRelativeDimension_of_forall_topologicalKrullDimAt sM 3 hdim
  haveI := Ch.sepW
  haveI := Ch.qcW
  have hsM : (iW ≫ Ch.W.ι) ≫ Z ↘ Spec (.of ℂ) = sM := by
    rw [Category.assoc, ← hM.comp_eq]; exact hcomp
  haveI : IsSeparated (M ↘ Spec (.of ℂ)) := by
    change IsSeparated sM
    rw [← hcomp, ← Category.assoc, ← Category.assoc, Category.assoc (iW ≫ Ch.W.ι) r sY]
    rw [hM.comp_eq, Category.assoc]
    infer_instance
  haveI : QuasiCompact (M ↘ Spec (.of ℂ)) := by
    change QuasiCompact sM
    rw [← hsM, Category.assoc]
    infer_instance
  obtain ⟨h1, h2⟩ := isComplexScheme_of_smoothOfRelativeDimension (M := M) 3
  refine ⟨h1, h2, ‹IsSeparated (M ↘ Spec (.of ℂ))›, ?_⟩
  -- quasi-projectivity: `M` is immersed in the projective variety `Z`
  have hZp : MMP.Mori.IsProjectiveVariety ℂ (r ≫ sY) := by
    have hY := hM.isProjectiveVariety
    rw [MMP.Mori.isProjectiveVariety_iff] at hY ⊢
    exact ⟨hM.isResolution.2.1, hM.isResolution.2.2.2.1.comp hY.2⟩
  have hunit : ∃ (L : (Spec (.of ℂ)).Modules) (hL : Stacks.Ample.IsInvertibleModule _ L),
      letI : Stacks.Ample.IsInvertibleModule _ L := hL
      Stacks.Ample.IsAmple _ L :=
    ⟨_, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (r ≫ sY) := hZp
  haveI : QuasiCompact (iW ≫ Ch.W.ι) := by
    haveI : QuasiCompact Ch.W.ι := by
      haveI : QuasiCompact ((Ch.W.ι ≫ r) ≫ sY) := by
        rw [Category.assoc, hM.comp_eq]; exact Ch.qcW
      exact QuasiCompact.of_comp Ch.W.ι (r ≫ sY)
    infer_instance
  haveI hvar : AlgebraicGeometry.IsVariety ℂ ((iW ≫ Ch.W.ι) ≫ r ≫ sY) := by
    rw [Category.assoc, hcomp]
    exact (MMP.Mori.isVariety_iff ℂ sM).2 ⟨hint,
      (inferInstance : IsSeparated (M ↘ Spec (.of ℂ))),
      (inferInstance : LocallyOfFiniteType (M ↘ Spec (.of ℂ))),
      (inferInstance : QuasiCompact (M ↘ Spec (.of ℂ)))⟩
  have := (isQuasiProjectiveVariety_iff ℂ _).2 ⟨hvar, isQuasiProjective_comp_of_exists_isAmple _ _
      hunit (isQuasiProjective_of_isImmersion (iW ≫ Ch.W.ι))
      (AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ (r ≫ sY)).isQuasiProjective⟩
  rw [Category.assoc, hcomp] at this
  exact ⟨this, (inferInstance : SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ)))⟩

/-- A `ℂ`-point of a scheme locally of finite type over `ℂ` is determined by its image point. -/
private theorem complexPoints_ext_of_base {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {y₁ y₂ : ComplexPoints sX}
    (h : y₁.hom.base (IsLocalRing.closedPoint ℂ) = y₂.hom.base (IsLocalRing.closedPoint ℂ)) :
    y₁ = y₂ := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  apply (ComplexPoints.homeomorphUnderlyingSpace (X := X)).injective
  apply (UnderlyingSpace.equivClosedPoints (K := ℂ) X).injective
  exact Subtype.ext h

open UnderlyingSpace in
/-- **Separating `t` from the other singular points of the slice.** For a slice `M` of an
algebraic exceptional chart through `F_t`, some neighbourhood `V₀` of `t` in `Y^an` has the
following property: every `ℂ`-point of `M` lying on `F` over `V₀` lies on `F_t`. The singular
points of `Y` on the slice form the finite fibre of `C ⟶ B` over `b₀`, from which the point under
`t` is separated by the Hausdorff property. -/
private theorem exists_separating_open (hM : IsCurvePointExceptionalModel sY r F D)
    [IsComplexScheme Z] {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b)
      {M : Scheme.{0}} (sM : M ⟶ Spec (.of ℂ)) (iW : M ⟶ Ch.W.toScheme)
      (j : pointFibre sY r To t ⟶ M) (b₀ : Spec (.of ℂ) ⟶ Ch.B),
      iW ≫ Ch.W.ι ≫ r ≫ sY = sM → j ≫ iW ≫ Ch.W.ι = pointFibreFst sY r To t →
      iW ≫ Ch.ρ ≫ Ch.φ = sM ≫ b₀ → Function.Injective (iW ≫ Ch.W.ι).base →
      ∃ V₀ : Opens (analyticSpace sY), curveOpenInclusion sY To t ∈ V₀ ∧
        ∀ x : ComplexPoints sM,
          (x.hom ≫ iW ≫ Ch.W.ι ≫ r).base (IsLocalRing.closedPoint ℂ) ∈
            (ComplexPoints.toScheme '' (V₀ : Set (analyticSpace sY)) : Set Y) →
          (x.hom ≫ iW ≫ Ch.W.ι).base (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z) →
          x.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range j.base := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch M sM iW j b₀ hcomp hj hpb hinj
  haveI : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI : LocallyOfFiniteType sY := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType (f := sY)
  haveI : IsSeparated sY := AlgebraicGeometry.IsVariety.toIsSeparated (f := sY)
  haveI := Ch.finite
  haveI : T2Space (analyticSpace sY) := MMP.Analytic.ComplexPoints.t2Space
  set y := curveOpenInclusion sY To t
  -- the singular points of `Y` on the slice: a finite set
  let P : Set (analyticSpace sY) := {y' | ∃ c : Ch.C,
    (Ch.iC ≫ Ch.φ).base c = b₀.base (IsLocalRing.closedPoint ℂ) ∧
      y'.hom.base (IsLocalRing.closedPoint ℂ) = Ch.X.ι.base (Ch.iC.base c)}
  have hPfin : P.Finite := by
    haveI : LocallyQuasiFinite (Ch.iC ≫ Ch.φ) := instLocallyQuasiFiniteOfIsFinite _
    have hfib := (Ch.iC ≫ Ch.φ).finite_preimage_singleton (b₀.base (IsLocalRing.closedPoint ℂ))
    have himg := (hfib.image fun c ↦ Ch.X.ι.base (Ch.iC.base c))
    refine Set.Finite.of_finite_image (f := fun y' : analyticSpace sY ↦
      y'.hom.base (IsLocalRing.closedPoint ℂ)) (himg.subset ?_) ?_
    · rintro _ ⟨y', ⟨c, hc, hy'⟩, rfl⟩
      exact ⟨c, hc, hy'.symm⟩
    · intro a _ b _ hab
      exact complexPoints_ext_of_base hab
  let V₀ : Opens (analyticSpace sY) := ⟨(P \ {y})ᶜ, ((hPfin.subset Set.diff_subset).isClosed).isOpen_compl⟩
  refine ⟨V₀, fun h ↦ h.2 rfl, fun x hxV hxF ↦ ?_⟩
  obtain ⟨y', hy'V, hy'x⟩ := hxV
  set pt := IsLocalRing.closedPoint ℂ
  set e := x.hom ≫ iW ≫ Ch.W.ι with he
  have hm : e ≫ r = (x.hom ≫ iW ≫ Ch.ρ) ≫ Ch.X.ι := by
    simp only [he, Category.assoc, Ch.hρ]
  -- the point of `Y` under `x` lies in `X ∩ T` over `b₀`
  have hXT : (e ≫ r).base pt ∈ (Ch.X : Set Y) ∩ T := by
    have hW : e.base pt ∈ r.base ⁻¹' (Ch.X : Set Y) ∩ (F.supp : Set Z) := by
      refine ⟨?_, hxF⟩
      have : (e ≫ r).base pt = Ch.X.ι.base ((x.hom ≫ iW ≫ Ch.ρ).base pt) :=
        congrArg (fun φ : Spec (.of ℂ) ⟶ Y ↦ φ.base pt) hm
      change (e ≫ r).base pt ∈ (Ch.X : Set Y)
      rw [this, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [Ch.supp_inter_eq] at hW
    exact hW
  have hxX : (e ≫ r).base pt = Ch.X.ι.base ((x.hom ≫ iW ≫ Ch.ρ).base pt) :=
    congrArg (fun φ : Spec (.of ℂ) ⟶ Y ↦ φ.base pt) hm
  obtain ⟨c, hc⟩ : (x.hom ≫ iW ≫ Ch.ρ).base pt ∈ Set.range Ch.iC.base := by
    have : Ch.X.ι.base ((x.hom ≫ iW ≫ Ch.ρ).base pt) ∈ Ch.X.ι.base '' Set.range Ch.iC.base := by
      rw [Ch.range_iC, ← hxX]; exact hXT
    obtain ⟨xX', hxX', he'⟩ := this
    exact Ch.X.ι.isOpenEmbedding.injective he' ▸ hxX'
  have hcb : (Ch.iC ≫ Ch.φ).base c = b₀.base pt := by
    have h1 : (Ch.iC ≫ Ch.φ).base c = Ch.φ.base ((x.hom ≫ iW ≫ Ch.ρ).base pt) := by
      rw [← hc]; rfl
    have h2 : ((x.hom ≫ iW ≫ Ch.ρ) ≫ Ch.φ).base pt = ((x.hom ≫ sM) ≫ b₀).base pt := by
      congr 2
      simp only [Category.assoc, hpb]
    have h3 : ((x.hom ≫ sM) ≫ b₀).base pt = b₀.base pt := by
      rw [x.hom_comp_structure, Category.id_comp]
    exact h1.trans (h2.trans h3)
  have hy'x' : y'.hom.base pt = (e ≫ r).base pt := by
    have : y'.toScheme = y'.hom.base pt := by
      unfold ComplexPoints.toScheme
      rw [Subsingleton.elim (default : Spec (.of ℂ)) pt]
    rw [← this]; exact hy'x
  have hy'P : y' ∈ P := ⟨c, hcb, by rw [hc]; exact hy'x'.trans hxX⟩
  have hy'y : y' = y := by
    by_contra hne
    exact hy'V ⟨hy'P, hne⟩
  -- so `x` lies over `t`, hence on `F_t`
  have hstr : (e ≫ r) ≫ sY = 𝟙 _ := by
    simp only [he, Category.assoc]
    rw [hcomp]; exact x.hom_comp_structure
  have hover : e ≫ r = t.hom ≫ To.ι ≫ curveι T := by
    have := complexPoints_ext_of_base (sX := sY) (y₁ := ⟨e ≫ r, hstr⟩) (y₂ := y)
      (by rw [← hy'y]; exact hy'x'.symm)
    exact congrArg ComplexPoints.hom this
  have hstrZ : e ≫ r ≫ sY = 𝟙 _ := by rw [← Category.assoc]; exact hstr
  obtain ⟨z, hz⟩ := exists_pointFibreInclusion_eq To t (V := ⊤) trivial ⟨⟨e, hstrZ⟩, trivial⟩
    (ComplexPoints.ext hover)
  have hz' : z.hom ≫ pointFibreFst sY r To t = e :=
    congrArg (fun w : preimageSpace (resolutionAnalyticMap sY r) ⊤ ↦ w.1.hom) hz
  refine ⟨z.hom.base pt, hinj ?_⟩
  have h1 : (iW ≫ Ch.W.ι).base (j.base (z.hom.base pt)) =
      ((z.hom ≫ j) ≫ iW ≫ Ch.W.ι).base pt := rfl
  rw [h1, Category.assoc, hj, hz']
  rfl

/-- Over an adapted open, the preimage in `Z` of the point under a `ℂ`-point `t` has dimension at
most two. -/
private theorem topologicalKrullDim_preimage_le {T : IrreducibleCloseds Y}
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    topologicalKrullDim (r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) ≤
      ((2 : ℕ) : WithBot ℕ∞) := by
  have h := hTo.topologicalKrullDim_fibre_le (t.hom (default : Spec (.of ℂ)))
  exact ((r.fiberHomeo ((t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)))).isHomeomorph
    |>.topologicalKrullDim_eq).symm.le.trans h

/-- A maximal irreducible subset of `r⁻¹(y)`, for `y` the point under `t`, pulls back to an
irreducible component of the fibre `F_t`. -/
private theorem preimage_mem_irreducibleComponents {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {A : Set Z}
    (hA : Maximal (fun A ↦ IsIrreducible A ∧
      A ⊆ r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A) :
    (pointFibreFst sY r To t) ⁻¹' A ∈ irreducibleComponents (pointFibre sY r To t) := by
  obtain ⟨hemb, hrange⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
  have hAr : A ⊆ Set.range (pointFibreFst sY r To t) := hrange ▸ hA.1.2
  have h := (maximal_image_iff_of_isEmbedding hemb.isEmbedding
    (Q := Set.univ) (A := (pointFibreFst sY r To t) ⁻¹' A)).1 (by
      rw [Set.image_univ, hrange, Set.image_preimage_eq_of_subset hAr]
      exact hA)
  exact ⟨h.1.1, fun B hB hAB ↦ h.2 ⟨hB, Set.subset_univ _⟩ hAB⟩

/-- The `ℂ`-point of `Z` underlying a `ℂ`-point of the fibre `F_t`. -/
private noncomputable def pointFibreZPoint (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) : UnderlyingSpace ℂ Z :=
  ⟨y.hom ≫ pointFibreFst sY r To t, by
    rw [Category.assoc, ← hM.comp_eq, pointFibreFst_comp_structure]
    exact y.hom_comp_structure⟩

/-- A `ℂ`-point of `F_t` lies in a component `S` iff its point of `Z` lies over the image of
`S`. -/
private theorem mem_iff_pointFibreZPoint_mem (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) (S : Set (pointFibre sY r To t)) :
    y.hom.base (IsLocalRing.closedPoint ℂ) ∈ S ↔
      pointFibreZPoint hM To t y ∈ UnderlyingSpace.pointsOver (K := ℂ)
        ((pointFibreFst sY r To t) '' S) := by
  obtain ⟨hemb, -⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
  change _ ↔ (pointFibreFst sY r To t).base (y.hom.base (IsLocalRing.closedPoint ℂ)) ∈
    (pointFibreFst sY r To t).base '' S
  exact (hemb.injective.mem_set_image).symm

/-- A `ℂ`-point of `Z` whose scheme point lies over the point under `t` lies over `t`. -/
private theorem mapFun_eq_of_base_eq (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (p : UnderlyingSpace ℂ Z)
    (hp : r.base (p.toHom (IsLocalRing.closedPoint ℂ)) =
      (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    UnderlyingSpace.mapFun r p =
      ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To t) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) :=
    AlgebraicGeometry.IsVariety.toLocallyOfFiniteType (f := sY)
  apply (UnderlyingSpace.equivClosedPoints (K := ℂ) Y).injective
  apply Subtype.ext
  rw [UnderlyingSpace.equivClosedPoints_apply, UnderlyingSpace.equivClosedPoints_apply,
    UnderlyingSpace.toHom_mapFun]
  change r.base (p.toHom (IsLocalRing.closedPoint ℂ)) =
    (t.hom ≫ To.ι ≫ curveι T) (IsLocalRing.closedPoint ℂ)
  rw [hp, Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)]

/-- Every irreducible component `S` of the fibre `F_t` over a point of `T ⊆ Sing Y` lies in an
exceptional component `E` of `F`. -/
private theorem exists_mem_support_subset_preimage
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y)) (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (S : irreducibleComponents (pointFibre sY r To t)) :
    ∃ E ∈ F.support, (S : Set (pointFibre sY r To t)) ⊆
      (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) := by
  classical
  have hsub : (S : Set (pointFibre sY r To t)) ⊆
      ⋃ E ∈ F.support, (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) := by
    intro x _
    have hxT : r.base ((pointFibreFst sY r To t).base x) ∈ (T : Set Y) := by
      have hrange : Set.range (curveι T).base = (T : Set Y) := by
        rw [Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl
      rw [← hrange, ← Scheme.Hom.comp_apply, pointFibreFst_comp]
      exact ⟨_, rfl⟩
    have hxF : (pointFibreFst sY r To t).base x ∈ (F.supp : Set Z) := by
      rw [hM.supp_eq_preimage_singularLocus]
      exact hT hxT
    rw [DivisorWithCoeffs.coe_supp] at hxF
    simpa using hxF
  obtain ⟨z, hz, hsz⟩ := isIrreducible_iff_sUnion_isClosed.1 S.2.1
    (F.support.image fun E ↦ (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z))
    (fun z hz ↦ by
      obtain ⟨E, -, rfl⟩ := Finset.mem_image.1 hz
      exact E.idealSheaf.support.isClosed.preimage (pointFibreFst sY r To t).continuous)
    (fun x hx ↦ by
      obtain ⟨E, hE, hxE⟩ := Set.mem_iUnion₂.1 (hsub hx)
      exact Set.mem_sUnion.2 ⟨_, Finset.mem_coe.2 (Finset.mem_image_of_mem _ hE), hxE⟩)
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.1 hz
  exact ⟨E, hE, hsz⟩

open UnderlyingSpace in
/-- The complex points over an open of a scheme over `ℂ` form an open set. -/
private theorem isOpen_pointsOver_of_opens {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (W : X.Opens) : IsOpen (pointsOver (K := ℂ) (W : Set X)) := by
  convert isOpen_setOf_le_preimage (K := ℂ) W using 1
  ext p
  exact (top_le_preimage_iff p W).symm

/-- The point of `Y` under a `ℂ`-point `t` of `T°` is closed. -/
private theorem isClosed_singleton_point {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    IsClosed ({(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))} : Set Y) := by
  have hb : (t.hom ≫ To.ι ≫ curveι T) ≫ sY = 𝟙 _ := by
    simpa [Category.assoc] using t.hom_comp_structure
  have : IsClosedImmersion (t.hom ≫ To.ι ≫ curveι T) := isClosedImmersion_of_comp_eq_id sY _ hb
  have h := (t.hom ≫ To.ι ≫ curveι T).isClosedEmbedding.isClosed_range
  convert h using 1
  ext y
  constructor
  · rintro rfl; exact ⟨_, rfl⟩
  · rintro ⟨z, rfl⟩
    rw [Subsingleton.elim z default]
    rfl

/-- **General position of fibre components.** Over a suitable open `U` of `Y` meeting `T`, no
component `S` of a fibre `F_t` lies in two distinct exceptional components: such an `S` would be
a whole component of `E ∩ E'` lying in one fibre, and only finitely many points of `Y` carry
one. -/
private theorem exists_open_eq_of_subset_preimage (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U →
        ∀ t (S : irreducibleComponents (pointFibre sY r To t)) (E E' : Mori.PrimeDivisor Z),
          E ∈ F.support → E' ∈ F.support →
          (S : Set (pointFibre sY r To t)) ⊆
            (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) →
          (S : Set (pointFibre sY r To t)) ⊆
            (pointFibreFst sY r To t).base ⁻¹' (E'.support : Set Z) → E = E' := by
  classical
  haveI : IsNoetherian Z := {}
  haveI := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
  obtain ⟨U₀, U, -, hU, -, Hdisj, -⟩ := exists_open_general hM hT hdim
  -- the components of `E ∩ E'` lying in one fibre
  let bad : Set (Set Z) := ⋃ E ∈ F.support, ⋃ E' ∈ F.support,
    {C | E ≠ E' ∧ Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.support : Set Z) ∩ E'.support) C ∧
      ∃ y, C ⊆ r.base ⁻¹' {y}}
  have hbad : bad.Finite := by
    refine Set.Finite.biUnion F.support.finite_toSet fun E _ ↦
      Set.Finite.biUnion F.support.finite_toSet fun E' _ ↦ ?_
    exact (finite_setOf_maximal _).subset fun C hC ↦ hC.2.1
  have hbadcl : ∀ C ∈ bad, IsClosed C := by
    intro C hC
    simp only [bad, Set.mem_iUnion] at hC
    obtain ⟨E, -, E', -, -, hC, -⟩ := hC
    exact isClosed_of_maximal (E.idealSheaf.support.isClosed.inter
      E'.idealSheaf.support.isClosed) hC
  let B : Set Y := ⋃ C ∈ bad, r.base '' C
  have hB : IsClosed B := hbad.isClosed_biUnion fun C hC ↦ r.isClosedMap _ (hbadcl C hC)
  let U' : Y.Opens := U ⊓ ⟨Bᶜ, hB.isOpen_compl⟩
  -- the generic point of `T` is off `B`
  obtain ⟨η, hgen⟩ : ∃ η, IsGenericPoint η (T : Set Y) := by
    have hgen := T.isIrreducible.isGenericPoint_genericPoint_closure
    rw [T.isClosed.closure_eq] at hgen
    exact ⟨_, hgen⟩
  have hη : η ∈ (U' : Set Y) ∩ T := by
    have hηU : η ∈ (U : Set Y) := by
      obtain ⟨y, hyU, hyT⟩ := hU
      exact (hgen.mem_open_set_iff U.isOpen).2 ⟨y, hyT, hyU⟩
    refine ⟨⟨hηU, ?_⟩, hgen.mem⟩
    intro hηB
    simp only [B, Set.mem_iUnion] at hηB
    obtain ⟨C, hC, z, hzC, hz⟩ := hηB
    have hC' := hC
    simp only [bad, Set.mem_iUnion] at hC'
    obtain ⟨E, -, E', -, -, -, y, hy⟩ := hC'
    have hz' : r.base z = η := hz
    have hrC : r.base '' C = {η} := by
      refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.2 ⟨z, hzC, hz'⟩)
      rintro _ ⟨w, hw, rfl⟩
      exact Set.mem_singleton_iff.2 ((show r.base w = y from hy hw).trans
        ((show r.base z = y from hy hzC).symm.trans hz'))
    have hcl : IsClosed ({η} : Set Y) := hrC ▸ r.isClosedMap _ (hbadcl C hC)
    have hTη : (T : Set Y) = {η} := by
      rw [← hgen.def, hcl.closure_eq]
    haveI : Subsingleton (T : Set Y) := by rw [hTη]; infer_instance
    have h0 : topologicalKrullDim (T : Set Y) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hdim] at h0
    exact absurd h0 (by decide)
  refine ⟨U', ⟨_, hη⟩, fun To hle t S E E' hE hE' hS hS' ↦ ?_⟩
  by_contra hne
  set y := (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))
  have hrange : Set.range (curveι T).base = (T : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hyU : y ∈ (U' : Set Y) := hle (t.hom.base (default : Spec (.of ℂ))).2
  have hyT : y ∈ (T : Set Y) := hrange ▸ ⟨_, rfl⟩
  have hA := maximal_image_pointFibreFst (r := r) To t S E hS
  have hA2 := (Hdisj y ⟨hyU.1, hyT⟩ ⟨E, hE⟩).2 _ hA
  set A := (pointFibreFst sY r To t) '' (S : Set _)
  have hAEE : A ⊆ (E.support : Set Z) ∩ E'.support := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hS hx, hS' hx⟩
  obtain ⟨C, hAC, hC⟩ := exists_subset_maximal_of_isIrreducible hA.1.1 hAEE
  have hCcl : IsClosed C := isClosed_of_maximal (E.idealSheaf.support.isClosed.inter
    E'.idealSheaf.support.isClosed) hC
  have hC2 := topologicalKrullDim_le_two_of_subset_inter hM hne hCcl hC.1.2
  have hQ : IsClosed ((E.support : Set Z) ∩ r.base ⁻¹' {y}) :=
    E.idealSheaf.support.isClosed.inter ((isClosed_singleton_point To t).preimage r.continuous)
  have hAcl : IsClosed A := isClosed_of_maximal hQ hA
  have hAC' : A = C := by
    by_contra hAC'
    have := MMP.topologicalKrullDim_lt_of_subset_of_ne hC.1.1 hAcl hAC hAC'
      (ne_top_of_le_ne_top (by decide) hC2)
    rw [hA2] at this
    exact absurd (this.trans_le hC2) (lt_irrefl _)
  have hCbad : C ∈ bad := by
    simp only [bad, Set.mem_iUnion]
    exact ⟨E, hE, E', hE', hne, hC, y, hAC' ▸ hA.1.2.trans Set.inter_subset_right⟩
  obtain ⟨a, haA⟩ := hA.1.1.nonempty
  have hya : r.base a = y := hA.1.2 haA |>.2
  exact hyU.2 (Set.mem_iUnion₂.2 ⟨C, hCbad, a, hAC haA, hya⟩)

open UnderlyingSpace in
/-- **Transport of one fibre component.** A homeomorphism `F_t(ℂ) ≃ₜ F_{t'}(ℂ)` of fibres over
general points, preserving every component of `F`, carries the complex points of every
component of `F_t` onto those of a component of `F_{t'}`. -/
private theorem exists_transport_component (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To)
    (t t' : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (hdt : ∀ E : F.support,
      (∀ A B : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
          r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
          r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) B → A ≠ B → Disjoint A B))
    (hdt' : ∀ E : F.support,
      (∀ A B : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
          r ⁻¹' {(t'.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
          r ⁻¹' {(t'.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) B → A ≠ B →
          Disjoint A B) ∧
      ∀ A : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
          r ⁻¹' {(t'.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
        topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ (h : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹'
          {ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To t)}) ≃ₜ
        ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹'
          {ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To t')})),
      (∀ E ∈ F.support, ∀ z, (h z : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
        (z : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z)) →
      ∀ S : irreducibleComponents (pointFibre sY r To t),
        ∃ S' : irreducibleComponents (pointFibre sY r To t'), ∀ z,
          (h z : UnderlyingSpace ℂ Z) ∈
              pointsOver (K := ℂ) ((pointFibreFst sY r To t') '' (S' : Set _)) ↔
            (z : UnderlyingSpace ℂ Z) ∈
              pointsOver (K := ℂ) ((pointFibreFst sY r To t) '' (S : Set _)) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI := isComplexScheme_of_isCurvePointExceptionalModel hM
  haveI : IsNoetherian Z := {}
  intro h hE S
  obtain ⟨E, hEs, hSE⟩ := exists_mem_support_subset_preimage hM hT To t S
  have hA := maximal_image_pointFibreFst (r := r) To t S E hSE
  set y := (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))
  set y' := (t'.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))
  have hQ : IsClosed ((E.support : Set Z) ∩ r ⁻¹' {y}) :=
    E.idealSheaf.support.isClosed.inter ((isClosed_singleton_point To t).preimage r.continuous)
  have hR' : IsClosed (r ⁻¹' {y'} : Set Z) :=
    (isClosed_singleton_point To t').preimage r.continuous
  have hQ' : IsClosed ((E.support : Set Z) ∩ r ⁻¹' {y'}) :=
    E.idealSheaf.support.isClosed.inter hR'
  have hEF : (E.support : Set Z) ⊆ (F.supp : Set Z) := by
    intro z hz
    rw [DivisorWithCoeffs.coe_supp]
    exact Set.mem_iUnion₂.2 ⟨E, hEs, hz⟩
  have hsub : ∀ (s : analyticSpace (To.ι ≫ curveι T ≫ sY)),
      pointsOver (K := ℂ) ((E.support : Set Z) ∩
        r ⁻¹' {(s.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) ⊆
      pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹'
        {ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To s)} :=
    fun s p hp ↦ ⟨hEF hp.1, mapFun_eq_of_base_eq hM To s p hp.2⟩
  have hfibre : ∀ (s : analyticSpace (To.ι ≫ curveι T ≫ sY))
      (w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹'
        {ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To s)})),
      (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) ((E.support : Set Z) ∩
        r ⁻¹' {(s.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) ↔
      (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) (E.support : Set Z) := by
    intro s w
    refine ⟨fun hw ↦ hw.1, fun hw ↦ ⟨hw, ?_⟩⟩
    have h2 : mapFun r (w : UnderlyingSpace ℂ Z) =
        ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To s) := w.2.2
    have h3 := congrArg (fun q : UnderlyingSpace ℂ Y ↦ q.toHom (IsLocalRing.closedPoint ℂ)) h2
    simp only [toHom_mapFun] at h3
    change r.base ((w : UnderlyingSpace ℂ Z).toHom (IsLocalRing.closedPoint ℂ)) = _
    rw [Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)]
    exact h3
  obtain ⟨A', hA', htr⟩ := exists_maximal_forall_mem_iff h hQ hQ' (hsub t) (hsub t')
    (fun w ↦ by rw [hfibre t' (h w), hfibre t w]; exact hE E hEs w)
    (hdt ⟨E, hEs⟩) (hdt' ⟨E, hEs⟩).1 hA
  have hA'R := maximal_of_maximal_of_subset Set.inter_subset_right hR'
    (topologicalKrullDim_preimage_le hTo t') hA' (isClosed_of_maximal hQ' hA')
    ((hdt' ⟨E, hEs⟩).2 A' hA')
  obtain ⟨-, hrange⟩ := isClosedEmbedding_pointFibreFst (r := r) To t'
  have hA'r : A' ⊆ Set.range (pointFibreFst sY r To t') := hrange ▸ hA'R.1.2
  refine ⟨⟨_, preimage_mem_irreducibleComponents To t' hA'R⟩, fun z ↦ ?_⟩
  rw [show (pointFibreFst sY r To t') '' ((pointFibreFst sY r To t') ⁻¹' A') = A' from
    Set.image_preimage_eq_of_subset hA'r]
  exact htr z

open UnderlyingSpace in
/-- The `ℂ`-point of `Z` under a `ℂ`-point of `F_t` lies in the exceptional fibre over `t`. -/
private theorem pointFibreZPoint_mem (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    pointFibreZPoint hM To t y ∈ pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹'
      {ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To t)} := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  obtain ⟨-, hrange⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
  have hy : r.base ((pointFibreZPoint hM To t y).toHom (IsLocalRing.closedPoint ℂ)) =
      (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)) := by
    have : (pointFibreFst sY r To t).base (y.hom.base (IsLocalRing.closedPoint ℂ)) ∈
        Set.range (pointFibreFst sY r To t) := ⟨_, rfl⟩
    rw [hrange] at this
    exact this
  refine ⟨?_, mapFun_eq_of_base_eq hM To t _ hy⟩
  change _ ∈ (F.supp : Set Z)
  rw [hM.supp_eq_preimage_singularLocus]
  change r.base ((pointFibreZPoint hM To t y).toHom (IsLocalRing.closedPoint ℂ)) ∈
    (singularLocus sY : Set Y)
  rw [hy]
  have hrangeT : Set.range (curveι T).base = (T : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  exact hT (hrangeT ▸ ⟨_, rfl⟩)

open UnderlyingSpace in
/-- **The bijection of fibre components.** A homeomorphism `F_t(ℂ) ≃ₜ F_{t'}(ℂ)` of fibres over
general points, preserving every component of `F`, induces a bijection between the components of
`F_t` and of `F_{t'}`, matching their complex points. -/
private theorem exists_equiv_transport (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY r To)
    (t t' : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (hd : ∀ s ∈ ({t, t'} : Set (analyticSpace (To.ι ≫ curveι T ≫ sY))), ∀ E : F.support,
      (∀ A B : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
          r ⁻¹' {(s.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
        Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
          r ⁻¹' {(s.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) B → A ≠ B →
          Disjoint A B) ∧
      ∀ A : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
          r ⁻¹' {(s.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
        topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ (h : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹'
          {ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To t)}) ≃ₜ
        ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹'
          {ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To t')})),
      (∀ E ∈ F.support, ∀ z, (h z : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) ↔
        (z : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z)) →
      ∃ e : irreducibleComponents (pointFibre sY r To t) ≃
          irreducibleComponents (pointFibre sY r To t'),
        ∀ S z, (h z : UnderlyingSpace ℂ Z) ∈
              pointsOver (K := ℂ) ((pointFibreFst sY r To t') '' (e S : Set _)) ↔
            (z : UnderlyingSpace ℂ Z) ∈
              pointsOver (K := ℂ) ((pointFibreFst sY r To t) '' (S : Set _)) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro h hE
  have hd₁ := hd t (Or.inl rfl)
  have hd₂ := hd t' (Or.inr rfl)
  have hE' : ∀ E ∈ F.support, ∀ z, (h.symm z : UnderlyingSpace ℂ Z) ∈
      pointsOver (E.support : Set Z) ↔ (z : UnderlyingSpace ℂ Z) ∈ pointsOver (E.support : Set Z) :=
    fun E hEs z ↦ by rw [← hE E hEs (h.symm z), h.apply_symm_apply]
  choose f hf using exists_transport_component hM hT hTo t t' (fun E ↦ (hd₁ E).1) hd₂ h hE
  choose g hg using exists_transport_component hM hT hTo t' t (fun E ↦ (hd₂ E).1) hd₁ h.symm hE'
  have key : ∀ (s : analyticSpace (To.ι ≫ curveι T ≫ sY))
      (S₁ S₂ : irreducibleComponents (pointFibre sY r To s)),
      (∀ w : ↥(pointsOver (K := ℂ) (F.supp : Set Z) ∩ mapFun r ⁻¹'
          {ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To s)}),
        (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) ((pointFibreFst sY r To s) '' S₁) ↔
          (w : UnderlyingSpace ℂ Z) ∈ pointsOver (K := ℂ) ((pointFibreFst sY r To s) '' S₂)) →
      S₁ = S₂ := fun s S₁ S₂ hS ↦
    eq_of_forall_mem_iff_irreducibleComponents hM To s fun y ↦ by
      rw [mem_iff_pointFibreZPoint_mem hM To s y, mem_iff_pointFibreZPoint_mem hM To s y]
      exact hS ⟨_, pointFibreZPoint_mem hM hT To s y⟩
  refine ⟨⟨f, g, fun S ↦ key t _ _ fun w ↦ ?_, fun S' ↦ key t' _ _ fun w ↦ ?_⟩, hf⟩
  · convert (hg (f S) (h w)).trans (hf S w) using 3
    exact (h.symm_apply_apply w).symm
  · convert (hf (g S') (h.symm w)).trans (hg S' w) using 3
    exact (h.apply_symm_apply w).symm

/-- If the maximal irreducible subsets of a closed `Q` in a Noetherian space are pairwise
disjoint, removing one of them leaves a closed set: the union of the others. -/
private theorem isClosed_diff_of_maximal {X' : Type*} [TopologicalSpace X'] [NoetherianSpace X']
    {Q A : Set X'} (hQ : IsClosed Q)
    (hdisj : ∀ A B : Set X', Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) B → A ≠ B → Disjoint A B)
    (hA : Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) A) : IsClosed (Q \ A) := by
  have h : Q \ A = ⋃ B ∈ {B | Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ Q) B ∧ B ≠ A}, B := by
    ext x
    simp only [Set.mem_diff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨hxQ, hxA⟩
      obtain ⟨B, hxB, hB⟩ := exists_subset_maximal_of_isIrreducible isIrreducible_singleton
        (Set.singleton_subset_iff.2 hxQ)
      exact ⟨B, ⟨hB, fun h ↦ hxA (h ▸ hxB rfl)⟩, hxB rfl⟩
    · rintro ⟨B, ⟨hB, hBA⟩, hxB⟩
      exact ⟨hB.1.2 hxB, fun hxA ↦ Set.disjoint_left.1 (hdisj B A hB hA hBA) hxB hxA⟩
  rw [h]
  exact ((finite_setOf_maximal Q).subset fun B hB ↦ hB.1).isClosed_biUnion
    fun B hB ↦ isClosed_of_maximal hQ hB.1

/-- **Closed pieces of the exceptional components.** Over adapted opens inside a suitable open
`U` of `Y` meeting `T`, near every `t` the components of the fibres are matched, and for every
exceptional component `E ⊇ S` there is a closed piece `G = O ∩ E^an` of `E^an ∩ r⁻¹V`, over a
neighbourhood `V` of `t`, meeting `F_t` exactly in `S` and every nearby fibre `F_{t'}` exactly
in the matching component. -/
private theorem exists_open_closedPiece
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U → IsAdaptedOpen sY r To →
        ∀ t, ∃ (O : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY))) (_ : t ∈ O)
          (e : ∀ t' ∈ O, irreducibleComponents (pointFibre sY r To t) ≃
            irreducibleComponents (pointFibre sY r To t')),
          ∀ (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z),
            E ∈ F.support → (S : Set (pointFibre sY r To t)) ⊆
              (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) →
            ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
              (G Oₛ : Set (preimageSpace (resolutionAnalyticMap sY r) V)),
              IsClosed G ∧ IsOpen Oₛ ∧
              G = Oₛ ∩ {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)} ∧
              (∀ y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
                pointFibreInclusion sY r To t hV y ∈ G ↔
                  y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t))) ∧
              ∀ t' (ht' : t' ∈ O), ∃ hV' : curveOpenInclusion sY To t' ∈ V,
                ∀ y : analyticSpace (pointFibre sY r To t' ↘ Spec (.of ℂ)),
                  pointFibreInclusion sY r To t' hV' y ∈ G ↔
                    y.hom.base (IsLocalRing.closedPoint ℂ) ∈
                      ((e t' ht' S : irreducibleComponents (pointFibre sY r To t')) :
                        Set (pointFibre sY r To t')) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI := isComplexScheme_of_isCurvePointExceptionalModel hM
  obtain ⟨U₀, U, hUU₀, hU, Hgerm, Hdisj, HSing⟩ := exists_open_general hM hT hdim
  refine ⟨U, hU, fun To hle hTo t ↦ ?_⟩
  -- the point of `Y` under a point of `T°`
  let pt : analyticSpace (To.ι ≫ curveι T ≫ sY) → UnderlyingSpace ℂ Y := fun t' ↦
    ComplexPoints.homeomorphUnderlyingSpace (X := Y) (curveOpenInclusion sY To t')
  have hpt : Continuous pt :=
    ComplexPoints.homeomorphUnderlyingSpace.continuous.comp (curveOpenInclusion sY To).hom.continuous
  have hptU : ∀ t', pt t' ∈ UnderlyingSpace.pointsOver (K := ℂ) ((U : Set Y) ∩ T) := by
    intro t'
    have hrange : Set.range (curveι T).base = (T : Set Y) := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    refine ⟨?_, ?_⟩
    · change (curveι T).base (To.ι.base (t'.hom.base (IsLocalRing.closedPoint ℂ))) ∈ (U : Set Y)
      exact hle (t'.hom.base (IsLocalRing.closedPoint ℂ)).2
    · change (curveι T).base (To.ι.base (t'.hom.base (IsLocalRing.closedPoint ℂ))) ∈ (T : Set Y)
      exact hrange ▸ ⟨_, rfl⟩
  obtain ⟨Δ, hΔN, ⟨O, hO, hΔO⟩, -, hbΔ, Φ, hΦr, hΦb, hΦE⟩ :=
    Hgerm (pt t) (hptU t) (UnderlyingSpace.pointsOver (K := ℂ) (U : Set Y))
      ((isOpen_pointsOver_of_opens U).mem_nhds (hptU t).1)
  -- the neighbourhood `V` of `t` in `Y^an` and the neighbourhood `O_T` of `t` in `T°`
  let V : Opens (analyticSpace sY) :=
    ⟨ComplexPoints.homeomorphUnderlyingSpace (X := Y) ⁻¹'
        (O ∩ UnderlyingSpace.pointsOver (K := ℂ) (U : Set Y)),
      (hO.inter (isOpen_pointsOver_of_opens U)).preimage
        ComplexPoints.homeomorphUnderlyingSpace.continuous⟩
  let OT : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY)) :=
    ⟨curveOpenInclusion sY To ⁻¹' V, V.isOpen.preimage (curveOpenInclusion sY To).hom.continuous⟩
  have hptΔ : ∀ t' ∈ OT, pt t' ∈ Δ := by
    intro t' ht'
    rw [hΔO]
    exact ⟨ht'.1, hUU₀ (hptU t').1, (hptU t').2⟩
  have htOT : t ∈ OT := ⟨(hΔO ▸ hbΔ).1, (hptU t).1⟩
  -- the fibre homeomorphisms `F_b ≃ₜ F_{b'}`
  let π : ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
      UnderlyingSpace.mapFun r ⁻¹' Δ) → Δ := fun w ↦ ⟨UnderlyingSpace.mapFun r w, w.2.2⟩
  have hΦπ : ∀ p, π (Φ p) = p.2 := fun p ↦ Subtype.ext (hΦr p)
  let hfib : ∀ t' (ht' : t' ∈ OT),
      ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
        UnderlyingSpace.mapFun r ⁻¹' {pt t}) ≃ₜ
      ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
        UnderlyingSpace.mapFun r ⁻¹' {pt t'}) := fun t' ht' ↦
    (fibreHomeomorph π Φ hΦπ ⟨pt t', hptΔ t' ht'⟩).trans
      (fibreSubtypeHomeomorph π _ _ fun w ↦ ⟨fun hw ↦ ⟨⟨hw.1, by
          have h2 : UnderlyingSpace.mapFun r w = pt t' := hw.2
          show UnderlyingSpace.mapFun r w ∈ Δ
          rw [h2]; exact hptΔ t' ht'⟩,
        Subtype.ext hw.2⟩, fun ⟨h, hw⟩ ↦ ⟨h.1, congrArg Subtype.val hw⟩⟩)
  have hfib_apply : ∀ t' (ht' : t' ∈ OT) z,
      (hfib t' ht' z : UnderlyingSpace ℂ Z) = Φ (z, ⟨pt t', hptΔ t' ht'⟩) := fun _ _ _ ↦ rfl
  have hfibE : ∀ t' (ht' : t' ∈ OT), ∀ E ∈ F.support, ∀ z,
      (hfib t' ht' z : UnderlyingSpace ℂ Z) ∈ UnderlyingSpace.pointsOver (E.support : Set Z) ↔
        (z : UnderlyingSpace ℂ Z) ∈ UnderlyingSpace.pointsOver (E.support : Set Z) :=
    fun t' ht' E hE z ↦ by rw [hfib_apply t' ht']; exact hΦE E hE _
  -- the points under `T°` lie in `U ∩ T`
  have hy : ∀ s : analyticSpace (To.ι ≫ curveι T ≫ sY),
      (s.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)) ∈ (U : Set Y) ∩ T := by
    intro s
    rw [Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)]
    exact hptU s
  -- the bijections of fibre components
  have he : ∀ t' (ht' : t' ∈ OT), ∃ e : irreducibleComponents (pointFibre sY r To t) ≃
      irreducibleComponents (pointFibre sY r To t'), ∀ S z,
        (hfib t' ht' z : UnderlyingSpace ℂ Z) ∈ UnderlyingSpace.pointsOver (K := ℂ)
            ((pointFibreFst sY r To t') '' (e S : Set _)) ↔
          (z : UnderlyingSpace ℂ Z) ∈ UnderlyingSpace.pointsOver (K := ℂ)
            ((pointFibreFst sY r To t) '' (S : Set _)) := fun t' ht' ↦
    exists_equiv_transport hM hT hTo t t' (fun s _ E ↦ Hdisj _ (hy s) E) (hfib t' ht')
      (hfibE t' ht')
  choose e he using he
  refine ⟨OT, htOT, e, fun S E hE hSE ↦ ?_⟩
  -- the complex point of `Z` underlying a point of `r⁻¹(V)`
  let κ : preimageSpace (resolutionAnalyticMap sY r) V → UnderlyingSpace ℂ Z := fun z ↦
    ComplexPoints.homeomorphUnderlyingSpace (X := Z)
      (analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm) z.1)
  have hκ : Continuous κ := ComplexPoints.homeomorphUnderlyingSpace.continuous.comp
    ((analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)).hom.continuous.comp
      continuous_subtype_val)
  have hκΔ : ∀ z, κ z ∈ UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) →
      κ z ∈ UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
        UnderlyingSpace.mapFun r ⁻¹' Δ := by
    intro z hF
    refine ⟨hF, ?_⟩
    have hmap : UnderlyingSpace.mapFun r (κ z) =
        ComplexPoints.homeomorphUnderlyingSpace (X := Y) (resolutionAnalyticMap sY r z.1) :=
      Subtype.ext (by
        change (z.1.hom ≫ 𝟙 Z) ≫ r = z.1.hom ≫ r
        rw [Category.comp_id])
    have hV' : ComplexPoints.homeomorphUnderlyingSpace (X := Y) (resolutionAnalyticMap sY r z.1) ∈
        O ∩ UnderlyingSpace.pointsOver (K := ℂ) (U : Set Y) := z.2
    change UnderlyingSpace.mapFun r (κ z) ∈ Δ
    rw [hmap, hΔO]
    refine ⟨hV'.1, hUU₀ hV'.2, ?_⟩
    have hFS : r.base ((κ z).toHom (IsLocalRing.closedPoint ℂ)) ∈ (singularLocus sY : Set Y) := by
      have h := hF
      change (κ z).toHom (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z) at h
      rw [hM.supp_eq_preimage_singularLocus] at h
      exact h
    have hrw : (ComplexPoints.homeomorphUnderlyingSpace (X := Y)
        (resolutionAnalyticMap sY r z.1)).toHom (IsLocalRing.closedPoint ℂ) =
        r.base ((κ z).toHom (IsLocalRing.closedPoint ℂ)) := by
      rw [← hmap]; rfl
    have hUS : (ComplexPoints.homeomorphUnderlyingSpace (X := Y)
        (resolutionAnalyticMap sY r z.1)).toHom (IsLocalRing.closedPoint ℂ) ∈
        (U : Set Y) ∩ (singularLocus sY : Set Y) := ⟨hV'.2, hrw ▸ hFS⟩
    rw [HSing] at hUS
    exact hUS.2
  let A : Set Z := (pointFibreFst sY r To t) '' (S : Set _)
  let Q : Set Z := (E.support : Set Z) ∩
    r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}
  let G : Set (preimageSpace (resolutionAnalyticMap sY r) V) :=
    {z | ∃ hz : κ z ∈ UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
        UnderlyingSpace.mapFun r ⁻¹' Δ,
      ((Φ.symm ⟨κ z, hz⟩).1 : UnderlyingSpace ℂ Z) ∈ UnderlyingSpace.pointsOver (K := ℂ) A}
  let Bad : Set (preimageSpace (resolutionAnalyticMap sY r) V) :=
    {z | ∃ hz : κ z ∈ UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
        UnderlyingSpace.mapFun r ⁻¹' Δ,
      ((Φ.symm ⟨κ z, hz⟩).1 : UnderlyingSpace ℂ Z) ∈
        UnderlyingSpace.pointsOver (K := ℂ) Q \ UnderlyingSpace.pointsOver (K := ℂ) A}
  have hκpt : ∀ s (hs : curveOpenInclusion sY To s ∈ V)
      (y : analyticSpace (pointFibre sY r To s ↘ Spec (.of ℂ))),
      κ (pointFibreInclusion sY r To s hs y) = pointFibreZPoint hM To s y :=
    fun _ _ _ ↦ Subtype.ext (Category.comp_id _)
  have hsymm : ∀ (z : ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
        UnderlyingSpace.mapFun r ⁻¹' {pt t})) (d : Δ) hz,
      Φ.symm ⟨((Φ (z, d) : _) : UnderlyingSpace ℂ Z), hz⟩ = (z, d) := by
    intro z d hz
    apply Φ.injective
    rw [Φ.apply_symm_apply]
  have hAE : UnderlyingSpace.pointsOver (K := ℂ) A ⊆
      UnderlyingSpace.pointsOver (K := ℂ) (E.support : Set Z) := by
    rintro p ⟨x, hx, hxp⟩
    change p.toHom (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)
    rw [← hxp]
    exact hSE hx
  have hκE : ∀ z, κ z ∈ UnderlyingSpace.pointsOver (K := ℂ) (E.support : Set Z) ↔
      z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z) := fun z ↦ by
    change (z.1.hom ≫ 𝟙 Z).base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z) ↔ _
    rw [Category.comp_id]
  have hEF : (E.support : Set Z) ⊆ (F.supp : Set Z) := by
    intro x hx
    rw [DivisorWithCoeffs.coe_supp]
    exact Set.mem_iUnion₂.2 ⟨E, hE, hx⟩
  have hfibQ : ∀ (w : ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
      UnderlyingSpace.mapFun r ⁻¹' {pt t})),
      (w : UnderlyingSpace ℂ Z) ∈ UnderlyingSpace.pointsOver (K := ℂ) (E.support : Set Z) →
      (w : UnderlyingSpace ℂ Z) ∈ UnderlyingSpace.pointsOver (K := ℂ) Q := by
    intro w hw
    refine ⟨hw, ?_⟩
    have h2 : UnderlyingSpace.mapFun r (w : UnderlyingSpace ℂ Z) = pt t := w.2.2
    have h3 := congrArg (fun q : UnderlyingSpace ℂ Y ↦ q.toHom (IsLocalRing.closedPoint ℂ)) h2
    simp only [UnderlyingSpace.toHom_mapFun] at h3
    change r.base ((w : UnderlyingSpace ℂ Z).toHom (IsLocalRing.closedPoint ℂ)) =
      (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))
    rw [Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)]
    exact h3
  haveI : IsNoetherian Z := {}
  have hP : IsClosed {z | κ z ∈ UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z)} :=
    (UnderlyingSpace.isClosed_pointsOver (K := ℂ) F.supp.isClosed).preimage hκ
  have hψ : Continuous (fun z : {z | κ z ∈ UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z)} ↦
      (⟨κ z.1, hκΔ z.1 z.2⟩ : ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
        UnderlyingSpace.mapFun r ⁻¹' Δ))) :=
    (hκ.comp continuous_subtype_val).subtype_mk _
  have hfst : Continuous fun w : ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
      UnderlyingSpace.mapFun r ⁻¹' Δ) ↦ ((Φ.symm w).1 : UnderlyingSpace ℂ Z) :=
    continuous_subtype_val.comp (continuous_fst.comp Φ.symm.continuous)
  have hAmax := maximal_image_pointFibreFst (r := r) To t S E hSE
  have hQcl : IsClosed Q :=
    E.idealSheaf.support.isClosed.inter ((isClosed_singleton_point To t).preimage r.continuous)
  have hAcl : IsClosed A := isClosed_of_maximal hQcl hAmax
  refine ⟨V, htOT, G, Badᶜ, ?_, ?_, ?_, fun y ↦ ?_, fun t' ht' ↦ ⟨ht', fun y ↦ ?_⟩⟩
  · convert isClosed_setOf_exists_mem hP _ hψ
      ((UnderlyingSpace.isClosed_pointsOver (K := ℂ) hAcl).preimage hfst) using 1
    ext z
    exact ⟨fun ⟨hz, hA⟩ ↦ ⟨hz.1, hA⟩, fun ⟨hz, hA⟩ ↦ ⟨hκΔ z hz, hA⟩⟩
  · rw [isOpen_compl_iff]
    have hQA : IsClosed (UnderlyingSpace.pointsOver (K := ℂ) Q \
        UnderlyingSpace.pointsOver (K := ℂ) A) :=
      UnderlyingSpace.isClosed_pointsOver (K := ℂ)
        (isClosed_diff_of_maximal hQcl (Hdisj _ (hy t) ⟨E, hE⟩).1 hAmax)
    convert isClosed_setOf_exists_mem hP _ hψ (hQA.preimage hfst) using 1
    ext z
    exact ⟨fun ⟨hz, hA⟩ ↦ ⟨hz.1, hA⟩, fun ⟨hz, hA⟩ ↦ ⟨hκΔ z hz, hA⟩⟩
  · ext z
    constructor
    · rintro ⟨hz, hA⟩
      refine ⟨fun ⟨hz', hQ, hnA⟩ ↦ hnA hA, (hκE z).1 ?_⟩
      have := (hΦE E hE (Φ.symm ⟨κ z, hz⟩)).2 (hAE hA)
      rwa [Φ.apply_symm_apply] at this
    · rintro ⟨hnb, hzE⟩
      have hκz := (hκE z).2 hzE
      have hz := hκΔ z (hEF hκz)
      refine ⟨hz, ?_⟩
      have hp := (hΦE E hE (Φ.symm ⟨κ z, hz⟩)).1 (by rw [Φ.apply_symm_apply]; exact hκz)
      by_contra hnA
      exact hnb ⟨hz, hfibQ _ hp, hnA⟩
  · rw [mem_iff_pointFibreZPoint_mem hM To t y]
    have hz := pointFibreZPoint_mem hM hT To t y
    have hΦz : ((Φ (⟨_, hz⟩, ⟨pt t, hbΔ⟩) : _) : UnderlyingSpace ℂ Z) =
        pointFibreZPoint hM To t y := hΦb _
    constructor
    · rintro ⟨hz', hA⟩
      have e1 : (⟨κ (pointFibreInclusion sY r To t htOT y), hz'⟩ :
          ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
            UnderlyingSpace.mapFun r ⁻¹' Δ)) = Φ (⟨_, hz⟩, ⟨pt t, hbΔ⟩) :=
        Subtype.ext ((hκpt t htOT y).trans hΦz.symm)
      rw [e1, Φ.symm_apply_apply] at hA
      exact hA
    · intro hA
      refine ⟨(hκpt t htOT y) ▸ hΦz ▸ (Φ (⟨_, hz⟩, ⟨pt t, hbΔ⟩)).2, ?_⟩
      have e1 : (⟨κ (pointFibreInclusion sY r To t htOT y), (hκpt t htOT y) ▸ hΦz ▸
          (Φ (⟨_, hz⟩, ⟨pt t, hbΔ⟩)).2⟩ :
          ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
            UnderlyingSpace.mapFun r ⁻¹' Δ)) = Φ (⟨_, hz⟩, ⟨pt t, hbΔ⟩) :=
        Subtype.ext ((hκpt t htOT y).trans hΦz.symm)
      rw [e1, Φ.symm_apply_apply]
      exact hA
  · rw [mem_iff_pointFibreZPoint_mem hM To t' y]
    set q : ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
        UnderlyingSpace.mapFun r ⁻¹' {pt t'}) := ⟨_, pointFibreZPoint_mem hM hT To t' y⟩
    set w := (hfib t' ht').symm q
    have hΦw : ((Φ (w, ⟨pt t', hptΔ t' ht'⟩) : _) : UnderlyingSpace ℂ Z) =
        pointFibreZPoint hM To t' y := by
      rw [← hfib_apply t' ht' w, (hfib t' ht').apply_symm_apply]
    have hmem : κ (pointFibreInclusion sY r To t' ht' y) ∈
        UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
          UnderlyingSpace.mapFun r ⁻¹' Δ :=
      (hκpt t' ht' y) ▸ hΦw ▸ (Φ (w, ⟨pt t', hptΔ t' ht'⟩)).2
    have e1 : (⟨κ (pointFibreInclusion sY r To t' ht' y), hmem⟩ :
        ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
          UnderlyingSpace.mapFun r ⁻¹' Δ)) = Φ (w, ⟨pt t', hptΔ t' ht'⟩) :=
      Subtype.ext ((hκpt t' ht' y).trans hΦw.symm)
    have key := he t' ht' S w
    rw [(hfib t' ht').apply_symm_apply] at key
    constructor
    · rintro ⟨hz', hA⟩
      have e2 : (⟨κ (pointFibreInclusion sY r To t' ht' y), hz'⟩ :
          ↥(UnderlyingSpace.pointsOver (K := ℂ) (F.supp : Set Z) ∩
            UnderlyingSpace.mapFun r ⁻¹' Δ)) = Φ (w, ⟨pt t', hptΔ t' ht'⟩) :=
        Subtype.ext ((hκpt t' ht' y).trans hΦw.symm)
      rw [e2, Φ.symm_apply_apply] at hA
      exact key.2 hA
    · intro hA
      refine ⟨hmem, ?_⟩
      rw [e1, Φ.symm_apply_apply]
      exact key.1 hA

/-- **Existence of local classes.** Over adapted opens inside a suitable open `U` of `Y`
meeting `T`, near every `t` the components of the fibres are matched, and every exceptional
component `E ⊇ S` has a local class along `S` on a neighbourhood of `F_t` which is a local class
along the matching component of every nearby fibre. -/
private theorem exists_open_isLocalClass
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U → IsAdaptedOpen sY r To →
        ∀ t, ∃ (O : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY))) (_ : t ∈ O)
          (e : ∀ t' ∈ O, irreducibleComponents (pointFibre sY r To t) ≃
            irreducibleComponents (pointFibre sY r To t')),
          ∀ (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z),
            E ∈ F.support → (S : Set (pointFibre sY r To t)) ⊆
              (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) →
            ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
              (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
              IsLocalClass hM To t S E hV α ∧
              ∀ t' (ht' : t' ∈ O), ∃ hV' : curveOpenInclusion sY To t' ∈ V,
                IsLocalClass hM To t' (e t' ht' S) E hV' α := by
  obtain ⟨U, hU, H⟩ := exists_open_closedPiece hM hT hdim
  refine ⟨U, hU, fun To hle hTo t ↦ ?_⟩
  obtain ⟨O, htO, e, h⟩ := H To hle hTo t
  refine ⟨O, htO, e, fun S E hE hS ↦ ?_⟩
  obtain ⟨V, hV, G, Oₛ, hG, hOₛ, hGO, hfib, hprop⟩ := h S E hE hS
  obtain ⟨α, hα⟩ := exists_forall_isLocalClass hM To E G hG Oₛ hOₛ hGO
  refine ⟨V, hV, α, hα t S hV hfib, fun t' ht' ↦ ?_⟩
  obtain ⟨hV', hfib'⟩ := hprop t' ht'
  exact ⟨hV', hα t' _ hV' hfib'⟩

/-- The component `S` along which `α` is a local class of `E` lies in `E`: its closed points,
which are dense, are complex points of the piece `G ⊆ E^an`. -/
private theorem subset_preimage_of_isLocalClass (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} {To : (curveScheme T).Opens}
    {t : analyticSpace (To.ι ≫ curveι T ≫ sY)} {S : irreducibleComponents (pointFibre sY r To t)}
    {E : Mori.PrimeDivisor Z} {V : Opens (analyticSpace sY)} {hV : curveOpenInclusion sY To t ∈ V}
    {α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2}
    (h : IsLocalClass hM To t S E hV α) :
    (S : Set (pointFibre sY r To t)) ⊆
      (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) := by
  obtain ⟨G, -, -, ⟨O, -, hGO⟩, hfib, -⟩ := h
  haveI : LocallyOfFiniteType r := by
    have : LocallyOfFiniteType (r ≫ sY) := hM.isResolution.2.1.toLocallyOfFiniteType
    exact LocallyOfFiniteType.of_comp (g := sY) this
  haveI : LocallyOfFiniteType (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (pullback.snd r (t.hom ≫ To.ι ≫ curveι T))
    infer_instance
  haveI : JacobsonSpace (pointFibre sY r To t) :=
    LocallyOfFiniteType.jacobsonSpace (pointFibre sY r To t ↘ Spec (.of ℂ))
  have hS : IsClosed (S : Set (pointFibre sY r To t)) :=
    isClosed_of_mem_irreducibleComponents _ S.2
  rw [← closure_inter_closedPoints hS]
  refine closure_minimal (fun a ⟨ha, hac⟩ ↦ ?_)
    (E.idealSheaf.support.isClosed.preimage (pointFibreFst sY r To t).continuous)
  obtain ⟨p, hp⟩ : ∃ p : UnderlyingSpace ℂ (pointFibre sY r To t),
      p.toHom (IsLocalRing.closedPoint ℂ) = a :=
    ⟨(UnderlyingSpace.equivClosedPoints (K := ℂ) _).symm ⟨a, hac⟩, by
      rw [← UnderlyingSpace.equivClosedPoints_apply, Equiv.apply_symm_apply]⟩
  let y := (ComplexPoints.homeomorphUnderlyingSpace (X := pointFibre sY r To t)).symm p
  have hya : y.hom.base (IsLocalRing.closedPoint ℂ) = a := hp
  have hyG := (hfib y).2 (hya ▸ ha)
  rw [hGO] at hyG
  rw [← hya]
  exact hyG.2

/-- **Uniqueness of local classes.** Over adapted opens inside a suitable open `U` of `Y`
meeting `T`, the germ in `𝒲_t` of a local class along a component `S` of `F_t` depends only on
`S`. -/
private theorem exists_open_classGerm_eq
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U → IsAdaptedOpen sY r To →
        ∀ t (S : irreducibleComponents (pointFibre sY r To t)) (E E' : Mori.PrimeDivisor Z)
          (V V' : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
          (hV' : curveOpenInclusion sY To t ∈ V')
          (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
          (α' : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V') 2),
          E ∈ F.support → E' ∈ F.support →
          IsLocalClass hM To t S E hV α → IsLocalClass hM To t S E' hV' α' →
          classGerm sY r To t hV α = classGerm sY r To t hV' α' := by
  obtain ⟨U, hU, H⟩ := exists_open_eq_of_subset_preimage hM hT hdim
  refine ⟨U, hU, fun To hle _ t S E E' V V' hV hV' α α' hE hE' h h' ↦ ?_⟩
  obtain rfl := H To hle t S E E' hE hE' (subset_preimage_of_isLocalClass hM h)
    (subset_preimage_of_isLocalClass hM h')
  obtain ⟨G, hG, hK, ⟨O, hO, hGO⟩, hfib, rfl⟩ := h
  obtain ⟨G', hG', hK', ⟨O', hO', hGO'⟩, hfib', rfl⟩ := h'
  haveI := isInvertible_divisorialSheaf_single hM E
  exact classGerm_canonicalClass_eq hM To t S E hV hV' G G' hG hK hG' hK'
    (by rw [hGO]; exact Set.inter_subset_right) (by rw [hGO']; exact Set.inter_subset_right)
    hfib hfib'

/-- **Local classes lie in the kernel.** The germ of a local class of an exceptional component
lies in `ker (r_t : 𝒲_t ⟶ 𝒱_{T,t})`: the class vanishes off its piece of `F`, hence on
`r⁻¹(V) ∩ r⁻¹(Y_reg) ≅ j⁻¹(V)`. -/
private theorem classGerm_mem_ker (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {S : irreducibleComponents (pointFibre sY r To t)}
    {E : Mori.PrimeDivisor Z} (hE : E ∈ F.support) {V : Opens (analyticSpace sY)}
    {hV : curveOpenInclusion sY To t ∈ V}
    {α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2}
    (h : IsLocalClass hM To t S E hV α) :
    classGerm sY r To t hV α ∈
      LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom := by
  obtain ⟨G, -, ⟨O, -, hGO⟩, -, h0, -⟩ := h.properties
  let ρ := preimageRestrict (resolutionAnalyticMap sY r)
    (analyticMap (regularSection sY hM.isBiregular)
      (by rw [← Category.assoc, regularSection_comp]))
    (regularSection_analyticMap_comp sY hM.isBiregular) V
  have hreg : ∀ x, ρ x ∉ G := by
    intro x hx
    rw [hGO] at hx
    have hE' : (ρ x).1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z) := hx.2
    have hF : (ρ x).1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z) := by
      rw [DivisorWithCoeffs.coe_supp]
      exact Set.mem_iUnion₂.2 ⟨E, hE, hE'⟩
    rw [hM.supp_eq_preimage_singularLocus] at hF
    have hcomp : (ρ x).1.hom ≫ r = x.1.hom ≫ (smoothLocus sY).ι := by
      change (x.1.hom ≫ regularSection sY hM.isBiregular) ≫ r = _
      rw [Category.assoc, regularSection_comp]
    have hr : r.base ((ρ x).1.hom.base (IsLocalRing.closedPoint ℂ)) =
        (smoothLocus sY).ι.base (x.1.hom.base (IsLocalRing.closedPoint ℂ)) :=
      congrArg (fun f : Spec (.of ℂ) ⟶ Y ↦ f.base (IsLocalRing.closedPoint ℂ)) hcomp
    rw [Set.mem_preimage, hr] at hF
    exact hF ((smoothLocus sY).range_ι ▸ ⟨_, rfl⟩)
  let g : preimageSpace (regularInclusion sY) V ⟶ TopCat.of (Gᶜ : Set _) :=
    TopCat.ofHom ⟨fun x ↦ ⟨ρ x, hreg x⟩, ρ.hom.continuous.subtype_mk _⟩
  have hρ : ρ = g ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := rfl
  have hzero : (rationalCohomologyMap ρ 2).hom α = 0 := by
    rw [hρ, rationalCohomologyMap_comp, ModuleCat.comp_apply, h0, map_zero]
  rw [LinearMap.mem_ker]
  refine (localSystemRestrictionFibre_germ sY hM.isBiregular To t hV α).trans ?_
  change (stalkToPullbackStalk _ _ t).hom ((higherDirectImageGerm _ 2 _ hV).hom
    ((rationalCohomologyMap ρ 2).hom α)) = 0
  rw [hzero, map_zero, map_zero]

/-- Every vector of `𝒲_t` is the germ of a class on a tube `r⁻¹(V)`. -/
private theorem exists_classGerm_eq {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) (β : resolutionLocalSystemFibre sY r To t) :
    ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
      classGerm sY r To t hV α = β := by
  haveI := isIso_stalkToPullbackStalk (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY r 2) t
  obtain ⟨γ, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 this).2 β
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (C := ModuleCat.{0} ℚ)
    (𝓕 := directImagePresheaf (resolutionAnalyticMap sY r) 2)
    (p₀ := curveOpenInclusion sY To t)
  obtain ⟨δ, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 this).2 γ
  obtain ⟨V, hV, α, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ δ
  exact ⟨V, hV, α, rfl⟩

/-- A class whose germ in `𝒲_t` vanishes restricts to zero on a smaller tube. -/
private theorem exists_le_eq_zero_of_classGerm_eq_zero {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
    (h : classGerm sY r To t hV α = 0) :
    ∃ (V' : Opens (analyticSpace sY)) (_ : curveOpenInclusion sY To t ∈ V') (hle : V' ≤ V),
      (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) hle) 2).hom α = 0 := by
  have h0 : (higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α = 0 :=
    injective_stalkToPullbackStalk _ _ t (h.trans (map_zero _).symm)
  exact exists_res_eq_zero_of_germ_eq_zero _ 2 _ hV α h0

/-- Over the smooth locus the section of `r` inverts `r`: a `ℂ`-point `z` of `Z` over a point
`x` of `Y_reg` is the image of `x` under the section. -/
private theorem comp_regularSection_eq (hM : IsCurvePointExceptionalModel sY r F D)
    {z : Spec (.of ℂ) ⟶ Z} (x : Spec (.of ℂ) ⟶ (smoothLocus sY : Scheme.{0}))
    (h : x ≫ (smoothLocus sY).ι = z ≫ r) : x ≫ regularSection sY hM.isBiregular = z := by
  haveI : IsIso (r ∣_ smoothLocus sY) := hM.isBiregular
  have hz : Set.range z.base ⊆ Set.range (r ⁻¹ᵁ smoothLocus sY).ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    change r.base (z.base p) ∈ smoothLocus sY
    rw [← Scheme.Hom.comp_apply, ← h, Scheme.Hom.comp_apply]
    exact (Scheme.Opens.range_ι (smoothLocus sY)).subset ⟨_, rfl⟩
  set z' := IsOpenImmersion.lift (r ⁻¹ᵁ smoothLocus sY).ι z hz
  have hz' : z' ≫ (r ⁻¹ᵁ smoothLocus sY).ι = z := IsOpenImmersion.lift_fac _ _ _
  have hx : z' ≫ (r ∣_ smoothLocus sY) = x := by
    rw [← cancel_mono (smoothLocus sY).ι, Category.assoc, morphismRestrict_ι, ← Category.assoc,
      hz', h]
  unfold regularSection
  rw [← hx, Category.assoc]
  exact (congrArg (z' ≫ ·) (@IsIso.hom_inv_id_assoc _ _ _ _ (r ∣_ smoothLocus sY)
    hM.isBiregular _ _)).trans hz'

/-- **Vanishing off the exceptional divisor.** If the germ of `α` lies in `ker r_t`, then on a
smaller tube `α` vanishes on the complement of `F`: the germ of its restriction to
`j⁻¹(V) ≅ r⁻¹(V) ∖ F` vanishes. -/
private theorem exists_le_compl_eq_zero (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
    (h : (localSystemRestrictionFibre sY hM.isBiregular To t).hom (classGerm sY r To t hV α) = 0) :
    ∃ (V' : Opens (analyticSpace sY)) (_ : curveOpenInclusion sY To t ∈ V') (hle : V' ≤ V),
      (rationalCohomologyMap (X' := TopCat.of ({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∉
          (F.supp : Set Z)} : Set (preimageSpace (resolutionAnalyticMap sY r) V')))
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom
        ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) hle) 2).hom α) =
        0 := by
  let ρ := fun V : Opens (analyticSpace sY) ↦ preimageRestrict (resolutionAnalyticMap sY r)
    (analyticMap (regularSection sY hM.isBiregular)
      (by rw [← Category.assoc, regularSection_comp]))
    (regularSection_analyticMap_comp sY hM.isBiregular) V
  have h1 := (localSystemRestrictionFibre_germ sY hM.isBiregular To t hV α).symm.trans h
  have h2 : (higherDirectImageGerm (regularInclusion sY) 2 _ hV).hom
      ((rationalCohomologyMap (ρ V) 2).hom α) = 0 :=
    injective_stalkToPullbackStalk _ _ t (h1.trans (map_zero _).symm)
  obtain ⟨V', hV', hle, h3⟩ := exists_res_eq_zero_of_germ_eq_zero _ 2 _ hV _ h2
  refine ⟨V', hV', hle, ?_⟩
  -- the inverse of the section, off `F`
  have hemb := isOpenEmbedding_realize_ι (sX := sY) (smoothLocus sY)
  let Fc : Set (preimageSpace (resolutionAnalyticMap sY r) V') :=
    {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∉ (F.supp : Set Z)}
  have hmem : ∀ z : Fc, resolutionAnalyticMap sY r z.1.1 ∈
      Set.range (realize (sX := (smoothLocus sY).ι ≫ sY) (smoothLocus sY).ι rfl) := by
    intro z
    rw [range_realize_ι]
    have hz : z.1.1.hom.base (IsLocalRing.closedPoint ℂ) ∉ (F.supp : Set Z) := z.2
    rw [hM.supp_eq_preimage_singularLocus] at hz
    change (z.1.1.hom ≫ r).base (default : Spec (.of ℂ)) ∈ smoothLocus sY
    rw [Subsingleton.elim (default : Spec (.of ℂ)) (IsLocalRing.closedPoint ℂ)]
    by_contra h'
    exact hz h'
  let e₀ : Fc → analyticSpace ((smoothLocus sY).ι ≫ sY) := fun z ↦
    hemb.isEmbedding.toHomeomorph.symm ⟨_, hmem z⟩
  have he₀ : ∀ z, realize (sX := (smoothLocus sY).ι ≫ sY) (smoothLocus sY).ι rfl (e₀ z) =
      resolutionAnalyticMap sY r z.1.1 := fun z ↦
    congrArg Subtype.val (hemb.isEmbedding.toHomeomorph.apply_symm_apply ⟨_, hmem z⟩)
  have he₁ : ∀ z, e₀ z ∈ (regularInclusion sY) ⁻¹' (V' : Set (analyticSpace sY)) := by
    intro z
    change realize (sX := (smoothLocus sY).ι ≫ sY) (smoothLocus sY).ι rfl (e₀ z) ∈ V'
    rw [he₀]
    exact z.1.2
  have hcont : Continuous e₀ := hemb.isEmbedding.toHomeomorph.symm.continuous.comp
    (((resolutionAnalyticMap sY r).hom.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)
  let e : TopCat.of Fc ⟶ preimageSpace (regularInclusion sY) V' :=
    TopCat.ofHom ⟨fun z ↦ ⟨e₀ z, he₁ z⟩, hcont.subtype_mk he₁⟩
  have hfac : (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of Fc ⟶ _) ≫
      preimageInclusion (resolutionAnalyticMap sY r) hle =
      e ≫ preimageInclusion (regularInclusion sY) hle ≫ ρ V := by
    ext z
    change z.1.1.hom = (e₀ z).hom ≫ regularSection sY hM.isBiregular
    exact (comp_regularSection_eq hM _ (congrArg ComplexPoints.hom (he₀ z))).symm
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hfac, rationalCohomologyMap_comp,
    rationalCohomologyMap_comp, ModuleCat.comp_apply, ModuleCat.comp_apply]
  change (rationalCohomologyMap e 2).hom ((rationalCohomologyMap
    (preimageInclusion (regularInclusion sY) hle) 2).hom ((rationalCohomologyMap (ρ V) 2).hom α)) = 0
  rw [h3, map_zero]

/-- The fibre `F_t` of the proper morphism `r` has finitely many irreducible components. -/
private theorem finite_irreducibleComponents_pointFibre (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) :
    Finite (irreducibleComponents (pointFibre sY r To t)) := by
  haveI : LocallyOfFiniteType r := by
    have : LocallyOfFiniteType (r ≫ sY) := hM.isResolution.2.1.toLocallyOfFiniteType
    exact LocallyOfFiniteType.of_comp (g := sY) this
  haveI : LocallyOfFiniteType (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (pullback.snd r (t.hom ≫ To.ι ≫ curveι T))
    infer_instance
  haveI : IsLocallyNoetherian (pointFibre sY r To t) :=
    LocallyOfFiniteType.isLocallyNoetherian (pointFibre sY r To t ↘ Spec (.of ℂ))
  haveI : QuasiCompact (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
    change QuasiCompact (pullback.snd r (t.hom ≫ To.ι ≫ curveι T))
    haveI : QuasiCompact r := by
      haveI := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
      infer_instance
    infer_instance
  haveI : CompactSpace (pointFibre sY r To t) :=
    QuasiCompact.compactSpace_of_compactSpace (pointFibre sY r To t ↘ Spec (.of ℂ))
  haveI : IsNoetherian (pointFibre sY r To t) := {}
  exact NoetherianSpace.finite_irreducibleComponents

/-- **The fibres are surfaces.** If every maximal irreducible piece of `E ∩ r⁻¹(y)` is a
surface, for every component `E` of `F`, then the fibre `F_t` over `y` has dimension at most
`2`. -/
private theorem topologicalKrullDim_pointFibre_le (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (h2 : ∀ E : F.support, ∀ A : Set Z,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim (pointFibre sY r To t) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
  apply MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents
  intro S hS
  obtain ⟨E, hE, hSE⟩ := exists_mem_support_subset_preimage hM hT To t ⟨S, hS⟩
  have hA := maximal_image_pointFibreFst (r := r) To t ⟨S, hS⟩ E hSE
  rw [← h2 ⟨E, hE⟩ _ hA]
  obtain ⟨hemb, -⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
  let f : S → ((pointFibreFst sY r To t) '' S : Set Z) := fun x ↦ ⟨_, Set.mem_image_of_mem _ x.2⟩
  refine Topology.IsInducing.topologicalKrullDim_le (f := f) ?_
  refine (Topology.IsInducing.subtypeVal.of_comp_iff).1 ?_
  exact hemb.isInducing.comp Topology.IsInducing.subtypeVal

/-- **Counting classes through a supported lift.** Let `g : N ⟶ X` carry the complement of
`D ⊆ N` off `Φ ⊆ X`, and let `L` be a linear map on `H²(X; ℚ)` killing every class whose
pullback along `ι = q ≫ g : Q ⟶ X` vanishes. Then a family of classes on `X` vanishing off `Φ`
whose images under `L` are linearly independent has at most `rank H²(N, N ∖ D; ℚ)` members: each
lifts to `H²(X, X ∖ Φ)`, and pulling back to `H²(N, N ∖ D)` is injective on their span. -/
private theorem card_le_rank_cohomologyWithSupports {X N Q : TopCat.{0}} (Φ : Set X) (D : Set N)
    (g : N ⟶ X) (hg : Dᶜ ⊆ g ⁻¹' Φᶜ) (q : Q ⟶ N) (ι : Q ⟶ X) (hq : q ≫ g = ι)
    {K : Type} [AddCommGroup K] [Module ℚ K] (L : rationalCohomology X 2 →ₗ[ℚ] K)
    (hL : ∀ a, (rationalCohomologyMap ι 2).hom a = 0 → L a = 0) {s : Type} [Fintype s]
    (β : s → rationalCohomology X 2)
    (hβ : ∀ k, (rationalCohomologyMap (X' := TopCat.of (Φᶜ : Set X))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom (β k) = 0)
    (hli : LinearIndependent ℚ (fun k ↦ L (β k))) :
    (Fintype.card s : Cardinal) ≤
      Module.rank ℚ (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) N D 2) := by
  classical
  have hlift : ∀ k, ∃ γ, (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) X Φ 2).hom γ =
      β k := fun k ↦
    (cohomologyWithSupports.exact_toCohomology_restrictCompl ℚ X Φ 2 (β k)).1 (hβ k)
  choose γ hγ using hlift
  let G := relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) g hg 2
  let δ : s → cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) N D 2 := fun k ↦ G.hom (γ k)
  have key : ∀ x, (rationalCohomologyMap ι 2).hom
      ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) X Φ 2).hom x) =
      (rationalCohomologyMap q 2).hom
        ((cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) N D 2).hom (G.hom x)) := by
    intro x
    rw [← hq, rationalCohomologyMap_comp, ModuleCat.comp_apply]
    congr 1
    exact (congrArg (fun φ ↦ φ.hom x) (relMap_comp_toCohomology g hg g rfl)).symm
  have hinj : Function.Injective (Fintype.linearCombination ℚ δ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearCombination_apply] at hc
    have hβc : ∑ k, c k • β k = (cohomologyWithSupports.toCohomology ℚ (ModuleCat.of ℚ ℚ) X Φ 2).hom
        (∑ k, c k • γ k) := by
      simp only [map_sum, map_smul, hγ]
    have h0 : L (∑ k, c k • β k) = 0 := by
      refine hL _ ?_
      rw [hβc, key]
      have : G.hom (∑ k, c k • γ k) = ∑ k, c k • δ k := by simp only [map_sum, map_smul, δ]
      rw [this, hc, map_zero, map_zero]
    rw [map_sum] at h0
    simp only [map_smul] at h0
    funext k
    exact Fintype.linearIndependent_iff.1 hli c h0 k
  have := LinearMap.rank_le_of_injective _ hinj
  rwa [rank_fun'] at this

/-- **Specializations on a slice stay over one point.** On a slice `M` of an algebraic
exceptional chart, a point `x` lying on `F` and any specialization `x'` of it have the same image
in `X`: that image lies in the finite étale fibre of `C ⟶ B` over `b₀`, which is discrete. -/
private theorem slice_map_eq_of_specializes (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b)
      {M : Scheme.{0}} (sM : M ⟶ Spec (.of ℂ)) (iW : M ⟶ Ch.W.toScheme)
      (b₀ : Spec (.of ℂ) ⟶ Ch.B), iW ≫ Ch.ρ ≫ Ch.φ = sM ≫ b₀ →
      ∀ x : M, (iW ≫ Ch.W.ι).base x ∈ (F.supp : Set Z) → ∀ x' : M, x ⤳ x' →
        (iW ≫ Ch.ρ).base x' = (iW ≫ Ch.ρ).base x := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch M sM iW b₀ hpb x hxF x' hxx'
  haveI := Ch.finite
  haveI := Ch.isClosedImmersion
  -- the image of `x` in `X` lies in `C`
  have hm : (iW ≫ Ch.W.ι ≫ r).base x = Ch.X.ι.base ((iW ≫ Ch.ρ).base x) := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, Ch.hρ]
  have hXT : (iW ≫ Ch.W.ι ≫ r).base x ∈ (Ch.X : Set Y) ∩ T := by
    have hW : (iW ≫ Ch.W.ι).base x ∈ r.base ⁻¹' (Ch.X : Set Y) ∩ (F.supp : Set Z) := by
      refine ⟨?_, hxF⟩
      change (iW ≫ Ch.W.ι ≫ r).base x ∈ (Ch.X : Set Y)
      rw [hm, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [Ch.supp_inter_eq] at hW
    exact hW
  obtain ⟨c, hc⟩ : (iW ≫ Ch.ρ).base x ∈ Set.range Ch.iC.base := by
    have : Ch.X.ι.base ((iW ≫ Ch.ρ).base x) ∈ Ch.X.ι.base '' Set.range Ch.iC.base := by
      rw [Ch.range_iC, ← hm]; exact hXT
    obtain ⟨xX', hxX', he'⟩ := this
    exact Ch.X.ι.isOpenEmbedding.injective he' ▸ hxX'
  -- its specialization stays in `C`
  have hsp : (iW ≫ Ch.ρ).base x ⤳ (iW ≫ Ch.ρ).base x' := hxx'.map (iW ≫ Ch.ρ).continuous
  obtain ⟨c', hc'⟩ : (iW ≫ Ch.ρ).base x' ∈ Set.range Ch.iC.base := by
    have hcl := Ch.iC.isClosedEmbedding.isClosed_range
    exact hsp.mem_closed hcl ⟨c, hc⟩
  have hcc' : c ⤳ c' := by
    rw [← Ch.iC.isClosedEmbedding.isInducing.specializes_iff, hc, hc']
    exact hsp
  -- both lie in the fibre over `b₀`
  have hfib : ∀ z : M, ∀ w : Ch.C, Ch.iC.base w = (iW ≫ Ch.ρ).base z →
      (Ch.iC ≫ Ch.φ).base w = b₀.base (sM.base z) := by
    intro z w hw
    rw [Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, Category.assoc, hpb]
    rfl
  have hb : b₀.base (sM.base x') = b₀.base (sM.base x) :=
    congrArg b₀.base (Subsingleton.elim _ _)
  haveI : LocallyQuasiFinite (Ch.iC ≫ Ch.φ) := instLocallyQuasiFiniteOfIsFinite _
  have hd := (Ch.iC ≫ Ch.φ).isDiscrete_preimage_singleton (b₀.base (sM.base x))
  have := hd.eq_of_specializes hcc' (hfib x c hc) ((hfib x' c' hc').trans hb)
  rw [← hc', ← this, hc]

/-- On a slice through `F_t`, the points over the image of `t` are those of `F_t`. -/
private theorem slice_mem_range_of_map_eq {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {W : Z.Opens} {M : Scheme.{0}} (iW : M ⟶ W.toScheme)
    (j : pointFibre sY r To t ⟶ M) (hj : j ≫ iW ≫ W.ι = pointFibreFst sY r To t)
    (hinj : Function.Injective (iW ≫ W.ι).base) (x : M)
    (hx : (iW ≫ W.ι ≫ r).base x = (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))) :
    x ∈ Set.range j.base := by
  have hmem : (iW ≫ W.ι).base x ∈ Set.range (pointFibreFst sY r To t).base := by
    rw [(isClosedEmbedding_pointFibreFst (r := r) To t).2]
    show r.base ((iW ≫ W.ι).base x) ∈
      ({(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))} : Set Y)
    rw [← Scheme.Hom.comp_apply, Category.assoc, hx]
    rfl
  obtain ⟨p, hp⟩ := hmem
  refine ⟨p, hinj ?_⟩
  rw [← hp, ← hj]
  rfl

/-- The points of `F_t` on a slice lie over the image of `t`. -/
private theorem slice_map_j_eq {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {W : Z.Opens} {M : Scheme.{0}} (iW : M ⟶ W.toScheme)
    (j : pointFibre sY r To t ⟶ M) (hj : j ≫ iW ≫ W.ι = pointFibreFst sY r To t)
    (p : pointFibre sY r To t) :
    (iW ≫ W.ι ≫ r).base (j.base p) = (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)) := by
  have : (pointFibreFst sY r To t).base p ∈ Set.range (pointFibreFst sY r To t).base := ⟨p, rfl⟩
  rw [(isClosedEmbedding_pointFibreFst (r := r) To t).2] at this
  rw [← this, ← hj]
  rfl

/-- An embedding preserves the dimension of every subset. -/
private theorem topologicalKrullDim_image_eq {X₁ X₂ : Type*} [TopologicalSpace X₁]
    [TopologicalSpace X₂] {e : X₁ → X₂} (he : Topology.IsEmbedding e) (A : Set X₁) :
    topologicalKrullDim (e '' A) = topologicalKrullDim A :=
  (IsHomeomorph.topologicalKrullDim_eq _ (he.homeomorphImage A).isHomeomorph).symm

/-- A prime divisor of an integral threefold locally of finite type over `ℂ` is a surface. -/
private theorem topologicalKrullDim_primeDivisor_support_eq_two {M : Scheme.{0}}
    (sM : M ⟶ Spec (.of ℂ)) [IsIntegral M] [LocallyOfFiniteType sM]
    (hM3 : topologicalKrullDim M = ((3 : ℕ) : WithBot ℕ∞)) (P : Mori.PrimeDivisor M) :
    topologicalKrullDim (P.support : Set M) = ((2 : ℕ) : WithBot ℕ∞) := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sM P.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hM3,
    ← AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  generalize topologicalKrullDim (P.support : Set M) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by decide)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe n =>
      have h' : (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((3 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        rw [Nat.cast_add, WithBot.coe_add, Nat.cast_one]; exact h
      have : n + 1 = 3 := Nat.cast_injective (WithBot.coe_injective h')
      have hn : n = 2 := by omega
      subst hn
      rfl

/-- **A slice through `F_t` is not contained in `F`.** If the generic point of the slice lay on
`F`, every point of the slice would lie over the image of `t`, so the slice would be `F_t`,
which has dimension at most two. -/
private theorem slice_genericPoint_notMem (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (hdimF : topologicalKrullDim (pointFibre sY r To t) ≤ ((2 : ℕ) : WithBot ℕ∞))
    (p : pointFibre sY r To t) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b)
      {M : Scheme.{0}} [IsIntegral M] (sM : M ⟶ Spec (.of ℂ)) (iW : M ⟶ Ch.W.toScheme)
      (j : pointFibre sY r To t ⟶ M) [IsClosedImmersion j] (b₀ : Spec (.of ℂ) ⟶ Ch.B),
      iW ≫ Ch.ρ ≫ Ch.φ = sM ≫ b₀ → j ≫ iW ≫ Ch.W.ι = pointFibreFst sY r To t →
      Function.Injective (iW ≫ Ch.W.ι).base →
      topologicalKrullDim M = ((3 : ℕ) : WithBot ℕ∞) →
      (iW ≫ Ch.W.ι).base (genericPoint M) ∉ (F.supp : Set Z) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch M _ sM iW j _ b₀ hpb hj hinj hM3 hF
  have hall : ∀ x : M, x ∈ Set.range j.base := by
    intro x
    have hξ : genericPoint M ⤳ x := (genericPoint_spec M).specializes (Set.mem_univ x)
    have hξp : genericPoint M ⤳ j.base p := (genericPoint_spec M).specializes (Set.mem_univ _)
    have hm : ∀ z : M, (iW ≫ Ch.W.ι ≫ r).base z = Ch.X.ι.base ((iW ≫ Ch.ρ).base z) := by
      intro z
      rw [← Scheme.Hom.comp_apply, Category.assoc, Ch.hρ]
    refine slice_mem_range_of_map_eq To t iW j hj hinj x ?_
    rw [hm, slice_map_eq_of_specializes hM Ch sM iW b₀ hpb _ hF x hξ,
      ← slice_map_eq_of_specializes hM Ch sM iW b₀ hpb _ hF _ hξp, ← hm]
    exact slice_map_j_eq To t iW j hj p
  have hhom : IsHomeomorph j.base :=
    isHomeomorph_iff_isEmbedding_surjective.2 ⟨j.isClosedEmbedding.isEmbedding, hall⟩
  have := IsHomeomorph.topologicalKrullDim_eq _ hhom
  rw [this, hM3] at hdimF
  exact absurd hdimF (by decide)

/-- **Prime divisors of the slice meeting `F_t` along `F` are components of `F_t`.** A prime
divisor `P` of the slice whose generic point lies on `F` and which meets `F_t` lies over the
image of `t`, hence in `F_t`; being a surface it is (the image of) a component of `F_t`. -/
private theorem slice_primeDivisor_support_eq (hM : IsCurvePointExceptionalModel sY r F D)
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (hdimF : topologicalKrullDim (pointFibre sY r To t) ≤ ((2 : ℕ) : WithBot ℕ∞)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b)
      {M : Scheme.{0}} [IsIntegral M] (sM : M ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sM]
      (iW : M ⟶ Ch.W.toScheme) (j : pointFibre sY r To t ⟶ M) [IsClosedImmersion j]
      (b₀ : Spec (.of ℂ) ⟶ Ch.B),
      iW ≫ Ch.ρ ≫ Ch.φ = sM ≫ b₀ → j ≫ iW ≫ Ch.W.ι = pointFibreFst sY r To t →
      Function.Injective (iW ≫ Ch.W.ι).base →
      topologicalKrullDim M = ((3 : ℕ) : WithBot ℕ∞) →
      ∀ P : Mori.PrimeDivisor M, (iW ≫ Ch.W.ι).base P.genericPoint ∈ (F.supp : Set Z) →
        (∃ p, j.base p ∈ (P.support : Set M)) →
        ∃ S : irreducibleComponents (pointFibre sY r To t),
          (P.support : Set M) = j.base '' (S : Set (pointFibre sY r To t)) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch M _ sM _ iW j _ b₀ hpb hj hinj hM3 P hPF ⟨p, hp⟩
  have hsupp := AlgebraicGeometry.PrimeDivisor.support_eq_closure P
  have hm : ∀ z : M, (iW ≫ Ch.W.ι ≫ r).base z = Ch.X.ι.base ((iW ≫ Ch.ρ).base z) := by
    intro z
    rw [← Scheme.Hom.comp_apply, Category.assoc, Ch.hρ]
  have hsub : (P.support : Set M) ⊆ Set.range j.base := by
    intro x hx
    rw [hsupp] at hx hp
    have hξ : P.genericPoint ⤳ x := specializes_iff_mem_closure.2 hx
    have hξp : P.genericPoint ⤳ j.base p := specializes_iff_mem_closure.2 hp
    refine slice_mem_range_of_map_eq To t iW j hj hinj x ?_
    rw [hm, slice_map_eq_of_specializes hM Ch sM iW b₀ hpb _ hPF x hξ,
      ← slice_map_eq_of_specializes hM Ch sM iW b₀ hpb _ hPF _ hξp, ← hm]
    exact slice_map_j_eq To t iW j hj p
  obtain ⟨q, hq⟩ := hsub (show P.genericPoint ∈ (P.support : Set M) by
    rw [hsupp]; exact subset_closure rfl)
  have hPq : (P.support : Set M) = j.base '' closure {q} := by
    rw [hsupp, ← j.isClosedEmbedding.closure_image_eq, Set.image_singleton]
    exact congrArg (fun z ↦ closure ({z} : Set M)) hq.symm
  obtain ⟨S, hS, hqS⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := q)).closure
  refine ⟨⟨S, hS⟩, ?_⟩
  have hle : (P.support : Set M) ⊆ j.base '' S := hPq ▸ Set.image_mono hqS
  by_contra hne
  have hSirr : IsIrreducible (j.base '' S) := hS.1.image _ j.continuous.continuousOn
  have hScl : IsClosed (j.base '' S) :=
    j.isClosedEmbedding.isClosedMap _ (isClosed_of_mem_irreducibleComponents S hS)
  have hdS : topologicalKrullDim (j.base '' S) ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_image_eq j.isClosedEmbedding.isEmbedding]
    exact (topologicalKrullDim_subspace_le _ _).trans hdimF
  have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hSirr
    P.idealSheaf.support.isClosed hle hne (ne_top_of_le_ne_top (by decide) hdS)
  rw [topologicalKrullDim_primeDivisor_support_eq_two sM hM3 P] at hlt
  exact absurd (hlt.trans_le hdS) (lt_irrefl _)

open UnderlyingSpace in
/-- `rank_cohomologyWithSupports_le_one`, read on the complex points `M^an`. -/
private theorem rank_cohomologyWithSupports_le_one' {M : Scheme.{0}} [M.Over (Spec (.of ℂ))]
    [IsComplexScheme M] [IsIntegral M]
    (hqp : IsQuasiProjectiveVariety ℂ (M ↘ Spec (.of ℂ)))
    [SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ))]
    (P : Closeds M) (hP : IsIrreducible (P : Set M))
    (hP2 : topologicalKrullDim (P : Set M) = ((2 : ℕ) : WithBot ℕ∞))
    (hPp : IsProper ((Scheme.IdealSheafData.vanishingIdeal P).subschemeι ≫ (M ↘ Spec (.of ℂ))))
    (U' : Opens (analyticSpace (M ↘ Spec (.of ℂ))))
    (hU' : ∀ x : analyticSpace (M ↘ Spec (.of ℂ)),
      x.hom.base (IsLocalRing.closedPoint ℂ) ∈ (P : Set M) → x ∈ U') :
    Module.rank ℚ (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of U')
      {x : U' | x.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (P : Set M)} 2) ≤ 1 := by
  let e := ComplexPoints.homeomorphUnderlyingSpace (X := M)
  let U : Opens (TopCat.of (UnderlyingSpace ℂ M)) := ⟨e '' U', e.isOpenMap _ U'.isOpen⟩
  have hDU : pointsOver (K := ℂ) (P : Set M) ⊆ U := by
    intro p hp
    refine ⟨e.symm p, hU' _ ?_, e.apply_symm_apply p⟩
    exact hp
  let h : (U' : Set (analyticSpace (M ↘ Spec (.of ℂ)))) ≃ₜ (U : Set (UnderlyingSpace ℂ M)) :=
    e.image (U' : Set (analyticSpace (M ↘ Spec (.of ℂ))))
  have hb := rank_cohomologyWithSupports_le_one hqp P hP hP2 hPp U hDU
  have hiso := (cohomologyWithSupportsHomeomorphIso (X := TopCat.of U') (X' := TopCat.of U) h
    ((borelMooreHomology.inclHom U) ⁻¹' pointsOver (K := ℂ) (P : Set M)) 2).toLinearEquiv.rank_eq
  refine le_of_eq_of_le ?_ (hiso.symm.le.trans hb)
  rfl

/-- **Points of `F_t` on a component of `F` lie on a component of `F_t` in it.** If the fibre
pieces of `E` over `t` are surfaces and `F_t` has dimension at most two, every point of `F_t` on
`E` lies on a component of `F_t` contained in `E`. -/
private theorem exists_component_subset_of_mem {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (hdimF : topologicalKrullDim (pointFibre sY r To t) ≤ ((2 : ℕ) : WithBot ℕ∞))
    (E : Mori.PrimeDivisor Z)
    (h2 : ∀ A : Set Z, Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞))
    (p : pointFibre sY r To t) (hp : (pointFibreFst sY r To t).base p ∈ (E.support : Set Z)) :
    ∃ S' : irreducibleComponents (pointFibre sY r To t), p ∈ (S' : Set (pointFibre sY r To t)) ∧
      (S' : Set (pointFibre sY r To t)) ⊆ (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) := by
  obtain ⟨hemb, hrange⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
  set yY := (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))
  have hQ : IsClosed ((E.support : Set Z) ∩ r.base ⁻¹' {yY}) :=
    E.idealSheaf.support.isClosed.inter ((isClosed_singleton_point To t).preimage r.continuous)
  have hpmem : (pointFibreFst sY r To t).base p ∈ (E.support : Set Z) ∩ r.base ⁻¹' {yY} :=
    ⟨hp, hrange.subset ⟨p, rfl⟩⟩
  obtain ⟨A, hpA, hA⟩ := exists_subset_maximal_of_isIrreducible
    (isIrreducible_singleton (x := (pointFibreFst sY r To t).base p))
    (Set.singleton_subset_iff.2 hpmem)
  have hAcl : IsClosed A := isClosed_of_maximal hQ hA
  have hgen := hA.1.1.isGenericPoint_genericPoint_closure
  rw [hAcl.closure_eq] at hgen
  obtain ⟨a', ha'⟩ : hA.1.1.genericPoint ∈ Set.range (pointFibreFst sY r To t).base := by
    have h := (hA.1.2 hgen.mem).2
    change _ ∈ Set.range ⇑(pointFibreFst sY r To t)
    rw [hrange]
    exact h
  have hAeq : A = (pointFibreFst sY r To t).base '' closure {a'} := by
    rw [← hemb.closure_image_eq, Set.image_singleton, ha', hgen.def]
  obtain ⟨S', hS', hS'a⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := a')).closure
  have hAS : A ⊆ (pointFibreFst sY r To t).base '' S' := hAeq ▸ Set.image_mono hS'a
  have hSirr : IsIrreducible ((pointFibreFst sY r To t).base '' S') :=
    hS'.1.image _ (pointFibreFst sY r To t).continuous.continuousOn
  have hScl : IsClosed ((pointFibreFst sY r To t).base '' S') :=
    hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents S' hS')
  have hdS : topologicalKrullDim ((pointFibreFst sY r To t).base '' S') ≤
      ((2 : ℕ) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_image_eq hemb.isEmbedding]
    exact (topologicalKrullDim_subspace_le _ _).trans hdimF
  have hAS' : A = (pointFibreFst sY r To t).base '' S' := by
    by_contra hne
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hSirr hAcl hAS hne
      (ne_top_of_le_ne_top (by decide) hdS)
    rw [h2 A hA] at hlt
    exact absurd (hlt.trans_le hdS) (lt_irrefl _)
  refine ⟨⟨S', hS'⟩, ?_, fun z hz ↦ ?_⟩
  · have : (pointFibreFst sY r To t).base p ∈ (pointFibreFst sY r To t).base '' S' :=
      hAS' ▸ hpA rfl
    obtain ⟨p', hp', he⟩ := this
    exact hemb.injective he ▸ hp'
  · exact (hA.1.2 (hAS'.symm ▸ Set.mem_image_of_mem _ hz : _ ∈ A)).1

/-- **Components of `F_t` in one exceptional component are disjoint**, when the fibre pieces of
that component over `t` are. -/
private theorem disjoint_of_subset_preimage {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (E : Mori.PrimeDivisor Z)
    (hdisj : ∀ A B : Set Z,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) B → A ≠ B → Disjoint A B)
    (S S' : irreducibleComponents (pointFibre sY r To t))
    (hS : (S : Set (pointFibre sY r To t)) ⊆ (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z))
    (hS' : (S' : Set (pointFibre sY r To t)) ⊆
      (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z))
    (hne : S ≠ S') : Disjoint (S : Set (pointFibre sY r To t)) S' := by
  obtain ⟨hemb, -⟩ := isClosedEmbedding_pointFibreFst (r := r) To t
  have hA := maximal_image_pointFibreFst (r := r) To t S E hS
  have hB := maximal_image_pointFibreFst (r := r) To t S' E hS'
  have hAB : (pointFibreFst sY r To t).base '' S ≠ (pointFibreFst sY r To t).base '' S' :=
    fun h ↦ hne (Subtype.ext ((Set.image_injective.2 hemb.injective) h))
  exact (Set.disjoint_image_iff hemb.injective).1 (hdisj _ _ hA hB hAB)

/-- The ideal sheaf of a quasi-compact morphism from a reduced scheme is the vanishing ideal of
the closure of its image. -/
private theorem ker_eq_vanishingIdeal' {X₁ X₂ : Scheme.{0}} (f : X₂ ⟶ X₁) [IsReduced X₂]
    [QuasiCompact f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
      (Set.range f)) := by
  rw [← Set.image_univ, ← Scheme.IdealSheafData.map_bot]
  have := Scheme.IdealSheafData.map_vanishingIdeal f ⊤
  rwa [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot] at this

/-- **On a slice, a local class is a multiple of the class of its surface.** Let `M` be a
slice threefold through `F_t` and `α` a local class of `E` along a component `S` of `F_t`. On `F_t`
the class `α` restricts to `a · c₁(𝒪_M(P))`, for `P` the prime divisor `S` of `M` and `a` the
multiplicity of `P` in `E|_M`, provided `α` does not vanish on some family of points of `S`. On a
tube of the slice both classes vanish off `S` and agree off the other components of `E` along
`F_t`, where `E|_M = a P`; supported cohomology along `S` is a line, so they agree. -/
private theorem fibreRestriction_localClass_eq
    (hM : IsCurvePointExceptionalModel sY r F D) [IsComplexScheme Z] {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (hdimF : topologicalKrullDim (pointFibre sY r To t) ≤ ((2 : ℕ) : WithBot ℕ∞))
    (hdisj : ∀ E : F.support, ∀ A B : Set Z,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) B → A ≠ B → Disjoint A B)
    (h2 : ∀ E : F.support, ∀ A : Set Z,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b)
      {M : Scheme.{0}} [M.Over (Spec (.of ℂ))] [IsComplexScheme M]
      [IsIntegral M] [SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ))]
      [CompactSpace M] [IsLocallyNoetherian M] [IsNormal M]
      (_hqp : IsQuasiProjectiveVariety ℂ (M ↘ Spec (.of ℂ))) (iW : M ⟶ Ch.W.toScheme)
      [IsClosedImmersion iW] (j : pointFibre sY r To t ⟶ M) [IsClosedImmersion j]
      (b₀ : Spec (.of ℂ) ⟶ Ch.B),
      iW ≫ Ch.W.ι ≫ r ≫ sY = M ↘ Spec (.of ℂ) → j ≫ iW ≫ Ch.W.ι = pointFibreFst sY r To t →
      iW ≫ Ch.ρ ≫ Ch.φ = (M ↘ Spec (.of ℂ)) ≫ b₀ →
      ∀ (hjs : j ≫ M ↘ Spec (.of ℂ) = pointFibre sY r To t ↘ Spec (.of ℂ))
        (V₀ : Opens (analyticSpace sY)), curveOpenInclusion sY To t ∈ V₀ →
      (∀ x : ComplexPoints (M ↘ Spec (.of ℂ)),
          (x.hom ≫ iW ≫ Ch.W.ι ≫ r).base (IsLocalRing.closedPoint ℂ) ∈
            (ComplexPoints.toScheme '' (V₀ : Set (analyticSpace sY)) : Set Y) →
          (x.hom ≫ iW ≫ Ch.W.ι).base (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z) →
          x.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range j.base) →
      ∀ (hcartM : ∀ B : Divisor M, B.IsCartier)
        (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z),
        E ∈ F.support → ∀ {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
        IsLocalClass hM To t S E hV α →
        ∀ (P : Mori.PrimeDivisor M),
          (P.support : Set M) = j.base '' (S : Set (pointFibre sY r To t)) →
        ∀ (hEc : Divisor.IsCartier (Finsupp.single E (1 : ℤ)))
          (hB : ∀ Zc : irreducibleComponents M, (iW ≫ Ch.W.ι) (componentGenericPoint M Zc) ∉
            DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ))),
        (∃ (Xt : TopCat.{0}) (f : Xt ⟶ analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ))),
          (∀ z, (f z).hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t))) ∧
          (rationalCohomologyMap (f ≫ pointFibreInclusion sY r To t hV) 2).hom α ≠ 0) →
        (rationalCohomologyMap (pointFibreInclusion sY r To t hV) 2).hom α =
          ((Divisor.pullback (f := iW ≫ Ch.W.ι) (Finsupp.single E (1 : ℤ)) hEc hB).coeff P : ℚ) •
            (rationalCohomologyMap (analyticMap j hjs) 2).hom
              (rationalChernHom hcartM (Finsupp.single P 1)) := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch M _ _ _ _ _ _ _ hqp iW _ j _ b₀ hcomp hj hpb hjs V₀ hyV₀ hsep hcartM S E hE V hV
    α hloc P hPS hEc hB hnz
  haveI : IsSeparated (M ↘ Spec (.of ℂ)) := hqp.toIsSeparated
  classical
  haveI : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI : LocallyOfFiniteType sY := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType (f := sY)
  set pt := IsLocalRing.closedPoint ℂ with hpt0
  have hcp : pt = (default : Spec (.of ℂ)) := Subsingleton.elim _ _
  set y := curveOpenInclusion sY To t with hy
  set iM := iW ≫ Ch.W.ι with hiMdef
  have hinj : Function.Injective iM.base := fun a a' h ↦
    iW.isClosedEmbedding.injective (Ch.W.ι.isOpenEmbedding.injective h)
  have hgM : iM ≫ r ≫ sY = M ↘ Spec (.of ℂ) := by rw [hiMdef, Category.assoc]; exact hcomp
  let gM : analyticSpace (M ↘ Spec (.of ℂ)) ⟶ analyticSpace (r ≫ sY) := analyticMap iM hgM
  have hpt : ∀ y', gM (analyticMap j hjs y') = pointFibreAnalyticMap sY r To t y' := fun y' ↦
    ComplexPoints.ext (by
      change (y'.hom ≫ j) ≫ iW ≫ Ch.W.ι = y'.hom ≫ pointFibreFst sY r To t
      rw [Category.assoc, hj])
  let Vt : Opens (analyticSpace sY) := V ⊓ V₀
  have hyVt : y ∈ Vt := ⟨hV, hyV₀⟩
  let U' : Opens (analyticSpace (M ↘ Spec (.of ℂ))) :=
    ⟨gM ⁻¹' (resolutionAnalyticMap sY r ⁻¹' (Vt : Set (analyticSpace sY))),
      (Vt.isOpen.preimage (resolutionAnalyticMap sY r).hom.continuous).preimage
        gM.hom.continuous⟩
  let g : TopCat.of U' ⟶ preimageSpace (resolutionAnalyticMap sY r) V :=
    TopCat.ofHom ⟨fun x ↦ ⟨gM x.1, x.2.1⟩,
      (gM.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let incl : TopCat.of U' ⟶ analyticSpace (M ↘ Spec (.of ℂ)) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hmemq : ∀ y', analyticMap j hjs y' ∈ U' := by
    intro y'
    change resolutionAnalyticMap sY r (gM (analyticMap j hjs y')) ∈ Vt
    rw [hpt, resolutionAnalyticMap_pointFibreAnalyticMap]
    exact hyVt
  let q : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)) ⟶ TopCat.of U' :=
    TopCat.ofHom ⟨fun y' ↦ ⟨analyticMap j hjs y', hmemq y'⟩,
      ((analyticMap j hjs).hom.continuous).subtype_mk hmemq⟩
  have hq : q ≫ g = pointFibreInclusion sY r To t hV :=
    TopCat.ext fun y' ↦ Subtype.ext (hpt y')
  have hqi : q ≫ incl = analyticMap j hjs := TopCat.ext fun y' ↦ rfl
  -- points of the tube of the slice on `F` lie on `F_t` and come from `F_t(ℂ)`
  have hFt : ∀ x : U', iM.base (x.1.hom.base pt) ∈ (F.supp : Set Z) →
      x.1.hom.base pt ∈ Set.range j.base := by
    intro x hx
    refine hsep x.1 ⟨resolutionAnalyticMap sY r (gM x.1), x.2.2, ?_⟩ hx
    unfold ComplexPoints.toScheme
    rw [hcp]
    change ((x.1.hom ≫ iW ≫ Ch.W.ι) ≫ r).base default = _
    simp only [Category.assoc]
  have hlift : ∀ x : U', x.1.hom.base pt ∈ Set.range j.base → ∃ y', q y' = x := by
    rintro x ⟨p, hp⟩
    have hstrZ : (x.1.hom ≫ iM) ≫ r ≫ sY = 𝟙 _ := by
      rw [Category.assoc, hgM]; exact x.1.hom_comp_structure
    have hz : resolutionAnalyticMap sY r ⟨x.1.hom ≫ iM, hstrZ⟩ = y := by
      refine complexPoints_ext_of_base (sX := sY) ?_
      change ((x.1.hom ≫ iM) ≫ r).base pt = (t.hom ≫ To.ι ≫ curveι T).base pt
      have h1 : ((x.1.hom ≫ iM) ≫ r).base pt = (iW ≫ Ch.W.ι ≫ r).base (j.base p) := by
        rw [hp]; rfl
      rw [h1, slice_map_j_eq To t iW j hj p, hcp]
    obtain ⟨y', hy'⟩ := exists_pointFibreInclusion_eq To t (V := ⊤) trivial
      ⟨⟨x.1.hom ≫ iM, hstrZ⟩, trivial⟩ hz
    have hy'h : y'.hom ≫ pointFibreFst sY r To t = x.1.hom ≫ iM :=
      congrArg (fun w : preimageSpace (resolutionAnalyticMap sY r) ⊤ ↦ w.1.hom) hy'
    refine ⟨y', Subtype.ext (ComplexPoints.ext ?_)⟩
    change y'.hom ≫ j = x.1.hom
    rw [← cancel_mono iM, Category.assoc]
    change y'.hom ≫ j ≫ iW ≫ Ch.W.ι = _
    rw [hj, hy'h]
  obtain ⟨G, hG, ⟨O, hO, hGO⟩, hfib, h0, hinv, h1⟩ := hloc.properties
  have hSE := subset_preimage_of_isLocalClass hM hloc
  let Sset : Set (TopCat.of U') :=
    {x | x.1.hom.base pt ∈ j.base '' (S : Set (pointFibre sY r To t))}
  let compsK : Set (pointFibre sY r To t) :=
    ⋃ (S' : irreducibleComponents (pointFibre sY r To t))
      (_ : S' ≠ S ∧ (S' : Set (pointFibre sY r To t)) ⊆
        (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z)), (S' : Set _)
  let Kset : Set (TopCat.of U') := {x | x.1.hom.base pt ∈ j.base '' compsK}
  set EM := Divisor.pullback (f := iM) (Finsupp.single E (1 : ℤ)) hEc hB with hEM
  have hgq : ∀ y', g (q y') = pointFibreInclusion sY r To t hV y' := fun y' ↦
    Subtype.ext (hpt y')
  have hFE : ∀ x : TopCat.of U', (g x).1.hom.base pt ∈ (E.support : Set Z) →
      iM.base (x.1.hom.base pt) ∈ (F.supp : Set Z) := by
    intro x hx
    rw [DivisorWithCoeffs.coe_supp]
    exact Set.mem_iUnion₂.2 ⟨E, hE, hx⟩
  -- Claim A: off `S`, the tube of the slice maps off the piece `G`
  have hAS : ∀ x : TopCat.of U', x ∉ Sset → g x ∉ G := by
    intro x hx hxG
    have hxE : (g x).1.hom.base pt ∈ (E.support : Set Z) := by
      rw [hGO] at hxG; exact hxG.2
    obtain ⟨y', rfl⟩ := hlift x (hFt x (hFE x hxE))
    rw [hgq] at hxG
    exact hx ⟨_, (hfib y').1 hxG, rfl⟩
  -- Claim B: off the other components, it maps off the rest of `E`
  have hBK : ∀ x : TopCat.of U', x ∉ Kset →
      g x ∉ {z : preimageSpace (resolutionAnalyticMap sY r) V |
        z.1.hom.base pt ∈ (E.support : Set Z)} \ G := by
    rintro x hx ⟨hxE, hxG⟩
    obtain ⟨y', rfl⟩ := hlift x (hFt x (hFE x hxE))
    rw [hgq] at hxE hxG
    have hnS : y'.hom.base pt ∉ (S : Set (pointFibre sY r To t)) := fun h ↦ hxG ((hfib y').2 h)
    obtain ⟨S', hpS', hS'E⟩ := exists_component_subset_of_mem To t hdimF E (h2 ⟨E, hE⟩) _ hxE
    have hS'S : S' ≠ S := fun h ↦ hnS (h ▸ hpS')
    exact hx ⟨y'.hom.base pt, Set.mem_iUnion₂.2 ⟨S', ⟨hS'S, hS'E⟩, hpS'⟩, rfl⟩
  let α' := (rationalCohomologyMap g 2).hom α
  let β' := ((EM.coeff P : ℤ) : ℚ) • (rationalCohomologyMap incl 2).hom
    (rationalChernHom hcartM (Finsupp.single P 1))
  have hα0 : (rationalCohomologyMap (X' := TopCat.of (Ssetᶜ : Set (TopCat.of U')))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α' = 0 := by
    let m : TopCat.of (Ssetᶜ : Set (TopCat.of U')) ⟶ TopCat.of (Gᶜ : Set _) :=
      TopCat.ofHom ⟨fun x ↦ ⟨g x.1, hAS x.1 x.2⟩,
        (g.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hfac : (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of (Ssetᶜ : Set (TopCat.of U')) ⟶ _) ≫ g =
        m ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := rfl
    change (rationalCohomologyMap _ 2).hom ((rationalCohomologyMap g 2).hom α) = 0
    rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hfac, rationalCohomologyMap_comp,
      ModuleCat.comp_apply, h0, map_zero]
  have hβ0 : (rationalCohomologyMap (X' := TopCat.of (Ssetᶜ : Set (TopCat.of U')))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom β' = 0 := by
    haveI := (hcartM (Finsupp.single P 1)).isInvertibleModule_divisorialSheaf
    change (rationalCohomologyMap _ 2).hom (_ • (rationalCohomologyMap incl 2).hom _) = 0
    rw [map_smul, ← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, rationalChernHom_apply,
      rationalCohomologyMap_firstChernClass_eq_zero (Z := M) P, smul_zero]
    intro x hx
    rw [hPS] at hx
    exact x.2 hx
  have hαβ : (rationalCohomologyMap (X' := TopCat.of (Ksetᶜ : Set (TopCat.of U')))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α' =
      (rationalCohomologyMap (X' := TopCat.of (Ksetᶜ : Set (TopCat.of U')))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom β' := by
    haveI := isInvertible_divisorialSheaf_single hM E
    have hM3 : topologicalKrullDim M = ((3 : ℕ) : WithBot ℕ∞) :=
      (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M 3).symm
    haveI : LocallyOfFiniteType (r ≫ sY) := hM.isResolution.2.1.toLocallyOfFiniteType
    have hEeff : Stacks.Divisors.IsEffectiveCartierDivisor E.idealSheaf :=
      MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf (r ≫ sY) hM.isResolution.2.2.1 E
    let valK : TopCat.of (Ksetᶜ : Set (TopCat.of U')) ⟶ TopCat.of U' :=
      TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    -- the other prime divisors of `E|_M` miss the complement of the other components
    have hPvan : ∀ P' ∈ EM.support, P' ≠ P →
        (rationalCohomologyMap (valK ≫ incl) 2).hom
          (rationalChernHom hcartM (Finsupp.single P' 1)) = 0 := by
      intro P' hP' hne
      haveI := (hcartM (Finsupp.single P' 1)).isInvertibleModule_divisorialSheaf
      rw [rationalChernHom_apply]
      refine rationalCohomologyMap_firstChernClass_eq_zero (Z := M) P' _ fun x hxP' ↦ ?_
      have hcoef : EM.coeff P' ≠ 0 := Finsupp.mem_support_iff.1 hP'
      have hgen : iM.base P'.genericPoint ∈ (E.support : Set Z) := by
        by_contra h
        exact hcoef (coeff_pullback_single_eq_zero iM E hEeff hEc hB P' h)
      have hsub : (P'.support : Set M) ⊆ iM.base ⁻¹' (E.support : Set Z) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact closure_minimal (Set.singleton_subset_iff.2 hgen)
          (E.idealSheaf.support.isClosed.preimage iM.continuous)
      have hxE := hsub hxP'
      have hxF : iM.base (x.1.1.hom.base pt) ∈ (F.supp : Set Z) := by
        rw [DivisorWithCoeffs.coe_supp]
        exact Set.mem_iUnion₂.2 ⟨E, hE, hxE⟩
      obtain ⟨p, hp⟩ := hFt x.1 hxF
      have hgenF : iM.base P'.genericPoint ∈ (F.supp : Set Z) := by
        rw [DivisorWithCoeffs.coe_supp]
        exact Set.mem_iUnion₂.2 ⟨E, hE, hgen⟩
      obtain ⟨S'', hS''⟩ := slice_primeDivisor_support_eq hM To t hdimF Ch (M ↘ Spec (.of ℂ))
        iW j b₀ hpb hj hinj hM3 P' hgenF ⟨p, hp ▸ hxP'⟩
      have hS''E : (S'' : Set (pointFibre sY r To t)) ⊆
          (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) := by
        intro z hz
        have : j.base z ∈ (P'.support : Set M) := hS''.symm ▸ Set.mem_image_of_mem _ hz
        have h' := hsub this
        rw [Set.mem_preimage, ← hj]
        exact h'
      have hS''S : S'' ≠ S := by
        rintro rfl
        exact hne (primeDivisor_eq_of_support_eq (hS''.trans hPS.symm))
      apply x.2
      rw [hS''] at hxP'
      obtain ⟨z, hz, hzx⟩ := hxP'
      exact ⟨z, Set.mem_iUnion₂.2 ⟨S'', ⟨hS''S, hS''E⟩, hz⟩, hzx⟩
    -- `c₁(𝒪_M(E|_M))` is `a · c₁(𝒪_M(P))` off the other components
    have hdecomp : rationalChernHom hcartM EM =
        ∑ P' ∈ EM.support, EM P' • rationalChernHom hcartM (Finsupp.single P' 1) := by
      conv_lhs => rw [← Finsupp.sum_single EM]
      rw [Finsupp.sum, map_sum]
      refine Finset.sum_congr rfl fun P' _ ↦ ?_
      rw [← Finsupp.smul_single_one, map_zsmul]
    have hC : (rationalCohomologyMap (valK ≫ incl) 2).hom (rationalChernHom hcartM EM) =
        ((EM.coeff P : ℤ) : ℚ) • (rationalCohomologyMap (valK ≫ incl) 2).hom
          (rationalChernHom hcartM (Finsupp.single P 1)) := by
      rw [hdecomp, map_sum]
      simp only [map_zsmul]
      rw [Finset.sum_eq_single P (fun P' hP' hne ↦ by rw [hPvan P' hP' hne, smul_zero])
        (fun hP ↦ by rw [Finsupp.notMem_support_iff.1 hP, zero_smul]),
        ← Int.cast_smul_eq_zsmul ℚ]
      rfl
    -- `α` is `c₁(𝒪_Z(E))` off the other components
    have hiMZ : iM ≫ Z ↘ Spec (.of ℂ) = M ↘ Spec (.of ℂ) := by rw [← hM.comp_eq]; exact hgM
    obtain ⟨e⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso hEc iM hB
    have hchain : (rationalCohomologyMap (analyticMap iM hiMZ) 2).hom
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
          (algebraicFirstChernClass (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)))) =
        rationalChernHom hcartM EM := by
      haveI := (hcartM EM).isInvertibleModule_divisorialSheaf
      rw [rationalChernHom_apply, rationalCohomologyMap_mapCoeff,
        algebraicFirstChernClass_eq_of_iso e,
        algebraicFirstChernClass_pullback iM (analyticMap iM hiMZ) (fun _ ↦ rfl)]
      rfl
    let mK : TopCat.of (Ksetᶜ : Set (TopCat.of U')) ⟶
        TopCat.of (({z : preimageSpace (resolutionAnalyticMap sY r) V |
          z.1.hom.base pt ∈ (E.support : Set Z)} \ G)ᶜ :
            Set (preimageSpace (resolutionAnalyticMap sY r) V)) :=
      TopCat.ofHom ⟨fun x ↦ ⟨g x.1, hBK x.1 x.2⟩,
        (g.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hfacK : valK ≫ g = mK ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := rfl
    have hmaps : mK ≫ (TopCat.ofHom (X := TopCat.of (({z : preimageSpace
        (resolutionAnalyticMap sY r) V | z.1.hom.base pt ∈ (E.support : Set Z)} \ G)ᶜ :
          Set (preimageSpace (resolutionAnalyticMap sY r) V))) (Y := analyticSpace (r ≫ sY))
        ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
        analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) =
        valK ≫ incl ≫ analyticMap iM hiMZ :=
      TopCat.ext fun x ↦ ComplexPoints.ext (Category.comp_id _)
    have hL : (rationalCohomologyMap valK 2).hom ((rationalCohomologyMap g 2).hom α) =
        (rationalCohomologyMap (valK ≫ incl) 2).hom (rationalChernHom hcartM EM) := by
      calc (rationalCohomologyMap valK 2).hom ((rationalCohomologyMap g 2).hom α)
          = (rationalCohomologyMap (valK ≫ g) 2).hom α := by
            rw [rationalCohomologyMap_comp]; rfl
        _ = (rationalCohomologyMap (mK ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom
            α := by rw [hfacK]
        _ = (rationalCohomologyMap mK 2).hom ((rationalCohomologyMap
              (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α) := by
            rw [rationalCohomologyMap_comp]; rfl
        _ = (rationalCohomologyMap mK 2).hom ((rationalCohomologyMap (TopCat.ofHom (X :=
              TopCat.of (({z : preimageSpace (resolutionAnalyticMap sY r) V |
                z.1.hom.base pt ∈ (E.support : Set Z)} \ G)ᶜ :
                  Set (preimageSpace (resolutionAnalyticMap sY r) V)))
              (Y := analyticSpace (r ≫ sY))
              ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
              analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) 2).hom
                (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
                  (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))))) := by
            rw [h1]
        _ = (rationalCohomologyMap ((valK ≫ incl) ≫ analyticMap iM hiMZ) 2).hom
              (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass
                (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)))) := by
            rw [Category.assoc, ← hmaps, rationalCohomologyMap_comp mK]; rfl
        _ = (rationalCohomologyMap (valK ≫ incl) 2).hom (rationalChernHom hcartM EM) := by
            rw [rationalCohomologyMap_comp (valK ≫ incl), ModuleCat.comp_apply, hchain]
    change (rationalCohomologyMap valK 2).hom ((rationalCohomologyMap g 2).hom α) =
      (rationalCohomologyMap valK 2).hom (_ • (rationalCohomologyMap incl 2).hom _)
    rw [hL, hC, map_smul, rationalCohomologyMap_comp valK incl]
    rfl
  have hne : (rationalCohomologyMap (X' := TopCat.of (Ksetᶜ : Set (TopCat.of U')))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α' ≠ 0 := by
    obtain ⟨Xt, f, hfS, hfne⟩ := hnz
    have hnotK : ∀ z, q (f z) ∉ Kset := by
      intro z hz
      obtain ⟨w, hw, hwz⟩ := hz
      have hw' : w = (f z).hom.base pt := j.isClosedEmbedding.injective hwz
      obtain ⟨S', ⟨hS'S, hS'E⟩, hwS'⟩ := Set.mem_iUnion₂.1 hw
      have hd := disjoint_of_subset_preimage To t E (hdisj ⟨E, hE⟩) S S' hSE hS'E (Ne.symm hS'S)
      exact Set.disjoint_left.1 hd (hfS z) (hw' ▸ hwS')
    let f' : Xt ⟶ TopCat.of (Ksetᶜ : Set (TopCat.of U')) :=
      TopCat.ofHom ⟨fun z ↦ ⟨q (f z), hnotK z⟩,
        (q.hom.continuous.comp f.hom.continuous).subtype_mk _⟩
    have hff : f' ≫ (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ ≫ g) =
        f ≫ pointFibreInclusion sY r To t hV := TopCat.ext fun z ↦ hgq (f z)
    intro h0'
    apply hfne
    rw [← hff, rationalCohomologyMap_comp, rationalCohomologyMap_comp, ModuleCat.comp_apply,
      ModuleCat.comp_apply]
    change (rationalCohomologyMap f' 2).hom ((rationalCohomologyMap
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α') = 0
    rw [h0', map_zero]
  have hrank : Module.rank ℚ (cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of U') Sset 2)
      ≤ 1 := by
    have hScl : IsClosed (j.base '' (S : Set (pointFibre sY r To t))) :=
      j.isClosedEmbedding.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ S.2)
    let Pc : Closeds M := ⟨j.base '' (S : Set (pointFibre sY r To t)), hScl⟩
    have hirr : IsIrreducible (Pc : Set M) := S.2.1.image _ j.continuous.continuousOn
    have hd2 : topologicalKrullDim (Pc : Set M) = ((2 : ℕ) : WithBot ℕ∞) := by
      change topologicalKrullDim (j.base '' (S : Set (pointFibre sY r To t))) = _
      rw [topologicalKrullDim_image_eq j.isClosedEmbedding.isEmbedding,
        ← topologicalKrullDim_image_eq (isClosedEmbedding_pointFibreFst (r := r) To t).1.isEmbedding]
      exact h2 ⟨E, hE⟩ _ (maximal_image_pointFibreFst (r := r) To t S E hSE)
    have hPp : IsProper ((Scheme.IdealSheafData.vanishingIdeal Pc).subschemeι ≫
        (M ↘ Spec (.of ℂ))) := by
      let QS := Scheme.IdealSheafData.vanishingIdeal
        (⟨S, isClosed_of_mem_irreducibleComponents _ S.2⟩ : Closeds (pointFibre sY r To t))
      let φ := QS.subschemeι ≫ j
      have hrφ : Set.range φ.base = (Pc : Set M) := by
        change Set.range (QS.subschemeι ≫ j).base = j.base '' (S : Set _)
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
          Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
        rfl
      have hker : (Scheme.IdealSheafData.vanishingIdeal Pc).subschemeι.ker = φ.ker := by
        rw [ker_eq_vanishingIdeal', ker_eq_vanishingIdeal', hrφ,
          Scheme.IdealSheafData.range_subschemeι,
          Scheme.IdealSheafData.coe_support_vanishingIdeal]
      haveI := IsClosedImmersion.isIso_lift φ _ hker.symm
      have he : IsClosedImmersion.lift φ _ hker.symm.le ≫ φ =
          (Scheme.IdealSheafData.vanishingIdeal Pc).subschemeι :=
        IsClosedImmersion.lift_fac φ _ hker.symm.le
      haveI : IsProper (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
        haveI := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
        change IsProper (pullback.snd r (t.hom ≫ To.ι ≫ curveι T))
        infer_instance
      rw [← he, Category.assoc, Category.assoc, hjs]
      infer_instance
    have hU'' : ∀ x : analyticSpace (M ↘ Spec (.of ℂ)),
        x.hom.base pt ∈ (Pc : Set M) → x ∈ U' := by
      rintro x ⟨p, -, hp⟩
      change resolutionAnalyticMap sY r (gM x) ∈ Vt
      have hx : resolutionAnalyticMap sY r (gM x) = y := by
        refine complexPoints_ext_of_base (sX := sY) ?_
        change ((x.hom ≫ iM) ≫ r).base pt = (t.hom ≫ To.ι ≫ curveι T).base pt
        have h1 : ((x.hom ≫ iM) ≫ r).base pt = (iW ≫ Ch.W.ι ≫ r).base (j.base p) := by
          rw [hp]; rfl
        rw [h1, slice_map_j_eq To t iW j hj p, hcp]
      rw [hx]
      exact hyVt
    exact rank_cohomologyWithSupports_le_one' hqp Pc hirr hd2 hPp U' hU''
  have heq := eq_of_rationalCohomologyMap_eq_of_rank_le_one hrank hα0 hβ0 hαβ hne
  have h1' := congrArg (rationalCohomologyMap q 2).hom heq
  simp only [α', β', ← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, map_smul] at h1'
  rw [hq, hqi] at h1'
  exact h1'

/-- **Germ relations restrict to fibre relations.** A linear relation among the germs of
classes on tubes holds among their restrictions to `F_t(ℂ)`: on a smaller common tube the
combination vanishes, and the fibre lies in every tube. -/
private theorem sum_smul_pointFibreInclusion_eq_zero {T : IrreducibleCloseds Y}
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {ι : Type*}
    [Fintype ι] (V : ι → Opens (analyticSpace sY)) (hV : ∀ i, curveOpenInclusion sY To t ∈ V i)
    (α : ∀ i, rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) (V i)) 2)
    (l : ι → ℚ) (h : ∑ i, l i • classGerm sY r To t (hV i) (α i) = 0) :
    ∑ i, l i • (rationalCohomologyMap (pointFibreInclusion sY r To t (hV i)) 2).hom (α i) = 0 := by
  classical
  let Vs : Opens (analyticSpace sY) := (Finset.univ : Finset ι).inf V
  have hyVs : curveOpenInclusion sY To t ∈ Vs := by
    change curveOpenInclusion sY To t ∈ ((Finset.univ.inf V : Opens _) : Set _)
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    simp only [Function.comp_apply, Set.iInf_eq_iInter, Set.mem_iInter]
    exact fun i _ ↦ hV i
  have hle : ∀ i, Vs ≤ V i := fun i ↦ Finset.inf_le (Finset.mem_univ i)
  let β : ι → rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) Vs) 2 := fun i ↦
    (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) (hle i)) 2).hom (α i)
  have hβ : classGerm sY r To t hyVs (∑ i, l i • β i) = 0 := by
    simp only [classGerm, map_sum, map_smul]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    exact (classGerm_restrict sY r To t (hle i) hyVs (α i)).symm
  obtain ⟨V'', hV'', hle'', h0⟩ := exists_le_eq_zero_of_classGerm_eq_zero To t hyVs _ hβ
  have hfac : ∀ i, pointFibreInclusion sY r To t hV'' ≫
      preimageInclusion (resolutionAnalyticMap sY r) hle'' ≫
        preimageInclusion (resolutionAnalyticMap sY r) (hle i) =
      pointFibreInclusion sY r To t (hV i) := fun i ↦ rfl
  calc ∑ i, l i • (rationalCohomologyMap (pointFibreInclusion sY r To t (hV i)) 2).hom (α i)
      = ∑ i, l i • (rationalCohomologyMap (pointFibreInclusion sY r To t hV'') 2).hom
          ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) hle'') 2).hom
            (β i)) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [← hfac i, rationalCohomologyMap_comp, rationalCohomologyMap_comp]
        rfl
    _ = (rationalCohomologyMap (pointFibreInclusion sY r To t hV'') 2).hom
          ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) hle'') 2).hom
            (∑ i, l i • β i)) := by
        simp only [map_sum, map_smul]
    _ = 0 := by rw [h0, map_zero]

/-- **`D` is negative on contracted test curves.** For a finite morphism `ν : Γ ⟶ Z` from a
proper complex curve into a fibre of `r`, `deg_ν 𝒪_Z(D) < 0`, since `-D` is `r`-ample. -/
private theorem degreeOnHom_neg (hM : IsCurvePointExceptionalModel sY r F D)
    (hcartZ : ∀ B : Divisor Z, B.IsCartier) [QuasiCompact (Z ↘ Spec (.of ℂ))]
    {Γ : Scheme.{0}} [Γ.Over (Spec (.of ℂ))] [IsIntegral Γ] [IsProper (Γ ↘ Spec (.of ℂ))]
    (hdim1 : topologicalKrullDim Γ = 1) (ν : Γ ⟶ Z) [IsFinite ν]
    (hν : ν ≫ Z ↘ Spec (.of ℂ) = Γ ↘ Spec (.of ℂ)) {y : Y} (hcon : ∀ c, r (ν c) = y) :
    haveI : IsProper (ν ≫ Z ↘ Spec (.of ℂ)) := by rw [hν]; infer_instance
    degreeOnHom hcartZ ν hdim1.le D < 0 := by
  haveI : IsProper (ν ≫ Z ↘ Spec (.of ℂ)) := by rw [hν]; infer_instance
  haveI : AlgebraicGeometry.IsCurve ℂ (ν ≫ Z ↘ Spec (.of ℂ)) := by
    rw [hν]
    exact { toIsIntegral := inferInstance
            toIsSeparated := inferInstance
            toLocallyOfFiniteType := inferInstance
            toQuasiCompact := inferInstance
            topologicalKrullDim_eq_one := hdim1 }
  obtain ⟨hnegC, hamp⟩ := hM.isRelativelyAmple_neg
  haveI := hnegC.isInvertibleModule_divisorialSheaf
  have hpos := degreeOn_pos_of_isRelativelyAmple_of_isFinite (sX := Z ↘ Spec (.of ℂ)) r _ hamp ν
    hdim1.le hcon
  have : degreeOnHom hcartZ ν hdim1.le (-D) = -degreeOnHom hcartZ ν hdim1.le D := map_neg _ _
  have h' : 0 < degreeOnHom hcartZ ν hdim1.le (-D) := hpos
  omega

/-- **The exceptional component through a test curve is negative on it.** Let `ν : Γ ⟶ Z` be a
finite morphism from a proper complex curve into a fibre of `r`, meeting the complement of every
component of `F` but `E₀`. Then `deg_ν 𝒪_Z(E₀) < 0`: the components of `F` other than `E₀` are
nonnegative on `ν`, while `D = ∑ mᵢ Fᵢ` is negative on it, `-D` being `r`-ample. -/
private theorem degreeOn_single_neg (hM : IsCurvePointExceptionalModel sY r F D)
    (hcartZ : ∀ B : Divisor Z, B.IsCartier) [QuasiCompact (Z ↘ Spec (.of ℂ))]
    {Γ : Scheme.{0}} [Γ.Over (Spec (.of ℂ))] [IsIntegral Γ] [IsProper (Γ ↘ Spec (.of ℂ))]
    (hdim1 : topologicalKrullDim Γ = 1) (ν : Γ ⟶ Z) [IsFinite ν]
    (hν : ν ≫ Z ↘ Spec (.of ℂ) = Γ ↘ Spec (.of ℂ)) {y : Y} (hcon : ∀ c, r (ν c) = y)
    {E₀ : Mori.PrimeDivisor Z} (hE₀ : E₀ ∈ F.support)
    (hoff : ∀ E' ∈ F.support, E' ≠ E₀ → ∃ c, ν c ∉ (E'.support : Set Z)) :
    haveI : IsProper (ν ≫ Z ↘ Spec (.of ℂ)) := by rw [hν]; infer_instance
    degreeOnHom hcartZ ν hdim1.le (Finsupp.single E₀ 1) < 0 := by
  classical
  haveI : IsProper (ν ≫ Z ↘ Spec (.of ℂ)) := by rw [hν]; infer_instance
  -- `D` is negative on `ν`
  have hD : degreeOnHom hcartZ ν hdim1.le D < 0 := degreeOnHom_neg hM hcartZ hdim1 ν hν hcon
  -- `D = ∑ mᵢ Fᵢ`
  have hsum : degreeOnHom hcartZ ν hdim1.le D =
      ∑ E ∈ D.support, D E * degreeOnHom hcartZ ν hdim1.le (Finsupp.single E 1) := by
    conv_lhs => rw [← Finsupp.sum_single D]
    rw [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun E _ ↦ ?_
    rw [← Finsupp.smul_single_one, map_zsmul, smul_eq_mul]
  have hsupp : ∀ E ∈ D.support, E ∈ F.support := by
    intro E hE
    by_contra h
    exact Finsupp.mem_support_iff.1 hE (hM.coeff_eq_zero E h)
  have hE₀D : E₀ ∈ D.support := Finsupp.mem_support_iff.2 (hM.coeff_pos E₀ hE₀).ne'
  have hrest : 0 ≤ ∑ E ∈ D.support.erase E₀,
      D E * degreeOnHom hcartZ ν hdim1.le (Finsupp.single E 1) := by
    refine Finset.sum_nonneg fun E hE ↦ ?_
    obtain ⟨hne, hED⟩ := Finset.mem_erase.1 hE
    refine mul_nonneg (hM.coeff_pos E (hsupp E hED)).le ?_
    obtain ⟨c, hc⟩ := hoff E (hsupp E hED) hne
    have hsupp1 : (DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ)) : Set Z) = E.support := by
      rw [DivisorWithCoeffs.coe_supp, Finsupp.support_single_ne_zero _ one_ne_zero]
      simp
    exact (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (Z ↘ Spec (.of ℂ)) ν hdim1.le
      (Finsupp.single E 1) (hcartZ _) (by simp [Finsupp.single_nonneg])
      ⟨c, fun h ↦ hc (by rw [← hsupp1]; exact h)⟩).1
  rw [hsum, ← Finset.add_sum_erase _ _ hE₀D] at hD
  have h1 : D E₀ * degreeOnHom hcartZ ν hdim1.le (Finsupp.single E₀ 1) < 0 := by linarith
  have h2 : 0 < D E₀ := hM.coeff_pos E₀ hE₀
  by_contra hge
  have hge' := not_lt.1 hge
  nlinarith

/-- **Independence of the local classes on a slice.** Let `M` be a slice threefold of an
algebraic exceptional chart through `F_t`, with a neighbourhood `V₀` of `t` separating `F_t` from
the other singular points of the slice. If the fibre pieces of `F` over `t` are disjoint
surfaces and every component of `F_t` lies in a single exceptional component, then the germs of
local classes along the components of `F_t` are linearly independent. -/
private theorem linearIndependent_classGerm_of_slice
    (hM : IsCurvePointExceptionalModel sY r F D) [IsComplexScheme Z] {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y)) (To : (curveScheme T).Opens)
    (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    (hdisj : ∀ E : F.support, ∀ A B : Set Z,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) B → A ≠ B → Disjoint A B)
    (h2 : ∀ E : F.support, ∀ A : Set Z,
      Maximal (fun A ↦ IsIrreducible A ∧ A ⊆ (E.1.support : Set Z) ∩
        r ⁻¹' {(t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ))}) A →
      topologicalKrullDim A = ((2 : ℕ) : WithBot ℕ∞))
    (hgen : ∀ (S : irreducibleComponents (pointFibre sY r To t)) (E E' : Mori.PrimeDivisor Z),
      E ∈ F.support → E' ∈ F.support →
      (S : Set (pointFibre sY r To t)) ⊆ (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) →
      (S : Set (pointFibre sY r To t)) ⊆ (pointFibreFst sY r To t).base ⁻¹' (E'.support : Set Z) →
      E = E') :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
    ∀ {U₀ : Y.Opens} {b : UnderlyingSpace ℂ Y} (Ch : ExceptionalAlgebraicChart r F T U₀ b)
      {M : Scheme.{0}} [M.Over (Spec (.of ℂ))] [IsComplexScheme M]
      [IsIntegral M] [SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ))]
      (_hqp : IsQuasiProjectiveVariety ℂ (M ↘ Spec (.of ℂ))) (iW : M ⟶ Ch.W.toScheme)
      [IsClosedImmersion iW] (j : pointFibre sY r To t ⟶ M) [IsClosedImmersion j]
      (b₀ : Spec (.of ℂ) ⟶ Ch.B),
      iW ≫ Ch.W.ι ≫ r ≫ sY = M ↘ Spec (.of ℂ) → j ≫ iW ≫ Ch.W.ι = pointFibreFst sY r To t →
      iW ≫ Ch.ρ ≫ Ch.φ = (M ↘ Spec (.of ℂ)) ≫ b₀ →
      ∀ (V₀ : Opens (analyticSpace sY)), curveOpenInclusion sY To t ∈ V₀ →
      (∀ x : ComplexPoints (M ↘ Spec (.of ℂ)),
          (x.hom ≫ iW ≫ Ch.W.ι ≫ r).base (IsLocalRing.closedPoint ℂ) ∈
            (ComplexPoints.toScheme '' (V₀ : Set (analyticSpace sY)) : Set Y) →
          (x.hom ≫ iW ≫ Ch.W.ι).base (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z) →
          x.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range j.base) →
      ∀ (c : irreducibleComponents (pointFibre sY r To t) →
            resolutionLocalSystemFibre sY r To t),
          (∀ S, ∃ (E : Mori.PrimeDivisor Z) (V : Opens (analyticSpace sY))
            (hV : curveOpenInclusion sY To t ∈ V)
            (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
            E ∈ F.support ∧ IsLocalClass hM To t S E hV α ∧ c S = classGerm sY r To t hV α) →
          LinearIndependent ℚ c := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  intro U₀ b Ch M _ _ _ _ hqp iW _ j _ b₀ hcomp hj hpb V₀ hyV₀ hsep c hc
  haveI : IsSeparated (M ↘ Spec (.of ℂ)) := hqp.toIsSeparated
  classical
  -- the slice is a smooth integral threefold
  haveI : Smooth (M ↘ Spec (.of ℂ)) := SmoothOfRelativeDimension.smooth 3 _
  haveI : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian (M ↘ Spec (.of ℂ))
  haveI : IsNormal M := isNormal_of_smooth_over_field (M ↘ Spec (.of ℂ))
  haveI : QuasiCompact (M ↘ Spec (.of ℂ)) := inferInstance
  haveI : CompactSpace M := QuasiCompact.compactSpace_of_compactSpace (M ↘ Spec (.of ℂ))
  have hsmM : IsSmoothScheme (M ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).2 inferInstance
  have hcartM : ∀ B : Divisor M, B.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsmM
  have hsmZ : IsSmoothScheme (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hM.isResolution.2.2.1
  haveI : QuasiCompact (Z ↘ Spec (.of ℂ)) := by rw [← hM.comp_eq]; infer_instance
  have hcartZ : ∀ B : Divisor Z, B.IsCartier :=
    MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsmZ
  have hM3 : topologicalKrullDim M = ((3 : ℕ) : WithBot ℕ∞) :=
    (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) M 3).symm
  set pt := IsLocalRing.closedPoint ℂ with hpt0
  set iM := iW ≫ Ch.W.ι with hiMdef
  have hinj : Function.Injective iM.base := fun a a' h ↦
    iW.isClosedEmbedding.injective (Ch.W.ι.isOpenEmbedding.injective h)
  have hjs : j ≫ M ↘ Spec (.of ℂ) = pointFibre sY r To t ↘ Spec (.of ℂ) := by
    calc j ≫ M ↘ Spec (.of ℂ) = (j ≫ iW ≫ Ch.W.ι) ≫ r ≫ sY := by
          rw [← hcomp]; simp only [Category.assoc]
      _ = _ := by rw [hj]; exact pointFibreFst_comp_structure sY r To t
  have hdimF := topologicalKrullDim_pointFibre_le hM hT To t h2
  haveI := finite_irreducibleComponents_pointFibre hM To t
  haveI : Fintype (irreducibleComponents (pointFibre sY r To t)) := Fintype.ofFinite _
  rcases isEmpty_or_nonempty (irreducibleComponents (pointFibre sY r To t)) with hemp | ⟨⟨S₀, hS₀⟩⟩
  · exact linearIndependent_empty_type
  obtain ⟨p₀, -⟩ := hS₀.1.nonempty
  have hgenM := slice_genericPoint_notMem hM To t hdimF p₀ Ch (M ↘ Spec (.of ℂ)) iW j b₀ hpb hj
    hinj hM3
  have hB : ∀ E ∈ F.support, ∀ Zc : irreducibleComponents M,
      iM (componentGenericPoint M Zc) ∉ DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ)) := by
    intro E hE Zc h
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h
    apply hgenM
    have h' : iM (genericPoint M) ∈ (E.support : Set Z) := by
      have hsupp1 : (DivisorWithCoeffs.supp (Finsupp.single E (1 : ℤ)) : Set Z) = E.support := by
        rw [DivisorWithCoeffs.coe_supp, Finsupp.support_single_ne_zero _ one_ne_zero]
        simp
      rw [← hsupp1]; exact h
    rw [DivisorWithCoeffs.coe_supp]
    exact Set.mem_iUnion₂.2 ⟨E, hE, h'⟩
  -- the local classes
  choose E V hV α hEF hloc hcS using hc
  have hSE : ∀ S : irreducibleComponents (pointFibre sY r To t), (S : Set (pointFibre sY r To t)) ⊆
      (pointFibreFst sY r To t).base ⁻¹' ((E S).support : Set Z) := fun S ↦
    subset_preimage_of_isLocalClass hM (hloc S)
  have hdimS : ∀ S : irreducibleComponents (pointFibre sY r To t),
      topologicalKrullDim (S : Set (pointFibre sY r To t)) = ((2 : ℕ) : WithBot ℕ∞) := by
    intro S
    rw [← topologicalKrullDim_image_eq (isClosedEmbedding_pointFibreFst (r := r) To t).1.isEmbedding]
    exact h2 ⟨E S, hEF S⟩ _ (maximal_image_pointFibreFst (r := r) To t S (E S) (hSE S))
  -- the components of `F_t` as prime divisors of the slice
  have hPex : ∀ S : irreducibleComponents (pointFibre sY r To t), ∃ P : Mori.PrimeDivisor M,
      (P.support : Set M) = j.base '' (S : Set (pointFibre sY r To t)) := by
    intro S
    refine exists_primeDivisor_support_eq (M ↘ Spec (.of ℂ)) hM3
      (j.isClosedEmbedding.isClosedMap _ (isClosed_of_mem_irreducibleComponents _ S.2))
      (S.2.1.image _ j.continuous.continuousOn) ?_
    rw [topologicalKrullDim_image_eq j.isClosedEmbedding.isEmbedding]
    exact hdimS S
  choose P hP using hPex
  let a : irreducibleComponents (pointFibre sY r To t) → ℤ := fun S ↦
    (Divisor.pullback (f := iM) (Finsupp.single (E S) (1 : ℤ)) (hcartZ _) (hB _ (hEF S))).coeff
      (P S)
  haveI : LocallyOfFiniteType (r ≫ sY) := hM.isResolution.2.1.toLocallyOfFiniteType
  have hEeff : ∀ E' : Mori.PrimeDivisor Z, Stacks.Divisors.IsEffectiveCartierDivisor E'.idealSheaf :=
    fun E' ↦ MMP.Resolution.Aux.isEffectiveCartierDivisor_idealSheaf (r ≫ sY)
      hM.isResolution.2.2.1 E'
  have hPgen : ∀ S, iM.base (P S).genericPoint ∈ ((E S).support : Set Z) := by
    intro S
    have hmem : (P S).genericPoint ∈ ((P S).support : Set M) := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    rw [hP S] at hmem
    obtain ⟨q, hq, hqe⟩ := hmem
    rw [← hqe]
    have := hSE S hq
    rw [Set.mem_preimage, ← hj] at this
    exact this
  have ha : ∀ S, 1 ≤ a S := fun S ↦
    one_le_coeff_pullback_single iM (E S) (hEeff _) (hcartZ _) (hB _ (hEF S)) (P S) (hPgen S)
  -- smooth projective test curves in each component
  have htest : ∀ S : irreducibleComponents (pointFibre sY r To t),
      ∃ (Γ : Scheme.{0}) (_ : Γ.Over (Spec (.of ℂ))) (ν : Γ ⟶ pointFibre sY r To t),
        ν ≫ pointFibre sY r To t ↘ Spec (.of ℂ) = Γ ↘ Spec (.of ℂ) ∧ IsComplexScheme Γ ∧
        IsIntegral Γ ∧ IsProper (Γ ↘ Spec (.of ℂ)) ∧ IsSmoothScheme (Γ ↘ Spec (.of ℂ)) ∧
        topologicalKrullDim Γ = 1 ∧ MMP.Mori.IsProjectiveVariety ℂ (Γ ↘ Spec (.of ℂ)) ∧
        IsFinite ν ∧ (∀ c, ν c ∈ (S : Set (pointFibre sY r To t))) ∧
        ∃ c, (∀ S' : irreducibleComponents (pointFibre sY r To t), S' ≠ S →
            ν c ∉ (S' : Set (pointFibre sY r To t))) ∧
          ∀ E' ∈ F.support, E' ≠ E S →
            (pointFibreFst sY r To t).base (ν c) ∉ (E'.support : Set Z) := by
    intro S
    haveI := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
    haveI : IsProper (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
      change IsProper (pullback.snd r (t.hom ≫ To.ι ≫ curveι T))
      infer_instance
    haveI : LocallyOfFiniteType r := by
      have : LocallyOfFiniteType (r ≫ sY) := hM.isResolution.2.1.toLocallyOfFiniteType
      exact LocallyOfFiniteType.of_comp (g := sY) this
    haveI : LocallyOfFiniteType (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
      change LocallyOfFiniteType (pullback.snd r (t.hom ≫ To.ι ≫ curveι T))
      infer_instance
    haveI : IsLocallyNoetherian (pointFibre sY r To t) :=
      LocallyOfFiniteType.isLocallyNoetherian (pointFibre sY r To t ↘ Spec (.of ℂ))
    haveI : CompactSpace (pointFibre sY r To t) :=
      QuasiCompact.compactSpace_of_compactSpace (pointFibre sY r To t ↘ Spec (.of ℂ))
    have hb : (t.hom ≫ To.ι ≫ curveι T) ≫ sY = 𝟙 _ := by
      simpa [Category.assoc] using t.hom_comp_structure
    haveI : IsClosedImmersion (t.hom ≫ To.ι ≫ curveι T) := isClosedImmersion_of_comp_eq_id sY _ hb
    haveI : IsClosedImmersion (pointFibreFst sY r To t) := by
      change IsClosedImmersion (pullback.fst r (t.hom ≫ To.ι ≫ curveι T))
      infer_instance
    have hproj : IsProjectiveMorphism (pointFibre sY r To t ↘ Spec (.of ℂ)) := by
      have hZp : MMP.Mori.IsProjectiveVariety ℂ (r ≫ sY) := by
        have hY := hM.isProjectiveVariety
        rw [MMP.Mori.isProjectiveVariety_iff] at hY ⊢
        exact ⟨hM.isResolution.2.1, hM.isResolution.2.2.2.1.comp hY.2⟩
      obtain ⟨-, n, i, hi, h⟩ := (MMP.Mori.isProjectiveVariety_iff _ _).1 hZp
      haveI := hi
      exact ⟨n, pointFibreFst sY r To t ≫ i, inferInstance, by
        rw [Category.assoc, h]; exact pointFibreFst_comp_structure sY r To t⟩
    have hScl := isClosed_of_mem_irreducibleComponents _ S.2
    set η := S.2.1.genericPoint with hηdef
    have hgp : IsGenericPoint η (S : Set (pointFibre sY r To t)) := by
      have := S.2.1.isGenericPoint_genericPoint_closure
      rwa [hScl.closure_eq] at this
    obtain ⟨p, hpS, hpcl⟩ := hScl.exists_closed_singleton S.2.1.nonempty
    have hηp : η ⤳ p := hgp.specializes hpS
    let Zc : Set (pointFibre sY r To t) := {p} ∪
      (⋃ (S' : irreducibleComponents (pointFibre sY r To t)) (_ : S' ≠ S),
        (S' : Set (pointFibre sY r To t))) ∪
      ⋃ E' ∈ F.support.filter (· ≠ E S),
        (pointFibreFst sY r To t).base ⁻¹' (E'.support : Set Z)
    have hZcl : IsClosed Zc := by
      refine (hpcl.union (isClosed_iUnion_of_finite fun S' ↦ isClosed_iUnion_of_finite fun _ ↦
        isClosed_of_mem_irreducibleComponents _ S'.2)).union ?_
      exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun E' _ ↦
        E'.idealSheaf.support.isClosed.preimage (pointFibreFst sY r To t).continuous
    have hηZ : η ∉ Zc := by
      rintro ((hηp' | hηS') | hηE')
      · -- `S` would be a point
        have hSp : (S : Set (pointFibre sY r To t)) = {p} := by
          rw [← hgp.def, Set.mem_singleton_iff.1 hηp', hpcl.closure_eq]
        have h0 : topologicalKrullDim (S : Set (pointFibre sY r To t)) ≤ 0 := by
          haveI : Subsingleton (S : Set (pointFibre sY r To t)) := by
            rw [hSp]; infer_instance
          haveI : DiscreteTopology (S : Set (pointFibre sY r To t)) := ⟨Subsingleton.elim _ _⟩
          exact topologicalKrullDim_zero_of_discreteTopology _
        rw [hdimS S] at h0
        exact absurd h0 (by decide)
      · obtain ⟨S', hS'S, hηS'⟩ := Set.mem_iUnion₂.1 hηS'
        have hsub : (S : Set (pointFibre sY r To t)) ⊆ S' := by
          rw [← hgp.def]
          exact closure_minimal (Set.singleton_subset_iff.2 hηS')
            (isClosed_of_mem_irreducibleComponents _ S'.2)
        exact hS'S (Subtype.ext (le_antisymm (S.2.2 S'.2.1 hsub) hsub))
      · obtain ⟨E', hE', hηE'⟩ := Set.mem_iUnion₂.1 hηE'
        obtain ⟨hE'F, hE'ne⟩ := Finset.mem_filter.1 hE'
        have hsub : (S : Set (pointFibre sY r To t)) ⊆
            (pointFibreFst sY r To t).base ⁻¹' (E'.support : Set Z) := by
          rw [← hgp.def]
          exact closure_minimal (Set.singleton_subset_iff.2 hηE')
            (E'.idealSheaf.support.isClosed.preimage (pointFibreFst sY r To t).continuous)
        exact hE'ne (hgen S E' (E S) hE'F (hEF S) hsub (hSE S))
    obtain ⟨Γ, _, ν, hν, hcx, hint, hpr, hsm, hdim, hpj, hfin, hspec, ⟨c, hc⟩, -⟩ :=
      exists_smooth_projective_curve hproj hηp hpcl hZcl (Or.inl (Or.inl rfl)) hηZ
    refine ⟨Γ, inferInstance, ν, hν, hcx, hint, hpr, hsm, hdim, hpj, hfin, fun c' ↦ ?_, c,
      fun S' hS' h ↦ hc (Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨S', hS', h⟩))),
      fun E' hE' hne h ↦ hc (Or.inr (Set.mem_iUnion₂.2 ⟨E', Finset.mem_filter.2 ⟨hE', hne⟩, h⟩))⟩
    rw [← hgp.def]
    exact specializes_iff_mem_closure.1 (hspec c')
  -- on each component, the local class is a multiple of the class of the surface
  have hK : ∀ S, (rationalCohomologyMap (pointFibreInclusion sY r To t (hV S)) 2).hom (α S) =
      ((a S : ℤ) : ℚ) • (rationalCohomologyMap (analyticMap j hjs) 2).hom
        (rationalChernHom hcartM (Finsupp.single (P S) 1)) := by
    intro S
    obtain ⟨Γ, _, ν, hν, hcx, hint, hpr, hsm, hdim, hpj, hfin, hS, c₀, -, hc₀E⟩ := htest S
    haveI := hcx
    haveI := hint
    haveI := hpr
    haveI := hfin
    have hb : (t.hom ≫ To.ι ≫ curveι T) ≫ sY = 𝟙 _ := by
      simpa [Category.assoc] using t.hom_comp_structure
    haveI : IsClosedImmersion (t.hom ≫ To.ι ≫ curveι T) := isClosedImmersion_of_comp_eq_id sY _ hb
    haveI : IsClosedImmersion (pointFibreFst sY r To t) := by
      change IsClosedImmersion (pullback.fst r (t.hom ≫ To.ι ≫ curveι T))
      infer_instance
    let ν' := ν ≫ pointFibreFst sY r To t
    haveI : IsFinite ν' := inferInstance
    have hν' : ν' ≫ Z ↘ Spec (.of ℂ) = Γ ↘ Spec (.of ℂ) := by
      change ν ≫ pointFibreFst sY r To t ≫ Z ↘ Spec (.of ℂ) = _
      rw [← hM.comp_eq, pointFibreFst_comp_structure, hν]
    have hcon : ∀ c, r (ν' c) = (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)) := by
      intro c
      have : (pointFibreFst sY r To t).base (ν c) ∈ Set.range (pointFibreFst sY r To t).base :=
        ⟨_, rfl⟩
      rw [(isClosedEmbedding_pointFibreFst (r := r) To t).2] at this
      exact this
    have hneg := degreeOn_single_neg hM hcartZ hdim ν' hν' hcon (hEF S)
      (fun E' hE' hne ↦ ⟨c₀, hc₀E E' hE' hne⟩)
    refine fibreRestriction_localClass_eq hM To t hdimF hdisj h2 Ch hqp iW j b₀ hcomp hj hpb hjs
      V₀ hyV₀ hsep hcartM S (E S) (hEF S) (hV S) (α S) (hloc S) (P S) (hP S) (hcartZ _)
      (hB _ (hEF S)) ⟨analyticSpace (Γ ↘ Spec (.of ℂ)), analyticMap ν hν, fun z ↦ hS _, ?_⟩
    intro h0
    obtain ⟨G, hG, ⟨O, hO, hGO⟩, hfib, -, hinv, h1⟩ := (hloc S).properties
    have hout : ∀ z : analyticSpace (Γ ↘ Spec (.of ℂ)),
        pointFibreInclusion sY r To t (hV S) (analyticMap ν hν z) ∉
          {z' : preimageSpace (resolutionAnalyticMap sY r) (V S) |
            z'.1.hom.base pt ∈ ((E S).support : Set Z)} \ G :=
      fun z hz ↦ hz.2 ((hfib _).2 (hS _))
    let m : analyticSpace (Γ ↘ Spec (.of ℂ)) ⟶
        TopCat.of (({z' : preimageSpace (resolutionAnalyticMap sY r) (V S) |
          z'.1.hom.base pt ∈ ((E S).support : Set Z)} \ G)ᶜ :
            Set (preimageSpace (resolutionAnalyticMap sY r) (V S))) :=
      TopCat.ofHom ⟨fun z ↦ ⟨_, hout z⟩, (((pointFibreInclusion sY r To t (hV S)).hom.continuous.comp
        (analyticMap ν hν).hom.continuous)).subtype_mk _⟩
    have hfac : analyticMap ν hν ≫ pointFibreInclusion sY r To t (hV S) =
        m ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := rfl
    have hmaps : m ≫ (TopCat.ofHom (X := TopCat.of (({z' : preimageSpace
        (resolutionAnalyticMap sY r) (V S) | z'.1.hom.base pt ∈ ((E S).support : Set Z)} \ G)ᶜ :
          Set (preimageSpace (resolutionAnalyticMap sY r) (V S)))) (Y := analyticSpace (r ≫ sY))
        ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
        analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) =
        analyticMap ν' hν' :=
      TopCat.ext fun z ↦ ComplexPoints.ext (by
        change ((z.hom ≫ ν) ≫ pointFibreFst sY r To t) ≫ 𝟙 Z = z.hom ≫ ν ≫ pointFibreFst sY r To t
        rw [Category.comp_id, Category.assoc])
    have hc1 : ∑ _u : Unit, (1 : ℚ) • (rationalCohomologyMap (analyticMap ν' hν') 2).hom
        (rationalChernHom hcartZ (Finsupp.single (E S) 1)) = 0 := by
      haveI := (hcartZ (Finsupp.single (E S) 1)).isInvertibleModule_divisorialSheaf
      rw [Fintype.sum_unique, one_smul, rationalChernHom_apply, ← hmaps,
        rationalCohomologyMap_comp, ModuleCat.comp_apply, ← h1, ← ModuleCat.comp_apply,
        ← rationalCohomologyMap_comp, ← hfac]
      exact h0
    have hdeg0 := sum_mul_degreeOn_eq_zero hcartZ hsm hdim hpj ν' hν'
      (fun _ : Unit ↦ Finsupp.single (E S) (1 : ℤ)) (fun _ ↦ 1) hc1
    rw [Fintype.sum_unique, one_mul] at hdeg0
    have key : ∀ x : ℤ, (x : ℚ) = 0 → x < 0 → False := fun x h1 h2 ↦ by
      have := Int.cast_eq_zero.mp h1
      omega
    exact key _ hdeg0 hneg
  rw [Fintype.linearIndependent_iff]
  intro l hl
  have hfib0 := sum_smul_pointFibreInclusion_eq_zero To t V hV α l (by
    rw [← hl]
    exact Finset.sum_congr rfl fun S _ ↦ by rw [hcS S])
  -- the degree matrix of the test curves against the surfaces
  have hdeg : ∀ i : irreducibleComponents (pointFibre sY r To t),
      ∃ A : irreducibleComponents (pointFibre sY r To t) → ℚ,
        (∑ S, A S * (l S * a S) = 0) ∧ (∀ S, i ≠ S → 0 ≤ A S) ∧
          ∑ S, A S * (D.coeff (E S) * a S) < 0 := by
    intro i
    obtain ⟨Γ, _, ν, hν, hcx, hint, hpr, hsm, hdim, hpj, hfin, hS, c₀, hc₀S, hc₀E⟩ := htest i
    haveI := hcx
    haveI := hint
    haveI := hpr
    haveI := hfin
    let νM := ν ≫ j
    have hνM : νM ≫ M ↘ Spec (.of ℂ) = Γ ↘ Spec (.of ℂ) := by
      change ν ≫ j ≫ M ↘ Spec (.of ℂ) = _
      rw [hjs, hν]
    haveI : IsProper (νM ≫ M ↘ Spec (.of ℂ)) := by rw [hνM]; infer_instance
    refine ⟨fun S ↦ (degreeOnHom hcartM νM hdim.le (Finsupp.single (P S) 1) : ℚ), ?_, ?_, ?_⟩
    · -- the relation among the surfaces on the test curve
      have hrel : ∑ S, (l S * a S) • (rationalCohomologyMap (analyticMap νM hνM) 2).hom
          (rationalChernHom hcartM (Finsupp.single (P S) 1)) = 0 := by
        have hanalytic : analyticMap νM hνM = analyticMap ν hν ≫ analyticMap j hjs :=
          (analyticMap_comp ν hν j hjs).symm
        have h' := congrArg (rationalCohomologyMap (analyticMap ν hν) 2).hom hfib0
        rw [map_sum, map_zero] at h'
        rw [← h']
        refine Finset.sum_congr rfl fun S _ ↦ ?_
        rw [hK S, map_smul, map_smul, smul_smul, hanalytic, rationalCohomologyMap_comp,
          ModuleCat.comp_apply]
      have h' := sum_mul_degreeOn_eq_zero hcartM hsm hdim hpj νM hνM
        (fun S ↦ Finsupp.single (P S) (1 : ℤ)) (fun S ↦ l S * a S) hrel
      rw [← h']
      exact Finset.sum_congr rfl fun S _ ↦ by ring
    · -- the other surfaces are nonnegative on the test curve
      intro S hiS
      have hsupp1 : (DivisorWithCoeffs.supp (Finsupp.single (P S) (1 : ℤ)) : Set M) =
          (P S).support := by
        rw [DivisorWithCoeffs.coe_supp, Finsupp.support_single_ne_zero _ one_ne_zero]
        simp
      have hnn := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (M ↘ Spec (.of ℂ)) νM
        hdim.le (Finsupp.single (P S) 1) (hcartM _) (by simp [Finsupp.single_nonneg])
        ⟨c₀, fun h ↦ ?_⟩).1
      · have key : ∀ x : ℤ, 0 ≤ x → (0 : ℚ) ≤ x := fun x h ↦ by exact_mod_cast h
        exact key _ hnn
      · have h' : j.base (ν.base c₀) ∈ ((P S).support : Set M) := by rw [← hsupp1]; exact h
        rw [hP S] at h'
        obtain ⟨q, hq, hqe⟩ := h'
        exact hc₀S S (Ne.symm hiS) (j.isClosedEmbedding.injective hqe ▸ hq)
    · -- the weighted surfaces are negative on the test curve
      have hiMZ : iM ≫ Z ↘ Spec (.of ℂ) = M ↘ Spec (.of ℂ) := by
        rw [← hM.comp_eq, hiMdef, Category.assoc]; exact hcomp
      set ν' := νM ≫ iM with hν'def
      have hν' : ν' ≫ Z ↘ Spec (.of ℂ) = Γ ↘ Spec (.of ℂ) := by
        rw [hν'def, Category.assoc, hiMZ, hνM]
      haveI : IsProper (ν' ≫ Z ↘ Spec (.of ℂ)) := by rw [hν']; infer_instance
      have hb : (t.hom ≫ To.ι ≫ curveι T) ≫ sY = 𝟙 _ := by
        simpa [Category.assoc] using t.hom_comp_structure
      haveI : IsClosedImmersion (t.hom ≫ To.ι ≫ curveι T) :=
        isClosedImmersion_of_comp_eq_id sY _ hb
      haveI : IsClosedImmersion (pointFibreFst sY r To t) := by
        change IsClosedImmersion (pullback.fst r (t.hom ≫ To.ι ≫ curveι T))
        infer_instance
      have hν'eq : ν' = ν ≫ pointFibreFst sY r To t := by
        rw [hν'def, ← hj]; rfl
      haveI : IsFinite ν' := by rw [hν'eq]; infer_instance
      have hcon : ∀ c, r (ν' c) = (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)) := by
        intro c
        rw [hν'eq]
        have : (pointFibreFst sY r To t).base (ν c) ∈ Set.range (pointFibreFst sY r To t).base :=
          ⟨_, rfl⟩
        rw [(isClosedEmbedding_pointFibreFst (r := r) To t).2] at this
        exact this
      have hDneg := degreeOnHom_neg hM hcartZ hdim ν' hν' hcon
      have hsumD : degreeOnHom hcartZ ν' hdim.le D =
          ∑ E' ∈ D.support, D E' * degreeOnHom hcartZ ν' hdim.le (Finsupp.single E' 1) := by
        conv_lhs => rw [← Finsupp.sum_single D]
        rw [Finsupp.sum, map_sum]
        refine Finset.sum_congr rfl fun E' _ ↦ ?_
        rw [← Finsupp.smul_single_one, map_zsmul, smul_eq_mul]
      have hsuppD : ∀ E' ∈ D.support, E' ∈ F.support := by
        intro E' hE'
        by_contra h
        exact Finsupp.mem_support_iff.1 hE' (hM.coeff_eq_zero E' h)
      -- degrees of exceptional components on `Z` and of their traces on the slice
      have hdegZM : ∀ E' (hE' : E' ∈ F.support), degreeOnHom hcartZ ν' hdim.le
          (Finsupp.single E' 1) = degreeOnHom hcartM νM hdim.le
            (Divisor.pullback (f := iM) (Finsupp.single E' (1 : ℤ)) (hcartZ _) (hB E' hE')) := by
        intro E' hE'
        haveI := (hcartZ (Finsupp.single E' 1)).isInvertibleModule_divisorialSheaf
        haveI := (hcartM (Divisor.pullback (f := iM) (Finsupp.single E' (1 : ℤ)) (hcartZ _)
          (hB E' hE'))).isInvertibleModule_divisorialSheaf
        obtain ⟨e⟩ := MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso (hcartZ _) iM
          (hB E' hE')
        haveI : IsProper ((νM ≫ iM) ≫ Z ↘ Spec (.of ℂ)) := by rw [hν']; infer_instance
        haveI : IsProper (νM ≫ iM ≫ Z ↘ Spec (.of ℂ)) := by rw [hiMZ]; infer_instance
        have h1 := MMP.Threefold.Resolution.degreeOn_comp (k := ℂ) (Z ↘ Spec (.of ℂ)) iM νM
          hdim.le (Divisor.divisorialSheaf (Finsupp.single E' (1 : ℤ)))
        have h2 := Mori.degreeOn_eq_of_iso ℂ (M ↘ Spec (.of ℂ)) νM hdim.le e
        change Mori.degreeOn ℂ (Z ↘ Spec (.of ℂ)) (νM ≫ iM) hdim.le _ =
          Mori.degreeOn ℂ (M ↘ Spec (.of ℂ)) νM hdim.le _
        rw [h1, h2, Mori.degreeOn_eq_invertibleCurveDegree, Mori.degreeOn_eq_invertibleCurveDegree]
        exact invertibleCurveDegree_congr_structure (by rw [hiMZ]) hdim.le _
      -- the trace of an exceptional component bounds its surfaces from above
      have hPinj : Function.Injective P := by
        intro S S' h
        have : j.base '' (S : Set (pointFibre sY r To t)) = j.base '' S' := by
          rw [← hP S, ← hP S', h]
        exact Subtype.ext (Set.image_injective.2 j.isClosedEmbedding.injective this)
      have hlow : ∀ E' (hE' : E' ∈ F.support),
          ∑ S ∈ Finset.univ.filter (fun S ↦ E S = E'),
              a S * degreeOnHom hcartM νM hdim.le (Finsupp.single (P S) 1) ≤
            degreeOnHom hcartM νM hdim.le
              (Divisor.pullback (f := iM) (Finsupp.single E' (1 : ℤ)) (hcartZ _) (hB E' hE')) := by
        intro E' hE'
        set EM := Divisor.pullback (f := iM) (Finsupp.single E' (1 : ℤ)) (hcartZ _) (hB E' hE')
          with hEMdef
        set BE : Divisor M := ∑ S ∈ Finset.univ.filter (fun S ↦ E S = E'),
          a S • Finsupp.single (P S) 1 with hBEdef
        have hBEapp : ∀ Q, BE Q = ∑ S ∈ Finset.univ.filter (fun S ↦ E S = E'),
            if P S = Q then a S else 0 := by
          intro Q
          rw [hBEdef, Finsupp.finset_sum_apply]
          refine Finset.sum_congr rfl fun S _ ↦ ?_
          rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
          split_ifs <;> simp
        have hBE1 : ∀ S₀, E S₀ = E' → BE (P S₀) = a S₀ := by
          intro S₀ hS₀
          rw [hBEapp, Finset.sum_eq_single S₀ (fun S _ hne ↦ by rw [if_neg (fun h ↦ hne (hPinj h))])
            (fun h ↦ absurd (Finset.mem_filter.2 ⟨Finset.mem_univ S₀, hS₀⟩) h), if_pos rfl]
        have hBE2 : ∀ Q, (∀ S, E S = E' → P S ≠ Q) → BE Q = 0 := by
          intro Q hQ
          rw [hBEapp]
          exact Finset.sum_eq_zero fun S hS ↦ if_neg (hQ S (Finset.mem_filter.1 hS).2)
        have hEM1 : ∀ S₀, E S₀ = E' → EM (P S₀) = a S₀ := by
          intro S₀ hS₀
          subst hS₀
          rfl
        have hEM2 : ∀ S₀, E S₀ ≠ E' → EM (P S₀) = 0 := by
          intro S₀ hS₀
          refine coeff_pullback_single_eq_zero iM E' (hEeff _) (hcartZ _) (hB E' hE') (P S₀)
            fun hmem ↦ hS₀ ?_
          have hsub : ((P S₀).support : Set M) ⊆ iM.base ⁻¹' (E'.support : Set Z) := by
            rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
            exact closure_minimal (Set.singleton_subset_iff.2 hmem)
              (E'.idealSheaf.support.isClosed.preimage iM.continuous)
          refine hgen S₀ (E S₀) E' (hEF S₀) hE' (hSE S₀) fun z hz ↦ ?_
          have : j.base z ∈ ((P S₀).support : Set M) := (hP S₀).symm ▸ Set.mem_image_of_mem _ hz
          have h' := hsub this
          rw [Set.mem_preimage, ← hj]
          exact h'
        have hR0 : ∀ S₀, (EM - BE) (P S₀) = 0 := by
          intro S₀
          rw [Finsupp.sub_apply]
          by_cases hS₀ : E S₀ = E'
          · rw [hEM1 S₀ hS₀, hBE1 S₀ hS₀, sub_self]
          · rw [hEM2 S₀ hS₀, hBE2 _ (fun S hS h ↦ hS₀ (by rw [← hPinj h]; exact hS)), sub_self]
        have hRnn : 0 ≤ EM - BE := by
          intro Q
          by_cases hQ : ∃ S₀, P S₀ = Q
          · obtain ⟨S₀, rfl⟩ := hQ
            rw [hR0 S₀]; rfl
          · push Not at hQ
            change (0 : ℤ) ≤ (EM - BE) Q
            rw [Finsupp.sub_apply, hBE2 Q (fun S _ ↦ hQ S), sub_zero]
            exact coeff_pullback_single_nonneg iM E' (hEeff _) (hcartZ _) (hB E' hE') Q
        have hRsupp : ∃ c, νM c ∉ DivisorWithCoeffs.supp (EM - BE) := by
          refine ⟨c₀, fun hmem ↦ ?_⟩
          obtain ⟨Q, hQR, hcQ⟩ := DivisorWithCoeffs.mem_supp_iff.1 hmem
          have hQP : ∀ S, P S ≠ Q := fun S h ↦ hQR (by rw [← h]; exact hR0 S)
          have hEMQ : EM Q ≠ 0 := by
            intro h0
            apply hQR
            change (EM - BE) Q = 0
            rw [Finsupp.sub_apply, h0, hBE2 Q (fun S _ ↦ hQP S), sub_zero]
          have hgenQ : iM.base Q.genericPoint ∈ (E'.support : Set Z) := by
            by_contra h
            exact hEMQ (coeff_pullback_single_eq_zero iM E' (hEeff _) (hcartZ _) (hB E' hE') Q h)
          have hgenF : iM.base Q.genericPoint ∈ (F.supp : Set Z) := by
            rw [DivisorWithCoeffs.coe_supp]
            exact Set.mem_iUnion₂.2 ⟨E', hE', hgenQ⟩
          obtain ⟨S'', hS''⟩ := slice_primeDivisor_support_eq hM To t hdimF Ch (M ↘ Spec (.of ℂ))
            iW j b₀ hpb hj hinj hM3 Q hgenF ⟨ν.base c₀, hcQ⟩
          exact hQP S'' (primeDivisor_eq_of_support_eq ((hP S'').trans hS''.symm))
        have hdR := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff (M ↘ Spec (.of ℂ)) νM
          hdim.le (EM - BE) (hcartM _) hRnn hRsupp).1
        have hsplit : degreeOnHom hcartM νM hdim.le EM =
            degreeOnHom hcartM νM hdim.le BE + degreeOnHom hcartM νM hdim.le (EM - BE) := by
          rw [← map_add, add_sub_cancel]
        have hBEdeg : degreeOnHom hcartM νM hdim.le BE = ∑ S ∈ Finset.univ.filter
            (fun S ↦ E S = E'), a S * degreeOnHom hcartM νM hdim.le (Finsupp.single (P S) 1) := by
          rw [hBEdef, map_sum]
          refine Finset.sum_congr rfl fun S _ ↦ ?_
          rw [map_zsmul, smul_eq_mul]
        rw [hsplit, ← hBEdeg]
        have hdR' : 0 ≤ degreeOnHom hcartM νM hdim.le (EM - BE) := hdR
        omega
      -- assembly
      have hfiber : ∑ S, D (E S) * a S * degreeOnHom hcartM νM hdim.le (Finsupp.single (P S) 1) =
          ∑ E' ∈ D.support, D E' * ∑ S ∈ Finset.univ.filter (fun S ↦ E S = E'),
            a S * degreeOnHom hcartM νM hdim.le (Finsupp.single (P S) 1) := by
        rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := D.support) (g := E)
          (fun S _ ↦ Finsupp.mem_support_iff.2 (hM.coeff_pos (E S) (hEF S)).ne')]
        refine Finset.sum_congr rfl fun E' _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS ↦ ?_
        rw [(Finset.mem_filter.1 hS).2]
        ring
      have hle : ∑ S, D (E S) * a S * degreeOnHom hcartM νM hdim.le (Finsupp.single (P S) 1) ≤
          degreeOnHom hcartZ ν' hdim.le D := by
        rw [hfiber, hsumD]
        refine Finset.sum_le_sum fun E' hE' ↦ ?_
        rw [hdegZM E' (hsuppD E' hE')]
        exact mul_le_mul_of_nonneg_left (hlow E' (hsuppD E' hE'))
          (hM.coeff_pos E' (hsuppD E' hE')).le
      have hlt := hle.trans_lt hDneg
      have hlt' : ((∑ S, D (E S) * a S * degreeOnHom hcartM νM hdim.le
          (Finsupp.single (P S) 1) : ℤ) : ℚ) < 0 := by exact_mod_cast hlt
      push_cast at hlt'
      calc ∑ S, (degreeOnHom hcartM νM hdim.le (Finsupp.single (P S) 1) : ℚ) *
            (D.coeff (E S) * a S)
          = ∑ S, (D (E S) : ℚ) * a S * degreeOnHom hcartM νM hdim.le (Finsupp.single (P S) 1) :=
            Finset.sum_congr rfl fun S _ ↦ by rw [DivisorWithCoeffs.coeff_apply]; ring
        _ < 0 := hlt'
  choose A hA0 hAoff hArow using hdeg
  have hw : ∀ S, (0 : ℚ) < D.coeff (E S) * a S := by
    intro S
    have h1 := hM.coeff_pos (E S) (hEF S)
    have h2 := ha S
    exact_mod_cast mul_pos h1 (by omega)
  have hz := eq_zero_of_sum_mul_eq_zero A (fun S ↦ (D.coeff (E S) * a S : ℚ)) hw hAoff
    (fun i ↦ by exact_mod_cast hArow i) (fun S ↦ l S * a S) hA0
  intro S
  have := congrFun hz S
  have hne : ((a S : ℤ) : ℚ) ≠ 0 := by have := ha S; exact_mod_cast (by omega : a S ≠ 0)
  exact (mul_eq_zero.1 this).resolve_right hne

/-- **Independence of the local classes.** Over adapted opens inside a suitable open `U` of `Y`
meeting `T`, the germs of one local class along each component of `F_t` are linearly
independent in `𝒲_t`. -/
private theorem exists_open_linearIndependent_classGerm_aux
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U → IsAdaptedOpen sY r To →
        ∀ t (c : irreducibleComponents (pointFibre sY r To t) →
            resolutionLocalSystemFibre sY r To t),
          (∀ S, ∃ (E : Mori.PrimeDivisor Z) (V : Opens (analyticSpace sY))
            (hV : curveOpenInclusion sY To t ∈ V)
            (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
            E ∈ F.support ∧ IsLocalClass hM To t S E hV α ∧ c S = classGerm sY r To t hV α) →
          LinearIndependent ℚ c := by
  classical
  haveI := isComplexScheme_of_isCurvePointExceptionalModel hM
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  obtain ⟨-, U₁, -, hU₁, -, Hdisj, -⟩ := exists_open_general hM hT hdim
  obtain ⟨U₂, hU₂, hch⟩ := exists_open_forall_nonempty_exceptionalAlgebraicChart (Y := Y)
    (by exact hM) T (by exact hT) hdim
  obtain ⟨U₃, hU₃, H₃⟩ := exists_open_eq_of_subset_preimage hM hT hdim
  refine ⟨U₁ ⊓ U₂ ⊓ U₃, inter_inter_nonempty_of_irreducibleCloseds T
    (inter_inter_nonempty_of_irreducibleCloseds T hU₁ hU₂) hU₃, fun To hle _ t c hc ↦ ?_⟩
  set y := curveOpenInclusion sY To t with hy
  set yY := (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)) with hyY
  have hrange : Set.range (curveι T).base = (T : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hyU : yY ∈ ((U₁ ⊓ U₂ ⊓ U₃ : Y.Opens) : Set Y) :=
    hle (t.hom.base (default : Spec (.of ℂ))).2
  have hyT : yY ∈ (T : Set Y) := hrange ▸ ⟨_, rfl⟩
  -- the chart and the slice through `F_t`
  let b : UnderlyingSpace ℂ Y := ComplexPoints.homeomorphUnderlyingSpace (X := Y) y
  have hbmem : b ∈ UnderlyingSpace.pointsOver (K := ℂ) ((U₂ : Set Y) ∩ T) := by
    show (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∈ (U₂ : Set Y) ∩ T
    have e : (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) = yY :=
      congrArg _ (Subsingleton.elim _ _)
    rw [e]
    exact ⟨hyU.1.2, hyT⟩
  let Ch := (hch b hbmem).some
  have hbX : (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∈ (Ch.X : Set Y) :=
    Ch.mem_X
  obtain ⟨M, sM, iW, j, b₀, ⟨hcx, hvar, hns, hqp, hsmo⟩, hiW, hcomp, hj, hjc, hpb, -⟩ :=
    exists_slice_variety hM hT To t Ch hbX
  letI : M.Over (Spec (.of ℂ)) := ⟨sM⟩
  haveI := hcx
  haveI := hvar
  haveI : IsSeparated (M ↘ Spec (.of ℂ)) := hns
  haveI := hiW
  haveI := hjc
  have hinj : Function.Injective (iW ≫ Ch.W.ι).base := fun a a' h ↦
    iW.isClosedEmbedding.injective (Ch.W.ι.isOpenEmbedding.injective h)
  obtain ⟨V₀, hyV₀, hsep⟩ := exists_separating_open hM To t Ch sM iW j b₀ hcomp hj hpb hinj
  haveI : SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ)) := hsmo
  exact linearIndependent_classGerm_of_slice hM hT To t
    (fun E A B hA hB ↦ (Hdisj yY ⟨hyU.1.1, hyT⟩ E).1 A B hA hB)
    (fun E A hA ↦ (Hdisj yY ⟨hyU.1.1, hyT⟩ E).2 A hA)
    (fun S E E' hE hE' hS hS' ↦ H₃ To (hle.trans (Scheme.Hom.preimage_mono _ inf_le_right)) t S E
      E' hE hE' hS hS')
    Ch hqp iW j b₀ hcomp hj hpb V₀ hyV₀ hsep c hc

/-- **The kernel has at most one dimension per component.** Over adapted opens inside a
suitable open `U` of `Y` meeting `T`, `ker (r_t : 𝒲_t ⟶ 𝒱_{T,t})` has rank at most the number of
irreducible components of `F_t`. -/
private theorem exists_open_rank_ker_le
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U → IsAdaptedOpen sY r To →
        BaseChangeInjective sY r To → ∀ t, Module.rank ℚ
            (LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom) ≤
          Cardinal.mk (irreducibleComponents (pointFibre sY r To t)) := by
  classical
  haveI := isComplexScheme_of_isCurvePointExceptionalModel hM
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  letI : r.IsOver (Spec (.of ℂ)) := ⟨hM.comp_eq⟩
  haveI : MMP.Mori.IsVariety ℂ sY := hM.isResolution.1
  haveI : LocallyOfFiniteType sY := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType (f := sY)
  haveI := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
  obtain ⟨-, U₁, -, hU₁, -, Hdisj, -⟩ := exists_open_general hM hT hdim
  obtain ⟨U₂, hU₂, hch⟩ := exists_open_forall_nonempty_exceptionalAlgebraicChart (Y := Y)
    (by exact hM) T (by exact hT) hdim
  refine ⟨U₁ ⊓ U₂, inter_inter_nonempty_of_irreducibleCloseds T hU₁ hU₂,
    fun To hle _ hbc t ↦ ?_⟩
  set y := curveOpenInclusion sY To t with hy
  set yY := (t.hom ≫ To.ι ≫ curveι T) (default : Spec (.of ℂ)) with hyY
  have hrange : Set.range (curveι T).base = (T : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hyU : yY ∈ ((U₁ ⊓ U₂ : Y.Opens) : Set Y) := hle (t.hom.base (default : Spec (.of ℂ))).2
  have hyT : yY ∈ (T : Set Y) := hrange ▸ ⟨_, rfl⟩
  have hcp : (IsLocalRing.closedPoint ℂ : Spec (.of ℂ)) = default := Subsingleton.elim _ _
  -- the chart and the slice through `F_t`
  let b : UnderlyingSpace ℂ Y := ComplexPoints.homeomorphUnderlyingSpace (X := Y) y
  have hbmem : b ∈ UnderlyingSpace.pointsOver (K := ℂ) ((U₂ : Set Y) ∩ T) := by
    show (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∈ (U₂ : Set Y) ∩ T
    have e : (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) = yY :=
      congrArg _ (Subsingleton.elim _ _)
    rw [e]
    exact ⟨hyU.2, hyT⟩
  let Ch := (hch b hbmem).some
  have hbX : (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ) ∈ (Ch.X : Set Y) :=
    Ch.mem_X
  obtain ⟨M, sM, iW, j, b₀, ⟨hcx, hvar, hns, hqp, hsmo⟩, hiW, hcomp, hj, hjc, hpb, -⟩ :=
    exists_slice_variety hM hT To t Ch hbX
  letI : M.Over (Spec (.of ℂ)) := ⟨sM⟩
  haveI := hcx
  haveI := hvar
  haveI : IsSeparated (M ↘ Spec (.of ℂ)) := hns
  haveI : SmoothOfRelativeDimension 3 (M ↘ Spec (.of ℂ)) := hsmo
  haveI := hiW
  haveI := hjc
  haveI := Ch.sepW
  have hinj : Function.Injective (iW ≫ Ch.W.ι).base := fun a a' h ↦
    iW.isClosedEmbedding.injective (Ch.W.ι.isOpenEmbedding.injective h)
  obtain ⟨V₀, hyV₀, hsep⟩ := exists_separating_open hM To t Ch sM iW j b₀ hcomp hj hpb hinj
  haveI : IsSeparated (M ↘ Spec (.of ℂ)) := by
    change IsSeparated sM
    rw [← hcomp, ← Category.assoc, ← Category.assoc, Category.assoc (iW ≫ Ch.W.ι) r sY]
    rw [hM.comp_eq, Category.assoc]
    infer_instance
  have hjs : j ≫ sM = pointFibre sY r To t ↘ Spec (.of ℂ) := by
    calc j ≫ sM = (j ≫ iW ≫ Ch.W.ι) ≫ r ≫ sY := by rw [← hcomp]; simp only [Category.assoc]
      _ = _ := by rw [hj]; exact pointFibreFst_comp_structure sY r To t
  haveI : IsProper (j ≫ M ↘ Spec (.of ℂ)) := by
    change IsProper (j ≫ sM)
    rw [hjs]
    change IsProper (pullback.snd r (t.hom ≫ To.ι ≫ curveι T))
    infer_instance
  haveI := finite_irreducibleComponents_pointFibre hM To t
  have hdim2 := topologicalKrullDim_pointFibre_le hM hT To t
    (fun E A hA ↦ (Hdisj yY ⟨hyU.1, hyT⟩ E).2 A hA)
  have hgM : (iW ≫ Ch.W.ι) ≫ r ≫ sY = sM := by rw [Category.assoc]; exact hcomp
  let gM : analyticSpace sM ⟶ analyticSpace (r ≫ sY) := analyticMap (iW ≫ Ch.W.ι) hgM
  have hpt : ∀ y', gM (analyticMap j hjs y') = pointFibreAnalyticMap sY r To t y' := fun y' ↦
    ComplexPoints.ext (by
      change (y'.hom ≫ j) ≫ iW ≫ Ch.W.ι = y'.hom ≫ pointFibreFst sY r To t
      rw [Category.assoc, hj])
  -- the rank bound
  rw [← Nat.cast_card]
  refine rank_le fun s hs ↦ ?_
  have hex : ∀ i : s, ∃ (V : Opens (analyticSpace sY)) (hV : y ∈ V)
      (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
      classGerm sY r To t hV α = (i : LinearMap.ker
        (localSystemRestrictionFibre sY hM.isBiregular To t).hom).1 ∧
      (rationalCohomologyMap (X' := TopCat.of ({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∉
          (F.supp : Set Z)} : Set (preimageSpace (resolutionAnalyticMap sY r) V)))
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α = 0 := by
    intro i
    obtain ⟨V, hV, α, hα⟩ := exists_classGerm_eq To t (i : LinearMap.ker
      (localSystemRestrictionFibre sY hM.isBiregular To t).hom).1
    obtain ⟨V', hV', hle', h0⟩ := exists_le_compl_eq_zero hM To t hV α
      (by rw [hα]; exact i.1.2)
    exact ⟨V', hV', _, (classGerm_restrict sY r To t hle' hV' α).symm.trans hα, h0⟩
  choose V hV α hα h0 using hex
  let Vs : Opens (analyticSpace sY) := V₀ ⊓ (Finset.univ : Finset s).inf V
  have hyVs : y ∈ Vs := by
    refine ⟨hyV₀, ?_⟩
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    simp only [Function.comp_apply, Set.iInf_eq_iInter, Set.mem_iInter]
    exact fun i _ ↦ hV i
  have hleV : ∀ i, Vs ≤ V i := fun i ↦ inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  let β : s → rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) Vs) 2 := fun i ↦
    (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY r) (hleV i)) 2).hom (α i)
  let Φ : Set (preimageSpace (resolutionAnalyticMap sY r) Vs) :=
    {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (F.supp : Set Z)}
  have hβ : ∀ i, (rationalCohomologyMap (X' := TopCat.of (Φᶜ : Set _))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom (β i) = 0 := by
    intro i
    let m : TopCat.of (Φᶜ : Set _) ⟶ TopCat.of ({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∉
        (F.supp : Set Z)} : Set (preimageSpace (resolutionAnalyticMap sY r) (V i))) :=
      TopCat.ofHom ⟨fun z ↦ ⟨⟨z.1.1, hleV i z.1.2⟩, z.2⟩, by fun_prop⟩
    have hfac : (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of (Φᶜ : Set _) ⟶ _) ≫ preimageInclusion (resolutionAnalyticMap sY r) (hleV i) =
        m ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := rfl
    change (rationalCohomologyMap _ 2).hom ((rationalCohomologyMap _ 2).hom (α i)) = 0
    rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hfac, rationalCohomologyMap_comp,
      ModuleCat.comp_apply, h0, map_zero]
  -- the slice over `Vs`
  let U' : Opens (analyticSpace (M ↘ Spec (.of ℂ))) :=
    ⟨gM ⁻¹' (resolutionAnalyticMap sY r ⁻¹' (Vs : Set (analyticSpace sY))),
      (Vs.isOpen.preimage (resolutionAnalyticMap sY r).hom.continuous).preimage
        gM.hom.continuous⟩
  let g : TopCat.of U' ⟶ preimageSpace (resolutionAnalyticMap sY r) Vs :=
    TopCat.ofHom ⟨fun x ↦ ⟨gM x.1, x.2⟩, (gM.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let Dset : Set (TopCat.of U') :=
    {x | x.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range j.base}
  have hg : Dsetᶜ ⊆ g ⁻¹' Φᶜ := by
    intro x hx hxF
    refine hx (hsep x.1 ⟨resolutionAnalyticMap sY r (gM x.1), x.2.1, ?_⟩ hxF)
    unfold ComplexPoints.toScheme
    rw [hcp]
    change ((x.1.hom ≫ iW ≫ Ch.W.ι) ≫ r).base default = _
    simp only [Category.assoc]
    exact congrArg _ (Subsingleton.elim _ _)
  have hmemq : ∀ y' : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
      analyticMap j hjs y' ∈ U' := by
    intro y'
    change resolutionAnalyticMap sY r (gM (analyticMap j hjs y')) ∈ Vs
    rw [hpt, resolutionAnalyticMap_pointFibreAnalyticMap]
    exact hyVs
  let q : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)) ⟶ TopCat.of U' :=
    TopCat.ofHom ⟨fun y' ↦ ⟨analyticMap j hjs y', hmemq y'⟩,
      ((analyticMap j hjs).hom.continuous).subtype_mk hmemq⟩
  have hq : q ≫ g = pointFibreInclusion sY r To t hyVs :=
    TopCat.ext fun y' ↦ Subtype.ext (hpt y')
  let L : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) Vs) 2 →ₗ[ℚ]
      resolutionLocalSystemFibre sY r To t := (stalkToPullbackStalk (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY r 2) t).hom ∘ₗ
      (higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hyVs).hom
  have hLβ : ∀ i, L (β i) = (i : LinearMap.ker
      (localSystemRestrictionFibre sY hM.isBiregular To t).hom).1 := fun i ↦
    (classGerm_restrict sY r To t (hleV i) hyVs (α i)).symm.trans (hα i)
  have hli : LinearIndependent ℚ (fun i ↦ L (β i)) := by
    have := hs.map' (LinearMap.ker _).subtype (Submodule.ker_subtype _)
    have e : (fun i ↦ L (β i)) = (LinearMap.ker
        (localSystemRestrictionFibre sY hM.isBiregular To t).hom).subtype ∘
          (fun i : s ↦ (i : LinearMap.ker
            (localSystemRestrictionFibre sY hM.isBiregular To t).hom)) := funext hLβ
    rw [e]
    exact this
  have hcard := card_le_rank_cohomologyWithSupports Φ Dset g hg q _ hq L
    (fun a ha ↦ classGerm_eq_zero_of_pointFibreInclusion hM hbc t hyVs a ha) β hβ hli
  have hU' : ∀ x : analyticSpace (M ↘ Spec (.of ℂ)),
      x.hom.base (IsLocalRing.closedPoint ℂ) ∈ Set.range j.base → x ∈ U' := by
    rintro x ⟨p, hp⟩
    change resolutionAnalyticMap sY r (gM x) ∈ Vs
    have hx : resolutionAnalyticMap sY r (gM x) = y := by
      refine complexPoints_ext_of_base (sX := sY) ?_
      change ((x.hom ≫ iW ≫ Ch.W.ι) ≫ r).base (IsLocalRing.closedPoint ℂ) =
        (t.hom ≫ To.ι ≫ curveι T).base (IsLocalRing.closedPoint ℂ)
      calc ((x.hom ≫ iW ≫ Ch.W.ι) ≫ r).base (IsLocalRing.closedPoint ℂ)
          = (iW ≫ Ch.W.ι ≫ r).base (j.base p) := by
            rw [hp]; rfl
        _ = ((j ≫ iW ≫ Ch.W.ι) ≫ r).base p := by
            simp only [Category.assoc, Scheme.Hom.comp_apply]
        _ = (pointFibreSnd sY r To t ≫ t.hom ≫ To.ι ≫ curveι T).base p := by
            rw [hj, pointFibreFst_comp]
        _ = _ := by
            rw [Scheme.Hom.comp_apply,
              Subsingleton.elim ((pointFibreSnd sY r To t).base p) (IsLocalRing.closedPoint ℂ)]
    rw [hx]
    exact hyVs
  have hrk := rank_cohomologyWithSupports_range_le' hqp j hdim2 U' hU'
  have := hcard.trans hrk
  rw [Fintype.card_coe] at this
  exact_mod_cast this

/-- **The local classes form a basis of the kernel.** Over adapted opens inside a suitable open
`U` of `Y` meeting `T`, the germs of one local class along each component of `F_t` form a basis
of `ker (r_t : 𝒲_t ⟶ 𝒱_{T,t})`. -/
private theorem exists_open_linearIndependent_classGerm
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U → IsAdaptedOpen sY r To →
        BaseChangeInjective sY r To →
        ∀ t (c : irreducibleComponents (pointFibre sY r To t) →
            resolutionLocalSystemFibre sY r To t),
          (∀ S, ∃ (E : Mori.PrimeDivisor Z) (V : Opens (analyticSpace sY))
            (hV : curveOpenInclusion sY To t ∈ V)
            (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
            E ∈ F.support ∧ IsLocalClass hM To t S E hV α ∧ c S = classGerm sY r To t hV α) →
          LinearIndependent ℚ c ∧ Submodule.span ℚ (Set.range c) =
            LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom := by
  obtain ⟨U₁, h₁, H₁⟩ := exists_open_linearIndependent_classGerm_aux hM hT hdim
  obtain ⟨U₂, h₂, H₂⟩ := exists_open_rank_ker_le hM hT hdim
  refine ⟨U₁ ⊓ U₂, inter_inter_nonempty_of_irreducibleCloseds T h₁ h₂,
    fun To hle hTo hbc t c hc ↦ ?_⟩
  have hli := H₁ To (hle.trans (Scheme.Hom.preimage_mono _ inf_le_left)) hTo t c hc
  have hrk := H₂ To (hle.trans (Scheme.Hom.preimage_mono _ inf_le_right)) hTo hbc t
  have hle' : Submodule.span ℚ (Set.range c) ≤
      LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom := by
    rw [Submodule.span_le]
    rintro _ ⟨S, rfl⟩
    obtain ⟨E, V, hV, α, hE, hα, hcS⟩ := hc S
    rw [hcS]
    exact classGerm_mem_ker hM To t hE hα
  haveI := finite_irreducibleComponents_pointFibre hM To t
  haveI : FiniteDimensional ℚ
      (LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom) := by
    refine Module.rank_lt_aleph0_iff.1 (hrk.trans_lt ?_)
    exact Cardinal.lt_aleph0_of_finite _
  have hspan : Module.rank ℚ (Submodule.span ℚ (Set.range c)) =
      Cardinal.mk (irreducibleComponents (pointFibre sY r To t)) := by
    rw [rank_span hli, Cardinal.mk_range_eq c hli.injective]
  haveI : FiniteDimensional ℚ (Submodule.span ℚ (Set.range c)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range c)
  refine ⟨hli, Submodule.eq_of_le_of_finrank_le hle' ?_⟩
  have := hrk.trans hspan.symm.le
  rw [← Module.finrank_eq_rank', ← Module.finrank_eq_rank'] at this
  exact_mod_cast this

/-- The three clauses `exists_open_isLocalClass`, `exists_open_classGerm_eq` and
`exists_open_linearIndependent_classGerm` hold together over one open `U` meeting `T`. -/
private theorem exists_open_localClasses
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U → IsAdaptedOpen sY r To →
        BaseChangeInjective sY r To →
        (∀ t, ∃ (O : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY))) (_ : t ∈ O)
          (e : ∀ t' ∈ O, irreducibleComponents (pointFibre sY r To t) ≃
            irreducibleComponents (pointFibre sY r To t')),
          ∀ (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z),
            E ∈ F.support → (S : Set (pointFibre sY r To t)) ⊆
              (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) →
            ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
              (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
              IsLocalClass hM To t S E hV α ∧
              ∀ t' (ht' : t' ∈ O), ∃ hV' : curveOpenInclusion sY To t' ∈ V,
                IsLocalClass hM To t' (e t' ht' S) E hV' α) ∧
        (∀ t (S : irreducibleComponents (pointFibre sY r To t)) (E E' : Mori.PrimeDivisor Z)
          (V V' : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
          (hV' : curveOpenInclusion sY To t ∈ V')
          (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
          (α' : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V') 2),
          E ∈ F.support → E' ∈ F.support →
          IsLocalClass hM To t S E hV α → IsLocalClass hM To t S E' hV' α' →
          classGerm sY r To t hV α = classGerm sY r To t hV' α') ∧
        (∀ t (c : irreducibleComponents (pointFibre sY r To t) →
            resolutionLocalSystemFibre sY r To t),
          (∀ S, ∃ (E : Mori.PrimeDivisor Z) (V : Opens (analyticSpace sY))
            (hV : curveOpenInclusion sY To t ∈ V)
            (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
            E ∈ F.support ∧ IsLocalClass hM To t S E hV α ∧ c S = classGerm sY r To t hV α) →
          LinearIndependent ℚ c ∧ Submodule.span ℚ (Set.range c) =
            LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom) := by
  obtain ⟨U₁, h₁, H₁⟩ := exists_open_isLocalClass hM hT hdim
  obtain ⟨U₂, h₂, H₂⟩ := exists_open_classGerm_eq hM hT hdim
  obtain ⟨U₃, h₃, H₃⟩ := exists_open_linearIndependent_classGerm hM hT hdim
  have hirr := T.isIrreducible
  obtain ⟨y, hyT, hy₁, hy₂⟩ := hirr.2 _ _ U₁.isOpen U₂.isOpen
    (by obtain ⟨y, hy⟩ := h₁; exact ⟨y, hy.2, hy.1⟩) (by obtain ⟨y, hy⟩ := h₂; exact ⟨y, hy.2, hy.1⟩)
  obtain ⟨z, hzT, hz₁₂, hz₃⟩ := hirr.2 _ _ (U₁ ⊓ U₂).isOpen U₃.isOpen
    ⟨y, hyT, hy₁, hy₂⟩ (by obtain ⟨y, hy⟩ := h₃; exact ⟨y, hy.2, hy.1⟩)
  refine ⟨U₁ ⊓ U₂ ⊓ U₃, ⟨z, ⟨hz₁₂, hz₃⟩, hzT⟩, fun To hle hTo hbc ↦ ⟨?_, ?_, ?_⟩⟩
  · exact H₁ To (hle.trans (Scheme.Hom.preimage_mono _ (inf_le_left.trans inf_le_left))) hTo
  · exact H₂ To (hle.trans (Scheme.Hom.preimage_mono _ (inf_le_left.trans inf_le_right))) hTo
  · exact H₃ To (hle.trans (Scheme.Hom.preimage_mono _ inf_le_right)) hTo hbc

end LocalClass

/-! ### Sections of kernels and of inverse images -/

/-- Sections of the kernel of a morphism of sheaves of `ℚ`-vector spaces: a section killed by
the morphism comes from the kernel. -/
private theorem exists_kernel_ι_app {X : TopCat.{0}} {A B : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (f : A ⟶ B) (O : Opens X) (s : ((TopCat.Sheaf.forget _ _).obj A).obj (op O))
    (hs : ((TopCat.Sheaf.forget _ _).map f).app (op O) s = 0) :
    ∃ σ : ((TopCat.Sheaf.forget _ _).obj (Limits.kernel f)).obj (op O),
      ((TopCat.Sheaf.forget _ _).map (Limits.kernel.ι f)).app (op O) σ = s := by
  haveI : PreservesLimits (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X) := inferInstance
  haveI : (TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_preserves_terminal_object
  haveI : PreservesLimits ((CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{0} ℚ)).obj
    (op O)) := inferInstance
  haveI : ((CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{0} ℚ)).obj
    (op O)).PreservesZeroMorphisms := inferInstance
  let G := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) X ⋙
    (CategoryTheory.evaluation (Opens X)ᵒᵖ (ModuleCat.{0} ℚ)).obj (op O)
  haveI : G.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_comp _ _
  haveI : PreservesLimits G := comp_preservesLimits _ _
  let S := ShortComplex.mk (Limits.kernel.ι f) f (Limits.kernel.condition f)
  have hS : Limits.IsLimit (Limits.KernelFork.ofι (S.map G).f (S.map G).zero) :=
    Limits.isLimitForkMapOfIsLimit' G S.zero (Limits.kernelIsKernel f)
  obtain ⟨he, -⟩ := (S.map G).exact_and_mono_f_iff_f_is_kernel.2 ⟨hS⟩
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 he
  have : s ∈ LinearMap.ker (S.map G).g.hom := hs
  rw [← h] at this
  exact this

/-- The germ at `x` of the inverse image of a section `s` of `𝒢` over `V ∋ f x` is the image of
the germ of `s` under `𝒢_{f x} ⟶ (f^*𝒢)_x`. -/
private theorem germ_unit_app {X Y' : TopCat.{0}} (f : X ⟶ Y')
    (𝒢 : TopCat.Sheaf (ModuleCat.{0} ℚ) Y') (V : Opens Y') (s : 𝒢.obj.obj (op V)) (x : X)
    (hx : f x ∈ V) :
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝒢).presheaf.germ ((Opens.map f).obj V) x hx
        (((TopCat.Sheaf.forget _ _).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app 𝒢)).app
          (op V) s) =
      (stalkToPullbackStalk f 𝒢 x).hom (𝒢.presheaf.germ V (f x) hx s) := by
  have h1 := TopCat.Presheaf.stalkFunctor_map_germ_apply V (f x) hx ((TopCat.Sheaf.forget _ _).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app 𝒢)) s
  have h2 := ConcreteCategory.congr_hom (TopCat.Presheaf.stalkPushforward_germ (ModuleCat.{0} ℚ) f
    ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝒢)) V x hx)
    (((TopCat.Sheaf.forget _ _).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app 𝒢)).app (op V) s)
  exact h2.symm.trans (congrArg (TopCat.Presheaf.stalkPushforward (ModuleCat.{0} ℚ) f
    ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj 𝒢)) x).hom
    h1.symm)

/-- **The component basis along `T`.** Over adapted opens inside a suitable open `U` of `Y`
meeting `T`, the stalk of `ker r` at `t` has a basis indexed by the components `S` of `F_t`,
matched at nearby points by local sections, whose vector at `S` is the germ of the local class
of the exceptional component through `S`. -/
private theorem exists_open_componentBasis
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ U : Y.Opens, ((U : Set Y) ∩ T).Nonempty ∧
      ∀ To : (curveScheme T).Opens, To ≤ (curveι T) ⁻¹ᵁ U → IsAdaptedOpen sY r To →
        BaseChangeInjective sY r To →
        ∃ b : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
          Module.Basis (irreducibleComponents (pointFibre sY r To t)) ℚ
            (((TopCat.Sheaf.forget _ _).obj (Limits.kernel (localSystemRestriction sY hM.isBiregular To))).stalk t),
          -- permutation monodromy: the bases are matched by local sections
          (∀ t, ∃ (O : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY))) (_ : t ∈ O)
            (σ : irreducibleComponents (pointFibre sY r To t) →
              ((TopCat.Sheaf.forget _ _).obj (Limits.kernel (localSystemRestriction sY hM.isBiregular To))).obj (op O)),
            ∀ t' (ht' : t' ∈ O), ∃ e : irreducibleComponents (pointFibre sY r To t) ≃
                irreducibleComponents (pointFibre sY r To t'),
              ∀ S, ((TopCat.Sheaf.forget _ _).obj (Limits.kernel (localSystemRestriction sY hM.isBiregular To))).germ O t' ht' (σ S) = b t' (e S)) ∧
          -- the basis vector of `S ⊆ Fᵢ` goes to the local class of `Fᵢ` along `S`
          (∀ t (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z),
            E ∈ F.support → (S : Set (pointFibre sY r To t)) ⊆
              (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) →
            ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
              (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
              (G : Set (preimageSpace (resolutionAnalyticMap sY r) V)),
              IsClosed G ∧
              (∃ O : Set (preimageSpace (resolutionAnalyticMap sY r) V), IsOpen O ∧
                G = O ∩ {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)}) ∧
              (∀ y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
                pointFibreInclusion sY r To t hV y ∈ G ↔
                  y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t))) ∧
              (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY r 2)
                  t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α) =
                ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
                  ((TopCat.Sheaf.forget _ _).map (Limits.kernel.ι (localSystemRestriction sY hM.isBiregular To)))).hom (b t S) ∧
              (rationalCohomologyMap (X' := TopCat.of (Gᶜ : Set _))
                (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α = 0 ∧
              ∃ _ : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
                  (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)),
                (rationalCohomologyMap
                    (X' := TopCat.of (({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈
                      (E.support : Set Z)} \ G)ᶜ :
                        Set (preimageSpace (resolutionAnalyticMap sY r) V)))
                    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α =
                  (rationalCohomologyMap
                    (TopCat.ofHom (X := TopCat.of (({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈
                      (E.support : Set Z)} \ G)ᶜ :
                        Set (preimageSpace (resolutionAnalyticMap sY r) V)))
                      (Y := analyticSpace (r ≫ sY))
                      ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
                      analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) 2).hom
                    (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
                      (algebraicFirstChernClass
                        (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))))) := by
  classical
  obtain ⟨U, hUT, hU⟩ := exists_open_localClasses hM hT hdim
  refine ⟨U, hUT, fun To hle hTo hbc ↦ ?_⟩
  obtain ⟨hprop, huniq, hbasis⟩ := hU To hle hTo hbc
  have hk := stalk_kernel_ι (localSystemRestriction sY hM.isBiregular To)
  let φ := fun t : analyticSpace (To.ι ≫ curveι T ≫ sY) ↦
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map ((TopCat.Sheaf.forget _ _).map
      (Limits.kernel.ι (localSystemRestriction sY hM.isBiregular To)))).hom
  have hrange : ∀ t, LinearMap.range (φ t) =
      LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom := fun t ↦ (hk t).2
  have hinj : ∀ t, Function.Injective (φ t) := fun t ↦ (hk t).1
  -- one local class per component
  have hex : ∀ t (S : irreducibleComponents (pointFibre sY r To t)),
      ∃ (E : Mori.PrimeDivisor Z) (V : Opens (analyticSpace sY))
        (hV : curveOpenInclusion sY To t ∈ V)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2),
        E ∈ F.support ∧ (S : Set (pointFibre sY r To t)) ⊆
          (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) ∧
        IsLocalClass hM To t S E hV α := by
    intro t S
    obtain ⟨E, hE, hS⟩ := exists_mem_support_subset_preimage hM hT To t S
    obtain ⟨O, -, e, h⟩ := hprop t
    obtain ⟨V, hV, α, hα, -⟩ := h S E hE hS
    exact ⟨E, V, hV, α, hE, hS, hα⟩
  choose E V hV α hE hS hα using hex
  let c : ∀ t, irreducibleComponents (pointFibre sY r To t) →
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).obj
        ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY r To)) := fun t S ↦ classGerm sY r To t (hV t S) (α t S)
  have hc : ∀ t, LinearIndependent ℚ (c t) ∧ Submodule.span ℚ (Set.range (c t)) =
      LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom := fun t ↦
    hbasis t (c t) fun S ↦ ⟨E t S, V t S, hV t S, α t S, hE t S, hα t S, rfl⟩
  -- the germ of any local class along `S` is `c t S`
  have hgerm : ∀ t S (E' : Mori.PrimeDivisor Z) (V' : Opens (analyticSpace sY))
      (hV' : curveOpenInclusion sY To t ∈ V')
      (α' : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V') 2),
      E' ∈ F.support → IsLocalClass hM To t S E' hV' α' →
      classGerm sY r To t hV' α' = c t S := fun t S E' V' hV' α' hE' h ↦
    huniq t S E' (E t S) V' (V t S) hV' (hV t S) α' (α t S) hE' (hE t S) h (hα t S)
  have hker : ∀ t S, c t S ∈ LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom :=
    fun t S ↦ (hc t).2.le (Submodule.subset_span ⟨S, rfl⟩)
  have hmem : ∀ t S, c t S ∈ LinearMap.range (φ t) := fun t S ↦ by
    rw [hrange]; exact hker t S
  choose b' hb' using hmem
  have hcomp : ∀ t, φ t ∘ b' t = c t := fun t ↦ funext (hb' t)
  have hli : ∀ t, LinearIndependent ℚ (b' t) := fun t ↦
    LinearIndependent.of_comp (φ t) (by rw [hcomp]; exact (hc t).1)
  have hsp : ∀ t, ⊤ ≤ Submodule.span ℚ (Set.range (b' t)) := by
    intro t x _
    have hx : φ t x ∈ Submodule.span ℚ (Set.range (c t)) := by
      rw [(hc t).2, ← hrange]; exact ⟨x, rfl⟩
    have hr : Set.range (c t) = (φ t) '' Set.range (b' t) :=
      Set.ext fun y ↦ ⟨fun ⟨S, hS⟩ ↦ ⟨b' t S, ⟨S, rfl⟩, (hb' t S).trans hS⟩,
        fun ⟨_, ⟨S, hS⟩, h⟩ ↦ ⟨S, (hb' t S).symm.trans (hS ▸ h)⟩⟩
    rw [hr, ← Submodule.map_span] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rwa [hinj t hxy] at hy
  let b := fun t ↦ Module.Basis.mk (hli t) (hsp t)
  have hφb : ∀ t S, φ t (b t S) = c t S := fun t S ↦ by
    simp only [b, Module.Basis.mk_apply]; exact hb' t S
  refine ⟨b, fun t ↦ ?_, fun t S E' hE' hS' ↦ ?_⟩
  · obtain ⟨O, htO, e, h⟩ := hprop t
    have hsec : ∀ S, ∃ σ : ((TopCat.Sheaf.forget _ _).obj
        (Limits.kernel (localSystemRestriction sY hM.isBiregular To))).obj (op O),
        ∀ t' (ht' : t' ∈ O), ((TopCat.Sheaf.forget _ _).obj
          (Limits.kernel (localSystemRestriction sY hM.isBiregular To))).germ O t' ht' σ =
            b t' (e t' ht' S) := by
      intro S
      obtain ⟨V', hV', α', -, hα'⟩ := h S (E t S) (hE t S) (hS t S)
      have hO : O ≤ (Opens.map (curveOpenInclusion sY To)).obj V' := fun t' ht' ↦
        (hα' t' ht').1
      let s : ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY r To)).obj (op O) :=
        ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY r To)).map (homOfLE hO).op
          (((TopCat.Sheaf.forget _ _).map
            ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ)
              (curveOpenInclusion sY To)).unit.app (resolutionHigherDirectImage sY r 2))).app
            (op V')
            ((toSheafify (Opens.grothendieckTopology _)
              (directImagePresheaf (resolutionAnalyticMap sY r) 2)).app (op V') α'))
      have hs : ∀ t' (ht' : t' ∈ O),
          ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY r To)).germ O t' ht' s =
            c t' (e t' ht' S) := by
        intro t' ht'
        rw [← hgerm t' (e t' ht' S) (E t S) V' (hα' t' ht').1 α' (hE t S) (hα' t' ht').2]
        refine (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ?_
        refine (germ_unit_app (curveOpenInclusion sY To) (resolutionHigherDirectImage sY r 2)
          V' _ t' (hα' t' ht').1).trans ?_
        congr 1
        exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V' _ (hα' t' ht').1
          (toSheafify (Opens.grothendieckTopology _)
            (directImagePresheaf (resolutionAnalyticMap sY r) 2)) α').symm
      have hzero : ((TopCat.Sheaf.forget _ _).map
          (localSystemRestriction sY hM.isBiregular To)).app (op O) s = 0 := by
        refine TopCat.Presheaf.section_ext (curveLocalSystem sY To) O _ _ fun t' ht' ↦ ?_
        have := TopCat.Presheaf.stalkFunctor_map_germ_apply O t' ht'
          ((TopCat.Sheaf.forget _ _).map (localSystemRestriction sY hM.isBiregular To)) s
        refine (this.symm.trans ?_).trans (map_zero _).symm
        change (localSystemRestrictionFibre sY hM.isBiregular To t').hom
          (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY r To)).germ O t' ht' s) = 0
        rw [hs t' ht']
        exact hker t' _
      obtain ⟨σ, hσ⟩ := exists_kernel_ι_app _ O s hzero
      refine ⟨σ, fun t' ht' ↦ hinj t' ?_⟩
      rw [hφb, ← hs t' ht', ← hσ]
      exact TopCat.Presheaf.stalkFunctor_map_germ_apply O t' ht' _ σ
    choose σ hσ using hsec
    exact ⟨O, htO, σ, fun t' ht' ↦ ⟨e t' ht', fun S ↦ hσ S t' ht'⟩⟩
  · obtain ⟨O, -, e, h⟩ := hprop t
    obtain ⟨V', hV', α', hα', -⟩ := h S E' hE' hS'
    obtain ⟨G, hG1, hG2, hG3, hG4, hG5⟩ := hα'.properties
    exact ⟨V', hV', α', G, hG1, hG2, hG3,
      (hgerm t S E' V' hV' α' hE' hα').trans (hφb t S).symm, hG4, hG5⟩

private theorem solution
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ T₀ : (curveScheme T).Opens, IsAdaptedOpen sY r T₀ ∧
      ∀ To : (curveScheme T).Opens, To ≤ T₀ → IsAdaptedOpen sY r To →
      ∃ (P : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace (To.ι ≫ curveι T ≫ sY)))
        (φ : P ⟶ resolutionLocalSystem sY r To)
        (b : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
          Module.Basis (irreducibleComponents (pointFibre sY r To t)) ℚ
            (((TopCat.Sheaf.forget _ _).obj P).stalk t)),
        IsLocalSystem P ∧
        -- exactness at `𝒫`, `𝒲` and `𝒱_T`, stalkwise
        (∀ t, Function.Injective
          ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
            ((TopCat.Sheaf.forget _ _).map φ)).hom) ∧
        (∀ t, LinearMap.range ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
            ((TopCat.Sheaf.forget _ _).map φ)).hom =
          LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom) ∧
        (∀ t, Function.Surjective (localSystemRestrictionFibre sY hM.isBiregular To t).hom) ∧
        -- permutation monodromy: the bases are matched by local sections
        (∀ t, ∃ (O : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY))) (_ : t ∈ O)
          (σ : irreducibleComponents (pointFibre sY r To t) →
            ((TopCat.Sheaf.forget _ _).obj P).obj (op O)),
          ∀ t' (ht' : t' ∈ O), ∃ e : irreducibleComponents (pointFibre sY r To t) ≃
              irreducibleComponents (pointFibre sY r To t'),
            ∀ S, ((TopCat.Sheaf.forget _ _).obj P).germ O t' ht' (σ S) = b t' (e S)) ∧
        -- the basis vector of `S ⊆ Fᵢ` goes to the local class of `Fᵢ` along `S`
        (∀ t (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z),
          E ∈ F.support → (S : Set (pointFibre sY r To t)) ⊆
            (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) →
          ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
            (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
            (G : Set (preimageSpace (resolutionAnalyticMap sY r) V)),
            IsClosed G ∧
            (∃ O : Set (preimageSpace (resolutionAnalyticMap sY r) V), IsOpen O ∧
              G = O ∩ {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)}) ∧
            (∀ y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
              pointFibreInclusion sY r To t hV y ∈ G ↔
                y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t))) ∧
            (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY r 2)
                t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α) =
              ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
                ((TopCat.Sheaf.forget _ _).map φ)).hom (b t S) ∧
            (rationalCohomologyMap (X' := TopCat.of (Gᶜ : Set _))
              (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α = 0 ∧
            ∃ _ : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
                (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)),
              (rationalCohomologyMap
                  (X' := TopCat.of (({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈
                    (E.support : Set Z)} \ G)ᶜ :
                      Set (preimageSpace (resolutionAnalyticMap sY r) V)))
                  (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α =
                (rationalCohomologyMap
                  (TopCat.ofHom (X := TopCat.of (({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈
                    (E.support : Set Z)} \ G)ᶜ :
                      Set (preimageSpace (resolutionAnalyticMap sY r) V)))
                    (Y := analyticSpace (r ≫ sY))
                    ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
                    analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) 2).hom
                  (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
                    (algebraicFirstChernClass
                      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))))) ∧
        -- dually, `𝒱_{T,t}^*` is the annihilator of the divisor classes in `𝒲_t^*`
        (∀ t, LinearMap.range (localSystemRestrictionFibre sY hM.isBiregular To t).hom.dualMap =
          (LinearMap.range ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
            ((TopCat.Sheaf.forget _ _).map φ)).hom).dualAnnihilator) := by
  classical
  -- an open `U` of `Y` meeting `T` over which the component basis exists
  obtain ⟨U, hUT, hcomp⟩ := exists_open_componentBasis hM hT hdim
  -- an adapted open of `T` inside `U`
  have hLS : IsLocalSetting sY 0 T r := ⟨hM.isQFactorial, hM.isProjectiveVariety,
    hM.topologicalKrullDim_eq, hM.isTerminalVariety, hdim, hT, hM.isResolution, hM.isBiregular⟩
  obtain ⟨⟨T₁, hT₁⟩, hshrink⟩ := hLS.exists_isAdaptedOpen_and_isAdaptedOpen_of_le
  have hrange : Set.range (curveι T).base = (T : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  haveI : IrreducibleSpace (curveScheme T) := by
    have h : IsIrreducible (Set.range (curveι T).base) := hrange ▸ T.isIrreducible
    haveI := Subtype.irreducibleSpace h
    obtain ⟨_, x, -⟩ := h.nonempty
    haveI : Nonempty (curveScheme T) := ⟨x⟩
    exact ((curveι T).isClosedEmbedding.isEmbedding.toHomeomorph).isOpenEmbedding.irreducibleSpace
  -- proper base change on germs holds over an open `T₂` of `T`
  obtain ⟨T₂, hT₂, -, hbcT₂⟩ := hLS.exists_isLocalSystem_higherDirectImage
  let T₀ : (curveScheme T).Opens := T₁ ⊓ (curveι T) ⁻¹ᵁ U ⊓ T₂
  have hne : (T₀ : Set (curveScheme T)).Nonempty := by
    obtain ⟨y, hyU, hyT⟩ := hUT
    obtain ⟨z, rfl⟩ : y ∈ Set.range (curveι T).base := hrange ▸ hyT
    obtain ⟨w, hw1, hw2⟩ := hT₁.dense.inter_open_nonempty _ ((curveι T) ⁻¹ᵁ U).isOpen ⟨z, hyU⟩
    obtain ⟨v, hv₁, hv₂⟩ := (IrreducibleSpace.isIrreducible_univ (curveScheme T)).2 _ _
      (T₁ ⊓ (curveι T) ⁻¹ᵁ U).isOpen T₂.isOpen ⟨w, trivial, hw2, hw1⟩
      (by obtain ⟨v, hv⟩ := hT₂; exact ⟨v, trivial, hv⟩)
    exact ⟨v, hv₂.1, hv₂.2⟩
  have hT₀ : IsAdaptedOpen sY r T₀ := by
    have hirr : IsIrreducible (T₀ : Set (curveScheme T)) :=
      ⟨hne, (IrreducibleSpace.isIrreducible_univ _).2.open_subset T₀.isOpen
        (Set.subset_univ _)⟩
    exact hshrink T₁ T₀ hT₁ (inf_le_left.trans inf_le_left)
      (isConnected_iff_connectedSpace.1 hirr.isConnected) (T₀.isOpen.dense hne)
  refine ⟨T₀, hT₀, fun To hle hTo ↦ ?_⟩
  have hbc : BaseChangeInjective sY r To := by
    intro t V hV α hα
    obtain ⟨e, he⟩ := (hbcT₂ To (hle.trans inf_le_right) 2).1.2 t
    have h1 := congrArg (fun φ ↦ φ.hom α) (he V hV)
    simp only [ModuleCat.comp_apply] at h1
    have hinj : Function.Injective e.hom.hom :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    exact hinj ((h1.trans hα).trans (map_zero _).symm)
  -- `r` is onto on stalks
  have hsurj := surjective_localSystemRestrictionFibre hLS hTo
  haveI := hTo.smooth
  haveI := locallyConnectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  have hloc := isLocalSystem_kernel (localSystemRestriction sY hM.isBiregular To)
    hTo.isLocalSystem_resolution hTo.isLocalSystem
  obtain ⟨b, hperm, hcls⟩ := hcomp To (hle.trans (inf_le_left.trans inf_le_right)) hTo hbc
  have hk := stalk_kernel_ι (localSystemRestriction sY hM.isBiregular To)
  refine ⟨Limits.kernel (localSystemRestriction sY hM.isBiregular To),
    Limits.kernel.ι _, b, hloc, fun t ↦ (hk t).1, fun t ↦ (hk t).2, hsurj, hperm, hcls,
    fun t ↦ by
      rw [(hk t).2]
      exact LinearMap.range_dualMap_eq_dualAnnihilator_ker _⟩

end Proof_lem_mmp_conductor_curve_local_exact_sequence

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MMP
open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Fourfold

variable {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [CompactSpace Z] [IsLocallyNoetherian Z]
  [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **The exact divisor-class sequence at a generic singular curve.** For a curve-and-point
exceptional model `r : Z ⟶ Y` with exceptional divisor `F` and a curve `T ⊆ Sing Y`, there is an
adapted open `T₀ ⊆ T` such that on every adapted open `T° ⊆ T₀` there are a local system `𝒫` and
a map `φ : 𝒫 ⟶ 𝒲` to the resolution local system with `0 ⟶ 𝒫 ⟶ 𝒲 ⟶ 𝒱_T ⟶ 0` exact
(`MMP.Fourfold.localSystemRestriction`), where the stalk `𝒫_t` has a basis indexed by the
irreducible components of `F_t`, locally matched by sections of `𝒫` (permutation monodromy), the
basis vector of a component `S ⊆ Fᵢ` going to the germ of the local class of `Fᵢ` along `S`;
and `𝒱_{T,t}^*` is the annihilator of the image of `𝒫_t` in `𝒲_t^*`. -/
@[mmp "lem_mmp_conductor_curve_local_exact_sequence"]
public theorem IsCurvePointExceptionalModel.exists_exact_localSystemRestriction
    {sY : Y ⟶ Spec (.of ℂ)} {r : Z ⟶ Y} {F D : Divisor Z}
    (hM : IsCurvePointExceptionalModel sY r F D) {T : IrreducibleCloseds Y}
    (hT : (T : Set Y) ⊆ (singularLocus sY : Set Y))
    (hdim : topologicalKrullDim (T : Set Y) = 1) :
    ∃ T₀ : (curveScheme T).Opens, IsAdaptedOpen sY r T₀ ∧
      ∀ To : (curveScheme T).Opens, To ≤ T₀ → IsAdaptedOpen sY r To →
      ∃ (P : TopCat.Sheaf (ModuleCat.{0} ℚ) (analyticSpace (To.ι ≫ curveι T ≫ sY)))
        (φ : P ⟶ resolutionLocalSystem sY r To)
        (b : ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
          Module.Basis (irreducibleComponents (pointFibre sY r To t)) ℚ
            (((TopCat.Sheaf.forget _ _).obj P).stalk t)),
        IsLocalSystem P ∧
        -- exactness at `𝒫`, `𝒲` and `𝒱_T`, stalkwise
        (∀ t, Function.Injective
          ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
            ((TopCat.Sheaf.forget _ _).map φ)).hom) ∧
        (∀ t, LinearMap.range ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
            ((TopCat.Sheaf.forget _ _).map φ)).hom =
          LinearMap.ker (localSystemRestrictionFibre sY hM.isBiregular To t).hom) ∧
        (∀ t, Function.Surjective (localSystemRestrictionFibre sY hM.isBiregular To t).hom) ∧
        -- permutation monodromy: the bases are matched by local sections
        (∀ t, ∃ (O : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY))) (_ : t ∈ O)
          (σ : irreducibleComponents (pointFibre sY r To t) →
            ((TopCat.Sheaf.forget _ _).obj P).obj (op O)),
          ∀ t' (ht' : t' ∈ O), ∃ e : irreducibleComponents (pointFibre sY r To t) ≃
              irreducibleComponents (pointFibre sY r To t'),
            ∀ S, ((TopCat.Sheaf.forget _ _).obj P).germ O t' ht' (σ S) = b t' (e S)) ∧
        -- the basis vector of `S ⊆ Fᵢ` goes to the local class of `Fᵢ` along `S`
        (∀ t (S : irreducibleComponents (pointFibre sY r To t)) (E : Mori.PrimeDivisor Z),
          E ∈ F.support → (S : Set (pointFibre sY r To t)) ⊆
            (pointFibreFst sY r To t).base ⁻¹' (E.support : Set Z) →
          ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
            (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY r) V) 2)
            (G : Set (preimageSpace (resolutionAnalyticMap sY r) V)),
            IsClosed G ∧
            (∃ O : Set (preimageSpace (resolutionAnalyticMap sY r) V), IsOpen O ∧
              G = O ∩ {z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈ (E.support : Set Z)}) ∧
            (∀ y : analyticSpace (pointFibre sY r To t ↘ Spec (.of ℂ)),
              pointFibreInclusion sY r To t hV y ∈ G ↔
                y.hom.base (IsLocalRing.closedPoint ℂ) ∈ (S : Set (pointFibre sY r To t))) ∧
            (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY r 2)
                t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY r) 2 _ hV).hom α) =
              ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
                ((TopCat.Sheaf.forget _ _).map φ)).hom (b t S) ∧
            (rationalCohomologyMap (X' := TopCat.of (Gᶜ : Set _))
              (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α = 0 ∧
            ∃ _ : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2
                (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z)),
              (rationalCohomologyMap
                  (X' := TopCat.of (({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈
                    (E.support : Set Z)} \ G)ᶜ :
                      Set (preimageSpace (resolutionAnalyticMap sY r) V)))
                  (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) 2).hom α =
                (rationalCohomologyMap
                  (TopCat.ofHom (X := TopCat.of (({z | z.1.hom.base (IsLocalRing.closedPoint ℂ) ∈
                    (E.support : Set Z)} \ G)ᶜ :
                      Set (preimageSpace (resolutionAnalyticMap sY r) V)))
                    (Y := analyticSpace (r ≫ sY))
                    ⟨fun z ↦ z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩ ≫
                    analyticMap (𝟙 Z) (by rw [Category.id_comp]; exact hM.comp_eq.symm)) 2).hom
                  (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2
                    (algebraicFirstChernClass
                      (Divisor.divisorialSheaf (Finsupp.single E 1 : Divisor Z))))) ∧
        -- dually, `𝒱_{T,t}^*` is the annihilator of the divisor classes in `𝒲_t^*`
        (∀ t, LinearMap.range (localSystemRestrictionFibre sY hM.isBiregular To t).hom.dualMap =
          (LinearMap.range ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) t).map
            ((TopCat.Sheaf.forget _ _).map φ)).hom).dualAnnihilator) :=
  Proof_lem_mmp_conductor_curve_local_exact_sequence.solution hM hT hdim

end MMP.Fourfold
