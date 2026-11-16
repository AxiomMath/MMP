module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.ImmersionClosure
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceChangeModule
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.RegularLocalRingRational
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageRingedSpace
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityFromCechVanishing
import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
import StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle
import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDevissage
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange
import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Normalization.Completion
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.EmbeddedResolution
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.MultiplicityIdealMembership
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.InfinitelyNearPointsFinite
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.ReducedGermNotFormalPower
import MMP.AlgebraicGeometry.Resolution.Surface.RegularSurfaceBlowup
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.WeakSequenceLengthBound
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.Surface.RegularLocus
import MMP.AlgebraicGeometry.Resolution.CurveOnSurface.PointBlowupComposites
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyRestrictOpen
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelProperties
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.EntryIndex
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Projective lc completions of affine lc surface pairs

Let `(U, B_U)` be a log canonical pair with rational boundary on an affine normal complex
surface `U`. Then `U` is an open subscheme of a normal projective complex surface `V` carrying a
log canonical rational boundary `B_V` whose restriction to `U` is `B_U`.

The proof takes the normalization of the projective closure of `U` in affine space, resolves its
finitely many singular points outside `U` by normalized point blowups, and then makes the strict
closure of `B_U` snc outside `U` by embedded curve resolution, again by point blowups away from
`U`. On the final model `B_V` is the strict closure of `B_U` (exceptional curves get coefficient
zero); outside `U` the surface is smooth and the boundary is snc with coefficients at most one,
so the pair is lc there.

## Main results

* `MMP.Threefold.exists_isOpenImmersion_isLogCanonicalPair_of_isAffine`: the completion.

## Implementation notes

* "`V` contains `U` as an open and the inclusion modifies no point of `U`" is an open immersion
  `j : U ⟶ V` over `ℂ`. The restriction of `B_V` to `U` is its inverse transform along `j`
  (`MMP.Mori.inverseTransformDivisor`), whose prime divisors are the traces `P ∩ U`.
* "Surface" is `topologicalKrullDim = 2`; normality and being a variety over `ℂ` are part of
  `MMP.Intersection.IsLogCanonicalPair`, as is effectivity of the boundary.

## References

* [OAI] *Threefold slc surface bridges*, the affine completion lemma.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Threefold

namespace Compactify

/-- A finite morphism into a scheme which is H-projective over a field is H-projective over that
field. -/
private theorem isProjectiveMorphism_comp_of_isFinite {k : Type u} [Field k]
    {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [IsFinite g] (sY : Y ⟶ Spec (.of k))
    (hY : IsProjectiveMorphism sY) : IsProjectiveMorphism (g ≫ sY) := by
  obtain ⟨L, hL, hLa⟩ := exists_isAmple_of_isQuasiProjective sY
    (Stacks.Ample.unitModule (Spec (.of k)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine _)
    (isQuasiProjective_of_isHQuasiProjective sY hY.isHQuasiProjective)
  have hg : IsProjectiveMorphism g :=
    isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
      ⟨isHQuasiProjective_of_isQuasiProjective g L hLa (isQuasiProjective_of_isFinite g),
        inferInstance⟩
  exact hg.comp hY

/-- **Normal projective compactification of an affine normal variety.** -/
private theorem exists_compactification {k : Type u} [Field k] {U : Scheme.{u}} [IsIntegral U]
    [IsNormal U] [IsAffine U] (sU : U ⟶ Spec (.of k)) [LocallyOfFiniteType sU] :
    ∃ (X : Scheme.{u}) (_ : IsIntegral X) (_ : IsNormal X) (sX : X ⟶ Spec (.of k)) (ι : U ⟶ X),
      IsOpenImmersion ι ∧ ι ≫ sX = sU ∧ IsProjectiveVariety k sX := by
  obtain ⟨Y, j, p, hj, hp, hjp⟩ := exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_toSpec sU
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have : QuasiCompact j := by
    have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated p
    exact quasiCompact_of_compactSpace j
  let Z := j.image
  haveI : IsIntegral Z := j.isIntegral_image
  let ι₀ : U ⟶ Z := j.toImage
  haveI : IsOpenImmersion ι₀ := inferInstance
  let sZ : Z ⟶ Spec (.of k) := j.imageι ≫ p
  have hsZ : IsProjectiveMorphism sZ := isProjectiveMorphism_comp_of_isFinite j.imageι p hp
  haveI : IsProper sZ := isProper_of_isProjectiveMorphism sZ hsZ
  haveI : LocallyOfFiniteType sZ := inferInstance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  let hZ : ∀ V : Z.Opens, IsCompact (V : Set Z) → (irreducibleComponents V).Finite :=
    finite_irreducibleComponents_of_isCompact Z
  let N := Z.normalizationScheme hZ
  let ν : N ⟶ Z := Z.normalization hZ
  haveI : IsFinite ν := normalization_isFinite Z
    (isJapaneseScheme_of_isNagataScheme Z (isNagataScheme_of_locallyOfFiniteType_over_field k sZ))
  haveI : IsNormal N := Scheme.isNormal_normalizationScheme Z hZ
  haveI : IsIntegral N := inferInstance
  let W : Z.Opens := ι₀.opensRange
  haveI : Nonempty W := ⟨⟨ι₀ (Classical.arbitrary U), ⟨_, rfl⟩⟩⟩
  haveI : IsIntegral W := isIntegral_of_isOpenImmersion W.ι
  haveI : IsNormal W := isNormal_of_flat_preimmersion ι₀.isoOpensRange.inv
  haveI : Nonempty (ν ⁻¹ᵁ W) := by
    obtain ⟨w⟩ := ‹Nonempty W›
    obtain ⟨x, hx⟩ := (Scheme.surjective_normalization Z hZ).surj w.1
    refine ⟨⟨x, ?_⟩⟩
    change ν x ∈ W
    rw [hx]
    exact w.2
  haveI : IsIntegral (ν ⁻¹ᵁ W) := inferInstance
  haveI : IsIso (ν ∣_ W) := isIso_of_isIntegralHom_of_isBirational_of_isNormal (ν ∣_ W)
    ((Scheme.isBirational_normalization Z hZ).morphismRestrict W)
  let ι : U ⟶ N := ι₀.isoOpensRange.hom ≫ inv (ν ∣_ W) ≫ (ν ⁻¹ᵁ W).ι
  have hιν : ι ≫ ν = ι₀ := by
    simp only [ι, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
    exact ι₀.isoOpensRange_hom_ι
  refine ⟨N, inferInstance, inferInstance, ν ≫ sZ, ι, inferInstance, ?_, ?_⟩
  · rw [← Category.assoc, hιν]
    simp only [sZ, ι₀, Scheme.Hom.toImage_imageι_assoc, hjp]
  · haveI : IsSeparated (ν ≫ sZ) := inferInstance
    haveI : AlgebraicGeometry.IsVariety k (ν ≫ sZ) := ⟨⟩
    exact ⟨isProjectiveMorphism_comp_of_isFinite ν sZ hsZ⟩

end Compactify

namespace Resolve

open IsLocalRing Filter MMP.Resolution TopologicalSpace

/-- Properness of the structure morphism depends only on the isomorphism class over the base. -/
private theorem isProper_of_overIso {S : Scheme.{u}} {A B : Over S} (e : A ≅ B)
    (hB : IsProper B.hom) : IsProper A.hom := by
  let : IsIso e.hom.left := by
    simpa only [Over.forget_map] using Functor.map_isIso (Over.forget S) e.hom
  let : IsProper B.hom := hB
  rw [← e.hom.w]
  infer_instance

/-- Replacing the source of a normalized blowup step by an isomorphic object over the base. -/
private theorem isNormalizedBlowUpOutside_of_source_iso {X : Scheme.{u}} (U : X.Opens)
    {A B C : Over X} (e : C ≅ A) (h : IsNormalizedBlowUpOutside U A B) :
    IsNormalizedBlowUpOutside U C B := by
  obtain ⟨hA, x, hx, hout, eB, heB⟩ := h
  let a : C.left ≅ A.left := (Over.forget X).mapIso e
  let y := a.inv x
  have hyx : a.hom y = x := by simp [y]
  have hCfin : ∀ V : C.left.Opens, IsCompact (V : Set C.left) →
      (irreducibleComponents V).Finite :=
    finite_irreducibleComponents_of_flat_preimmersion a.hom hA
  obtain ⟨hy, hideal⟩ := vanishingIdeal_singleton_comap_of_isIso a.hom x hx y hyx
  obtain ⟨g, hg⟩ :=
    exists_isPullback_normalizedBlowUp_comap a.hom hA hCfin x hx y hy hideal
  let : IsIso g := (MorphismProperty.IsStableUnderBaseChange.isomorphisms Scheme).of_isPullback
    hg.flip (show MorphismProperty.isomorphisms Scheme a.hom from inferInstance)
  refine ⟨hCfin, y, hy, ?_, eB ≪≫ (asIso g).symm, ?_⟩
  · have hw : C.hom y = A.hom x := by
      rw [← e.hom.w]
      change A.hom (a.hom y) = A.hom x
      rw [hyx]
    simpa only [hw] using hout
  · let νC := Stacks.Blowup.normalizedBlowUp C.left hCfin y hy
    let νA := Stacks.Blowup.normalizedBlowUp A.left hA x hx
    have hf : νC ≫ C.hom = g ≫ νA ≫ A.hom := by
      rw [← e.hom.w]
      change νC ≫ a.hom ≫ A.hom = g ≫ νA ≫ A.hom
      rw [← Category.assoc, ← hg.w, Category.assoc]
    have hi : inv g ≫ νC ≫ C.hom = νA ≫ A.hom := (IsIso.inv_comp_eq g).mpr hf
    change (eB.hom ≫ inv g) ≫ νC ≫ C.hom = B.hom
    rw [Category.assoc, hi, heB]

/-- A resolution by normalized blowups of a normal base all of whose closed points lie outside
`U` is a sequence of proper normalized blowups at closed points outside `U`, with regular total
space. -/
private theorem exists_reflTransGen_of_hasResolutionByNormalizedBlowUps {S : Scheme.{u}}
    [IsNormal S] [IsLocallyNoetherian S] (U : S.Opens)
    (hU : ∀ z : S, IsClosed ({z} : Set S) → z ∉ (U : Set S))
    (hres : HasResolutionByNormalizedBlowUps S) :
    ∃ Z : Over S, Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U)
        (Over.mk (𝟙 S)) Z ∧ IsProper Z.hom ∧ IsRegular Z.left := by
  obtain ⟨hS, X, f, hchain, hreg⟩ := hres
  have hseq : ∃ Z : Over S, Relation.ReflTransGen (IsProperNormalizedBlowUpOutside U)
      (Over.mk (𝟙 S)) Z ∧ Nonempty (Z ≅ Over.mk f) := by
    clear hreg
    induction hchain with
    | normalization hproper =>
      let : IsIso (Scheme.normalization S hS) :=
        (Scheme.isIso_normalization_iff_isNormal S hS).2 inferInstance
      exact ⟨Over.mk (𝟙 S), .refl,
        ⟨Over.isoMk (asIso (Scheme.normalization S hS)).symm (by simp)⟩⟩
    | @blowUp W g previous hW w hw hproper ih =>
      obtain ⟨Z, hZ, ⟨eZ⟩⟩ := ih
      let : IsProper g := previous.isProper
      have hwclosed : IsClosed ({g w} : Set S) := by
        simpa only [Set.image_singleton] using g.isClosedMap _ hw
      refine ⟨Over.mk (Stacks.Blowup.normalizedBlowUp W hW w hw ≫ g),
        hZ.tail ⟨isNormalizedBlowUpOutside_of_source_iso U eZ
          ⟨hW, w, hw, hU _ hwclosed, Iso.refl _, Category.id_comp _⟩, hproper⟩, ⟨Iso.refl _⟩⟩
  obtain ⟨Z, hZ, ⟨eZ⟩⟩ := hseq
  have hproperZ : IsProper Z.hom := isProper_of_overIso eZ hchain.isProper
  let : IsProper Z.hom := hproperZ
  let : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  exact ⟨Z, hZ, hproperZ, isRegular_of_iso ((Over.forget S).mapIso eZ) hreg⟩

/-- Regularity of a local ring is invariant under a stalk isomorphism. -/
private theorem isRegularLocalRing_stalk_iff_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsIso (f.stalkMap x)] :
    IsRegularLocalRing (Y.presheaf.stalk (f x)) ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  ⟨fun _ => .of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv,
    fun _ => .of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm⟩

/-- The local rings of a regular scheme are regular. -/
private theorem isRegularLocalRing_stalk_of_isRegular {Y : Scheme.{u}} (h : IsRegular Y) (y : Y) :
    IsRegularLocalRing (Y.presheaf.stalk y) :=
  ((show IsRegular Y ↔ IsLocallyNoetherian Y ∧ ∀ x : Y, IsRegularLocalRing (Y.presheaf.stalk x)
    from (isRegular_tfae Y).out 1 2).mp h).2 y

/-- Precomposition with an isomorphism preserves projectivity. -/
private theorem isProjectiveMorphism_iso_comp {X Y S : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    {f : Y ⟶ S} (hf : IsProjectiveMorphism f) : IsProjectiveMorphism (e ≫ f) := by
  obtain ⟨n, i, hi, hif⟩ := hf
  exact ⟨n, e ≫ i, inferInstance, by rw [Category.assoc, hif]⟩

/-- Over a projective variety, the normalized blowup at a closed point is projective. -/
private theorem isProjectiveMorphism_normalizedBlowUp_comp {k : Type u} [Field k]
    {A : Scheme.{u}} (sA : A ⟶ Spec (.of k)) [LocallyOfFiniteType sA]
    (hsA : IsProjectiveMorphism sA)
    (hA : ∀ V : A.Opens, IsCompact (V : Set A) → (irreducibleComponents V).Finite)
    (x : A) (hx : IsClosed ({x} : Set A)) :
    IsProjectiveMorphism (Stacks.Blowup.normalizedBlowUp A hA x hx ≫ sA) := by
  have hNagata : IsNagataScheme A := isNagataScheme_of_locallyOfFiniteType_over_field k sA
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  obtain ⟨L, hLinv, hLample⟩ := exists_isAmple_of_isProjectiveMorphism sA
    (Stacks.Ample.unitModule (Spec (.of k))) (Stacks.Ample.isAmple_unitModule_of_isAffine _) hsA
  have := hLinv
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds A)
  have hblow : IsProjectiveMorphism (blowUpToBase I) :=
    isProjectiveMorphism_of_isQuasiProjective _ L hLample
      (Stacks.Blowup.isQuasiProjective_blowUpToBase I (isFiniteType_of_isLocallyNoetherian I))
  obtain ⟨N, hNinv, hNample⟩ := exists_isAmple_of_isProjectiveMorphism _ L hLample hblow
  have := hNinv
  have hNagataBlow : IsNagataScheme (AlgebraicGeometry.blowUp I) :=
    isNagataScheme_of_locallyOfFiniteType (blowUpToBase I) hNagata
  have hfin := Stacks.Blowup.finite_irreducibleComponents_blowUp I hA
  have : IsFinite (Scheme.normalization (AlgebraicGeometry.blowUp I) hfin) :=
    Scheme.isFinite_normalization hNagataBlow hfin
  have hnorm : IsProjectiveMorphism (Scheme.normalization (AlgebraicGeometry.blowUp I) hfin) :=
    isProjectiveMorphism_of_isFinite _ N hNample
  change IsProjectiveMorphism
    ((Scheme.normalization (AlgebraicGeometry.blowUp I) hfin ≫ blowUpToBase I) ≫ sA)
  exact (hnorm.comp hblow).comp hsA

/-- The invariant carried along a sequence of normalized blowups of a normal projective variety
centred outside an open `V`: every stage is normal, integral, projective over the field, and
meets the inverse image of `V`. -/
private theorem stage_props {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {V : X.Opens} {A B : Over X}
    (hA : IsNormal A.left ∧ IsIntegral A.left ∧ IsProjectiveMorphism (A.hom ≫ sX) ∧
      ∃ a, A.hom a ∈ V)
    (h : Relation.ReflTransGen (IsNormalizedBlowUpOutside V) A B) :
    IsNormal B.left ∧ IsIntegral B.left ∧ IsProjectiveMorphism (B.hom ≫ sX) ∧
      ∃ b, B.hom b ∈ V := by
  induction h with
  | refl => exact hA
  | @tail B C _ hBC ih =>
    obtain ⟨hBn, hBi, hBp, b, hb⟩ := ih
    obtain ⟨hB, x, hx, hout, e, he⟩ := hBC
    have : LocallyOfFiniteType (B.hom ≫ sX) := by
      have := hBp
      exact (isProper_of_isProjectiveMorphism _ hBp).toLocallyOfFiniteType
    set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds B.left)
    have hbx : b ≠ x := fun hbx => hout (hbx ▸ hb)
    have hI : I ≠ ⊥ := by
      intro hI
      have hsupp : (I.support : Set B.left) = {x} :=
        Scheme.IdealSheafData.coe_support_vanishingIdeal _
      rw [hI, Scheme.IdealSheafData.support_bot] at hsupp
      have : b ∈ ({x} : Set B.left) := by rw [← hsupp]; trivial
      exact hbx this
    have : IsIntegral (AlgebraicGeometry.blowUp I) := isIntegral_blowUp I hI
    have : IsIntegral (Stacks.Blowup.normalizedBlowUpScheme B.left hB x hx) :=
      inferInstanceAs (IsIntegral (Scheme.normalizationScheme _
        (Stacks.Blowup.finite_irreducibleComponents_blowUp I hB)))
    have : IsNormal (Stacks.Blowup.normalizedBlowUpScheme B.left hB x hx) :=
      Scheme.isNormal_normalizationScheme _ (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hB)
    let ν := Stacks.Blowup.normalizedBlowUp B.left hB x hx
    let W : B.left.Opens := ⟨({x} : Set B.left)ᶜ, hx.isOpen_compl⟩
    have hiso : IsIso (ν ∣_ W) := isIso_normalizedBlowUp_restrict_compl_singleton hB x hx
    have hbW : b ∈ W := hbx
    let c : (ν ⁻¹ᵁ W).toScheme := inv (ν ∣_ W) ⟨b, hbW⟩
    have hc : ν c.1 = b := by
      have h1 : (ν ∣_ W) c = ⟨b, hbW⟩ := Scheme.inv_hom_apply (asIso (ν ∣_ W)) _
      rw [← morphismRestrict_base_coe ν W c, h1]
    haveI : Nonempty C.left := ⟨e.inv c.1⟩
    refine ⟨isNormal_of_flat_preimmersion e.hom, isIntegral_of_isOpenImmersion e.hom, ?_, ?_⟩
    · rw [← he, Category.assoc, Category.assoc]
      exact isProjectiveMorphism_iso_comp e.hom
        (isProjectiveMorphism_normalizedBlowUp_comp (B.hom ≫ sX) hBp hB x hx)
    · refine ⟨e.inv c.1, ?_⟩
      rw [← he]
      simp only [Scheme.Hom.comp_apply]
      rw [Scheme.inv_hom_apply]
      change B.hom (ν c.1) ∈ V
      rw [hc]
      exact hb

/-- The residue field at a closed point of a scheme locally of finite type over a perfect field
is separable over it. -/
private theorem isSeparable_residueField {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {o : X} (ho : IsClosed ({o} : Set X)) :
    letI : Algebra k (X.residueField o) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation o).hom.toAlgebra
    Algebra.IsSeparable k (X.residueField o) := by
  letI : Algebra k (X.residueField o) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation o).hom.toAlgebra
  have : Module.Finite k (X.residueField o) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX o ho
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

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

/-- Every point of the blow-up `B` of a closed point of a scheme, when `B` is smooth over a field,
is a specialization of a point off the exceptional curve: the local equation of the exceptional
curve is a nonzero element of the domain `𝒪_{B,w}`. -/
private theorem exists_specializes_notMem_support_exceptionalIdeal {k : Type u} [Field k]
    {X : Scheme.{u}} (I : X.IdealSheafData) (f : blowUp I ⟶ Spec (.of k)) [Smooth f]
    (w : blowUp I) : ∃ η, η ⤳ w ∧ η ∉ (exceptionalIdeal I).support := by
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field f w
  have : IsDomain ((blowUp I).presheaf.stalk w) := IsRegularLocalRing.isDomain _
  obtain ⟨a, ha, hspan⟩ :=
    Stacks.Divisors.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor
      (exceptionalIdeal I) (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) w
  have ha0 : a ≠ 0 := fun h => by
    rw [h] at ha
    exact not_isRegular_zero ha
  let P : PrimeSpectrum ((blowUp I).presheaf.stalk w) := ⟨⊥, Ideal.isPrime_bot⟩
  have hsp : (blowUp I).fromSpecStalk w P ⤳ w := MMP.Resolution.specializes_fromSpecStalk w P
  refine ⟨_, hsp, fun hmem => ?_⟩
  rw [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes _ hsp,
    MMP.Resolution.primeOfSpecializes_fromSpecStalk, hspan, Ideal.span_le,
    Set.singleton_subset_iff] at hmem
  exact ha0 hmem

/-- The blow-up of a closed point of a smooth quasi-compact surface over a perfect field is again a
smooth quasi-compact surface. -/
private theorem smoothOfRelativeDimension_blowUpToBase_comp {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] {p : X} (hp : IsClosed ({p} : Set X)) :
    SmoothOfRelativeDimension 2
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sX) ∧
      QuasiCompact (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ sX) := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : TopologicalSpace.Closeds X)
  have : Smooth sX := SmoothOfRelativeDimension.smooth 2 sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsProper (blowUpToBase I) := isProper_blowUpToBase I
  refine ⟨?_, inferInstance⟩
  have : Smooth (blowUpToBase I ≫ sX) :=
    MMP.Resolution.Kollar.smooth_blowUpToBase_comp_of_isSeparable sX hp
      (isSeparable_residueField sX hp)
  -- the local dimension of the blow-up is `2` at every point
  have hloc : ∀ x : blowUp I, topologicalKrullDimAt (blowUp I) x = (2 : ℕ) := by
    intro x
    obtain ⟨V, hxV, m, hm⟩ := exists_smoothOfRelativeDimension_nbhd (blowUpToBase I ≫ sX) x
    obtain ⟨η, hηx, hηE⟩ :=
      exists_specializes_notMem_support_exceptionalIdeal I (blowUpToBase I ≫ sX) x
    have hV : ∀ y : V.toScheme, topologicalKrullDimAt (blowUp I) (V.ι y) = m := fun y =>
      (V.ι.isOpenEmbedding.topologicalKrullDimAt_eq y).trans
        (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field m
          (V.ι ≫ blowUpToBase I ≫ sX) y)
    let O : (blowUp I).Opens := (exceptionalIdeal I).support.compl
    have := MMP.Resolution.Kr1c.isOpenImmersion_compl_exceptional I
    have : SmoothOfRelativeDimension 2 (O.ι ≫ blowUpToBase I ≫ sX) := by
      rw [← Category.assoc]
      exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
    have hηO : η ∈ O := hηE
    have h2 : topologicalKrullDimAt (blowUp I) (O.ι (⟨η, hηO⟩ : O.toScheme)) = (2 : ℕ) :=
      (O.ι.isOpenEmbedding.topologicalKrullDimAt_eq _).trans
        (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field 2
          (O.ι ≫ blowUpToBase I ≫ sX) _)
    exact (hV (⟨x, hxV⟩ : V.toScheme)).trans
      ((hV (⟨η, hηx.mem_open V.isOpen hxV⟩ : V.toScheme)).symm.trans h2)
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ 2 fun x => ?_
  set f := blowUpToBase I ≫ sX
  have : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hpre : f.base ⁻¹' {f.base x} = (Set.univ : Set (blowUp I)) := by
    ext y; simp [Subsingleton.elim (f.base y) (f.base x)]
  let e : f.fiber (f.base x) ≃ₜ blowUp I :=
    (f.fiberHomeo _).trans ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ _))
  have he : e (f.asFiber x) = x := f.fiberι_asFiber x
  calc topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)
      = topologicalKrullDimAt (blowUp I) (e (f.asFiber x)) :=
        (e.isOpenEmbedding.topologicalKrullDimAt_eq _).symm
    _ = _ := by rw [he]; exact hloc x

/-- A smooth quasi-compact surface over a field is a regular surface. -/
private theorem isRegularSurface_of_smoothOfRelativeDimension {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sX]
    [QuasiCompact sX] : IsRegularSurface X := by
  have : Smooth sX := SmoothOfRelativeDimension.smooth 2 sX
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  refine ⟨inferInstance, isRegularLocalRing_stalk_of_smooth_over_field sX, fun x hx => ?_⟩
  rw [← topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sX x hx,
    topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field 2 sX x]
  rfl

/-- Every surface `S_i` of a sequence of point blow-ups of a smooth quasi-compact surface over a
perfect field is a smooth quasi-compact surface. -/
private theorem smoothOfRelativeDimension_π_comp {k : Type u} [Field k] [PerfectField k]
    {S₀ : Scheme.{u}} (sS : S₀ ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sS]
    [QuasiCompact sS] (s : PointBlowupSequence S₀) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length),
      SmoothOfRelativeDimension 2 (s.π i hi ≫ sS) ∧ QuasiCompact (s.π i hi ≫ sS)
  | 0, _ => by
    change SmoothOfRelativeDimension 2 (s.zeroIso.hom ≫ sS) ∧ QuasiCompact (s.zeroIso.hom ≫ sS)
    exact ⟨inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _), inferInstance⟩
  | i + 1, hi => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    obtain ⟨h1, h2⟩ := smoothOfRelativeDimension_π_comp sS s i hlt.le
    obtain ⟨h3, h4⟩ := smoothOfRelativeDimension_blowUpToBase_comp (s.π i hlt.le ≫ sS)
      (s.isClosed_p i hlt)
    change SmoothOfRelativeDimension 2 ((s.blowupIso i hlt).hom ≫ (blowUpToBase _ ≫
        (s.π i hlt.le ≫ sS))) ∧ QuasiCompact ((s.blowupIso i hlt).hom ≫ (blowUpToBase _ ≫
        (s.π i hlt.le ≫ sS)))
    exact ⟨inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _), inferInstance⟩

/-- Being a regular surface is invariant under isomorphism. -/
private theorem isRegularSurface_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hY : IsRegularSurface Y) : IsRegularSurface X := by
  obtain ⟨hN, hreg, hdim⟩ := hY
  have hst : ∀ x : X, IsIso (e.hom.stalkMap x) := fun x =>
    ((isIso_iff_isIso_stalkMap e.hom).mp (inferInstanceAs (IsIso e.hom))).2 x
  let st : ∀ x : X, Y.presheaf.stalk (e.hom.base x) ≃+* X.presheaf.stalk x := fun x =>
    (@asIso _ _ _ _ (e.hom.stalkMap x) (hst x)).commRingCatIsoToRingEquiv
  refine ⟨?_, fun x => IsRegularLocalRing.of_ringEquiv (st x), fun x hx => ?_⟩
  · have : IsLocallyNoetherian Y := hN.toIsLocallyNoetherian
    have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion e.hom
    have : CompactSpace X := e.hom.homeomorph.symm.compactSpace
    exact {}
  · rw [← ringKrullDim_eq_of_ringEquiv (st x)]
    refine hdim _ ?_
    rw [← Set.image_singleton]
    exact e.hom.homeomorph.isClosedMap _ hx

/-- Every scheme `S_i` of a sequence of point blow-ups of a regular surface is a regular
surface. -/
private theorem isRegularSurface_S {S₀ : Scheme.{u}} (hS : IsRegularSurface S₀)
    (s : PointBlowupSequence S₀) : ∀ i : ℕ, (i : ℕ∞) ≤ s.length → IsRegularSurface (s.S i)
  | 0, _ => isRegularSurface_of_iso s.zeroIso hS
  | i + 1, hi =>
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    isRegularSurface_of_iso (s.blowupIso i hlt)
      (isRegularSurface_blowUp (isRegularSurface_S hS s i hlt.le) _ (s.isClosed_p i hlt))

/-- `π_i : S_i → S₀` is a composite of `i` point blow-ups. -/
private theorem isCompositeOfPointBlowupsOfLength_π {S₀ : Scheme.{u}}
    (s : PointBlowupSequence S₀) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), IsCompositeOfPointBlowupsOfLength i (s.π i hi)
  | 0, _ => inferInstanceAs (IsIso s.zeroIso.hom)
  | i + 1, hi =>
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    ⟨s.S i, s.π i hlt.le, s.p i, s.isClosed_p i hlt,
      isCompositeOfPointBlowupsOfLength_π s i hlt.le, s.blowupIso i hlt, by
        rw [PointBlowupSequence.π, PointBlowupSequence.σ, Category.assoc]⟩

/-- The dimension of local rings grows along specialization. -/
private theorem ringKrullDim_stalk_le_of_specializes {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim (X.presheaf.stalk y) := by
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Order.coheight_anti (α := X) (show y ≤ x from h)

/-- A closed point of a closed subscheme is a closed point of the ambient scheme lying on the
support. -/
private theorem isClosed_and_mem_support_of_isClosed {S : Scheme.{u}} (C : S.IdealSheafData)
    {z : C.subscheme} (hz : IsClosed ({z} : Set C.subscheme)) :
    IsClosed ({C.subschemeι z} : Set S) ∧ C.subschemeι z ∈ C.support := by
  refine ⟨by simpa only [Set.image_singleton] using
    C.subschemeι.isClosedEmbedding.isClosedMap _ hz, ?_⟩
  rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨z, rfl⟩

/-- A nonempty effective Cartier divisor on a smooth quasi-compact surface over a field has
dimension one. -/
private theorem topologicalKrullDim_subscheme_eq_one {k : Type u} [Field k] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C : S.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    (hne : (C.support : Set S).Nonempty) : topologicalKrullDim C.subscheme = 1 := by
  have hS := isRegularSurface_of_smoothOfRelativeDimension sS
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace C.subscheme := C.subschemeι.isClosedEmbedding.compactSpace
  have hPS := MMP.Resolution.Kr1c.hasPrincipalStalks_of_isEffectiveCartierDivisor hC
  -- at a closed point of the curve the local ring has dimension one
  have hcl : ∀ z : C.subscheme, IsClosed ({z} : Set C.subscheme) →
      ringKrullDim (C.subscheme.presheaf.stalk z) = 1 := by
    intro z hz
    obtain ⟨hzS, hzC⟩ := isClosed_and_mem_support_of_isClosed C hz
    obtain ⟨g, hg, hspan⟩ := hPS (C.subschemeι z)
    have := hS.2.1 (C.subschemeι z)
    have hgm : g ∈ maximalIdeal (S.presheaf.stalk (C.subschemeι z)) := by
      have hne : IdealSheafData.stalk C (C.subschemeι z) ≠ ⊤ := fun h =>
        ((IdealSheafData.stalk_eq_top_iff_notMem_support C _).1 h) hzC
      rw [hspan, Ne, Ideal.span_singleton_eq_top] at hne
      exact (mem_maximalIdeal g).mpr hne
    rw [← ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv C z), hspan]
    exact (ringKrullDim_quotient_span_singleton_eq_one_and_not_isFiniteLength (hS.2.2 _ hzS)
      (nonZeroDivisors.ne_zero hg) hgm).1
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  obtain ⟨x, hx⟩ := hne
  obtain ⟨z₀, -, hz₀⟩ := isClosed_univ.exists_closed_singleton
    ⟨IdealSheafData.subschemePoint C x hx, Set.mem_univ _⟩
  refine le_antisymm (iSup_le fun z => ?_) ((hcl z₀ hz₀).symm.le.trans (le_iSup
    (fun z => ringKrullDim (C.subscheme.presheaf.stalk z)) z₀))
  obtain ⟨z', hz', hz'c⟩ :=
    (isClosed_closure (s := ({z} : Set C.subscheme))).exists_closed_singleton
      ⟨z, subset_closure rfl⟩
  exact (ringKrullDim_stalk_le_of_specializes (specializes_iff_mem_closure.mpr hz')).trans
    (hcl z' hz'c).le

/-- A reduced effective Cartier divisor on a smooth quasi-compact surface over a field has finitely
many singular points. -/
private theorem finite_singular_points {k : Type u} [Field k] {S : Scheme.{u}}
    (sS : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS]
    (C : S.IdealSheafData) (hC : Stacks.Divisors.IsEffectiveCartierDivisor C)
    [IsReduced C.subscheme] :
    {p : S | IsClosed ({p} : Set S) ∧ p ∈ C.support ∧
      ¬ IsRegularLocalRing (S.presheaf.stalk p ⧸ IdealSheafData.stalk C p)}.Finite := by
  by_cases hne : (C.support : Set S).Nonempty
  swap
  · exact Set.finite_empty.subset fun p hp => hne ⟨p, hp.2.1⟩
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  have : CompactSpace C.subscheme := C.subschemeι.isClosedEmbedding.compactSpace
  have : Smooth sS := SmoothOfRelativeDimension.smooth 2 sS
  have : LocallyOfFiniteType (C.subschemeι ≫ sS) := inferInstance
  have : IsLocallyNoetherian C.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (C.subschemeι ≫ sS)
  have : IsNoetherian C.subscheme := {}
  have hT : IsClosed (singularLocus C.subscheme) :=
    MMP.Resolution.isClosed_setOf_not_isRegularLocalRing (C.subschemeι ≫ sS)
  have hfin : (singularLocus C.subscheme).Finite :=
    Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset
      (topologicalKrullDim_subscheme_eq_one sS C hC hne).le hT
      fun _ hZ => not_subset_singularLocus_of_mem_irreducibleComponents C.subscheme hZ
  refine (hfin.image C.subschemeι).subset fun p hp => ?_
  obtain ⟨-, hpC, hsing⟩ := hp
  obtain ⟨z, hzp⟩ : ∃ z : C.subscheme, C.subschemeι z = p :=
    ⟨_, IdealSheafData.subschemeι_subschemePoint C p hpC⟩
  refine ⟨z, fun hreg => hsing ?_, hzp⟩
  have : IsRegularLocalRing (C.subscheme.presheaf.stalk z) := hreg
  subst hzp
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv C z).symm

/-- In a unique factorization domain the radical of a nonzero principal ideal is principal,
generated by a nonzero element. -/
private theorem exists_radical_span_singleton_eq {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {a : R} (ha : a ≠ 0) :
    ∃ g : R, g ≠ 0 ∧ (Ideal.span {a}).radical = Ideal.span {g} := by
  classical
  let : NormalizationMonoid R := UniqueFactorizationMonoid.normalizationMonoid.toNormalizationMonoid
  refine ⟨UniqueFactorizationMonoid.radical a, UniqueFactorizationMonoid.radical_ne_zero, ?_⟩
  ext x
  rw [Ideal.mem_radical_iff, Ideal.mem_span_singleton]
  simp only [Ideal.mem_span_singleton]
  exact UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd ha

/-- A closed subscheme has simple normal crossings at `x` as soon as its stalk at `x` is
generated by a monomial in a regular system of parameters of `𝒪_{X,x}`. -/
private theorem hasSNCAt_of_stalk_eq_span_prod {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (x : X) {N : ℕ} {w : Fin N → X.presheaf.stalk x}
    (hw : MMP.Mori.IsRegularSystemOfParameters w) (m : Fin N → ℕ)
    (h : IdealSheafData.stalk D x = Ideal.span {∏ c, w c ^ m c}) : HasSNCAt D x := by
  classical
  choose V hV t ht using fun c => X.presheaf.germ_exist (x := x) (w c)
  let W : X.Opens := Finset.univ.inf V
  have hxW : x ∈ W := by
    change x ∈ ((Finset.univ.inf V : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    exact Set.mem_iInter₂.2 fun c _ => hV c
  have hWV : ∀ c, W ≤ V c := fun c => Finset.inf_le (Finset.mem_univ c)
  let t' : Fin N → Γ(X, W) := fun c => (X.presheaf.map (homOfLE (hWV c)).op).hom (t c)
  have ht' : ∀ c (y : X) (hy : y ∈ W), (X.presheaf.germ W y hy).hom (t' c) =
      (X.presheaf.germ (V c) y (hWV c hy)).hom (t c) := fun c y hy =>
    X.presheaf.germ_res_apply (homOfLE (hWV c)) y hy (t c)
  let g : Γ(X, W) := ∏ c, t' c ^ m c
  have hg : (X.presheaf.germ W x hxW).hom g = ∏ c, w c ^ m c := by
    simp only [g, map_prod, map_pow, ht', ht]
  obtain ⟨U, hUW, hxU, hU⟩ := MMP.Flips.ResolutionInputs.exists_ideal_eq_span_of_stalk_eq D hxW
    (fun _ : Unit => g) (by rw [Set.range_const, hg, h])
  let r : Fin N → Γ(X, U) := fun c => (X.presheaf.map (homOfLE hUW).op).hom (t' c)
  have hr : ∀ c (y : X) (hy : y ∈ U), (X.presheaf.germ U y hy).hom (r c) =
      (X.presheaf.germ W y (hUW hy)).hom (t' c) := fun c y hy =>
    X.presheaf.germ_res_apply (homOfLE hUW) y hy (t' c)
  refine ⟨N, U, hxU, r, m, ?_, fun y hy => ?_⟩
  · convert hw using 1
    funext c
    rw [hr, ht', ht]
  · obtain ⟨W', hW', hyW', hW'U⟩ := exists_isAffineOpen_mem_and_subset hy
    rw [IdealSheafData.stalk_eq_map_germ D y ⟨W', hW'⟩ hyW', hU ⟨W', hW'⟩ hW'U, Ideal.map_span,
      Set.range_const, Set.image_singleton]
    congr 2
    have h1 : (X.presheaf.germ W' y hyW').hom (restrictSection ⟨W', hW'⟩ (hW'U.trans hUW) g) =
        (X.presheaf.germ W y (hUW hy)).hom g :=
      X.presheaf.germ_res_apply (homOfLE (hW'U.trans hUW)) y hyW' g
    rw [h1]
    simp only [g, map_prod, map_pow, hr]

/-- Simple normal crossings at `x` are a condition on the stalk at `x`: the stalk is generated
by a monomial in a regular system of parameters. -/
private theorem hasSNCAt_iff {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
    (x : X) : HasSNCAt D x ↔ ∃ (N : ℕ) (w : Fin N → X.presheaf.stalk x) (m : Fin N → ℕ),
      MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk D x = Ideal.span {∏ c, w c ^ m c} := by
  refine ⟨fun ⟨d, U, hU, s, m, hreg, hst⟩ => ⟨d, _, m, hreg, ?_⟩,
    fun ⟨N, w, m, hw, h⟩ => hasSNCAt_of_stalk_eq_span_prod D x hw m h⟩
  rw [hst x hU, map_prod]
  simp only [map_pow]

/-- A closed subscheme has simple normal crossings at a point with regular local ring off its
support: there the ideal is the unit ideal, the empty monomial in a regular system of
parameters. -/
private theorem hasSNCAt_of_notMem_support {X : Scheme.{u}} (D : X.IdealSheafData) {x : X}
    [IsRegularLocalRing (X.presheaf.stalk x)] (hx : x ∉ D.support) : HasSNCAt D x := by
  classical
  obtain ⟨N, w, hw⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
  choose V hV t ht using fun c => X.presheaf.germ_exist (x := x) (w c)
  let W : X.Opens := Finset.univ.inf V ⊓ D.support.compl
  have hxW : x ∈ W := by
    refine ⟨?_, hx⟩
    change x ∈ ((Finset.univ.inf V : X.Opens) : Set X)
    rw [TopologicalSpace.Opens.coe_finset_inf, Finset.inf_eq_iInf]
    exact Set.mem_iInter₂.2 fun c _ => hV c
  have hWV : ∀ c, W ≤ V c := fun c => inf_le_left.trans (Finset.inf_le (Finset.mem_univ c))
  refine ⟨N, W, hxW, fun c => (X.presheaf.map (homOfLE (hWV c)).op).hom (t c), 0, ?_,
    fun y hy => ?_⟩
  · convert hw using 1
    funext c
    rw [X.presheaf.germ_res_apply, ht]
  · simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, map_one, Ideal.span_singleton_one]
    exact (IdealSheafData.stalk_eq_top_iff_notMem_support D y).2 hy.2

/-- Simple normal crossings are local: they can be read off an open neighbourhood. -/
private theorem hasSNCAt_comap_iff {X Y : Scheme.{u}} [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [IsOpenImmersion f] (D : Y.IdealSheafData) (x : X) :
    HasSNCAt (D.comap f) x ↔ HasSNCAt D (f x) := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isOpenImmersion f
  have : IsIso (f.stalkMap x) := IsOpenImmersion.instIsIsoCommRingCatStalkMap f x
  let φ := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  have hst : IdealSheafData.stalk (D.comap f) x = Ideal.map φ (IdealSheafData.stalk D (f x)) :=
    IdealSheafData.stalk_comap D f x
  rw [hasSNCAt_iff, hasSNCAt_iff, hst]
  constructor
  · rintro ⟨N, w, m, hw, h⟩
    refine ⟨N, fun c => φ.symm (w c), m, hw.map_ringEquiv φ.symm, ?_⟩
    have h2 := congrArg (Ideal.map φ.symm) h
    rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ φ.bijective] at h2
    rw [h2, Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]
  · rintro ⟨N, w, m, hw, h⟩
    refine ⟨N, fun c => φ (w c), m, hw.map_ringEquiv φ, ?_⟩
    rw [h, Ideal.map_span, Set.image_singleton, map_prod]
    simp only [map_pow]

/-- Along an open immersion, the inverse image of the reduced structure on a closed set is the
reduced structure on its preimage. -/
private theorem comap_vanishingIdeal_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (C : TopologicalSpace.Closeds Y) :
    (Scheme.IdealSheafData.vanishingIdeal C).comap f =
      Scheme.IdealSheafData.vanishingIdeal ⟨f ⁻¹' C, C.isClosed.preimage f.continuous⟩ := by
  set J := Scheme.IdealSheafData.vanishingIdeal C
  have : IsReduced (J.comap f).subscheme :=
    isReduced_of_isOpenImmersion ((J.comapIso f).hom ≫ Limits.pullback.snd f J.subschemeι)
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  rw [Scheme.IdealSheafData.support_comap]
  ext1
  simp [J]

/-- Simple normal crossings of a reduced closed subscheme are transported along an
isomorphism. -/
private theorem isSNCSubscheme_vanishingIdeal_preimage {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (e : X ≅ Y) (Z : TopologicalSpace.Closeds Y)
    (hZ : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal Z)) :
    IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal
      ⟨e.hom ⁻¹' Z, Z.isClosed.preimage e.hom.continuous⟩) := by
  intro q hq
  rw [← comap_vanishingIdeal_of_isOpenImmersion, hasSNCAt_comap_iff]
  refine hZ _ ?_
  simpa only [Set.image_singleton] using e.hom.isClosedEmbedding.isClosedMap _ hq

/-- On a regular surface, the reduced structure on the support of a regular effective Cartier
divisor has simple normal crossings at every closed point. -/
private theorem hasSNCAt_vanishingIdeal_support_of_isRegularLocalRing {X : Scheme.{u}}
    (hX : IsRegularSurface X) (Γ : X.IdealSheafData)
    (hΓ : Stacks.Divisors.IsEffectiveCartierDivisor Γ) {x : X} (hx : IsClosed ({x} : Set X))
    (hreg : x ∈ Γ.support →
      IsRegularLocalRing (X.presheaf.stalk x ⧸ IdealSheafData.stalk Γ x)) :
    HasSNCAt (Scheme.IdealSheafData.vanishingIdeal Γ.support) x := by
  have : IsLocallyNoetherian X := hX.1.toIsLocallyNoetherian
  have := hX.2.1 x
  by_cases hxΓ : x ∈ Γ.support
  swap
  · refine hasSNCAt_of_notMem_support _ ?_
    rwa [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hq := hreg hxΓ
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  obtain ⟨g, hg, hspan⟩ := MMP.Resolution.Kr1c.hasPrincipalStalks_of_isEffectiveCartierDivisor hΓ x
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  have hgm : g ∈ maximalIdeal (X.presheaf.stalk x) := by
    have hne : IdealSheafData.stalk Γ x ≠ ⊤ := fun h =>
      ((IdealSheafData.stalk_eq_top_iff_notMem_support Γ x).1 h) hxΓ
    rw [hspan, Ne, Ideal.span_singleton_eq_top] at hne
    exact (mem_maximalIdeal g).mpr hne
  rw [hspan] at hq
  have hdim := (MMP.Resolution.ringKrullDim_quotient_span_singleton_eq_one_and_not_isFiniteLength
    (hX.2.2 x hx) hg0 hgm).1
  have hrange : Set.range ![g] = {g} := by simp
  obtain ⟨m, t, ht⟩ := (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff
    ![g]).1 ⟨by rwa [hrange], by rw [hrange, hdim, hX.2.2 x hx]; rfl⟩
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x ⧸ Ideal.span {g})
  have hprime : (Ideal.span {g}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).1 this
  refine (hasSNCAt_iff _ x).2 ⟨1 + m, Fin.append ![g] t, Fin.append ![1] 0, ht, ?_⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_support, MMP.Resolution.stalk_radical, hspan,
    hprime.isRadical.radical, Fin.prod_univ_add]
  simp

/-- On a locally Noetherian scheme with regular local rings, the reduced structure on the
support of an effective Cartier divisor is an effective Cartier divisor: in the factorial local
rings, the radical of a nonzero principal ideal is principal. -/
private theorem isEffectiveCartierDivisor_vanishingIdeal_support {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x))
    {J : X.IdealSheafData} (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal J.support) := by
  refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor _
    fun x _ => ?_
  have := hX x
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x)
  obtain ⟨a, ha, hspan⟩ := MMP.Resolution.Kr1c.hasPrincipalStalks_of_isEffectiveCartierDivisor hJ x
  obtain ⟨g, hg, hrad⟩ := exists_radical_span_singleton_eq (nonZeroDivisors.ne_zero ha)
  refine ⟨g, mem_nonZeroDivisors_of_ne_zero hg, ?_⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_support, MMP.Resolution.stalk_radical, hspan, hrad]

/-- A strong embedded resolution sequence dominated by a composite of `N` point blow-ups with snc
reduced preimage of `C` has length at most `N`. -/
private theorem length_le {S Sstar : Scheme.{u}} (hS : IsRegularSurface S)
    (C : S.IdealSheafData) {πstar : Sstar ⟶ S} {N : ℕ}
    (hN : IsCompositeOfPointBlowupsOfLength N πstar)
    (hsnc : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal (C.comap πstar).support))
    (s : PointBlowupSequence S) (hs : s.IsStrongEmbeddedResolution C) : s.length ≤ N := by
  by_contra h
  have hi : ((N + 1 : ℕ) : ℕ∞) ≤ s.length := by
    rw [Nat.cast_succ]; exact Order.add_one_le_of_lt (not_le.mp h)
  obtain ⟨g, hg, hcomp⟩ := PointBlowupSequence.exists_isCompositeOfPointBlowups_comp_π_eq hS C
    ⟨N, hN⟩ hsnc s hs (N + 1) hi
  have := IsCompositeOfPointBlowupsOfLength.le_of_comp hS
    (isCompositeOfPointBlowupsOfLength_π s (N + 1) hi) hg (hcomp ▸ hN)
  omega

/-- The length-zero sequence of point blow-ups. -/
private noncomputable def trivialSeq (T : Scheme.{u}) [Nonempty T] : PointBlowupSequence T where
  length := 0
  S := fun _ => T
  zeroIso := Iso.refl T
  p := fun _ => Classical.arbitrary T
  isClosed_p := fun _ hi => by simp at hi
  blowupIso := fun _ hi => by simp at hi

/-- **A stopping strong embedded resolution sequence exists.** Strong embedded resolution
sequences of a curve on a smooth surface have bounded length, so one of maximal length is
maximal, and maximal ones stop (`strongEmbeddedResolutionStops_of_maximal`). -/
private theorem exists_strongEmbeddedResolutionStops {k : Type u} [Field k] [PerfectField k]
    {S : Scheme.{u}} [Nonempty S] (sS : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension 2 sS]
    [QuasiCompact sS] (C : S.IdealSheafData)
    (hC : Stacks.Divisors.IsEffectiveCartierDivisor C) :
    ∃ s : PointBlowupSequence S, s.IsStrongEmbeddedResolution C ∧
      s.StrongEmbeddedResolutionStops C := by
  classical
  have hS := isRegularSurface_of_smoothOfRelativeDimension sS
  obtain ⟨Sstar, πstar, ⟨N, hN⟩, hsnc⟩ := exists_isCompositeOfPointBlowups_isSNCSubscheme sS C hC
  have hle : ∀ s : PointBlowupSequence S, s.IsStrongEmbeddedResolution C → s.length ≤ N :=
    fun s hs => length_le hS C hN hsnc s hs
  let P : ℕ → Prop := fun m => ∃ s : PointBlowupSequence S, s.IsStrongEmbeddedResolution C ∧
    s.length = m
  have hP0 : P 0 := ⟨trivialSeq S, fun i hi =>
    absurd (show (i : ℕ∞) < 0 from hi) (not_lt_of_ge zero_le), rfl⟩
  obtain ⟨s, hs, hlen⟩ : P (Nat.findGreatest P N) := Nat.findGreatest_spec (Nat.zero_le N) hP0
  refine ⟨s, hs, PointBlowupSequence.strongEmbeddedResolutionStops_of_maximal sS C hC s hs ?_⟩
  intro s' hs' hlt _
  have h' := hle s' hs'
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top N) h')
  rw [← hm] at h' hlt
  rw [hlen] at hlt
  have hmN : m ≤ N := by exact_mod_cast h'
  have h3 : (m : ℕ∞) ≤ (Nat.findGreatest P N : ℕ) := by
    exact_mod_cast Nat.le_findGreatest hmN (show P m from ⟨s', hs', hm.symm⟩)
  exact h3.not_gt hlt

/-- An open immersion into a Jacobson scheme maps closed points to closed points. -/
private theorem isClosed_singleton_of_isOpenImmersion {X Y : Scheme.{u}} [JacobsonSpace Y]
    (f : X ⟶ Y) [IsOpenImmersion f] {x : X} (hx : IsClosed ({x} : Set X)) :
    IsClosed ({f x} : Set Y) := by
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [← Set.image_singleton]
  exact hx.isLocallyClosed.image f.isOpenEmbedding.isInducing
    f.isOpenEmbedding.isOpen_range.isLocallyClosed

/-- A composite is an isomorphism over `V` when both factors are, over the relevant opens. -/
private theorem isIso_comp_restrict {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (V : Z.Opens)
    (hf : IsIso (f ∣_ g ⁻¹ᵁ V)) (hg : IsIso (g ∣_ V)) : IsIso ((f ≫ g) ∣_ V) := by
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso' hf hg

/-- A point of an open subscheme whose image is a closed point is a closed point. -/
private theorem isClosed_singleton_of_ι {X : Scheme.{u}} (W : X.Opens) (w : W.toScheme)
    (h : IsClosed ({W.ι w} : Set X)) : IsClosed ({w} : Set W.toScheme) := by
  have h' := h.preimage W.ι.continuous
  convert h' using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  exact ⟨fun hz => hz ▸ rfl, fun hz => W.ι.isOpenEmbedding.injective hz⟩

/-- **The centres of a strong embedded resolution sequence avoid the snc locus.** If `π_i` is an
isomorphism over an open `W` of `S` at whose closed points the reduced curve is snc, the centre
`p_i` does not lie over `W`: over `W` the reduced preimage of the curve is the curve itself. -/
private theorem π_p_notMem {k : Type u} [Field k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS] (C : S.IdealSheafData)
    (s : PointBlowupSequence S) (hs : s.IsStrongEmbeddedResolution C) (W : S.Opens)
    (hW : ∀ w : S, w ∈ W → IsClosed ({w} : Set S) →
      HasSNCAt (Scheme.IdealSheafData.vanishingIdeal C.support) w)
    (i : ℕ) (hlt : (i : ℕ∞) < s.length) (hiso : IsIso (s.π i hlt.le ∣_ W)) :
    s.π i hlt.le (s.p i) ∉ W := by
  intro hmem
  have hS := isRegularSurface_of_smoothOfRelativeDimension sS
  haveI : IsLocallyNoetherian S := hS.1.toIsLocallyNoetherian
  haveI : Smooth sS := SmoothOfRelativeDimension.smooth 2 sS
  haveI : JacobsonSpace S := LocallyOfFiniteType.jacobsonSpace sS
  haveI : IsLocallyNoetherian (s.S i) := (isRegularSurface_S hS s i hlt.le).1.toIsLocallyNoetherian
  set π := s.π i hlt.le with hπ
  set W' := π ⁻¹ᵁ W with hW'
  let p' : W'.toScheme := ⟨s.p i, hmem⟩
  have hp'cl : IsClosed ({p'} : Set W'.toScheme) :=
    isClosed_singleton_of_ι W' p' (s.isClosed_p i hlt)
  let φ := π ∣_ W
  have hcomp : W'.ι ≫ π = φ ≫ W.ι := (morphismRestrict_ι π W).symm
  have hφcl : IsClosed ({φ p'} : Set W.toScheme) := by
    have h := (Scheme.homeoOfIso (asIso φ)).isClosedMap _ hp'cl
    rwa [Set.image_singleton] at h
  have heq : W.ι (φ p') = π (s.p i) := by
    rw [← Scheme.Hom.comp_apply, ← hcomp]; rfl
  have hcl : IsClosed ({W.ι (φ p')} : Set S) := isClosed_singleton_of_isOpenImmersion W.ι hφcl
  have hsnc := hW _ (heq ▸ hmem) hcl
  apply (hs i hlt).2
  rw [show s.p i = W'.ι p' from rfl, ← hasSNCAt_comap_iff W'.ι,
    comap_vanishingIdeal_of_isOpenImmersion]
  have hset : (⟨W'.ι ⁻¹' ((C.comap π).support : Set (s.S i)),
      (C.comap π).support.isClosed.preimage W'.ι.continuous⟩ : TopologicalSpace.Closeds _) =
      ⟨(φ ≫ W.ι) ⁻¹' (C.support : Set S), C.support.isClosed.preimage (φ ≫ W.ι).continuous⟩ := by
    ext z
    rw [← hcomp]
    simp [Scheme.IdealSheafData.support_comap]
  rw [hset, ← comap_vanishingIdeal_of_isOpenImmersion (φ ≫ W.ι), hasSNCAt_comap_iff (φ ≫ W.ι)]
  exact hsnc

/-- **A strong embedded resolution sequence is an isomorphism over the snc locus.** Every `π_i`
is an isomorphism over an open `W` of `S` at whose closed points the reduced curve is snc. -/
private theorem isIso_π_restrict {k : Type u} [Field k] {S : Scheme.{u}} (sS : S ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 2 sS] [QuasiCompact sS] (C : S.IdealSheafData)
    (s : PointBlowupSequence S) (hs : s.IsStrongEmbeddedResolution C) (W : S.Opens)
    (hW : ∀ w : S, w ∈ W → IsClosed ({w} : Set S) →
      HasSNCAt (Scheme.IdealSheafData.vanishingIdeal C.support) w) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), IsIso (s.π i hi ∣_ W)
  | 0, _ => by
    change IsIso (s.zeroIso.hom ∣_ W)
    infer_instance
  | i + 1, hi => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    have hS := isRegularSurface_of_smoothOfRelativeDimension sS
    haveI : IsLocallyNoetherian (s.S i) :=
      (isRegularSurface_S hS s i hlt.le).1.toIsLocallyNoetherian
    have hiso := isIso_π_restrict sS C s hs W hW i hlt.le
    have hnot := π_p_notMem sS C s hs W hW i hlt hiso
    set I := Scheme.IdealSheafData.vanishingIdeal
      (⟨{s.p i}, s.isClosed_p i hlt⟩ : TopologicalSpace.Closeds (s.S i))
    change IsIso ((((s.blowupIso i hlt).hom ≫ blowUpToBase I) ≫ s.π i hlt.le) ∣_ W)
    have hb : IsIso (blowUpToBase I ∣_ (s.π i hlt.le ⁻¹ᵁ W)) := by
      refine @MMP.Resolution.Kollar.isIso_morphismRestrict_of_le _ _ _ _ _ ?_
        (isIso_blowUp_restrict_compl_support I)
      intro z hz hzI
      have hsupp : ((I.support : Set (s.S i))) = {s.p i} :=
        Scheme.IdealSheafData.coe_support_vanishingIdeal _
      have : z ∈ ({s.p i} : Set (s.S i)) := by
        rw [← hsupp]; exact hzI
      rw [Set.mem_singleton_iff] at this
      subst this
      exact hnot hz
    exact isIso_comp_restrict _ _ W (isIso_comp_restrict _ _ _ inferInstance hb) hiso

/-- The base change of the identity is the identity. -/
private noncomputable def pullbackIdentityIso {S T : Scheme.{u}} (s : T ⟶ S) :
    ((Over.pullback s).obj (Over.mk (𝟙 S))) ≅ Over.mk (𝟙 T) :=
  Over.isoMk (asIso (Limits.pullback.snd (𝟙 S) s)) (by simp)

/-- **One step of the globalization of a point blow-up.** Let `S ⊆ Y` be open, and let `A` be a
scheme over `Y` whose restriction over `S` is identified with `π : T ⟶ S`, `T` a regular surface.
Blowing up a closed point `p` of `T` lying outside an open `V` is the restriction over `S` of the
normalized blowup of `A` at the corresponding closed point. -/
private theorem exists_globalize_step {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (S V : Y.Opens) {T : Scheme.{u}} (hT : IsRegularSurface T)
    (π : T ⟶ S) (p : T) (hp : IsClosed ({p} : Set T)) (hout : S.ι (π p) ∉ V) (A : Over Y)
    [IsLocallyNoetherian A.left] [LocallyOfFiniteType (A.hom ≫ sY)]
    (e : (Over.pullback S.ι).obj A ≅ Over.mk π) :
    ∃ C : Over Y, IsNormalizedBlowUpOutside V A C ∧
      Nonempty ((Over.pullback S.ι).obj C ≅
        Over.mk (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) ≫ π)) := by
  set L := (Over.pullback S.ι).obj A with hL
  let q : L.left ⟶ A.left := Limits.pullback.fst A.hom S.ι
  haveI : IsOpenImmersion q := by
    change IsOpenImmersion (Limits.pullback.fst A.hom S.ι); infer_instance
  let a : L.left ≅ T := (Over.forget _).mapIso e
  have ha : a.hom ≫ π = L.hom := Over.w e.hom
  let y := a.inv p
  have hya : a.hom y = p := Scheme.inv_hom_apply a p
  obtain ⟨hy, hideal_a⟩ := vanishingIdeal_singleton_comap_of_isIso a.hom p hp y hya
  haveI : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace (A.hom ≫ sY)
  have hx : IsClosed ({q y} : Set A.left) := isClosed_singleton_of_isOpenImmersion q hy
  have hAfin : ∀ W : A.left.Opens, IsCompact (W : Set A.left) →
      (irreducibleComponents W).Finite := finite_irreducibleComponents_of_isCompact A.left
  have hLfin : ∀ W : L.left.Opens, IsCompact (W : Set L.left) →
      (irreducibleComponents W).Finite := finite_irreducibleComponents_of_flat_preimmersion q hAfin
  haveI : IsLocallyNoetherian T := hT.1.toIsLocallyNoetherian
  have hTfin : ∀ W : T.Opens, IsCompact (W : Set T) → (irreducibleComponents W).Finite :=
    finite_irreducibleComponents_of_isCompact T
  have hxV : A.hom (q y) ∉ V := by
    have h1 : A.hom (q y) = S.ι (L.hom y) := by
      change (Limits.pullback.fst A.hom S.ι ≫ A.hom) y = (Limits.pullback.snd A.hom S.ι ≫ S.ι) y
      rw [Limits.pullback.condition]
    have h2 : L.hom y = π p := by
      rw [← ha, Scheme.Hom.comp_apply, hya]
    rw [h1, h2]
    exact hout
  let C : Over Y := Over.mk (Stacks.Blowup.normalizedBlowUp A.left hAfin (q y) hx ≫ A.hom)
  refine ⟨C, ⟨hAfin, q y, hx, hxV, Iso.refl _, Category.id_comp _⟩, ?_⟩
  -- the normalized blowup of `A` restricts over `S` to that of `L`
  have hideal : (Scheme.IdealSheafData.vanishingIdeal (⟨{q y}, hx⟩ : Closeds A.left)).comap q =
      Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds L.left) := by
    rw [comap_vanishingIdeal_of_isOpenImmersion]
    congr 1
    ext z
    simp only [Closeds.coe_mk, Set.mem_preimage, Set.mem_singleton_iff]
    exact q.isOpenEmbedding.injective.eq_iff
  obtain ⟨m, hm⟩ := exists_isPullback_normalizedBlowUp_comap q hAfin hLfin (q y) hx y hy hideal
  let νL := Stacks.Blowup.normalizedBlowUp L.left hLfin y hy
  let νA := Stacks.Blowup.normalizedBlowUp A.left hAfin (q y) hx
  have hsq : IsPullback (νL ≫ L.hom) m S.ι (νA ≫ A.hom) :=
    hm.flip.paste_horiz (IsPullback.of_hasPullback A.hom S.ι).flip
  let e1 : Over.mk (νL ≫ L.hom) ≅ (Over.pullback S.ι).obj C :=
    Over.isoMk hsq.flip.isoPullback hsq.flip.isoPullback_hom_snd
  -- transport along `a`
  obtain ⟨g, hg⟩ := exists_isPullback_normalizedBlowUp_comap a.hom hTfin hLfin p hp y hy hideal_a
  haveI : IsIso g := (MorphismProperty.IsStableUnderBaseChange.isomorphisms Scheme).of_isPullback
    hg.flip (show MorphismProperty.isomorphisms Scheme a.hom from inferInstance)
  let νT := Stacks.Blowup.normalizedBlowUp T hTfin p hp
  let e2 : Over.mk (νL ≫ L.hom) ≅ Over.mk (νT ≫ π) := Over.isoMk (asIso g) (by
    change g ≫ νT ≫ π = νL ≫ L.hom
    rw [← Category.assoc, hg.w, Category.assoc, ha])
  -- the normalized blowup of the regular surface `T` is its blowup
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds T)
  have hBl : IsRegularSurface (AlgebraicGeometry.blowUp I) := isRegularSurface_blowUp hT p hp
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp I) := hBl.1.toIsLocallyNoetherian
  have h12 : IsRegular (AlgebraicGeometry.blowUp I) ↔
      IsLocallyNoetherian (AlgebraicGeometry.blowUp I) ∧
        ∀ x, IsRegularLocalRing ((AlgebraicGeometry.blowUp I).presheaf.stalk x) :=
    (isRegular_tfae _).out 1 2
  haveI : IsNormal (AlgebraicGeometry.blowUp I) := isNormal_of_isRegular _
    (h12.mpr ⟨inferInstance, hBl.2.1⟩)
  let e3 : Over.mk (νT ≫ π) ≅ Over.mk (blowUpToBase I ≫ π) :=
    Over.isoMk (Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp hTfin p hp) (by
      change (Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp hTfin p hp).hom ≫ blowUpToBase I ≫ π =
        νT ≫ π
      rw [← Category.assoc]
      rfl)
  exact ⟨e1.symm ≪≫ e2 ≪≫ e3⟩

/-- A sequence of normalized blowups of a normal scheme at points lying outside an open `V` is
an isomorphism over `V`, and every stage is normal. -/
private theorem isIso_restrict_of_reflTransGen {X : Scheme.{u}} {V : X.Opens} {A B : Over X}
    (hA : IsNormal A.left) (hAiso : IsIso (A.hom ∣_ V))
    (h : Relation.ReflTransGen (IsNormalizedBlowUpOutside V) A B) :
    IsNormal B.left ∧ IsIso (B.hom ∣_ V) := by
  induction h with
  | refl => exact ⟨hA, hAiso⟩
  | @tail B C _ hBC ih =>
    obtain ⟨hBn, hBiso⟩ := ih
    obtain ⟨hB, x, hx, hout, e, he⟩ := hBC
    haveI : IsNormal (Stacks.Blowup.normalizedBlowUpScheme B.left hB x hx) :=
      Scheme.isNormal_normalizationScheme _ (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hB)
    refine ⟨isNormal_of_flat_preimmersion e.hom, ?_⟩
    rw [← he]
    have h1 : IsIso (Stacks.Blowup.normalizedBlowUp B.left hB x hx ∣_ (B.hom ⁻¹ᵁ V)) := by
      refine @MMP.Resolution.Kollar.isIso_morphismRestrict_of_le _ _ _ _ _ ?_
        (isIso_normalizedBlowUp_restrict_compl_singleton hB x hx)
      intro z hz hzx
      exact hout ((Set.mem_singleton_iff.mp hzx) ▸ hz)
    exact isIso_comp_restrict _ _ V inferInstance (isIso_comp_restrict _ _ V h1 hBiso)

/-- **Globalization of a sequence of point blow-ups.** Let `S ⊆ Y` be an open regular surface and
`s` a sequence of point blow-ups of `S` whose centres lie over points of `Y` outside an open `V`.
Then every stage `π_i : S_i ⟶ S` is the restriction over `S` of a sequence of normalized blowups
of `Y` at closed points outside `V`. -/
private theorem exists_globalization {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    [IsNormal Y] (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (hY : IsProjectiveMorphism sY)
    (S V : Y.Opens) (hVne : (V : Set Y).Nonempty) (hS : IsRegularSurface S.toScheme)
    (s : PointBlowupSequence S.toScheme)
    (hcen : ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length), S.ι (s.π i hi.le (s.p i)) ∉ V) :
    ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ s.length), ∃ A : Over Y,
      Relation.ReflTransGen (IsNormalizedBlowUpOutside V) (Over.mk (𝟙 Y)) A ∧
        Nonempty ((Over.pullback S.ι).obj A ≅ Over.mk (s.π i hi))
  | 0, _ => ⟨Over.mk (𝟙 Y), .refl, ⟨pullbackIdentityIso S.ι ≪≫
      Over.isoMk s.zeroIso.symm (by simp [PointBlowupSequence.π])⟩⟩
  | i + 1, hi => by
    have hlt := PointBlowupSequence.coe_lt_of_succ_le hi
    obtain ⟨A, hA, ⟨e⟩⟩ := exists_globalization sY hY S V hVne hS s hcen i hlt.le
    obtain ⟨v, hv⟩ := hVne
    obtain ⟨-, -, hAp, -⟩ := stage_props sY (V := V) (A := Over.mk (𝟙 Y))
      ⟨inferInstanceAs (IsNormal Y), inferInstanceAs (IsIntegral Y),
        by simpa using hY, ⟨v, hv⟩⟩ hA
    haveI : LocallyOfFiniteType (A.hom ≫ sY) :=
      (isProper_of_isProjectiveMorphism _ hAp).toLocallyOfFiniteType
    haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian (A.hom ≫ sY)
    obtain ⟨C, hAC, ⟨eC⟩⟩ := exists_globalize_step sY S V (isRegularSurface_S hS s i hlt.le)
      (s.π i hlt.le) (s.p i) (s.isClosed_p i hlt) (hcen i hlt) A e
    refine ⟨C, hA.tail hAC, ⟨eC ≪≫ Over.isoMk (s.blowupIso i hlt).symm ?_⟩⟩
    change (s.blowupIso i hlt).inv ≫ ((s.blowupIso i hlt).hom ≫ blowUpToBase _) ≫
      s.π i hlt.le = blowUpToBase _ ≫ s.π i hlt.le
    rw [Category.assoc, Iso.inv_hom_id_assoc]

/-- On an integral scheme, the generic point of the spectrum of a local ring maps to the generic
point. -/
private theorem fromSpecStalk_eq_genericPoint {O : Scheme.{u}} [IsIntegral O] (y : O)
    (P : PrimeSpectrum (O.presheaf.stalk y)) (hP : P.asIdeal = ⊥) :
    O.fromSpecStalk y P = genericPoint O := by
  have hη : genericPoint O ∈ Set.range (O.fromSpecStalk y) := by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoint_spec O).specializes (Set.mem_univ y)
  obtain ⟨P₀, hP₀⟩ := hη
  have hsp : P ⤳ P₀ := (PrimeSpectrum.le_iff_specializes _ _).mp (by
    change P.asIdeal ≤ P₀.asIdeal
    rw [hP]; exact bot_le)
  have h1 : O.fromSpecStalk y P ⤳ genericPoint O :=
    hP₀ ▸ hsp.map (O.fromSpecStalk y).continuous
  refine (IsGenericPoint.eq ?_ (genericPoint_spec O))
  rw [isGenericPoint_iff_specializes]
  intro z
  exact ⟨fun _ => trivial, fun _ => h1.trans ((genericPoint_spec O).specializes (Set.mem_univ z))⟩

/-- **Simple normal crossings of the reduced structure give an snc closed subset, pointwise.** On a
regular surface, if the reduced structure on a closed set `T` not containing the generic point is
snc at every closed point, then `T` is snc at every point (in the sense of
`MMP.Resolution.IsSNCAt`). -/
private theorem isSNCAt_of_isSNCSubscheme {O : Scheme.{u}} [IsIntegral O]
    (hO : IsRegularSurface O) (T : Closeds O) (hgen : genericPoint O ∉ (T : Set O))
    (hT : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal T)) (y : O) :
    MMP.Resolution.IsSNCAt (T : Set O) y := by
  classical
  haveI : IsLocallyNoetherian O := hO.1.toIsLocallyNoetherian
  haveI : CompactSpace O := hO.1.toCompactSpace
  haveI := hO.2.1 y
  haveI : IsDomain (O.presheaf.stalk y) := IsRegularLocalRing.isDomain _
  have hpre : O.fromSpecStalk y ⁻¹' (T : Set O) = PrimeSpectrum.zeroLocus
      (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y :
        Set (O.presheaf.stalk y)) := by
    have := MMP.Resolution.preimage_fromSpecStalk_support (Scheme.IdealSheafData.vanishingIdeal T) y
    rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
  by_cases hy : IsClosed ({y} : Set O)
  · obtain ⟨N, w, m, hw, h⟩ := (hasSNCAt_iff _ y).1 (hT y hy)
    refine ⟨N, w, Finset.univ.filter (fun c => m c ≠ 0), hw, ?_⟩
    rw [hpre, h]
    ext P
    simp only [PrimeSpectrum.zeroLocus_span, PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff,
      SetLike.mem_coe, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
    constructor
    · intro hP
      obtain ⟨c, -, hc⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).mp hP
      refine ⟨c, fun h0 => ?_, P.isPrime.mem_of_pow_mem _ hc⟩
      rw [h0, pow_zero] at hc
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hc)
    · rintro ⟨c, hc, hwc⟩
      exact (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).mpr
        ⟨c, Finset.mem_univ c, Ideal.pow_mem_of_mem _ hwc _ (Nat.pos_of_ne_zero hc)⟩
  · obtain ⟨n, w, hw⟩ := MMP.Mori.exists_isRegularSystemOfParameters (O.presheaf.stalk y)
    by_cases hyT : y ∈ (T : Set O)
    · -- `y` is the generic point of a curve: its local ring has dimension one
      obtain ⟨p, hp, hpc⟩ := (isClosed_closure (s := ({y} : Set O))).exists_closed_singleton
        ⟨y, subset_closure rfl⟩
      have hyp : y ⤳ p := specializes_iff_mem_closure.mpr hp
      have hne : p ≠ y := fun h => hy (h ▸ hpc)
      have hlt : p < y := lt_of_le_not_ge (show p ≤ y from hyp)
        (fun h => hne (Specializes.antisymm (show p ⤳ y from h) hyp).eq)
      have h2 := hO.2.2 p hpc
      rw [ringKrullDim_stalk_eq_coheight] at h2
      have h2' : Order.coheight p = 2 := by
        rw [show (2 : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) from rfl] at h2
        exact WithBot.coe_injective h2
      have h3 := Order.coheight_add_one_le hlt
      rw [h2'] at h3
      have h5 : Order.coheight y ≤ 1 := by
        by_contra h6
        push Not at h6
        have h7 : (2 : ℕ∞) ≤ Order.coheight y := Order.add_one_le_of_lt h6
        have := (add_le_add h7 (le_refl (1 : ℕ∞))).trans h3
        exact absurd this (by decide)
      have hdy : ringKrullDim (O.presheaf.stalk y) ≤ 1 := by
        rw [ringKrullDim_stalk_eq_coheight]
        exact_mod_cast h5
      have hn1 : n ≠ 0 := by
        rintro rfl
        have h0 : ringKrullDim (O.presheaf.stalk y) = 0 := by rw [hw.2]; rfl
        rw [ringKrullDim_stalk_eq_coheight] at h0
        have hmax : IsMax y := Order.coheight_eq_zero.mp (by exact_mod_cast h0)
        have hgy : genericPoint O ⤳ y := (genericPoint_spec O).specializes (Set.mem_univ y)
        have : y = genericPoint O :=
          (Specializes.antisymm (show y ⤳ genericPoint O from hmax hgy) hgy).eq
        exact hgen (this ▸ hyT)
      have hn : n = 1 := by
        have := hw.2
        rw [this] at hdy
        have : (n : WithBot ℕ∞) ≤ 1 := hdy
        have : n ≤ 1 := by exact_mod_cast this
        omega
      subst hn
      haveI : Ring.KrullDimLE 1 (O.presheaf.stalk y) := ⟨hdy⟩
      have hprime := (Ring.krullDimLE_one_iff_of_isPrime_bot (R := O.presheaf.stalk y)).mp
        inferInstance
      have hspan : Ideal.span {w 0} = IsLocalRing.maximalIdeal (O.presheaf.stalk y) := by
        rw [← hw.1]; congr 1; ext a; simp [Set.mem_range, eq_comm]
      have hw0 : w 0 ≠ 0 := by
        intro h0
        have hm : IsLocalRing.maximalIdeal (O.presheaf.stalk y) = ⊥ := by
          rw [← hspan, h0, Ideal.span_singleton_eq_bot]
        have : ringKrullDim (O.presheaf.stalk y) = 0 := by
          have hfield : IsField (O.presheaf.stalk y) :=
            (IsLocalRing.isField_iff_maximalIdeal_eq).mpr hm
          exact ringKrullDim_eq_zero_of_isField hfield
        rw [hw.2] at this
        exact absurd this (by decide)
      refine ⟨1, w, {0}, hw, ?_⟩
      rw [hpre]
      ext P
      simp only [Finset.mem_singleton, Set.iUnion_iUnion_eq_left, PrimeSpectrum.mem_zeroLocus,
        Set.singleton_subset_iff, SetLike.mem_coe]
      by_cases hP : P.asIdeal = ⊥
      · constructor
        · intro hD
          exfalso
          have hmem : P ∈ O.fromSpecStalk y ⁻¹' (T : Set O) := by rw [hpre]; exact hD
          have hmem' : O.fromSpecStalk y P ∈ (T : Set O) := hmem
          rw [fromSpecStalk_eq_genericPoint y P hP] at hmem'
          exact hgen hmem'
        · intro h0
          rw [hP] at h0
          exact absurd ((Submodule.mem_bot _).mp h0) hw0
      · have hPm : P.asIdeal = IsLocalRing.maximalIdeal _ :=
          IsLocalRing.eq_maximalIdeal (hprime P.asIdeal hP P.isPrime)
        rw [hPm]
        constructor
        · intro _; rw [← hspan]; exact Ideal.subset_span rfl
        · intro _
          apply IsLocalRing.le_maximalIdeal
          intro htop
          rw [IdealSheafData.stalk_eq_top_iff_notMem_support] at htop
          exact htop (by rwa [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal])
    · refine ⟨n, w, ∅, hw, ?_⟩
      rw [hpre, (IdealSheafData.stalk_eq_top_iff_notMem_support _ y).2
        (by rwa [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal])]
      ext P
      simp

/-- On an integral scheme, a prime divisor whose generic point lies in a closed set `T` not
containing the generic point is an irreducible component of `T`. -/
private theorem support_mem_componentsOf {O : Scheme.{u}} [IsIntegral O] (T : Closeds O)
    (hgen : genericPoint O ∉ (T : Set O)) (F : MMP.Mori.PrimeDivisor O)
    (hF : F.genericPoint ∈ (T : Set O)) :
    (F.support : Set O) ∈ MMP.Resolution.componentsOf (T : Set O) := by
  have hsupp : (F.support : Set O) = closure {F.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure F
  have hFmem : F.genericPoint ∈ (F.support : Set O) := by rw [hsupp]; exact subset_closure rfl
  refine ⟨⟨MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support F, ?_⟩,
    fun W hW hFW => ?_⟩
  · rw [hsupp]; exact closure_minimal (Set.singleton_subset_iff.mpr hF) T.isClosed
  · obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1.closure isClosed_closure
    have hWT : closure W ⊆ (T : Set O) := closure_minimal hW.2 T.isClosed
    have hξmem : ξ ∈ closure W := hξ.mem
    have hFξ : ξ ⤳ F.genericPoint := hξ.specializes (subset_closure (hFW hFmem))
    by_cases heq : ξ = F.genericPoint
    · intro w hw
      rw [hsupp, ← heq, hξ.def]
      exact subset_closure hw
    · exfalso
      have hlt : F.genericPoint < ξ := lt_of_le_not_ge (show F.genericPoint ≤ ξ from hFξ)
        (fun h => heq (Specializes.antisymm hFξ (show F.genericPoint ⤳ ξ from h)).eq)
      have hne : ξ ≠ genericPoint O := fun h => hgen (h ▸ hWT hξmem)
      have hgξ : genericPoint O ⤳ ξ := (genericPoint_spec O).specializes (Set.mem_univ ξ)
      have hlt2 : ξ < genericPoint O := lt_of_le_not_ge (show ξ ≤ genericPoint O from hgξ)
        (fun h => hne (Specializes.antisymm (show ξ ⤳ genericPoint O from h) hgξ).eq)
      have h1 := Order.coheight_add_one_le hlt
      have h2 := Order.coheight_add_one_le hlt2
      rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint F] at h1
      have h3 : (1 : ℕ∞) ≤ Order.coheight ξ := le_trans le_add_self h2
      have := (add_le_add h3 (le_refl (1 : ℕ∞))).trans h1
      exact absurd this (by decide)

/-- **From snc of the reduced structure to snc divisors.** On a regular surface over a perfect
field, if the reduced structure on a closed set `T` not containing the generic point is snc at
every closed point, every divisor whose components have their generic points in `T` is an snc
divisor. -/
private theorem isSNC_of_isSNCSubscheme {k : Type u} [Field k] [PerfectField k]
    {O : Scheme.{u}} [IsIntegral O] (sO : O ⟶ Spec (.of k)) [LocallyOfFiniteType sO]
    (hO : IsRegularSurface O) (T : Closeds O) (hgen : genericPoint O ∉ (T : Set O))
    (hT : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal T)) {R : Type*} [Zero R]
    (D : MMP.Mori.DivisorWithCoeffs R O)
    (hD : ∀ F ∈ D.support, MMP.Mori.PrimeDivisor.genericPoint F ∈ (T : Set O)) :
    MMP.Mori.DivisorWithCoeffs.IsSNC sO D := by
  classical
  haveI : CompactSpace O := hO.1.toCompactSpace
  haveI : IsLocallyNoetherian O := hO.1.toIsLocallyNoetherian
  have hcl := MMP.Resolution.isSNCClosedSubset_of_forall_isSNCAt sO T.isClosed
    (isSNCAt_of_isSNCSubscheme hO T hgen hT)
  have hcomp : ∀ F ∈ D.support, (F.support : Set O) ∈ MMP.Resolution.componentsOf (T : Set O) :=
    fun F hF => support_mem_componentsOf T hgen F (hD F hF)
  obtain ⟨-, hD0 | ⟨-, -, hfam1, hfam2⟩⟩ := hcl
  · have hsupp : D.support = ∅ := by
      by_contra hne
      obtain ⟨F, hF⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 := hD F hF
      rw [hD0] at h1
      exact h1
    have hnot : ∀ F, F ∉ D.support := fun F hF => by
      rw [hsupp] at hF; exact Finset.notMem_empty _ hF
    refine ⟨fun E hE => absurd hE (hnot E), fun x => ?_⟩
    haveI := hO.2.1 x
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (O.presheaf.stalk x)
    exact ⟨n, z, fun E => absurd E.2.1 (hnot _), hz, fun E => absurd E.2.1 (hnot _),
      fun E => absurd E.2.1 (hnot _)⟩
  · refine ⟨fun E hE => ?_, fun x => ?_⟩
    · have := (hfam1 ⟨_, hcomp E hE⟩).2.2
      rwa [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf
        ⟨_, hcomp E hE⟩ E rfl] at this
    · obtain ⟨n, z, c, hz, hI, hc⟩ := hfam2 x
      have hmem : ∀ E : {E : MMP.Mori.PrimeDivisor O // E ∈ D.support ∧ x ∈ E.support},
          x ∈ (MMP.Resolution.componentsFamily (T : Set O) ⟨_, hcomp E.1 E.2.1⟩).support :=
        fun E => by
          rw [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf
            ⟨_, hcomp E.1 E.2.1⟩ E.1 rfl]
          exact E.2.2
      refine ⟨n, z, fun E => c ⟨⟨_, hcomp E.1 E.2.1⟩, hmem E⟩, hz, ?_, fun E => ?_⟩
      · intro E E' hEE'
        have h1 := congrArg (fun W => W.1.1) (hc hEE')
        simp only at h1
        exact Subtype.ext (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset h1.le)
      · have := hI ⟨⟨_, hcomp E.1 E.2.1⟩, hmem E⟩
        rwa [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf
          ⟨_, hcomp E.1 E.2.1⟩ E.1 rfl] at this

/-- Over a perfect field, the smooth points are the points with regular local ring. -/
private theorem mem_smoothLocus_iff_isRegularLocalRing_stalk {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (y : Y) :
    y ∈ MMP.Mori.smoothLocus s ↔ IsRegularLocalRing (Y.presheaf.stalk y) := by
  rw [MMP.Mori.mem_smoothLocus_iff, ← InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp]
  exact Set.ext_iff.mp (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k s) y

/-- The local ring of a normal locally Noetherian scheme at a point of coheight at most one is
regular. -/
private theorem isRegularLocalRing_of_coheight_le_one {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] (y : Y) (hy : Order.coheight y ≤ 1) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  have hR1 : IsRegularInCodimension Y 1 :=
    ((isNormal_iff_hasPropertySk_two_and_isRegularInCodimension_one Y).mp inferInstance).2
  exact hR1 y (by rw [ringKrullDim_stalk_eq_coheight]; exact_mod_cast hy)

/-- **The curve on a smooth open.** On an open `S` of `Y` smooth over a field and containing the
generic points of finitely many prime divisors `Ps` of `Y`, the product of the ideal sheaves of
the restrictions of the `P ∈ Ps` is an effective Cartier divisor supported on the preimage of
their union. -/
private theorem exists_isEffectiveCartierDivisor_restrict {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) (S : Y.Opens) [IsLocallyNoetherian S.toScheme] [IsNormal S.toScheme]
    (hS : MMP.Mori.IsSmoothScheme (S.ι ≫ sY)) (Ps : Finset (MMP.Mori.PrimeDivisor Y))
    (hPs : ∀ P ∈ Ps, MMP.Mori.PrimeDivisor.genericPoint P ∈ S) :
    ∃ C : S.toScheme.IdealSheafData, Stacks.Divisors.IsEffectiveCartierDivisor C ∧
      (C.support : Set S.toScheme) = S.ι ⁻¹' (⋃ P ∈ Ps, (P.support : Set Y)) := by
  classical
  induction Ps using Finset.induction_on with
  | empty => exact ⟨⊤, Stacks.Divisors.isEffectiveCartierDivisor_top, by simp⟩
  | @insert P Ps hP ih =>
    obtain ⟨C, hC, hCs⟩ := ih (fun Q hQ => hPs Q (Finset.mem_insert_of_mem hQ))
    obtain ⟨P', hP'⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff S.ι P).2
      (by rw [Scheme.Opens.range_ι]; exact hPs P (Finset.mem_insert_self P Ps))
    have hI : (P.idealSheaf.comap S.ι) = P'.idealSheaf := by
      rw [← hP']
      exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap S.ι P'
    refine ⟨P'.idealSheaf * C, AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _
      (MMP.Threefold.Resolution.isEffectiveCartierDivisor_idealSheaf_of_isSmoothScheme hS P')
        hC, ?_⟩
    rw [Scheme.IdealSheafData.support_mul, ← hI, Scheme.IdealSheafData.support_comap]
    ext z
    simp only [Closeds.coe_sup, Closeds.coe_preimage, Set.mem_union, Set.mem_preimage, hCs,
      Finset.mem_insert, Set.mem_iUnion, exists_prop]
    constructor
    · rintro (h | ⟨Q, hQ, hz⟩)
      · exact ⟨P, Or.inl rfl, h⟩
      · exact ⟨Q, Or.inr hQ, hz⟩
    · rintro ⟨Q, (rfl | hQ), hz⟩
      · exact Or.inl hz
      · exact Or.inr ⟨Q, hQ, hz⟩

section OpenSubvarieties

open MMP.Mori

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-- A nonempty open of the smooth locus of a surface is a smooth surface. -/
private theorem smoothOfRelativeDimension_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsIntegral Y] (sY : Y ⟶ Spec (.of k)) (hY : IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 2) (S : Y.Opens) [Nonempty S]
    (hS : S ≤ smoothLocus sY) :
    SmoothOfRelativeDimension 2 (S.ι ≫ sY) ∧ QuasiCompact (S.ι ≫ sY) := by
  have := hY.1
  haveI : IsDominant S.ι := isDominant_opens_ι S
  haveI : IsIntegral S.toScheme := isIntegral_of_isOpenImmersion S.ι
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := {}
  haveI : QuasiCompact (S.ι ≫ sY) := inferInstance
  haveI : AlgebraicGeometry.IsVariety k (S.ι ≫ sY) := ⟨⟩
  haveI : Smooth (S.ι ≫ sY) :=
    MMP.Resolution.Aux.smooth_of_isSmoothScheme' (S.ι ≫ sY) (isSmoothScheme_ι_of_le_smoothLocus hS)
  have hdS : topologicalKrullDim S = 2 :=
    (topologicalKrullDim_opens_eq hY S).trans hdim
  exact ⟨MMP.Intersection.smoothOfRelativeDimension_of_isVariety (S.ι ≫ sY) 2 hdS, inferInstance⟩

end OpenSubvarieties

/-- The generic point of an integral scheme is maximal for specialization. -/
private theorem coheight_genericPoint_eq_zero (Y : Scheme.{u}) [IsIntegral Y] :
    Order.coheight (genericPoint Y) = 0 :=
  Order.coheight_eq_zero.mpr fun b _ => (genericPoint_spec Y).specializes (Set.mem_univ b)

/-- **Making a boundary snc away from an open.** Let `Y` be a normal projective surface over a
perfect field, `j : U ⟶ Y` an open immersion of an integral scheme such that `Y` is regular at
every point outside `U`, and `Ps` a finite set of prime divisors of `Y`. There is a normal
projective surface `Z` with a morphism `g : Z ⟶ Y` which is an isomorphism over `U`, and an open
`O ⊆ Z` containing every point outside `U`, contained in the smooth locus, on which every divisor
supported over the union of the `Ps` is snc. -/
private theorem exists_snc_outside {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    [IsIntegral Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k)) (hY : IsProjectiveVariety k sY)
    (hdim : topologicalKrullDim Y = 2) {U : Scheme.{u}} [IsIntegral U] (j : U ⟶ Y)
    [IsOpenImmersion j]
    (hreg : ∀ y : Y, y ∉ Set.range j → IsRegularLocalRing (Y.presheaf.stalk y))
    (Ps : Finset (MMP.Mori.PrimeDivisor Y)) :
    ∃ (Z : Scheme.{u}) (_ : IsIntegral Z) (_ : IsNormal Z) (g : Z ⟶ Y) (j' : U ⟶ Z)
      (O : Z.Opens), IsOpenImmersion j' ∧ j' ≫ g = j ∧ IsProjectiveVariety k (g ≫ sY) ∧
      (∀ z : Z, z ∉ Set.range j' → z ∈ O) ∧ O ≤ MMP.Mori.smoothLocus (g ≫ sY) ∧
      ∀ D : MMP.Mori.QDivisor O.toScheme,
        (∀ F ∈ D.support, g (O.ι (AlgebraicGeometry.PrimeDivisor.genericPoint F)) ∈
          ⋃ P ∈ Ps, (P.support : Set Y)) →
        MMP.Mori.DivisorWithCoeffs.IsSNC (O.ι ≫ g ≫ sY) D := by
  classical
  have hYv : AlgebraicGeometry.IsVariety k sY := hY.toIsVariety
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  have hYn : MMP.Mori.IsNormalVariety k sY := ⟨hYv, inferInstance⟩
  let Γ : Set Y := ⋃ P ∈ Ps, (P.support : Set Y)
  have hηΓ : genericPoint Y ∉ Γ := by
    intro h
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp h
    obtain ⟨-, hP⟩ := Set.mem_iUnion.mp hP
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_notMem_support P hP
  -- the smooth locus and the curve on it
  let S₀ : Y.Opens := MMP.Mori.smoothLocus sY
  have hmemS₀ : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) → y ∈ S₀ := fun y hy =>
    (mem_smoothLocus_iff_isRegularLocalRing_stalk sY y).2 hy
  have hηS₀ : genericPoint Y ∈ S₀ := hmemS₀ _ (isRegularLocalRing_of_coheight_le_one _
    (by rw [coheight_genericPoint_eq_zero]; exact bot_le))
  haveI : Nonempty S₀ := ⟨⟨_, hηS₀⟩⟩
  obtain ⟨hsm₀, hqc₀⟩ := smoothOfRelativeDimension_ι sY hYn hdim S₀ le_rfl
  haveI := hsm₀
  haveI := hqc₀
  have hS₀reg : IsRegularSurface S₀.toScheme :=
    isRegularSurface_of_smoothOfRelativeDimension (S₀.ι ≫ sY)
  haveI : IsLocallyNoetherian S₀.toScheme := inferInstance
  haveI : IsNormal S₀.toScheme := isNormal_of_flat_preimmersion S₀.ι
  have hPs : ∀ P ∈ Ps, AlgebraicGeometry.PrimeDivisor.genericPoint P ∈ S₀ := fun P _ =>
    hmemS₀ _ (isRegularLocalRing_of_coheight_le_one _
      (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le)
  obtain ⟨C₀, hC₀, hC₀s⟩ := exists_isEffectiveCartierDivisor_restrict sY S₀
    (MMP.Mori.isSmoothScheme_ι_of_le_smoothLocus le_rfl) Ps hPs
  let C₀' := Scheme.IdealSheafData.vanishingIdeal C₀.support
  have hC₀' : Stacks.Divisors.IsEffectiveCartierDivisor C₀' :=
    isEffectiveCartierDivisor_vanishingIdeal_support hS₀reg.2.1 hC₀
  haveI : IsReduced C₀'.subscheme := Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _
  have hC₀'s : (C₀'.support : Set S₀.toScheme) = S₀.ι ⁻¹' Γ := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, hC₀s]
  -- the singular points of the curve lying in `U`
  let Fs : Set S₀.toScheme := {p : S₀.toScheme | IsClosed ({p} : Set S₀.toScheme) ∧
    p ∈ C₀'.support ∧
      ¬ IsRegularLocalRing (S₀.toScheme.presheaf.stalk p ⧸ IdealSheafData.stalk C₀' p)}
  have hFfin : Fs.Finite := finite_singular_points (S₀.ι ≫ sY) C₀' hC₀'
  let N : Set Y := S₀.ι '' {p | p ∈ Fs ∧ S₀.ι p ∈ Set.range j}
  have hNfin : N.Finite := (hFfin.subset fun p hp => hp.1).image _
  have hNcl : IsClosed N := by
    rw [← Set.biUnion_of_singleton N]
    exact hNfin.isClosed_biUnion (by
      rintro _ ⟨p, hp, rfl⟩
      exact isClosed_singleton_of_isOpenImmersion S₀.ι hp.1.1)
  have hNΓ : N ⊆ Γ := by
    rintro _ ⟨p, hp, rfl⟩
    have h : p ∈ (C₀'.support : Set S₀.toScheme) := hp.1.2.1
    rw [hC₀'s] at h
    exact h
  have hNj : N ⊆ Set.range j := by
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  -- the open on which the curve is resolved
  let S : Y.Opens := S₀ ⊓ ⟨Nᶜ, hNcl.isOpen_compl⟩
  have hSS₀ : S ≤ S₀ := inf_le_left
  have hηS : genericPoint Y ∈ S := ⟨hηS₀, fun h => hηΓ (hNΓ h)⟩
  haveI : Nonempty S := ⟨⟨_, hηS⟩⟩
  obtain ⟨hsm, hqc⟩ := smoothOfRelativeDimension_ι sY hYn hdim S hSS₀
  haveI := hsm
  haveI := hqc
  have hSreg : IsRegularSurface S.toScheme :=
    isRegularSurface_of_smoothOfRelativeDimension (S.ι ≫ sY)
  let ιSS : S.toScheme ⟶ S₀.toScheme := Y.homOfLE hSS₀
  have hιSS : ∀ x : S.toScheme, S₀.ι (ιSS x) = S.ι x := fun x => by
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
  let C := C₀'.comap ιSS
  have hC : Stacks.Divisors.IsEffectiveCartierDivisor C :=
    Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion C₀' hC₀' ιSS
  have hCs : ∀ x : S.toScheme, x ∈ (C.support : Set S.toScheme) ↔ S.ι x ∈ Γ := by
    intro x
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage, hC₀'s,
      Set.mem_preimage, hιSS]
  obtain ⟨s, hs, n, hn, hsnc⟩ := exists_strongEmbeddedResolutionStops (S.ι ≫ sY) C hC
  -- the centres lie outside `U`
  let W : S.toScheme.Opens := S.ι ⁻¹ᵁ j.opensRange
  have hW : ∀ w : S.toScheme, w ∈ W → IsClosed ({w} : Set S.toScheme) →
      HasSNCAt (Scheme.IdealSheafData.vanishingIdeal C.support) w := by
    intro w hwW hw
    have heq : Scheme.IdealSheafData.vanishingIdeal C.support =
        (Scheme.IdealSheafData.vanishingIdeal C₀'.support).comap ιSS := by
      rw [comap_vanishingIdeal_of_isOpenImmersion, Scheme.IdealSheafData.support_comap]
      rfl
    rw [heq, hasSNCAt_comap_iff]
    have hw0 : IsClosed ({ιSS w} : Set S₀.toScheme) :=
      isClosed_singleton_of_ι S₀ _ (by
        rw [hιSS]; exact isClosed_singleton_of_isOpenImmersion S.ι hw)
    refine hasSNCAt_vanishingIdeal_support_of_isRegularLocalRing hS₀reg C₀' hC₀' hw0
      fun hmem => ?_
    by_contra hnr
    have hwj : S₀.ι (ιSS w) ∈ Set.range j := by
      rw [hιSS]
      exact hwW
    have hN : S.ι w ∈ N := ⟨ιSS w, ⟨⟨hw0, hmem, hnr⟩, hwj⟩, hιSS w⟩
    exact w.2.2 hN
  have hiso := isIso_π_restrict (S.ι ≫ sY) C s hs W hW
  have hcen : ∀ (i : ℕ) (hi : (i : ℕ∞) < s.length), S.ι (s.π i hi.le (s.p i)) ∉ j.opensRange :=
    fun i hi h => π_p_notMem (S.ι ≫ sY) C s hs W hW i hi (hiso i hi.le) h
  have hVne : (j.opensRange : Set Y).Nonempty := ⟨j (Classical.arbitrary U), ⟨_, rfl⟩⟩
  -- globalizing the resolution
  obtain ⟨A, hA, ⟨e⟩⟩ := exists_globalization sY hY.isProjective S j.opensRange hVne hSreg s
    hcen n hn.ge
  obtain ⟨hAn, hAi, hAp, -⟩ := stage_props sY (V := j.opensRange) (A := Over.mk (𝟙 Y))
    ⟨inferInstanceAs (IsNormal Y), inferInstanceAs (IsIntegral Y),
      by simpa using hY.isProjective, ⟨j (Classical.arbitrary U), ⟨_, rfl⟩⟩⟩ hA
  obtain ⟨-, hAiso⟩ := isIso_restrict_of_reflTransGen (V := j.opensRange)
    (A := Over.mk (𝟙 Y)) (inferInstanceAs (IsNormal Y))
    (by change IsIso (𝟙 Y ∣_ j.opensRange); infer_instance) hA
  haveI := hAn
  haveI := hAi
  haveI : IsIso (A.hom ∣_ j.opensRange) := hAiso
  haveI : IsProper (A.hom ≫ sY) := isProper_of_isProjectiveMorphism _ hAp
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian (A.hom ≫ sY)
  have hproj : IsProjectiveVariety k (A.hom ≫ sY) := by
    haveI : AlgebraicGeometry.IsVariety k (A.hom ≫ sY) := ⟨⟩
    exact ⟨hAp⟩
  let j' : U ⟶ A.left :=
    j.isoOpensRange.hom ≫ inv (A.hom ∣_ j.opensRange) ≫ (A.hom ⁻¹ᵁ j.opensRange).ι
  have hj' : j' ≫ A.hom = j := by
    simp only [j', Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]
  -- the open over `S`
  let O : A.left.Opens := A.hom ⁻¹ᵁ S
  let eO : O.toScheme ≅ s.S n :=
    (pullbackRestrictIsoRestrict A.hom S).symm ≪≫ (Over.forget _).mapIso e
  have heO : eO.hom ≫ s.π n hn.ge = A.hom ∣_ S := by
    have hw : e.hom.left ≫ s.π n hn.ge = Limits.pullback.snd A.hom S.ι := Over.w e.hom
    change (pullbackRestrictIsoRestrict A.hom S).inv ≫ e.hom.left ≫ s.π n hn.ge = _
    rw [hw]
    rfl
  have h1 : eO.hom ≫ s.π n hn.ge ≫ S.ι = O.ι ≫ A.hom := by
    rw [← Category.assoc, heO, morphismRestrict_ι]
  have hpt : ∀ x : O.toScheme, S.ι (s.π n hn.ge (eO.hom x)) = A.hom (O.ι x) := fun x =>
    calc S.ι (s.π n hn.ge (eO.hom x)) = (eO.hom ≫ s.π n hn.ge ≫ S.ι) x := by
          rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      _ = (O.ι ≫ A.hom) x := by rw [h1]
      _ = A.hom (O.ι x) := Scheme.Hom.comp_apply _ _ _
  have hSn : IsRegularSurface (s.S n) := isRegularSurface_S hSreg s n hn.ge
  haveI : IsLocallyNoetherian (s.S n) := hSn.1.toIsLocallyNoetherian
  haveI : IsLocallyNoetherian O.toScheme := inferInstance
  have hOreg : IsRegularSurface O.toScheme := isRegularSurface_of_iso eO hSn
  let T : Closeds O.toScheme :=
    ⟨eO.hom ⁻¹' (C.comap (s.π n hn.ge)).support,
      (C.comap (s.π n hn.ge)).support.isClosed.preimage eO.hom.continuous⟩
  have hTmem : ∀ x : O.toScheme, x ∈ (T : Set O.toScheme) ↔ A.hom (O.ι x) ∈ Γ := by
    intro x
    change eO.hom x ∈ ((C.comap (s.π n hn.ge)).support : Set (s.S n)) ↔ _
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage, hCs, hpt]
  have hTsnc : IsSNCSubscheme (Scheme.IdealSheafData.vanishingIdeal T) :=
    isSNCSubscheme_vanishingIdeal_preimage eO _ hsnc
  -- generic points
  have hAη : A.hom (genericPoint A.left) = genericPoint Y := by
    rw [← genericPoint_eq_of_isOpenImmersion j', ← Scheme.Hom.comp_apply, hj',
      genericPoint_eq_of_isOpenImmersion j]
  have hηO : genericPoint A.left ∈ O := by
    change A.hom (genericPoint A.left) ∈ S
    rw [hAη]
    exact hηS
  haveI : Nonempty O := ⟨⟨_, hηO⟩⟩
  haveI : IsIntegral O.toScheme := isIntegral_of_isOpenImmersion O.ι
  have hgen : genericPoint O.toScheme ∉ (T : Set O.toScheme) := by
    rw [hTmem, genericPoint_eq_of_isOpenImmersion O.ι, hAη]
    exact hηΓ
  refine ⟨A.left, hAi, hAn, A.hom, j', O, inferInstance, hj', hproj, ?_, ?_, ?_⟩
  · intro z hz
    change A.hom z ∈ S
    by_cases hzV : A.hom z ∈ j.opensRange
    · exfalso
      apply hz
      let w : (A.hom ⁻¹ᵁ j.opensRange).toScheme := ⟨z, hzV⟩
      refine ⟨j.isoOpensRange.inv ((A.hom ∣_ j.opensRange) w), ?_⟩
      simp only [j']
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.inv_hom_apply]
      exact congrArg (A.hom ⁻¹ᵁ j.opensRange).ι (Scheme.hom_inv_apply (asIso _) w)
    · have hzj : A.hom z ∉ Set.range j := hzV
      exact ⟨hmemS₀ _ (hreg _ hzj), fun hN => hzj (hNj hN)⟩
  · intro x hx
    refine MMP.Mori.mem_smoothLocus_iff.2 ⟨O, hx, ?_⟩
    have h2 : O.ι ≫ A.hom ≫ sY = eO.hom ≫ s.π n hn.ge ≫ S.ι ≫ sY := by
      rw [← Category.assoc, ← h1, Category.assoc, Category.assoc]
    obtain ⟨hπ, -⟩ := smoothOfRelativeDimension_π_comp (S.ι ≫ sY) s n hn.ge
    haveI := hπ
    haveI : Smooth (s.π n hn.ge ≫ S.ι ≫ sY) := SmoothOfRelativeDimension.smooth 2 _
    rw [h2]
    infer_instance
  · intro D hD
    exact isSNC_of_isSNCSubscheme (O.ι ≫ A.hom ≫ sY) hOreg T hgen hTsnc D
      fun F hF => (hTmem _).2 (hD F hF)

/-- **Resolving the singular points outside an open.** Let `X` be a normal projective surface
over a field and `ι : U ⟶ X` an open immersion. There is a normal projective surface `Y` with a
morphism `g : Y ⟶ X` which is an isomorphism over `U` and whose source is regular at every point
outside `U`. -/
private theorem exists_regular_outside {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsNormal X] (sX : X ⟶ Spec (.of k)) (hX : IsProjectiveVariety k sX)
    (hdim : topologicalKrullDim X = 2) {U : Scheme.{u}} [Nonempty U] (ι : U ⟶ X)
    [IsOpenImmersion ι] :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (_ : IsNormal Y) (g : Y ⟶ X) (j : U ⟶ Y),
      IsOpenImmersion j ∧ j ≫ g = ι ∧ IsProjectiveVariety k (g ≫ sX) ∧
        ∀ y : Y, y ∉ Set.range j → IsRegularLocalRing (Y.presheaf.stalk y) := by
  classical
  have hk : IsExcellent k := isExcellent_of_standard_classes_and_finiteType.{u, u}.1 k
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := {}
  have hsing : (singularLocus X).Finite :=
    finite_singularLocus_of_locallyOfFiniteType_of_isExcellent hk sX hdim.le
  -- the singular points outside `U`
  let T : Set X := singularLocus X \ Set.range ι
  have hT : T.Finite := hsing.subset Set.diff_subset
  let : Fintype T := hT.fintype
  let eT : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  have hTclosed : ∀ t ∈ T, IsClosed ({t} : Set X) := fun t ht =>
    isClosed_singleton_of_mem_singularLocus X hdim.le t ht.1
  let D : FinitePresentationAwayPointsSituation.{u} :=
    { S := X
      n := Fintype.card T
      points := fun i => (eT i).1
      points_injective := fun i j h => eT.injective (Subtype.ext h)
      points_closed := fun i => hTclosed _ (eT i).2
      complement_quasiCompact := inferInstance }
  have hDrange : Set.range D.points = T := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro y ⟨i, rfl⟩
      exact (eT i).2
    · intro y hy
      obtain ⟨i, hi⟩ := eT.surjective ⟨y, hy⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  haveI : IsNormal D.S := inferInstanceAs (IsNormal X)
  haveI : IsLocallyNoetherian D.S := inferInstanceAs (IsLocallyNoetherian X)
  have hcomponents : ∀ V : D.S.Opens, IsCompact (V : Set D.S) →
      (irreducibleComponents V).Finite := finite_irreducibleComponents_of_isCompact D.S
  -- local resolutions at the points of `T`
  have hlocal : ∀ i : Fin D.n, ∃ Z : Over (D.localScheme i),
      Relation.ReflTransGen (IsProperNormalizedBlowUpOutside (D.puncturedLocalScheme i))
        (Over.mk (𝟙 (D.localScheme i))) Z ∧ IsProper Z.hom ∧ IsRegular Z.left := by
    intro i
    let : Flat (D.S.fromSpecStalk (D.points i)) := flat_fromSpecStalk D.S (D.points i)
    let : IsNormal (D.localScheme i) :=
      isNormal_of_flat_preimmersion (D.S.fromSpecStalk (D.points i))
    let : IsLocallyNoetherian (D.localScheme i) := by
      change IsLocallyNoetherian (Spec (.of (D.S.presheaf.stalk (D.points i))))
      exact isLocallyNoetherian_Spec.mpr inferInstance
    refine exists_reflTransGen_of_hasResolutionByNormalizedBlowUps _ (fun z hz hzU => ?_) ?_
    · exact hzU (Set.mem_singleton_iff.mpr
        (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
          ((PrimeSpectrum.isClosed_singleton_iff_isMaximal z).mp hz))))
    · haveI : IsNormalDomain (X.presheaf.stalk (D.points i)) := ⟨inferInstance, inferInstance⟩
      exact hasResolutionByNormalizedBlowUps_of_isExcellent_of_ringKrullDim_eq_two _
        (isExcellent_stalk_of_locallyOfFiniteType hk sX _)
        (ringKrullDim_stalk_eq_two_of_mem_singularLocus X hdim.le _ (eT i).2.1)
  choose Z hZ hZproper hZreg using hlocal
  obtain ⟨A, hA, hAproper, hAlocal, ⟨eAU⟩⟩ :=
    D.exists_properNormalizedBlowUpSequence_of_local hcomponents Z hZ
  have hιC : ∀ u : U, ι u ∈ D.complement := by
    intro u hu
    obtain ⟨i, hi⟩ := hu
    have := (eT i).2.2
    exact this ⟨u, hi.symm⟩
  obtain ⟨hAn, hAi, hAp, -⟩ := stage_props sX (V := D.complement) (A := Over.mk (𝟙 X))
    ⟨inferInstanceAs (IsNormal X), inferInstanceAs (IsIntegral X),
      by simpa using hX.isProjective, ⟨ι (Classical.arbitrary U), hιC _⟩⟩
    (reflTransGen_isNormalizedBlowUpOutside_of_isProper hA)
  -- the isomorphism over the complement
  let C := D.complement
  let P := Limits.pullback A.hom C.ι
  let fst : P ⟶ A.left := Limits.pullback.fst A.hom C.ι
  let snd : P ⟶ C := Limits.pullback.snd A.hom C.ι
  haveI : IsIso snd := by
    have h := eAU.hom.w
    simp only [Functor.id_obj, Functor.const_obj_obj, Over.mk_hom, Category.comp_id] at h
    have h' : eAU.hom.left = Limits.pullback.snd A.hom C.ι := h
    have : IsIso eAU.hom.left := by
      simpa only [Over.forget_map] using Functor.map_isIso (Over.forget _) eAU.hom
    change IsIso (Limits.pullback.snd A.hom C.ι)
    rw [← h']
    infer_instance
  have hrange : Set.range ι ⊆ Set.range C.ι := by
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨ι u, hιC u⟩, rfl⟩
  let ι' : U ⟶ C := IsOpenImmersion.lift C.ι ι hrange
  have hι' : ι' ≫ C.ι = ι := IsOpenImmersion.lift_fac _ _ _
  let j : U ⟶ A.left := ι' ≫ inv snd ≫ fst
  have hj : j ≫ A.hom = ι := by
    simp only [j, Category.assoc, fst, Limits.pullback.condition]
    rw [← Category.assoc (inv snd), IsIso.inv_hom_id, Category.id_comp]
    exact hι'
  haveI : IsProper A.hom := hAproper
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  refine ⟨A.left, hAi, hAn, A.hom, j, inferInstance, hj, ?_, ?_⟩
  · haveI : IsSeparated (A.hom ≫ sX) := inferInstance
    haveI : AlgebraicGeometry.IsVariety k (A.hom ≫ sX) := ⟨⟩
    exact ⟨hAp⟩
  · intro y hy
    by_cases hyC : A.hom y ∈ C
    · obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := C.ι)
        y ⟨A.hom y, hyC⟩ rfl
      subst hw
      have hsw : C.ι (snd w) = A.hom (fst w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Limits.pullback.condition]
      have hpt : A.hom (fst w) ∉ singularLocus X := by
        intro hsingy
        have hyι : A.hom (fst w) ∉ Set.range ι := by
          rintro ⟨u, hu⟩
          refine hy ⟨u, ?_⟩
          have h1 : snd w = ι' u := by
            apply C.ι.isOpenEmbedding.injective
            rw [hsw, ← hu, ← hι', Scheme.Hom.comp_apply]
          have h2 : inv snd (ι' u) = w := by
            rw [← h1, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
          change fst (inv snd (ι' u)) = fst w
          rw [h2]
        exact hyC (by rw [hDrange]; exact ⟨hsingy, hyι⟩)
      have h1 : IsRegularLocalRing (X.presheaf.stalk (A.hom (fst w))) := not_not.mp hpt
      rw [← hsw] at h1
      haveI : IsIso (C.ι.stalkMap (snd w)) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
      haveI : IsIso (snd.stalkMap w) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
      haveI : IsIso (fst.stalkMap w) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
      exact (isRegularLocalRing_stalk_iff_of_isIso fst w).2
        ((isRegularLocalRing_stalk_iff_of_isIso snd w).1
          ((isRegularLocalRing_stalk_iff_of_isIso C.ι (snd w)).1 h1))
    · have hyp : A.hom y ∈ Set.range D.points := not_not.mp hyC
      obtain ⟨i, hi⟩ := hyp
      let s := D.S.fromSpecStalk (D.points i)
      let q := Limits.pullback.fst A.hom s
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := s)
        y (IsLocalRing.closedPoint _) (by rw [Scheme.fromSpecStalk_closedPoint]; exact hi.symm)
      subst hw
      let : Flat s := flat_fromSpecStalk D.S (D.points i)
      haveI : IsIso (q.stalkMap w) := isIso_stalkMap_of_flat_preimmersion q w
      haveI : IsProper ((Over.pullback s).obj A).hom := by
        change IsProper (Limits.pullback.snd A.hom s)
        infer_instance
      haveI : IsLocallyNoetherian ((Over.pullback s).obj A).left :=
        LocallyOfFiniteType.isLocallyNoetherian ((Over.pullback s).obj A).hom
      have hreg : IsRegular ((Over.pullback s).obj A).left :=
        isRegular_of_iso ((Over.forget _).mapIso (hAlocal i).some) (hZreg i)
      exact (isRegularLocalRing_stalk_iff_of_isIso q w).2
        (isRegularLocalRing_stalk_of_isRegular hreg w)

end Resolve

namespace Extend

open TopologicalSpace Opposite MMP.Mori Resolve

section Restrict

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

section DivisorialRestrict

/-! ### The divisorial sheaf on an open subscheme -/

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

/-- On an irreducible scheme there is only one irreducible component meeting an open. -/
private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

/-- The generic point of every irreducible component specializes to the generic point. -/
private theorem specializes_genericPoint_of_isIntegral {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (MMP.Fourfold.componentGenericPoint_eq_genericPoint Z)).specializes

/-- The specialization map of a point to itself is the identity. -/
private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes (componentGenericPoint _ Z.1))).hom (φ Z)

/-- `evFF` does not depend on the chosen component. -/
private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes
        (genericPoint_specializes (componentGenericPoint _ E.component))).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

/-- `OrdGE` in terms of the divisorial valuation on the function field. -/
private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes
          (genericPoint_specializes (componentGenericPoint _ E.component))).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes
            (genericPoint_specializes (componentGenericPoint _ E.component))).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1
      (MMP.Intersection.stalkSpecializes_injective (genericPoint_specializes _))]

/-- `OrdGE` of a section of `𝒦_Y`, read through `evFF`. -/
private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

/-- An open of `U` meeting a component contains the generic point of `U`. -/
private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at this

/-- An open `V` of `U` whose image contains a component generic point of `X` contains the
generic point of `U`. -/
private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component (all of `Y`) of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

/-- The unique component of `X`, as an index over `U.ι ''ᵁ V`. -/
private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

/-- The unique component of `U`, as an index over `V`. -/
private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint_of_isIntegral Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

/-- `restrictRF` is `functionFieldMap U.ι` on function-field values. -/
private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, TopCat.Presheaf.stalkSpecializes_comp_apply,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

/-- `restrictRF` is injective. -/
private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact MMP.Intersection.stalkSpecializes_injective (genericPoint_specializes _)
    ((functionFieldMap U.ι).injective h1)

/-- `restrictRF` is surjective. -/
private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' =>
    (X.presheaf.stalkSpecializes (specializes_genericPoint_of_isIntegral Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint_of_isIntegral Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint_of_isIntegral _)).hom
        (e.symm _)))) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint_of_isIntegral Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    TopCat.Presheaf.stalkSpecializes_comp_apply, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    Divisor.IsDivisorialSection (D.restrictOpen U) V (restrictRF U V ψ) ↔
      D.IsDivisorialSection (U.ι ''ᵁ V) ψ := by
  have key : ∀ (E' : MMP.Mori.PrimeDivisor U.toScheme) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty),
      E'.OrdGE (-(D.restrictOpen U).coeff E')
          (restrictRF U V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        MMP.Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap U.ι E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap U.ι E'))
          (ψ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF U V ψ _ ⟨_, MMP.Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap U.ι E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap U.ι).injective,
      DivisorWithCoeffs.coeff_restrictOpen]
    rfl
  have hmem : ∀ E' : MMP.Mori.PrimeDivisor U.toScheme, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap U.ι E').support ∩ U.ι ''ᵁ V).Nonempty := by
    intro E'
    rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff, ← MMP.Mori.PrimeDivisor.genericPoint_mem_iff,
      show MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap U.ι E') =
        U.ι E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨x, hx, hxe⟩
      rwa [U.ι.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range U.ι.base := by
      rw [Scheme.Opens.range_ι]
      obtain ⟨x, -, hx⟩ := (MMP.Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      rw [← hx]
      exact x.2
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

/-- Germs at the generic point are compatible with `U.ι.appIso` and `functionFieldMap U.ι`. -/
private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

/-- `restrictRF` is semilinear over `U.ι.appIso`. -/
private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

/-- `restrictRF` preserves zero. -/
private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

/-- `restrictRF` is additive. -/
private theorem restrictRF_add (V : U.toScheme.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V (ψ₁ + ψ₂) = restrictRF U V ψ₁ + restrictRF U V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict U.ι ⟶ Divisor.divisorialSheaf (D.restrictOpen U) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF U V.unop (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff U D V.unop _).2
              (ψ : D.divisorialSubmodule (U.ι ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (D.restrictOpen U) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero U V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add U V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul U V.unop r _)⟩

/-- `divisorialSheafRestrictHom` is an isomorphism. -/
private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom U D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (U.ι ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF U V ψ₁.1 = restrictRF U V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective U V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective U V (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff U D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (D.restrictOpen U) V).2)⟩ :
        D.divisorialSubmodule (U.ι ''ᵁ V)), Subtype.ext hψ⟩

end DivisorialRestrict

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictOpen_iso (D : Divisor X) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] :
    Nonempty (Divisor.divisorialSheaf (D.restrictOpen U) ≅ D.divisorialSheaf.restrict U.ι) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom U D)).symm⟩

/-- Relative differential forms restrict along an open immersion: for `ψ : Z ⟶ Y` an open
immersion and `p' = ψ ≫ p`, `(Ω^n_{Y/S})|_Z ≅ Ω^n_{Z/S}`. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_restrictOpen {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- The smooth locus of an open subscheme `U ⊆ X` lies in the smooth locus of `X`. -/
private theorem range_smoothLocus_subset (U : X.Opens) :
    Set.range ((smoothLocus (U.ι ≫ sX)).ι ≫ U.ι) ⊆ Set.range (smoothLocus sX).ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 x.2
  let V := (W.ι ≫ U.ι).opensRange
  have e : (W.ι ≫ U.ι).isoOpensRange.inv ≫ (W.ι ≫ U.ι) = V.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hV : Smooth (V.ι ≫ sX) := by
    rw [← e, Category.assoc, Category.assoc]
    infer_instance
  refine le_smoothLocus sX hV ⟨⟨x.1, hxW⟩, rfl⟩

/-- On the smooth locus of a nonempty open subscheme `U`, the divisorial sheaf of `K|_U` is the
canonical sheaf when that of `K` is on the smooth locus of `X`. -/
private theorem nonempty_restrict_smoothLocus_iso {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U] [IsDominant U.ι] :
    Nonempty ((Divisor.divisorialSheaf (K.restrictOpen U)).restrict (smoothLocus (U.ι ≫ sX)).ι ≅
      canonicalSheaf (U.ι ≫ sX) n) := by
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso K U
  let T := smoothLocus (U.ι ≫ sX)
  let S := smoothLocus sX
  let ψ : T.toScheme ⟶ S := IsOpenImmersion.lift S.ι (T.ι ≫ U.ι) (range_smoothLocus_subset U)
  have hψ : ψ ≫ S.ι = T.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso ψ (S.ι ≫ sX)
    (T.ι ≫ U.ι ≫ sX) (by rw [← Category.assoc, hψ, Category.assoc]) n
  exact ⟨(Scheme.Modules.restrictFunctor T.ι).mapIso e₀ ≪≫
    (Scheme.Modules.restrictFunctorComp T.ι U.ι).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorCongr hψ.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ψ S.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso hK.iso ≪≫ e₁⟩

/-- The restriction of a canonical divisor to a nonempty open subscheme is canonical. -/
private theorem isCanonicalDivisor_restrictOpen {n : ℕ} {K : Divisor X}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n) (U : X.Opens) [Nonempty U]
    [IsDominant U.ι] :
    Divisor.IsCanonicalDivisor (U.ι ≫ sX) n (K.restrictOpen U) :=
  ⟨(topologicalKrullDim_opens_eq hX U).trans hK.1, nonempty_restrict_smoothLocus_iso hK U⟩

end Restrict

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS with hT
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := isDominant_opens_ι T
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_restrictOpen hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : IsIntegral T := inferInstance
  haveI : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : KS.restrictOpen T = KT := by
    ext W
    rw [MMP.Mori.DivisorWithCoeffs.coeff_restrictOpen]
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictOpen_iso KS T
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

/-- A variety of dimension `n` with an exceptional divisor over it has `n ≥ 2`. -/
private theorem two_le_of_isExceptional {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {D : DivisorOver k sX} (hD : D.IsExceptional) : 2 ≤ n := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  rw [hn] at h
  have h0 : 0 ≤ topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) :=
    Order.krullDim_nonneg_iff.mpr ⟨⟨closure {⟨_, subset_closure rfl⟩},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have : ((Order.coheight (D.f D.E.genericPoint) : ℕ∞) : WithBot ℕ∞) ≤ n :=
    h ▸ le_add_of_nonneg_left h0
  exact_mod_cast ((MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hX D).mp hD).trans
    (WithBot.coe_le_coe.mp this)

/-- The minimum in the snc discrepancy formula is `≥ -1` when every coefficient is `≤ 1`. -/
private theorem neg_one_le_inf_snc_bound {ι : Type*} (S : Finset ι) (c : ι → ℚ)
    (hc : ∀ i ∈ S, c i ≤ 1) (P Q : ι → ι → Prop) :
    (-1 : EReal) ≤ (⨅ (i ∈ S) (j ∈ S) (_ : P i j) (_ : Q i j),
        (((1 - c i - c j : ℚ) : ℝ) : EReal)) ⊓ (⨅ i ∈ S, (((1 - c i : ℚ) : ℝ) : EReal)) ⊓ 1 := by
  have hL : ∀ q : ℚ, -1 ≤ q → (-1 : EReal) ≤ ((q : ℝ) : EReal) := fun q hq => by
    simpa using EReal.coe_le_coe_iff.mpr (by exact_mod_cast hq : (-1 : ℝ) ≤ q)
  refine le_inf (le_inf ?_ ?_) ?_
  · refine le_iInf₂ fun i hi => le_iInf₂ fun j hj => le_iInf₂ fun _ _ => hL _ ?_
    linarith [hc i hi, hc j hj]
  · exact le_iInf₂ fun i hi => hL _ (by linarith [hc i hi])
  · simpa using hL 1 (by norm_num)

/-- **Snc pairs with coefficients `≤ 1` are lc**, divisor by divisor: on a smooth variety over
a perfect field, if `Δ` is snc with every coefficient `≤ 1`, then every discrepancy
`a(E, X, Δ)` is `≥ -1`, for every divisor `E` over `X`, exceptional or not. -/
private theorem neg_one_le_of_isSNC {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hsm : IsSmoothScheme sX) (hsnc : Δ.IsSNC sX)
    (hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P ≤ 1) {D : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  classical
  by_cases hD : D.IsExceptional
  · have h := discrep_le hD ha
    rw [discrep_eq_of_isSNC sX ha.1 hsm
      (two_le_of_isExceptional ha.1 ha.2.1.topologicalKrullDim_eq hD) ha.2.1 Δ.support le_rfl
      (hsnc.of_support_subset <| Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr
        fun E hE => Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr hE))
      (fun E _ => hcoeff E)] at h
    have : ((-1 : ℝ) : EReal) ≤ ((a : ℝ) : EReal) := by
      simpa using (neg_one_le_inf_snc_bound _ _ (fun E _ => hcoeff E) _ _).trans h
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  · exact MMP.Mori.neg_one_le_of_not_isExceptional hcoeff hD ha

/-- **Discrepancies over an snc open are at least `-1`.** Let `(X, Δ)` be a pair with every
coefficient `≤ 1`, and `U ⊆ X` an open subset of the smooth locus on which `Δ` is snc. Every
divisor over `X` whose center meets `U` has discrepancy `≥ -1`: the discrepancy is computed on
`U`, where `neg_one_le_of_isSNC` applies. -/
private theorem neg_one_le_of_isSNC_restrictOpen {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hΔ : IsPairWith sX n K Δ)
    (hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P ≤ 1) {U : X.Opens}
    (hsm : U ≤ smoothLocus sX) (hsnc : (Δ.restrictOpen U).IsSNC (U.ι ≫ sX))
    {D : DivisorOver k sX} (hDU : ((D.center : Set X) ∩ U).Nonempty) {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  obtain ⟨_, _, _, -, -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hΔ D U hDU
  have : Nonempty U := ⟨⟨hDU.choose, hDU.choose_spec.2⟩⟩
  exact neg_one_le_of_isSNC (isSmoothScheme_ι_of_le_smoothLocus hsm) hsnc
    (fun P => by simpa [DivisorWithCoeffs.coeff_restrictOpen] using hcoeff _) ((hiff a).mp ha)

/-- An open immersion restricted over its image is an isomorphism. -/
private theorem isIso_morphismRestrict_opensRange {U V : Scheme.{u}} (j : U ⟶ V)
    [IsOpenImmersion j] : IsIso (j ∣_ j.opensRange) := by
  have : Surjective (j ∣_ j.opensRange) := by
    constructor
    rintro ⟨y, u, rfl⟩
    refine ⟨⟨u, show u ∈ j ⁻¹ᵁ j.opensRange from ⟨u, rfl⟩⟩, ?_⟩
    exact Subtype.ext (morphismRestrict_base_coe j _ _)
  exact isIso_of_mono_of_strongEpi (j ∣_ j.opensRange)

/-- The extension of a divisor on an open subscheme to the ambient scheme: each prime divisor is
replaced by its closure. -/
private noncomputable def strictClosureDivisor {R : Type*} [AddCommMonoid R] {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] (B : DivisorWithCoeffs R U) : DivisorWithCoeffs R V :=
  Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap j) B

/-- The coefficient of `strictClosureDivisor j B` along the closure of `P` is that of `P`. -/
private theorem strictClosureDivisor_apply {R : Type*} [AddCommMonoid R] {U V : Scheme.{u}}
    (j : U ⟶ V) [IsOpenImmersion j] (B : DivisorWithCoeffs R U) (P : MMP.Mori.PrimeDivisor U) :
    strictClosureDivisor j B (OpenWeilRestriction.primeDivisorMap j P) = B P :=
  Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective j) B P

/-- `strictClosureDivisor j B` vanishes along prime divisors missing the image of `j`. -/
private theorem strictClosureDivisor_apply_of_notMem {R : Type*} [AddCommMonoid R]
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (B : DivisorWithCoeffs R U)
    (Q : MMP.Mori.PrimeDivisor V)
    (hQ : Q.genericPoint ∉ Set.range j) : strictClosureDivisor j B Q = 0 := by
  refine Finsupp.mapDomain_notin_range B Q ?_
  rintro ⟨P, rfl⟩
  exact hQ ((OpenWeilRestriction.mem_range_primeDivisorMap_iff j _).1 ⟨P, rfl⟩)

/-- The inverse transform of the extension along an open immersion is the divisor itself. -/
private theorem inverseTransformDivisor_strictClosureDivisor {R : Type*} [AddCommMonoid R]
    {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] (B : DivisorWithCoeffs R U) :
    inverseTransformDivisor j (strictClosureDivisor j B) = B := by
  have hiso := isIso_morphismRestrict_opensRange j
  have hbir : ∀ u : U, j u ∈ biregularLocus j := fun u =>
    le_biregularLocus hiso ⟨u, rfl⟩
  refine Finsupp.ext fun P => ?_
  have h1 : inverseTransformPrimeDivisor j (OpenWeilRestriction.primeDivisorMap j P) = some P :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap j P).symm (hbir _)
  refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h1 (fun E' hE' => ?_) _).trans
    (strictClosureDivisor_apply j B P)
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1]

section LocalCartier

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor whose restriction to an open `V` is Cartier has a local equation near every point
of `V`: a local equation of `D|_V` on `W ⊆ V` is one of `D` on `W`, since the prime divisors of
`X` meeting `W` are the closures of those of `V` meeting `W`, with the same local rings. -/
private theorem exists_isLocalEquation_of_isCartier_restrictOpen {D : Divisor X} {V : X.Opens}
    (h : Divisor.IsCartier (D.restrictOpen V)) {x : X} (hx : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation W φ := by
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨x, hx⟩)
  obtain ⟨W, hxW, φ', hφ'⟩ := h ⟨x, hx⟩
  obtain ⟨g', hg', hφg'⟩ := MMP.Positivity.exists_ord_eq_of_units φ'
  obtain ⟨g, rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤
    ⟨⟨x, hx⟩, trivial⟩).2 g'
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (g := g)
    (fun h0 => hg' (by rw [h0, map_zero]))
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hxW, rfl⟩, φ, fun E hE => ?_⟩
  have hEW : E.genericPoint ∈ V.ι ''ᵁ W := (E.genericPoint_mem_iff _).2 hE
  obtain ⟨y, hyW, hy⟩ := hEW
  obtain ⟨E₀, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff V.ι E).2 ⟨y, hy⟩
  have hgp : V.ι E₀.genericPoint = V.ι y :=
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm.trans hy.symm
  have hE₀ : (E₀.support ∩ (W : Set V)).Nonempty := by
    rw [← PrimeDivisor.genericPoint_mem_iff]
    have : E₀.genericPoint = y := V.ι.isOpenEmbedding.injective hgp
    change E₀.genericPoint ∈ W
    rw [this]
    exact hyW
  have h1 := hφ' E₀ hE₀
  rw [DivisorWithCoeffs.coeff_restrictOpen] at h1
  rw [h1, hφg', hφ, MMP.Positivity.ord_functionFieldMap_of_isIso V.ι E₀ _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

end LocalCartier

/-- On a log canonical pair every coefficient of the boundary is at most one: the log
discrepancy of a prime divisor `P` is `1 - coeff_P`. -/
private theorem coeff_le_one_of_isLogCanonicalPair {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {B : QDivisor X} (hB : MMP.Intersection.IsLogCanonicalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P ≤ 1 := by
  obtain ⟨⟨hX, n, K, hK, hQ⟩, -, hlc⟩ := hB
  obtain ⟨m, hm, hmC⟩ := hQ.exists_pos
  obtain ⟨-, V, hV, τ, hτ⟩ :=
    MMP.Positivity.IsPair.exists_generatesOn ⟨hX, n, K, hK, hQ⟩ hK hmC P.genericPoint
  have hd : IsDiscrepancy sX n K B (DivisorOver.ofPrimeDivisor k hX P) (-B.coeff P) := by
    refine ⟨hX, hK, m, hm, hmC, V, hV, τ, hτ, ?_⟩
    rw [DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P τ]
    have hPV : (P.support ∩ (V : Set X)).Nonempty := by
      refine ⟨P.genericPoint, ?_, hV⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    linear_combination -hτ.2 P hPV
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hd
    (show IsProper (𝟙 X) from inferInstance))
  have h1 : ((B.coeff P : ℚ) : ℝ) ≤ 1 := by push_cast at h0; linarith
  exact_mod_cast h1

/-- For an open immersion `j : U ⟶ V` with image `W ≅ U`, the restriction to `W` of the extension
of a divisor `B` of `U` is the crepant boundary of `(U, B)` along the isomorphism `W ≅ U`. -/
private theorem isCrepantBoundary_restrictOpen_strictClosureDivisor {k : Type u} [Field k]
    [PerfectField k] {U V : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {sU : U ⟶ Spec (.of k)}
    (j : U ⟶ V) [IsOpenImmersion j] {n : ℕ} {K : Divisor U} {B : QDivisor U}
    (hP : IsPairWith sU n K B) (hW : IsNormalVariety k (j.isoOpensRange.inv ≫ sU)) :
    IsCrepantBoundary sU n K B j.isoOpensRange.inv hW (isBirationalMorphism_of_isIso _)
      ((strictClosureDivisor j B).restrictOpen j.opensRange) := by
  intro F
  set e := j.isoOpensRange
  set P : MMP.Mori.PrimeDivisor U := OpenWeilRestriction.primeDivisorMap e.inv F
  have hPg : P.genericPoint = e.inv F.genericPoint :=
    OpenWeilRestriction.genericPoint_primeDivisorMap _ _
  let D : DivisorOver k sU := ⟨_, e.inv, hW, isBirationalMorphism_of_isIso _, F⟩
  have hnex : ¬ D.IsExceptional := by
    rw [MMP.Mori.DivisorOver.isExceptional_iff_two_le_coheight hP.1 D]
    change ¬ 2 ≤ Order.coheight (e.inv F.genericPoint)
    rw [← hPg, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P]
    decide
  obtain ⟨Q, hQ, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP D hnex
  have hQP : Q = P := by
    refine MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset (Eq.subset ?_)
    rw [← hQ, DivisorOver.center_eq_closure_genericPoint,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact congrArg (fun x => closure {x}) hPg.symm
  have hjP : OpenWeilRestriction.primeDivisorMap j.opensRange.ι F =
      OpenWeilRestriction.primeDivisorMap j P := by
    refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
    rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
      OpenWeilRestriction.genericPoint_primeDivisorMap]
    change j.opensRange.ι F.genericPoint = j P.genericPoint
    have h2 : e.inv ≫ j = j.opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    rw [hPg, ← Scheme.Hom.comp_apply, h2]
  have hcoeff : ((strictClosureDivisor j B).restrictOpen j.opensRange).coeff F = B.coeff P := by
    rw [DivisorWithCoeffs.coeff_restrictOpen, hjP]
    exact strictClosureDivisor_apply j B P
  rw [hcoeff, ← hQP]
  exact hd

/-- **Transport of the lc bound along an isomorphism.** If `f : W ⟶ U` is an isomorphism and
`B_W` is the crepant boundary of the lc pair `(U, B)` on `W`, every discrepancy of a proper
divisor over `(W, B_W)` is at least `-1`. -/
private theorem neg_one_le_of_isCrepantBoundary {k : Type u} [Field k] [PerfectField k]
    {U W : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sU : U ⟶ Spec (.of k)} (f : W ⟶ U) [IsIso f]
    {sW : W ⟶ Spec (.of k)} (hfs : f ≫ sU = sW) {B : QDivisor U}
    (hlc : MMP.Intersection.IsLogCanonicalPair sU B) {n : ℕ} {KU : Divisor U}
    (hKU : KU.IsCanonicalDivisor sU n) {BW : QDivisor W} {KW : Divisor W}
    (hKW : KW.IsCanonicalDivisor sW n)
    (hcb : ∀ hW, IsCrepantBoundary sU n KU B f hW (isBirationalMorphism_of_isIso f) BW)
    (D : DivisorOver k sW) (hD : IsProper D.f) {c : ℚ}
    (hc : IsDiscrepancy sW n KW BW D c) : -1 ≤ c := by
  subst hfs
  have hW : IsNormalVariety k (f ≫ sU) := hc.1
  have hbir : IsBirationalMorphism f := isBirationalMorphism_of_isIso f
  obtain ⟨-, hiff⟩ := IsPair.isDiscrepancy_iff_of_crepant hlc.1 f hW hbir hKU hKW
    (Or.inl (hcb hW))
  have hEc : IsDiscrepancy sU n KU B (MMP.Mori.compDivisorOver f hW hbir D) c :=
    (hiff D _ (MMP.Mori.valuation_compDivisorOver f hW hbir D) c).mp hc
  have hEp : IsProper (MMP.Mori.compDivisorOver f hW hbir D).f := by
    change IsProper (D.f ≫ f)
    infer_instance
  have h0 := hlc.2.2 n _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hEc hEp)
  have : (-1 : ℝ) ≤ c := by linarith
  exact_mod_cast this

/-- **`ℚ`-Cartier divisors glue over a smooth complement.** A `ℚ`-divisor `D` on a normal variety
which is `ℚ`-Cartier on an open `W`, has integral coefficients along the prime divisors missing
`W`, and such that the complement of `W` lies in a smooth open `O`, is `ℚ`-Cartier. -/
private theorem isQCartier_of_isQCartier_restrictOpen {k : Type u} [Field k] {V : Scheme.{u}}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of k)}
    (D : QDivisor V) (W O : V.Opens) (hcov : ∀ v, v ∉ W → v ∈ O)
    (hO : IsSmoothScheme (O.ι ≫ sV))
    (hint : ∀ Q : MMP.Mori.PrimeDivisor V, Q.genericPoint ∉ W → ∃ z : ℤ, D.coeff Q = z)
    (hW : QDivisor.IsQCartier (D.restrictOpen W)) : D.IsQCartier := by
  obtain ⟨m, hm, C, hC, hCc⟩ := hW
  have hmint : ∀ Q : MMP.Mori.PrimeDivisor V, ∃ z : ℤ, DivisorWithCoeffs.coeff (m • D) Q = z := by
    intro Q
    by_cases hQ : Q.genericPoint ∈ W
    · obtain ⟨Q', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff W.ι Q).2
        (by rwa [Scheme.Opens.range_ι])
      refine ⟨C.coeff Q', ?_⟩
      have h := congrArg (fun F : QDivisor W => DivisorWithCoeffs.coeff F Q') hC
      simp only [Divisor.coeff_toQDivisor] at h
      rw [h]
      rfl
    · obtain ⟨z, hz⟩ := hint Q hQ
      refine ⟨m * z, ?_⟩
      change ((m : ℤ) • D) Q = _
      rw [Finsupp.smul_apply, zsmul_eq_mul]
      change (m : ℚ) * D.coeff Q = _
      rw [hz]
      push_cast
      ring
  let C' : Divisor V := DivisorWithCoeffs.roundDown (m • D)
  have hC' : Divisor.toQDivisor C' = m • D := by
    refine Finsupp.ext fun Q => ?_
    change (Divisor.toQDivisor C').coeff Q = DivisorWithCoeffs.coeff (m • D) Q
    obtain ⟨z, hz⟩ := hmint Q
    rw [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_roundDown, hz, Int.floor_intCast]
  refine ⟨m, hm, C', hC', fun v => ?_⟩
  by_cases hv : v ∈ W
  · have hCW : C'.restrictOpen W = C := by
      refine Divisor.toQDivisor_injective (Finsupp.ext fun Q' => ?_)
      change (Divisor.toQDivisor (C'.restrictOpen W)).coeff Q' =
        (Divisor.toQDivisor C).coeff Q'
      rw [hC, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_restrictOpen,
        ← Divisor.coeff_toQDivisor, hC']
      rfl
    have : Divisor.IsCartier (C'.restrictOpen W) := hCW ▸ hCc
    exact exists_isLocalEquation_of_isCartier_restrictOpen this hv
  · haveI : Nonempty O := ⟨⟨v, hcov v hv⟩⟩
    exact exists_isLocalEquation_of_isCartier_restrictOpen
      (MMP.Fourfold.isCartier_of_isSmoothScheme hO _) (hcov v hv)

/-- **The extension of an lc boundary over a smooth snc complement is lc.** Let `j : U ⟶ V` be an
open immersion of normal varieties over a perfect field, `(U, B)` an lc pair, and `O ⊆ V` an open
of the smooth locus containing the complement of `U`, on which the extension `B_V` of `B` has snc
support. Then `(V, B_V)` is lc. -/
private theorem isLogCanonicalPair_strictClosureDivisor {k : Type u} [Field k] [PerfectField k]
    {U V : Scheme.{u}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sU : U ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)} (hV : IsNormalVariety k sV)
    (j : U ⟶ V) [IsOpenImmersion j] (hjs : j ≫ sV = sU) {B : QDivisor U}
    (hB : MMP.Intersection.IsLogCanonicalPair sU B) (O : V.Opens)
    (hO : ∀ v, v ∉ Set.range j → v ∈ O) (hOsm : O ≤ smoothLocus sV)
    (hsnc : DivisorWithCoeffs.IsSNC (O.ι ≫ sV) ((strictClosureDivisor j B).restrictOpen O)) :
    MMP.Intersection.IsLogCanonicalPair sV (strictClosureDivisor j B) := by
  classical
  have hBU := hB
  obtain ⟨⟨hU, n, KU, hKU, hQU⟩, hBnn, -⟩ := hB
  set W : V.Opens := j.opensRange with hWdef
  set e : U ≅ W := j.isoOpensRange with hedef
  haveI : Nonempty W := ⟨⟨j (genericPoint U), ⟨_, rfl⟩⟩⟩
  haveI : IsDominant W.ι := isDominant_opens_ι W
  have hej : e.inv ≫ j = W.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hWs : e.inv ≫ sU = W.ι ≫ sV := by rw [← hjs, ← Category.assoc, hej]
  have hW : IsNormalVariety k (e.inv ≫ sU) := by rw [hWs]; exact isNormalVariety_restrictOpen hV W
  have hcb := isCrepantBoundary_restrictOpen_strictClosureDivisor j ⟨hU, hKU, hQU⟩ hW
  haveI : CompactSpace V := haveI := hV.1; QuasiCompact.compactSpace_of_compactSpace sV
  have hdimV : topologicalKrullDim V = n := by
    rw [← topologicalKrullDim_opens_eq hV W, ← hKU.1]
    exact IsHomeomorph.topologicalKrullDim_eq e.inv (Scheme.homeoOfIso e.symm).isHomeomorph
  obtain ⟨KV, hKV⟩ := exists_isCanonicalDivisor sV hV hdimV
  have hKW' := isCanonicalDivisor_restrictOpen hV hKV W
  have hKW : Divisor.IsCanonicalDivisor (e.inv ≫ sU) n (KV.restrictOpen W) := by
    rwa [hWs]
  obtain ⟨hPW, -⟩ := IsPair.isDiscrepancy_iff_of_crepant ⟨hU, n, KU, hKU, hQU⟩ e.inv hW
    (isBirationalMorphism_of_isIso _) hKU hKW (Or.inl hcb)
  have hQW : QDivisor.IsQCartier
      (DivisorWithCoeffs.restrictOpen W (Divisor.toQDivisor KV + strictClosureDivisor j B)) := by
    obtain ⟨-, n', K', hK', hQ'⟩ := hPW
    haveI : CompactSpace W := haveI := hW.1; QuasiCompact.compactSpace_of_compactSpace (e.inv ≫ sU)
    have hlin : K'.LinearlyEquivalent (KV.restrictOpen W) :=
      MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor (e.inv ≫ sU) hW hK' hKW
    have h := hQ'.add_of_linearlyEquivalent hlin
    convert h using 1
    exact Finsupp.ext fun _ => rfl
  have hint : ∀ Q : MMP.Mori.PrimeDivisor V, Q.genericPoint ∉ W →
      ∃ z : ℤ, (Divisor.toQDivisor KV + strictClosureDivisor j B).coeff Q = z := by
    intro Q hQ
    refine ⟨KV.coeff Q, ?_⟩
    change (Divisor.toQDivisor KV).coeff Q + (strictClosureDivisor j B) Q = _
    rw [strictClosureDivisor_apply_of_notMem j B Q (fun h => hQ (by simpa [hWdef] using h)),
      Divisor.coeff_toQDivisor, add_zero]
  have hQV : (Divisor.toQDivisor KV + strictClosureDivisor j B).IsQCartier :=
    isQCartier_of_isQCartier_restrictOpen _ W O
      (fun v hv => hO v (fun h => hv (by simpa [hWdef] using h)))
      (isSmoothScheme_ι_of_le_smoothLocus hOsm) hint hQW
  have hPV : IsPairWith sV n KV (strictClosureDivisor j B) := ⟨hV, hKV, hQV⟩
  have hcoeffV : ∀ Q : MMP.Mori.PrimeDivisor V,
      0 ≤ (strictClosureDivisor j B).coeff Q ∧ (strictClosureDivisor j B).coeff Q ≤ 1 := by
    intro Q
    by_cases hQ : Q.genericPoint ∈ Set.range j
    · obtain ⟨P, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff j Q).2 hQ
      change 0 ≤ strictClosureDivisor j B _ ∧ strictClosureDivisor j B _ ≤ 1
      rw [strictClosureDivisor_apply]
      exact ⟨hBnn P, coeff_le_one_of_isLogCanonicalPair hBU P⟩
    · change 0 ≤ strictClosureDivisor j B Q ∧ strictClosureDivisor j B Q ≤ 1
      rw [strictClosureDivisor_apply_of_notMem j B Q hQ]
      exact ⟨le_rfl, zero_le_one⟩
  refine ⟨⟨hV, n, KV, hKV, hQV⟩, fun Q => (hcoeffV Q).1, ?_⟩
  intro n' D a ha
  have hn' : n' = n := by
    have h := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
    rw [hdimV] at h
    exact_mod_cast h.symm
  subst hn'
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hPV.isPair hKV D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha]
  suffices h : (-1 : ℚ) ≤ c by
    have : (-1 : ℝ) ≤ c := by exact_mod_cast h
    linarith
  by_cases hDW : ((D.center : Set V) ∩ W).Nonempty
  · obtain ⟨hY, hf, E', -, -, hiff⟩ := DivisorOver.exists_restrict_isDiscrepancy_iff hPV D W hDW
    have hp : IsProper D.f := ha.2.1
    exact neg_one_le_of_isCrepantBoundary e.inv hWs hBU hKU hKW'
      (fun hW' => isCrepantBoundary_restrictOpen_strictClosureDivisor j ⟨hU, hKU, hQU⟩ hW')
      ⟨_, D.f ∣_ W, hY, hf, E'⟩ (show IsProper (D.f ∣_ W) from inferInstance) ((hiff c).mp hc)
  · have hDO : ((D.center : Set V) ∩ O).Nonempty := by
      refine ⟨D.f D.E.genericPoint, ?_, hO _ ?_⟩
      · rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure rfl
      · intro hmem
        refine hDW ⟨D.f D.E.genericPoint, ?_, ?_⟩
        · rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure rfl
        · simpa [hWdef] using hmem
    exact neg_one_le_of_isSNC_restrictOpen hPV (fun Q => (hcoeffV Q).2) hOsm hsnc hDO hc

end Extend

open MMP.Mori

/-- A nonempty open subscheme of a normal variety has the dimension of the variety. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {k : Type u} [Field k]
    {U Y : Scheme.{u}} [IsIntegral Y] [Nonempty U] {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) (j : U ⟶ Y) [IsOpenImmersion j] :
    topologicalKrullDim U = topologicalKrullDim Y := by
  haveI := hY.1
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsNormal Y := hY.2
  haveI : Nonempty j.opensRange := ⟨⟨j (Classical.arbitrary U), ⟨_, rfl⟩⟩⟩
  haveI : IsDominant j.opensRange.ι := Resolve.isDominant_opens_ι _
  rw [← Resolve.topologicalKrullDim_opens_eq hY j.opensRange]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso j.isoOpensRange).isHomeomorph

open Classical in
/-- The prime components of the restriction to `O` of the closure of `B` along `j'` lie over the
closures of the components of `B`. -/
private theorem mem_of_mem_support_restrictOpen {U Y Z : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (j' : U ⟶ Z) [IsOpenImmersion j'] (g : Z ⟶ Y) (hj : j' ≫ g = j)
    (B : QDivisor U) (O : Z.Opens) (F : MMP.Mori.PrimeDivisor O.toScheme)
    (hF : F ∈ ((Extend.strictClosureDivisor j' B).restrictOpen O).support) :
    g (O.ι (AlgebraicGeometry.PrimeDivisor.genericPoint F)) ∈
      ⋃ P ∈ B.support.image (OpenWeilRestriction.primeDivisorMap j), (P.support : Set Y) := by
  classical
  have hmem :
      OpenWeilRestriction.primeDivisorMap O.ι F ∈ (Extend.strictClosureDivisor j' B).support :=
    Finsupp.mem_support_iff.mpr (Finsupp.mem_support_iff.mp hF :)
  obtain ⟨P, hP, hPF⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  have hgen : O.ι (AlgebraicGeometry.PrimeDivisor.genericPoint F) =
      j' (AlgebraicGeometry.PrimeDivisor.genericPoint P) := by
    rw [← OpenWeilRestriction.genericPoint_primeDivisorMap, ← hPF,
      OpenWeilRestriction.genericPoint_primeDivisorMap]
  refine Set.mem_iUnion₂.mpr ⟨_, Finset.mem_image_of_mem _ hP, ?_⟩
  rw [hgen, ← Scheme.Hom.comp_apply, hj, ← OpenWeilRestriction.genericPoint_primeDivisorMap]
  exact MMP.Spreading.genericPoint_mem_support _

/-- **Affine lc surface pairs have lc projective completions.** Let `(U, B_U)` be a log canonical
pair with `B_U` a `ℚ`-divisor on an affine normal complex surface `U`. Then there are a normal
projective complex surface `V`, an open immersion `j : U ⟶ V` over `ℂ`, and a `ℚ`-divisor `B_V`
on `V` such that `(V, B_V)` is log canonical and the restriction of `B_V` to `U` along `j` is
`B_U`. -/
@[mmp "lem_mmp_surface_affine_lc_projective_completion"]
public theorem exists_isOpenImmersion_isLogCanonicalPair_of_isAffine
    {U : Scheme.{0}} [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [IsAffine U]
    (sU : U ⟶ Spec (.of ℂ)) (hdim : topologicalKrullDim U = 2) {B_U : QDivisor U}
    (hB : MMP.Intersection.IsLogCanonicalPair sU B_U) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (sV : V ⟶ Spec (.of ℂ)) (j : U ⟶ V) (B_V : QDivisor V),
      IsOpenImmersion j ∧ j ≫ sV = sU ∧ MMP.Mori.IsProjectiveVariety ℂ sV ∧
      topologicalKrullDim V = 2 ∧ MMP.Intersection.IsLogCanonicalPair sV B_V ∧
      MMP.Mori.inverseTransformDivisor j B_V = B_U := by
  classical
  have hUv : IsNormalVariety ℂ sU := hB.1.1
  haveI : AlgebraicGeometry.IsVariety ℂ sU := hUv.1
  haveI : Nonempty U := ⟨genericPoint U⟩
  -- a normal projective compactification
  obtain ⟨X, hXi, hXn, sX, ι, hι, hιs, hXp⟩ := Compactify.exists_compactification sU
  haveI := hι
  have hdimX : topologicalKrullDim X = 2 :=
    (topologicalKrullDim_eq_of_isOpenImmersion ⟨hXp.toIsVariety, hXn⟩ ι).symm.trans hdim
  -- resolving the singular points outside `U`
  obtain ⟨Y, hYi, hYn, g, j, hj, hjg, hYp, hreg⟩ := Resolve.exists_regular_outside sX hXp hdimX ι
  haveI := hj
  have hdimY : topologicalKrullDim Y = 2 :=
    (topologicalKrullDim_eq_of_isOpenImmersion ⟨hYp.toIsVariety, hYn⟩ j).symm.trans hdim
  -- making the closure of the boundary snc outside `U`
  obtain ⟨Z, hZi, hZn, g', j', O, hj', hj'g, hZp, hcov, hsm, hsnc⟩ :=
    Resolve.exists_snc_outside (g ≫ sX) hYp hdimY j hreg
      (B_U.support.image (OpenWeilRestriction.primeDivisorMap j))
  haveI := hj'
  haveI : AlgebraicGeometry.IsVariety ℂ (g' ≫ g ≫ sX) := hZp.toIsVariety
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (g' ≫ g ≫ sX)
  have hZnv : IsNormalVariety ℂ (g' ≫ g ≫ sX) := ⟨hZp.toIsVariety, hZn⟩
  have hjs : j' ≫ g' ≫ g ≫ sX = sU := by
    rw [← Category.assoc, hj'g, ← Category.assoc, hjg, hιs]
  refine ⟨Z, hZi, inferInstance, hZn, g' ≫ g ≫ sX, j', Extend.strictClosureDivisor j' B_U, hj',
    hjs, hZp,
    (topologicalKrullDim_eq_of_isOpenImmersion hZnv j').symm.trans hdim,
    Extend.isLogCanonicalPair_strictClosureDivisor hZnv j' hjs hB O hcov hsm
      (hsnc _ fun F hF => mem_of_mem_support_restrictOpen j j' g' hj'g B_U O F hF),
    Extend.inverseTransformDivisor_strictClosureDivisor j' B_U⟩

end MMP.Threefold
