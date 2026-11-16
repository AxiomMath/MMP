module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Surface.CrepantDltModification
import MMP.AlgebraicGeometry.MMP.Surface.LcNefBigSemiample
import MMP.AlgebraicGeometry.MMP.Abundance.SdltCommonBaseTwist
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.PushforwardComparison
import MMP.AlgebraicGeometry.Morphisms.GenericallyFinite
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
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
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.DeformationSpace
import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeSections
import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle
import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimLocal
import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.WhitneyChowCohomology
import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersectionFormula
import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedExcessIntersectionFormula
import StacksFrontier.AlgebraicGeometry.Chow.DeformationGysinIdentity
import StacksFrontier.AlgebraicGeometry.Chow.BlowupExceptionalBundle
import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.SpecializationProperPushforward
import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimConormalRank
import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleMapClosedImmersionOfSurjection
import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.ChowSteps
import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafSpelling
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisor
import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.Morphism
import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients
import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleIrreducible
import StacksFrontier.CategoryTheory.Sites.IsIsoOfBijectiveOnCoveringObjects
import StacksFrontier.AlgebraicGeometry.Chow.SmoothComponentMultiplicity
import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveLineIdealOfEquations
import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.GradedRealizationPullbackIso
import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.ArbitraryModule
import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.RelativeSpecTransport
import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.ImageIdealPullback
import StacksFrontier.RingTheory.GradedAlgebra.Proj.HomogeneousPrimes
import StacksFrontier.AlgebraicGeometry.Picard.FamilyFittingIdeal
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerSheafifyNaturality
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.EpiIso
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.NoetherianRegularKoszul
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothTargetPermanence
import StacksFrontier.AlgebraicGeometry.RegularImmersion.StalkDimension
import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreExceptionalCompletionCone
import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSectionGysin
import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionCartier
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.PresentationTwistIso
import StacksFrontier.AlgebraicGeometry.NodalContraction.SmoothAt
import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdealChart
import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorizationGlue
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.TwistTrivial
import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineHom
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyNoetherianRegular
import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.HomogeneousIdealSheaf
import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BlowupExcessConormal
import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.AcyclicCycles
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.RingTheory.GradedAlgebra.KrullDimension
import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.AffineCone
import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.StalkKoszulCriterion
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearMapExactness
import StacksFrontier.AlgebraicGeometry.Cube.GeometricallyIntegralProduct
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumTwistComparison
import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationProperProjective
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSection
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyQuasiAffineHom
import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleAbelianVanishing
import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.QuasiSeparated
import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectTensorLocalModels
import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwoStandardClasses
import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroupImageKernel
import StacksFrontier.AlgebraicGeometry.Modules.PushforwardUnitHomEquiv
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementAffineSpace
import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartAssembly
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.SectionsClause
import StacksFrontier.AlgebraicGeometry.HigherDirectImageBaseChange.Basic
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforward
import StacksFrontier.AlgebraicGeometry.FlagTower.Grassmannian
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupEtaleChartTransfer
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDivisor
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.Modules.MonoRestrictLocality
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionStalk
import StacksFrontier.Topology.Dimension.UnionDimension
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.LinearEquations.ChartKernel
import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso
import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtRestrictExtension
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity

/-!
# Complemented nef lc surface adjoints are relatively semiample

Let `(S, B)` be a log canonical pair with rational boundary on a normal projective complex
surface `S`, with canonical divisor `K`, and let `f : S ⟶ Z` be a morphism to a projective
variety such that `D = K + B` is `f`-nef. If `A ≥ 0` is a `ℚ`-Cartier divisor with
`D + A ∼_ℚ f^*H` for a rational Cartier divisor `H` on `Z`, then `D` is `f`-semiample. No
condition on the position of `A` is needed.

If the image of `f` has dimension at most one, pass to a crepant dlt modification `q : S' ⟶ S`,
which is `ℚ`-factorial: the hypotheses pull back, `q^*D` is semiample over `Z` there
(`MMP.Fourfold.exists_isRelativelyFreeDivisor_of_add_qLinearlyEquivalent`), and semiampleness
descends along the birational `q` (`MMP.Fourfold.exists_isRelativelyFreeDivisor_of_pullback`).
If the image has dimension two, `f` is generically finite onto its scheme-theoretic image `Z'`,
every divisor is big over `Z'`, and the lc nef-big theorem for surfaces
(`MMP.Fourfold.QDivisor.isRelativelySemiample_of_isLcPair_of_isRelativelyNef_of_isRelativelyBig`)
makes `D` semiample over `Z'`, hence over `Z`, since `Z' ⟶ Z` is a closed immersion.

## Main results

* `MMP.Threefold.exists_isRelativelyFreeDivisor_of_isLogCanonicalPair_of_add_qLinearlyEquivalent`:
  the statement above.

## Implementation notes

* As in `MMP.Fourfold.exists_isRelativelyFreeDivisor_of_isDltPair_of_add_qLinearlyEquivalent`,
  "`D + A ∼_ℚ f^*H` for a rational Cartier divisor `H` on `Z`" is `D + A ∼_ℚ G`
  (`MMP.Mori.QDivisor.QLinearlyEquivalent`) for a `ℚ`-divisor `G` on `S` with `𝒪_S(mG) ≅ f^* M`
  for some `m > 0` and an invertible `𝒪_Z`-module `M` (`M = 𝒪_Z(mH)`); `f` need not be dominant.
* "`D` is `f`-semiample" is: some positive multiple `m D` is a Cartier divisor `L` with
  `f^* f_* 𝒪_S(L) → 𝒪_S(L)` surjective (`MMP.Fourfold.IsRelativelyFreeDivisor`).
* The canonical divisor `K` is any canonical divisor of `S` (`MMP.Mori.Divisor.IsCanonicalDivisor`
  in dimension `2`, which also records that `S` is a surface).

* The source passes to the Stein factorization `S ⟶ T ⟶ Z`; over a two-dimensional image we use
  instead the scheme-theoretic image of `f`, through which relative generation over `Z` is read
  off directly, and the bigness of every divisor over a generically finite base is computed at
  the generic point of the image, where the push-forward of a line bundle has a non-zero stalk.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Stacks.AlgebraicGeometry.Normalization

namespace MMP.Threefold

open MMP.Mori MMP.Fourfold

/- ### Log canonical pairs in the sense of Kollár–Mori -/

section LogCanonical

universe u

/-- **Nagata compactification**: a separated morphism of finite type `f : Y ⟶ Z` to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion followed by a
proper morphism. -/
private theorem exists_isOpenImmersion_isProper_comp_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ (P : Scheme.{u}) (j : Y ⟶ P) (p : P ⟶ Z), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsProper p ∧ j ≫ p = f := by
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
  exact ⟨c.space, c.immersion, c.toBase, inferInstance, hc, inferInstance, Over.w c.obj.hom⟩

/-- The normalization of `P` in a normal locally Noetherian scheme `Y`, along a quasi-compact
open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal and finite
over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {k : Type u} [Field k]
    {Y P : Scheme.{u}} {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P)
    [IsOpenImmersion j] [QuasiCompact j] [QuasiSeparated j] [IsNormal Y] [IsLocallyNoetherian Y] :
    IsOpenImmersion (Scheme.Hom.toNormalization j) ∧
      IsNormal (Scheme.Hom.normalization j) ∧ IsFinite (Scheme.Hom.fromNormalization j) := by
  refine ⟨?_, AlgebraicGeometry.isNormal_normalization j fun V hV => ?_,
    isFinite_fromNormalization_of_locallyOfFiniteType j
    (isNagataScheme_of_locallyOfFiniteType_over_field k sP)⟩
  · have : IsOpenImmersion ((Limits.pullback.snd j j).toNormalization ≫ j.normalizationPullback j ≫
        Limits.pullback.fst _ _) := inferInstance
    rw [Scheme.Hom.toNormalization_normalizationPullback_fst j j] at this
    exact (MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion
      (Limits.pullback.fst j j) _).mp this
  · have : IsNoetherian V :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := isCompact_iff_compactSpace.mp hV }
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/-- If `t ≫ g` is birational and `t` is an open immersion of integral schemes, `g` is
birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion_comp {Y P Z : Scheme.{u}} [IsIntegral Y]
    [IsIntegral P] [IsIntegral Z] (t : Y ⟶ P) [IsOpenImmersion t] (g : P ⟶ Z)
    (h : IsBirationalMorphism (t ≫ g)) : IsBirationalMorphism g := by
  obtain ⟨W, ⟨w, hw⟩, hWo⟩ := h.exists_isOpenImmersion
  let U : P.Opens := t ''ᵁ W
  let V : Z.Opens := (W.ι ≫ t ≫ g).opensRange
  have hUV : U ≤ g ⁻¹ᵁ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hU : U.ι ≫ g = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [← Scheme.Hom.isoImage_inv_ι_assoc]
  have hc : g.resLE V U hUV ≫ V.ι = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [Scheme.Hom.resLE_comp_ι, hU]
  have : IsOpenImmersion (g.resLE V U hUV ≫ V.ι) := by
    rw [hc]
    infer_instance
  have : IsOpenImmersion (g.resLE V U hUV) := IsOpenImmersion.of_comp _ V.ι
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V ?_ ?_ hUV ?_
  · exact ⟨t w, w, hw, rfl⟩
  · exact ⟨_, ⟨w, hw⟩, rfl⟩
  · rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
    obtain ⟨w, rfl⟩ := hz
    refine ⟨(t.isoImage W).hom w, ?_⟩
    apply V.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
    rfl

/-- **Kollár–Mori 2.22 for the identity model.** Every divisor `(Y, f, E)` over a normal variety
`X` has the valuation of a divisor over `X` whose morphism is proper: compactify `f` by Nagata's
theorem, `Y ⊆ P → X`, and replace `P` by the normalization of `P` in `Y`. -/
private theorem exists_isProper_valuation_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    ∃ E : DivisorOver k sX, IsProper E.f ∧ E.valuation = D.valuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have hYv := D.isNormalVariety.1
  have hXv := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsSeparated sX := hXv.toIsSeparated
  have : IsSeparated (D.f ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (D.f ≫ sX) := hYv.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : QuasiCompact (D.f ≫ sX) := hYv.toQuasiCompact
  have : IsSeparated D.f := IsSeparated.of_comp D.f sX
  have : LocallyOfFiniteType D.f := locallyOfFiniteType_of_comp D.f sX
  have : QuasiCompact D.f := QuasiCompact.of_comp D.f sX
  have : IsNoetherian X := {}
  have : QuasiSeparatedSpace X := inferInstance
  obtain ⟨P, j, p, hj, hjq, hp, hjp⟩ := exists_isOpenImmersion_isProper_comp_eq D.f
  have : IsSeparated j := by
    have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
    exact IsSeparated.of_comp j p
  have : LocallyOfFiniteType (p ≫ sX) := inferInstance
  have : QuasiSeparated j := IsSeparated.instQuasiSeparated j
  obtain ⟨ht, hnorm, hfin⟩ :=
    isOpenImmersion_toNormalization_and_isNormal_and_isFinite (sP := p ≫ sX) j
  set t := j.toNormalization
  let g := j.fromNormalization ≫ p
  have htg : t ≫ g = D.f := by
    simp only [g, t, Scheme.Hom.toNormalization_fromNormalization_assoc, hjp]
  have hgv : IsNormalVariety k (g ≫ sX) :=
    ⟨(isVariety_iff k _).2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hnorm⟩
  have hgb : IsBirationalMorphism g :=
    isBirationalMorphism_of_isOpenImmersion_comp t g (htg ▸ D.isBirationalMorphism)
  let D' : DivisorOver k sX :=
    ⟨_, g, hgv, hgb, OpenWeilRestriction.primeDivisorMap t D.E⟩
  refine ⟨D', (inferInstance : IsProper g), (MMP.Positivity.DivisorOver.valuation_eq_of_iso D D' ⊤
    t.opensRange trivial ⟨D.E.genericPoint, ?_⟩ (D.Y.topIso ≪≫ t.isoOpensRange) ?_ ?_).symm⟩
  · exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm
  · simp [D', htg]
  · apply Subtype.ext
    change (D.Y.topIso.hom ≫ t.isoOpensRange.hom ≫ t.opensRange.ι) ⟨D.E.genericPoint, trivial⟩ = _
    rw [Scheme.Hom.isoOpensRange_hom_ι]
    exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}

/-- **Log canonical pairs are Kollár–Mori lc**, for every canonical divisor: every discrepancy
`a(E, X, B)` of an exceptional divisor over `X` is the log discrepancy, minus one, of a divisor
with proper morphism and the same valuation, hence is `≥ -1`. -/
private theorem isLcPair_of_isLogCanonicalPair {B : QDivisor X}
    (hB : MMP.Intersection.IsLogCanonicalPair sX B) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) : IsLcPair sX n K B := by
  obtain ⟨⟨hX, n', K', hK', hQ'⟩, -, hlc⟩ := hB
  haveI : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  have hlin : K'.LinearlyEquivalent K :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK
  have hP : IsPairWith sX n K B := ⟨hX, hK, hQ'.add_of_linearlyEquivalent hlin⟩
  refine ⟨hP, le_discrep_iff.mpr fun D a hD ha => ?_⟩
  obtain ⟨E, hEp, hEv⟩ := exists_isProper_valuation_eq hX D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK E
  have haa : a' = a := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hEv ha' ha
  have h0 := hlc n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' hEp)
  have : (-1 : ℝ) ≤ a := by
    rw [← haa]
    linarith
  simpa using EReal.coe_le_coe_iff.mpr this

end LogCanonical

/- ### Relative semiampleness gives a relatively free Cartier multiple -/

section Semiample

open MMP.Intersection

/-- **A relatively semiample `ℚ`-divisor has a relatively free Cartier multiple.** -/
private theorem exists_isRelativelyFreeDivisor_of_isRelativelySemiample {X Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Z)
    {D : QDivisor X} (hD : QDivisor.IsRelativelySemiample f D) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor X, Divisor.toQDivisor L = (m : ℤ) • D ∧ L.IsCartier ∧
      IsRelativelyFreeDivisor f L := by
  classical
  haveI : IsNoetherian X := ⟨⟩
  obtain ⟨C, hC, q, hq, hint, hfree⟩ := hD
  obtain ⟨B, hEB⟩ := MMP.Intersection.exists_isWeilDivisorOfCartier
    (KCartierDivisor.realization ((q : ℚ) • C) hint)
  have hBq : Divisor.toQDivisor B = ((q : ℤ)) • D := by
    ext P
    rw [Divisor.coeff_toQDivisor, MMP.Fourfold.coeff_eq_mul_of_isWeilDivisorOfCartier_realization
      hC hint hEB P]
    simp [DivisorWithCoeffs.coeff_apply, zsmul_eq_mul]
  exact ⟨q, hq, B, hBq, hEB.isCartier,
    MMP.Fourfold.epi_counit_of_iso f hEB.sheafIsoDivisorialSheaf.symm hfree⟩

end Semiample

/- ### Pull-backs of `ℚ`-Cartier `ℚ`-divisors along a dominant morphism -/

section Pullback

variable {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (q : X ⟶ Y) [IsDominant q]

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor along a dominant morphism. -/
private noncomputable abbrev qpb (B : QDivisor Y) (hB : B.IsQCartier) : QDivisor X :=
  B.pullback hB (map_componentGenericPoint_notMem_supp_of_isQCartier q hB)

/-- `n • q^*B` is the pull-back of a Cartier divisor `N = n • B`. -/
private theorem toQDivisor_pullback_eq_smul_qpb {B : QDivisor Y} (hBq : B.IsQCartier) {n : ℕ}
    (hn : 0 < n) {N : Divisor Y} (hN : Divisor.toQDivisor N = (n : ℤ) • B) (hNc : N.IsCartier) :
    Divisor.toQDivisor (N.pullback hNc (map_componentGenericPoint_notMem_supp_of_isDominant q N)) =
      (n : ℤ) • qpb q B hBq := by
  obtain ⟨N', hN', hp⟩ := QDivisor.isPullback_pullback hBq
    (map_componentGenericPoint_notMem_supp_of_isQCartier q hBq) n hn N hN hNc
  rw [← hN', Divisor.IsPullback.pullback_eq hNc hp]

/-- If `D₁ = a B₁` and `D₂ = b B₂`, then `c₁ b D₁ + c₂ a D₂ = ab (c₁ B₁ + c₂ B₂)`. -/
private theorem toQDivisor_add_smul_eq {B₁ B₂ : QDivisor Y} {a b : ℕ} {D₁ D₂ : Divisor Y}
    (hD₁ : Divisor.toQDivisor D₁ = (a : ℤ) • B₁) (hD₂ : Divisor.toQDivisor D₂ = (b : ℤ) • B₂)
    (c₁ c₂ : ℤ) :
    Divisor.toQDivisor ((c₁ * b) • D₁ + (c₂ * a) • D₂) =
      ((a * b : ℕ) : ℤ) • (c₁ • B₁ + c₂ • B₂) := by
  rw [map_add, map_zsmul, map_zsmul, hD₁, hD₂, smul_add, smul_smul, smul_smul, smul_smul,
    smul_smul]
  push_cast
  congr 2 <;> ring

/-- An integral linear combination of `ℚ`-Cartier `ℚ`-divisors is `ℚ`-Cartier. -/
private theorem isQCartier_zsmul_add_zsmul {B₁ B₂ : QDivisor Y} (h₁ : B₁.IsQCartier) (h₂ : B₂.IsQCartier)
    (c₁ c₂ : ℤ) : (c₁ • B₁ + c₂ • B₂).IsQCartier := by
  obtain ⟨a, ha, D₁, hD₁, hD₁c⟩ := h₁.exists_pos
  obtain ⟨b, hb, D₂, hD₂, hD₂c⟩ := h₂.exists_pos
  exact ⟨(a * b : ℕ), by positivity, _, toQDivisor_add_smul_eq hD₁ hD₂ c₁ c₂,
    (hD₁c.zsmul _).add (hD₂c.zsmul _)⟩

/-- **Linearity of the pull-back.** `q^*(c₁ B₁ + c₂ B₂) = c₁ q^*B₁ + c₂ q^*B₂`. -/
private theorem qpb_zsmul_add_zsmul {B₁ B₂ : QDivisor Y} (h₁ : B₁.IsQCartier)
    (h₂ : B₂.IsQCartier) (c₁ c₂ : ℤ) (h : (c₁ • B₁ + c₂ • B₂).IsQCartier) :
    qpb q (c₁ • B₁ + c₂ • B₂) h = c₁ • qpb q B₁ h₁ + c₂ • qpb q B₂ h₂ := by
  obtain ⟨a, ha, D₁, hD₁, hD₁c⟩ := h₁.exists_pos
  obtain ⟨b, hb, D₂, hD₂, hD₂c⟩ := h₂.exists_pos
  set N := (c₁ * b) • D₁ + (c₂ * a) • D₂ with hNdef
  have hNc : N.IsCartier := (hD₁c.zsmul _).add (hD₂c.zsmul _)
  have e1 := toQDivisor_pullback_eq_smul_qpb q h (by positivity)
    (toQDivisor_add_smul_eq hD₁ hD₂ c₁ c₂) hNc
  have e2 := toQDivisor_pullback_eq_smul_qpb q h₁ ha hD₁ hD₁c
  have e3 := toQDivisor_pullback_eq_smul_qpb q h₂ hb hD₂ hD₂c
  have hp : N.IsPullback q (map_componentGenericPoint_notMem_supp_of_isDominant q N)
      ((c₁ * b) • D₁.pullback hD₁c (map_componentGenericPoint_notMem_supp_of_isDominant q D₁) +
        (c₂ * a) • D₂.pullback hD₂c (map_componentGenericPoint_notMem_supp_of_isDominant q D₂)) :=
    ((Divisor.isPullback_pullback hD₁c _).zsmul hD₁c _
      (map_componentGenericPoint_notMem_supp_of_isDominant q _)).add (hD₁c.zsmul _)
      (hD₂c.zsmul _) _ ((Divisor.isPullback_pullback hD₂c _).zsmul hD₂c _
        (map_componentGenericPoint_notMem_supp_of_isDominant q _))
  rw [Divisor.IsPullback.pullback_eq hNc hp, map_add, map_zsmul, map_zsmul, e2, e3] at e1
  apply smul_right_injective (QDivisor X) (by positivity : ((a * b : ℕ) : ℤ) ≠ 0)
  change _ • _ = _ • _
  rw [← e1, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  push_cast
  congr 2 <;> ring

/-- The pull-back of a Cartier divisor, as a `ℚ`-divisor. -/
private theorem qpb_toQDivisor {N : Divisor Y} (hNc : N.IsCartier)
    (h : (Divisor.toQDivisor N).IsQCartier) :
    qpb q (Divisor.toQDivisor N) h =
      Divisor.toQDivisor
        (N.pullback hNc (map_componentGenericPoint_notMem_supp_of_isDominant q N)) := by
  rw [toQDivisor_pullback_eq_smul_qpb q h one_pos (by simp) hNc]
  simp

/-- **`ℚ`-linear equivalence pulls back.** -/
private theorem qpb_qLinearlyEquivalent {B₁ B₂ : QDivisor Y} (h₁ : B₁.IsQCartier)
    (h₂ : B₂.IsQCartier) (h : B₁.QLinearlyEquivalent B₂) :
    (qpb q B₁ h₁).QLinearlyEquivalent (qpb q B₂ h₂) := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  have e : (m : ℤ) • B₁ + (-(m : ℤ)) • B₂ = Divisor.toQDivisor (principalDivisor φ) := by
    rw [← hφ, smul_sub, neg_smul, sub_eq_add_neg]
  have hc := isQCartier_zsmul_add_zsmul h₁ h₂ (m : ℤ) (-(m : ℤ))
  have hpc := Divisor.isCartier_principalDivisor φ
  have key := qpb_zsmul_add_zsmul q h₁ h₂ (m : ℤ) (-(m : ℤ)) hc
  have h3 : qpb q _ hc = qpb q _ (e ▸ hc) := by congr 1
  rw [h3, qpb_toQDivisor q hpc,
    Divisor.IsPullback.pullback_eq hpc (Divisor.isPullback_principalDivisor φ _)] at key
  exact ⟨m, hm, _, by rw [smul_sub, key, neg_smul, sub_eq_add_neg]⟩

/-- **Effectivity pulls back.** -/
private theorem qpb_nonneg {B : QDivisor Y} (hBq : B.IsQCartier) (hB : 0 ≤ B) :
    0 ≤ qpb q B hBq := by
  obtain ⟨n, hn, N, hN, hNc⟩ := hBq.exists_pos
  have e := toQDivisor_pullback_eq_smul_qpb q hBq hn hN hNc
  have hNnn : ∀ P, 0 ≤ N.coeff P := fun P => by
    have h1 := congrArg (fun D : QDivisor Y => D.coeff P) hN
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
    have : (0 : ℚ) ≤ N.coeff P := by
      rw [h1]
      exact mul_nonneg (by positivity) (hB P)
    exact_mod_cast this
  intro E
  have h2 := coeff_nonneg_of_isPullback_of_isEffectiveOn hNc (V := ⊤) (fun P _ => hNnn P)
    (Divisor.isPullback_pullback hNc (map_componentGenericPoint_notMem_supp_of_isDominant q N)) E
    ((E.genericPoint_mem_iff _).mp trivial)
  have h1 := congrArg (fun D : QDivisor X => D.coeff E) e
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h1
  have h3 : (0 : ℚ) ≤ (n : ℚ) * (qpb q B hBq).coeff E := by
    push_cast at h1
    rw [← h1]
    exact_mod_cast h2
  exact (mul_nonneg_iff_of_pos_left (by positivity)).mp h3

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private theorem qpb_isQCartier {B : QDivisor Y} (hBq : B.IsQCartier) :
    (qpb q B hBq).IsQCartier := by
  obtain ⟨n, hn, N, hN, hNc⟩ := hBq.exists_pos
  exact ⟨n, by exact_mod_cast hn.ne', _, toQDivisor_pullback_eq_smul_qpb q hBq hn hN hNc,
    hNc.isCartier_pullback q _⟩

end Pullback

/- ### Relative nefness pulls back -/

section Nef

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type} [Field k] {Y Y' : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_left (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type} [Field k] {Y Y' : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_right hc, map_zero]

/-- **Relative nefness pulls back**: if `B` is `f`-nef, then `q^*B` is `(q ≫ f)`-nef, by the
projection formula. -/
private theorem qpb_isRelativelyNef {k : Type} [Field k] {Y Y' Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsNormal Y'] (q : Y' ⟶ Y) [IsProper q] [IsDominant q] [QuasiCompact (q ≫ sY)]
    [CompactSpace Y] [CompactSpace Y'] (f : Y ⟶ Z) {B : QDivisor Y} (hBq : B.IsQCartier)
    (hnef : B.IsRelativelyNef sY f) :
    (qpb q B hBq).IsRelativelyNef (q ≫ sY) (q ≫ f) := by
  refine QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (q ≫ sY) (qpb_isQCartier q hBq)
    fun γ hγ => ?_
  obtain ⟨n, hn, N, hN, hNc⟩ := hBq.exists_pos
  have e := toQDivisor_pullback_eq_smul_qpb q hBq hn hN hNc
  rw [QDivisor.intersectionNumber_eq_of_smul k (q ≫ sY) γ.ι γ.dim_le _ _ hn _
    (hNc.isCartier_pullback q _) e]
  refine div_nonneg ?_ (by positivity)
  by_cases hc : IsProperCurve sY (q γ.point)
  · obtain ⟨C, hCp⟩ : ∃ C : ProperCurve sY, C.point = q γ.point := ⟨⟨_, hc⟩, rfl⟩
    have hCf : C.IsContractedBy f := by
      intro y hy
      rw [hCp] at hy ⊢
      have hsub : closure ({q γ.point} : Set Y) ⊆ q '' closure ({γ.point} : Set Y') :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨γ.point, subset_closure rfl, rfl⟩)
          (q.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hγ z hz
    rw [degreeOn_pullback_eq_mul q hNc _ γ C hCp]
    have h1 := QDivisor.IsRelativelyNef.intersectionNumber_nonneg sY hnef hBq C hCf
    rw [QDivisor.intersectionNumber_eq_of_smul k sY C.ι C.dim_le _ _ hn _ hNc hN] at h1
    have h2 : (0 : ℚ) ≤ N.degreeOn k sY C.ι C.dim_le hNc :=
      ((div_nonneg_iff.mp h1).resolve_right fun h => h.2.not_gt (by exact_mod_cast hn)).1
    push_cast
    exact mul_nonneg (by positivity) h2
  · rw [degreeOn_pullback_eq_zero q hNc _ γ hc]
    simp

end Nef

/- ### Bigness over a generically finite base -/

section Big

/-- **The push-forward of a line bundle along a generically finite morphism has positive rank
at the generic point.** Let `g : X ⟶ W` be proper and dominant, with the generic point of `X`
the only point over the generic point `η` of `W`. For a Cartier divisor `E` on `X`, a local
equation `ψ` of `E` near the generic point of `X` is a local equation on `g⁻¹ U` for a
neighbourhood `U` of `η`, so `ψ⁻¹` is a section of `g_* 𝒪_X(E)` over `U` whose germ at `η` is
non-zero; the stalk there is a finite `K(W)`-vector space, `g_* 𝒪_X(E)` being coherent. -/
private theorem one_le_relativeGenericRank {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    (g : X ⟶ W) [IsProper g] [IsDominant g]
    (hfib : ∀ x : X, g x = genericPoint W → x = genericPoint X) {E : Divisor X}
    (hE : E.IsCartier) : 1 ≤ relativeGenericRank g E.divisorialSheaf := by
  classical
  have := hE.isInvertibleModule_divisorialSheaf
  haveI : E.divisorialSheaf.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
  set F := (Scheme.Modules.pushforward g).obj E.divisorialSheaf with hF
  haveI : F.IsCoherent := ProperCoherenceWitness.isCoherent_pushforward g _
  haveI : F.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  have hη : g (genericPoint X) = genericPoint W := map_genericPoint_of_isDominant g
  unfold relativeGenericRank
  rw [← hF, hη, Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk]
  obtain ⟨V, hξV, ψ, hψ⟩ := hE (genericPoint X)
  have hcl : IsClosed (g '' (V : Set X)ᶜ) := g.isClosedMap _ V.isOpen.isClosed_compl
  let U : W.Opens := ⟨(g '' (V : Set X)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hηU : genericPoint W ∈ U := fun ⟨x, hx, hgx⟩ => hx (hfib x hgx ▸ hξV)
  have hUV : g ⁻¹ᵁ U ≤ V := fun x hx => Classical.byContradiction fun h => hx ⟨x, h, rfl⟩
  let s : Γ(E.divisorialSheaf, g ⁻¹ᵁ U) := divisorialSectionOfUnit ψ⁻¹ fun P hP => by
    rw [PrimeDivisor.ord_inv, hψ P (hP.mono (Set.inter_subset_inter_right _ hUV))]
    simp
  let s' : ToType (F.presheaf.obj (Opposite.op U)) := s
  have hne : (F.presheaf.germ U (genericPoint W) hηU).hom s' ≠ 0 := by
    intro h0
    rw [← map_zero (F.presheaf.germ U (genericPoint W) hηU).hom] at h0
    obtain ⟨W', hW', iU, iV, heq⟩ := TopCat.Presheaf.germ_eq F.presheaf _ hηU hηU s' 0 h0
    rw [map_zero] at heq
    have hZ : componentGenericPoint X (pointComponent (genericPoint X)) ∈ g ⁻¹ᵁ W' := by
      rw [componentGenericPoint_eq_genericPoint]
      change g _ ∈ W'
      rwa [hη]
    have h1 := congrFun (congrArg Subtype.val heq) ⟨_, hZ⟩
    change ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
      (pointComponent (genericPoint X)) = 0 at h1
    have hu : IsUnit ((ψ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) := Units.isUnit _
    exact (hu.map (Pi.evalRingHom _ (pointComponent (genericPoint X)))).ne_zero h1
  haveI := Scheme.Modules.finite_stalk_of_isCoherent F (genericPoint W)
  haveI := Scheme.Modules.free_stalk_genericPoint F
  haveI : Nontrivial (F.presheaf.stalk (genericPoint W)) := ⟨⟨_, 0, hne⟩⟩
  exact (Module.finrank_pos_iff_of_free _ _).mpr inferInstance

/-- **Every `ℚ`-Cartier divisor is big over a generically finite base.** If `g : X ⟶ W` is
proper and dominant between schemes of the same dimension `n`, with the generic point of `X` the
only point over that of `W`, every `ℚ`-Cartier `ℚ`-divisor on `X` is `g`-big: the exponent
`dim X - dim W` is zero, and `g_* 𝒪_X(kD)` has positive rank at the generic point of `W`. -/
private theorem isRelativelyBig_of_eq_genericPoint {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    (g : X ⟶ W) [IsProper g] [IsDominant g]
    (hfib : ∀ x : X, g x = genericPoint W → x = genericPoint X) {n : ℕ}
    (hX : topologicalKrullDim X = n) (hW : topologicalKrullDim W = n) {D : QDivisor X}
    (hD : D.IsQCartier) : D.IsRelativelyBig g := by
  obtain ⟨m, hm, N, hN, hNc⟩ := hD.exists_pos
  refine ⟨m, hm, N, by rw [hN, natCast_zsmul, Nat.cast_smul_eq_nsmul], hNc, n, n, hX, ?_,
    1 / 2, by norm_num, 0, fun k _ => ?_⟩
  · rw [g.denseRange.closure_range, ← hW]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ W).isHomeomorph
  · have h2 : (1 : ℝ) ≤ (relativeGenericRank g (k • N).divisorialSheaf : ℝ) := by
      exact_mod_cast one_le_relativeGenericRank g hfib (hNc.zsmul k)
    rw [Nat.sub_self, pow_zero, mul_one]
    linarith

end Big

/- ### Relative freeness over a subscheme of the base -/

section Embedding

/-- **Relative freeness over a subspace of the base.** If `ι : Z' ⟶ Z` is a topological
embedding and `L` is a Cartier divisor relatively free over `f' : X ⟶ Z'`, then `L` is
relatively free over `f' ≫ ι`: every open of `Z'` is the preimage of an open of `Z`. -/
private theorem isRelativelyFreeDivisor_comp_of_isEmbedding {X Z' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f' : X ⟶ Z') (ι : Z' ⟶ Z)
    (hι : Topology.IsEmbedding ι) {L : Divisor X} (hLc : L.IsCartier)
    (hfree : IsRelativelyFreeDivisor f' L) : IsRelativelyFreeDivisor (f' ≫ ι) L := by
  refine isRelativelyFreeDivisor_of_forall_exists (f' ≫ ι) fun x => ?_
  obtain ⟨U', hU', ψ, h1, h2⟩ := exists_coeff_add_ord_eq_zero_of_isRelativelyFree f' hLc hfree x
  obtain ⟨U, hUo, hUeq⟩ := hι.isInducing.isOpen_iff.mp U'.isOpen
  refine ⟨⟨U, hUo⟩, ?_, ψ, fun P hP => h1 P ?_, h2⟩
  · change ι (f' x) ∈ U
    have : f' x ∈ ι ⁻¹' U := by rw [hUeq]; exact hU'
    exact this
  · obtain ⟨y, hyP, hyU⟩ := hP
    refine ⟨y, hyP, ?_⟩
    have : f' y ∈ ι ⁻¹' U := hyU
    rw [hUeq] at this
    exact this

end Embedding

/-- A dominant morphism of integral schemes of finite type over a field does not raise
dimension. -/
private theorem topologicalKrullDim_le_of_isDominant {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsIntegral X] [IsIntegral Y] (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsDominant f]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType (f ≫ sX)] :
    topologicalKrullDim X ≤ topologicalKrullDim Y := by
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra (f ≫ sX)
  letI := functionFieldMapAlgebra f
  haveI := isScalarTower_functionFieldMap sX f
  rw [← toENat_trdeg_functionField (sX := sX), ← toENat_trdeg_functionField (sX := f ≫ sX)]
  have hadd := congrArg Cardinal.toENat (trdeg_add_eq k X.functionField (A := Y.functionField))
  rw [map_add] at hadd
  exact WithBot.coe_le_coe.mpr (hadd ▸ le_self_add)

/-- An equal-dimensional dominant morphism of integral schemes of finite type over a field has
only the generic point over the generic point. -/
private theorem eq_genericPoint_of_topologicalKrullDim_eq {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X)
    [IsDominant f] [LocallyOfFiniteType sX] [LocallyOfFiniteType f] [QuasiCompact f]
    (h : topologicalKrullDim Y = topologicalKrullDim X) :
    ∀ y : Y, f y = genericPoint X → y = genericPoint Y := by
  have hfin := finite_functionField_of_topologicalKrullDim_eq sX f h
  letI : Algebra X.functionField Y.functionField := (dominantFunctionFieldMap f).toAlgebra
  have h0 : Algebra.trdeg X.functionField Y.functionField = 0 := by
    have : Module.Finite X.functionField Y.functionField := by
      convert hfin using 3
      exact congrArg RingHom.toAlgebra (dominantFunctionFieldMap_eq_functionFieldMap f)
    exact trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)
  exact eq_genericPoint_of_trdeg_functionField_eq_zero f h0

/-- If the image of `f` has dimension at most one, some positive multiple of `K + B` is a
Cartier divisor that is relatively free over `f`. -/
private theorem exists_isRelativelyFreeDivisor_of_topologicalKrullDim_range_le_one
    {S Z : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sS]
    (hSp : MMP.Mori.IsProjectiveVariety ℂ sS) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    {B : QDivisor S} (hB : MMP.Intersection.IsLogCanonicalPair sS B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : S ⟶ Z) (hf : f ≫ sZ = sS)
    (himg : topologicalKrullDim (Set.range f) ≤ 1)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sS f) {A : QDivisor S} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) {G : QDivisor S}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor S, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor S,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L := by
  classical
  obtain ⟨hSv, hSproj⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ sS).mp hSp
  have hdim : topologicalKrullDim S = 2 := hK.1
  obtain ⟨Y, _, _, _, q, hqb, hYQ, Δ, hqproj, hYp, -, -, -⟩ :=
    MMP.Threefold.exists_crepant_dltModification_of_surface sS hSp hdim hB
  obtain ⟨hYv, hYproj⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ (q ≫ sS)).mp hYp
  have : IsProper sS := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hSproj).2
  have : IsProper (q ≫ sS) :=
    (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hYproj).2
  have : IsProper q := IsProper.of_comp q sS
  have : QuasiCompact (q ≫ sS) := inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (q ≫ sS)
  have : IsDominant q := hqb.isDominant
  have : AlgebraicGeometry.IsVariety ℂ sZ := ((MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZ).1
  set D := Divisor.toQDivisor K + B with hDdef
  have hDq : D.IsQCartier := hnef.1
  obtain ⟨m₀, hm₀, L, hL, ⟨e⟩⟩ := hGM
  have hLc : L.IsCartier := fun x => by
    obtain ⟨U, hU, ψ, hψ⟩ := exists_isLocalEquation_preimage_of_iso_pullback f M e (f x)
    exact ⟨f ⁻¹ᵁ U, hU, ψ, hψ⟩
  have hGq : G.IsQCartier := ⟨m₀, by exact_mod_cast hm₀.ne', L, hL, hLc⟩
  have hDAq : (D + A).IsQCartier := hDq.add hAq
  have hDG' := qpb_qLinearlyEquivalent q hDAq hGq hDG
  have hadd : qpb q (D + A) hDAq = qpb q D hDq + qpb q A hAq := by
    simpa only [one_smul] using
      qpb_zsmul_add_zsmul q hDq hAq 1 1 (by simpa only [one_smul] using hDAq)
  rw [hadd] at hDG'
  have hGM' : ∃ m : ℕ, 0 < m ∧ ∃ L' : Divisor Y,
      Divisor.toQDivisor L' = (m : ℤ) • qpb q G hGq ∧
        Nonempty (L'.divisorialSheaf ≅ (Scheme.Modules.pullback (q ≫ f)).obj M) :=
    ⟨m₀, hm₀, L.pullback hLc (map_componentGenericPoint_notMem_supp_of_isDominant q L),
      toQDivisor_pullback_eq_smul_qpb q hGq hm₀ hL hLc,
      ⟨(Divisor.isPullback_pullback hLc _).divisorialSheafIso (hBc := hLc) ≪≫
        (Scheme.Modules.pullback q).mapIso e ≪≫ (Scheme.Modules.pullbackComp q f).app M⟩⟩
  have himg' : topologicalKrullDim (Set.range (q ≫ f)) ≤ 1 := by
    have : Set.range (q ≫ f) = Set.range f := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr q.surjective, Set.image_univ]
    rwa [this]
  have hfin : letI := functionFieldMapAlgebra q; Module.Finite S.functionField Y.functionField := by
    letI := functionFieldMapAlgebra q
    exact Module.Finite.of_surjective (Algebra.linearMap S.functionField Y.functionField)
      hqb.functionFieldMap_bijective.2
  obtain ⟨m, hm, L', hL', hL'c, hfree⟩ := exists_isRelativelyFreeDivisor_of_add_qLinearlyEquivalent
    (q ≫ sS) sZ hYp hYQ (q ≫ f) (by rw [Category.assoc, hf]) himg'
    (qpb_isRelativelyNef sS q f hDq hnef) (qpb_nonneg q hAq hA) (qpb_isQCartier q hAq) hDG' M hGM'
  exact exists_isRelativelyFreeDivisor_of_pullback (q ≫ sS) sS ⟨hYv, inferInstance⟩
    ⟨hSv, inferInstance⟩ q rfl hfin f D hDq ⟨m, hm, L', hL', hL'c, hfree⟩

/-- If the image of `f` has dimension two, some positive multiple of `K + B` is a Cartier
divisor that is relatively free over `f`. -/
private theorem exists_isRelativelyFreeDivisor_of_not_topologicalKrullDim_range_le_one
    {S Z : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sS]
    (hSp : MMP.Mori.IsProjectiveVariety ℂ sS) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    {B : QDivisor S} (hB : MMP.Intersection.IsLogCanonicalPair sS B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : S ⟶ Z) (hf : f ≫ sZ = sS)
    (himg : ¬ topologicalKrullDim (Set.range f) ≤ 1)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sS f) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor S,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L := by
  classical
  obtain ⟨hSv, hSproj⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ sS).mp hSp
  obtain ⟨hZv, hZproj⟩ := (MMP.Mori.isProjectiveVariety_iff ℂ sZ).mp hZ
  have hdim : topologicalKrullDim S = 2 := hK.1
  have : IsProper sS := (isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mp hSproj).2
  have : IsSeparated sZ := hZv.toIsSeparated
  have : LocallyOfFiniteType sZ := hZv.toLocallyOfFiniteType
  have : QuasiCompact sZ := hZv.toQuasiCompact
  have : IsProper (f ≫ sZ) := hf ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sZ
  set Z' := f.image
  set ι := f.imageι
  set f' := f.toImage
  have hf'ι : f' ≫ ι = f := f.toImage_imageι
  set sZ' := ι ≫ sZ
  have hf' : f' ≫ sZ' = sS := by rw [← Category.assoc, hf'ι, hf]
  have : IsSeparated sZ' := inferInstance
  have : LocallyOfFiniteType sZ' := inferInstance
  have : QuasiCompact sZ' := inferInstance
  have : IsProper (f' ≫ sZ') := hf' ▸ inferInstance
  have : IsProper f' := IsProper.of_comp f' sZ'
  have hZ'v : AlgebraicGeometry.IsVariety ℂ sZ' :=
    (MMP.Mori.isVariety_iff ℂ sZ').2 ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  have hZ' : MMP.Mori.IsProjectiveVariety ℂ sZ' := by
    refine (MMP.Mori.isProjectiveVariety_iff ℂ sZ').2 ⟨hZ'v, ?_⟩
    obtain ⟨n, j, hj, hj'⟩ := hZproj
    exact ⟨n, ι ≫ j, inferInstance, by rw [Category.assoc, hj']⟩
  have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
  have hιemb : Topology.IsEmbedding ι := (IsClosedImmersion.isClosedEmbedding ι).isEmbedding
  have hdimZ' : topologicalKrullDim Z' = topologicalKrullDim (Set.range f) := by
    rw [← hf'ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr f'.surjective, Set.image_univ]
    exact IsHomeomorph.topologicalKrullDim_eq _ hιemb.toHomeomorph.isHomeomorph
  have hdimZ'2 : topologicalKrullDim Z' = 2 := by
    refine le_antisymm (hdim ▸ topologicalKrullDim_le_of_isDominant sZ' f') ?_
    by_contra h
    exact himg (hdimZ' ▸ Order.le_of_lt_succ (not_le.mp h))
  have hfib := eq_genericPoint_of_topologicalKrullDim_eq sZ' f' (by rw [hdim, hdimZ'2])
  have hnef' : (Divisor.toQDivisor K + B).IsRelativelyNef sS f' := by
    obtain ⟨h1, h2⟩ := hnef
    refine ⟨h1, fun C hC => h2 C fun x hx => ?_⟩
    rw [← hf'ι, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]
  have hsemi := QDivisor.isRelativelySemiample_of_isLcPair_of_isRelativelyNef_of_isRelativelyBig
    sS sZ' hSp hdim hZ' f' hf' K B hB.2.1 (isLcPair_of_isLogCanonicalPair hB hK) hnef'
    (isRelativelyBig_of_eq_genericPoint f' hfib (n := 2) hdim hdimZ'2 hnef.1)
  obtain ⟨m, hm, L, hL, hLc, hfree⟩ :=
    exists_isRelativelyFreeDivisor_of_isRelativelySemiample f' hsemi
  refine ⟨m, hm, L, hL, hLc, ?_⟩
  rw [← hf'ι]
  exact isRelativelyFreeDivisor_comp_of_isEmbedding f' ι hιemb hLc hfree

/-- **Complemented nef lc surface adjoints are relatively semiample.** Let `(S, B)` be a log
canonical pair with `B` a `ℚ`-divisor on a normal projective complex surface `S`, with canonical
divisor `K`, and let `f : S ⟶ Z` be a morphism to a projective complex variety such that `K + B`
is `f`-nef. Suppose `A ≥ 0` is a `ℚ`-Cartier divisor and `K + B + A ∼_ℚ G`, where `G` is the
pull-back of a rational Cartier divisor on `Z`: `𝒪_S(mG) ≅ f^* M` for some `m > 0` and an
invertible `𝒪_Z`-module `M`. Then `K + B` is `f`-semiample: some positive multiple `m' (K + B)`
is a Cartier divisor `L` with `f^* f_* 𝒪_S(L) → 𝒪_S(L)` surjective. -/
@[mmp "thm_mmp_surface_complemented_lc_relative_semiample"]
public theorem exists_isRelativelyFreeDivisor_of_isLogCanonicalPair_of_add_qLinearlyEquivalent
    {S Z : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sS]
    (hSp : MMP.Mori.IsProjectiveVariety ℂ sS) {K : Divisor S} (hK : K.IsCanonicalDivisor sS 2)
    {B : QDivisor S} (hB : MMP.Intersection.IsLogCanonicalPair sS B)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : S ⟶ Z) (hf : f ≫ sZ = sS)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sS f) {A : QDivisor S} (hA : 0 ≤ A)
    (hAq : A.IsQCartier) {G : QDivisor S}
    (hDG : (Divisor.toQDivisor K + B + A).QLinearlyEquivalent G) (M : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z M]
    (hGM : ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor S, Divisor.toQDivisor L = (m : ℤ) • G ∧
      Nonempty (L.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj M)) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : Divisor S,
      Divisor.toQDivisor L = (m : ℤ) • (Divisor.toQDivisor K + B) ∧ L.IsCartier ∧
        IsRelativelyFreeDivisor f L := by
  by_cases himg : topologicalKrullDim (Set.range f) ≤ 1
  · exact exists_isRelativelyFreeDivisor_of_topologicalKrullDim_range_le_one sS sZ hSp hK hB hZ
      f hf himg hnef hA hAq hDG M hGM
  · exact exists_isRelativelyFreeDivisor_of_not_topologicalKrullDim_range_le_one sS sZ hSp hK hB
      hZ f hf himg hnef

end MMP.Threefold
