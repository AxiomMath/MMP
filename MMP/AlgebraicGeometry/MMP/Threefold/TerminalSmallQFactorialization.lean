module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
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
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.DeformationSpace
import StacksFrontier.AlgebraicGeometry.FormsTrace.RelativeSections
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FamilyCoeff
import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalBundle
import StacksFrontier.AlgebraicGeometry.RegularImmersion.CodimLocal
import StacksFrontier.RingTheory.Filtration.AssociatedGradedCongr
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
import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.SupComapSubscheme
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisor
import StacksFrontier.AlgebraicGeometry.ProjThetaCompare.Morphism
import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.ChartBasicOpen
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients
import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleIrreducible
import StacksFrontier.CategoryTheory.Sites.IsIsoOfBijectiveOnCoveringObjects
import StacksFrontier.AlgebraicGeometry.Chow.SmoothComponentMultiplicity
import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveLineIdealOfEquations
import StacksFrontier.AlgebraicGeometry.Flatness.FiniteFlatLocallyFree
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
import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackEquivalence
import StacksFrontier.AlgebraicGeometry.Modules.DualBiproduct
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
import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhood
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumTwistComparison
import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
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
import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SourceDimension
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
import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TowerProjective
import StacksFrontier.AlgebraicGeometry.FlagTower.Grassmannian
import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveBundleCycleClassBridge
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupEtaleChartTransfer
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDivisor
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.Modules.MonoRestrictLocality
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionStalk
import StacksFrontier.Topology.Dimension.UnionDimension
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.LinearEquations.ChartKernel
import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso
import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtRestrictExtension
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible
import MMP.AlgebraicGeometry.Singularities.EtaleDiscrepancy
import MMP.AlgebraicGeometry.Singularities.EtaleNeighbourhoodTerminal
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalRelativeProgramme
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Small `ℚ`-factorializations of terminal threefolds

Let `U` be a normal quasi-projective complex threefold such that `(U, 0)` is terminal. Then `U`
has a small `ℚ`-factorialization: a projective small birational morphism `g : U' ⟶ U` from a
`ℚ`-factorial threefold `U'` with `(U', 0)` terminal.

## Main results

* `MMP.Fourfold.IsTerminalVariety.exists_isSmallMorphism_isQFactorial`: the small
  `ℚ`-factorialization.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace Proof_lem_mmp_indexb_small_q_factorialization

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {k : Type} [Field k] {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [IsOpenImmersion f] [Nonempty X] : topologicalKrullDim X = topologicalKrullDim Y := by
  letI : Y.Over (Spec (.of k)) := ⟨sY⟩
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sY)
  have hne : ((f.opensRange : Y.Opens) : Set Y).Nonempty :=
    ⟨_, ⟨Nonempty.some inferInstance, rfl⟩⟩
  have h := (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen k _ (_ ↘ Spec (.of k)) _
      (TopologicalSpace.Opens.isOpen _) hne).symm
  rw [(Scheme.homeoOfIso f.isoOpensRange).isHomeomorph.topologicalKrullDim_eq]
  exact h

/-! ### Compactification -/

/-- A normal quasi-projective complex variety is a dense open subscheme of a normal projective
complex variety. -/
private theorem exists_normal_projective_compactification {U : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)} (hUn : IsNormalVariety ℂ sU)
    (hUq : IsQuasiProjectiveVariety ℂ sU) :
    ∃ (Ub : Scheme.{0}) (_ : IsIntegral Ub) (_ : IsLocallyNoetherian Ub) (_ : IsNormal Ub)
      (_ : CompactSpace Ub) (sUb : Ub ⟶ Spec (.of ℂ)) (ι : U ⟶ Ub),
      IsOpenImmersion ι ∧ ι ≫ sUb = sU ∧ MMP.Mori.IsProjectiveVariety ℂ sUb ∧
        IsNormalVariety ℂ sUb := by
  obtain ⟨hUv, -⟩ := hUn
  have hqp : IsQuasiProjective sU := ((isQuasiProjectiveVariety_iff ℂ sU).mp hUq).2
  obtain ⟨n, i, hi, hiqc, hip⟩ := isHQuasiProjective_of_isQuasiProjective sU
    (Stacks.Ample.unitModule (Spec (.of ℂ)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))) hqp
  have : IsImmersion i := hi
  have : QuasiCompact i := hiqc
  set π := projectiveSpaceOver n (Spec (.of ℂ)) ↘ Spec (.of ℂ) with hπ
  have hπp : IsProjectiveMorphism π := ⟨n, 𝟙 _, inferInstance, Category.id_comp _⟩
  have : IsProper π := isProper_of_isProjectiveMorphism π hπp
  have hNagata : IsNagataScheme (projectiveSpaceOver n (Spec (.of ℂ))) :=
    isNagataScheme_of_locallyOfFiniteType_over_field ℂ π
  have hfin : IsFinite i.fromNormalization :=
    isFinite_fromNormalization_of_locallyOfFiniteType i hNagata
  have hcomp : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite :=
    fun V hV => by
      have : IsNoetherian V :=
        { toIsLocallyNoetherian := inferInstance
          toCompactSpace := isCompact_iff_compactSpace.mp hV }
      exact finite_irreducibleComponents_of_isNoetherian
  have hproj : IsProjective (i.fromNormalization ≫ π) :=
    (Stacks.FiniteMorphismProjective.isProjective_of_isFinite i.fromNormalization).comp
      hπp.isProjective
  have h2 : IsProjectiveMorphism (i.fromNormalization ≫ π) :=
    isProjectiveMorphism_of_isProjective _ (Stacks.Ample.unitModule (Spec (.of ℂ)))
      (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))) hproj
  have hnorm : IsNormal i.normalization := isNormal_normalization i hcomp
  have : IsProper (i.fromNormalization ≫ π) := isProper_of_isProjectiveMorphism _ h2
  have hv : AlgebraicGeometry.IsVariety ℂ (i.fromNormalization ≫ π) := { }
  have : IsIntegral i.normalization := inferInstance
  have : IsLocallyNoetherian i.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian (i.fromNormalization ≫ π)
  have : CompactSpace i.normalization :=
    QuasiCompact.compactSpace_of_compactSpace (i.fromNormalization ≫ π)
  refine ⟨i.normalization, inferInstance, inferInstance, hnorm, inferInstance,
    i.fromNormalization ≫ π, i.toNormalization, inferInstance, ?_,
    (MMP.Mori.isProjectiveVariety_iff _ _).mpr ⟨hv, h2⟩, ⟨hv, hnorm⟩⟩
  rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hip]

/-! ### Resolution -/

/-- A scheme separated over a field is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {X : Scheme.{0}} {s : X ⟶ Spec (.of ℂ)}
    (hs : IsSeparated s) : IsSeparated (X ↘ Limits.terminal Scheme) := by
  rw [show (X ↘ Limits.terminal Scheme) = s ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- A divisor `(Y, f, E)` over a separated normal scheme `X` is exceptional if and only if
`f(η_E)` has coheight at least two. -/
private theorem isExceptional_iff_two_le_coheight {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [IsSeparated (X ↘ Limits.terminal Scheme)] (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff,
    MMP.Flips.le_closedsCodimension_iff_le_coheight]
  have hc : ((TopologicalSpace.Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) :
      TopologicalSpace.Closeds X) : Set X) = closure {D.f D.E.genericPoint} :=
    D.center_eq_closure_genericPoint
  rw [hc]
  exact ⟨fun h => h _ (subset_closure rfl),
    fun h x hx => h.trans (Order.coheight_anti (specializes_iff_mem_closure.mpr hx))⟩

/-- **Divisors that are not exceptional have log discrepancy one** over a pair `(X, 0)`: such a
divisor has the valuation of a prime divisor `P` of `X`, whose discrepancy is `-coeff_P 0 = 0`. -/
private theorem eq_one_of_not_isExceptional {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hP : MMP.Mori.IsPair sX 0)
    {D : DivisorOver ℂ sX} (hD : ¬ D.IsExceptional) {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n 0 D a) : a = 1 := by
  obtain ⟨P, hv⟩ :=
    MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hP.1 D hD
  obtain ⟨-, n₀, K, hK, -⟩ := id hP
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (DivisorOver.ofPrimeDivisor ℂ hP.1 P)
  have hc0 := MMP.Mori.IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hP.1 hc
  have h1 := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc
    (show IsProper (𝟙 X) from inferInstance)
  rw [map_zero] at h1
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha h1 hv, hc0]
  simp

/-- A smooth variety `X` with canonical divisor of index `n` makes `(X, 0)` a pair. -/
private theorem isPair_zero_of_isSmoothScheme {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n) :
    ∃ K : Divisor X, K.IsCanonicalDivisor sX n ∧ MMP.Mori.IsPair sX 0 := by
  haveI := hX.1
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsm hn
  refine ⟨K, hK, hX, n, K, hK, ?_⟩
  rw [add_zero]
  exact MMP.Mori.QDivisor.isQCartier_toQDivisor (MMP.Fourfold.isCartier_of_isSmoothScheme hsm K)

/-- **Log discrepancies over a smooth variety.** If `X` is smooth, every log discrepancy of
`(X, 0)` is at least one, and at least two for an exceptional divisor over `X`. -/
private theorem one_le_logDiscrepancy_of_isSmoothScheme {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (hsm : IsSmoothScheme sX) {D : DivisorOver ℂ sX} {n : ℕ} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n 0 D a) : 1 ≤ a ∧ (D.IsExceptional → 2 ≤ a) := by
  have hn := MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  obtain ⟨K, hK, hP⟩ := isPair_zero_of_isSmoothScheme hX hsm hn
  by_cases hD : D.IsExceptional
  · obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
    have ha' : MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor 0) D a := by
      rwa [map_zero]
    have hac := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy hc ha'
    haveI := isSeparated_toTerminal (hX.1.toIsSeparated)
    haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
    have h2n : 2 ≤ n := by
      have h2 := (isExceptional_iff_two_le_coheight D).mp hD
      have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
        (D.f D.E.genericPoint)
      rw [hn] at h
      have h0 : (0 : WithBot ℕ∞) ≤
          topologicalKrullDim (closure {D.f D.E.genericPoint} : Set X) := by
        have : Nonempty (TopologicalSpace.IrreducibleCloseds
            (closure {D.f D.E.genericPoint} : Set X)) :=
          ⟨TopologicalSpace.IrreducibleCloseds.closureSingleton ⟨_, subset_closure rfl⟩⟩
        exact Order.krullDim_nonneg
      have h2' : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
        rw [← h]
        calc ((2 : ℕ∞) : WithBot ℕ∞) ≤ (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) :=
              WithBot.coe_le_coe.mpr h2
          _ ≤ _ := le_add_of_nonneg_left h0
      exact_mod_cast h2'
    haveI : LocallyOfFinitePresentation sX :=
      (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sX)).mpr inferInstance
    have hdisc := MMP.Mori.discrep_eq_of_isSNC sX hX hsm h2n hK (Δ := 0) ∅ (by simp)
      (by simpa using MMP.Mori.DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme sX hsm) (by simp)
    have hle := MMP.Mori.discrep_le hD hc
    simp only [Finset.notMem_empty, iInf_false, iInf_top, top_inf_eq] at hdisc
    rw [hdisc] at hle
    have h1c : (1 : ℝ) ≤ c := by exact_mod_cast EReal.coe_le_coe_iff.mp hle
    exact ⟨by linarith, fun _ => by linarith⟩
  · have := eq_one_of_not_isExceptional hP hD ha
    exact ⟨this.ge, fun h => absurd h hD⟩

/-- A smooth complex variety is terminal. -/
private theorem isTerminalVariety_of_isSmoothScheme {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n) :
    IsTerminalVariety sX := by
  obtain ⟨-, -, hP⟩ := isPair_zero_of_isSmoothScheme hX hsm hn
  refine ⟨⟨⟨inferInstance, inferInstance, hP, fun _ => le_rfl⟩, fun m D a ha => ?_⟩,
    fun m D a hD ha => ?_⟩
  · rw [map_zero] at ha
    linarith [(one_le_logDiscrepancy_of_isSmoothScheme hX hsm ha).1]
  · rw [map_zero] at ha
    linarith [(one_le_logDiscrepancy_of_isSmoothScheme hX hsm ha).2 hD]

/-- A normal projective complex threefold `Ū` has a projective birational morphism from a
`ℚ`-factorial projective threefold `W₀` with `(W₀, 0)` terminal (a projective resolution). -/
private theorem exists_terminal_resolution {Ub : Scheme.{0}} [IsIntegral Ub]
    [IsLocallyNoetherian Ub] [IsNormal Ub] [CompactSpace Ub] {sUb : Ub ⟶ Spec (.of ℂ)}
    (hUbp : MMP.Mori.IsProjectiveVariety ℂ sUb) (hUbn : IsNormalVariety ℂ sUb)
    (hdim : topologicalKrullDim Ub = 3) :
    ∃ (W₀ : Scheme.{0}) (_ : IsIntegral W₀) (_ : CompactSpace W₀) (_ : IsLocallyNoetherian W₀)
      (_ : IsNormal W₀) (sW₀ : W₀ ⟶ Spec (.of ℂ)) (μ₀ : W₀ ⟶ Ub),
      IsTerminalVariety sW₀ ∧ IsQFactorial sW₀ ∧ MMP.Mori.IsProjectiveVariety ℂ sW₀ ∧
        topologicalKrullDim W₀ = 3 ∧ μ₀ ≫ sUb = sW₀ ∧ IsBirationalMorphism μ₀ := by
  obtain ⟨hvUb, hpUb⟩ := (MMP.Mori.isProjectiveVariety_iff _ _).mp hUbp
  obtain ⟨W₀, g, hW, hgproj, hgb, hsm, -, -⟩ := MMP.Resolution.exists_isStrongResolution sUb hvUb
  haveI := hW
  haveI : IsIntegral W₀ := hW.toIsIntegral
  obtain ⟨hln, hnorm⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hsm
  haveI : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace (g ≫ sUb)
  have hproj : IsProjective (g ≫ sUb) := hgproj.comp hpUb.isProjective
  have hP : IsProjectiveMorphism (g ≫ sUb) :=
    isProjectiveMorphism_of_isProjective _ (Stacks.Ample.unitModule (Spec (.of ℂ)))
      (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))) hproj
  have hWn : IsNormalVariety ℂ (g ≫ sUb) := ⟨hW, hnorm⟩
  have hd : topologicalKrullDim W₀ = 3 := by
    rw [← hdim]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sUb (g ≫ sUb) hgb).symm
  refine ⟨W₀, inferInstance, inferInstance, hln, hnorm, g ≫ sUb, g,
    isTerminalVariety_of_isSmoothScheme hWn hsm (n := 3) (by exact_mod_cast hd),
    ⟨hWn, fun D => ⟨1, one_pos, by simpa using isCartier_of_isSmoothScheme hsm D⟩⟩,
    (MMP.Mori.isProjectiveVariety_iff _ _).mpr ⟨hW, hP⟩, hd, rfl, hgb⟩

/-! ### The terminal programme over a projective base -/

/-- The terminal `K`-programme of `W₀` over a projective base `S` terminates: there is a normal
projective `ℚ`-factorial threefold `W` with `(W, 0)` terminal, a projective birational
`μ : W ⟶ S` and a canonical divisor of `W` nef over `S`. -/
private theorem exists_relativelyNef_terminal_model {W₀ S : Scheme.{0}}
    [IsIntegral W₀] [CompactSpace W₀] [IsLocallyNoetherian W₀] [IsNormal W₀]
    {sW₀ : W₀ ⟶ Spec (.of ℂ)} (hW : IsTerminalVariety sW₀) (hQ : IsQFactorial sW₀)
    (hWp : MMP.Mori.IsProjectiveVariety ℂ sW₀) (hdim : topologicalKrullDim W₀ = 3)
    {sS : S ⟶ Spec (.of ℂ)} (hS : MMP.Mori.IsProjectiveVariety ℂ sS) {μ₀ : W₀ ⟶ S}
    (hμ : μ₀ ≫ sS = sW₀) (hμb : IsBirationalMorphism μ₀) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : CompactSpace W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (μ : W ⟶ S),
      IsQFactorial sW ∧ MMP.Mori.IsProjectiveVariety ℂ sW ∧ topologicalKrullDim W = 3 ∧
      IsTerminalVariety sW ∧ μ ≫ sS = sW ∧ IsBirationalMorphism μ ∧ IsProjectiveMorphism μ ∧
      ∃ (K : Divisor W) (m : ℕ), K.IsCanonicalDivisor sW m ∧
        MMP.Flips.IsRelativelyNef ℂ sW μ (QDivisor.toRDivisor (Divisor.toQDivisor K)) := by
  obtain ⟨-, n, K, hK, -⟩ := hW.1.1.isPair
  have hn : n = 3 := by
    have := hK.topologicalKrullDim_eq
    rw [hdim] at this
    exact_mod_cast this.symm
  subst hn
  obtain ⟨P, hn, hproj, -, hall, hnef⟩ :=
    exists_relativeDltProgram_isRelativelyNef_of_isTerminalVariety W₀ S sW₀ sS μ₀ hWp hQ hdim hW
      hS hμ hμb K hK
  have hN : ((P.n.toNat : ℕ) : ℕ∞) ≤ P.n := by rw [ENat.coe_toNat hn]
  obtain ⟨hQN, hdN, htN, hpN, hbN⟩ := hall _ hN
  have hmod := P.isRelativeDltModel _ hN
  obtain ⟨m, hm⟩ := hmod.isCanonicalDivisor
  exact ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, _, _, hQN, hproj.2 _ hN,
    hdN, htN, hmod.comp_eq, hbN, hpN, _, m, hm, hnef⟩

/-! ### Restriction over `U` and smallness -/

/-- The birational transform of divisors commutes with regarding a divisor as a
`ℚ`-divisor. -/
private theorem transformDivisor_toQDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : Divisor X) :
    MMP.Mori.RationalMap.transformDivisor φ (Divisor.toQDivisor D) =
      Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor φ D) := by
  classical
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  | single P n =>
    have hP : Divisor.toQDivisor (Finsupp.single P n) = Finsupp.single P (n : ℚ) := by
      ext E
      change ((Finsupp.single P n E : ℤ) : ℚ) = Finsupp.single P (n : ℚ) E
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp
    rw [hP, MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    cases MMP.Mori.RationalMap.transformPrimeDivisor φ P with
    | none => simp
    | some E =>
      simp only [Option.elim]
      ext F
      change (Finsupp.single E (n : ℚ)) F = (((Finsupp.single E n) F : ℤ) : ℚ)
      rw [Finsupp.single_apply, Finsupp.single_apply]
      split_ifs <;> simp

/-- A proper birational morphism `r : Z ⟶ Y` onto a normal variety is an isomorphism over the
points of codimension at most one: an exceptional point maps to a point of coheight at least
two. -/
private theorem two_le_coheight_map_of_mem_exceptionalSet {Y Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsNormal Y] (hYv : MMP.Mori.IsVariety ℂ sY) (r : Z ⟶ Y)
    (hZv : MMP.Mori.IsVariety ℂ (r ≫ sY)) [IsProper r] (hrb : IsBirationalMorphism r) {x : Z}
    (hx : x ∈ MMP.Mori.exceptionalSet r) : 2 ≤ Order.coheight (r x) := by
  haveI : IsIntegral Y := hYv.toIsIntegral
  haveI : IsIntegral Z := hZv.toIsIntegral
  haveI : IsDominant r := hrb.isDominant
  have hb := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hrb
  obtain ⟨-, hex, -⟩ :=
    MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hZv hYv r rfl hb
  have hpos : 0 < topologicalKrullDim (r ⁻¹' {r x}) := by
    have : x ∈ (MMP.Mori.exceptionalSet r : Set Z) := hx
    rwa [hex] at this
  set y := r x
  let e := r.fiberHomeo y
  rw [← (e.isHomeomorph).topologicalKrullDim_eq] at hpos
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints,
    Order.krullDim_pos_iff] at hpos
  obtain ⟨a, b, hab⟩ := hpos
  have hI : Topology.IsInducing (fun t => (e t).1) :=
    Topology.IsInducing.subtypeVal.comp e.isInducing
  set w := (e b).1
  set w' := (e a).1
  have hw : r w = y := (e b).2
  have hw' : r w' = y := (e a).2
  have hlt : w' < w := by
    rw [lt_iff_le_not_ge] at hab ⊢
    exact ⟨hI.specializes_iff.mpr hab.1, fun h => hab.2 (hI.specializes_iff.mp h)⟩
  have hdim : topologicalKrullDim Z = topologicalKrullDim Y :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (r ≫ sY) hrb).symm
  have hle : ∀ t : Z, Order.coheight t ≤ Order.coheight (r t) := fun t =>
    MMP.Flips.coheight_le_coheight_map sY (r ≫ sY) hYv hZv r rfl hdim t
  by_contra hcon
  push Not at hcon
  have h1 : Order.coheight w' ≤ 1 := (hle w').trans (hw' ▸ Order.le_of_lt_succ hcon)
  have hwfin : Order.coheight w < ⊤ :=
    (hle w).trans_lt (hw ▸ hcon.trans_le le_top)
  have h2 : Order.coheight w < Order.coheight w' := Order.coheight_strictAnti hlt hwfin
  have h0 : Order.coheight w = 0 := ENat.lt_one_iff_eq_zero.mp (h2.trans_le h1)
  have hmax : IsMax w := Order.coheight_eq_zero.mp h0
  have hgw : w = genericPoint Z :=
    (Specializes.antisymm (hmax (genericPoint_specializes w)) (genericPoint_specializes w)).eq
  have hyg : y = genericPoint Y := by
    rw [← hw, hgw]
    exact MMP.Positivity.map_genericPoint_eq_of_isDominant r
  have hmaxY : IsMax (genericPoint Y) := fun z _ => genericPoint_specializes z
  have h3 : Order.coheight w' ≤ 0 := by
    have := hle w'
    rwa [hw', hyg, Order.coheight_eq_zero.mpr hmaxY] at this
  exact absurd (h2.trans_le h3) (by simp)

/-! ### Intersection numbers -/

section Intersection

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    MMP.Flips.IsCartierIntersectionNumber ℂ sX C L hL (L.degreeOn ℂ sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve ℂ p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType ℂ p
  have hvar : AlgebraicGeometry.IsVariety ℂ (normalizationOverField ℂ p ≫ p) :=
    isVariety_normalizationOverField ℂ p
  have : IsIntegral (normalizationSchemeOverField ℂ p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField ℂ p) := isFinite_normalizationOverField ℂ p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField ℂ p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism :=
        MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isBirational _
          (Scheme.isBirational_normalization C.scheme hX) }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField ℂ p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  have : IsProper ((normalizationOverField ℂ p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (MMP.Fourfold.Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    MMP.Flips.IsRIntersectionNumber ℂ sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn ℂ sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn sX C (L j) (hL j), rfl⟩

/-- Every value of `D · C` is `∑ r_j (L_j · C)`, for any presentation `D = ∑ r_j L_j`. -/
private theorem eq_sum_degreeOn_of_isRIntersectionNumber (C : ProperCurve sX) {D : RDivisor X}
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) {m' : ℕ} {r' : Fin m' → ℝ}
    {L' : Fin m' → Divisor X} {x : ℝ} (hx : MMP.Flips.IsRIntersectionNumber ℂ sX D r' L' C x) :
    x = ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hL j) : ℝ) := by
  subst hD
  exact (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r' L' r L _ _ hx
    (isRIntersectionNumber_sum_degreeOn sX C r L hL)

/-- A sum of nef `ℝ`-divisors over `Y` is nef over `Y`. -/
private theorem isRelativelyNef_add {Y : Scheme.{0}} {g : X ⟶ Y} {D₁ D₂ : RDivisor X}
    (h₁ : MMP.Flips.IsRelativelyNef ℂ sX g D₁) (h₂ : MMP.Flips.IsRelativelyNef ℂ sX g D₂) :
    MMP.Flips.IsRelativelyNef ℂ sX g (D₁ + D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl, hn₁⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, rfl, hn₂⟩ := h₂
  have hc : ∀ j, (Fin.append L₁ L₂ j).IsCartier :=
    Fin.addCases (fun j => by simpa using hL₁ j) (fun j => by simpa using hL₂ j)
  refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂, hc, ?_, fun C hC x hx => ?_⟩
  · simp [Fin.sum_univ_add]
  · have hx₁ := isRIntersectionNumber_sum_degreeOn sX C r₁ L₁ hL₁
    have hx₂ := isRIntersectionNumber_sum_degreeOn sX C r₂ L₂ hL₂
    have hsum := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX C).2 _ _ r₁ L₁ r₂ L₂ _ _
      1 1 hx₁ hx₂
    simp only [one_smul, one_mul] at hsum
    rw [(MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ hx hsum]
    exact add_nonneg (hn₁ C hC _ hx₁) (hn₂ C hC _ hx₂)

end Intersection

/-- **The pull-back of a `ℚ`-Cartier divisor is numerically trivial over the base**: for
`R = g^* K`, the `ℝ`-divisor `-R` is `g`-nef, since `R` has degree zero on every curve
contracted by `g`. -/
private theorem isRelativelyNef_neg_of_isPullback {U U' : Scheme.{0}} [IsIntegral U']
    [IsLocallyNoetherian U'] [IsNormal U'] {sU' : U' ⟶ Spec (.of ℂ)} [QuasiCompact sU']
    {sU : U ⟶ Spec (.of ℂ)} [QuasiCompact sU] [IsSeparated sU] [LocallyOfFiniteType sU]
    [IsLocallyNoetherian U] [IsNormal U] (g : U' ⟶ U) (hg : g ≫ sU = sU') {K : QDivisor U}
    (hK : K.IsQCartier)
    {hB : ∀ Z : irreducibleComponents U', g (componentGenericPoint U' Z) ∉ K.supp}
    {R : QDivisor U'} (hR : K.IsPullback g hB R) :
    MMP.Flips.IsRelativelyNef ℂ sU' g (-(QDivisor.toRDivisor R)) := by
  obtain ⟨m, hm, M, hM, hMc⟩ := hK.exists_pos
  obtain ⟨M', hM'q, hMp⟩ := hR m hm M hM hMc
  have hM'c := hMp.isCartier hMc
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpres : -(QDivisor.toRDivisor R) =
      ∑ _j : Fin 1, (-(1 / (m : ℝ))) • Divisor.toRDivisor M' := by
    refine Finsupp.ext fun P => ?_
    have h1 := congrArg (fun G : QDivisor U' => G P) hM'q
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
    change ((M' P : ℤ) : ℚ) = m * R P at h1
    have h2 : ((M' P : ℤ) : ℝ) = (m : ℝ) * ((R P : ℚ) : ℝ) := by exact_mod_cast h1
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Finsupp.neg_apply, Finsupp.smul_apply, smul_eq_mul]
    change -((R P : ℚ) : ℝ) = -(1 / (m : ℝ)) * ((M' P : ℤ) : ℝ)
    rw [h2]
    field_simp
  refine ⟨1, fun _ => -(1 / (m : ℝ)), fun _ => M', fun _ => hM'c, hpres, fun C hC x hx => ?_⟩
  rw [eq_sum_degreeOn_of_isRIntersectionNumber sU' C _ _ (fun _ => hM'c) hpres hx]
  have h0 := MMP.Fourfold.Oai4C1.degreeOn_isPullback_eq_zero (k := ℂ) g hg hMc hMp C hC
  simp [h0]

/-- The coefficient of the restriction `L|_V` of a Cartier divisor along a prime divisor `E` of
the open subscheme `V` is the coefficient of `L` along the closure of `E`. -/
private theorem coeff_pullback_ι {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (V : Y.Opens) [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {L : Divisor Y} (hL : L.IsCartier)
    (hB : ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ L.supp)
    (E : MMP.Mori.PrimeDivisor V) :
    (L.pullback hL hB).coeff E = L.coeff (OpenWeilRestriction.primeDivisorMap V.ι E) :=
  MMP.Positivity.coeff_eq_of_isPullback E _
    (OpenWeilRestriction.genericPoint_primeDivisorMap V.ι E).symm hL
    (Divisor.isPullback_pullback hL hB)

/-! ### Curves and nefness on an open subscheme -/

/-- A proper curve `C` of an open `U ⊆ X`, `X` separated over `ℂ`, is a proper curve `Γ` of `X`
with the same generic point, whose closure lies in `U`. -/
private theorem exists_properCurve_of_opens {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsSeparated sX] (U : X.Opens) (C : ProperCurve (U.ι ≫ sX)) :
    ∃ Γ : ProperCurve sX, Γ.point = U.ι C.point ∧ closure ({Γ.point} : Set X) ⊆ U := by
  have : IsProper ((C.ι ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have : IsProper (C.ι ≫ U.ι) := IsProper.of_comp (C.ι ≫ U.ι) sX
  have hrange : Set.range (C.ι ≫ U.ι) = U.ι '' closure {C.point} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    congr 1
    change Set.range (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({C.point} : Set U))).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  have hcl : closure ({U.ι C.point} : Set X) ⊆ Set.range U.ι := by
    refine (closure_minimal ?_ (C.ι ≫ U.ι).isClosedMap.isClosed_range).trans ?_
    · rw [Set.singleton_subset_iff, hrange]; exact ⟨C.point, subset_closure rfl, rfl⟩
    · rw [hrange]; exact Set.image_subset_range _ _
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso U.ι C.point rfl hcl
  refine ⟨⟨U.ι C.point, ⟨?_, ?_⟩⟩, rfl, ?_⟩
  · rw [← IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact C.dim_eq
  · have : curveSubschemeAtι (U.ι C.point) ≫ sX = e.inv ≫ (C.ι ≫ U.ι) ≫ sX := by
      rw [← he, Category.assoc, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  · rw [Scheme.Opens.range_ι] at hcl
    exact hcl

/-- **Degrees can be computed on an open subscheme.** Let `V ⊆ Y` be an integral open subscheme,
`L` a Cartier divisor on `Y` and `C` a proper curve of `Y` lying in `V`, which is the proper curve
`C_V` of `V`. Then the degree of the restriction `L|_V` along `C_V` is the degree of `L` along
`C`. -/
private theorem degreeOn_pullback_ι {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]
    (V : Y.Opens) [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {L : Divisor Y} (hL : L.IsCartier)
    (hB : ∀ Z : irreducibleComponents V, V.ι (componentGenericPoint V Z) ∉ L.supp)
    (C : ProperCurve sY) (CV : ProperCurve (V.ι ≫ sY)) (hC : V.ι CV.point = C.point)
    (hCV : closure ({C.point} : Set Y) ⊆ V) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    (L.pullback hL hB).degreeOn ℂ (V.ι ≫ sY) CV.ι CV.dim_le (hL.isCartier_pullback V.ι hB) =
      L.degreeOn ℂ sY C.ι C.dim_le hL := by
  have := QuasiCompact.compactSpace_of_compactSpace sY
  have := hL.isInvertibleModule_divisorialSheaf
  have hLV := hL.isCartier_pullback V.ι hB
  have := hLV.isInvertibleModule_divisorialSheaf
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso V.ι CV.point hC (by
    rw [Scheme.Opens.range_ι]; exact hCV)
  have : IsProper ((CV.ι ≫ V.ι) ≫ sY) := by rw [Category.assoc]; infer_instance
  have h1 := MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp ℂ sY C.ι (CV.ι ≫ V.ι) C.dim_le
    CV.dim_le e.symm (by rw [Iso.symm_hom, Iso.inv_comp_eq]; exact he.symm) L.divisorialSheaf
  have h2 := MMP.Threefold.Resolution.degreeOn_comp ℂ sY V.ι CV.ι CV.dim_le L.divisorialSheaf
  obtain ⟨e₂⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hL V.ι hB
  have h3 := MMP.Mori.degreeOn_eq_of_iso ℂ (V.ι ≫ sY) CV.ι CV.dim_le e₂
  exact (h1.trans (h2.trans h3.symm)).symm

/-- **Nefness restricts to an open subscheme.** Let `O ⊆ W` be a nonempty open subscheme and
`g : O ⟶ Z`, `j : Z ⟶ Y`, `μ : W ⟶ Y` with `g ≫ j = (O ⟶ W) ≫ μ`. If an `ℝ`-divisor `D` on `W` is
`μ`-nef, then its restriction `D|_O` is `g`-nef: a curve of `O` contracted by `g` is a curve of
`W` contracted by `μ`, along which the restricted Cartier divisors have the same degrees. -/
private theorem isRelativelyNef_restrict {W Y Z : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {sW : W ⟶ Spec (.of ℂ)} [IsSeparated sW]
    [QuasiCompact sW] (O : W.Opens) [Nonempty O] [IsLocallyNoetherian O] [IsNormal O]
    [CompactSpace O] [QuasiCompact (O.ι ≫ sW)] {μ : W ⟶ Y} {g : O.toScheme ⟶ Z} {j : Z ⟶ Y}
    (hj : g ≫ j = O.ι ≫ μ) {D : RDivisor W} (hD : MMP.Flips.IsRelativelyNef ℂ sW μ D)
    {D' : RDivisor O}
    (hD' : ∀ P, D'.coeff P = D.coeff (OpenWeilRestriction.primeDivisorMap O.ι P)) :
    MMP.Flips.IsRelativelyNef ℂ (O.ι ≫ sW) g D' := by
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsDominant O.ι := MMP.Fourfold.isDominant_ι_of_nonempty O
  obtain ⟨m, r, L, hL, hDp, hall⟩ := hD
  have hB : ∀ i, ∀ Z : irreducibleComponents O, O.ι (componentGenericPoint O Z) ∉ (L i).supp :=
    fun i => MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant O.ι (L i)
  let L' : Fin m → Divisor O := fun i => (L i).pullback (hL i) (hB i)
  have hL' : ∀ i, (L' i).IsCartier := fun i => (hL i).isCartier_pullback O.ι (hB i)
  have hD'p : D' = ∑ i, r i • Divisor.toRDivisor (L' i) := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    rw [hD' P, hDp, MMP.Flips.coeff_sum_smul_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_pullback_ι O (hL i) (hB i) P]
  refine ⟨m, r, L', hL', hD'p, fun C hC x hx => ?_⟩
  obtain ⟨Γ, hΓ, hcl⟩ := exists_properCurve_of_opens sW O C
  have hdeg : ∀ i, (L' i).degreeOn ℂ (O.ι ≫ sW) C.ι C.dim_le (hL' i) =
      (L i).degreeOn ℂ sW Γ.ι Γ.dim_le (hL i) := fun i =>
    degreeOn_pullback_ι O (hL i) (hB i) Γ C hΓ.symm hcl
  have hΓc : Γ.IsContractedBy μ := by
    intro w hw
    have hwO : w ∈ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hcl hw
    obtain ⟨c, rfl⟩ := hwO
    have hc : c ∈ closure ({C.point} : Set O) := by
      rw [O.ι.isOpenEmbedding.toIsEmbedding.closure_eq_preimage_closure_image,
        Set.image_singleton, ← hΓ]
      exact hw
    have h1 := hC c hc
    rw [hΓ, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hj, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply, h1]
  rw [eq_sum_degreeOn_of_isRIntersectionNumber (O.ι ≫ sW) C r L' hL' hD'p hx]
  simp_rw [hdeg]
  exact hall Γ hΓc _ (hDp ▸ isRIntersectionNumber_sum_degreeOn sW Γ r L hL)

/-! ### The log discrepancy read on a model -/

/-- **The log discrepancy on a model with compatible canonical divisors.** Let `(X, B)` be a
normal variety with canonical divisor `K` and `K + B` `ℚ`-Cartier, `r : W ⟶ X` a proper
birational morphism from a normal variety with canonical divisor `K_W`, `r_* K_W = K`, and
`R = r^*(K + B)`. Then the log discrepancy of a prime divisor `P` of `W` is
`1 + coeff_P (K_W - R)`. -/
private theorem isLogDiscrepancy_of_isPullback {X W : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (hX : IsNormalVariety ℂ sX) {d : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX d)
    {B : QDivisor X} (hKB : (Divisor.toQDivisor K + B).IsQCartier) {r : W ⟶ X} [IsProper r]
    (hr : IsBirationalMorphism r) (hW : IsNormalVariety ℂ (r ≫ sX))
    [LocallyOfFiniteType (r ≫ sX)] {KW : Divisor W} (hKW : KW.IsCanonicalDivisor (r ≫ sX) d)
    (hKX : RationalMap.transformDivisor (X := W) r.toRationalMap KW = K)
    {hR₀ : ∀ Z : irreducibleComponents W,
      r (componentGenericPoint W Z) ∉ (Divisor.toQDivisor K + B).supp}
    {R : QDivisor W} (hR : (Divisor.toQDivisor K + B).IsPullback r hR₀ R)
    (P : MMP.Mori.PrimeDivisor W) :
    MMP.Intersection.IsLogDiscrepancy sX d (QDivisor.toRDivisor B)
      (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX) (1 + KW P - R P) := by
  haveI := hr.isDominant
  obtain ⟨ω, hω0, hωK, hωW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hX hW hr hK hKW hKX
  obtain ⟨m, hm, L, hL, hLc⟩ := hKB.exists_pos
  obtain ⟨L', hL'q, hLp⟩ := hR m hm L hL hLc
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  refine ⟨hX, inferInstance, ω, hω0, ⟨K, hK, fun Γ => by rw [← hωK]; rfl⟩, 1,
    fun _ => ((m : ℝ)⁻¹), fun _ => L, fun _ => L', fun _ => hLc, fun Γ => ?_,
    fun _ => ⟨_, hLp⟩, ?_⟩
  · have h1 := congrArg (fun G : QDivisor X => G Γ) hL
    have h2 : Γ.ordForm ω = K Γ := by rw [← hωK]; rfl
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast, Finsupp.add_apply] at h1
    change ((L Γ : ℤ) : ℚ) = m * (((K Γ : ℤ) : ℚ) + B Γ) at h1
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      QDivisor.coeff_toRDivisor, h2]
    change (((K Γ : ℤ) : ℝ)) + ((B Γ : ℚ) : ℝ) = (m : ℝ)⁻¹ * ((L Γ : ℤ) : ℝ)
    have h3 : ((L Γ : ℤ) : ℝ) = (m : ℝ) * (((K Γ : ℤ) : ℝ) + ((B Γ : ℚ) : ℝ)) := by
      exact_mod_cast h1
    rw [h3]
    field_simp
  · have h1 := congrArg (fun G : QDivisor W => G P) hL'q
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h1
    change ((L' P : ℤ) : ℚ) = m * R P at h1
    have h2 : DivisorOver.ordPullback (⟨W, r, hW, hr, P⟩ : DivisorOver ℂ sX) ω = KW P := by
      rw [← hωW]; rfl
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, h2]
    change 1 + ((KW P : ℤ) : ℝ) - ((R P : ℚ) : ℝ) =
      1 + ((KW P : ℤ) : ℝ) - (m : ℝ)⁻¹ * ((L' P : ℤ) : ℝ)
    have h3 : ((L' P : ℤ) : ℝ) = (m : ℝ) * ((R P : ℚ) : ℝ) := by exact_mod_cast h1
    rw [h3]
    field_simp

/-! ### The negativity argument -/

/-- **No exceptional divisor over a terminal base on a `K`-nef model.** Let `g : U' ⟶ U` be a
proper birational morphism of normal complex varieties with `(U, 0)` terminal, and let `K_{U'}`
be a canonical divisor of `U'` nef over `U`. Then no prime divisor `P` of `U'` maps to a point of
codimension at least two. With `K_U = g_* K_{U'}`, the divisor `B = g^* K_U - K_{U'}` has
`-B ≡_g K_{U'}` nef and `g_* B = 0`, so `B` is effective (negativity lemma); but terminality
gives `coeff_P B = 1 - a(P; U, 0) < 0`. -/
private theorem false_of_two_le_coheight {U U' : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U']
    [CompactSpace U'] {sU : U ⟶ Spec (.of ℂ)} (hU : IsTerminalVariety sU)
    (hUn : IsNormalVariety ℂ sU) (g : U' ⟶ U) (hU'n : IsNormalVariety ℂ (g ≫ sU)) [IsProper g]
    (hgb : IsBirationalMorphism g) {K' : Divisor U'} {n : ℕ}
    (hK' : K'.IsCanonicalDivisor (g ≫ sU) n)
    (hnef : MMP.Flips.IsRelativelyNef ℂ (g ≫ sU) g
      (QDivisor.toRDivisor (Divisor.toQDivisor K')))
    (P : MMP.Mori.PrimeDivisor U') (hP : 2 ≤ Order.coheight (g P.genericPoint)) : False := by
  haveI := hUn.1
  haveI : LocallyOfFiniteType sU := hUn.1.toLocallyOfFiniteType
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace sU
  haveI : IsSeparated sU := hUn.1.toIsSeparated
  haveI : QuasiCompact sU := hUn.1.toQuasiCompact
  haveI : LocallyOfFiniteType (g ≫ sU) := hU'n.1.toLocallyOfFiniteType
  haveI : QuasiCompact (g ≫ sU) := hU'n.1.toQuasiCompact
  haveI : AlgebraicGeometry.IsVariety ℂ (g ≫ sU) := hU'n.1
  haveI : IsDominant g := hgb.isDominant
  -- a canonical divisor of `U` with `K_U` `ℚ`-Cartier
  obtain ⟨-, n₁, K₁, hK₁, hK₁q⟩ := hU.1.1.isPair
  have hn : n₁ = n := by
    have h1 := hK₁.topologicalKrullDim_eq
    have h2 := hK'.topologicalKrullDim_eq
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sU (g ≫ sU) hgb, h2] at h1
    exact_mod_cast h1.symm
  subst hn
  set K : Divisor U := RationalMap.transformDivisor (X := U') g.toRationalMap K' with hKdef
  have hK : Divisor.IsCanonicalDivisor sU n₁ K :=
    MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hUn hU'n hgb hK₁ hK'
  have hKq : (Divisor.toQDivisor K + 0).IsQCartier :=
    (QDivisor.isQCartier_add_iff_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sU hUn hK₁ hK)).mp hK₁q
  have hB₀ := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g
    (Divisor.toQDivisor K + 0)
  obtain ⟨R, hR, -⟩ := hKq.existsUnique_isPullback hB₀
  set BQ : QDivisor U' := R - Divisor.toQDivisor K' with hBQ
  -- `g_* B = 0`
  have hpush : RationalMap.transformDivisor (X := U') g.toRationalMap BQ = 0 := by
    rw [hBQ, map_sub, MMP.Positivity.transformDivisor_of_isPullback hUn hU'n hgb hKq hB₀ hR,
      transformDivisor_toQDivisor, ← hKdef, add_zero, sub_self]
  have hBG : ∀ P' : MMP.Mori.PrimeDivisor U', ¬ MMP.Flips.IsExceptionalPrimeDivisor sU g P' →
      0 ≤ (QDivisor.toRDivisor BQ).coeff P' := fun P' hP' => by
    rw [QDivisor.coeff_toRDivisor]
    exact_mod_cast MMP.Fourfold.Oai4C1.Negativity.coeff_nonneg_of_not_isExceptionalPrimeDivisor
      hUn g hU'n hgb (by rw [hpush]; intro E; simp) P' hP'
  -- `-B = K_{U'} - g^* K_U` is `g`-nef
  have hnegR := isRelativelyNef_neg_of_isPullback (sU' := g ≫ sU) g rfl hKq hR
  have hnef' : MMP.Flips.IsRelativelyNef ℂ (g ≫ sU) g (-(QDivisor.toRDivisor BQ)) := by
    have := isRelativelyNef_add (g ≫ sU) hnef hnegR
    convert this using 1
    rw [hBQ, map_sub]
    abel
  have heff := MMP.Fourfold.Oai4C1.Negativity.isEffective_of_isRelativelyNef_neg ℂ sU (g ≫ sU)
    hUn hU'n g rfl hgb hnef' hBG
  have hPnn : 0 ≤ (QDivisor.toRDivisor BQ).coeff P := heff P
  -- terminality: `a(P; U, 0) = 1 + coeff_P (K_{U'} - g^* K_U) > 1`
  haveI := isSeparated_toTerminal hUn.1.toIsSeparated
  have hlog := isLogDiscrepancy_of_isPullback hUn hK hKq hgb hU'n hK' rfl hR P
  have hex : (⟨U', g, hU'n, hgb, P⟩ : DivisorOver ℂ sU).IsExceptional :=
    (isExceptional_iff_two_le_coheight _).mpr hP
  have h1 := hU.2 n₁ _ _ hex hlog
  rw [QDivisor.coeff_toRDivisor, hBQ, DivisorWithCoeffs.coeff_sub] at hPnn
  have h2 : ((Divisor.toQDivisor K').coeff P : ℝ) = (K' P : ℝ) := by
    rw [Divisor.coeff_toQDivisor]; push_cast; rfl
  rw [Rat.cast_sub, h2] at hPnn
  change 0 ≤ ((R P : ℚ) : ℝ) - _ at hPnn
  linarith

/-- **A `K`-nef model of a terminal variety is small.** Let `g : U' ⟶ U` be a proper birational
morphism of normal complex varieties with `(U, 0)` terminal and a canonical divisor `K_{U'}` nef
over `U`. Then the exceptional set of `g` has codimension at least two: a point of `Ex(g)` maps to
a point of coheight at least two, so it is neither the generic point of `U'` nor, by
`false_of_two_le_coheight`, the generic point of a prime divisor. -/
private theorem two_le_closedsCodimension_exceptionalSet {U U' : Scheme.{0}} [IsIntegral U]
    [IsLocallyNoetherian U] [IsNormal U] [IsIntegral U'] [IsLocallyNoetherian U'] [IsNormal U']
    [CompactSpace U'] {sU : U ⟶ Spec (.of ℂ)} (hU : IsTerminalVariety sU)
    (hUn : IsNormalVariety ℂ sU) (g : U' ⟶ U) (hU'n : IsNormalVariety ℂ (g ≫ sU)) [IsProper g]
    (hgb : IsBirationalMorphism g) {K' : Divisor U'} {n : ℕ}
    (hK' : K'.IsCanonicalDivisor (g ≫ sU) n)
    (hnef : MMP.Flips.IsRelativelyNef ℂ (g ≫ sU) g
      (QDivisor.toRDivisor (Divisor.toQDivisor K'))) :
    2 ≤ closedsCodimension (exceptionalSet g) := by
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  have h2 := two_le_coheight_map_of_mem_exceptionalSet hUn.1 g hU'n.1 hgb hx
  by_contra hlt
  have hle : Order.coheight x ≤ 1 := by
    contrapose! hlt
    exact Order.add_one_le_of_lt hlt
  rcases hle.lt_or_eq with h0 | h1
  · have hx0 : x = genericPoint U' := by
      have hmax : IsMax x := Order.coheight_eq_zero.mp (ENat.lt_one_iff_eq_zero.mp h0)
      exact (Specializes.antisymm (hmax (genericPoint_specializes x))
        (genericPoint_specializes x)).eq
    haveI : IsDominant g := hgb.isDominant
    rw [hx0, MMP.Positivity.map_genericPoint_eq_of_isDominant g,
      Order.coheight_eq_zero.mpr fun z _ => genericPoint_specializes z] at h2
    exact absurd h2 (by decide)
  · exact false_of_two_le_coheight hU hUn g hU'n hgb hK' hnef
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1)
      (by
        rw [show MMP.Mori.PrimeDivisor.genericPoint
            (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x h1) = x from
          AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x h1]
        exact h2)

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_restrictOpen {Y : Scheme.{0}} {s : Y ⟶ Spec (.of ℂ)}
    (h : IsNormalVariety ℂ s) (V : Y.Opens) [Nonempty V] : IsNormalVariety ℂ (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- A morphism `g : O ⟶ U` with `g ≫ ι = (O ⟶ W) ≫ μ`, for an open immersion `ι` and a
birational `μ`, from a nonempty open `O ⊆ W`, is birational. -/
private theorem isBirationalMorphism_of_comp_eq_ι {U Ub W : Scheme.{0}} [IsIntegral U]
    [IsIntegral W] (ι : U ⟶ Ub) [IsOpenImmersion ι] {μ : W ⟶ Ub}
    (hμb : IsBirationalMorphism μ) (O : W.Opens) [Nonempty O] {g : O.toScheme ⟶ U}
    (hg : g ≫ ι = O.ι ≫ μ) : IsBirationalMorphism g := by
  obtain ⟨Wμ, hWμ, hWμo⟩ :=
    MMP.Fourfold.Oai4C1.CommonModel.exists_isOpenImmersion_of_isBirationalMorphism hμb
  let S : O.toScheme.Opens := O.ι ⁻¹ᵁ Wμ
  have hSne : (S : Set O.toScheme).Nonempty := by
    obtain ⟨w, hwO, hwW⟩ := hWμ.inter_open_nonempty _ O.isOpen
      ⟨_, (Classical.arbitrary O).2⟩
    exact ⟨⟨w, hwO⟩, hwW⟩
  have hrange : Set.range (S.ι ≫ O.ι) ⊆ Set.range Wμ.ι := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hcomp : (S.ι ≫ g) ≫ ι = IsOpenImmersion.lift Wμ.ι (S.ι ≫ O.ι) hrange ≫ Wμ.ι ≫ μ := by
    rw [Category.assoc, hg, IsOpenImmersion.lift_fac_assoc, Category.assoc]
  haveI : IsOpenImmersion ((S.ι ≫ g) ≫ ι) := by rw [hcomp]; infer_instance
  haveI : IsOpenImmersion (S.ι ≫ g) := IsOpenImmersion.of_comp (S.ι ≫ g) ι
  haveI : IsDominant g := by
    refine ⟨?_⟩
    have h1 : Set.range (S.ι ≫ g) ⊆ Set.range g := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact Set.image_subset_range _ _
    exact Dense.mono h1 ((S.ι ≫ g).isOpenEmbedding.isOpen_range.dense
      (Set.range_nonempty_iff_nonempty.mpr hSne.to_subtype))
  exact MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isOpenImmersion g S
    (S.isOpen.dense hSne)

/-- A nonempty open subscheme of a `ℚ`-factorial variety is `ℚ`-factorial. -/
private theorem isQFactorial_restrictOpen {W : Scheme.{0}} [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of ℂ)}
    (hWQ : IsQFactorial sW) (O : W.Opens) [Nonempty O] : IsQFactorial (O.ι ≫ sW) := by
  have hOv : IsNormalVariety ℂ (O.ι ≫ sW) := isNormalVariety_restrictOpen hWQ.1 O
  haveI : IsDominant O.ι := MMP.Fourfold.isDominant_ι_of_nonempty O
  haveI : AlgebraicGeometry.IsVariety ℂ (O.ι ≫ sW) := hOv.1
  haveI : CompactSpace O := QuasiCompact.compactSpace_of_compactSpace (O.ι ≫ sW)
  refine ⟨hOv, fun D => ?_⟩
  obtain ⟨m, hm, hC⟩ := hWQ.2 (Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap O.ι) D)
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant O.ι
    ((m : ℤ) • Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap O.ι) D)
  refine ⟨m, hm, ?_⟩
  convert hC.isCartier_pullback O.ι hB using 1
  refine Finsupp.ext fun P => ?_
  have := coeff_pullback_ι O hC hB P
  rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at this
  rw [this, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective O.ι)]

/-- The restriction `g : μ⁻¹(U) ⟶ U` of the terminal model over the compactification is a
projective small birational morphism from a `ℚ`-factorial terminal threefold. -/
private theorem exists_restriction {U Ub W : Scheme.{0}}
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)}
    (hU : IsTerminalVariety sU) (hUn : IsNormalVariety ℂ sU) (hdim : topologicalKrullDim U = 3)
    {sUb : Ub ⟶ Spec (.of ℂ)} (ι : U ⟶ Ub) [IsOpenImmersion ι] (hιs : ι ≫ sUb = sU)
    [IsIntegral W] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    {sW : W ⟶ Spec (.of ℂ)} {μ : W ⟶ Ub}
    (hWQ : IsQFactorial sW) (hWp : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hWd : topologicalKrullDim W = 3) (hWt : IsTerminalVariety sW) (hμs : μ ≫ sUb = sW)
    (hμb : IsBirationalMorphism μ) (hμp : IsProjectiveMorphism μ)
    {KW : Divisor W} {mW : ℕ} (hKW : KW.IsCanonicalDivisor sW mW)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sW μ (QDivisor.toRDivisor (Divisor.toQDivisor KW))) :
    ∃ (U' : Scheme.{0}) (_ : IsIntegral U') (_ : IsLocallyNoetherian U') (_ : IsNormal U')
      (sU' : U' ⟶ Spec (.of ℂ)) (g : U' ⟶ U),
      IsProjectiveMorphism g ∧ IsSmallMorphism sU' sU g ∧ IsQFactorial sU' ∧
        IsTerminalVariety sU' := by
  classical
  set V : Ub.Opens := ι.opensRange
  let e : U ≅ V := ι.isoOpensRange
  have he : e.hom ≫ V.ι = ι := Scheme.Hom.isoOpensRange_hom_ι ι
  set O : W.Opens := μ ⁻¹ᵁ V
  haveI : IsProper μ := isProper_of_isProjectiveMorphism μ hμp
  haveI : IsDominant μ := hμb.isDominant
  have hsurj : Function.Surjective μ := by
    rw [← Set.range_eq_univ, ← μ.isClosedMap.isClosed_range.closure_eq]
    exact μ.denseRange.closure_eq
  haveI hOne : Nonempty O := by
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    obtain ⟨w, hw⟩ := hsurj (ι u)
    exact ⟨⟨w, show μ w ∈ V by rw [hw]; exact ⟨u, rfl⟩⟩⟩
  have hWn : IsNormalVariety ℂ sW := hWQ.1
  have hOv : IsNormalVariety ℂ (O.ι ≫ sW) := isNormalVariety_restrictOpen hWn O
  let g : O.toScheme ⟶ U := (μ ∣_ V) ≫ e.inv
  have hg : g ≫ ι = O.ι ≫ μ := by
    simp only [g, ← he, Category.assoc, Iso.inv_hom_id_assoc, morphismRestrict_ι]
    rfl
  have hgs : g ≫ sU = O.ι ≫ sW := by
    rw [← hιs, ← Category.assoc, hg, Category.assoc, hμs]
  have hgp : IsProjectiveMorphism g :=
    (hμp.restrict V).of_iso (Iso.refl _) e.symm (by simp [g])
  haveI : IsProper g := isProper_of_isProjectiveMorphism g hgp
  have hgb := isBirationalMorphism_of_comp_eq_ι ι hμb O hg
  have hOt : IsTerminalVariety (O.ι ≫ sW) := (hWt.comp_etale O.ι hOv).1
  haveI : IsDominant O.ι := MMP.Fourfold.isDominant_ι_of_nonempty O
  haveI : AlgebraicGeometry.IsVariety ℂ (O.ι ≫ sW) := hOv.1
  haveI : CompactSpace O := QuasiCompact.compactSpace_of_compactSpace (O.ι ≫ sW)
  have hOQ := isQFactorial_restrictOpen hWQ O
  have hsmall : 2 ≤ closedsCodimension (exceptionalSet g) := by
    haveI : IsSeparated sW := hWn.1.toIsSeparated
    haveI : QuasiCompact sW := hWn.1.toQuasiCompact
    obtain ⟨-, hK'⟩ := hWt.comp_etale O.ι hOv
    obtain ⟨hq, K', hK'c, hK'p, -⟩ := hK' mW KW hKW
    have hKWq : (Divisor.toQDivisor KW).IsQCartier :=
      MMP.Fourfold.isQCartier_of_isQFactorial sW hWQ _
    have hcoeff : ∀ P, (QDivisor.toRDivisor (Divisor.toQDivisor K')).coeff P =
        (QDivisor.toRDivisor (Divisor.toQDivisor KW)).coeff
          (OpenWeilRestriction.primeDivisorMap O.ι P) := by
      intro P
      rw [QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
      haveI : IsIso (O.ι.stalkMap P.genericPoint) :=
        inferInstanceAs <| IsIso (O.ι.toLRSHom.stalkMap P.genericPoint)
      exact congrArg _ (MMP.Fourfold.coeff_eq_of_isPullback_qDivisor P _
        (OpenWeilRestriction.genericPoint_primeDivisorMap O.ι P).symm hKWq hK'p)
    have hnefO := isRelativelyNef_restrict O hg hnef hcoeff
    have hgsv : IsNormalVariety ℂ (g ≫ sU) := hgs ▸ hOv
    exact two_le_closedsCodimension_exceptionalSet hU hUn g hgsv hgb (K' := K') (n := mW)
      (by rw [hgs]; exact hK'c) (by rw [hgs]; exact hnefO)
  exact ⟨O, inferInstance, inferInstance, inferInstance, O.ι ≫ sW, g, hgp,
    ⟨hOv, hUn, hgs, inferInstance, hgb, hsmall⟩, hOQ, hOt⟩

private theorem solution : ∀ {U : Scheme.{0}}
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)}
    (hU : IsTerminalVariety sU) (hUn : IsNormalVariety ℂ sU)
    (hUq : IsQuasiProjectiveVariety ℂ sU) (hdim : topologicalKrullDim U = 3),
    ∃ (U' : Scheme.{0}) (_ : IsIntegral U') (_ : IsLocallyNoetherian U') (_ : IsNormal U')
      (sU' : U' ⟶ Spec (.of ℂ)) (g : U' ⟶ U),
      IsProjectiveMorphism g ∧ IsSmallMorphism sU' sU g ∧ IsQFactorial sU' ∧
        IsTerminalVariety sU' := by
  intro U _ _ _ sU hU hUn hUq hdim
  obtain ⟨Ub, _, _, _, _, sUb, ι, hι, hιs, hUbp, hUbn⟩ :=
    exists_normal_projective_compactification hUn hUq
  have hdimUb : topologicalKrullDim Ub = 3 := by
    haveI : LocallyOfFiniteType sUb :=
      ((MMP.Mori.isProjectiveVariety_iff _ _).mp hUbp).1.toLocallyOfFiniteType
    rw [← topologicalKrullDim_eq_of_isOpenImmersion sUb ι, hdim]
  obtain ⟨W₀, _, _, _, _, sW₀, μ₀, hW₀t, hW₀Q, hW₀p, hW₀d, hμ₀s, hμ₀b⟩ :=
    exists_terminal_resolution hUbp hUbn hdimUb
  obtain ⟨W, _, _, _, _, sW, μ, hWQ, hWp, hWd, hWt, hμs, hμb, hμp, KW, mW, hKW, hnef⟩ :=
    exists_relativelyNef_terminal_model hW₀t hW₀Q hW₀p hW₀d hUbp hμ₀s hμ₀b
  exact exists_restriction hU hUn hdim ι hιs hWQ hWp hWd hWt hμs hμb hμp hKW hnef

end Proof_lem_mmp_indexb_small_q_factorialization

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Small `ℚ`-factorialization.** Let `U` be a normal quasi-projective complex threefold with
`(U, 0)` terminal. Then there is a projective small birational morphism `g : U' ⟶ U` over `ℂ`
with `U'` `ℚ`-factorial and `(U', 0)` terminal. -/
@[mmp "lem_mmp_indexb_small_q_factorialization"]
public theorem IsTerminalVariety.exists_isSmallMorphism_isQFactorial {U : Scheme.{0}}
    [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of ℂ)}
    (hU : IsTerminalVariety sU) (hUn : IsNormalVariety ℂ sU)
    (hUq : IsQuasiProjectiveVariety ℂ sU) (hdim : topologicalKrullDim U = 3) :
    ∃ (U' : Scheme.{0}) (_ : IsIntegral U') (_ : IsLocallyNoetherian U') (_ : IsNormal U')
      (sU' : U' ⟶ Spec (.of ℂ)) (g : U' ⟶ U),
      IsProjectiveMorphism g ∧ IsSmallMorphism sU' sU g ∧ IsQFactorial sU' ∧
        IsTerminalVariety sU' :=
  Proof_lem_mmp_indexb_small_q_factorialization.solution hU hUn hUq hdim

end MMP.Fourfold
