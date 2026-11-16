module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CanonicalDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.MinimalModel.RadialNefInterval
import MMP.AlgebraicGeometry.MMP.Threefold.RadialPerturbationNullRays
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalWithNefWeakModel
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
import StacksFrontier.AlgebraicGeometry.FiniteMorphismProjective.Projective
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
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
import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.SupComapSubscheme
import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
import StacksFrontier.AlgebraicGeometry.MeromorphicConstant.OrderUnit
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
import StacksFrontier.AlgebraicGeometry.Flatness.FiniteFlatLocallyFree
import StacksFrontier.AlgebraicGeometry.Flatness.FlatQuotientPullbackMono
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
import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernCompositionCartier
import StacksFrontier.AlgebraicGeometry.Spaces.SchemeModuleBridge.StrictTransformChart
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceAlgebraization
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.PresentationTwistIso
import StacksFrontier.AlgebraicGeometry.NodalContraction.SmoothAt
import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdealChart
import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorizationGlue
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.TwistTrivial
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine
import StacksFrontier.AlgebraicGeometry.Curves.GenusZeroPositiveDegree.PlaneConic
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyAffineHom
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyNoetherianRegular
import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.HomogeneousIdealSheaf
import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BlowupExcessConormal
import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.AcyclicCycles
import StacksFrontier.AlgebraicGeometry.Recovery27.Presentation
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme
import StacksFrontier.Topology.Dimension.MaximalPointDrop
import StacksFrontier.AlgebraicGeometry.Modules.ExactOnAffineOpens
import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Smooth
import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Proper
import StacksFrontier.RingTheory.GradedAlgebra.KrullDimension
import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.AffineCone
import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.StalkKoszulCriterion
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearMapExactness
import StacksFrontier.AlgebraicGeometry.Cube.GeometricallyIntegralProduct
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumTwistComparison
import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationProperProjective
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSection
import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheafLinear
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
import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechFractionBaseChange
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.Modules.MonoRestrictLocality
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusColimitStalk
import StacksFrontier.AlgebraicGeometry.FlatBaseChange.GlobalGeneration
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionStalk
import StacksFrontier.Topology.Dimension.UnionDimension
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroUnconditional
import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.LinearEquations.ChartKernel
import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso
import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtRestrictExtension
import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible
import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Singularities.LogResolution.Basic
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Morphisms.ChowLemma
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Morphisms.GenericFlatnessFiberDimension
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefAdjointTargets
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTrace
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Resolution.StrongResolution.QuasiProjective
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.Intersection.SmallModificationPicardNumber
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Intersection.CurveClassesFiniteDim
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Singularities.AmpleFloorLowering
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
import MMP.AlgebraicGeometry.Positivity.Kleiman.RhoOneCurveTest
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
import MMP.AlgebraicGeometry.MMP.Flip.RealCanonicalRationalWitness
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Surface.ContractionChainBound
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.MMP.Flip.DivisorNormalizationLift
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonEquality
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy

/-!
# Transferring a radial nef interval to a given weak model

Let `Y` be a projective `ℚ`-factorial complex threefold over a projective complex variety `S`
(by `π_Y`), with canonical divisor `K_Y`, and let `(Y, B)` and `(Y, C)` be real terminal pairs
with `D = K_Y + B` nef over `S`. Fix rational null-decomposition data for `B`, with weights `rᵢ`
and Cartier index `m`; its intersection gap `τ > 0` depends only on the `rᵢ` and `m`, and put
`ε = τ / (2 (τ + 6))`. For `C_t = (1 - t) B + t C` with `0 < t < ε`, suppose `(Y, C_t)` has a
`ℚ`-factorial nef weak model `φ : Y ⤏ Z` whose comparison divisor
`p^*(K_Y + C_t) - q^*(K_Z + φ_* C_t)` has coefficient zero at the strict transform of every
positive component of `C_t`. Then for every `0 < s < ε` the same `φ` is a nef weak model of
`(Y, C_s)`, with the same vanishing of comparison coefficients along the positive components of
`C_s`, and the nef models `(Z, φ_* C_s)`, `0 < s < ε`, are pairwise equivalent through the
identity of `Z`.

## Main results

* `MMP.Fourfold.exists_pos_forall_isNefWeakModel_of_isNefWeakModel`.

## Implementation notes

* As in `MMP.Fourfold.exists_pos_forall_isRelativelyNef_of_isRelativelyNef`, the gap `τ`
  depends on the data only through the weights and `m`: it is produced as a positive function
  of `(s, r, m)` before the threefold is given, the gap of data `ν` being `τ ν.s ν.weight ν.m`.
* The comparison coefficient at a prime `P` of `Y` is the coefficient of
  `p^*(K_Y + C) - q^*(K_Z + φ_* C)` at the strict transform of `P` on a common projective
  resolution `p : W ⟶ Y`, `q : W ⟶ Z` of the kind in `MMP.Fourfold.IsNefWeakModel`; the
  hypothesis asks for one such resolution, and the conclusion provides one for each `s`.
* Equivalence is asserted for every pair of parameters `0 < s, s' < ε` (which contains the
  equivalence with the given model at `t`), the birational map being the identity of `Z`.

## References

* [OAI4] the fourfold source, *Transferring a radial nef interval to the given weak model*.
-/

@[expose] public section

universe u

section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP.Mori MMP.Flips MMP.Fourfold

namespace Proof_lem_fourfold_radial_weak_model_interval

/-! ### Rational maps, models and pull-backs -/

namespace Crepant

/-! ### Generalities on points and partial maps -/

section Generalities

/-- A morphism of irreducible schemes sending the generic point to the generic point is
dominant. -/
private theorem isDominant_of_apply_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace Y] (f : X ⟶ Y) (h : f (genericPoint X) = genericPoint Y) :
    IsDominant f := by
  rw [isDominant_iff]
  intro y
  have hy : y ∈ closure ({genericPoint Y} : Set Y) := by
    rw [(genericPoint_spec Y).def]; trivial
  have hmem : genericPoint Y ∈ Set.range (f : X → Y) := ⟨genericPoint X, h⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem) hy

/-- The local ring of a normal locally noetherian integral scheme at a point of coheight at most
one is a valuation ring (a field or a discrete valuation ring). -/
private theorem valuationRing_stalk_of_coheight_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {x : X} (hx : Order.coheight x ≤ 1) :
    ValuationRing (X.presheaf.stalk x) := by
  rcases lt_or_eq_of_le hx with h | h
  · have hmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp h)
    have hgen : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    have hx' : x ⤳ genericPoint X := hmax (show x ≤ genericPoint X from hgen)
    have hgx : genericPoint X = x := (hgen.antisymm hx').eq
    subst hgx
    have : IsField (X.presheaf.stalk (genericPoint X)) := Field.toIsField X.functionField
    letI := this.toField
    infer_instance
  · have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, h]; rfl
    have h5 : IsNoetherianRing (X.presheaf.stalk x) ∧ IsLocalRing (X.presheaf.stalk x) ∧
        IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) ∧
        ringKrullDim (X.presheaf.stalk x) = 1 :=
      ⟨inferInstance, inferInstance, inferInstance, IsNormal.stalk_normal x, hdim⟩
    have h1 : ∃ _ : IsDomain (X.presheaf.stalk x), IsDiscreteValuationRing (X.presheaf.stalk x) :=
      ((isDiscreteValuationRing_tfae (X.presheaf.stalk x)).out 5 1).mp h5
    have := h1.choose_spec
    infer_instance

/-- **The point over a codimension-one point.** Let `f : X ⟶ Y` be a separated dominant morphism
of normal integral schemes inducing an isomorphism of function fields, and `y ∈ Y` a point of
coheight at most one. Then `f` induces an isomorphism of local rings at every point over `y`, and
two points over `y` coincide. -/
private theorem isIso_stalkMap_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {x : X} (hx : Order.coheight (f x) ≤ 1) :
    IsIso (f.stalkMap x) := by
  have := valuationRing_stalk_of_coheight_le_one hx
  exact MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x

private theorem eq_of_apply_eq_of_coheight_le_one {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsSeparated f]
    [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) {x₁ x₂ : X}
    (h : f x₂ = f x₁) (hx : Order.coheight (f x₁) ≤ 1) : x₁ = x₂ := by
  have := valuationRing_stalk_of_coheight_le_one hx
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf x₁
  have : IsIso (f.stalkMap x₂) :=
    isIso_stalkMap_of_coheight_le_one f hf (by rw [h]; exact hx)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hf h

/-- The coheight of the generic point of a prime divisor is at most one. -/
private theorem coheight_genericPoint_le_one {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight P.genericPoint ≤ 1 :=
  P.coheight_genericPoint.le

/-- The coheight of the generic point is zero, hence at most one. -/
private theorem coheight_genericPoint_scheme_le_one (X : Scheme.{u}) [IrreducibleSpace X] :
    Order.coheight (genericPoint X) ≤ 1 := by
  have : IsMax (genericPoint X) := fun y _ =>
    (genericPoint_spec X).specializes (Set.mem_univ y)
  rw [Order.coheight_eq_zero.mpr this]
  exact zero_le_one

/-- Two partial maps with the same domain representing the same rational map to a separated
scheme are equal. -/
private theorem hom_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) {f g : U.toScheme ⟶ Y}
    (h : (⟨U, hU, f⟩ : X.PartialMap Y).toRationalMap =
      (⟨U, hU, g⟩ : X.PartialMap Y).toRationalMap) :
    f = g := by
  have := (Scheme.PartialMap.equiv_iff_of_domain_eq_of_isSeparated (S := ⊤_ Scheme)
    (f := ⟨U, hU, f⟩) (g := ⟨U, hU, g⟩) rfl).mp (Scheme.PartialMap.toRationalMap_eq_iff.mp h)
  injection this

/-- The partial map given by the restriction of `g` to `U`, composed with `q`, represents
`g ∘ q`. -/
private theorem toRationalMap_restrict_comp {X Y Z : Scheme.{u}} (g : X.PartialMap Y)
    {U : X.Opens} (hU : Dense (U : Set X)) (hle : U ≤ g.domain) (q : Y ⟶ Z) :
    (⟨U, hU, (g.restrict U hU hle).hom ≫ q⟩ : X.PartialMap Z).toRationalMap =
      g.toRationalMap.compHom q := by
  rw [← Scheme.PartialMap.restrict_toRationalMap g U hU hle,
    ← Scheme.RationalMap.compHom_toRationalMap]
  rfl

/-- The partial map given by the inclusion of a dense open `U`, composed with `q`, represents
`q`. -/
private theorem toRationalMap_ι_comp {X Z : Scheme.{u}} {U : X.Opens} (hU : Dense (U : Set X))
    (q : X ⟶ Z) :
    (⟨U, hU, U.ι ≫ q⟩ : X.PartialMap Z).toRationalMap = q.toRationalMap := by
  change _ = q.toPartialMap.toRationalMap
  rw [← Scheme.PartialMap.restrict_toRationalMap q.toPartialMap U hU le_top]
  congr 1
  refine Scheme.PartialMap.ext _ _ rfl ?_
  change U.ι ≫ q = (X.isoOfEq rfl).hom ≫ (X.homOfLE (le_top : U ≤ ⊤) ≫ X.topIso.hom ≫ q)
  simp [Scheme.topIso_hom]

/-- Two representatives, restricted to a common dense open `U` and composed with morphisms to a
separated scheme, agree on `U` when the composite rational maps agree. -/
private theorem comp_eq_comp_of_compHom_eq {X Y₁ Y₂ Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) (g₁ : X.PartialMap Y₁)
    (g₂ : X.PartialMap Y₂) (h₁ : U ≤ g₁.domain) (h₂ : U ≤ g₂.domain) (q₁ : Y₁ ⟶ Z)
    (q₂ : Y₂ ⟶ Z) (h : g₁.toRationalMap.compHom q₁ = g₂.toRationalMap.compHom q₂) :
    (X.homOfLE h₁ ≫ g₁.hom) ≫ q₁ = (X.homOfLE h₂ ≫ g₂.hom) ≫ q₂ :=
  hom_eq_of_toRationalMap_eq hU ((toRationalMap_restrict_comp g₁ hU h₁ q₁).trans
    (h.trans (toRationalMap_restrict_comp g₂ hU h₂ q₂).symm))

/-- A representative restricted to a dense open `U` and composed with a morphism agrees on `U`
with a morphism `r` when the composite rational map is `r`. -/
private theorem comp_eq_ι_comp_of_compHom_eq {X Y Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] {U : X.Opens} (hU : Dense (U : Set X)) (g : X.PartialMap Y)
    (h₁ : U ≤ g.domain) (q : Y ⟶ Z) (r : X ⟶ Z)
    (h : g.toRationalMap.compHom q = r.toRationalMap) :
    (X.homOfLE h₁ ≫ g.hom) ≫ q = U.ι ≫ r :=
  hom_eq_of_toRationalMap_eq hU ((toRationalMap_restrict_comp g hU h₁ q).trans
    (h.trans (toRationalMap_ι_comp hU r).symm))

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `h` is an inverse of the morphism `p`, then `p ∘ h` is the identity. -/
private theorem compHom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] {p : Y ⟶ X} {h : X.RationalMap Y}
    (hinv : RationalMap.IsInverse p.toRationalMap h) :
    h.compHom p = Scheme.Hom.toRationalMap (𝟙 X) := by
  obtain ⟨e, he1, he2⟩ := id hinv
  rw [← he2, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff,
    Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
  change e.iso.inv ≫ e.source.ι ≫ p = e.target.ι ≫ 𝟙 X
  rw [source_ι_comp_eq_of_toRationalMap_eq p e he1, Iso.inv_hom_id_assoc, Category.comp_id]

/-- A morphism whose composite with `s` is a given separated morphism is separated. -/
private theorem isSeparated_of_comp_eq {X Y T : Scheme.{u}} {f : X ⟶ Y} {s : Y ⟶ T}
    {t : X ⟶ T} (h : f ≫ s = t) [IsSeparated t] : IsSeparated f := by
  subst h
  exact IsSeparated.of_comp f s

/-- **Cancelling a local isomorphism at a codimension-one point.** If `f ≫ g` induces an
isomorphism of local rings at `x`, and `g` is a separated dominant morphism of normal integral
schemes inducing an isomorphism of function fields with `f x` over a point of coheight at most
one, then `f` induces an isomorphism of local rings at `x`. -/
private theorem isIso_stalkMap_of_isIso_comp {X Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant g]
    (hg : Function.Bijective (functionFieldMap g)) (x : X) [h : IsIso ((f ≫ g).stalkMap x)]
    (hx : Order.coheight (g (f x)) ≤ 1) : IsIso (f.stalkMap x) := by
  have := isIso_stalkMap_of_coheight_le_one g hg hx
  rw [Scheme.Hom.stalkMap_comp] at h
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (g.stalkMap (f x)) (f.stalkMap x) this h

end Generalities

/-! ### Transforms of prime divisors -/

section Transforms

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ,
    TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- A representative of `φ` defined at `η_Q` sends `η_Q` to `η_P` when `φ_* Q = P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

end Transforms

/-! ### Pull-backs along composites -/

section Pullback

private theorem mem_irreducibleComponent' {T : Type*} [TopologicalSpace T] [IrreducibleSpace T]
    (W : irreducibleComponents T) (t : T) : t ∈ W.1 := by
  rw [W.2.eq_of_le (IrreducibleSpace.isIrreducible_univ T) (Set.subset_univ _)]
  trivial

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (g ≫ f)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral X] [IsLocallyNoetherian Z] [IsNormal Z]
    {f : Y ⟶ X} {g : Z ⟶ Y} {L : Divisor X} {L' : Divisor Y}
    {L'' : Divisor Z} {hB : ∀ W : irreducibleComponents Y, f (componentGenericPoint Y W) ∉ L.supp}
    {hB' : ∀ W : irreducibleComponents Z, g (componentGenericPoint Z W) ∉ L'.supp}
    (h : L.IsPullback f hB L') (h' : L'.IsPullback g hB' L'')
    (hB'' : ∀ W : irreducibleComponents Z, (g ≫ f) (componentGenericPoint Z W) ∉ L.supp) :
    L.IsPullback (g ≫ f) hB'' L'' := by
  intro U φ hφ E hE
  have hψ := h.isLocalEquation hφ
  rw [h' (f ⁻¹ᵁ U) _ hψ E hE]
  congr 1
  set z := componentGenericPoint Z E.component
  have hzU : f (g z) ∈ U := E.map_componentGenericPoint_mem (g ≫ f) hE
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _) (mem_irreducibleComponent'
    (pointComponent ((g ≫ f) z)) _)
  rw [pullbackComponent_eq hB'' hφ hzU _ a ha]
  set W := pointComponent (g z)
  have hspec : componentGenericPoint Y W ⤳ g z :=
    (isGenericPoint_componentGenericPoint Y W).specializes (mem_pointComponent _)
  have hWU : f (componentGenericPoint Y W) ∈ U :=
    (f.base.hom.map_specializes hspec).mem_open U.isOpen hzU
  have hb : (stalkToRationalFunctions Y (mem_pointComponent (g z))).hom
      (Units.map (f.stalkMap (g z)).hom.toMonoidHom a) =
      ((pullbackLocalEquation f hB hφ : (RationalFunctions Y)ˣ) : RationalFunctions Y) W := by
    have e1 := congrArg Units.val (pullbackLocalEquation_apply f hB hφ W hWU)
    refine Eq.trans ?_ e1.symm
    rw [pullbackComponent_eq hB hφ hWU
      (mem_irreducibleComponent' (pointComponent ((g ≫ f) z)) _)
      (Units.map (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom.toMonoidHom a)
      ?_]
    · change (stalkToRationalFunctions Y _).hom ((f.stalkMap (g z)).hom a.val) =
        (f.stalkMap _).hom ((X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec)).hom
          a.val)
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkToRationalFunctions,
        Scheme.Hom.stalkSpecializes_stalkMap]
    · change (X.presheaf.stalkSpecializes (f.base.hom.map_specializes hspec) ≫
        X.presheaf.stalkSpecializes _).hom a.val = _
      rw [TopCat.Presheaf.stalkSpecializes_comp]
      exact ha
  rw [pullbackComponent_eq hB' hψ _ (mem_pointComponent (g z)) _ hb]
  ext
  change _ = ((g ≫ f).stalkMap z).hom a.val
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- **Pulling a pull-back back once more.** Let `g^*M = D` be an `ℝ`-Cartier pull-back and
`f : V ⟶ W` dominant from a quasi-compact normal integral scheme. Then `M` has a pull-back `G`
along `f ≫ g` whose coefficient along a prime divisor `E` of `V` dominating a prime divisor `P` of
`W` with an isomorphism of local rings is the coefficient of `D` along `P`. -/
private theorem exists_isRCartierPullback_comp {V W Z : Scheme.{u}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (f : V ⟶ W) [IsDominant f]
    (g : W ⟶ Z) [IsDominant g] {M : RDivisor Z} {D : RDivisor W}
    (hD : MMP.Flips.IsRCartierPullback g M D) :
    ∃ G : RDivisor V, MMP.Flips.IsRCartierPullback (f ≫ g) M G ∧
      ∀ (E : MMP.Mori.PrimeDivisor V) (P : MMP.Mori.PrimeDivisor W),
        f E.genericPoint = P.genericPoint → IsIso (f.stalkMap E.genericPoint) →
          G.coeff E = D.coeff P := by
  obtain ⟨m, r, L, L', hLc, hM, hpb, rfl⟩ := hD
  have hL'c : ∀ j, (L' j).IsCartier := fun j => ((hpb j).2).isCartier (hLc j)
  let L'' : Fin m → Divisor V := fun j =>
    (L' j).pullback (hL'c j) (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _)
  have hL'' : ∀ j, (L' j).IsPullback f
      (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant f _) (L'' j) :=
    fun j => Divisor.isPullback_pullback (hL'c j) _
  refine ⟨∑ j, r j • Divisor.toRDivisor (L'' j), ⟨m, r, L, L'', hLc, hM, fun j =>
    ⟨MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant (f ≫ g) _,
      isPullback_comp (hpb j).2 (hL'' j) _⟩, rfl⟩, fun E P heq hiso => ?_⟩
  rw [MMP.Flips.coeff_sum_smul_toRDivisor, MMP.Flips.coeff_sum_smul_toRDivisor]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact_mod_cast MMP.Positivity.coeff_eq_of_isPullback E P heq (hL'c j) (hL'' j)

end Pullback

/-! ### Dominance -/

section Dominance

/-- The partial map underlying a partial isomorphism is dominant. -/
private theorem isDominant_toPartialMap_hom {X Y : Scheme.{u}} (e : X.PartialIso Y) :
    IsDominant e.toPartialMap.hom := by
  change IsDominant (e.iso.hom ≫ e.target.ι)
  haveI : IsDominant e.target.ι := Opens.isDominant_ι e.dense_target
  infer_instance

/-- If `a ≫ p` is dominant, with `p` a separated dominant morphism of integral schemes inducing
an isomorphism of function fields onto a normal scheme, then `a` is dominant. -/
private theorem isDominant_of_comp_eq {V W T : Scheme.{u}} [IsIntegral V] [IsIntegral W]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] (a : V ⟶ W) (p : W ⟶ T) [IsSeparated p]
    [IsDominant p] (hp : Function.Bijective (functionFieldMap p)) [IsDominant (a ≫ p)] :
    IsDominant a := by
  refine isDominant_of_apply_genericPoint a ?_
  have h1 : p (a (genericPoint V)) = genericPoint T := by
    rw [← Scheme.Hom.comp_apply]; exact MMP.Positivity.map_genericPoint_eq_of_isDominant (a ≫ p)
  have h2 : p (genericPoint W) = genericPoint T :=
    MMP.Positivity.map_genericPoint_eq_of_isDominant p
  refine (eq_of_apply_eq_of_coheight_le_one p hp (h1.trans h2.symm) ?_).symm
  rw [h2]; exact coheight_genericPoint_scheme_le_one T

end Dominance

/-! ### Composites of rational maps -/

section Composition

/-- **A representative of a composite.** If `f` maps a dense open `O ⊆ dom f` into `dom g`
through `β`, then `g ∘ f` is represented on `O` by `β` followed by `g`. -/
private theorem comp_toRationalMap_eq {X Y Z : Scheme.{u}} [IsIntegral X] [Nonempty Y]
    (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) {O : X.Opens}
    (hO : Dense (O : Set X)) (hOf : O ≤ f.domain) (β : O.toScheme ⟶ g.domain.toScheme)
    (hβ : β ≫ g.domain.ι = X.homOfLE hOf ≫ f.hom) :
    f.toRationalMap.comp g.toRationalMap = (⟨O, hO, β ≫ g.hom⟩ : X.PartialMap Z).toRationalMap := by
  rw [Scheme.RationalMap.toRationalMap_comp, Scheme.PartialMap.toRationalMap_eq_iff]
  have hOc : O ≤ f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain := by
    intro x hx
    let y : O.toScheme := ⟨x, hx⟩
    have h1 : f.hom (X.homOfLE hOf y) = g.domain.ι (β y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hβ]
    refine ⟨X.homOfLE hOf y, ?_, ?_⟩
    · show f.hom (X.homOfLE hOf y) ∈ g.domain
      rw [h1]; exact (β y).2
    · show f.domain.ι (X.homOfLE hOf y) = x
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]; rfl
  have key2 : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      (f.hom ⁻¹ᵁ g.domain).ι = X.homOfLE hOf := by
    rw [← cancel_mono f.domain.ι]
    simp only [Category.assoc]
    rw [← Scheme.Hom.isoImage_hom_ι, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have key : X.homOfLE hOc ≫ (Scheme.Hom.isoImage f.domain.ι (f.hom ⁻¹ᵁ g.domain)).inv ≫
      f.hom ∣_ g.domain = β := by
    rw [← cancel_mono g.domain.ι, hβ, ← key2]
    simp only [Category.assoc, morphismRestrict_ι]
  refine ⟨O, hO, hOc, le_rfl, ?_⟩
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.comp_hom, Scheme.homOfLE_rfl,
    Category.id_comp]
  rw [← key]
  rfl

/-- A partial map which is an open immersion represents a birational map. -/
private theorem isBirational_of_isOpenImmersion {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (c : X.PartialMap Y) [IsOpenImmersion c.hom] [Nonempty c.domain] :
    RationalMap.IsBirational c.toRationalMap := by
  have hd : Dense (c.hom.opensRange : Set Y) :=
    c.hom.opensRange.2.dense ⟨_, Classical.arbitrary c.domain, rfl⟩
  refine ⟨⟨c.domain, c.dense_domain, c.hom.opensRange, hd, c.hom.isoOpensRange⟩, ?_⟩
  change Scheme.PartialMap.toRationalMap
    ⟨c.domain, c.dense_domain, c.hom.isoOpensRange.hom ≫ c.hom.opensRange.ι⟩ = _
  rw [Scheme.Hom.isoOpensRange_hom_ι]

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

end Composition

/-! ### Pull-backs of rational forms along birational morphisms -/

section Forms

variable {k : Type u} [Field k] [PerfectField k]

/-- Along a dominant morphism inducing an isomorphism of function fields, the pull-back of a
nonzero rational form is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X V : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (f : V ⟶ X) [IsIntegral X] [IsIntegral V] [IsDominant f] [LocallyOfFiniteType sX]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  have h1 : pullbackRationalPluriForms sX f τ =
      pullbackFormsAlong (K' := V.functionField) hω m τ := pullbackForms_eq hω m τ
  rw [h1]
  exact smul_ne_zero ((map_ne_zero _).mpr (repr_ne_zero_of_ne_zero _ hτ))
    ((ZTensorPower.basis _ m).ne_zero ())

/-- Along a dominant morphism inducing an isomorphism of function fields, every rational form is
a pull-back. -/
private theorem exists_pullbackRationalPluriForms_eq {X V : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (f : V ⟶ X) [IsIntegral X] [IsIntegral V] [IsDominant f] [LocallyOfFiniteType sX]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    (σ : RationalPluriForms (f ≫ sX) d m) :
    ∃ τ : RationalPluriForms sX d m, pullbackRationalPluriForms sX f τ = σ ∧ (σ ≠ 0 → τ ≠ 0) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let B' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  let B := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hbij.2 (B'.repr σ ())
  refine ⟨c • B (), ?_, fun hσ => smul_ne_zero ?_ (B.ne_zero ())⟩
  swap
  · rintro rfl
    rw [map_zero] at hc
    apply hσ
    have h2 := (B'.sum_repr σ).symm
    simp only [← hc, Finset.univ_unique, Finset.sum_singleton, zero_smul] at h2
    exact h2
  change pullbackForms (K := X.functionField) (K' := V.functionField) m (c • B ()) = σ
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  rw [show B.repr (c • B ()) () = c by simp]
  change functionFieldMap f c • B' () = σ
  rw [hc]
  simpa using B'.sum_repr σ

/-- The order of a rational form does not see a rewriting of the structure morphism. -/
private theorem ordForm_cast {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {s s' : V ⟶ Spec (.of k)}
    (h : s = s') {d : ℕ} {m : ℤ} (τ : RationalPluriForms s d m) (E : MMP.Mori.PrimeDivisor V) :
    E.ordForm (cast (congrArg (fun t => RationalPluriForms t d m) h) τ) = E.ordForm τ := by
  subst h; rfl

private theorem cast_ne_zero {V : Scheme.{u}} [IsIntegral V] {s s' : V ⟶ Spec (.of k)}
    (h : s = s') {d : ℕ} {m : ℤ} {τ : RationalPluriForms s d m} (hτ : τ ≠ 0) :
    cast (congrArg (fun t => RationalPluriForms t d m) h) τ ≠ 0 := by
  subst h; exact hτ

end Forms

/-! ### Existence of canonical divisors on normal varieties -/

section CanonicalDivisorExistence

open Opposite TopologicalSpace

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- A nonempty open subscheme of an irreducible scheme is dense. -/
private theorem isDominant_opens_ι {Y : Scheme.{u}} [IrreducibleSpace Y] (V : Y.Opens)
    [Nonempty V] : IsDominant V.ι :=
  Opens.isDominant_ι (V.isOpen.dense ⟨_, (Classical.arbitrary V).2⟩)

/-- A nonempty open subscheme of an integral scheme has the same function field. -/
private theorem functionFieldMap_opens_ι_bijective {Y : Scheme.{u}} [IsIntegral Y] (V : Y.Opens)
    [Nonempty V] [IsDominant V.ι] : Function.Bijective (functionFieldMap V.ι) :=
  functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤ ⟨Classical.arbitrary V, trivial⟩

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {Y : Scheme.{u}} {s : Y ⟶ Spec (.of k)}
    (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

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

/-- A nonempty open subscheme of a variety has the dimension of the variety: both are the
transcendence degree of the common function field. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hbij := functionFieldMap_opens_ι_bijective U
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-! ### The divisorial sheaf on an open subscheme -/

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : MMP.Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
  rw [MMP.Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable (U : X.Opens) [Nonempty U] [IsDominant U.ι]

private theorem genericPoint_mem_of_index {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V}) :
    genericPoint U.toScheme ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : U.toScheme.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    genericPoint U.toScheme ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint U.toScheme ⤳ x := (genericPoint_spec U.toScheme).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The irreducible component `X` of the integral scheme `X`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant U.ι]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : U.toScheme.Opens} (h : genericPoint U.toScheme ∈ V) :
    {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V} :=
  ⟨topComponent U.toScheme, by rw [componentGenericPoint_eq_genericPoint]; exact h⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf U.toScheme).obj (op V)) :=
  fun Z => (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι (evFF ψ (indexX U (genericPoint_mem_of_index U Z))))

private theorem evFF_restrictRF (V : U.toScheme.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V))))
    (Z : {Z : irreducibleComponents U.toScheme // componentGenericPoint U.toScheme Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    evFF (restrictRF U V ψ) Z = functionFieldMap U.ι (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : U.toScheme.Opens) :
    Function.Injective (restrictRF U V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX U Z'
  have h1 := congrArg (fun φ => evFF φ (indexU U hV)) h
  simp only [evFF_restrictRF U V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap U.ι).injective h1)

private theorem restrictRF_surjective (V : U.toScheme.Opens) :
    Function.Surjective (restrictRF U V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap U.ι) (functionFieldMap_opens_ι_bijective U)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU U (genericPoint_mem_of_indexX U Z')))), ?_⟩
  funext Z
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap U.ι ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (U.toScheme.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

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

private theorem functionFieldMap_germ_appIso_inv (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (h₁ : genericPoint X ∈ U.ι ''ᵁ V) (h₂ : genericPoint U.toScheme ∈ V) :
    functionFieldMap U.ι (X.presheaf.germ (U.ι ''ᵁ V) (genericPoint X) h₁
      ((U.ι.appIso V).inv r)) = U.toScheme.presheaf.germ V (genericPoint U.toScheme) h₂ r := by
  have h₃ : U.ι (genericPoint U.toScheme) ∈ U.ι ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (U.ι.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (U.ι ''ᵁ V)))) :
    restrictRF U V ((U.ι.appIso V).inv r • ψ) = r • restrictRF U V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv U V r _
    (genericPoint_mem_of_index U Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : U.toScheme.Opens) : restrictRF U V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

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

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := isDominant_opens_ι T
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
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

end CanonicalDivisorExistence

/-! ### The comparison of two nef weak models -/

section Comparison

variable {k : Type u} [Field k] {Y Z₁ Z₂ S : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z₁] [IsLocallyNoetherian Z₁] [IsNormal Z₁]
    [IsIntegral Z₂] [IsLocallyNoetherian Z₂] [IsNormal Z₂]
    {sY : Y ⟶ Spec (.of k)} {s₁ : Z₁ ⟶ Spec (.of k)} {s₂ : Z₂ ⟶ Spec (.of k)}
    [QuasiCompact s₁] [QuasiCompact s₂] {sS : S ⟶ Spec (.of k)}
    {πY : Y ⟶ S} {π₁ : Z₁ ⟶ S} {π₂ : Z₂ ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ₁ : Y.RationalMap Z₁} {φ₂ : Y.RationalMap Z₂}

/-- A rational map `Y ⤏ V` inverse to a proper morphism `p : V ⟶ Y` is defined at the generic
point of every prime divisor of `Y`. -/
private theorem exists_rep_mem_domain {V : Scheme.{u}} [IsReduced V]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {p : V ⟶ Y} [IsProper p] {h : Y.RationalMap V}
    (hinv : RationalMap.IsInverse p.toRationalMap h) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ g : Y.PartialMap V, g.toRationalMap = h ∧ Q.genericPoint ∈ g.domain := by
  have hhp := compHom_eq_of_isInverse hinv
  obtain ⟨g, hg, hg'⟩ := Scheme.RationalMap.mem_domain.mp
    (MMP.Flips.RationalMap.mem_domain_of_coheight_le_one (𝟙 Y) p h hhp
      (coheight_genericPoint_le_one Q))
  exact ⟨g, hg', hg⟩

/-- The adjoint `K_Z + C_Z` of a nef weak model is a real combination of Cartier divisors. -/
private theorem isCartierCombination_logCanonicalDivisor {πZ : Z₁ ⟶ S}
    (h₁ : IsNefWeakModel sY s₁ sS πY πZ KY C φ₁) :
    MMP.Flips.IsCartierCombination
      (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ₁ KY)
        (MMP.Mori.RationalMap.transformDivisor φ₁ C)) := by
  obtain ⟨m, r, L, hLc, heq, -⟩ := h₁.isRelativelyNef
  exact ⟨m, r, L, hLc, by rw [heq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

end Comparison

end Crepant

namespace SamePrimes

open CategoryTheory.Limits

section Generalities

private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [Crepant.coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

private theorem two_le_of_not_le_one {c : ℕ∞} (h : ¬ c ≤ 1) : 2 ≤ c := by
  simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (not_le.mp h)

end Generalities

/-- A prime divisor with a divisorial transform is not exceptional. -/
private theorem not_isExceptional_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}}
    {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor Y}
    (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some F) :
    ¬ MMP.Mori.RationalMap.IsExceptional φ P := by
  rw [MMP.Mori.RationalMap.isExceptional_iff]
  intro hex
  have h2 := hex (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight,
    ← MMP.Mori.RationalMap.support_transformPrimeDivisor h] at h2
  have h3 := h2 F.genericPoint (by
    change F.genericPoint ∈ F.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl)
  rw [F.coheight_genericPoint] at h3
  exact absurd h3 (by decide)

/-- If `P` is not exceptional for `φ = q ∘ g`, then `q(g(η_P))` has coheight at most one. -/
private theorem coheight_apply_le_one_of_not_isExceptional {X W Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (q : W ⟶ Y) {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    (g : X.PartialMap W) (hg : (g.compHom q).toRationalMap = φ) (hP : P.genericPoint ∈ g.domain)
    (hnex : ¬ MMP.Mori.RationalMap.IsExceptional φ P) :
    Order.coheight (q (g.hom ⟨P.genericPoint, hP⟩)) ≤ 1 := by
  by_contra h2
  refine hnex (Or.inr ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨_, hP, hg⟩, ?_⟩)
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  have hx' : x ∈ (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) := hx
  rw [Crepant.coe_transform_eq_closure_singleton (g.compHom q) hg P hP] at hx'
  exact (two_le_of_not_le_one h2).trans (Order.coheight_anti
    (Scheme.le_iff_specializes.mpr (specializes_iff_mem_closure.mpr hx')))

end SamePrimes

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem isCurve_ι (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := isCurve_ι (k := k) C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

end Intersection

section Geometry

/-- A combination of Cartier divisors, written with `Divisor.toRDivisor`, is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_eq_sum {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    [IsNormal Y] {D : RDivisor Y} {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor Y)
    (hL : ∀ j, (L j).IsCartier) (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    IsCartierCombination D :=
  ⟨m, r, L, hL, by simpa only [toRDivisor_eq_mapCoeffs] using hD⟩

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier: each prime divisor `P` has a
Cartier multiple `m_P P`, and `D = ∑ (D_P / m_P) (m_P P)`. -/
private theorem isCartierCombination_of_isQFactorial {k : Type u} [Field k] {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : MMP.Fourfold.IsQFactorial sY) (D : RDivisor Y) : IsCartierCombination D := by
  classical
  choose m hm hc using fun P : MMP.Mori.PrimeDivisor Y => hY.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  refine isCartierCombination_of_eq_sum (fun j => D (e.symm j) / m (e.symm j))
    (fun j => ((m (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor Y) 1)
    (fun j => hc _) ?_
  have hterm : ∀ P : MMP.Mori.PrimeDivisor Y, (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)) =
        Finsupp.single P (D P) := by
    intro P
    ext Q
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : P = Q
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply, div_mul_cancel₀ _ hm0]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  rw [Equiv.sum_comp e.symm (fun P : D.support => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single (P : MMP.Mori.PrimeDivisor Y) 1 :
        Divisor Y)))]
  rw [Finset.sum_coe_sort D.support (fun P => (D P / m P) •
      Divisor.toRDivisor (((m P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor Y)))]
  simp_rw [hterm]
  exact (Finsupp.sum_single D).symm

/-- A prime divisor of `W` that is not exceptional over `Y` lies over a prime divisor `P` of `Y`,
`q` is a local isomorphism at its generic point, and the coefficient of `P` in a push-forward
`q_* D` is the coefficient of `E` in `D`. -/
private theorem exists_transformDivisor_apply_eq_of_not_isExceptionalPrimeDivisor
    {k : Type u} [Field k] {W Y : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    (q : W ⟶ Y) (hW : IsNormalVariety k (q ≫ sY)) [IsProper q] (hqb : IsBirationalMorphism q)
    (E : MMP.Mori.PrimeDivisor W) (hE : ¬ IsExceptionalPrimeDivisor sY q E) :
    ∃ P : MMP.Mori.PrimeDivisor Y, q E.genericPoint = P.genericPoint ∧
      IsIso (q.stalkMap E.genericPoint) ∧
      ∀ D : RDivisor W, MMP.Mori.RationalMap.transformDivisor q.toRationalMap D P = D E := by
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsSeparated sY := hY.1.toIsSeparated
  haveI : IsSeparated q := IsSeparated.of_comp q sY
  haveI : IsDominant q := hqb.isDominant
  set DE : ProperDivisorOver k sY := ProperDivisorOver.mk ⟨W, q, hW, hqb, E⟩ inferInstance
  have hnot : ¬ DE.IsExceptional := fun h => hE ⟨hW, hqb, inferInstance, h⟩
  have hc : ¬ 2 ≤ codimension DE.toDivisorOver.center := by
    intro h2
    refine hnot ?_
    rw [MMP.Positivity.DivisorOver.codimension_center] at h2
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint]
    have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
      (DE.toDivisorOver.f DE.toDivisorOver.E.genericPoint)
    rw [← hd]
    gcongr
    rw [← WithBot.coe_ofNat]
    exact WithBot.coe_le_coe.mpr h2
  rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hY] at hc
  simp only [not_forall, not_not] at hc
  obtain ⟨P, hv⟩ := hc
  have hEP : q E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hv
  obtain ⟨E', hE'P, hiso', htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hW hqb P
  have hbij := hqb.functionFieldMap_bijective
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (Y.presheaf.stalk (q E.genericPoint)) := by rw [hEP]; infer_instance
  have : ValuationRing (Y.presheaf.stalk (q E'.genericPoint)) := by rw [hE'P]; infer_instance
  have hiso := MMP.Positivity.isIso_stalkMap_of_valuationRing q hbij E.genericPoint
  have hEE' : E'.genericPoint = E.genericPoint :=
    MMP.Positivity.eq_of_isIso_stalkMap q hbij (hEP.trans hE'P.symm)
  have hEE : E' = E := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hEE'
  subst hEE
  exact ⟨P, hEP, hiso, fun D => htr D⟩

/-- **The projection formula for the pull-back of a Cartier divisor.** If `L'` is the pull-back of
the Cartier divisor `L` along `f` and `f(C') = C` is a proper curve, then
`(L' · C') = [k(C') : k(C)] (L · C)`. -/
private theorem degreeOn_eq_mul_of_isPullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sX] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ Y) (hf : f ≫ sY = sX)
    {L : Divisor Y} (hL : L.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ L.supp}
    {L' : Divisor X} (h : L.IsPullback f hB L') (hc : L'.IsCartier) (C' : ProperCurve sX)
    (C : ProperCurve sY) (hC : f C'.point = C.point) :
    (L'.degreeOn k sX C'.ι C'.dim_le hc : ℝ) =
      (residueFieldDegree f C'.point : ℝ) * (L.degreeOn k sY C.ι C.dim_le hL : ℝ) := by
  obtain rfl := Divisor.IsPullback.pullback_eq hL h
  obtain ⟨c, hcC⟩ := C
  dsimp only at hC
  subst hC
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward f hf hL hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos hcC]
  simp only [OneCycle.degree, Finsupp.linearCombination_single, smul_eq_mul]
  push_cast
  rfl

end Geometry

section CurveLifting

/-- A nonempty fibre of a map out of a Noetherian T₀ space has a point closed in the fibre. -/
private lemma exists_closed_mem_fiber {X Y : Type*} [TopologicalSpace X] [T0Space X]
    [TopologicalSpace.NoetherianSpace X] (f : X → Y) {y : Y} (hy : y ∈ Set.range f) :
    ∃ a, f a = y ∧ ∀ b, f b = y → a ⤳ b → b = a := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨⟨a, ha⟩, -, hcl⟩ := (isClosed_univ (X := f ⁻¹' {y})).exists_closed_singleton
    ⟨⟨x, hx⟩, Set.mem_univ _⟩
  refine ⟨a, ha, fun b hb hab => ?_⟩
  have : (⟨a, ha⟩ : f ⁻¹' {y}) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp (this.mem_closed hcl rfl))

/-- A one-point space has topological Krull dimension `0`. -/
private lemma topologicalKrullDim_eq_zero_of_subsingleton (X : Type*) [TopologicalSpace X]
    [Nonempty X] [Subsingleton X] : topologicalKrullDim X = 0 := by
  have : DiscreteTopology X := ⟨Subsingleton.elim _ _⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

variable {k : Type u} [Field k]

/-- A proper morphism from a reduced scheme whose image is dense in a proper curve `C'` is proper
over `k`: it factors through its scheme-theoretic image, which is `C'`. -/
private lemma isProper_comp_of_closure_range {X B : Scheme.{u}}
    {sB : B ⟶ Spec (.of k)} (C' : ProperCurve sB) (φ : X ⟶ B) [IsReduced X] [IsProper φ]
    (hφ : closure (Set.range φ.base) = closure {C'.point}) : IsProper (φ ≫ sB) := by
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure {C'.point}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact congrArg _ (TopologicalSpace.Closeds.ext (by
      rw [TopologicalSpace.Closeds.coe_closure, TopologicalSpace.Closeds.coe_closure, hφ]))
  have : IsProper (φ.imageι ≫ sB) := by
    change IsProper (φ.ker.subschemeι ≫ sB); rw [hker]; exact C'.isProper_ι_comp
  have : IsProper (φ.toImage ≫ φ.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper φ.toImage := IsProper.of_comp _ φ.imageι
  rw [← Scheme.Hom.toImage_imageι φ, Category.assoc]
  infer_instance

/-- **Lifting proper curves.** Let `h : A ⟶ B` be a proper surjective morphism of schemes of
finite type over `k`. Every proper curve `C'` on `B` is `h(C)` for a proper curve `C` on `A`
whose function field is a finite extension of that of `C'`. -/
private theorem exists_properCurve_map_eq {A B : Scheme.{u}} (sA : A ⟶ Spec (.of k))
    (sB : B ⟶ Spec (.of k)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    [LocallyOfFiniteType sB] [QuasiCompact sB] (h : A ⟶ B) [IsProper h] [Surjective h]
    (hh : h ≫ sB = sA) (C' : ProperCurve sB) :
    ∃ C : ProperCurve sA, h C.point = C'.point ∧ residueFieldDegree h C.point ≠ 0 := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace sA
  have : IsNoetherian A := ⟨⟩
  obtain ⟨a, haξ, hamax⟩ := exists_closed_mem_fiber h.base (h.surjective C'.point)
  set ι := curveSubschemeAtι a
  set φ := ι ≫ h
  have : IrreducibleSpace (curveSubschemeAt a) :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := a)).closure
  have hgen : ι (genericPoint _) = a :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure a
  have hφgen : φ (genericPoint _) = C'.point := by simp [φ, hgen, haξ]
  have hclr : closure (Set.range φ.base) = closure {C'.point} := by
    rw [MMP.Flips.closure_range_eq_closure_genericPoint φ, hφgen]
  have : Subsingleton (φ.base ⁻¹' {φ.base (genericPoint _)}) := by
    suffices ∀ c, φ c = C'.point → c = genericPoint _ from
      ⟨fun u v => Subtype.ext ((this _ (u.2.trans hφgen)).trans (this _ (v.2.trans hφgen)).symm)⟩
    intro c hc
    have hca : a ⤳ ι c := specializes_iff_mem_closure.mpr (range_curveSubschemeAtι a ▸ ⟨c, rfl⟩)
    exact ι.isEmbedding.injective
      ((hamax _ (by rw [← hc, Scheme.Hom.comp_apply]) hca).trans hgen.symm)
  let e := φ.fiberHomeo (φ.base (genericPoint _))
  have : Subsingleton (φ.fiber (φ.base (genericPoint _))) := e.injective.subsingleton
  have : Nonempty (φ.fiber (φ.base (genericPoint _))) := ⟨e.symm ⟨genericPoint _, rfl⟩⟩
  have hcomp : φ ≫ sB = ι ≫ sA := by rw [Category.assoc, hh]
  have hdim : topologicalKrullDim (curveSubschemeAt a) = 1 := by
    rw [MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range φ k (ι ≫ sA) sB hcomp,
      topologicalKrullDim_eq_zero_of_subsingleton (φ.fiber _), hclr, zero_add]
    exact C'.dim_eq
  refine ⟨⟨a, hdim, hcomp ▸ isProper_comp_of_closure_range C' φ hclr⟩, haξ, ?_⟩
  -- `a` is a closed point of its fibre, so `κ(a)` is finite over `κ(h(a))`
  have : LocallyOfFiniteType h := by
    have : LocallyOfFiniteType (h ≫ sB) := hh ▸ inferInstance
    exact locallyOfFiniteType_of_comp h sB
  have hcl : IsClosed ({h.asFiber a} : Set (h.fiber (h a))) := by
    have hsub : IsClosed ({⟨a, rfl⟩} : Set (h.base ⁻¹' {h a})) := by
      refine isClosed_of_closure_subset fun b hb => ?_
      have hab : (⟨a, rfl⟩ : h.base ⁻¹' {h a}) ⤳ b := specializes_iff_mem_closure.mpr hb
      exact Subtype.ext (hamax b.1 ((Set.mem_singleton_iff.mp b.2).trans haξ)
        (hab.map continuous_subtype_val))
    have hpre : ({h.asFiber a} : Set (h.fiber (h a))) = h.fiberHomeo (h a) ⁻¹' {⟨a, rfl⟩} := by
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        simp [Scheme.Hom.asFiber]
      · intro hz
        rw [Scheme.Hom.asFiber, ← hz, Homeomorph.symm_apply_apply]
    rw [hpre]
    exact (h.fiberHomeo (h a)).isClosed_preimage.mpr hsub
  have hfin := (isClosed_asFiber_iff_finite_residueField h a).mp hcl
  letI := (h.residueFieldMap a).hom.toAlgebra
  exact Module.finrank_pos.ne'

end CurveLifting

section Nef

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

/-- **Pull-backs of divisors nef over a base are nef along morphisms over it.** Let
`p : W ⟶ Y` and `q : W ⟶ Z` be morphisms with `p ≫ πY = q ≫ πZ` for `πY : Y ⟶ S`,
`πZ : Z ⟶ S`, and `q` proper. If `M` is an `ℝ`-Cartier divisor on `Z` nef over `S`, its pull-back
`q^*M` is `p`-nef. -/
private theorem isRelativelyNef_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z S : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ]
    [LocallyOfFiniteType sZ] [QuasiCompact sZ] (πY : Y ⟶ S) (πZ : Z ⟶ S) (p : W ⟶ Y)
    (q : W ⟶ Z) [IsProper q] [QuasiCompact (q ≫ sZ)] (hpq : p ≫ πY = q ≫ πZ)
    {M : RDivisor Z} (hM : IsRelativelyNef k sZ πZ M) {M' : RDivisor W}
    (hM' : IsRCartierPullback q M M') : IsRelativelyNef k (q ≫ sZ) p M' := by
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q ≫ sZ)
  obtain ⟨m, r, L₀, L₁, hL₀, hMeq, hpb, hM'eq⟩ := hM'
  choose hB hpbj using hpb
  obtain rfl : L₁ = fun j => (L₀ j).pullback (hL₀ j) (hB j) :=
    funext fun j => (Divisor.IsPullback.pullback_eq (hL₀ j) (hpbj j)).symm
  have hL₁c : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).IsCartier := fun j =>
    (hL₀ j).isCartier_pullback q (hB j)
  refine ⟨m, r, _, hL₁c, hM'eq, fun C hC x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sZ) C r _ hL₁c
  rw [← hM'eq] at hx0
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sZ) C).1 _ _ _ _ _ _ _ hx hx0]
  by_cases hc : IsProperCurve sZ (q C.point)
  · obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ProperCurve sZ, C₀.point = q C.point := ⟨⟨_, hc⟩, rfl⟩
    have hC₀c : C₀.IsContractedBy πZ := by
      intro z hz
      rw [hC₀] at hz ⊢
      have hsub : closure ({q C.point} : Set Z) ⊆ q '' closure ({C.point} : Set W) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C.point, subset_closure rfl, rfl⟩)
          (q.isClosedMap _ isClosed_closure)
      obtain ⟨w, hw, rfl⟩ := hsub hz
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply,
        Scheme.Hom.comp_apply, hC w hw]
    have hdeg : ∀ j, ((((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) C.ι C.dim_le
        (hL₁c j) : ℤ) : ℝ) =
        (residueFieldDegree q C.point : ℝ) * (L₀ j).degreeOn k sZ C₀.ι C₀.dim_le (hL₀ j) := by
      intro j
      rw [degreeOn_pullback_eq_mul q (hL₀ j) (hB j) C C₀ hC₀]
      push_cast; rfl
    obtain ⟨mM, rM, LM, hLM, hMeq', hMall⟩ := hM
    have hMx := isRIntersectionNumber_sum_degreeOn k sZ C₀ rM LM hLM
    rw [← hMeq'] at hMx
    have h0 := isRIntersectionNumber_sum_degreeOn k sZ C₀ r L₀ hL₀
    rw [← hMeq] at h0
    have hnn := hMall C₀ hC₀c _ hMx
    rw [(IsRIntersectionNumber.eq_and_linear k sZ C₀).1 _ _ _ _ _ _ _ hMx h0] at hnn
    simp only [hdeg, mul_left_comm (r _), ← Finset.mul_sum]
    exact mul_nonneg (Nat.cast_nonneg _) hnn
  · have hdeg : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).degreeOn k (q ≫ sZ) C.ι C.dim_le
        (hL₁c j) = 0 := fun j => degreeOn_pullback_eq_zero q (hL₀ j) (hB j) C hc
    simp [hdeg]

end Nef

section RationalMaps

open CategoryTheory.Limits

/-- Composing a rational map with two morphisms in turn is composing it with their composite. -/
private theorem compHom_compHom {X Y Z T : Scheme.{u}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- The rational map of a morphism, composed with a morphism, is the rational map of the
composite. -/
private theorem toRationalMap_compHom {X Z T : Scheme.{u}} (f : X ⟶ Z) (g : Z ⟶ T) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toPartialMap_compHom]

/-! ### Function fields along a common resolution -/

private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- For a partial isomorphism `e` representing a dominant morphism `p : W ⟶ X` of integral
schemes, `Spec k(W) ⟶ Spec k(X) ⟶ W` along `e⁻¹` is the canonical map. -/
private theorem specMap_functionFieldMap_fromFunctionField_symm {W X : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] (p : W ⟶ X) [IsDominant p] (e : W.PartialIso X)
    (he : e.toRationalMap = p.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ e.symm.toRationalMap.fromFunctionField =
      W.fromSpecStalk (genericPoint W) := by
  have hW : genericPoint W ∈ e.source :=
    (genericPoint_specializes _).mem_open e.source.2 e.dense_source.nonempty.choose_spec
  have hX : genericPoint X ∈ e.target :=
    (genericPoint_specializes _).mem_open e.target.2 e.dense_target.nonempty.choose_spec
  have h1 := congrArg Scheme.RationalMap.fromFunctionField he
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hW] at h1
  have h1' : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom ≫ e.target.ι =
      W.fromSpecStalk (genericPoint W) ≫ p := by
    refine h1.trans ?_
    exact Scheme.PartialMap.fromSpecStalkOfMem_toPartialMap p _
  have c1 : e.source.fromSpecStalkOfMem (genericPoint W) hW ≫ e.iso.hom =
      Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
        e.target.fromSpecStalkOfMem (genericPoint X) hX := by
    rw [← cancel_mono e.target.ι, Category.assoc, h1', Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (functionFieldMap_fromSpecStalk p).symm
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq _ hX]
  change Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
    e.target.fromSpecStalkOfMem (genericPoint X) hX ≫ e.iso.inv ≫ e.source.ι = _
  rw [← Category.assoc, ← c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- On a common resolution `p : W ⟶ X`, `q : W ⟶ Y` of `φ : X ⤏ Y` (with `h` inverse to `p`
and `q = φ ∘ h`), `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_functionFieldMap_fromFunctionField_of_isInverse {X Y W : Scheme.{u}}
    [IsIntegral X] [IsIntegral W] (φ : X.RationalMap Y) (p : W ⟶ X) (q : W ⟶ Y)
    (h : X.RationalMap W) [IsDominant p]
    (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h) (hcomp : h.compHom q = φ) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨e, he1, he2⟩ := hinv
  rw [← hcomp, ← he2, MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc,
    specMap_functionFieldMap_fromFunctionField_symm p e he1]

/-! ### Comparison of the two composites to the base -/

/-- On a common resolution `p : W ⟶ X`, `q : W ⟶ Y` of a map `φ` over `Z`, the two composites
`W ⟶ Z` agree. -/
private theorem comp_eq_comp_of_isOver {X Y Z W : Scheme.{u}} [IsIntegral X] [IsIntegral W]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (πX : X ⟶ Z) (πY : Y ⟶ Z) {φ : X.RationalMap Y}
    (hφZ : MMP.Flips.RationalMap.IsOver πX πY φ) (p : W ⟶ X) (q : W ⟶ Y) (h : X.RationalMap W)
    [IsDominant p] (hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap h)
    (hcomp : h.compHom q = φ) : p ≫ πX = q ≫ πY := by
  have h1 := specMap_functionFieldMap_fromFunctionField_of_isInverse φ p q h hinv hcomp
  have h2 : (p ≫ πX).toRationalMap = (q ≫ πY).toRationalMap := by
    refine Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom]
    calc W.fromSpecStalk (genericPoint W) ≫ p ≫ πX
        = Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫
            X.fromSpecStalk (genericPoint X) ≫ πX := by
          rw [← Category.assoc (Spec.map _), functionFieldMap_fromSpecStalk, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField ≫ πY := by
          rw [← MMP.Flips.RationalMap.fromFunctionField_compHom, hφZ,
            MMP.Flips.RationalMap.fromFunctionField_hom]
      _ = W.fromSpecStalk (genericPoint W) ≫ q ≫ πY := by
          rw [← Category.assoc, h1, Category.assoc]
  have H := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h2)
  rw [Scheme.Hom.toPartialMap_hom] at H
  exact (cancel_epi _).mp H

/-! ### Strict transforms on a common resolution -/

end RationalMaps

section CurveInequality

variable {k : Type u} [Field k]

/-- An effective `ℝ`-divisor on a smooth scheme has nonnegative degree on a proper curve whose
generic point is outside its support. -/
private theorem nonneg_of_isRIntersectionNumber {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (hsm : IsSmoothScheme sX)
    {A : RDivisor X} (hA : ∀ P, 0 ≤ A.coeff P) (C : ProperCurve sX) (hC : C.point ∉ A.supp)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX A r L C x) : 0 ≤ x := by
  classical
  let e := A.support.equivFin
  let P : Fin A.support.card → MMP.Mori.PrimeDivisor X := fun j => (e.symm j : _)
  let PD : Fin A.support.card → Divisor X := fun j => Finsupp.single (P j) 1
  have hL : ∀ j, (PD j).IsCartier := fun j =>
    MMP.Fourfold.isCartier_of_isSmoothScheme hsm _
  have hterm : ∀ Q : MMP.Mori.PrimeDivisor X,
      A Q • Divisor.toRDivisor (Finsupp.single Q (1 : ℤ) : Divisor X) = Finsupp.single Q (A Q) := by
    intro Q
    ext Q'
    simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    by_cases hQ : Q = Q'
    · subst hQ
      simp [DivisorWithCoeffs.coeff_apply]
    · simp [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hQ]
  have hAeq : A = ∑ j, A (P j) • Divisor.toRDivisor (PD j) := by
    rw [Equiv.sum_comp e.symm (fun Q : A.support => A Q •
      Divisor.toRDivisor (Finsupp.single (Q : MMP.Mori.PrimeDivisor X) (1 : ℤ) : Divisor X))]
    rw [Finset.sum_coe_sort A.support (fun Q => A Q •
      Divisor.toRDivisor (Finsupp.single Q (1 : ℤ) : Divisor X))]
    simp_rw [hterm]
    exact (Finsupp.sum_single A).symm
  rw [eq_sum_degreeOn_of_isRIntersectionNumber k sX C _ _ hL hAeq hx]
  refine Finset.sum_nonneg fun j _ => mul_nonneg (hA _) ?_
  have hne : ∃ c : C.scheme, C.ι c ∉ (PD j).supp := by
    refine ⟨genericPoint C.scheme, ?_⟩
    rw [ProperCurve.ι_genericPoint]
    intro hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    have hEP : P j = E := by
      by_contra h
      exact hE (DivisorWithCoeffs.coeff_single_of_ne h _)
    subst hEP
    have hPA : A (P j) ≠ 0 := Finsupp.mem_support_iff.mp (e.symm j).2
    exact hC (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P j, hPA, hxE⟩)
  have h0 := (MMP.Threefold.Mori.degreeOn_nonneg_and_eq_zero_iff sX C.ι C.dim_le _ (hL j)
    (Finsupp.single_nonneg.mpr zero_le_one) hne).1
  exact_mod_cast h0

/-- **The curve inequality on a common resolution.** Let `p : W ⟶ Y`, `q : W ⟶ Z` be proper
morphisms over `S`, `p` surjective and `W` smooth, `L` an `ℝ`-Cartier divisor on `Y` and `M` an
`ℝ`-Cartier divisor on `Z` nef over `S`, with `p^*L - q^*M ≥ 0`. A proper curve `Γ ⊆ Y` over a
point of `S` whose generic point is not the image of a point of `Supp (p^*L - q^*M)` has
`L · Γ ≥ 0`. -/
private theorem nonneg_of_isRIntersectionNumber_of_resolution {Y Z S W : Scheme.{u}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    [LocallyOfFiniteType sW] [QuasiCompact sW] (hWs : IsSmoothScheme sW)
    {πY : Y ⟶ S} {πZ : Z ⟶ S} (p : W ⟶ Y) (q : W ⟶ Z) [IsProper p] [IsProper q] [Surjective p]
    (hpY : p ≫ sY = sW) (hqZ : q ≫ sZ = sW) (hpq : p ≫ πY = q ≫ πZ)
    {L : RDivisor Y} {M : RDivisor Z} (hM : IsRelativelyNef k sZ πZ M)
    {GY GZ : RDivisor W} (hGY : IsRCartierPullback p L GY) (hGZ : IsRCartierPullback q M GZ)
    (hA : ∀ P, 0 ≤ (GY - GZ).coeff P)
    (Γ : ProperCurve sY) (hΓ : Γ.IsContractedBy πY)
    (hΓB : Γ.point ∉ p '' ((GY - GZ).supp : Set W))
    {m : ℕ} {r : Fin m → ℝ} {Ls : Fin m → Divisor Y} {x : ℝ}
    (hx : IsRIntersectionNumber k sY L r Ls Γ x) : 0 ≤ x := by
  subst hqZ
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q ≫ sZ)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  obtain ⟨Γ', hΓ'p, hd⟩ := exists_properCurve_map_eq (q ≫ sZ) sY p hpY Γ
  -- `q^*M` is nef over `S`
  have hnef : IsRelativelyNef k (q ≫ sZ) (p ≫ πY) GZ :=
    isRelativelyNef_of_isRCartierPullback (𝟙 S) πZ (p ≫ πY) q (by rw [Category.comp_id, hpq])
      hM hGZ
  have hcon : Γ'.IsContractedBy (p ≫ πY) := by
    intro w hw
    have hpw : p w ∈ closure {Γ.point} := by
      rw [← hΓ'p]
      exact specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hw).map p.continuous)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ (p w) hpw, hΓ'p]
  -- `p^*L · Γ' = [k(Γ') : k(Γ)] (L · Γ)`
  obtain ⟨mY, rY, LY, LY', hLY, hLeq, hpb, hGYeq⟩ := hGY
  choose hB hpbj using hpb
  have hLY'c : ∀ j, (LY' j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hLY j) (hpbj j)]
    exact (hLY j).isCartier_pullback p (hB j)
  have hxY := isRIntersectionNumber_sum_degreeOn k (q ≫ sZ) Γ' rY LY' hLY'c
  rw [← hGYeq] at hxY
  have hxL := isRIntersectionNumber_sum_degreeOn k sY Γ rY LY hLY
  rw [← hLeq] at hxL
  have hxx := (IsRIntersectionNumber.eq_and_linear k sY Γ).1 _ _ _ _ _ _ _ hx hxL
  have hdeg : ∀ j, ((LY' j).degreeOn k (q ≫ sZ) Γ'.ι Γ'.dim_le (hLY'c j) : ℝ) =
      (residueFieldDegree p Γ'.point : ℝ) * ((LY j).degreeOn k sY Γ.ι Γ.dim_le (hLY j) : ℝ) :=
    fun j => degreeOn_eq_mul_of_isPullback p hpY (hLY j) (hpbj j) (hLY'c j) Γ' Γ hΓ'p
  -- `q^*M · Γ' ≥ 0`
  obtain ⟨mZ, rZ, LZ, hLZ, hGZeq, hnefall⟩ := hnef
  have hxZ := isRIntersectionNumber_sum_degreeOn k (q ≫ sZ) Γ' rZ LZ hLZ
  rw [← hGZeq] at hxZ
  have hZ0 := hnefall Γ' hcon _ hxZ
  -- `(p^*L - q^*M) · Γ' ≥ 0`
  have hA' := (IsRIntersectionNumber.eq_and_linear k (q ≫ sZ) Γ').2 _ _ _ _ _ _ _ _ 1 (-1) hxY hxZ
  rw [one_smul, neg_one_smul, ← sub_eq_add_neg] at hA'
  have hA0 := nonneg_of_isRIntersectionNumber hWs hA Γ' (fun h => hΓB ⟨_, h, hΓ'p⟩) hA'
  have hdpos : (0 : ℝ) < residueFieldDegree p Γ'.point := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  simp only [hdeg, mul_left_comm (rY _), ← Finset.mul_sum] at hA0
  rw [← hxx] at hA0
  nlinarith

end CurveInequality

section FibreType

variable {k : Type u} [Field k]

/-- A divisor whose negative is `f`-ample is negative on every proper curve contracted by `f`. -/
private theorem exists_isRIntersectionNumber_neg {X V : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (f : X ⟶ V)
    {L : RDivisor X} (hL : IsRelativelyAntiAmple f L) (Γ : ProperCurve sX)
    (hΓ : Γ.IsContractedBy f) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (Ls : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber k sX L r Ls Γ x ∧ x < 0 := by
  obtain ⟨m, r, A, hm, hr, hA, hLeq⟩ := hL
  have hAc : ∀ j, (A j).IsCartier := fun j => (hA j).1
  have hLeq' : L = ∑ j, (-r j) • Divisor.toRDivisor (A j) := by
    have hL' : L = -(-L) := (neg_neg L).symm
    rw [hL', hLeq]
    simp [neg_smul, Finset.sum_neg_distrib]
  have hx := isRIntersectionNumber_sum_degreeOn k sX Γ (fun j => -r j) A hAc
  rw [← hLeq'] at hx
  refine ⟨m, _, A, _, hx, ?_⟩
  have hpos : ∀ j, (0 : ℝ) < (A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) := fun j => by
    exact_mod_cast MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hA j) (hAc j) Γ hΓ
  have hsum : 0 < ∑ j, r j * ((A j).degreeOn k sX Γ.ι Γ.dim_le (hAc j) : ℝ) :=
    Finset.sum_pos (fun j _ => mul_pos (hr j) (hpos j)) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

/-- A contraction is dominant: an open set missing its image has no sections upstairs. -/
private theorem isDominant_of_isContraction {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X} (hf : MMP.Flips.IsContraction k sX sY f) :
    IsDominant f := by
  have hfX := hf.isIso_app
  refine ⟨dense_iff_inter_open.mpr fun V hV hVne => ?_⟩
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  let V' : X.Opens := ⟨V, hV⟩
  have hbot : f ⁻¹ᵁ V' = ⊥ := by
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
    intro y hy
    exact (Set.eq_empty_iff_forall_notMem.mp hempty) (f y) ⟨hy, y, rfl⟩
  have hsub : Subsingleton Γ(Y, f ⁻¹ᵁ V') := by rw [hbot]; infer_instance
  have : Subsingleton Γ(X, V') :=
    (ConcreteCategory.bijective_of_isIso (f.app V')).1.subsingleton
  obtain ⟨x, hx⟩ := hVne
  have h10 := congrArg (X.presheaf.germ V' x hx).hom (Subsingleton.elim (1 : Γ(X, V')) 0)
  rw [map_one, map_zero] at h10
  exact one_ne_zero h10

end FibreType

section PartThree

variable {k : Type u} [Field k]

open CategoryTheory.Limits in
/-- The image of the support of a divisor under a birational morphism of varieties misses the
generic point. -/
private theorem genericPoint_notMem_image_supp {W Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    (hY : AlgebraicGeometry.IsVariety k sY) (p : W ⟶ Y)
    (hW : AlgebraicGeometry.IsVariety k (p ≫ sY)) (hpb : IsBirationalMorphism p)
    (D : RDivisor W) : genericPoint Y ∉ p '' (D.supp : Set W) := by
  rintro ⟨w, hw, hpw⟩
  obtain ⟨E, -, hwE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hw
  have hdim := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hpb
  have h1 := coheight_le_coheight_map sY (p ≫ sY) hY hW p rfl hdim.symm w
  rw [hpw] at h1
  have h0 : Order.coheight (genericPoint Y) = 0 :=
    Order.coheight_eq_zero.mpr fun y _ => genericPoint_specializes y
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwE
  have hs : E.genericPoint ⤳ w := specializes_iff_mem_closure.mpr hwE
  have h2 : Order.coheight E.genericPoint ≤ Order.coheight w := Order.coheight_anti hs
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
  rw [h0] at h1
  have := h2.trans h1
  norm_num at this

/-- **No negative contraction of fibre type.** If `(Y, C)` has a nef weak model over a separated
base `S`, then `K_Y + C` admits no negative extremal contraction `f : Y ⟶ V` over `S` with
`dim V < dim Y`. -/
private theorem false_of_isNefWeakModel_of_lt {Y Z S V : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} [QuasiCompact sZ] {sS : S ⟶ Spec (.of k)}
    [IsSeparated sS] {πY : Y ⟶ S} {πZ : Z ⟶ S} {KY : Divisor Y} {C : RDivisor Y}
    {φ : Y.RationalMap Z} (hφ : MMP.Fourfold.IsNefWeakModel sY sZ sS πY πZ KY C φ)
    {sV : V ⟶ Spec (.of k)} (πV : V ⟶ S) (f : Y ⟶ V)
    (hf : IsNegativeExtremalContraction k sY sV (logCanonicalDivisor KY C) f)
    (hfV : f ≫ πV = πY) (hdim : topologicalKrullDim V < topologicalKrullDim Y) : False := by
  obtain ⟨W, _, _, _, sW, p, q, h, hW, hWs, hpY, hqZ, hp, hq, hpb, hqb, hinv, hhq, GY, GZ, hGY,
    hGZ, hA, -⟩ := hφ.exists_resolution
  have hYv := hφ.isNormalVariety_source
  have hZv := hφ.isNormalVariety_target
  have : LocallyOfFiniteType sY := hYv.1.toLocallyOfFiniteType
  have : QuasiCompact sY := hYv.1.toQuasiCompact
  have : IsSeparated sY := hYv.1.toIsSeparated
  have : IsProper sY :=
    isProper_of_isProjectiveMorphism sY hφ.isProjectiveVariety_source.isProjective
  have : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  have : IsSeparated sZ := hZv.1.toIsSeparated
  have : LocallyOfFiniteType sW := hW.toLocallyOfFiniteType
  have : QuasiCompact sW := hW.toQuasiCompact
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  have : IsDominant p := hpb.isDominant
  have := MMP.Fourfold.isSeparated_terminal sS
  have hpq : p ≫ πY = q ≫ πZ := comp_eq_comp_of_isOver πY πZ hφ.isOver p q h hinv hhq
  have hBc : IsClosed (p '' ((GY - GZ).supp : Set W)) :=
    p.isClosedMap _ (DivisorWithCoeffs.isClosed_supp _)
  have hηB := genericPoint_notMem_image_supp hYv.1 p (by rw [hpY]; exact hW) hpb (GY - GZ)
  have := isDominant_of_isContraction hf.isContraction
  have : IsProper f := hf.isContraction.isProper
  obtain ⟨Γ, hΓ, hΓB⟩ := exists_properCurve_isContractedBy_of_lt hYv.1
    hf.isNormalVariety_target.1 f hf.isContraction.comp_eq hdim hBc hηB
  obtain ⟨m, r, Ls, x, hx, hxneg⟩ :=
    exists_isRIntersectionNumber_neg f hf.isRelativelyAntiAmple Γ hΓ
  have hΓS : Γ.IsContractedBy πY := fun y hy => by
    rw [← hfV, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ y hy]
  have := nonneg_of_isRIntersectionNumber_of_resolution hWs p q hpY hqZ hpq hφ.isRelativelyNef
    hGY hGZ hA Γ hΓS hΓB hx
  linarith

end PartThree

section PartTwo

variable {k : Type u} [Field k]

open CategoryTheory.Limits

/-- The exceptional set `Ex(f)` (points with no neighbourhood on which `f` is an open immersion)
is contained in the complement of the preimage of the biregular locus of `f`. -/
private theorem exceptionalSet_subset {X Y : Scheme.{u}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hyM
  apply hy
  have : IsIso (f ∣_ biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ biregularLocus f, ?_, ?_⟩
  · by_contra h
    exact hyM (MMP.Mori.mem_exceptionalSet.mpr h)
  · rw [← morphismRestrict_ι]
    infer_instance

/-- A prime divisor of `Y` whose generic point is outside `Ex(f)` is not `f`-exceptional. -/
private theorem not_isExceptional_of_notMem_exceptionalSet {Y Y' : Scheme.{u}} [IsReduced Y]
    [IsSeparated (Y' ↘ ⊤_ Scheme)] (f : Y ⟶ Y') (G : MMP.Mori.PrimeDivisor Y)
    (hG : G.genericPoint ∉ MMP.Flips.exceptionalSet f) :
    ¬ MMP.Mori.RationalMap.IsExceptional f.toRationalMap G := by
  have hco : Order.coheight (f G.genericPoint) = 1 := by
    rw [coheight_map_of_notMem_exceptionalSet hG,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact SamePrimes.not_isExceptional_of_transformPrimeDivisor_eq_some
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f G
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco)).mpr
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm)

/-- The generic point of a prime divisor `G` of `Y` is not the image of a point of the support of
a divisor `A` on `W` along a birational morphism `p : W ⟶ Y`, if `A` vanishes along the prime
divisor `P₀` of `W` over `G`: a point of `W` over `η_G` has coheight at most one, so it is the
generic point of a prime divisor, which is `P₀`. -/
private theorem genericPoint_notMem_image_supp_of_coeff_eq_zero {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : AlgebraicGeometry.IsVariety k sY) (p : W ⟶ Y)
    (hW : AlgebraicGeometry.IsVariety k (p ≫ sY)) [IsSeparated p] (hpb : IsBirationalMorphism p)
    {A : RDivisor W} (G : MMP.Mori.PrimeDivisor Y) (P₀ : MMP.Mori.PrimeDivisor W)
    (hP₀ : p P₀.genericPoint = G.genericPoint) (hA : A.coeff P₀ = 0) :
    G.genericPoint ∉ p '' (A.supp : Set W) := by
  rintro ⟨w, hw, hpw⟩
  obtain ⟨Q, hQ, hwQ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hw
  have : IsDominant p := hpb.isDominant
  have hdim := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hpb
  have h1 := coheight_le_coheight_map sY (p ≫ sY) hY hW p rfl hdim.symm w
  rw [hpw, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h1
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hwQ
  have hs : Q.genericPoint ⤳ w := specializes_iff_mem_closure.mpr hwQ
  have hQw : Q.genericPoint = w := by
    by_contra hne
    have hle : w ≤ Q.genericPoint := Scheme.le_iff_specializes.mpr hs
    have hlt : w < Q.genericPoint := lt_of_le_not_ge hle fun h' =>
      hne (hs.antisymm (Scheme.le_iff_specializes.mp h')).eq
    have h2 := Order.coheight_add_one_le hlt
    rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
    have h3 := h2.trans h1
    norm_num at h3
  have hQP : P₀.genericPoint = Q.genericPoint :=
    Crepant.eq_of_apply_eq_of_coheight_le_one p hpb.functionFieldMap_bijective
      (by rw [hQw, hpw, hP₀]) (by rw [hP₀]; exact Crepant.coheight_genericPoint_le_one G)
  obtain rfl := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hQP
  exact hQ hA

end PartTwo

section RationalMapAlgebra

/-- **Cancelling a birational map on the right.** If `g` has an inverse, two dominant rational
maps `χ₁`, `χ₂` with `g ∘ χ₁ = g ∘ χ₂` are equal. -/
private theorem eq_of_comp_eq_comp_right {X A B : Scheme.{u}} [IsIntegral X] [IsIntegral A]
    [IsIntegral B] {g : A.RationalMap B} [g.IsDominant] {gi : B.RationalMap A}
    (hg : RationalMap.IsInverse g gi) {χ₁ χ₂ : X.RationalMap A} [χ₁.IsDominant] [χ₂.IsDominant]
    (h : χ₁.comp g = χ₂.comp g) : χ₁ = χ₂ := by
  have h1 : g.comp gi = Scheme.RationalMap.id A := Crepant.comp_eq_id_of_isInverse hg
  calc χ₁ = χ₁.comp (Scheme.RationalMap.id A) := (Scheme.RationalMap.comp_id χ₁).symm
    _ = χ₁.comp (g.comp gi) := by rw [h1]
    _ = (χ₁.comp g).comp gi := (Scheme.RationalMap.comp_assoc _ _ _).symm
    _ = (χ₂.comp g).comp gi := Crepant.comp_eq_comp_of_eq h gi
    _ = χ₂.comp (g.comp gi) := Scheme.RationalMap.comp_assoc _ _ _
    _ = χ₂ := by rw [h1, Scheme.RationalMap.comp_id]

/-- **Cancelling a birational map on the left.** If `g` has a dominant inverse, two rational maps
`ψ₁`, `ψ₂` with `ψ₁ ∘ g = ψ₂ ∘ g` are equal. -/
private theorem eq_of_comp_eq_comp_left {A B T : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    {g : A.RationalMap B} [g.IsDominant] {gi : B.RationalMap A} [gi.IsDominant]
    (hg : RationalMap.IsInverse g gi) {ψ₁ ψ₂ : B.RationalMap T} (h : g.comp ψ₁ = g.comp ψ₂) :
    ψ₁ = ψ₂ := by
  have h1 : gi.comp g = Scheme.RationalMap.id B := Crepant.comp_eq_id_of_isInverse hg.symm
  calc ψ₁ = (Scheme.RationalMap.id B).comp ψ₁ := (Scheme.RationalMap.id_comp ψ₁).symm
    _ = (gi.comp g).comp ψ₁ := Crepant.comp_eq_comp_of_eq h1.symm ψ₁
    _ = gi.comp (g.comp ψ₁) := Scheme.RationalMap.comp_assoc _ _ _
    _ = gi.comp (g.comp ψ₂) := by rw [h]
    _ = (gi.comp g).comp ψ₂ := (Scheme.RationalMap.comp_assoc _ _ _).symm
    _ = (Scheme.RationalMap.id B).comp ψ₂ := Crepant.comp_eq_comp_of_eq h1 ψ₂
    _ = ψ₂ := Scheme.RationalMap.id_comp ψ₂

/-- A morphism inducing a birational map is dominant as a rational map. -/
private theorem isDominant_toRationalMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f] :
    f.toRationalMap.IsDominant := by
  change f.toPartialMap.toRationalMap.IsDominant
  infer_instance

end RationalMapAlgebra

section CommonModelOver

variable {k : Type u} [Field k]

end CommonModelOver

section StepModel

open CategoryTheory.Limits

end StepModel

section ExceptionalPrime

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- A prime divisor `F` of `Y` whose image `g(η_F)` has coheight one in the normal variety `X`
is not exceptional over `X`. -/
private theorem not_isExceptionalPrimeDivisor {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (F : MMP.Mori.PrimeDivisor Y) (hF : Order.coheight (g F.genericPoint) = 1) :
    ¬ IsExceptionalPrimeDivisor sX g F := by
  rintro ⟨hY, hg, hp, hexc⟩
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  unfold ProperDivisorOver.IsExceptional at hexc
  rw [ProperDivisorOver.center_eq_toDivisorOver_center,
    DivisorOver.center_eq_closure_genericPoint, hn] at hexc
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  have h2 := (withBot_add_two_le_iff hd).mp hexc
  change 2 ≤ Order.coheight (g F.genericPoint) at h2
  rw [hF] at h2
  exact absurd h2 (by decide)

/-! ### Intersection numbers -/

end ExceptionalPrime

section PartOne

variable {k : Type u} [Field k]

open CategoryTheory.Limits

/-- An inverse `h` of a proper birational morphism `p` has a representative defined at the
generic point of every prime divisor `R`, sending it to the generic point of the prime divisor of
`W` over `R`. -/
private theorem exists_rep_apply_eq_of_isInverse {X W : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsSeparated (X ↘ ⊤_ Scheme)]
    (p : W ⟶ X) [IsProper p] [IsSeparated p] (hpb : IsBirationalMorphism p)
    {h : X.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h)
    (R : MMP.Mori.PrimeDivisor X) (RW : MMP.Mori.PrimeDivisor W)
    (hRW : p RW.genericPoint = R.genericPoint) :
    ∃ (g₀ : X.PartialMap W) (_ : g₀.toRationalMap = h) (hR : R.genericPoint ∈ g₀.domain),
      g₀.hom ⟨R.genericPoint, hR⟩ = RW.genericPoint := by
  have : IsDominant p := hpb.isDominant
  obtain ⟨g₀, hg₀, hRg⟩ := Crepant.exists_rep_mem_domain hinv R
  have he : g₀.hom ≫ p = g₀.domain.ι ≫ 𝟙 X :=
    Crepant.hom_eq_of_toRationalMap_eq g₀.dense_domain <| by
      rw [Crepant.toRationalMap_ι_comp]
      change (g₀.compHom p).toRationalMap = _
      rw [Scheme.RationalMap.compHom_toRationalMap, hg₀, Crepant.compHom_eq_of_isInverse hinv]
  have hw : p (g₀.hom ⟨R.genericPoint, hRg⟩) = R.genericPoint := by
    calc p (g₀.hom ⟨R.genericPoint, hRg⟩) = (g₀.hom ≫ p) ⟨R.genericPoint, hRg⟩ :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = R.genericPoint := by rw [he]; simp
  exact ⟨g₀, hg₀, hRg, (Crepant.eq_of_apply_eq_of_coheight_le_one p hpb.functionFieldMap_bijective
    (hw.trans hRW.symm) (by rw [hRW]; exact Crepant.coheight_genericPoint_le_one R)).symm⟩

/-- **Transforms of prime divisors through a model.** Let `p : W ⟶ X` be a proper birational
morphism with inverse `h`, and `ψ = q ∘ h` for a morphism `q : W ⟶ T`. If `R_W ⊆ W` lies over
the prime divisor `R` of `X`, then `ψ_* R = F` exactly when `q(η_{R_W}) = η_F`. -/
private theorem transformPrimeDivisor_eq_some_iff_of_isInverse {X W T : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (T ↘ ⊤_ Scheme)]
    (p : W ⟶ X) [IsProper p] [IsSeparated p] (hpb : IsBirationalMorphism p)
    {h : X.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h) (q : W ⟶ T)
    {ψ : X.RationalMap T} (hψ : h.compHom q = ψ) (R : MMP.Mori.PrimeDivisor X)
    (RW : MMP.Mori.PrimeDivisor W) (hRW : p RW.genericPoint = R.genericPoint)
    (F : MMP.Mori.PrimeDivisor T) :
    RationalMap.transformPrimeDivisor ψ R = some F ↔ q RW.genericPoint = F.genericPoint := by
  obtain ⟨g₀, hg₀, hRg, hwRW⟩ := exists_rep_apply_eq_of_isInverse p hpb hinv R RW hRW
  have hgq : (g₀.compHom q).toRationalMap = ψ := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg₀, hψ]
  constructor
  · intro hRF
    have h1 := Crepant.genericPoint_eq_of_transformPrimeDivisor_eq_some hRF (g₀.compHom q) hgq hRg
    rw [h1, ← hwRW]
    rfl
  · intro hq
    refine SamePrimes.transformPrimeDivisor_eq_some_of_genericPoint_eq (g₀.compHom q) hgq hRg ?_
    change F.genericPoint = q (g₀.hom ⟨R.genericPoint, hRg⟩)
    rw [hwRW, hq]

/-- The linear extensions of two partial maps on prime divisors compose to the linear extension
of their composite. -/
private theorem mapPrimeDivisors_mapPrimeDivisors {X Y T : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (χ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (ψ : MMP.Mori.PrimeDivisor Y → Option (MMP.Mori.PrimeDivisor T))
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors ψ (DivisorWithCoeffs.mapPrimeDivisors χ D) =
      DivisorWithCoeffs.mapPrimeDivisors (fun G => (χ G).bind ψ) D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, map_add, hD, hD']
  | single G r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases χ G with _ | D'
    · simp
    · simp [DivisorWithCoeffs.mapPrimeDivisors_single]

end PartOne

/-! ### Program steps

The step machinery of a `(K + C)`-program over `S`: the step map of a step, in the form of the
weak-model step lemma, for any canonical divisor of the source. -/

namespace Kit

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori
open TopologicalSpace

/-! ### The flip as a birational map -/

section Points

variable {X Y : Scheme.{u}}

/-- The restriction `f ∣_ V` followed by `V ⊆ Y` is `f` on `f⁻¹(V)`. -/
private theorem apply_ι_morphismRestrict (f : X ⟶ Y) (V : Y.Opens) (p : (f ⁻¹ᵁ V).toScheme) :
    V.ι ((f ∣_ V) p) = f ((f ⁻¹ᵁ V).ι p) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, `f` is injective. -/
private theorem eq_of_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x₁ x₂ : X}
    (h₁ : f x₁ ∈ V) (h₂ : f x₂ ∈ V) (h : f x₁ = f x₂) : x₁ = x₂ := by
  let p₁ : (f ⁻¹ᵁ V).toScheme := ⟨x₁, h₁⟩
  let p₂ : (f ⁻¹ᵁ V).toScheme := ⟨x₂, h₂⟩
  have : (f ∣_ V) p₁ = (f ∣_ V) p₂ :=
    V.ι.isOpenEmbedding.injective ((apply_ι_morphismRestrict f V p₁).trans
      (h.trans (apply_ι_morphismRestrict f V p₂).symm))
  exact congrArg Subtype.val ((f ∣_ V).isOpenEmbedding.injective this)

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, every point of `V` is in the image
of `f`. -/
private theorem exists_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {y : Y}
    (hy : y ∈ V) : ∃ x, f x = y := by
  let q : V.toScheme := ⟨y, hy⟩
  refine ⟨(f ⁻¹ᵁ V).ι (inv (f ∣_ V) q), ?_⟩
  rw [← apply_ι_morphismRestrict, ← Scheme.Hom.comp_apply (inv (f ∣_ V)) (f ∣_ V), IsIso.inv_hom_id]
  rfl

/-- Over an open `V` such that `f ∣_ V` is an isomorphism, `f` preserves coheights. -/
private theorem coheight_apply_eq (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x : X}
    (hx : f x ∈ V) : Order.coheight (f x) = Order.coheight x :=
  MMP.Positivity.coheight_map_of_mem_biregularLocus f
    ((isBiregular_iff_le_biregularLocus.mp ‹IsIso (f ∣_ V)›) hx)

/-- Prime divisors correspond over `V`: if `f` and `f⁺` are isomorphisms over `V`, every prime
divisor `P⁺` of `X⁺` lying over `V` has a prime divisor `P` of `X` over the same point of `Y`. -/
private theorem exists_primeDivisor_genericPoint_eq {X' : Scheme.{u}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (P' : MMP.Mori.PrimeDivisor X')
    (hP' : fp P'.genericPoint ∈ V) :
    ∃ P : MMP.Mori.PrimeDivisor X, f P.genericPoint = fp P'.genericPoint := by
  obtain ⟨x, hx⟩ := exists_apply_eq f V hP'
  have hxV : f x ∈ V := hx ▸ hP'
  have hco : Order.coheight x = 1 := by
    rw [← coheight_apply_eq f V hxV, hx, coheight_apply_eq fp V hP',
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco,
    (congrArg f (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco)).trans hx⟩

end Points

section Small

variable {X Z : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- **A small contraction is an isomorphism off codimension two.** For a small birational
contraction `f : X ⟶ Z` there are closed subsets `V ⊆ X` and `W ⊆ Z` of points of coheight at
least two, with `X ∖ V ⊆ f⁻¹(Z ∖ W)`, such that `f` is an isomorphism over `Z ∖ W`: the section of
the separated `f⁻¹(Z ∖ W) ⟶ Z ∖ W` given by `X ∖ V` is a closed immersion, so `X ∖ V` is
open and closed in the irreducible `f⁻¹(Z ∖ W)`. -/
private theorem exists_closeds_isIso_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f) :
    ∃ (V : Closeds X) (W : Closeds Z), (∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) ∧
      (∀ z ∈ (W : Set Z), 2 ≤ Order.coheight z) ∧ V.compl ≤ f ⁻¹ᵁ W.compl ∧
      IsIso (f ∣_ W.compl) := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := hf.exists_isIso
  have hV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV
  have hW' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW
  refine ⟨V, W, hV', hW', h, ?_⟩
  haveI : IsProper f := hf.isProper
  set U := f ⁻¹ᵁ W.compl
  set g := f ∣_ W.compl
  set j := X.homOfLE h
  have hjg : j ≫ g = f.resLE W.compl V.compl h := rfl
  set s := inv (f.resLE W.compl V.compl h) ≫ j
  have hs : s ≫ g = 𝟙 _ := by simp [s, hjg]
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s g
  have hj : j = f.resLE W.compl V.compl h ≫ s := by simp [s]
  haveI : IsClosedImmersion j := by rw [hj]; infer_instance
  -- `X ∖ V` is nonempty: it contains the generic point
  have hgen : genericPoint X ∈ (V.compl : Set X) := by
    intro hgV
    have := hV' (genericPoint X) hgV
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at this
    exact absurd this (by decide)
  haveI : Nonempty U := ⟨⟨_, h hgen⟩⟩
  have hclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range j).Nonempty := ⟨_, ⟨⟨_, hgen⟩, rfl⟩⟩
  have hrange : Set.range j = Set.univ := (isClopen_iff.mp hclopen).resolve_left hne.ne_empty
  haveI : Surjective j := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  have hg : g = inv j ≫ f.resLE W.compl V.compl h := by rw [← hjg]; simp
  change IsIso g
  rw [hg]
  infer_instance

variable [IsLocallyNoetherian X] [IsNormal X]

/-- Points of coheight at most one of the base lie in the biregular locus of a small
contraction. -/
private theorem mem_biregularLocus_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    {z : Z} (hz : Order.coheight z ≤ 1) : z ∈ biregularLocus f := by
  obtain ⟨V, W, -, hW, -, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hzW : z ∈ (W.compl : Set Z) := fun h => absurd ((hW z h).trans hz) (by decide)
  exact le_biregularLocus hiso hzW

/-- A small contraction maps the generic point of a prime divisor to a point of coheight one,
in its biregular locus. -/
private theorem coheight_map_genericPoint_of_isSmall {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (P : MMP.Mori.PrimeDivisor X) :
    Order.coheight (f P.genericPoint) = 1 ∧ f P.genericPoint ∈ biregularLocus f := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hPV : P.genericPoint ∈ (V.compl : Set X) := fun hP =>
    absurd (hV _ hP) (by rw [P.coheight_genericPoint]; decide)
  have hb : f P.genericPoint ∈ biregularLocus f := le_biregularLocus hiso (h hPV)
  exact ⟨by rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb,
    P.coheight_genericPoint], hb⟩

end Small

section SmallPair

variable {X X' Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- Every prime divisor of `X` corresponds, through `Z`, to a prime divisor of `X⁺`. -/
private theorem exists_primeDivisor_map_eq_of_isSmall {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint = f P.genericPoint := by
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  have hb := mem_biregularLocus_of_isSmall hfp hz.le
  obtain ⟨x', hx'⟩ :=
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj (f P.genericPoint)
  have hc : Order.coheight x' = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hx' ▸ hb), hx', hz]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hc,
    (congrArg fp (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x' hc)).trans hx'⟩

/-- The strict transform `(f⁺)⁻¹_* f_* D` across two small contractions has, at the prime divisor
`P⁺` corresponding to `P`, the coefficient of `D` at `P`. -/
private theorem flipTransform_apply_of_isSmall [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hPP' : fp P'.genericPoint = f P.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI : IsProper f := hf.isProper
  haveI := hfb.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  obtain ⟨hz, -⟩ := coheight_map_genericPoint_of_isSmall hf P
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz
  have hQ : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz).symm
  have := Q.isDiscreteValuationRing_localRing
  exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj hQ (hPP'.trans hQ)
    (mem_biregularLocus_of_isSmall hfp (hQ ▸ hz).le) D

/-- The strict transform commutes with real multiples of integral divisors. -/
private theorem flipTransform_smul_toRDivisor [IsIntegral Z] (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f) (c : ℝ)
    (G : Divisor X) :
    flipTransform f fp (c • Divisor.toRDivisor G) =
      c • Divisor.toRDivisor (flipTransform f fp G) := by
  ext P'
  obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall hfp hf P'
  have h1 := flipTransform_apply_of_isSmall hZ hf hfp hfb hP.symm (c • Divisor.toRDivisor G)
  have h2 := flipTransform_apply_of_isSmall hZ hf hfp hfb hP.symm G
  simp only [DivisorWithCoeffs.coeff_apply] at h1 ⊢
  rw [h1]
  change c * (Divisor.toRDivisor G).coeff P = c * (Divisor.toRDivisor (flipTransform f fp G)).coeff P'
  rw [Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply,
    DivisorWithCoeffs.coeff_apply, h2]

end SmallPair

/-! ### The two transforms of divisors -/

section Transforms

/-- The coefficients of `(f⁺)⁻¹_* f_* D`: if `f` and `f⁺` are isomorphisms over `V`, over which
lie the points of codimension one of `X`, the coefficient of `P⁺` is that of the prime divisor `P`
of `X` over the same point of `Y`. -/
private theorem flipTransform_apply {k : Type u} [Field k] {X X' Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY)
    {f : X ⟶ Y} {fp : X' ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) [IsProper f]
    (hf : IsBirationalMorphism f) (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hV : f P.genericPoint ∈ V :=
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  have hV' : fp P'.genericPoint ∈ V := hPP ▸ hV
  have hco : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [coheight_apply_eq fp V hV', AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = fp P'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have hbir : fp P'.genericPoint ∈ biregularLocus fp :=
    (isBiregular_iff_le_biregularLocus.mp ‹IsIso (fp ∣_ V)›) hV'
  have huniq : ∀ Q₁ : MMP.Mori.PrimeDivisor Y, inverseTransformPrimeDivisor fp Q₁ = some P' → Q₁ = Q := by
    intro Q₁ hQ₁
    obtain ⟨h1, -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ₁
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.symm.trans hQ.symm)
  have h1 : inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := X)
      f.toRationalMap D) P' = MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        hQ.symm hbir) huniq _
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hf Q
  change inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := X)
    f.toRationalMap D) P' = _
  rw [h1, htr]
  have hE : f E.genericPoint = f P.genericPoint := hEQ.trans (hQ.trans hPP.symm)
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_apply_eq f V (hE ▸ hV) hV hE)]

/-- If `f⁺` is an isomorphism over `U`, two morphisms into `(f⁺)⁻¹(U)` which agree after
composing with `f⁺` are equal. -/
private theorem eq_of_comp_eq {T X' Y : Scheme.{u}} (fp : X' ⟶ Y) (U : Y.Opens)
    [IsIso (fp ∣_ U)] (a b : T ⟶ X') (ha : Set.range a ⊆ (fp ⁻¹ᵁ U : Set X'))
    (hb : Set.range b ⊆ (fp ⁻¹ᵁ U : Set X')) (h : a ≫ fp = b ≫ fp) : a = b := by
  have ha' : Set.range a ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  have hb' : Set.range b ⊆ Set.range (fp ⁻¹ᵁ U).ι := by rwa [Scheme.Opens.range_ι]
  rw [← IsOpenImmersion.lift_fac _ _ ha', ← IsOpenImmersion.lift_fac _ _ hb']
  congr 1
  rw [← cancel_mono (fp ∣_ U), ← cancel_mono U.ι, Category.assoc, Category.assoc,
    morphismRestrict_ι, ← Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
    IsOpenImmersion.lift_fac, h]

/-- A morphism `a : T ⟶ X'` with `a ≫ f⁺ = c ≫ f` for some `c` landing in `f⁻¹(U)` lands in
`(f⁺)⁻¹(U)`. -/
private theorem range_subset_of_comp_eq {T X X' Y : Scheme.{u}} {f : X ⟶ Y} {fp : X' ⟶ Y}
    {U : Y.Opens} (a : T ⟶ X') (c : T ⟶ X) (hc : ∀ t, c t ∈ f ⁻¹ᵁ U) (h : a ≫ fp = c ≫ f) :
    Set.range a ⊆ (fp ⁻¹ᵁ U : Set X') := by
  rintro _ ⟨t, rfl⟩
  change fp (a t) ∈ U
  rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  exact hc t

/-- Let `f⁺` be an isomorphism over `U`. A partial map `p : X ⇀ X'` defined inside `f⁻¹(U)` with
`f⁺ ∘ p = f` represents every rational map `g` with `f⁺ ∘ g = f`. -/
private theorem toRationalMap_eq_of_comp_eq {X X' Y : Scheme.{u}} {f : X ⟶ Y} (fp : X' ⟶ Y)
    (U : Y.Opens) [IsIso (fp ∣_ U)] (p : X.PartialMap X') (hpU : p.domain ≤ f ⁻¹ᵁ U)
    (hp : p.hom ≫ fp = p.domain.ι ≫ f) (g : X.PartialMap X')
    (hg : g.toRationalMap.compHom fp = f.toPartialMap.toRationalMap) :
    p.toRationalMap = g.toRationalMap := by
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at hg
  obtain ⟨W, hWd, hWl, _, hWe⟩ := hg
  replace hWl : W ≤ g.domain := hWl
  have h2 : W ⊓ p.domain ≤ g.domain := inf_le_left.trans hWl
  have hc : ∀ t, (W ⊓ p.domain).ι t ∈ f ⁻¹ᵁ U := fun t ↦ hpU t.2.2
  have ha : (X.homOfLE (inf_le_right : W ⊓ p.domain ≤ _) ≫ p.hom) ≫ fp =
      (W ⊓ p.domain).ι ≫ f := by
    rw [Category.assoc, hp, Scheme.homOfLE_ι_assoc]
  have hb : (X.homOfLE h2 ≫ g.hom) ≫ fp = (W ⊓ p.domain).ι ≫ f := by
    have hWe' : X.homOfLE hWl ≫ g.hom ≫ fp = X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom ≫ f := hWe
    rw [Category.assoc, ← X.homOfLE_homOfLE (inf_le_left : W ⊓ p.domain ≤ W) hWl,
      Category.assoc, hWe', Scheme.topIso_hom, ← Category.assoc, ← Category.assoc,
      Scheme.homOfLE_homOfLE, Scheme.homOfLE_ι]
  rw [Scheme.PartialMap.toRationalMap_eq_iff]
  exact ⟨_, hWd.inter_of_isOpen_left p.dense_domain W.isOpen, inf_le_right, h2,
    eq_of_comp_eq fp U _ _ (range_subset_of_comp_eq _ _ hc ha)
      (range_subset_of_comp_eq _ _ hc hb) (ha.trans hb.symm)⟩

/-- A rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`, where `f` and `f⁺` are isomorphisms over a
`V` whose preimage in `X` is dense, is represented on `f⁻¹(V)` by `(f⁺)⁻¹ ∘ f`. -/
private theorem exists_partialMap {X X' Y : Scheme.{u}} {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hd : Dense (f ⁻¹ᵁ V : Set X))
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) :
    ∃ g : X.PartialMap X', g.domain = f ⁻¹ᵁ V ∧ g.toRationalMap = φ ∧
      g.hom ≫ fp = g.domain.ι ≫ f ∧ ∀ t, fp (g.hom t) ∈ V := by
  let g : X.PartialMap X' := ⟨f ⁻¹ᵁ V, hd, (f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι⟩
  have hg : g.hom ≫ fp = g.domain.ι ≫ f := by
    change ((f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι) ≫ fp = (f ⁻¹ᵁ V).ι ≫ f
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
      morphismRestrict_ι]
  refine ⟨g, rfl, ?_, hg, fun t => ?_⟩
  · obtain ⟨g₀, rfl⟩ := Quotient.exists_rep φ
    exact toRationalMap_eq_of_comp_eq fp V g le_rfl hg g₀ hφ
  · change fp ((fp ⁻¹ᵁ V).ι ((inv (fp ∣_ V)) ((f ∣_ V) t))) ∈ V
    exact ((inv (fp ∣_ V)) ((f ∣_ V) t)).2

/-- The transform of a prime divisor `P` under a rational map represented by `g'`, defined at
`η_P`, is the closure of `g'(η_P)`. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : MMP.Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (MMP.Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If `φ_* P = E` and `φ` is represented by `g'` near `η_P`, then `η_E = g'(η_P)`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (h : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := MMP.Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If `φ` is represented by `g'` near `η_P` and `η_E = g'(η_P)`, then `φ_* P = E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : MMP.Mori.PrimeDivisor X}
    {E : MMP.Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨MMP.Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : MMP.Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [MMP.Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- The coefficients of `φ_* D` for a rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`, when `f` and
`f⁺` are isomorphisms over `V`, over which lie the points of codimension at most one of `X`: the
coefficient of `P⁺` is that of the prime divisor `P` of `X` over the same point of `Y`. -/
private theorem transformDivisor_apply {X X' Y : Scheme.{u}} [IsIntegral X]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D P' = D P := by
  have hgen : Order.coheight (genericPoint X) ≤ 1 :=
    (Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z).trans_le zero_le_one
  obtain ⟨g, hgd, hgφ, hgc, hgV⟩ :=
    exists_partialMap fp V ((f ⁻¹ᵁ V).isOpen.dense ⟨_, hXV _ hgen⟩) hφ
  have hmem : ∀ Q : MMP.Mori.PrimeDivisor X, Q.genericPoint ∈ g.domain := fun Q => by
    rw [hgd]; exact hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le
  have hval : ∀ Q : MMP.Mori.PrimeDivisor X,
      fp (g.hom ⟨Q.genericPoint, hmem Q⟩) = f Q.genericPoint := fun Q =>
    congrArg (fun h => h.base ⟨Q.genericPoint, hmem Q⟩) hgc
  have hPV : ∀ Q : MMP.Mori.PrimeDivisor X, f Q.genericPoint ∈ V := fun Q =>
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_eq_some_of_genericPoint_eq g hgφ (hmem P) ?_) (fun P₁ hP₁ => ?_) D
  · exact eq_of_apply_eq fp V (hPP ▸ hPV P) (hgV _) (hPP.symm.trans (hval P).symm)
  · have h1 := genericPoint_eq_of_transformPrimeDivisor_eq_some hP₁ g hgφ (hmem P₁)
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq f V (hPV P₁) (hPV P) (by rw [← hval P₁, ← h1, ← hPP]))

/-- **The flip transforms divisors as `(f⁺)⁻¹_* f_*`.** If `f` and `f⁺` are isomorphisms over `V`,
over which lie the points of codimension at most one of `X` and of `X⁺`, then
`φ_* D = (f⁺)⁻¹_* f_* D` for every rational map `φ : X ⤏ X⁺` with `f⁺ ∘ φ = f`. -/
private theorem transformDivisor_eq_flipTransform {k : Type u} [Field k] {X X' Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsSeparated (X' ↘ ⊤_ Scheme)]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {f : X ⟶ Y} {fp : X' ⟶ Y}
    (hX : IsNormalVariety k (f ≫ sY)) [IsProper f] (hf : IsBirationalMorphism f) (V : Y.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {φ : X.RationalMap X'}
    (hφ : φ.compHom fp = f.toRationalMap) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor φ D = flipTransform f fp D := by
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq f fp V P'
    (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le)
  rw [transformDivisor_apply fp V hXV hφ hP, flipTransform_apply hY hX hf V hXV hP]

end Transforms

section CommonModel

/-- A birational morphism `f : X ⟶ Y` restricts to an isomorphism of a dense open of `X` onto a
dense open of `Y`, under which it is the inclusion of that open. -/
private theorem exists_partialIso_isOver {X Y : Scheme.{0}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) : ∃ e : X.PartialIso Y, e.IsOver f (𝟙 Y) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨W, hW, hWl, hWr, heq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at heq
  have hWl' : W ≤ e.source := hWl
  refine ⟨e.restrictSource W hW hWl', ?_⟩
  have h1 : (Scheme.Opens.isoOfLE hWl').inv ≫ (e.source.ι ⁻¹ᵁ W).ι = X.homOfLE hWl' := by
    rw [← cancel_mono e.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  have h2 : X.homOfLE hWr ≫ X.topIso.hom = W.ι := by
    simp only [Scheme.topIso_hom]
    exact Scheme.homOfLE_ι X hWr
  change ((Scheme.Opens.isoOfLE hWl').inv ≫ (e.iso.hom.isoImage (e.source.ι ⁻¹ᵁ W)).hom ≫
    (e.target.ι.isoImage (e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W)).hom) ≫
    (e.target.ι ''ᵁ e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W).ι ≫ 𝟙 Y = W.ι ≫ f
  rw [Category.comp_id, Category.assoc, Category.assoc, Scheme.Hom.isoImage_hom_ι,
    Scheme.Hom.isoImage_hom_ι_assoc, ← Category.assoc, h1]
  exact heq.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) h2))

/-- For birational morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y`, the birational map
`φ = f'⁻¹ ∘ f : X ⇢ X'` satisfies `f' ∘ φ = f`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : MMP.Mori.RationalMap X X', φ.IsBirational ∧ φ.compHom f' = f.toRationalMap := by
  obtain ⟨e₁, h₁⟩ := exists_partialIso_isOver hf
  obtain ⟨e₂, h₂⟩ := exists_partialIso_isOver hf'
  set e := e₁.trans e₂.symm
  have h : e.IsOver f f' := h₁.trans h₂.symm
  refine ⟨e.toRationalMap, RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨e.source, e.dense_source, le_rfl,
    le_top, ?_⟩
  change X.homOfLE le_rfl ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, h]
  simp

end CommonModel

/-! ### `ℚ`-factorial varieties and presentations -/

/-- An `ℝ`-divisor is the sum of its prime components with their coefficients. -/
private theorem eq_sum_coeff_smul_single {W : Scheme.{0}} (G : RDivisor W) :
    G = ∑ j : Fin G.support.card, G.coeff (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) •
      Divisor.toRDivisor
        (Finsupp.single (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) 1) := by
  classical
  have hsumFin : ∀ F : MMP.Mori.PrimeDivisor W → ℝ,
      ∑ j, F (G.support.equivFin.symm j) = ∑ Q ∈ G.support, F Q := fun F => by
    rw [← Finset.sum_coe_sort G.support]
    exact Equiv.sum_comp G.support.equivFin.symm (fun Q => F Q)
  refine DivisorWithCoeffs.ext' fun Q => ?_
  simp only [MMP.Flips.coeff_sum_smul_toRDivisor]
  have key : ∀ R : MMP.Mori.PrimeDivisor W,
      ((DivisorWithCoeffs.coeff (R := ℤ) (Finsupp.single R 1) Q : ℤ) : ℝ) =
        if R = Q then 1 else 0 := fun R => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp
  simp only [key, mul_ite, mul_one, mul_zero]
  rw [hsumFin (fun R => if R = Q then G.coeff R else 0), Finset.sum_ite_eq']
  by_cases hQ : Q ∈ G.support
  · simp [hQ]
  · simp only [hQ, if_false]
    rw [DivisorWithCoeffs.coeff_apply]
    exact Finsupp.notMem_support_iff.mp hQ

section QFactorial

open MMP.Flips

variable {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- Dividing the coefficient by `m` undoes the multiple `m D`:
`(c / m) • (m D) = c • D` for `m > 0`. -/
private theorem div_smul_toRDivisor_zsmul {X : Scheme.{u}} (c : ℝ) {m : ℕ} (hm : 0 < m)
    (D : Divisor X) :
    (c / m) • Divisor.toRDivisor ((m : ℤ) • D) = c • Divisor.toRDivisor D := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast,
    div_mul_cancel₀ c (by exact_mod_cast hm.ne')]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor `G = ∑ g_P P` is the combination
`∑ (g_P / m_P) (m_P P)` of Cartier divisors, where `m_P P` is Cartier. -/
private theorem exists_presentation_of_isQFactorial (hq : IsQFactorial sX) (G : RDivisor X) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      G = ∑ j, r j • Divisor.toRDivisor (L j) := by
  classical
  choose mq hmq hmqC using fun P : MMP.Mori.PrimeDivisor X => hq.2 (Finsupp.single P 1)
  set Pj : Fin G.support.card → MMP.Mori.PrimeDivisor X :=
    fun j => (G.support.equivFin.symm j : _)
  refine ⟨G.support.card, fun j => G.coeff (Pj j) / (mq (Pj j) : ℝ),
    fun j => (mq (Pj j) : ℤ) • Finsupp.single (Pj j) 1, fun j => hmqC _, ?_⟩
  conv_lhs => rw [eq_sum_coeff_smul_single G]
  exact Finset.sum_congr rfl fun j _ => (div_smul_toRDivisor_zsmul _ (hmq _) _).symm

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isQFactorial (hq : IsQFactorial sX) (G : RDivisor X) :
    IsCartierCombination G := by
  obtain ⟨m, r, L, hL, hG⟩ := exists_presentation_of_isQFactorial hq G
  exact ⟨m, r, L, hL, by rw [hG]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

end QFactorial

section FlipMap

variable {X Z X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- The points of codimension at most one of `X` lie over the open of `Z` over which both small
contractions are isomorphisms. -/
private theorem mem_biregularLocus_inf_of_isSmall (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) {x : X} (hx : Order.coheight x ≤ 1) :
    f x ∈ biregularLocus f ⊓ biregularLocus fp := by
  obtain ⟨V, W, hV, -, hVW, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hxV : x ∈ (V.compl : Set X) := fun h => absurd ((hV x h).trans hx) (by decide)
  have hb : f x ∈ biregularLocus f := le_biregularLocus hiso (hVW hxV)
  refine ⟨hb, mem_biregularLocus_of_isSmall hfp ?_⟩
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hb]
  exact hx

/-- If `f`, `f⁺` are isomorphisms over `V`, over which lie the points of codimension at most one
of `X`, a rational map `φ` with `f⁺ ∘ φ = f` carries a prime divisor `P` to the prime divisor
`P⁺` over the same point of `Z`. -/
private theorem transformPrimeDivisor_eq_some_of_map_eq {X X' Y : Scheme.{u}} [IsIntegral X]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {f : X ⟶ Y} (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)]
    [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (hPP : f P.genericPoint = fp P'.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor φ P = some P' := by
  have hgen : Order.coheight (genericPoint X) ≤ 1 :=
    (Order.coheight_eq_zero.mpr fun z _ ↦ genericPoint_specializes z).trans_le zero_le_one
  obtain ⟨g, hgd, hgφ, hgc, hgV⟩ :=
    exists_partialMap fp V ((f ⁻¹ᵁ V).isOpen.dense ⟨_, hXV _ hgen⟩) hφ
  have hmem : ∀ Q : MMP.Mori.PrimeDivisor X, Q.genericPoint ∈ g.domain := fun Q => by
    rw [hgd]; exact hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q).le
  have hval : ∀ Q : MMP.Mori.PrimeDivisor X,
      fp (g.hom ⟨Q.genericPoint, hmem Q⟩) = f Q.genericPoint := fun Q =>
    congrArg (fun h => h.base ⟨Q.genericPoint, hmem Q⟩) hgc
  have hPV : f P.genericPoint ∈ V :=
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  exact transformPrimeDivisor_eq_some_of_genericPoint_eq g hgφ (hmem P)
    (eq_of_apply_eq fp V (hPP ▸ hPV) (hgV _) (hPP.symm.trans (hval P).symm))

/-- **The flip as a birational map.** For small contractions `f : X ⟶ Z ⟵ X⁺ : f⁺` of normal
varieties there is a birational map `g = (f⁺)⁻¹ ∘ f : X ⤏ X⁺` over `Z`, which transforms divisors
as the strict transform `(f⁺)⁻¹_* f_*` and every prime divisor of `X⁺` is a transform. -/
private theorem exists_flipMap (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX')
    (hZ : IsNormalVariety ℂ sZ) (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp) :
    ∃ g : X.RationalMap X', MMP.Mori.RationalMap.IsBirational g ∧
      MMP.Flips.RationalMap.IsOver f fp g ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor g D = flipTransform f fp D) ∧
      ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformPrimeDivisor g P = some P' := by
  obtain ⟨g, hg, hgo⟩ := exists_isBirational_compHom_eq hfb hfpb
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal_of_isNormalVariety hX'
  haveI : IsIso (f ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
    isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI : IsIso (fp ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
    isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ biregularLocus f ⊓ biregularLocus fp :=
    fun x hx => mem_biregularLocus_inf_of_isSmall hf hfp hx
  have hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ biregularLocus f ⊓ biregularLocus fp :=
    fun x hx => by
      have := mem_biregularLocus_inf_of_isSmall hfp hf hx
      exact ⟨this.2, this.1⟩
  haveI : IsProper f := hf.isProper
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rw [hf.comp_eq]; exact hX
  refine ⟨g, hg, hgo, fun D => transformDivisor_eq_flipTransform hZ hXn hfb _ hXV hX'V hgo D,
    fun P' => ?_⟩
  obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq f fp _ P'
    (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le)
  exact ⟨P, transformPrimeDivisor_eq_some_of_map_eq fp _ hXV hgo hP⟩

end FlipMap

section CurveNormalization

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  have : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  have : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  have : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        have : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        have : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- An integral scheme proper over `k` is a `k`-variety. -/
private theorem isVariety_of_isProper {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    [hp : IsProper f] : AlgebraicGeometry.IsVariety k f :=
  { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
    toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have := isVariety_of_isProper (ν ≫ C.ι ≫ sX)
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

end CurveNormalization

/-! ### Numerical triviality over the base -/

section Numerical

open MMP.Flips

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

/-- The empty presentation computes `0 · C = 0`. -/
private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber ℂ sX 0 (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- Every presentation of an `ℝ`-Cartier divisor computes some value of `D · C`. -/
private theorem exists_isRIntersectionNumber {D : RDivisor X} (hD : IsCartierCombination D)
    (C : ProperCurve sX) : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX D r L C x := by
  obtain ⟨m, r, L, hL, hDeq⟩ := hD
  refine ⟨m, r, L, ∑ j, r j * (L j).degreeOn ℂ sX C.ι C.dim_le (hL j),
    isRIntersectionNumber_sum_degreeOn D r L hL ?_ C⟩
  rw [hDeq]
  simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]

/-- `ℝ`-Cartier divisors form a real vector space. -/
private theorem isCartierCombination_add_smul {D N : RDivisor X} (hD : IsCartierCombination D)
    (hN : IsCartierCombination N) (c : ℝ) : IsCartierCombination (D + c • N) := by
  obtain ⟨m, r, L, hL, rfl⟩ := hD
  obtain ⟨m', r', L', hL', rfl⟩ := hN
  refine ⟨m + m', Fin.append r (c • r'), Fin.append L L', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hL j
    · simpa using hL' j
  · rw [Fin.sum_univ_add, Finset.smul_sum]
    simp [smul_smul]

/-- A numerically trivial divisor computes `0` on every contracted curve. -/
private theorem eq_zero_of_isNumericallyTrivialOver {f : X ⟶ Y} {N : RDivisor X}
    (hN : IsNumericallyTrivialOver ℂ sX f N) {C : ProperCurve sX} (hC : C.IsContractedBy f)
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sX N r L C x) : x = 0 :=
  hN.2.2 C hC m r L x 0 Fin.elim0 Fin.elim0 0 hx (isRIntersectionNumber_zero C)

/-- Adding a multiple of a numerically trivial divisor does not change numerical classes. -/
private theorem isNumericallyEquivalentOver_add_smul {f : X ⟶ Y} {D N : RDivisor X}
    (hD : IsCartierCombination D) (hN : IsNumericallyTrivialOver ℂ sX f N) (c : ℝ) :
    IsNumericallyEquivalentOver ℂ sX f (D + c • N) D := by
  refine ⟨isCartierCombination_add_smul hD hN.1 c, hD,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  obtain ⟨m₃, r₃, L₃, x₃, h₃⟩ := exists_isRIntersectionNumber hN.1 C
  have h0 := eq_zero_of_isNumericallyTrivialOver hN hC h₃
  have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 D N r₂ L₂ r₃ L₃ x₂ x₃ 1 c h₂ h₃
  rw [one_smul] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ hsum, h0]
  ring

/-- A Cartier divisor linearly equivalent to `0` is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent [CompactSpace X]
    (f : X ⟶ Y) {D : Divisor X} (hD : D.IsCartier) (h : D.LinearlyEquivalent 0) :
    IsNumericallyTrivialOver ℂ sX f (Divisor.toRDivisor D) := by
  have hDc : IsCartierCombination (Divisor.toRDivisor D) :=
    ⟨1, fun _ => 1, fun _ => D, fun _ => hD, by simp [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  refine ⟨hDc, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩,
    fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
  have h₃ := isRIntersectionNumber_sum_degreeOn (Divisor.toRDivisor D) (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => D) (fun _ => hD) (by simp) C
  have hdeg : D.degreeOn ℂ sX C.ι C.dim_le hD = 0 :=
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hD h
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ x₁ _ h₁ h₃,
    (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₂ L₂ _ _ x₂ _ h₂
      (isRIntersectionNumber_zero C)]
  simp [hdeg]

end Numerical

/-- **Numerically equivalent divisors are ample together** over a projective morphism of normal
varieties (FA 2.16.3). -/
private theorem isRelativelyAmple_of_isNumericallyEquivalentOver {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (hX : IsNormalVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z}
    (hf : IsProjectiveMorphism f) (hfs : f ≫ sZ = sX) {D A : RDivisor X}
    (hDA : haveI : QuasiCompact sX := hX.1.toQuasiCompact
      MMP.Flips.IsNumericallyEquivalentOver ℂ sX f D A)
    (hA : MMP.Flips.IsRelativelyAmple f A) : MMP.Flips.IsRelativelyAmple f D := by
  haveI : QuasiCompact sX := hX.1.toQuasiCompact
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf
  exact (MMP.Flips.relativelyAmple_basics sX sZ hX hZ f hfs).2.2.2.2.2
    (IsProjectiveMorphism.isProjective hf) D A hDA hA

section Sign

open MMP.Flips

variable {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {sZ : Z ⟶ Spec (.of ℂ)}

end Sign

end Kit

namespace Kit

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori
open TopologicalSpace

/-! ### Linear algebra of strict transforms and of numerical classes -/

section Linear

open MMP.Flips

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

end Linear

/-! ### One step of the sequence -/

section Step

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- **The strict transform of a canonical divisor across a flip is canonical.** If `K` is a
canonical divisor of `X`, then `(f⁺)⁻¹_* f_* K` is a canonical divisor of `X⁺`: `f_* K` is a
canonical divisor of `Z`, which is `f⁺_* K⁺` for a canonical divisor `K⁺` of `X⁺`, and the small
`f⁺` identifies the prime divisors of `X⁺` and `Z`. -/
private theorem isCanonicalDivisor_flipTransform (hX : IsNormalVariety ℂ sX)
    (hX' : IsNormalVariety ℂ sX') (hZ : IsNormalVariety ℂ sZ) (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) (hfb : IsBirationalMorphism f)
    (hfpb : IsBirationalMorphism fp) {n : ℕ} (hK : K.IsCanonicalDivisor sX n) :
    Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K) := by
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper f := hf.isProper
  haveI : IsProper fp := hfp.isProper
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  have hdimZ : topologicalKrullDim Z = n := by rw [← hf.dim_eq]; exact hK.1
  have hdimX' : topologicalKrullDim X' = n := by rw [hfp.dim_eq]; exact hdimZ
  obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor sZ hZ hdimZ
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor sX' hX' hdimX'
  have hXn : IsNormalVariety ℂ (f ≫ sZ) := by rw [hf.comp_eq]; exact hX
  have hX'n : IsNormalVariety ℂ (fp ≫ sZ) := by rw [hfp.comp_eq]; exact hX'
  haveI : LocallyOfFiniteType (f ≫ sZ) := hXn.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (fp ≫ sZ) := hX'n.1.toLocallyOfFiniteType
  have hK1 : K.IsCanonicalDivisor (f ≫ sZ) n := by rw [hf.comp_eq]; exact hK
  have hK₀' : K₀.IsCanonicalDivisor (fp ≫ sZ) n := by rw [hfp.comp_eq]; exact hK₀
  have h1 := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hZ hXn hfb hKZ hK1
  obtain ⟨KY, hKY, hKYeq⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hZ hX'n hfpb h1 hK₀'
  have heq : flipTransform f fp K = flipTransform fp fp KY := by
    simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply, hKYeq]
  have hid : flipTransform fp fp KY = KY := by
    ext P
    simp only [DivisorWithCoeffs.coeff_apply]
    exact flipTransform_apply_of_isSmall hZ hfp hfp hfpb rfl KY
  rw [heq, hid]
  rw [hfp.comp_eq] at hKY
  exact hKY

/-- A principal divisor is numerically trivial over any base. -/
private theorem isNumericallyTrivialOver_principalDivisor [QuasiCompact sX] {Y : Scheme.{0}}
    (g : X ⟶ Y) (ψ : (RationalFunctions X)ˣ) :
    MMP.Flips.IsNumericallyTrivialOver ℂ sX g (Divisor.toRDivisor (principalDivisor ψ)) :=
  isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent g (Divisor.isCartier_principalDivisor ψ)
    (Divisor.linearlyEquivalent_principalDivisor_zero ψ)

end Step

end Kit

namespace Kit

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori
open TopologicalSpace
open scoped WithZero

/-! ### The dictionary between the two log discrepancies -/

section Bridge

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]

end Bridge

section FormDivisors

end FormDivisors

section Forms

open MMP.Flips

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)}

end Forms

section InverseTransform

open MMP.Flips

variable {X Y : Scheme.{u}}

private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

end InverseTransform

end Kit

namespace Kit

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori
open TopologicalSpace

section KltStep

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

end KltStep

end Kit

namespace Kit

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

/-! ### Picard numbers along a program -/

section Picard

open TopologicalSpace

/-- A contraction is surjective: an open subset of the target missing the image would have no
sections upstairs, while `𝒪_X → f_* 𝒪_Y` is an isomorphism and the target is integral. -/
private theorem surjective_of_isContraction {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X}
    (hf : MMP.Flips.IsContraction k sX sY f) : Surjective f := by
  have := hf.isVariety_target.toIsIntegral
  have := hf.isProper
  have hdom : IsDominant f := by
    refine ⟨dense_iff_inter_open.mpr fun V hV hVne => ?_⟩
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    let V' : X.Opens := ⟨V, hV⟩
    have hbot : f ⁻¹ᵁ V' = ⊥ := by
      refine Opens.ext ?_
      rw [Opens.coe_bot, Set.eq_empty_iff_forall_notMem]
      intro y hy
      exact (Set.eq_empty_iff_forall_notMem.mp hempty) (f y) ⟨hy, y, rfl⟩
    have hsub : Subsingleton Γ(Y, f ⁻¹ᵁ V') := by rw [hbot]; infer_instance
    have := hf.isIso_app V'
    have : Subsingleton Γ(X, V') :=
      (ConcreteCategory.bijective_of_isIso (f.app V')).1.subsingleton
    obtain ⟨x, hx⟩ := hVne
    have h10 := congrArg (X.presheaf.germ V' x hx).hom (Subsingleton.elim (1 : Γ(X, V')) 0)
    rw [map_one, map_zero] at h10
    exact one_ne_zero h10
  have hrange : Set.range f = Set.univ := by
    rw [← (f.isClosedMap.isClosed_range).closure_eq, hdom.denseRange.closure_range]
  exact ⟨Set.range_eq_univ.mp hrange⟩

/-- Two morphisms from the target of a contraction to an affine scheme that agree after
composing with the contraction are equal, since a contraction is an isomorphism on global
sections. -/
private theorem eq_of_isContraction_comp_eq {k : Type} [Field k] {X Y T : Scheme.{0}}
    [IsAffine T] {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {f : Y ⟶ X}
    (hf : MMP.Flips.IsContraction k sX sY f) {u v : X ⟶ T} (h : f ≫ u = f ≫ v) : u = v := by
  apply ext_of_isAffine
  have := hf.isIso_app ⊤
  have h' := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop] at h'
  exact (cancel_mono (f.app ⊤)).mp h'

section CurveCopies

open MMP.Mori

variable {k : Type} [Field k] {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]

/-- A proper curve has more than one point. -/
private theorem not_subsingleton_range_ι {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) :
    ¬ (Set.range C.ι).Subsingleton := fun hs => by
  have : Subsingleton C.scheme := ⟨fun a b => C.ι.isEmbedding.injective (hs ⟨a, rfl⟩ ⟨b, rfl⟩)⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

end CurveCopies

end Picard

/-! ### Steps of the program in the form of the weak model lemma -/

section StepConversions

open TopologicalSpace

/-- **A proper morphism to a projective variety with a relatively ample Cartier divisor is
projective** (Stacks 087S and 0BCL). -/
private theorem isProjectiveMorphism_of_isRelativelyAmpleCartier {Y Z : Scheme.{0}}
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : Y ⟶ Z) [IsProper f] [LocallyOfFiniteType f]
    {L : MMP.Mori.Divisor Y} (hL : MMP.Flips.IsRelativelyAmpleCartier f L) :
    IsProjectiveMorphism f := by
  obtain ⟨hLc, hamp⟩ := hL
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have hinv : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L.divisorialSheaf :=
    Stacks.InvertibleRankOneScheme.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one Y _
  have hqp : IsQuasiProjective f := ⟨⟨inferInstance, inferInstance⟩, L.divisorialSheaf, hinv,
    ⟨inferInstance, hamp⟩⟩
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of ℂ))
  obtain ⟨H, hH, hHa⟩ := exists_isAmple_of_isProjectiveMorphism sZ M hMa hZ.isProjective
  exact isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_isQuasiProjective f H hHa hqp, inferInstance⟩

/-- A proper morphism to a projective variety carrying a relatively ample `ℝ`-divisor is
projective. -/
private theorem isProjectiveMorphism_of_isRelativelyAmple {Y Z : Scheme.{0}}
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (f : Y ⟶ Z) [IsProper f] [LocallyOfFiniteType f]
    {A : RDivisor Y} (hA : MMP.Flips.IsRelativelyAmple f A) : IsProjectiveMorphism f := by
  obtain ⟨m, r, L, hm, -, hL, -⟩ := hA
  exact isProjectiveMorphism_of_isRelativelyAmpleCartier hZ f (hL ⟨0, hm⟩)

variable {X V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}

/-- **Negativity does not depend on the canonical divisor.** A `(K₁ + C)`-negative extremal
contraction onto a variety, projective over it, is `(K₂ + C)`-negative for every `K₂ ∼ K₁`,
on a `ℚ`-factorial `X`. -/
private theorem isNegativeExtremalContraction_of_linearlyEquivalent (hQ : IsQFactorial sX)
    {K₁ K₂ : Divisor X} {C : RDivisor X} {f : X ⟶ V} (hfp : IsProjectiveMorphism f)
    (hf : IsNegativeExtremalContraction ℂ sX sV (logCanonicalDivisor K₁ C) f)
    (hK : K₂.LinearlyEquivalent K₁) :
    IsNegativeExtremalContraction ℂ sX sV (logCanonicalDivisor K₂ C) f := by
  obtain ⟨φ, hφ⟩ := hK
  haveI : QuasiCompact sX := hf.isNormalVariety_source.1.toQuasiCompact
  have hK2 : K₂ = K₁ + principalDivisor φ := by rw [← hφ]; abel
  have heq : -logCanonicalDivisor K₂ C =
      -logCanonicalDivisor K₁ C + (-1 : ℝ) • Divisor.toRDivisor (principalDivisor φ) := by
    rw [logCanonicalDivisor, logCanonicalDivisor, hK2, map_add]
    module
  refine ⟨hf.isNormalVariety_source, hf.isNormalVariety_target,
    isCartierCombination_of_isQFactorial hQ _, hf.isContraction, ?_,
    hf.relativePicardNumber_eq_one⟩
  change MMP.Flips.IsRelativelyAmple f (-logCanonicalDivisor K₂ C)
  rw [heq]
  exact isRelativelyAmple_of_isNumericallyEquivalentOver hf.isNormalVariety_source
    hf.isNormalVariety_target hfp hf.isContraction.comp_eq
    (isNumericallyEquivalentOver_add_smul (isCartierCombination_of_isQFactorial hQ _)
      (isNumericallyTrivialOver_principalDivisor f φ) (-1)) hf.isRelativelyAntiAmple

/-- A curve contracted by `f ≫ e` with `e` injective is contracted by `f`, and conversely. -/
private theorem properCurve_isContractedBy_comp_iff {k : Type} [Field k] {X Y Y' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (Γ : ProperCurve sX) (f : X ⟶ Y) (e : Y ⟶ Y') [IsIso e] :
    Γ.IsContractedBy (f ≫ e) ↔ Γ.IsContractedBy f := by
  have hinj : Function.Injective e := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
    (asIso e))).injective
  refine ⟨fun h x hx => hinj (by simpa only [Scheme.Hom.comp_apply] using h x hx),
    fun h x hx => by simp only [Scheme.Hom.comp_apply, h x hx]⟩

/-- **A negative extremal contraction followed by an isomorphism** is a negative extremal
contraction. -/
private theorem isNegativeExtremalContraction_comp_inv {X' : Scheme.{0}}
    {sX' : X' ⟶ Spec (.of ℂ)} {E : RDivisor X} {f : X ⟶ V} {fp : X' ⟶ V} [IsIso fp]
    (hf : IsNegativeExtremalContraction ℂ sX sV E f) (hfp : fp ≫ sV = sX')
    (hX' : IsNormalVariety ℂ sX') :
    IsNegativeExtremalContraction ℂ sX sX' E (f ≫ inv fp) := by
  have hc := hf.isContraction
  haveI : IsProper f := hc.isProper
  have hsV : inv fp ≫ sX' = sV := by rw [← hfp, IsIso.inv_hom_id_assoc]
  have htriv : MMP.Flips.relativeNumericallyTrivialDivisors sX (f ≫ inv fp) =
      MMP.Flips.relativeNumericallyTrivialDivisors sX f := by
    ext D
    simp only [MMP.Flips.mem_relativeNumericallyTrivialDivisors]
    exact ⟨fun h Γ hΓ => h Γ ((properCurve_isContractedBy_comp_iff Γ f (inv fp)).mpr hΓ),
      fun h Γ hΓ => h Γ ((properCurve_isContractedBy_comp_iff Γ f (inv fp)).mp hΓ)⟩
  refine ⟨hf.isNormalVariety_source, hX', hf.isCartierCombination,
    ⟨hX'.1, hc.isVariety_source, by rw [Category.assoc, hsV, hc.comp_eq], inferInstance,
      fun U => ?_⟩, ?_, ?_⟩
  · rw [Scheme.Hom.comp_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance (hc.isIso_app _)
  · obtain ⟨m, r, L, hm, hr, hL, hA⟩ := hf.isRelativelyAntiAmple
    refine ⟨m, r, L, hm, hr, fun j => ?_, hA⟩
    obtain ⟨hLc, hamp⟩ := hL j
    refine ⟨hLc, fun U hU => ?_⟩
    exact hamp ((inv fp) ⁻¹ᵁ U) (hU.preimage_of_isIso (inv fp))
  · unfold MMP.Flips.relativePicardNumber MMP.Flips.RelativeNumericalDivisorClasses
    rw [htriv]
    exact hf.relativePicardNumber_eq_one

/-- **The exceptional set of a divisorial contraction followed by an isomorphism.** If the
exceptional set `Ex(f)` (complement of the preimage of the biregular locus) of a proper birational
`f : X ⟶ V` onto a normal `V` is a prime divisor `E`, then so is the exceptional set of
`f ≫ (f⁺)⁻¹` in the sense of open immersions, for an isomorphism `f⁺`. -/
private theorem flips_exceptionalSet_comp_inv_eq {X' : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] {f : X ⟶ V} {fp : X' ⟶ V} [IsIso fp] [IsProper f]
    (hfb : IsBirationalMorphism f) {E : MMP.Mori.PrimeDivisor X}
    (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support) :
    MMP.Flips.exceptionalSet (f ≫ inv fp) = E.support := by
  have h1 : MMP.Flips.exceptionalSet (f ≫ inv fp) = MMP.Flips.exceptionalSet f := by
    ext x
    simp only [MMP.Flips.exceptionalSet, Set.mem_setOf_eq]
    refine not_congr (exists_congr fun U => and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩)
    · have : IsOpenImmersion ((U.ι ≫ f ≫ inv fp) ≫ fp) := inferInstance
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using this
    · rw [← Category.assoc]; infer_instance
  rw [h1]
  refine subset_antisymm (fun x hx => ?_) ?_
  · rw [← hE]
    intro hxm
    apply hx
    have hb : f x ∈ biregularLocus f := hxm
    refine ⟨f ⁻¹ᵁ biregularLocus f, hb, ?_⟩
    have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
    rw [← morphismRestrict_ι]
    infer_instance
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine closure_minimal ?_ (MMP.Flips.isClosed_exceptionalSet f)
    rintro _ rfl hne
    have hc := MMP.Flips.coheight_map_of_notMem_exceptionalSet (f := f)
      (y := E.genericPoint) (fun h => h hne)
    have hb := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb
      (by rw [hc, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
    have hmem : E.genericPoint ∈ (MMP.Mori.exceptionalSet f : Set X) := by
      rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
    exact hmem hb

/-- Composing a rational map with two morphisms in turn composes with their composite. -/
private theorem rationalMap_compHom_compHom {X₁ X₂ X₃ X₄ : Scheme.{0}} (φ : X₁.RationalMap X₂)
    (a : X₂ ⟶ X₃) (b : X₃ ⟶ X₄) : (φ.compHom a).compHom b = φ.compHom (a ≫ b) := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

/-- A rational map `φ` with `f⁺ ∘ φ = f` for an isomorphism `f⁺` is `(f⁺)⁻¹ ∘ f`. -/
private theorem toRationalMap_comp_inv_eq {X' : Scheme.{0}} {f : X ⟶ V} {fp : X' ⟶ V} [IsIso fp]
    {φ : X.RationalMap X'} (hφ : φ.compHom fp = f.toRationalMap) :
    (f ≫ inv fp).toRationalMap = φ := by
  have h1 : φ.compHom (fp ≫ inv fp) = φ := by
    rw [IsIso.hom_inv_id]
    obtain ⟨φ, rfl⟩ := φ.exists_rep
    rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]
  rw [← h1, ← rationalMap_compHom_compHom, hφ]
  change (f ≫ inv fp).toPartialMap.toRationalMap = f.toPartialMap.toRationalMap.compHom (inv fp)
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.Hom.toPartialMap_compHom]

/-- An isomorphism is biregular everywhere. -/
private theorem mem_biregularLocus_of_isIso {A B : Scheme.{0}} (e : A ⟶ B) [IsIso e] (b : B) :
    b ∈ biregularLocus e :=
  le_biregularLocus ((isBiregular_top_iff e).mpr inferInstance) trivial

/-- **The transform along a divisorial contraction followed by an isomorphism** is the strict
transform `(f⁺)⁻¹_* f_*`. -/
private theorem transformDivisor_comp_inv_eq_flipTransform {X' : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsSeparated (V ↘ ⊤_ Scheme)]
    [IsSeparated (X' ↘ ⊤_ Scheme)] {f : X ⟶ V} {fp : X' ⟶ V} [IsIso fp] [IsProper f]
    (hfb : IsBirationalMorphism f) (hsurj : Function.Surjective f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor (f ≫ inv fp).toRationalMap D = flipTransform f fp D := by
  haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  refine Finsupp.ext fun P' => ?_
  have hcoP' : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [Topology.IsOpenEmbedding.coheight_eq _ fp.isOpenEmbedding,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoP'
  have hQ : Q.genericPoint = fp P'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoP'
  have hbQ : Q.genericPoint ∈ biregularLocus f :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb
      (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
  obtain ⟨x, hx⟩ := hsurj Q.genericPoint
  have hcox : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (hx ▸ hbQ), hx,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcox
  have hP : f P.genericPoint = Q.genericPoint := by
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]; exact hx
  have huniq : ∀ P₁ : MMP.Mori.PrimeDivisor X, f P₁.genericPoint = Q.genericPoint → P₁ = P :=
    fun P₁ h1 => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq f (biregularLocus f) (h1 ▸ hbQ) (hP ▸ hbQ) (h1.trans hP.symm))
  have hL : MMP.Mori.RationalMap.transformDivisor (f ≫ inv fp).toRationalMap D P' = D P := by
    refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ P P').mpr ?_)
      (fun P₁ hP₁ => ?_) D
    · rw [Scheme.Hom.comp_apply, hP, hQ, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]; rfl
    · have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ P₁ P').mp hP₁
      refine huniq P₁ ?_
      rw [hQ, ← h1, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (inv fp) fp, IsIso.inv_hom_id]
      rfl
  have hR1 : inverseTransformDivisor fp
      (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D) P' =
        MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ.symm
        (mem_biregularLocus_of_isIso fp _))
      (fun Q₁ hQ₁ => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hQ₁).1.symm.trans hQ.symm)) _
  have hR2 : MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q = D P :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hP)
      (fun P₁ hP₁ => huniq P₁
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P₁ Q).mp hP₁)) D
  change _ = inverseTransformDivisor fp
    (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D) P'
  rw [hL, hR1, hR2]

end StepConversions

/-! ### Real flip steps as flips -/

section FlipConversion

/-- A relatively ample `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRelativelyAmple {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} {A : RDivisor X}
    (hA : MMP.Flips.IsRelativelyAmple f A) : IsCartierCombination A := by
  obtain ⟨m, r, L, -, -, hL, rfl⟩ := hA
  exact ⟨m, r, L, fun j => (hL j).1, by simp [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩

variable {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- Across a step of an extremal real flip sequence, the strict transform of the canonical
divisor `K` is linearly equivalent to the canonical divisor `K⁺`. -/
private theorem linearlyEquivalent_flipTransform (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) :
    MMP.Mori.Divisor.LinearlyEquivalent (flipTransform f fp K) K' := by
  have hE := h.isNegativeExtremalContraction
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  obtain ⟨m, hKm⟩ := hK
  obtain ⟨m', hK'm⟩ := h.isCanonicalDivisor_flip
  exact MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'
    (isCanonicalDivisor_flipTransform hE.isNormalVariety_source hX' hZ h.isSmall h.isSmall_flip
      h.isBirationalMorphism h.isBirationalMorphism_flip hKm) hK'm

/-- **A step of an extremal real flip sequence is a flip** in the sense of `MMP.Flips.IsFlip`, for
the birational map `(f⁺)⁻¹ ∘ f`, which transforms divisors as the strict transform. -/
private theorem exists_isFlip_of_isRealFlipStep (h : IsRealFlipStep sX sZ sX' K B K' B' f fp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hQ' : IsQFactorial sX') :
    ∃ g : X.RationalMap X',
      MMP.Flips.IsFlip ℂ sX sZ sX' (MMP.Flips.logCanonicalDivisor K B) f fp g ∧
      MMP.Flips.RationalMap.IsOver f fp g ∧
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        MMP.Mori.RationalMap.transformDivisor g D = flipTransform f fp D) ∧
      ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
        MMP.Mori.RationalMap.transformPrimeDivisor g P = some P' := by
  have hE := h.isNegativeExtremalContraction
  have hX := hE.isNormalVariety_source
  have hZ := hE.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hX' : IsNormalVariety ℂ sX' := ⟨h.isSmall_flip.isVariety_source, inferInstance⟩
  haveI : IsProper fp := isProper_of_isProjectiveMorphism _ h.isProjectiveMorphism_flip
  obtain ⟨g, hg, hgo, htr, hsurj⟩ := exists_flipMap hX hX' hZ h.isSmall h.isSmall_flip
    h.isBirationalMorphism h.isBirationalMorphism_flip
  obtain ⟨φ, hφ⟩ := linearlyEquivalent_flipTransform h hK
  have hTK : flipTransform f fp (Divisor.toRDivisor K) =
      Divisor.toRDivisor (flipTransform f fp K) := by
    have := flipTransform_smul_toRDivisor hZ h.isSmall h.isSmall_flip h.isBirationalMorphism 1 K
    simpa only [one_smul] using this
  have htrE : MMP.Mori.RationalMap.transformDivisor g (MMP.Flips.logCanonicalDivisor K B) =
      MMP.Flips.logCanonicalDivisor K' B' + (1 : ℝ) • Divisor.toRDivisor (principalDivisor φ) := by
    rw [htr, MMP.Flips.logCanonicalDivisor, map_add, hTK, ← h.eq_flipTransform, ← hφ,
      MMP.Flips.logCanonicalDivisor, one_smul, map_sub]
    abel
  have hnum := isNumericallyTrivialOver_toRDivisor_of_linearlyEquivalent (sX := sX') fp
    (Divisor.isCartier_principalDivisor φ) (Divisor.linearlyEquivalent_principalDivisor_zero φ)
  refine ⟨g,
    { isNormalVariety_source := hX
      isNormalVariety_target := hZ
      isNormalVariety_flip := hX'
      isContraction := hE.isContraction
      isCartierCombination := hE.isCartierCombination
      isRelativelyAntiAmple := hE.isRelativelyAntiAmple
      isProper := inferInstance
      isModificationOf := ⟨hg, hgo⟩
      isMorphismInCodimOne := MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX f fp g hgo
      isSmall := h.isSmall_flip
      isCartierCombination_transform := isCartierCombination_of_isQFactorial hQ' _
      isRelativelyAmple_transform := by
        rw [htrE]
        exact isRelativelyAmple_of_isNumericallyEquivalentOver hX' hZ
          h.isProjectiveMorphism_flip h.isSmall_flip.comp_eq
          (isNumericallyEquivalentOver_add_smul
            (isCartierCombination_of_isRelativelyAmple h.isRelativelyAmple_flip) hnum 1) h.isRelativelyAmple_flip
      isSmall_source := h.isSmall }, hgo, htr, hsurj⟩

end FlipConversion

/-! ### Birational contractions -/

section Trichotomy

open TopologicalSpace

end Trichotomy

/-! ### Terminality across a divisorial contraction -/

section KltTerminal

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

end KltTerminal

section DivisorialTerminal

open TopologicalSpace

variable {X X' V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}

/-- No proper curve is contracted by an isomorphism. -/
private theorem not_isContractedBy_of_isIso {k : Type} [Field k] {A B : Scheme.{0}}
    {sA : A ⟶ Spec (.of k)} (Γ : ProperCurve sA) (e : A ⟶ B) [IsIso e] : ¬ Γ.IsContractedBy e := by
  intro h
  have hinj : Function.Injective e := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
    (asIso e))).injective
  refine not_subsingleton_range_ι Γ fun a ha b hb => ?_
  rw [ProperCurve.ι, range_curveSubschemeAtι] at ha hb
  exact (hinj (h a ha)).trans (hinj (h b hb)).symm

/-- Every `ℝ`-Cartier divisor is relatively nef over an isomorphism. -/
private theorem isRelativelyNef_of_isIso {A B : Scheme.{0}} [IsLocallyNoetherian A] [IsNormal A]
    {sA : A ⟶ Spec (.of ℂ)} [QuasiCompact sA] (e : A ⟶ B) [IsIso e] {D : RDivisor A} (hD : IsCartierCombination D) :
    MMP.Flips.IsRelativelyNef ℂ sA e D := by
  obtain ⟨m, r, L, hL, hDeq⟩ := hD
  exact ⟨m, r, L, hL, by rw [hDeq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs],
    fun Γ hΓ => absurd hΓ (not_isContractedBy_of_isIso Γ e)⟩

/-- **The prime divisors across a divisorial contraction followed by an isomorphism.** Every
prime divisor `P'` of `X'` corresponds to a prime divisor `P` of `X` outside `Ex(f)`, over the
same point of `V`, and the strict transform has coefficient `D P` along `P'`. -/
private theorem exists_primeDivisor_of_comp_inv [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [IsSeparated (V ↘ ⊤_ Scheme)] {f : X ⟶ V} {fp : X' ⟶ V} [IsIso fp]
    [IsProper f] (hfb : IsBirationalMorphism f) (hsurj : Function.Surjective f)
    (P' : MMP.Mori.PrimeDivisor X') :
    ∃ P : MMP.Mori.PrimeDivisor X, f P.genericPoint = fp P'.genericPoint ∧
      f P.genericPoint ∈ biregularLocus f ∧
      ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X), flipTransform f fp D P' = D P := by
  haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have hcoP' : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [Topology.IsOpenEmbedding.coheight_eq _ fp.isOpenEmbedding,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoP'
  have hQ : Q.genericPoint = fp P'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoP'
  have hbQ : Q.genericPoint ∈ biregularLocus f :=
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hfb
      (by rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint])
  obtain ⟨x, hx⟩ := hsurj Q.genericPoint
  have hcox : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (hx ▸ hbQ), hx,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcox
  have hP : f P.genericPoint = Q.genericPoint := by
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]; exact hx
  have huniq : ∀ P₁ : MMP.Mori.PrimeDivisor X, f P₁.genericPoint = Q.genericPoint → P₁ = P :=
    fun P₁ h1 => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq f (biregularLocus f) (h1 ▸ hbQ) (hP ▸ hbQ) (h1.trans hP.symm))
  refine ⟨P, hP.trans hQ, hP ▸ hbQ, fun {R} _ D => ?_⟩
  have hR1 : inverseTransformDivisor fp
      (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D) P' =
        MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ.symm
        (mem_biregularLocus_of_isIso fp _))
      (fun Q₁ hQ₁ => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
          hQ₁).1.symm.trans hQ.symm)) _
  have hR2 : MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q = D P :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hP)
      (fun P₁ hP₁ => huniq P₁
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P₁ Q).mp hP₁)) D
  change inverseTransformDivisor fp
    (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D) P' = _
  rw [hR1, hR2]

end DivisorialTerminal

section Program

variable {S Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
  {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ] {πZ : Z ⟶ S}

variable (sS) in
/-- A model of the program over `S`: a projective `ℚ`-factorial variety over `S`. -/
private def IsProgramModel {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (πX : X ⟶ S) : Prop :=
  MMP.Mori.IsProjectiveVariety ℂ sX ∧ IsQFactorial sX ∧ πX ≫ sS = sX

/-- A step `X ⟶ V ⟵ X'` over `S` of a `(K + C)`-program: a `(K + C)`-negative extremal ray `R`
of `NE̅(X/S)` with its contraction `f`, `g`, followed by `f⁺` over `S`, an isomorphism for a
divisorial `f` and a real flip otherwise, `C'` being the strict transform of `C`. -/
private def IsProgramStep {X X' V : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    (sX : X ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ)) (sV : V ⟶ Spec (.of ℂ)) (πX : X ⟶ S)
    (πX' : X' ⟶ S) (KX : Divisor X) (CX : RDivisor X) (KX' : Divisor X') (CX' : RDivisor X')
    (R : Set (RelativeNumericalCurveClasses sX πX)) (f : X ⟶ V) (g : V ⟶ S) (fp : X' ⟶ V) :
    Prop :=
  IsExtremalRay ℝ (relativeClosedConeOfCurves sX πX :
      Set (RelativeNumericalCurveClasses sX πX)) R ∧
    (∀ (Γ : ProperCurve sX) (hΓ : Γ.IsContractedBy πX), Γ.relativeClass πX hΓ ∈ R →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        IsRIntersectionNumber ℂ sX (logCanonicalDivisor KX CX) r L Γ x → x < 0) ∧
    IsRelativeContractionOfFace πX R f g ∧
    IsNegativeExtremalContraction ℂ sX sV (logCanonicalDivisor KX CX) f ∧
    fp ≫ g = πX' ∧
    (((IsBirationalMorphism f ∧ ∃ E : MMP.Mori.PrimeDivisor X,
          (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧
        IsIso fp ∧ (∃ m : ℕ, KX'.IsCanonicalDivisor sX' m) ∧ CX' = flipTransform f fp CX) ∨
      IsRealFlipStep sX sV sX' KX CX KX' CX' f fp)

section Steps

variable {X X' V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
  {πX : X ⟶ S} {πX' : X' ⟶ S} {KX : Divisor X} {CX : RDivisor X} {KX' : Divisor X'}
  {CX' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ V} {g : V ⟶ S}
  {fp : X' ⟶ V}

/-- The contraction of a step is a contraction in the sense of `MMP.Flips.IsContraction`. -/
private theorem IsProgramStep.isContraction
    (hs : IsProgramStep sX sX' sV πX πX' KX CX KX' CX' R f g fp) :
    MMP.Flips.IsContraction ℂ sV sX f :=
  hs.2.2.2.1.isContraction

/-- The base of a step lies over `S` compatibly with the structure morphisms. -/
private theorem IsProgramStep.comp_eq_base (hXm : IsProgramModel sS sX πX)
    (hs : IsProgramStep sX sX' sV πX πX' KX CX KX' CX' R f g fp) : g ≫ sS = sV :=
  eq_of_isContraction_comp_eq hs.isContraction (by
    rw [← Category.assoc, hs.2.2.1.comp_eq, hXm.2.2, hs.isContraction.comp_eq])

/-- The second contraction of a step lies over `ℂ`. -/
private theorem IsProgramStep.comp_eq_flip (hXm : IsProgramModel sS sX πX)
    (hX'm : IsProgramModel sS sX' πX')
    (hs : IsProgramStep sX sX' sV πX πX' KX CX KX' CX' R f g fp) : fp ≫ sV = sX' := by
  rw [← hs.comp_eq_base hXm, ← Category.assoc, hs.2.2.2.2.1, hX'm.2.2]

/-- The target of a step is a projective variety. -/
private theorem IsProgramStep.isProjectiveVariety_target (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hXm : IsProgramModel sS sX πX)
    (hs : IsProgramStep sX sX' sV πX πX' KX CX KX' CX' R f g fp) :
    MMP.Mori.IsProjectiveVariety ℂ sV := by
  have hV := hs.2.2.2.1.isNormalVariety_target
  refine (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨hV.1, ?_⟩
  rw [← hs.comp_eq_base hXm]
  exact hs.2.2.1.isProjectiveMorphism.comp hS.isProjective

/-- **The step map of a program step**, in the form of the weak model lemma, for a canonical
divisor `K'` of `X`: a birational map `φ : X ⤏ X'` over `V` transforming divisors as the strict
transform, which is the divisorial contraction followed by `(f⁺)⁻¹` or the flip. -/
private theorem IsProgramStep.exists_stepMap (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hXm : IsProgramModel sS sX πX) (hX'm : IsProgramModel sS sX' πX')
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hs : IsProgramStep sX sX' sV πX πX' KX CX KX' CX' R f g fp) {K' : Divisor X}
    (hK' : ∃ m : ℕ, K'.IsCanonicalDivisor sX m) :
    ∃ φg : X.RationalMap X', MMP.Mori.RationalMap.IsBirational φg ∧
      φg.compHom fp = f.toRationalMap ∧
      (∀ D : RDivisor X, RationalMap.transformDivisor φg D = flipTransform f fp D) ∧
      (∀ D : Divisor X, RationalMap.transformDivisor φg D = flipTransform f fp D) ∧
      ((∃ f' : X ⟶ X', f'.toRationalMap = φg ∧ f' ≫ πX' = πX ∧
          IsNegativeExtremalContraction ℂ sX sX' (logCanonicalDivisor K' CX) f' ∧
          IsBirationalMorphism f' ∧
          ∃ E : MMP.Mori.PrimeDivisor X, MMP.Flips.exceptionalSet f' = E.support) ∨
        (∃ (W : Scheme.{0}) (sW : W ⟶ Spec (.of ℂ)) (πW : W ⟶ S) (f₀ : X ⟶ W) (fp₀ : X' ⟶ W),
          f₀ ≫ πW = πX ∧ fp₀ ≫ πW = πX' ∧
          IsNegativeExtremalContraction ℂ sX sW (logCanonicalDivisor K' CX) f₀ ∧
          MMP.Flips.IsFlip ℂ sX sW sX' (logCanonicalDivisor K' CX) f₀ fp₀ φg)) ∧
      ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
        RationalMap.transformPrimeDivisor φg P = some P' ∧
          ∀ D : RDivisor X, flipTransform f fp D P' = D P := by
  have hXv : IsNormalVariety ℂ sX := hXm.2.1.1
  have hX'v : IsNormalVariety ℂ sX' := hX'm.2.1.1
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  have hKK : K'.LinearlyEquivalent KX := by
    obtain ⟨m, hm⟩ := hK'
    obtain ⟨m', hm'⟩ := hKX
    exact MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXv hm hm'
  have hneg := hs.2.2.2.1
  have hVv := hneg.isNormalVariety_target
  haveI : IsIntegral V := hVv.1.toIsIntegral
  haveI : IsNormal V := hVv.2
  haveI : LocallyOfFiniteType sV := hVv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : IsSeparated sV := hVv.1.toIsSeparated
  haveI := isSeparated_toTerminal sV
  haveI : IsSeparated sX' := hX'v.1.toIsSeparated
  haveI := isSeparated_toTerminal sX'
  haveI : IsProper f := hneg.isContraction.isProper
  rcases hs.2.2.2.2.2 with ⟨⟨hbir, E, hE⟩, hiso, -, -⟩ | hfl
  · haveI := hiso
    obtain ⟨φg, hφb, hφ⟩ := exists_isBirational_compHom_eq hbir (isBirationalMorphism_of_isIso fp)
    have hφf := toRationalMap_comp_inv_eq hφ
    have hsurj : Function.Surjective f := (surjective_of_isContraction hneg.isContraction).1
    haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
    haveI : LocallyOfFiniteType f := by
      have : LocallyOfFiniteType (f ≫ sV) := by rw [hneg.isContraction.comp_eq]; infer_instance
      exact locallyOfFiniteType_of_comp f sV
    have hfproj : IsProjectiveMorphism f := isProjectiveMorphism_of_isRelativelyAmple
      (hs.isProjectiveVariety_target hS hXm) f hneg.isRelativelyAntiAmple
    refine ⟨φg, hφb, hφ, fun D => ?_, fun D => ?_, Or.inl ⟨f ≫ inv fp, hφf, ?_, ?_, ?_,
      E, flips_exceptionalSet_comp_inv_eq hbir hE⟩, fun P' => ?_⟩
    · rw [← hφf]; exact transformDivisor_comp_inv_eq_flipTransform hbir hsurj D
    · rw [← hφf]; exact transformDivisor_comp_inv_eq_flipTransform hbir hsurj D
    · rw [Category.assoc, ← hs.2.2.2.2.1, IsIso.inv_hom_id_assoc]
      exact hs.2.2.1.comp_eq
    · exact isNegativeExtremalContraction_comp_inv
        (isNegativeExtremalContraction_of_linearlyEquivalent hXm.2.1 hfproj hneg hKK)
        (hs.comp_eq_flip hXm hX'm) hX'v
    · change MMP.Mori.RationalMap.IsBirational _
      rw [hφf]; exact hφb
    · obtain ⟨P, hPP', -, hval⟩ := exists_primeDivisor_of_comp_inv hbir hsurj (fp := fp) P'
      refine ⟨P, ?_, fun D => hval D⟩
      rw [← hφf]
      refine (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ P P').mpr ?_
      rw [Scheme.Hom.comp_apply, hPP', ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
      rfl
  · have hfl' : IsRealFlipStep sX sV sX' K' CX KX' CX' f fp :=
      { hfl with
        isNegativeExtremalContraction := isNegativeExtremalContraction_of_linearlyEquivalent
          hXm.2.1 hfl.isProjectiveMorphism hfl.isNegativeExtremalContraction hKK }
    obtain ⟨φg, hflip, hover, htr, -⟩ := exists_isFlip_of_isRealFlipStep hfl' hK' hX'm.2.1
    refine ⟨φg, hflip.isModificationOf.1, hover, fun D => htr D, fun D => htr D,
      Or.inr ⟨V, sV, g, f, fp, hs.2.2.1.comp_eq, hs.2.2.2.2.1,
        hfl'.isNegativeExtremalContraction, hflip⟩, fun P' => ?_⟩
    obtain ⟨P, hP⟩ := exists_primeDivisor_map_eq_of_isSmall hfl.isSmall_flip hfl.isSmall P'
    haveI : IsIso (f ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
      isBiregular_iff_le_biregularLocus.mpr inf_le_left
    haveI : IsIso (fp ∣_ (biregularLocus f ⊓ biregularLocus fp)) :=
      isBiregular_iff_le_biregularLocus.mpr inf_le_right
    refine ⟨P, transformPrimeDivisor_eq_some_of_map_eq fp _
      (fun x hx => mem_biregularLocus_inf_of_isSmall hfl.isSmall hfl.isSmall_flip hx) hover
      hP, fun D => ?_⟩
    exact flipTransform_apply_of_isSmall hVv hfl.isSmall hfl.isSmall_flip hfl.isBirationalMorphism
      hP.symm D

/-- The canonical divisor of the next model of a step is a canonical divisor. -/
private theorem IsProgramStep.isCanonicalDivisor_next
    (hs : IsProgramStep sX sX' sV πX πX' KX CX KX' CX' R f g fp) :
    ∃ m : ℕ, KX'.IsCanonicalDivisor sX' m := by
  rcases hs.2.2.2.2.2 with ⟨-, -, hc, -⟩ | hfl
  · exact hc
  · exact hfl.isCanonicalDivisor_flip

end Steps

end Program

end Kit

namespace Kit

open MMP.Flips

section NefTransfer

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] [IsIntegral X]

/-- An `ℝ`-Cartier divisor numerically equivalent over `Y` to an `f`-nef one is `f`-nef. -/
private theorem isRelativelyNef_of_isNumericallyEquivalentOver {f : X ⟶ Y} {D D' : RDivisor X}
    (h : IsNumericallyEquivalentOver ℂ sX f D' D) (hD : IsRelativelyNef ℂ sX f D) :
    IsRelativelyNef ℂ sX f D' := by
  obtain ⟨m, r, L, hL, hDeq, hnef⟩ := hD
  obtain ⟨m', r', L', hL', hD'eq⟩ := h.1
  refine ⟨m', r', L', hL', by rw [hD'eq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs],
    fun C hC x hx => ?_⟩
  have hy := isRIntersectionNumber_sum_degreeOn D r L hL hDeq C
  rw [h.2.2 C hC m' r' L' x m r L _ hx hy]
  exact hnef C hC _ hy

/-- Nefness of an adjoint does not depend on the canonical divisor. -/
private theorem isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent {f : X ⟶ Y}
    {K₁ K₂ : Divisor X} {C : RDivisor X} (hK : K₂.LinearlyEquivalent K₁)
    (h : IsRelativelyNef ℂ sX f (logCanonicalDivisor K₁ C)) :
    IsRelativelyNef ℂ sX f (logCanonicalDivisor K₂ C) := by
  obtain ⟨φ, hφ⟩ := hK
  have hK2 : K₂ = K₁ + principalDivisor φ := by rw [← hφ]; abel
  have heq : logCanonicalDivisor K₂ C =
      logCanonicalDivisor K₁ C + (1 : ℝ) • Divisor.toRDivisor (principalDivisor φ) := by
    rw [logCanonicalDivisor, logCanonicalDivisor, hK2, map_add, one_smul]
    abel
  have hD : IsCartierCombination (logCanonicalDivisor K₁ C) := by
    obtain ⟨m, r, L, hL, hDeq, -⟩ := h
    exact ⟨m, r, L, hL, by rw [hDeq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  rw [heq]
  exact isRelativelyNef_of_isNumericallyEquivalentOver
    (isNumericallyEquivalentOver_add_smul hD (isNumericallyTrivialOver_principalDivisor f φ) 1) h

end NefTransfer

section KltTerminal

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- The log discrepancy of a prime divisor `P` of `X` with respect to `B` with `K + B`
`ℝ`-Cartier is `1 - coeff_P B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor [CompactSpace X] (hX : IsNormalVariety ℂ sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX P)
      (1 - B.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant (𝟙 X) (hC i)
  have hC'P : ∀ i, (C' i).coeff P = (C i).coeff P := fun i =>
    MMP.Positivity.coeff_eq_of_isPullback (f := 𝟙 X) P P rfl (hC i) (hC' i)
  have hord : (DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω = P.ordForm ω :=
    DivisorOver.ordPullback_ofPrimeDivisor hX hK.topologicalKrullDim_eq P ω
  have hsumΓ : ∀ Γ, (Γ.ordForm ω : ℝ) + B.coeff Γ = ∑ i, r i * (C i).coeff Γ := fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C,
    C', hC, hsumΓ, fun i => ⟨_, hC' i⟩, ?_⟩
  change 1 - B.coeff P = 1 + ((DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω : ℝ) -
    ∑ i, r i * ((C' i).coeff P : ℝ)
  simp_rw [hC'P, hord]
  rw [← hsumΓ P]
  ring

/-- The coefficients of a real canonical boundary are less than one. -/
private theorem coeff_lt_one_of_isRealTerminalPair {B : RDivisor X} (hB : IsRealTerminalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P < 1 := by
  by_cases h : B.coeff P = 0
  · rw [h]; exact one_pos
  · exact (hB.1.2.1 P h).2

/-- **A real terminal pair is klt**: exceptional divisors have log discrepancy `> 1`, and a
non-exceptional divisor has the valuation of a prime divisor `P` of `X`, with log discrepancy
`1 - coeff_P B > 0`. -/
private theorem isRealKltPair_of_isRealTerminalPair [CompactSpace X] {B : RDivisor X}
    (hB : IsRealTerminalPair sX B) : IsRealKltPair sX B := by
  have hlt := coeff_lt_one_of_isRealTerminalPair hB
  obtain ⟨⟨hX, -, ⟨n, K, hK, hKB⟩, -⟩, hterm⟩ := hB
  refine ⟨hX, hlt, ⟨n, K, hK, hKB⟩, fun m E a ha => ?_⟩
  by_cases hE : E.IsExceptional
  · linarith [hterm m E a hE ha]
  · obtain ⟨P, hP⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX E hE
    have h1 := isLogDiscrepancy_ofPrimeDivisor hX hK hKB P
    rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha h1 hP]
    linarith [hlt P]

end KltTerminal

end Kit

section Main

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### The two radial inputs -/

/-- The property of the constant `ε` of the null-rays lemma. -/
private def NullSpec (ε : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ) : Prop :=
      ∀ {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
        (sX : X ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (g : X ⟶ S),
        MMP.Mori.IsProjectiveVariety ℂ sS → g ≫ sS = sX →
        ∀ {K : Divisor X} {B C : RDivisor X}, K.IsCanonicalDivisor sX 3 →
        ∀ ν : RationalNullData sX K B, (∀ P, 0 ≤ C.coeff P) → IsRealKltPair sX C →
        MMP.Flips.IsRelativelyNef ℂ sX g (MMP.Flips.logCanonicalDivisor K B) →
        ∀ t : ℝ, 0 < t → t < ε ν.s ν.weight ν.m →
        -- every `D_t`-negative extremal ray of `NE̅(X/S)` is `D`-null
        (∀ R : Set (RelativeNumericalCurveClasses sX g),
          IsExtremalRay ℝ
            (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R →
          (∃ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
            Divisor.toRDivisor K + ((1 - t) • B + t • C) =
                ∑ j, c j • Divisor.toRDivisor (L j) ∧
              ∀ u ∈ R, u ≠ 0 →
                ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
                  RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) < 0) →
          ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
            Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
            ∀ u ∈ R, ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
              RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) = 0) ∧
        -- every step of the `D_t`-program over `S` is `D`-null and preserves the data
        (∀ {Z X' : Scheme.{0}} [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X']
          [IsNormal X'] (sZ : Z ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ)) (f : X ⟶ Z)
          (h : Z ⟶ S) (fp : X' ⟶ Z),
          f ≫ h = g → h ≫ sS = sZ →
          MMP.Flips.IsNegativeExtremalContraction ℂ sX sZ
            (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) f →
          IsBirationalMorphism f → IsProjectiveMorphism f →
          MMP.Mori.IsProjectiveVariety ℂ sZ →
          IsQFactorial sX' → MMP.Mori.IsProjectiveVariety ℂ sX' →
          Divisor.IsCanonicalDivisor sX' 3 (flipTransform f fp K : Divisor X') →
          MMP.Flips.IsSmall ℂ sZ sX' fp → IsProjectiveMorphism fp →
          MMP.Flips.IsRelativelyAmple fp
            (MMP.Flips.logCanonicalDivisor (flipTransform f fp K)
              (flipTransform f fp ((1 - t) • B + t • C))) →
          (∀ A : ProperCurve sX, A.IsContractedBy f →
            ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
              Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
              ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
                NumericalCurveClasses.degree sX (L j).divisorialSheaf
                  (OneCycle.numericalClass sX (A.cycle ℝ))) = 0) ∧
          MMP.Flips.IsRelativelyNef ℂ sX' (fp ≫ h)
            (MMP.Flips.logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B)) ∧
          (∃ (ν' : RationalNullData sX' (flipTransform f fp K) (flipTransform f fp B))
              (hs : ν'.s = ν.s),
            ν'.m = ν.m ∧ ∀ i, ν'.weight i = ν.weight (Fin.cast hs i) ∧
              ν'.boundary i = flipTransform f fp (ν.boundary (Fin.cast hs i))) ∧
          (∀ P, 0 ≤ (flipTransform f fp C).coeff P) ∧
          IsRealKltPair sX' (flipTransform f fp C))

/-- The property of the gap `τ` of the radial nef interval. -/
private def NefSpec (τ : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ) : Prop :=
      ∀ {Y S : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
        (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (g : Y ⟶ S),
        IsProjectiveMorphism g → MMP.Mori.IsProjectiveVariety ℂ sS → g ≫ sS = sY →
        ∀ {K : Divisor Y} {B C : RDivisor Y}, K.IsCanonicalDivisor sY 3 →
        ∀ ν : RationalNullData sY K B, (∀ P, 0 ≤ C.coeff P) → IsRealKltPair sY C →
        MMP.Flips.IsRelativelyNef ℂ sY g (MMP.Flips.logCanonicalDivisor K B) →
        ∀ t₀ : ℝ, 0 < t₀ →
          t₀ < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
          MMP.Flips.IsRelativelyNef ℂ sY g
            (MMP.Flips.logCanonicalDivisor K ((1 - t₀) • B + t₀ • C)) →
          (∀ t : ℝ, 0 < t → t < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            MMP.Flips.IsRelativelyNef ℂ sY g
              (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C))) ∧
          (∀ t t' : ℝ, 0 < t → t < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            0 < t' → t' < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            ∀ A : ProperCurve sY, A.IsContractedBy g →
            ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor Y) (x : ℝ)
              (n' : ℕ) (c' : Fin n' → ℝ) (L' : Fin n' → Divisor Y) (x' : ℝ),
              MMP.Flips.IsRIntersectionNumber ℂ sY
                (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) c L A x →
              MMP.Flips.IsRIntersectionNumber ℂ sY
                (MMP.Flips.logCanonicalDivisor K ((1 - t') • B + t' • C)) c' L' A x' →
              (x = 0 ↔ x' = 0))

/-! ### Elementary inequalities -/

private theorem div_le_div_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a / (2 * (a + 6)) ≤ b / (2 * (b + 6)) := by
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

private theorem div_lt_self' {a : ℝ} (ha : 0 < a) : a / (2 * (a + 6)) < a := by
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-! ### The final assembly -/

section Final

private theorem transformDivisor_smul' {X Y : Scheme.{0}} (φ : X.RationalMap Y) (a : ℝ)
    (D : RDivisor X) :
    RationalMap.transformDivisor φ (a • D) = a • RationalMap.transformDivisor φ D :=
  DivisorWithCoeffs.mapPrimeDivisors_smul _ a D

private theorem rationalMap_compHom_id {X Y : Scheme.{0}} (f : X.RationalMap Y) :
    f.compHom (𝟙 Y) = f := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep f
  exact congrArg Scheme.PartialMap.toRationalMap (Scheme.PartialMap.compHom_id g)

/-- `K + ((1 - s) B + s C) = (1 - s/t)(K + B) + (s/t)(K + ((1 - t) B + t C))`. -/
private theorem logCanonicalDivisor_radial_eq {X : Scheme.{0}} (K : Divisor X)
    (B C : RDivisor X) {s t : ℝ} (ht : t ≠ 0) :
    logCanonicalDivisor K ((1 - s) • B + s • C) =
      (1 - s / t) • logCanonicalDivisor K B +
        (s / t) • logCanonicalDivisor K ((1 - t) • B + t • C) := by
  refine Finsupp.ext fun P => ?_
  simp only [logCanonicalDivisor, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The transform of a radial boundary is radial. -/
private theorem transformDivisor_radial {X Y : Scheme.{0}} (φ : X.RationalMap Y) (B C : RDivisor X)
    (s : ℝ) : RationalMap.transformDivisor φ ((1 - s) • B + s • C) =
      (1 - s) • RationalMap.transformDivisor φ B + s • RationalMap.transformDivisor φ C := by
  rw [map_add, transformDivisor_smul', transformDivisor_smul']

/-- On a resolution `p : W ⟶ Y` with inverse `h`, every prime divisor of `Y` has a strict
transform: a prime divisor of `W` mapping birationally onto it, which is its transform by `h`. -/
private theorem exists_transformPrimeDivisor_eq_some {Y W : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sY : Y ⟶ Spec (.of ℂ)} (hY : IsNormalVariety ℂ sY) {p : W ⟶ Y}
    (hW : IsNormalVariety ℂ (p ≫ sY)) [IsProper p] (hpb : IsBirationalMorphism p)
    {h : Y.RationalMap W} (hinv : RationalMap.IsInverse p.toRationalMap h)
    (P : MMP.Mori.PrimeDivisor Y) :
    ∃ P' : MMP.Mori.PrimeDivisor W, p P'.genericPoint = P.genericPoint ∧
      IsIso (p.stalkMap P'.genericPoint) ∧ RationalMap.transformPrimeDivisor h P = some P' := by
  obtain ⟨E, hE, hiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hY hW hpb P
  have : IsSeparated sY := hY.1.toIsSeparated
  have : IsSeparated (p ≫ sY) := hW.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sY
  have := MMP.Fourfold.isSeparated_terminal (p ≫ sY)
  have : IsSeparated p := IsSeparated.of_comp p sY
  exact ⟨E, hE, hiso, (transformPrimeDivisor_eq_some_iff_of_isInverse p hpb hinv (𝟙 W)
    (rationalMap_compHom_id h) P E hE E).mpr rfl⟩

/-- **Assembly on the given resolution.** If `D = K + B` is crepant between `Y` and `Z` on every
common resolution of `φ`, and every `K_Z + φ_* C_s` is nef over `S`, then `φ` is a nef weak model
of every `(Y, C_s)`: on the resolution of the weak model at `t`, the comparison for `C_s` is
`s / t` times the comparison for `C_t`. -/
private theorem isNefWeakModel_radial {Y S Z : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [QuasiCompact sY] [QuasiCompact sZ] {πY : Y ⟶ S} {πZ : Z ⟶ S}
    (hYQ : IsQFactorial sY) (hZQ : IsQFactorial sZ) {K : Divisor Y} {B C : RDivisor Y}
    (hB0 : ∀ P, 0 ≤ B.coeff P) (hC0 : ∀ P, 0 ≤ C.coeff P)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {φ : Y.RationalMap Z}
    (hφ : IsNefWeakModel sY sZ sS πY πZ K ((1 - t) • B + t • C) φ)
    (hcomp : ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
      (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
        q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
        IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
        MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
        ∃ GY GZ : RDivisor W,
          MMP.Flips.IsRCartierPullback p
            (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) GY ∧
          MMP.Flips.IsRCartierPullback q
            (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
              (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B + t • C))) GZ ∧
          ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - t) • B + t • C).coeff P →
            ∃ P' : MMP.Mori.PrimeDivisor W,
              MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                (GY - GZ).coeff P' = 0)
    (hcrep : ∀ {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
      (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW → MMP.Mori.IsSmoothScheme sW → p ≫ sY = sW → q ≫ sZ = sW →
      IsProjectiveMorphism p →
      IsProjectiveMorphism q → IsBirationalMorphism p → IsBirationalMorphism q →
      RationalMap.IsInverse p.toRationalMap h → h.compHom q = φ →
      ∀ G₁ G₂ : RDivisor W, IsRCartierPullback p (logCanonicalDivisor K B) G₁ →
        IsRCartierPullback q (logCanonicalDivisor (RationalMap.transformDivisor φ K)
          (RationalMap.transformDivisor φ B)) G₂ → G₁ = G₂)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hnefZ : IsRelativelyNef ℂ sZ πZ (logCanonicalDivisor (RationalMap.transformDivisor φ K)
      (RationalMap.transformDivisor φ ((1 - s) • B + s • C)))) :
    IsNefWeakModel sY sZ sS πY πZ K ((1 - s) • B + s • C) φ ∧
      ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
        (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
        (h : Y.RationalMap W),
        MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
          q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
          IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
          MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
          ∃ GY GZ : RDivisor W,
            MMP.Flips.IsRCartierPullback p
              (MMP.Flips.logCanonicalDivisor K ((1 - s) • B + s • C)) GY ∧
            MMP.Flips.IsRCartierPullback q
              (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))) GZ ∧
            ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - s) • B + s • C).coeff P →
              ∃ P' : MMP.Mori.PrimeDivisor W,
                MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                  (GY - GZ).coeff P' = 0 := by
  classical
  have hYv := hφ.isNormalVariety_source
  have hZv := hφ.isNormalVariety_target
  have : IsSeparated sY := hYv.1.toIsSeparated
  have : IsSeparated sZ := hZv.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sY
  have := MMP.Fourfold.isSeparated_terminal sZ
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have ht : t ≠ 0 := ht0.ne'
  set c : ℝ := s / t with hc
  have hc0 : 0 < c := div_pos hs0 ht0
  -- the resolution of the weak model at `t`
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, hW₀s, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀,
    hhq₀, GY₀, GZ₀, hGY₀, hGZ₀, hA₀, hA₀q⟩ := hφ.exists_resolution
  have : IsProper p₀ := isProper_of_isProjectiveMorphism p₀ hp₀
  have : IsProper q₀ := isProper_of_isProjectiveMorphism q₀ hq₀
  have : IsDominant p₀ := hp₀b.isDominant
  have : IsDominant q₀ := hq₀b.isDominant
  have : IsSeparated p₀ := Crepant.isSeparated_of_comp_eq hp₀Y
  have hW₀n : IsNormalVariety ℂ (p₀ ≫ sY) := by rw [hp₀Y]; exact ⟨hW₀, inferInstance⟩
  have : QuasiCompact sW₀ := hW₀.toQuasiCompact
  have : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace sW₀
  -- the pull-backs of `D` and `D_Z`
  obtain ⟨G0Y, hG0Y, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p₀
    (isCartierCombination_of_isQFactorial hYQ (logCanonicalDivisor K B))
  obtain ⟨G0Z, hG0Z, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q₀
    (isCartierCombination_of_isQFactorial hZQ (logCanonicalDivisor
      (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ B)))
  have hG0 : G0Y = G0Z := hcrep sW₀ p₀ q₀ h₀ hW₀ hW₀s hp₀Y hq₀Z hp₀ hq₀ hp₀b hq₀b hinv₀ hhq₀ G0Y G0Z
    hG0Y hG0Z
  -- the pull-backs for `C_s`
  have hGYs : IsRCartierPullback p₀ (logCanonicalDivisor K ((1 - s) • B + s • C))
      ((1 - c) • G0Y + c • GY₀) := by
    rw [logCanonicalDivisor_radial_eq K B C ht]
    exact isRCartierPullback_add (isRCartierPullback_smul _ hG0Y) (isRCartierPullback_smul _ hGY₀)
  have hGZs : IsRCartierPullback q₀ (logCanonicalDivisor (RationalMap.transformDivisor φ K)
      (RationalMap.transformDivisor φ ((1 - s) • B + s • C))) ((1 - c) • G0Z + c • GZ₀) := by
    rw [transformDivisor_radial, logCanonicalDivisor_radial_eq _ _ _ ht, ← transformDivisor_radial]
    exact isRCartierPullback_add (isRCartierPullback_smul _ hG0Z) (isRCartierPullback_smul _ hGZ₀)
  have hdiff : (1 - c) • G0Y + c • GY₀ - ((1 - c) • G0Z + c • GZ₀) = c • (GY₀ - GZ₀) := by
    rw [hG0, smul_sub]; abel
  have hcoeff : ∀ P, ((1 - c) • G0Y + c • GY₀ - ((1 - c) • G0Z + c • GZ₀)).coeff P =
      c * (GY₀ - GZ₀).coeff P := fun P => by
    rw [hdiff]; rfl
  -- the positive components of `C_s` are those of `C_t`
  have hpos : ∀ P, 0 < ((1 - s) • B + s • C).coeff P → 0 < ((1 - t) • B + t • C).coeff P := by
    intro P hP
    have e : ∀ r : ℝ, ((1 - r) • B + r • C).coeff P = (1 - r) * B.coeff P + r * C.coeff P :=
      fun r => rfl
    rw [e] at hP ⊢
    have hb := hB0 P
    have hcc := hC0 P
    by_contra hneg
    push Not at hneg
    have h1 : B.coeff P = 0 := by nlinarith
    have h2 : C.coeff P = 0 := by nlinarith
    rw [h1, h2] at hP
    simp at hP
  refine ⟨{ isNormalVariety_source := hYv
            isProjectiveVariety_source := hφ.isProjectiveVariety_source
            comp_eq_source := hφ.comp_eq_source
            isCanonicalDivisor := hφ.isCanonicalDivisor
            isCartierCombination := isCartierCombination_of_isQFactorial hYQ _
            isNormalVariety_target := hZv
            isProjectiveVariety_target := hφ.isProjectiveVariety_target
            comp_eq_target := hφ.comp_eq_target
            isBirational := hφ.isBirational
            isOver := hφ.isOver
            not_isInverseExceptional := hφ.not_isInverseExceptional
            isRelativelyNef := hnefZ
            exists_resolution := ⟨W₀, inferInstance, inferInstance, inferInstance, sW₀, p₀, q₀, h₀,
              hW₀, hW₀s, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀, hhq₀, _, _, hGYs, hGZs,
              fun P => by rw [hcoeff]; exact mul_nonneg hc0.le (hA₀ P),
              fun P hP => hA₀q P (by rw [hcoeff] at hP; exact right_ne_zero_of_mul hP)⟩ },
    W₀, inferInstance, inferInstance, inferInstance, sW₀, p₀, q₀, h₀, hW₀, hW₀s, hp₀Y, hq₀Z, hp₀,
    hq₀, hp₀b, hq₀b, hinv₀, hhq₀, _, _, hGYs, hGZs, fun P hP => ?_⟩
  -- the comparison coefficient at the strict transform of a positive component vanishes
  obtain ⟨W₁, _, _, _, sW₁, p₁, q₁, h₁, hW₁, -, hp₁Y, hq₁Z, hp₁, hq₁, hp₁b, hq₁b, hinv₁, hhq₁,
    GY₁, GZ₁, hGY₁, hGZ₁, hzero⟩ := hcomp
  have : IsProper p₁ := isProper_of_isProjectiveMorphism p₁ hp₁
  have : IsDominant q₁ := hq₁b.isDominant
  have : IsSeparated p₁ := Crepant.isSeparated_of_comp_eq hp₁Y
  have hW₁n : IsNormalVariety ℂ (p₁ ≫ sY) := by rw [hp₁Y]; exact ⟨hW₁, inferInstance⟩
  obtain ⟨P₁, hP₁t, hP₁0⟩ := hzero P (hpos P hP)
  obtain ⟨Q₁, hQ₁, hQ₁iso, hQ₁t⟩ := exists_transformPrimeDivisor_eq_some hYv hW₁n hp₁b hinv₁ P
  obtain rfl : Q₁ = P₁ := Option.some_injective _ (hQ₁t.symm.trans hP₁t)
  obtain ⟨P₀, hP₀, hP₀iso, hP₀t⟩ := exists_transformPrimeDivisor_eq_some hYv hW₀n hp₀b hinv₀ P
  refine ⟨P₀, hP₀t, ?_⟩
  rw [hcoeff]
  have e1 : GY₀.coeff P₀ = GY₁.coeff Q₁ := by
    rw [MMP.Fourfold.coeff_eq_of_isRCartierPullback P₀ P hP₀ hGY₀,
      MMP.Fourfold.coeff_eq_of_isRCartierPullback Q₁ P hQ₁ hGY₁]
  have e2 : GZ₀.coeff P₀ = GZ₁.coeff Q₁ :=
    coeff_eq_coeff_of_isRCartierPullback p₀ q₀ h₀ hp₀b hinv₀ hhq₀ p₁ q₁ h₁ hp₁b hinv₁ hhq₁ hGZ₀
      hGZ₁ P P₀ Q₁ hP₀ hQ₁
  rw [DivisorWithCoeffs.coeff_sub, e1, e2, ← DivisorWithCoeffs.coeff_sub, hP₁0, mul_zero]

/-- `K + ((1 - s) B + s C) = (1 - s) (K + B) + s (K + C)`. -/
private theorem logCanonicalDivisor_affine {X : Scheme.{0}} (K : Divisor X) (B C : RDivisor X)
    (s : ℝ) :
    logCanonicalDivisor K ((1 - s) • B + s • C) =
      (1 - s) • logCanonicalDivisor K B + s • logCanonicalDivisor K C := by
  refine Finsupp.ext fun P => ?_
  simp only [logCanonicalDivisor, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

/-- An affine function nonnegative on an open interval and vanishing at one of its points vanishes
on the whole interval. -/
private theorem eq_zero_of_affine_nonneg {a b e s s' : ℝ}
    (h : ∀ σ : ℝ, 0 < σ → σ < e → 0 ≤ a + σ * b) (hs0 : 0 < s) (hse : s < e)
    (hz : a + s * b = 0) : a + s' * b = 0 := by
  have hb : b = 0 := by
    by_contra hb
    rcases lt_or_gt_of_ne hb with hb | hb
    · have := h ((s + e) / 2) (by linarith) (by linarith)
      nlinarith
    · have := h (s / 2) (by linarith) (by linarith)
      nlinarith
  subst hb
  simpa using hz

/-- **Equivalence of the radial nef models on `Z`.** If every `K_Z + φ_* C_s`, `0 < s < e`, is nef
over `S`, then on a resolution of `Z` the pull-backs of `K_Z + φ_* C_s` have the same zero-degree
curves for all `s`: their degrees are affine in `s` and nonnegative on `(0, e)`. -/
private theorem isNefModelEquivalent_radial {Y S Z : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsSeparated sS]
    [QuasiCompact sY] [QuasiCompact sZ] {πY : Y ⟶ S} {πZ : Z ⟶ S}
    (hZQ : IsQFactorial sZ) {K : Divisor Y} {B C : RDivisor Y} {t : ℝ} {φ : Y.RationalMap Z}
    (hφ : IsNefWeakModel sY sZ sS πY πZ K ((1 - t) • B + t • C) φ) {e : ℝ}
    (hnefs : ∀ s : ℝ, 0 < s → s < e → IsRelativelyNef ℂ sZ πZ
      (logCanonicalDivisor (RationalMap.transformDivisor φ K)
        (RationalMap.transformDivisor φ ((1 - s) • B + s • C))))
    {s s' : ℝ} (hs0 : 0 < s) (hse : s < e) (hs'0 : 0 < s') (hs'e : s' < e) :
    IsNefModelEquivalent sZ sZ sS πZ πZ
      (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ ((1 - s) • B + s • C))
      (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ ((1 - s') • B + s' • C))
      (𝟙 Z : Z ⟶ Z).toRationalMap := by
  classical
  have hYv := hφ.isNormalVariety_source
  have hZv := hφ.isNormalVariety_target
  have : IsSeparated sZ := hZv.1.toIsSeparated
  have : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have := MMP.Fourfold.isSeparated_terminal sZ
  haveI : φ.IsDominant := Crepant.isDominant_of_isBirational hφ.isBirational
  -- the fields not involving the resolution, from the weak model compared with itself
  have hid : φ.comp (𝟙 Z : Z ⟶ Z).toRationalMap = φ := by
    rw [Scheme.RationalMap.comp_toRationalMap, rationalMap_compHom_id]
  have E0 := (IsNefWeakModel.eq_of_isRCartierPullback_and_isNefModelEquivalent hφ hφ).2
    (𝟙 Z : Z ⟶ Z).toRationalMap hid
  -- the resolution of `Z`
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, hW₀s, hp₀Y, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, -, -,
    -⟩ := hφ.exists_resolution
  have : QuasiCompact sW₀ := hW₀.toQuasiCompact
  have : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace sW₀
  have : IsDominant q₀ := hq₀b.isDominant
  have : IsProper q₀ := isProper_of_isProjectiveMorphism q₀ hq₀
  obtain ⟨hq, hhq⟩ := hq₀b.exists_isInverse
  have hhq' : hq.compHom q₀ = (𝟙 Z : Z ⟶ Z).toRationalMap :=
    Crepant.compHom_eq_of_isInverse hhq
  subst hq₀Z
  -- the pull-backs of `K_Z + B_Z` and `K_Z + C_Z`
  set LB := logCanonicalDivisor (RationalMap.transformDivisor φ K)
    (RationalMap.transformDivisor φ B) with hLB
  set LC := logCanonicalDivisor (RationalMap.transformDivisor φ K)
    (RationalMap.transformDivisor φ C) with hLC
  obtain ⟨GB, hGB, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q₀
    (isCartierCombination_of_isQFactorial hZQ LB)
  obtain ⟨GC, hGC, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q₀
    (isCartierCombination_of_isQFactorial hZQ LC)
  have hL : ∀ σ : ℝ, logCanonicalDivisor (RationalMap.transformDivisor φ K)
      (RationalMap.transformDivisor φ ((1 - σ) • B + σ • C)) = (1 - σ) • LB + σ • LC := by
    intro σ
    rw [transformDivisor_radial, logCanonicalDivisor_affine]
  have hG : ∀ σ : ℝ, IsRCartierPullback q₀ (logCanonicalDivisor
      (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ ((1 - σ) • B + σ • C)))
      ((1 - σ) • GB + σ • GC) := by
    intro σ
    rw [hL]
    exact isRCartierPullback_add (isRCartierPullback_smul _ hGB) (isRCartierPullback_smul _ hGC)
  -- presentations of `GB`, `GC` by Cartier divisors
  obtain ⟨mB, rB, LB₀, LB', hLB₀, -, hpbB, hGBeq⟩ := hGB
  obtain ⟨mC, rC, LC₀, LC', hLC₀, -, hpbC, hGCeq⟩ := hGC
  have hLB'c : ∀ j, (LB' j).IsCartier := fun j => by
    obtain ⟨hB, hpb⟩ := hpbB j
    rw [← Divisor.IsPullback.pullback_eq (hLB₀ j) hpb]
    exact (hLB₀ j).isCartier_pullback q₀ hB
  have hLC'c : ∀ j, (LC' j).IsCartier := fun j => by
    obtain ⟨hB, hpb⟩ := hpbC j
    rw [← Divisor.IsPullback.pullback_eq (hLC₀ j) hpb]
    exact (hLC₀ j).isCartier_pullback q₀ hB
  -- the degree of the pull-back of `K_Z + φ_* C_σ` on a curve is affine in `σ`
  have hval : ∀ (Γ : ProperCurve (q₀ ≫ sZ)) (σ : ℝ) {m : ℕ} {r : Fin m → ℝ}
      {L : Fin m → Divisor W₀} {x : ℝ},
      IsRIntersectionNumber ℂ (q₀ ≫ sZ) ((1 - σ) • GB + σ • GC) r L Γ x →
      x = (1 - σ) * (∑ j, rB j * ((LB' j).degreeOn ℂ (q₀ ≫ sZ) Γ.ι Γ.dim_le (hLB'c j) : ℝ)) +
        σ * (∑ j, rC j * ((LC' j).degreeOn ℂ (q₀ ≫ sZ) Γ.ι Γ.dim_le (hLC'c j) : ℝ)) := by
    intro Γ σ m r L x hx
    have hxB := isRIntersectionNumber_sum_degreeOn ℂ (q₀ ≫ sZ) Γ rB LB' hLB'c
    have hxC := isRIntersectionNumber_sum_degreeOn ℂ (q₀ ≫ sZ) Γ rC LC' hLC'c
    rw [← hGBeq] at hxB
    rw [← hGCeq] at hxC
    exact (IsRIntersectionNumber.eq_and_linear ℂ (q₀ ≫ sZ) Γ).1 _ _ _ _ _ _ _ hx
      ((IsRIntersectionNumber.eq_and_linear ℂ (q₀ ≫ sZ) Γ).2 _ _ _ _ _ _ _ _ _ _ hxB hxC)
  -- and nonnegative on `(0, e)` for curves over a point of `S`
  have hnn : ∀ Γ : ProperCurve (q₀ ≫ sZ), Γ.IsContractedBy (q₀ ≫ πZ) → ∀ σ : ℝ, 0 < σ → σ < e →
      0 ≤ (1 - σ) * (∑ j, rB j * ((LB' j).degreeOn ℂ (q₀ ≫ sZ) Γ.ι Γ.dim_le (hLB'c j) : ℝ)) +
        σ * (∑ j, rC j * ((LC' j).degreeOn ℂ (q₀ ≫ sZ) Γ.ι Γ.dim_le (hLC'c j) : ℝ)) := by
    intro Γ hΓ σ hσ0 hσe
    obtain ⟨m, r, L, hLc, hpres, hall⟩ := isRelativelyNef_of_isRCartierPullback (𝟙 S) πZ
      (q₀ ≫ πZ) q₀ (by rw [Category.comp_id]) (hnefs σ hσ0 hσe) (hG σ)
    have hx := isRIntersectionNumber_sum_degreeOn ℂ (q₀ ≫ sZ) Γ r L hLc
    rw [← hpres] at hx
    rw [← hval Γ σ hx]
    exact hall Γ hΓ _ hx
  refine
    { isNormalVariety₁ := E0.isNormalVariety₁
      isProjectiveVariety₁ := E0.isProjectiveVariety₁
      comp_eq₁ := E0.comp_eq₁
      isCanonicalDivisor₁ := E0.isCanonicalDivisor₁
      isRelativelyNef₁ := hnefs s hs0 hse
      isNormalVariety₂ := E0.isNormalVariety₂
      isProjectiveVariety₂ := E0.isProjectiveVariety₂
      comp_eq₂ := E0.comp_eq₂
      isCanonicalDivisor₂ := E0.isCanonicalDivisor₂
      isRelativelyNef₂ := hnefs s' hs'0 hs'e
      isBirational := E0.isBirational
      isOver := E0.isOver
      exists_resolution := ⟨W₀, inferInstance, inferInstance, inferInstance, q₀ ≫ sZ,
        inferInstance, q₀, q₀, hq, hW₀, hW₀s, rfl, rfl, hq₀, hq₀, hq₀b, hq₀b, hhq, hhq',
        _, _, hG s, hG s', fun Γ hΓ => ?_⟩ }
  -- the zero-degree curves agree
  set a := ∑ j, rB j * ((LB' j).degreeOn ℂ (q₀ ≫ sZ) Γ.ι Γ.dim_le (hLB'c j) : ℝ)
  set b := ∑ j, rC j * ((LC' j).degreeOn ℂ (q₀ ≫ sZ) Γ.ι Γ.dim_le (hLC'c j) : ℝ)
  have haff : ∀ σ : ℝ, (1 - σ) * a + σ * b = a + σ * (b - a) := fun σ => by ring
  have hnn' : ∀ σ : ℝ, 0 < σ → σ < e → 0 ≤ a + σ * (b - a) := fun σ h0 h1 => by
    rw [← haff]; exact hnn Γ hΓ σ h0 h1
  have key : ∀ σ σ' : ℝ, 0 < σ → σ < e →
      (∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W₀) (x : ℝ),
        IsRIntersectionNumber ℂ (q₀ ≫ sZ) ((1 - σ) • GB + σ • GC) r L Γ x → x = 0) →
      ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W₀) (x : ℝ),
        IsRIntersectionNumber ℂ (q₀ ≫ sZ) ((1 - σ') • GB + σ' • GC) r L Γ x → x = 0 := by
    intro σ σ' hσ0 hσe h m r L x hx
    have hxB := isRIntersectionNumber_sum_degreeOn ℂ (q₀ ≫ sZ) Γ rB LB' hLB'c
    have hxC := isRIntersectionNumber_sum_degreeOn ℂ (q₀ ≫ sZ) Γ rC LC' hLC'c
    rw [← hGBeq] at hxB
    rw [← hGCeq] at hxC
    have h0 := h _ _ _ _ ((IsRIntersectionNumber.eq_and_linear ℂ (q₀ ≫ sZ) Γ).2 _ _ _ _ _ _ _ _
      (1 - σ) σ hxB hxC)
    rw [hval Γ σ' hx, haff]
    rw [haff] at h0
    exact eq_zero_of_affine_nonneg hnn' hσ0 hσe h0
  exact ⟨key s s' hs0 hse, key s' s hs'0 hs'e⟩

/-- The coefficients of a real terminal boundary are nonnegative. -/
private theorem coeff_nonneg_of_isRealTerminalPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : RDivisor X} (hB : IsRealTerminalPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : 0 ≤ B.coeff P := by
  by_cases h : B.coeff P = 0
  · exact h.ge
  · exact (hB.1.2.1 P h).1.le

/-- `D = K + B` is crepant between `Y` and `Z` along `φ`: on every smooth common model, the
pull-backs of `K_Y + B` and `K_Z + φ_* B` agree. -/
private def IsCrepantAlong {Y Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (sY : Y ⟶ Spec (.of ℂ))
    (sZ : Z ⟶ Spec (.of ℂ)) (φ : Y.RationalMap Z) (L : RDivisor Y) (LZ : RDivisor Z) : Prop :=
  ∀ {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W),
    MMP.Mori.IsVariety ℂ sW → MMP.Mori.IsSmoothScheme sW → p ≫ sY = sW → q ≫ sZ = sW →
    IsProjectiveMorphism p → IsProjectiveMorphism q → IsBirationalMorphism p →
    IsBirationalMorphism q → RationalMap.IsInverse p.toRationalMap h → h.compHom q = φ →
    ∀ G₁ G₂ : RDivisor W, IsRCartierPullback p L G₁ → IsRCartierPullback q LZ G₂ → G₁ = G₂

/-- **The conclusion from the crepancy of `D` and the nefness on `Z`.** -/
private theorem conclusion_of_isCrepantAlong {Y S Z : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsSeparated sS]
    [QuasiCompact sY] [QuasiCompact sZ] {πY : Y ⟶ S} {πZ : Z ⟶ S}
    (hYQ : IsQFactorial sY) (hZQ : IsQFactorial sZ) {K : Divisor Y} {B C : RDivisor Y}
    (hB : IsRealTerminalPair sY B) (hC : IsRealTerminalPair sY C) {e t : ℝ} (he : e < 1)
    (ht0 : 0 < t) (hte : t < e) {φ : Y.RationalMap Z}
    (hφ : IsNefWeakModel sY sZ sS πY πZ K ((1 - t) • B + t • C) φ)
    (hcomp : ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
      (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
      (h : Y.RationalMap W),
      MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
        q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
        IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
        MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
        ∃ GY GZ : RDivisor W,
          MMP.Flips.IsRCartierPullback p
            (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) GY ∧
          MMP.Flips.IsRCartierPullback q
            (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
              (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B + t • C))) GZ ∧
          ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - t) • B + t • C).coeff P →
            ∃ P' : MMP.Mori.PrimeDivisor W,
              MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                (GY - GZ).coeff P' = 0)
    (hcrep : IsCrepantAlong sY sZ φ (logCanonicalDivisor K B)
      (logCanonicalDivisor (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ B)))
    (hnefs : ∀ s : ℝ, 0 < s → s < e → IsRelativelyNef ℂ sZ πZ
      (logCanonicalDivisor (RationalMap.transformDivisor φ K)
        (RationalMap.transformDivisor φ ((1 - s) • B + s • C)))) :
    (∀ s : ℝ, 0 < s → s < e →
      IsNefWeakModel sY sZ sS πY πZ K ((1 - s) • B + s • C) φ ∧
      ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
        (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
        (h : Y.RationalMap W),
        MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
          q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
          IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
          MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
          ∃ GY GZ : RDivisor W,
            MMP.Flips.IsRCartierPullback p
              (MMP.Flips.logCanonicalDivisor K ((1 - s) • B + s • C)) GY ∧
            MMP.Flips.IsRCartierPullback q
              (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))) GZ ∧
            ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - s) • B + s • C).coeff P →
              ∃ P' : MMP.Mori.PrimeDivisor W,
                MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                  (GY - GZ).coeff P' = 0) ∧
    (∀ s s' : ℝ, 0 < s → s < e → 0 < s' → s' < e →
      IsNefModelEquivalent sZ sZ sS πZ πZ
        (MMP.Mori.RationalMap.transformDivisor φ K)
        (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))
        (MMP.Mori.RationalMap.transformDivisor φ K)
        (MMP.Mori.RationalMap.transformDivisor φ ((1 - s') • B + s' • C))
        (𝟙 Z : Z ⟶ Z).toRationalMap) := by
  refine ⟨fun s hs0 hse => isNefWeakModel_radial hYQ hZQ (coeff_nonneg_of_isRealTerminalPair hB)
    (coeff_nonneg_of_isRealTerminalPair hC) ht0 (hte.trans he) hφ hcomp
    hcrep hs0 (hse.trans he)
    (hnefs s hs0 hse),
    fun s s' hs0 hse hs'0 hs'e => isNefModelEquivalent_radial hZQ hφ hnefs hs0 hse hs'0 hs'e⟩

end Final

/-! ### Tools for the program -/

section ProgramTools

/-- A function of the null data takes the same value on data with the same number of
boundaries, weights and Cartier index. -/
private theorem apply_eq_of_weight_eq (F : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ) {s s' : ℕ}
    {w : Fin s → ℝ} {w' : Fin s' → ℝ} {m m' : ℕ} (hs : s' = s) (hm : m' = m)
    (hw : ∀ i, w' i = w (Fin.cast hs i)) : F s' w' m' = F s w m := by
  subst hs hm
  congr 1
  funext i
  simpa using hw i

/-- A curve contracted by a proper morphism maps to a closed point, which is not a proper
curve. -/
private theorem not_isProperCurve_of_isContractedBy {k : Type} [Field k] {W T : Scheme.{0}}
    {sW : W ⟶ Spec (.of k)} (sT : T ⟶ Spec (.of k)) (q : W ⟶ T) [IsProper q]
    (Γ : ProperCurve sW) (hΓ : Γ.IsContractedBy q) : ¬ IsProperCurve sT (q Γ.point) := by
  intro h
  have himg : q '' closure ({Γ.point} : Set W) = {q Γ.point} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨Γ.point, subset_closure rfl, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hΓ x hx
  have hc : IsClosed ({q Γ.point} : Set T) := himg ▸ q.isClosedMap _ isClosed_closure
  have h1 := h.dim_eq
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, hc.closure_eq,
    topologicalKrullDim_eq_zero_of_subsingleton] at h1
  exact absurd h1 (by norm_num)

variable {T W : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)} [IsSeparated sT] [LocallyOfFiniteType sT]
  [QuasiCompact sT] [IsLocallyNoetherian T] [IsNormal T] [IsIntegral W] [IsLocallyNoetherian W]
  [IsNormal W]

/-- The pull-back of an `ℝ`-Cartier divisor has degree zero on a curve whose image is not a
proper curve. -/
private theorem eq_zero_of_isRCartierPullback_of_not_isProperCurve (q : W ⟶ T)
    {sW : W ⟶ Spec (.of ℂ)} (hq : q ≫ sT = sW) [QuasiCompact sW] [CompactSpace T]
    [CompactSpace W] {M : RDivisor T} {G : RDivisor W} (hG : IsRCartierPullback q M G)
    (Γ : ProperCurve sW) (hΓ : ¬ IsProperCurve sT (q Γ.point)) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor W} {x : ℝ} (hx : IsRIntersectionNumber ℂ sW G r L Γ x) : x = 0 := by
  subst hq
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, -, hpb, hGeq⟩ := hG
  choose hB hpbj using hpb
  obtain rfl : L₁ = fun j => (L₀ j).pullback (hL₀ j) (hB j) :=
    funext fun j => (Divisor.IsPullback.pullback_eq (hL₀ j) (hpbj j)).symm
  have hL₁c : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).IsCartier := fun j =>
    (hL₀ j).isCartier_pullback q (hB j)
  have hx0 := isRIntersectionNumber_sum_degreeOn ℂ (q ≫ sT) Γ r₀ _ hL₁c
  rw [← hGeq] at hx0
  rw [(IsRIntersectionNumber.eq_and_linear ℂ (q ≫ sT) Γ).1 _ _ _ _ _ _ _ hx hx0]
  have hdeg : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).degreeOn ℂ (q ≫ sT) Γ.ι Γ.dim_le
      (hL₁c j) = 0 := fun j => degreeOn_pullback_eq_zero q (hL₀ j) (hB j) Γ hΓ
  simp [hdeg]

/-- **Projection formula** for the pull-back of an `ℝ`-Cartier divisor: on a curve `Γ` with
image the proper curve `A`, `q^*M · Γ = [k(Γ) : k(A)] (M · A)`. -/
private theorem eq_mul_of_isRCartierPullback (q : W ⟶ T) {sW : W ⟶ Spec (.of ℂ)}
    (hq : q ≫ sT = sW) [QuasiCompact sW] [CompactSpace T] [CompactSpace W] {M : RDivisor T}
    {G : RDivisor W} (hG : IsRCartierPullback q M G) (Γ : ProperCurve sW) (A : ProperCurve sT)
    (hA : A.point = q Γ.point) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber ℂ sW G r L Γ x) {m' : ℕ} {r' : Fin m' → ℝ}
    {L' : Fin m' → Divisor T} {y : ℝ} (hy : IsRIntersectionNumber ℂ sT M r' L' A y) :
    x = (residueFieldDegree q Γ.point : ℝ) * y := by
  subst hq
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, hMeq, hpb, hGeq⟩ := hG
  choose hB hpbj using hpb
  obtain rfl : L₁ = fun j => (L₀ j).pullback (hL₀ j) (hB j) :=
    funext fun j => (Divisor.IsPullback.pullback_eq (hL₀ j) (hpbj j)).symm
  have hL₁c : ∀ j, ((L₀ j).pullback (hL₀ j) (hB j)).IsCartier := fun j =>
    (hL₀ j).isCartier_pullback q (hB j)
  have hx0 := isRIntersectionNumber_sum_degreeOn ℂ (q ≫ sT) Γ r₀ _ hL₁c
  rw [← hGeq] at hx0
  rw [(IsRIntersectionNumber.eq_and_linear ℂ (q ≫ sT) Γ).1 _ _ _ _ _ _ _ hx hx0]
  have hy0 := isRIntersectionNumber_sum_degreeOn ℂ sT A r₀ L₀ hL₀
  rw [← hMeq] at hy0
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sT A).1 _ _ _ _ _ _ _ hy hy0]
  have hdeg : ∀ j, ((((L₀ j).pullback (hL₀ j) (hB j)).degreeOn ℂ (q ≫ sT) Γ.ι Γ.dim_le
      (hL₁c j) : ℤ) : ℝ) =
      (residueFieldDegree q Γ.point : ℝ) * (L₀ j).degreeOn ℂ sT A.ι A.dim_le (hL₀ j) := by
    intro j
    rw [degreeOn_pullback_eq_mul q (hL₀ j) (hB j) Γ A hA]
    push_cast; rfl
  simp only [hdeg, mul_left_comm (r₀ _), ← Finset.mul_sum]

/-- **The pull-back of an `ℝ`-Cartier divisor vanishes on contracted curves.** -/
private theorem eq_zero_of_isRCartierPullback_of_isContractedBy (q : W ⟶ T) [IsProper q]
    {sW : W ⟶ Spec (.of ℂ)} (hq : q ≫ sT = sW) [QuasiCompact sW] [CompactSpace T]
    [CompactSpace W] {M : RDivisor T} {G : RDivisor W} (hG : IsRCartierPullback q M G)
    (Γ : ProperCurve sW) (hΓ : Γ.IsContractedBy q) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor W} {x : ℝ} (hx : IsRIntersectionNumber ℂ sW G r L Γ x) : x = 0 :=
  eq_zero_of_isRCartierPullback_of_not_isProperCurve q hq hG Γ
    (not_isProperCurve_of_isContractedBy sT q Γ hΓ) hx

/-- **Nefness descends along a proper surjective morphism**: if the pull-back of `M` is nef over
`S`, so is `M`, since every curve over a point of `S` lifts to a curve with a finite residue
extension. -/
private theorem isRelativelyNef_of_isRCartierPullback_of_surjective {S : Scheme.{0}}
    [CompactSpace W] (q : W ⟶ T) [IsProper q] [Surjective q] {sW : W ⟶ Spec (.of ℂ)}
    (hq : q ≫ sT = sW) [LocallyOfFiniteType sW] [QuasiCompact sW] (πT : T ⟶ S) {M : RDivisor T}
    (hM : IsCartierCombination M) {G : RDivisor W} (hG : IsRCartierPullback q M G)
    (hnef : IsRelativelyNef ℂ sW (q ≫ πT) G) : IsRelativelyNef ℂ sT πT M := by
  subst hq
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace sT
  obtain ⟨m, r, L, hL, hMeq⟩ := hM
  refine ⟨m, r, L, hL, by rw [hMeq]; simp only [toRDivisor_eq_mapCoeffs], fun A hA x hx => ?_⟩
  obtain ⟨Γ, hΓA, hd⟩ := exists_properCurve_map_eq (q ≫ sT) sT q rfl A
  have hΓ : Γ.IsContractedBy (q ≫ πT) := by
    intro w hw
    have hqw : q w ∈ closure {A.point} := by
      rw [← hΓA]
      exact specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hw).map q.continuous)
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hA (q w) hqw, hΓA]
  obtain ⟨mG, rG, LG, hLG, hGeq, hall⟩ := hnef
  have hxG := isRIntersectionNumber_sum_degreeOn ℂ (q ≫ sT) Γ rG LG hLG
  rw [← hGeq] at hxG
  have h0 := hall Γ hΓ _ hxG
  rw [eq_mul_of_isRCartierPullback q rfl hG Γ A hΓA.symm hxG hx] at h0
  have hdpos : (0 : ℝ) < residueFieldDegree q Γ.point := by
    exact_mod_cast Nat.pos_of_ne_zero hd
  by_contra hneg
  push Not at hneg
  nlinarith

end ProgramTools

section ProgramTools2

/-- The negative of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_neg {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {F : RDivisor X} (hF : IsCartierCombination F) : IsCartierCombination (-F) := by
  obtain ⟨m, r, L, hL, hFeq⟩ := hF
  exact ⟨m, fun j => -r j, L, hL, by rw [hFeq]; simp [neg_smul, Finset.sum_neg_distrib]⟩

/-- The difference of `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_sub {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    {F G : RDivisor X} (hF : IsCartierCombination F) (hG : IsCartierCombination G) :
    IsCartierCombination (F - G) := by
  obtain ⟨m, r, L, hL, hFeq⟩ := hF
  obtain ⟨m', r', L', hL', hGeq⟩ := isCartierCombination_neg hG
  refine ⟨m + m', Fin.append r r', Fin.append L L', fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa using hL j
    · simpa using hL' j
  · rw [sub_eq_add_neg, hFeq, hGeq, Fin.sum_univ_add]
    simp

/-- An `ℝ`-Cartier divisor all of whose degrees on the curves contracted by `q` vanish is
`q`-nef. -/
private theorem isRelativelyNef_of_forall_eq_zero {W T : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)}
    [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W] (q : W ⟶ T) {G : RDivisor W}
    (hG : IsCartierCombination G)
    (h0 : ∀ Γ : ProperCurve sW, Γ.IsContractedBy q → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor W) (x : ℝ), IsRIntersectionNumber ℂ sW G r L Γ x → x = 0) :
    IsRelativelyNef ℂ sW q G := by
  obtain ⟨m, r, L, hL, hGeq⟩ := hG
  exact ⟨m, r, L, hL, by rw [hGeq]; simp only [toRDivisor_eq_mapCoeffs],
    fun Γ hΓ x hx => (h0 Γ hΓ _ _ _ _ hx).ge⟩

/-- **Negativity, both ways.** An `ℝ`-Cartier divisor on `W` which is exceptional over `T` and has
degree zero on every curve contracted by the projective birational `q : W ⟶ T` is zero. -/
private theorem eq_zero_of_forall_eq_zero_of_transformDivisor_eq_zero {W T : Scheme.{0}}
    {sW : W ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} [QuasiCompact sW] [IsLocallyNoetherian T]
    [IsNormal T] [IsLocallyNoetherian W] [IsNormal W] (hT : IsNormalVariety ℂ sT)
    (hW : IsNormalVariety ℂ sW) (q : W ⟶ T) (hq : q ≫ sT = sW) (hqp : IsProjectiveMorphism q)
    (hqb : IsBirationalMorphism q) {F : RDivisor W} (hF : IsCartierCombination F)
    (htr : RationalMap.transformDivisor q.toRationalMap F = 0)
    (h0 : ∀ Γ : ProperCurve sW, Γ.IsContractedBy q → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor W) (x : ℝ), IsRIntersectionNumber ℂ sW F r L Γ x → x = 0) :
    F = 0 := by
  have h0' : ∀ Γ : ProperCurve sW, Γ.IsContractedBy q → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor W) (x : ℝ), IsRIntersectionNumber ℂ sW (-F) r L Γ x → x = 0 := by
    intro Γ hΓ m r L x hx
    obtain ⟨hL, d, hFeq, hd, rfl⟩ := hx
    have := h0 Γ hΓ m (fun j => -r j) L (-(∑ j, r j * (d j : ℝ)))
      ⟨hL, d, by rw [← neg_neg F, hFeq]; simp [neg_smul, Finset.sum_neg_distrib], hd,
        by simp [Finset.sum_neg_distrib, neg_mul]⟩
    linarith
  have h1 := isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor ℂ sT sW hT hW q
    hq hqp hqb hF (isRelativelyNef_of_forall_eq_zero q (isCartierCombination_neg hF) h0')
    (by rw [htr]; exact DivisorWithCoeffs.isEffective_iff_nonneg.mpr le_rfl)
  have h2 := isEffective_of_isRelativelyNef_neg_of_isEffective_transformDivisor ℂ sT sW hT hW q
    hq hqp hqb (isCartierCombination_neg hF)
    (by rw [neg_neg]; exact isRelativelyNef_of_forall_eq_zero q hF h0)
    (by rw [map_neg, htr, neg_zero]; exact DivisorWithCoeffs.isEffective_iff_nonneg.mpr le_rfl)
  exact le_antisymm (neg_nonneg.mp (DivisorWithCoeffs.isEffective_iff_nonneg.mp h2))
    (DivisorWithCoeffs.isEffective_iff_nonneg.mp h1)

/-- The linear extension of a partial map on prime divisors commutes with regarding a divisor as
an `ℝ`-divisor. -/
private theorem mapPrimeDivisors_toRDivisor {X Y : Scheme.{0}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toRDivisor D) =
      Divisor.toRDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, map_add, hD, hD', map_add, map_add]
  | single G n =>
    have e : ∀ {Z : Scheme.{0}} (P : MMP.Mori.PrimeDivisor Z) (n : ℤ),
        Divisor.toRDivisor (Finsupp.single P n : Divisor Z) = Finsupp.single P (n : ℝ) := by
      intro Z P n
      simp [Divisor.toRDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom]
    rw [e, DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases φ G with _ | E
    · simp
    · simp [e]

/-- The birational transform commutes with regarding a divisor as an `ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (D : Divisor X) :
    RationalMap.transformDivisor φ (Divisor.toRDivisor D) =
      Divisor.toRDivisor (RationalMap.transformDivisor φ D) :=
  mapPrimeDivisors_toRDivisor _ D

/-- The transform of an adjoint is the adjoint of the transforms. -/
private theorem transformDivisor_logCanonicalDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (K : Divisor X) (C : RDivisor X) :
    RationalMap.transformDivisor φ (logCanonicalDivisor K C) =
      logCanonicalDivisor (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ C) := by
  rw [logCanonicalDivisor, map_add, transformDivisor_toRDivisor, logCanonicalDivisor]

/-- The transform along the identity is the identity. -/
private theorem transformDivisor_id {X : Scheme.{0}} [IsReduced X]
    [IsSeparated (X ↘ CategoryTheory.Limits.terminal Scheme)] {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    RationalMap.transformDivisor (𝟙 X : X ⟶ X).toRationalMap D = D := by
  have hφ : RationalMap.transformPrimeDivisor (X := X) (𝟙 X : X ⟶ X).toRationalMap = some :=
    funext fun G => (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 X) G G).mpr
      rfl
  change DivisorWithCoeffs.mapPrimeDivisors _ D = D
  rw [hφ]
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, hD, hD']
  | single G r => rw [DivisorWithCoeffs.mapPrimeDivisors_single]; rfl

end ProgramTools2

section CommonModels

variable {X T W : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [IsIntegral W] [IsLocallyNoetherian W]
  [IsNormal W] {sX : X ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)}

/-- On a common model `p : W ⟶ X`, `q : W ⟶ T` of `ψ = q ∘ p⁻¹`, two prime divisors of `X` with
the same transform under `ψ` coincide. -/
private theorem eq_of_transformPrimeDivisor_eq_some (hX : IsNormalVariety ℂ sX)
    (hT : IsNormalVariety ℂ sT) (p : W ⟶ X) (q : W ⟶ T) {h : X.RationalMap W} [IsProper p]
    (hpX : IsNormalVariety ℂ (p ≫ sX)) (hqT : IsNormalVariety ℂ (q ≫ sT))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : RationalMap.IsInverse p.toRationalMap h) {ψ : X.RationalMap T}
    (hψ : h.compHom q = ψ) {G G' : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor T}
    (hG : RationalMap.transformPrimeDivisor ψ G = some F)
    (hG' : RationalMap.transformPrimeDivisor ψ G' = some F) : G' = G := by
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated sT := hT.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sX
  have := MMP.Fourfold.isSeparated_terminal sT
  have : IsSeparated (p ≫ sX) := hpX.1.toIsSeparated
  have : IsSeparated (q ≫ sT) := hqT.1.toIsSeparated
  have : IsSeparated p := IsSeparated.of_comp p sX
  have : IsSeparated q := IsSeparated.of_comp q sT
  have : IsDominant q := hqb.isDominant
  obtain ⟨P, hP, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hpX hpb G
  obtain ⟨P', hP', -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hpX hpb G'
  have hq := (transformPrimeDivisor_eq_some_iff_of_isInverse p hpb hinv q hψ G P hP F).mp hG
  have hq' := (transformPrimeDivisor_eq_some_iff_of_isInverse p hpb hinv q hψ G' P' hP' F).mp hG'
  have hPP : P.genericPoint = P'.genericPoint :=
    Crepant.eq_of_apply_eq_of_coheight_le_one q hqb.functionFieldMap_bijective (hq'.trans hq.symm)
      (by rw [hq]; exact Crepant.coheight_genericPoint_le_one F)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (hP'.symm.trans ((congrArg (fun x => p x) hPP).symm.trans hP))

/-- On a common model of `ψ`, the coefficient of a transform `ψ_* D` along `ψ_* G` is the
coefficient of `D` along `G`. -/
private theorem transformDivisor_apply_of_eq_some (hX : IsNormalVariety ℂ sX)
    (hT : IsNormalVariety ℂ sT) (p : W ⟶ X) (q : W ⟶ T) {h : X.RationalMap W} [IsProper p]
    (hpX : IsNormalVariety ℂ (p ≫ sX)) (hqT : IsNormalVariety ℂ (q ≫ sT))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : RationalMap.IsInverse p.toRationalMap h) {ψ : X.RationalMap T}
    (hψ : h.compHom q = ψ) {G : MMP.Mori.PrimeDivisor X} {F : MMP.Mori.PrimeDivisor T}
    (hG : RationalMap.transformPrimeDivisor ψ G = some F) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : RationalMap.transformDivisor ψ D F = D G :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hG
    (fun _ hG' => eq_of_transformPrimeDivisor_eq_some hX hT p q hpX hqT hpb hqb hinv hψ hG hG') D

/-- **The comparison of a common model is exceptional over the target.** On a common model
`p : W ⟶ X`, `q : W ⟶ T` of a birational map `ψ` extracting no divisor of `T`, the difference
`p^* L - q^* M` of the pull-backs of divisors `L` and `M` with `M = ψ_* L` coefficientwise has
push-forward zero on `T`. -/
private theorem transformDivisor_sub_eq_zero (hX : IsNormalVariety ℂ sX)
    (hT : IsNormalVariety ℂ sT) (p : W ⟶ X) (q : W ⟶ T) {h : X.RationalMap W} [IsProper p]
    [IsProper q] (hpX : IsNormalVariety ℂ (p ≫ sX)) (hqT : IsNormalVariety ℂ (q ≫ sT))
    (hpb : IsBirationalMorphism p) (hqb : IsBirationalMorphism q)
    (hinv : RationalMap.IsInverse p.toRationalMap h) {ψ : X.RationalMap T}
    (hψ : h.compHom q = ψ)
    {L : RDivisor X} {M : RDivisor T}
    (hcorr : ∀ F : MMP.Mori.PrimeDivisor T, ∃ G, RationalMap.transformPrimeDivisor ψ G = some F ∧
      M.coeff F = L.coeff G)
    {G₁ G₂ : RDivisor W} (hG₁ : IsRCartierPullback p L G₁) (hG₂ : IsRCartierPullback q M G₂) :
    RationalMap.transformDivisor q.toRationalMap (G₁ - G₂) = 0 := by
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated sT := hT.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sX
  have := MMP.Fourfold.isSeparated_terminal sT
  have : IsSeparated (p ≫ sX) := hpX.1.toIsSeparated
  have : IsSeparated (q ≫ sT) := hqT.1.toIsSeparated
  have : IsSeparated p := IsSeparated.of_comp p sX
  have : IsSeparated q := IsSeparated.of_comp q sT
  have : IsDominant q := hqb.isDominant
  refine Finsupp.ext fun F => ?_
  obtain ⟨P, hPF, hPiso, hPtr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hT hqT hqb F
  obtain ⟨G, hGF, hLM⟩ := hcorr F
  obtain ⟨PG, hPG, hPGiso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hX hpX hpb G
  have hqPG : q PG.genericPoint = F.genericPoint :=
    (transformPrimeDivisor_eq_some_iff_of_isInverse p hpb hinv q hψ G PG hPG F).mp hGF
  have hPPG : P.genericPoint = PG.genericPoint :=
    Crepant.eq_of_apply_eq_of_coheight_le_one q hqb.functionFieldMap_bijective
      (hqPG.trans hPF.symm) (by rw [hPF]; exact Crepant.coheight_genericPoint_le_one F)
  obtain rfl : P = PG := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hPPG
  haveI := hPiso
  haveI := hPGiso
  have e1 := MMP.Fourfold.coeff_eq_of_isRCartierPullback P G hPG hG₁
  have e2 := MMP.Fourfold.coeff_eq_of_isRCartierPullback P F hPF hG₂
  rw [hPtr]
  change (G₁ - G₂).coeff P = (0 : RDivisor T).coeff F
  rw [DivisorWithCoeffs.coeff_sub, e1, e2, hLM, sub_self]
  rfl

end CommonModels

/-- **The identity is a nef weak model** of a `ℚ`-factorial projective pair with nef adjoint. -/
private theorem isNefWeakModel_id {X S : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    {sS : S ⟶ Spec (.of ℂ)} {πX : X ⟶ S} (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXQ : IsQFactorial sX) (hπ : πX ≫ sS = sX) {K : Divisor X}
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) {C : RDivisor X}
    (hnef : IsRelativelyNef ℂ sX πX (logCanonicalDivisor K C)) :
    IsNefWeakModel sX sX sS πX πX K C (𝟙 X : X ⟶ X).toRationalMap := by
  have hXv : IsNormalVariety ℂ sX := hXQ.1
  haveI : MMP.Mori.IsVariety ℂ sX := hXv.1
  have : IsSeparated sX := hXv.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sX
  have hid : ∀ G : MMP.Mori.PrimeDivisor X,
      RationalMap.transformPrimeDivisor (𝟙 X : X ⟶ X).toRationalMap G = some G := fun G =>
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 X) G G).mpr rfl
  obtain ⟨W', r, p', hW'v, hW'sm, -, -, -, hp'proj, hp'b⟩ :=
    MMP.Fourfold.exists_common_model_over sX (𝟙 X) (𝟙 X) (isBirationalMorphism_of_isIso _)
      (isBirationalMorphism_of_isIso _) (by rw [Category.id_comp]; exact hXv)
      (by rw [Category.id_comp]; exact hXv)
  rw [Category.id_comp] at hW'v hW'sm
  have : IsIntegral W' := hW'v.1.toIsIntegral
  have : IsNormal W' := hW'v.2
  have : LocallyOfFiniteType (p' ≫ sX) := hW'v.1.toLocallyOfFiniteType
  have : QuasiCompact (p' ≫ sX) := hW'v.1.toQuasiCompact
  have : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian (p' ≫ sX)
  have : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace (p' ≫ sX)
  have : IsDominant p' := hp'b.isDominant
  obtain ⟨h, hh⟩ := hp'b.exists_isInverse
  obtain ⟨G, hG, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p'
    (isCartierCombination_of_isQFactorial hXQ (logCanonicalDivisor K C))
  have hG' : IsRCartierPullback p' (logCanonicalDivisor
      (RationalMap.transformDivisor (𝟙 X : X ⟶ X).toRationalMap K)
      (RationalMap.transformDivisor (𝟙 X : X ⟶ X).toRationalMap C)) G := by
    rw [transformDivisor_id, transformDivisor_id]; exact hG
  refine
    { isNormalVariety_source := hXv
      isProjectiveVariety_source := hXp
      comp_eq_source := hπ
      isCanonicalDivisor := hK
      isCartierCombination := isCartierCombination_of_isQFactorial hXQ _
      isNormalVariety_target := hXv
      isProjectiveVariety_target := hXp
      comp_eq_target := hπ
      isBirational := isBirationalMorphism_of_isIso (𝟙 X)
      isOver := by
        change (𝟙 X : X ⟶ X).toRationalMap.compHom πX = πX.toRationalMap
        rw [toRationalMap_compHom, Category.id_comp]
      not_isInverseExceptional := fun F hF => hF F (hid F)
      isRelativelyNef := by rw [transformDivisor_id, transformDivisor_id]; exact hnef
      exists_resolution := ⟨W', inferInstance, inferInstance, inferInstance, p' ≫ sX, p', p', h,
        hW'v.1, hW'sm, rfl, rfl, hp'proj, hp'proj, hp'b, hp'b, hh,
        Crepant.compHom_eq_of_isInverse hh, G, G, hG, hG', fun P => by simp,
        fun P hP => absurd (by simp) hP⟩ }

/-! ### Convex combinations of real terminal boundaries -/

section Convex

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- **Log discrepancies are affine in the boundary.** On a `ℚ`-factorial variety, a log
discrepancy of `(1 - t) B + t C` along a divisor `E` is `(1 - t) a_B + t a_C` for log
discrepancies `a_B`, `a_C` of `B`, `C` along `E`, all computed with one rational top form. -/
private theorem exists_isLogDiscrepancy_of_convex (hXQ : IsQFactorial sX) {n : ℕ}
    {B C : RDivisor X} {t : ℝ} {E : DivisorOver ℂ sX} {a : ℝ}
    (h : MMP.Intersection.IsLogDiscrepancy sX n ((1 - t) • B + t • C) E a) :
    ∃ aB aC : ℝ, MMP.Intersection.IsLogDiscrepancy sX n B E aB ∧
      MMP.Intersection.IsLogDiscrepancy sX n C E aC ∧ a = (1 - t) * aB + t * aC := by
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isIntegral
  haveI := E.isDominant
  obtain ⟨hnv, hprop, ω, hω0, ⟨K, hK, hKc⟩, -, -, -, -, -, -, -, -⟩ := id h
  haveI : IsProper E.f := hprop
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  -- a log discrepancy of any boundary with the form `ω`
  have hex : ∀ D : RDivisor X, ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X)
      (L' : Fin m → Divisor E.Y), (∀ i, (L i).IsCartier) ∧
      (∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + D.coeff Γ = ∑ i, r i * (L i).coeff Γ) ∧
      (∀ i, ∃ hL, (L i).IsPullback E.f hL (L' i)) := by
    intro D
    obtain ⟨m, r, L, hL, hDeq⟩ := isCartierCombination_of_isQFactorial hXQ
      (Divisor.toRDivisor K + D)
    have hDeq' : Divisor.toRDivisor K + D = ∑ j, r j • Divisor.toRDivisor (L j) := by
      simpa only [toRDivisor_eq_mapCoeffs] using hDeq
    choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hL j)
    refine ⟨m, r, L, L', hL, fun Γ => ?_, fun j => ⟨_, hL' j⟩⟩
    have := congrArg (fun D : RDivisor X => D.coeff Γ) hDeq'
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this, hKc Γ]
  obtain ⟨mB, rB, LB, LB', hLB, hrelB, hpbB⟩ := hex B
  obtain ⟨mC, rC, LC, LC', hLC, hrelC, hpbC⟩ := hex C
  set aB := 1 + (E.ordPullback ω : ℝ) - ∑ i, rB i * ((LB' i).coeff E.E : ℝ)
  set aC := 1 + (E.ordPullback ω : ℝ) - ∑ i, rC i * ((LC' i).coeff E.E : ℝ)
  have hB : MMP.Intersection.IsLogDiscrepancy sX n B E aB :=
    ⟨hnv, hprop, ω, hω0, ⟨K, hK, hKc⟩, mB, rB, LB, LB', hLB, hrelB, hpbB, rfl⟩
  have hC : MMP.Intersection.IsLogDiscrepancy sX n C E aC :=
    ⟨hnv, hprop, ω, hω0, ⟨K, hK, hKc⟩, mC, rC, LC, LC', hLC, hrelC, hpbC, rfl⟩
  have ht : MMP.Intersection.IsLogDiscrepancy sX n ((1 - t) • B + t • C) E
      ((1 - t) * aB + t * aC) := by
    refine ⟨hnv, hprop, ω, hω0, ⟨K, hK, hKc⟩, mB + mC, Fin.append ((1 - t) • rB) (t • rC),
      Fin.append LB LC, Fin.append LB' LC', fun i => ?_, fun Γ => ?_, fun i => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using hLB j
      · simpa using hLC j
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
        DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
      have h1 := hrelB Γ
      have h2 := hrelC Γ
      simp only [mul_assoc, ← Finset.mul_sum]
      linear_combination (1 - t) * h1 + t * h2
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa using hpbB j
      · simpa using hpbC j
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul]
      simp only [aB, aC, mul_assoc, ← Finset.mul_sum]
      ring
  exact ⟨aB, aC, hB, hC, MMP.Threefold.Bridges.IsLogDiscrepancy.unique h ht⟩

/-- **A convex combination of real terminal boundaries is real terminal** on a `ℚ`-factorial
variety. -/
private theorem isRealTerminalPair_convex (hXQ : IsQFactorial sX) {B C : RDivisor X}
    (hB : IsRealTerminalPair sX B) (hC : IsRealTerminalPair sX C) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : IsRealTerminalPair sX ((1 - t) • B + t • C) := by
  obtain ⟨⟨hX, hBc, ⟨n, K, hK, -⟩, hBcan⟩, hBterm⟩ := hB
  obtain ⟨⟨-, hCc, -, hCcan⟩, hCterm⟩ := hC
  have hb : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P < 1 := fun P => by
    by_cases h : B.coeff P = 0
    · rw [h]; exact ⟨le_rfl, one_pos⟩
    · exact ⟨(hBc P h).1.le, (hBc P h).2⟩
  have hc : ∀ P, 0 ≤ C.coeff P ∧ C.coeff P < 1 := fun P => by
    by_cases h : C.coeff P = 0
    · rw [h]; exact ⟨le_rfl, one_pos⟩
    · exact ⟨(hCc P h).1.le, (hCc P h).2⟩
  have hcoef : ∀ P, ((1 - t) • B + t • C).coeff P = (1 - t) * B.coeff P + t * C.coeff P :=
    fun P => rfl
  refine ⟨⟨hX, fun P hP => ?_, ⟨n, K, hK, ?_⟩, fun m E a hE ha => ?_⟩, fun m E a hE ha => ?_⟩
  · rw [hcoef] at hP ⊢
    obtain ⟨hb0, hb1⟩ := hb P
    obtain ⟨hc0, hc1⟩ := hc P
    have h0 : 0 ≤ (1 - t) * B.coeff P + t * C.coeff P :=
      add_nonneg (mul_nonneg (by linarith) hb0) (mul_nonneg ht0 hc0)
    refine ⟨lt_of_le_of_ne h0 (Ne.symm hP), ?_⟩
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · simpa using hc1
    · have e1 : (1 - t) * B.coeff P < (1 - t) * 1 := mul_lt_mul_of_pos_left hb1 (by linarith)
      have e2 : t * C.coeff P ≤ t * 1 := mul_le_mul_of_nonneg_left hc1.le ht0
      linarith
  · obtain ⟨m, r, L, hL, hDeq⟩ := isCartierCombination_of_isQFactorial hXQ
      (Divisor.toRDivisor K + ((1 - t) • B + t • C))
    have hDeq' : Divisor.toRDivisor K + ((1 - t) • B + t • C) =
        ∑ j, r j • Divisor.toRDivisor (L j) := by
      simpa only [toRDivisor_eq_mapCoeffs] using hDeq
    refine ⟨m, r, L, hL, fun Γ => ?_⟩
    have := congrArg (fun D : RDivisor X => D.coeff Γ) hDeq'
    simp only [MMP.Flips.coeff_sum_smul_toRDivisor] at this
    exact this
  · obtain ⟨aB, aC, hB', hC', rfl⟩ := exists_isLogDiscrepancy_of_convex hXQ ha
    have h1 := hBcan m E aB hE hB'
    have h2 := hCcan m E aC hE hC'
    have e1 : 0 ≤ (1 - t) * (aB - 1) := mul_nonneg (by linarith) (by linarith)
    have e2 : 0 ≤ t * (aC - 1) := mul_nonneg ht0 (by linarith)
    nlinarith
  · obtain ⟨aB, aC, hB', hC', rfl⟩ := exists_isLogDiscrepancy_of_convex hXQ ha
    have h1 := hBterm m E aB hE hB'
    have h2 := hCterm m E aC hE hC'
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · linarith
    · have e1 : 0 < (1 - t) * (aB - 1) := mul_pos (by linarith) (by linarith)
      have e2 : 0 ≤ t * (aC - 1) := mul_nonneg ht0 (by linarith)
      nlinarith

end Convex

/-! ### Crepancy of `D` along the program -/

section Crep

/-- An `ℝ`-Cartier pull-back is a combination of Cartier divisors. -/
private theorem isCartierCombination_of_isRCartierPullback {X W : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace X] [CompactSpace W]
    {q : W ⟶ X} {M : RDivisor X} {G : RDivisor W} (hG : IsRCartierPullback q M G) :
    IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := hG
  refine ⟨m, r, L', fun j => ?_, by simp only [toRDivisor_eq_mapCoeffs]⟩
  obtain ⟨hB, hp⟩ := hpb j
  rw [← Divisor.IsPullback.pullback_eq (hL j) hp]
  exact (hL j).isCartier_pullback q hB

/-- **Crepancy of `D` moves back along a `D`-null step.** Let `φ_g : X ⤏ X⁺` be a step over `V`
(`f : X ⟶ V`, `f⁺ : X⁺ ⟶ V`, `f⁺ ∘ φ_g = f`) extracting no divisor, `φ' = φ'' ∘ φ_g` with
`φ'' : X⁺ ⤏ Z`, and `D` an `ℝ`-Cartier divisor on `X` of degree zero on every curve contracted
by `f`, with transform `D⁺`. If `D⁺` is crepant to `L_Z` along `φ''`, then `D` is crepant to
`L_Z` along `φ'`: on a common model of `X`, `X⁺` over `V` the pull-backs of `D` and `D⁺` agree by
negativity, being numerically trivial over `X⁺` and exceptional over it. -/
private theorem isCrepantAlong_of_step {X X' V Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sX] (hXv : IsNormalVariety ℂ sX)
    (hX'Q : IsQFactorial sX') (hVv : IsNormalVariety ℂ sV) {f : X ⟶ V} {fp : X' ⟶ V}
    [IsProper f] [IsProper fp] (hfV : f ≫ sV = sX) (hfpV : fp ≫ sV = sX')
    (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    {φg : X.RationalMap X'} [φg.IsDominant] (hφb : RationalMap.IsBirational φg)
    (hover : φg.compHom fp = f.toRationalMap)
    {φ' : X.RationalMap Z} {φ'' : X'.RationalMap Z} (hcomp : φg.comp φ'' = φ')
    {D : RDivisor X} (hD : IsCartierCombination D) {D' : RDivisor X'}
    (hcorr : ∀ F : MMP.Mori.PrimeDivisor X', ∃ G,
      RationalMap.transformPrimeDivisor φg G = some F ∧ D'.coeff F = D.coeff G)
    (hnull : ∀ A : ProperCurve sX, A.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ), IsRIntersectionNumber ℂ sX D r L A x → x = 0)
    {LZ : RDivisor Z} (h' : IsCrepantAlong sX' sZ φ'' D' LZ) :
    IsCrepantAlong sX sZ φ' D LZ := by
  intro W _ _ _ sW p q h hW hWs hpX hqZ hp hq hpb hqb hinv hhq G₁ G₂ hG₁ hG₂
  have hX'v : IsNormalVariety ℂ sX' := hX'Q.1
  have : IsIntegral V := hVv.1.toIsIntegral
  have : IsNormal V := hVv.2
  have : LocallyOfFiniteType sV := hVv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : MMP.Mori.IsVariety ℂ sV := hVv.1
  have : IsSeparated sV := hVv.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sV
  have : IsSeparated sX := hXv.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sX
  have : IsSeparated sX' := hX'v.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sX'
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  have : QuasiCompact sX' := hX'v.1.toQuasiCompact
  have : QuasiCompact sW := hW.toQuasiCompact
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have : IsProper q := isProper_of_isProjectiveMorphism q hq
  have : IsDominant p := hpb.isDominant
  have : IsDominant q := hqb.isDominant
  have : IsDominant fp := hfpb.isDominant
  have hWn : IsNormalVariety ℂ ((p ≫ f) ≫ sV) := by
    rw [Category.assoc, hfV, hpX]; exact ⟨hW, inferInstance⟩
  -- a common model of `W` and `X⁺` over `V`
  obtain ⟨W', r, p', hW'v, hW'sm, hrp, hrproj, hrb, hp'proj, hp'b⟩ :=
    MMP.Fourfold.exists_common_model_over sV (p ≫ f) fp
      (Crepant.isBirationalMorphism_comp hpb hfb) hfpb hWn (by rw [hfpV]; exact hX'v)
  rw [hfpV] at hW'v hW'sm
  have : IsIntegral W' := hW'v.1.toIsIntegral
  have : IsNormal W' := hW'v.2
  have : LocallyOfFiniteType (p' ≫ sX') := hW'v.1.toLocallyOfFiniteType
  have : QuasiCompact (p' ≫ sX') := hW'v.1.toQuasiCompact
  have : IsLocallyNoetherian W' := LocallyOfFiniteType.isLocallyNoetherian (p' ≫ sX')
  have : CompactSpace W' := QuasiCompact.compactSpace_of_compactSpace (p' ≫ sX')
  have : IsProper r := isProper_of_isProjectiveMorphism r hrproj
  have : IsProper p' := isProper_of_isProjectiveMorphism p' hp'proj
  have : IsDominant r := hrb.isDominant
  have : IsDominant p' := hp'b.isDominant
  have hp''b : IsBirationalMorphism (r ≫ p) := Crepant.isBirationalMorphism_comp hrb hpb
  have hq''b : IsBirationalMorphism (r ≫ q) := Crepant.isBirationalMorphism_comp hrb hqb
  have : IsDominant (r ≫ p) := hp''b.isDominant
  have : IsDominant (r ≫ q) := hq''b.isDominant
  have hrpX : (r ≫ p) ≫ sX = p' ≫ sX' := by
    rw [← hfpV, ← Category.assoc p', ← hrp, ← hfV]; simp only [Category.assoc]
  have hrqZ : (r ≫ q) ≫ sZ = p' ≫ sX' := by
    rw [Category.assoc, hqZ, ← hpX, ← Category.assoc, hrpX]
  -- the inverses
  obtain ⟨h₁, h₂, hh₁, hh₂, hh₂q, hh₂p, hh₁q⟩ :=
    MMP.Fourfold.exists_isInverse_of_common_model hφb hcomp hinv hhq hfpb hover hp'b hrp hp''b
  -- the pull-backs to `W'`
  obtain ⟨G₁', hG₁', hc₁⟩ := Crepant.exists_isRCartierPullback_comp r p hG₁
  obtain ⟨G₂', hG₂', hc₂⟩ := Crepant.exists_isRCartierPullback_comp r q hG₂
  obtain ⟨G₃, hG₃, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p'
    (isCartierCombination_of_isQFactorial hX'Q D')
  -- `D⁺` is crepant along `φ''`
  have h32 : G₃ = G₂' := h' (p' ≫ sX') p' (r ≫ q) h₁ hW'v.1 hW'sm rfl hrqZ hp'proj
    (hrproj.comp hq) hp'b hq''b hh₁ hh₁q G₃ G₂' hG₃ hG₂'
  -- the pull-backs of `D` and `D⁺` agree
  have h13 : G₁' = G₃ := by
    have hF := isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hG₁')
      (isCartierCombination_of_isRCartierPullback hG₃)
    have htr : RationalMap.transformDivisor p'.toRationalMap (G₁' - G₃) = 0 :=
      transformDivisor_sub_eq_zero hXv hX'v (r ≫ p) p' (by rw [hrpX]; exact hW'v) hW'v hp''b
        hp'b hh₂ hh₂p hcorr hG₁' hG₃
    have h0 : ∀ Γ : ProperCurve (p' ≫ sX'), Γ.IsContractedBy p' → ∀ (m : ℕ)
        (rr : Fin m → ℝ) (L : Fin m → Divisor W') (x : ℝ),
        IsRIntersectionNumber ℂ (p' ≫ sX') (G₁' - G₃) rr L Γ x → x = 0 := by
      intro Γ hΓ m rr L x hx
      obtain ⟨m₁, r₁, L₁, hL₁, hG₁'eq⟩ := isCartierCombination_of_isRCartierPullback hG₁'
      obtain ⟨m₃, r₃, L₃, hL₃, hG₃eq⟩ := isCartierCombination_of_isRCartierPullback hG₃
      have hx₁ := isRIntersectionNumber_sum_degreeOn ℂ (p' ≫ sX') Γ r₁ L₁ hL₁
      have hx₃ := isRIntersectionNumber_sum_degreeOn ℂ (p' ≫ sX') Γ r₃ L₃ hL₃
      have hG₁'eq' : G₁' = ∑ j, r₁ j • Divisor.toRDivisor (L₁ j) := by
        simpa only [toRDivisor_eq_mapCoeffs] using hG₁'eq
      have hG₃eq' : G₃ = ∑ j, r₃ j • Divisor.toRDivisor (L₃ j) := by
        simpa only [toRDivisor_eq_mapCoeffs] using hG₃eq
      rw [← hG₁'eq'] at hx₁
      rw [← hG₃eq'] at hx₃
      have hsum := (IsRIntersectionNumber.eq_and_linear ℂ (p' ≫ sX') Γ).2 _ _ _ _ _ _ _ _ 1 (-1)
        hx₁ hx₃
      have e : (1 : ℝ) • G₁' + (-1 : ℝ) • G₃ = G₁' - G₃ := by
        rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
      rw [e] at hsum
      rw [(IsRIntersectionNumber.eq_and_linear ℂ (p' ≫ sX') Γ).1 _ _ _ _ _ _ _ hx hsum,
        eq_zero_of_isRCartierPullback_of_isContractedBy p' rfl hG₃ Γ hΓ hx₃]
      -- the pull-back of `D` vanishes on `Γ`
      by_cases hc : IsProperCurve sX ((r ≫ p) Γ.point)
      · set A : ProperCurve sX := ⟨_, hc⟩
        have hA : A.IsContractedBy f := by
          intro z hz
          change z ∈ closure {(r ≫ p) Γ.point} at hz
          have hsub : closure ({(r ≫ p) Γ.point} : Set X) ⊆
              (r ≫ p) '' closure ({Γ.point} : Set W') :=
            closure_minimal (Set.singleton_subset_iff.2 ⟨Γ.point, subset_closure rfl, rfl⟩)
              ((r ≫ p).isClosedMap _ isClosed_closure)
          obtain ⟨w, hw, rfl⟩ := hsub hz
          change f ((r ≫ p) w) = f ((r ≫ p) Γ.point)
          rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, hrp,
            Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓ w hw]
        obtain ⟨mD, rD, LD, hLD, hDeq⟩ := hD
        have hy := isRIntersectionNumber_sum_degreeOn ℂ sX A rD LD hLD
        have hDeq' : D = ∑ j, rD j • Divisor.toRDivisor (LD j) := by
          simpa only [toRDivisor_eq_mapCoeffs] using hDeq
        rw [← hDeq'] at hy
        rw [eq_mul_of_isRCartierPullback (r ≫ p) hrpX hG₁' Γ A rfl hx₁ hy,
          hnull A hA _ _ _ _ hy]
        ring
      · rw [eq_zero_of_isRCartierPullback_of_not_isProperCurve (r ≫ p) hrpX hG₁' Γ hc hx₁]
        ring
    exact sub_eq_zero.mp (eq_zero_of_forall_eq_zero_of_transformDivisor_eq_zero hX'v hW'v p' rfl
      hp'proj hp'b hF htr h0)
  -- descend to `W`
  have hWn' : IsNormalVariety ℂ (p ≫ sX) := by rw [hpX]; exact ⟨hW, inferInstance⟩
  have hW'n : IsNormalVariety ℂ (r ≫ p ≫ sX) := by
    rw [← Category.assoc, hrpX]; exact hW'v
  refine Finsupp.ext fun P => ?_
  obtain ⟨P', hP', hP'iso, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hWn' hW'n hrb P
  have e1 := hc₁ P' P hP' hP'iso
  have e2 := hc₂ P' P hP' hP'iso
  change G₁.coeff P = G₂.coeff P
  rw [← e1, ← e2, h13, h32]

end Crep

/-! ### The program: invariants and steps -/

section ProgramSteps

/-- Every morphism to a variety is small when it is an isomorphism. -/
private theorem isSmall_of_isIso {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (f : Y ⟶ X) [IsIso f]
    (hX : MMP.Mori.IsVariety ℂ sX) (hY : MMP.Mori.IsVariety ℂ sY) (hf : f ≫ sX = sY) :
    IsSmall ℂ sX sY f := by
  subst hf
  exact {
    isVariety_target := hX
    isVariety_source := hY
    comp_eq := rfl
    isProper := inferInstance
    isIso_app _ := inferInstance
    dim_eq := IsHomeomorph.topologicalKrullDim_eq _ f.homeomorph.isHomeomorph
    exists_isIso := ⟨⊥, ⊥, le_closedsCodimension_iff_le_coheight.mpr (by simp),
      le_closedsCodimension_iff_le_coheight.mpr (by simp), fun _ _ h => h, by
        have h : (⊥ : TopologicalSpace.Closeds Y).compl =
            f ⁻¹ᵁ (⊥ : TopologicalSpace.Closeds X).compl := by ext; simp
        refine (Scheme.Hom.resLE_congr f _ rfl h (MorphismProperty.isomorphisms _)).mpr ?_
        rw [Scheme.Hom.resLE_eq_morphismRestrict]
        exact inferInstanceAs (IsIso _)⟩ }

/-- Every Cartier divisor is ample relative to an isomorphism: the preimage of an affine open is
affine, and every invertible sheaf on an affine scheme is ample. -/
private theorem isRelativelyAmpleCartier_of_isIso' {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {L : Divisor X}
    (hL : L.IsCartier) : IsRelativelyAmpleCartier e L := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  refine ⟨hL, fun V hV => ?_⟩
  haveI : IsAffine (e ⁻¹ᵁ V) := hV.preimage e
  have hinv : Stacks.Ample.IsInvertibleModule (e ⁻¹ᵁ V).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (e ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- Every `ℝ`-Cartier divisor is ample relative to an isomorphism: in a presentation
`D = ∑ cⱼ Lⱼ`, `cⱼ Lⱼ = (|cⱼ| + 1) Lⱼ + (|cⱼ| + 1 - cⱼ)(-Lⱼ)` is a positive combination of
Cartier divisors, all ample over the isomorphism, and the summand `1 • 0` makes the presentation
nonempty. -/
private theorem isRelativelyAmple_of_isIso' {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {D : RDivisor X}
    (hD : IsCartierCombination D) : IsRelativelyAmple e D := by
  obtain ⟨m, c, L, hL, rfl⟩ := hD
  refine ⟨m + m + 1, Fin.cons 1 (Fin.append (fun j => |c j| + 1) (fun j => |c j| + 1 - c j)),
    Fin.cons 0 (Fin.append L fun j => -L j), by omega, fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.cases one_pos (fun i => Fin.addCases (fun i => ?_) (fun i => ?_) i) j <;>
      simp only [Fin.cons_succ, Fin.append_left, Fin.append_right]
    · positivity
    · linarith [le_abs_self (c i)]
  · refine Fin.cases (isRelativelyAmpleCartier_of_isIso' e Divisor.isCartier_zero)
      (fun i => Fin.addCases (fun i => ?_) (fun i => ?_) i) j <;>
      simp only [Fin.cons_succ, Fin.append_left, Fin.append_right]
    · exact isRelativelyAmpleCartier_of_isIso' e (hL i)
    · exact isRelativelyAmpleCartier_of_isIso' e (hL i).neg
  · rw [Fin.sum_univ_succ, Fin.sum_univ_add, ← Finset.sum_add_distrib]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.append_left, Fin.append_right, map_zero,
      smul_zero, zero_add, map_neg, smul_neg, ← sub_eq_add_neg, ← sub_smul, add_sub_cancel_left,
      sub_sub_cancel]
    rfl

/-- A proper dominant morphism is surjective. -/
private theorem surjective_of_isProper_of_isDominant {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsProper f] [IsDominant f] : Surjective f := by
  have huniv : Set.range f = Set.univ := by
    rw [← f.isClosedMap.isClosed_range.closure_eq, f.denseRange.closure_range]
  exact ⟨Set.range_eq_univ.mp huniv⟩

/-- The null condition of the null-rays lemma, as intersection numbers. -/
private theorem forall_eq_zero_of_degree_eq_zero {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [CompactSpace X] {D : RDivisor X}
    (A : ProperCurve sX)
    (h : ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
      D = ∑ j, c j • Divisor.toRDivisor (L j) →
      ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
        NumericalCurveClasses.degree sX (L j).divisorialSheaf
          (OneCycle.numericalClass sX (A.cycle ℝ))) = 0)
    (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ)
    (hx : IsRIntersectionNumber ℂ sX D r L A x) : x = 0 := by
  obtain ⟨hL, d, hDeq, hd, hxeq⟩ := hx
  have h1 := h m r L hL hDeq
  have hcan := isRIntersectionNumber_sum_degreeOn ℂ sX A r L hL
  rw [← hDeq] at hcan
  rw [(IsRIntersectionNumber.eq_and_linear ℂ sX A).1 _ _ _ _ _ _ _ ⟨hL, d, hDeq, hd, hxeq⟩ hcan,
    ← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  haveI := (hL j).isInvertibleModule_divisorialSheaf
  exact congrArg (r j * ·) (OneCycle.degree_cycle ℝ (L j).divisorialSheaf A).symm

/-- **The data carried along the program.** On a model `X` of the program over `S` with canonical
divisor `K_X` and boundary `C_X`: a canonical divisor `K'` linearly equivalent to `K_X` and
boundaries `B'`, `C'` with `C_X = (1 - t) B' + t C'`; the given `Z` is a nef weak model of
`(X, C_X)`, with transforms those of `K`, `B`, `C`; rational null data for `B'` with the original
weights and index; `K' + B'` nef over `S`; `C'` effective klt; and crepancy of `K' + B'` along the
weak model gives that of `K + B`. -/
private def ProgInv {Y S Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] (sY : Y ⟶ Spec (.of ℂ))
    (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) [QuasiCompact sZ] (πZ : Z ⟶ S)
    (K : Divisor Y) (B C : RDivisor Y) (φ : Y.RationalMap Z) (t : ℝ) (s₀ : ℕ)
    (w₀ : Fin s₀ → ℝ) (m₀ : ℕ) {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (πX : X ⟶ S)
    (KX : Divisor X) (CX : RDivisor X) : Prop :=
  ∃ (K' : Divisor X) (B' C' : RDivisor X) (φ' : X.RationalMap Z),
    IsNefWeakModel sX sZ sS πX πZ K' CX φ' ∧ K'.IsCanonicalDivisor sX 3 ∧
    K'.LinearlyEquivalent KX ∧ CX = (1 - t) • B' + t • C' ∧
    RationalMap.transformDivisor φ' K' = RationalMap.transformDivisor φ K ∧
    RationalMap.transformDivisor φ' B' = RationalMap.transformDivisor φ B ∧
    RationalMap.transformDivisor φ' C' = RationalMap.transformDivisor φ C ∧
    (∃ (ν' : RationalNullData sX K' B') (hs : ν'.s = s₀), ν'.m = m₀ ∧
      ∀ i, ν'.weight i = w₀ (Fin.cast hs i)) ∧
    IsRelativelyNef ℂ sX πX (logCanonicalDivisor K' B') ∧
    (∀ P, 0 ≤ C'.coeff P) ∧ IsRealKltPair sX C' ∧
    (IsCrepantAlong sX sZ φ' (logCanonicalDivisor K' B')
        (logCanonicalDivisor (RationalMap.transformDivisor φ K)
          (RationalMap.transformDivisor φ B)) →
      IsCrepantAlong sY sZ φ (logCanonicalDivisor K B)
        (logCanonicalDivisor (RationalMap.transformDivisor φ K)
          (RationalMap.transformDivisor φ B)))

/-- The dimension of the target of a step is that of its source. -/
private theorem topologicalKrullDim_eq_of_step {X X' V : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hXv : IsNormalVariety ℂ sX)
    (hX'v : IsNormalVariety ℂ sX') (hVv : IsNormalVariety ℂ sV) {f : X ⟶ V} {fp : X' ⟶ V}
    (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp) (hf : f ≫ sV = sX)
    (hfp : fp ≫ sV = sX') : topologicalKrullDim X' = topologicalKrullDim X := by
  haveI : MMP.Mori.IsVariety ℂ sV := hVv.1
  haveI : MMP.Mori.IsVariety ℂ sX := hXv.1
  haveI : MMP.Mori.IsVariety ℂ sX' := hX'v.1
  subst hf hfp
  rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV (fp ≫ sV) hfpb,
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV (f ≫ sV) hfb]

/-- A canonical divisor of a threefold is a canonical divisor of index three. -/
private theorem isCanonicalDivisor_three {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} (hd : topologicalKrullDim X = 3)
    (hK : ∃ m : ℕ, Divisor.IsCanonicalDivisor sX m K) : Divisor.IsCanonicalDivisor sX 3 K := by
  obtain ⟨m, hm⟩ := hK
  have h := hm.topologicalKrullDim_eq
  rw [hd] at h
  have hm3 : m = 3 := by exact_mod_cast h.symm
  rwa [hm3] at hm

/-- **One step of the program.** Along a step of the `(K + C_t)`-program, the invariants pass to
the next model: the weak model survives the step, the step is `D`-null, so that `D` stays nef with
its null data, and crepancy of `D` on the next model gives crepancy on the previous one. -/
private theorem progInv_step (εN : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ) (hN : NullSpec εN)
    {Y S Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sY : Y ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ] {πZ : Z ⟶ S}
    {K : Divisor Y} {B C : RDivisor Y} {φ : Y.RationalMap Z} {t : ℝ} {s₀ : ℕ}
    {w₀ : Fin s₀ → ℝ} {m₀ : ℕ} (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hZQ : IsQFactorial sZ)
    (ht0 : 0 < t) (htε : t < εN s₀ w₀ m₀)
    {X X' V : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    {πX : X ⟶ S} {πX' : X' ⟶ S} {KX : Divisor X} {CX : RDivisor X} {KX' : Divisor X'}
    {CX' : RDivisor X'} {R : Set (RelativeNumericalCurveClasses sX πX)} {f : X ⟶ V}
    {g : V ⟶ S} {fp : X' ⟶ V}
    (hXm : Kit.IsProgramModel sS sX πX) (hX'm : Kit.IsProgramModel sS sX' πX')
    (hKX : ∃ m : ℕ, KX.IsCanonicalDivisor sX m)
    (hs : Kit.IsProgramStep sX sX' sV πX πX' KX CX KX' CX' R f g fp)
    (hI : ProgInv sY sS sZ πZ K B C φ t s₀ w₀ m₀ sX πX KX CX) :
    ProgInv sY sS sZ πZ K B C φ t s₀ w₀ m₀ sX' πX' KX' CX' := by
  obtain ⟨K', B', C', φ', hwm, hK'3, hKK, hCX, hTK, hTB, hTC, ⟨ν', hs₀, hm₀, hw₀⟩, hDnef,
    hC'0, hC'klt, hRel⟩ := hI
  have hXv : IsNormalVariety ℂ sX := hXm.2.1.1
  have hX'v : IsNormalVariety ℂ sX' := hX'm.2.1.1
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
  haveI : IsSeparated sS := ((MMP.Mori.isProjectiveVariety_iff ℂ sS).mp hS).1.toIsSeparated
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sX
  -- the step map
  obtain ⟨φg, hφb, hover, hTR, hTRd, hfmt, hcorr⟩ :=
    hs.exists_stepMap hS hXm hX'm hKX ⟨3, hK'3⟩
  haveI : φg.IsDominant := Crepant.isDominant_of_isBirational hφb
  have hneg := hs.2.2.2.1
  have hVv := hneg.isNormalVariety_target
  haveI : IsIntegral V := hVv.1.toIsIntegral
  haveI : IsNormal V := hVv.2
  haveI : LocallyOfFiniteType sV := hVv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : QuasiCompact sV := hVv.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : IsSeparated sV := hVv.1.toIsSeparated
  haveI : IsProper f := hneg.isContraction.isProper
  have hfb : IsBirationalMorphism f := by
    rcases hs.2.2.2.2.2 with ⟨⟨hbir, -⟩, -⟩ | hfl
    · exact hbir
    · exact hfl.isBirationalMorphism
  have hfpb : IsBirationalMorphism fp := by
    rcases hs.2.2.2.2.2 with ⟨-, hiso, -⟩ | hfl
    · haveI := hiso; exact isBirationalMorphism_of_isIso fp
    · exact hfl.isBirationalMorphism_flip
  have hfpV : fp ≫ sV = sX' := hs.comp_eq_flip hXm hX'm
  have hfpproj : IsProjectiveMorphism fp :=
    IsProjectiveMorphism.of_comp fp sV (by rw [hfpV]; exact hX'm.1.isProjective)
  haveI : IsProper fp := isProper_of_isProjectiveMorphism fp hfpproj
  have hfproj : IsProjectiveMorphism f :=
    IsProjectiveMorphism.of_comp f sV (by rw [hneg.isContraction.comp_eq]; exact hXm.1.isProjective)
  -- the next weak model
  have hinvg := MMP.Mori.RationalMap.IsBirational.isInverse_inverse hφb
  haveI : (MMP.Mori.RationalMap.IsBirational.inverse hφb).IsDominant :=
    Crepant.isDominant_of_isBirational (MMP.Mori.RationalMap.IsBirational.isBirational_inverse hφb)
  set φ'' : X'.RationalMap Z := (MMP.Mori.RationalMap.IsBirational.inverse hφb).comp φ'
    with hφ''def
  have hcomp : φg.comp φ'' = φ' := by
    rw [hφ''def, ← Scheme.RationalMap.comp_assoc,
      Crepant.comp_eq_comp_of_eq (Crepant.comp_eq_id_of_isInverse hinvg) φ',
      Scheme.RationalMap.id_comp]
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, -, hp₀X, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀, hhq₀,
    GY₀, GZ₀, hGY₀, hGZ₀, hA₀, hA₀q⟩ := hwm.exists_resolution
  obtain ⟨hsurv, -⟩ := hwm.isNefWeakModel_of_negativeStep hXm.2.1 hZQ
  obtain ⟨-, hnex⟩ := hsurv sX' πX' φg φ'' hX'm.1 hX'm.2.1 hX'm.2.2 hfmt hcomp
  have hu1 : ∀ D : MMP.Mori.PrimeDivisor X', Order.coheight (fp D.genericPoint) ≤ 1 := by
    rcases hs.2.2.2.2.2 with ⟨-, hiso, -⟩ | hfl
    · haveI := hiso
      intro D
      rw [Topology.IsOpenEmbedding.coheight_eq _ fp.isOpenEmbedding,
        AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    · exact fun D => (Kit.coheight_map_genericPoint_of_isSmall hfl.isSmall_flip D).1.le
  have : IsSeparated sW₀ := hW₀.toIsSeparated
  obtain ⟨hwm', hTT, hgF, -⟩ := hwm.isNefWeakModel_of_step_over hW₀ hp₀X hq₀Z hp₀ hq₀ hp₀b
    hq₀b hinv₀ hhq₀ hGY₀ hGZ₀ hA₀ hA₀q hX'm.1 hX'm.2.1 hX'm.2.2 hcomp hφb hVv f fp hfb hfpb
    hneg.isContraction.comp_eq hfpV hs.2.2.1.comp_eq hs.2.2.2.2.1 hover hu1
    (fun G P₀ hP₀ h0 => hnex sW₀ p₀ q₀ h₀ hW₀ hp₀X hq₀Z hp₀ hq₀ hp₀b hq₀b hinv₀ hhq₀ hGY₀ hGZ₀ G
      P₀ ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff p₀ P₀ G).mpr hP₀) h0)
  -- the new divisors
  have hCX' : CX' = flipTransform f fp CX := by
    rcases hs.2.2.2.2.2 with ⟨-, -, -, hC'⟩ | hfl
    · exact hC'
    · exact hfl.eq_flipTransform
  have hCX'' : CX' = (1 - t) • flipTransform f fp B' + t • flipTransform f fp C' := by
    rw [hCX', hCX, ← hgF, map_add, transformDivisor_smul', transformDivisor_smul', hgF, hgF]
  have hwm'' : IsNefWeakModel sX' sZ sS πX' πZ (flipTransform f fp K') CX' φ'' := by
    have h := hwm'
    rw [hgF, hgF] at h
    rwa [← hCX'] at h
  have hd : topologicalKrullDim X = 3 := hK'3.topologicalKrullDim_eq
  have hd' : topologicalKrullDim X' = 3 := by
    rw [topologicalKrullDim_eq_of_step hXv hX'v hVv hfb hfpb hneg.isContraction.comp_eq hfpV, hd]
  have hK''3 : Divisor.IsCanonicalDivisor sX' 3 (flipTransform f fp K') :=
    isCanonicalDivisor_three hd' hwm''.isCanonicalDivisor
  have hKK' : Divisor.LinearlyEquivalent (flipTransform f fp K') KX' :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'v hK''3
      (isCanonicalDivisor_three hd' hs.isCanonicalDivisor_next)
  -- the null-rays lemma at this step
  have hneg' : IsNegativeExtremalContraction ℂ sX sV
      (logCanonicalDivisor K' ((1 - t) • B' + t • C')) f := by
    rw [← hCX]; exact Kit.isNegativeExtremalContraction_of_linearlyEquivalent hXm.2.1 hfproj hneg hKK
  have hsmall : IsSmall ℂ sV sX' fp := by
    rcases hs.2.2.2.2.2 with ⟨-, hiso, -⟩ | hfl
    · haveI := hiso; exact isSmall_of_isIso fp hVv.1 hX'v.1 hfpV
    · exact hfl.isSmall_flip
  have hamp : IsRelativelyAmple fp (logCanonicalDivisor (flipTransform f fp K')
      (flipTransform f fp ((1 - t) • B' + t • C'))) := by
    rw [← hCX, ← hCX']
    rcases hs.2.2.2.2.2 with ⟨-, hiso, -⟩ | hfl
    · haveI := hiso
      exact isRelativelyAmple_of_isIso' fp (isCartierCombination_of_isQFactorial hX'm.2.1 _)
    · obtain ⟨ψ, hψ⟩ := hKK'
      have hK2 : flipTransform f fp K' = KX' + principalDivisor ψ := by rw [← hψ]; abel
      have heq : logCanonicalDivisor (flipTransform f fp K') CX' = logCanonicalDivisor KX' CX' +
          (1 : ℝ) • Divisor.toRDivisor (principalDivisor ψ) := by
        rw [logCanonicalDivisor, logCanonicalDivisor, hK2, map_add, one_smul]; abel
      rw [heq]
      exact Kit.isRelativelyAmple_of_isNumericallyEquivalentOver hX'v hVv
        hfl.isProjectiveMorphism_flip hfl.isSmall_flip.comp_eq
        (Kit.isNumericallyEquivalentOver_add_smul
          (Kit.isCartierCombination_of_isRelativelyAmple hfl.isRelativelyAmple_flip)
          (Kit.isNumericallyTrivialOver_principalDivisor fp ψ) 1) hfl.isRelativelyAmple_flip
  have htε' : t < εN ν'.s ν'.weight ν'.m := by
    rwa [apply_eq_of_weight_eq εN hs₀ hm₀ hw₀]
  obtain ⟨-, hstep⟩ := hN sX sS πX hS hXm.2.2 hK'3 ν' hC'0 hC'klt hDnef t ht0 htε'
  obtain ⟨hnull, hDnef', ⟨ν'', hs', hm', hw'⟩, hC''0, hC''klt⟩ :=
    hstep sV sX' f g fp hs.2.2.1.comp_eq (hs.comp_eq_base hXm) hneg' hfb hfproj
      (hs.isProjectiveVariety_target hS hXm) hX'm.2.1 hX'm.1 hK''3 hsmall hfpproj hamp
  -- the reduction of the crepancy
  have hlog : logCanonicalDivisor (flipTransform f fp K') (flipTransform f fp B') =
      flipTransform f fp (logCanonicalDivisor K' B') := by
    rw [← hgF, ← hgF, ← hgF, transformDivisor_logCanonicalDivisor]
  refine ⟨flipTransform f fp K', flipTransform f fp B', flipTransform f fp C', φ'', hwm'', hK''3,
    hKK', hCX'', by rw [← hgF, hTT, hTK], by rw [← hgF, hTT, hTB], by rw [← hgF, hTT, hTC],
    ⟨ν'', hs'.trans hs₀, hm'.trans hm₀, fun i => by rw [(hw' i).1, hw₀]; rfl⟩,
    by rw [← hs.2.2.2.2.1]; exact hDnef', hC''0, hC''klt, fun hcrep => hRel ?_⟩
  refine isCrepantAlong_of_step hXv hX'm.2.1 hVv hneg.isContraction.comp_eq hfpV hfb hfpb hφb
    hover hcomp (isCartierCombination_of_isQFactorial hXm.2.1 _) (fun F => ?_)
    (fun A hA => forall_eq_zero_of_degree_eq_zero A (hnull A hA)) hcrep
  obtain ⟨P, hP, hval⟩ := hcorr F
  exact ⟨P, hP, by rw [hlog]; exact hval _⟩

end ProgramSteps

/-! ### The end of the program -/

section ProgramEnd

/-- **The end of the program.** On the last model `X` of the program, where `K_X + C_X` is nef,
the radial nef interval makes every `K' + C'_s` nef with one set of zero curves; `X` and `Z` are
two nef weak models of `(X, C_X)`, so their `C_X`-adjoints are crepant; `K' + B'` is null on the
curves `Z` contracts and descends crepantly to `Z`; and every `K_Z + φ_* C_s` is nef, its pull-back
being that of `K' + C'_s`. -/
private theorem crep_and_nef_of_progInv (τn : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ) (hnef : NefSpec τn)
    {Y S Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sY : Y ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [QuasiCompact sZ] {πZ : Z ⟶ S}
    {K : Divisor Y} {B C : RDivisor Y} {φ : Y.RationalMap Z} {t e : ℝ} {s₀ : ℕ}
    {w₀ : Fin s₀ → ℝ} {m₀ : ℕ} (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hZQ : IsQFactorial sZ)
    (ht0 : 0 < t) (hte : t < e) (he : e ≤ τn s₀ w₀ m₀ / (2 * (τn s₀ w₀ m₀ + 6)))
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {πX : X ⟶ S} {KX : Divisor X} {CX : RDivisor X}
    (hXm : Kit.IsProgramModel sS sX πX)
    (hnefX : IsRelativelyNef ℂ sX πX (logCanonicalDivisor KX CX))
    (hI : ProgInv sY sS sZ πZ K B C φ t s₀ w₀ m₀ sX πX KX CX) :
    IsCrepantAlong sY sZ φ (logCanonicalDivisor K B)
        (logCanonicalDivisor (RationalMap.transformDivisor φ K)
          (RationalMap.transformDivisor φ B)) ∧
      ∀ s : ℝ, 0 < s → s < e → IsRelativelyNef ℂ sZ πZ
        (logCanonicalDivisor (RationalMap.transformDivisor φ K)
          (RationalMap.transformDivisor φ ((1 - s) • B + s • C))) := by
  obtain ⟨K', B', C', φ', hwm, hK'3, hKK, hCX, hTK, hTB, hTC, ⟨ν', hs₀, hm₀, hw₀⟩, hDnef,
    hC'0, hC'klt, hRel⟩ := hI
  have hXv : IsNormalVariety ℂ sX := hXm.2.1.1
  have hZv := hwm.isNormalVariety_target
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : IsSeparated sZ := hZv.1.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  have := MMP.Fourfold.isSeparated_terminal sX
  have := MMP.Fourfold.isSeparated_terminal sZ
  haveI : IsSeparated sS := ((MMP.Mori.isProjectiveVariety_iff ℂ sS).mp hS).1.toIsSeparated
  have := MMP.Fourfold.isSeparated_terminal sS
  haveI : φ'.IsDominant := Crepant.isDominant_of_isBirational hwm.isBirational
  have ht : t ≠ 0 := ht0.ne'
  set LZ := logCanonicalDivisor (RationalMap.transformDivisor φ K)
    (RationalMap.transformDivisor φ B) with hLZ
  have hLZ' : LZ = RationalMap.transformDivisor φ' (logCanonicalDivisor K' B') := by
    rw [hLZ, transformDivisor_logCanonicalDivisor, hTK, hTB]
  -- the radial nef interval on `X`
  have hnefX' : IsRelativelyNef ℂ sX πX (logCanonicalDivisor K' CX) :=
    Kit.isRelativelyNef_logCanonicalDivisor_of_linearlyEquivalent hKK hnefX
  have hτeq : τn ν'.s ν'.weight ν'.m = τn s₀ w₀ m₀ := apply_eq_of_weight_eq τn hs₀ hm₀ hw₀
  have hπproj : IsProjectiveMorphism πX :=
    IsProjectiveMorphism.of_comp πX sS (by rw [hXm.2.2]; exact hXm.1.isProjective)
  obtain ⟨hnefs, hzero⟩ := hnef sX sS πX hπproj hS hXm.2.2 hK'3 ν' hC'0 hC'klt hDnef t ht0
    (by rw [hτeq]; linarith) (by rw [← hCX]; exact hnefX')
  have hε0 : 0 < τn s₀ w₀ m₀ / (2 * (τn s₀ w₀ m₀ + 6)) := lt_of_lt_of_le (ht0.trans hte) he
  -- `X` and `Z` are two nef weak models of `(X, C_X)`
  have hid : IsNefWeakModel sX sX sS πX πX K' CX (𝟙 X : X ⟶ X).toRationalMap :=
    isNefWeakModel_id (K := K') (C := CX) hXm.1 hXm.2.1 hXm.2.2 ⟨3, hK'3⟩ hnefX'
  obtain ⟨h2wm, -⟩ := IsNefWeakModel.eq_of_isRCartierPullback_and_isNefModelEquivalent hid hwm
  -- `K' + B'` is null on the curves along which `K' + C_X` is null
  have hnullD : ∀ A : ProperCurve sX, A.IsContractedBy πX → ∀ {m : ℕ} {r : Fin m → ℝ}
      {L : Fin m → Divisor X} {x : ℝ},
      IsRIntersectionNumber ℂ sX (logCanonicalDivisor K' CX) r L A x → x = 0 →
      ∀ {m' : ℕ} {r' : Fin m' → ℝ} {L' : Fin m' → Divisor X} {y : ℝ},
        IsRIntersectionNumber ℂ sX (logCanonicalDivisor K' B') r' L' A y → y = 0 := by
    intro A hA m r L x hx hx0 m' r' L' y hy
    obtain ⟨mC, rC, LC, hLC, hCeq⟩ :=
      isCartierCombination_of_isQFactorial hXm.2.1 (logCanonicalDivisor K' C')
    have hCeq' : logCanonicalDivisor K' C' = ∑ j, rC j • Divisor.toRDivisor (LC j) := by
      simpa only [toRDivisor_eq_mapCoeffs] using hCeq
    have hyC := isRIntersectionNumber_sum_degreeOn ℂ sX A rC LC hLC
    rw [← hCeq'] at hyC
    have hσ : ∀ σ : ℝ, IsRIntersectionNumber ℂ sX
        (logCanonicalDivisor K' ((1 - σ) • B' + σ • C')) (Fin.append ((1 - σ) • r') (σ • rC))
        (Fin.append L' LC) A
        ((1 - σ) * y + σ * ∑ j, rC j * ((LC j).degreeOn ℂ sX A.ι A.dim_le (hLC j) : ℝ)) := by
      intro σ
      rw [logCanonicalDivisor_affine]
      exact (IsRIntersectionNumber.eq_and_linear ℂ sX A).2 _ _ _ _ _ _ _ _ (1 - σ) σ hy hyC
    have hxt : (1 - t) * y + t * ∑ j, rC j * ((LC j).degreeOn ℂ sX A.ι A.dim_le (hLC j) : ℝ)
        = 0 := by
      rw [hCX] at hx
      rw [← (IsRIntersectionNumber.eq_and_linear ℂ sX A).1 _ _ _ _ _ _ _ hx (hσ t)]
      exact hx0
    have ht2 : t / 2 < τn ν'.s ν'.weight ν'.m / (2 * (τn ν'.s ν'.weight ν'.m + 6)) := by
      rw [hτeq]; linarith
    have ht1 : t < τn ν'.s ν'.weight ν'.m / (2 * (τn ν'.s ν'.weight ν'.m + 6)) := by
      rw [hτeq]; linarith
    have hx2 := (hzero t (t / 2) ht0 ht1 (by linarith) ht2 A hA _ _ _ _ _ _ _ _ (hσ t)
      (hσ (t / 2))).1 hxt
    linarith
  -- crepancy of `K' + B'` along `φ'`
  have hcrepX : IsCrepantAlong sX sZ φ' (logCanonicalDivisor K' B') LZ := by
    intro W _ _ _ sW p q h hW hWs hpX hqZ hp hq hpb hqb hinv hhq G₁ G₂ hG₁ hG₂
    have : QuasiCompact sW := hW.toQuasiCompact
    have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
    have : IsProper p := isProper_of_isProjectiveMorphism p hp
    have : IsProper q := isProper_of_isProjectiveMorphism q hq
    have : IsDominant p := hpb.isDominant
    have : IsDominant q := hqb.isDominant
    have hWn : IsNormalVariety ℂ sW := ⟨hW, inferInstance⟩
    have hpX' : IsNormalVariety ℂ (p ≫ sX) := by rw [hpX]; exact hWn
    have hqZ' : IsNormalVariety ℂ (q ≫ sZ) := by rw [hqZ]; exact hWn
    have hpq : p ≫ πX = q ≫ πZ := comp_eq_comp_of_isOver πX πZ hwm.isOver p q h hinv hhq
    -- the pull-backs of the `C_X`-adjoints agree
    obtain ⟨E₁, hE₁, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p
      (isCartierCombination_of_isQFactorial hXm.2.1 (logCanonicalDivisor K' CX))
    obtain ⟨E₂, hE₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q
      (Crepant.isCartierCombination_logCanonicalDivisor hwm)
    have hE : E₁ = E₂ := by
      refine h2wm sW p q h hW hpX hqZ hp hq hpb hqb (Crepant.compHom_eq_of_isInverse hinv) hhq
        ?_ hE₂
      rw [transformDivisor_id, transformDivisor_id]; exact hE₁
    -- `G₁ - G₂` is numerically trivial over `Z`
    have h0 : ∀ Γ : ProperCurve sW, Γ.IsContractedBy q → ∀ (m : ℕ) (rr : Fin m → ℝ)
        (L : Fin m → Divisor W) (x : ℝ),
        IsRIntersectionNumber ℂ sW (G₁ - G₂) rr L Γ x → x = 0 := by
      intro Γ hΓ m rr L x hx
      obtain ⟨m₁, r₁, L₁, hL₁, h1eq⟩ := isCartierCombination_of_isRCartierPullback hG₁
      obtain ⟨m₂, r₂, L₂, hL₂, h2eq⟩ := isCartierCombination_of_isRCartierPullback hG₂
      obtain ⟨mE, rE, LE, hLE, hEeq⟩ := isCartierCombination_of_isRCartierPullback hE₁
      have h1eq' : G₁ = ∑ j, r₁ j • Divisor.toRDivisor (L₁ j) := by
        simpa only [toRDivisor_eq_mapCoeffs] using h1eq
      have h2eq' : G₂ = ∑ j, r₂ j • Divisor.toRDivisor (L₂ j) := by
        simpa only [toRDivisor_eq_mapCoeffs] using h2eq
      have hEeq' : E₁ = ∑ j, rE j • Divisor.toRDivisor (LE j) := by
        simpa only [toRDivisor_eq_mapCoeffs] using hEeq
      have hx₁ := isRIntersectionNumber_sum_degreeOn ℂ sW Γ r₁ L₁ hL₁
      have hx₂ := isRIntersectionNumber_sum_degreeOn ℂ sW Γ r₂ L₂ hL₂
      have hxE := isRIntersectionNumber_sum_degreeOn ℂ sW Γ rE LE hLE
      rw [← h1eq'] at hx₁
      rw [← h2eq'] at hx₂
      rw [← hEeq'] at hxE
      have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sW Γ).2 _ _ _ _ _ _ _ _ 1 (-1) hx₁ hx₂
      have e : (1 : ℝ) • G₁ + (-1 : ℝ) • G₂ = G₁ - G₂ := by
        rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
      rw [e] at hsum
      rw [(IsRIntersectionNumber.eq_and_linear ℂ sW Γ).1 _ _ _ _ _ _ _ hx hsum,
        eq_zero_of_isRCartierPullback_of_isContractedBy q hqZ hG₂ Γ hΓ hx₂]
      have hE0 := eq_zero_of_isRCartierPullback_of_isContractedBy q hqZ hE₂ Γ hΓ (hE ▸ hxE)
      have hG₁0 : ∑ j, r₁ j * ((L₁ j).degreeOn ℂ sW Γ.ι Γ.dim_le (hL₁ j) : ℝ) = 0 := by
        by_cases hc : IsProperCurve sX (p Γ.point)
        · set A : ProperCurve sX := ⟨_, hc⟩
          have hA : A.IsContractedBy πX := by
            intro z hz
            change z ∈ closure {p Γ.point} at hz
            have hsub : closure ({p Γ.point} : Set X) ⊆ p '' closure ({Γ.point} : Set W) :=
              closure_minimal (Set.singleton_subset_iff.2 ⟨Γ.point, subset_closure rfl, rfl⟩)
                (p.isClosedMap _ isClosed_closure)
            obtain ⟨w, hw, rfl⟩ := hsub hz
            change πX (p w) = πX (p Γ.point)
            rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpq, Scheme.Hom.comp_apply,
              Scheme.Hom.comp_apply, hΓ w hw]
          obtain ⟨mC, rC, LC, hLC, hCeq⟩ :=
            isCartierCombination_of_isQFactorial hXm.2.1 (logCanonicalDivisor K' CX)
          obtain ⟨mD, rD, LD, hLD, hDeq⟩ :=
            isCartierCombination_of_isQFactorial hXm.2.1 (logCanonicalDivisor K' B')
          have hCeq' : logCanonicalDivisor K' CX = ∑ j, rC j • Divisor.toRDivisor (LC j) := by
            simpa only [toRDivisor_eq_mapCoeffs] using hCeq
          have hDeq' : logCanonicalDivisor K' B' = ∑ j, rD j • Divisor.toRDivisor (LD j) := by
            simpa only [toRDivisor_eq_mapCoeffs] using hDeq
          have hyC := isRIntersectionNumber_sum_degreeOn ℂ sX A rC LC hLC
          have hyD := isRIntersectionNumber_sum_degreeOn ℂ sX A rD LD hLD
          rw [← hCeq'] at hyC
          rw [← hDeq'] at hyD
          have e1 := eq_mul_of_isRCartierPullback p hpX hE₁ Γ A rfl hxE hyC
          have e2 := eq_mul_of_isRCartierPullback p hpX hG₁ Γ A rfl hx₁ hyD
          rw [e2]
          rcases eq_or_ne (residueFieldDegree p Γ.point : ℝ) 0 with hd | hd
          · rw [hd, zero_mul]
          · have hyC0 := (mul_eq_zero.mp (hE0 ▸ e1).symm).resolve_left hd
            rw [hnullD A hA hyC hyC0 hyD, mul_zero]
        · exact eq_zero_of_isRCartierPullback_of_not_isProperCurve p hpX hG₁ Γ hc hx₁
      rw [hG₁0]
      ring
    have hcorrZ : ∀ F : MMP.Mori.PrimeDivisor Z, ∃ G,
        RationalMap.transformPrimeDivisor φ' G = some F ∧
          LZ.coeff F = (logCanonicalDivisor K' B').coeff G := by
      intro F
      obtain ⟨G, hG⟩ : ∃ G, RationalMap.transformPrimeDivisor φ' G = some F := by
        have := hwm.not_isInverseExceptional F
        simpa [MMP.Flips.RationalMap.IsInverseExceptional] using this
      refine ⟨G, hG, ?_⟩
      rw [hLZ']
      exact transformDivisor_apply_of_eq_some hXv hZv p q hpX' hqZ' hpb hqb hinv hhq hG _
    have htr := transformDivisor_sub_eq_zero hXv hZv p q hpX' hqZ' hpb hqb hinv hhq hcorrZ hG₁ hG₂
    exact sub_eq_zero.mp (eq_zero_of_forall_eq_zero_of_transformDivisor_eq_zero hZv hWn q hqZ hq
      hqb (isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hG₁)
        (isCartierCombination_of_isRCartierPullback hG₂)) htr h0)
  refine ⟨hRel hcrepX, fun s hs0 hse => ?_⟩
  -- the nefness of `K_Z + φ_* C_s`
  obtain ⟨W₀, _, _, _, sW₀, p₀, q₀, h₀, hW₀, hW₀s, hp₀X, hq₀Z, hp₀, hq₀, hp₀b, hq₀b, hinv₀, hhq₀,
    -, -, -, -, -, -⟩ := hwm.exists_resolution
  subst hp₀X
  haveI : QuasiCompact (p₀ ≫ sX) := hW₀.toQuasiCompact
  haveI : LocallyOfFiniteType (p₀ ≫ sX) := hW₀.toLocallyOfFiniteType
  haveI : CompactSpace W₀ := QuasiCompact.compactSpace_of_compactSpace (p₀ ≫ sX)
  haveI : IsProper p₀ := isProper_of_isProjectiveMorphism p₀ hp₀
  haveI : IsProper q₀ := isProper_of_isProjectiveMorphism q₀ hq₀
  haveI : IsDominant p₀ := hp₀b.isDominant
  haveI : IsDominant q₀ := hq₀b.isDominant
  have hpq₀ : p₀ ≫ πX = q₀ ≫ πZ := comp_eq_comp_of_isOver πX πZ hwm.isOver p₀ q₀ h₀ hinv₀ hhq₀
  obtain ⟨GD, hGD, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p₀
    (isCartierCombination_of_isQFactorial hXm.2.1 (logCanonicalDivisor K' B'))
  obtain ⟨GDZ, hGDZ, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q₀
    (isCartierCombination_of_isQFactorial hZQ LZ)
  obtain ⟨E₁, hE₁, -⟩ := MMP.Flips.existsUnique_isRCartierPullback p₀
    (isCartierCombination_of_isQFactorial hXm.2.1 (logCanonicalDivisor K' CX))
  obtain ⟨E₂, hE₂, -⟩ := MMP.Flips.existsUnique_isRCartierPullback q₀
    (Crepant.isCartierCombination_logCanonicalDivisor hwm)
  have hD12 : GD = GDZ := hcrepX (p₀ ≫ sX) p₀ q₀ h₀ hW₀ hW₀s rfl hq₀Z hp₀ hq₀ hp₀b hq₀b hinv₀
    hhq₀ GD GDZ hGD hGDZ
  have hE12 : E₁ = E₂ := h2wm (p₀ ≫ sX) p₀ q₀ h₀ hW₀ rfl hq₀Z hp₀ hq₀ hp₀b hq₀b
    (Crepant.compHom_eq_of_isInverse hinv₀) hhq₀
    (by rw [transformDivisor_id, transformDivisor_id]; exact hE₁) hE₂
  have hMZ : logCanonicalDivisor (RationalMap.transformDivisor φ K)
      (RationalMap.transformDivisor φ ((1 - s) • B + s • C)) =
      (1 - s / t) • LZ + (s / t) • logCanonicalDivisor (RationalMap.transformDivisor φ' K')
        (RationalMap.transformDivisor φ' CX) := by
    rw [hLZ, transformDivisor_radial, ← hTK, ← hTB, ← hTC, hCX, transformDivisor_radial]
    exact logCanonicalDivisor_radial_eq _ _ _ ht
  have hM : IsRCartierPullback q₀ (logCanonicalDivisor (RationalMap.transformDivisor φ K)
      (RationalMap.transformDivisor φ ((1 - s) • B + s • C))) ((1 - s / t) • GDZ + (s / t) • E₂) := by
    rw [hMZ]
    exact isRCartierPullback_add (isRCartierPullback_smul _ hGDZ) (isRCartierPullback_smul _ hE₂)
  have hMX : IsRCartierPullback p₀ (logCanonicalDivisor K' ((1 - s) • B' + s • C'))
      ((1 - s / t) • GD + (s / t) • E₁) := by
    rw [logCanonicalDivisor_radial_eq K' B' C' ht, ← hCX]
    exact isRCartierPullback_add (isRCartierPullback_smul _ hGD) (isRCartierPullback_smul _ hE₁)
  have hnefs' := hnefs s hs0 (by rw [hτeq]; linarith)
  have hnefW := isRelativelyNef_of_isRCartierPullback (𝟙 S) πX (q₀ ≫ πZ) p₀
    (by rw [Category.comp_id, hpq₀]) hnefs' hMX
  rw [hD12, hE12] at hnefW
  haveI := surjective_of_isProper_of_isDominant q₀
  exact isRelativelyNef_of_isRCartierPullback_of_surjective q₀ hq₀Z πZ
    (isCartierCombination_of_isQFactorial hZQ _) hM hnefW

end ProgramEnd

/-! ### The main argument -/

/-- The theorem, for any `e` below the two radial constants. -/
private theorem main (εN τn : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ) (hN : NullSpec εN)
    (hnef : NefSpec τn) (hεN : ∀ s r m, 0 < εN s r m) (hτn : ∀ s r m, 0 < τn s r m) :
      ∀ {Y S Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
        [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
        (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
        [QuasiCompact sY] [QuasiCompact sZ] (πY : Y ⟶ S) (πZ : Z ⟶ S),
        MMP.Mori.IsProjectiveVariety ℂ sY → IsQFactorial sY →
        MMP.Mori.IsProjectiveVariety ℂ sS → πY ≫ sS = sY →
        ∀ {K : Divisor Y} {B C : RDivisor Y}, K.IsCanonicalDivisor sY 3 →
        IsRealTerminalPair sY B → IsRealTerminalPair sY C →
        MMP.Flips.IsRelativelyNef ℂ sY πY (MMP.Flips.logCanonicalDivisor K B) →
        ∀ ν : RationalNullData sY K B, ∀ e : ℝ,
        e ≤ τn ν.s ν.weight ν.m / (2 * (τn ν.s ν.weight ν.m + 6)) → e < εN ν.s ν.weight ν.m →
        ∀ (t : ℝ), 0 < t → t < e →
        ∀ φ : Y.RationalMap Z,
          IsNefWeakModel sY sZ sS πY πZ K ((1 - t) • B + t • C) φ → IsQFactorial sZ →
          (∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
            (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
            (h : Y.RationalMap W),
            MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
              q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
              IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
              MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
              ∃ GY GZ : RDivisor W,
                MMP.Flips.IsRCartierPullback p
                  (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) GY ∧
                MMP.Flips.IsRCartierPullback q
                  (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                    (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B + t • C))) GZ ∧
                ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - t) • B + t • C).coeff P →
                  ∃ P' : MMP.Mori.PrimeDivisor W,
                    MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                      (GY - GZ).coeff P' = 0) →
          (∀ s : ℝ, 0 < s → s < e →
            IsNefWeakModel sY sZ sS πY πZ K ((1 - s) • B + s • C) φ ∧
            ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
              (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
              (h : Y.RationalMap W),
              MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
                q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
                IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
                MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
                ∃ GY GZ : RDivisor W,
                  MMP.Flips.IsRCartierPullback p
                    (MMP.Flips.logCanonicalDivisor K ((1 - s) • B + s • C)) GY ∧
                  MMP.Flips.IsRCartierPullback q
                    (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                      (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))) GZ ∧
                  ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - s) • B + s • C).coeff P →
                    ∃ P' : MMP.Mori.PrimeDivisor W,
                      MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                        (GY - GZ).coeff P' = 0) ∧
          (∀ s s' : ℝ, 0 < s → s < e →
            0 < s' → s' < e →
            IsNefModelEquivalent sZ sZ sS πZ πZ
              (MMP.Mori.RationalMap.transformDivisor φ K)
              (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))
              (MMP.Mori.RationalMap.transformDivisor φ K)
              (MMP.Mori.RationalMap.transformDivisor φ ((1 - s') • B + s' • C))
              (𝟙 Z : Z ⟶ Z).toRationalMap) := by
  intro Y S Z _ _ _ _ _ _ sY sS sZ _ _ πY πZ hY hYQ hS hπ K B C hK hB hC hD ν e he1 he2 t ht0 hte
    φ hφ hZQ hcomp
  have : IsSeparated sS := ((MMP.Mori.isProjectiveVariety_iff ℂ sS).mp hS).1.toIsSeparated
  have hτ := hτn ν.s ν.weight ν.m
  have he : e < 1 := by
    have : τn ν.s ν.weight ν.m / (2 * (τn ν.s ν.weight ν.m + 6)) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  obtain ⟨hcrep, hnefs⟩ : IsCrepantAlong sY sZ φ (logCanonicalDivisor K B)
      (logCanonicalDivisor (RationalMap.transformDivisor φ K) (RationalMap.transformDivisor φ B)) ∧
      ∀ s : ℝ, 0 < s → s < e → IsRelativelyNef ℂ sZ πZ
        (logCanonicalDivisor (RationalMap.transformDivisor φ K)
          (RationalMap.transformDivisor φ ((1 - s) • B + s • C))) := by
    haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    have hCt : IsRealTerminalPair sY ((1 - t) • B + t • C) :=
      isRealTerminalPair_convex hYQ hB hC ht0.le (by linarith)
    have hcomp' : ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
        (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z) (h : Y.RationalMap W),
        MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧ q ≫ sZ = sW ∧
          IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧ IsBirationalMorphism p ∧
          IsBirationalMorphism q ∧ MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧
          h.compHom q = φ ∧
          ∃ GY GZ : RDivisor W,
            IsRCartierPullback p (logCanonicalDivisor K ((1 - t) • B + t • C)) GY ∧
            IsRCartierPullback q
              (logCanonicalDivisor (RationalMap.transformDivisor φ K)
                (RationalMap.transformDivisor φ ((1 - t) • B + t • C))) GZ ∧
            ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - t) • B + t • C).coeff P →
              ∀ P' : MMP.Mori.PrimeDivisor W, RationalMap.transformPrimeDivisor h P = some P' →
                (GY - GZ).coeff P' = 0 := by
      obtain ⟨W, i₁, i₂, i₃, sW, p, q, h, hW, hWs, hpY, hqZ, hp, hq, hpb, hqb, hinv, hhq, GY, GZ,
        hGY, hGZ, h0⟩ := hcomp
      refine ⟨W, i₁, i₂, i₃, sW, p, q, h, hW, hWs, hpY, hqZ, hp, hq, hpb, hqb, hinv, hhq, GY, GZ,
        hGY, hGZ, fun P hP P' hP' => ?_⟩
      obtain ⟨P'', hP'', hz⟩ := h0 P hP
      rw [hP'] at hP''
      cases hP''
      exact hz
    obtain ⟨n, Yi, sYi, _, _, _, _, πYi, KY, CY, R, Zi, sZi, f, g, fp, hM, hP, hnefn⟩ :=
      (IsRealTerminalPair.terminates_of_isNefWeakModel hY hS hπ hYQ hK.topologicalKrullDim_eq
        ⟨3, hK⟩ hCt hφ hZQ hcomp').2
    have hKX : ∀ i, i < n + 1 → ∃ m : ℕ,
        Divisor.IsCanonicalDivisor (modelStr sY sYi i) m (divisorSeq K KY i) := by
      intro i hi
      rcases i with _ | i
      · exact ⟨3, hK⟩
      · exact Kit.IsProgramStep.isCanonicalDivisor_next (hP i (by omega))
    have hall : ∀ i, i ≤ n → ProgInv sY sS sZ πZ K B C φ t ν.s ν.weight ν.m
        (modelStr sY sYi i) (modelMap πY πYi i) (divisorSeq K KY i)
        (divisorSeq ((1 - t) • B + t • C) CY i) := by
      intro i
      induction i with
      | zero =>
        intro _
        exact ⟨K, B, C, φ, hφ, hK, Divisor.LinearlyEquivalent.refl K, rfl, rfl, rfl, rfl,
          ⟨ν, rfl, rfl, fun i => rfl⟩, hD, coeff_nonneg_of_isRealTerminalPair hC,
          Kit.isRealKltPair_of_isRealTerminalPair hC, id⟩
      | succ i ih =>
        intro hi
        exact progInv_step εN hN hS hZQ ht0 (hte.trans he2) (hM i (by omega)) (hM (i + 1) hi)
          (hKX i (by omega)) (hP i (by omega)) (ih (by omega))
    exact crep_and_nef_of_progInv τn hnef hS hZQ ht0 hte he1 (hM n le_rfl) hnefn (hall n le_rfl)
  exact conclusion_of_isCrepantAlong hYQ hZQ hB hC he ht0 hte hφ hcomp hcrep hnefs

/-- The theorem. -/
private theorem solution :
    ∃ τ : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ, (∀ s r m, 0 < τ s r m) ∧
      ∀ {Y S Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
        [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
        (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
        [QuasiCompact sY] [QuasiCompact sZ] (πY : Y ⟶ S) (πZ : Z ⟶ S),
        MMP.Mori.IsProjectiveVariety ℂ sY → IsQFactorial sY →
        MMP.Mori.IsProjectiveVariety ℂ sS → πY ≫ sS = sY →
        ∀ {K : Divisor Y} {B C : RDivisor Y}, K.IsCanonicalDivisor sY 3 →
        IsRealTerminalPair sY B → IsRealTerminalPair sY C →
        MMP.Flips.IsRelativelyNef ℂ sY πY (MMP.Flips.logCanonicalDivisor K B) →
        ∀ ν : RationalNullData sY K B,
        ∀ (t : ℝ), 0 < t → t < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
        ∀ φ : Y.RationalMap Z,
          IsNefWeakModel sY sZ sS πY πZ K ((1 - t) • B + t • C) φ → IsQFactorial sZ →
          (∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
            (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
            (h : Y.RationalMap W),
            MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
              q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
              IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
              MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
              ∃ GY GZ : RDivisor W,
                MMP.Flips.IsRCartierPullback p
                  (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) GY ∧
                MMP.Flips.IsRCartierPullback q
                  (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                    (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B + t • C))) GZ ∧
                ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - t) • B + t • C).coeff P →
                  ∃ P' : MMP.Mori.PrimeDivisor W,
                    MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                      (GY - GZ).coeff P' = 0) →
          (∀ s : ℝ, 0 < s → s < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            IsNefWeakModel sY sZ sS πY πZ K ((1 - s) • B + s • C) φ ∧
            ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
              (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
              (h : Y.RationalMap W),
              MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
                q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
                IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
                MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
                ∃ GY GZ : RDivisor W,
                  MMP.Flips.IsRCartierPullback p
                    (MMP.Flips.logCanonicalDivisor K ((1 - s) • B + s • C)) GY ∧
                  MMP.Flips.IsRCartierPullback q
                    (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                      (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))) GZ ∧
                  ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - s) • B + s • C).coeff P →
                    ∃ P' : MMP.Mori.PrimeDivisor W,
                      MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                        (GY - GZ).coeff P' = 0) ∧
          (∀ s s' : ℝ, 0 < s → s < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            0 < s' → s' < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            IsNefModelEquivalent sZ sZ sS πZ πZ
              (MMP.Mori.RationalMap.transformDivisor φ K)
              (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))
              (MMP.Mori.RationalMap.transformDivisor φ K)
              (MMP.Mori.RationalMap.transformDivisor φ ((1 - s') • B + s' • C))
              (𝟙 Z : Z ⟶ Z).toRationalMap) := by
  obtain ⟨εN, hεN, hN⟩ :=
    MMP.Fourfold.exists_pos_forall_isExtremalRay_null_and_isNegativeExtremalContraction
  obtain ⟨τn, hτn, hnef⟩ := MMP.Fourfold.exists_pos_forall_isRelativelyNef_of_isRelativelyNef
  refine ⟨fun s r m => min (τn s r m) (εN s r m), fun s r m => lt_min (hτn s r m) (hεN s r m),
    ?_⟩
  intro Y S Z _ _ _ _ _ _ sY sS sZ _ _ πY πZ hY hYQ hS hπ K B C hK hB hC hD ν
  have hpos := lt_min (hτn ν.s ν.weight ν.m) (hεN ν.s ν.weight ν.m)
  exact main εN τn hN hnef hεN hτn sY sS sZ πY πZ hY hYQ hS hπ hK hB hC hD ν _
    (div_le_div_of_le hpos (min_le_left _ _)) ((div_lt_self' hpos).trans_le (min_le_right _ _))

end Main

end Proof_lem_fourfold_radial_weak_model_interval

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Transferring a radial nef interval to a given weak model.** There is a positive function
`τ` of the number `s` of boundaries, the weights `r : Fin s → ℝ` and the Cartier index `m` with
the following property. Let `Y` be a projective `ℚ`-factorial complex threefold with canonical
divisor `K` over a projective complex variety `S` (by `π_Y`), let `(Y, B)` and `(Y, C)` be real
terminal pairs (`MMP.Fourfold.IsRealTerminalPair`) with `K + B` nef over `S`, let `ν` be
rational null-decomposition data for `B` (`MMP.Fourfold.RationalNullData`), and put
`ε = τ / (2 (τ + 6))` for `τ = τ ν.s ν.weight ν.m` and `C_t = (1 - t) B + t C`. Let `0 < t < ε`
and let `φ : Y ⤏ Z` be a `ℚ`-factorial nef weak model of `(Y, C_t)` over `S`
(`MMP.Fourfold.IsNefWeakModel`) such that on a common projective resolution `p : W ⟶ Y`,
`q : W ⟶ Z` the comparison `p^*(K + C_t) - q^*(K_Z + φ_* C_t)` has coefficient zero at the strict
transform of every prime `P` with `0 < C_t(P)`. Then for every `0 < s < ε`, `φ` is a nef weak
model of `(Y, C_s)` whose comparison, on some common projective resolution, has coefficient zero
at the strict transform of every prime `P` with `0 < C_s(P)`; and for all `0 < s, s' < ε` the
nef models `(Z, φ_* C_s)` and `(Z, φ_* C_{s'})` are equivalent
(`MMP.Fourfold.IsNefModelEquivalent`) through the identity of `Z`. -/
@[mmp "lem_fourfold_radial_weak_model_interval"]
public theorem exists_pos_forall_isNefWeakModel_of_isNefWeakModel :
    ∃ τ : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ, (∀ s r m, 0 < τ s r m) ∧
      ∀ {Y S Z : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
        [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
        (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
        [QuasiCompact sY] [QuasiCompact sZ] (πY : Y ⟶ S) (πZ : Z ⟶ S),
        MMP.Mori.IsProjectiveVariety ℂ sY → IsQFactorial sY →
        MMP.Mori.IsProjectiveVariety ℂ sS → πY ≫ sS = sY →
        ∀ {K : Divisor Y} {B C : RDivisor Y}, K.IsCanonicalDivisor sY 3 →
        IsRealTerminalPair sY B → IsRealTerminalPair sY C →
        MMP.Flips.IsRelativelyNef ℂ sY πY (MMP.Flips.logCanonicalDivisor K B) →
        ∀ ν : RationalNullData sY K B,
        ∀ (t : ℝ), 0 < t → t < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
        ∀ φ : Y.RationalMap Z,
          IsNefWeakModel sY sZ sS πY πZ K ((1 - t) • B + t • C) φ → IsQFactorial sZ →
          (∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
            (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
            (h : Y.RationalMap W),
            MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
              q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
              IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
              MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
              ∃ GY GZ : RDivisor W,
                MMP.Flips.IsRCartierPullback p
                  (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) GY ∧
                MMP.Flips.IsRCartierPullback q
                  (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                    (MMP.Mori.RationalMap.transformDivisor φ ((1 - t) • B + t • C))) GZ ∧
                ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - t) • B + t • C).coeff P →
                  ∃ P' : MMP.Mori.PrimeDivisor W,
                    MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                      (GY - GZ).coeff P' = 0) →
          (∀ s : ℝ, 0 < s → s < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            IsNefWeakModel sY sZ sS πY πZ K ((1 - s) • B + s • C) φ ∧
            ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W)
              (_ : IsNormal W) (sW : W ⟶ Spec (.of ℂ)) (p : W ⟶ Y) (q : W ⟶ Z)
              (h : Y.RationalMap W),
              MMP.Mori.IsVariety ℂ sW ∧ MMP.Mori.IsSmoothScheme sW ∧ p ≫ sY = sW ∧
                q ≫ sZ = sW ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism q ∧
                IsBirationalMorphism p ∧ IsBirationalMorphism q ∧
                MMP.Mori.RationalMap.IsInverse p.toRationalMap h ∧ h.compHom q = φ ∧
                ∃ GY GZ : RDivisor W,
                  MMP.Flips.IsRCartierPullback p
                    (MMP.Flips.logCanonicalDivisor K ((1 - s) • B + s • C)) GY ∧
                  MMP.Flips.IsRCartierPullback q
                    (MMP.Flips.logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor φ K)
                      (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))) GZ ∧
                  ∀ P : MMP.Mori.PrimeDivisor Y, 0 < ((1 - s) • B + s • C).coeff P →
                    ∃ P' : MMP.Mori.PrimeDivisor W,
                      MMP.Mori.RationalMap.transformPrimeDivisor h P = some P' ∧
                        (GY - GZ).coeff P' = 0) ∧
          (∀ s s' : ℝ, 0 < s → s < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            0 < s' → s' < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            IsNefModelEquivalent sZ sZ sS πZ πZ
              (MMP.Mori.RationalMap.transformDivisor φ K)
              (MMP.Mori.RationalMap.transformDivisor φ ((1 - s) • B + s • C))
              (MMP.Mori.RationalMap.transformDivisor φ K)
              (MMP.Mori.RationalMap.transformDivisor φ ((1 - s') • B + s' • C))
              (𝟙 Z : Z ⟶ Z).toRationalMap) :=
                by exact Proof_lem_fourfold_radial_weak_model_interval.solution

end MMP.Fourfold
