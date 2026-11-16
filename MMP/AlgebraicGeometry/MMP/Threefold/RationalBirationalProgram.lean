module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.RationalProgram
import MMP.AlgebraicGeometry.MMP.Threefold.LogMMP
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
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
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedPushforward
import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.LocallyFreeSmooth
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients
import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineBundleIrreducible
import StacksFrontier.CategoryTheory.Sites.IsIsoOfBijectiveOnCoveringObjects
import StacksFrontier.AlgebraicGeometry.Chow.SmoothComponentMultiplicity
import StacksFrontier.AlgebraicGeometry.Blowup.ProjectiveLineIdealOfEquations
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
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentChartZeroCycleGrouping
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartFiniteLength
import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyQuasiAffineHom
import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.MapExact
import StacksFrontier.AlgebraicGeometry.HigherDirectImage.ModuleAbelianVanishing
import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SourceDimension
import StacksFrontier.AlgebraicGeometry.FlatModuleCohomologyBaseChange.QuasiSeparated
import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectTensorLocalModels
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
import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechFractionBaseChange
import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
import StacksFrontier.AlgebraicGeometry.Modules.MonoRestrictLocality
import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveDisjointUnion
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.InvertibleToBaseIso
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ZeroSectionStalk
import StacksFrontier.Topology.Dimension.UnionDimension
import StacksFrontier.Algebra.Homology.RightDerivedDeltaEpi
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroUnconditional
import StacksFrontier.AlgebraicGeometry.Curves.LinearSystemScheme.LinearEquations.ChartKernel
import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso
import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.CoherentExtRestrictExtension
import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
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
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageRingedSpace
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing
import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityFromCechVanishing
import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
import StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic
import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.Combinatorics.WeightedGraph.ChainDeterminant

/-!
# The rational birational program property in dimension three

For every projective birational morphism `p : W ⟶ Z` of normal projective complex threefolds
with `W` smooth, and every effective `ℚ`-divisor `C` on `W` with snc support and coefficients
less than one, there is a finite projective negative program from `(W, C)` over `Z` ending with a
`ℚ`-factorial projective klt pair `(Y, C_Y)` over `Z` with `K_Y + C_Y` nef over `Z`, where
`C_Y` is the push-forward of `C` and no prime divisor is extracted. That is, the property
`MMP.Fourfold.RationalBirationalProgramProperty 3` holds.

The proof runs the threefold log minimal model program `MMP.Fourfold.ProjectiveLowerLogMMP 3`
over `Z`: the snc pair with coefficients less than one is klt, hence dlt; coefficients stay less
than one along the program, so every model is klt; no fibre-type contraction can occur over the
three-dimensional base `Z`, so the final adjoint is nef; and elementary negative steps extract no
divisor and push the boundary forward.

## Main results

* `MMP.Fourfold.rationalBirationalProgramProperty_three`: the property `Q(3)`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, §3.7 and §6.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

universe u

namespace Proof_thm_fourfold_rational_birational_program_q3

open TopologicalSpace MMP.Mori MMP.Fourfold

open MMP MMP.Flips in
/-- If `g'` represents `φ` at `η_P` and `g'(η_P) = η_E`, then the strict transform of `P` under
`φ` is `E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- `X ⟶ ⊤_ Scheme` is separated for a variety `X`. -/
private theorem isSeparated_terminal_of_isVariety {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) : IsSeparated (X ↘ ⊤_ Scheme) := by
  have : IsSeparated sX := hX.toIsSeparated
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- A proper birational morphism `μ : Y ⟶ X` of varieties onto a normal variety is an isomorphism
over a neighbourhood of every point `x` of `X` whose local ring is a valuation ring (the generic
point, and the generic points of the prime divisors): the fibre over `x` is a single point, so
`x` lies in the finite-fibre locus, over which `μ` is an isomorphism. -/
private theorem mem_biregularLocus_of_valuationRing {Y X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) {μ : Y ⟶ X}
    [IsProper μ] (hY : MMP.Mori.IsVariety ℂ (μ ≫ sX)) (hμ : IsBirationalMorphism μ) (x : X)
    [ValuationRing (X.presheaf.stalk x)] : x ∈ biregularLocus μ := by
  have : IsIntegral Y := hY.toIsIntegral
  have : IsNormal X := hX.2
  have : IsDominant μ := hμ.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (μ ≫ sX) := hY.toIsSeparated
  have : IsSeparated μ := IsSeparated.of_comp μ sX
  have hbij := hμ.functionFieldMap_bijective
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso μ
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hμ)).1 inferInstance
  let V : X.Opens := ⟨_, hU⟩
  have hxV : x ∈ V := by
    change (μ ⁻¹' {x}).Finite
    refine Set.Subsingleton.finite fun a ha b hb => ?_
    have ha' : μ a = x := ha
    have hb' : μ b = x := hb
    have : ValuationRing (X.presheaf.stalk (μ a)) := by rw [ha']; infer_instance
    have : ValuationRing (X.presheaf.stalk (μ b)) := by rw [hb']; infer_instance
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij a
    have := MMP.Positivity.isIso_stalkMap_of_valuationRing μ hbij b
    exact MMP.Positivity.eq_of_isIso_stalkMap μ hbij (hb'.trans ha'.symm)
  exact le_biregularLocus (f := μ) (V := V) hiso hxV

/-! ### Birationality at the generic point -/

/-- For integral schemes, a morphism is birational at the generic point when it maps the generic
point to the generic point and is an isomorphism on the stalks there. -/
private theorem isBirational_iff_of_isIntegral {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) : IsBirational f ↔
      f (genericPoint X) = genericPoint Y ∧ IsIso (f.stalkMap (genericPoint X)) := by
  unfold IsBirational
  rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
  simp

/-- If `f` and `f ≫ g` are birational at the generic point, so is `g`. -/
private theorem isBirational_of_comp {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirational f) (hfg : IsBirational (f ≫ g)) :
    IsBirational g := by
  rw [isBirational_iff_of_isIntegral] at *
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hfg1, hfg2⟩ := hfg
  refine ⟨by rw [← hf1, ← Scheme.Hom.comp_apply, hfg1], ?_⟩
  rw [Scheme.Hom.stalkMap_comp] at hfg2
  have : IsIso (g.stalkMap (f (genericPoint X))) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hf2 hfg2
  exact hf1 ▸ this

/-! ### Crepant dlt lifts -/

open MMP.Threefold.Mori.OpenRestriction in
/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen {R : Type*} [Zero R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => (sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E₀)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE₀ : D.restrictOpen U E₀ ≠ 0))
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
  exact (isSmoothScheme_comap_iff U.ι g (OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf
    E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr fun z _ => hsm ▸ trivial

section RIntersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A proper curve over `k` is a curve over `k`. -/
private theorem isCurve_properCurve (C : ProperCurve sX) :
    AlgebraicGeometry.IsCurve k (C.ι ≫ sX) where
  toIsIntegral := inferInstance
  toIsSeparated := inferInstance
  toLocallyOfFiniteType := (inferInstance : IsProper (C.ι ≫ sX)).toLocallyOfFiniteType
  toQuasiCompact := inferInstance
  topologicalKrullDim_eq_one := C.dim_eq

/-- A proper curve has more than one point. -/
private theorem not_subsingleton (C : ProperCurve sX) : ¬ Subsingleton C.scheme := fun _ => by
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  refine not_subsingleton C ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := ν.surjective a
  obtain ⟨x', rfl⟩ := ν.surjective b
  exact (hy x).trans (hy x').symm

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : MMP.Flips.IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
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

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{u}} [IsIntegral Y]
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
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : MMP.Flips.IsCurveNormalization ν)
    (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    degreeOn k sX (ν ≫ C.ι) hdim M = degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := isCurve_properCurve C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [degreeOn, degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem eq_degreeOn {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : MMP.Flips.IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- Every Cartier divisor has an intersection number with a proper curve: the normalization
of the curve is a normal proper curve birational to it. -/
private theorem exists_isCartierIntersectionNumber (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) : ∃ d, MMP.Flips.IsCartierIntersectionNumber k sX C L hL d := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := isCurve_properCurve C
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV
          hiso }
  exact ⟨_, _, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le,
    rfl⟩

/-- A presentation `D = ∑ rⱼ Lⱼ` computes `D · C = ∑ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem isRIntersectionNumber_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    MMP.Flips.IsRIntersectionNumber k sX D r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) := by
  choose d hd using fun j => exists_isCartierIntersectionNumber C (L j) (hL j)
  refine ⟨hL, d, hD, hd, Finset.sum_congr rfl fun j _ => ?_⟩
  rw [eq_degreeOn (hd j)]

/-- **The two notions of relative nefness agree.** A `ℚ`-Cartier `ℚ`-divisor `D` whose real
divisor is `f`-nef, with intersection numbers computed from a presentation by Cartier divisors, is
`f`-nef in the `ℚ`-Cartier sense: both compute `D · C` as the degree of `D` along `C`. -/
private theorem isRelativelyNef_of_isRelativelyNef_toRDivisor [IsIntegral X] {Y : Scheme.{u}}
    {f : X ⟶ Y} {D : QDivisor X} (hD : D.IsQCartier)
    (h : MMP.Flips.IsRelativelyNef k sX f (QDivisor.toRDivisor D)) :
    QDivisor.IsRelativelyNef sX f D := by
  obtain ⟨m, r, L, hL, hDeq, hnn⟩ := h
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hD fun C hC => ?_
  set c := D.cartierIndex hD
  have hc : (0 : ℚ) < c := by exact_mod_cast QDivisor.cartierIndex_pos hD
  set M : Divisor X := (D.cartierIndexSMul hD : Divisor X)
  have hM : M.IsCartier := (D.cartierIndexSMul hD).2
  have hMD := QDivisor.toQDivisor_cartierIndexSMul D hD
  have hDR : QDivisor.toRDivisor D =
      ∑ _j : Fin 1, ((1 : ℝ) / c) • Divisor.toRDivisor M := by
    ext P
    have hP := congrArg (fun E => DivisorWithCoeffs.coeff E P) hMD
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at hP
    simp only [QDivisor.coeff_toRDivisor, Finset.univ_unique, Finset.sum_singleton,
      DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, smul_eq_mul]
    have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
    have : ((M.coeff P : ℚ) : ℝ) = (c : ℝ) * (D.coeff P : ℝ) := by
      rw [hP]; push_cast; ring
    rw [show ((M.coeff P : ℤ) : ℝ) = ((M.coeff P : ℚ) : ℝ) by push_cast; rfl, this]
    field_simp
  have hx := isRIntersectionNumber_sum C r L hL hDeq
  have hy := isRIntersectionNumber_sum C (fun _ : Fin 1 => (1 : ℝ) / c) (fun _ => M)
    (fun _ => hM) hDR
  have heq := (MMP.Flips.IsRIntersectionNumber.eq_and_linear k sX C).1 _ r L _ _ _ _ hx hy
  have h0 := hnn C hC _ hx
  rw [heq] at h0
  rw [QDivisor.intersectionNumber_eq_of_toQDivisor_eq k sX C.ι C.dim_le D hD M hM hMD]
  simp only [Finset.univ_unique, Finset.sum_singleton] at h0
  have : (0 : ℝ) ≤ ((M.degreeOn k sX C.ι C.dim_le hM : ℚ) / c : ℚ) := by
    push_cast
    rw [div_eq_mul_one_div, mul_comm]
    exact h0
  exact_mod_cast this

end RIntersection

/-! ### Prime divisors along a step of the program -/

/-- A map `φ : X ⤏ X'` over `Z` (for `f : X ⟶ Z`, `f⁺ : X' ⟶ Z`) satisfies `f⁺ ∘ φ = f` at every
point of its domain of definition, `Z` being separated. -/
private theorem apply_toPartialMap_hom {X X' Z : Scheme.{u}} [IsIntegral X] [X'.IsSeparated]
    [Z.IsSeparated] (f : X ⟶ Z) (fp : X' ⟶ Z) (φ : X.RationalMap X')
    (hφ : φ.compHom fp = f.toRationalMap) (x : X) (hx : x ∈ φ.domain) :
    fp (φ.toPartialMap.hom ⟨x, hx⟩) = f x := by
  have he : (φ.toPartialMap.compHom fp).toRationalMap = f.toPartialMap.toRationalMap := by
    change _ = f.toRationalMap
    rw [← hφ]
    conv_rhs => rw [← φ.toRationalMap_toPartialMap]
    rfl
  obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  have hWl' : W ≤ φ.toPartialMap.domain := hWl
  have : IsDominant (X.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
  have hEq' : X.homOfLE hWl' ≫ φ.toPartialMap.hom ≫ fp = X.homOfLE hWr ≫ X.topIso.hom ≫ f := by
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.compHom_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    exact hEq
  have key : φ.toPartialMap.hom ≫ fp = φ.toPartialMap.domain.ι ≫ f := by
    refine ext_of_isDominant (X.homOfLE hWl') ?_
    refine hEq'.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc X hWr f
  exact congrArg (fun g : φ.toPartialMap.domain.toScheme ⟶ Z => g ⟨x, hx⟩) key

/-- A morphism restricting to an isomorphism over `V` is injective on the preimage of `V`. -/
private theorem eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens)
    [IsIso (g ∣_ V)] {a b : X} (ha : g a ∈ V) (h : g a = g b) : a = b := by
  have hb : g b ∈ V := h ▸ ha
  have hopen : IsOpenImmersion ((g ⁻¹ᵁ V).ι ≫ g) := by
    rw [← morphismRestrict_ι]; infer_instance
  have := ((g ⁻¹ᵁ V).ι ≫ g).isOpenEmbedding.injective
    (a₁ := (⟨a, ha⟩ : g ⁻¹ᵁ V)) (a₂ := ⟨b, hb⟩) h
  exact congrArg Subtype.val this

/-- **Prime divisors along a step.** Let `f : X ⟶ Z` and `f⁺ : X' ⟶ Z` be proper birational
morphisms of varieties onto a normal variety and `φ : X ⤏ X'` a map over `Z`. If a prime divisor
`F'` of `X'` lies over a prime divisor `Q` of `Z`, then `f` and `f⁺` are isomorphisms over a
neighbourhood `V₀` of `η_Q`, there is a prime divisor `F` of `X` over `Q`, and every divisor `D`
on `X` has `coeff_{F'} φ_* D = coeff_F D`. -/
private theorem exists_primeDivisor_of_isOver {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsIntegral Z] [IsLocallyNoetherian Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) (fp : X' ⟶ Z)
    [IsProper f] [IsProper fp] (hXv : MMP.Mori.IsVariety ℂ (f ≫ sZ))
    (hX'v : MMP.Mori.IsVariety ℂ (fp ≫ sZ)) (hf : IsBirationalMorphism f)
    (hfp : IsBirationalMorphism fp) (φ : X.RationalMap X') (hφ : φ.compHom fp = f.toRationalMap)
    (F' : MMP.Mori.PrimeDivisor X') (Q : MMP.Mori.PrimeDivisor Z)
    (hQ : fp F'.genericPoint = Q.genericPoint) :
    ∃ (F : MMP.Mori.PrimeDivisor X) (V₀ : Z.Opens) (hV : Q.genericPoint ∈ V₀),
      IsIso (f ∣_ V₀) ∧ IsIso (fp ∣_ V₀) ∧ f F.genericPoint = Q.genericPoint ∧
      ∀ D : QDivisor X, (MMP.Mori.RationalMap.transformDivisor φ D).coeff F' = D.coeff F := by
  classical
  have : IsNormal Z := hZ.2
  have : IsSeparated sZ := hZ.1.toIsSeparated
  have : Z.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sZ]; infer_instance⟩
  have : IsSeparated (fp ≫ sZ) := hX'v.toIsSeparated
  have : X'.IsSeparated := ⟨by rw [← Limits.terminal.comp_from (fp ≫ sZ)]; infer_instance⟩
  have hsep := isSeparated_terminal_of_isVariety hX'v
  have := Q.isDiscreteValuationRing_localRing
  set V₀ : Z.Opens := biregularLocus f ⊓ biregularLocus fp
  have hQV : Q.genericPoint ∈ V₀ :=
    ⟨mem_biregularLocus_of_valuationRing hZ hXv hf _,
      mem_biregularLocus_of_valuationRing hZ hX'v hfp _⟩
  have hfV : IsIso (f ∣_ V₀) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  have hfpV : IsIso (fp ∣_ V₀) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  -- the point of `X` over `η_Q`
  set U : X.Opens := f ⁻¹ᵁ V₀
  have hUopen : IsOpenImmersion (U.ι ≫ f) := by rw [← morphismRestrict_ι]; infer_instance
  set y : U := (inv (f ∣_ V₀)) ⟨Q.genericPoint, hQV⟩
  have hfy : f (U.ι y) = Q.genericPoint := by
    have h1 : (f ∣_ V₀) y = ⟨Q.genericPoint, hQV⟩ := by
      change ((inv (f ∣_ V₀)) ≫ (f ∣_ V₀)) _ = _
      rw [IsIso.inv_hom_id]; rfl
    have h2 := congrArg (fun g : U.toScheme ⟶ Z => g y) (morphismRestrict_ι f V₀)
    change V₀.ι ((f ∣_ V₀) y) = f (U.ι y) at h2
    rw [← h2, h1]; rfl
  have hcoh : Order.coheight (U.ι y) = 1 := by
    rw [coheight_eq_of_isOpenImmersion U.ι, ← coheight_eq_of_isOpenImmersion (U.ι ≫ f)]
    change Order.coheight (f (U.ι y)) = 1
    rw [hfy, Q.coheight_genericPoint]
  set F : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hFη : F.genericPoint = U.ι y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  have hfF : f F.genericPoint = Q.genericPoint := by rw [hFη, hfy]
  refine ⟨F, V₀, hQV, hfV, hfpV, hfF, fun D => ?_⟩
  -- the strict transform of `F` is `F'`, and only `F` maps to `F'`
  have hdom : ∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ φ.domain := fun P =>
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one f fp φ hφ (by rw [P.coheight_genericPoint])
  have hg' : φ.toPartialMap.toRationalMap = φ := φ.toRationalMap_toPartialMap
  have hF' : F'.genericPoint = φ.toPartialMap.hom ⟨F.genericPoint, hdom F⟩ := by
    refine eq_of_isIso_morphismRestrict fp V₀ (hQ ▸ hQV) ?_
    rw [hQ, apply_toPartialMap_hom f fp φ hφ _ (hdom F), hfF]
  have hE := transformPrimeDivisor_eq_some_of_genericPoint_eq φ.toPartialMap hg' (hdom F) hF'
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hE (fun P hP => ?_) D
  have h1 :=
    MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hP φ.toPartialMap hg' (hdom P)
  have h2 : f P.genericPoint = f F.genericPoint := by
    rw [← apply_toPartialMap_hom f fp φ hφ _ (hdom P), ← h1, hQ, hfF]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (eq_of_isIso_morphismRestrict f V₀ (h2 ▸ hfF ▸ hQV) h2)

/-- **Valuations along a step.** With `f : X ⟶ Z`, `f⁺ : X' ⟶ Z` isomorphisms over `V₀ ∋ η_Q` and
prime divisors `F ⊆ X`, `F' ⊆ X'` over `Q`, the divisors `F` and `F'` over `S` (via
`π = g ∘ f` and `π' = g ∘ f⁺`) define the same valuation of `k(S)`. -/
private theorem valuation_eq_of_isIso_morphismRestrict {X X' Z S : Scheme.{0}} [IsIntegral S]
    {sS : S ⟶ Spec (.of ℂ)} (f : X ⟶ Z) (fp : X' ⟶ Z) (g : Z ⟶ S) {π : X ⟶ S} {π' : X' ⟶ S}
    (hπ : f ≫ g = π) (hπ' : fp ≫ g = π') (hX : IsNormalVariety ℂ (π ≫ sS))
    (hX' : IsNormalVariety ℂ (π' ≫ sS)) (hb : IsBirationalMorphism π)
    (hb' : IsBirationalMorphism π') (V₀ : Z.Opens) [IsIso (f ∣_ V₀)] [IsIso (fp ∣_ V₀)]
    (F : MMP.Mori.PrimeDivisor X) (F' : MMP.Mori.PrimeDivisor X') (hV : f F.genericPoint ∈ V₀)
    (h : fp F'.genericPoint = f F.genericPoint) :
    (⟨X', π', hX', hb', F'⟩ : DivisorOver ℂ sS).valuation =
      (⟨X, π, hX, hb, F⟩ : DivisorOver ℂ sS).valuation := by
  have hV' : fp F'.genericPoint ∈ V₀ := h ▸ hV
  let e : (fp ⁻¹ᵁ V₀).toScheme ≅ (f ⁻¹ᵁ V₀).toScheme := asIso (fp ∣_ V₀) ≪≫ (asIso (f ∣_ V₀)).symm
  refine MMP.Positivity.DivisorOver.valuation_eq_of_iso _ _ (fp ⁻¹ᵁ V₀) (f ⁻¹ᵁ V₀) hV' hV e ?_ ?_
  · change ((fp ∣_ V₀) ≫ inv (f ∣_ V₀)) ≫ (f ⁻¹ᵁ V₀).ι ≫ π = (fp ⁻¹ᵁ V₀).ι ≫ π'
    rw [← hπ, ← hπ', ← Category.assoc (f ⁻¹ᵁ V₀).ι, ← morphismRestrict_ι, ← Category.assoc,
      Category.assoc _ (inv _), IsIso.inv_hom_id_assoc, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  · have hinj : Function.Injective (f ∣_ V₀) := (f ∣_ V₀).isOpenEmbedding.injective
    apply hinj
    change ((fp ∣_ V₀) ≫ inv (f ∣_ V₀) ≫ (f ∣_ V₀)) _ = _
    rw [IsIso.inv_hom_id, Category.comp_id]
    apply Subtype.ext
    have h1 := congrArg (fun k : (fp ⁻¹ᵁ V₀).toScheme ⟶ Z => k ⟨F'.genericPoint, hV'⟩)
      (morphismRestrict_ι fp V₀)
    have h2 := congrArg (fun k : (f ⁻¹ᵁ V₀).toScheme ⟶ Z => k ⟨F.genericPoint, hV⟩)
      (morphismRestrict_ι f V₀)
    change V₀.ι _ = fp F'.genericPoint at h1
    change V₀.ι _ = f F.genericPoint at h2
    exact h1.trans (h.trans h2.symm)

/-- A small contraction `f : X ⟶ Z` of integral schemes is birational, and maps the generic point
of every prime divisor of `X` to the generic point of a prime divisor of `Z`: it is an
isomorphism off closed subsets of codimension `≥ 2`. -/
private theorem isBirationalMorphism_and_exists_of_isSmall {k : Type u} [Field k]
    {X Z : Scheme.{u}} [IsIntegral X] [IsIntegral Z] {sZ : Z ⟶ Spec (.of k)}
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z} (h : MMP.Flips.IsSmall k sZ sX f) :
    IsBirationalMorphism f ∧ ∀ F : MMP.Mori.PrimeDivisor X,
      ∃ Q : MMP.Mori.PrimeDivisor Z, f F.genericPoint = Q.genericPoint := by
  obtain ⟨-, V, W, hV, hW, hle, hiso⟩ := h
  refine ⟨MMP.Flips.isBirationalMorphism_of_isIso_resLE f V.compl W.compl
    (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension V hV)
    (MMP.Flips.nonempty_compl_of_two_le_closedsCodimension W hW) hle hiso, fun F => ?_⟩
  have hFV : F.genericPoint ∈ (V.compl : X.Opens) := by
    intro hmem
    have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV) _ hmem
    rw [F.coheight_genericPoint] at this
    exact absurd this (by decide)
  have hopen : IsOpenImmersion (Scheme.Opens.ι (X := X) V.compl ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f hle]; infer_instance
  have hcoh : Order.coheight (f F.genericPoint) = 1 := by
    have h1 := coheight_eq_of_isOpenImmersion (Scheme.Opens.ι (X := X) V.compl ≫ f)
      (x := (⟨F.genericPoint, hFV⟩ : Scheme.Opens.toScheme (X := X) V.compl))
    have h2 := coheight_eq_of_isOpenImmersion (Scheme.Opens.ι (X := X) V.compl)
      (x := (⟨F.genericPoint, hFV⟩ : Scheme.Opens.toScheme (X := X) V.compl))
    change Order.coheight (f F.genericPoint) = _ at h1
    change Order.coheight F.genericPoint = _ at h2
    rw [h1, ← h2, F.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩

/-- **The data of a step of a program.** The `i`-th step `X_i → Z_i ← X_{i+1}` of a relative
elementary dlt program consists of proper birational morphisms onto a normal variety `Z_i` over
`S`, with `φ_i : X_i ⤏ X_{i+1}` a map over `Z_i`, and every prime divisor of `X_{i+1}` lies over a
prime divisor of `Z_i` (for a divisorial step `X_{i+1} ≅ Z_i`; for a flip, `f⁺` is small). -/
private theorem exists_step {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)}
    {π : X ⟶ S} {K : Divisor X} {B : QDivisor X} (P : RelativeDltProgram sX sS π K B) (i : ℕ)
    (hi : (i : ℕ∞) < P.n) :
    ∃ (_ : IsIntegral (P.Z i)) (_ : IsLocallyNoetherian (P.Z i)),
      IsNormalVariety ℂ (P.sZ i) ∧ IsProper (P.f i) ∧ IsProper (P.fp i) ∧
      MMP.Mori.IsVariety ℂ (P.f i ≫ P.sZ i) ∧ MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) ∧
      IsBirationalMorphism (P.f i) ∧ IsBirationalMorphism (P.fp i) ∧
      P.f i ≫ P.gZ i = modelMap π P.πY i ∧ P.fp i ≫ P.gZ i = P.πY i ∧
      (P.φ i).compHom (P.fp i) = (P.f i).toRationalMap ∧
      ∀ F' : MMP.Mori.PrimeDivisor (P.Y i), ∃ Q : MMP.Mori.PrimeDivisor (P.Z i),
        P.fp i F'.genericPoint = Q.genericPoint := by
  have hstep := P.isElementaryDltStep i hi
  have hctr := hstep.isNegativeRelativeRayContraction.isNegativeExtremalContraction
  have hZ : IsNormalVariety ℂ (P.sZ i) := hctr.isNormalVariety_target
  have hcon := hctr.isContraction
  haveI : IsIntegral (P.Z i) := hZ.1.toIsIntegral
  haveI : LocallyOfFiniteType (P.sZ i) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (P.Z i) := LocallyOfFiniteType.isLocallyNoetherian (P.sZ i)
  haveI : IsSeparated (P.sZ i) := hZ.1.toIsSeparated
  haveI : QuasiCompact (P.sZ i) := hZ.1.toQuasiCompact
  have hf : IsProper (P.f i) := hcon.isProper
  have hfv : MMP.Mori.IsVariety ℂ (P.f i ≫ P.sZ i) := hcon.comp_eq ▸ hcon.isVariety_source
  have hfg := hstep.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
  rcases hstep.divisorial_or_flip with ⟨hfb, -, hiso, hmod⟩ | hflip
  · have hfpv : MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) :=
      { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
        toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
    refine ⟨inferInstance, inferInstance, hZ, hf, inferInstance, hfv, hfpv, hfb,
      isBirationalMorphism_of_isIso _, hfg, hstep.comp_eq, hmod.2, fun F' => ?_⟩
    have hcoh : Order.coheight (P.fp i F'.genericPoint) = 1 := by
      rw [coheight_eq_of_isOpenImmersion (P.fp i), F'.coheight_genericPoint]
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm⟩
  · obtain ⟨hfb, -⟩ := isBirationalMorphism_and_exists_of_isSmall hflip.isSmall_source
    obtain ⟨hfpb, hQ⟩ := isBirationalMorphism_and_exists_of_isSmall hflip.isSmall
    have hfpv : MMP.Mori.IsVariety ℂ (P.fp i ≫ P.sZ i) :=
      hflip.isSmall.comp_eq ▸ hflip.isSmall.isVariety_source
    exact ⟨inferInstance, inferInstance, hZ, hf, hflip.isProper, hfv, hfpv, hfb, hfpb, hfg,
      hstep.comp_eq, hflip.isModificationOf.2, hQ⟩

/-- **The models of a program over `S`.** Let `P` be a relative elementary dlt program over `S`
starting from a birational morphism `p : Y ⟶ S`. Every model `π_i : X_i ⟶ S`, `i ≤ n`, is
birational, and every prime divisor `F'` of `X_i` is the transform of a prime divisor `F` of `Y`:
they define the same valuation of `k(S)`, and `coeff_{F'} B_i = coeff_F B_0`. -/
private theorem isBirationalMorphism_and_exists_primeDivisor {S Y : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] {sS : S ⟶ Spec (.of ℂ)} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (p : Y ⟶ S) {KY : Divisor Y} {Γ : QDivisor Y}
    (hbir : IsBirationalMorphism p) (hYn : IsNormalVariety ℂ (p ≫ sS))
    (P : RelativeDltProgram (p ≫ sS) sS p KY Γ) :
    ∀ i : ℕ, (i : ℕ∞) ≤ P.n → ∃ hbi : IsBirationalMorphism (modelMap p P.πY i),
      ∀ (hni : IsNormalVariety ℂ (modelMap p P.πY i ≫ sS))
        (F' : MMP.Mori.PrimeDivisor (modelSeq Y P.Y i)), ∃ F : MMP.Mori.PrimeDivisor Y,
        (⟨_, modelMap p P.πY i, hni, hbi, F'⟩ : DivisorOver ℂ sS).valuation =
          (⟨Y, p, hYn, hbir, F⟩ : DivisorOver ℂ sS).valuation ∧
        (divisorSeq Γ P.BY i).coeff F' = Γ.coeff F := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨hbir, fun hni F' => ⟨F', rfl, rfl⟩⟩
  | succ i ih =>
    intro hi
    have hi' : (i : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self i) hi
    obtain ⟨hbi, hti⟩ := ih hi'.le
    obtain ⟨_, _, hZ, hf, hfp, hfv, hfpv, hfb, hfpb, hfg, hfpg, hφ, hQ⟩ := exists_step P i hi'
    have hmi := P.isRelativeDltModel i hi'.le
    have hmi1 := P.isRelativeDltModel (i + 1) hi
    have : IsProper (P.πY i) := isProper_of_isProjectiveMorphism _ hmi1.isProjectiveMorphism
    -- the next model is birational over `S`
    have hBi := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hbi
    have hBf := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb
    have hBfp := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfpb
    have hBg : IsBirational (P.gZ i) := isBirational_of_comp hBf (hfg ▸ hBi)
    have hB' : IsBirational (P.πY i) := hfpg ▸ hBfp.comp hBg
    have hbi' : IsBirationalMorphism (P.πY i) := by
      have := isBirationalMorphism_comp_of_isBirational (P.πY i) (𝟙 _) hB'
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          (isBirationalMorphism_of_isIso _))
      simpa using this
    refine ⟨hbi', fun hni F' => ?_⟩
    obtain ⟨Q, hQF⟩ := hQ F'
    obtain ⟨F, V₀, hV, hfV, hfpV, hfF, hcoeff⟩ := exists_primeDivisor_of_isOver hZ (P.f i)
      (P.fp i) hfv hfpv hfb hfpb (P.φ i) hφ F' Q hQF
    have hni_i : IsNormalVariety ℂ (modelMap p P.πY i ≫ sS) :=
      hmi.comp_eq ▸ hmi.isQFactorial.1
    obtain ⟨F₀, hv0, hc0⟩ := hti hni_i F
    refine ⟨F₀, ?_, ?_⟩
    · exact (valuation_eq_of_isIso_morphismRestrict (P.f i) (P.fp i) (P.gZ i) hfg hfpg hni_i hni
        hbi hbi' V₀ F F' (hfF ▸ hV) (hQF.trans hfF.symm)).trans hv0
    · change (P.BY i).coeff F' = _
      rw [P.BY_eq i hi', hcoeff, hc0]

/-- A birational proper morphism `π : U ⟶ S` onto a normal variety does not factor through a
scheme `T` of smaller dimension: over the open subset of `S` where `π` is an isomorphism,
`U ⟶ T` is a topological embedding, so `dim U ≤ dim T`. -/
private theorem topologicalKrullDim_le_of_comp_eq {U T S : Scheme.{0}} [IsIntegral U]
    [IsIntegral S] [IsLocallyNoetherian S] {sS : S ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sS)
    {πU : U ⟶ S} [IsProper πU] (hUv : MMP.Mori.IsVariety ℂ (πU ≫ sS))
    (hb : IsBirationalMorphism πU) (g : U ⟶ T) (gT : T ⟶ S) (h : g ≫ gT = πU) :
    topologicalKrullDim U ≤ topologicalKrullDim T := by
  haveI : ValuationRing (S.presheaf.stalk (genericPoint S)) :=
    inferInstanceAs (ValuationRing S.functionField)
  have hA := mem_biregularLocus_of_valuationRing hX hUv hb (genericPoint S)
  have hiso : IsIso (πU ∣_ biregularLocus πU) := isBiregular_biregularLocus πU
  haveI : IsDominant πU := hb.isDominant
  set W : U.Opens := πU ⁻¹ᵁ biregularLocus πU
  have hWne : (W : Set U).Nonempty := ⟨genericPoint U, by
    change πU (genericPoint U) ∈ biregularLocus πU
    rw [map_genericPoint_of_isDominant]; exact hA⟩
  have hopen : IsOpenImmersion (W.ι ≫ πU) := by rw [← morphismRestrict_ι]; infer_instance
  have hind : Topology.IsInducing (W.ι ≫ g).base := by
    refine Topology.IsInducing.of_comp (W.ι ≫ g).base.hom.continuous gT.base.hom.continuous ?_
    have : (W.ι ≫ πU).base = (W.ι ≫ g).base ≫ gT.base := by
      rw [← h, ← Category.assoc, Scheme.Hom.comp_base]
    have h2 := (W.ι ≫ πU).isOpenEmbedding.isInducing
    rw [this] at h2
    exact h2
  haveI : AlgebraicGeometry.IsVariety ℂ (πU ≫ sS) := hUv
  rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ U (πU ≫ sS) _ W.isOpen hWne]
  exact hind.topologicalKrullDim_le

/-! ### The birational map to the last model -/

section BirationalMap

/-- Two morphisms `h₁ h₂ : T ⟶ Y` from a reduced irreducible scheme with `h₁ ≫ q = h₂ ≫ q` are
equal, if `q : Y ⟶ Z` is separated and an isomorphism over an open `V ⊆ Z` met by `h₁ ≫ q`. -/
private theorem eq_of_comp_eq_of_isIso_morphismRestrict {T Y Z : Scheme.{u}} [IsReduced T]
    [IrreducibleSpace T] (q : Y ⟶ Z) [IsSeparated q] (V : Z.Opens) [IsIso (q ∣_ V)]
    {h₁ h₂ : T ⟶ Y} (h : h₁ ≫ q = h₂ ≫ q) {t : T} (ht : (h₁ ≫ q) t ∈ V) : h₁ = h₂ := by
  set O : T.Opens := (h₁ ≫ q) ⁻¹ᵁ V
  haveI : IsDominant O.ι := Opens.isDominant_ι (O.2.dense ⟨t, ht⟩)
  refine ext_of_isDominant_of_isSeparated q h O.ι ?_
  have hr : ∀ g : T ⟶ Y, g ≫ q = h₁ ≫ q →
      Set.range (O.ι ≫ g) ⊆ Set.range (q ⁻¹ᵁ V).ι := by
    rintro g hg _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : ((O.ι ≫ g) ≫ q) x ∈ V := by
      rw [Category.assoc, hg, Scheme.Hom.comp_apply]
      exact x.2
    rwa [Scheme.Hom.comp_apply] at this
  have hmono : Mono ((q ⁻¹ᵁ V).ι ≫ q) := by
    rw [← morphismRestrict_ι]; infer_instance
  have e₁ := IsOpenImmersion.lift_fac _ _ (hr h₁ rfl)
  have e₂ := IsOpenImmersion.lift_fac _ _ (hr h₂ h.symm)
  rw [← e₁, ← e₂]
  congr 1
  refine (cancel_mono ((q ⁻¹ᵁ V).ι ≫ q)).mp ?_
  rw [← Category.assoc, e₁, ← Category.assoc, e₂, Category.assoc, Category.assoc, h]

/-- A partial map representing a rational map `φ : X ⤏ X'` over `Z` lies over `Z`. -/
private theorem hom_comp_eq_of_compHom_eq {X X' Z : Scheme.{u}} [IsReduced X]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (f : X ⟶ Z) (fp : X' ⟶ Z) (g : X.PartialMap X')
    (h : g.toRationalMap.compHom fp = f.toRationalMap) : g.hom ≫ fp = g.domain.ι ≫ f :=
  (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp (by
      rw [Scheme.RationalMap.compHom_toRationalMap]; exact h))

/-- The generic point of an irreducible scheme lies in every nonempty open subset. -/
private theorem genericPoint_mem {X : Scheme.{u}} [IrreducibleSpace X] (U : X.Opens)
    (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.2).mpr (by simpa using hU)

/-- **The birational map between two models over `Z`.** Let `p : W ⟶ Z` and `q : Y ⟶ Z` be
proper birational morphisms from normal varieties onto a normal variety. There is a birational
map `φ : W ⤏ Y` over `Z`; for prime divisors `D ⊆ W`, `Q ⊆ Y` defining the same valuation of
`k(Z)`, the transform of `D` is `Q`, and `D` is the only prime divisor whose transform is `Q`. -/
private theorem exists_isBirational_isOver_of_valuation_eq {W Y Z : Scheme.{0}}
    [IsIntegral W] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) (p : W ⟶ Z) (q : Y ⟶ Z)
    [IsProper p] [IsProper q] (hW : IsNormalVariety ℂ (p ≫ sZ))
    (hY : IsNormalVariety ℂ (q ≫ sZ)) (hp : IsBirationalMorphism p)
    (hq : IsBirationalMorphism q) :
    ∃ φ : W.RationalMap Y, MMP.Mori.RationalMap.IsBirational φ ∧
      MMP.Flips.RationalMap.IsOver p q φ ∧
      ∀ (D : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor Y),
        (⟨W, p, hW, hp, D⟩ : DivisorOver ℂ sZ).valuation =
            (⟨Y, q, hY, hq, Q⟩ : DivisorOver ℂ sZ).valuation →
          MMP.Mori.RationalMap.transformPrimeDivisor φ D = some Q ∧
            ∀ D', MMP.Mori.RationalMap.transformPrimeDivisor φ D' = some Q → D' = D := by
  classical
  haveI : IsNormal Z := hZ.2
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  have hsepZ : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_terminal_of_isVariety hZ.1
  have hsepY : IsSeparated (Y ↘ ⊤_ Scheme) := isSeparated_terminal_of_isVariety hY.1
  haveI : ValuationRing (Z.presheaf.stalk (genericPoint Z)) :=
    inferInstanceAs (ValuationRing Z.functionField)
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant q := hq.isDominant
  set V : Z.Opens := biregularLocus p ⊓ biregularLocus q
  have hηV : genericPoint Z ∈ V :=
    ⟨mem_biregularLocus_of_valuationRing hZ hW.1 hp _,
      mem_biregularLocus_of_valuationRing hZ hY.1 hq _⟩
  haveI hpV : IsIso (p ∣_ V) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI hqV : IsIso (q ∣_ V) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have hpη : p (genericPoint W) ∈ V := by rw [map_genericPoint_of_isDominant]; exact hηV
  have hqη : q (genericPoint Y) ∈ V := by rw [map_genericPoint_of_isDominant]; exact hηV
  let e₀ : W.PartialIso Y :=
    { source := p ⁻¹ᵁ V
      dense_source := (p ⁻¹ᵁ V).2.dense ⟨_, hpη⟩
      target := q ⁻¹ᵁ V
      dense_target := (q ⁻¹ᵁ V).2.dense ⟨_, hqη⟩
      iso := asIso (p ∣_ V) ≪≫ (asIso (q ∣_ V)).symm }
  have he₀ : e₀.iso.hom ≫ e₀.target.ι ≫ q = e₀.source.ι ≫ p := by
    change (p ∣_ V) ≫ inv (q ∣_ V) ≫ (q ⁻¹ᵁ V).ι ≫ q = (p ⁻¹ᵁ V).ι ≫ p
    rw [← morphismRestrict_ι, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  -- every partial map over `Z` represents `e₀`
  have hrep : ∀ g : W.PartialMap Y, g.hom ≫ q = g.domain.ι ≫ p →
      g.toRationalMap = e₀.toRationalMap := by
    intro g hg
    set O : W.Opens := g.domain ⊓ e₀.source
    have hO : Dense (O : Set W) := g.dense_domain.inter_of_isOpen_left e₀.dense_source g.domain.2
    have hηO : genericPoint W ∈ O := genericPoint_mem O hO.nonempty
    haveI : Nonempty O := ⟨⟨_, hηO⟩⟩
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨O, hO, inf_le_left, inf_le_right, ?_⟩
    change W.homOfLE inf_le_left ≫ g.hom = W.homOfLE inf_le_right ≫ e₀.iso.hom ≫ e₀.target.ι
    have hc : (W.homOfLE inf_le_left ≫ g.hom) ≫ q =
        (W.homOfLE inf_le_right ≫ e₀.iso.hom ≫ e₀.target.ι) ≫ q := by
      simp only [Category.assoc, hg, he₀, Scheme.homOfLE_ι_assoc]
    refine eq_of_comp_eq_of_isIso_morphismRestrict q V hc (t := ⟨_, hηO⟩) ?_
    rw [Category.assoc, hg, Scheme.homOfLE_ι_assoc]
    exact hpη
  have hover : MMP.Flips.RationalMap.IsOver p q e₀.toRationalMap := by
    change e₀.toRationalMap.compHom q = p.toPartialMap.toRationalMap
    rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap]
    refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mpr ?_)
    change (e₀.iso.hom ≫ e₀.target.ι) ≫ q = e₀.source.ι ≫ p
    rw [Category.assoc, he₀]
  refine ⟨e₀.toRationalMap, ⟨e₀, rfl⟩, hover, fun D Q hv => ?_⟩
  obtain ⟨U, V', hU, hV', e, h1, h2⟩ :=
    MMP.Positivity.DivisorOver.exists_iso_of_valuation_eq hZ.1 _ _ hv
  change D.genericPoint ∈ U at hU
  change Q.genericPoint ∈ V' at hV'
  change e.hom ≫ V'.ι ≫ q = U.ι ≫ p at h1
  change e.hom ⟨D.genericPoint, hU⟩ = ⟨Q.genericPoint, hV'⟩ at h2
  let g' : W.PartialMap Y := ⟨U, U.2.dense ⟨_, hU⟩, e.hom ≫ V'.ι⟩
  have hg' : g'.toRationalMap = e₀.toRationalMap :=
    hrep g' (by change (e.hom ≫ V'.ι) ≫ q = U.ι ≫ p; rw [Category.assoc, h1])
  have hDQ : MMP.Mori.RationalMap.transformPrimeDivisor e₀.toRationalMap D = some Q := by
    refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hU ?_
    change Q.genericPoint = V'.ι (e.hom ⟨D.genericPoint, hU⟩)
    rw [h2]; rfl
  refine ⟨hDQ, fun D' hD'Q => ?_⟩
  obtain ⟨g, hD', hg⟩ := MMP.Mori.RationalMap.definedAt_iff.mp
    (MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hD'Q).1
  have hgQ : Q.genericPoint = g.hom ⟨D'.genericPoint, hD'⟩ :=
    MMP.Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hD'Q g hg hD'
  have hgover : g.hom ≫ q = g.domain.ι ≫ p := hom_comp_eq_of_compHom_eq p q g (by rw [hg]; exact hover)
  set O : g.domain.toScheme.Opens := g.hom ⁻¹ᵁ V'
  have hoO : (⟨D'.genericPoint, hD'⟩ : g.domain.toScheme) ∈ O := by
    change g.hom _ ∈ V'
    rw [← hgQ]; exact hV'
  let o : O.toScheme := ⟨_, hoO⟩
  haveI : Nonempty g.domain.toScheme := ⟨⟨_, hD'⟩⟩
  haveI : Nonempty O.toScheme := ⟨o⟩
  haveI : IsDominant (O.ι ≫ g.domain.ι) := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion _
  have hcomp : ((g.hom ∣_ V') ≫ e.inv ≫ U.ι) ≫ p = (O.ι ≫ g.domain.ι) ≫ p := by
    have h1' : e.inv ≫ U.ι ≫ p = V'.ι ≫ q := by
      rw [← h1, Iso.inv_hom_id_assoc]
    rw [Category.assoc, Category.assoc, h1', ← Category.assoc, morphismRestrict_ι,
      Category.assoc, hgover, Category.assoc]
  have heq := eq_of_comp_eq_of_isIso_morphismRestrict p V hcomp (t := genericPoint O.toScheme)
    (by
      rw [hcomp, Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
      exact hpη)
  have hval := congrArg (fun k : O.toScheme ⟶ W => k o) heq
  have hrest : (g.hom ∣_ V') o = ⟨Q.genericPoint, hV'⟩ := by
    apply Subtype.ext
    have := congrArg (fun k : O.toScheme ⟶ Y => k o) (morphismRestrict_ι g.hom V')
    change V'.ι ((g.hom ∣_ V') o) = g.hom (O.ι o) at this
    exact this.trans hgQ.symm
  have hinv : e.inv ⟨Q.genericPoint, hV'⟩ = ⟨D.genericPoint, hU⟩ := by
    rw [← h2]
    change (e.hom ≫ e.inv) _ = _
    rw [Iso.hom_inv_id]; rfl
  change U.ι (e.inv ((g.hom ∣_ V') o)) = g.domain.ι (O.ι o) at hval
  rw [hrest, hinv] at hval
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective hval.symm

end BirationalMap

section Main

attribute [local instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **The rational birational program property `Q(3)`.** -/
private theorem solution : MMP.Fourfold.RationalBirationalProgramProperty 3 := by
  classical
  refine ⟨by norm_num, ?_⟩
  intro W _ _ _ _ sW Z sZ p hWp hWn hWsm hWd hZp hZn hZd hpZ hpproj hpbir K hK C hC hsnc
  subst hpZ
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsNormal Z := hZn.2
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : QuasiCompact (p ≫ sZ) := hWn.1.toQuasiCompact
  haveI : LocallyOfFiniteType (p ≫ sZ) := hWn.1.toLocallyOfFiniteType
  have : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  -- the smooth snc pair `(W, C)` is `ℚ`-factorial and dlt
  have hQW : IsQFactorial (p ≫ sZ) := ⟨hWn, fun D => ⟨1, one_pos, by
    simpa using MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hWsm D⟩⟩
  have hdltM : MMP.Mori.IsDltPair (p ≫ sZ) 3 K C := by
    refine ⟨⟨hWn, hK, MMP.Fourfold.isQCartier_of_isQFactorial _ hQW _⟩,
      fun P => ⟨(hC P).1, (hC P).2.le⟩, ⊤, hWsm.ge, isSNC_restrictOpen (p ≫ sZ) hsnc ⊤, ?_⟩
    intro D a hD _
    exfalso
    obtain ⟨x, hx⟩ := D.center.isIrreducible.nonempty
    exact hD hx (by simp)
  have hdlt : MMP.Intersection.IsDltPair (p ≫ sZ) C :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair (p ≫ sZ) hK C).mpr hdltM
  -- the threefold log minimal model program over `Z`
  obtain ⟨-, -, P, hPproj, hPn, hPend⟩ := MMP.Fourfold.projectiveLowerLogMMP_three.2 W Z
    (p ≫ sZ) sZ p K C hWp hZp rfl hWd.le hQW ⟨3, hK⟩ hdlt
  set m := P.n.toNat with hmdef
  have hm : (m : ℕ∞) ≤ P.n := ENat.coe_toNat_le_self _
  have hmod := P.isRelativeDltModel m hm
  set U := modelSeq W P.Y m
  set πU : U ⟶ Z := modelMap p P.πY m with hπUdef
  have hcomp : πU ≫ sZ = modelStr (p ≫ sZ) P.sY m := hmod.comp_eq
  have hQU : IsQFactorial (πU ≫ sZ) := hcomp ▸ hmod.isQFactorial
  have hUnv : IsNormalVariety ℂ (πU ≫ sZ) := hQU.1
  have hprojU : IsProjectiveMorphism πU := hmod.isProjectiveMorphism
  have : IsProper πU := isProper_of_isProjectiveMorphism πU hprojU
  haveI : QuasiCompact (modelStr (p ≫ sZ) P.sY m) := hmod.isQFactorial.1.1.toQuasiCompact
  -- every model is birational over `Z`, and its prime divisors come from `W`
  obtain ⟨hbirU, htrack0⟩ := isBirationalMorphism_and_exists_primeDivisor p hpbir hWn P m hm
  have htrack := htrack0 hUnv
  -- no fibre-type contraction over the base `Z`
  have hnotFinal : ¬ P.hasFinal := by
    intro hfin
    obtain ⟨-, hctr, hlt⟩ := P.final_spec hfin
    have hle := topologicalKrullDim_le_of_comp_eq hZn hUnv.1 hbirU P.g P.gT
      hctr.isRelativeContractionOfFace.comp_eq
    exact absurd hlt (not_lt.mpr hle)
  obtain ⟨φ, hφb, hφo, hφ⟩ :=
    exists_isBirational_isOver_of_valuation_eq hZn p πU hWn hUnv hpbir hbirU
  refine ⟨P, hPn, hPproj, hnotFinal, hmod.isQFactorial, hPproj.2 m hm, hprojU, ?_, ?_, φ, hφb,
    hφo, ?_, ?_⟩
  · -- the boundary coefficients stay below one, so the dlt pair is klt
    refine MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one hmod.isDltPair fun F' => ?_
    obtain ⟨F, -, hc⟩ := htrack F'
    rw [hc]; exact (hC F).2
  · exact isRelativelyNef_of_isRelativelyNef_toRDivisor
      (MMP.Fourfold.isQCartier_of_isQFactorial _ hmod.isQFactorial _)
      (hPend.resolve_right hnotFinal)
  · refine DivisorWithCoeffs.ext' fun Q => ?_
    obtain ⟨F, hv, hc⟩ := htrack Q
    obtain ⟨hFQ, huniq⟩ := hφ F Q hv.symm
    rw [hc]
    exact (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hFQ huniq C).symm
  · intro Q
    obtain ⟨F, hv, -⟩ := htrack Q
    exact ⟨F, (hφ F Q hv.symm).1⟩

end Main

end Proof_thm_fourfold_rational_birational_program_q3

end

namespace MMP.Fourfold

/-- **The rational birational program property in dimension three.** The property
`RationalBirationalProgramProperty 3` holds: every projective birational morphism of normal
projective complex threefolds from a smooth threefold with an effective snc `ℚ`-boundary of
coefficients less than one admits a finite projective negative program over the base ending at a
`ℚ`-factorial klt model with relatively nef adjoint, whose boundary is the push-forward and which
extracts no prime divisor. -/
@[mmp "thm_fourfold_rational_birational_program_q3"]
public theorem rationalBirationalProgramProperty_three : RationalBirationalProgramProperty 3 :=
  by first | exact Proof_thm_fourfold_rational_birational_program_q3.solution | exact Proof_thm_fourfold_rational_birational_program_q3.solution _ | exact Proof_thm_fourfold_rational_birational_program_q3.solution _ _ | exact Proof_thm_fourfold_rational_birational_program_q3.solution _ _ _ | exact Proof_thm_fourfold_rational_birational_program_q3.solution _ _ _ _

end MMP.Fourfold
