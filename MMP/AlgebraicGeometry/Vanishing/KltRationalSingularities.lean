module

public import Mathlib
public import MMP.Attr
import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.QuasiCompact
import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.Untwisting
import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.OpenSubscheme
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologyBridge
import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepOpen
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
public import MMP.AlgebraicGeometry.Cohomology.Duality.SmoothSerreDuality
import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
import MMP.AlgebraicGeometry.Intersection.Nef
import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Curves.Maps.CoefficientSpace
import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.StrongResolutionCharZero
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.SpreadingOut.CountableFieldOfDefinition
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.Arithmetic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Divisor.Canonical.Basic
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesChartRatio
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpaceChangeModule
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBaseFull
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimTwoInvertibleClass
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.IntegralDivisorPicardGeneration
public import StacksFrontier.AlgebraicGeometry.FiberRank.FreeLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.Limit
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.GenericFibreRankLocallyConstant
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.ChangeOfSpaces
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.ResolutionSpreadOutProjective
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LerayShortExactSequenceDimTwo
public import StacksFrontier.AlgebraicGeometry.SheafComplexGlue.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceAlgebra
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RationalPoint
public import StacksFrontier.AlgebraicGeometry.VeryAmplePowersQuasiCompactBase.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch
public import StacksFrontier.AlgebraicGeometry.GlobalSectionsOverField.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImageRingedSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionFromCechVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityFromCechVanishing
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ConnectedLocal
public import StacksFrontier.AlgebraicGeometry.NilradicalNilpotent.Basic
public import StacksFrontier.AlgebraicGeometry.PicardUFD.ProjectiveSpaceCocycle
public import StacksFrontier.Homology.DerivedIndexing.ZeroUnitSingle
public import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.StalkHomotopy
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
public import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxDevissage
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.BaseChange
public import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
public import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeCartier
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.CyclicCover.Algebra
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.ProjectiveLogResolution
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.Morphisms.ValuativeCentre
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedBiduality
import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.SchemeCoherentDerivedHom
import MMP.AlgebraicGeometry.Resolution.Principalization.ResolutionPrincipalization
import MMP.AlgebraicGeometry.Resolution.DivisorTuple.TransformationSequence
import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.GradedNaturality
import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.FreeTower.ProjMapTwist
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryKlt
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.Morphisms.Birational.RationalMap
public import MMP.AlgebraicGeometry.Positivity.CartierTwistEulerPolynomial
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedApplicationRightUnitLawOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Uniqueness
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardSingleUnit
import MMP.AlgebraicGeometry.Cohomology.Duality.BirationalTrace
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Divisor.DivisorialSheaf
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Vanishing.RelativeKawamataViehweg
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic
import MMP.AlgebraicGeometry.Singularities.LogResolution.RoundUpPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Modules.ProjectionFormulaInvertible
import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Positivity.AsymptoticAdjointIdeal
public import MMP.AlgebraicGeometry.Divisor.CartierDivisorSheafMul

/-!
# Kawamata–Viehweg vanishing over smooth snc pairs and rational singularities of klt pairs

For a smooth variety `Y` over an algebraically closed field of characteristic zero, an effective
snc `ℚ`-divisor `B` with coefficients `< 1` and a Cartier divisor `L`, this file proves the
relative vanishing `R^i f_* 𝒪_Y(L) = 0` (`i > 0`) when `L - (K_Y + B)` is `f`-ample, then when it
is `f`-nef and `f`-big for a projective and finally for a proper `f`. It then proves the split-unit
criterion for rationality of a projective resolution and deduces that a projective klt pair has
rational singularities along every projective log resolution: `𝒪_X ⟶ Rf_* 𝒪_Y` is an isomorphism.

## Main results

In the namespace `MMP.Mori`:

* `isZero_rightDerived_pushforward_divisorialSheaf_of_hasRelativelyAmpleMultiple`: the vanishing
  `R^i f_* 𝒪_Y(L) = 0` for `i > 0` when `f` is projective and `L - (K_Y + B)` is `f`-ample.
* `isZero_rightDerived_pushforward_divisorialSheaf_of_isRelativelyNef_of_isRelativelyBig`: the
  same vanishing when `f` is projective and `L - (K_Y + B)` is `f`-nef and `f`-big.
* the same vanishing when `f` is proper and `L - (K_Y + B)` is `f`-nef and `f`-big:
`isZero_rightDerived_pushforward_divisorialSheaf_of_isProper_of_isRelativelyNef_of_isRelativelyBig`

In the namespace `MMP.Duality`:

* `isIso_unit_of_isSplitMono`: for a projective birational morphism `f : Y ⟶ X` of normal
  projective varieties with `Y` smooth, if the unit `𝒪_X ⟶ Rf_* 𝒪_Y` has a left inverse, then it
  is an isomorphism and `R^i f_* 𝒪_Y = 0` for `i > 0`.
* `isIso_unit_of_isKltPair_of_isLogResolution`: for a projective klt pair and a projective log
  resolution `f`, the unit `𝒪_X ⟶ Rf_* 𝒪_Y` is an isomorphism.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KM98], Theorems 2.64, 5.10,
  5.22
-/

@[expose] public section

universe u

/-! ### `lem_mmp_relative_snc_ample_gap_vanishing` -/

section

namespace Proof_lem_mmp_relative_snc_ample_gap_vanishing

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules Stacks.Cohomology.TwistedGradedModule

section Endgame

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- **Cohomology of the nonvanishing open from vanishing of all twists.** Let `X` be a
quasi-compact quasi-separated scheme, `ℒ` an invertible module, `s ∈ Γ(X, ℒ)` and `𝒢` a
quasi-coherent module with `Hⁿ(X, 𝒢 ⊗ ℒ^{⊗ k}) = 0` for every `k ≥ 0`. Then `Hⁿ(X_s, 𝒢) = 0`:
a class `η` on `X_s` has some `sᵏ η` extending to `X` ([Stacks, Tag 09MR]), hence `sᵏ η = 0`,
and multiplication by `sᵏ` is injective on the cohomology of `X_s`. -/
private theorem isZero_hgroup_nonvanishingOpen {X : Scheme.{0}} [QuasiSeparatedSpace X] [CompactSpace X]
    (L : SheafOfModules.{0} (structureSheafRing X.toRingedSpace))
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    (s : L.sections) (G : X.Modules) [G.IsQuasicoherent] (n : ℕ)
    (h : ∀ k : ℕ, IsZero (Hgroup X.ringCatSheaf ⊤ n (twist X L G (k : ℤ)))) :
    IsZero (Hgroup X.ringCatSheaf (nonvanishingOpen L s) n G) := by
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  refine subsingleton_of_forall_eq 0 fun η => ?_
  obtain ⟨-, hext⟩ := SectionPowerAnnihilation.annihilates_and_extends_of_isCompact s ⊤
    isCompact_univ n
  obtain ⟨k, ξ, hξ⟩ := hext (nonvanishingOpen L s) le_top (top_inf_eq _).symm G inferInstance η
  have hξ0 : ξ = 0 := (AddCommGrpCat.isZero_iff_subsingleton.mp (h k)).elim _ _
  rw [hξ0, map_zero] at hξ
  have hiso := Untwisting.isIso_hfunctor_map_sectionPowerAction X L s G k
    (nonvanishingOpen L s) le_rfl n
  have hinj : Function.Injective (ConcreteCategory.hom ((Hfunctor X.ringCatSheaf
      (nonvanishingOpen L s) n).map (SectionPowerComposition.mul X L s G k))) :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj (hξ.symm.trans (map_zero _).symm)

end Endgame

section Main

open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

private theorem roundUp_toQDivisor_add {X : Scheme.{0}} (D : Divisor X) (Δ : QDivisor X) :
    (Divisor.toQDivisor D + Δ).roundUp = D + Δ.roundUp := by
  ext E
  change (Divisor.toQDivisor D + Δ).roundUp.coeff E = D.coeff E + Δ.roundUp.coeff E
  rw [DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_roundUp,
    DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, Int.ceil_intCast_add]

/-- The prime divisor of `X` whose generic point is the image of the generic point of a prime
divisor of `W`, for an open immersion `u : W ⟶ X`. -/
private def openPrimeDivisor {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u] (P : MMP.Mori.PrimeDivisor W) :
    MMP.Mori.PrimeDivisor X :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (u P.genericPoint)
    ((coheight_eq_of_isOpenImmersion u).trans P.coheight_genericPoint)

private theorem genericPoint_openPrimeDivisor {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u]
    (P : MMP.Mori.PrimeDivisor W) : (openPrimeDivisor u P).genericPoint = u P.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- On a smooth variety a canonical divisor `K` of dimension `n` has `𝒪_X(K) ≅ ⋀ⁿ Ω_{X/k}`:
the defining isomorphism lives on the smooth locus, which is all of `X`. -/
private theorem nonempty_divisorialSheaf_iso_exteriorPower {k : Type} [Field k] {X : Scheme.{0}}
    {f : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor f n) :
    Nonempty (K.divisorialSheaf ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f) n) :=
  MMP.Flips.nonempty_iso_of_restrict_iso hsm (hK.iso ≪≫
    ((Scheme.Modules.restrictFunctorIsoPullback (smoothLocus f).ι).app _ ≪≫
      Scheme.Modules.exteriorPowerPullbackIso (smoothLocus f).ι _ n ≪≫
      (Scheme.Modules.exteriorPowerFunctor _ n).mapIso
        (Scheme.Hom.etaleRelativeDifferentialsIso (smoothLocus f).ι f _ rfl)).symm)

/-- The pull-back of a canonical divisor of a smooth variety along an open immersion `ι` has
divisorial sheaf `⋀ⁿ Ω_{W/k}`. -/
private theorem nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback {k : Type} [Field k]
    {W X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (hsm : IsSmoothScheme sX)
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [CompactSpace W] (ι : W ⟶ X) [IsOpenImmersion ι] {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n)
    {hB : ∀ Z : irreducibleComponents W, ι (componentGenericPoint W Z) ∉ K.supp}
    {K' : Divisor W} (h : K.IsPullback ι hB K') :
    Nonempty (K'.divisorialSheaf ≅
      Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials (ι ≫ sX)) n) := by
  have hKc : K.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm K
  obtain ⟨e⟩ := nonempty_divisorialSheaf_iso_exteriorPower hsm hK
  exact ⟨(Divisor.IsPullback.divisorialSheafIso (hBc := hKc) h) ≪≫
    (Scheme.Modules.pullback ι).mapIso e ≪≫
    Scheme.Modules.exteriorPowerPullbackIso ι _ n ≪≫
    (Scheme.Modules.exteriorPowerFunctor _ n).mapIso
      (Scheme.Hom.etaleRelativeDifferentialsIso ι sX _ rfl)⟩

/-- The coefficients of the pull-back of a Cartier divisor along an open immersion are those of
the corresponding prime divisors. -/
private theorem coeff_of_isPullback_of_isOpenImmersion {W X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian W] [IsNormal W] (ι : W ⟶ X) [IsOpenImmersion ι]
    {D : Divisor X} (hDc : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents W, ι (componentGenericPoint W Z) ∉ D.supp}
    {D' : Divisor W} (h : D.IsPullback ι hB D') (P : MMP.Mori.PrimeDivisor W) :
    D'.coeff P = D.coeff (openPrimeDivisor ι P) :=
  MMP.Positivity.coeff_eq_of_isPullback P _ (genericPoint_openPrimeDivisor ι P).symm hDc h

private theorem openPrimeDivisor_injective {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u] :
    Function.Injective (openPrimeDivisor u) := fun P Q h =>
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective (u.isOpenEmbedding.injective (by
    rw [← genericPoint_openPrimeDivisor, h, genericPoint_openPrimeDivisor]))

private theorem openPrimeDivisor_eq_primeDivisorMap {W X : Scheme.{0}} (u : W ⟶ X) [IsOpenImmersion u]
    (P : MMP.Mori.PrimeDivisor W) :
    openPrimeDivisor u P = OpenWeilRestriction.primeDivisorMap u P :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_injective ((genericPoint_openPrimeDivisor u P).trans
    (OpenWeilRestriction.genericPoint_primeDivisorMap u P).symm)

/-- **Prime divisors through the complement of a support.** If an open immersion `ι : W ⟶ X` has
image `X ∖ Supp E`, then `E` has coefficient zero along the closure of every prime divisor of
`W`. -/
private theorem coeff_openPrimeDivisor_eq_zero {W X : Scheme.{0}} (ι : W ⟶ X) [IsOpenImmersion ι]
    {E : Divisor X} (h : Set.range ι = (E.supp : Set X)ᶜ) (P : MMP.Mori.PrimeDivisor W) :
    E.coeff (openPrimeDivisor ι P) = 0 := by
  by_contra hne
  have hmem : (openPrimeDivisor ι P).genericPoint ∈ (E.supp : Set X) :=
    DivisorWithCoeffs.support_subset_supp hne (by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl)
  rw [genericPoint_openPrimeDivisor, ← Set.notMem_compl_iff, ← h] at hmem
  exact hmem ⟨_, rfl⟩

/-- **Comparison of divisorial sheaves along two open immersions.** Let `ι : W ⟶ X` and
`j : W ⟶ X'` be open immersions into smooth varieties over `k` compatible with the structure
morphisms, `K`, `K'` canonical divisors and `D`, `D'` divisors with the same coefficient along
corresponding prime divisors. Then `ι^* 𝒪_X(K + D) ≅ j^* 𝒪_{X'}(K' + D')`. -/
private theorem nonempty_restrict_divisorialSheaf_iso {k : Type} [Field k]
    {W X X' : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral X'] [CompactSpace X] [CompactSpace X']
    [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [IsNormal X] [IsNormal X']
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    (hsm : IsSmoothScheme sX) (hsm' : IsSmoothScheme sX')
    (ι : W ⟶ X) [IsOpenImmersion ι] (j : W ⟶ X') [IsOpenImmersion j]
    (hιj : ι ≫ sX = j ≫ sX') {n : ℕ} {K : Divisor X} {K' : Divisor X'}
    (hK : K.IsCanonicalDivisor sX n) (hK' : K'.IsCanonicalDivisor sX' n)
    (D : Divisor X) (D' : Divisor X')
    (hD : ∀ P : MMP.Mori.PrimeDivisor W,
      D.coeff (openPrimeDivisor ι P) = D'.coeff (openPrimeDivisor j P)) :
    Nonempty ((K + D).divisorialSheaf.restrict ι ≅ (K' + D').divisorialSheaf.restrict j) := by
  haveI : IsDominant ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion ι
  haveI : IsDominant j := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion j
  have hc : ∀ G : Divisor X, G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  have hc' : ∀ G : Divisor X', G.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm'
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant ι
  have hB' := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant j
  obtain ⟨Kι, hKι⟩ := (hc K).exists_isPullback (hB K)
  obtain ⟨Dι, hDι⟩ := (hc D).exists_isPullback (hB D)
  obtain ⟨Kj, hKj⟩ := (hc' K').exists_isPullback (hB' K')
  obtain ⟨Dj, hDj⟩ := (hc' D').exists_isPullback (hB' D')
  have hDD : Dι = Dj := by
    ext P
    change Dι.coeff P = Dj.coeff P
    rw [coeff_of_isPullback_of_isOpenImmersion ι (hc D) hDι,
      coeff_of_isPullback_of_isOpenImmersion j (hc' D') hDj, hD P]
  subst hDD
  have hsum := Divisor.IsPullback.add (hc K) (hc D) (hB (K + D)) hKι hDι
  have hsum' := Divisor.IsPullback.add (hc' K') (hc' D') (hB' (K' + D')) hKj hDj
  have hKιc : Kι.IsCartier := hKι.isCartier (hc K)
  have hKjc : Kj.IsCartier := hKj.isCartier (hc' K')
  have hDc : Dι.IsCartier := hDι.isCartier (hc D)
  obtain ⟨eK⟩ := nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback hsm ι hK hKι
  obtain ⟨eK'⟩ := nonempty_divisorialSheaf_iso_exteriorPower_of_isPullback hsm' j hK' hKj
  rw [hιj] at eK
  have e₁ : (K + D).divisorialSheaf.restrict ι ≅ (Kι + Dι).divisorialSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback ι).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hc (K + D)) hsum).symm
  have e₂ : (K' + D').divisorialSheaf.restrict j ≅ (Kj + Dι).divisorialSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hc' (K' + D')) hsum').symm
  exact ⟨e₁ ≪≫ (hKιc.divisorialSheafTensorIso hDc).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso (eK ≪≫ eK'.symm)).app _ ≪≫
    hKjc.divisorialSheafTensorIso hDc ≪≫ e₂.symm⟩

/-- The tensor powers of `𝒪_X(E)` for a Cartier divisor `E`: `𝒪_X(E)^{⊗ k} ≅ 𝒪_X(kE)`. -/
private theorem nonempty_tensorPower_divisorialSheaf_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier) (k : ℕ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Nonempty (Stacks.SheafOfModules.TensorPower.tensorPower
      (Stacks.SheafOfModules.sectionSiteRing X) (Stacks.SheafOfModules.sectionSiteSheaf X)
      E.divisorialSheaf (k : ℤ) ≅ (k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  induction k with
  | zero =>
    exact ⟨eqToIso (Stacks.SheafOfModules.TensorPower.tensorPower_zero _ _ _) ≪≫
      Divisor.divisorialSheafZeroIso.symm ≪≫ eqToIso (by rw [zero_nsmul])⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [Nat.cast_succ]) ≪≫
      (Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso _ _ _ (k : ℤ)).symm ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app E.divisorialSheaf ≪≫
      (hE.nsmul k).divisorialSheafTensorIso hE ≪≫ eqToIso (by rw [succ_nsmul])⟩

/-- The tensor powers of `𝒪_X(E)` for a Cartier divisor `E`, in the spelling of
`Stacks.Ample.tensorPowModule`: `𝒪_X(E)^{⊗ k} ≅ 𝒪_X(kE)`. -/
private theorem nonempty_tensorPowModule_divisorialSheaf_iso {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier) (k : ℕ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Nonempty (Stacks.Ample.tensorPowModule X E.divisorialSheaf (k : ℤ) ≅
      (k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  induction k with
  | zero =>
    exact ⟨Stacks.Ample.tensorPowModuleZeroIso X _ ≪≫ Divisor.divisorialSheafZeroIso.symm ≪≫
      eqToIso (by rw [zero_nsmul])⟩
  | succ k ih =>
    obtain ⟨e⟩ := ih
    exact ⟨eqToIso (by rw [Nat.cast_succ]) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X _ (k : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e
        (Stacks.Ample.tensorPowModuleOneIso X _) ≪≫
      (hE.nsmul k).divisorialSheafTensorIso hE ≪≫ eqToIso (by rw [succ_nsmul])⟩

/-- **The twists of a divisorial sheaf by `𝒪(E)` are divisorial.** For Cartier divisors `D`,
`E` on a Noetherian normal scheme, `𝒪_X(D) ⊗ 𝒪_X(E)^{⊗ k} ≅ 𝒪_X(D + kE)`. -/
private theorem nonempty_twist_divisorialSheaf_iso {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {D E : Divisor X} (hD : D.IsCartier) (hE : E.IsCartier) (k : ℕ) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    Nonempty (twist X E.divisorialSheaf D.divisorialSheaf (k : ℤ) ≅
      (D + k • E).divisorialSheaf) := by
  haveI := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := nonempty_tensorPower_divisorialSheaf_iso hE k
  exact ⟨((Stacks.SheafOfModules.Tensor.sheafTensor _).obj D.divisorialSheaf).mapIso e ≪≫
    hD.divisorialSheafTensorIso (hE.nsmul k)⟩

/-- The nonvanishing open of the canonical section `1` of `𝒪_X(E)`, for `E ≥ 0` Cartier, is the
complement of the support of `E`. -/
private theorem nonvanishingOpen_divisorialSheafOneSection {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {E : Divisor X} (hE : E.IsCartier) (hE0 : 0 ≤ E) :
    haveI := hE.isInvertibleModule_divisorialSheaf
    ((Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) E.divisorialSheaf
      (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) E.divisorialSheaf
        (MMP.Threefold.Mori.oneSection hE0)) : X.Opens) : Set X) = (E.supp : Set X)ᶜ :=
  (Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop _ _).trans
    (MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 hE)

/-- **EGA-projective over an H-projective variety is H-projective.** Over a field every scheme
has an ample invertible sheaf on the base, so the two notions of projectivity agree there
(Stacks, Tag 0B45); a projective morphism `g` to an H-projective `Y` is therefore H-projective,
and so is `g ≫ s_Y`. -/
private theorem isProjectiveMorphism_of_isProjective {k : Type} [Field k] {X Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (hY : IsProjectiveMorphism sY) (g : X ⟶ Y) (hg : IsProjective g) :
    IsProjectiveMorphism (g ≫ sY) ∧ IsProjectiveMorphism g := by
  have hS : HasAmpleInvertibleSheaf (Spec (.of k)) :=
    (hasAmpleInvertibleSheaf_iff _).mpr (Stacks.HProjective.exists_isAmple_of_isAffine _)
  have hsY : IsProjective sY :=
    (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf sY hS).mpr hY
  have hc : IsProjective (g ≫ sY) := isProjective_comp_of_hasAmpleInvertibleSheaf g sY hS hsY hg
  have hcm := (isProjective_iff_isProjectiveMorphism_of_hasAmpleInvertibleSheaf _ hS).mp hc
  haveI : IsProper sY := isProper_of_isProjectiveMorphism sY hY
  exact ⟨hcm, IsProjectiveMorphism.of_comp g sY hcm⟩

/-- The preimage of a quasi-compact open under a quasi-compact morphism is quasi-compact. -/
private theorem compactSpace_preimage {Y Z : Scheme.{0}} (f : Y ⟶ Z) [QuasiCompact f]
    {V : Z.Opens} (hV : IsCompact (V : Set Z)) : CompactSpace (f ⁻¹ᵁ V) :=
  isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := f) _ V.isOpen hV)

/-- The `i`-th coordinate section of `𝒪(1)` on `ℙⁿ_A` does not vanish exactly on the `i`-th
standard chart `D₊(Tᵢ)`. -/
private theorem mem_nonvanishingLocus_coordSectionTop_iff {A : Type} [CommRing A] (n : ℕ)
    (i : Fin (n + 1)) (z : projectiveSpaceOver n (Spec (.of A))) :
    z ∈ Stacks.Ample.nonvanishingLocus
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of A)))
        (MMP.Fourfold.coordSectionTop (A := A) n i) ↔
      z ∈ projectiveSpaceOver.standardChart n (Spec (.of A)) i :=
  MMP.Fourfold.mem_nonvanishingLocus_pullbackCoordSection_iff
    (projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of A))) i z

/-- The data of a projective closure of an open `W ⊆ Y` adapted to a `ℚ`-divisor `B` on `Y`, in
continuation-passing style: a projective variety `Y₀ ⊇ W`, an invertible sheaf `H` on `Y₀` with a
section `t` whose nonvanishing locus is `W`, and a sequence `A_a ≅ A_0 ⊗ H^{⊗ a}` of invertible
sheaves on `Y₀`, ample for large `a`, with `A_0|_W ≅ 𝒪_Y(cB)|_W` for some `c > 0`. -/
private abbrev ProjectiveClosureData {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] (W : Y.Opens) (B : QDivisor Y) (C : Prop) : Prop :=
  ∀ (c : ℕ) (_ : 0 < c) (Lc : Divisor Y) (_ : Divisor.toQDivisor Lc = (c : ℚ) • B)
    (Y₀ : Scheme.{0}) (s₀ : Y₀ ⟶ Spec (.of k)) (_ : MMP.Mori.IsProjectiveVariety k s₀)
    (j : W.toScheme ⟶ Y₀) (_ : IsOpenImmersion j) (_ : j ≫ s₀ = W.ι ≫ sY)
    (Hb : Y₀.Modules) (_ : Stacks.Ample.IsInvertibleModule Y₀ Hb) (t : Γ(Hb, ⊤))
    (_ : Set.range j = Stacks.Ample.nonvanishingLocus Hb t)
    (A : ℕ → Y₀.Modules) (_ : ∀ a, Stacks.Ample.IsInvertibleModule Y₀ (A a)) (a₀ : ℕ)
    (_ : ∀ a, a₀ ≤ a → Stacks.Ample.IsAmple Y₀ (A a))
    (_ : ∀ a, Nonempty (A (a + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y₀.toRingedSpace.sheaf).obj (A a)).obj Hb))
    (_ : Nonempty ((Scheme.Modules.pullback j).obj (A 0) ≅ Lc.divisorialSheaf.restrict W.ι)), C

/-- The conclusion of the compactification step, in continuation-passing style: a smooth
projective variety `X ⊇ W` whose boundary is the support of an effective divisor `E`, and a
decomposition `L + Δ` with `Δ` snc extending `B`, such that `L + mE + Δ` is nef and big for all
large `m`. -/
private abbrev CompactificationData {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [IsLocallyNoetherian Y] [IsNormal Y] (W : Y.Opens) (B : QDivisor Y) (C : Prop) : Prop :=
  ∀ (X : Scheme.{0}) (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (_ : IsSmoothScheme sX)
    (ι : W.toScheme ⟶ X) [IsOpenImmersion ι] (_ : ι ≫ sX = W.ι ≫ sY)
    (E L : Divisor X) (Δ : QDivisor X) (n₀ : ℕ) (_ : 0 ≤ E)
    (_ : Set.range ι = (E.supp : Set X)ᶜ) (_ : Δ.IsSNC sX)
    (_ : ∀ m : ℕ, n₀ ≤ m → (Divisor.toQDivisor (L + m • E) + Δ).IsNef k sX ∧
      (Divisor.toQDivisor (L + m • E) + Δ).IsBig k sX)
    (_ : ∀ P : MMP.Mori.PrimeDivisor W, (L + Δ.roundUp).coeff (openPrimeDivisor ι P) =
      B.roundUp.coeff (openPrimeDivisor W.ι P)), C

/-- **Projective closure of the preimage of an affine open.** For `f : Y ⟶ Z` projective, `B`
`f`-ample and `V ⊆ Z` affine with `W = f⁻¹(V)` nonempty, a high multiple `cB` of `B` is very
ample over `V`; the embedding `W ⟶ ℙᴹ_V ⊆ ℙᴹ × ℙʳ` by its sections, followed by the closure,
gives the data of `ProjectiveClosureData`. -/
private theorem exists_projectiveClosure
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sZ]
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Z) (hfs : f ≫ sZ = sY) (hf : IsProjectiveMorphism f)
    (B : QDivisor Y) (hB : B.HasRelativelyAmpleMultiple f)
    (V : Z.Opens) (hV : IsAffineOpen V) (hW : Nonempty (f ⁻¹ᵁ V)) (C : Prop)
    (H : ProjectiveClosureData sY (f ⁻¹ᵁ V) B C) : C := by
  classical
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI : IsAffine V.toScheme := hV
  -- Step 1: a multiple `L₀ = mB` that is ample on `W = f⁻¹(V)`
  obtain ⟨m, hm, L₀, hL₀c, hL₀B, hL₀amp⟩ := hB
  haveI := hL₀c.isInvertibleModule_divisorialSheaf
  have hrel : Stacks.RelativeAmple.IsRelativelyAmple f L₀.divisorialSheaf :=
    Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _ inferInstance
      hL₀amp
  set LW := (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L₀.divisorialSheaf with hLW
  haveI : Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V) LW :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  have hampW : Stacks.Ample.IsAmple (f ⁻¹ᵁ V) LW := hrel.2 V hV
  -- Step 2: a power of `LW` embeds `W` into `ℙᴹ_V` over `V`
  have hT := Stacks.AmpleRelativeFiniteType.tfae_six (f ∣_ V) LW
  obtain ⟨N₀, hN₀, himm⟩ := (hT.out 1 6).mp hampW
  obtain ⟨M, i, hi, hif, ⟨eL⟩⟩ := himm N₀ le_rfl
  -- Step 3: `V` is a closed subscheme of the standard chart `𝔸ʳ ⊆ ℙʳ_k`
  obtain ⟨r, c₀, hc₀, hc₀s⟩ := exists_isClosedImmersion_affineSpace (V.ι ≫ sZ)
  set Pr := projectiveSpaceOver r (Spec (.of k)) with hPr
  set ach : 𝔸(ULift.{0} (Fin r); Spec (.of k)) ⟶ Pr := projectiveSpaceOver.affineChart r 0
    (Equiv.ulift.{0}.trans (finSuccAboveEquiv (0 : Fin (r + 1)))) (Spec (.of k)) with hach
  set φ : V.toScheme ⟶ Pr := c₀ ≫ ach with hφ
  -- Step 4: `W ⟶ ℙᴹ_V ⟶ ℙᴹ_{ℙʳ}` and its scheme-theoretic image `Y₀`
  set P := projectiveSpaceOver M Pr with hP
  set πP : P ⟶ Pr := pullback.fst (terminal.from Pr) (terminal.from (projectiveSpaceAtUniverse M))
    with hπP
  set πPr : Pr ⟶ Spec (.of k) := pullback.fst (terminal.from (Spec (.of k)))
    (terminal.from (projectiveSpaceAtUniverse r)) with hπPr
  set b : projectiveSpaceOver M V.toScheme ⟶ P := projectiveSpaceOverMap M φ with hb
  set e : (f ⁻¹ᵁ V).toScheme ⟶ P := i ≫ b with he
  haveI := hi
  haveI := hc₀
  haveI : IsOpenImmersion ach := by rw [hach]; infer_instance
  haveI : IsImmersion φ := by rw [hφ]; infer_instance
  haveI : IsImmersion b :=
    MorphismProperty.of_isPullback (P := @IsImmersion) (isPullback_projectiveSpaceOverMap M φ).flip
      ‹IsImmersion φ›
  haveI : IsImmersion e := inferInstance
  haveI := compactSpace_preimage f hV.isCompact
  haveI : IsProper πPr := isProper_projectiveSpaceOver r (Spec (.of k))
  haveI : IsProper πP := isProper_projectiveSpaceOver M Pr
  haveI : QuasiCompact e := quasiCompact_of_compactSpace e
  set Y₀ := e.image with hY₀
  set j : (f ⁻¹ᵁ V).toScheme ⟶ Y₀ := e.toImage with hj
  set ι' : Y₀ ⟶ P := e.imageι with hι'
  set q : Y₀ ⟶ Pr := ι' ≫ πP with hq
  set s₀ : Y₀ ⟶ Spec (.of k) := q ≫ πPr with hs₀
  have hPP : IsProjectiveMorphism (πP ≫ πPr) :=
    IsProjectiveMorphism.comp ⟨M, 𝟙 _, inferInstance, Category.id_comp _⟩
      ⟨r, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hs₀' : s₀ = ι' ≫ πP ≫ πPr := by rw [hs₀, hq, Category.assoc]
  obtain ⟨hs₀p, -⟩ := isProjectiveMorphism_of_isProjective (πP ≫ πPr) hPP ι'
    (Stacks.FiniteMorphismProjective.isProjective_of_isFinite ι')
  have hY₀ : MMP.Mori.IsProjectiveVariety k s₀ := by
    rw [hs₀']
    haveI : IsProper (ι' ≫ πP ≫ πPr) := isProper_of_isProjectiveMorphism _ hs₀p
    haveI : IsIntegral (f ⁻¹ᵁ V).toScheme := inferInstance
    exact (MMP.Mori.isProjectiveVariety_iff k _).2
      ⟨@AlgebraicGeometry.IsVariety.mk k _ _ _ inferInstance inferInstance inferInstance
        inferInstance, hs₀p⟩
  have heπ : e ≫ πP = (f ∣_ V) ≫ φ := by
    rw [he, Category.assoc, hb, hπP, projectiveSpaceOverMap_fst, ← Category.assoc, hif]
  have hφπ : φ ≫ πPr = V.ι ≫ sZ := by
    rw [hφ, Category.assoc, hπPr]
    erw [projectiveSpaceOver.affineChart_over]
    exact hc₀s
  have hjs : j ≫ s₀ = (f ⁻¹ᵁ V).ι ≫ sY := by
    rw [hs₀, hq, ← Category.assoc, ← Category.assoc, hj, hι', Scheme.Hom.toImage_imageι,
      heπ, Category.assoc, hφπ, ← Category.assoc, morphismRestrict_ι, Category.assoc, hfs]
  -- the boundary section `t = q^* x₀`
  set Hb : Y₀.Modules := (Scheme.Modules.pullback q).obj
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))) with hHb
  haveI hHbi : Stacks.Ample.IsInvertibleModule Y₀ Hb :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  set t : Γ(Hb, ⊤) := pullbackGlobalSections q _ (MMP.Fourfold.coordSectionTop (A := k) r 0)
    with ht
  have hrange : Set.range j = Stacks.Ample.nonvanishingLocus Hb t := by
    have hNV : Stacks.Ample.nonvanishingLocus Hb t = q.base ⁻¹' Set.range ach.base := by
      ext y
      rw [Set.mem_preimage, ht, MMP.Fourfold.mem_nonvanishingLocus_pullbackGlobalSections_iff,
        mem_nonvanishingLocus_coordSectionTop_iff, hach, projectiveSpaceOver.range_affineChart]
      rfl
    rw [hNV]
    have hje : j ≫ ι' = e := by rw [hj, hι']; exact Scheme.Hom.toImage_imageι e
    have hjq : j ≫ q = ((f ∣_ V) ≫ c₀) ≫ ach := by
      rw [hq, ← Category.assoc, hje, heπ, hφ, Category.assoc]
    set U₀ : Pr.Opens := ach.opensRange with hU₀
    set Q : Y₀.Opens := q ⁻¹ᵁ U₀ with hQ
    have hjQ : Set.range j.base ⊆ Set.range Q.ι.base := by
      rintro _ ⟨w, rfl⟩
      rw [Scheme.Opens.range_ι]
      change q.base (j.base w) ∈ Set.range ach.base
      rw [← Scheme.Hom.comp_apply, hjq, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    set j' := IsOpenImmersion.lift Q.ι j hjQ with hj'
    have hj'f : j' ≫ Q.ι = j := IsOpenImmersion.lift_fac _ _ _
    haveI : IsOpenImmersion j' := by
      haveI : IsOpenImmersion (j' ≫ Q.ι) := by rw [hj'f]; infer_instance
      exact IsOpenImmersion.of_comp j' Q.ι
    have hcomp : j' ≫ (q ∣_ U₀) = ((f ∣_ V) ≫ c₀) ≫ ach.isoOpensRange.hom := by
      rw [← cancel_mono U₀.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hj'f,
        Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, hjq]
    haveI : IsSeparated q := by rw [hq]; infer_instance
    haveI : IsProper (j' ≫ (q ∣_ U₀)) := by rw [hcomp]; infer_instance
    haveI : IsProper j' := IsProper.of_comp j' (q ∣_ U₀)
    haveI : IsIntegral Y₀ := hY₀.toIsVariety.toIsIntegral
    obtain ⟨w⟩ := hW
    haveI : Nonempty Q := ⟨j' w⟩
    have hcl : IsClopen (Set.range j'.base) :=
      ⟨j'.isClosedMap.isClosed_range, j'.isOpenEmbedding.isOpen_range⟩
    have huniv : Set.range j'.base = Set.univ := by
      rcases isClopen_iff.mp hcl with h | h
      · exact absurd h (Set.Nonempty.ne_empty ⟨_, w, rfl⟩)
      · exact h
    rw [← hj'f, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, huniv, Set.image_univ,
      Scheme.Opens.range_ι]
    rfl
  -- the ample family `A_a = 𝒪(1) ⊗ q^* 𝒪(a)` restricted to `Y₀`
  set A : ℕ → Y₀.Modules := fun a => (Scheme.Modules.pullback ι').obj
    (Stacks.AmplePullbackPart1.tensorPullbackPowModule πP
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr)
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))) a) with hA
  have hAi : ∀ a, Stacks.Ample.IsInvertibleModule Y₀ (A a) := fun a =>
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj _ _
  obtain ⟨a₀, hamp⟩ : ∃ a₀ : ℕ, ∀ a, a₀ ≤ a → Stacks.Ample.IsAmple Y₀ (A a) := by
    obtain ⟨a₀, ha₀⟩ := Stacks.AmplePullbackDatum.exists_threshold_isAmple πP _ _
      (Stacks.HProjective.isRelativelyAmple_projectiveSpaceTwistingSheaf M Pr)
      (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf (n := r) (S := Spec (.of k)))
    refine ⟨a₀, fun a ha => ?_⟩
    exact Stacks.AmplePullbackCovering.isAmple_modulePullback_of_immersion_or_isEmbedding ι' _
      (ha₀ a ha) (Or.inl ⟨inferInstance, inferInstance⟩)
  have eA : ∀ a, Nonempty (A (a + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor Y₀.toRingedSpace.sheaf).obj (A a)).obj Hb) := by
    intro a
    set O1M := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr
    set O1r := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))
    have e1 : Stacks.Ample.tensorPowModule Pr O1r ((a + 1 : ℕ) : ℤ) ≅
        Stacks.RelativeVeryAmple.tensorModules Pr (Stacks.Ample.tensorPowModule Pr O1r (a : ℤ))
          O1r :=
      eqToIso (by push_cast; rfl) ≪≫ (Stacks.Ample.tensorPowModuleAddIso Pr O1r a 1).symm ≪≫
        Stacks.RelativeVeryAmple.tensorModulesMapIso Pr (Iso.refl _)
          (Stacks.Ample.tensorPowModuleOneIso Pr O1r)
    have e2 := (Scheme.Modules.pullback πP).mapIso e1 ≪≫
      Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso πP _ _
    have e3 := Stacks.RelativeVeryAmple.tensorModulesMapIso P (Iso.refl O1M) e2 ≪≫
      (Stacks.TensorSheafSpellingIso.tensorModulesAssociator P _ _ _).symm
    have e4 := (Scheme.Modules.pullback ι').mapIso e3 ≪≫
      Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso ι' _ _
    exact ⟨e4 ≪≫ Stacks.RelativeVeryAmple.tensorModulesMapIso Y₀ (Iso.refl _)
      ((Scheme.Modules.pullbackComp ι' πP).app O1r)⟩
  have eA0 : Nonempty ((Scheme.Modules.pullback j).obj (A 0) ≅
      (N₀ • L₀).divisorialSheaf.restrict (f ⁻¹ᵁ V).ι) := by
    obtain ⟨eP⟩ := nonempty_tensorPowModule_divisorialSheaf_iso hL₀c N₀
    set O1M := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M Pr
    set O1r := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf r (Spec (.of k))
    have hje : j ≫ ι' = e := by rw [hj, hι']; exact Scheme.Hom.toImage_imageι e
    have hbs : b ≫ projectiveSpaceOver.toIntegralAtUniverse M Pr =
        projectiveSpaceOver.toIntegralAtUniverse M V.toScheme := projectiveSpaceOverMap_snd M φ
    have eT : Stacks.RelativeVeryAmple.tensorModules P O1M ((Scheme.Modules.pullback πP).obj
        (Stacks.Ample.tensorPowModule Pr O1r ((0 : ℕ) : ℤ))) ≅ O1M :=
      Stacks.RelativeVeryAmple.tensorModulesMapIso P (Iso.refl _)
        ((Scheme.Modules.pullback πP).mapIso (Stacks.Ample.tensorPowModuleZeroIso Pr O1r) ≪≫
          Stacks.PullbackAlgebra.pullbackUnitIso πP.toLRSHom.toShHom) ≪≫
        Stacks.TensorSheafSpellingIso.tensorModulesRightUnitor P O1M
    have eb : (Scheme.Modules.pullback b).obj O1M ≅
        Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf M V.toScheme :=
      (Scheme.Modules.pullbackComp b (projectiveSpaceOver.toIntegralAtUniverse M Pr)).app _ ≪≫
        eqToIso (by rw [hbs])
    exact ⟨(Scheme.Modules.pullbackComp j ι').app _ ≪≫ eqToIso (by rw [hje]; rfl) ≪≫
      (Scheme.Modules.pullback e).mapIso eT ≪≫ eqToIso (by rw [he]) ≪≫
      ((Scheme.Modules.pullbackComp i b).app O1M).symm ≪≫
      (Scheme.Modules.pullback i).mapIso eb ≪≫ eL.symm ≪≫
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (f ⁻¹ᵁ V).ι
        L₀.divisorialSheaf N₀).symm ≪≫
      (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).mapIso eP ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app _).symm⟩
  refine H (N₀ * m) (Nat.mul_pos (by omega) hm) (N₀ • L₀) ?_ Y₀ s₀ hY₀ j inferInstance hjs Hb hHbi
    t hrange A hAi a₀ hamp eA eA0
  rw [map_nsmul, hL₀B]
  ext P
  change (N₀ • ((m : ℚ) • B)) P = (((N₀ * m : ℕ) : ℚ) • B) P
  simp only [Finsupp.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
  ring

/-- **Lifting an open immersion along a morphism that is an isomorphism over an open.** If
`g : X' ⟶ X` restricts to an isomorphism over `U` and `j : W ⟶ X` is an open immersion with image
in `U`, then `j` lifts to an open immersion `ι : W ⟶ X'` with image `g⁻¹(j(W))`. -/
private theorem exists_isOpenImmersion_lift {W X X' : Scheme.{0}} (g : X' ⟶ X) (U : X.Opens)
    [IsIso (g ∣_ U)] (j : W ⟶ X) [IsOpenImmersion j] (hj : Set.range j ⊆ U) :
    ∃ ι : W ⟶ X', IsOpenImmersion ι ∧ ι ≫ g = j ∧ Set.range ι = g ⁻¹' Set.range j := by
  have hjU : Set.range j ⊆ Set.range U.ι := by simpa using hj
  set j' : W ⟶ U.toScheme := IsOpenImmersion.lift U.ι j hjU with hj'def
  have hj' : j' ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion j' := by
    have : IsOpenImmersion (j' ≫ U.ι) := by rw [hj']; infer_instance
    exact IsOpenImmersion.of_comp j' U.ι
  have hfac : inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι ≫ g = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  refine ⟨j' ≫ inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hfac, hj']
  · ext x
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hfac, hj']
    · rintro ⟨w, hw⟩
      have hxU : x ∈ g ⁻¹ᵁ U := by
        change g x ∈ U
        rw [← hw]
        exact hj ⟨w, rfl⟩
      let y : (g ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
      have hy : (g ⁻¹ᵁ U).ι y = x := rfl
      have h1 : (g ∣_ U) y = j' w := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, hy,
          ← Scheme.Hom.comp_apply, hj']
        exact hw.symm
      have h2 : inv (g ∣_ U) (j' w) = y := by
        rw [← h1, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
        rfl
      refine ⟨w, ?_⟩
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h2, hy]

/-- **The effective divisor of a section.** On an integral Noetherian normal scheme on which every
divisor is Cartier, a section `t` of an invertible sheaf `L` that does not vanish identically is
the canonical section `1` of `𝒪_X(E)` for an effective divisor `E` with `𝒪_X(E) ≅ L`; the
complement of `Supp E` is the nonvanishing locus of `t`. -/
private theorem exists_divisor_of_section {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (hcart : ∀ D : Divisor X, D.IsCartier)
    (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (t : Γ(L, ⊤))
    (ht : (Stacks.Ample.nonvanishingLocus L t).Nonempty) :
    ∃ E : Divisor X, 0 ≤ E ∧ Nonempty (E.divisorialSheaf ≅ L) ∧
      (E.supp : Set X)ᶜ = Stacks.Ample.nonvanishingLocus L t := by
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    ‹Stacks.Ample.IsInvertibleModule X L›
  obtain ⟨D, ⟨e⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible L
  set sΓ : Γ(D.divisorialSheaf, ⊤) := e.inv.app ⊤ t with hsΓ
  have hts : e.hom.app ⊤ sΓ = t := by
    rw [hsΓ, ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.inv_hom_id]
    rfl
  have hsne : sΓ ≠ 0 := fun h => by
    obtain ⟨x, hx⟩ := ht
    rw [← hts, h, map_zero, Stacks.Ample.nonvanishingLocus_zero] at hx
    exact hx
  set σ : D.divisorialSubmodule ⊤ := sΓ with hσ
  let ψ₀ : RationalFunctions X := fun Z => σ.1 ⟨Z, trivial⟩
  have hsub : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hψ₀ : ∀ Z, ψ₀ Z ≠ 0 := by
    intro Z hZ
    apply hsne
    change σ = 0
    apply Subtype.ext
    funext Z'
    change σ.1 Z' = 0
    obtain rfl : Z' = ⟨Z, trivial⟩ := Subtype.ext (Subsingleton.elim _ _)
    exact hZ
  have hunit : IsUnit ψ₀ := by
    rw [Pi.isUnit_iff]
    intro Z
    obtain ⟨b, hb⟩ := (RationalFunctions.isField_stalk X Z).mul_inv_cancel (hψ₀ Z)
    exact IsUnit.of_mul_eq_one _ hb
  set ψ := hunit.unit with hψ
  set E : Divisor X := D + principalDivisor ψ with hE
  have hEc : ∀ P : MMP.Mori.PrimeDivisor X, E.coeff P = D.coeff P + P.ord ψ := fun P => by
    rw [hE, DivisorWithCoeffs.coeff_add, coeff_principalDivisor]
  have hE0 : 0 ≤ E := by
    intro P
    change 0 ≤ E.coeff P
    rw [hEc]
    have h := σ.2 P ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, trivial⟩
    rcases h with h | h
    · exact absurd h (hψ₀ _)
    · have h' : WithZero.exp (-D.coeff P) ≤ WithZero.exp (P.ord ψ) := by
        rw [← P.valuation_component ψ]
        exact h
      rw [WithZero.exp_le_exp] at h'
      linarith
  let eM : E.divisorialSheaf ≅ D.divisorialSheaf := Divisor.divisorialSheafMulIso ψ hEc
  have h1 : eM.hom.app ⊤ (MMP.Threefold.Mori.oneSection hE0) = sΓ := by
    change (⟨_, _⟩ : D.divisorialSubmodule ⊤) = σ
    apply Subtype.ext
    funext Z
    change (ψ : RationalFunctions X) Z.1 *
      ((Divisor.structureSheafToDivisorialSheaf hE0).app ⊤ (1 : Γ(X, ⊤))).1 Z = σ.1 Z
    rw [Divisor.coe_structureSheafToDivisorialSheaf_app, map_one]
    change (ψ : RationalFunctions X) Z.1 * 1 = σ.1 Z
    rw [mul_one]
    rfl
  refine ⟨E, hE0, ⟨eM ≪≫ e⟩, ?_⟩
  rw [← MMP.Threefold.Mori.nonvanishingLocus_oneSection hE0 (hcart E),
    ← Stacks.Ample.nonvanishingLocus_congr (eM ≪≫ e) (MMP.Threefold.Mori.oneSection hE0)]
  congr 1
  rw [Iso.trans_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply, h1, hts]

/-- **Rational functions lift along an open immersion.** For an open immersion `ι : W ⟶ X` of
integral schemes, every unit of `K(W)` is the pull-back of a unit of `K(X)`: the stalk map of `ι`
at the generic point of `W` is an isomorphism. -/
private theorem exists_pullbackRationalFunction_eq {W X : Scheme.{0}} [IsIntegral W] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (ι : W ⟶ X) [IsOpenImmersion ι]
    (hφ' : ∀ (φ : (RationalFunctions X)ˣ) (Z : irreducibleComponents W),
      ι (componentGenericPoint W Z) ∉ (principalDivisor φ).supp)
    (ψ : (RationalFunctions W)ˣ) :
    ∃ φ : (RationalFunctions X)ˣ, pullbackRationalFunction ι φ (hφ' φ) = ψ := by
  have hsubW : Subsingleton (irreducibleComponents W) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents W) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  set η := componentGenericPoint W Z₀ with hη
  have hmem : ∀ W' : irreducibleComponents X, ι η ∈ W'.1 := fun W' => by
    have h : W'.1 ∈ ({Set.univ} : Set (Set X)) := by
      rw [← irreducibleComponents_eq_singleton]; exact W'.2
    rw [Set.mem_singleton_iff] at h
    rw [h]; trivial
  set a : (X.presheaf.stalk (ι η))ˣ :=
    Units.map (inv (ι.stalkMap η)).hom.toMonoidHom ((RationalFunctions.unitsEquiv W ψ) Z₀)
  refine ⟨(RationalFunctions.unitsEquiv X).symm
    (fun W' => Units.map (stalkToRationalFunctions X (hmem W')).hom.toMonoidHom a), ?_⟩
  apply (RationalFunctions.unitsEquiv W).injective
  funext Z
  obtain rfl : Z = Z₀ := Subsingleton.elim _ _
  obtain ⟨W₀⟩ : Nonempty (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  simp only [pullbackRationalFunction, MulEquiv.apply_symm_apply]
  rw [pullbackComponent_eq (hφ' _) (Divisor.isLocalEquation_principalDivisor _ ⊤) trivial
    (hmem W₀) a rfl]
  apply Units.ext
  change (ι.stalkMap η).hom ((inv (ι.stalkMap η)).hom _) = _
  rw [← CommRingCat.comp_apply, IsIso.inv_hom_id]
  rfl

/-- **Extending a divisor from an open subscheme up to linear equivalence.** Let `ι : W ⟶ X` be
an open immersion of integral Noetherian normal schemes and `G` a Cartier divisor on `X` whose
pull-back to `W` has divisorial sheaf isomorphic to `𝒪_W(T)`. Then some `G' ∼ G` has coefficient
`T(P)` along the prime divisor of `X` through every prime divisor `P` of `W`. -/
private theorem exists_linearlyEquivalent_coeff_eq {W X : Scheme.{0}} [IsIntegral W] [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] (ι : W ⟶ X) [IsOpenImmersion ι] {G : Divisor X} (hG : G.IsCartier)
    (T : Divisor W) (e : Nonempty ((Scheme.Modules.pullback ι).obj G.divisorialSheaf ≅
      T.divisorialSheaf)) :
    ∃ G' : Divisor X, Nonempty (G'.divisorialSheaf ≅ G.divisorialSheaf) ∧
      ∀ P : MMP.Mori.PrimeDivisor W, G'.coeff (openPrimeDivisor ι P) = T.coeff P := by
  haveI : IsDominant ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion ι
  have hB := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant ι
  obtain ⟨Gι, hGι⟩ := hG.exists_isPullback (hB G)
  obtain ⟨e⟩ := e
  obtain ⟨ψ, hψ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    ((Divisor.IsPullback.divisorialSheafIso (hBc := hG) hGι) ≪≫ e)
  obtain ⟨φ, hφ⟩ := exists_pullbackRationalFunction_eq ι (fun φ => hB _) ψ
  refine ⟨G - principalDivisor φ, ⟨Divisor.LinearlyEquivalent.divisorialSheafIso
    ⟨φ⁻¹, by rw [MMP.Mori.principalDivisor_inv]; abel⟩⟩, fun P => ?_⟩
  have hpr := Divisor.isPullback_principalDivisor (f := ι) φ (hB _)
  rw [hφ] at hpr
  rw [DivisorWithCoeffs.coeff_sub, ← coeff_of_isPullback_of_isOpenImmersion ι hG hGι,
    ← coeff_of_isPullback_of_isOpenImmersion ι (Divisor.isCartier_principalDivisor φ) hpr]
  have := congrArg (DivisorWithCoeffs.coeff · P) hψ
  simp only [DivisorWithCoeffs.coeff_sub] at this
  rw [← this]
  ring

/-- A divisor whose components are members of an snc family is snc. -/
private theorem isSNC_of_isSNCFamily {k : Type} [Field k] {X : Scheme.{0}}
    {s : X ⟶ Spec (.of k)} {ι : Type*} {F : ι → X.IdealSheafData}
    (hF : MMP.Resolution.IsSNCFamily s F)
    {R : Type*} [Zero R] (D : MMP.Mori.DivisorWithCoeffs R X)
    (hD : ∀ P ∈ D.support, ∃ i, F i = P.idealSheaf) :
    MMP.Mori.DivisorWithCoeffs.IsSNC s D := by
  choose g hg using hD
  refine ⟨fun P hP => ?_, fun x => ?_⟩
  · rw [← hg P hP]; exact (hF.1 _).2.2
  · obtain ⟨n, w, c, hw, hc, hinj⟩ := hF.2 x
    have hmem : ∀ P : {P : MMP.Mori.PrimeDivisor X // P ∈ D.support ∧ x ∈ P.support},
        x ∈ (F (g P.1 P.2.1)).support := fun P => by rw [hg]; exact P.2.2
    refine ⟨n, w, fun P => c ⟨_, hmem P⟩, hw, fun P Q hPQ => ?_, fun P => ?_⟩
    · have h : g P.1 P.2.1 = g Q.1 Q.2.1 := congrArg Subtype.val (hinj hPQ)
      have : P.1.idealSheaf = Q.1.idealSheaf := by
        rw [← hg P.1 P.2.1, ← hg Q.1 Q.2.1, h]
      exact Subtype.ext (MMP.Mori.PrimeDivisor.ext_idealSheaf this)
    · have := hc ⟨_, hmem P⟩
      rwa [hg] at this

/-- A prime divisor contained in a closed set of pure codimension one is one of its irreducible
components. -/
private theorem mem_componentsOf_of_support_subset {X : Scheme.{0}} {S : Set X} (hS : IsClosed S)
    (hpure : MMP.Mori.IsPureCodimOne (⟨S, hS⟩ : TopologicalSpace.Closeds X))
    (P : MMP.Mori.PrimeDivisor X) (hP : (P.support : Set X) ⊆ S) :
    (P.support : Set X) ∈ MMP.Resolution.componentsOf S := by
  have hηS : P.genericPoint ∈ S :=
    hP (MMP.Flips.primeDivisor_genericPoint_mem_support P)
  obtain ⟨W, hW, hηW⟩ := MMP.Resolution.exists_mem_componentsOf hηS
  have hWcl : IsClosed W := MMP.Resolution.isClosed_of_mem_componentsOf hS hW
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1.1 hWcl
  have hmax : Maximal (fun W' : TopologicalSpace.IrreducibleCloseds X => (W' : Set X) ⊆ S)
      ⟨W, hW.1.1, hWcl⟩ :=
    ⟨hW.1.2, fun W' hW' hle => hW.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hcod := hpure _ hmax
  have hξc : Order.coheight ξ = 1 := by
    rw [← Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
    convert hcod using 2
    ext1
    exact hξ.def
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hξc with hQ
  have hQs : (Q.support : Set X) = W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hξ.def
  have hPQ : (P.support : Set X) ⊆ Q.support := by
    rw [hQs, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηW) hWcl
  have hPQe := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ
  rw [hPQe, hQs]
  exact hW

/-- A divisor all of whose components lie in an snc closed subset is snc. -/
private theorem isSNC_of_isSNCClosedSubset {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] {S : Set X} (hS : MMP.Resolution.IsSNCClosedSubset sX S)
    {R : Type*} [Zero R] (Δ : MMP.Mori.DivisorWithCoeffs R X)
    (hΔ : ∀ P ∈ Δ.support, (P.support : Set X) ⊆ S) : Δ.IsSNC sX := by
  obtain ⟨hScl, hS0 | ⟨hpure, -, hfam⟩⟩ := hS
  · have hempty : ∀ P ∈ Δ.support, False := fun P hP => by
      have := hΔ P hP (MMP.Flips.primeDivisor_genericPoint_mem_support P)
      rw [hS0] at this
      exact this
    refine ⟨fun P hP => (hempty P hP).elim, fun x => ?_⟩
    haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk x)
    exact ⟨n, z, fun P => (hempty P.1 P.2.1).elim, hz, fun P => (hempty P.1 P.2.1).elim,
      fun P => (hempty P.1 P.2.1).elim⟩
  · exact isSNC_of_isSNCFamily hfam Δ fun P hP =>
      ⟨⟨_, mem_componentsOf_of_support_subset hScl hpure P (hΔ P hP)⟩,
        MMP.Fourfold.SNCWeight.PrimeDivisorUnion.componentsFamily_eq_idealSheaf _ P rfl⟩

/-- The local snc condition at a point only depends on the support of the divisor. -/
private theorem sncStalk_of_support_iff {R R' : Type*} [Zero R] [Zero R'] {W : Scheme.{0}}
    (D : MMP.Mori.DivisorWithCoeffs R W) (D' : MMP.Mori.DivisorWithCoeffs R' W)
    (h : ∀ P, D P ≠ 0 ↔ D' P ≠ 0) (w : W)
    (hD : ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk w)
      (jj : {E : MMP.Mori.PrimeDivisor W // E ∈ D.support ∧ w ∈ E.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, AlgebraicGeometry.IdealSheafData.stalk E.1.idealSheaf w = Ideal.span {z (jj E)}) :
    ∃ (n : ℕ) (z : Fin n → W.presheaf.stalk w)
      (jj : {E : MMP.Mori.PrimeDivisor W // E ∈ D'.support ∧ w ∈ E.support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, AlgebraicGeometry.IdealSheafData.stalk E.1.idealSheaf w = Ideal.span {z (jj E)} := by
  have hs : D.support = D'.support := Finset.ext fun P => by
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]; exact h P
  rw [← hs]
  exact hD

/-- **Transport of the snc condition to the image of an open immersion.** Let `ι : W ⟶ X` and
`j : W ⟶ Y` be open immersions over `k`, `F` an snc divisor on `Y` and `D` a finite set of prime
divisors of `X` whose members through `ι(W)` are exactly the closures of the components of
`F|_W`. Then `D` restricted to `ι(W)` is an snc closed subset. -/
private theorem isSNCClosedSubset_opensRange {k : Type} [Field k] {W X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sY] (ι : W ⟶ X) [IsOpenImmersion ι] (jY : W ⟶ Y) [IsOpenImmersion jY]
    (h : ι ≫ sX = jY ≫ sY) {R : Type*} [Zero R] (F : MMP.Mori.DivisorWithCoeffs R Y)
    (hF : F.IsSNC sY) (D : Finset (MMP.Mori.PrimeDivisor X))
    (hD : ∀ Q : MMP.Mori.PrimeDivisor W,
      openPrimeDivisor ι Q ∈ D ↔ F.coeff (openPrimeDivisor jY Q) ≠ 0) :
    MMP.Resolution.IsSNCClosedSubset (ι.opensRange.ι ≫ sX)
      (ι.opensRange.ι ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X))) := by
  classical
  set U := ι.opensRange with hU
  set Rd : Divisor X := ∑ E ∈ D, Finsupp.single E (1 : ℤ) with hRd
  have hRd' : ∀ P, Rd P ≠ 0 ↔ P ∈ D := fun P => by
    rw [hRd, Finset.sum_apply']; simp [Finsupp.single_apply]
  set T : Divisor U := Rd.restrictOpen U with hT
  have hTc : ∀ Fc, T Fc = Rd (OpenWeilRestriction.primeDivisorMap U.ι Fc) := fun _ => rfl
  have hrangeU : Set.range U.ι = Set.range ι := by rw [Scheme.Opens.range_ι]; rfl
  have hlofp : ∀ {Z : Scheme.{0}} (I : Z.IdealSheafData) (s : Z ⟶ Spec (.of k))
      [LocallyOfFiniteType s], LocallyOfFinitePresentation (I.subschemeι ≫ s) := fun I s _ =>
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := I.subschemeι ≫ s)).mpr
      inferInstance
  have hTQ : ∀ Fc : MMP.Mori.PrimeDivisor U, Fc ∈ T.support →
      ∃ Q : MMP.Mori.PrimeDivisor W,
        OpenWeilRestriction.primeDivisorMap U.ι Fc = openPrimeDivisor ι Q ∧
          openPrimeDivisor ι Q ∈ D := by
    intro Fc hFc
    have hPD : OpenWeilRestriction.primeDivisorMap U.ι Fc ∈ D :=
      (hRd' _).1 (by rw [← hTc]; exact Finsupp.mem_support_iff.mp hFc)
    obtain ⟨w, hw⟩ : U.ι Fc.genericPoint ∈ Set.range ι := by
      rw [← hrangeU]; exact ⟨_, rfl⟩
    have hmem : ι w ∈ (OpenWeilRestriction.primeDivisorMap U.ι Fc).support := by
      rw [hw, MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
      ι _ w hmem
    refine ⟨Q, by rw [openPrimeDivisor_eq_primeDivisorMap, hQ], ?_⟩
    rw [openPrimeDivisor_eq_primeDivisorMap, hQ]
    exact hPD
  have hTsnc : T.IsSNC (U.ι ≫ sX) := by
    refine ⟨fun Fc hFc => ?_, fun x => ?_⟩
    · obtain ⟨Q, hPQ, hQD⟩ := hTQ Fc hFc
      have hFQ : F.coeff (openPrimeDivisor jY Q) ≠ 0 := (hD Q).1 hQD
      have hsmY := hF.1 (openPrimeDivisor jY Q) (Finsupp.mem_support_iff.mpr hFQ)
      haveI := hlofp (openPrimeDivisor jY Q).idealSheaf sY
      haveI := hlofp (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf sX
      have h1 : MMP.Mori.IsSmoothScheme (Q.idealSheaf.subschemeι ≫ jY ≫ sY) := by
        refine (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff jY sY
          (openPrimeDivisor jY Q).idealSheaf Q.idealSheaf (by
            rw [openPrimeDivisor_eq_primeDivisorMap]
            exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap jY Q)).2
          fun z _ => ?_
        rw [← MMP.Mori.smoothLocus_eq_smoothLocus, hsmY]; trivial
      rw [← h] at h1
      have h2 := (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff ι sX
        (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf Q.idealSheaf (by
          rw [hPQ, openPrimeDivisor_eq_primeDivisorMap]
          exact MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap ι Q)).1 h1
      exact (MMP.Threefold.Mori.OpenRestriction.isSmoothScheme_comap_iff U.ι sX
        (OpenWeilRestriction.primeDivisorMap U.ι Fc).idealSheaf Fc.idealSheaf
        (MMP.Threefold.Mori.OpenRestriction.idealSheaf_comap_primeDivisorMap U.ι Fc)).2
        fun z hz => h2 z (by rw [← hrangeU]; exact hz)
    · obtain ⟨w, hw⟩ := x.2
      have hx : U.ι x = ι w := hw.symm
      refine (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι Rd x).2 ?_
      rw [hx]
      refine (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff ι Rd w).1 ?_
      have hY := (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff jY F w).2
        (hF.2 (jY w))
      refine sncStalk_of_support_iff _ _ (fun Q => ?_) w hY
      rw [Finsupp.comapDomain_apply, Finsupp.comapDomain_apply, ← openPrimeDivisor_eq_primeDivisorMap,
        ← openPrimeDivisor_eq_primeDivisorMap, hRd', hD Q]
      rfl
  have hset : U.ι ⁻¹' (D.sup fun E => (E.idealSheaf.support : Set X)) =
      ⋃ Fc ∈ T.support, (Fc.support : Set U) := by
    ext x
    simp only [Set.mem_preimage, Finset.sup_set_eq_biUnion, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨P, hP, hx⟩
      obtain ⟨Fc, hFc⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
        U.ι P x hx
      refine ⟨Fc, ?_, ?_⟩
      · rw [Finsupp.mem_support_iff, hTc, hFc]; exact (hRd' P).2 hP
      · rw [← MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι, hFc]
        exact hx
    · rintro ⟨Fc, hFc, hx⟩
      exact ⟨_, (hRd' _).1 (by rw [← hTc]; exact Finsupp.mem_support_iff.mp hFc),
        (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff U.ι Fc x).2 hx⟩
  rw [hset]
  exact MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ hTsnc

/-- **Resolution of a projective closure.** From the data of `ProjectiveClosureData`, a strong
resolution of `Y₀` followed by a log resolution of the closures of the components of `{B}` and
of the boundary, both isomorphisms over `W`, gives the data of `CompactificationData`. -/
private theorem exists_compactification_of_projectiveClosure
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (W : Y.Opens) [Nonempty W] [CompactSpace W]
    (B : QDivisor Y) (hBf : B.fract.IsSNC sY) (C : Prop)
    (H : CompactificationData sY W B C) : ProjectiveClosureData sY W B C := by
  classical
  intro c hc Lc hLc Y₀ s₀ hY₀ j hjo hj Hb hHb t ht A hA a₀ hamp eA eA0
  haveI := hjo
  haveI := hHb
  haveI := hY₀
  have hY₀v : AlgebraicGeometry.IsVariety k s₀ := hY₀.toIsVariety
  haveI := hY₀v
  haveI : IsIntegral Y₀ := hY₀v.toIsIntegral
  haveI : IsLocallyNoetherian Y₀ := LocallyOfFiniteType.isLocallyNoetherian s₀
  haveI : CompactSpace Y₀ := QuasiCompact.compactSpace_of_compactSpace s₀
  -- the image of `W` lies in the smooth locus of `Y₀`
  have hsY : Smooth sY := (MMP.Mori.isSmoothScheme_iff sY).1 hsm
  have hWsm : Set.range j ⊆ (smoothLocus s₀ : Set Y₀) := by
    have hU : Smooth (j.opensRange.ι ≫ s₀) := by
      rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc, hj]
      infer_instance
    exact fun _ hx => (le_sSup hU : j.opensRange ≤ smoothLocus s₀) hx
  -- Step 1: a strong resolution `g₁ : X₁ ⟶ Y₀`, an isomorphism over the smooth locus
  obtain ⟨X₁, g₁, hX₁v, hg₁p, hg₁b, hX₁sm, hg₁iso, -⟩ :=
    MMP.Resolution.exists_isStrongResolution s₀ hY₀v
  haveI := hg₁iso
  obtain ⟨ι₁, hι₁o, hι₁, hι₁r⟩ := exists_isOpenImmersion_lift g₁ (smoothLocus s₀) j hWsm
  haveI := hι₁o
  haveI := hX₁v
  haveI : IsIntegral X₁ := hX₁v.toIsIntegral
  haveI : IsLocallyNoetherian X₁ := LocallyOfFiniteType.isLocallyNoetherian (g₁ ≫ s₀)
  haveI : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace (g₁ ≫ s₀)
  haveI : Smooth (g₁ ≫ s₀) := (MMP.Mori.isSmoothScheme_iff _).1 hX₁sm
  haveI : IsNormal X₁ := isNormal_of_smooth_over_field (g₁ ≫ s₀)
  have hcart₁ : ∀ D : Divisor X₁, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hX₁sm
  -- the boundary divisor `E₁` on `X₁`, with `X₁ ∖ Supp E₁ = ι₁(W)`
  haveI : Stacks.Ample.IsInvertibleModule X₁ ((Scheme.Modules.pullback g₁).obj Hb) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj g₁ Hb
  have hrange₁ : Set.range ι₁ = Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback g₁).obj Hb) (pullbackGlobalSections g₁ Hb t) := by
    rw [hι₁r, ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections, ht]
  obtain ⟨E₁, hE₁0, -, hE₁r⟩ := exists_divisor_of_section hcart₁ _
    (pullbackGlobalSections g₁ Hb t) (by rw [← hrange₁]; exact Set.range_nonempty _)
  -- the closures in `X₁` of the components of `{B}` meeting `W`
  have hinjW : Function.Injective (openPrimeDivisor W.ι) := openPrimeDivisor_injective W.ι
  set S : Set (MMP.Mori.PrimeDivisor W) := {Q | B.fract.coeff (openPrimeDivisor W.ι Q) ≠ 0}
    with hSdef
  have hS : S.Finite := (B.fract.support.finite_toSet.preimage hinjW.injOn).subset
    fun Q hQ => Finsupp.mem_support_iff.mpr hQ
  set D : Finset (MMP.Mori.PrimeDivisor X₁) := hS.toFinset.image (openPrimeDivisor ι₁) ∪ E₁.support
    with hDdef
  -- Step 2: a log resolution of `(X₁, D)`, an isomorphism over `ι₁(W)`
  have hX₁n : MMP.Mori.IsNormalVariety k (g₁ ≫ s₀) := ⟨hX₁v, inferInstance⟩
  obtain ⟨Yb, f₂, hres, -, hsnc, hiso⟩ :=
    MMP.Resolution.exists_isLogResolution_isIso_restrict_of_isSNCClosedSubset (g₁ ≫ s₀) hX₁n D
  have hU : IsIso (f₂ ∣_ ι₁.opensRange) := hiso _ ((MMP.Mori.isSmoothScheme_iff _).2 inferInstance)
    (isSNCClosedSubset_opensRange (g₁ ≫ s₀) sY ι₁ W.ι (by rw [← Category.assoc, hι₁, hj]) B.fract
      hBf D fun Q => by
        constructor
        · intro hQ
          rcases Finset.mem_union.mp hQ with hQ | hQ
          · obtain ⟨Q', hQ', hQQ'⟩ := Finset.mem_image.mp hQ
            rw [← openPrimeDivisor_injective ι₁ hQQ']
            exact hS.mem_toFinset.mp hQ'
          · exact absurd (coeff_openPrimeDivisor_eq_zero ι₁ (hrange₁.trans hE₁r.symm) Q)
              (Finsupp.mem_support_iff.mp hQ)
        · intro hQ
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Q, hS.mem_toFinset.mpr hQ, rfl⟩))
  obtain ⟨ι, hιo, hι, hιr⟩ := exists_isOpenImmersion_lift f₂ ι₁.opensRange ι₁ (by simp)
  haveI := hιo
  set g : Yb ⟶ Y₀ := f₂ ≫ g₁ with hg
  have hιg : ι ≫ g = j := by rw [hg, ← Category.assoc, hι, hι₁]
  have hιgr : Set.range ι = g ⁻¹' Set.range j := by
    rw [hιr, hι₁r]; rfl
  -- the resolution `Yb` is a smooth projective variety
  have hgproj : IsProjective g := hres.isProjective.comp hg₁p
  obtain ⟨hYbpm, hgpm⟩ := isProjectiveMorphism_of_isProjective s₀
    ((MMP.Mori.isProjectiveVariety_iff k s₀).1 hY₀).2 g hgproj
  set sYb : Yb ⟶ Spec (.of k) := g ≫ s₀ with hsYb
  have hsYb' : sYb = f₂ ≫ g₁ ≫ s₀ := by rw [hsYb, hg, Category.assoc]
  have hYbv : AlgebraicGeometry.IsVariety k sYb := by rw [hsYb']; exact hres.isVariety_source
  haveI := hYbv
  haveI : MMP.Mori.IsProjectiveVariety k sYb :=
    (MMP.Mori.isProjectiveVariety_iff k sYb).2 ⟨hYbv, hYbpm⟩
  have hYbsm : IsSmoothScheme sYb := by rw [hsYb']; exact hres.isSmoothScheme
  haveI : IsIntegral Yb := hYbv.toIsIntegral
  haveI : IsLocallyNoetherian Yb := LocallyOfFiniteType.isLocallyNoetherian sYb
  haveI : CompactSpace Yb := QuasiCompact.compactSpace_of_compactSpace sYb
  haveI : Smooth sYb := (MMP.Mori.isSmoothScheme_iff _).1 hYbsm
  haveI : IsNormal Yb := isNormal_of_smooth_over_field sYb
  have hcart : ∀ D : Divisor Yb, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hYbsm
  -- the boundary divisor `E` on `Yb`, with `Yb ∖ Supp E = ι(W)`
  haveI : Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback g).obj Hb) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj g Hb
  have hrange : Set.range ι = Stacks.Ample.nonvanishingLocus
      ((Scheme.Modules.pullback g).obj Hb) (pullbackGlobalSections g Hb t) := by
    rw [hιgr, ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections, ht]
  obtain ⟨E, hE0, ⟨eE⟩, hEr⟩ := exists_divisor_of_section hcart _
    (pullbackGlobalSections g Hb t) (by rw [← hrange]; exact Set.range_nonempty _)
  -- the extension `G'` of `cB|_W` with `𝒪(G') ≅ g^* A₀`
  haveI : Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback g).obj (A 0)) :=
    Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj g (A 0)
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible Yb.sheaf.obj Yb.ringCatSheaf.property
      ((Scheme.Modules.pullback g).obj (A 0)) :=
    ‹Stacks.Ample.IsInvertibleModule Yb ((Scheme.Modules.pullback g).obj (A 0))›
  obtain ⟨G, ⟨eG⟩⟩ := MMP.Mori.exists_divisorialSheaf_iso_of_isInvertible
    ((Scheme.Modules.pullback g).obj (A 0))
  haveI : IsDominant W.ι := MMP.Positivity.DivisorOver.isDominant_of_isOpenImmersion W.ι
  have hcartY : ∀ D : Divisor Y, D.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  obtain ⟨T, hT⟩ := (hcartY Lc).exists_isPullback
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant W.ι Lc)
  have eT : Nonempty ((Scheme.Modules.pullback ι).obj G.divisorialSheaf ≅ T.divisorialSheaf) := by
    obtain ⟨e0⟩ := eA0
    exact ⟨(Scheme.Modules.pullback ι).mapIso eG ≪≫
      (Scheme.Modules.pullbackComp ι g).app _ ≪≫ (Scheme.Modules.pullbackCongr hιg).app _ ≪≫ e0 ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).app _ ≪≫
      (Divisor.IsPullback.divisorialSheafIso (hBc := hcartY Lc) hT).symm⟩
  obtain ⟨G', ⟨eG'⟩, hG'⟩ := exists_linearlyEquivalent_coeff_eq ι (hcart G) T eT
  -- `𝒪(G' + aE) ≅ g^* A_a`
  have hGa : ∀ a : ℕ, Nonempty ((G' + a • E).divisorialSheaf ≅
      (Scheme.Modules.pullback g).obj (A a)) := by
    intro a
    induction a with
    | zero => exact ⟨eqToIso (by rw [zero_nsmul, add_zero]) ≪≫ eG' ≪≫ eG⟩
    | succ a ih =>
      obtain ⟨e⟩ := ih
      obtain ⟨ea⟩ := eA a
      exact ⟨eqToIso (by rw [succ_nsmul, add_assoc]) ≪≫
        ((hcart _).divisorialSheafTensorIso (hcart E)).symm ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor _).mapIso e).app _ ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor _).obj _).mapIso eE ≪≫
        (Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso g (A a) Hb).symm ≪≫
        (Scheme.Modules.pullback g).mapIso ea.symm⟩
  -- `g` is birational: it maps `ι(W)` isomorphically onto `j(W)`
  have hgb : IsBirationalMorphism g := by
    have hle : ι.opensRange ≤ g ⁻¹ᵁ j.opensRange := by
      rintro _ ⟨w, rfl⟩
      exact ⟨w, by rw [← Scheme.Hom.comp_apply, hιg]⟩
    have hcomp : ι.isoOpensRange.hom ≫ g.resLE j.opensRange ι.opensRange hle =
        j.isoOpensRange.hom := by
      rw [← cancel_mono j.opensRange.ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
        Scheme.Hom.isoOpensRange_hom_ι_assoc, hιg, Scheme.Hom.isoOpensRange_hom_ι]
    have hres' : g.resLE j.opensRange ι.opensRange hle =
        inv ι.isoOpensRange.hom ≫ j.isoOpensRange.hom := by
      rw [← hcomp, IsIso.inv_hom_id_assoc]
    have : IsIso (g.resLE j.opensRange ι.opensRange hle) := by rw [hres']; infer_instance
    obtain ⟨w⟩ : Nonempty W := inferInstance
    exact MMP.Flips.isBirationalMorphism_of_isIso_resLE g _ _
      (show ((ι.opensRange : Yb.Opens) : Set Yb).Nonempty from ⟨ι w, w, rfl⟩)
      (show ((j.opensRange : Y₀.Opens) : Set Y₀).Nonempty from ⟨j w, w, rfl⟩) hle this
  -- the `ℚ`-divisor `B̄ = G'/c` extending `B`
  set Bb : QDivisor Yb := ((c : ℚ)⁻¹) • Divisor.toQDivisor G' with hBb
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hBbc : ∀ P, Bb.coeff P = (c : ℚ)⁻¹ * G'.coeff P := fun P => rfl
  have hdecomp : Divisor.toQDivisor Bb.roundDown + Bb.fract = Bb := by
    ext P
    change (Bb.roundDown.coeff P : ℚ) + Bb.fract.coeff P = Bb.coeff P
    rw [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_fract, Int.floor_add_fract]
  have hBbW : ∀ Q : MMP.Mori.PrimeDivisor W,
      Bb.coeff (openPrimeDivisor ι Q) = B.coeff (openPrimeDivisor W.ι Q) := by
    intro Q
    rw [hBbc, hG' Q, coeff_of_isPullback_of_isOpenImmersion W.ι (hcartY Lc) hT Q]
    have := congrArg (DivisorWithCoeffs.coeff · (openPrimeDivisor W.ι Q)) hLc
    simp only [Divisor.coeff_toQDivisor] at this
    rw [this]
    change (c : ℚ)⁻¹ * ((c : ℚ) * B.coeff _) = B.coeff _
    rw [← mul_assoc, inv_mul_cancel₀ hcq, one_mul]
  refine H Yb sYb hYbsm ι ?_ E Bb.roundDown Bb.fract a₀ hE0 ?_ ?_ ?_ ?_
  · rw [hsYb, ← Category.assoc, hιg, hj]
  · rw [hrange, ← hEr]
  · have hsnc' : MMP.Resolution.IsSNCClosedSubset sYb
        ((exceptionalSet f₂ : Set Yb) ∪ f₂ ⁻¹' (D.sup fun E => E.idealSheaf.support)) := by
      rwa [hsYb']
    refine isSNC_of_isSNCClosedSubset sYb hsnc' Bb.fract fun P hP => ?_
    by_cases hPW : ∃ w, ι w ∈ P.support
    · obtain ⟨w, hw⟩ := hPW
      obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
        ι P w hw
      rw [← openPrimeDivisor_eq_primeDivisorMap] at hQ
      subst hQ
      have hfr : B.fract.coeff (openPrimeDivisor W.ι Q) ≠ 0 := by
        have h := Finsupp.mem_support_iff.mp hP
        change Int.fract (Bb.coeff (openPrimeDivisor ι Q)) ≠ 0 at h
        rw [hBbW] at h
        rw [DivisorWithCoeffs.coeff_fract]
        exact h
      have hQS : Q ∈ S := hfr
      have hD : openPrimeDivisor ι₁ Q ∈ D :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Q, hS.mem_toFinset.mpr hQS, rfl⟩)
      have hcl : IsClosed (f₂ ⁻¹' ((openPrimeDivisor ι₁ Q).support : Set X₁)) :=
        (openPrimeDivisor ι₁ Q).idealSheaf.support.isClosed.preimage f₂.continuous
      intro y hy
      refine Or.inr ?_
      have hy' : y ∈ f₂ ⁻¹' ((openPrimeDivisor ι₁ Q).support : Set X₁) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hy
        refine closure_minimal ?_ hcl hy
        have hgp : AlgebraicGeometry.PrimeDivisor.genericPoint (openPrimeDivisor ι Q) =
            ι Q.genericPoint := genericPoint_openPrimeDivisor ι Q
        have hgp₁ : AlgebraicGeometry.PrimeDivisor.genericPoint (openPrimeDivisor ι₁ Q) =
            ι₁ Q.genericPoint := genericPoint_openPrimeDivisor ι₁ Q
        rw [Set.singleton_subset_iff, hgp]
        change f₂ (ι Q.genericPoint) ∈ ((openPrimeDivisor ι₁ Q).support : Set X₁)
        rw [← Scheme.Hom.comp_apply, hι, AlgebraicGeometry.PrimeDivisor.support_eq_closure, hgp₁]
        exact subset_closure rfl
      exact (Finset.le_sup (f := fun E : MMP.Mori.PrimeDivisor X₁ =>
        (E.idealSheaf.support : Set X₁)) hD) hy'
    · intro y hy
      refine Or.inr ?_
      have hyι : y ∉ Set.range ι := fun ⟨w, hw⟩ => hPW ⟨w, hw ▸ hy⟩
      rw [hιr, Set.mem_preimage, hrange₁, ← hE₁r, Set.notMem_compl_iff] at hyι
      obtain ⟨F, hF, hyF⟩ := DivisorWithCoeffs.mem_supp_iff.mp hyι
      have hD : F ∈ D := Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hF)
      exact (Finset.le_sup (f := fun E : MMP.Mori.PrimeDivisor X₁ =>
        (E.idealSheaf.support : Set X₁)) hD) hyF
  · intro m hm
    have hB' : Divisor.toQDivisor (G' + (c * m) • E) =
        (c : ℚ) • (Divisor.toQDivisor (Bb.roundDown + m • E) + Bb.fract) := by
      ext P
      have h : ((Bb.roundDown P : ℤ) : ℚ) + Bb.fract P = Bb P :=
        congrArg (fun D : QDivisor Yb => D P) hdecomp
      have hb : Bb P = (c : ℚ)⁻¹ * (G' P : ℚ) := rfl
      change (((G' + (c * m) • E) P : ℤ) : ℚ) =
        (c : ℚ) * ((((Bb.roundDown + m • E) P : ℤ) : ℚ) + Bb.fract P)
      simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul, Int.cast_add, Int.cast_mul,
        Int.cast_natCast]
      rw [add_right_comm, h, hb]
      field_simp
      push_cast
      ring
    obtain ⟨e⟩ := hGa (c * m)
    haveI := hA (c * m)
    exact QDivisor.isNef_and_isBig_of_isBirationalMorphism sYb s₀ hYbv hYbpm hY₀v
      ((MMP.Mori.isProjectiveVariety_iff k s₀).1 hY₀).2 g rfl hgpm hgb (A (c * m))
      (hamp _ (hm.trans (Nat.le_mul_of_pos_left m hc))) c hc _ (hcart _) e _ hB'
  · intro P
    have h1 : Bb.roundDown + Bb.fract.roundUp = Bb.roundUp := by
      rw [← roundUp_toQDivisor_add, hdecomp]
    rw [h1, DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_roundUp, hBbW P]

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_eq_of_isOpenImmersion {k : Type} [Field k] {W X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] (u : W ⟶ X) [IsOpenImmersion u]
    [Nonempty W] : topologicalKrullDim W = topologicalKrullDim X := by
  haveI : Nonempty u.opensRange := ⟨⟨u (Classical.arbitrary W), ⟨_, rfl⟩⟩⟩
  rw [← Stacks.Intersection.RationalEquivalenceProduct.topologicalKrullDim_opens k sX u.opensRange]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso u.isoOpensRange).isHomeomorph

/-- **Projective round-up vanishing, in the `Hgroup` spelling.** -/
private theorem isZero_hgroup_top_canonical_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k sX] (hsm : IsSmoothScheme sX)
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (L : Divisor X) (Δ : QDivisor X) (hΔ : Δ.IsSNC sX)
    (hnef : (Divisor.toQDivisor L + Δ).IsNef k sX) (hbig : (Divisor.toQDivisor L + Δ).IsBig k sX)
    (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup X.ringCatSheaf ⊤ i (K + (Divisor.toQDivisor L + Δ).roundUp).divisorialSheaf) := by
  set F := (K + (Divisor.toQDivisor L + Δ).roundUp).divisorialSheaf
  haveI := MMP.Mori.subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp
    sX hsm hK L Δ hΔ hnef hbig (i : ℤ) (by exact_mod_cast hi)
  haveI : Subsingleton (cohomologyOverField k sX F i) :=
    (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k sX F i).toEquiv.subsingleton
  haveI : Subsingleton (Hgroup X.ringCatSheaf ⊤ i F) :=
    (AlgebraicGeometry.cohomologyOverFieldAddEquivHgroup k sX F i).symm.toEquiv.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- The vanishing over the preimage of one affine open of the base. -/
private theorem isZero_hgroup_preimage
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sZ]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Z) (hfs : f ≫ sZ = sY) (hf : IsProjectiveMorphism f)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    (B : QDivisor Y) (hB : B.HasRelativelyAmpleMultiple f) (hBf : B.fract.IsSNC sY)
    (i : ℕ) (hi : 0 < i) (V : Z.Opens) (hV : IsAffineOpen V) :
    IsZero (Hgroup Y.ringCatSheaf (f ⁻¹ᵁ V) i (K + B.roundUp).divisorialSheaf) := by
  classical
  by_cases hW : Nonempty (f ⁻¹ᵁ V)
  swap
  · have hbot : f ⁻¹ᵁ V = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hW ⟨⟨x, hx⟩⟩
    rw [hbot]
    exact isZero_Hgroup_bot _ i
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI := compactSpace_preimage f hV.isCompact
  refine exists_projectiveClosure sY sZ f hfs hf B hB V hV hW _
    (exists_compactification_of_projectiveClosure sY hsm (f ⁻¹ᵁ V) B hBf _ ?_)
  intro X sX _ _ _ _ _ hsmX ι _ hιs E L Δ n₀ hE0 hrange hΔ hnb hcoeff
  have hdimX : topologicalKrullDim X = n := by
    rw [← hK.topologicalKrullDim_eq, ← topologicalKrullDim_eq_of_isOpenImmersion sX ι,
      topologicalKrullDim_eq_of_isOpenImmersion sY (f ⁻¹ᵁ V).ι]
  obtain ⟨K', hK'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme sX hsmX hdimX
  have hEc : E.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hsmX E
  set D : Divisor X := K' + (Divisor.toQDivisor (L + n₀ • E) + Δ).roundUp with hD
  haveI := hEc.isInvertibleModule_divisorialSheaf
  haveI := Divisor.isQuasicoherent_divisorialSheaf D
  have hT : ι ''ᵁ ⊤ = Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace)
      E.divisorialSheaf (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace)
        E.divisorialSheaf (MMP.Threefold.Mori.oneSection hE0)) := by
    apply TopologicalSpace.Opens.ext
    rw [nonvanishingOpen_divisorialSheafOneSection hEc hE0, ← hrange]
    simp
  have hG : IsZero (Hgroup X.ringCatSheaf (ι ''ᵁ ⊤) i D.divisorialSheaf) := by
    rw [hT]
    refine isZero_hgroup_nonvanishingOpen (X := X) E.divisorialSheaf _ D.divisorialSheaf i
      fun k => ?_
    obtain ⟨e⟩ := nonempty_twist_divisorialSheaf_iso
      (MMP.Fourfold.isCartier_of_isSmoothScheme hsmX D) hEc k
    refine IsZero.of_iso ?_ ((Hfunctor X.ringCatSheaf ⊤ i).mapIso e)
    have hDk : D + k • E = K' + (Divisor.toQDivisor (L + (n₀ + k) • E) + Δ).roundUp := by
      rw [hD, roundUp_toQDivisor_add, roundUp_toQDivisor_add, add_smul]
      abel
    rw [hDk]
    obtain ⟨h1, h2⟩ := hnb (n₀ + k) (Nat.le_add_right _ _)
    exact isZero_hgroup_top_canonical_add_roundUp sX hsmX hK' _ Δ hΔ h1 h2 i hi
  have hcoeff' : ∀ P : MMP.Mori.PrimeDivisor (f ⁻¹ᵁ V),
      ((Divisor.toQDivisor (L + n₀ • E) + Δ).roundUp).coeff (openPrimeDivisor ι P) =
        B.roundUp.coeff (openPrimeDivisor (f ⁻¹ᵁ V).ι P) := by
    intro P
    have hE : (n₀ • E).coeff (openPrimeDivisor ι P) = 0 := by
      change n₀ • E.coeff (openPrimeDivisor ι P) = 0
      rw [coeff_openPrimeDivisor_eq_zero ι hrange, smul_zero]
    rw [roundUp_toQDivisor_add, ← hcoeff P, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add, hE, add_zero]
  obtain ⟨e3⟩ := nonempty_restrict_divisorialSheaf_iso sX sY hsmX hsm ι (f ⁻¹ᵁ V).ι hιs hK' hK
    _ _ hcoeff'
  have e1 := (AlgebraicGeometry.CohomologyScalars.hfunctorOpenImmersionIso ι i).app
    D.divisorialSheaf
  have e2 := (AlgebraicGeometry.CohomologyScalars.hfunctorOpenImmersionIso (f ⁻¹ᵁ V).ι i).app
    (K + B.roundUp).divisorialSheaf
  have hW' : f ⁻¹ᵁ V = (f ⁻¹ᵁ V).ι ''ᵁ ⊤ := (Scheme.Opens.ι_image_top _).symm
  rw [hW']
  exact ((hG.of_iso e1.symm).of_iso ((Hfunctor _ ⊤ i).mapIso e3).symm).of_iso e2

/-- **Relative round-up vanishing.** For `f : Y ⟶ Z` projective with `Y` smooth, `K` canonical
and `B` an `f`-ample `ℚ`-divisor with snc fractional part, `R^i f_* 𝒪_Y(K + ⌈B⌉) = 0` for
`i > 0`: it suffices to check `H^i(f⁻¹V, 𝒪_Y(K + ⌈B⌉)) = 0` on the affine opens `V` of `Z`. -/
private theorem isZero_rightDerived_pushforward_divisorialSheaf_canonical_add_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sZ]
    (hsm : IsSmoothScheme sY)
    [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ Z) (hfs : f ≫ sZ = sY) (hf : IsProjectiveMorphism f)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    (B : QDivisor Y) (hB : B.HasRelativelyAmpleMultiple f) (hBf : B.fract.IsSNC sY)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
      (K + B.roundUp).divisorialSheaf) := by
  letI := HasDerivedCategory.standard Y.Modules
  letI := HasDerivedCategory.standard Z.Modules
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (Scheme.Modules.pushforward f)
    (rfl : (i : ℤ) = (i : ℤ)) _).1 ?_
  exact Stacks.AffineHigherDirectImage.isZero_rightDerivedPlus_pushforward_of_isZero_hgroup_preimage
    f _ i Z.isBasis_affineOpens fun V hV =>
      isZero_hgroup_preimage sY sZ hsm f hfs hf hK B hB hBf i hi V hV

/-- For an integer `n` and `0 ≤ b < 1`, `⌈n - b⌉ = n`. -/
private theorem ceil_intCast_sub {n : ℤ} {b : ℚ} (h0 : 0 ≤ b) (h1 : b < 1) :
    ⌈(n : ℚ) - b⌉ = n := by
  rw [Int.ceil_eq_iff]
  constructor <;> push_cast <;> linarith

end Main

end

end Proof_lem_mmp_relative_snc_ample_gap_vanishing

end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Mori

open Proof_lem_mmp_relative_snc_ample_gap_vanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules Stacks.Cohomology.TwistedGradedModule
open MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral
attribute [local implicit_reducible] _root_.SheafOfModules.forget
attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- **Relative Kawamata–Viehweg vanishing, ample form.** Let `k` be algebraically closed of
characteristic zero, `f : Y ⟶ Z` a projective morphism of `k`-varieties with `Y` smooth over `k`,
`K` a canonical divisor of `Y` of dimension `n`, `B` an effective `ℚ`-divisor on `Y` with snc
support and all coefficients `< 1`, and `L` a Cartier divisor on `Y`. If `L - (K + B)` is
`f`-ample, then `R^i f_* 𝒪_Y(L) = 0` for all `i > 0`. -/
@[mmp "lem_mmp_relative_snc_ample_gap_vanishing"]
public theorem isZero_rightDerived_pushforward_divisorialSheaf_of_hasRelativelyAmpleMultiple
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY)
    (hf : IsProjectiveMorphism f) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : DivisorWithCoeffs.IsSNC sY B)
    (hB1 : ∀ E : PrimeDivisor Y, B.coeff E < 1) {L : Divisor Y} (hL : L.IsCartier)
    (hM : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj L.divisorialSheaf) := by
  set M := Divisor.toQDivisor L - (Divisor.toQDivisor K + B) with hMdef
  have hcoeff : ∀ E, M.coeff E = ((L.coeff E - K.coeff E : ℤ) : ℚ) - B.coeff E := fun E => by
    change (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)) E = _
    simp only [Finsupp.sub_apply, Finsupp.add_apply]
    change (L.coeff E : ℚ) - ((K.coeff E : ℚ) + B.coeff E) = _
    push_cast; ring
  have hround : K + M.roundUp = L := by
    ext E
    change K.coeff E + M.roundUp.coeff E = L.coeff E
    rw [DivisorWithCoeffs.coeff_roundUp, hcoeff, ceil_intCast_sub (hB E) (hB1 E)]
    ring
  have hfract : M.fract.IsSNC sY := by
    refine hsnc.of_support_subset fun E hE => ?_
    rw [Finsupp.mem_support_iff] at hE ⊢
    intro hBE
    apply hE
    change M.fract.coeff E = 0
    rw [DivisorWithCoeffs.coeff_fract, hcoeff]
    change Int.fract (((L.coeff E - K.coeff E : ℤ) : ℚ) - B E) = 0
    rw [hBE, sub_zero, Int.fract_intCast]
  exact hround ▸ isZero_rightDerived_pushforward_divisorialSheaf_canonical_add_roundUp
    sY sZ hY f hfZ hf hK M hM hfract i hi

end MMP.Mori

end

/-! ### `lem_mmp_projective_snc_nef_big_vanishing` -/

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction TopologicalSpace
  Opposite

namespace Proof_lem_mmp_projective_snc_nef_big_vanishing

open MMP.Mori

/-- A sheaf of modules on a scheme which vanishes on every affine open is zero. -/
private theorem isZero_of_forall_isAffineOpen {Z : Scheme.{0}} (M : Z.Modules)
    (h : ∀ V : Z.Opens, IsAffineOpen V → IsZero ((Scheme.Modules.restrictFunctor V.ι).obj M)) :
    IsZero M := by
  let V : Z.affineOpens → Z.Opens := fun U => U.1
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_restrict_cover V ?_ M
    fun U => h U.1 U.2
  exact iSup_affineOpens_eq_top Z

section Leray

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **Degenerate Leray.** If `R^q p_* M = 0` for every `q > 0`, then
`R^i f_*(p_* M) ≅ R^i (p ≫ f)_* M`: the derived direct image `Rp_* M` is concentrated in degree
zero, hence is `p_* M` placed in degree zero, and `R(p ≫ f)_* = Rf_* ∘ Rp_*`. -/
private theorem nonempty_rightDerived_comp_iso {V Y Z : Scheme.{0}} (p : V ⟶ Y) (f : Y ⟶ Z)
    (M : V.Modules)
    (hp : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj M))
    (i : ℕ) :
    Nonempty (((Scheme.Modules.pushforward f).rightDerived i).obj
        ((Scheme.Modules.pushforward p).obj M) ≅
      ((Scheme.Modules.pushforward (p ≫ f)).rightDerived i).obj M) := by
  haveI : PreservesFiniteLimits (Scheme.Modules.pushforward p) := inferInstance
  haveI : (Scheme.Modules.pushforward p).Additive := inferInstance
  haveI : (Scheme.Modules.pushforward f).Additive := inferInstance
  set X := (derivedPushforward p.toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor V.Modules 0).obj M) with hX
  have hH : ∀ q : ℤ, Nonempty ((DerivedCategory.homologyFunctor Y.Modules q).obj X ≅
      ((Scheme.Modules.pushforward p).rightDerivedPlus q).obj M) :=
    fun q => Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso p M q
  have hz : ∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor Y.Modules q).obj X) := by
    intro q hq
    obtain ⟨e⟩ := hH q
    refine IsZero.of_iso ?_ e
    rcases lt_or_gt_of_ne hq with h | h
    · exact Functor.isZero_rightDerivedPlus_of_neg _ M q h
    · obtain ⟨q', rfl⟩ := Int.eq_ofNat_of_zero_le h.le
      exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ q' M).1
        (hp q' (by exact_mod_cast h))
  haveI : X.IsGE 0 := by
    rw [DerivedCategory.isGE_iff]
    intro q hq
    exact hz q hq.ne
  haveI : X.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro q hq
    exact hz q hq.ne'
  obtain ⟨A, ⟨eA⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X 0
  obtain ⟨e0⟩ := hH 0
  have eAM : A ≅ (Scheme.Modules.pushforward p).obj M :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).app A).symm ≪≫
      (DerivedCategory.homologyFunctor Y.Modules 0).mapIso eA.symm ≪≫ e0 ≪≫
      (Stacks.RightDerivedPlus.rightDerivedPlusZeroIso (Scheme.Modules.pushforward p)).app M
  obtain ⟨e1⟩ := Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso
    f A i
  obtain ⟨e2⟩ := Stacks.AffineHigherDirectImage.nonempty_homologyFunctor_derivedPushforward_iso
    (p ≫ f) M i
  exact ⟨((Scheme.Modules.pushforward f).rightDerived i).mapIso eAM.symm ≪≫
    (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) i).app A ≪≫ e1.symm ≪≫
    (DerivedCategory.homologyFunctor Z.Modules i).mapIso
      ((derivedPushforward f.toLRSHom.toShHom).mapIso eA.symm ≪≫
        (derivedPushforwardCompIso p.toLRSHom.toShHom f.toLRSHom.toShHom).app _) ≪≫ e2 ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward (p ≫ f)) i).app M).symm⟩

end Leray

section ResolutionSteps

/-! ### Steps on a log resolution -/

variable {k : Type} [Field k] {Y V : Scheme.{0}} {sY : Y ⟶ Spec (.of k)}
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]

/-- The pull-back of a divisor along a dominant morphism to a smooth scheme, on which every
divisor is Cartier. -/
private noncomputable def pb (hY : IsSmoothScheme sY) (p : V ⟶ Y) [IsDominant p]
    (W : Divisor Y) : Divisor V :=
  W.pullback (MMP.Fourfold.isCartier_of_isSmoothScheme hY W)
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p W)

variable (hY : IsSmoothScheme sY) (p : V ⟶ Y) [IsDominant p]

/-- `pb` is the pull-back of Cartier divisors. -/
private theorem isPullback_pb (W : Divisor Y) :
    W.IsPullback p (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant'
      p W) (pb hY p W) :=
  Divisor.isPullback_pullback _ _

/-- The pull-back is additive. -/
private theorem pb_add (W₁ W₂ : Divisor Y) : pb hY p (W₁ + W₂) = pb hY p W₁ + pb hY p W₂ :=
  Divisor.IsPullback.pullback_eq _ ((isPullback_pb hY p W₁).add
    (MMP.Fourfold.isCartier_of_isSmoothScheme hY W₁)
    (MMP.Fourfold.isCartier_of_isSmoothScheme hY W₂) _ (isPullback_pb hY p W₂))

/-- The pull-back commutes with integer multiples. -/
private theorem pb_zsmul (n : ℤ) (W : Divisor Y) : pb hY p (n • W) = n • pb hY p W :=
  Divisor.IsPullback.pullback_eq _ ((isPullback_pb hY p W).zsmul
    (MMP.Fourfold.isCartier_of_isSmoothScheme hY W) n _)

/-- The pull-back commutes with differences. -/
private theorem pb_sub (W₁ W₂ : Divisor Y) : pb hY p (W₁ - W₂) = pb hY p W₁ - pb hY p W₂ := by
  have h := pb_add hY p (W₁ - W₂) W₂
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-- The pull-back of a divisor is Cartier. -/
private theorem isCartier_pb (W : Divisor Y) : (pb hY p W).IsCartier :=
  MMP.Fourfold.isCartier_of_isPullback p (MMP.Fourfold.isCartier_of_isSmoothScheme hY W)
    (isPullback_pb hY p W)

/-- The pull-back of a divisor has no component over the complement of its support. -/
private theorem coeff_pb_eq_zero (W : Divisor Y) (P : MMP.Mori.PrimeDivisor V)
    (hP : p P.genericPoint ∉ W.supp) : (pb hY p W).coeff P = 0 := by
  let U : Y.Opens := ⟨(W.supp : Set Y)ᶜ, W.supp.isClosed.isOpen_compl⟩
  have hφ : W.IsLocalEquation U 1 := by
    intro E hE
    obtain ⟨x, hxE, hxU⟩ := hE
    have h0 : W.coeff E = 0 :=
      of_not_not fun h => hxU (DivisorWithCoeffs.support_subset_supp h hxE)
    simp [h0]
  have hE : (P.support ∩ p ⁻¹ᵁ U).Nonempty := (P.genericPoint_mem_iff (p ⁻¹ᵁ U)).mp hP
  rw [isPullback_pb hY p W U 1 hφ P hE, pullbackComponent_eq _ _ _ (mem_pointComponent _) 1
    (by simp), map_one, PrimeDivisor.ordUnit_one]

/-- The pull-back of an effective divisor is effective. -/
private theorem isEffective_pb {W : Divisor Y} (hW : W.IsEffective) :
    (pb hY p W).IsEffective :=
  fun P => MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤)
    (MMP.Fourfold.isCartier_of_isSmoothScheme hY W) (fun P _ => hW P) (isPullback_pb hY p W) P
    ((P.genericPoint_mem_iff _).mp trivial)

/-- A `p`-ample divisor stays `p`-ample after adding a pull-back. -/
private theorem isRelativelyAmple_pb_add {H : Divisor V} (hH : H.IsCartier)
    (hHa : H.IsRelativelyAmple p hH) (W : Divisor Y) :
    ∃ h : (pb hY p W + H).IsCartier, (pb hY p W + H).IsRelativelyAmple p h := by
  rw [add_comm]
  exact ⟨_, MMP.Threefold.Resolution.isRelativelyAmple_add_of_isPullback p hH hHa
    (MMP.Fourfold.isCartier_of_isSmoothScheme hY W) (isPullback_pb hY p W) (isCartier_pb hY p W)⟩

end ResolutionSteps

/-- Positive tensor powers of the sheaf of a Cartier divisor. -/
private theorem nonempty_tensorPowModule_iso {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    (H : Divisor X) (hH : H.IsCartier) [Stacks.Ample.IsInvertibleModule X H.divisorialSheaf]
    (n : ℕ) :
    Nonempty (Stacks.Ample.tensorPowModule X H.divisorialSheaf ((n + 1 : ℕ) : ℤ) ≅
      (((n + 1 : ℕ) : ℤ) • H).divisorialSheaf) := by
  induction n with
  | zero => exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by norm_num) ≪≫
      Stacks.Ample.tensorPowModuleOneIso X _ ≪≫
      eqToIso (by rw [Nat.cast_one, one_smul])⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih
    exact ⟨Stacks.RelativeVeryAmple.tensorPowModuleCongr X _ (by push_cast; ring) ≪≫
      (Stacks.Ample.tensorPowModuleAddIso X _ ((n + 1 : ℕ) : ℤ) 1).symm ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso X e (Stacks.Ample.tensorPowModuleOneIso X _) ≪≫
      (hH.zsmul _).divisorialSheafTensorIso hH ≪≫
      eqToIso (by congr 1; push_cast; simp only [add_smul, one_smul])⟩

/-- The two spellings of the pull-back of modules agree. -/
private noncomputable def modulePullbackIso {X X' : Scheme.{0}} (q : X' ⟶ X) (F : X.Modules) :
    (modulePullback q.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback q).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction q.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction q)).app F

/-- **Composite ampleness.** For projective `p : V ⟶ Y` and `f : Y ⟶ Z`, a `p`-ample `H` and an
`f`-ample `G`, the divisor `c p^*G + H` is `(p ≫ f)`-ample for every large `c`. -/
private theorem exists_isRelativelyAmple_zsmul_pb_add {k : Type} [Field k] {Y V Z : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsAffine Z]
    (hY : IsSmoothScheme sY) (p : V ⟶ Y) [IsDominant p] (f : Y ⟶ Z)
    (hp : IsProjectiveMorphism p) (hf : IsProjectiveMorphism f)
    {H : Divisor V} (hH : H.IsCartier) (hHa : H.IsRelativelyAmple p hH)
    {G : Divisor Y} (hG : G.IsCartier) (hGa : G.IsRelativelyAmple f hG) :
    ∃ c₀ : ℕ, ∀ c : ℕ, c₀ ≤ c → ∃ h : ((c : ℤ) • pb hY p G + H).IsCartier,
      ((c : ℤ) • pb hY p G + H).IsRelativelyAmple (p ≫ f) h := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  haveI := hG.isInvertibleModule_divisorialSheaf
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  have hL : Stacks.RelativeAmple.IsRelativelyAmple p H.divisorialSheaf :=
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover p _
      inferInstance).mpr hHa
  have hM : Stacks.RelativeAmple.IsRelativelyAmple f G.divisorialSheaf :=
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover f _
      inferInstance).mpr hGa
  obtain ⟨n, hn⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp p f _ _ hL hM
  refine ⟨n + 1, fun c hc => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  have hc' : ((((m + 1 : ℕ) : ℤ) • pb hY p G + H)).IsCartier :=
    ((isCartier_pb hY p G).zsmul _).add hH
  refine ⟨hc', ?_⟩
  haveI := hc'.isInvertibleModule_divisorialSheaf
  obtain ⟨eG⟩ := nonempty_tensorPowModule_iso G hG m
  have hpbz := pb_zsmul hY p ((m + 1 : ℕ) : ℤ) G
  have e₁ : (Scheme.Modules.pullback p).obj ((((m + 1 : ℕ) : ℤ) • G).divisorialSheaf) ≅
      (((m + 1 : ℕ) : ℤ) • pb hY p G).divisorialSheaf :=
    ((isPullback_pb hY p _).divisorialSheafIso
      (hBc := MMP.Fourfold.isCartier_of_isSmoothScheme hY _)).symm ≪≫ eqToIso (by rw [hpbz])
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule p H.divisorialSheaf
      G.divisorialSheaf (m + 1) ≅ (((m + 1 : ℕ) : ℤ) • pb hY p G + H).divisorialSheaf :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso V (Iso.refl _)
        ((modulePullback p.toLRSHom.toShHom).mapIso eG ≪≫ modulePullbackIso p _ ≪≫ e₁) ≪≫
      hH.divisorialSheafTensorIso ((isCartier_pb hY p G).zsmul _) ≪≫ eqToIso (by rw [add_comm])
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (hn (m + 1) (by omega)))

section Kleiman

/-- Relative ampleness of an invertible sheaf depends only on its isomorphism class. -/
private theorem isRelativelyAmple_of_iso {X Y : Scheme.{0}} (f : X ⟶ Y) {L L' : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] [Stacks.Ample.IsInvertibleModule X L'] (e : L ≅ L')
    (h : MMP.Mori.IsRelativelyAmple f L) : MMP.Mori.IsRelativelyAmple f L' := by
  intro y
  obtain ⟨V, hV, hyV, hamp⟩ := h y
  refine ⟨V, hV, hyV, ?_⟩
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V).ι.toLRSHom.toShHom).mapIso e)).1 hamp

variable {k : Type} [Field k] {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (f : Y ⟶ Z)

/-- The intersection number with a Cartier divisor is the degree of its invertible sheaf. -/
private theorem intersectionNumber_ofCartier_eq_degree (E : Y.CartierDivisor) :
    RelativeNumericalCurveClasses.intersectionNumber (sX := sY) (f := f)
        (KCartierDivisor.ofCartier ℝ E) =
      RelativeNumericalCurveClasses.degree sY f (MMP.CartierDivisor.sheaf E) := by
  apply Submodule.linearMap_qext
  ext Z
  exact OneCycle.intersectionNumber_ofCartier Z.1 E

/-- The degree form depends only on the isomorphism class of the sheaf. -/
private theorem degree_congr {L L' : Y.Modules}
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L'] (e : L ≅ L') :
    RelativeNumericalCurveClasses.degree sY f L = RelativeNumericalCurveClasses.degree sY f L' := by
  apply Submodule.linearMap_qext
  ext Z
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  change OneCycle.degree ℝ sY L Z.1 = OneCycle.degree ℝ sY L' Z.1
  rw [OneCycle.degree_apply, OneCycle.degree_apply]
  refine Finsupp.sum_congr fun C _ => ?_
  rw [MMP.ProgramBaseChange.degree_congr C e]

variable [IsLocallyNoetherian Y] [IsNormal Y] [QuasiCompact sY]

/-- The degree of `𝒪_Y(D)` on the class of a contracted curve is the degree of `D` on it. -/
private theorem degree_relativeClass_divisorialSheaf (D : Divisor Y) (hD : D.IsCartier)
    (C : ProperCurve sY) (hC : C.IsContractedBy f) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := hD.isInvertibleModule_divisorialSheaf
    RelativeNumericalCurveClasses.degree sY f D.divisorialSheaf (C.relativeClass f hC) =
      (D.degreeOn k sY C.ι C.dim_le hD : ℝ) := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := hD.isInvertibleModule_divisorialSheaf
  rw [ProperCurve.relativeClass, RelativeNumericalCurveClasses.degree_relativeNumericalClass,
    OneCycle.degree_apply]
  change ((C.cycle ℝ).sum fun C a => a * (C.degree k D.divisorialSheaf : ℝ)) = _
  rw [ProperCurve.cycle, Finsupp.sum_single_index (by simp), one_mul,
    ProperCurve.degree_divisorialSheaf]

/-- The degree form is additive on Cartier divisors. -/
private theorem degree_divisorialSheaf_add (D₁ D₂ : Divisor Y) (h₁ : D₁.IsCartier)
    (h₂ : D₂.IsCartier) :
    haveI := QuasiCompact.compactSpace_of_compactSpace sY
    haveI := h₁.isInvertibleModule_divisorialSheaf
    haveI := h₂.isInvertibleModule_divisorialSheaf
    haveI := (h₁.add h₂).isInvertibleModule_divisorialSheaf
    RelativeNumericalCurveClasses.degree sY f (D₁ + D₂).divisorialSheaf =
      RelativeNumericalCurveClasses.degree sY f D₁.divisorialSheaf +
        RelativeNumericalCurveClasses.degree sY f D₂.divisorialSheaf := by
  haveI := QuasiCompact.compactSpace_of_compactSpace sY
  haveI := h₁.isInvertibleModule_divisorialSheaf
  haveI := h₂.isInvertibleModule_divisorialSheaf
  haveI := (h₁.add h₂).isInvertibleModule_divisorialSheaf
  apply Submodule.linearMap_qext
  ext Z
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.add_apply]
  change OneCycle.degree ℝ sY _ Z.1 = OneCycle.degree ℝ sY _ Z.1 + OneCycle.degree ℝ sY _ Z.1
  rw [OneCycle.degree_apply, OneCycle.degree_apply, OneCycle.degree_apply, ← Finsupp.sum_add]
  refine Finsupp.sum_congr fun C _ => ?_
  rw [ProperCurve.degree_divisorialSheaf C (D₁ + D₂) (h₁.add h₂),
    ProperCurve.degree_divisorialSheaf C D₁ h₁, ProperCurve.degree_divisorialSheaf C D₂ h₂,
    Divisor.degreeOn_add k sY C.ι C.dim_le D₁ D₂ h₁ h₂]
  push_cast
  ring

/-- A degree form nonnegative on contracted curves is nonnegative on the closed cone. -/
private theorem degree_nonneg_of_mem_relativeClosedConeOfCurves (L : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L]
    (h : ∀ (C : ProperCurve sY) (hC : C.IsContractedBy f),
      0 ≤ RelativeNumericalCurveClasses.degree sY f L (C.relativeClass f hC))
    {z : RelativeNumericalCurveClasses sY f} (hz : z ∈ relativeClosedConeOfCurves sY f) :
    0 ≤ RelativeNumericalCurveClasses.degree sY f L z := by
  have hcl : IsClosed {z : RelativeNumericalCurveClasses sY f |
      0 ≤ RelativeNumericalCurveClasses.degree sY f L z} :=
    isClosed_le continuous_const (RelativeNumericalCurveClasses.continuous_degree sY f L)
  have hsub : (relativeConeOfCurves sY f : Set (RelativeNumericalCurveClasses sY f)) ⊆
      {z | 0 ≤ RelativeNumericalCurveClasses.degree sY f L z} := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact h C hC
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      linarith
    | smul a x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg a.2 hx
  rw [← SetLike.mem_coe, coe_relativeClosedConeOfCurves] at hz
  exact closure_minimal hsub hcl hz

/-- The term of the nef condition for `D` on a curve `C` is `(1 / m) deg_C (m D)`, for `m` the
Cartier index of `D`. -/
private theorem sum_associatedCartier_degreeOn {D : QDivisor Y} (hD : D.IsQCartier)
    (C : ProperCurve sY) :
    (D.associatedCartier hD).sum (fun E c =>
      (c : ℝ) * ((E : Divisor Y).degreeOn k sY C.ι C.dim_le E.2 : ℝ)) =
      (((1 / (D.cartierIndex hD : ℚ)) : ℚ) : ℝ) *
        ((D.cartierIndexSMul hD : Divisor Y).degreeOn k sY C.ι C.dim_le
          (D.cartierIndexSMul hD).2 : ℝ) := by
  rw [QDivisor.associatedCartier, CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single,
    smul_eq_mul, mul_one, Finsupp.sum_single_index (by simp)]

/-- Integral multiples `N = m D` and `m' D`, for `m'` the Cartier index of `D`, have proportional
degrees: `m deg_C (m' D) = m' deg_C N`. -/
private theorem mul_degreeOn_cartierIndexSMul {D : QDivisor Y} (hD : D.IsQCartier) {m : ℕ}
    {N : Divisor Y} (hN : Divisor.toQDivisor N = (m : ℚ) • D) (hNc : N.IsCartier)
    (C : ProperCurve sY) :
    (m : ℤ) * (D.cartierIndexSMul hD : Divisor Y).degreeOn k sY C.ι C.dim_le
        (D.cartierIndexSMul hD).2 = (D.cartierIndex hD : ℤ) * N.degreeOn k sY C.ι C.dim_le hNc := by
  have hkey : (m : ℤ) • (D.cartierIndexSMul hD : Divisor Y) = (D.cartierIndex hD : ℤ) • N := by
    apply Divisor.toQDivisor_injective
    ext P
    have h1 := congrArg (fun G : QDivisor Y => G.coeff P) hN
    have h2 := congrArg (fun G : QDivisor Y => G.coeff P)
      (QDivisor.toQDivisor_cartierIndexSMul D hD)
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      zsmul_eq_mul] at h1 h2 ⊢
    push_cast
    rw [h1, h2]
    push_cast
    ring
  have h := Divisor.degreeOn_zsmul' k sY C.ι C.dim_le _ (D.cartierIndexSMul hD).2 (m : ℤ)
  rw [Divisor.degreeOn_congr hkey _ (hNc.zsmul _)] at h
  exact h.symm.trans (Divisor.degreeOn_zsmul' k sY C.ι C.dim_le N hNc _)

/-- An integral multiple `D_N = N D` of an `f`-nef `ℚ`-divisor has nonnegative degree on every
contracted curve. -/
private theorem degreeOn_nonneg_of_isRelativelyNef {D : QDivisor Y} (hnef : D.IsRelativelyNef sY f)
    {N : ℕ} {DN : Divisor Y} (hDN : Divisor.toQDivisor DN = (N : ℚ) • D) (hDNc : DN.IsCartier)
    (C : ProperCurve sY) (hC : C.IsContractedBy f) :
    0 ≤ DN.degreeOn k sY C.ι C.dim_le hDNc := by
  obtain ⟨hD, hn⟩ := hnef
  have h0 := hn C hC
  rw [sum_associatedCartier_degreeOn] at h0
  have hm := QDivisor.cartierIndex_pos hD
  have hE : 0 ≤ (D.cartierIndexSMul hD : Divisor Y).degreeOn k sY C.ι C.dim_le
      (D.cartierIndexSMul hD).2 := by
    have hpos : (0 : ℝ) < ((1 / (D.cartierIndex hD : ℚ) : ℚ) : ℝ) := by
      exact_mod_cast one_div_pos.2 (Nat.cast_pos.2 hm)
    exact_mod_cast nonneg_of_mul_nonneg_right h0 hpos
  have := mul_degreeOn_cartierIndexSMul sY hD hDN hDNc C
  have hm' : (0 : ℤ) < D.cartierIndex hD := by exact_mod_cast hm
  nlinarith

/-- Conversely, a `ℚ`-Cartier `ℚ`-divisor with a positive integral multiple of nonnegative degree
on every contracted curve is relatively nef. -/
private theorem isRelativelyNef_of_degreeOn_nonneg {D : QDivisor Y} (hD : D.IsQCartier) {m : ℕ}
    (hm : 0 < m) {N : Divisor Y} (hN : Divisor.toQDivisor N = (m : ℚ) • D) (hNc : N.IsCartier)
    (h : ∀ C : ProperCurve sY, C.IsContractedBy f → 0 ≤ N.degreeOn k sY C.ι C.dim_le hNc) :
    D.IsRelativelyNef sY f := by
  refine ⟨hD, fun C hC => ?_⟩
  rw [sum_associatedCartier_degreeOn]
  have := mul_degreeOn_cartierIndexSMul sY hD hN hNc C
  have hN0 := h C hC
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hE : 0 ≤ (D.cartierIndexSMul hD : Divisor Y).degreeOn k sY C.ι C.dim_le
      (D.cartierIndexSMul hD).2 := by nlinarith
  exact mul_nonneg (by positivity) (by exact_mod_cast hE)

end Kleiman

/-- **Nef plus ample is ample.** On a projective morphism of varieties in characteristic zero, an
`f`-nef `ℚ`-divisor `D` whose multiple `N D` is a Cartier divisor `D_N`, plus an `f`-ample
Cartier divisor `A`, is `f`-ample; this is the relative Kleiman criterion. -/
private theorem isRelativelyAmple_add_of_isRelativelyNef
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY) (hf : IsProjectiveMorphism f)
    {D : QDivisor Y} (hnef : D.IsRelativelyNef sY f) {N : ℕ} {DN : Divisor Y}
    (hDN : Divisor.toQDivisor DN = (N : ℚ) • D) (hDNc : DN.IsCartier)
    {A : Divisor Y} (hA : A.IsCartier) (hAamp : A.IsRelativelyAmple f hA) :
    ∃ h : (DN + A).IsCartier, (DN + A).IsRelativelyAmple f h := by
  have hGc : (DN + A).IsCartier := hDNc.add hA
  refine ⟨hGc, ?_⟩
  haveI := hGc.isInvertibleModule_divisorialSheaf
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hDNc.isInvertibleModule_divisorialSheaf
  have hfp : IsProjective f := hf.isProjective
  obtain ⟨EA, ⟨eA⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf A.divisorialSheaf
  obtain ⟨EG, ⟨eG⟩⟩ :=
    MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (DN + A).divisorialSheaf
  have hA' : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf EA) :=
    isRelativelyAmple_of_iso f eA hAamp
  have hApos := (isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos
    sZ sY f hfp hfZ EA).1 hA'
  have hDNcone : ∀ z ∈ relativeClosedConeOfCurves sY f,
      0 ≤ RelativeNumericalCurveClasses.degree sY f DN.divisorialSheaf z := fun z hz =>
    degree_nonneg_of_mem_relativeClosedConeOfCurves sY f _ (fun C hC => by
      rw [degree_relativeClass_divisorialSheaf sY f DN hDNc C hC]
      exact_mod_cast degreeOn_nonneg_of_isRelativelyNef sY f hnef hDN hDNc C hC) hz
  refine isRelativelyAmple_of_iso f eG.symm
    ((isRelativelyAmple_cartierSheaf_iff_forall_relativeClosedConeOfCurves_pos
      sZ sY f hfp hfZ EG).2 fun z hz hz0 => ?_)
  have h1 := hApos z hz hz0
  rw [intersectionNumber_ofCartier_eq_degree, ← degree_congr sY f eA] at h1
  rw [intersectionNumber_ofCartier_eq_degree, ← degree_congr sY f eG,
    degree_divisorialSheaf_add sY f DN A hDNc hA, LinearMap.add_apply]
  linarith [hDNcone z hz]

/-- **A log resolution.** A smooth variety `Y` has a projective log resolution `p : V ⟶ Y` of
a `ℚ`-divisor `G`: `V` is smooth, and the exceptional divisors and the divisors over `Supp G` are
the components of one snc divisor. -/
private theorem exists_logResolution {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] [IsNormal Y]
    (G : QDivisor Y) :
    ∃ (V : Scheme.{0}) (p : V ⟶ Y) (_ : IsIntegral V) (_ : IsLocallyNoetherian V)
      (_ : IsNormal V) (_ : CompactSpace V), AlgebraicGeometry.IsVariety k (p ≫ sY) ∧
      IsSmoothScheme (p ≫ sY) ∧ IsProjectiveMorphism p ∧ IsBirationalMorphism p ∧ IsProper p ∧
      ∃ s : Finset (MMP.Mori.PrimeDivisor V),
        DivisorWithCoeffs.IsSNC (p ≫ sY) (∑ P ∈ s, Finsupp.single P (1 : ℤ)) ∧
        ∀ P : MMP.Mori.PrimeDivisor V, (RationalMap.IsExceptional (X := V) p.toRationalMap P ∨
          p P.genericPoint ∈ G.supp) → P ∈ s := by
  have hY : IsNormalVariety k sY := ⟨‹_›, ‹_›⟩
  obtain ⟨V, p, hlog, hproj⟩ :=
    MMP.Mori.exists_isLogResolution_isProjectiveMorphism sY hY (QDivisor.toRDivisor G)
  obtain ⟨hW, -, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hY
  haveI : IsIntegral V := hW.1.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sY) := hW.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sY)
  haveI : IsNormal V := hW.2
  haveI : AlgebraicGeometry.IsVariety k (p ≫ sY) := hW.1
  haveI : QuasiCompact (p ≫ sY) := hW.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sY)
  haveI : LocallyOfFinitePresentation (p ≫ sY) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  have hη : ∀ P : MMP.Mori.PrimeDivisor V, P.genericPoint ∈ P.support :=
    MMP.Flips.primeDivisor_genericPoint_mem_support
  have hmem : ∀ P : MMP.Mori.PrimeDivisor V, (RationalMap.IsExceptional (X := V) p.toRationalMap P ∨
      p P.genericPoint ∈ G.supp) → P.genericPoint ∈
        ((exceptionalSet p ⊔ (QDivisor.toRDivisor G).supp.preimage p.continuous : Closeds V) :
          Set V) := by
    intro P hP
    rcases hP with h | h
    · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet P h (hη P))
    · refine Or.inr ?_
      change p P.genericPoint ∈ (QDivisor.toRDivisor G).supp
      rwa [QDivisor.supp_toRDivisor]
  refine ⟨V, p, inferInstance, inferInstance, inferInstance, inferInstance, hW.1,
    hlog.isSmoothScheme, hproj, hlog.isBirationalMorphism, hlog.isProper, ?_⟩
  rcases hlog.isSNCSubset with h | ⟨s, hs, hsnc⟩
  · refine ⟨∅, ?_, fun P hP => ?_⟩
    · simpa using DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℤ) (p ≫ sY)
        hlog.isSmoothScheme
    · have := hmem P hP
      rw [h] at this
      exact absurd this (by simp)
  · refine ⟨s, hsnc, fun P hP => ?_⟩
    have hP' := hmem P hP
    rw [← hs] at hP'
    obtain ⟨E, hE, hPE⟩ := Set.mem_iUnion₂.mp hP'
    have hEP := MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support hPE
    subst hEP
    exact hE

/-- The divisor of a nonzero rational top form on a smooth variety is canonical. -/
private theorem isCanonicalDivisor_divisorOfForm {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sX]
    (hXs : IsSmoothScheme sX) [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {n : ℕ} (hn : topologicalKrullDim X = n) {τ : RationalPluriForms sX n 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n := by
  obtain ⟨K, hK⟩ := exists_isCanonicalDivisor_of_isSmoothScheme sX hXs hn
  exact hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul ⟨‹_›, inferInstance⟩ hK hτ

/-- A canonical divisor lifts along a proper birational morphism from a smooth variety. -/
private theorem exists_isCanonicalDivisor_transformDivisor_eq {k : Type} [Field k]
    [PerfectField k] {Y Y' : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] [IsIntegral Y']
    [IsLocallyNoetherian Y'] [IsNormal Y'] [CompactSpace Y'] (hY : IsNormalVariety k sY)
    (f : Y' ⟶ Y) [IsProper f] (hY' : IsNormalVariety k (f ≫ sY))
    (hs : IsSmoothScheme (f ≫ sY)) (hf : IsBirationalMorphism f) {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) :
    ∃ K' : Divisor Y', K'.IsCanonicalDivisor (f ≫ sY) n ∧
      RationalMap.transformDivisor (X := Y') f.toRationalMap K' = K := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hY hK
  haveI : LocallyOfFiniteType (f ≫ sY) := hY'.1.toLocallyOfFiniteType
  haveI := hf.isDominant
  haveI : AlgebraicGeometry.IsVariety k sY := hY.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sY) := hY'.1
  have hbij := hf.functionFieldMap_bijective
  have hdim : topologicalKrullDim Y' = n := by
    rw [← hK.topologicalKrullDim_eq]
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (f ≫ sY) hf).symm
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
    hK.topologicalKrullDim_eq
  refine ⟨divisorOfForm (pullbackRationalPluriForms sY f ω),
    isCanonicalDivisor_divisorOfForm hs hdim
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f hbij hd hω0), ?_⟩
  refine Finsupp.ext fun Γ => ?_
  obtain ⟨E, heq, hiso, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hY' hf Γ
  rw [htr]
  change E.ordForm (pullbackRationalPluriForms sY f ω) = K.coeff Γ
  rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hbij hd E Γ heq ω, hω Γ]

/-- A component of an inverse transform is the transform of a component. -/
private theorem exists_of_inverseTransformDivisor_ne_zero {Y V : Scheme.{0}} (p : V ⟶ Y)
    (B : QDivisor Y) (P : MMP.Mori.PrimeDivisor V) (h : inverseTransformDivisor p B P ≠ 0) :
    ∃ D : MMP.Mori.PrimeDivisor Y, B D ≠ 0 ∧ inverseTransformPrimeDivisor p D = some P := by
  classical
  induction B using Finsupp.induction with
  | zero => simp at h
  | single_add a b f ha hb ih =>
    rw [map_add, Finsupp.add_apply] at h
    by_cases hf0 : inverseTransformDivisor p f P = 0
    · rw [hf0, add_zero] at h
      refine ⟨a, by simp [Finsupp.notMem_support_iff.mp ha, hb], ?_⟩
      rw [inverseTransformDivisor_single] at h
      cases hφ : inverseTransformPrimeDivisor p a with
      | none => rw [hφ] at h; simp at h
      | some E =>
        rw [hφ] at h
        have hE : E = P := by
          by_contra hEP
          exact h (Finsupp.single_eq_of_ne (Ne.symm hEP))
        rw [hE]
    · obtain ⟨D, hD, hDP⟩ := ih hf0
      refine ⟨D, ?_, hDP⟩
      have hDa : D ≠ a := by
        rintro rfl
        exact hD (Finsupp.notMem_support_iff.mp ha)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hDa, zero_add]
      exact hD

/-- **The crepant boundary on a resolution of a klt snc pair.** There are a canonical divisor
`K_V` and a `ℚ`-divisor `Γ` with `K_V + Γ = p^*(K + B)`, `⌈-Γ⌉` effective and exceptional, and
every component of `Γ` exceptional or over `Supp B`. -/
private theorem exists_crepantBoundary {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y V : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (hY : IsSmoothScheme sY) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : DivisorWithCoeffs.IsSNC sY B)
    (hB1 : ∀ E : MMP.Mori.PrimeDivisor Y, B.coeff E < 1)
    (p : V ⟶ Y) [IsDominant p] [IsProper p] (hV : AlgebraicGeometry.IsVariety k (p ≫ sY))
    (hVs : IsSmoothScheme (p ≫ sY)) (hp : IsBirationalMorphism p)
    {M : ℕ} (hM : 0 < M) {BM : Divisor Y} (hBM : Divisor.toQDivisor BM = (M : ℚ) • B) :
    ∃ KV : Divisor V, KV.IsCanonicalDivisor (p ≫ sY) n ∧ ∃ Γ : QDivisor V,
      (-Γ).roundUp.IsEffective ∧
      (∀ P, (-Γ).roundUp.coeff P ≠ 0 → RationalMap.IsExceptional (X := V) p.toRationalMap P) ∧
      (∀ P, Γ.coeff P ≠ 0 →
        RationalMap.IsExceptional (X := V) p.toRationalMap P ∨ p P.genericPoint ∈ B.supp) ∧
      Divisor.toQDivisor (pb hY p ((M : ℤ) • K + BM)) =
        (M : ℚ) • (Divisor.toQDivisor KV + Γ) := by
  haveI := hV
  have hYn : IsNormalVariety k sY := ⟨‹_›, ‹_›⟩
  have hVn : IsNormalVariety k (p ≫ sY) := ⟨hV, ‹_›⟩
  have hklt := isKltPair_of_isSNC sY hYn hY hK hsnc hB1
  have hP : IsPair sY B := hklt.1.isPair
  obtain ⟨KV, hKV, hKVt⟩ := exists_isCanonicalDivisor_transformDivisor_eq hYn p hVn hVs hp hK
  obtain ⟨⟨Γ, hΓ, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hP hK p hVn hp
  obtain ⟨hQe, hQx⟩ := MMP.Positivity.IsKltPair.isEffective_roundUp_neg_of_isCrepantBoundary hklt hB
    hVn hp hΓ
  obtain ⟨hpb1, -, -⟩ := IsPair.isPullback_of_isCrepantBoundary hP p hVn hp hK hKV
    (Or.inr ⟨inferInstance, hKVt⟩) hΓ
  have hDM : Divisor.toQDivisor ((M : ℤ) • K + BM) = ((M : ℕ) : ℤ) • (Divisor.toQDivisor K + B) := by
    ext P
    have h1 := congrArg (fun G : QDivisor Y => G.coeff P) hBM
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      smul_eq_mul, zsmul_eq_mul] at h1 ⊢
    push_cast
    rw [h1]
    ring
  obtain ⟨DY, hDY, -, hB', hDYpb⟩ := hpb1 M hM ((M : ℤ) • K + BM) hDM
    (MMP.Fourfold.isCartier_of_isSmoothScheme hY _)
  have hDYeq : pb hY p ((M : ℤ) • K + BM) = DY :=
    Divisor.IsPullback.pullback_eq _ hDYpb
  obtain ⟨hΓeq, -⟩ := IsCrepantBoundary.eq_inverseTransformDivisor_add_exceptional hP hΓ
  refine ⟨KV, hKV, Γ, hQe, hQx, fun P hP0 => ?_, ?_⟩
  · by_cases hPx : RationalMap.IsExceptional (X := V) p.toRationalMap P
    · exact Or.inl hPx
    · refine Or.inr ?_
      have h1 : inverseTransformDivisor p B P ≠ 0 := by
        intro h0
        apply hP0
        have := congrArg (fun G : QDivisor V => G P) hΓeq
        simp only [Finsupp.add_apply, Finsupp.filter_apply, hPx, if_false, h0, add_zero] at this
        exact this
      obtain ⟨D, hD, hDP⟩ := exists_of_inverseTransformDivisor_ne_zero p B P h1
      have hsub : P.support ⊆ p ⁻¹' (D.support : Set Y) := by
        rw [support_inverseTransformPrimeDivisor hDP]
        refine closure_minimal (fun x hx => hx.1) ?_
        exact (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure :
          IsClosed (D.support : Set Y)).preimage p.continuous
      exact DivisorWithCoeffs.support_subset_supp hD (hsub (MMP.Flips.primeDivisor_genericPoint_mem_support P))
  · rw [hDYeq, hDY, natCast_zsmul, Nat.cast_smul_eq_nsmul]

/-- **An effective exceptional divisor with `p`-ample negative**, on a projective birational
morphism onto a smooth variety. -/
private theorem exists_isRelativelyAmple_neg {k : Type} [Field k] {Y V : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (hY : IsSmoothScheme sY) (p : V ⟶ Y) (hV : MMP.Mori.IsNormalVariety k (p ≫ sY))
    (hp : IsProjectiveMorphism p) (hpb : IsBirationalMorphism p) :
    ∃ J : Divisor V, J.IsEffective ∧
      (∀ P, J.coeff P ≠ 0 → RationalMap.IsExceptional (X := V) p.toRationalMap P) ∧
      ∃ h : (-J).IsCartier, (-J).IsRelativelyAmple p h := by
  have hQ : MMP.Fourfold.IsQFactorial sY :=
    ⟨⟨‹_›, ‹_›⟩, fun D => ⟨1, one_pos, by
      rw [Nat.cast_one, one_smul]; exact MMP.Fourfold.isCartier_of_isSmoothScheme hY D⟩⟩
  obtain ⟨F, e, he, hF, hFx, D, hD, hDF, hDa⟩ :=
    exists_isRelativelyAmple_neg_smul_of_isExceptional sY (p ≫ sY) hQ hV p rfl hp hpb
  have hcoeff : ∀ P, (D.coeff P : ℚ) = e * F.coeff P := by
    intro P
    have := congrArg (fun G : QDivisor V => G.coeff P) hDF
    simpa [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul] using this
  refine ⟨D, fun P => ?_, fun P hP => hFx P fun h0 => hP ?_, hD.neg, hDa⟩
  · have h1 := hcoeff P
    have h2 : (0 : ℚ) ≤ F.coeff P := hF P
    have : (0 : ℚ) ≤ D.coeff P := by rw [h1]; positivity
    exact_mod_cast this
  · have h1 := hcoeff P
    have h0' : F.coeff P = 0 := h0
    rw [h0', mul_zero] at h1
    exact_mod_cast h1

/-- For finitely many indices with `b i < 1`, `b i + a i / t < 1` for every large `t`. -/
private theorem exists_forall_add_div_lt_one {ι : Type*} (S : Finset ι) (b a : ι → ℚ)
    (hb : ∀ i, b i < 1) : ∃ T : ℕ, ∀ t : ℕ, T ≤ t → ∀ i ∈ S, b i + a i / t < 1 := by
  have h : ∀ i ∈ S, ∀ᶠ t : ℕ in Filter.atTop, b i + a i / t < 1 := by
    intro i _
    have h : Filter.Tendsto (fun t : ℕ => b i + a i / (t : ℚ)) Filter.atTop (nhds (b i + 0)) :=
      tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat (a i))
    rw [add_zero] at h
    exact h.eventually (gt_mem_nhds (hb i))
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 ((Filter.eventually_all_finset S).2 h)
  exact ⟨T, fun t ht i hi => hT t ht i hi⟩

/-- The coefficient identity behind the first gap. -/
private theorem gap₁_coeff (a k d e α κ γ q j M c j₁ r t : ℚ) (hM : M ≠ 0) (hc : c ≠ 0)
    (ht0 : t ≠ 0) (ht : t = M * j₁ + r) (hk : k = M * (κ + γ)) (hd : d = M * a - k)
    (hr : r * d = M * α + M * e) :
    c * (j₁ * d + α) + -j = c * t * ((a + q) - (κ + (γ + q +
      t⁻¹ * e + (c * t)⁻¹ * j))) := by
  have hγ : γ = k / M - κ := by field_simp; linarith
  have hα : α = (r * d - M * e) / M := by field_simp; linarith
  rw [hγ, hα]
  field_simp
  rw [ht, hd]
  ring

/-- The coefficient identity behind the second gap. -/
private theorem gap₂_coeff (a k d κ γ q j M j₂ : ℚ) (hM : M ≠ 0) (hj : j₂ ≠ 0)
    (hk : k = M * (κ + γ)) (hd : d = M * a - k) :
    j₂ * d + -j = M * j₂ * ((a + q) - (κ + (γ + q + (M * j₂)⁻¹ * j))) := by
  have hγ : γ = k / M - κ := by field_simp; linarith
  rw [hγ]
  field_simp
  rw [hd]
  ring

/-- **Resolution data.** Given `rD = A + E`, a log resolution `p : V ⟶ Y` of `B + E` carries a
Cartier divisor `L' = p^*L + Q` with `p_* 𝒪_V(L') = 𝒪_Y(L)` and two klt snc boundaries `F₁`, `F₂`
whose gaps `L' - (K_V + F₁)` and `L' - (K_V + F₂)` are `(p ≫ f)`-ample and `p`-ample. -/
private theorem exists_resolutionData
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [IsAffine Z] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY)
    (hf : IsProjectiveMorphism f) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : DivisorWithCoeffs.IsSNC sY B)
    (hB1 : ∀ E : MMP.Mori.PrimeDivisor Y, B.coeff E < 1) {L : Divisor Y} (hL : L.IsCartier)
    (hnef : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyNef sY f)
    {r : ℕ} (hr : 0 < r) {A E : Divisor Y} (hA : A.IsCartier) (hAamp : A.IsRelativelyAmple f hA)
    (hE : E.IsEffective)
    (hdec : Divisor.toQDivisor A + Divisor.toQDivisor E =
      (r : ℚ) • (Divisor.toQDivisor L - (Divisor.toQDivisor K + B))) :
    ∃ (V : Scheme.{0}) (sV : V ⟶ Spec (.of k)) (p : V ⟶ Y) (_ : AlgebraicGeometry.IsVariety k sV)
      (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V) (_ : CompactSpace V),
      IsSmoothScheme sV ∧ p ≫ sY = sV ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism (p ≫ f) ∧
      ∃ KV : Divisor V, KV.IsCanonicalDivisor sV n ∧
      ∃ (L' : Divisor V) (_ : L'.IsCartier),
        Nonempty ((Scheme.Modules.pushforward p).obj L'.divisorialSheaf ≅ L.divisorialSheaf) ∧
      ∃ F₁ F₂ : QDivisor V,
        F₁.IsEffective ∧ DivisorWithCoeffs.IsSNC sV F₁ ∧ (∀ P : MMP.Mori.PrimeDivisor V, F₁.coeff P < 1) ∧
        (Divisor.toQDivisor L' - (Divisor.toQDivisor KV + F₁)).HasRelativelyAmpleMultiple (p ≫ f) ∧
        F₂.IsEffective ∧ DivisorWithCoeffs.IsSNC sV F₂ ∧ (∀ P : MMP.Mori.PrimeDivisor V, F₂.coeff P < 1) ∧
        (Divisor.toQDivisor L' - (Divisor.toQDivisor KV + F₂)).HasRelativelyAmpleMultiple p := by
  classical
  haveI : AlgebraicGeometry.IsVariety k sY := ‹_›
  set D : QDivisor Y := Divisor.toQDivisor L - (Divisor.toQDivisor K + B) with hDdef
  -- an integral multiple of `B`
  obtain ⟨M, hM, BM, hBMz, -⟩ := (MMP.Fourfold.isQCartier_of_isSmoothScheme hY B).exists_pos
  have hBM : Divisor.toQDivisor BM = (M : ℚ) • B := by
    rw [hBMz, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  -- the log resolution
  obtain ⟨V, p, _, _, _, _, hVv, hVs, hpp, hpb, hpprop, s, hs, hsmem⟩ :=
    exists_logResolution sY (B + Divisor.toQDivisor E)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsProper p := hpprop
  obtain ⟨KV, hKV, Γ, hQe, hQx, hΓs, hΓ⟩ :=
    exists_crepantBoundary sY hY hK hB hsnc hB1 p hVv hVs hpb hM hBM
  obtain ⟨J, hJe, hJx, hJc, hJa⟩ := exists_isRelativelyAmple_neg sY hY p ⟨hVv, ‹_›⟩ hpp hpb
  set Q : Divisor V := (-Γ).roundUp with hQdef
  set F : QDivisor V := Γ + Divisor.toQDivisor Q with hFdef
  set DM : Divisor Y := (M : ℤ) • L - ((M : ℤ) • K + BM) with hDMdef
  have hrDM : (r : ℤ) • DM = (M : ℤ) • A + (M : ℤ) • E := by
    apply Divisor.toQDivisor_injective
    ext P
    have h1 := congrArg (fun G : QDivisor Y => G.coeff P) hBM
    have h2 := congrArg (fun G : QDivisor Y => G.coeff P) hdec
    simp only [hDMdef, hDdef, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h1 h2 ⊢
    push_cast
    rw [h1]
    linear_combination (-(M : ℚ)) * h2
  -- coefficientwise facts on `V`
  have hF01 : ∀ P, 0 ≤ F.coeff P ∧ F.coeff P < 1 := by
    intro P
    simp only [hFdef, hQdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor,
      DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_neg]
    exact ⟨by linarith [Int.le_ceil (-Γ.coeff P)], by linarith [Int.ceil_lt_add_one (-Γ.coeff P)]⟩
  have hpbE := isEffective_pb hY p hE
  set S : Finset (MMP.Mori.PrimeDivisor V) := (pb hY p E).support ∪ J.support ∪ F.support
    with hSdef
  -- the parameters
  obtain ⟨T₁, hT₁⟩ := exists_forall_add_div_lt_one S F.coeff
    (fun P => ((pb hY p E).coeff P : ℚ) + (J.coeff P : ℚ)) (fun P => (hF01 P).2)
  obtain ⟨T₂, hT₂⟩ := exists_forall_add_div_lt_one S F.coeff
    (fun P => (J.coeff P : ℚ)) (fun P => (hF01 P).2)
  set j₁ : ℕ := T₁ + 1 with hj₁
  set t : ℕ := M * j₁ + r with htdef
  have htT : T₁ ≤ t := by
    have : j₁ ≤ M * j₁ := Nat.le_mul_of_pos_left _ hM
    omega
  have ht0 : (t : ℚ) ≠ 0 := by
    have : 0 < t := by omega
    exact_mod_cast this.ne'
  set DN : Divisor Y := (j₁ : ℤ) • DM with hDNdef
  have hDN : Divisor.toQDivisor DN = ((M * j₁ : ℕ) : ℚ) • D := by
    ext P
    have h1 := congrArg (fun G : QDivisor Y => G.coeff P) hBM
    simp only [hDNdef, hDMdef, hDdef, Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h1 ⊢
    push_cast
    rw [h1]
    ring
  obtain ⟨hGc, hGa⟩ := isRelativelyAmple_add_of_isRelativelyNef sY sZ f hfZ hf hnef hDN
    (MMP.Fourfold.isCartier_of_isSmoothScheme hY DN) hA hAamp
  obtain ⟨c₀, hc₀⟩ := exists_isRelativelyAmple_zsmul_pb_add hY p f hpp hf hJc hJa hGc hGa
  set c : ℕ := c₀ + 1 with hcdef
  obtain ⟨hW₁c, hW₁a⟩ := hc₀ c (by omega)
  have hc0 : (c : ℚ) ≠ 0 := by positivity
  have hc1 : (1 : ℚ) ≤ c := by exact_mod_cast (by omega : 1 ≤ c)
  set j₂ : ℕ := T₂ + 1 with hj₂
  set m₂ : ℕ := M * j₂ with hm₂
  have hm₂T : T₂ ≤ m₂ := by
    have : j₂ ≤ M * j₂ := Nat.le_mul_of_pos_left _ hM
    omega
  have hm₂0 : (m₂ : ℚ) ≠ 0 := by
    have : 0 < m₂ := Nat.mul_pos hM (by omega)
    exact_mod_cast this.ne'
  obtain ⟨hW₂c, hW₂a⟩ := isRelativelyAmple_pb_add hY p hJc hJa ((j₂ : ℤ) • DM)
  -- the boundaries
  set F₁ : QDivisor V := F + (t : ℚ)⁻¹ • Divisor.toQDivisor (pb hY p E) +
    ((c : ℚ) * t)⁻¹ • Divisor.toQDivisor J with hF₁def
  set F₂ : QDivisor V := F + (m₂ : ℚ)⁻¹ • Divisor.toQDivisor J with hF₂def
  -- the pull-back identities, coefficientwise
  have hΓP : ∀ P, ((pb hY p ((M : ℤ) • K + BM)).coeff P : ℚ) = M * (KV.coeff P + Γ.coeff P) := by
    intro P
    have h := congrArg (fun G : QDivisor V => G.coeff P) hΓ
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul] at h
    rw [h]
  have hpbDM : pb hY p DM = (M : ℤ) • pb hY p L - pb hY p ((M : ℤ) • K + BM) := by
    rw [hDMdef, pb_sub, pb_zsmul]
  have hpbr : (r : ℤ) • pb hY p DM = (M : ℤ) • pb hY p A + (M : ℤ) • pb hY p E := by
    rw [← pb_zsmul, hrDM, pb_add, pb_zsmul, pb_zsmul]
  -- membership in the snc divisor
  have hsuppB : ∀ x, x ∈ B.supp → x ∈ (B + Divisor.toQDivisor E).supp := by
    intro x hx
    obtain ⟨C, hC, hxC⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨C, ?_, hxC⟩
    have h1 := hB C
    have h2 := hE C
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    have h2' : (0 : ℚ) ≤ E.coeff C := by exact_mod_cast h2
    have : 0 < B.coeff C := lt_of_le_of_ne h1 (Ne.symm hC)
    linarith
  have hsuppE : ∀ x, x ∈ E.supp → x ∈ (B + Divisor.toQDivisor E).supp := by
    intro x hx
    obtain ⟨C, hC, hxC⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx
    refine DivisorWithCoeffs.mem_supp_iff.mpr ⟨C, ?_, hxC⟩
    have h1 := hB C
    have h2 := hE C
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor]
    have : (0 : ℚ) < E.coeff C := by exact_mod_cast lt_of_le_of_ne h2 (Ne.symm hC)
    linarith
  have hmemF : ∀ P, F.coeff P ≠ 0 → P ∈ s := by
    intro P hP
    by_cases hΓ0 : Γ.coeff P = 0
    · have hQ0 : Q.coeff P ≠ 0 := by
        intro hq
        apply hP
        simp [hFdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hΓ0, hq]
      exact hsmem P (Or.inl (hQx P hQ0))
    · rcases hΓs P hΓ0 with h | h
      · exact hsmem P (Or.inl h)
      · exact hsmem P (Or.inr (hsuppB _ h))
  have hmemE : ∀ P, (pb hY p E).coeff P ≠ 0 → P ∈ s := fun P hP =>
    by_contra fun hPs => hP (coeff_pb_eq_zero hY p E P fun h => hPs (hsmem P (Or.inr (hsuppE _ h))))
  have hmemJ : ∀ P, J.coeff P ≠ 0 → P ∈ s := fun P hP => hsmem P (Or.inl (hJx P hP))
  have hsnc' : ∀ G : QDivisor V, (∀ P, G.coeff P ≠ 0 → P ∈ s) →
      DivisorWithCoeffs.IsSNC (p ≫ sY) G := by
    intro G hG
    refine hs.of_support_subset fun P hP => ?_
    have hPs := hG P (Finsupp.mem_support_iff.mp hP)
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hPs]
  have hnot : ∀ P, P ∉ S → F.coeff P = 0 ∧ (pb hY p E).coeff P = 0 ∧ J.coeff P = 0 := by
    intro P hP
    simp only [hSdef, Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hP
    exact ⟨hP.2, hP.1.1, hP.1.2⟩
  refine ⟨V, p ≫ sY, p, hVv, ‹_›, ‹_›, ‹_›, ‹_›, hVs, rfl, hpp, hpp.comp hf, KV, hKV,
    pb hY p L + Q, MMP.Fourfold.isCartier_of_isSmoothScheme hVs _, ?_, F₁, F₂, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · -- `p_* 𝒪_V(p^*L + Q) ≅ 𝒪_Y(L)`
    obtain ⟨e, -⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sY p
      ‹_› hVv hpb L hL _ (pb hY p L) (isPullback_pb hY p L) Q
      (MMP.Fourfold.isCartier_of_isSmoothScheme hVs Q)
      (DivisorWithCoeffs.isEffective_iff_nonneg.mp hQe) hQx
    exact ⟨e.symm⟩
  · -- `F₁` effective
    intro P
    simp only [hF₁def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      Divisor.coeff_toQDivisor]
    have h1 : (0 : ℚ) ≤ (pb hY p E).coeff P := by exact_mod_cast hpbE P
    have h2 : (0 : ℚ) ≤ J.coeff P := by exact_mod_cast hJe P
    have := (hF01 P).1
    positivity
  · -- `F₁` snc
    refine hsnc' F₁ fun P hP => ?_
    by_contra hPs
    apply hP
    have hF : F.coeff P = 0 := of_not_not (hPs ∘ hmemF P)
    have hE' : (pb hY p E).coeff P = 0 := of_not_not (hPs ∘ hmemE P)
    have hJ' : J.coeff P = 0 := of_not_not (hPs ∘ hmemJ P)
    simp [hF₁def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, hF, hE', hJ']
  · -- `F₁` has coefficients `< 1`
    intro P
    simp only [hF₁def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      Divisor.coeff_toQDivisor]
    have h1 : (0 : ℚ) ≤ (pb hY p E).coeff P := by exact_mod_cast hpbE P
    have h2 : (0 : ℚ) ≤ J.coeff P := by exact_mod_cast hJe P
    have htpos : (0 : ℚ) < t := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm ht0)
    have hle : ((c : ℚ) * t)⁻¹ * J.coeff P ≤ (t : ℚ)⁻¹ * J.coeff P := by
      apply mul_le_mul_of_nonneg_right _ h2
      apply inv_anti₀ htpos
      nlinarith
    by_cases hPS : P ∈ S
    · have := hT₁ t htT P hPS
      rw [add_div, div_eq_inv_mul, div_eq_inv_mul] at this
      linarith
    · obtain ⟨hF, hE', hJ'⟩ := hnot P hPS
      simp [hF, hE', hJ']
  · -- the first gap
    refine ⟨c * t, by positivity, (c : ℤ) • pb hY p (DN + A) + -J, hW₁c, ?_, hW₁a⟩
    clear_value F₁ F₂ c m₂ j₂ S t DN j₁ F Q DM D
    ext P
    have hk := hΓP P
    have hd := congrArg (fun G : Divisor V => (G.coeff P : ℚ)) hpbDM
    have hr' := congrArg (fun G : Divisor V => (G.coeff P : ℚ)) hpbr
    rw [pb_add, hDNdef, pb_zsmul]
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_smul, smul_eq_mul, hF₁def,
      hFdef] at hk hd hr' ⊢
    push_cast at hk hd hr' ⊢
    have key := gap₁_coeff ((pb hY p L).coeff P : ℚ) ((pb hY p ((M : ℤ) • K + BM)).coeff P : ℚ)
      ((pb hY p DM).coeff P : ℚ) ((pb hY p E).coeff P : ℚ) ((pb hY p A).coeff P : ℚ)
      (KV.coeff P : ℚ) (Γ.coeff P) (Q.coeff P : ℚ) (J.coeff P : ℚ) (M : ℚ) (c : ℚ) (j₁ : ℚ)
      (r : ℚ) (t : ℚ) hMq hc0 ht0 (by rw [htdef]; push_cast; ring) hk hd hr'
    linear_combination key
  · -- `F₂` effective
    intro P
    simp only [hF₂def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      Divisor.coeff_toQDivisor]
    have h2 : (0 : ℚ) ≤ J.coeff P := by exact_mod_cast hJe P
    have := (hF01 P).1
    positivity
  · -- `F₂` snc
    refine hsnc' F₂ fun P hP => ?_
    by_contra hPs
    apply hP
    have hF : F.coeff P = 0 := of_not_not (hPs ∘ hmemF P)
    have hJ' : J.coeff P = 0 := of_not_not (hPs ∘ hmemJ P)
    simp [hF₂def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toQDivisor, hF, hJ']
  · -- `F₂` has coefficients `< 1`
    intro P
    simp only [hF₂def, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul,
      Divisor.coeff_toQDivisor]
    by_cases hPS : P ∈ S
    · have := hT₂ m₂ hm₂T P hPS
      rw [div_eq_inv_mul] at this
      linarith
    · obtain ⟨hF, -, hJ'⟩ := hnot P hPS
      simp [hF, hJ']
  · -- the second gap
    refine ⟨m₂, by positivity, pb hY p ((j₂ : ℤ) • DM) + -J, hW₂c, ?_, hW₂a⟩
    clear_value F₁ F₂ c m₂ j₂ S t DN j₁ F Q DM D
    ext P
    have hk := hΓP P
    have hd := congrArg (fun G : Divisor V => (G.coeff P : ℚ)) hpbDM
    rw [pb_zsmul]
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_smul, smul_eq_mul, zsmul_eq_mul,
      hF₂def, hFdef, hm₂] at hk hd ⊢
    push_cast at hk hd ⊢
    have hj₂0 : (j₂ : ℚ) ≠ 0 := by rw [hj₂]; positivity
    have key := gap₂_coeff ((pb hY p L).coeff P : ℚ) ((pb hY p ((M : ℤ) • K + BM)).coeff P : ℚ)
      ((pb hY p DM).coeff P : ℚ) (KV.coeff P : ℚ) (Γ.coeff P) (Q.coeff P : ℚ) (J.coeff P : ℚ)
      (M : ℚ) (j₂ : ℚ) hMq hj₂0 hk hd
    linear_combination key

/-- The vanishing over an affine base, given the decomposition `rD = A + E` of the gap into an
`f`-ample Cartier divisor and an effective divisor. -/
private theorem isZero_of_decomposition
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [IsAffine Z] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY)
    (hf : IsProjectiveMorphism f) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : DivisorWithCoeffs.IsSNC sY B)
    (hB1 : ∀ E : MMP.Mori.PrimeDivisor Y, B.coeff E < 1) {L : Divisor Y} (hL : L.IsCartier)
    (hnef : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyNef sY f)
    {r : ℕ} (hr : 0 < r) {A E : Divisor Y} (hA : A.IsCartier) (hAamp : A.IsRelativelyAmple f hA)
    (hE : E.IsEffective)
    (hdec : Divisor.toQDivisor A + Divisor.toQDivisor E =
      (r : ℚ) • (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)))
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj L.divisorialSheaf) := by
  obtain ⟨V, sV, p, _, _, _, _, _, hV, hpY, hp, hpf, KV, hKV, L', hL', ⟨eL⟩, F₁, F₂, hF₁, hsnc₁,
    hF₁1, hgap₁, hF₂, hsnc₂, hF₂1, hgap₂⟩ :=
    exists_resolutionData sY sZ hY f hfZ hf hK hB hsnc hB1 hL hnef hr hA hAamp hE hdec
  have h₁ := MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_of_hasRelativelyAmpleMultiple
    sV sZ hV (p ≫ f) (by rw [Category.assoc, hfZ, hpY]) hpf hKV hF₁ hsnc₁ hF₁1 hL' hgap₁ i hi
  have h₂ := fun q (hq : 0 < q) =>
    MMP.Mori.isZero_rightDerived_pushforward_divisorialSheaf_of_hasRelativelyAmpleMultiple
      sV sY hV p hpY hp hKV hF₂ hsnc₂ hF₂1 hL' hgap₂ q hq
  obtain ⟨e⟩ := nonempty_rightDerived_comp_iso p f L'.divisorialSheaf h₂ i
  exact (h₁.of_iso e).of_iso (((Scheme.Modules.pushforward f).rightDerived i).mapIso eL.symm)

section Comparison

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- The comparison of divisorial and Cartier sheaves is additive. -/
private theorem nonempty_divisorialSheaf_add_iso {W₁ W₂ : Divisor X} (h₁ : W₁.IsCartier)
    (h₂ : W₂.IsCartier) {C₁ C₂ : X.CartierDivisor}
    (e₁ : W₁.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C₁)
    (e₂ : W₂.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C₂) :
    Nonempty ((W₁ + W₂).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (C₁ + C₂)) :=
  ⟨(h₁.divisorialSheafTensorIso h₂).symm ≪≫ MonoidalCategory.tensorIso e₁ e₂ ≪≫
    MMP.CartierDivisorSheaf.sheafMulIso C₁ C₂⟩

/-- The comparison of divisorial and Cartier sheaves is compatible with positive multiples. -/
private theorem nonempty_divisorialSheaf_nsmul_iso {W : Divisor X} (hW : W.IsCartier)
    {C : X.CartierDivisor} (e : W.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C)
    (n : ℕ) (hn : 1 ≤ n) :
    Nonempty ((n • W).divisorialSheaf ≅ MMP.CartierDivisor.sheaf (n • C)) := by
  induction n, hn using Nat.le_induction with
  | base => rw [one_nsmul, one_nsmul]; exact ⟨e⟩
  | succ n hn ih =>
    obtain ⟨ie⟩ := ih
    rw [succ_nsmul, succ_nsmul]
    exact nonempty_divisorialSheaf_add_iso (hW.nsmul n) hW ie e

/-- The generic rank only depends on the isomorphism class of the module. -/
private theorem relativeGenericRank_congr {Y : Scheme.{0}} (f : X ⟶ Y) {F G : X.Modules}
    (e : F ≅ G) : relativeGenericRank f F = relativeGenericRank f G :=
  Scheme.Modules.fiberRank_eq_of_iso ((Scheme.Modules.pushforward f).mapIso e) _

/-- Bigness of a Cartier Weil divisor transfers to a Cartier divisor with the same sheaf. -/
private theorem isRelativelyBigCartier_of_isRelativelyBig {Y : Scheme.{0}} (f : X ⟶ Y)
    {D₀ : Divisor X} (hD₀ : D₀.IsCartier) {C : X.CartierDivisor}
    (e : D₀.divisorialSheaf ≅ MMP.CartierDivisor.sheaf C)
    (hb : D₀.IsRelativelyBig f) : IsRelativelyBigCartier f C := by
  obtain ⟨a, b, ha, hb', c, hc, k₀, hk⟩ := hb
  refine ⟨a, b, ha, hb', c, hc, max k₀ 1, fun m hm => ?_⟩
  have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
  have hk0 : k₀ ≤ m := le_trans (le_max_left _ _) hm
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  obtain ⟨ie⟩ := nonempty_divisorialSheaf_nsmul_iso hD₀ e n (by omega)
  have h := hk _ hk0
  rw [natCast_zsmul] at h ⊢
  rw [← relativeGenericRank_congr f ie]
  exact h

end Comparison

/-- A nonzero quasi-coherent module on an affine scheme has a nonzero global section. -/
private theorem exists_ne_zero_of_not_isZero {T : Scheme.{0}} [IsAffine T] (M : T.Modules)
    [M.IsQuasicoherent] (h : ¬ IsZero M) : ∃ t : Γ(M, ⊤), t ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply h
  refine Stacks.AlgebraicGeometry.TopDegreeBaseChange.isZero_of_isZero_sections_of_isAffine M ?_
  rw [ModuleCat.isZero_iff_subsingleton]
  exact ⟨fun a b => (hcon a).trans (hcon b).symm⟩

/-- **Relative Kodaira lemma.** Over an affine base, an `f`-big `ℚ`-Cartier `ℚ`-divisor `D` has
a positive multiple `rD = A + E` with `A` an `f`-ample Cartier divisor and `E ≥ 0`. -/
private theorem exists_decomposition
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [IsAffine Z] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY)
    (hf : IsProjectiveMorphism f) {D : QDivisor Y} (hD : D.IsQCartier)
    (hbig : D.IsRelativelyBig f) :
    ∃ r : ℕ, 0 < r ∧ ∃ (A E : Divisor Y) (hA : A.IsCartier), A.IsRelativelyAmple f hA ∧
      E.IsEffective ∧ Divisor.toQDivisor A + Divisor.toQDivisor E = (r : ℚ) • D := by
  obtain ⟨m₁, hm₁, DD, hDD, hDDc, hDDb⟩ := hbig
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  have hcart : ∀ W : Divisor Y, W.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hY
  -- an `f`-ample Cartier divisor `L_H`
  obtain ⟨⟨L, hLinv, hLamp, hLC⟩, -⟩ :=
    MMP.Foundations.IsProjective.exists_isRelativelyAmple hf.isProjective
  haveI := hLinv
  obtain ⟨LH, ⟨eLH⟩⟩ := exists_divisorialSheaf_iso_of_isInvertible L
  haveI := (hcart LH).isInvertibleModule_divisorialSheaf
  have hLHa : LH.IsRelativelyAmple f (hcart LH) :=
    MMP.Mori.IsRelativelyAmple.of_stacks _ _
      ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ eLH.symm).mp hLamp)
  -- Cartier divisors realizing `𝒪(DD)` and `𝒪(-L_H)`
  haveI := hDDc.isInvertibleModule_divisorialSheaf
  haveI := (hcart (-LH)).isInvertibleModule_divisorialSheaf
  obtain ⟨Ec, ⟨eEc⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf DD.divisorialSheaf
  obtain ⟨Hc, ⟨eHc⟩⟩ :=
    MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf (-LH).divisorialSheaf
  have hEcb := isRelativelyBigCartier_of_isRelativelyBig f hDDc eEc hDDb
  obtain ⟨s, hs, hrank⟩ :=
    MMP.Mori.exists_pos_relativeGenericRank_sub_of_isRelativelyBigCartier sY sZ f hfZ hEcb (-Hc)
  rw [neg_neg] at hrank
  -- the divisor `W = s DD - L_H`
  set W : Divisor Y := s • DD + -LH with hWdef
  obtain ⟨eW1⟩ := nonempty_divisorialSheaf_nsmul_iso hDDc eEc s hs
  obtain ⟨eW⟩ := nonempty_divisorialSheaf_add_iso (hDDc.nsmul s) (hcart _) eW1 eHc
  have hrankW : relativeGenericRank f W.divisorialSheaf ≠ 0 := by
    rwa [relativeGenericRank_congr f eW]
  haveI := (hcart W).isInvertibleModule_divisorialSheaf
  have hnz : ¬ IsZero ((Scheme.Modules.pushforward f).obj W.divisorialSheaf) := fun h0 =>
    hrankW (MMP.Mori.fiberRank_eq_zero_of_isZero _ h0 _)
  haveI : IsSeparated f := IsProper.toIsSeparated
  haveI : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  haveI : ((Scheme.Modules.pushforward f).obj W.divisorialSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs f _
  obtain ⟨t, ht⟩ := exists_ne_zero_of_not_isZero _ hnz
  let σ : W.divisorialSubmodule ⊤ := t
  have hσ : σ ≠ 0 := ht
  set φ := (Divisor.isUnit_sectionToRationalFunctions hσ).unit with hφ
  have hE := Divisor.zeroDivisor_nonneg W σ hσ
  refine ⟨s * m₁, Nat.mul_pos hs hm₁, LH - principalDivisor φ, W.zeroDivisor σ hσ, hcart _, ?_,
    DivisorWithCoeffs.isEffective_iff_nonneg.mpr hE, ?_⟩
  · haveI := (hcart (LH - principalDivisor φ)).isInvertibleModule_divisorialSheaf
    have e : LH.divisorialSheaf ≅ (LH - principalDivisor φ).divisorialSheaf :=
      Divisor.divisorialSheafMulIso φ fun E => by
        rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor]; ring
    exact isRelativelyAmple_of_iso f e hLHa
  · rw [Divisor.zeroDivisor_eq, ← map_add, show LH - principalDivisor φ + (principalDivisor φ + W) =
      s • DD by rw [hWdef]; abel, map_nsmul, hDD, ← Nat.cast_smul_eq_nsmul ℚ s, smul_smul,
      Nat.cast_mul]

/-- The statement over an affine base. -/
private theorem isZero_of_isAffine
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [IsAffine Z] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY)
    (hf : IsProjectiveMorphism f) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : DivisorWithCoeffs.IsSNC sY B)
    (hB1 : ∀ E : MMP.Mori.PrimeDivisor Y, B.coeff E < 1) {L : Divisor Y} (hL : L.IsCartier)
    (hnef : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyNef sY f)
    (hbig : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyBig f)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj L.divisorialSheaf) := by
  obtain ⟨r, hr, A, E, hA, hAamp, hE, hdec⟩ :=
    exists_decomposition sY sZ hY f hfZ hf hnef.1 hbig
  exact isZero_of_decomposition sY sZ hY f hfZ hf hK hB hsnc hB1 hL hnef hr hA hAamp hE hdec i hi

section Restrict

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  (U : X.Opens)
  [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U] [IsDominant U.ι]

/-- The restriction of a Cartier divisor to a dense open is its pull-back along the inclusion. -/
private theorem isPullback_restrictOpen {N : Divisor X} (hN : N.IsCartier) :
    N.IsPullback U.ι (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
      (N.restrictOpen U) := by
  obtain ⟨N', hN'⟩ := hN.exists_isPullback (f := U.ι)
    (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant U.ι N)
  have hiso : ∀ P : MMP.Mori.PrimeDivisor U, IsIso (U.ι.stalkMap P.genericPoint) := fun P =>
    inferInstanceAs <| IsIso (U.ι.toLRSHom.stalkMap P.genericPoint)
  have : N' = N.restrictOpen U := by
    ext P
    change N'.coeff P = (N.restrictOpen U).coeff P
    rw [DivisorWithCoeffs.coeff_restrictOpen]
    exact MMP.Positivity.coeff_eq_of_isPullback P _
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι P).symm hN hN'
  exact this ▸ hN'

/-- The divisorial sheaf of the restriction of a Cartier divisor is the restriction of its
divisorial sheaf. -/
private theorem nonempty_restrict_divisorialSheaf_iso {N : Divisor X} (hN : N.IsCartier) :
    Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj N.divisorialSheaf ≅
      Divisor.divisorialSheaf (N.restrictOpen U)) :=
  ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    ((isPullback_restrictOpen U hN).divisorialSheafIso (hBc := hN)).symm⟩

end Restrict

open MMP.Threefold.Mori.OpenRestriction in
/-- The restriction of an snc divisor to an open subscheme is snc. -/
private theorem isSNC_restrictOpen {R : Type*} [Zero R] {X Y : Scheme.{0}} (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {D : DivisorWithCoeffs R X} (hD : D.IsSNC g) (U : X.Opens) :
    (D.restrictOpen U).IsSNC (U.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => (sncStalk_restrict_iff U.ι D x).mpr (hD.2 (U.ι x))⟩
  have hsm := hD.1 (OpenWeilRestriction.primeDivisorMap U.ι E₀)
    (Finsupp.mem_support_iff.2 (Finsupp.mem_support_iff.1 hE₀ : D.restrictOpen U E₀ ≠ 0))
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus] at hsm
  exact (isSmoothScheme_comap_iff U.ι g (OpenWeilRestriction.primeDivisorMap U.ι E₀).idealSheaf
    E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U.ι E₀)).mpr fun z _ => hsm ▸ trivial

/-- H-projectivity restricts over an open of the base. -/
private theorem isProjectiveMorphism_morphismRestrict {Y Z : Scheme.{0}} {f : Y ⟶ Z}
    (hf : IsProjectiveMorphism f) (V : Z.Opens) : IsProjectiveMorphism (f ∣_ V) := by
  obtain ⟨n, i, hi, hif⟩ := hf.baseChange V.ι
  have := hi
  refine ⟨n, (isPullback_morphismRestrict f V).flip.isoPullback.hom ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hif]
  exact (isPullback_morphismRestrict f V).flip.isoPullback_hom_snd

section Curves

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) (U : X.Opens)

/-- A proper curve of an open `U ⊆ X`, `X` separated over `k`, is a proper curve of `X`. -/
private theorem exists_properCurve_of_opens [IsSeparated sX] (C : ProperCurve (U.ι ≫ sX)) :
    ∃ (Γ : ProperCurve sX) (e : C.scheme ≅ Γ.scheme),
      Γ.point = U.ι C.point ∧ e.hom ≫ Γ.ι = C.ι ≫ U.ι ∧
      closure ({Γ.point} : Set X) = U.ι '' closure {C.point} := by
  have : IsProper ((C.ι ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have : IsProper (C.ι ≫ U.ι) := IsProper.of_comp (C.ι ≫ U.ι) sX
  have hrange : Set.range (C.ι ≫ U.ι) = U.ι '' closure {C.point} := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    congr 1
    change Set.range (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({C.point} : Set U))).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      TopologicalSpace.Closeds.coe_closure]
  have hcl0 : closure ({U.ι C.point} : Set X) ⊆ U.ι '' closure {C.point} := by
    rw [← hrange]
    refine closure_minimal ?_ (C.ι ≫ U.ι).isClosedMap.isClosed_range
    rw [Set.singleton_subset_iff, hrange]; exact ⟨C.point, subset_closure rfl, rfl⟩
  have hcl : closure ({U.ι C.point} : Set X) ⊆ Set.range U.ι :=
    hcl0.trans (Set.image_subset_range _ _)
  have hcl' : closure ({U.ι C.point} : Set X) = U.ι '' closure {C.point} := by
    refine subset_antisymm hcl0 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hx).map
      U.ι.base.hom.continuous)
  obtain ⟨e, he⟩ := MMP.Threefold.Resolution.exists_curveSubschemeAt_iso U.ι C.point rfl hcl
  refine ⟨⟨U.ι C.point, ⟨?_, ?_⟩⟩, e, rfl, he, hcl'⟩
  · rw [← IsHomeomorph.topologicalKrullDim_eq e.hom e.hom.homeomorph.isHomeomorph]
    exact C.dim_eq
  · have : curveSubschemeAtι (U.ι C.point) ≫ sX = e.inv ≫ (C.ι ≫ U.ι) ≫ sX := by
      rw [← he, Category.assoc, Iso.inv_hom_id_assoc]
    rw [this]
    infer_instance

/-- The degree of the restriction of a Cartier divisor on a curve of `U` is its degree on the
same curve in `X`. -/
private theorem degreeOn_restrictOpen_eq [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsIntegral U] [IsLocallyNoetherian U] [IsNormal U] [CompactSpace U]
    [IsDominant U.ι] [QuasiCompact sX] [QuasiCompact (U.ι ≫ sX)]
    {N : Divisor X} (hNc : N.IsCartier) (hNUc : Divisor.IsCartier (N.restrictOpen U))
    (C : ProperCurve (U.ι ≫ sX)) (Γ : ProperCurve sX) (e : C.scheme ≅ Γ.scheme)
    (he : e.hom ≫ Γ.ι = C.ι ≫ U.ι) :
    Divisor.degreeOn k (U.ι ≫ sX) C.ι C.dim_le (N.restrictOpen U) hNUc =
      N.degreeOn k sX Γ.ι Γ.dim_le hNc := by
  have hp := isPullback_restrictOpen U hNc
  have := hNc.isInvertibleModule_divisorialSheaf
  have := hNUc.isInvertibleModule_divisorialSheaf
  have : IsProper ((C.ι ≫ U.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  change MMP.Mori.degreeOn k (U.ι ≫ sX) C.ι C.dim_le (Divisor.divisorialSheaf (N.restrictOpen U)) =
    MMP.Mori.degreeOn k sX Γ.ι Γ.dim_le N.divisorialSheaf
  rw [degreeOn_eq_of_iso k (U.ι ≫ sX) C.ι C.dim_le
      (Divisor.IsPullback.divisorialSheafIso (hBc := hNc) hp),
    degreeOn_pullback_eq_degreeOn_comp (U.ι ≫ sX) sX U.ι C.ι rfl]
  exact MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX (C.ι ≫ U.ι) Γ.ι C.dim_le
    Γ.dim_le e he N.divisorialSheaf

end Curves

/-- `f`-nefness restricts to the preimage of an open of the base. -/
private theorem isRelativelyNef_restrictOpen {k : Type} [Field k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hY : IsSmoothScheme sY)
    (f : Y ⟶ Z) (V : Z.Opens) [Nonempty (f ⁻¹ᵁ V)] [IsLocallyNoetherian (f ⁻¹ᵁ V)]
    [IsNormal (f ⁻¹ᵁ V)] [QuasiCompact ((f ⁻¹ᵁ V).ι ≫ sY)]
    {D : QDivisor Y} (hD : D.IsRelativelyNef sY f) :
    QDivisor.IsRelativelyNef ((f ⁻¹ᵁ V).ι ≫ sY) (f ∣_ V) (D.restrictOpen (f ⁻¹ᵁ V)) := by
  set U := f ⁻¹ᵁ V with hU
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sY)
  have hUs : IsSmoothScheme (U.ι ≫ sY) := MMP.Threefold.Resolution.isSmoothScheme_ι k hY U
  have h := hD.1
  set m := D.cartierIndex h with hm
  set E : Divisor Y := (D.cartierIndexSMul h : Divisor Y) with hEdef
  have hEc : E.IsCartier := (D.cartierIndexSMul h).2
  have hE : Divisor.toQDivisor E = (m : ℚ) • D := by
    rw [hEdef, QDivisor.toQDivisor_cartierIndexSMul, natCast_zsmul, Nat.cast_smul_eq_nsmul]
  have hEU : Divisor.toQDivisor (E.restrictOpen U) = (m : ℚ) • D.restrictOpen U := by
    ext P
    exact congrArg (fun G : QDivisor Y => G (OpenWeilRestriction.primeDivisorMap U.ι P)) hE
  have hEUc : Divisor.IsCartier (E.restrictOpen U) :=
    MMP.Fourfold.isCartier_of_isSmoothScheme hUs _
  refine isRelativelyNef_of_degreeOn_nonneg (U.ι ≫ sY) (f ∣_ V)
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hUs _) (QDivisor.cartierIndex_pos h) hEU hEUc
    fun C hC => ?_
  obtain ⟨Γ, e, hpt, he, hcl⟩ := exists_properCurve_of_opens sY U C
  rw [degreeOn_restrictOpen_eq sY U hEc hEUc C Γ e he]
  refine degreeOn_nonneg_of_isRelativelyNef sY f hD hE hEc Γ ?_
  intro x hx
  rw [hcl] at hx
  obtain ⟨x', hx', rfl⟩ := hx
  rw [hpt]
  have h1 : ∀ y : U.toScheme, f (U.ι y) = V.ι ((f ∣_ V) y) := fun y =>
    (congrArg (fun φ : U.toScheme ⟶ Z => φ y) (morphismRestrict_ι f V)).symm
  rw [h1 x', h1 C.point, hC x' hx']

/-- A nonempty open subscheme of an open subscheme has the dimension of the closure of a point in
the ambient scheme. -/
private theorem topologicalKrullDim_closure_singleton_opens (k : Type) [Field k] (Z : Scheme.{0})
    (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] (V : Z.Opens) (y : V.toScheme) :
    topologicalKrullDim (closure ({y} : Set V.toScheme)) =
      topologicalKrullDim (closure ({V.ι y} : Set Z)) := by
  rw [topologicalKrullDim_closure_singleton_eq_trdeg k V (V.ι ≫ sZ),
    topologicalKrullDim_closure_singleton_eq_trdeg k Z sZ,
    ← trdeg_residueField_of_surjectiveOnStalks k sZ V.ι y]

/-- `f`-bigness restricts to the preimage of an open of the base meeting the image. -/
private theorem isRelativelyBig_restrictOpen {k : Type} [Field k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (hY : IsSmoothScheme sY)
    (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY) (V : Z.Opens) [Nonempty (f ⁻¹ᵁ V)] [IsIntegral (f ⁻¹ᵁ V)]
    [IsLocallyNoetherian (f ⁻¹ᵁ V)] [IsNormal (f ⁻¹ᵁ V)]
    {D : QDivisor Y} (hD : D.IsRelativelyBig f) :
    QDivisor.IsRelativelyBig (f ∣_ V) (D.restrictOpen (f ⁻¹ᵁ V)) := by
  set U := f ⁻¹ᵁ V with hU
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  haveI : LocallyOfFiniteType sZ := inferInstance
  haveI : LocallyOfFiniteType (U.ι ≫ sY) := inferInstance
  haveI : QuasiCompact (U.ι ≫ sY) := inferInstance
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sY)
  have hUs : IsSmoothScheme (U.ι ≫ sY) := MMP.Threefold.Resolution.isSmoothScheme_ι k hY U
  obtain ⟨m₁, hm₁, DD, hDD, hDDc, a, b, ha, hb, c, hc, k₀, hk⟩ := hD
  have hgen : U.ι (genericPoint U) = genericPoint Y := genericPoint_eq_of_isOpenImmersion U.ι
  have hη : V.ι ((f ∣_ V) (genericPoint U)) = f (genericPoint Y) := by
    rw [← hgen]
    exact (congrArg (fun φ : U.toScheme ⟶ Z => φ (genericPoint U)) (morphismRestrict_ι f V))
  refine ⟨m₁, hm₁, DD.restrictOpen U, ?_, MMP.Fourfold.isCartier_of_isSmoothScheme hUs _, a, b,
    ?_, ?_, c, hc, k₀, fun m hm => ?_⟩
  · ext P
    exact congrArg (fun G : QDivisor Y => G (OpenWeilRestriction.primeDivisorMap U.ι P)) hDD
  · rw [← ha, topologicalKrullDim_eq_trdeg_residueField k U (U.ι ≫ sY) (genericPoint U)
      (genericPoint_spec U), topologicalKrullDim_eq_trdeg_residueField k Y sY (genericPoint Y)
      (genericPoint_spec Y), ← hgen, trdeg_residueField_of_surjectiveOnStalks k sY U.ι]
  · rw [← hb, MMP.Flips.closure_range_eq_closure_genericPoint,
      MMP.Flips.closure_range_eq_closure_genericPoint]
    rw [topologicalKrullDim_closure_singleton_opens k Z sZ V]
    change topologicalKrullDim (closure ({V.ι ((f ∣_ V) (genericPoint U))} : Set Z)) = _
    rw [hη]
  · have h1 := hk m hm
    have hres : m • DD.restrictOpen U = (m • DD).restrictOpen U := by ext P; rfl
    rw [hres]
    obtain ⟨e⟩ := nonempty_restrict_divisorialSheaf_iso U (hDDc.zsmul m)
    rw [← relativeGenericRank_congr (f ∣_ V) e]
    have e₂ := ((Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso
      f V 0).app (m • DD).divisorialSheaf) ≪≫
        (Scheme.Modules.restrictFunctor V.ι).mapIso
          ((Functor.rightDerivedZeroIsoSelf (Scheme.Modules.pushforward f)).app _)
    have e₃ := ((Functor.rightDerivedZeroIsoSelf (Scheme.Modules.pushforward (f ∣_ V))).app
      ((Scheme.Modules.restrictFunctor U.ι).obj (m • DD).divisorialSheaf)).symm ≪≫ e₂
    unfold relativeGenericRank at h1 ⊢
    rw [Scheme.Modules.fiberRank_eq_of_iso e₃, Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict, hη]
    exact h1

/-- The hypotheses restrict to the preimage of an affine open of the base. -/
private theorem isZero_restrict_of_isAffineOpen
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY)
    (hf : IsProjectiveMorphism f) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : DivisorWithCoeffs.IsSNC sY B)
    (hB1 : ∀ E : MMP.Mori.PrimeDivisor Y, B.coeff E < 1) {L : Divisor Y} (hL : L.IsCartier)
    (hnef : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyNef sY f)
    (hbig : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyBig f)
    (i : ℕ) (hi : 0 < i) (V : Z.Opens) (hV : IsAffineOpen V) :
    IsZero ((Scheme.Modules.pushforward (f ∣_ V)).rightDerived i |>.obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj L.divisorialSheaf)) := by
  set U := f ⁻¹ᵁ V with hUdef
  by_cases hU : Nonempty U
  swap
  · haveI : IsEmpty U := not_nonempty_iff.mp hU
    refine Functor.map_isZero _ ?_
    exact AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun x => (IsEmpty.false x).elim
  haveI := hU
  have hYn : IsNormalVariety k sY := ⟨‹_›, ‹_›⟩
  have hUn := hYn.restrictOpen U
  haveI : AlgebraicGeometry.IsVariety k (U.ι ≫ sY) := hUn.1
  haveI : IsIntegral U := hUn.1.toIsIntegral
  haveI : IsNormal U := hUn.2
  haveI : LocallyOfFiniteType (U.ι ≫ sY) := hUn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ sY)
  haveI : QuasiCompact (U.ι ≫ sY) := hUn.1.toQuasiCompact
  haveI : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace (U.ι ≫ sY)
  haveI : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, (Classical.arbitrary U).2⟩)
  haveI : Nonempty V := ⟨(f ∣_ V) (Classical.arbitrary U)⟩
  haveI : IsAffine V := hV
  haveI : LocallyOfFiniteType sZ := inferInstance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsNoetherian Z := ⟨⟩
  haveI : AlgebraicGeometry.IsVariety k (V.ι ≫ sZ) := ⟨⟩
  have hUs : IsSmoothScheme (U.ι ≫ sY) := MMP.Threefold.Resolution.isSmoothScheme_ι k hY U
  have hfU : (f ∣_ V) ≫ (V.ι ≫ sZ) = U.ι ≫ sY := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hfZ]
  have hfp := isProjectiveMorphism_morphismRestrict hf V
  have hKU := MMP.Mori.Divisor.IsCanonicalDivisor.restrictOpen hYn hK U
  have hBU : (B.restrictOpen U).IsEffective := fun P => by
    rw [DivisorWithCoeffs.coeff_restrictOpen]; exact hB _
  have hsncU : DivisorWithCoeffs.IsSNC (U.ι ≫ sY) (B.restrictOpen U) := isSNC_restrictOpen sY hsnc U
  have hB1U : ∀ P, (B.restrictOpen U).coeff P < 1 := fun P => by
    rw [DivisorWithCoeffs.coeff_restrictOpen]; exact hB1 _
  have hLU : Divisor.IsCartier (L.restrictOpen U) := MMP.Fourfold.isCartier_of_isSmoothScheme hUs _
  have hDU : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).restrictOpen U =
      Divisor.toQDivisor (L.restrictOpen U) -
        (Divisor.toQDivisor (K.restrictOpen U) + B.restrictOpen U) := by
    ext P
    rfl
  have hnefU := isRelativelyNef_restrictOpen sY hY f V hnef
  have hbigU := isRelativelyBig_restrictOpen sY sZ hY f hfZ V hbig
  rw [hDU] at hnefU hbigU
  obtain ⟨e⟩ := nonempty_restrict_divisorialSheaf_iso U hL
  exact (isZero_of_isAffine (U.ι ≫ sY) (V.ι ≫ sZ) hUs (f ∣_ V) hfU hfp hKU hBU hsncU hB1U hLU
    hnefU hbigU i hi).of_iso (((Scheme.Modules.pushforward (f ∣_ V)).rightDerived i).mapIso e)

end Proof_lem_mmp_projective_snc_nef_big_vanishing

end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Mori

open Proof_lem_mmp_projective_snc_nef_big_vanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction TopologicalSpace
open MMP.Mori

/-- **Relative Kawamata–Viehweg vanishing, nef and big form.** Let `k` be algebraically closed of
characteristic zero, `f : Y ⟶ Z` a projective morphism of `k`-varieties with `Y` smooth over `k`,
`K` a canonical divisor of `Y` of dimension `n`, `B` an effective `ℚ`-divisor on `Y` with snc
support and all coefficients `< 1`, and `L` a Cartier divisor on `Y`. If `L - (K + B)` is
`f`-nef and `f`-big, then `R^i f_* 𝒪_Y(L) = 0` for all `i > 0`. -/
@[mmp "lem_mmp_projective_snc_nef_big_vanishing"]
public theorem isZero_rightDerived_pushforward_divisorialSheaf_of_isRelativelyNef_of_isRelativelyBig
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY)
    (hf : IsProjectiveMorphism f) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : DivisorWithCoeffs.IsSNC sY B)
    (hB1 : ∀ E : PrimeDivisor Y, B.coeff E < 1) {L : Divisor Y} (hL : L.IsCartier)
    (hnef : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyNef sY f)
    (hbig : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyBig f)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj L.divisorialSheaf) := by
  refine isZero_of_forall_isAffineOpen _ fun V hV => ?_
  exact (isZero_restrict_of_isAffineOpen sY sZ hY f hfZ hf hK hB hsnc hB1 hL hnef hbig i hi V
    hV).of_iso
      ((Stacks.AlgebraicGeometry.SchemeHigherDirectImage.higherDirectImageRestrictIso f V i).app
        L.divisorialSheaf).symm

end MMP.Mori

end

/-! ### `lem_mmp_proper_snc_nef_big_vanishing` -/

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Proof_lem_mmp_proper_snc_nef_big_vanishing

open MMP.Mori

section Leray

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Degenerate Leray.** If `F` has no higher direct images under `f`, then
`R^i (f ≫ g)_* F ≅ R^i g_* (f_* F)`, so one vanishes iff the other does. -/
private theorem isZero_rightDerived_comp_iff {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : X.Modules)
    (hf : ∀ j : ℕ, 0 < j → IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj F))
    (i : ℕ) :
    IsZero (((Scheme.Modules.pushforward (f ≫ g)).rightDerived i).obj F) ↔
      IsZero (((Scheme.Modules.pushforward g).rightDerived i).obj
        ((Scheme.Modules.pushforward f).obj F)) := by
  open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.AffineHigherDirectImage in
  let K := (derivedPushforward f.toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)
  have hK : ∀ j : ℤ, j ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor Y.Modules j).obj K) := by
    intro j hj
    obtain ⟨e⟩ := nonempty_homologyFunctor_derivedPushforward_iso f F j
    refine IsZero.of_iso ?_ e
    rcases lt_or_gt_of_ne hj with h | h
    · exact Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
        (Scheme.Modules.pushforward f) j h F
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m := ⟨j.toNat, by omega⟩
      exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
        (Scheme.Modules.pushforward f) m F).1 (hf m (by omega))
  have : K.IsGE 0 := (DerivedCategory.isGE_iff K 0).2 fun j hj => hK j (by omega)
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 fun j hj => hK j (by omega)
  obtain ⟨Y0, ⟨eK⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  let eY0 : Y0 ≅ (Scheme.Modules.pushforward f).obj F :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).app Y0).symm ≪≫
      (DerivedCategory.homologyFunctor Y.Modules 0).mapIso eK.symm ≪≫
      (nonempty_homologyFunctor_derivedPushforward_iso f F 0).some ≪≫
      Stacks.RightDerivedPlus.rightDerivedPlusZeroObjIso (Scheme.Modules.pushforward f) F
  let L := (derivedPushforward g.toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor Y.Modules 0).obj ((Scheme.Modules.pushforward f).obj F))
  let eL : (derivedPushforward (f ≫ g).toLRSHom.toShHom).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) ≅ L :=
    ((derivedPushforwardCompIso f.toLRSHom.toShHom g.toLRSHom.toShHom).app _).symm ≪≫
      (derivedPushforward g.toLRSHom.toShHom).mapIso
        (eK ≪≫ (DerivedCategory.singleFunctor Y.Modules 0).mapIso eY0)
  rw [Stacks.DerivedIndexing.isZero_rightDerived_obj_iff, Stacks.DerivedIndexing.isZero_rightDerived_obj_iff]
  obtain ⟨e₁⟩ := nonempty_homologyFunctor_derivedPushforward_iso (f ≫ g) F i
  obtain ⟨e₂⟩ := nonempty_homologyFunctor_derivedPushforward_iso g
    ((Scheme.Modules.pushforward f).obj F) i
  exact Iso.isZero_iff (e₁.symm ≪≫ (DerivedCategory.homologyFunctor Z.Modules i).mapIso eL ≪≫ e₂)

end Leray

section Nef

/-- Intersection numbers are unchanged by an isomorphism of curves over the target. -/
private theorem intersectionNumber_eq_of_iso_comp' {k : Type} [Field k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] {C C' : Scheme.{0}} (i : C ⟶ X) (i' : C' ⟶ X)
    [IsProper (i ≫ sX)] [IsProper (i' ≫ sX)] (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (e : C ≅ C') (he : e.hom ≫ i' = i) (D : QDivisor X)
    (hD : D.IsQCartier) :
    D.intersectionNumber k sX i hdim hD = D.intersectionNumber k sX i' hdim' hD := by
  have := QuasiCompact.compactSpace_of_compactSpace sX
  unfold QDivisor.intersectionNumber Divisor.degreeOn
  have := (QDivisor.isCartierDivisor_cartierIndex_smul hD).isCartier_toDivisor
    |>.isInvertibleModule_divisorialSheaf
  rw [MMP.Threefold.Resolution.degreeOn_eq_of_iso_comp k sX i i' hdim hdim' e he]

/-- The pull-back of a `g`-nef `ℚ`-Cartier divisor along `u` is `u ≫ g`-nef. -/
private theorem isRelativelyNef_comp_of_isPullback {k : Type} [Field k] {V W T : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) [IsProper u] (hu : u ≫ sW = sV) (g : W ⟶ T) {L : QDivisor W}
    (hL : L.IsRelativelyNef sW g)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') :
    L'.IsRelativelyNef sV (u ≫ g) := by
  have hLq : L.IsQCartier := hL.1
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV
    (h.isQCartier hLq) fun C hC => ?_
  have := C.isCurve
  set φ := C.ι ≫ u with hφ
  by_cases hpt : ∃ w : W, Set.range φ = {w}
  · exact (intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hLq h hpt).symm.le
  · have : MMP.Mori.IsCurve k (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
    have : IsProper (φ ≫ sW) := by rw [hφ, Category.assoc, hu]; infer_instance
    have hcurve := isCurve_imageι_comp sW φ hpt
    have key := intersectionNumber_pullback_eq_degreeOver_mul k sV sW u hu C.ι hLq h hcurve
    have : IsProper φ := IsProper.of_comp φ sW
    have : IsProper (φ.imageι ≫ sW) := isProper_imageι_comp φ sW
    have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({u C.point} : Set W)) := by
      rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
      congr 1
      ext1
      simp only [TopologicalSpace.Closeds.coe_closure]
      rw [hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, C.range_ι,
        closure_image_closure u.continuous, Set.image_singleton]
    obtain ⟨e, he⟩ : ∃ e : φ.ker.subscheme ≅ (Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({u C.point} : Set W))).subscheme,
        e.hom ≫ Scheme.IdealSheafData.subschemeι _ = φ.ker.subschemeι := by
      rw [hker]; exact ⟨Iso.refl _, by simp⟩
    have hdim : topologicalKrullDim (curveSubschemeAt (u C.point)) = 1 :=
      (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph).symm.trans
        hcurve.topologicalKrullDim_eq_one
    have hι : curveSubschemeAtι (u C.point) = e.inv ≫ φ.imageι := by
      rw [Iso.eq_inv_comp]; exact he
    have hprop : IsProper (curveSubschemeAtι (u C.point) ≫ sW) := by
      rw [hι, Category.assoc]; infer_instance
    let C'' : ProperCurve sW := ⟨u C.point, ⟨hdim, hprop⟩⟩
    have hC'' : C''.IsContractedBy g := by
      intro x hx
      have hsub : closure ({u C.point} : Set W) ⊆ u '' closure ({C.point} : Set V) :=
        (u.isClosedMap _ isClosed_closure).closure_subset_iff.mpr (by
          rintro _ rfl; exact ⟨C.point, subset_closure rfl, rfl⟩)
      obtain ⟨z, hz, rfl⟩ := hsub hx
      have := hC z hz
      simpa only [Scheme.Hom.comp_apply] using this
    rw [key, intersectionNumber_eq_of_iso_comp' sW φ.imageι C''.ι _ C''.dim_le e he _ hLq]
    exact mul_nonneg (by positivity)
      (MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sW hL hLq C'' hC'')

/-- The pull-back of a `ℚ`-Cartier divisor along `u` is `u`-nef: a curve contracted by `u`
maps to a point. -/
private theorem isRelativelyNef_of_isPullback {k : Type} [Field k] {V W : Scheme.{0}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsVariety k sV] [AlgebraicGeometry.IsVariety k sW]
    [IsLocallyNoetherian V] [IsNormal V] [IsLocallyNoetherian W] [IsNormal W]
    (u : V ⟶ W) (hu : u ≫ sW = sV) {L : QDivisor W} (hLq : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') :
    L'.IsRelativelyNef sV u := by
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV
    (h.isQCartier hLq) fun C hC => ?_
  have := C.isCurve
  have hpt : ∃ w : W, Set.range (C.ι ≫ u) = {w} := by
    refine ⟨u C.point, ?_⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, C.range_ι]
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hC x hx
    · rintro rfl
      exact ⟨C.point, subset_closure rfl, rfl⟩
  exact (intersectionNumber_pullback_eq_zero k sV sW u hu C.ι hLq h hpt).symm.le

end Nef

section Big

/-- The divisorial sheaf of a Cartier divisor has fibre rank one at every point. -/
private theorem fiberRank_divisorialSheaf {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {G : Divisor X} (hG : G.IsCartier) (x : X) :
    Scheme.Modules.fiberRank G.divisorialSheaf x = 1 := by
  obtain ⟨U, hxU, ψ, hψ⟩ := hG x
  have e := hψ.restrictDivisorialSheafIso
  have h1 := Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict U.ι G.divisorialSheaf ⟨x, hxU⟩
  have h2 := Scheme.Modules.fiberRank_eq_of_iso e ⟨x, hxU⟩
  exact h1.symm.trans (h2.trans (Scheme.Modules.fiberRank_unit_eq_one _))

/-- `𝒪_W(G) ≅ u_* 𝒪_V(u^*G)` for a Cartier divisor `G` and a proper birational morphism `u` of
normal varieties. -/
private theorem nonempty_iso_pushforward_divisorialSheaf {k : Type} [Field k] {V W : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] (sW : W ⟶ Spec (.of k)) (u : V ⟶ W) (hW : MMP.Mori.IsVariety k sW)
    (hV : MMP.Mori.IsVariety k (u ≫ sW)) [IsProper u] (hu : IsBirationalMorphism u)
    {G : Divisor W} (hG : G.IsCartier)
    {hGB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ G.supp}
    {G' : Divisor V} (h : G.IsPullback u hGB G') :
    Nonempty (G.divisorialSheaf ≅ (Scheme.Modules.pushforward u).obj G'.divisorialSheaf) := by
  obtain ⟨e, -⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sW u hW hV
    hu G hG hGB G' h 0 Divisor.isCartier_zero le_rfl (fun P hP => absurd (by simp) hP)
  exact ⟨e ≪≫ eqToIso (by rw [add_zero])⟩

/-- The generic rank of `F` along `u ≫ g` is that of `u_* F` along `g`, for `u` dominant. -/
private theorem relativeGenericRank_comp {V W T : Scheme.{0}} [IrreducibleSpace V]
    [IrreducibleSpace W] (u : V ⟶ W) [IsDominant u] (g : W ⟶ T) (F : V.Modules) (G : W.Modules)
    (e : G ≅ (Scheme.Modules.pushforward u).obj F) :
    relativeGenericRank (u ≫ g) F = relativeGenericRank g G := by
  unfold relativeGenericRank
  have hpt : (u ≫ g) (genericPoint V) = g (genericPoint W) := by
    rw [Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
  rw [hpt]
  exact Scheme.Modules.fiberRank_eq_of_iso
    ((Scheme.Modules.pushforwardComp u g).symm.app F ≪≫
      (Scheme.Modules.pushforward g).mapIso e.symm) _

/-- The pull-back of a `g`-big `ℚ`-divisor along a proper birational morphism `u` of normal
varieties is `u ≫ g`-big. -/
private theorem isRelativelyBig_comp_of_isPullback {k : Type} [Field k] {V W T : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] (sW : W ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sW]
    (u : V ⟶ W) [AlgebraicGeometry.IsVariety k (u ≫ sW)] [IsProper u]
    (hu : IsBirationalMorphism u) (g : W ⟶ T) {L : QDivisor W} (hL : L.IsRelativelyBig g)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') :
    L'.IsRelativelyBig (u ≫ g) := by
  obtain ⟨m, hm, D₀, hD₀, hD₀c, a, b, ha, hb, c, hc, k₀, hk⟩ := hL
  obtain ⟨D₀', hD₀', hp⟩ := h m hm D₀ hD₀ hD₀c
  haveI := hu.isDominant
  refine ⟨m, hm, D₀', hD₀', hp.isCartier hD₀c, a, b, ?_, ?_, c, hc, k₀, fun j hj => ?_⟩
  · rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW (u ≫ sW) hu]
    exact ha
  · have : Set.range (u ≫ g).base = Set.range g.base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr u.surjective, Set.image_univ]
    rw [this]
    exact hb
  · have hpj := hp.zsmul hD₀c j
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant u _)
    obtain ⟨e⟩ := nonempty_iso_pushforward_divisorialSheaf sW u inferInstance inferInstance hu
      (hD₀c.zsmul j) hpj
    rw [relativeGenericRank_comp u g _ _ e]
    exact hk j hj

/-- The pull-back of a `ℚ`-Cartier divisor along a proper birational morphism `u` of normal
varieties is `u`-big: the generic fibre is a point and every invertible sheaf has rank one. -/
private theorem isRelativelyBig_of_isPullback {k : Type} [Field k] {V W : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] (sW : W ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sW] (u : V ⟶ W) [AlgebraicGeometry.IsVariety k (u ≫ sW)]
    [IsProper u] (hu : IsBirationalMorphism u) {n : ℕ} (hn : topologicalKrullDim V = n)
    {L : QDivisor W} (hLq : L.IsQCartier)
    {hLB : ∀ Z : irreducibleComponents V, u (componentGenericPoint V Z) ∉ L.supp}
    {L' : QDivisor V} (h : L.IsPullback u hLB L') :
    L'.IsRelativelyBig u := by
  obtain ⟨D₀, D₀', hD₀c, hD₀B, -, hD₀', hp⟩ := h.exists_cartierIndex hLq
  haveI := hu.isDominant
  refine ⟨_, QDivisor.cartierIndex_pos hLq, D₀', hD₀', hp.isCartier hD₀c, n, n, hn, ?_, 1 / 2,
    by norm_num, 0, fun j _ => ?_⟩
  · rw [Set.range_eq_univ.mpr u.surjective, closure_univ,
      (Homeomorph.Set.univ W).isHomeomorph.topologicalKrullDim_eq,
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sW (u ≫ sW) hu, hn]
  · have hpj := hp.zsmul hD₀c j
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant u _)
    obtain ⟨e⟩ := nonempty_iso_pushforward_divisorialSheaf sW u inferInstance inferInstance hu
      (hD₀c.zsmul j) hpj
    unfold relativeGenericRank
    rw [← Scheme.Modules.fiberRank_eq_of_iso e, fiberRank_divisorialSheaf (hD₀c.zsmul j)]
    norm_num

end Big

section Core

/-- **The proper case from a projective model.** Let `p : V ⟶ Y` be a projective birational
morphism from a smooth variety with `f ∘ p` projective, `K_V` a canonical divisor, `F` an
effective snc `ℚ`-divisor on `V` with coefficients `< 1` and `L'` a Cartier divisor on `V` with
`L' - (K_V + F) = p^*D`. If `D` is `f`-nef and `f`-big and `G ≅ p_* 𝒪_V(L')`, then
`R^i f_* G = 0` for `i > 0`: `p^*D` is `p`-nef and `p`-big and `(f ∘ p)`-nef and `(f ∘ p)`-big,
so the projective theorem kills the higher direct images of `𝒪_V(L')` under `p` and under `f ∘ p`,
and the Leray spectral sequence of `f ∘ p` degenerates. -/
private theorem isZero_rightDerived_of_model {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [AlgebraicGeometry.IsVariety k sY] [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (f : Y ⟶ Z) (hfZ : f ≫ sZ = sY)
    {D : QDivisor Y} (hnef : D.IsRelativelyNef sY f) (hbig : D.IsRelativelyBig f)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (p : V ⟶ Y) [AlgebraicGeometry.IsVariety k (p ≫ sY)] (hVsm : IsSmoothScheme (p ≫ sY))
    (hp : IsProjectiveMorphism p) (hpf : IsProjectiveMorphism (p ≫ f))
    (hpb : IsBirationalMorphism p) {n : ℕ} {KV : Divisor V}
    (hKV : KV.IsCanonicalDivisor (p ≫ sY) n) {F : QDivisor V} (hF0 : F.IsEffective)
    (hFsnc : DivisorWithCoeffs.IsSNC (p ≫ sY) F)
    (hF1 : ∀ E : MMP.Mori.PrimeDivisor V, F.coeff E < 1)
    {L' : Divisor V} (hL' : L'.IsCartier)
    {hDB : ∀ Z : irreducibleComponents V, p (componentGenericPoint V Z) ∉ D.supp}
    (hgap : D.IsPullback p hDB (Divisor.toQDivisor L' - (Divisor.toQDivisor KV + F)))
    {G : Y.Modules} (e : G ≅ (Scheme.Modules.pushforward p).obj L'.divisorialSheaf)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj G) := by
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  have hnV : topologicalKrullDim V = n := hKV.topologicalKrullDim_eq
  have hpvan : ∀ j : ℕ, 0 < j →
      IsZero (((Scheme.Modules.pushforward p).rightDerived j).obj L'.divisorialSheaf) :=
    fun j hj => isZero_rightDerived_pushforward_divisorialSheaf_of_isRelativelyNef_of_isRelativelyBig
      (p ≫ sY) sY hVsm p rfl hp hKV hF0 hFsnc hF1 hL'
      (isRelativelyNef_of_isPullback p rfl hnef.1 hgap)
      (isRelativelyBig_of_isPullback sY p hpb hnV hnef.1 hgap) j hj
  have hfpvan := isZero_rightDerived_pushforward_divisorialSheaf_of_isRelativelyNef_of_isRelativelyBig
    (p ≫ sY) sZ hVsm (p ≫ f) (by rw [Category.assoc, hfZ]) hpf hKV hF0 hFsnc hF1 hL'
    (isRelativelyNef_comp_of_isPullback p rfl f hnef hgap)
    (isRelativelyBig_comp_of_isPullback sY p hpb f hbig hgap) i hi
  exact ((isZero_rightDerived_comp_iff p f _ hpvan i).1 hfpvan).of_iso
    (((Scheme.Modules.pushforward f).rightDerived i).mapIso e)

end Core

section Model

/-- **Chow's lemma for a variety.** A variety `X` over `k` is the target of a proper morphism
`r : X₁ ⟶ X` from a variety `X₁` which is H-quasi-projective over `k` and an isomorphism over a
dense open subset of `X`. -/
private theorem exists_isHQuasiProjective_isIso_morphismRestrict {k : Type} [Field k]
    {X : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX] :
    ∃ (X₁ : Scheme.{0}) (r : X₁ ⟶ X) (U : X.Opens), AlgebraicGeometry.IsVariety k (r ≫ sX) ∧
      IsProper r ∧ Dense (U : Set X) ∧ IsIso (r ∣_ U) ∧ IsHQuasiProjective (r ≫ sX) := by
  obtain ⟨n, X', π, i, U, hπ, -, hi, hcomm, hdense, hiso⟩ := hasDenseChowModification sX
  haveI := hπ
  haveI := hiso
  haveI := hi
  have hUne : Nonempty U := hdense.nonempty.to_subtype
  have hVne : Nonempty (π ⁻¹ᵁ U) := ⟨(inv (π ∣_ U)).base hUne.some⟩
  haveI : IsIntegral (π ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (π ∣_ U)
  haveI : IsSeparated (π ≫ sX) := by rw [hcomm]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (π ≫ sX)
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace (π ≫ sX)
  haveI : IsNoetherian X' := ⟨⟩
  have hi1 : IsIso ((π ⁻¹ᵁ U).ι.imageι ∣_ (π ⁻¹ᵁ U)) :=
    Stacks.SchemeTheoreticImage.isIso_imageι_restrict _
  refine ⟨(π ⁻¹ᵁ U).ι.image, (π ⁻¹ᵁ U).ι.imageι ≫ π, U, ?_, inferInstance, hdense, ?_, ?_⟩
  · rw [Category.assoc]
    exact Scheme.Hom.isVariety_image k _ (π ≫ sX)
  · rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hi1 hiso
  · have heq : ((π ⁻¹ᵁ U).ι.imageι ≫ i) ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) =
        ((π ⁻¹ᵁ U).ι.imageι ≫ π) ≫ sX := by
      rw [Category.assoc, Category.assoc, hcomm]
    have : QuasiCompact (((π ⁻¹ᵁ U).ι.imageι ≫ i) ≫
        (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k))) := by
      rw [heq]; infer_instance
    have hsep : IsSeparated (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) :=
      Stacks.HProjective.isSeparated_over n _
    have hqs : QuasiSeparated (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) :=
      @IsSeparated.instQuasiSeparated _ _ _ hsep
    have him : IsImmersion ((π ⁻¹ᵁ U).ι.imageι ≫ i) := inferInstance
    exact ⟨n, (π ⁻¹ᵁ U).ι.imageι ≫ i, him, @QuasiCompact.of_comp _ _ _ _
      (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) this hqs, heq⟩

/-- A proper morphism `g` whose composite with a separated morphism `s` is H-quasi-projective is
H-projective: `g` factors through an immersion into `ℙⁿ_X`, which is closed since `g` is
proper. -/
private theorem isProjectiveMorphism_of_isHQuasiProjective_comp {Y X S : Scheme.{0}}
    (g : Y ⟶ X) (s : X ⟶ S) [IsSeparated s] [IsProper g] (h : IsHQuasiProjective (g ≫ s)) :
    IsProjectiveMorphism g := by
  obtain ⟨n, i, hi, -, hif⟩ := h
  haveI := hi
  rw [isProjectiveMorphism_iff_isHQuasiProjective_and_isProper]
  refine ⟨?_, inferInstance⟩
  let l : Y ⟶ Limits.pullback (projectiveSpaceOver n S ↘ S) s := Limits.pullback.lift i g hif
  have hl : IsImmersion l := by
    have : IsImmersion (l ≫ Limits.pullback.fst _ _) := by
      rwa [Limits.pullback.lift_fst]
    exact IsImmersion.of_comp l (Limits.pullback.fst _ _)
  have heq : (l ≫ (projectiveSpaceOverBaseChangeIso n s).hom) ≫
      (projectiveSpaceOver n X ↘ X) = g := by
    rw [Category.assoc, projectiveSpaceOverBaseChangeIso_hom_over, Limits.pullback.lift_snd]
  have hsep : IsSeparated (projectiveSpaceOver n X ↘ X) := Stacks.HProjective.isSeparated_over n X
  have hqs : QuasiSeparated (projectiveSpaceOver n X ↘ X) :=
    @IsSeparated.instQuasiSeparated _ _ _ hsep
  have : QuasiCompact ((l ≫ (projectiveSpaceOverBaseChangeIso n s).hom) ≫
      (projectiveSpaceOver n X ↘ X)) := by
    rw [heq]; infer_instance
  exact ⟨n, l ≫ (projectiveSpaceOverBaseChangeIso n s).hom, inferInstance,
    @QuasiCompact.of_comp _ _ _ _ (projectiveSpaceOver n X ↘ X) this hqs, heq⟩

/-- **A projective model.** Let `f : Y ⟶ Z` be a proper morphism of varieties over a field of
characteristic zero, `Y` smooth, and `T ⊊ Y` a closed subset. There are a smooth variety `V` and
a birational morphism `p : V ⟶ Y` with `p` and `f ∘ p` H-projective, an open `U₀ ⊆ Y ∖ T` over
which `p` is an isomorphism, and an snc divisor `∑_{E ∈ s} E` on `V` containing every prime
divisor of `V` whose generic point does not map into `U₀`. -/
private theorem exists_model {k : Type} [Field k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) [IsProper f]
    (hfZ : f ≫ sZ = sY) (T : TopologicalSpace.Closeds Y) (hT : T ≠ ⊤) :
    ∃ (V : Scheme.{0}) (p : V ⟶ Y), AlgebraicGeometry.IsVariety k (p ≫ sY) ∧
      IsSmoothScheme (p ≫ sY) ∧ IsProjectiveMorphism p ∧ IsProjectiveMorphism (p ≫ f) ∧
      IsBirationalMorphism p ∧ ∃ U₀ : Y.Opens, Disjoint (U₀ : Set Y) T ∧ IsIso (p ∣_ U₀) ∧
        ∃ s : Finset (MMP.Mori.PrimeDivisor V),
          DivisorWithCoeffs.IsSNC (p ≫ sY) (∑ E ∈ s, Finsupp.single E (1 : ℤ)) ∧
          ∀ E : MMP.Mori.PrimeDivisor V, p E.genericPoint ∉ U₀ → E ∈ s := by
  classical
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  obtain ⟨Y₁, r, U, hY₁, hr, hUd, hrU, hqp⟩ := exists_isHQuasiProjective_isIso_morphismRestrict sY
  haveI := hY₁
  haveI := hr
  haveI := hrU
  -- the open `U₀ = U ∖ T`, over which `r` is an isomorphism
  set U₀ : Y.Opens := U ⊓ T.compl with hU₀
  have hU₀T : Disjoint (U₀ : Set Y) T := Set.disjoint_left.mpr fun _ hy hyT => hy.2 hyT
  have hU₀ne : (U₀ : Set Y).Nonempty := by
    have hTc : ((T.compl : Y.Opens) : Set Y).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      exact fun h => hT (TopologicalSpace.Closeds.ext (compl_eq_bot.mp h))
    obtain ⟨y, hy1, hy2⟩ := hUd.inter_open_nonempty _ T.compl.isOpen hTc
    exact ⟨y, hy2, hy1⟩
  haveI hrU₀ : IsIso (r ∣_ U₀) := MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le r
    inf_le_left
  have hr₀ne : ((r ⁻¹ᵁ U₀ : Y₁.Opens) : Set Y₁).Nonempty := by
    obtain ⟨y, hy⟩ := hU₀ne
    exact ⟨_, ((inv (r ∣_ U₀)) ⟨y, hy⟩).2⟩
  -- `r⁻¹(U₀)` is smooth over `k`
  haveI : LocallyOfFinitePresentation sY :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := sY)).mpr inferInstance
  haveI : Smooth sY := (MMP.Mori.isSmoothScheme_iff sY).mp hY
  have hsm₁ : r ⁻¹ᵁ U₀ ≤ smoothLocus (r ≫ sY) := by
    apply MMP.Mori.le_smoothLocus
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance
  -- the ideal of `Y₁ ∖ r⁻¹(U₀)`
  set T₁ : TopologicalSpace.Closeds Y₁ := (r ⁻¹ᵁ U₀).compl with hT₁
  set I : Y₁.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal T₁ with hI_def
  have hIsupp : (I.support : Set Y₁) = (T₁ : Set Y₁) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal T₁
  have hI : I ≠ ⊥ := by
    intro h
    obtain ⟨x, hx⟩ := hr₀ne
    have : x ∈ (I.support : Set Y₁) := by rw [h, Scheme.IdealSheafData.support_bot]; trivial
    exact (hIsupp ▸ this) hx
  obtain ⟨V, f₁, hV, hf₁, hf₁b, hVsm, hiso, -, hsnc, -⟩ :=
    MMP.Resolution.exists_isResolutionOfVariety_isEffectiveCartierDivisor_comap (r ≫ sY) hY₁ I hI
  haveI := hV
  haveI hf₁U : IsIso (f₁ ∣_ (r ⁻¹ᵁ U₀)) := by
    refine @MMP.Resolution.TupleResolutionAux.isIso_restrict_of_le _ _ f₁ _ _
      (le_inf hsm₁ ?_) hiso
    intro x hx hxI
    rw [hIsupp] at hxI
    exact hxI hx
  -- projectivity
  have hrH : IsProjectiveMorphism r := isProjectiveMorphism_of_isHQuasiProjective_comp r sY hqp
  haveI : IsProper (r ≫ f) := inferInstance
  have hrfH : IsProjectiveMorphism (r ≫ f) :=
    isProjectiveMorphism_of_isHQuasiProjective_comp (r ≫ f) sZ (by rwa [Category.assoc, hfZ])
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of k))
  obtain ⟨Lm, hLm, hLa⟩ := exists_isAmple_of_isQuasiProjective (r ≫ sY) _
    (Stacks.Ample.isAmple_unitModule_of_isAffine _) (isQuasiProjective_of_isHQuasiProjective _ hqp)
  haveI := hLm
  have hf₁H : IsProjectiveMorphism f₁ := isProjectiveMorphism_of_isProjective f₁ Lm hLa hf₁
  have hiso' : IsIso ((f₁ ≫ r) ∣_ U₀) := by
    rw [morphismRestrict_comp]; exact @IsIso.comp_isIso _ _ _ _ _ _ _ hf₁U hrU₀
  refine ⟨V, f₁ ≫ r, by rwa [Category.assoc], by rwa [Category.assoc], hf₁H.comp hrH,
    by rw [Category.assoc]; exact hf₁H.comp hrfH, ?_, U₀, hU₀T, hiso', ?_⟩
  · -- birationality
    obtain ⟨y, hy⟩ := hU₀ne
    refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (f₁ ≫ r) ((f₁ ≫ r) ⁻¹ᵁ U₀) U₀
      ⟨_, ((inv ((f₁ ≫ r) ∣_ U₀)) ⟨y, hy⟩).2⟩ ⟨y, hy⟩ le_rfl ?_
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact hiso'
  -- the snc divisor
  have hkey : ∀ E : MMP.Mori.PrimeDivisor V, (f₁ ≫ r) E.genericPoint ∉ U₀ →
      E.genericPoint ∈ ((MMP.Mori.exceptionalSet f₁ ⊔ (I.comap f₁).support :
        TopologicalSpace.Closeds V) : Set V) := by
    intro E hE
    right
    rw [Scheme.IdealSheafData.support_comap]
    change f₁ E.genericPoint ∈ (I.support : Set Y₁)
    rw [hIsupp]
    exact hE
  rcases hsnc with h0 | ⟨t, ht, htsnc⟩
  · refine ⟨∅, ?_, fun E hE => ?_⟩
    · rw [Finset.sum_empty]
      haveI hV' : AlgebraicGeometry.IsVariety k ((f₁ ≫ r) ≫ sY) := by rwa [Category.assoc]
      haveI : LocallyOfFinitePresentation ((f₁ ≫ r) ≫ sY) :=
        (LocallyOfFinitePresentation.iff_locallyOfFiniteType).mpr hV'.toLocallyOfFiniteType
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ (by rwa [Category.assoc])
    · have := hkey E hE
      rw [h0] at this
      exact absurd this (by simp)
  · refine ⟨t, by rwa [Category.assoc], fun E hE => ?_⟩
    have hmem := hkey E hE
    rw [← ht] at hmem
    obtain ⟨P, hP, hEP⟩ := Set.mem_iUnion₂.mp hmem
    have hsub : E.support ⊆ P.support := by
      have hcl : IsClosed (P.support : Set V) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure E]
      exact closure_minimal (Set.singleton_subset_iff.mpr hEP) hcl
    rw [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hsub]
    exact hP

end Model

section Boundary

/-- A divisor over `Y` whose generic point maps into an open over which its morphism is an
isomorphism is not exceptional: its image there has codimension one. -/
private theorem not_isExceptional_of_mem {k : Type} [Field k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (D : DivisorOver k sY) (U₀ : Y.Opens) (hU₀ : IsIso (D.f ∣_ U₀))
    (h : D.f D.E.genericPoint ∈ U₀) : ¬ D.IsExceptional := by
  intro hE
  have hdef : RationalMap.DefinedAt (X := D.Y) D.f.toRationalMap D.E.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp hE) hdef
  have hmem : D.f D.E.genericPoint ∈
      (RationalMap.transform (X := D.Y) D.f.toRationalMap D.E.idealSheaf.support : Set Y) := by
    refine RationalMap.image_subset_transform D.f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨_, ?_, rfl⟩
    change D.E.genericPoint ∈ D.E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hc := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2) _ hmem
  have hbir : D.f D.E.genericPoint ∈ biregularLocus D.f :=
    isBiregular_iff_le_biregularLocus.mp hU₀ h
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus D.f hbir,
    MMP.Mori.PrimeDivisor.coheight_genericPoint] at hc
  norm_num at hc

/-- On a non-exceptional prime divisor `F` of `Y`, the crepant boundary of `(X, Δ)` has the
coefficient of `Δ` along the prime divisor `P = f(F)` of `X`. -/
private theorem exists_coeff_eq_of_isCrepantBoundary {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {Y : Scheme.{0}} {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) (F : MMP.Mori.PrimeDivisor Y)
    (hE : ¬ (⟨Y, f, hY, hf, F⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff F = Δ.coeff P ∧ f F.genericPoint = P.genericPoint := by
  set D : DivisorOver k sX := ⟨Y, f, hY, hf, F⟩ with hD
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hmτ⟩ := hΔY F
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hE
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
  have hx : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hPU : (P.support ∩ (U : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hx ▸ hU⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have e := hτ.2 P hPU
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  refine ⟨P, ?_, hx⟩
  have : -ΔY.coeff F = -Δ.coeff P := by
    apply mul_left_cancel₀ hm0
    linear_combination hmτ + e
  linarith

/-- A nonzero rational top form is nonzero as a `1`-canonical form. -/
private theorem toPluriForms_ne_zero' {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {ω : RationalTopForms sX n} (hω : ω ≠ 0) :
    ω.toPluriForms sX ≠ 0 := by
  letI := functionFieldAlgebra sX
  intro h
  apply hω
  have h' : (PiTensorProduct.tprod X.functionField
      fun _ : Fin 1 => (ω : ⋀[X.functionField]^n Ω[X.functionField⁄k])) = 0 := h
  have h'' := congrArg (PiTensorProduct.subsingletonEquiv (0 : Fin 1)) h'
  rwa [PiTensorProduct.subsingletonEquiv_apply_tprod, map_zero] at h''

/-- **The pull-back from one Cartier multiple.** If `mB = G` with `G` Cartier, and the pull-back
`G'` of `G` is `mB'`, then `B'` is the pull-back of the `ℚ`-Cartier `ℚ`-divisor `B`. -/
private theorem isPullback_of_toQDivisor_eq_smul {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace X] {f : X ⟶ Y}
    {B : QDivisor Y} (hBq : B.IsQCartier)
    (hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp) {m : ℕ}
    (hm : 0 < m) {G : Divisor Y} (hGq : Divisor.toQDivisor G = (m : ℤ) • B) (hGc : G.IsCartier)
    {hG : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ G.supp}
    {G' : Divisor X} (hG' : G.IsPullback f hG G') {B' : QDivisor X}
    (hG'q : Divisor.toQDivisor G' = (m : ℤ) • B') :
    B.IsPullback f hB B' := by
  obtain ⟨G'', hG''q, hG''⟩ := QDivisor.isPullback_pullback hBq hB m hm G hGq hGc
  rw [hG''.eq hGc hG', hG'q] at hG''q
  convert QDivisor.isPullback_pullback hBq hB
  ext E
  have := congrArg (fun H : QDivisor X => H.coeff E) hG''q
  simp only [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
  exact mul_left_cancel₀ (by exact_mod_cast hm.ne') this

/-- The coefficient of a reduced sum `∑_{E ∈ s} E` is nonzero exactly on `s`. -/
private theorem mem_support_sum_single {V : Scheme.{0}} (s : Finset (MMP.Mori.PrimeDivisor V))
    {E : MMP.Mori.PrimeDivisor V} (hE : E ∈ s) :
    E ∈ (∑ P ∈ s, Finsupp.single P (1 : ℤ)).support := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply, hE]

/-- The crepant boundary of `(Y, B)` on a birational model `p : V ⟶ Y` vanishes along every
prime divisor of `V` whose generic point lies in an open `U₀ ⊆ Y ∖ Supp B` over which `p` is an
isomorphism: such a divisor is the strict transform of a prime divisor of `Y` not in `Supp B`. -/
private theorem coeff_eq_zero_of_isCrepantBoundary {k : Type} [Field k] [PerfectField k]
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {K : Divisor Y} {B : QDivisor Y} {V : Scheme.{0}} {p : V ⟶ Y}
    (hV : IsNormalVariety k (p ≫ sY)) (hp : IsBirationalMorphism p) {Γ : QDivisor V}
    (hΓ : IsCrepantBoundary sY n K B p hV hp Γ) {U₀ : Y.Opens}
    (hU₀B : Disjoint (U₀ : Set Y) (B.supp : Set Y)) (hpU₀ : IsIso (p ∣_ U₀))
    {E : MMP.Mori.PrimeDivisor V} (hE : p E.genericPoint ∈ U₀) :
    Γ.coeff E = 0 := by
  by_contra hne
  obtain ⟨P, hPc, hPg⟩ := exists_coeff_eq_of_isCrepantBoundary hV hp hΓ E
    (not_isExceptional_of_mem ⟨V, p, hV, hp, E⟩ U₀ hpU₀ hE)
  rw [hPg] at hE
  refine Set.disjoint_left.mp hU₀B hE (DivisorWithCoeffs.mem_supp_iff.mpr ⟨P, ?_, ?_⟩)
  · rwa [← hPc]
  · exact MMP.Flips.primeDivisor_genericPoint_mem_support P

/-- The divisor of the pull-back of a nonzero rational top form along a birational morphism from
a smooth variety is a canonical divisor there. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [AlgebraicGeometry.IsVariety k sY]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ} (hn : topologicalKrullDim Y = n)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    {p : V ⟶ Y} [IsDominant p] [AlgebraicGeometry.IsVariety k (p ≫ sY)]
    (hV : IsNormalVariety k (p ≫ sY))
    (hVsm : IsSmoothScheme (p ≫ sY)) (hp : IsBirationalMorphism p)
    (hnV : topologicalKrullDim V = n) {ω : RationalTopForms sY n} (hω : ω ≠ 0) :
    (divisorOfForm (pullbackRationalPluriForms sY p (ω.toPluriForms sY))).IsCanonicalDivisor
      (p ≫ sY) n := by
  obtain ⟨K₁, hK₁⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (p ≫ sY) hVsm hnV
  have hτ : pullbackRationalPluriForms sY p (ω.toPluriForms sY) ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
      hp.functionFieldMap_bijective
      (MMP.Mori.toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)
      (toPluriForms_ne_zero' hω)
  have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hK₁ hτ
  rw [one_smul] at h
  exact hK₁.of_linearlyEquivalent h

end Boundary

end Proof_lem_mmp_proper_snc_nef_big_vanishing

end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace MMP.Mori

open Proof_lem_mmp_proper_snc_nef_big_vanishing
open MMP.Mori

/-- **Relative Kawamata–Viehweg vanishing, nef and big form, for proper morphisms.** Let `k` be
algebraically closed of characteristic zero, `f : Y ⟶ Z` a proper morphism of `k`-varieties
with `Y` smooth over `k`, `K` a canonical divisor of `Y` of dimension `n`, `B` an effective
`ℚ`-divisor on `Y` with snc support and all coefficients `< 1`, and `L` a Cartier divisor on
`Y`. If `L - (K + B)` is `f`-nef and `f`-big, then `R^i f_* 𝒪_Y(L) = 0` for all `i > 0`. -/
@[mmp "lem_mmp_proper_snc_nef_big_vanishing"]
public theorem
    isZero_rightDerived_pushforward_divisorialSheaf_of_isProper_of_isRelativelyNef_of_isRelativelyBig
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y Z : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY]
    [AlgebraicGeometry.IsVariety k sZ] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] (hY : IsSmoothScheme sY) (f : Y ⟶ Z) [IsProper f] (hfZ : f ≫ sZ = sY)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : DivisorWithCoeffs.IsSNC sY B)
    (hB1 : ∀ E : PrimeDivisor Y, B.coeff E < 1) {L : Divisor Y} (hL : L.IsCartier)
    (hnef : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyNef sY f)
    (hbig : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyBig f)
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj L.divisorialSheaf) := by
  classical
  set D : QDivisor Y := Divisor.toQDivisor L - (Divisor.toQDivisor K + B) with hD
  have hYn : IsNormalVariety k sY := ⟨inferInstance, inferInstance⟩
  have hn : topologicalKrullDim Y = n := hK.topologicalKrullDim_eq
  /- The projective model `p : V ⟶ Y`. -/
  have hT : B.supp ≠ ⊤ := fun h =>
    MMP.Fourfold.genericPoint_notMem_supp B (by rw [h]; trivial)
  obtain ⟨V, p, hVv, hVsm, hp, hpf, hpb, U₀, hU₀B, hpU₀, s, hs, hsE⟩ :=
    exists_model sY sZ hY f hfZ B.supp hT
  haveI := hVv
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hp
  haveI : IsDominant p := hpb.isDominant
  obtain ⟨hVln, hVnor⟩ :=
    MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hVsm
  haveI := hVln
  haveI := hVnor
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sY)
  have hVn : IsNormalVariety k (p ≫ sY) := ⟨hVv, inferInstance⟩
  have hnV : topologicalKrullDim V = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY (p ≫ sY) hpb, hn]
  /- A nonzero top form `ω`, the canonical divisor `K₀ = div ω` and `L₀ = L + (K₀ - K)`. -/
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hYn hn
  let ω : RationalTopForms sY n := b ()
  have hω : ω ≠ 0 := b.ne_zero ()
  set K₀ : Divisor Y := topFormDivisor sY ω with hK₀def
  obtain ⟨φ, hφ⟩ := MMP.Spreading.CanonExist.linearlyEquivalent_topFormDivisor hYn hn hω hK
  have hK₀ : K₀.IsCanonicalDivisor sY n := hK.of_linearlyEquivalent ⟨φ, hφ⟩
  set L₀ : Divisor Y := L + principalDivisor φ with hL₀def
  have hL₀ : L₀.IsCartier := hL.add (Divisor.isCartier_principalDivisor φ)
  have hDeq : D = Divisor.toQDivisor L₀ - (Divisor.toQDivisor K₀ + B) := by
    have hKK : K₀ = K + principalDivisor φ := by rw [← hφ]; abel
    rw [hD, hL₀def, hKK, map_add, map_add]
    abel
  /- A Cartier multiple `L₁ = m(K₀ + B)` and the crepant boundary `Γ`. -/
  obtain ⟨m, hm, L₁, hL₁, hL₁c⟩ :=
    (MMP.Fourfold.isQCartier_of_isSmoothScheme hY (Divisor.toQDivisor K₀ + B)).exists_pos
  have hB₁ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p L₁
  set L₁' : Divisor V := L₁.pullback hL₁c hB₁ with hL₁'def
  set KV : Divisor V := divisorOfForm (pullbackRationalPluriForms sY p (ω.toPluriForms sY))
    with hKVdef
  set Γ : QDivisor V := (1 / (m : ℚ)) • Divisor.toQDivisor L₁' - Divisor.toQDivisor KV
    with hΓdef
  have hcb : IsCrepantBoundary sY n K₀ B p hVn hpb Γ :=
    MMP.ProgramBaseChange.isCrepantBoundary_pullback hYn hn hVn hpb hnV hω hm hL₁ hL₁c
  have hKV : KV.IsCanonicalDivisor (p ≫ sY) n :=
    isCanonicalDivisor_divisorOfForm_pullback hn hVn hVsm hpb hnV hω
  have hklt : IsKltPair sY n K₀ B := isKltPair_of_isSNC sY hYn hY hK₀ hsnc hB1
  have hΓ1 : ∀ E, Γ.coeff E < 1 := fun E =>
    MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary hklt hVn hpb hcb E
  have hΓsupp : ∀ E, Γ.coeff E ≠ 0 → E ∈ s := fun E hE =>
    hsE E fun hU => hE (coeff_eq_zero_of_isCrepantBoundary hVn hpb hcb hU₀B hpU₀ hU)
  /- The round-down `Q = -⌊Γ⌋` and the boundary `F = Γ + Q = {Γ}`. -/
  set Q : Divisor V := -Γ.roundDown with hQdef
  have hQc : ∀ E, Q.coeff E = -⌊Γ.coeff E⌋ := fun E => by
    rw [hQdef, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_roundDown]
  set F : QDivisor V := Γ + Divisor.toQDivisor Q with hFdef
  have hFc : ∀ E, F.coeff E = Int.fract (Γ.coeff E) := fun E => by
    rw [hFdef, DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, hQc, Int.fract]
    push_cast
    ring
  have hF0 : F.IsEffective := fun E => by rw [hFc]; exact Int.fract_nonneg _
  have hF1 : ∀ E, F.coeff E < 1 := fun E => by rw [hFc]; exact Int.fract_lt_one _
  have hFsnc : DivisorWithCoeffs.IsSNC (p ≫ sY) F := by
    refine hs.of_support_subset fun E hE => mem_support_sum_single s (hΓsupp E fun h0 => ?_)
    rw [Finsupp.mem_support_iff] at hE
    apply hE
    change F.coeff E = 0
    rw [hFc, h0, Int.fract_zero]
  have hQ0 : 0 ≤ Q := by
    intro E
    change 0 ≤ Q.coeff E
    rw [hQc]
    have : ⌊Γ.coeff E⌋ < 1 := Int.floor_lt.mpr (by exact_mod_cast hΓ1 E)
    omega
  have hQexc : ∀ P : MMP.Mori.PrimeDivisor V, Q.coeff P ≠ 0 →
      RationalMap.IsExceptional p.toRationalMap P := by
    intro P hP
    by_contra hex
    obtain ⟨P', hPc, -⟩ := exists_coeff_eq_of_isCrepantBoundary hVn hpb hcb P hex
    apply hP
    rw [hQc, hPc, Int.floor_eq_zero_iff.mpr ⟨hB P', hB1 P'⟩, neg_zero]
  /- The Cartier divisor `L' = p^*L₀ + Q` and `p_* 𝒪_V(L') ≅ 𝒪_Y(L)`. -/
  have hB₀ := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p L₀
  set L₀' : Divisor V := L₀.pullback hL₀ hB₀ with hL₀'def
  set L' : Divisor V := L₀' + Q with hL'def
  have hL'c : L'.IsCartier := MMP.Fourfold.isCartier_of_isSmoothScheme hVsm L'
  obtain ⟨e₀, -⟩ := Divisor.exists_iso_pushforward_divisorialSheaf_add_of_isExceptional sY p
    inferInstance hVv hpb L₀ hL₀ hB₀ L₀' (Divisor.isPullback_pullback hL₀ hB₀) Q
    (MMP.Fourfold.isCartier_of_isSmoothScheme hVsm Q) hQ0 hQexc
  have hLL₀ : L₀.LinearlyEquivalent L := ⟨φ, by rw [hL₀def, add_sub_cancel_left]⟩
  let e : L.divisorialSheaf ≅ (Scheme.Modules.pushforward p).obj L'.divisorialSheaf :=
    hLL₀.divisorialSheafIso.symm ≪≫ e₀
  /- The gap `L' - (K_V + F) = p^*D`. -/
  set G : Divisor Y := (m : ℤ) • L₀ + (-1 : ℤ) • L₁ with hGdef
  have hGc : G.IsCartier := (hL₀.zsmul _).add (hL₁c.zsmul _)
  have hGq : Divisor.toQDivisor G = (m : ℤ) • D := by
    rw [hGdef, map_add, map_zsmul, map_zsmul, hL₁, hDeq]
    ext E
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      zsmul_eq_mul]
    ring
  set G' : Divisor V := (m : ℤ) • L₀' + (-1 : ℤ) • L₁' with hG'def
  have hG' : G.IsPullback p (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p G)
      G' :=
    Divisor.IsPullback.add (hL₀.zsmul _) (hL₁c.zsmul _) _
      ((Divisor.isPullback_pullback hL₀ hB₀).zsmul hL₀ _
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p _))
      ((Divisor.isPullback_pullback hL₁c hB₁).zsmul hL₁c _
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant p _))
  set gap : QDivisor V := Divisor.toQDivisor L' - (Divisor.toQDivisor KV + F) with hgapdef
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmz : ((m : ℤ) : ℚ) = (m : ℚ) := Int.cast_natCast m
  have hG'q : Divisor.toQDivisor G' = (m : ℤ) • gap := by
    ext E
    simp only [hG'def, hgapdef, hL'def, hFdef, hΓdef, map_add, map_zsmul,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
      zsmul_eq_mul, smul_eq_mul, hmz]
    field_simp
    ring
  have hpbD : D.IsPullback p
      (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p D) gap :=
    isPullback_of_toQDivisor_eq_smul (MMP.Fourfold.isQCartier_of_isSmoothScheme hY D) _ hm hGq
      hGc hG' hG'q
  exact isZero_rightDerived_of_model sY sZ f hfZ hnef hbig p hVsm hp hpf hpb hKV hF0 hFsnc hF1
    hL'c hpbD e i hi

end MMP.Mori

end

/-! ### `lem_mmp_projective_split_unit_rationality` -/

section

open CategoryTheory AlgebraicGeometry Stacks.Duality Opposite Limits

namespace Proof_lem_mmp_projective_split_unit_rationality

/-! ### A retraction onto a nonzero object of a module without idempotents -/

/-- In a preadditive category, if every idempotent endomorphism of `M` is `0` or `𝟙`, then a
retraction `t : M ⟶ Q` with section `s` is an isomorphism unless `Q` is zero. -/
private theorem isIso_of_retraction {C : Type*} [Category C] [Preadditive C] {M Q : C}
    (hM : ∀ e : M ⟶ M, e ≫ e = e → e = 0 ∨ e = 𝟙 M) (t : M ⟶ Q) (s : Q ⟶ M)
    (hst : s ≫ t = 𝟙 Q) (hQ : ¬ IsZero Q) : IsIso t := by
  have he : (t ≫ s) ≫ (t ≫ s) = t ≫ s := by
    rw [Category.assoc, reassoc_of% hst]
  refine (hM _ he).elim (fun h => (hQ ?_).elim) (fun h => ⟨⟨s, h, hst⟩⟩)
  rw [IsZero.iff_id_eq_zero, ← hst, ← Category.comp_id t, ← hst]
  simp [reassoc_of% h]

/-- Having only the trivial idempotent endomorphisms is invariant under isomorphism. -/
private theorem idempotent_trivial_of_iso {C : Type*} [Category C] [Preadditive C] {M N : C}
    (i : M ≅ N) (hM : ∀ e : M ⟶ M, e ≫ e = e → e = 0 ∨ e = 𝟙 M) :
    ∀ e : N ⟶ N, e ≫ e = e → e = 0 ∨ e = 𝟙 N := by
  intro e he
  refine (hM (i.hom ≫ e ≫ i.inv) (by simp [reassoc_of% he])).imp (fun h => ?_) (fun h => ?_) <;>
    simpa using congr(i.inv ≫ $h ≫ i.hom)

/-! ### The idempotents of `f_* ω_Y` -/

/-- **Sections over an affine open generate the function field of a birational source.** For a
dominant morphism `f : Y ⟶ X` of integral schemes inducing an isomorphism of function fields and
a nonempty affine open `U ⊆ X`, every element of `K(Y)` is a quotient of pullbacks of sections of
`𝒪_X` over `U`. -/
private theorem exists_mul_germ_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) (U : X.Opens)
    (hU : IsAffineOpen U) (hη : genericPoint Y ∈ f ⁻¹ᵁ U) (c : Y.functionField) :
    ∃ s t : Γ(X, U), s ≠ 0 ∧
      Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hη (f.app U s) * c =
        Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hη (f.app U t) := by
  have hXU : genericPoint X ∈ U := by
    have := hη
    simpa [Scheme.Hom.mem_preimage, map_genericPoint_of_isDominant] using this
  haveI : Nonempty U := ⟨⟨_, hXU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨c', rfl⟩ := hf.2 c
  obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, U)) c'
  refine ⟨s, t, nonZeroDivisors.ne_zero s.2, ?_⟩
  rw [mul_comm, ← MMP.Fourfold.functionFieldMap_germ f U hXU hη, ← MMP.Fourfold.functionFieldMap_germ f U hXU hη, ← map_mul]
  exact congrArg (functionFieldMap f) hts

/-- The pullback of sections along a dominant morphism of integral schemes, read at the generic
point of the source, is injective, and every element of the function field of a birational
source is a quotient of such pullbacks over an affine open. -/
private theorem germ_app_injective_and_exists {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (hf : Function.Bijective (functionFieldMap f)) (U : X.Opens)
    (hU : IsAffineOpen U) (x : Y) (hx : x = genericPoint Y) (hxU : x ∈ f ⁻¹ᵁ U) :
    Function.Injective (fun r : Γ(X, U) => Y.presheaf.germ (f ⁻¹ᵁ U) x hxU (f.app U r)) ∧
      ∀ c : Y.presheaf.stalk x, ∃ s t : Γ(X, U), s ≠ 0 ∧
        Y.presheaf.germ (f ⁻¹ᵁ U) x hxU (f.app U s) * c =
          Y.presheaf.germ (f ⁻¹ᵁ U) x hxU (f.app U t) := by
  subst hx
  have hXU : genericPoint X ∈ U := by
    have := hxU
    simpa [Scheme.Hom.mem_preimage, map_genericPoint_of_isDominant] using this
  refine ⟨fun r r' h => ?_, exists_mul_germ_eq f hf U hU hxU⟩
  simp only at h
  rw [← MMP.Fourfold.functionFieldMap_germ f U hXU hxU, ← MMP.Fourfold.functionFieldMap_germ f U hXU hxU] at h
  exact germ_injective_of_isIntegral X _ hXU ((functionFieldMap f).injective h)

/-- An idempotent endomorphism of a torsion-free module whose elements are pairwise dependent
fixes or kills each nonzero element. -/
private theorem apply_eq_self_or_eq_zero_of_idempotent {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (htf : ∀ (r : R) (a : M), r • a = 0 → r = 0 ∨ a = 0)
    (hdep : ∀ a b : M, a ≠ 0 → ∃ s t : R, s ≠ 0 ∧ s • b = t • a)
    (e : M →ₗ[R] M) (he : ∀ a, e (e a) = e a) (a : M) (ha : a ≠ 0) : e a = a ∨ e a = 0 := by
  obtain ⟨s, t, hs, hst⟩ := hdep a (e a) ha
  have h1 : s • e a = t • e a := by
    have := congrArg e hst
    rwa [map_smul, map_smul, he] at this
  have h2 : (s - t) • e a = 0 := by rw [sub_smul, h1, sub_self]
  rcases htf _ _ h2 with h | h
  · left
    have hst' : s = t := sub_eq_zero.mp h
    subst hst'
    have h3 : s • (e a - a) = 0 := by rw [smul_sub, hst, sub_self]
    rcases htf _ _ h3 with h4 | h4
    · exact absurd h4 hs
    · exact sub_eq_zero.mp h4
  · exact Or.inr h

/-- An endomorphism of a torsion-free module whose elements are pairwise dependent cannot fix one
nonzero element and kill another. -/
private theorem false_of_apply_eq_self_of_apply_eq_zero {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (htf : ∀ (r : R) (a : M), r • a = 0 → r = 0 ∨ a = 0)
    (hdep : ∀ a b : M, a ≠ 0 → ∃ s t : R, s ≠ 0 ∧ s • b = t • a)
    (e : M →ₗ[R] M) (a b : M) (ha : a ≠ 0) (hb : b ≠ 0) (hea : e a = a) (heb : e b = 0) :
    False := by
  obtain ⟨s, t, hs, hst⟩ := hdep a b ha
  have h1 : t • a = 0 := by
    have := congrArg e hst
    rwa [map_smul, map_smul, heb, hea, smul_zero, eq_comm] at this
  rcases htf _ _ h1 with h | h
  · rw [h, zero_smul] at hst
    rcases htf _ _ hst with h' | h'
    · exact hs h'
    · exact hb h'
  · exact ha h

/-- **Idempotents of a torsion-free module of rank one.** Let `M` be an `𝒪_X`-module on an
integral scheme whose restriction maps to nonempty opens are injective, which vanishes on the
empty open, and whose sections over each nonempty affine open form a torsion-free module with
pairwise dependent elements. Then every idempotent endomorphism of `M` is `0` or `1`. -/
private theorem idempotent_eq_zero_or_id {X : Scheme.{0}} [IsIntegral X] (M : X.Modules)
    (hinj : ∀ (U V : X.Opens) (h : V ≤ U), (V : Set X).Nonempty →
      Function.Injective (M.presheaf.map (homOfLE h).op))
    (hemp : ∀ U : X.Opens, ¬ (U : Set X).Nonempty → Subsingleton Γ(M, U))
    (htf : ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty →
      ∀ (r : Γ(X, U)) (a : Γ(M, U)), r • a = 0 → r = 0 ∨ a = 0)
    (hdep : ∀ U : X.Opens, IsAffineOpen U → (U : Set X).Nonempty →
      ∀ a b : Γ(M, U), a ≠ 0 → ∃ s t : Γ(X, U), s ≠ 0 ∧ s • b = t • a)
    (e : M ⟶ M) (he : e ≫ e = e) : e = 0 ∨ e = 𝟙 M := by
  let eU : ∀ U : X.Opens, Γ(M, U) →ₗ[Γ(X, U)] Γ(M, U) := fun U =>
    { toFun := e.app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul e }
  have hidem : ∀ U x, e.app U (e.app U x) = e.app U x := fun U x => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, he]
  have hnat : ∀ (U V : X.Opens) (h : V ≤ U) (x : Γ(M, U)),
      M.presheaf.map (homOfLE h).op (e.app U x) = e.app V (M.presheaf.map (homOfLE h).op x) :=
    fun U V h x => by
      have := congr($(e.mapPresheaf.naturality (homOfLE h).op) x)
      simpa using this.symm
  -- every nonempty open contains a nonempty affine open
  have haff : ∀ W : X.Opens, (W : Set X).Nonempty →
      ∃ V : X.Opens, IsAffineOpen V ∧ (V : Set X).Nonempty ∧ V ≤ W := fun W hW => by
    obtain ⟨x, hx⟩ := hW
    obtain ⟨V, hV, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset (U := W) hx
    exact ⟨V, hV, ⟨x, hxV⟩, hVW⟩
  have hgen : ∀ W : X.Opens, (W : Set X).Nonempty → genericPoint X ∈ W := fun W hW =>
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  by_cases P : ∃ (U : X.Opens) (_ : IsAffineOpen U) (_ : (U : Set X).Nonempty) (a : Γ(M, U)),
      a ≠ 0 ∧ e.app U a = a
  · obtain ⟨U₀, hU₀, hU₀ne, a₀, ha₀, hea₀⟩ := P
    right
    ext W x
    by_cases hW : (W : Set X).Nonempty
    · obtain ⟨V, hV, hVne, hVle⟩ := haff (W ⊓ U₀)
        ⟨genericPoint X, hgen W hW, hgen U₀ hU₀ne⟩
      have hVW : V ≤ W := hVle.trans inf_le_left
      have hVU : V ≤ U₀ := hVle.trans inf_le_right
      set a := M.presheaf.map (homOfLE hVU).op a₀
      have ha : a ≠ 0 := fun h => ha₀ (hinj _ _ hVU hVne (h.trans (map_zero _).symm))
      have hea : e.app V a = a := by rw [← hnat, hea₀]
      set x' := M.presheaf.map (homOfLE hVW).op x
      have hx' : e.app V x' = x' := by
        by_cases hx0 : x' = 0
        · rw [hx0, map_zero]
        · exact (apply_eq_self_or_eq_zero_of_idempotent (htf V hV hVne) (hdep V hV hVne) (eU V)
            (hidem V) x' hx0).resolve_right (false_of_apply_eq_self_of_apply_eq_zero
              (htf V hV hVne) (hdep V hV hVne) (eU V) a x' ha hx0 hea)
      apply hinj _ _ hVW hVne
      rw [hnat]
      exact hx'
    · haveI := hemp W hW
      exact Subsingleton.elim _ _
  · left
    push Not at P
    ext W x
    by_cases hW : (W : Set X).Nonempty
    · obtain ⟨V, hV, hVne, hVW⟩ := haff W hW
      set x' := M.presheaf.map (homOfLE hVW).op x
      have hx' : e.app V x' = 0 := by
        by_cases hx0 : x' = 0
        · rw [hx0, map_zero]
        · exact (apply_eq_self_or_eq_zero_of_idempotent (htf V hV hVne) (hdep V hV hVne) (eU V)
            (hidem V) x' hx0).resolve_left (P V hV hVne x' hx0)
      apply hinj _ _ hVW hVne
      rw [hnat]
      simpa using hx'
    · haveI := hemp W hW
      exact Subsingleton.elim _ _

/-- **Idempotents of the direct image of a divisorial sheaf.** For a dominant morphism
`f : Y ⟶ X` of integral schemes inducing an isomorphism of function fields, with `Y` normal and
locally Noetherian, every idempotent endomorphism of `f_* 𝒪_Y(D)` is `0` or `1`. -/
private theorem idempotent_pushforward_divisorialSheaf {X Y : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (D : MMP.Mori.Divisor Y)
    (e : (Scheme.Modules.pushforward f).obj D.divisorialSheaf ⟶
      (Scheme.Modules.pushforward f).obj D.divisorialSheaf) (he : e ≫ e = e) :
    e = 0 ∨ e = 𝟙 _ := by
  haveI := MMP.Fourfold.subsingleton_irreducibleComponents (X := Y)
  have hcgp : ∀ Z : irreducibleComponents Y, MMP.Mori.componentGenericPoint Y Z = genericPoint Y :=
    MMP.Fourfold.componentGenericPoint_eq_genericPoint
  -- the generic point of `Y` lies over every nonempty open of `X`
  have hmem : ∀ U : X.Opens, (U : Set X).Nonempty → ∀ Z : irreducibleComponents Y,
      MMP.Mori.componentGenericPoint Y Z ∈ f ⁻¹ᵁ U := fun U hU Z => by
    rw [hcgp, Scheme.Hom.mem_preimage, map_genericPoint_of_isDominant]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hnmem : ∀ U : X.Opens, ¬ (U : Set X).Nonempty → ∀ Z : irreducibleComponents Y,
      MMP.Mori.componentGenericPoint Y Z ∉ f ⁻¹ᵁ U := fun U hU Z h =>
    hU ⟨_, h⟩
  -- sections are determined by their components
  have hext : ∀ (W : Y.Opens) (φ ψ : D.divisorialSubmodule W),
      (∀ Z h, φ.1 ⟨Z, h⟩ = ψ.1 ⟨Z, h⟩) → φ = ψ := fun W φ ψ h =>
    Subtype.ext (funext fun Z => h Z.1 Z.2)
  obtain ⟨Z₀⟩ : Nonempty (irreducibleComponents Y) := by
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    exact ⟨⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩⟩
  refine idempotent_eq_zero_or_id _ ?_ ?_ ?_ ?_ e he
  · intro U V h hV φ ψ hφψ
    refine hext _ φ ψ fun Z hZ => ?_
    have := congrArg (fun χ : D.divisorialSubmodule (f ⁻¹ᵁ V) => χ.1 ⟨Z, hmem V hV Z⟩) hφψ
    exact this
  · intro U hU
    exact ⟨fun φ ψ => hext _ φ ψ fun Z hZ => (hnmem U hU Z hZ).elim⟩
  · intro U hU hUne r a hra
    have hZ := hmem U hUne Z₀
    obtain ⟨hinj, -⟩ := germ_app_injective_and_exists f hf U hU _ (hcgp Z₀) hZ
    have h0 : Y.presheaf.germ (f ⁻¹ᵁ U) _ hZ (f.app U r) * a.1 ⟨Z₀, hZ⟩ = 0 :=
      congrArg (fun χ : D.divisorialSubmodule (f ⁻¹ᵁ U) => χ.1 ⟨Z₀, hZ⟩) hra
    rcases mul_eq_zero.mp h0 with h | h
    · left
      exact hinj (h.trans (by simp))
    · right
      refine hext _ a 0 fun Z h' => ?_
      obtain rfl : Z = Z₀ := Subsingleton.elim _ _
      exact h
  · intro U hU hUne a b ha
    have hZ := hmem U hUne Z₀
    obtain ⟨hinj, hex⟩ := germ_app_injective_and_exists f hf U hU _ (hcgp Z₀) hZ
    set g := fun r : Γ(X, U) => Y.presheaf.germ (f ⁻¹ᵁ U) _ hZ (f.app U r)
    have ha' : a.1 ⟨Z₀, hZ⟩ ≠ 0 := fun h => ha (hext _ a 0 fun Z h' => by
      obtain rfl : Z = Z₀ := Subsingleton.elim _ _
      exact h)
    obtain ⟨s₁, t₁, hs₁, h₁⟩ := hex (b.1 ⟨Z₀, hZ⟩)
    obtain ⟨s₂, t₂, hs₂, h₂⟩ := hex (a.1 ⟨Z₀, hZ⟩)
    haveI : Nonempty U := ⟨⟨_, (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr
      (by simpa using hUne)⟩⟩
    have hg0 : ∀ r, r ≠ 0 → g r ≠ 0 := fun r hr h => hr (hinj (h.trans (by simp [g])))
    have ht₂ : t₂ ≠ 0 := by
      rintro rfl
      exact mul_ne_zero (hg0 s₂ hs₂) ha' (h₂.trans (by simp [g]))
    refine ⟨s₁ * t₂, t₁ * s₂, mul_ne_zero hs₁ ht₂, hext _ _ _ fun Z hZ' => ?_⟩
    obtain rfl : Z₀ = Z := Subsingleton.elim _ _
    change g (s₁ * t₂) * b.1 ⟨Z₀, hZ⟩ = g (t₁ * s₂) * a.1 ⟨Z₀, hZ⟩
    have hgm : ∀ r r', g (r * r') = g r * g r' := fun r r' => by simp [g]
    have h₁' : g s₁ * b.1 ⟨Z₀, hZ⟩ = g t₁ := h₁
    have h₂' : g s₂ * a.1 ⟨Z₀, hZ⟩ = g t₂ := h₂
    rw [hgm, hgm]
    linear_combination (g t₂) * h₁' - (g t₁) * h₂'

private theorem idempotent_pushforward_exteriorPower {k : Type} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{0}} (rX : X ⟶ Spec (.of k)) (rY : Y ⟶ Spec (.of k)) (f : Y ⟶ X) (n : ℕ)
    [IsProjectiveVariety k rX] [IsProjectiveVariety k rY] [IsNormal X] [IsNormal Y]
    [SmoothOfRelativeDimension n rY] (hX : topologicalKrullDim X = n)
    (hfr : f ≫ rX = rY) (hbir : MMP.Mori.IsBirationalMorphism f) :
    ∀ e : (Scheme.Modules.pushforward f).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n) ⟶
        (Scheme.Modules.pushforward f).obj
          (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n),
      e ≫ e = e → e = 0 ∨ e = 𝟙 _ := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian rY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace rY
  haveI : Smooth rY := SmoothOfRelativeDimension.smooth n rY
  have hsm : MMP.Mori.IsSmoothScheme rY := MMP.Resolution.isSmoothScheme_of_smooth rY
  have hnY : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism rX rY hbir).symm.trans hX
  obtain ⟨K, hK⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme rY hsm hnY
  obtain ⟨eK⟩ :=
    Proof_lem_mmp_relative_snc_ample_gap_vanishing.nonempty_divisorialSheaf_iso_exteriorPower hsm hK
  haveI := hbir.isDominant
  exact idempotent_trivial_of_iso ((Scheme.Modules.pushforward f).mapIso eK)
    (idempotent_pushforward_divisorialSheaf f hbir.functionFieldMap_bijective K)

/-! ### Grauert–Riemenschneider vanishing -/

/-- **Grauert–Riemenschneider vanishing**: `R^q f_* ω_Y = 0` for `q > 0`. -/
private theorem isZero_rightDerived_exteriorPower {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} (rX : X ⟶ Spec (.of k)) (rY : Y ⟶ Spec (.of k)) (f : Y ⟶ X)
    (n : ℕ) [IsProjectiveVariety k rX] [IsProjectiveVariety k rY] [IsNormal X] [IsNormal Y]
    [SmoothOfRelativeDimension n rY] (hX : topologicalKrullDim X = n)
    (hfr : f ≫ rX = rY) (hbir : MMP.Mori.IsBirationalMorphism f) (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n)) := by
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian rY
  haveI : Smooth rY := SmoothOfRelativeDimension.smooth n rY
  have hsm : MMP.Mori.IsSmoothScheme rY := MMP.Resolution.isSmoothScheme_of_smooth rY
  have hnY : topologicalKrullDim Y = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism rX rY hbir).symm.trans hX
  have h0 : (0 : MMP.Mori.QDivisor Y).IsNef k rY :=
    have ⟨h0, h⟩ := (MMP.Mori.QDivisor.isNumericallyTrivial_iff 0).mp
      (MMP.Mori.QDivisor.NumericallyEquivalent.refl (k := k) (sX := rY)
        MMP.Mori.QDivisor.isQCartier_zero)
    ⟨h0, fun C i _ _ _ hC => (h C i hC).ge⟩
  have hB : (MMP.Mori.Divisor.toQDivisor (0 : MMP.Mori.Divisor Y)).NumericallyEquivalent k rY
      (0 + 0) := by
    simpa using MMP.Mori.QDivisor.NumericallyEquivalent.refl (k := k) (sX := rY)
      (MMP.Mori.QDivisor.isQCartier_zero (X := Y))
  have hKV := MMP.Mori.isZero_rightDerived_pushforward_exteriorPower_tensor_divisorialSheaf rX rY
    hsm f hfr hbir hnY 0 0 0 h0 (MMP.Mori.DivisorWithCoeffs.isSNC_zero rY) (fun _ => le_rfl)
    (fun _ => zero_lt_one) hB q hq
  let T := Stacks.SheafOfModules.Tensor.sheafTensor Y.toRingedSpace.sheaf
  let ω := Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n
  exact hKV.of_iso (((Scheme.Modules.pushforward f).rightDerived q).mapIso
    ((T.obj ω).mapIso MMP.Mori.Divisor.divisorialSheafZeroIso ≪≫
      (Stacks.SheafOfModules.sheafTensorUnitNatIso Y.toRingedSpace.sheaf).app ω).symm)

section Standard

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

/-- The cohomology of `Rf_*(M[m])` in degree `i` is that of `Rf_*(M[0])` in degree `i + m`. -/
private noncomputable def homologyDerivedPushforwardSingleIso {X Y : Scheme.{0}} (f : Y ⟶ X)
    (M : Y.Modules) (m i j : ℤ) (h : m + i = j) :
    (DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward f).obj ((DerivedCategory.singleFunctor Y.Modules (-m)).obj M)) ≅
      (DerivedCategory.homologyFunctor X.Modules j).obj
        ((derivedPushforward f).obj ((DerivedCategory.singleFunctor Y.Modules 0).obj M)) :=
  (DerivedCategory.homologyFunctor X.Modules i).mapIso
      ((derivedPushforward f).mapIso
          (((DerivedCategory.singleFunctors Y.Modules).shiftIso m (-m) 0 (by omega)).app M).symm ≪≫
        ((derivedPushforward f).commShiftIso m).app _) ≪≫
    ((DerivedCategory.homologyFunctor X.Modules 0).shiftIso m i j h).app _

/-- With Grauert–Riemenschneider vanishing, `Rf_*(ω_Y[n])` has no cohomology outside degree
`-n`. -/
private theorem isZero_homology_derivedPushforward_single_exteriorPower {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Y : Scheme.{0}} (rX : X ⟶ Spec (.of k))
    (rY : Y ⟶ Spec (.of k)) (f : Y ⟶ X) (n : ℕ) [IsProjectiveVariety k rX]
    [IsProjectiveVariety k rY] [IsNormal X] [IsNormal Y] [SmoothOfRelativeDimension n rY]
    (hX : topologicalKrullDim X = n) (hfr : f ≫ rX = rY) (hbir : MMP.Mori.IsBirationalMorphism f)
    (i : ℤ) (hi : i ≠ -n) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor Y.Modules (-(n : ℤ))).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n)))) := by
  refine IsZero.of_iso ?_ (homologyDerivedPushforwardSingleIso f _ n i (n + i) rfl)
  rcases lt_or_gt_of_ne (show (n : ℤ) + i ≠ 0 by omega) with h | h
  · exact isZero_homology_derivedPushforward_of_neg f _ _ h
  · obtain ⟨q, hq⟩ : ∃ q : ℕ, (n : ℤ) + i = q := ⟨(n + i).toNat, by omega⟩
    obtain ⟨e⟩ := nonempty_homology_derivedPushforward_iso_rightDerived f
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n) q
    rw [hq]
    exact (isZero_rightDerived_exteriorPower rX rY f n hX hfr hbir q (by omega)).of_iso e

/-- The cohomology of `Rf_*(ω_Y[n])` in degree `-n` is `f_* ω_Y`. -/
private theorem nonempty_homology_derivedPushforward_single_iso {X Y : Scheme.{0}} (f : Y ⟶ X)
    (M : Y.Modules) (m : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor X.Modules (-(m : ℤ))).obj ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor Y.Modules (-(m : ℤ))).obj M)) ≅
        (Scheme.Modules.pushforward f).obj M) := by
  obtain ⟨e⟩ := nonempty_homology_derivedPushforward_iso_rightDerived f M 0
  exact ⟨homologyDerivedPushforwardSingleIso f M m (-m) 0 (by omega) ≪≫ e ≪≫
    (Functor.rightDerivedZeroIsoSelf (Scheme.Modules.pushforward f)).app M⟩

/-- `R𝓗om(B, K)` vanishes when `K` does: it represents `Hom(- ⊗^L B, K)`. -/
private theorem isZero_derivedSheafHom_of_isZero (X : Scheme.{0}) (B : DerivedCategory X.Modules)
    {K : DerivedCategory X.Modules} (hK : IsZero K) :
    IsZero (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op B)).obj K) := by
  rw [IsZero.iff_id_eq_zero]
  have e := RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite X.sheaf)
    (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op B)).obj K) B K
  obtain ⟨e', -⟩ := e
  haveI : Subsingleton (((Stacks.SheafOfModules.derivedTensorProductFunctor
      (Stacks.SheafOfModules.ringedSite X.sheaf)).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op B)).obj K)).obj B ⟶ K) :=
    ⟨fun a b => hK.eq_of_tgt a b⟩
  exact (e'.subsingleton).elim _ _

/-- The structure sheaf in degree `0` is not zero on a nonempty scheme. -/
private theorem not_isZero_singleFunctor_unit (X : Scheme.{0}) [Nonempty X] :
    ¬ IsZero ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf)) := by
  intro h
  have h₀ : IsZero (SheafOfModules.unit X.ringCatSheaf) :=
    ((DerivedCategory.homologyFunctor X.Modules 0).map_isZero h).of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app _).symm
  have h₁ := (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map_isZero h₀
  rw [ModuleCat.isZero_iff_subsingleton] at h₁
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hne : (0 : Γ(X, ⊤)) ≠ 1 := by
    haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    exact zero_ne_one
  exact hne (@Subsingleton.elim _ h₁ _ _)

/-- The cohomology sheaves of `Rf_* 𝒪_Y` are coherent for proper `f`. -/
private theorem isCoherent_homology_derivedPushforward_unit {X Y : Scheme.{0}} (f : Y ⟶ X)
    [IsProper f] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)))).IsCoherent := by
  rcases lt_or_ge i 0 with hi | hi
  · exact (Stacks.SheafOfModules.isCoherent_of_isZero
      (isZero_homology_derivedPushforward_of_neg f _ i hi)).rootIsCoherent
  · obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = q := ⟨i.toNat, by omega⟩
    obtain ⟨e⟩ := nonempty_homology_derivedPushforward_iso_rightDerived f
      (SheafOfModules.unit Y.ringCatSheaf) q
    have h := ProperCoherenceWitness.higherDirectImageIsCoherent Y X f inferInstance inferInstance _
      (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit Y) q
    exact isCoherent_of_modulesIso
      (e ≪≫ (Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app _).symm h

/-- The cohomology sheaves of `𝒪_X[0]` are coherent on a locally Noetherian scheme. -/
private theorem isCoherent_homology_singleFunctor_unit (X : Scheme.{0}) [IsLocallyNoetherian X]
    (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))).IsCoherent := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · exact (Stacks.SheafOfModules.isCoherent_of_isZero
      (@DerivedCategory.isZero_of_isGE _ _ _ (HasDerivedCategory.standard X.Modules) _ 0 i hi
        (@DerivedCategory.instIsGEObjSingleFunctor _ _ _ (HasDerivedCategory.standard X.Modules)
          _ _))).rootIsCoherent
  · exact isCoherent_of_modulesIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app _).symm
      (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit X)
  · exact (Stacks.SheafOfModules.isCoherent_of_isZero
      (@DerivedCategory.isZero_of_isLE _ _ _ (HasDerivedCategory.standard X.Modules) _ 0 i hi
        (@DerivedCategory.instIsLEObjSingleFunctor _ _ _ (HasDerivedCategory.standard X.Modules)
          _ _))).rootIsCoherent

/-- An object of the derived category whose cohomology sheaves all vanish is zero. -/
private theorem isZero_of_forall_isZero_homology {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C)
    (h : ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor C i).obj K)) : IsZero K := by
  open ZeroObject in
  have : IsIso (0 : K ⟶ 0) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    exact isIso_of_source_target_iso_zero _ (h i).isoZero
      ((DerivedCategory.homologyFunctor C i).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

/-- **The dualized splitting.** Let `K`, `O`, `C` be objects of `D(𝒪_X)` such that biduality
with respect to `K` holds on `O` and on `C`, `O` is nonzero, `R𝓗om(O, K) ≅ K`, and `R𝓗om(C, K)` is
isomorphic to an object `P` concentrated in degree `m` whose cohomology there has only the trivial
idempotents. Then every split monomorphism `v : O ⟶ C` is an isomorphism. -/
private theorem isIso_of_isSplitMono_of_derivedSheafHom_iso {X : Scheme.{0}}
    (K P O C : DerivedCategory X.Modules) (m : ℤ) (hO : ¬ IsZero O)
    (hbO : IsIso (RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite X.sheaf) K O))
    (hbC : IsIso (RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite X.sheaf) K C))
    (ε : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op O)).obj K ≅ K)
    (φ : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op C)).obj K ≅ P)
    (hP : ∀ i : ℤ, i ≠ m → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj P))
    (hPm : ∀ e : (DerivedCategory.homologyFunctor X.Modules m).obj P ⟶
        (DerivedCategory.homologyFunctor X.Modules m).obj P, e ≫ e = e → e = 0 ∨ e = 𝟙 _)
    (v : O ⟶ C) [IsSplitMono v] : IsIso v := by
  let D := Stacks.SheafOfModules.derivedSheafHom X.sheaf
  let H := fun i : ℤ => DerivedCategory.homologyFunctor X.Modules i
  let t : (D.obj (op C)).obj K ⟶ (D.obj (op O)).obj K := (D.map v.op).app K
  let s : (D.obj (op O)).obj K ⟶ (D.obj (op C)).obj K := (D.map (retraction v).op).app K
  have h1 : (D.map (v ≫ retraction v).op).app K = 𝟙 _ :=
    (congrArg (fun g => (D.map g.op).app K) (IsSplitMono.id v)).trans
      ((congrArg (fun g => NatTrans.app g K) (D.map_id (op O))).trans (NatTrans.id_app _ K))
  have hst : s ≫ t = 𝟙 _ :=
    (NatTrans.comp_app (D.map (retraction v).op) (D.map v.op) K).symm.trans
      ((congrArg (fun g => NatTrans.app g K) (D.map_comp (retraction v).op v.op)).symm.trans h1)
  have hst' : ∀ i, (H i).map s ≫ (H i).map t = 𝟙 _ := fun i =>
    ((H i).map_comp s t).symm.trans ((congrArg (H i).map hst).trans ((H i).map_id _))
  have hDC : ∀ i, i ≠ m → IsZero ((H i).obj ((D.obj (op C)).obj K)) := fun i hi =>
    (hP i hi).of_iso ((H i).mapIso φ)
  have hDO : ∀ i, i ≠ m → IsZero ((H i).obj ((D.obj (op O)).obj K)) := fun i hi => by
    rw [IsZero.iff_id_eq_zero, ← hst' i, (hDC i hi).eq_zero_of_tgt ((H i).map s), zero_comp]
  have hnz : ¬ IsZero ((H m).obj ((D.obj (op O)).obj K)) := by
    intro hz
    have hall : IsZero ((D.obj (op O)).obj K) := isZero_of_forall_isZero_homology _ fun i => by
      by_cases hi : i = m
      · subst hi; exact hz
      · exact hDO i hi
    have hK : IsZero K := hall.of_iso ε.symm
    exact hO ((isZero_derivedSheafHom_of_isZero X _ hK).of_iso (@asIso _ _ _ _ _ hbO))
  have ht : IsIso t := by
    rw [DerivedCategory.isIso_iff]
    intro i
    by_cases hi : i = m
    · subst hi
      exact isIso_of_retraction (idempotent_trivial_of_iso ((H i).mapIso φ).symm hPm)
        ((H i).map t) ((H i).map s) (hst' i) hnz
    · exact isIso_of_source_target_iso_zero _ (hDC i hi).isoZero (hDO i hi).isoZero
  have hnat := RingedSite.derivedBiduality_naturality (Stacks.SheafOfModules.ringedSite X.sheaf) K v
  have hDD : IsIso ((D.map t.op).app K) :=
    Iso.isIso_hom ((D.mapIso (@asIso _ _ _ _ t ht).op).app K)
  have h3 : IsIso (v ≫ RingedSite.derivedBiduality (Stacks.SheafOfModules.ringedSite X.sheaf) K C) :=
    (congrArg IsIso hnat).mpr (IsIso.comp_isIso' hbO hDD)
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ v _ hbC h3

/-- **The standard-model statement.** Under the hypotheses of the duality comparison, every split
monomorphism `𝒪_X[0] ⟶ Rf_* 𝒪_Y[0]` of the standard model of the derived categories is an
isomorphism. -/
private theorem isIso_of_isSplitMono_standard {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}}
    (rX : X ⟶ Spec (.of k)) (rY : Y ⟶ Spec (.of k)) (f : Y ⟶ X) (n : ℕ)
    [IsProjectiveVariety k rX] [IsProjectiveVariety k rY] [IsNormal X] [IsNormal Y]
    [SmoothOfRelativeDimension n rY] (hX : topologicalKrullDim X = n)
    (hfr : f ≫ rX = rY) (hf : IsProjectiveMorphism f) (hbir : MMP.Mori.IsBirationalMorphism f)
    (v : (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard X.Modules) 0).obj
        (SheafOfModules.unit X.ringCatSheaf) ⟶
      (@derivedPushforward _ _ f (HasDerivedCategory.standard Y.Modules)
        (HasDerivedCategory.standard X.Modules)).obj
        ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard Y.Modules) 0).obj
          (SheafOfModules.unit Y.ringCatSheaf)))
    [IsSplitMono v] : IsIso v := by
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hf
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace rX
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated rX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace rY
  haveI : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated rY
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian rX
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian rY
  obtain ⟨hD, hbid, ψ, φ, -, -⟩ :=
    MMP.Duality.dual_unit_eq_trace_of_isBirationalMorphism rX rY f n hX hfr hf hbir
      (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
        (Stacks.SheafOfModules.ringedSite X.sheaf))
      (Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomAdjunction
        (Stacks.SheafOfModules.ringedSite Y.sheaf))
      rfl rfl (twistedInverseImageAdjunction rX _) (twistedInverseImageAdjunction f _)
  obtain ⟨eω⟩ := nonempty_homology_derivedPushforward_single_iso f
    (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials rY) n) n
  exact isIso_of_isSplitMono_of_derivedSheafHom_iso _ _ _ _ (-(n : ℤ))
    (not_isZero_singleFunctor_unit X) (hbid _ (isCoherent_homology_singleFunctor_unit X))
    (hbid _ (isCoherent_homology_derivedPushforward_unit f))
    ((RingedSite.derivedStructureSheafHomNatIso (Stacks.SheafOfModules.ringedSite X.sheaf)).app _)
    φ (fun i hi => isZero_homology_derivedPushforward_single_exteriorPower rX rY f n hX hfr hbir i hi)
    (idempotent_trivial_of_iso eω.symm
      (idempotent_pushforward_exteriorPower rX rY f n hX hfr hbir)) v

end Standard

open scoped Stacks.SmallDerivedModel

end Proof_lem_mmp_projective_split_unit_rationality

end

section

open CategoryTheory AlgebraicGeometry Stacks.Duality
open scoped Stacks.SmallDerivedModel

namespace MMP.Duality

open Proof_lem_mmp_projective_split_unit_rationality
open CategoryTheory AlgebraicGeometry Stacks.Duality Opposite Limits

/-- **A split structural unit is an isomorphism.** Let `f : Y ⟶ X` be a projective birational
morphism of normal projective varieties of dimension `n` over an algebraically closed field `k`
of characteristic zero, with structure morphisms `r_X` and `r_Y = f ≫ r_X`, and `Y` smooth of
relative dimension `n` over `k`. If the structural unit `u : 𝒪_X ⟶ Rf_* 𝒪_Y` has a left inverse
in the derived category, then `u` is an isomorphism, and the cohomology sheaves
`R^i f_* 𝒪_Y` vanish for all `i > 0`. -/
@[mmp "lem_mmp_projective_split_unit_rationality"]
public theorem isIso_unit_of_isSplitMono {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}}
    (rX : X ⟶ Spec (.of k)) (rY : Y ⟶ Spec (.of k)) (f : Y ⟶ X) (n : ℕ)
    [IsProjectiveVariety k rX] [IsProjectiveVariety k rY] [IsNormal X] [IsNormal Y]
    [SmoothOfRelativeDimension n rY] (hX : topologicalKrullDim X = n)
    (hfr : f ≫ rX = rY) (hf : IsProjectiveMorphism f) (hbir : MMP.Mori.IsBirationalMorphism f) :
    let u : (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (derivedPushforward f).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
      (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
        DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor X.Modules 0).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (HomotopyCategory.quotient _ _).map
            ((HomologicalComplex.singleMapHomologicalComplex
              (Scheme.Modules.pushforward f) _ 0).inv.app _)) ≫
        ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
            ((HomotopyCategory.singleFunctor Y.Modules 0).obj
              (SheafOfModules.unit Y.ringCatSheaf)) ≫
        (derivedPushforward f).map
          ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _)
    IsSplitMono u → IsIso u ∧ ∀ i : ℤ, 0 < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward f).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj
            (SheafOfModules.unit Y.ringCatSheaf)))) := by
  intro u hu
  have hiso : IsIso u := by
    let EX := StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard X.Modules)
      (Scheme.Modules.hasDerivedCategory X)
    let a := (StacksDraft.DerivedModel.modelSingleFunctorIso (HasDerivedCategory.standard X.Modules)
      (Scheme.Modules.hasDerivedCategory X) 0).app (SheafOfModules.unit X.ringCatSheaf)
    let b := (derivedPushforward f).mapIso
        ((StacksDraft.DerivedModel.modelSingleFunctorIso (HasDerivedCategory.standard Y.Modules)
          (Scheme.Modules.hasDerivedCategory Y) 0).app (SheafOfModules.unit Y.ringCatSheaf)).symm ≪≫
      ((Stacks.Duality.StandardModel.derivedPushforwardModelIso f).app
        (@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard Y.Modules) 0 |>.obj
          (SheafOfModules.unit Y.ringCatSheaf))).symm
    let w := a.hom ≫ u ≫ b.hom
    let v := EX.fullyFaithfulFunctor.preimage w
    haveI : IsSplitMono v := by
      refine IsSplitMono.mk' ⟨EX.fullyFaithfulFunctor.preimage (b.inv ≫ retraction u ≫ a.inv), ?_⟩
      apply EX.fullyFaithfulFunctor.map_injective
      simp [v, w]
    have hv : IsIso v := isIso_of_isSplitMono_standard rX rY f n hX hfr hf hbir v
    have hw : IsIso w := by
      have : w = EX.functor.map v := by simp [v]
      rw [this]
      infer_instance
    have : u = a.inv ≫ w ≫ b.inv := by simp [w]
    rw [this]
    infer_instance
  refine ⟨hiso, fun i hi => ?_⟩
  have h0 : IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf))) :=
    @DerivedCategory.isZero_of_isLE _ _ _ (Scheme.Modules.hasDerivedCategory X) _ 0 i hi
      (@DerivedCategory.instIsLEObjSingleFunctor _ _ _ (Scheme.Modules.hasDerivedCategory X) _ _)
  exact h0.of_iso ((DerivedCategory.homologyFunctor X.Modules i).mapIso (asIso u)).symm

end MMP.Duality

end

/-! ### `thm_mmp_projective_klt_log_resolution_vanishing` -/

section

namespace Proof_thm_mmp_projective_klt_log_resolution_vanishing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Duality MMP.Mori
open scoped Stacks.SmallDerivedModel

section SingleComparison

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (w : A ⥤ B) [w.Additive] (Rw : DerivedCategory A ⥤ DerivedCategory B)
  (α : w.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rw)

/-- The comparison `w(M)[0] ⟶ Rw(M[0])` given by the unit `α` of a right derived functor. -/
private noncomputable def singleComparison : w ⋙ DerivedCategory.singleFunctor B 0 ⟶
    DerivedCategory.singleFunctor A 0 ⋙ Rw where
  app M := (DerivedCategory.singleFunctorIsoCompQh B 0).hom.app (w.obj M) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((HomologicalComplex.singleMapHomologicalComplex w _ 0).inv.app M)) ≫
      α.app ((HomotopyCategory.singleFunctor A 0).obj M) ≫
      Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M)
  naturality M N g := by
    have h1 := (DerivedCategory.singleFunctorIsoCompQh B 0).hom.naturality (w.map g)
    have h2 := (HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) 0).inv.naturality g
    have h3 := α.naturality ((HomotopyCategory.singleFunctor A 0).map g)
    have h4 := (DerivedCategory.singleFunctorIsoCompQh A 0).inv.naturality g
    simp only [Functor.comp_obj, Functor.comp_map] at h1 h2 h3 h4
    simp only [Functor.comp_obj, Functor.comp_map, Category.assoc]
    have h2' : DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor B 0).map (w.map g)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) 0).inv.app N)) =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) 0).inv.app M)) ≫
        DerivedCategory.Qh.map ((w.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.singleFunctor A 0).map g)) := by
      have := congrArg (fun t => DerivedCategory.Qh.map
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map t)) h2
      simp only [Functor.map_comp] at this
      exact this
    have h34 : DerivedCategory.Qh.map ((w.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.singleFunctor A 0).map g)) ≫
        α.app ((HomotopyCategory.singleFunctor A 0).obj N) ≫
          Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app N) =
        α.app ((HomotopyCategory.singleFunctor A 0).obj M) ≫
          Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M) ≫
            Rw.map ((DerivedCategory.singleFunctor A 0).map g) := by
      rw [reassoc_of% h3, ← Rw.map_comp, h4, Rw.map_comp]
    rw [reassoc_of% h1]
    exact congrArg (_ ≫ ·) <| ((reassoc_of% h2') _).trans <| (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ ·) (h34.trans (Category.assoc _ _ _).symm)

/-- The comparison `w(M)[0] ⟶ Rw(M[0])` of a left exact `w` is an isomorphism at an object `M`
with `Rⁿw(M) = 0` for every `n > 0`: both sides have cohomology only in degree `0`, where the
comparison is `R⁰w ≅ w`. -/
private theorem isIso_singleComparison_app [Rw.CommShift ℤ] [Rw.IsTriangulated]
    [Rw.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [EnoughInjectives A] [PreservesFiniteLimits w]
    (hGE : ∀ M : A, (Rw.obj ((DerivedCategory.singleFunctor A 0).obj M)).IsGE 0)
    (hres : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    (M : A) (hM : ∀ n : ℕ, 0 < n → IsZero ((w.rightDerived n).obj M)) :
    IsIso ((singleComparison w Rw α).app M) := by
  rw [DerivedCategory.isIso_iff]
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have h₁ : IsZero ((DerivedCategory.homologyFunctor B n).obj
        ((DerivedCategory.singleFunctor B 0).obj (w.obj M))) :=
      DerivedCategory.isZero_of_isGE _ 0 n hn
    have := hGE M
    have h₂ : IsZero ((DerivedCategory.homologyFunctor B n).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj M))) :=
      DerivedCategory.isZero_of_isGE _ 0 n hn
    exact IsZero.isIso h₁ h₂ _
  · have h := Stacks.DerivedFunctor.isIso_singleUnitHomology_app w Rw α hGE
      (fun J hJ => Stacks.DerivedFunctor.isIso_unit_app_single_of_injective w Rw α hres J hJ) M
    rw [Stacks.DerivedFunctor.singleUnitHomology_app] at h
    simp only [singleComparison, Functor.comp_obj, Functor.map_comp]
    have i₁ : IsIso ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) 0).inv.app M)) :=
      Functor.map_isIso _ _
    have i₂ : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex w (ComplexShape.up ℤ) 0).inv.app M))) :=
      Functor.map_isIso _ _
    refine IsIso.comp_isIso' inferInstance
      (IsIso.comp_isIso' ((DerivedCategory.homologyFunctor B 0).mapIso (@asIso _ _ _ _ _ i₂)).isIso_hom ?_)
    exact (congrArg IsIso ((DerivedCategory.homologyFunctor B 0).map_comp _ _)).mpr
      (IsIso.comp_isIso' h inferInstance)
  · have h₁ : IsZero ((DerivedCategory.homologyFunctor B n).obj
        ((DerivedCategory.singleFunctor B 0).obj (w.obj M))) :=
      DerivedCategory.isZero_of_isLE _ 0 n hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
    have h₂ : IsZero ((DerivedCategory.homologyFunctor B (m : ℤ)).obj
        (Rw.obj ((DerivedCategory.singleFunctor A 0).obj M))) :=
      (hM m (by exact_mod_cast hn)).of_iso
        ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived w Rw α hres m).app M)
    exact IsZero.isIso h₁ h₂ _

/-- The structural map `N[0] ⟶ Rw(M[0])` built from `φ : N ⟶ w(M)` factors as `φ[0]` followed by
the comparison `w(M)[0] ⟶ Rw(M[0])`. -/
private theorem comp_eq_singleFunctor_map_comp_singleComparison_app {N : B} {M : A}
    (φ : N ⟶ w.obj M) :
    (DerivedCategory.singleFunctorIsoCompQh B 0).hom.app N ≫
        DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor B 0).map φ ≫
          (HomotopyCategory.quotient _ _).map
            ((HomologicalComplex.singleMapHomologicalComplex w _ 0).inv.app M)) ≫
        α.app ((HomotopyCategory.singleFunctor A 0).obj M) ≫
        Rw.map ((DerivedCategory.singleFunctorIsoCompQh A 0).inv.app M) =
      (DerivedCategory.singleFunctor B 0).map φ ≫ (singleComparison w Rw α).app M := by
  have h := (DerivedCategory.singleFunctorIsoCompQh B 0).hom.naturality φ
  simp only [Functor.comp_map] at h
  erw [Functor.map_comp, reassoc_of% h]
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _)

end SingleComparison

section KltVanishing

/-- A `ℚ`-divisor whose components have their generic points in an snc subset `S` is snc: each
such component is one of the prime divisors whose union is `S`. -/
private theorem isSNC_of_forall_genericPoint_mem {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY)
    {S : TopologicalSpace.Closeds Y} (hS : IsSNCSubset sY S) (D : QDivisor Y)
    (hD : ∀ E, D E ≠ 0 → E.genericPoint ∈ S) : D.IsSNC sY := by
  classical
  rcases hS with rfl | ⟨s, hs, hsnc⟩
  · refine (DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme (R := ℚ) sY hsm).of_support_subset
      fun E hE => ?_
    have h := hD E (Finsupp.mem_support_iff.1 hE)
    rw [← SetLike.mem_coe, TopologicalSpace.Closeds.coe_bot] at h
    exact h.elim
  · refine hsnc.of_support_subset fun E hE => ?_
    have h := hD E (Finsupp.mem_support_iff.1 hE)
    rw [← SetLike.mem_coe, ← hs, Set.mem_iUnion₂] at h
    obtain ⟨E', hE', hm⟩ := h
    obtain rfl := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hm
    rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hE']

/-- The discrepancy of a non-exceptional divisor `(Y, f, E)` over a pair `(X, Δ)` is
`-coeff_P(Δ)`, where `P` is the prime divisor of `X` with generic point `f(η_E)`. -/
private theorem exists_eq_neg_coeff_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D : DivisorOver k sX} {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) (hE : ¬ D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint = P.genericPoint ∧ a = -Δ.coeff P := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hmτ⟩ := ha
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hE
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
  have hx : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hPU : (P.support ∩ (U : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hx ▸ hU⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have e := hτ.2 P hPU
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  refine ⟨P, hx, mul_left_cancel₀ hm0 ?_⟩
  linear_combination hmτ + e

/-- A divisor over `(X, Δ)` with nonzero discrepancy is exceptional or lies over `Supp Δ`. -/
private theorem genericPoint_mem_of_isDiscrepancy_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {Y : Scheme.{u}} {f : Y ⟶ X} {hY : IsNormalVariety k (f ≫ sX)} {hf : IsBirationalMorphism f}
    {E : MMP.Mori.PrimeDivisor Y} {a : ℚ} (ha : IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, E⟩ a)
    (ha0 : a ≠ 0) :
    E.genericPoint ∈ exceptionalSet f ⊔ (QDivisor.toRDivisor Δ).supp.preimage f.continuous := by
  by_cases hex : (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).IsExceptional
  · exact Or.inl (MMP.Positivity.support_subset_exceptionalSet E hex
      (MMP.Flips.primeDivisor_genericPoint_mem_support E))
  obtain ⟨Q, hfE, hQ⟩ := exists_eq_neg_coeff_of_not_isExceptional ha hex
  refine Or.inr (DivisorWithCoeffs.mem_supp_iff.2 ⟨Q, ?_, ?_⟩)
  · rw [QDivisor.coeff_toRDivisor, Rat.cast_ne_zero]
    rintro h
    exact ha0 (by rw [hQ, h, neg_zero])
  · exact hfE ▸ MMP.Flips.primeDivisor_genericPoint_mem_support Q

/-- If `-1 < c`, then `⌈max c 0⌉ - c` lies in `[0, 1)`: the coefficient of `A + {-B}` at a
divisor of discrepancy `c` over a klt pair. -/
private theorem ceil_max_zero_sub_mem_Ico {c : ℚ} (hc : -1 < c) :
    0 ≤ (⌈max c 0⌉ : ℚ) - c ∧ (⌈max c 0⌉ : ℚ) - c < 1 := by
  rcases le_or_gt 0 c with h | h
  · rw [max_eq_left h]
    exact ⟨by linarith [Int.le_ceil c], by linarith [Int.ceil_lt_add_one c]⟩
  · rw [max_eq_right h.le, Int.ceil_zero, Int.cast_zero]
    constructor <;> linarith

/-- On a smooth birational model `f : Y ⟶ X`, the pull-back `f^*ω` of a rational `n`-form with
canonical divisor `div ω` has canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (hYsm : IsSmoothScheme (f ≫ sX)) :
    (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n := by
  have hn := hK.topologicalKrullDim_eq
  haveI : AlgebraicGeometry.IsVariety k sX := hX.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hYsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hf).symm.trans hn)
  exact hK₀.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
        hf.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0)

/-- The pull-back to `Y` of a `ℚ`-Cartier `ℚ`-divisor of `X` is `f`-nef: it has degree zero on
every curve contracted by `f`. -/
private theorem isRelativelyNef_neg_of_isPullback {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] {D : QDivisor X} (hD : D.IsQCartier)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    {D' : QDivisor Y} (hp : D.IsPullback f hB D') :
    (-D').IsRelativelyNef (f ≫ sX) f := by
  obtain ⟨Dc, Dc', hDc, hDB, -, hDc'q, hpc⟩ := hp.exists_cartierIndex hD
  have hDB' : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ (-Dc).supp :=
    fun Z hZ => hDB Z (by simpa using hZ)
  have hpn : Divisor.IsPullback f (-Dc) hDB' (-Dc') := by
    have := hpc.zsmul hDc (-1) (by simpa using hDB')
    simpa using this
  have hq : (-D').IsQCartier := MMP.Fourfold.Oai4C1.isQCartier_neg (hp.isQCartier hD)
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg (f ≫ sX) hq
    fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul k _ C.ι C.dim_le _ hq (QDivisor.cartierIndex_pos hD)
    (-Dc') (hpc.isCartier hDc).neg (by rw [map_neg, hDc'q, smul_neg])]
  have he := hpn.eq hDc.neg (Divisor.isPullback_pullback hDc.neg hDB')
  have h0 := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy f rfl hDc.neg hDB' C hC
  have h1 : Divisor.degreeOn k (f ≫ sX) C.ι C.dim_le (-Dc') (hpc.isCartier hDc).neg = 0 := by
    simp only [he]
    exact h0
  rw [h1]
  simp

open RingedSpaceModuleAdjunction Stacks.RingedSpace Stacks.AffineProjectionFormula in
/-- For a proper birational morphism `f : Y ⟶ X` onto a normal variety, `f_* f^* N ≅ N` for an
invertible `N`: by the projection formula `f_*(𝒪_Y ⊗ f^*N) ≅ f_*𝒪_Y ⊗ N`, and `f_*𝒪_Y = 𝒪_X`. -/
private noncomputable def pushforwardPullbackIso {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] :
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj N) ≅ N :=
  haveI : ∀ U, IsIso (f.c.app U) := fun U =>
    MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism (f ≫ sX) sX hY hX f hf U.unop
  haveI : IsIso f.c := NatIso.isIso_of_isIso_app _
  haveI : IsIso (unitToPushforwardStructure f.toLRSHom.toShHom) :=
    isIso_unitToPushforwardObjUnit_of_isIso_c f inferInstance
  haveI := (MMP.Resolution.Bridges.isIso_projectionFormulaMap_and_tmul f
    (structureModule Y.toRingedSpace) N).1
  (pushforwardFunctor f.toLRSHom.toShHom).mapIso
      (structureUnitor ((pullbackFunctor f.toLRSHom.toShHom).obj N)).symm ≪≫
    (asIso (Stacks.ProjectionFormula.projectionFormulaMap' f.toLRSHom.toShHom
      (structureModule Y.toRingedSpace) N)).symm ≪≫
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0}
      X.sheaf)).mapIso ((asIso (unitToPushforwardStructure f.toLRSHom.toShHom)).symm.prod
        (Iso.refl N)) ≪≫
    structureUnitor N

/-- For a proper birational morphism onto a normal variety, the pull-back of an invertible
module has generic rank one. -/
private theorem relativeGenericRank_pullback_eq_one {k : Type} [Field k] {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : AlgebraicGeometry.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    [IrreducibleSpace Y] (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N] :
    relativeGenericRank f ((Scheme.Modules.pullback f).obj N) = 1 := by
  unfold relativeGenericRank
  rw [Scheme.Modules.fiberRank_eq_of_iso (pushforwardPullbackIso sX hX f hY hf N)]
  exact Scheme.Modules.fiberRank_eq_of_isFiniteLocallyFreeOfRank N 1 _

/-- On the source of a proper birational morphism `f : Y ⟶ X` onto a normal variety, the
negative of the pull-back of a `ℚ`-Cartier `ℚ`-divisor is `f`-big: `f` has relative dimension
zero and every `f_* 𝒪_Y(k D)` with `D` a pulled-back Cartier divisor has generic rank one. -/
private theorem isRelativelyBig_neg_of_isPullback {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) (hY : AlgebraicGeometry.IsVariety k (f ≫ sX))
    [IsProper f] [IsDominant f] (hf : IsBirationalMorphism f) {n : ℕ}
    (hnY : topologicalKrullDim Y = n) (hnX : topologicalKrullDim X = n)
    {D : QDivisor X} (hD : D.IsQCartier)
    (hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ D.supp)
    {D' : QDivisor Y} (hp : D.IsPullback f hB D') :
    (-D').IsRelativelyBig f := by
  obtain ⟨Dc, Dc', hDc, hDB, -, hDc'q, hpc⟩ := hp.exists_cartierIndex hD
  have hdom : ∀ E : Divisor X, ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ E.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f
  refine ⟨D.cartierIndex hD, QDivisor.cartierIndex_pos hD, -Dc', by
      rw [map_neg, hDc'q, smul_neg]
      exact congrArg _ (Nat.cast_smul_eq_nsmul ℚ _ _),
    (hpc.isCartier hDc).neg, ?_⟩
  have hrange : closure (Set.range f.base) = Set.univ := by
    rw [(f.isClosedMap.isClosed_range).closure_eq]
    exact Set.range_eq_univ.mpr f.surjective
  refine ⟨n, n, hnY, ?_, 1 / 2, by norm_num, 0, fun m _ => ?_⟩
  · rw [← hnX, hrange]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph
  · rw [Nat.sub_self, pow_zero, mul_one]
    have hpm : Divisor.IsPullback f ((-m) • Dc) (hdom _) (m • -Dc') :=
      (show (-m) • Dc' = m • -Dc' by rw [neg_smul, smul_neg]) ▸ hpc.zsmul hDc (-m) (hdom _)
    haveI := (hDc.zsmul (-m)).isInvertibleModule_divisorialSheaf
    have hr : relativeGenericRank f (m • -Dc').divisorialSheaf = 1 := by
      unfold relativeGenericRank
      rw [Scheme.Modules.fiberRank_eq_of_iso ((Scheme.Modules.pushforward f).mapIso
        (Divisor.IsPullback.divisorialSheafIso (hBc := hDc.zsmul (-m)) hpm))]
      exact relativeGenericRank_pullback_eq_one sX hX f hY hf _
    rw [hr]
    norm_num

/-- **Vanishing on a log resolution of a klt pair** (KM, proof of Theorem 5.22). With
`B = B_f`, `R^j f_* 𝒪_Y(⌈B⌉) = 0` for `j > 0`. Writing `K_X = div ω`, `K_Y = div f^*ω` and
`C = K_Y - f^*(K_X + Δ)`, the boundary `Δ' = ⌈B⌉ - C = A_f + {-B_f}` has snc support and
coefficients in `[0, 1)`, and `⌈B⌉ - (K_Y + Δ') = -f^*(K_X + Δ)` is `f`-nef and `f`-big. -/
private theorem isZero_rightDerived_pushforward_divisorialSheaf_roundUp
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsProjectiveVariety k sX]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair sX n K Δ)
    {Y : Scheme.{0}} (f : Y ⟶ X) (hres : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hfp : IsProjectiveMorphism f) (hY : IsNormalVariety k (f ≫ sX)) {B : QDivisor Y}
    (hB : IsDiscrepancyPositivePart sX n K Δ f hY hres.isBirationalMorphism B)
    (j : ℕ) (hj : 0 < j) :
    haveI : IsLocallyNoetherian Y := hY.1.isLocallyNoetherian
    haveI : IsNormal Y := hY.2
    IsZero (((Scheme.Modules.pushforward f).rightDerived j).obj B.roundUp.divisorialSheaf) := by
  haveI : IsLocallyNoetherian Y := hY.1.isLocallyNoetherian
  haveI : IsNormal Y := hY.2
  have hbir := hres.isBirationalMorphism
  have hP : IsPairWith sX n K Δ := hklt.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsDominant f := hbir.isDominant
  haveI : IsProper f := hres.isProper
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX
    AlgebraicGeometry.IsProjectiveVariety.isProjective
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have hsm : IsSmoothScheme (f ≫ sX) := hres.isSmoothScheme
  have hcart := MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm
  -- `K = div ω` for a rational top form `ω`, and `K_Y = div f^*ω`
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hP.1 hP.2.1
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' hωK
  set KY := divisorOfForm (pullbackRationalPluriForms sX f ω) with hKY
  have hQ : (Divisor.toQDivisor (divisorOfForm ω) + Δ).IsQCartier := hP.2.2
  have hsupp := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier f hQ
  set P := QDivisor.pullback (f := f) (Divisor.toQDivisor (divisorOfForm ω) + Δ) hQ hsupp
    with hPdef
  set C : QDivisor Y := Divisor.toQDivisor KY - P with hCdef
  have hdisc : ∀ E : MMP.Mori.PrimeDivisor Y,
      IsDiscrepancy sX n (divisorOfForm ω) Δ ⟨Y, f, hY, hbir, E⟩ (C.coeff E) :=
    fun E => isDiscrepancy_coeff_divisorOfForm_sub_pullback hP.1 ω hω0 hP.2.1 Δ hQ f hY hbir E
  have hBC : ∀ E, B.coeff E = max (C.coeff E) 0 := fun E => by
    obtain ⟨a, ha, hBa⟩ := hB.2 E
    rw [hBa, ha.eq (hdisc E)]
  have hcrep : IsCrepantBoundary sX n (divisorOfForm ω) Δ f hY hbir (-C) := fun E => by
    simpa [DivisorWithCoeffs.coeff_neg] using hdisc E
  have hC1 : ∀ E, -1 < C.coeff E := fun E => by
    have := MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary hklt hY hbir hcrep E
    rw [DivisorWithCoeffs.coeff_neg] at this
    linarith
  -- the boundary `Δ' = ⌈B⌉ - C = A + {-B}` has coefficients in `[0, 1)`
  set Δ' : QDivisor Y := Divisor.toQDivisor B.roundUp - C with hΔ'def
  have hΔ'E : ∀ E, Δ' E = ⌈max (C.coeff E) 0⌉ - C.coeff E := fun E => by
    rw [← hBC E]
    rfl
  have hΔ'01 : ∀ E, 0 ≤ Δ' E ∧ Δ' E < 1 := fun E => by
    rw [hΔ'E]
    exact ceil_max_zero_sub_mem_Ico (hC1 E)
  haveI : LocallyOfFinitePresentation (f ≫ sX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  -- `Supp Δ' ⊆ Ex(f) ∪ f⁻¹(Supp Δ)`, which is snc
  have hΔ'snc : Δ'.IsSNC (f ≫ sX) := by
    refine isSNC_of_forall_genericPoint_mem hsm hres.isSNCSubset Δ' fun E hE => ?_
    exact genericPoint_mem_of_isDiscrepancy_ne_zero (hdisc E) fun h => hE (by rw [hΔ'E, h]; simp)
  -- `K_Y` is a canonical divisor of `Y`
  have hKYc : KY.IsCanonicalDivisor (f ≫ sX) n :=
    isCanonicalDivisor_divisorOfForm_pullback hP.1 hω0 hP.2.1 hY hbir hsm
  -- `⌈B⌉ - (K_Y + Δ') = -P`
  have hLM : Divisor.toQDivisor B.roundUp - (Divisor.toQDivisor KY + Δ') = -P := by
    rw [hΔ'def, hCdef]
    abel
  have hpb := QDivisor.isPullback_pullback (f := f) hQ hsupp
  have hnef : (Divisor.toQDivisor B.roundUp - (Divisor.toQDivisor KY + Δ')).IsRelativelyNef
      (f ≫ sX) f := hLM ▸ isRelativelyNef_neg_of_isPullback f hQ hsupp hpb
  have hbig : (Divisor.toQDivisor B.roundUp - (Divisor.toQDivisor KY + Δ')).IsRelativelyBig f := by
    rw [hLM]
    exact isRelativelyBig_neg_of_isPullback hP.1 f hY.1 hbir
      ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hbir).symm.trans
        hP.2.1.topologicalKrullDim_eq) hP.2.1.topologicalKrullDim_eq hQ hsupp hpb
  exact isZero_rightDerived_pushforward_divisorialSheaf_of_isRelativelyNef_of_isRelativelyBig
    (f ≫ sX) sX hsm f rfl hfp hKYc
    (fun E => (hΔ'01 E).1) hΔ'snc (fun E => (hΔ'01 E).2) (hcart _) hnef hbig j hj

end KltVanishing

end Proof_thm_mmp_projective_klt_log_resolution_vanishing

end

section

open CategoryTheory AlgebraicGeometry Stacks.Duality MMP.Mori
open scoped Stacks.SmallDerivedModel

namespace MMP.Duality

open Proof_thm_mmp_projective_klt_log_resolution_vanishing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Duality MMP.Mori

/-- **Klt pairs have rational singularities along projective log resolutions.** Let `X` be a
normal projective variety over an algebraically closed field `k` of characteristic zero, `K` a
canonical divisor of `X` of dimension `n`, and `Δ` an effective `ℚ`-divisor with `(X, Δ)` klt.
For a projective log resolution `f : Y ⟶ X` of `(X, Δ)`, the structural unit
`𝒪_X ⟶ Rf_* 𝒪_Y` (the map `𝒪_X ⟶ f_* 𝒪_Y` followed by `f_* ⟶ Rf_*`) is an isomorphism. -/
@[mmp "thm_mmp_projective_klt_log_resolution_vanishing"]
public theorem isIso_unit_of_isKltPair_of_isLogResolution {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{0}} (rX : X ⟶ Spec (.of k))
    [AlgebraicGeometry.IsProjectiveVariety k rX] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (hklt : IsKltPair rX n K Δ) (hΔ : Δ.IsEffective) (f : Y ⟶ X)
    (hlog : IsLogResolution rX (QDivisor.toRDivisor Δ) f) (hf : IsProjectiveMorphism f) :
    let u : (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (derivedPushforward f).obj
          ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
      (DerivedCategory.singleFunctorIsoCompQh X.Modules 0).hom.app _ ≫
        DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor X.Modules 0).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (HomotopyCategory.quotient _ _).map
            ((HomologicalComplex.singleMapHomologicalComplex
              (Scheme.Modules.pushforward f) _ 0).inv.app _)) ≫
        ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ))).app
            ((HomotopyCategory.singleFunctor Y.Modules 0).obj
              (SheafOfModules.unit Y.ringCatSheaf)) ≫
        (derivedPushforward f).map
          ((DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).inv.app _)
    IsIso u := by
  intro u
  /- `Y` is a smooth projective variety of dimension `n`, birational to `X`. -/
  obtain ⟨hYn, hdimY, -⟩ := hlog.toIsSmoothResolution.isNormalVariety hklt.1.1
  haveI : AlgebraicGeometry.IsVariety k (f ≫ rX) := hYn.1
  haveI : IsLocallyNoetherian Y := hYn.1.isLocallyNoetherian
  haveI : IsNormal Y := hYn.2
  haveI : IsProper f := hlog.isProper
  haveI : AlgebraicGeometry.IsProjectiveVariety k (f ≫ rX) :=
    ⟨hf.comp AlgebraicGeometry.IsProjectiveVariety.isProjective⟩
  haveI : LocallyOfFinitePresentation (f ≫ rX) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  haveI : Smooth (f ≫ rX) := (MMP.Mori.isSmoothScheme_iff _).mp hlog.isSmoothScheme
  have hdim : topologicalKrullDim X = n := hklt.1.2.1.topologicalKrullDim_eq
  haveI : SmoothOfRelativeDimension n (f ≫ rX) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety (f ≫ rX) n (hdimY.trans hdim)
  /- `B = B_f`, the positive part of the discrepancy, and `E = ⌈B⌉`. -/
  obtain ⟨⟨ΔY, hΔY, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hklt.1.isPair hklt.1.2.1 f
    hYn hlog.isBirationalMorphism
  have hB := hΔY.isDiscrepancyPositivePart hklt.1
  set B := (-ΔY).mapCoeffs (max · 0) (by simp)
  have hΔ0 : 0 ≤ Δ := DivisorWithCoeffs.isEffective_iff_nonneg.mp hΔ
  /- `R^q f_* 𝒪_Y(E) = 0` for `q > 0` and `𝒪_X ≅ f_* 𝒪_Y(E)`. -/
  have hvan : ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward f).rightDerived q).obj
      B.roundUp.divisorialSheaf) :=
    isZero_rightDerived_pushforward_divisorialSheaf_roundUp rX hklt f hlog hf hYn hB
  obtain ⟨h0, hφ⟩ := isIso_pushforward_structureSheafToDivisorialSheaf_roundUp rX hΔ0 f hYn
    hlog.isBirationalMorphism hB
  /- The comparison `(f_* 𝒪_Y(E))[0] ⟶ Rf_*(𝒪_Y(E)[0])` is an isomorphism. -/
  let c := singleComparison (Scheme.Modules.pushforward f) (derivedPushforward f)
    ((homotopyPushforward f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso Y.Modules (ComplexShape.up ℤ)))
  have hc : IsIso (c.app B.roundUp.divisorialSheaf) := by
    have : PreservesFiniteLimits (Scheme.Modules.pushforward f) :=
      have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.pushforward f) :=
        (Scheme.Modules.pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits
      inferInstance
    exact isIso_singleComparison_app _ _ _
      (fun M => Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward f)
        ((DerivedCategory.singleFunctor _ 0).obj M) 0)
      (Scheme.Modules.exists_quasiIso_isKInjective Y) _ hvan
  /- `u` followed by `Rf_*` of `𝒪_Y ⟶ 𝒪_Y(E)` is the isomorphism `α : 𝒪_X ⟶ Rf_* 𝒪_Y(E)`. -/
  let ι := Divisor.structureSheafToDivisorialSheaf h0
  have hu : u = (DerivedCategory.singleFunctor X.Modules 0).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        c.app (SheafOfModules.unit Y.ringCatSheaf) :=
    comp_eq_singleFunctor_map_comp_singleComparison_app (Scheme.Modules.pushforward f)
      (derivedPushforward f) _ _
  let a := (DerivedCategory.singleFunctor X.Modules 0).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map ι) ≫ c.app B.roundUp.divisorialSheaf
  have ha : u ≫ (derivedPushforward f).map ((DerivedCategory.singleFunctor Y.Modules 0).map ι) =
      a := by
    rw [hu]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (c.naturality ι).symm).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) ((DerivedCategory.singleFunctor X.Modules 0).map_comp _ _).symm)))
  haveI : IsIso a := IsIso.comp_isIso'
    ((DerivedCategory.singleFunctor X.Modules 0).mapIso (@asIso _ _ _ _ _ hφ)).isIso_hom hc
  have hsplit : IsSplitMono u :=
    .mk' ⟨(derivedPushforward f).map ((DerivedCategory.singleFunctor Y.Modules 0).map ι) ≫ inv a,
      by rw [reassoc_of% ha, IsIso.hom_inv_id]⟩
  /- The split-unit criterion. -/
  exact (MMP.Duality.isIso_unit_of_isSplitMono rX (f ≫ rX) f n hdim rfl hf
    hlog.isBirationalMorphism hsplit).1

end MMP.Duality

end
