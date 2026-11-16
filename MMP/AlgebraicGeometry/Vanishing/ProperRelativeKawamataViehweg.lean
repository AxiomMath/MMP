module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlops
public import MMP.AlgebraicGeometry.Singularities.Snc.Basic
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafQuasicoherent
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
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite
import MMP.AlgebraicGeometry.Vanishing.KltRationalSingularities
import MMP.AlgebraicGeometry.Singularities.LogCanonicalOneResolution
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition

/-!
# Relative Kawamata–Viehweg vanishing for proper morphisms

For a proper morphism `f : Y ⟶ Z` of varieties over an algebraically closed field of
characteristic zero, with `Y` smooth, and a `ℚ`-divisor `D` that is `f`-nef and `f`-big with
`⌈D⌉ - D` of simple normal crossing support, we prove `R^i f_* 𝒪_Y(K_Y + ⌈D⌉) = 0` for `i > 0`.

## Main results

* `MMP.Flips.isZero_rightDerived_divisorialSheaf_canonical_add_roundUp`
-/

open CategoryTheory AlgebraicGeometry Limits

namespace MMP.Flips

open MMP.Mori

/-- Snc support in the sense of Lazarsfeld gives snc in the sense of Kollár–Mori on a smooth
variety in characteristic zero. -/
private theorem isSNC_of_hasSNCSupport {k : Type} [Field k] [PerfectField k] {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsLocallyNoetherian Y] [CompactSpace Y]
    (hY : AlgebraicGeometry.IsVariety k sY) (hsm : IsSmoothScheme sY) {B : QDivisor Y}
    (hB : MMP.Intersection.HasSNCSupport sY B) : DivisorWithCoeffs.IsSNC sY B := by
  refine (DivisorWithCoeffs.isSNC_iff_of_support_eq
    (MMP.Intersection.support_reducedDivisorOf _)).mp ?_
  exact IsSNCDivisor.isSNC hY hsm
    ⟨hB.1, hB.2.1, fun x hx => hB.exists_isRegularSystemOfParameters x hx⟩

/-- The dimension of a module under scalars pulled back along a ring map depends only on that
ring map. -/
private theorem finrank_compHom_congr {K R M : Type*} [Field K] [CommRing R] [AddCommGroup M]
    [Module R M] {φ ψ : K →+* R} (h : φ = ψ) :
    @Module.finrank K M _ _ (Module.compHom M φ) =
      @Module.finrank K M _ _ (Module.compHom M ψ) := by
  subst h; rfl

/-- `genericFiberH0` is the dimension of `H⁰` of the generic fibre. -/
private theorem genericFiberH0_eq_finrank_cohomologyOverField {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IrreducibleSpace X] (F : X.Modules) :
    genericFiberH0 f F = Module.finrank (Y.residueField (f (genericPoint X)))
      (cohomologyOverField (Y.residueField (f (genericPoint X)))
        (f.fiberToSpecResidueField (f (genericPoint X)))
        ((Scheme.Modules.pullback (f.fiberι (f (genericPoint X)))).obj F) 0) := by
  rw [LinearEquiv.finrank_eq (cohomologyOverFieldZeroLinearIso _ _ _).toLinearEquiv]
  unfold genericFiberH0
  refine finrank_compHom_congr ?_
  simp only [scalarsToGlobalSections, Scheme.Hom.appLE, Scheme.Hom.appTop]
  congr 2
  exact (Category.comp_id _).symm.trans (congrArg _ (CategoryTheory.Functor.map_id _ _).symm)

/-- The sections of `F` on the generic fibre `Y_η` have dimension the rank of `f_* F` at `η`. -/
private theorem genericFiberH0_eq_relativeGenericRank {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    [IsIntegral Y] [QuasiCompact f] [QuasiSeparated f] (F : Y.Modules) [F.IsQuasicoherent] :
    genericFiberH0 f F = relativeGenericRank f F := by
  rw [genericFiberH0_eq_finrank_cohomologyOverField, relativeGenericRank_eq_finrank_fibre]

/-- Bigness on the generic fibre gives bigness by generic rank. -/
private theorem isRelativelyBig_of_isRelativelyBigOnGenericFiber {k : Type} [Field k]
    {Y Z : Scheme.{0}} [IrreducibleSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : Y ⟶ Z} {M : QDivisor Y}
    (h : IsRelativelyBigOnGenericFiber f k sY sZ M) : M.IsRelativelyBig f := by
  obtain ⟨hY, -, -, hf, a, b, ha, hb, m₀, hm₀, D, hD, hDc, c, hc, k₀, hk⟩ := h
  have : AlgebraicGeometry.IsVariety k sY := hY
  have : IsIntegral Y := hY.toIsIntegral
  have : IsProper f := hf
  have : QuasiSeparated f := IsSeparated.instQuasiSeparated f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  refine ⟨m₀, hm₀, D, hD, hDc, a, b, ha, hb, c / 2, by positivity, max k₀ 1, fun m hm => ?_⟩
  lift m to ℕ using by omega
  calc c / 2 * ((m : ℤ) : ℝ) ^ (a - b) < c * (m : ℝ) ^ (a - b) := by
        push_cast
        exact mul_lt_mul_of_pos_right (half_lt_self hc) (pow_pos (by norm_cast; omega) _)
    _ ≤ _ := hk m (by omega)
    _ ≤ _ := by exact_mod_cast (genericFiberH0_eq_relativeGenericRank f _).le

/-- The fractional part `⌈D⌉ - D` of a `ℚ`-divisor has coefficients in `[0, 1)`. -/
private theorem coeff_roundUp_sub_mem_Ico {Y : Scheme.{0}} (D : QDivisor Y)
    (E : MMP.Mori.PrimeDivisor Y) :
    (Divisor.toQDivisor D.roundUp - D).coeff E ∈ Set.Ico 0 1 := by
  simp only [DivisorWithCoeffs.coeff_sub, Divisor.coeff_toQDivisor,
    DivisorWithCoeffs.coeff_roundUp, Set.mem_Ico, sub_nonneg]
  exact ⟨Int.le_ceil _, by linarith [Int.ceil_lt_add_one (D.coeff E)]⟩

/-- Relative Kawamata–Viehweg vanishing for a proper smooth snc pair, with bigness on the
generic fibre and snc support in the sense of Lazarsfeld. -/
private theorem isZero_rightDerived_of_snc_pair {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y Z : Scheme.{0}} [IrreducibleSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] {sZ : Z ⟶ Spec (.of k)} {f : Y ⟶ Z}
    (hsm : IsSmoothScheme sY) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hB : B.IsEffective) (hsnc : MMP.Intersection.HasSNCSupport sY B)
    (hB1 : ∀ E : MMP.Mori.PrimeDivisor Y, B.coeff E < 1) {L : Divisor Y} (hL : L.IsCartier)
    (hnef : (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)).IsRelativelyNef sY f)
    (hbig : IsRelativelyBigOnGenericFiber f k sY sZ
      (Divisor.toQDivisor L - (Divisor.toQDivisor K + B)))
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj L.divisorialSheaf) := by
  obtain ⟨hY, hZ, hfZ, hf, -⟩ := id hbig
  have : AlgebraicGeometry.IsVariety k sY := hY
  have : AlgebraicGeometry.IsVariety k sZ := hZ
  have : IsIntegral Y := hY.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  exact
    isZero_rightDerived_pushforward_divisorialSheaf_of_isProper_of_isRelativelyNef_of_isRelativelyBig
    sY sZ hsm f hfZ hK hB (isSNC_of_hasSNCSupport hY hsm hsnc) hB1 hL hnef
    (isRelativelyBig_of_isRelativelyBigOnGenericFiber hbig) i hi

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
  {Y Z : Scheme.{0}} [IrreducibleSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of k)} [QuasiCompact sY] {sZ : Z ⟶ Spec (.of k)} {f : Y ⟶ Z}

/-- **Relative Kawamata–Viehweg vanishing.** Let `f : Y ⟶ Z` be a proper morphism of varieties
over an algebraically closed field `k` of characteristic zero, with `Y` smooth over `k`, let `K`
be a canonical divisor of `Y`, and let `D` be a `ℚ`-Cartier `ℚ`-divisor on `Y` which is `f`-nef
and `f`-big and such that `⌈D⌉ - D` has simple normal crossing support. Then
`R^i f_* 𝒪_Y(K + ⌈D⌉) = 0` for every `i > 0`. -/
@[mmp "thm_mmp_fa17_proper_relative_kawamata_viehweg"]
public theorem isZero_rightDerived_divisorialSheaf_canonical_add_roundUp
    (hsm : IsSmoothScheme sY) {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {D : QDivisor Y} (hnef : D.IsRelativelyNef sY f)
    (hbig : IsRelativelyBigOnGenericFiber f k sY sZ D)
    (hsnc : MMP.Intersection.HasSNCSupport sY (Divisor.toQDivisor D.roundUp - D))
    (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj
      (K + D.roundUp).divisorialSheaf) := by
  have hgap : Divisor.toQDivisor (K + D.roundUp) -
      (Divisor.toQDivisor K + (Divisor.toQDivisor D.roundUp - D)) = D := by
    rw [map_add]; abel
  exact isZero_rightDerived_of_snc_pair hsm hK
    (B := Divisor.toQDivisor D.roundUp - D)
    (fun E => (coeff_roundUp_sub_mem_Ico D E).1)
    hsnc
    (fun E => (coeff_roundUp_sub_mem_Ico D E).2)
    (MMP.Threefold.Resolution.isCartier_of_isSmoothScheme hsm _)
    (by rwa [hgap]) (by rwa [hgap]) i hi

end MMP.Flips
