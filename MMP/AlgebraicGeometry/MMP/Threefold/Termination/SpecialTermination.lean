module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumAvoidsFlip
import MMP.AlgebraicGeometry.MMP.Termination.StrataEventuallyBirational
import MMP.AlgebraicGeometry.MMP.Termination.StratumDivisorsStabilize
import MMP.AlgebraicGeometry.MMP.Surface.ContractionChainBound
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.SecondLegCollapse
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HgroupAlternatingCech
import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.FormsTopGeneratorFibres
import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
import StacksFrontier.AlgebraicGeometry.LocalCohomology.ClosedImmersionCoherence
import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Variety
import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.PreimageDimension
import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange
import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.FibreHilbertLocus
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
import StacksFrontier.AlgebraicGeometry.InvertibleOnClosedCover.Basic
import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardDegree
import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumUniversalOver
import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.RestrictOpen
import StacksFrontier.AlgebraicGeometry.RelativeProjTwist.Basic
import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.LocalOnBase
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
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Basic
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Intersection.Surface.Symmetry
import MMP.AlgebraicGeometry.MMP.Flip.ContractedCurveNormalization
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
import MMP.AlgebraicGeometry.MMP.Abundance.SubkltSurfacePluriformFinite
import MMP.AlgebraicGeometry.Resolution.CommonLogResolution
import MMP.AlgebraicGeometry.Singularities.DltLogTerminal
import MMP.AlgebraicGeometry.Singularities.FiniteLowDiscrepancyKlt
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.LowDiscrepancyJunction
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Resolution.ZariskiSequence
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.Divisor.Negativity.CodimTwoCentres
import MMP.AlgebraicGeometry.Singularities.LogCanonicalOneResolution
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.SncStrata.ZeroPlaceExtraction
import MMP.AlgebraicGeometry.Singularities.CrepantBoundaryPushforward
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.Adjunction.EffectiveResidueAdjunction
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.Adjunction.SmoothDivisorResidueRestriction
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.PoincareResidueSmoothDivisor
import MMP.AlgebraicGeometry.Singularities.BlowupDiscrepancy
import MMP.RingTheory.RegularLocalRing.QuotientRegularIff
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalFlips
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange

/-!
# Special termination for projective dlt threefolds

Along a sequence of `(K + B)`-flips of `ℚ`-factorial projective dlt threefolds, the components of
`⌊Bᵢ⌋` are eventually disjoint from the flipping and flipped loci. The proof tracks the boundary
strata through the flips by dimension, using that a flip is an isomorphism over the biregular
locus of the flipping contraction.

## Main results

* `MMP.Fourfold.exists_forall_ge_disjoint_exceptionalSet_of_isFlipOf`: special termination.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fold06.ThmFourfoldProjectiveDltThreefoldSpecialTermination

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Fourfold

/-! ### Flips of dlt pairs -/

section DltFlip

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X X' Z : Scheme.{0}}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
  {f : X ⟶ Z} {fp : X' ⟶ Z} {n : ℕ} {K : Divisor X} {B : QDivisor X}

omit [IsAlgClosed k] [CharZero k] [IsIntegral X] [IsIntegral X'] in
/-- A flip in the sense of `MMP.Fourfold.IsFlipOf` is a Kollár–Mori flip. -/
private theorem isFlip_of_isFlipOf (hK : K.IsCanonicalDivisor sX n)
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp) :
    MMP.Mori.IsFlip sX sZ sX' K B f fp := by
  have hc := hflip.isContraction
  have hs := hflip.isSmallMorphism
  have hs' := hflip.isSmallMorphism_flip
  have htr : flipTransform f fp (Divisor.toQDivisor K + B) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B := by
    rw [map_add, flipTransform_toQDivisor]
  exact
    { isFlippingContraction :=
        { isNormalVariety_source := hc.isNormalVariety_source
          isNormalVariety_target := hc.isNormalVariety_target
          comp_eq := hc.comp_eq
          isCanonicalDivisor := ⟨n, hK⟩
          isQCartier := hflip.isQCartier
          isProper := hs.isProper
          isBirationalMorphism := hs.isBirationalMorphism
          two_le_codimension := hs.two_le_codimension
          hasRelativelyAmpleMultiple := hflip.hasRelativelyAmpleMultiple }
      isNormalVariety := hs'.isNormalVariety_source
      comp_eq := hs'.comp_eq
      isProper := hs'.isProper
      isBirationalMorphism := hs'.isBirationalMorphism
      isQCartier := htr ▸ hflip.isQCartier_flip
      hasRelativelyAmpleMultiple := htr ▸ hflip.hasRelativelyAmpleMultiple_flip
      two_le_codimension := hs'.two_le_codimension }

/-- Flips preserve dlt pairs. -/
private theorem isDltPair_flipTransform (hK : K.IsCanonicalDivisor sX n)
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    (hB : MMP.Intersection.IsDltPair sX B) :
    MMP.Intersection.IsDltPair sX' (flipTransform f fp B) := by
  have hIF := isFlip_of_isFlipOf hK hflip
  have hK' := hIF.isCanonicalDivisor_flipTransform hK
  exact (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX' hK' _).mpr
    (hIF.isDltPair ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hK B).mp hB))

end DltFlip

/-! ### `IsFlipOf` as a flip in the sense of *Flips and abundance* -/

section FlipOfAsFlip

open MMP

variable {k : Type} [Field k]

/-- If `L = m D` with `m ≠ 0`, then `D = m⁻¹ L` as `ℝ`-divisors. -/
private theorem toRDivisor_eq_inv_smul {X : Scheme.{0}} {D : QDivisor X} {m : ℤ} (hm : m ≠ 0)
    {L : Divisor X} (hL : Divisor.toQDivisor L = m • D) :
    QDivisor.toRDivisor D = ((m : ℝ)⁻¹) • Divisor.toRDivisor L := by
  ext E
  have h := congrArg (fun D : QDivisor X => D.coeff E) hL
  simp only [Divisor.coeff_toQDivisor] at h
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  rw [mul_comm]
  exact_mod_cast h.symm

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : QDivisor X} (h : D.IsQCartier) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
    rw [Fin.sum_univ_one]; exact toRDivisor_eq_inv_smul hm hL⟩

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-ample as an `ℝ`-divisor. -/
private theorem isRelativelyAmple_toRDivisor {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} [QuasiCompact f] {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) :
    MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have := hL.isInvertibleModule_divisorialSheaf
  refine ⟨1, fun _ => ((m : ℤ) : ℝ)⁻¹, fun _ => L, le_rfl, fun _ => by positivity,
    fun _ => ⟨hL, fun U hU =>
      (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
        inferInstance hamp).2 U hU⟩, ?_⟩
  rw [Fin.sum_univ_one]
  exact toRDivisor_eq_inv_smul (by exact_mod_cast hm.ne') hLD

/-- The terminal morphism of a separated `k`-scheme is separated. -/
private theorem isSeparated_toTerminal {X : Scheme.{0}} {s : X ⟶ Spec (.of k)}
    [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  have : (X ↘ ⊤_ Scheme) = s ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
  rw [this]
  infer_instance

/-- A small morphism with `𝒪_Z ≅ f_* 𝒪_X` is a small birational contraction. -/
private theorem isSmall_of_isSmallMorphism {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    (happ : ∀ U : Z.Opens, IsIso (f.app U)) : MMP.Flips.IsSmall k sZ sX f := by
  have := hf.isNormalVariety_target.2
  have := hf.isProper
  have := hf.isNormalVariety_source.1
  have := hf.isNormalVariety_target.1
  have hbc : MMP.Flips.IsBirationalContraction k sZ sX f :=
    { isVariety_target := hf.isNormalVariety_target.1
      isVariety_source := hf.isNormalVariety_source.1
      comp_eq := hf.comp_eq
      isProper := hf.isProper
      isIso_app := happ
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX
        hf.isBirationalMorphism).symm }
  refine (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
  have h := hf.two_le_codimension
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at h ⊢
  intro x hx
  refine h x fun hx' => hx ⟨f ⁻¹ᵁ biregularLocus f, by simpa [exceptionalSet] using hx', ?_⟩
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  rw [← morphismRestrict_ι]
  infer_instance

section Transforms

variable {X Y Z : Scheme.{0}}

/-- Extending a composite `φ₂ ∘ φ₁` of partial maps on prime divisors linearly is composing the
linear extensions. -/
private theorem mapPrimeDivisors_bind {R : Type*} [AddCommMonoid R]
    (φ₁ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y))
    (φ₂ : Mori.PrimeDivisor Y → Option (Mori.PrimeDivisor Z)) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors (fun P => (φ₁ P).bind φ₂) D =
      DivisorWithCoeffs.mapPrimeDivisors φ₂ (DivisorWithCoeffs.mapPrimeDivisors φ₁ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ₁ E with
    | none => simp
    | some E' => simp [DivisorWithCoeffs.mapPrimeDivisors_single]

/-- A representative `ψ` of a rational map `φ` over `f` and `g` satisfies `ψ ≫ g = f`. -/
private theorem hom_comp_eq_of_isOver [IsReduced X] [IsSeparated (Z ↘ ⊤_ Scheme)]
    {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y} (hφ : Flips.RationalMap.IsOver f g φ)
    (ψ : X.PartialMap Y) (hψ : ψ.toRationalMap = φ) : ψ.hom ≫ g = ψ.domain.ι ≫ f := by
  have h1 : (ψ.compHom g).toRationalMap = f.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hψ]
    exact hφ
  exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)

private theorem hom_apply_eq_of_comp_eq {ψ : X.PartialMap Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : ψ.hom ≫ g = ψ.domain.ι ≫ f) (x : ψ.domain) : g (ψ.hom x) = f x.1 :=
  congrArg (fun k : ψ.domain.toScheme ⟶ Z => k x) h

/-- Two morphisms with the same composite with `g`, both landing over the biregular locus of `g`,
are equal. -/
private theorem eq_of_comp_eq_of_mem_biregularLocus {W : Scheme.{0}} (g : Y ⟶ Z) {a b : W ⟶ Y}
    {h : W ⟶ Z} (ha' : a ≫ g = h) (hb' : b ≫ g = h) (hh : ∀ w, h w ∈ biregularLocus g) :
    a = b := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hab : a ≫ g = b ≫ g := ha'.trans hb'.symm
  have ha : ∀ w, g (a w) ∈ biregularLocus g := fun w => by
    rw [← Scheme.Hom.comp_apply, ha']; exact hh w
  have hb : ∀ w, g (b w) ∈ biregularLocus g := fun w => by
    rw [← Scheme.Hom.comp_apply, hb']; exact hh w
  have hra : Set.range a ⊆ Set.range (g ⁻¹ᵁ biregularLocus g).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ha w
  have hrb : Set.range b ⊆ Set.range (g ⁻¹ᵁ biregularLocus g).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hb w
  rw [← IsOpenImmersion.lift_fac (g ⁻¹ᵁ biregularLocus g).ι a hra,
    ← IsOpenImmersion.lift_fac (g ⁻¹ᵁ biregularLocus g).ι b hrb]
  congr 1
  rw [← cancel_mono (g ∣_ biregularLocus g), ← cancel_mono (biregularLocus g).ι]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, hab]

/-- The partial map `g⁻¹ ∘ f`, defined on `f⁻¹(V_g)` for the biregular locus `V_g` of `g`. -/
private noncomputable def partialMapOverBiregularLocus [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty) :
    X.PartialMap Y where
  domain := f ⁻¹ᵁ biregularLocus g
  dense_domain := (f ⁻¹ᵁ biregularLocus g).2.dense hne
  hom := haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
    (f ∣_ biregularLocus g) ≫ inv (g ∣_ biregularLocus g) ≫ (g ⁻¹ᵁ biregularLocus g).ι

private theorem partialMapOverBiregularLocus_hom_comp [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty) :
    (partialMapOverBiregularLocus f g hne).hom ≫ g =
      (partialMapOverBiregularLocus f g hne).domain.ι ≫ f := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  change ((f ∣_ biregularLocus g) ≫ inv (g ∣_ biregularLocus g) ≫
    (g ⁻¹ᵁ biregularLocus g).ι) ≫ g = (f ⁻¹ᵁ biregularLocus g).ι ≫ f
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    morphismRestrict_ι]

private theorem partialMapOverBiregularLocus_hom_mem [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty)
    (x : (partialMapOverBiregularLocus f g hne).domain) :
    (partialMapOverBiregularLocus f g hne).hom x ∈ g ⁻¹ᵁ biregularLocus g := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  exact (inv (g ∣_ biregularLocus g) ((f ∣_ biregularLocus g) x)).2

end Transforms

/-- The birational map `(f⁺)⁻¹ ∘ f`, composed of partial isomorphisms representing the birational
morphisms `f` and `f⁺`, is a modification of `f` into `f⁺`. -/
private theorem exists_isModificationOf {Xm Xp Z : Scheme.{0}} [IsReduced Xm] [IsReduced Xp]
    {sZ : Z ⟶ Spec (.of k)} [IsSeparated sZ] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hm : IsBirationalMorphism fm) (hp : IsBirationalMorphism fp) :
    ∃ φ : Xm.RationalMap Xp, MMP.Flips.IsModificationOf fm fp φ := by
  obtain ⟨em, hm⟩ := hm
  obtain ⟨ep, hp⟩ := hp
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em fm (𝟙 Z) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 Z) hp
  simp only [Category.comp_id] at h1 h2
  set e := em.trans ep.symm
  have H : e.IsOver fm fp := h1.trans h2.symm
  refine ⟨e.toRationalMap, ⟨e, rfl⟩, ?_⟩
  rw [MMP.Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change Xm.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
    Xm.homOfLE (le_top : e.source ≤ ⊤) ≫ Xm.topIso.hom ≫ fm
  rw [Category.assoc, H]
  simp

/-- For a small `f`, the birational transform of divisors under a modification `φ` of `f` into
`f⁺` is the strict transform `(f⁺)⁻¹_* f_*`. -/
private theorem transformDivisor_eq_flipTransform_of_isModificationOf {Xm Xp Z : Scheme.{0}}
    [IsIntegral Xm] {sZ : Z ⟶ Spec (.of k)} {sXp : Xp ⟶ Spec (.of k)} [IsSeparated sZ]
    [IsSeparated sXp] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hm2 : 2 ≤ closedsCodimension (exceptionalSet fm))
    (hp2 : 2 ≤ closedsCodimension (exceptionalSet fp))
    {φ : Xm.RationalMap Xp} (hφ : MMP.Flips.IsModificationOf fm fp φ)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) :
    Mori.RationalMap.transformDivisor φ D = flipTransform fm fp D := by
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  have : IsSeparated (Xp ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sXp)
  have hpt : ∀ P : Mori.PrimeDivisor Xm, Mori.RationalMap.transformPrimeDivisor φ P =
      (Mori.RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap P).bind
        (inverseTransformPrimeDivisor fp) := by
    intro P
    have hcoh : Order.coheight (fm P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fm
        (MMP.Fourfold.Oai4C1.map_genericPoint_mem_biregularLocus hm2 P),
        P.coheight_genericPoint]
    set Q : Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
    have hQ : fm P.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm P Q).mpr hQ,
      Option.bind_some]
    by_cases hV : Q.genericPoint ∈ biregularLocus fp
    · have hPU : P.genericPoint ∈ fm ⁻¹ᵁ biregularLocus fp :=
        show fm P.genericPoint ∈ biregularLocus fp from hQ ▸ hV
      set g' := partialMapOverBiregularLocus fm fp ⟨_, hPU⟩
      have hg' : g'.toRationalMap = φ := by
        obtain ⟨ψ, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective φ
        have hψ := hom_comp_eq_of_isOver hφ.2 ψ rfl
        have hg := partialMapOverBiregularLocus_hom_comp fm fp ⟨_, hPU⟩
        rw [Scheme.PartialMap.toRationalMap_eq_iff]
        refine ⟨g'.domain ⊓ ψ.domain,
          g'.dense_domain.inter_of_isOpen_left ψ.dense_domain g'.domain.2, inf_le_left,
          inf_le_right, ?_⟩
        have key : ∀ (U : Xm.Opens) (hWU : g'.domain ⊓ ψ.domain ≤ U) (c : U.toScheme ⟶ Xp),
            c ≫ fp = U.ι ≫ fm → (Xm.homOfLE hWU ≫ c) ≫ fp = (g'.domain ⊓ ψ.domain).ι ≫ fm :=
          fun U hWU c hc => by rw [Category.assoc, hc, Scheme.homOfLE_ι_assoc]
        refine eq_of_comp_eq_of_mem_biregularLocus fp (key _ inf_le_left _ hg)
          (key _ inf_le_right _ hψ) fun w => w.2.1
      set y := g'.hom ⟨P.genericPoint, hPU⟩
      have hyQ : fp y = Q.genericPoint :=
        (hom_apply_eq_of_comp_eq (partialMapOverBiregularLocus_hom_comp fm fp ⟨_, hPU⟩)
          ⟨P.genericPoint, hPU⟩).trans hQ
      have hyV : y ∈ fp ⁻¹ᵁ biregularLocus fp := partialMapOverBiregularLocus_hom_mem _ _ _ _
      have hcy : Order.coheight y = 1 := by
        rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hyV, hyQ,
          Q.coheight_genericPoint]
      set P' : Mori.PrimeDivisor Xp := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcy
      have hP' : y = P'.genericPoint :=
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy).symm
      rw [MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        (E := P') (hP' ▸ hyQ) (hP' ▸ hyV)]
      exact Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hPU hP'.symm
    · have hnone : inverseTransformPrimeDivisor fp Q = none := by
        rw [inverseTransformPrimeDivisor_eq_none_iff]
        rintro ⟨⟨z, hzQ, hzV⟩, -⟩
        have hz : Q.genericPoint ⤳ z := by
          have : z ∈ Q.support := hzQ
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
          exact specializes_iff_mem_closure.mpr this
        exact hV (hz.mem_open (biregularLocus fp).2 hzV)
      rw [hnone, Mori.RationalMap.transformPrimeDivisor_eq_none_iff]
      rintro ⟨hdef, E, hE⟩
      have hsome : Mori.RationalMap.transformPrimeDivisor φ P = some E :=
        Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr ⟨hdef, hE⟩
      obtain ⟨ψ, hPψ, hψ⟩ := Mori.RationalMap.definedAt_iff.mp hdef
      have hηE := Flips.genericPoint_eq_of_transformPrimeDivisor_eq_some hsome ψ hψ hPψ
      have h1 : fp E.genericPoint = Q.genericPoint := by
        rw [hηE]
        exact (hom_apply_eq_of_comp_eq (hom_comp_eq_of_isOver hφ.2 ψ hψ)
          ⟨P.genericPoint, hPψ⟩).trans hQ
      exact hV (h1 ▸ MMP.Fourfold.Oai4C1.map_genericPoint_mem_biregularLocus
        hp2 E)
  change DivisorWithCoeffs.mapPrimeDivisors _ D = inverseTransformDivisor fp
    (Mori.RationalMap.transformDivisor (X := Xm) fm.toRationalMap D)
  rw [funext hpt]
  exact mapPrimeDivisors_bind _ _ D

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {X Y : Scheme.{0}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y))
    (f : R →+ S) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with changing coefficients. -/
private theorem flipTransform_mapCoeffsAddMonoidHom {X Y X' : Scheme.{0}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (fm : X ⟶ Y) (fp : X' ⟶ Y) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    flipTransform fm fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (flipTransform fm fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- **A flip is an isomorphism over the biregular locus of the flipping contraction**:
`V_f ⊆ V_{f⁺}` for a `D`-flip `f⁺` of `f` (`MMP.Fourfold.IsFlipOf`). -/
private theorem biregularLocus_le_of_isFlipOf {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {D : QDivisor X} {f : X ⟶ Z}
    {fp : X' ⟶ Z} (h : IsFlipOf sX sZ sX' D f fp) : biregularLocus f ≤ biregularLocus fp := by
  have hc := h.isContraction
  have hs := h.isSmallMorphism
  have hsp := h.isSmallMorphism_flip
  haveI := hs.isProper
  haveI := hsp.isProper
  haveI : IsSeparated sZ := hc.isNormalVariety_target.1.toIsSeparated
  haveI : IsSeparated sX' := hsp.isNormalVariety_source.1.toIsSeparated
  obtain ⟨g, hg⟩ := exists_isModificationOf (sZ := sZ) hs.isBirationalMorphism
    hsp.isBirationalMorphism
  have htr : Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (flipTransform f fp D) := by
    rw [transformDivisor_eq_flipTransform_of_isModificationOf (sZ := sZ) (sXp := sX')
      hs.two_le_codimension hsp.two_le_codimension hg]
    simp only [QDivisor.toRDivisor, flipTransform_mapCoeffsAddMonoidHom]
  have happ := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sX' sZ
    hsp.isNormalVariety_source.1 hc.isNormalVariety_target fp hsp.isBirationalMorphism).1
  have hF : MMP.Flips.IsFlip k sX sZ sX' (QDivisor.toRDivisor D) f fp g :=
    { isNormalVariety_source := hc.isNormalVariety_source
      isNormalVariety_target := hc.isNormalVariety_target
      isNormalVariety_flip := hsp.isNormalVariety_source
      isContraction :=
        { isVariety_target := hc.isNormalVariety_target.1
          isVariety_source := hc.isNormalVariety_source.1
          comp_eq := hc.comp_eq
          isProper := inferInstance
          isIso_app := hc.isIso_app }
      isCartierCombination := isCartierCombination_toRDivisor h.isQCartier
      isRelativelyAntiAmple := by
        rw [MMP.Flips.IsRelativelyAntiAmple, ← map_neg]
        exact isRelativelyAmple_toRDivisor h.hasRelativelyAmpleMultiple
      isProper := inferInstance
      isModificationOf := hg
      isMorphismInCodimOne :=
        MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hc.isNormalVariety_source f fp g hg.2
      isSmall := isSmall_of_isSmallMorphism hsp happ
      isCartierCombination_transform := by
        rw [htr]; exact isCartierCombination_toRDivisor h.isQCartier_flip
      isRelativelyAmple_transform := by
        rw [htr]; exact isRelativelyAmple_toRDivisor h.hasRelativelyAmpleMultiple_flip
      isSmall_source := isSmall_of_isSmallMorphism hs hc.isIso_app }
  haveI : IsIso (fp ∣_ biregularLocus f) :=
    hF.isIso_morphismRestrict_of_disjoint_image_exceptionalSet h.isQCartier _ (by
      rw [Set.disjoint_left]
      rintro _ hzV ⟨y, hy, rfl⟩
      have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
      refine hy ⟨f ⁻¹ᵁ biregularLocus f, hzV, ?_⟩
      rw [← morphismRestrict_ι]
      infer_instance)
  exact le_biregularLocus this

end FlipOfAsFlip

section BiregularLocus

variable {k : Type} [Field k]

/-- A morphism is injective over its biregular locus. -/
private theorem injOn_preimage_biregularLocus {Y Z : Scheme.{0}} (g : Y ⟶ Z) :
    Set.InjOn g.base (g ⁻¹ᵁ biregularLocus g : Set Y) := by
  have := isBiregular_biregularLocus g
  unfold IsBiregular at this
  intro a ha b hb hab
  have hinj : Function.Injective (g ∣_ biregularLocus g).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (g ∣_ biregularLocus g)))).injective
  let a' : (g ⁻¹ᵁ biregularLocus g).toScheme := ⟨a, ha⟩
  let b' : (g ⁻¹ᵁ biregularLocus g).toScheme := ⟨b, hb⟩
  have h2 : (g ∣_ biregularLocus g).base a' = (g ∣_ biregularLocus g).base b' :=
    Subtype.ext (by rwa [morphismRestrict_base_coe, morphismRestrict_base_coe])
  exact congrArg Subtype.val (hinj h2)

/-- Every point of the biregular locus of `g` is the image of a point of `g⁻¹(V_g)`. -/
private theorem exists_apply_eq_of_mem_biregularLocus {Y Z : Scheme.{0}} (g : Y ⟶ Z) {z : Z}
    (hz : z ∈ biregularLocus g) : ∃ y : Y, g.base y = z := by
  have := isBiregular_biregularLocus g
  unfold IsBiregular at this
  have hsurj : Function.Surjective (g ∣_ biregularLocus g).base :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (g ∣_ biregularLocus g)))).surjective
  obtain ⟨y, hy⟩ := hsurj ⟨z, hz⟩
  refine ⟨y.1, ?_⟩
  have := congrArg Subtype.val hy
  rwa [morphismRestrict_base_coe] at this

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- The coefficients of `(f⁺)⁻¹_* f_* D` over the biregular loci: if `f(η_P) = f⁺(η_{P'})` lies
over the biregular loci of `f` and `f⁺`, the coefficient of `P'` is that of `P`. -/
private theorem flipTransform_apply_of_mem [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hZ : IsNormalVariety k sZ)
    (hX : IsNormalVariety k (f ≫ sZ)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hV : f.base P.genericPoint ∈ biregularLocus f)
    (hV' : fp.base P'.genericPoint ∈ biregularLocus fp)
    (hPP : f.base P.genericPoint = fp.base P'.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hco : Order.coheight (fp.base P'.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hV',
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = fp.base P'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  have huniq : ∀ Q₁ : MMP.Mori.PrimeDivisor Z, inverseTransformPrimeDivisor fp Q₁ = some P' →
      Q₁ = Q := by
    intro Q₁ hQ₁
    obtain ⟨h1, -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ₁
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h1.symm.trans hQ.symm)
  have h1 : inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := X)
      f.toRationalMap D) P' = MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D Q :=
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
        hQ.symm hV') huniq _
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hX hf Q
  change inverseTransformDivisor fp (MMP.Mori.RationalMap.transformDivisor (X := X)
    f.toRationalMap D) P' = _
  rw [h1, htr]
  have hE : f.base E.genericPoint = f.base P.genericPoint := hEQ.trans (hQ.trans hPP.symm)
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (injOn_preimage_biregularLocus f (show f.base E.genericPoint ∈ biregularLocus f from
      hE ▸ hV) hV hE)]

/-- Over a point `z` of `Z` of coheight at most one, a small birational morphism is biregular. -/
private theorem mem_biregularLocus_of_isSmallMorphism {f : X ⟶ Z} (hs : IsSmallMorphism sX sZ f)
    {z : Z} (hz : Order.coheight z ≤ 1) : z ∈ biregularLocus f := by
  haveI : IsProper f := hs.isProper
  haveI : IsIntegral X := hs.isNormalVariety_source.1.toIsIntegral
  haveI : IsIntegral Z := hs.isNormalVariety_target.1.toIsIntegral
  haveI : IsNormal Z := hs.isNormalVariety_target.2
  haveI : LocallyOfFiniteType sZ := hs.isNormalVariety_target.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsDominant f := hs.isBirationalMorphism.isDominant
  exact MMP.Positivity.mem_biregularLocus_of_coheight_le_one f
    hs.isBirationalMorphism.functionFieldMap_bijective hs.two_le_codimension hz

/-- For a prime divisor `P` of `X` and small birational morphisms `f : X ⟶ Z`, `f⁺ : X⁺ ⟶ Z`,
there is a prime divisor `P'` of `X⁺` over the same point of `Z`. -/
private theorem exists_primeDivisor_map_genericPoint_eq (hs : IsSmallMorphism sX sZ f)
    (hs' : IsSmallMorphism sX' sZ fp) (P : MMP.Mori.PrimeDivisor X) :
    ∃ P' : MMP.Mori.PrimeDivisor X', fp.base P'.genericPoint = f.base P.genericPoint := by
  have hV := MMP.Fourfold.Oai4C1.map_genericPoint_mem_biregularLocus hs.two_le_codimension P
  have hco : Order.coheight (f.base P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f hV, P.coheight_genericPoint]
  have hV' := mem_biregularLocus_of_isSmallMorphism hs' hco.le
  obtain ⟨y, hy⟩ := exists_apply_eq_of_mem_biregularLocus fp hV'
  have hy' : fp.base y ∈ biregularLocus fp := hy ▸ hV'
  have hcy : Order.coheight y = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hy', hy, hco]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcy,
    (congrArg fp.base (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy)).trans hy⟩

/-- The strict transform back and forth along small birational morphisms is the identity. -/
private theorem flipTransform_flipTransform [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    (hZ : IsNormalVariety k sZ) (hs : IsSmallMorphism sX sZ f)
    (hs' : IsSmallMorphism sX' sZ fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform fp f (flipTransform f fp D) = D := by
  haveI : IsProper f := hs.isProper
  haveI : IsProper fp := hs'.isProper
  have hXv : IsNormalVariety k (f ≫ sZ) := hs.comp_eq ▸ hs.isNormalVariety_source
  have hX'v : IsNormalVariety k (fp ≫ sZ) := hs'.comp_eq ▸ hs'.isNormalVariety_source
  ext P
  obtain ⟨P', hP'⟩ := exists_primeDivisor_map_genericPoint_eq hs hs' P
  have hV := MMP.Fourfold.Oai4C1.map_genericPoint_mem_biregularLocus hs.two_le_codimension P
  have hV' := MMP.Fourfold.Oai4C1.map_genericPoint_mem_biregularLocus hs'.two_le_codimension P'
  change flipTransform fp f (flipTransform f fp D) P = D P
  rw [flipTransform_apply_of_mem (k := k) hZ hX'v hs'.isBirationalMorphism hV' hV hP',
    flipTransform_apply_of_mem (k := k) hZ hXv hs.isBirationalMorphism hV hV' hP'.symm]

/-- A small proper birational morphism onto a normal variety is surjective. -/
private theorem surjective_of_isSmallMorphism {f : X ⟶ Z} (hs : IsSmallMorphism sX sZ f) :
    Function.Surjective f.base := by
  haveI : IsProper f := hs.isProper
  haveI : IsDominant f := hs.isBirationalMorphism.isDominant
  have hcl : IsClosed (Set.range f.base) := f.isClosedMap.isClosed_range
  have hd : Dense (Set.range f.base) := f.denseRange
  rw [← Set.range_eq_univ, ← hcl.closure_eq, hd.closure_eq]

/-- **The flip read backwards.** If `f⁺` is a `D`-flip of `f`, then `f` is a `(-D⁺)`-flip of
`f⁺`, where `D⁺ = (f⁺)⁻¹_* f_* D`. -/
private theorem IsFlipOf.symm [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] {D : QDivisor X}
    (h : IsFlipOf sX sZ sX' D f fp) :
    IsFlipOf sX' sZ sX (-flipTransform f fp D) fp f := by
  have hc := h.isContraction
  have hs := h.isSmallMorphism
  have hsp := h.isSmallMorphism_flip
  haveI : IsProper fp := hsp.isProper
  have hround : flipTransform fp f (-flipTransform f fp D) = -D := by
    rw [map_neg, flipTransform_flipTransform hc.isNormalVariety_target hs hsp]
  have happ := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sX' sZ
    hsp.isNormalVariety_source.1 hc.isNormalVariety_target fp hsp.isBirationalMorphism).1
  exact
    { isQCartier := Oai4C1.isQCartier_neg h.isQCartier_flip
      isContraction :=
        { isNormalVariety_source := hsp.isNormalVariety_source
          isNormalVariety_target := hsp.isNormalVariety_target
          comp_eq := hsp.comp_eq
          isProjectiveMorphism := h.isProjectiveMorphism_flip
          surjective := surjective_of_isSmallMorphism hsp
          isIso_app := happ }
      isSmallMorphism := hsp
      hasRelativelyAmpleMultiple := by rw [neg_neg]; exact h.hasRelativelyAmpleMultiple_flip
      isSmallMorphism_flip := hs
      isProjectiveMorphism_flip := hc.isProjectiveMorphism
      isQCartier_flip := by rw [hround]; exact Oai4C1.isQCartier_neg h.isQCartier
      hasRelativelyAmpleMultiple_flip := by rw [hround]; exact h.hasRelativelyAmpleMultiple }

/-- **A flip and its flipping contraction have the same biregular locus.** -/
private theorem biregularLocus_eq_of_isFlipOf [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {D : QDivisor X} (h : IsFlipOf sX sZ sX' D f fp) : biregularLocus f = biregularLocus fp :=
  le_antisymm (biregularLocus_le_of_isFlipOf h) (biregularLocus_le_of_isFlipOf (IsFlipOf.symm h))

end BiregularLocus

/-! ### Boundary strata -/

section Strata

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}

/-- A boundary stratum is closed and irreducible. -/
private theorem isClosed_and_isIrreducible_of_isDltStratum {T : Set X}
    (hT : IsDltStratum sX B T) : IsClosed T ∧ IsIrreducible T := by
  obtain ⟨-, J, -, -, -, hmax⟩ := hT
  have hC : IsClosed (⋂ P ∈ J, (P.support : Set X)) :=
    isClosed_biInter fun P _ => TopologicalSpace.Closeds.isClosed P.idealSheaf.support
  have hcl : closure T ⊆ T := hmax.2 ⟨hmax.1.1.closure, closure_minimal hmax.1.2 hC⟩ subset_closure
  exact ⟨closure_subset_iff_isClosed.mp hcl, hmax.1.1⟩

/-- A boundary stratum is the closure of a point. -/
private theorem exists_closure_singleton_eq_of_isDltStratum {T : Set X}
    (hT : IsDltStratum sX B T) : ∃ η : X, closure {η} = T := by
  obtain ⟨hc, hi⟩ := isClosed_and_isIrreducible_of_isDltStratum hT
  obtain ⟨η, hgen⟩ : ∃ η, IsGenericPoint η T :=
    ⟨_, by simpa [hc.closure_eq] using hi.isGenericPoint_genericPoint_closure⟩
  exact ⟨η, isGenericPoint_def.mp hgen⟩

/-- A dlt pair on a Noetherian scheme has finitely many boundary strata. -/
private theorem finite_setOf_isDltStratum [CompactSpace X] (B : QDivisor X) :
    {T : Set X | IsDltStratum sX B T}.Finite := by
  classical
  haveI : IsNoetherian X := ⟨⟩
  have key : ∀ J : Finset (MMP.Mori.PrimeDivisor X), {T : Set X |
      Maximal (fun T : Set X => IsIrreducible T ∧ T ⊆ ⋂ P ∈ J, (P.support : Set X)) T}.Finite := by
    intro J
    have hC : IsClosed (⋂ P ∈ J, (P.support : Set X)) :=
      isClosed_biInter fun P _ => TopologicalSpace.Closeds.isClosed P.idealSheaf.support
    obtain ⟨S, hSf, hSc, hSi, hS⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
    refine hSf.subset fun T hT => ?_
    obtain ⟨z, hz, hTz⟩ := isIrreducible_iff_sUnion_isClosed.mp hT.1.1 hSf.toFinset
      (fun z hz => hSc z (hSf.mem_toFinset.mp hz)) (by rw [hSf.coe_toFinset, ← hS]; exact hT.1.2)
    rw [Set.Finite.mem_toFinset] at hz
    have hzC : z ⊆ ⋂ P ∈ J, (P.support : Set X) := hS ▸ Set.subset_sUnion_of_mem hz
    have hzT : z ⊆ T := hT.2 ⟨hSi z hz, hzC⟩ hTz
    rwa [show T = z from le_antisymm hTz hzT]
  refine ((B.support.powerset : Set (Finset (MMP.Mori.PrimeDivisor X))).toFinite.biUnion
    fun J _ => key J).subset ?_
  rintro T ⟨-, J, -, hJ1, -, hmax⟩
  refine Set.mem_iUnion₂.mpr ⟨J, ?_, hmax⟩
  rw [Finset.mem_coe, Finset.mem_powerset]
  intro P hP
  rw [Finsupp.mem_support_iff]
  intro h0
  have := hJ1 P hP
  rw [show B.coeff P = B P from rfl, h0] at this
  norm_num at this

/-- A prime divisor with coefficient at least one in the boundary of a dlt pair is a dlt
stratum. -/
private theorem isDltStratum_support (hB : MMP.Intersection.IsDltPair sX B)
    (P : MMP.Mori.PrimeDivisor X) (hP : 1 ≤ B.coeff P) :
    IsDltStratum sX B (P.support : Set X) := by
  have hinter : (⋂ Q ∈ ({P} : Finset (MMP.Mori.PrimeDivisor X)), (Q.support : Set X)) =
      (P.support : Set X) := by simp
  refine ⟨hB, {P}, Finset.singleton_nonempty P, by simpa using hP, ?_, ?_⟩
  · rw [hinter]
    exact ⟨P.genericPoint, by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl⟩
  · rw [hinter]
    refine ⟨⟨?_, le_rfl⟩, fun T hT _ => hT.2⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isIrreducible_singleton.closure

end Strata

/-! ### Dimensions -/

/-- A point whose closure is not contained in the exceptional set of `g` lies over the
biregular locus of `g`. -/
private theorem map_mem_biregularLocus_of_not_closure_subset {Y W : Scheme.{0}} (g : Y ⟶ W)
    {η : Y} (h : ¬ closure {η} ⊆ (exceptionalSet g : Set Y)) : g η ∈ biregularLocus g := by
  by_contra hc
  exact h (closure_minimal (Set.singleton_subset_iff.mpr (mem_exceptionalSet.mpr hc))
    (exceptionalSet g).isClosed)

/-- The closure of a point of dimension zero is that point. -/
private theorem eq_singleton_of_topologicalKrullDim_lt_one {α : Type*} [TopologicalSpace α]
    [T0Space α] {η : α} (hd : topologicalKrullDim (closure {η} : Set α) < 1) :
    closure {η} = ({η} : Set α) := by
  refine le_antisymm (fun y hy => ?_) (Set.singleton_subset_iff.mpr (subset_closure rfl))
  by_contra hne
  set T : Set α := closure {η}
  let a : T := ⟨y, hy⟩
  let b : T := ⟨η, subset_closure rfl⟩
  let A : IrreducibleCloseds T := ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  let C : IrreducibleCloseds T := ⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hba : b ⤳ a := by
    rw [← Topology.IsInducing.subtypeVal.specializes_iff]
    exact specializes_iff_mem_closure.mpr hy
  have hle : (A : Set T) ⊆ C :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hba))
      isClosed_closure
  have hAC : A < C := by
    refine lt_of_le_of_ne (show A ≤ C from hle) fun h => ?_
    have hb : b ∈ (A : Set T) := by
      rw [h]; exact subset_closure rfl
    have hab : a ⤳ b := specializes_iff_mem_closure.mpr hb
    exact hne (congrArg Subtype.val (hab.antisymm hba).eq)
  have : (1 : WithBot ℕ∞) ≤ topologicalKrullDim T := Order.one_le_krullDim_iff.mpr ⟨A, C, hAC⟩
  exact absurd hd (not_lt.mpr this)

/-- Cancellation of a coheight: if `a + c = n = b + c` with `n` finite, then `a = b`. -/
private theorem eq_of_add_eq_of_add_eq {a b : WithBot ℕ∞} {c : ℕ∞} {n : ℕ}
    (ha : a + c = n) (hb : b + c = n) : a = b := by
  have hn : ((n : ℕ∞) : WithBot ℕ∞) = n := rfl
  induction a using WithBot.recBotCoe with
  | bot => simp at ha
  | coe a =>
  induction b using WithBot.recBotCoe with
  | bot => simp at hb
  | coe b =>
  rw [← WithBot.coe_add, ← hn, WithBot.coe_inj] at ha hb
  have hc : c ≠ ⊤ := by rintro rfl; simp at ha
  exact congrArg _ ((ENat.add_left_injective_of_ne_top hc).eq_iff.mp (ha.trans hb.symm))

/-- If `a + m = d` for natural numbers `m ≤ d`, then `a = d - m`. -/
private theorem eq_natCast_sub_of_add_eq {a : WithBot ℕ∞} {m d : ℕ} (hm : m ≤ d)
    (h : a + (m : ℕ∞) = d) : a = ((d - m : ℕ) : WithBot ℕ∞) :=
  eq_of_add_eq_of_add_eq h (by
    rw [← WithBot.coe_natCast, ← WithBot.coe_add, ← Nat.cast_add, Nat.sub_add_cancel hm]; rfl)

/-- In `WithBot ℕ∞`, `x < d + 1` implies `x < d ∨ x = d`. -/
private theorem lt_or_eq_of_lt_natCast_add_one {x : WithBot ℕ∞} {d : ℕ}
    (h : x < ((d + 1 : ℕ) : WithBot ℕ∞)) : x < d ∨ x = d := by
  induction x using WithBot.recBotCoe with
  | bot => exact Or.inl (WithBot.bot_lt_coe _)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have hle : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_natCast]; exact WithBot.coe_le_coe.mpr le_top
      exact absurd h (not_lt.mpr hle)
    | coe e =>
      have h' : e < d + 1 := by exact_mod_cast h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h' with h'' | h''
      · exact Or.inl (by exact_mod_cast h'')
      · exact Or.inr (by rw [h'']; rfl)

/-- For a variety of dimension `d`, the dimension of the closure of a point plus its coheight is
`d`. -/
private theorem topologicalKrullDim_closure_add_coheight' {k : Type} [Field k] {S : Scheme.{0}}
    [IsIntegral S] (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS] {d : ℕ}
    (hd : topologicalKrullDim S = d) (x : S) :
    topologicalKrullDim (closure {x} : Set S) + Order.coheight x = d := by
  rw [MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sS x, hd]

/-- In a variety of dimension `d`, the closure of a point of coheight `m ≤ d` has dimension
`d - m`. -/
private theorem topologicalKrullDim_closure_eq_sub {k : Type} [Field k] {S : Scheme.{0}}
    [IsIntegral S] (sS : S ⟶ Spec (.of k)) [LocallyOfFiniteType sS] {d : ℕ}
    (hd : topologicalKrullDim S = d) {x : S} {m : ℕ} (hx : Order.coheight x = m) (hm : m ≤ d) :
    topologicalKrullDim (closure {x} : Set S) = (d - m : ℕ) := by
  have h := topologicalKrullDim_closure_add_coheight' sS hd x
  rw [hx] at h
  exact eq_natCast_sub_of_add_eq hm h

/-- The closure of a point has nonnegative dimension. -/
private theorem topologicalKrullDim_closure_nonneg {α : Type*} [TopologicalSpace α] (x : α) :
    0 ≤ topologicalKrullDim (closure {x} : Set α) := by
  haveI : Nonempty (TopologicalSpace.IrreducibleCloseds (closure {x} : Set α)) :=
    ⟨⟨closure {⟨x, subset_closure rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

/-- A coheight `c` with `a + c = d` and `0 ≤ a` is at most `d`. -/
private theorem coheight_le_of_add_eq {a : WithBot ℕ∞} {c : ℕ∞} {d : ℕ} (ha : 0 ≤ a)
    (h : a + c = d) : c ≤ d := by
  have : (c : WithBot ℕ∞) ≤ d := by rw [← h]; exact le_add_of_nonneg_left ha
  exact_mod_cast this

/-- On a projective variety with a canonical divisor of dimension `n`, the dimension of the
closure of a point plus its coheight is `n`. -/
private theorem topologicalKrullDim_closure_add_coheight {k : Type} [Field k] {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : MMP.Mori.IsProjectiveVariety k sY) {K : Divisor Y} {n : ℕ}
    (hK : K.IsCanonicalDivisor sY n) (y : Y) :
    topologicalKrullDim (closure {y} : Set Y) + Order.coheight y = n := by
  haveI := hY
  exact topologicalKrullDim_closure_add_coheight' sY hK.topologicalKrullDim_eq y

/-- Points over the biregular loci of `g : Y ⟶ W` and `g' : Y' ⟶ W` with the same image have
closures of the same dimension. -/
private theorem topologicalKrullDim_closure_eq_of_map_eq {k : Type} [Field k]
    {Y Y' W : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y'] {sY : Y ⟶ Spec (.of k)}
    {sY' : Y' ⟶ Spec (.of k)} (hY : MMP.Mori.IsProjectiveVariety k sY)
    (hY' : MMP.Mori.IsProjectiveVariety k sY') {K : Divisor Y} {K' : Divisor Y'} {n : ℕ}
    (hK : K.IsCanonicalDivisor sY n) (hK' : K'.IsCanonicalDivisor sY' n)
    (g : Y ⟶ W) (g' : Y' ⟶ W) {y : Y} {y' : Y'} (hy : g.base y ∈ biregularLocus g)
    (hy' : g'.base y' ∈ biregularLocus g') (hyy : g.base y = g'.base y') :
    topologicalKrullDim (closure {y} : Set Y) = topologicalKrullDim (closure {y'} : Set Y') := by
  have hc : Order.coheight y = Order.coheight y' := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g hy, hyy,
      MMP.Positivity.coheight_map_of_mem_biregularLocus g' hy']
  have h1 := topologicalKrullDim_closure_add_coheight hY hK y
  have h2 := topologicalKrullDim_closure_add_coheight hY' hK' y'
  rw [hc] at h1
  exact eq_of_add_eq_of_add_eq h1 h2

/-! ### Transforms of strata under a flip -/

/-- Transport of a maximal irreducible subset of a closed set along a homeomorphism of open
subsets which matches the two closed sets. -/
private theorem maximal_closure_image_of_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {U' : Set α} {U : Set β} (hU' : IsOpen U') (hU : IsOpen U)
    (ψ : U' ≃ₜ U) {C' : Set α} {C : Set β} (hC' : IsClosed C') (hC : IsClosed C)
    (hCC : ∀ x : U', (x : α) ∈ C' ↔ (ψ x : β) ∈ C)
    {T' : Set α} (hT' : Maximal (fun T => IsIrreducible T ∧ T ⊆ C') T')
    {η : U'} (hη : (η : α) ∈ T') :
    Maximal (fun T => IsIrreducible T ∧ T ⊆ C)
      (closure ((fun x : U' => (ψ x : β)) '' (Subtype.val ⁻¹' T'))) := by
  set g : U' → β := fun x => (ψ x : β)
  have hg : Continuous g := continuous_subtype_val.comp ψ.continuous
  set S' : Set U' := Subtype.val ⁻¹' T'
  have hS' : IsIrreducible S' := ⟨⟨η, hη⟩, hT'.1.1.2.preimage hU'.isOpenEmbedding_subtypeVal⟩
  refine ⟨⟨(hS'.image g hg.continuousOn).closure, closure_minimal ?_ hC⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact (hCC x).mp (hT'.1.2 hx)
  intro T'' ⟨hT''i, hT''C⟩ hle
  set R : Set U := Subtype.val ⁻¹' T''
  have hgη : (ψ η : β) ∈ T'' := hle (subset_closure ⟨η, hη, rfl⟩)
  have hR : IsIrreducible R := ⟨⟨ψ η, hgη⟩, hT''i.2.preimage hU.isOpenEmbedding_subtypeVal⟩
  set g' : U → α := fun y => (ψ.symm y : α)
  have hg' : Continuous g' := continuous_subtype_val.comp ψ.symm.continuous
  have hR'i : IsIrreducible (closure (g' '' R)) := (hR.image g' hg'.continuousOn).closure
  have hR'C : closure (g' '' R) ⊆ C' := closure_minimal (by
    rintro _ ⟨y, hy, rfl⟩
    refine (hCC (ψ.symm y)).mpr ?_
    rw [Homeomorph.apply_symm_apply]; exact hT''C hy) hC'
  have hT'sub : T' ⊆ closure (g' '' R) := by
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen hT'.1.1.2 hU'
      ⟨η, hη, η.2⟩).trans (closure_mono ?_)
    rintro x ⟨hxT, hxU⟩
    refine ⟨ψ ⟨x, hxU⟩, hle (subset_closure ⟨⟨x, hxU⟩, hxT, rfl⟩), ?_⟩
    simp [g']
  have hmax := hT'.2 ⟨hR'i, hR'C⟩ hT'sub
  refine (subset_closure_inter_of_isPreirreducible_of_isOpen hT''i.2 hU
    ⟨_, hgη, (ψ η).2⟩).trans (closure_mono ?_)
  rintro y ⟨hyT, hyU⟩
  refine ⟨ψ.symm ⟨y, hyU⟩, hmax (subset_closure ⟨⟨y, hyU⟩, hyT, rfl⟩), ?_⟩
  simp [g]

/-- The closure of the image of the closure of a point is the closure of the image point. -/
private theorem closure_image_closure_singleton {Y W : Scheme.{0}} (g : Y ⟶ W) (η : Y) :
    closure (g.base '' closure {η}) = closure {g.base η} := by
  rw [closure_image_closure g.base.hom.continuous, Set.image_singleton]

/-- Two closed irreducible subsets not contained in the exceptional set of `g` and with the same
closure of their images coincide. -/
private theorem eq_of_closure_image_eq {Y Z : Scheme.{0}} (g : Y ⟶ Z) {T₁ T₂ : Set Y}
    (h₁ : IsClosed T₁ ∧ IsIrreducible T₁) (h₂ : IsClosed T₂ ∧ IsIrreducible T₂)
    (h₁e : ¬ T₁ ⊆ (exceptionalSet g : Set Y)) (h₂e : ¬ T₂ ⊆ (exceptionalSet g : Set Y))
    (h : closure (g.base '' T₁) = closure (g.base '' T₂)) : T₁ = T₂ := by
  -- a closed irreducible set not in `Ex(g)` has its generic point over the biregular locus
  have key : ∀ {T : Set Y}, IsClosed T ∧ IsIrreducible T → ¬ T ⊆ (exceptionalSet g : Set Y) →
      ∃ η : Y, closure {η} = T ∧ η ∈ (g ⁻¹ᵁ biregularLocus g : Set Y) ∧
        closure (g.base '' T) = closure {g.base η} := by
    intro T hT hTe
    obtain ⟨η, hgen⟩ : ∃ η, IsGenericPoint η T :=
      ⟨_, by simpa [hT.1.closure_eq] using hT.2.isGenericPoint_genericPoint_closure⟩
    have hcl : closure {η} = T := isGenericPoint_def.mp hgen
    refine ⟨η, hcl, ?_, ?_⟩
    · obtain ⟨x, hxT, hxe⟩ := Set.not_subset.mp hTe
      have hx : g.base x ∈ biregularLocus g := by
        by_contra hx; exact hxe (mem_exceptionalSet.mpr hx)
      have hsp : η ⤳ x := by rw [specializes_iff_mem_closure, hcl]; exact hxT
      exact (hsp.map g.base.hom.continuous).mem_open (biregularLocus g).isOpen hx
    · rw [← hcl, closure_image_closure_singleton]
  obtain ⟨η₁, e₁, m₁, c₁⟩ := key h₁ h₁e
  obtain ⟨η₂, e₂, m₂, c₂⟩ := key h₂ h₂e
  have hη : g.base η₁ = g.base η₂ := by
    rw [c₁, c₂] at h
    exact (inseparable_iff_closure_eq.mpr h).eq
  rw [← e₁, ← e₂, injOn_preimage_biregularLocus g m₁ m₂ hη]

/-- Two closures of points with the same closure of images have the same image points. -/
private theorem map_eq_of_closure_image_eq {Y Y' W : Scheme.{0}} (g : Y ⟶ W) (g' : Y' ⟶ W)
    {η : Y} {η' : Y'} (h : closure (g.base '' closure {η}) = closure (g'.base '' closure {η'})) :
    g.base η = g'.base η' := by
  rw [closure_image_closure_singleton, closure_image_closure_singleton] at h
  exact (inseparable_iff_closure_eq.mpr h).eq

section Transform

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X X' Z : Scheme.{0}}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
  {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
  {f : X ⟶ Z} {fp : X' ⟶ Z} {K : Divisor X} {B : QDivisor X}

/-- A boundary stratum after the flip whose generic point lies over the common biregular locus
of `f` and `f⁺` is the birational transform of a boundary stratum before the flip. -/
private theorem exists_isDltStratum_of_mem_biregularLocus
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    (hB : MMP.Intersection.IsDltPair sX B) {T' : Set X'}
    (hT' : IsDltStratum sX' (flipTransform f fp B) T') {η : X'} (hη : closure {η} = T')
    (hηV : fp.base η ∈ biregularLocus f) (hηV' : fp.base η ∈ biregularLocus fp) :
    ∃ T : Set X, IsDltStratum sX B T ∧ ¬ T ⊆ (exceptionalSet f : Set X) ∧
      closure (f.base '' T) = closure (fp.base '' T') := by
  classical
  have hc := hflip.isContraction
  have hs := hflip.isSmallMorphism
  haveI : IsProper f := hs.isProper
  have hZ := hc.isNormalVariety_target
  have hXv : IsNormalVariety k (f ≫ sZ) := hc.comp_eq ▸ hc.isNormalVariety_source
  obtain ⟨-, J', hJ'ne, hJ'1, -, hmax'⟩ := hT'
  -- the common biregular locus and the homeomorphism over it
  set W := biregularLocus f ⊓ biregularLocus fp with hWdef
  haveI : IsIso (f ∣_ W) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI : IsIso (fp ∣_ W) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  let ef : (f ⁻¹ᵁ W : Set X) ≃ₜ (W : Set Z) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (f ∣_ W)))
  let efp : (fp ⁻¹ᵁ W : Set X') ≃ₜ (W : Set Z) :=
    TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (fp ∣_ W)))
  let ψ := efp.trans ef.symm
  have h2 : ∀ y : (f ⁻¹ᵁ W : Set X), (ef y : Z) = f.base (y : X) := fun y => by
    change ((f ∣_ W).base y).val = f.base y.val
    exact morphismRestrict_base_coe f W y
  have h2' : ∀ y : (fp ⁻¹ᵁ W : Set X'), (efp y : Z) = fp.base (y : X') := fun y => by
    change ((fp ∣_ W).base y).val = fp.base y.val
    exact morphismRestrict_base_coe fp W y
  have hψ : ∀ x : (fp ⁻¹ᵁ W : Set X'), f.base (ψ x : X) = fp.base (x : X') := by
    intro x
    rw [← h2, ← h2', Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
  have hfV : ∀ y : (f ⁻¹ᵁ W : Set X), f.base (y : X) ∈ biregularLocus f := fun y => y.2.1
  have hηT : η ∈ T' := hη ▸ subset_closure rfl
  have hηW : fp.base η ∈ W := ⟨hηV, hηV'⟩
  -- the generic points of the components in `J'` lie over `W`
  have hJ'W : ∀ P' ∈ J', fp.base P'.genericPoint ∈ W := by
    intro P' hP'
    have hmem : η ∈ P'.support := Set.mem_iInter₂.mp (hmax'.1.2 hηT) P' hP'
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
    exact ((specializes_iff_mem_closure.mpr hmem).map fp.base.hom.continuous).mem_open
      W.isOpen hηW
  -- the corresponding prime divisors of `X`
  have hex : ∀ P' : J', ∃ P : MMP.Mori.PrimeDivisor X,
      f.base P.genericPoint = fp.base (P' : MMP.Mori.PrimeDivisor X').genericPoint := by
    rintro ⟨P', hP'⟩
    set x := ef.symm ⟨_, hJ'W P' hP'⟩
    have hx : f.base (x : X) = fp.base P'.genericPoint := by
      rw [← h2, Homeomorph.apply_symm_apply]
    have hco : Order.coheight (x : X) = 1 := by
      rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (hfV x), hx,
        MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hJ'W P' hP').2,
        AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
      (congrArg f.base (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco)).trans hx⟩
  choose σ hσ using hex
  set J : Finset (MMP.Mori.PrimeDivisor X) := J'.attach.image σ
  -- membership in the supports corresponds under `ψ`
  have hsupp : ∀ (P' : J') (x : (fp ⁻¹ᵁ W : Set X')),
      (x : X') ∈ (P' : MMP.Mori.PrimeDivisor X').support ↔ (ψ x : X) ∈ (σ P').support := by
    intro P' x
    set ξ : (fp ⁻¹ᵁ W : Set X') := ⟨_, hJ'W P'.1 P'.2⟩
    have hξ : (ψ ξ : X) = (σ P').genericPoint := by
      refine injOn_preimage_biregularLocus f (hfV (ψ ξ)) ?_ ?_
      · show f.base (σ P').genericPoint ∈ biregularLocus f
        rw [hσ]
        exact (hJ'W P'.1 P'.2).1
      · rw [hψ, hσ]
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← specializes_iff_mem_closure,
      ← specializes_iff_mem_closure,
      show AlgebraicGeometry.PrimeDivisor.genericPoint (σ P') = (ψ ξ : X) from hξ.symm]
    change (ξ : X') ⤳ (x : X') ↔ ((ψ ξ : (f ⁻¹ᵁ W : Set X)) : X) ⤳ (ψ x : X)
    rw [Topology.IsInducing.subtypeVal.specializes_iff,
      Topology.IsInducing.subtypeVal.specializes_iff, ψ.isInducing.specializes_iff]
  have hCC : ∀ x : (fp ⁻¹ᵁ W : Set X'), (x : X') ∈ (⋂ P' ∈ J', (P'.support : Set X')) ↔
      (ψ x : X) ∈ (⋂ P ∈ J, (P.support : Set X)) := by
    intro x
    simp only [Set.mem_iInter₂]
    refine ⟨fun h P hP => ?_, fun h P' hP' =>
      (hsupp ⟨P', hP'⟩ x).mpr (h _ (Finset.mem_image_of_mem σ (Finset.mem_attach _ _)))⟩
    obtain ⟨P', -, rfl⟩ := Finset.mem_image.mp hP
    exact (hsupp P' x).mp (h P'.1 P'.2)
  have hC' : IsClosed (⋂ P' ∈ J', (P'.support : Set X')) :=
    isClosed_biInter fun P _ => TopologicalSpace.Closeds.isClosed P.idealSheaf.support
  have hC : IsClosed (⋂ P ∈ J, (P.support : Set X)) :=
    isClosed_biInter fun P _ => TopologicalSpace.Closeds.isClosed P.idealSheaf.support
  set η₀ : (fp ⁻¹ᵁ W : Set X') := ⟨η, hηW⟩
  have hmax := maximal_closure_image_of_homeomorph (fp ⁻¹ᵁ W).isOpen (f ⁻¹ᵁ W).isOpen ψ hC' hC
    hCC hmax' (η := η₀) hηT
  set T := closure ((fun x : (fp ⁻¹ᵁ W : Set X') => (ψ x : X)) '' (Subtype.val ⁻¹' T'))
  have hψη : (ψ η₀ : X) ∈ T := subset_closure ⟨η₀, hηT, rfl⟩
  have hfψη : f.base (ψ η₀ : X) = fp.base η := hψ η₀
  refine ⟨T, ⟨hB, J, ?_, ?_, ⟨_, hmax.1.2 hψη⟩, hmax⟩, fun hsub => ?_, ?_⟩
  · obtain ⟨P', hP'⟩ := hJ'ne
    exact ⟨σ ⟨P', hP'⟩, Finset.mem_image.mpr ⟨⟨P', hP'⟩, Finset.mem_attach _ _, rfl⟩⟩
  · intro P hP
    obtain ⟨P', -, rfl⟩ := Finset.mem_image.mp hP
    have hP'V := hJ'W P'.1 P'.2
    have := flipTransform_apply_of_mem hZ hXv hs.isBirationalMorphism
      ((hσ P').symm ▸ hP'V.1) hP'V.2 (hσ P') B
    change 1 ≤ B (σ P')
    rw [← this]
    exact hJ'1 P'.1 P'.2
  · exact (mem_exceptionalSet.mp (hsub hψη)) (hfψη ▸ hηV)
  · -- both closures are the closure of `f⁺(η)`
    have hT'cl : closure (fp.base '' T') = closure {fp.base η} := by
      rw [← hη, closure_image_closure_singleton]
    rw [hT'cl]
    refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono
      (Set.singleton_subset_iff.mpr ⟨_, hψη, hfψη⟩))
    calc f.base '' T ⊆ closure (f.base '' ((fun x : (fp ⁻¹ᵁ W : Set X') => (ψ x : X)) ''
          (Subtype.val ⁻¹' T'))) := image_closure_subset_closure_image f.base.hom.continuous
      _ ⊆ closure {fp.base η} := by
        refine closure_minimal ?_ isClosed_closure
        rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        rw [hψ x, ← hT'cl]
        exact subset_closure (Set.mem_image_of_mem _ hx)

end Transform

/-! ### Strata as images of closed immersions -/

/-- A morphism from an irreducible scheme with range `closure {η}` maps the generic point to `η`. -/
private theorem map_genericPoint_eq_of_range_eq {S Y : Scheme.{0}} [IrreducibleSpace S]
    (g : S ⟶ Y) {η : Y} (h : Set.range g.base = closure {η}) :
    g (genericPoint S) = η := by
  have h1 := (genericPoint_spec S).image g.base.hom.continuous
  have h2 : closure (g.base.hom '' Set.univ) = closure {η} := by
    rw [Set.image_univ, h, closure_closure]
  rw [h2] at h1
  exact (inseparable_iff_closure_eq.mpr (isGenericPoint_def.mp h1)).eq

/-- A closed immersion preserves the dimension: the source is homeomorphic to the range. -/
private theorem topologicalKrullDim_eq_of_isClosedImmersion {S Y : Scheme.{0}} (g : S ⟶ Y)
    [IsClosedImmersion g] :
    topologicalKrullDim S = topologicalKrullDim (Set.range g.base) :=
  IsHomeomorph.topologicalKrullDim_eq _ g.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph

/-! ### Morphisms between strata -/

section Geometry

/-- A morphism from a reduced scheme into the range of a closed immersion with reduced source
factors through it. -/
private theorem exists_lift_of_range_subset {Y S X : Scheme.{0}} [IsReduced Y] [IsReduced S]
    (i : S ⟶ X) [IsClosedImmersion i] (g : Y ⟶ X) (h : Set.range g.base ⊆ Set.range i.base) :
    ∃ l : Y ⟶ S, l ≫ i = g := by
  have H : i.ker ≤ g.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range i,
      Scheme.Hom.ker_eq_vanishingIdeal_closure_range g]
    exact Scheme.IdealSheafData.vanishingIdeal_antimono (fun x hx => closure_mono h hx)
  exact ⟨IsClosedImmersion.lift i g H, IsClosedImmersion.lift_fac i g H⟩

/-- If `u ≫ v` is surjective and `v` is a homomorphism from a field to a nontrivial ring, then
`v` is an isomorphism. -/
private theorem isIso_of_surjective_comp_of_isField {A B C : CommRingCat.{0}} (u : A ⟶ B)
    (v : B ⟶ C) (hs : Function.Surjective (u ≫ v)) (hB : IsField B) [Nontrivial C] : IsIso v := by
  have hsurj : Function.Surjective v := by
    intro c
    obtain ⟨a, ha⟩ := hs c
    exact ⟨u a, by rw [← ha]; rfl⟩
  have hinj : Function.Injective v := by
    letI := hB.toField
    exact RingHom.injective v.hom
  exact (ConcreteCategory.isIso_iff_bijective v).mpr ⟨hinj, hsurj⟩

/-- If `u ≫ v` is an isomorphism, `v` is a homomorphism from a field to a nontrivial ring, then
`u` is an isomorphism. -/
private theorem isIso_of_isIso_comp_of_isField {A B C : CommRingCat.{0}} (u : A ⟶ B) (v : B ⟶ C)
    (huv : IsIso (u ≫ v)) (hB : IsField B) [Nontrivial C] : IsIso u :=
  haveI := isIso_of_surjective_comp_of_isField u v
    (ConcreteCategory.bijective_of_isIso (u ≫ v)).2 hB
  IsIso.of_isIso_comp_right u v

/-- **Extension over a quasi-finite target.** Let `S` be a normal variety, `a : S ⟶ W` and
`b : S' ⟶ W` with `b` proper and locally quasi-finite, and let `u : U ⟶ S'` be a morphism over `W`
on a nonempty open `U ⊆ S`. Then `u` extends to a morphism `g : S ⟶ S'` over `W`: the closure of
the graph of `u` in `S ×_W S'` is proper, birational and quasi-finite over the normal `S`, hence
isomorphic to it. -/
private theorem exists_hom_comp_eq_of_locallyQuasiFinite {k : Type} [Field k]
    {S S' W : Scheme.{0}} [IsIntegral S] [IsNormal S] {sS : S ⟶ Spec (.of k)}
    (hS : AlgebraicGeometry.IsVariety k sS) (a : S ⟶ W) (b : S' ⟶ W) [IsProper b]
    [LocallyQuasiFinite b]
    (U : S.Opens) (hU : (U : Set S).Nonempty) (u : U.toScheme ⟶ S') (hu : u ≫ b = U.ι ≫ a) :
    ∃ g : S ⟶ S', g ≫ b = a ∧ U.ι ≫ g = u := by
  haveI := hS
  haveI : Nonempty U := hU.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  let γ : U.toScheme ⟶ Limits.pullback a b := Limits.pullback.lift U.ι u hu.symm
  have hγ1 : γ ≫ Limits.pullback.fst a b = U.ι := Limits.pullback.lift_fst _ _ _
  have hγ2 : γ ≫ Limits.pullback.snd a b = u := Limits.pullback.lift_snd _ _ _
  haveI : QuasiCompact (γ ≫ Limits.pullback.fst a b) := by rw [hγ1]; infer_instance
  haveI : QuasiCompact γ := QuasiCompact.of_comp γ (Limits.pullback.fst a b)
  let t := γ.toImage
  let i := γ.imageι
  have hti : t ≫ i = γ := γ.toImage_imageι
  let p := i ≫ Limits.pullback.fst a b
  have htp : t ≫ p = U.ι := by
    change t ≫ i ≫ Limits.pullback.fst a b = U.ι
    rw [← Category.assoc, hti, hγ1]
  haveI : IsIntegral γ.image := Scheme.Hom.isIntegral_image γ
  haveI : IsProper p := by change IsProper (i ≫ Limits.pullback.fst a b); infer_instance
  haveI : LocallyQuasiFinite p := by
    change LocallyQuasiFinite (i ≫ Limits.pullback.fst a b); infer_instance
  have hU0 : U.ι (genericPoint U) = genericPoint S := genericPoint_eq_of_isOpenImmersion U.ι
  have ht0 : t (genericPoint U) = genericPoint γ.image := genericPoint_eq_of_isDominant t
  have hp0 : p (genericPoint γ.image) = genericPoint S := by
    rw [← ht0, ← Scheme.Hom.comp_apply, htp, hU0]
  have hbir : IsBirational p := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
      exact Set.bijOn_singleton.mpr hp0
    · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
      subst hx
      rw [← ht0]
      have h1 : IsIso ((t ≫ p).stalkMap (genericPoint U)) := by
        rw [Scheme.Hom.stalkMap_congr_hom (t ≫ p) U.ι htp]; infer_instance
      rw [Scheme.Hom.stalkMap_comp] at h1
      have hB : IsField (γ.image.presheaf.stalk (t (genericPoint U))) := by
        rw [ht0]; exact Field.toIsField γ.image.functionField
      haveI : Nontrivial (U.toScheme.presheaf.stalk (genericPoint U)) :=
        inferInstanceAs (Nontrivial U.toScheme.functionField)
      exact isIso_of_isIso_comp_of_isField (p.stalkMap (t (genericPoint U)))
        (t.stalkMap (genericPoint U)) h1 hB
  have hΓ : AlgebraicGeometry.IsVariety k (p ≫ sS) := AlgebraicGeometry.IsVariety.mk
  obtain ⟨-, -, hiso⟩ :=
    MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k hΓ hS p rfl hbir
  haveI : IsIso p := hiso inferInstance
  refine ⟨inv p ≫ i ≫ Limits.pullback.snd a b, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← Limits.pullback.condition, ← Category.assoc i,
      show i ≫ Limits.pullback.fst a b = p from rfl, IsIso.inv_hom_id_assoc]
  · have h2 : U.ι ≫ inv p = t := by
      rw [← htp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, h2, ← Category.assoc, hti, hγ2]

/-- A closed subscheme `ι : S ⟶ Y` of a proper `k`-scheme stays proper over a separated
`k`-scheme `W` through any `k`-morphism `g : Y ⟶ W`. -/
private theorem isProper_comp_of_comp_eq {k : Type} [Field k] {S Y W : Scheme.{0}} (ι : S ⟶ Y)
    (g : Y ⟶ W) {sY : Y ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsSeparated sW]
    (hg : g ≫ sW = sY) (hι : IsProper (ι ≫ sY)) : IsProper (ι ≫ g) := by
  haveI : IsProper ((ι ≫ g) ≫ sW) := by rw [Category.assoc, hg]; exact hι
  exact IsProper.of_comp _ sW

/-- If `ι` is a closed immersion and `g` is biregular over `g (ι y)`, then `y` is the only point
of its fibre under `ι ≫ g`. -/
private theorem eq_of_comp_apply_eq_of_mem_biregularLocus {S Y W : Scheme.{0}} (ι : S ⟶ Y)
    [IsClosedImmersion ι] (g : Y ⟶ W) {x y : S} (hV : g (ι y) ∈ biregularLocus g)
    (h : (ι ≫ g) x = (ι ≫ g) y) : x = y := by
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
  have hx : g (ι x) ∈ biregularLocus g := h ▸ hV
  exact ι.isClosedEmbedding.injective (injOn_preimage_biregularLocus g hx hV h)

/-- A morphism `g : S ⟶ S'` of integral schemes carrying the generic point to the generic point is
birational once `a = g ≫ b` is surjective on the local ring at the generic point of `S`. -/
private theorem isBirational_of_comp_eq {S S' W : Scheme.{0}} [IsIntegral S] [IsIntegral S']
    (g : S ⟶ S') (b : S' ⟶ W) {a : S ⟶ W} (hgb : g ≫ b = a)
    (hg0 : g (genericPoint S) = genericPoint S')
    (ha : Function.Surjective (a.stalkMap (genericPoint S))) : IsBirational g := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    exact Set.bijOn_singleton.mpr hg0
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    have hs : Function.Surjective
        (b.stalkMap (g (genericPoint S)) ≫ g.stalkMap (genericPoint S)) := by
      rw [← Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_congr_hom _ _ hgb]
      exact ha.comp (Iso.commRingCatIsoToRingEquiv _).surjective
    have hB : IsField (S'.presheaf.stalk (g (genericPoint S))) := by
      rw [hg0]; exact Field.toIsField S'.functionField
    haveI : Nontrivial (S.presheaf.stalk (genericPoint S)) :=
      inferInstanceAs (Nontrivial S.functionField)
    exact isIso_of_surjective_comp_of_isField _ _ hs hB

/-- A quasi-compact morphism locally of finite type in whose fibres no point specializes to
another is locally quasi-finite. -/
private theorem locallyQuasiFinite_of_forall_specializes {X Y : Scheme.{0}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f]
    (h : ∀ x y : X, f x = f y → x ⤳ y → x = y) : LocallyQuasiFinite f := by
  refine locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun w => ?_
  refine MMP.Resolution.Bridges.finite_preimage_singleton_of_topologicalKrullDim_le f w ?_
  rw [← IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo w).isHomeomorph]
  set e := f.fiberHomeo w
  -- every irreducible closed subset of the fibre is a point
  have hpt : ∀ (C : TopologicalSpace.IrreducibleCloseds (f.fiber w)) (x : f.fiber w),
      x ∈ C → x = C.isIrreducible.genericPoint := by
    intro C x hx
    have hgen := C.isIrreducible.isGenericPoint_genericPoint_closure
    rw [C.isClosed.closure_eq] at hgen
    have hsp : C.isIrreducible.genericPoint ⤳ x := hgen.specializes hx
    have hsp' : ((e C.isIrreducible.genericPoint : X)) ⤳ (e x : X) :=
      (hsp.map e.continuous).map continuous_subtype_val
    have hf : f (e C.isIrreducible.genericPoint : X) = f (e x : X) :=
      ((e C.isIrreducible.genericPoint).2.trans (e x).2.symm)
    exact (e.injective (Subtype.ext (h _ _ hf hsp'))).symm
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun C D hCD => ?_
  obtain ⟨c, hc⟩ := C.isIrreducible.nonempty
  intro x hx
  rw [hpt D x hx, ← hpt D c (hCD hc)]
  exact hc

/-- A singleton has topological Krull dimension at most zero. -/
private theorem topologicalKrullDim_singleton_le_zero {α : Type*} [TopologicalSpace α] (a : α) :
    topologicalKrullDim (({a} : Set α)) ≤ 0 := by
  haveI : Subsingleton (({a} : Set α)) := Set.subsingleton_singleton.coe_sort
  haveI : DiscreteTopology (({a} : Set α)) := Subsingleton.discreteTopology
  exact topologicalKrullDim_zero_of_discreteTopology _

/-- **Fibres of maps from strata of dimension at most two.** Let `h : S ⟶ Y` be a closed map from
a variety of dimension `d ≤ 2` whose fibre through the generic point is that point and which
sends no point of codimension one to a closed point when `d = 2`. Then no two distinct points of
a fibre of `h` specialize one to the other. -/
private theorem forall_specializes_eq_of_le_two {k : Type} [Field k] {S Y : Scheme.{0}}
    [IsIntegral S] {sS : S ⟶ Spec (.of k)} [LocallyOfFiniteType sS] {d : ℕ}
    (hd : topologicalKrullDim S = d) (hd2 : d ≤ 2) (h : S ⟶ Y) (hcl : IsClosedMap h.base)
    (h1 : ∀ x, h x = h (genericPoint S) → x = genericPoint S)
    (h2 : ∀ x, Order.coheight x = 1 → d = 2 → ¬ IsClosed ({h x} : Set Y)) :
    ∀ x y : S, h x = h y → x ⤳ y → x = y := by
  intro x y hxy hsp
  by_contra hne
  have hlt : y < x := lt_of_le_not_ge (show y ≤ x from hsp) (fun h' => hne (hsp.antisymm h').eq)
  have hfy := topologicalKrullDim_closure_add_coheight' sS hd y
  have hcy : Order.coheight y ≤ d :=
    coheight_le_of_add_eq (topologicalKrullDim_closure_nonneg y) hfy
  have hc := Order.coheight_strictAnti hlt
    (lt_of_le_of_lt ((Order.coheight_anti hlt.le).trans hcy) (ENat.coe_lt_top d))
  have hx2 : Order.coheight x < 2 :=
    lt_of_lt_of_le hc (hcy.trans (by exact_mod_cast hd2))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Order.coheight x = m :=
    (ENat.ne_top_iff_exists.mp (ne_top_of_lt hx2)).imp fun _ h => h.symm
  rw [hm] at hx2 hc
  have hm2 : m < 2 := by exact_mod_cast hx2
  interval_cases m
  · -- `x` is the generic point
    have hmax : IsMax x := Order.coheight_eq_zero.mp (by exact_mod_cast hm)
    have h1' : genericPoint S ⤳ x := (genericPoint_spec S).specializes trivial
    have h2' : x ⤳ genericPoint S := hmax h1'
    have hgx : x = genericPoint S := (h2'.antisymm h1').eq
    have hy := h1 y (by rw [← hxy, hgx])
    exact hne (hgx.trans hy.symm)
  · -- `x` has codimension one, so `d = 2` and `y` is closed
    have hcy2 : Order.coheight y = 2 := by
      have h1y : (1 : ℕ∞) < Order.coheight y := by exact_mod_cast hc
      have : Order.coheight y ≤ 2 := hcy.trans (by exact_mod_cast hd2)
      obtain ⟨n, hn⟩ : ∃ n : ℕ, Order.coheight y = n :=
        (ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by decide) this)).imp fun _ h => h.symm
      rw [hn] at h1y this ⊢
      have : n = 2 := by
        have a1 : 1 < n := by exact_mod_cast h1y
        have a2 : n ≤ 2 := by exact_mod_cast this
        omega
      rw [this]; rfl
    have hd2' : d = 2 := by
      have : (2 : ℕ∞) ≤ d := hcy2 ▸ hcy
      have : 2 ≤ d := by exact_mod_cast this
      omega
    have hy0 : topologicalKrullDim (closure {y} : Set S) < 1 := by
      rw [topologicalKrullDim_closure_eq_sub sS hd (m := 2) (by exact_mod_cast hcy2) (by omega),
        hd2']
      norm_num
    have hycl : IsClosed ({y} : Set S) := by
      rw [← eq_singleton_of_topologicalKrullDim_lt_one hy0]; exact isClosed_closure
    have := hcl _ hycl
    rw [Set.image_singleton, ← hxy] at this
    exact h2 x (by exact_mod_cast hm) hd2' this

end Geometry

section Chain

/-- The composite `S a ⟶ S (a + n)` of a chain of morphisms. -/
private noncomputable def chainComp {S : ℕ → Scheme.{0}} (g : ∀ j, S j ⟶ S (j + 1)) (a : ℕ) :
    ∀ n : ℕ, S a ⟶ S (a + n)
  | 0 => 𝟙 (S a)
  | n + 1 => chainComp g a n ≫ g (a + n)

/-- **Chains of birational morphisms of normal surfaces contract curves only finitely often.**
In an infinite chain of proper birational morphisms of normal surfaces over a field of
characteristic zero, from some index on no morphism maps a curve to a point. -/
private theorem eventually_not_isExceptionalCurve {k : Type} [Field k] [CharZero k]
    {S : ℕ → Scheme.{0}} [∀ j, IsIntegral (S j)] [∀ j, IsNormal (S j)]
    {sS : ∀ j, S j ⟶ Spec (.of k)} (hSv : ∀ j, IsNormalVariety k (sS j))
    (hdim : ∀ j, topologicalKrullDim (S j) = 2) (g : ∀ j, S j ⟶ S (j + 1))
    (hcomp : ∀ j, g j ≫ sS (j + 1) = sS j) (hprop : ∀ j, IsProper (g j))
    (hbir : ∀ j, IsBirational (g j)) :
    ∃ N, ∀ j ≥ N, ¬ ∃ C : (S j).IdealSheafData, IsExceptionalCurve (g j) C := by
  classical
  by_contra hcon
  push Not at hcon
  choose nxt hnxt hC using hcon
  -- the contracting indices
  let p : ℕ → ℕ := fun t => Nat.rec (nxt 0) (fun _ q => q + (nxt (q + 1) - q)) t
  have hpsucc : ∀ t, p (t + 1) = p t + (nxt (p t + 1) - p t) := fun _ => rfl
  have hpeq : ∀ t, p (t + 1) = nxt (p t + 1) := fun t => by
    rw [hpsucc]; have := hnxt (p t + 1); omega
  have hpC : ∀ t, ∃ C : (S (p t)).IdealSheafData, IsExceptionalCurve (g (p t)) C := by
    intro t
    cases t with
    | zero => exact hC 0
    | succ t => rw [hpeq t]; exact hC _
  -- properties of the composites
  have hG : ∀ a n, chainComp g a n ≫ sS (a + n) = sS a ∧ IsProper (chainComp g a n) ∧
      IsBirational (chainComp g a n) := by
    intro a n
    induction n with
    | zero =>
      refine ⟨Category.id_comp _, by change IsProper (𝟙 (S a)); infer_instance,
        Stacks.Chow.isBirational_id _⟩
    | succ n ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      haveI := h2
      haveI := hprop (a + n)
      refine ⟨?_, ?_, h3.comp (hbir (a + n))⟩
      · change (chainComp g a n ≫ g (a + n)) ≫ sS (a + n + 1) = sS a
        rw [Category.assoc, hcomp, h1]
      · change IsProper (chainComp g a n ≫ g (a + n)); infer_instance
  have hGC : ∀ a n (C : (S a).IdealSheafData), IsExceptionalCurve (g a) C →
      IsExceptionalCurve (chainComp g a (n + 1)) C := by
    intro a n C hCa
    induction n with
    | zero =>
      refine ⟨hCa.1, ?_⟩
      obtain ⟨x, hx⟩ := hCa.2
      refine ⟨x, ?_⟩
      change (𝟙 (S a) ≫ g (a + 0)).base '' _ = _
      rw [Category.id_comp]; exact hx
    | succ n ih =>
      obtain ⟨hcur, x, hx⟩ := ih
      refine ⟨hcur, g (a + (n + 1)) x, ?_⟩
      change (chainComp g a (n + 1) ≫ g (a + (n + 1))).base '' _ = _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, hx, Set.image_singleton]
  -- the chain bound for the surface `S (p 0)`
  obtain ⟨Mb, hMb⟩ := MMP.Mori.exists_forall_length_le_of_isExceptionalCurve_chain k (sS (p 0))
    (hSv (p 0)) (hdim (p 0))
  have := hMb (Mb + 1) (fun t => S (p t)) (fun t => sS (p t))
    (fun t => chainComp g (p t) (nxt (p t + 1) - p t)) (Iso.refl _) (Category.id_comp _)
    (fun t _ => ⟨hSv _, hdim _⟩) (fun t _ => by
      obtain ⟨h1, h2, h3⟩ := hG (p t) (nxt (p t + 1) - p t)
      haveI := h2
      refine ⟨h1, h2, Oai4C1.CommonModel.isBirationalMorphism_of_isBirational _ h3, ?_⟩
      obtain ⟨C, hCt⟩ := hpC t
      obtain ⟨m, hm⟩ : ∃ m, nxt (p t + 1) - p t = m + 1 :=
        ⟨nxt (p t + 1) - p t - 1, by have := hnxt (p t + 1); omega⟩
      -- `S (p (t + 1))` is `S (p t + n)` only up to unfolding `p`, so generalize `n` first
      have key : ∀ n, n = m + 1 → IsExceptionalCurve (chainComp g (p t) n) C := fun n hn => by
        subst hn; exact hGC (p t) m C hCt
      exact ⟨C, key _ hm⟩)
  omega

end Chain

/-! ### Sequences of flips -/

section Seq

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Z : ℕ → Scheme.{0}}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  [∀ i, CompactSpace (X i)]

/-- A sequence of flips of projective dlt threefolds, `B (i + 1)` the strict transform of `B i`,
in which from the index `M` on no boundary stratum lies in a flipping or a flipped locus, and
every boundary stratum has a birational transform. -/
private structure IsTail (sX : ∀ i, X i ⟶ Spec (.of k)) (sZ : ∀ i, Z i ⟶ Spec (.of k))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i) (K : ∀ i, Divisor (X i))
    (B : ∀ i, QDivisor (X i)) (M : ℕ) : Prop where
  proj : ∀ i, MMP.Mori.IsProjectiveVariety k (sX i)
  dlt : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i)
  canon : ∀ i, (K i).IsCanonicalDivisor (sX i) 3
  flip : ∀ i, IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i)
  trans : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i)
  strata : ∀ i ≥ M, ∀ T, IsDltStratum (sX i) (B i) T → ¬ T ⊆ (exceptionalSet (f i) : Set (X i))
  strata' : ∀ i ≥ M, ∀ T', IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
    ¬ T' ⊆ (exceptionalSet (fp i) : Set (X (i + 1)))
  strata_trans : ∀ i ≥ M, ∀ T, IsDltStratum (sX i) (B i) T →
    ∃ T', IsDltStratum (sX (i + 1)) (B (i + 1)) T' ∧
      closure ((f i).base '' T) = closure ((fp i).base '' T')

/-- From the index `M` on, the boundary strata of dimension `< d` miss the flipping and the
flipped loci. -/
private def LowFixed (sX : ∀ i, X i ⟶ Spec (.of k)) (f : ∀ i, X i ⟶ Z i)
    (fp : ∀ i, X (i + 1) ⟶ Z i) (B : ∀ i, QDivisor (X i)) (M d : ℕ) : Prop :=
  ∀ i ≥ M, (∀ T, IsDltStratum (sX i) (B i) T → topologicalKrullDim T < d →
      Disjoint T (exceptionalSet (f i) : Set (X i))) ∧
    (∀ T', IsDltStratum (sX (i + 1)) (B (i + 1)) T' → topologicalKrullDim T' < d →
      Disjoint T' (exceptionalSet (fp i) : Set (X (i + 1))))

/-- The birational transform of a subset of `X i` which is a boundary stratum, chosen among the
boundary strata of `X (i + 1)` with the same closure of images in `Z i`. -/
private noncomputable def nextStratum (sX : ∀ i, X i ⟶ Spec (.of k)) (f : ∀ i, X i ⟶ Z i)
    (fp : ∀ i, X (i + 1) ⟶ Z i) (B : ∀ i, QDivisor (X i)) (i : ℕ) (T : Set (X i)) :
    Set (X (i + 1)) := by
  classical
  exact if h : ∃ T', IsDltStratum (sX (i + 1)) (B (i + 1)) T' ∧
      closure ((f i).base '' T) = closure ((fp i).base '' T') then h.choose else ∅

/-- The successive birational transforms of a subset of `X A`. -/
private noncomputable def trackStratum (sX : ∀ i, X i ⟶ Spec (.of k)) (f : ∀ i, X i ⟶ Z i)
    (fp : ∀ i, X (i + 1) ⟶ Z i) (B : ∀ i, QDivisor (X i)) (A : ℕ) (T : Set (X A)) :
    ∀ j : ℕ, Set (X (A + j))
  | 0 => T
  | j + 1 => nextStratum sX f fp B (A + j) (trackStratum sX f fp B A T j)

/-- The birational transform relation between strata of consecutive models. -/
private def IsTransform (sX : ∀ i, X i ⟶ Spec (.of k)) (f : ∀ i, X i ⟶ Z i)
    (fp : ∀ i, X (i + 1) ⟶ Z i) (B : ∀ i, QDivisor (X i)) (i : ℕ) (T : Set (X i))
    (T' : Set (X (i + 1))) : Prop :=
  IsDltStratum (sX i) (B i) T ∧ IsDltStratum (sX (i + 1)) (B (i + 1)) T' ∧
    closure ((f i).base '' T) = closure ((fp i).base '' T')

variable {sX : ∀ i, X i ⟶ Spec (.of k)} {sZ : ∀ i, Z i ⟶ Spec (.of k)}
  {f : ∀ i, X i ⟶ Z i} {fp : ∀ i, X (i + 1) ⟶ Z i} {K : ∀ i, Divisor (X i)}
  {B : ∀ i, QDivisor (X i)} {M : ℕ}

private theorem isTransform_nextStratum (h : IsTail sX sZ f fp K B M) {i : ℕ} (hi : M ≤ i)
    {T : Set (X i)} (hT : IsDltStratum (sX i) (B i) T) :
    IsTransform sX f fp B i T (nextStratum sX f fp B i T) := by
  classical
  have hex := h.strata_trans i hi T hT
  have : nextStratum sX f fp B i T = hex.choose := dif_pos hex
  rw [this]
  exact ⟨hT, hex.choose_spec.1, hex.choose_spec.2⟩

/-- The generic points of corresponding strata. -/
private theorem IsTransform.exists_genericPoint (h : IsTail sX sZ f fp K B M) {i : ℕ}
    (hi : M ≤ i) {T : Set (X i)} {T' : Set (X (i + 1))} (hTT : IsTransform sX f fp B i T T') :
    ∃ (η : X i) (η' : X (i + 1)), closure {η} = T ∧ closure {η'} = T' ∧
      (f i).base η = (fp i).base η' ∧ (f i).base η ∈ biregularLocus (f i) ∧
      (fp i).base η' ∈ biregularLocus (fp i) := by
  obtain ⟨hT, hT', hcl⟩ := hTT
  obtain ⟨η, hη⟩ := exists_closure_singleton_eq_of_isDltStratum hT
  obtain ⟨η', hη'⟩ := exists_closure_singleton_eq_of_isDltStratum hT'
  refine ⟨η, η', hη, hη', ?_, ?_, ?_⟩
  · rw [← hη, ← hη'] at hcl
    exact map_eq_of_closure_image_eq _ _ hcl
  · exact map_mem_biregularLocus_of_not_closure_subset _ (hη ▸ h.strata i hi T hT)
  · exact map_mem_biregularLocus_of_not_closure_subset _ (hη' ▸ h.strata' i hi T' hT')

/-- Corresponding strata have the same dimension. -/
private theorem IsTransform.topologicalKrullDim_eq (h : IsTail sX sZ f fp K B M) {i : ℕ}
    (hi : M ≤ i) {T : Set (X i)} {T' : Set (X (i + 1))} (hTT : IsTransform sX f fp B i T T') :
    topologicalKrullDim T = topologicalKrullDim T' := by
  obtain ⟨η, η', hη, hη', he, hV, hV'⟩ := hTT.exists_genericPoint h hi
  rw [← hη, ← hη']
  exact topologicalKrullDim_closure_eq_of_map_eq (h.proj i) (h.proj (i + 1)) (h.canon i)
    (h.canon (i + 1)) (f i) (fp i) hV hV' he

/-- A stratum has at most one transform. -/
private theorem IsTransform.unique (h : IsTail sX sZ f fp K B M) {i : ℕ} (hi : M ≤ i)
    {T : Set (X i)} {T₁ T₂ : Set (X (i + 1))} (h₁ : IsTransform sX f fp B i T T₁)
    (h₂ : IsTransform sX f fp B i T T₂) : T₁ = T₂ :=
  eq_of_closure_image_eq (fp i) (isClosed_and_isIrreducible_of_isDltStratum h₁.2.1)
    (isClosed_and_isIrreducible_of_isDltStratum h₂.2.1) (h.strata' i hi T₁ h₁.2.1)
    (h.strata' i hi T₂ h₂.2.1) (h₁.2.2.symm.trans h₂.2.2)

/-- Every stratum of `X (i + 1)` is the transform of a stratum of `X i`. -/
private theorem exists_isTransform_of_isDltStratum (h : IsTail sX sZ f fp K B M) {i : ℕ}
    (hi : M ≤ i) {T' : Set (X (i + 1))} (hT' : IsDltStratum (sX (i + 1)) (B (i + 1)) T') :
    ∃ T, IsTransform sX f fp B i T T' := by
  obtain ⟨η', hη'⟩ := exists_closure_singleton_eq_of_isDltStratum hT'
  have hV' : (fp i).base η' ∈ biregularLocus (fp i) :=
    map_mem_biregularLocus_of_not_closure_subset _ (hη' ▸ h.strata' i hi T' hT')
  have hV : (fp i).base η' ∈ biregularLocus (f i) := by
    rw [biregularLocus_eq_of_isFlipOf (h.flip i)]; exact hV'
  have hT'' : IsDltStratum (sX (i + 1)) (flipTransform (f i) (fp i) (B i)) T' := by
    rw [← h.trans i]; exact hT'
  obtain ⟨T, hT, -, hcl⟩ :=
    exists_isDltStratum_of_mem_biregularLocus (h.flip i) (h.dlt i) hT'' hη' hV hV'
  exact ⟨T, hT, hT', hcl⟩

private theorem trackStratum_spec (h : IsTail sX sZ f fp K B M) {A : ℕ} (hA : M ≤ A)
    {T : Set (X A)} (hT : IsDltStratum (sX A) (B A) T) (j : ℕ) :
    IsTransform sX f fp B (A + j) (trackStratum sX f fp B A T j)
      (trackStratum sX f fp B A T (j + 1)) ∧
      topologicalKrullDim (trackStratum sX f fp B A T j) = topologicalKrullDim T := by
  induction j with
  | zero => exact ⟨isTransform_nextStratum h hA hT, rfl⟩
  | succ j ih =>
    have hdim := ih.1.topologicalKrullDim_eq h (hA.trans (Nat.le_add_right _ _))
    exact ⟨isTransform_nextStratum h (hA.trans (Nat.le_add_right _ _)) ih.1.2.1,
      hdim.symm.trans ih.2⟩

/-- Every stratum of `X (A + j)` is the `j`-th transform of a stratum of `X A`. -/
private theorem exists_trackStratum_eq (h : IsTail sX sZ f fp K B M) {A : ℕ} (hA : M ≤ A)
    (j : ℕ) {T' : Set (X (A + j))} (hT' : IsDltStratum (sX (A + j)) (B (A + j)) T') :
    ∃ T, IsDltStratum (sX A) (B A) T ∧ topologicalKrullDim T = topologicalKrullDim T' ∧
      trackStratum sX f fp B A T j = T' := by
  induction j with
  | zero => exact ⟨T', hT', rfl, rfl⟩
  | succ j ih =>
    obtain ⟨T₁, hT₁⟩ := exists_isTransform_of_isDltStratum h
      (hA.trans (Nat.le_add_right A j)) hT'
    obtain ⟨T, hT, hTd, hTT⟩ := ih hT₁.1
    have hs := trackStratum_spec h hA hT j
    rw [hTT] at hs
    refine ⟨T, hT, ?_, hs.1.unique h (hA.trans (Nat.le_add_right A j)) hT₁⟩
    rw [hTd, hT₁.topologicalKrullDim_eq h (hA.trans (Nat.le_add_right A j))]

/-- **The induced maps of strata.** Along a family of adjunction pairs on the transforms of a
stratum of dimension `d ≤ 2`, once the positive sides contract no prime divisor, the maps
induced by the flips are eventually isomorphisms over `Z`. -/
private theorem eventually_iso_of_family (h : IsTail sX sZ f fp K B M) {A d : ℕ} (hA : M ≤ A)
    (hd : d = 0 ∨ d = 1 ∨ d = 2) {T : Set (X A)} (hT : IsDltStratum (sX A) (B A) T)
    {S : ℕ → Scheme.{0}} [∀ j, IsIntegral (S j)]
    [∀ j, IsLocallyNoetherian (S j)] [∀ j, IsNormal (S j)] {ι : ∀ j, S j ⟶ X (A + j)}
    [∀ j, IsClosedImmersion (ι j)]
    (hrange : ∀ j, Set.range (ι j).base = trackStratum sX f fp B A T j)
    (hSv : ∀ j, IsNormalVariety k (ι j ≫ sX (A + j)))
    (hdimS : ∀ j, topologicalKrullDim (S j) = d)
    (hcorr : ∀ j, (ι j ≫ f (A + j)).base (genericPoint (S j)) =
      (ι (j + 1) ≫ fp (A + j)).base (genericPoint (S (j + 1))))
    {Na : ℕ} (ha : ∀ j ≥ Na, ∀ P : MMP.Mori.PrimeDivisor (S (j + 1)),
      ¬ topologicalKrullDim
          (closure {(ι (j + 1) ≫ fp (A + j)).base P.genericPoint} : Set (Z (A + j))) <
        topologicalKrullDim (closure {P.genericPoint} : Set (S (j + 1)))) :
    ∃ Nb, ∀ j ≥ Nb, ∃ φ : S j ≅ S (j + 1),
      ι j ≫ f (A + j) = φ.hom ≫ ι (j + 1) ≫ fp (A + j) := by
  classical
  have hAj : ∀ j, M ≤ A + j := fun j => hA.trans (Nat.le_add_right _ _)
  have hspec := trackStratum_spec h hA hT
  have hd2 : d ≤ 2 := by rcases hd with rfl | rfl | rfl <;> omega
  have hlft : ∀ j, LocallyOfFiniteType (ι j ≫ sX (A + j)) := fun j =>
    (hSv j).1.toLocallyOfFiniteType
  -- the generic points of the strata
  have hcl : ∀ j, closure {(ι j) (genericPoint (S j))} = trackStratum sX f fp B A T j := by
    intro j
    obtain ⟨η, hη⟩ := exists_closure_singleton_eq_of_isDltStratum (hspec j).1.1
    rw [map_genericPoint_eq_of_range_eq (ι j) ((hrange j).trans hη.symm), hη]
  have hfV : ∀ j, f (A + j) ((ι j) (genericPoint (S j))) ∈ biregularLocus (f (A + j)) := by
    intro j
    exact map_mem_biregularLocus_of_not_closure_subset _
      (by rw [hcl j]; exact h.strata (A + j) (hAj j) _ (hspec j).1.1)
  have hfpV : ∀ j, fp (A + j) ((ι (j + 1)) (genericPoint (S (j + 1)))) ∈
      biregularLocus (fp (A + j)) := by
    intro j
    exact map_mem_biregularLocus_of_not_closure_subset _
      (by rw [hcl (j + 1)]; exact h.strata' (A + j) (hAj j) _ (hspec j).1.2.1)
  have hVeq : ∀ j, biregularLocus (f (A + j)) = biregularLocus (fp (A + j)) := fun j =>
    biregularLocus_eq_of_isFlipOf (h.flip (A + j))
  -- images of the strata
  have hproper : ∀ j, IsProper (ι j ≫ sX (A + j)) := fun j => by
    haveI := h.proj (A + j); infer_instance
  have hsepZ : ∀ j, IsSeparated (sZ (A + j)) := fun j =>
    (h.flip (A + j)).isContraction.isNormalVariety_target.1.toIsSeparated
  have hpa : ∀ j, IsProper (ι j ≫ f (A + j)) := fun j =>
    haveI := hsepZ j
    isProper_comp_of_comp_eq _ _ (h.flip (A + j)).isContraction.comp_eq (hproper j)
  have hpb : ∀ j, IsProper (ι (j + 1) ≫ fp (A + j)) := fun j =>
    haveI := hsepZ j
    isProper_comp_of_comp_eq _ _ (h.flip (A + j)).isSmallMorphism_flip.comp_eq (hproper (j + 1))
  have himg : ∀ j, (f (A + j)).base '' trackStratum sX f fp B A T j =
      (fp (A + j)).base '' trackStratum sX f fp B A T (j + 1) := by
    intro j
    haveI := (h.flip (A + j)).isSmallMorphism.isProper
    haveI := (h.flip (A + j)).isSmallMorphism_flip.isProper
    have h1 : closure ((f (A + j)).base '' trackStratum sX f fp B A T j) =
        (f (A + j)).base '' trackStratum sX f fp B A T j := ((f (A + j)).isClosedMap _
      (isClosed_and_isIrreducible_of_isDltStratum (hspec j).1.1).1).closure_eq
    have h2 : closure ((fp (A + j)).base '' trackStratum sX f fp B A T (j + 1)) =
        (fp (A + j)).base '' trackStratum sX f fp B A T (j + 1) := ((fp (A + j)).isClosedMap _
      (isClosed_and_isIrreducible_of_isDltStratum (hspec j).1.2.1).1).closure_eq
    rw [← h1, ← h2]
    exact (hspec j).1.2.2
  -- fibres through the generic points
  have hfiba : ∀ j x, (ι j ≫ f (A + j)) x = (ι j ≫ f (A + j)) (genericPoint (S j)) →
      x = genericPoint (S j) := fun j _ =>
    eq_of_comp_apply_eq_of_mem_biregularLocus (ι j) (f (A + j)) (hfV j)
  have hfibb : ∀ j x, (ι (j + 1) ≫ fp (A + j)) x =
      (ι (j + 1) ≫ fp (A + j)) (genericPoint (S (j + 1))) → x = genericPoint (S (j + 1)) :=
    fun j _ => eq_of_comp_apply_eq_of_mem_biregularLocus (ι (j + 1)) (fp (A + j)) (hfpV j)
  -- the positive sides are quasi-finite
  have hlqf : ∀ j ≥ Na, LocallyQuasiFinite (ι (j + 1) ≫ fp (A + j)) := by
    intro j hj
    haveI := hpb j
    haveI := hlft (j + 1)
    refine locallyQuasiFinite_of_forall_specializes _ ?_
    refine forall_specializes_eq_of_le_two (sS := ι (j + 1) ≫ sX (A + (j + 1))) (hdimS (j + 1))
      hd2 _ (ι (j + 1) ≫ fp (A + j)).isClosedMap (hfibb j) ?_
    intro x hx hd2' hxc
    set P : MMP.Mori.PrimeDivisor (S (j + 1)) := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx
    have hPx : P.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx
    have hP := ha j hj P
    rw [hPx] at hP
    apply hP
    have h1 : topologicalKrullDim (closure {x} : Set (S (j + 1))) = 1 := by
      rw [topologicalKrullDim_closure_eq_sub (ι (j + 1) ≫ sX (A + (j + 1))) (hdimS (j + 1))
        (m := 1) (by exact_mod_cast hx) (by omega), hd2']
      norm_num
    have hxc' : closure {(ι (j + 1) ≫ fp (A + j)).base x} =
        ({(ι (j + 1) ≫ fp (A + j)).base x} : Set (Z (A + j))) := hxc.closure_eq
    rw [h1, hxc']
    exact lt_of_le_of_lt (topologicalKrullDim_singleton_le_zero _) zero_lt_one
  -- the induced morphisms
  have hg : ∀ j ≥ Na, ∃ g : S j ⟶ S (j + 1), g ≫ ι (j + 1) ≫ fp (A + j) = ι j ≫ f (A + j) := by
    intro j hj
    haveI := hpb j
    haveI := hlqf j hj
    have hV1 := isBiregular_biregularLocus (f (A + j))
    unfold IsBiregular at hV1
    have hV2 := isBiregular_biregularLocus (fp (A + j))
    unfold IsBiregular at hV2
    rw [← hVeq j] at hV2
    set V := biregularLocus (f (A + j)) with hVdef
    let U : (S j).Opens := ι j ⁻¹ᵁ (f (A + j) ⁻¹ᵁ V)
    let c : U.toScheme ⟶ X (A + j + 1) :=
      (ι j ∣_ (f (A + j) ⁻¹ᵁ V)) ≫ (f (A + j) ∣_ V) ≫ inv (fp (A + j) ∣_ V) ≫
        (fp (A + j) ⁻¹ᵁ V).ι
    have hc : c ≫ fp (A + j) = U.ι ≫ ι j ≫ f (A + j) := by
      simp only [c, Category.assoc]
      rw [← morphismRestrict_ι (fp (A + j)) V, IsIso.inv_hom_id_assoc, morphismRestrict_ι,
        morphismRestrict_ι_assoc]
    have hcr : Set.range c.base ⊆ Set.range (ι (j + 1)).base := by
      rintro _ ⟨x, rfl⟩
      rw [hrange (j + 1)]
      have hfx : fp (A + j) (c x) = f (A + j) ((ι j) (U.ι x)) := by
        rw [← Scheme.Hom.comp_apply, hc]; rfl
      have hT : (ι j) (U.ι x) ∈ trackStratum sX f fp B A T j := by
        rw [← hrange j]; exact ⟨_, rfl⟩
      obtain ⟨y, hy, hyf⟩ : f (A + j) ((ι j) (U.ι x)) ∈
          (fp (A + j)).base '' trackStratum sX f fp B A T (j + 1) := by
        rw [← himg j]; exact ⟨_, hT, rfl⟩
      have hxV : f (A + j) ((ι j) (U.ι x)) ∈ biregularLocus (fp (A + j)) := by
        rw [← hVeq j]; exact x.2
      have hcx : c x ∈ fp (A + j) ⁻¹ᵁ biregularLocus (fp (A + j)) := by
        show fp (A + j) (c x) ∈ biregularLocus (fp (A + j))
        rw [hfx]; exact hxV
      have hyx : y ∈ fp (A + j) ⁻¹ᵁ biregularLocus (fp (A + j)) := by
        show (fp (A + j)).base y ∈ biregularLocus (fp (A + j))
        rw [hyf]; exact hxV
      rw [injOn_preimage_biregularLocus (fp (A + j)) hcx hyx (hfx.trans hyf.symm)]
      exact hy
    obtain ⟨u, hu⟩ := exists_lift_of_range_subset (ι (j + 1)) c hcr
    have hU : (U : Set (S j)).Nonempty := ⟨genericPoint (S j), hfV j⟩
    obtain ⟨g, hg, -⟩ := exists_hom_comp_eq_of_locallyQuasiFinite (hSv j).1
      (ι j ≫ f (A + j)) (ι (j + 1) ≫ fp (A + j)) U hU u (by rw [← Category.assoc, hu, hc])
    exact ⟨g, hg⟩
  -- properties of the induced morphisms
  have hgprop : ∀ j (g : S j ⟶ S (j + 1)), g ≫ ι (j + 1) ≫ fp (A + j) = ι j ≫ f (A + j) →
      g ≫ ι (j + 1) ≫ sX (A + j + 1) = ι j ≫ sX (A + j) ∧ IsProper g ∧ IsBirational g ∧
        (∀ x, g x = genericPoint (S (j + 1)) → x = genericPoint (S j)) ∧
        (LocallyQuasiFinite g → IsIso g) ∧ g (genericPoint (S j)) = genericPoint (S (j + 1)) := by
    intro j g hgj
    have hgs : g ≫ ι (j + 1) ≫ sX (A + j + 1) = ι j ≫ sX (A + j) := by
      rw [← (h.flip (A + j)).isSmallMorphism_flip.comp_eq,
        ← (h.flip (A + j)).isContraction.comp_eq, reassoc_of% hgj]
    have hpt : ∀ x, (ι (j + 1) ≫ fp (A + j)) (g x) = (ι j ≫ f (A + j)) x := fun x => by
      rw [← Scheme.Hom.comp_apply, hgj]
    have hg0 : g (genericPoint (S j)) = genericPoint (S (j + 1)) := by
      refine hfibb j _ ?_
      rw [hpt]
      exact hcorr j
    haveI := hpb j
    haveI : IsProper (g ≫ ι (j + 1) ≫ fp (A + j)) := by rw [hgj]; exact hpa j
    haveI : IsProper g := IsProper.of_comp g (ι (j + 1) ≫ fp (A + j))
    have hbir : IsBirational g := by
      refine isBirational_of_comp_eq g _ hgj hg0 ?_
      rw [Scheme.Hom.stalkMap_comp]
      haveI := MMP.isIso_stalkMap_of_mem_biregularLocus (f (A + j)) (hfV j)
      exact ((ι j).stalkMap_surjective (genericPoint (S j))).comp
        (ConcreteCategory.bijective_of_isIso
          ((f (A + j)).stalkMap ((ι j) (genericPoint (S j))))).2
    refine ⟨hgs, inferInstance, hbir, fun x hx => hfiba j x ?_, fun hq => ?_, hg0⟩
    · rw [← hpt, hx, ← hg0, hpt]
    · obtain ⟨-, -, hiso⟩ := MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq k
        (hSv j).1 (hSv (j + 1)).1 g hgs hbir
      exact hiso hq
  -- quasi-finiteness of the induced morphisms with no exceptional curve
  have hgq : ∀ j (g : S j ⟶ S (j + 1)), g ≫ ι (j + 1) ≫ fp (A + j) = ι j ≫ f (A + j) →
      (d = 2 → ¬ ∃ C : (S j).IdealSheafData, IsExceptionalCurve g C) → LocallyQuasiFinite g := by
    intro j g hgj hnoC
    obtain ⟨-, hgp, -, hgf, -, hg0⟩ := hgprop j g hgj
    haveI := hgp
    haveI := hlft j
    refine locallyQuasiFinite_of_forall_specializes _ ?_
    refine forall_specializes_eq_of_le_two (sS := ι j ≫ sX (A + j)) (hdimS j) hd2 g
      g.isClosedMap (fun x hx => hgf x (hx.trans hg0)) ?_
    intro x hx hd2' hxc
    apply hnoC hd2'
    set P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hx
    have hPx : P.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx
    refine ⟨P.idealSheaf, ⟨P.integral, ?_⟩, g x, ?_⟩
    · rw [topologicalKrullDim_eq_of_isClosedImmersion P.idealSheaf.subschemeι,
        Scheme.IdealSheafData.range_subschemeι]
      change topologicalKrullDim (P.support : Set (S j)) = 1
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hPx]
      rw [topologicalKrullDim_closure_eq_sub (ι j ≫ sX (A + j)) (hdimS j) (m := 1)
        (by exact_mod_cast hx) (by omega), hd2']
      norm_num
    · change g.base '' (P.support : Set (S j)) = {g x}
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hPx]
      refine le_antisymm ?_ (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩)
      calc g.base '' closure {x} ⊆ closure (g.base '' {x}) :=
            image_closure_subset_closure_image g.base.hom.continuous
        _ = {g x} := by rw [Set.image_singleton]; exact hxc.closure_eq
  -- choose the morphisms on the tail
  choose gm hgm using fun m : ℕ => hg (Na + m) (Nat.le_add_right _ _)
  have hlow2 : d ≠ 2 → ∃ Nb, ∀ j ≥ Nb, ∃ φ : S j ≅ S (j + 1),
      ι j ≫ f (A + j) = φ.hom ≫ ι (j + 1) ≫ fp (A + j) := by
    -- points and curves: every induced map is an isomorphism
    intro hd2'
    refine ⟨Na, fun j hj => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, j = Na + m := ⟨j - Na, by omega⟩
    have hq := hgq _ (gm m) (hgm m) (fun h2 => absurd h2 hd2')
    haveI := (hgprop _ (gm m) (hgm m)).2.2.2.2.1 hq
    exact ⟨asIso (gm m), (hgm m).symm⟩
  rcases hd with rfl | rfl | rfl
  · exact hlow2 (by norm_num)
  · exact hlow2 (by norm_num)
  · -- surfaces: by the chain bound, eventually no curve is contracted
    obtain ⟨N, hN⟩ := eventually_not_isExceptionalCurve (S := fun m => S (Na + m))
      (sS := fun m => ι (Na + m) ≫ sX (A + (Na + m))) (fun m => hSv _)
      (fun m => by exact_mod_cast hdimS (Na + m)) gm
      (fun m => (hgprop _ (gm m) (hgm m)).1) (fun m => (hgprop _ (gm m) (hgm m)).2.1)
      (fun m => (hgprop _ (gm m) (hgm m)).2.2.1)
    refine ⟨Na + N, fun j hj => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, j = Na + m := ⟨j - Na, by omega⟩
    have hq := hgq _ (gm m) (hgm m) (fun _ => hN m (by omega))
    haveI := (hgprop _ (gm m) (hgm m)).2.2.2.2.1 hq
    exact ⟨asIso (gm m), (hgm m).symm⟩

end Seq

/-! ### Isomorphisms of adjunction pairs -/

/-- The stalk map at the generic point of a composite, read through the extension of function
fields of the first factor. -/
private theorem stalkMap_comp_genericPoint_apply {S T Z : Scheme.{0}} [IsIntegral S]
    [IsIntegral T] (g : S ⟶ T) [IsDominant g] (h : T ⟶ Z)
    (a : Z.presheaf.stalk ((g ≫ h) (genericPoint S))) :
    ((g ≫ h).stalkMap (genericPoint S)).hom a =
      functionFieldMap g (algebraMap (T.presheaf.stalk (g (genericPoint S))) T.functionField
        ((h.stalkMap (g (genericPoint S))).hom a)) := by
  rw [functionFieldMap_algebraMap_stalk g (genericPoint S), Scheme.Hom.stalkMap_comp]
  simp only [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- Germs at equal points have equal images in the function field. -/
private theorem algebraMap_stalkMap_congr {T Z : Scheme.{0}} [IsIntegral T] (h : T ⟶ Z)
    {t₁ t₂ : T} (ht : t₁ = t₂) (hz : h t₁ = h t₂) (a : Z.presheaf.stalk (h t₁)) :
    algebraMap (T.presheaf.stalk t₁) T.functionField ((h.stalkMap t₁).hom a) =
      algebraMap (T.presheaf.stalk t₂) T.functionField
        ((h.stalkMap t₂).hom ((Z.presheaf.stalkCongr (.of_eq hz)).hom.hom a)) := by
  subst ht
  simp [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]

/-- At the generic point, the map from the stalk to the function field is the identity. -/
private theorem algebraMap_genericPoint_apply {T : Scheme.{0}} [IsIntegral T]
    (y : T.presheaf.stalk (genericPoint T)) :
    @algebraMap (T.presheaf.stalk (genericPoint T)) T.functionField _ _
      (AlgebraicGeometry.stalkFunctionFieldAlgebra T (genericPoint T)) y = y := by
  simp only [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The valuation of a prime divisor of a normal variety, as a divisor over it. -/
private theorem valuation_ofPrimeDivisor_apply {k : Type} [Field k] {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) (Q : MMP.Mori.PrimeDivisor Y) (y : Y.functionField) :
    (DivisorOver.ofPrimeDivisor k hY Q).valuation y = Q.divisorialValuation y := by
  change Q.divisorialValuation (functionFieldMap (𝟙 Y) y) = _
  rw [MMP.Mori.functionFieldMap_id_apply]

/-- **Valuations through an isomorphism of strata.** If `a = φ ≫ ψ` for an isomorphism
`φ : S ≅ S'` carrying `P` to `P'`, then `ord_P` and `ord_{P'}` agree on the local ring at the
common image of the generic points. -/
private theorem valuation_comap_stalkMap_eq_of_iso {k : Type} [Field k] {S S' Z : Scheme.{0}}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S']
    [IsNormal S'] {sS : S ⟶ Spec (.of k)} {sS' : S' ⟶ Spec (.of k)}
    (hS : IsNormalVariety k sS) (hS' : IsNormalVariety k sS') (φ : S ≅ S') (ψ : S' ⟶ Z)
    (a : S ⟶ Z) (ha : a = φ.hom ≫ ψ) (hcorr : a (genericPoint S) = ψ (genericPoint S'))
    (P : MMP.Mori.PrimeDivisor S) (P' : MMP.Mori.PrimeDivisor S')
    (hP : φ.hom P.genericPoint = P'.genericPoint) :
    (DivisorOver.ofPrimeDivisor k hS P).valuation.comap (a.stalkMap (genericPoint S)).hom =
      (DivisorOver.ofPrimeDivisor k hS' P').valuation.comap
        ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫ ψ.stalkMap (genericPoint S')).hom := by
  subst ha
  have hgen : φ.hom (genericPoint S) = genericPoint S' := genericPoint_eq_of_isOpenImmersion φ.hom
  have htr : ∀ t : S'.functionField,
      P.divisorialValuation (functionFieldMap φ.hom t) = P'.divisorialValuation t := fun t => by
    have := Oai4C1.valuationOver_eq_of_isIso φ.hom P P' hP
    rw [← this]; rfl
  refine Valuation.ext fun x => ?_
  simp only [Valuation.comap_apply]
  calc (DivisorOver.ofPrimeDivisor k hS P).valuation
        (((φ.hom ≫ ψ).stalkMap (genericPoint S)).hom x)
      = P.divisorialValuation (((φ.hom ≫ ψ).stalkMap (genericPoint S)).hom x) :=
        valuation_ofPrimeDivisor_apply hS P _
    _ = P.divisorialValuation (functionFieldMap φ.hom
          (algebraMap (S'.presheaf.stalk (φ.hom (genericPoint S))) S'.functionField
            ((ψ.stalkMap (φ.hom (genericPoint S))).hom x))) :=
        congrArg _ (stalkMap_comp_genericPoint_apply φ.hom ψ x)
    _ = P'.divisorialValuation
          (algebraMap (S'.presheaf.stalk (φ.hom (genericPoint S))) S'.functionField
            ((ψ.stalkMap (φ.hom (genericPoint S))).hom x)) := htr _
    _ = P'.divisorialValuation ((ψ.stalkMap (genericPoint S')).hom
          ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom.hom x)) :=
        congrArg _ ((algebraMap_stalkMap_congr ψ hgen hcorr x).trans
          (algebraMap_genericPoint_apply _))
    _ = (DivisorOver.ofPrimeDivisor k hS' P').valuation
          (((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫ ψ.stalkMap (genericPoint S')).hom x) :=
        (valuation_ofPrimeDivisor_apply hS' P' _).symm

/-- Through an isomorphism carrying `η_P` to `η_{P'}`, the inverse transform of a divisor has at
`P` the coefficient at `P'`. -/
private theorem inverseTransformDivisor_iso_apply {S S' : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    (φ : S ≅ S') {P : MMP.Mori.PrimeDivisor S} {P' : MMP.Mori.PrimeDivisor S'}
    (hP : φ.hom P.genericPoint = P'.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R S') : inverseTransformDivisor φ.hom D P = D P' := by
  have hV : φ.hom P.genericPoint ∈ biregularLocus φ.hom := by
    have : IsBiregular φ.hom ⊤ := (isBiregular_top_iff φ.hom).mpr inferInstance
    exact le_biregularLocus this trivial
  have h1 : inverseTransformPrimeDivisor φ.hom P' = some P :=
    MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hP hV
  have huniq : ∀ Q, inverseTransformPrimeDivisor φ.hom Q = some P → Q = P' := by
    intro Q hQ
    obtain ⟨h2, -⟩ :=
      MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hQ
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (h2.symm.trans hP)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq h1 huniq _

/-- An isomorphism carries every prime divisor to a prime divisor. -/
private theorem exists_primeDivisor_iso {S S' : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    (φ : S ≅ S') (P : MMP.Mori.PrimeDivisor S) :
    ∃ P' : MMP.Mori.PrimeDivisor S', φ.hom P.genericPoint = P'.genericPoint := by
  have hco : Order.coheight (φ.hom P.genericPoint) = 1 := by
    rw [AlgebraicGeometry.coheight_eq_of_isOpenImmersion φ.hom, P.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco).symm⟩

/-- An isomorphism matching the coefficients of corresponding prime divisors matches the
divisors. -/
private theorem inverseTransformDivisor_eq_of_forall_coeff_eq {S S' : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    (φ : S ≅ S') {BS : QDivisor S} {BS' : QDivisor S'}
    (hb : ∀ (P : MMP.Mori.PrimeDivisor S) (P' : MMP.Mori.PrimeDivisor S'),
      φ.hom P.genericPoint = P'.genericPoint → BS.coeff P = BS'.coeff P') :
    inverseTransformDivisor φ.hom BS' = BS := by
  ext P
  obtain ⟨P', hP'⟩ := exists_primeDivisor_iso φ P
  change inverseTransformDivisor φ.hom BS' P = BS P
  rw [inverseTransformDivisor_iso_apply φ hP']
  exact (hb P P' hP').symm

/-- An isomorphism of strata over `Z` which matches the boundary coefficients of corresponding
prime divisors is an isomorphism of adjunction pairs. -/
private theorem inverseTransformDivisor_eq_of_coeff_eq {k : Type} [Field k] {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {B : QDivisor X}
    {B' : QDivisor X'} {f : X ⟶ Z} {fp : X' ⟶ Z} {S S' : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    {ι : S ⟶ X} {ι' : S' ⟶ X'} {BS : QDivisor S} {BS' : QDivisor S'}
    (hcorr : (ι ≫ f).base (genericPoint S) = (ι' ≫ fp).base (genericPoint S'))
    (φ : S ≅ S') (hφ : ι ≫ f = φ.hom ≫ ι' ≫ fp)
    (hS : IsStratumAdjunctionPair sX B ι BS) (hS' : IsStratumAdjunctionPair sX' B' ι' BS')
    (hb : ∀ (P : MMP.Mori.PrimeDivisor S) (P' : MMP.Mori.PrimeDivisor S'),
      (DivisorOver.ofPrimeDivisor k hS.some.isNormalVariety P).valuation.comap
          ((ι ≫ f).stalkMap (genericPoint S)).hom =
        (DivisorOver.ofPrimeDivisor k hS'.some.isNormalVariety P').valuation.comap
          ((Z.presheaf.stalkCongr (.of_eq hcorr)).hom ≫
            (ι' ≫ fp).stalkMap (genericPoint S')).hom →
      BS.coeff P = BS'.coeff P') :
    inverseTransformDivisor φ.hom BS' = BS :=
  inverseTransformDivisor_eq_of_forall_coeff_eq φ fun P P' hP =>
    hb P P' (valuation_comap_stalkMap_eq_of_iso _ _ φ (ι' ≫ fp) (ι ≫ f) hφ hcorr P P' hP)

section Seq2

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X Z : ℕ → Scheme.{0}}
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  [∀ i, CompactSpace (X i)]
variable {sX : ∀ i, X i ⟶ Spec (.of k)} {sZ : ∀ i, Z i ⟶ Spec (.of k)}
  {f : ∀ i, X i ⟶ Z i} {fp : ∀ i, X (i + 1) ⟶ Z i} {K : ∀ i, Divisor (X i)}
  {B : ∀ i, QDivisor (X i)} {M : ℕ}

/-- **The family step.** Along the transforms of a stratum of dimension `d ≤ 2` of `X A`, once
the strata of dimension `< d` miss the flipping and flipped loci, the chosen
adjunction pairs on the transforms are eventually carried isomorphically across the flips, as
adjunction pairs. -/
private theorem family_stable (h : IsTail sX sZ f fp K B M) {A d : ℕ} (hA : M ≤ A)
    (hlow : LowFixed sX f fp B A d) (hd : d = 0 ∨ d = 1 ∨ d = 2) {T : Set (X A)}
    (hT : IsDltStratum (sX A) (B A) T) (hTd : topologicalKrullDim T = d) :
    ∃ (S : ℕ → Scheme.{0}) (ι : ∀ j, S j ⟶ X (A + j)) (BS : ∀ j, QDivisor (S j)),
      (∀ j, Set.range (ι j).base = trackStratum sX f fp B A T j) ∧
      (∀ j, IsStratumAdjunctionPair (sX (A + j)) (B (A + j)) (ι j) (BS j)) ∧
      ∃ N, ∀ j ≥ N, ∃ φ : S j ≅ S (j + 1),
        ι j ≫ f (A + j) = φ.hom ≫ ι (j + 1) ≫ fp (A + j) ∧
          inverseTransformDivisor φ.hom (BS (j + 1)) = BS j := by
  classical
  have hAj : ∀ j, M ≤ A + j := fun j => hA.trans (Nat.le_add_right _ _)
  have hspec := trackStratum_spec h hA hT
  -- adjunction pairs on the transforms
  have hadj : ∀ j, ∃ (S : Scheme.{0}) (ι : S ⟶ X (A + j)) (BS : QDivisor S),
      Set.range ι.base = trackStratum sX f fp B A T j ∧
        IsStratumAdjunctionPair (sX (A + j)) (B (A + j)) ι BS := fun j =>
    (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair (hspec j).1.1).1.1
  choose S ι BS hrange hS using hadj
  have hSv : ∀ j, IsNormalVariety k (ι j ≫ sX (A + j)) := fun j => (hS j).some.isNormalVariety
  haveI : ∀ j, IsIntegral (S j) := fun j => (hSv j).1.toIsIntegral
  haveI : ∀ j, IsNormal (S j) := fun j => (hSv j).2
  haveI : ∀ j, IsLocallyNoetherian (S j) := fun j => by
    have := (hSv j).1
    exact LocallyOfFiniteType.isLocallyNoetherian (ι j ≫ sX (A + j))
  haveI hιc : ∀ j, IsClosedImmersion (ι j) := fun j => (hS j).some.isClosedImmersion
  -- generic points and dimensions
  have hgen : ∀ j, ∀ η : X (A + j), closure {η} = trackStratum sX f fp B A T j →
      (ι j) (genericPoint (S j)) = η := fun j η hη =>
    map_genericPoint_eq_of_range_eq (ι j) ((hrange j).trans hη.symm)
  have hcorr : ∀ j, (ι j ≫ f (A + j)).base (genericPoint (S j)) =
      (ι (j + 1) ≫ fp (A + j)).base (genericPoint (S (j + 1))) := by
    intro j
    obtain ⟨η, η', hη, hη', he, -, -⟩ := (hspec j).1.exists_genericPoint h (hAj j)
    show f (A + j) ((ι j) (genericPoint (S j))) =
      fp (A + j) ((ι (j + 1)) (genericPoint (S (j + 1))))
    rw [hgen j η hη, hgen (j + 1) η' hη']
    exact he
  have hdimS : ∀ j, topologicalKrullDim (S j) = d := fun j => by
    rw [topologicalKrullDim_eq_of_isClosedImmersion (ι j), hrange j, (hspec j).2, hTd]
  -- the stabilization on the tail from `A`
  obtain ⟨Na, hNa⟩ := MMP.Fourfold.exists_forall_ge_isStratumAdjunctionPair_coeff_eq
    (X := fun j => X (A + j)) (Z := fun j => Z (A + j)) (sX := fun j => sX (A + j))
    (sZ := fun j => sZ (A + j)) (f := fun j => f (A + j)) (fp := fun j => fp (A + j))
    (K := fun j => K (A + j)) (B := fun j => B (A + j)) (fun j => h.proj _) (fun j => h.dlt _)
    (fun j => h.canon _) (fun j => h.flip _) (fun j => h.trans _) (d := d)
    (fun j => (hlow (A + j) (Nat.le_add_right _ _)).1)
    (fun j => (hlow (A + j) (Nat.le_add_right _ _)).2)
    (S := S) (ι := ι) (BS := BS) hS (fun j => (hdimS j).le) hcorr
  -- the induced maps of strata are eventually isomorphisms
  obtain ⟨Nb, hNb⟩ := eventually_iso_of_family h hA hd hT hrange hSv hdimS hcorr
    (Na := Na) (fun j hj => (hNa j hj).1)
  refine ⟨S, ι, BS, hrange, hS, max Na Nb, fun j hj => ?_⟩
  obtain ⟨φ, hφ⟩ := hNb j (le_of_max_le_right hj)
  exact ⟨φ, hφ, inverseTransformDivisor_eq_of_coeff_eq (hcorr j) φ hφ (hS j) (hS (j + 1))
    ((hNa j (le_of_max_le_left hj)).2)⟩

/-- Along the transforms of a stratum of dimension `d ≤ 2` of `X A`, once the strata of
dimension `< d` miss the flipping and flipped loci, the flips are eventually isomorphisms
near the transforms
(`MMP.Fourfold.IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair`). -/
private theorem family_eventually_disjoint (h : IsTail sX sZ f fp K B M) {A d : ℕ} (hA : M ≤ A)
    (hlow : LowFixed sX f fp B A d) (hd : d = 0 ∨ d = 1 ∨ d = 2) {T : Set (X A)}
    (hT : IsDltStratum (sX A) (B A) T) (hTd : topologicalKrullDim T = d) :
    ∃ N, ∀ j ≥ N,
      Disjoint (trackStratum sX f fp B A T j : Set (X (A + j)))
        (exceptionalSet (f (A + j)) : Set (X (A + j))) ∧
      Disjoint (trackStratum sX f fp B A T (j + 1) : Set (X (A + j + 1)))
        (exceptionalSet (fp (A + j)) : Set (X (A + j + 1))) := by
  obtain ⟨S, ι, BS, hrange, hS, N, hN⟩ := family_stable h hA hlow hd hT hTd
  have hAj : ∀ j, M ≤ A + j := fun j => hA.trans (Nat.le_add_right _ _)
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨φ, hφ, hφB⟩ := hN j hj
  have hB' : B (A + (j + 1)) = flipTransform (f (A + j)) (fp (A + j)) (B (A + j)) :=
    h.trans (A + j)
  have hS' := hS (j + 1)
  rw [hB'] at hS'
  have key := IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair (h.proj (A + j))
    (h.proj (A + j + 1)) (h.canon (A + j)) (h.dlt (A + j)) (hB' ▸ h.dlt (A + j + 1))
    (h.flip (A + j)) (h.strata (A + j) (hAj j)) (by rw [← hB']; exact h.strata' (A + j) (hAj j))
    (hS j) hS' φ hφ hφB
  rw [hrange j, hrange (j + 1)] at key
  exact key

/-- The zero-dimensional strata: a point not contained in the exceptional set misses it. -/
private theorem lowFixed_one (h : IsTail sX sZ f fp K B M) : LowFixed sX f fp B M 1 := by
  intro i hi
  have key : ∀ {Y W : Scheme.{0}} (g : Y ⟶ W) {T : Set Y}, (∃ η, closure {η} = T) →
      topologicalKrullDim T < ((1 : ℕ) : WithBot ℕ∞) → ¬ T ⊆ (exceptionalSet g : Set Y) →
      Disjoint T (exceptionalSet g : Set Y) := by
    intro Y W g T ⟨η, hη⟩ hd hT
    subst hη
    have h1 : closure {η} = ({η} : Set Y) :=
      eq_singleton_of_topologicalKrullDim_lt_one (by exact_mod_cast hd)
    rw [h1] at hT ⊢
    exact Set.disjoint_singleton_left.mpr fun hη => hT (Set.singleton_subset_iff.mpr hη)
  exact ⟨fun T hT hd => key _ (exists_closure_singleton_eq_of_isDltStratum hT) hd
      (h.strata i hi T hT),
    fun T hT hd => key _ (exists_closure_singleton_eq_of_isDltStratum hT) hd
      (h.strata' i hi T hT)⟩

/-- **The inductive step.** If the strata of dimension `< d` are eventually fixed, `d = 1, 2`,
then so are the strata of dimension `< d + 1`. -/
private theorem exists_lowFixed_succ (h : IsTail sX sZ f fp K B M) {d M' : ℕ}
    (hd : d = 1 ∨ d = 2) (hlow : LowFixed sX f fp B M' d) :
    ∃ N, LowFixed sX f fp B N (d + 1) := by
  classical
  set A := max M M'
  have hAM : M ≤ A := le_max_left _ _
  have hlowA : LowFixed sX f fp B A d := fun i hi => hlow i ((le_max_right _ _).trans hi)
  have hd' : d = 0 ∨ d = 1 ∨ d = 2 := Or.inr hd
  have hfam : ∀ T : Set (X A), ∃ N, IsDltStratum (sX A) (B A) T →
      topologicalKrullDim T = d → ∀ j ≥ N,
        Disjoint (trackStratum sX f fp B A T j : Set (X (A + j)))
          (exceptionalSet (f (A + j)) : Set (X (A + j))) ∧
        Disjoint (trackStratum sX f fp B A T (j + 1) : Set (X (A + j + 1)))
          (exceptionalSet (fp (A + j)) : Set (X (A + j + 1))) := by
    intro T
    by_cases hT : IsDltStratum (sX A) (B A) T ∧ topologicalKrullDim T = d
    · obtain ⟨N, hN⟩ := family_eventually_disjoint h hAM hlowA hd' hT.1 hT.2
      exact ⟨N, fun _ _ => hN⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hT⟩
  choose Nf hNf using hfam
  set 𝒯 := (finite_setOf_isDltStratum (sX := sX A) (B A)).toFinset
  set N₀ := 𝒯.sup Nf
  refine ⟨A + N₀, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = A + j := ⟨i - A, by omega⟩
  have hj : N₀ ≤ j := by omega
  have hNj : ∀ T, IsDltStratum (sX A) (B A) T → Nf T ≤ j := fun T hT =>
    le_trans (Finset.le_sup (f := Nf) (by simpa [𝒯] using hT)) hj
  refine ⟨fun T' hT' hd' => ?_, fun T' hT' hd' => ?_⟩
  · rcases lt_or_eq_of_lt_natCast_add_one hd' with hlt | heq
    · exact (hlowA (A + j) (Nat.le_add_right _ _)).1 T' hT' hlt
    · obtain ⟨T, hT, hTd, rfl⟩ := exists_trackStratum_eq h hAM j hT'
      exact (hNf T hT (hTd.trans heq) j (hNj T hT)).1
  · rcases lt_or_eq_of_lt_natCast_add_one hd' with hlt | heq
    · exact (hlowA (A + j) (Nat.le_add_right _ _)).2 T' hT' hlt
    · obtain ⟨T, hT, hTd, hTT⟩ := exists_trackStratum_eq h hAM (j + 1) hT'
      have := (hNf T hT (hTd.trans heq) j (hNj T hT)).2
      rw [hTT] at this
      exact this

/-- A component of `⌊B⌋` is a boundary stratum of dimension two. -/
private theorem isDltStratum_support_and_dim (h : IsTail sX sZ f fp K B M) (i : ℕ)
    (P : MMP.Mori.PrimeDivisor (X i)) (hP : 1 ≤ (B i).coeff P) :
    IsDltStratum (sX i) (B i) (P.support : Set (X i)) ∧
      topologicalKrullDim (P.support : Set (X i)) < ((2 + 1 : ℕ) : WithBot ℕ∞) := by
  refine ⟨isDltStratum_support (h.dlt i) P hP, ?_⟩
  have h3 := topologicalKrullDim_closure_add_coheight (h.proj i) (h.canon i) P.genericPoint
  rw [P.coheight_genericPoint] at h3
  have h4 : topologicalKrullDim (closure {P.genericPoint} : Set (X i)) = ((3 - 1 : ℕ) : _) :=
    eq_natCast_sub_of_add_eq (by norm_num) (by exact_mod_cast h3)
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, h4]
  exact_mod_cast (by norm_num : 3 - 1 < 2 + 1)

end Seq2

/-- Every pair of the sequence is dlt, and from some index on the strata are birational. -/
private theorem exists_isTail {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : ℕ → Scheme.{0}}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    [∀ i, CompactSpace (X i)]
    {sX : ∀ i, X i ⟶ Spec (.of k)} {sZ : ∀ i, Z i ⟶ Spec (.of k)}
    {f : ∀ i, X i ⟶ Z i} {fp : ∀ i, X (i + 1) ⟶ Z i}
    {K : ∀ i, Divisor (X i)} {B : ∀ i, QDivisor (X i)}
    (hX : ∀ i, MMP.Mori.IsProjectiveVariety k (sX i))
    (hB0 : MMP.Intersection.IsDltPair (sX 0) (B 0))
    (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 3)
    (hflip : ∀ i, IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i))
    (hB : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i)) :
    ∃ M, IsTail sX sZ f fp K B M := by
  have hdlt : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i) := by
    intro i
    induction i with
    | zero => exact hB0
    | succ i ih => rw [hB i]; exact isDltPair_flipTransform (hK i) (hflip i) ih
  obtain ⟨M, hM⟩ := exists_forall_ge_not_subset_exceptionalSet_of_isDltStratum (L := ⊤)
    (hX 0) hB0 (fun i _ => hK i) (fun i _ => hflip i) (fun i _ => hB i)
  exact ⟨M, hX, hdlt, hK, hflip, hB, fun i hi => (hM i hi (ENat.coe_lt_top _)).1,
    fun i hi => (hM i hi (ENat.coe_lt_top _)).2.1, fun i hi => (hM i hi (ENat.coe_lt_top _)).2.2⟩

end MMP.Fold06.ThmFourfoldProjectiveDltThreefoldSpecialTermination

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

open MMP.Fold06.ThmFourfoldProjectiveDltThreefoldSpecialTermination in
/-- **Special termination for projective dlt threefolds.** Let `X 0` be a `ℚ`-factorial
projective threefold over an algebraically closed field of characteristic zero with a dlt boundary
`B 0`, and for every `i` let `f i : X i ⟶ Z i` be the contraction of a `(K i + B i)`-negative
extremal ray `R i`, with `K i` a canonical divisor, and `fp i : X (i + 1) ⟶ Z i` its
`(K i + B i)`-flip, with `B (i + 1) = (fp i)⁻¹_* (f i)_* (B i)` and all `X i` projective. Then
there is `N` such that for every `i ≥ N`, every component of `⌊B i⌋` is disjoint from `Ex(f i)`
and every component of `⌊B (i + 1)⌋` is disjoint from `Ex(fp i)`. -/
@[mmp "thm_fourfold_projective_dlt_threefold_special_termination"]
public theorem exists_forall_ge_disjoint_exceptionalSet_of_isFlipOf {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : ℕ → Scheme.{0}}
    [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    [∀ i, CompactSpace (X i)]
    {sX : ∀ i, X i ⟶ Spec (.of k)} {sZ : ∀ i, Z i ⟶ Spec (.of k)}
    {f : ∀ i, X i ⟶ Z i} {fp : ∀ i, X (i + 1) ⟶ Z i}
    {K : ∀ i, Divisor (X i)} {B : ∀ i, QDivisor (X i)}
    {R : ∀ i, Set (NumericalCurveClasses (sX i))}
    (hX : ∀ i, Mori.IsProjectiveVariety k (sX i))
    (_hQ : IsQFactorial (sX 0))
    (hB0 : MMP.Intersection.IsDltPair (sX 0) (B 0))
    (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 3)
    (_hR : ∀ i, IsNegativeExtremalRayOf (sX i) (Divisor.toQDivisor (K i) + B i) (R i))
    (_hf : ∀ i, IsContractionOfRay (sX i) (sZ i) (R i) (f i))
    (hflip : ∀ i, IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i))
    (hB : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i)) :
    ∃ N : ℕ, ∀ i ≥ N,
      (∀ P : MMP.Mori.PrimeDivisor (X i), 1 ≤ (B i).coeff P →
        Disjoint (P.support : Set (X i)) (exceptionalSet (f i) : Set (X i))) ∧
      (∀ P : MMP.Mori.PrimeDivisor (X (i + 1)), 1 ≤ (B (i + 1)).coeff P →
        Disjoint (P.support : Set (X (i + 1))) (exceptionalSet (fp i) : Set (X (i + 1)))) := by
  obtain ⟨M, hM⟩ := exists_isTail hX hB0 hK hflip hB
  obtain ⟨N₁, h₁⟩ := exists_lowFixed_succ hM (Or.inl rfl) (lowFixed_one hM)
  obtain ⟨N₂, h₂⟩ := exists_lowFixed_succ hM (Or.inr rfl) h₁
  refine ⟨N₂, fun i hi => ⟨fun P hP => ?_, fun P hP => ?_⟩⟩
  · obtain ⟨hS, hd⟩ := isDltStratum_support_and_dim hM i P hP
    exact (h₂ i hi).1 _ hS hd
  · obtain ⟨hS, hd⟩ := isDltStratum_support_and_dim hM (i + 1) P hP
    exact (h₂ i hi).2 _ hS hd

end MMP.Fourfold
