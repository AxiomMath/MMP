module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic
public import MMP.AlgebraicGeometry.Divisor.SNC
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Basic
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.Surface.CastelnuovoContraction
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalDivisorSupport
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.PairClasses
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
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
import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
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
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.Resolution.CommonNormalModel
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# Discrepancies of snc pairs and log resolutions

Let `X` be a smooth variety of dimension `n ≥ 2` over a perfect field and `Δ = ∑ aᵢ Dᵢ` a
`ℚ`-divisor with `∑ Dᵢ` a simple normal crossing divisor and every `aᵢ ≤ 1`. Then
`discrep(X, Δ) = min {min_{i ≠ j, Dᵢ ∩ Dⱼ ≠ ∅} (1 - aᵢ - aⱼ), minᵢ (1 - aᵢ), 1}`. The upper bound
comes from blowing up points of codimension two with prescribed components through them; the
lower bound from an estimate on logarithmic forms at the center of an exceptional divisor.

From this formula: an snc pair with coefficients `< 1` is klt; a dlt pair is lc; along an snc
divisor `∑_{G ∈ S} G` the log discrepancy satisfies `a(E, X, Δ) + 1 ≥ ∑ (1 - a_G) ord_E(G)`; and a
log resolution `f : Y ⟶ X` computes `discrep(X, Δ)` from the discrepancies of the `f`-exceptional
prime divisors, and bounds the discrepancies centred in a closed subset uniformly away from `-1`.
The Kollár–Mori dlt and lc predicates are compared with the background ones, and a surface germ
is smooth exactly when its minimal resolution has no exceptional curve.

## Main results

* `MMP.Mori.discrep_eq_of_isSNC`: the discrepancy of an snc pair on a smooth variety.
* `MMP.Mori.exists_isExceptional_isDiscrepancy_eq_one_sub_sub`: an exceptional divisor over a
  codimension two stratum of an snc divisor, of discrepancy `1 - a_E - a_F`;
  `MMP.Mori.exists_isExceptional_isDiscrepancy_eq_one_sub_sub_of_mem` takes the stratum through
  a given point of `E ∩ F`.
* `MMP.Mori.isKltPair_of_isSNC`: snc pairs with coefficients `< 1` are klt.
* `MMP.Mori.IsDltPair.isLcPair`, `MMP.Mori.IsDltPair.isLcPair_of_two_le`: dlt pairs are lc.
* `MMP.Mori.sum_le_add_one_of_isSNC`: the lower bound for log discrepancies along an snc divisor.
* `MMP.Mori.discrep_eq_min_of_isLogResolution`: the discrepancy from a log resolution.
* `MMP.Mori.exists_pos_forall_le_discrepancy_of_isLogResolution`: a uniform lower bound for the
  discrepancies of divisors with center in a closed subset.
* `MMP.Mori.mem_smoothLocus_iff_forall_not_isExceptionalCurve`: a surface germ is smooth iff its
  minimal resolution has no exceptional curve.
* `MMP.Threefold.Bridges.isDltPair_iff_isDltPair`: the background and Kollár–Mori dlt predicates
  agree.
* `MMP.Threefold.Bridges.isLogCanonicalPair_iff_isLcPair`: the background lc predicate is the
  Kollár–Mori one with `0 ≤ Δ ≤ 1`.

## Implementation notes

The lower bound in `MMP.Mori.discrep_eq_of_isSNC` is proved at the center of the exceptional
divisor, by the estimate on logarithmic forms, rather than by Kollár–Mori's induction on the
number of blow-ups needed to reach it. Kollár–Mori work over an algebraically closed field of
characteristic zero; the snc formula, and the step from dlt to lc, use only that the ground field
is perfect, which makes the differentials of a regular system of parameters extend to a basis of
the differentials of the local ring.

Minima of discrepancies are infima in `EReal`, where `MMP.Mori.discrep` takes its values, and a
discrepancy `a(E, X, Δ)` is the predicate `MMP.Mori.IsDiscrepancy`.

The Kollár–Mori predicates depend on a canonical divisor `K`, which fixes the dimension `n`; the
background predicate `MMP.Intersection.IsDltPair` does not, and the comparison holds for every
canonical divisor `K`. Background log discrepancies are defined only for proper models, so a
divisor over `X` is first replaced by a proper model with the same valuation (Nagata
compactification followed by normalization).

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.25, 2.31(3),
  2.32(2), 2.37, 2.40, 4.5
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

universe u

namespace MMP.Mori

/-! ### Exceptional divisors and smooth opens -/

/-- A divisor over a normal variety is exceptional if and only if its center has codimension at
least two. -/
public theorem DivisorOver.isExceptional_iff_two_le_coheight {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (D : DivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

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
  exact_mod_cast ((DivisorOver.isExceptional_iff_two_le_coheight hX D).mp hD).trans
    (WithBot.coe_le_coe.mp this)

/-- An open subscheme contained in the smooth locus of `s` is smooth. -/
public theorem isSmoothScheme_ι_of_le_smoothLocus {Y : Scheme.{u}} {k : Type u} [Field k]
    {s : Y ⟶ Spec (.of k)} {V : Y.Opens} (hV : V ≤ smoothLocus s) :
    IsSmoothScheme (V.ι ≫ s) := by
  rw [IsSmoothScheme, eq_top_iff]
  intro x _
  obtain ⟨W, hxW, hW⟩ := mem_smoothLocus_iff.1 (hV x.2 : V.ι x ∈ smoothLocus s)
  refine mem_smoothLocus_iff.2 ⟨V.ι ⁻¹ᵁ W, hxW, ?_⟩
  have : Smooth (W.ι ≫ s) := hW
  rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
  infer_instance

/-- A smooth open subscheme lies in the smooth locus, for `s` locally of finite type over a
field. -/
public theorem le_smoothLocus_of_isSmoothScheme_ι {Y : Scheme.{u}} {k : Type u} [Field k]
    {s : Y ⟶ Spec (.of k)} [LocallyOfFiniteType s] {V : Y.Opens}
    (hV : IsSmoothScheme (V.ι ≫ s)) : V ≤ smoothLocus s := by
  have : LocallyOfFinitePresentation (V.ι ≫ s) := inferInstance
  exact le_smoothLocus _ ((isSmoothScheme_iff _).mp hV)

/-- The inclusion `U.ι` of an open subscheme, restricted over `U`, is an isomorphism. -/
public theorem isIso_ι_restrict_self {X : Scheme.{u}} (U : X.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := by
    constructor
    intro y
    let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
    rw [morphismRestrict_ι] at this
    exact this.symm
  exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)

/-- The inverse transform of a divisor along the inclusion of an open subscheme is its
restriction. -/
private theorem inverseTransformDivisor_ι_eq_restrictOpen {X : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] (U : X.Opens) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor U.ι B = B.restrictOpen U := by
  have hbir : ∀ x : U.toScheme, U.ι x ∈ biregularLocus U.ι := fun x =>
    le_biregularLocus (isIso_ι_restrict_self U)
      (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩)
  refine Finsupp.ext fun W => ?_
  refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (E := OpenWeilRestriction.primeDivisorMap U.ι W)
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W).symm (hbir _))
    (fun E' hE' => ?_) B).trans rfl
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1]

/-- The support of `∑_{E ∈ S} E` is `S`. -/
private theorem mem_support_sum_single {X : Scheme.{u}} (S : Finset (MMP.Mori.PrimeDivisor X))
    (G : MMP.Mori.PrimeDivisor X) :
    G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ↔ G ∈ S := by
  classical
  rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-! ### Blowing up a point of codimension two -/

/-- If `π` generates the prime of `η_Γ` in `𝒪_{X,x}`, then `π` has order one along `Γ`. -/
private theorem ord_eq_one_of_primeOfSpecializes_eq_span
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {x : X}
    {Γ : MMP.Mori.PrimeDivisor X} (hsp : Γ.genericPoint ⤳ x) {π : X.presheaf.stalk x}
    (hqπ : MMP.Intersection.primeOfSpecializes hsp = Ideal.span {π})
    (hπK : algebraMap Γ.localRing X.functionField ((X.presheaf.stalkSpecializes hsp).hom π) ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField
      ((X.presheaf.stalkSpecializes hsp).hom π)) Γ.genericPoint = 1 := by
  have := Γ.isDiscreteValuationRing_localRing
  let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
  have := MMP.Intersection.isLocalization_stalkSpecializes hsp
  have hmax : IsLocalRing.maximalIdeal Γ.localRing =
      Ideal.span {(X.presheaf.stalkSpecializes hsp).hom π} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (MMP.Intersection.primeOfSpecializes hsp)
      (X.presheaf.stalk Γ.genericPoint), hqπ, Ideal.map_span, Set.image_singleton]
    rfl
  have hirr : Irreducible ((X.presheaf.stalkSpecializes hsp).hom π) :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
      (fun h => by rw [h, map_zero] at hπK; exact hπK rfl) hmax
  rw [Scheme.ord_eq_iff Γ.coheight_genericPoint hπK]
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le Γ.coheight_genericPoint.le
  exact Ring.ordFrac_irreducible hirr

/-- If `π` generates the prime of `η_Γ` in `𝒪_{X,x}` and is not a unit at `η_{Γ'}`, then
`Γ' = Γ`. -/
private theorem eq_of_primeOfSpecializes_eq_span_of_not_isUnit
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {x : X}
    {Γ Γ' : MMP.Mori.PrimeDivisor X} (hsp : Γ.genericPoint ⤳ x) (hsp' : Γ'.genericPoint ⤳ x)
    {π : X.presheaf.stalk x} (hqπ : MMP.Intersection.primeOfSpecializes hsp = Ideal.span {π})
    (hnu : ¬IsUnit ((X.presheaf.stalkSpecializes hsp').hom π)) : Γ' = Γ := by
  have hle : MMP.Intersection.primeOfSpecializes hsp ≤
      MMP.Intersection.primeOfSpecializes hsp' := by
    rw [hqπ, Ideal.span_singleton_le_iff_mem]
    change (X.presheaf.stalkSpecializes hsp').hom π ∈ IsLocalRing.maximalIdeal _
    exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h1 := MMP.Intersection.specializes_of_primeOfSpecializes_le hsp hsp' hle
  by_contra hne
  have hle : Γ'.genericPoint ≤ Γ.genericPoint := h1
  have hlt : Γ'.genericPoint < Γ.genericPoint := lt_of_le_not_ge hle fun h =>
    hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (Specializes.antisymm (show Γ'.genericPoint ⤳ Γ.genericPoint from h) h1).eq)
  have h2 := Order.coheight_add_one_le hlt
  rw [Γ.coheight_genericPoint, Γ'.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

open scoped Classical in
/-- Local equations of the prime divisors through a point with regular local ring: the local
ring there is factorial. -/
private theorem exists_localEquation
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (x : X) (hreg : IsRegularLocalRing (X.presheaf.stalk x)) (Γ : MMP.Mori.PrimeDivisor X)
    (hΓ : x ∈ Γ.support) :
    ∃ π : X.presheaf.stalk x, π ≠ 0 ∧
      Γ.idealSheaf.stalkIdeal x = Ideal.span {π} ∧
      ∀ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support →
        X.ord (algebraMap _ X.functionField π) Γ'.genericPoint = if Γ' = Γ then 1 else 0 := by
  have := IsRegularLocalRing.uniqueFactorizationMonoid (X.presheaf.stalk x)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
  have hsp : Γ.genericPoint ⤳ x := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
  set q := MMP.Intersection.primeOfSpecializes hsp with hq
  -- the prime of `η_Γ` has height one
  have hq1 : q.height = 1 := by
    let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height q (X.presheaf.stalk Γ.genericPoint)
    rw [ringKrullDim_stalk_eq_coheight, Γ.coheight_genericPoint] at e
    exact_mod_cast e.symm
  -- the stalk of the ideal of `Γ`
  set I := IdealSheafData.stalk Γ.idealSheaf x with hI
  have hxs : x ∈ Γ.idealSheaf.support := hΓ
  have hIp : I.IsPrime := by
    have := Γ.integral
    obtain ⟨y, hy⟩ : x ∈ Set.range Γ.idealSheaf.subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    rw [hI, ← hy, ← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact RingHom.ker_isPrime _
  have hI0 : I ≠ ⊥ := by
    intro h0
    have := Γ.isDiscreteValuationRing_localRing
    have hmap := MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes Γ.idealSheaf hsp
    rw [MMP.Resolution.Aux.stalk_idealSheaf_genericPoint, ← hI, h0, Ideal.map_bot] at hmap
    exact IsDiscreteValuationRing.not_a_field _ hmap
  have hIq : I ≤ q :=
    (MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes Γ.idealSheaf hsp).mp
      (MMP.Positivity.PrimeDivisor.genericPoint_mem_support' Γ)
  obtain ⟨π, hπI, hπ⟩ := hIp.exists_mem_prime_of_ne_bot hI0
  have hqπ : q = Ideal.span {π} := Ideal.eq_span_singleton_of_height_eq_one hq1 (hIq hπI) hπ
  have hIπ : I = Ideal.span {π} :=
    le_antisymm (hqπ ▸ hIq) ((Ideal.span_singleton_le_iff_mem _).mpr hπI)
  refine ⟨π, hπ.ne_zero, by rwa [Scheme.IdealSheafData.stalkIdeal_eq_stalk], fun Γ' hΓ' => ?_⟩
  have hsp' : Γ'.genericPoint ⤳ x :=
    MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ' hΓ'
  rw [← MMP.Mori.algebraMap_stalkSpecializes hsp' π]
  have hπK : algebraMap Γ'.localRing X.functionField
      ((X.presheaf.stalkSpecializes hsp').hom π) ≠ 0 := by
    rw [MMP.Mori.algebraMap_stalkSpecializes hsp' π]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
  split_ifs with hΓΓ'
  · subst hΓΓ'
    exact ord_eq_one_of_primeOfSpecializes_eq_span hsp' hqπ hπK
  · exact Γ'.ord_algebraMap_of_isUnit <| not_not.mp fun hnu =>
      hΓΓ' (eq_of_primeOfSpecializes_eq_span_of_not_isUnit hsp hsp' hqπ hnu)

/-- Over a perfect field, the smooth points are the points with regular local ring. -/
private theorem mem_smoothLocus_iff_isRegularLocalRing {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] (y : Y) :
    y ∈ smoothLocus s ↔ IsRegularLocalRing (Y.presheaf.stalk y) := by
  rw [MMP.Mori.mem_smoothLocus_iff, ← InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp]
  exact Set.ext_iff.mp (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k s) y

/-- Over a perfect field, a scheme is smooth when all its local rings are regular. -/
private theorem isSmoothScheme_of_forall_isRegularLocalRing {k : Type u} [Field k]
    [PerfectField k] {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (h : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)) : IsSmoothScheme s :=
  eq_top_iff.mpr fun y _ => (mem_smoothLocus_iff_isRegularLocalRing s y).mpr (h y)

/-- Regularity of a local ring is read through an open immersion. -/
private theorem isRegularLocalRing_of_isOpenImmersion {P Y : Scheme.{u}} (j : P ⟶ Y)
    [IsOpenImmersion j] (p : P) (h : IsRegularLocalRing (Y.presheaf.stalk (j p))) :
    IsRegularLocalRing (P.presheaf.stalk p) := by
  have : IsIso (j.stalkMap p) := inferInstanceAs (IsIso (j.toLRSHom.stalkMap p))
  exact IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap p)).commRingCatIsoToRingEquiv

/-- The generic point of the reduced subscheme on `V` is the generic point of `V`. -/
private theorem subschemeι_genericPoint_vanishingIdeal {X : Scheme.{u}} (V : IrreducibleCloseds X)
    [IsIntegral (Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds X)).subscheme] :
    (Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds X)).subschemeι
      (genericPoint _) = V.isIrreducible.genericPoint := by
  have h1 : IsGenericPoint ((Scheme.IdealSheafData.vanishingIdeal
      (⟨V, V.isClosed⟩ : Closeds X)).subschemeι (genericPoint _)) (V : Set X) := by
    change closure _ = _
    rw [MMP.Resolution.closure_subschemeι_genericPoint,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have h2 := V.isIrreducible.isGenericPoint_genericPoint_closure
  rw [V.isClosed.closure_eq] at h2
  exact h1.eq h2

/-- A point of an open subscheme has the same codimension there as in the ambient scheme. -/
private theorem coheight_opens_ι {X : Scheme.{u}} {U : X.Opens} (x : U.toScheme) :
    Order.coheight x = Order.coheight (U.ι x) := by
  have h1 := ringKrullDim_stalk_eq_coheight x
  rw [ringKrullDim_eq_of_ringEquiv (U.stalkIso x).commRingCatIsoToRingEquiv] at h1
  change ringKrullDim (X.presheaf.stalk (U.ι x)) = _ at h1
  rw [ringKrullDim_stalk_eq_coheight] at h1
  exact_mod_cast h1.symm

/-- Over a perfect field, the restriction to `U` of a closed subscheme `Z` is smooth when every
point of `Z` lying in `U` is a smooth point of `Z`. -/
private theorem isSmoothScheme_comap_ι {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (Z : X.IdealSheafData) (U : X.Opens)
    (hU : ∀ z, Z.subschemeι z ∈ U → z ∈ smoothLocus (Z.subschemeι ≫ sX)) :
    IsSmoothScheme ((Z.comap U.ι).subschemeι ≫ U.ι ≫ sX) := by
  have e : (Z.comap U.ι).subschemeι ≫ U.ι = (Z.comapIso U.ι).hom ≫
      Limits.pullback.snd U.ι Z.subschemeι ≫ Z.subschemeι := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Limits.pullback.condition]
  refine isSmoothScheme_of_forall_isRegularLocalRing _ fun y => ?_
  set j := (Z.comapIso U.ι).hom ≫ Limits.pullback.snd U.ι Z.subschemeι with hj
  have hjy : Z.subschemeι (j y) = U.ι ((Z.comap U.ι).subschemeι y) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hj, Category.assoc, ← e]
  exact isRegularLocalRing_of_isOpenImmersion j y
    ((mem_smoothLocus_iff_isRegularLocalRing (Z.subschemeι ≫ sX) _).mp
      (hU _ (hjy ▸ ((Z.comap U.ι).subschemeι y).2)))

/-- **A smooth neighbourhood of `η_V` in which `V` is smooth.** If `X` is a variety over a
perfect field, `V ⊆ X` an irreducible closed subset with generic point `x` of coheight two and
`𝒪_{X,x}` regular, there is an open `U ∋ x` such that `U` and `V ∩ U` (with its reduced
structure, the inverse image of that of `V`) are smooth over `k`, and `V ∩ U` has codimension
two in `U` with generic point `x`. -/
private theorem exists_smoothBlowup {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsVariety k sX) (V : IrreducibleCloseds X) (x : X)
    (hx : x = V.isIrreducible.genericPoint)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) (hcod : Order.coheight x = 2) :
    ∃ (U : X.Opens) (_ : x ∈ U) (I : U.toScheme.IdealSheafData)
      (_ : MMP.Resolution.IsSmoothBlowup (U.ι ≫ sX) I) (hirr : IsIrreducible (I.support : Set U)),
      U.ι hirr.genericPoint = x ∧
        codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) = 2 := by
  have : LocallyOfFiniteType sX := hX.toLocallyOfFiniteType
  set Z := Scheme.IdealSheafData.vanishingIdeal (⟨V, V.isClosed⟩ : Closeds X) with hZ
  have hZsupp : (Z.support : Set X) = V := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have : IsIntegral Z.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ V.isIrreducible
  set ζ := genericPoint Z.subscheme with hζ
  have hζx : Z.subschemeι ζ = x := hx ▸ subschemeι_genericPoint_vanishingIdeal V
  set S := smoothLocus (Z.subschemeι ≫ sX) with hS
  have hζS : ζ ∈ S := (mem_smoothLocus_iff_isRegularLocalRing _ ζ).mpr
    (inferInstanceAs (IsRegularLocalRing Z.subscheme.functionField))
  set T : Set X := Z.subschemeι '' (S : Set Z.subscheme)ᶜ with hT
  have hTc : IsClosed T :=
    Z.subschemeι.isClosedEmbedding.isClosedMap _ S.isOpen.isClosed_compl
  have hxT : x ∉ T := by
    rintro ⟨z, hz, hzx⟩
    rw [← hζx] at hzx
    exact hz (Z.subschemeι.isClosedEmbedding.injective hzx ▸ hζS)
  set R := smoothLocus sX with hR
  have hxR : x ∈ R := (mem_smoothLocus_iff_isRegularLocalRing sX x).mpr hreg
  set U : X.Opens := R ⊓ ⟨Tᶜ, hTc.isOpen_compl⟩ with hU
  have hxU : x ∈ U := ⟨hxR, hxT⟩
  set I := Z.comap U.ι with hI
  have hIsupp : (I.support : Set U) = U.ι ⁻¹' V := by
    rw [hI, Scheme.IdealSheafData.support_comap]
    change U.ι ⁻¹' (Z.support : Set X) = _
    rw [hZsupp]
  -- `U` is smooth
  have hUsm : IsSmoothScheme (U.ι ≫ sX) :=
    isSmoothScheme_of_forall_isRegularLocalRing _ fun u =>
      isRegularLocalRing_of_isOpenImmersion U.ι u
        ((mem_smoothLocus_iff_isRegularLocalRing sX _).mp u.2.1)
  -- `V ∩ U` is smooth
  have hIsm : IsSmoothScheme (I.subschemeι ≫ U.ι ≫ sX) :=
    isSmoothScheme_comap_ι Z U fun z hz => by_contra fun hns => hz.2 ⟨z, hns, rfl⟩
  -- irreducibility and the generic point
  have hxgen : IsGenericPoint x (V : Set X) := by
    have := V.isIrreducible.isGenericPoint_genericPoint_closure
    rwa [V.isClosed.closure_eq, ← hx] at this
  let xU : U.toScheme := ⟨x, hxU⟩
  have hxU' : U.ι xU = x := rfl
  have hpre' : IsGenericPoint xU (I.support : Set U.toScheme) := by
    rw [isGenericPoint_iff_specializes]
    intro y
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, hxU', hxgen.specializes_iff_mem,
      hIsupp]
    rfl
  have hirr : IsIrreducible (I.support : Set U.toScheme) := hpre'.isIrreducible
  have hgen : hirr.genericPoint = xU := by
    have h1 := hirr.isGenericPoint_genericPoint_closure
    rw [I.support.isClosed.closure_eq] at h1
    exact h1.eq hpre'
  refine ⟨U, hxU, I, ⟨hUsm, hIsm⟩, hirr, by rw [hgen]; rfl, ?_⟩
  have hcl : (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U.toScheme) =
      IrreducibleCloseds.closureSingleton xU := by
    ext1
    exact hpre'.symm
  rw [hcl, MMP.Flips.codimension_closureSingleton]
  exact (coheight_opens_ι xU).trans hcod

/-- The pull-back of a nonzero form along a dominant morphism inducing an isomorphism of
function fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := pullbackForms_eq hω m τ ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- Pulling a form back along `a : A ⟶ X` and then along `c : Z ⟶ A` is pulling it back along
`c ≫ a`, when both induce isomorphisms of function fields. -/
private theorem ordForm_pullback_pullback {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX]
    {A Z : Scheme.{u}} [IsIntegral A] [IsIntegral Z] [IsLocallyNoetherian Z]
    (a : A ⟶ X) (c : Z ⟶ A) [IsDominant a] [IsDominant c] [LocallyOfFiniteType (a ≫ sX)]
    [IsDominant (c ≫ a)]
    (hbija : Function.Bijective (functionFieldMap a))
    (hbijc : Function.Bijective (functionFieldMap c)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (E : MMP.Mori.PrimeDivisor Z) {m : ℤ} (τ : RationalPluriForms sX d m) :
    E.ordForm (pullbackRationalPluriForms (a ≫ sX) c (pullbackRationalPluriForms sX a τ)) =
      E.ordForm (pullbackRationalPluriForms sX (c ≫ a) τ) := by
  have key : pullbackRationalPluriForms (a ≫ sX) c (pullbackRationalPluriForms sX a τ) =
      pullbackRationalPluriForms sX (c ≫ a) τ := by
    let := functionFieldAlgebra sX
    let := functionFieldAlgebra (a ≫ sX)
    let := functionFieldAlgebra (c ≫ a ≫ sX)
    let := functionFieldMapAlgebra a
    let := functionFieldMapAlgebra c
    let := functionFieldMapAlgebra (c ≫ a)
    have := isScalarTower_functionFieldMap sX a
    have := isScalarTower_functionFieldMap (a ≫ sX) c
    have : IsScalarTower k X.functionField Z.functionField :=
      isScalarTower_functionFieldMap sX (c ≫ a)
    have : IsScalarTower X.functionField A.functionField Z.functionField :=
      IsScalarTower.of_algebraMap_eq fun x =>
        (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply c a x).symm
    obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX a hbija hd
    have hdA : (Algebra.trdeg k A.functionField).toNat = d := by
      rw [← trdeg_functionField_eq_of_bijective sX a hbija]
      exact hd
    obtain ⟨ω₁, hω₁⟩ := exists_isPullbackGenerator_of_bijective (a ≫ sX) c hbijc hdA
    exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω
      (MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₁ hω.2.1 hω.2.2) τ
  exact congrArg E.ordForm key

/-- Membership in powers of the maximal ideal is read through an isomorphism of local rings. -/
private theorem mem_maximalIdeal_pow_iff_of_bijective {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) (a : R) :
    e a ∈ IsLocalRing.maximalIdeal S ^ n ↔ a ∈ IsLocalRing.maximalIdeal R ^ n := by
  have hm : Ideal.map e (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  rw [← hm, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨b, hb, hba⟩ => e.injective hba ▸ hb, fun ha => ⟨a, ha, rfl⟩⟩

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}}
    {f : X ⟶ Y} (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

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

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι {k : Type u} [Field k] {Y : Scheme.{u}}
    {s : Y ⟶ Spec (.of k)} (h : IsNormalVariety k s) (V : Y.Opens) [Nonempty V] :
    IsNormalVariety k (V.ι ≫ s) := by
  have := h.1
  have := h.2
  have : IsIntegral Y := h.1.toIsIntegral
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s
  have : IsNoetherian Y := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- **The exceptional divisor of the blow-up of a codimension two point.** Let `X` be a normal
variety of dimension `n` over a perfect field and `x ∈ X` a point of codimension
two with regular local ring. There is a divisor `(Y, f, E)` over `X` with `f(η_E) = x` such that
`ord_E(f^*g) = max {s | g ∈ 𝔪_x^s}` for every nonzero `g ∈ 𝒪_{X,x}`, and `ord_E(f^*σ) = 1` for
every rational top form `σ` with `ord_Γ σ = 0` along every prime divisor `Γ` through `x`: the
exceptional divisor of the blow-up of the closure of `x`, near `x`. -/
private theorem exists_blowupDivisor {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n) (x : X)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) (hcod : Order.coheight x = 2) :
    ∃ D : DivisorOver k sX, D.f D.E.genericPoint = x ∧
      (haveI := D.isIntegral
       haveI := D.isLocallyNoetherian
       haveI := D.isDominant
       ∀ g : X.presheaf.stalk x, g ≠ 0 → ∀ s : ℕ,
        (s : ℤ) ≤ D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField g))
            D.E.genericPoint ↔
          g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ s) ∧
      ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
        (∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → Γ.ordForm σ = 0) →
          D.ordPullback σ = 1 := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  set V : IrreducibleCloseds X := IrreducibleCloseds.closureSingleton x with hV
  have hxV : x = V.isIrreducible.genericPoint := by
    have h1 : IsGenericPoint x (V : Set X) := rfl
    have h2 : IsGenericPoint V.isIrreducible.genericPoint (V : Set X) := by
      have := V.isIrreducible.isGenericPoint_genericPoint_closure
      rwa [V.isClosed.closure_eq] at this
    exact h1.eq h2
  obtain ⟨U, hxU, I, hsb, hirr, hgenpt, hcodI⟩ := exists_smoothBlowup hX.1 V x hxV hreg hcod
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨x, hxU⟩)
  have hbijU : Function.Bijective (functionFieldMap U.ι) :=
    functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨⟨x, hxU⟩, trivial⟩
  have hUnv := isNormalVariety_ι hX U
  have : LocallyOfFiniteType (U.ι ≫ sX) := hUnv.1.toLocallyOfFiniteType
  have hdU : topologicalKrullDim U = n := by
    let := functionFieldAlgebra sX
    let := functionFieldAlgebra (U.ι ≫ sX)
    rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX U.ι hbijU, toENat_trdeg_functionField (sX := sX),
      hn]
  have hc2 : (2 : ℕ) ≤ 2 := le_rfl
  have hcI : ((2 : ℕ) : ℕ∞) =
      codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [hcodI]; rfl
  obtain ⟨hordE, hformE⟩ :=
    MMP.Threefold.Resolution.ord_exceptionalPrimeDivisor_pullback_and_ordForm_pullback
      (U.ι ≫ sX) hUnv.1 I hsb hirr hcI hc2 hdU
  obtain ⟨hvarB, hsmB, -, hbirπ, -⟩ :=
    MMP.Threefold.Resolution.isVariety_smooth_blowUpToBase_divisorOfForm_pullbackRationalPluriForms
      (U.ι ≫ sX) hUnv.1 hdU I hsb hirr hcI hc2
  set y := hirr.genericPoint with hy
  have hc1 : 1 ≤ codimension (⟨I.support, hirr, I.support.isClosed⟩ : IrreducibleCloseds U) := by
    rw [hcodI]; decide
  set π := blowUpToBase I with hπ
  have : IsIntegral (blowUp I) :=
    MMP.Threefold.Resolution.isIntegral_blowUp_of_one_le_codimension I hirr hc1
  have : IsDominant π := MMP.Threefold.Resolution.isDominant_blowUpToBase I hirr hc1
  have : LocallyOfFiniteType (π ≫ U.ι ≫ sX) := hvarB.toLocallyOfFiniteType
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian (π ≫ U.ι ≫ sX)
  have : IsNormal (Spec (.of k)) := isNormal_spec_of_isIntegrallyClosed _
  have : IsNormal (blowUp I) := AlgebraicGeometry.isNormal_of_smooth (π ≫ U.ι ≫ sX)
  have : IsDominant (π ≫ U.ι) := inferInstance
  set Eex := MMP.Resolution.exceptionalPrimeDivisor (U.ι ≫ sX) I hsb hirr hc1 with hEex
  have hnv : IsNormalVariety k ((π ≫ U.ι) ≫ sX) := by
    rw [Category.assoc]; exact ⟨hvarB, inferInstance⟩
  have hbir : IsBirationalMorphism (π ≫ U.ι) := by
    obtain ⟨O, hO, hOi⟩ := exists_isOpenImmersion_of_isBirationalMorphism hbirπ
    have : IsOpenImmersion (O.ι ≫ π ≫ U.ι) := by
      rw [← Category.assoc]; infer_instance
    exact isBirationalMorphism_of_isOpenImmersion (π ≫ U.ι) O hO
  let D' : DivisorOver k sX := ⟨blowUp I, π ≫ U.ι, hnv, hbir, Eex⟩
  -- the generic point of the exceptional divisor lies over the generic point of the centre
  have hπξ : π Eex.genericPoint = y := by
    have := MMP.Threefold.Resolution.smooth_of_isSmoothScheme hsb.1
    have := (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
      (U.ι ≫ sX) I hsb).1
    obtain ⟨-, F', hF'id, -, hFimg⟩ :=
      MMP.Resolution.isSmoothScheme_blowUp_and_exists_primeDivisor_exceptionalIdeal (U.ι ≫ sX) I
        hsb hirr hc1
    have hsuppF : Eex.support = ((exceptionalIdeal I).support : Set (blowUp I)) := rfl
    have hsuppF' : F'.support = ((exceptionalIdeal I).support : Set (blowUp I)) := by
      simp only [AlgebraicGeometry.PrimeDivisor.support, hF'id]
    have hgenπ : IsGenericPoint (π Eex.genericPoint) (I.support : Set U) := by
      change closure {π Eex.genericPoint} = _
      rw [← Set.image_singleton, π.isClosedMap.closure_image_eq_of_continuous π.continuous,
        ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, hsuppF, ← hsuppF', hFimg]
    exact hgenπ.eq (hirr.isGenericPoint_genericPoint_closure.trans I.support.isClosed.closure_eq)
  have hD'x : D'.f D'.E.genericPoint = x := by
    change U.ι (π Eex.genericPoint) = x
    rwa [hπξ]
  refine ⟨D', hD'x, ?_, ?_⟩
  · -- orders of functions
    have key : ∀ (z : X) (_ : U.ι y = z) (g : X.presheaf.stalk z), g ≠ 0 → ∀ s : ℕ,
        (s : ℤ) ≤ (blowUp I).ord (functionFieldMap (π ≫ U.ι) (algebraMap _ X.functionField g))
            Eex.genericPoint ↔ g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) ^ s := by
      rintro z rfl g hg s
      have : IsIso (U.ι.stalkMap y) := inferInstance
      set e := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv with he
      set g' := e g with hg'
      have hg'0 : g' ≠ 0 := fun h0 => hg (e.injective (h0.trans (map_zero e).symm))
      have hffm : functionFieldMap (π ≫ U.ι) (algebraMap _ X.functionField g) =
          functionFieldMap π (algebraMap _ (U : Scheme).functionField g') := by
        rw [← MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
          MMP.Mori.functionFieldMap_algebraMap_stalk]
        rfl
      rw [hffm]
      exact (hordE g' hg'0 s).trans (mem_maximalIdeal_pow_iff_of_bijective e s g)
    exact key x hgenpt
  · -- orders of top forms
    intro σ hσ0 hσΓ
    let F := (finite_ordForm_ne_zero σ).toFinset
    have hFc : IsClosed (⋃ Γ ∈ F, (Γ.support : Set X)) :=
      F.finite_toSet.isClosed_biUnion fun Γ _ => Γ.idealSheaf.support.isClosed
    let W : X.Opens := ⟨_, hFc.isOpen_compl⟩
    have hxW : x ∈ W := by
      change x ∉ ⋃ Γ ∈ F, (Γ.support : Set X)
      simp only [Set.mem_iUnion, not_exists]
      intro Γ hΓF hxΓ
      exact ((Set.Finite.mem_toFinset _).mp hΓF) (hσΓ Γ hxΓ)
    have hgen : GeneratesOn (0 : QDivisor X) 1 W σ := by
      refine ⟨hσ0, fun Γ ⟨w, hwΓ, hwW⟩ => ?_⟩
      have : Γ.ordForm σ = 0 := by
        by_contra hne
        exact hwW (Set.mem_biUnion ((Set.Finite.mem_toFinset _).mpr hne) hwΓ)
      simp [this]
    set τU := pullbackRationalPluriForms sX U.ι σ with hτU
    have hτgen : GeneratesOn (0 : QDivisor U) 1 (U.ι ⁻¹ᵁ W) τU := by
      refine ⟨pullbackRationalPluriForms_ne_zero U.ι hbijU hd hσ0, fun Wd hWd => ?_⟩
      have hP : ((OpenWeilRestriction.primeDivisorMap U.ι Wd).support ∩ W).Nonempty := by
        rw [← MMP.Mori.PrimeDivisor.genericPoint_mem_iff]
        exact (congrArg (· ∈ W) (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι Wd)).mpr
          ((Wd.genericPoint_mem_iff _).2 hWd)
      have e1 := MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso U.ι hbijU hd Wd
        (OpenWeilRestriction.primeDivisorMap U.ι Wd)
        (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm σ
      have e2 := hgen.2 _ hP
      rw [hτU, e1]
      simpa using e2
    have hyW : y ∈ U.ι ⁻¹ᵁ W := by
      change U.ι y ∈ W
      rwa [hgenpt]
    have hform1 := hformE 1 τU ⟨_, hyW, hτgen⟩
    change MMP.Mori.PrimeDivisor.ordForm Eex (pullbackRationalPluriForms sX (π ≫ U.ι) σ) = 1
    rw [← ordForm_pullback_pullback U.ι π hbijU hbirπ.functionFieldMap_bijective hd Eex σ]
    rw [hform1]
    norm_num

/-- The order of `1` at any point is zero. -/
private theorem ord_one {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (y : Y) :
    Y.ord 1 y = 0 := by
  have := Scheme.ord_mul (X := Y) (x := y) (one_ne_zero (α := Y.functionField)) one_ne_zero
  rw [mul_one] at this
  omega

open scoped Classical in
/-- **Local equations at a regular point.** For `x` with regular local ring, a choice for every
prime divisor `Γ` of a rational function `p Γ`: a generator of the ideal of `Γ` at `x` when
`x ∈ Γ`, and `1` otherwise. Along the prime divisors through `x`, `p Γ` vanishes to order one on
`Γ` and is a unit elsewhere. -/
private theorem exists_localEquations {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (x : X) (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ p : MMP.Mori.PrimeDivisor X → X.functionField, (∀ Γ, p Γ ≠ 0) ∧
      (∀ Γ, x ∉ Γ.support → p Γ = 1) ∧
      (∀ Γ, x ∈ Γ.support → ∃ π : X.presheaf.stalk x, π ≠ 0 ∧
        IdealSheafData.stalk Γ.idealSheaf x = Ideal.span {π} ∧
        p Γ = algebraMap _ X.functionField π) ∧
      ∀ Γ Γ' : MMP.Mori.PrimeDivisor X, x ∈ Γ'.support →
        X.ord (p Γ) Γ'.genericPoint = if Γ' = Γ then 1 else 0 := by
  refine ⟨fun Γ => if h : x ∈ Γ.support then
    algebraMap _ X.functionField (exists_localEquation x hreg Γ h).choose else 1,
    fun Γ => ?_, fun Γ h => dite_eq_right h, fun Γ h => ?_, fun Γ Γ' hΓ' => ?_⟩
  · dsimp only
    split_ifs with h
    · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero (exists_localEquation x hreg Γ h).choose_spec.1)
    · exact one_ne_zero
  · obtain ⟨hπ0, hπI, -⟩ := (exists_localEquation x hreg Γ h).choose_spec
    exact ⟨_, hπ0, (Scheme.IdealSheafData.stalkIdeal_eq_stalk _ _).symm.trans hπI, dite_eq_left h⟩
  · by_cases h : x ∈ Γ.support
    · simp only [dite_eq_left h]
      exact (exists_localEquation x hreg Γ h).choose_spec.2.2 Γ' hΓ'
    · simp only [dite_eq_right h]
      rw [ite_eq_right (by rintro rfl; exact h hΓ'), ord_one]

/-- **A form with no zeros or poles through a regular point.** On a normal variety of dimension
`n` over a perfect field, for `x` with regular local ring, there is a nonzero
rational top form `σ` with `ord_Γ σ = 0` along every prime divisor `Γ` through `x`: a rational top
form divided by local equations of the prime divisors through `x` along which it has a zero or
a pole. -/
private theorem exists_form_ordForm_eq_zero {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) {n : ℕ} (hn : topologicalKrullDim X = n) (x : X)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ σ : RationalPluriForms sX n 1, σ ≠ 0 ∧
      ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → Γ.ordForm σ = 0 := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨β⟩ := MMP.Positivity.exists_basis_topForms hX hn
  let ω₀ : RationalPluriForms sX n 1 := (ZTensorPower.basis β 1) ()
  have hω₀ : ω₀ ≠ 0 := (ZTensorPower.basis β 1).ne_zero ()
  let T : Finset (MMP.Mori.PrimeDivisor X) :=
    (finite_ordForm_ne_zero ω₀).toFinset.filter fun Γ => x ∈ Γ.support
  obtain ⟨p, hp0, -, -, hpΓ⟩ := exists_localEquations x hreg
  let h₀ : X.functionField := ∏ Γ ∈ T, p Γ ^ (-(Γ.ordForm ω₀))
  have hh₀ : h₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun Γ _ => zpow_ne_zero _ (hp0 Γ)
  refine ⟨h₀ • ω₀, smul_ne_zero hh₀ hω₀, fun Γ hΓ => ?_⟩
  rw [Γ.ordForm_smul_of_topologicalKrullDim_eq hn hh₀ hω₀,
    MMP.Threefold.Bridges.ord_prod_zpow _ _ _ hp0]
  simp_rw [hpΓ _ Γ hΓ]
  by_cases hT : Γ ∈ T
  · rw [Finset.sum_eq_single Γ]
    · simp
    · intro Γ' _ hne
      simp [Ne.symm hne]
    · exact fun h => (h hT).elim
  · have h0 : Γ.ordForm ω₀ = 0 := by
      by_contra hne
      exact hT (Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hne, hΓ⟩)
    rw [h0, add_zero]
    refine Finset.sum_eq_zero fun Γ' hΓ' => ?_
    have : Γ ≠ Γ' := fun e => hT (e ▸ hΓ')
    simp [this]

/-- The order along `E` of a local equation `π ∈ 𝔪_x ∖ 𝔪_x²` is one, when orders along `E` of
elements of `𝒪_{X,x}` are their `𝔪_x`-adic orders. -/
private theorem ord_eq_one_of_mem_maximalIdeal_of_notMem_sq {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)} (D : DivisorOver k sX) (x : X)
    (hord : haveI := D.isIntegral
      haveI := D.isLocallyNoetherian
      haveI := D.isDominant
      ∀ g : X.presheaf.stalk x, g ≠ 0 → ∀ s : ℕ,
        (s : ℤ) ≤ D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField g))
            D.E.genericPoint ↔
          g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ s)
    {π : X.presheaf.stalk x} (hπ0 : π ≠ 0) (hπm : π ∈ IsLocalRing.maximalIdeal _)
    (hπ2 : π ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isDominant
    D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField π)) D.E.genericPoint = 1 := by
  have h1 := (hord π hπ0 1).mpr (by rwa [pow_one])
  have h2 : ¬ ((2 : ℕ) : ℤ) ≤ _ := fun h => hπ2 ((hord π hπ0 2).mp h)
  push_cast at h1 h2
  omega

open scoped Classical in
/-- **The discrepancy of the blow-up of a codimension two point.** Let `(Y, f, E)` be a divisor
over a normal variety `X` with `f(η_E) = x`, `x` with regular local ring, such that
`ord_E(f^*g) = max {s | g ∈ 𝔪_x^s}` for `g ∈ 𝒪_{X,x}` and `ord_E(f^*σ) = 1` for every top form `σ`
with no zero or pole through `x`. If every component of `Δ` through `x` has a local equation in
`𝔪_x ∖ 𝔪_x²`, then `a(E, X, Δ) = 1 - ∑_{x ∈ Γ} coeff_Γ Δ`. -/
public theorem isDiscrepancy_eq_one_sub_sum {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {Δ : QDivisor X} (x : X) (hreg : IsRegularLocalRing (X.presheaf.stalk x))
    (hmult : ∀ Γ ∈ Δ.support, x ∈ Γ.support →
      ¬ IdealSheafData.stalk Γ.idealSheaf x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2)
    (D : DivisorOver k sX) (hDx : D.f D.E.genericPoint = x)
    (hord : haveI := D.isIntegral
      haveI := D.isLocallyNoetherian
      haveI := D.isDominant
      ∀ g : X.presheaf.stalk x, g ≠ 0 → ∀ s : ℕ,
        (s : ℤ) ≤ D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField g))
            D.E.genericPoint ↔
          g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ s)
    {n : ℕ}
    (hσ : ∀ σ : RationalPluriForms sX n 1, σ ≠ 0 →
        (∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support → Γ.ordForm σ = 0) →
          D.ordPullback σ = 1)
    {K : Divisor X} {c : ℚ} (hc : IsDiscrepancy sX n K Δ D c) :
    c = 1 - ∑ Γ ∈ Δ.support, if x ∈ Γ.support then Δ.coeff Γ else 0 := by
  classical
  obtain ⟨hX, hK, m, hm, -, W, hW, τ, hτ, hτc⟩ := hc
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨σ, hσ0, hσΓ⟩ := exists_form_ordForm_eq_zero hX hn x hreg
  have hσE := hσ σ hσ0 hσΓ
  obtain ⟨β, N, hN⟩ := D.exists_ordPullback_eq hX hn
  -- local equations
  obtain ⟨p, hp0, hp1, hpπ, hpΓ⟩ := exists_localEquations x hreg
  have hpE : ∀ Γ ∈ Δ.support,
      D.Y.ord (functionFieldMap D.f (p Γ)) D.E.genericPoint =
        if x ∈ Γ.support then 1 else 0 := by
    intro Γ hΓS
    by_cases h : x ∈ Γ.support
    · obtain ⟨π, hπ0, hπI, hpπ⟩ := hpπ Γ h
      rw [hpπ, ite_eq_left h]
      have hπm : π ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
        have hle := (Stacks.Divisors.stalk_le_maximalIdeal_iff_mem_support Γ.idealSheaf x).mpr h
        exact hle (hπI ▸ Ideal.mem_span_singleton_self π)
      have hπ2 : π ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2 := by
        intro hmem
        refine hmult Γ hΓS h ?_
        rw [hπI, Ideal.span_singleton_le_iff_mem]
        exact hmem
      exact ord_eq_one_of_mem_maximalIdeal_of_notMem_sq D x hord hπ0 hπm hπ2
    · rw [hp1 Γ h, ite_eq_right h, map_one, ord_one]
  -- the Hartogs relation
  set cτ := (ZTensorPower.basis β (m : ℤ)).repr τ () with hcτ
  set cσ := (ZTensorPower.basis β 1).repr σ () with hcσ
  have hcτ0 : cτ ≠ 0 := repr_ne_zero_of_ne_zero β hτ.1
  have hcσ0 : cσ ≠ 0 := repr_ne_zero_of_ne_zero β hσ0
  let S := Δ.support
  let G : Option (Option S) → X.functionField := fun j =>
    Option.elim j cτ fun j => Option.elim j cσ fun Γ => p Γ.1
  let w : Option (Option S) → ℝ := fun j =>
    Option.elim j 1 fun j => Option.elim j (-(m : ℝ)) fun Γ => (m : ℝ) * (Δ Γ.1 : ℝ)
  have hG : ∀ j, G j ≠ 0 := by
    rintro (_ | _ | Γ)
    exacts [hcτ0, hcσ0, hp0 _]
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E G hG w
    fun Γ' hΓ' => by
      rw [hDx] at hΓ'
      obtain ⟨NΓ, hNΓ⟩ := Γ'.exists_ordForm_eq_ord_add_mul hd β
      have e1 := hNΓ m τ hτ.1
      have e2 := hNΓ 1 σ hσ0
      rw [hσΓ Γ' hΓ'] at e2
      have e3 := hτ.2 Γ' ⟨_, hΓ', hDx ▸ hW⟩
      simp only [Fintype.sum_option, G, w, Option.elim]
      have e4 : ∑ Γ : S, (X.ord (p Γ.1) Γ'.genericPoint : ℝ) * ((m : ℝ) * (Δ Γ.1 : ℝ)) =
          (m : ℝ) * (Δ Γ' : ℝ) := by
        simp_rw [hpΓ _ Γ' hΓ']
        by_cases hS : Γ' ∈ S
        · rw [Finset.sum_eq_single ⟨Γ', hS⟩]
          · simp
          · rintro ⟨Γ, hΓS⟩ - hne
            have : Γ' ≠ Γ := fun h => hne (Subtype.ext h.symm)
            simp [this]
          · simp
        · have hB : Δ Γ' = 0 := Finsupp.notMem_support_iff.mp hS
          rw [hB, Rat.cast_zero, mul_zero]
          refine Finset.sum_eq_zero fun Γ _ => ?_
          have : Γ' ≠ Γ.1 := fun h => hS (h ▸ Γ.2)
          simp [this]
      rw [e4]
      have e3' : (Γ'.ordForm τ : ℝ) + (m : ℝ) * (Δ Γ' : ℝ) = 0 := by
        have := congrArg (fun q : ℚ => (q : ℝ)) e3
        push_cast at this
        simpa [DivisorWithCoeffs.coeff_apply] using this
      have e1' : (Γ'.ordForm τ : ℝ) = X.ord cτ Γ'.genericPoint + (m : ℝ) * NΓ := by
        exact_mod_cast e1
      have e2' : (0 : ℝ) = X.ord cσ Γ'.genericPoint + NΓ := by
        exact_mod_cast (by simpa using e2)
      linear_combination e3' - e1' + (m : ℝ) * e2'
  simp only [Fintype.sum_option, G, w, Option.elim] at key
  have hsumE : ∑ Γ : S, (D.Y.ord (functionFieldMap D.f (p Γ.1)) D.E.genericPoint : ℝ) *
      ((m : ℝ) * (Δ Γ.1 : ℝ)) =
      (m : ℝ) * (((∑ Γ ∈ Δ.support, if x ∈ Γ.support then Δ.coeff Γ else 0 : ℚ)) : ℝ) := by
    rw [Rat.cast_sum, Finset.mul_sum, ← Finset.sum_coe_sort Δ.support]
    refine Finset.sum_congr rfl fun Γ _ => ?_
    rw [hpE Γ.1 Γ.2]
    split_ifs <;> simp [DivisorWithCoeffs.coeff_apply]
  rw [hsumE] at key
  have h1 : ((m : ℤ) : ℝ) * (c : ℝ) = (D.Y.ord (functionFieldMap D.f cτ) D.E.genericPoint : ℝ) +
      (m : ℝ) * N := by
    have := hN m τ hτ.1
    have h1' : (m : ℚ) * c = ((D.Y.ord (functionFieldMap D.f cτ) D.E.genericPoint : ℤ) : ℚ) +
        (m : ℚ) * N := by
      rw [hτc, this]; push_cast; ring
    have := congrArg (fun q : ℚ => (q : ℝ)) h1'
    push_cast at this ⊢
    linear_combination this
  have h2 : (1 : ℝ) = (D.Y.ord (functionFieldMap D.f cσ) D.E.genericPoint : ℝ) + N := by
    have := hN 1 σ hσ0
    rw [hσE] at this
    exact_mod_cast (by simpa using this)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hfin : (m : ℝ) * (c : ℝ) = (m : ℝ) *
      ((1 : ℝ) - (((∑ Γ ∈ Δ.support, if x ∈ Γ.support then Δ.coeff Γ else 0 : ℚ)) : ℝ)) := by
    push_cast at h1
    linear_combination h1 - (m : ℝ) * h2 + key
  have := mul_left_cancel₀ hm'.ne' hfin
  exact_mod_cast this

open scoped Classical in
/-- **Blowing up a codimension two point bounds the discrepancy.** On a smooth variety over a
perfect field, if `x` has codimension two and every component of `Δ` through `x`
has a local equation in `𝔪_x ∖ 𝔪_x²`, then `discrep(X, Δ) ≤ 1 - ∑_{x ∈ Γ} coeff_Γ Δ`. -/
private theorem discrep_le_of_coheight_eq_two {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) (Δ : QDivisor X) (x : X) (hcod : Order.coheight x = 2)
    (hmult : ∀ Γ ∈ Δ.support, x ∈ Γ.support →
      ¬ IdealSheafData.stalk Γ.idealSheaf x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2) :
    discrep sX n K Δ ≤
      (((1 - ∑ Γ ∈ Δ.support, if x ∈ Γ.support then Δ.coeff Γ else 0 : ℚ) : ℝ) : EReal) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth_over_field sX x
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨D, hDx, hord, hσ⟩ := exists_blowupDivisor hX hn x hreg hcod
  have hP : IsPair sX Δ :=
    isPair_of_isCanonicalDivisor hX hK (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  have hE : D.IsExceptional :=
    (DivisorOver.isExceptional_iff_two_le_coheight hX D).mpr (by rw [hDx, hcod])
  have hval := isDiscrepancy_eq_one_sub_sum x hreg hmult D hDx hord hσ ha
  rw [← hval]
  exact discrep_le hE ha

/-! ### Codimension two points with prescribed components -/

/-- In a regular local ring, two distinct members of a regular system of parameters generate a
prime ideal of height two. -/
private theorem isPrime_span_pair_and_height_eq_two {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {N : ℕ} {z : Fin N → R} (hz : IsRegularSystemOfParameters z)
    {a b : Fin N} (hab : a ≠ b) :
    (Ideal.span {z a, z b}).IsPrime ∧ (Ideal.span {z a, z b}).height = 2 := by
  classical
  have hN : 2 ≤ N := by
    have := Finset.card_le_univ ({a, b} : Finset (Fin N))
    rw [Finset.card_pair hab, Fintype.card_fin] at this
    exact this
  obtain ⟨h2, hdim2, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz {a, b}
  obtain ⟨h1, hdim1, -⟩ :=
    MMP.Flips.ResolutionInputs.isRegularSystemOfParameters_quotient_image hz {a}
  have e2 : z '' (({a, b} : Finset (Fin N)) : Set (Fin N)) = {z a, z b} := by
    rw [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton]
  have e1 : z '' (({a} : Finset (Fin N)) : Set (Fin N)) = {z a} := by
    rw [Finset.coe_singleton, Set.image_singleton]
  rw [e2] at h2 hdim2
  rw [e1] at h1 hdim1
  rw [Finset.card_pair hab] at hdim2
  rw [Finset.card_singleton] at hdim1
  have := IsRegularLocalRing.isDomain (R ⧸ Ideal.span {z a, z b})
  have := IsRegularLocalRing.isDomain (R ⧸ Ideal.span {z a})
  have := IsRegularLocalRing.isDomain R
  have hP : (Ideal.span {z a, z b}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hP1 : (Ideal.span {z a}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hR := hz.2
  refine ⟨hP, le_antisymm ?_ ?_⟩
  · -- Krull's height theorem
    have hmin : Ideal.span {z a, z b} ∈ (Ideal.span {z a, z b}).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl
    refine (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ hmin).trans ?_
    have hc := Submodule.spanRank_span_le_card (R := R) ({z a, z b} : Set R)
    have hc2 : Cardinal.mk ({z a, z b} : Set R) ≤ 2 := by
      have := Cardinal.mk_insert_le (a := z a) (s := ({z b} : Set R))
      simp only [Cardinal.mk_singleton] at this
      exact this.trans (by norm_num)
    have := Cardinal.toENat.monotone' (hc.trans hc2)
    simpa using this
  · -- the chain `0 < (z a) < (z a, z b)`
    have hbot : (⊥ : Ideal R).IsPrime := Ideal.isPrime_bot
    have hlt1 : (⊥ : Ideal R) < Ideal.span {z a} := by
      refine lt_of_le_of_ne bot_le fun h => ?_
      rw [← h, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R), hR] at hdim1
      have : ((N : ℕ∞) : WithBot ℕ∞) = ((N - 1 : ℕ) : ℕ∞) := by exact_mod_cast hdim1
      have : N = N - 1 := by exact_mod_cast this
      omega
    have hlt2 : Ideal.span {z a} < Ideal.span {z a, z b} := by
      refine lt_of_le_of_ne (Ideal.span_mono (by simp)) fun h => ?_
      rw [← h, hdim1] at hdim2
      have : N - 1 = N - 2 := by exact_mod_cast hdim2
      omega
    have i1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt1
    rw [Ideal.height_bot, zero_add] at i1
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ (Ideal.span {z a}).height + 1 := by gcongr
      _ ≤ _ := Ideal.height_add_one_le_of_lt_of_isPrime hlt2

/-- **The generization cut out by two regular parameters.** If `z` is a regular system of
parameters of `𝒪_{X,p}` and `a ≠ b`, the prime `(z_a, z_b)` of `𝒪_{X,p}` is a point `x ⤳ p` of
codimension two, lying on every closed subscheme whose ideal at `p` is contained in
`(z_a, z_b)`. -/
private theorem exists_specializes_coheight_eq_two {X : Scheme.{u}} (p : X)
    [IsRegularLocalRing (X.presheaf.stalk p)] {N : ℕ} {z : Fin N → X.presheaf.stalk p}
    (hz : IsRegularSystemOfParameters z) {a b : Fin N} (hab : a ≠ b) :
    ∃ x : X, x ⤳ p ∧ Order.coheight x = 2 ∧ ∀ I : X.IdealSheafData,
      IdealSheafData.stalk I p ≤ Ideal.span {z a, z b} → x ∈ I.support := by
  obtain ⟨hP, hh⟩ := isPrime_span_pair_and_height_eq_two hz hab
  set P : PrimeSpectrum (X.presheaf.stalk p) := ⟨_, hP⟩
  set x := X.fromSpecStalk p P with hx
  have hsp : x ⤳ p := MMP.Resolution.specializes_fromSpecStalk p P
  have hprime := MMP.Resolution.primeOfSpecializes_fromSpecStalk p P hsp
  refine ⟨x, hsp, ?_, fun I hI => ?_⟩
  · let := (X.presheaf.stalkSpecializes hsp).hom.toAlgebra
    have := MMP.Intersection.isLocalization_stalkSpecializes hsp
    have hp' : (MMP.Intersection.primeOfSpecializes hsp).IsPrime := by
      rwa [hprime]
    have e := IsLocalization.AtPrime.ringKrullDim_eq_height
      (MMP.Intersection.primeOfSpecializes hsp) (X.presheaf.stalk x)
    rw [ringKrullDim_stalk_eq_coheight, hprime] at e
    change ((Order.coheight x : ℕ∞) : WithBot ℕ∞) = (((Ideal.span {z a, z b}).height : ℕ∞) :
      WithBot ℕ∞) at e
    rw [hh] at e
    exact_mod_cast e
  · rwa [MMP.Resolution.mem_support_iff_stalk_le_primeOfSpecializes I hsp, hprime]

/-! ### Simple normal crossing divisors -/

/-- A member of a regular system of parameters does not lie in `𝔪²`. -/
private theorem notMem_maximalIdeal_sq {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {N : ℕ} {z : Fin N → R} (hz : IsRegularSystemOfParameters z) (i : Fin N) :
    z i ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  obtain ⟨hmem, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular z hz.1 hz.2
  intro h
  exact hli.ne_zero i ((Ideal.toCotangent_eq_zero _ _).mpr h)

/-- The length of a regular system of parameters of `𝒪_{X,y}` is the codimension of `y`. -/
public theorem coheight_eq_of_isRegularSystemOfParameters {X : Scheme.{u}} {y : X} {N : ℕ}
    {z : Fin N → X.presheaf.stalk y} (hz : IsRegularSystemOfParameters z) :
    Order.coheight y = N := by
  have h := hz.2
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- The local description of `∑_{E ∈ S} E` snc at a point `y`: a regular system of parameters of
`𝒪_{X,y}` and an injective choice, for each `E ∈ S` through `y`, of a parameter generating the
ideal of `E`. -/
public theorem exists_at_of_isSNC {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ))) (y : X) :
    ∃ (N : ℕ) (z : Fin N → X.presheaf.stalk y)
      (j : {G : MMP.Mori.PrimeDivisor X // G ∈ S ∧ y ∈ G.support} → Fin N),
      IsRegularSystemOfParameters z ∧ Function.Injective j ∧
        ∀ G, IdealSheafData.stalk G.1.idealSheaf y = Ideal.span {z (j G)} := by
  obtain ⟨N, z, j, hz, hj, hI⟩ := hsnc.2 y
  let e : {G : MMP.Mori.PrimeDivisor X // G ∈ S ∧ y ∈ G.support} →
      {G : MMP.Mori.PrimeDivisor X //
        G ∈ (∑ E ∈ S, Finsupp.single E (1 : ℤ)).support ∧ y ∈ G.support} :=
    fun G => ⟨G.1, (mem_support_sum_single S G.1).mpr G.2.1, G.2.2⟩
  exact ⟨N, z, j ∘ e, hz, hj.comp fun G G' h => Subtype.ext (congrArg Subtype.val h :),
    fun G => hI (e G)⟩

/-- On a smooth scheme over a field, a component through `y` of an snc divisor has a local
equation at `y` outside `𝔪_y²`. -/
private theorem stalk_not_le_sq_of_isSNC {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [Smooth sX] {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ))) (y : X)
    {G : MMP.Mori.PrimeDivisor X} (hG : G ∈ S) (hy : y ∈ G.support) :
    ¬ IdealSheafData.stalk G.idealSheaf y ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) ^ 2 := by
  have := isRegularLocalRing_stalk_of_smooth_over_field sX y
  obtain ⟨N, z, j, hz, -, hI⟩ := exists_at_of_isSNC hsnc y
  rw [hI ⟨G, hG, hy⟩, Ideal.span_singleton_le_iff_mem]
  exact notMem_maximalIdeal_sq hz _

/-- At a point of codimension two, at most two components of an snc divisor pass. -/
private theorem eq_or_eq_of_isSNC_of_coheight_eq_two {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ))) {x : X}
    (hx : Order.coheight x = 2) {E F G : MMP.Mori.PrimeDivisor X} (hEF : E ≠ F)
    (hE : E ∈ S) (hF : F ∈ S) (hG : G ∈ S) (hxE : x ∈ E.support) (hxF : x ∈ F.support)
    (hxG : x ∈ G.support) : G = E ∨ G = F := by
  obtain ⟨N, z, j, hz, hj, -⟩ := exists_at_of_isSNC hsnc x
  have hN : N = 2 := by
    have := coheight_eq_of_isRegularSystemOfParameters hz
    rw [hx] at this
    exact_mod_cast this.symm
  by_contra hne
  rw [not_or] at hne
  have hlt := fun i : Fin N => (hN ▸ i.2 : (i : ℕ) < 2)
  have v1 : (j ⟨E, hE, hxE⟩ : ℕ) ≠ j ⟨F, hF, hxF⟩ := fun h =>
    hEF (congrArg Subtype.val (hj (Fin.ext h)))
  have v2 : (j ⟨G, hG, hxG⟩ : ℕ) ≠ j ⟨E, hE, hxE⟩ := fun h =>
    hne.1 (congrArg Subtype.val (hj (Fin.ext h)))
  have v3 : (j ⟨G, hG, hxG⟩ : ℕ) ≠ j ⟨F, hF, hxF⟩ := fun h =>
    hne.2 (congrArg Subtype.val (hj (Fin.ext h)))
  have := hlt (j ⟨E, hE, hxE⟩)
  have := hlt (j ⟨F, hF, hxF⟩)
  have := hlt (j ⟨G, hG, hxG⟩)
  omega

/-- A sum over the support of `Δ` of the coefficients of the components with a property is the
sum over the finite set of components with that property. -/
private theorem sum_ite_coeff_eq_sum {X : Scheme.{u}} (Δ : QDivisor X)
    (T : Finset (MMP.Mori.PrimeDivisor X)) (P : MMP.Mori.PrimeDivisor X → Prop) [DecidablePred P]
    (h : ∀ Γ ∈ Δ.support, P Γ ↔ Γ ∈ T) :
    ∑ Γ ∈ Δ.support, (if P Γ then Δ.coeff Γ else 0) = ∑ Γ ∈ T, Δ.coeff Γ := by
  classical
  rw [Finset.sum_congr rfl fun Γ hΓ => by rw [if_congr (h Γ hΓ) rfl rfl], Finset.sum_ite_mem]
  refine Finset.sum_subset Finset.inter_subset_right fun Γ hΓT hΓ => ?_
  have : Γ ∉ Δ.support := fun hs => hΓ (Finset.mem_inter.mpr ⟨hs, hΓT⟩)
  rw [DivisorWithCoeffs.coeff_apply]
  exact Finsupp.notMem_support_iff.mp this

/-- A closed point of a variety of dimension `n` has codimension `n`. -/
private theorem coheight_eq_of_isClosed {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {n : ℕ} (hn : topologicalKrullDim X = n)
    {p : X} (hp : IsClosed ({p} : Set X)) : Order.coheight p = n := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX p
  have h0 : topologicalKrullDim (closure {p} : Set X) = 0 := by
    rw [hp.closure_eq]
    apply le_antisymm (topologicalKrullDim_zero_of_discreteTopology _)
    have : Nonempty ({p} : Set X) := ⟨⟨p, rfl⟩⟩
    have : Nonempty (TopologicalSpace.IrreducibleCloseds ({p} : Set X)) :=
      ⟨⟨{⟨p, rfl⟩}, isIrreducible_singleton, isClosed_discrete _⟩⟩
    exact Order.krullDim_nonneg
  rw [h0, zero_add, hn] at h
  have : ((Order.coheight p : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := h
  exact WithBot.coe_injective this

/-! ### The upper bound -/

section UpperBound

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}

open scoped Classical in
/-- The discrepancy bound of a codimension two point `x`, for `Δ` supported on the components
of an snc divisor `∑_{E ∈ S} E`, when the components of `S` through `x` are those of `T`. -/
private theorem discrep_le_of_isSNC_of_coheight_eq_two (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Δ : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)} (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ))) {x : X}
    (hcod : Order.coheight x = 2) (T : Finset (MMP.Mori.PrimeDivisor X))
    (hT : ∀ Γ ∈ S, x ∈ Γ.support ↔ Γ ∈ T) :
    discrep sX n K Δ ≤ (((1 - ∑ Γ ∈ T, Δ.coeff Γ : ℚ) : ℝ) : EReal) := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
  have h := discrep_le_of_coheight_eq_two hX hsm hK Δ x hcod fun Γ hΓ hxΓ =>
    stalk_not_le_sq_of_isSNC hsnc x (hS hΓ) hxΓ
  rwa [sum_ite_coeff_eq_sum Δ T _ fun Γ hΓ => hT Γ (hS hΓ)] at h

/-- **The blow-up of a codimension two stratum of an snc divisor, through a given point.** On a
smooth variety of dimension `n` with an snc divisor `∑_{G ∈ S} G`, let `E ≠ F` be components in
`S` and `p ∈ E ∩ F`. There is an exceptional divisor `D` over `X`, the blow-up of a component of
`E ∩ F` through `p` near its generic point, whose center lies on `E` and on `F` and specializes to
`p`, with `a(D, X, Δ) = 1 - coeff_E Δ - coeff_F Δ` for every `ℚ`-divisor `Δ` supported on `S`. -/
public theorem exists_isExceptional_isDiscrepancy_eq_one_sub_sub_of_mem
    (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {S : Finset (PrimeDivisor X)}
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    {E F : PrimeDivisor X} (hE : E ∈ S) (hF : F ∈ S) (hEF : E ≠ F)
    {p : X} (hpE : p ∈ E.support) (hpF : p ∈ F.support) :
    ∃ D : DivisorOver k sX, D.IsExceptional ∧
      D.f D.E.genericPoint ∈ E.support ∧ D.f D.E.genericPoint ∈ F.support ∧
      D.f D.E.genericPoint ⤳ p ∧
      ∀ (K : Divisor X) (Δ : QDivisor X), Δ.support ⊆ S → ∀ c : ℚ,
        IsDiscrepancy sX n K Δ D c → c = 1 - Δ.coeff E - Δ.coeff F := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
  have := isRegularLocalRing_stalk_of_smooth_over_field sX p
  obtain ⟨N, z, j, hz, hj, hI⟩ := exists_at_of_isSNC hsnc p
  have hab : j ⟨E, hE, hpE⟩ ≠ j ⟨F, hF, hpF⟩ := fun h => hEF (congrArg Subtype.val (hj h))
  obtain ⟨x, hxp, hcod, hmem⟩ := exists_specializes_coheight_eq_two p hz hab
  have hxE : x ∈ E.support := hmem E.idealSheaf (by
    rw [hI ⟨E, hE, hpE⟩]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
  have hxF : x ∈ F.support := hmem F.idealSheaf (by
    rw [hI ⟨F, hF, hpF⟩]
    exact Ideal.span_mono
      (Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field sX x
  obtain ⟨D, hDx, hord, hσ⟩ := exists_blowupDivisor hX hn x hreg hcod
  refine ⟨D, (DivisorOver.isExceptional_iff_two_le_coheight hX D).mpr (by rw [hDx, hcod]),
    hDx ▸ hxE, hDx ▸ hxF, hDx ▸ hxp, fun K Δ hS c hc => ?_⟩
  have hval := isDiscrepancy_eq_one_sub_sum x hreg
    (fun Γ hΓ hxΓ => stalk_not_le_sq_of_isSNC hsnc x (hS hΓ) hxΓ) D hDx hord hσ hc
  rw [sum_ite_coeff_eq_sum Δ {E, F} _ fun Γ hΓ => ?_, Finset.sum_pair hEF] at hval
  · rw [hval]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    refine ⟨fun hxΓ => eq_or_eq_of_isSNC_of_coheight_eq_two hsnc hcod hEF hE hF (hS hΓ) hxE hxF
      hxΓ, ?_⟩
    rintro (rfl | rfl)
    exacts [hxE, hxF]

/-- **The blow-up of a codimension two stratum of an snc divisor.** On a smooth variety of
dimension `n` with an snc divisor `∑_{G ∈ S} G`, two distinct meeting components `E, F ∈ S` give
an exceptional divisor `D` over `X`, the blow-up of a component of `E ∩ F` near its generic point,
with `a(D, X, Δ) = 1 - coeff_E Δ - coeff_F Δ` for every `ℚ`-divisor `Δ` supported on `S`. -/
public theorem exists_isExceptional_isDiscrepancy_eq_one_sub_sub (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : topologicalKrullDim X = n)
    {S : Finset (PrimeDivisor X)}
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    {E F : PrimeDivisor X} (hE : E ∈ S) (hF : F ∈ S) (hEF : E ≠ F)
    (hmeet : (E.support ∩ F.support).Nonempty) :
    ∃ D : DivisorOver k sX, D.IsExceptional ∧ ∀ (K : Divisor X) (Δ : QDivisor X),
      Δ.support ⊆ S → ∀ c : ℚ, IsDiscrepancy sX n K Δ D c → c = 1 - Δ.coeff E - Δ.coeff F := by
  obtain ⟨p, hpE, hpF⟩ := hmeet
  obtain ⟨D, hD, -, -, -, hc⟩ :=
    exists_isExceptional_isDiscrepancy_eq_one_sub_sub_of_mem hX hsm hn hsnc hE hF hEF hpE hpF
  exact ⟨D, hD, hc⟩

/-- **`discrep(X, Δ) ≤ 1 - a_E - a_F`** for two distinct components `E`, `F` that meet: the
divisor of `exists_isExceptional_isDiscrepancy_eq_one_sub_sub` has this discrepancy. -/
private theorem discrep_le_pair (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Δ : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)} (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    {E F : MMP.Mori.PrimeDivisor X} (hE : E ∈ S) (hF : F ∈ S) (hEF : E ≠ F)
    (hmeet : (E.support ∩ F.support).Nonempty) :
    discrep sX n K Δ ≤ (((1 - Δ.coeff E - Δ.coeff F : ℚ) : ℝ) : EReal) := by
  obtain ⟨D, hD, hDc⟩ := exists_isExceptional_isDiscrepancy_eq_one_sub_sub hX hsm
    hK.topologicalKrullDim_eq hsnc hE hF hEF hmeet
  have hP : IsPair sX Δ :=
    isPair_of_isCanonicalDivisor hX hK (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  rw [← hDc K Δ hS a ha]
  exact discrep_le hD ha

/-- **`discrep(X, Δ) ≤ 1 - a_E`** for a component `E`: blow up a codimension one subvariety of
`E` through a closed point of `E` on no other component. -/
private theorem discrep_le_single (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : 2 ≤ n) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n)
    {Δ : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)} (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    {E : MMP.Mori.PrimeDivisor X} (hE : E ∈ S) :
    discrep sX n K Δ ≤ (((1 - Δ.coeff E : ℚ) : ℝ) : EReal) := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set C : Set X := ⋃ G ∈ S.erase E, (G.support : Set X) with hC
  have hCc : IsClosed C :=
    (S.erase E).finite_toSet.isClosed_biUnion fun G _ => G.idealSheaf.support.isClosed
  have hne : ((E.support : Set X) ∩ Cᶜ).Nonempty := by
    refine ⟨E.genericPoint, MMP.Positivity.PrimeDivisor.genericPoint_mem_support' E, ?_⟩
    simp only [hC, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro G hG
    exact MMP.Threefold.Resolution.genericPoint_notMem_support_of_ne
      (Finset.ne_of_mem_erase hG).symm
  obtain ⟨p, ⟨hpE, hpC⟩, hpcl⟩ := nonempty_inter_closedPoints hne
    (E.idealSheaf.support.isClosed.isLocallyClosed.inter hCc.isOpen_compl.isLocallyClosed)
  rw [mem_closedPoints_iff] at hpcl
  have hcp := coheight_eq_of_isClosed sX hK.topologicalKrullDim_eq hpcl
  have := isRegularLocalRing_stalk_of_smooth_over_field sX p
  obtain ⟨N, z, j, hz, -, hI⟩ := exists_at_of_isSNC hsnc p
  have hN : N = n := by
    have := coheight_eq_of_isRegularSystemOfParameters hz
    rw [hcp] at this
    exact_mod_cast this.symm
  set a := j ⟨E, hE, hpE⟩
  have hN2 : 2 ≤ N := hN ▸ hn
  set b : Fin N := if (a : ℕ) = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩ with hb
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    by_cases h0 : (a : ℕ) = 0
    · rw [hb, ite_eq_left h0] at hv
      change (a : ℕ) = 1 at hv
      omega
    · rw [hb, ite_eq_right h0] at hv
      exact h0 hv
  obtain ⟨x, hxp, hcod, hmem⟩ := exists_specializes_coheight_eq_two p hz hab
  have hxE : x ∈ E.support := hmem E.idealSheaf (by
    rw [hI ⟨E, hE, hpE⟩]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))
  have h := discrep_le_of_isSNC_of_coheight_eq_two hX hsm hK hS hsnc hcod {E}
    fun Γ hΓ => by
      rw [Finset.mem_singleton]
      refine ⟨fun hxΓ => ?_, fun h => h ▸ hxE⟩
      by_contra hΓE
      have hpΓ : p ∈ Γ.support := hxp.mem_closed Γ.idealSheaf.support.isClosed hxΓ
      exact hpC (Set.mem_biUnion (Finset.mem_erase.mpr ⟨hΓE, hΓ⟩) hpΓ)
  rwa [Finset.sum_singleton] at h

/-- **`discrep(X, Δ) ≤ 1`**: blow up a codimension two subvariety through a closed point on no
component. -/
private theorem discrep_le_one (hX : IsNormalVariety k sX)
    (hsm : IsSmoothScheme sX) {n : ℕ} (hn : 2 ≤ n) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n)
    {Δ : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)} (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ))) :
    discrep sX n K Δ ≤ 1 := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set C : Set X := ⋃ G ∈ S, (G.support : Set X) with hC
  have hCc : IsClosed C :=
    S.finite_toSet.isClosed_biUnion fun G _ => G.idealSheaf.support.isClosed
  have hne : (Set.univ ∩ Cᶜ).Nonempty := by
    refine ⟨genericPoint X, trivial, ?_⟩
    simp only [hC, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro G _
    exact MMP.Threefold.Mori.CanonUniq.genericPoint_notMem_support G
  obtain ⟨p, ⟨-, hpC⟩, hpcl⟩ := nonempty_inter_closedPoints hne
    (isClosed_univ.isLocallyClosed.inter hCc.isOpen_compl.isLocallyClosed)
  rw [mem_closedPoints_iff] at hpcl
  have hcp := coheight_eq_of_isClosed sX hK.topologicalKrullDim_eq hpcl
  have := isRegularLocalRing_stalk_of_smooth_over_field sX p
  obtain ⟨N, z, -, hz, -, -⟩ := exists_at_of_isSNC hsnc p
  have hN : N = n := by
    have := coheight_eq_of_isRegularSystemOfParameters hz
    rw [hcp] at this
    exact_mod_cast this.symm
  have hN2 : 2 ≤ N := hN ▸ hn
  have hab : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  obtain ⟨x, hxp, hcod, -⟩ := exists_specializes_coheight_eq_two p hz hab
  have h := discrep_le_of_isSNC_of_coheight_eq_two hX hsm hK hS hsnc hcod ∅
    fun Γ hΓ => by
      simp only [Finset.notMem_empty, iff_false]
      intro hxΓ
      exact hpC (Set.mem_biUnion hΓ (hxp.mem_closed Γ.idealSheaf.support.isClosed hxΓ))
  simpa using h

end UpperBound

/-! ### The lower bound -/

/-- **Alternating maps on logarithmic vectors.** If the vectors `v_i`, `i ∈ T`, lie in
`ϖ M + R t` for a fixed `t ∈ M`, then `φ(v) ∈ ϖ^{|T| - 1} N`; if moreover some `v_{i₀}`, `i₀ ∉ T`,
equals `t`, then `φ(v) ∈ ϖ^{|T|} N`. -/
private theorem exists_eq_pow_smul_of_mem {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (φ : M [⋀^ι]→ₗ[R] N) (ϖ : R)
    (t : M) (T : Finset ι) :
    ∀ v : ι → M, (∀ i ∈ T, ∃ (a : M) (b : R), v i = ϖ • a + b • t) →
      (∃ η, φ v = ϖ ^ (T.card - 1) • η) ∧
        ((∃ i₀ ∉ T, v i₀ = t) → ∃ η, φ v = ϖ ^ T.card • η) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro v _
    exact ⟨⟨φ v, by simp⟩, fun _ => ⟨φ v, by simp⟩⟩
  | insert i T hiT ih =>
    intro v hv
    obtain ⟨a, b, hvi⟩ := hv i (Finset.mem_insert_self i T)
    have hsplit : φ v = ϖ • φ (Function.update v i a) + b • φ (Function.update v i t) := by
      conv_lhs => rw [← Function.update_eq_self i v, hvi]
      rw [AlternatingMap.map_update_add, AlternatingMap.map_update_smul,
        AlternatingMap.map_update_smul]
    have hT : ∀ w : M, ∀ j ∈ T, ∃ (a : M) (b : R), Function.update v i w j = ϖ • a + b • t := by
      intro w j hj
      have hji : j ≠ i := fun h => hiT (h ▸ hj)
      rw [Function.update_of_ne hji]
      exact hv j (Finset.mem_insert_of_mem hj)
    have hcard := Finset.card_insert_of_notMem hiT
    obtain ⟨⟨η₁, h₁⟩, -⟩ := ih (Function.update v i a) (hT a)
    obtain ⟨-, h₂⟩ := ih (Function.update v i t) (hT t)
    obtain ⟨η₂, h₂⟩ := h₂ ⟨i, hiT, by simp⟩
    refine ⟨?_, ?_⟩
    · rw [hcard, Nat.add_sub_cancel]
      rcases Nat.eq_zero_or_pos T.card with h0 | hpos
      · exact ⟨φ v, by rw [h0, pow_zero, one_smul]⟩
      · rw [hsplit, h₁, h₂]
        refine ⟨η₁ + b • η₂, ?_⟩
        rw [smul_smul, ← pow_succ', Nat.sub_add_cancel hpos, smul_add, smul_comm b]
    · rintro ⟨i₀, hi₀, hvi₀⟩
      have hi₀i : i₀ ≠ i := fun h => hi₀ (h ▸ Finset.mem_insert_self i T)
      have hi₀T : i₀ ∉ T := fun h => hi₀ (Finset.mem_insert_of_mem h)
      have hz : φ (Function.update v i t) = 0 :=
        AlternatingMap.map_eq_zero_of_eq φ _ (i := i) (j := i₀)
          (by rw [Function.update_self, Function.update_of_ne hi₀i, hvi₀]) hi₀i.symm
      obtain ⟨-, h₃⟩ := ih (Function.update v i a) (hT a)
      obtain ⟨η₃, h₃⟩ := h₃ ⟨i₀, hi₀T, by rw [Function.update_of_ne hi₀i, hvi₀]⟩
      refine ⟨η₃, ?_⟩
      rw [hsplit, hz, smul_zero, add_zero, h₃, smul_smul, ← pow_succ', hcard]

open scoped TensorProduct in
/-- **Regular parameters are part of a basis of the differentials.** On an integral scheme `X`
of dimension `n` smooth over a perfect field, a regular system of parameters
`z_1, …, z_c` of `𝒪_{X,x}` extends to a basis `dz_1, …, dz_c, w_{c+1}, …, w_n` of
`Ω_{𝒪_{X,x}/k}`; its wedge generates `Ω^n_{𝒪_{X,x}/k}` and has nonzero image in `Ω^n_{k(X)/k}`. -/
private theorem exists_topForms_generator_ιMulti {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] (sX : X ⟶ Spec (.of k)) [Smooth sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (x : X) {c : ℕ} {z : Fin c → X.presheaf.stalk x}
    (hz : IsRegularSystemOfParameters z) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX x
    ∃ (hcn : c ≤ n) (w : Fin n → Ω[X.presheaf.stalk x⁄k]),
      (∀ i : Fin c, w (Fin.castLE hcn i) = KaehlerDifferential.D k _ (z i)) ∧
      Submodule.span (X.presheaf.stalk x) {exteriorPower.ιMulti (X.presheaf.stalk x) n w} = ⊤ ∧
      topFormsMap k (X.presheaf.stalk x) X.functionField n
        (exteriorPower.ιMulti (X.presheaf.stalk x) n w) ≠ 0 := by
  classical
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX x
  obtain ⟨h1, h2, h3⟩ := MMP.Flips.ResolutionInputs.stalk_facts sX x
  have := h1
  have := h2
  have := h3
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.EssFiniteType.of_surjective
      (IsScalarTower.toAlgHom k (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x))) IsLocalRing.residue_surjective
  have : Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    Algebra.FormallySmooth.of_perfectField
  obtain ⟨ht0, hli, -⟩ := MMP.Flips.ResolutionInputs.cotangent_basis_of_regular z hz.1 hz.2
  have hli' := MMP.Flips.ResolutionInputs.linearIndependent_tmul_D k z ht0 hli
  have : Module.Projective (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    ((Algebra.formallySmooth_iff _ _).mp ‹_›).1
  obtain ⟨e, v, hvS, hvli, hvsp⟩ := MMP.Flips.ResolutionInputs.exists_sumElim_basis _ hli' _
    (MMP.Flips.ResolutionInputs.span_tmul_range_D k)
  choose r hr using hvS
  have hu : (TensorProduct.mk (X.presheaf.stalk x) (IsLocalRing.ResidueField (X.presheaf.stalk x))
      Ω[X.presheaf.stalk x⁄k] 1 ∘ fun i => KaehlerDifferential.D k (X.presheaf.stalk x)
        (Sum.elim z r i)) = Sum.elim (fun i => (1 : IsLocalRing.ResidueField (X.presheaf.stalk x))
          ⊗ₜ KaehlerDifferential.D k (X.presheaf.stalk x) (z i)) v := by
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact hr j
  have hbij : Function.Bijective (Finsupp.linearCombination (X.presheaf.stalk x)
      (fun i => KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim z r i))) := by
    apply Module.IsLocalRing.linearCombination_bijective_of_flat
    rw [hu]
    refine ⟨hvli, ?_⟩
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact top_le_iff.mp hvsp
  let B := MMP.Flips.ResolutionInputs.basisOfBijective _ hbij
  have hB : ∀ i, B i = KaehlerDifferential.D k (X.presheaf.stalk x) (Sum.elim z r i) :=
    MMP.Flips.ResolutionInputs.basisOfBijective_apply _ hbij
  -- the rank of the differentials is `n`
  obtain ⟨n', ⟨b⟩, hn'⟩ := MMP.Threefold.Resolution.exists_basis_kaehler_stalk sX x
  have hnn' : n' = n := by
    have := (topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x).trans hn'
    rw [hn] at this
    exact_mod_cast this.symm
  have hce : c + e = n := by
    have := Module.Basis.indexEquiv b B
    have h := Fintype.card_congr this
    rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
    omega
  let b' : Module.Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] :=
    B.reindex (finSumFinEquiv.trans (finCongr hce))
  have hcn : c ≤ n := by omega
  refine ⟨hcn, b', fun i => ?_, ?_, ?_⟩
  · simp only [b', Module.Basis.reindex_apply, Equiv.symm_trans_apply, finCongr_symm,
      finCongr_apply]
    have : Fin.cast hce.symm (Fin.castLE hcn i) = Fin.castAdd e i := Fin.ext rfl
    rw [this, finSumFinEquiv_symm_apply_castAdd, hB]
    rfl
  · rw [eq_top_iff]
    intro ω _
    obtain ⟨t, ht⟩ := (MMP.Intersection.bijective_smul_ιMulti_basis b').2 ω
    rw [← ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · have := MMP.Threefold.Resolution.nontrivial_topForms sX hn
    refine topFormsMap_ne_zero_of_span_eq_top ?_
    rw [eq_top_iff]
    intro ω _
    obtain ⟨t, ht⟩ := (MMP.Intersection.bijective_smul_ιMulti_basis b').2 ω
    rw [← ht]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- `d(u ϖ^e) = ϖ^{e-1}(ϖ du + e u dϖ)` for `e ≥ 1`. -/
private theorem D_mul_pow {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (u ϖ : R)
    {e : ℕ} (he : 1 ≤ e) :
    KaehlerDifferential.D k R (u * ϖ ^ e) = ϖ ^ (e - 1) •
      (ϖ • KaehlerDifferential.D k R u + ((e : R) * u) • KaehlerDifferential.D k R ϖ) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [Derivation.leibniz, Derivation.leibniz_pow]
  simp only [add_tsub_cancel_left]
  rw [pow_add, pow_one, ← Nat.cast_smul_eq_nsmul R]
  module

/-- **Logarithmic poles are simple.** Let `R` be a discrete valuation ring with uniformizer `ϖ`
over a field `k`, and `σ` a generator of `Ω^n_{R/k}` with nonzero image in `Ω^n_{K/k}`. If
`h σ = dg_1 ∧ ⋯ ∧ dg_c ∧ v_{c+1} ∧ ⋯ ∧ v_n` with `c ≥ 1` and `g_i = u_i ϖ^{e_i}`, `u_i` units
and `e_i ≥ 1`, then `h ∈ 𝔪^{e_1 + ⋯ + e_c - 1}`: writing `dg_i = g_i dlog g_i`, the wedge of the
logarithmic forms `dlog g_i ∈ Ω_R + R dϖ/ϖ` has at most a simple pole. -/
private theorem mem_maximalIdeal_pow_of_ιMulti_eq_smul {k R K : Type*} [Field k] [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R] [Field K] [Algebra k K] [Algebra R K]
    [IsScalarTower k R K] [IsFractionRing R K] {n c : ℕ} (hcn : c ≤ n) (hc : 1 ≤ c) {ϖ : R}
    (hϖ : Irreducible ϖ) {σ : ⋀[R]^n Ω[R⁄k]} (hσ : Submodule.span R {σ} = ⊤)
    (h0 : topFormsMap k R K n σ ≠ 0) (v : Fin n → Ω[R⁄k]) (u : Fin c → Rˣ) (e : Fin c → ℕ)
    (he : ∀ i, 1 ≤ e i)
    (hv : ∀ i : Fin c, v (Fin.castLE hcn i) = KaehlerDifferential.D k R (u i * ϖ ^ e i))
    {h : R} (hh : exteriorPower.ιMulti R n v = h • σ) :
    h ∈ IsLocalRing.maximalIdeal R ^ (∑ i, e i - 1) := by
  classical
  -- the data indexed by `Fin n`
  let ee : Fin n → ℕ := fun i => if hi : (i : ℕ) < c then e ⟨i, hi⟩ else 0
  let uu : Fin n → R := fun i => if hi : (i : ℕ) < c then (u ⟨i, hi⟩ : R) else 1
  let w : Fin n → Ω[R⁄k] := fun i => if (i : ℕ) < c then
    ϖ • KaehlerDifferential.D k R (uu i) + ((ee i : R) * uu i) • KaehlerDifferential.D k R ϖ
    else v i
  have hvw : v = fun i => ϖ ^ (ee i - 1) • w i := by
    funext i
    by_cases hi : (i : ℕ) < c
    · have := hv ⟨i, hi⟩
      simp only [Fin.castLE_mk] at this
      simp only [w, ee, uu, dite_eq_left hi, ite_eq_left hi]
      rw [this]
      exact D_mul_pow _ _ (he _)
    · simp [w, ee, hi]
  set T : Finset (Fin n) := Finset.univ.map (Fin.castLEEmb hcn) with hT
  have hTc : T.card = c := by simp [hT]
  have hwT : ∀ i ∈ T, ∃ (a : Ω[R⁄k]) (b : R), w i = ϖ • a + b • KaehlerDifferential.D k R ϖ := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    have hj : ((Fin.castLEEmb hcn j : Fin n) : ℕ) < c := j.2
    refine ⟨KaehlerDifferential.D k R (uu (Fin.castLEEmb hcn j)),
      (ee (Fin.castLEEmb hcn j) : R) * uu (Fin.castLEEmb hcn j), ?_⟩
    simp only [w, ite_eq_left hj]
  obtain ⟨⟨η, hη⟩, -⟩ := exists_eq_pow_smul_of_mem (M := Ω[R⁄k]) (N := ⋀[R]^n Ω[R⁄k])
    (exteriorPower.ιMulti R n) ϖ (KaehlerDifferential.D k R ϖ) T w hwT
  have hprod : exteriorPower.ιMulti R n v = ϖ ^ (∑ i, (ee i - 1)) • exteriorPower.ιMulti R n w := by
    rw [hvw, AlternatingMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top : η ∈ _)
  -- the exponent
  have hsum : ∑ i, (ee i - 1) + (c - 1) = ∑ i, e i - 1 := by
    have h1 : ∑ i : Fin n, (ee i - 1) = ∑ i : Fin c, (e i - 1) := by
      rw [← Finset.sum_subset (Finset.subset_univ T) fun i _ hiT => ?_]
      · rw [hT, Finset.sum_map]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : ((Fin.castLEEmb hcn j : Fin n) : ℕ) < c := j.2
        simp only [ee, dite_eq_left hj]
        rfl
      · have hi : ¬ (i : ℕ) < c := fun hi =>
          hiT (Finset.mem_map.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, Fin.ext rfl⟩)
        simp [ee, hi]
    have h2 : ∑ i : Fin c, (e i - 1) + c = ∑ i, e i := by
      have : ∑ i : Fin c, e i = ∑ i : Fin c, ((e i - 1) + 1) :=
        Finset.sum_congr rfl fun i _ => (Nat.sub_add_cancel (he i)).symm
      rw [this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
    omega
  have hrel : h • σ = (ϖ ^ (∑ i, e i - 1) * r) • σ := by
    rw [← hh, hprod, hη, hTc, ← hr, smul_smul, smul_smul, ← pow_add, hsum]
  -- cancel `σ` in `Ω^n_{K/k}`
  have hK : algebraMap R K h = algebraMap R K (ϖ ^ (∑ i, e i - 1) * r) := by
    have := congrArg (topFormsMap k R K n) hrel
    rw [LinearMap.map_smul (topFormsMap k R K n) h σ,
      LinearMap.map_smul (topFormsMap k R K n) (ϖ ^ (∑ i, e i - 1) * r) σ,
      ← algebraMap_smul K h (topFormsMap k R K n σ),
      ← algebraMap_smul K (ϖ ^ (∑ i, e i - 1) * r) (topFormsMap k R K n σ)] at this
    have h' := sub_eq_zero.mpr this
    rw [← sub_smul, smul_eq_zero] at h'
    exact sub_eq_zero.mp (h'.resolve_right h0)
  rw [IsFractionRing.injective R K hK]
  refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
  exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit

/-- Along a prime divisor `F` with uniformizer `ϖ`, the order of `u ϖ^m`, `u` a unit, is `m`. -/
private theorem ord_unit_mul_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : MMP.Mori.PrimeDivisor Y) [IsDiscreteValuationRing F.localRing] {ϖ : F.localRing}
    (hϖ : Irreducible ϖ) (v : F.localRingˣ) (m : ℕ) :
    Y.ord (algebraMap F.localRing Y.functionField (v * ϖ ^ m)) F.genericPoint = m := by
  have hϖK : algebraMap F.localRing Y.functionField ϖ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero
      hϖ.ne_zero)
  have hord1 : Y.ord (algebraMap F.localRing Y.functionField ϖ) F.genericPoint = 1 := by
    rw [Scheme.ord_eq_iff F.coheight_genericPoint hϖK]
    have : Ring.KrullDimLE 1 F.localRing := krullDimLE_of_coheight_le F.coheight_genericPoint.le
    exact Ring.ordFrac_irreducible hϖ
  have hvK : algebraMap F.localRing Y.functionField v ≠ 0 := (v.isUnit.map _).ne_zero
  rw [map_mul, Scheme.ord_mul hvK (by rw [map_pow]; exact pow_ne_zero _ hϖK),
    F.ord_algebraMap_of_isUnit v.isUnit, map_pow, ← zpow_natCast,
    MMP.Mori.ord_zpow _ hϖK, hord1]
  simp

/-- Along a prime divisor `F` with uniformizer `ϖ`, a nonzero element of `𝔪_F^N` has order at
least `N`. -/
private theorem le_ord_of_mem_pow {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (F : MMP.Mori.PrimeDivisor Y) [IsDiscreteValuationRing F.localRing] {h : F.localRing}
    (hh : h ≠ 0) {N : ℕ} (hN : h ∈ IsLocalRing.maximalIdeal F.localRing ^ N) :
    (N : ℤ) ≤ Y.ord (algebraMap F.localRing Y.functionField h) F.genericPoint := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.localRing
  obtain ⟨M, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hh hϖ
  rw [ord_unit_mul_pow F hϖ v M, Nat.cast_le]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Units.dvd_mul_left] at hN
  exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp hN

/-- **The pull-back of a top form along a birational morphism is nonzero at a prime divisor.**
If `f : Y ⟶ X` is dominant with `f^* : k(X) ≅ k(Y)`, a top form `σ` at `f(η_F)` with nonzero
image in `Ω^d_{k(X)/k}` has nonzero image in `Ω^d_{𝒪_{Y,F}/k}`. -/
private theorem topFormsMap_stalk_localRing_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hbij : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d)
    (F : MMP.Mori.PrimeDivisor Y)
    {σA : letI := stalkAlgebra sX (f F.genericPoint)
      ⋀[X.presheaf.stalk (f F.genericPoint)]^d Ω[X.presheaf.stalk (f F.genericPoint)⁄k]}
    (h0A : letI := stalkAlgebra sX (f F.genericPoint)
      letI := functionFieldAlgebra sX
      haveI := isScalarTower_stalk_functionField sX (f F.genericPoint)
      topFormsMap k (X.presheaf.stalk (f F.genericPoint)) X.functionField d σA ≠ 0) :
    letI := stalkAlgebra sX (f F.genericPoint)
    letI := stalkAlgebra (f ≫ sX) F.genericPoint
    letI := (f.stalkMap F.genericPoint).hom.toAlgebra
    haveI := MMP.Threefold.Resolution.isScalarTower_stalkMap sX f F.genericPoint
    topFormsMap k (X.presheaf.stalk (f F.genericPoint)) F.localRing d σA ≠ 0 := by
  let := stalkAlgebra sX (f F.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (f F.genericPoint)
  let := stalkAlgebra (f ≫ sX) F.genericPoint
  let := functionFieldAlgebra (f ≫ sX)
  have := isScalarTower_stalk_functionField (f ≫ sX) F.genericPoint
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  let := (f.stalkMap F.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX f F.genericPoint
  let : Algebra (X.presheaf.stalk (f F.genericPoint)) Y.functionField :=
    ((algebraMap X.functionField Y.functionField).comp
      (algebraMap (X.presheaf.stalk (f F.genericPoint)) X.functionField)).toAlgebra
  have : IsScalarTower (X.presheaf.stalk (f F.genericPoint)) X.functionField Y.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (X.presheaf.stalk (f F.genericPoint)) F.localRing Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      MMP.Mori.functionFieldMap_algebraMap_stalk f F.genericPoint a
  have : IsScalarTower k (X.presheaf.stalk (f F.genericPoint)) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [IsScalarTower.algebraMap_apply k X.functionField Y.functionField,
        IsScalarTower.algebraMap_apply k (X.presheaf.stalk (f F.genericPoint)) X.functionField]
      rfl
  intro h0
  have e1 := MMP.Threefold.Mori.Helpers.topFormsMap_comp (k := k) (A := X.presheaf.stalk
    (f F.genericPoint)) (B := F.localRing) (C := Y.functionField) (d := d) σA
  have e2 := MMP.Threefold.Mori.Helpers.topFormsMap_comp (k := k) (A := X.presheaf.stalk
    (f F.genericPoint)) (B := X.functionField) (C := Y.functionField) (d := d) σA
  rw [h0, map_zero, ← e2] at e1
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sX f hbij hd
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp
    (hω₀.1 ▸ Submodule.mem_top : topFormsMap k (X.presheaf.stalk (f F.genericPoint))
      X.functionField d σA ∈ _)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact h0A ht.symm
  rw [← ht, map_smul, ← algebraMap_smul Y.functionField t] at e1
  exact smul_ne_zero ((map_ne_zero _).mpr ht0) hω₀.2.2 e1.symm

open scoped Classical in
/-- **The lower bound for one exceptional divisor.** Let `(Y, f, E)` be exceptional over a smooth
variety `X`, with center `x₀ = f(η_E)` of codimension `c ≥ 2`, and let `T` be the components of
the snc divisor `∑_{G ∈ S} G` through `x₀`, so that `T ⊆ S`, `|T| ≤ c` and
`a(E, X, Δ) ≥ -1 + ∑_{G ∈ T} (1 - a_G) + (c - |T|)`. -/
public theorem le_isDiscrepancy_of_isSNC {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {Δ : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hS : Δ.support ⊆ S) (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (hcoeff : ∀ E ∈ S, Δ.coeff E ≤ 1) (D : DivisorOver k sX) (hD : D.IsExceptional) {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) :
    ∃ (c : ℕ) (T : Finset (MMP.Mori.PrimeDivisor X)),
      (c : ℕ∞) = Order.coheight (D.f D.E.genericPoint) ∧
      T = S.filter (fun G => D.f D.E.genericPoint ∈ G.support) ∧ 2 ≤ c ∧ T.card ≤ c ∧ T ⊆ S ∧
      (∀ G ∈ T, D.f D.E.genericPoint ∈ G.support) ∧
      -1 + ∑ G ∈ T, (1 - Δ.coeff G) + ((c : ℚ) - T.card) ≤ a := by
  classical
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : Smooth sX := (isSmoothScheme_iff sX).mp hsm
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have hbij : Function.Bijective (functionFieldMap D.f) :=
    D.isBirationalMorphism.functionFieldMap_bijective
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hdY : (letI := functionFieldAlgebra (D.f ≫ sX)
      (Algebra.trdeg k D.Y.functionField).toNat = n) := by
    rwa [← trdeg_functionField_eq_of_bijective sX D.f hbij]
  have hcod : 2 ≤ Order.coheight (D.f D.E.genericPoint) :=
    (DivisorOver.isExceptional_iff_two_le_coheight hX D).mp hD
  have hreg := isRegularLocalRing_stalk_of_smooth_over_field sX (D.f D.E.genericPoint)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk (D.f D.E.genericPoint))
  obtain ⟨c, z, j, hz, hj, hI⟩ := exists_at_of_isSNC hsnc (D.f D.E.genericPoint)
  have hc2 : 2 ≤ c := by
    rw [coheight_eq_of_isRegularSystemOfParameters hz] at hcod
    exact_mod_cast hcod
  set T := S.filter (fun G => D.f D.E.genericPoint ∈ G.support) with hT
  have hTmem : ∀ G ∈ T, G ∈ S ∧ D.f D.E.genericPoint ∈ G.support :=
    fun G hG => Finset.mem_filter.mp hG
  let jT : MMP.Mori.PrimeDivisor X → Fin c := fun G =>
    if h : G ∈ S ∧ D.f D.E.genericPoint ∈ G.support then j ⟨G, h⟩ else ⟨0, by omega⟩
  have hjT : ∀ G (h : G ∈ T), jT G = j ⟨G, hTmem G h⟩ := fun G h => dite_eq_left _
  have hinj : Set.InjOn jT T := fun G hG G' hG' h => by
    rw [hjT G hG, hjT G' hG'] at h
    exact congrArg Subtype.val (hj h)
  have hcard : T.card ≤ c := by
    have := Finset.card_le_card_of_injOn jT (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hinj
    simpa using this
  refine ⟨c, T, (coheight_eq_of_isRegularSystemOfParameters hz).symm, rfl, hc2, hcard,
    Finset.filter_subset _ _, fun G hG => (hTmem G hG).2, ?_⟩
  -- the discrepancy data
  obtain ⟨-, -, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  -- a generator `σ_A = dz_1 ∧ ⋯ ∧ dz_c ∧ w` at `x₀`
  obtain ⟨hcn, w, hw, hσA, h0A⟩ :=
    exists_topForms_generator_ιMulti sX hn (D.f D.E.genericPoint) hz
  let := stalkAlgebra sX (D.f D.E.genericPoint)
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX (D.f D.E.genericPoint)
  let := stalkAlgebra (D.f ≫ sX) D.E.genericPoint
  let := functionFieldAlgebra (D.f ≫ sX)
  have := isScalarTower_stalk_functionField (D.f ≫ sX) D.E.genericPoint
  let := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sX D.f D.E.genericPoint
  have := D.E.isDiscreteValuationRing_localRing
  -- a generator `σ_B` at `η_E`, and `f^♯ σ_A = h' σ_B`
  obtain ⟨σB, hσB, h0B⟩ := D.E.exists_topForms_generator (sX := D.f ≫ sX) hdY
  obtain ⟨h', hrel⟩ : ∃ h' : D.E.localRing,
      topFormsMap k (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing n
        (exteriorPower.ιMulti (X.presheaf.stalk (D.f D.E.genericPoint)) n w) = h' • σB := by
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hσB ▸ Submodule.mem_top :
      topFormsMap k (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing n
        (exteriorPower.ιMulti (X.presheaf.stalk (D.f D.E.genericPoint)) n w) ∈ _)
    exact ⟨t, ht.symm⟩
  have hne := topFormsMap_stalk_localRing_ne_zero sX D.f hbij hd D.E h0A
  have hh'0 : h' ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hrel
    exact hne hrel
  have hh : algebraMap D.E.localRing D.Y.functionField h' ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hh'0)
  have hord := MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sX D.f D.E hσA h0A
    hσB h0B h' hrel hh hτ.1
  -- the parameters along `E`: `f^♯ z_i = u_i ϖ^{e_i}` with `e_i ≥ 1`
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D.E.localRing
  have hzm : ∀ i, z i ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (D.f D.E.genericPoint)) :=
    fun i => hz.1 ▸ Ideal.subset_span ⟨i, rfl⟩
  have hz0 : ∀ i, (D.f.stalkMap D.E.genericPoint).hom (z i) ≠ 0 := by
    intro i h0
    have hzi : z i ≠ 0 := fun h => notMem_maximalIdeal_sq hz i (h ▸ Submodule.zero_mem _)
    have := MMP.Mori.functionFieldMap_algebraMap_stalk D.f D.E.genericPoint (z i)
    rw [h0, map_zero] at this
    exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hzi)) this
  have hzmE : ∀ i, (D.f.stalkMap D.E.genericPoint).hom (z i) ∈
      IsLocalRing.maximalIdeal D.E.localRing := fun i =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
      (IsLocalRing.mem_maximalIdeal _).mp (hzm i) (isUnit_of_map_unit _ _ hu)
  choose e u hzu using fun i =>
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hz0 i) hϖ
  have he : ∀ i, 1 ≤ e i := by
    intro i
    by_contra h0
    have h0 : e i = 0 := by omega
    have := hzmE i
    rw [hzu i, h0, pow_zero, mul_one] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this (u i).isUnit
  have hordz : ∀ i, D.Y.ord (algebraMap D.E.localRing D.Y.functionField
      ((D.f.stalkMap D.E.genericPoint).hom (z i))) D.E.genericPoint = e i := by
    intro i
    rw [hzu i]
    exact ord_unit_mul_pow D.E hϖ (u i) (e i)
  -- the logarithmic estimate: `ord_E h' ≥ ∑ e_i - 1`
  have hvi : ∀ i : Fin c, KaehlerDifferential.map k k (X.presheaf.stalk (D.f D.E.genericPoint))
      D.E.localRing (w (Fin.castLE hcn i)) =
        KaehlerDifferential.D k D.E.localRing (u i * ϖ ^ e i) := by
    intro i
    rw [hw i, KaehlerDifferential.map_D, ← hzu i]
    rfl
  have hrel' : exteriorPower.ιMulti D.E.localRing n (fun i => KaehlerDifferential.map k k
      (X.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (w i)) = h' • σB := by
    rw [← topFormsMap_ιMulti]
    exact hrel
  have hmem := mem_maximalIdeal_pow_of_ιMulti_eq_smul (K := D.Y.functionField) hcn (by omega) hϖ
    hσB h0B _ u e he hvi hrel'
  have hordh := le_ord_of_mem_pow D.E hh'0 hmem
  -- the coefficient `g` of `τ` along `σ_A^{⊗m}`: `ord_Γ g = -m a_Γ` through `x₀`
  let g := formCoeff (k := k) (X.presheaf.stalk (D.f D.E.genericPoint)) hσA h0A
    (show PluriForms k X.functionField n m from τ)
  have hg0 : g ≠ 0 := fun h0 => hτ.1 ((formCoeff_eq_zero_iff hσA h0A _).mp h0)
  have hgΓ : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      (X.ord g Γ.genericPoint : ℝ) = -((m : ℝ) * (Δ.coeff Γ : ℝ)) := by
    intro Γ hΓ
    have e1 := MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff sX (D.f D.E.genericPoint) Γ hΓ
      hσA h0A τ
    have e2 := hτ.2 Γ ⟨_, hΓ, hU⟩
    rw [e1] at e2
    have := congrArg (fun q : ℚ => (q : ℝ)) e2
    push_cast at this
    linarith
  -- local equations of the components through `x₀`
  have hπex : ∀ G : T, ∃ π : X.presheaf.stalk (D.f D.E.genericPoint), π ≠ 0 ∧
      G.1.idealSheaf.stalkIdeal (D.f D.E.genericPoint) = Ideal.span {π} ∧
      ∀ Γ' : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ'.support →
        X.ord (algebraMap _ X.functionField π) Γ'.genericPoint = if Γ' = G.1 then 1 else 0 :=
    fun G => exists_localEquation _ hreg G.1 (hTmem G.1 G.2).2
  choose π hπ0 hπI hπord using hπex
  have hπE : ∀ G : T, D.Y.ord (functionFieldMap D.f (algebraMap _ X.functionField (π G)))
      D.E.genericPoint = e (jT G.1) := by
    intro G
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
    have hspan : Ideal.span {π G} = Ideal.span {z (jT G.1)} := by
      rw [hjT G.1 G.2, ← hI ⟨G.1, hTmem G.1 G.2⟩, ← Scheme.IdealSheafData.stalkIdeal_eq_stalk,
        hπI G]
    obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
    have hmul := congrArg (D.f.stalkMap D.E.genericPoint).hom hv
    rw [map_mul] at hmul
    have h1 : algebraMap D.E.localRing D.Y.functionField
        ((D.f.stalkMap D.E.genericPoint).hom (π G)) ≠ 0 := by
      refine IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ?_)
      exact left_ne_zero_of_mul (hmul ▸ hz0 (jT G.1))
    have hvu : IsUnit ((D.f.stalkMap D.E.genericPoint).hom (v : X.presheaf.stalk _)) :=
      v.isUnit.map _
    have h2 := Scheme.ord_mul (X := D.Y) (x := D.E.genericPoint) h1
      (hvu.map (algebraMap D.E.localRing D.Y.functionField)).ne_zero
    rw [← map_mul, hmul, hordz, D.E.ord_algebraMap_of_isUnit hvu, add_zero] at h2
    exact h2.symm
  -- the Hartogs relation along `E`
  let Gf : Option T → X.functionField := fun i =>
    Option.elim i g fun G => algebraMap _ X.functionField (π G)
  let wt : Option T → ℝ := fun i => Option.elim i 1 fun G => (m : ℝ) * (Δ.coeff G.1 : ℝ)
  have hGf : ∀ i, Gf i ≠ 0 := by
    rintro (_ | G)
    · exact hg0
    · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero (hπ0 G))
  have key := MMP.Threefold.Bridges.sum_ord_functionFieldMap_eq_zero (f := D.f) D.E Gf hGf wt
    fun Γ hΓ => by
      simp only [Fintype.sum_option, Gf, wt, Option.elim]
      rw [hgΓ Γ hΓ]
      simp_rw [hπord _ Γ hΓ]
      by_cases hΓT : Γ ∈ T
      · rw [Finset.sum_eq_single ⟨Γ, hΓT⟩]
        · simp
        · rintro G - hne
          have : Γ ≠ G.1 := fun h => hne (Subtype.ext h.symm)
          simp [this]
        · simp
      · have hΓS : Γ ∉ S := fun h => hΓT (Finset.mem_filter.mpr ⟨h, hΓ⟩)
        have h0 : Δ.coeff Γ = 0 := by
          rw [DivisorWithCoeffs.coeff_apply]
          exact Finsupp.notMem_support_iff.mp fun h => hΓS (hS h)
        rw [h0]
        simp only [Rat.cast_zero, mul_zero, neg_zero, mul_one, zero_add]
        refine Finset.sum_eq_zero fun G _ => ?_
        have : Γ ≠ G.1 := fun h => hΓT (h ▸ G.2)
        simp [this]
  simp only [Fintype.sum_option, Gf, wt, Option.elim, mul_one] at key
  simp_rw [hπE] at key
  push_cast at key
  -- the numerical conclusion
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmain : (m : ℝ) * (a : ℝ) = (D.Y.ord (functionFieldMap D.f g) D.E.genericPoint : ℝ) +
      (m : ℝ) * (D.Y.ord (algebraMap D.E.localRing D.Y.functionField h') D.E.genericPoint : ℝ) := by
    have h1 : (m : ℚ) * a = D.ordPullback τ := hτa
    have h2 : D.ordPullback τ = _ := hord
    rw [h2] at h1
    have := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at this
    exact this
  have hordh' : ((∑ i, e i - 1 : ℕ) : ℝ) ≤
      (D.Y.ord (algebraMap D.E.localRing D.Y.functionField h') D.E.genericPoint : ℝ) := by
    exact_mod_cast hordh
  have hsub : ((∑ i, e i - 1 : ℕ) : ℝ) = ((∑ i, e i : ℕ) : ℝ) - 1 := by
    have : 1 ≤ ∑ i, e i := by
      calc 1 ≤ e ⟨0, by omega⟩ := he _
        _ ≤ ∑ i, e i := Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ _)
    push_cast [this]
    ring
  -- `a ≥ ∑ e_i - 1 - ∑_{G ∈ T} e_{j G} a_G`
  have hlow : ((∑ i, e i : ℕ) : ℝ) - 1 - ∑ G : T, (e (jT G.1) : ℝ) * (Δ.coeff G.1 : ℝ) ≤ a := by
    have h3 : (D.Y.ord (functionFieldMap D.f g) D.E.genericPoint : ℝ) =
        -∑ G : T, (e (jT G.1) : ℝ) * ((m : ℝ) * (Δ.coeff G.1 : ℝ)) := by
      linarith
    have h4 : ∑ G : T, (e (jT G.1) : ℝ) * ((m : ℝ) * (Δ.coeff G.1 : ℝ)) =
        (m : ℝ) * ∑ G : T, (e (jT G.1) : ℝ) * (Δ.coeff G.1 : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [h4] at h3
    have h5 : (m : ℝ) * (((∑ i, e i : ℕ) : ℝ) - 1 - ∑ G : T, (e (jT G.1) : ℝ) *
        (Δ.coeff G.1 : ℝ)) ≤ (m : ℝ) * a := by
      rw [hmain, h3, ← hsub]
      nlinarith [hordh']
    exact le_of_mul_le_mul_left h5 hm'
  -- the combinatorial bound
  have hsplit : ((∑ i, e i : ℕ) : ℝ) = ∑ G ∈ T, (e (jT G) : ℝ) +
      ∑ i ∈ (T.image jT)ᶜ, (e i : ℝ) := by
    push_cast
    rw [← Finset.sum_add_sum_compl (T.image jT), Finset.sum_image hinj]
  have hcompl : ((c : ℝ) - T.card) ≤ ∑ i ∈ (T.image jT)ᶜ, (e i : ℝ) := by
    have hc' : ((T.image jT)ᶜ.card : ℝ) = c - T.card := by
      rw [Finset.card_compl, Fintype.card_fin, Finset.card_image_of_injOn hinj]
      push_cast [hcard]
      ring
    rw [← hc']
    have := Finset.card_nsmul_le_sum (T.image jT)ᶜ (fun i => (e i : ℝ)) 1
      (fun i _ => by exact_mod_cast he i)
    simpa using this
  have hterm : ∑ G ∈ T, (1 - (Δ.coeff G : ℝ)) ≤
      ∑ G ∈ T, (e (jT G) : ℝ) - ∑ G ∈ T, (e (jT G) : ℝ) * (Δ.coeff G : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun G hG => ?_
    have h1 : (Δ.coeff G : ℝ) ≤ 1 := by exact_mod_cast hcoeff G (hTmem G hG).1
    have h2 : (1 : ℝ) ≤ e (jT G) := by exact_mod_cast he (jT G)
    nlinarith
  have hTsum : ∑ G : T, (e (jT G.1) : ℝ) * (Δ.coeff G.1 : ℝ) =
      ∑ G ∈ T, (e (jT G) : ℝ) * (Δ.coeff G : ℝ) :=
    Finset.sum_coe_sort T (fun G => (e (jT G) : ℝ) * (Δ.coeff G : ℝ))
  rw [hTsum, hsplit] at hlow
  have hfin : ((-1 + ∑ G ∈ T, (1 - Δ.coeff G) + ((c : ℚ) - T.card) : ℚ) : ℝ) ≤ (a : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hfin

/-- The right-hand side of the snc formula is at most the discrepancy of every exceptional
divisor. -/
public theorem le_discrep_of_isSNC {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {Δ : QDivisor X} {S : Finset (MMP.Mori.PrimeDivisor X)}
    (hS : Δ.support ⊆ S) (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (hcoeff : ∀ E ∈ S, Δ.coeff E ≤ 1) :
    (⨅ (E ∈ S) (F ∈ S) (_ : E ≠ F) (_ : (E.support ∩ F.support).Nonempty),
        (((1 - Δ.coeff E - Δ.coeff F : ℚ) : ℝ) : EReal)) ⊓
      (⨅ E ∈ S, (((1 - Δ.coeff E : ℚ) : ℝ) : EReal)) ⊓ 1 ≤ discrep sX n K Δ := by
  classical
  refine le_discrep_iff.mpr fun D a hD ha => ?_
  obtain ⟨c, T, -, -, hc2, hcard, hTS, hTx, hle⟩ :=
    le_isDiscrepancy_of_isSNC hX hsm hK hS hsnc hcoeff D hD ha
  have hnn : ∀ G ∈ T, 0 ≤ 1 - Δ.coeff G := fun G hG => by linarith [hcoeff G (hTS hG)]
  have hcT : (T.card : ℚ) ≤ c := by exact_mod_cast hcard
  -- reduce to a bound in `ℚ`
  suffices h : ∃ t : ℚ, t ≤ a ∧
      (⨅ (E ∈ S) (F ∈ S) (_ : E ≠ F) (_ : (E.support ∩ F.support).Nonempty),
          (((1 - Δ.coeff E - Δ.coeff F : ℚ) : ℝ) : EReal)) ⊓
        (⨅ E ∈ S, (((1 - Δ.coeff E : ℚ) : ℝ) : EReal)) ⊓ 1 ≤ ((t : ℝ) : EReal) by
    obtain ⟨t, hta, ht⟩ := h
    exact ht.trans (EReal.coe_le_coe_iff.mpr (by exact_mod_cast hta))
  rcases Nat.lt_or_ge 1 T.card with h2 | h1
  · -- two components `G ≠ G'` through the center
    obtain ⟨G, hG, G', hG', hne⟩ := Finset.one_lt_card.mp h2
    refine ⟨1 - Δ.coeff G - Δ.coeff G', ?_, ?_⟩
    · have hsub : ({G, G'} : Finset _) ⊆ T := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hpair := Finset.sum_le_sum_of_subset_of_nonneg hsub fun x hx _ => hnn x hx
      rw [Finset.sum_pair hne] at hpair
      linarith
    · refine (inf_le_left.trans inf_le_left).trans ?_
      refine (iInf₂_le G (hTS hG)).trans ((iInf₂_le G' (hTS hG')).trans ?_)
      exact iInf₂_le hne ⟨_, hTx G hG, hTx G' hG'⟩
  · rcases Nat.lt_or_ge 0 T.card with h0 | h0
    · -- one component `G` through the center
      obtain ⟨G, hTG⟩ := Finset.card_eq_one.mp (show T.card = 1 by omega)
      refine ⟨1 - Δ.coeff G, ?_, ?_⟩
      · rw [hTG, Finset.sum_singleton, Finset.card_singleton] at hle
        have : (2 : ℚ) ≤ c := by exact_mod_cast hc2
        push_cast at hle
        linarith
      · have hG : G ∈ T := hTG ▸ Finset.mem_singleton_self G
        exact (inf_le_left.trans inf_le_right).trans (iInf₂_le G (hTS hG))
    · -- no component through the center
      have hT0 : T = ∅ := Finset.card_eq_zero.mp (show T.card = 0 by omega)
      refine ⟨1, ?_, ?_⟩
      · rw [hT0, Finset.sum_empty, Finset.card_empty] at hle
        have : (2 : ℚ) ≤ c := by exact_mod_cast hc2
        push_cast at hle
        linarith
      · refine inf_le_right.trans ?_
        norm_num

/-- **The discrepancy of an snc pair** (Kollár–Mori 2.31(3)). Let `X` be a smooth variety over
a perfect field, with canonical divisor `K` of dimension
`n ≥ 2`, and let `Δ = ∑_{E ∈ S} a_E E` for a finite set `S` of prime divisors with `∑_{E ∈ S} E`
snc and every `a_E ≤ 1`. Then `discrep(X, Δ)` is the minimum of `1 - a_E - a_F` over distinct
`E, F ∈ S` that meet, of `1 - a_E` over `E ∈ S`, and of `1`. -/
@[mmp "thm_km2b_discrep_snc_formula"]
public theorem discrep_eq_of_isSNC {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {n : ℕ} (hn : 2 ≤ n) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Δ : QDivisor X} (S : Finset (PrimeDivisor X)) (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ E ∈ S, Finsupp.single E (1 : ℤ)))
    (hcoeff : ∀ E ∈ S, Δ.coeff E ≤ 1) :
    discrep sX n K Δ =
      (⨅ (E ∈ S) (F ∈ S) (_ : E ≠ F) (_ : (E.support ∩ F.support).Nonempty),
          (((1 - Δ.coeff E - Δ.coeff F : ℚ) : ℝ) : EReal)) ⊓
        (⨅ E ∈ S, (((1 - Δ.coeff E : ℚ) : ℝ) : EReal)) ⊓ 1 := by
  refine le_antisymm (le_inf (le_inf ?_ ?_) (discrep_le_one hX hsm hn hK hS hsnc))
    (le_discrep_of_isSNC hX hsm hK hS hsnc hcoeff)
  · refine le_iInf₂ fun E hE => le_iInf₂ fun F hF => le_iInf₂ fun hEF hmeet => ?_
    exact discrep_le_pair hX hsm hK hS hsnc hE hF hEF hmeet
  · exact le_iInf₂ fun E hE => discrep_le_single hX hsm hn hK hS hsnc hE

/-! ### Klt and lc pairs -/

/-- On a scheme of dimension `≤ 1` no divisor over `X` is exceptional. -/
private theorem not_isExceptional_of_le_one {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {n : ℕ} (hdim : topologicalKrullDim X = n) (hn : n ≤ 1)
    (D : DivisorOver k sX) : ¬ D.IsExceptional := by
  intro h
  have hdef : RationalMap.DefinedAt (X := D.Y) D.f.toRationalMap D.E.genericPoint := by
    rw [RationalMap.DefinedAt, RationalMap.dom_toRationalMap_hom]
    trivial
  have h2 := (RationalMap.isExceptional_iff.mp h) hdef
  have hmem : D.f D.E.genericPoint ∈
      (RationalMap.transform (X := D.Y) D.f.toRationalMap D.E.idealSheaf.support : Set X) := by
    refine RationalMap.image_subset_transform D.f.toPartialMap rfl _ ?_
    rw [MMP.Positivity.image_toPartialMap_hom]
    refine ⟨_, ?_, rfl⟩
    change D.E.genericPoint ∈ D.E.support
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have hc := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2) _ hmem
  have hle : (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) ≤ n := by
    rw [← hdim, ← MMP.Flips.codimension_closureSingleton]
    exact Order.coheight_le_krullDim _
  have : ((2 : ℕ∞) : WithBot ℕ∞) ≤ (1 : ℕ) := (WithBot.coe_le_coe.mpr hc).trans
    (hle.trans (by exact_mod_cast hn))
  exact absurd this (by decide)

/-- A lower bound for the snc discrepancy formula: if `c i < 1` for every `i ∈ S`, then the
minimum of `1`, of the `1 - c i` and of the `1 - c i - c j` over `i, j ∈ S` exceeds `-1`. -/
private theorem neg_one_lt_inf_snc_bound {ι : Type*} (S : Finset ι) (c : ι → ℚ)
    (hc : ∀ i ∈ S, c i < 1) (P Q : ι → ι → Prop) :
    (-1 : EReal) < (⨅ (i ∈ S) (j ∈ S) (_ : P i j) (_ : Q i j),
        (((1 - c i - c j : ℚ) : ℝ) : EReal)) ⊓ (⨅ i ∈ S, (((1 - c i : ℚ) : ℝ) : EReal)) ⊓ 1 := by
  obtain ⟨δ, hδ, hδc⟩ : ∃ δ : ℚ, 0 < δ ∧ ∀ i ∈ S, δ ≤ 1 - c i := by
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨1, one_pos, by simp⟩
    · obtain ⟨i₀, hi₀, hmin⟩ := S.exists_min_image (fun i => 1 - c i) hS
      exact ⟨_, sub_pos.mpr (hc i₀ hi₀), hmin⟩
  have hL : ∀ q : ℚ, min (2 * δ - 1) 0 ≤ q →
      (((min (2 * δ - 1) 0 : ℚ) : ℝ) : EReal) ≤ ((q : ℝ) : EReal) := fun q hq =>
    EReal.coe_le_coe_iff.mpr (by exact_mod_cast hq)
  refine lt_of_lt_of_le (b := (((min (2 * δ - 1) 0 : ℚ) : ℝ) : EReal)) ?_
    (le_inf (le_inf ?_ ?_) ?_)
  · have : (-1 : ℚ) < min (2 * δ - 1) 0 := lt_min (by linarith) (by norm_num)
    simpa using (EReal.coe_lt_coe_iff.mpr (by exact_mod_cast this) :
      ((-1 : ℝ) : EReal) < (((min (2 * δ - 1) 0 : ℚ) : ℝ) : EReal))
  · refine le_iInf₂ fun i hi => le_iInf₂ fun j hj => le_iInf₂ fun _ _ => hL _ ?_
    linarith [min_le_left (2 * δ - 1) 0, hδc i hi, hδc j hj]
  · exact le_iInf₂ fun i hi => hL _ (by linarith [min_le_right (2 * δ - 1) 0, hδc i hi])
  · simpa using hL 1 (by linarith [min_le_right (2 * δ - 1) 0])

/-- **Snc pairs with coefficients `< 1` are klt.** Let `Y` be a smooth variety over an
algebraically closed field of characteristic zero, with canonical divisor `K` of dimension `n`,
and let `B` be a `ℚ`-divisor on `Y` that is snc and has every coefficient `< 1`. Then `(Y, B)` is
klt. -/
@[mmp "lem_km3a_snc_klt"]
public theorem isKltPair_of_isSNC {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of k)) (hY : IsNormalVariety k sY) (hsm : IsSmoothScheme sY)
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor sY n)
    {B : QDivisor Y} (hsnc : B.IsSNC sY) (hcoeff : ∀ E : PrimeDivisor Y, B.coeff E < 1) :
    IsKltPair sY n K B := by
  refine ⟨⟨hY, hK, MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _⟩, ?_,
    roundDown_nonpos_iff.mpr hcoeff⟩
  rcases le_or_gt 2 n with hn | hn
  · classical
    rw [discrep_eq_of_isSNC sY hY hsm hn hK B.support le_rfl
      (hsnc.of_support_subset <| Finsupp.support_finsetSum.trans <| Finset.biUnion_subset.mpr
        fun E hE => Finsupp.support_single_subset.trans (Finset.singleton_subset_iff.mpr hE))
      (fun E _ => (hcoeff E).le)]
    exact neg_one_lt_inf_snc_bound _ _ (fun E _ => hcoeff E) _ _
  · rw [discrep_eq_top fun D a hD _ =>
      not_isExceptional_of_le_one hK.topologicalKrullDim_eq (by omega) D hD]
    exact EReal.coe_lt_top (-1)

/-- If every coefficient of `Δ` is `≤ 1`, then every discrepancy of a non-exceptional divisor
over `X` is `≥ -1`. -/
public theorem neg_one_le_of_not_isExceptional {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hcoeff : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P ≤ 1) {D : DivisorOver k sX}
    (hD : ¬ D.IsExceptional) {a : ℚ} (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  obtain ⟨hX, hK, m, hm, -, V, hV, τ, hτ, hmτ⟩ := ha
  obtain ⟨P, hv⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX D hD
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
    DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
  have hx : D.f D.E.genericPoint = P.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
  have hPV : (P.support ∩ (V : Set X)).Nonempty := by
    refine ⟨P.genericPoint, ?_, hx ▸ hV⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have e := hτ.2 P hPV
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have : a = -Δ.coeff P := by
    apply mul_left_cancel₀ hm0
    linear_combination hmτ + e
  rw [this]
  linarith [hcoeff P]

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
  · exact neg_one_le_of_not_isExceptional hcoeff hD ha

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

section IsDltPair

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
  {Δ : QDivisor X}

/-- **Dlt pairs are lc.** Let `k` be a perfect field. If `(X, Δ)`, with canonical divisor `K` of
dimension `n`, is dlt, then it is lc: `discrep(X, Δ) ≥ -1`. -/
@[mmp "lem_km3c_dlt_is_lc"]
public theorem IsDltPair.isLcPair (h : IsDltPair sX n K Δ) : IsLcPair sX n K Δ := by
  obtain ⟨hpair, hcoeff, U, hUsm, hsnc, hZ⟩ := h
  refine ⟨hpair, le_discrep_iff.mpr fun D a _ ha => ?_⟩
  suffices -1 ≤ a by
    simpa using EReal.coe_le_coe_iff.mpr (by exact_mod_cast this : (-1 : ℝ) ≤ a)
  by_cases hU : ((D.center : Set X) ∩ U).Nonempty
  · exact neg_one_le_of_isSNC_restrictOpen hpair (fun P => (hcoeff P).2) hUsm hsnc hU ha
  · exact (hZ D a (fun x hx hxU => hU ⟨x, hx, hxU⟩) ha).le

end IsDltPair

section IsDltPairOfTwoLe

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- **Dlt pairs are lc.** If `(X, Δ)`, with canonical divisor `K` of dimension `n ≥ 2`, is dlt
over an algebraically closed field of characteristic zero, then it is lc: `discrep(X, Δ) ≥ -1`. -/
@[mmp "lem_km5b_dlt_implies_lc"]
public theorem IsDltPair.isLcPair_of_two_le [IsAlgClosed k] [CharZero k] (h : IsDltPair sX n K Δ)
    (hn : 2 ≤ n) :
    IsLcPair sX n K Δ :=
  h.isLcPair

end IsDltPairOfTwoLe

/-! ### Log discrepancies along an snc divisor -/

/-- The pull-back of an integral combination of divisors with given pull-backs is the same
combination of the pull-backs. -/
private theorem isPullback_sum {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (hc : ∀ D : Divisor Y, D.IsCartier)
    (hgen : ∀ (D : Divisor Y) (Z : irreducibleComponents X), f (componentGenericPoint X Z) ∉ D.supp)
    (S : Finset (MMP.Mori.PrimeDivisor Y)) (c : MMP.Mori.PrimeDivisor Y → ℤ)
    (B : MMP.Mori.PrimeDivisor Y → Divisor X)
    (hB : ∀ G ∈ S, Divisor.IsPullback f (Finsupp.single G (1 : ℤ)) (hgen _) (B G)) :
    Divisor.IsPullback f (∑ G ∈ S, c G • (Finsupp.single G (1 : ℤ) : Divisor Y)) (hgen _)
      (∑ G ∈ S, c G • B G) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Divisor.isPullback_zero (f := f) (hgen _)
  | insert G S hG ih =>
    rw [Finset.sum_insert hG, Finset.sum_insert hG]
    exact Divisor.IsPullback.add (hc _) (hc _) (hgen _)
      ((hB G (Finset.mem_insert_self _ _)).zsmul (hc _) (c G) (hgen _))
      (ih fun G' hG' => hB G' (Finset.mem_insert_of_mem hG'))

/-- **The pull-back of a `ℚ`-divisor supported on `S`, coefficientwise.** If every divisor on `Y`
is Cartier and `B G = f^*G` for each prime `G ∈ S`, then the pull-back `D'` of a `ℚ`-Cartier
`ℚ`-divisor `D = ∑_{G ∈ S} d_G G` has `coeff_P D' = ∑_{G ∈ S} d_G coeff_P (B G)`. -/
private theorem coeff_of_isPullback {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Y} (hc : ∀ D : Divisor Y, D.IsCartier)
    (hgen : ∀ (D : Divisor Y) (Z : irreducibleComponents X), f (componentGenericPoint X Z) ∉ D.supp)
    {D : QDivisor Y} (hDq : D.IsQCartier) {S : Finset (MMP.Mori.PrimeDivisor Y)}
    (hS : D.support ⊆ S)
    {hD : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ D.supp}
    {D' : QDivisor X} (hD' : D.IsPullback f hD D') (B : MMP.Mori.PrimeDivisor Y → Divisor X)
    (hB : ∀ G ∈ S, Divisor.IsPullback f (Finsupp.single G (1 : ℤ)) (hgen _) (B G))
    (P : MMP.Mori.PrimeDivisor X) :
    D'.coeff P = ∑ G ∈ S, D.coeff G * ((B G).coeff P : ℚ) := by
  classical
  have hm := QDivisor.cartierIndex_pos hDq
  obtain ⟨D₀, hD₀, -⟩ := QDivisor.isCartierDivisor_cartierIndex_smul hDq
  set m := D.cartierIndex hDq
  have hD₀G : ∀ G, (D₀ G : ℚ) = m * D G := fun G => by
    have h := congrArg (· G) hD₀
    simp only [Finsupp.smul_apply, zsmul_eq_mul, Int.cast_natCast] at h
    exact h
  have hD₀S : D₀ = ∑ G ∈ S, D₀ G • (Finsupp.single G (1 : ℤ) : Divisor Y) := by
    ext G
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
    split_ifs with hG
    · rfl
    · have := hD₀G G
      rw [Finsupp.notMem_support_iff.mp (mt (@hS G) hG), mul_zero] at this
      exact_mod_cast this
  obtain ⟨D'', hD'', hpb⟩ := hD' m hm D₀ hD₀ (hc _)
  have hD''S := hpb.eq (hc _) ((isPullback_sum hc hgen S D₀ B hB).of_eq hD₀S.symm)
  have h := congrArg (DivisorWithCoeffs.coeff · P) hD''
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hD''S] at h
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, Int.cast_sum, Int.cast_mul, zsmul_eq_mul, Int.cast_natCast] at h ⊢
  apply mul_left_cancel₀ (show (m : ℚ) ≠ 0 by positivity)
  rw [← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun G _ => by rw [hD₀G]; ring

/-- **Log discrepancies on an snc pair.** Let `X` be a smooth variety over an algebraically closed
field of characteristic zero, with canonical divisor `K` of dimension `n ≥ 2`, and let
`Δ = ∑_{G ∈ S} d_G G` for a finite set `S` of prime divisors with `∑_{G ∈ S} G` snc and every
`d_G ≤ 1`. Let `(Y, f, E)` be an exceptional divisor over `X` and `a = a(E, X, Δ)`. Then each
`G ∈ S` has a pull-back `f^*G`, and for any choice `B G` of these pull-backs,
`ord_E(G) = coeff_E(f^*G) ≥ 0` and `a + 1 ≥ ∑_{G ∈ S} (1 - d_G) ord_E(G)`. -/
@[mmp "lem_km5b_snc_log_discrepancy_bound"]
public theorem sum_le_add_one_of_isSNC {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) (hX : IsNormalVariety k sX) (hsm : IsSmoothScheme sX)
    {n : ℕ} (hn : 2 ≤ n) {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {Δ : QDivisor X} (S : Finset (PrimeDivisor X)) (hS : Δ.support ⊆ S)
    (hsnc : DivisorWithCoeffs.IsSNC sX (∑ G ∈ S, Finsupp.single G (1 : ℤ)))
    (hcoeff : ∀ G ∈ S, Δ.coeff G ≤ 1)
    (E : DivisorOver k sX) (hE : E.IsExceptional) {a : ℚ} (ha : IsDiscrepancy sX n K Δ E a) :
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    ∃ hB : ∀ G ∈ S, ∀ Z : irreducibleComponents E.Y,
        E.f (componentGenericPoint E.Y Z) ∉
          DivisorWithCoeffs.supp (Finsupp.single G (1 : ℤ) : Divisor X),
      ∀ B : PrimeDivisor X → Divisor E.Y,
        (∀ (G : PrimeDivisor X) (hG : G ∈ S),
          Divisor.IsPullback E.f (Finsupp.single G (1 : ℤ)) (hB G hG) (B G)) →
        (∀ G ∈ S, 0 ≤ (B G).coeff E.E) ∧
          ∑ G ∈ S, (1 - Δ.coeff G) * ((B G).coeff E.E : ℚ) ≤ a + 1 := by
  classical
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isIntegral
  have := E.isDominant
  have : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  have hgen : ∀ (D : Divisor X) (Z : irreducibleComponents E.Y),
      E.f (componentGenericPoint E.Y Z) ∉ D.supp :=
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f
  have hcart := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  refine ⟨fun G _ => hgen _, fun B hBpb => ⟨fun G hG =>
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) (hcart _)
      (fun P _ => by rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp)
      (hBpb G hG) E.E ((E.E.genericPoint_mem_iff _).mp trivial), ?_⟩⟩
  -- move from `Δ` to the reduced boundary `Δ₁ = ∑_{G ∈ S} G` along `Δ₁ - Δ`
  set Δ₁ : QDivisor X := ∑ G ∈ S, Finsupp.single G (1 : ℚ)
  have hΔ₁ : ∀ G, Δ₁.coeff G = if G ∈ S then 1 else 0 := fun G => by
    simp [Δ₁, DivisorWithCoeffs.coeff_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hq := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  obtain ⟨-, hB', hmain⟩ := IsPairWith.isDiscrepancy_add_smul_iff ⟨hX, hK, hq _⟩ (hq (Δ₁ - Δ)) E
  have hpb := QDivisor.isPullback_pullback (hq (Δ₁ - Δ)) hB'
  have ha₁ := ((hmain _ hpb).1 a).mpr ha
  rw [add_sub_cancel] at ha₁
  have hsnc₁ : Δ₁.IsSNC sX := (DivisorWithCoeffs.isSNC_iff_of_support_eq (by
    ext G
    rw [Finsupp.mem_support_iff, ← DivisorWithCoeffs.coeff_apply, hΔ₁, mem_support_sum_single]
    split_ifs <;> simp_all)).mpr hsnc
  have hlow := neg_one_le_of_isSNC hsm hsnc₁ (fun G => by rw [hΔ₁]; split_ifs <;> norm_num) ha₁
  rw [coeff_of_isPullback hcart hgen (hq _) (fun G hG => ?_) hpb B hBpb] at hlow
  · rw [Finset.sum_congr rfl fun G hG => by
      rw [DivisorWithCoeffs.coeff_sub, hΔ₁, ite_eq_left hG]] at hlow
    linarith
  · by_contra hGS
    refine Finsupp.mem_support_iff.mp hG ?_
    rw [← DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_sub, hΔ₁, ite_eq_right hGS,
      DivisorWithCoeffs.coeff_apply, Finsupp.notMem_support_iff.mp (mt (@hS G) hGS), sub_zero]

/-! ### Log resolutions -/

section LogResolution

variable {k : Type u} [Field k]

/-- A divisor over a normal variety `X` is exceptional exactly when its valuation is that of no
prime divisor of `X`. -/
private theorem isExceptional_iff_forall_valuation_ne {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) :
    D.IsExceptional ↔
      ∀ P : MMP.Mori.PrimeDivisor X,
        D.valuation ≠ (DivisorOver.ofPrimeDivisor k hX P).valuation :=
  (show D.IsExceptional ↔ 2 ≤ codimension D.center by
    rw [DivisorOver.isExceptional_iff_two_le_coheight hX,
      MMP.Positivity.DivisorOver.codimension_center]).trans
    (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX D)

/-- Being exceptional depends only on the valuation. -/
private theorem isExceptional_of_valuation_eq {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX)
    {D D' : DivisorOver k sX} (h : D.valuation = D'.valuation) (hD : D.IsExceptional) :
    D'.IsExceptional :=
  (isExceptional_iff_forall_valuation_ne hX D').mpr fun P hP =>
    (isExceptional_iff_forall_valuation_ne hX D).mp hD P (h.trans hP)

/-- The generic point of a prime divisor of a normal variety `X` lies in the biregular locus of
a proper birational morphism `f : Y ⟶ X` of varieties. -/
private theorem genericPoint_mem_biregularLocus {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsNormal X] (hX : MMP.Mori.IsVariety k sX) {f : Y ⟶ X} (hY : MMP.Mori.IsVariety k (f ≫ sX))
    [IsProper f] (hf : IsBirationalMorphism f) (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∈ biregularLocus f := by
  have h := two_le_closedsCodimension_compl_biregularLocus (hY := hX) (hX := hY) sX f hf
  by_contra hP
  have := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h) P.genericPoint hP
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- The valuation of the divisor `(Y, f, G)` over `X` is the valuation of the prime divisor `G`
of `Y`, read on `k(X)` through `f^*`. -/
private theorem valuation_mk_eq_comap {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (G : MMP.Mori.PrimeDivisor Y) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).valuation =
      (DivisorOver.ofPrimeDivisor k hY G).valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  ext t
  change G.divisorialValuation (functionFieldMap f t) =
    G.divisorialValuation (functionFieldMap (𝟙 Y) (functionFieldMap f t))
  rw [functionFieldMap_id_apply]

/-- A composite of birational morphisms of irreducible schemes is birational. -/
public theorem isBirationalMorphism_comp {V X' X : Scheme.{u}} [IrreducibleSpace V]
    [IrreducibleSpace X'] [IrreducibleSpace X] {g : V ⟶ X'} {μ : X' ⟶ X}
    (hg : MMP.Mori.IsBirationalMorphism g) (hμ : MMP.Mori.IsBirationalMorphism μ) :
    MMP.Mori.IsBirationalMorphism (g ≫ μ) := by
  have : Nonempty V := (IrreducibleSpace.isIrreducible_univ V).nonempty.to_subtype.map Subtype.val
  have : Nonempty X' :=
    (IrreducibleSpace.isIrreducible_univ X').nonempty.to_subtype.map Subtype.val
  obtain ⟨Wg, hWgne, hWg⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hg
  obtain ⟨Wμ, hWμne, hWμ⟩ := MMP.Mori.IsBirationalMorphism.exists_isOpenImmersion hμ
  obtain ⟨x₀, hx₀⟩ := hWgne
  obtain ⟨y, ⟨w, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    (Wg.ι ≫ g).isOpenEmbedding.isOpen_range Wμ.isOpen ⟨_, (⟨x₀, hx₀⟩ : Wg.toScheme), rfl⟩ hWμne
  let U : V.Opens := Wg ⊓ g ⁻¹ᵁ Wμ
  have hwU : w.1 ∈ U := ⟨w.2, hy⟩
  have h1 : IsOpenImmersion (U.ι ≫ g) := by
    rw [← Scheme.homOfLE_ι V (inf_le_left : U ≤ Wg), Category.assoc]
    infer_instance
  have hrange : Set.range (U.ι ≫ g) ⊆ Set.range Wμ.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact z.2.2
  have hfac := IsOpenImmersion.lift_fac Wμ.ι (U.ι ≫ g) hrange
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange ≫ Wμ.ι) := by
    rwa [hfac]
  have : IsOpenImmersion (IsOpenImmersion.lift Wμ.ι (U.ι ≫ g) hrange) :=
    IsOpenImmersion.of_comp _ Wμ.ι
  have hU : IsOpenImmersion (U.ι ≫ g ≫ μ) := by
    rw [← Category.assoc, ← hfac, Category.assoc]
    infer_instance
  let V' : X.Opens := (U.ι ≫ g ≫ μ).opensRange
  have hle : U ≤ (g ≫ μ) ⁻¹ᵁ V' := fun x hx => ⟨⟨x, hx⟩, rfl⟩
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE (g ≫ μ) U V' ⟨_, hwU⟩
    ⟨_, ⟨⟨w.1, hwU⟩, rfl⟩⟩ hle ?_
  have e : (g ≫ μ).resLE V' U hle = (U.ι ≫ g ≫ μ).isoOpensRange.hom := by
    rw [← cancel_mono V'.ι, Scheme.Hom.resLE_comp_ι, Scheme.Hom.isoOpensRange_hom_ι]
  rw [e]
  infer_instance

/-- A divisor `(W, g, F)` over `Y`, for a birational morphism `f : Y ⟶ X` of varieties, regarded
as the divisor `(W, f ∘ g, F)` over `X`. -/
public noncomputable def compDivisorOver {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) : DivisorOver k sX :=
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI := E.isIntegral
  { Y := E.Y
    f := E.f ≫ f
    isNormalVariety := by rw [Category.assoc]; exact E.isNormalVariety
    isBirationalMorphism := isBirationalMorphism_comp E.isBirationalMorphism hf
    E := E.E }

/-- The valuation of `(W, f ∘ g, F)` is that of `(W, g, F)`, read on `k(X)` through `f^*`. -/
public theorem valuation_compDivisorOver {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] (f : Y ⟶ X) (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    (E : DivisorOver k (f ≫ sX)) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hY hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have := E.isIntegral
  have := E.isDominant
  have := E.isNormal
  have := E.isLocallyNoetherian
  ext t
  change E.E.divisorialValuation (functionFieldMap (E.f ≫ f) t) =
    E.E.divisorialValuation (functionFieldMap E.f (functionFieldMap f t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- **Divisors over `X` lift to a proper birational model.** For a proper birational morphism
`f : Y ⟶ X` from a normal variety, every divisor `D` over `X` has the valuation of a divisor `E`
over `Y`, read on `k(X)` through `f^*`. -/
public theorem exists_divisorOver_comap_eq {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] {f : Y ⟶ X} (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f)
    [IsProper f] (D : DivisorOver k sX) :
    haveI : IsIntegral Y := hY.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    ∃ E : DivisorOver k (f ≫ sX), D.valuation = E.valuation.comap (functionFieldMap f) := by
  have : IsIntegral Y := hY.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : IsNormal Y := hY.2
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have hbW := hf.functionFieldMap_bijective
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap f) hbW
  let ξ : Valuation Y.functionField ℤᵐ⁰ := D.valuation.comap (e.symm : Y.functionField →+* _)
  have hξ : ξ.comap (functionFieldMap f) = D.valuation := by
    ext t
    change D.valuation (e.symm (functionFieldMap f t)) = D.valuation t
    have : e.symm (functionFieldMap f t) = t := e.symm_apply_apply t
    rw [this]
  -- `ξ` dominates the local ring of a point of `Y` (valuative criterion for `f`)
  obtain ⟨x, h1, h2⟩ : ∃ x : Y, (∀ a : Y.presheaf.stalk x,
      ξ (algebraMap _ Y.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk x),
        ξ (algebraMap _ Y.functionField a) < 1 := by
    set z := D.f D.E.genericPoint
    have hw : ∀ b : X.presheaf.stalk z,
        ξ (functionFieldMap f (algebraMap _ X.functionField b)) =
          D.valuation (algebraMap _ X.functionField b) := by
      intro b
      have := congrArg (fun v => v (algebraMap _ X.functionField b)) hξ
      simpa only [Valuation.comap_apply] using this
    let R := ξ.valuationSubring
    let φ : X.presheaf.stalk z →+* R :=
      ((functionFieldMap f).comp (algebraMap (X.presheaf.stalk z) X.functionField)).codRestrict R
        fun b => (ξ.mem_valuationSubring_iff _).2 (by
          rw [RingHom.comp_apply, hw]
          exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D z rfl _)
    have hgen : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
    have hex : ValuativeCriterion.Existence f := by
      have h : @IsProper _ _ f := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1.existence
    let S : ValuativeCommSq f :=
      { R := R
        K := Y.functionField
        i₁ := Y.fromSpecStalk (genericPoint Y)
        i₂ := Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z
        commSq := ⟨by
          rw [← functionFieldMap_fromSpecStalk f,
            ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
            ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
          rfl⟩ }
    obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
    have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R Y.functionField)) ≫ l =
        Y.fromSpecStalk (genericPoint Y) := hl₁
    set x := l (IsLocalRing.closedPoint R)
    have hx : genericPoint Y ⤳ x := (genericPoint_spec Y).specializes trivial
    let g := Scheme.stalkClosedPointTo l
    have hg : g ≫ CommRingCat.ofHom (algebraMap R Y.functionField) =
        Y.presheaf.stalkSpecializes hx := by
      apply Spec.map_injective
      apply (cancel_mono (Y.fromSpecStalk x)).mp
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hga : ∀ a : Y.presheaf.stalk x,
        algebraMap _ Y.functionField a = ((g.hom a : R) : Y.functionField) := fun a =>
      (congrArg (fun q => q.hom a) hg).symm
    refine ⟨x, fun a => ?_, fun a ha => ?_⟩
    · rw [hga]; exact (g.hom a).2
    · rw [hga]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
        (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))
  -- `ξ` is a divisor of `k(Y)`: `ord_E` on `D.Y`, along `k(Y) ≅ k(X) ≅ k(D.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sX) := hY.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sX) ξ := by
    have := D.isIntegral
    have := D.isNormal
    have := D.isLocallyNoetherian
    have := D.isDominant
    refine ⟨D.Y, D.f ≫ sX, D.isNormalVariety, D.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sX
    let := MMP.Mori.functionFieldAlgebra (f ≫ sX)
    let := MMP.Mori.functionFieldAlgebra (D.f ≫ sX)
    let eP := MMP.Mori.functionFieldAlgEquiv sX f hbW
    let eY :=
      MMP.Mori.functionFieldAlgEquiv sX D.f D.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eP.symm.trans eY, ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbW.2 t
    have hs := congrArg (fun v => v s) hξ
    simp only [Valuation.comap_apply] at hs
    have h1 : eP.symm (functionFieldMap f s) = s := eP.symm_apply_apply s
    change ξ (functionFieldMap f s) = D.E.divisorialValuation (eY (eP.symm (functionFieldMap f s)))
    rw [h1, hs]
    rfl
  obtain ⟨D', -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sX) hdiv x h1 h2
  refine ⟨D'.toDivisorOver, ?_⟩
  change D.valuation = D'.valuation.comap (functionFieldMap f)
  rw [hv, hξ]

/-- **The pull-back of a prime divisor is positive along divisors over it.** If `G` is a Cartier
prime divisor of `Y` and `E` a prime divisor of `W` with `g(η_E) ∈ G`, then `g^*G` has
coefficient at least `1` along `E`. -/
private theorem one_le_coeff_of_isPullback {W Y : Scheme.{u}} [IsLocallyNoetherian W]
    [IsNormal W] [IsLocallyNoetherian Y] [IsNormal Y] {g : W ⟶ Y} (G : MMP.Mori.PrimeDivisor Y)
    (hGc : Divisor.IsCartier (Finsupp.single G (1 : ℤ) : Divisor Y))
    {hB : ∀ Z : irreducibleComponents W,
      g (componentGenericPoint W Z) ∉ DivisorWithCoeffs.supp (Finsupp.single G (1 : ℤ) : Divisor Y)}
    {B : Divisor W} (h : Divisor.IsPullback g (Finsupp.single G (1 : ℤ)) hB B)
    (E : MMP.Mori.PrimeDivisor W) (hE : g E.genericPoint ∈ G.support) : 1 ≤ B.coeff E := by
  classical
  have heff : ∀ P : MMP.Mori.PrimeDivisor Y,
      0 ≤ DivisorWithCoeffs.coeff (Finsupp.single G (1 : ℤ) : Divisor Y) P :=
    fun P => by rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp
  have h0 : 0 ≤ B.coeff E :=
    MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (V := ⊤) hGc (fun P _ => heff P) h E
      ((E.genericPoint_mem_iff _).mp trivial)
  have hG : DivisorWithCoeffs.coeff (Finsupp.single G (1 : ℤ) : Divisor Y) G ≠ 0 := by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_eq_same]; exact one_ne_zero
  have hmem : E.genericPoint ∈ (B.supp : Set W) := by
    rw [MMP.Flips.supp_eq_preimage_supp_of_isPullback hGc heff h]
    exact DivisorWithCoeffs.support_subset_supp hG hE
  obtain ⟨E₂, hE₂, hηE₂⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
  obtain rfl := MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hηE₂
  omega

/-- In any topological space, a point of a closed set `T` lies on an irreducible closed subset
maximal among those contained in `T`. -/
private theorem exists_maximal_irreducibleCloseds {T : Type*} [TopologicalSpace T] (S : Closeds T)
    {y : T} (hy : y ∈ S) :
    ∃ W : IrreducibleCloseds T, Maximal (fun W' : IrreducibleCloseds T => (W' : Set T) ⊆ S) W ∧
      y ∈ W := by
  obtain ⟨m, hsm, hm⟩ := zorn_subset_nonempty {t : Set T | IsPreirreducible t ∧ t ⊆ S}
    (fun c hc hcc _ => ⟨⋃₀ c, ⟨fun u v hu hv ⟨y, hy, hyu⟩ ⟨x, hx, hxv⟩ =>
      let ⟨p, hpc, hyp⟩ := Set.mem_sUnion.1 hy
      let ⟨q, hqc, hxq⟩ := Set.mem_sUnion.1 hx
      Or.casesOn (hcc.total hpc hqc)
        (fun hpq : p ⊆ q =>
          let ⟨x, hxp, hxuv⟩ := (hc hqc).1 u v hu hv ⟨y, hpq hyp, hyu⟩ ⟨x, hxq, hxv⟩
          ⟨x, Set.mem_sUnion_of_mem hxp hqc, hxuv⟩)
        fun hqp : q ⊆ p =>
        let ⟨x, hxp, hxuv⟩ := (hc hpc).1 u v hu hv ⟨y, hyp, hyu⟩ ⟨x, hqp hxq, hxv⟩
        ⟨x, Set.mem_sUnion_of_mem hxp hpc, hxuv⟩,
      Set.sUnion_subset fun t ht => (hc ht).2⟩,
      fun _ hxc => Set.subset_sUnion_of_mem hxc⟩)
    {y} ⟨isPreirreducible_singleton, Set.singleton_subset_iff.mpr hy⟩
  have hcl : closure m = m := by
    refine (hm.eq_of_subset ⟨hm.prop.1.closure, ?_⟩ subset_closure).symm
    exact closure_minimal hm.prop.2 S.isClosed
  have hirr : IsIrreducible m := ⟨⟨y, hsm rfl⟩, hm.prop.1⟩
  refine ⟨⟨m, hirr, hcl ▸ isClosed_closure⟩, ⟨hm.prop.2, fun W' hW' hle => ?_⟩, hsm rfl⟩
  exact (hm.eq_of_subset ⟨W'.isIrreducible.isPreirreducible, hW'⟩ hle).symm.le

/-- A point of a closed subset of pure codimension one of a scheme lies on a prime divisor
contained in it. -/
private theorem exists_primeDivisor_of_isPureCodimOne {Y : Scheme.{u}} {T : Closeds Y}
    (hT : IsPureCodimOne T) {y : Y} (hy : y ∈ T) :
    ∃ G : MMP.Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ T ∧ y ∈ G.support := by
  obtain ⟨W, hW, hyW⟩ := exists_maximal_irreducibleCloseds T hy
  have h1 := hT W hW
  rw [MMP.Flips.codimension_eq_coheight_genericPoint] at h1
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1, ?_⟩
  have hsupp : ((AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ h1).support : Set Y) = W := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact W.isIrreducible.isGenericPoint_genericPoint_closure.trans W.isClosed.closure_eq
  rw [hsupp]
  exact ⟨hW.prop, hyW⟩

/-- The components of the snc subset `Ex(f) ∪ f⁻¹(Supp Δ) ∪ f⁻¹(Z)` form a finite set of prime
divisors whose reduced sum is snc. -/
public theorem exists_finset_isSNC {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [IsLocallyNoetherian Y] [LocallyOfFinitePresentation sY] (hsm : IsSmoothScheme sY)
    {T : Closeds Y} (hT : IsSNCSubset sY T) :
    ∃ S : Finset (MMP.Mori.PrimeDivisor Y),
      DivisorWithCoeffs.IsSNC sY (∑ E ∈ S, Finsupp.single E (1 : ℤ)) ∧
      ∀ F : MMP.Mori.PrimeDivisor Y, F.genericPoint ∈ (T : Set Y) → F ∈ S := by
  rcases hT with h0 | ⟨s, hs, hsnc⟩
  · refine ⟨∅, ?_, fun F hF => ?_⟩
    · rw [Finset.sum_empty]
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
    · rw [h0] at hF
      exact absurd hF (by simp)
  · refine ⟨s, hsnc, fun F hF => ?_⟩
    rw [← hs] at hF
    obtain ⟨E, hE, hgen⟩ := Set.mem_iUnion₂.mp hF
    rwa [MMP.Threefold.Resolution.eq_of_genericPoint_mem_support hgen] at hE

/-- A function positive on the members of a finite set satisfying `p` has a uniform positive
lower bound there. -/
private theorem exists_pos_forall_le {α : Type*} (s : Finset α) (p : α → Prop) (g : α → ℚ)
    (h : ∀ x ∈ s, p x → 0 < g x) : ∃ ε : ℚ, 0 < ε ∧ ∀ x ∈ s, p x → ε ≤ g x := by
  classical
  refine ⟨(insert 1 ((s.filter p).image g)).min' (Finset.insert_nonempty _ _), ?_,
    fun x hx hpx => Finset.min'_le _ _ (by simpa using Or.inr ⟨x, ⟨hx, hpx⟩, rfl⟩)⟩
  simpa [Finset.lt_min'_iff] using fun _ x hx hpx hgx => hgx ▸ h x hx hpx

/-- **The snc bound along a component.** Let `Y` be a smooth variety and `Δ` a `ℚ`-divisor on
`Y` supported on a finite set `S` of prime divisors, with `∑_{G ∈ S} G` snc and coefficients at
most `1`. If `E` is an exceptional divisor over `Y` whose center lies on some `G₀ ∈ S`, then
`a(E, Y, Δ) ≥ -1 + (1 - coeff_{G₀}(Δ))`: the term of `G₀` in the log-discrepancy bound
`a(E, Y, Δ) + 1 ≥ ∑_{G ∈ S} (1 - coeff_G(Δ)) ord_E(G)` is at least `1 - coeff_{G₀}(Δ)`, since
`ord_E(G₀) ≥ 1`. -/
private theorem neg_one_add_le_of_genericPoint_mem [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)}
    (hY : IsNormalVariety k sY) (hsm : IsSmoothScheme sY) {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) {Δ : QDivisor Y} {S : Finset (MMP.Mori.PrimeDivisor Y)}
    (hS : Δ.support ⊆ S) (hsnc : DivisorWithCoeffs.IsSNC sY (∑ G ∈ S, Finsupp.single G (1 : ℤ)))
    (hcoeff : ∀ G, Δ.coeff G ≤ 1) {G₀ : MMP.Mori.PrimeDivisor Y} (hG₀ : G₀ ∈ S)
    (E : DivisorOver k sY) (hE : E.IsExceptional) (hEG₀ : E.f E.E.genericPoint ∈ G₀.support)
    {a : ℚ} (ha : IsDiscrepancy sY n K Δ E a) : -1 + (1 - Δ.coeff G₀) ≤ a := by
  classical
  have := E.isLocallyNoetherian
  have := E.isNormal
  have : CompactSpace E.Y := E.isNormalVariety.1.toQuasiCompact.compactSpace_of_compactSpace
  obtain ⟨hB, hmain⟩ := sum_le_add_one_of_isSNC sY hY hsm
    (two_le_of_isExceptional hY hK.topologicalKrullDim_eq hE) hK S hS hsnc
    (fun G _ => hcoeff G) E hE ha
  have hcart := MMP.Fourfold.isCartier_of_isSmoothScheme hsm
  let B : MMP.Mori.PrimeDivisor Y → Divisor E.Y := fun G =>
    if hG : G ∈ S then Divisor.pullback _ (hcart _) (hB G hG) else 0
  have hBpb : ∀ (G : MMP.Mori.PrimeDivisor Y) (hG : G ∈ S),
      Divisor.IsPullback E.f (Finsupp.single G (1 : ℤ)) (hB G hG) (B G) := fun G hG => by
    simp only [B, dite_eq_left hG]
    exact Divisor.isPullback_pullback _ _
  obtain ⟨h0, hsum⟩ := hmain B hBpb
  have h1 : (1 : ℚ) ≤ (B G₀).coeff E.E := by
    exact_mod_cast one_le_coeff_of_isPullback G₀ (hcart _) (hBpb G₀ hG₀) E.E hEG₀
  have hle := Finset.single_le_sum (f := fun G => (1 - Δ.coeff G) * ((B G).coeff E.E : ℚ))
    (fun G hG => mul_nonneg (by linarith [hcoeff G]) (by exact_mod_cast h0 G hG)) hG₀
  have := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 (hcoeff G₀))
  linarith

variable [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {f : Y ⟶ X}
  [IsProper f]

omit [IsAlgClosed k] in
/-- **The strict-transform part of the crepant boundary.** For a proper birational morphism
`f : Y ⟶ X` from a normal variety, a prime divisor `G` of `Y` that is not `f`-exceptional is the
birational transform `f⁻¹_* P` of a prime divisor `P` of `X`, and the crepant boundary `Δ_Y` has
`coeff_G(Δ_Y) = coeff_P(Δ)`. -/
public theorem exists_coeff_eq_of_not_isExceptional (hP : IsPairWith sX n K Δ)
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) {G : MMP.Mori.PrimeDivisor Y}
    (hG : ¬ (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, ΔY.coeff G = Δ.coeff P ∧
      f G.genericPoint = P.genericPoint ∧ inverseTransformPrimeDivisor f P = some G := by
  obtain ⟨P, hc, hd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP _ hG
  have hη : f G.genericPoint = P.genericPoint := by
    refine (inseparable_iff_closure_eq.2 ?_).eq
    rw [← DivisorOver.center_eq_closure_genericPoint (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX), hc,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine ⟨P, neg_injective ((hΔY G).eq hd), hη, ?_⟩
  exact MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hη
    (hη ▸ genericPoint_mem_biregularLocus hP.1.1 hY.1 hf P)

/-- **The discrepancy via a proper birational model.** Let `f : Y ⟶ X` be a proper birational
morphism from a normal variety with canonical divisor `K_Y`, and `Δ_Y` the crepant boundary of
`(X, Δ)` on `Y`. Then `discrep(X, Δ)` is the minimum of `discrep(Y, Δ_Y)` and the discrepancies
`a(E, X, Δ)` of the `f`-exceptional prime divisors `E` of `Y`. -/
private theorem discrep_eq_min_of_isCrepantBoundary [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (hP : IsPairWith sX n K Δ) (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) {KY : Divisor Y} (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    {ΔY : QDivisor Y} (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY)
    (a : MMP.Mori.PrimeDivisor Y → ℚ)
    (ha : ∀ E : MMP.Mori.PrimeDivisor Y, (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).IsExceptional →
      IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf, E⟩ (a E)) :
    discrep sX n K Δ = min (discrep (f ≫ sX) n KY ΔY)
      (⨅ (E : MMP.Mori.PrimeDivisor Y) (_ : (⟨Y, f, hY, hf, E⟩ : DivisorOver k sX).IsExceptional),
        ((a E : ℝ) : EReal)) := by
  obtain ⟨hX, hK, -⟩ := id hP
  have : IsDominant f := hf.isDominant
  obtain ⟨-, hcr⟩ := IsPair.isDiscrepancy_iff_of_crepant hP.isPair f hY hf hK hKY (Or.inl hΔY)
  refine le_antisymm (le_min ?_ (le_iInf₂ fun E hE => discrep_le hE (ha E hE))) ?_
  · -- a divisor exceptional over `Y` is exceptional over `X`, with the same discrepancy
    refine le_discrep_iff.mpr fun E b hE hb => ?_
    have hv := valuation_compDivisorOver f hY hf E
    refine discrep_le ?_ ((hcr E _ hv b).mp hb)
    by_contra hne
    obtain ⟨P, hPv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX _ hne
    obtain ⟨G, -, hηG⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P
      (genericPoint_mem_biregularLocus hX.1 hY.1 hf P)
    have hGv := MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX
      (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX) P hηG
    refine (isExceptional_iff_forall_valuation_ne hY E).mp hE G ?_
    ext t
    obtain ⟨s, rfl⟩ := hf.functionFieldMap_bijective.2 t
    exact congrArg (· s)
      (hv.symm.trans <| hPv.trans <| hGv.symm.trans <| valuation_mk_eq_comap f hY hf G)
  · -- a divisor exceptional over `X` is a divisor over `Y`, exceptional or a prime divisor of `Y`
    refine le_discrep_iff.mpr fun D b hD hb => ?_
    obtain ⟨E, hE⟩ := exists_divisorOver_comap_eq hY hf D
    by_cases hEx : E.IsExceptional
    · exact (min_le_left _ _).trans (discrep_le hEx ((hcr E D hE b).mpr hb))
    obtain ⟨G, hGv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hY E hEx
    have hval : D.valuation = (⟨Y, f, hY, hf, G⟩ : DivisorOver k sX).valuation := by
      rw [hE, hGv]; exact (valuation_mk_eq_comap f hY hf G).symm
    have hGe := isExceptional_of_valuation_eq hX hval hD
    rw [MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP hval hb (ha G hGe)]
    exact (min_le_right _ _).trans (iInf₂_le G hGe)

end LogResolution

/-- **The discrepancy from a log resolution** (Kollár–Mori, Cor. 2.32(2)). Let `(X, Δ)` be a pair
with canonical divisor `K` of dimension `n ≥ 2` over an algebraically closed field of
characteristic zero, with `coeff_P Δ ≤ 1` for every prime divisor `P`, and let `f : Y ⟶ X` be a
log resolution of `(X, Δ)`, `Y` a normal variety, such that the birational transforms
`f⁻¹_* P` of the components `P` of `Δ` are smooth and pairwise disjoint. Let `a E` be the
discrepancy `a(E, X, Δ)` of each `f`-exceptional prime divisor `E` of `Y`, and suppose all of
them are `≥ -1`. Then
`discrep(X, Δ) = min {inf_E a E, inf_{P ∈ Supp Δ} (1 - coeff_P Δ), 1}`. -/
@[mmp "prop_km2b_discrep_from_log_resolution"]
public theorem discrep_eq_min_of_isLogResolution {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hP : IsPairWith sX n K Δ) (hn : 2 ≤ n) (hΔ : ∀ P : PrimeDivisor X, Δ.coeff P ≤ 1)
    {f : Y ⟶ X} (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hY : IsNormalVariety k (f ≫ sX))
    (hsmooth : ∀ P ∈ Δ.support, ∀ E : PrimeDivisor Y, inverseTransformPrimeDivisor f P = some E →
      IsSmoothScheme (E.idealSheaf.subschemeι ≫ f ≫ sX))
    (hdisj : ∀ P ∈ Δ.support, ∀ Q ∈ Δ.support, P ≠ Q → ∀ E E' : PrimeDivisor Y,
      inverseTransformPrimeDivisor f P = some E → inverseTransformPrimeDivisor f Q = some E' →
        Disjoint (E.support : Set Y) E'.support)
    (a : PrimeDivisor Y → ℚ)
    (ha : ∀ E : PrimeDivisor Y,
      (⟨Y, f, hY, hf.isBirationalMorphism, E⟩ : DivisorOver k sX).IsExceptional →
        IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf.isBirationalMorphism, E⟩ (a E))
    (h1 : ∀ E : PrimeDivisor Y,
      (⟨Y, f, hY, hf.isBirationalMorphism, E⟩ : DivisorOver k sX).IsExceptional → -1 ≤ a E) :
    discrep sX n K Δ =
      min (⨅ (E : PrimeDivisor Y)
          (_ : (⟨Y, f, hY, hf.isBirationalMorphism, E⟩ : DivisorOver k sX).IsExceptional),
          ((a E : ℝ) : EReal))
        (min (⨅ P ∈ Δ.support, (((1 - Δ.coeff P : ℚ) : ℝ) : EReal)) 1) := by
  have hX : IsNormalVariety k sX := hP.1
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsNormal Y := hY.2
  have : IsProper f := hf.isProper
  have : MMP.Mori.IsVariety k sX := hX.1
  have : MMP.Mori.IsVariety k (f ≫ sX) := hY.1
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  set hfb := hf.isBirationalMorphism
  let DG : MMP.Mori.PrimeDivisor Y → DivisorOver k sX := fun G => ⟨Y, f, hY, hfb, G⟩
  -- a canonical divisor on `Y` and the crepant boundary `Δ_Y`
  have hdimY : topologicalKrullDim Y = n := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hfb]
    exact hP.2.1.topologicalKrullDim_eq
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hf.isSmoothScheme hdimY
  obtain ⟨⟨ΔY, hΔY, -⟩, -⟩ :=
    IsPair.existsUnique_isCrepantBoundary hP.isPair hP.2.1 f hY hfb
  rw [discrep_eq_min_of_isCrepantBoundary hP hY hfb hKY hΔY a ha]
  -- the coefficients of `Δ_Y` are at most `1`, and its support lies in the snc divisor
  have hexc : ∀ G, (DG G).IsExceptional → a G = -ΔY.coeff G := fun G hG =>
    (ha G hG).eq (hΔY G)
  have hcoeff1 : ∀ G, ΔY.coeff G ≤ 1 := by
    intro G
    by_cases hG : (DG G).IsExceptional
    · linarith [hexc G hG, h1 G hG]
    · obtain ⟨P, hc, -⟩ := exists_coeff_eq_of_not_isExceptional hP hY hfb hΔY hG
      exact hc ▸ hΔ P
  obtain ⟨S, hsncS, hmemS⟩ := exists_finset_isSNC hf.isSmoothScheme hf.isSNCSubset
  have hpre : ∀ G : MMP.Mori.PrimeDivisor Y, ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P ≠ 0 →
      f G.genericPoint = P.genericPoint → G ∈ S := by
    intro G P hP0 hη
    refine hmemS G (Or.inr ?_)
    change f G.genericPoint ∈ (QDivisor.toRDivisor Δ).supp
    rw [QDivisor.supp_toRDivisor, hη]
    exact DivisorWithCoeffs.support_subset_supp hP0
      (MMP.Flips.primeDivisor_genericPoint_mem_support P)
  have hS : ΔY.support ⊆ S := by
    intro G hG
    by_cases hGe : (DG G).IsExceptional
    · exact hmemS G (Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
        (MMP.Flips.primeDivisor_genericPoint_mem_support G)))
    · obtain ⟨P, hc, hη, -⟩ := exists_coeff_eq_of_not_isExceptional hP hY hfb hΔY hGe
      exact hpre G P (hc ▸ Finsupp.mem_support_iff.mp hG) hη
  rw [discrep_eq_of_isSNC (f ≫ sX) hY hf.isSmoothScheme hn hKY S hS hsncS (fun G _ => hcoeff1 G)]
  -- the right-hand side `R` bounds every term of the snc formula from below
  set R : EReal := min (⨅ (E : MMP.Mori.PrimeDivisor Y)
          (_ : (⟨Y, f, hY, hf.isBirationalMorphism, E⟩ : DivisorOver k sX).IsExceptional),
          ((a E : ℝ) : EReal))
        (min (⨅ P ∈ Δ.support, (((1 - Δ.coeff P : ℚ) : ℝ) : EReal)) 1)
  have hA : ∀ G, (DG G).IsExceptional → R ≤ ((a G : ℝ) : EReal) := fun G hG =>
    (min_le_left _ _).trans (iInf₂_le G hG)
  have hone : R ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hBP : ∀ P : MMP.Mori.PrimeDivisor X, R ≤ (((1 - Δ.coeff P : ℚ) : ℝ) : EReal) := by
    intro P
    by_cases hP0 : Δ.coeff P = 0
    · rw [hP0, sub_zero]; simpa using hone
    · exact (min_le_right _ _).trans
        ((min_le_left _ _).trans (iInf₂_le P (Finsupp.mem_support_iff.mpr hP0)))
  have hmono : ∀ {x y : ℚ}, R ≤ ((x : ℝ) : EReal) → x ≤ y → R ≤ ((y : ℝ) : EReal) :=
    fun hx hxy => hx.trans (EReal.coe_le_coe_iff.mpr (by exact_mod_cast hxy))
  refine le_antisymm (le_min inf_le_right (le_min ?_ (inf_le_left.trans inf_le_right)))
    (le_min (le_inf (le_inf ?_ ?_) hone) (min_le_left _ _))
  · -- each boundary component `Dⱼ` has a transform in `S` with coefficient `aⱼ`
    refine le_iInf₂ fun P hPΔ => inf_le_left.trans (inf_le_left.trans (inf_le_right.trans ?_))
    obtain ⟨G, -, hηG⟩ := MMP.Flips.exists_inverseTransformPrimeDivisor_eq_some P
      (genericPoint_mem_biregularLocus hX.1 hY.1 hfb P)
    have hGe : ¬ (DG G).IsExceptional := by
      rw [isExceptional_iff_forall_valuation_ne hX, not_forall]
      exact ⟨P, not_not.mpr (MMP.Positivity.DivisorOver.valuation_eq_of_map_genericPoint_eq hX
        (DG G) P hηG)⟩
    obtain ⟨P', hc, hη', -⟩ := exists_coeff_eq_of_not_isExceptional hP hY hfb hΔY hGe
    obtain rfl : P' = P :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hη'.symm.trans hηG)
    refine (iInf₂_le G (hpre G P' (Finsupp.mem_support_iff.mp hPΔ) hηG)).trans ?_
    rw [hc]
  · -- pairs of meeting components of `S`
    refine le_iInf₂ fun G _ => le_iInf₂ fun F _ => le_iInf₂ fun hGF hmeet => ?_
    by_cases hG : (DG G).IsExceptional
    · exact hmono (hA G hG) (by linarith [hexc G hG, hcoeff1 F])
    by_cases hF : (DG F).IsExceptional
    · exact hmono (hA F hF) (by linarith [hexc F hF, hcoeff1 G])
    obtain ⟨P, hcP, -, hiP⟩ := exists_coeff_eq_of_not_isExceptional hP hY hfb hΔY hG
    obtain ⟨Q, hcQ, -, hiQ⟩ := exists_coeff_eq_of_not_isExceptional hP hY hfb hΔY hF
    rw [hcP, hcQ]
    by_cases hP0 : Δ.coeff P = 0
    · rw [hP0, sub_zero]; exact hBP Q
    by_cases hQ0 : Δ.coeff Q = 0
    · rw [hQ0, sub_zero]; exact hBP P
    exfalso
    by_cases hPQ : P = Q
    · subst hPQ
      exact hGF (Option.some.inj (hiP.symm.trans hiQ))
    · exact (Set.not_disjoint_iff_nonempty_inter.mpr hmeet)
        (hdisj P (Finsupp.mem_support_iff.mpr hP0) Q (Finsupp.mem_support_iff.mpr hQ0) hPQ
          G F hiP hiQ)
  · -- single components of `S`
    refine le_iInf₂ fun G _ => ?_
    by_cases hG : (DG G).IsExceptional
    · exact hmono (hA G hG) (by linarith [hexc G hG])
    · obtain ⟨P, hcP, -⟩ := exists_coeff_eq_of_not_isExceptional hP hY hfb hΔY hG
      rw [hcP]; exact hBP P

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **A uniform lower bound for discrepancies with center in `Z`** (Kollár–Mori, proof of
Proposition 2.40). Let `k` be algebraically closed of characteristic zero and `(X, Δ)` a pair
over `k` with canonical divisor `K` of dimension `n` and all
coefficients of `Δ` in `[0, 1]`, and `Z ⊊ X` closed with `X \ Z` in the smooth locus and
`Δ|_{X \ Z}` snc. If `f : Y ⟶ X` is a log resolution of `(X, Δ)` with `f⁻¹(Z)` of pure
codimension one (or empty), `Ex(f) ∪ f⁻¹(Supp Δ) ∪ f⁻¹(Z)` an snc divisor, and
`a(G, X, Δ) > -1` for every prime divisor `G` of `Y` contained in `f⁻¹(Z)`, then there is a
rational `δ > 0` with `a(E, X, Δ) ≥ -1 + δ` for every divisor `E` over `X` whose center lies
in `Z`. -/
@[mmp "lem_km2b_log_resolution_uniform_bound"]
public theorem exists_pos_forall_le_discrepancy_of_isLogResolution
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X}
    (hΔ : IsPairWith sX n K Δ) (hcoeff : ∀ P : PrimeDivisor X, 0 ≤ Δ.coeff P ∧ Δ.coeff P ≤ 1)
    {Z : Closeds X} (hZ : Z ≠ ⊤) (hsmooth : (Z.compl : X.Opens) ≤ smoothLocus sX)
    (hsnc : (Δ.restrictOpen (Z.compl : X.Opens)).IsSNC (Scheme.Opens.ι (X := X) Z.compl ≫ sX))
    {f : Y ⟶ X} (hf : IsLogResolution sX (QDivisor.toRDivisor Δ) f)
    (hZY : IsPureCodimOne (Z.preimage f.continuous))
    (hS : IsSNCSubset (f ≫ sX)
      (exceptionalSet f ⊔ Δ.supp.preimage f.continuous ⊔ Z.preimage f.continuous))
    (hG : ∀ (hY : IsNormalVariety k (f ≫ sX)) (G : PrimeDivisor Y),
      G.support ⊆ f ⁻¹' (Z : Set X) → ∀ a : ℚ,
        IsDiscrepancy sX n K Δ ⟨Y, f, hY, hf.isBirationalMorphism, G⟩ a → -1 < a) :
    ∃ δ : ℚ, 0 < δ ∧ ∀ (E : DivisorOver k sX) (a : ℚ), (E.center : Set X) ⊆ Z →
      IsDiscrepancy sX n K Δ E a → -1 + δ ≤ a := by
  classical
  have hX : IsNormalVariety k sX := hΔ.1
  obtain ⟨hY, hdimY, -⟩ := hf.toIsSmoothResolution.isNormalVariety hX
  have : IsIntegral Y := hY.1.toIsIntegral
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : IsNormal Y := hY.2
  have : IsProper f := hf.isProper
  have : MMP.Mori.IsVariety k sX := hX.1
  have : MMP.Mori.IsVariety k (f ≫ sX) := hY.1
  have : IsDominant f := hf.isBirationalMorphism.isDominant
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  set hfb := hf.isBirationalMorphism
  let DG : MMP.Mori.PrimeDivisor Y → DivisorOver k sX := fun G => ⟨Y, f, hY, hfb, G⟩
  -- a canonical divisor `K_Y` and the crepant boundary `Δ_Y`
  obtain ⟨KY, hKY⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hf.isSmoothScheme
    (hdimY.trans hΔ.2.1.topologicalKrullDim_eq)
  obtain ⟨⟨ΔY, hΔY, -⟩, -⟩ := IsPair.existsUnique_isCrepantBoundary hΔ.isPair hΔ.2.1 f hY hfb
  obtain ⟨-, hcr⟩ := IsPair.isDiscrepancy_iff_of_crepant hΔ.isPair f hY hfb hΔ.2.1 hKY (Or.inl hΔY)
  -- the components of the snc divisor `S`
  obtain ⟨S, hsncS, hmemS⟩ := exists_finset_isSNC hf.isSmoothScheme hS
  have hZS : ∀ G : MMP.Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ f ⁻¹' (Z : Set X) → G ∈ S :=
    fun G hG => hmemS G (Or.inr (hG (MMP.Flips.primeDivisor_genericPoint_mem_support G)))
  have hsuppZ : ∀ G : MMP.Mori.PrimeDivisor Y, f G.genericPoint ∈ Z →
      (G.support : Set Y) ⊆ f ⁻¹' (Z : Set X) := fun G hG => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.mpr hG) (Z.isClosed.preimage f.continuous)
  -- the coefficients of `Δ_Y`
  have hlt : ∀ G : MMP.Mori.PrimeDivisor Y, (G.support : Set Y) ⊆ f ⁻¹' (Z : Set X) →
      ΔY.coeff G < 1 := fun G hGZ => by
    linarith [hG hY G hGZ _ (hΔY G)]
  have hcoeff1 : ∀ G, ΔY.coeff G ≤ 1 := by
    intro G
    by_cases hGZ : (G.support : Set Y) ⊆ f ⁻¹' (Z : Set X)
    · exact (hlt G hGZ).le
    have hU : f G.genericPoint ∈ (Z.compl : X.Opens) := fun h => hGZ (hsuppZ G h)
    linarith [neg_one_le_of_isSNC_restrictOpen hΔ (fun P => (hcoeff P).2) hsmooth hsnc
      ⟨_, by rw [(DG G).center_eq_closure_genericPoint]; exact subset_closure rfl, hU⟩ (hΔY G)]
  have hsupp : ΔY.support ⊆ S := by
    intro G hG
    by_cases hGe : (DG G).IsExceptional
    · exact hmemS G (Or.inl (Or.inl (MMP.Positivity.support_subset_exceptionalSet G hGe
        (MMP.Flips.primeDivisor_genericPoint_mem_support G))))
    · obtain ⟨P, hc, hη, -⟩ := exists_coeff_eq_of_not_isExceptional hΔ hY hfb hΔY hGe
      refine hmemS G (Or.inl (Or.inr ?_))
      change f G.genericPoint ∈ Δ.supp
      rw [hη]
      exact DivisorWithCoeffs.support_subset_supp (hc ▸ Finsupp.mem_support_iff.mp hG)
        (MMP.Flips.primeDivisor_genericPoint_mem_support P)
  -- the uniform bound `δ`
  obtain ⟨ε, hε, hεle⟩ := exists_pos_forall_le S
    (fun G => (G.support : Set Y) ⊆ f ⁻¹' (Z : Set X)) (fun G => 1 - ΔY.coeff G)
    (fun G _ hGZ => by linarith [hlt G hGZ])
  refine ⟨ε, hε, fun E a hEZ ha => ?_⟩
  -- `E` is a divisor `E'` over `Y`, with center in `f⁻¹(Z)`
  obtain ⟨E', hE'⟩ := exists_divisorOver_comap_eq hY hfb E
  have hval : E.valuation = (compDivisorOver f hY hfb E').valuation := by
    rwa [valuation_compDivisorOver]
  have hη : E.f E.E.genericPoint = f (E'.f E'.E.genericPoint) :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hval
  have hyZ : f (E'.f E'.E.genericPoint) ∈ Z := by
    rw [← hη]
    exact hEZ (by rw [E.center_eq_closure_genericPoint]; exact subset_closure rfl)
  by_cases hEx : E'.IsExceptional
  · -- `E'` is exceptional over `Y`: the snc bound on `(Y, Δ_Y)` along a component of `f⁻¹(Z)`
    obtain ⟨G₀, hG₀Z, hyG₀⟩ := exists_primeDivisor_of_isPureCodimOne hZY hyZ
    linarith [neg_one_add_le_of_genericPoint_mem hY hf.isSmoothScheme hKY hsupp hsncS hcoeff1
      (hZS G₀ hG₀Z) E' hEx hyG₀ ((hcr E' E hE' a).mpr ha), hεle G₀ (hZS G₀ hG₀Z) hG₀Z]
  · -- `E'` is a prime divisor `G` of `Y`, contained in `f⁻¹(Z)`
    obtain ⟨G, hGv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hY E' hEx
    have hval' : E.valuation = (DG G).valuation := by
      rw [hE', hGv]; exact (valuation_mk_eq_comap f hY hfb G).symm
    have ha' := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hΔ hval' ha (hΔY G)
    have hηG : E'.f E'.E.genericPoint = G.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hGv
    have hGZ := hsuppZ G (hηG ▸ hyZ)
    linarith [hεle G (hZS G hGZ) hGZ]

end

/-! ### Smoothness of surface germs -/

section SurfaceGerm

open MMP.Resolution.Bridges (finiteFibreLocus isOpen_finiteFibreLocus_and_isIso)

/-- A resolution `f` of a normal surface whose fibre over `x` is infinite has an exceptional
curve contracted to `x`. -/
private theorem exists_isExceptionalCurve_of_infinite {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (hdim : topologicalKrullDim X = 2)
    {f : Y ⟶ X} (hf : IsSmoothResolution sX f) {x : X}
    (hx : x ∉ finiteFibreLocus f) : ∃ C : Y.IdealSheafData, IsExceptionalCurve f C := by
  obtain ⟨hYv, hdimY, hbir⟩ := hf.isNormalVariety hX
  have hXv := hX.1
  have : IsIntegral X := hXv.toIsIntegral
  have : IsNormal X := hX.2
  have : IsIntegral Y := hf.isIntegral
  have : IsProper f := hf.isProper
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  have : QuasiCompact sX := hXv.toQuasiCompact
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ sX)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := ⟨⟩
  have hdY : topologicalKrullDim Y ≤ 2 := by rw [hdimY, hdim]
  have hxc : IsClosed ({x} : Set X) :=
    (finite_and_isClosed_singleton_compl_finiteFibreLocus f hbir hdY).2 x hx
  have hT : IsClosed (f.base ⁻¹' {x}) := hxc.preimage f.continuous
  obtain ⟨Z, hZf, hZc, hZirr, hZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hT
  obtain ⟨W, hWZ, hWinf⟩ : ∃ W ∈ Z, W.Infinite := by
    by_contra! h
    exact hx (show (f.base ⁻¹' {x}).Finite from hZ ▸ Set.Finite.sUnion hZf h)
  have hWsub : W ⊆ f.base ⁻¹' {x} := hZ ▸ Set.subset_sUnion_of_mem hWZ
  obtain ⟨g, hg⟩ := QuasiSober.sober (hZirr W hWZ) (hZc W hWZ)
  have hgcl : ¬ IsClosed ({g} : Set Y) := fun h ↦ hWinf (by
    rw [← hg.def, h.closure_eq]; exact Set.finite_singleton g)
  obtain ⟨c, -, hgc, hne⟩ := exists_isClosed_singleton_specializes hgcl
  have hWne : W ≠ Set.univ := fun h ↦ hx <|
    (hWsub (h ▸ Set.mem_univ (genericPoint Y)) : f (genericPoint Y) = x) ▸
      map_genericPoint_mem_finiteFibreLocus f hbir
  have hcW : c ∈ W := hg.def ▸ specializes_iff_mem_closure.mp hgc
  have hdimW : topologicalKrullDim W = 1 :=
    topologicalKrullDim_eq_one_of_ne_univ hdY (hZc W hWZ) hWne hg.mem hcW hgc hne
  set C := Scheme.IdealSheafData.vanishingIdeal ⟨W, hZc W hWZ⟩ with hCdef
  have hsupp : (C.support : Set Y) = W := by
    rw [hCdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsIntegral C.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ (hZirr W hWZ)
  refine ⟨C, ⟨this, by rw [topologicalKrullDim_subscheme_eq, hsupp, hdimW]⟩, x, ?_⟩
  rw [hsupp]
  exact (Set.image_nonempty.mpr ⟨g, hg.mem⟩).subset_singleton_iff.mp
    (Set.image_subset_iff.mpr hWsub)

/-- Let `(x ∈ X)` be a surface germ over an algebraically closed field `k` and `f : Y ⟶ X` a
minimal resolution. Then `X` is smooth at `x` if and only if `f` has no exceptional curve. -/
@[mmp "lem_km4a_germ_smooth_iff_no_exceptional_curve"]
public theorem mem_smoothLocus_iff_forall_not_isExceptionalCurve {k : Type u} [Field k]
    [IsAlgClosed k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) {x : X}
    (hx : IsSurfaceGerm sX x) (f : Y ⟶ X) [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] (hf : IsMinimalSurfaceResolution sX f) :
    x ∈ smoothLocus sX ↔ ∀ C : Y.IdealSheafData, ¬ IsExceptionalCurve f C := by
  obtain ⟨hX, hdim, -, hsm⟩ := hx
  constructor
  · intro hxs C ⟨hC, y, hy⟩
    have hfy : ∀ a ∈ (C.support : Set Y), f a = y := fun a ha ↦
      Set.mem_singleton_iff.mp (hy ▸ Set.mem_image_of_mem f.base ha)
    have hys : y ∈ smoothLocus sX := by
      by_cases hz : y = x
      · exact hz ▸ hxs
      · exact hsm y hz
    have := isIso_morphismRestrict_smoothLocus_of_isMinimalSurfaceResolution sX f hX hdim hf
    exact hC.not_subsingleton fun a ha b hb ↦ Stacks.Models.eq_of_isIso_morphismRestrict f
      (smoothLocus sX) (hfy a ha ▸ hys) ((hfy a ha).trans (hfy b hb).symm)
  · intro h
    have hres := hf.1
    obtain ⟨hYv, -, hbir⟩ := hres.isNormalVariety hX
    have : IsIntegral X := hX.1.toIsIntegral
    have : IsNormal X := hX.2
    have : IsIntegral Y := hres.isIntegral
    have : IsProper f := hres.isProper
    have hfin : x ∈ finiteFibreLocus f := of_not_not fun hx' ↦
      let ⟨C, hC⟩ := exists_isExceptionalCurve_of_infinite hX hdim hres hx'
      h C hC
    obtain ⟨hU, hiso⟩ := (isOpen_finiteFibreLocus_and_isIso f hbir).1 inferInstance
    let V : X.Opens := ⟨finiteFibreLocus f, hU⟩
    have : LocallyOfFiniteType (f ≫ sX) := hYv.1.toLocallyOfFiniteType
    have : Smooth (f ≫ sX) := (isSmoothScheme_iff _).mp hres.isSmoothScheme
    have : Smooth (V.ι ≫ sX) := by
      rw [show V.ι ≫ sX = inv (f ∣_ V) ≫ (f ⁻¹ᵁ V).ι ≫ f ≫ sX by
        rw [← morphismRestrict_ι_assoc, IsIso.inv_hom_id_assoc]]
      infer_instance
    exact le_smoothLocus sX this hfin

end SurfaceGerm

end MMP.Mori

/-! ### The two dlt predicates -/

namespace MMP.Threefold.Bridges

open MMP.Mori

section Nagata

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- The normalization of `P` in a normal integral locally Noetherian scheme `Y`, along a
quasi-compact open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal
and finite over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {Y P : Scheme.{u}}
    {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P) [IsOpenImmersion j]
    [QuasiCompact j] [QuasiSeparated j] [IsNormal Y] [IsLocallyNoetherian Y] :
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
  obtain ⟨W, hW, hWo⟩ := h.exists_isOpenImmersion
  let U : P.Opens := t ''ᵁ W
  let V : Z.Opens := (W.ι ≫ t ≫ g).opensRange
  have hUV : U ≤ g ⁻¹ᵁ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hU : U.ι ≫ g = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [← Scheme.Hom.isoImage_inv_ι_assoc]
  have hc : g.resLE V U hUV ≫ V.ι = (t.isoImage W).inv ≫ W.ι ≫ t ≫ g := by
    rw [Scheme.Hom.resLE_comp_ι, hU]
  have : IsOpenImmersion (g.resLE V U hUV ≫ V.ι) := by rw [hc]; infer_instance
  have : IsOpenImmersion (g.resLE V U hUV) := IsOpenImmersion.of_comp _ V.ι
  obtain ⟨w, hw⟩ := hW
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V ⟨t w, w, hw, rfl⟩
    ⟨_, ⟨w, hw⟩, rfl⟩ hUV ?_
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
  obtain ⟨w', rfl⟩ := hz
  refine ⟨(t.isoImage W).hom w', ?_⟩
  apply V.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  rfl

/-- **Nagata compactification**, in the form used here: a separated morphism of finite type
`f : Y ⟶ X` to a quasi-compact quasi-separated scheme factors as a quasi-compact open immersion
followed by a proper morphism. -/
private theorem exists_isOpenImmersion_isProper_comp_eq {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ (P : Scheme.{u}) (j : Y ⟶ P) (p : P ⟶ Z), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsProper p ∧ j ≫ p = f := by
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
  exact ⟨c.space, c.immersion, c.toBase, inferInstance, hc, inferInstance, Over.w c.obj.hom⟩

omit [IsNormal X] in
/-- **KM 2.22 for `g = 𝟙`.** Every divisor `(Y, f, E)` over a normal variety `X` (with `f` not
necessarily proper) has the valuation of a divisor over `X` with `f` proper. -/
public theorem exists_properDivisorOver_valuation_eq (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) : ∃ E : MMP.Flips.ProperDivisorOver k sX, E.valuation = D.valuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have hYv := D.isNormalVariety.1
  have hXv := hX.1
  have : IsSeparated sX := hXv.toIsSeparated
  have : IsSeparated (D.f ≫ sX) := hYv.toIsSeparated
  have : LocallyOfFiniteType (D.f ≫ sX) := hYv.toLocallyOfFiniteType
  have : QuasiCompact (D.f ≫ sX) := hYv.toQuasiCompact
  have : IsSeparated D.f := IsSeparated.of_comp D.f sX
  have : LocallyOfFiniteType D.f := locallyOfFiniteType_of_comp D.f sX
  have : QuasiCompact D.f := QuasiCompact.of_comp D.f sX
  have : IsNoetherian X := {}
  obtain ⟨P, j, p, hj, hjq, hp, hjp⟩ := exists_isOpenImmersion_isProper_comp_eq D.f
  have : IsSeparated j := by
    have : IsSeparated (j ≫ p) := by rw [hjp]; infer_instance
    exact IsSeparated.of_comp j p
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
  refine ⟨⟨D', inferInstance⟩, (MMP.Positivity.DivisorOver.valuation_eq_of_iso D D' ⊤
    t.opensRange trivial ⟨D.E.genericPoint, ?_⟩ (D.Y.topIso ≪≫ t.isoOpensRange) ?_ ?_).symm⟩
  · exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm
  · simp [D', htg]
  · apply Subtype.ext
    change (D.Y.topIso.hom ≫ t.isoOpensRange.hom ≫ t.opensRange.ι) ⟨D.E.genericPoint, trivial⟩ = _
    rw [Scheme.Hom.isoOpensRange_hom_ι]
    exact (OpenWeilRestriction.genericPoint_primeDivisorMap t D.E).symm

/-- **The dlt positivity condition, from proper models to all divisors.** If the log discrepancy
`A(E, X, Δ)` is positive for every divisor over `X` centred in `Z` (log discrepancies exist only
for proper models), then the discrepancy `a(E, X, Δ)` of every divisor `(Y, f, E)` over `X`
centred in `Z`, with `f` arbitrary, is `> -1`. -/
public theorem neg_one_lt_of_forall_isLogDiscrepancy_pos [PerfectField k] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} (hP : IsPairWith sX n K Δ) {Z : Set X}
    (hpos : ∀ D : DivisorOver k sX, (D.center : Set X) ⊆ Z →
      ∀ b : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor Δ) D b → 0 < b)
    {D : DivisorOver k sX} (hDZ : (D.center : Set X) ⊆ Z) {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) : -1 < a := by
  obtain ⟨E, hE⟩ := exists_properDivisorOver_valuation_eq hP.1 D
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hP.2.1
    E.toDivisorOver
  have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hP.1 hE
  have hEZ : (E.toDivisorOver.center : Set X) ⊆ Z := by
    rwa [E.toDivisorOver.center_eq_closure_genericPoint, hc, ← D.center_eq_closure_genericPoint]
  have h1 := hpos _ hEZ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha' E.isProper)
  rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE.symm hc.symm ha ha']
  exact_mod_cast (by linarith : (-1 : ℝ) < a')

end Nagata

/-- A log discrepancy `A(E, X, Δ)` of a pair, at any index, is `1 + a(E, X, Δ)` for the
Kollár–Mori discrepancy computed with a given canonical divisor `K`. -/
public theorem exists_isDiscrepancy_of_isLogDiscrepancy {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n n' : ℕ} {K : Divisor X} {Δ : QDivisor X} (hP : IsPair sX Δ)
    (hK : K.IsCanonicalDivisor sX n) {D : DivisorOver k sX} {b : ℝ}
    (hb : MMP.Intersection.IsLogDiscrepancy sX n' (QDivisor.toRDivisor Δ) D b) :
    ∃ a : ℚ, IsDiscrepancy sX n K Δ D a ∧ b = 1 + a := by
  obtain rfl : n' = n := by
    exact_mod_cast (MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq hb).symm.trans
      hK.topologicalKrullDim_eq
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  exact ⟨a, ha, ((MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy ha b).mp hb).2⟩

/-- Every discrepancy of a Kollár–Mori lc pair with coefficients `≤ 1` is `≥ -1`: for an
exceptional divisor this is the lc bound, and otherwise the discrepancy is minus a coefficient of
`Δ`. -/
private theorem neg_one_le_of_isLcPair {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (h : IsLcPair sX n K Δ)
    (h1 : ∀ P, Δ.coeff P ≤ 1) {D : DivisorOver k sX} {a : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) : -1 ≤ a := by
  by_cases hD : D.IsExceptional
  · have := h.2.trans (discrep_le hD ha)
    rw [show (-1 : EReal) = ((-1 : ℝ) : EReal) by simp] at this
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  · exact neg_one_le_of_not_isExceptional h1 hD ha

/-- **The two dlt predicates agree.** For a normal variety `X` over an algebraically closed
field `k` of characteristic zero with canonical divisor `K` of dimension `n`, and a `ℚ`-divisor
`Δ` on `X`, the pair `(X, Δ)` is dlt in the sense of `MMP.Intersection.IsDltPair` if and only if
it is dlt in the sense of Kollár–Mori, `MMP.Mori.IsDltPair`. -/
@[mmp "lem_mmp_km_dlt_dictionary"]
public theorem isDltPair_iff_isDltPair {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (Δ : QDivisor X) :
    MMP.Intersection.IsDltPair sX Δ ↔ MMP.Mori.IsDltPair sX n K Δ := by
  constructor
  · rintro ⟨⟨hP, hnn, -⟩, hle1, Z, hsm, hsnc, hpos⟩
    obtain ⟨hX, _, K', hK', hQ'⟩ := hP
    have hXv := hX.1
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
    have hPw : IsPairWith sX n K Δ := ⟨hX, hK, hQ'.add_of_linearlyEquivalent
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK)⟩
    refine ⟨hPw, fun P => ⟨hnn P, hle1 P⟩, Z.compl, le_smoothLocus_of_isSmoothScheme_ι hsm,
      inverseTransformDivisor_ι_eq_restrictOpen (Z.compl : X.Opens) Δ ▸ hsnc,
      fun D a hDZ => neg_one_lt_of_forall_isLogDiscrepancy_pos hPw (hpos n) (by simpa using hDZ)⟩
  · intro h
    obtain ⟨⟨hX, -, hQ⟩, hcoeff, U, hUsm, hsnc, hZ⟩ := id h
    have hP : IsPair sX Δ := ⟨hX, n, K, hK, hQ⟩
    have hUU : U.compl.compl = U := by ext; simp
    refine ⟨⟨hP, fun P => (hcoeff P).1, fun n' D b hb => ?_⟩, fun P => (hcoeff P).2, U.compl,
      by rw [hUU]; exact isSmoothScheme_ι_of_le_smoothLocus hUsm,
      by rw [hUU, inverseTransformDivisor_ι_eq_restrictOpen]; exact hsnc, fun n' D hDZ b hb => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := exists_isDiscrepancy_of_isLogDiscrepancy hP hK hb
      have : (-1 : ℝ) ≤ a := by
        exact_mod_cast neg_one_le_of_isLcPair h.isLcPair (fun P => (hcoeff P).2) ha
      linarith
    · obtain ⟨a, ha, rfl⟩ := exists_isDiscrepancy_of_isLogDiscrepancy hP hK hb
      have : (-1 : ℝ) < a := by exact_mod_cast hZ D a (by simpa using hDZ) ha
      linarith

/-- **Kollár–Mori lc pairs are log canonical.** If `(X, Δ)`, with canonical divisor `K` of
dimension `n`, is lc in the sense of Kollár–Mori and `0 ≤ Δ ≤ 1`, then it is log canonical in the
sense of `MMP.Intersection.IsLogCanonicalPair`: every log discrepancy is `1 + a(E, X, Δ) ≥ 0`. -/
public theorem isLogCanonicalPair_of_isLcPair {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {Δ : QDivisor X} (h : IsLcPair sX n K Δ)
    (h0 : ∀ P, 0 ≤ Δ.coeff P) (h1 : ∀ P, Δ.coeff P ≤ 1) :
    MMP.Intersection.IsLogCanonicalPair sX Δ := by
  refine ⟨h.1.isPair, h0, fun n' D b hb => ?_⟩
  obtain ⟨a, ha, rfl⟩ := exists_isDiscrepancy_of_isLogDiscrepancy h.1.isPair h.1.2.1 hb
  have : (-1 : ℝ) ≤ a := by exact_mod_cast neg_one_le_of_isLcPair h h1 ha
  linarith

/-- **The two lc predicates agree.** For a normal variety `X` over a perfect field with canonical
divisor `K` of dimension `n`, a `ℚ`-divisor `Δ` makes `(X, Δ)` log canonical in the sense of
`MMP.Intersection.IsLogCanonicalPair` if and only if it is lc in the sense of Kollár–Mori,
`MMP.Mori.IsLcPair`, with `0 ≤ Δ ≤ 1`. -/
public theorem isLogCanonicalPair_iff_isLcPair {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) (Δ : QDivisor X) :
    MMP.Intersection.IsLogCanonicalPair sX Δ ↔
      IsLcPair sX n K Δ ∧ ∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ Δ.coeff P ∧ Δ.coeff P ≤ 1 := by
  refine ⟨fun ⟨⟨hX, _, K', hK', hQ'⟩, h0, hlc⟩ => ?_,
    fun ⟨h, hc⟩ => isLogCanonicalPair_of_isLcPair h (fun P => (hc P).1) fun P => (hc P).2⟩
  have : CompactSpace X := haveI := hX.1; QuasiCompact.compactSpace_of_compactSpace sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hP : IsPairWith sX n K Δ := ⟨hX, hK, hQ'.add_of_linearlyEquivalent
    (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK)⟩
  -- every discrepancy is `≥ -1`, read on a proper model with the same valuation
  have hge : ∀ (D : DivisorOver k sX) (a : ℚ), IsDiscrepancy sX n K Δ D a → -1 ≤ a := by
    intro D a ha
    obtain ⟨E, hE⟩ := exists_properDivisorOver_valuation_eq hX D
    obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK E.toDivisorOver
    have hc := MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX hE
    have h := hlc n _ _ (isLogDiscrepancy_one_add_of_isDiscrepancy ha' E.isProper)
    rw [MMP.Threefold.Mori.ModelIndependence.isDiscrepancy_eq_of_center_eq hE.symm hc.symm ha ha']
    exact_mod_cast (by linarith : (-1 : ℝ) ≤ a')
  refine ⟨⟨hP, le_discrep_iff.mpr fun D a _ ha => ?_⟩, fun P => ⟨h0 P, ?_⟩⟩
  · simpa using EReal.coe_le_coe_iff.mpr (by exact_mod_cast hge D a ha : (-1 : ℝ) ≤ a)
  · obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK
      (DivisorOver.ofPrimeDivisor k hX P)
    linarith [hge _ a ha, ha.eq_neg_coeff_of_ofPrimeDivisor hX]

end MMP.Threefold.Bridges

end
