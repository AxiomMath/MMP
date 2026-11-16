module
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionPushPull

import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ConductorDefect
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
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
import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Unconditional
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.IdealTwistVanishing
import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOpenImmersion
import StacksFrontier.AlgebraicGeometry.Blowup.StructureSheafPushforward
import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
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
import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.GrothendieckExistenceLevelIso
import StacksFrontier.AlgebraicGeometry.Blowup.PointBlowupHigherDirectImage
import StacksFrontier.AlgebraicGeometry.Blowup.TwistVanishingThreshold
import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupDescent
import StacksFrontier.AlgebraicGeometry.Blowup.RegularCentreLocalCompleteIntersection
import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinateSquare
import StacksFrontier.AlgebraicGeometry.InvertiblePushforwardPullback
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Contraction
import StacksFrontier.AlgebraicGeometry.PicSurjectiveOpen.AffineGenerator
public import MMP.AlgebraicGeometry.Analytic.ComplexScheme.OfProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCentre
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.OneBlowupTotalTransform
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Morphisms.Birational.ExceptionalAntiampleDivisor
import MMP.AlgebraicGeometry.Resolution.SNCWeight.StratumBlowup
import MMP.AlgebraicTopology.BorelMoore.Connecting
import MMP.AlgebraicGeometry.Intersection.CartierRestriction
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.DisjoiningCenter
import MMP.AlgebraicTopology.BorelMoore.RestrictionFunctorial
import MMP.AlgebraicTopology.BorelMoore.DisjointUnion
import MMP.AlgebraicTopology.BorelMoore.RestrictionPushforward
import MMP.AlgebraicGeometry.Resolution.Basic
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.BorelMooreLongExact
import MMP.AlgebraicTopology.PoincareDuality.EmbeddingIndependence.Iterate
import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
import MMP.AlgebraicGeometry.Resolution.ExceptionalDivisorPrime
import MMP.AlgebraicTopology.PoincareDuality.AlexanderCocycleDuality
import MMP.AlgebraicTopology.CapProduct.SupportRetraction
import MMP.AlgebraicTopology.PoincareDuality.AlexanderGeneral
import MMP.AlgebraicGeometry.Intersection.Nef
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicTopology.CapProduct.SupportLemmas
import MMP.AlgebraicTopology.CapProduct.CupSupport
import MMP.AlgebraicTopology.BorelMoore.Suspension
import MMP.AlgebraicTopology.PoincareDuality.AlexanderFiveLemma
import MMP.AlgebraicTopology.BorelMoore.TopHomologyRestriction
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.DualityAntiampleFibre
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ConductorKernel
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.JunctionTerminal
public import MMP.Topology.KrullDimensionProperClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.SubschemeOver

/-!
# Transfer of the vertical defect along boundary-compatible smooth blow-ups

Let `Y` be a normal projective `ℚ`-factorial complex variety and `r : Z ⟶ Y` a projective
resolution by a smooth projective complex fourfold whose full exceptional divisor `F` is a reduced
snc divisor. If `q : Z' ⟶ Z` is a finite sequence of blow-ups along smooth centres having simple
normal crossings with the exceptional locus of the composite to `Y` reached so far, and `F'` is
the full exceptional divisor of `q ≫ r`, there is an injective `ℚ`-linear map
`D_v(q ≫ r) → D_v(r)` of vertical defects carrying `D_{v,Q}(q ≫ r)` into `D_{v,Q}(r)` for every
closed `Q ⊆ Y`.

## Main results

* `MMP.Fourfold.exists_injective_verticalDefect_blowup`: the injection, with its support
  property.

## Implementation notes

* The finite sequences of blow-ups are the least class of morphisms `p : W ⟶ Z` that contains
  `𝟙 Z` and is closed under `p ↦ blowUpToBase I ≫ p` for an ideal sheaf `I` on `W` whose
  subscheme is smooth over `ℂ` and has simple normal crossings
  (`MMP.Resolution.HasSNCWith`) with the irreducible components of `Ex(p ≫ r)`. The proof is by
  induction along this class: the invariant records that the current model is again a smooth
  projective fourfold resolving `Y` whose exceptional locus carries a reduced snc divisor (or is
  empty, after blowing up the zero ideal), together with the transfer map for every reduced
  divisor supported on the exceptional locus.
* For one blow-up with centre `C`, every class of `K_v(q ≫ r)` has a representative `(L'_E)_E`
  with `q_* L'_J = 0` on each new boundary component `J` over the part of `C` of codimension at
  least two; on such representatives the map is `(L'_E)_E ↦ (q_* L'_{e(P)})_P`, where `e(P)` is
  the strict transform of `P`. The source instead adds `a [C]` on a chosen component containing
  a surface centre; the induced map on `D_v` is the same and no choice is made. Injectivity comes
  from the threefold blow-up kernels and the exceptional Gysin step.
* The auxiliary results are in `Proof_thm_mmp_conductor_vertical_defect_blowup_transfer`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP
open scoped MMP.SubschemeOver
open MMP.Intersection.Scheme (Subvariety)

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The rational `k`-cycles `Z_k(X)_ℚ` of a scheme over `ℂ`, in Stacks' encoding. -/
local notation:max "RatCycles" X:max k:max =>
  Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (CommRingCat.of ℂ))
    ((k : ℕ) : ℤ)

/-- Proper push-forward `f_*` of rational `k`-cycles along a morphism over `ℂ` (Stacks 02R4). -/
local notation:max "ratPush" f:max k:max =>
  Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((k : ℕ) : ℤ) f
    (comp_over f (Spec (CommRingCat.of ℂ)))

namespace Proof_thm_mmp_conductor_vertical_defect_blowup_transfer

open MMP MMP.Fourfold MMP.Mori

section Setting

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The standing setting of the vertical defect for a complex model `Z` of `Y`: `Z` is a smooth
projective complex fourfold, `r : Z ⟶ Y` a projective resolution over `ℂ`, and the exceptional
locus of `r` is the support of a reduced snc divisor. -/
private structure IsModel {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] (sY : Y ⟶ Spec (.of ℂ))
    (r : Z ⟶ Y) : Prop where
  isComplexScheme : IsComplexScheme Z
  compactSpace : CompactSpace Z
  isLocallyNoetherian : IsLocallyNoetherian Z
  isNormal : IsNormal Z
  comp_eq : r ≫ sY = Z ↘ Spec (.of ℂ)
  isResolution : MMP.Intersection.IsResolution sY r
  isProjective : IsProjective (Z ↘ Spec (.of ℂ))
  topologicalKrullDim_eq : topologicalKrullDim Z = 4
  exists_divisor : ∃ F : Divisor Z, MMP.Intersection.IsReducedEffective F ∧
    DivisorWithCoeffs.IsSNC (r ≫ sY) F ∧ (F.supp : Set Z) = exceptionalSet r

end Setting

private theorem genericPoint_mem_support {X : Scheme.{0}} (E : MMP.Mori.PrimeDivisor X) :
    E.genericPoint ∈ (E.support : Set X) := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- The generic point of a prime divisor `E` lies on no other prime divisor. -/
private theorem eq_of_genericPoint_mem_support {X : Scheme.{0}} {E E' : MMP.Mori.PrimeDivisor X}
    (h : E.genericPoint ∈ E'.support) : E = E' := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have hle : E.genericPoint ≤ E'.genericPoint := specializes_iff_mem_closure.mpr h
  by_contra hne
  have hne' : E.genericPoint ≠ E'.genericPoint := fun h' =>
    hne (AlgebraicGeometry.PrimeDivisor.genericPoint_injective h')
  have hlt : E.genericPoint < E'.genericPoint :=
    lt_iff_le_not_ge.mpr ⟨hle, fun h' => hne' (Specializes.antisymm h' hle).eq⟩
  have hstep := Order.coheight_add_one_le hlt
  rw [E.coheight_genericPoint, E'.coheight_genericPoint] at hstep
  exact absurd hstep (by decide)

/-- Two reduced effective divisors with the same support are equal. -/
private theorem eq_of_isReducedEffective_of_supp_eq {X : Scheme.{0}} {F F' : Divisor X}
    (hF : MMP.Intersection.IsReducedEffective F) (hF' : MMP.Intersection.IsReducedEffective F')
    (h : (F.supp : Set X) = F'.supp) : F = F' := by
  have key : ∀ {G G' : Divisor X}, MMP.Intersection.IsReducedEffective G' →
      (G.supp : Set X) = G'.supp → ∀ E, G.coeff E ≠ 0 → G'.coeff E = 1 := by
    intro G G' hG' hGG' E hE
    have hη : E.genericPoint ∈ (G'.supp : Set X) :=
      hGG' ▸ DivisorWithCoeffs.support_subset_supp hE (genericPoint_mem_support E)
    obtain ⟨E', hE', hηE'⟩ := DivisorWithCoeffs.mem_supp_iff.mp hη
    rw [eq_of_genericPoint_mem_support hηE']
    exact (hG' E').resolve_left hE'
  refine DivisorWithCoeffs.ext' fun E => ?_
  rcases hF E with h0 | h1
  · rcases hF' E with h0' | h1'
    · rw [h0, h0']
    · have := key hF h.symm E (by rw [h1']; exact one_ne_zero)
      rw [h0] at this
      exact absurd this zero_ne_one
  · rw [h1, key hF' h E (by rw [h1]; exact one_ne_zero)]

section Homology

/-! Rational cycles are Stacks' rational cycles `ℚ ⊗ Z_k(X)` over the Chow situation
`fieldChowSituation ℂ` (`MMP.Chow.RationalCycleGroup`); a point `x` of delta-dimension `k` gives
the rational prime cycle `[x]` (`MMP.Chow.rationalPointCycle`). -/

/-- The rational prime cycles `[x]` of the points of delta-dimension `k` are linearly
independent. -/
private theorem linearIndependent_rationalPointCycle {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (k : ℕ) :
    LinearIndependent ℚ fun x : {x : X // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k} =>
      Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x.1 x.2 := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
    k i.1) hg
  rw [map_sum, map_zero, Finset.sum_eq_single i (fun j _ hji => by
      rw [map_smul, Chow.rationalCoeff_rationalPointCycle,
        if_neg fun h => hji (Subtype.ext h).symm, smul_zero])
      (fun h => absurd hi h), map_smul, Chow.rationalCoeff_rationalPointCycle, if_pos rfl,
    smul_eq_mul, mul_one] at h
  exact h

/-- The rational prime cycles `[x]` of the points of delta-dimension `k` span the rational
`k`-cycles of a complex scheme. -/
private theorem span_rationalPointCycle {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (k : ℕ) :
    ⊤ ≤ Submodule.span ℚ (Set.range fun x : {x : X // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k} =>
      Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x.1 x.2) := by
  rintro α -
  induction α using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul q c =>
    rw [Chow.eq_sum_pointCycleOrZero c, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hxk : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) x = k :=
      (Stacks.Chow.mem_cyclesOfDimension_iff_forall_point (Stacks.Chow.fieldChowSituation ℂ) _ k
        c.1).mp c.2 x ((Chow.finite_support_cycle c).mem_toFinset.mp hx)
    rw [TensorProduct.tmul_smul, Chow.pointCycleOrZero, dif_pos hxk]
    refine zsmul_mem ?_ _
    have he : q ⊗ₜ[ℤ] Stacks.Chow.pointCycle (Stacks.Chow.fieldChowSituation ℂ)
        (X ↘ Spec (.of ℂ)) k x hxk =
        q • Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x
          hxk := by
      rw [Chow.rationalPointCycle, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hxk⟩, rfl⟩)
  | add a b ha hb => exact add_mem ha hb

/-- The basis of the rational `k`-cycles of a complex scheme given by the prime cycles `[x]` of
the points of delta-dimension `k`. -/
private noncomputable def rationalPointBasis (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (k : ℕ) :
    Module.Basis {x : X // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k} ℚ
      (RatCycles X k) :=
  Module.Basis.mk (linearIndependent_rationalPointCycle (X := X) k)
    (span_rationalPointCycle (X := X) k)

private theorem rationalPointBasis_apply {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] {k : ℕ}
    (i : {x : X // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k}) :
    rationalPointBasis X k i =
      Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k i.1 i.2 :=
  Module.Basis.mk_apply _ _ _

/-- The coordinate of a rational cycle at the basis vector `[x]` is its coefficient at `x`. -/
private theorem rationalCoeff_eq_repr {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] {k : ℕ}
    (i : {x : X // Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k})
    (M : RatCycles X k) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k i.1 M =
      (rationalPointBasis X k).repr M i := by
  classical
  rw [← Module.Basis.coord_apply]
  refine LinearMap.congr_fun ((rationalPointBasis X k).ext fun j => ?_) M
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, rationalPointBasis_apply,
    Chow.rationalCoeff_rationalPointCycle, Finsupp.single_apply]
  by_cases hj : j = i
  · subst hj; simp
  · rw [if_neg fun h => hj (Subtype.ext h).symm, if_neg hj]

/-- A rational cycle on a complex scheme is determined by its coefficients. -/
private theorem rationalCycle_ext {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
    {k : ℕ} {L L' : RatCycles X k}
    (h : ∀ x, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x L =
      Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x L') :
    L = L' :=
  (rationalPointBasis X k).ext_elem fun i => by
    rw [← rationalCoeff_eq_repr, ← rationalCoeff_eq_repr, h]

/-- A rational cycle on a complex scheme is the finite sum `∑ L(x) [x]` over its support. -/
private theorem rationalCycle_eq_sum {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] {k : ℕ} (L : RatCycles X k) :
    L = ∑ i ∈ ((rationalPointBasis X k).repr L).support,
      Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k i.1 L •
        Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k i.1
          i.2 := by
  conv_lhs => rw [← (rationalPointBasis X k).linearCombination_repr L]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rationalCoeff_eq_repr, rationalPointBasis_apply]

/-- The coefficient of a rational `k`-cycle at a point not of delta-dimension `k` is zero. -/
private theorem rationalCoeff_eq_zero_of_relativeDimension_ne {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {k : ℕ}
    (L : Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x ≠ k) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x L = 0 := by
  induction L using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, ha, hb, add_zero]
  | tmul q c =>
    rw [Chow.rationalCoeff_tmul]
    have : c.1 x = 0 := by
      by_contra h
      exact hx ((Stacks.Chow.mem_cyclesOfDimension_iff_forall_point
        (Stacks.Chow.fieldChowSituation ℂ) _ k c.1).mp c.2 x h)
    simp [this]

/-- A closed immersion over `ℂ` preserves delta-dimensions. -/
private theorem relativeDimension_map_of_isClosedImmersion {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] (ι : X ⟶ Y) [ι.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion ι] (x : X) :
    Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Y ↘ Spec (.of ℂ)) (ι.base x) =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) x := by
  have hδ := Stacks.Chow.relativeDimension_comp_closedImmersion
    (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction ι (Y ↘ Spec (.of ℂ)) x
  rw [comp_over] at hδ
  exact hδ.symm

/-- The coefficient of a push-forward at a point outside the image is zero. -/
private theorem rationalCoeff_rationalProperPushforward_eq_zero_of_notMem {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsProper f]
    (k : ℕ) (L : Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (y : Y) (hy : y ∉ Set.range f.base) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) k y
      (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ k f (comp_over f _)
        L) = 0 := by
  induction L using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, add_zero]
  | tmul q c =>
    rw [Chow.rationalCoeff_rationalProperPushforward_tmul]
    have hpre : f.base ⁻¹' {y} = ∅ :=
      Set.eq_empty_of_forall_notMem fun x hx => hy ⟨x, hx⟩
    rw [hpre, finsum_mem_empty, Int.cast_zero, mul_zero]

/-- Along a closed immersion `ι`, the coefficient of `ι_* L` at `ι x` is that of `L` at `x`. -/
private theorem rationalCoeff_rationalProperPushforward_of_isClosedImmersion {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (ι : X ⟶ Y) [ι.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion ι] (k : ℕ)
    (L : Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k)
    (x : X) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) k (ι.base x)
        (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ k ι
          (comp_over ι _) L) =
      Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x L := by
  induction L using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
  | tmul q c =>
    rw [Chow.rationalCoeff_rationalProperPushforward_tmul, Chow.rationalCoeff_tmul]
    have hpre : ι.base ⁻¹' {ι.base x} = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ι.isClosedEmbedding.injective.eq_iff
    have hδ := Stacks.Chow.relativeDimension_comp_closedImmersion
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction ι (Y ↘ Spec (.of ℂ)) x
    rw [comp_over] at hδ
    rw [hpre, finsum_mem_singleton, if_pos hδ,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion ι x]
    simp

/-- Push-forward of rational cycles along a closed immersion is injective. -/
private theorem rationalProperPushforward_injective_of_isClosedImmersion {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] (ι : X ⟶ Y) [ι.IsOver (Spec (.of ℂ))]
    [IsClosedImmersion ι] (k : ℕ) :
    Function.Injective (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _
      (Y ↘ Spec (.of ℂ)) k ι (comp_over ι _)) := fun L L' h =>
  rationalCycle_ext fun x => by
    rw [← rationalCoeff_rationalProperPushforward_of_isClosedImmersion ι k L x, h,
      rationalCoeff_rationalProperPushforward_of_isClosedImmersion]

/-- **Proper push-forward of a rational prime cycle** (Stacks 02R4): `f_*[x] = deg(x/f x) [f x]`
when `f x` has the delta-dimension `k` of `x`, and `0` otherwise. -/
private theorem rationalProperPushforward_rationalPointCycle {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y]
    (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsProper f] {k : ℕ} (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = k) :
    Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ k f (comp_over f _)
        (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx) =
      if hd : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
          (Y ↘ Spec (.of ℂ)) (f.base x) = k then
        (f.residueDegree x : ℚ) •
          Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) k
            (f.base x) hd
      else 0 := by
  rw [Chow.rationalPointCycle, Chow.rationalProperPushforward_tmul,
    Chow.properPushforward_pointCycle_eq]
  split_ifs with hd
  · rw [TensorProduct.tmul_smul, Chow.rationalPointCycle, ← Int.cast_smul_eq_zsmul ℚ,
      Int.cast_natCast]
  · rw [TensorProduct.tmul_zero]

/-- Prime cycles of equal points agree. -/
private theorem rationalPointCycle_congr {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {k : ℤ} {x y : X} (h : x = y)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = k)
    (hy : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) y = k) :
    Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx =
      Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k y hy := by
  subst h; rfl

/-- The surface cycle of a prime divisor whose generic point `x` has delta-dimension two is the
prime cycle `[x]`. -/
private theorem primeDivisorCycle_eq_rationalPointCycle {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (P : Mori.PrimeDivisor X) {x : X} (hPx : P.genericPoint = x)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = ((2 : ℕ) : ℤ)) :
    Chow.primeDivisorCycle X P =
      Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ)
        x hx := by
  subst hPx
  unfold Chow.primeDivisorCycle
  exact dif_pos hx

/-- The surface cycle of a prime divisor whose generic point is not of delta-dimension two is
zero. -/
private theorem primeDivisorCycle_eq_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (P : Mori.PrimeDivisor X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) P.genericPoint ≠ 2) :
    Chow.primeDivisorCycle X P = 0 := by
  unfold Chow.primeDivisorCycle
  exact dif_neg hx

open Classical in
/-- The coefficient of the surface cycle of a prime divisor `P` at a point `x` of
delta-dimension two is one if `x` is the generic point of `P`, and zero otherwise. -/
private theorem rationalCoeff_primeDivisorCycle {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (P : Mori.PrimeDivisor X) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = 2) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) x
        (Chow.primeDivisorCycle X P) = if P.genericPoint = x then 1 else 0 := by
  by_cases h : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) P.genericPoint = 2
  · rw [primeDivisorCycle_eq_rationalPointCycle P rfl h, Chow.rationalCoeff_rationalPointCycle]
    by_cases hP : P.genericPoint = x
    · rw [if_pos hP.symm, if_pos hP]
    · rw [if_neg (Ne.symm hP), if_neg hP]
  · rw [primeDivisorCycle_eq_zero P h, map_zero, if_neg]
    rintro rfl
    exact h hx

/-- The coefficient of the surface cycle of a `ℚ`-divisor `D` at a point `x` of delta-dimension
two and coheight one is the coefficient of `D` at the prime divisor with generic point `x`. -/
private theorem rationalCoeff_divisorCycle {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (D : QDivisor X) (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = 2) (hc : Order.coheight x = 1) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) x
        (Chow.divisorCycle X D) = D (AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hc) := by
  classical
  set P₀ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hc
  have hP : ∀ P : Mori.PrimeDivisor X, P.genericPoint = x ↔ P = P₀ := fun P =>
    ⟨fun h => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (h.trans (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hc).symm),
      fun h => h ▸ AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hc⟩
  rw [Chow.divisorCycle, Finsupp.linearCombination_apply, map_finsuppSum]
  simp only [map_smul, rationalCoeff_primeDivisorCycle _ x hx, hP, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  rw [Finsupp.sum, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

/-- **The push-forward of `Zᵢ(a)` to the ambient scheme, coefficientwise.** If every surface
point of the component `E` has coheight one in `E`, the coefficient of `ι_* Z_E(a)` at a point `w`
of `Z` of delta-dimension two is the sum of `a_σ` over the double surfaces `σ` of `E` with surface
`closure {w}`. -/
private theorem rationalCoeff_rationalProperPushforward_divisorCycle {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] {F : Divisor Z} (a : DoubleSurface F → ℚ)
    (E : Mori.PrimeDivisor Z)
    (hE : ∀ v : E.idealSheaf.subscheme, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) v = 2 → Order.coheight v = 1)
    (w : Z) (hw : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w = 2) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) w
        (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((2 : ℕ) : ℤ)
          E.idealSheaf.subschemeι (comp_over _ _)
          (Chow.divisorCycle _ (surfaceCoefficientDivisor a E))) =
      ∑ᶠ σ : {σ : DoubleSurface F // σ.fst = E ∧ σ.carrier = closure {w}}, a σ := by
  classical
  have : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
  by_cases hW : w ∈ Set.range E.idealSheaf.subschemeι.base
  · obtain ⟨v, rfl⟩ := hW
    have hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) v = 2 := by
      have hδ := Stacks.Chow.relativeDimension_comp_closedImmersion
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction E.idealSheaf.subschemeι
        (Z ↘ Spec (.of ℂ)) v
      rw [comp_over] at hδ
      rw [hδ, hw]
    rw [rationalCoeff_rationalProperPushforward_of_isClosedImmersion,
      rationalCoeff_divisorCycle _ v hv (hE v hv)]
    change (surfaceCoefficientDivisor a E).coeff _ = _
    have hgen : Mori.PrimeDivisor.genericPoint
        (AlgebraicGeometry.PrimeDivisor.ofCoheightOne v (hE v hv)) = v :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    rw [coeff_surfaceCoefficientDivisor, surfaceCoefficientCoeff, hgen]
  · rw [rationalCoeff_rationalProperPushforward_eq_zero_of_notMem _ _ _ _ hW]
    haveI : IsEmpty {σ : DoubleSurface F // σ.fst = E ∧ σ.carrier = closure {w}} :=
      ⟨fun σ => hW (by
        rw [Scheme.IdealSheafData.range_subschemeι]
        have hx' : w ∈ σ.1.carrier := by rw [σ.2.2]; exact subset_closure rfl
        have h1 := (σ.1.carrier_subset hx').1
        rw [σ.2.1] at h1
        exact h1)⟩
    exact (finsum_of_isEmpty _).symm

/-- For an oriented system, the double surfaces with a given surface `S`, summed over all
components, cancel in pairs `σ`, `σ.swap`. -/
private theorem sum_finsum_doubleSurface_eq_zero {Z : Scheme.{0}} (F : Divisor Z)
    (a : DoubleSurface F → ℚ) (ha : a ∈ orientedSurfaceCoefficients F) (S : Set Z) :
    ∑ E : F.support, ∑ᶠ σ : {σ : DoubleSurface F // σ.fst = E.1 ∧ σ.carrier = S}, a σ = 0 := by
  classical
  set g : DoubleSurface F → ℚ := fun σ => if σ.carrier = S then a σ else 0 with hg
  have hT : Finite {σ : DoubleSurface F // σ.carrier = S} :=
    Finite.of_injective (β := F.support × F.support)
      (fun σ => (⟨σ.1.fst, σ.1.fst_mem⟩, ⟨σ.1.snd, σ.1.snd_mem⟩)) fun σ τ h => by
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
        exact Subtype.ext (DoubleSurface.ext h.1 h.2 (σ.2.trans τ.2.symm))
  have hgfin : (Function.support g).Finite := by
    refine (Set.finite_range (Subtype.val : {σ : DoubleSurface F // σ.carrier = S} → _)).subset ?_
    intro σ hσ
    by_cases h : σ.carrier = S
    · exact ⟨⟨σ, h⟩, rfl⟩
    · exact absurd (by simp [hg, h]) hσ
  have h1 : ∀ E : F.support,
      ∑ᶠ σ : {σ : DoubleSurface F // σ.fst = E.1 ∧ σ.carrier = S}, a σ =
        ∑ᶠ σ, if σ.fst = E.1 then g σ else 0 := by
    intro E
    rw [finsum_subtype_eq_finsum_cond]
    refine finsum_congr fun σ => ?_
    rw [finsum_eq_if]
    by_cases h1 : σ.fst = E.1 <;> by_cases h2 : σ.carrier = S <;> simp [hg, h1, h2]
  simp_rw [h1]
  rw [← finsum_sum_comm _ _ fun E _ => hgfin.subset fun σ hσ => by
    by_contra h
    exact hσ (by simp [Function.notMem_support.1 h])]
  have h2 : ∀ σ : DoubleSurface F, (∑ E : F.support, if σ.fst = E.1 then g σ else 0) = g σ := by
    intro σ
    rw [Finset.sum_eq_single ⟨σ.fst, σ.fst_mem⟩ (fun E _ hE => if_neg fun h => hE
      (Subtype.ext h.symm)) (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]
  simp_rw [h2]
  have hswap : ∀ σ : DoubleSurface F, g σ.swap = -g σ := by
    intro σ
    by_cases h : σ.carrier = S <;> simp [hg, h, ha σ]
  have e := finsum_comp_equiv (Function.Involutive.toPerm DoubleSurface.swap
    DoubleSurface.swap_swap) (f := g)
  change ∑ᶠ i : DoubleSurface F, g i.swap = _ at e
  simp only [hswap, finsum_neg_distrib] at e
  linarith

end Homology

section Centre

open MMP.Resolution

variable {X : Scheme.{0}} [IsLocallyNoetherian X]

/-- Off the components of codimension at least two, a centre having simple normal crossings with
some family is locally principal, generated by a member of a regular system of parameters (when
it vanishes nowhere identically). -/
private theorem exists_stalk_eq_span_singleton [NoetherianSpace X] {Λ : Type*}
    {E : Λ → X.IdealSheafData} {I : X.IdealSheafData} (hI : HasSNCWith E I)
    (hne : ∀ x, IdealSheafData.stalk I x ≠ ⊥) {x : X} (hx : x ∈ (I.support : Set X))
    (hx2 : x ∉ componentsOfCodimAtLeastTwo (I.support : Set X)) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (j : Fin n),
      IsRegularSystemOfParameters z ∧ IdealSheafData.stalk I x = Ideal.span {z j} := by
  classical
  obtain ⟨n, z, -, J, hz, -, -, hJ⟩ := hI x hx
  have hJc : IdealSheafData.stalk I x = (coordPrime hz J).asIdeal := hJ
  rcases J.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact absurd (by rw [hJ]; simp) (hne x)
  by_cases hsub : ∃ b ∈ J, b ≠ a
  · obtain ⟨b, hb, hba⟩ := hsub
    exfalso
    apply hx2
    have hmem := closure_coordPrime_mem_componentsOf hz hJc hx
    have h2 := two_le_codimension_closure_coordPrime hz ha hb hba.symm
      isIrreducible_singleton.closure
    exact Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨hmem, Set.mem_iUnion.2 ⟨h2,
      specializes_iff_mem_closure.1 (fromSpecStalk_specializes_self x _)⟩⟩⟩
  · push Not at hsub
    have : J = {a} := Finset.eq_singleton_iff_unique_mem.2 ⟨ha, hsub⟩
    refine ⟨n, z, a, hz, ?_⟩
    rw [hJ, this, Finset.coe_singleton, Set.image_singleton]

/-- The open complement of the components of codimension at least two of the centre. -/
private def complCodimTwo [NoetherianSpace X] (I : X.IdealSheafData) : X.Opens :=
  ⟨(componentsOfCodimAtLeastTwo (I.support : Set X))ᶜ,
    (isClosed_componentsOfCodimAtLeastTwo I.support.isClosed).isOpen_compl⟩

/-- **The blow-up is an isomorphism off the components of codimension at least two** of a
centre having simple normal crossings with some family: there the centre is an effective
Cartier divisor. -/
private theorem isIso_blowUpToBase_restrict_complCodimTwo [NoetherianSpace X] {Λ : Type*}
    {E : Λ → X.IdealSheafData} {I : X.IdealSheafData} (hI : HasSNCWith E I)
    (hne : ∀ x, IdealSheafData.stalk I x ≠ ⊥) :
    IsIso (blowUpToBase I ∣_ complCodimTwo I) := by
  set U := complCodimTwo I
  have hC : Stacks.Divisors.IsEffectiveCartierDivisor (I.comap U.ι) := by
    apply isEffectiveCartierDivisor_of_stalk_eq_span_parameter
    intro y hy
    have hy' : U.ι y ∈ (I.support : Set X) := by
      rw [Scheme.IdealSheafData.support_comap] at hy
      exact hy
    obtain ⟨n, z, j, hz, hs⟩ := exists_stalk_eq_span_singleton hI hne hy' y.2
    let e := (asIso (U.ι.stalkMap y)).commRingCatIsoToRingEquiv
    refine ⟨n, fun i => e (z i), j, hz.map_ringEquiv e, ?_⟩
    rw [MMP.Threefold.Mori.OpenRestriction.stalk_comap_eq_map, hs, Ideal.map_span, Set.image_singleton]
    rfl
  have := Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor _ hC
  have hpb := Kollar.isPullback_canonicalLift_of_flat U.ι I
  have hpb2 := isPullback_morphismRestrict (blowUpToBase I) U
  have h := hpb.isoIsPullback_hom_fst _ _ hpb2
  rw [(Iso.eq_inv_comp _).2 h]
  infer_instance

end Centre

section Connecting

open CategoryTheory.Limits borelMooreHomology

variable {R : Type} [CommRing R] (M : ModuleCat.{0} R)

/-- The restriction `q⁻¹ X → X` of a continuous map. -/
private def closedRestrict {Y' Y : TopCat.{0}} (q : Y' ⟶ Y) (X : Set Y) :
    TopCat.of (q ⁻¹' X : Set Y') ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun x => ⟨q x.1, x.2⟩, (q.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem isProperMap_closedRestrict {Y' Y : TopCat.{0}} (q : Y' ⟶ Y) (hq : IsProperMap q)
    (X : Set Y) : IsProperMap (closedRestrict q X) :=
  hq.restrictPreimage X

/-- The restriction `Y' - q⁻¹ X → Y - X` of a continuous map. -/
private def openRestrict {Y' Y : TopCat.{0}} (q : Y' ⟶ Y) {X : Set Y} (hX : IsClosed X) :
    TopCat.of (complOpens (hX.preimage q.hom.continuous)) ⟶ TopCat.of (complOpens hX) :=
  TopCat.ofHom ⟨fun x => ⟨q x.1, x.2⟩, (q.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem isProperMap_openRestrict {Y' Y : TopCat.{0}} (q : Y' ⟶ Y) (hq : IsProperMap q)
    {X : Set Y} (hX : IsClosed X) : IsProperMap (openRestrict q hX) :=
  isProperMap_restrictPreimage q (complOpens hX) hq

/-- **Naturality of the Borel–Moore connecting map** under proper push-forward. -/
private theorem connecting_comp_pushforward {Y' Y : TopCat.{0}} [T2Space Y'] [T2Space Y] (q : Y' ⟶ Y)
    (hq : IsProperMap q) {X : Set Y} (hX : IsClosed X) (h : IsRelativeQuasiIso R M hX)
    (h' : IsRelativeQuasiIso R M (hX.preimage q.hom.continuous)) (k : ℤ) :
    connecting R M _ h' k ≫
        pushforward R M (closedRestrict q X) (isProperMap_closedRestrict q hq X) k =
      pushforward R M (openRestrict q hX) (isProperMap_openRestrict q hq hX) (k + 1) ≫
        connecting R M hX h k := by
  have hX' : IsClosed (q ⁻¹' X) := hX.preimage q.hom.continuous
  set f' := extIncl R M hX'
  set f := extIncl R M hX
  set g' := extRestrict R M hX'
  set g := extRestrict R M hX
  set t₁ := HomologicalComplex.extendMap
    (chainMap R M (closedRestrict q X) (isProperMap_closedRestrict q hq X))
    ComplexShape.embeddingDownNat
  set t₂ := HomologicalComplex.extendMap (chainMap R M q hq) ComplexShape.embeddingDownNat
  set tU := HomologicalComplex.extendMap
    (chainMap R M (openRestrict q hX) (isProperMap_openRestrict q hq hX))
    ComplexShape.embeddingDownNat
  have c₁ : f' ≫ t₂ = t₁ ≫ f := by
    simp only [f', f, t₁, t₂, extIncl, ← HomologicalComplex.extendMap_comp, ← chainMap_comp]
    congr 1
  have e' : chainMap R M q hq ≫ restrictChainMap R M (complOpens hX) =
      restrictChainMap R M (complOpens hX') ≫
        chainMap R M (openRestrict q hX) (isProperMap_openRestrict q hq hX) :=
    chainMap_comp_restrictChainMap R M q hq (complOpens hX)
  have c₂ : t₂ ≫ g = g' ≫ tU := by
    simp only [g', g, t₂, tU, extRestrict, ← HomologicalComplex.extendMap_comp, e']
  let t₃ : cokernel f' ⟶ cokernel f := cokernel.desc f' (t₂ ≫ cokernel.π f) (by
    rw [← Category.assoc, c₁, Category.assoc, cokernel.condition, Limits.comp_zero])
  let Φ : ShortComplex.mk f' (cokernel.π f') (cokernel.condition f') ⟶
      ShortComplex.mk f (cokernel.π f) (cokernel.condition f) :=
    { τ₁ := t₁, τ₂ := t₂, τ₃ := t₃, comm₁₂ := c₁.symm, comm₂₃ := (cokernel.π_desc _ _ _).symm }
  have hδ := HomologicalComplex.HomologySequence.δ_naturality Φ
    (MMP.ModuleCatComplex.shortExact_cokernel f') (MMP.ModuleCatComplex.shortExact_cokernel f)
    (-(k + 1)) (-k) (rel_neg_succ_neg k)
  set φ' := cokernel.desc f' g' (extIncl_comp_extRestrict R M hX')
  set φ := cokernel.desc f g (extIncl_comp_extRestrict R M hX)
  haveI : QuasiIso φ' := h'
  haveI : QuasiIso φ := h
  have c₃ : t₃ ≫ φ = φ' ≫ tU := by
    refine (cancel_epi (cokernel.π f')).1 ?_
    rw [← Category.assoc, cokernel.π_desc, Category.assoc, cokernel.π_desc, c₂,
      ← Category.assoc, cokernel.π_desc]
  have c₄ : inv (HomologicalComplex.homologyMap φ' (-(k + 1))) ≫
      HomologicalComplex.homologyMap t₃ (-(k + 1)) =
      HomologicalComplex.homologyMap tU (-(k + 1)) ≫
        inv (HomologicalComplex.homologyMap φ (-(k + 1))) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← HomologicalComplex.homologyMap_comp, ← c₃, HomologicalComplex.homologyMap_comp,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  change (inv (HomologicalComplex.homologyMap φ' (-(k + 1))) ≫ _) ≫
      HomologicalComplex.homologyMap t₁ (-k) =
    HomologicalComplex.homologyMap tU (-(k + 1)) ≫
      (inv (HomologicalComplex.homologyMap φ (-(k + 1))) ≫ _)
  rw [Category.assoc]
  erw [hδ]
  rw [← Category.assoc, c₄, Category.assoc]

/-- **The ladder with naturality.** Let `q : Y' → Y` be proper, `X ⊆ Y` closed with
`X' = q⁻¹ X`, both with their relative quasi-isomorphisms, `q_*` surjective on `H_{k+1}` and
`q : Y' - X' → Y - X` bijective on `H_{k+1}`. A class `u ∈ H_k(X')` vanishing in `H_k(Y')` and in
`H_k(X)` vanishes. -/
private theorem eq_zero_of_pushforward_eq_zero_of_ladder {Y' Y : TopCat.{0}} [T2Space Y'] [T2Space Y]
    (q : Y' ⟶ Y) (hq : IsProperMap q) {X : Set Y} (hX : IsClosed X) (h : IsRelativeQuasiIso R M hX)
    (h' : IsRelativeQuasiIso R M (hX.preimage q.hom.continuous)) (k : ℕ)
    (hsurj : Function.Surjective (pushforward R M q hq ((k : ℤ) + 1)).hom)
    (hbij : Function.Bijective
      (pushforward R M (openRestrict q hX) (isProperMap_openRestrict q hq hX) ((k : ℤ) + 1)).hom)
    (u : borelMooreHomology R M (TopCat.of (q ⁻¹' X : Set Y')) k)
    (hu₁ : (pushforward R M (subspaceInclusion Y' (q ⁻¹' X))
      (isProperMap_subspaceInclusion (hX.preimage q.hom.continuous)) k).hom u = 0)
    (hu₂ : (pushforward R M (closedRestrict q X) (isProperMap_closedRestrict q hq X) k).hom u = 0) :
    u = 0 := by
  have hX' : IsClosed (q ⁻¹' X) := hX.preimage q.hom.continuous
  obtain ⟨x, rfl⟩ := (exact_connecting_pushforward h' k u).1 hu₁
  have hnat := congrArg (fun φ => φ.hom x) (connecting_comp_pushforward M q hq hX h h' k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hu₂] at hnat
  obtain ⟨z, hz⟩ := (exact_restrict_connecting h k _).1 hnat.symm
  obtain ⟨z', rfl⟩ := hsurj z
  rw [restrict_pushforward_apply] at hz
  have hx : (restrict R M (complOpens hX') ((k : ℤ) + 1)).hom z' = x := hbij.1 hz
  rw [← hx]
  exact (exact_restrict_connecting h' k _).2 ⟨z', rfl⟩

end Connecting

section JStepLadder

open MMP.borelMooreHomology

section Ladder

variable {R : Type} [CommRing R] (M : ModuleCat.{0} R)

/-- A class of `Y` whose restriction to `U` comes from `U' = q⁻¹ U` comes from `Y'`, when the
restriction to `U` is injective and every class of `U'` extends to `Y'`. -/
private theorem exists_pushforward_eq_of_ladder {Y Y' : TopCat.{0}} [T2Space Y] [T2Space Y']
    (q : Y' ⟶ Y) (hq : IsProperMap q) (U : Opens Y) (U' : Opens Y')
    (hU' : U' = Opens.comap q.hom U) (m : ℤ)
    (hres : Function.Injective (restrict R M U m).hom)
    (hext : Function.Surjective (restrict R M U' m).hom)
    (hφ : Function.Surjective (pushforward R M (restrictPreimage q U)
      (isProperMap_restrictPreimage q U hq) m).hom)
    (μ : borelMooreHomology R M Y m) :
    ∃ μ', (pushforward R M q hq m).hom μ' = μ := by
  subst hU'
  obtain ⟨x, hx⟩ := hφ ((restrict R M U m).hom μ)
  obtain ⟨μ', rfl⟩ := hext x
  refine ⟨μ', hres ?_⟩
  rw [restrict_pushforward_apply, hx]

end Ladder

section Dimension

/-- If every irreducible closed subset of the closed set `S` has codimension at least `c` in a
space of dimension at most `n`, then `S` has dimension at most `n - c`. -/
private lemma topologicalKrullDim_le_sub_of_le_codimension {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsClosed S) {c n : ℕ} (hX : topologicalKrullDim X ≤ n)
    (hc : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ S → (c : ℕ∞) ≤ codimension W) :
    topologicalKrullDim S ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
  let e : IrreducibleCloseds S → IrreducibleCloseds X := fun W ↦
    ⟨(↑) '' (W : Set S), W.2.image _ continuous_subtype_val.continuousOn,
      hS.isClosedMap_subtype_val _ W.3⟩
  have he : StrictMono e := by
    intro a b hab
    have hab' : (a : Set S) ⊂ b := hab
    change Subtype.val '' (a : Set S) ⊂ Subtype.val '' (b : Set S)
    exact ⟨Set.image_mono hab'.1, fun h ↦ hab'.2 ((Set.image_subset_image_iff
      Subtype.val_injective).1 h)⟩
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun W ↦ ?_
  have h1 : Order.height W ≤ Order.height (e W) :=
    Order.height_le_height_apply_of_strictMono _ he _
  have h2 : (c : ℕ∞) ≤ Order.coheight (e W) := by
    rw [← codimension_eq_coheight]
    exact hc _ (by rintro _ ⟨x, -, rfl⟩; exact x.2)
  have h3 : ((Order.height (e W) + Order.coheight (e W) : ℕ∞) : WithBot ℕ∞) ≤ n := by
    haveI : Nonempty (IrreducibleCloseds X) := ⟨e W⟩
    refine le_trans ?_ hX
    rw [topologicalKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_le_coe.2 (le_iSup (fun a ↦ Order.height a + Order.coheight a) (e W))
  have h4 : Order.height W + c ≤ n := (add_le_add h1 h2).trans (WithBot.coe_le_coe.1 h3)
  have hne : Order.height W ≠ ⊤ := fun h ↦ by
    rw [h, top_add] at h4
    exact absurd h4 (by simp)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
  rw [← hm] at h4 ⊢
  have h6 : m + c ≤ n := by exact_mod_cast h4
  exact WithBot.coe_le_coe.2 (Nat.cast_le.2 (show m ≤ n - c by omega))

/-- A closed subscheme of a scheme of dimension at most `n`, all of whose irreducible closed
subsets have codimension at least `c`, has dimension at most `n - c`. -/
private lemma dimension_subscheme_le {X : Scheme.{0}} (I : X.IdealSheafData) {c n : ℕ}
    (hX : topologicalKrullDim X ≤ n)
    (hc : ∀ W : IrreducibleCloseds X, (W : Set X) ⊆ I.support → (c : ℕ∞) ≤ codimension W) :
    topologicalKrullDim I.subscheme ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
  have hmem : ∀ z, I.subschemeι z ∈ (I.support : Set X) := fun z ↦ by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self z
  exact ((I.subschemeι.isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le).trans
    (topologicalKrullDim_le_sub_of_le_codimension I.support.isClosed hX hc)

end Dimension

section Points

open UnderlyingSpace

/-- Push-forward along a proper continuous bijection is bijective. -/
private lemma bijective_pushforward_of_bijective {R : Type} [CommRing R] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : IsProperMap f) (hb : Function.Bijective f) (j : ℤ) :
    Function.Bijective (pushforward R (ModuleCat.of R R) f hf j).hom :=
  bijective_pushforward_homeomorph R
    ((Equiv.ofBijective f hb).toHomeomorphOfContinuousClosed f.hom.continuous
      hf.isClosedMap) j

/-- If `f ∣_ W` is an isomorphism, `f` is bijective on `ℂ`-points over `W`. -/
private lemma bijective_restrictPreimage_map_of_isIso {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
    (W : Y.Opens) [IsIso (f ∣_ W)] (U : Opens (TopCat.of (UnderlyingSpace ℂ Y)))
    (hU : ∀ p : UnderlyingSpace ℂ Y, p ∈ U ↔ p.toHom (IsLocalRing.closedPoint ℂ) ∈ W) :
    Function.Bijective (restrictPreimage (TopCat.ofHom (map (K := ℂ) f)) U) := by
  have hpt : ∀ x : Spec (.of ℂ), x = IsLocalRing.closedPoint ℂ := fun x ↦ Subsingleton.elim _ _
  have hX : ∀ a : Opens.comap (TopCat.ofHom (map (K := ℂ) f)).hom U,
      Set.range a.1.toHom ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rintro a _ ⟨x, rfl⟩
    rw [hpt x, Scheme.Opens.range_ι]
    exact (hU _).1 a.2
  refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
  · have hab' : a.1.toHom ≫ f = b.1.toHom ≫ f :=
      congrArg UnderlyingSpace.toHom (congrArg Subtype.val hab)
    have key : IsOpenImmersion.lift (f ⁻¹ᵁ W).ι a.1.toHom (hX a) =
        IsOpenImmersion.lift (f ⁻¹ᵁ W).ι b.1.toHom (hX b) := by
      rw [← cancel_mono (f ∣_ W), ← cancel_mono W.ι, Category.assoc, Category.assoc,
        morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, hab']
    apply Subtype.ext
    apply UnderlyingSpace.ext
    rw [← IsOpenImmersion.lift_fac (f ⁻¹ᵁ W).ι a.1.toHom (hX a),
      ← IsOpenImmersion.lift_fac (f ⁻¹ᵁ W).ι b.1.toHom (hX b), key]
  · have hb : Set.range b.1.toHom ⊆ Set.range W.ι := by
      rintro _ ⟨x, rfl⟩
      rw [hpt x, Scheme.Opens.range_ι]
      exact (hU _).1 b.2
    set x := IsOpenImmersion.lift W.ι b.1.toHom hb ≫ inv (f ∣_ W) ≫ (f ⁻¹ᵁ W).ι with hxdef
    have hxf : x ≫ f = b.1.toHom := by
      rw [hxdef, Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
        IsOpenImmersion.lift_fac]
    have hxo : x ≫ X ↘ Spec (.of ℂ) = 𝟙 _ := by
      rw [← comp_over f (Spec (.of ℂ)), ← Category.assoc, hxf, b.1.toHom_comp_over]
    let x' : UnderlyingSpace ℂ X := ⟨x, hxo⟩
    have hx' : map (K := ℂ) f x' = b.1 := UnderlyingSpace.ext hxf
    refine ⟨⟨x', ?_⟩, Subtype.ext hx'⟩
    change map (K := ℂ) f x' ∈ U
    rw [hx']
    exact b.2

end Points

section Duality

open BorelMooreCap BorelMooreCross

/-- If capping with `μ` maps `H^{n-k}(Y)` onto `H_k(Y)` and `μ = q_* μ'`, then
`q_* : H_k(Y') → H_k(Y)` is onto, by the projection formula. -/
private lemma surjective_pushforward_of_surjective_dualityMap {R : Type} [CommRing R]
    {Y' Y : TopCat.{0}} [T2Space Y] [T2Space Y'] (q : Y' ⟶ Y) (hq : IsProperMap q) {n : ℕ}
    (μ : borelMooreHomology R (ModuleCat.of R R) Y n)
    (μ' : borelMooreHomology R (ModuleCat.of R R) Y' n)
    (hμ : (pushforward R (ModuleCat.of R R) q hq n).hom μ' = μ)
    {A : Set Y} (hA : IsClosed A) (hAu : A = Set.univ) (hAd : HasProperNeighbourhoodDeformations A)
    (hA'd : HasProperNeighbourhoodDeformations (q ⁻¹' A)) (k : ℤ)
    (hdual : Function.Surjective (dualityMap R hA hAd μ k)) :
    Function.Surjective (pushforward R (ModuleCat.of R R) q hq k).hom := by
  subst hAu
  intro z
  have hb := bijective_pushforward_of_bijective (R := R) (subsetInclusion (Set.univ : Set Y))
    (isProperMap_subsetInclusion hA)
    ⟨Subtype.val_injective, fun y ↦ ⟨⟨y, trivial⟩, rfl⟩⟩ k
  obtain ⟨w, rfl⟩ := hb.2 z
  obtain ⟨c, rfl⟩ := hdual w
  refine ⟨congrDegree R Y' (by omega : (n : ℤ) - (n - k) = k)
    (capProduct R Y' (q ⁻¹' Set.univ) (n - k) n
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) q Set.univ (n - k)).hom c) μ'), ?_⟩
  rw [pushforward_congrDegree, pushforward_capProduct_pullback R q hq hA hAd hA'd, hμ,
    dualityMap_apply, pushforward_congrDegree, pushforward_subsetInclusion_capProductSupport]

end Duality

section Main

/-- A smooth complex variety of dimension `n` is smooth of relative dimension `n`: on a standard
smooth affine chart `V` of relative dimension `d`, `d = dim V = dim W`. -/
private theorem smoothOfRelativeDimension_of_isSmoothScheme {W : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W]
    (hv : AlgebraicGeometry.IsVariety ℂ (W ↘ Spec (.of ℂ)))
    (hsm : MMP.Mori.IsSmoothScheme (W ↘ Spec (.of ℂ))) (n : ℕ) (hdim : topologicalKrullDim W = n) :
    SmoothOfRelativeDimension n (W ↘ Spec (.of ℂ)) := by
  haveI : IsIntegral W := hv.toIsIntegral
  haveI : Smooth (W ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hst⟩ := Smooth.exists_isStandardSmooth (W ↘ Spec (.of ℂ)) x
  letI := ((W ↘ Spec (.of ℂ)).appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hst.out
  have hr : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
      ((W ↘ Spec (.of ℂ)).appLE U V e).hom := ⟨ι, σ, inferInstance, inferInstance, P, rfl⟩
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  suffices hr3 : P.dimension = n by rw [← hr3]; exact hr
  -- the open `V` as a scheme, smooth of relative dimension `P.dimension`
  haveI : IsAffine V.toScheme := hV
  haveI : SmoothOfRelativeDimension P.dimension (V.ι ≫ W ↘ Spec (.of ℂ)) := by
    constructor
    intro y
    have e' : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ W ↘ Spec (.of ℂ)) ⁻¹ᵁ U := by
      intro z _
      exact e z.2
    refine ⟨U, hU, ⊤, isAffineOpen_top _, trivial, e', ?_⟩
    have e'' : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun z _ ↦ z.2
    rw [← Scheme.Hom.appLE_comp_appLE V.ι (W ↘ Spec (.of ℂ)) U V ⊤ e e'']
    haveI : IsIso (V.ι.appLE V ⊤ e'') := by
      rw [Scheme.Opens.ι_appLE]
      have h1 : (homOfLE (Set.image_subset_iff.mpr e'') : V.ι ''ᵁ ⊤ ⟶ V) =
          eqToHom V.ι_image_top := Subsingleton.elim _ _
      rw [h1]
      exact (W.presheaf.mapIso (eqToIso V.ι_image_top).op).isIso_hom
    exact ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso
      (n := P.dimension)).cancel_right_isIso
      ((W ↘ Spec (.of ℂ)).appLE U V e) (V.ι.appLE V ⊤ e'')).2 hr
  haveI : Nonempty V.toScheme := ⟨⟨x, hx⟩⟩
  have h1 := AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field
    P.dimension (V.ι ≫ W ↘ Spec (.of ℂ))
  have h2 := AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ W (W ↘ Spec (.of ℂ))
    (V : Set W) V.isOpen ⟨x, hx⟩
  change topologicalKrullDim (V : Set W) = _ at h1
  rw [← h2, hdim] at h1
  exact_mod_cast h1.symm

end Main

section Core

open MMP UnderlyingSpace BorelMooreCap BorelMooreCross

/-- The relative quasi-isomorphism of the points over a closed subset of a complex scheme. -/
private theorem isRelativeQuasiIso_pointsOver (S : Scheme.{0}) [S.Over (Spec (.of ℂ))]
    [IsComplexScheme S] {T : Set S} (hT : IsClosed T)
    {A : Set (TopCat.of (UnderlyingSpace ℂ S))} (hA : IsClosed A) (hAT : A = pointsOver T) :
    IsRelativeQuasiIso ℚ (ModuleCat.of ℚ ℚ) hA := by
  subst hAT
  obtain ⟨hYc, n, F, hF⟩ := hasBasis_contractible_and_exists_isClosedEmbedding S
  exact isRelativeQuasiIso_of_isClosedEmbedding ℚ (ModuleCat.of ℚ ℚ)
    (Y := TopCat.of (UnderlyingSpace ℂ S)) hF hA (hasOpenContractibleBasis_pointsOver S ⟨T, hT⟩)
    hYc

/-- Borel–Moore homology of the points over a closed subset vanishes above twice the dimension
of its reduced structure. -/
private theorem subsingleton_borelMooreHomology_pointsOver (S : Scheme.{0})
    [S.Over (Spec (.of ℂ))] [IsComplexScheme S] {T : Set S} (hT : IsClosed T)
    {A : Set (TopCat.of (UnderlyingSpace ℂ S))} (hAT : A = pointsOver T) {n : ℕ}
    (hdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).subscheme ≤ n) {i : ℤ}
    (hi : 2 * (n : ℤ) < i) :
    Subsingleton (borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of A) i) := by
  set ι := (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).subschemeι
  have : IsComplexScheme (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).subscheme :=
    IsComplexScheme.of_isClosedImmersion ι
  have h0 := IsComplexScheme.isZero_borelMooreHomology_of_dimension_le
    (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).subscheme ℚ hdim hi
  rw [ModuleCat.isZero_iff_subsingleton] at h0
  have hrange : Set.range (map (K := ℂ) ι) = A := by
    rw [range_map_of_isClosedImmersion, hAT, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let e : UnderlyingSpace ℂ (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).subscheme ≃ₜ A :=
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) ι).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  have hb := bijective_pushforward_homeomorph ℚ
    (Y := TopCat.of (UnderlyingSpace ℂ (Scheme.IdealSheafData.vanishingIdeal ⟨T, hT⟩).subscheme))
    (Y' := TopCat.of A) e i
  exact hb.2.subsingleton

/-- **The ladder for a morphism which is an isomorphism off a closed subset.** Let `Z` be a
non-singular projective complex fourfold, `q : Z' ⟶ Z` proper, `K ⊆ Z` closed with `q` an
isomorphism over `Z - K`, the reduced structure on `K` of dimension at most two and that on
`q⁻¹ K` of dimension at most three. A class `u ∈ H_4(q⁻¹ K(ℂ))` vanishing in `H_4(Z')` and in
`H_4(K(ℂ))` vanishes. -/
private theorem eq_zero_of_isIso_restrict_compl {Z Z' : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z]
    [SmoothOfRelativeDimension 4 (Z ↘ Spec (.of ℂ))]
    [AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ))]
    (hZ : AlgebraicGeometry.IsProjective (Z ↘ Spec (.of ℂ))) [Z'.Over (Spec (.of ℂ))]
    [IsComplexScheme Z'] (q : Z' ⟶ Z) [q.IsOver (Spec (.of ℂ))] [IsProper q]
    {K : Set Z} (hK : IsClosed K) [IsIso (q ∣_ ⟨Kᶜ, hK.isOpen_compl⟩)]
    (hdimK : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal ⟨K, hK⟩).subscheme ≤
      ((4 - 2 : ℕ) : WithBot ℕ∞))
    (hdimK' : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      ⟨q ⁻¹' K, hK.preimage q.continuous⟩).subscheme ≤ ((4 - 1 : ℕ) : WithBot ℕ∞))
    (u : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of ((TopCat.ofHom (map (K := ℂ) q)) ⁻¹' pointsOver (K := ℂ) K :
        Set (TopCat.of (UnderlyingSpace ℂ Z')))) 4)
    (hu₁ : (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (subspaceInclusion (TopCat.of (UnderlyingSpace ℂ Z'))
        ((TopCat.ofHom (map (K := ℂ) q)) ⁻¹' pointsOver (K := ℂ) K))
      (isProperMap_subspaceInclusion
        ((isClosed_pointsOver hK).preimage (TopCat.ofHom (map (K := ℂ) q)).hom.continuous))
      4).hom u = 0)
    (hu₂ : (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (closedRestrict (TopCat.ofHom (map (K := ℂ) q)) (pointsOver (K := ℂ) K))
      (isProperMap_closedRestrict _ (isProperMap_map (K := ℂ) q) _) 4).hom u = 0) :
    u = 0 := by
  have hq : IsProperMap (TopCat.ofHom (map (K := ℂ) q)) := isProperMap_map (K := ℂ) q
  have hX : IsClosed (pointsOver (K := ℂ) K : Set (TopCat.of (UnderlyingSpace ℂ Z))) :=
    isClosed_pointsOver hK
  have hX'eq : (TopCat.ofHom (map (K := ℂ) q)) ⁻¹' (pointsOver (K := ℂ) K) = pointsOver (K := ℂ) (q ⁻¹' K) := by
    ext p
    simp only [Set.mem_preimage, mem_pointsOver, TopCat.hom_ofHom, toHom_map]
    rfl
  have h := isRelativeQuasiIso_pointsOver Z hK hX rfl
  have h' := isRelativeQuasiIso_pointsOver Z' (hK.preimage q.continuous)
    (hX.preimage (TopCat.ofHom (map (K := ℂ) q)).hom.continuous) hX'eq
  have hbij : ∀ j, Function.Bijective (pushforward ℚ (ModuleCat.of ℚ ℚ) (openRestrict (TopCat.ofHom (map (K := ℂ) q)) hX)
      (isProperMap_openRestrict (TopCat.ofHom (map (K := ℂ) q)) hq hX) j).hom := by
    intro j
    refine bijective_pushforward_of_bijective _ _ ?_ _
    exact bijective_restrictPreimage_map_of_isIso q ⟨Kᶜ, hK.isOpen_compl⟩ (complOpens hX)
      fun p => Iff.rfl
  -- the fundamental class lifts
  haveI : IsIntegral Z :=
    (inferInstance : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ))).toIsIntegral
  let μ : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Z))
      (2 * 4 : ℕ) :=
    Chow.pointCycleClass ℚ (genericPoint Z)
      (Chow.relativeDimension_genericPoint_eq ℂ (Z ↘ Spec (.of ℂ))
        (natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := ℂ) Z 4).symm)
  have hX8 := subsingleton_borelMooreHomology_pointsOver Z hK rfl hdimK
    (i := ((2 * 4 : ℕ) : ℤ)) (by norm_num)
  have hX'7 := subsingleton_borelMooreHomology_pointsOver Z' (hK.preimage q.continuous) hX'eq
    hdimK' (i := 7) (by norm_num)
  have hμ' : ∃ μ', (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) q)) hq (2 * 4 : ℕ)).hom μ' = μ := by
    refine exists_pushforward_eq_of_ladder (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) q)) hq (complOpens hX)
      (complOpens (hX.preimage (TopCat.ofHom (map (K := ℂ) q)).hom.continuous)) rfl _ ?_ ?_ ?_ μ
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨a, rfl⟩ := (exact_pushforward_restrict h _ x).1 hx
      rw [Subsingleton.elim a 0, map_zero]
    · intro x
      exact (exact_restrict_connecting h' 7 x).1 (Subsingleton.elim _ _)
    · exact (hbij _).2
  obtain ⟨μ', hμ'⟩ := hμ'
  have hsurj : Function.Surjective (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) q)) hq (4 + 1)).hom := by
    have hqp : IsQuasiProjectiveVariety ℂ (Z ↘ Spec (.of ℂ)) :=
      (isQuasiProjectiveVariety_iff_isQuasiProjective ℂ _).2 (isQuasiProjective_of_isProjective hZ)
    have : IsProper (Z ↘ Spec (.of ℂ)) := hZ.isProper
    have hD : IsProper ((Scheme.IdealSheafData.vanishingIdeal ⊤).subschemeι ≫
        (Z ↘ Spec (.of ℂ))) := inferInstance
    have hdual := (MMP.Analytic.bijective_dualityMap_of_isQuasiProjectiveVariety hqp
      (μ := μ) rfl ⊤ hD (4 + 1)).1
    have hpre : map (K := ℂ) q ⁻¹' pointsOver ((⊤ : Closeds Z) : Set Z) =
        pointsOver ((⊤ : Closeds Z') : Set Z') := by
      ext p; simp [mem_pointsOver]
    exact surjective_pushforward_of_surjective_dualityMap _ _ μ μ' hμ'
      (isClosed_pointsOver (⊤ : Closeds Z).isClosed) (by ext p; simp [mem_pointsOver]) _
      (hpre ▸ hasProperNeighbourhoodDeformations_pointsOver Z' ⊤) _ hdual.2
  exact eq_zero_of_pushforward_eq_zero_of_ladder (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) q)) hq hX h h' 4 hsurj
    (hbij _) u hu₁ hu₂

end Core

end JStepLadder

section Divisor

/-- On an integral scheme, a nonzero ideal sheaf has nonzero stalks. -/
private theorem stalk_ne_bot_of_ne_bot {X : Scheme.{0}} [IsIntegral X] {I : X.IdealSheafData}
    (hI : I ≠ ⊥) (x : X) : IdealSheafData.stalk I x ≠ ⊥ := by
  intro hx
  apply hI
  ext U : 2
  change I.ideal U = ⊥
  have hη : IdealSheafData.stalk I (genericPoint X) = ⊥ := by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
    lift V to X.affineOpens using hV
    have hyV : genericPoint X ∈ V.1 := (genericPoint_specializes x).mem_open V.1.isOpen hxV
    rw [IdealSheafData.stalk_eq_map_germ I x V hxV] at hx
    rw [IdealSheafData.stalk_eq_map_germ I _ V hyV,
      ← X.presheaf.germ_stalkSpecializes hxV (genericPoint_specializes x), CommRingCat.hom_comp,
      ← Ideal.map_map, hx, Ideal.map_bot]
  by_cases hU : genericPoint X ∈ U.1
  swap
  · have hU' : U.1 = ⊥ := by
      by_contra h
      refine hU (((genericPoint_spec X).mem_open_set_iff U.1.isOpen).2 ?_)
      rw [Set.univ_inter]
      exact Set.nonempty_iff_ne_empty.2 fun h' => h (by ext1; exact h')
    have : Subsingleton Γ(X, U.1) := by
      rw [hU']
      infer_instance
    exact Subsingleton.elim _ _
  rw [IdealSheafData.stalk_eq_map_germ I _ U hU] at hη
  exact (Ideal.map_eq_bot_iff_of_injective (germ_injective_of_isIntegral X _ hU)).1 hη

/-- A morphism biregular over `V` is injective over `V`. -/
private theorem eq_of_isBiregular {X Y : Scheme.{0}} {f : X ⟶ Y} {V : Y.Opens} (hV : IsBiregular f V)
    {z₁ z₂ : X} (h1 : f z₁ ∈ V) (h : f z₁ = f z₂) : z₁ = z₂ := by
  have : IsIso (f ∣_ V) := hV
  have h2 : f z₂ ∈ V := h ▸ h1
  have hinj := (f ∣_ V).isOpenEmbedding.injective
  have key : ∀ p : (f ⁻¹ᵁ V).toScheme, V.ι ((f ∣_ V) p) = f ((f ⁻¹ᵁ V).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  let p₁ : (f ⁻¹ᵁ V).toScheme := ⟨z₁, by simpa using h1⟩
  let p₂ : (f ⁻¹ᵁ V).toScheme := ⟨z₂, by simpa using h2⟩
  have hp : p₁ = p₂ := hinj (V.ι.isOpenEmbedding.injective (by
    rw [key, key]
    exact h))
  exact congrArg (fun p => ((f ⁻¹ᵁ V).ι p)) hp

/-- If `g` is biregular off a closed set `K` and `f` is a closed map, the exceptional set of
`g ≫ f` lies over `Ex(f) ∪ K`. -/
private theorem exceptionalSet_comp_subset {X Z Y : Scheme.{0}} (g : X ⟶ Z) (f : Z ⟶ Y)
    (hf : IsClosedMap f.base) {K : Set Z} (hK : IsClosed K)
    (hg : IsBiregular g ⟨Kᶜ, hK.isOpen_compl⟩) :
    (exceptionalSet (g ≫ f) : Set X) ⊆ g ⁻¹' ((exceptionalSet f : Set Z) ∪ K) := by
  intro x hx
  by_contra hxn
  simp only [Set.mem_preimage, Set.mem_union, not_or] at hxn
  obtain ⟨h1, h2⟩ := hxn
  rw [SetLike.mem_coe, mem_exceptionalSet] at hx h1
  rw [not_not] at h1
  let V : Y.Opens := biregularLocus f ⊓ ⟨(f.base '' K)ᶜ, (hf K hK).isOpen_compl⟩
  have hyV : f (g x) ∈ V := by
    refine ⟨h1, ?_⟩
    rintro ⟨k, hk, hkx⟩
    exact h2 (eq_of_isBiregular (isBiregular_biregularLocus f) (by rw [hkx]; exact h1) hkx ▸ hk)
  have hV : IsBiregular (g ≫ f) V := by
    unfold IsBiregular
    rw [morphismRestrict_comp]
    have h3 : IsIso (f ∣_ V) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
    have h4 : IsIso (g ∣_ f ⁻¹ᵁ V) := by
      refine isBiregular_iff_le_biregularLocus.mpr (le_trans ?_ (le_biregularLocus hg))
      intro z hz
      exact fun hzK => hz.2 ⟨z, hzK, rfl⟩
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h4 h3
  apply hx
  rw [Scheme.Hom.comp_apply]
  exact le_biregularLocus hV hyV

/-- A closed subset of pure codimension one of a Noetherian scheme is a finite union of
supports of prime divisors. -/
private theorem exists_finset_primeDivisor_eq {X : Scheme.{0}} [NoetherianSpace X] {T : Set X}
    (hT : IsClosed T) (hp : IsPureCodimOne (⟨T, hT⟩ : Closeds X)) :
    ∃ Ps : Finset (MMP.Mori.PrimeDivisor X), T = ⋃ P ∈ Ps, (P.support : Set X) := by
  classical
  obtain ⟨hfin, hcov⟩ := MMP.Resolution.Aux.finite_and_cover_componentsOf hT
  have key : ∀ W ∈ MMP.Resolution.componentsOf T,
      ∃ P : MMP.Mori.PrimeDivisor X, (P.support : Set X) = W := by
    intro W hW
    have hWc := MMP.Resolution.Aux.isClosed_of_mem_componentsOf hT hW
    let W' : IrreducibleCloseds X := ⟨W, hW.1.1, hWc⟩
    have hmax : Maximal (fun W'' : IrreducibleCloseds X =>
        (W'' : Set X) ⊆ ((⟨T, hT⟩ : Closeds X) : Set X)) W' :=
      ⟨hW.1.2, fun V hV hle => hW.2 ⟨V.isIrreducible, hV⟩ hle⟩
    have h1 := hp W' hmax
    obtain ⟨η, hη⟩ := QuasiSober.sober hW.1.1 hWc
    have hW'eq : W' = IrreducibleCloseds.closureSingleton η := by
      ext1
      exact hη.symm
    rw [hW'eq, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton] at h1
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne η h1, ?_⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hη
  let S : Set (MMP.Mori.PrimeDivisor X) :=
    (fun P : MMP.Mori.PrimeDivisor X => (P.support : Set X)) ⁻¹' MMP.Resolution.componentsOf T
  have hS : S.Finite := hfin.preimage fun P _ Q _ h =>
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset h.le
  refine ⟨hS.toFinset, ?_⟩
  ext x
  simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
  constructor
  · intro hx
    obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.1 (hcov hx)
    obtain ⟨P, hPW⟩ := key W hW
    exact ⟨P, show (P.support : Set X) ∈ _ from hPW ▸ hW, hPW ▸ hxW⟩
  · rintro ⟨P, hP, hx⟩
    exact (show (P.support : Set X) ∈ MMP.Resolution.componentsOf T from hP).1.2 hx

private theorem coe_supp_reducedDivisorOf {X : Scheme.{0}} (Ps : Finset (MMP.Mori.PrimeDivisor X)) :
    ((MMP.Intersection.reducedDivisorOf Ps).supp : Set X) =
      ⋃ P ∈ Ps, (P.support : Set X) := by
  classical
  ext x
  rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
  simp only [MMP.Intersection.coeff_reducedDivisorOf, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨E, hE, hx⟩
    exact ⟨E, by by_contra h; simp [h] at hE, hx⟩
  · rintro ⟨E, hE, hx⟩
    exact ⟨E, by simp [hE], hx⟩

/-- **A pure codimension one closed subset of an snc closed subset carries a reduced snc
divisor.** -/
private theorem exists_divisor_of_subset {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [NoetherianSpace X]
    [IsLocallyNoetherian X]
    (hreg : ∀ y : X, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk y), IsRegularSystemOfParameters z)
    {D T : Set X} (hD : MMP.Resolution.IsSNCClosedSubset sX D) (hT : IsClosed T)
    (hTp : IsPureCodimOne (⟨T, hT⟩ : Closeds X)) (hsub : T ⊆ D) :
    ∃ F : Divisor X, MMP.Intersection.IsReducedEffective F ∧ DivisorWithCoeffs.IsSNC sX F ∧
      (F.supp : Set X) = T := by
  classical
  obtain ⟨Ps, hPs⟩ := exists_finset_primeDivisor_eq hT hTp
  have hDp : IsPureCodimOne (⟨D, hD.1⟩ : Closeds X) := by
    rcases hD.2 with h | h
    · intro W hW
      exfalso
      obtain ⟨w, hw⟩ := W.isIrreducible.nonempty
      have hwD : w ∈ D := hW.1 hw
      rw [h] at hwD
      exact hwD
    · exact h.1
  obtain ⟨Qs, hQs⟩ := exists_finset_primeDivisor_eq hD.1 hDp
  have hQsnc : (MMP.Intersection.reducedDivisorOf Qs).IsSNC sX :=
    MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNC_reducedDivisorOf_of_isSNCClosedSubset sX hreg
      Qs (hQs ▸ hD)
  have hPQ : Ps ⊆ Qs := by
    intro P hP
    have hPsub : (P.support : Set X) ⊆ ⋃ Q ∈ Qs, (Q.support : Set X) := by
      rw [← hQs]
      refine subset_trans ?_ hsub
      rw [hPs]
      exact Set.subset_biUnion_of_mem (u := fun P : MMP.Mori.PrimeDivisor X =>
        (P.support : Set X)) hP
    obtain ⟨Q, hQ, hPQ⟩ := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.exists_subset_of_isIrreducible
      (fun Q _ => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support Q)
      (MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isIrreducible_support P) hPsub
    rwa [MMP.Fourfold.SNCWeight.PrimeDivisorUnion.eq_of_support_subset hPQ]
  refine ⟨MMP.Intersection.reducedDivisorOf Ps,
    MMP.Intersection.isReducedEffective_reducedDivisorOf Ps,
    hQsnc.of_support_subset (by
      rw [MMP.Intersection.support_reducedDivisorOf, MMP.Intersection.support_reducedDivisorOf]
      exact hPQ), ?_⟩
  rw [coe_supp_reducedDivisorOf, hPs]

/-- The support of a divisor is the union of the supports of its components. -/
private theorem coe_supp_eq_iUnion {X : Scheme.{0}} (F : Divisor X) :
    (F.supp : Set X) = ⋃ E ∈ F.support, (E.support : Set X) := by
  ext x
  rw [SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
  simp only [Set.mem_iUnion, exists_prop, Finsupp.mem_support_iff, DivisorWithCoeffs.coeff_apply]

section Local

/-- If `(w)` is a nonzero prime ideal, `a` is not a unit and `w ∈ (a)`, then `a ∈ (w)`. -/
private theorem mem_span_singleton_of_mem_span_singleton {R : Type*} [CommRing R] [IsDomain R]
    {w a : R} (hw : (Ideal.span {w}).IsPrime) (hw0 : w ≠ 0) (ha : ¬ IsUnit a)
    (h : w ∈ Ideal.span {a}) : a ∈ Ideal.span {w} := by
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h
  have hsa : s * a ∈ Ideal.span {w} := by rw [hs]; exact Ideal.mem_span_singleton_self w
  rcases hw.mem_or_mem hsa with h1 | h1
  · exfalso
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 h1
    apply ha
    have h2 : w * (r * a) = w * 1 := by
      rw [mul_one]
      calc w * (r * a) = r * w * a := by ring
        _ = w := by rw [hr, hs]
    have h3 : r * a = 1 := mul_left_cancel₀ hw0 h2
    exact isUnit_iff_exists_inv.2 ⟨r, by rw [mul_comm]; exact h3⟩
  · exact h1

/-- **Over the centre, a component of an snc divisor of the blow-up is stable under
generization.** -/
private theorem mem_support_of_specializes {X : Scheme.{0}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {Λ : Type*} {D : Λ → X.IdealSheafData} (hI : Resolution.HasSNCWith D I)
    {S : Scheme.{0}} {sX' : blowUp I ⟶ S} {F' : Divisor (blowUp I)}
    (hF' : DivisorWithCoeffs.IsSNC sX' F') {E : Mori.PrimeDivisor (blowUp I)} (hE : E ∈ F'.support)
    (hEs : (E.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' (I.support : Set X))
    {x' y : blowUp I} (hx' : x' ∈ E.support) (hy : y ⤳ x')
    (hyT : blowUpToBase I y ∈ (I.support : Set X)) : y ∈ E.support := by
  classical
  have : IsLocallyNoetherian (blowUp I) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I)
  set π := blowUpToBase I with hπ
  have hx : π x' ∈ (I.support : Set X) := hEs hx'
  obtain ⟨n, z, c, J, hz, -, -, hJ⟩ := hI (π x') hx
  obtain ⟨N, w, m, i₀, σ, U, hw, hmJ, hU, hwi₀, hout, hin, hunit, hσ₀⟩ :=
    Resolution.exists_chart_coordinates I x' hx hz hJ
  set φ := (π.stalkMap x').hom with hφ
  set f' := (blowUp I).fromSpecStalk x' with hf'
  have key : ∀ T : Set X, f' ⁻¹' (π ⁻¹' T) =
      PrimeSpectrum.comap φ ⁻¹' (X.fromSpecStalk (π x') ⁻¹' T) := by
    intro T
    have h := Scheme.SpecMap_stalkMap_fromSpecStalk π (x := x')
    refine Set.ext fun p => ?_
    change π (f' p) ∈ T ↔ X.fromSpecStalk (π x') (PrimeSpectrum.comap φ p) ∈ T
    rw [← Scheme.Hom.comp_apply, hf', ← h]
    rfl
  have hE' : ∀ p : PrimeSpectrum ((blowUp I).presheaf.stalk x'),
      π (f' p) ∈ I.support ↔ w i₀ ∈ p.asIdeal := by
    intro p
    refine (Set.ext_iff.1 (key I.support) p).trans
      ((Set.ext_iff.1 (Resolution.preimage_fromSpecStalk_support I (π x'))
        (PrimeSpectrum.comap φ p)).trans ?_)
    rw [hJ]
    refine (PrimeSpectrum.mem_zeroLocus _ _).trans ?_
    rw [SetLike.coe_subset_coe, Ideal.span_le]
    constructor
    · intro h
      rw [hwi₀]
      exact h ⟨m, hmJ, rfl⟩
    · rintro h _ ⟨j, hj, rfl⟩
      change φ (z j) ∈ p.asIdeal
      by_cases hjm : j = m
      · rw [hjm, ← hwi₀]; exact h
      by_cases hjU : j ∈ U
      · obtain ⟨u, -, hu⟩ := hunit j hjU
        rw [hu]; exact Ideal.mul_mem_left _ _ h
      · rw [hin j hj hjm hjU]; exact Ideal.mul_mem_left _ _ h
  obtain ⟨n', z', jj, hz', -, hI'⟩ := hF'.2 x'
  set a := jj ⟨E, hE, hx'⟩
  have hstE : IdealSheafData.stalk E.idealSheaf x' = Ideal.span {z' a} := hI' ⟨E, hE, hx'⟩
  have : IsRegularLocalRing ((blowUp I).presheaf.stalk x') :=
    isRegularLocalRing_of_isRegularSystemOfParameters hz'
  have : IsDomain ((blowUp I).presheaf.stalk x') := IsRegularLocalRing.isDomain _
  have hPa := Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz' a
  let Pa : PrimeSpectrum ((blowUp I).presheaf.stalk x') := ⟨_, hPa⟩
  have hpre := Resolution.preimage_fromSpecStalk_support E.idealSheaf x'
  rw [hstE] at hpre
  have hPaE : f' Pa ∈ (E.idealSheaf.support : Set (blowUp I)) :=
    (Set.ext_iff.1 hpre Pa).2 ((PrimeSpectrum.mem_zeroLocus _ _).2 (fun x hx => hx))
  have hwa : w i₀ ∈ Ideal.span {z' a} := (hE' Pa).1 (hEs hPaE)
  have hza : z' a ∈ Ideal.span {w i₀} := by
    refine mem_span_singleton_of_mem_span_singleton
      (Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hw i₀)
      (Resolution.ne_zero_of_isRegularSystemOfParameters hw i₀) ?_ hwa
    have : z' a ∈ IsLocalRing.maximalIdeal _ := hz'.1 ▸ Ideal.subset_span ⟨a, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 this
  have hyr : y ∈ Set.range f' := by rw [hf', Scheme.range_fromSpecStalk]; exact hy
  obtain ⟨P, rfl⟩ := hyr
  have hwP : w i₀ ∈ P.asIdeal := (hE' P).1 hyT
  refine (Set.ext_iff.1 hpre P).2 ((PrimeSpectrum.mem_zeroLocus _ _).2 ?_)
  rw [SetLike.coe_subset_coe, Ideal.span_le, Set.singleton_subset_iff]
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hza
  rw [← hr]
  exact Ideal.mul_mem_left _ _ hwP

/-- **Components of an snc divisor of the blow-up lying over the centre are disjoint.** -/
private theorem disjoint_support_of_subset_preimage {X : Scheme.{0}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {Λ : Type*} {D : Λ → X.IdealSheafData} (hI : Resolution.HasSNCWith D I)
    {S : Scheme.{0}} {sX' : blowUp I ⟶ S} {F' : Divisor (blowUp I)}
    (hF' : DivisorWithCoeffs.IsSNC sX' F') {E E' : Mori.PrimeDivisor (blowUp I)}
    (hE : E ∈ F'.support) (hne : E ≠ E')
    (hEs : (E.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' (I.support : Set X))
    (hE's : (E'.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' (I.support : Set X)) :
    Disjoint (E.support : Set (blowUp I)) E'.support := by
  rw [Set.disjoint_left]
  intro x' hx hx'
  have hmem : E'.genericPoint ∈ E'.support := genericPoint_mem_support _
  have hη : E'.genericPoint ⤳ x' := by
    rw [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact hx'
  exact hne (eq_of_genericPoint_mem_support
    (mem_support_of_specializes hI hF' hE hEs hx hη (hE's hmem))).symm

/-- **A component of an snc divisor of the blow-up lying over the centre is open in the
inverse image of the centre.** -/
private theorem exists_isOpen_inter_subset {X : Scheme.{0}} [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {Λ : Type*} {D : Λ → X.IdealSheafData} (hI : Resolution.HasSNCWith D I)
    [NoetherianSpace (blowUp I)]
    {S : Scheme.{0}} {sX' : blowUp I ⟶ S} {F' : Divisor (blowUp I)}
    (hF' : DivisorWithCoeffs.IsSNC sX' F') {E : Mori.PrimeDivisor (blowUp I)} (hE : E ∈ F'.support)
    (hEs : (E.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' (I.support : Set X))
    {x' : blowUp I} (hx' : x' ∈ E.support) :
    ∃ W : Set (blowUp I), IsOpen W ∧ x' ∈ W ∧
      ∀ y ∈ W, blowUpToBase I y ∈ (I.support : Set X) → y ∈ E.support := by
  classical
  set T : Set (blowUp I) := blowUpToBase I ⁻¹' (I.support : Set X)
  have hT : IsClosed T := I.support.isClosed.preimage (blowUpToBase I).continuous
  obtain ⟨hfin, hcov⟩ := Resolution.Aux.finite_and_cover_componentsOf hT
  set S₁ := {V ∈ Resolution.componentsOf T | x' ∉ V}
  have hS₁ : IsClosed (⋃ V ∈ S₁, V) :=
    (hfin.subset fun V hV => hV.1).isClosed_biUnion fun V hV =>
      Resolution.Aux.isClosed_of_mem_componentsOf hT hV.1
  refine ⟨(⋃ V ∈ S₁, V)ᶜ, hS₁.isOpen_compl, ?_, fun y hy hyT => ?_⟩
  · simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun V hV hxV => hV.2 hxV
  · obtain ⟨V, hV, hyV⟩ := Set.mem_sUnion.1 (hcov hyT)
    have hxV : x' ∈ V := by
      by_contra hxV
      exact hy (Set.mem_iUnion₂.2 ⟨V, ⟨hV, hxV⟩, hyV⟩)
    have hVc := Resolution.Aux.isClosed_of_mem_componentsOf hT hV
    obtain ⟨η, hη⟩ := QuasiSober.sober hV.1.1 hVc
    have hηV : η ∈ V := hη ▸ subset_closure rfl
    have hηx : η ⤳ x' := specializes_iff_mem_closure.2 (hη.symm ▸ hxV)
    have hηE := mem_support_of_specializes hI hF' hE hEs hx' hηx (hV.1.2 hηV)
    have hVE : V ⊆ E.support := by
      rw [← hη]
      exact closure_minimal (Set.singleton_subset_iff.2 hηE) E.idealSheaf.support.isClosed
    exact hVE hyV

end Local

end Divisor

section Exceptional

open Stacks.AlgebraicGeometry (exceptionalSubschemeMap)
open MMP.Resolution (IsSmoothBlowup isClosedMap_exceptionalSubschemeMap connectedSpace_projSpace)

variable {k : Type} [Field k]

/-- **The biregular locus of a composite with a surjection.** If `q` is surjective and `r` is
separated with reduced source, `r` is biregular wherever `q ≫ r` is. -/
private theorem isBiregular_of_comp {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z) (hq : Function.Surjective q)
    (r : Z ⟶ Y) [IsSeparated r] [IsReduced Z] {V : Y.Opens} (hV : IsBiregular (q ≫ r) V) :
    IsBiregular r V := by
  have hφ : IsIso ((q ≫ r) ∣_ V) := hV
  rw [morphismRestrict_comp] at hφ
  set φ := q ∣_ r ⁻¹ᵁ V ≫ r ∣_ V with hφdef
  haveI : IsIso φ := hφ
  set s := inv φ ≫ q ∣_ r ⁻¹ᵁ V with hsdef
  have hs : s ≫ r ∣_ V = 𝟙 _ := by
    rw [hsdef, Category.assoc, ← hφdef, IsIso.inv_hom_id]
  have : IsClosedImmersion (s ≫ r ∣_ V) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s (r ∣_ V)
  have hsur : Surjective s := by
    refine ⟨fun u ↦ ?_⟩
    obtain ⟨w, hw⟩ := hq ((r ⁻¹ᵁ V).ι u)
    have hwV : w ∈ q ⁻¹ᵁ (r ⁻¹ᵁ V) := by
      change q w ∈ r ⁻¹ᵁ V
      rw [hw]
      exact u.2
    let w' : (q ⁻¹ᵁ r ⁻¹ᵁ V).toScheme := ⟨w, hwV⟩
    refine ⟨φ w', ?_⟩
    have h1 : φ ≫ s = q ∣_ r ⁻¹ᵁ V := by rw [hsdef, IsIso.hom_inv_id_assoc]
    rw [← Scheme.Hom.comp_apply, h1]
    apply (r ⁻¹ᵁ V).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    exact hw
  have : IsIso s := isIso_of_isClosedImmersion_of_surjective s
  have : r ∣_ V = inv s := (IsIso.inv_eq_of_hom_inv_id hs).symm
  change IsIso (r ∣_ V)
  rw [this]
  infer_instance

private theorem biregularLocus_comp_le {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z) (hq : Function.Surjective q)
    (r : Z ⟶ Y) [IsSeparated r] [IsReduced Z] :
    biregularLocus (q ≫ r) ≤ biregularLocus r :=
  le_biregularLocus (isBiregular_of_comp q hq r (isBiregular_biregularLocus (q ≫ r)))

/-- The exceptional set of a composite with a surjection contains the inverse image of the
exceptional set. -/
private theorem preimage_exceptionalSet_subset {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z)
    (hq : Function.Surjective q) (r : Z ⟶ Y) [IsSeparated r] [IsReduced Z] :
    q ⁻¹' (exceptionalSet r : Set Z) ⊆ exceptionalSet (q ≫ r) := by
  intro x hx h
  apply hx
  have := biregularLocus_comp_le q hq r h
  rwa [Scheme.Hom.comp_apply] at this

/-- The exceptional set of a surjection is contained in that of its composite with a separated
morphism of reduced source: where `q ≫ r` is biregular, so are `r` and hence `q`. -/
private theorem exceptionalSet_subset_comp {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z)
    (hq : Function.Surjective q) (r : Z ⟶ Y) [IsSeparated r] [IsReduced Z] :
    (exceptionalSet q : Set Z') ⊆ exceptionalSet (q ≫ r) := by
  intro x hx h
  apply hx
  set V := biregularLocus (q ≫ r)
  have hV : IsBiregular (q ≫ r) V := isBiregular_biregularLocus (q ≫ r)
  have hr : IsBiregular r V := isBiregular_of_comp q hq r hV
  have hφ : IsIso ((q ≫ r) ∣_ V) := hV
  have hr' : IsIso (r ∣_ V) := hr
  rw [morphismRestrict_comp] at hφ
  have : IsIso (q ∣_ r ⁻¹ᵁ V) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _ (q ∣_ r ⁻¹ᵁ V) (r ∣_ V) hr' hφ
  have hq' : IsBiregular q (r ⁻¹ᵁ V) := this
  exact le_biregularLocus hq' (show r (q x) ∈ V from h)

/-- **Every point over the centre lies on a prime divisor over the centre**: the exceptional
divisor of a blow-up is an effective Cartier divisor, so by Krull's principal ideal theorem the
generic points of its components have coheight one. -/
private theorem exists_primeDivisor_mem_of_mem_support {X : Scheme.{0}} (I : X.IdealSheafData)
    [IsLocallyNoetherian (blowUp I)] {y : blowUp I}
    (hy : y ∈ ((exceptionalIdeal I).support : Set (blowUp I))) :
    ∃ G : Mori.PrimeDivisor (blowUp I), y ∈ G.support ∧
      (G.support : Set (blowUp I)) ⊆ (exceptionalIdeal I).support := by
  set D := exceptionalIdeal I
  obtain ⟨ξ, rfl⟩ : y ∈ Set.range D.subschemeι := by rw [D.range_subschemeι]; exact hy
  let c : irreducibleComponents D.subscheme :=
    ⟨irreducibleComponent ξ, irreducibleComponent_mem_irreducibleComponents ξ⟩
  let η : D.subscheme := genericPoints.ofComponent c
  have hη : IsGenericPoint η (c : Set D.subscheme) := genericPoints.isGenericPoint_ofComponent c
  have h1 := AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isEffectiveCartierDivisor D
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) η ⟨c, hη⟩
  rw [ringKrullDim_stalk_eq_coheight] at h1
  have hcoh : Order.coheight (D.subschemeι η) = 1 := by exact_mod_cast h1
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_, ?_⟩
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact specializes_iff_mem_closure.1
      ((hη.specializes mem_irreducibleComponent).map D.subschemeι.continuous)
  · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    refine closure_minimal ?_ D.support.isClosed
    rw [Set.singleton_subset_iff]
    have : D.subschemeι η ∈ Set.range D.subschemeι := ⟨η, rfl⟩
    rwa [D.range_subschemeι] at this

/-- A closed map which is an isomorphism over a dense open is surjective. -/
private theorem surjective_of_isIso_restrict {X Y : Scheme.{0}} (f : X ⟶ Y) (hf : IsClosedMap f.base)
    (U : Y.Opens) [IsIso (f ∣_ U)] (hU : Dense (U : Set Y)) : Function.Surjective f := by
  have hsub : (U : Set Y) ⊆ Set.range f := by
    intro y hy
    let y' : U.toScheme := ⟨y, hy⟩
    let p := (inv (f ∣_ U)) y'
    have hp : (f ∣_ U) p = y' := by
      rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    refine ⟨(f ⁻¹ᵁ U).ι p, ?_⟩
    have key : U.ι ((f ∣_ U) p) = f ((f ⁻¹ᵁ U).ι p) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rw [← key, hp]
    rfl
  have hcl : IsClosed (Set.range f) := by
    rw [← Set.image_univ]
    exact hf _ isClosed_univ
  intro y
  have : y ∈ closure (U : Set Y) := hU y
  exact (closure_minimal hsub hcl) this

/-- **An old partner.** If `q` is surjective and closed, every component of the full exceptional
divisor of `r` lies in the image of a component of the full exceptional divisor of `q ≫ r` not
lying over a closed subset `K` all of whose irreducible closed subsets have codimension at least
two. -/
private theorem exists_mem_support_subset_image {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z)
    (hq : Function.Surjective q) (hqc : IsClosedMap q.base) (r : Z ⟶ Y) [IsSeparated r]
    [IsReduced Z] {F : Divisor Z} (hF : (F.supp : Set Z) = exceptionalSet r) {F' : Divisor Z'}
    (hF' : (F'.supp : Set Z') = exceptionalSet (q ≫ r)) {K : Set Z} (hK : IsClosed K)
    (hKcod : ∀ W : IrreducibleCloseds Z, (W : Set Z) ⊆ K → 2 ≤ codimension W)
    {P : Mori.PrimeDivisor Z} (hP : P ∈ F.support) :
    ∃ E ∈ F'.support, ¬ ((E.support : Set Z') ⊆ q ⁻¹' K) ∧
      (P.support : Set Z) ⊆ q.base '' E.support := by
  have hηP : P.genericPoint ∈ (P.support : Set Z) := genericPoint_mem_support _
  have hηK : P.genericPoint ∉ K := by
    intro h
    have hsub : (P.support : Set Z) ⊆ K := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_minimal (Set.singleton_subset_iff.2 h) hK
    have h2 := hKcod (IrreducibleCloseds.closureSingleton P.genericPoint) (by
      rw [IrreducibleCloseds.coe_closureSingleton, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hsub)
    rw [P.codimension_closure_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨w, hw⟩ := hq P.genericPoint
  have hwex : w ∈ (exceptionalSet (q ≫ r) : Set Z') := by
    refine preimage_exceptionalSet_subset q hq r ?_
    change q w ∈ (exceptionalSet r : Set Z)
    rw [hw, ← hF, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
    exact ⟨P, Finsupp.mem_support_iff.1 hP, hηP⟩
  rw [← hF', SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff] at hwex
  obtain ⟨E, hE, hwE⟩ := hwex
  refine ⟨E, Finsupp.mem_support_iff.2 hE, fun h => hηK (hw ▸ h hwE), ?_⟩
  have hcl : IsClosed (q.base '' (E.support : Set Z')) := hqc _ E.idealSheaf.support.isClosed
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact closure_minimal (Set.singleton_subset_iff.2 ⟨w, hwE, hw⟩) hcl

/-- For a smooth blow-up whose centre has nonzero stalks, every fibre of the exceptional divisor
over the centre is connected. -/
private theorem isConnected_preimage_exceptionalSubschemeMap' {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [Smooth sX] (I : X.IdealSheafData) (h : IsSmoothBlowup sX I)
    (hne : ∀ x, IdealSheafData.stalk I x ≠ ⊥) (z : I.subscheme) :
    _root_.IsConnected ((exceptionalSubschemeMap I) ⁻¹' {z}) := by
  obtain ⟨-, -, -, -, hfib⟩ :=
    MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup sX I h
  obtain ⟨c, hc, e, -⟩ := hfib z
  have := isRegularLocalRing_stalk_of_smooth_over_field sX (I.subschemeι z)
  have := IsRegularLocalRing.isDomain (X.presheaf.stalk (I.subschemeι z))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne (I.subschemeι z)
    rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact Ideal.height_eq_zero_iff_eq_bot.mp (by rw [← hc]; rfl)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc0
  have := connectedSpace_projSpace (I.subscheme.residueField z) n
  have : ConnectedSpace ((exceptionalSubschemeMap I).fiber z) :=
    e.inv.homeomorph.surjective.connectedSpace e.inv.homeomorph.continuous
  rw [← Scheme.Hom.range_fiberι]
  exact isConnected_range (Scheme.Hom.continuous _)

/-- **Inverse images of connected subsets of the centre are connected.** -/
private theorem isConnected_preimage_blowUpToBase {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [Smooth sX] (I : X.IdealSheafData) (h : IsSmoothBlowup sX I)
    (hne : ∀ x, IdealSheafData.stalk I x ≠ ⊥) {C : Set X} (hC : IsClosed C)
    (hCc : _root_.IsConnected C) (hCI : C ⊆ (I.support : Set X)) :
    _root_.IsConnected (blowUpToBase I ⁻¹' C) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  set p := exceptionalSubschemeMap I
  have hsurj : Function.Surjective p := fun z =>
    (isConnected_preimage_exceptionalSubschemeMap' sX I h hne z).nonempty
  have hq : Topology.IsQuotientMap p :=
    (isClosedMap_exceptionalSubschemeMap I).isQuotientMap (Scheme.Hom.continuous _) hsurj
  set C' : Set I.subscheme := I.subschemeι ⁻¹' C
  have hC'cl : IsClosed C' := hC.preimage I.subschemeι.continuous
  have hC'im : I.subschemeι '' C' = C := by
    rw [Set.image_preimage_eq_of_subset]
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hCI
  have hC'c : _root_.IsConnected C' := by
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := hCc.nonempty
      obtain ⟨y, hy⟩ := (show C ⊆ Set.range I.subschemeι by
        rw [Scheme.IdealSheafData.range_subschemeι]; exact hCI) hx
      exact ⟨y, show I.subschemeι y ∈ C from hy ▸ hx⟩
    · rw [← I.subschemeι.isClosedEmbedding.isInducing.isPreconnected_image, hC'im]
      exact hCc.isPreconnected
  have hconn := hq.isCoinducing.isConnected_preimage_of_isClosed
    (isConnected_preimage_exceptionalSubschemeMap' sX I h hne) hC'cl hC'c
  have hcomp : p ≫ I.subschemeι = (exceptionalIdeal I).subschemeι ≫ blowUpToBase I :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have himg : (exceptionalIdeal I).subschemeι '' (p ⁻¹' C') = blowUpToBase I ⁻¹' C := by
    ext x'
    constructor
    · rintro ⟨e, he, rfl⟩
      change (blowUpToBase I) ((exceptionalIdeal I).subschemeι e) ∈ C
      rw [← Scheme.Hom.comp_apply, ← hcomp, Scheme.Hom.comp_apply]
      exact he
    · intro hx'
      have hx'' : x' ∈ Set.range (exceptionalIdeal I).subschemeι := by
        rw [Scheme.IdealSheafData.range_subschemeι, exceptionalIdeal,
          Scheme.IdealSheafData.support_comap]
        exact hCI hx'
      obtain ⟨e, rfl⟩ := hx''
      refine ⟨e, ?_, rfl⟩
      change I.subschemeι (p e) ∈ C
      rw [← Scheme.Hom.comp_apply, hcomp, Scheme.Hom.comp_apply]
      exact hx'
  rw [← himg]
  exact hconn.image _ (Scheme.Hom.continuous _).continuousOn

/-- **A component over a connected part of the centre fills its inverse image.** If a component
`E` of an snc divisor of the blow-up lies over a connected closed subset `C` of the centre, then
`q⁻¹ C ⊆ E`: `E` is open and closed in `q⁻¹(V(I))` and `q⁻¹ C` is connected. -/
private theorem preimage_subset_support_of_subset {X : Scheme.{0}} [IsLocallyNoetherian X]
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (I : X.IdealSheafData) (h : IsSmoothBlowup sX I)
    (hne : ∀ x, IdealSheafData.stalk I x ≠ ⊥) {Λ : Type*} {D : Λ → X.IdealSheafData}
    (hI : MMP.Resolution.HasSNCWith D I) [NoetherianSpace (blowUp I)]
    {S : Scheme.{0}} {sX' : blowUp I ⟶ S} {F' : Divisor (blowUp I)}
    (hF' : DivisorWithCoeffs.IsSNC sX' F') {E : Mori.PrimeDivisor (blowUp I)} (hE : E ∈ F'.support)
    {C : Set X} (hC : IsClosed C) (hCc : _root_.IsConnected C) (hCI : C ⊆ (I.support : Set X))
    (hEC : (E.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' C) :
    blowUpToBase I ⁻¹' C ⊆ E.support := by
  classical
  have hEs : (E.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' (I.support : Set X) :=
    hEC.trans (Set.preimage_mono hCI)
  have hconn := isConnected_preimage_blowUpToBase sX I h hne hC hCc hCI
  have hW : ∀ x' ∈ (E.support : Set (blowUp I)), ∃ W : Set (blowUp I), IsOpen W ∧ x' ∈ W ∧
      ∀ y ∈ W, blowUpToBase I y ∈ (I.support : Set X) → y ∈ E.support :=
    fun x' hx' => exists_isOpen_inter_subset hI hF' hE hEs hx'
  choose! W hWo hxW hWE using hW
  set O := ⋃ x' ∈ (E.support : Set (blowUp I)), W x'
  have hOo : IsOpen O := isOpen_biUnion fun x' hx' => hWo x' hx'
  have hpre := hconn.isPreconnected
  rw [isPreconnected_iff_subset_of_disjoint] at hpre
  rcases hpre O (E.support : Set (blowUp I))ᶜ hOo E.idealSheaf.support.isClosed.isOpen_compl
      (fun y hy => by
        by_cases hyE : y ∈ (E.support : Set (blowUp I))
        · exact Or.inl (Set.mem_biUnion hyE (hxW y hyE))
        · exact Or.inr hyE)
      (by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
        intro hy hyO hyE
        obtain ⟨x', hx', hyW⟩ := Set.mem_iUnion₂.1 hyO
        exact hyE (hWE x' hx' y hyW (hCI hy))) with h1 | h1
  · intro y hy
    obtain ⟨x', hx', hyW⟩ := Set.mem_iUnion₂.1 (h1 hy)
    exact hWE x' hx' y hyW (hCI hy)
  · exfalso
    have hmem : E.genericPoint ∈ (E.support : Set (blowUp I)) := genericPoint_mem_support _
    exact h1 (hEC hmem) hmem

/-- **Subvarieties whose image drops dimension are exceptional.** An irreducible closed subset of
dimension `n` whose image has dimension `< n` lies in the exceptional set: over the biregular
locus the morphism is a homeomorphism, and a nonempty open of `C` has dimension `n`. -/
private theorem subset_exceptionalSet_of_lt {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))] (r : Z ⟶ Y) (C : IrreducibleCloseds Z) {n : ℕ}
    (hC : topologicalKrullDim (C : Set Z) = n)
    (hr : topologicalKrullDim (r.base '' (C : Set Z)) < n) :
    (C : Set Z) ⊆ exceptionalSet r := by
  intro c hc
  by_contra hcE
  rw [SetLike.mem_coe, mem_exceptionalSet, not_not] at hcE
  have hV : IsIso (r ∣_ biregularLocus r) := isBiregular_biregularLocus r
  set S := Subvariety.ofIrreducibleCloseds C
  set ιS := S.ideal.subschemeι
  set W' : S.toScheme.Opens := ιS ⁻¹ᵁ (r ⁻¹ᵁ biregularLocus r)
  have hcS : c ∈ Set.range ιS := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    change c ∈ (S.support : Set Z)
    rw [Subvariety.support_ofIrreducibleCloseds]
    exact hc
  obtain ⟨c', hc'⟩ := hcS
  have hW'ne : (W' : Set S.toScheme).Nonempty := ⟨c', by
    change r (ιS c') ∈ biregularLocus r
    rw [hc']
    exact hcE⟩
  have : LocallyOfFiniteType (S.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (ιS ≫ Z ↘ Spec (.of ℂ))
    infer_instance
  have hdim : topologicalKrullDim W'.toScheme = topologicalKrullDim S.toScheme :=
    (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ _ (_ ↘ Spec (.of ℂ)) _
      (TopologicalSpace.Opens.isOpen W') hW'ne).symm
  have hS : topologicalKrullDim S.toScheme = n := by
    have := Subvariety.dim_eq_topologicalKrullDim_support S
    rw [Subvariety.support_ofIrreducibleCloseds] at this
    exact this.trans hC
  -- the inducing map `W' → r(C)`
  have hmemU : ∀ p : W'.toScheme, ιS (W'.ι p) ∈ r ⁻¹ᵁ biregularLocus r := fun p => p.2
  let a : W'.toScheme → (r ⁻¹ᵁ biregularLocus r).toScheme := fun p => ⟨ιS (W'.ι p), hmemU p⟩
  have ha_cont : Continuous a :=
    ((ιS.continuous.comp W'.ι.continuous)).subtype_mk _
  have ha : Topology.IsInducing a := by
    refine Topology.IsInducing.of_comp ha_cont (r ⁻¹ᵁ biregularLocus r).ι.continuous ?_
    exact ιS.isClosedEmbedding.isInducing.comp W'.ι.isOpenEmbedding.isInducing
  have hb : Topology.IsInducing ((biregularLocus r).ι ∘ (r ∣_ biregularLocus r) ∘ a) :=
    (biregularLocus r).ι.isOpenEmbedding.isInducing.comp
      ((r ∣_ biregularLocus r).isOpenEmbedding.isInducing.comp ha)
  have hbeq : ∀ p, ((biregularLocus r).ι ∘ (r ∣_ biregularLocus r) ∘ a) p = r (ιS (W'.ι p)) := by
    intro p
    change (biregularLocus r).ι ((r ∣_ biregularLocus r) (a p)) = _
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rfl
  have hmemC : ∀ p : W'.toScheme, r (ιS (W'.ι p)) ∈ r.base '' (C : Set Z) := by
    intro p
    refine ⟨ιS (W'.ι p), ?_, rfl⟩
    have : ιS (W'.ι p) ∈ Set.range ιS := ⟨_, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι] at this
    change _ ∈ (S.support : Set Z) at this
    rwa [Subvariety.support_ofIrreducibleCloseds] at this
  let g : W'.toScheme → r.base '' (C : Set Z) := fun p => ⟨r (ιS (W'.ι p)), hmemC p⟩
  have hg : Topology.IsInducing g := by
    have hb' : Topology.IsInducing (fun p : W'.toScheme => r (ιS (W'.ι p))) := by
      have : ((biregularLocus r).ι ∘ (r ∣_ biregularLocus r) ∘ a) =
          (fun p : W'.toScheme => r (ιS (W'.ι p))) := funext hbeq
      rw [← this]
      exact hb
    exact hb'.codRestrict hmemC
  have hle := hg.topologicalKrullDim_le
  change topologicalKrullDim W'.toScheme ≤ _ at hle
  rw [hdim, hS] at hle
  exact absurd (hle.trans_lt hr) (lt_irrefl _)

/-- **The degree of a dimension-preserving map is positive.** If `closure {f x}` has the
dimension of `closure {x}`, the residue field extension at `x` has transcendence degree zero and
is essentially of finite type, hence finite, so its degree is nonzero. -/
private theorem residueDegree_ne_zero {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (x : X) {n : ℕ}
    (hξ : topologicalKrullDim (closure ({x} : Set X)) = n)
    (hfξ : topologicalKrullDim (closure ({f x} : Set Y)) = n) :
    f.residueDegree x ≠ 0 := by
  have h1 := Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    ℂ sX x n hξ
  have h2 := Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    ℂ sY (f x) n hfξ
  rw [← hf] at h1
  have hfin := Stacks.Chow.finiteDimensional_residueField_of_relativeDimension_eq
    (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction sY f x (h1.trans h2.symm)
  letI := (f.residueFieldMap x).hom.toAlgebra
  exact (Module.finrank_pos (R := Y.residueField (f x)) (M := X.residueField x)).ne'

/-- The connected components of the support of a closed subscheme are the images of the
connected components of the subscheme. -/
private theorem connectedComponentIn_support_eq_image {X : Scheme.{0}} (I : X.IdealSheafData)
    (z : I.subscheme) :
    connectedComponentIn (I.support : Set X) (I.subschemeι z) =
      I.subschemeι '' connectedComponent z := by
  have hrange : Set.range I.subschemeι = (I.support : Set X) := I.range_subschemeι
  have hy : I.subschemeι z ∈ (I.support : Set X) := hrange ▸ ⟨z, rfl⟩
  have hemb := I.subschemeι.isClosedEmbedding.isEmbedding
  apply subset_antisymm
  · set C := connectedComponentIn (I.support : Set X) (I.subschemeι z)
    have hC : C ⊆ Set.range I.subschemeι := hrange ▸ connectedComponentIn_subset _ _
    have hCim : I.subschemeι '' (I.subschemeι ⁻¹' C) = C := Set.image_preimage_eq_of_subset hC
    have hpc : _root_.IsPreconnected (I.subschemeι ⁻¹' C) := by
      rw [← hemb.isInducing.isPreconnected_image, hCim]
      exact isPreconnected_connectedComponentIn
    have := hpc.subset_connectedComponent (show z ∈ I.subschemeι ⁻¹' C from
      mem_connectedComponentIn hy)
    rw [← hCim]
    exact Set.image_mono this
  · refine (isPreconnected_connectedComponent.image _
      I.subschemeι.continuous.continuousOn).subset_connectedComponentIn
      ⟨z, mem_connectedComponent, rfl⟩ ?_
    rintro _ ⟨w, -, rfl⟩
    exact hrange ▸ ⟨w, rfl⟩

/-- The connected components of the support of a normal closed subscheme are irreducible. -/
private theorem isIrreducible_connectedComponentIn_support {X : Scheme.{0}}
    (I : X.IdealSheafData) [IsLocallyNoetherian I.subscheme] [NoetherianSpace I.subscheme]
    [IsNormal I.subscheme] {x : X} (hx : x ∈ (I.support : Set X)) :
    IsIrreducible (connectedComponentIn (I.support : Set X) x) := by
  obtain ⟨z, rfl⟩ : x ∈ Set.range I.subschemeι := by rw [I.range_subschemeι]; exact hx
  rw [connectedComponentIn_support_eq_image]
  exact (isIrreducible_connectedComponent_of_isNormal I.subscheme z).image _
    I.subschemeι.continuous.continuousOn

/-- For an snc divisor, a connected component of the intersection of two distinct components is
irreducible: the intersection is regular, hence normal. -/
private theorem isIrreducible_carrier {Z : Scheme.{0}} {S : Scheme.{0}} (sZ : Z ⟶ S)
    [IsLocallyNoetherian Z] [NoetherianSpace Z] {B : Divisor Z}
    (hBsnc : DivisorWithCoeffs.IsSNC sZ B) (σ : DoubleSurface B) : IsIrreducible σ.carrier := by
  set D : Z.IdealSheafData := σ.fst.idealSheaf ⊔ σ.snd.idealSheaf
  have hDsupp : (D.support : Set Z) = σ.fst.support ∩ σ.snd.support := by
    rw [Scheme.IdealSheafData.support_sup]; rfl
  have : IsLocallyNoetherian D.subscheme := isLocallyNoetherian_of_isClosedImmersion D.subschemeι
  have : NoetherianSpace D.subscheme :=
    D.subschemeι.isClosedEmbedding.isEmbedding.noetherianSpace
  have hsup : ∀ y : Z, IdealSheafData.stalk D y = IdealSheafData.stalk σ.fst.idealSheaf y ⊔
      IdealSheafData.stalk σ.snd.idealSheaf y := by
    intro y
    have : D = ⨆ b : Bool, cond b σ.fst.idealSheaf σ.snd.idealSheaf := by
      rw [iSup_bool_eq]; rfl
    rw [this, MMP.Resolution.stalk_iSup, iSup_bool_eq]
    rfl
  have : IsNormal D.subscheme := by
    rw [isNormal_iff_stalk_normal]
    intro z
    have hz : D.subschemeι z ∈ (D.support : Set Z) := by
      rw [← D.range_subschemeι]; exact ⟨z, rfl⟩
    rw [hDsupp] at hz
    obtain ⟨n, w, j, hw, -, hI⟩ := hBsnc.2 (D.subschemeι z)
    have := isRegularLocalRing_of_isRegularSystemOfParameters hw
    have hstalk : IdealSheafData.stalk D (D.subschemeι z) =
        Ideal.span (w '' ((({j ⟨σ.fst, σ.fst_mem, hz.1⟩, j ⟨σ.snd, σ.snd_mem, hz.2⟩} :
          Finset (Fin n)) : Set (Fin n)))) := by
      rw [hsup, hI ⟨σ.fst, σ.fst_mem, hz.1⟩, hI ⟨σ.snd, σ.snd_mem, hz.2⟩, Finset.coe_insert,
        Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton, Ideal.span_insert]
    have := isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient D z (by
      rw [hstalk]
      exact MMP.Resolution.isRegularLocalRing_quotient_span_image w hw _)
    exact ⟨IsRegularLocalRing.isDomain _, isIntegrallyClosed_of_isRegularLocalRing _⟩
  obtain ⟨y, hy, hσ⟩ := σ.isComponent
  rw [← hDsupp] at hy
  rw [← hσ, ← hDsupp]
  exact isIrreducible_connectedComponentIn_support D hy

end Exceptional

section JAssembly

open MMP.borelMooreHomology UnderlyingSpace

/-- The `ℂ`-points of `W` mapping, along `f`, into the points of `Z'` over `q⁻¹ T`. -/
private noncomputable def toPreimagePointsOver {W Z' Z : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [Z'.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))] (f : W ⟶ Z') [f.IsOver (Spec (.of ℂ))]
    (q : Z' ⟶ Z) [q.IsOver (Spec (.of ℂ))] (T : Set Z) (hT : Set.range (f ≫ q) ⊆ T) :
    TopCat.of (UnderlyingSpace ℂ W) ⟶ TopCat.of ((TopCat.ofHom (map (K := ℂ) q)) ⁻¹'
      pointsOver (K := ℂ) T : Set (TopCat.of (UnderlyingSpace ℂ Z'))) :=
  TopCat.ofHom ⟨fun p => ⟨map (K := ℂ) f p, by
      change (map (K := ℂ) q (map (K := ℂ) f p)).toHom _ ∈ T
      rw [toHom_map, toHom_map]
      exact hT ⟨_, rfl⟩⟩, (map (K := ℂ) f).continuous.subtype_mk _⟩

private theorem isProperMap_toPreimagePointsOver {W Z' Z : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [Z'.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z' ↘ Spec (.of ℂ))]
    [T2Space (UnderlyingSpace ℂ Z')] (f : W ⟶ Z') [f.IsOver (Spec (.of ℂ))] [IsProper f]
    (q : Z' ⟶ Z) [q.IsOver (Spec (.of ℂ))] (T : Set Z) (hT : Set.range (f ≫ q) ⊆ T) :
    IsProperMap (toPreimagePointsOver f q T hT) :=
  isProperMap_of_comp_of_t2 (toPreimagePointsOver f q T hT).hom.continuous continuous_subtype_val
    (isProperMap_map (K := ℂ) f)

/-- The `ℂ`-points of `W` mapping, along `g`, into the points of `Z` over `T`. -/
private noncomputable def toPointsOver {W Z : Scheme.{0}} [W.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))]
    (g : W ⟶ Z) [g.IsOver (Spec (.of ℂ))] (T : Set Z) (hT : Set.range g ⊆ T) :
    TopCat.of (UnderlyingSpace ℂ W) ⟶
      TopCat.of (pointsOver (K := ℂ) T : Set (TopCat.of (UnderlyingSpace ℂ Z))) :=
  TopCat.ofHom ⟨fun p => ⟨map (K := ℂ) g p, by
      rw [mem_pointsOver, toHom_map]
      exact hT ⟨_, rfl⟩⟩, (map (K := ℂ) g).continuous.subtype_mk _⟩

private theorem isProperMap_toPointsOver {W Z : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [Z.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Z ↘ Spec (.of ℂ))]
    [T2Space (UnderlyingSpace ℂ Z)]
    (g : W ⟶ Z) [g.IsOver (Spec (.of ℂ))] [IsProper g] (T : Set Z) (hT : Set.range g ⊆ T) :
    IsProperMap (toPointsOver g T hT) :=
  isProperMap_of_comp_of_t2 (toPointsOver g T hT).hom.continuous continuous_subtype_val
    (isProperMap_map (K := ℂ) g)

private theorem toPreimagePointsOver_comp_closedRestrict {W Z' Z : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [Z'.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))] (f : W ⟶ Z')
    [f.IsOver (Spec (.of ℂ))] (q : Z' ⟶ Z) [q.IsOver (Spec (.of ℂ))] (T : Set Z)
    (hT : Set.range (f ≫ q) ⊆ T) :
    toPreimagePointsOver f q T hT ≫ closedRestrict (TopCat.ofHom (map (K := ℂ) q))
      (pointsOver (K := ℂ) T) = toPointsOver (f ≫ q) T hT := by
  refine TopCat.ext fun p => Subtype.ext ?_
  change map (K := ℂ) q (map (K := ℂ) f p) = map (K := ℂ) (f ≫ q) p
  rw [map_comp]
  rfl

private theorem toPointsOver_congr {W Z : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [Z.Over (Spec (.of ℂ))] {g g' : W ⟶ Z} [g.IsOver (Spec (.of ℂ))] [g'.IsOver (Spec (.of ℂ))]
    (h : g = g') (T : Set Z) (hT : Set.range g ⊆ T) (hT' : Set.range g' ⊆ T) :
    toPointsOver g T hT = toPointsOver g' T hT' := by
  subst h
  rfl

private theorem toPointsOver_comp {V W Z : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [W.Over (Spec (.of ℂ))] [Z.Over (Spec (.of ℂ))] (g : V ⟶ W) (h : W ⟶ Z)
    [g.IsOver (Spec (.of ℂ))] [h.IsOver (Spec (.of ℂ))] (T : Set Z)
    (hT : Set.range (g ≫ h) ⊆ T) (hT' : Set.range h ⊆ T) :
    toPointsOver (g ≫ h) T hT = TopCat.ofHom (map (K := ℂ) g) ≫ toPointsOver h T hT' := by
  refine TopCat.ext fun p => Subtype.ext ?_
  change map (K := ℂ) (g ≫ h) p = map (K := ℂ) h (map (K := ℂ) g p)
  rw [map_comp]
  rfl

private theorem pushforward_congr {R : Type} [CommRing R] {M : ModuleCat.{0} R}
    {X Y : TopCat.{0}} [T2Space X] [T2Space Y] {f g : X ⟶ Y} (h : f = g) (hf : IsProperMap f)
    (hg : IsProperMap g) (j : ℤ) : pushforward R M f hf j = pushforward R M g hg j := by
  subst h; rfl

/-- Push-forward of rational cycles is functorial (Stacks 02R5). -/
private theorem rationalPushforward_comp {X Y W : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] [W.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
    [IsProper f] (g : Y ⟶ W) [g.IsOver (Spec (.of ℂ))] [IsProper g] (k : ℕ)
    (L : Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k) :
    Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ (W ↘ Spec (.of ℂ)) k
        (f ≫ g) (comp_over (f ≫ g) _) L =
      Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ k g (comp_over g _)
        (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ k f
          (comp_over f _) L) :=
  (Chow.rationalProperPushforward_rationalProperPushforward f g (comp_over f _) (comp_over g _)
    L).symm

/-- Push-forward of rational cycles along equal morphisms. -/
private theorem rationalPushforward_congr {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {u v : X ⟶ Y} (h : u = v) [IsProper u]
    [IsProper v] [u.IsOver (Spec (.of ℂ))] [v.IsOver (Spec (.of ℂ))] (k : ℕ)
    (L : RatCycles X k) : ratPush u k L = ratPush v k L := by
  subst h; rfl

/-- An irreducible closed subset of the components of codimension at least two has codimension
at least two. -/
private theorem two_le_codimension_of_subset {X : Scheme.{0}} [NoetherianSpace X] {S : Set X}
    (hS : IsClosed S) (W : IrreducibleCloseds X)
    (hW : (W : Set X) ⊆ MMP.Resolution.componentsOfCodimAtLeastTwo S) : 2 ≤ codimension W := by
  obtain ⟨η, hη⟩ := QuasiSober.sober W.isIrreducible W.isClosed
  have hηW : η ∈ (W : Set X) := hη ▸ subset_closure rfl
  obtain ⟨V, hV⟩ := Set.mem_iUnion.1 (hW hηW)
  obtain ⟨hVc, hV⟩ := Set.mem_iUnion.1 hV
  obtain ⟨h2, hηV⟩ := Set.mem_iUnion.1 hV
  have hle : W ≤ MMP.Resolution.irreducibleClosure hVc.1.1 := by
    change (W : Set X) ⊆ closure V
    rw [← hη]
    exact closure_mono (Set.singleton_subset_iff.2 hηV)
  rw [codimension_eq_coheight] at h2 ⊢
  exact h2.trans (Order.coheight_anti hle)

/-- The components of codimension at least two of `S` lie in `S`. -/
private theorem componentsOfCodimAtLeastTwo_subset {X : Scheme.{0}} (S : Set X) :
    MMP.Resolution.componentsOfCodimAtLeastTwo S ⊆ S := by
  intro x hx
  obtain ⟨W, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨hW, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨-, hx⟩ := Set.mem_iUnion.1 hx
  exact hW.1.2 hx

/-- In an irreducible Noetherian scheme, the components of codimension at least two of a closed
set do not cover the scheme: the whole scheme has codimension zero. -/
private theorem nonempty_compl_componentsOfCodimAtLeastTwo {X : Scheme.{0}} [NoetherianSpace X]
    [IrreducibleSpace X] {S : Set X} (hS : IsClosed S) :
    (MMP.Resolution.componentsOfCodimAtLeastTwo S)ᶜ.Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
  have h2 := two_le_codimension_of_subset hS
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ h.symm.subset
  have h0 : Order.coheight (⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ :
      IrreducibleCloseds X) = 0 :=
    Order.coheight_eq_zero.2 fun b _ => SetLike.coe_subset_coe.1 (Set.subset_univ _)
  rw [codimension_eq_coheight, h0] at h2
  exact absurd h2 (by decide)

/-- A centre whose blow-up has a point is nonzero: the blow-up of the zero ideal is empty. -/
private theorem ne_bot_of_blowUp {X : Scheme.{0}} {I : X.IdealSheafData} (x : blowUp I) :
    I ≠ ⊥ := by
  rintro rfl
  have := isEmpty_blowUp_bot X
  exact isEmptyElim x

/-- **The blow-up of a nonzero centre having simple normal crossings with some family is
surjective** (when closed): it is an isomorphism over the dense complement of the components of
codimension at least two. -/
private theorem surjective_blowUpToBase {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [NoetherianSpace X] {Λ : Type*} {E : Λ → X.IdealSheafData} {I : X.IdealSheafData}
    (hI : MMP.Resolution.HasSNCWith E I) (hI0 : I ≠ ⊥) (hc : IsClosedMap (blowUpToBase I).base) :
    Function.Surjective (blowUpToBase I) :=
  haveI := isIso_blowUpToBase_restrict_complCodimTwo hI (stalk_ne_bot_of_ne_bot hI0)
  surjective_of_isIso_restrict _ hc (complCodimTwo I)
    ((MMP.Resolution.isClosed_componentsOfCodimAtLeastTwo I.support.isClosed).isOpen_compl.dense
      (nonempty_compl_componentsOfCodimAtLeastTwo I.support.isClosed))

end JAssembly

section Step

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- **One blow-up, geometry.** Blowing up a nonzero smooth centre having simple normal crossings
with the exceptional locus of a model gives again a model. -/
private theorem isModel_blowUp {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYQ : IsQFactorial sY)
    (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    (hI : I ≠ ⊥)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))] :
    IsModel sY (blowUpToBase I ≫ r) := by
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  obtain ⟨hvar', hprojq, hbir⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have hover : blowUpToBase I ≫ (Z ↘ Spec (.of ℂ)) = blowUp I ↘ Spec (.of ℂ) :=
    (inferInstance : (blowUpToBase I).IsOver (Spec (.of ℂ))).comp_over
  have hprojZ' : IsProjective (blowUp I ↘ Spec (.of ℂ)) := by
    rw [← hover]
    exact hprojq.comp hM.isProjective
  have hcx : IsComplexScheme (blowUp I) := MMP.Analytic.isComplexScheme_of_isProjective _ hprojZ'
  have : IsProper (blowUp I ↘ Spec (.of ℂ)) := hprojZ'.isProper
  have hZsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hM.isResolution.2.2.1
  have hsm : Smooth (blowUp I ↘ Spec (.of ℂ)) := by
    rw [← hover]
    exact (MMP.Resolution.Bridges.smooth_blowUp_and_exceptionalDivisor_of_isSmoothBlowup
      (Z ↘ Spec (.of ℂ)) I ⟨hZsm, hIs⟩).1
  have hres : MMP.Intersection.IsResolution sY (blowUpToBase I ≫ r) := by
    refine ⟨hM.isResolution.1, ?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, hM.comp_eq]
      exact hvar'
    · rw [Category.assoc, hM.comp_eq, hover]
      exact (MMP.Mori.isSmoothScheme_iff _).2 hsm
    · have hYp : IsProjective sY := hY.isProjective.isProjective
      have hrp : IsProjective r := hM.isResolution.2.2.2.1.isProjective
      have : IsProper sY := hYp.isProper
      have : CompactSpace Y := (quasiCompact_iff_compactSpace sY).mp inferInstance
      have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated sY
      have hcomp' : IsProjective (blowUpToBase I ≫ r) := hprojq.comp hrp
      haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of ℂ))
      obtain ⟨L, _, hLa⟩ := exists_isAmple_of_isQuasiProjective sY _
        (Stacks.Ample.isAmple_unitModule_of_isAffine _) (isQuasiProjective_of_isProjective hYp)
      exact isProjectiveMorphism_of_isProjective _ L hLa hcomp'
    · have : IsIntegral (blowUp I) := hvar'.toIsIntegral
      have : IsIntegral Z := hvarZ.toIsIntegral
      have := hM.isNormal
      have := hM.isLocallyNoetherian
      have : IsProper r := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
      have : IsProper (blowUpToBase I) := hprojq.isProper
      exact MMP.Mori.isBirationalMorphism_comp_of_isBirational r (blowUpToBase I)
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hM.isResolution.2.2.2.2)
        hbir
  refine ⟨hcx, ?_, ?_, ?_, ?_, hres, hprojZ', ?_, ?_⟩
  · exact (quasiCompact_iff_compactSpace (blowUp I ↘ Spec (.of ℂ))).mp inferInstance
  · exact LocallyOfFiniteType.isLocallyNoetherian ((blowUp I) ↘ Spec (.of ℂ))
  · exact isNormal_of_smooth_over_field (blowUp I ↘ Spec (.of ℂ))
  · rw [Category.assoc, hM.comp_eq, hover]
  · have : IsIntegral (blowUp I) := hvar'.toIsIntegral
    have : IsIntegral Z := hvarZ.toIsIntegral
    have hu : (Set.univ : Set (blowUp I)) ∈ irreducibleComponents (blowUp I) :=
      ⟨IrreducibleSpace.isIrreducible_univ _, fun _ _ _ ↦ Set.subset_univ _⟩
    obtain ⟨D, hD, hDeq⟩ :=
      MMP.Resolution.exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp
        (Z ↘ Spec (.of ℂ)) I hu
    have hDu : D = Set.univ :=
      Set.eq_univ_of_univ_subset (hD.2 (IrreducibleSpace.isIrreducible_univ Z)
        (Set.subset_univ D))
    subst hDu
    rw [← (Homeomorph.Set.univ (blowUp I)).isHomeomorph.topologicalKrullDim_eq, hDeq,
      (Homeomorph.Set.univ Z).isHomeomorph.topologicalKrullDim_eq, hM.topologicalKrullDim_eq]
  · have : NoetherianSpace Z := noetherianSpace_of_isComplexScheme
    have := hM.isLocallyNoetherian
    obtain ⟨F, -, hFsnc, hFsupp⟩ := hM.exists_divisor
    rw [hM.comp_eq] at hFsnc
    have hD : MMP.Resolution.IsSNCClosedSubset (Z ↘ Spec (.of ℂ)) (exceptionalSet r : Set Z) := by
      have := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isSNCClosedSubset_of_isSNC _ hFsnc
      rwa [← coe_supp_eq_iUnion, hFsupp] at this
    have hD' := MMP.Resolution.isSNCClosedSubset_totalTransformStep (Z ↘ Spec (.of ℂ)) hZsm hD hIc
    rw [hover] at hD'
    have hT := MMP.Mori.isPureCodimOne_exceptionalSet_of_isQFactorial sY
      (blowUpToBase I ≫ (Z ↘ Spec (.of ℂ))) hYQ hvar' (blowUpToBase I ≫ r)
      (by rw [Category.assoc, hM.comp_eq]) hres.2.2.2.1 hres.2.2.2.2
    have : NoetherianSpace (blowUp I) := noetherianSpace_of_isComplexScheme
    have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((blowUp I) ↘ Spec (.of ℂ))
    have hreg : ∀ y : blowUp I, ∃ (n : ℕ) (z : Fin n → (blowUp I).presheaf.stalk y),
        MMP.Mori.IsRegularSystemOfParameters z := fun y => by
      have := isRegularLocalRing_stalk_of_smooth_over_field (blowUp I ↘ Spec (.of ℂ)) y
      exact MMP.Mori.exists_isRegularSystemOfParameters _
    have hsub : (exceptionalSet (blowUpToBase I ≫ r) : Set (blowUp I)) ⊆
        MMP.Resolution.ClosedBlowupSequence.totalTransformStep I (exceptionalSet r : Set Z) := by
      have hK := MMP.Resolution.isClosed_componentsOfCodimAtLeastTwo I.support.isClosed
      have : IsIntegral Z := hvarZ.toIsIntegral
      have hbir := isIso_blowUpToBase_restrict_complCodimTwo hIc (stalk_ne_bot_of_ne_bot hI)
      have : IsProper r := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
      refine (exceptionalSet_comp_subset _ r r.isClosedMap hK hbir).trans ?_
      rintro x (hx | hx)
      · by_cases hxC : blowUpToBase I x ∈ (I.support : Set Z)
        · exact Or.inr hxC
        · exact Or.inl (subset_closure ⟨hx, hxC⟩)
      · exact Or.inr (componentsOfCodimAtLeastTwo_subset (I.support : Set Z) hx)
    obtain ⟨F', hF'r, hF'snc, hF'supp⟩ := exists_divisor_of_subset _ hreg hD'
      (exceptionalSet (blowUpToBase I ≫ r)).isClosed hT hsub
    refine ⟨F', hF'r, ?_, hF'supp⟩
    rwa [Category.assoc, hM.comp_eq, hover]

/-- **One blow-up, geometry.** Blowing up a smooth centre having simple normal crossings with the
exceptional locus of a model gives an empty scheme (the centre is everything) or again a model. -/
private theorem isEmpty_or_isModel_blowUp {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYQ : IsQFactorial sY)
    (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))] :
    IsEmpty (blowUp I) ∨ IsModel sY (blowUpToBase I ≫ r) := by
  by_cases hI : I = ⊥
  · subst hI
    exact Or.inl (isEmpty_blowUp_bot Z)
  · exact Or.inr (isModel_blowUp sY hY hYQ r hM I hIs hIc hI)

/-- On a model, every surface point of a prime divisor `E` is the generic point of a prime
divisor of `E`: it has coheight one in the threefold `E`. -/
private theorem coheight_genericPoint_eq_one_of_isModel {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r)
    (E : Mori.PrimeDivisor Z) (v : E.idealSheaf.subscheme)
    (hv : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) v = 2) :
    Order.coheight v = 1 := by
  have := hM.isComplexScheme
  have hcomp := hM.comp_eq
  have hvar : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  have : IsIntegral Z := hvar.toIsIntegral
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := inferInstance
  -- `dim E = 3`
  let E' : Subvariety Z := ⟨E.idealSheaf, E.integral⟩
  have h1 := Subvariety.dim_add_codim ℂ E'
  rw [Subvariety.codim_eq_coheight_genericPoint,
    show E'.genericPoint = E.genericPoint from rfl, E.coheight_genericPoint] at h1
  change _ = topologicalKrullDim Z at h1
  rw [hM.topologicalKrullDim_eq] at h1
  haveI := E.integral
  have h2 := Subvariety.dim_add_codim ℂ (Subvariety.ofPoint v)
  rw [Subvariety.codim_eq_coheight_genericPoint, Subvariety.genericPoint_ofPoint] at h2
  have hV : (Subvariety.ofPoint v).dim = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [Subvariety.dim_eq_topologicalKrullDim_support, Subvariety.support_ofPoint]
    exact Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
      ℂ _ v 2 hv
  change topologicalKrullDim _ + _ = (4 : WithBot ℕ∞) at h1
  rw [hV] at h2
  change _ + _ = topologicalKrullDim _ at h2
  generalize Order.coheight v = c at h2 ⊢
  generalize topologicalKrullDim (E.idealSheaf.subscheme) = d at h1 h2
  induction d using WithBot.recBotCoe with
  | bot => simp at h1
  | coe d =>
    have h1' : d + 1 = 4 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h1)
    have h2' : 2 + c = d := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h2)
    induction d using ENat.recTopCoe with
    | top => simp at h1'
    | coe d =>
      induction c using ENat.recTopCoe with
      | top => simp at h2'
      | coe c =>
        have e1 : d + 1 = 4 := by exact_mod_cast h1'
        have e2 : 2 + c = d := by exact_mod_cast h2'
        exact_mod_cast (by omega : c = 1)

/-- On a model, a point of a component `E` whose closure has dimension at least two and which is
not a maximal point of `E` is the generic point of a prime divisor of `E`. -/
private theorem coheight_eq_one_of_two_le {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r)
    (E : Mori.PrimeDivisor Z) (x : E.idealSheaf.subscheme)
    (hx : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({x} : Set E.idealSheaf.subscheme)))
    (hne : ¬ IsMax x) :
    Order.coheight x = 1 := by
  have := hM.isComplexScheme
  have hvar : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  have : IsIntegral Z := hvar.toIsIntegral
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := inferInstance
  let E' : Subvariety Z := ⟨E.idealSheaf, E.integral⟩
  have h1 := Subvariety.dim_add_codim ℂ E'
  rw [Subvariety.codim_eq_coheight_genericPoint,
    show E'.genericPoint = E.genericPoint from rfl, E.coheight_genericPoint] at h1
  change _ = topologicalKrullDim Z at h1
  rw [hM.topologicalKrullDim_eq] at h1
  haveI := E.integral
  set V := Subvariety.ofPoint x
  have h2 := Subvariety.dim_add_codim ℂ V
  rw [Subvariety.codim_eq_coheight_genericPoint, Subvariety.genericPoint_ofPoint] at h2
  have hVd : V.dim = topologicalKrullDim (closure ({x} : Set E.idealSheaf.subscheme)) := by
    rw [Subvariety.dim_eq_topologicalKrullDim_support, Subvariety.support_ofPoint]
  rw [hVd] at h2
  have hc0 : Order.coheight x ≠ 0 := fun h0 => hne (Order.coheight_eq_zero.mp h0)
  change topologicalKrullDim _ + _ = (4 : WithBot ℕ∞) at h1
  change _ + _ = topologicalKrullDim E.idealSheaf.subscheme at h2
  revert hx hc0 h2
  generalize Order.coheight x = c
  generalize topologicalKrullDim (closure ({x} : Set E.idealSheaf.subscheme)) = e
  generalize topologicalKrullDim (E.idealSheaf.subscheme) = d at h1
  intro hx hc0 h2
  induction d using WithBot.recBotCoe with
  | bot => simp at h1
  | coe d =>
    induction e using WithBot.recBotCoe with
    | bot => simp at hx
    | coe e =>
      have h1' : d + 1 = 4 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h1)
      have h2' : e + c = d := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h2)
      have hx' : (2 : ℕ∞) ≤ e := WithBot.coe_le_coe.mp (by rw [WithBot.coe_ofNat]; exact hx)
      induction d using ENat.recTopCoe with
      | top => simp at h1'
      | coe d =>
        induction e using ENat.recTopCoe with
        | top => simp at h2'
        | coe e =>
          induction c using ENat.recTopCoe with
          | top => simp at h2'
          | coe c =>
            have e1 : d + 1 = 4 := by exact_mod_cast h1'
            have e2 : e + c = d := by exact_mod_cast h2'
            have e3 : 2 ≤ e := by exact_mod_cast hx'
            have e4 : c ≠ 0 := by exact_mod_cast hc0
            exact_mod_cast (by omega : c = 1)

/-- On a model, a prime divisor of a component `E` is a surface: `E` is a threefold. -/
private theorem topologicalKrullDim_closure_genericPoint_eq_two {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r)
    (E : Mori.PrimeDivisor Z) (P : Mori.PrimeDivisor E.idealSheaf.subscheme) :
    topologicalKrullDim (closure ({P.genericPoint} : Set E.idealSheaf.subscheme)) =
      ((2 : ℕ) : WithBot ℕ∞) := by
  have := hM.isComplexScheme
  have hvar : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  have : IsIntegral Z := hvar.toIsIntegral
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := inferInstance
  let E' : Subvariety Z := ⟨E.idealSheaf, E.integral⟩
  have h1 := Subvariety.dim_add_codim ℂ E'
  rw [Subvariety.codim_eq_coheight_genericPoint,
    show E'.genericPoint = E.genericPoint from rfl, E.coheight_genericPoint] at h1
  change _ = topologicalKrullDim Z at h1
  rw [hM.topologicalKrullDim_eq] at h1
  haveI := E.integral
  set V := Subvariety.ofPoint P.genericPoint
  have h2 := Subvariety.dim_add_codim ℂ V
  rw [Subvariety.codim_eq_coheight_genericPoint, Subvariety.genericPoint_ofPoint,
    P.coheight_genericPoint] at h2
  have hVd : V.dim =
      topologicalKrullDim (closure ({P.genericPoint} : Set E.idealSheaf.subscheme)) := by
    rw [Subvariety.dim_eq_topologicalKrullDim_support, Subvariety.support_ofPoint]
  rw [hVd] at h2
  change topologicalKrullDim _ + _ = (4 : WithBot ℕ∞) at h1
  change _ + _ = topologicalKrullDim E.idealSheaf.subscheme at h2
  revert h2
  generalize topologicalKrullDim (closure ({P.genericPoint} : Set E.idealSheaf.subscheme)) = e
  generalize topologicalKrullDim (E.idealSheaf.subscheme) = d at h1
  intro h2
  induction d using WithBot.recBotCoe with
  | bot => simp at h1
  | coe d =>
    induction e using WithBot.recBotCoe with
    | bot => simp at h2
    | coe e =>
      have h1' : d + 1 = 4 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h1)
      have h2' : e + 1 = d := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h2)
      induction d using ENat.recTopCoe with
      | top => simp at h1'
      | coe d =>
        induction e using ENat.recTopCoe with
        | top => simp at h2'
        | coe e =>
          have e1 : d + 1 = 4 := by exact_mod_cast h1'
          have e2 : e + 1 = d := by exact_mod_cast h2'
          rw [(by omega : e = 2)]; rfl

/-- A closed embedding preserves the dimensions of closures of points. -/
private theorem topologicalKrullDim_closure_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsClosedEmbedding f) (a : X) :
    topologicalKrullDim (closure ({f a} : Set Y)) = topologicalKrullDim (closure ({a} : Set X)) := by
  have hemb := hf.isEmbedding.comp
    (Topology.IsEmbedding.subtypeVal (p := (· ∈ closure ({a} : Set X))))
  have hrange : Set.range (f ∘ Subtype.val : closure ({a} : Set X) → Y) = closure {f a} := by
    rw [Set.range_comp, Subtype.range_coe, ← hf.closure_image_eq, Set.image_singleton]
  let e := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  exact e.isHomeomorph.topologicalKrullDim_eq.symm

/-- **The edge through `J`.** Let `E` be a new component whose image `C = q(E)` is a surface
mapping to dimension at most one in `Y`. Then `E` meets an old component `E''` along a double
surface `T` with `q(T) = C`, whose generic point is that of a prime divisor of `E`. -/
private theorem exists_doubleSurface_jEdge {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (E : F'.support) (hEN : E.1.support ⊆ blowUpToBase I ⁻¹'
      MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z))
    (hC2 : topologicalKrullDim ((blowUpToBase I).base '' E.1.support) = (2 : ℕ))
    (hrC : topologicalKrullDim (r.base '' ((blowUpToBase I).base '' E.1.support)) ≤ 1) :
    ∃ σ : DoubleSurface F', σ.fst = E.1 ∧ ¬ (σ.snd.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) ∧
      (∃ P : Mori.PrimeDivisor E.1.idealSheaf.subscheme,
        σ.carrier = closure {E.1.idealSheaf.subschemeι P.genericPoint}) ∧
      (blowUpToBase I).base '' σ.carrier = (blowUpToBase I).base '' E.1.support := by
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have hZsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hM.isResolution.2.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  have hvar' : AlgebraicGeometry.IsVariety ℂ (blowUp I ↘ Spec (.of ℂ)) :=
    hM'.comp_eq ▸ hM'.isResolution.2.1
  have hI : I ≠ ⊥ := ne_bot_of_blowUp E.1.genericPoint
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper (blowUpToBase I) := hqproj.isProper
  have hqc : IsClosedMap (blowUpToBase I).base := (blowUpToBase I).isClosedMap
  have hK : IsClosed K := MMP.Resolution.isClosed_componentsOfCodimAtLeastTwo I.support.isClosed
  have hne := stalk_ne_bot_of_ne_bot hI
  have hKcod : ∀ W : IrreducibleCloseds Z, (W : Set Z) ⊆ K → 2 ≤ codimension W :=
    fun W hW => two_le_codimension_of_subset I.support.isClosed W hW
  have hqs : Function.Surjective (blowUpToBase I) := surjective_blowUpToBase hIc hI hqc
  have : IsProper r := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
  obtain ⟨F, -, -, hFex⟩ := hM.exists_divisor
  obtain ⟨G, hGred, hGsnc, hGex⟩ := hM'.exists_divisor
  have hF'G : F' = G := eq_of_isReducedEffective_of_supp_eq hF'red hGred (hF'ex.trans hGex.symm)
  rw [← hF'G] at hGsnc
  have hKI : K ⊆ (I.support : Set Z) := componentsOfCodimAtLeastTwo_subset _
  have : NoetherianSpace (blowUp I) := noetherianSpace_of_isComplexScheme
  -- the surface `C`
  set C := (blowUpToBase I).base '' (E.1.support : Set (blowUp I)) with hCdef
  have hCcl : IsClosed C := hqc _ E.1.idealSheaf.support.isClosed
  have hEirr : IsIrreducible (E.1.support : Set (blowUp I)) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
  have hCirr : IsIrreducible C := hEirr.image _ (blowUpToBase I).continuous.continuousOn
  have hCK : C ⊆ K := by rintro _ ⟨x, hx, rfl⟩; exact hEN hx
  have hCex : C ⊆ exceptionalSet r :=
    subset_exceptionalSet_of_lt r ⟨C, hCirr, hCcl⟩ hC2 (hrC.trans_lt (by norm_num))
  have hCF : C ⊆ ⋃ P ∈ F.support, (P.support : Set Z) := by
    rw [← coe_supp_eq_iUnion, hFex]; exact hCex
  obtain ⟨P, hP, hCP⟩ := MMP.Fourfold.SNCWeight.PrimeDivisorUnion.exists_subset_of_isIrreducible
    (fun P _ => MMP.Fourfold.SNCWeight.PrimeDivisorUnion.isClosed_support P) hCirr hCF
  obtain ⟨E'', hE'', hE''old, hPE''⟩ :=
    exists_mem_support_subset_image (blowUpToBase I) hqs hqc r hFex hF'ex hK hKcod hP
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hCirr hCcl
  have hξC : ξ ∈ C := hξ.mem
  obtain ⟨y', hy'E'', hy'ξ⟩ := hPE'' (hCP hξC)
  haveI : Smooth (Z ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hZsm
  have hy'E : y' ∈ (E.1.support : Set (blowUp I)) :=
    preimage_subset_support_of_subset (Z ↘ Spec (.of ℂ)) I ⟨hZsm, hIs⟩ hne hIc hGsnc E.2 hCcl
      hCirr.isConnected (hCK.trans hKI) (fun x hx => ⟨x, hx, rfl⟩)
      (show (blowUpToBase I) y' ∈ C from hy'ξ ▸ hξC)
  have hEE'' : E.1 ≠ E'' := fun h => hE''old (h ▸ hEN)
  let σ : DoubleSurface F' := ⟨E.1, E'', E.2, hE'', hEE'',
    connectedComponentIn ((E.1.support : Set (blowUp I)) ∩ E''.support) y',
    ⟨y', ⟨hy'E, hy'E''⟩, rfl⟩⟩
  have hy'T : y' ∈ σ.carrier := mem_connectedComponentIn ⟨hy'E, hy'E''⟩
  refine ⟨σ, rfl, hE''old, ?_⟩
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((blowUp I) ↘ Spec (.of ℂ))
  have hTirr : IsIrreducible σ.carrier := isIrreducible_carrier _ hGsnc σ
  have hTsub : σ.carrier ⊆ (E.1.support : Set (blowUp I)) ∩ E''.support := σ.carrier_subset
  have hTcl : IsClosed σ.carrier := by
    have hsub : closure σ.carrier ⊆ σ.carrier :=
      hTirr.isConnected.isPreconnected.closure.subset_connectedComponentIn (subset_closure hy'T)
        (closure_minimal hTsub
          (E.1.idealSheaf.support.isClosed.inter E''.idealSheaf.support.isClosed))
    exact closure_subset_iff_isClosed.mp hsub
  have hTimg : (blowUpToBase I).base '' σ.carrier = C := by
    apply subset_antisymm
    · exact Set.image_mono (hTsub.trans Set.inter_subset_left)
    · rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.2 ⟨y', hy'T, hy'ξ⟩) (hqc _ hTcl)
  refine ⟨?_, hTimg⟩
  obtain ⟨g, hg⟩ := QuasiSober.sober hTirr hTcl
  have hgE : g ∈ Set.range E.1.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact (hTsub hg.mem).1
  obtain ⟨g', rfl⟩ := hgE
  set ιE := E.1.idealSheaf.subschemeι
  have himg : ιE '' closure ({g'} : Set E.1.idealSheaf.subscheme) = σ.carrier := by
    rw [← ιE.isClosedEmbedding.closure_image_eq, Set.image_singleton, hg.def]
  -- the dimension of `T` is at least two
  have hdimT : (2 : WithBot ℕ∞) ≤ topologicalKrullDim σ.carrier := by
    by_contra hlt
    push Not at hlt
    have hle : topologicalKrullDim σ.carrier ≤ ((1 : ℕ) : WithBot ℕ∞) := by
      rw [Nat.cast_one]; exact Order.le_of_lt_succ hlt
    have := Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le ℂ
      (blowUp I ↘ Spec (.of ℂ)) (Z ↘ Spec (.of ℂ)) (blowUpToBase I)
      (inferInstance : (blowUpToBase I).IsOver (Spec (.of ℂ))).comp_over σ.carrier hTcl 1 hle
      C hCcl hTimg.symm.le
    rw [hC2] at this
    exact absurd this (by norm_num)
  have hdimg : (2 : WithBot ℕ∞) ≤
      topologicalKrullDim (closure ({g'} : Set E.1.idealSheaf.subscheme)) := by
    rwa [← topologicalKrullDim_closure_image ιE.isClosedEmbedding, hg.def]
  haveI : IsIntegral E.1.idealSheaf.subscheme := E.1.integral
  have hmax : ¬ IsMax g' := by
    intro hmax
    have hgen : genericPoint E.1.idealSheaf.subscheme ∈ closure ({g'} : Set _) :=
      specializes_iff_mem_closure.1 (hmax (genericPoint_specializes g'))
    have huniv : closure ({g'} : Set E.1.idealSheaf.subscheme) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← (genericPoint_spec E.1.idealSheaf.subscheme).def]
      exact closure_minimal (Set.singleton_subset_iff.2 hgen) isClosed_closure
    have hEgen : E.1.genericPoint ∈ (E.1.support : Set (blowUp I)) := genericPoint_mem_support _
    have : E.1.genericPoint ∈ σ.carrier := by
      rw [← himg, huniv, Set.image_univ]
      change _ ∈ Set.range ιE
      rw [Scheme.IdealSheafData.range_subschemeι]
      exact hEgen
    exact hEE'' (eq_of_genericPoint_mem_support (hTsub this).2)
  have hcoh := coheight_eq_one_of_two_le sY (blowUpToBase I ≫ r) hM' E.1 g' hdimg hmax
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne g' hcoh, ?_⟩
  change σ.carrier = closure {ιE (AlgebraicGeometry.PrimeDivisor.genericPoint
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne g' hcoh))}
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
  exact hg.def.symm

/-- In an integral scheme of finite type over `ℂ` of finite dimension, the closure of a point has
dimension `dim X - coheight`. -/
private theorem topologicalKrullDim_closure_add_coheight {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) + (Order.coheight x : WithBot ℕ∞) =
      topologicalKrullDim X := by
  have h := Subvariety.dim_add_codim ℂ (Subvariety.ofPoint x)
  rw [Subvariety.codim_eq_coheight_genericPoint, Subvariety.genericPoint_ofPoint,
    Subvariety.dim_eq_topologicalKrullDim_support, Subvariety.support_ofPoint] at h
  exact h

/-- **Irreducible closed subsets of equal finite dimension, one inside the other, coincide.** -/
private theorem eq_of_subset_of_topologicalKrullDim_eq {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] {d : ℕ}
    (hX : topologicalKrullDim X = d) {W C : Set X} (hW : IsClosed W) (hWirr : IsIrreducible W)
    (hC : IsClosed C) (hCirr : IsIrreducible C) (hWC : W ⊆ C) {n : ℕ}
    (hWn : topologicalKrullDim W = n) (hCn : topologicalKrullDim C = n) : W = C := by
  obtain ⟨w, hw⟩ := QuasiSober.sober hWirr hW
  obtain ⟨c, hc⟩ := QuasiSober.sober hCirr hC
  have hw' := topologicalKrullDim_closure_add_coheight w
  have hc' := topologicalKrullDim_closure_add_coheight c
  rw [hw.def, hWn, hX] at hw'
  rw [hc.def, hCn, hX] at hc'
  have hle : w ≤ c := by
    rw [Scheme.le_iff_specializes, specializes_iff_mem_closure, hc.def]
    exact hWC hw.mem
  by_contra hne
  have hwc : w ≠ c := fun h => hne (by rw [← hw.def, ← hc.def, h])
  have hlt : w < c := lt_of_le_not_ge hle fun h => hwc
    (Specializes.antisymm (Scheme.le_iff_specializes.mp h) (Scheme.le_iff_specializes.mp hle)).eq
  have hstep := Order.coheight_add_one_le hlt
  revert hstep hw' hc'
  generalize Order.coheight w = a
  generalize Order.coheight c = b
  intro hw' hc' hstep
  induction a using ENat.recTopCoe with
  | top =>
    exfalso
    have h' : ((n : ℕ∞) + ⊤ : ℕ∞) = d := by exact_mod_cast hw'
    simp at h'
  | coe a =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((n : ℕ∞) + ⊤ : ℕ∞) = d := by exact_mod_cast hc'
      simp at h'
    | coe b =>
      have e1 : n + a = d := by exact_mod_cast hw'
      have e2 : n + b = d := by exact_mod_cast hc'
      have e3 : b + 1 ≤ a := by exact_mod_cast hstep
      omega

/-- A connected component of a closed set is closed. -/
private theorem isClosed_connectedComponentIn {T : Type*} [TopologicalSpace T] {F : Set T}
    (hF : IsClosed F) (x : T) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · have hsub : closure (connectedComponentIn F x) ⊆ connectedComponentIn F x :=
      isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hx))
        (closure_minimal (connectedComponentIn_subset F x) hF)
    exact closure_subset_iff_isClosed.mp hsub
  · rw [connectedComponentIn_eq_empty hx]; exact isClosed_empty

/-- In an integral fourfold of finite type over `ℂ`, a prime divisor is a threefold. -/
private theorem topologicalKrullDim_support_eq_three {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsIntegral X] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] (hX : topologicalKrullDim X = 4)
    (E : Mori.PrimeDivisor X) :
    topologicalKrullDim (E.support : Set X) = ((3 : ℕ) : WithBot ℕ∞) := by
  have h := topologicalKrullDim_closure_add_coheight E.genericPoint
  rw [E.coheight_genericPoint, hX] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  revert h
  generalize topologicalKrullDim (closure ({E.genericPoint} : Set X)) = e
  intro h
  induction e using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    have h' : e + 1 = 4 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe e =>
      have : e + 1 = 4 := by exact_mod_cast h'
      rw [(by omega : e = 3)]; rfl

/-- **A new component through every point over the codimension-`≥ 2` part of the centre.**
Every point `y` of the blow-up over the codimension-`≥ 2` part `K` of a smooth centre lies on a
component `J` of the full exceptional divisor of `q ≫ r` lying over the connected component of the
centre through `q(y)`, and that connected component lies in `K`. -/
private theorem exists_new_component {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    (F' : Divisor (blowUp I))
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    {y : blowUp I} (hy : blowUpToBase I y ∈
      MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) :
    ∃ J ∈ F'.support, (J.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹'
        connectedComponentIn (I.support : Set Z) (blowUpToBase I y) ∧ y ∈ J.support ∧
      connectedComponentIn (I.support : Set Z) (blowUpToBase I y) ⊆
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) := by
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  have hvar' : AlgebraicGeometry.IsVariety ℂ (blowUp I ↘ Spec (.of ℂ)) :=
    hM'.comp_eq ▸ hM'.isResolution.2.1
  have : IsIntegral (blowUp I) := hvar'.toIsIntegral
  have hI : I ≠ ⊥ := ne_bot_of_blowUp y
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper (blowUpToBase I) := hqproj.isProper
  have hqc : IsClosedMap (blowUpToBase I).base := (blowUpToBase I).isClosedMap
  have hqs : Function.Surjective (blowUpToBase I) := surjective_blowUpToBase hIc hI hqc
  have : IsProper r := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((blowUp I) ↘ Spec (.of ℂ))
  have hKI : K ⊆ (I.support : Set Z) := componentsOfCodimAtLeastTwo_subset _
  have hmemI : ∀ x : blowUp I, x ∈ ((exceptionalIdeal I).support : Set (blowUp I)) →
      blowUpToBase I x ∈ (I.support : Set Z) := by
    intro x hx
    change x ∈ ((I.comap (blowUpToBase I)).support : Set (blowUp I)) at hx
    rw [Scheme.IdealSheafData.support_comap] at hx
    exact hx
  have hyI : y ∈ ((exceptionalIdeal I).support : Set (blowUp I)) := by
    change y ∈ ((I.comap (blowUpToBase I)).support : Set (blowUp I))
    rw [Scheme.IdealSheafData.support_comap]
    exact hKI hy
  obtain ⟨G, hyG, hGsub⟩ := exists_primeDivisor_mem_of_mem_support I hyI
  set C₀ := connectedComponentIn (I.support : Set Z) (blowUpToBase I y) with hC₀def
  have hsmI : Smooth (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))) := (MMP.Mori.isSmoothScheme_iff _).1 hIs
  have : IsNormal I.subscheme := isNormal_of_smooth_over_field (I.subschemeι ≫ (Z ↘ Spec (.of ℂ)))
  have : IsLocallyNoetherian I.subscheme := isLocallyNoetherian_of_isClosedImmersion I.subschemeι
  have : NoetherianSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.noetherianSpace
  have hC₀irr := isIrreducible_connectedComponentIn_support I (hKI hy)
  have hC₀cl : IsClosed C₀ := isClosed_connectedComponentIn I.support.isClosed _
  have hC₀K : C₀ ⊆ K := by
    obtain ⟨W, hx⟩ := Set.mem_iUnion.1 hy
    obtain ⟨hW, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨h2, hyW⟩ := Set.mem_iUnion.1 hx
    have hWirr : IsIrreducible W := hW.1.1
    have hWC : W ⊆ C₀ := hWirr.isConnected.isPreconnected.subset_connectedComponentIn hyW hW.1.2
    have hCW : C₀ ⊆ W := hW.2 ⟨hC₀irr, connectedComponentIn_subset _ _⟩ hWC
    intro z hz
    exact Set.mem_iUnion.2 ⟨W, Set.mem_iUnion.2 ⟨hW, Set.mem_iUnion.2 ⟨h2, hCW hz⟩⟩⟩
  have hGirr : IsIrreducible (G.support : Set (blowUp I)) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
  have hqG : (blowUpToBase I).base '' (G.support : Set (blowUp I)) ⊆ C₀ :=
    (hGirr.image _ (blowUpToBase I).continuous.continuousOn).isConnected.isPreconnected.subset_connectedComponentIn
      ⟨y, hyG, rfl⟩ (by rintro _ ⟨x, hx, rfl⟩; exact hmemI x (hGsub hx))
  have hdimC₀ : topologicalKrullDim C₀ ≤ ((4 - 2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_le_sub_of_le_codimension (c := 2) (n := 4) hC₀cl
      (by rw [hM.topologicalKrullDim_eq]; rfl)
      (fun W hW => by
        have := two_le_codimension_of_subset I.support.isClosed W (Set.Subset.trans hW hC₀K)
        exact_mod_cast this)
  have hdimqG : topologicalKrullDim ((blowUpToBase I).base '' (G.support : Set (blowUp I))) <
      ((3 : ℕ) : WithBot ℕ∞) :=
    lt_of_le_of_lt (((Topology.IsEmbedding.inclusion hqG).isInducing.topologicalKrullDim_le).trans
      hdimC₀) (by norm_num)
  have hG3 := topologicalKrullDim_support_eq_three hM'.topologicalKrullDim_eq G
  have hGex : (G.support : Set (blowUp I)) ⊆ exceptionalSet (blowUpToBase I) :=
    subset_exceptionalSet_of_lt (blowUpToBase I)
      ⟨G.support, hGirr, G.idealSheaf.support.isClosed⟩ hG3 hdimqG
  have hη : G.genericPoint ∈ (F'.supp : Set (blowUp I)) := by
    rw [hF'ex]
    refine exceptionalSet_subset_comp _ hqs r (hGex ?_)
    exact genericPoint_mem_support _
  obtain ⟨J, hJ, hηJ⟩ := DivisorWithCoeffs.mem_supp_iff.mp hη
  have hGJ := eq_of_genericPoint_mem_support hηJ
  subst hGJ
  exact ⟨G, Finsupp.mem_support_iff.2 hJ, fun x hx => hqG ⟨x, hx, rfl⟩, hyG, hC₀K⟩

private theorem withBot_le_of_lt_succ {e : WithBot ℕ∞} {n : ℕ}
    (h : e < ((n + 1 : ℕ) : WithBot ℕ∞)) : e ≤ (n : WithBot ℕ∞) :=
  ENat.WithBot.lt_add_one_iff.1 (by exact_mod_cast h)

/-- **The push-forward of the surface of a prime divisor of a component.** If `P` is a surface
in the component `E` whose image `w = q(ξ_P)` is a surface point, then `q_* ι_* [P]` is
`deg(ξ_P / w) [w]`. -/
private theorem rationalPushforward_divisorCycle_single {X Z : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    (q : X ⟶ Z) [q.IsOver (Spec (.of ℂ))] [IsProper q] (E : Mori.PrimeDivisor X)
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2)
    (hW : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Z ↘ Spec (.of ℂ)) (q.base (E.idealSheaf.subschemeι.base P.genericPoint)) =
        ((2 : ℕ) : ℤ)) :
    Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((2 : ℕ) : ℤ) q (comp_over q _)
        (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((2 : ℕ) : ℤ)
          E.idealSheaf.subschemeι (comp_over _ _)
          (Chow.divisorCycle _ (Finsupp.single P 1))) =
      (q.residueDegree (E.idealSheaf.subschemeι.base P.genericPoint) : ℚ) •
        Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ)
          (q.base (E.idealSheaf.subschemeι.base P.genericPoint)) hW := by
  have hι : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) (E.idealSheaf.subschemeι.base P.genericPoint) = ((2 : ℕ) : ℤ) := by
    rw [relativeDimension_map_of_isClosedImmersion]
    exact hP
  rw [Chow.divisorCycle_single, one_smul, primeDivisorCycle_eq_rationalPointCycle P rfl hP,
    rationalProperPushforward_rationalPointCycle, dif_pos hι,
    Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion, Nat.cast_one, one_smul,
    rationalProperPushforward_rationalPointCycle, dif_pos hW]

/-- On a model, a surface through a point of a component `E` is a prime divisor of `E`. -/
private theorem exists_primeDivisor_genericPoint_eq {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    (sY : Y ⟶ Spec (.of ℂ)) (r : X ⟶ Y) (hM : IsModel sY r) (E : Mori.PrimeDivisor X) {y : X}
    (hy : y ∈ E.support)
    (h2 : topologicalKrullDim (closure ({y} : Set X)) = ((2 : ℕ) : WithBot ℕ∞)) :
    ∃ P : Mori.PrimeDivisor E.idealSheaf.subscheme, E.idealSheaf.subschemeι P.genericPoint = y := by
  have := hM.isComplexScheme
  have hvar : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  have : IsIntegral X := hvar.toIsIntegral
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := inferInstance
  obtain ⟨g', rfl⟩ : y ∈ Set.range E.idealSheaf.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hy
  set ιE := E.idealSheaf.subschemeι
  have hdimg : topologicalKrullDim (closure ({g'} : Set E.idealSheaf.subscheme)) =
      ((2 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_closure_image ιE.isClosedEmbedding g').symm.trans h2
  haveI : IsIntegral E.idealSheaf.subscheme := E.integral
  have hmax : ¬ IsMax g' := by
    intro hmax
    have hgen : genericPoint E.idealSheaf.subscheme ∈ closure ({g'} : Set _) :=
      specializes_iff_mem_closure.1 (hmax (genericPoint_specializes g'))
    have huniv : closure ({g'} : Set E.idealSheaf.subscheme) = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← (genericPoint_spec E.idealSheaf.subscheme).def]
      exact closure_minimal (Set.singleton_subset_iff.2 hgen) isClosed_closure
    have hcl : closure ({ιE g'} : Set X) = E.support := by
      rw [← Set.image_singleton, ιE.isClosedEmbedding.closure_image_eq, huniv, Set.image_univ,
        Scheme.IdealSheafData.range_subschemeι]
    rw [hcl, topologicalKrullDim_support_eq_three hM.topologicalKrullDim_eq E] at h2
    exact absurd h2 (by norm_num)
  have hcoh := coheight_eq_one_of_two_le sY r hM E g' (by rw [hdimg]; norm_num) hmax
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne g' hcoh, ?_⟩
  change ιE (AlgebraicGeometry.PrimeDivisor.genericPoint
    (AlgebraicGeometry.PrimeDivisor.ofCoheightOne g' hcoh)) = ιE g'
  rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]

/-- **A double surface through a surface point.** On a model, if `y` lies on two distinct
components `E₁`, `E₂` of the full exceptional divisor and its closure has dimension at least two,
the closure of `y` is a double surface of `(E₁, E₂)`. -/
private theorem exists_doubleSurface_of_mem {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [IsLocallyNoetherian X] [NoetherianSpace X] (sY : Y ⟶ Spec (.of ℂ)) (r : X ⟶ Y)
    (hM : IsModel sY r) (F : Divisor X) (hFred : MMP.Intersection.IsReducedEffective F)
    (hFex : (F.supp : Set X) = exceptionalSet r) {E₁ E₂ : Mori.PrimeDivisor X}
    (h₁ : E₁ ∈ F.support) (h₂ : E₂ ∈ F.support) (hne : E₁ ≠ E₂) {y : X}
    (hy₁ : y ∈ E₁.support) (hy₂ : y ∈ E₂.support)
    (hy : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({y} : Set X))) :
    ∃ σ : DoubleSurface F, σ.fst = E₁ ∧ σ.snd = E₂ ∧ σ.carrier = closure {y} ∧
      topologicalKrullDim (closure ({y} : Set X)) = ((2 : ℕ) : WithBot ℕ∞) := by
  have := hM.isComplexScheme
  have hvar : AlgebraicGeometry.IsVariety ℂ (r ≫ sY) := hM.isResolution.2.1
  have : IsIntegral X := hvar.toIsIntegral
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := inferInstance
  obtain ⟨G, hGred, hGsnc, hGex⟩ := hM.exists_divisor
  have hFG : F = G := eq_of_isReducedEffective_of_supp_eq hFred hGred (hFex.trans hGex.symm)
  rw [← hFG] at hGsnc
  let σ : DoubleSurface F := ⟨E₁, E₂, h₁, h₂, hne,
    connectedComponentIn ((E₁.support : Set X) ∩ E₂.support) y, ⟨y, ⟨hy₁, hy₂⟩, rfl⟩⟩
  have hTirr : IsIrreducible σ.carrier := isIrreducible_carrier _ hGsnc σ
  have hTcl : IsClosed σ.carrier := isClosed_connectedComponentIn
    (E₁.idealSheaf.support.isClosed.inter E₂.idealSheaf.support.isClosed) y
  have hyT : closure {y} ⊆ σ.carrier :=
    closure_minimal (Set.singleton_subset_iff.2 (mem_connectedComponentIn ⟨hy₁, hy₂⟩)) hTcl
  have hTE : σ.carrier ⊆ (E₁.support : Set X) := σ.carrier_subset.trans Set.inter_subset_left
  have hE₁irr : IsIrreducible (E₁.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
  have hTne : σ.carrier ≠ (E₁.support : Set X) := by
    intro h
    have hg : E₁.genericPoint ∈ σ.carrier := by
      rw [h]
      exact genericPoint_mem_support _
    exact hne (eq_of_genericPoint_mem_support (σ.carrier_subset hg).2)
  have hE3 := topologicalKrullDim_support_eq_three hM.topologicalKrullDim_eq E₁
  have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hE₁irr hTcl hTE hTne
    (by rw [hE3]; simp; decide)
  rw [hE3] at hlt
  have hle : topologicalKrullDim σ.carrier ≤ ((2 : ℕ) : WithBot ℕ∞) :=
    withBot_le_of_lt_succ (n := 2) hlt
  have hcy : topologicalKrullDim (closure ({y} : Set X)) ≤ topologicalKrullDim σ.carrier :=
    (Topology.IsEmbedding.inclusion hyT).isInducing.topologicalKrullDim_le
  have h2 : topologicalKrullDim (closure ({y} : Set X)) = ((2 : ℕ) : WithBot ℕ∞) :=
    le_antisymm (hcy.trans hle) (by exact_mod_cast hy)
  have hT2 : topologicalKrullDim σ.carrier = ((2 : ℕ) : WithBot ℕ∞) :=
    le_antisymm hle (h2 ▸ hcy)
  have heq := eq_of_subset_of_topologicalKrullDim_eq (d := 4)
    (by rw [hM.topologicalKrullDim_eq]; rfl) isClosed_closure isIrreducible_singleton.closure
    hTcl hTirr hyT h2 hT2
  exact ⟨σ, rfl, rfl, heq.symm, h2⟩

/-- **The image of an old component.** If `q` is biregular off a closed set `K`, a component
`E` of the full exceptional divisor of `q ≫ r` not lying over `K` maps onto a component of the
full exceptional divisor of `r`. -/
private theorem exists_image_eq_of_not_subset {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z)
    (hqc : IsClosedMap q.base) (r : Z ⟶ Y) (hrc : IsClosedMap r.base) {K : Set Z}
    (hK : IsClosed K) (hq : IsBiregular q ⟨Kᶜ, hK.isOpen_compl⟩) {F : Divisor Z}
    (hF : (F.supp : Set Z) = exceptionalSet r) {F' : Divisor Z'}
    (hF' : (F'.supp : Set Z') = exceptionalSet (q ≫ r)) {E : Mori.PrimeDivisor Z'}
    (hE : E ∈ F'.support) (hEK : ¬ ((E.support : Set Z') ⊆ q ⁻¹' K)) :
    ∃ P ∈ F.support, q.base '' (E.support : Set Z') = P.support := by
  have hηE : E.genericPoint ∈ (E.support : Set Z') := genericPoint_mem_support _
  have hηK : q E.genericPoint ∉ K := by
    intro h
    apply hEK
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.2 h) (hK.preimage q.continuous)
  have hηex : E.genericPoint ∈ (exceptionalSet (q ≫ r) : Set Z') := by
    rw [← hF', SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff]
    exact ⟨E, Finsupp.mem_support_iff.1 hE, hηE⟩
  have hηr : q E.genericPoint ∈ (exceptionalSet r : Set Z) := by
    rcases exceptionalSet_comp_subset q r hrc hK hq hηex with h | h
    · exact h
    · exact absurd h hηK
  have hbir : q E.genericPoint ∈ biregularLocus q := le_biregularLocus hq hηK
  have hcoh : Order.coheight (q E.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus q hbir, E.coheight_genericPoint]
  rw [← hF, SetLike.mem_coe, DivisorWithCoeffs.mem_supp_iff] at hηr
  obtain ⟨P, hP, hηP⟩ := hηr
  have hPeq : AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh = P := by
    apply eq_of_genericPoint_mem_support
    change AlgebraicGeometry.PrimeDivisor.genericPoint
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh) ∈ (P.support : Set Z)
    rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
    exact hηP
  have hPgen : AlgebraicGeometry.PrimeDivisor.genericPoint P = q E.genericPoint := by
    rw [← hPeq]; exact AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨P, Finsupp.mem_support_iff.2 hP, ?_⟩
  conv_rhs => rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, hPgen]
  conv_lhs => rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  rw [← hqc.closure_image_eq_of_continuous q.continuous, Set.image_singleton]

/-- **Old components are determined by their images.** -/
private theorem eq_of_image_eq_of_not_subset {Z' Z : Scheme.{0}} (q : Z' ⟶ Z)
    (hqc : IsClosedMap q.base) {K : Set Z} (hK : IsClosed K)
    (hq : IsBiregular q ⟨Kᶜ, hK.isOpen_compl⟩) {E₁ E₂ : Mori.PrimeDivisor Z'}
    (hE₁ : ¬ ((E₁.support : Set Z') ⊆ q ⁻¹' K))
    (h : q.base '' (E₁.support : Set Z') = q.base '' E₂.support) : E₁ = E₂ := by
  have hηK : q E₁.genericPoint ∉ K := by
    intro h'
    apply hE₁
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.2 h') (hK.preimage q.continuous)
  have hcl' : ∀ E : Mori.PrimeDivisor Z',
      closure ({q E.genericPoint} : Set Z) = q.base '' (E.support : Set Z') := by
    intro E
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← hqc.closure_image_eq_of_continuous q.continuous, Set.image_singleton]
  have hcl : closure ({q E₁.genericPoint} : Set Z) = closure {q E₂.genericPoint} := by
    rw [hcl', hcl', h]
  have heq : q E₁.genericPoint = q E₂.genericPoint := (inseparable_iff_closure_eq.2 hcl).eq
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (eq_of_isBiregular hq hηK heq)

/-- Double surfaces are closed. -/
private theorem isClosed_carrier {X : Scheme.{0}} {B : Divisor X} (σ : DoubleSurface B) :
    IsClosed σ.carrier := by
  obtain ⟨x, -, hx⟩ := σ.isComponent
  rw [← hx]
  exact isClosed_connectedComponentIn
    (σ.fst.idealSheaf.support.isClosed.inter σ.snd.idealSheaf.support.isClosed) x

/-- Systems vertical for `q` are vertical for `q ≫ r`. -/
private theorem verticalSurfaceCoefficients_le_comp {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z)
    (r : Z ⟶ Y) (hqc : IsClosedMap q.base) (hrc : IsClosedMap r.base)
    (sZ : Z ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsVariety ℂ sZ]
    [AlgebraicGeometry.IsVariety ℂ sY] (hr : r ≫ sY = sZ) (F' : Divisor Z') :
    verticalSurfaceCoefficients q F' ≤ verticalSurfaceCoefficients (q ≫ r) F' := by
  rintro a ⟨ha, hv⟩
  refine ⟨ha, fun σ hσ => ?_⟩
  have h1 := hv σ hσ
  have hT : IsClosed (q.base '' σ.carrier) := hqc _ (isClosed_carrier σ)
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp]
  have := Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le ℂ sZ sY r hr
    (q.base '' σ.carrier) hT 1 (by exact_mod_cast h1) (r.base '' (q.base '' σ.carrier))
    (hrc _ hT) le_rfl
  exact_mod_cast this

/-- **A push-forward to a surface image is a multiple of that surface.** If the image of a prime
divisor `E` has dimension at most two, a nonzero push-forward of a rational surface cycle on `E`
is a multiple of the prime cycle `[w₀]` of the generic point of the surface `f(E)`. -/
private theorem exists_eq_smul_single_of_ne_zero {Z' X : Scheme.{0}} [Z'.Over (Spec (.of ℂ))]
    [IsComplexScheme Z'] [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [IsIntegral X] {d : ℕ}
    (hX : topologicalKrullDim X = d) (f : Z' ⟶ X) [f.IsOver (Spec (.of ℂ))] [IsProper f]
    (hfc : IsClosedMap f.base)
    (E : Mori.PrimeDivisor Z') (hCdim : topologicalKrullDim (f.base '' E.support) ≤ (2 : ℕ))
    (L : Chow.RationalCycleGroup (Stacks.Chow.fieldChowSituation ℂ)
      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ))
    (hc : Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((2 : ℕ) : ℤ)
      (E.idealSheaf.subschemeι ≫ f) (comp_over _ _) L ≠ 0) :
    ∃ (w₀ : X) (hw₀ : Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) w₀ = 2),
      closure {w₀} = f.base '' E.support ∧ ∃ t : ℚ, t ≠ 0 ∧
        Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((2 : ℕ) : ℤ)
          (E.idealSheaf.subschemeι ≫ f) (comp_over _ _) L =
          t • Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ)
            w₀ hw₀ := by
  classical
  set g := E.idealSheaf.subschemeι ≫ f
  set N := Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((2 : ℕ) : ℤ) g
    (comp_over g _) L with hN
  set C := f.base '' (E.support : Set Z')
  have hCcl : IsClosed C := hfc _ E.idealSheaf.support.isClosed
  have hEirr : IsIrreducible (E.support : Set Z') := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
  have hCirr : IsIrreducible C := hEirr.image _ f.continuous.continuousOn
  -- every point in the support of `g_* L` is the generic point of `C`, of delta-dimension two
  have hsupp : ∀ y : X, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ)
      (X ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) y N ≠ 0 →
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) y = 2 ∧ closure {y} = C := by
    intro y hy
    have hy2 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (X ↘ Spec (.of ℂ)) y = 2 := by
      by_contra h
      exact hy (rationalCoeff_eq_zero_of_relativeDimension_ne _ y h)
    have hyC : y ∈ C := by
      by_contra h
      refine hy (rationalCoeff_rationalProperPushforward_eq_zero_of_notMem g 2 L y ?_)
      rintro ⟨x, rfl⟩
      refine h ⟨E.idealSheaf.subschemeι x, ?_, rfl⟩
      change _ ∈ (E.idealSheaf.support : Set Z')
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    have hsub : closure ({y} : Set X) ⊆ C :=
      closure_minimal (Set.singleton_subset_iff.2 hyC) hCcl
    have hW2 : topologicalKrullDim (closure ({y} : Set X)) = ((2 : ℕ) : WithBot ℕ∞) :=
      Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
        ℂ _ y 2 hy2
    have hC2 : topologicalKrullDim C = ((2 : ℕ) : WithBot ℕ∞) := by
      refine le_antisymm hCdim ?_
      rw [← hW2]
      exact (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    exact ⟨hy2, eq_of_subset_of_topologicalKrullDim_eq hX isClosed_closure
      isIrreducible_singleton.closure hCcl hCirr hsub hW2 hC2⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : X, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ)
      (X ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) w₀ N ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (rationalCycle_ext fun y => by rw [h y, map_zero])
  obtain ⟨hw₂, hwC⟩ := hsupp w₀ hw₀
  refine ⟨w₀, hw₂, hwC, _, hw₀, rationalCycle_ext fun y => ?_⟩
  rw [map_smul, Chow.rationalCoeff_rationalPointCycle, smul_eq_mul]
  by_cases hy : y = w₀
  · subst hy; rw [if_pos rfl, mul_one]
  · rw [if_neg hy, mul_zero]
    by_contra h
    exact hy ((inseparable_iff_closure_eq.2 ((hsupp y h).2.trans hwC.symm)).eq)

section Edge

variable {X : Scheme.{0}} {B : Divisor X}

open Classical in
/-- The oriented system of one edge: `t` on `σ`, `-t` on `σ.swap`, zero elsewhere. -/
private noncomputable def edgeSystem (σ : DoubleSurface B) (t : ℚ) : DoubleSurface B → ℚ :=
  fun τ => if τ = σ then t else if τ = σ.swap then -t else 0

private theorem swap_ne (σ : DoubleSurface B) : σ.swap ≠ σ := fun h =>
  σ.fst_ne_snd (congrArg DoubleSurface.fst h).symm

private theorem edgeSystem_mem_vertical {Y : Scheme.{0}} (f : X ⟶ Y) (σ : DoubleSurface B)
    (t : ℚ) (hσ : topologicalKrullDim (f.base '' σ.carrier) ≤ 1) :
    edgeSystem σ t ∈ verticalSurfaceCoefficients f B := by
  classical
  refine ⟨fun τ => ?_, fun τ hτ => ?_⟩
  · unfold edgeSystem
    by_cases h1 : τ = σ
    · subst h1
      rw [if_neg (swap_ne τ), if_pos rfl, if_pos rfl]
    · by_cases h2 : τ = σ.swap
      · subst h2
        rw [DoubleSurface.swap_swap, if_pos rfl, if_neg (swap_ne σ), if_pos rfl, neg_neg]
      · rw [if_neg h1, if_neg h2, if_neg (fun h => h2 (by rw [← h, DoubleSurface.swap_swap])),
          if_neg (fun h => h1 (by rw [← DoubleSurface.swap_swap τ, h, DoubleSurface.swap_swap])),
          neg_zero]
  · unfold edgeSystem at hτ
    by_cases h1 : τ = σ
    · subst h1; exact hσ
    · by_cases h2 : τ = σ.swap
      · subst h2; exact hσ
      · rw [if_neg h1, if_neg h2] at hτ; exact absurd rfl hτ

private theorem surfaceCoefficientDivisor_edgeSystem_of_ne [NoetherianSpace X]
    (σ : DoubleSurface B) (t : ℚ) {E : Mori.PrimeDivisor X} (h1 : E ≠ σ.fst) (h2 : E ≠ σ.snd) :
    surfaceCoefficientDivisor (edgeSystem σ t) E = 0 := by
  classical
  refine Finsupp.ext fun P => ?_
  change (surfaceCoefficientDivisor (edgeSystem σ t) E).coeff P = 0
  rw [coeff_surfaceCoefficientDivisor, surfaceCoefficientCoeff]
  refine finsum_eq_zero_of_forall_eq_zero fun τ => ?_
  unfold edgeSystem
  rw [if_neg (fun h => h1 (τ.2.1.symm.trans (by rw [h]))),
    if_neg (fun h => h2 (τ.2.1.symm.trans (by rw [h]; rfl)))]

private theorem surfaceCoefficientDivisor_edgeSystem_fst [NoetherianSpace X]
    (σ : DoubleSurface B) (t : ℚ) (P : Mori.PrimeDivisor σ.fst.idealSheaf.subscheme)
    (hP : σ.carrier = closure {σ.fst.idealSheaf.subschemeι P.genericPoint}) :
    surfaceCoefficientDivisor (edgeSystem σ t) σ.fst = Finsupp.single P t := by
  classical
  refine Finsupp.ext fun P' => ?_
  change (surfaceCoefficientDivisor (edgeSystem σ t) σ.fst).coeff P' = _
  rw [coeff_surfaceCoefficientDivisor, surfaceCoefficientCoeff, Finsupp.single_apply]
  have hval : ∀ τ : {τ : DoubleSurface B // τ.fst = σ.fst ∧
      τ.carrier = closure {σ.fst.idealSheaf.subschemeι P'.genericPoint}},
      edgeSystem σ t τ = if τ.1 = σ then t else 0 := by
    intro τ
    unfold edgeSystem
    split_ifs with h h'
    · rfl
    · have : σ.snd = σ.fst := by rw [← DoubleSurface.swap_fst σ, ← h', τ.2.1]
      exact absurd this σ.fst_ne_snd.symm
    · rfl
  simp_rw [hval]
  by_cases hPP : P = P'
  · subst hPP
    rw [if_pos rfl, finsum_eq_single _ ⟨σ, rfl, hP⟩ (fun τ hτ => by
      rw [if_neg (fun h => hτ (Subtype.ext h))])]
    rw [if_pos rfl]
  · rw [if_neg hPP]
    refine finsum_eq_zero_of_forall_eq_zero ?_
    rintro ⟨τ, hτ1, hτ2⟩
    rw [if_neg]
    intro hτσ
    apply hPP
    change τ = σ at hτσ
    have hcl : closure {σ.fst.idealSheaf.subschemeι P.genericPoint} =
        closure {σ.fst.idealSheaf.subschemeι P'.genericPoint} := by
      rw [← hP, ← hτ2, hτσ]
    have hins := (inseparable_iff_closure_eq.2 hcl).eq
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (σ.fst.idealSheaf.subschemeι.isClosedEmbedding.injective hins)

private theorem surfaceCoefficientDivisor_edgeSystem_of_eq [NoetherianSpace X]
    (σ : DoubleSurface B) (t : ℚ) {E : Mori.PrimeDivisor X} (hE : σ.fst = E)
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP : σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}) :
    surfaceCoefficientDivisor (edgeSystem σ t) E = Finsupp.single P t := by
  subst hE
  exact surfaceCoefficientDivisor_edgeSystem_fst σ t P hP

private theorem edgeSystem_swap (σ : DoubleSurface B) (t : ℚ) :
    edgeSystem σ.swap t = edgeSystem σ (-t) := by
  classical
  funext τ
  unfold edgeSystem
  rw [DoubleSurface.swap_swap]
  by_cases h1 : τ = σ.swap
  · subst h1
    simp [swap_ne σ]
  · by_cases h2 : τ = σ
    · subst h2
      simp [h1]
    · simp [h1, h2]

private theorem surfaceCoefficientDivisor_edgeSystem_of_snd_eq [NoetherianSpace X]
    (σ : DoubleSurface B) (t : ℚ) {E : Mori.PrimeDivisor X} (hE : σ.snd = E)
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP : σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}) :
    surfaceCoefficientDivisor (edgeSystem σ t) E = Finsupp.single P (-t) := by
  have h := surfaceCoefficientDivisor_edgeSystem_of_eq σ.swap (-t) hE P hP
  rwa [edgeSystem_swap, neg_neg] at h

end Edge

/-- **The ambient cycles of an oriented system cancel**: `∑ᵢ (ιᵢ)_* Zᵢ(a) = 0` as a rational
surface cycle on a model. -/
private theorem sum_rationalPushforward_divisorCycle_eq_zero {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y)
    (hM : IsModel sY r) (F : Divisor Z) (a : DoubleSurface F → ℚ)
    (ha : a ∈ orientedSurfaceCoefficients F) :
    ∑ E : F.support, Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((2 : ℕ) : ℤ)
      E.1.idealSheaf.subschemeι (comp_over _ _)
      (Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1)) = 0 := by
  refine rationalCycle_ext fun w => ?_
  rw [map_sum, map_zero]
  by_cases hw : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Z ↘ Spec (.of ℂ)) w = 2
  · simp_rw [rationalCoeff_rationalProperPushforward_divisorCycle a _
      (coheight_genericPoint_eq_one_of_isModel sY r hM _) w hw]
    exact sum_finsum_doubleSurface_eq_zero F a ha _
  · exact Finset.sum_eq_zero fun E _ => rationalCoeff_eq_zero_of_relativeDimension_ne _ w hw

/-- **Oriented systems have vanishing ambient class** (`B(r) ⊆ K(r)` before intersecting with
the component classes): for an oriented surface coefficient system `a` of the full exceptional
divisor of a model, `∑ᵢ (ιᵢ)_* [Zᵢ(a)] = 0` in `H_4(Z, ℚ)`, each double surface being counted
once from each of its two components with opposite signs. -/
private theorem sum_componentHomologyMap_divisorClass_eq_zero {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r)
    [IsComplexScheme Z] (F : Divisor Z)
    (a : DoubleSurface F → ℚ) (ha : a ∈ orientedSurfaceCoefficients F) :
    ∑ E : F.support, componentHomologyMap E.1 4
      (Chow.divisorClass E.1.idealSheaf.subscheme (surfaceCoefficientDivisor a E.1)) = 0 := by
  calc ∑ E : F.support, componentHomologyMap E.1 4
        (Chow.divisorClass E.1.idealSheaf.subscheme (surfaceCoefficientDivisor a E.1))
      = ∑ E : F.support, Chow.rationalCycleClass Z 2
          (Chow.rationalProperPushforward (Stacks.Chow.fieldChowSituation ℂ) _ _ ((2 : ℕ) : ℤ)
            E.1.idealSheaf.subschemeι (comp_over _ _)
            (Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1))) := by
        refine Finset.sum_congr rfl fun E _ => ?_
        rw [Chow.rationalCycleClass_rationalProperPushforward]
        rfl
    _ = 0 := by rw [← map_sum, sum_rationalPushforward_divisorCycle_eq_zero sY r hM F a ha,
          map_zero]

open MMP.borelMooreHomology MMP.UnderlyingSpace in
/-- **The exceptional step.** After a blow-up `q` of a model, a family of rational surface
cycles on the components of the new full exceptional divisor whose classes vanish on the
components not lying over the codimension-`≥ 2` part `C` of the centre, whose cycles push forward
to zero in `Z` on the components over `C`, and whose ambient class sum vanishes, has vanishing
classes everywhere. -/
private theorem rationalCycleClass_eq_zero_of_sum_eq_zero {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (M : ∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2)
    (hO : ∀ E : F'.support, ¬ (E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) →
      Chow.rationalCycleClass _ 2 (M E) = 0)
    (hN : ∀ E : F'.support, E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
      ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2 (M E) = 0)
    (hsum : ∑ E : F'.support, componentHomologyMap E.1 4 (Chow.rationalCycleClass _ 2 (M E)) = 0)
    (E : F'.support) : Chow.rationalCycleClass _ 2 (M E) = 0 := by
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  by_cases hEN : E.1.support ⊆ blowUpToBase I ⁻¹' K
  swap
  · exact hO E hEN
  have := hM.isComplexScheme
  have hcomp := hM.comp_eq
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hcomp ▸ hM.isResolution.2.1
  have hZsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)) := hcomp ▸ hM.isResolution.2.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  haveI : SmoothOfRelativeDimension 4 (Z ↘ Spec (.of ℂ)) :=
    smoothOfRelativeDimension_of_isSmoothScheme hvarZ hZsm 4
      (by rw [hM.topologicalKrullDim_eq]; rfl)
  have hI : I ≠ ⊥ := ne_bot_of_blowUp E.1.genericPoint
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper (blowUpToBase I) := hqproj.isProper
  have hK : IsClosed K := MMP.Resolution.isClosed_componentsOfCodimAtLeastTwo I.support.isClosed
  haveI : IsIso (blowUpToBase I ∣_ ⟨Kᶜ, hK.isOpen_compl⟩) :=
    isIso_blowUpToBase_restrict_complCodimTwo hIc (stalk_ne_bot_of_ne_bot hI)
  have hvar' : AlgebraicGeometry.IsVariety ℂ (blowUp I ↘ Spec (.of ℂ)) :=
    hM'.comp_eq ▸ hM'.isResolution.2.1
  have : IsIntegral (blowUp I) := hvar'.toIsIntegral
  have : NoetherianSpace (blowUp I) := noetherianSpace_of_isComplexScheme
  -- dimensions
  have hZdim : topologicalKrullDim Z = ((4 : ℕ) : WithBot ℕ∞) := by
    rw [hM.topologicalKrullDim_eq]; rfl
  have hdimK : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal ⟨K, hK⟩).subscheme ≤
      ((4 - 2 : ℕ) : WithBot ℕ∞) := by
    refine dimension_subscheme_le _ hZdim.le fun W hW => ?_
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hW
    exact_mod_cast two_le_codimension_of_subset I.support.isClosed W hW
  have hnot : ∃ y : blowUp I, y ∉ blowUpToBase I ⁻¹' K := by
    obtain ⟨x, hx⟩ := nonempty_compl_componentsOfCodimAtLeastTwo I.support.isClosed
    obtain ⟨y, rfl⟩ := surjective_blowUpToBase hIc hI (blowUpToBase I).isClosedMap x
    exact ⟨y, hx⟩
  have hdimK' : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal
      ⟨blowUpToBase I ⁻¹' K, hK.preimage (blowUpToBase I).continuous⟩).subscheme ≤
      ((4 - 1 : ℕ) : WithBot ℕ∞) := by
    obtain ⟨y, hy⟩ := hnot
    refine dimension_subscheme_le _ hM'.topologicalKrullDim_eq.le fun W hW => ?_
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hW
    have hlt : W < ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩ := by
      refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) fun h => hy (hW ?_)
      rw [h]
      exact Set.mem_univ y
    rw [codimension_eq_coheight]
    exact_mod_cast le_add_self.trans (Order.coheight_add_one_le hlt)
  -- the snc structure of `F'`
  obtain ⟨G, hGred, hGsnc, hGex⟩ := hM'.exists_divisor
  have hF'G : F' = G := eq_of_isReducedEffective_of_supp_eq hF'red hGred (hF'ex.trans hGex.symm)
  rw [← hF'G] at hGsnc
  have hKI : K ⊆ (I.support : Set Z) := componentsOfCodimAtLeastTwo_subset _
  -- the class `u` on the points over `q⁻¹ K`
  let P : F'.support → Prop := fun E' => E'.1.support ⊆ blowUpToBase I ⁻¹' K
  have hrange : ∀ E' : {E' : F'.support // P E'},
      Set.range (E'.1.1.idealSheaf.subschemeι ≫ blowUpToBase I) ⊆ K := by
    rintro E' _ ⟨p, rfl⟩
    refine E'.2 ?_
    change E'.1.1.idealSheaf.subschemeι p ∈ (E'.1.1.idealSheaf.support : Set (blowUp I))
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨p, rfl⟩
  let j : ∀ E' : {E' : F'.support // P E'}, _ := fun E' =>
    toPreimagePointsOver E'.1.1.idealSheaf.subschemeι (blowUpToBase I) K (hrange E')
  have hj : ∀ E', IsProperMap (j E') := fun E' =>
    isProperMap_toPreimagePointsOver _ _ K (hrange E')
  let u := ∑ E' : {E' : F'.support // P E'}, (pushforward ℚ (ModuleCat.of ℚ ℚ) (j E') (hj E')
    ((2 * 2 : ℕ) : ℤ)).hom (Chow.rationalCycleClass _ 2 (M E'.1))
  have hu₁ : (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (subspaceInclusion (TopCat.of (UnderlyingSpace ℂ (blowUp I)))
        ((TopCat.ofHom (map (K := ℂ) (blowUpToBase I))) ⁻¹' pointsOver (K := ℂ) K))
      (isProperMap_subspaceInclusion
        ((isClosed_pointsOver hK).preimage
          (TopCat.ofHom (map (K := ℂ) (blowUpToBase I))).hom.continuous))
      ((2 * 2 : ℕ) : ℤ)).hom u = 0 := by
    simp only [u, map_sum]
    have hterm : ∀ E' : {E' : F'.support // P E'}, (pushforward ℚ (ModuleCat.of ℚ ℚ)
        (subspaceInclusion (TopCat.of (UnderlyingSpace ℂ (blowUp I)))
          ((TopCat.ofHom (map (K := ℂ) (blowUpToBase I))) ⁻¹' pointsOver (K := ℂ) K))
        (isProperMap_subspaceInclusion
          ((isClosed_pointsOver hK).preimage
            (TopCat.ofHom (map (K := ℂ) (blowUpToBase I))).hom.continuous))
        ((2 * 2 : ℕ) : ℤ)).hom ((pushforward ℚ (ModuleCat.of ℚ ℚ) (j E') (hj E')
          ((2 * 2 : ℕ) : ℤ)).hom (Chow.rationalCycleClass _ 2 (M E'.1))) =
        componentHomologyMap E'.1.1 4 (Chow.rationalCycleClass _ 2 (M E'.1)) := by
      intro E'
      rw [← ModuleCat.comp_apply, ← pushforward_comp]
      rfl
    simp only [hterm]
    have hsplit := Fintype.sum_subtype_add_sum_subtype P
      (fun E' : F'.support => componentHomologyMap E'.1 4 (Chow.rationalCycleClass _ 2 (M E')))
    have hzero : ∑ E' : {E' : F'.support // ¬ P E'},
        componentHomologyMap E'.1.1 4 (Chow.rationalCycleClass _ 2 (M E'.1)) = 0 :=
      Finset.sum_eq_zero fun E' _ => by rw [hO E'.1 E'.2, map_zero]
    rw [hzero, add_zero, hsum] at hsplit
    exact hsplit
  have hu₂ : (pushforward ℚ (ModuleCat.of ℚ ℚ)
      (closedRestrict (TopCat.ofHom (map (K := ℂ) (blowUpToBase I))) (pointsOver (K := ℂ) K))
      (isProperMap_closedRestrict _ (isProperMap_map (K := ℂ) (blowUpToBase I)) _)
      ((2 * 2 : ℕ) : ℤ)).hom u = 0 := by
    simp only [u, map_sum]
    refine Finset.sum_eq_zero fun E' _ => ?_
    rw [← ModuleCat.comp_apply, ← pushforward_comp]
    -- factor through the reduced structure on `K`
    set IK := Scheme.IdealSheafData.vanishingIdeal (⟨K, hK⟩ : Closeds Z)
    have hH : IK ≤ E'.1.1.idealSheaf.map (blowUpToBase I) := by
      rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf E'.1.1,
        Scheme.IdealSheafData.map_vanishingIdeal]
      refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
      change closure _ ⊆ K
      refine closure_minimal ?_ hK
      rintro _ ⟨x, hx, rfl⟩
      exact E'.2 hx
    set g := Scheme.IdealSheafData.subschemeMap _ IK (blowUpToBase I) hH
    have hg : g ≫ IK.subschemeι = E'.1.1.idealSheaf.subschemeι ≫ blowUpToBase I :=
      Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
    haveI : g.IsOver (Spec (.of ℂ)) := ⟨by
      change g ≫ IK.subschemeι ≫ (Z ↘ Spec (.of ℂ)) = _
      rw [← Category.assoc, hg, Category.assoc,
        (inferInstance : (blowUpToBase I).IsOver (Spec (.of ℂ))).comp_over]
      rfl⟩
    haveI : IsProper (g ≫ IK.subschemeι) := by rw [hg]; infer_instance
    haveI : IsProper g := IsProper.of_comp g IK.subschemeι
    have : IsComplexScheme IK.subscheme := IsComplexScheme.of_isClosedImmersion IK.subschemeι
    have : IsComplexScheme E'.1.1.idealSheaf.subscheme :=
      IsComplexScheme.of_isClosedImmersion E'.1.1.idealSheaf.subschemeι
    have hrK : Set.range IK.subschemeι ⊆ K := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hfac : j E' ≫ closedRestrict (TopCat.ofHom (map (K := ℂ) (blowUpToBase I)))
        (pointsOver (K := ℂ) K) =
        TopCat.ofHom (map (K := ℂ) g) ≫ toPointsOver IK.subschemeι K hrK := by
      dsimp only [j]
      rw [toPreimagePointsOver_comp_closedRestrict,
        toPointsOver_congr hg.symm K (hrange E') (by rw [hg]; exact hrange E'), toPointsOver_comp]
    have hpush : ratPush g 2 (M E'.1) = 0 := by
      apply rationalProperPushforward_injective_of_isClosedImmersion IK.subschemeι 2
      rw [← rationalPushforward_comp, rationalPushforward_congr hg, map_zero]
      exact hN E'.1 E'.2
    rw [pushforward_congr hfac _ ((isProperMap_toPointsOver IK.subschemeι K hrK).comp
      (isProperMap_map (K := ℂ) g)), pushforward_comp ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (map (K := ℂ) g)) (toPointsOver IK.subschemeι K hrK) (isProperMap_map (K := ℂ) g)
      (isProperMap_toPointsOver IK.subschemeι K hrK), ModuleCat.comp_apply]
    change (pushforward ℚ (ModuleCat.of ℚ ℚ) _ _ _).hom
      ((pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) g))
        (isProperMap_map (K := ℂ) g) ((2 * 2 : ℕ) : ℤ)).hom (Chow.rationalCycleClass _ 2 (M E'.1))) = 0
    rw [← Chow.rationalCycleClass_rationalProperPushforward, hpush, map_zero, map_zero]
  have hu : u = 0 := eq_zero_of_isIso_restrict_compl (Z := Z) (Z' := blowUp I) hM.isProjective
    (blowUpToBase I) hK hdimK hdimK' u hu₁ hu₂
  -- restrict to the open and closed piece over `E`
  have hEs : (E.1.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹' (I.support : Set Z) :=
    hEN.trans (Set.preimage_mono hKI)
  let X' : Set (TopCat.of (UnderlyingSpace ℂ (blowUp I))) :=
    (TopCat.ofHom (map (K := ℂ) (blowUpToBase I))) ⁻¹' pointsOver (K := ℂ) K
  have hOopen : IsOpen (Subtype.val ⁻¹' pointsOver (K := ℂ) (E.1.support : Set (blowUp I)) :
      Set (TopCat.of X')) := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨W, hW, hxW, hWE⟩ := exists_isOpen_inter_subset hIc hGsnc E.2 hEs hp
    refine ⟨Subtype.val ⁻¹' (pointsOver (K := ℂ) Wᶜ)ᶜ, fun p' hp' => ?_,
      ((isClosed_pointsOver hW.isClosed_compl).isOpen_compl).preimage continuous_subtype_val,
      fun h => h hxW⟩
    have h1 : p'.1.toHom (IsLocalRing.closedPoint ℂ) ∈ W := by
      by_contra h
      exact hp' h
    have h2 : (map (K := ℂ) (blowUpToBase I) p'.1).toHom (IsLocalRing.closedPoint ℂ) ∈ K := p'.2
    rw [toHom_map] at h2
    exact hWE _ h1 (hKI h2)
  let O : Opens (TopCat.of X') := ⟨_, hOopen⟩
  have hOclopen : IsClopen (O : Set (TopCat.of X')) :=
    ⟨(isClosed_pointsOver E.1.idealSheaf.support.isClosed).preimage continuous_subtype_val,
      hOopen⟩
  have hincl : IsProperMap (clopenInclusion O) := hOclopen.1.isClosedEmbedding_subtypeVal.isProperMap
  have hres := congrArg (restrict ℚ (ModuleCat.of ℚ ℚ) O ((2 * 2 : ℕ) : ℤ)).hom hu
  rw [map_zero] at hres
  simp only [u, map_sum] at hres
  set e₀ : {E' : F'.support // P E'} := ⟨E, hEN⟩
  rw [Finset.sum_eq_single e₀ ?_ (by simp)] at hres
  swap
  · intro e _ he
    rw [restrict_pushforward_apply]
    have hne : e.1.1 ≠ E.1 := fun h => he (Subtype.ext (Subtype.ext h))
    have hdisj := disjoint_support_of_subset_preimage hIc hGsnc e.1.2 hne
      (e.2.trans (Set.preimage_mono hKI)) hEs
    haveI : IsEmpty (Opens.comap (j e).hom O) := ⟨fun p => by
      have hp : (map (K := ℂ) e.1.1.idealSheaf.subschemeι p.1).toHom
          (IsLocalRing.closedPoint ℂ) ∈ (E.1.support : Set (blowUp I)) := p.2
      rw [toHom_map] at hp
      have hp' : e.1.1.idealSheaf.subschemeι (p.1.toHom (IsLocalRing.closedPoint ℂ)) ∈
          (e.1.1.support : Set (blowUp I)) := by
        change _ ∈ (e.1.1.idealSheaf.support : Set (blowUp I))
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨_, rfl⟩
      exact Set.disjoint_left.1 hdisj hp' hp⟩
    have h0 := isZero_borelMooreHomology_of_isEmpty ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (Opens.comap (j e).hom O)) ((2 * 2 : ℕ) : ℤ)
    rw [ModuleCat.isZero_iff_subsingleton] at h0
    rw [Subsingleton.elim ((restrict ℚ (ModuleCat.of ℚ ℚ) (Opens.comap (j e).hom O)
      ((2 * 2 : ℕ) : ℤ)).hom (Chow.rationalCycleClass _ 2 (M e.1))) 0, map_zero]
  -- the main term
  have hψmem : ∀ p : TopCat.of (UnderlyingSpace ℂ E.1.idealSheaf.subscheme), j e₀ p ∈ O := by
    intro p
    change (map (K := ℂ) E.1.idealSheaf.subschemeι p).toHom (IsLocalRing.closedPoint ℂ) ∈
      (E.1.idealSheaf.support : Set (blowUp I))
    rw [toHom_map, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨_, rfl⟩
  let ψ : TopCat.of (UnderlyingSpace ℂ E.1.idealSheaf.subscheme) ⟶ TopCat.of O :=
    TopCat.ofHom ⟨fun p => ⟨j e₀ p, hψmem p⟩, (j e₀).hom.continuous.subtype_mk _⟩
  have hψj : ψ ≫ clopenInclusion O = j e₀ := rfl
  have hψ : IsProperMap ψ :=
    isProperMap_of_comp_of_t2 ψ.hom.continuous continuous_subtype_val (hj e₀)
  have hψb : Function.Bijective ψ := by
    refine ⟨fun a b hab => ?_, fun b => ?_⟩
    · have h1 := congrArg (fun x => (x.1.1 : UnderlyingSpace ℂ (blowUp I))) hab
      exact (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ)
        E.1.idealSheaf.subschemeι).injective h1
    · have hb : b.1.1 ∈ Set.range (map (K := ℂ) E.1.idealSheaf.subschemeι) := by
        rw [range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι]
        exact b.2
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext (Subtype.ext ha)⟩
  rw [← pushforward_congr hψj ((hincl).comp hψ) (hj e₀), pushforward_comp ℚ (ModuleCat.of ℚ ℚ)
    ψ (clopenInclusion O) hψ hincl, ModuleCat.comp_apply] at hres
  have hrs := ConcreteCategory.congr_hom (pushforward_restrict_self ℚ (ModuleCat.of ℚ ℚ) O
    hOclopen hincl ((2 * 2 : ℕ) : ℤ))
    ((pushforward ℚ (ModuleCat.of ℚ ℚ) ψ hψ ((2 * 2 : ℕ) : ℤ)).hom
      (Chow.rationalCycleClass _ 2 (M e₀.1)))
  rw [ModuleCat.comp_apply] at hrs
  rw [hrs] at hres
  exact (bijective_pushforward_of_bijective ψ hψ hψb _).1 (hres.trans (map_zero _).symm)

/-- **Vertical systems push forward to zero.** The divisor of a vertical oriented system on a
component pushes forward to the zero surface cycle: each of its surfaces has image of dimension at
most one. -/
private theorem rationalPushforward_divisorCycle_eq_zero_of_mem_vertical {Z' Y : Scheme.{0}}
    [Z'.Over (Spec (.of ℂ))] [IsComplexScheme Z'] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y]
    (f : Z' ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsProper f] (hf : IsClosedMap f.base)
    (F' : Divisor Z') {a : DoubleSurface F' → ℚ} (ha : a ∈ verticalSurfaceCoefficients f F')
    (E : Mori.PrimeDivisor Z') :
    ratPush (E.idealSheaf.subschemeι ≫ f) 2
      (Chow.divisorCycle _ (surfaceCoefficientDivisor a E)) = 0 := by
  classical
  have : NoetherianSpace Z' := noetherianSpace_of_isComplexScheme
  rw [Chow.divisorCycle, Finsupp.linearCombination_apply, map_finsuppSum]
  refine Finset.sum_eq_zero fun P hP => ?_
  dsimp only
  rw [map_smul]
  have hP' : surfaceCoefficientCoeff a E P ≠ 0 := by
    rw [← coeff_surfaceCoefficientDivisor]
    exact Finsupp.mem_support_iff.1 hP
  obtain ⟨σ, hσ⟩ : ∃ σ : {σ : DoubleSurface F' // σ.fst = E ∧
      σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}}, a σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hP' (finsum_eq_zero_of_forall_eq_zero h)
  have hdim := ha.2 σ.1 hσ
  by_cases h2 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2
  · rw [primeDivisorCycle_eq_rationalPointCycle P rfl h2,
      rationalProperPushforward_rationalPointCycle, dif_neg, smul_zero]
    intro hW
    have hcl := Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
      ℂ _ _ 2 hW
    have heq : closure {(E.idealSheaf.subschemeι ≫ f).base P.genericPoint} =
        f.base '' σ.1.carrier := by
      rw [σ.2.2, ← hf.closure_image_eq_of_continuous f.continuous, Set.image_singleton]
      rfl
    rw [heq] at hcl
    rw [hcl] at hdim
    exact absurd hdim (by decide)
  · rw [primeDivisorCycle_eq_zero P h2, map_zero, smul_zero]

/-- **A cycle with zero push-forward drops dimension.** For a proper morphism of complex
varieties, a point `x` of delta-dimension `k` whose prime cycle pushes forward to zero has
`dim f(closure {x}) < k`: an image of dimension `k` is hit with nonzero degree. -/
private theorem topologicalKrullDim_image_lt_of_rationalPushforward_eq_zero {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y]
    [AlgebraicGeometry.IsVariety ℂ (X ↘ Spec (.of ℂ))]
    [AlgebraicGeometry.IsVariety ℂ (Y ↘ Spec (.of ℂ))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] [IsProper f] (hfc : IsClosedMap f.base) {k : ℕ}
    (x : X) (hx : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (X ↘ Spec (.of ℂ)) x = k)
    (h0 : ratPush f k (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
      (X ↘ Spec (.of ℂ)) k x hx) = 0) :
    topologicalKrullDim (f.base '' closure ({x} : Set X)) < k := by
  classical
  have hxk : topologicalKrullDim (closure ({x} : Set X)) = k :=
    Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
      ℂ _ x k hx
  have hle := Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le ℂ
    (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f (comp_over f _) _ isClosed_closure k hxk.le _
    (hfc _ isClosed_closure) le_rfl
  refine lt_of_le_of_ne hle fun heq => ?_
  have himg : closure ({f.base x} : Set Y) = f.base '' closure {x} := by
    rw [← hfc.closure_image_eq_of_continuous f.continuous, Set.image_singleton]
  have hfx := Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
    ℂ (Y ↘ Spec (.of ℂ)) (f.base x) k (by rw [himg]; exact heq)
  have hd := residueDegree_ne_zero (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f (comp_over f _) x
    hxk (by rw [himg]; exact heq)
  rw [rationalProperPushforward_rationalPointCycle, dif_pos hfx] at h0
  have := congrArg (Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ)) k
    (f.base x)) h0
  rw [map_smul, Chow.rationalCoeff_rationalPointCycle, if_pos rfl, map_zero, smul_eq_mul,
    mul_one] at this
  exact hd (by exact_mod_cast this)

private theorem rationalPushforward_divisorCycle_single_smul {X Z : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    (q : X ⟶ Z) [q.IsOver (Spec (.of ℂ))] [IsProper q] (E : Mori.PrimeDivisor X)
    (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
    (hP : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2)
    (hW : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Z ↘ Spec (.of ℂ)) (q.base (E.idealSheaf.subschemeι.base P.genericPoint)) =
        ((2 : ℕ) : ℤ)) (t : ℚ) :
    ratPush q 2 (ratPush E.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (Finsupp.single P t))) =
      (t * q.residueDegree (E.idealSheaf.subschemeι.base P.genericPoint)) •
        Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ)
          (q.base (E.idealSheaf.subschemeι.base P.genericPoint)) hW := by
  rw [show Finsupp.single P t = t • Finsupp.single P (1 : ℚ) by simp, map_smul, map_smul,
    map_smul, rationalPushforward_divisorCycle_single q E P hP hW, smul_smul]

open Classical in
/-- **Lifting one edge of the old boundary.** Let `σ` be a double surface of the full
exceptional divisor of `r` with vertical surface `T = W`, and let `E₁`, `E₂` be the old components
of the new boundary over its two components. There is a vertical oriented system `ℓ` on the new
boundary whose surfaces push forward to `[W]` on `E₁`, to `-[W]` on `E₂` and to `0` on every other
component: the edge through the strict transform of `T` when `T` is not over the
codimension-`≥ 2` part of the centre, and otherwise the path of two edges through the new
component over `T`. -/
private theorem exists_lift_edge {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)] [IsComplexScheme Z]
    [IsProper (blowUpToBase I)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (F : Divisor Z) (σ : DoubleSurface F)
    (hσ : topologicalKrullDim (r.base '' σ.carrier) ≤ 1)
    (ξ : Z) (hξ2 : Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) ξ = 2)
    (hW : closure ({ξ} : Set Z) = σ.carrier)
    {E₁ E₂ : Mori.PrimeDivisor (blowUp I)} (hE₁ : E₁ ∈ F'.support) (hE₂ : E₂ ∈ F'.support)
    (hE₁o : ¬ ((E₁.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹'
      MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)))
    (hE₂o : ¬ ((E₂.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹'
      MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)))
    (h₁ : (blowUpToBase I).base '' (E₁.support : Set (blowUp I)) = σ.fst.support)
    (h₂ : (blowUpToBase I).base '' (E₂.support : Set (blowUp I)) = σ.snd.support) :
    ∃ ℓ ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F', ∀ E : F'.support,
      ratPush (blowUpToBase I) 2 (ratPush E.1.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor ℓ E.1))) =
      ((if E.1 = E₁ then 1 else 0) - (if E.1 = E₂ then 1 else 0) : ℚ) •
        Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) ξ hξ2 := by
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  set q := blowUpToBase I with hqdef
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have hZsm : MMP.Mori.IsSmoothScheme (Z ↘ Spec (.of ℂ)) := hM.comp_eq ▸ hM.isResolution.2.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  have hvar' : AlgebraicGeometry.IsVariety ℂ (blowUp I ↘ Spec (.of ℂ)) :=
    hM'.comp_eq ▸ hM'.isResolution.2.1
  have : IsIntegral (blowUp I) := hvar'.toIsIntegral
  have hI : I ≠ ⊥ := ne_bot_of_blowUp E₁.genericPoint
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper q := hqproj.isProper
  have hqc : IsClosedMap q.base := q.isClosedMap
  have hK : IsClosed K := MMP.Resolution.isClosed_componentsOfCodimAtLeastTwo I.support.isClosed
  have hne := stalk_ne_bot_of_ne_bot hI
  haveI hiso : IsIso (q ∣_ ⟨Kᶜ, hK.isOpen_compl⟩) :=
    isIso_blowUpToBase_restrict_complCodimTwo hIc hne
  have hqbir : IsBiregular q ⟨Kᶜ, hK.isOpen_compl⟩ := hiso
  have : NoetherianSpace (blowUp I) := noetherianSpace_of_isComplexScheme
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((blowUp I) ↘ Spec (.of ℂ))
  have hbase : q ≫ (Z ↘ Spec (.of ℂ)) = blowUp I ↘ Spec (.of ℂ) :=
    (inferInstance : q.IsOver (Spec (.of ℂ))).comp_over
  have : LocallyOfFiniteType q :=
    AlgebraicGeometry.locallyOfFiniteType_of_isVariety_comp ℂ _ _ q hbase
  have : LocallyOfFiniteType (blowUp I ↘ Spec (.of ℂ)) := inferInstance
  have : LocallyOfFiniteType (Z ↘ Spec (.of ℂ)) := inferInstance
  obtain ⟨G, hGred, hGsnc, hGex⟩ := hM'.exists_divisor
  have hF'G : F' = G := eq_of_isReducedEffective_of_supp_eq hF'red hGred (hF'ex.trans hGex.symm)
  rw [← hF'G] at hGsnc
  -- the surface `T` and its generic point
  have hξT : closure ({ξ} : Set Z) = σ.carrier := hW
  have hT2 : topologicalKrullDim σ.carrier = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [← hW]
    exact Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
      ℂ _ ξ 2 hξ2
  have hξ₁ : ξ ∈ (σ.fst.support : Set Z) :=
    (σ.carrier_subset (hξT ▸ subset_closure rfl)).1
  have hξ₂ : ξ ∈ (σ.snd.support : Set Z) :=
    (σ.carrier_subset (hξT ▸ subset_closure rfl)).2
  rw [← h₁] at hξ₁
  rw [← h₂] at hξ₂
  obtain ⟨y₁, hy₁E, hy₁ξ⟩ := hξ₁
  obtain ⟨y₂, hy₂E, hy₂ξ⟩ := hξ₂
  have hE₁₂ : E₁ ≠ E₂ := by
    intro h
    apply σ.fst_ne_snd
    apply eq_of_genericPoint_mem_support
    have : (σ.fst.support : Set Z) = σ.snd.support := by rw [← h₁, ← h₂, h]
    rw [← this, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  -- images and dimensions of the closures of the points over `ξ`
  have himg : ∀ y : blowUp I, q y = ξ → q.base '' closure {y} = σ.carrier := by
    intro y hy
    rw [← hqc.closure_image_eq_of_continuous q.continuous, Set.image_singleton, hy, hξT]
  have hdim : ∀ y : blowUp I, q y = ξ →
      (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({y} : Set (blowUp I))) := by
    intro y hy
    by_contra hlt
    push Not at hlt
    have hle : topologicalKrullDim (closure ({y} : Set (blowUp I))) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
      withBot_le_of_lt_succ (n := 1) (by exact_mod_cast hlt)
    have := Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le ℂ
      (blowUp I ↘ Spec (.of ℂ)) (Z ↘ Spec (.of ℂ)) q hbase _ isClosed_closure 1 hle
      σ.carrier (isClosed_carrier σ) (himg y hy).symm.le
    rw [hT2] at this
    exact absurd this (by norm_num)
  have hdeg : ∀ y : blowUp I, q y = ξ →
      topologicalKrullDim (closure ({y} : Set (blowUp I))) = ((2 : ℕ) : WithBot ℕ∞) →
      q.residueDegree y ≠ 0 := by
    intro y hy h2
    refine residueDegree_ne_zero (blowUp I ↘ Spec (.of ℂ)) (Z ↘ Spec (.of ℂ)) q hbase y h2 ?_
    rw [hy, hξT]; exact hT2
  have hvert : ∀ τ : DoubleSurface F', ∀ y : blowUp I, q y = ξ → τ.carrier = closure {y} →
      topologicalKrullDim ((q ≫ r).base '' τ.carrier) ≤ 1 := by
    intro τ y hy hτ
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, hτ, himg y hy]
    exact hσ
  -- the push-forward of the surface of one prime divisor of a component through a point over `ξ`
  have hpush : ∀ (E : Mori.PrimeDivisor (blowUp I)) (P : Mori.PrimeDivisor E.idealSheaf.subscheme)
      (y : blowUp I), q y = ξ → E.idealSheaf.subschemeι P.genericPoint = y → ∀ t : ℚ,
      ratPush q 2 (ratPush E.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (Finsupp.single P t))) =
      (t * q.residueDegree y) •
        Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) ξ hξ2 := by
    intro E P y hy hPy t
    have hP2 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2 :=
      Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
        ℂ _ _ 2 (topologicalKrullDim_closure_genericPoint_eq_two sY (q ≫ r) hM' E P)
    subst hPy
    subst hy
    exact rationalPushforward_divisorCycle_single_smul q E P hP2 hξ2 t
  by_cases hξK : ξ ∈ K
  · -- the path of two edges through the new component over `T`
    obtain ⟨J, hJ, hJC, hy₁J, hCK⟩ := exists_new_component sY r hM I hIs hIc hM' F' hF'ex
      (show q y₁ ∈ K by rw [hy₁ξ]; exact hξK)
    rw [hy₁ξ] at hJC hCK
    have hξI : ξ ∈ (I.support : Set Z) := componentsOfCodimAtLeastTwo_subset _ hξK
    haveI : Smooth (Z ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hZsm
    have hy₂J : y₂ ∈ (J.support : Set (blowUp I)) :=
      preimage_subset_support_of_subset (Z ↘ Spec (.of ℂ)) I ⟨hZsm, hIs⟩ hne hIc hGsnc hJ
        (isClosed_connectedComponentIn I.support.isClosed ξ)
        (isConnected_connectedComponentIn_iff.2 hξI) (connectedComponentIn_subset _ _) hJC
        (show q y₂ ∈ _ by rw [hy₂ξ]; exact mem_connectedComponentIn hξI)
    have hJK : (J.support : Set (blowUp I)) ⊆ q ⁻¹' K := hJC.trans (Set.preimage_mono hCK)
    have hJ₁ : E₁ ≠ J := fun h => hE₁o (h ▸ hJK)
    have hJ₂ : E₂ ≠ J := fun h => hE₂o (h ▸ hJK)
    obtain ⟨σ₁, hσ₁f, hσ₁s, hσ₁c, hd₁⟩ := exists_doubleSurface_of_mem sY (q ≫ r) hM' F' hF'red
      hF'ex hE₁ hJ hJ₁ hy₁E hy₁J (hdim y₁ hy₁ξ)
    obtain ⟨σ₂, hσ₂f, hσ₂s, hσ₂c, hd₂⟩ := exists_doubleSurface_of_mem sY (q ≫ r) hM' F' hF'red
      hF'ex hE₂ hJ hJ₂ hy₂E hy₂J (hdim y₂ hy₂ξ)
    obtain ⟨P₁, hP₁⟩ := exists_primeDivisor_genericPoint_eq sY (q ≫ r) hM' E₁ hy₁E hd₁
    obtain ⟨Q₁, hQ₁⟩ := exists_primeDivisor_genericPoint_eq sY (q ≫ r) hM' J hy₁J hd₁
    obtain ⟨P₂, hP₂⟩ := exists_primeDivisor_genericPoint_eq sY (q ≫ r) hM' E₂ hy₂E hd₂
    obtain ⟨Q₂, hQ₂⟩ := exists_primeDivisor_genericPoint_eq sY (q ≫ r) hM' J hy₂J hd₂
    set d₁ : ℚ := (q.residueDegree y₁ : ℚ)
    set d₂ : ℚ := (q.residueDegree y₂ : ℚ)
    have hd₁0 : d₁ ≠ 0 := Nat.cast_ne_zero.2 (hdeg y₁ hy₁ξ hd₁)
    have hd₂0 : d₂ ≠ 0 := Nat.cast_ne_zero.2 (hdeg y₂ hy₂ξ hd₂)
    refine ⟨edgeSystem σ₁ (1 / d₁) + edgeSystem σ₂ (-(1 / d₂)),
      add_mem (edgeSystem_mem_vertical _ σ₁ _ (hvert σ₁ y₁ hy₁ξ hσ₁c))
        (edgeSystem_mem_vertical _ σ₂ _ (hvert σ₂ y₂ hy₂ξ hσ₂c)), fun E => ?_⟩
    have hadd : surfaceCoefficientDivisor (edgeSystem σ₁ (1 / d₁) + edgeSystem σ₂ (-(1 / d₂)))
        E.1 = surfaceCoefficientDivisor (edgeSystem σ₁ (1 / d₁)) E.1 +
          surfaceCoefficientDivisor (edgeSystem σ₂ (-(1 / d₂))) E.1 :=
      (surfaceCoefficientDivisorLinearMap F' E.1).map_add _ _
    rw [hadd, map_add, map_add, map_add]
    have hc₁ : σ₁.carrier = closure {E₁.idealSheaf.subschemeι P₁.genericPoint} := by
      rw [hP₁]; exact hσ₁c
    have hc₁' : σ₁.carrier = closure {J.idealSheaf.subschemeι Q₁.genericPoint} := by
      rw [hQ₁]; exact hσ₁c
    have hc₂ : σ₂.carrier = closure {E₂.idealSheaf.subschemeι P₂.genericPoint} := by
      rw [hP₂]; exact hσ₂c
    have hc₂' : σ₂.carrier = closure {J.idealSheaf.subschemeι Q₂.genericPoint} := by
      rw [hQ₂]; exact hσ₂c
    by_cases hE1 : E.1 = E₁
    · rw [hE1, surfaceCoefficientDivisor_edgeSystem_of_eq σ₁ _ hσ₁f P₁ hc₁,
        surfaceCoefficientDivisor_edgeSystem_of_ne σ₂ _ (by rw [hσ₂f]; exact hE₁₂)
          (by rw [hσ₂s]; exact hJ₁),
        hpush E₁ P₁ y₁ hy₁ξ hP₁, map_zero, map_zero, map_zero, add_zero, if_pos rfl,
        if_neg hE₁₂, one_div, inv_mul_cancel₀ hd₁0]
      simp
    by_cases hE2 : E.1 = E₂
    · rw [hE2, surfaceCoefficientDivisor_edgeSystem_of_ne σ₁ _ (by rw [hσ₁f]; exact hE₁₂.symm)
          (by rw [hσ₁s]; exact hJ₂),
        surfaceCoefficientDivisor_edgeSystem_of_eq σ₂ _ hσ₂f P₂ hc₂,
        hpush E₂ P₂ y₂ hy₂ξ hP₂, map_zero, map_zero, map_zero, zero_add, if_pos rfl,
        if_neg hE₁₂.symm, one_div, neg_mul, inv_mul_cancel₀ hd₂0]
      simp
    by_cases hEJ : E.1 = J
    · rw [hEJ, surfaceCoefficientDivisor_edgeSystem_of_snd_eq σ₁ _ hσ₁s Q₁ hc₁',
        surfaceCoefficientDivisor_edgeSystem_of_snd_eq σ₂ _ hσ₂s Q₂ hc₂',
        hpush J Q₁ y₁ hy₁ξ hQ₁, hpush J Q₂ y₂ hy₂ξ hQ₂, if_neg hJ₁.symm, if_neg hJ₂.symm,
        ← add_smul]
      congr 1
      change -(1 / d₁) * d₁ + -(-(1 / d₂)) * d₂ = 0 - 0
      rw [neg_neg, neg_mul, one_div, one_div, inv_mul_cancel₀ hd₁0, inv_mul_cancel₀ hd₂0]
      ring
    · rw [surfaceCoefficientDivisor_edgeSystem_of_ne σ₁ _ (by rw [hσ₁f]; exact hE1)
          (by rw [hσ₁s]; exact hEJ),
        surfaceCoefficientDivisor_edgeSystem_of_ne σ₂ _ (by rw [hσ₂f]; exact hE2)
          (by rw [hσ₂s]; exact hEJ), if_neg hE1, if_neg hE2]
      simp
  · -- the edge through the strict transform of `T`
    have hy₁y₂ : y₁ = y₂ := eq_of_isBiregular hqbir (show q y₁ ∈ Kᶜ by rw [hy₁ξ]; exact hξK)
      (hy₁ξ.trans hy₂ξ.symm)
    subst hy₁y₂
    obtain ⟨σ', hσ'f, hσ's, hσ'c, hd⟩ := exists_doubleSurface_of_mem sY (q ≫ r) hM' F' hF'red
      hF'ex hE₁ hE₂ hE₁₂ hy₁E hy₂E (hdim y₁ hy₁ξ)
    obtain ⟨P₁, hP₁⟩ := exists_primeDivisor_genericPoint_eq sY (q ≫ r) hM' E₁ hy₁E hd
    obtain ⟨P₂, hP₂⟩ := exists_primeDivisor_genericPoint_eq sY (q ≫ r) hM' E₂ hy₂E hd
    set d : ℚ := (q.residueDegree y₁ : ℚ)
    have hd0 : d ≠ 0 := Nat.cast_ne_zero.2 (hdeg y₁ hy₁ξ hd)
    refine ⟨edgeSystem σ' (1 / d), edgeSystem_mem_vertical _ σ' _ (hvert σ' y₁ hy₁ξ hσ'c),
      fun E => ?_⟩
    have hc₁ : σ'.carrier = closure {E₁.idealSheaf.subschemeι P₁.genericPoint} := by
      rw [hP₁]; exact hσ'c
    have hc₂ : σ'.carrier = closure {E₂.idealSheaf.subschemeι P₂.genericPoint} := by
      rw [hP₂]; exact hσ'c
    by_cases hE1 : E.1 = E₁
    · rw [hE1, surfaceCoefficientDivisor_edgeSystem_of_eq σ' _ hσ'f P₁ hc₁,
        hpush E₁ P₁ y₁ hy₁ξ hP₁, if_pos rfl, if_neg hE₁₂, one_div, inv_mul_cancel₀ hd0]
      simp
    by_cases hE2 : E.1 = E₂
    · rw [hE2, surfaceCoefficientDivisor_edgeSystem_of_snd_eq σ' _ hσ's P₂ hc₂,
        hpush E₂ P₂ y₁ hy₁ξ hP₂, if_pos rfl, if_neg hE₁₂.symm, one_div, neg_mul,
        inv_mul_cancel₀ hd0]
      simp
    · rw [surfaceCoefficientDivisor_edgeSystem_of_ne σ' _ (by rw [hσ'f]; exact hE1)
          (by rw [hσ's]; exact hE2), if_neg hE1, if_neg hE2]
      simp

/-- Every point in the support of a push-forward is the image of a point in the support of the
cycle. -/
private theorem exists_mem_support_of_mem_support_rationalPushforward {X X' : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [X'.Over (Spec (.of ℂ))] [IsComplexScheme X']
    (f : X ⟶ X') [f.IsOver (Spec (.of ℂ))] [IsProper f] {k : ℕ} {L : RatCycles X k} {y : X'}
    (hy : Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X' ↘ Spec (.of ℂ)) k y
      (ratPush f k L) ≠ 0) :
    ∃ x, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x L ≠ 0 ∧
      f.base x = y := by
  classical
  by_contra h
  push Not at h
  apply hy
  rw [rationalCycle_eq_sum L, map_sum, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, map_smul, rationalProperPushforward_rationalPointCycle, smul_eq_mul]
  by_cases hc : Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k i.1
      L = 0
  · rw [hc, zero_mul]
  · have hne := h i.1 hc
    split_ifs with hd
    · rw [map_smul, Chow.rationalCoeff_rationalPointCycle, if_neg (Ne.symm hne), smul_zero,
        mul_zero]
    · rw [map_zero, mul_zero]

/-- Push-forward along a closed map preserves the cycles mapping into `Q`. -/
private theorem rationalPushforward_mem_cyclesMappingInto {X X' Y' : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [X'.Over (Spec (.of ℂ))] [IsComplexScheme X']
    (g : X ⟶ X') [g.IsOver (Spec (.of ℂ))] [IsProper g]
    (hg : IsClosedMap g.base) (f : X' ⟶ Y') {k : ℕ} {Q : Set Y'} {L : RatCycles X k}
    (hL : L ∈ cyclesMappingInto (g ≫ f) k Q) :
    ratPush g k L ∈ cyclesMappingInto f k Q := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := exists_mem_support_of_mem_support_rationalPushforward g hy
  have := hL x hx
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp] at this
  have hcl : closure {g.base x} = g.base '' closure {x} := by
    rw [← hg.closure_image_eq_of_continuous g.continuous, Set.image_singleton]
  rw [hcl]
  exact this

/-- The divisor `Z_E(a)` of a system all of whose surfaces of nonzero coefficient map into `Q`
maps into `Q`. -/
private theorem divisorCycle_mem_cyclesMappingInto {X Y' : Scheme.{0}} {B : Divisor X}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] (f : X ⟶ Y') {Q : Set Y'}
    {a : DoubleSurface B → ℚ}
    (ha : ∀ σ, a σ ≠ 0 → f.base '' σ.carrier ⊆ Q) (E : Mori.PrimeDivisor X) :
    Chow.divisorCycle _ (surfaceCoefficientDivisor a E) ∈
      cyclesMappingInto (E.idealSheaf.subschemeι ≫ f) 2 Q := by
  classical
  have : NoetherianSpace X := noetherianSpace_of_isComplexScheme
  rw [Chow.divisorCycle, Finsupp.linearCombination_apply]
  refine Submodule.finsuppSum_mem _ _ _ _ fun P hP => ?_
  refine Submodule.smul_mem _ _ ?_
  have hP' : surfaceCoefficientCoeff a E P ≠ 0 := by
    rw [← coeff_surfaceCoefficientDivisor]; exact hP
  obtain ⟨σ, hσ⟩ : ∃ σ : {σ : DoubleSurface B // σ.fst = E ∧
      σ.carrier = closure {E.idealSheaf.subschemeι P.genericPoint}}, a σ ≠ 0 := by
    by_contra h
    push Not at h
    exact hP' (finsum_eq_zero_of_forall_eq_zero h)
  by_cases h2 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2
  · rw [primeDivisorCycle_eq_rationalPointCycle P rfl h2]
    intro y hy
    rw [Chow.rationalCoeff_rationalPointCycle] at hy
    have hyP : y = P.genericPoint := by
      by_contra h
      exact hy (if_neg h)
    subst hyP
    have := ha σ.1 hσ
    rw [σ.2.2] at this
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp,
      ← E.idealSheaf.subschemeι.isClosedEmbedding.closure_image_eq, Set.image_singleton]
    exact this
  · rw [primeDivisorCycle_eq_zero P h2]
    exact Submodule.zero_mem _

/-- On a model, the image of a component of the new boundary lying over the
codimension-`≥ 2` part of the centre has dimension at most two. -/
private theorem topologicalKrullDim_image_le_two {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (E : Mori.PrimeDivisor (blowUp I)) (hEN : E.support ⊆ blowUpToBase I ⁻¹'
      MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) :
    topologicalKrullDim ((blowUpToBase I).base '' (E.support : Set (blowUp I))) ≤
      ((2 : ℕ) : WithBot ℕ∞) := by
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  have hI : I ≠ ⊥ := ne_bot_of_blowUp E.genericPoint
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper (blowUpToBase I) := hqproj.isProper
  have hqc : IsClosedMap (blowUpToBase I).base := (blowUpToBase I).isClosedMap
  have hZ4 : topologicalKrullDim Z = ((4 : ℕ) : WithBot ℕ∞) := by
    rw [hM.topologicalKrullDim_eq]; rfl
  set C := (blowUpToBase I).base '' (E.support : Set (blowUp I)) with hCdef
  have hCcl : IsClosed C := hqc _ E.idealSheaf.support.isClosed
  have hEirr : IsIrreducible (E.support : Set (blowUp I)) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
  have hCirr : IsIrreducible C := hEirr.image _ (blowUpToBase I).continuous.continuousOn
  have hCK : C ⊆ K := by rintro _ ⟨x, hx, rfl⟩; exact hEN hx
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hCirr hCcl
  have h1 := topologicalKrullDim_closure_add_coheight ξ
  rw [hξ.def, hZ4] at h1
  have h2 := two_le_codimension_of_subset I.support.isClosed ⟨C, hCirr, hCcl⟩ hCK
  have hCξ : (⟨C, hCirr, hCcl⟩ : IrreducibleCloseds Z) =
      IrreducibleCloseds.closureSingleton ξ := by
    ext1; exact hξ.def.symm
  rw [hCξ, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton] at h2
  revert h1 h2
  generalize Order.coheight ξ = c
  generalize topologicalKrullDim C = e
  intro h1 h2
  induction e using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h1' : e + c = ((4 : ℕ) : ℕ∞) :=
      WithBot.coe_injective (by rw [WithBot.coe_add]; exact h1)
    induction e using ENat.recTopCoe with
    | top => simp at h1'
    | coe e =>
      induction c using ENat.recTopCoe with
      | top => simp at h1'
      | coe c =>
        have e1 : e + c = 4 := by exact_mod_cast h1'
        have e2 : 2 ≤ c := by exact_mod_cast h2
        exact WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : e ≤ 2))

/-- **The correction through `J` on one component.** For a single component `E` of the new
full exceptional divisor over the codimension-`≥ 2` part of the centre, a vertical edge system
corrects `q_* L_E` to zero, without touching the other components over that part. -/
private theorem exists_verticalSurfaceCoefficients_jCorrection_one {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hY : MMP.Mori.IsProjectiveVariety ℂ (Y ↘ Spec (.of ℂ))) (hYQ : IsQFactorial (Y ↘ Spec (.of ℂ)))
    (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r] (hM : IsModel (Y ↘ Spec (.of ℂ)) r)
    (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel (Y ↘ Spec (.of ℂ)) (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    [IsProper (blowUpToBase I)] [IsProper (blowUpToBase I ≫ r)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (L : ∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2)
    (hL : ∀ E : F'.support, ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I ≫ r) 2 (L E) = 0)
    (E : F'.support) (hEN : E.1.support ⊆ blowUpToBase I ⁻¹'
      MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) (Q : Set Y)
    (hLQ : L E ∈ cyclesMappingInto (E.1.idealSheaf.subschemeι ≫ blowUpToBase I ≫ r) 2 Q) :
    ∃ a ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F',
      (∀ τ, a τ ≠ 0 → (blowUpToBase I ≫ r).base '' τ.carrier ⊆ Q) ∧
      ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2
          (L E - Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1)) = 0 ∧
      ∀ E₂ : F'.support, E₂ ≠ E → E₂.1.support ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
        surfaceCoefficientDivisor a E₂.1 = 0 := by
  haveI : IsComplexScheme Y :=
    MMP.Analytic.isComplexScheme_of_isProjective Y hY.isProjective.isProjective
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  by_cases hc : ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2 (L E) = 0
  · refine ⟨0, Submodule.zero_mem _, fun τ h => absurd rfl h, ?_, fun E₂ _ _ =>
      (surfaceCoefficientDivisorLinearMap F' E₂.1).map_zero⟩
    rw [show surfaceCoefficientDivisor (0 : DoubleSurface F' → ℚ) E.1 = 0 from
      (surfaceCoefficientDivisorLinearMap F' E.1).map_zero, map_zero, sub_zero]
    exact hc
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  have hI : I ≠ ⊥ := ne_bot_of_blowUp E.1.genericPoint
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper (blowUpToBase I) := hqproj.isProper
  have hqc : IsClosedMap (blowUpToBase I).base := (blowUpToBase I).isClosedMap
  have : NoetherianSpace (blowUp I) := noetherianSpace_of_isComplexScheme
  have hZ4 : topologicalKrullDim Z = ((4 : ℕ) : WithBot ℕ∞) := by
    rw [hM.topologicalKrullDim_eq]; rfl
  set C := (blowUpToBase I).base '' (E.1.support : Set (blowUp I)) with hCdef
  have hCdim : topologicalKrullDim C ≤ ((2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_image_le_two (Y ↘ Spec (.of ℂ)) r hM I E.1 hEN
  haveI : IsComplexScheme E.1.idealSheaf.subscheme :=
    IsComplexScheme.of_isClosedImmersion E.1.idealSheaf.subschemeι
  obtain ⟨w₀, hw₀, hW₀C, t, ht, hct⟩ :=
    exists_eq_smul_single_of_ne_zero hZ4 (blowUpToBase I) hqc E.1 hCdim (L E) hc
  have hC2 : topologicalKrullDim C = ((2 : ℕ) : WithBot ℕ∞) := by
    rw [hCdef, ← hW₀C]
    exact Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
      ℂ _ w₀ 2 hw₀
  have hrC : topologicalKrullDim (r.base '' C) ≤ 1 := by
    haveI : AlgebraicGeometry.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hY.toIsVariety
    haveI : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) := hvarZ
    have h0 : ratPush r 2 (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
        (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) w₀ hw₀) = 0 := by
      have h := hL E
      rw [rationalPushforward_congr (Category.assoc _ _ _).symm, rationalPushforward_comp, hct,
        map_smul] at h
      exact (smul_eq_zero.1 h).resolve_left ht
    have hlt := topologicalKrullDim_image_lt_of_rationalPushforward_eq_zero r r.isClosedMap w₀
      hw₀ h0
    rw [hW₀C] at hlt
    change topologicalKrullDim (r.base '' C) < ((2 : ℕ) : WithBot ℕ∞) at hlt
    revert hlt
    generalize topologicalKrullDim (r.base '' C) = e
    intro hlt
    induction e using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe e =>
      have hlt' : e < ((2 : ℕ) : ℕ∞) := WithBot.coe_lt_coe.1 hlt
      induction e using ENat.recTopCoe with
      | top => simp at hlt'
      | coe e =>
        have : e < 2 := by exact_mod_cast hlt'
        exact WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : e ≤ 1))
  obtain ⟨σ, hσE, hσold, ⟨P, hP⟩, hσimg⟩ :=
    exists_doubleSurface_jEdge (Y ↘ Spec (.of ℂ)) r hM I hIs hIc hM' F' hF'red hF'ex E hEN hC2 hrC
  obtain ⟨μ, hμ, hpush⟩ : ∃ μ : ℚ, μ ≠ 0 ∧
      ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2
        (Chow.divisorCycle _ (Finsupp.single P 1)) =
        μ • Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ))
          ((2 : ℕ) : ℤ) w₀ hw₀ := by
    set ιE := E.1.idealSheaf.subschemeι
    have hgc : IsClosedMap (ιE ≫ blowUpToBase I).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp]
      exact hqc.comp ιE.isClosedEmbedding.isClosedMap
    have hP2 : topologicalKrullDim (closure ({P.genericPoint} : Set E.1.idealSheaf.subscheme)) =
        ((2 : ℕ) : WithBot ℕ∞) :=
      topologicalKrullDim_closure_genericPoint_eq_two (Y ↘ Spec (.of ℂ)) (blowUpToBase I ≫ r) hM'
        E.1 P
    have h2 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (E.1.idealSheaf.subscheme ↘ Spec (.of ℂ)) P.genericPoint = 2 :=
      Stacks.Intersection.ExteriorProductProjections.relativeDimension_eq_of_topologicalKrullDim_closure
        ℂ _ _ 2 hP2
    have hgcl : closure {(ιE ≫ blowUpToBase I).base P.genericPoint} = closure {w₀} := by
      rw [hW₀C, ← Set.image_singleton, hgc.closure_image_eq_of_continuous
        (ιE ≫ blowUpToBase I).continuous, Scheme.Hom.comp_base, TopCat.coe_comp,
        Set.image_comp, ← ιE.isClosedEmbedding.closure_image_eq, Set.image_singleton, ← hP,
        hσimg]
    have hgP : (ιE ≫ blowUpToBase I).base P.genericPoint = w₀ :=
      (inseparable_iff_closure_eq.2 hgcl).eq
    have hd := residueDegree_ne_zero ((ιE ≫ blowUpToBase I) ≫ (Z ↘ Spec (.of ℂ)))
      (Z ↘ Spec (.of ℂ)) (ιE ≫ blowUpToBase I) rfl P.genericPoint hP2 (by
        rw [show ((ιE ≫ blowUpToBase I) P.genericPoint) = w₀ from hgP]
        exact Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
          ℂ _ w₀ 2 hw₀)
    refine ⟨((ιE ≫ blowUpToBase I).residueDegree P.genericPoint : ℚ), Nat.cast_ne_zero.2 hd, ?_⟩
    have hgw : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Z ↘ Spec (.of ℂ)) ((ιE ≫ blowUpToBase I).base P.genericPoint) = ((2 : ℕ) : ℤ) := by
      rw [hgP]; exact hw₀
    rw [Chow.divisorCycle_single, one_smul, primeDivisorCycle_eq_rationalPointCycle P rfl h2,
      rationalProperPushforward_rationalPointCycle, dif_pos hgw,
      rationalPointCycle_congr hgP hgw hw₀]
  refine ⟨edgeSystem σ (t / μ), edgeSystem_mem_vertical _ σ _ ?_, ?_, ?_,
    fun E₂ hE₂ hE₂N => ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, hσimg]
    exact hrC
  · intro τ hτ
    have hτσ : τ.carrier = σ.carrier := by
      unfold edgeSystem at hτ
      split_ifs at hτ with h1 h2
      · rw [h1]
      · rw [h2, DoubleSurface.swap_carrier]
      · exact absurd rfl hτ
    have hW₀Q : r.base '' closure ({w₀} : Set Z) ⊆ Q := by
      have hmem := rationalPushforward_mem_cyclesMappingInto
        (E.1.idealSheaf.subschemeι ≫ blowUpToBase I)
        (by rw [Scheme.Hom.comp_base, TopCat.coe_comp]
            exact hqc.comp E.1.idealSheaf.subschemeι.isClosedEmbedding.isClosedMap) r
        (L := L E) (by rw [Category.assoc]; exact hLQ)
      refine hmem w₀ ?_
      rw [hct, map_smul, Chow.rationalCoeff_rationalPointCycle, if_pos rfl, smul_eq_mul, mul_one]
      exact ht
    rw [hτσ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, hσimg]
    rw [hW₀C] at hW₀Q
    exact hW₀Q
  · have hZE : surfaceCoefficientDivisor (edgeSystem σ (t / μ)) E.1 =
        (t / μ) • Finsupp.single P 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      exact surfaceCoefficientDivisor_edgeSystem_of_eq σ (t / μ) hσE P hP
    rw [hZE, map_smul, map_sub, map_smul, hpush, hct, smul_smul, div_mul_cancel₀ _ hμ, sub_self]
  · apply surfaceCoefficientDivisor_edgeSystem_of_ne
    · rw [hσE]; exact fun h => hE₂ (Subtype.ext h)
    · exact fun h => hσold (h ▸ hE₂N)

/-- **The correction through `J`.** After a boundary-compatible smooth blow-up, a family of
vertical rational surface cycles on the new boundary differs on the components over the
codimension-`≥ 2` part of the centre, after subtracting a vertical oriented system, by cycles with
zero push-forward to `Z`. If every surface of the family maps into `Q ⊆ Y`, so does every surface
of nonzero coefficient of the system. -/
private theorem exists_verticalSurfaceCoefficients_jCorrection {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hY : MMP.Mori.IsProjectiveVariety ℂ (Y ↘ Spec (.of ℂ))) (hYQ : IsQFactorial (Y ↘ Spec (.of ℂ)))
    (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r] (hM : IsModel (Y ↘ Spec (.of ℂ)) r)
    (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel (Y ↘ Spec (.of ℂ)) (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    [IsProper (blowUpToBase I)] [IsProper (blowUpToBase I ≫ r)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (L : ∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2)
    (hL : ∀ E : F'.support, ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I ≫ r) 2 (L E) = 0)
    (Q : Set Y)
    (hLQ : ∀ E : F'.support, L E ∈ cyclesMappingInto (E.1.idealSheaf.subschemeι ≫ blowUpToBase I ≫ r) 2 Q) :
    ∃ a ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F',
      (∀ τ, a τ ≠ 0 → (blowUpToBase I ≫ r).base '' τ.carrier ⊆ Q) ∧
      ∀ E : F'.support, E.1.support ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
        ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2
          (L E - Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1)) = 0 := by
  haveI : IsComplexScheme Y :=
    MMP.Analytic.isComplexScheme_of_isProjective Y hY.isProjective.isProjective
  classical
  have key : ∀ E : F'.support, ∃ aE ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F',
      (∀ τ, aE τ ≠ 0 → (blowUpToBase I ≫ r).base '' τ.carrier ⊆ Q) ∧
      (E.1.support ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
        ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2
          (L E - Chow.divisorCycle _ (surfaceCoefficientDivisor aE E.1)) = 0) ∧
      ∀ E₂ : F'.support, E₂ ≠ E → E₂.1.support ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
        surfaceCoefficientDivisor aE E₂.1 = 0 := by
    intro E
    by_cases hEN : E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)
    · obtain ⟨aE, haE, h0, h1, h2⟩ := exists_verticalSurfaceCoefficients_jCorrection_one hY
        hYQ r hM I hIs hIc hM' F' hF'red hF'ex L hL E hEN Q (hLQ E)
      exact ⟨aE, haE, h0, fun _ => h1, h2⟩
    · exact ⟨0, Submodule.zero_mem _, fun τ h => absurd rfl h, fun h => absurd h hEN, fun E₂ _ _ =>
        (surfaceCoefficientDivisorLinearMap F' E₂.1).map_zero⟩
  choose a ha h0 h1 h2 using key
  refine ⟨∑ E, a E, Submodule.sum_mem _ fun E _ => ha E, fun τ hτ => ?_, fun E hE => ?_⟩
  · rw [Finset.sum_apply] at hτ
    obtain ⟨E, -, hE⟩ := Finset.exists_ne_zero_of_sum_ne_zero hτ
    exact h0 E τ hE
  have hZ : surfaceCoefficientDivisor (∑ E', a E') E.1 = surfaceCoefficientDivisor (a E) E.1 := by
    change surfaceCoefficientDivisorLinearMap F' E.1 (∑ E', a E') =
      surfaceCoefficientDivisorLinearMap F' E.1 (a E)
    rw [map_sum]
    exact Finset.sum_eq_single (f := fun x => surfaceCoefficientDivisorLinearMap F' E.1 (a x)) E
      (fun E₂ _ hne => h2 E₂ E (Ne.symm hne) hE) (fun h => absurd (Finset.mem_univ _) h)
  rw [hZ]
  exact h1 E hE

/-- **A map of closed integral subschemes compatible with a morphism which is a local isomorphism
at the generic point is birational**: its stalk map at the generic point is surjective, being a
factor of a quotient of an isomorphism, and injective, its source being a field. -/
private theorem isBirational_of_comp_eq {X Y Z' Z : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (ρ : X ⟶ Y) (i : X ⟶ Z') [IsClosedImmersion i] (j : Y ⟶ Z) (q : Z' ⟶ Z)
    (h : ρ ≫ j = i ≫ q) (hgen : ρ (genericPoint X) = genericPoint Y)
    (hq : IsIso (q.stalkMap (i (genericPoint X)))) : IsBirational ρ := by
  refine ⟨?_, fun x hx => ?_⟩
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton]
    refine ⟨fun x hx => ?_, fun a ha b hb _ => ?_, fun y hy => ?_⟩
    · rw [Set.mem_singleton_iff] at hx ⊢; rw [hx, hgen]
    · rw [Set.mem_singleton_iff] at ha hb; rw [ha, hb]
    · rw [Set.mem_singleton_iff] at hy; exact ⟨genericPoint X, rfl, hgen.trans hy.symm⟩
  · rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx
    subst hx
    set η := genericPoint X
    have e1 : ∀ x, (ρ ≫ j).stalkMap η x = ρ.stalkMap η (j.stalkMap (ρ η) x) := fun x =>
      DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (Scheme.Hom.stalkMap_comp ρ j η)) x
    have e2 : ∀ x, (i ≫ q).stalkMap η x = i.stalkMap η (q.stalkMap (i η) x) := fun x =>
      DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (Scheme.Hom.stalkMap_comp i q η)) x
    obtain ⟨φ, hφi, hφ⟩ : ∃ φ : Z.presheaf.stalk ((ρ ≫ j) η) ⟶ Z.presheaf.stalk ((i ≫ q) η),
        IsIso φ ∧ (ρ ≫ j).stalkMap η = φ ≫ (i ≫ q).stalkMap η :=
      ⟨_, inferInstance, Scheme.Hom.stalkMap_congr_hom (ρ ≫ j) (i ≫ q) h η⟩
    have e3 : ∀ x, (ρ ≫ j).stalkMap η x = (i ≫ q).stalkMap η (φ x) := fun x =>
      DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hφ) x
    have hsurj : Function.Surjective (ρ.stalkMap η) := by
      intro b
      obtain ⟨a, ha⟩ := i.stalkMap_surjective η b
      obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (q.stalkMap (i η))).2 a
      obtain ⟨d, hd⟩ := (ConcreteCategory.bijective_of_isIso φ).2 c
      refine ⟨j.stalkMap (ρ η) d, ?_⟩
      rw [← e1, e3, hd]
      exact (e2 c).trans (by rw [hc, ha])
    have hfield : IsField (Y.presheaf.stalk (ρ η)) :=
      (Y.presheaf.stalkCongr (.of_eq hgen)).commRingCatIsoToRingEquiv.toMulEquiv.isField
        (Field.toIsField Y.functionField)
    letI := hfield.toField
    have hinj : Function.Injective (ρ.stalkMap η) := RingHom.injective (ρ.stalkMap η).hom
    exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩

/-- In a Noetherian sober space, the points of a closed set `S` whose closures have the largest
dimension `n` allowed in `S` are finitely many: their closures are irreducible components of
`S`. -/
private theorem finite_setOf_le_topologicalKrullDim_closure {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] [T0Space X] {S : Set X} (hS : IsClosed S) {n : ℕ}
    (hn : ∀ a ∈ S, topologicalKrullDim (closure ({a} : Set X)) ≤ n) :
    {a | a ∈ S ∧ (n : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({a} : Set X))}.Finite := by
  classical
  obtain ⟨T, hT, hTcl, hTirr, hST⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  refine Set.Finite.of_finite_image (f := fun a => closure ({a} : Set X)) (hT.subset ?_) ?_
  · rintro _ ⟨a, ⟨haS, han⟩, rfl⟩
    have hsub : closure ({a} : Set X) ⊆ ⋃₀ (hT.toFinset : Set (Set X)) := by
      rw [hT.coe_toFinset, ← hST]
      exact closure_minimal (Set.singleton_subset_iff.2 haS) hS
    obtain ⟨t, htT, hat⟩ := isIrreducible_iff_sUnion_isClosed.1 isIrreducible_singleton.closure
      hT.toFinset (fun z hz => hTcl z (hT.mem_toFinset.1 hz)) hsub
    rw [hT.mem_toFinset] at htT
    have htS : t ⊆ S := by rw [hST]; exact Set.subset_sUnion_of_mem htT
    obtain ⟨g, hg⟩ := QuasiSober.sober (hTirr t htT) (hTcl t htT)
    have hdt : topologicalKrullDim t ≤ n := hg.def ▸ hn g (htS hg.mem)
    by_contra hne
    have hnt : ((n : ℕ) : WithBot ℕ∞) ≠ ⊤ := by
      have : ((n : ℕ) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this, ← WithBot.coe_top, Ne, WithBot.coe_inj]
      exact ENat.coe_ne_top n
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne (hTirr t htT) isClosed_closure hat
      (fun h => hne (by show closure {a} ∈ T; rw [h]; exact htT)) (ne_top_of_le_ne_top hnt hdt)
    exact absurd (lt_of_le_of_lt han (hlt.trans_le hdt)) (lt_irrefl _)
  · intro a _ b _ hab
    exact (inseparable_iff_closure_eq.2 hab).eq

open MMP.borelMooreHomology UnderlyingSpace in
/-- **A class killed by a proper map which is an isomorphism over an open is a cycle class
supported off that open.** Let `ρ : X ⟶ P` be proper and an isomorphism over `U ⊆ P`, and let
every point of `X - ρ⁻¹U` have closure of dimension at most two. A class of `H_4(X)` with
`ρ_* x = 0` restricts to zero on `ρ⁻¹U`, hence comes from `H_4(X - ρ⁻¹U)`, which is spanned by
the classes of the surfaces there. -/
private theorem exists_rationalCycleClass_eq_of_pushforward_eq_zero {X P : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X] [P.Over (Spec (.of ℂ))] [IsComplexScheme P]
    (ρ : X ⟶ P) [ρ.IsOver (Spec (.of ℂ))] [IsProper ρ] (U : P.Opens) [IsIso (ρ ∣_ U)]
    (hdim : ∀ a : X, a ∉ (ρ ⁻¹ᵁ U : X.Opens) →
      topologicalKrullDim (closure ({a} : Set X)) ≤ ((2 : ℕ) : WithBot ℕ∞))
    (x : RationalHomology X (2 * 2))
    (hx : (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) ρ))
      (isProperMap_map (K := ℂ) ρ) (2 * 2 : ℕ)).hom x = 0) :
    ∃ N : RatCycles X 2, x = Chow.rationalCycleClass X 2 N ∧
      ∀ v : X, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
        ((2 : ℕ) : ℤ) v N ≠ 0 → closure {v} ⊆ ((ρ ⁻¹ᵁ U : X.Opens) : Set X)ᶜ := by
  classical
  set C : Set X := ((ρ ⁻¹ᵁ U : X.Opens) : Set X)ᶜ with hCdef
  have hC : IsClosed C := (ρ ⁻¹ᵁ U).isOpen.isClosed_compl
  set A := Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩ with hAdef
  set i := A.subschemeι with hidef
  haveI : IsComplexScheme A.subscheme := IsComplexScheme.of_isClosedImmersion i
  have hrangeA : Set.range i = C := by
    rw [hidef, Scheme.IdealSheafData.range_subschemeι, hAdef,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨-, -, hex, -⟩ := IsComplexScheme.exists_borelMooreHomology_longExact ℚ
    (ModuleCat.of ℚ ℚ) X i
  -- the open of `ℂ`-points of `P` over `U`
  have hB : IsClosed ((U : Set P)ᶜ) := U.isOpen.isClosed_compl
  have hXB : IsClosed (pointsOver (K := ℂ) ((U : Set P)ᶜ) :
      Set (TopCat.of (UnderlyingSpace ℂ P))) := isClosed_pointsOver hB
  set U' := complOpens (Y := TopCat.of (UnderlyingSpace ℂ P)) hXB with hU'def
  have hU' : ∀ p : UnderlyingSpace ℂ P, p ∈ U' ↔
      p.toHom (IsLocalRing.closedPoint ℂ) ∈ U := by
    intro p
    change p ∉ pointsOver (K := ℂ) ((U : Set P)ᶜ) ↔ _
    rw [mem_pointsOver]
    simp
  have hbij := bijective_restrictPreimage_map_of_isIso ρ U U' hU'
  have hinj := (bijective_pushforward_of_bijective (R := ℚ)
    (restrictPreimage (TopCat.ofHom (map (K := ℂ) ρ)) U')
    (isProperMap_restrictPreimage _ U' (isProperMap_map (K := ℂ) ρ)) hbij
    ((2 * 2 : ℕ) : ℤ)).1
  have hres : restrict ℚ (ModuleCat.of ℚ ℚ) (Opens.comap (TopCat.ofHom (map (K := ℂ) ρ)).hom U')
      ((2 * 2 : ℕ) : ℤ) x = 0 := by
    have h := restrict_pushforward_apply ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) ρ))
      (isProperMap_map (K := ℂ) ρ) U' ((2 * 2 : ℕ) : ℤ) x
    rw [hx, map_zero] at h
    exact hinj (h.symm.trans (map_zero _).symm)
  have hopens : complOpens (Y := TopCat.of (UnderlyingSpace ℂ X))
      (isClosed_range_map_of_isClosedImmersion i) =
      Opens.comap (TopCat.ofHom (map (K := ℂ) ρ)).hom U' := by
    ext p
    change p ∉ Set.range (map (K := ℂ) i) ↔ map (K := ℂ) ρ p ∈ U'
    rw [hU', toHom_map]
    change p ∉ Set.range (mapFun (K := ℂ) i) ↔ _
    rw [range_mapFun_of_isClosedImmersion, Set.mem_setOf_eq, hrangeA, hCdef]
    simp only [Set.mem_compl_iff, not_not]
    rfl
  have hres' : restrict ℚ (ModuleCat.of ℚ ℚ) (complOpens (Y := TopCat.of (UnderlyingSpace ℂ X))
      (isClosed_range_map_of_isClosedImmersion i)) ((2 * 2 : ℕ) : ℤ) x = 0 := by
    rw [hopens]; exact hres
  obtain ⟨y, hy⟩ := (hex ((2 * 2 : ℕ) : ℤ) x).1 hres'
  -- the classes of `A` are cycle classes
  have hAdim : topologicalKrullDim A.subscheme ≤ ((2 : ℕ) : WithBot ℕ∞) := by
    have hemb := i.isClosedEmbedding
    have hrange : Set.range i = C := hrangeA
    let e := hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
    change topologicalKrullDim A.subscheme ≤ _
    rw [e.isHomeomorph.topologicalKrullDim_eq]
    exact topologicalKrullDim_le_of_forall_closure hC hdim
  obtain ⟨M, rfl⟩ := (MMP.Fourfold.bijective_rationalCycleClass (X := A.subscheme) hAdim).2 y
  refine ⟨ratPush A.subschemeι 2 M, ?_, ?_⟩
  · rw [Chow.rationalCycleClass_rationalProperPushforward, ← hy]
  · intro v hv
    have hvC : v ∈ C := by
      by_contra h
      exact hv (rationalCoeff_rationalProperPushforward_eq_zero_of_notMem A.subschemeι 2 M v
        (by rw [hrangeA]; exact h))
    exact closure_minimal (Set.singleton_subset_iff.2 hvC) hC

/-- The components of an snc divisor are normal: they are regular. -/
private theorem isNormal_subscheme_of_isSNC {Z S : Scheme.{0}} (sZ : Z ⟶ S)
    [IsLocallyNoetherian Z] {B : Divisor Z} (hB : DivisorWithCoeffs.IsSNC sZ B)
    {P : Mori.PrimeDivisor Z} (hP : P ∈ B.support) : IsNormal P.idealSheaf.subscheme := by
  rw [isNormal_iff_stalk_normal]
  intro z
  have hz : P.idealSheaf.subschemeι z ∈ (P.support : Set Z) := by
    change _ ∈ (P.idealSheaf.support : Set Z)
    rw [← P.idealSheaf.range_subschemeι]; exact ⟨z, rfl⟩
  obtain ⟨n, w, j, hw, -, hI⟩ := hB.2 (P.idealSheaf.subschemeι z)
  have := isRegularLocalRing_of_isRegularSystemOfParameters hw
  have hstalk : IdealSheafData.stalk P.idealSheaf (P.idealSheaf.subschemeι z) =
      Ideal.span (w '' (({j ⟨P, hP, hz⟩} : Finset (Fin n)) : Set (Fin n))) := by
    rw [hI ⟨P, hP, hz⟩, Finset.coe_singleton, Set.image_singleton]
  have := isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient P.idealSheaf z (by
    rw [hstalk]
    exact MMP.Resolution.isRegularLocalRing_quotient_span_image w hw _)
  exact ⟨IsRegularLocalRing.isDomain _, isIntegrallyClosed_of_isRegularLocalRing _⟩

open MMP.borelMooreHomology UnderlyingSpace in
/-- **The threefold blow-up kernel.** For an old component `E` of the new boundary over the
component `P` of the old one, a class of `H_4(E)` killed by `ρ : E ⟶ P` is the class of the
divisor on `E` of a system of edges between `E` and new components, along surfaces contracted by
`q`: off the finite-fibre locus of `ρ`, over which `ρ` is an isomorphism by Zariski's main
theorem, the surfaces of `E` map to curves or points of the centre. -/
private theorem exists_verticalSurfaceCoefficients_of_pushforward_class_eq_zero {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (F : Divisor Z) (hFred : MMP.Intersection.IsReducedEffective F)
    (hFex : (F.supp : Set Z) = exceptionalSet r)
    {E : Mori.PrimeDivisor (blowUp I)} (hE : E ∈ F'.support)
    (hEo : ¬ ((E.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹'
      MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)))
    {P : Mori.PrimeDivisor Z} (hP : P ∈ F.support)
    (hEP : (blowUpToBase I).base '' (E.support : Set (blowUp I)) = P.support)
    [IsComplexScheme E.idealSheaf.subscheme] [IsComplexScheme P.idealSheaf.subscheme]
    (ρ : E.idealSheaf.subscheme ⟶ P.idealSheaf.subscheme)
    (hρ : ρ ≫ P.idealSheaf.subschemeι = E.idealSheaf.subschemeι ≫ blowUpToBase I)
    [ρ.IsOver (Spec (.of ℂ))] [IsProper ρ]
    (x : RationalHomology E.idealSheaf.subscheme (2 * 2))
    (hx : (pushforward ℚ (ModuleCat.of ℚ ℚ) (TopCat.ofHom (map (K := ℂ) ρ))
      (isProperMap_map (K := ℂ) ρ) (2 * 2 : ℕ)).hom x = 0) :
    ∃ a ∈ verticalSurfaceCoefficients (blowUpToBase I) F',
      x = Chow.divisorClass _ (surfaceCoefficientDivisor a E) ∧
      ∀ E₂ : Mori.PrimeDivisor (blowUp I), E₂ ≠ E → ¬ ((E₂.support : Set (blowUp I)) ⊆
        blowUpToBase I ⁻¹' MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) →
        surfaceCoefficientDivisor a E₂ = 0 := by
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  set q := blowUpToBase I with hqdef
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  have hvar' : AlgebraicGeometry.IsVariety ℂ (blowUp I ↘ Spec (.of ℂ)) :=
    hM'.comp_eq ▸ hM'.isResolution.2.1
  have : IsIntegral (blowUp I) := hvar'.toIsIntegral
  have hI : I ≠ ⊥ := ne_bot_of_blowUp E.genericPoint
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper q := hqproj.isProper
  have hqc : IsClosedMap q.base := q.isClosedMap
  have hK : IsClosed K := MMP.Resolution.isClosed_componentsOfCodimAtLeastTwo I.support.isClosed
  have hne := stalk_ne_bot_of_ne_bot hI
  haveI hiso : IsIso (q ∣_ ⟨Kᶜ, hK.isOpen_compl⟩) :=
    isIso_blowUpToBase_restrict_complCodimTwo hIc hne
  have hqbir : IsBiregular q ⟨Kᶜ, hK.isOpen_compl⟩ := hiso
  have : NoetherianSpace (blowUp I) := noetherianSpace_of_isComplexScheme
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((blowUp I) ↘ Spec (.of ℂ))
  have hbase : q ≫ (Z ↘ Spec (.of ℂ)) = blowUp I ↘ Spec (.of ℂ) :=
    (inferInstance : q.IsOver (Spec (.of ℂ))).comp_over
  obtain ⟨G, hGred, hGsnc, hGex⟩ := hM.exists_divisor
  have hFG : F = G := eq_of_isReducedEffective_of_supp_eq hFred hGred (hFex.trans hGex.symm)
  rw [← hFG] at hGsnc
  set ιE := E.idealSheaf.subschemeι with hιE
  set ιP := P.idealSheaf.subschemeι with hιP
  haveI : IsIntegral E.idealSheaf.subscheme := E.integral
  haveI : IsIntegral P.idealSheaf.subscheme := P.integral
  have : IsLocallyNoetherian Z := inferInstance
  haveI : IsNormal P.idealSheaf.subscheme := isNormal_subscheme_of_isSNC _ hGsnc hP
  -- generic points
  have hgE : ιE (genericPoint E.idealSheaf.subscheme) = E.genericPoint := by
    have h := MMP.Resolution.closure_subschemeι_genericPoint E.idealSheaf
    have h2 : closure {ιE (genericPoint E.idealSheaf.subscheme)} =
        closure ({E.genericPoint} : Set (blowUp I)) := by
      rw [h, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact (inseparable_iff_closure_eq.2 h2).eq
  have hgP : ιP (genericPoint P.idealSheaf.subscheme) = P.genericPoint := by
    have h := MMP.Resolution.closure_subschemeι_genericPoint P.idealSheaf
    have h2 : closure {ιP (genericPoint P.idealSheaf.subscheme)} =
        closure ({P.genericPoint} : Set Z) := by
      rw [h, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact (inseparable_iff_closure_eq.2 h2).eq
  have hEgK : q E.genericPoint ∉ K := by
    intro h
    apply hEo
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact closure_minimal (Set.singleton_subset_iff.2 h) (hK.preimage q.continuous)
  have hqEP : q E.genericPoint = P.genericPoint := by
    have h : closure ({q E.genericPoint} : Set Z) = closure {P.genericPoint} := by
      rw [← Set.image_singleton, hqc.closure_image_eq_of_continuous q.continuous,
        ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, hEP,
        AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact (inseparable_iff_closure_eq.2 h).eq
  have hcomm : ∀ a, ιP (ρ a) = q (ιE a) := fun a => by
    rw [← Scheme.Hom.comp_apply, hρ, Scheme.Hom.comp_apply]
  have hgen : ρ (genericPoint E.idealSheaf.subscheme) = genericPoint P.idealSheaf.subscheme :=
    ιP.isClosedEmbedding.injective (by rw [hcomm, hgE, hqEP, hgP])
  have hqst : IsIso (q.stalkMap (ιE (genericPoint E.idealSheaf.subscheme))) := by
    have hx : q (ιE (genericPoint E.idealSheaf.subscheme)) ∈ biregularLocus q := by
      rw [hgE]; exact le_biregularLocus hqbir hEgK
    have hiso' : IsIso (q ∣_ biregularLocus q) := isBiregular_biregularLocus q
    have hstalk : IsIso ((q ∣_ biregularLocus q).stalkMap ⟨_, hx⟩) :=
      ((isIso_iff_isIso_stalkMap (q ∣_ biregularLocus q)).mp hiso').2 ⟨_, hx⟩
    exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
      (morphismRestrictStalkMap q (biregularLocus q) ⟨_, hx⟩)).mp hstalk
  have hbir : IsBirational ρ := isBirational_of_comp_eq ρ ιE ιP q hρ hgen hqst
  obtain ⟨hUo, hUiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso ρ hbir).1
    inferInstance
  set U : P.idealSheaf.subscheme.Opens := ⟨MMP.Resolution.Bridges.finiteFibreLocus ρ, hUo⟩
  haveI : IsIso (ρ ∣_ U) := hUiso
  -- the fibres of `ρ` over points off `K` or with closure of dimension `≥ 2` are finite
  have hrangeE : Set.range ιE = (E.support : Set (blowUp I)) := E.idealSheaf.range_subschemeι
  have hfib : ∀ y : P.idealSheaf.subscheme, (ιP y ∉ K ∨
      (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({ιP y} : Set Z))) → y ∈ U := by
    intro y hy
    change (ρ ⁻¹' {y}).Finite
    by_cases hyK : ιP y ∈ K
    · have hy2 : (2 : WithBot ℕ∞) ≤ topologicalKrullDim (closure ({ιP y} : Set Z)) :=
        hy.resolve_left (not_not.2 hyK)
      set S := q ⁻¹' closure ({ιP y} : Set Z) ∩ (E.support : Set (blowUp I)) with hSdef
      have hS : IsClosed S :=
        (isClosed_closure.preimage q.continuous).inter E.idealSheaf.support.isClosed
      have hE3 := topologicalKrullDim_support_eq_three hM'.topologicalKrullDim_eq E
      have hEirr : IsIrreducible (E.support : Set (blowUp I)) := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
      have hSdim : ∀ a ∈ S, topologicalKrullDim (closure ({a} : Set (blowUp I))) ≤
          ((2 : ℕ) : WithBot ℕ∞) := by
        intro a ha
        have hsub : closure ({a} : Set (blowUp I)) ⊆ E.support :=
          closure_minimal (Set.singleton_subset_iff.2 ha.2) E.idealSheaf.support.isClosed
        have hne : closure ({a} : Set (blowUp I)) ≠ E.support := by
          intro h
          have hgS : E.genericPoint ∈ S := by
            have : E.genericPoint ∈ closure ({a} : Set (blowUp I)) := by
              rw [h]
              exact genericPoint_mem_support _
            exact closure_minimal (Set.singleton_subset_iff.2 ha) hS this
          exact hEgK (hK.closure_subset_iff.2 (Set.singleton_subset_iff.2 hyK) hgS.1)
        have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne hEirr isClosed_closure hsub hne
          (by rw [hE3]; simp; decide)
        rw [hE3] at hlt
        exact withBot_le_of_lt_succ (n := 2) hlt
      have hfin := finite_setOf_le_topologicalKrullDim_closure hS hSdim
      refine (hfin.preimage ιE.isClosedEmbedding.injective.injOn).subset ?_
      intro a ha
      have ha' : ρ a = y := ha
      have hqa : q (ιE a) = ιP y := by rw [← hcomm, ha']
      refine ⟨⟨by rw [Set.mem_preimage, hqa]; exact subset_closure rfl,
        hrangeE ▸ ⟨a, rfl⟩⟩, ?_⟩
      by_contra hlt
      push Not at hlt
      have hle : topologicalKrullDim (closure ({ιE a} : Set (blowUp I))) ≤ ((1 : ℕ) : WithBot ℕ∞) :=
        withBot_le_of_lt_succ (n := 1) (by exact_mod_cast hlt)
      have := Stacks.Intersection.ProjectionFormula.topologicalKrullDim_image_le ℂ
        (blowUp I ↘ Spec (.of ℂ)) (Z ↘ Spec (.of ℂ)) q hbase _ isClosed_closure 1 hle
        (closure ({ιP y} : Set Z)) isClosed_closure (by
          rw [← hqa, ← Set.image_singleton, hqc.closure_image_eq_of_continuous q.continuous])
      exact absurd (hy2.trans this) (by norm_num)
    · refine Set.Subsingleton.finite ?_
      intro a ha b hb
      have ha' : ρ a = y := ha
      have hb' : ρ b = y := hb
      apply ιE.isClosedEmbedding.injective
      refine eq_of_isBiregular hqbir (show q (ιE a) ∈ Kᶜ by rw [← hcomm, ha']; exact hyK) ?_
      rw [← hcomm, ← hcomm, ha', hb']
  have hoff : ∀ y : P.idealSheaf.subscheme, y ∉ U → ιP y ∈ K ∧
      topologicalKrullDim (closure ({ιP y} : Set Z)) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
    intro y hy
    refine ⟨by_contra fun hK' => hy (hfib y (Or.inl hK')), ?_⟩
    by_contra h2
    apply hy (hfib y (Or.inr ?_))
    by_contra h3
    push Not at h3
    exact h2 (withBot_le_of_lt_succ (n := 1) (by exact_mod_cast h3))
  -- the points of `E` off `ρ⁻¹ U` have closures of dimension at most two
  have hE3 : topologicalKrullDim E.idealSheaf.subscheme = ((3 : ℕ) : WithBot ℕ∞) := by
    let e := ιE.isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrangeE)
    rw [e.isHomeomorph.topologicalKrullDim_eq]
    exact topologicalKrullDim_support_eq_three hM'.topologicalKrullDim_eq E
  have hdim : ∀ a : E.idealSheaf.subscheme, a ∉ (ρ ⁻¹ᵁ U : E.idealSheaf.subscheme.Opens) →
      topologicalKrullDim (closure ({a} : Set E.idealSheaf.subscheme)) ≤
        ((2 : ℕ) : WithBot ℕ∞) := by
    intro a ha
    have hne : closure ({a} : Set E.idealSheaf.subscheme) ≠ Set.univ := by
      intro h
      have hag : a = genericPoint E.idealSheaf.subscheme :=
        (inseparable_iff_closure_eq.2 (h.trans (genericPoint_spec _).def.symm)).eq
      apply ha
      change ρ a ∈ U
      rw [hag, hgen]
      exact hfib _ (Or.inl (by rw [hgP, ← hqEP]; exact hEgK))
    have hlt := MMP.topologicalKrullDim_lt_of_subset_of_ne
      (IrreducibleSpace.isIrreducible_univ E.idealSheaf.subscheme) isClosed_closure
      (Set.subset_univ _) hne (by
        rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq, hE3]; simp; decide)
    rw [(Homeomorph.Set.univ _).isHomeomorph.topologicalKrullDim_eq, hE3] at hlt
    exact withBot_le_of_lt_succ (n := 2) hlt
  obtain ⟨N, hxN, hNsupp⟩ := exists_rationalCycleClass_eq_of_pushforward_eq_zero ρ U hdim x hx
  -- an edge for every surface of `N`
  set S := ((rationalPointBasis E.idealSheaf.subscheme 2).repr N).support with hSdef
  have hedge : ∀ V ∈ S, ∃ σ : DoubleSurface F', ∃ D : Mori.PrimeDivisor
      E.idealSheaf.subscheme, σ.fst = E ∧ (σ.snd.support : Set (blowUp I)) ⊆ q ⁻¹' K ∧
      σ.carrier = closure {ιE D.genericPoint} ∧
      Chow.divisorCycle _ (Finsupp.single D 1) =
        Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
          (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) V.1 V.2 ∧
      topologicalKrullDim (q.base '' σ.carrier) ≤ 1 := by
    intro V hV
    have hcoh := coheight_genericPoint_eq_one_of_isModel sY (q ≫ r) hM' E V.1 V.2
    set D : Mori.PrimeDivisor E.idealSheaf.subscheme :=
      AlgebraicGeometry.PrimeDivisor.ofCoheightOne V.1 hcoh with hDdef
    have hDv : D.genericPoint = V.1 :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
    have hNv : Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ)
        (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) V.1 N ≠ 0 := by
      rw [rationalCoeff_eq_repr]
      exact Finsupp.mem_support_iff.1 hV
    have hvoff : V.1 ∉ (ρ ⁻¹ᵁ U : E.idealSheaf.subscheme.Opens) :=
      hNsupp V.1 hNv (subset_closure rfl)
    obtain ⟨hK', hdim1⟩ := hoff (ρ V.1) hvoff
    set y' := ιE V.1 with hy'def
    have hqy' : q y' = ιP (ρ V.1) := (hcomm V.1).symm
    have hV2 : topologicalKrullDim (closure ({V.1} : Set E.idealSheaf.subscheme)) =
        ((2 : ℕ) : WithBot ℕ∞) :=
      Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
        ℂ _ V.1 2 V.2
    have hy'2 : topologicalKrullDim (closure ({y'} : Set (blowUp I))) =
        ((2 : ℕ) : WithBot ℕ∞) := by
      rw [topologicalKrullDim_closure_image ιE.isClosedEmbedding V.1, hV2]
    obtain ⟨J, hJ, hJC, hy'J, hCK⟩ := exists_new_component sY r hM I hIs hIc hM' F' hF'ex
      (show q y' ∈ K by rw [hqy']; exact hK')
    have hJK : (J.support : Set (blowUp I)) ⊆ q ⁻¹' K := hJC.trans (Set.preimage_mono hCK)
    have hEJ : E ≠ J := fun h => hEo (h ▸ hJK)
    have hy'E : y' ∈ (E.support : Set (blowUp I)) := hrangeE ▸ ⟨V.1, rfl⟩
    obtain ⟨σ, hσf, hσs, hσc, -⟩ := exists_doubleSurface_of_mem sY (q ≫ r) hM' F' hF'red
      hF'ex hE hJ hEJ hy'E hy'J (by rw [hy'2]; norm_num)
    refine ⟨σ, D, hσf, hσs ▸ hJK, by rw [hσc, hDv], ?_, ?_⟩
    · rw [Chow.divisorCycle_single, one_smul, primeDivisorCycle_eq_rationalPointCycle D hDv V.2]
    · have himg : q.base '' closure ({y'} : Set (blowUp I)) = closure {ιP (ρ V.1)} := by
        rw [← hqc.closure_image_eq_of_continuous q.continuous, Set.image_singleton, hqy']
      rw [hσc, himg]
      exact_mod_cast hdim1
  choose σf Df hσf hσs hσc hDV hσd using hedge
  set c : _ → ℚ := fun V : {v : E.idealSheaf.subscheme // Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) v = 2} =>
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ)
      (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) V.1 N with hcdef
  refine ⟨∑ V ∈ S.attach, edgeSystem (σf V.1 V.2) (c V.1),
    Submodule.sum_mem _ fun V _ => edgeSystem_mem_vertical q _ _ (hσd V.1 V.2), ?_, ?_⟩
  · have hZ : surfaceCoefficientDivisor (∑ V ∈ S.attach,
        edgeSystem (σf V.1 V.2) (c V.1)) E =
        ∑ V ∈ S.attach, Finsupp.single (Df V.1 V.2) (c V.1) := by
      change surfaceCoefficientDivisorLinearMap F' E _ = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun V _ =>
        surfaceCoefficientDivisor_edgeSystem_of_eq _ _ (hσf V.1 V.2) _ (hσc V.1 V.2)
    change x = Chow.rationalCycleClass _ 2 (Chow.divisorCycle _ (surfaceCoefficientDivisor _ E))
    rw [hZ, map_sum, hxN]
    congr 1
    have hterm : ∀ V : S, Chow.divisorCycle _ (Finsupp.single (Df V.1 V.2) (c V.1)) =
        c V.1 • Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ)
          (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) V.1.1 V.1.2 := by
      intro V
      rw [show Finsupp.single (Df V.1 V.2) (c V.1) = c V.1 • Finsupp.single (Df V.1 V.2) 1 by
        simp, map_smul, hDV V.1 V.2]
    simp_rw [hterm]
    rw [Finset.sum_attach S (fun V => c V • Chow.rationalPointCycle
      (Stacks.Chow.fieldChowSituation ℂ) (E.idealSheaf.subscheme ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ)
        V.1 V.2)]
    exact rationalCycle_eq_sum N
  · intro E₂ hE₂ hE₂o
    change surfaceCoefficientDivisorLinearMap F' E₂ _ = 0
    rw [map_sum]
    refine Finset.sum_eq_zero fun V _ => ?_
    exact surfaceCoefficientDivisor_edgeSystem_of_ne _ _ (by rw [hσf V.1 V.2]; exact hE₂)
      (fun h => hE₂o (h ▸ hσs V.1 V.2))

/-- Push-forwards along the two sides of a commutative square agree. -/
private theorem rationalPushforward_rationalPushforward_eq {A B C D : Scheme.{0}}
    [A.Over (Spec (.of ℂ))] [LocallyOfFiniteType (A ↘ Spec (.of ℂ))] [B.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (B ↘ Spec (.of ℂ))] [C.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (C ↘ Spec (.of ℂ))] [D.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (D ↘ Spec (.of ℂ))] (f : A ⟶ B) (g : B ⟶ D) (f' : A ⟶ C)
    (g' : C ⟶ D) [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] [f'.IsOver (Spec (.of ℂ))]
    [g'.IsOver (Spec (.of ℂ))] [IsProper f] [IsProper g] [IsProper f'] [IsProper g']
    (h : f ≫ g = f' ≫ g') (k : ℕ) (L : RatCycles A k) :
    ratPush g k (ratPush f k L) =
      ratPush g' k (ratPush f' k L) := by
  rw [← rationalPushforward_comp, ← rationalPushforward_comp, rationalPushforward_congr h]

open Classical in
/-- The surface cycle `[S]` of a double surface whose surface `S` is the closure of a point of
delta-dimension two, `0` otherwise. -/
private noncomputable def surfaceCycle {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {F : Divisor Z} (σ : DoubleSurface F) : RatCycles Z 2 :=
  if h : ∃ w : Z, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w =
        ((2 : ℕ) : ℤ) ∧ closure {w} = σ.carrier then
    Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ)
      h.choose h.choose_spec.1
  else 0

private theorem surfaceCycle_eq_single {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {F : Divisor Z} (σ : DoubleSurface F) (w : Z)
    (hw : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Z ↘ Spec (.of ℂ)) w = ((2 : ℕ) : ℤ)) (hW : closure ({w} : Set Z) = σ.carrier) :
    surfaceCycle σ =
      Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ)
        w hw := by
  classical
  have h : ∃ w : Z, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w =
        ((2 : ℕ) : ℤ) ∧ closure {w} = σ.carrier := ⟨w, hw, hW⟩
  unfold surfaceCycle
  rw [dif_pos h]
  exact rationalPointCycle_congr
    (inseparable_iff_closure_eq.2 (h.choose_spec.2.trans hW.symm)).eq _ _

open Classical in
private theorem rationalCoeff_surfaceCycle {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {F : Divisor Z} (σ : DoubleSurface F) (w : Z)
    (hw : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Z ↘ Spec (.of ℂ)) w = ((2 : ℕ) : ℤ)) :
    Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) w
        (surfaceCycle σ) = if closure ({w} : Set Z) = σ.carrier then 1 else 0 := by
  by_cases hW : closure ({w} : Set Z) = σ.carrier
  · rw [surfaceCycle_eq_single σ w hw hW, Chow.rationalCoeff_rationalPointCycle, if_pos rfl,
      if_pos hW]
  · rw [if_neg hW]
    unfold surfaceCycle
    split_ifs with h
    · rw [Chow.rationalCoeff_rationalPointCycle, if_neg]
      rintro rfl
      exact hW h.choose_spec.2
    · rw [map_zero]

private theorem surfaceCycle_swap {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {F : Divisor Z} (σ : DoubleSurface F) : surfaceCycle σ.swap = surfaceCycle σ := rfl

open Classical in
/-- **The push-forward of `Z_P(b)` to the ambient scheme as a sum over double surfaces.** -/
private theorem rationalPushforward_divisorCycle_eq_sum {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] {F : Divisor Z} [Fintype (DoubleSurface F)] (b : DoubleSurface F → ℚ)
    (P : Mori.PrimeDivisor Z)
    (hP : ∀ v : P.idealSheaf.subscheme, Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (P.idealSheaf.subscheme ↘ Spec (.of ℂ)) v = 2 → Order.coheight v = 1) :
    ratPush P.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor b P)) =
      ∑ σ, if σ.fst = P then b σ • surfaceCycle σ else 0 := by
  refine rationalCycle_ext fun w => ?_
  rw [map_sum]
  by_cases hw : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Z ↘ Spec (.of ℂ)) w = 2
  · have key : ∀ (p : DoubleSurface F → Prop), ∑ᶠ x : {σ // p σ}, b x =
        ∑ σ, if p σ then b σ else 0 := by
      intro p
      rw [finsum_eq_sum_of_fintype, ← Finset.sum_filter,
        Finset.sum_subtype (Finset.univ.filter p) (p := p) (by simp)]
    rw [rationalCoeff_rationalProperPushforward_divisorCycle b P hP w hw, key]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases h1 : σ.fst = P
    · rw [if_pos h1, map_smul, rationalCoeff_surfaceCycle σ w hw, smul_eq_mul]
      by_cases h2 : σ.carrier = closure {w}
      · rw [if_pos ⟨h1, h2⟩, if_pos h2.symm, mul_one]
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.symm), mul_zero]
    · rw [if_neg (fun h => h1 h.1), if_neg h1, map_zero]
  · rw [rationalCoeff_eq_zero_of_relativeDimension_ne _ w hw]
    refine (Finset.sum_eq_zero fun σ _ => ?_).symm
    split_ifs
    · rw [map_smul, rationalCoeff_eq_zero_of_relativeDimension_ne _ w hw, smul_zero]
    · rw [map_zero]

open Classical in
/-- **Lifting an old vertical oriented system.** Given an old component `e P` over every
component `P` of the old boundary, every vertical oriented system `b` of the old boundary lifts
to a vertical oriented system of the new boundary whose divisors push forward, component by
component, to the halved signed sums of the surfaces of `b`. -/
private theorem exists_lift {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)] [IsComplexScheme Z]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (F : Divisor Z) [Fintype (DoubleSurface F)] (e : F.support → F'.support)
    (he : ∀ P, ¬ (((e P).1.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) ∧
      (blowUpToBase I).base '' ((e P).1.support : Set (blowUp I)) = P.1.support)
    (b : DoubleSurface F → ℚ) (hb : b ∈ verticalSurfaceCoefficients r F) :
    ∃ a ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F', ∀ E : F'.support,
      ratPush (blowUpToBase I) 2 (ratPush E.1.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1))) =
      ∑ σ, (b σ / 2) • (((if E.1 = (e ⟨σ.fst, σ.fst_mem⟩).1 then 1 else 0) -
        (if E.1 = (e ⟨σ.snd, σ.snd_mem⟩).1 then 1 else 0) : ℚ) • surfaceCycle σ) := by
  have hpush : ∀ (ℓ : DoubleSurface F' → ℚ) (E : F'.support),
      ratPush (blowUpToBase I) 2 (ratPush E.1.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor ℓ E.1))) =
      (ratPush (blowUpToBase I) 2 ∘ₗ ratPush E.1.idealSheaf.subschemeι 2 ∘ₗ
        Chow.divisorCycle _ ∘ₗ surfaceCoefficientDivisorLinearMap F' E.1) ℓ := fun _ _ => rfl
  have hℓ : ∀ σ : DoubleSurface F, ∃ ℓ ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F',
      ∀ E : F'.support,
      ratPush (blowUpToBase I) 2 (ratPush E.1.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor ℓ E.1))) =
      (b σ / 2) • (((if E.1 = (e ⟨σ.fst, σ.fst_mem⟩).1 then 1 else 0) -
        (if E.1 = (e ⟨σ.snd, σ.snd_mem⟩).1 then 1 else 0) : ℚ) • surfaceCycle σ) := by
    intro σ
    by_cases h : b σ ≠ 0 ∧ ∃ w : Z, Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w =
          ((2 : ℕ) : ℤ) ∧ closure {w} = σ.carrier
    · obtain ⟨w, hw, hW⟩ := h.2
      obtain ⟨ℓ, hℓv, hℓ⟩ := exists_lift_edge sY r hM I hIs hIc hM' F' hF'red hF'ex F σ
        (hb.2 σ h.1) w hw hW (e ⟨σ.fst, σ.fst_mem⟩).2 (e ⟨σ.snd, σ.snd_mem⟩).2
        (he _).1 (he _).1 (he _).2 (he _).2
      refine ⟨(b σ / 2) • ℓ, Submodule.smul_mem _ _ hℓv, fun E => ?_⟩
      rw [hpush, map_smul, ← hpush, hℓ E, surfaceCycle_eq_single σ w hw hW]
    · refine ⟨0, Submodule.zero_mem _, fun E => ?_⟩
      rw [hpush, map_zero]
      by_cases hb0 : b σ = 0
      · rw [hb0, zero_div, zero_smul]
      · have hnW : ¬ ∃ w : Z, Stacks.Chow.relativeDimension
            (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w =
              ((2 : ℕ) : ℤ) ∧ closure {w} = σ.carrier :=
          fun hW => h ⟨hb0, hW⟩
        rw [surfaceCycle, dif_neg hnW, smul_zero, smul_zero]
  choose ℓ hℓv hℓ using hℓ
  refine ⟨∑ σ, ℓ σ, Submodule.sum_mem _ fun σ _ => hℓv σ, fun E => ?_⟩
  rw [hpush, map_sum]
  exact Finset.sum_congr rfl fun σ _ => by rw [← hpush, hℓ σ E]

open Classical in
/-- **The halved signed sum over double surfaces.** For an oriented system `b`, summing
`(b_σ / 2) ([σ_1 = P] - [σ_2 = P]) [S_σ]` over all double surfaces counts every double surface of
`P` once. -/
private theorem sum_half_signed_eq {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    {F : Divisor Z} [Fintype (DoubleSurface F)]
    (b : DoubleSurface F → ℚ) (hb : b ∈ orientedSurfaceCoefficients F)
    (c₁ c₂ : DoubleSurface F → Prop) (P : Mori.PrimeDivisor Z) (hc₁ : ∀ σ, c₁ σ ↔ σ.fst = P)
    (hc₂ : ∀ σ, c₂ σ ↔ σ.snd = P) :
    ∑ σ : DoubleSurface F, (b σ / 2) • (((if c₁ σ then 1 else 0) -
        (if c₂ σ then 1 else 0) : ℚ) • surfaceCycle σ) =
      ∑ σ, if σ.fst = P then b σ • surfaceCycle σ else 0 := by
  simp_rw [hc₁, hc₂]
  have h1 : ∀ σ : DoubleSurface F, (b σ / 2) • (((if σ.fst = P then 1 else 0) -
      (if σ.snd = P then 1 else 0) : ℚ) • surfaceCycle σ) =
      (1 / 2 : ℚ) • (if σ.fst = P then b σ • surfaceCycle σ else 0) -
        (1 / 2 : ℚ) • (if σ.snd = P then b σ • surfaceCycle σ else 0) := by
    intro σ
    split_ifs <;> module
  have h2 : ∑ σ : DoubleSurface F, (if σ.snd = P then b σ • surfaceCycle σ else 0) =
      -∑ σ : DoubleSurface F, (if σ.fst = P then b σ • surfaceCycle σ else 0) := by
    rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (DoubleSurface.swap_swap (B := F))),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    change (if σ.swap.snd = P then b σ.swap • surfaceCycle σ.swap else 0) = _
    rw [DoubleSurface.swap_snd, surfaceCycle_swap, hb σ]
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, h2]
  module

/-- **The strict transforms of the old components.** After a blow-up `q` along a nonzero
boundary-compatible smooth centre, every component `P` of `F` is the image of exactly one
component `e(P)` of the new boundary not lying over the codimension-`≥ 2` part `K` of the centre;
the components not over `K` are exactly the `e(P)`, and `q` maps `e(P)` into `P`. -/
private theorem exists_strictTransform {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)] (hI : I ≠ ⊥)
    (F : Divisor Z) (hFex : (F.supp : Set Z) = exceptionalSet r)
    (F' : Divisor (blowUp I))
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r)) :
    ∃ e : F.support → F'.support,
      (∀ P, ¬ (((e P).1.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) ∧
        (blowUpToBase I).base '' ((e P).1.support : Set (blowUp I)) = P.1.support) ∧
      (∀ E : F'.support, ¬ ((E.1.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) → ∃ P, E = e P) ∧
      Function.Injective e ∧
      ∀ P, P.1.idealSheaf ≤ (e P).1.idealSheaf.map (blowUpToBase I) := by
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  set q := blowUpToBase I with hqdef
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper q := hqproj.isProper
  have hqc : IsClosedMap q.base := q.isClosedMap
  have hK : IsClosed K := MMP.Resolution.isClosed_componentsOfCodimAtLeastTwo I.support.isClosed
  have hne := stalk_ne_bot_of_ne_bot hI
  haveI hiso : IsIso (q ∣_ ⟨Kᶜ, hK.isOpen_compl⟩) :=
    isIso_blowUpToBase_restrict_complCodimTwo hIc hne
  have hqbir : IsBiregular q ⟨Kᶜ, hK.isOpen_compl⟩ := hiso
  have hKcod : ∀ W : IrreducibleCloseds Z, (W : Set Z) ⊆ K → 2 ≤ codimension W :=
    fun W hW => two_le_codimension_of_subset I.support.isClosed W hW
  have hqs : Function.Surjective q := surjective_blowUpToBase hIc hI hqc
  have : IsProper r := isProper_of_isProjectiveMorphism r hM.isResolution.2.2.2.1
  have hrc : IsClosedMap r.base := r.isClosedMap
  have hold : ∀ E : F'.support, ¬ ((E.1.support : Set (blowUp I)) ⊆ q ⁻¹' K) →
      ∃ P ∈ F.support, q.base '' (E.1.support : Set (blowUp I)) = P.support :=
    fun E hE => exists_image_eq_of_not_subset q hqc r hrc hK hqbir hFex hF'ex E.2 hE
  have hsurjF : ∀ P : F.support, ∃ E : F'.support,
      ¬ ((E.1.support : Set (blowUp I)) ⊆ q ⁻¹' K) ∧
      q.base '' (E.1.support : Set (blowUp I)) = P.1.support := by
    intro P
    obtain ⟨E, hE, hEo, hPE⟩ := exists_mem_support_subset_image q hqs hqc r hFex hF'ex hK hKcod P.2
    obtain ⟨P', -, hEP'⟩ := hold ⟨E, hE⟩ hEo
    have hPP' : P.1 = P' := by
      apply eq_of_genericPoint_mem_support
      rw [← hEP']
      apply hPE
      exact genericPoint_mem_support _
    exact ⟨⟨E, hE⟩, hEo, hEP'.trans (by rw [hPP'])⟩
  choose e he using hsurjF
  have he' : ∀ E : F'.support, ¬ ((E.1.support : Set (blowUp I)) ⊆ q ⁻¹' K) →
      ∃ P, E = e P := by
    intro E hE
    obtain ⟨P, hP, hEP⟩ := hold E hE
    refine ⟨⟨P, hP⟩, Subtype.ext (eq_of_image_eq_of_not_subset q hqc hK hqbir hE ?_)⟩
    rw [hEP, (he ⟨P, hP⟩).2]
  have he_inj : Function.Injective e := by
    intro P₁ P₂ h
    have h' : (P₁.1.support : Set Z) = P₂.1.support := by
      rw [← (he P₁).2, ← (he P₂).2, h]
    apply Subtype.ext
    apply eq_of_genericPoint_mem_support
    rw [← h']
    exact genericPoint_mem_support _
  refine ⟨e, he, he', he_inj, fun P => ?_⟩
  rw [← MMP.Intersection.vanishingIdeal_support_idealSheaf (e P).1,
    Scheme.IdealSheafData.map_vanishingIdeal,
    ← MMP.Intersection.vanishingIdeal_support_idealSheaf P.1]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  change closure _ ⊆ (P.1.support : Set Z)
  rw [← (he P).2, (hqc _ (e P).1.idealSheaf.support.isClosed).closure_eq]

/-- **Lifting old boundaries and the threefold blow-up kernels.** Let a family of vertical
rational surface cycles on the new boundary, with vanishing ambient class sum, have cycles on the
components over the codimension-`≥ 2` part of the centre pushing forward to zero, and push-downs
to the old components whose classes are those of a vertical oriented system of `F`. Then on the
other components it is, class by class, the divisor of a vertical oriented system which pushes
forward to zero on the components over that part. -/
private theorem exists_verticalSurfaceCoefficients_of_pushforward_eq_zero {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hY : MMP.Mori.IsProjectiveVariety ℂ (Y ↘ Spec (.of ℂ))) (hYQ : IsQFactorial (Y ↘ Spec (.of ℂ)))
    (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r] (hM : IsModel (Y ↘ Spec (.of ℂ)) r)
    (F : Divisor Z) (hFred : MMP.Intersection.IsReducedEffective F)
    (hFex : (F.supp : Set Z) = exceptionalSet r)
    (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel (Y ↘ Spec (.of ℂ)) (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    [IsProper (blowUpToBase I)] [IsProper (blowUpToBase I ≫ r)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (L : ∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2)
    (hL : ∀ E : F'.support, ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I ≫ r) 2 (L E) = 0)
    (hsum : ∑ E : F'.support, componentHomologyMap E.1 4 (Chow.rationalCycleClass _ 2 (L E)) = 0)
    (hN : ∀ E : F'.support, E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
      ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2 (L E) = 0)
    (hB : ∃ b ∈ verticalSurfaceCoefficients r F, ∀ (P : F.support) (E : F'.support),
      ¬ (E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) →
      (blowUpToBase I).base '' (E.1.support : Set (blowUp I)) = P.1.support →
      ∀ (ρ : E.1.idealSheaf.subscheme ⟶ P.1.idealSheaf.subscheme) [ρ.IsOver (Spec (.of ℂ))]
        [IsProper ρ],
        ρ ≫ P.1.idealSheaf.subschemeι = E.1.idealSheaf.subschemeι ≫ blowUpToBase I →
        Chow.rationalCycleClass _ 2 (ratPush ρ 2 (L E)) =
          Chow.divisorClass _ (surfaceCoefficientDivisor b P.1)) :
    ∃ a ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F',
      (∀ E : F'.support, E.1.support ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
        ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2
          (Chow.divisorCycle _ (surfaceCoefficientDivisor a E.1)) = 0) ∧
      ∀ E : F'.support, ¬ (E.1.support ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) →
        Chow.rationalCycleClass _ 2 (L E) = Chow.divisorClass _ (surfaceCoefficientDivisor a E.1) := by
  haveI : IsComplexScheme Y :=
    MMP.Analytic.isComplexScheme_of_isProjective Y hY.isProjective.isProjective
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  set q := blowUpToBase I with hqdef
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  have hvar' : AlgebraicGeometry.IsVariety ℂ (blowUp I ↘ Spec (.of ℂ)) :=
    hM'.comp_eq ▸ hM'.isResolution.2.1
  have : IsIntegral (blowUp I) := hvar'.toIsIntegral
  by_cases hI : I = ⊥
  · subst hI
    have := isEmpty_blowUp_bot Z
    refine ⟨0, Submodule.zero_mem _, fun E => isEmptyElim E.1.genericPoint,
      fun E => isEmptyElim E.1.genericPoint⟩
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper q := hqproj.isProper
  have hqc : IsClosedMap q.base := q.isClosedMap
  have hrc : IsClosedMap r.base := r.isClosedMap
  have : NoetherianSpace (blowUp I) := noetherianSpace_of_isComplexScheme
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((blowUp I) ↘ Spec (.of ℂ))
  haveI : Finite (DoubleSurface F) := DoubleSurface.finite
  letI : Fintype (DoubleSurface F) := Fintype.ofFinite _
  obtain ⟨e, he, he', he_inj, hH⟩ :=
    exists_strictTransform (Y ↘ Spec (.of ℂ)) r hM I hIs hIc hM' hI F hFex F' hF'ex
  set ρ : ∀ P : F.support, (e P).1.idealSheaf.subscheme ⟶ P.1.idealSheaf.subscheme :=
    fun P => Scheme.IdealSheafData.subschemeMap _ _ q (hH P) with hρdef
  have hρ : ∀ P, ρ P ≫ P.1.idealSheaf.subschemeι = (e P).1.idealSheaf.subschemeι ≫ q :=
    fun P => Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have hρover : ∀ P, (ρ P).IsOver (Spec (.of ℂ)) := fun P => ⟨by
    change ρ P ≫ P.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ)) = _
    rw [← Category.assoc, hρ, Category.assoc,
      (inferInstance : q.IsOver (Spec (.of ℂ))).comp_over]
    rfl⟩
  have hρprop : ∀ P, IsProper (ρ P) := fun P => by
    haveI : IsProper (ρ P ≫ P.1.idealSheaf.subschemeι) := by rw [hρ]; infer_instance
    exact IsProper.of_comp (ρ P) P.1.idealSheaf.subschemeι
  have hcxE : ∀ E : Mori.PrimeDivisor (blowUp I), IsComplexScheme E.idealSheaf.subscheme :=
    fun E => IsComplexScheme.of_isClosedImmersion E.idealSheaf.subschemeι
  have hcxP : ∀ P : Mori.PrimeDivisor Z, IsComplexScheme P.idealSheaf.subscheme :=
    fun P => IsComplexScheme.of_isClosedImmersion P.idealSheaf.subschemeι
  -- the square `ι_P ∘ ρ_P = q ∘ ι_E` on cycles
  have hsq : ∀ (P : F.support) (M : RatCycles (e P).1.idealSheaf.subscheme 2),
      ratPush P.1.idealSheaf.subschemeι 2 (ratPush (ρ P) 2 M) =
        ratPush q 2 (ratPush (e P).1.idealSheaf.subschemeι 2 M) := by
    intro P M
    haveI := hρover P; haveI := hρprop P; haveI := hcxE (e P).1; haveI := hcxP P.1
    exact rationalPushforward_rationalPushforward_eq _ _ _ _ (hρ P) 2 M
  -- the push-downs
  set LP : ∀ P : F.support, RatCycles P.1.idealSheaf.subscheme 2 :=
    fun P => ratPush (ρ P) 2 (L (e P)) with hLPdef
  obtain ⟨b, hb, hbL'⟩ := hB
  have hbL : ∀ P : F.support, Chow.rationalCycleClass _ 2 (LP P) =
      Chow.divisorClass _ (surfaceCoefficientDivisor b P.1) := fun P => by
    haveI := hρover P; haveI := hρprop P
    exact hbL' P (e P) (he P).1 (he P).2 (ρ P) (hρ P)
  -- the lift of `b`
  obtain ⟨a₁, ha₁, hlift⟩ := exists_lift (Y ↘ Spec (.of ℂ)) r hM I hIs hIc hM' F' hF'red hF'ex F e he b hb
  have hcond : ∀ (P : F.support) (P' : Mori.PrimeDivisor Z) (hP' : P' ∈ F.support),
      (e P).1 = (e ⟨P', hP'⟩).1 ↔ P' = P.1 := by
    intro P P' hP'
    refine ⟨fun h ↦ (congrArg Subtype.val (he_inj (Subtype.ext h))).symm, fun h ↦ ?_⟩
    rw [show (⟨P', hP'⟩ : F.support) = P from Subtype.ext h]
  have hcmp : ∀ P : F.support, ratPush (ρ P) 2
      (Chow.divisorCycle _ (surfaceCoefficientDivisor a₁ (e P).1)) =
      Chow.divisorCycle _ (surfaceCoefficientDivisor b P.1) := by
    intro P
    apply rationalProperPushforward_injective_of_isClosedImmersion P.1.idealSheaf.subschemeι 2
    rw [hsq, hlift (e P), rationalPushforward_divisorCycle_eq_sum b P.1
      (coheight_genericPoint_eq_one_of_isModel (Y ↘ Spec (.of ℂ)) r hM P.1)]
    exact sum_half_signed_eq b hb.1 _ _ P.1 (fun σ => hcond P σ.fst σ.fst_mem)
      (fun σ => hcond P σ.snd σ.snd_mem)
  -- the threefold kernels
  have hker : ∀ P : F.support, ∃ a ∈ verticalSurfaceCoefficients q F',
      Chow.rationalCycleClass _ 2 (L (e P)) - Chow.divisorClass _ (surfaceCoefficientDivisor a₁ (e P).1) =
        Chow.divisorClass _ (surfaceCoefficientDivisor a (e P).1) ∧
      ∀ E₂ : Mori.PrimeDivisor (blowUp I), E₂ ≠ (e P).1 →
        ¬ ((E₂.support : Set (blowUp I)) ⊆ q ⁻¹' K) → surfaceCoefficientDivisor a E₂ = 0 := by
    intro P
    haveI := hρover P; haveI := hρprop P; haveI := hcxE (e P).1; haveI := hcxP P.1
    exact exists_verticalSurfaceCoefficients_of_pushforward_class_eq_zero (Y ↘ Spec (.of ℂ)) r
      hM I hIs hIc hM' F' hF'red hF'ex F hFred hFex (e P).2 (he P).1 P.2 (he P).2 (ρ P) (hρ P)
      (Chow.rationalCycleClass _ 2 (L (e P)) - Chow.divisorClass _ (surfaceCoefficientDivisor a₁ (e P).1))
      (by
        rw [map_sub]
        change (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (ρ P)))
            (UnderlyingSpace.isProperMap_map (K := ℂ) (ρ P)) (2 * 2 : ℕ)).hom
            (Chow.rationalCycleClass _ 2 (L (e P))) -
          (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (ρ P)))
            (UnderlyingSpace.isProperMap_map (K := ℂ) (ρ P)) (2 * 2 : ℕ)).hom
            (Chow.rationalCycleClass _ 2 (Chow.divisorCycle _ (surfaceCoefficientDivisor a₁ (e P).1))) = 0
        rw [← Chow.rationalCycleClass_rationalProperPushforward, ← Chow.rationalCycleClass_rationalProperPushforward,
          hcmp P]
        change Chow.rationalCycleClass _ 2 (LP P) - _ = 0
        rw [hbL P]
        exact sub_self _)
  choose a₂ ha₂v ha₂x ha₂o using hker
  haveI := hvarZ
  haveI : AlgebraicGeometry.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := hY.toIsVariety
  have ha₂v' : ∀ P, a₂ P ∈ verticalSurfaceCoefficients (q ≫ r) F' := fun P =>
    verticalSurfaceCoefficients_le_comp q r hqc hrc (Z ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) hM.comp_eq F' (ha₂v P)
  have hZsum : ∀ E : Mori.PrimeDivisor (blowUp I),
      surfaceCoefficientDivisor (a₁ + ∑ P, a₂ P) E =
        surfaceCoefficientDivisor a₁ E + ∑ P, surfaceCoefficientDivisor (a₂ P) E := fun E => by
    change surfaceCoefficientDivisorLinearMap F' E _ = _
    rw [map_add, map_sum]
    rfl
  refine ⟨a₁ + ∑ P, a₂ P, add_mem ha₁ (Submodule.sum_mem _ fun P _ => ha₂v' P), ?_, ?_⟩
  · intro E hE
    haveI := hcxE E.1
    rw [hZsum, map_add, map_sum, map_add, map_sum]
    have h1 : ratPush (E.1.idealSheaf.subschemeι ≫ q) 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor a₁ E.1)) = 0 := by
      rw [rationalPushforward_comp, hlift E]
      refine Finset.sum_eq_zero fun σ _ => ?_
      rw [if_neg (fun h => (he _).1 (h ▸ hE)), if_neg (fun h => (he _).1 (h ▸ hE)), sub_self,
        zero_smul, smul_zero]
    rw [h1, zero_add]
    exact Finset.sum_eq_zero fun P _ =>
      rationalPushforward_divisorCycle_eq_zero_of_mem_vertical q hqc F' (ha₂v P) E.1
  · intro E hE
    obtain ⟨P₀, rfl⟩ := he' E hE
    rw [hZsum, map_add, map_sum,
      Finset.sum_eq_single P₀ (fun P _ hP => by
        rw [ha₂o P (e P₀).1 (fun h => hP (he_inj (Subtype.ext h)).symm) (he P₀).1, map_zero])
        (by simp),
      ← ha₂x P₀, add_sub_cancel]

/-! ### Supports of push-forwards and the classes of top cycles -/

/-- On a projective complex variety, the class `cl_X(x)` of the prime cycle of a point is nonzero
(`MMP.Analytic.fundamentalClass_ne_zero`, the transport of `cl_X(x)` to the complex points). -/
private theorem rationalCycleClass_rationalPointCycle_ne_zero {X : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [IsComplexScheme X]
    (hX : MMP.Mori.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))) {k : ℕ} (x : X)
    (hx : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (X ↘ Spec (.of ℂ)) x = k) :
    Chow.rationalCycleClass X k
      (Chow.rationalPointCycle (Stacks.Chow.fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k x hx) ≠
      0 := by
  rw [Chow.rationalCycleClass_rationalPointCycle]
  exact fun h ↦ MMP.Analytic.fundamentalClass_ne_zero hX x hx
    (by rw [MMP.Analytic.fundamentalClass, h]; exact map_zero _)

/-- A model is a projective complex variety. -/
private theorem isProjectiveVariety_of_isModel {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) :
    MMP.Mori.IsProjectiveVariety ℂ (Z ↘ Spec (.of ℂ)) := by
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  haveI := Stacks.Ample.isInvertibleModule_unit (Spec (.of ℂ))
  refine (MMP.Mori.isProjectiveVariety_iff ℂ _).2 ⟨hvarZ, ?_⟩
  exact isProjectiveMorphism_of_isProjective _ (Stacks.Ample.unitModule (Spec (.of ℂ)))
    (Stacks.Ample.isAmple_unitModule_of_isAffine (Spec (.of ℂ))) hM.isProjective

/-- **The class of a cycle on a new component determines its push-forward.** On a component `E`
of the new boundary over the codimension-`≥ 2` part `C` of the centre, a rational surface cycle
with zero class in `H_4(E, ℚ)` pushes forward to the zero cycle on `Z`: its push-forward is a
multiple of the surface `q(E)` (or zero), and the class of a surface in the projective fourfold `Z`
is nonzero. -/
private theorem rationalPushforward_eq_zero_of_rationalCycleClass_eq_zero {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    [IsComplexScheme (blowUp I)]
    (E : Mori.PrimeDivisor (blowUp I)) (hEN : E.support ⊆ blowUpToBase I ⁻¹'
      MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z))
    (N : RatCycles E.idealSheaf.subscheme 2)
    (hN : Chow.rationalCycleClass _ 2 N = 0) :
    ratPush (E.idealSheaf.subschemeι ≫ blowUpToBase I) 2 N = 0 := by
  by_contra hc
  have := hM.isComplexScheme
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  have hI : I ≠ ⊥ := ne_bot_of_blowUp E.genericPoint
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper (blowUpToBase I) := hqproj.isProper
  have hqc : IsClosedMap (blowUpToBase I).base := (blowUpToBase I).isClosedMap
  have hZ4 : topologicalKrullDim Z = ((4 : ℕ) : WithBot ℕ∞) := by
    rw [hM.topologicalKrullDim_eq]; rfl
  haveI : IsComplexScheme E.idealSheaf.subscheme :=
    IsComplexScheme.of_isClosedImmersion E.idealSheaf.subschemeι
  obtain ⟨w₀, hw₀, -, t, ht, hct⟩ := exists_eq_smul_single_of_ne_zero hZ4 (blowUpToBase I) hqc E
    (topologicalKrullDim_image_le_two sY r hM I E hEN) N hc
  have h1 : Chow.rationalCycleClass Z 2
      (ratPush (E.idealSheaf.subschemeι ≫ blowUpToBase I) 2 N) = 0 := by
    rw [Chow.rationalCycleClass_rationalProperPushforward, hN, map_zero]
  rw [hct, map_smul, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact ht h1
  · exact rationalCycleClass_rationalPointCycle_ne_zero (isProjectiveVariety_of_isModel sY r hM)
      w₀ hw₀ h1

/-! ### Pushing oriented systems down -/

open Classical in
/-- **Surface cycles on the components that cancel come from an oriented system.** On a model,
let `X_P` be rational surface cycles of `Z`, one for each component `P` of the full exceptional
divisor `F`, such that every surface of `X_P` lies in `P` and maps to dimension at most one in
`Y`, and `∑_P X_P = 0`. Then `X_P = (ι_P)_* Z_P(b)` for a vertical oriented system `b`: on a
surface `W` lying on the `m` components `P₁, …, P_m`, put `b = (X_{Pᵢ}(W) - X_{Pⱼ}(W)) / m` on
the double surface `W` of `(Pᵢ, Pⱼ)`. -/
private theorem exists_verticalSurfaceCoefficients_of_sum_eq_zero {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (F : Divisor Z)
    (hFred : MMP.Intersection.IsReducedEffective F) (hFex : (F.supp : Set Z) = exceptionalSet r)
    (X : F.support → RatCycles Z 2)
    (h1 : ∀ P w, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ))
      ((2 : ℕ) : ℤ) w (X P) ≠ 0 → closure ({w} : Set Z) ⊆ P.1.support)
    (h2 : ∀ w, ∑ P, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ))
      ((2 : ℕ) : ℤ) w (X P) = 0)
    (h3 : ∀ P w, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ))
      ((2 : ℕ) : ℤ) w (X P) ≠ 0 → topologicalKrullDim (r.base '' closure ({w} : Set Z)) ≤ 1) :
    ∃ b ∈ verticalSurfaceCoefficients r F, ∀ P : F.support,
      ratPush P.1.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor b P.1)) = X P := by
  set c : F.support → Z → ℚ := fun P w => Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ)
    (Z ↘ Spec (.of ℂ)) ((2 : ℕ) : ℤ) w (X P) with hcdef
  set T : Z → Finset F.support := fun w =>
    Finset.univ.filter fun P : F.support => closure ({w} : Set Z) ⊆ P.1.support with hTdef
  set b : DoubleSurface F → ℚ := fun σ =>
    if h : ∃ w : Z, Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w = 2 ∧
        closure {w} = σ.carrier then
      (c ⟨σ.fst, σ.fst_mem⟩ h.choose - c ⟨σ.snd, σ.snd_mem⟩ h.choose) / (T h.choose).card
    else 0 with hbdef
  have hW : ∀ (σ : DoubleSurface F) (w : Z), Stacks.Chow.relativeDimension
      (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w = 2 →
      closure {w} = σ.carrier →
        b σ = (c ⟨σ.fst, σ.fst_mem⟩ w - c ⟨σ.snd, σ.snd_mem⟩ w) / (T w).card := by
    intro σ w hw hWσ
    have h : ∃ w : Z, Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w = 2 ∧
        closure {w} = σ.carrier := ⟨w, hw, hWσ⟩
    have hc : h.choose = w :=
      (inseparable_iff_closure_eq.2 (h.choose_spec.2.trans hWσ.symm)).eq
    simp only [hbdef, dif_pos h, hc]
  refine ⟨b, ⟨fun σ => ?_, fun σ hσ => ?_⟩, fun P => ?_⟩
  · by_cases h : ∃ w : Z, Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w = 2 ∧
        closure {w} = σ.carrier
    · obtain ⟨w, hw, hWσ⟩ := h
      rw [hW σ.swap w hw (by rw [DoubleSurface.swap_carrier]; exact hWσ), hW σ w hw hWσ]
      simp only [DoubleSurface.swap_fst, DoubleSurface.swap_snd]
      ring
    · have h' : ¬ ∃ w : Z, Stacks.Chow.relativeDimension
          (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w = 2 ∧
          closure {w} = σ.swap.carrier := by
        rwa [DoubleSurface.swap_carrier]
      simp only [hbdef, dif_neg h, dif_neg h', neg_zero]
  · by_cases h : ∃ w : Z, Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w = 2 ∧
        closure {w} = σ.carrier
    · obtain ⟨w, hw, hWσ⟩ := h
      rw [hW σ w hw hWσ] at hσ
      rw [← hWσ]
      by_cases h₁ : c ⟨σ.fst, σ.fst_mem⟩ w = 0
      · refine h3 ⟨σ.snd, σ.snd_mem⟩ w fun h₂ => hσ ?_
        rw [h₁, show c ⟨σ.snd, σ.snd_mem⟩ w = 0 from h₂]
        simp
      · exact h3 _ w h₁
    · exact absurd (by simp only [hbdef, dif_neg h]) hσ
  · refine rationalCycle_ext fun w => ?_
    by_cases hw : Stacks.Chow.relativeDimension
        (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Z ↘ Spec (.of ℂ)) w = 2
    swap
    · rw [rationalCoeff_eq_zero_of_relativeDimension_ne _ w hw,
        rationalCoeff_eq_zero_of_relativeDimension_ne _ w hw]
    rw [rationalCoeff_rationalProperPushforward_divisorCycle b P.1
      (coheight_genericPoint_eq_one_of_isModel sY r hM _) w hw]
    change _ = c P w
    by_cases hWP : closure ({w} : Set Z) ⊆ P.1.support
    swap
    · haveI : IsEmpty {σ : DoubleSurface F // σ.fst = P.1 ∧
          σ.carrier = closure {w}} := ⟨fun ⟨σ, h1σ, h2σ⟩ => hWP (by
        rw [← h2σ, ← h1σ]
        exact σ.carrier_subset.trans Set.inter_subset_left)⟩
      rw [finsum_of_isEmpty]
      by_contra hne
      exact hWP (h1 P w (Ne.symm hne))
    -- the double surfaces of `P` with surface `closure {w}` are the other components through it
    set g : {σ : DoubleSurface F // σ.fst = P.1 ∧ σ.carrier = closure {w}} →
        {P' : F.support // P' ∈ (T w).erase P} := fun σ =>
      ⟨⟨σ.1.snd, σ.1.snd_mem⟩, Finset.mem_erase.2 ⟨fun h => σ.1.fst_ne_snd
        (σ.2.1.trans (congrArg Subtype.val h).symm), Finset.mem_filter.2 ⟨Finset.mem_univ _,
          by intro x hx; rw [← σ.2.2] at hx; exact (σ.1.carrier_subset hx).2⟩⟩⟩ with hgdef
    have hg : Function.Bijective g := by
      constructor
      · intro σ τ h
        have h' := congrArg (fun x => x.1.1) h
        exact Subtype.ext (DoubleSurface.ext (σ.2.1.trans τ.2.1.symm) h'
          (σ.2.2.trans τ.2.2.symm))
      · rintro ⟨P', hP'⟩
        obtain ⟨hne, hP'T⟩ := Finset.mem_erase.1 hP'
        have hWP' : closure ({w} : Set Z) ⊆ P'.1.support := (Finset.mem_filter.1 hP'T).2
        have hy : w ∈ closure ({w} : Set Z) := subset_closure rfl
        have hdim : topologicalKrullDim (closure ({w} : Set Z)) = ((2 : ℕ) : WithBot ℕ∞) :=
          Stacks.Intersection.ExteriorProductProjections.topologicalKrullDim_closure_of_relativeDimension_eq
            ℂ _ w 2 hw
        obtain ⟨σ, hσ1, hσ2, hσ3, -⟩ := exists_doubleSurface_of_mem sY r hM F hFred hFex P.2 P'.2
          (fun h => hne (Subtype.ext h).symm) (hWP hy) (hWP' hy)
          (by rw [hdim]; norm_num)
        exact ⟨⟨σ, hσ1, hσ3⟩, Subtype.ext (Subtype.ext hσ2)⟩
    set e := Equiv.ofBijective g hg
    set f : {P' : F.support // P' ∈ (T w).erase P} → ℚ := fun P' =>
      (c P w - c P'.1 w) / (T w).card with hfdef
    have hbf : ∀ σ, b σ.1 = f (e σ) := by
      intro σ
      rw [hW σ.1 w hw σ.2.2.symm]
      have : (⟨σ.1.fst, σ.1.fst_mem⟩ : F.support) = P := Subtype.ext σ.2.1
      rw [this]
      rfl
    simp_rw [hbf]
    rw [finsum_comp_equiv e, finsum_eq_sum_of_fintype,
      Finset.sum_coe_sort ((T w).erase P) (fun P' => (c P w - c P' w) / (T w).card)]
    have hPT : P ∈ T w := Finset.mem_filter.2 ⟨Finset.mem_univ _, hWP⟩
    rw [Finset.sum_erase _ (by simp), ← Finset.sum_div, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
    have hsumT : ∑ P' ∈ T w, c P' w = 0 := by
      rw [← h2 w, hTdef]
      exact Finset.sum_filter_of_ne fun P' _ hP' => h1 P' w hP'
    have hc : ((T w).card : ℚ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 ⟨P, hPT⟩).ne'
    rw [hsumT, sub_zero]
    field_simp

/-! ### One blow-up: the transfer map -/

/-- The surface cycle of a `ℚ`-divisor, as a rational cycle of delta-dimension `((2 : ℕ) : ℤ)`. -/
private noncomputable def divisorCycleTwo (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (D : QDivisor X) : RatCycles X 2 :=
  Chow.divisorCycle X D

private theorem rationalCycleClass_divisorCycleTwo (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [IsComplexScheme X] (D : QDivisor X) :
    Chow.rationalCycleClass X 2 (divisorCycleTwo X D) = Chow.divisorClass X D :=
  rfl

/-- **The exceptional step, for a difference.** If a family `L` of rational surface cycles agrees
in class with the divisors `Z_E(a)` of an oriented system on the components not over the
codimension-`≥ 2` part of the centre, both push forward to zero on the components over it, and
both have vanishing ambient class sums, then `[L_E] = [Z_E(a)]` on every component. -/
private theorem rationalCycleClass_eq_divisorClass_of_sum_eq {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (L : ∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2) (a : DoubleSurface F' → ℚ)
    (hO : ∀ E : F'.support, ¬ (E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) →
      Chow.rationalCycleClass _ 2 (L E) = Chow.divisorClass _ (surfaceCoefficientDivisor a E.1))
    (hN : ∀ E : F'.support, E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
      ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2 (L E) = 0)
    (hNa : ∀ E : F'.support, E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
      ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2
        (divisorCycleTwo _ (surfaceCoefficientDivisor a E.1)) = 0)
    (hsum : ∑ E : F'.support, componentHomologyMap E.1 4 (Chow.rationalCycleClass _ 2 (L E)) = 0)
    (hB : ∑ E : F'.support, componentHomologyMap E.1 4
      (Chow.divisorClass _ (surfaceCoefficientDivisor a E.1)) = 0)
    (E : F'.support) :
    Chow.rationalCycleClass _ 2 (L E) = Chow.divisorClass _ (surfaceCoefficientDivisor a E.1) := by
  have key := rationalCycleClass_eq_zero_of_sum_eq_zero sY r hM I hIs hIc hM' F' hF'red hF'ex
    (fun E => L E - divisorCycleTwo _ (surfaceCoefficientDivisor a E.1))
    (fun E hE => by
      rw [map_sub, hO E hE, rationalCycleClass_divisorCycleTwo, sub_self])
    (fun E hE => by rw [map_sub, hN E hE, hNa E hE, sub_zero])
    (by
      simp only [map_sub, rationalCycleClass_divisorCycleTwo]
      rw [Finset.sum_sub_distrib, hsum, hB, sub_zero])
    E
  rw [map_sub, rationalCycleClass_divisorCycleTwo, sub_eq_zero] at key
  exact key

/-- The tuple of classes `([Lᵢ])ᵢ ∈ ⨁ᵢ H_4(Fᵢ, ℚ)` of a tuple of rational surface cycles. -/
private noncomputable def componentCycleClasses {Z : Scheme.{0}} [Z.Over (Spec (.of ℂ))]
    [IsComplexScheme Z] (F : Divisor Z) :
    (∀ E : F.support, RatCycles E.1.idealSheaf.subscheme 2) →ₗ[ℚ] ComponentHomology F :=
  LinearMap.pi fun E => Chow.rationalCycleClass _ 2 ∘ₗ LinearMap.proj E

private theorem exists_verticalSurfaceCoefficients_rationalCycleClass_eq {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hY : MMP.Mori.IsProjectiveVariety ℂ (Y ↘ Spec (.of ℂ))) (hYQ : IsQFactorial (Y ↘ Spec (.of ℂ)))
    (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r] (hM : IsModel (Y ↘ Spec (.of ℂ)) r)
    (F : Divisor Z) (hFred : MMP.Intersection.IsReducedEffective F)
    (hFex : (F.supp : Set Z) = exceptionalSet r)
    (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel (Y ↘ Spec (.of ℂ)) (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    [IsProper (blowUpToBase I)] [IsProper (blowUpToBase I ≫ r)]
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r))
    (L : ∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2)
    (hL : ∀ E : F'.support, ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I ≫ r) 2 (L E) = 0)
    (hsum : ∑ E : F'.support, componentHomologyMap E.1 4 (Chow.rationalCycleClass _ 2 (L E)) = 0)
    (hN : ∀ E : F'.support, E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
      ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2 (L E) = 0)
    (hB : ∃ b ∈ verticalSurfaceCoefficients r F, ∀ (P : F.support) (E : F'.support),
      ¬ (E.1.support ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) →
      (blowUpToBase I).base '' (E.1.support : Set (blowUp I)) = P.1.support →
      ∀ (ρ : E.1.idealSheaf.subscheme ⟶ P.1.idealSheaf.subscheme) [ρ.IsOver (Spec (.of ℂ))]
        [IsProper ρ],
        ρ ≫ P.1.idealSheaf.subschemeι = E.1.idealSheaf.subschemeι ≫ blowUpToBase I →
        Chow.rationalCycleClass _ 2 (ratPush ρ 2 (L E)) =
          Chow.divisorClass _ (surfaceCoefficientDivisor b P.1)) :
    ∃ a ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F', ∀ E : F'.support,
      Chow.rationalCycleClass _ 2 (L E) = Chow.divisorClass _ (surfaceCoefficientDivisor a E.1) := by
  obtain ⟨a, ha, hNa, hOa⟩ := exists_verticalSurfaceCoefficients_of_pushforward_eq_zero hY
    hYQ r hM F hFred hFex I hIs hIc hM' F' hF'red hF'ex L hL hsum hN hB
  have hB' := sum_componentHomologyMap_divisorClass_eq_zero (Y ↘ Spec (.of ℂ)) _ hM' F' a ha.1
  have : IsComplexScheme Y :=
    MMP.Analytic.isComplexScheme_of_isProjective Y hY.isProjective.isProjective
  exact ⟨a, ha, rationalCycleClass_eq_divisorClass_of_sum_eq (Y ↘ Spec (.of ℂ)) r hM I hIs hIc
    hM' F' hF'red hF'ex L a hOa hN hNa hsum hB'⟩

/-- **Pushing a boundary system down.** For a family `L` of rational surface cycles on the new
boundary whose cycles over the codimension-`≥ 2` part `K` of the centre push forward to zero,
and whose classes are those of the divisors of a vertical oriented system `a'`, the classes of the
push-downs `ρ_{P*} L_{e(P)}` are the divisor classes of a vertical oriented system of the old
boundary. -/
private theorem exists_verticalSurfaceCoefficients_pushDown {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (hM : IsModel sY r) (I : Z.IdealSheafData)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel sY (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    [IsProper (blowUpToBase I)]
    (F : Divisor Z) (hFred : MMP.Intersection.IsReducedEffective F)
    (hFex : (F.supp : Set Z) = exceptionalSet r)
    (F' : Divisor (blowUp I))
    (e : F.support → F'.support)
    (hsplit : ∀ f : F'.support → RatCycles Z 2, (∀ E : F'.support, (E.1.support : Set (blowUp I)) ⊆
        blowUpToBase I ⁻¹' MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
        f E = 0) → ∑ P, f (e P) = ∑ E, f E)
    (ρ : ∀ P : F.support, (e P).1.idealSheaf.subscheme ⟶ P.1.idealSheaf.subscheme)
    (hρ : ∀ P, ρ P ≫ P.1.idealSheaf.subschemeι = (e P).1.idealSheaf.subschemeι ≫ blowUpToBase I)
    [hρover : ∀ P, (ρ P).IsOver (Spec (.of ℂ))] [hρprop : ∀ P, IsProper (ρ P)]
    (L : ∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2)
    (hN : ∀ E : F'.support, (E.1.support : Set (blowUp I)) ⊆ blowUpToBase I ⁻¹'
        MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) →
      ratPush (E.1.idealSheaf.subschemeι ≫ blowUpToBase I) 2 (L E) = 0)
    (a' : DoubleSurface F' → ℚ) (ha' : a' ∈ verticalSurfaceCoefficients (blowUpToBase I ≫ r) F')
    (hcl : ∀ E : F'.support, Chow.rationalCycleClass _ 2 (L E) =
        Chow.divisorClass _ (surfaceCoefficientDivisor a' E.1)) :
    ∃ b ∈ verticalSurfaceCoefficients r F, ∀ P : F.support,
      Chow.divisorClass _ (surfaceCoefficientDivisor b P.1) =
        Chow.rationalCycleClass _ 2 (ratPush (ρ P) 2 (L (e P))) := by
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  set q := blowUpToBase I with hqdef
  have hqc : IsClosedMap q.base := q.isClosedMap
  have hcxE : ∀ E : Mori.PrimeDivisor (blowUp I), IsComplexScheme E.idealSheaf.subscheme :=
    fun E => IsComplexScheme.of_isClosedImmersion E.idealSheaf.subschemeι
  have hcxP : ∀ P : Mori.PrimeDivisor Z, IsComplexScheme P.idealSheaf.subscheme :=
    fun P => IsComplexScheme.of_isClosedImmersion P.idealSheaf.subschemeι
  have hsq : ∀ (P : F.support) (M : RatCycles (e P).1.idealSheaf.subscheme 2),
      ratPush P.1.idealSheaf.subschemeι 2 (ratPush (ρ P) 2 M) =
        ratPush q 2 (ratPush (e P).1.idealSheaf.subschemeι 2 M) := fun P M =>
    rationalPushforward_rationalPushforward_eq _ _ _ _ (hρ P) 2 M
  -- the new components of the boundary system push forward to zero
  have hJ : ∀ E : F'.support, (E.1.support : Set (blowUp I)) ⊆ q ⁻¹' K →
      ratPush (E.1.idealSheaf.subschemeι ≫ q) 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor a' E.1)) = 0 := by
    intro E hE
    haveI := hcxE E.1
    have h := rationalPushforward_eq_zero_of_rationalCycleClass_eq_zero sY r hM I E.1 hE
      (L E - Chow.divisorCycle _ (surfaceCoefficientDivisor a' E.1))
      (by rw [map_sub, hcl E, Chow.divisorClass, LinearMap.comp_apply, sub_self])
    rw [map_sub, hN E hE, zero_sub, neg_eq_zero] at h
    exact h
  -- the push-downs of the old components, as cycles on `Z`
  obtain ⟨X, hXdef⟩ : ∃ X : F.support → RatCycles Z 2, ∀ P, X P = ratPush q 2
      (ratPush (e P).1.idealSheaf.subschemeι 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor a' (e P).1))) := ⟨_, fun _ => rfl⟩
  have hXsum : ∑ P, X P = 0 := by
    have h := hsplit (fun E : F'.support => ratPush q 2
        (ratPush E.1.idealSheaf.subschemeι 2
          (Chow.divisorCycle _ (surfaceCoefficientDivisor a' E.1)))) (fun E hE => by
      haveI := hcxE E.1
      rw [← rationalPushforward_comp, hJ E hE])
    simp only [hXdef]
    rw [h, ← map_sum, sum_rationalPushforward_divisorCycle_eq_zero sY (q ≫ r) hM' F' a' ha'.1,
      map_zero]
  have h1 : ∀ P w, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ))
      ((2 : ℕ) : ℤ) w (X P) ≠ 0 → closure ({w} : Set Z) ⊆ P.1.support := by
    intro P w hW
    haveI := hρover P; haveI := hρprop P; haveI := hcxE (e P).1; haveI := hcxP P.1
    rw [hXdef, ← hsq P] at hW
    obtain ⟨v, -, rfl⟩ := exists_mem_support_of_mem_support_rationalPushforward _ hW
    refine closure_minimal (Set.singleton_subset_iff.2 ?_) P.1.idealSheaf.support.isClosed
    change _ ∈ (P.1.idealSheaf.support : Set Z)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨v, rfl⟩
  have h3 : ∀ P w, Chow.rationalCoeff (Stacks.Chow.fieldChowSituation ℂ) (Z ↘ Spec (.of ℂ))
      ((2 : ℕ) : ℤ) w (X P) ≠ 0 →
      topologicalKrullDim (r.base '' closure ({w} : Set Z)) ≤ 1 := by
    intro P w hW
    haveI := hcxE (e P).1
    rw [hXdef] at hW
    obtain ⟨v, hv, rfl⟩ := exists_mem_support_of_mem_support_rationalPushforward q hW
    have hv2 : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (blowUp I ↘ Spec (.of ℂ)) v = 2 := by
      by_contra h
      exact hv (rationalCoeff_eq_zero_of_relativeDimension_ne _ v h)
    rw [rationalCoeff_rationalProperPushforward_divisorCycle a' (e P).1
      (coheight_genericPoint_eq_one_of_isModel sY (q ≫ r) hM' _) v hv2] at hv
    obtain ⟨σ, hσ⟩ : ∃ σ : {σ : DoubleSurface F' // σ.fst = (e P).1 ∧
        σ.carrier = closure {v}}, a' σ ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (finsum_eq_zero_of_forall_eq_zero h)
    have hd := ha'.2 σ.1 hσ
    have hcl : closure {q.base v} = q.base '' closure {v} := by
      rw [← hqc.closure_image_eq_of_continuous q.continuous, Set.image_singleton]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, σ.2.2, ← hcl] at hd
    exact hd
  obtain ⟨b, hb, hbX⟩ := exists_verticalSurfaceCoefficients_of_sum_eq_zero sY r hM F hFred hFex
    X h1 (fun w => by rw [← map_sum, hXsum, map_zero]) h3
  refine ⟨b, hb, fun P => ?_⟩
  have hdiv : Chow.divisorCycle _ (surfaceCoefficientDivisor b P.1) = ratPush (ρ P) 2
      (Chow.divisorCycle _ (surfaceCoefficientDivisor a' (e P).1)) := by
    apply rationalProperPushforward_injective_of_isClosedImmersion P.1.idealSheaf.subschemeι 2
    rw [hbX P, hXdef, hsq]
  rw [Chow.rationalCycleClass_rationalProperPushforward (ρ P), hcl (e P)]
  change Chow.rationalCycleClass _ 2 (Chow.divisorCycle _ _) = _
  rw [hdiv, Chow.rationalCycleClass_rationalProperPushforward (ρ P)]
  rfl

/-- **The vertical defect does not grow under one boundary-compatible smooth blow-up.** For a
blow-up `q` of a model along a boundary-compatible smooth centre, there is an injective `ℚ`-linear
map `D_v(q ≫ r) → D_v(r)` carrying `D_{v,Q}(q ≫ r)` into `D_{v,Q}(r)` for every `Q ⊆ Y`. On a
representative `(L'_E)_E` whose cycles on the components over the codimension-`≥ 2` part of the
centre push forward to zero in `Z`, it is `(ρ_{P*} L'_{e(P)})_P`. -/
private theorem exists_injective_verticalDefect_blowUp {Z : Scheme.{0}}
    [Z.Over (Spec (.of ℂ))] [IsLocallyNoetherian Z] [NoetherianSpace Z] [IsComplexScheme Z]
    [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
    (hY : MMP.Mori.IsProjectiveVariety ℂ (Y ↘ Spec (.of ℂ))) (hYQ : IsQFactorial (Y ↘ Spec (.of ℂ)))
    (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r] (hM : IsModel (Y ↘ Spec (.of ℂ)) r) (I : Z.IdealSheafData)
    (hIs : MMP.Mori.IsSmoothScheme (I.subschemeι ≫ (Z ↘ Spec (.of ℂ))))
    (hIc : MMP.Resolution.HasSNCWith
      (MMP.Resolution.componentsFamily (exceptionalSet r : Set Z)) I)
    [(blowUp I).Over (Spec (.of ℂ))] [(blowUpToBase I).IsOver (Spec (.of ℂ))]
    (hM' : IsModel (Y ↘ Spec (.of ℂ)) (blowUpToBase I ≫ r)) [IsComplexScheme (blowUp I)]
    [IsProper (blowUpToBase I)] [IsProper (blowUpToBase I ≫ r)]
    (F : Divisor Z) (hFred : MMP.Intersection.IsReducedEffective F)
    (hFex : (F.supp : Set Z) = exceptionalSet r)
    (F' : Divisor (blowUp I)) (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set (blowUp I)) = exceptionalSet (blowUpToBase I ≫ r)) :
    ∃ φ : VerticalDefect (blowUpToBase I ≫ r) F' →ₗ[ℚ] VerticalDefect r F,
      Function.Injective φ ∧ ∀ Q : Set Y,
        (verticalDefectOver (blowUpToBase I ≫ r) F' Q).map φ ≤ verticalDefectOver r F Q := by
  haveI : IsComplexScheme Y :=
    MMP.Analytic.isComplexScheme_of_isProjective Y hY.isProjective.isProjective
  classical
  set K := MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z) with hKdef
  have hvarZ : AlgebraicGeometry.IsVariety ℂ (Z ↘ Spec (.of ℂ)) :=
    hM.comp_eq ▸ hM.isResolution.2.1
  have : IsIntegral Z := hvarZ.toIsIntegral
  by_cases hI : I = ⊥
  · subst hI
    have := isEmpty_blowUp_bot Z
    haveI : IsEmpty F'.support := ⟨fun E => isEmptyElim E.1.genericPoint⟩
    haveI : Subsingleton (VerticalDefect (blowUpToBase ⊥ ≫ r) F') := by
      haveI : Subsingleton (ComponentHomology F') := inferInstance
      infer_instance
    refine ⟨0, fun x y _ => Subsingleton.elim x y, fun Q => ?_⟩
    rw [Submodule.map_zero]
    exact bot_le
  obtain ⟨-, hqproj, -⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational
      (Z ↘ Spec (.of ℂ)) I hI
  have : IsProper (blowUpToBase I) := hqproj.isProper
  have hqc : IsClosedMap (blowUpToBase I).base := (blowUpToBase I).isClosedMap
  have hrc : IsClosedMap r.base := r.isClosedMap
  have : NoetherianSpace (blowUp I) := noetherianSpace_of_isComplexScheme
  have : IsLocallyNoetherian (blowUp I) := LocallyOfFiniteType.isLocallyNoetherian ((blowUp I) ↘ Spec (.of ℂ))
  obtain ⟨e, he, he', he_inj, hH⟩ :=
    exists_strictTransform (Y ↘ Spec (.of ℂ)) r hM I hIs hIc hM' hI F hFex F' hF'ex
  set ρ : ∀ P : F.support, (e P).1.idealSheaf.subscheme ⟶ P.1.idealSheaf.subscheme :=
    fun P => Scheme.IdealSheafData.subschemeMap _ _ (blowUpToBase I) (hH P) with hρdef
  have hρ : ∀ P, ρ P ≫ P.1.idealSheaf.subschemeι = (e P).1.idealSheaf.subschemeι ≫ (blowUpToBase I) :=
    fun P => Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  have hρover : ∀ P, (ρ P).IsOver (Spec (.of ℂ)) := fun P => ⟨by
    change ρ P ≫ P.1.idealSheaf.subschemeι ≫ (Z ↘ Spec (.of ℂ)) = _
    rw [← Category.assoc, hρ, Category.assoc,
      (inferInstance : (blowUpToBase I).IsOver (Spec (.of ℂ))).comp_over]
    rfl⟩
  have hρprop : ∀ P, IsProper (ρ P) := fun P => by
    haveI : IsProper (ρ P ≫ P.1.idealSheaf.subschemeι) := by rw [hρ]; infer_instance
    exact IsProper.of_comp (ρ P) P.1.idealSheaf.subschemeι
  have hcxE : ∀ E : Mori.PrimeDivisor (blowUp I), IsComplexScheme E.idealSheaf.subscheme :=
    fun E => IsComplexScheme.of_isClosedImmersion E.idealSheaf.subschemeι
  have hcxP : ∀ P : Mori.PrimeDivisor Z, IsComplexScheme P.idealSheaf.subscheme :=
    fun P => IsComplexScheme.of_isClosedImmersion P.idealSheaf.subschemeι
  have hsq : ∀ (P : F.support) (M : RatCycles (e P).1.idealSheaf.subscheme 2),
      ratPush P.1.idealSheaf.subschemeι 2 (ratPush (ρ P) 2 M) =
        ratPush (blowUpToBase I) 2 (ratPush (e P).1.idealSheaf.subschemeι 2 M) := by
    intro P M
    haveI := hρover P; haveI := hρprop P; haveI := hcxE (e P).1; haveI := hcxP P.1
    exact rationalPushforward_rationalPushforward_eq _ _ _ _ (hρ P) 2 M
  -- the representatives whose cycles over `K` push forward to zero
  let V' : Submodule ℚ (∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2) :=
    { carrier := {L | (∀ E : F'.support, ratPush (E.1.idealSheaf.subschemeι ≫ (blowUpToBase I) ≫ r) 2 (L E) = 0) ∧
        ∑ E : F'.support, componentHomologyMap E.1 4 (Chow.rationalCycleClass _ 2 (L E)) = 0 ∧
        ∀ E : F'.support, (E.1.support : Set (blowUp I)) ⊆ (blowUpToBase I) ⁻¹' K →
          ratPush (E.1.idealSheaf.subschemeι ≫ (blowUpToBase I)) 2 (L E) = 0}
      add_mem' := fun {L L'} hL hL' => ⟨fun E => by
          rw [Pi.add_apply, map_add, hL.1 E, hL'.1 E, add_zero], by
          simp only [Pi.add_apply, map_add, Finset.sum_add_distrib, hL.2.1, hL'.2.1, add_zero],
          fun E hE => by rw [Pi.add_apply, map_add, hL.2.2 E hE, hL'.2.2 E hE, add_zero]⟩
      zero_mem' := ⟨fun E => map_zero _, by simp, fun E _ => map_zero _⟩
      smul_mem' := fun c L hL => ⟨fun E => by
          rw [Pi.smul_apply, map_smul, hL.1 E, smul_zero], by
          simp only [Pi.smul_apply, map_smul, ← Finset.smul_sum, hL.2.1, smul_zero],
          fun E hE => by rw [Pi.smul_apply, map_smul, hL.2.2 E hE, smul_zero]⟩ }
  -- sums over the new components are sums over the old ones, if the other terms vanish
  have hsplit : ∀ {M : Type} [AddCommGroup M] (f : F'.support → M),
      (∀ E : F'.support, (E.1.support : Set (blowUp I)) ⊆ (blowUpToBase I) ⁻¹' K → f E = 0) →
      ∑ P, f (e P) = ∑ E, f E := by
    intro M _ f hf
    have himg : Finset.univ.image e = Finset.univ.filter
        (fun E : F'.support => ¬ ((E.1.support : Set (blowUp I)) ⊆ (blowUpToBase I) ⁻¹' K)) := by
      ext E
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
      refine ⟨?_, fun hE ↦ ?_⟩
      · rintro ⟨P, rfl⟩
        exact (he P).1
      · obtain ⟨P, rfl⟩ := he' E hE
        exact ⟨P, rfl⟩
    rw [← Finset.sum_image (fun P _ P' _ h => he_inj h), himg]
    exact Finset.sum_filter_of_ne fun E _ hE h => hE (hf E h)
  -- push-downs of representatives
  set push : (∀ E : F'.support, RatCycles E.1.idealSheaf.subscheme 2) →ₗ[ℚ]
      (∀ P : F.support, RatCycles P.1.idealSheaf.subscheme 2) :=
    LinearMap.pi fun P => ratPush (ρ P) 2 ∘ₗ LinearMap.proj (e P) with hpushdef
  have hpush : ∀ L P, push L P = ratPush (ρ P) 2 (L (e P)) := fun _ _ => rfl
  have hpushV : ∀ L ∈ V', (∀ P : F.support,
      ratPush (P.1.idealSheaf.subschemeι ≫ r) 2 (push L P) = 0) ∧
      ∑ P : F.support, componentHomologyMap P.1 4 (Chow.rationalCycleClass _ 2 (push L P)) = 0 := by
    intro L hLV
    obtain ⟨hL, hsum, hN⟩ := hLV
    refine ⟨fun P => ?_, ?_⟩
    · haveI := hρover P; haveI := hρprop P; haveI := hcxE (e P).1; haveI := hcxP P.1
      have h := rationalPushforward_rationalPushforward_eq (ρ P) (P.1.idealSheaf.subschemeι ≫ r)
        (e P).1.idealSheaf.subschemeι ((blowUpToBase I) ≫ r) (by rw [← Category.assoc, hρ, Category.assoc]) 2
        (L (e P))
      rw [hpush, h, ← rationalPushforward_comp]
      exact hL (e P)
    · obtain ⟨T, hTdef⟩ : ∃ T : F'.support → RationalHomology Z (2 * 2), ∀ E, T E =
          Chow.rationalCycleClass Z 2 (ratPush (blowUpToBase I) 2 (ratPush E.1.idealSheaf.subschemeι 2 (L E))) :=
        ⟨_, fun _ => rfl⟩
      have hTsum : ∑ E, T E = 0 := by
        have h : ∀ E : F'.support, T E = (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
            (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (blowUpToBase I)))
            (UnderlyingSpace.isProperMap_map (K := ℂ) (blowUpToBase I)) (2 * 2 : ℕ)).hom
            (componentHomologyMap E.1 4 (Chow.rationalCycleClass _ 2 (L E))) := by
          intro E
          haveI := hcxE E.1
          simp only [hTdef]
          rw [Chow.rationalCycleClass_rationalProperPushforward (blowUpToBase I),
            Chow.rationalCycleClass_rationalProperPushforward E.1.idealSheaf.subschemeι]
          rfl
        simp_rw [h]
        rw [← map_sum, hsum, map_zero]
      have hTP : ∀ P : F.support,
          componentHomologyMap P.1 4 (Chow.rationalCycleClass _ 2 (push L P)) = T (e P) := by
        intro P
        haveI := hρover P; haveI := hρprop P; haveI := hcxE (e P).1; haveI := hcxP P.1
        simp only [hTdef, hpush]
        rw [← hsq, Chow.rationalCycleClass_rationalProperPushforward P.1.idealSheaf.subschemeι]
        rfl
      simp_rw [hTP]
      rw [hsplit T (fun E hE => by
        haveI := hcxE E.1
        simp only [hTdef]
        rw [← rationalPushforward_comp, hN E hE, map_zero]), hTsum]
  have hαmem : ∀ L : V', componentCycleClasses F' L.1 ∈ verticalKernel ((blowUpToBase I) ≫ r) F' := by
    intro L
    exact (mem_exceptionalKernel F').2 ⟨fun E => Submodule.mem_map.2 ⟨L.1 E,
      LinearMap.mem_ker.2 (L.2.1 E), rfl⟩, L.2.2.1⟩
  have hβmem : ∀ L : V', componentCycleClasses F (push L.1) ∈ verticalKernel r F := by
    intro L
    exact (mem_exceptionalKernel F).2 ⟨fun P => Submodule.mem_map.2 ⟨push L.1 P,
      LinearMap.mem_ker.2 ((hpushV L.1 L.2).1 P), rfl⟩, (hpushV L.1 L.2).2⟩
  set α : V' →ₗ[ℚ] verticalKernel ((blowUpToBase I) ≫ r) F' :=
    LinearMap.codRestrict _ (componentCycleClasses F' ∘ₗ V'.subtype) hαmem with hαdef
  set β : V' →ₗ[ℚ] verticalKernel r F :=
    LinearMap.codRestrict _ (componentCycleClasses F ∘ₗ push ∘ₗ V'.subtype) hβmem with hβdef
  set α' := ((verticalSurfaceClasses ((blowUpToBase I) ≫ r) F').comap (verticalKernel ((blowUpToBase I) ≫ r) F').subtype).mkQ
    ∘ₗ α with hα'def
  set β' := ((verticalSurfaceClasses r F).comap (verticalKernel r F).subtype).mkQ ∘ₗ β
    with hβ'def
  -- every class over `Q` has a representative in `V'` whose push-down lies over `Q`
  have hDQ : ∀ (Q : Set Y) (x : verticalKernel ((blowUpToBase I) ≫ r) F'),
      (x : ComponentHomology F') ∈ verticalKernelOver ((blowUpToBase I) ≫ r) F' Q →
      ∃ v : V', ((α v : ComponentHomology F') - x) ∈ verticalSurfaceClasses ((blowUpToBase I) ≫ r) F' ∧
        (β v : ComponentHomology F) ∈ verticalKernelOver r F Q := by
    intro Q x hx
    have hqr : IsClosedMap ((blowUpToBase I) ≫ r).base := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp]; exact hrc.comp hqc
    obtain ⟨hxC, -⟩ := (mem_exceptionalKernel F').1 hx
    have hxs := ((mem_exceptionalKernel F').1 x.2).2
    choose L hL hLx using fun E => Submodule.mem_map.1 (hxC E)
    have hL0 : ∀ E : F'.support, ratPush (E.1.idealSheaf.subschemeι ≫ (blowUpToBase I) ≫ r) 2 (L E) = 0 :=
      fun E => LinearMap.mem_ker.1 (hL E).1
    obtain ⟨a₁, ha₁, ha₁Q, h₁⟩ := exists_verticalSurfaceCoefficients_jCorrection hY hYQ r hM I
      hIs hIc hM' F' hF'red hF'ex L hL0 Q (fun E => (hL E).2)
    have hB := sum_componentHomologyMap_divisorClass_eq_zero (Y ↘ Spec (.of ℂ)) _ hM' F' a₁ ha₁.1
    have hdiv : ∀ E : F'.support, Chow.rationalCycleClass _ 2
        (Chow.divisorCycle _ (surfaceCoefficientDivisor a₁ E.1)) =
          Chow.divisorClass _ (surfaceCoefficientDivisor a₁ E.1) := fun E => rfl
    have hv : (fun E => L E - Chow.divisorCycle _ (surfaceCoefficientDivisor a₁ E.1)) ∈ V' := by
      refine ⟨fun E => ?_, ?_, fun E hE => h₁ E hE⟩
      · rw [map_sub, hL0 E,
          rationalPushforward_divisorCycle_eq_zero_of_mem_vertical _ hqr F' ha₁ E.1, sub_zero]
      · simp only [map_sub, Finset.sum_sub_distrib, hLx, hdiv]
        rw [hxs, hB, sub_zero]
    refine ⟨⟨_, hv⟩, ?_, ?_⟩
    · refine ⟨-a₁, neg_mem ha₁, funext fun E => ?_⟩
      change Chow.divisorClass _ (surfaceCoefficientDivisorLinearMap F' E.1 (-a₁)) =
        Chow.rationalCycleClass _ 2 (L E - Chow.divisorCycle _ (surfaceCoefficientDivisor a₁ E.1)) - x.1 E
      rw [map_neg, map_neg, map_sub, hLx, hdiv]
      change _ = _ - Chow.divisorClass _ (surfaceCoefficientDivisorLinearMap F' E.1 a₁) - _
      abel
    · refine (mem_exceptionalKernel F).2 ⟨fun P => Submodule.mem_map.2 ⟨_,
        ⟨LinearMap.mem_ker.2 ((hpushV _ hv).1 P), ?_⟩, rfl⟩, (hpushV _ hv).2⟩
      haveI := hρover P; haveI := hρprop P
      rw [hpush, map_sub]
      refine sub_mem ?_ ?_
      · refine rationalPushforward_mem_cyclesMappingInto (ρ P) (ρ P).isClosedMap _ ?_
        rw [← Category.assoc, hρ, Category.assoc]
        exact (hL (e P)).2
      · refine rationalPushforward_mem_cyclesMappingInto (ρ P) (ρ P).isClosedMap _ ?_
        rw [← Category.assoc, hρ, Category.assoc]
        exact divisorCycle_mem_cyclesMappingInto ((blowUpToBase I) ≫ r) ha₁Q (e P).1
  have hsurj : Function.Surjective α' := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    have hx : (x : ComponentHomology F') ∈ verticalKernelOver ((blowUpToBase I) ≫ r) F' Set.univ := by
      obtain ⟨hxC, hxs⟩ := (mem_exceptionalKernel F').1 x.2
      refine (mem_exceptionalKernel F').2 ⟨fun E => ?_, hxs⟩
      obtain ⟨L, hL, hLx⟩ := Submodule.mem_map.1 (hxC E)
      exact Submodule.mem_map.2 ⟨L, ⟨hL, fun V _ => Set.subset_univ _⟩, hLx⟩
    obtain ⟨v, hv, -⟩ := hDQ Set.univ x hx
    refine ⟨v, (Submodule.Quotient.eq _).2 ?_⟩
    simpa [Submodule.mem_comap] using hv
  -- well-definedness: boundaries push down to boundaries
  have hwd : LinearMap.ker α' ≤ LinearMap.ker β' := by
    intro v hv
    have hv' : (α v : ComponentHomology F') ∈ verticalSurfaceClasses ((blowUpToBase I) ≫ r) F' :=
      (Submodule.Quotient.mk_eq_zero ((verticalSurfaceClasses ((blowUpToBase I) ≫ r) F').comap (verticalKernel ((blowUpToBase I) ≫ r) F').subtype)).1 (LinearMap.mem_ker.1 hv)
    obtain ⟨a', ha', ha'v⟩ := Submodule.mem_map.1 hv'
    have hcl : ∀ E : F'.support, Chow.rationalCycleClass _ 2 (v.1 E) =
        Chow.divisorClass _ (surfaceCoefficientDivisor a' E.1) := fun E => (congrFun ha'v E).symm
    obtain ⟨b, hb, hbP⟩ := exists_verticalSurfaceCoefficients_pushDown (Y ↘ Spec (.of ℂ)) r hM I
      hM' F hFred hFex F' e (fun f hf => hsplit f hf) ρ hρ v.1 v.2.2.2 a' ha' hcl
    refine LinearMap.mem_ker.2 ((Submodule.Quotient.mk_eq_zero ((verticalSurfaceClasses r F).comap (verticalKernel r F).subtype)).2 ?_)
    refine Submodule.mem_map.2 ⟨b, hb, funext fun P => ?_⟩
    change Chow.divisorClass _ (surfaceCoefficientDivisor b P.1) =
      Chow.rationalCycleClass _ 2 (push v.1 P)
    rw [hpush]
    exact hbP P
  -- injectivity
  have hinj : LinearMap.ker β' ≤ LinearMap.ker α' := by
    rintro ⟨L, hLv⟩ hv
    have hv' : (β ⟨L, hLv⟩ : ComponentHomology F) ∈ verticalSurfaceClasses r F :=
      (Submodule.Quotient.mk_eq_zero ((verticalSurfaceClasses r F).comap (verticalKernel r F).subtype)).1 (LinearMap.mem_ker.1 hv)
    obtain ⟨b, hb, hbv⟩ := Submodule.mem_map.1 hv'
    obtain ⟨hL, hsum, hN⟩ := id hLv
    have hB' : ∀ (P : F.support) (E : F'.support),
        ¬ (E.1.support ⊆ blowUpToBase I ⁻¹'
          MMP.Resolution.componentsOfCodimAtLeastTwo (I.support : Set Z)) →
        (blowUpToBase I).base '' (E.1.support : Set (blowUp I)) = P.1.support →
        ∀ (ρ' : E.1.idealSheaf.subscheme ⟶ P.1.idealSheaf.subscheme) [ρ'.IsOver (Spec (.of ℂ))]
          [IsProper ρ'],
          ρ' ≫ P.1.idealSheaf.subschemeι = E.1.idealSheaf.subschemeι ≫ blowUpToBase I →
          Chow.rationalCycleClass _ 2 (ratPush ρ' 2 (L E)) =
            Chow.divisorClass _ (surfaceCoefficientDivisor b P.1) := by
      intro P E hE hEP ρ' _ _ hρ'
      obtain ⟨P', rfl⟩ := he' E hE
      have hPP' : P' = P := by
        have hs : (P'.1.support : Set Z) = P.1.support := (he P').2.symm.trans hEP
        apply Subtype.ext
        apply eq_of_genericPoint_mem_support
        rw [← hs, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      subst hPP'
      have hρρ : ρ' = ρ P' := by
        rw [← cancel_mono P'.1.idealSheaf.subschemeι, hρ', hρ]
      subst hρρ
      exact (congrFun hbv P').symm
    obtain ⟨a, ha, key⟩ := exists_verticalSurfaceCoefficients_rationalCycleClass_eq hY
      hYQ r hM F hFred hFex I hIs hIc hM' F' hF'red hF'ex L hL hsum hN ⟨b, hb, hB'⟩
    refine LinearMap.mem_ker.2 ((Submodule.Quotient.mk_eq_zero ((verticalSurfaceClasses ((blowUpToBase I) ≫ r) F').comap (verticalKernel ((blowUpToBase I) ≫ r) F').subtype)).2 ?_)
    exact Submodule.mem_map.2 ⟨a, ha, funext fun E => (key E).symm⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ, φ = (LinearMap.ker α').liftQ β' hwd ∘ₗ
      (α'.quotKerEquivOfSurjective hsurj).symm.toLinearMap := ⟨_, rfl⟩
  have hφ : ∀ v, φ (α' v) = β' v := by
    intro v
    have h : (α'.quotKerEquivOfSurjective hsurj).symm (α' v) = (LinearMap.ker α').mkQ v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [hφdef, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
  refine ⟨φ, ?_, fun Q => ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨v, rfl⟩ := hsurj x
    rw [LinearMap.mem_ker, hφ] at hx
    exact (Submodule.mem_bot ℚ).2 (hinj hx)
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 hz
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 hy
    obtain ⟨v, hv1, hv2⟩ := hDQ Q x hx
    have hαv : α' v = y := by
      rw [← hxy]
      simp only [hα'def, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      exact (Submodule.Quotient.eq _).2 hv1
    rw [← hyz, ← hαv, hφ]
    exact ⟨β v, hv2, rfl⟩

/-- On an empty scheme the vertical defect vanishes: there are no prime divisors. -/
private theorem subsingleton_verticalDefect_of_isEmpty {Z' Y' : Scheme.{0}}
    [Z'.Over (Spec (.of ℂ))] [IsComplexScheme Z'] [IsEmpty Z'] [Y'.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of ℂ))] (f : Z' ⟶ Y') [f.IsOver (Spec (.of ℂ))]
    [IsProper f] (G : Divisor Z') :
    Subsingleton (VerticalDefect f G) := by
  haveI : IsEmpty G.support := ⟨fun E => isEmptyElim E.1.genericPoint⟩
  infer_instance

/-- The transfer statement only depends on the morphism, not on how it is written. -/
private theorem exists_injective_verticalDefect_congr {W Z Y : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [IsComplexScheme W] [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z]
    [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] {f g : W ⟶ Y} (h : f = g)
    [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] [IsProper f] [IsProper g]
    (r : Z ⟶ Y) [r.IsOver (Spec (.of ℂ))] [IsProper r] (G : Divisor W) (F : Divisor Z)
    (hg : ∃ φ : VerticalDefect g G →ₗ[ℚ] VerticalDefect r F, Function.Injective φ ∧
      ∀ Q : Set Y, (verticalDefectOver g G Q).map φ ≤ verticalDefectOver r F Q) :
    ∃ φ : VerticalDefect f G →ₗ[ℚ] VerticalDefect r F, Function.Injective φ ∧
      ∀ Q : Set Y, (verticalDefectOver f G Q).map φ ≤ verticalDefectOver r F Q := by
  subst h
  exact hg

end Step

end Proof_thm_mmp_conductor_vertical_defect_blowup_transfer

namespace MMP.Fourfold

open MMP.Mori
open Proof_thm_mmp_conductor_vertical_defect_blowup_transfer

/-- A morphism in the least class containing `𝟙 Z` and closed under `p ↦ blowUpToBase I ≫ p`
(under any side conditions `A p I`, `B p I`) is proper, for `Z` locally Noetherian: blow-ups of
locally Noetherian schemes are proper and again locally Noetherian. -/
public theorem isProper_of_forall_blowUp {Z Z' : Scheme.{0}} [IsLocallyNoetherian Z]
    (q : Z' ⟶ Z) {A B : ∀ ⦃W : Scheme.{0}⦄, (W ⟶ Z) → W.IdealSheafData → Prop}
    (hq : ∀ P : ∀ ⦃W : Scheme.{0}⦄, (W ⟶ Z) → Prop, P (𝟙 Z) →
      (∀ ⦃W : Scheme.{0}⦄ (p : W ⟶ Z) (I : W.IdealSheafData), P p → A p I → B p I →
        P (blowUpToBase I ≫ p)) → P q) :
    IsProper q := by
  refine (hq (fun W p => IsLocallyNoetherian W ∧ IsProper p) ⟨inferInstance, inferInstance⟩
    fun W p I hp _ _ => ?_).2
  obtain ⟨hW, hp⟩ := hp
  haveI := hW
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I), inferInstance⟩

/-- **Injective transfer of the vertical defect under smooth boundary blow-ups.** Let `Y` be a
normal projective `ℚ`-factorial complex variety, `r : Z ⟶ Y` a projective resolution by a smooth
projective complex fourfold `Z` whose full exceptional divisor `F` is a reduced snc divisor,
and `q : Z' ⟶ Z` a composite of finitely many blow-ups, each along a smooth centre having simple
normal crossings with the exceptional locus of the composite to `Y` so far. If `F'` is the full
exceptional divisor of `q ≫ r`, there is an injective `ℚ`-linear map
`VerticalDefect (q ≫ r) F' →ₗ[ℚ] VerticalDefect r F` sending `verticalDefectOver (q ≫ r) F' Q`
into `verticalDefectOver r F Q` for every closed `Q ⊆ Y`. -/
@[mmp "thm_mmp_conductor_vertical_defect_blowup_transfer"]
public theorem exists_injective_verticalDefect_blowup
    {Z Y : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [IsComplexScheme Z] [CompactSpace Z]
    [IsLocallyNoetherian Z] [IsNormal Z] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (r : Z ⟶ Y) (F : Divisor Z)
    (hcomp : r ≫ sY = Z ↘ Spec (.of ℂ))
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hYQ : IsQFactorial sY)
    (hr : MMP.Intersection.IsResolution sY r)
    (hZ : IsProjective (Z ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim Z = 4)
    (hFred : MMP.Intersection.IsReducedEffective F)
    (hFsnc : DivisorWithCoeffs.IsSNC (r ≫ sY) F)
    (hFex : (F.supp : Set Z) = exceptionalSet r)
    {Z' : Scheme.{0}} [Z'.Over (Spec (.of ℂ))] [IsComplexScheme Z'] (q : Z' ⟶ Z)
    [q.IsOver (Spec (.of ℂ))]
    (hq : ∀ P : ∀ ⦃W : Scheme.{0}⦄, (W ⟶ Z) → Prop, P (𝟙 Z) →
      (∀ ⦃W : Scheme.{0}⦄ (p : W ⟶ Z) (I : W.IdealSheafData), P p →
        MMP.Mori.IsSmoothScheme (I.subschemeι ≫ p ≫ (Z ↘ Spec (.of ℂ))) →
        MMP.Resolution.HasSNCWith
          (MMP.Resolution.componentsFamily (exceptionalSet (p ≫ r) : Set W)) I →
        P (blowUpToBase I ≫ p)) → P q)
    (F' : Divisor Z') (hF'red : MMP.Intersection.IsReducedEffective F')
    (hF'ex : (F'.supp : Set Z') = exceptionalSet (q ≫ r)) :
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    haveI : r.IsOver (Spec (.of ℂ)) := ⟨hcomp⟩
    haveI : IsComplexScheme Y :=
      MMP.Analytic.isComplexScheme_of_isProjective Y hY.isProjective.isProjective
    haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.2.2.2.1
    haveI : IsProper q := isProper_of_forall_blowUp q hq
    ∃ φ : VerticalDefect (q ≫ r) F' →ₗ[ℚ] VerticalDefect r F, Function.Injective φ ∧
      ∀ Q : Set Y, IsClosed Q →
        (verticalDefectOver (q ≫ r) F' Q).map φ ≤ verticalDefectOver r F Q := by
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨hcomp⟩
  haveI : IsComplexScheme Y :=
    MMP.Analytic.isComplexScheme_of_isProjective Y hY.isProjective.isProjective
  haveI : IsProper r := isProper_of_isProjectiveMorphism r hr.2.2.2.1
  -- the inductive invariant along the blow-up sequence
  let P : ∀ ⦃W : Scheme.{0}⦄, (W ⟶ Z) → Prop := fun W p =>
    IsLocallyNoetherian W ∧ ∃ _ : IsProper p, ∀ [W.Over (Spec (.of ℂ))] [p.IsOver (Spec (.of ℂ))],
      (IsEmpty W ∨ IsModel sY (p ≫ r)) ∧
      ∀ [IsComplexScheme W] (G : Divisor W), MMP.Intersection.IsReducedEffective G →
        (G.supp : Set W) = exceptionalSet (p ≫ r) →
        ∃ φ : VerticalDefect (p ≫ r) G →ₗ[ℚ] VerticalDefect r F, Function.Injective φ ∧
          ∀ Q : Set Y, (verticalDefectOver (p ≫ r) G Q).map φ ≤ verticalDefectOver r F Q
  have hP : P q := by
    refine hq P ?_ ?_
    · refine ⟨inferInstance, inferInstance, ?_⟩
      intro instZ0 hover
      obtain ⟨s⟩ := instZ0
      have hs : s = Z ↘ Spec (.of ℂ) := by
        have := hover.comp_over
        rw [Category.id_comp] at this
        exact this.symm
      subst hs
      refine ⟨Or.inr ?_, fun G hG hGex => ?_⟩
      · exact ⟨‹_›, ‹_›, ‹_›, ‹_›,
          by rw [Category.id_comp]; exact hcomp, by rw [Category.id_comp]; exact hr, hZ, hdim,
          ⟨F, hFred, by rw [Category.id_comp]; exact hFsnc, by rw [Category.id_comp]; exact hFex⟩⟩
      · rw [Category.id_comp] at hGex
        obtain rfl := eq_of_isReducedEffective_of_supp_eq hFred hG (hFex.trans hGex.symm)
        exact exists_injective_verticalDefect_congr (Category.id_comp r) r _ _
          ⟨LinearMap.id, Function.injective_id, fun Q => (Submodule.map_id _).le⟩
    · intro W p I hp hIs hIc
      obtain ⟨hWn, hpr, hp⟩ := hp
      haveI := hWn
      haveI : IsLocallyNoetherian (blowUp I) :=
        LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase I)
      refine ⟨inferInstance, inferInstance, ?_⟩
      intro instB hover
      letI : W.Over (Spec (.of ℂ)) := ⟨p ≫ Z ↘ Spec (.of ℂ)⟩
      haveI : p.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
      haveI : (blowUpToBase I).IsOver (Spec (.of ℂ)) :=
        ⟨by rw [← hover.comp_over, Category.assoc]; rfl⟩
      obtain ⟨hWM, hWA⟩ := hp
      rcases hWM with hW | hWM
      · haveI : IsEmpty (blowUp I) := ⟨fun x => hW.elim (blowUpToBase I x)⟩
        refine ⟨Or.inl inferInstance, fun G _ _ => ?_⟩
        haveI := subsingleton_verticalDefect_of_isEmpty ((blowUpToBase I ≫ p) ≫ r) G
        refine ⟨0, fun x y _ => Subsingleton.elim x y, fun Q => ?_⟩
        rw [Submodule.map_zero]
        exact bot_le
      · have hB := isEmpty_or_isModel_blowUp sY hY hYQ (p ≫ r) hWM I hIs hIc
        refine ⟨by rw [Category.assoc]; exact hB, fun G hG hGex => ?_⟩
        rw [Category.assoc] at hGex
        haveI : IsComplexScheme W := hWM.isComplexScheme
        haveI : NoetherianSpace W := noetherianSpace_of_isComplexScheme
        obtain ⟨F₁, hF₁red, -, hF₁ex⟩ := hWM.exists_divisor
        obtain ⟨φ₁, hφ₁, hφ₁Q⟩ := hWA F₁ hF₁red hF₁ex
        rcases hB with hBe | hBM
        · haveI := subsingleton_verticalDefect_of_isEmpty ((blowUpToBase I ≫ p) ≫ r) G
          refine ⟨0, fun x y _ => Subsingleton.elim x y, fun Q => ?_⟩
          rw [Submodule.map_zero]
          exact bot_le
        · haveI : IsProper (blowUpToBase I ≫ p ≫ r) := inferInstance
          obtain ⟨φ₂, hφ₂, hφ₂Q⟩ := exists_injective_verticalDefect_blowUp hY hYQ (p ≫ r) hWM
            I hIs hIc hBM F₁ hF₁red hF₁ex G hG hGex
          refine exists_injective_verticalDefect_congr (Category.assoc _ _ _) r G F
            ⟨φ₁ ∘ₗ φ₂, hφ₁.comp hφ₂, fun Q => ?_⟩
          rw [Submodule.map_comp]
          exact (Submodule.map_mono (hφ₂Q Q)).trans (hφ₁Q Q)
  obtain ⟨-, _, hP⟩ := hP
  obtain ⟨φ, hφ, hφQ⟩ := hP.2 F' hF'red hF'ex
  exact ⟨φ, hφ, fun Q _ => hφQ Q⟩

end MMP.Fourfold
