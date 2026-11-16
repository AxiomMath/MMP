module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.MMP.Termination.Defs
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafTensor
public import MMP.AlgebraicGeometry.Intersection.QCartierCurveNumber
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.FlatPullbackVariety
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Properties.NormalConnectedIntegral
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
public import MMP.AlgebraicGeometry.MMP.Abundance.Basic
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeConeInAbsolute
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.DltNegativeFace
public import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent
public import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.LowerDimDltModel
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Termination.StrataEventuallyBirational
import MMP.AlgebraicGeometry.MMP.Termination.StratumDivisorsStabilize
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumAvoidsFlip
import MMP.AlgebraicGeometry.Singularities.Adjunction.DltStratum
public import MMP.AlgebraicGeometry.MMP.Flip.IsoOffFlippingLocus
import MMP.RingTheory.Kaehler.PluriformProduct
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferentEffective
import MMP.AlgebraicGeometry.Singularities.Adjunction.ForwardDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.StratumDiscrepancyMonotone
import MMP.AlgebraicGeometry.Morphisms.Birational.ModificationCodimOne
import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
import MMP.AlgebraicGeometry.MMP.MinimalModel.WeakLcModelLcModelMorphism
import MMP.AlgebraicGeometry.MMP.Flip.NegativeContractionDiscrepancy
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.MMP.Flip.FlippedCurveDiscrepancy
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
import MMP.AlgebraicGeometry.MMP.Contraction.CurveFactorization
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.MMP.MinimalModel.WeakLcModelComparison
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.Resolution.StratumBlowupRelativelyAmple
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension

/-!
# Termination of the induced stratum diagrams

Let `X_0 ⇢ X_1 ⇢ ⋯` be a sequence of flips `X_i → Z_i ← X_{i+1}` of rational dlt pairs
`(X_i, B_i)` of dimension four, with all models `X_i` and all contraction targets `Z_i`
projective. A boundary stratum `S ⊆ X_i` (an irreducible component of an intersection of
components of `⌊B_i⌋`) carries, by iterated adjunction, a rational pair `(S, B_S)` with
`K_S + B_S = (K_{X_i} + B_i)|_S`. A stratum `S ⊆ X_i` is *fixed* by the step `i` if there is a
stratum `S⁺ ⊆ X_{i+1}` and an isomorphism `S ≅ S⁺` of pairs over `Z_i`, and conversely.

Assume the projective log minimal model program in dimension at most three
(`MMP.Fourfold.ProjectiveLowerLogMMP 3`), and let `1 ≤ d ≤ 3`. If, along a tail of the sequence,
every step fixes all boundary strata of dimension less than `d`, then along a further tail every
step fixes all boundary strata of dimension `d`.

## Main results

* `MMP.Fourfold.SequenceOfFlips.eventually_stratumAdjunctionPair_iso_of_projectiveLowerLogMMP`:
  termination of the induced diagrams `S_i → T_i ← S_{i+1}` on `d`-dimensional strata.

## Implementation notes

A stratum is recorded as a closed immersion `ι : S ⟶ X_i` carrying iterated adjunction data
(`MMP.Fourfold.IsStratumAdjunctionPair`), with adjunction boundary `B_S`, whose image is a boundary
stratum of `(X_i, B_i)` (`MMP.Fourfold.IsDltStratum`). Two strata `S ⊆ X_i` and `S⁺ ⊆ X_{i+1}`
correspond through the step `i` when an isomorphism `e : S ≅ S⁺` commutes with the maps to the
common contraction target `Z_i`, that is `ι ≫ φ_i = e ≫ ι⁺ ≫ φ_i⁺`; it is an isomorphism of
pairs when moreover `e_* B_S = B_{S⁺}`. Fixing is required in both directions, so that the step
induces a bijection between the strata of the given dimensions. A tail is a filter
`Filter.atTop` condition; the hypotheses on the models are only asked along a tail.

The fixed strata of dimension `< d` lie in the isomorphism locus of each flip
(`MMP.Fourfold.IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair`). Along a tail of the
sequence the `d`-dimensional strata correspond step by step, the positive
sides `S_{i+1} → Z_i` of the stratum diagrams `S_i → Z_i ← S_{i+1}` are small, and corresponding
prime divisors of the strata have the same coefficients in the adjunction boundaries. Each step
`i` is then covered by a *block*: a relative dlt program over `Z_i`, started at a crepant
`ℚ`-factorial dlt model of `(S_i, B_{S_i})`. Along a block every prime divisor comes from the
start with the same coefficient, and discrepancies do not decrease (Kollár–Mori 3.38). When the
adjoint becomes nef over `Z_i`, `S_{i+1}` is a log canonical model of the current pair over
`Z_i`, so the birational map to `S_{i+1}` is a crepant morphism (FA 2.24.3 and FA 17.10).

A block with no steps forces `S_i ≅ S_{i+1}` over `Z_i`. Both `p : W → S_i` and
`h : W → S_{i+1}` are crepant, `-(K_{S_i} + B_{S_i})` is ample over `Z_i` and
`K_{S_{i+1}} + B_{S_{i+1}}` is ample over `Z_i`, so by the projection formula `p` and `h`
contract the same curves, and the rigidity lemma for contractions identifies the targets.
Infinitely many nonempty blocks would concatenate to an infinite sequence of elementary dlt steps
of projective threefold pairs, which the projective log MMP in dimension three excludes.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Flips
open MMP.Fourfold.Oai4C1.StepChain (specializes_of_map_specializes)
open MMP.Fourfold.Oai4C1.Negativity (isCartierCombination_neg)
open MMP.Threefold.Resolution (inverseTransformPrimeDivisor_eq_some_of_map_genericPoint)
open MMP.Mori.DivisorOver (isExceptional_iff_two_le_coheight)

section ProperModel

universe v

/-- **Nagata compactification**: a separated morphism of finite type `f : Y ⟶ Z` to a
quasi-compact quasi-separated scheme factors as a quasi-compact open immersion followed by a
proper morphism. -/
private theorem exists_isOpenImmersion_isProper_comp_eq {Y Z : Scheme.{v}} (f : Y ⟶ Z)
    [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] :
    ∃ (P : Scheme.{v}) (j : Y ⟶ P) (p : P ⟶ Z), IsOpenImmersion j ∧ QuasiCompact j ∧
      IsProper p ∧ j ≫ p = f := by
  obtain ⟨c, hc⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
  exact ⟨c.space, c.immersion, c.toBase, inferInstance, hc, inferInstance, Over.w c.obj.hom⟩

/-- The normalization of `P` in a normal integral locally Noetherian scheme `Y`, along a
quasi-compact open immersion `j : Y ⟶ P` with `P` locally of finite type over a field, is normal
and finite over `P`, and `Y` is open in it. -/
private theorem isOpenImmersion_toNormalization_and_isNormal_and_isFinite {k : Type v} [Field k]
    {Y P : Scheme.{v}} {sP : P ⟶ Spec (.of k)} [LocallyOfFiniteType sP] (j : Y ⟶ P)
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
private theorem isBirationalMorphism_of_isOpenImmersion_comp {Y P Z : Scheme.{v}} [IsIntegral Y]
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
  refine MMP.Flips.isBirationalMorphism_of_isIso_resLE g U V ⟨t w, w, hw, rfl⟩ ⟨_, ⟨w, hw⟩, rfl⟩
    hUV ?_
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun ⟨z, hz⟩ => ?_⟩⟩
  obtain ⟨w, rfl⟩ := hz
  refine ⟨(t.isoImage W).hom w, ?_⟩
  apply V.ι.isOpenEmbedding.injective
  rw [← Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc]
  rfl

/-- **Kollár–Mori 2.22 for the identity model.** Every divisor `(Y, f, E)` over a normal variety
`X` (with `f` not necessarily proper) has the valuation of a divisor over `X` whose morphism is
proper: compactify `f` by Nagata's theorem, `Y ⊆ P → X`, and replace `P` by the normalization of
`P` in `Y`, which is finite over `P`, normal, and contains `Y` as an open subscheme. -/
private theorem exists_isProper_valuation_eq {k : Type v} [Field k] {X : Scheme.{v}}
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

end ProperModel

/-- Step `i` of a sequence of flips *fixes the adjunction strata whose dimension satisfies `p`*:
every such adjunction stratum `(T, B_T)` of `(X_i, B_i)` whose image is a dlt stratum has a
counterpart `(T', B_{T'})` on `(X_{i+1}, B_{i+1})`, isomorphic to it as a pair over `Z_i`, and
conversely. -/
private def StepFixesStrata {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} (S : SequenceOfFlips sX 4 K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) (p : WithBot ℕ∞ → Prop) : Prop :=
  haveI := S.isLocallyNoetherian_model i
  haveI := S.isNormal_model i
  haveI := S.isLocallyNoetherian_model (i + 1)
  haveI := S.isNormal_model (i + 1)
  haveI : IsIntegral (S.model i).1 :=
    (S.isNormalVariety_model i (lt_of_le_of_lt (by exact_mod_cast i.le_succ) hi)).1.toIsIntegral
  haveI : IsIntegral (S.model (i + 1)).1 := (S.isNormalVariety_model (i + 1) hi).1.toIsIntegral
  (∀ (T : Scheme.{0}) (ι : T ⟶ (S.model i).1) (BT : QDivisor T),
    IsStratumAdjunctionPair (S.model i).2.1 (S.model i).2.2.2 ι BT →
    IsDltStratum (S.model i).2.1 (S.model i).2.2.2 (Set.range ι.base) →
    p (topologicalKrullDim T) →
    ∃ (T' : Scheme.{0}) (ι' : T' ⟶ (S.model (i + 1)).1) (BT' : QDivisor T') (e : T ≅ T'),
      IsStratumAdjunctionPair (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 ι' BT' ∧
      IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 (Set.range ι'.base) ∧
      ι ≫ S.contraction i = e.hom ≫ ι' ≫ S.flip i ∧
      RationalMap.transformDivisor e.hom.toRationalMap BT = BT') ∧
  (∀ (T' : Scheme.{0}) (ι' : T' ⟶ (S.model (i + 1)).1) (BT' : QDivisor T'),
    IsStratumAdjunctionPair (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 ι' BT' →
    IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 (Set.range ι'.base) →
    p (topologicalKrullDim T') →
    ∃ (T : Scheme.{0}) (ι : T ⟶ (S.model i).1) (BT : QDivisor T) (e : T ≅ T'),
      IsStratumAdjunctionPair (S.model i).2.1 (S.model i).2.2.2 ι BT ∧
      IsDltStratum (S.model i).2.1 (S.model i).2.2.2 (Set.range ι.base) ∧
      ι ≫ S.contraction i = e.hom ≫ ι' ≫ S.flip i ∧
      RationalMap.transformDivisor e.hom.toRationalMap BT = BT')

/-! ### Rational solutions of rational linear systems -/

section RationalApproximation

/-- Finitely many positive elements of a finite-dimensional `ℚ`-subspace `W ⊆ ℝ` are positive
under some `ℚ`-linear form `ψ : W → ℚ`: the forms `x ↦ ∑ᵢ xᵢ cᵢ`, for coordinates `xᵢ` in a
`ℚ`-basis `bᵢ` of `W`, depend continuously on `c ∈ ℝˢ`, give the inclusion at `c = (bᵢ)`, and
`ℚˢ` is dense in `ℝˢ`. -/
private theorem exists_linearMap_pos {W : Submodule ℚ ℝ} [FiniteDimensional ℚ W] {ι : Type*}
    [Finite ι] (w : ι → W) (hw : ∀ j, 0 < (w j : ℝ)) : ∃ ψ : W →ₗ[ℚ] ℚ, ∀ j, 0 < ψ (w j) := by
  set b := Module.finBasis ℚ W
  set s := Module.finrank ℚ W
  let φ : (Fin s → ℝ) → W → ℝ := fun c x => ∑ i, (b.repr x i : ℝ) * c i
  have hφc : ∀ x, Continuous fun c => φ c x := fun x => by
    simp only [φ]; fun_prop
  set cstar : Fin s → ℝ := fun i => (b i : ℝ)
  have hstar : ∀ x, φ cstar x = x := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    simp only [φ, cstar, Submodule.coe_sum, Submodule.coe_smul_of_tower]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def]
  set U : Set (Fin s → ℝ) := ⋂ j, {c | 0 < φ c (w j)}
  have hU : IsOpen U := isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (hφc _)
  have hcU : cstar ∈ U := Set.mem_iInter.2 fun j => by simp [hstar, hw j]
  obtain ⟨c, hc⟩ :=
    (DenseRange.piMap (fun _ => Rat.denseRange_cast)).exists_mem_open hU ⟨cstar, hcU⟩
  refine ⟨∑ i, c i • b.coord i, fun j => ?_⟩
  have := Set.mem_iInter.1 hc j
  simp only [Set.mem_setOf_eq, φ, Pi.map_apply] at this
  have h2 : ((∑ i, c i • b.coord i) (w j) : ℝ) = ∑ i, (b.repr (w j) i : ℝ) * (c i : ℝ) := by
    simp [mul_comm]
  exact_mod_cast h2 ▸ this

/-- A system of linear equations `∑ⱼ rⱼ aₚⱼ = dₚ` with integer coefficients and rational right
hand sides which has a positive real solution `r` has a positive rational solution: apply to `r`
a `ℚ`-linear form on the `ℚ`-span of `1, r₁, …, rₘ` positive on all of them, normalized at `1`. -/
private theorem exists_rat_pos_solution {m : ℕ} {κ : Type*} (a : κ → Fin m → ℤ) (d : κ → ℚ)
    (r : Fin m → ℝ) (hr : ∀ j, 0 < r j) (h : ∀ P, (d P : ℝ) = ∑ j, r j * a P j) :
    ∃ q : Fin m → ℚ, (∀ j, 0 < q j) ∧ ∀ P, d P = ∑ j, q j * a P j := by
  set W := Submodule.span ℚ (insert (1 : ℝ) (Set.range r))
  have : FiniteDimensional ℚ W :=
    FiniteDimensional.span_of_finite ℚ ((Set.finite_range r).insert 1)
  let one : W := ⟨1, Submodule.subset_span (Set.mem_insert _ _)⟩
  let rr : Fin m → W := fun j => ⟨r j, Submodule.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)⟩
  obtain ⟨ψ, hψ⟩ := exists_linearMap_pos (W := W) (fun o : Option (Fin m) => o.elim one rr)
    (fun o => by cases o <;> simp [one, rr, hr])
  have h1 : 0 < ψ one := hψ none
  refine ⟨fun j => ψ (rr j) / ψ one, fun j => div_pos (hψ (some j)) h1, fun P => ?_⟩
  have hW : (d P) • one = ∑ j, (a P j : ℚ) • rr j := by
    apply Subtype.ext
    simp only [one, rr, Submodule.coe_smul_of_tower, Submodule.coe_sum, Rat.smul_def]
    rw [mul_one, h P]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  have := congrArg ψ hW
  simp only [map_smul, map_sum, smul_eq_mul] at this
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [eq_div_iff h1.ne', this]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end RationalApproximation

/-! ### Relatively ample multiples of `ℝ`-ample `ℚ`-divisors -/

section RelativelyAmple

universe u

open RingedSpaceModuleAdjunction Stacks.Ample Stacks.RelativeVeryAmple

/-- The ringed-space pull-back of a module along a morphism of schemes is the scheme pull-back. -/
private noncomputable def modulePullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (modulePullback f.toLRSHom.toShHom).obj F ≅ (Scheme.Modules.pullback f).obj F :=
  (Adjunction.leftAdjointUniq (modulePullbackPushforwardAdjunction f.toLRSHom.toShHom)
    (Scheme.Modules.pullbackPushforwardAdjunction f)).app F

/-- For a quasi-compact morphism, `f`-ampleness gives ampleness over every affine open. -/
private theorem stacks_isRelativelyAmple_of_isRelativelyAmple {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f]
    (L : X.Modules) [IsInvertibleModule X L] (hL : MMP.Mori.IsRelativelyAmple f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L inferInstance hL

/-- If `φ = (a, b) : W ⟶ X ×_S Y` is affine, `L` is `f`-ample and `N` is `g`-ample, then
`a^* L ⊗ b^* N` is ample relative to `a ≫ f`. -/
private theorem isRelativelyAmple_tensorModules_of_isAffineHom {S X Y W : Scheme.{u}}
    {f : X ⟶ S} {g : Y ⟶ S} {a : W ⟶ X} {b : W ⟶ Y} (h : a ≫ f = b ≫ g)
    [IsAffineHom (Limits.pullback.lift a b h)] (L : X.Modules) (N : Y.Modules)
    [IsInvertibleModule X L] [IsInvertibleModule Y N]
    (hL : Stacks.RelativeAmple.IsRelativelyAmple f L)
    (hN : Stacks.RelativeAmple.IsRelativelyAmple g N) :
    Stacks.RelativeAmple.IsRelativelyAmple (a ≫ f)
      (tensorModules W ((modulePullback a.toLRSHom.toShHom).obj L)
        ((modulePullback b.toLRSHom.toShHom).obj N)) := by
  have h1 := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (Limits.pullback.lift a b h) (Limits.pullback.fst f g ≫ f) _
    (Stacks.AmpleExternalTensor.isRelativelyAmple_externalTensor f g L N hL hN)
  have e := Stacks.AmpleExternalTensor.pullbackExternalTensorIso f g
    (Limits.pullback.lift a b h) L N
  simp only [Limits.pullback.lift_fst, Limits.pullback.lift_snd] at e
  rw [← Category.assoc, Limits.pullback.lift_fst] at h1
  exact (isRelativelyAmple_congr _ _ _ e).mp h1

/-- For a quasi-compact separated morphism `f`, the sum of two `f`-ample Cartier divisors is
`f`-ample: `𝒪(A + B) ≅ Δ^*(𝒪(A) ⊠ 𝒪(B))` and the diagonal of `f` is affine. -/
private theorem isRelativelyAmple_add {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {A B : Divisor X} (hA : A.IsCartier) (hAf : A.IsRelativelyAmple f hA)
    (hB : B.IsCartier) (hBf : B.IsRelativelyAmple f hB) :
    (A + B).IsRelativelyAmple f (hA.add hB) := by
  haveI := hA.isInvertibleModule_divisorialSheaf
  haveI := hB.isInvertibleModule_divisorialSheaf
  haveI := (hA.add hB).isInvertibleModule_divisorialSheaf
  haveI : IsAffineHom (Limits.pullback.lift (𝟙 X) (𝟙 X) (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f)) :=
    show IsAffineHom (Limits.pullback.diagonal f) from inferInstance
  have h := isRelativelyAmple_tensorModules_of_isAffineHom (rfl : 𝟙 X ≫ f = 𝟙 X ≫ f) _ _
    (stacks_isRelativelyAmple_of_isRelativelyAmple f _ hAf)
    (stacks_isRelativelyAmple_of_isRelativelyAmple f _ hBf)
  rw [Category.id_comp] at h
  refine MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ ?_).mp h)
  exact tensorModulesMapIso X (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _)
    (modulePullbackIso _ _ ≪≫ (Scheme.Modules.pullbackId X).app _) ≪≫
    hA.divisorialSheafTensorIso hB

/-- For a quasi-compact separated morphism `f`, every positive multiple of an `f`-ample Cartier
divisor is `f`-ample. -/
private theorem isRelativelyAmple_nsmul {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {L : Divisor X} (hL : L.IsCartier) (hLf : L.IsRelativelyAmple f hL)
    (n : ℕ) (hn : 0 < n) : (n • L).IsRelativelyAmple f (hL.nsmul n) := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · simpa using hLf
    · convert isRelativelyAmple_add _ (ih hn') _ hLf using 2
      rw [succ_nsmul]

/-- A finite nonempty sum of `f`-ample Cartier divisors is an `f`-ample Cartier divisor. -/
private theorem exists_isRelativelyAmple_sum {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (g : ι → Divisor X)
    (hg : ∀ j ∈ s, ∃ hL : (g j).IsCartier, (g j).IsRelativelyAmple f hL) :
    ∃ hL : (∑ j ∈ s, g j).IsCartier, (∑ j ∈ s, g j).IsRelativelyAmple f hL := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hg a (Finset.mem_singleton_self a)
  | cons a s ha hs ih =>
    rw [Finset.sum_cons]
    obtain ⟨h1, h1'⟩ := hg a (Finset.mem_cons_self a s)
    obtain ⟨h2, h2'⟩ := ih fun j hj => hg j (Finset.mem_cons_of_mem hj)
    exact ⟨h1.add h2, isRelativelyAmple_add h1 h1' h2 h2'⟩

/-- A Cartier divisor ample over every affine open of the base is `f`-ample. -/
private theorem isRelativelyAmple_of_isRelativelyAmpleCartier {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} {L : Divisor X}
    (h : MMP.Flips.IsRelativelyAmpleCartier f L) :
    ∃ hL : L.IsCartier, L.IsRelativelyAmple f hL := by
  obtain ⟨hL, h⟩ := h
  refine ⟨hL, fun y => ?_⟩
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨V, hV, hyV, h V hV⟩

/-- A `ℚ`-divisor which is `f`-ample as an `ℝ`-divisor (a positive real combination of `f`-ample
Cartier divisors) has an `f`-ample Cartier multiple: the real coefficients may be replaced by
positive rational ones (`exists_rat_pos_solution`), and a common denominator clears them. -/
private theorem hasRelativelyAmpleMultiple_of_isRelativelyAmple {S X : Scheme.{u}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ S} [QuasiCompact f]
    [IsSeparated f] {D : QDivisor X} (h : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor D)) :
    D.HasRelativelyAmpleMultiple f := by
  classical
  obtain ⟨m, r, L, hm, hr, hL, hD⟩ := h
  have hcoeff : ∀ P, (D.coeff P : ℝ) = ∑ j, r j * ((L j).coeff P : ℤ) := by
    intro P
    have := congrArg (fun E : RDivisor X => E.coeff P) hD
    rw [show (QDivisor.toRDivisor D).coeff P = (D.coeff P : ℝ) from rfl] at this
    rw [this, DivisorWithCoeffs.coeff_apply, Finset.sum_apply']
    refine Finset.sum_congr rfl fun j _ => ?_
    rfl
  obtain ⟨q, hq, hqD⟩ := exists_rat_pos_solution (fun P j => (L j).coeff P) (fun P => D.coeff P)
    r hr hcoeff
  set N : ℕ := ∏ j, (q j).den
  have hN : 0 < N := Finset.prod_pos fun j _ => (q j).den_pos
  have hk : ∀ j, ∃ k : ℕ, 0 < k ∧ (N : ℚ) * q j = k := by
    intro j
    set z : ℤ := (q j).num * ∏ i ∈ Finset.univ.erase j, ((q i).den : ℤ)
    have hz : 0 < z := mul_pos (Rat.num_pos.2 (hq j))
      (Finset.prod_pos fun i _ => by exact_mod_cast (q i).den_pos)
    refine ⟨z.toNat, by omega, ?_⟩
    rw [show ((z.toNat : ℕ) : ℚ) = (z : ℚ) by exact_mod_cast Int.toNat_of_nonneg hz.le]
    simp only [z, N, Int.cast_mul, Int.cast_prod, Int.cast_natCast]
    rw [Nat.cast_prod, ← Finset.mul_prod_erase Finset.univ (fun i => ((q i).den : ℚ))
      (Finset.mem_univ j), mul_right_comm, Rat.den_mul_eq_num]
  choose k hk0 hkq using hk
  obtain ⟨hLs, hLa⟩ := exists_isRelativelyAmple_sum (f := f) (s := Finset.univ)
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun j => k j • L j) fun j _ => by
      obtain ⟨hc, ha⟩ := isRelativelyAmple_of_isRelativelyAmpleCartier (hL j)
      exact ⟨hc.nsmul _, isRelativelyAmple_nsmul hc ha _ (hk0 j)⟩
  refine ⟨N, hN, ∑ j, k j • L j, hLs, ?_, hLa⟩
  ext P
  change (((∑ j, k j • L j).coeff P : ℤ) : ℚ) = (N : ℤ) * D.coeff P
  rw [hqD P, DivisorWithCoeffs.coeff_apply, Finset.sum_apply', Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, hkq j]
  simp [DivisorWithCoeffs.coeff_apply]

/-- A complex projective variety carries an ample invertible module. -/
private theorem exists_isAmple_of_isProjectiveVariety {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) :
    ∃ (L : Z.Modules) (hL : Stacks.Ample.IsInvertibleModule Z L),
      letI : Stacks.Ample.IsInvertibleModule Z L := hL
      Stacks.Ample.IsAmple Z L := by
  have h := (isProjective_tfae_seven_of_exists_isAmple sZ
    ⟨Stacks.Ample.unitModule _, inferInstance,
      Stacks.Ample.isAmple_unitModule_of_isAffine _⟩).out 2 5
  exact (h.mp hZ.isProjective).2

/-- **A proper morphism to a projective variety carrying a relatively ample invertible module is
H-projective** (Stacks 0B45, clause (6) ⟹ clause (2)). -/
private theorem isProjectiveMorphism_of_isRelativelyAmple {V Z : Scheme.{0}}
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (p : V ⟶ Z) (hp : IsProper p)
    (hL : ∃ (L : V.Modules) (hL : Stacks.Ample.IsInvertibleModule V L),
      letI : Stacks.Ample.IsInvertibleModule V L := hL
      Stacks.RelativeAmple.IsRelativelyAmple p L) :
    IsProjectiveMorphism p := by
  have h := (isProjective_tfae_seven_of_exists_isAmple p
    (exists_isAmple_of_isProjectiveVariety hZ)).out 6 2
  exact h.mp ⟨hp, hL⟩

/-- A proper morphism to a projective variety with an `ℝ`-divisor ample over the base is
H-projective. -/
private theorem isProjectiveMorphism_of_isRelativelyAmple_rDivisor {V Z : Scheme.{0}}
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (p : V ⟶ Z) [IsProper p] {E : RDivisor V}
    (h : MMP.Flips.IsRelativelyAmple p E) : IsProjectiveMorphism p := by
  obtain ⟨m, r, L, hm, -, hL, -⟩ := h
  obtain ⟨hc, ha⟩ := isRelativelyAmple_of_isRelativelyAmpleCartier (hL ⟨0, hm⟩)
  haveI := hc.isInvertibleModule_divisorialSheaf
  exact isProjectiveMorphism_of_isRelativelyAmple hZ p inferInstance
    ⟨_, inferInstance, stacks_isRelativelyAmple_of_isRelativelyAmple p _ ha⟩

/-- **Relative ampleness restricts to closed subschemes.** If `D` has an `f`-ample Cartier
multiple and `D'` is its pull-back along a closed immersion `ι`, then `D'` has an `ι ≫ f`-ample
Cartier multiple: `𝒪(ι^* L) ≅ ι^* 𝒪(L)` (`MMP.Mori.Divisor.nonempty_divisorialSheaf_pullback_iso`)
and relative ampleness is preserved by pull-back along affine morphisms. -/
private theorem hasRelativelyAmpleMultiple_of_isPullback {X S Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral S] [IsLocallyNoetherian S]
    [IsNormal S] [CompactSpace S] {ι : S ⟶ X} [IsClosedImmersion ι] {f : X ⟶ Y}
    [QuasiCompact f] {D : QDivisor X} {D' : QDivisor S}
    {hB : ∀ Z : irreducibleComponents S, ι (componentGenericPoint S Z) ∉ D.supp}
    (hpb : D.IsPullback ι hB D') (hD : D.HasRelativelyAmpleMultiple f) :
    D'.HasRelativelyAmpleMultiple (ι ≫ f) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := hD
  obtain ⟨L', hL'D', hpbL⟩ := hpb m hm L hLD hL
  have hB' : ∀ Z : irreducibleComponents S, ι (componentGenericPoint S Z) ∉ L.supp := fun Z hZ =>
    hB Z (by rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hLD] at hZ)
  have heq : L.pullback hL hB' = L' := Divisor.IsPullback.pullback_eq hL hpbL
  have hL'c : L'.IsCartier := heq ▸ hL.isCartier_pullback ι hB'
  refine ⟨m, hm, L', hL'c, hL'D', ?_⟩
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := hL'c.isInvertibleModule_divisorialSheaf
  have h := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom ι f
    L.divisorialSheaf (stacks_isRelativelyAmple_of_isRelativelyAmple f _ hamp)
  obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hL ι hB'
  refine MMP.Mori.IsRelativelyAmple.of_stacks _ _ ((isRelativelyAmple_congr _ _ _ ?_).mp h)
  rw [← heq]
  exact modulePullbackIso ι _ ≪≫ e.symm

/-- **Relative ampleness depends only on the linear equivalence class.** Adding a principal
divisor `div ψ` to a `ℚ`-divisor with an `f`-ample Cartier multiple gives one: if `L = m D` then
`L + div ψ^m = m (D + div ψ)`, and `𝒪(L + div ψ^m) ≅ 𝒪(L)` by multiplication by `ψ^m`. -/
private theorem hasRelativelyAmpleMultiple_add_principalDivisor {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Y}
    [QuasiCompact f] {D : QDivisor X} (hD : D.HasRelativelyAmpleMultiple f)
    (ψ : (RationalFunctions X)ˣ) :
    (D + Divisor.toQDivisor (principalDivisor ψ)).HasRelativelyAmpleMultiple f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := hD
  set L' := L + principalDivisor (ψ ^ (m : ℤ))
  have hcoeff : ∀ E : MMP.Mori.PrimeDivisor X,
      L'.coeff E = L.coeff E + E.ord (ψ ^ (m : ℤ)) := fun E => by
    simp [L', DivisorWithCoeffs.coeff_add]
  have hL'c : L'.IsCartier := hL.add (MMP.Mori.Divisor.isCartier_principalDivisor _)
  refine ⟨m, hm, L', hL'c, ?_, ?_⟩
  · ext E
    have h1 := congrArg (fun A : QDivisor X => A.coeff E) hLD
    simp only [DivisorWithCoeffs.coeff_apply] at h1 ⊢
    change ((L'.coeff E : ℤ) : ℚ) = _
    rw [hcoeff, MMP.Mori.PrimeDivisor.ord_zpow]
    change _ = ((m : ℤ) : ℚ) * (D E + ((principalDivisor ψ).coeff E : ℚ))
    rw [MMP.Mori.coeff_principalDivisor]
    change ((L.coeff E : ℤ) : ℚ) = ((m : ℤ) : ℚ) * D E at h1
    push_cast
    rw [h1]
    simp only [smul_eq_mul, Int.cast_mul, Int.cast_natCast]
    ring
  · haveI := hL.isInvertibleModule_divisorialSheaf
    haveI := hL'c.isInvertibleModule_divisorialSheaf
    refine MMP.Mori.IsRelativelyAmple.of_stacks _ _
      ((isRelativelyAmple_congr _ _ _
        (MMP.Mori.Divisor.divisorialSheafMulIso (ψ ^ (m : ℤ)) hcoeff)).mpr
        (stacks_isRelativelyAmple_of_isRelativelyAmple f _ hamp))

end RelativelyAmple

/-! ### Finiteness of the boundary strata -/

section FiniteStrata

/-- In a Noetherian space, a closed set has only finitely many maximal irreducible subsets: they
are among the finitely many irreducible closed pieces of the set. -/
private theorem finite_setOf_maximal_isIrreducible {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] {C : Set X} (hC : IsClosed C) :
    {T : Set X | Maximal (fun T => IsIrreducible T ∧ T ⊆ C) T}.Finite := by
  classical
  obtain ⟨S, hSf, hScl, hSirr, rfl⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  refine hSf.subset fun T hT => ?_
  obtain ⟨z, hz, hTz⟩ := (isIrreducible_iff_sUnion_isClosed.mp hT.1.1) hSf.toFinset
    (fun z hz => hScl z (hSf.mem_toFinset.mp hz)) (by simpa using hT.1.2)
  rw [Set.Finite.mem_toFinset] at hz
  have hzT : z ⊆ T := hT.2 ⟨hSirr z hz, Set.subset_sUnion_of_mem hz⟩ hTz
  exact (Set.Subset.antisymm hTz hzT) ▸ hz

/-- A Noetherian pair has only finitely many boundary strata. -/
private theorem finite_setOf_isDltStratum {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} (B : QDivisor X) :
    {T : Set X | IsDltStratum sX B T}.Finite := by
  classical
  haveI : IsNoetherian X := {}
  refine (B.support.powerset.finite_toSet.biUnion fun J _ =>
    finite_setOf_maximal_isIrreducible (C := ⋂ P ∈ J, (P.support : Set X))
      (isClosed_biInter fun P _ => by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)).subset ?_
  rintro T ⟨-, J, -, hJ, -, hmax⟩
  refine Set.mem_biUnion (x := J) ?_ hmax
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  intro P hP
  rw [Finsupp.mem_support_iff]
  have := hJ P hP
  intro h0
  rw [DivisorWithCoeffs.coeff_apply, h0] at this
  norm_num at this

end FiniteStrata

/-! ### Birational transforms along a flip -/

section Transforms

variable {X Y Z : Scheme.{0}}

/-- Extending a composite `φ₂ ∘ φ₁` of partial maps on prime divisors linearly is composing the
linear extensions. -/
private theorem mapPrimeDivisors_bind {R : Type*} [AddCommMonoid R]
    (φ₁ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (φ₂ : MMP.Mori.PrimeDivisor Y → Option (MMP.Mori.PrimeDivisor Z)) (D : DivisorWithCoeffs R X) :
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
    {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y} (hφ : MMP.Flips.RationalMap.IsOver f g φ)
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

/-- For small `f` and `f⁺`, the birational transform of divisors under a modification `φ` of `f`
into `f⁺` is the strict transform `(f⁺)⁻¹_* f_*`. -/
private theorem transformDivisor_eq_flipTransform_of_small
    {Xm Xp Z : Scheme.{0}} [IsIntegral Xm]
    [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated (Xp ↘ ⊤_ Scheme)] {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (hsmall : 2 ≤ closedsCodimension (exceptionalSet fm))
    (hsmall' : 2 ≤ closedsCodimension (exceptionalSet fp))
    {φ : Xm.RationalMap Xp} (hφ : MMP.Flips.IsModificationOf fm fp φ)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) :
    MMP.Mori.RationalMap.transformDivisor φ D = flipTransform fm fp D := by
  have hpt : ∀ P : MMP.Mori.PrimeDivisor Xm, MMP.Mori.RationalMap.transformPrimeDivisor φ P =
      (MMP.Mori.RationalMap.transformPrimeDivisor (X := Xm) fm.toRationalMap P).bind
        (inverseTransformPrimeDivisor fp) := by
    intro P
    have hcoh : Order.coheight (fm P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fm
        (Oai4C1.map_genericPoint_mem_biregularLocus hsmall P),
        P.coheight_genericPoint]
    set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
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
      set P' : MMP.Mori.PrimeDivisor Xp := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcy
      have hP' : y = P'.genericPoint :=
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy).symm
      rw [inverseTransformPrimeDivisor_eq_some_of_map_genericPoint (E := P') (hP' ▸ hyQ)
        (hP' ▸ hyV)]
      exact transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hPU hP'.symm
    · have hnone : inverseTransformPrimeDivisor fp Q = none := by
        rw [inverseTransformPrimeDivisor_eq_none_iff]
        rintro ⟨⟨z, hzQ, hzV⟩, -⟩
        have hz : Q.genericPoint ⤳ z := by
          have : z ∈ Q.support := hzQ
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
          exact specializes_iff_mem_closure.mpr this
        exact hV (hz.mem_open (biregularLocus fp).2 hzV)
      rw [hnone, MMP.Mori.RationalMap.transformPrimeDivisor_eq_none_iff]
      rintro ⟨hdef, E, hE⟩
      have hsome : MMP.Mori.RationalMap.transformPrimeDivisor φ P = some E :=
        MMP.Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr ⟨hdef, hE⟩
      obtain ⟨ψ, hPψ, hψ⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
      have hηE := genericPoint_eq_of_transformPrimeDivisor_eq_some hsome ψ hψ hPψ
      have h1 : fp E.genericPoint = Q.genericPoint := by
        rw [hηE]
        exact (hom_apply_eq_of_comp_eq (hom_comp_eq_of_isOver hφ.2 ψ hψ)
          ⟨P.genericPoint, hPψ⟩).trans hQ
      exact hV (h1 ▸ Oai4C1.map_genericPoint_mem_biregularLocus
        hsmall' E)
  change DivisorWithCoeffs.mapPrimeDivisors _ D = inverseTransformDivisor fp
    (MMP.Mori.RationalMap.transformDivisor (X := Xm) fm.toRationalMap D)
  rw [funext hpt]
  exact mapPrimeDivisors_bind _ _ D

/-- If `f` maps a nonempty open `V` of an irreducible scheme isomorphically onto an open `U`, with
`V ⊆ f⁻¹(U)` and `f` separated, then `f` is biregular over `U`: the inclusion `V ⊆ f⁻¹(U)` is a
section of a separated morphism, hence closed, and so equal to the irreducible `f⁻¹(U)`. -/
private theorem isBiregular_of_isIso_resLE {X Y : Scheme.{0}} [IrreducibleSpace X] (f : X ⟶ Y)
    [IsSeparated f] (U : Y.Opens) (V : X.Opens) (hV : (V : Set X).Nonempty) (h : V ≤ f ⁻¹ᵁ U)
    [IsIso (f.resLE U V h)] : IsBiregular f U := by
  have hres : f.resLE U V h = X.homOfLE h ≫ f ∣_ U := by
    simp [Scheme.Hom.resLE, morphismRestrict]
  set j := X.homOfLE h
  have hj : j ≫ (f ∣_ U ≫ inv (f.resLE U V h)) = 𝟙 _ := by
    rw [← Category.assoc, ← hres, IsIso.hom_inv_id]
  have : IsClosedImmersion j := by
    have : IsClosedImmersion (j ≫ (f ∣_ U ≫ inv (f.resLE U V h))) := by rw [hj]; infer_instance
    exact IsClosedImmersion.of_comp j (f ∣_ U ≫ inv (f.resLE U V h))
  have hsurj : Function.Surjective j := by
    obtain ⟨x, hx⟩ := hV
    have : PreconnectedSpace (f ⁻¹ᵁ U) := Subtype.preconnectedSpace
      (IsPreirreducible.open_subset (IrreducibleSpace.isIrreducible_univ X).isPreirreducible
        (f ⁻¹ᵁ U).2 (Set.subset_univ _)).isPreconnected
    have hcl : IsClopen (Set.range j) :=
      ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
    exact Set.range_eq_univ.mp (hcl.eq_univ ⟨_, ⟨⟨x, hx⟩, rfl⟩⟩)
  have : IsIso j :=
    (isIso_iff_isOpenImmersion_and_epi_base j).mpr
      ⟨inferInstance, (TopCat.epi_iff_surjective _).mpr hsurj⟩
  have : f ∣_ U = inv j ≫ f.resLE U V h := by rw [hres, IsIso.inv_hom_id_assoc]
  change IsIso (f ∣_ U)
  rw [this]; infer_instance

/-- A small birational contraction (FA 2.1.6) has exceptional set `Ex(f) = Y ∖ f⁻¹(V_f)` of
codimension at least two. -/
private theorem two_le_closedsCodimension_exceptionalSet_of_isSmall {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral Y] {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {f : Y ⟶ X} (hf : MMP.Flips.IsSmall k sX sY f) :
    2 ≤ closedsCodimension (exceptionalSet f) := by
  obtain ⟨V, W, hV, -, h, hiso⟩ := hf.exists_isIso
  have := hf.isProper
  have hne : (V.compl : Set Y).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    have hg : genericPoint Y ∈ (V : Set Y) := by
      by_contra hg'
      exact (hc.symm ▸ (show genericPoint Y ∈ (V.compl : Set Y) from hg') :
        genericPoint Y ∈ (∅ : Set Y))
    have h2 := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV _ hg
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at h2
    exact absurd h2 (by decide)
  have hb := isBiregular_of_isIso_resLE f W.compl V.compl hne h
  have hsub : (MMP.Mori.exceptionalSet f : Set Y) ⊆ V := by
    intro y hy
    by_contra hyV
    exact mem_exceptionalSet.mp hy (le_biregularLocus hb (h hyV))
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at hV ⊢
  exact fun y hy => hV y (hsub hy)

/-- A morphism over `Spec ℂ` from a separated scheme is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {s : X ⟶ Spec (.of ℂ)} [IsSeparated s] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  have : (X ↘ ⊤_ Scheme) = s ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
  rw [this]
  infer_instance

/-- Along a step of a sequence of flips, the birational transform by `g_i : X_i ⤏ X_{i+1}` is the
strict transform `(φ_i⁺)⁻¹_* (φ_i)_*`. -/
private theorem transformDivisor_flipMap_eq_flipTransform {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfFlips sX n K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R (S.model i).1) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    MMP.Mori.RationalMap.transformDivisor (S.flipMap i) D =
      flipTransform (S.contraction i) (S.flip i) D := by
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hfl := S.isFlip i hi
  have : IsIntegral (S.model i).1 :=
    (S.isNormalVariety_model i (lt_of_le_of_lt (by exact_mod_cast i.le_succ) hi)).1.toIsIntegral
  have : IsIntegral (S.model (i + 1)).1 := hfl.isNormalVariety_flip.1.toIsIntegral
  have : IsSeparated (S.baseStr i) := hfl.isNormalVariety_target.1.toIsSeparated
  have : IsSeparated (S.base i ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := S.baseStr i)
  have : IsSeparated (S.model (i + 1)).2.1 := hfl.isNormalVariety_flip.1.toIsSeparated
  have : IsSeparated ((S.model (i + 1)).1 ↘ ⊤_ Scheme) :=
    isSeparated_toTerminal (s := (S.model (i + 1)).2.1)
  exact transformDivisor_eq_flipTransform_of_small
    (two_le_closedsCodimension_exceptionalSet_of_isSmall (S.isSmall i hi))
    (two_le_closedsCodimension_exceptionalSet_of_isSmall hfl.isSmall) hfl.isModificationOf D

/-- Along a step of a sequence of flips, `D_{i+1} = (φ_i⁺)⁻¹_* (φ_i)_* D_i`. -/
private theorem boundary_succ_eq_flipTransform {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfFlips sX n K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    (S.model (i + 1)).2.2.2 = flipTransform (S.contraction i) (S.flip i) (S.model i).2.2.2 := by
  rw [S.transform_eq i hi, transformDivisor_flipMap_eq_flipTransform S i hi]

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {R S : Type*} [AddCommMonoid R]
    [AddCommMonoid S] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
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
private theorem flipTransform_mapCoeffsAddMonoidHom {X' : Scheme.{0}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (fm : X ⟶ Y) (fp : X' ⟶ Y) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    flipTransform fm fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (flipTransform fm fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- `K + B`, for a canonical divisor `K` and a `ℚ`-divisor `B`, as an `ℝ`-divisor. -/
private theorem logCanonicalDivisor_eq (K : Divisor X) (B : QDivisor X) :
    MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + B) := by
  rw [MMP.Flips.logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-- **A step of a sequence of flips is a flip in the sense of `MMP.Fourfold.IsFlipOf`**, when the
contraction target is projective: the `ℝ`-Cartier and `ℝ`-ample conditions on `K_i + D_i` and
its transform become `ℚ`-Cartier conditions with ample Cartier multiples, and the two proper
morphisms, being relatively ample over a projective base, are projective. -/
private theorem isFlipOf_of_sequenceOfFlips {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {n : ℕ}
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfFlips sX n K B) (i : ℕ)
    (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) (hZ : MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) :
    haveI := S.isLocallyNoetherian_model i
    haveI := S.isNormal_model i
    haveI := S.compactSpace_model i
    haveI := S.isLocallyNoetherian_model (i + 1)
    haveI := S.isNormal_model (i + 1)
    haveI := S.compactSpace_model (i + 1)
    IsFlipOf (S.model i).2.1 (S.baseStr i) (S.model (i + 1)).2.1
      (Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2) (S.contraction i) (S.flip i) := by
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hneg := S.isNegativeExtremalContraction i hi
  have hfl := S.isFlip i hi
  have hsm := S.isSmall i hi
  have : IsIntegral (S.model i).1 := hneg.isNormalVariety_source.1.toIsIntegral
  have : IsIntegral (S.model (i + 1)).1 := hfl.isNormalVariety_flip.1.toIsIntegral
  have : IsProper (S.contraction i) := hneg.isContraction.isProper
  have : IsProper (S.flip i) := hfl.isProper
  rw [logCanonicalDivisor_eq] at hneg hfl
  set D := Divisor.toQDivisor (S.model i).2.2.1 + (S.model i).2.2.2
  have htr : MMP.Mori.RationalMap.transformDivisor (S.flipMap i) (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (flipTransform (S.contraction i) (S.flip i) D) := by
    rw [transformDivisor_flipMap_eq_flipTransform S i hi]
    exact flipTransform_mapCoeffsAddMonoidHom _ _ _ D
  have hamp := hfl.isRelativelyAmple_transform
  rw [htr] at hamp
  have hcart := hfl.isCartierCombination_transform
  rw [htr] at hcart
  have hanti : MMP.Flips.IsRelativelyAmple (S.contraction i) (QDivisor.toRDivisor (-D)) := by
    rw [map_neg]; exact hneg.isRelativelyAntiAmple
  refine
    { isQCartier := MMP.Flips.QDivisor.isQCartier_of_isCartierCombination hneg.isCartierCombination
      isContraction :=
        { isNormalVariety_source := hneg.isNormalVariety_source
          isNormalVariety_target := hneg.isNormalVariety_target
          comp_eq := hneg.isContraction.comp_eq
          isProjectiveMorphism :=
            isProjectiveMorphism_of_isRelativelyAmple_rDivisor hZ _ hneg.isRelativelyAntiAmple
          surjective := (hsm.toIsBirationalContraction.surjective_and_isBirational).1.surj
          isIso_app := hneg.isContraction.isIso_app }
      isSmallMorphism :=
        { isNormalVariety_source := hneg.isNormalVariety_source
          isNormalVariety_target := hneg.isNormalVariety_target
          comp_eq := hneg.isContraction.comp_eq
          isProper := inferInstance
          isBirationalMorphism := MMP.Flips.IsSmall.isBirationalMorphism _ _ hsm
          two_le_codimension := two_le_closedsCodimension_exceptionalSet_of_isSmall hsm }
      hasRelativelyAmpleMultiple := hasRelativelyAmpleMultiple_of_isRelativelyAmple hanti
      isSmallMorphism_flip :=
        { isNormalVariety_source := hfl.isNormalVariety_flip
          isNormalVariety_target := hfl.isNormalVariety_target
          comp_eq := hfl.isSmall.comp_eq
          isProper := inferInstance
          isBirationalMorphism := MMP.Flips.IsSmall.isBirationalMorphism _ _ hfl.isSmall
          two_le_codimension := two_le_closedsCodimension_exceptionalSet_of_isSmall hfl.isSmall }
      isProjectiveMorphism_flip := isProjectiveMorphism_of_isRelativelyAmple_rDivisor hZ _ hamp
      isQCartier_flip := MMP.Flips.QDivisor.isQCartier_of_isCartierCombination hcart
      hasRelativelyAmpleMultiple_flip := hasRelativelyAmpleMultiple_of_isRelativelyAmple hamp }

/-- A point whose image lies in the biregular locus of `f` has a neighbourhood on which `f` is an
open immersion. -/
private theorem image_flipsExceptionalSet_disjoint_biregularLocus {X Y : Scheme.{0}} (f : X ⟶ Y) :
    Disjoint (biregularLocus f : Set Y) (f '' MMP.Flips.exceptionalSet f) := by
  rw [Set.disjoint_left]
  rintro _ hW ⟨y, hy, rfl⟩
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  refine hy ⟨f ⁻¹ᵁ biregularLocus f, hW, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

/-- Along a step of a sequence of flips, the flip `φ_i⁺` is an isomorphism over the biregular
locus of the contraction `φ_i` (FA 4: a flip is an isomorphism off the flipping locus). -/
private theorem isIso_flip_morphismRestrict_biregularLocus {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfFlips sX n K B) (i : ℕ) (hi : ((i + 1 : ℕ) : ℕ∞) < S.length) :
    IsIso (S.flip i ∣_ biregularLocus (S.contraction i)) := by
  have := S.isLocallyNoetherian_model i
  have := S.isNormal_model i
  have := S.compactSpace_model i
  have := S.isLocallyNoetherian_model (i + 1)
  have := S.isNormal_model (i + 1)
  have := S.compactSpace_model (i + 1)
  have hneg := S.isNegativeExtremalContraction i hi
  have hfl := S.isFlip i hi
  rw [logCanonicalDivisor_eq] at hneg hfl
  exact hfl.isIso_morphismRestrict_of_disjoint_image_exceptionalSet
    (MMP.Flips.QDivisor.isQCartier_of_isCartierCombination hneg.isCartierCombination) _
    (image_flipsExceptionalSet_disjoint_biregularLocus _)

/-- Pushing forward along an isomorphism `e` and pulling back along `e` are inverse. -/
private theorem inverseTransformDivisor_transformDivisor_of_isIso {T T' : Scheme.{0}}
    [IsIntegral T] [IsSeparated (T' ↘ ⊤_ Scheme)] (e : T ⟶ T') [IsIso e] {R : Type}
    [AddCommMonoid R]
    (D : DivisorWithCoeffs R T) :
    inverseTransformDivisor e (MMP.Mori.RationalMap.transformDivisor (X := T) e.toRationalMap D) =
      D := by
  have hb : biregularLocus e = ⊤ := top_le_iff.mp (le_biregularLocus (by
    change IsIso _; infer_instance))
  have hP : ∀ P : MMP.Mori.PrimeDivisor T,
      (MMP.Mori.RationalMap.transformPrimeDivisor (X := T) e.toRationalMap P).bind
        (inverseTransformPrimeDivisor e) = some P := by
    intro P
    have hV : e P.genericPoint ∈ biregularLocus e := by rw [hb]; trivial
    have hcoh : Order.coheight (e P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus e hV, P.coheight_genericPoint]
    set Q : MMP.Mori.PrimeDivisor T' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
    have hQ : e P.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e P Q).mpr hQ,
      Option.bind_some]
    exact inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hQ hV
  change DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _ D) = D
  rw [← mapPrimeDivisors_bind, funext hP]
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r => rw [DivisorWithCoeffs.mapPrimeDivisors_single]; rfl

end Transforms

/-- **Eventually no boundary stratum is lost**
(`MMP.Fourfold.exists_forall_ge_not_subset_exceptionalSet_of_isDltStratum` applied to the tail of
the sequence from `N` on): from some step on, no boundary stratum of `(X_i, B_i)` lies in
the flipping locus, none of `(X_{i+1}, B_{i+1})` lies in the flipped locus, and every stratum of
`(X_i, B_i)` has a stratum of `(X_{i+1}, B_{i+1})` with the same image in `Z_i`. -/
private theorem exists_forall_ge_strata_not_subset {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} (S : SequenceOfFlips sX 4 K B) (hL : S.length = ⊤) (N : ℕ)
    (hproj : ∀ i ≥ N, MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1)
    (hbase : ∀ i ≥ N, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i))
    (hdlt : ∀ i ≥ N, ∀ hi : (i : ℕ∞) < S.length,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI : IsIntegral (S.model i).1 := (S.isNormalVariety_model i hi).1.toIsIntegral
      MMP.Intersection.IsDltPair (S.model i).2.1 (S.model i).2.2.2) :
    ∃ M ≥ N, ∀ i ≥ M,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.isLocallyNoetherian_model (i + 1)
      haveI := S.isNormal_model (i + 1)
      haveI : IsIntegral (S.model i).1 :=
        (S.isNormalVariety_model i (hL ▸ ENat.coe_lt_top i)).1.toIsIntegral
      haveI : IsIntegral (S.model (i + 1)).1 :=
        (S.isNormalVariety_model (i + 1) (hL ▸ ENat.coe_lt_top _)).1.toIsIntegral
      (∀ T : Set (S.model i).1, IsDltStratum (S.model i).2.1 (S.model i).2.2.2 T →
        ¬ T ⊆ (MMP.Mori.exceptionalSet (S.contraction i) : Set (S.model i).1)) ∧
      (∀ T' : Set (S.model (i + 1)).1,
        IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 T' →
        ¬ T' ⊆ (MMP.Mori.exceptionalSet (S.flip i) : Set (S.model (i + 1)).1)) ∧
      (∀ T : Set (S.model i).1, IsDltStratum (S.model i).2.1 (S.model i).2.2.2 T →
        ∃ T' : Set (S.model (i + 1)).1,
          IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 T' ∧
          closure ((S.contraction i).base '' T) = closure ((S.flip i).base '' T')) := by
  have hlt : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hL ▸ ENat.coe_lt_top i
  haveI : ∀ j, IsLocallyNoetherian (S.model (N + j)).1 := fun j => S.isLocallyNoetherian_model _
  haveI : ∀ j, IsNormal (S.model (N + j)).1 := fun j => S.isNormal_model _
  haveI : ∀ j, CompactSpace (S.model (N + j)).1 := fun j => S.compactSpace_model _
  haveI : ∀ j, IsIntegral (S.model (N + j)).1 := fun j =>
    (S.isNormalVariety_model _ (hlt _)).1.toIsIntegral
  obtain ⟨M, hM⟩ := exists_forall_ge_not_subset_exceptionalSet_of_isDltStratum
    (X := fun j => (S.model (N + j)).1) (Z := fun j => S.base (N + j))
    (sX := fun j => (S.model (N + j)).2.1) (sZ := fun j => S.baseStr (N + j))
    (f := fun j => S.contraction (N + j)) (fp := fun j => S.flip (N + j))
    (n := 4) (K := fun j => (S.model (N + j)).2.2.1) (B := fun j => (S.model (N + j)).2.2.2)
    (L := ⊤) (hproj N le_rfl) (hdlt N le_rfl (hlt N))
    (fun j _ => S.isCanonicalDivisor_model _ (hlt _))
    (fun j _ => isFlipOf_of_sequenceOfFlips S (N + j) (hlt _) (hbase _ (Nat.le_add_right _ _)))
    (fun j _ => boundary_succ_eq_flipTransform S (N + j) (hlt _))
  refine ⟨N + M, Nat.le_add_right _ _, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
  exact hM j (by omega) (ENat.coe_lt_top _)

/-! ### The identity as a flip -/

section IdentityFlip

/-- Every Cartier divisor is ample relative to an isomorphism. -/
private theorem isRelativelyAmple_of_isIso {X Y : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (e : X ⟶ Y) [IsIso e] {L : Divisor X}
    (hL : L.IsCartier) : L.IsRelativelyAmple e hL := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  intro y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  refine ⟨V, hV, hyV, ?_⟩
  haveI : IsAffine (e ⁻¹ᵁ V) := hV.preimage e
  haveI : CompactSpace (e ⁻¹ᵁ V) := inferInstance
  have hinv : Stacks.Ample.IsInvertibleModule (e ⁻¹ᵁ V).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (e ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- The birational transform under the identity is the identity. -/
private theorem transformDivisor_id {Y : Scheme.{0}} [IsReduced Y]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) :
    MMP.Mori.RationalMap.transformDivisor (X := Y) (𝟙 Y : Y ⟶ Y).toRationalMap D = D := by
  have h (E : MMP.Mori.PrimeDivisor Y) :
      MMP.Mori.RationalMap.transformPrimeDivisor (X := Y) (𝟙 Y : Y ⟶ Y).toRationalMap E =
        some E :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff (𝟙 Y) E E).mpr rfl
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, hD, hD']
  | single E r => exact MMP.Mori.RationalMap.transformDivisor_single_of_eq_some (h E) r

/-- The strict transform along the identity is the identity. -/
private theorem flipTransform_id {Y : Scheme.{0}} [IsReduced Y]
    [IsSeparated (Y ↘ Limits.terminal Scheme)] {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Y) : flipTransform (𝟙 Y) (𝟙 Y) D = D := by
  simp only [flipTransform, AddMonoidHom.comp_apply, transformDivisor_id,
    inverseTransformDivisor_id]

/-- The identity has empty exceptional set. -/
private theorem two_le_closedsCodimension_exceptionalSet_id (X : Scheme.{0}) :
    2 ≤ closedsCodimension (exceptionalSet (𝟙 X)) := by
  have hb : biregularLocus (𝟙 X) = ⊤ := top_le_iff.mp (le_biregularLocus (by
    change IsIso _; infer_instance))
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  exact absurd (show (𝟙 X) x ∈ biregularLocus (𝟙 X) by rw [hb]; trivial) (mem_exceptionalSet.mp hx)

/-- Every `ℚ`-Cartier divisor has a Cartier multiple ample over the identity. -/
private theorem hasRelativelyAmpleMultiple_id {X : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} (hD : D.IsQCartier) :
    D.HasRelativelyAmpleMultiple (𝟙 X) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := hD.exists_pos
  exact ⟨m, hm, L, hLc, hL, isRelativelyAmple_of_isIso _ hLc⟩

/-- **The identity is a flip of itself** for every `ℚ`-Cartier divisor on a projective normal
variety. -/
private theorem isFlipOf_id {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hXn : IsNormalVariety ℂ sX) {D : QDivisor X} (hD : D.IsQCartier) :
    IsFlipOf sX sX sX D (𝟙 X) (𝟙 X) := by
  have : IsSeparated sX := hXn.1.toIsSeparated
  have : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  have hproj : IsProjectiveMorphism (𝟙 X) := by
    have h0 := isRelativelyAmple_of_isIso (𝟙 X) (MMP.Mori.Divisor.isCartier_zero (X := X))
    haveI := (MMP.Mori.Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
    exact isProjectiveMorphism_of_isRelativelyAmple hX (𝟙 X) inferInstance
      ⟨_, inferInstance, stacks_isRelativelyAmple_of_isRelativelyAmple (𝟙 X) _ h0⟩
  have hsm : IsSmallMorphism sX sX (𝟙 X) :=
    ⟨hXn, hXn, Category.id_comp _, inferInstance, isBirationalMorphism_of_isIso _,
      two_le_closedsCodimension_exceptionalSet_id X⟩
  refine
    { isQCartier := hD
      isContraction := ⟨hXn, hXn, Category.id_comp _, hproj, Function.surjective_id,
        fun U => inferInstance⟩
      isSmallMorphism := hsm
      hasRelativelyAmpleMultiple := hasRelativelyAmpleMultiple_id (by
        obtain ⟨m, hm, h⟩ := hD; exact ⟨m, hm, by rw [smul_neg]; exact h.neg⟩)
      isSmallMorphism_flip := hsm
      isProjectiveMorphism_flip := hproj
      isQCartier_flip := by rw [flipTransform_id]; exact hD
      hasRelativelyAmpleMultiple_flip := by
        rw [flipTransform_id]; exact hasRelativelyAmpleMultiple_id hD }

end IdentityFlip

/-! ### Uniqueness of the adjunction boundary -/

section AdjunctionUniqueness

/-- The kernel of a morphism from a reduced scheme is the vanishing ideal of the closure of its
image. -/
private theorem ker_eq_vanishingIdeal_closure_range {X Y : Scheme.{0}} [IsReduced X]
    (f : X ⟶ Y) :
    f.ker = Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure (Set.range f)) := by
  rw [← Scheme.IdealSheafData.map_bot]
  have : (⊥ : X.IdealSheafData) = Scheme.IdealSheafData.vanishingIdeal ⊤ := by
    rw [Scheme.IdealSheafData.vanishingIdeal_top]
    exact Eq.symm Scheme.nilradical_eq_bot
  rw [this, Scheme.IdealSheafData.map_vanishingIdeal]
  simp

/-- Two closed immersions from reduced schemes with the same image differ by an isomorphism of
their sources. -/
private theorem exists_iso_of_range_eq {X₁ X₂ Y : Scheme.{0}} [IsReduced X₁] [IsReduced X₂]
    (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) [IsClosedImmersion f₁] [IsClosedImmersion f₂]
    (h : Set.range f₁ = Set.range f₂) : ∃ e : X₁ ≅ X₂, e.hom ≫ f₂ = f₁ := by
  have hk : f₁.ker = f₂.ker := by
    rw [ker_eq_vanishingIdeal_closure_range, ker_eq_vanishingIdeal_closure_range, h]
  refine ⟨⟨IsClosedImmersion.lift f₂ f₁ hk.ge, IsClosedImmersion.lift f₁ f₂ hk.le, ?_, ?_⟩,
    IsClosedImmersion.lift_fac _ _ _⟩
  · rw [← cancel_mono f₁, Category.assoc, IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac,
      Category.id_comp]
  · rw [← cancel_mono f₂, Category.assoc, IsClosedImmersion.lift_fac, IsClosedImmersion.lift_fac,
      Category.id_comp]

/-- The stalk map of `e ≫ g'` at the generic point, for an isomorphism `e`, is the stalk map of
`g'` at the generic point followed by the extension of function fields of `e`. -/
private theorem stalkMap_comp_genericPoint_eq {Z T T' : Scheme.{0}} [IsIntegral T] [IsIntegral T']
    (e : T ⟶ T') [IsIso e] (g' : T' ⟶ Z)
    (hη : (e ≫ g') (genericPoint T) = g' (genericPoint T')) :
    (e ≫ g').stalkMap (genericPoint T) =
      ((Z.presheaf.stalkCongr (.of_eq hη)).hom ≫ g'.stalkMap (genericPoint T')) ≫
        (T'.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant e).symm)).hom ≫
          e.stalkMap (genericPoint T) := by
  have hx : genericPoint T' = e (genericPoint T) := (map_genericPoint_of_isDominant e).symm
  have h := Scheme.Hom.stalkMap_congr_point g' _ _ hx
  rw [Scheme.Hom.stalkMap_comp, Category.assoc, reassoc_of% h]
  simp only [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  erw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  rfl

/-- Divisorial valuations correspond along an isomorphism `e : T ≅ T'` over `Z`: read in the
stalk of `Z` at the common image of the generic points, `ord_P` on `T` is `ord_{e(P)}` on `T'`. -/
private theorem divisorialValuation_comap_stalkMap_eq_of_isIso {Z T T' : Scheme.{0}}
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsIntegral T'] [IsLocallyNoetherian T'] [IsNormal T']
    (e : T ⟶ T') [IsIso e] (g' : T' ⟶ Z) (g : T ⟶ Z) (hg : e ≫ g' = g)
    (hη : g (genericPoint T) = g' (genericPoint T'))
    (P : MMP.Mori.PrimeDivisor T) (Q : MMP.Mori.PrimeDivisor T')
    (hPQ : e P.genericPoint = Q.genericPoint) :
    P.divisorialValuation.comap (g.stalkMap (genericPoint T)).hom =
      Q.divisorialValuation.comap
        ((Z.presheaf.stalkCongr (.of_eq hη)).hom ≫ g'.stalkMap (genericPoint T')).hom := by
  subst hg
  refine Valuation.ext fun z => ?_
  rw [Valuation.comap_apply, Valuation.comap_apply, stalkMap_comp_genericPoint_eq e g' hη]
  set w := ((Z.presheaf.stalkCongr (.of_eq hη)).hom ≫ g'.stalkMap (genericPoint T')).hom z
  change P.divisorialValuation (functionFieldMap e w) = Q.divisorialValuation w
  by_cases hw : w = 0
  · rw [hw, map_zero, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr hw),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hw,
    MMP.Positivity.ord_functionFieldMap_of_isIso e P Q hPQ w]

/-- The alternating parity `true, false, true, …`. -/
private def alt : ℕ → Bool
  | 0 => true
  | n + 1 => !alt n

/-- Two schemes indexed by `Bool`. -/
private def boolScheme (T₁ T₂ : Scheme.{0}) : Bool → Scheme.{0}
  | true => T₁
  | false => T₂

/-- Two morphisms to `X`, indexed by `Bool`. -/
private def boolHom {X T₁ T₂ : Scheme.{0}} (ι₁ : T₁ ⟶ X) (ι₂ : T₂ ⟶ X) :
    ∀ b, boolScheme T₁ T₂ b ⟶ X
  | true => ι₁
  | false => ι₂

/-- Two `ℚ`-divisors, indexed by `Bool`. -/
private def boolDiv {T₁ T₂ : Scheme.{0}} (BT₁ : QDivisor T₁) (BT₂ : QDivisor T₂) :
    ∀ b, QDivisor (boolScheme T₁ T₂ b)
  | true => BT₁
  | false => BT₂

/-- **The adjunction boundary of a stratum is unique.** Two adjunction pairs `(T₁, B_{T₁})`,
`(T₂, B_{T₂})` of a projective dlt pair `(X, B)` with the same generic point have equal
coefficients along prime divisors with the same valuation of `K(X)`: apply the stabilization of
divisors on strata (`exists_forall_ge_isStratumAdjunctionPair_coeff_eq`) to the constant sequence
of identity flips of `(X, B)` (`isFlipOf_id`) and the chain alternating between the two pairs. -/
private theorem coeff_eq_of_isStratumAdjunctionPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B) {d : ℕ}
    {T₁ T₂ : Scheme.{0}} [IsIntegral T₁] [IsLocallyNoetherian T₁] [IsNormal T₁]
    [IsIntegral T₂] [IsLocallyNoetherian T₂] [IsNormal T₂]
    {ι₁ : T₁ ⟶ X} {ι₂ : T₂ ⟶ X} {BT₁ : QDivisor T₁} {BT₂ : QDivisor T₂}
    (h₁ : IsStratumAdjunctionPair sX B ι₁ BT₁) (h₂ : IsStratumAdjunctionPair sX B ι₂ BT₂)
    (hd₁ : topologicalKrullDim T₁ ≤ d) (hd₂ : topologicalKrullDim T₂ ≤ d)
    (hcorr : (ι₁ ≫ 𝟙 X).base (genericPoint T₁) = (ι₂ ≫ 𝟙 X).base (genericPoint T₂))
    (P₁ : MMP.Mori.PrimeDivisor T₁) (P₂ : MMP.Mori.PrimeDivisor T₂)
    (hv : (DivisorOver.ofPrimeDivisor ℂ h₁.some.isNormalVariety P₁).valuation.comap
        ((ι₁ ≫ 𝟙 X).stalkMap (genericPoint T₁)).hom =
      (DivisorOver.ofPrimeDivisor ℂ h₂.some.isNormalVariety P₂).valuation.comap
        ((X.presheaf.stalkCongr (.of_eq hcorr)).hom ≫
          (ι₂ ≫ 𝟙 X).stalkMap (genericPoint T₂)).hom) :
    BT₁.coeff P₁ = BT₂.coeff P₂ := by
  obtain ⟨-, n, K, hK, hKB⟩ := hB.1.1
  have hXn := hB.1.1.1
  have : IsSeparated sX := hXn.1.toIsSeparated
  have : IsSeparated (X ↘ Limits.terminal Scheme) := by
    rw [show (X ↘ Limits.terminal Scheme) = sX ≫ Limits.terminal.from (Spec (.of ℂ)) from
      Subsingleton.elim _ _]
    infer_instance
  -- the alternating chain, as functions of the parity
  have iI : ∀ b, IsIntegral (boolScheme T₁ T₂ b) := fun b => by cases b <;> assumption
  have iN : ∀ b, IsLocallyNoetherian (boolScheme T₁ T₂ b) := fun b => by
    cases b <;> assumption
  have iNo : ∀ b, IsNormal (boolScheme T₁ T₂ b) := fun b => by cases b <;> assumption
  have hSb : ∀ b, IsStratumAdjunctionPair sX B (boolHom ι₁ ι₂ b) (boolDiv BT₁ BT₂ b) :=
    fun b => by cases b <;> assumption
  have hdb : ∀ b, topologicalKrullDim ↥(boolScheme T₁ T₂ b) ≤ d := fun b => by
    cases b <;> assumption
  have hcb : ∀ b, (boolHom ι₁ ι₂ b ≫ 𝟙 X).base (genericPoint (boolScheme T₁ T₂ b)) =
      (boolHom ι₁ ι₂ (!b) ≫ 𝟙 X).base (genericPoint (boolScheme T₁ T₂ (!b))) := fun b => by
    cases b
    · exact hcorr.symm
    · exact hcorr
  have hid : ∀ {T : Set X}, Disjoint T (MMP.Mori.exceptionalSet (𝟙 X) : Set X) := fun {T} =>
    Set.disjoint_right.mpr fun _ hx _ => hx (MMP.Mori.le_biregularLocus
      ((MMP.Mori.isBiregular_top_iff (𝟙 X)).mpr inferInstance) trivial)
  haveI : ∀ i, IsIntegral (boolScheme T₁ T₂ (alt i)) := fun i => iI _
  haveI : ∀ i, IsLocallyNoetherian (boolScheme T₁ T₂ (alt i)) := fun i => iN _
  haveI : ∀ i, IsNormal (boolScheme T₁ T₂ (alt i)) := fun i => iNo _
  obtain ⟨N, hN⟩ := exists_forall_ge_isStratumAdjunctionPair_coeff_eq (k := ℂ)
    (X := fun _ => X) (Z := fun _ => X) (sX := fun _ => sX) (sZ := fun _ => sX)
    (f := fun _ => 𝟙 X) (fp := fun _ => 𝟙 X) (n := n) (K := fun _ => K) (B := fun _ => B)
    (fun _ => hX) (fun _ => hB) (fun _ => hK) (fun _ => isFlipOf_id hX hXn hKB)
    (fun _ => (flipTransform_id B).symm) (d := d)
    (fun _ _ _ _ => hid) (fun _ _ _ _ => hid)
    (S := fun i => boolScheme T₁ T₂ (alt i)) (ι := fun i => boolHom ι₁ ι₂ (alt i))
    (BS := fun i => boolDiv BT₁ BT₂ (alt i))
    (fun i => hSb _) (fun i => hdb _) (fun i => hcb (alt i))
  have key2 : ∀ b : Bool, b = true →
      (∀ (P : MMP.Mori.PrimeDivisor (boolScheme T₁ T₂ b))
        (P' : MMP.Mori.PrimeDivisor (boolScheme T₁ T₂ (!b))),
        (DivisorOver.ofPrimeDivisor ℂ (hSb b).some.isNormalVariety P).valuation.comap
            ((boolHom ι₁ ι₂ b ≫ 𝟙 X).stalkMap (genericPoint (boolScheme T₁ T₂ b))).hom =
          (DivisorOver.ofPrimeDivisor ℂ (hSb (!b)).some.isNormalVariety P').valuation.comap
            ((X.presheaf.stalkCongr (.of_eq (hcb b))).hom ≫
              (boolHom ι₁ ι₂ (!b) ≫ 𝟙 X).stalkMap
                (genericPoint (boolScheme T₁ T₂ (!b)))).hom →
        (boolDiv BT₁ BT₂ b).coeff P = (boolDiv BT₁ BT₂ (!b)).coeff P') →
      BT₁.coeff P₁ = BT₂.coeff P₂ := by
    rintro b rfl h
    exact h P₁ P₂ hv
  have key : ∀ i ≥ N, alt i = true → BT₁.coeff P₁ = BT₂.coeff P₂ :=
    fun i hi hti => key2 (alt i) hti (hN i hi).2
  cases h : alt N
  · exact key (N + 1) (Nat.le_succ N) (by simp [alt, h])
  · exact key N le_rfl h

/-- The valuation of a prime divisor regarded as a divisor over its own scheme. -/
private theorem valuation_ofPrimeDivisor {T : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] {sT : T ⟶ Spec (.of ℂ)} (hT : IsNormalVariety ℂ sT) (P : MMP.Mori.PrimeDivisor T) :
    (DivisorOver.ofPrimeDivisor ℂ hT P).valuation = P.divisorialValuation :=
  Valuation.ext fun z => by
    change P.divisorialValuation (functionFieldMap (𝟙 T) z) = _
    rw [functionFieldMap_id_apply]

/-- **Two adjunction pairs on the same stratum are isomorphic as pairs**: their sources differ by
an isomorphism `e` over `X` carrying one adjunction boundary to the other. -/
private theorem exists_iso_transformDivisor_eq_of_range_eq {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {B : QDivisor X}
    (hB : MMP.Intersection.IsDltPair sX B) {d : ℕ}
    {T₁ T₂ : Scheme.{0}} [IsIntegral T₁] [IsLocallyNoetherian T₁] [IsNormal T₁]
    [IsIntegral T₂] [IsLocallyNoetherian T₂] [IsNormal T₂]
    {ι₁ : T₁ ⟶ X} {ι₂ : T₂ ⟶ X} {BT₁ : QDivisor T₁} {BT₂ : QDivisor T₂}
    (h₁ : IsStratumAdjunctionPair sX B ι₁ BT₁) (h₂ : IsStratumAdjunctionPair sX B ι₂ BT₂)
    (hd₁ : topologicalKrullDim T₁ ≤ d) (hd₂ : topologicalKrullDim T₂ ≤ d)
    (hr : Set.range ι₁.base = Set.range ι₂.base) :
    ∃ e : T₁ ≅ T₂, e.hom ≫ ι₂ = ι₁ ∧
      MMP.Mori.RationalMap.transformDivisor (X := T₁) e.hom.toRationalMap BT₁ = BT₂ := by
  have := h₁.some.isClosedImmersion
  have := h₂.some.isClosedImmersion
  have hn₂ := h₂.some.isNormalVariety
  have : IsSeparated (ι₂ ≫ sX) := hn₂.1.toIsSeparated
  have : IsSeparated (T₂ ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := ι₂ ≫ sX)
  obtain ⟨e, he⟩ := exists_iso_of_range_eq ι₁ ι₂ hr
  refine ⟨e, he, ?_⟩
  subst he
  ext Q
  have hV : e.inv Q.genericPoint ∈ biregularLocus e.inv := by
    rw [top_le_iff.mp (le_biregularLocus (f := e.inv) (by change IsIso _; infer_instance))]
    trivial
  have hcoh : Order.coheight (e.inv Q.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus e.inv hV, Q.coheight_genericPoint]
  set P : MMP.Mori.PrimeDivisor T₁ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hP : e.hom P.genericPoint = Q.genericPoint := by
    have hPg : P.genericPoint = e.inv Q.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
    rw [hPg, ← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have htr : MMP.Mori.RationalMap.transformPrimeDivisor (X := T₁) e.hom.toRationalMap P = some Q :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e.hom P Q).mpr hP
  have huniq : ∀ P', MMP.Mori.RationalMap.transformPrimeDivisor (X := T₁) e.hom.toRationalMap P' =
      some Q → P' = P := by
    intro P' hP'
    have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e.hom P' Q).mp hP'
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have hinj : Function.Injective e.hom.base := by
      intro a b hab
      have := congrArg e.inv.base hab
      simpa [← Scheme.Hom.comp_apply] using this
    exact hinj (h1.trans hP.symm)
  rw [DivisorWithCoeffs.coeff_apply, MMP.Mori.RationalMap.transformDivisor,
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq htr huniq]
  have hcorr : ((e.hom ≫ ι₂) ≫ 𝟙 X).base (genericPoint T₁) =
      (ι₂ ≫ 𝟙 X).base (genericPoint T₂) := by
    rw [Category.comp_id, Category.comp_id, Scheme.Hom.comp_apply,
      map_genericPoint_of_isDominant e.hom]
  refine coeff_eq_of_isStratumAdjunctionPair hX hB h₁ h₂ hd₁ hd₂ hcorr P Q ?_
  rw [valuation_ofPrimeDivisor, valuation_ofPrimeDivisor]
  exact divisorialValuation_comap_stalkMap_eq_of_isIso e.hom (ι₂ ≫ 𝟙 X) _
    (by rw [Category.assoc]) hcorr P Q hP

end AdjunctionUniqueness

/-! ### Corresponding strata along a step -/

section CorrespondingStrata

variable {X X' Z : Scheme.{0}}

/-- A boundary stratum is closed: it is a maximal irreducible subset of a closed set. -/
private theorem isClosed_of_isDltStratum [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} {T : Set X} (hT : IsDltStratum sX B T) :
    IsClosed T := by
  obtain ⟨-, J, -, -, -, hmax⟩ := hT
  have hC : IsClosed (⋂ P ∈ J, (P.support : Set X)) := isClosed_biInter fun P _ => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  exact closure_subset_iff_isClosed.mp
    (hmax.2 ⟨hmax.1.1.closure, closure_minimal hmax.1.2 hC⟩ subset_closure)

/-- A boundary stratum is irreducible. -/
private theorem isIrreducible_of_isDltStratum [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} {T : Set X} (hT : IsDltStratum sX B T) :
    IsIrreducible T :=
  hT.2.choose_spec.2.2.2.1.1

/-- A boundary stratum is the closure of its generic point. -/
private theorem isGenericPoint_of_isDltStratum [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} {T : Set X}
    (hT : IsDltStratum sX B T) :
    IsGenericPoint (isIrreducible_of_isDltStratum hT).genericPoint T := by
  have h := (isIrreducible_of_isDltStratum hT).isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_isDltStratum hT).closure_eq] at h

/-- Over its biregular locus a morphism is injective. -/
private theorem eq_of_map_eq_of_mem_biregularLocus {f : X ⟶ Z} {x y : X}
    (hx : f x ∈ biregularLocus f) (h : f x = f y) : x = y := by
  have hy : f y ∈ biregularLocus f := h ▸ hx
  exact ((specializes_of_map_specializes hx hy (Inseparable.of_eq h).specializes).antisymm
    (specializes_of_map_specializes hy hx (Inseparable.of_eq h.symm).specializes)).eq

/-- A point of the biregular locus of `f` is an image under `f`. -/
private theorem exists_map_eq_of_mem_biregularLocus (f : X ⟶ Z) {z : Z}
    (hz : z ∈ biregularLocus f) : ∃ x, f x = z := by
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  let z' : (biregularLocus f).toScheme := ⟨z, hz⟩
  refine ⟨(f ⁻¹ᵁ biregularLocus f).ι (inv (f ∣_ biregularLocus f) z'), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← morphismRestrict_ι, ← Scheme.Hom.comp_apply,
    ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rfl

/-- For an irreducible closed `T` with generic point `η`, `closure (f '' T) = closure {f η}`. -/
private theorem closure_image_eq_closure_singleton {f : X ⟶ Z} {T : Set X} {η : X}
    (hη : IsGenericPoint η T) : closure (f.base '' T) = closure {f η} := by
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨y, hy, rfl⟩
    exact specializes_iff_mem_closure.mp ((hη.specializes hy).map f.base.hom.continuous)
  · exact Set.singleton_subset_iff.mpr ⟨η, hη.mem, rfl⟩

/-- **Strata are determined by their images off the exceptional set.** Two irreducible closed
subsets of `X` not contained in `Ex(f)` whose images under `f` have the same closure are equal. -/
private theorem eq_of_closure_image_eq {f : X ⟶ Z} {T₁ T₂ : Set X} {η₁ η₂ : X}
    (h₁ : IsGenericPoint η₁ T₁) (h₂ : IsGenericPoint η₂ T₂)
    (hn₁ : ¬ T₁ ⊆ (MMP.Mori.exceptionalSet f : Set X))
    (hn₂ : ¬ T₂ ⊆ (MMP.Mori.exceptionalSet f : Set X))
    (h : closure (f.base '' T₁) = closure (f.base '' T₂)) : T₁ = T₂ := by
  have hm : ∀ {T : Set X} {η : X}, IsGenericPoint η T → ¬ T ⊆ (MMP.Mori.exceptionalSet f : Set X) →
      f η ∈ biregularLocus f := fun {T η} hη hn => by
    by_contra hc
    refine hn ?_
    rw [← hη.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (MMP.Mori.mem_exceptionalSet.mpr hc))
      (MMP.Mori.isClosed_exceptionalSet f)
  rw [closure_image_eq_closure_singleton h₁, closure_image_eq_closure_singleton h₂] at h
  have hfη : f η₁ = f η₂ :=
    (isGenericPoint_closure.eq (h ▸ isGenericPoint_closure) : _)
  rw [← h₁.def, ← h₂.def, eq_of_map_eq_of_mem_biregularLocus (hm h₁ hn₁) hfη]

/-- An irreducible closed subset not contained in `Ex(f)` has its generic point over the biregular
locus of `f`. -/
private theorem map_mem_biregularLocus_of_not_subset {f : X ⟶ Z} {T : Set X} {η : X}
    (hη : IsGenericPoint η T) (hn : ¬ T ⊆ (MMP.Mori.exceptionalSet f : Set X)) :
    f η ∈ biregularLocus f := by
  by_contra hc
  refine hn ?_
  rw [← hη.def]
  exact closure_minimal (Set.singleton_subset_iff.mpr (MMP.Mori.mem_exceptionalSet.mpr hc))
    (MMP.Mori.isClosed_exceptionalSet f)

/-- **Coefficients of a strict transform along a flip.** For `f` small, the coefficient of
`(f⁺)⁻¹_* f_* D` along a prime divisor `P'` lying over the biregular locus of `f⁺` is the
coefficient of `D` along the prime divisor `P` with the same image. -/
private theorem flipTransform_apply_of_map_genericPoint_eq [IsReduced X] [IsReduced X']
    [IsSeparated (Z ↘ ⊤_ Scheme)] {f : X ⟶ Z}
    {fp : X' ⟶ Z} (hsmall : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet f)) {R : Type}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (h : f P.genericPoint = fp P'.genericPoint)
    (hV : fp P'.genericPoint ∈ biregularLocus fp) : flipTransform f fp D P' = D P := by
  have hcoh : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f
      (Oai4C1.map_genericPoint_mem_biregularLocus hsmall P), P.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hQ : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm
  have e : flipTransform f fp D = DivisorWithCoeffs.mapPrimeDivisors
      (fun E => (MMP.Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap E).bind
        (inverseTransformPrimeDivisor fp)) D :=
    (mapPrimeDivisors_bind _ _ D).symm
  rw [e]
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq ?_ ?_ D
  · rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hQ,
      Option.bind_some]
    exact inverseTransformPrimeDivisor_eq_some_of_map_genericPoint (h.symm.trans hQ) hV
  · intro E hE
    obtain ⟨Q', hQ'1, hQ'2⟩ := Option.bind_eq_some_iff.mp hE
    have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f E Q').mp hQ'1
    have h2 := (MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' fp Q' P').mp hQ'2
    exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      eq_of_map_eq_of_mem_biregularLocus (Oai4C1.map_genericPoint_mem_biregularLocus hsmall E)
        (h1.trans (h2.2.symm.trans h.symm))

/-- **Strata of the flipped model come from strata of the model.** Let `f` be small, `f⁺` an
isomorphism wherever `f` is (`V_{f⁺} ⊆ V_f`), and `B' = (f⁺)⁻¹_* f_* B`. A boundary stratum `T'`
of `(X', B')` not contained in `Ex(f⁺)` has a boundary stratum `T` of `(X, B)` with the same
image: over `V_{f⁺}` the two models are isomorphic, and boundaries and strata correspond. -/
private theorem exists_isDltStratum_of_isDltStratum_flipTransform [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsSeparated (Z ↘ ⊤_ Scheme)] {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {fp : X' ⟶ Z} {B : QDivisor X}
    (hsmall : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet f))
    (hV : biregularLocus fp ≤ biregularLocus f) (hB : MMP.Intersection.IsDltPair sX B)
    {T' : Set X'} (hT' : IsDltStratum sX' (flipTransform f fp B) T')
    (hn : ¬ T' ⊆ (MMP.Mori.exceptionalSet fp : Set X')) :
    ∃ T : Set X, IsDltStratum sX B T ∧ closure (f.base '' T) = closure (fp.base '' T') := by
  classical
  have hη' := isGenericPoint_of_isDltStratum hT'
  set η' := (isIrreducible_of_isDltStratum hT').genericPoint
  have hη'V : fp η' ∈ biregularLocus fp := map_mem_biregularLocus_of_not_subset hη' hn
  obtain ⟨x, hx⟩ := exists_map_eq_of_mem_biregularLocus f (hV hη'V)
  have hxV : f x ∈ biregularLocus f := hx ▸ hV hη'V
  obtain ⟨J', hJ'ne, hJ'1, -, hmax'⟩ := hT'.2
  -- the prime divisors of `X` over the components of `J'`
  have hP : ∀ P' : J', ∃ P : MMP.Mori.PrimeDivisor X,
      f P.genericPoint = fp (P' : MMP.Mori.PrimeDivisor X').genericPoint ∧
        fp (P' : MMP.Mori.PrimeDivisor X').genericPoint ∈ biregularLocus fp := by
    intro P'
    have hmem : η' ∈ ((P' : MMP.Mori.PrimeDivisor X').support : Set X') :=
      Set.mem_iInter₂.mp (hmax'.1.2 hη'.mem) _ P'.2
    have hsp : (P' : MMP.Mori.PrimeDivisor X').genericPoint ⤳ η' := by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem
      exact specializes_iff_mem_closure.mpr hmem
    have hPV : fp (P' : MMP.Mori.PrimeDivisor X').genericPoint ∈ biregularLocus fp :=
      (hsp.map fp.base.hom.continuous).mem_open (biregularLocus fp).2 hη'V
    obtain ⟨p, hp⟩ := exists_map_eq_of_mem_biregularLocus f (hV hPV)
    have hcoh : Order.coheight p = 1 := by
      rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (hp ▸ hV hPV), hp,
        MMP.Positivity.coheight_map_of_mem_biregularLocus fp hPV,
        (P' : MMP.Mori.PrimeDivisor X').coheight_genericPoint]
    refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_, hPV⟩
    exact (congrArg (fun z => f z)
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh)).trans hp
  choose φ hφ hφV using hP
  set J := J'.attach.image φ
  have hfV : ∀ P' : J', f (φ P').genericPoint ∈ biregularLocus f := fun P' =>
    (hφ P').symm ▸ hV (hφV P')
  -- specializations of points of `X` over `V_{f⁺}` are read off in `Z`
  have hJx : ∀ P ∈ J, x ∈ (P.support : Set X) := by
    intro P hPJ
    obtain ⟨P', -, rfl⟩ := Finset.mem_image.mp hPJ
    have hmem : η' ∈ ((P' : MMP.Mori.PrimeDivisor X').support : Set X') :=
      Set.mem_iInter₂.mp (hmax'.1.2 hη'.mem) _ P'.2
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem ⊢
    have hsp := (specializes_iff_mem_closure.mpr hmem).map fp.base.hom.continuous
    rw [← hφ P', ← hx] at hsp
    exact specializes_iff_mem_closure.mp (specializes_of_map_specializes (hfV P') hxV hsp)
  have hcl : IsClosed (⋂ P ∈ J, (P.support : Set X)) := isClosed_biInter fun P _ => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  refine ⟨closure {x}, ⟨hB, J, hJ'ne.attach.image φ, ?_, ⟨x, Set.mem_iInter₂.mpr hJx⟩,
    ⟨isIrreducible_singleton.closure, closure_minimal
      (Set.singleton_subset_iff.mpr (Set.mem_iInter₂.mpr hJx)) hcl⟩, ?_⟩, ?_⟩
  · intro P hPJ
    obtain ⟨P', -, rfl⟩ := Finset.mem_image.mp hPJ
    have h1 := hJ'1 P' P'.2
    rw [DivisorWithCoeffs.coeff_apply, flipTransform_apply_of_map_genericPoint_eq hsmall B
      (hφ P') (hφV P')] at h1
    rwa [DivisorWithCoeffs.coeff_apply]
  · intro Y hY hxY
    have hyY := hY.1.isGenericPoint_genericPoint_closure
    set y := hY.1.genericPoint
    have hyx : y ⤳ x := hyY.specializes (subset_closure (hxY (subset_closure rfl)))
    have hfy : f y ∈ biregularLocus fp :=
      (hyx.map f.base.hom.continuous).mem_open (biregularLocus fp).2 (hx ▸ hη'V)
    obtain ⟨y', hy'⟩ := exists_map_eq_of_mem_biregularLocus fp hfy
    have hy'V : fp y' ∈ biregularLocus fp := hy' ▸ hfy
    have hy'J : y' ∈ ⋂ P' ∈ J', ((P' : MMP.Mori.PrimeDivisor X').support : Set X') := by
      refine Set.mem_iInter₂.mpr fun P' hP' => ?_
      have hyP : y ∈ ((φ ⟨P', hP'⟩).support : Set X) :=
        closure_minimal (hY.2.trans (Set.biInter_subset_of_mem
          (Finset.mem_image_of_mem φ (Finset.mem_attach _ ⟨P', hP'⟩))))
          (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)
          hyY.mem
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hyP ⊢
      have hsp := (specializes_iff_mem_closure.mpr hyP).map f.base.hom.continuous
      rw [hφ ⟨P', hP'⟩, ← hy'] at hsp
      have h3 : (P' : MMP.Mori.PrimeDivisor X').genericPoint ⤳ y' :=
        specializes_of_map_specializes (hφV ⟨P', hP'⟩) hy'V hsp
      exact specializes_iff_mem_closure.mp h3
    have hy'η : y' ⤳ η' := by
      have hsp := hyx.map f.base.hom.continuous
      rw [← hy', hx] at hsp
      exact specializes_of_map_specializes hy'V hη'V hsp
    have hT'y : T' ⊆ closure {y'} := by
      rw [← hη'.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr
        (specializes_iff_mem_closure.mp hy'η)) isClosed_closure
    have hle := hmax'.2 ⟨isIrreducible_singleton.closure, closure_minimal
      (Set.singleton_subset_iff.mpr hy'J) (isClosed_biInter fun P _ => by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure)⟩ hT'y
    have hηy : η' ⤳ y' := hη'.specializes (hle (subset_closure rfl))
    have hsp := hηy.map fp.base.hom.continuous
    rw [← hx, hy'] at hsp
    have hxy : x ⤳ y := specializes_of_map_specializes hxV (hy'.symm ▸ hV hy'V) hsp
    exact subset_closure.trans (hyY.def ▸ closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hxy)) isClosed_closure)
  · rw [closure_image_eq_closure_singleton isGenericPoint_closure,
      closure_image_eq_closure_singleton hη', hx]

/-- Cancellation in `WithBot ℕ∞` against a natural number. -/
private theorem withBot_eq_of_add_eq_add {a b : WithBot ℕ∞} {c : ℕ∞} {n : ℕ}
    (ha : a + c = n) (hb : b + c = n) : a = b := by
  induction a using WithBot.recBotCoe with
  | bot => simp at ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at hb
    | coe b =>
      have ha' : a + c = n := by exact_mod_cast ha
      have hb' : b + c = n := by exact_mod_cast hb
      induction c using ENat.recTopCoe with
      | top => simp at ha'
      | coe c =>
        induction a using ENat.recTopCoe with
        | top => simp at ha'
        | coe a =>
          induction b using ENat.recTopCoe with
          | top => simp at hb'
          | coe b =>
            have h1 : a + c = n := by exact_mod_cast ha'
            have h2 : b + c = n := by exact_mod_cast hb'
            have : a = b := by omega
            rw [this]

/-- **Corresponding strata have the same dimension.** Two irreducible closed sets on varieties of
the same dimension, with generic points over the biregular loci and images with the same
closure, have the same dimension: their generic points have the same codimension. -/
private theorem topologicalKrullDim_eq_of_closure_image_eq {sX : X ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} [IsIntegral X] [IsIntegral X'] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] {n : ℕ} (hX : topologicalKrullDim X = n)
    (hX' : topologicalKrullDim X' = n) {f : X ⟶ Z} {fp : X' ⟶ Z} {T : Set X} {T' : Set X'}
    {η : X} {η' : X'} (hη : IsGenericPoint η T) (hη' : IsGenericPoint η' T')
    (hm : f η ∈ biregularLocus f) (hm' : fp η' ∈ biregularLocus fp)
    (h : closure (f.base '' T) = closure (fp.base '' T')) :
    topologicalKrullDim T = topologicalKrullDim T' := by
  rw [closure_image_eq_closure_singleton hη, closure_image_eq_closure_singleton hη'] at h
  have hfη : f η = fp η' := (isGenericPoint_closure.eq (h ▸ isGenericPoint_closure) : _)
  have h1 := topologicalKrullDim_closure_singleton_add_coheight sX η
  have h2 := topologicalKrullDim_closure_singleton_add_coheight sX' η'
  rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f hm, hfη,
    MMP.Positivity.coheight_map_of_mem_biregularLocus fp hm', hX, hη.def] at h1
  rw [hX', hη'.def] at h2
  exact withBot_eq_of_add_eq_add h1 h2

/-- **The strict transform along a flip is an involution**: `f⁻¹_* f⁺_* (f⁺)⁻¹_* f_* D = D` for
small `f`, `f⁺` with `f⁺` an isomorphism over `V_f`. -/
private theorem flipTransform_flipTransform [IsReduced X] [IsReduced X']
    [IsSeparated (Z ↘ ⊤_ Scheme)] {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hs : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet f))
    (hs' : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet fp))
    (hle : biregularLocus f ≤ biregularLocus fp) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform fp f (flipTransform f fp D) = D := by
  ext P
  have hPV := Oai4C1.map_genericPoint_mem_biregularLocus hs P
  obtain ⟨p, hp⟩ := exists_map_eq_of_mem_biregularLocus fp (hle hPV)
  have hcoh : Order.coheight p = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hp ▸ hle hPV), hp,
      MMP.Positivity.coheight_map_of_mem_biregularLocus f hPV, P.coheight_genericPoint]
  set P' : MMP.Mori.PrimeDivisor X' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hP' : fp P'.genericPoint = f P.genericPoint :=
    (congrArg (fun z => fp z)
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh)).trans hp
  rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
    flipTransform_apply_of_map_genericPoint_eq hs' _ hP' hPV,
    flipTransform_apply_of_map_genericPoint_eq hs D hP'.symm (hP' ▸ hle hPV)]

/-- **The contraction of a flip is an isomorphism wherever the flip is** (`V_{f⁺} ⊆ V_f`): the
reversed diagram `X⁺ → Z ← X` is a flip with respect to `-(f⁺)⁻¹_* f_* D`, and a flip is an
isomorphism over the biregular locus of its contraction. -/
private theorem biregularLocus_flip_le_of_isFlip {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] {D : QDivisor X}
    {f : X ⟶ Z} {fp : X' ⟶ Z} {g : X.RationalMap X'}
    (hflip : IsFlip ℂ sX sZ sX' (QDivisor.toRDivisor D) f fp g) :
    biregularLocus fp ≤ biregularLocus f := by
  have hX := hflip.isNormalVariety_source
  have hX' := hflip.isNormalVariety_flip
  have hZ := hflip.isNormalVariety_target
  haveI : IsIntegral X := hX.1.toIsIntegral
  haveI : IsIntegral X' := hX'.1.toIsIntegral
  haveI : IsProper f := hflip.isContraction.isProper
  haveI : IsProper fp := hflip.isProper
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  haveI : IsSeparated sX := hX.1.toIsSeparated
  haveI : IsSeparated (X ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sX)
  haveI : IsSeparated sX' := hX'.1.toIsSeparated
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sX')
  have hD : D.IsQCartier :=
    MMP.Flips.QDivisor.isQCartier_of_isCartierCombination hflip.isCartierCombination
  have h2 := two_le_closedsCodimension_exceptionalSet_of_isSmall hflip.isSmall_source
  have h2' := two_le_closedsCodimension_exceptionalSet_of_isSmall hflip.isSmall
  have hle : biregularLocus f ≤ biregularLocus fp := le_biregularLocus
    (hflip.isIso_morphismRestrict_of_disjoint_image_exceptionalSet hD _
      (image_flipsExceptionalSet_disjoint_biregularLocus f))
  -- the inverse birational map over `V_f`
  set V := biregularLocus f
  haveI : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  haveI : IsIso (fp ∣_ V) := hflip.isIso_morphismRestrict_of_disjoint_image_exceptionalSet hD _
    (image_flipsExceptionalSet_disjoint_biregularLocus f)
  have hηX : f (genericPoint X) ∈ V := by
    by_contra hc
    have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2 _
      (MMP.Mori.mem_exceptionalSet.mpr hc)
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at this
    exact absurd this (by decide)
  obtain ⟨x', hx'⟩ := exists_map_eq_of_mem_biregularLocus fp (hle hηX)
  let e : X'.PartialIso X :=
    { source := fp ⁻¹ᵁ V
      dense_source := (fp ⁻¹ᵁ V).isOpen.dense ⟨x', show fp x' ∈ V from hx' ▸ hηX⟩
      target := f ⁻¹ᵁ V
      dense_target := (f ⁻¹ᵁ V).isOpen.dense ⟨_, hηX⟩
      iso := asIso (fp ∣_ V) ≪≫ (asIso (f ∣_ V)).symm }
  have key : e.iso.hom ≫ e.target.ι ≫ f = e.source.ι ≫ fp := by
    change ((fp ∣_ V) ≫ inv (f ∣_ V)) ≫ (f ⁻¹ᵁ V).ι ≫ f = (fp ⁻¹ᵁ V).ι ≫ fp
    rw [← morphismRestrict_ι, ← morphismRestrict_ι, Category.assoc, IsIso.inv_hom_id_assoc]
  have hover : MMP.Flips.RationalMap.IsOver fp f e.toRationalMap := by
    rw [MMP.Flips.RationalMap.IsOver, Scheme.PartialIso.toRationalMap,
      ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
    refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
    change X'.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ f =
      X'.homOfLE (le_top : e.source ≤ ⊤) ≫ X'.topIso.hom ≫ fp
    rw [Category.assoc, key]
    simp
  have hmod : IsModificationOf fp f e.toRationalMap :=
    ⟨MMP.Mori.RationalMap.isBirational_toRationalMap e, hover⟩
  have htr : MMP.Mori.RationalMap.transformDivisor g (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (flipTransform f fp D) := by
    rw [transformDivisor_eq_flipTransform_of_small h2 h2' hflip.isModificationOf]
    exact flipTransform_mapCoeffsAddMonoidHom _ _ _ D
  have htr' : MMP.Mori.RationalMap.transformDivisor e.toRationalMap
      (QDivisor.toRDivisor (-flipTransform f fp D)) = -QDivisor.toRDivisor D := by
    rw [transformDivisor_eq_flipTransform_of_small h2' h2 hmod, map_neg, map_neg]
    congr 1
    have e1 := flipTransform_mapCoeffsAddMonoidHom fp f (Rat.castHom ℝ).toAddMonoidHom
      (flipTransform f fp D)
    rw [flipTransform_flipTransform h2 h2' hle] at e1
    exact e1
  have hrev : IsFlip ℂ sX' sZ sX (QDivisor.toRDivisor (-flipTransform f fp D)) fp f
      e.toRationalMap :=
    { isNormalVariety_source := hX'
      isNormalVariety_target := hZ
      isNormalVariety_flip := hX
      isContraction := hflip.isSmall.toIsBirationalContraction.toIsContraction
      isCartierCombination := by
        rw [map_neg, ← htr]; exact isCartierCombination_neg hflip.isCartierCombination_transform
      isRelativelyAntiAmple := by
        change IsRelativelyAmple fp (-_)
        rw [map_neg, neg_neg, ← htr]; exact hflip.isRelativelyAmple_transform
      isProper := inferInstance
      isModificationOf := hmod
      isMorphismInCodimOne :=
        MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX' fp f _ hover
      isSmall := hflip.isSmall_source
      isCartierCombination_transform := by
        rw [htr']; exact isCartierCombination_neg hflip.isCartierCombination
      isRelativelyAmple_transform := by rw [htr']; exact hflip.isRelativelyAntiAmple
      isSmall_source := hflip.isSmall }
  have hD' : QDivisor.IsQCartier (-flipTransform f fp D) :=
    MMP.Flips.QDivisor.isQCartier_of_isCartierCombination hrev.isCartierCombination
  exact le_biregularLocus (hrev.isIso_morphismRestrict_of_disjoint_image_exceptionalSet hD' _
    (image_flipsExceptionalSet_disjoint_biregularLocus fp))

/-- A closed immersion is a homeomorphism onto its image, so the source and the image have the
same dimension. -/
private theorem topologicalKrullDim_eq_range {T Y : Scheme.{0}} (ι : T ⟶ Y)
    [IsClosedImmersion ι] : topologicalKrullDim T = topologicalKrullDim (Set.range ι.base) :=
  IsHomeomorph.topologicalKrullDim_eq _ ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph

/-- The image of the generic point under a closed immersion is the generic point of the image. -/
private theorem isGenericPoint_range {T Y : Scheme.{0}} [IsIntegral T] (ι : T ⟶ Y)
    [IsClosedImmersion ι] : IsGenericPoint (ι (genericPoint T)) (Set.range ι.base) := by
  have h := (genericPoint_spec T).image ι.base.hom.continuous
  rwa [Set.image_univ, ι.isClosedEmbedding.isClosed_range.closure_eq] at h

end CorrespondingStrata

/-! ### The adjoints of adjunction pairs -/

section AdjointSigns

/-- Pull-backs of `ℚ`-divisors commute with negation. -/
private theorem qDivisor_isPullback_neg {X Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} {B : QDivisor Y} {B' : QDivisor X}
    {hB : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ B.supp}
    (h : B.IsPullback f hB B')
    (hBn : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ (-B).supp) :
    (-B).IsPullback f hBn (-B') := by
  intro m hm D hD hDc
  have hD' : Divisor.toQDivisor (-D) = (m : ℤ) • B := by
    rw [map_neg, hD, smul_neg, neg_neg]
  obtain ⟨D'', hD''eq, hpb⟩ := h m hm (-D) hD' hDc.neg
  refine ⟨-D'', by rw [map_neg, hD''eq, smul_neg], ?_⟩
  have h2 := hpb.zsmul hDc.neg (-1) (by
    intro Z hZ
    rw [show ((-1 : ℤ) • -D) = D by simp] at hZ
    exact hBn Z (by
      rwa [QDivisor.supp_eq_of_toQDivisor_eq (by exact_mod_cast hm.ne') hD] at hZ))
  convert h2 using 1 <;> simp

/-- **The adjoint of an adjunction pair has the sign of the ambient adjoint.** If
`ε (K_X + B)` (`ε = ±1`) has an `f`-ample Cartier multiple, then for every adjunction pair
`(S, B_S)` of positive dimension there is a canonical divisor `K_S` of `S` with
`ε (K_S + B_S)` having an `ι ≫ f`-ample Cartier multiple. -/
private theorem StratumAdjunctionData.exists_adjoint_hasRelativelyAmpleMultiple
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of ℂ)} {N : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX N)
    {B : QDivisor X} {f : X ⟶ Y} [QuasiCompact f] (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hamp : (ε • (Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple f) :
    ∀ {S : Scheme.{0}} {ι : S ⟶ X} {BS : QDivisor S} (_ : StratumAdjunctionData sX B ι BS)
      [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S] (e : ℕ),
      topologicalKrullDim S = e → 1 ≤ e →
      ∃ KS : Divisor S, KS.IsCanonicalDivisor (ι ≫ sX) e ∧
        (ε • (Divisor.toQDivisor KS + BS)).HasRelativelyAmpleMultiple (ι ≫ f) := by
  intro S ι BS F
  induction F with
  | refl h =>
    intro _ _ _ _ e he _
    have hNe : e = N := by rw [hK.1] at he; exact_mod_cast he.symm
    subst hNe
    exact ⟨K, by rw [Category.id_comp]; exact hK, by rw [Category.id_comp]; exact hamp⟩
  | @step S T ι BS F j BT h ih =>
    intro _ _ _ _ e he he1
    have hSv := F.isNormalVariety
    haveI : IsIntegral S := hSv.1.toIsIntegral
    haveI : IsNormal S := hSv.2
    haveI : LocallyOfFiniteType (ι ≫ sX) := hSv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)
    haveI : IsClosedImmersion ι := F.isClosedImmersion
    haveI : CompactSpace S := ι.isClosedEmbedding.compactSpace
    obtain ⟨hTv, P, -, hrange, hci, -⟩ := id h
    haveI := hci
    -- `dim S = e + 1`
    have hdimS : topologicalKrullDim S = ((e : ℕ) + 1 : ℕ) := by
      have h1 := topologicalKrullDim_closure_singleton_add_coheight (ι ≫ sX) P.genericPoint
      rw [P.coheight_genericPoint, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure, ← hrange,
        ← topologicalKrullDim_eq_range j, he] at h1
      rw [← h1]
      push_cast
      rfl
    obtain ⟨KS, hKS, hampS⟩ := ih (e + 1) hdimS (by omega)
    obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq he (by omega)
    obtain ⟨σ, hσ0, hσP, -, ρ, hρ, hρ0, -⟩ :=
      MMP.Fourfold.exists_form_of_residue_order (ι ≫ sX) hSv hdimS j hTv P hrange Q
    obtain ⟨ψ, hψ⟩ : Divisor.LinearlyEquivalent (divisorOfForm σ) KS := by
      simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hSv hKS hσ0
    have hdivσ : Divisor.toQDivisor (divisorOfForm σ) + BS =
        (Divisor.toQDivisor KS + BS) + Divisor.toQDivisor (principalDivisor ψ) := by
      rw [← hψ, map_sub]; abel
    have hampσ : (ε • (Divisor.toQDivisor (divisorOfForm σ) + BS)).HasRelativelyAmpleMultiple
        (ι ≫ f) := by
      rcases hε with rfl | rfl
      · rw [one_smul] at hampS ⊢
        rw [hdivσ]
        exact hasRelativelyAmpleMultiple_add_principalDivisor hampS ψ
      · have := hasRelativelyAmpleMultiple_add_principalDivisor hampS ψ⁻¹
        rw [hdivσ]
        convert this using 1
        rw [MMP.Mori.principalDivisor_inv, map_neg]
        simp only [neg_smul, one_smul, neg_add]
    have hq : (Divisor.toQDivisor (divisorOfForm σ) + BS).IsQCartier := by
      obtain ⟨m, hm, L, hL, hLD, -⟩ := hampσ
      refine ⟨(m : ℤ) * ε, mul_ne_zero (by exact_mod_cast hm.ne')
        (by rcases hε with rfl | rfl <;> norm_num), L, by rw [hLD, smul_smul], hL⟩
    obtain ⟨hgen, hpb⟩ := IsAdjunctionStep.isPullback_divisorOfForm_add_of_isPoincareResidue h
      hdimS P hrange σ hσ0 hσP ρ hρ hq
    have hampT : (ε • (Divisor.toQDivisor (divisorOfForm ρ) + BT)).HasRelativelyAmpleMultiple
        (j ≫ ι ≫ f) := by
      rcases hε with rfl | rfl
      · rw [one_smul] at hampσ ⊢
        exact hasRelativelyAmpleMultiple_of_isPullback hpb hampσ
      · rw [neg_one_smul] at hampσ ⊢
        refine hasRelativelyAmpleMultiple_of_isPullback (qDivisor_isPullback_neg hpb ?_) hampσ
        intro Z hZ
        refine hgen Z ?_
        rwa [show -(Divisor.toQDivisor (divisorOfForm σ) + BS) =
            (-1 : ℤ) • (Divisor.toQDivisor (divisorOfForm σ) + BS) from (neg_one_smul ℤ _).symm,
          QDivisor.supp_zsmul (by norm_num)] at hZ
    obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (j ≫ ι ≫ sX) hTv he
    have hKT : (divisorOfForm ρ).IsCanonicalDivisor (j ≫ ι ≫ sX) e :=
      hK₀.of_linearlyEquivalent (by
        simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hTv hK₀ hρ0)
    exact ⟨divisorOfForm ρ, by rw [Category.assoc]; exact hKT, by rw [Category.assoc]; exact hampT⟩

end AdjointSigns

/-! ### Chains of corresponding strata -/

section Chains

/-- **Eventual properties along finitely many chains.** Let `D j ⊆ A j` be sets and `R j` a
relation from `A j` to `A (j + 1)` which is a functional, everywhere defined correspondence from
`D j` onto `D (j + 1)`, with `D 0` finite. If a property `Q j` of related pairs holds eventually
along every chain `c` (`R j (c j) (c (j + 1))` for all `j`), then it holds eventually for all
related pairs: every element of `D j` lies on one of the finitely many chains issued from `D 0`. -/
private theorem exists_forall_ge_of_chains {A : ℕ → Type*} (D : ∀ j, Set (A j))
    (R : ∀ j, A j → A (j + 1) → Prop) (hD0 : (D 0).Finite)
    (hR : ∀ j a b, R j a b → a ∈ D j ∧ b ∈ D (j + 1))
    (hfwd : ∀ j a, a ∈ D j → ∃ b, R j a b) (hbwd : ∀ j b, b ∈ D (j + 1) → ∃ a, R j a b)
    (hfun : ∀ j a b₁ b₂, R j a b₁ → R j a b₂ → b₁ = b₂)
    (Q : ∀ j, A j → A (j + 1) → Prop)
    (hQ : ∀ c : ∀ j, A j, (∀ j, R j (c j) (c (j + 1))) → ∃ N, ∀ j ≥ N, Q j (c j) (c (j + 1))) :
    ∃ N, ∀ j ≥ N, ∀ a b, R j a b → Q j a b := by
  classical
  -- the chain issued from `a₀ ∈ D 0`
  let g : ∀ j, D j → D (j + 1) := fun j a =>
    ⟨(hfwd j a a.2).choose, (hR _ _ _ (hfwd j a a.2).choose_spec).2⟩
  have hg : ∀ j (a : D j), R j a (g j a) := fun j a => (hfwd j a a.2).choose_spec
  let c : D 0 → ∀ j, D j := fun a₀ j => Nat.rec (motive := fun j => D j) a₀ (fun j x => g j x) j
  have hc : ∀ a₀ j, R j (c a₀ j) (c a₀ (j + 1)) := fun a₀ j => hg j (c a₀ j)
  choose Nf hNf using fun a₀ : D 0 => hQ (fun j => c a₀ j) (hc a₀)
  have : Finite (D 0) := hD0.to_subtype
  have : Fintype (D 0) := Fintype.ofFinite _
  refine ⟨Finset.univ.sup Nf, fun j hj a b hab => ?_⟩
  -- every element of `D j` lies on a chain
  have hall : ∀ j, ∀ a ∈ D j, ∃ a₀ : D 0, (c a₀ j : A j) = a := by
    intro j
    induction j with
    | zero => exact fun a ha => ⟨⟨a, ha⟩, rfl⟩
    | succ j ih =>
      intro a ha
      obtain ⟨a', ha'⟩ := hbwd j a ha
      obtain ⟨a₀, rfl⟩ := ih a' (hR _ _ _ ha').1
      exact ⟨a₀, hfun j _ _ _ (hc a₀ j) ha'⟩
  obtain ⟨a₀, rfl⟩ := hall j a (hR _ _ _ hab).1
  obtain rfl := hfun j _ _ _ hab (hc a₀ j)
  exact hNf a₀ j ((Finset.le_sup (Finset.mem_univ a₀)).trans hj)

end Chains

/-! ### Transforms along isomorphisms -/

section IsoTransforms

variable {T₁ T₂ T₃ : Scheme.{0}}

/-- Along an isomorphism, every prime divisor has a transform, through its generic point. -/
private theorem exists_transformPrimeDivisor_of_isIso [IsReduced T₁]
    [IsSeparated (T₂ ↘ ⊤_ Scheme)] (a : T₁ ⟶ T₂) [IsIso a] (P : MMP.Mori.PrimeDivisor T₁) :
    ∃ Q : MMP.Mori.PrimeDivisor T₂,
      MMP.Mori.RationalMap.transformPrimeDivisor (X := T₁) a.toRationalMap P = some Q ∧
        Q.genericPoint = a P.genericPoint := by
  have hV : a P.genericPoint ∈ biregularLocus a := by
    rw [top_le_iff.mp (le_biregularLocus (f := a) (by change IsIso _; infer_instance))]
    trivial
  have hcoh : Order.coheight (a P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus a hV, P.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh⟩
  exact (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff a P _).mpr
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm

/-- **Transforms along composites of isomorphisms** compose. -/
private theorem transformDivisor_comp_of_isIso [IsReduced T₁] [IsReduced T₂]
    [IsSeparated (T₂ ↘ ⊤_ Scheme)] [IsSeparated (T₃ ↘ ⊤_ Scheme)] (a : T₁ ⟶ T₂) (b : T₂ ⟶ T₃)
    [IsIso a] [IsIso b] {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R T₁) :
    MMP.Mori.RationalMap.transformDivisor (X := T₁) (a ≫ b).toRationalMap D =
      MMP.Mori.RationalMap.transformDivisor (X := T₂) b.toRationalMap
        (MMP.Mori.RationalMap.transformDivisor (X := T₁) a.toRationalMap D) := by
  have hP : ∀ P : MMP.Mori.PrimeDivisor T₁,
      MMP.Mori.RationalMap.transformPrimeDivisor (X := T₁) (a ≫ b).toRationalMap P =
        (MMP.Mori.RationalMap.transformPrimeDivisor (X := T₁) a.toRationalMap P).bind
          (MMP.Mori.RationalMap.transformPrimeDivisor (X := T₂) b.toRationalMap) := by
    intro P
    obtain ⟨Q, hQ, hQη⟩ := exists_transformPrimeDivisor_of_isIso a P
    obtain ⟨Q', hQ', hQ'η⟩ := exists_transformPrimeDivisor_of_isIso b Q
    obtain ⟨Q'', hQ'', hQ''η⟩ := exists_transformPrimeDivisor_of_isIso (a ≫ b) P
    rw [hQ, Option.bind_some, hQ', hQ'']
    congr 1
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change Q''.genericPoint = Q'.genericPoint
    rw [hQ''η, hQ'η, hQη, Scheme.Hom.comp_apply]
  change DivisorWithCoeffs.mapPrimeDivisors _ D =
    DivisorWithCoeffs.mapPrimeDivisors _ (DivisorWithCoeffs.mapPrimeDivisors _ D)
  rw [funext hP]
  exact mapPrimeDivisors_bind _ _ D

/-- Transforming back along the inverse of an isomorphism. -/
private theorem transformDivisor_inv_transformDivisor [IsReduced T₁] [IsReduced T₂]
    [IsSeparated (T₁ ↘ ⊤_ Scheme)] [IsSeparated (T₂ ↘ ⊤_ Scheme)] (e : T₁ ≅ T₂) {R : Type}
    [AddCommMonoid R] (D : DivisorWithCoeffs R T₁) :
    MMP.Mori.RationalMap.transformDivisor (X := T₂) e.inv.toRationalMap
      (MMP.Mori.RationalMap.transformDivisor (X := T₁) e.hom.toRationalMap D) = D := by
  rw [← transformDivisor_comp_of_isIso, e.hom_inv_id, transformDivisor_id]

end IsoTransforms

/-! ### Valuations over a base -/

section ValuationsOver

open scoped WithZero

/-- `stalkCongr` along `a = b` and back is the identity. -/
private theorem stalkCongr_hom_stalkCongr_hom_apply {Z : Scheme.{0}} {a b : Z} (h : a = b)
    (z : Z.presheaf.stalk b) :
    (Z.presheaf.stalkCongr (.of_eq h)).hom ((Z.presheaf.stalkCongr (.of_eq h.symm)).hom z) = z := by
  subst h
  simp [TopCat.Presheaf.stalkCongr]

/-- `stalkCongr` composes. -/
private theorem stalkCongr_hom_comp {Z : Scheme.{0}} {a b c : Z} (h₁ : a = b) (h₂ : b = c) :
    (Z.presheaf.stalkCongr (.of_eq h₁)).hom ≫ (Z.presheaf.stalkCongr (.of_eq h₂)).hom =
      (Z.presheaf.stalkCongr (.of_eq (h₁.trans h₂))).hom := by
  subst h₁ h₂
  simp [TopCat.Presheaf.stalkCongr]

/-- The stalk map at the generic point of a composite through a dominant morphism. -/
private theorem stalkMap_comp_genericPoint_eq_of_isDominant {Z T T' : Scheme.{0}} [IsIntegral T]
    [IsIntegral T'] (e : T ⟶ T') [IsDominant e] (g' : T' ⟶ Z)
    (hη : (e ≫ g') (genericPoint T) = g' (genericPoint T')) :
    (e ≫ g').stalkMap (genericPoint T) =
      ((Z.presheaf.stalkCongr (.of_eq hη)).hom ≫ g'.stalkMap (genericPoint T')) ≫
        (T'.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant e).symm)).hom ≫
          e.stalkMap (genericPoint T) := by
  have hx : genericPoint T' = e (genericPoint T) := (map_genericPoint_of_isDominant e).symm
  have h := Scheme.Hom.stalkMap_congr_point g' _ _ hx
  rw [Scheme.Hom.stalkMap_comp, Category.assoc, reassoc_of% h]
  simp only [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
  erw [TopCat.Presheaf.stalkSpecializes_comp, TopCat.Presheaf.stalkSpecializes_refl,
    Category.id_comp]
  rfl

/-- Valuations `v₁` of `k(T₁)` and `v₂` of `k(T₂)` *agree over `Z`* for `g₁ : T₁ ⟶ Z`,
`g₂ : T₂ ⟶ Z` mapping the generic points to the same point `z`: they induce the same valuation of
the local ring `𝒪_{Z,z}`. -/
private def ValEqOver {Z T₁ T₂ : Scheme.{0}} [IsIntegral T₁] [IsIntegral T₂] (g₁ : T₁ ⟶ Z)
    (g₂ : T₂ ⟶ Z) (v₁ : Valuation T₁.functionField ℤᵐ⁰) (v₂ : Valuation T₂.functionField ℤᵐ⁰) :
    Prop :=
  ∃ h : g₁ (genericPoint T₁) = g₂ (genericPoint T₂),
    v₁.comap (g₁.stalkMap (genericPoint T₁)).hom =
      v₂.comap ((Z.presheaf.stalkCongr (.of_eq h)).hom ≫ g₂.stalkMap (genericPoint T₂)).hom

section ValEqOver

variable {Z T₁ T₂ T₃ : Scheme.{0}} [IsIntegral T₁] [IsIntegral T₂] [IsIntegral T₃]
  {g₁ : T₁ ⟶ Z} {g₂ : T₂ ⟶ Z} {g₃ : T₃ ⟶ Z} {v₁ : Valuation T₁.functionField ℤᵐ⁰}
  {v₂ : Valuation T₂.functionField ℤᵐ⁰} {v₃ : Valuation T₃.functionField ℤᵐ⁰}

private theorem ValEqOver.symm (H : ValEqOver g₁ g₂ v₁ v₂) : ValEqOver g₂ g₁ v₂ v₁ := by
  obtain ⟨h, hv⟩ := H
  refine ⟨h.symm, Valuation.ext fun z => ?_⟩
  have := congrArg (fun w : Valuation _ ℤᵐ⁰ => w ((Z.presheaf.stalkCongr (.of_eq h.symm)).hom z))
    hv
  simp only [Valuation.comap_apply, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] at this ⊢
  rw [this, stalkCongr_hom_stalkCongr_hom_apply h]

private theorem ValEqOver.trans (H₁ : ValEqOver g₁ g₂ v₁ v₂) (H₂ : ValEqOver g₂ g₃ v₂ v₃) :
    ValEqOver g₁ g₃ v₁ v₃ := by
  obtain ⟨h₁, hv₁⟩ := H₁
  obtain ⟨h₂, hv₂⟩ := H₂
  refine ⟨h₁.trans h₂, Valuation.ext fun z => ?_⟩
  have e1 := congrArg (fun w : Valuation _ ℤᵐ⁰ => w z) hv₁
  have e2 := congrArg (fun w : Valuation _ ℤᵐ⁰ => w ((Z.presheaf.stalkCongr (.of_eq h₁)).hom z))
    hv₂
  simp only [Valuation.comap_apply, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] at e1 e2 ⊢
  rw [e1, e2, ← stalkCongr_hom_comp h₁ h₂]
  rfl

/-- A valuation and its restriction along a dominant morphism over `Z` agree over `Z`. -/
private theorem valEqOver_comap_functionFieldMap (e : T₁ ⟶ T₂) [IsDominant e] (g : T₂ ⟶ Z)
    (v : Valuation T₁.functionField ℤᵐ⁰) :
    ValEqOver (e ≫ g) g v (v.comap (functionFieldMap e)) := by
  have hη : (e ≫ g) (genericPoint T₁) = g (genericPoint T₂) := by
    rw [Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
  refine ⟨hη, Valuation.ext fun z => ?_⟩
  rw [Valuation.comap_apply, Valuation.comap_apply, Valuation.comap_apply,
    stalkMap_comp_genericPoint_eq_of_isDominant e g hη]
  rfl

/-- Agreement over `Z` only depends on the morphisms through their values. -/
private theorem ValEqOver.of_eq {g₁' : T₁ ⟶ Z} {g₂' : T₂ ⟶ Z} (H : ValEqOver g₁ g₂ v₁ v₂)
    (e₁ : g₁ = g₁') (e₂ : g₂ = g₂') : ValEqOver g₁' g₂' v₁ v₂ := by
  subst e₁ e₂; exact H

end ValEqOver

end ValuationsOver

/-! ### Strata, common models and discrepancies -/

section StrataModels

open scoped WithZero

/-- The closure of the image of a point under a morphism locally of finite type has dimension at
most that of the closure of the point. -/
private theorem topologicalKrullDim_closure_map_le {T Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sY] (h : T ⟶ Y) [LocallyOfFiniteType h] (x : T) :
    topologicalKrullDim (closure {h x} : Set Y) ≤ topologicalKrullDim (closure {x} : Set T) :=
  topologicalKrullDim_closure_singleton_image_le ℂ h (h ≫ sY) sY rfl x

/-- **Strata over a common biregular open are birational.** If `f : X ⟶ Z` and `f⁺ : X' ⟶ Z`
are isomorphisms over an open `V ⊆ Z`, and `ι : S ⟶ X`, `ι' : S' ⟶ X'` are closed immersions of
integral schemes whose generic points have the same image in `V`, then `S` and `S'` have
isomorphic dense opens over `Z`. -/
private theorem exists_partialIso_isOver_of_isIso {X X' Z S S' : Scheme.{0}}
    [IsIntegral S] [IsIntegral S'] (f : X ⟶ Z) (fp : X' ⟶ Z) (V : Z.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (ι : S ⟶ X) (ι' : S' ⟶ X') [IsClosedImmersion ι]
    [IsClosedImmersion ι'] (hη : (ι ≫ f) (genericPoint S) ∈ V)
    (hcorr : (ι ≫ f) (genericPoint S) = (ι' ≫ fp) (genericPoint S')) :
    ∃ e : S.PartialIso S', e.IsOver (ι ≫ f) (ι' ≫ fp) := by
  have hη' : (ι' ≫ fp) (genericPoint S') ∈ V := hcorr ▸ hη
  set O : S.Opens := (ι ≫ f) ⁻¹ᵁ V
  set O' : S'.Opens := (ι' ≫ fp) ⁻¹ᵁ V
  have hO : (O : Set S).Nonempty := ⟨_, hη⟩
  have hO' : (O' : Set S').Nonempty := ⟨_, hη'⟩
  set a : O.toScheme ⟶ V.toScheme := (ι ≫ f) ∣_ V
  set a' : O'.toScheme ⟶ V.toScheme := (ι' ≫ fp) ∣_ V
  have ha : a = (ι ∣_ (f ⁻¹ᵁ V)) ≫ (f ∣_ V) := morphismRestrict_comp ι f V
  have ha' : a' = (ι' ∣_ (fp ⁻¹ᵁ V)) ≫ (fp ∣_ V) := morphismRestrict_comp ι' fp V
  have h₁ : IsClosedImmersion (ι ∣_ (f ⁻¹ᵁ V)) := IsZariskiLocalAtTarget.restrict ‹_› _
  have h₂ : IsClosedImmersion (ι' ∣_ (fp ⁻¹ᵁ V)) := IsZariskiLocalAtTarget.restrict ‹_› _
  haveI : IsClosedImmersion a := by
    rw [ha]; exact @IsClosedImmersion.comp _ _ _ _ _ h₁ inferInstance
  haveI : IsClosedImmersion a' := by
    rw [ha']; exact @IsClosedImmersion.comp _ _ _ _ _ h₂ inferInstance
  -- the two images in `V` are the closure of the common generic point
  have hrange : ∀ {T : Scheme.{0}} [IsIntegral T] (g : T ⟶ Z) (hg : g (genericPoint T) ∈ V)
      [IsClosedImmersion (g ∣_ V)],
      Set.range (g ∣_ V) = closure {(⟨g (genericPoint T), hg⟩ : V)} := by
    intro T _ g hg _
    have hpt : (g ∣_ V) ⟨genericPoint T, hg⟩ = ⟨g (genericPoint T), hg⟩ := by
      apply Subtype.ext
      have := congrArg (fun k : (g ⁻¹ᵁ V).toScheme ⟶ Z => k ⟨genericPoint T, hg⟩)
        (morphismRestrict_ι g V)
      simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] at this
      exact this
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [← hpt]
      have hx : (⟨genericPoint T, hg⟩ : (g ⁻¹ᵁ V).toScheme) ⤳ x :=
        (g ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.specializes_iff.mp
          (by simpa using genericPoint_specializes ((g ⁻¹ᵁ V).ι x))
      exact specializes_iff_mem_closure.mp (hx.map (g ∣_ V).continuous)
    · exact closure_minimal (Set.singleton_subset_iff.mpr ⟨_, hpt⟩)
        (g ∣_ V).isClosedEmbedding.isClosed_range
  have hr : Set.range a = Set.range a' := by
    rw [hrange (ι ≫ f) hη, hrange (ι' ≫ fp) hη']
    congr 2
    exact Subtype.ext hcorr
  obtain ⟨e₀, he₀⟩ := exists_iso_of_range_eq a a' hr
  refine ⟨⟨O, O.2.dense hO, O', O'.2.dense hO', e₀⟩, ?_⟩
  change e₀.hom ≫ O'.ι ≫ (ι' ≫ fp) = O.ι ≫ (ι ≫ f)
  rw [← morphismRestrict_ι (ι' ≫ fp) V, ← morphismRestrict_ι (ι ≫ f) V]
  change e₀.hom ≫ a' ≫ V.ι = a ≫ V.ι
  rw [← Category.assoc, he₀]

/-- A partial isomorphism over `Z` is a modification over `Z`. -/
private theorem isModificationOf_toRationalMap_of_isOver {X Y Z : Scheme.{0}} (g : X ⟶ Z)
    (g' : Y ⟶ Z) (e : X.PartialIso Y) (he : e.IsOver g g') :
    IsModificationOf g g' e.toRationalMap := by
  refine ⟨MMP.Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [MMP.Flips.RationalMap.IsOver, Scheme.PartialIso.toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ g' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ g
  rw [Category.assoc, he]
  simp

/-- **Strict transforms of prime divisors.** For a proper birational morphism `q : Γ ⟶ S` onto a
normal variety and a prime divisor `F` of `S`, there is a prime divisor `F̃` of `Γ` over `F`,
inducing the same valuation of `k(S)`. -/
private theorem exists_primeDivisor_valuation_eq_of_isBirationalMorphism {Γ S : Scheme.{0}}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [IsLocallyNoetherian Γ] [IsNormal Γ]
    {sS : S ⟶ Spec (.of ℂ)} (hS : IsNormalVariety ℂ sS) (q : Γ ⟶ S) [IsProper q]
    (hΓ : IsNormalVariety ℂ (q ≫ sS)) (hq : IsBirationalMorphism q)
    (F : MMP.Mori.PrimeDivisor S) :
    haveI : IsIntegral Γ := hΓ.1.toIsIntegral
    haveI : IsDominant q := hq.isDominant
    ∃ F' : MMP.Mori.PrimeDivisor Γ, q F'.genericPoint = F.genericPoint ∧
      F'.divisorialValuation.comap (functionFieldMap q) = F.divisorialValuation := by
  haveI : IsIntegral Γ := hΓ.1.toIsIntegral
  haveI : IsDominant q := hq.isDominant
  have := F.isDiscreteValuationRing_localRing
  have hFV : F.genericPoint ∈ biregularLocus q :=
    MMP.Flips.mem_biregularLocus_of_valuationRing hS hΓ.1 hq _
  obtain ⟨y, hy⟩ := exists_map_eq_of_mem_biregularLocus q hFV
  have hyV : q y ∈ biregularLocus q := hy ▸ hFV
  have hcy : Order.coheight y = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus q hyV, hy, F.coheight_genericPoint]
  set F' : MMP.Mori.PrimeDivisor Γ := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcy
  have hF' : F'.genericPoint = y := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  refine ⟨F', by rw [hF', hy], ?_⟩
  -- the divisor `(Γ, q, F')` over `S` is not exceptional, so it is a prime divisor of `S`
  let D : DivisorOver ℂ sS := ⟨Γ, q, hΓ, hq, F'⟩
  have hD : ¬ D.IsExceptional := by
    rw [isExceptional_iff_two_le_coheight hS]
    change ¬ 2 ≤ Order.coheight (q F'.genericPoint)
    rw [hF', hy, F.coheight_genericPoint]
    decide
  obtain ⟨P, hP⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hS D hD
  have hPF : P = F := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hS.1 hP
    change q F'.genericPoint = P.genericPoint at this
    rw [hF', hy] at this
    exact this.symm
  subst hPF
  have h1 : D.valuation = F'.divisorialValuation.comap (functionFieldMap q) := rfl
  rw [← h1, hP]
  refine Valuation.ext fun z => ?_
  change P.divisorialValuation (functionFieldMap (𝟙 S) z) = _
  rw [functionFieldMap_id_apply]

/-- `a + c = d` and `b + 1 = d` with `b ≤ a` force `c ≤ 1`. -/
private theorem le_one_of_add_eq_of_le {a b : WithBot ℕ∞} {c : ℕ∞} {d : ℕ}
    (h₁ : a + c = d) (h₂ : b + (1 : ℕ∞) = d) (hab : b ≤ a) : c ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h₁
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at h₂
    | coe b =>
      have h₁' : a + c = d := by exact_mod_cast h₁
      have h₂' : b + 1 = d := by exact_mod_cast h₂
      have hab' : b ≤ a := by exact_mod_cast hab
      induction a using ENat.recTopCoe with
      | top => simp at h₁'
      | coe a =>
        induction b using ENat.recTopCoe with
        | top => simp at h₂'
        | coe b =>
          induction c using ENat.recTopCoe with
          | top => simp at h₁'
          | coe c =>
            have e₁ : a + c = d := by exact_mod_cast h₁'
            have e₂ : b + 1 = d := by exact_mod_cast h₂'
            have e₃ : b ≤ a := by exact_mod_cast hab'
            exact_mod_cast (by omega : c ≤ 1)

/-- **Prime divisors of the positive side of a small stratum diagram.** Let `S ⤏ S'` be
birational over `Z` (a partial isomorphism `e` over `g`, `g'`), with `g`, `g'` proper, and `F` a
prime divisor of `S'` not contracted by `g'` (`dim g'(F) ≥ dim F`). Then some prime divisor of `S`
induces the same valuation of the local ring of `Z` at the common image of the generic points:
on a common model, the centre on `S` of `ord_F` has dimension at least `dim g'(F) = dim S - 1`. -/
private theorem exists_primeDivisor_valEqOver_of_partialIso {S S' Z : Scheme.{0}}
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S']
    [IsNormal S'] {sS : S ⟶ Spec (.of ℂ)} {sS' : S' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hS : IsNormalVariety ℂ sS) (hS' : IsNormalVariety ℂ sS') (hZ : MMP.Mori.IsVariety ℂ sZ)
    (g : S ⟶ Z) (g' : S' ⟶ Z) [IsProper g] [IsProper g'] (hgs : g ≫ sZ = sS)
    (hg's : g' ≫ sZ = sS') {d : ℕ} (hd : topologicalKrullDim S = d)
    (hd' : topologicalKrullDim S' = d) (e : S.PartialIso S') (he : e.IsOver g g')
    (F : MMP.Mori.PrimeDivisor S')
    (hF : ¬ topologicalKrullDim (closure {g' F.genericPoint} : Set Z) <
      topologicalKrullDim (closure {F.genericPoint} : Set S')) :
    ∃ D : MMP.Mori.PrimeDivisor S, ValEqOver g g' D.divisorialValuation F.divisorialValuation := by
  obtain ⟨Γ, p, q, hΓv, hΓs, hpP, hqP, hpb, hqb, -, hcomm⟩ :=
    IsModificationOf.exists_smooth_common_model sS sS' sZ hS hS' hZ g g' hgs hg's _
      (isModificationOf_toRationalMap_of_isOver g g' e he)
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral Γ := hΓv.toIsIntegral
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hΓs).1
  haveI := (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hΓs).2
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hΓn : IsNormalVariety ℂ (p ≫ sS) := ⟨hΓv, inferInstance⟩
  have hqs : q ≫ sS' = p ≫ sS := by
    rw [← hg's, ← hgs, ← Category.assoc, ← hcomm, Category.assoc]
  have hΓn' : IsNormalVariety ℂ (q ≫ sS') := hqs ▸ hΓn
  obtain ⟨F', hF'η, hF'v⟩ :=
    exists_primeDivisor_valuation_eq_of_isBirationalMorphism hS' q hΓn' hqb F
  -- the centre `x = p(η_{F'})` of `ord_F` on `S` has codimension one
  set x := p F'.genericPoint with hx
  have hgx : g x = g' F.genericPoint := by
    rw [hx, ← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply, hF'η]
  haveI : LocallyOfFiniteType sZ := hZ.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sS' := hS'.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (g ≫ sZ) := by rw [hgs]; infer_instance
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g sZ
  have h₁ := topologicalKrullDim_closure_map_le sZ g x
  rw [hgx] at h₁
  have h₂ : topologicalKrullDim (closure {F.genericPoint} : Set S') ≤
      topologicalKrullDim (closure {g' F.genericPoint} : Set Z) := not_lt.mp hF
  have e₁ := topologicalKrullDim_closure_singleton_add_coheight sS x
  have e₂ := topologicalKrullDim_closure_singleton_add_coheight sS' F.genericPoint
  rw [F.coheight_genericPoint, hd'] at e₂
  rw [hd] at e₁
  have hle : Order.coheight x ≤ 1 := le_one_of_add_eq_of_le e₁ e₂ (h₂.trans h₁)
  -- `x` is not the generic point of `S`
  have hne : Order.coheight x ≠ 0 := by
    intro h0
    have hmax : IsMax x := Order.coheight_eq_zero.mp h0
    have h1 : x ⤳ genericPoint S := hmax (genericPoint_specializes x)
    have hxη : x = genericPoint S := (h1.antisymm (genericPoint_specializes x)).eq
    have hηV : genericPoint S ∈ biregularLocus p := by
      haveI : ValuationRing (S.presheaf.stalk (genericPoint S)) :=
        inferInstanceAs (ValuationRing S.functionField)
      exact MMP.Flips.mem_biregularLocus_of_valuationRing hS hΓv hpb _
    have hpη : p (genericPoint Γ) = genericPoint S := map_genericPoint_of_isDominant p
    have h3 : F'.genericPoint = genericPoint Γ :=
      eq_of_map_eq_of_mem_biregularLocus (hx ▸ hxη ▸ hηV) (by rw [← hx, hxη, hpη])
    have h4 := F'.coheight_genericPoint
    rw [h3, Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at h4
    exact absurd h4 (by decide)
  have hcx : Order.coheight x = 1 :=
    le_antisymm hle (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hne))
  set D₀ : MMP.Mori.PrimeDivisor S := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcx
  have hD₀ : D₀.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
  obtain ⟨F'', hF''η, hF''v⟩ :=
    exists_primeDivisor_valuation_eq_of_isBirationalMorphism hS p hΓn hpb D₀
  have hF'' : F'' = F' := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have := D₀.isDiscreteValuationRing_localRing
    have hV : D₀.genericPoint ∈ biregularLocus p :=
      MMP.Flips.mem_biregularLocus_of_valuationRing hS hΓv hpb _
    exact eq_of_map_eq_of_mem_biregularLocus (hF''η ▸ hV) (hF''η.trans hD₀)
  subst hF''
  refine ⟨D₀, ?_⟩
  have H₁ := valEqOver_comap_functionFieldMap p g F''.divisorialValuation
  have H₂ := valEqOver_comap_functionFieldMap q g' F''.divisorialValuation
  rw [hF''v] at H₁
  rw [hF'v] at H₂
  exact H₁.symm.trans (H₂.of_eq hcomm.symm rfl)

/-- A `ℚ`-Cartier `ℚ`-divisor is an `ℝ`-combination of Cartier divisors. -/
private theorem isCartierCombination_toRDivisor_of_isQCartier {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {D : QDivisor X} (hD : D.IsQCartier) :
    IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, r, L, hL, hD⟩ := (QDivisor.isCartierCombination_iff_isQCartier D).mpr hD
  refine ⟨m, fun j => (r j : ℝ), L, hL, ?_⟩
  ext P
  rw [hD]
  simp [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [QDivisor.toRDivisor, DivisorWithCoeffs.mapCoeffsAddMonoidHom, DivisorWithCoeffs.mapCoeffs,
    Finsupp.mapRange_apply]

/-- **FA discrepancies are Kollár–Mori discrepancies.** If `a` is the FA discrepancy of a
valuation `v` with respect to a `ℚ`-divisor `Δ`, then `v` is the valuation of a divisor over `X`
whose Kollár–Mori discrepancy is `a`. -/
private theorem exists_isDiscrepancy_of_flipsIsDiscrepancy {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {v : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : MMP.Flips.IsDiscrepancy sX n K (QDivisor.toRDivisor Δ) v a) :
    ∃ (E : DivisorOver ℂ sX) (a' : ℚ), IsProper E.f ∧ E.valuation = v ∧
      MMP.Mori.IsDiscrepancy sX n K Δ E a' ∧ (a' : ℝ) = a := by
  obtain ⟨hK, hC, -, E, ω, m, r, L, hEv, hω, hw⟩ := h
  have hX : IsNormalVariety ℂ sX := hw.1
  have hl := hw.isLogDiscrepancy (hω ▸ hK)
  have hQ : (Divisor.toQDivisor K + Δ).IsQCartier := by
    apply MMP.Flips.QDivisor.isQCartier_of_isCartierCombination
    rwa [map_add, QDivisor.toRDivisor_toQDivisor]
  have hP : MMP.Mori.IsPair sX Δ := ⟨hX, n, K, hK, hQ⟩
  obtain ⟨a', ha'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK E.toDivisorOver
  refine ⟨E.toDivisorOver, a', E.isProper, hEv, ha', ?_⟩
  have := MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha' hl
  linarith

/-- **A dlt pair is log canonical in the sense of FA.** -/
private theorem isLogCanonical_of_isDltPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] {B : QDivisor X} (hB : MMP.Intersection.IsDltPair sX B) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    MMP.Flips.IsLogCanonical sX n K (QDivisor.toRDivisor B) := by
  obtain ⟨⟨hP, hB0, hlc⟩, hB1, -⟩ := hB
  have hX : IsNormalVariety ℂ sX := hP.1
  refine ⟨⟨hX, fun P => ?_⟩, hK, ?_, fun F _ a ha => ?_⟩
  · rw [QDivisor.coeff_toRDivisor]
    exact ⟨by exact_mod_cast hB0 P, by exact_mod_cast hB1 P⟩
  · have hQ : (Divisor.toQDivisor K + B).IsQCartier := by
      obtain ⟨-, n', K', hK', hQ'⟩ := hP
      exact hQ'.add_of_linearlyEquivalent
        (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hX hK' hK)
    have := isCartierCombination_toRDivisor_of_isQCartier hQ
    rwa [map_add, QDivisor.toRDivisor_toQDivisor] at this
  · obtain ⟨-, -, -, E, ω, m, r, L, -, hω, hw⟩ := ha
    have hl := hw.isLogDiscrepancy (hω ▸ hK)
    have := hlc n E.toDivisorOver (1 + a) hl
    linarith

/-- **A flip of `K + B` in the sense of `MMP.Fourfold.IsFlipOf` is a flip in the sense of
Kollár–Mori**, for a canonical divisor `K`. -/
private theorem isFlip_of_isFlipOf {X X' Z : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : QDivisor X} {f : X ⟶ Z}
    {fp : X' ⟶ Z} (h : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp) :
    MMP.Mori.IsFlip sX sZ sX' K B f fp := by
  have htr : flipTransform f fp (Divisor.toQDivisor K + B) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B := by
    rw [map_add]
    congr 1
    exact flipTransform_mapCoeffsAddMonoidHom _ _ _ _
  have := isProper_of_isProjectiveMorphism _ h.isContraction.isProjectiveMorphism
  exact
    { isFlippingContraction :=
        { isNormalVariety_source := h.isContraction.isNormalVariety_source
          isNormalVariety_target := h.isContraction.isNormalVariety_target
          comp_eq := h.isContraction.comp_eq
          isCanonicalDivisor := ⟨n, hK⟩
          isQCartier := h.isQCartier
          isProper := this
          isBirationalMorphism := h.isSmallMorphism.isBirationalMorphism
          two_le_codimension := h.isSmallMorphism.two_le_codimension
          hasRelativelyAmpleMultiple := h.hasRelativelyAmpleMultiple }
      isNormalVariety := h.isSmallMorphism_flip.isNormalVariety_source
      comp_eq := h.isSmallMorphism_flip.comp_eq
      isProper := h.isSmallMorphism_flip.isProper
      isBirationalMorphism := h.isSmallMorphism_flip.isBirationalMorphism
      isQCartier := htr ▸ h.isQCartier_flip
      hasRelativelyAmpleMultiple := htr ▸ h.hasRelativelyAmpleMultiple_flip
      two_le_codimension := h.isSmallMorphism_flip.two_le_codimension }

/-- **Discrepancies of strata do not decrease along a flip**
(`MMP.Mori.IsFlip.isDiscrepancy_le_of_isStratumAdjunctionPair`), for divisors over corresponding
adjunction strata which agree over the base. -/
private theorem isDiscrepancy_le_of_valEqOver_of_isFlipOf {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {n₀ : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n₀) {B : QDivisor X} {f : X ⟶ Z}
    {fp : X' ⟶ Z} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') (hB : MMP.Intersection.IsDltPair sX B)
    (hB' : MMP.Intersection.IsDltPair sX' (flipTransform f fp B))
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp)
    (hstrata : ∀ T : Set X, IsDltStratum sX B T →
      ¬ T ⊆ (MMP.Mori.exceptionalSet f : Set X))
    (hstrata' : ∀ T : Set X', IsDltStratum sX' (flipTransform f fp B) T →
      ¬ T ⊆ (MMP.Mori.exceptionalSet fp : Set X'))
    {S S' : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    {ι : S ⟶ X} {ι' : S' ⟶ X'} {BS : QDivisor S} {BS' : QDivisor S'}
    (hS : IsStratumAdjunctionPair sX B ι BS)
    (hS' : IsStratumAdjunctionPair sX' (flipTransform f fp B) ι' BS')
    (D : DivisorOver ℂ (ι ≫ sX)) (D' : DivisorOver ℂ (ι' ≫ sX'))
    (hv : ValEqOver (ι ≫ f) (ι' ≫ fp) D.valuation D'.valuation)
    {n n' : ℕ} {KS : Divisor S} {KS' : Divisor S'} {a a' : ℚ}
    (ha : MMP.Mori.IsDiscrepancy (ι ≫ sX) n KS BS D a)
    (ha' : MMP.Mori.IsDiscrepancy (ι' ≫ sX') n' KS' BS' D' a') :
    a ≤ a' := by
  obtain ⟨hcorr, hv⟩ := hv
  exact MMP.Mori.IsFlip.isDiscrepancy_le_of_isStratumAdjunctionPair hX hX' hB hB'
    (isFlip_of_isFlipOf hK hflip) hstrata hstrata' hS hS' hcorr D D' hv ha ha'

/-- A birational morphism `p : U ⟶ S` is represented by a partial isomorphism over every
`g : S ⟶ Z`. -/
private theorem exists_partialIso_isOver_of_isBirationalMorphism {U S Z : Scheme.{0}}
    [IsReduced U] [IsSeparated (S ↘ ⊤_ Scheme)] (p : U ⟶ S) (hp : IsBirationalMorphism p)
    (g : S ⟶ Z) : ∃ e : U.PartialIso S, e.IsOver (p ≫ g) g := by
  obtain ⟨e, he⟩ := hp
  have h1 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)
  refine ⟨e, ?_⟩
  change e.iso.hom ≫ e.target.ι ≫ g = e.source.ι ≫ p ≫ g
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ g) h1

/-- **Realizations agree over the base.** If a divisor `E` over `X` realizes the prime divisor `F`
of `Y` through a map `φ : X ⤏ Y` over `Z`, then `E` and `ord_F` agree over `Z`. -/
private theorem valEqOver_of_isRealizedOver {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (f : X ⟶ Z) (g : Y ⟶ Z) {φ : X.RationalMap Y}
    (hφ : MMP.Flips.RationalMap.IsOver f g φ) {F : MMP.Mori.PrimeDivisor Y}
    {E : MMP.Flips.ProperDivisorOver ℂ sX} (hE : MMP.Flips.IsRealizedOver sX φ F E) :
    ValEqOver f g E.valuation F.divisorialValuation := by
  obtain ⟨g', p, hp, hg', hcomm, hv⟩ := hE
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI : IsDominant p := hp.isDominant
  haveI : IsDominant E.f := E.isDominant
  have h1 : g'.hom ≫ g = g'.domain.ι ≫ f := hom_comp_eq_of_isOver hφ g' hg'
  have hgen : genericPoint X ∈ g'.domain :=
    ((genericPoint_spec X).mem_open_set_iff g'.domain.isOpen).mpr
      (by simpa using g'.dense_domain.nonempty)
  have hne : ((E.f ⁻¹ᵁ g'.domain : E.Y.Opens) : Set E.Y).Nonempty :=
    ⟨genericPoint E.Y, show E.f (genericPoint E.Y) ∈ g'.domain by
      rw [map_genericPoint_of_isDominant]; exact hgen⟩
  haveI : IsDominant (E.f ⁻¹ᵁ g'.domain).ι := AlgebraicGeometry.Opens.isDominant_ι
    ((E.f ⁻¹ᵁ g'.domain).2.dense hne)
  have h2 : p ≫ g = E.f ≫ f := by
    refine ext_of_isDominant_of_isSeparated (Z ↘ ⊤_ Scheme) (Subsingleton.elim _ _)
      (E.f ⁻¹ᵁ g'.domain).ι ?_
    rw [← Category.assoc, hcomm, Category.assoc, h1, ← Category.assoc, morphismRestrict_ι,
      Category.assoc]
  have H1 := valEqOver_comap_functionFieldMap E.f f E.E.divisorialValuation
  have H2 := valEqOver_comap_functionFieldMap p g E.E.divisorialValuation
  rw [hv] at H2
  exact H1.symm.trans (H2.of_eq h2 rfl)

/-- A partial isomorphism over `Z` is over `Z` as a rational map, and so is every inverse. -/
private theorem isOver_inverse_of_isOver {X Y Z : Scheme.{0}} [IsReduced X] [IsReduced Y]
    [IsSeparated (Z ↘ ⊤_ Scheme)] (f : X ⟶ Z) (g : Y ⟶ Z) (e : X.PartialIso Y)
    (he : e.IsOver f g) {ψ : Y.RationalMap X}
    (hψ : MMP.Mori.RationalMap.IsInverse e.toRationalMap ψ) :
    MMP.Flips.RationalMap.IsOver g f ψ := by
  obtain ⟨e', he', rfl⟩ := hψ
  have hov : MMP.Flips.RationalMap.IsOver f g e.toRationalMap :=
    (isModificationOf_toRationalMap_of_isOver f g e he).2
  rw [← he'] at hov
  have h1 := hom_comp_eq_of_isOver hov e'.toPartialMap rfl
  exact (isModificationOf_toRationalMap_of_isOver g f e'.symm (by
    change e'.iso.inv ≫ e'.source.ι ≫ f = e'.target.ι ≫ g
    rw [← cancel_epi e'.iso.hom, Iso.hom_inv_id_assoc, ← Category.assoc]
    exact h1.symm)).2

/-- A common model of a map over `Z` commutes over `Z`: `p ≫ f = q ≫ g`. -/
private theorem comp_eq_of_isCommonModel {X Y Z W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {f : X ⟶ Z}
    {g : Y ⟶ Z} {φ : X.RationalMap Y} {p : W ⟶ X} {q : W ⟶ Y}
    (hW : IsCommonModel ℂ sX sY sZ sW f g φ p q) : p ≫ f = q ≫ g := by
  obtain ⟨φ₀, hφ₀, hd, hq⟩ := hW.comp_eq
  have hWv := hW.isNormalVariety
  haveI : IsIntegral W := hWv.1.toIsIntegral
  haveI : IsSeparated sY := hW.isVariety_Y.toIsSeparated
  haveI : IsSeparated (Y ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sY)
  haveI : IsSeparated sZ := hW.isVariety_Z.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  haveI : IsIntegral X := hW.isVariety_X.toIsIntegral
  have h1 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp hq)
  have h2 := hom_comp_eq_of_isOver hW.isModificationOf.2 φ₀ hφ₀
  haveI : IsDominant (p ⁻¹ᵁ φ₀.domain).ι := AlgebraicGeometry.Opens.isDominant_ι hd
  refine ext_of_isDominant_of_isSeparated (Z ↘ ⊤_ Scheme) (Subsingleton.elim _ _)
    (p ⁻¹ᵁ φ₀.domain).ι ?_
  have h1' : p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom = (p ⁻¹ᵁ φ₀.domain).ι ≫ q := h1
  rw [← Category.assoc _ q, ← h1', Category.assoc, h2, Scheme.Hom.resLE_comp_ι_assoc]

/-- **A log canonical model over a base.** Let `π : W ⟶ Z` and `g : S ⟶ Z` be proper morphisms
of normal varieties, `e : W ⤏ S` birational over `Z`, and `(W, B_W)`, `(S, B_S)` dlt pairs with
canonical divisors of dimension `d`, `K_W + B_W` `ℚ`-Cartier and `K_S + B_S` `g`-ample. If every
prime divisor `P` of `W` has `-coeff_P B_W ≤ a(P, S, B_S)` and every prime divisor `F` of `S` has
`-coeff_F B_S ≤ a(F, W, B_W)`, the valuations being compared over `Z`, then
`g : (S, B_S) ⟶ Z` is a log canonical model of `π : (W, B_W) ⟶ Z` through `e`. -/
private theorem isLogCanonicalModelOf_of_le {W S Z : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
    [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S] [CompactSpace S]
    {sW : W ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sW] [QuasiCompact sW] [LocallyOfFiniteType sS] [QuasiCompact sS]
    (hW : IsNormalVariety ℂ sW) (hS : IsNormalVariety ℂ sS) (hZ : MMP.Mori.IsVariety ℂ sZ)
    (π : W ⟶ Z) (g : S ⟶ Z) [IsProper π] [IsProper g] (hπ : π ≫ sZ = sW) (hg : g ≫ sZ = sS)
    {d : ℕ} {KW : Divisor W} (hKW : KW.IsCanonicalDivisor sW d) {BW : QDivisor W}
    (hBW : MMP.Intersection.IsDltPair sW BW)
    {KS : Divisor S} (hKS : KS.IsCanonicalDivisor sS d) {BS : QDivisor S}
    (hBS : MMP.Intersection.IsDltPair sS BS)
    (hamp : (Divisor.toQDivisor KS + BS).HasRelativelyAmpleMultiple g)
    (e : W.PartialIso S) (he : e.IsOver π g)
    (hprime : ∀ (P : MMP.Mori.PrimeDivisor W) (D : DivisorOver ℂ sS) (n : ℕ) (K : Divisor S)
      (a : ℚ), ValEqOver π g P.divisorialValuation D.valuation →
      MMP.Mori.IsDiscrepancy sS n K BS D a → -BW.coeff P ≤ a)
    (hprime' : ∀ (F : MMP.Mori.PrimeDivisor S) (D : DivisorOver ℂ sW) (n : ℕ) (K : Divisor W)
      (a : ℚ), ValEqOver π g D.valuation F.divisorialValuation →
      MMP.Mori.IsDiscrepancy sW n K BW D a → -BS.coeff F ≤ a) :
    IsLogCanonicalModelOf sS sW d KW (QDivisor.toRDivisor BW) KS π g e.toRationalMap
      (fun F => (BS.coeff F : ℝ)) (QDivisor.toRDivisor BS) := by
  classical
  haveI : IsSeparated sZ := hZ.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  have hmod := isModificationOf_toRationalMap_of_isOver π g e he
  obtain ⟨hcodim, -, hfin, hreal⟩ :=
    hmod.isMorphismInCodimOne_and_exists_isRealizedOver sW sS sZ hW hS hZ π g hπ hg
  have hlcS := isLogCanonical_of_isDltPair hBS hKS
  have hlcW := isLogCanonical_of_isDltPair hBW hKW
  have hampR : IsRelativelyAmple g (logCanonicalDivisor KS (QDivisor.toRDivisor BS)) := by
    rw [logCanonicalDivisor_eq]
    exact hamp.isRelativelyAmple_toRDivisor
  have hnefR : IsRelativelyNef ℂ sS g (logCanonicalDivisor KS (QDivisor.toRDivisor BS)) :=
    IsRelativelyAmple.isRelativelyNef sS hampR
  have hcoeff : ∀ (P : MMP.Mori.PrimeDivisor W) (F : MMP.Mori.PrimeDivisor S),
      ValEqOver π g P.divisorialValuation F.divisorialValuation → BW.coeff P = BS.coeff F := by
    intro P F hPF
    obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBS.1.1 hKS
      (DivisorOver.ofPrimeDivisor ℂ hS F)
    obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBW.1.1 hKW
      (DivisorOver.ofPrimeDivisor ℂ hW P)
    have ha' := ha.eq_neg_coeff_of_ofPrimeDivisor hS
    have hb' := hb.eq_neg_coeff_of_ofPrimeDivisor hW
    have h1 := hprime P _ d KS a (by rwa [valuation_ofPrimeDivisor]) ha
    have h2 := hprime' F _ d KW b (by rwa [valuation_ofPrimeDivisor]) hb
    linarith
  refine ⟨⟨inferInstance, inferInstance, hmod, ⟨hW, hS, hmod.1, hcodim, hKW, hlcW.2.2.1,
    hfin.toFinset, fun F => by simp, fun F _ => hreal F, fun F _ => ⟨?_, fun E a hE ha => ?_⟩,
    ?_⟩, hlcS.2.2.1, ⟨inferInstance, hlcS, hnefR⟩, ?_⟩, ⟨inferInstance, hlcS, hampR⟩⟩
  · show (BS.coeff F : ℝ) ≤ 1
    exact_mod_cast hBS.2.1 F
  · -- `𝓕` is admissible
    obtain ⟨E', a', -, hE'v, ha', haa⟩ := exists_isDiscrepancy_of_flipsIsDiscrepancy ha
    have hv := valEqOver_of_isRealizedOver π g hmod.2 hE
    rw [← hE'v] at hv
    have := hprime' F E' d KW a' hv ha'
    have : -(BS.coeff F : ℝ) ≤ a := by rw [← haa]; exact_mod_cast this
    exact (min_le_right _ _).trans (by linarith)
  · -- the boundary of `S` is the `𝓕`-birational transform of `B_W`
    obtain ⟨θ, -, -, hmatch, W', sW', p, q, hWc, hval⟩ :=
      MMP.Flips.IsModificationOf.exists_ringHom_functionField hW hS hZ hπ hg hmod
    haveI : IsIntegral W' := hWc.isNormalVariety.1.toIsIntegral
    haveI : IsDominant p := hWc.isBirationalMorphism_p.isDominant
    haveI : IsDominant q := hWc.isBirationalMorphism_q.isDominant
    have hpq := comp_eq_of_isCommonModel hWc
    ext F
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.finset_sum_apply,
      Finsupp.single_apply]
    by_cases hF : MMP.Flips.RationalMap.IsInverseExceptional e.toRationalMap F
    · have h0 : (MMP.Mori.RationalMap.transformDivisor e.toRationalMap
          (QDivisor.toRDivisor BW)) F = 0 :=
        MMP.Flips.mapPrimeDivisors_apply_eq_zero_of_forall_ne (fun P hP => hF P hP) _
      have hmem : F ∈ hfin.toFinset := by simpa using hF
      rw [h0, zero_add, Finset.sum_ite_eq' _ _ _, if_pos hmem]
      rfl
    · obtain ⟨Q, -, hQv, hQc⟩ := hmatch F hF
      obtain ⟨w, hw1, hw2⟩ := hval Q.divisorialValuation
      have H1 := valEqOver_comap_functionFieldMap p π w
      have H2 := valEqOver_comap_functionFieldMap q g w
      rw [hw1] at H1
      rw [hw2, hQv] at H2
      have hv : ValEqOver π g Q.divisorialValuation F.divisorialValuation :=
        H1.symm.trans (H2.of_eq hpq.symm rfl)
      have hnmem : F ∉ hfin.toFinset := by simpa using hF
      have hQc' := hQc (QDivisor.toRDivisor BW)
      rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply] at hQc'
      rw [hQc', Finset.sum_ite_eq' _ _ _, if_neg hnmem, add_zero]
      change ((BS.coeff F : ℚ) : ℝ) = ((BW.coeff Q : ℚ) : ℝ)
      rw [hcoeff Q F hv]
  · -- the discrepancy inequalities on the divisors contracted by `e`
    intro hφ P _ E a a' hE ha ha'
    have hov := isOver_inverse_of_isOver π g e he hφ.isInverse_inverse
    have hv := valEqOver_of_isRealizedOver g π hov hE
    obtain ⟨E', b, -, hE'v, hb, hba⟩ := exists_isDiscrepancy_of_flipsIsDiscrepancy ha
    obtain ⟨E'', c, -, hE''v, hc, hca⟩ := exists_isDiscrepancy_of_flipsIsDiscrepancy ha'
    have hc' : c = -BW.coeff P := by
      obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBW.1.1 hKW
        (DivisorOver.ofPrimeDivisor ℂ hW P)
      have := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq
        (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sW hKW BW |>.mp hBW).1
        (hE''v.trans (valuation_ofPrimeDivisor hW P).symm) hc hc₀
      rw [this, hc₀.eq_neg_coeff_of_ofPrimeDivisor hW]
    rw [← hE'v] at hv
    have := hprime P E' d KS b hv.symm hb
    rw [← hba, ← hca, hc']
    exact_mod_cast this

/-- Agreement over `Z` along one morphism whose stalk map at the generic point is surjective is
equality of valuations. -/
private theorem ValEqOver.eq_of_surjective {Z T : Scheme.{0}} [IsIntegral T] {g : T ⟶ Z}
    (hg : Function.Surjective (g.stalkMap (genericPoint T)))
    {v w : Valuation T.functionField ℤᵐ⁰} (H : ValEqOver g g v w) : v = w := by
  obtain ⟨h, hv⟩ := H
  have hc : ∀ z, (Z.presheaf.stalkCongr (.of_eq h)).hom z = z := fun z => by
    simp [TopCat.Presheaf.stalkCongr]
  refine Valuation.ext fun x => ?_
  obtain ⟨y, rfl⟩ := hg x
  have := congrArg (fun u : Valuation _ ℤᵐ⁰ => u y) hv
  simp only [Valuation.comap_apply, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply, hc] at this
  exact this

/-- The stalk map at the generic point of a composite with a birational morphism is surjective
when that of the second factor is. -/
private theorem surjective_stalkMap_comp_of_isBirationalMorphism {Z T T' : Scheme.{0}}
    [IsIntegral T] [IsIntegral T'] (q : T ⟶ T') (hq : IsBirationalMorphism q) (g : T' ⟶ Z)
    (hg : Function.Surjective (g.stalkMap (genericPoint T'))) :
    Function.Surjective ((q ≫ g).stalkMap (genericPoint T)) := by
  haveI : IsDominant q := hq.isDominant
  have hη : (q ≫ g) (genericPoint T) = g (genericPoint T') := by
    rw [Scheme.Hom.comp_apply, map_genericPoint_of_isDominant]
  have hb := hq.functionFieldMap_bijective
  rw [stalkMap_comp_genericPoint_eq_of_isDominant q g hη]
  intro x
  obtain ⟨y, rfl⟩ := hb.2 x
  obtain ⟨z, rfl⟩ := hg y
  refine ⟨(Z.presheaf.stalkCongr (.of_eq hη)).inv z, ?_⟩
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  rfl

/-- The stalk map at the generic point of a stratum not inside the exceptional set is
surjective. -/
private theorem surjective_stalkMap_of_not_subset {X Z S : Scheme.{0}} [IsIntegral S]
    (ι : S ⟶ X) [IsClosedImmersion ι] (f : X ⟶ Z)
    (h : ¬ Set.range ι.base ⊆ (MMP.Mori.exceptionalSet f : Set X)) :
    Function.Surjective ((ι ≫ f).stalkMap (genericPoint S)) := by
  have hm := map_mem_biregularLocus_of_not_subset (isGenericPoint_range ι) h
  haveI := MMP.isIso_stalkMap_of_mem_biregularLocus f hm
  intro y
  obtain ⟨z, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective (f := ι) _ y
  obtain ⟨w, rfl⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap (ι (genericPoint S)))).2 z
  exact ⟨w, by rw [Scheme.Hom.stalkMap_comp]; rfl⟩

/-- **Prime divisors along a step over a normal base.** Let `f : X ⟶ Z'` and `f⁺ : X' ⟶ Z'` be
proper birational morphisms of normal varieties onto a normal variety, `f⁺` with exceptional set
of codimension at least two, `φ : X ⤏ X'` a modification of `f` into `f⁺`, and `B' = φ_* B`.
Every prime divisor `F'` of `X'` lies over a prime divisor of `Z'`; its strict transform `F` on
`X` has the same coefficient, `F' = φ_* F`, and `F`, `F'` define the same valuation of `k(Z')`. -/
private theorem exists_primeDivisor_of_isModificationOf {X X' Z' : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z'] [IsLocallyNoetherian Z'] [IsNormal Z']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ' : Z' ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX') (hZ' : IsNormalVariety ℂ sZ')
    {f : X ⟶ Z'} {fp : X' ⟶ Z'} [IsProper f] [IsProper fp] (hfs : f ≫ sZ' = sX)
    (hfps : fp ≫ sZ' = sX') (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hsmall : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet fp))
    {φ : X.RationalMap X'} (hφ : IsModificationOf f fp φ) (D : QDivisor X)
    (F' : MMP.Mori.PrimeDivisor X') :
    haveI : IsDominant f := hfb.isDominant
    haveI : IsDominant fp := hfpb.isDominant
    ∃ F : MMP.Mori.PrimeDivisor X, f F.genericPoint = fp F'.genericPoint ∧
      F.divisorialValuation.comap (functionFieldMap f) =
        F'.divisorialValuation.comap (functionFieldMap fp) ∧
      (MMP.Mori.RationalMap.transformDivisor φ D).coeff F' = D.coeff F := by
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  haveI : IsSeparated sZ' := hZ'.1.toIsSeparated
  haveI : IsSeparated (Z' ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ')
  haveI : IsSeparated sX' := hX'.1.toIsSeparated
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sX')
  haveI : X'.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sX']; infer_instance⟩
  have hXn : IsNormalVariety ℂ (f ≫ sZ') := hfs ▸ hX
  have hX'n : IsNormalVariety ℂ (fp ≫ sZ') := hfps ▸ hX'
  -- the prime divisor `Q` of `Z'` under `F'`
  have hF'V : fp F'.genericPoint ∈ biregularLocus fp :=
    Oai4C1.map_genericPoint_mem_biregularLocus hsmall F'
  have hcoh : Order.coheight (fp F'.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp hF'V, F'.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hQ : Q.genericPoint = fp F'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
  -- its strict transforms
  obtain ⟨F, hFη, hFv⟩ := exists_primeDivisor_valuation_eq_of_isBirationalMorphism hZ' f hXn hfb Q
  obtain ⟨F'', hF''η, hF''v⟩ :=
    exists_primeDivisor_valuation_eq_of_isBirationalMorphism hZ' fp hX'n hfpb Q
  have hF'' : F'' = F' :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      eq_of_map_eq_of_mem_biregularLocus (by rw [hF''η.trans hQ]; exact hF'V)
        (hF''η.trans hQ)
  subst hF''
  have hQV : Q.genericPoint ∈ biregularLocus f := by
    have := Q.isDiscreteValuationRing_localRing
    exact MMP.Flips.mem_biregularLocus_of_valuationRing hZ' hXn.1 hfb _
  refine ⟨F, hFη.trans hQ, hFv.trans hF''v.symm, ?_⟩
  -- `F'' = φ_* F`, and `F` is the only prime divisor sent to `F''`
  have hdom : ∀ P : MMP.Mori.PrimeDivisor X, P.genericPoint ∈ φ.domain := fun P =>
    MMP.Flips.RationalMap.mem_domain_of_coheight_le_one f fp φ hφ.2
      (by rw [P.coheight_genericPoint])
  have hg' : φ.toPartialMap.toRationalMap = φ := φ.toRationalMap_toPartialMap
  have hcomp := hom_comp_eq_of_isOver hφ.2 φ.toPartialMap hg'
  have hE : MMP.Mori.RationalMap.transformPrimeDivisor φ F = some F'' := by
    refine transformPrimeDivisor_eq_some_of_genericPoint_eq φ.toPartialMap hg' (hdom F) ?_
    have h1 := hom_apply_eq_of_comp_eq hcomp ⟨F.genericPoint, hdom F⟩
    refine eq_of_map_eq_of_mem_biregularLocus hF'V ?_
    rw [h1, hF''η, hFη]
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hE (fun P hP => ?_) D
  have h1 := genericPoint_eq_of_transformPrimeDivisor_eq_some hP φ.toPartialMap hg' (hdom P)
  have h2 := hom_apply_eq_of_comp_eq hcomp ⟨P.genericPoint, hdom P⟩
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  have hPF : f P.genericPoint = f F.genericPoint := by rw [← h2, ← h1, hF''η, ← hFη]
  exact eq_of_map_eq_of_mem_biregularLocus (by rw [hPF, hFη]; exact hQV) hPF

/-- A modification over `Z'` is represented by a partial isomorphism over `Z'`, hence over every
`g : Z' ⟶ T`. -/
private theorem exists_partialIso_isOver_of_isModificationOf {X X' Z' T : Scheme.{0}}
    [IsReduced X] [IsSeparated (Z' ↘ ⊤_ Scheme)] {f : X ⟶ Z'} {fp : X' ⟶ Z'}
    {φ : X.RationalMap X'} (hφ : IsModificationOf f fp φ) (g : Z' ⟶ T) :
    ∃ e : X.PartialIso X', e.toRationalMap = φ ∧ e.IsOver (f ≫ g) (fp ≫ g) := by
  obtain ⟨e, he⟩ := hφ.1
  refine ⟨e, he, ?_⟩
  have h1 := hom_comp_eq_of_isOver hφ.2 e.toPartialMap he
  change e.iso.hom ≫ e.target.ι ≫ fp ≫ g = e.source.ι ≫ f ≫ g
  rw [← Category.assoc e.target.ι, ← Category.assoc, ← Category.assoc e.source.ι]
  exact congrArg (· ≫ g) h1

/-- The push-forward along a birational morphism onto a normal variety has, along a prime divisor
`Q` of the target, the coefficient of the strict transform of `Q`. -/
private theorem coeff_transformDivisor_toRationalMap {X Z' : Scheme.{0}} [IsIntegral X]
    [IsSeparated (Z' ↘ ⊤_ Scheme)] (f : X ⟶ Z') {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) {F : MMP.Mori.PrimeDivisor X} {Q : MMP.Mori.PrimeDivisor Z'}
    (hFQ : f F.genericPoint = Q.genericPoint) (hQV : Q.genericPoint ∈ biregularLocus f) :
    (MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D) Q = D F := by
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f F Q).mpr hFQ)
    (fun P hP => ?_) D
  have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mp hP
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective <| eq_of_map_eq_of_mem_biregularLocus
    (by rw [h1]; exact hQV) (h1.trans hFQ.symm)

/-- Restriction of valuations along a surjective ring homomorphism is injective. -/
private theorem valuation_eq_of_comap_eq {A K : Type*} [CommRing A] [CommRing K] {φ : A →+* K}
    (hφ : Function.Surjective φ) {v w : Valuation K ℤᵐ⁰} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation A ℤᵐ⁰ => u y) h

/-- **Discrepancies along a step over a normal base** (KM 3.38). In the setting of
`exists_primeDivisor_of_isModificationOf`, with canonical divisors `K`, `K'` of dimension `n`,
`-(K + B)` nef over `f` and `K' + B'` nef over `f⁺`: every divisor `D'` over `X'` has the
valuation, read in `k(Z')`, of a divisor `D` over `X` with `a(D, X, B) ≤ a(D', X', B')`. -/
private theorem exists_isDiscrepancy_le_of_isModificationOf {X X' Z' : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [IsIntegral Z'] [IsLocallyNoetherian Z'] [IsNormal Z']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ' : Z' ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (hX' : IsNormalVariety ℂ sX') (hZ' : IsNormalVariety ℂ sZ')
    {f : X ⟶ Z'} {fp : X' ⟶ Z'} [IsProper f] [IsProper fp] (hfs : f ≫ sZ' = sX)
    (hfps : fp ≫ sZ' = sX') (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hsmall : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet fp))
    {φ : X.RationalMap X'} (hφ : IsModificationOf f fp φ) {B : QDivisor X} {B' : QDivisor X'}
    (hB' : B' = MMP.Mori.RationalMap.transformDivisor φ B) {n : ℕ} {K : Divisor X}
    {K' : Divisor X'} (hK : K.IsCanonicalDivisor sX n) (hK' : K'.IsCanonicalDivisor sX' n)
    (hP : MMP.Mori.IsPairWith sX n K B) (hP' : MMP.Mori.IsPairWith sX' n K' B')
    (hN : QDivisor.IsRelativelyNef sX f (-(Divisor.toQDivisor K + B)))
    (hN' : QDivisor.IsRelativelyNef sX' fp (Divisor.toQDivisor K' + B'))
    (D' : DivisorOver ℂ sX') {a' : ℚ} (ha' : MMP.Mori.IsDiscrepancy sX' n K' B' D' a') :
    haveI : IsDominant f := hfb.isDominant
    haveI : IsDominant fp := hfpb.isDominant
    ∃ D : DivisorOver ℂ sX, D.valuation.comap (functionFieldMap f) =
        D'.valuation.comap (functionFieldMap fp) ∧
      ∀ a : ℚ, MMP.Mori.IsDiscrepancy sX n K B D a → a ≤ a' := by
  haveI : IsDominant f := hfb.isDominant
  haveI : IsDominant fp := hfpb.isDominant
  haveI : IsSeparated sZ' := hZ'.1.toIsSeparated
  haveI : IsSeparated (Z' ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ')
  have hXn : IsNormalVariety ℂ (f ≫ sZ') := hfs ▸ hX
  have hX'n : IsNormalVariety ℂ (fp ≫ sZ') := hfps ▸ hX'
  -- a proper divisor over `X'` with the valuation of `D'`
  obtain ⟨D'₁, hD'₁p, hD'₁v⟩ := exists_isProper_valuation_eq hX' D'
  obtain ⟨a'₁, ha'₁⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP'.isPair hK' D'₁
  have heq := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP' hD'₁v ha'₁ ha'
  haveI := D'₁.isIntegral
  haveI := D'₁.isLocallyNoetherian
  haveI := D'₁.isNormal
  haveI := D'₁.isDominant
  haveI := hD'₁p
  -- `D'₁` as a divisor over `Z'`, realized over `X`
  have hcb : IsBirationalMorphism (D'₁.f ≫ fp) :=
    MMP.Mori.isBirationalMorphism_comp D'₁.isBirationalMorphism hfpb
  have hcn : IsNormalVariety ℂ ((D'₁.f ≫ fp) ≫ sZ') := by
    rw [Category.assoc, hfps]; exact D'₁.isNormalVariety
  let D'' : MMP.Flips.ProperDivisorOver ℂ sZ' :=
    ⟨⟨D'₁.Y, D'₁.f ≫ fp, hcn, hcb, D'₁.E⟩, inferInstance⟩
  have hD''v : D''.valuation = D'₁.valuation.comap (functionFieldMap fp) := by
    haveI : IsDominant (D'₁.f ≫ fp) := hcb.isDominant
    refine Valuation.ext fun t => ?_
    change D'₁.E.divisorialValuation (functionFieldMap (D'₁.f ≫ fp) t) =
      D'₁.E.divisorialValuation (functionFieldMap D'₁.f (functionFieldMap fp t))
    rw [MMP.Fourfold.Oai4C1.functionFieldMap_comp_apply D'₁.f fp rfl]
  obtain ⟨D₁, hD₁v, hn₁, hb₁, hp₁, hD₁v'⟩ :=
    MMP.Flips.ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hZ'.1 f hXn.1 hfb D''
  let D : DivisorOver ℂ sX := ⟨D₁.Y, D₁.f, hfs ▸ D₁.isNormalVariety, D₁.isBirationalMorphism, D₁.E⟩
  have hv : D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) := by
    change D₁.valuation.comap (functionFieldMap f) = _
    rw [hD₁v, hD''v, hD'₁v]
  refine ⟨D, hv, fun a ha => ?_⟩
  by_cases hex : D''.toDivisorOver.IsExceptional
  · -- KM 3.38
    have hΔ : MMP.Mori.RationalMap.transformDivisor (X := X) f.toRationalMap B =
        MMP.Mori.RationalMap.transformDivisor (X := X') fp.toRationalMap B' := by
      ext Q
      have := Q.isDiscreteValuationRing_localRing
      have hQV : Q.genericPoint ∈ biregularLocus f :=
        MMP.Flips.mem_biregularLocus_of_valuationRing hZ' hXn.1 hfb _
      have hQV' : Q.genericPoint ∈ biregularLocus fp :=
        MMP.Flips.mem_biregularLocus_of_valuationRing hZ' hX'n.1 hfpb _
      obtain ⟨F, hFη, -⟩ := exists_primeDivisor_valuation_eq_of_isBirationalMorphism hZ' f hXn hfb Q
      obtain ⟨F', hF'η, -⟩ :=
        exists_primeDivisor_valuation_eq_of_isBirationalMorphism hZ' fp hX'n hfpb Q
      obtain ⟨F₀, hF₀η, -, hF₀c⟩ :=
        exists_primeDivisor_of_isModificationOf hX hX' hZ' hfs hfps hfb hfpb hsmall hφ B F'
      have hF₀ : F₀ = F :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
          eq_of_map_eq_of_mem_biregularLocus (by rw [hF₀η, hF'η]; exact hQV)
            (hF₀η.trans (hF'η.trans hFη.symm))
      subst hF₀
      rw [DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_apply,
        coeff_transformDivisor_toRationalMap f B hFη hQV,
        coeff_transformDivisor_toRationalMap fp B' hF'η hQV', hB']
      rw [DivisorWithCoeffs.coeff_apply] at hF₀c
      exact hF₀c.symm
    have hE : MMP.Mori.RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E := by
      let E₁ : DivisorOver ℂ sZ' := ⟨D₁.Y, D₁.f ≫ f, hn₁, hb₁, D₁.E⟩
      have hc : E₁.f E₁.E.genericPoint = D''.f D''.E.genericPoint :=
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hZ'.1 hD₁v'
      have : E₁.IsExceptional := by
        rw [isExceptional_iff_two_le_coheight hZ', hc]
        exact (isExceptional_iff_two_le_coheight hZ' _).mp hex
      exact this
    rw [← heq]
    exact MMP.Mori.isDiscrepancy_le_of_isRelativelyNef hX hX' hZ' hfs hfps hfb hfpb hK hK' hΔ
      hN hN' D D'₁ (by rw [hv, hD'₁v]) hE ha ha'₁
  · -- `D'` is a prime divisor of `Z'`
    obtain ⟨Q, hQ⟩ := MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hZ'
      _ hex
    rw [valuation_ofPrimeDivisor] at hQ
    obtain ⟨F, hFη, hFv⟩ := exists_primeDivisor_valuation_eq_of_isBirationalMorphism hZ' f hXn hfb Q
    obtain ⟨F', hF'η, hF'v⟩ :=
      exists_primeDivisor_valuation_eq_of_isBirationalMorphism hZ' fp hX'n hfpb Q
    have hDv : D.valuation = F.divisorialValuation :=
      valuation_eq_of_comap_eq hfb.functionFieldMap_bijective.2
        (by rw [hFv, ← hQ]; exact hD₁v)
    have hD'v : D'₁.valuation = F'.divisorialValuation :=
      valuation_eq_of_comap_eq hfpb.functionFieldMap_bijective.2
        (by rw [hF'v, ← hQ]; exact hD''v.symm)
    obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK
      (DivisorOver.ofPrimeDivisor ℂ hX F)
    obtain ⟨b', hb'⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP'.isPair hK'
      (DivisorOver.ofPrimeDivisor ℂ hX' F')
    have e1 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP
      (hDv.trans (valuation_ofPrimeDivisor hX F).symm) ha hb
    have e2 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hP'
      (hD'v.trans (valuation_ofPrimeDivisor hX' F').symm) ha'₁ hb'
    have e3 := hb.eq_neg_coeff_of_ofPrimeDivisor hX
    have e4 := hb'.eq_neg_coeff_of_ofPrimeDivisor hX'
    have hQV : Q.genericPoint ∈ biregularLocus f := by
      have := Q.isDiscreteValuationRing_localRing
      exact MMP.Flips.mem_biregularLocus_of_valuationRing hZ' hXn.1 hfb _
    obtain ⟨F₀, hF₀η, -, hF₀c⟩ :=
      exists_primeDivisor_of_isModificationOf hX hX' hZ' hfs hfps hfb hfpb hsmall hφ B F'
    have hF₀ : F₀ = F :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
        eq_of_map_eq_of_mem_biregularLocus (by rw [hF₀η, hF'η]; exact hQV)
          (hF₀η.trans (hF'η.trans hFη.symm))
    subst hF₀
    rw [← hB'] at hF₀c
    linarith

/-- An isomorphism has exceptional set of codimension at least two (it is empty). -/
private theorem two_le_closedsCodimension_exceptionalSet_of_isIso {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsIso f] : 2 ≤ closedsCodimension (MMP.Mori.exceptionalSet f) := by
  have hb : biregularLocus f = ⊤ := top_le_iff.mp (le_biregularLocus (by
    change IsIso _; infer_instance))
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  exact absurd (show f x ∈ biregularLocus f by rw [hb]; trivial) (mem_exceptionalSet.mp hx)

/-- **The adjoint of a flipped model is ample over the flipped contraction**, for every canonical
divisor of the flipped model: it is linearly equivalent to the transform of `K_X + B`. -/
private theorem hasRelativelyAmpleMultiple_of_isFlip {X X' Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z} {φ : X.RationalMap X'}
    (hflip : IsFlip ℂ sX sZ sX' (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) f fp φ)
    {n : ℕ} (hK : K.IsCanonicalDivisor sX n) {K' : Divisor X'}
    (hK' : K'.IsCanonicalDivisor sX' n) :
    (Divisor.toQDivisor K' + MMP.Mori.RationalMap.transformDivisor φ B).HasRelativelyAmpleMultiple
      fp := by
  have hX := hflip.isNormalVariety_source
  have hX' := hflip.isNormalVariety_flip
  have hZ := hflip.isNormalVariety_target
  haveI : IsProper f := hflip.isContraction.isProper
  haveI : IsProper fp := hflip.isProper
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  haveI : IsSeparated sX' := hX'.1.toIsSeparated
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sX')
  have h2 := two_le_closedsCodimension_exceptionalSet_of_isSmall hflip.isSmall_source
  have h2' := two_le_closedsCodimension_exceptionalSet_of_isSmall hflip.isSmall
  have htr : MMP.Mori.RationalMap.transformDivisor φ
      (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) =
      QDivisor.toRDivisor (Divisor.toQDivisor (flipTransform f fp K) +
        MMP.Mori.RationalMap.transformDivisor φ B) := by
    rw [transformDivisor_eq_flipTransform_of_small h2 h2' hflip.isModificationOf,
      transformDivisor_eq_flipTransform_of_small h2 h2' hflip.isModificationOf B]
    rw [show flipTransform f fp (QDivisor.toRDivisor (Divisor.toQDivisor K + B)) =
        QDivisor.toRDivisor (flipTransform f fp (Divisor.toQDivisor K + B)) from
      flipTransform_mapCoeffsAddMonoidHom _ _ _ _]
    congr 1
    rw [map_add]
    congr 1
    exact flipTransform_mapCoeffsAddMonoidHom _ _ _ _
  have hamp := hflip.isRelativelyAmple_transform
  rw [htr] at hamp
  have hamp' := hasRelativelyAmpleMultiple_of_isRelativelyAmple hamp
  -- the transform of `K` is a canonical divisor
  have hD : (Divisor.toQDivisor K + B).IsQCartier :=
    MMP.Flips.QDivisor.isQCartier_of_isCartierCombination hflip.isCartierCombination
  have hKf : Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K : Divisor X') := by
    haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
    haveI : IsIso (fp ∣_ biregularLocus f) :=
      hflip.isIso_morphismRestrict_of_disjoint_image_exceptionalSet hD _
        (image_flipsExceptionalSet_disjoint_biregularLocus _)
    have hc := hflip.isContraction.comp_eq
    have hc' := hflip.isSmall.comp_eq
    have hXv : IsNormalVariety ℂ (f ≫ sZ) := by rw [hc]; exact hX
    have hX'v : IsNormalVariety ℂ (fp ≫ sZ) := by rw [hc']; exact hX'
    have hK₀ : K.IsCanonicalDivisor (f ≫ sZ) n := by rw [hc]; exact hK
    have hV := biregularLocus_flip_le_of_isFlip hflip
    have h := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict hZ hXv hX'v
      (MMP.Flips.IsSmall.isBirationalMorphism _ _ hflip.isSmall_source)
      (MMP.Flips.IsSmall.isBirationalMorphism _ _ hflip.isSmall) (biregularLocus f)
      (fun x hx => by
        by_contra hc0
        have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2 x
          (MMP.Mori.mem_exceptionalSet.mpr hc0)
        exact absurd (this.trans hx) (by decide))
      (fun x hx => by
        refine hV ?_
        by_contra hc0
        have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp h2' x
          (MMP.Mori.mem_exceptionalSet.mpr hc0)
        exact absurd (this.trans hx) (by decide)) hK₀
    rwa [hc'] at h
  obtain ⟨ψ, hψ⟩ := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX' hKf hK'
  have := hasRelativelyAmpleMultiple_add_principalDivisor hamp' ψ⁻¹
  convert this using 1
  rw [MMP.Mori.principalDivisor_inv, map_neg, ← hψ, map_sub]
  abel

end StrataModels

/-! ### Crepant models contracting the same curves -/

section SameContractions

universe u

/-- A proper curve is contracted by `u` exactly when its image under `u` is a point. -/
private theorem isContractedBy_iff_exists_range_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) (u : X ⟶ Y) :
    C.IsContractedBy u ↔ ∃ w : Y, Set.range (C.ι ≫ u) = {w} := by
  have hr : Set.range (C.ι ≫ u) = u.base '' closure {C.point} := by
    rw [← ProperCurve.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [hr]
  constructor
  · intro hC
    refine ⟨u C.point, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨C.point, subset_closure rfl, rfl⟩, ?_⟩⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hC x hx
  · rintro ⟨w, hw⟩ x hx
    have h1 : u x ∈ ({w} : Set Y) := hw ▸ ⟨x, hx, rfl⟩
    have h2 : u C.point ∈ ({w} : Set Y) := hw ▸ ⟨C.point, subset_closure rfl, rfl⟩
    exact h1.trans h2.symm

/-- **A curve contracted by one crepant model and not by another.** Let `u : W ⟶ S` and
`u' : W ⟶ S'` be proper birational morphisms of normal varieties over `k` under which `Δ` is the
crepant boundary both of `(S, B)` and of `(S', B')`, with `K_S + B` and `K_{S'} + B'`
`ℚ`-Cartier. If a proper curve `C ⊆ W` is contracted by `u` and by `u' ≫ v'` but not by `u'`,
then there is a proper curve `C''` of `S'` contracted by `v'` with `((K_{S'} + B') · C'') = 0`.
Indeed `u^*(K_S + B)` and `u'^*(K_{S'} + B')` are both of the form `K_W + Δ`, so they have the
same degree on `C`; it is `0` by the projection formula along `u`, and `d ((K_{S'} + B') · u'(C))`
with `d > 0` by the projection formula along `u'`. -/
private theorem exists_intersectionNumber_eq_zero_of_isCrepantBoundary {k : Type u} [Field k]
    [PerfectField k] {W S S' Y : Scheme.{u}} [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S]
    [IsNormal S] [IsIntegral S'] [CompactSpace S'] [IsLocallyNoetherian S'] [IsNormal S']
    {sW : W ⟶ Spec (.of k)} {sS : S ⟶ Spec (.of k)} {sS' : S' ⟶ Spec (.of k)}
    [QuasiCompact sS] [QuasiCompact sS'] (hS : IsNormalVariety k sS)
    (hS' : IsNormalVariety k sS') {u : W ⟶ S} {u' : W ⟶ S'} [IsProper u] [IsProper u']
    (hW : IsNormalVariety k (u ≫ sS)) (hW' : IsNormalVariety k (u' ≫ sS'))
    (hsW : u ≫ sS = sW) (hsW' : u' ≫ sS' = sW)
    (hu : IsBirationalMorphism u) (hu' : IsBirationalMorphism u') {n n' m m' : ℕ}
    {K : Divisor S} {K' : Divisor S'} (hK : K.IsCanonicalDivisor sS m)
    (hK' : K'.IsCanonicalDivisor sS' m') {B : QDivisor S} {B' : QDivisor S'} {Δ : QDivisor W}
    (hΔ : IsCrepantBoundary sS n K B u hW hu Δ) (hΔ' : IsCrepantBoundary sS' n' K' B' u' hW' hu' Δ)
    (hQ : (Divisor.toQDivisor K + B).IsQCartier) (hQ' : (Divisor.toQDivisor K' + B').IsQCartier)
    (v' : S' ⟶ Y) (C : ProperCurve sW) (hC : C.IsContractedBy (u' ≫ v'))
    (hCu : C.IsContractedBy u) (hCu' : ¬ C.IsContractedBy u') :
    ∃ C'' : ProperCurve sS', C''.IsContractedBy v' ∧
      (Divisor.toQDivisor K' + B').intersectionNumber k sS' C''.ι C''.dim_le hQ' = 0 := by
  subst hsW
  have : AlgebraicGeometry.IsVariety k sS := hS.1
  have : AlgebraicGeometry.IsVariety k sS' := hS'.1
  have : AlgebraicGeometry.IsVariety k (u ≫ sS) := hW.1
  have : AlgebraicGeometry.IsVariety k (u' ≫ sS') := hW'.1
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sS' := hS'.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (u ≫ sS) := hW.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (u' ≫ sS') := hW'.1.toLocallyOfFiniteType
  have : QuasiCompact (u ≫ sS) := hW.1.toQuasiCompact
  have : IsDominant u := hu.isDominant
  have : IsDominant u' := hu'.isDominant
  -- the crepant pull-backs `u^*(K_S + B)` and `u'^*(K_{S'} + B')`
  obtain ⟨ω, hω0, hωK⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hS hK
  obtain ⟨ω', hω0', hωK'⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hS' hK'
  have hLB : ∀ Z : irreducibleComponents W, u (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor K + B).supp := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hLB' : ∀ Z : irreducibleComponents W, u' (componentGenericPoint W Z) ∉
      (Divisor.toQDivisor K' + B').supp := fun Z => by
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
    exact MMP.Fourfold.genericPoint_notMem_supp _
  have hpb := MMP.Mori.IsCrepantBoundary.isPullback_divisorOfForm_add hS hW hu hK hΔ hω0 hωK hLB
  have hpb' :=
    MMP.Mori.IsCrepantBoundary.isPullback_divisorOfForm_add hS' hW' hu' hK' hΔ' hω0' hωK' hLB'
  have hA := hpb.isQCartier hQ
  have hA' := hpb'.isQCartier hQ'
  -- the two pulled-back canonical divisors are linearly equivalent
  have hdW : topologicalKrullDim W = m := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (u ≫ sS) hu, hK.1]
  have hdW' : topologicalKrullDim W = m' := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS' (u' ≫ sS') hu',
      hK'.1]
  obtain rfl : m = m' := by exact_mod_cast hdW.symm.trans hdW'
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (u ≫ sS) hW hdW
  have key : ∀ (s : W ⟶ Spec (.of k)) (_ : s = u ≫ sS) [LocallyOfFiniteType s]
      (τ : RationalPluriForms s m 1), τ ≠ 0 → (divisorOfForm τ).LinearlyEquivalent K₀ := by
    rintro s rfl _ τ hτ
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hW hK₀ hτ
    rwa [one_zsmul] at h
  have hl := key _ rfl _ (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' u
    hu.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hK.1) hω0)
  have hl' := key _ hsW' _ (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' u'
    hu'.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hK'.1)
    hω0')
  have hA0 : (Divisor.toQDivisor K₀ + Δ).IsQCartier := hA.add_of_linearlyEquivalent hl
  have e1 := MMP.Mori.QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent (u ≫ sS) C.ι
    C.dim_le hl Δ hA hA0
  have e2 := MMP.Mori.QDivisor.intersectionNumber_add_eq_of_linearlyEquivalent (u ≫ sS) C.ι
    C.dim_le hl' Δ hA' hA0
  -- degree `0` along `u`, degree `d ((K_{S'} + B') · C'')` along `u'`
  have z : (Divisor.toQDivisor (divisorOfForm (pullbackRationalPluriForms sS u ω)) +
      Δ).intersectionNumber k (u ≫ sS) C.ι C.dim_le hA = 0 := by
    have := C.isCurve
    exact MMP.Mori.intersectionNumber_pullback_eq_zero k (u ≫ sS) sS u rfl C.ι hQ hpb
      ((isContractedBy_iff_exists_range_eq C u).mp hCu)
  obtain ⟨d, hd, C'', hC'', heq⟩ := MMP.Mori.QDivisor.exists_intersectionNumber_pullback_eq_mul u'
    hsW' v' hQ' hpb' hA' C hC fun h => hCu' ((isContractedBy_iff_exists_range_eq C u').mpr h)
  refine ⟨C'', hC'', ?_⟩
  have h0 : d * (Divisor.toQDivisor K' + B').intersectionNumber k sS' C''.ι C''.dim_le hQ' = 0 := by
    rw [← heq, e2, ← e1, z]
  exact (mul_eq_zero.mp h0).resolve_left hd.ne'

/-- **Crepant models of opposite signs contract the same curves.** Let `u : W ⟶ S` and
`u' : W ⟶ S'` be proper birational morphisms of normal varieties over `k` under which `Δ` is the
crepant boundary both of `(S, B)` and of `(S', B')`, with `u ≫ v = u' ≫ v'`. If `-(K_S + B)` is
`v`-ample and `K_{S'} + B'` is `v'`-ample, then a proper curve of `W` is contracted by `u` if and
only if it is contracted by `u'`. -/
private theorem isContractedBy_iff_of_isCrepantBoundary {k : Type u} [Field k]
    [PerfectField k] {W S S' Y : Scheme.{u}} [IsIntegral W] [CompactSpace W]
    [IsLocallyNoetherian W] [IsNormal W] [IsIntegral S] [CompactSpace S] [IsLocallyNoetherian S]
    [IsNormal S] [IsIntegral S'] [CompactSpace S'] [IsLocallyNoetherian S'] [IsNormal S']
    {sW : W ⟶ Spec (.of k)} {sS : S ⟶ Spec (.of k)} {sS' : S' ⟶ Spec (.of k)}
    [QuasiCompact sS] [QuasiCompact sS'] (hS : IsNormalVariety k sS)
    (hS' : IsNormalVariety k sS') {u : W ⟶ S} {u' : W ⟶ S'} [IsProper u] [IsProper u']
    (hW : IsNormalVariety k (u ≫ sS)) (hW' : IsNormalVariety k (u' ≫ sS'))
    (hsW : u ≫ sS = sW) (hsW' : u' ≫ sS' = sW)
    (hu : IsBirationalMorphism u) (hu' : IsBirationalMorphism u') {n n' m m' : ℕ}
    {K : Divisor S} {K' : Divisor S'} (hK : K.IsCanonicalDivisor sS m)
    (hK' : K'.IsCanonicalDivisor sS' m') {B : QDivisor S} {B' : QDivisor S'} {Δ : QDivisor W}
    (hΔ : IsCrepantBoundary sS n K B u hW hu Δ) (hΔ' : IsCrepantBoundary sS' n' K' B' u' hW' hu' Δ)
    {v : S ⟶ Y} {v' : S' ⟶ Y} (hvv : u ≫ v = u' ≫ v')
    (hA : (-(Divisor.toQDivisor K + B)).HasRelativelyAmpleMultiple v)
    (hA' : (Divisor.toQDivisor K' + B').HasRelativelyAmpleMultiple v') (C : ProperCurve sW) :
    C.IsContractedBy u ↔ C.IsContractedBy u' := by
  obtain ⟨a, ha, L, hLc, hL, -⟩ := id hA
  obtain ⟨a', ha', L', hLc', hL', -⟩ := id hA'
  have hQn : (-(Divisor.toQDivisor K + B)).IsQCartier :=
    ⟨a, by exact_mod_cast ha.ne', L, hL, hLc⟩
  have hQ : (Divisor.toQDivisor K + B).IsQCartier :=
    ⟨-(a : ℤ), by simpa using ha.ne', L, by rw [hL, smul_neg, neg_smul], hLc⟩
  have hQ' : (Divisor.toQDivisor K' + B').IsQCartier :=
    ⟨a', by exact_mod_cast ha'.ne', L', hL', hLc'⟩
  have hcomp : ∀ {T T' : Scheme.{u}} (g : W ⟶ T) (g' : T ⟶ T'), C.IsContractedBy g →
      C.IsContractedBy (g ≫ g') := fun g g' hg x hx => by
    simp only [Scheme.Hom.comp_apply, hg x hx]
  constructor
  · intro hCu
    by_contra hCu'
    obtain ⟨C'', hC'', h0⟩ := exists_intersectionNumber_eq_zero_of_isCrepantBoundary hS hS' hW hW'
      hsW hsW' hu hu' hK hK' hΔ hΔ' hQ hQ' v' C (hvv ▸ hcomp u v hCu) hCu hCu'
    have := MMP.Mori.QDivisor.HasRelativelyAmpleMultiple.intersectionNumber_pos hA' hQ' C'' hC''
    linarith
  · intro hCu'
    by_contra hCu
    obtain ⟨C'', hC'', h0⟩ := exists_intersectionNumber_eq_zero_of_isCrepantBoundary hS' hS hW' hW
      hsW' hsW hu' hu hK' hK hΔ' hΔ hQ' hQ v C (hvv.symm ▸ hcomp u' v' hCu') hCu' hCu
    have := MMP.Mori.QDivisor.HasRelativelyAmpleMultiple.intersectionNumber_pos hA hQn C'' hC''
    rw [MMP.Mori.QDivisor.intersectionNumber_neg k sS C''.ι C''.dim_le hQ hQn, h0] at this
    linarith

/-- **Two contractions with the same contracted curves are isomorphic.** Let `q : X ⟶ V` and
`q' : X ⟶ V'` be projective surjections of projective `k`-varieties with `𝒪_V = q_* 𝒪_X` and
`𝒪_{V'} = q'_* 𝒪_X`. If `q` and `q'` contract the same proper curves, then `q' = q ≫ φ` for an
isomorphism `φ : V ≅ V'` (by the rigidity lemma
`MMP.Mori.existsUnique_comp_eq_of_isContractedBy`, applied in both directions). -/
private theorem exists_iso_comp_eq_of_isContractedBy_iff {k : Type u} [Field k]
    {X V V' : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sV : V ⟶ Spec (.of k)}
    {sV' : V' ⟶ Spec (.of k)} (hX : MMP.Mori.IsProjectiveVariety k sX)
    (hV : MMP.Mori.IsProjectiveVariety k sV) (hV' : MMP.Mori.IsProjectiveVariety k sV')
    {q : X ⟶ V} {q' : X ⟶ V'} (hq : IsProjectiveMorphism q) (hq' : IsProjectiveMorphism q')
    [Surjective q] [Surjective q'] [IsIso q.c] [IsIso q'.c] (hqV : q ≫ sV = sX)
    (hqV' : q' ≫ sV' = sX)
    (hcurves : ∀ C : ProperCurve sX, C.IsContractedBy q ↔ C.IsContractedBy q') :
    ∃ φ : V ≅ V', q ≫ φ.hom = q' := by
  obtain ⟨φ, hφ, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hX hV hV' hq hqV hqV'
    fun C hC => (hcurves C).mp hC
  obtain ⟨ψ, hψ, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hX hV' hV hq' hqV' hqV
    fun C hC => (hcurves C).mpr hC
  have h1 : φ ≫ ψ = 𝟙 V :=
    (MMP.Mori.existsUnique_comp_eq_of_isContractedBy hX hV hV hq hqV hqV fun C hC => hC).unique
      (by rw [← Category.assoc, hφ, hψ]) (Category.comp_id q)
  have h2 : ψ ≫ φ = 𝟙 V' :=
    (MMP.Mori.existsUnique_comp_eq_of_isContractedBy hX hV' hV' hq' hqV' hqV'
      fun C hC => hC).unique (by rw [← Category.assoc, hψ, hφ]) (Category.comp_id q')
  exact ⟨⟨φ, ψ, h1, h2⟩, hφ⟩

end SameContractions

/-! ### Blocks of the stratum programs -/

section Blocks

/-- A complex pair `(W, B_W)` with a canonical divisor `K_W`, bundled. -/
private structure BlockModel where
  W : Scheme.{0}
  [isIntegral : IsIntegral W]
  [compactSpace : CompactSpace W]
  [isLocallyNoetherian : IsLocallyNoetherian W]
  [isNormal : IsNormal W]
  sW : W ⟶ Spec (.of ℂ)
  K : Divisor W
  B : QDivisor W

attribute [local instance] BlockModel.isIntegral BlockModel.compactSpace
  BlockModel.isLocallyNoetherian BlockModel.isNormal

/-- A bundled pair is a projective `ℚ`-factorial dlt pair with canonical divisor `K_W`. -/
private structure BlockModel.IsAbsModel (M : BlockModel) : Prop where
  isProjectiveVariety : MMP.Mori.IsProjectiveVariety ℂ M.sW
  isQFactorial : IsQFactorial M.sW
  isCanonicalDivisor : ∃ m : ℕ, M.K.IsCanonicalDivisor M.sW m
  isDltPair : MMP.Intersection.IsDltPair M.sW M.B

/-- An elementary dlt step over the point from one bundled pair to another. -/
private def BlockModel.IsAbsStep (M M' : BlockModel) : Prop :=
  ∃ (R : Set (RelativeNumericalCurveClasses M.sW M.sW)) (Z : Scheme.{0})
    (sZ : Z ⟶ Spec (.of ℂ)) (f : M.W ⟶ Z) (g : Z ⟶ Spec (.of ℂ)) (fp : M'.W ⟶ Z)
    (φ : M.W.RationalMap M'.W),
    IsElementaryDltStep M.sW M.sW sZ M'.sW M'.sW M.K M.B R f g fp φ ∧
      M'.B = MMP.Mori.RationalMap.transformDivisor φ M.B

/-- The adjoint `K_W + B_W` of a bundled pair is nef over `π`. -/
private def BlockModel.IsNefOver (M : BlockModel) {Y : Scheme.{0}} (π : M.W ⟶ Y) : Prop :=
  MMP.Flips.IsRelativelyNef ℂ M.sW π (QDivisor.toRDivisor (Divisor.toQDivisor M.K + M.B))

/-! #### Steps over a projective base are steps over the point -/

/-- The point `Spec ℂ` is a projective variety. -/
private theorem isProjectiveVariety_spec : MMP.Mori.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
  (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
    ⟨by constructor <;> infer_instance, isProjectiveMorphism_id _⟩

/-- A curve contracted by `f` is contracted by `f ≫ h`. -/
private theorem isContractedBy_comp' {X Y W : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {C : ProperCurve sX} {f : X ⟶ Y} (h : Y ⟶ W) (hC : C.IsContractedBy f) :
    C.IsContractedBy (f ≫ h) := fun x hx => by
  simp only [Scheme.Hom.comp_apply, hC x hx]

/-- The natural map sends the relative class of a contracted curve to its class. -/
private theorem relativeToAbsolute_relativeClass' {X S : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (π : X ⟶ S) (C : ProperCurve sX) (hC : C.IsContractedBy π) :
    relativeToAbsolute sX π (C.relativeClass π hC) = OneCycle.numericalClass sX (C.cycle ℝ) :=
  isNaturalRelativeMap_relativeToAbsolute sX π ⟨C.cycle ℝ, C.cycle_mem_relativeOneCycles hC⟩

/-- The natural map `N₁(X/S) → N₁(X)` is injective. -/
private theorem relativeToAbsolute_injective' {X S : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (π : X ⟶ S) : Function.Injective (relativeToAbsolute sX π) :=
  (MMP.Mori.existsUnique_isNaturalRelativeMap_and_injective sX π).2 _
    (isNaturalRelativeMap_relativeToAbsolute sX π)

/-- Over the point, the natural map `N₁(X / Spec ℂ) → N₁(X)` is surjective. -/
private theorem relativeToAbsolute_surjective_self {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    Function.Surjective (relativeToAbsolute sX sX) := fun z => by
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX z
  have hZ : Z ∈ relativeOneCycles sX sX :=
    (Finsupp.mem_supported ℝ Z).mpr fun C _ => fun _ _ => Subsingleton.elim _ _
  exact ⟨relativeNumericalClass sX sX ⟨Z, hZ⟩,
    isNaturalRelativeMap_relativeToAbsolute sX sX ⟨Z, hZ⟩⟩

/-- Let `φ : W → V` be injective and linear, and `A ⊆ W` with `φ(A) = N ∩ φ(W)`. The preimage
of an extremal ray `R ⊆ φ(W)` of `N` is an extremal ray of `A`. -/
private theorem isExtremalRay_preimage' {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (φ : W →ₗ[ℝ] V) (hφ : Function.Injective φ) {A : Set W}
    {N R : Set V} (hA : φ '' A = N ∩ Set.range φ) (hR : IsExtremalRay ℝ N R)
    (hRr : R ⊆ Set.range φ) : IsExtremalRay ℝ A (φ ⁻¹' R) := by
  obtain ⟨⟨hRN, ⟨hR0, hRs⟩, hRadd, hRext⟩, v, hv0, hRv⟩ := hR
  have hAN : ∀ a ∈ A, φ a ∈ N := fun a ha =>
    (show φ a ∈ N ∩ Set.range φ from hA ▸ Set.mem_image_of_mem φ ha).1
  have hvR : v ∈ R := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
  obtain ⟨v', rfl⟩ := hRr hvR
  refine ⟨⟨fun x hx => ?_, ⟨?_, fun x hx c hc => ?_⟩, fun x hx y hy => ?_,
    fun x hx y hy hxy => ?_⟩, v', fun h => hv0 (by rw [h, map_zero]), ?_⟩
  · obtain ⟨a, ha, hax⟩ : φ x ∈ φ '' A := hA ▸ ⟨hRN hx, x, rfl⟩
    rwa [← hφ hax]
  · show φ 0 ∈ R
    rwa [map_zero]
  · show φ (c • x) ∈ R
    rw [map_smul]; exact hRs _ hx c hc
  · show φ (x + y) ∈ R
    rw [map_add]; exact hRadd _ hx _ hy
  · have hxy' : φ x + φ y ∈ R := by rw [← map_add]; exact hxy
    exact hRext _ (hAN x hx) _ (hAN y hy) hxy'
  · ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [hRv]
    constructor
    · rintro ⟨c, hc, h⟩
      exact ⟨c, hc, hφ (by rw [map_smul, h])⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, (map_smul _ _ _).symm⟩

/-- The pull-back of an invertible sheaf of the base has degree zero on the image of every
relative curve class. -/
private theorem degree_pullback_relativeToAbsolute_eq_zero {X S : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} [IsSeparated sS] [LocallyOfFiniteType sS]
    (π : X ⟶ S) (hπ : π ≫ sS = sX) (H : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 H]
    (z : RelativeNumericalCurveClasses sX π) :
    NumericalCurveClasses.degree sX ((Scheme.Modules.pullback π).obj H)
      (relativeToAbsolute sX π z) = 0 := by
  classical
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX π z
  rw [isNaturalRelativeMap_relativeToAbsolute sX π Z, NumericalCurveClasses.degree_numericalClass,
    OneCycle.degree_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun C hC => ?_
  have hCπ : C.IsContractedBy π :=
    (Finsupp.mem_supported ℝ (Z : OneCycle ℝ sX)).mp Z.2 hC
  rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy π hπ C hCπ H]
  simp

/-- **An elementary dlt step over a projective base is one over the point.** The ray `R` of
`NE̅(W/Z)` maps to an extremal ray of `NE̅(W)` (`MMP.Mori.isExtremalRay_image_relativeToAbsolute`),
which is the image of an extremal ray of `NE̅(W / Spec ℂ)`; a curve with class in it is contracted
by `W ⟶ Z`, its degree against the pull-back of an ample sheaf of `Z` being zero. -/
private theorem BlockModel.isAbsStep_of_isElementaryDltStep {M M' : BlockModel}
    (hM : M.IsAbsModel) {Z Z' : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {π : M.W ⟶ Z} (hπ : π ≫ sZ = M.sW)
    {π' : M'.W ⟶ Z} (hπ' : π' ≫ sZ = M'.sW) {R : Set (RelativeNumericalCurveClasses M.sW π)}
    {sZ' : Z' ⟶ Spec (.of ℂ)} {f : M.W ⟶ Z'} {g : Z' ⟶ Z} {fp : M'.W ⟶ Z'}
    {φ : M.W.RationalMap M'.W}
    (hst : IsElementaryDltStep M.sW π sZ' M'.sW π' M.K M.B R f g fp φ)
    (hB : M'.B = MMP.Mori.RationalMap.transformDivisor φ M.B) : M.IsAbsStep M' := by
  classical
  have hW := hM.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ M.sW := hW
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) := isProjectiveVariety_spec
  haveI : IsSeparated sZ := hZ.toIsVariety.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.toIsVariety.toLocallyOfFiniteType
  obtain ⟨⟨⟨hq, hray, hneg⟩, hface, hnec⟩, hcomp, hdiv⟩ := hst
  set φZ := relativeToAbsolute M.sW π
  set φP := relativeToAbsolute M.sW M.sW
  have hφPinj := relativeToAbsolute_injective' M.sW M.sW
  have hφZinj := relativeToAbsolute_injective' M.sW π
  set Rpt := φP ⁻¹' (φZ '' R)
  have hrayA := isExtremalRay_image_relativeToAbsolute M.sW sZ π hπ hray
  have hrayP : IsExtremalRay ℝ (relativeClosedConeOfCurves M.sW M.sW : Set _) Rpt :=
    isExtremalRay_preimage' φP hφPinj
      (image_relativeClosedConeOfCurves_eq_inter_range M.sW (𝟙 _) M.sW (Category.comp_id _))
      hrayA fun u _ => relativeToAbsolute_surjective_self M.sW u
  have hnegP : ∀ u ∈ Rpt, u ≠ 0 →
      QDivisor.relativeCurveForm M.sW M.sW (Divisor.toQDivisor M.K + M.B) hq u < 0 := by
    intro u hu hu0
    obtain ⟨r, hr, hru⟩ := hu
    have hr0 : r ≠ 0 := fun h => hu0 (hφPinj (by
      change φP u = φP 0
      rw [← hru, h, map_zero, map_zero]))
    have h1 := hneg r hr hr0
    rw [MMP.Mori.QDivisor.relativeCurveForm_eq_comp] at h1 ⊢
    simp only [LinearMap.comp_apply] at h1 ⊢
    change _ < 0
    rw [show φP u = φZ r from hru.symm]
    exact h1
  obtain ⟨H, hHinv, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
  have hcontr : ∀ (C : ProperCurve M.sW) (hC : C.IsContractedBy M.sW),
      C.IsContractedBy f ↔ C.relativeClass M.sW hC ∈ Rpt := by
    intro C hC
    have hcls : φP (C.relativeClass M.sW hC) = OneCycle.numericalClass M.sW (C.cycle ℝ) :=
      relativeToAbsolute_relativeClass' M.sW M.sW C hC
    constructor
    · intro hCf
      have hCπ : C.IsContractedBy π := hface.comp_eq ▸ isContractedBy_comp' g hCf
      refine ⟨C.relativeClass π hCπ, (hface.isContractedBy_iff C hCπ).mp hCf, ?_⟩
      rw [hcls]
      exact relativeToAbsolute_relativeClass' M.sW π C hCπ
    · rintro ⟨r, hr, hrC⟩
      rw [hcls] at hrC
      have hCπ : C.IsContractedBy π := by
        refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero π hπ H hHa C ?_
        have h0 := degree_pullback_relativeToAbsolute_eq_zero π hπ H r
        change NumericalCurveClasses.degree M.sW _ (φZ r) = 0 at h0
        rw [hrC, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle] at h0
        exact_mod_cast h0
      refine (hface.isContractedBy_iff C hCπ).mpr ?_
      rwa [← hφZinj (hrC.trans (relativeToAbsolute_relativeClass' M.sW π C hCπ).symm)]
  refine ⟨Rpt, Z', sZ', f, g ≫ sZ, fp, φ, ⟨⟨⟨hq, hrayP, hnegP⟩,
    ⟨hrayP.1, hface.isProjectiveMorphism.comp hZ.isProjective,
      by rw [← Category.assoc, hface.comp_eq, hπ], hface.isIso_app, hcontr⟩, hnec⟩,
    by rw [← Category.assoc, hcomp, hπ'], hdiv⟩, hB⟩

/-- **`P₃` forbids an infinite sequence of elementary dlt steps over the point** starting from a
projective `ℚ`-factorial dlt pair of dimension at most three: the steps form a projective
elementary dlt program over `Spec ℂ` with infinitely many steps. -/
private theorem false_of_forall_isAbsStep (hP : ProjectiveLowerLogMMP 3) (M : ℕ → BlockModel)
    (hM : ∀ t, (M t).IsAbsModel) (hdim : topologicalKrullDim (M 0).W ≤ 3)
    (hstep : ∀ t, (M t).IsAbsStep (M (t + 1))) : False := by
  classical
  choose R Zf sZf ff gf fpf φf hst hBe using hstep
  let Yi : ℕ → Scheme.{0} := fun i => (M (i + 1)).W
  let sYi : ∀ i, Yi i ⟶ Spec (.of ℂ) := fun i => (M (i + 1)).sW
  let KYi : ∀ i, Divisor (Yi i) := fun i => (M (i + 1)).K
  let BYi : ∀ i, QDivisor (Yi i) := fun i => (M (i + 1)).B
  have hrel : ∀ t, IsRelativeDltModel (M t).sW (𝟙 (Spec (.of ℂ))) (M t).sW (M t).K (M t).B :=
    fun t => by
      have hX := (hM t).isProjectiveVariety
      haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (M t).sW := hX
      haveI : AlgebraicGeometry.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
        isProjectiveVariety_spec
      exact ⟨AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _,
        AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ _, Category.comp_id _,
        hX.isProjective, (hM t).isQFactorial, (hM t).isCanonicalDivisor, (hM t).isDltPair⟩
  let P : RelativeDltProgram (M 0).sW (𝟙 (Spec (.of ℂ))) (M 0).sW (M 0).K (M 0).B :=
    { n := ⊤
      Y := Yi
      sY := sYi
      isIntegral := fun i => (M (i + 1)).isIntegral
      compactSpace := fun i => (M (i + 1)).compactSpace
      isLocallyNoetherian := fun i => (M (i + 1)).isLocallyNoetherian
      isNormal := fun i => (M (i + 1)).isNormal
      πY := sYi
      KY := KYi
      BY := BYi
      R := fun i => match i with
        | 0 => R 0
        | j + 1 => R (j + 1)
      Z := Zf
      sZ := sZf
      f := fun i => match i with
        | 0 => ff 0
        | j + 1 => ff (j + 1)
      gZ := gf
      fp := fpf
      φ := fun i => match i with
        | 0 => φf 0
        | j + 1 => φf (j + 1)
      isRelativeDltModel := fun i _ => match i with
        | 0 => hrel 0
        | j + 1 => hrel (j + 1)
      isElementaryDltStep := fun i _ => match i with
        | 0 => hst 0
        | j + 1 => hst (j + 1)
      BY_eq := fun i _ => match i with
        | 0 => hBe 0
        | j + 1 => hBe (j + 1)
      hasFinal := False
      finalRay := ∅
      T := Spec (.of ℂ)
      sT := 𝟙 _
      gT := 𝟙 _
      g := modelStr (M 0).sW sYi _
      final_spec := fun h => h.elim }
  have hProj : P.IsProjective := ⟨isProjectiveVariety_spec, fun i _ => match i with
    | 0 => (hM 0).isProjectiveVariety
    | j + 1 => (hM (j + 1)).isProjectiveVariety⟩
  exact ((hP.2 (M 0).W (Spec (.of ℂ)) (M 0).sW (𝟙 _) (M 0).sW (M 0).K (M 0).B
    (hM 0).isProjectiveVariety isProjectiveVariety_spec (Category.comp_id _) hdim
    (hM 0).isQFactorial
    (hM 0).isCanonicalDivisor (hM 0).isDltPair).2.1 P hProj) rfl

variable {X Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)]
  [∀ i, IsNormal (X i)] [∀ i, CompactSpace (X i)]
  {S : ℕ → Scheme.{0}} [∀ i, IsIntegral (S i)] [∀ i, IsLocallyNoetherian (S i)]
  [∀ i, IsNormal (S i)]

/-- `p : W ⟶ S_i` is a *crepant model* of the adjunction pair `(S_i, B_{S_i})`: `(W, B_W)` is a
projective `ℚ`-factorial dlt pair of the dimension of `S_i`, `p` is proper and birational, and
`B_W` is the crepant boundary of `(S_i, B_{S_i})`. -/
private def IsCrepantOver (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (ι : ∀ i, S i ⟶ X i)
    (BS : ∀ i, QDivisor (S i)) (i : ℕ) (M : BlockModel) (p : M.W ⟶ S i) : Prop :=
  M.IsAbsModel ∧ p ≫ ι i ≫ sX i = M.sW ∧ topologicalKrullDim M.W = topologicalKrullDim (S i) ∧
    IsProper p ∧ ∃ hb : IsBirationalMorphism p, ∃ (n : ℕ) (KS : Divisor (S i))
      (hU : IsNormalVariety ℂ (p ≫ ι i ≫ sX i)),
      (∃ m : ℕ, KS.IsCanonicalDivisor (ι i ≫ sX i) m) ∧
        IsCrepantBoundary (ι i ≫ sX i) n KS (BS i) p hU hb M.B

/-- `(W, B_W)` over `Z_i` (by `π`) is *reached in block `i`*: it is a crepant model of
`(S_i, B_{S_i})` over `Z_i`, or it is obtained from a pair reached in block `i` by an elementary
dlt step over `Z_i` to a projective `ℚ`-factorial dlt pair. -/
private inductive IsReachedOver (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (ι : ∀ i, S i ⟶ X i) (BS : ∀ i, QDivisor (S i)) (i : ℕ) :
    (M : BlockModel) → (M.W ⟶ Z i) → Prop
  | start (M : BlockModel) (p : M.W ⟶ S i) : IsCrepantOver sX ι BS i M p →
      IsReachedOver sX sZ f ι BS i M (p ≫ ι i ≫ f i)
  | step (M M' : BlockModel) (π : M.W ⟶ Z i) (π' : M'.W ⟶ Z i)
      (R : Set (RelativeNumericalCurveClasses M.sW π)) (Z' : Scheme.{0})
      (sZ' : Z' ⟶ Spec (.of ℂ)) (f' : M.W ⟶ Z') (g' : Z' ⟶ Z i) (fp' : M'.W ⟶ Z')
      (φ' : M.W.RationalMap M'.W) : IsReachedOver sX sZ f ι BS i M π →
      IsElementaryDltStep M.sW π sZ' M'.sW π' M.K M.B R f' g' fp' φ' →
      M'.B = MMP.Mori.RationalMap.transformDivisor φ' M.B → M'.IsAbsModel →
      π' ≫ sZ i = M'.sW → IsProjectiveMorphism π' → IsReachedOver sX sZ f ι BS i M' π'

/-- A pair reached in a block is a projective `ℚ`-factorial dlt pair. -/
private theorem IsReachedOver.isAbsModel {sX : ∀ i, X i ⟶ Spec (.of ℂ)}
    {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)} {f : ∀ i, X i ⟶ Z i} {ι : ∀ i, S i ⟶ X i}
    {BS : ∀ i, QDivisor (S i)} {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (h : IsReachedOver sX sZ f ι BS i M π) : M.IsAbsModel := by
  cases h with
  | start M p hp => exact hp.1
  | step M₀ M π₀ π R Z' sZ' f' g' fp' φ' _ _ _ hM _ _ => exact hM

variable {sX : ∀ i, X i ⟶ Spec (.of ℂ)} {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)}
  {f : ∀ i, X i ⟶ Z i} {fp : ∀ i, X (i + 1) ⟶ Z i}
  {K : ∀ i, Divisor (X i)} {B : ∀ i, QDivisor (X i)}
  {ι : ∀ i, S i ⟶ X i} {BS : ∀ i, QDivisor (S i)}

/-- The hypotheses on a chain of corresponding `d`-dimensional adjunction strata along a family
of flips of projective dlt fourfolds, after the stabilization of the divisors on the strata
(`MMP.Fourfold.exists_forall_ge_isStratumAdjunctionPair_coeff_eq`): the positive sides of the
stratum diagrams are small, and corresponding prime divisors have the same coefficients. -/
private structure IsStabilizedChain (sX : ∀ i, X i ⟶ Spec (.of ℂ))
    (sZ : ∀ i, Z i ⟶ Spec (.of ℂ)) (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (K : ∀ i, Divisor (X i)) (B : ∀ i, QDivisor (X i)) (d : ℕ) (ι : ∀ i, S i ⟶ X i)
    (BS : ∀ i, QDivisor (S i)) : Prop where
  isProjectiveVariety : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i)
  isProjectiveVariety_base : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sZ i)
  isDltPair : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i)
  isCanonicalDivisor : ∀ i, (K i).IsCanonicalDivisor (sX i) 4
  isFlipOf : ∀ i,
    IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i)
  boundary_succ : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i)
  pos_sign : ∀ i, ∃ K' : Divisor (X (i + 1)), K'.IsCanonicalDivisor (sX (i + 1)) 4 ∧
    (Divisor.toQDivisor K' + B (i + 1)).HasRelativelyAmpleMultiple (fp i)
  one_le : 1 ≤ d
  le_three : d ≤ 3
  isStratumAdjunctionPair : ∀ i, IsStratumAdjunctionPair (sX i) (B i) (ι i) (BS i)
  isDltStratum : ∀ i, IsDltStratum (sX i) (B i) (Set.range (ι i).base)
  dim_eq : ∀ i, topologicalKrullDim (S i) = d
  corr : ∀ i,
    (ι i ≫ f i).base (genericPoint (S i)) = (ι (i + 1) ≫ fp i).base (genericPoint (S (i + 1)))
  not_subset : ∀ i, ¬ Set.range (ι i).base ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i))
  not_subset' : ∀ i,
    ¬ Set.range (ι (i + 1)).base ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1)))
  all_not_subset : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T →
    ¬ T ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i))
  all_not_subset' : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
    ¬ T' ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1)))
  small : ∀ i (P : MMP.Mori.PrimeDivisor (S (i + 1))),
    ¬ topologicalKrullDim (closure {(ι (i + 1) ≫ fp i).base P.genericPoint} : Set (Z i)) <
      topologicalKrullDim (closure {P.genericPoint} : Set (S (i + 1)))
  coeff_eq : ∀ i (P : MMP.Mori.PrimeDivisor (S i)) (P' : MMP.Mori.PrimeDivisor (S (i + 1))),
    P.divisorialValuation.comap ((ι i ≫ f i).stalkMap (genericPoint (S i))).hom =
      P'.divisorialValuation.comap
        (((Z i).presheaf.stalkCongr (.of_eq (corr i))).hom ≫
          (ι (i + 1) ≫ fp i).stalkMap (genericPoint (S (i + 1)))).hom →
    (BS i).coeff P = (BS (i + 1)).coeff P'

/-- **The negative adjoint sign on `S_i`.** The adjoint `K_{S_i} + B_{S_i}` of the stratum on the
negative side is anti-ample over `Z_i`: it is the restriction of the `f_i`-anti-ample
`K_{X_i} + B_i` (`StratumAdjunctionData.exists_adjoint_hasRelativelyAmpleMultiple`). -/
private theorem IsStabilizedChain.exists_adjoint_neg {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) (i : ℕ) [CompactSpace (S i)] :
    ∃ KS : Divisor (S i), KS.IsCanonicalDivisor (ι i ≫ sX i) d ∧
      (-(Divisor.toQDivisor KS + BS i)).HasRelativelyAmpleMultiple (ι i ≫ f i) := by
  have F := (hC.isStratumAdjunctionPair i).some
  haveI : QuasiCompact (f i) := by
    haveI : IsProper (f i) :=
      isProper_of_isProjectiveMorphism _ (hC.isFlipOf i).isContraction.isProjectiveMorphism
    infer_instance
  have hamp := (hC.isFlipOf i).hasRelativelyAmpleMultiple
  rw [← neg_one_smul ℤ] at hamp
  obtain ⟨KS, hKS, hKSa⟩ := StratumAdjunctionData.exists_adjoint_hasRelativelyAmpleMultiple
    (hC.isCanonicalDivisor i) (-1) (Or.inr rfl) hamp F d (hC.dim_eq i) hC.one_le
  exact ⟨KS, hKS, by rwa [neg_one_smul] at hKSa⟩

/-- **The positive adjoint sign on `S_{i+1}`.** The adjoint of the stratum on the positive side
is ample over `Z_i`: it is the restriction of the `f_i⁺`-ample `K_{X_{i+1}} + B_{i+1}`. -/
private theorem IsStabilizedChain.exists_adjoint_pos {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) (i : ℕ) [CompactSpace (S (i + 1))] :
    ∃ KS : Divisor (S (i + 1)), KS.IsCanonicalDivisor (ι (i + 1) ≫ sX (i + 1)) d ∧
      (Divisor.toQDivisor KS + BS (i + 1)).HasRelativelyAmpleMultiple (ι (i + 1) ≫ fp i) := by
  have F := (hC.isStratumAdjunctionPair (i + 1)).some
  haveI : QuasiCompact (fp i) := by
    haveI := (hC.isFlipOf i).isSmallMorphism_flip.isProper
    infer_instance
  obtain ⟨K', hK', hamp⟩ := hC.pos_sign i
  rw [← one_smul ℤ (Divisor.toQDivisor K' + B (i + 1))] at hamp
  obtain ⟨KS, hKS, hKSa⟩ := StratumAdjunctionData.exists_adjoint_hasRelativelyAmpleMultiple
    hK' 1 (Or.inl rfl) hamp F d (hC.dim_eq (i + 1)) hC.one_le
  exact ⟨KS, hKS, by rwa [one_smul] at hKSa⟩

/-- The strata of a stabilized chain are projective varieties. -/
private theorem IsStabilizedChain.isProjectiveVariety_stratum {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) (i : ℕ) :
    MMP.Mori.IsProjectiveVariety ℂ (ι i ≫ sX i) := by
  have F := (hC.isStratumAdjunctionPair i).some
  haveI : IsClosedImmersion (ι i) := F.isClosedImmersion
  refine (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr ⟨F.isNormalVariety.1, ?_⟩
  obtain ⟨n, j, hj, h⟩ := (hC.isProjectiveVariety i).isProjective
  haveI := hj
  exact ⟨n, ι i ≫ j, inferInstance, by rw [Category.assoc, h]⟩

/-- **Crepant models exist** (`MMP.Fourfold.ProjectiveLowerLogMMP.exists_isCrepantDltLift`). -/
private theorem IsStabilizedChain.exists_isCrepantOver (hP : ProjectiveLowerLogMMP 3) {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) (i : ℕ) :
    ∃ (M : BlockModel) (p : M.W ⟶ S i), IsCrepantOver sX ι BS i M p := by
  have F := (hC.isStratumAdjunctionPair i).some
  have hn := F.isNormalVariety
  haveI : IsClosedImmersion (ι i) := F.isClosedImmersion
  haveI : CompactSpace (S i) := (ι i).isClosedEmbedding.compactSpace
  haveI : AlgebraicGeometry.IsVariety ℂ (ι i ≫ sX i) := hn.1
  have hSproj := hC.isProjectiveVariety_stratum i
  obtain ⟨KS, hKS⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (ι i ≫ sX i) hn
    (hC.dim_eq i)
  have hdlt := (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair
    (hC.isDltStratum i)).1.2 F rfl
  have hd3 : topologicalKrullDim (S i) ≤ 3 := by
    rw [hC.dim_eq i]; exact_mod_cast hC.le_three
  obtain ⟨U, _, _, _, _, p, Δ, hlift, hUproj⟩ :=
    ProjectiveLowerLogMMP.exists_isCrepantDltLift hP (ι i ≫ sX i) hSproj hd3 KS ⟨d, hKS⟩ (BS i)
      hdlt
  have hUn : IsNormalVariety ℂ (p ≫ ι i ≫ sX i) := hlift.isQFactorial.1
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ ι i ≫ sX i) := hUn.1
  have hdimU : topologicalKrullDim U = topologicalKrullDim (S i) :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ι i ≫ sX i) (p ≫ ι i ≫ sX i)
      hlift.isBirationalMorphism).symm
  obtain ⟨KU, hKU⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety (p ≫ ι i ≫ sX i)
    hUn (hdimU.trans (hC.dim_eq i))
  obtain ⟨n, hcrep⟩ := hlift.isCrepantBoundary
  refine ⟨⟨U, p ≫ ι i ≫ sX i, KU, Δ⟩, p, ⟨⟨hUproj, hlift.isQFactorial, ⟨d, hKU⟩,
    hlift.isDltPair⟩, rfl, hdimU, isProper_of_isProjectiveMorphism _ hlift.isProjectiveMorphism,
    hlift.isBirationalMorphism, n, KS, hUn, ⟨d, hKS⟩, hcrep⟩⟩

/-- The `k`-th model of a program from a bundled pair, bundled. -/
private noncomputable def BlockModel.ofProgram {M : BlockModel} {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} {π : M.W ⟶ Y} (P : RelativeDltProgram M.sW sY π M.K M.B) (k : ℕ) :
    BlockModel :=
  ⟨modelSeq M.W P.Y k, modelStr M.sW P.sY k, divisorSeq M.K P.KY k, divisorSeq M.B P.BY k⟩

/-- **The models of a program over `Z_i` from a pair reached in block `i` are reached in block
`i`.** -/
private theorem IsReachedOver.of_program {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (h : IsReachedOver sX sZ f ι BS i M π) (P : RelativeDltProgram M.sW (sZ i) π M.K M.B)
    (hP : P.IsProjective) :
    ∀ k : ℕ, (k : ℕ∞) ≤ P.n →
      IsReachedOver sX sZ f ι BS i (BlockModel.ofProgram P k) (modelMap π P.πY k)
  | 0, _ => h
  | k + 1, hk => by
    have hlt : (k : ℕ∞) < P.n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self k) hk
    have hrel := P.isRelativeDltModel (k + 1) hk
    exact IsReachedOver.step (BlockModel.ofProgram P k) (BlockModel.ofProgram P (k + 1))
      (modelMap π P.πY k) (P.πY k) (P.R k) (P.Z k) (P.sZ k) (P.f k) (P.gZ k) (P.fp k) (P.φ k)
      (IsReachedOver.of_program h P hP k hlt.le) (P.isElementaryDltStep k hlt) (P.BY_eq k hlt)
      ⟨hP.2 (k + 1) hk, hrel.isQFactorial, hrel.isCanonicalDivisor, hrel.isDltPair⟩
      hrel.comp_eq hrel.isProjectiveMorphism

/-- A proper morphism between projective varieties is projective (Stacks 0B45). -/
private theorem isProjectiveMorphism_of_isProper_of_isProjectiveVariety {V Y : Scheme.{0}}
    {sV : V ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)} (hV : MMP.Mori.IsProjectiveVariety ℂ sV)
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (p : V ⟶ Y) [IsProper p] :
    IsProjectiveMorphism p := by
  have h := (isProjective_tfae_seven_of_exists_isAmple p
    (exists_isAmple_of_isProjectiveVariety hY)).out 5 2
  exact h.mp ⟨inferInstance, exists_isAmple_of_isProjectiveVariety hV⟩

/-- The invariants of a pair reached in block `i`: its structure morphism is `π ≫ s_{Z_i}`, `π`
is projective, the generic point maps to that of `ι_i(S_i)`, and it has the dimension of `S_i`. -/
private theorem IsStabilizedChain.invariants_of_isReachedOver {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (h : IsReachedOver sX sZ f ι BS i M π) :
    π ≫ sZ i = M.sW ∧ IsProjectiveMorphism π ∧
      π (genericPoint M.W) = (ι i ≫ f i) (genericPoint (S i)) ∧
      topologicalKrullDim M.W = topologicalKrullDim (S i) := by
  induction h with
  | start M p hp =>
    obtain ⟨hAbs, hcomp, hdim, hprop, hb, -⟩ := hp
    haveI := hprop
    haveI : IsClosedImmersion (ι i) := (hC.isStratumAdjunctionPair i).some.isClosedImmersion
    haveI : IsProper (f i) :=
      isProper_of_isProjectiveMorphism _ (hC.isFlipOf i).isContraction.isProjectiveMorphism
    have hfZ : f i ≫ sZ i = sX i := (hC.isFlipOf i).isContraction.comp_eq
    refine ⟨by rw [Category.assoc, Category.assoc, hfZ, hcomp], ?_, ?_, hdim⟩
    · exact isProjectiveMorphism_of_isProper_of_isProjectiveVariety hAbs.isProjectiveVariety
        (hC.isProjectiveVariety_base i) _
    · haveI := hb.isDominant
      rw [Scheme.Hom.comp_apply, map_genericPoint_of_isDominant p]
  | step M M' π π' R Z' sZ' f' g' fp' φ' hr hst hBe hAbs' hcomp' hproj' ih =>
    obtain ⟨hcomp, -, hgen, hdim⟩ := ih
    have hAbs := hr.isAbsModel
    have hnec := hst.isNegativeRelativeRayContraction.isNegativeExtremalContraction
    have hZ'v := hnec.isNormalVariety_target
    haveI : IsIntegral Z' := hZ'v.1.toIsIntegral
    haveI : AlgebraicGeometry.IsVariety ℂ sZ' := hZ'v.1
    haveI : AlgebraicGeometry.IsVariety ℂ M.sW := hAbs.isProjectiveVariety.toIsVariety
    haveI : AlgebraicGeometry.IsVariety ℂ M'.sW := hAbs'.isProjectiveVariety.toIsVariety
    have hbir : IsBirationalMorphism f' ∧ IsBirationalMorphism fp' := by
      rcases hst.divisorial_or_flip with ⟨hb, -, hiso, -⟩ | hflip
      · exact ⟨hb, isBirationalMorphism_of_isIso _⟩
      · exact ⟨MMP.Flips.IsSmall.isBirationalMorphism _ _ hflip.isSmall_source,
          MMP.Flips.IsSmall.isBirationalMorphism _ _ hflip.isSmall⟩
    have hfg : f' ≫ g' = π :=
      hst.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
    have hfpg : fp' ≫ g' = π' := hst.comp_eq
    refine ⟨hcomp', hproj', ?_, ?_⟩
    · haveI := hbir.1.isDominant
      haveI := hbir.2.isDominant
      rw [← hgen, ← hfg, ← hfpg, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
        map_genericPoint_of_isDominant f', map_genericPoint_of_isDominant fp']
    · rw [← hdim,
        ← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ' M.sW hbir.1,
        MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ' M'.sW hbir.2]

/-- Two morphisms `Z ⟶ Spec R` agreeing after `f : X ⟶ Z` agree, when `f` induces an isomorphism
`Γ(Z, 𝒪_Z) ≅ Γ(X, 𝒪_X)`: morphisms into an affine scheme are ring maps into global sections. -/
private theorem eq_of_comp_eq_of_isIso_appTop' {X Z : Scheme.{0}} {R : CommRingCat.{0}}
    (f : X ⟶ Z) [IsIso f.appTop] {a b : Z ⟶ Spec R} (h : f ≫ a = f ≫ b) : a = b := by
  apply (ΓSpec.adjunction.homEquiv Z (Opposite.op R)).symm.injective
  have h' := congrArg (ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm h
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm] at h'
  have : IsIso (Scheme.Γ.rightOp.map f) := by
    change IsIso (f.appTop).op
    infer_instance
  exact (cancel_epi _).mp h'

/-- **No fibre-type contraction over `Z_i`.** A pair reached in block `i` maps birationally onto
`f_i(S_i)`, so it has no contraction over `Z_i` onto a lower-dimensional variety: the image of its
generic point is the generic point of `f_i(ι_i(S_i))`, of dimension `dim S_i`, and it is the
image of a point of `T`. -/
private theorem IsStabilizedChain.not_isNegativeRelativeRayContraction_of_lt {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (h : IsReachedOver sX sZ f ι BS i M π) {R : Set (RelativeNumericalCurveClasses M.sW π)}
    {T : Scheme.{0}} {sT : T ⟶ Spec (.of ℂ)} {gT : T ⟶ Z i} {g : M.W ⟶ T}
    (hc : IsNegativeRelativeRayContraction M.sW π sT (Divisor.toQDivisor M.K + M.B) R g gT)
    (hdim : topologicalKrullDim T < topologicalKrullDim M.W) : False := by
  obtain ⟨hcomp, -, hgen, hdimM⟩ := hC.invariants_of_isReachedOver h
  have hfg : g ≫ gT = π := hc.isRelativeContractionOfFace.comp_eq
  have hnec := hc.isNegativeExtremalContraction
  have hTv := hnec.isNormalVariety_target
  haveI : IsIso g.appTop := hnec.isContraction.isIso_app ⊤
  have hsT : sT = gT ≫ sZ i := eq_of_comp_eq_of_isIso_appTop' g (by
    rw [hnec.isContraction.comp_eq, ← Category.assoc, hfg, hcomp])
  have hZv := (hC.isProjectiveVariety_base i).toIsVariety
  haveI : LocallyOfFiniteType (sZ i) := hZv.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (gT ≫ sZ i) := by rw [← hsT]; exact hTv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType gT := locallyOfFiniteType_of_comp gT (sZ i)
  have h1 : topologicalKrullDim (closure {π (genericPoint M.W)} : Set (Z i)) ≤
      topologicalKrullDim T := by
    rw [← hfg, Scheme.Hom.comp_apply]
    exact (topologicalKrullDim_closure_map_le (sZ i) gT _).trans
      (topologicalKrullDim_subspace_le _ _)
  -- the image of the generic point of `S_i`
  have hXv := (hC.isProjectiveVariety i).toIsVariety
  haveI : LocallyOfFiniteType (sX i) := hXv.toLocallyOfFiniteType
  haveI : AlgebraicGeometry.IsVariety ℂ (sX i) := hXv
  haveI : AlgebraicGeometry.IsVariety ℂ (sZ i) := hZv
  haveI : IsIntegral (Z i) := hZv.toIsIntegral
  haveI : IsClosedImmersion (ι i) := (hC.isStratumAdjunctionPair i).some.isClosedImmersion
  have hgp := isGenericPoint_range (ι i)
  have hm := map_mem_biregularLocus_of_not_subset hgp (hC.not_subset i)
  have hX4 := (hC.isCanonicalDivisor i).1
  have hZ4 : topologicalKrullDim (Z i) = (4 : ℕ) := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (sZ i) (sX i)
      (hC.isFlipOf i).isSmallMorphism.isBirationalMorphism, hX4]
  have e1 := topologicalKrullDim_closure_singleton_add_coheight (sX i) ((ι i) (genericPoint (S i)))
  have e2 := topologicalKrullDim_closure_singleton_add_coheight (sZ i)
    ((f i) ((ι i) (genericPoint (S i))))
  rw [MMP.Positivity.coheight_map_of_mem_biregularLocus (f i) hm, hZ4] at e2
  rw [hX4] at e1
  have h2 : topologicalKrullDim (closure {π (genericPoint M.W)} : Set (Z i)) =
      topologicalKrullDim (S i) := by
    rw [hgen, Scheme.Hom.comp_apply, withBot_eq_of_add_eq_add e2 e1, hgp.def,
      ← topologicalKrullDim_eq_range]
  rw [h2, ← hdimM] at h1
  exact absurd (h1.trans_lt hdim) (lt_irrefl _)

/-- **A block continues while the adjoint is not nef.** From a pair reached in block `i` whose
adjoint is not nef over `Z_i`, there is an elementary dlt step over `Z_i` to a pair reached in
block `i`, which is also an elementary dlt step over the point. -/
private theorem IsStabilizedChain.exists_step (hP : ProjectiveLowerLogMMP 3) {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (hM : IsReachedOver sX sZ f ι BS i M π) (hnef : ¬ M.IsNefOver π) :
    ∃ (M' : BlockModel) (π' : M'.W ⟶ Z i), M.IsAbsStep M' ∧ IsReachedOver sX sZ f ι BS i M' π' :=
  by
  classical
  obtain ⟨hcomp, -, -, hdimM⟩ := hC.invariants_of_isReachedOver hM
  have hAbs := hM.isAbsModel
  have hdim3 : topologicalKrullDim M.W ≤ 3 := by
    rw [hdimM, hC.dim_eq i]; exact_mod_cast hC.le_three
  obtain ⟨P, hPp, -, hfin⟩ := (hP.2 M.W (Z i) M.sW (sZ i) π M.K M.B hAbs.isProjectiveVariety
    (hC.isProjectiveVariety_base i) hcomp hdim3 hAbs.isQFactorial hAbs.isCanonicalDivisor
    hAbs.isDltPair).2.2
  by_cases h0 : (0 : ℕ∞) < P.n
  · have h1 : ((1 : ℕ) : ℕ∞) ≤ P.n := by exact_mod_cast Order.one_le_iff_pos.mpr h0
    have hr1 := IsReachedOver.of_program hM P hPp 1 h1
    refine ⟨BlockModel.ofProgram P 1, P.πY 0, ?_, hr1⟩
    exact BlockModel.isAbsStep_of_isElementaryDltStep hAbs (hC.isProjectiveVariety_base i) hcomp
      (P.isRelativeDltModel 1 h1).comp_eq (P.isElementaryDltStep 0 h0) (P.BY_eq 0 h0)
  · have htoNat : P.n.toNat = 0 := by
      rw [not_lt, nonpos_iff_eq_zero] at h0
      rw [h0]; rfl
    let Q : ℕ → Prop := fun m =>
      (BlockModel.ofProgram P m).IsNefOver (modelMap π P.πY m) ∨
        ∃ (R' : Set (RelativeNumericalCurveClasses (BlockModel.ofProgram P m).sW
            (modelMap π P.πY m))) (T : Scheme.{0}) (sT : T ⟶ Spec (.of ℂ)) (gT : T ⟶ Z i)
          (g : (BlockModel.ofProgram P m).W ⟶ T),
          IsNegativeRelativeRayContraction (BlockModel.ofProgram P m).sW (modelMap π P.πY m) sT
            (Divisor.toQDivisor (BlockModel.ofProgram P m).K + (BlockModel.ofProgram P m).B)
            R' g gT ∧ topologicalKrullDim T < topologicalKrullDim (BlockModel.ofProgram P m).W
    have hQ : Q P.n.toNat := by
      rcases hfin with hn | hF
      · exact Or.inl hn
      · exact Or.inr ⟨P.finalRay, P.T, P.sT, P.gT, P.g, (P.final_spec hF).2.1,
          (P.final_spec hF).2.2⟩
    rw [htoNat] at hQ
    rcases hQ with hn | ⟨R', T, sT, gT, g, hc, hlt⟩
    · exact absurd hn hnef
    · exact (hC.not_isNegativeRelativeRayContraction_of_lt hM hc hlt).elim

/-- The strata `S_i ⤏ S_{i+1}` of a stabilized chain are birational over `Z_i`: over the common
biregular locus of `f_i` and `f_i⁺`, both are the closure of the common image. -/
private theorem IsStabilizedChain.exists_partialIso {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) (i : ℕ) :
    ∃ e : (S i).PartialIso (S (i + 1)), e.IsOver (ι i ≫ f i) (ι (i + 1) ≫ fp i) := by
  haveI : IsClosedImmersion (ι i) := (hC.isStratumAdjunctionPair i).some.isClosedImmersion
  haveI : IsClosedImmersion (ι (i + 1)) :=
    (hC.isStratumAdjunctionPair (i + 1)).some.isClosedImmersion
  set V := biregularLocus (f i) ⊓ biregularLocus (fp i)
  haveI : IsIso (f i ∣_ V) := isBiregular_iff_le_biregularLocus.mpr inf_le_left
  haveI : IsIso (fp i ∣_ V) := isBiregular_iff_le_biregularLocus.mpr inf_le_right
  have h1 := map_mem_biregularLocus_of_not_subset (isGenericPoint_range (ι i)) (hC.not_subset i)
  have h2 := map_mem_biregularLocus_of_not_subset (isGenericPoint_range (ι (i + 1)))
    (hC.not_subset' i)
  have hcorr := hC.corr i
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hcorr
  refine exists_partialIso_isOver_of_isIso (f i) (fp i) V (ι i) (ι (i + 1)) ⟨?_, ?_⟩ (hC.corr i)
  · rw [Scheme.Hom.comp_apply]; exact h1
  · rw [Scheme.Hom.comp_apply, hcorr]; exact h2

/-- **Discrepancies on the strata do not decrease** along a step of a stabilized chain
(`MMP.Mori.IsFlip.isDiscrepancy_le_of_isStratumAdjunctionPair`). -/
private theorem IsStabilizedChain.isDiscrepancy_le {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) (i : ℕ)
    (D : DivisorOver ℂ (ι i ≫ sX i)) (D' : DivisorOver ℂ (ι (i + 1) ≫ sX (i + 1)))
    (hv : ValEqOver (ι i ≫ f i) (ι (i + 1) ≫ fp i) D.valuation D'.valuation)
    {n n' : ℕ} {KS : Divisor (S i)} {KS' : Divisor (S (i + 1))} {a a' : ℚ}
    (ha : MMP.Mori.IsDiscrepancy (ι i ≫ sX i) n KS (BS i) D a)
    (ha' : MMP.Mori.IsDiscrepancy (ι (i + 1) ≫ sX (i + 1)) n' KS' (BS (i + 1)) D' a') :
    a ≤ a' := by
  have hb := hC.boundary_succ i
  have hS' := hC.isStratumAdjunctionPair (i + 1)
  have hB' := hC.isDltPair (i + 1)
  rw [hb] at hS' hB'
  refine isDiscrepancy_le_of_valEqOver_of_isFlipOf (hC.isCanonicalDivisor i)
    (hC.isProjectiveVariety i) (hC.isProjectiveVariety (i + 1)) (hC.isDltPair i) hB'
    (hC.isFlipOf i) (hC.all_not_subset i) ?_ (hC.isStratumAdjunctionPair i) hS' D D' hv ha ha'
  rw [← hb]
  exact hC.all_not_subset' i

/-- **Prime divisors of the next stratum come from the stratum**
(`exists_primeDivisor_valEqOver_of_partialIso` with the smallness of `S_{i+1} ⟶ Z_i`). -/
private theorem IsStabilizedChain.exists_primeDivisor_valEqOver {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) (i : ℕ) (F : MMP.Mori.PrimeDivisor (S (i + 1))) :
    ∃ D : MMP.Mori.PrimeDivisor (S i),
      ValEqOver (ι i ≫ f i) (ι (i + 1) ≫ fp i) D.divisorialValuation F.divisorialValuation := by
  haveI : IsClosedImmersion (ι i) := (hC.isStratumAdjunctionPair i).some.isClosedImmersion
  haveI : IsClosedImmersion (ι (i + 1)) :=
    (hC.isStratumAdjunctionPair (i + 1)).some.isClosedImmersion
  haveI : IsProper (f i) :=
    isProper_of_isProjectiveMorphism _ (hC.isFlipOf i).isContraction.isProjectiveMorphism
  haveI : IsProper (fp i) := (hC.isFlipOf i).isSmallMorphism_flip.isProper
  obtain ⟨e, he⟩ := hC.exists_partialIso i
  have hd := hC.dim_eq i
  have hd' := hC.dim_eq (i + 1)
  exact exists_primeDivisor_valEqOver_of_partialIso
    (hC.isStratumAdjunctionPair i).some.isNormalVariety
    (hC.isStratumAdjunctionPair (i + 1)).some.isNormalVariety
    (hC.isProjectiveVariety_base i).toIsVariety (ι i ≫ f i) (ι (i + 1) ≫ fp i)
    (by rw [Category.assoc, (hC.isFlipOf i).isContraction.comp_eq])
    (by rw [Category.assoc, (hC.isFlipOf i).isSmallMorphism_flip.comp_eq])
    hd hd' e he F (hC.small i F)

/-- **Tracking a block.** A pair `(W, B_W)` reached in block `i`, over `Z_i` by `π`, comes with a
crepant model `p₀ : U ⟶ S_i` from which it is reached and a birational map `U ⤏ W` over `Z_i`;
every prime divisor of `W` is the transform of a prime divisor of `U` with the same coefficient,
and discrepancies do not decrease from `(U, B_U)` to `(W, B_W)`. -/
private theorem IsStabilizedChain.track {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (hM : IsReachedOver sX sZ f ι BS i M π) :
    ∃ (U : BlockModel) (p₀ : U.W ⟶ S i), IsCrepantOver sX ι BS i U p₀ ∧
      (∃ e : U.W.PartialIso M.W, e.IsOver (p₀ ≫ ι i ≫ f i) π) ∧
      (∀ F : MMP.Mori.PrimeDivisor M.W, ∃ P : MMP.Mori.PrimeDivisor U.W,
        ValEqOver (p₀ ≫ ι i ≫ f i) π P.divisorialValuation F.divisorialValuation ∧
          M.B.coeff F = U.B.coeff P) ∧
      (∀ (n : ℕ) (KU : Divisor U.W) (KM : Divisor M.W) (D₀ : DivisorOver ℂ U.sW)
        (D : DivisorOver ℂ M.sW) (a a' : ℚ),
        ValEqOver (p₀ ≫ ι i ≫ f i) π D₀.valuation D.valuation →
        MMP.Mori.IsDiscrepancy U.sW n KU U.B D₀ a →
        MMP.Mori.IsDiscrepancy M.sW n KM M.B D a' → a ≤ a') := by
  induction hM with
  | start M p hp =>
    have hp' := hp
    obtain ⟨hAbs, -, -, -, hb, -⟩ := hp'
    have hsurj : Function.Surjective ((p ≫ ι i ≫ f i).stalkMap (genericPoint M.W)) := by
      haveI : IsClosedImmersion (ι i) := (hC.isStratumAdjunctionPair i).some.isClosedImmersion
      exact surjective_stalkMap_comp_of_isBirationalMorphism p hb (ι i ≫ f i)
        (surjective_stalkMap_of_not_subset (ι i) (f i) (hC.not_subset i))
    refine ⟨M, p, hp, ⟨Scheme.PartialIso.refl M.W, ?_⟩, fun F => ⟨F, ⟨rfl, ?_⟩, rfl⟩, ?_⟩
    · change (Iso.refl _).hom ≫ (⊤ : M.W.Opens).ι ≫ p ≫ ι i ≫ f i =
        (⊤ : M.W.Opens).ι ≫ p ≫ ι i ≫ f i
      rw [Iso.refl_hom, Category.id_comp]
    · refine Valuation.ext fun z => ?_
      have hc : ((Z i).presheaf.stalkCongr (.of_eq
          (rfl : (p ≫ ι i ≫ f i) (genericPoint M.W) = _))).hom z = z := by
        simp [TopCat.Presheaf.stalkCongr]
        try rfl
      simp only [Valuation.comap_apply, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply, hc]
    · intro n KU KM D₀ D a a' hv ha ha'
      have hval := hv.eq_of_surjective hsurj
      have hWv : IsNormalVariety ℂ M.sW := hAbs.isDltPair.1.1.1
      have hlin := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor M.sW hWv ha'.2.1
        ha.2.1
      have ha₂ := MMP.Spreading.isDiscrepancy_of_linearlyEquivalent ha hlin
      have hPW := ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair M.sW ha'.2.1 M.B).mp
        hAbs.isDltPair).1
      exact (MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPW hval ha₂ ha').le
  | step M M' π π' R Z' sZ' f' g' fp' φ' hr hst hBe hAbs' hcomp' hproj' ih =>
    obtain ⟨U, p₀, hU, ⟨e, he⟩, hT2, hT3⟩ := ih
    have hrM' := IsReachedOver.step M M' π π' R Z' sZ' f' g' fp' φ' hr hst hBe hAbs' hcomp' hproj'
    obtain ⟨hcomp, -, -, hdimM⟩ := hC.invariants_of_isReachedOver hr
    obtain ⟨-, -, -, hdimM'⟩ := hC.invariants_of_isReachedOver hrM'
    have hAbs := hr.isAbsModel
    have hnec := hst.isNegativeRelativeRayContraction.isNegativeExtremalContraction
    have hZv := hnec.isNormalVariety_target
    haveI : IsIntegral Z' := hZv.1.toIsIntegral
    haveI : IsNormal Z' := hZv.2
    haveI : LocallyOfFiniteType sZ' := hZv.1.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian sZ'
    haveI : IsProper f' := hnec.isContraction.isProper
    have hfs : f' ≫ sZ' = M.sW := hnec.isContraction.comp_eq
    have hfg : f' ≫ g' = π :=
      hst.isNegativeRelativeRayContraction.isRelativeContractionOfFace.comp_eq
    have hfpg : fp' ≫ g' = π' := hst.comp_eq
    haveI : IsIso f'.appTop := hnec.isContraction.isIso_app ⊤
    have hsZ' : sZ' = g' ≫ sZ i := eq_of_comp_eq_of_isIso_appTop' f' (by
      rw [hfs, ← Category.assoc, hfg, hcomp])
    have hfps : fp' ≫ sZ' = M'.sW := by rw [hsZ', ← Category.assoc, hfpg, hcomp']
    have hX : IsNormalVariety ℂ M.sW := hAbs.isDltPair.1.1.1
    have hX' : IsNormalVariety ℂ M'.sW := hAbs'.isDltPair.1.1.1
    haveI : LocallyOfFiniteType M.sW := hX.1.toLocallyOfFiniteType
    haveI : QuasiCompact M.sW := hX.1.toQuasiCompact
    haveI : LocallyOfFiniteType M'.sW := hX'.1.toLocallyOfFiniteType
    haveI : QuasiCompact M'.sW := hX'.1.toQuasiCompact
    -- the canonical divisors
    obtain ⟨n₀, hK⟩ := hAbs.isCanonicalDivisor
    obtain ⟨n₁, hK'⟩ := hAbs'.isCanonicalDivisor
    have hn₁ : n₁ = n₀ := by
      have h1 := hK.topologicalKrullDim_eq
      have h2 := hK'.topologicalKrullDim_eq
      rw [hdimM] at h1
      rw [hdimM'] at h2
      exact_mod_cast h2.symm.trans h1
    have hK'' : M'.K.IsCanonicalDivisor M'.sW n₀ := hn₁ ▸ hK'
    have hQX : ∀ D : QDivisor M.W, D.IsQCartier := fun D =>
      MMP.Fourfold.isQCartier_of_isQFactorial M.sW hAbs.isQFactorial D
    have hQX' : ∀ D : QDivisor M'.W, D.IsQCartier := fun D =>
      MMP.Fourfold.isQCartier_of_isQFactorial M'.sW hAbs'.isQFactorial D
    -- the nefness conditions of the step
    have hN : QDivisor.IsRelativelyNef M.sW f' (-(Divisor.toQDivisor M.K + M.B)) := by
      refine MMP.Mori.QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor (sX := M.sW)
        (hQX _) ?_
      rw [map_neg]
      exact IsRelativelyAmple.isRelativelyNef M.sW hnec.isRelativelyAntiAmple
    obtain ⟨hfb, hfpb, hproper, hsmall, hφ, hN'⟩ : IsBirationalMorphism f' ∧
        IsBirationalMorphism fp' ∧ IsProper fp' ∧
        2 ≤ closedsCodimension (MMP.Mori.exceptionalSet fp') ∧ IsModificationOf f' fp' φ' ∧
        QDivisor.IsRelativelyNef M'.sW fp' (Divisor.toQDivisor M'.K + M'.B) := by
      rcases hst.divisorial_or_flip with ⟨hb, -, hiso, hmod⟩ | hflip
      · haveI := hiso
        refine ⟨hb, isBirationalMorphism_of_isIso _, inferInstance,
          two_le_closedsCodimension_exceptionalSet_of_isIso fp', hmod, hQX' _, fun C hC => ?_⟩
        exact absurd (by simpa using isContractedBy_comp' (inv fp') hC)
          (MMP.Mori.ProperCurve.not_isContractedBy_id C)
      · haveI := hflip.isProper
        refine ⟨MMP.Flips.IsSmall.isBirationalMorphism _ _ hflip.isSmall_source,
          MMP.Flips.IsSmall.isBirationalMorphism _ _ hflip.isSmall, hflip.isProper,
          two_le_closedsCodimension_exceptionalSet_of_isSmall hflip.isSmall,
          hflip.isModificationOf, ?_⟩
        have hamp := hasRelativelyAmpleMultiple_of_isFlip hflip hK hK''
        rw [← hBe] at hamp
        exact MMP.Mori.QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor (sX := M'.sW)
          (hQX' _) (IsRelativelyAmple.isRelativelyNef M'.sW hamp.isRelativelyAmple_toRDivisor)
    haveI := hproper
    haveI : IsDominant f' := hfb.isDominant
    haveI : IsDominant fp' := hfpb.isDominant
    haveI : IsSeparated sZ' := hZv.1.toIsSeparated
    haveI : IsSeparated (Z' ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ')
    obtain ⟨e', -, he'⟩ := exists_partialIso_isOver_of_isModificationOf hφ g'
    rw [hfg, hfpg] at he'
    refine ⟨U, p₀, hU, ⟨e.trans e', he.trans he'⟩, fun F' => ?_, ?_⟩
    · obtain ⟨F, -, hFv, hc⟩ :=
        exists_primeDivisor_of_isModificationOf hX hX' hZv hfs hfps hfb hfpb hsmall hφ M.B F'
      have H1 := valEqOver_comap_functionFieldMap f' g' F.divisorialValuation
      have H2 := valEqOver_comap_functionFieldMap fp' g' F'.divisorialValuation
      rw [hFv] at H1
      have hv : ValEqOver π π' F.divisorialValuation F'.divisorialValuation :=
        (H1.trans H2.symm).of_eq hfg hfpg
      obtain ⟨P, hPv, hPc⟩ := hT2 F
      exact ⟨P, hPv.trans hv, by rw [hBe, hc, hPc]⟩
    · intro n KU KM' D₀ D a a' hv ha ha'
      have hn : n₀ = n := by
        have h1 := ha'.2.1.topologicalKrullDim_eq
        have h2 := hK''.topologicalKrullDim_eq
        exact_mod_cast h2.symm.trans h1
      subst hn
      have hlin := MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor M'.sW hX' hK''
        ha'.2.1
      have ha'₂ := MMP.Spreading.isDiscrepancy_of_linearlyEquivalent ha' hlin
      have hP := ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair M.sW hK M.B).mp
        hAbs.isDltPair).1
      have hP' := ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair M'.sW hK'' M'.B).mp
        hAbs'.isDltPair).1
      obtain ⟨Dm, hDm, hle⟩ := exists_isDiscrepancy_le_of_isModificationOf hX hX' hZv hfs hfps hfb
        hfpb hsmall hφ hBe hK hK'' hP hP' hN hN' D ha'₂
      obtain ⟨b, hb⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP.isPair hK Dm
      have H1 := valEqOver_comap_functionFieldMap f' g' Dm.valuation
      have H2 := valEqOver_comap_functionFieldMap fp' g' D.valuation
      rw [hDm] at H1
      have hvm : ValEqOver π π' Dm.valuation D.valuation := (H1.trans H2.symm).of_eq hfg hfpg
      have h1 := hT3 n₀ KU M.K D₀ Dm a b (hv.trans hvm.symm) ha hb
      have h2 := hle b hb
      linarith

/-- **Prime divisors of a reached pair against the next stratum.** For a pair `(W, B_W)` reached
in block `i` and a prime divisor `P` of `W`, `-coeff_P B_W ≤ a(P, S_{i+1}, B_{S_{i+1}})`: the
prime divisor of the crepant model `U` it comes from has the same coefficient, and its
discrepancy over `S_i` does not exceed that over `S_{i+1}`. -/
private theorem IsStabilizedChain.neg_coeff_le_of_isReachedOver {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (hM : IsReachedOver sX sZ f ι BS i M π) (P : MMP.Mori.PrimeDivisor M.W)
    (D : DivisorOver ℂ (ι (i + 1) ≫ sX (i + 1))) {n : ℕ} {KS : Divisor (S (i + 1))} {a : ℚ}
    (hv : ValEqOver π (ι (i + 1) ≫ fp i) P.divisorialValuation D.valuation)
    (ha : MMP.Mori.IsDiscrepancy (ι (i + 1) ≫ sX (i + 1)) n KS (BS (i + 1)) D a) :
    -M.B.coeff P ≤ a := by
  obtain ⟨U, p₀, hU, -, hT2, -⟩ := hC.track hM
  obtain ⟨P₀, hP₀v, hP₀c⟩ := hT2 P
  obtain ⟨-, -, -, hprop, hb, nS, KS₀, hUn, -, hcrep⟩ := hU
  haveI := hprop
  haveI : IsDominant p₀ := hb.isDominant
  let D₀ : DivisorOver ℂ (ι i ≫ sX i) := ⟨U.W, p₀, hUn, hb, P₀⟩
  have hv₀ : ValEqOver (ι i ≫ f i) (ι (i + 1) ≫ fp i) D₀.valuation D.valuation :=
    (valEqOver_comap_functionFieldMap p₀ (ι i ≫ f i) P₀.divisorialValuation).symm.trans
      (hP₀v.trans hv)
  rw [hP₀c]
  exact hC.isDiscrepancy_le i D₀ D hv₀ (hcrep P₀) ha

/-- **Prime divisors of the next stratum against a reached pair.** For a pair `(W, B_W)` reached
in block `i` and a prime divisor `F` of `S_{i+1}`, `-coeff_F B_{S_{i+1}} ≤ a(F, W, B_W)`: `F`
corresponds to a prime divisor of `S_i` with the same coefficient, whose strict transform on the
crepant model `U` has discrepancy `-coeff_F B_{S_{i+1}}`, and discrepancies do not decrease from
`U` to `W`. -/
private theorem IsStabilizedChain.neg_coeff_le_of_isReachedOver' {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (hM : IsReachedOver sX sZ f ι BS i M π) (F : MMP.Mori.PrimeDivisor (S (i + 1)))
    (D : DivisorOver ℂ M.sW) {n : ℕ} {KM : Divisor M.W} {a : ℚ}
    (hv : ValEqOver π (ι (i + 1) ≫ fp i) D.valuation F.divisorialValuation)
    (ha : MMP.Mori.IsDiscrepancy M.sW n KM M.B D a) :
    -(BS (i + 1)).coeff F ≤ a := by
  obtain ⟨-, -, -, hdimM⟩ := hC.invariants_of_isReachedOver hM
  obtain ⟨U, p₀, hU, -, -, hT3⟩ := hC.track hM
  obtain ⟨hUabs, -, hdimU, hprop, hb, nS, KS₀, hUn, -, hcrep⟩ := hU
  haveI := hprop
  haveI : IsDominant p₀ := hb.isDominant
  -- the prime divisor of `S_i` corresponding to `F`, and its strict transform on `U`
  obtain ⟨D₀, hD₀⟩ := hC.exists_primeDivisor_valEqOver i F
  have hcoeff : (BS i).coeff D₀ = (BS (i + 1)).coeff F := by
    obtain ⟨h, hv'⟩ := hD₀
    exact hC.coeff_eq i D₀ F hv'
  have hSv : IsNormalVariety ℂ (ι i ≫ sX i) := (hC.isStratumAdjunctionPair i).some.isNormalVariety
  obtain ⟨P₀, -, hP₀v⟩ := exists_primeDivisor_valuation_eq_of_isBirationalMorphism hSv p₀ hUn hb D₀
  -- the discrepancy of `P₀` on `U` is `-coeff_{D₀} B_{S_i}`
  have hUv : IsNormalVariety ℂ U.sW := hUabs.isDltPair.1.1.1
  have hnU : topologicalKrullDim U.W = n := by
    rw [hdimU, ← hdimM, ha.2.1.topologicalKrullDim_eq]
  obtain ⟨KU, hKU⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety U.sW hUv hnU
  obtain ⟨aP, haP⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hUabs.isDltPair.1.1 hKU
    (DivisorOver.ofPrimeDivisor ℂ hUv P₀)
  have haP' := haP.eq_neg_coeff_of_ofPrimeDivisor hUv
  have hcr := hcrep P₀
  have hdltS := (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair
    (hC.isDltStratum i)).1.2 (hC.isStratumAdjunctionPair i).some rfl
  obtain ⟨c₀, hc₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hdltS.1.1 hcr.2.1
    (DivisorOver.ofPrimeDivisor ℂ hSv D₀)
  have hPW := ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair (ι i ≫ sX i) hcr.2.1 (BS i)).mp
    hdltS).1
  have hval₀ : (⟨U.W, p₀, hUn, hb, P₀⟩ : DivisorOver ℂ (ι i ≫ sX i)).valuation =
      (DivisorOver.ofPrimeDivisor ℂ hSv D₀).valuation := by
    rw [valuation_ofPrimeDivisor, ← hP₀v]
    rfl
  have heq := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPW hval₀ hcr hc₀
  have hc₀' := hc₀.eq_neg_coeff_of_ofPrimeDivisor hSv
  -- discrepancies do not decrease from `U` to `W`
  have hval : ValEqOver (p₀ ≫ ι i ≫ f i) π (DivisorOver.ofPrimeDivisor ℂ hUv P₀).valuation
      D.valuation := by
    rw [valuation_ofPrimeDivisor]
    have H1 := valEqOver_comap_functionFieldMap p₀ (ι i ≫ f i) P₀.divisorialValuation
    rw [hP₀v] at H1
    exact H1.trans (hD₀.trans hv.symm)
  have hT := hT3 n KU KM _ D aP a hval haP ha
  linarith

/-- **The end of a block is a crepant model of the next stratum.** A pair reached in block `i`
whose adjoint is nef over `Z_i` maps to `S_{i+1}` over `Z_i` as a crepant model. `S_{i+1}` is a
log canonical model of `(W, B_W) ⟶ Z_i` (`isLogCanonicalModelOf_of_le`), so the birational map
`W ⤏ S_{i+1}` is a morphism `h` (FA 2.24.3); `B_W` minus the crepant boundary of `S_{i+1}` on
`W` is effective, `h`-exceptional and `h`-nef, hence zero (FA 17.10). -/
private theorem IsStabilizedChain.exists_isCrepantOver_succ {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) {i : ℕ} {M : BlockModel} {π : M.W ⟶ Z i}
    (hM : IsReachedOver sX sZ f ι BS i M π) (hnef : M.IsNefOver π) :
    ∃ p : M.W ⟶ S (i + 1), IsCrepantOver sX ι BS (i + 1) M p ∧ p ≫ ι (i + 1) ≫ fp i = π := by
  classical
  obtain ⟨hcomp, hπproj, -, hdimM⟩ := hC.invariants_of_isReachedOver hM
  have hAbs := hM.isAbsModel
  obtain ⟨U, p₀, hU, ⟨e₁, he₁⟩, -, -⟩ := hC.track hM
  obtain ⟨-, -, -, -, hb₀, -⟩ := hU
  -- the strata and their structure
  have hSv : IsNormalVariety ℂ (ι i ≫ sX i) := (hC.isStratumAdjunctionPair i).some.isNormalVariety
  have hS'v : IsNormalVariety ℂ (ι (i + 1) ≫ sX (i + 1)) :=
    (hC.isStratumAdjunctionPair (i + 1)).some.isNormalVariety
  haveI : IsClosedImmersion (ι (i + 1)) :=
    (hC.isStratumAdjunctionPair (i + 1)).some.isClosedImmersion
  haveI : CompactSpace (S (i + 1)) := (ι (i + 1)).isClosedEmbedding.compactSpace
  haveI : LocallyOfFiniteType (ι (i + 1) ≫ sX (i + 1)) := hS'v.1.toLocallyOfFiniteType
  haveI : QuasiCompact (ι (i + 1) ≫ sX (i + 1)) := hS'v.1.toQuasiCompact
  haveI : IsSeparated (ι i ≫ sX i) := hSv.1.toIsSeparated
  haveI : IsSeparated (S i ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := ι i ≫ sX i)
  haveI : IsSeparated (ι (i + 1) ≫ sX (i + 1)) := hS'v.1.toIsSeparated
  haveI : IsSeparated (S (i + 1) ↘ ⊤_ Scheme) :=
    isSeparated_toTerminal (s := ι (i + 1) ≫ sX (i + 1))
  have hZv : MMP.Mori.IsVariety ℂ (sZ i) := (hC.isProjectiveVariety_base i).toIsVariety
  haveI : IsSeparated (sZ i) := hZv.toIsSeparated
  haveI : IsSeparated (Z i ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ i)
  have hWv : IsNormalVariety ℂ M.sW := hAbs.isDltPair.1.1.1
  haveI : LocallyOfFiniteType M.sW := hWv.1.toLocallyOfFiniteType
  haveI : QuasiCompact M.sW := hWv.1.toQuasiCompact
  haveI : IsProper π := isProper_of_isProjectiveMorphism _ hπproj
  haveI : IsProper (fp i) := (hC.isFlipOf i).isSmallMorphism_flip.isProper
  have hgc : (ι (i + 1) ≫ fp i) ≫ sZ i = ι (i + 1) ≫ sX (i + 1) := by
    rw [Category.assoc, (hC.isFlipOf i).isSmallMorphism_flip.comp_eq]
  -- the birational map `W ⤏ S_{i+1}` over `Z_i`
  obtain ⟨e₀, he₀⟩ := exists_partialIso_isOver_of_isBirationalMorphism p₀ hb₀ (ι i ≫ f i)
  obtain ⟨e₂, he₂⟩ := hC.exists_partialIso i
  set ρ := (e₁.symm.trans e₀).trans e₂ with hρdef
  have hρ : ρ.IsOver π (ι (i + 1) ≫ fp i) := (he₁.symm.trans he₀).trans he₂
  -- canonical divisors and the adjoint of `S_{i+1}`
  obtain ⟨KS, hKS, hamp⟩ := hC.exists_adjoint_pos i
  have hd : topologicalKrullDim M.W = d := by rw [hdimM, hC.dim_eq i]
  obtain ⟨mW, hKW⟩ := hAbs.isCanonicalDivisor
  have hmW : mW = d := by
    have := hKW.topologicalKrullDim_eq
    rw [hd] at this
    exact_mod_cast this.symm
  have hKW' : M.K.IsCanonicalDivisor M.sW d := hmW ▸ hKW
  have hBS : MMP.Intersection.IsDltPair (ι (i + 1) ≫ sX (i + 1)) (BS (i + 1)) :=
    (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair (hC.isDltStratum (i + 1))).1.2
      (hC.isStratumAdjunctionPair (i + 1)).some rfl
  -- `S_{i+1}` is the log canonical model of `W ⟶ Z_i`, so `W ⤏ S_{i+1}` is a morphism `h`
  have hlc := isLogCanonicalModelOf_of_le hWv hS'v hZv π (ι (i + 1) ≫ fp i) hcomp hgc hKW'
    hAbs.isDltPair hKS hBS hamp ρ hρ
    (fun P D _ _ _ hv ha => hC.neg_coeff_le_of_isReachedOver hM P D hv ha)
    (fun F D _ _ _ hv ha => hC.neg_coeff_le_of_isReachedOver' hM F D hv ha)
  have hfW : IsRelativeWeakLogCanonicalModel M.sW d M.K (QDivisor.toRDivisor M.B) π :=
    ⟨inferInstance, isLogCanonical_of_isDltPair hAbs.isDltPair hKW', by
      rw [logCanonicalDivisor_eq]; exact hnef⟩
  obtain ⟨h, hh⟩ :=
    IsLogCanonicalModelOf.exists_toRationalMap_eq_of_isRelativeWeakLogCanonicalModel hWv.1 hS'v.1
      hZv hcomp hgc hfW hlc
  -- `h ≫ g = π`
  have h1 := (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp hh.symm)
  haveI : IsDominant ρ.source.ι := AlgebraicGeometry.Opens.isDominant_ι ρ.dense_source
  have hhπ : h ≫ ι (i + 1) ≫ fp i = π := by
    refine ext_of_isDominant_of_isSeparated (Z i ↘ ⊤_ Scheme) (Subsingleton.elim _ _)
      ρ.source.ι ?_
    have h1' : ρ.iso.hom ≫ ρ.target.ι = ρ.source.ι ≫ h := h1
    rw [← Category.assoc, ← h1', Category.assoc]
    exact hρ
  -- `h` is a proper birational morphism
  have hsW : h ≫ ι (i + 1) ≫ sX (i + 1) = M.sW := by
    rw [← hgc, ← Category.assoc, hhπ, hcomp]
  have hb : IsBirationalMorphism h := by
    change MMP.Mori.RationalMap.IsBirational h.toRationalMap
    rw [hh]
    exact MMP.Mori.RationalMap.isBirational_toRationalMap ρ
  haveI : IsProper h := by
    have : IsProper (h ≫ ι (i + 1) ≫ sX (i + 1)) := by
      rw [hsW]; exact isProper_of_isProjectiveMorphism _ hAbs.isProjectiveVariety.isProjective
    exact MorphismProperty.of_postcomp (W := @IsProper) (W' := @IsSeparated) h
      (ι (i + 1) ≫ sX (i + 1)) inferInstance this
  have hWn : IsNormalVariety ℂ (h ≫ ι (i + 1) ≫ sX (i + 1)) := by rw [hsW]; exact hWv
  -- the crepant boundaries of `S_{i+1}` and of `W` on `W`
  obtain ⟨Δ, hΔ, -⟩ := (hBS.1.1.existsUnique_isCrepantBoundary hKS h hWn hb).1
  have hWn1 : IsNormalVariety ℂ (𝟙 M.W ≫ M.sW) := by rw [Category.id_comp]; exact hWv
  obtain ⟨Δ', hΔ', -⟩ := (hAbs.isDltPair.1.1.existsUnique_isCrepantBoundary hKW' (𝟙 M.W) hWn1
    (isBirationalMorphism_of_isIso _)).1
  have hΔ'eq : Δ' = M.B := by
    ext F
    have h2 : MMP.Mori.IsDiscrepancy M.sW d M.K M.B (DivisorOver.ofPrimeDivisor ℂ hWv F)
        (-Δ'.coeff F) := hΔ' F
    have := h2.eq_neg_coeff_of_ofPrimeDivisor hWv
    change Δ'.coeff F = M.B.coeff F
    linarith
  -- `B_W - Δ` is nef over `S_{i+1}`
  have hQS : (Divisor.toQDivisor KS + BS (i + 1)).IsQCartier := by
    obtain ⟨m, hm, L, hL, hLD, -⟩ := hamp
    exact ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩
  have hN : QDivisor.IsRelativelyNef (ι (i + 1) ≫ sX (i + 1)) (𝟙 (S (i + 1)))
      (-(Divisor.toQDivisor KS + BS (i + 1))) := by
    obtain ⟨m, hm, hmC⟩ := hQS
    exact ⟨⟨m, hm, by rw [smul_neg]; exact hmC.neg⟩,
      fun C hC => absurd hC (MMP.Mori.ProperCurve.not_isContractedBy_id C)⟩
  have hQW : ∀ D : QDivisor M.W, D.IsQCartier := fun D =>
    MMP.Fourfold.isQCartier_of_isQFactorial M.sW hAbs.isQFactorial D
  have hNπ := MMP.Mori.QDivisor.isRelativelyNef_of_isRelativelyNef_toRDivisor (sX := M.sW)
    (hQW _) hnef
  have hN' : QDivisor.IsRelativelyNef M.sW h (Divisor.toQDivisor M.K + M.B) := by
    obtain ⟨hq, hall⟩ := hNπ
    exact ⟨hq, fun C hC => hall C (by rw [← hhπ]; exact isContractedBy_comp' _ hC)⟩
  have hnefG := MMP.Mori.IsCrepantBoundary.isRelativelyNef_sub hS'v hWv hS'v
    (f := 𝟙 (S (i + 1))) (f' := h) (Category.id_comp _) hsW (isBirationalMorphism_of_isIso _) hb
    hKS hKW' hN hN' (g := h) (g' := 𝟙 M.W) hWn hWn1 hb (isBirationalMorphism_of_isIso _)
    (by simp) hΔ hΔ'
  rw [hΔ'eq, Category.comp_id] at hnefG
  -- `B_W - Δ` is effective and exceptional over `S_{i+1}`
  have hvF : ∀ F : MMP.Mori.PrimeDivisor M.W, ValEqOver π (ι (i + 1) ≫ fp i)
      F.divisorialValuation (⟨M.W, h, hWn, hb, F⟩ : DivisorOver ℂ _).valuation := fun F => by
    haveI : IsDominant h := hb.isDominant
    exact (valEqOver_comap_functionFieldMap h (ι (i + 1) ≫ fp i) F.divisorialValuation).of_eq
      hhπ rfl
  have hGeff : (M.B - Δ).IsEffective := by
    rw [DivisorWithCoeffs.isEffective_iff_nonneg]
    intro F
    have := hC.neg_coeff_le_of_isReachedOver hM F _ (hvF F) (hΔ F)
    change 0 ≤ M.B.coeff F - Δ.coeff F
    linarith
  have hGexc : ∀ F : MMP.Mori.PrimeDivisor M.W,
      ¬ MMP.Flips.IsExceptionalPrimeDivisor (ι (i + 1) ≫ sX (i + 1)) h F →
        (M.B - Δ).coeff F = 0 := by
    intro F hF
    have hnot' : ¬ (MMP.Flips.ProperDivisorOver.mk ⟨M.W, h, hWn, hb, F⟩ inferInstance :
        MMP.Flips.ProperDivisorOver ℂ (ι (i + 1) ≫ sX (i + 1))).IsExceptional :=
      fun hex => hF ⟨hWn, hb, inferInstance, hex⟩
    obtain ⟨Q₀, -, hQ₀, -⟩ :=
      MMP.Flips.ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hS'v _ hnot'
    have hnot : ¬ (⟨M.W, h, hWn, hb, F⟩ : DivisorOver ℂ _).IsExceptional := by
      rw [isExceptional_iff_two_le_coheight hS'v]
      change ¬ 2 ≤ Order.coheight (h F.genericPoint)
      have hQ₀' : h F.genericPoint = Q₀.genericPoint := hQ₀
      rw [hQ₀', Q₀.coheight_genericPoint]
      decide
    obtain ⟨Q, hQ⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hS'v _ hnot
    obtain ⟨aQ, haQ⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBS.1.1 hKS
      (DivisorOver.ofPrimeDivisor ℂ hS'v Q)
    have haQ' := haQ.eq_neg_coeff_of_ofPrimeDivisor hS'v
    have hPWS := ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair (ι (i + 1) ≫ sX (i + 1)) hKS
      (BS (i + 1))).mp hBS).1
    have h3 := MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq hPWS hQ (hΔ F) haQ
    have hvQ : ValEqOver π (ι (i + 1) ≫ fp i) F.divisorialValuation
        (DivisorOver.ofPrimeDivisor ℂ hS'v Q).valuation := by
      rw [← hQ]; exact hvF F
    have h4 := hC.neg_coeff_le_of_isReachedOver hM F _ hvQ haQ
    obtain ⟨bF, hbF⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hAbs.isDltPair.1.1 hKW'
      (DivisorOver.ofPrimeDivisor ℂ hWv F)
    have hbF' := hbF.eq_neg_coeff_of_ofPrimeDivisor hWv
    have hvQ' : ValEqOver π (ι (i + 1) ≫ fp i) (DivisorOver.ofPrimeDivisor ℂ hWv F).valuation
        Q.divisorialValuation := by
      rw [valuation_ofPrimeDivisor, ← valuation_ofPrimeDivisor hS'v Q]
      exact hvQ
    have h5 := hC.neg_coeff_le_of_isReachedOver' hM Q _ hvQ' hbF
    change M.B.coeff F - Δ.coeff F = 0
    linarith
  have hG0 := MMP.Mori.QDivisor.eq_zero_of_isEffective_of_isRelativelyNef ℂ
    (ι (i + 1) ≫ sX (i + 1)) (h ≫ ι (i + 1) ≫ sX (i + 1)) hS'v hWn h rfl hb (hQW _) hGexc
    hGeff hnefG
  have hBΔ : M.B = Δ := sub_eq_zero.mp hG0
  refine ⟨h, ⟨hAbs, hsW, by rw [hd, hC.dim_eq (i + 1)], inferInstance, hb, d, KS, hWn, ⟨d, hKS⟩,
    hBΔ ▸ hΔ⟩, hhπ⟩

/-- **An empty block is a trivial stratum diagram.** If a crepant model of `S_i` has adjoint nef
over `Z_i`, then `S_i ≅ S_{i+1}` over `Z_i`. -/
private theorem IsStabilizedChain.exists_iso_of_isNefOver {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) {i : ℕ} {M : BlockModel} {p : M.W ⟶ S i}
    (hM : IsCrepantOver sX ι BS i M p) (hnef : M.IsNefOver (p ≫ ι i ≫ f i)) :
    ∃ φ : S i ≅ S (i + 1), ι i ≫ f i = φ.hom ≫ ι (i + 1) ≫ fp i := by
  classical
  have hπZ := (hC.invariants_of_isReachedOver (IsReachedOver.start M p hM)).1
  obtain ⟨h, hh, hhπ⟩ := hC.exists_isCrepantOver_succ (IsReachedOver.start M p hM) hnef
  obtain ⟨hAbs, hp, -, hpprop, hpb, n, KS, hU, ⟨m, hKS⟩, hcrep⟩ := hM
  obtain ⟨-, hh0, -, hhprop, hhb, n', KS', hU', ⟨m', hKS'⟩, hcrep'⟩ := hh
  haveI := hpprop
  haveI := hhprop
  -- the strata are projective normal varieties
  have hSv : IsNormalVariety ℂ (ι i ≫ sX i) := (hC.isStratumAdjunctionPair i).some.isNormalVariety
  have hS'v : IsNormalVariety ℂ (ι (i + 1) ≫ sX (i + 1)) :=
    (hC.isStratumAdjunctionPair (i + 1)).some.isNormalVariety
  have hSp := hC.isProjectiveVariety_stratum i
  have hS'p := hC.isProjectiveVariety_stratum (i + 1)
  haveI : IsProper (ι i ≫ sX i) := isProper_of_isProjectiveMorphism _ hSp.isProjective
  haveI : IsProper (ι (i + 1) ≫ sX (i + 1)) :=
    isProper_of_isProjectiveMorphism _ hS'p.isProjective
  haveI : QuasiCompact (ι i ≫ sX i) := inferInstance
  haveI : QuasiCompact (ι (i + 1) ≫ sX (i + 1)) := inferInstance
  haveI : CompactSpace (S i) := QuasiCompact.compactSpace_of_compactSpace (ι i ≫ sX i)
  haveI : CompactSpace (S (i + 1)) :=
    QuasiCompact.compactSpace_of_compactSpace (ι (i + 1) ≫ sX (i + 1))
  -- the adjoint signs, for the canonical divisors of the crepant boundaries
  obtain ⟨KS₀, hKS₀, hneg⟩ := hC.exists_adjoint_neg i
  obtain ⟨KS₀', hKS₀', hpos⟩ := hC.exists_adjoint_pos i
  have hcrep₀ : IsCrepantBoundary (ι i ≫ sX i) n KS₀ (BS i) p hU hpb M.B := fun F =>
    MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hcrep F)
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor _ hSv hKS₀ hKS)
  have hcrep₀' : IsCrepantBoundary (ι (i + 1) ≫ sX (i + 1)) n' KS₀' (BS (i + 1)) h hU' hhb M.B :=
    fun F => MMP.Spreading.isDiscrepancy_of_linearlyEquivalent (hcrep' F)
      (MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor _ hS'v hKS₀' hKS')
  -- `p` and `h` contract the same curves
  have hcurves := fun C => isContractedBy_iff_of_isCrepantBoundary hSv hS'v hU hU' hp hh0 hpb hhb
    hKS₀ hKS₀' hcrep₀ hcrep₀' hhπ.symm hneg hpos C
  -- both are contractions
  have hWp := hAbs.isProjectiveVariety
  have hpproj : IsProjectiveMorphism p :=
    IsProjectiveMorphism.of_comp p (ι i ≫ sX i) (hp ▸ hWp.isProjective)
  have hhproj : IsProjectiveMorphism h :=
    IsProjectiveMorphism.of_comp h (ι (i + 1) ≫ sX (i + 1)) (hh0 ▸ hWp.isProjective)
  have hpapp := MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism _ _ hU.1 hSv p hpb
  have hhapp := MMP.Mori.isIso_app_of_isProper_of_isBirationalMorphism _ _ hU'.1 hS'v h hhb
  haveI : IsIso p.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ p.c fun U => hpapp U.unop
  haveI : IsIso h.c := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ h.c fun U => hhapp U.unop
  haveI : Surjective p := p.surjective_of_isIso_app hpapp
  haveI : Surjective h := h.surjective_of_isIso_app hhapp
  obtain ⟨φ, hφ⟩ := exists_iso_comp_eq_of_isContractedBy_iff hWp hSp hS'p hpproj hhproj hp hh0
    hcurves
  -- `φ` is compatible with the maps to `Z_i`, by uniqueness of the factorization through `p`
  refine ⟨φ, (MMP.Mori.existsUnique_comp_eq_of_isContractedBy hWp hSp
    (hC.isProjectiveVariety_base i) hpproj hp hπZ fun C hC x hx => ?_).unique rfl ?_⟩
  · simp only [Scheme.Hom.comp_apply, hC x hx]
  · rw [← Category.assoc, hφ, hhπ]

/-- **The stratum diagrams of a stabilized chain become isomorphisms.** Otherwise infinitely many
blocks are nonempty (`exists_iso_of_isNefOver`), and running them one after the other
(`exists_step`, `exists_isCrepantOver_succ`) gives an infinite sequence of elementary dlt steps
over the point, which `P₃` forbids (`false_of_forall_isAbsStep`). -/
private theorem IsStabilizedChain.exists_forall_ge_iso (hP : ProjectiveLowerLogMMP 3) {d : ℕ}
    (hC : IsStabilizedChain sX sZ f fp K B d ι BS) :
    ∃ N, ∀ i ≥ N, ∃ φ : S i ≅ S (i + 1), ι i ≫ f i = φ.hom ≫ ι (i + 1) ≫ fp i := by
  classical
  by_contra hcon
  have hni : ∀ N, ∃ i ≥ N, ¬ ∃ φ : S i ≅ S (i + 1), ι i ≫ f i = φ.hom ≫ ι (i + 1) ≫ fp i := by
    intro N
    by_contra h
    exact hcon ⟨N, fun i hi => by
      by_contra h'
      exact h ⟨i, hi, h'⟩⟩
  -- passing through empty blocks
  have hswitch : ∀ (k i j₀ : ℕ), j₀ - i = k → i ≤ j₀ →
      (¬ ∃ φ : S j₀ ≅ S (j₀ + 1), ι j₀ ≫ f j₀ = φ.hom ≫ ι (j₀ + 1) ≫ fp j₀) →
      ∀ (M : BlockModel) (p : M.W ⟶ S i), IsCrepantOver sX ι BS i M p →
      ∃ j ≥ i, ∃ p' : M.W ⟶ S j, IsCrepantOver sX ι BS j M p' ∧
        ¬ M.IsNefOver (p' ≫ ι j ≫ f j) := by
    intro k
    induction k with
    | zero =>
      intro i j₀ hk hij hj M p hp
      obtain rfl : i = j₀ := by omega
      refine ⟨i, le_rfl, p, hp, fun hn => hj (hC.exists_iso_of_isNefOver hp hn)⟩
    | succ k ih =>
      intro i j₀ hk hij hj M p hp
      by_cases hn : M.IsNefOver (p ≫ ι i ≫ f i)
      · obtain ⟨p', hp', -⟩ := hC.exists_isCrepantOver_succ (IsReachedOver.start M p hp) hn
        obtain ⟨j, hj', p'', hp'', hnn⟩ := ih (i + 1) j₀ (by omega) (by omega) hj M p' hp'
        exact ⟨j, by omega, p'', hp'', hnn⟩
      · exact ⟨i, le_rfl, p, hp, hn⟩
  have hfind : ∀ (i : ℕ) (M : BlockModel) (p : M.W ⟶ S i), IsCrepantOver sX ι BS i M p →
      ∃ j ≥ i, ∃ p' : M.W ⟶ S j, IsCrepantOver sX ι BS j M p' ∧
        ¬ M.IsNefOver (p' ≫ ι j ≫ f j) := by
    intro i M p hp
    obtain ⟨j₀, hj₀, hj⟩ := hni i
    exact hswitch (j₀ - i) i j₀ rfl hj₀ hj M p hp
  -- the states of the run: a pair reached in a block, with adjoint not nef over its base
  let State := {s : (i : ℕ) × (M : BlockModel) × (M.W ⟶ Z i) //
    IsReachedOver sX sZ f ι BS s.1 s.2.1 s.2.2 ∧ ¬ s.2.1.IsNefOver s.2.2}
  have hnext : ∀ s : State, ∃ s' : State, s.1.2.1.IsAbsStep s'.1.2.1 := by
    rintro ⟨⟨i, M, π⟩, hr, hnn⟩
    obtain ⟨M', π', habs, hr'⟩ := hC.exists_step hP hr hnn
    by_cases hn' : M'.IsNefOver π'
    · obtain ⟨p', hp', -⟩ := hC.exists_isCrepantOver_succ hr' hn'
      obtain ⟨j, -, p'', hp'', hnn''⟩ := hfind (i + 1) M' p' hp'
      exact ⟨⟨⟨j, M', p'' ≫ ι j ≫ f j⟩, IsReachedOver.start M' p'' hp'', hnn''⟩, habs⟩
    · exact ⟨⟨⟨i, M', π'⟩, hr', hn'⟩, habs⟩
  choose nxt hnxt using hnext
  obtain ⟨M₀, p₀, hp₀⟩ := hC.exists_isCrepantOver hP 0
  obtain ⟨j, -, p₁, hp₁, hnn₁⟩ := hfind 0 M₀ p₀ hp₀
  let s₀ : State := ⟨⟨j, M₀, p₁ ≫ ι j ≫ f j⟩, IsReachedOver.start M₀ p₁ hp₁, hnn₁⟩
  let Sq : ℕ → State := fun t => nxt^[t] s₀
  refine false_of_forall_isAbsStep hP (fun t => (Sq t).1.2.1)
    (fun t => (Sq t).2.1.isAbsModel) ?_ fun t => ?_
  · change topologicalKrullDim M₀.W ≤ 3
    rw [hp₀.2.2.1, hC.dim_eq 0]
    exact_mod_cast hC.le_three
  · change (Sq t).1.2.1.IsAbsStep (nxt^[t + 1] s₀).1.2.1
    rw [Function.iterate_succ_apply']
    exact hnxt (Sq t)

end Blocks

/-! ### From chains of adjunction pairs to the stratum diagrams -/

section ChainPairs

/-- **Equality of adjunction boundaries from equality of coefficients.** For an isomorphism
`e : S ≅ S'` over `Y`, if prime divisors of `S` and `S'` with the same valuation on the stalk of
`Y` at the common image of the generic points have the same coefficients in `B_S` and `B_{S'}`,
then `e_* B_S = B_{S'}`. -/
private theorem transformDivisor_eq_of_valuation_coeff_eq {Y S S' : Scheme.{0}} [IsIntegral S]
    [IsLocallyNoetherian S] [IsNormal S] [IsIntegral S'] [IsLocallyNoetherian S'] [IsNormal S']
    [IsSeparated (S' ↘ ⊤_ Scheme)] (e : S ≅ S') (g : S ⟶ Y) (g' : S' ⟶ Y)
    (hg : e.hom ≫ g' = g) (hcorr : g.base (genericPoint S) = g'.base (genericPoint S'))
    {BS : QDivisor S} {BS' : QDivisor S'}
    (h : ∀ (P : MMP.Mori.PrimeDivisor S) (P' : MMP.Mori.PrimeDivisor S'),
      P.divisorialValuation.comap (g.stalkMap (genericPoint S)).hom =
        P'.divisorialValuation.comap
          ((Y.presheaf.stalkCongr (.of_eq hcorr)).hom ≫ g'.stalkMap (genericPoint S')).hom →
      BS.coeff P = BS'.coeff P') :
    MMP.Mori.RationalMap.transformDivisor (X := S) e.hom.toRationalMap BS = BS' := by
  ext Q
  have hV : e.inv Q.genericPoint ∈ biregularLocus e.inv := by
    rw [top_le_iff.mp (le_biregularLocus (f := e.inv) (by change IsIso _; infer_instance))]
    trivial
  have hcoh : Order.coheight (e.inv Q.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus e.inv hV, Q.coheight_genericPoint]
  set P : MMP.Mori.PrimeDivisor S := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hP : e.hom P.genericPoint = Q.genericPoint := by
    have hPg : P.genericPoint = e.inv Q.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
    rw [hPg, ← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have htr : MMP.Mori.RationalMap.transformPrimeDivisor (X := S) e.hom.toRationalMap P = some Q :=
    (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e.hom P Q).mpr hP
  have huniq : ∀ P', MMP.Mori.RationalMap.transformPrimeDivisor (X := S) e.hom.toRationalMap P' =
      some Q → P' = P := by
    intro P' hP'
    have h1 := (MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff e.hom P' Q).mp hP'
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    have hinj : Function.Injective e.hom.base := by
      intro a b hab
      have := congrArg e.inv.base hab
      simpa [← Scheme.Hom.comp_apply] using this
    exact hinj (h1.trans hP.symm)
  rw [DivisorWithCoeffs.coeff_apply, MMP.Mori.RationalMap.transformDivisor,
    MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq htr huniq]
  exact h P Q (divisorialValuation_comap_stalkMap_eq_of_isIso e.hom g' g hg hcorr P Q hP)

variable {X Z : ℕ → Scheme.{0}} [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)]
  [∀ i, IsNormal (X i)] [∀ i, CompactSpace (X i)]
  {sX : ∀ i, X i ⟶ Spec (.of ℂ)} {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)}
  {f : ∀ i, X i ⟶ Z i} {fp : ∀ i, X (i + 1) ⟶ Z i}
  {K : ∀ i, Divisor (X i)} {B : ∀ i, QDivisor (X i)}

/-- Step `i` of a family of flips *fixes the adjunction strata whose dimension satisfies `p`*
(the family form of `StepFixesStrata`). -/
private def FamilyFixesStrata (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (f : ∀ i, X i ⟶ Z i)
    (fp : ∀ i, X (i + 1) ⟶ Z i) (B : ∀ i, QDivisor (X i)) (i : ℕ)
    (p : WithBot ℕ∞ → Prop) : Prop :=
  (∀ (T : Scheme.{0}) (ι : T ⟶ X i) (BT : QDivisor T),
    IsStratumAdjunctionPair (sX i) (B i) ι BT →
    IsDltStratum (sX i) (B i) (Set.range ι.base) →
    p (topologicalKrullDim T) →
    ∃ (T' : Scheme.{0}) (ι' : T' ⟶ X (i + 1)) (BT' : QDivisor T') (e : T ≅ T'),
      IsStratumAdjunctionPair (sX (i + 1)) (B (i + 1)) ι' BT' ∧
      IsDltStratum (sX (i + 1)) (B (i + 1)) (Set.range ι'.base) ∧
      ι ≫ f i = e.hom ≫ ι' ≫ fp i ∧
      RationalMap.transformDivisor e.hom.toRationalMap BT = BT') ∧
  (∀ (T' : Scheme.{0}) (ι' : T' ⟶ X (i + 1)) (BT' : QDivisor T'),
    IsStratumAdjunctionPair (sX (i + 1)) (B (i + 1)) ι' BT' →
    IsDltStratum (sX (i + 1)) (B (i + 1)) (Set.range ι'.base) →
    p (topologicalKrullDim T') →
    ∃ (T : Scheme.{0}) (ι : T ⟶ X i) (BT : QDivisor T) (e : T ≅ T'),
      IsStratumAdjunctionPair (sX i) (B i) ι BT ∧
      IsDltStratum (sX i) (B i) (Set.range ι.base) ∧
      ι ≫ f i = e.hom ≫ ι' ≫ fp i ∧
      RationalMap.transformDivisor e.hom.toRationalMap BT = BT')

/-- **The stratum diagrams become isomorphisms.** Along a family of flips of projective dlt
fourfolds over projective bases whose boundary strata of dimension `< d` avoid the flipping and
flipped loci, a chain of corresponding `d`-dimensional adjunction strata `S_i ⊆ X_i`, none inside
the flipping or flipped loci, eventually has isomorphisms `S_i ≅ S_{i+1}` over `Z_i`. -/
private theorem exists_forall_ge_iso_of_chain (hP : ProjectiveLowerLogMMP 3)
    (hX : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hZ : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sZ i))
    (hB : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i))
    (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 4)
    (hflip : ∀ i,
      IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i))
    (hBflip : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i))
    (hpos : ∀ i, ∃ K' : Divisor (X (i + 1)), K'.IsCanonicalDivisor (sX (i + 1)) 4 ∧
      (Divisor.toQDivisor K' + B (i + 1)).HasRelativelyAmpleMultiple (fp i))
    (hst1 : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T →
      ¬ T ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hst2 : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      ¬ T' ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1))))
    {d : ℕ} (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3)
    (hlow : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T → topologicalKrullDim T < d →
      Disjoint T (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hlow' : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      topologicalKrullDim T' < d → Disjoint T' (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1))))
    {S : ℕ → Scheme.{0}} [∀ i, IsIntegral (S i)] [∀ i, IsLocallyNoetherian (S i)]
    [∀ i, IsNormal (S i)] {ι : ∀ i, S i ⟶ X i} {BS : ∀ i, QDivisor (S i)}
    (hS : ∀ i, IsStratumAdjunctionPair (sX i) (B i) (ι i) (BS i))
    (hT : ∀ i, IsDltStratum (sX i) (B i) (Set.range (ι i).base))
    (hdim : ∀ i, topologicalKrullDim (S i) = d)
    (hcorr : ∀ i,
      (ι i ≫ f i).base (genericPoint (S i)) = (ι (i + 1) ≫ fp i).base (genericPoint (S (i + 1))))
    (hnot : ∀ i, ¬ Set.range (ι i).base ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hnot' : ∀ i,
      ¬ Set.range (ι (i + 1)).base ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1)))) :
    ∃ N, ∀ i ≥ N, ∃ φ : S i ≅ S (i + 1), ι i ≫ f i = φ.hom ≫ ι (i + 1) ≫ fp i := by
  obtain ⟨N₂, h₂⟩ := exists_forall_ge_isStratumAdjunctionPair_coeff_eq (k := ℂ) hX hB hK hflip
    hBflip hlow hlow' hS (fun i => (hdim i).le) hcorr
  have hC : IsStabilizedChain (X := fun j => X (N₂ + j)) (Z := fun j => Z (N₂ + j))
      (S := fun j => S (N₂ + j)) (fun j => sX (N₂ + j)) (fun j => sZ (N₂ + j))
      (fun j => f (N₂ + j)) (fun j => fp (N₂ + j)) (fun j => K (N₂ + j)) (fun j => B (N₂ + j)) d
      (fun j => ι (N₂ + j)) (fun j => BS (N₂ + j)) :=
    { isProjectiveVariety := fun j => hX _
      isProjectiveVariety_base := fun j => hZ _
      isDltPair := fun j => hB _
      isCanonicalDivisor := fun j => hK _
      isFlipOf := fun j => hflip _
      boundary_succ := fun j => hBflip _
      pos_sign := fun j => hpos _
      one_le := hd₁
      le_three := hd₃
      isStratumAdjunctionPair := fun j => hS _
      isDltStratum := fun j => hT _
      dim_eq := fun j => hdim _
      corr := fun j => hcorr _
      not_subset := fun j => hnot _
      not_subset' := fun j => hnot' _
      all_not_subset := fun j => hst1 _
      all_not_subset' := fun j => hst2 _
      small := fun j => (h₂ (N₂ + j) (by omega)).1
      coeff_eq := fun j P P' hv => (h₂ (N₂ + j) (by omega)).2 P P' (by
        rw [valuation_ofPrimeDivisor, valuation_ofPrimeDivisor]; exact hv) }
  obtain ⟨N, hN⟩ := hC.exists_forall_ge_iso hP
  refine ⟨N₂ + N, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = N₂ + j := ⟨i - N₂, by omega⟩
  exact hN j (by omega)

/-- **Stratum diagrams with stabilized boundaries.** Under the hypotheses of
`exists_forall_ge_iso_of_chain`, the isomorphisms `S_i ≅ S_{i+1}` over `Z_i` eventually carry the
adjunction boundary of `S_i` to that of `S_{i+1}`
(`MMP.Fourfold.exists_forall_ge_isStratumAdjunctionPair_coeff_eq`). -/
private theorem exists_forall_ge_iso_transformDivisor_of_chain (hP : ProjectiveLowerLogMMP 3)
    (hX : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hZ : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sZ i))
    (hB : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i))
    (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 4)
    (hflip : ∀ i,
      IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i))
    (hBflip : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i))
    (hpos : ∀ i, ∃ K' : Divisor (X (i + 1)), K'.IsCanonicalDivisor (sX (i + 1)) 4 ∧
      (Divisor.toQDivisor K' + B (i + 1)).HasRelativelyAmpleMultiple (fp i))
    (hst1 : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T →
      ¬ T ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hst2 : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      ¬ T' ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1))))
    {d : ℕ} (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3)
    (hlow : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T → topologicalKrullDim T < d →
      Disjoint T (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hlow' : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      topologicalKrullDim T' < d → Disjoint T' (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1))))
    {S : ℕ → Scheme.{0}} [∀ i, IsIntegral (S i)] [∀ i, IsLocallyNoetherian (S i)]
    [∀ i, IsNormal (S i)] {ι : ∀ i, S i ⟶ X i} {BS : ∀ i, QDivisor (S i)}
    (hS : ∀ i, IsStratumAdjunctionPair (sX i) (B i) (ι i) (BS i))
    (hT : ∀ i, IsDltStratum (sX i) (B i) (Set.range (ι i).base))
    (hdim : ∀ i, topologicalKrullDim (S i) = d)
    (hcorr : ∀ i,
      (ι i ≫ f i).base (genericPoint (S i)) = (ι (i + 1) ≫ fp i).base (genericPoint (S (i + 1))))
    (hnot : ∀ i, ¬ Set.range (ι i).base ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hnot' : ∀ i,
      ¬ Set.range (ι (i + 1)).base ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1)))) :
    ∃ N, ∀ i ≥ N, ∃ φ : S i ≅ S (i + 1), ι i ≫ f i = φ.hom ≫ ι (i + 1) ≫ fp i ∧
      MMP.Mori.RationalMap.transformDivisor (X := S i) φ.hom.toRationalMap (BS i) = BS (i + 1) := by
  obtain ⟨N₁, h₁⟩ := exists_forall_ge_iso_of_chain hP hX hZ hB hK hflip hBflip hpos hst1 hst2
    hd₁ hd₃ hlow hlow' hS hT hdim hcorr hnot hnot'
  obtain ⟨N₂, h₂⟩ := exists_forall_ge_isStratumAdjunctionPair_coeff_eq (k := ℂ) hX hB hK hflip
    hBflip hlow hlow' hS (fun i => (hdim i).le) hcorr
  refine ⟨max N₁ N₂, fun i hi => ?_⟩
  obtain ⟨φ, hφ⟩ := h₁ i (le_of_max_le_left hi)
  refine ⟨φ, hφ, ?_⟩
  have hn := (hS (i + 1)).some.isNormalVariety
  haveI : IsSeparated (ι (i + 1) ≫ sX (i + 1)) := hn.1.toIsSeparated
  haveI : IsSeparated (S (i + 1) ↘ ⊤_ Scheme) :=
    isSeparated_toTerminal (s := ι (i + 1) ≫ sX (i + 1))
  refine transformDivisor_eq_of_valuation_coeff_eq φ (ι i ≫ f i) (ι (i + 1) ≫ fp i) hφ.symm
    (hcorr i) fun P P' hv => (h₂ i (le_of_max_le_right hi)).2 P P' ?_
  rw [valuation_ofPrimeDivisor, valuation_ofPrimeDivisor]
  exact hv

/-- Adjunction pairs on the strata `T ⊆ X_i` and `T' ⊆ X_{i+1}` *correspond* along step `i`: each
adjunction pair on `T` is carried, by an isomorphism over `Z_i` preserving the boundaries, onto an
adjunction pair on `T'`, and conversely. -/
private def PairsCorrespond (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (f : ∀ i, X i ⟶ Z i)
    (fp : ∀ i, X (i + 1) ⟶ Z i) (B : ∀ i, QDivisor (X i)) (i : ℕ) (T : Set (X i))
    (T' : Set (X (i + 1))) : Prop :=
  (∀ (U : Scheme.{0}) (ι : U ⟶ X i) (BU : QDivisor U),
    IsStratumAdjunctionPair (sX i) (B i) ι BU → Set.range ι.base = T →
    ∃ (U' : Scheme.{0}) (ι' : U' ⟶ X (i + 1)) (BU' : QDivisor U') (e : U ≅ U'),
      IsStratumAdjunctionPair (sX (i + 1)) (B (i + 1)) ι' BU' ∧ Set.range ι'.base = T' ∧
      ι ≫ f i = e.hom ≫ ι' ≫ fp i ∧
      RationalMap.transformDivisor e.hom.toRationalMap BU = BU') ∧
  (∀ (U' : Scheme.{0}) (ι' : U' ⟶ X (i + 1)) (BU' : QDivisor U'),
    IsStratumAdjunctionPair (sX (i + 1)) (B (i + 1)) ι' BU' → Set.range ι'.base = T' →
    ∃ (U : Scheme.{0}) (ι : U ⟶ X i) (BU : QDivisor U) (e : U ≅ U'),
      IsStratumAdjunctionPair (sX i) (B i) ι BU ∧ Set.range ι.base = T ∧
      ι ≫ f i = e.hom ≫ ι' ≫ fp i ∧
      RationalMap.transformDivisor e.hom.toRationalMap BU = BU')

/-- The instances carried by an adjunction pair. -/
private theorem instances_of_isStratumAdjunctionPair {Y U : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)} {BY : QDivisor Y} {ι : U ⟶ Y} {BU : QDivisor U}
    (h : IsStratumAdjunctionPair sY BY ι BU) :
    IsIntegral U ∧ IsLocallyNoetherian U ∧ IsNormal U ∧ IsClosedImmersion ι ∧
      IsSeparated (U ↘ ⊤_ Scheme) := by
  have hn := h.some.isNormalVariety
  have := hn.1
  haveI : IsSeparated (ι ≫ sY) := hn.1.toIsSeparated
  exact ⟨hn.1.toIsIntegral, LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sY), hn.2,
    h.some.isClosedImmersion, isSeparated_toTerminal (s := ι ≫ sY)⟩

/-- **Along a chain of corresponding `d`-dimensional strata, the adjunction pairs eventually
correspond.** Choose adjunction pairs on the strata of the chain
(`MMP.Fourfold.IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair`), apply
`exists_forall_ge_iso_transformDivisor_of_chain`, and reach an arbitrary adjunction pair on a
stratum of the chain through the uniqueness of adjunction pairs on a stratum
(`exists_iso_transformDivisor_eq_of_range_eq`). -/
private theorem exists_forall_ge_pairsCorrespond_of_chain (hP : ProjectiveLowerLogMMP 3)
    (hX : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hZ : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sZ i))
    (hB : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i))
    (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 4)
    (hflip : ∀ i,
      IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i))
    (hBflip : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i))
    (hpos : ∀ i, ∃ K' : Divisor (X (i + 1)), K'.IsCanonicalDivisor (sX (i + 1)) 4 ∧
      (Divisor.toQDivisor K' + B (i + 1)).HasRelativelyAmpleMultiple (fp i))
    (hst1 : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T →
      ¬ T ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hst2 : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      ¬ T' ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1))))
    {d : ℕ} (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3)
    (hfix : ∀ i, FamilyFixesStrata sX f fp B i (· < d))
    (c : ∀ i, Set (X i)) (hc : ∀ i, IsDltStratum (sX i) (B i) (c i))
    (hcd : ∀ i, topologicalKrullDim (c i) = d)
    (hcc : ∀ i, closure ((f i).base '' c i) = closure ((fp i).base '' c (i + 1)))
    (hnot : ∀ i, ¬ c i ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hnot' : ∀ i, ¬ c (i + 1) ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1)))) :
    ∃ N, ∀ i ≥ N, PairsCorrespond sX f fp B i (c i) (c (i + 1)) := by
  choose Sc ιc BSc hr hpair using fun i =>
    (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair (hc i)).1.1
  have hinst := fun i => instances_of_isStratumAdjunctionPair (hpair i)
  haveI : ∀ i, IsIntegral (Sc i) := fun i => (hinst i).1
  haveI : ∀ i, IsLocallyNoetherian (Sc i) := fun i => (hinst i).2.1
  haveI : ∀ i, IsNormal (Sc i) := fun i => (hinst i).2.2.1
  haveI : ∀ i, IsClosedImmersion (ιc i) := fun i => (hinst i).2.2.2.1
  haveI : ∀ i, IsSeparated (Sc i ↘ ⊤_ Scheme) := fun i => (hinst i).2.2.2.2
  have hdimS : ∀ i, topologicalKrullDim (Sc i) = d := fun i => by
    rw [topologicalKrullDim_eq_range (ιc i), hr i, hcd i]
  have hcorr : ∀ i, (ιc i ≫ f i).base (genericPoint (Sc i)) =
      (ιc (i + 1) ≫ fp i).base (genericPoint (Sc (i + 1))) := fun i => by
    have h1 := closure_image_eq_closure_singleton (f := f i) ((hr i) ▸ isGenericPoint_range (ιc i))
    have h2 := closure_image_eq_closure_singleton (f := fp i)
      ((hr (i + 1)) ▸ isGenericPoint_range (ιc (i + 1)))
    rw [hcc i, h2] at h1
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact (isGenericPoint_closure.eq (h1 ▸ isGenericPoint_closure) : _).symm
  -- the lower strata, from `hfix`: a fixed stratum avoids the flip
  -- (`MMP.Fourfold.IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair`)
  have hB' : ∀ i, MMP.Intersection.IsDltPair (sX (i + 1)) (flipTransform (f i) (fp i) (B i)) :=
    fun i => hBflip i ▸ hB (i + 1)
  have hst2' : ∀ i (T' : Set (X (i + 1))),
      IsDltStratum (sX (i + 1)) (flipTransform (f i) (fp i) (B i)) T' →
      ¬ T' ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1))) :=
    fun i => hBflip i ▸ hst2 i
  have hlow : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T → topologicalKrullDim T < d →
      Disjoint T (MMP.Mori.exceptionalSet (f i) : Set (X i)) := by
    intro i T hT hd
    obtain ⟨U, j, BU, hjr, hU⟩ := (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hT).1.1
    obtain ⟨hU1, hU2, hU3, hU4, hU5⟩ := instances_of_isStratumAdjunctionPair hU
    have hdU : topologicalKrullDim U < d := by rw [topologicalKrullDim_eq_range j, hjr]; exact hd
    obtain ⟨U', j', BU', e, hU', -, hcomm, htr⟩ := (hfix i).1 U j BU hU (hjr ▸ hT) hdU
    have := (instances_of_isStratumAdjunctionPair hU').2.2.2.2
    have hU'f : IsStratumAdjunctionPair (sX (i + 1)) (flipTransform (f i) (fp i) (B i)) j' BU' :=
      hBflip i ▸ hU'
    have := (IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair (hX i) (hX (i + 1))
      (hK i) (hB i) (hB' i) (hflip i) (hst1 i) (hst2' i) hU hU'f e hcomm (by
        rw [← htr]; exact inverseTransformDivisor_transformDivisor_of_isIso _ _)).1
    rwa [hjr] at this
  have hlow' : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      topologicalKrullDim T' < d →
        Disjoint T' (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1))) := by
    intro i T' hT' hd
    obtain ⟨U', j', BU', hjr, hU'⟩ :=
      (IsDltStratum.exists_isStratumAdjunctionPair_and_isDltPair hT').1.1
    obtain ⟨hU1, hU2, hU3, hU4, hU5⟩ := instances_of_isStratumAdjunctionPair hU'
    have hdU : topologicalKrullDim U' < d := by
      rw [topologicalKrullDim_eq_range j', hjr]; exact hd
    obtain ⟨U, j, BU, e, hU, -, hcomm, htr⟩ := (hfix i).2 U' j' BU' hU' (hjr ▸ hT') hdU
    have := (instances_of_isStratumAdjunctionPair hU).1
    have := (instances_of_isStratumAdjunctionPair hU').2.2.2.2
    have hU'f : IsStratumAdjunctionPair (sX (i + 1)) (flipTransform (f i) (fp i) (B i)) j' BU' :=
      hBflip i ▸ hU'
    have := (IsFlipOf.disjoint_exceptionalSet_of_isStratumAdjunctionPair (hX i) (hX (i + 1))
      (hK i) (hB i) (hB' i) (hflip i) (hst1 i) (hst2' i) hU hU'f e hcomm (by
        rw [← htr]; exact inverseTransformDivisor_transformDivisor_of_isIso _ _)).2
    rwa [hjr] at this
  obtain ⟨N, hN⟩ := exists_forall_ge_iso_transformDivisor_of_chain hP hX hZ hB hK hflip hBflip hpos
    hst1 hst2 hd₁ hd₃ hlow hlow' hpair (fun i => (hr i).symm ▸ hc i) hdimS hcorr
    (fun i => (hr i).symm ▸ hnot i) (fun i => (hr (i + 1)).symm ▸ hnot' i)
  refine ⟨N, fun i hi => ?_⟩
  obtain ⟨φ, hφ, hφB⟩ := hN i hi
  refine ⟨fun U ι BU hU hUr => ?_, fun U' ι' BU' hU' hU'r => ?_⟩
  · obtain ⟨hU1, hU2, hU3, hU4, hU5⟩ := instances_of_isStratumAdjunctionPair hU
    have hdU : topologicalKrullDim U ≤ d := by rw [topologicalKrullDim_eq_range ι, hUr, hcd i]
    obtain ⟨e₁, he₁, he₁B⟩ := exists_iso_transformDivisor_eq_of_range_eq (hX i) (hB i) hU
      (hpair i) hdU (hdimS i).le (hUr.trans (hr i).symm)
    refine ⟨Sc (i + 1), ιc (i + 1), BSc (i + 1), e₁ ≪≫ φ, hpair (i + 1), hr (i + 1), ?_, ?_⟩
    · rw [← he₁, Category.assoc, hφ, Iso.trans_hom, Category.assoc]
    · rw [Iso.trans_hom, transformDivisor_comp_of_isIso, he₁B, hφB]
  · obtain ⟨hU1, hU2, hU3, hU4, hU5⟩ := instances_of_isStratumAdjunctionPair hU'
    have hdU : topologicalKrullDim U' ≤ d := by
      rw [topologicalKrullDim_eq_range ι', hU'r, hcd (i + 1)]
    obtain ⟨e₂, he₂, he₂B⟩ := exists_iso_transformDivisor_eq_of_range_eq (hX (i + 1))
      (hB (i + 1)) hU' (hpair (i + 1)) hdU (hdimS (i + 1)).le (hU'r.trans (hr (i + 1)).symm)
    refine ⟨Sc i, ιc i, BSc i, φ ≪≫ e₂.symm, hpair i, hr i, ?_, ?_⟩
    · rw [hφ, ← he₂, Iso.trans_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · rw [Iso.trans_hom, Iso.symm_hom, transformDivisor_comp_of_isIso, hφB, ← he₂B,
        transformDivisor_inv_transformDivisor]

/-- **Special termination on `d`-dimensional strata, for a family.** Along a family of flips of
projective dlt fourfolds over projective bases, in which every boundary stratum of `X_i` (resp.
`X_{i+1}`) misses the flipping (resp. flipped) locus generically and has a stratum with the same
image on the other side, and whose steps fix the strata of dimension `< d`, the steps eventually
fix the strata of dimension `d`. The `d`-strata of consecutive models correspond bijectively
through their images; there are finitely many, so finitely many chains, along each of which the
adjunction pairs eventually correspond (`exists_forall_ge_pairsCorrespond_of_chain`). -/
private theorem exists_forall_ge_familyFixesStrata (hP : ProjectiveLowerLogMMP 3)
    (hX : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hZ : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sZ i))
    (hB : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i))
    (hK : ∀ i, (K i).IsCanonicalDivisor (sX i) 4)
    (hflip : ∀ i,
      IsFlipOf (sX i) (sZ i) (sX (i + 1)) (Divisor.toQDivisor (K i) + B i) (f i) (fp i))
    (hBflip : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i))
    (hpos : ∀ i, ∃ K' : Divisor (X (i + 1)), K'.IsCanonicalDivisor (sX (i + 1)) 4 ∧
      (Divisor.toQDivisor K' + B (i + 1)).HasRelativelyAmpleMultiple (fp i))
    (hV : ∀ i, biregularLocus (fp i) ≤ biregularLocus (f i))
    (hst1 : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T →
      ¬ T ⊆ (MMP.Mori.exceptionalSet (f i) : Set (X i)))
    (hst2 : ∀ i (T' : Set (X (i + 1))), IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      ¬ T' ⊆ (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1))))
    (hst3 : ∀ i (T : Set (X i)), IsDltStratum (sX i) (B i) T →
      ∃ T' : Set (X (i + 1)), IsDltStratum (sX (i + 1)) (B (i + 1)) T' ∧
        closure ((f i).base '' T) = closure ((fp i).base '' T'))
    {d : ℕ} (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3) (hfix : ∀ i, FamilyFixesStrata sX f fp B i (· < d)) :
    ∃ N, ∀ i ≥ N, FamilyFixesStrata sX f fp B i (· = d) := by
  classical
  have hXv : ∀ i, IsNormalVariety ℂ (sX i) := fun i => (hB i).1.1.1
  haveI : ∀ i, LocallyOfFiniteType (sX i) := fun i => (hXv i).1.toLocallyOfFiniteType
  haveI : ∀ i, IsSeparated (Z i ↘ ⊤_ Scheme) := fun i => by
    haveI : IsSeparated (sZ i) := (hflip i).isContraction.isNormalVariety_target.1.toIsSeparated
    exact isSeparated_toTerminal (s := sZ i)
  let D : ∀ i, Set (Set (X i)) := fun i =>
    {T | IsDltStratum (sX i) (B i) T ∧ topologicalKrullDim T = d}
  let R : ∀ i, Set (X i) → Set (X (i + 1)) → Prop := fun i T T' =>
    T ∈ D i ∧ T' ∈ D (i + 1) ∧ closure ((f i).base '' T) = closure ((fp i).base '' T')
  have hdimeq : ∀ i (T : Set (X i)) (T' : Set (X (i + 1))), IsDltStratum (sX i) (B i) T →
      IsDltStratum (sX (i + 1)) (B (i + 1)) T' →
      closure ((f i).base '' T) = closure ((fp i).base '' T') →
      topologicalKrullDim T = topologicalKrullDim T' := fun i T T' hT hT' h =>
    topologicalKrullDim_eq_of_closure_image_eq (sX := sX i) (sX' := sX (i + 1)) (hK i).1
      (hK (i + 1)).1
      (isGenericPoint_of_isDltStratum hT) (isGenericPoint_of_isDltStratum hT')
      (map_mem_biregularLocus_of_not_subset (isGenericPoint_of_isDltStratum hT) (hst1 i T hT))
      (map_mem_biregularLocus_of_not_subset (isGenericPoint_of_isDltStratum hT')
        (hst2 i T' hT')) h
  have hfwd : ∀ i T, T ∈ D i → ∃ T', R i T T' := fun i T hT => by
    obtain ⟨T', hT', hcl⟩ := hst3 i T hT.1
    exact ⟨T', hT, ⟨hT', (hdimeq i T T' hT.1 hT' hcl).symm.trans hT.2⟩, hcl⟩
  have hbwd : ∀ i T', T' ∈ D (i + 1) → ∃ T, R i T T' := fun i T' hT' => by
    have hT'' : IsDltStratum (sX (i + 1)) (flipTransform (f i) (fp i) (B i)) T' :=
      hBflip i ▸ hT'.1
    obtain ⟨T, hT, hcl⟩ := exists_isDltStratum_of_isDltStratum_flipTransform
      (hflip i).isSmallMorphism.two_le_codimension (hV i) (hB i) hT'' (hst2 i T' hT'.1)
    exact ⟨T, ⟨hT, (hdimeq i T T' hT hT'.1 hcl).trans hT'.2⟩, hT', hcl⟩
  have hfun : ∀ i T T₁ T₂, R i T T₁ → R i T T₂ → T₁ = T₂ := fun i T T₁ T₂ h₁ h₂ =>
    eq_of_closure_image_eq (isGenericPoint_of_isDltStratum h₁.2.1.1)
      (isGenericPoint_of_isDltStratum h₂.2.1.1) (hst2 i _ h₁.2.1.1) (hst2 i _ h₂.2.1.1)
      (h₁.2.2.symm.trans h₂.2.2)
  have hD0 : (D 0).Finite :=
    (finite_setOf_isDltStratum (sX := sX 0) (B 0)).subset fun T hT => hT.1
  obtain ⟨N, hN⟩ := exists_forall_ge_of_chains D R hD0 (fun j a b h => ⟨h.1, h.2.1⟩) hfwd hbwd
    hfun (fun i => PairsCorrespond sX f fp B i) fun c hc =>
      exists_forall_ge_pairsCorrespond_of_chain hP hX hZ hB hK hflip hBflip hpos hst1 hst2 hd₁ hd₃
        hfix c
        (fun i => (hc i).1.1) (fun i => (hc i).1.2) (fun i => (hc i).2.2)
        (fun i => hst1 i _ (hc i).1.1) (fun i => hst2 i _ (hc i).2.1.1)
  refine ⟨N, fun i hi => ⟨fun T ι BT hpair hstr hdT => ?_, fun T' ι' BT' hpair hstr hdT => ?_⟩⟩
  · obtain ⟨-, -, -, hci, -⟩ := instances_of_isStratumAdjunctionPair hpair
    have hmem : Set.range ι.base ∈ D i := ⟨hstr, (topologicalKrullDim_eq_range ι).symm.trans hdT⟩
    obtain ⟨T', hR⟩ := hfwd i _ hmem
    obtain ⟨U', ι'', BU', e, hp', hr', hc', ht'⟩ := (hN i hi _ _ hR).1 T ι BT hpair rfl
    exact ⟨U', ι'', BU', e, hp', hr' ▸ hR.2.1.1, hc', ht'⟩
  · obtain ⟨-, -, -, hci, -⟩ := instances_of_isStratumAdjunctionPair hpair
    have hmem : Set.range ι'.base ∈ D (i + 1) :=
      ⟨hstr, (topologicalKrullDim_eq_range ι').symm.trans hdT⟩
    obtain ⟨T, hR⟩ := hbwd i _ hmem
    obtain ⟨U, ι'', BU, e, hp, hr, hc', ht'⟩ := (hN i hi _ _ hR).2 T' ι' BT' hpair rfl
    exact ⟨U, ι'', BU, e, hp, hr ▸ hR.1.1, hc', ht'⟩

end ChainPairs

/-- A property of the steps `i` with `i + 1 < L` holds eventually when `L` is finite: it is
vacuous from `L` on. -/
private theorem eventually_of_ne_top {L : ℕ∞} (hL : L ≠ ⊤)
    {Q : ∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < L → Prop} :
    ∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < L, Q i hi := by
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.mp hL
  refine eventually_atTop.2 ⟨m, fun i hi h => absurd h ?_⟩
  exact not_lt.2 (Nat.cast_le.2 (by omega))

/-- **Special termination on `d`-dimensional strata, on a tail.** For an infinite sequence of
flips whose models from `N` on are projective and dlt, with projective contraction targets, and
whose steps from `N` on fix the strata of dimension `< d`, the steps eventually fix the strata of
dimension `d`: from the step `M` of `exists_forall_ge_strata_not_subset` on, the shifted sequence
is a family as in `exists_forall_ge_familyFixesStrata`. -/
private theorem eventually_stepFixesStrata_of_forall_ge (hP : ProjectiveLowerLogMMP 3)
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    (S : SequenceOfFlips sX 4 K B) (hL : S.length = ⊤) (N : ℕ)
    (hproj : ∀ i ≥ N, MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1)
    (hbase : ∀ i ≥ N, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i))
    (hdlt : ∀ i ≥ N, ∀ hi : (i : ℕ∞) < S.length,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI : IsIntegral (S.model i).1 := (S.isNormalVariety_model i hi).1.toIsIntegral
      MMP.Intersection.IsDltPair (S.model i).2.1 (S.model i).2.2.2)
    (d : ℕ) (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3)
    (hfix : ∀ i ≥ N, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length, StepFixesStrata S i hi (· < d)) :
    ∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length,
      StepFixesStrata S i hi (· = d) := by
  obtain ⟨M, hMN, hM⟩ := exists_forall_ge_strata_not_subset S hL N hproj hbase hdlt
  have hlt : ∀ i : ℕ, (i : ℕ∞) < S.length := fun i => hL ▸ ENat.coe_lt_top i
  haveI : ∀ j, IsLocallyNoetherian (S.model (M + j)).1 := fun j => S.isLocallyNoetherian_model _
  haveI : ∀ j, IsNormal (S.model (M + j)).1 := fun j => S.isNormal_model _
  haveI : ∀ j, CompactSpace (S.model (M + j)).1 := fun j => S.compactSpace_model _
  haveI : ∀ j, IsIntegral (S.model (M + j)).1 := fun j =>
    (S.isNormalVariety_model _ (hlt _)).1.toIsIntegral
  have hV : ∀ j, biregularLocus (S.flip (M + j)) ≤ biregularLocus (S.contraction (M + j)) := by
    intro j
    haveI := S.isLocallyNoetherian_model (M + j + 1)
    haveI := S.isNormal_model (M + j + 1)
    haveI := S.compactSpace_model (M + j + 1)
    have h := S.isFlip (M + j) (hlt _)
    rw [logCanonicalDivisor_eq] at h
    exact biregularLocus_flip_le_of_isFlip h
  haveI : ∀ j, IsLocallyNoetherian (S.model (M + j + 1)).1 := fun j =>
    S.isLocallyNoetherian_model _
  haveI : ∀ j, IsNormal (S.model (M + j + 1)).1 := fun j => S.isNormal_model _
  haveI : ∀ j, CompactSpace (S.model (M + j + 1)).1 := fun j => S.compactSpace_model _
  have hpos : ∀ j, ∃ K' : Divisor (S.model (M + j + 1)).1,
      K'.IsCanonicalDivisor (S.model (M + j + 1)).2.1 4 ∧
      (Divisor.toQDivisor K' + (S.model (M + j + 1)).2.2.2).HasRelativelyAmpleMultiple
        (S.flip (M + j)) := by
    intro j
    haveI := S.isLocallyNoetherian_model (M + j + 1)
    haveI := S.isNormal_model (M + j + 1)
    haveI := S.compactSpace_model (M + j + 1)
    haveI : IsIntegral (S.model (M + j + 1)).1 :=
      (S.isNormalVariety_model _ (hlt _)).1.toIsIntegral
    have hfl := isFlipOf_of_sequenceOfFlips S (M + j) (hlt _) (hbase _ (by omega))
    have hamp := hfl.hasRelativelyAmpleMultiple_flip
    have htr : flipTransform (S.contraction (M + j)) (S.flip (M + j))
        (Divisor.toQDivisor (S.model (M + j)).2.2.1 + (S.model (M + j)).2.2.2) =
        Divisor.toQDivisor (flipTransform (S.contraction (M + j)) (S.flip (M + j))
          (S.model (M + j)).2.2.1) + (S.model (M + j + 1)).2.2.2 := by
      rw [map_add, boundary_succ_eq_flipTransform S (M + j) (hlt _)]
      congr 1
      exact flipTransform_mapCoeffsAddMonoidHom _ _ _ _
    rw [htr] at hamp
    refine ⟨_, ?_, hamp⟩
    have hZv := hfl.isContraction.isNormalVariety_target
    haveI : IsProper (S.contraction (M + j)) :=
      isProper_of_isProjectiveMorphism _ hfl.isContraction.isProjectiveMorphism
    haveI : IsIso (S.contraction (M + j) ∣_ biregularLocus (S.contraction (M + j))) :=
      isBiregular_biregularLocus _
    haveI : IsIso (S.flip (M + j) ∣_ biregularLocus (S.contraction (M + j))) :=
      isIso_flip_morphismRestrict_biregularLocus S (M + j) (hlt _)
    have hc := hfl.isContraction.comp_eq
    have hc' := hfl.isSmallMorphism_flip.comp_eq
    have hXv : IsNormalVariety ℂ (S.contraction (M + j) ≫ S.baseStr (M + j)) := by
      rw [hc]; exact hfl.isContraction.isNormalVariety_source
    have hX'v : IsNormalVariety ℂ (S.flip (M + j) ≫ S.baseStr (M + j)) := by
      rw [hc']; exact hfl.isSmallMorphism_flip.isNormalVariety_source
    have hK' : (S.model (M + j)).2.2.1.IsCanonicalDivisor
        (S.contraction (M + j) ≫ S.baseStr (M + j)) 4 := by
      rw [hc]; exact S.isCanonicalDivisor_model _ (hlt _)
    have h := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict hZv hXv hX'v
      hfl.isSmallMorphism.isBirationalMorphism hfl.isSmallMorphism_flip.isBirationalMorphism
      (biregularLocus (S.contraction (M + j)))
      (fun x hx => by
        by_contra hc0
        have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
          hfl.isSmallMorphism.two_le_codimension x (MMP.Mori.mem_exceptionalSet.mpr hc0)
        exact absurd (this.trans hx) (by decide))
      (fun x hx => by
        refine hV j ?_
        by_contra hc0
        have := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp
          hfl.isSmallMorphism_flip.two_le_codimension x (MMP.Mori.mem_exceptionalSet.mpr hc0)
        exact absurd (this.trans hx) (by decide)) hK'
    rwa [hc'] at h
  obtain ⟨N', hN'⟩ := exists_forall_ge_familyFixesStrata (X := fun j => (S.model (M + j)).1)
    (Z := fun j => S.base (M + j)) (sX := fun j => (S.model (M + j)).2.1)
    (sZ := fun j => S.baseStr (M + j)) (f := fun j => S.contraction (M + j))
    (fp := fun j => S.flip (M + j)) (K := fun j => (S.model (M + j)).2.2.1)
    (B := fun j => (S.model (M + j)).2.2.2) hP
    (fun j => hproj _ (by omega)) (fun j => hbase _ (by omega))
    (fun j => hdlt _ (by omega) (hlt _)) (fun j => S.isCanonicalDivisor_model _ (hlt _))
    (fun j => isFlipOf_of_sequenceOfFlips S (M + j) (hlt _) (hbase _ (by omega)))
    (fun j => boundary_succ_eq_flipTransform S (M + j) (hlt _)) hpos hV
    (fun j => (hM (M + j) (by omega)).1) (fun j => (hM (M + j) (by omega)).2.1)
    (fun j => (hM (M + j) (by omega)).2.2) hd₁ hd₃ (fun j => hfix (M + j) (by omega) (hlt _))
  refine eventually_atTop.2 ⟨M + N', fun i hi _ => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = M + j := ⟨i - M, by omega⟩
  exact hN' j (by omega)

/-- **Special termination on `d`-dimensional strata, infinite case.** It suffices to work on a
tail where all the hypotheses hold. -/
private theorem eventually_stepFixesStrata_of_length_eq_top (hP : ProjectiveLowerLogMMP 3)
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (hdim : topologicalKrullDim X = 4) (S : SequenceOfFlips sX 4 K B) (hL : S.length = ⊤)
    (hproj : ∀ᶠ i : ℕ in atTop, (i : ℕ∞) < S.length →
      MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1)
    (hbase : ∀ᶠ i : ℕ in atTop, ((i + 1 : ℕ) : ℕ∞) < S.length →
      MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i))
    (hdlt : ∀ᶠ i : ℕ in atTop, ∀ hi : (i : ℕ∞) < S.length,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI : IsIntegral (S.model i).1 := (S.isNormalVariety_model i hi).1.toIsIntegral
      MMP.Intersection.IsDltPair (S.model i).2.1 (S.model i).2.2.2)
    (d : ℕ) (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3)
    (hfix : ∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length,
      StepFixesStrata S i hi (· < d)) :
    ∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length,
      StepFixesStrata S i hi (· = d) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hproj.and (hbase.and (hdlt.and hfix)))
  have hlt : ∀ i : ℕ, ((i : ℕ) : ℕ∞) < S.length := fun i => hL ▸ ENat.coe_lt_top i
  exact eventually_stepFixesStrata_of_forall_ge hP S hL N
    (fun i hi => (hN i hi).1 (hlt i)) (fun i hi => (hN i hi).2.1 (hlt (i + 1)))
    (fun i hi => (hN i hi).2.2.1) d hd₁ hd₃ (fun i hi => (hN i hi).2.2.2)

/-- **Termination of the induced stratum diagrams.** Assume `ProjectiveLowerLogMMP 3`. Let
`(X_i, B_i)` be a sequence of flips of rational pairs on a fourfold whose models are, along a
tail, projective and dlt, with projective contraction targets `Z_i`, and let `1 ≤ d ≤ 3`.
Suppose that along a tail every step fixes all boundary strata of dimension less than `d`: each
such adjunction stratum `(S, B_S)` of `(X_i, B_i)` is isomorphic over `Z_i`, as a pair, to an
adjunction stratum of `(X_{i+1}, B_{i+1})`, and conversely. Then along a further tail every
step fixes in the same sense all boundary strata of dimension `d`. -/
@[mmp "lem_mmp_projective_stratum_diagrams_terminate"]
public theorem SequenceOfFlips.eventually_stratumAdjunctionPair_iso_of_projectiveLowerLogMMP
    (hP : ProjectiveLowerLogMMP 3)
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] {K : Divisor X} {B : QDivisor X}
    (hdim : topologicalKrullDim X = 4) (S : SequenceOfFlips sX 4 K B)
    (hproj : ∀ᶠ i : ℕ in atTop, (i : ℕ∞) < S.length →
      MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1)
    (hbase : ∀ᶠ i : ℕ in atTop, ((i + 1 : ℕ) : ℕ∞) < S.length →
      MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i))
    (hdlt : ∀ᶠ i : ℕ in atTop, ∀ hi : (i : ℕ∞) < S.length,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI : IsIntegral (S.model i).1 := (S.isNormalVariety_model i hi).1.toIsIntegral
      MMP.Intersection.IsDltPair (S.model i).2.1 (S.model i).2.2.2)
    (d : ℕ) (hd₁ : 1 ≤ d) (hd₃ : d ≤ 3)
    (hfix : ∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.isLocallyNoetherian_model (i + 1)
      haveI := S.isNormal_model (i + 1)
      haveI : IsIntegral (S.model i).1 :=
        (S.isNormalVariety_model i (lt_of_le_of_lt (by exact_mod_cast i.le_succ) hi)).1.toIsIntegral
      haveI : IsIntegral (S.model (i + 1)).1 := (S.isNormalVariety_model (i + 1) hi).1.toIsIntegral
      (∀ (T : Scheme.{0}) (ι : T ⟶ (S.model i).1) (BT : QDivisor T),
        IsStratumAdjunctionPair (S.model i).2.1 (S.model i).2.2.2 ι BT →
        IsDltStratum (S.model i).2.1 (S.model i).2.2.2 (Set.range ι.base) →
        topologicalKrullDim T < d →
        ∃ (T' : Scheme.{0}) (ι' : T' ⟶ (S.model (i + 1)).1) (BT' : QDivisor T') (e : T ≅ T'),
          IsStratumAdjunctionPair (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 ι' BT' ∧
          IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 (Set.range ι'.base) ∧
          ι ≫ S.contraction i = e.hom ≫ ι' ≫ S.flip i ∧
          RationalMap.transformDivisor e.hom.toRationalMap BT = BT') ∧
      (∀ (T' : Scheme.{0}) (ι' : T' ⟶ (S.model (i + 1)).1) (BT' : QDivisor T'),
        IsStratumAdjunctionPair (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 ι' BT' →
        IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 (Set.range ι'.base) →
        topologicalKrullDim T' < d →
        ∃ (T : Scheme.{0}) (ι : T ⟶ (S.model i).1) (BT : QDivisor T) (e : T ≅ T'),
          IsStratumAdjunctionPair (S.model i).2.1 (S.model i).2.2.2 ι BT ∧
          IsDltStratum (S.model i).2.1 (S.model i).2.2.2 (Set.range ι.base) ∧
          ι ≫ S.contraction i = e.hom ≫ ι' ≫ S.flip i ∧
          RationalMap.transformDivisor e.hom.toRationalMap BT = BT')) :
    ∀ᶠ i : ℕ in atTop, ∀ hi : ((i + 1 : ℕ) : ℕ∞) < S.length,
      haveI := S.isLocallyNoetherian_model i
      haveI := S.isNormal_model i
      haveI := S.isLocallyNoetherian_model (i + 1)
      haveI := S.isNormal_model (i + 1)
      haveI : IsIntegral (S.model i).1 :=
        (S.isNormalVariety_model i (lt_of_le_of_lt (by exact_mod_cast i.le_succ) hi)).1.toIsIntegral
      haveI : IsIntegral (S.model (i + 1)).1 := (S.isNormalVariety_model (i + 1) hi).1.toIsIntegral
      (∀ (T : Scheme.{0}) (ι : T ⟶ (S.model i).1) (BT : QDivisor T),
        IsStratumAdjunctionPair (S.model i).2.1 (S.model i).2.2.2 ι BT →
        IsDltStratum (S.model i).2.1 (S.model i).2.2.2 (Set.range ι.base) →
        topologicalKrullDim T = d →
        ∃ (T' : Scheme.{0}) (ι' : T' ⟶ (S.model (i + 1)).1) (BT' : QDivisor T') (e : T ≅ T'),
          IsStratumAdjunctionPair (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 ι' BT' ∧
          IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 (Set.range ι'.base) ∧
          ι ≫ S.contraction i = e.hom ≫ ι' ≫ S.flip i ∧
          RationalMap.transformDivisor e.hom.toRationalMap BT = BT') ∧
      (∀ (T' : Scheme.{0}) (ι' : T' ⟶ (S.model (i + 1)).1) (BT' : QDivisor T'),
        IsStratumAdjunctionPair (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 ι' BT' →
        IsDltStratum (S.model (i + 1)).2.1 (S.model (i + 1)).2.2.2 (Set.range ι'.base) →
        topologicalKrullDim T' = d →
        ∃ (T : Scheme.{0}) (ι : T ⟶ (S.model i).1) (BT : QDivisor T) (e : T ≅ T'),
          IsStratumAdjunctionPair (S.model i).2.1 (S.model i).2.2.2 ι BT ∧
          IsDltStratum (S.model i).2.1 (S.model i).2.2.2 (Set.range ι.base) ∧
          ι ≫ S.contraction i = e.hom ≫ ι' ≫ S.flip i ∧
          RationalMap.transformDivisor e.hom.toRationalMap BT = BT') := by
  by_cases hL : S.length = ⊤
  · exact eventually_stepFixesStrata_of_length_eq_top hP hdim S hL hproj hbase hdlt d hd₁ hd₃ hfix
  · exact eventually_of_ne_top hL

end MMP.Fourfold
