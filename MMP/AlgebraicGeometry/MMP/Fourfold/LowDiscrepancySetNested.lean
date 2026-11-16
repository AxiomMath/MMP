module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
import MMP.AlgebraicGeometry.MMP.Fourfold.GraphDivisor
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Resolution.OrderReduction.RegularStalkComponents
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.LowDiscrepancyJunction
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.AmpleModelGraphDivisor
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.RingTheory.SerreCondition.ExtSupportCriterion
import MMP.AlgebraicGeometry.RegularEmbedding.ExceptionalBundle
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.MMP.Fourfold.MinimalModel.AmpleModelSmall

/-!
# Low-discrepancy sets along small threefold steps

Let `(X⁻, B⁻) → Z ← (X⁺, B⁺)` be a threefold step diagram (`MMP.Fourfold.IsThreefoldStepDiagram`)
whose negative contraction `f⁻` is small and whose negative pair `(X⁻, B⁻)` is klt. Then the
positive pair `(X⁺, B⁺)`, with `B⁺ = (f⁺)⁻¹_* f⁻_* B⁻`, is klt, its low-discrepancy set
`I(X⁺, B⁺)` is contained in `I(X⁻, B⁻)`, and `I(X⁻, B⁻)` is finite.

The heart of this is the comparison `a(ξ; X⁻, B⁻) ≤ a(ξ; X⁺, B⁺)` of log discrepancies along
the step (Kollár–Mori 3.38): on a common normal model `Y` of `X⁻` and `X⁺` over `Z` on which `ξ`
is a prime divisor, the difference `H = Δ_Y⁺ - Δ_Y⁻` of the crepant boundaries is nef over `Z`
and vanishes off the exceptional divisors of `Y ⟶ Z`, so `H ≤ 0` by the negativity lemma.
Exceptionality over `X⁺` and over `X⁻` agree because `f⁻` is small.

Along a sequence of such steps, starting from a klt pair, every pair is klt and the cardinalities
of the finite sets `I(X_i, B_i)` are nonincreasing, so the sets are eventually constant. Along a
stabilized tail (`MMP.Fourfold.StabilizedTail`), log discrepancies do not decrease, the strict
transform is a coefficient-preserving bijection of prime divisors, and every boundary `B_i` has
the nonzero coefficients of `B_0`, which lie in `[0, 1)`.

## Main results

* `MMP.Fourfold.IsThreefoldStepDiagram.lowDiscrepancySet_subset_of_isSmallMorphism`: along a
  small step from a klt pair, `(X⁺, B⁺)` is klt and `I(X⁺, B⁺) ⊆ I(X⁻, B⁻)`, a finite set.
* `MMP.Fourfold.isKltPair_and_exists_lowDiscrepancySet_eq_of_isSmallMorphism`: along a sequence
  of small steps from a klt pair, every pair is klt and the low-discrepancy sets stabilize.
* `MMP.Fourfold.StabilizedTail.finite_and_monotone_and_frange_eq`: the basic properties of a
  stabilized tail.

## Implementation notes

The sets `I(X^±, B^±)` are sets of valuations of the two function fields `k(X^±)`; they are
compared after transporting both to `k(Z)` along the birational morphisms `f^±`
(`MMP.Fourfold.valuationsOver`), the identification `k(X⁻) ≅ k(Z) ≅ k(X⁺)` the source uses.
Along a sequence of steps, `I(X_i, B_i) = I(X_{i₀}, B_{i₀})` for `i ≥ i₀` (under the composite
identifications) is stated as `I(X_i, B_i) = I(X_{i+1}, B_{i+1})` in `k(Z_i)` for `i ≥ i₀`, the
convention of `MMP.Fourfold.StabilizedTail`; likewise monotonicity of `a_i(ξ)` is stated step by
step, for valuations of `k(X_i)` and `k(X_{i+1})` agreeing on `k(Z_i)`.

The comparison of log discrepancies is proved on the common model given by
`MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq`
with the comparison divisor of `MMP.Mori.isRelativelyNef_of_isDiscrepancy_sub`. The negativity
lemma is applied in the form `MMP.Flips.isEffective_of_isNumericallyEquivalentOver_pullback`,
after translating relative nefness of `ℚ`-divisors into relative nefness of `ℝ`-divisors.

The set `Γ` of coefficients of `B_0` is `Finsupp.frange`, the finite set of nonzero
coefficients; coefficient `0` lies in `[0, 1)` in any case.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.36 and 3.38
* [OpenAI, *Projective lc fourfolds*][OAI4], the index chain
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori

/-! ### Counting -/

/-- Pulling back valuations along a surjective ring hom is injective. -/
private lemma comap_injective {R S Γ : Type*} [Ring R] [Ring S] [LinearOrderedCommMonoidWithZero Γ]
    {φ : R →+* S} (hφ : Function.Surjective φ) :
    Function.Injective (fun ξ : Valuation S Γ => ξ.comap φ) := by
  intro ξ η h
  ext x
  obtain ⟨y, rfl⟩ := hφ x
  exact congrArg (fun v : Valuation R Γ => v y) h

/-- If finite sets `A i` are transported injectively by `g i` and `g' i` into common types
`β i`, with `g' i '' A (i + 1) ⊆ g i '' A i`, then the inclusions are eventually equalities. -/
private lemma exists_image_eq_of_image_subset {α β : ℕ → Type*} {A : ∀ i, Set (α i)}
    {g : ∀ i, α i → β i} {g' : ∀ i, α (i + 1) → β i}
    (hg : ∀ i, (g i).Injective) (hg' : ∀ i, (g' i).Injective) (hA : ∀ i, (A i).Finite)
    (hsub : ∀ i, g' i '' A (i + 1) ⊆ g i '' A i) :
    ∃ i₀, ∀ i ≥ i₀, g i '' A i = g' i '' A (i + 1) := by
  have hanti : Antitone fun i => (A i).ncard := antitone_nat_of_succ_le fun i => by
    rw [← Set.ncard_image_of_injective _ (hg' i), ← Set.ncard_image_of_injective _ (hg i)]
    exact Set.ncard_le_ncard (hsub i) ((hA i).image _)
  refine ⟨Function.argmin fun i => (A i).ncard, fun i hi => ?_⟩
  refine (Set.eq_of_subset_of_ncard_le (hsub i) ?_ ((hA i).image _)).symm
  rw [Set.ncard_image_of_injective _ (hg i), Set.ncard_image_of_injective _ (hg' i)]
  exact (hanti hi).trans (Function.argmin_le (fun i => (A i).ncard) (i + 1))

/-- Two finitely supported functions related by a bijection of their domains preserving values
have the same set of nonzero values. -/
private theorem frange_eq_of_equiv {α β M : Type*} [Zero M] [DecidableEq M] (f : α →₀ M)
    (g : β →₀ M) (e : α ≃ β) (he : ∀ a, g (e a) = f a) : g.frange = f.frange := by
  ext c
  simp only [Finsupp.mem_frange]
  constructor
  · rintro ⟨hc, b, rfl⟩
    exact ⟨hc, e.symm b, by rw [← he, e.apply_symm_apply]⟩
  · rintro ⟨hc, a, rfl⟩
    exact ⟨hc, e a, he a⟩

/-! ### Relative nefness -/

section Nef

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
  [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y}

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-nef. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple [CompactSpace X] {D : QDivisor X}
    (hD : D.HasRelativelyAmpleMultiple f) : D.IsRelativelyNef sX f := by
  obtain ⟨N, hN, L, hL, hLD, hLa⟩ := hD
  have hDq : D.IsQCartier := ⟨N, by exact_mod_cast hN.ne', L, hLD, hL⟩
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hDq fun C hC => ?_
  rw [QDivisor.intersectionNumber_eq_of_smul k sX C.ι C.dim_le D hDq hN L hL hLD]
  have := hL.isInvertibleModule_divisorialSheaf
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _
    hLa C hC
  have : (0 : ℚ) ≤ (L.degreeOn k sX C.ι C.dim_le hL : ℚ) := by exact_mod_cast hpos.le
  positivity

end Nef

/-! ### The negativity lemma -/

section Negativity

open MMP.Flips

variable (k : Type) [Field k] {Z Y : Scheme.{0}}

/-- A prime divisor exceptional for a morphism `h` (as a rational map) is mapped to a point of
coheight at least two. -/
private theorem two_le_coheight_of_isExceptional {h : Y ⟶ Z} {P : MMP.Mori.PrimeDivisor Y}
    (hP : RationalMap.IsExceptional (X := Y) h.toRationalMap P) :
    2 ≤ Order.coheight (h P.genericPoint) := by
  have hdef : RationalMap.DefinedAt (X := Y) h.toRationalMap P.genericPoint :=
    RationalMap.definedAt_iff.2 ⟨h.toPartialMap, trivial, rfl⟩
  have h2 := (RationalMap.isExceptional_iff.1 hP) hdef
  refine (MMP.Flips.le_closedsCodimension_iff_le_coheight.1 h2) _ ?_
  have hsub := RationalMap.image_subset_transform h.toPartialMap rfl P.idealSheaf.support
  refine hsub ⟨⟨P.genericPoint, trivial⟩, ?_, ?_⟩
  · exact primeDivisor_genericPoint_mem_support P
  · rw [Scheme.Hom.toPartialMap_hom]
    rfl

/-- **Negativity lemma, KM form.** Let `h : Y ⟶ Z` be a proper birational morphism of normal
varieties and `H` a `ℚ`-divisor on `Y` which is `h`-nef and has coefficient `0` along every prime
divisor not exceptional over `Z`. Then `-H` is effective. -/
private theorem coeff_nonpos_of_isRelativelyNef (sZ : Z ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [QuasiCompact sY] [IsLocallyNoetherian Z] [IsNormal Z] [IsLocallyNoetherian Y] [IsNormal Y]
    (hZ : IsNormalVariety k sZ) (hY : IsNormalVariety k sY) (h : Y ⟶ Z) (hh : h ≫ sZ = sY)
    [IsProper h] (hhb : IsBirationalMorphism h) {H : QDivisor Y}
    (hnef : H.IsRelativelyNef sY h)
    (hzero : ∀ F, ¬ RationalMap.IsExceptional (X := Y) h.toRationalMap F → H.coeff F = 0)
    (F : MMP.Mori.PrimeDivisor Y) : H.coeff F ≤ 0 := by
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have hMnef := Oai4C1.Negativity.isRelativelyNef_toRDivisor hnef
  have hM := Oai4C1.Negativity.isCartierCombination_of_isRelativelyNef hMnef
  have hB := Oai4C1.Negativity.isCartierCombination_neg hM
  have h0 : IsCartierCombination (0 : RDivisor Y) := Oai4C1.Negativity.isCartierCombination_zero
  have hL0 : IsCartierCombination (0 : RDivisor Z) := Oai4C1.Negativity.isCartierCombination_zero
  have hL'0 : IsRCartierPullback h (0 : RDivisor Z) (0 : RDivisor Y) :=
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
  have hBG : ∀ P : MMP.Mori.PrimeDivisor Y, ¬ IsExceptionalPrimeDivisor sZ h P →
      0 ≤ (-QDivisor.toRDivisor H).coeff P := by
    intro P hP
    have hY' : IsNormalVariety k (h ≫ sZ) := hh ▸ hY
    have hPm : ¬ RationalMap.IsExceptional (X := Y) h.toRationalMap P := fun hex => by
      have hnot := ProperDivisorOver.not_two_le_coheight_of_not_isExceptional
        (ProperDivisorOver.mk ⟨Y, h, hY', hhb, P⟩ inferInstance)
        (fun hD => hP ⟨hY', hhb, inferInstance, hD⟩)
      exact hnot (two_le_coheight_of_isExceptional hex)
    rw [DivisorWithCoeffs.coeff_neg, QDivisor.coeff_toRDivisor, hzero P hPm]
    simp
  have hnum : IsNumericallyEquivalentOver k sY h 0
      (QDivisor.toRDivisor H + -QDivisor.toRDivisor H) := by
    rw [add_neg_cancel]
    exact ⟨h0, h0, fun C _ m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ =>
      (IsRIntersectionNumber.eq_and_linear k sY C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ h₁ h₂⟩
  have heff := isEffective_of_isNumericallyEquivalentOver_pullback k sZ sY hZ hY h hh hhb hL0
    hL'0 hM hMnef hB hBG hnum
  have := heff F
  rw [DivisorWithCoeffs.coeff_neg, QDivisor.coeff_toRDivisor] at this
  exact_mod_cast neg_nonneg.mp this

end Negativity

/-! ### Comparison of log discrepancies along a step -/

section Comparison

open MMP.Flips

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}

/-- In a threefold step diagram, `f⁻_* D = f⁺_* (f⁺)⁻¹_* f⁻_* D`. -/
private theorem transformDivisor_flipTransform_of_isThreefoldStepDiagram
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R Xm) :
    RationalMap.transformDivisor (X := Xp) fp.toRationalMap (flipTransform fm fp D) =
      RationalMap.transformDivisor (X := Xm) fm.toRationalMap D := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z := hZ.1.toLocallyOfFiniteType.isLocallyNoetherian
  haveI := isSeparated_toTerminal_of_isNormalVariety h.isNormalVariety_target
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := isProper_of_isProjectiveMorphism fp h.isProjectiveMorphism_plus
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hXm' : IsNormalVariety ℂ (fm ≫ sZ) := h.comp_eq_minus ▸ h.isNormalVariety_minus
  have hXp' : IsNormalVariety ℂ (fp ≫ sZ) := h.comp_eq_plus ▸ h.isNormalVariety_plus
  have hfmb := h.isBirationalMorphism_minus
  have hfpb := h.isSmallMorphism_plus.isBirationalMorphism
  haveI : LocallyOfFiniteType fp :=
    LocallyOfFiniteType.of_comp (f := fp) (g := sZ) hXp'.1.toLocallyOfFiniteType
  refine Finsupp.ext fun Q => ?_
  obtain ⟨Qm, hQm, -, htm⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hXm' hfmb Q
  obtain ⟨Qp, hQp, -, htp⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hXp' hfpb Q
  rw [htm, htp]
  have hQ : Q.genericPoint ∈ biregularLocus fp :=
    MMP.Positivity.mem_biregularLocus_of_coheight_le_one fp hfpb.functionFieldMap_bijective
      h.isSmallMorphism_plus.two_le_codimension Q.coheight_genericPoint.le
  have := Q.isDiscreteValuationRing_localRing
  exact flipTransform_apply_of_map_genericPoint hfmb.functionFieldMap_bijective fp.surjective
    hQm hQp hQ D

/-- The birational map `(f⁻)⁻¹ ∘ f⁺ : X⁺ ⤏ X⁻` of a threefold step diagram lies over `Z`. -/
private theorem exists_isBirational_compHom_of_isThreefoldStepDiagram
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) :
    ∃ φ : RationalMap Xp Xm, φ.IsBirational ∧ φ.compHom fm = fp.toRationalMap := by
  haveI := isSeparated_toTerminal_of_isNormalVariety h.isNormalVariety_target
  obtain ⟨ep, hep⟩ := h.isSmallMorphism_plus.isBirationalMorphism
  obtain ⟨em, hem⟩ := h.isBirationalMorphism_minus
  set e := ep.trans em.symm with he
  refine ⟨e.toRationalMap, ⟨e, rfl⟩, ?_⟩
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 Z) hep
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em fm (𝟙 Z) hem
  rw [Category.comp_id] at h1 h2
  have H : e.IsOver fp fm := h1.trans h2.symm
  rw [Scheme.PartialIso.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change Xp.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fm =
    Xp.homOfLE (le_top : e.source ≤ ⊤) ≫ Xp.topIso.hom ≫ fp
  rw [Category.assoc, H]
  simp

/-- Two divisors over `X⁻` and `X⁺` given by one prime divisor `P` on a common model over `Z`
induce the same valuation of `k(Z)`. -/
private theorem valuation_comap_eq_of_comp_eq [IsIntegral Z] [IsDominant fm] [IsDominant fp]
    {Y : Scheme.{0}} [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] {g₁ : Y ⟶ Xp}
    {g₂ : Y ⟶ Xm} [IsDominant g₁] [IsDominant g₂] {hY₁ : IsNormalVariety ℂ (g₁ ≫ sXp)}
    {hY₂ : IsNormalVariety ℂ (g₂ ≫ sXm)} {hg₁ : IsBirationalMorphism g₁}
    {hg₂ : IsBirationalMorphism g₂} {P : MMP.Mori.PrimeDivisor Y} (hcomm : g₂ ≫ fm = g₁ ≫ fp) :
    (⟨Y, g₂, hY₂, hg₂, P⟩ : DivisorOver ℂ sXm).valuation.comap (functionFieldMap fm) =
      (⟨Y, g₁, hY₁, hg₁, P⟩ : DivisorOver ℂ sXp).valuation.comap (functionFieldMap fp) := by
  ext t
  change P.divisorialValuation (functionFieldMap g₂ (functionFieldMap fm t)) =
    P.divisorialValuation (functionFieldMap g₁ (functionFieldMap fp t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  have key : ∀ (u v : Y ⟶ Z) (_ : u = v) [IsDominant u] [IsDominant v],
      functionFieldMap u t = functionFieldMap v t := by
    rintro u v rfl _ _
    rfl
  rw [key _ _ hcomm]

/-- **Negativity along a threefold step diagram.** On a common model `Y` of `X⁻` and `X⁺` over
`Z`, the crepant boundary of `(X⁺, B⁺)` is coefficientwise at most that of `(X⁻, B⁻)`. -/
private theorem coeff_le_of_isCrepantBoundary (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hKm : Divisor.IsCanonicalDivisor sXm 3 K)
    (hKp : Divisor.IsCanonicalDivisor sXp 3 (flipTransform fm fp K))
    {Y : Scheme.{0}} [IsIntegral Y] [IsNormal Y] [IsLocallyNoetherian Y] {g₁ : Y ⟶ Xp}
    {g₂ : Y ⟶ Xm} [IsProper g₁] [IsProper g₂] (hY : IsNormalVariety ℂ (g₁ ≫ sXp))
    (hY₂ : IsNormalVariety ℂ (g₂ ≫ sXm)) (hg₁ : IsBirationalMorphism g₁)
    (hg₂ : IsBirationalMorphism g₂) (hcomm : g₁ ≫ fp = g₂ ≫ fm) {ΔYm ΔYp : QDivisor Y}
    (hΔYm : IsCrepantBoundary sXm 3 K B g₂ hY₂ hg₂ ΔYm)
    (hΔYp : IsCrepantBoundary sXp 3 (flipTransform fm fp K) (flipTransform fm fp B) g₁ hY hg₁ ΔYp)
    (P : MMP.Mori.PrimeDivisor Y) : ΔYp.coeff P ≤ ΔYm.coeff P := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z := hZ.1.toLocallyOfFiniteType.isLocallyNoetherian
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := isProper_of_isProjectiveMorphism fp h.isProjectiveMorphism_plus
  haveI : QuasiCompact sXm := h.isNormalVariety_minus.1.toQuasiCompact
  haveI : QuasiCompact sXp := h.isNormalVariety_plus.1.toQuasiCompact
  have hfmb := h.isBirationalMorphism_minus
  have hfpb := h.isSmallMorphism_plus.isBirationalMorphism
  haveI := hfmb.isDominant
  haveI := hfpb.isDominant
  have hNm : QDivisor.IsRelativelyNef sXm fm (-(Divisor.toQDivisor K + B)) :=
    isRelativelyNef_of_hasRelativelyAmpleMultiple h.hasRelativelyAmpleMultiple_minus
  have hNp : QDivisor.IsRelativelyNef sXp fp
      (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B) :=
    isRelativelyNef_of_hasRelativelyAmpleMultiple h.hasRelativelyAmpleMultiple_plus
  have hcomp := isRelativelyNef_of_isDiscrepancy_sub h.isNormalVariety_minus
    h.isNormalVariety_plus hZ h.comp_eq_minus h.comp_eq_plus hfmb hfpb hKm hKp
    (transformDivisor_flipTransform_of_isThreefoldStepDiagram h B).symm hNm hNp
    hY₂ hg₂ hg₁ hcomm.symm (ΔYp - ΔYm) (fun F a a' ha ha' => by
      rw [DivisorWithCoeffs.coeff_sub, ← (hΔYm F).eq ha, ← (hΔYp F).eq ha']
      ring)
  haveI : QuasiCompact (g₂ ≫ sXm) := hY₂.1.toQuasiCompact
  have hle := coeff_nonpos_of_isRelativelyNef ℂ sZ (g₂ ≫ sXm) hZ hY₂ (g₂ ≫ fm)
    (by rw [Category.assoc, h.comp_eq_minus]) (IsPair.isBirationalMorphism_comp hg₂ hfmb)
    hcomp.1 hcomp.2 P
  rwa [DivisorWithCoeffs.coeff_sub, sub_nonpos] at hle

/-- **Discrepancy comparison along a threefold step diagram** (KM 3.38). Every log discrepancy `a`
of a divisor over `X⁺` for `(X⁺, B⁺)` dominates the log discrepancy, for `(X⁻, B⁻)`, of a divisor
over `X⁻` with the same valuation of `k(Z)`. -/
private theorem exists_logDiscrepancy_minus_le (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (n : ℕ) (D : DivisorOver ℂ sXp) (a : ℝ)
    (hD : MMP.Intersection.IsLogDiscrepancy sXp n (QDivisor.toRDivisor (flipTransform fm fp B))
      D a) :
    haveI := h.isNormalVariety_target.1.toIsIntegral
    haveI := h.isBirationalMorphism_minus.isDominant
    haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
    ∃ (n' : ℕ) (D' : DivisorOver ℂ sXm) (a' : ℝ),
      D'.valuation.comap (functionFieldMap fm) = D.valuation.comap (functionFieldMap fp) ∧
      MMP.Intersection.IsLogDiscrepancy sXm n' (QDivisor.toRDivisor B) D' a' ∧ a' ≤ a := by
  have hZ := h.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z := hZ.1.toLocallyOfFiniteType.isLocallyNoetherian
  haveI : IsProper fm := isProper_of_isProjectiveMorphism fm h.isProjectiveMorphism_minus
  haveI : IsProper fp := isProper_of_isProjectiveMorphism fp h.isProjectiveMorphism_plus
  have hfmb := h.isBirationalMorphism_minus
  have hfpb := h.isSmallMorphism_plus.isBirationalMorphism
  haveI := hfmb.isDominant
  haveI := hfpb.isDominant
  have hXm := h.isNormalVariety_minus
  have hXp := h.isNormalVariety_plus
  haveI : QuasiCompact sXm := hXm.1.toQuasiCompact
  haveI : QuasiCompact sXp := hXp.1.toQuasiCompact
  obtain ⟨nm, hKm⟩ := h.isCanonicalDivisor
  obtain ⟨np, hKp⟩ := h.isCanonicalDivisor_plus
  obtain rfl : nm = 3 := by exact_mod_cast hKm.topologicalKrullDim_eq.symm.trans h.dim_minus
  obtain rfl : np = 3 := by exact_mod_cast hKp.topologicalKrullDim_eq.symm.trans h.dim_plus
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_of_isThreefoldStepDiagram h
  obtain ⟨Y, g₁, g₂, hY, hg₁, hg₁p, hg₂p, hg₂, -, hcomm, P, hPv⟩ :=
    exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hXp hXm fp fm
      φ hφ hφS D
  haveI := hg₁p
  haveI := hg₂p
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : IsLocallyNoetherian Y := hY.1.toLocallyOfFiniteType.isLocallyNoetherian
  haveI := hg₁.isDominant
  haveI := hg₂.isDominant
  have hs : g₂ ≫ sXm = g₁ ≫ sXp := by
    rw [← h.comp_eq_minus, ← h.comp_eq_plus, ← Category.assoc, ← Category.assoc, hcomm]
  have hY₂ : IsNormalVariety ℂ (g₂ ≫ sXm) := hs ▸ hY
  have hPm : MMP.Mori.IsPair sXm B := ⟨hXm, 3, K, hKm, h.isQCartier_minus⟩
  have hPp : MMP.Mori.IsPair sXp (flipTransform fm fp B) := ⟨hXp, 3, _, hKp, h.isQCartier_plus⟩
  obtain ⟨⟨ΔYm, hΔYm, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPm hKm g₂ hY₂ hg₂
  obtain ⟨⟨ΔYp, hΔYp, -⟩, -⟩ := MMP.Mori.IsPair.existsUnique_isCrepantBoundary hPp hKp g₁ hY hg₁
  have hle := coeff_le_of_isCrepantBoundary h hKm hKp hY hY₂ hg₁ hg₂ hcomm hΔYm hΔYp P
  have hlm := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΔYm P) hg₂p
  have hlp := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy (hΔYp P) hg₁p
  have ha := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hlp hPv.symm
  refine ⟨3, ⟨Y, g₂, hY₂, hg₂, P⟩, _, ?_, hlm, ?_⟩
  · rw [← hPv]
    exact valuation_comap_eq_of_comp_eq hcomm.symm
  · rw [ha]
    have : ((-ΔYm.coeff P : ℚ) : ℝ) ≤ ((-ΔYp.coeff P : ℚ) : ℝ) := by
      exact_mod_cast neg_le_neg hle
    linarith

end Comparison

/-! ### Small steps -/

/-- Along a threefold step diagram `(X⁻, B⁻) → Z ← (X⁺, B⁺)` with `f⁻` small and `(X⁻, B⁻)` klt,
the pair `(X⁺, B⁺)` is klt, the low-discrepancy set `I(X⁺, B⁺)` is contained in `I(X⁻, B⁻)` (as
sets of valuations of `k(Z)`), and `I(X⁻, B⁻)` is finite. -/
@[mmp "lem_mmp_indexc_low_set_nested"]
public theorem IsThreefoldStepDiagram.lowDiscrepancySet_subset_of_isSmallMorphism
    {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
    [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
    (h : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hsmall : IsSmallMorphism sXm sZ fm) (hklt : IsKltPair sXm B) :
    IsKltPair sXp (flipTransform fm fp B) ∧
      (haveI := h.isNormalVariety_target.1.toIsIntegral
       haveI := h.isBirationalMorphism_minus.isDominant
       haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
       valuationsOver fp (lowDiscrepancySet sXp (flipTransform fm fp B)) ⊆
         valuationsOver fm (lowDiscrepancySet sXm B)) ∧
      (lowDiscrepancySet sXm B).Finite := by
  haveI := h.isNormalVariety_target.1.toIsIntegral
  haveI := h.isBirationalMorphism_minus.isDominant
  haveI := h.isSmallMorphism_plus.isBirationalMorphism.isDominant
  obtain ⟨-, e, he⟩ := h.isExceptionalValuation_iff_of_isSmallMorphism hsmall
  refine ⟨⟨⟨hklt.1.isAlgClosed, hklt.1.charZero, ⟨h.isNormalVariety_plus, _, _,
    h.isCanonicalDivisor_plus.choose_spec, h.isQCartier_plus⟩, fun Q => ?_⟩,
    fun n D a hD => ?_⟩, ?_, hklt.finite_lowDiscrepancySet⟩
  · rw [← e.apply_symm_apply Q, (he _).2.2]
    exact h.nonneg _
  · obtain ⟨n', D', a', -, hD', hle⟩ := exists_logDiscrepancy_minus_le h n D a hD
    exact (hklt.2 n' D' a' hD').trans_le hle
  · rintro _ ⟨ξ, ⟨hexc, a, ⟨n, D, hDp, rfl, hD⟩, ha⟩, rfl⟩
    obtain ⟨n', D', a', hval, hD', hle⟩ := exists_logDiscrepancy_minus_le h n D a hD
    refine ⟨D'.valuation, ⟨?_, a', ⟨n', D', hD'.2.1, rfl, hD'⟩, hle.trans ha⟩, hval⟩
    exact ((h.isExceptionalValuation_iff_of_isSmallMorphism hsmall).1 D'.valuation D.valuation
      ⟨D', hD'.2.1, rfl⟩ hval.symm).2 hexc

/-- Along a sequence of threefold step diagrams `(X_i, B_i) → Z_i ← (X_{i+1}, B_{i+1})` with every
`f_i` small and `(X_0, B_0)` klt, every `(X_i, B_i)` is klt, and from some `i₀` on the
low-discrepancy sets `I(X_i, B_i)` and `I(X_{i+1}, B_{i+1})` agree as sets of valuations of
`k(Z_i)`, so that `I(X_i, B_i) = I(X_{i₀}, B_{i₀})` for all `i ≥ i₀`. -/
@[mmp "lem_mmp_indexc_low_set_stabilizes"]
public theorem isKltPair_and_exists_lowDiscrepancySet_eq_of_isSmallMorphism
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B : ∀ i, QDivisor (X i))
    (Z : ℕ → Scheme.{0}) (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (hstep : ∀ i, IsThreefoldStepDiagram (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (f i) (fp i))
    (hK : ∀ i, K (i + 1) = flipTransform (f i) (fp i) (K i))
    (hB : ∀ i, B (i + 1) = flipTransform (f i) (fp i) (B i))
    (hsmall : ∀ i, IsSmallMorphism (sX i) (sZ i) (f i))
    (hklt : IsKltPair (sX 0) (B 0)) :
    (∀ i, IsKltPair (sX i) (B i)) ∧
      ∃ i₀, ∀ i ≥ i₀,
        haveI := (hstep i).isNormalVariety_target.1.toIsIntegral
        haveI := (hstep i).isBirationalMorphism_minus.isDominant
        haveI := (hstep i).isSmallMorphism_plus.isBirationalMorphism.isDominant
        valuationsOver (f i) (lowDiscrepancySet (sX i) (B i)) =
          valuationsOver (fp i) (lowDiscrepancySet (sX (i + 1)) (B (i + 1))) := by
  have hall : ∀ i, IsKltPair (sX i) (B i) := by
    intro i
    induction i with
    | zero => exact hklt
    | succ i ih =>
      rw [hB i]
      exact ((hstep i).lowDiscrepancySet_subset_of_isSmallMorphism (hsmall i) ih).1
  have (i : ℕ) : IsIntegral (Z i) := (hstep i).isNormalVariety_target.1.toIsIntegral
  have (i : ℕ) : IsDominant (f i) := (hstep i).isBirationalMorphism_minus.isDominant
  have (i : ℕ) : IsDominant (fp i) :=
    (hstep i).isSmallMorphism_plus.isBirationalMorphism.isDominant
  have hnest i := (hstep i).lowDiscrepancySet_subset_of_isSmallMorphism (hsmall i) (hall i)
  refine ⟨hall, exists_image_eq_of_image_subset
    (fun i => comap_injective (hstep i).isBirationalMorphism_minus.functionFieldMap_bijective.2)
    (fun i => comap_injective
      (hstep i).isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2)
    (fun i => (hnest i).2.2) fun i => ?_⟩
  rw [hB i]
  exact (hnest i).2.1

/-! ### Stabilized tails -/

/-- The coefficients of the boundary of a klt pair lie in `[0, 1)`: for a prime divisor `P`,
`0 < a(ord_P; X, B) = 1 - coeff_P B`. -/
private theorem coeff_mem_Ico {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} (hB : IsKltPair sX B)
    (P : MMP.Mori.PrimeDivisor X) : B.coeff P ∈ Set.Ico (0 : ℚ) 1 := by
  have hpair := hB.1.isPair
  have hX : IsNormalVariety ℂ sX := hpair.1
  obtain ⟨-, n, K, hK, -⟩ := id hpair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  have hprop : IsProper (DivisorOver.ofPrimeDivisor ℂ hX P).f := inferInstanceAs (IsProper (𝟙 X))
  have hpos := hB.2 n _ _
    (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hprop)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha] at hpos
  push_cast at hpos
  exact ⟨hB.1.nonneg P, by exact_mod_cast (by linarith : ((B.coeff P : ℚ) : ℝ) < 1)⟩

/-- Along a step of a stabilized tail, the log discrepancy at `X_i` of a valuation is at most its
log discrepancy at `X_{i+1}`, for valuations agreeing on `k(Z_i)`. -/
private theorem StabilizedTail.logDiscrepancy_le (T : StabilizedTail) (i : ℕ)
    (ξ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))
    (ξ' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))) :
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    ξ.comap (functionFieldMap (T.f i)) = ξ'.comap (functionFieldMap (T.fp i)) →
    ∀ a a' : ℝ, T.IsLogDiscrepancyAt i ξ a → T.IsLogDiscrepancyAt (i + 1) ξ' a' → a ≤ a' := by
  have hS := T.isThreefoldStepDiagram i
  haveI := hS.isNormalVariety_target.1.toIsIntegral
  haveI := hS.isBirationalMorphism_minus.isDominant
  haveI := hS.isSmallMorphism_plus.isBirationalMorphism.isDominant
  rintro hξ a a' ⟨n, D, -, rfl, hD⟩ ⟨n', D', -, rfl, hD'⟩
  rw [T.B_eq i] at hD'
  obtain ⟨m, E, b, hE, hEl, hb⟩ := exists_logDiscrepancy_minus_le hS n' D' a' hD'
  rwa [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hEl
    (comap_injective hS.isBirationalMorphism_minus.functionFieldMap_bijective.2
      (hξ.trans hE.symm))]

namespace StabilizedTail

/-- In a stabilized tail `T`: the low-discrepancy set `I_∞ = I(X_0, B_0)` is finite; log
discrepancies of a valuation of the common function field are nondecreasing along each step;
for every `i` the strict transform `flipTransformPrimeDivisor (f i) (fp i)` is a bijection from
the prime divisors of `X_i` onto those of `X_{i+1}` preserving boundary coefficients; and every
`B_i` has the same set of nonzero coefficients as `B_0`, contained in `[0, 1)`. -/
@[mmp "lem_mmp_indexc_tail_basic"]
public theorem finite_and_monotone_and_frange_eq (T : StabilizedTail) :
    T.lowDiscrepancySetLimit.Finite ∧
      (∀ i (ξ : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))
          (ξ' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))),
          haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
          haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
          haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
          ξ.comap (functionFieldMap (T.f i)) = ξ'.comap (functionFieldMap (T.fp i)) →
          ∀ a a' : ℝ, T.IsLogDiscrepancyAt i ξ a → T.IsLogDiscrepancyAt (i + 1) ξ' a' →
            a ≤ a') ∧
      (∀ i, ∃ g : MMP.Mori.PrimeDivisor (T.X i) → MMP.Mori.PrimeDivisor (T.X (i + 1)),
          Function.Bijective g ∧ ∀ P, flipTransformPrimeDivisor (T.f i) (T.fp i) P = some (g P) ∧
            (T.B (i + 1)).coeff (g P) = (T.B i).coeff P) ∧
      (∀ i, (T.B i).frange = (T.B 0).frange) ∧
      ∀ c ∈ (T.B 0).frange, c ∈ Set.Ico (0 : ℚ) 1 := by
  have hbij : ∀ i, ∃ e : MMP.Mori.PrimeDivisor (T.X i) ≃ MMP.Mori.PrimeDivisor (T.X (i + 1)),
      ∀ P, flipTransformPrimeDivisor (T.f i) (T.fp i) P = some (e P) ∧
        (T.B (i + 1)).coeff (e P) = (T.B i).coeff P := by
    intro i
    obtain ⟨-, e, he⟩ :=
      (T.isThreefoldStepDiagram i).isExceptionalValuation_iff_of_isSmallMorphism
        (T.isSmallMorphism i)
    exact ⟨e, fun P => ⟨(he P).1, by rw [T.B_eq i]; exact (he P).2.2⟩⟩
  have hfr : ∀ i, (T.B i).frange = (T.B 0).frange := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      obtain ⟨e, he⟩ := hbij i
      exact (frange_eq_of_equiv _ _ e fun P => (he P).2).trans ih
  refine ⟨(T.isKltPair 0).finite_lowDiscrepancySet, T.logDiscrepancy_le,
    fun i => (hbij i).elim fun e he => ⟨e, e.bijective, he⟩, hfr, fun c hc => ?_⟩
  obtain ⟨-, P, rfl⟩ := Finsupp.mem_frange.mp hc
  exact coeff_mem_Ico (T.isKltPair 0) P

end StabilizedTail

end MMP.Fourfold
