module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FourfoldDefs
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.DefaultWeightEventuallyConst
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.EchoWeightUnchanged
import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.MMP.Fourfold.SurfaceEchoLogDiscrepancy
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ExceptionalValuations
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence
import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Normalization.IntegralScheme
import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Difficulty change under a coefficient decrease

Let `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` be the coefficient-decrease move of the `i`-th bridge of a
prepared chain of fourfolds, `i ≥ i₀`. The variety, the labels, the centres of valuations, the
branch numbers, the default echo weights and the ranks of the normalized labels are the same for
both boundaries, and the weights `w_v` of the exceptional valuations change only for finitely
many `v`. Hence there is a finite set `F` of normalized divisorial valuations exceptional over
`Y_i`, outside which `w_v(Y_i, Θ_i) = w_v(Y_i, Θ_i')`, with
`𝒟(Y_i, Θ_i) - 𝒟(Y_i, Θ_i') = ∑_{v ∈ F} (w_v(Y_i, Θ_i) - w_v(Y_i, Θ_i'))`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.exists_finset_difficulty_sub_eq_sum`:
  the difference of the difficulties across a coefficient decrease is a finite sum of weight
  differences, and the weights of all other exceptional valuations are unchanged.

## Implementation notes

* The coefficient decrease of the `i`-th bridge is the step from the junction `⟨i, none⟩` to
  the next model `Q.chain.next ⟨i, none⟩` of the chain. When the bridge has a flip this is the
  decreased pair `⟨i, some 0⟩`, whose variety is `Y_i`; when it has none, the decreased pair is
  identified with the junction `⟨i + 1, none⟩` through the bridge's isomorphism `e`. Uniformly,
  the target is `(Y_i, Θ_i')` up to an isomorphism `φ` of pairs over `ℂ`
  (`Θ_i' = φ⁻¹_* Θ`), and a valuation `v` of `ℂ(Y_i)` is carried to the valuation
  `v ∘ φ^*` of the function field of the target. Log discrepancies are invariant under
  isomorphisms of pairs, so the statement holds for every such `φ`.
* Weights (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`) and
  difficulties (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`) are
  predicates on their values; the equalities are stated for all values satisfying them.
-/

@[expose] public section

section

universe u

namespace MMP.Fourfold.CoefficientDecrease

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold
  MMP.Fourfold.StabilizedSmallKltTail MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Label centres, label defaults and weights are unique -/

section Unique

variable {T : StabilizedSmallKltTail}

/-- On every model of a terminal chain, the centre relation of the labels is the centre map of a
bijection of prime divisors. -/
private theorem exists_equiv_isLabelCentre_iff (C : TerminalChain T) (x : C.ModelIndex) :
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.model x),
      ∀ (S : C.Label) (P : MMP.Mori.PrimeDivisor (C.model x)),
        C.IsLabelCentre S x P ↔ e S.1 = P := by
  have he := TerminalChain.isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C x
  rcases x with ⟨i, _ | k⟩ <;> exact ⟨_, fun S P => he S.1 P⟩

/-- Every label has a centre on every model of a terminal chain. -/
private theorem exists_isLabelCentre (C : TerminalChain T) (S : C.Label) (x : C.ModelIndex) :
    ∃ P, C.IsLabelCentre S x P := by
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff C x
  exact ⟨e S.1, (he S _).2 rfl⟩

/-- A label has at most one centre on a model of a terminal chain. -/
private theorem isLabelCentre_unique {C : TerminalChain T} {S : C.Label} {x : C.ModelIndex}
    {P P' : MMP.Mori.PrimeDivisor (C.model x)} (h : C.IsLabelCentre S x P)
    (h' : C.IsLabelCentre S x P') : P = P' := by
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff C x
  exact ((he S P).1 h).symm.trans ((he S P').1 h')

/-- The coefficient of a label on a model is unique. -/
private theorem isLabelCoefficient_unique {C : TerminalChain T} {S : C.Label} {x : C.ModelIndex}
    {b b' : ℚ} (h : C.IsLabelCoefficient S x b) (h' : C.IsLabelCoefficient S x b') : b = b' := by
  rcases h with ⟨P, hP, rfl⟩ | ⟨hn, rfl⟩ <;> rcases h' with ⟨P', hP', rfl⟩ | ⟨hn', rfl⟩
  · rw [isLabelCentre_unique hP hP']
  · exact absurd hP (hn' P)
  · exact absurd hP' (hn P')
  · rfl

/-- The default echo weight of a label on a model is unique. -/
private theorem isLabelDefault_unique {C : TerminalChain T} {N : ℕ} {S : C.Label}
    {x : C.ModelIndex} {d d' : ℕ} (h : C.IsLabelDefault N S x d)
    (h' : C.IsLabelDefault N S x d') : d = d' := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', rfl⟩ := h'
  rw [isLabelCoefficient_unique hb hb']

/-- The weight of a valuation on a model is unique. -/
private theorem isValuationWeight_unique {C : TerminalChain T} {N : ℕ} {x : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))} {n n' : ℕ}
    (h : C.IsValuationWeight N x v n) (h' : C.IsValuationWeight N x v n') : n = n' := by
  obtain ⟨-, a, ⟨m, D, -, hD, ha⟩, rfl⟩ := h
  obtain ⟨-, a', ⟨m', D', -, hD', ha'⟩, rfl⟩ := h'
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hD.trans hD'.symm)]

end Unique

/-! ### Codimensions and dimensions of closures of points -/

section Dimension

/-- The codimension of the closure of a point is the coheight of the point. -/
private theorem codimension_eq_coheight_of_eq_closure {X : Scheme.{0}} {W : IrreducibleCloseds X}
    {x : X} (h : (W : Set X) = closure {x}) : codimension W = Order.coheight x := by
  have hEq : (irreducibleSetEquivPoints (α := X)).symm x = W := IrreducibleCloseds.ext h.symm
  rw [codimension_eq_coheight, ← hEq, Order.coheight_orderIso]

/-- On a fourfold, the closure of a point of coheight `c` has dimension `4 - c`, in the form
`dim + c = 4`. -/
private theorem topologicalKrullDim_closure_add_coheight {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 4) (x : X) :
    topologicalKrullDim (closure {x} : Set X) + Order.coheight x = 4 := by
  rw [MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX x, hdim]

/-- Dimension arithmetic: `d + c = 4` with `c = 2` forces `d = 2`, and conversely. -/
private theorem eq_two_iff_of_add_eq_four {d : WithBot ℕ∞} {c : ℕ∞} (h : d + c = 4) :
    d = 2 ↔ c = 2 := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    norm_cast at h ⊢
    induction e using ENat.recTopCoe <;> induction c using ENat.recTopCoe <;> simp_all <;>
      norm_cast at * <;> omega

end Dimension

/-- A divisorial valuation has at most one centre. -/
private theorem isCentre_unique {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    (hX : MMP.Mori.IsVariety ℂ sY) {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    {V V' : IrreducibleCloseds Y} (hV : MMP.Intersection.IsCentre ℂ sY ξ V)
    (hV' : MMP.Intersection.IsCentre ℂ sY ξ V') : V = V' := by
  obtain ⟨D, -, hD, rfl⟩ := hV
  obtain ⟨D', -, hD', rfl⟩ := hV'
  exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX (hD.symm.trans hD')

/-! ### Brackets vanish at almost every surface -/

namespace Bracket

open MMP.Mori IsLocalRing
open scoped WithZero

/-- In `WithBot ℕ∞`, `d + 1 = n + 1` forces `d = n`. -/
private theorem eq_of_add_one_eq {d : WithBot ℕ∞} {n : ℕ} (h : d + 1 = ((n + 1 : ℕ) : ℕ∞)) :
    d = (n : ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact (WithBot.bot_ne_coe h).elim
  | coe e =>
    norm_cast at h ⊢
    induction e using ENat.recTopCoe <;> simp_all <;> norm_cast at * <;> omega

/-- Dimension arithmetic: `2 + c = 3` forces `c = 1`. -/
private theorem eq_one_of_two_add_eq_three {c : ℕ∞} (h : (2 : WithBot ℕ∞) + c = 3) : c = 1 := by
  norm_cast at h
  induction c using ENat.recTopCoe <;> simp_all <;> norm_cast at * <;> omega

/-- The coefficients of the boundary of a klt pair are `< 1`. -/
private theorem coeff_lt_one_of_isKltPair {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {Θ : QDivisor X} (hΘ : IsKltPair sX Θ) (P : MMP.Mori.PrimeDivisor X) :
    Θ.coeff P < 1 := by
  obtain ⟨hX, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hX P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hX P).f := by
    change IsProper (𝟙 X)
    infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hX ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- The default echo weight of a nonpositive coefficient vanishes. -/
private theorem defaultWeight_of_nonpos (N : ℕ) {b : ℝ} (hb : b ≤ 0) : defaultWeight N b = 0 := by
  rw [defaultWeight]
  apply finsum_eq_zero_of_forall_eq_zero
  intro j
  rw [finsum_eq_if]
  split_ifs with hj
  · apply difficultyWeight_of_nonpos
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    nlinarith
  · rfl

/-- A log discrepancy over a proper model is a log discrepancy. -/
private theorem IsValuationLogDiscrepancy.hasLogDiscrepancy {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sX B v a) : HasLogDiscrepancy sX B v a := by
  obtain ⟨n, D, -, hv, ha⟩ := h
  exact ⟨n, D, hv, ha⟩

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {B : QDivisor X} {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    {a a' : ℝ} (h : HasLogDiscrepancy sX B v a) (h' : HasLogDiscrepancy sX B v a') : a = a' := by
  obtain ⟨n, D, hv, ha⟩ := h
  obtain ⟨n', D', hv', ha'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hv.trans hv'.symm)

/-- **Regularity in codimension two.** On a terminal pair on a `ℚ`-factorial normal variety over
`ℂ`, the local ring at every point of coheight at most two is regular. -/
private theorem isRegularLocalRing_stalk_of_coheight_le_two {Y : Scheme.{0}}
    {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    (hΘ : IsKltTerminalPair sY Θ) (hQ : IsQFactorial sY) {y : Y} (hy : Order.coheight y ≤ 2) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨-, n, K, hK, -⟩ := id hΘ.1.1.isPair
  obtain ⟨-, hsing⟩ :=
    IsKltTerminalPair.isTerminalVariety_and_three_le_closedsCodimension_singularLocus hΘ
      (isQCartier_of_isQFactorial sY hQ Θ) hK (isQCartier_of_isQFactorial sY hQ _)
  have hy' : y ∈ smoothLocus sY := by
    by_contra hns
    let e := irreducibleSetEquivPoints (α := Y)
    have hsub : ((e.symm y : IrreducibleCloseds Y) : Set Y) ⊆ (singularLocus sY : Set Y) := by
      change closure {y} ⊆ _
      exact (singularLocus sY).isClosed.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr hns)
    have h3 := le_closedsCodimension_iff.1 hsing _ hsub
    rw [codimension_eq_coheight_of_eq_closure (rfl : ((e.symm y : IrreducibleCloseds Y) :
      Set Y) = closure {y})] at h3
    exact absurd (h3.trans hy) (by decide)
  obtain ⟨U, hyU, hU⟩ := mem_smoothLocus_iff.mp hy'
  have : Smooth (U.ι ≫ sY) := hU
  have := isRegularLocalRing_stalk_of_smooth_over_field (U.ι ≫ sY) ⟨y, hyU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨y, hyU⟩).commRingCatIsoToRingEquiv

/-! ### Valuations from additive valuations -/

/-- The order-reversing monoid map `WithTop ℤ → ℤᵐ⁰`, `n ↦ exp (-n)`, `⊤ ↦ 0`. -/
private def expNeg : WithTop ℤ → ℤᵐ⁰
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private lemma expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := rfl

private lemma expNeg_top : expNeg ⊤ = 0 := rfl

private lemma expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg_top, ← WithTop.coe_add, expNeg_coe, neg_add, WithZero.exp_add, mul_comm]

private lemma expNeg_antitone : Antitone expNeg := by
  intro a b h
  cases b with
  | top => simp [expNeg_top]
  | coe n =>
    cases a with
    | top => simp at h
    | coe m =>
      simp only [expNeg_coe, WithZero.exp_le_exp, neg_le_neg_iff]
      exact_mod_cast h

/-- The multiplicative valuation `z ↦ exp (-V z)` attached to an additive valuation `V`. -/
private def valuationOfAddValuation {R : Type*} [Ring R] (V : AddValuation R (WithTop ℤ)) :
    Valuation R ℤᵐ⁰ where
  toFun z := expNeg (V z)
  map_zero' := by simp [expNeg_top]
  map_one' := by simp [← WithTop.coe_zero, expNeg_coe]
  map_mul' a b := by simp [V.map_mul, expNeg_add]
  map_add_le_max' a b := by
    rw [← expNeg_antitone.map_min]
    exact expNeg_antitone (V.map_add a b)

private lemma valuationOfAddValuation_apply {R : Type*} [Ring R]
    (V : AddValuation R (WithTop ℤ)) (z : R) :
    valuationOfAddValuation V z = expNeg (V z) := rfl

/-! ### Echo ideals in a two-dimensional regular local ring -/

/-- A pair `(x, y)` is a regular system of parameters iff it spans `𝔪` and `dim A = 2`. -/
private lemma isRegularSystemOfParameters_pair_iff {A : Type*} [CommRing A] [IsLocalRing A]
    {x y : A} :
    IsRegularSystemOfParameters ![x, y] ↔
      Ideal.span {x, y} = maximalIdeal A ∧ ringKrullDim A = 2 := by
  rw [isRegularSystemOfParameters_iff, Matrix.range_cons, Matrix.range_cons,
    Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rfl

private lemma isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : IsRegularSystemOfParameters ![x, y]) :
    IsRegularSystemOfParameters ![y, x] := by
  rw [isRegularSystemOfParameters_pair_iff, Set.pair_comm]
  exact isRegularSystemOfParameters_pair_iff.1 hxy

/-- A point whose local ring has a regular system of parameters of length two is the generic
point of a closed subset of codimension two. -/
private lemma codimension_eq_two {X : Scheme.{u}} (Z : IrreducibleCloseds X)
    {x t : X.presheaf.stalk Z.isIrreducible.genericPoint}
    (ht : IsRegularSystemOfParameters ![x, t]) : codimension Z = 2 :=
  WithBot.coe_injective (by rw [codimension_eq_ringKrullDim_stalk_genericPoint, ht.2]; rfl)

/-- A local equation of a prime divisor at a point of it is a nonzero element of the maximal
ideal. -/
private theorem mem_maximalIdeal_and_ne_zero_of_stalk_eq_span {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hy : y ∈ E.support) {a : Y.presheaf.stalk y}
    (ha : IdealSheafData.stalk E.idealSheaf y = Ideal.span {a}) :
    a ∈ maximalIdeal (Y.presheaf.stalk y) ∧ a ≠ 0 := by
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hy
  refine ⟨(mem_maximalIdeal _).2 fun hu => ?_, ?_⟩
  · exact (IdealSheafData.stalk_eq_top_iff_notMem_support E.idealSheaf y).1
      (by rw [ha, Ideal.span_singleton_eq_top]; exact hu) hy
  · rintro rfl
    exact Ideal.ne_bot_of_height_eq_one hqh (by rw [← hq, ha, Ideal.span_singleton_eq_bot])

/-- The generic point of a surface in a fourfold has coheight two. -/
private theorem coheight_genericPoint_eq_two {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {V : IrreducibleCloseds Y}
    (hY : IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 4) (hV : topologicalKrullDim (V : Set Y) = 2) :
    Order.coheight V.isIrreducible.genericPoint = 2 := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [V.isIrreducible.closure_genericPoint V.isClosed, hV, hdim] at h
  exact (add_right_inj_of_ne_top (by decide)).mp (WithBot.coe_inj.mp h :
    2 + Order.coheight V.isIrreducible.genericPoint = 2 + 2)

/-- The local ring of a normal fourfold at the generic point of a surface has dimension two. -/
private theorem ringKrullDim_stalk_genericPoint_eq_two {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {V : IrreducibleCloseds Y}
    (hY : IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 4) (hV : topologicalKrullDim (V : Set Y) = 2) :
    ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, coheight_genericPoint_eq_two hY hdim hV]
  rfl

/-! ### Existence of echoes -/

/-- **A valuation of log discrepancy below two at a surface in a boundary component.** Let `(Y, Θ)`
be a pair on a normal fourfold, `V` an irreducible surface at whose generic point `Y` is regular,
and `P` a component of `Θ` containing `V`. The `𝔪_V`-adic order (the monomial valuation of
weights `(1, 1)` in a regular system of parameters at `η_V`) is a normalized divisorial valuation
with centre `V` and log discrepancy at most `2 - Θ(P)`. -/
private theorem exists_isCentre_hasLogDiscrepancy_le {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    (hΘ : MMP.Fourfold.IsPair sY Θ) (hY : IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 4) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 2)
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {P : MMP.Mori.PrimeDivisor Y} (hVP : (V : Set Y) ⊆ P.support) (hP : 0 < Θ.coeff P) :
    ∃ v : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      MMP.Intersection.IsCentre ℂ sY v V ∧
        ∃ a : ℝ, a ≤ 2 - (Θ.coeff P : ℝ) ∧ HasLogDiscrepancy sY Θ v a := by
  classical
  set η := V.isIrreducible.genericPoint with hη
  have hdimR := ringKrullDim_stalk_genericPoint_eq_two hY hdim hV
  obtain ⟨s, hs, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (maximalIdeal (Y.presheaf.stalk η)).fg_of_isNoetherianRing
  have h2 : (maximalIdeal (Y.presheaf.stalk η)).spanFinrank = 2 := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := Y.presheaf.stalk η)).trans
      hdimR
  obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (hs.trans h2)
  have hab : Ideal.span {a, b} = maximalIdeal (Y.presheaf.stalk η) := by simpa using hspan
  have ht : IsRegularSystemOfParameters ![a, b] :=
    isRegularSystemOfParameters_pair_iff.2 ⟨hab, hdimR⟩
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap ht) (le_refl 1)
  have hvalW : ∀ f : Y.presheaf.stalk η, f ≠ 0 →
      ∃ M : ℕ, MMP.Resolution.monomialValuation b a 1 f = M ∧
        valuationOfAddValuation W (algebraMap _ Y.functionField f) =
          WithZero.exp (-(M : ℤ)) := by
    intro f hf
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
    refine ⟨M, hM.symm, ?_⟩
    rw [valuationOfAddValuation_apply, hW, ← hM]
    rfl
  have hv : IsWeightedMonomialValuation sY V a b 1 (valuationOfAddValuation W) :=
    ⟨hY, codimension_eq_two V ht, inferInstance, ht, le_rfl, hvalW⟩
  have hηP : η ∈ P.support := hVP (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  have hgen : ∀ S : MMP.Mori.PrimeDivisor Y, ∃ g : Y.presheaf.stalk η,
      IdealSheafData.stalk S.idealSheaf η = Ideal.span {g} ∧ g ≠ 0 := by
    intro S
    by_cases hS : η ∈ S.support
    · haveI := IsRegularLocalRing.isDomain (Y.presheaf.stalk η)
      haveI := IsRegularLocalRing.uniqueFactorizationMonoid (Y.presheaf.stalk η)
      obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
      obtain ⟨g, hgq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh).principal
      have hg := hq.trans hgq
      exact ⟨g, hg, (mem_maximalIdeal_and_ne_zero_of_stalk_eq_span S hS hg).2⟩
    · refine ⟨1, ?_, one_ne_zero⟩
      rw [Ideal.span_singleton_one]
      exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).mpr hS
  choose f hf hf0 using hgen
  have hd := hv.hasLogDiscrepancy hΘ f fun S _ => hf S
  refine ⟨_, hv.isNormalizedDivisorialValuation_and_isCentre.2, _, ?_, hd⟩
  have hM : ∀ S, ∃ M : ℕ, (-WithZero.log (valuationOfAddValuation W
      (algebraMap _ Y.functionField (f S))) : ℤ) = M ∧
        (η ∈ S.support → 1 ≤ M) := by
    intro S
    obtain ⟨M, hMv, hMw⟩ := hvalW (f S) (hf0 S)
    refine ⟨M, by rw [hMw, WithZero.log_exp, neg_neg], fun hS => ?_⟩
    have hmem : f S ∈ MMP.Resolution.monomialIdeal b a 1 1 := by
      rw [MMP.Fourfold.monomialIdeal_one_eq_pow, pow_one, Set.pair_comm, hab]
      exact (mem_maximalIdeal_and_ne_zero_of_stalk_eq_span S hS (hf S)).1
    have h1 : (1 : ℕ∞) ≤ MMP.Resolution.monomialValuation b a 1 (f S) :=
      le_iSup₂_of_le (f := fun (ν : ℕ) (_ : f S ∈ MMP.Resolution.monomialIdeal b a 1 ν) =>
        (ν : ℕ∞)) 1 hmem (by norm_num)
    rw [hMv] at h1
    exact_mod_cast h1
  have hnn : ∀ S ∈ Θ.support, 0 ≤ (Θ.coeff S : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f S))) : ℤ) :
        ℝ) := by
    intro S _
    obtain ⟨M, hMe, -⟩ := hM S
    rw [hMe]
    exact mul_nonneg (by exact_mod_cast hΘ.nonneg S) (by positivity)
  have hPmem : P ∈ Θ.support := Finsupp.mem_support_iff.mpr hP.ne'
  have hle := Finset.single_le_sum hnn hPmem
  obtain ⟨MP, hMPe, hMP1⟩ := hM P
  have hPterm : (Θ.coeff P : ℝ) ≤ (Θ.coeff P : ℝ) *
      ((-WithZero.log (valuationOfAddValuation W (algebraMap _ Y.functionField (f P))) : ℤ) :
        ℝ) := by
    rw [hMPe]
    have : (1 : ℝ) ≤ (MP : ℝ) := by exact_mod_cast hMP1 hηP
    have hc : (0 : ℝ) ≤ Θ.coeff P := by exact_mod_cast hP.le
    push_cast
    nlinarith
  rw [Nat.cast_one]
  linarith

/-- **Branch number one at a regular point.** Let `S` be a prime divisor of a fourfold `Y`
and `V ⊆ S` an irreducible closed surface at whose generic point `S` is regular. Then exactly one
prime divisor of the normalization `S^ν` maps onto `V`: `r_{V} = 1`. -/
private theorem branchNumber_eq_one {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsVariety ℂ sY] (hdim : topologicalKrullDim Y = 4)
    (S : MMP.Mori.PrimeDivisor Y)
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 2)
    (hVS : (V : Set Y) ⊆ S.support)
    (hreg : V.isIrreducible.genericPoint ∉
      S.idealSheaf.subschemeι '' AlgebraicGeometry.singularLocus S.idealSheaf.subscheme) :
    branchNumber S V = 1 := by
  classical
  haveI : IsIntegral Y := (inferInstance : AlgebraicGeometry.IsVariety ℂ sY).toIsIntegral
  haveI := S.integral
  haveI hvarS : AlgebraicGeometry.IsVariety ℂ (S.idealSheaf.subschemeι ≫ sY) :=
    (MMP.Mori.isVariety_iff ℂ _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨⟨-, -, hfinν, hsurj, -⟩, ⟨U, hU, hiso⟩, -⟩ :=
    MMP.Threefold.normalization_spec (S.idealSheaf.subschemeι ≫ sY)
  set ν := S.idealSheaf.subscheme.normalization
    (MMP.finite_irreducibleComponents_of_isIntegral
      S.idealSheaf.subscheme) with hν
  set ι := S.idealSheaf.subschemeι with hι
  have hgen := V.isIrreducible.isGenericPoint_genericPoint V.isClosed
  obtain ⟨s, hs⟩ : V.isIrreducible.genericPoint ∈ Set.range ι := by
    rw [hι, Scheme.IdealSheafData.range_subschemeι]
    exact hVS hgen.mem
  have hsreg : IsRegularLocalRing (S.idealSheaf.subscheme.presheaf.stalk s) := by
    by_contra h
    exact hreg ⟨s, h, hs⟩
  have hsU : s ∈ U := by
    rw [← SetLike.mem_coe, hU]
    haveI := IsRegularLocalRing.isDomain (S.idealSheaf.subscheme.presheaf.stalk s)
    haveI := IsRegularLocalRing.uniqueFactorizationMonoid
      (S.idealSheaf.subscheme.presheaf.stalk s)
    exact (inferInstance : IsIntegrallyClosed (S.idealSheaf.subscheme.presheaf.stalk s))
  have hdimS : topologicalKrullDim S.idealSheaf.subscheme = 3 := by
    have hdP := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY S.genericPoint
    rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdim] at hdP
    let e := ι.isClosedEmbedding.isEmbedding.toHomeomorph
    let e' := e.trans (Homeomorph.setCongr (Scheme.IdealSheafData.range_subschemeι S.idealSheaf))
    exact (IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph).trans
      (eq_of_add_one_eq (n := 3) hdP)
  have hdimCs : topologicalKrullDim (closure ({s} : Set S.idealSheaf.subscheme)) = 2 := by
    rw [← hV]
    have hemb : Topology.IsEmbedding
        (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) :=
      ι.isClosedEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have hrange : Set.range (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) =
        (V : Set Y) := by
      rw [show (fun p : closure ({s} : Set S.idealSheaf.subscheme) => ι p.1) = ι ∘ Subtype.val
        from rfl, Set.range_comp, Subtype.range_coe,
        ← ι.isClosedEmbedding.closure_image_eq, Set.image_singleton, hs, hgen.def]
    let e := hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
    exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph
  have hcohs : Order.coheight s = 1 := by
    have hdS := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      (S.idealSheaf.subschemeι ≫ sY) s
    rw [hdimS, hdimCs] at hdS
    exact eq_one_of_two_add_eq_three hdS
  haveI := hsurj
  haveI := hiso
  haveI := hfinν
  obtain ⟨z₀, hz₀⟩ := ν.surjective s
  have hcomm : ∀ p, U.ι ((ν ∣_ U) p) = ν ((ν ⁻¹ᵁ U).ι p) := fun p => by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  have hlift : ∀ z, ν z = s → ∃ p, (ν ⁻¹ᵁ U).ι p = z := fun z hz => by
    have : z ∈ Set.range (ν ⁻¹ᵁ U).ι := by
      rw [Scheme.Opens.range_ι]
      show ν z ∈ U
      rwa [hz]
    exact this
  obtain ⟨p₀, hp₀⟩ := hlift z₀ hz₀
  have huniq : ∀ z, ν z = s → z = z₀ := by
    intro z hz
    obtain ⟨p, hp⟩ := hlift z hz
    have h1 : U.ι ((ν ∣_ U) p) = U.ι ((ν ∣_ U) p₀) := by rw [hcomm, hcomm, hp, hp₀, hz, hz₀]
    have h2 := (ν ∣_ U).isOpenEmbedding.injective (U.ι.isOpenEmbedding.injective h1)
    rw [← hp, ← hp₀, h2]
  have hcoh0 : Order.coheight z₀ = 1 := by
    calc Order.coheight z₀ = Order.coheight ((ν ⁻¹ᵁ U).ι p₀) := by rw [hp₀]
      _ = Order.coheight p₀ := coheight_eq_of_isOpenImmersion _
      _ = Order.coheight ((ν ∣_ U) p₀) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight (U.ι ((ν ∣_ U) p₀)) := (coheight_eq_of_isOpenImmersion _).symm
      _ = Order.coheight s := by rw [hcomm, hp₀, hz₀]
      _ = 1 := hcohs
  have hfun : ⇑(ν ≫ ι) = ⇑ι ∘ ⇑ν := funext fun _ => rfl
  have hcl : IsClosedMap (ν ≫ ι) := by
    rw [hfun]
    exact ι.isClosedEmbedding.isClosedMap.comp ν.isClosedMap
  have himg : ∀ Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)),
      (ν ≫ ι) '' Q.support = closure {ι (ν Q.genericPoint)} := by
    intro Q
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← hcl.closure_image_eq_of_continuous (ν ≫ ι).continuous, Set.image_singleton]
    rfl
  have hset : {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) | (ν ≫ ι) '' Q.support = (V : Set Y)} =
        {AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0} := by
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [himg]
    constructor
    · intro hQ
      have hQη : ι (ν Q.genericPoint) = V.isIrreducible.genericPoint :=
        (inseparable_iff_closure_eq.mpr (hQ.trans hgen.def.symm)).eq
      have hνQ : ν Q.genericPoint = s := ι.isClosedEmbedding.injective (hQη.trans hs.symm)
      apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      rw [AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne]
      exact huniq _ hνQ
    · rintro rfl
      have hg0 : MMP.Mori.PrimeDivisor.genericPoint
          (AlgebraicGeometry.PrimeDivisor.ofCoheightOne z₀ hcoh0) = z₀ :=
        AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _
      rw [hg0, hz₀, hs, hgen.def]
  change {Q : MMP.Mori.PrimeDivisor (S.idealSheaf.subscheme.normalizationScheme
      (MMP.finite_irreducibleComponents_of_isIntegral
        S.idealSheaf.subscheme)) | (ν ≫ ι) '' Q.support = (V : Set Y)}.ncard = 1
  rw [hset, Set.ncard_singleton]

end Bracket

/-- At a positive scale, a nonzero weight `w(2 - a)` comes from a log discrepancy `a < 2`. -/
private theorem lt_two_of_difficultyWeight_ne_zero {N : ℕ} (hN : 0 < N) {a : ℝ}
    (h : difficultyWeight N (2 - a) ≠ 0) : a < 2 := by
  by_contra h'
  exact h ((difficultyWeight_eq_zero_iff hN).2 (by linarith [not_lt.mp h']))

/-! ### Finiteness on a model of a prepared chain -/

namespace Side

open MMP.Mori

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T) (x : Q.ModelIndex)

/-- `v` has a centre of codimension at least three on the model indexed by `x`. -/
private abbrev IsDeepCentred
    (v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ))) : Prop :=
  ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
    MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧ 3 ≤ codimension Z

variable {Q x}

/-- **Brackets vanish at almost every surface.** On a model of a prepared chain, the bracket
`β_V` vanishes at all but finitely many irreducible surfaces `V`. -/
private theorem finite_setOf_isSurfaceBracket_ne_zero :
    {V : IrreducibleCloseds (Q.chain.model x.1) |
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 ∧
        ∃ β, Q.IsSurfaceBracket x V β ∧ β ≠ 0}.Finite := by
  classical
  haveI : Finite Q.chain.Label := Q.chain.finite_label
  letI : Fintype Q.chain.Label := Fintype.ofFinite _
  obtain ⟨hΘ, hQf, hY, hdim⟩ := TerminalChain.isKltTerminalPair_modelBoundary Q.chain x.1
  have hnv : MMP.Mori.IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hΘ.1.1.isPair.1
  haveI := hnv.1.toIsIntegral
  haveI := hnv.2
  haveI : AlgebraicGeometry.IsVariety ℂ (Q.chain.modelStructure x.1) := hnv.1
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hnv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian (Q.chain.model x.1) :=
    LocallyOfFiniteType.isLocallyNoetherian (Q.chain.modelStructure x.1)
  have hN := Q.isAdmissibleScale.pos
  set Θ := Q.chain.modelBoundary x.1 with hΘdef
  choose c hc using fun S => exists_isLabelCentre Q.chain S x.1
  have hcinj : Function.Injective c := by
    obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff Q.chain x.1
    intro S S' h
    have h1 := (he S (c S)).1 (hc S)
    have h2 := (he S' (c S')).1 (hc S')
    exact Subtype.ext (e.injective (h1.trans (h.trans h2.symm)))
  set L : Finset (MMP.Mori.PrimeDivisor (Q.chain.model x.1)) := Finset.univ.image c with hL
  have hcL : ∀ S, c S ∈ L := fun S => Finset.mem_image_of_mem c (Finset.mem_univ S)
  have hsupp : Θ.support ⊆ L := by
    intro P hP
    have hne : Θ.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
    rw [TerminalChain.coeff_modelBoundary_eq_finsum Q.chain x.1 (fun S => Θ.coeff (c S))
      (fun S => TerminalChain.isLabelCoefficient_of_isLabelCentre (hc S)) P] at hne
    obtain ⟨S, hS⟩ : ∃ S, Q.chain.IsLabelCentre S x.1 P := by
      by_contra h
      push Not at h
      exact hne (finsum_eq_zero_of_forall_eq_zero fun S => by rw [finsum_eq_if, if_neg (h S)])
    rw [isLabelCentre_unique hS (hc S)]
    exact hcL S
  have hlt : ∀ P ∈ L, Θ.coeff P < 1 := fun P _ => Bracket.coeff_lt_one_of_isKltPair hΘ.1 P
  obtain ⟨𝒮, -, h𝒮⟩ := IsKltTerminalPair.exists_finset_forall_isSurfaceEcho hY hQf hdim hΘ hsupp
  refine 𝒮.finite_toSet.subset ?_
  rintro V ⟨hV, β, ⟨wβ, r, d, hwβ, hr, hd, rfl⟩, hne⟩
  by_contra hV𝒮
  apply hne
  have hηV : V.isIrreducible.genericPoint ∈ (V : Set (Q.chain.model x.1)) :=
    (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  have hrS : ∀ S, r S = branchNumber (c S) (V : Set (Q.chain.model x.1)) := fun S => by
    rcases hr S with ⟨P, hP, hrP⟩ | ⟨hn, -⟩
    · rw [hrP, isLabelCentre_unique hP (hc S)]
    · exact absurd (hc S) (hn _)
  have hdS : ∀ S, d S = defaultWeight Q.scale ((Θ.coeff (c S) : ℚ) : ℝ) := fun S =>
    isLabelDefault_unique (hd S) ⟨_, TerminalChain.isLabelCoefficient_of_isLabelCentre (hc S), rfl⟩
  have hwa : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V → ∀ a,
      HasLogDiscrepancy (Q.chain.modelStructure x.1) Θ v a →
        wβ v = difficultyWeight Q.scale (2 - a) := by
    intro v hv a ha
    obtain ⟨-, a', ha', h⟩ := hwβ v hv
    rw [h, Bracket.HasLogDiscrepancy.unique
      (Bracket.IsValuationLogDiscrepancy.hasLogDiscrepancy ha') ha]
  by_cases hcase : ∃ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧ wβ v ≠ 0
  · -- some valuation at `V` has positive weight: `V` carries the echoes of a single label
    obtain ⟨v₀, hv₀, hw₀⟩ := hcase
    obtain ⟨-, a₀, ha₀, hw₀eq⟩ := hwβ v₀ hv₀
    have ha₀2 : a₀ < 2 := lt_two_of_difficultyWeight_ne_zero hN fun h => hw₀ (hw₀eq.trans h)
    obtain ⟨S₀, j₀, hecho₀, -⟩ := h𝒮 V hV hV𝒮 v₀ hv₀ a₀ ha₀2
      (Bracket.IsValuationLogDiscrepancy.hasLogDiscrepancy ha₀)
    obtain ⟨-, -, hS₀L, hVS₀, -, hη, -, -, -⟩ := hecho₀
    obtain ⟨h₀, -, rfl⟩ := Finset.mem_image.mp hS₀L
    set b : ℝ := ((Θ.coeff (c h₀) : ℚ) : ℝ) with hbdef
    have hb1 : b < 1 := by rw [hbdef]; exact_mod_cast hlt _ hS₀L
    have hlab : (∑ᶠ S, r S * d S) = d h₀ := by
      rw [finsum_eq_single _ h₀ (fun S hS => ?_)]
      · rw [hrS, Bracket.branchNumber_eq_one (sY := Q.chain.modelStructure x.1) hdim (c h₀) hV hVS₀
          ((mem_oneLabelSmoothLocus_iff.mp hη).2.1 _ hS₀L), one_mul]
      · rw [hrS, branchNumber_eq_zero_of_not_subset, zero_mul]
        intro hVS
        exact hS (hcinj (eq_of_mem_oneLabelSmoothLocus hη (hcL S) hS₀L (hVS hηV) (hVS₀ hηV)))
    have hex : ∀ j : ℕ, 1 ≤ j → ∃ ξ, IsSurfaceEcho (Q.chain.modelStructure x.1) L (c h₀) V j ξ :=
      fun j hj => exists_isSurfaceEcho hnv hdim hS₀L hVS₀ hV hη hj
    let ξ : ℕ → Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) :=
      fun j => if hj : 1 ≤ j then (hex j hj).choose else 1
    have hξ : ∀ j (hj : 1 ≤ j), IsSurfaceEcho (Q.chain.modelStructure x.1) L (c h₀) V j (ξ j) :=
      fun j hj => by simp only [ξ, dif_pos hj]; exact (hex j hj).choose_spec
    have hξa : ∀ j (hj : 1 ≤ j), HasLogDiscrepancy (Q.chain.modelStructure x.1) Θ (ξ j)
        (1 + j * (1 - b)) := fun j hj => (hξ j hj).hasLogDiscrepancy hΘ.1.1 hsupp hlt
    have hξc : ∀ j (hj : 1 ≤ j), MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) (ξ j) V :=
      fun j hj => (hξ j hj).2.2.2.2.2.2.2.1
    have hξw : ∀ j (hj : 1 ≤ j), wβ (ξ j) = difficultyWeight Q.scale (1 - j * (1 - b)) :=
      fun j hj => by rw [hwa _ (hξc j hj) _ (hξa j hj)]; congr 1; ring
    have hval : (∑ᶠ (v) (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V),
        wβ v) = defaultWeight Q.scale b := by
      rw [defaultWeight]
      change ∑ᶠ v ∈ {v | MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V}, wβ v =
        ∑ᶠ j ∈ {j : ℕ | 1 ≤ j}, difficultyWeight Q.scale (1 - j * (1 - b))
      rw [← finsum_mem_inter_support, ← finsum_mem_inter_support (s := {j : ℕ | 1 ≤ j})]
      symm
      refine finsum_mem_eq_of_bijOn ξ ⟨fun j hj' => ?_, fun j₁ h₁' j₂ h₂' h12 => ?_,
        fun v hv' => ?_⟩ fun j hj' => (hξw j hj'.1).symm
      · obtain ⟨hj, hjne⟩ := hj'
        refine ⟨hξc j hj, ?_⟩
        change wβ (ξ j) ≠ 0
        rw [hξw j hj]
        exact hjne
      · have h₁ : 1 ≤ j₁ := h₁'.1
        have h₂ : 1 ≤ j₂ := h₂'.1
        have ha₁ := hξa j₁ h₁
        rw [h12] at ha₁
        have := Bracket.HasLogDiscrepancy.unique ha₁ (hξa j₂ h₂)
        have hpos : 0 < 1 - b := by linarith
        have : (j₁ : ℝ) = j₂ := by
          have := mul_right_cancel₀ hpos.ne' (by linarith : (j₁ : ℝ) * (1 - b) = j₂ * (1 - b))
          exact this
        exact_mod_cast this
      · obtain ⟨hv, hvne⟩ := hv'
        obtain ⟨-, a, ha, hwv⟩ := hwβ v hv
        have ha2 : a < 2 := lt_two_of_difficultyWeight_ne_zero hN fun h => hvne (hwv.trans h)
        obtain ⟨S, j, hecho, -⟩ := h𝒮 V hV hV𝒮 v hv a ha2
          (Bracket.IsValuationLogDiscrepancy.hasLogDiscrepancy ha)
        obtain ⟨-, -, hSL, hVS, -, -, hj, -, -⟩ := id hecho
        obtain rfl : S = c h₀ := eq_of_mem_oneLabelSmoothLocus hη hSL hS₀L (hVS hηV) (hVS₀ hηV)
        have hvj : v = ξ j := hecho.eq (hξ j hj)
        refine ⟨j, ⟨hj, ?_⟩, hvj.symm⟩
        change difficultyWeight Q.scale (1 - j * (1 - b)) ≠ 0
        rw [← hξw j hj, ← hvj]
        exact hvne
    rw [hlab, hval, hdS, hbdef, sub_self]
  · -- no valuation at `V` has positive weight: no label of positive coefficient contains `V`
    push Not at hcase
    have h1 : (∑ᶠ (v) (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V),
        wβ v) = 0 :=
      finsum_eq_zero_of_forall_eq_zero fun v => by
        rw [finsum_eq_if]
        split_ifs with h
        · exact hcase v h
        · rfl
    have h2 : (∑ᶠ S, r S * d S) = 0 := finsum_eq_zero_of_forall_eq_zero fun S => by
      by_cases hVS : (V : Set (Q.chain.model x.1)) ⊆ (c S).support
      · rw [hdS S]
        by_cases hb : ((Θ.coeff (c S) : ℚ) : ℝ) ≤ 0
        · rw [Bracket.defaultWeight_of_nonpos _ hb, mul_zero]
        · exfalso
          push Not at hb
          haveI := Bracket.isRegularLocalRing_stalk_of_coheight_le_two hΘ hQf
            (Bracket.coheight_genericPoint_eq_two hnv hdim hV).le
          obtain ⟨v, hv, a, ha, hla⟩ := Bracket.exists_isCentre_hasLogDiscrepancy_le hΘ.1.1 hnv
            hdim hV hVS (by exact_mod_cast hb)
          refine absurd (hcase v hv) ?_
          rw [hwa v hv a hla]
          intro h0
          rw [difficultyWeight_eq_zero_iff hN] at h0
          linarith
      · rw [hrS, branchNumber_eq_zero_of_not_subset hVS, zero_mul]
    rw [h1, h2]
    rfl

/-- The surface part of a difficulty has finite support. -/
private theorem finite_support_ite_isSurfaceBracket
    {β : IrreducibleCloseds (Q.chain.model x.1) → ℤ}
    (hβ : ∀ V : IrreducibleCloseds (Q.chain.model x.1),
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 → Q.IsSurfaceBracket x V (β V)) :
    (Function.support fun V : IrreducibleCloseds (Q.chain.model x.1) =>
      if topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 then β V else 0).Finite := by
  refine finite_setOf_isSurfaceBracket_ne_zero.subset fun V hV => ?_
  by_cases h2 : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2
  · rw [Function.mem_support, if_pos h2] at hV
    exact ⟨h2, β V, hβ V h2, hV⟩
  · rw [Function.mem_support, if_neg h2] at hV
    exact absurd rfl hV

end Side

section IsoHelpers

open MMP.Mori MMP.Fourfold

/-! ### Valuations of prime divisors -/

/-- `ord_P` regarded through a composite is `ord_P` regarded through the first map, restricted
along the second. -/
private theorem valuationOver_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (P : MMP.Mori.PrimeDivisor X) (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsDominant f] [IsDominant g] [IsDominant (f ≫ g)] :
    P.valuationOver (f ≫ g) = (P.valuationOver f).comap (functionFieldMap g) := by
  ext t
  simp only [PrimeDivisor.valuationOver_apply, Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- `valuationOver` only depends on the morphism. -/
private theorem valuationOver_congr {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] (P : MMP.Mori.PrimeDivisor X) {f g : X ⟶ Y} [hf : IsDominant f]
    [hg : IsDominant g] (h : f = g) : P.valuationOver f = P.valuationOver g := by
  subst h
  rfl

/-- The image of a prime divisor under an isomorphism. -/
private noncomputable def mapOfIso {V W : Scheme.{0}} (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) :
    MMP.Mori.PrimeDivisor W :=
  AlgebraicGeometry.PrimeDivisor.ofCoheightOne (e.hom Q.genericPoint) (by
    rw [coheight_eq_of_isOpenImmersion e.hom]
    exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q)

private theorem genericPoint_mapOfIso {V W : Scheme.{0}} (e : V ≅ W)
    (Q : MMP.Mori.PrimeDivisor V) : (mapOfIso e Q).genericPoint = e.hom Q.genericPoint :=
  AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _

/-- Transport of prime divisors along an isomorphism. -/
private noncomputable def primeDivisorEquivOfIso {V W : Scheme.{0}} (e : V ≅ W) :
    MMP.Mori.PrimeDivisor V ≃ MMP.Mori.PrimeDivisor W where
  toFun := mapOfIso e
  invFun := mapOfIso e.symm
  left_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (mapOfIso e.symm (mapOfIso e Q)).genericPoint = _
    rw [genericPoint_mapOfIso, genericPoint_mapOfIso, ← Scheme.Hom.comp_apply]
    simp
  right_inv Q := by
    apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    change (mapOfIso e (mapOfIso e.symm Q)).genericPoint = _
    rw [genericPoint_mapOfIso, genericPoint_mapOfIso, ← Scheme.Hom.comp_apply]
    simp

private theorem genericPoint_primeDivisorEquivOfIso {V W : Scheme.{0}} (e : V ≅ W)
    (Q : MMP.Mori.PrimeDivisor V) :
    (primeDivisorEquivOfIso e Q).genericPoint = e.hom Q.genericPoint :=
  genericPoint_mapOfIso e Q

/-- Transport along an isomorphism preserves the divisorial valuation. -/
private theorem divisorialValuation_primeDivisorEquivOfIso {V W : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (e : V ≅ W) [IsDominant e.hom] (Q : MMP.Mori.PrimeDivisor V) :
    Q.divisorialValuation.comap (functionFieldMap e.hom) =
      (primeDivisorEquivOfIso e Q).divisorialValuation := by
  ext g
  rw [Valuation.comap_apply]
  by_cases hg : g = 0
  · subst hg; simp
  have hg' : functionFieldMap e.hom g ≠ 0 := (map_ne_zero _).mpr hg
  rw [PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    MMP.Positivity.ord_functionFieldMap_of_isIso e.hom Q (primeDivisorEquivOfIso e Q)
      (genericPoint_mapOfIso e Q).symm]

/-- `ord_Q` regarded through `e ≫ b`, for an isomorphism `e`, is `ord` of the transported prime
divisor regarded through `b`. -/
private theorem valuationOver_iso_comp {V W Z : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [IsIntegral Z] (e : V ≅ W) (Q : MMP.Mori.PrimeDivisor V) (b : W ⟶ Z) [IsDominant b]
    [IsDominant e.hom] [IsDominant (e.hom ≫ b)] :
    Q.valuationOver (e.hom ≫ b) = (primeDivisorEquivOfIso e Q).valuationOver b := by
  rw [valuationOver_comp, PrimeDivisor.valuationOver, divisorialValuation_primeDivisorEquivOfIso]
  rfl

/-- The inverse transform along an isomorphism has, at `P`, the coefficient at the image of
`P`. -/
private theorem coeff_inverseTransformDivisor_iso {V W : Scheme.{0}} (e : V ≅ W)
    (D : MMP.Mori.QDivisor W) (P : MMP.Mori.PrimeDivisor V) :
    (inverseTransformDivisor e.hom D).coeff P = D.coeff (primeDivisorEquivOfIso e P) := by
  have htop : biregularLocus e.hom = ⊤ :=
    top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff e.hom).mpr inferInstance))
  exact MMP.Fourfold.Oai4C1.inverseTransformDivisor_apply_of_map_genericPoint
    (genericPoint_mapOfIso e P).symm (by rw [htop]; trivial) D

section IsoTransport

open MMP.Fourfold.Oai4C1.CommonModel

/-- **Pull-back of Cartier divisors along a composite**: `g^*(f^*L) = (f ∘ g)^*L`. -/
private theorem isPullback_comp {X Y Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]
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
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hzU (hB'' _)
    (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
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
      (MMP.Fourfold.mem_irreducibleComponent_of_irreducibleSpace (pointComponent ((g ≫ f) z)) _)
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

/-- **Pull-back of rational forms along a composite**: `g^*(f^*τ) = (f ∘ g)^*τ`, for
morphisms inducing isomorphisms of function fields. -/
private theorem pullbackRationalPluriForms_comp {X Y Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral Z] {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    (f : Y ⟶ X) (g : Z ⟶ Y) [IsDominant f]
    [IsDominant g] [LocallyOfFiniteType (f ≫ sX)] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg ℂ X.functionField).toNat = d) {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower ℂ X.functionField Z.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField Z.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  have hd' : (Algebra.trdeg ℂ Y.functionField).toNat = d := by
    rw [← trdeg_functionField_eq_of_bijective sX f hf]
    exact hd
  obtain ⟨ω1, hω1⟩ := exists_isPullbackGenerator_of_bijective (f ≫ sX) g hg hd'
  have hω' : IsPullbackGenerator Z.functionField
      (topFormsMap ℂ X.functionField Y.functionField d ω0) :=
    MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω1 hω0.2.1 hω0.2.2
  exact MMP.Threefold.Mori.Helpers.pullbackForms_comp hω0 hω' τ

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {X U : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [IsIntegral U]
    (hX : IsNormalVariety ℂ sX)
    {p : U ⟶ X} [IsDominant p] (hp : IsBirationalMorphism p) {n : ℕ}
    (hn : topologicalKrullDim X = n) {m : ℤ} {τ : RationalPluriForms sX n m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX p τ ≠ 0 := by
  let := functionFieldAlgebra sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hbij := hp.functionFieldMap_bijective
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX p hbij hd
  let := functionFieldAlgebra (p ≫ sX)
  let := functionFieldMapAlgebra p
  have := isScalarTower_functionFieldMap sX p
  have hpull : pullbackRationalPluriForms sX p τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField U.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

variable {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- The divisor `(Y, f ≫ g, E)` over `W`, for a divisor `(Y, f, E)` over `V` and a dominant open
immersion `g : V ⟶ W`. -/
private noncomputable def compOpen (g : V ⟶ W) [IsOpenImmersion g] [IsDominant g]
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : g ≫ sW = sV)
    (D : DivisorOver ℂ sV) : DivisorOver ℂ sW where
  Y := D.Y
  f := D.f ≫ g
  isNormalVariety := by
    have := D.isNormalVariety
    rwa [Category.assoc, hs]
  isBirationalMorphism := by
    haveI := D.isIntegral
    exact isBirationalMorphism_comp D.isBirationalMorphism
      (isBirationalMorphism_of_isOpenImmersion g ⊤ dense_univ)
  E := D.E

/-- The valuation of `(Y, f ≫ g, E)` is that of `(Y, f, E)` carried along `g`. -/
private theorem valuation_compOpen (g : V ⟶ W) [IsOpenImmersion g] [IsDominant g]
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : g ≫ sW = sV)
    (D : DivisorOver ℂ sV) :
    (compOpen g hs D).valuation = D.valuation.comap (functionFieldMap g) := by
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  haveI := (compOpen g hs D).isDominant
  refine Valuation.ext fun t => ?_
  change D.E.valuationOver (D.f ≫ g) t = D.E.valuationOver D.f (functionFieldMap g t)
  rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.valuationOver_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- **Log discrepancies are invariant under isomorphisms of pairs.** Let `φ : V ≅ W` be an
isomorphism of normal varieties over `ℂ`, `B'` a `ℚ`-divisor on `W` and `B` the divisor on `V`
with `coeff_Γ B = coeff_{φ(Γ)} B'`. If `(Y, f, E)` is a divisor over `V` and `(Y', f', E')` one
over `W` with the corresponding valuation, then `a(E, V, B) = a(E', W, B')`. -/
private theorem eq_of_isLogDiscrepancy_of_iso [CompactSpace V] (φ : V ≅ W)
    {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} (hs : φ.hom ≫ sW = sV) {B : QDivisor V}
    {B' : QDivisor W}
    (hB : ∀ Γ : MMP.Mori.PrimeDivisor V,
      B.coeff Γ = B'.coeff (OpenWeilRestriction.primeDivisorMap φ.hom Γ))
    {n n' : ℕ} {D : DivisorOver ℂ sV} {D' : DivisorOver ℂ sW} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sV n (QDivisor.toRDivisor B) D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sW n' (QDivisor.toRDivisor B') D' a')
    (hv : D'.valuation = D.valuation.comap (functionFieldMap φ.hom)) : a = a' := by
  subst hs
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp : IsProper D.f := ha.2.1
  obtain ⟨hW, -, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, -, hCc, hdec, -, -⟩ := id ha'
  obtain ⟨hV, -, -, -, ⟨K₀, hK₀, -⟩, -⟩ := id ha
  have hnn : n = n' := by
    have h1 := hK₀.topologicalKrullDim_eq
    have h2 := hK'.topologicalKrullDim_eq
    rw [(Scheme.homeoOfIso φ).isHomeomorph.topologicalKrullDim_eq] at h1
    exact_mod_cast h1.symm.trans h2
  subst hnn
  haveI : LocallyOfFiniteType sW := hW.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (φ.hom ≫ sW) := hV.1.toLocallyOfFiniteType
  haveI : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace D.f
  have hbφ : IsBirationalMorphism φ.hom := isBirationalMorphism_of_isIso _
  have hbij : Function.Bijective (functionFieldMap φ.hom) := hbφ.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sW)
    hK'.topologicalKrullDim_eq
  choose L hL using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant φ.hom (hCc i)
  have hLc : ∀ i, (L i).IsCartier := fun i => (hL i).isCartier (hCc i)
  choose M hM using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hLc i)
  set Dφ := compOpen φ.hom rfl D
  haveI : IsDominant (D.f ≫ φ.hom) := Dφ.isDominant
  have hpφ : IsProper Dφ.f := by
    change IsProper (D.f ≫ φ.hom)
    infer_instance
  have hord : D.ordPullback (pullbackRationalPluriForms sW φ.hom ω) = Dφ.ordPullback ω := by
    change D.E.ordForm (pullbackRationalPluriForms (φ.hom ≫ sW) D.f
      (pullbackRationalPluriForms sW φ.hom ω)) =
        D.E.ordForm (pullbackRationalPluriForms sW (D.f ≫ φ.hom) ω)
    rw [pullbackRationalPluriForms_comp φ.hom D.f hbij
      (IsBirationalMorphism.functionFieldMap_bijective D.isBirationalMorphism) hd ω]
    rfl
  have h1 : MMP.Intersection.IsLogDiscrepancy sW n (QDivisor.toRDivisor B') Dφ
      (1 + (Dφ.ordPullback ω : ℝ) - ∑ i, r i * (M i).coeff Dφ.E) :=
    ⟨hW, hpφ, ω, hω, ⟨K', hK', hK'c⟩, m, r, C, M, hCc, hdec, fun i => ⟨_, isPullback_comp
      (hL i) (hM i) (fun Z =>
      MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ φ.hom) (C i) Z)⟩, rfl⟩
  have e1 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha' h1
    (hv.trans (valuation_compOpen φ.hom rfl D).symm)
  have hne : pullbackRationalPluriForms sW φ.hom ω ≠ 0 :=
    pullbackRationalPluriForms_ne_zero hW hbφ hK'.topologicalKrullDim_eq hω
  have hcan : (divisorOfForm (pullbackRationalPluriForms sW φ.hom ω)).IsCanonicalDivisor
      (φ.hom ≫ sW) n := by
    have := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hV hK₀ hne
    rw [one_smul] at this
    exact hK₀.of_linearlyEquivalent this
  have hdec2 : ∀ Γ : MMP.Mori.PrimeDivisor V,
      ((Γ.ordForm (pullbackRationalPluriForms sW φ.hom ω) : ℤ) : ℝ) +
        (QDivisor.toRDivisor B).coeff Γ = ∑ i, r i * ((L i).coeff Γ : ℝ) := by
    intro Γ
    set Γ' := OpenWeilRestriction.primeDivisorMap φ.hom Γ
    have hΓ : φ.hom Γ.genericPoint = Γ'.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm
    rw [MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso φ.hom hbij hd Γ Γ' hΓ ω,
      QDivisor.coeff_toRDivisor, hB Γ]
    simp_rw [MMP.Positivity.coeff_eq_of_isPullback Γ Γ' hΓ (hCc _) (hL _)]
    have := hdec Γ'
    rwa [QDivisor.coeff_toRDivisor] at this
  have h2 : MMP.Intersection.IsLogDiscrepancy (φ.hom ≫ sW) n (QDivisor.toRDivisor B) D
      (1 + (Dφ.ordPullback ω : ℝ) - ∑ i, r i * (M i).coeff Dφ.E) := by
    refine ⟨hV, hp, _, hne, ⟨_, hcan, fun Γ => coeff_divisorOfForm _ Γ⟩, m, r, L, M, hLc,
      hdec2, fun i => ⟨_, hM i⟩, ?_⟩
    rw [hord]
    rfl
  exact (MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha h2).trans e1.symm

end IsoTransport

/-! ### Transport along an isomorphism of normal varieties -/

section Transport

variable {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
  [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]

/-- Transporting a valuation along `e` and back along `e⁻¹` gives it back. -/
private theorem comap_inv_comap_hom (e : V ≅ W)
    (v : Valuation V.functionField (WithZero (Multiplicative ℤ))) :
    (v.comap (functionFieldMap e.hom)).comap (functionFieldMap e.inv) = v := by
  ext t
  simp only [Valuation.comap_apply]
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
    MMP.Positivity.DivisorOver.functionFieldMap_congr (e.hom_inv_id),
    MMP.Mori.functionFieldMap_id_apply]

/-- The centre of a transported valuation is the image of the centre. -/
private theorem isCentre_comap (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    (hs : e.hom ≫ sW = sV) {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    {Z : IrreducibleCloseds V} (h : MMP.Intersection.IsCentre ℂ sV v Z) :
    ∃ Z' : IrreducibleCloseds W, MMP.Intersection.IsCentre ℂ sW
      (v.comap (functionFieldMap e.hom)) Z' ∧ (Z' : Set W) = e.hom.base '' Z := by
  obtain ⟨D, hp, rfl, rfl⟩ := h
  refine ⟨(compOpen e.hom hs D).center,
    ⟨compOpen e.hom hs D, ?_, (valuation_compOpen e.hom hs D).symm, rfl⟩, ?_⟩
  · change IsProper (D.f ≫ e.hom)
    infer_instance
  · rw [MMP.Positivity.DivisorOver.center_eq_closureSingleton,
      MMP.Positivity.DivisorOver.center_eq_closureSingleton]
    change closure {(D.f ≫ e.hom) D.E.genericPoint} = e.hom.base '' closure {D.f D.E.genericPoint}
    have := (Scheme.homeoOfIso e).image_closure ({D.f D.E.genericPoint} : Set V)
    rw [Set.image_singleton] at this
    rw [Scheme.Hom.comp_apply]
    exact this.symm

/-- A transported exceptional valuation is exceptional. -/
private theorem isExceptionalValuation_comap (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV)
    {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sV v) :
    MMP.Intersection.IsExceptionalValuation ℂ sW (v.comap (functionFieldMap e.hom)) := by
  obtain ⟨D, hp, rfl, hc⟩ := h
  refine ⟨compOpen e.hom hs D, ?_, (valuation_compOpen e.hom hs D).symm, ?_⟩
  · change IsProper (D.f ≫ e.hom)
    infer_instance
  · rw [MMP.Positivity.DivisorOver.codimension_center] at hc ⊢
    change 2 ≤ Order.coheight ((D.f ≫ e.hom) D.E.genericPoint)
    rwa [Scheme.Hom.comp_apply, Topology.IsOpenEmbedding.coheight_eq _ e.hom.isOpenEmbedding]

/-- Log discrepancies are carried along an isomorphism of pairs. -/
private theorem isValuationLogDiscrepancy_comap [CompactSpace V] (e : V ≅ W)
    {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) {B : QDivisor V}
    {B' : QDivisor W} (hB : ∀ Γ, B.coeff Γ = B'.coeff (primeDivisorEquivOfIso e Γ))
    (hB' : MMP.Mori.IsPair sW B') {v : Valuation V.functionField (WithZero (Multiplicative ℤ))}
    {a : ℝ} (h : IsValuationLogDiscrepancy sV B v a) :
    IsValuationLogDiscrepancy sW B' (v.comap (functionFieldMap e.hom)) a := by
  obtain ⟨n, D, hp, rfl, ha⟩ := h
  obtain ⟨-, n₀, K, hK, -⟩ := id hB'
  haveI := D.isIntegral
  haveI := D.isNormal
  haveI := D.isLocallyNoetherian
  haveI := D.isDominant
  have hp' : IsProper (compOpen e.hom hs D).f := by
    change IsProper (D.f ≫ e.hom)
    infer_instance
  obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hB' hK (compOpen e.hom hs D)
  have ha' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hp'
  have hB2 : ∀ Γ : MMP.Mori.PrimeDivisor V,
      B.coeff Γ = B'.coeff (OpenWeilRestriction.primeDivisorMap e.hom Γ) := fun Γ => by
    have hΓ : primeDivisorEquivOfIso e Γ = OpenWeilRestriction.primeDivisorMap e.hom Γ :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((genericPoint_primeDivisorEquivOfIso e Γ).trans
          (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ _).symm)
    rw [hB Γ, hΓ]
  have hac := eq_of_isLogDiscrepancy_of_iso e hs hB2 ha ha' (valuation_compOpen e.hom hs D)
  exact ⟨n₀, compOpen e.hom hs D, hp', valuation_compOpen e.hom hs D, hac ▸ ha'⟩

end Transport

section IsoSchemes

variable {V W : Scheme.{0}}

/-- An isomorphism carries the closure of a point to the closure of its image. -/
private theorem image_closure_singleton (e : V ≅ W) (x : V) :
    e.hom.base '' closure ({x} : Set V) = closure {e.hom x} := by
  have := (Scheme.homeoOfIso e).image_closure ({x} : Set V)
  rw [Set.image_singleton] at this
  exact this

private theorem inv_comp_eq_of_hom_comp_eq (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV) : e.inv ≫ sV = sW := by
  rw [← hs, Iso.inv_hom_id_assoc]

/-- The support of a transported prime divisor is the image of the support. -/
private theorem support_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    (primeDivisorEquivOfIso e P).support = e.hom.base '' P.support := by
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure, image_closure_singleton]
  have h := genericPoint_primeDivisorEquivOfIso e P
  exact congrArg (fun x => closure {x}) h

private theorem primeDivisorEquivOfIso_symm_apply (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    primeDivisorEquivOfIso e.symm (primeDivisorEquivOfIso e P) = P :=
  (primeDivisorEquivOfIso e).left_inv P

/-- The ideal sheaf of a transported prime divisor is the image of the ideal sheaf. -/
private theorem idealSheaf_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    P.idealSheaf.map e.hom = (primeDivisorEquivOfIso e P).idealSheaf := by
  have := P.integral
  have := (primeDivisorEquivOfIso e P).integral
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme P.idealSheaf _ rfl,
    Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme
      (primeDivisorEquivOfIso e P).idealSheaf _ rfl, Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  ext1
  change closure (e.hom.base '' P.support) = (primeDivisorEquivOfIso e P).support
  rw [support_primeDivisorEquivOfIso]
  exact ((Scheme.homeoOfIso e).isClosedMap _ P.idealSheaf.support.isClosed).closure_eq

/-- The closed subschemes of a prime divisor and of its transport are isomorphic. -/
private noncomputable def subschemeIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    P.idealSheaf.subscheme ≅ (primeDivisorEquivOfIso e P).idealSheaf.subscheme where
  hom := P.idealSheaf.subschemeMap (primeDivisorEquivOfIso e P).idealSheaf e.hom
    (idealSheaf_primeDivisorEquivOfIso e P).ge
  inv := (primeDivisorEquivOfIso e P).idealSheaf.subschemeMap P.idealSheaf e.inv (by
    have h := idealSheaf_primeDivisorEquivOfIso e.symm (primeDivisorEquivOfIso e P)
    rw [primeDivisorEquivOfIso_symm_apply] at h
    exact h.ge)
  hom_inv_id := by
    rw [← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
    simp
  inv_hom_id := by
    rw [← cancel_mono (Scheme.IdealSheafData.subschemeι _)]
    simp

private theorem subschemeIso_hom_ι (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V) :
    (subschemeIso e P).hom ≫ (primeDivisorEquivOfIso e P).idealSheaf.subschemeι =
      P.idealSheaf.subschemeι ≫ e.hom :=
  Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ (idealSheaf_primeDivisorEquivOfIso e P).ge

/-- Isomorphic schemes have isomorphic normalizations, compatibly with the normalization
morphisms. -/
private theorem exists_iso_normalizationScheme_of_iso {X X' : Scheme}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hX' : ∀ U : X'.Opens, IsCompact (U : Set X') → (irreducibleComponents U).Finite)
    (e : X ≅ X') :
    ∃ E : X.normalizationScheme hX ≅ X'.normalizationScheme hX',
      E.hom ≫ X'.normalization hX' = X.normalization hX ≫ e.hom := by
  have hgen : ∀ {Y Y' : Scheme} (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
      (irreducibleComponents U).Finite) (e : Y ≅ Y') (η : genericPoints (Y.normalizationScheme hY)),
      (Y.normalization hY ≫ e.hom) η.1 ∈ genericPoints Y' := fun hY e η =>
    genericPoints_image_of_generalizingMap _ (Scheme.homeoOfIso e).isOpenEmbedding.generalizingMap
      (Scheme.normalization_mem_genericPoints _ hY η.2)
  have := X.isNormal_normalizationScheme hX
  have := X'.isNormal_normalizationScheme hX'
  obtain ⟨a, ha, -⟩ := Scheme.existsUnique_lift_normalization hX' _ (hgen hX e)
  obtain ⟨b, hb, -⟩ := Scheme.existsUnique_lift_normalization hX _ (hgen hX' e.symm)
  obtain ⟨g, -, hu⟩ := Scheme.existsUnique_lift_normalization hX (X.normalization hX)
    (fun η => Scheme.normalization_mem_genericPoints _ hX η.2)
  obtain ⟨g', -, hu'⟩ := Scheme.existsUnique_lift_normalization hX' (X'.normalization hX')
    (fun η => Scheme.normalization_mem_genericPoints _ hX' η.2)
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · rw [hu (a ≫ b) (by dsimp only; rw [Category.assoc, hb, ← Category.assoc, ha]; simp),
      hu (𝟙 _) (by dsimp only; simp)]
  · rw [hu' (b ≫ a) (by dsimp only; rw [Category.assoc, ha, ← Category.assoc, hb]; simp),
      hu' (𝟙 _) (by dsimp only; simp)]

/-- The normalizations of a prime divisor and of its transport are isomorphic over the
isomorphism. -/
private theorem exists_iso_primeDivisorNormalizationScheme (e : V ≅ W)
    (P : MMP.Mori.PrimeDivisor V) :
    ∃ E : primeDivisorNormalizationScheme P ≅
        primeDivisorNormalizationScheme (primeDivisorEquivOfIso e P),
      E.hom ≫ primeDivisorNormalization (primeDivisorEquivOfIso e P) =
        primeDivisorNormalization P ≫ e.hom := by
  have := P.integral
  have := (primeDivisorEquivOfIso e P).integral
  obtain ⟨E, hE⟩ := exists_iso_normalizationScheme_of_iso
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) (subschemeIso e P)
  refine ⟨E, ?_⟩
  change E.hom ≫ (Scheme.normalization _ _ ≫ Scheme.IdealSheafData.subschemeι _) =
    (Scheme.normalization _ _ ≫ Scheme.IdealSheafData.subschemeι _) ≫ e.hom
  rw [← Category.assoc, hE, Category.assoc, subschemeIso_hom_ι, Category.assoc]

/-- **Branch numbers are invariant under isomorphism.** -/
private theorem branchNumber_primeDivisorEquivOfIso (e : V ≅ W) (P : MMP.Mori.PrimeDivisor V)
    (Z : Set V) :
    branchNumber (primeDivisorEquivOfIso e P) (e.hom.base '' Z) = branchNumber P Z := by
  obtain ⟨E, hE⟩ := exists_iso_primeDivisorNormalizationScheme e P
  have key : ∀ R : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme P),
      primeDivisorNormalization (primeDivisorEquivOfIso e P) ''
          (primeDivisorEquivOfIso E R).support =
        e.hom.base '' (primeDivisorNormalization P '' R.support) := by
    intro R
    rw [support_primeDivisorEquivOfIso, Set.image_image, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    simpa using congrArg (fun f => f.base x) hE
  have hinj : Function.Injective (Set.image e.hom.base) :=
    Set.image_injective.mpr (Scheme.homeoOfIso e).injective
  unfold branchNumber
  rw [← Set.ncard_image_of_injective _ (primeDivisorEquivOfIso E).injective]
  congr 1
  ext R'
  constructor
  · intro h
    refine ⟨(primeDivisorEquivOfIso E).symm R', hinj ?_, Equiv.apply_symm_apply _ _⟩
    rwa [← key, Equiv.apply_symm_apply]
  · rintro ⟨R, hR, rfl⟩
    change _ = _
    rw [key]
    exact congrArg _ hR

end IsoSchemes

/-! ### Finite sums -/

/-- A finsum over `s` whose support in `s` lies in a finite set `t` is a sum over `t`. -/
private theorem natCast_finsum_mem_eq_sum {α : Type*} {f : α → ℕ} {s : Set α} (t : Finset α)
    (h : s ∩ Function.support f ⊆ t) [DecidablePred (· ∈ s)] :
    ((∑ᶠ a ∈ s, f a : ℕ) : ℤ) = ∑ a ∈ t, if a ∈ s then (f a : ℤ) else 0 := by
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (by rwa [Set.support_indicator]),
    Nat.cast_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Set.indicator_apply]
  split_ifs <;> simp

/-- `natCast_finsum_mem_eq_sum` for a sum over the values satisfying a predicate. -/
private theorem natCast_finsum_eq_sum {α : Type*} {f : α → ℕ} {P : α → Prop} (t : Finset α)
    (h : ∀ a, P a → f a ≠ 0 → a ∈ t) [DecidablePred P] :
    ((∑ᶠ (a) (_ : P a), f a : ℕ) : ℤ) = ∑ a ∈ t, if P a then (f a : ℤ) else 0 :=
  natCast_finsum_mem_eq_sum (s := {a | P a}) t fun a ⟨ha, hne⟩ => h a ha hne

/-- **Comparing two weight sums along a bijection.** Let `Φ : α → β` be injective with right
inverse `Ψ`, and let the predicates `P` on `α` and `P'` on `β` correspond along `Φ`. If the
supports of `f` on `P` and of `f'` on `P'` are pulled back into a finite set `F`, on which `f`
and `f' ∘ Φ` agree with `w` and `w'` where `P` holds, then
`∑_{P} f - ∑_{P'} f' = ∑_{a ∈ F, P a} (w a - w' a)`. -/
private theorem natCast_finsum_sub_finsum_eq_sum {α β : Type*} {P : α → Prop} {P' : β → Prop}
    [DecidablePred P] [DecidablePred P'] {f w w' : α → ℕ} {f' : β → ℕ} {Φ : α → β} {Ψ : β → α}
    (hΦ : Function.Injective Φ) (hΦΨ : ∀ b, Φ (Ψ b) = b) (hP : ∀ a, P' (Φ a) ↔ P a)
    (F : Finset α) (hf : ∀ a, P a → f a ≠ 0 → a ∈ F) (hf' : ∀ b, P' b → f' b ≠ 0 → Ψ b ∈ F)
    (hw : ∀ a ∈ F, P a → f a = w a) (hw' : ∀ a ∈ F, P a → f' (Φ a) = w' a) :
    ((∑ᶠ (a) (_ : P a), f a : ℕ) : ℤ) - ((∑ᶠ (b) (_ : P' b), f' b : ℕ) : ℤ) =
      ∑ a ∈ F, if P a then ((w a : ℤ) - w' a) else 0 := by
  classical
  rw [natCast_finsum_eq_sum F hf, natCast_finsum_eq_sum (F.image Φ)
    (fun b hb hne => Finset.mem_image.2 ⟨Ψ b, hf' b hb hne, hΦΨ b⟩),
    Finset.sum_image fun a _ b _ h => hΦ h, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  by_cases hp : P a
  · rw [if_pos hp, if_pos ((hP a).2 hp), if_pos hp, hw a ha hp, hw' a ha hp]
  · rw [if_neg hp, if_neg (mt (hP a).1 hp), if_neg hp, sub_zero]

/-- A sum over the values satisfying `P` is a sum along an injection `g` whose image is the set
of values satisfying `P`. -/
private theorem finsum_eq_finsum_comp_of_injective {α β M : Type*} [AddCommMonoid M]
    {f : β → M} {P : β → Prop} {R : α → Prop} {g : α → β} (hg : Function.Injective g)
    (h : ∀ b, P b ↔ ∃ a, R a ∧ g a = b) :
    ∑ᶠ (b) (_ : P b), f b = ∑ᶠ (a) (_ : R a), f (g a) := by
  have hs : {b | P b} = g '' {a | R a} := Set.ext h
  have := finsum_mem_image (f := f) (s := {a | R a}) hg.injOn
  rwa [← hs] at this

end IsoHelpers

/-! ### Irreducible closed subsets along an isomorphism -/

section IsoCloseds

variable {V W : Scheme.{0}}

/-- The image of an irreducible closed subset under an isomorphism of schemes. -/
private noncomputable def irreducibleClosedsMap (e : V ≅ W) (Z : IrreducibleCloseds V) :
    IrreducibleCloseds W :=
  ⟨e.hom.base '' Z, Z.isIrreducible.image _ e.hom.continuous.continuousOn,
    (Scheme.homeoOfIso e).isClosedMap _ Z.isClosed⟩

/-- Irreducible closed subsets correspond along an isomorphism of schemes. -/
private noncomputable def irreducibleClosedsEquivOfIso (e : V ≅ W) :
    IrreducibleCloseds V ≃ IrreducibleCloseds W where
  toFun := irreducibleClosedsMap e
  invFun := irreducibleClosedsMap e.symm
  left_inv Z := IrreducibleCloseds.ext (by
    change e.inv.base '' (e.hom.base '' Z) = Z
    rw [Set.image_image]
    exact (Set.image_congr fun x _ => Scheme.hom_inv_apply e x).trans (Set.image_id' _))
  right_inv Z := IrreducibleCloseds.ext (by
    change e.hom.base '' (e.inv.base '' Z) = Z
    rw [Set.image_image]
    exact (Set.image_congr fun x _ => Scheme.inv_hom_apply e x).trans (Set.image_id' _))

private theorem coe_irreducibleClosedsEquivOfIso (e : V ≅ W) (Z : IrreducibleCloseds V) :
    (irreducibleClosedsEquivOfIso e Z : Set W) = e.hom.base '' Z := rfl

/-- An isomorphism preserves the codimension of an irreducible closed subset. -/
private theorem codimension_of_coe_eq_image (e : V ≅ W) {Z : IrreducibleCloseds V}
    {Z' : IrreducibleCloseds W} (h : (Z' : Set W) = e.hom.base '' Z) :
    codimension Z' = codimension Z := by
  obtain ⟨z, hZ⟩ : ∃ z, (Z : Set V) = closure {z} :=
    ⟨_, (Z.isIrreducible.closure_genericPoint Z.isClosed).symm⟩
  have hZ' : (Z' : Set W) = closure {e.hom z} := by
    rw [h, hZ, image_closure_singleton]
  rw [codimension_eq_coheight_of_eq_closure hZ, codimension_eq_coheight_of_eq_closure hZ',
    Topology.IsOpenEmbedding.coheight_eq _ e.hom.isOpenEmbedding]

/-- The centre of a valuation transported along an isomorphism is the transported centre. -/
private theorem isCentre_comap_iff {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (e : V ≅ W)
    {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV)
    (v : Valuation V.functionField (WithZero (Multiplicative ℤ))) (Z : IrreducibleCloseds V) :
    MMP.Intersection.IsCentre ℂ sW (v.comap (functionFieldMap e.hom))
        (irreducibleClosedsEquivOfIso e Z) ↔ MMP.Intersection.IsCentre ℂ sV v Z := by
  constructor
  · intro h
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap e.symm (inv_comp_eq_of_hom_comp_eq e hs) h
    have hv : (v.comap (functionFieldMap e.hom)).comap (functionFieldMap e.symm.hom) = v :=
      comap_inv_comap_hom e v
    have hZZ : Z' = Z := IrreducibleCloseds.ext (hZ'.trans
      (congrArg (fun Z : IrreducibleCloseds V => (Z : Set V))
        ((irreducibleClosedsEquivOfIso e).left_inv Z)))
    rwa [hv, hZZ] at h'
  · intro h
    obtain ⟨Z', h', hZ'⟩ := isCentre_comap e hs h
    convert h'
    exact IrreducibleCloseds.ext hZ'.symm

/-- Centres of codimension at least three correspond along an isomorphism. -/
private theorem isDeepCentred_comap_iff {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] (e : V ≅ W)
    {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} (hs : e.hom ≫ sW = sV)
    (v : Valuation V.functionField (WithZero (Multiplicative ℤ))) :
    (∃ Z : IrreducibleCloseds W, MMP.Intersection.IsCentre ℂ sW
        (v.comap (functionFieldMap e.hom)) Z ∧ 3 ≤ codimension Z) ↔
      ∃ Z : IrreducibleCloseds V, MMP.Intersection.IsCentre ℂ sV v Z ∧ 3 ≤ codimension Z := by
  constructor
  · rintro ⟨Z, hZ, h3⟩
    obtain ⟨Z₀, rfl⟩ := (irreducibleClosedsEquivOfIso e).surjective Z
    refine ⟨Z₀, (isCentre_comap_iff e hs v Z₀).1 hZ, ?_⟩
    rwa [codimension_of_coe_eq_image e (coe_irreducibleClosedsEquivOfIso e Z₀)] at h3
  · rintro ⟨Z, hZ, h3⟩
    exact ⟨_, (isCentre_comap_iff e hs v Z).2 hZ,
      by rwa [codimension_of_coe_eq_image e (coe_irreducibleClosedsEquivOfIso e Z)]⟩

end IsoCloseds

/-! ### Weights along an isomorphism of pairs -/

/-- **Weights along an isomorphism of pairs.** Let `e : V ≅ W` be an isomorphism over `ℂ` of
normal varieties carrying a boundary `B` of `V` to a boundary `B'` of `W`. A valuation `v` of
`ℂ(V)` is exceptional over `V` with `w = w(2 - a(v; V, B))` exactly when its transport is
exceptional over `W` with `w = w(2 - a(v; W, B'))`. -/
private theorem isWeight_comap_iff {V W : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] (e : V ≅ W) {sV : V ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)}
    (hs : e.hom ≫ sW = sV) {B : MMP.Mori.QDivisor V} {B' : MMP.Mori.QDivisor W}
    (hB : ∀ Γ, B.coeff Γ = B'.coeff (primeDivisorEquivOfIso e Γ))
    (hBp : MMP.Mori.IsPair sV B) (hB'p : MMP.Mori.IsPair sW B') (N : ℕ)
    (v : Valuation V.functionField (WithZero (Multiplicative ℤ))) (n : ℕ) :
    (MMP.Intersection.IsExceptionalValuation ℂ sW (v.comap (functionFieldMap e.hom)) ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy sW B' (v.comap (functionFieldMap e.hom)) a ∧
        n = difficultyWeight N (2 - a)) ↔
    (MMP.Intersection.IsExceptionalValuation ℂ sV v ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy sV B v a ∧ n = difficultyWeight N (2 - a)) := by
  constructor
  · rintro ⟨hex, a, ha, rfl⟩
    have hs' := inv_comp_eq_of_hom_comp_eq e hs
    have hB' : ∀ Γ', B'.coeff Γ' = B.coeff (primeDivisorEquivOfIso e.symm Γ') := fun Γ' => by
      rw [hB (primeDivisorEquivOfIso e.symm Γ')]
      exact congrArg _ ((primeDivisorEquivOfIso e).right_inv Γ').symm
    have h1 := isExceptionalValuation_comap e.symm hs' hex
    have h2 := isValuationLogDiscrepancy_comap e.symm hs' hB' hBp ha
    have hv : (v.comap (functionFieldMap e.hom)).comap (functionFieldMap e.symm.hom) = v :=
      comap_inv_comap_hom e v
    rw [hv] at h1 h2
    exact ⟨h1, a, h2, rfl⟩
  · rintro ⟨hex, a, ha, rfl⟩
    exact ⟨isExceptionalValuation_comap e hs hex, a,
      isValuationLogDiscrepancy_comap e hs hB hB'p ha, rfl⟩

/-! ### Centres of exceptional valuations on a fourfold -/

section Centres

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [LocallyOfFiniteType sX]

/-- An exceptional valuation on a fourfold has a centre, of codimension at least three or a
surface. -/
private theorem exists_isCentre_of_isExceptionalValuation (hdim : topologicalKrullDim X = 4)
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (h : MMP.Intersection.IsExceptionalValuation ℂ sX v) :
    ∃ Z : IrreducibleCloseds X, MMP.Intersection.IsCentre ℂ sX v Z ∧
      (3 ≤ codimension Z ∨ topologicalKrullDim (Z : Set X) = 2) := by
  obtain ⟨D, hp, rfl, hc⟩ := h
  refine ⟨D.center, ⟨D, hp, rfl, rfl⟩, ?_⟩
  have hZz := D.center_eq_closure_genericPoint
  have hcod : codimension D.center = Order.coheight (D.f D.E.genericPoint) :=
    codimension_eq_coheight_of_eq_closure hZz
  have hsum := topologicalKrullDim_closure_add_coheight sX hdim (D.f D.E.genericPoint)
  rw [hcod] at hc ⊢
  by_cases h3 : 3 ≤ Order.coheight (D.f D.E.genericPoint)
  · exact Or.inl h3
  · refine Or.inr ?_
    rw [hZz]
    refine (eq_two_iff_of_add_eq_four hsum).2 ?_
    generalize Order.coheight (D.f D.E.genericPoint) = c at hc h3 ⊢
    induction c using ENat.recTopCoe with
    | top => exact absurd le_top h3
    | coe c =>
      norm_cast at hc h3 ⊢
      omega

end Centres

/-- A surface of a fourfold has codimension two, not at least three. -/
private theorem not_three_le_codimension {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 4)
    {Z : IrreducibleCloseds X} (hZ : topologicalKrullDim (Z : Set X) = 2) :
    ¬ 3 ≤ codimension Z := by
  have hZz : (Z : Set X) = closure {Z.isIrreducible.genericPoint} :=
    (Z.isIrreducible.closure_genericPoint Z.isClosed).symm
  have hsum := topologicalKrullDim_closure_add_coheight sX hdim Z.isIrreducible.genericPoint
  rw [← hZz, hZ] at hsum
  rw [codimension_eq_coheight_of_eq_closure hZz, (eq_two_iff_of_add_eq_four hsum).1 rfl]
  decide

open Classical in
/-- On a fourfold, a valuation centred either in codimension at least three or on a surface of
`s` contributes its weight difference `a` exactly once: to the deep part or to that surface. -/
private theorem eq_ite_add_sum_ite_isCentre {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [LocallyOfFiniteType sX] (hX : MMP.Mori.IsVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) (s : Finset (IrreducibleCloseds X))
    {v : Valuation X.functionField (WithZero (Multiplicative ℤ))}
    (hv : (∃ Z : IrreducibleCloseds X, MMP.Intersection.IsCentre ℂ sX v Z ∧ 3 ≤ codimension Z) ∨
      ∃ V ∈ s, topologicalKrullDim (V : Set X) = 2 ∧ MMP.Intersection.IsCentre ℂ sX v V)
    (a : ℤ) :
    a = (if ∃ Z : IrreducibleCloseds X, MMP.Intersection.IsCentre ℂ sX v Z ∧ 3 ≤ codimension Z
        then a else 0) +
      ∑ V ∈ s, if topologicalKrullDim (V : Set X) = 2 ∧ MMP.Intersection.IsCentre ℂ sX v V
        then a else 0 := by
  rcases hv with hp | ⟨V₀, hV₀s, hV₀2, hV₀⟩
  · rw [if_pos hp, Finset.sum_eq_zero, add_zero]
    intro V _
    rw [if_neg]
    rintro ⟨hV2, hcV⟩
    obtain ⟨Z, hZ, h3⟩ := hp
    obtain rfl := isCentre_unique hX hZ hcV
    exact not_three_le_codimension sX hdim hV2 h3
  · have hnp : ¬ ∃ Z : IrreducibleCloseds X, MMP.Intersection.IsCentre ℂ sX v Z ∧
        3 ≤ codimension Z := fun ⟨Z, hZ, h3⟩ => by
      obtain rfl := isCentre_unique hX hZ hV₀
      exact not_three_le_codimension sX hdim hV₀2 h3
    rw [if_neg hnp, zero_add, Finset.sum_eq_single V₀, if_pos ⟨hV₀2, hV₀⟩]
    · intro V _ hne
      rw [if_neg]
      rintro ⟨-, hcV⟩
      exact hne (isCentre_unique hX hcV hV₀)
    · exact fun h => absurd hV₀s h

/-! ### The decreased pair and the next model -/

section NextModel

open MMP.Mori

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-- The centre of a label on a junction `Y_i` is its centre on the first model `V_0 = Y_i` of the
`i`-th bridge. -/
private theorem isLabelCentre_some_zero {S : C.Label} {i : ℕ} (hm : 0 < (C.bridge i).P.m)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (h : C.IsLabelCentre S ⟨i, none⟩ P) :
    C.IsLabelCentre S ⟨i, some ⟨0, hm⟩⟩ P := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  obtain ⟨w, hw, hP⟩ := h
  refine ⟨w, hw, (inferInstance : IsDominant ((C.junction i).p ≫ T.f i)), ?_⟩
  change P.valuationOver ((C.junction i).p ≫ T.f i) = _
  rw [valuationOver_comp, hP]

/-- Through an identification `e : Y_i ≅ Y_{i+1}` over `Z_i`, the centre of a label on `Y_i` is
carried to its centre on `Y_{i+1}`. -/
private theorem isLabelCentre_succ_of_iso {S : C.Label} {i : ℕ}
    (e : (C.junction i).Y ≅ (C.junction (i + 1)).Y)
    (hπ : (C.junction i).p ≫ T.f i = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i)
    {P : MMP.Mori.PrimeDivisor (C.junction i).Y} (h : C.IsLabelCentre S ⟨i, none⟩ P) :
    C.IsLabelCentre S ⟨i + 1, none⟩ (primeDivisorEquivOfIso e P) := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  haveI := (C.junction (i + 1)).isBirationalMorphism.isDominant
  haveI := (T.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_minus.isDominant
  haveI := (T.isFourfoldStepDiagram i).isBirationalMorphism_plus.isDominant
  haveI : IsDominant e.hom := (isBirationalMorphism_of_isIso e.hom).isDominant
  obtain ⟨w, hw, hP⟩ := h
  refine ⟨_, ⟨w, hw, ?_⟩, rfl⟩
  change ((primeDivisorEquivOfIso e P).valuationOver (C.junction (i + 1)).p).comap
    (functionFieldMap (T.fp i)) = w.comap (functionFieldMap (T.f i))
  rw [← valuationOver_comp, ← valuationOver_iso_comp, ← hP, ← valuationOver_comp]
  exact valuationOver_congr _ (by rw [hπ])

/-- Along a bridge with no step, the decreased pair `(Y_i, Θ_i')` is the next junction
`(Y_{i+1}, Θ_{i+1})` up to the identification `e` of the end of the bridge. -/
private theorem exists_iso_succ_of_m_eq_zero (i : ℕ) (h : (C.bridge i).P.m = 0) :
    ∃ ψ : (C.junction i).Y ≅ (C.junction (i + 1)).Y,
      ψ.hom ≫ (C.junction (i + 1)).sY = (C.junction i).sY ∧
      (C.bridge i).Θ' = inverseTransformDivisor ψ.hom (C.junction (i + 1)).Θ ∧
      (C.junction i).p ≫ T.f i = ψ.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := by
  have key : ∀ (m : ℕ) (_ : m = 0) (e : (C.bridge i).P.model m ≅ (C.junction (i + 1)).Y),
      e.hom ≫ (C.junction (i + 1)).sY = (C.bridge i).P.modelStructure m →
      (C.bridge i).P.boundary m = inverseTransformDivisor e.hom (C.junction (i + 1)).Θ →
      (C.bridge i).P.toBase m = e.hom ≫ (C.junction (i + 1)).p ≫ T.fp i →
      ∃ ψ : (C.junction i).Y ≅ (C.junction (i + 1)).Y,
        ψ.hom ≫ (C.junction (i + 1)).sY = (C.junction i).sY ∧
        (C.bridge i).Θ' = inverseTransformDivisor ψ.hom (C.junction (i + 1)).Θ ∧
        (C.junction i).p ≫ T.f i = ψ.hom ≫ (C.junction (i + 1)).p ≫ T.fp i := by
    rintro m rfl e h1 h2 h3
    exact ⟨e, h1, h2, h3⟩
  exact key _ h (C.bridge i).e (C.bridge i).comp_sY (C.bridge i).endBoundary_eq
    (C.bridge i).toBase_end_eq

/-- **The decreased pair is the next model.** The model following the junction `(Y_i, Θ_i)` is
`(Y_i, Θ_i')` up to an isomorphism `ψ` over `ℂ` carrying `Θ_i'` to its boundary and the centre of
every label on `Y_i` to its centre there. -/
private theorem exists_iso_next (i : ℕ) :
    ∃ ψ : C.model ⟨i, none⟩ ≅ C.model (C.next ⟨i, none⟩),
      ψ.hom ≫ C.modelStructure (C.next ⟨i, none⟩) = C.modelStructure ⟨i, none⟩ ∧
      (∀ Γ, (C.bridge i).Θ'.coeff Γ =
        (C.modelBoundary (C.next ⟨i, none⟩)).coeff (primeDivisorEquivOfIso ψ Γ)) ∧
      ∀ (S : C.Label) (P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)),
        C.IsLabelCentre S ⟨i, none⟩ P →
          C.IsLabelCentre S (C.next ⟨i, none⟩) (primeDivisorEquivOfIso ψ P) := by
  by_cases h : 0 < (C.bridge i).P.m
  · have hn : C.next ⟨i, none⟩ = ⟨i, some ⟨0, h⟩⟩ := by
      simp only [TerminalChain.next, h, ↓reduceDIte]
    rw [hn]
    let ψ : C.model ⟨i, none⟩ ≅ C.model ⟨i, some ⟨0, h⟩⟩ := Iso.refl (C.junction i).Y
    have hid : ∀ Γ, primeDivisorEquivOfIso ψ Γ = Γ := fun Γ =>
      AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        ((genericPoint_primeDivisorEquivOfIso _ Γ).trans rfl)
    refine ⟨ψ, Category.id_comp _, fun Γ => ?_, fun S P hP => ?_⟩
    · exact congrArg (fun Γ' => (C.bridge i).Θ'.coeff Γ') (hid Γ).symm
    · rw [hid]
      exact isLabelCentre_some_zero C h hP
  · have hn : C.next ⟨i, none⟩ = ⟨i + 1, none⟩ := by
      simp only [TerminalChain.next, h, ↓reduceDIte]
    rw [hn]
    obtain ⟨ψ, h1, h2, h3⟩ := exists_iso_succ_of_m_eq_zero C i (by omega)
    refine ⟨ψ, h1, fun Γ => ?_, fun S P hP => isLabelCentre_succ_of_iso C ψ h3 hP⟩
    exact (congrArg (fun D => D.coeff Γ) h2).trans (coeff_inverseTransformDivisor_iso ψ _ Γ)

end NextModel

/-! ### The difference of the difficulties -/

section Main

open MMP.Mori

/-- **The difficulty change under a coefficient decrease**, for an identification `ψ` over `ℂ` of
the decreased pair `(Y_i, Θ_i')` with a model `x` of the prepared chain which carries `Θ_i'` to the
boundary of `x` and the label centres of `Y_i` to those of `x`. -/
private theorem exists_finset_difficulty_sub_eq_sum_of_iso {T : StabilizedSmallKltTail} (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i) (x : Q.ModelIndex) (ψ : Q.chain.model ⟨i, none⟩ ≅ Q.chain.model x.1)
    (hs : ψ.hom ≫ Q.chain.modelStructure x.1 = Q.chain.modelStructure ⟨i, none⟩)
    (hB : ∀ Γ, (Q.chain.bridge i).Θ'.coeff Γ =
      (Q.chain.modelBoundary x.1).coeff (primeDivisorEquivOfIso ψ Γ))
    (hc : ∀ (S : Q.chain.Label) P, Q.chain.IsLabelCentre S ⟨i, none⟩ P →
      Q.chain.IsLabelCentre S x.1 (primeDivisorEquivOfIso ψ P)) :
    ∃ F : Finset (Valuation (Q.chain.model ⟨i, none⟩).functionField
        (WithZero (Multiplicative ℤ))),
      (∀ v ∈ F, MMP.Intersection.IsExceptionalValuation ℂ
        (Q.chain.modelStructure ⟨i, none⟩) v) ∧
      (∀ v, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v →
        v ∉ F → ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
          Q.chain.IsValuationWeight Q.scale x.1 (v.comap (functionFieldMap ψ.hom)) w' →
            w = w') ∧
      ∀ (D D' : ℤ), Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D → Q.IsDifficulty x D' →
        ∀ w w' : Valuation (Q.chain.model ⟨i, none⟩).functionField
            (WithZero (Multiplicative ℤ)) → ℕ,
          (∀ v ∈ F, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)) →
          (∀ v ∈ F, Q.chain.IsValuationWeight Q.scale x.1
            (v.comap (functionFieldMap ψ.hom)) (w' v)) →
          D - D' = ∑ v ∈ F, ((w v : ℤ) - w' v) := by
  classical
  haveI : Finite Q.chain.Label := Q.chain.finite_label
  letI : Fintype Q.chain.Label := Fintype.ofFinite _
  have hN := Q.isAdmissibleScale.pos
  set y : Q.ModelIndex := ⟨⟨i, none⟩, hi⟩ with hy
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ)) →
      Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)),
      ∀ v, Φ v = v.comap (functionFieldMap ψ.hom) := ⟨_, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Valuation (Q.chain.model x.1).functionField
      (WithZero (Multiplicative ℤ)) →
      Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)),
      ∀ v', Ψ v' = v'.comap (functionFieldMap ψ.inv) := ⟨_, fun _ => rfl⟩
  have hΨΦ : ∀ v, Ψ (Φ v) = v := fun v => by rw [hΨ, hΦ]; exact comap_inv_comap_hom ψ v
  have hΦΨ : ∀ v', Φ (Ψ v') = v' := fun v' => by
    rw [hΦ, hΨ]; exact comap_inv_comap_hom ψ.symm v'
  have hΦinj : Function.Injective Φ := fun a b h => by rw [← hΨΦ a, h, hΨΦ]
  obtain ⟨hΘY, hQY, hprojY, hdimY⟩ :=
    TerminalChain.isKltTerminalPair_modelBoundary Q.chain ⟨i, none⟩
  obtain ⟨hΘM, -, -, -⟩ := TerminalChain.isKltTerminalPair_modelBoundary Q.chain x.1
  have hnvY : IsNormalVariety ℂ (Q.chain.modelStructure ⟨i, none⟩) := hΘY.1.1.isPair.1
  have hvarY := hnvY.1
  haveI : LocallyOfFiniteType (Q.chain.modelStructure ⟨i, none⟩) := hnvY.1.toLocallyOfFiniteType
  have hΘ'kt : IsKltTerminalPair (Q.chain.modelStructure ⟨i, none⟩) (Q.chain.bridge i).Θ' :=
    IsDecreasedBoundary.isKltTerminalPair (Q.chain.coe_I i) (Q.chain.bridge i).isDecreasedBoundary
  have hwt : ∀ v n, Q.chain.IsValuationWeight Q.scale x.1 (Φ v) n ↔
      (MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
        ∃ a : ℝ, IsValuationLogDiscrepancy (Q.chain.modelStructure ⟨i, none⟩)
          (Q.chain.bridge i).Θ' v a ∧ n = difficultyWeight Q.scale (2 - a)) := fun v n => by
    rw [hΦ]
    exact isWeight_comap_iff ψ hs hB hΘ'kt.1.1.isPair hΘM.1.1.isPair Q.scale v n
  have hdeep : ∀ v, Side.IsDeepCentred Q x (Φ v) ↔ Side.IsDeepCentred Q y v := fun v => by
    rw [hΦ]
    exact isDeepCentred_comap_iff ψ hs v
  set SE := irreducibleClosedsEquivOfIso ψ with hSE
  have hcen : ∀ v V, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) (Φ v) (SE V) ↔
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v V := fun v V => by
    rw [hΦ]
    exact isCentre_comap_iff ψ hs v V
  have hdimSE : ∀ V, topologicalKrullDim (SE V : Set (Q.chain.model x.1)) =
      topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) := fun V =>
    (((Scheme.homeoOfIso ψ).image V).isHomeomorph.topologicalKrullDim_eq).symm
  obtain ⟨E, hEfin, hE⟩ := Q.exists_finite_forall_isValuationWeight_iff_decreasedBoundary i hi
  obtain ⟨F, hF⟩ : ∃ F : Set (Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))), ∀ v, v ∈ F ↔
        MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
          (Side.IsDeepCentred Q y v ∨ ∃ V ∈ E,
            topologicalKrullDim (V : Set (Q.chain.junction i).Y) = 2 ∧
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v V) ∧
          ((∃ n, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v n ∧ n ≠ 0) ∨
            ∃ n, Q.chain.IsValuationWeight Q.scale x.1 (Φ v) n ∧ n ≠ 0) :=
    ⟨_, fun _ => Iff.rfl⟩
  have hfin1 := IsKltTerminalPair.finite_setOf_three_le_codimension_centre hprojY hQY hdimY hΘY
    (L := (Q.chain.modelBoundary ⟨i, none⟩).support) subset_rfl
  have hfin2 := IsKltTerminalPair.finite_setOf_three_le_codimension_centre hprojY hQY hdimY hΘ'kt
    (L := (Q.chain.bridge i).Θ'.support) subset_rfl
  have hfin3 := fun V hV =>
    IsKltTerminalPair.finite_setOf_isCentre_of_hasLogDiscrepancy_lt_two hprojY hQY hdimY hΘY
      (L := (Q.chain.modelBoundary ⟨i, none⟩).support) subset_rfl V hV
  have hfin4 := fun V hV =>
    IsKltTerminalPair.finite_setOf_isCentre_of_hasLogDiscrepancy_lt_two hprojY hQY hdimY hΘ'kt
      (L := (Q.chain.bridge i).Θ'.support) subset_rfl V hV
  have hFfin : F.Finite := by
    refine ((hfin1.union hfin2).union ((hEfin.inter_of_left
      {V | topologicalKrullDim (V : Set (Q.chain.junction i).Y) = 2}).biUnion
        fun V hV => (hfin3 V hV.2).union (hfin4 V hV.2))).subset ?_
    intro v hv
    obtain ⟨hex, hcent, hw⟩ := (hF v).1 hv
    have ha : (∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy (Q.chain.modelStructure ⟨i, none⟩)
          (Q.chain.modelBoundary ⟨i, none⟩) v a) ∨
        ∃ a : ℝ, a < 2 ∧ HasLogDiscrepancy (Q.chain.modelStructure ⟨i, none⟩)
          (Q.chain.bridge i).Θ' v a := by
      rcases hw with ⟨n, ⟨-, a, ha, rfl⟩, hn⟩ | ⟨n, hn', hn⟩
      · exact Or.inl ⟨a, lt_two_of_difficultyWeight_ne_zero hN hn,
          Bracket.IsValuationLogDiscrepancy.hasLogDiscrepancy ha⟩
      · obtain ⟨-, a, ha, rfl⟩ := (hwt v n).1 hn'
        exact Or.inr ⟨a, lt_two_of_difficultyWeight_ne_zero hN hn,
          Bracket.IsValuationLogDiscrepancy.hasLogDiscrepancy ha⟩
    rcases hcent with hd | ⟨V, hVE, hV2, hVc⟩
    · rcases ha with ha | ha
      · exact Or.inl (Or.inl ⟨hex, ha, hd⟩)
      · exact Or.inl (Or.inr ⟨hex, ha, hd⟩)
    · refine Or.inr (Set.mem_biUnion (x := V) ⟨hVE, hV2⟩ ?_)
      rcases ha with ⟨a, ha2, ha⟩ | ⟨a, ha2, ha⟩
      · exact Or.inl ⟨hex, hVc, a, ha2, ha⟩
      · exact Or.inr ⟨hex, hVc, a, ha2, ha⟩
  set 𝔉 := hFfin.toFinset with h𝔉
  have hmem𝔉 : ∀ {v}, v ∈ 𝔉 ↔ v ∈ F := fun {v} => hFfin.mem_toFinset
  refine ⟨𝔉, fun v hv => ((hF v).1 (hmem𝔉.1 hv)).1, ?_, ?_⟩
  · -- weights outside `F` are unchanged
    intro v hex hvF w w' hw hw'
    rw [← hΦ v] at hw'
    have hvF' : v ∉ F := fun h => hvF (hmem𝔉.2 h)
    obtain ⟨Z, hZ, h3 | h2⟩ := exists_isCentre_of_isExceptionalValuation hdimY hex
    · by_contra hne
      apply hvF'
      refine (hF v).2 ⟨hex, Or.inl ⟨Z, hZ, h3⟩, ?_⟩
      by_cases hw0 : w = 0
      · exact Or.inr ⟨w', hw', by omega⟩
      · exact Or.inl ⟨w, hw, hw0⟩
    · by_cases hZE : Z ∈ E
      · by_contra hne
        apply hvF'
        refine (hF v).2 ⟨hex, Or.inr ⟨Z, hZE, h2, hZ⟩, ?_⟩
        by_cases hw0 : w = 0
        · exact Or.inr ⟨w', hw', by omega⟩
        · exact Or.inl ⟨w, hw, hw0⟩
      · exact isValuationWeight_unique hw ((hE Z hZE h2 v hZ w').2 ((hwt v w').1 hw'))
  · intro D D' hD hD' w w' hw hw'
    have hw₀ : ∀ v ∈ F, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v) :=
      fun v hv => hw v (hmem𝔉.2 hv)
    have hw'' : ∀ v ∈ F, Q.chain.IsValuationWeight Q.scale x.1 (Φ v) (w' v) :=
      fun v hv => by rw [hΦ]; exact hw' v (hmem𝔉.2 hv)
    obtain ⟨wD, β, d, ρ, hwD, hβ, hd, hρ, rfl⟩ := hD
    obtain ⟨wD', β', d', ρ', hwD', hβ', hd', hρ', rfl⟩ := hD'
    choose c hcc using fun S => exists_isLabelCentre Q.chain S ⟨i, none⟩
    choose d₀ hd₀ using Q.isLabelDefault_const
    have hdx : ∀ S, d S = d₀ S := fun S => isLabelDefault_unique (hd S) (hd₀ S _ hi)
    have hdy : ∀ S, d' S = d₀ S := fun S => isLabelDefault_unique (hd' S) (hd₀ S _ x.2)
    have hlab : ((∑ᶠ S, d S * ρ S : ℕ) : ℤ) = ((∑ᶠ S, d' S * ρ' S : ℕ) : ℤ) := by
      congr 1
      refine finsum_congr fun S => ?_
      rw [hdx S, hdy S]
      congr 1
      rcases hρ S with ⟨P, hP, hcx, hρP⟩ | ⟨hn, -⟩
      swap
      · exact absurd (hcc S) (hn _)
      rcases hρ' S with ⟨P', hP', hcx', hρP'⟩ | ⟨hn', -⟩
      swap
      · exact absurd (hc S _ (hcc S)) (hn' _)
      obtain rfl := isLabelCentre_unique hP' (hc S P hP)
      rw [hρP, hρP']
      obtain ⟨E', hE'⟩ := exists_iso_primeDivisorNormalizationScheme ψ P
      letI := primeDivisorNormalizationOver (Q.chain.modelStructure ⟨i, none⟩) P
      letI := primeDivisorNormalizationOver (Q.chain.modelStructure x.1)
        (primeDivisorEquivOfIso ψ P)
      exact (MMP.Analytic.cycleRank_eq_of_iso E' (by
        change E'.hom ≫ (primeDivisorNormalization _ ≫ _) = primeDivisorNormalization P ≫ _
        rw [← Category.assoc, hE', Category.assoc, hs])).2.2.2 2
    have hdeepsum : ((∑ᶠ (v) (_ : Side.IsDeepCentred Q y v), wD v : ℕ) : ℤ) -
        ((∑ᶠ (v') (_ : Side.IsDeepCentred Q x v'), wD' v' : ℕ) : ℤ) =
        ∑ v ∈ 𝔉, if Side.IsDeepCentred Q y v then ((w v : ℤ) - w' v) else 0 :=
      natCast_finsum_sub_finsum_eq_sum hΦinj hΦΨ hdeep 𝔉
        (fun v hv hne => hmem𝔉.2 ((hF v).2 ⟨(hwD v hv).1, Or.inl hv, Or.inl ⟨wD v, hwD v hv, hne⟩⟩))
        (fun v' hv' hne => by
          have hv'w : Q.chain.IsValuationWeight Q.scale x.1 (Φ (Ψ v')) (wD' v') := by
            rw [hΦΨ]; exact hwD' v' hv'
          exact hmem𝔉.2 ((hF _).2 ⟨((hwt _ _).1 hv'w).1,
            Or.inl ((hdeep _).1 (by rw [hΦΨ]; exact hv')), Or.inr ⟨_, hv'w, hne⟩⟩))
        (fun v hv hp => isValuationWeight_unique (hwD v hp) (hw₀ v (hmem𝔉.1 hv)))
        (fun v hv hp => isValuationWeight_unique (hwD' _ ((hdeep v).2 hp)) (hw'' v (hmem𝔉.1 hv)))
    have hbr : (∑ᶠ (V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩))
          (_ : topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2), β V) -
        (∑ᶠ (V' : IrreducibleCloseds (Q.chain.model x.1))
          (_ : topologicalKrullDim (V' : Set (Q.chain.model x.1)) = 2), β' V') =
        ∑ V ∈ hEfin.toFinset, ∑ v ∈ 𝔉,
          if topologicalKrullDim (V : Set (Q.chain.junction i).Y) = 2 ∧
            MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v V
          then ((w v : ℤ) - w' v) else 0 := by
      have hkey : ∀ V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          ((if topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 then β V else 0) -
            if topologicalKrullDim (SE V : Set (Q.chain.model x.1)) = 2 then β' (SE V) else 0) =
          if V ∈ E then ∑ v ∈ 𝔉,
            (if topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 ∧
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v V
            then ((w v : ℤ) - w' v) else 0) else 0 := by
        intro V
        rw [hdimSE V]
        by_cases hV2 : topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2
        swap
        · rw [if_neg hV2, if_neg hV2, sub_zero]
          split_ifs
          · exact (Finset.sum_eq_zero fun v _ => if_neg fun h => hV2 h.1).symm
          · rfl
        rw [if_pos hV2, if_pos hV2]
        have hV2' : topologicalKrullDim (SE V : Set (Q.chain.model x.1)) = 2 :=
          (hdimSE V).trans hV2
        obtain ⟨wβ, r, dβ, hwβ, hr, hdβ, hβeq⟩ := hβ V hV2
        obtain ⟨wβ', r', dβ', hwβ', hr', hdβ', hβeq'⟩ := hβ' (SE V) hV2'
        have hrd : (∑ᶠ S, r S * dβ S : ℕ) = ∑ᶠ S, r' S * dβ' S := by
          refine finsum_congr fun S => ?_
          rw [isLabelDefault_unique (hdβ S) (hd₀ S _ hi),
            isLabelDefault_unique (hdβ' S) (hd₀ S _ x.2)]
          congr 1
          have hrS : r S = branchNumber (c S) (V : Set (Q.chain.model ⟨i, none⟩)) := by
            rcases hr S with ⟨P, hP, hrP⟩ | ⟨hn, -⟩
            · rw [hrP, isLabelCentre_unique hP (hcc S)]
            · exact absurd (hcc S) (hn _)
          have hrS' : r' S = branchNumber (primeDivisorEquivOfIso ψ (c S))
              (SE V : Set (Q.chain.model x.1)) := by
            rcases hr' S with ⟨P, hP, hrP⟩ | ⟨hn, -⟩
            · rw [hrP, isLabelCentre_unique hP (hc S _ (hcc S))]
            · exact absurd (hc S _ (hcc S)) (hn _)
          rw [hrS, hrS', coe_irreducibleClosedsEquivOfIso, branchNumber_primeDivisorEquivOfIso]
        rw [hβeq, hβeq', hrd, sub_sub_sub_cancel_right]
        split_ifs with hVE
        · refine (natCast_finsum_sub_finsum_eq_sum (f := wβ) (f' := wβ') hΦinj hΦΨ
            (fun v => hcen v V) 𝔉 ?_ ?_ ?_ ?_).trans
            (Finset.sum_congr rfl fun v _ => if_congr (and_iff_right hV2).symm rfl rfl)
          · intro v hv hne
            exact hmem𝔉.2 ((hF v).2 ⟨(hwβ v hv).1, Or.inr ⟨V, hVE, hV2, hv⟩,
              Or.inl ⟨wβ v, hwβ v hv, hne⟩⟩)
          · intro v' hv' hne
            have hv'w : Q.chain.IsValuationWeight Q.scale x.1 (Φ (Ψ v')) (wβ' v') := by
              rw [hΦΨ]
              exact hwβ' v' hv'
            exact hmem𝔉.2 ((hF _).2 ⟨((hwt _ _).1 hv'w).1,
              Or.inr ⟨V, hVE, hV2, (hcen _ V).1 (by rwa [hΦΨ])⟩,
              Or.inr ⟨_, hv'w, hne⟩⟩)
          · exact fun v hv hcv => isValuationWeight_unique (hwβ v hcv) (hw₀ v (hmem𝔉.1 hv))
          · exact fun v hv hcv =>
              isValuationWeight_unique (hwβ' _ ((hcen v V).2 hcv)) (hw'' v (hmem𝔉.1 hv))
        · rw [finsum_eq_finsum_comp_of_injective (f := wβ')
            (P := fun v' => MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v' (SE V))
            (R := fun v => MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v V)
            hΦinj ?_, sub_eq_zero]
          · congr 1
            refine finsum_congr fun v => finsum_congr fun hv => ?_
            have h1 := (hwt v _).1 (hwβ' (Φ v) ((hcen v V).2 hv))
            exact isValuationWeight_unique (hwβ v hv) ((hE V hVE hV2 v hv _).2 h1)
          · intro v'
            constructor
            · intro h'
              exact ⟨Ψ v', (hcen _ V).1 (by rwa [hΦΨ]), hΦΨ v'⟩
            · rintro ⟨v, hv, rfl⟩
              exact (hcen v V).2 hv
      have hfinY := Side.finite_support_ite_isSurfaceBracket (x := y) hβ
      have hfinM : (Function.support fun V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) =>
          if topologicalKrullDim (SE V : Set (Q.chain.model x.1)) = 2 then β' (SE V)
          else 0).Finite :=
        (Side.finite_support_ite_isSurfaceBracket hβ').preimage SE.injective.injOn
      calc _ = (∑ᶠ V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
              if topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 then β V else 0) -
            ∑ᶠ V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
              if topologicalKrullDim (SE V : Set (Q.chain.model x.1)) = 2 then β' (SE V)
              else 0 := by
            congr 1
            · exact finsum_congr fun V => finsum_eq_if
            · rw [finsum_comp_equiv SE (f := fun V' =>
                if topologicalKrullDim (V' : Set (Q.chain.model x.1)) = 2 then β' V' else 0)]
              exact finsum_congr fun V' => finsum_eq_if
        _ = ∑ᶠ V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
              ((if topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 then β V
                else 0) -
              if topologicalKrullDim (SE V : Set (Q.chain.model x.1)) = 2 then β' (SE V)
              else 0) := (finsum_sub_distrib hfinY hfinM).symm
        _ = _ := by
            refine Eq.trans (finsum_eq_sum_of_support_subset _ (s := hEfin.toFinset) ?_)
              (Finset.sum_congr rfl fun V hV => ?_)
            · intro V hV
              rw [hEfin.coe_toFinset]
              by_contra hVE
              exact hV ((hkey V).trans (if_neg hVE))
            · exact (hkey V).trans (if_pos (hEfin.mem_toFinset.1 hV))
    have hdec : ∀ v ∈ 𝔉, ((w v : ℤ) - w' v) =
        (if Side.IsDeepCentred Q y v then ((w v : ℤ) - w' v) else 0) +
          ∑ V ∈ hEfin.toFinset,
            if topologicalKrullDim (V : Set (Q.chain.junction i).Y) = 2 ∧
              MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v V
            then ((w v : ℤ) - w' v) else 0 := by
      intro v hv
      obtain ⟨-, hcent, -⟩ := (hF v).1 (hmem𝔉.1 hv)
      refine eq_ite_add_sum_ite_isCentre hvarY hdimY _ ?_ _
      rcases hcent with hp | ⟨V, hVE, hV2, hV⟩
      · exact Or.inl hp
      · exact Or.inr ⟨V, hEfin.mem_toFinset.2 hVE, hV2, hV⟩
    rw [Finset.sum_congr rfl hdec, Finset.sum_add_distrib, Finset.sum_comm (s := 𝔉)]
    linear_combination hdeepsum + hbr + hlab

end Main

end MMP.Fourfold.CoefficientDecrease

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

open MMP.Fourfold.CoefficientDecrease MMP.Mori in
/-- On a prepared chain, let `(Y_i, Θ_i) ⇝ (Y', Θ')` be the coefficient-decrease move of the
`i`-th bridge, `i ≥ i₀`, from the junction to the next model `Q.chain.next ⟨i, none⟩`, and let
`φ : Y_i ≅ Y'` be an isomorphism over `ℂ` carrying the decreased boundary `Θ_i'` to `Θ'`. There
is a finite set `F` of normalized divisorial valuations of `ℂ(Y_i)` exceptional over `Y_i` such
that every exceptional `v ∉ F` has `w_v(Y_i, Θ_i) = w_{φ_* v}(Y', Θ')`, and
`𝒟(Y_i, Θ_i) - 𝒟(Y', Θ') = ∑_{v ∈ F} (w_v(Y_i, Θ_i) - w_{φ_* v}(Y', Θ'))`. -/
@[mmp "lem_oai4_c3_coefficient_move_difference"]
public theorem exists_finset_difficulty_sub_eq_sum {i : ℕ} (hi : Q.start ≤ i)
    (φ : Q.chain.model ⟨i, none⟩ ≅ Q.chain.model (Q.chain.next ⟨i, none⟩))
    (hφ : φ.hom ≫ Q.chain.modelStructure (Q.chain.next ⟨i, none⟩) =
      Q.chain.modelStructure ⟨i, none⟩)
    (hΘ : (Q.chain.bridge i).Θ' =
      MMP.Mori.inverseTransformDivisor φ.hom (Q.chain.modelBoundary (Q.chain.next ⟨i, none⟩)))
    (hx : Q.start ≤ (Q.chain.next ⟨i, none⟩).1) :
    ∃ F : Finset (Valuation (Q.chain.model ⟨i, none⟩).functionField
        (WithZero (Multiplicative ℤ))),
      (∀ v ∈ F, MMP.Intersection.IsExceptionalValuation ℂ
        (Q.chain.modelStructure ⟨i, none⟩) v) ∧
      (∀ v, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v →
        v ∉ F → ∀ w w' : ℕ, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v w →
          Q.chain.IsValuationWeight Q.scale (Q.chain.next ⟨i, none⟩)
            (v.comap (functionFieldMap φ.hom)) w' → w = w') ∧
      ∀ (D D' : ℤ), Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D →
        Q.IsDifficulty ⟨Q.chain.next ⟨i, none⟩, hx⟩ D' →
        ∀ w w' : Valuation (Q.chain.model ⟨i, none⟩).functionField
            (WithZero (Multiplicative ℤ)) → ℕ,
          (∀ v ∈ F, Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)) →
          (∀ v ∈ F, Q.chain.IsValuationWeight Q.scale (Q.chain.next ⟨i, none⟩)
            (v.comap (functionFieldMap φ.hom)) (w' v)) →
          D - D' = ∑ v ∈ F, ((w v : ℤ) - w' v) := by
  obtain ⟨ψ, hs, hB, hc⟩ := exists_iso_next Q.chain i
  obtain ⟨F, hFex, hFeq, hFsum⟩ := exists_finset_difficulty_sub_eq_sum_of_iso Q hi ⟨_, hx⟩ ψ hs hB hc
  have hBφ : ∀ Γ, (Q.chain.bridge i).Θ'.coeff Γ =
      (Q.chain.modelBoundary (Q.chain.next ⟨i, none⟩)).coeff (primeDivisorEquivOfIso φ Γ) :=
    fun Γ => (congrArg (fun D => D.coeff Γ) hΘ).trans (coeff_inverseTransformDivisor_iso φ _ Γ)
  have hpair : MMP.Mori.IsPair (Q.chain.modelStructure ⟨i, none⟩) (Q.chain.bridge i).Θ' :=
    (IsDecreasedBoundary.isKltTerminalPair (Q.chain.coe_I i)
      (Q.chain.bridge i).isDecreasedBoundary).1.1.isPair
  have hpairM := (TerminalChain.isKltTerminalPair_modelBoundary Q.chain
    (Q.chain.next ⟨i, none⟩)).1.1.1.isPair
  have hiff : ∀ (v : Valuation (Q.chain.model ⟨i, none⟩).functionField
      (WithZero (Multiplicative ℤ))) (n : ℕ),
      Q.chain.IsValuationWeight Q.scale (Q.chain.next ⟨i, none⟩)
      (v.comap (functionFieldMap φ.hom)) n ↔ Q.chain.IsValuationWeight Q.scale
        (Q.chain.next ⟨i, none⟩) (v.comap (functionFieldMap ψ.hom)) n := fun v n =>
    (isWeight_comap_iff φ hφ hBφ hpair hpairM Q.scale v n).trans
      (isWeight_comap_iff ψ hs hB hpair hpairM Q.scale v n).symm
  exact ⟨F, hFex, fun v hex hvF w w' hw hw' => hFeq v hex hvF w w' hw ((hiff v w').1 hw'),
    fun D D' hD hD' w w' hw hw' => hFsum D D' hD hD' w w' hw fun v hv => (hiff v _).1 (hw' v hv)⟩

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
