module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BadSurface
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PreparedChainTerminal
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChain.FirstDefaultError
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChain.MultiplicitySumBound
import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BranchMultiplicity
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.Singularities.Snc.LocalEquations

/-!
# The local ceiling error at a surface

Let `(Y, Θ)`, `Θ = ∑_h b_h S_h`, be a model of a prepared chain of fourfolds at the admissible
scale `N` and let `V ⊆ Y` be an irreducible surface. Write `w_v` for the weight of a normalized
divisorial valuation `v` exceptional over `Y`, `r_{V,h}` for the branch number of the label `S_h`
at `V`, `d_h` for its default echo weight and `r_V^var` for the varying branch number at `V`.
Then
`∑_{c_Y(v) = V} w_v - ∑_h r_{V,h} d_h ≥ -max{r_V^var - 1, 0}`,
with no simple normal crossings assumption on `Θ` at the generic point `η_V`. The left-hand side
is the bracket `β_V(Y, Θ)` of
`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsSurfaceBracket`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.neg_max_le_finsum_valuationWeight_sub`:
  the inequality above.

## Implementation notes

The weights, branch numbers, default echo weights and the varying branch number are given as
values satisfying the predicates
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight` (for the valuations with
centre `V`, `MMP.Intersection.IsCentre`),
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelBranchNumber`,
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelDefault` and
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsVaryingBranchNumber`, in the spelling of
`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsSurfaceBracket`. The first sum is the
finitely supported sum `∑ᶠ`; its support is finite at a surface, so it is the sum of the source.
The inequality is stated in `ℤ`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_oai4_ceiling_error

/-! ### Centres of labels -/

/-- On every model of a terminal chain the centre relation of the labels is the graph of the
injection `S ↦ e S` for an equivalence `e` of prime divisors. -/
private theorem exists_equiv_isLabelCentre_iff {T : StabilizedSmallKltTail}
    (C : TerminalChain T) (x : C.ModelIndex) :
    ∃ e : MMP.Mori.PrimeDivisor (C.junction 0).Y ≃ MMP.Mori.PrimeDivisor (C.model x),
      ∀ (S : C.Label) (P : MMP.Mori.PrimeDivisor (C.model x)),
        C.IsLabelCentre S x P ↔ e S.1 = P := by
  have he := TerminalChain.isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C x
  rcases x with ⟨i, _ | k⟩ <;> exact ⟨_, fun S P => he S.1 P⟩

/-! ### Arithmetic of weights and defaults -/

/-- For `b < 1` the default splits as `d(b) = w(b) + ∑_{2 ≤ j < K} w(1 - j(1 - b))` with
`K = ⌈(1 - b)⁻¹⌉₊ + 1`. -/
private theorem defaultWeight_eq_add_sum_Ico (N : ℕ) {b : ℝ} (hb : b < 1) :
    defaultWeight N b = difficultyWeight N b +
      ∑ j ∈ Finset.Ico 2 (⌈(1 - b)⁻¹⌉₊ + 1), difficultyWeight N (1 - j * (1 - b)) := by
  have hK : 1 < ⌈(1 - b)⁻¹⌉₊ + 1 := by
    have : 0 < ⌈(1 - b)⁻¹⌉₊ := Nat.ceil_pos.mpr (inv_pos.mpr (sub_pos.mpr hb))
    omega
  have h : defaultWeight N b = ∑ j ∈ Finset.Ico 1 (⌈(1 - b)⁻¹⌉₊ + 1),
      difficultyWeight N (1 - j * (1 - b)) :=
    finsum_mem_eq_sum_of_subset (s := Set.Ici 1) _
      (fun j hj => Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨hj.1, Nat.lt_succ_of_le
        (Nat.lt_ceil.mpr (lt_inv_of_difficultyWeight_ne_zero hb hj.2)).le⟩))
      (fun _ hj => (Finset.mem_Ico.mp hj).1)
  rw [h, Finset.sum_eq_sum_Ico_succ_bot hK, Nat.cast_one, one_mul, sub_sub_cancel]

/-- For `b ≤ 1/2` the higher terms `w(1 - j(1 - b))`, `j ≥ 2`, of the default vanish. -/
private theorem sum_Ico_two_eq_zero (N : ℕ) {b : ℝ} (hb : b ≤ 1 / 2) (K : ℕ) :
    ∑ j ∈ Finset.Ico 2 K, difficultyWeight N (1 - j * (1 - b)) = 0 :=
  Finset.sum_eq_zero fun j hj => difficultyWeight_of_nonpos <| by
    have : (2 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Ico.mp hj).1
    nlinarith

/-- If `∑_{i ∈ s} m_i b_i < 1` with `b_i ≥ 0` and `r_i ≤ m_i`, then an index `i₀ ∈ s` with
`r_{i₀} ≥ 1` and `b_{i₀} > 1/2` has `m_{i₀} = r_{i₀} = 1`, and every other index of `s` with
`r_i ≥ 1` has `b_i ≤ 1/2`. -/
private theorem eq_one_and_forall_le_half {ι : Type*} {s : Finset ι} {m r : ι → ℕ} {b : ι → ℝ}
    (hb : ∀ i ∈ s, 0 ≤ b i) (hlt : ∑ i ∈ s, (m i : ℝ) * b i < 1) (hrm : ∀ i ∈ s, r i ≤ m i)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hr₀ : 1 ≤ r i₀) (hb₀ : 1 / 2 < b i₀) :
    m i₀ = 1 ∧ r i₀ = 1 ∧ ∀ i ∈ s, i ≠ i₀ → 1 ≤ r i → b i ≤ 1 / 2 := by
  classical
  have hnn : ∀ i ∈ s, 0 ≤ (m i : ℝ) * b i := fun i hi =>
    mul_nonneg (Nat.cast_nonneg _) (hb i hi)
  have hm₀ : m i₀ = 1 := by
    have h1 := Finset.single_le_sum hnn hi₀
    by_contra h
    have h2 : (2 : ℝ) ≤ m i₀ := by
      exact_mod_cast (show 2 ≤ m i₀ by have := hrm i₀ hi₀; omega)
    nlinarith [mul_le_mul_of_nonneg_right h2 (hb i₀ hi₀)]
  refine ⟨hm₀, le_antisymm (hm₀ ▸ hrm i₀ hi₀) hr₀, fun i hi hne hri => ?_⟩
  by_contra h
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hi₀⟩)
    (fun j hj _ => hnn j hj)
  rw [Finset.sum_pair hne, hm₀, Nat.cast_one, one_mul] at h2
  have h3 : (1 : ℝ) ≤ m i := by exact_mod_cast hri.trans (hrm i hi)
  nlinarith [mul_le_mul_of_nonneg_right h3 (hb i hi), not_le.mp h]

/-- A finite sum of a weight along an injective family of points satisfying `p` is at most the
finitely supported sum of the weight over all points satisfying `p`. -/
private theorem sum_le_finsum_of_injOn {α : Type*} {p : α → Prop} {w : α → ℕ}
    (hfin : {a | p a ∧ w a ≠ 0}.Finite) {v : ℕ → α} {s : Finset ℕ} (hinj : Set.InjOn v s)
    (hp : ∀ j ∈ s, p (v j)) : ∑ j ∈ s, w (v j) ≤ ∑ᶠ (a) (_ : p a), w a := by
  classical
  have hfin' : ({a | p a} ∩ Function.support w).Finite := hfin
  rw [show (∑ᶠ (a) (_ : p a), w a) = ∑ᶠ (a) (_ : a ∈ {a | p a}), w a from rfl,
    finsum_mem_eq_sum w hfin', ← Finset.sum_image fun a ha b hb h => hinj ha hb h,
    ← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset fun a ha => ?_
  obtain ⟨ha, hw⟩ := Finset.mem_filter.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  exact hfin'.mem_toFinset.mpr ⟨hp j hj, hw⟩

/-! ### Local algebra in a two-dimensional regular local ring -/

/-- An element of `𝔪` whose `𝔪`-adic order is one lies in `𝔪 ∖ 𝔪²`. -/
private theorem mem_maximalIdeal_and_notMem_sq_of_iSup_eq_one {R : Type*} [CommRing R]
    [IsLocalRing R] {g : R} (h : ⨆ (n : ℕ) (_ : g ∈ maximalIdeal R ^ n), (n : ℕ∞) = 1) :
    g ∈ maximalIdeal R ∧ g ∉ maximalIdeal R ^ 2 := by
  refine ⟨?_, fun hg => ?_⟩
  · by_contra hg
    have : ⨆ (n : ℕ) (_ : g ∈ maximalIdeal R ^ n), (n : ℕ∞) ≤ 0 := iSup₂_le fun n hn => by
      rcases n with _ | n
      · simp
      · exact absurd (Ideal.pow_le_self (Nat.succ_ne_zero n) hn) hg
    rw [h] at this
    exact absurd this (by norm_num)
  · have : (2 : ℕ∞) ≤ ⨆ (n : ℕ) (_ : g ∈ maximalIdeal R ^ n), (n : ℕ∞) :=
      le_iSup₂_of_le (f := fun (n : ℕ) (_ : g ∈ maximalIdeal R ^ n) => (n : ℕ∞)) 2 hg le_rfl
    rw [h] at this
    exact absurd this (by norm_num)

/-- In a local ring with regular system of parameters `(a, b)`, an element `x ∈ 𝔪 ∖ 𝔪²` is the
first member of a regular system of parameters `(x, t)`. -/
private theorem exists_isRegularSystemOfParameters_pair {R : Type*} [CommRing R] [IsLocalRing R]
    {a b x : R} (hab : IsRegularSystemOfParameters ![a, b]) (hxm : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) : ∃ t : R, IsRegularSystemOfParameters ![x, t] := by
  have hrange : ∀ p q : R, Set.range ![p, q] = {p, q} := fun p q => by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]
  obtain ⟨hspan, hdim⟩ := hab
  rw [hrange] at hspan
  have ha : a ∈ maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hb : b ∈ maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  obtain ⟨c₀, c₁, hx⟩ := Ideal.mem_span_pair.mp (hspan ▸ hxm : x ∈ Ideal.span {a, b})
  have hunit : IsUnit c₀ ∨ IsUnit c₁ := by
    by_contra h
    rw [not_or] at h
    apply hx2
    rw [← hx, pow_two]
    exact add_mem (Ideal.mul_mem_mul ((mem_maximalIdeal _).2 h.1) ha)
      (Ideal.mul_mem_mul ((mem_maximalIdeal _).2 h.2) hb)
  have key : ∀ p q c d : R, Ideal.span {p, q} = maximalIdeal R → c * p + d * q = x →
      IsUnit c → Ideal.span {x, q} = maximalIdeal R := by
    intro p q c d hpq hx hu
    have hq : q ∈ Ideal.span {x, q} := Ideal.subset_span (by simp)
    have hp : p ∈ Ideal.span {x, q} := by
      obtain ⟨u, hu'⟩ := hu.exists_left_inv
      have hp : p = u * x - u * d * q := by
        rw [← hx]
        linear_combination (-p) * hu'
      rw [hp]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ hq)
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · intro y hy
      rcases hy with hy | hy
      · exact hy ▸ hxm
      · rw [Set.mem_singleton_iff.mp hy, ← hpq]
        exact Ideal.subset_span (by simp)
    · rw [← hpq, Ideal.span_le]
      intro y hy
      rcases hy with hy | hy
      · exact hy ▸ hp
      · exact Set.mem_singleton_iff.mp hy ▸ hq
  rcases hunit with hu | hu
  · refine ⟨b, ?_, hdim⟩
    rw [hrange]
    exact key a b c₀ c₁ hspan hx hu
  · have hspan' : Ideal.span {b, a} = maximalIdeal R := by
      rw [Set.pair_comm]
      exact hspan
    have hx' : c₁ * b + c₀ * a = x := by
      rw [← hx]
      ring
    refine ⟨a, ?_, hdim⟩
    rw [hrange]
    exact key b a c₁ c₀ hspan' hx' hu

/-- If `x, t ∈ 𝔪` and `x ∉ 𝔪²`, the monomial valuation of weights `(j, 1)` takes the value
`v_{x,t;j}(x) = j`: every monomial `t^i x^k` of weight `i + j k > j` lies in `𝔪²`. -/
private theorem monomialValuation_eq_of_notMem_sq {R : Type*} [CommRing R] [IsLocalRing R]
    {x t : R} (hx : x ∈ maximalIdeal R) (ht : t ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) {j : ℕ} (hj : 1 ≤ j) :
    MMP.Resolution.monomialValuation t x j x = j := by
  refine le_antisymm (iSup₂_le fun ν hν => ?_)
    (le_iSup₂_of_le j (Ideal.subset_span ⟨0, 1, by simp, by simp⟩) le_rfl)
  by_contra hlt
  have hjν : j < ν := by exact_mod_cast not_le.mp hlt
  refine hx2 ((Ideal.span_le.mpr ?_) hν)
  rintro r ⟨i, k, hik, rfl⟩
  have h2 : 2 ≤ i + k := by
    by_contra h
    have hk : k ≤ 1 := by omega
    interval_cases k
    · simp only [mul_zero, add_zero] at hik
      omega
    · simp only [mul_one] at hik
      omega
  have hmem : t ^ i * x ^ k ∈ maximalIdeal R ^ (i + k) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ht i) (Ideal.pow_mem_pow hx k)
  exact Ideal.pow_le_pow_right h2 hmem

/-! ### Monomial valuations at the generic point of a surface -/

/-- The order-reversing monoid map `WithTop ℤ → ℤᵐ⁰`, `n ↦ exp (-n)`, `⊤ ↦ 0`. -/
private def expNeg : WithTop ℤ → ℤᵐ⁰
  | ⊤ => 0
  | (n : ℤ) => WithZero.exp (-n)

private theorem expNeg_coe (n : ℤ) : expNeg n = WithZero.exp (-n) := rfl

private theorem expNeg_top : expNeg ⊤ = 0 := rfl

private theorem expNeg_add (a b : WithTop ℤ) : expNeg (a + b) = expNeg a * expNeg b := by
  cases a <;> cases b <;>
    simp [expNeg_top, ← WithTop.coe_add, expNeg_coe, neg_add, WithZero.exp_add, mul_comm]

private theorem expNeg_antitone : Antitone expNeg := by
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

private theorem valuationOfAddValuation_apply {R : Type*} [Ring R]
    (V : AddValuation R (WithTop ℤ)) (z : R) :
    valuationOfAddValuation V z = expNeg (V z) := rfl

private theorem isRegularSystemOfParameters_swap {R : Type*} [CommRing R] [IsLocalRing R]
    {x y : R} (hxy : IsRegularSystemOfParameters ![x, y]) :
    IsRegularSystemOfParameters ![y, x] := by
  refine ⟨?_, hxy.2⟩
  rw [← hxy.1]
  congr 1
  ext
  simp [Matrix.range_cons, Set.pair_comm]

/-- At the generic point of an irreducible closed subset `V` of codimension two with regular
local ring, a regular system of parameters `(x, t)` carries the monomial valuations
`v_{x,t;j}` of weights `(j, 1)` for all `j ≥ 1`. -/
private theorem exists_isWeightedMonomialValuation {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] (hY : IsNormalVariety ℂ sY)
    {V : IrreducibleCloseds Y} (hV : codimension V = 2)
    [IsRegularLocalRing (Y.presheaf.stalk V.isIrreducible.genericPoint)]
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint}
    (hxt : IsRegularSystemOfParameters ![x, t]) :
    ∃ v : ℕ → Valuation Y.functionField ℤᵐ⁰,
      ∀ j, 1 ≤ j → IsWeightedMonomialValuation sY V x t j (v j) := by
  have h : ∀ j, 1 ≤ j → ∃ v, IsWeightedMonomialValuation sY V x t j v := by
    intro j hj
    obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
      Y.functionField (isRegularSystemOfParameters_swap hxt) hj
    refine ⟨valuationOfAddValuation W, hY, hV, inferInstance, hxt, hj, fun f hf => ?_⟩
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
    refine ⟨M, hM.symm, ?_⟩
    rw [valuationOfAddValuation_apply, hW, ← hM]
    rfl
  have h' : ∀ j, ∃ v, 1 ≤ j → IsWeightedMonomialValuation sY V x t j v := fun j =>
    if hj : 1 ≤ j then ⟨_, fun _ => (h j hj).choose_spec⟩
    else ⟨(h 1 le_rfl).choose, fun h1 => absurd h1 hj⟩
  choose v hv using h'
  exact ⟨v, hv⟩

/-- At a point with regular local ring, every prime divisor has a local equation: its stalk
ideal is principal, generated by a nonzero element. -/
private theorem exists_stalk_idealSheaf_eq_span {X : Scheme.{0}} [IsIntegral X] {η : X}
    [IsRegularLocalRing (X.presheaf.stalk η)] (S : MMP.Mori.PrimeDivisor X) :
    ∃ g : X.presheaf.stalk η, g ≠ 0 ∧ IdealSheafData.stalk S.idealSheaf η = Ideal.span {g} := by
  have : IsDomain (X.presheaf.stalk η) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (X.presheaf.stalk η) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  by_cases hS : η ∈ S.support
  · obtain ⟨q, -, hq, hh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hS
    obtain ⟨g, hg⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh).principal
    refine ⟨g, ?_, hq.trans hg⟩
    rintro rfl
    exact q.asIdeal.ne_bot_of_height_eq_one hh (by rw [hg, Ideal.span_singleton_eq_bot])
  · exact ⟨1, one_ne_zero, (MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support S hS).trans
      Ideal.span_singleton_one.symm⟩

/-! ### The surface on a model -/

/-- In `WithBot ℕ∞`, `2 + c = 4` forces `c = 2`. -/
private theorem eq_two_of_two_add_eq_four {c : ℕ∞}
    (h : (2 : WithBot ℕ∞) + (c : WithBot ℕ∞) = 4) : c = 2 := by
  have h' : (2 + c : ℕ∞) = 4 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n =>
    have : 2 + n = 4 := by exact_mod_cast h'
    norm_cast
    omega

/-- On a terminal pair `(X, B)` with `X` a `ℚ`-factorial complex variety, the local ring at the
generic point of an irreducible closed subset of codimension at most two is regular. -/
private theorem isRegularLocalRing_stalk_genericPoint {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}
    (h : IsKltTerminalPair sX B) (hQ : IsQFactorial sX) (V : IrreducibleCloseds X)
    (hV : codimension V ≤ 2) :
    IsRegularLocalRing (X.presheaf.stalk V.isIrreducible.genericPoint) := by
  obtain ⟨-, n, K, hK, -⟩ := h.1.1.isPair
  have h3 := (h.isTerminalVariety_and_three_le_closedsCodimension_singularLocus
    (isQCartier_of_isQFactorial sX hQ B) hK (isQCartier_of_isQFactorial sX hQ _)).2
  have hη : V.isIrreducible.genericPoint ∈ smoothLocus sX := by
    by_contra hη
    have hsub : (V : Set X) ⊆ (singularLocus sX : Set X) := by
      rw [← (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def]
      exact (singularLocus sX).isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη)
    have := (le_closedsCodimension_iff.mp h3) V hsub
    have : (3 : ℕ∞) ≤ 2 := this.trans hV
    exact absurd this (by decide)
  obtain ⟨U, hηU, hU⟩ := mem_smoothLocus_iff.mp hη
  haveI : LocallyOfFiniteType sX := hQ.1.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType (U.ι ≫ sX) := inferInstance
  have hreg := (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk
    (U.ι ≫ sX)).mp hU ⟨_, hηU⟩
  exact IsRegularLocalRing.of_ringEquiv (U.stalkIso ⟨_, hηU⟩).commRingCatIsoToRingEquiv

/-- **Weights of monomial valuations.** On a model `(Y, Θ)` of a prepared chain, let `f_P` be
local equations at `η_V` of the components `P` of `Θ`. A monomial valuation `v = v_{x,t;j}` at
`η_V` has centre `V` and weight `w_v = w(2 - a)` for `a = 1 + j - ∑_P Θ(P) v(f_P)`. -/
private theorem weight_eq_of_isWeightedMonomialValuation {T : StabilizedSmallKltTail}
    {Q : PreparedChain T} {x : Q.ModelIndex} {V : IrreducibleCloseds (Q.chain.model x.1)}
    {w : Valuation (Q.chain.model x.1).functionField ℤᵐ⁰ → ℕ}
    (hw : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v))
    (hpair : MMP.Fourfold.IsPair (Q.chain.modelStructure x.1) (Q.chain.modelBoundary x.1))
    {f : MMP.Mori.PrimeDivisor (Q.chain.model x.1) →
      (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint}
    (hf : ∀ S ∈ (Q.chain.modelBoundary x.1).support,
      IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {f S})
    {x' t' : (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint} {j : ℕ}
    {v : Valuation (Q.chain.model x.1).functionField ℤᵐ⁰}
    (hv : IsWeightedMonomialValuation (Q.chain.modelStructure x.1) V x' t' j v) :
    MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧
      w v = difficultyWeight Q.scale (2 - (1 + j - ∑ S ∈ (Q.chain.modelBoundary x.1).support,
        ((Q.chain.modelBoundary x.1).coeff S : ℝ) *
          (-WithZero.log (v (algebraMap _ (Q.chain.model x.1).functionField (f S))) : ℤ))) := by
  have hc := hv.isNormalizedDivisorialValuation_and_isCentre.2
  obtain ⟨n, D, hDv, hD⟩ := hv.hasLogDiscrepancy hpair f hf
  obtain ⟨-, a', ⟨n', D', -, hD'v, hD'⟩, h⟩ := hw v hc
  refine ⟨hc, h.trans ?_⟩
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq_of_isPair hpair.isPair hD' hD
    (hD'v.trans hDv.symm)]

/-- The value of a monomial valuation `v_{x,t;j}` on a nonzero element `g` of `𝒪_{Y,η_V}` is a
natural number `M = v_{x,t;j}(g)`, read off as `-log v(g)`. -/
private theorem exists_neg_log_eq {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    {V : IrreducibleCloseds Y} {x t : Y.presheaf.stalk V.isIrreducible.genericPoint} {j : ℕ}
    {v : Valuation Y.functionField ℤᵐ⁰} (hv : IsWeightedMonomialValuation sY V x t j v)
    {g : Y.presheaf.stalk V.isIrreducible.genericPoint} (hg : g ≠ 0) :
    ∃ M : ℕ, MMP.Resolution.monomialValuation t x j g = M ∧
      -WithZero.log (v (algebraMap _ Y.functionField g)) = M := by
  obtain ⟨M, hM, hvM⟩ := hv.2.2.2.2.2 g hg
  exact ⟨M, hM, by rw [hvM, WithZero.log_exp, neg_neg]⟩

/-- **The valuations along a regular boundary component.** On a model `(Y, Θ)` of a prepared
chain, let `𝒪_{Y,η_V}` be regular of dimension two with local equations `f_P` of the prime
divisors, and let the equation `x = f_{P₀}` of a component `P₀` of `Θ` lie in `𝔪 ∖ 𝔪²`. Then
`x` is part of a regular system of parameters `(x, t)`, and the valuations `v_j = v_{x,t;j}`,
`j ≥ 1`, are pairwise distinct, have centre `V`, and have weights
`w_{v_j} ≥ w(1 - j(1 - Θ(P₀)))`. -/
private theorem exists_valuations_of_mem_maximalIdeal {T : StabilizedSmallKltTail}
    {Q : PreparedChain T} {x : Q.ModelIndex} {V : IrreducibleCloseds (Q.chain.model x.1)}
    {w : Valuation (Q.chain.model x.1).functionField ℤᵐ⁰ → ℕ}
    (hw : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v))
    (hpair : MMP.Fourfold.IsPair (Q.chain.modelStructure x.1) (Q.chain.modelBoundary x.1))
    (hY : IsNormalVariety ℂ (Q.chain.modelStructure x.1)) (hcodim : codimension V = 2)
    [IsRegularLocalRing ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint)]
    {f : MMP.Mori.PrimeDivisor (Q.chain.model x.1) →
      (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint}
    (hf0 : ∀ P, f P ≠ 0)
    (hf : ∀ P, IdealSheafData.stalk P.idealSheaf V.isIrreducible.genericPoint = Ideal.span {f P})
    {a a' : (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint}
    (haa' : IsRegularSystemOfParameters ![a, a'])
    {P₀ : MMP.Mori.PrimeDivisor (Q.chain.model x.1)}
    (hP₀ : P₀ ∈ (Q.chain.modelBoundary x.1).support) (hx : f P₀ ∈ maximalIdeal _)
    (hx2 : f P₀ ∉ maximalIdeal _ ^ 2) :
    ∃ (t : (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint)
      (v : ℕ → Valuation (Q.chain.model x.1).functionField ℤᵐ⁰),
      IsRegularSystemOfParameters ![f P₀, t] ∧ Set.InjOn v {j | 1 ≤ j} ∧
      ∀ j, 1 ≤ j → IsWeightedMonomialValuation (Q.chain.modelStructure x.1) V (f P₀) t j (v j) ∧
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) (v j) V ∧
        difficultyWeight Q.scale (1 - j * (1 - (Q.chain.modelBoundary x.1).coeff P₀)) ≤
          w (v j) := by
  obtain ⟨t, ht⟩ := exists_isRegularSystemOfParameters_pair haa' hx hx2
  obtain ⟨v, hv⟩ := exists_isWeightedMonomialValuation hY hcodim ht
  have htm : t ∈ maximalIdeal
      ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint) := by
    rw [← ht.1]
    exact Ideal.subset_span ⟨1, rfl⟩
  have hvx : ∀ j, 1 ≤ j →
      -WithZero.log (v j (algebraMap _ (Q.chain.model x.1).functionField (f P₀))) = j :=
    fun j hj => by
      obtain ⟨M, hM, hvM⟩ := exists_neg_log_eq (hv j hj) (hf0 P₀)
      rw [hvM]
      have := (monomialValuation_eq_of_notMem_sq hx htm hx2 hj).symm.trans hM
      exact_mod_cast this.symm
  refine ⟨t, v, ht, fun j hj j' hj' h => ?_, fun j hj => ?_⟩
  · have h1 := hvx j hj
    rw [h, hvx j' hj'] at h1
    exact_mod_cast h1.symm
  obtain ⟨hc, hwv⟩ :=
    weight_eq_of_isWeightedMonomialValuation hw hpair (fun S _ => hf S) (hv j hj)
  refine ⟨hv j hj, hc, ?_⟩
  rw [hwv]
  refine difficultyWeight_mono _ ?_
  have hν : ∀ P, (0 : ℝ) ≤
      ((-WithZero.log (v j (algebraMap _ (Q.chain.model x.1).functionField (f P))) : ℤ) :
        ℝ) := fun P => by
    obtain ⟨M, -, hM⟩ := exists_neg_log_eq (hv j hj) (hf0 P)
    rw [hM]
    positivity
  have hsingle := Finset.single_le_sum (f := fun P =>
    ((Q.chain.modelBoundary x.1).coeff P : ℝ) *
      ((-WithZero.log (v j (algebraMap _ (Q.chain.model x.1).functionField (f P))) : ℤ) :
        ℝ)) (fun P _ => mul_nonneg (by exact_mod_cast hpair.nonneg P) (hν P)) hP₀
  simp only [hvx j hj, Int.cast_natCast] at hsingle
  linarith

/-- **Labels inject into the boundary.** If the coefficients `b_i = Θ(c_i)` are read at the
images of an injection `c` into the prime divisors and `Θ ≥ 0`, then
`∑_i μ(c_i) b_i ≤ ∑_{P ∈ Supp Θ} Θ(P) μ(P)`. -/
private theorem sum_mul_le_sum_coeff_mul {ι : Type*} [Fintype ι] {Y : Scheme.{0}}
    {Θ : MMP.Mori.QDivisor Y} (hΘ : ∀ P, 0 ≤ Θ.coeff P) {c : ι → MMP.Mori.PrimeDivisor Y}
    (hc : Function.Injective c) (μ : MMP.Mori.PrimeDivisor Y → ℕ) {b : ι → ℚ}
    (hbc : ∀ i, b i = Θ.coeff (c i)) :
    ∑ i, (μ (c i) : ℝ) * (b i : ℝ) ≤ ∑ P ∈ Θ.support, (Θ.coeff P : ℝ) * (μ P : ℝ) := by
  classical
  calc ∑ i, (μ (c i) : ℝ) * (b i : ℝ)
      = ∑ i ∈ Finset.univ.filter (fun i => c i ∈ Θ.support),
          (Θ.coeff (c i) : ℝ) * (μ (c i) : ℝ) := by
        rw [Finset.sum_filter_of_ne]
        · exact Finset.sum_congr rfl fun i _ => by rw [hbc i, mul_comm]
        · intro i _ h
          refine Finsupp.mem_support_iff.mpr fun h0 => h ?_
          change (Θ.coeff (c i) : ℝ) * _ = 0
          rw [show Θ.coeff (c i) = 0 from h0, Rat.cast_zero, zero_mul]
    _ = ∑ P ∈ (Finset.univ.filter (fun i => c i ∈ Θ.support)).image c,
          (Θ.coeff P : ℝ) * (μ P : ℝ) :=
        (Finset.sum_image (f := fun P => (Θ.coeff P : ℝ) * (μ P : ℝ))
          fun i _ i' _ h => hc h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (fun P hP => by
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hP
          exact (Finset.mem_filter.mp hi).2)
        fun P _ _ => mul_nonneg (by exact_mod_cast hΘ P) (Nat.cast_nonneg _)

/-- **The order valuations.** On a model `(Y, Θ)` of a prepared chain with `𝒪_{Y,η_V}` regular,
local equations `f_P` and multiplicities `μ(P) = mult_V P`, every order valuation `v_{x,t;1}`
has centre `V` and weight `w_v ≥ w(σ)` for any `σ ≤ ∑_P Θ(P) μ(P)`. -/
private theorem isCentre_and_difficultyWeight_le_of_order {T : StabilizedSmallKltTail}
    {Q : PreparedChain T} {x : Q.ModelIndex} {V : IrreducibleCloseds (Q.chain.model x.1)}
    {w : Valuation (Q.chain.model x.1).functionField ℤᵐ⁰ → ℕ}
    (hw : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v))
    (hpair : MMP.Fourfold.IsPair (Q.chain.modelStructure x.1) (Q.chain.modelBoundary x.1))
    {f : MMP.Mori.PrimeDivisor (Q.chain.model x.1) →
      (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint}
    (hf0 : ∀ P, f P ≠ 0)
    (hf : ∀ P, IdealSheafData.stalk P.idealSheaf V.isIrreducible.genericPoint = Ideal.span {f P})
    {μ : MMP.Mori.PrimeDivisor (Q.chain.model x.1) → ℕ}
    (hμ : ∀ P, P.multiplicityAlong V = μ P) {σ : ℝ}
    (hσ : σ ≤ ∑ P ∈ (Q.chain.modelBoundary x.1).support,
      ((Q.chain.modelBoundary x.1).coeff P : ℝ) * (μ P : ℝ))
    {x' t' : (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint}
    (hxt' : IsRegularSystemOfParameters ![x', t'])
    {v : Valuation (Q.chain.model x.1).functionField ℤᵐ⁰}
    (hv : IsWeightedMonomialValuation (Q.chain.modelStructure x.1) V x' t' 1 v) :
    MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧
      difficultyWeight Q.scale σ ≤ w v := by
  obtain ⟨hc, hwv⟩ := weight_eq_of_isWeightedMonomialValuation hw hpair (fun S _ => hf S) hv
  refine ⟨hc, ?_⟩
  rw [hwv]
  refine difficultyWeight_mono _ (hσ.trans (le_of_eq ?_))
  have hνμ : ∀ P, (-WithZero.log (v (algebraMap _ (Q.chain.model x.1).functionField (f P))) :
      ℤ) = μ P := fun P => by
    obtain ⟨M, hM, hvM⟩ := exists_neg_log_eq hv (hf0 P)
    rw [hvM]
    have h1 : (M : ℕ∞) = μ P := by
      rw [← hM, monomialValuation_one_eq_iSup hxt', ← hμ,
        P.multiplicityAlong_eq_of_stalkIdeal_eq_span V (by
          rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk]
          exact hf P)]
    have h2 : M = μ P := by exact_mod_cast h1
    rw [h2]
  simp only [hνμ, Int.cast_natCast, Nat.cast_one]
  ring

/-! ### The valuations dominating the error -/

/-- **The valuations dominating the ceiling error.** On a model `(Y, Θ)` of a prepared chain, let
`𝒪_{Y,η_V}` be a two-dimensional regular local ring with local equations `f_P` and
multiplicities `μ(P) = mult_V P`, and let `c` inject labels `i` into the prime divisors, with
coefficients `b_i = Θ(c_i) < 1` and integers `r_i ≤ μ(c_i)` such that
`σ = ∑_i μ(c_i) b_i < 1`. Then finitely many pairwise distinct valuations `v_1, …, v_{K-1}`
centred at `V` have total weight at least `w(σ) + ∑_i r_i ∑_{j ≥ 2} w(1 - j(1 - b_i))`.

They are the order valuation `v_1` alone, unless some `i₀` has `r_{i₀} ≥ 1` and `b_{i₀} > 1/2`;
then `μ(c_{i₀}) = r_{i₀} = 1`, every other higher term vanishes, and they are the monomial
valuations `v_{x,t;j}` built on the regular parameter `x = f_{c_{i₀}}`. -/
private theorem exists_injOn_difficultyWeight_add_sum_le {T : StabilizedSmallKltTail}
    {Q : PreparedChain T} {x : Q.ModelIndex} {V : IrreducibleCloseds (Q.chain.model x.1)}
    {w : Valuation (Q.chain.model x.1).functionField ℤᵐ⁰ → ℕ}
    (hw : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v))
    (hpair : MMP.Fourfold.IsPair (Q.chain.modelStructure x.1) (Q.chain.modelBoundary x.1))
    (hY : IsNormalVariety ℂ (Q.chain.modelStructure x.1)) (hcodim : codimension V = 2)
    [IsRegularLocalRing ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint)]
    {f : MMP.Mori.PrimeDivisor (Q.chain.model x.1) →
      (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint}
    (hf0 : ∀ P, f P ≠ 0)
    (hf : ∀ P, IdealSheafData.stalk P.idealSheaf V.isIrreducible.genericPoint = Ideal.span {f P})
    {a a' : (Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint}
    (haa' : IsRegularSystemOfParameters ![a, a'])
    {μ : MMP.Mori.PrimeDivisor (Q.chain.model x.1) → ℕ}
    (hμ : ∀ P, P.multiplicityAlong V = μ P)
    {ι : Type*} [Fintype ι] {c : ι → MMP.Mori.PrimeDivisor (Q.chain.model x.1)}
    (hc : Function.Injective c) {b : ι → ℚ}
    (hbc : ∀ i, b i = (Q.chain.modelBoundary x.1).coeff (c i)) (hb1 : ∀ i, (b i : ℝ) < 1)
    {r : ι → ℕ} (hrm : ∀ i, r i ≤ μ (c i)) (hσlt : ∑ i, (μ (c i) : ℝ) * (b i : ℝ) < 1) :
    ∃ (v : ℕ → Valuation (Q.chain.model x.1).functionField ℤᵐ⁰) (K : ℕ),
      Set.InjOn v (Finset.Ico 1 K : Set ℕ) ∧
      (∀ j ∈ Finset.Ico 1 K, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) (v j) V) ∧
      difficultyWeight Q.scale (∑ i, (μ (c i) : ℝ) * (b i : ℝ)) +
          ∑ i, r i * ∑ j ∈ Finset.Ico 2 (⌈(1 - (b i : ℝ))⁻¹⌉₊ + 1),
            difficultyWeight Q.scale (1 - j * (1 - b i)) ≤
        ∑ j ∈ Finset.Ico 1 K, w (v j) := by
  classical
  have hb0 : ∀ i, (0 : ℝ) ≤ b i := fun i => by
    rw [hbc i]
    exact_mod_cast hpair.nonneg _
  have hσ := sum_mul_le_sum_coeff_mul hpair.nonneg hc μ hbc
  by_cases hex : ∃ i, 1 ≤ r i ∧ (1 / 2 : ℝ) < b i
  · obtain ⟨i₀, hr₀, hb₀⟩ := hex
    obtain ⟨hm₀, hr₁, hle⟩ := eq_one_and_forall_le_half
      (fun i _ => hb0 i) hσlt (fun i _ => hrm i) (Finset.mem_univ i₀) hr₀ hb₀
    -- the local equation of `c i₀` is a regular parameter
    have hx₀ := mem_maximalIdeal_and_notMem_sq_of_iSup_eq_one (g := f (c i₀)) (by
      rw [← (c i₀).multiplicityAlong_eq_of_stalkIdeal_eq_span V (by
        rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk]
        exact hf _), hμ]
      exact_mod_cast hm₀)
    have hS₀ : c i₀ ∈ (Q.chain.modelBoundary x.1).support :=
      Finsupp.mem_support_iff.mpr fun h0 => by
        rw [hbc i₀, show (Q.chain.modelBoundary x.1).coeff (c i₀) = 0 from h0] at hb₀
        norm_num at hb₀
    obtain ⟨t₀, v, ht₀, hinj, hvj⟩ := exists_valuations_of_mem_maximalIdeal hw hpair hY hcodim
      hf0 hf haa' hS₀ hx₀.1 hx₀.2
    rw [← hbc i₀] at hvj
    have hK : 1 < ⌈(1 - (b i₀ : ℝ))⁻¹⌉₊ + 1 := by
      have : 0 < ⌈(1 - (b i₀ : ℝ))⁻¹⌉₊ := Nat.ceil_pos.mpr (inv_pos.mpr (sub_pos.mpr (hb1 i₀)))
      omega
    refine ⟨v, ⌈(1 - (b i₀ : ℝ))⁻¹⌉₊ + 1, hinj.mono fun j hj => (Finset.mem_Ico.mp hj).1,
      fun j hj => (hvj j (Finset.mem_Ico.mp hj).1).2.1, ?_⟩
    rw [Finset.sum_eq_single (M := ℕ) i₀ (fun i _ hi => ?_) (by simp), hr₁, one_mul,
      Finset.sum_eq_sum_Ico_succ_bot hK]
    · exact add_le_add (isCentre_and_difficultyWeight_le_of_order hw hpair hf0 hf hμ hσ ht₀
        (hvj 1 le_rfl).1).2 (Finset.sum_le_sum fun j hj =>
        (hvj j (by have := (Finset.mem_Ico.mp hj).1; omega)).2.2)
    · rcases Nat.eq_zero_or_pos (r i) with hri | hri
      · rw [hri, zero_mul]
      · rw [sum_Ico_two_eq_zero _ (hle i (Finset.mem_univ i) hi hri) _, mul_zero]
  · obtain ⟨v₀, hv₀⟩ := exists_isWeightedMonomialValuation hY hcodim haa'
    have h₁ := isCentre_and_difficultyWeight_le_of_order hw hpair hf0 hf hμ hσ haa' (hv₀ 1 le_rfl)
    refine ⟨fun _ => v₀ 1, 2, fun j hj j' hj' _ => ?_, fun j _ => h₁.1, ?_⟩
    · have h1 := Finset.mem_Ico.mp hj
      have h2 := Finset.mem_Ico.mp hj'
      omega
    · rw [Finset.sum_eq_zero (M := ℕ) fun i _ => ?_, add_zero, show Finset.Ico 1 2 = {1} by decide,
        Finset.sum_singleton]
      · exact h₁.2
      · rcases Nat.eq_zero_or_pos (r i) with hri | hri
        · rw [hri, zero_mul]
        · rw [sum_Ico_two_eq_zero _ (not_lt.mp fun h => hex ⟨i, hri, h⟩) _, mul_zero]

/-- On a model of a prepared chain, the weights of valuations centred at a surface `V` are
finitely supported: a valuation of nonzero weight is exceptional with `a(v) < 2`. -/
private theorem finite_setOf_isCentre_and_ne_zero {T : StabilizedSmallKltTail}
    {Q : PreparedChain T} {x : Q.ModelIndex} {V : IrreducibleCloseds (Q.chain.model x.1)}
    (hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2)
    {w : Valuation (Q.chain.model x.1).functionField ℤᵐ⁰ → ℕ}
    (hw : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v)) :
    {u | MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) u V ∧ w u ≠ 0}.Finite := by
  obtain ⟨hproj, hQF, hdim, hterm, -⟩ := Q.isKltTerminalPair_modelBoundary x
  refine (IsKltTerminalPair.finite_setOf_isCentre_of_hasLogDiscrepancy_lt_two hproj hQF hdim
    hterm (L := (Q.chain.modelBoundary x.1).support) subset_rfl V hV).subset ?_
  rintro u ⟨hcen, hw0⟩
  obtain ⟨a, ⟨n, D, -, hD, hlogD⟩, ha⟩ := (hw u hcen).exists_eq_zero_iff Q.isAdmissibleScale.pos
  exact ⟨(hw u hcen).isExceptionalValuation, hcen, a, not_le.1 (mt ha.2 hw0), n, D, hD, hlogD⟩

end Proof_lem_oai4_ceiling_error

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

open Proof_lem_oai4_ceiling_error

/-- On a model `(Y, Θ)` of a prepared chain, at an irreducible surface `V ⊆ Y`,
`∑_{c_Y(v) = V} w_v - ∑_h r_{V,h} d_h ≥ -max{r_V^var - 1, 0}`, where `w_v` is the weight
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`) at the chain's scale of
a valuation with centre `V`, `r_{V,h}` the branch number, `d_h` the default echo weight
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelDefault`) of the label `S_h`, and
`r_V^var` the varying branch number at `V`. -/
@[mmp "lem_oai4_ceiling_error"]
public theorem neg_max_le_finsum_valuationWeight_sub {T : StabilizedSmallKltTail}
    (Q : PreparedChain T) (x : Q.ModelIndex) (V : IrreducibleCloseds (Q.chain.model x.1))
    (hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2)
    (w : Valuation (Q.chain.model x.1).functionField ℤᵐ⁰ → ℕ)
    (r d : Q.chain.Label → ℕ) (rv : ℕ)
    (hw : ∀ v, MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v))
    (hr : ∀ S : Q.chain.Label, Q.chain.IsLabelBranchNumber S x.1 V (r S))
    (hd : ∀ S : Q.chain.Label, Q.chain.IsLabelDefault Q.scale S x.1 (d S))
    (hrv : Q.chain.IsVaryingBranchNumber x.1 V rv) :
    -max ((rv : ℤ) - 1) 0 ≤
      ((∑ᶠ (v) (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V), w v : ℕ) :
        ℤ) - ((∑ᶠ S, r S * d S : ℕ) : ℤ)  := by
  classical
  haveI := Q.chain.finite_label
  letI := Fintype.ofFinite Q.chain.Label
  obtain ⟨-, hQF, hdim, hterm, -, -, hlt⟩ := Q.isKltTerminalPair_modelBoundary x
  have hpair : MMP.Fourfold.IsPair (Q.chain.modelStructure x.1) (Q.chain.modelBoundary x.1) :=
    hterm.1.1
  have hY : IsNormalVariety ℂ (Q.chain.modelStructure x.1) := hQF.1
  haveI : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hY.1.toLocallyOfFiniteType
  -- `𝒪_{Y,η_V}` is a two-dimensional regular local ring
  have hcoh : Order.coheight V.isIrreducible.genericPoint = 2 := by
    have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight
      (Q.chain.modelStructure x.1) V.isIrreducible.genericPoint
    rw [(V.isIrreducible.isGenericPoint_genericPoint V.isClosed).def, hV, hdim] at h
    exact eq_two_of_two_add_eq_four h
  have hcodim : codimension V = 2 := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hcoh]
  haveI hreg := isRegularLocalRing_stalk_genericPoint hterm hQF V hcodim.le
  have hdim2 : ringKrullDim
      ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hcoh]
    rfl
  obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters
    ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint)
  obtain rfl : n = 2 := by
    have h := hz.2
    rw [hdim2] at h
    exact_mod_cast h.symm
  have hz' : IsRegularSystemOfParameters ![z 0, z 1] := by
    convert hz using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨v₀, hv₀⟩ := exists_isWeightedMonomialValuation hY hcodim hz'
  -- local equations, multiplicities and the values of monomial valuations on them
  choose f hf0 hf using fun P : MMP.Mori.PrimeDivisor (Q.chain.model x.1) =>
    exists_stalk_idealSheaf_eq_span (η := V.isIrreducible.genericPoint) P
  have hmult : ∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
      P.multiplicityAlong V = ⨆ (s : ℕ) (_ : f P ∈ maximalIdeal
        ((Q.chain.model x.1).presheaf.stalk V.isIrreducible.genericPoint) ^ s), (s : ℕ∞) :=
    fun P => P.multiplicityAlong_eq_of_stalkIdeal_eq_span V (by
      rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk]
      exact hf P)
  have hμ : ∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1),
      ∃ M : ℕ, P.multiplicityAlong V = M := fun P => by
    obtain ⟨M, hM, -⟩ := exists_neg_log_eq (hv₀ 1 le_rfl) (hf0 P)
    exact ⟨M, by rw [hmult P, ← monomialValuation_one_eq_iSup hz', hM]⟩
  choose μ hμ using hμ
  -- centres, coefficients and branch numbers of the labels
  obtain ⟨e, he⟩ := exists_equiv_isLabelCentre_iff Q.chain x.1
  have hcinj : Function.Injective fun S : Q.chain.Label => e S.1 := fun S S' h =>
    Subtype.ext (e.injective h)
  have hd' : ∀ S, ∃ b : ℚ, Q.chain.IsLabelCoefficient S x.1 b ∧
      d S = defaultWeight Q.scale b := hd
  choose b hb hdb using hd'
  have hbc : ∀ S, b S = (Q.chain.modelBoundary x.1).coeff (e S.1) := fun S => by
    rcases hb S with ⟨P, hP, hbP⟩ | ⟨hno, -⟩
    · rw [← hbP, (he S P).mp hP]
    · exact absurd ((he S (e S.1)).mpr rfl) (hno _)
  have hrc : ∀ S, r S = branchNumber (e S.1) (V : Set (Q.chain.model x.1)) := fun S => by
    rcases hr S with ⟨P, hP, hrP⟩ | ⟨hno, -⟩
    · rw [hrP, (he S P).mp hP]
    · exact absurd ((he S (e S.1)).mpr rfl) (hno _)
  have hb1 : ∀ S, (b S : ℝ) < 1 := fun S => by exact_mod_cast (hlt S _ (hb S)).2
  have hm : ∀ (S : Q.chain.Label) (P : MMP.Mori.PrimeDivisor (Q.chain.model x.1)),
      Q.chain.IsLabelCentre S x.1 P → P.multiplicityAlong V = ((fun S => μ (e S.1)) S : ℕ) :=
    fun S P hP => by
      rw [← (he S P).mp hP]
      exact hμ _
  -- the branch number is at most the multiplicity
  have hrm : ∀ S, r S ≤ μ (e S.1) := fun S => by
    rw [hrc S, branchNumber]
    have h := encard_branches_le_multiplicityAlong (Q.chain.modelStructure x.1) V hreg hdim2
      (e S.1)
    rw [hμ] at h
    have h' := (Set.finite_of_encard_le_coe h).cast_ncard_eq.trans_le h
    exact_mod_cast h'
  -- `∑_h m_h b_h < 1`
  have hσlt : ∑ S, (μ (e S.1) : ℝ) * (b S : ℝ) < 1 := by
    have h := Q.finsum_multiplicityAlong_mul_lt_one x V hV (fun S => μ (e S.1)) b hm hb
    rw [finsum_eq_sum_of_fintype] at h
    have h' : ((∑ S, ((μ (e S.1) : ℕ) : ℚ) * b S : ℚ) : ℝ) < 1 := by exact_mod_cast h
    push_cast at h'
    exact h'
  obtain ⟨v, K, hinj, hcen, hle⟩ := exists_injOn_difficultyWeight_add_sum_le hw hpair hY hcodim
    hf0 hf hz' hμ hcinj hbc hb1 hrm hσlt
  beta_reduce at hle
  -- the default splits into `w(b_h)` and its higher terms `H_h`
  set H : Q.chain.Label → ℕ := fun S => ∑ j ∈ Finset.Ico 2 (⌈(1 - (b S : ℝ))⁻¹⌉₊ + 1),
    difficultyWeight Q.scale (1 - j * (1 - b S))
  have hdH : ∀ S, d S = difficultyWeight Q.scale (b S) + H S := fun S => by
    rw [hdb S]
    exact defaultWeight_eq_add_sum_Ico _ (hb1 S)
  have hsum := sum_le_finsum_of_injOn
    (p := fun u => MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) u V)
    (finite_setOf_isCentre_and_ne_zero hV hw) hinj hcen
  -- the first default error
  have hfd := Q.sum_branchNumber_mul_difficultyWeight_le x V hV (fun S => μ (e S.1)) b r rv hm
    hb hr hrv
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype] at hfd
  beta_reduce at hfd
  have hrd : ∑ S, r S * d S =
      ∑ S, r S * difficultyWeight Q.scale (b S) + ∑ S, r S * H S := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun S _ => by rw [hdH S, mul_add]
  rw [finsum_eq_sum_of_fintype (fun S => r S * d S), hrd]
  generalize (∑ᶠ (u) (_ : MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) u V), w u) = A
    at hsum ⊢
  generalize difficultyWeight Q.scale (∑ S, (μ (e S.1) : ℝ) * (b S : ℝ)) = B at hle hfd
  have htot : ((B + ∑ S, r S * H S : ℕ) : ℤ) ≤ (A : ℤ) := Nat.cast_le.mpr (hle.trans hsum)
  push_cast at htot hfd ⊢
  linarith

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

end
