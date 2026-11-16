module
public import MMP.AlgebraicGeometry.MMP.Fourfold.GenericValuation
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Singularities.WeightedMonomialValuation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleEmbedding
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import StacksFrontier.AlgebraicGeometry.Properties.CodimensionLocalRing
public import StacksFrontier.RingTheory.NodalChart.Regularity

/-!
# Echoes at a surface of a fourfold

Let `Y` be a normal fourfold with labels `S_1, …, S_m` and one-label smooth locus `Y°`, and let
`V ⊆ S_h` be an irreducible closed surface whose generic point `η_V` lies in `Y°`. An echo of
order `j` of `S_h` at `V` is a normalized divisorial valuation `ξ` of `k(Y)` with centre `V` and
`ξ(f) = max {n ≥ 0 : f ∈ ∑_{a ≥ 0} x^a 𝔪^{max(n - ja, 0)}}` for every nonzero `f ∈ 𝒪_{Y,η_V}`,
where `x` is a local equation of `S_h` at `η_V`.

The local ring `𝒪_{Y,η_V}` is regular of dimension `4 - 2 = 2`, and `x ∈ 𝔪 ∖ 𝔪²` because `S_h`
is regular at `η_V`, so `x` completes to a regular system of parameters `(x, t)`. Since
`𝔪 = (x, t)`, the echo ideals are the weighted monomial ideals `(x^a t^b : ja + b ≥ n)`, and an
echo of order `j` is exactly the monomial valuation `v_{x,t;j}` of weight `(j, 1)` in `(x, t)`.
This gives both existence and, for a pair `(Y, Θ)` with `Θ = ∑_h b_h S_h`, `0 ≤ b_h < 1`, the
log discrepancy `a(ξ; Y, Θ) = 1 + j (1 - b_h)`: only `S_h` passes through `η_V`, and `ξ(x) = j`.

## Main results

* `MMP.Fourfold.exists_isSurfaceEcho`: echoes of every order `j ≥ 1` exist.
* `MMP.Fourfold.IsSurfaceEcho.hasLogDiscrepancy`: `a(ξ; Y, Θ) = 1 + j (1 - b_h)`.

## Implementation notes

* The base field is any field `k`, as in `MMP.Fourfold.IsSurfaceEcho`; the source takes
  `k = ℂ`. Uniqueness of the echo is `MMP.Fourfold.IsSurfaceEcho.eq`.
* The monomial valuation of weight `(j, 1)` is built directly on the two-dimensional regular
  local ring `𝒪_{Y,η_V}` (`MMP.Resolution.exists_addValuation_monomialValuation`), and the log
  discrepancy is read off `MMP.Fourfold.IsWeightedMonomialValuation.hasLogDiscrepancy`. This
  works over any base field, where an snc neighbourhood of `η_V` need not be smooth.
* `Θ = ∑_h b_h S_h` is expressed by `Θ.support ⊆ L`, and `b_h` is the coefficient `Θ.coeff S`.
  The inequality `0 ≤ b_h` is part of the pair condition `MMP.Fourfold.IsPair`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open scoped WithZero

universe u

namespace MMP.Fourfold

open MMP.Mori

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
  WithBot.coe_injective <| by
    rw [codimension_eq_ringKrullDim_stalk_genericPoint, ht.2]
    rfl

/-- If `𝔪 = (x, t)` and `j ≥ 1`, the echo ideals `∑_a x^a 𝔪^{n - ja}` are the monomial ideals
generated by the `t^α x^β` with `α + jβ ≥ n`. -/
private lemma echoIdeal_eq_monomialIdeal {R : Type*} [CommRing R] {x t : R} {𝔪 : Ideal R}
    (h𝔪 : Ideal.span {x, t} = 𝔪) {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    echoIdeal x 𝔪 j n = MMP.Resolution.monomialIdeal t x j n := by
  refine le_antisymm (iSup_le fun b => ?_) (Ideal.span_le.mpr ?_)
  · rw [← h𝔪, Set.pair_comm, ← monomialIdeal_one_eq_pow, MMP.Resolution.monomialIdeal,
      Ideal.span_mul_span']
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, rfl, _, ⟨a', b', h, rfl⟩, rfl⟩
    refine Ideal.subset_span ⟨a', b + b', ?_, by ring⟩
    have : b' ≤ j * b' := Nat.le_mul_of_pos_left b' hj
    rw [Nat.mul_add]
    omega
  · rintro _ ⟨a, b, h, rfl⟩
    refine Ideal.mem_iSup_of_mem b ?_
    rw [mul_comm (t ^ a)]
    refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _)
      (Ideal.pow_le_pow_right (show n - j * b ≤ a by omega) (Ideal.pow_mem_pow ?_ a))
    exact h𝔪 ▸ Ideal.subset_span (by simp)

private lemma mem_monomialIdeal_zero {R : Type*} [CommRing R] (x t : R) (j : ℕ) (f : R) :
    f ∈ MMP.Resolution.monomialIdeal t x j 0 := by
  simpa using Ideal.mul_mem_left (MMP.Resolution.monomialIdeal t x j 0) f
    (Ideal.subset_span ⟨0, 0, le_rfl, by simp⟩ : (1 : R) ∈ MMP.Resolution.monomialIdeal t x j 0)

/-- If `x ∈ 𝔪 ∖ 𝔪²` and `j ≥ 1`, then `j` is the largest `n` with
`x ∈ ∑_a x^a 𝔪^{max(n - ja, 0)}`. -/
private theorem isGreatest_echoIdeal {R : Type*} [CommRing R] {x : R} {𝔪 : Ideal R}
    (hx𝔪 : x ∈ 𝔪) (hx : x ∉ 𝔪 ^ 2) {j : ℕ} (hj : 1 ≤ j) :
    IsGreatest {n : ℕ | x ∈ echoIdeal x 𝔪 j n} j := by
  refine ⟨?_, fun n hn => ?_⟩
  · refine Ideal.mem_iSup_of_mem 1 ?_
    simpa using Ideal.mul_mem_mul (Ideal.mem_span_singleton_self x) (Submodule.mem_top (x := 1))
  · by_contra! hlt
    have hle : echoIdeal x 𝔪 j (j + 1) ≤ 𝔪 ^ 2 := iSup_le fun a => by
      rcases a with _ | _ | a
      · simpa using Ideal.pow_le_pow_right (by omega)
      · rw [show j + 1 - j * (0 + 1) = 1 by omega, pow_one, pow_one, pow_two]
        exact Ideal.mul_mono_left ((Ideal.span_singleton_le_iff_mem _).mpr hx𝔪)
      · refine Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
        rw [show a + 1 + 1 = 2 + a by omega, pow_add]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx𝔪 2)
    exact hx (hle (echoIdeal_antitone x 𝔪 j hlt hn))

/-- In a two-dimensional regular local ring, an element of `𝔪 ∖ 𝔪²` is part of a regular system
of parameters. -/
private theorem exists_isRegularSystemOfParameters_pair {R : Type*} [CommRing R]
    [IsRegularLocalRing R] (hdim : ringKrullDim R = 2) {x : R}
    (hxm : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ t : R, IsRegularSystemOfParameters ![x, t] := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (maximalIdeal R).fg_of_isNoetherianRing
  have h2 : (maximalIdeal R).spanFinrank = 2 := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hdim
  obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp (hs.trans h2)
  have hab : Ideal.span {a, b} = maximalIdeal R := by simpa using hspan
  have key : ∀ {p q : R}, Ideal.span {p, q} = maximalIdeal R → ∀ c₀ c₁ : R,
      x = c₀ * p + c₁ * q → IsUnit c₀ → Ideal.span {x, q} = maximalIdeal R := by
    intro p q hpq c₀ c₁ hx hu
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · rintro _ (rfl | rfl)
      exacts [hxm, hpq ▸ Ideal.subset_span (by simp)]
    · have hp : p = ↑hu.unit⁻¹ * x - ↑hu.unit⁻¹ * c₁ * q := by
        rw [hx, mul_add, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
        ring
      rw [← hpq]
      refine Ideal.span_le.mpr ?_
      rintro _ (rfl | rfl)
      · rw [hp]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      · exact Ideal.subset_span (by simp)
  have ha : a ∈ maximalIdeal R := hab ▸ Ideal.subset_span (by simp)
  have hb : b ∈ maximalIdeal R := hab ▸ Ideal.subset_span (by simp)
  obtain ⟨c₀, c₁, hx⟩ := Ideal.mem_span_pair.mp (hab ▸ hxm : x ∈ Ideal.span {a, b})
  have hunit : IsUnit c₀ ∨ IsUnit c₁ := by
    by_contra! h
    refine hx2 ?_
    rw [← hx, pow_two]
    exact add_mem (Ideal.mul_mem_mul ((mem_maximalIdeal _).2 h.1) ha)
      (Ideal.mul_mem_mul ((mem_maximalIdeal _).2 h.2) hb)
  obtain ⟨t, ht⟩ : ∃ t, Ideal.span {x, t} = maximalIdeal R := by
    rcases hunit with hu | hu
    · exact ⟨b, key hab c₀ c₁ hx.symm hu⟩
    · exact ⟨a, key (by rwa [Set.pair_comm]) c₁ c₀ (by rw [← hx]; ring) hu⟩
  exact ⟨t, isRegularSystemOfParameters_pair_iff.2 ⟨ht, hdim⟩⟩

/-! ### Local equations of a label at a surface -/

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

/-- At a point of a prime divisor `E` where `E` is regular, `𝒪_{Y,y} ⧸ I_{E,y}` is regular. -/
private theorem isRegularLocalRing_quotient_of_notMem_image_singularLocus {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ E.support)
    (hsm : y ∉ E.idealSheaf.subschemeι '' singularLocus E.idealSheaf.subscheme) :
    IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk E.idealSheaf y) := by
  obtain ⟨z, rfl⟩ : y ∈ Set.range E.idealSheaf.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have hz : IsRegularLocalRing (E.idealSheaf.subscheme.presheaf.stalk z) := by
    by_contra h
    exact hsm ⟨z, h, rfl⟩
  exact IsRegularLocalRing.of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv _ z).symm

/-- A local equation `x` of a prime divisor `E` at a point `y` where `E` is regular lies in
`𝔪_y ∖ 𝔪_y²`. -/
private theorem mem_maximalIdeal_notMem_sq_of_regular {Y : Scheme.{u}}
    (E : MMP.Mori.PrimeDivisor Y) {y : Y} (hy : y ∈ E.support)
    [IsRegularLocalRing (Y.presheaf.stalk y)]
    (hsm : y ∉ E.idealSheaf.subschemeι '' singularLocus E.idealSheaf.subscheme)
    {x : Y.presheaf.stalk y} (hx : IdealSheafData.stalk E.idealSheaf y = Ideal.span {x}) :
    x ∈ maximalIdeal _ ∧ x ∉ maximalIdeal _ ^ 2 := by
  obtain ⟨hxm, hx0⟩ := mem_maximalIdeal_and_ne_zero_of_stalk_eq_span E hy hx
  have := IsRegularLocalRing.isDomain (Y.presheaf.stalk y)
  refine ⟨hxm, fun hx2 => ?_⟩
  have hquot := isRegularLocalRing_quotient_of_notMem_image_singularLocus E hy hsm
  rw [hx] at hquot
  exact Stacks.not_isRegularLocalRing_quotient_span_singleton_of_mem_sq
    (mem_nonZeroDivisors_of_ne_zero hx0) hx2 hquot

/-- The local ring of a normal fourfold at the generic point of a surface has dimension two. -/
private theorem ringKrullDim_stalk_genericPoint_eq_two {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {V : IrreducibleCloseds Y}
    (hY : IsNormalVariety k sY)
    (hdim : topologicalKrullDim Y = 4) (hV : topologicalKrullDim (V : Set Y) = 2) :
    ringKrullDim (Y.presheaf.stalk V.isIrreducible.genericPoint) = 2 := by
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [V.isIrreducible.closure_genericPoint V.isClosed, hV, hdim] at h
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight,
    (add_right_inj_of_ne_top (by decide)).mp (WithBot.coe_inj.mp h :
      2 + Order.coheight V.isIrreducible.genericPoint = 2 + 2)]
  rfl

/-! ### Existence of echoes -/

/-- **Echoes exist.** Let `Y` be a normal fourfold over `k` with labels `L`, `S ∈ L`, and
`V ⊆ S` an irreducible closed surface whose generic point lies in the one-label smooth locus
`MMP.Fourfold.oneLabelSmoothLocus L`. Then for every `j ≥ 1` there is an echo of order `j` of
`S` at `V`, namely the monomial valuation of weight `(j, 1)` in a regular system of parameters
`(x, t)` of `𝒪_{Y,η_V}` with `x` a local equation of `S`. -/
@[mmp "lem_oai4_c1_echo_exists"]
public theorem exists_isSurfaceEcho {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] {L : Finset (MMP.Mori.PrimeDivisor Y)}
    {S : MMP.Mori.PrimeDivisor Y} {V : IrreducibleCloseds Y}
    (hY : MMP.Mori.IsNormalVariety k sY) (hdim : topologicalKrullDim Y = 4) (hS : S ∈ L)
    (hVS : (V : Set Y) ⊆ S.support) (hV : topologicalKrullDim (V : Set Y) = 2)
    (hη : V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L) {j : ℕ} (hj : 1 ≤ j) :
    ∃ ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
      IsSurfaceEcho sY L S V j ξ := by
  have hηS := hVS (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  haveI hreg := (mem_oneLabelSmoothLocus_iff.mp hη).1
  obtain ⟨q, -, hq, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support S hηS
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid
    (Y.presheaf.stalk V.isIrreducible.genericPoint)
  obtain ⟨x, hxq⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh).principal
  have hx := hq.trans hxq
  obtain ⟨hxm, hx2⟩ := mem_maximalIdeal_notMem_sq_of_regular S hηS
    ((mem_oneLabelSmoothLocus_iff.mp hη).2.1 S hS) hx
  obtain ⟨t, ht⟩ := exists_isRegularSystemOfParameters_pair
    (ringKrullDim_stalk_genericPoint_eq_two hY hdim hV) hxm hx2
  obtain ⟨hfin, -, -, W, hW, -⟩ := MMP.Resolution.exists_addValuation_monomialValuation
    Y.functionField (isRegularSystemOfParameters_swap ht) hj
  have hvalW : ∀ f : Y.presheaf.stalk V.isIrreducible.genericPoint, f ≠ 0 →
      ∃ M : ℕ, MMP.Resolution.monomialValuation t x j f = M ∧
        valuationOfAddValuation W (algebraMap _ Y.functionField f) =
          WithZero.exp (-(M : ℤ)) := by
    intro f hf
    obtain ⟨M, hM⟩ := ENat.ne_top_iff_exists.mp (hfin f hf)
    refine ⟨M, hM.symm, ?_⟩
    rw [valuationOfAddValuation_apply, hW, ← hM]
    rfl
  have hv : IsWeightedMonomialValuation sY V x t j (valuationOfAddValuation W) :=
    ⟨hY, codimension_eq_two V ht, hreg, ht, hj, hvalW⟩
  refine ⟨_, hY, hdim, hS, hVS, hV, hη, hj,
    hv.isNormalizedDivisorialValuation_and_isCentre.2, x, hx, fun f hf => ?_⟩
  obtain ⟨M, hM, hfM⟩ := hvalW f hf
  refine ⟨M, ?_, hfM⟩
  simp_rw [echoIdeal_eq_monomialIdeal (isRegularSystemOfParameters_pair_iff.1 ht).1 hj]
  exact (isGreatest_iff_iSup_eq ⟨0, mem_monomialIdeal_zero x t j f⟩).2 hM

/-! ### Log discrepancy of an echo -/

/-- **An echo at a surface is a weighted monomial valuation.** If `ξ` is an echo of order `j` of
`S` at a surface `V`, `x` a local equation of `S` at `η_V` completed by `t` to a regular system
of parameters, then `ξ = v_{x,t;j}`. -/
private theorem IsSurfaceEcho.isWeightedMonomialValuation {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    {L : Finset (MMP.Mori.PrimeDivisor Y)} {S : MMP.Mori.PrimeDivisor Y}
    {V : IrreducibleCloseds Y} {j : ℕ} {ξ : Valuation Y.functionField ℤᵐ⁰}
    (hξ : IsSurfaceEcho sY L S V j ξ)
    {x t : Y.presheaf.stalk V.isIrreducible.genericPoint}
    (hx : IdealSheafData.stalk S.idealSheaf V.isIrreducible.genericPoint = Ideal.span {x})
    (ht : IsRegularSystemOfParameters ![x, t]) :
    IsWeightedMonomialValuation sY V x t j ξ := by
  obtain ⟨hY, -, -, -, -, hη, hj, -, x', hx', hecho⟩ := hξ
  refine ⟨hY, codimension_eq_two V ht, (mem_oneLabelSmoothLocus_iff.1 hη).1, ht, hj,
    fun f hf => ?_⟩
  obtain ⟨M, hM, hξM⟩ := isEchoValue_of_span_eq (hx'.symm.trans hx) hecho f hf
  refine ⟨M, (isGreatest_iff_iSup_eq (s := {n | f ∈ MMP.Resolution.monomialIdeal t x j n})
    ⟨0, mem_monomialIdeal_zero x t j f⟩).1 ?_, hξM⟩
  simpa only [echoIdeal_eq_monomialIdeal (isRegularSystemOfParameters_pair_iff.1 ht).1 hj] using hM

/-- **Log discrepancy of an echo at a surface.** Let `(Y, Θ)` be a pair on a normal fourfold with
labels `L`, with `Θ` supported on `L` and coefficients `< 1`. If `ξ` is an echo of order `j` of
the label `S` at a surface `V`, then `a(ξ; Y, Θ) = 1 + j (1 - Θ(S))`. -/
@[mmp "lem_oai4_c1_echo_log_discrepancy"]
public theorem IsSurfaceEcho.hasLogDiscrepancy
    {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {L : Finset (MMP.Mori.PrimeDivisor Y)} {S : MMP.Mori.PrimeDivisor Y}
    {V : IrreducibleCloseds Y} {j : ℕ} {ξ : Valuation Y.functionField ℤᵐ⁰}
    {Θ : MMP.Mori.QDivisor Y}
    (hξ : IsSurfaceEcho sY L S V j ξ) (hΘ : MMP.Fourfold.IsPair sY Θ) (hsupp : Θ.support ⊆ L)
    (hlt : ∀ S' ∈ L, Θ.coeff S' < 1) :
    HasLogDiscrepancy sY Θ ξ (1 + j * (1 - (Θ.coeff S : ℝ))) := by
  classical
  obtain ⟨hY, hdim, hS, hVS, hV, hη, hj, -, x, hx, hecho⟩ := id hξ
  have hηS := hVS (V.isIrreducible.isGenericPoint_genericPoint V.isClosed).mem
  haveI := (mem_oneLabelSmoothLocus_iff.mp hη).1
  obtain ⟨hxm, hx2⟩ := mem_maximalIdeal_notMem_sq_of_regular S hηS
    ((mem_oneLabelSmoothLocus_iff.mp hη).2.1 S hS) hx
  obtain ⟨t, ht⟩ := exists_isRegularSystemOfParameters_pair
    (ringKrullDim_stalk_genericPoint_eq_two hY hdim hV) hxm hx2
  have hd := (hξ.isWeightedMonomialValuation hx ht).hasLogDiscrepancy hΘ
    (fun S' => if S' = S then x else 1) fun S' hS' => by
      split_ifs with h
      · subst h
        exact hx
      · rw [Ideal.span_singleton_one]
        refine (IdealSheafData.stalk_eq_top_iff_notMem_support _ _).mpr fun hη' => h ?_
        exact eq_of_mem_oneLabelSmoothLocus hη (hsupp hS') hS hη' hηS
  convert hd using 1
  obtain ⟨M, hM, hξM⟩ := hecho x fun h => hx2 (h ▸ zero_mem _)
  obtain rfl : M = j := hM.unique (isGreatest_echoIdeal hxm hx2 hj)
  rw [Finset.sum_eq_single S]
  · rw [if_pos rfl, hξM, WithZero.log_exp]
    push_cast
    ring
  · simp +contextual
  · intro h
    rw [Finsupp.notMem_support_iff] at h
    simp [MMP.Mori.DivisorWithCoeffs.coeff_apply, h]

end MMP.Fourfold
