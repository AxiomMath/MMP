module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothCanonical
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
public import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC

/-!
# A divisor of high multiplicity along an lc centre destroys log canonicity

Let `(X, B)` be an lc pair with `ℚ`-coefficients over an algebraically closed field `k` of
characteristic zero, and let `W ⊆ X` be an lc centre of `(X, B)` of dimension `d > 0`: the
centre on `X` of a divisor over `X` of discrepancy `a(E, X, B) = -1`. For a sufficiently general
closed point `x ∈ W` at which `W` is smooth, every effective `ℚ`-Cartier divisor `G` not
containing `W` with `mult_x (G|_W) > d` makes `(X, B + G)` fail to be lc at `x`.

The proof takes a coefficient-one stratum `Z` of a log resolution of `(X, B)` dominating `W`,
and, at a general point of the fibre over `x`, the monomial valuation giving weight one to the
`d` lifted regular parameters of `W`, a large weight `N` to the equations of `Z`, and weight
zero to the vertical parameters. It is divisorial, has log discrepancy `d` with respect to
`(X, B)`, and value `> d` on `G`.

## Main results

* `MMP.Mori.not_isAt_isLcPair_add_of_mem_maximalIdeal_pow_sup`: the statement.

## Implementation notes

The lc centre `W` is an irreducible closed subset of `X` together with a divisor `E` over `X`
whose centre is `W` and whose discrepancy `a(E, X, B)` is `-1`; `E` may be exceptional or a
prime divisor of `X`. Its dimension is the Krull dimension of the subspace `W`.

"Sufficiently general" is an open subset `V` of `X` meeting `W`, chosen before `G`: the
conclusion holds for every closed point `x ∈ W ∩ V` and every `G`. The local ring of the reduced
subscheme `W` at `x` is `𝒪_{X,x}/I_{W,x}`, where `I_{W,x}` is the stalk at `x` of the vanishing
ideal of `W`; at a closed point over the perfect field `k`, `W` is smooth at `x` exactly when
this local ring is regular.

For the multiplicity of `G|_W`: if `q > 0` makes `qG` a Cartier divisor `D` and `g ∈ 𝒪_{X,x}`
is a local equation of `D` at `x`, then the image of `g` in `𝒪_{W,x}` is a local equation of
`qG|_W` (a non-zero-divisor, since `W ⊄ Supp G`), so `mult_x (G|_W) > d` reads
`g ∈ 𝔪_x^{qd+1} + I_{W,x}`. Local equations at `x` differ by units and multiplicity in the
regular local ring `𝒪_{W,x}` is additive, so this does not depend on `q` or on `g`; the
hypothesis asks for one such pair. The pair `(X, B + G)` being lc "over `x`" is lc at `x`,
`MMP.Mori.IsAt`, that is, on some open neighbourhood of `x`.

The proof (`Proof_lem_mmp_lc_bpf_centre_concentration_valuation`) constructs the valuation
algebraically: for a regular local ring `R` with regular system of parameters `x₀, x₁, …, x_c`
and weights `α_i ≥ 1`, the chart algebra `R' = R[x_i / x₀^{α_i}]` is presented by the relations
`x_i - T_i x₀^{α_i}`, so `x₀ R'` is prime and the localization of `R'` at `x₀ R'` is a discrete
valuation ring. On the model `Y` of `E`, at a general point `η` of the fibre of `E → W` over `x`,
the weights are one on the pull-backs of regular parameters of `W` at `x` and `N = qd + 1` on a
local equation of `E`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Definition 2.34
-/

@[expose] public section

universe u

namespace Proof_lem_mmp_lc_bpf_centre_concentration_valuation

open MvPolynomial
open scoped WithZero

section ChartKernel

variable {R : Type*} [CommRing R] {c : ℕ}

/-- The relations `x_i - T_i x₀^{α_i}` of the weighted chart presentation. -/
private noncomputable def chartRel (x0 : R) (x : Fin c → R) (α : Fin c → ℕ) :
    Fin c → MvPolynomial (Fin c) R :=
  fun i => C (x i) - X i * C (x0 ^ α i)

/-- **`x₀` is a nonzerodivisor modulo the chart relations.** If the images of the `x_i` in
`(R/x₀)[T]` are `H₁`-regular and all weights are positive, then `x₀ q ∈ J` forces `q ∈ J`. -/
private theorem mem_span_chartRel_of_C_mul_mem [IsDomain R] {x0 : R} (hx0 : x0 ≠ 0) {x : Fin c → R}
    {α : Fin c → ℕ} (hα : ∀ i, 1 ≤ α i)
    (hH1 : Koszul.IsH1Regular fun i => (C (Ideal.Quotient.mk (Ideal.span {x0}) (x i)) :
      MvPolynomial (Fin c) (R ⧸ Ideal.span {x0})))
    {q : MvPolynomial (Fin c) R}
    (hq : C x0 * q ∈ Ideal.span (Set.range (chartRel x0 x α))) :
    q ∈ Ideal.span (Set.range (chartRel x0 x α)) := by
  classical
  set f := chartRel x0 x α with hf
  set J := Ideal.span (Set.range f) with hJ
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hq
  set I0 : Ideal R := Ideal.span {x0}
  set π : MvPolynomial (Fin c) R →+* MvPolynomial (Fin c) (R ⧸ I0) :=
    MvPolynomial.map (Ideal.Quotient.mk I0)
  set fb : Fin c → MvPolynomial (Fin c) (R ⧸ I0) := fun i => C (Ideal.Quotient.mk I0 (x i))
  have hx0I : Ideal.Quotient.mk I0 x0 = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hπf : ∀ i, π (f i) = fb i := by
    intro i
    simp [f, chartRel, π, fb, hx0I, zero_pow (show α i ≠ 0 by have := hα i; omega)]
  have hsum : ∑ i, π (g i) * fb i = 0 := by
    have := congrArg π hg
    simp only [map_sum, smul_eq_mul, map_mul, hπf] at this
    rw [this]
    simp [π, hx0I]
  have hrel := (Koszul.isH1Regular_iff_forall fb).1 hH1 (fun i => π (g i)) hsum
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hrel
  have hπs : Function.Surjective π :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  choose ct hct using fun p => hπs (cc p)
  set b : Fin c → Fin c → MvPolynomial (Fin c) R := fun l j => ct (j, l) - ct (l, j)
  have hgl : ∀ l, π (g l - ∑ j, b l j * C (x j)) = 0 := by
    intro l
    have h1 : π (g l) = ∑ p : Fin c × Fin c, cc p * Koszul.trivRel fb p.1 p.2 l := by
      have := congrFun hcc l
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this.symm
    rw [map_sub, h1, map_sum]
    simp only [map_mul, map_sub, hct, b]
    simp only [Koszul.trivRel, Pi.sub_apply, Pi.single_apply, mul_sub, mul_ite, mul_zero,
      Fintype.sum_prod_type, Finset.sum_sub_distrib]
    have e1 : ∀ i, (∑ j : Fin c, if l = j then cc (i, j) * fb i else 0) = cc (i, l) * fb i := by
      intro i; simp
    have e2 : (∑ i : Fin c, ∑ j : Fin c, if l = i then cc (i, j) * fb j else 0) =
        ∑ j, cc (l, j) * fb j := by
      simp
    rw [Finset.sum_congr rfl fun i _ => e1 i, e2]
    have e3 : ∀ j, π (C (x j)) = fb j := fun j => by simp [π, fb]
    simp only [e3, sub_mul, Finset.sum_sub_distrib]
    ring
  have hker : ∀ l, ∃ h : MvPolynomial (Fin c) R, g l - ∑ j, b l j * C (x j) = C x0 * h := by
    intro l
    have hmem : g l - ∑ j, b l j * C (x j) ∈ RingHom.ker π := hgl l
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton] at hmem
    obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨h, by rw [← hh, mul_comm]⟩
  choose h hh using hker
  -- the antisymmetric part vanishes
  have hanti : ∑ l, ∑ j, b l j * f j * f l = 0 := by
    simp only [b, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hxf : ∀ j, C (x j) = f j + C x0 * (X j * C (x0 ^ (α j - 1))) := by
    intro j
    have : x0 ^ α j = x0 * x0 ^ (α j - 1) := by
      rw [← pow_succ']; congr 1; have := hα j; omega
    simp only [f, chartRel, this, map_mul]
    ring
  set Q : MvPolynomial (Fin c) R :=
    ∑ l, (∑ j, b l j * (X j * C (x0 ^ (α j - 1))) + h l) * f l
  have hQ : Q ∈ J := Ideal.sum_mem _ fun l _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)
  have hmain : C x0 * q = C x0 * Q := by
    rw [← hg]
    have hgl' : ∀ l, g l = ∑ j, b l j * C (x j) + C x0 * h l := fun l => by
      rw [← hh l]; ring
    simp only [smul_eq_mul, hgl', hxf]
    have : ∀ l, (∑ j, b l j * (f j + C x0 * (X j * C (x0 ^ (α j - 1)))) + C x0 * h l) * f l =
        ∑ j, b l j * f j * f l +
          C x0 * ((∑ j, b l j * (X j * C (x0 ^ (α j - 1))) + h l) * f l) := by
      intro l
      simp only [mul_add, Finset.sum_add_distrib, add_mul, Finset.sum_mul]
      ring_nf
      simp only [Finset.mul_sum, Finset.sum_mul]
      ring_nf
    simp only [this, Finset.sum_add_distrib, hanti, zero_add, ← Finset.mul_sum, Q]
  have hC : C x0 ≠ (0 : MvPolynomial (Fin c) R) := by
    rwa [Ne, MvPolynomial.C_eq_zero]
  rw [mul_left_cancel₀ hC hmain]
  exact hQ

variable (K : Type*) [Field K] [Algebra R K]

/-- The weighted chart map `R[T_1, …, T_c] → K`, `T_i ↦ x_i / x₀^{α_i}`. -/
private noncomputable def chartMap (x0 : R) (x : Fin c → R) (α : Fin c → ℕ) :
    MvPolynomial (Fin c) R →ₐ[R] K :=
  aeval fun i => algebraMap R K (x i) / algebraMap R K x0 ^ α i

variable {K}

private theorem chartMap_chartRel {x0 : R} (hx0 : algebraMap R K x0 ≠ 0) (x : Fin c → R)
    (α : Fin c → ℕ) (i : Fin c) : chartMap K x0 x α (chartRel x0 x α i) = 0 := by
  simp only [chartRel, chartMap, map_sub, map_mul, aeval_C, aeval_X, map_pow]
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hx0), sub_self]

/-- Every polynomial becomes a constant modulo the chart relations after multiplication by a
power of `x₀`. -/
private theorem exists_C_pow_mul_sub_C_mem (x0 : R) (x : Fin c → R) (α : Fin c → ℕ)
    (p : MvPolynomial (Fin c) R) :
    ∃ (M : ℕ) (r : R), C x0 ^ M * p - C r ∈ Ideal.span (Set.range (chartRel x0 x α)) := by
  set J := Ideal.span (Set.range (chartRel x0 x α))
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0, a, by simp⟩
  | add p q hp hq =>
    obtain ⟨M₁, r₁, h₁⟩ := hp
    obtain ⟨M₂, r₂, h₂⟩ := hq
    refine ⟨M₁ + M₂, x0 ^ M₂ * r₁ + x0 ^ M₁ * r₂, ?_⟩
    have : C x0 ^ (M₁ + M₂) * (p + q) - C (x0 ^ M₂ * r₁ + x0 ^ M₁ * r₂) =
        C x0 ^ M₂ * (C x0 ^ M₁ * p - C r₁) + C x0 ^ M₁ * (C x0 ^ M₂ * q - C r₂) := by
      simp only [map_add, map_mul, map_pow]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ h₁) (Ideal.mul_mem_left _ _ h₂)
  | mul_X p n hp =>
    obtain ⟨M, r, h⟩ := hp
    refine ⟨M + α n, r * x n, ?_⟩
    have : C x0 ^ (M + α n) * (p * X n) - C (r * x n) =
        (C x0 ^ M * p - C r) * (X n * C (x0 ^ α n)) + C r * -(chartRel x0 x α n) := by
      simp only [chartRel, map_mul, map_pow]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ h)
      (Ideal.mul_mem_left _ _ (neg_mem (Ideal.subset_span ⟨n, rfl⟩)))

/-- **The kernel of the weighted chart map** is generated by the relations
`x_i - T_i x₀^{α_i}`, when the images of the `x_i` in `(R/x₀)[T]` are `H₁`-regular. -/
private theorem ker_chartMap [IsDomain R] [IsFractionRing R K] {x0 : R} (hx0 : x0 ≠ 0)
    {x : Fin c → R} {α : Fin c → ℕ} (hα : ∀ i, 1 ≤ α i)
    (hH1 : Koszul.IsH1Regular fun i => (C (Ideal.Quotient.mk (Ideal.span {x0}) (x i)) :
      MvPolynomial (Fin c) (R ⧸ Ideal.span {x0}))) :
    RingHom.ker (chartMap K x0 x α) = Ideal.span (Set.range (chartRel x0 x α)) := by
  have hx0K : algebraMap R K x0 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0)
  refine le_antisymm (fun p hp => ?_) (Ideal.span_le.2 ?_)
  · obtain ⟨M, r, h⟩ := exists_C_pow_mul_sub_C_mem x0 x α p
    have hr : r = 0 := by
      have h1 : chartMap K x0 x α (C x0 ^ M * p - C r) = 0 := by
        have := Ideal.span_le.2 (fun _ ⟨i, hi⟩ => hi ▸ chartMap_chartRel hx0K x α i :
          Set.range (chartRel x0 x α) ⊆ (RingHom.ker (chartMap K x0 x α) : Set _))
        exact this h
      rw [map_sub, map_mul, RingHom.mem_ker.1 hp, mul_zero, zero_sub, neg_eq_zero,
        chartMap, aeval_C] at h1
      exact (IsFractionRing.injective R K) (by rw [h1, map_zero])
    rw [hr, map_zero, sub_zero] at h
    clear hr hp
    induction M with
    | zero => simpa using h
    | succ M ih =>
      exact ih (mem_span_chartRel_of_C_mul_mem hx0 hα hH1 (by rw [← mul_assoc, ← pow_succ']; exact h))
  · rintro _ ⟨i, rfl⟩
    exact chartMap_chartRel hx0K x α i

end ChartKernel

section H1

open IsLocalRing RingTheory.Sequence
open scoped Pointwise

/-- **The parameters after the first are `H₁`-regular in `(R/x₀)[T]`.** For a regular system of
parameters `x₀, x₁, …, x_c` of a regular local ring `R`, the images of `x₁, …, x_c` in the
polynomial ring over `R/x₀` form an `H₁`-regular sequence. -/
private theorem isH1Regular_C_mk_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsRegularLocalRing R] {c : ℕ} {z : Fin (c + 1) → R}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    Koszul.IsH1Regular fun i : Fin c => (C (Ideal.Quotient.mk (Ideal.span {z 0}) (z i.succ)) :
      MvPolynomial (Fin c) (R ⧸ Ideal.span {z 0})) := by
  set A := R ⧸ Ideal.span {z 0}
  set rs : List R := List.ofFn fun i : Fin c => z i.succ
  have hofn : List.ofFn z = z 0 :: rs := List.ofFn_succ
  have hgen : Ideal.ofList (List.ofFn z) = maximalIdeal R := by
    rw [Ideal.ofList, ← hz.1]
    congr 1
    ext a
    simp only [List.mem_ofFn, Set.mem_setOf_eq, Set.mem_range]
  have hlen : (List.ofFn z).length = (maximalIdeal R).spanFinrank := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hz.2] at h
    rw [List.length_ofFn]
    exact_mod_cast h.symm
  have hreg := ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
    R).1 _ hgen hlen).1
  rw [hofn, isRegular_cons_iff] at hreg
  have hw : IsWeaklyRegular (QuotSMulTop (z 0) R) rs := hreg.2.toIsWeaklyRegular
  -- `R/(z₀ • R) ≅ R/(z₀)` as `R`-modules
  have hsmul : (z 0 • (⊤ : Submodule R R)) = Ideal.span {z 0} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop (z 0) R ≃ₗ[R] A := Submodule.quotEquivOfEq _ _ hsmul
  have hwA : IsWeaklyRegular A rs := (LinearEquiv.isWeaklyRegular_congr e rs).1 hw
  have hwA' : IsWeaklyRegular A (rs.map (algebraMap R A)) :=
    (isWeaklyRegular_map_algebraMap_iff A A rs).2 hwA
  set M₂ := MvPolynomial (Fin c) A
  have h2 := hwA'.isWeaklyRegular_lTensor (M₂ := M₂)
  have h3 : IsWeaklyRegular M₂ (rs.map (algebraMap R A)) :=
    (LinearEquiv.isWeaklyRegular_congr (TensorProduct.rid A M₂) _).1 h2
  have h4 : IsWeaklyRegular M₂ ((rs.map (algebraMap R A)).map (algebraMap A M₂)) :=
    (isWeaklyRegular_map_algebraMap_iff M₂ M₂ _).2 h3
  have hlist : (rs.map (algebraMap R A)).map (algebraMap A M₂) =
      List.ofFn fun i : Fin c => (C (Ideal.Quotient.mk (Ideal.span {z 0}) (z i.succ)) : M₂) := by
    simp only [rs, List.map_ofFn, List.map_map]
    rfl
  rw [hlist] at h4
  have hK := (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := M₂)).1 h4
  exact ((Koszul.isKoszulRegularOn_self_iff _).1 hK).isH1Regular

end H1

section ChartValuation

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {c : ℕ}
  {x0 : R} {x : Fin c → R} {α : Fin c → ℕ}

/-- If `p(x/x₀^α) = x₀ q(x/x₀^α)`, then all coefficients of `p` lie in the maximal ideal. -/
private theorem mem_map_C_maximalIdeal_of_chartMap_eq (hα : ∀ i, 1 ≤ α i)
    (hx0m : x0 ∈ maximalIdeal R) (hxm : ∀ i, x i ∈ maximalIdeal R)
    (hker : RingHom.ker (chartMap K x0 x α) = Ideal.span (Set.range (chartRel x0 x α)))
    {p q : MvPolynomial (Fin c) R}
    (h : chartMap K x0 x α p = algebraMap R K x0 * chartMap K x0 x α q) :
    p ∈ Ideal.map (C : R →+* MvPolynomial (Fin c) R) (maximalIdeal R) := by
  have hJ : Ideal.span (Set.range (chartRel x0 x α)) ≤
      Ideal.map (C : R →+* MvPolynomial (Fin c) R) (maximalIdeal R) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine sub_mem (Ideal.mem_map_of_mem _ (hxm i)) (Ideal.mul_mem_left _ _
      (Ideal.mem_map_of_mem _ (Ideal.pow_mem_of_mem _ hx0m _ (by have := hα i; omega))))
  have hpq : p - C x0 * q ∈ RingHom.ker (chartMap K x0 x α) := by
    rw [RingHom.mem_ker, map_sub, map_mul, h]
    simp [chartMap]
  rw [hker] at hpq
  have := add_mem (hJ hpq) (Ideal.mul_mem_right q _ (Ideal.mem_map_of_mem C hx0m))
  simpa using this

end ChartValuation

section ChartPrime

open IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {c : ℕ}
  {x0 : R} {x : Fin c → R} {α : Fin c → ℕ}

variable (K x0 x α) in
/-- The ideal `x₀ R'` of the weighted chart algebra `R' = R[x_i / x₀^{α_i}] ⊆ K`. -/
private noncomputable def chartIdeal : Ideal (chartMap K x0 x α).range :=
  Ideal.span {algebraMap R (chartMap K x0 x α).range x0}

omit [IsDomain R] [IsLocalRing R] [IsFractionRing R K] in
private theorem chartMap_C (r : R) : chartMap K x0 x α (C r) = algebraMap R K r := aeval_C _ _

omit [IsDomain R] [IsLocalRing R] [IsFractionRing R K] in
private theorem chartMap_X (i : Fin c) :
    chartMap K x0 x α (X i) = algebraMap R K (x i) / algebraMap R K x0 ^ α i := aeval_X _ _

omit [IsDomain R] [IsLocalRing R] [IsFractionRing R K] in
private theorem coe_rangeRestrict_chartMap (p : MvPolynomial (Fin c) R) :
    ((chartMap K x0 x α).rangeRestrict p : K) = chartMap K x0 x α p := rfl

private theorem rangeRestrict_mem_chartIdeal_iff (hx0 : x0 ≠ 0) (hα : ∀ i, 1 ≤ α i)
    (hm : Ideal.span (insert x0 (Set.range x)) = maximalIdeal R)
    (hker : RingHom.ker (chartMap K x0 x α) = Ideal.span (Set.range (chartRel x0 x α)))
    (p : MvPolynomial (Fin c) R) :
    (chartMap K x0 x α).rangeRestrict p ∈ chartIdeal K x0 x α ↔
      p ∈ Ideal.map (C : R →+* MvPolynomial (Fin c) R) (maximalIdeal R) := by
  have hx0m : x0 ∈ maximalIdeal R := hm ▸ Ideal.subset_span (Set.mem_insert _ _)
  have hxm : ∀ i, x i ∈ maximalIdeal R := fun i =>
    hm ▸ Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hx0K : algebraMap R K x0 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0)
  refine ⟨fun h => ?_, fun hp => ?_⟩
  · obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
    obtain ⟨q, rfl⟩ := (chartMap K x0 x α).rangeRestrict_surjective a
    refine mem_map_C_maximalIdeal_of_chartMap_eq hα hx0m hxm hker (q := q) ?_
    have := congrArg Subtype.val ha
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_rangeRestrict_chartMap] at this
    rw [← this, mul_comm]
  · rw [← hm, Ideal.map_span] at hp
    refine Submodule.span_induction
      (p := fun p _ => (chartMap K x0 x α).rangeRestrict p ∈ chartIdeal K x0 x α) ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨r, hr, rfl⟩
      rw [Set.mem_insert_iff] at hr
      rcases hr with hr | ⟨i, hi⟩
      · rw [hr]
        have h0 : (chartMap K x0 x α).rangeRestrict (C x0) =
            algebraMap R (chartMap K x0 x α).range x0 :=
          (chartMap K x0 x α).rangeRestrict.commutes x0
        rw [h0]
        exact Ideal.mem_span_singleton_self _
      · rw [← hi]
        have hxi : (chartMap K x0 x α).rangeRestrict (C (x i)) =
            algebraMap R (chartMap K x0 x α).range x0 *
              (algebraMap R (chartMap K x0 x α).range x0 ^ (α i - 1) *
                (chartMap K x0 x α).rangeRestrict (X i)) := by
          apply Subtype.ext
          simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_pow,
            coe_rangeRestrict_chartMap, chartMap_C, chartMap_X]
          rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (hα i),
            mul_div_cancel₀ _ (pow_ne_zero _ hx0K)]
        rw [hxi]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · simp
    · intro a b _ _ ha hb
      rw [map_add]; exact add_mem ha hb
    · intro a b _ hb
      rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ hb

private theorem isPrime_chartIdeal (hx0 : x0 ≠ 0) (hα : ∀ i, 1 ≤ α i)
    (hm : Ideal.span (insert x0 (Set.range x)) = maximalIdeal R)
    (hker : RingHom.ker (chartMap K x0 x α) = Ideal.span (Set.range (chartRel x0 x α))) :
    (chartIdeal K x0 x α).IsPrime := by
  have hiff := rangeRestrict_mem_chartIdeal_iff hx0 hα hm hker
  have hker' : RingHom.ker (MvPolynomial.map (residue R) : MvPolynomial (Fin c) R →+* _) =
      Ideal.map (C : R →+* MvPolynomial (Fin c) R) (maximalIdeal R) := by
    rw [MvPolynomial.ker_map, ker_residue]
  refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
  · have h1 : (chartMap K x0 x α).rangeRestrict (C 1) ∈ chartIdeal K x0 x α := by
      rw [htop]; trivial
    rw [hiff, MvPolynomial.mem_map_C_iff] at h1
    have := h1 0
    simp only [MvPolynomial.coeff_C, if_pos rfl] at this
    exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  · obtain ⟨p, rfl⟩ := (chartMap K x0 x α).rangeRestrict_surjective a
    obtain ⟨q, rfl⟩ := (chartMap K x0 x α).rangeRestrict_surjective b
    rw [← map_mul, hiff, ← hker', RingHom.mem_ker, map_mul] at hab
    rcases mul_eq_zero.1 hab with h | h
    · left; rw [hiff, ← hker']; exact h
    · right; rw [hiff, ← hker']; exact h

/-- **The weighted valuation.** Under the hypotheses of `ker_chartMap`, there is a discrete
valuation `v` of `K` with `v(x₀) = exp (-1)`, `v ≤ 1` on the chart algebra, `v < 1` exactly on
the polynomials with coefficients in the maximal ideal, and whose valuation ring consists of the
fractions `p / q` of the chart algebra with `v(q) = 1`. -/
private theorem exists_chartValuation [IsNoetherianRing R] (hx0 : x0 ≠ 0) (hα : ∀ i, 1 ≤ α i)
    (hm : Ideal.span (insert x0 (Set.range x)) = maximalIdeal R)
    (hker : RingHom.ker (chartMap K x0 x α) = Ideal.span (Set.range (chartRel x0 x α))) :
    ∃ v : Valuation K ℤᵐ⁰, v (algebraMap R K x0) = WithZero.exp (-1) ∧
      (∀ p, v (chartMap K x0 x α p) ≤ 1) ∧
      (∀ p, v (chartMap K x0 x α p) < 1 ↔
        p ∈ Ideal.map (C : R →+* MvPolynomial (Fin c) R) (maximalIdeal R)) ∧
      ∀ g, v g ≤ 1 → ∃ p q, v (chartMap K x0 x α q) = 1 ∧
        g = chartMap K x0 x α p / chartMap K x0 x α q := by
  set S := (chartMap K x0 x α).range
  set P := chartIdeal K x0 x α
  haveI hP : P.IsPrime := isPrime_chartIdeal hx0 hα hm hker
  have hiff := rangeRestrict_mem_chartIdeal_iff hx0 hα hm hker
  have hPle : P.primeCompl ≤ nonZeroDivisors S := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero fun h => hs (h ▸ P.zero_mem)
  set B := Localization.subalgebra.ofField K P.primeCompl hPle
  haveI : IsLocalization.AtPrime B P := Localization.subalgebra.isLocalization_ofField K _ hPle
  haveI : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B P
  haveI : IsNoetherianRing S :=
    isNoetherianRing_of_surjective _ _ (chartMap K x0 x α).rangeRestrict.toRingHom
      (chartMap K x0 x α).rangeRestrict_surjective
  haveI : IsNoetherianRing B := IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  have hx0K : algebraMap R K x0 ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0)
  set t : B := algebraMap S B (algebraMap R S x0)
  have htK : algebraMap B K t = algebraMap R K x0 := rfl
  have ht0 : t ≠ 0 := fun h => hx0K (by rw [← htK, h, map_zero])
  have hmax : maximalIdeal B = Ideal.span {t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P B]
    simp only [P, chartIdeal, Ideal.map_span, Set.image_singleton]
    rfl
  have hnf : ¬ IsField B := by
    rw [isField_iff_maximalIdeal_eq, hmax]
    exact fun h => ht0 (Ideal.span_singleton_eq_bot.1 h)
  have hprinc : (maximalIdeal B).IsPrincipal := ⟨⟨t, hmax⟩⟩
  haveI : IsDiscreteValuationRing B :=
    ((IsDiscreteValuationRing.TFAE B hnf).out 1 5).mpr hprinc
  set w := IsDiscreteValuationRing.maximalIdeal B
  set v := w.valuation K
  have hrr : ∀ p, chartMap K x0 x α p =
      algebraMap B K (algebraMap S B ((chartMap K x0 x α).rangeRestrict p)) := fun p => rfl
  have hlt : ∀ p, v (chartMap K x0 x α p) < 1 ↔
      p ∈ Ideal.map (C : R →+* MvPolynomial (Fin c) R) (maximalIdeal R) := by
    intro p
    rw [hrr, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    change _ ∈ maximalIdeal B ↔ _
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff B P, hiff]
  have hle : ∀ p, v (chartMap K x0 x α p) ≤ 1 := fun p => by
    rw [hrr]; exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ _
  refine ⟨v, ?_, hle, hlt, fun g hg => ?_⟩
  · rw [← htK, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ ht0 hmax
  · obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
      K g fun w' => by
        rw [show w' = w from IsDedekindDomain.HeightOneSpectrum.ext
          (eq_maximalIdeal w'.isMaximal)]
        exact hg
    obtain ⟨a, s, hs, hrs⟩ : ∃ (a s : S) (_ : s ∈ P.primeCompl),
        (r : K) = algebraMap S K a * (algebraMap S K s)⁻¹ := r.2
    obtain ⟨p, rfl⟩ := (chartMap K x0 x α).rangeRestrict_surjective a
    obtain ⟨q, rfl⟩ := (chartMap K x0 x α).rangeRestrict_surjective s
    refine ⟨p, q, le_antisymm (hle q) (not_lt.1 fun h => hs ((hiff q).2 ((hlt q).1 h))), ?_⟩
    rw [← hr, div_eq_mul_inv]
    exact hrs

end ChartPrime

section Realization

open CategoryTheory AlgebraicGeometry IsLocalRing MMP.Mori

/-- The local rings of a scheme locally of finite type over a field `k` are essentially of
finite type over `k`. -/
private theorem essFiniteType_stalkAlgebra {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (y : Y) :
    letI := stalkAlgebra sY y
    Algebra.EssFiniteType k (Y.presheaf.stalk y) := by
  letI := stalkAlgebra sY y
  have := (sY.base y).isPrime
  have h0 : (algebraMap k (Localization.AtPrime (sY.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (sY.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of k) (sY.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of k) (sY.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sY.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of k) (x := sY.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  have h2 := h1.comp (LocallyOfFiniteType.stalkMap sY y)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h2 using 1
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom = _
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.germ_stalkMap]
  rfl

/-- **The valuation ring of the weighted valuation is essentially of finite type.** If `v ≤ 1`
on the chart algebra and every `g` with `v(g) ≤ 1` is a fraction `p / q` of the chart algebra
with `v(q) = 1`, then `{g | v g ≤ 1}` is the image of a localization of `R[T]`, a `k`-algebra
essentially of finite type when `R` is. -/
private theorem exists_essFiniteType_range_of_chart {k R K : Type u} [Field k] [CommRing R]
    [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra k R] [Algebra k K]
    [IsScalarTower k R K] [Algebra.EssFiniteType k R] {c : ℕ} {x0 : R} {x : Fin c → R}
    {α : Fin c → ℕ} (v : Valuation K ℤᵐ⁰) (hle : ∀ p, v (chartMap K x0 x α p) ≤ 1)
    (hfrac : ∀ g, v g ≤ 1 → ∃ p q, v (chartMap K x0 x α q) = 1 ∧
      g = chartMap K x0 x α p / chartMap K x0 x α q) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
      (φ : S →ₐ[k] K), ∀ g, v g ≤ 1 ↔ g ∈ φ.range := by
  let N : Submonoid K :=
    { carrier := {g | v g = 1}
      mul_mem' := fun {a b} (ha : v a = 1) (hb : v b = 1) => by
        change v (a * b) = 1
        rw [map_mul, ha, hb, one_mul]
      one_mem' := v.map_one }
  let ψ : MvPolynomial (Fin c) R →+* K := (chartMap K x0 x α).toRingHom
  let Mp : Submonoid (MvPolynomial (Fin c) R) := N.comap ψ
  have hunit : ∀ m : Mp, IsUnit (ψ m) := fun m => isUnit_iff_ne_zero.mpr fun h0 => by
    have h1 : v (ψ m) = 1 := m.2
    rw [h0, map_zero] at h1
    exact zero_ne_one h1
  let S := Localization Mp
  let lift : S →+* K := IsLocalization.lift (M := Mp) (S := S) hunit
  have hlift : ∀ p, lift (algebraMap _ S p) = ψ p := IsLocalization.lift_eq hunit
  haveI : Algebra.EssFiniteType k (MvPolynomial (Fin c) R) := Algebra.EssFiniteType.comp k R _
  let φ : S →ₐ[k] K :=
    { lift with
      commutes' := fun a => by
        change lift (algebraMap k S a) = _
        rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin c) R) S, hlift,
          IsScalarTower.algebraMap_apply k R (MvPolynomial (Fin c) R)]
        change chartMap K x0 x α _ = _
        rw [(chartMap K x0 x α).commutes, ← IsScalarTower.algebraMap_apply] }
  refine ⟨S, inferInstance, inferInstance, inferInstance, φ, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · obtain ⟨p, q, hq, rfl⟩ := hfrac g hg
    refine ⟨IsLocalization.mk' S p (⟨q, hq⟩ : Mp), ?_⟩
    change lift _ = _
    rw [IsLocalization.lift_mk'_spec]
    have hq0 : chartMap K x0 x α q ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hq
      exact zero_ne_one hq
    change chartMap K x0 x α p = chartMap K x0 x α q * _
    rw [mul_div_cancel₀ _ hq0]
  · rintro ⟨s, rfl⟩
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective Mp s
    have h := (IsLocalization.lift_mk'_spec (S := S) (g := ψ) hunit p
      (lift (IsLocalization.mk' S p q)) q).mp rfl
    have hq : v (ψ q) = 1 := q.2
    have h2 := congrArg v h
    rw [map_mul, hq, one_mul] at h2
    change v (lift _) ≤ 1
    rw [← h2]
    exact hle p

end Realization

section TopFormsGenerator

open IsLocalRing KaehlerDifferential TensorProduct

/-- If the differentials `dz₁, …, dzₙ` span `Ω_{B/k}` for a domain `B` whose fraction field `K`
has `dim_K Ω_{K/k} = n`, then `dz₁ ∧ ⋯ ∧ dzₙ` generates `Ω^n_{B/k}` and has nonzero image in
`Ω^n_{K/k}`. -/
private theorem span_ιMulti_D_eq_top {k B K : Type*} [CommRing k] [CommRing B] [IsDomain B]
    [Field K] [Algebra k B] [Algebra k K] [Algebra B K] [IsScalarTower k B K]
    [IsFractionRing B K] {n : ℕ} (z : Fin n → B)
    (hz : Submodule.span B (Set.range fun i => D k B (z i)) = ⊤)
    (hn : Module.finrank K Ω[K⁄k] = n) :
    Submodule.span B {exteriorPower.ιMulti B n (fun i => D k B (z i))} = ⊤ ∧
      MMP.Mori.topFormsMap k B K n (exteriorPower.ιMulti B n (fun i => D k B (z i))) ≠ 0 := by
  let zK : Fin n → Ω[K⁄k] := fun i => KaehlerDifferential.map k k B K (D k B (z i))
  have hspanK : Submodule.span K (Set.range zK) = ⊤ := by
    have hs := KaehlerDifferential.span_range_map_derivation_of_isLocalization k B K
      (nonZeroDivisors B)
    refine eq_top_iff.mpr (hs.symm.le.trans (Submodule.span_le.mpr ?_))
    rintro _ ⟨b, rfl⟩
    have hb : D k B b ∈ Submodule.span B (Set.range fun i => D k B (z i)) := hz ▸ Submodule.mem_top
    have : KaehlerDifferential.map k k B K (D k B b) ∈
        (Submodule.span K (Set.range zK)).restrictScalars B := by
      refine Submodule.span_induction (p := fun w _ => KaehlerDifferential.map k k B K w ∈
        (Submodule.span K (Set.range zK)).restrictScalars B) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
      · simp
      · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
      · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha
    exact this
  have hliK : LinearIndependent K zK :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanK.ge (by simp [hn])
  have hliB : LinearIndependent B fun i => D k B (z i) :=
    (hliK.restrict_scalars' (R := B)).of_comp
      ((KaehlerDifferential.map k k B K).restrictScalars B)
  let b := Module.Basis.mk hliB hz.ge
  have hb : ⇑b = fun i => D k B (z i) := Module.Basis.coe_mk _ _
  refine ⟨?_, ?_⟩
  · refine eq_top_iff.mpr fun w _ => ?_
    obtain ⟨r, hr⟩ := (MMP.Intersection.bijective_smul_ιMulti_basis b).2 w
    rw [← hr, ← hb]
    exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self _)
  · rw [MMP.Mori.topFormsMap_ιMulti]
    let bK := Module.Basis.mk hliK hspanK.ge
    have hbK : ⇑bK = zK := Module.Basis.coe_mk _ _
    intro h0
    have := (MMP.Intersection.bijective_smul_ιMulti_basis bK).1
      (a₁ := 1) (a₂ := 0) (by simpa only [hbK, one_smul, zero_smul] using h0)
    exact one_ne_zero this

/-- **Nakayama with the conormal sequence.** In a local ring `B` with `Ω_{B/k}` finite, if the
`pᵢ` generate the maximal ideal and the differentials of the residues of the `qᵢ` span
`Ω_{κ/k}`, then the `dpᵢ` and `dqᵢ` span `Ω_{B/k}`. -/
private theorem span_D_eq_top_of_residue {k B : Type*} [CommRing k] [CommRing B] [IsLocalRing B]
    [Algebra k B] [Module.Finite B Ω[B⁄k]] {ι₁ ι₂ : Type*} [Fintype ι₂] (p : ι₁ → B)
    (q : ι₂ → B) (hp : Ideal.span (Set.range p) = maximalIdeal B)
    (hq : Submodule.span (ResidueField B)
      (Set.range fun i => D k (ResidueField B) (residue B (q i))) = ⊤) :
    Submodule.span B (Set.range (fun i => D k B (p i)) ∪ Set.range (fun i => D k B (q i))) =
      ⊤ := by
  classical
  set N := Submodule.span B (Set.range (fun i => D k B (p i)) ∪ Set.range (fun i => D k B (q i)))
  let κ := ResidueField B
  rw [← IsLocalRing.map_tensorProduct_mk_eq_top]
  set T := N.map (TensorProduct.mk B κ Ω[B⁄k] 1)
  have hT : ∀ y ∈ N, (1 : κ) ⊗ₜ[B] y ∈ T := fun y hy => ⟨y, hy, rfl⟩
  have hTκ : ∀ (c : κ) (w : κ ⊗[B] Ω[B⁄k]), w ∈ T → c • w ∈ T := by
    intro c w hw
    obtain ⟨a, rfl⟩ := residue_surjective c
    rw [show (residue B a) • w = a • w from algebraMap_smul κ a w]
    exact Submodule.smul_mem _ a hw
  -- `1 ⊗ dm ∈ T` for `m ∈ 𝔪`
  have hm : ∀ m ∈ maximalIdeal B, (1 : κ) ⊗ₜ[B] D k B m ∈ T := by
    intro m hm
    rw [← hp] at hm
    refine Submodule.span_induction (p := fun m _ => (1 : κ) ⊗ₜ[B] D k B m ∈ T) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨i, rfl⟩; exact hT _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩))
    · simp
    · intro a b _ _ ha hb; rw [map_add, tmul_add]; exact add_mem ha hb
    · intro a b hb ih
      have hb0 : residue B b = 0 := by
        rwa [residue_eq_zero_iff, ← hp]
      rw [smul_eq_mul, Derivation.leibniz, tmul_add, tmul_smul, tmul_smul]
      refine add_mem (Submodule.smul_mem _ a ih) ?_
      rw [smul_tmul', show b • (1 : κ) = residue B b from by
        rw [Algebra.smul_def, mul_one]; rfl, hb0, zero_tmul]
      exact zero_mem _
  refine eq_top_iff.mpr fun w _ => ?_
  have hw : mapBaseChange k B κ w ∈ Submodule.span κ
      (Set.range fun i => D k κ (residue B (q i))) := hq ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun κ).mp hw
  set w' : κ ⊗[B] Ω[B⁄k] := ∑ i, c i • ((1 : κ) ⊗ₜ[B] D k B (q i))
  have hw'T : w' ∈ T := Submodule.sum_mem _ fun i _ =>
    hTκ _ _ (hT _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))
  have hker : mapBaseChange k B κ (w - w') = 0 := by
    simp only [w', map_sub, map_sum, map_smul, mapBaseChange_tmul, one_smul,
      KaehlerDifferential.map_D, ← hc]
    exact sub_self _
  obtain ⟨c', hc'⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k B κ
    residue_surjective (w - w')).mp hker
  obtain ⟨⟨m, hmk⟩, rfl⟩ := Ideal.toCotangent_surjective _ c'
  rw [kerCotangentToTensor_toCotangent] at hc'
  have hmm : m ∈ maximalIdeal B := (residue_eq_zero_iff m).mp hmk
  have := add_mem (hm m hmm) hw'T
  rwa [show (1 : κ) ⊗ₜ[B] D k B m = w - w' from hc', sub_add_cancel] at this

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- In characteristic zero, the differentials of a transcendence basis span `Ω_{L/k}`: `L` is
separable algebraic over `k(w)`, so `Ω_{L/k(w)} = 0`. -/
private theorem span_D_eq_top_of_isTranscendenceBasis {k L : Type*} [Field k] [CharZero k]
    [Field L] [Algebra k L] {ι : Type*} {w : ι → L} (hw : IsTranscendenceBasis k w) :
    Submodule.span L (Set.range fun i => D k L (w i)) = ⊤ := by
  classical
  set M := Submodule.span L (Set.range fun i => D k L (w i))
  let S := Algebra.adjoin k (Set.range w)
  let F := IntermediateField.adjoin k (Set.range w)
  have : Algebra.IsAlgebraic F L := hw.isAlgebraic_field
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap k F).injective
  have : Algebra.IsSeparable F L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  have hS : ∀ s ∈ S, D k L s ∈ M := by
    intro s hs
    refine Algebra.adjoin_induction (p := fun s _ => D k L s ∈ M) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩
    · intro c; simp
    · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
    · intro a b _ _ ha hb
      rw [Derivation.leibniz]
      exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  have hF : ∀ ω : Ω[F⁄k], KaehlerDifferential.map k k F L ω ∈ M := by
    intro ω
    have hω : ω ∈ Submodule.span F (Set.range
        (⇑(KaehlerDifferential.map k k S F) ∘ ⇑(D k S))) := by
      rw [KaehlerDifferential.span_range_map_derivation_of_isLocalization k S F
        (nonZeroDivisors S)]
      trivial
    refine Submodule.span_induction
      (p := fun ω _ => KaehlerDifferential.map k k F L ω ∈ M) ?_ ?_ ?_ ?_ hω
    · rintro _ ⟨s, rfl⟩
      simp only [Function.comp_apply, KaehlerDifferential.map_D]
      exact hS _ s.2
    · simp
    · intro a b _ _ ha hb; rw [map_add]; exact add_mem ha hb
    · intro a b _ hb
      rw [map_smul, ← algebraMap_smul L]
      exact Submodule.smul_mem _ _ hb
  rw [eq_top_iff]
  rintro x -
  have hx : x ∈ LinearMap.ker (KaehlerDifferential.map k F L L) := Subsingleton.elim _ _
  rw [← KaehlerDifferential.range_mapBaseChange] at hx
  obtain ⟨y, rfl⟩ := hx
  induction y with
  | tmul a ω =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    exact Submodule.smul_mem _ a (hF ω)
  | add y y' hy hy' => rw [map_add]; exact add_mem hy hy'

/-- **A generator of the top forms from parameters and a transcendence basis.** Let `B` be a
local domain over a field `k` of characteristic zero, with `Ω_{B/k}` finite and fraction field
`K` with `dim_K Ω_{K/k} = n`. If `n` elements `z` of `B` contain generators `p` of the maximal
ideal and lifts `q` of a transcendence basis of the residue field, `dz₁ ∧ ⋯ ∧ dzₙ` generates
`Ω^n_{B/k}` with nonzero image in `Ω^n_{K/k}`. -/
private theorem span_ιMulti_D_eq_top_of_residue {k B K : Type*} [Field k] [CharZero k]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Field K] [Algebra k B] [Algebra k K]
    [Algebra B K] [IsScalarTower k B K] [IsFractionRing B K] [Module.Finite B Ω[B⁄k]]
    {n : ℕ} (z : Fin n → B) {ι₁ ι₂ : Type*} [Fintype ι₂] (p : ι₁ → B) (q : ι₂ → B)
    (hpz : Set.range p ⊆ Set.range z) (hqz : Set.range q ⊆ Set.range z)
    (hp : Ideal.span (Set.range p) = IsLocalRing.maximalIdeal B)
    (hq : IsTranscendenceBasis k fun i => IsLocalRing.residue B (q i))
    (hn : Module.finrank K Ω[K⁄k] = n) :
    Submodule.span B {exteriorPower.ιMulti B n (fun i => D k B (z i))} = ⊤ ∧
      MMP.Mori.topFormsMap k B K n (exteriorPower.ιMulti B n (fun i => D k B (z i))) ≠ 0 := by
  refine span_ιMulti_D_eq_top z (eq_top_iff.mpr ?_) hn
  rw [← span_D_eq_top_of_residue (k := k) p q hp (span_D_eq_top_of_isTranscendenceBasis hq)]
  refine Submodule.span_mono (Set.union_subset ?_ ?_)
  · rintro _ ⟨i, rfl⟩
    obtain ⟨l, hl⟩ := hpz ⟨i, rfl⟩
    exact ⟨l, by simp [hl]⟩
  · rintro _ ⟨i, rfl⟩
    obtain ⟨l, hl⟩ := hqz ⟨i, rfl⟩
    exact ⟨l, by simp [hl]⟩

end TopFormsGenerator

/-! ### Stalks of a variety -/

section Stalks

open CategoryTheory AlgebraicGeometry MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- **Dimension formula.** On an irreducible scheme of dimension `n` locally of finite type over
`k`, `trdeg_k κ(x) + dim 𝒪_{X,x} = n`. -/
private theorem trdeg_residueField_stalk [IrreducibleSpace X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (x : X) {d : ℕ}
    (hd : ringKrullDim (X.presheaf.stalk x) = d) :
    letI := stalkAlgebra sX x
    Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x)) = ((n - d : ℕ) : Cardinal) ∧
      d ≤ n := by
  let := stalkAlgebra sX x
  have h := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X sX x
  rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x, hn, hd] at h
  have h' : (n : WithBot ℕ∞) = (Cardinal.toENat
      (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x))) : WithBot ℕ∞) + d := h
  generalize hT : Cardinal.toENat
      (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x))) = T at h'
  induction T using ENat.recTopCoe with
  | top =>
    have : (n : ℕ∞) = ⊤ + d := by exact_mod_cast h'
    simp at this
  | coe e =>
    have he : n = e + d := by exact_mod_cast h'
    refine ⟨?_, by omega⟩
    rw [show n - d = e by omega]
    exact Cardinal.toENat_eq_natCast.mp hT

/-- A transcendence basis of a field of finite transcendence degree `r`, indexed by `Fin r`. -/
private theorem exists_isTranscendenceBasis_fin {k L : Type*} [Field k] [Field L] [Algebra k L]
    {r : ℕ} (hr : Algebra.trdeg k L = r) : ∃ w : Fin r → L, IsTranscendenceBasis k w := by
  have : FaithfulSMul k L :=
    (faithfulSMul_iff_algebraMap_injective k L).mpr (algebraMap k L).injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  have hcard : Cardinal.mk s = r := hs.cardinalMk_eq_trdeg.trans hr
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hcard
  let w : Fin r → L := fun i => (e.symm i : L)
  have hinj : Function.Injective w := Subtype.val_injective.comp e.symm.injective
  have hrange : Set.range w = s := by
    ext a
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (e.symm i).2, fun ha => ⟨e ⟨a, ha⟩, by simp [w]⟩⟩
  exact ⟨w, (isTranscendenceBasis_subtype_range hinj).mp (hrange ▸ hs)⟩

/-- The degree of the rational top forms: `dim_{k(X)} Ω_{k(X)/k} = dim X`, over a perfect field. -/
private theorem finrank_kaehlerDifferential_functionField [PerfectField k] [IsIntegral X]
    [LocallyOfFiniteType sX] {n : ℕ} (hn : topologicalKrullDim X = n) :
    letI := functionFieldAlgebra sX
    Module.finrank X.functionField Ω[X.functionField⁄k] = n := by
  let := functionFieldAlgebra sX
  have := essFiniteType_functionField (sX := sX)
  exact (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn)

/-- An element of `𝒪_{Y,E}` of valuation `exp (-1)` generates the maximal ideal. -/
private theorem maximalIdeal_eq_span_of_divisorialValuation_eq {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : MMP.Mori.PrimeDivisor Y) {b : E.localRing}
    (hb : E.divisorialValuation (algebraMap E.localRing Y.functionField b) = WithZero.exp (-1)) :
    IsLocalRing.maximalIdeal E.localRing = Ideal.span {b} := by
  have := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hb
    exact WithZero.exp_ne_zero hb.symm
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hu : E.divisorialValuation (algebraMap E.localRing Y.functionField u) = 1 := by
    refine le_antisymm ((E.divisorialValuation_le_one_iff _).mpr ⟨_, rfl⟩) ?_
    refine not_lt.mp fun h => ?_
    exact (IsLocalRing.notMem_maximalIdeal.mpr u.isUnit)
      ((E.divisorialValuation_algebraMap_lt_one_iff _).mp h)
  rw [map_mul, map_mul, hu, one_mul, map_pow, map_pow,
    E.divisorialValuation_algebraMap_of_irreducible hϖ, ← WithZero.exp_nsmul] at hb
  have hm : m = 1 := by
    have := WithZero.exp_injective hb
    simp at this
    omega
  subst hm
  rw [pow_one, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.span_singleton_mul_left_unit u.isUnit]

open Classical in
/-- **The order of a local equation of a prime divisor.** If `g` generates the ideal of a prime
divisor `S` in `𝒪_{Y,x}`, then `g ≠ 0` in `k(Y)`, and along a prime divisor `Γ` through `x` the
order of `g` is `1` if `Γ = S` and `0` otherwise. -/
private theorem ord_algebraMap_of_stalk_eq_span {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {x : Y} (S Γ : MMP.Mori.PrimeDivisor Y)
    (hΓ : x ∈ Γ.support) {g : Y.presheaf.stalk x}
    (hg : IdealSheafData.stalk S.idealSheaf x = Ideal.span {g}) :
    algebraMap (Y.presheaf.stalk x) Y.functionField g ≠ 0 ∧
      Y.ord (algebraMap (Y.presheaf.stalk x) Y.functionField g) Γ.genericPoint =
        if Γ = S then 1 else 0 := by
  have hsp := MMP.Resolution.Aux.genericPoint_specializes_of_mem_support Γ hΓ
  have := Γ.isDiscreteValuationRing_localRing
  set a := (Y.presheaf.stalkSpecializes hsp).hom g with ha
  have hga : algebraMap (Y.presheaf.stalk x) Y.functionField g =
      algebraMap Γ.localRing Y.functionField a := (MMP.Mori.algebraMap_stalkSpecializes hsp g).symm
  have hI : IdealSheafData.stalk S.idealSheaf Γ.genericPoint = Ideal.span {a} := by
    rw [MMP.Resolution.Aux.stalk_eq_map_stalkSpecializes _ hsp, hg, Ideal.map_span,
      Set.image_singleton]
  rw [hga]
  by_cases hΓS : Γ = S
  · subst hΓS
    rw [ite_eq_left rfl]
    rw [MMP.Resolution.Aux.stalk_idealSheaf_genericPoint] at hI
    have hirr : Irreducible a := (IsDiscreteValuationRing.irreducible_iff_uniformizer a).mpr hI
    have hne : algebraMap Γ.localRing Y.functionField a ≠ 0 := by
      intro h0
      have := IsFractionRing.injective Γ.localRing Y.functionField (h0.trans (map_zero _).symm)
      exact hirr.ne_zero this
    refine ⟨hne, ?_⟩
    have h1 := Γ.divisorialValuation_algebraMap_of_irreducible hirr
    rw [Γ.divisorialValuation_eq_exp_neg_ord hne] at h1
    have := WithZero.exp_injective h1
    omega
  · rw [ite_eq_right hΓS]
    have hnot : Γ.genericPoint ∉ S.support := by
      intro hmem
      exact hΓS (MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes
        (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support S hmem)).symm
    rw [MMP.Intersection.stalk_idealSheaf_eq_top_of_notMem_support S hnot, eq_comm,
      Ideal.span_singleton_eq_top] at hI
    exact ⟨(hI.map _).ne_zero, Γ.ord_algebraMap_of_isUnit hI⟩

end Stalks

section Birational

open CategoryTheory AlgebraicGeometry MMP.Mori

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

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{u}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hU : Dense (U : Set X) := U.2.dense hne
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hle₁ : U ≤ U₁ := inf_le_left
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE hle₁ ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by rw [this]; infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U hU

end Birational

section ChartModel

open IsLocalRing MvPolynomial

variable {R : Type*} [CommRing R] [IsRegularLocalRing R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- **The weighted chart valuation at a regular system of parameters.** For a regular system of
parameters `z₀, z₁, …, z_c` of a regular local ring `R` and weights `α_i ≥ 1`, the chart valuation
of `exists_chartValuation` exists: `v(z₀) = exp (-1)`, `v ≤ 1` on the chart algebra
`R[z_i / z₀^{α_i}]`, `v < 1` exactly on the polynomials with coefficients in the maximal ideal, and
the valuation ring consists of the fractions of the chart algebra with denominator of value `1`. -/
private theorem exists_chartValuation_of_isRegularSystemOfParameters {c : ℕ}
    {z : Fin (c + 1) → R} (hz : MMP.Mori.IsRegularSystemOfParameters z) {α : Fin c → ℕ}
    (hα : ∀ i, 1 ≤ α i) :
    ∃ v : Valuation K ℤᵐ⁰, v (algebraMap R K (z 0)) = WithZero.exp (-1) ∧
      (∀ p, v (chartMap K (z 0) (fun i => z i.succ) α p) ≤ 1) ∧
      (∀ p, v (chartMap K (z 0) (fun i => z i.succ) α p) < 1 ↔
        p ∈ Ideal.map (C : R →+* MvPolynomial (Fin c) R) (maximalIdeal R)) ∧
      ∀ g, v g ≤ 1 → ∃ p q, v (chartMap K (z 0) (fun i => z i.succ) α q) = 1 ∧
        g = chartMap K (z 0) (fun i => z i.succ) α p /
          chartMap K (z 0) (fun i => z i.succ) α q := by
  have : IsDomain R := IsRegularLocalRing.isDomain R
  have : IsNoetherianRing R := inferInstance
  have hz0 : z 0 ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz 0
  have hm : Ideal.span (insert (z 0) (Set.range fun i : Fin c => z i.succ)) =
      maximalIdeal R := by
    rw [← hz.1, ← Fin.range_cons]
    congr 2
    exact Fin.cons_self_tail z
  have hker := ker_chartMap (K := K) hz0 hα (isH1Regular_C_mk_of_isRegularSystemOfParameters hz)
  exact exists_chartValuation hz0 hα hm hker

end ChartModel

section ChartWedge

open KaehlerDifferential

/-- **The pull-back of `dz₀ ∧ ⋯ ∧ dz_c ∧ ω` to the weighted chart.** If `z_i = T_i t^{α_i}` for
`i ≥ 1` and `z₀ = t`, then `dt ∧ d(T₁t^{α₁}) ∧ ⋯ ∧ d(T_ct^{α_c}) ∧ ω` is `t^{∑ α_i}` times
`dt ∧ dT₁ ∧ ⋯ ∧ dT_c ∧ ω`, since `d(T_i t^{α_i}) = t^{α_i} dT_i + α_i T_i t^{α_i - 1} dt`. -/
private theorem ιMulti_append_cons_D_mul_pow {k B : Type*} [CommRing k] [CommRing B]
    [Algebra k B] {c r : ℕ} (t : B) (T : Fin c → B) (α : Fin c → ℕ) (w : Fin r → Ω[B⁄k]) :
    exteriorPower.ιMulti B (c + 1 + r)
        (Fin.append (Fin.cons (D k B t) fun i => D k B (T i * t ^ α i)) w) =
      t ^ (∑ i, α i) • exteriorPower.ιMulti B (c + 1 + r)
        (Fin.append (Fin.cons (D k B t) fun i => D k B (T i)) w) := by
  classical
  set v : Fin (c + 1 + r) → Ω[B⁄k] := Fin.append (Fin.cons (D k B t) fun i => D k B (T i)) w
    with hv
  set ℓ : Fin (c + 1 + r) := Fin.castAdd r 0 with hℓdef
  set S : Finset (Fin (c + 1 + r)) :=
    Finset.univ.map ((Fin.succEmb c).trans (Fin.castAddEmb r)) with hS
  set a : Fin (c + 1 + r) → B :=
    Fin.append (Fin.cons 0 fun i => T i * ((α i : B) * t ^ (α i - 1))) 0 with ha
  set b : Fin (c + 1 + r) → B := Fin.append (Fin.cons 1 fun i => t ^ α i) 1 with hb
  have hmemS : ∀ j, j ∈ S ↔ ∃ i : Fin c, j = Fin.castAdd r i.succ := by
    intro j
    simp only [hS, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
      Fin.coe_succEmb, Fin.coe_castAddEmb]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  have hℓ : ℓ ∉ S := by
    rw [hmemS]
    rintro ⟨i, hi⟩
    have := Fin.castAdd_injective _ _ hi
    exact Fin.succ_ne_zero i this.symm
  have key := MMP.Threefold.Resolution.alternatingMap_apply_ite_smul_add (exteriorPower.ιMulti B (c + 1 + r)) v ℓ a b S hℓ
  have hprod : ∏ i ∈ S, b i = t ^ ∑ i, α i := by
    rw [hS, Finset.prod_map, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [hb, Fin.append_left]
  rw [hprod] at key
  rw [← key]
  congr 1
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · refine Fin.cases ?_ (fun i => ?_) j
    · have h0 : Fin.castAdd r (0 : Fin (c + 1)) ∉ S := hℓ
      rw [if_neg h0]
      simp [hv, Fin.append_left]
    · have hi : Fin.castAdd r i.succ ∈ S := (hmemS _).2 ⟨i, rfl⟩
      rw [if_pos hi]
      simp only [hv, ha, hb, hℓdef, Fin.append_left, Fin.cons_succ, Fin.cons_zero]
      rw [Derivation.leibniz, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul B, smul_smul,
        smul_smul]
      congr 2
      ring
  · have hj : Fin.natAdd (c + 1) j ∉ S := by
      rw [hmemS]
      rintro ⟨i, hi⟩
      have := congrArg Fin.val hi
      simp only [Fin.coe_natAdd, Fin.coe_castAdd, Fin.val_succ] at this
      have := i.2
      omega
    rw [if_neg hj]
    simp [hv, Fin.append_right]

end ChartWedge

section Residue

open IsLocalRing MvPolynomial

/-- **The chart coordinates have algebraically independent residues.** Let `R → B` be a local
homomorphism of local rings and `T_i ∈ B` such that a polynomial `P` over `R` with
`P(T) ∈ 𝔪_B` has all its coefficients in `𝔪_R`. Then the residues of the `T_i` are algebraically
independent over the residue field of `R`. -/
private theorem algebraicIndependent_residue_of_eval₂_mem {R B : Type*} [CommRing R]
    [IsLocalRing R] [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    {c : ℕ} (T : Fin c → B)
    (h : ∀ P : MvPolynomial (Fin c) R, eval₂ (algebraMap R B) T P ∈ maximalIdeal B →
      P ∈ Ideal.map (C : R →+* MvPolynomial (Fin c) R) (maximalIdeal R)) :
    AlgebraicIndependent (ResidueField R) (fun i => residue B (T i)) := by
  rw [algebraicIndependent_iff]
  intro P hP
  obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective (residue R) residue_surjective P
  have key : (aeval (fun i => residue B (T i))).toRingHom.comp (MvPolynomial.map (residue R)) =
      (residue B).comp (eval₂Hom (algebraMap R B) T) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [IsLocalRing.ResidueField.algebraMap_residue]
    · simp
  have hP' : residue B (eval₂ (algebraMap R B) T P) = 0 := by
    have := DFunLike.congr_fun key P
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, coe_eval₂Hom] at this
    rw [← this]
    exact hP
  have hm := h P ((residue_eq_zero_iff _).mp hP')
  rw [MvPolynomial.mem_map_C_iff] at hm
  ext m
  rw [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (residue_eq_zero_iff _).mpr (hm m)

end Residue

section WeightedDivisor

open CategoryTheory AlgebraicGeometry MMP.Mori IsLocalRing KaehlerDifferential MvPolynomial

/-- A model `Y'` of a divisor over a variety `Y` has the dimension of `Y`. -/
private theorem topologicalKrullDim_divisorOver_Y {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] (hY : IsNormalVariety k sY) {n : ℕ}
    (hn : topologicalKrullDim Y = n) (D : DivisorOver k sY) :
    topologicalKrullDim D.Y = n := by
  have := D.isIntegral
  have := D.isDominant
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sY) := D.isNormalVariety.1.toLocallyOfFiniteType
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (D.f ≫ sY)
  have hφ := D.isBirationalMorphism.functionFieldMap_bijective
  let := functionFieldMapAlgebra D.f
  have := isScalarTower_functionFieldMap sY D.f
  have htrK : Algebra.trdeg k Y.functionField = Algebra.trdeg k D.Y.functionField :=
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom k Y.functionField D.Y.functionField)
      hφ).trdeg_eq
  rw [← toENat_trdeg_functionField (sX := D.f ≫ sY), ← htrK,
    toENat_trdeg_functionField (sX := sY), hn]

/-- The residue field of a prime divisor `E` on a model of a variety `Y` of dimension `n + 1` has
transcendence degree `n`. -/
private theorem trdeg_residueField_localRing_divisorOver {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] (hY : IsNormalVariety k sY) {n : ℕ}
    (hn : topologicalKrullDim Y = (n + 1 : ℕ)) (D : DivisorOver k sY) :
    letI := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
    Algebra.trdeg k (ResidueField D.E.localRing) = n := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have : LocallyOfFiniteType (D.f ≫ sY) := D.isNormalVariety.1.toLocallyOfFiniteType
  have hnY := topologicalKrullDim_divisorOver_Y hY hn D
  have := D.E.isDiscreteValuationRing_localRing
  have hdB : ringKrullDim D.E.localRing = (1 : ℕ) := by
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one]; rfl
  obtain ⟨htrB, -⟩ := trdeg_residueField_stalk (D.f ≫ sY) hnY D.E.genericPoint hdB
  rw [htrB, Nat.add_sub_cancel]

/-- The valuation of a divisor over `Y` on the image of `𝒪_{Y,f(η_E)}` in `𝒪_{Y',E}`. -/
private theorem divisorialValuation_algebraMap_stalkMap {k : Type u} [Field k] {Y : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] (D : DivisorOver k sY) [IsIntegral D.Y]
    [IsLocallyNoetherian D.Y] [IsNormal D.Y] (a : Y.presheaf.stalk (D.f D.E.genericPoint)) :
    letI := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
    D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField
        (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing a)) =
      D.valuation (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) Y.functionField a) := by
  have := D.isDominant
  have hWf : ∀ g, D.E.divisorialValuation (functionFieldMap D.f g) = D.valuation g :=
    fun g => rfl
  rw [← hWf]
  change D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField
    ((D.f.stalkMap D.E.genericPoint).hom a)) = _
  rw [← MMP.Mori.functionFieldMap_algebraMap_stalk]

/-- **The chart coordinates along a divisor with a weighted valuation.** In the setting of
`exists_topForms_ordPullback_eq_of_valuation`, the quotients `T_i = z_i / z₀^{α_i}` lie in the
local ring `𝒪_{Y',E}`, and their residues together with the images of lifts `y_j` of a
transcendence basis of `κ(p)` form a transcendence basis of `κ(E)`. -/
private theorem exists_chartCoords_isTranscendenceBasis {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    (hY : IsNormalVariety k sY) {c r : ℕ} (hn : topologicalKrullDim Y = (c + 1 + r : ℕ))
    (D : DivisorOver k sY) [IsIntegral D.Y] [IsLocallyNoetherian D.Y] [IsNormal D.Y]
    [IsRegularLocalRing (Y.presheaf.stalk (D.f D.E.genericPoint))]
    {z : Fin (c + 1) → Y.presheaf.stalk (D.f D.E.genericPoint)} {α : Fin c → ℕ}
    (hv0 : D.valuation (algebraMap _ Y.functionField (z 0)) = WithZero.exp (-1))
    (hvz : ∀ i, D.valuation (algebraMap _ Y.functionField (z i.succ)) =
      WithZero.exp (-(α i : ℤ)))
    (hvlt : ∀ P, D.valuation (chartMap Y.functionField (z 0) (fun i => z i.succ) α P) < 1 →
      P ∈ Ideal.map (C : _ →+* MvPolynomial (Fin c) _)
        (maximalIdeal (Y.presheaf.stalk (D.f D.E.genericPoint))))
    {y : Fin r → Y.presheaf.stalk (D.f D.E.genericPoint)}
    (hyb : letI := stalkAlgebra sY (D.f D.E.genericPoint)
      IsTranscendenceBasis k (fun i => residue (Y.presheaf.stalk (D.f D.E.genericPoint)) (y i))) :
    letI := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
    letI := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
    ∃ T : Fin c → D.E.localRing,
      (∀ i, algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z i.succ) =
        T i * algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z 0) ^ α i) ∧
      IsTranscendenceBasis k fun i => residue D.E.localRing (Sum.elim T
        (fun j => algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (y j)) i) := by
  classical
  let := stalkAlgebra sY (D.f D.E.genericPoint)
  have := D.isDominant
  let := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
  let := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sY D.f D.E.genericPoint
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing) :=
    inferInstanceAs (IsLocalHom (D.f.stalkMap D.E.genericPoint).hom)
  have hWf : ∀ g, D.E.divisorialValuation (functionFieldMap D.f g) = D.valuation g :=
    fun g => rfl
  have hWv := divisorialValuation_algebraMap_stalkMap D
  have hWt : D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField
      (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z 0))) =
      WithZero.exp (-1) :=
    (hWv _).trans hv0
  have htK0 : algebraMap D.E.localRing D.Y.functionField
      (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z 0)) ≠ 0 :=
    fun h0 => by
      rw [h0, map_zero] at hWt
      exact WithZero.exp_ne_zero hWt.symm
  have hT : ∀ i, ∃ T : D.E.localRing, algebraMap D.E.localRing D.Y.functionField T =
      algebraMap D.E.localRing D.Y.functionField
        (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z i.succ)) /
        algebraMap D.E.localRing D.Y.functionField
          (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z 0)) ^ α i := by
    intro i
    refine (D.E.divisorialValuation_le_one_iff _).mp (le_of_eq ?_)
    change D.E.divisorialValuation _ = 1
    rw [map_div₀, map_pow, hWv, hvz i, hWt, ← WithZero.exp_nsmul,
      show α i • (-1 : ℤ) = -(α i : ℤ) by simp, div_self WithZero.exp_ne_zero]
  choose T hT using hT
  have hψz : ∀ i, algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z i.succ) =
      T i * algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z 0) ^ α i :=
    fun i => IsFractionRing.injective D.E.localRing D.Y.functionField (by
      rw [map_mul, map_pow, hT i, div_mul_cancel₀ _ (pow_ne_zero _ htK0)])
  refine ⟨T, hψz, ?_⟩
  -- the chart evaluation
  have hev : ∀ P : MvPolynomial (Fin c) (Y.presheaf.stalk (D.f D.E.genericPoint)),
      algebraMap D.E.localRing D.Y.functionField
        (eval₂ (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing) T P) =
      functionFieldMap D.f (chartMap Y.functionField (z 0) (fun i => z i.succ) α P) := by
    intro P
    have key : (algebraMap D.E.localRing D.Y.functionField).comp
        (eval₂Hom (algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing) T) =
        (functionFieldMap D.f).comp
          (chartMap Y.functionField (z 0) (fun i => z i.succ) α).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂Hom, eval₂_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartMap_C]
        rw [MMP.Mori.functionFieldMap_algebraMap_stalk]
        rfl
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂Hom, eval₂_X,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, chartMap_X, map_div₀, map_pow]
        rw [hT i, MMP.Mori.functionFieldMap_algebraMap_stalk,
          MMP.Mori.functionFieldMap_algebraMap_stalk]
        rfl
    exact DFunLike.congr_fun key P
  -- the residues of the chart coordinates
  have htrT : AlgebraicIndependent (ResidueField (Y.presheaf.stalk (D.f D.E.genericPoint)))
      (fun i => residue D.E.localRing (T i)) := by
    refine algebraicIndependent_residue_of_eval₂_mem T fun P hP => hvlt P ?_
    rw [← hWf, ← hev]
    exact (D.E.divisorialValuation_algebraMap_lt_one_iff _).mpr hP
  have hind := hyb.1.sumElim_comp (A := ResidueField D.E.localRing) htrT
  have htrB := trdeg_residueField_localRing_divisorOver hY (n := c + r)
    (by rw [hn, show c + 1 + r = c + r + 1 by omega]) D
  have hqb : IsTranscendenceBasis k (Sum.elim (fun i => residue D.E.localRing (T i))
      (algebraMap (ResidueField (Y.presheaf.stalk (D.f D.E.genericPoint)))
        (ResidueField D.E.localRing) ∘
          fun j => residue (Y.presheaf.stalk (D.f D.E.genericPoint)) (y j))) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (le_of_eq ?_)
    have hcard : Cardinal.mk (Fin c ⊕ Fin r) = ((c + r : ℕ) : Cardinal) := by
      rw [Cardinal.mk_sum, Cardinal.mk_fin, Cardinal.mk_fin, Cardinal.lift_natCast,
        Cardinal.lift_natCast, Nat.cast_add]
    rw [htrB, hcard, Cardinal.lift_natCast, Cardinal.lift_natCast]
  have hfun : (fun i => residue D.E.localRing (Sum.elim T
      (fun j => algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (y j)) i)) =
      Sum.elim (fun i => residue D.E.localRing (T i))
        (algebraMap (ResidueField (Y.presheaf.stalk (D.f D.E.genericPoint)))
          (ResidueField D.E.localRing) ∘
            fun j => residue (Y.presheaf.stalk (D.f D.E.genericPoint)) (y j)) := by
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact (IsLocalRing.ResidueField.algebraMap_residue (y j)).symm
  rw [hfun]
  exact hqb

/-- **The relation between the generators of the top forms at `p` and at `η_E`.** In the setting
of `exists_topForms_ordPullback_eq_of_valuation`, with `z_i = T_i z₀^{α_i}` in `𝒪_{Y',E}`, the form
`dz₀ ∧ ⋯ ∧ dz_c ∧ dy` is `z₀^{∑ α_i}` times a generator `dz₀ ∧ dT₁ ∧ ⋯ ∧ dT_c ∧ dy` of the top
forms of `𝒪_{Y',E}`, and `z₀^{∑ α_i}` has order `∑ α_i` along `E`. -/
private theorem exists_topFormsMap_eq_smul_of_chartCoords {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
    (hY : IsNormalVariety k sY) {c r : ℕ} (hn : topologicalKrullDim Y = (c + 1 + r : ℕ))
    (D : DivisorOver k sY) [IsIntegral D.Y] [IsLocallyNoetherian D.Y] [IsNormal D.Y]
    {z : Fin (c + 1) → Y.presheaf.stalk (D.f D.E.genericPoint)} {α : Fin c → ℕ}
    (hv0 : D.valuation (algebraMap _ Y.functionField (z 0)) = WithZero.exp (-1))
    (y : Fin r → Y.presheaf.stalk (D.f D.E.genericPoint)) (T : Fin c → D.E.localRing)
    (hψz : letI := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
      ∀ i, algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z i.succ) =
        T i * algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z 0) ^ α i)
    (hq : letI := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
      letI := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
      IsTranscendenceBasis k fun i => residue D.E.localRing (Sum.elim T
        (fun j => algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (y j)) i)) :
    letI := stalkAlgebra sY (D.f D.E.genericPoint)
    letI := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
    letI := functionFieldAlgebra (D.f ≫ sY)
    haveI := isScalarTower_stalk_functionField (D.f ≫ sY) D.E.genericPoint
    letI := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
    haveI := MMP.Threefold.Resolution.isScalarTower_stalkMap sY D.f D.E.genericPoint
    ∃ (σB : ⋀[D.E.localRing]^(c + 1 + r) Ω[D.E.localRing⁄k])
      (_ : Submodule.span D.E.localRing {σB} = ⊤)
      (_ : topFormsMap k D.E.localRing D.Y.functionField (c + 1 + r) σB ≠ 0)
      (h : D.E.localRing),
      topFormsMap k (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (c + 1 + r)
          (exteriorPower.ιMulti (Y.presheaf.stalk (D.f D.E.genericPoint)) (c + 1 + r)
            fun i => KaehlerDifferential.D k (Y.presheaf.stalk (D.f D.E.genericPoint))
              (Fin.append z y i)) = h • σB ∧
      algebraMap D.E.localRing D.Y.functionField h ≠ 0 ∧
      D.Y.ord (algebraMap D.E.localRing D.Y.functionField h) D.E.genericPoint =
        ∑ i, (α i : ℤ) := by
  classical
  let := stalkAlgebra sY (D.f D.E.genericPoint)
  have := D.isDominant
  have : LocallyOfFiniteType (D.f ≫ sY) := D.isNormalVariety.1.toLocallyOfFiniteType
  let := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
  let := functionFieldAlgebra (D.f ≫ sY)
  have := isScalarTower_stalk_functionField (D.f ≫ sY) D.E.genericPoint
  let := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
  have := MMP.Threefold.Resolution.isScalarTower_stalkMap sY D.f D.E.genericPoint
  have := D.E.isDiscreteValuationRing_localRing
  obtain ⟨t', ht'⟩ : ∃ t' : D.E.localRing,
      t' = algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z 0) := ⟨_, rfl⟩
  obtain ⟨yB, hyB⟩ : ∃ yB : Fin r → D.E.localRing,
      ∀ j, yB j = algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (y j) :=
    ⟨_, fun _ => rfl⟩
  have hψz' : ∀ i, algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (z i.succ) =
      T i * t' ^ α i := fun i => by
    rw [ht']
    exact hψz i
  have hq' : IsTranscendenceBasis k fun i => residue D.E.localRing (Sum.elim T yB i) := by
    rw [show yB = fun j => algebraMap (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing
      (y j) from funext hyB]
    exact hq
  have hWt : D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField t') =
      WithZero.exp (-1) := by
    rw [ht']
    exact (divisorialValuation_algebraMap_stalkMap D _).trans hv0
  have htK0 : algebraMap D.E.localRing D.Y.functionField t' ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hWt
    exact WithZero.exp_ne_zero hWt.symm
  have hmB : maximalIdeal D.E.localRing = Ideal.span {t'} :=
    maximalIdeal_eq_span_of_divisorialValuation_eq D.E hWt
  -- the generator `σ_B` at `η_E`
  have : Algebra.EssFiniteType k D.E.localRing :=
    essFiniteType_stalkAlgebra (D.f ≫ sY) D.E.genericPoint
  have : Module.Finite D.E.localRing Ω[D.E.localRing⁄k] := inferInstance
  have hnK' := finrank_kaehlerDifferential_functionField (D.f ≫ sY)
    (topologicalKrullDim_divisorOver_Y hY hn D)
  have hpz : Set.range (fun _ : Fin 1 => t') ⊆ Set.range (Fin.append (Fin.cons t' T) yB) :=
    Set.range_subset_iff.2 fun _ => ⟨Fin.castAdd r 0, by rw [Fin.append_left, Fin.cons_zero]⟩
  have hqz : Set.range (Sum.elim T yB) ⊆ Set.range (Fin.append (Fin.cons t' T) yB) := by
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i => exact ⟨Fin.castAdd r i.succ, by rw [Fin.append_left, Fin.cons_succ]; rfl⟩
    | inr j => exact ⟨Fin.natAdd (c + 1) j, by rw [Fin.append_right]; rfl⟩
  have hp : Ideal.span (Set.range fun _ : Fin 1 => t') = maximalIdeal D.E.localRing := by
    rw [Set.range_const, hmB]
  obtain ⟨hσB, h0B⟩ := span_ιMulti_D_eq_top_of_residue (k := k) (B := D.E.localRing)
    (K := D.Y.functionField) (Fin.append (Fin.cons t' T) yB)
    (fun _ : Fin 1 => t') _ hpz hqz hp hq' hnK'
  -- `σ_A = t'^{∑ α} • σ_B` in the top forms of `𝒪_{Y',E}`
  have hrel : topFormsMap k (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing (c + 1 + r)
      (exteriorPower.ιMulti (Y.presheaf.stalk (D.f D.E.genericPoint)) (c + 1 + r)
        fun i => KaehlerDifferential.D k (Y.presheaf.stalk (D.f D.E.genericPoint))
          (Fin.append z y i)) =
      t' ^ (∑ i, α i) • exteriorPower.ιMulti D.E.localRing (c + 1 + r)
        (fun i => KaehlerDifferential.D k D.E.localRing (Fin.append (Fin.cons t' T) yB i)) := by
    rw [topFormsMap_ιMulti]
    have e1 : (fun i => KaehlerDifferential.map k k (Y.presheaf.stalk (D.f D.E.genericPoint))
        D.E.localRing (KaehlerDifferential.D k (Y.presheaf.stalk (D.f D.E.genericPoint))
          (Fin.append z y i))) =
        Fin.append (Fin.cons (KaehlerDifferential.D k D.E.localRing t')
            fun i => KaehlerDifferential.D k D.E.localRing (T i * t' ^ α i))
          (fun j => KaehlerDifferential.D k D.E.localRing (yB j)) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left, Fin.append_left, KaehlerDifferential.map_D]
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [Fin.cons_zero, ← ht']
        · rw [Fin.cons_succ, hψz']
      · rw [Fin.append_right, Fin.append_right, KaehlerDifferential.map_D, hyB]
    have e2 : (fun i => KaehlerDifferential.D k D.E.localRing
          (Fin.append (Fin.cons t' T) yB i)) =
        Fin.append (Fin.cons (KaehlerDifferential.D k D.E.localRing t')
            fun i => KaehlerDifferential.D k D.E.localRing (T i))
          (fun j => KaehlerDifferential.D k D.E.localRing (yB j)) := by
      funext i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left, Fin.append_left]
        refine Fin.cases ?_ (fun i => ?_) i
        · rw [Fin.cons_zero, Fin.cons_zero]
        · rw [Fin.cons_succ, Fin.cons_succ]
      · rw [Fin.append_right, Fin.append_right]
    rw [e1, e2]
    exact ιMulti_append_cons_D_mul_pow _ _ _ _
  have hh : algebraMap D.E.localRing D.Y.functionField (t' ^ ∑ i, α i) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero _ htK0
  refine ⟨_, hσB, h0B, t' ^ ∑ i, α i, hrel, hh, ?_⟩
  have := D.E.divisorialValuation_eq_exp_neg_ord hh
  rw [map_pow, map_pow, hWt, ← WithZero.exp_nsmul] at this
  rw [map_pow]
  have := WithZero.exp_injective this
  simp only [nsmul_eq_mul, mul_neg, mul_one] at this
  push_cast at this
  linarith

/-- **The order of the pull-back of a form from a relation between generators.** If generators
`σ_A` of the top forms at `p = f(η_E)` and `σ_B` at `η_E` satisfy `f^* σ_A = h σ_B` with `h` of
order `N` along `E`, then `ord_E(f^*τ) = M + m N` for every nonzero `m`-canonical form `τ` with
`v(τ / σ_A^{⊗m}) = exp (-M)`. -/
private theorem ordPullback_eq_of_topFormsMap_eq_smul {k : Type u} [Field k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] (D : DivisorOver k sY)
    [IsIntegral D.Y] [IsLocallyNoetherian D.Y] [IsNormal D.Y] {d : ℕ} {N : ℤ}
    {σA : letI := stalkAlgebra sY (D.f D.E.genericPoint)
      ⋀[Y.presheaf.stalk (D.f D.E.genericPoint)]^d Ω[Y.presheaf.stalk (D.f D.E.genericPoint)⁄k]}
    (hσA : Submodule.span (Y.presheaf.stalk (D.f D.E.genericPoint)) {σA} = ⊤)
    (h0A : letI := stalkAlgebra sY (D.f D.E.genericPoint)
      letI := functionFieldAlgebra sY
      haveI := isScalarTower_stalk_functionField sY (D.f D.E.genericPoint)
      topFormsMap k (Y.presheaf.stalk (D.f D.E.genericPoint)) Y.functionField d σA ≠ 0)
    {σB : letI := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
      ⋀[D.E.localRing]^d Ω[D.E.localRing⁄k]}
    (hσB : Submodule.span D.E.localRing {σB} = ⊤)
    (h0B : letI := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
      letI := functionFieldAlgebra (D.f ≫ sY)
      haveI := isScalarTower_stalk_functionField (D.f ≫ sY) D.E.genericPoint
      topFormsMap k D.E.localRing D.Y.functionField d σB ≠ 0)
    (h : D.E.localRing)
    (hrel : letI := stalkAlgebra sY (D.f D.E.genericPoint)
      letI := stalkAlgebra (D.f ≫ sY) D.E.genericPoint
      letI := (D.f.stalkMap D.E.genericPoint).hom.toAlgebra
      haveI := MMP.Threefold.Resolution.isScalarTower_stalkMap sY D.f D.E.genericPoint
      topFormsMap k (Y.presheaf.stalk (D.f D.E.genericPoint)) D.E.localRing d σA = h • σB)
    (hh : algebraMap D.E.localRing D.Y.functionField h ≠ 0)
    (hN : D.Y.ord (algebraMap D.E.localRing D.Y.functionField h) D.E.genericPoint = N) :
    letI := stalkAlgebra sY (D.f D.E.genericPoint)
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY (D.f D.E.genericPoint)
    ∀ (m : ℤ) (τ : RationalPluriForms sY d m), τ ≠ 0 → ∀ M : ℤ,
      D.valuation (formCoeff (k := k) (Y.presheaf.stalk (D.f D.E.genericPoint)) hσA h0A τ) =
        WithZero.exp (-M) → D.ordPullback τ = M + m * N := by
  let := stalkAlgebra sY (D.f D.E.genericPoint)
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (D.f D.E.genericPoint)
  intro m τ hτ M hM
  have := D.isDominant
  have hWf : ∀ g, D.E.divisorialValuation (functionFieldMap D.f g) = D.valuation g :=
    fun g => rfl
  have key := MMP.Threefold.Resolution.ordForm_pullbackRationalPluriForms_eq sY D.f D.E hσA h0A
    hσB h0B h hrel hh hτ
  change D.E.ordForm (pullbackRationalPluriForms sY D.f τ) = _
  rw [key]
  have hne : functionFieldMap D.f
      (formCoeff (k := k) (Y.presheaf.stalk (D.f D.E.genericPoint)) hσA h0A τ) ≠ 0 := by
    intro h0
    have h1 : D.valuation
        (formCoeff (k := k) (Y.presheaf.stalk (D.f D.E.genericPoint)) hσA h0A τ) = 0 := by
      rw [← hWf, h0, map_zero]
    rw [hM] at h1
    exact WithZero.exp_ne_zero h1
  have h1 : D.Y.ord (functionFieldMap D.f
      (formCoeff (k := k) (Y.presheaf.stalk (D.f D.E.genericPoint)) hσA h0A τ))
        D.E.genericPoint = M := by
    have := D.E.divisorialValuation_eq_exp_neg_ord hne
    rw [hWf, hM] at this
    have := WithZero.exp_injective this
    omega
  rw [h1, hN]

/-- **The order of forms along a divisor with a weighted valuation.** Let `Y` be a normal variety
of dimension `c + 1 + r` over a field of characteristic zero and `(Y', f, E)` a divisor over `Y`
whose centre `p = f(η_E)` has a regular local ring with regular system of parameters
`z₀, …, z_c`, such that the valuation `v` of `E` has `v(z₀) = exp (-1)`,
`v(z_i) = exp (-α_i)` and `v(P(z_i / z₀^{α_i})) < 1` only for polynomials `P` with coefficients in
the maximal ideal. For lifts `y₁, …, y_r` of a transcendence basis of `κ(p)`, the form
`σ = dz₀ ∧ ⋯ ∧ dz_c ∧ dy₁ ∧ ⋯ ∧ dy_r` generates the top forms at `p`, and
`ord_E(f^*τ) = M + m ∑ α_i` for every nonzero `m`-canonical form `τ` with
`v(τ / σ^{⊗m}) = exp (-M)`: in the chart `z_i = T_i z₀^{α_i}`, `σ` is `z₀^{∑ α_i}` times the
generator `dz₀ ∧ dT₁ ∧ ⋯ ∧ dT_c ∧ dy` of the top forms at `η_E`. -/
private theorem exists_topForms_ordPullback_eq_of_valuation {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsNormalVariety k sY) {c r : ℕ} (hn : topologicalKrullDim Y = (c + 1 + r : ℕ))
    (D : DivisorOver k sY) [IsRegularLocalRing (Y.presheaf.stalk (D.f D.E.genericPoint))]
    {z : Fin (c + 1) → Y.presheaf.stalk (D.f D.E.genericPoint)}
    (hz : IsRegularSystemOfParameters z) {α : Fin c → ℕ}
    (hv0 : D.valuation (algebraMap _ Y.functionField (z 0)) = WithZero.exp (-1))
    (hvz : ∀ i, D.valuation (algebraMap _ Y.functionField (z i.succ)) =
      WithZero.exp (-(α i : ℤ)))
    (hvlt : ∀ P, D.valuation (chartMap Y.functionField (z 0) (fun i => z i.succ) α P) < 1 →
      P ∈ Ideal.map (C : _ →+* MvPolynomial (Fin c) _)
        (maximalIdeal (Y.presheaf.stalk (D.f D.E.genericPoint)))) :
    letI := stalkAlgebra sY (D.f D.E.genericPoint)
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY (D.f D.E.genericPoint)
    ∃ (σ : ⋀[Y.presheaf.stalk (D.f D.E.genericPoint)]^(c + 1 + r)
        Ω[Y.presheaf.stalk (D.f D.E.genericPoint)⁄k])
      (hσ : Submodule.span (Y.presheaf.stalk (D.f D.E.genericPoint)) {σ} = ⊤)
      (h0 : topFormsMap k (Y.presheaf.stalk (D.f D.E.genericPoint)) Y.functionField
        (c + 1 + r) σ ≠ 0),
      ∀ (m : ℤ) (τ : RationalPluriForms sY (c + 1 + r) m), τ ≠ 0 → ∀ M : ℤ,
        D.valuation (formCoeff (k := k) (Y.presheaf.stalk (D.f D.E.genericPoint)) hσ h0 τ) =
          WithZero.exp (-M) →
          D.ordPullback τ = M + m * ∑ i, (α i : ℤ) := by
  classical
  let := stalkAlgebra sY (D.f D.E.genericPoint)
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY (D.f D.E.genericPoint)
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : Algebra.EssFiniteType k (Y.presheaf.stalk (D.f D.E.genericPoint)) :=
    essFiniteType_stalkAlgebra sY _
  have : IsDomain (Y.presheaf.stalk (D.f D.E.genericPoint)) := IsRegularLocalRing.isDomain _
  -- lifts of a transcendence basis of the residue field at `p`
  have hd : ringKrullDim (Y.presheaf.stalk (D.f D.E.genericPoint)) = (c + 1 : ℕ) := hz.2
  -- (`have` rather than `obtain` throughout: `rcases` type-checks the large goal each time)
  have htr := (trdeg_residueField_stalk sY hn _ hd).1
  rw [Nat.add_sub_cancel_left] at htr
  have hw := exists_isTranscendenceBasis_fin htr
  choose y hy using fun i => IsLocalRing.residue_surjective (hw.choose i)
  have hyb : IsTranscendenceBasis k (fun i => residue (Y.presheaf.stalk _) (y i)) := by
    rw [show (fun i => residue (Y.presheaf.stalk _) (y i)) = hw.choose from funext hy]
    exact hw.choose_spec
  -- the generator `σ_A` at `p`
  have hnK := finrank_kaehlerDifferential_functionField sY hn
  have : Module.Finite (Y.presheaf.stalk (D.f D.E.genericPoint))
      Ω[Y.presheaf.stalk (D.f D.E.genericPoint)⁄k] := inferInstance
  have hzr : Set.range z ⊆ Set.range (Fin.append z y) :=
    Set.range_subset_iff.2 fun i => ⟨Fin.castAdd r i, Fin.append_left z y i⟩
  have hyr : Set.range y ⊆ Set.range (Fin.append z y) :=
    Set.range_subset_iff.2 fun j => ⟨Fin.natAdd (c + 1) j, Fin.append_right z y j⟩
  have hσA := span_ιMulti_D_eq_top_of_residue (k := k)
    (B := Y.presheaf.stalk (D.f D.E.genericPoint)) (K := Y.functionField) (Fin.append z y) z y
    hzr hyr hz.1 hyb hnK
  -- the chart coordinates, the generator `σ_B` at `η_E`, and the order of the pull-back
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have hT := exists_chartCoords_isTranscendenceBasis hY hn D hv0 hvz hvlt hyb
  have hB := exists_topFormsMap_eq_smul_of_chartCoords hY hn D hv0 y hT.choose
    hT.choose_spec.1 hT.choose_spec.2
  exact hB.elim fun _ hB => hB.elim fun hσB hB => hB.elim fun h0B hB => hB.elim fun h hB =>
    ⟨_, hσA.1, hσA.2,
      ordPullback_eq_of_topFormsMap_eq_smul D hσA.1 hσA.2 hσB h0B h hB.1 hB.2.1 hB.2.2⟩

/-- **The weighted monomial divisor at a regular point, and the order of forms along it.** Let
`Y` be a normal variety of dimension `c + 1 + r` over a field of characteristic zero, `p ∈ Y` a
point with `𝒪_{Y,p}` regular, `z₀, …, z_c` a regular system of parameters of `𝒪_{Y,p}` and
`α_i ≥ 1` weights. There is a divisor `(Y', f, E)` over `Y` with `f(η_E) = p` whose valuation `v`
has `v ≤ 1` on `𝒪_{Y,p}`, `v ≤ exp (-1)` on its maximal ideal and `v(z_i) = exp (-α_i)`, and a
generator `σ = dz₀ ∧ ⋯ ∧ dz_c ∧ dy₁ ∧ ⋯ ∧ dy_r` of the top forms at `p` with
`ord_E(f^*τ) = M + m ∑ α_i` for every nonzero `m`-canonical form `τ` with
`v(τ / σ^{⊗m}) = exp (-M)`. -/
private theorem exists_divisorOver_ordPullback_eq {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : IsNormalVariety k sY) {c r : ℕ} (hn : topologicalKrullDim Y = (c + 1 + r : ℕ)) (p : Y)
    [IsRegularLocalRing (Y.presheaf.stalk p)] {z : Fin (c + 1) → Y.presheaf.stalk p}
    (hz : IsRegularSystemOfParameters z) {α : Fin c → ℕ} (hα : ∀ i, 1 ≤ α i) :
    letI := stalkAlgebra sY p
    letI := functionFieldAlgebra sY
    haveI := isScalarTower_stalk_functionField sY p
    ∃ (D : DivisorOver k sY) (σ : ⋀[Y.presheaf.stalk p]^(c + 1 + r) Ω[Y.presheaf.stalk p⁄k])
      (hσ : Submodule.span (Y.presheaf.stalk p) {σ} = ⊤)
      (h0 : topFormsMap k (Y.presheaf.stalk p) Y.functionField (c + 1 + r) σ ≠ 0),
      D.f D.E.genericPoint = p ∧
      (∀ a : Y.presheaf.stalk p, D.valuation (algebraMap _ Y.functionField a) ≤ 1) ∧
      (∀ a ∈ maximalIdeal (Y.presheaf.stalk p),
        D.valuation (algebraMap _ Y.functionField a) ≤ WithZero.exp (-1)) ∧
      (∀ i, D.valuation (algebraMap _ Y.functionField (z i.succ)) =
        WithZero.exp (-(α i : ℤ))) ∧
      ∀ (m : ℤ) (τ : RationalPluriForms sY (c + 1 + r) m), τ ≠ 0 → ∀ M : ℤ,
        D.valuation (formCoeff (k := k) (Y.presheaf.stalk p) hσ h0 τ) = WithZero.exp (-M) →
          D.ordPullback τ = M + m * ∑ i, (α i : ℤ) := by
  classical
  let := stalkAlgebra sY p
  let := functionFieldAlgebra sY
  have := isScalarTower_stalk_functionField sY p
  haveI : AlgebraicGeometry.IsVariety k sY := hY.1
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsDomain (Y.presheaf.stalk p) := IsRegularLocalRing.isDomain _
  have : Algebra.EssFiniteType k (Y.presheaf.stalk p) := essFiniteType_stalkAlgebra sY p
  -- the chart valuation
  obtain ⟨v, hv0, hvle, hvlt, hvfrac⟩ :=
    exists_chartValuation_of_isRegularSystemOfParameters (K := Y.functionField) hz hα
  have hle : ∀ a : Y.presheaf.stalk p, v (algebraMap _ Y.functionField a) ≤ 1 := fun a => by
    simpa only [chartMap_C] using hvle (C a)
  have hlt : ∀ a ∈ maximalIdeal (Y.presheaf.stalk p), v (algebraMap _ Y.functionField a) < 1 :=
    fun a ha => by
      have := (hvlt (C a)).2 (Ideal.mem_map_of_mem _ ha)
      simpa only [chartMap_C] using this
  have hz0 : algebraMap _ Y.functionField (z 0) ≠ 0 := fun h => by
    rw [h, map_zero] at hv0
    exact WithZero.exp_ne_zero hv0.symm
  have hvz : ∀ i, v (algebraMap _ Y.functionField (z i.succ)) = WithZero.exp (-(α i : ℤ)) := by
    intro i
    have hX : v (chartMap Y.functionField (z 0) (fun i => z i.succ) α (X i)) = 1 := by
      refine le_antisymm (hvle _) (not_lt.mp fun h => ?_)
      have := (hvlt _).1 h
      rw [MvPolynomial.mem_map_C_iff] at this
      have h1 := this (Finsupp.single i 1)
      rw [MvPolynomial.coeff_X, if_pos rfl] at h1
      exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)
    have heq : algebraMap _ Y.functionField (z i.succ) =
        chartMap Y.functionField (z 0) (fun i => z i.succ) α (X i) *
          algebraMap _ Y.functionField (z 0) ^ α i := by
      rw [chartMap_X, div_mul_cancel₀ _ (pow_ne_zero _ hz0)]
    rw [heq, map_mul, hX, one_mul, map_pow, hv0, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hmle : ∀ a ∈ maximalIdeal (Y.presheaf.stalk p),
      v (algebraMap _ Y.functionField a) ≤ WithZero.exp (-1) := by
    intro a ha
    rw [← hz.1] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hv0.le
      · rw [hvz i]
        exact WithZero.exp_le_exp.2 (by have := hα i; omega)
    · simp
    · intro a b _ _ ha hb
      rw [map_add]
      exact v.map_add_le ha hb
    · intro a b _ hb
      rw [smul_eq_mul, map_mul, map_mul]
      calc v (algebraMap _ Y.functionField a) * v (algebraMap _ Y.functionField b)
          ≤ 1 * WithZero.exp (-1) := mul_le_mul' (hle a) hb
        _ = _ := one_mul _
  obtain ⟨D₀, -, hDv₀, hDp₀⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates_of_essFiniteType sY
      (exists_essFiniteType_range_of_chart (k := k) v hvle hvfrac) hv0 p hle hlt
  set D := D₀.toDivisorOver with hD
  have hDv : D.valuation = v := hDv₀
  have hDp : D.f D.E.genericPoint = p := hDp₀
  clear_value D
  clear hDv₀ hDp₀ hD D₀
  subst hDp
  obtain ⟨σ, hσ, h0, hord⟩ := exists_topForms_ordPullback_eq_of_valuation hY hn D hz
    (by rw [hDv]; exact hv0) (fun i => by rw [hDv]; exact hvz i)
    (fun P hP => (hvlt P).1 (by rw [← hDv]; exact hP))
  exact ⟨D, σ, hσ, h0, rfl, fun a => by rw [hDv]; exact hle a,
    fun a ha => by rw [hDv]; exact hmle a ha, fun i => by rw [hDv]; exact hvz i, hord⟩

end WeightedDivisor

section Additivity

open CategoryTheory AlgebraicGeometry MMP.Mori

/-- **Adding a `ℚ`-Cartier divisor lowers the discrepancy by its value.** Let `(Y, f, E)` be a
divisor over a normal variety `X` over a perfect field, `p = f(η_E)`, and let `qG` be a divisor
with a local equation `g ∈ k(X)` on an open `U ∋ p`, `ord_E(f^*g) = M`. If `a = a(E, X, B)` and
`a' = a(E, X, B + G)`, then `a' = a - M / q`. -/
private theorem isDiscrepancy_add_eq_sub {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {n : ℕ} {K : Divisor X} {B G : QDivisor X} {D : DivisorOver k sX} {a a' : ℚ}
    (ha : IsDiscrepancy sX n K B D a) (ha' : IsDiscrepancy sX n K (B + G) D a') {q : ℕ}
    (hq : 0 < q) {Dq : Divisor X} (hDq : Divisor.toQDivisor Dq = (q : ℤ) • G) {U : X.Opens}
    (hU : D.f D.E.genericPoint ∈ U) {gK : X.functionField} (hg0 : gK ≠ 0)
    (hgU : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
      (Dq.coeff Γ : ℤ) = X.ord gK Γ.genericPoint)
    {M : ℤ} (hM : D.valuation gK = WithZero.exp (-M)) :
    a' = a - M / q := by
  obtain ⟨hX, hK, m, hm, -, U₁, hU₁, τ, hτ, hτa⟩ := ha
  obtain ⟨-, -, m', hm', -, U₂, hU₂, τ', hτ', hτa'⟩ := ha'
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m).repr τ () with hc_def
  set c' := (ZTensorPower.basis b m').repr τ' () with hc'_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'.1
  set g : X.functionField :=
    c ^ ((q * m' : ℕ) : ℤ) * c' ^ (-((q * m : ℕ) : ℤ)) * gK ^ (-((m * m' : ℕ) : ℤ)) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'))
    (zpow_ne_zero _ hg0)
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      X.ord g Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hτ.2 Γ ⟨_, hΓ, hU₁⟩
    have e2 := hτ'.2 Γ ⟨_, hΓ, hU₂⟩
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ.1
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ' hτ'.1
    have e3 : ((Dq.coeff Γ : ℤ) : ℚ) = (X.ord gK Γ.genericPoint : ℚ) := by
      exact_mod_cast hgU Γ ⟨_, hΓ, hU⟩
    have e4 : ((Dq.coeff Γ : ℤ) : ℚ) = q * G.coeff Γ := by
      have := congrArg (fun D : QDivisor X => D.coeff Γ) hDq
      simpa [zsmul_eq_mul] using this
    have e5 : (B + G).coeff Γ = B.coeff Γ + G.coeff Γ := rfl
    rw [hg_def, Scheme.ord_mul (mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'))
      (zpow_ne_zero _ hg0), Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'),
      ord_zpow _ hc, ord_zpow _ hc', ord_zpow _ hg0]
    have : ((((q * m' : ℕ) : ℤ) : ℚ) * X.ord c Γ.genericPoint +
        ((-((q * m : ℕ) : ℤ) : ℤ) : ℚ) * X.ord c' Γ.genericPoint +
        ((-((m * m' : ℕ) : ℤ) : ℤ) : ℚ) * X.ord gK Γ.genericPoint) = 0 := by
      push_cast
      rw [e5] at e2
      linear_combination (q * m' : ℚ) * e1 - (q * m : ℚ) * e2 - (q * m' : ℚ) * f1 +
        (q * m : ℚ) * f2 + (m * m' : ℚ) * e3 - (m * m' : ℚ) * e4
    exact_mod_cast this
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hg hord
  have hY0 : D.Y.ord (functionFieldMap D.f g) D.E.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact D.E.ord_algebraMap_of_isUnit (hu.map _)
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap D.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  have hfg : functionFieldMap D.f gK ≠ 0 := (map_ne_zero _).mpr hg0
  rw [hg_def, map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (mul_ne_zero (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'))
      (zpow_ne_zero _ hfg), Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'),
    ord_zpow _ hfc, ord_zpow _ hfc', ord_zpow _ hfg] at hY0
  have hMg : D.Y.ord (functionFieldMap D.f gK) D.E.genericPoint = M := by
    have h1 := D.E.divisorialValuation_eq_exp_neg_ord hfg
    change D.E.divisorialValuation (functionFieldMap D.f gK) = _ at hM
    rw [hM] at h1
    have := WithZero.exp_injective h1
    omega
  rw [hMg] at hY0
  have h1 : (D.ordPullback τ : ℚ) =
      (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m τ hτ.1
  have h2 : (D.ordPullback τ' : ℚ) =
      (D.Y.ord (functionFieldMap D.f c') D.E.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ' hτ'.1
  have hY0' : (((q * m' : ℕ) : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      (-((q * m : ℕ) : ℚ)) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint +
      (-((m * m' : ℕ) : ℚ)) * M) = 0 := by
    exact_mod_cast hY0
  have key : (q : ℚ) * m * m' * (a - a') - m * m' * M = 0 := by
    push_cast at hY0'
    linear_combination (q * m' : ℚ) * hτa - (q * m : ℚ) * hτa' + (q * m' : ℚ) * h1 -
      (q * m : ℚ) * h2 + hY0'
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hm0 : (m : ℚ) * m' ≠ 0 := by positivity
  field_simp
  have : (m : ℚ) * m' * (q * (a - a') - M) = 0 := by linear_combination key
  have := (mul_eq_zero.mp this).resolve_left hm0
  linear_combination (-1 : ℚ) * this

end Additivity

section Composite

open CategoryTheory AlgebraicGeometry MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-- A divisor `(Y', g, F)` over a model `(Y, f)` of `X` is the divisor `(Y', f ∘ g, F)` over
`X`. -/
private noncomputable def compDivisorOver (E : DivisorOver k sX) (D : DivisorOver k (E.f ≫ sX)) :
    DivisorOver k sX :=
  haveI := E.isIntegral
  haveI := D.isIntegral
  { Y := D.Y
    f := D.f ≫ E.f
    isNormalVariety := by rw [Category.assoc]; exact D.isNormalVariety
    isBirationalMorphism := isBirationalMorphism_comp D.isBirationalMorphism E.isBirationalMorphism
    E := D.E }

/-- The valuation of `(Y', f ∘ g, F)` is that of `(Y', g, F)` through `f^*`. -/
private theorem valuation_compDivisorOver (E : DivisorOver k sX) (D : DivisorOver k (E.f ≫ sX))
    (t : X.functionField) :
    haveI := E.isIntegral
    haveI := E.isDominant
    (compDivisorOver E D).valuation t = D.valuation (functionFieldMap E.f t) := by
  have := E.isIntegral
  have := E.isDominant
  have := D.isIntegral
  have := D.isDominant
  have := D.isNormal
  have := D.isLocallyNoetherian
  have : IsDominant (D.f ≫ E.f) := (compDivisorOver E D).isDominant
  change D.E.divisorialValuation (functionFieldMap (D.f ≫ E.f) t) =
    D.E.divisorialValuation (functionFieldMap D.f (functionFieldMap E.f t))
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The order of `(f ∘ g)^*τ` along `F` is the order of `g^*(f^*τ)`. -/
private theorem ordPullback_compDivisorOver [PerfectField k] (hX : IsNormalVariety k sX)
    {n : ℕ} (hn : topologicalKrullDim X = n) (E : DivisorOver k sX)
    (D : DivisorOver k (E.f ≫ sX)) {m : ℤ} (τ : RationalPluriForms sX n m) :
    haveI := E.isIntegral
    haveI := E.isDominant
    (compDivisorOver E D).ordPullback τ = D.ordPullback (pullbackRationalPluriForms sX E.f τ) := by
  have := E.isIntegral
  have := E.isDominant
  have := D.isIntegral
  have := D.isDominant
  have := D.isNormal
  have := D.isLocallyNoetherian
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (E.f ≫ sX) := E.isNormalVariety.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  change D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ E.f) τ) =
    D.E.ordForm (pullbackRationalPluriForms (E.f ≫ sX) D.f (pullbackRationalPluriForms sX E.f τ))
  rw [MMP.Flips.pullbackRationalPluriForms_comp E.f D.f
    E.isBirationalMorphism.functionFieldMap_bijective
    D.isBirationalMorphism.functionFieldMap_bijective hd τ]
  rfl

end Composite

section WeightedDiscrepancy

open CategoryTheory AlgebraicGeometry MMP.Mori IsLocalRing

/-- A valuation bounded by `1` on `R` and by `exp (-1)` on an ideal `I` is bounded by
`exp (-M)` on `I^M`. -/
private theorem valuation_le_exp_of_mem_pow {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (v : Valuation K ℤᵐ⁰) {I : Ideal R} (h1 : ∀ a, v (algebraMap R K a) ≤ 1)
    (hI : ∀ a ∈ I, v (algebraMap R K a) ≤ WithZero.exp (-1)) (M : ℕ) :
    ∀ a ∈ I ^ M, v (algebraMap R K a) ≤ WithZero.exp (-(M : ℤ)) := by
  induction M with
  | zero => intro a _; simpa using h1 a
  | succ M ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) (fun x y hx hy => ?_)
    · rw [map_mul, map_mul]
      calc v (algebraMap R K x) * v (algebraMap R K y)
          ≤ WithZero.exp (-(M : ℤ)) * WithZero.exp (-1) := mul_le_mul' (ih x hx) (hI y hy)
        _ = WithZero.exp (-((M + 1 : ℕ) : ℤ)) := by
          rw [← WithZero.exp_add]; congr 1; push_cast; ring
    · rw [map_add]
      exact v.map_add_le hx hy

/-- **The discrepancy of the weighted divisor.** Let `E` be a divisor over a normal variety `X`
of dimension `n` over a field of characteristic zero with `a(E, X, B) = -1`, computed by a form
`τ` generating `𝒪_X(m(K + B))` on `U`. Let `η` be a point of the model `Y` of `E` with `f(η) ∈ U`,
`𝒪_{Y,η}` regular with a regular system of parameters `z₀, z₁, …, z_{c+1}` such that `z₁`
generates the ideal of `E` at `η`, and suppose `ord_F(f^*τ) = 0` along the other prime divisors
`F` through `η`. For `N ≥ 1` the monomial divisor `D` of weights `1` on the `z_i`, `i ≠ 1`, and
`N` on `z₁` has centre `f(η)` and `a(D, X, B) = c`; its valuation is `≤ exp (-M)` on `𝔪^M` and
`≤ exp (-N)` on the elements whose image in `𝒪_{Y,η}` is a multiple of `z₁`. -/
private theorem exists_divisorOver_isDiscrepancy_eq {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (E : DivisorOver k sX) {m : ℕ} (hm : 0 < m)
    (hmC : ((m : ℤ) • (Divisor.toQDivisor K + B)).IsCartierDivisor) {U : X.Opens}
    {τ : RationalPluriForms sX n m} (hτ : GeneratesOn B m U τ)
    (hτa : (m : ℚ) * (-1) = E.ordPullback τ) (η : E.Y)
    [IsRegularLocalRing (E.Y.presheaf.stalk η)] (hηU : E.f η ∈ U) {c : ℕ}
    {z : Fin (c + 2) → E.Y.presheaf.stalk η} (hz : IsRegularSystemOfParameters z)
    (hzE : haveI := E.isIntegral
      IdealSheafData.stalk E.E.idealSheaf η = Ideal.span {z 1})
    (hF : haveI := E.isIntegral
      haveI := E.isLocallyNoetherian
      haveI := E.isDominant
      ∀ F : MMP.Mori.PrimeDivisor E.Y, η ∈ F.support → F ≠ E.E →
        F.ordForm (pullbackRationalPluriForms sX E.f τ) = 0)
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ D : DivisorOver k sX, D.f D.E.genericPoint = E.f η ∧
      IsDiscrepancy sX n K B D c ∧
      (∀ a : X.presheaf.stalk (E.f η), D.valuation (algebraMap _ X.functionField a) ≤ 1) ∧
      (∀ M : ℕ, ∀ a ∈ maximalIdeal (X.presheaf.stalk (E.f η)) ^ M,
        D.valuation (algebraMap _ X.functionField a) ≤ WithZero.exp (-(M : ℤ))) ∧
      ∀ a : X.presheaf.stalk (E.f η), (E.f.stalkMap η).hom a ∈ Ideal.span {z 1} →
        D.valuation (algebraMap _ X.functionField a) ≤ WithZero.exp (-(N : ℤ)) := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have hYv := E.isNormalVariety
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (E.f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  have hnY := topologicalKrullDim_divisorOver_Y hX hn E
  have hd : ringKrullDim (E.Y.presheaf.stalk η) = (c + 2 : ℕ) := hz.2
  obtain ⟨-, hle2⟩ := trdeg_residueField_stalk (E.f ≫ sX) hnY η hd
  obtain ⟨r, rfl⟩ : ∃ r, n = c + 1 + 1 + r := ⟨n - (c + 2), by omega⟩
  -- the weights: `N` on `z₁`, `1` on the other parameters
  let α : Fin (c + 1) → ℕ := Fin.cons N fun _ => 1
  have hα : ∀ i, 1 ≤ α i := fun i => Fin.cases hN (fun _ => le_rfl) i
  obtain ⟨Dv, σ, hσ, h0, hDp, hle, hmle, hvz, hord⟩ :=
    exists_divisorOver_ordPullback_eq hYv (c := c + 1) (r := r) hnY η hz hα
  -- valuations of the composite divisor
  have hvX : ∀ a : X.presheaf.stalk (E.f η),
      (compDivisorOver E Dv).valuation (algebraMap _ X.functionField a) =
        Dv.valuation (algebraMap _ E.Y.functionField ((E.f.stalkMap η).hom a)) := by
    intro a
    rw [valuation_compDivisorOver, MMP.Mori.functionFieldMap_algebraMap_stalk]
  -- the pulled-back form and its coefficient along `σ`
  have hEo : E.E.ordForm (pullbackRationalPluriForms sX E.f τ) = -(m : ℤ) := by
    have : (E.ordPullback τ : ℚ) = -(m : ℚ) := by rw [← hτa]; ring
    exact_mod_cast this
  have hτY : pullbackRationalPluriForms sX E.f τ ≠ 0 := fun h0' => by
    rw [h0', MMP.Mori.PrimeDivisor.ordForm_zero] at hEo
    omega
  let := stalkAlgebra (E.f ≫ sX) η
  let := functionFieldAlgebra (E.f ≫ sX)
  have := isScalarTower_stalk_functionField (E.f ≫ sX) η
  obtain ⟨cY, hcY⟩ : ∃ cY : E.Y.functionField,
      cY = formCoeff (k := k) (E.Y.presheaf.stalk η) hσ h0 (pullbackRationalPluriForms sX E.f τ) :=
    ⟨_, rfl⟩
  have hcY0 : cY ≠ 0 := fun h => hτY ((formCoeff_eq_zero_iff hσ h0 _).mp (hcY ▸ h))
  obtain ⟨zE, hzE'⟩ : ∃ zE : E.Y.functionField,
      zE = algebraMap (E.Y.presheaf.stalk η) E.Y.functionField (z 1) := ⟨_, rfl⟩
  have hz1 : z 1 ≠ 0 := MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz 1
  have hzE0 : zE ≠ 0 := fun h => hz1 (IsFractionRing.injective _ E.Y.functionField
    ((hzE' ▸ h).trans (map_zero _).symm))
  have hu0 : cY * zE ^ (m : ℤ) ≠ 0 := mul_ne_zero hcY0 (zpow_ne_zero _ hzE0)
  have hordu : ∀ Γ : MMP.Mori.PrimeDivisor E.Y, η ∈ Γ.support →
      E.Y.ord (cY * zE ^ (m : ℤ)) Γ.genericPoint = 0 := by
    intro Γ hΓ
    have h1 := MMP.Threefold.Resolution.ordForm_eq_ord_formCoeff (E.f ≫ sX) η Γ hΓ hσ h0
      (pullbackRationalPluriForms sX E.f τ)
    have h2 := (ord_algebraMap_of_stalk_eq_span E.E Γ hΓ hzE).2
    rw [← hzE'] at h2
    rw [← hcY] at h1
    rw [Scheme.ord_mul hcY0 (zpow_ne_zero _ hzE0), ord_zpow _ hzE0, ← h1, h2]
    by_cases hΓE : Γ = E.E
    · subst hΓE
      rw [if_pos rfl, hEo]
      ring
    · rw [if_neg hΓE, hF Γ hΓ hΓE]
      ring
  obtain ⟨a, ha, hau⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero η hu0 hordu
  have hvu : Dv.valuation (cY * zE ^ (m : ℤ)) = 1 := by
    rw [← hau]
    refine le_antisymm (hle a) ?_
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    calc (1 : ℤᵐ⁰) = Dv.valuation (algebraMap _ E.Y.functionField a) *
          Dv.valuation (algebraMap _ E.Y.functionField b) := by
            rw [← map_mul, ← map_mul, hb, map_one, map_one]
      _ ≤ Dv.valuation (algebraMap _ E.Y.functionField a) * 1 := mul_le_mul' le_rfl (hle b)
      _ = _ := mul_one _
  have hvzE : Dv.valuation zE = WithZero.exp (-(N : ℤ)) := by
    rw [hzE']
    exact hvz 0
  have hvc : Dv.valuation cY = WithZero.exp (-(-((m : ℤ) * N))) := by
    rw [map_mul, map_zpow₀, hvzE, ← WithZero.exp_zsmul] at hvu
    rw [eq_inv_of_mul_eq_one_left hvu, ← WithZero.exp_neg]
    congr 1
    simp only [smul_eq_mul]
    ring
  have hordY := hord m (pullbackRationalPluriForms sX E.f τ) hτY (-((m : ℤ) * N))
    (by rw [← hcY]; exact hvc)
  have hsum : ∑ i, (α i : ℤ) = N + c := by
    simp [α, Fin.sum_univ_succ]
  refine ⟨compDivisorOver E Dv, ?_, ⟨hX, hK, m, hm, hmC, U, ?_, τ, hτ, ?_⟩, ?_, ?_, ?_⟩
  · show E.f (Dv.f Dv.E.genericPoint) = E.f η
    rw [hDp]
  · show E.f (Dv.f Dv.E.genericPoint) ∈ U
    rw [hDp]
    exact hηU
  · rw [ordPullback_compDivisorOver hX hn E Dv τ, hordY, hsum]
    push_cast
    ring
  · intro a
    rw [hvX]
    exact hle _
  · intro M a ha
    rw [hvX]
    refine valuation_le_exp_of_mem_pow Dv.valuation hle hmle M _ ?_
    have hmap : (maximalIdeal (X.presheaf.stalk (E.f η))).map (E.f.stalkMap η).hom ≤
        maximalIdeal (E.Y.presheaf.stalk η) :=
      Ideal.map_le_iff_le_comap.mpr fun x hx => map_nonunit (E.f.stalkMap η).hom x hx
    have := Ideal.mem_map_of_mem (E.f.stalkMap η).hom ha
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hmap M this
  · intro a ha
    rw [hvX]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
    rw [← hb, map_mul, map_mul]
    calc Dv.valuation (algebraMap _ E.Y.functionField b) *
          Dv.valuation (algebraMap _ E.Y.functionField (z 1))
        ≤ 1 * WithZero.exp (-(N : ℤ)) := mul_le_mul' (hle b) (le_of_eq (hvz 0))
      _ = _ := one_mul _

end WeightedDiscrepancy

section GeneralPosition

open CategoryTheory AlgebraicGeometry IsLocalRing

/-- The point of `Y` corresponding to a prime `p` of `𝒪_{Y,y}` has local ring the localization of
`𝒪_{Y,y}` at `p`: the maximal ideal of `𝒪_{Y,η}` pulls back to `p`. -/
private theorem under_maximalIdeal_stalk_fromSpecStalk {Y : Scheme.{u}} (y : Y)
    (p : Spec (Y.presheaf.stalk y)) (h : Y.fromSpecStalk y p ⤳ y) :
    (maximalIdeal (Y.presheaf.stalk (Y.fromSpecStalk y p))).comap
      (Y.presheaf.stalkSpecializes h).hom = p.asIdeal := by
  have e := congrArg (fun g => g (closedPoint (Y.presheaf.stalk (Y.fromSpecStalk y p))))
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk h)
  simp only [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint] at e
  have h2 : PrimeSpectrum.comap (Y.presheaf.stalkSpecializes h).hom (closedPoint _) = p :=
    (Spec.map_apply _ _).symm.trans (Stacks.Chow.fromSpecStalk_injective y e)
  exact congrArg PrimeSpectrum.asIdeal h2

/-- The stalk of `Y` at the point corresponding to a prime `p` of `𝒪_{Y,y}` has dimension the
height of `p`. -/
private theorem ringKrullDim_stalk_fromSpecStalk {Y : Scheme.{u}} (y : Y)
    (p : Spec (Y.presheaf.stalk y)) :
    ringKrullDim (Y.presheaf.stalk (Y.fromSpecStalk y p)) = p.asIdeal.height := by
  rw [ringKrullDim_stalk_eq_coheight, Stacks.Chow.coheight_fromSpecStalk_eq_height]

/-- The image under `f` of the point corresponding to a prime `p` of `𝒪_{Y,y}` containing the
image of `𝔪_{f y}` is `f y`. -/
private theorem hom_fromSpecStalk_eq {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    (p : Spec (Y.presheaf.stalk y))
    (hp : (maximalIdeal (X.presheaf.stalk (f y))).map (f.stalkMap y).hom ≤ p.asIdeal) :
    f (Y.fromSpecStalk y p) = f y := by
  have e := congrArg (fun g => g p) (Scheme.SpecMap_stalkMap_fromSpecStalk f (x := y))
  simp only [Scheme.Hom.comp_apply] at e
  rw [← e, Spec.map_apply]
  have : PrimeSpectrum.comap (f.stalkMap y).hom p = closedPoint (X.presheaf.stalk (f y)) := by
    ext1
    exact (Ideal.map_le_iff_le_comap.mp hp).antisymm' (le_maximalIdeal (Ideal.IsPrime.ne_top
      (PrimeSpectrum.comap (f.stalkMap y).hom p).2))
  rw [this, Scheme.fromSpecStalk_closedPoint]

/-- Germs of sections of an ideal sheaf at `x` generize to germs of sections at `y ⤳ x`. -/
private theorem map_stalkIdeal_le {X : Scheme.{u}} (I : X.IdealSheafData) {x y : X} (h : y ⤳ x) :
    (I.stalkIdeal x).map (X.presheaf.stalkSpecializes h).hom ≤ I.stalkIdeal y := by
  rw [Ideal.map_le_iff_le_comap]
  refine iSup_le fun U => Ideal.map_le_iff_le_comap.2 fun a ha => ?_
  have e := congrArg (fun g => g.hom a) (X.presheaf.germ_stalkSpecializes (U := U.1.1) U.2 h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
  rw [e]
  exact I.germ_mem_stalkIdeal U.1 _ ha

/-- At a point of the support, the stalk of an ideal sheaf is a proper ideal. -/
private theorem stalkIdeal_le_maximalIdeal {X : Scheme.{u}} (I : X.IdealSheafData) {x : X}
    (hx : x ∈ I.support) : I.stalkIdeal x ≤ maximalIdeal (X.presheaf.stalk x) := by
  obtain ⟨z, rfl⟩ : x ∈ Set.range I.subschemeι := by rw [I.range_subschemeι]; exact hx
  rw [← I.ker_stalkMap_subschemeι z]
  intro a ha
  by_contra hna
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hna
  exact (hna.map (I.subschemeι.stalkMap z).hom).ne_zero ha

/-- **Functions vanishing on `Z` vanish on a prime divisor mapping into `Z`.** If `f` sends the
generic point of the prime divisor `E` of `Y` into the closed set `Z`, then at every `y` the
stalk map sends the ideal of `Z` at `f y` into the ideal of `E` at `y`. -/
private theorem stalkMap_mem_stalk_idealSheaf {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : MMP.Mori.PrimeDivisor Y) (Z : TopologicalSpace.Closeds X) (hE : f E.genericPoint ∈ Z)
    (y : Y) {a : X.presheaf.stalk (f y)}
    (ha : a ∈ (Scheme.IdealSheafData.vanishingIdeal Z).stalkIdeal (f y)) :
    (f.stalkMap y).hom a ∈ IdealSheafData.stalk E.idealSheaf y := by
  by_cases hy : y ∈ E.support
  swap
  · rw [(Stacks.Divisors.stalk_eq_top_iff_notMem_support _ _).mpr hy]; trivial
  obtain ⟨q, hq, hI, -⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E hy
  rw [hI]
  have hsp : Y.fromSpecStalk y q ⤳ y := by
    have : Y.fromSpecStalk y q ∈ Set.range (Y.fromSpecStalk y) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  rw [← under_maximalIdeal_stalk_fromSpecStalk y q hsp, Ideal.mem_comap, ← CommRingCat.comp_apply,
    ← Scheme.Hom.stalkSpecializes_stalkMap f _ _ hsp, CommRingCat.comp_apply]
  refine map_nonunit _ _ (stalkIdeal_le_maximalIdeal _ ?_ (map_stalkIdeal_le _ _
    (Ideal.mem_map_of_mem _ ha)))
  rw [TopologicalSpace.Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal Z), hq]
  exact hE

/-- The local rings at the points of the smooth locus over a field are regular. -/
private theorem isRegularLocalRing_stalk_of_mem_smoothLocus {k : Type u} [Field k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) {y : Y} (hy : y ∈ MMP.Mori.smoothLocus sY) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨V, hyV, hV⟩ := MMP.Mori.mem_smoothLocus_iff.1 hy
  haveI : Smooth (V.ι ≫ sY) := hV
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sY) ⟨y, hyV⟩
  exact IsRegularLocalRing.of_ringEquiv (V.stalkIso ⟨y, hyV⟩).commRingCatIsoToRingEquiv

/-- **A prime divisor is generically regular.** For a prime divisor `E` of a scheme locally of
finite type over a perfect field, there is an open `V` containing the generic point of `E` such
that `𝒪_{Y,y}/I_{E,y}` is regular at every point `y ∈ E ∩ V`. -/
private theorem exists_opens_isRegularLocalRing_quotient {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (E : MMP.Mori.PrimeDivisor Y) :
    ∃ V : Y.Opens, E.genericPoint ∈ V ∧ ∀ y ∈ V, y ∈ E.support →
      IsRegularLocalRing (Y.presheaf.stalk y ⧸ IdealSheafData.stalk E.idealSheaf y) := by
  haveI := E.integral
  set ι := E.idealSheaf.subschemeι
  haveI : IsLocallyNoetherian E.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sY)
  obtain ⟨t, ht, hpre⟩ :=
    ι.isEmbedding.isInducing.isOpen_iff.mp (MMP.Mori.smoothLocus (ι ≫ sY)).2
  refine ⟨⟨t, ht⟩, ?_, fun y hyV hyE => ?_⟩
  · change ι (genericPoint _) ∈ t
    rw [← Set.mem_preimage, hpre]
    exact MMP.Threefold.Mori.OpenRestriction.genericPoint_mem_smoothLocus'
  · obtain ⟨z, rfl⟩ : y ∈ Set.range ι := by rw [E.idealSheaf.range_subschemeι]; exact hyE
    have hz : z ∈ MMP.Mori.smoothLocus (ι ≫ sY) := by
      change z ∈ (MMP.Mori.smoothLocus (ι ≫ sY)).carrier
      rw [← hpre]; exact hyV
    haveI := isRegularLocalRing_stalk_of_mem_smoothLocus (ι ≫ sY) hz
    rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk]
    exact IsRegularLocalRing.of_ringEquiv
      (RingHom.quotientKerEquivOfSurjective (ι.stalkMap_surjective z)).symm

open MMP.Mori in
/-- In a regular local ring, a nonzero `a ∈ 𝔪` with `A ⧸ (a)` regular is the first member of a
regular system of parameters. -/
private theorem exists_isRegularSystemOfParameters_cons {A : Type*} [CommRing A]
    [IsRegularLocalRing A] {a : A} (ham : a ∈ maximalIdeal A) (ha0 : a ≠ 0)
    (hreg : IsRegularLocalRing (A ⧸ Ideal.span {a})) :
    ∃ (n : ℕ) (z : Fin (n + 1) → A), IsRegularSystemOfParameters z ∧ z 0 = a := by
  have := IsRegularLocalRing.isDomain A
  have hdim : ringKrullDim (A ⧸ Ideal.span (Set.range ![a])) + (1 : ℕ) = ringKrullDim A := by
    rw [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
    exact_mod_cast Module.ringKrullDim_quotient_add_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero ha0) (p := maximalIdeal A)
      maximalIdeal_height_eq_ringKrullDim ham
  have hq : IsRegularLocalRing (A ⧸ Ideal.span (Set.range ![a])) := by
    rwa [Matrix.range_cons, Matrix.range_empty, Set.union_empty]
  obtain ⟨m, t, ht⟩ :=
    (MMP.Flips.ResolutionInputs.isRegularLocalRing_quotient_and_add_eq_iff ![a]).1 ⟨hq, hdim⟩
  refine ⟨m, Fin.cons a t, ⟨?_, ?_⟩, rfl⟩
  · rw [← ht.1, Fin.range_cons, MMP.Flips.ResolutionInputs.range_append, Matrix.range_cons,
      Matrix.range_empty, Set.union_empty, Set.insert_eq]
  · rw [ht.2]; push_cast; ring

open MMP.Mori in
/-- A regular system of parameters stays one after a permutation. -/
private theorem IsRegularSystemOfParameters.comp_equiv {A : Type*} [CommRing A] [IsLocalRing A]
    {n : ℕ} {z : Fin n → A} (hz : IsRegularSystemOfParameters z) (σ : Equiv.Perm (Fin n)) :
    IsRegularSystemOfParameters (z ∘ σ) := by
  refine ⟨?_, hz.2⟩
  rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  exact hz.1

/-- In a factorial domain a prime of height one is principal. -/
private theorem exists_eq_span_singleton_of_height_eq_one {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {q : Ideal R} [q.IsPrime] (hq : q.height = 1) :
    ∃ t : R, t ≠ 0 ∧ q = Ideal.span {t} := by
  obtain ⟨t, rfl⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hq).principal
  refine ⟨t, ?_, rfl⟩
  rintro rfl
  simp at hq

/-- **The local ring of a closed subvariety has dimension at most its dimension.** For an
irreducible closed subset `W` of a scheme locally of finite type over a field and `x ∈ W`,
`dim 𝒪_{X,x}/I_{W,x} ≤ dim W`. -/
private theorem ringKrullDim_quotient_stalkIdeal_le {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (W : TopologicalSpace.IrreducibleCloseds X)
    {x : X} (hx : x ∈ (W : Set X)) :
    ringKrullDim (X.presheaf.stalk x ⧸
        (Scheme.IdealSheafData.vanishingIdeal ⟨W, W.isClosed⟩).stalkIdeal x) ≤
      topologicalKrullDim (W : Set X) := by
  set I := Scheme.IdealSheafData.vanishingIdeal ⟨(W : Set X), W.isClosed⟩
  have hrange : Set.range I.subschemeι = (W : Set X) :=
    I.range_subschemeι.trans (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  obtain ⟨z, rfl⟩ : x ∈ Set.range I.subschemeι := hrange ▸ hx
  have hemb := I.subschemeι.isEmbedding
  -- the subscheme is integral
  haveI : IrreducibleSpace I.subscheme := by
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hrange]; exact isIrreducible_iff_irreducibleSpace.mp W.isIrreducible
    exact (Homeomorph.irreducibleSpace_iff hemb.toHomeomorph).mpr this
  haveI := isIntegral_of_irreducibleSpace_of_isReduced I.subscheme
  -- dimension of the local ring is the coheight of the point
  have e1 : ringKrullDim (X.presheaf.stalk (I.subschemeι z) ⧸ I.stalkIdeal (I.subschemeι z)) =
      ringKrullDim (I.subscheme.presheaf.stalk z) :=
    ringKrullDim_eq_of_ringEquiv (I.subschemeStalkRingEquiv z)
  rw [e1, ringKrullDim_stalk_eq_coheight]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight (I.subschemeι ≫ sX) z
  have h0 : 0 ≤ topologicalKrullDim (closure ({z} : Set I.subscheme)) := by
    haveI : Nonempty (closure ({z} : Set I.subscheme)) := ⟨⟨z, subset_closure rfl⟩⟩
    exact Stacks.TwistedSheafEuler.topologicalKrullDim_nonneg
  have h1 : topologicalKrullDim I.subscheme ≤ topologicalKrullDim (W : Set X) := by
    have hind : Topology.IsInducing (fun z' : I.subscheme => (⟨I.subschemeι z', by
        rw [← hrange]; exact ⟨z', rfl⟩⟩ : (W : Set X))) :=
      hemb.isInducing.codRestrict _
    exact hind.topologicalKrullDim_le
  calc ((Order.coheight z : ℕ∞) : WithBot ℕ∞)
      ≤ topologicalKrullDim (closure ({z} : Set I.subscheme)) + Order.coheight z :=
        le_add_of_nonneg_left h0
    _ = topologicalKrullDim I.subscheme := h
    _ ≤ _ := h1

end GeneralPosition

section Constructible

open Topology Set.Notation

/-- Near a point `x`, a constructible set either contains or misses all of the closure of `x`. -/
private theorem exists_isOpen_closure_inter_of_isConstructible {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsConstructible s) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      (closure {x} ∩ U ⊆ s ∨ closure {x} ∩ U ⊆ sᶜ) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases hx : x ∈ U
    · exact ⟨U, hU, hx, Or.inl Set.inter_subset_right⟩
    · refine ⟨Set.univ, isOpen_univ, trivial, Or.inr fun y ⟨hy, _⟩ hyU => hx ?_⟩
      exact (specializes_iff_mem_closure.mpr hy).mem_open hU hyU
  | union s _ t _ ihs iht =>
    obtain ⟨U, hU, hxU, hs⟩ := ihs
    obtain ⟨V, hV, hxV, ht⟩ := iht
    refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
    rcases hs with hs | hs
    · exact Or.inl fun y ⟨hy, hyU, _⟩ => Or.inl (hs ⟨hy, hyU⟩)
    rcases ht with ht | ht
    · exact Or.inl fun y ⟨hy, _, hyV⟩ => Or.inr (ht ⟨hy, hyV⟩)
    · exact Or.inr fun y ⟨hy, hyU, hyV⟩ h => h.elim (hs ⟨hy, hyU⟩) (ht ⟨hy, hyV⟩)
  | compl s _ ih =>
    obtain ⟨U, hU, hxU, h⟩ := ih
    exact ⟨U, hU, hxU, h.symm.imp id fun h' => by rwa [compl_compl]⟩

/-- **A locally constructible set through `x` contains a neighbourhood of `x` in its closure.**
If `s` is locally constructible and `x ∈ s`, then `closure {x} ∩ U ⊆ s` for an open `U ∋ x`. -/
private theorem exists_isOpen_closure_inter_subset_of_isLocallyConstructible {X : Type*}
    [TopologicalSpace X] {s : Set X} (hs : IsLocallyConstructible s) {x : X} (hx : x ∈ s) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ closure {x} ∩ U ⊆ s := by
  obtain ⟨O, hOx, hO, hOs⟩ := hs x
  have hxO : x ∈ O := mem_of_mem_nhds hOx
  obtain ⟨U', hU', hxU', h⟩ := exists_isOpen_closure_inter_of_isConstructible hOs ⟨x, hxO⟩
  obtain ⟨U, hU, rfl⟩ := isOpen_induced_iff.mp hU'
  refine ⟨U ∩ O, hU.inter hO, ⟨hxU', hxO⟩, fun y ⟨hy, hyU, hyO⟩ => ?_⟩
  have hy' : (⟨y, hyO⟩ : O) ∈ closure {(⟨x, hxO⟩ : O)} := by
    rw [← specializes_iff_mem_closure, ← Topology.IsInducing.subtypeVal.specializes_iff]
    exact specializes_iff_mem_closure.mpr hy
  rcases h with h | h
  · exact h ⟨hy', hyU⟩
  · exact (h ⟨subset_closure rfl, hxU'⟩ hx).elim

end Constructible

section HeightBound

open IsLocalRing

/-- **Krull's height theorem over a subvariety.** Let `φ : R → A` be a local homomorphism of
Noetherian local rings, `I` an ideal of `R` with `dim R ⧸ I ≤ d`, and `t ∈ 𝔪_A` with
`φ(I) ⊆ (t)`. A prime `p` of `A` minimal over `φ(𝔪_R) A + (t)` has height at most `d + 1`: it
is minimal over `t` and the images of lifts of `d` generators of an ideal of definition of
`R ⧸ I`. -/
private theorem exists_isPrime_height_le_add_one {R A : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (φ : R →+* A)
    [IsLocalHom φ] {I : Ideal R} {d : ℕ} (hI : ringKrullDim (R ⧸ I) ≤ d) {t : A}
    (ht : t ∈ maximalIdeal A) (hIt : I.map φ ≤ Ideal.span {t}) :
    ∃ p : Ideal A, p.IsPrime ∧ t ∈ p ∧ (maximalIdeal R).map φ ≤ p ∧ p.height ≤ d + 1 := by
  classical
  have htm : Ideal.span {t} ≤ maximalIdeal A := (Ideal.span_singleton_le_iff_mem _).2 ht
  have hmap : (maximalIdeal R).map φ ≤ maximalIdeal A :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => map_nonunit φ x hx
  have hItop : I ≠ ⊤ := by
    intro h
    have : (⊤ : Ideal R).map φ ≤ maximalIdeal A := h ▸ hIt.trans htm
    rw [Ideal.map_top] at this
    exact (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp this)
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (R ⧸ I) :=
    .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmk : (maximalIdeal (R ⧸ I)).comap (Ideal.Quotient.mk I) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _
      Ideal.Quotient.mk_surjective)
  obtain ⟨s, hs, hcard⟩ :=
    (maximalIdeal (R ⧸ I)).exists_finset_card_eq_height_of_isNoetherianRing
  choose g hg using fun r : R ⧸ I => Ideal.Quotient.mk_surjective r
  set J := (maximalIdeal R).map φ ⊔ Ideal.span {t} with hJ
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (sup_le hmap htm)
  have hpp : p.IsPrime := hp.1.1
  have hJp : J ≤ p := hp.1.2
  set L : Finset A := insert t (s.image fun r => φ (g r)) with hLdef
  have hL : p ∈ (Ideal.span (L : Set A)).minimalPrimes := by
    refine ⟨⟨hpp, Ideal.span_le.2 ?_⟩, fun q ⟨hq, hLq⟩ hqp => ?_⟩
    · intro a ha
      simp only [L, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
        Finset.mem_coe] at ha
      rcases ha with rfl | ⟨r, hr, rfl⟩
      · exact hJp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
      · refine hJp (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ?_))
        rw [← hmk, Ideal.mem_comap, hg r]
        exact hs.1.2 (Ideal.subset_span hr)
    · have htq : t ∈ q := hLq (Ideal.subset_span (Finset.mem_insert_self _ _))
      have hIq : I ≤ q.comap φ := fun a ha =>
        Ideal.mem_comap.mpr ((hIt.trans ((Ideal.span_singleton_le_iff_mem _).2 htq))
          (Ideal.mem_map_of_mem φ ha))
      have hq₀ : ((q.comap φ).map (Ideal.Quotient.mk I)).IsPrime :=
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
      have hsq : Ideal.span (s : Set (R ⧸ I)) ≤ (q.comap φ).map (Ideal.Quotient.mk I) := by
        rw [Ideal.span_le]
        intro r hr
        rw [← hg r]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr (hLq (Ideal.subset_span
          (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hr)))))
      have hm := hs.2 ⟨hq₀, hsq⟩ (IsLocalRing.le_maximalIdeal hq₀.ne_top)
      have hmq : (maximalIdeal R).map φ ≤ q := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [← hmk] at ha
        exact (Ideal.mem_quotient_iff_mem hIq).mp (hm ha)
      exact hp.2 ⟨hq, sup_le hmq ((Ideal.span_singleton_le_iff_mem _).2 htq)⟩ hqp
  refine ⟨p, hpp, hJp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)),
    le_sup_left.trans hJp, ?_⟩
  have h2 : L.card ≤ s.card + 1 :=
    (Finset.card_insert_le _ _).trans (by gcongr; exact Finset.card_image_le)
  have h3 : ((s.card : ℕ∞) : WithBot ℕ∞) ≤ d := by
    rwa [hcard, IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have h3' : s.card ≤ d := by exact_mod_cast h3
  calc p.height ≤ L.card := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hL
    _ ≤ ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast h2.trans (by omega)
    _ = d + 1 := by push_cast; rfl

end HeightBound

section Assembly

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

/-- A divisor over a normal variety of dimension at least two whose centre is a closed point is
exceptional. -/
private theorem isExceptional_of_isClosed {k : Type u} [Field k] {S : Scheme.{u}}
    {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    (hS : IsNormalVariety k sS) {n : ℕ} (hn : topologicalKrullDim S = n) (hn2 : 2 ≤ n)
    (D : DivisorOver k sS) (hD : IsClosed ({D.f D.E.genericPoint} : Set S)) :
    D.IsExceptional := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sS := hS.1.toIsSeparated
  have : IsSeparated (S ↘ ⊤_ Scheme) := by
    rw [show (S ↘ ⊤_ Scheme) = sS ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set S), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sS
    (D.f D.E.genericPoint)
  rw [hD.closure_eq, hn] at h
  have h0 : topologicalKrullDim ({D.f D.E.genericPoint} : Set S) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  have h2 : ((n : ℕ) : WithBot ℕ∞) ≤ (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) := by
    rw [← h]
    calc topologicalKrullDim ({D.f D.E.genericPoint} : Set S) +
          (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞)
        ≤ 0 + (Order.coheight (D.f D.E.genericPoint) : WithBot ℕ∞) := by gcongr
      _ = _ := zero_add _
  have h3 : (n : ℕ∞) ≤ Order.coheight (D.f D.E.genericPoint) := by exact_mod_cast h2
  exact le_trans (by exact_mod_cast hn2) h3

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori in
/-- **The good locus on the model of a divisor.** For a divisor `(Y, f, E)` over a normal variety
over a field of characteristic zero and a rational form `τ`, there is an open `U ⊆ Y` containing
the generic point of `E` at whose points `Y` is regular, `E` is regular, and no prime divisor
other than `E` along which `f^*τ` has nonzero order passes. -/
private theorem exists_opens_forall_isRegularLocalRing {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)} (E : DivisorOver k sX) {n : ℕ}
    {m : ℤ} (τ : RationalPluriForms sX n m) :
    haveI := E.isIntegral; haveI := E.isLocallyNoetherian; haveI := E.isDominant
    ∃ U : E.Y.Opens, E.E.genericPoint ∈ U ∧ ∀ y ∈ U,
      IsRegularLocalRing (E.Y.presheaf.stalk y) ∧
      (y ∈ E.E.support →
        IsRegularLocalRing (E.Y.presheaf.stalk y ⧸ IdealSheafData.stalk E.E.idealSheaf y)) ∧
      ∀ F : MMP.Mori.PrimeDivisor E.Y, y ∈ F.support → F ≠ E.E →
        F.ordForm (pullbackRationalPluriForms sX E.f τ) = 0 := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have hYv := E.isNormalVariety
  haveI : AlgebraicGeometry.IsVariety k (E.f ≫ sX) := hYv.1
  have : LocallyOfFiniteType (E.f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  obtain ⟨U₂, hηU₂, hU₂⟩ := exists_opens_isRegularLocalRing_quotient (E.f ≫ sX) E.E
  have hfin := MMP.Mori.finite_ordForm_ne_zero (sX := E.f ≫ sX)
    (pullbackRationalPluriForms sX E.f τ)
  set bad := {F : MMP.Mori.PrimeDivisor E.Y |
    F.ordForm (pullbackRationalPluriForms sX E.f τ) ≠ 0} \ {E.E} with hbad
  have hC : IsClosed (⋃ F ∈ bad, (F.support : Set E.Y)) :=
    (hfin.diff).isClosed_biUnion fun F _ => by
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  let U₃ : E.Y.Opens := ⟨_, hC.isOpen_compl⟩
  refine ⟨MMP.Mori.smoothLocus (E.f ≫ sX) ⊓ U₂ ⊓ U₃, ⟨⟨?_, hηU₂⟩, ?_⟩,
    fun y ⟨⟨hy1, hy2⟩, hy3⟩ => ⟨isRegularLocalRing_stalk_of_mem_smoothLocus _ hy1,
      hU₂ y hy2, fun F hF hFE => ?_⟩⟩
  · exact MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hYv E.E
  · intro hmem
    obtain ⟨F, ⟨-, hF2⟩, hF⟩ := Set.mem_iUnion₂.mp hmem
    exact hF2 (MMP.Positivity.PrimeDivisor.eq_of_genericPoint_specializes
      (MMP.Resolution.Aux.genericPoint_specializes_of_mem_support F hF))
  · by_contra h
    exact hy3 (Set.mem_iUnion₂.mpr ⟨F, ⟨h, hFE⟩, hF⟩)

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology MMP.Mori in
/-- **Chevalley over the centre.** If `U` is an open of the model `Y` of a divisor `E` over a
variety `X` containing the generic point of `E`, then `f(E ∩ U)` contains `W ∩ V` for an open
`V ⊆ X` containing the generic point of the centre `W` of `E`: the image is locally
constructible and contains the generic point of `W`. -/
private theorem exists_isOpen_center_inter_subset_image {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {sX : X ⟶ Spec (.of k)}
    (E : DivisorOver k sX) (U : E.Y.Opens) (hU : E.E.genericPoint ∈ U) :
    ∃ V : Set X, IsOpen V ∧ E.f E.E.genericPoint ∈ V ∧
      (E.center : Set X) ∩ V ⊆ E.f '' ((E.E.support : Set E.Y) ∩ U) := by
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have hYv := E.isNormalVariety
  haveI : AlgebraicGeometry.IsVariety k (E.f ≫ sX) := hYv.1
  have : LocallyOfFiniteType (E.f ≫ sX) := hYv.1.toLocallyOfFiniteType
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  haveI : IsNoetherian E.Y := ⟨⟩
  have : NoetherianSpace E.Y := inferInstance
  have : LocallyOfFiniteType E.f := LocallyOfFiniteType.of_comp (f := E.f) (g := sX) inferInstance
  have : LocallyOfFinitePresentation E.f := inferInstance
  have : QuasiCompact E.f := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hretro : ∀ s : Set E.Y, IsRetrocompact s := fun _ _ _ _ => NoetherianSpace.isCompact _
  have hcl : IsClosed (E.E.support : Set E.Y) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hS : IsConstructible ((E.E.support : Set E.Y) ∩ U) := by
    refine IsConstructible.inter ?_ ((hretro _).isConstructible U.2)
    simpa using ((hretro _).isConstructible hcl.isOpen_compl).compl
  have hT := E.f.isLocallyConstructible_image hS.isLocallyConstructible
  have hx0 : E.f E.E.genericPoint ∈ E.f '' ((E.E.support : Set E.Y) ∩ U) := by
    refine ⟨_, ⟨?_, hU⟩, rfl⟩
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  obtain ⟨V, hV, hxV, hVs⟩ := exists_isOpen_closure_inter_subset_of_isLocallyConstructible hT hx0
  refine ⟨V, hV, hxV, ?_⟩
  rw [← (E.isGenericPoint_center : closure _ = _)]
  exact hVs

/-- **General position.** Let `E` be a divisor over `X` with centre `W` of dimension `d > 0`.
There is an open `V` meeting `W` such that over every closed point `x ∈ W ∩ V` some point `η` of
the model `Y` of `E` has: `𝒪_{Y,η}` regular of dimension `c + 2 ≤ d + 1`, with a regular system
of parameters `z` whose `z₁` is an equation of `E`; no other prime divisor through `η` along which
`f^*τ` has nonzero order; and `I_{W,x}` pulled back into `(z₁)`. Here `V` is cut out by
Chevalley's theorem applied to the good locus of `E`. The point `η` is a prime of `𝒪_{Y,η₀}`
minimal over `𝔪_x` and the equation of `E`, for any `η₀` over `x` in that locus, and Krull's
height theorem bounds its dimension. -/
private theorem exists_open_forall_exists_regular_point {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (E : DivisorOver k sX) {m : ℤ}
    (τ : RationalPluriForms sX n m) (W : IrreducibleCloseds X) (hEW : E.center = W) {d : ℕ}
    (hd : 0 < d) (hWd : topologicalKrullDim (W : Set X) = d) :
    ∃ V : X.Opens, ((W : Set X) ∩ V).Nonempty ∧ ∀ x ∈ (W : Set X) ∩ V,
      IsClosed ({x} : Set X) → ∃ η : E.Y, E.f η = x ∧
        IsRegularLocalRing (E.Y.presheaf.stalk η) ∧ ∃ c : ℕ, c + 1 ≤ d ∧
          ∃ z : Fin (c + 2) → E.Y.presheaf.stalk η, IsRegularSystemOfParameters z ∧
            (haveI := E.isIntegral;
              IdealSheafData.stalk E.E.idealSheaf η = Ideal.span {z 1}) ∧
            (haveI := E.isIntegral; haveI := E.isLocallyNoetherian; haveI := E.isDominant;
              ∀ F : MMP.Mori.PrimeDivisor E.Y, η ∈ F.support → F ≠ E.E →
                F.ordForm (pullbackRationalPluriForms sX E.f τ) = 0) ∧
            ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal ⟨W, W.isClosed⟩).stalkIdeal (E.f η),
              (E.f.stalkMap η).hom a ∈ Ideal.span {z 1} := by
  classical
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  obtain ⟨UY, hηUY, hUY⟩ := exists_opens_forall_isRegularLocalRing E τ
  obtain ⟨V, hV, hgV, hVs⟩ := exists_isOpen_center_inter_subset_image E UY hηUY
  have hgen : IsGenericPoint (E.f E.E.genericPoint) (W : Set X) := by
    rw [← hEW]; exact E.isGenericPoint_center
  refine ⟨⟨V, hV⟩, ⟨_, hgen.mem, hgV⟩, fun x ⟨hxW, hxV⟩ hxc => ?_⟩
  obtain ⟨η₀, ⟨hη₀E, hη₀U⟩, rfl⟩ := hVs ⟨by rw [hEW]; exact hxW, hxV⟩
  -- the local ring at `η₀`
  haveI := (hUY η₀ hη₀U).1
  haveI := IsRegularLocalRing.isDomain (E.Y.presheaf.stalk η₀)
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (E.Y.presheaf.stalk η₀)
  obtain ⟨q, -, hqI, hqh⟩ := MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E.E hη₀E
  obtain ⟨t, -, htq⟩ := exists_eq_span_singleton_of_height_eq_one hqh
  have ht : t ∈ IsLocalRing.maximalIdeal (E.Y.presheaf.stalk η₀) :=
    IsLocalRing.le_maximalIdeal q.2.ne_top (htq ▸ Ideal.mem_span_singleton_self t)
  have hIt : ((Scheme.IdealSheafData.vanishingIdeal ⟨W, W.isClosed⟩).stalkIdeal
      (E.f η₀)).map (E.f.stalkMap η₀).hom ≤ Ideal.span {t} := by
    rw [Ideal.map_le_iff_le_comap, ← htq, ← hqI]
    intro a ha
    exact stalkMap_mem_stalk_idealSheaf E.f E.E ⟨W, W.isClosed⟩ hgen.mem η₀ ha
  have hdimW := (ringKrullDim_quotient_stalkIdeal_le sX W hxW).trans hWd.le
  obtain ⟨p, hp, htp, hmp, hph⟩ := exists_isPrime_height_le_add_one (E.f.stalkMap η₀).hom
    hdimW ht hIt
  -- the generization `η` of `η₀` at `p`
  set η := E.Y.fromSpecStalk η₀ ⟨p, hp⟩ with hηdef
  have hηη₀ : η ⤳ η₀ := by
    have : η ∈ Set.range (E.Y.fromSpecStalk η₀) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hfη : E.f η = E.f η₀ := hom_fromSpecStalk_eq E.f η₀ ⟨p, hp⟩ hmp
  have hηU : η ∈ UY := hηη₀.mem_open UY.2 hη₀U
  have hηE : η ∈ E.E.support := by
    obtain ⟨q₁, hq₁, hq₁I, -⟩ :=
      MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E.E hη₀E
    have hle : q₁ ≤ ⟨p, hp⟩ := by
      change q₁.asIdeal ≤ p
      rw [← hq₁I, hqI, htq, Ideal.span_le, Set.singleton_subset_iff]
      exact htp
    have hsp := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map
      (E.Y.fromSpecStalk η₀).continuous
    rw [hq₁] at hsp
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact specializes_iff_mem_closure.mp hsp
  obtain ⟨hηreg, hηEreg, hηF⟩ := hUY η hηU
  haveI := hηreg
  haveI := IsRegularLocalRing.isDomain (E.Y.presheaf.stalk η)
  haveI := IsRegularLocalRing.uniqueFactorizationMonoid (E.Y.presheaf.stalk η)
  have hηdim : ringKrullDim (E.Y.presheaf.stalk η) = p.height :=
    ringKrullDim_stalk_fromSpecStalk η₀ ⟨p, hp⟩
  -- a regular system of parameters at `η` starting with the equation of `E`
  obtain ⟨q', hq'gen, hq'I, hq'h⟩ :=
    MMP.Intersection.exists_stalk_idealSheaf_eq_of_mem_support E.E hηE
  obtain ⟨t', ht'0, ht'q⟩ := exists_eq_span_singleton_of_height_eq_one hq'h
  have ht'm : t' ∈ IsLocalRing.maximalIdeal (E.Y.presheaf.stalk η) :=
    IsLocalRing.le_maximalIdeal q'.2.ne_top (ht'q ▸ Ideal.mem_span_singleton_self t')
  have hreg' : IsRegularLocalRing (E.Y.presheaf.stalk η ⧸ Ideal.span {t'}) := by
    rw [← ht'q, ← hq'I]; exact hηEreg hηE
  obtain ⟨n', z', hz', hz'0⟩ := exists_isRegularSystemOfParameters_cons ht'm ht'0 hreg'
  have hn'd : ((n' + 1 : ℕ) : ℕ∞) ≤ ((d + 1 : ℕ) : ℕ∞) := by
    have h := hz'.2
    rw [hηdim] at h
    have : (p.height : WithBot ℕ∞) = ((n' + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
    rw [← WithBot.coe_inj.mp this]
    push_cast
    exact hph
  have hn'd' : n' ≤ d := by
    have := (Nat.cast_le (α := ℕ∞)).mp hn'd
    omega
  -- `η` is not the generic point of `E`, since `W` is not a point
  obtain ⟨c, rfl⟩ : ∃ c, n' = c + 1 := by
    refine ⟨n' - 1, ?_⟩
    by_contra hne
    have hn0 : n' = 0 := by omega
    subst hn0
    have h1 : (IsLocalRing.maximalIdeal (E.Y.presheaf.stalk η)).height = 1 := by
      have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := E.Y.presheaf.stalk η)
      rw [hz'.2] at this
      exact_mod_cast this
    have hq'm : q'.asIdeal = IsLocalRing.maximalIdeal _ := by
      by_contra hne'
      have hlt := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal q'.2.ne_top) hne'
      have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [hq'h, h1] at this
      norm_num at this
    have hq'c : q' = IsLocalRing.closedPoint _ := PrimeSpectrum.ext hq'm
    have hηg : η = E.E.genericPoint := by
      rw [← hq'gen, hq'c, Scheme.fromSpecStalk_closedPoint]
    have hWx : (W : Set X) = {E.f η₀} := by
      rw [← (hgen : closure _ = _), ← hηg, hfη, hxc.closure_eq]
    have h0 : topologicalKrullDim ({E.f η₀} : Set X) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hWx] at hWd
    rw [hWd] at h0
    have : d ≤ 0 := by exact_mod_cast h0
    omega
  refine ⟨η, hfη, hηreg, c, by omega, z' ∘ Equiv.swap 0 1,
    IsRegularSystemOfParameters.comp_equiv hz' _, ?_, fun F hF hFE => hηF F hF hFE,
    fun a ha => ?_⟩
  · rw [hq'I, ht'q]
    simp [hz'0]
  · have h := stalkMap_mem_stalk_idealSheaf E.f E.E ⟨W, W.isClosed⟩ hgen.mem η ha
    rw [hq'I, ht'q] at h
    simpa [hz'0] using h

end Assembly

end Proof_lem_mmp_lc_bpf_centre_concentration_valuation

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
open Proof_lem_mmp_lc_bpf_centre_concentration_valuation
open scoped WithZero

namespace MMP.Mori

/-- Let `(X, B)` be an lc pair over an algebraically closed field `k` of characteristic zero,
with canonical divisor `K` of dimension `n`, and let `W` be an lc centre of `(X, B)` (the centre
of a divisor `E` over `X` with `a(E, X, B) = -1`) of dimension `d > 0`. Then there is an open
`V ⊆ X` meeting `W` such that for every closed point `x ∈ W ∩ V` at which `W` is smooth
(`𝒪_{X,x}/I_{W,x}` regular) and every effective `ℚ`-Cartier divisor `G` with `W ⊄ Supp G` and
`mult_x (G|_W) > d` (a local equation `g` at `x` of a Cartier multiple `qG`, `q > 0`, lies in
`𝔪_x^{qd+1} + I_{W,x}`), the pair `(X, B + G)` is not lc at `x`. -/
@[mmp "lem_mmp_lc_bpf_centre_concentration_valuation"]
public theorem not_isAt_isLcPair_add_of_mem_maximalIdeal_pow_sup
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of k)) {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hB : IsLcPair sX n K B) (W : IrreducibleCloseds X)
    (hW : ∃ E : DivisorOver k sX, E.center = W ∧ IsDiscrepancy sX n K B E (-1))
    {d : ℕ} (hd : 0 < d) (hWd : topologicalKrullDim (W : Set X) = d) :
    ∃ V : X.Opens, ((W : Set X) ∩ V).Nonempty ∧
      ∀ x ∈ (W : Set X) ∩ V, IsClosed ({x} : Set X) →
        IsRegularLocalRing (X.presheaf.stalk x ⧸
          (Scheme.IdealSheafData.vanishingIdeal ⟨W, W.isClosed⟩).stalkIdeal x) →
        ∀ G : QDivisor X, G.IsEffective → G.IsQCartier → ¬ ((W : Set X) ⊆ G.supp) →
          (∃ q : ℕ, 0 < q ∧ ∃ D : Divisor X, Divisor.toQDivisor D = (q : ℤ) • G ∧
            ∃ U : X.Opens, x ∈ U ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation U φ ∧
              ∃ g : X.presheaf.stalk x,
                (∀ (Z : irreducibleComponents X) (hZ : x ∈ Z.1),
                  (φ : RationalFunctions X) Z = (stalkToRationalFunctions X hZ).hom g) ∧
                g ∈ maximalIdeal (X.presheaf.stalk x) ^ (q * d + 1) ⊔
                  (Scheme.IdealSheafData.vanishingIdeal ⟨W, W.isClosed⟩).stalkIdeal x) →
          ¬ IsAt sX (fun s n K Δ => IsLcPair s n K Δ) n K (B + G) x := by
  obtain ⟨E, hEc, hEa⟩ := hW
  obtain ⟨hX, hK, m, hm, hmC, Uτ, hUτ, τ, hτ, hτa⟩ := hEa
  have hn := hK.topologicalKrullDim_eq
  obtain ⟨V, hVne, hV⟩ :=
    exists_open_forall_exists_regular_point hX hn E τ W hEc hd hWd
  -- the generic point of `W` lies in every open meeting `W`
  have hgen : IsGenericPoint (E.f E.E.genericPoint) (W : Set X) := by
    rw [← hEc]; exact E.isGenericPoint_center
  refine ⟨V ⊓ Uτ, ?_, ?_⟩
  · refine ⟨E.f E.E.genericPoint, hgen.mem, ?_, hUτ⟩
    obtain ⟨y, hyW, hyV⟩ := hVne
    exact (hgen.specializes hyW).mem_open V.isOpen hyV
  intro x ⟨hxW, hxV, hxU⟩ hxc _hreg G hGe hGQ hGW hmult hlc
  obtain ⟨η, hηx, hηreg, c, hcd, z, hz, hzE, hF, hI⟩ := hV x ⟨hxW, hxV⟩ hxc
  subst hηx
  obtain ⟨q, hq, Dq, hDq, Uφ, hxUφ, φ, hφ, g, hgφ, hgmem⟩ := hmult
  -- the weighted divisor, with weight `N = q d + 1` on the equation of `E`
  obtain ⟨D, hDc, hDa, hD1, hDM, hDN⟩ :=
    exists_divisorOver_isDiscrepancy_eq hX hK E hm hmC hτ hτa η hxU hz hzE hF
      (N := q * d + 1) (by omega)
  -- its value on the local equation of `qG`
  have hvg : D.valuation (algebraMap _ X.functionField g) ≤
      WithZero.exp (-((q * d + 1 : ℕ) : ℤ)) := by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hgmem
    rw [map_add]
    exact D.valuation.map_add_le (hDM _ a ha) (hDN b (hI b hb))
  -- `2 ≤ n`: the local ring of `η` has dimension `c + 2`
  have h2n : 2 ≤ n := by
    have := E.isIntegral
    have : LocallyOfFiniteType (E.f ≫ sX) := E.isNormalVariety.1.toLocallyOfFiniteType
    have hnY := topologicalKrullDim_divisorOver_Y hX hn E
    have hdη : ringKrullDim (E.Y.presheaf.stalk η) = (c + 2 : ℕ) := hz.2
    have := (trdeg_residueField_stalk (E.f ≫ sX) hnY η hdη).2
    omega
  -- the local equation of `qG` in the function field
  let Z0 : irreducibleComponents X :=
    ⟨irreducibleComponent (E.f η), irreducibleComponent_mem_irreducibleComponents _⟩
  have hZ0 : E.f η ∈ Z0.1 := mem_irreducibleComponent
  have huniv : ∀ Z : irreducibleComponents X, Z = Z0 := fun Z => Subtype.ext (by
    have h1 : Z.1 ∈ ({Set.univ} : Set (Set X)) := (irreducibleComponents_eq_singleton (X := X)) ▸ Z.2
    have h2 : Z0.1 ∈ ({Set.univ} : Set (Set X)) := (irreducibleComponents_eq_singleton (X := X)) ▸ Z0.2
    rw [Set.mem_singleton_iff] at h1 h2
    rw [h1, h2])
  set gK : X.functionField := algebraMap _ X.functionField g with hgK
  have hgKφ : ∀ Z : irreducibleComponents X,
      (MMP.Positivity.componentToFunctionField Z).hom ((φ : RationalFunctions X) Z) = gK := by
    intro Z
    obtain rfl := (huniv Z).symm
    rw [hgφ Z0 hZ0, hgK, stalkToRationalFunctions, ← CommRingCat.comp_apply,
      TopCat.Presheaf.stalkSpecializes_comp]
    rfl
  have hg0 : gK ≠ 0 := by
    rw [← hgKφ Z0]
    exact ((φ.isUnit.map (Pi.evalRingHom _ Z0)).map _).ne_zero
  have hgU : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ Uφ).Nonempty →
      (Dq.coeff Γ : ℤ) = X.ord gK Γ.genericPoint := by
    intro Γ hΓ
    rw [hφ Γ hΓ, MMP.Positivity.ord_eq_ord_componentToFunctionField, ← hgKφ Γ.component]
  obtain ⟨M, hM⟩ : ∃ M : ℤ, D.valuation gK = WithZero.exp (-M) := by
    have h0 : D.valuation gK ≠ 0 := (Valuation.ne_zero_iff _).mpr hg0
    exact ⟨-WithZero.log (D.valuation gK), by rw [neg_neg, WithZero.exp_log h0]⟩
  have hMq : ((q * d + 1 : ℕ) : ℤ) ≤ M := by
    rw [hM] at hvg
    have := WithZero.exp_le_exp.mp hvg
    omega
  -- the pair `(X, B + G)` and the discrepancy of `D` with respect to it
  have hBG : IsPairWith sX n K (B + G) :=
    ⟨hX, hK, by rw [← add_assoc]; exact hB.1.2.2.add hGQ⟩
  obtain ⟨a₀, ha₀⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hBG.isPair hK D
  have ha₀eq := isDiscrepancy_add_eq_sub hDa ha₀ hq hDq (hDc ▸ hxUφ) hg0 hgU hM
  -- restrict to the neighbourhood on which `(X, B + G)` is lc
  obtain ⟨U', hxU', hne, hP⟩ := hlc
  have hxU'' : E.f η ∈ U' := hxU' rfl
  have hcen : ((D.center : Set X) ∩ U').Nonempty := by
    refine ⟨E.f η, ?_, hxU''⟩
    rw [D.center_eq_closure_genericPoint, hDc]
    exact subset_closure rfl
  obtain ⟨hY', hf', E', hE', -, hiff⟩ :=
    DivisorOver.exists_restrict_isDiscrepancy_iff hBG D U' hcen
  have hpt : U'.ι ((D.f ∣_ U') E'.genericPoint) = E.f η := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply, ← hDc, ← hE']
    exact congrArg D.f (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm
  have hclosed : IsClosed ({(D.f ∣_ U') E'.genericPoint} : Set U') := by
    have : ({(D.f ∣_ U') E'.genericPoint} : Set U') = U'.ι ⁻¹' {E.f η} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hpt, fun h => U'.ι.isOpenEmbedding.injective (h.trans hpt.symm)⟩
    rw [this]
    exact hxc.preimage U'.ι.continuous
  have hexc := isExceptional_of_isClosed hP.1.1 hP.1.2.1.topologicalKrullDim_eq h2n
    (⟨_, D.f ∣_ U', hY', hf', E'⟩ : DivisorOver k (U'.ι ≫ sX)) hclosed
  have hle := hP.2.trans (discrep_le hexc ((hiff a₀).mp ha₀))
  have hle' : (-1 : ℚ) ≤ a₀ := by
    have : ((-1 : ℝ) : EReal) ≤ ((a₀ : ℝ) : EReal) := by simpa using hle
    exact_mod_cast EReal.coe_le_coe_iff.mp this
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq
  have hdM : (d : ℚ) < M / q := by
    rw [lt_div_iff₀ hqpos]
    have : ((q * d + 1 : ℕ) : ℚ) ≤ M := by exact_mod_cast hMq
    push_cast at this
    linarith
  have hcd' : ((c : ℕ) : ℚ) + 1 ≤ d := by exact_mod_cast hcd
  rw [ha₀eq] at hle'
  linarith

end MMP.Mori

end
