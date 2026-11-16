module

public import MMP.AlgebraicGeometry.Resolution.MaximalContact.Derivative

/-!
# Automorphisms of the form `1 + B` and derivative ideals (Kollár Prop. 3.94)

Let `k` be a field of characteristic `0`, `K / k` a field extension and
`R = K[[x_1, …, x_n]]`, viewed as a `k`-algebra, with derivative ideals `D(J) = D_{R/k}(J)` and
`D^j(J) = D^j_{R/k}(J)`. For ideals `B ⊆ 𝔪` and `I` of `R`, Kollár's Prop. 3.94 says that the
following are equivalent:

1. `g^*(I) = I` for every automorphism `g^*` of the form `1 + B`;
2. `B · D(I) ⊆ I`;
3. `B^j · D^j(I) ⊆ I` for every `j ≥ 1`.

This file states the implications (2) ⇒ (3) and (3) ⇒ (1).

## Main results

* `MMP.Resolution.Kollar.pow_mul_higherDerivativeIdealOfRing_le`: if `B · D(I) ⊆ I`, then
  `B^j · D^j(I) ⊆ I` for every `j ≥ 1`.
* `MMP.Resolution.Kollar.image_subst_eq_of_pow_mul_higherDerivativeIdealOfRing_le`: if
  `B^j · D^j(I) ⊆ I` for every `j ≥ 1`, then every automorphism `g^*` of the form `1 + B`
  satisfies `g^*(I) = I`.

## Implementation notes

The implication (2) ⇒ (3) uses only the Leibniz rule, and is stated for ideals `B`, `I` of an
arbitrary commutative algebra `R` over a commutative ring `A₀`, with the derivative ideals
`D_{R/A₀}` (`MMP.Resolution.derivativeIdealOfRing`, `MMP.Resolution.higherDerivativeIdealOfRing`).

In (3) ⇒ (1) the extension `K / k` need not be finite, and `B` need not lie in `𝔪`: only the
partial derivatives `∂_i`, which are `k`-derivations of `R`, and the elements
`g_i - x_i ∈ B ∩ 𝔪` enter. The substitution `g^*` is Mathlib's `MvPowerSeries.subst g`, and
`g^*(I) = I` is the equality of the image of `I` with `I`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Notation 3.93, Prop. 3.94]
-/

@[expose] public section

namespace MMP.Resolution.Kollar

/-- A derivation maps `B^(j+1)` into `B^j`. -/
private theorem derivation_mem_pow_of_mem_pow {A₀ : Type*} {R : Type*} [CommRing A₀] [CommRing R]
    [Algebra A₀ R] (δ : Derivation A₀ R R) (B : Ideal R) (j : ℕ) {x : R}
    (hx : x ∈ B ^ (j + 1)) : δ x ∈ B ^ j := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun m hm n hn => ?_) (fun x y hx hy => ?_)
    · rw [Derivation.leibniz]
      simp only [smul_eq_mul]
      refine add_mem (Ideal.mul_mem_right _ _ hm) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hn (ih hm)
    · rw [map_add]
      exact add_mem hx hy

/-- **Kollár Prop. 3.94, (2) ⇒ (3).** Let `B`, `I` be ideals of an `A₀`-algebra `R` with
`B · D(I) ⊆ I`, where `D = D_{R/A₀}`. Then `B^j · D^j(I) ⊆ I` for every `j ≥ 1`. -/
@[mmp "lem_kr3d_higher_condition_from_first_order"]
theorem pow_mul_higherDerivativeIdealOfRing_le (A₀ : Type*) {R : Type*} [CommRing A₀]
    [CommRing R] [Algebra A₀ R] {B I : Ideal R} (h : B * derivativeIdealOfRing A₀ I ≤ I)
    (j : ℕ) (hj : 1 ≤ j) : B ^ j * higherDerivativeIdealOfRing A₀ I j ≤ I := by
  induction j, hj using Nat.le_induction with
  | base => simpa [higherDerivativeIdealOfRing] using h
  | succ j hj ih =>
    obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    rw [higherDerivativeIdealOfRing_succ, Ideal.mul_le]
    intro r hr s hs
    induction hs using Submodule.span_induction generalizing r with
    | mem x hx =>
      obtain ⟨δ, f, hf, rfl⟩ := hx
      rw [pow_succ] at hr
      refine Submodule.mul_induction_on hr (fun b' hb' b'' hb'' => ?_) (fun x y hx hy => ?_)
      · have h5 : δ b' * b'' * f ∈ I := by
          refine ih (Ideal.mul_mem_mul ?_ hf)
          rw [pow_succ]
          exact Ideal.mul_mem_mul (derivation_mem_pow_of_mem_pow δ B m hb') hb''
        have : b' * b'' * δ f = b'' * δ (b' * f) - δ b' * b'' * f := by
          rw [Derivation.leibniz]
          simp only [smul_eq_mul]
          ring
        rw [this]
        exact I.sub_mem (h (Ideal.mul_mem_mul hb''
          (Ideal.subset_span ⟨δ, _, ih (Ideal.mul_mem_mul hb' hf), rfl⟩))) h5
      · rw [add_mul]
        exact I.add_mem hx hy
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact I.add_mem (hx r hr) (hy r hr)
    | smul a x _ hx =>
      rw [smul_eq_mul, mul_left_comm]
      exact I.mul_mem_left a (hx r hr)

section TaylorHelpers

open MvPowerSeries

variable {K : Type*} [Field K] {n : ℕ}

private theorem order_pderiv {N : ℕ} {F : MvPowerSeries (Fin n) K} (i : Fin n)
    (hF : ((N + 1 : ℕ) : ℕ∞) ≤ F.order) : (N : ℕ∞) ≤ (pderiv (R := K) i F).order := by
  refine nat_le_order fun d hd => ?_
  rw [coeff_pderiv, coeff_of_lt_order, zero_mul]
  refine lt_of_lt_of_le ?_ hF
  rw [show Finsupp.degree (d + Finsupp.single i 1) = Finsupp.degree d + 1 by simp [map_add]]
  exact_mod_cast Nat.succ_lt_succ hd

private noncomputable def taylorPoly (e : Fin n → MvPowerSeries (Fin n) K) :
    MvPolynomial (Fin n) K →ₐ[K] Polynomial (MvPowerSeries (Fin n) K) :=
  MvPolynomial.aeval fun i =>
    Polynomial.C (MvPowerSeries.X i) + Polynomial.C (e i) * Polynomial.X

private theorem derivative_taylorPoly (e : Fin n → MvPowerSeries (Fin n) K)
    (F : MvPolynomial (Fin n) K) :
    Polynomial.derivative (taylorPoly e F) =
      ∑ i, Polynomial.C (e i) * taylorPoly e (MvPolynomial.pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp [taylorPoly]
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, mul_add]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.derivative_mul, hp]
    simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, map_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : Polynomial.derivative (taylorPoly e (MvPolynomial.X j)) = Polynomial.C (e j) := by
      simp [taylorPoly]
    rw [h1, Finset.sum_mul]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
      simp only [Pi.single_eq_same, map_one]
      ring

private theorem eval_taylorPoly (e : Fin n → MvPowerSeries (Fin n) K) (a : MvPowerSeries (Fin n) K)
    (F : MvPolynomial (Fin n) K) :
    (taylorPoly e F).eval a = MvPolynomial.aeval (fun i => MvPowerSeries.X i + e i * a) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [taylorPoly]
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul]
    simp [taylorPoly]

private theorem natDegree_taylorPoly_monomial_le (e : Fin n → MvPowerSeries (Fin n) K) (d : Fin n →₀ ℕ)
    (c : K) :
    (taylorPoly e (MvPolynomial.monomial d c)).natDegree ≤ Finsupp.degree d := by
  rw [MvPolynomial.monomial_eq, map_mul, Finsupp.prod, map_prod]
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h0 : (taylorPoly e (MvPolynomial.C c)).natDegree = 0 := by
    simp [taylorPoly]
  rw [h0, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  change _ ≤ ∑ i ∈ d.support, d i
  refine Finset.sum_le_sum fun i _ => ?_
  rw [map_pow]
  refine (Polynomial.natDegree_pow_le).trans ?_
  have : (taylorPoly e (MvPolynomial.X i)).natDegree ≤ 1 := by
    simp only [taylorPoly, MvPolynomial.aeval_X]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  exact (Nat.mul_le_mul_left _ this).trans_eq (mul_one _)

private theorem natDegree_taylorPoly_le (e : Fin n → MvPowerSeries (Fin n) K)
    (F : MvPolynomial (Fin n) K) :
    (taylorPoly e F).natDegree ≤ F.totalDegree := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  exact (natDegree_taylorPoly_monomial_le e d _).trans (MvPolynomial.le_totalDegree hd)

private noncomputable def tau (e : Fin n → MvPowerSeries (Fin n) K) :
    ℕ → MvPowerSeries (Fin n) K → MvPowerSeries (Fin n) K
  | 0, F => F
  | m + 1, F => ∑ i, e i * tau e m (pderiv (R := K) i F)

private theorem tau_eval (e : Fin n → MvPowerSeries (Fin n) K) (m : ℕ) :
    ∀ F : MvPolynomial (Fin n) K,
      (Polynomial.derivative^[m] (taylorPoly e F)).eval 0 = tau e m (F : MvPowerSeries (Fin n) K) := by
  induction m with
  | zero =>
    intro F
    simp only [Function.iterate_zero, id_eq, eval_taylorPoly, mul_zero, add_zero, tau]
    have := (subst_coe (a := fun i : Fin n => (MvPowerSeries.X i : MvPowerSeries (Fin n) K)) F)
    rw [subst_self] at this
    exact this.symm
  | succ m ih =>
    intro F
    rw [Function.iterate_succ_apply, derivative_taylorPoly, Polynomial.iterate_derivative_sum,
      Polynomial.eval_finset_sum]
    simp only [tau, Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
      ih, pderiv_coe]

private theorem subst_coe_eq_sum_tau [CharZero K] (e : Fin n → MvPowerSeries (Fin n) K) (N : ℕ)
    (p : MvPolynomial (Fin n) K) (hp : p.totalDegree < N) :
    subst (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin n) K) + e i)
        (p : MvPowerSeries (Fin n) K) =
      ∑ m ∈ Finset.range N, algebraMap K (MvPowerSeries (Fin n) K) ((m.factorial : K)⁻¹) *
        tau e m (p : MvPowerSeries (Fin n) K) := by
  rw [subst_coe]
  have h1 : MvPolynomial.aeval (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin n) K) + e i) p =
      (taylorPoly e p).eval 1 := by
    rw [eval_taylorPoly]
    simp
  rw [h1, Polynomial.eval_eq_sum_range' ((natDegree_taylorPoly_le e p).trans_lt hp)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← tau_eval, one_pow, mul_one, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self, nsmul_eq_mul,
    ← mul_assoc]
  have : (algebraMap K (MvPowerSeries (Fin n) K)) ((m.factorial : K)⁻¹) * (m.factorial : _) =
      1 := by
    rw [← map_natCast (algebraMap K (MvPowerSeries (Fin n) K)), ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)), map_one]
  rw [this, one_mul]

private theorem tau_add (e : Fin n → MvPowerSeries (Fin n) K) (m : ℕ)
    (F G : MvPowerSeries (Fin n) K) :
    tau e m (F + G) = tau e m F + tau e m G := by
  induction m generalizing F G with
  | zero => rfl
  | succ m ih => simp [tau, ih, mul_add, Finset.sum_add_distrib]

private theorem le_order_sum {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries (Fin n) K)
    {N : ℕ∞} (h : ∀ i ∈ s, N ≤ (f i).order) : N ≤ (∑ i ∈ s, f i).order :=
  Finset.sum_induction _ (fun f : MvPowerSeries (Fin n) K => N ≤ f.order)
    (fun a b ha hb => le_trans (le_min ha hb) min_order_le_add) (by simp) h

private theorem tau_order (e : Fin n → MvPowerSeries (Fin n) K) (he : ∀ i, 1 ≤ (e i).order)
    (m : ℕ) : ∀ (N : ℕ) (F : MvPowerSeries (Fin n) K), (N : ℕ∞) ≤ F.order →
      (N : ℕ∞) ≤ (tau e m F).order := by
  induction m with
  | zero => exact fun _ _ h => h
  | succ m ih =>
    intro N F h
    cases N with
    | zero => simp
    | succ N =>
      have : ((N + 1 : ℕ) : ℕ∞) ≤ (∑ i, e i * tau e m (pderiv (R := K) i F)).order := by
        refine le_order_sum _ _ fun i _ => le_trans ?_ le_order_mul
        calc ((N + 1 : ℕ) : ℕ∞) = 1 + N := by push_cast; ring
          _ ≤ _ := add_le_add (he i) (ih N _ (order_pderiv i h))
      simpa [tau] using this

private theorem tau_mem (e : Fin n → MvPowerSeries (Fin n) K)
    (J : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (hJ : ∀ j i F, F ∈ J j → pderiv (R := K) i F ∈ J (j + 1)) (m : ℕ) :
    ∀ (j : ℕ) (F : MvPowerSeries (Fin n) K), F ∈ J j →
      tau e m F ∈ Ideal.span (Set.range e) ^ m * J (j + m) := by
  induction m with
  | zero => exact fun j F hF => by simpa [tau] using hF
  | succ m ih =>
    intro j F hF
    refine Ideal.sum_mem _ fun i _ => ?_
    have h2 : e i * tau e m (pderiv (R := K) i F) ∈
        Ideal.span (Set.range e) * (Ideal.span (Set.range e) ^ m * J (j + 1 + m)) :=
      Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ih (j + 1) _ (hJ j i F hF))
    rwa [← mul_assoc, ← pow_succ', show j + 1 + m = j + (m + 1) by omega] at h2

private theorem euler_sum [CharZero K] (F : MvPowerSeries (Fin n) K) (hF : (1 : ℕ∞) ≤ F.order) :
    ∃ H : MvPowerSeries (Fin n) K, (∀ N : ℕ, ((N + 1 : ℕ) : ℕ∞) ≤ F.order →
        ((N + 1 : ℕ) : ℕ∞) ≤ H.order) ∧ F = ∑ i, MvPowerSeries.X i * pderiv (R := K) i H := by
  let H : MvPowerSeries (Fin n) K := fun d => coeff d F * (((Finsupp.degree d : ℕ) : K))⁻¹
  have hH : ∀ d, coeff d H = coeff d F * (((Finsupp.degree d : ℕ) : K))⁻¹ := fun d => rfl
  refine ⟨H, fun N hN => nat_le_order fun d hd => ?_, ?_⟩
  · rw [hH, coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hN), zero_mul]
  · ext d
    rw [map_sum]
    have key : ∀ i, coeff d (MvPowerSeries.X i * pderiv (R := K) i H) = coeff d H * (d i : K) := by
      intro i
      rw [MvPowerSeries.X, coeff_monomial_mul]
      by_cases hi : Finsupp.single i 1 ≤ d
      · rw [if_pos hi, one_mul, coeff_pderiv, tsub_add_cancel_of_le hi]
        have h1 : 1 ≤ d i := by simpa using (Finsupp.single_le_iff.mp hi)
        congr 1
        have : (d - Finsupp.single i 1 : Fin n →₀ ℕ) i + 1 = d i := by
          simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
          omega
        exact_mod_cast this
      · rw [if_neg hi]
        have : d i = 0 := by
          by_contra h
          exact hi (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr h))
        simp [this]
    simp only [key, ← Finset.mul_sum]
    have hs : ∑ i, (d i : K) = ((Finsupp.degree d : ℕ) : K) := by
      rw [Finsupp.degree_eq_sum]
      push_cast
      rfl
    rw [hs, hH]
    by_cases h0 : Finsupp.degree d = 0
    · obtain rfl : d = 0 := (Finsupp.degree_eq_zero_iff d).mp h0
      have : coeff (0 : Fin n →₀ ℕ) F = 0 :=
        coeff_of_lt_order (lt_of_lt_of_le (by simp) hF)
      simp [this]
    · rw [mul_assoc, inv_mul_cancel₀ (by exact_mod_cast h0), mul_one]

private theorem mem_pow_of_le_order [CharZero K] (N : ℕ) :
    ∀ F : MvPowerSeries (Fin n) K, (N : ℕ∞) ≤ F.order →
      F ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) K)) ^ N := by
  induction N with
  | zero => intro F _; simp
  | succ N ih =>
    intro F hF
    obtain ⟨H, hH, rfl⟩ := euler_sum F (le_trans (by exact_mod_cast Nat.le_add_left 1 N) hF)
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [pow_succ']
    exact Ideal.mul_mem_mul (Ideal.subset_span ⟨i, rfl⟩) (ih _ (order_pderiv i (hH N hF)))

private theorem mem_of_forall_mem_sup_pow (I : Ideal (MvPowerSeries (Fin n) K))
    (f : MvPowerSeries (Fin n) K)
    (h : ∀ N : ℕ,
      f ∈ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) K)) ^ N) :
    f ∈ I := by
  set m := Ideal.span (Set.range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) K)) with hm
  have hle : m ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, hm, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hb := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := MvPowerSeries (Fin n) K ⧸ I) m hle
  have hx : Ideal.Quotient.mk I f ∈ (⨅ i : ℕ, m ^ i • ⊤ :
      Submodule (MvPowerSeries (Fin n) K) (MvPowerSeries (Fin n) K ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro N
    obtain ⟨a, ha, b, hb', rfl⟩ := Submodule.mem_sup.mp (h N)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    have : Ideal.Quotient.mk I b = b • (1 : MvPowerSeries (Fin n) K ⧸ I) := by
      rw [Algebra.smul_def]
      simp
    rw [this]
    exact Submodule.smul_mem_smul hb' trivial
  rw [hb, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact hx

private theorem le_order_subst_sub_sum_tau [CharZero K] {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, constantCoeff (g i) = 0) {N : ℕ} (hN : 0 < N) (F : MvPowerSeries (Fin n) K) :
    (N : ℕ∞) ≤ (subst g F - ∑ m ∈ Finset.range N, algebraMap K (MvPowerSeries (Fin n) K)
      ((m.factorial : K)⁻¹) * tau (fun i => g i - MvPowerSeries.X i) m F).order := by
  classical
  set e : Fin n → MvPowerSeries (Fin n) K := fun i => g i - MvPowerSeries.X i with he
  have heo : ∀ i, 1 ≤ (e i).order := fun i => by
    rw [one_le_order_iff_constCoeff_eq_zero]
    simp [he, hg]
  have hS := hasSubst_of_constantCoeff_zero (S := K) hg
  have hgx : (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin n) K) + e i) = g := by
    funext i
    simp [he]
  have hp : (truncTotal N F).totalDegree < N := totalDegree_truncTotal_lt _ hN.ne'
  obtain ⟨p, hpdef⟩ : ∃ p, p = truncTotal N F := ⟨_, rfl⟩
  rw [← hpdef] at hp
  obtain ⟨t, htdef⟩ : ∃ t, t = F - (p : MvPowerSeries (Fin n) K) := ⟨_, rfl⟩
  have hF' : F = (p : MvPowerSeries (Fin n) K) + t := by
    rw [htdef]
    ring
  have ht : (N : ℕ∞) ≤ t.order := nat_le_order fun d hd => by
    rw [htdef, map_sub, MvPolynomial.coeff_coe, hpdef, coeff_truncTotal _ hd, sub_self]
  have h1 : subst g F = ∑ m ∈ Finset.range N, algebraMap K (MvPowerSeries (Fin n) K)
      ((m.factorial : K)⁻¹) * tau e m p + subst g t := by
    rw [hF', subst_add hS, ← subst_coe_eq_sum_tau e N p hp, hgx]
  have h2 : ∑ m ∈ Finset.range N, algebraMap K (MvPowerSeries (Fin n) K)
      ((m.factorial : K)⁻¹) * tau e m F = ∑ m ∈ Finset.range N, algebraMap K
      (MvPowerSeries (Fin n) K) ((m.factorial : K)⁻¹) * tau e m p +
      ∑ m ∈ Finset.range N, algebraMap K (MvPowerSeries (Fin n) K) ((m.factorial : K)⁻¹) *
        tau e m t := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by rw [hF', tau_add, mul_add]
  have e1 : subst g F - ∑ m ∈ Finset.range N, algebraMap K (MvPowerSeries (Fin n) K)
      ((m.factorial : K)⁻¹) * tau e m F = subst g t - ∑ m ∈ Finset.range N, algebraMap K
      (MvPowerSeries (Fin n) K) ((m.factorial : K)⁻¹) * tau e m t := by
    rw [h1, h2]
    ring
  rw [e1, sub_eq_add_neg]
  refine le_trans (le_min ?_ ?_) min_order_le_add
  · refine le_trans ?_ (le_order_subst hS t)
    calc (N : ℕ∞) = 1 * N := (one_mul _).symm
      _ ≤ _ := mul_le_mul' (le_iInf fun i => by
        rw [one_le_order_iff_constCoeff_eq_zero]; exact hg i) ht
  · rw [order_neg]
    exact le_order_sum _ _ fun m _ => le_trans (tau_order e heo m N t ht) (by
      rw [← Algebra.smul_def]; exact le_order_smul)

private theorem subst_mem_of_pow_mul_le [CharZero K] {g : Fin n → MvPowerSeries (Fin n) K}
    (hg : ∀ i, constantCoeff (g i) = 0) (I : Ideal (MvPowerSeries (Fin n) K))
    (J : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (hJ : ∀ j i F, F ∈ J j → pderiv (R := K) i F ∈ J (j + 1))
    (hE : ∀ m, Ideal.span (Set.range fun i =>
      g i - (MvPowerSeries.X i : MvPowerSeries (Fin n) K)) ^ m * J m ≤ I)
    {F : MvPowerSeries (Fin n) K} (hF : F ∈ J 0) : subst g F ∈ I := by
  refine mem_of_forall_mem_sup_pow I _ fun N => ?_
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hSI : ∑ m ∈ Finset.range N, algebraMap K (MvPowerSeries (Fin n) K)
      ((m.factorial : K)⁻¹) * tau (fun i => g i - MvPowerSeries.X i) m F ∈ I := by
    refine Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _ ?_
    exact hE m (by simpa using tau_mem (fun i => g i - MvPowerSeries.X i) J hJ m 0 F hF)
  have := Submodule.add_mem_sup hSI
    (mem_pow_of_le_order N _ (le_order_subst_sub_sum_tau hg hN F))
  rwa [add_sub_cancel] at this

private theorem image_eq_of_surjective_of_forall_mem {A R : Type*} [CommRing A] [CommRing R]
    [Algebra A R] [IsNoetherianRing R] (φ : R →ₐ[A] R) (hφ : Function.Surjective φ) (I : Ideal R)
    (h : ∀ f ∈ I, φ f ∈ I) : φ '' (I : Set R) = I := by
  have hmem : ∀ k : ℕ, ∀ x, (φ ^ (k + 1)) x = φ ((φ ^ k) x) := fun k x => by
    rw [pow_succ']; rfl
  let c : ℕ →o Ideal R :=
    ⟨fun k => Ideal.comap (φ ^ k) I, monotone_nat_of_le_succ fun k x hx => by
      simp only [Ideal.mem_comap] at hx ⊢
      rw [hmem]
      exact h _ hx⟩
  obtain ⟨k, hk⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) c
  have hsurj : Function.Surjective (φ ^ k) := by
    rw [AlgHom.coe_pow]
    exact hφ.iterate k
  have h2 : Ideal.comap (φ ^ k) I = Ideal.comap (φ ^ k) (Ideal.comap φ I) := by
    refine (hk (k + 1) k.le_succ).trans ?_
    ext x
    simp only [Ideal.mem_comap]
    show (φ ^ (k + 1)) x ∈ I ↔ φ ((φ ^ k) x) ∈ I
    rw [hmem]
  have h3 := Ideal.comap_injective_of_surjective (φ ^ k) hsurj h2
  refine Set.Subset.antisymm (Set.image_subset_iff.mpr h) fun y hy => ?_
  obtain ⟨x, rfl⟩ := hφ y
  refine ⟨x, ?_, rfl⟩
  rw [SetLike.mem_coe, h3]
  exact hy

end TaylorHelpers

/-- **Kollár Prop. 3.94, (3) ⇒ (1).** Let `k` be a field of characteristic `0`, `K / k` a field
extension, `R = K[[x_1, …, x_n]]` and `B`, `I` ideals of `R` with `B^j · D^j(I) ⊆ I` for every
`j ≥ 1`, where `D = D_{R/k}`. Then `g^*(I) = I` for every automorphism `g^*` of `R` of the form
`1 + B` (Kollár Notation 3.93). -/
@[mmp "lem_kr3d_invariance_from_higher_condition"]
theorem image_subst_eq_of_pow_mul_higherDerivativeIdealOfRing_le {k K : Type*} [Field k]
    [CharZero k] [Field K] [Algebra k K] {n : ℕ} {B I : Ideal (MvPowerSeries (Fin n) K)}
    (h : ∀ j : ℕ, 1 ≤ j → B ^ j * higherDerivativeIdealOfRing k I j ≤ I)
    {g : Fin n → MvPowerSeries (Fin n) K} (hg : IsAutomorphismOfFormOnePlus B g) :
    MvPowerSeries.subst (R := K) g '' (I : Set (MvPowerSeries (Fin n) K)) = I := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  obtain ⟨hg0, hbij, hgB⟩ := hg
  have hS : MvPowerSeries.HasSubst g := MvPowerSeries.hasSubst_of_constantCoeff_zero hg0
  have hcoe : ⇑(MvPowerSeries.substAlgHom (R := K) hS) = MvPowerSeries.subst (R := K) g :=
    MvPowerSeries.coe_substAlgHom hS
  have hJ : ∀ (j : ℕ) (i : Fin n) (F : MvPowerSeries (Fin n) K),
      F ∈ higherDerivativeIdealOfRing k I j →
        MvPowerSeries.pderiv (R := K) i F ∈ higherDerivativeIdealOfRing k I (j + 1) := by
    intro j i F hF
    rw [higherDerivativeIdealOfRing_succ]
    exact Ideal.subset_span ⟨(MvPowerSeries.pderiv (R := K) i).restrictScalars k, F, hF, rfl⟩
  have hE : ∀ m : ℕ, Ideal.span (Set.range fun i => g i -
      (MvPowerSeries.X i : MvPowerSeries (Fin n) K)) ^ m * higherDerivativeIdealOfRing k I m ≤
        I := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [higherDerivativeIdealOfRing_zero]
    · exact (Ideal.mul_mono_left (Ideal.pow_right_mono
        (Ideal.span_le.mpr (Set.range_subset_iff.mpr hgB)) m)).trans (h m hm)
  have hmem : ∀ f ∈ I, MvPowerSeries.substAlgHom (R := K) hS f ∈ I := fun f hf => by
    rw [hcoe]
    exact subst_mem_of_pow_mul_le hg0 I (higherDerivativeIdealOfRing k I) hJ hE
      (by simpa [higherDerivativeIdealOfRing_zero] using hf)
  have := image_eq_of_surjective_of_forall_mem (MvPowerSeries.substAlgHom (R := K) hS)
    (by simpa only [hcoe] using hbij.2) I hmem
  rwa [hcoe] at this

end MMP.Resolution.Kollar
