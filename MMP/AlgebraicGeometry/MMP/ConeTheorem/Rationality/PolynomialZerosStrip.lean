module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Data.Rat.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import MMP.Attr

/-!
# Zeros of a polynomial in a strip (KM Lemma 3.19, corrected)

Let `P ∈ ℝ[x, y]` be a nonzero polynomial, `a ∈ ℤ_{>0}`, `ε > 0` and `r > 0`, and suppose `P`
vanishes at every integral point `(x, y)` with `x, y ≥ N` in the strip `0 < ay - rx < ε`. Then
`r ∈ ℚ`; and if `r = u/v` in lowest terms and `deg P ≤ n`, then `v ≤ a(n + 1)/ε`.

KM state the lemma without `r > 0`; it is needed (for `r < 0` the strip contains no point with
`x, y ≥ N` large and the hypothesis is vacuous).

## Main results

* `MMP.Positivity.exists_rat_eq_of_eval_eq_zero_of_strip`
* `MMP.Positivity.den_le_of_eval_eq_zero_of_strip`
-/

@[expose] public noncomputable section

namespace MMP.Positivity

open Polynomial in
/-- Substituting polynomials of degree `≤ 1` into a multivariate polynomial gives a polynomial
of degree at most its total degree. -/
theorem natDegree_aeval_le_totalDegree {σ : Type*} (P : MvPolynomial σ ℝ) (g : σ → ℝ[X])
    (hg : ∀ i, (g i).natDegree ≤ 1) : (MvPolynomial.aeval g P).natDegree ≤ P.totalDegree := by
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  refine natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  refine Finset.sum_le_sum fun i _ => natDegree_pow_le.trans ?_
  simpa using Nat.mul_le_mul_left (d i) (hg i)

open Polynomial in
/-- A polynomial in two variables vanishing at more than `totalDegree P` points of a line
`t ↦ (p₀ + t q₀, p₁ + t q₁)` vanishes on the whole line. -/
theorem eval_line_eq_zero_of_totalDegree_lt_card {P : MvPolynomial (Fin 2) ℝ}
    (p0 p1 q0 q1 : ℝ) (s : Finset ℝ) (hs : P.totalDegree < s.card)
    (h : ∀ t ∈ s, MvPolynomial.eval ![p0 + t * q0, p1 + t * q1] P = 0) (t : ℝ) :
    MvPolynomial.eval ![p0 + t * q0, p1 + t * q1] P = 0 := by
  set g : Fin 2 → ℝ[X] := ![C p0 + C q0 * X, C p1 + C q1 * X] with hg
  have key : ∀ t, (MvPolynomial.aeval g P).eval t =
      MvPolynomial.eval ![p0 + t * q0, p1 + t * q1] P := by
    intro t
    rw [← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply,
      ← MvPolynomial.coe_aeval_eq_eval]
    have : (fun i => (Polynomial.aeval t) (g i)) = ![p0 + t * q0, p1 + t * q1] := by
      funext i
      fin_cases i <;> simp [g] <;> ring
    rw [this]
    rfl
  have hdeg : (MvPolynomial.aeval g P).natDegree ≤ P.totalDegree := by
    refine natDegree_aeval_le_totalDegree _ _ fun i => ?_
    fin_cases i <;> simp only [hg, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
      Matrix.cons_val_one] <;> compute_degree
  have h0 : MvPolynomial.aeval g P = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ s (fun t ht => (key t).trans (h t ht))
      (hdeg.trans_lt hs)
  rw [← key, h0, eval_zero]

/-- A polynomial in two variables vanishing at infinitely many points of a line vanishes on the
whole line. -/
theorem eval_line_eq_zero_of_infinite {P : MvPolynomial (Fin 2) ℝ} (p0 p1 q0 q1 : ℝ)
    (h : {t : ℝ | MvPolynomial.eval ![p0 + t * q0, p1 + t * q1] P = 0}.Infinite) (t : ℝ) :
    MvPolynomial.eval ![p0 + t * q0, p1 + t * q1] P = 0 := by
  obtain ⟨s, hs, hcard⟩ := h.exists_subset_card_eq (P.totalDegree + 1)
  exact eval_line_eq_zero_of_totalDegree_lt_card p0 p1 q0 q1 s (by omega) (fun t ht => hs ht) t

/-- A polynomial in two real variables vanishing everywhere is zero. -/
theorem eq_zero_of_forall_eval_eq_zero {P : MvPolynomial (Fin 2) ℝ}
    (h : ∀ x y : ℝ, MvPolynomial.eval ![x, y] P = 0) : P = 0 := by
  have : Infinite ℝ := Infinite.of_injective ((↑) : ℕ → ℝ) Nat.cast_injective
  refine MvPolynomial.funext fun x => ?_
  have hx : x = ![x 0, x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hx, h, map_zero]

/-- For `a > 0` and `η > 0`, every real `r` admits integers `j` and `k > 0` with
`|a j - r k| < η`. -/
theorem exists_int_abs_mul_sub_lt {a : ℝ} (ha : 0 < a) {η : ℝ} (hη : 0 < η) (r : ℝ) :
    ∃ j k : ℤ, 0 < k ∧ |a * j - r * k| < η := by
  obtain ⟨M, hM⟩ := exists_nat_gt (a / η)
  obtain ⟨j, k, hk0, -, hjk⟩ := Real.exists_int_int_abs_mul_sub_le (r / a) (Nat.succ_pos M)
  refine ⟨j, k, hk0, ?_⟩
  have h1 : a * j - r * k = -(a * (k * (r / a) - j)) := by
    field_simp
    ring
  rw [h1, abs_neg, abs_mul, abs_of_pos ha]
  have hM' : a / η < ((M.succ : ℕ) : ℝ) + 1 := by push_cast; linarith
  rw [div_lt_iff₀ hη] at hM'
  calc a * |k * (r / a) - j| ≤ a * (1 / (((M.succ : ℕ) : ℝ) + 1)) := by gcongr
    _ < η := by
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      linarith

/-- For `a, r > 0` and every `N'` there is an integer `X ≥ max N' 1` with `N' ≤ ⌊r X / a⌋`. -/
theorem exists_int_le_floor_mul_div {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (N' : ℤ) :
    ∃ X : ℤ, N' ≤ X ∧ 1 ≤ X ∧ N' ≤ ⌊r * X / a⌋ := by
  refine ⟨max (max N' 1) ⌈a * N' / r⌉, by simp, by simp, Int.le_floor.mpr ?_⟩
  have h1 : a * N' / r ≤ ((max (max N' 1) ⌈a * N' / r⌉ : ℤ) : ℝ) :=
    (Int.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  rw [div_le_iff₀ hr] at h1
  rw [le_div_iff₀ ha]
  linarith

/-- For `e < 0 < d` some `d + m e` with `m : ℕ` lies in `[0, -e)`. -/
theorem exists_nat_add_mul_mem_Ico_of_neg {d e : ℝ} (he : e < 0) (hd : 0 < d) :
    ∃ m : ℕ, 0 ≤ d + m * e ∧ d + m * e < -e := by
  have h1 := Nat.floor_le (div_nonneg hd.le (neg_nonneg.mpr he.le))
  have h2 := Nat.lt_floor_add_one (d / -e)
  rw [le_div_iff₀ (by linarith)] at h1
  rw [div_lt_iff₀ (by linarith)] at h2
  exact ⟨⌊d / -e⌋₊, by linarith, by linarith⟩

/-- For `d ≤ 0 < e` some `d + m e` with `m : ℕ` lies in `(0, e]`. -/
theorem exists_nat_add_mul_mem_Ioc_of_pos {d e : ℝ} (he : 0 < e) (hd : d ≤ 0) :
    ∃ m : ℕ, 0 < d + m * e ∧ d + m * e ≤ e := by
  have h1 := Nat.floor_le (div_nonneg (neg_nonneg.mpr hd) he.le)
  have h2 := Nat.lt_floor_add_one (-d / e)
  rw [le_div_iff₀ he] at h1
  rw [div_lt_iff₀ he] at h2
  refine ⟨⌊-d / e⌋₊ + 1, ?_, ?_⟩ <;> push_cast <;> linarith

/-- If `a > 0`, `r > 0` and `a q - r p ≠ 0` for all integers `p > 0`, `q` (i.e. `r` is
irrational), then for every `δ > 0` and `N'` there is an integral point `(x, y)` with
`x, y ≥ N'` and `0 < a y - r x < δ`. -/
theorem exists_strip_point_of_irrational {a : ℤ} (ha : 0 < a) {r : ℝ} (hr : 0 < r)
    (hirr : ∀ p q : ℤ, 0 < p → (a : ℝ) * q - r * p ≠ 0) {δ : ℝ} (hδ : 0 < δ) (N' : ℤ) :
    ∃ x y : ℤ, N' ≤ x ∧ N' ≤ y ∧ 0 < a * y - r * x ∧ a * y - r * x < δ := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  set η := min δ a with hη
  have hη0 : 0 < η := lt_min hδ haR
  obtain ⟨j, k, hk0, he_abs⟩ := exists_int_abs_mul_sub_lt haR hη0 r
  set e : ℝ := a * j - r * k with he
  have hene : e ≠ 0 := hirr k j hk0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hj0 : 0 ≤ j := by
    have h2 : (0 : ℝ) < a * (j + 1) := by
      linarith [neg_abs_le e, min_le_right δ (a : ℝ), mul_pos hr hkR]
    have h4 : (0 : ℤ) < j + 1 := by exact_mod_cast pos_of_mul_pos_right h2 haR.le
    omega
  obtain ⟨X, hXN, hX1, hfl⟩ := exists_int_le_floor_mul_div haR hr N'
  have hval : ∀ (m : ℕ) (Y0 : ℤ), (a : ℝ) * ((Y0 + m * j : ℤ) : ℝ) - r * ((X + m * k : ℤ) : ℝ) =
      (a * Y0 - r * X) + m * e := by
    intro m Y0
    rw [he]
    push_cast
    ring
  have hcoord : ∀ m : ℕ, N' ≤ X + m * k := fun m => by nlinarith
  have hcoord' : ∀ m : ℕ, 0 < X + m * k := fun m => by nlinarith
  rcases lt_or_gt_of_ne hene with hneg | hpos
  · set Y0 : ℤ := ⌊r * X / a⌋ + 1 with hY0
    have hd0 : 0 < (a : ℝ) * Y0 - r * X := by
      have h1 := Int.lt_floor_add_one (r * X / a)
      rw [div_lt_iff₀ haR] at h1
      rw [hY0]
      push_cast
      linarith
    obtain ⟨m, hm0, hm⟩ := exists_nat_add_mul_mem_Ico_of_neg hneg hd0
    refine ⟨X + m * k, Y0 + m * j, hcoord m, by nlinarith, ?_, ?_⟩ <;> rw [hval]
    · exact hm0.lt_of_ne fun h0 =>
        hirr _ (Y0 + m * j) (hcoord' m) (by rw [hval]; linarith)
    · linarith [le_abs_self (-e), abs_neg e, min_le_left δ (a : ℝ)]
  · set Y0 : ℤ := ⌊r * X / a⌋ with hY0
    have hd0 : (a : ℝ) * Y0 - r * X ≤ 0 := by
      have h1 := Int.floor_le (r * X / a)
      rw [le_div_iff₀ haR] at h1
      rw [hY0]
      linarith
    obtain ⟨m, hm0, hm⟩ := exists_nat_add_mul_mem_Ioc_of_pos hpos hd0
    refine ⟨X + m * k, Y0 + m * j, hcoord m, by nlinarith, ?_, ?_⟩ <;> rw [hval]
    · exact hm0
    · linarith [le_abs_self e, min_le_left δ (a : ℝ)]

/-- If `r > 0` is irrational in the sense that `a q - r p ≠ 0` for integers `p > 0`, `q`, then
the slopes `y / x` of the integral points with `x, y ≥ N`, `x ≥ 1` and `0 < a y - r x < ε`
form an infinite set. -/
theorem infinite_slopes_of_irrational {a : ℤ} (ha : 0 < a) {r : ℝ} (hr : 0 < r)
    (hirr : ∀ p q : ℤ, 0 < p → (a : ℝ) * q - r * p ≠ 0) {ε : ℝ} (hε : 0 < ε) (N : ℤ) :
    {s : ℝ | ∃ x y : ℤ, N ≤ x ∧ N ≤ y ∧ 1 ≤ x ∧ 0 < a * y - r * x ∧ a * y - r * x < ε ∧
      s = y / x}.Infinite := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  intro hfin
  obtain ⟨x, y, hxN, hyN, hpos, hlt⟩ := exists_strip_point_of_irrational ha hr hirr hε (max N 1)
  obtain ⟨s0, ⟨x0, y0, -, -, hx01, hpos0, -, rfl⟩, hmin⟩ := Set.exists_min_image _ id hfin
    ⟨y / x, x, y, le_of_max_le_left hxN, le_of_max_le_left hyN, le_of_max_le_right hxN, hpos,
      hlt, rfl⟩
  have hx0R : (1 : ℝ) ≤ x0 := by exact_mod_cast hx01
  obtain ⟨x, y, hxN, hyN, hpos, hlt⟩ := exists_strip_point_of_irrational ha hr hirr
    (lt_min hε (div_pos hpos0 (by linarith : (0 : ℝ) < x0))) (max N 1)
  have hx1 : 1 ≤ x := le_of_max_le_right hxN
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
  have hle : (y0 : ℝ) / x0 ≤ y / x := hmin _ ⟨x, y, le_of_max_le_left hxN,
    le_of_max_le_left hyN, hx1, hpos, lt_of_lt_of_le hlt (min_le_left _ _), rfl⟩
  have h1 : (a : ℝ) * (y / x) - r = (a * y - r * x) / x := by field_simp
  have h0 : (a : ℝ) * (y0 / x0) - r = (a * y0 - r * x0) / x0 := by field_simp
  have h2 : (a * y - r * x) / x ≤ a * y - r * x := div_le_self hpos.le hxR
  have h3 : (a : ℝ) * (y / x) < a * (y0 / x0) := by
    linarith [min_le_right ε ((a * y0 - r * x0) / x0)]
  have h4 : (y : ℝ) / x < y0 / x0 := lt_of_mul_lt_mul_left h3 haR.le
  linarith

/-- A polynomial in two real variables vanishing on the lines `y = s x` for more than
`totalDegree P` slopes `s` is zero. -/
theorem eq_zero_of_eval_ray_eq_zero {P : MvPolynomial (Fin 2) ℝ} (T : Finset ℝ)
    (hT : P.totalDegree < T.card) (h : ∀ s ∈ T, ∀ t, MvPolynomial.eval ![t, s * t] P = 0) :
    P = 0 := by
  have hvert : ∀ x : ℝ, x ≠ 0 → ∀ y, MvPolynomial.eval ![x, y] P = 0 := by
    intro x hx y
    have hline := eval_line_eq_zero_of_totalDegree_lt_card (P := P) x 0 0 1 (T.image (· * x))
      (by rwa [Finset.card_image_of_injective _ (mul_left_injective₀ hx)]) (by
        intro t ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        simpa using h s hs x) y
    simpa using hline
  refine eq_zero_of_forall_eval_eq_zero fun x y => ?_
  have hline := eval_line_eq_zero_of_totalDegree_lt_card (P := P) 0 y 1 0
    ((Finset.range (P.totalDegree + 1)).image (fun i : ℕ => ((i + 1 : ℕ) : ℝ)))
    (by
      rw [Finset.card_image_of_injective _ (fun i k h => by simpa using h), Finset.card_range]
      omega) (by
      intro t ht
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      simpa using hvert _ (by positivity) y) x
  simpa using hline

/-- **KM Lemma 3.19, first conclusion (corrected).** Let `P ∈ ℝ[x, y]` be a nonzero polynomial,
`a ∈ ℤ_{>0}`, `ε > 0` and `r ∈ ℝ` with `r > 0`. Suppose there is `N ∈ ℤ` such that `P(x, y) = 0`
for all `(x, y) ∈ ℤ²` with `x, y ≥ N` and `0 < ay - rx < ε`. Then `r ∈ ℚ`. KM also assume
`deg P ≤ n`, which this conclusion does not need. -/
@[mmp "lem_km3b_polynomial_zeros_irrational"]
theorem exists_rat_eq_of_eval_eq_zero_of_strip {P : MvPolynomial (Fin 2) ℝ} (hP : P ≠ 0)
    {a : ℤ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 < r)
    (hN : ∃ N : ℤ, ∀ x y : ℤ, N ≤ x → N ≤ y → 0 < a * y - r * x → a * y - r * x < ε →
      MvPolynomial.eval ![(x : ℝ), (y : ℝ)] P = 0) :
    ∃ q : ℚ, r = q := by
  obtain ⟨N, hN⟩ := hN
  by_contra hq
  have hirr : ∀ p q : ℤ, 0 < p → (a : ℝ) * q - r * p ≠ 0 := by
    intro p q hp h
    apply hq
    refine ⟨(a * q / p : ℚ), ?_⟩
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    push_cast
    field_simp
    linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  set n := P.totalDegree with hn
  set ε' : ℝ := ε / (n + 1) with hε'
  have hε'0 : 0 < ε' := by positivity
  set G : Set ℝ := {s | ∃ x y : ℤ, N ≤ x ∧ N ≤ y ∧ 1 ≤ x ∧ 0 < a * y - r * x ∧
    a * y - r * x < ε' ∧ s = y / x} with hGdef
  have hG : ∀ s ∈ G, ∀ t : ℝ, MvPolynomial.eval ![t, s * t] P = 0 := by
    rintro s ⟨x, y, hxN, hyN, hx1, hpos, hlt, rfl⟩ t
    have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    have hy1 : 1 ≤ y := by
      have h1 : (0 : ℝ) < y := by nlinarith [mul_pos hr (by linarith : (0 : ℝ) < x)]
      have h2 : (0 : ℤ) < y := by exact_mod_cast h1
      omega
    have hline := eval_line_eq_zero_of_totalDegree_lt_card (P := P) 0 0 x y
      ((Finset.range (n + 1)).image (fun i : ℕ => ((i + 1 : ℕ) : ℝ))) ?_ ?_ (t / x)
    · have e1 : (0 : ℝ) + t / x * x = t := by
        rw [zero_add]
        field_simp
      have e2 : (0 : ℝ) + t / x * y = y / x * t := by ring
      rwa [e1, e2] at hline
    · rw [Finset.card_image_of_injective _ (fun i k h => by simpa using h), Finset.card_range]
      omega
    · intro t ht
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
      rw [Finset.mem_range] at hi
      have hiR : (i : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : i + 1 ≤ n + 1)
      have hpt := hN ((i + 1 : ℕ) * x) ((i + 1 : ℕ) * y) (by push_cast; nlinarith)
        (by push_cast; nlinarith) (by push_cast; nlinarith) (by
          push_cast
          have h1 : ((i : ℝ) + 1) * (a * y - r * x) ≤ (n + 1) * (a * y - r * x) :=
            mul_le_mul_of_nonneg_right hiR hpos.le
          have h2 : ((n : ℝ) + 1) * (a * y - r * x) < (n + 1) * ε' :=
            mul_lt_mul_of_pos_left hlt (by positivity)
          have h3 : ((n : ℝ) + 1) * ε' = ε := by rw [hε']; field_simp
          linarith)
      push_cast at hpt ⊢
      simpa using hpt
  obtain ⟨T, hTG, hTcard⟩ :=
    (infinite_slopes_of_irrational ha hr hirr hε'0 N).exists_subset_card_eq (n + 1)
  exact hP (eq_zero_of_eval_ray_eq_zero T (by omega) fun s hs => hG s (hTG hs))

/-- If `a v Y - u X = a j` in `ℤ`, where `r = u / v` in lowest terms, then
`a Y - r X = a j / v` in `ℝ`. -/
theorem mul_sub_ratCast_mul_eq_div_den {a X Y : ℤ} {r : ℚ} {j : ℕ}
    (h : a * r.den * Y - r.num * X = a * j) : (a : ℝ) * Y - (r : ℝ) * X = a * j / r.den := by
  have h' : (a : ℝ) * r.den * Y - r.num * X = a * j := by exact_mod_cast h
  have hv : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  rw [Rat.cast_def]
  field_simp
  linear_combination h'

/-- Under the hypothesis of `den_le_of_eval_eq_zero_of_strip`, `P` vanishes on the line
`a v y - u x = a j` (`r = u / v`) through an integral point, as soon as `0 < a j / v < ε`. -/
theorem eval_eq_zero_of_line_through_intPoint {P : MvPolynomial (Fin 2) ℝ} {a : ℤ} (ha : 0 < a)
    {ε : ℝ} {r : ℚ} (hr : 0 < r) {N : ℤ}
    (hN : ∀ x y : ℤ, N ≤ x → N ≤ y → 0 < a * y - (r : ℝ) * x → a * y - (r : ℝ) * x < ε →
      MvPolynomial.eval ![(x : ℝ), (y : ℝ)] P = 0)
    {j : ℕ} (hjpos : 0 < (a : ℝ) * j / r.den) (hjε : (a : ℝ) * j / r.den < ε) {x0 y0 : ℤ}
    (h0 : a * r.den * y0 - r.num * x0 = a * j) (x y : ℝ)
    (hxy : (a : ℝ) * r.den * y - r.num * x = a * j) :
    MvPolynomial.eval ![x, y] P = 0 := by
  have hu0 : 0 < r.num := Rat.num_pos.mpr hr
  have hv1 : (1 : ℤ) ≤ a * r.den := by
    have : (1 : ℤ) ≤ r.den := by exact_mod_cast r.den_pos
    nlinarith
  set K : ℕ := N.natAbs + x0.natAbs + y0.natAbs with hK
  have hinf :
      {t : ℝ | MvPolynomial.eval ![x0 + t * (a * r.den), y0 + t * r.num] P = 0}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((K + k : ℕ) : ℝ))
      (fun k l hkl => by simpa using hkl) fun k => ?_
    have hKk : ((K + k : ℕ) : ℤ) = |N| + |x0| + |y0| + k := by
      rw [hK]
      push_cast
      rfl
    have hk0 : (0 : ℤ) ≤ k := by positivity
    have hpt := hN (x0 + (K + k : ℕ) * (a * r.den)) (y0 + (K + k : ℕ) * r.num) (by
        rw [hKk]
        nlinarith [abs_nonneg N, abs_nonneg x0, abs_nonneg y0, le_abs_self N, neg_abs_le x0])
      (by
        rw [hKk]
        nlinarith [abs_nonneg N, abs_nonneg x0, abs_nonneg y0, le_abs_self N, neg_abs_le y0])
      (by rw [mul_sub_ratCast_mul_eq_div_den (j := j) (by linear_combination h0)]; exact hjpos)
      (by rw [mul_sub_ratCast_mul_eq_div_den (j := j) (by linear_combination h0)]; exact hjε)
    simp only [Set.mem_ofPred_eq]
    push_cast at hpt ⊢
    exact hpt
  have hvne : (a : ℝ) * r.den ≠ 0 := by positivity
  have h0R : (a : ℝ) * r.den * y0 - r.num * x0 = a * j := by exact_mod_cast h0
  have e1 : (x0 : ℝ) + (x - x0) / (a * r.den) * (a * r.den) = x := by
    field_simp
    ring
  have e2 : (y0 : ℝ) + (x - x0) / (a * r.den) * r.num = y := by
    field_simp
    linear_combination h0R - hxy
  have hpt := eval_line_eq_zero_of_infinite _ _ _ _ hinf ((x - x0) / (a * r.den))
  rwa [e1, e2] at hpt

/-- Under the hypothesis of `den_le_of_eval_eq_zero_of_strip`, `P` vanishes on the line
`a v y - u x = a j` (`r = u / v`) for every `j ≥ 1` with `a j / v < ε`. -/
theorem eval_eq_zero_of_level_line {P : MvPolynomial (Fin 2) ℝ} {a : ℤ} (ha : 0 < a)
    {ε : ℝ} {r : ℚ} (hr : 0 < r) {N : ℤ}
    (hN : ∀ x y : ℤ, N ≤ x → N ≤ y → 0 < a * y - (r : ℝ) * x → a * y - (r : ℝ) * x < ε →
      MvPolynomial.eval ![(x : ℝ), (y : ℝ)] P = 0)
    {j : ℕ} (hj1 : 1 ≤ j) (hjε : (a : ℝ) * j / r.den < ε) (x y : ℝ)
    (hxy : (a : ℝ) * r.den * y - r.num * x = a * j) :
    MvPolynomial.eval ![x, y] P = 0 := by
  have hbez : (1 : ℤ) = r.num * Int.gcdA r.num r.den + r.den * Int.gcdB r.num r.den := by
    have h1 := Int.gcd_eq_gcd_ab r.num r.den
    have hcop : Int.gcd r.num r.den = 1 := r.reduced
    rw [hcop] at h1
    exact_mod_cast h1
  have hjpos : (0 : ℝ) < a * j / r.den := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    positivity
  exact eval_eq_zero_of_line_through_intPoint ha hr hN hjpos hjε
    (x0 := -(a * j * Int.gcdA r.num r.den)) (y0 := j * Int.gcdB r.num r.den)
    (by linear_combination (-(a * j) : ℤ) * hbez) x y hxy

/-- A polynomial in two real variables vanishing on more than `totalDegree P` distinct parallel
lines `α y - β x = c i` is zero. -/
theorem eq_zero_of_eval_eq_zero_of_parallel_lines {P : MvPolynomial (Fin 2) ℝ} {α β : ℝ}
    (hα : α ≠ 0) (c : ℕ → ℝ) (hc : Function.Injective c)
    (h : ∀ i < P.totalDegree + 1, ∀ x y : ℝ, α * y - β * x = c i →
      MvPolynomial.eval ![x, y] P = 0) :
    P = 0 := by
  refine eq_zero_of_forall_eval_eq_zero fun x y => ?_
  set s : Finset ℝ :=
    (Finset.range (P.totalDegree + 1)).image (fun i : ℕ => (c i + β * x) / α) with hs
  have hscard : s.card = P.totalDegree + 1 := by
    rw [hs, Finset.card_image_of_injective _ ?_, Finset.card_range]
    intro i k hik
    have hik' : (c i + β * x) / α = (c k + β * x) / α := hik
    rw [div_left_inj' hα, add_left_inj] at hik'
    exact hc hik'
  have hpt := eval_line_eq_zero_of_totalDegree_lt_card (P := P) x 0 0 1 s (by omega) (by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    simp only [mul_zero, add_zero, mul_one, zero_add]
    refine h i (Finset.mem_range.mp hi) _ _ ?_
    field_simp
    ring) y
  simpa using hpt

/-- **KM Lemma 3.19, second conclusion (corrected).** Let `P ∈ ℝ[x, y]` be a nonzero polynomial
of degree `≤ n`, `a ∈ ℤ_{>0}`, `ε > 0`, and `r = u/v` with `u, v ∈ ℤ`, `v > 0`, `gcd(u, v) = 1`
and `r > 0`. Suppose there is `N ∈ ℤ` such that `P(x, y) = 0` for all `(x, y) ∈ ℤ²` with
`x, y ≥ N` and `0 < ay - rx < ε`. Then `v ≤ a(n + 1)/ε`. -/
@[mmp "lem_km3b_polynomial_zeros_denominator"]
theorem den_le_of_eval_eq_zero_of_strip {P : MvPolynomial (Fin 2) ℝ} (hP : P ≠ 0) {n : ℕ}
    (hPn : P.totalDegree ≤ n) {a : ℤ} (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) {r : ℚ} (hr : 0 < r)
    (hN : ∃ N : ℤ, ∀ x y : ℤ, N ≤ x → N ≤ y → 0 < a * y - (r : ℝ) * x → a * y - (r : ℝ) * x < ε →
      MvPolynomial.eval ![(x : ℝ), (y : ℝ)] P = 0) :
    (r.den : ℝ) ≤ a * (n + 1) / ε := by
  obtain ⟨N, hN⟩ := hN
  by_contra hlt
  rw [not_le] at hlt
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hvR : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hlt' : (a : ℝ) * (n + 1) < ε * r.den := by
    rw [div_lt_iff₀ hε] at hlt
    linarith
  refine hP (eq_zero_of_eval_eq_zero_of_parallel_lines (β := (r.num : ℝ))
    (mul_pos haR hvR).ne' (fun i : ℕ => a * ((i + 1 : ℕ) : ℝ))
    (fun i k h => by simpa [ha.ne'] using h) fun i hi x y hxy =>
      eval_eq_zero_of_level_line ha hr hN (j := i + 1) (by omega) ?_ x y hxy)
  have : ((i + 1 : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : i + 1 ≤ n + 1)
  rw [div_lt_iff₀ hvR]
  nlinarith

end MMP.Positivity
