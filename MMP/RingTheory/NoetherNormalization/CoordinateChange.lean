module

public import MMP.Attr
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The coordinate changes in the proof of Noether normalization (Kollár 1.35, 1.37)

Kollár, *Lectures on resolution of singularities*, proof of Theorem 1.35: after a linear change
of coordinates (over an infinite field) or Nagata's change `yᵢ ↦ yᵢ + y_m^{nᵢ}` (over any
field), a polynomial `f ∈ k[y₁, …, y_m]` of degree `d ≥ 1` becomes, up to a non-zero constant,
monic in `y_m`. Also the elementary well-definedness of set-theoretic liftings (1.37).

Noether normalization itself (Kollár, Theorem 1.35) is Mathlib's
`exists_finite_inj_algHom_of_fg` and is recorded as library coverage, not restated.

## Main statements

* `MMP.Resolution.Kollar.exists_linear_change_degreeOf_lt`: the linear change over an infinite
  field.
* `MMP.Resolution.Kollar.exists_nagata_change_degreeOf_lt`: Nagata's change over any field.
* `MMP.Resolution.Kollar.mul_pow_mul_pow_sub_mem_maximalIdeal_pow`:
  `r xⁱ yʲ - r' xⁱ yʲ ∈ 𝔪^{i+j+1}` when `r ≡ r'` modulo `𝔪` and `x, y ∈ 𝔪`.

## Implementation notes

The variables `y₁, …, y_m` of `k[y₁, …, y_m]` are `MvPolynomial (Fin (n + 1)) k` with
`m = n + 1`, `y_m = X (Fin.last n)` and `y_{i+1} = X i.castSucc` for `i : Fin n`. A polynomial
"viewed as a polynomial in `y_m` with coefficients in `k[y₁, …, y_{m-1}]` has degree `< d`" is
`MvPolynomial.degreeOf (Fin.last n) _ < d`. The substitution
`yᵢ ↦ yᵢ + aᵢ y_m` (`i < m`), `y_m ↦ y_m` is `MvPolynomial.aeval` at the corresponding family.
-/

@[expose] public section

open MvPolynomial

namespace MMP.Resolution.Kollar

section Noether

variable {k : Type*} [Field k] {n : ℕ}

/-- `q` is zero or has `y_m`-degree `< N`. -/
private abbrev Low (N : ℕ) (q : MvPolynomial (Fin (n + 1)) k) : Prop :=
  degreeOf (Fin.last n) q < N ∨ q = 0

/-- `p = c y_mᴺ + (terms of lower y_m-degree)`. -/
private def Top (N : ℕ) (c : k) (p : MvPolynomial (Fin (n + 1)) k) : Prop :=
  ∃ q, Low N q ∧ p = C c * X (Fin.last n) ^ N + q

private lemma low_zero {N : ℕ} : Low N (0 : MvPolynomial (Fin (n + 1)) k) := Or.inr rfl

private lemma low_add {N : ℕ} {p q : MvPolynomial (Fin (n + 1)) k} (hp : Low N p)
    (hq : Low N q) : Low N (p + q) := by
  rcases hp with hp | rfl
  · rcases hq with hq | rfl
    · exact Or.inl (lt_of_le_of_lt (degreeOf_add_le _ _ _) (max_lt hp hq))
    · rw [add_zero]
      exact Or.inl hp
  · simpa using hq

private lemma low_mul {N M : ℕ} {p r : MvPolynomial (Fin (n + 1)) k} (hp : Low N p)
    (hr : degreeOf (Fin.last n) r ≤ M) : Low (N + M) (p * r) := by
  rcases hp with hp | rfl
  · exact Or.inl (lt_of_le_of_lt (degreeOf_mul_le _ _ _) (by omega))
  · rw [zero_mul]
    exact low_zero

private lemma degreeOf_C_mul_X_pow_le (c : k) (N : ℕ) :
    degreeOf (Fin.last n) (C c * X (Fin.last n) ^ N) ≤ N :=
  (degreeOf_C_mul_le _ _ _).trans ((degreeOf_pow_le _ _ _).trans (by simp))

private lemma degreeOf_le_of_top {N : ℕ} {c : k} {p : MvPolynomial (Fin (n + 1)) k}
    (h : Top N c p) : degreeOf (Fin.last n) p ≤ N := by
  obtain ⟨q, hq, rfl⟩ := h
  refine (degreeOf_add_le _ _ _).trans (max_le (degreeOf_C_mul_X_pow_le _ _) ?_)
  rcases hq with hq | rfl
  · exact hq.le
  · simp

private lemma top_mul {N M : ℕ} {c d : k} {p p' : MvPolynomial (Fin (n + 1)) k}
    (h : Top N c p) (h' : Top M d p') : Top (N + M) (c * d) (p * p') := by
  obtain ⟨q, hq, rfl⟩ := h
  obtain ⟨q', hq', rfl⟩ := h'
  refine ⟨C c * X (Fin.last n) ^ N * q' + q * (C d * X (Fin.last n) ^ M + q'),
    low_add ?_ (low_mul hq (degreeOf_le_of_top ⟨q', hq', rfl⟩)), ?_⟩
  · have h1 := low_mul hq' (degreeOf_C_mul_X_pow_le (n := n) c N)
    rwa [add_comm M N, ← mul_comm] at h1
  · rw [map_mul, pow_add]
    ring

private lemma top_one : Top 0 (1 : k) (1 : MvPolynomial (Fin (n + 1)) k) :=
  ⟨0, low_zero, by simp⟩

private lemma top_C (r : k) : Top 0 r (C r : MvPolynomial (Fin (n + 1)) k) :=
  ⟨0, low_zero, by simp⟩

private lemma top_pow {N : ℕ} {c : k} {p : MvPolynomial (Fin (n + 1)) k} (h : Top N c p)
    (m : ℕ) : Top (N * m) (c ^ m) (p ^ m) := by
  induction m with
  | zero => simpa using top_one
  | succ m ih =>
    rw [pow_succ, pow_succ, Nat.mul_succ]
    exact top_mul ih h

private lemma top_prod {ι : Type*} (s : Finset ι) (N : ι → ℕ) (c : ι → k)
    (p : ι → MvPolynomial (Fin (n + 1)) k) (h : ∀ i ∈ s, Top (N i) (c i) (p i)) :
    Top (∑ i ∈ s, N i) (∏ i ∈ s, c i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using top_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    exact top_mul (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma top_sum {ι : Type*} (s : Finset ι) (N : ℕ) (c : ι → k)
    (p : ι → MvPolynomial (Fin (n + 1)) k) (h : ∀ i ∈ s, Top N (c i) (p i)) :
    Top N (∑ i ∈ s, c i) (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, low_zero, by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    obtain ⟨q1, h1, e1⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨q2, h2, e2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨q1 + q2, low_add h1 h2, by rw [e1, e2, map_add]; ring⟩

private lemma top_lift {E N : ℕ} {c : k} {p : MvPolynomial (Fin (n + 1)) k} (h : Top E c p)
    (hE : E ≤ N) : Top N (if E = N then c else 0) p := by
  by_cases hEN : E = N
  · subst hEN
    simpa using h
  · rw [if_neg hEN]
    exact ⟨p, Or.inl (lt_of_le_of_lt (degreeOf_le_of_top h) (lt_of_le_of_ne hE hEN)),
      by simp⟩

private lemma degreeOf_sub_lt_of_top {N : ℕ} {c : k} {p : MvPolynomial (Fin (n + 1)) k}
    (h : Top N c p) (hN : 0 < N) :
    degreeOf (Fin.last n) (p - C c * X (Fin.last n) ^ N) < N := by
  obtain ⟨q, hq, rfl⟩ := h
  rw [add_sub_cancel_left]
  rcases hq with hq | rfl
  · exact hq
  · simpa using hN

/-- The substitution family `yᵢ ↦ yᵢ + aᵢ y_m^{wᵢ}`, `y_m ↦ y_m`. -/
private noncomputable def gen (w : Fin (n + 1) → ℕ) (a : Fin n → k) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) k :=
  Fin.lastCases (X (Fin.last n)) (fun i ↦ X i.castSucc + C (a i) * X (Fin.last n) ^ w i.castSucc)

private lemma top_gen {w : Fin (n + 1) → ℕ} (hw : ∀ i, 0 < w i) (hl : w (Fin.last n) = 1)
    (a : Fin n → k) (j : Fin (n + 1)) : Top (w j) (Fin.lastCases (1 : k) a j) (gen w a j) := by
  cases j using Fin.lastCases with
  | last =>
    simp only [gen, Fin.lastCases_last, hl]
    exact ⟨0, low_zero, by simp⟩
  | cast i =>
    simp only [gen, Fin.lastCases_castSucc]
    refine ⟨X i.castSucc, Or.inl ?_, by ring⟩
    rw [degreeOf_X, if_neg (Fin.castSucc_lt_last i).ne']
    exact hw _

private lemma top_aeval {w : Fin (n + 1) → ℕ} (hw : ∀ i, 0 < w i) (hl : w (Fin.last n) = 1)
    (a : Fin n → k) (f : MvPolynomial (Fin (n + 1)) k) (N : ℕ)
    (hN : ∀ v ∈ f.support, ∑ j, w j * v j ≤ N) :
    Top N (∑ v ∈ f.support, if ∑ j, w j * v j = N then
        f.coeff v * ∏ j, Fin.lastCases (1 : k) a j ^ v j else 0)
      (aeval (gen w a) f) := by
  have : aeval (gen w a) f = ∑ v ∈ f.support, aeval (gen w a) (monomial v (f.coeff v)) := by
    rw [← map_sum, support_sum_monomial_coeff]
  rw [this]
  refine top_sum _ _ _ _ fun v hv => top_lift ?_ (hN v hv)
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), algebraMap_eq]
  simpa only [zero_add] using top_mul (top_C (n := n) (f.coeff v))
    (top_prod Finset.univ (fun j => w j * v j) _ _
      fun j _ => top_pow (top_gen hw hl a j) (v j))

private lemma sum_mul_lt_of_head_lt {d m : ℕ} (hd : 0 < d) {w : Fin (m + 1) → ℕ}
    (hw : ∀ i, 0 < w i) (hdec : ∀ i j, i < j → d * w j < w i) {v u : Fin (m + 1) → ℕ}
    (hu : ∑ i, u i ≤ d) (hlt : u 0 < v 0) : ∑ i, w i * u i < ∑ i, w i * v i := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ (fun i => w i * v i)]
  rw [Fin.sum_univ_succ] at hu
  set B := (w 0 - 1) / d with hBdef
  have hB : ∀ j : Fin m, w j.succ ≤ B := fun j => by
    rw [hBdef, Nat.le_div_iff_mul_le hd]
    have := hdec 0 j.succ (Fin.succ_pos j)
    rw [mul_comm] at this
    omega
  have h1 : ∑ j : Fin m, w j.succ * u j.succ ≤ ∑ j : Fin m, B * u j.succ :=
    Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (hB j)
  rw [← Finset.mul_sum] at h1
  have h2 : B * ∑ j : Fin m, u j.succ ≤ B * d := Nat.mul_le_mul_left _ (by omega)
  have h3 : B * d ≤ w 0 - 1 := Nat.div_mul_le_self _ _
  have h4 : w 0 * (u 0 + 1) ≤ w 0 * v 0 := Nat.mul_le_mul_left _ hlt
  have h5 := hw 0
  rw [mul_add, mul_one] at h4
  omega

private lemma sum_mul_inj (d : ℕ) (hd : 0 < d) : ∀ (m : ℕ) (w : Fin m → ℕ), (∀ i, 0 < w i) →
    (∀ i j, i < j → d * w j < w i) → ∀ v u : Fin m → ℕ, ∑ i, v i ≤ d → ∑ i, u i ≤ d →
    ∑ i, w i * v i = ∑ i, w i * u i → v = u
  | 0, w, _, _, v, u, _, _, _ => funext fun i => i.elim0
  | m + 1, w, hw, hdec, v, u, hv, hu, h => by
    rcases lt_trichotomy (v 0) (u 0) with hlt | heq | hgt
    · exact absurd h (sum_mul_lt_of_head_lt hd hw hdec hv hlt).ne
    · rw [Fin.sum_univ_succ, Fin.sum_univ_succ (fun i => w i * u i), heq] at h
      have h' := Nat.add_left_cancel h
      rw [Fin.sum_univ_succ] at hv hu
      have := sum_mul_inj d hd m (fun j => w j.succ) (fun i => hw _)
        (fun i j hij => hdec _ _ (Fin.succ_lt_succ_iff.2 hij)) (fun j => v j.succ)
        (fun j => u j.succ) (by omega) (by omega) h'
      funext i
      exact Fin.cases heq (fun j => congrFun this j) i
    · exact absurd h (sum_mul_lt_of_head_lt hd hw hdec hu hgt).ne'

private lemma sum_le_totalDegree {f : MvPolynomial (Fin (n + 1)) k} {v : Fin (n + 1) →₀ ℕ}
    (hv : v ∈ f.support) : ∑ j, v j ≤ f.totalDegree := by
  simpa [Finsupp.sum_fintype] using le_totalDegree hv

private lemma exists_mem_support_sum_eq_totalDegree {f : MvPolynomial (Fin (n + 1)) k}
    (hf : f ≠ 0) : ∃ v ∈ f.support, ∑ j, v j = f.totalDegree := by
  obtain ⟨v, hv, hsup⟩ := Finset.exists_mem_eq_sup f.support (support_nonempty.2 hf)
    (fun s => s.sum fun _ e => e)
  refine ⟨v, hv, ?_⟩
  rw [totalDegree, hsup]
  simp [Finsupp.sum_fintype]

private lemma sum_filter_monomial_castSucc_ne_zero {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    {v₁ : Fin (n + 1) →₀ ℕ} (hv₁ : v₁ ∈ f.support) (hd : ∑ j, v₁ j = d) :
    ∑ v ∈ f.support.filter (fun v => ∑ j, v j = d),
      monomial (Finsupp.equivFunOnFinite.symm fun i : Fin n => v i.castSucc) (f.coeff v) ≠ 0 := by
  intro h0
  have hcoef : (∑ v ∈ f.support.filter (fun v => ∑ j, v j = d),
        monomial (Finsupp.equivFunOnFinite.symm fun i : Fin n => v i.castSucc) (f.coeff v)).coeff
        (Finsupp.equivFunOnFinite.symm fun i : Fin n => v₁ i.castSucc) =
      f.coeff v₁ := by
    rw [coeff_sum, Finset.sum_eq_single v₁]
    · simp [coeff_monomial]
    · intro v hv hne
      rw [coeff_monomial, if_neg]
      intro heq
      apply hne
      have h₁ : ∀ i : Fin n, v i.castSucc = v₁ i.castSucc := fun i => by
        simpa using congrArg (fun x => x i) heq
      have hs := (Finset.mem_filter.1 hv).2
      have hs₁ := hd
      rw [Fin.sum_univ_castSucc] at hs hs₁
      simp only [h₁] at hs
      refine Finsupp.ext fun j => ?_
      cases j using Fin.lastCases with
      | last => omega
      | cast i => exact h₁ i
    · exact fun h => absurd (Finset.mem_filter.2 ⟨hv₁, hd⟩) h
  exact mem_support_iff.1 hv₁ (by rw [← hcoef, h0, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply])

private lemma mul_lt_of_succ_mul_lt {d : ℕ} {w : Fin (n + 1) → ℕ} (hd : 0 < d)
    (hdec : ∀ i : Fin n, d * w i.succ < w i.castSucc) (i j : Fin (n + 1)) (hij : i < j) :
    d * w j < w i := by
  have anti : StrictAnti w := Fin.strictAnti_iff_succ_lt.2 fun i =>
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hd) (hdec i)
  obtain ⟨i', rfl⟩ := Fin.exists_castSucc_eq.2 (lt_of_lt_of_le hij (Fin.le_last j)).ne
  exact lt_of_le_of_lt
    (Nat.mul_le_mul_left _ (anti.antitone (Fin.castSucc_lt_iff_succ_le.1 hij))) (hdec i')

/-- **Kollár, proof of Theorem 1.35, infinite fields.** Let `k` be an infinite field, `m ≥ 1`
and `f ∈ k[y₁, …, y_m]` of total degree `d ≥ 1`. Then there are `a₁, …, a_{m-1} ∈ k` and
`c ∈ k^×` such that `f(y₁ + a₁ y_m, …, y_{m-1} + a_{m-1} y_m, y_m) - c y_mᵈ`, viewed as a
polynomial in `y_m` with coefficients in `k[y₁, …, y_{m-1}]`, has degree `< d` in `y_m`. -/
@[mmp "lem_kr1b_noether_linear_change"]
theorem exists_linear_change_degreeOf_lt [Infinite k] (f : MvPolynomial (Fin (n + 1)) k)
    (hf : 1 ≤ f.totalDegree) :
    ∃ (a : Fin n → k) (c : k), c ≠ 0 ∧
      degreeOf (Fin.last n)
          (aeval (Fin.lastCases (X (Fin.last n))
              (fun i ↦ X i.castSucc + C (a i) * X (Fin.last n))) f -
            C c * X (Fin.last n) ^ f.totalDegree) < f.totalDegree := by
  classical
  have hne : f ≠ 0 := by
    rintro rfl
    simp at hf
  obtain ⟨v1, hv1, hv1d⟩ := exists_mem_support_sum_eq_totalDegree hne
  set d := f.totalDegree with hd
  have hdeg : ∀ v ∈ f.support, ∑ j, v j ≤ d := fun v hv => sum_le_totalDegree hv
  let S := f.support.filter (fun v => ∑ j, v j = d)
  let u : (Fin (n + 1) →₀ ℕ) → (Fin n →₀ ℕ) := fun v =>
    Finsupp.equivFunOnFinite.symm fun i => v i.castSucc
  let H : MvPolynomial (Fin n) k := ∑ v ∈ S, monomial (u v) (f.coeff v)
  have hH : H ≠ 0 := sum_filter_monomial_castSucc_ne_zero hv1 hv1d
  obtain ⟨a, ha⟩ : ∃ a : Fin n → k, eval a H ≠ 0 := by
    by_contra! hcon
    exact hH (MvPolynomial.funext fun x => by simp [hcon x])
  have key := top_aeval (w := fun _ => 1) (fun _ => one_pos) rfl a f d
    (fun v hv => by simpa using hdeg v hv)
  have hc0 : (∑ v ∈ f.support, if ∑ j, (fun _ => 1) j * v j = d then
      f.coeff v * ∏ j, Fin.lastCases (motive := fun _ => k) 1 a j ^ v j else 0) = eval a H := by
    simp only [one_mul]
    rw [← Finset.sum_filter]
    simp only [H, S, map_sum, eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Fin.prod_univ_castSucc]
    simp [u]
  rw [hc0] at key
  have hfam : (Fin.lastCases (X (Fin.last n))
      (fun i ↦ X i.castSucc + C (a i) * X (Fin.last n)) :
        Fin (n + 1) → MvPolynomial (Fin (n + 1)) k) = gen (fun _ => 1) a := by
    funext j
    cases j using Fin.lastCases <;> simp [gen]
  refine ⟨a, eval a H, ha, ?_⟩
  rw [hfam]
  exact degreeOf_sub_lt_of_top key hf

/-- **Kollár, proof of Theorem 1.35, all fields** (Nagata's change of coordinates). Let `k` be a
field, `m ≥ 1`, `f ∈ k[y₁, …, y_m]` of total degree `d ≥ 1`, and `n₁, …, n_m` positive integers
with `n_m = 1` and `nᵢ > d n_{i+1}` for `i < m`. Then there are `c ∈ k^×` and `N ≥ 1` such that
`f(y₁ + y_m^{n₁}, …, y_{m-1} + y_m^{n_{m-1}}, y_m) - c y_m^N` has degree `< N` in `y_m`
(coefficients in `k[y₁, …, y_{m-1}]`). -/
@[mmp "lem_kr1b_noether_nagata_change"]
theorem exists_nagata_change_degreeOf_lt (f : MvPolynomial (Fin (n + 1)) k)
    (hf : 1 ≤ f.totalDegree) (w : Fin (n + 1) → ℕ) (hw : ∀ i, 0 < w i)
    (hlast : w (Fin.last n) = 1) (hdec : ∀ i : Fin n, f.totalDegree * w i.succ < w i.castSucc) :
    ∃ (c : k) (N : ℕ), c ≠ 0 ∧ 1 ≤ N ∧
      degreeOf (Fin.last n)
          (aeval (Fin.lastCases (X (Fin.last n))
              (fun i ↦ X i.castSucc + X (Fin.last n) ^ w i.castSucc)) f -
            C c * X (Fin.last n) ^ N) < N := by
  classical
  have hne : f ≠ 0 := by
    rintro rfl
    simp at hf
  obtain ⟨v1, hv1, hv1d⟩ := exists_mem_support_sum_eq_totalDegree hne
  set d := f.totalDegree with hd
  have hEge : ∀ v : Fin (n + 1) →₀ ℕ, ∑ j, v j ≤ ∑ j, w j * v j := fun v =>
    Finset.sum_le_sum fun j _ => Nat.le_mul_of_pos_left _ (hw j)
  obtain ⟨vs, hvs, hmax⟩ := Finset.exists_max_image f.support (fun v => ∑ j, w j * v j)
    (support_nonempty.2 hne)
  have hN1 : 1 ≤ ∑ j, w j * vs j := hf.trans (hv1d.ge.trans ((hEge v1).trans (hmax v1 hv1)))
  have key := top_aeval hw hlast (fun _ : Fin n => (1 : k)) f (∑ j, w j * vs j) hmax
  have hcoef : ∀ j : Fin (n + 1),
      Fin.lastCases (motive := fun _ => k) 1 (fun _ : Fin n => 1) j = 1 := by
    intro j
    cases j using Fin.lastCases <;> simp
  simp only [hcoef, one_pow, Finset.prod_const_one, mul_one] at key
  rw [Finset.sum_eq_single vs] at key
  · rw [if_pos rfl] at key
    have hfam : (Fin.lastCases (X (Fin.last n))
        (fun i ↦ X i.castSucc + X (Fin.last n) ^ w i.castSucc) :
          Fin (n + 1) → MvPolynomial (Fin (n + 1)) k) = gen w (fun _ => 1) := by
      funext j
      cases j using Fin.lastCases <;> simp [gen]
    refine ⟨f.coeff vs, _, mem_support_iff.1 hvs, hN1, ?_⟩
    rw [hfam]
    exact degreeOf_sub_lt_of_top key hN1
  · intro v hv hne'
    rw [if_neg]
    intro heq
    exact hne' (Finsupp.ext (congrFun (sum_mul_inj d (by omega) (n + 1) w hw
      (mul_lt_of_succ_mul_lt (by omega) hdec) v vs (sum_le_totalDegree hv)
      (sum_le_totalDegree hvs) heq) ·))
  · exact fun h => absurd hvs h

end Noether

section Lifting

variable {A : Type*} [CommRing A] [IsLocalRing A]

/-- **Kollár 1.37**: a set-theoretic lifting is well defined modulo higher order terms. Let
`(A, 𝔪)` be a local ring, `x, y ∈ 𝔪`, `i, j ≥ 0` and `r, r' ∈ A` with the same image in
`A / 𝔪`. Then `r xⁱ yʲ - r' xⁱ yʲ ∈ 𝔪^{i+j+1}`. -/
@[mmp "lem_kr1b_set_theoretic_lifting_well_defined"]
theorem mul_pow_mul_pow_sub_mem_maximalIdeal_pow {x y : A}
    (hx : x ∈ IsLocalRing.maximalIdeal A) (hy : y ∈ IsLocalRing.maximalIdeal A) (i j : ℕ)
    {r r' : A} (hr : IsLocalRing.residue A r = IsLocalRing.residue A r') :
    r * x ^ i * y ^ j - r' * x ^ i * y ^ j ∈ IsLocalRing.maximalIdeal A ^ (i + j + 1) := by
  have hrr : r - r' ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hr, sub_self]
  rw [← sub_mul, ← sub_mul, mul_assoc, add_comm, pow_add, pow_one, pow_add]
  exact Ideal.mul_mem_mul hrr
    (Ideal.mul_mem_mul (Ideal.pow_mem_pow hx i) (Ideal.pow_mem_pow hy j))

end Lifting

end MMP.Resolution.Kollar
