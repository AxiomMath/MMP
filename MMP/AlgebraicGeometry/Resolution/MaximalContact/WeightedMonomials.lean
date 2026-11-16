module

public import MMP.Attr
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Weighted monomials and the bound `(m - 1) · lcm(2, …, m) ≤ m!` (Kollár 3.99.9–3.99.10)

Two elementary facts used in Kollár's proof that the maximal-coefficient ideal is
`D`-balanced (*Lectures on resolution of singularities*, 3.99).

Let `L = lcm(2, …, m)` and let `u₁, …, u_m` be variables with `deg uᵢ = i`. A monomial
`U = ∏ uᵢ^{cᵢ}` is its exponent vector `c`, and `deg U` is the weight `∑ i · cᵢ` of `c`.

## Main statements

* `MMP.Resolution.Kollar.sub_one_mul_lcm_le_factorial`: for `m ≥ 6`,
  `(m - 1) · lcm(2, …, m) ≤ m!` (Aside 3.99.10).
* `MMP.Resolution.Kollar.exists_weighted_monomial_split`: a monomial of degree at least
  `(r + m - 1) L` is a product `U₁ U₂` of monomials with `deg U₁ = r L` (Claim 3.99.9, with the
  misprint of the book corrected).

## Implementation notes

The variable `uᵢ` (`1 ≤ i ≤ m`) is indexed by `i - 1 : Fin m`, so a monomial is an element
`c : Fin m →₀ ℕ` (`c (i - 1)` the exponent of `uᵢ`), the product of monomials is the sum of
exponent vectors, and the degree is `Finsupp.weight (fun i ↦ i + 1) c`.
-/

@[expose] public section

namespace MMP.Resolution.Kollar

/-- `lcm(2, …, m)`, the least common multiple of the integers `2, …, m` (`1` for `m ≤ 1`). -/
def lcmUpTo (m : ℕ) : ℕ :=
  (Finset.Icc 2 m).lcm id

/-- The weight `deg uᵢ = i` of the variable `uᵢ`, indexed by `i - 1 : Fin m`. -/
def monomialWeight (m : ℕ) : Fin m → ℕ :=
  fun i ↦ (i : ℕ) + 1

private lemma lcmUpTo_dvd_factorial (k : ℕ) : lcmUpTo k ∣ k.factorial := by
  unfold lcmUpTo
  apply Finset.lcm_dvd
  intro i hi
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi
  exact Nat.dvd_factorial (m := i) (by omega) h2

private lemma lcmUpTo_pos (k : ℕ) : 0 < lcmUpTo k :=
  Nat.pos_of_dvd_of_pos (lcmUpTo_dvd_factorial k) k.factorial_pos

private lemma dvd_lcmUpTo {i k : ℕ} (h2 : 2 ≤ i) (hk : i ≤ k) : i ∣ lcmUpTo k :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.2 ⟨h2, hk⟩)

private lemma monomialWeight_dvd_lcmUpTo {m : ℕ} (i : Fin m) :
    monomialWeight m i ∣ lcmUpTo m := by
  by_cases h1 : (i : ℕ) = 0
  · simp [monomialWeight, h1]
  · exact dvd_lcmUpTo (by simp [monomialWeight]; omega) i.isLt

private lemma lcmUpTo_succ {k : ℕ} (hk : 1 ≤ k) :
    lcmUpTo (k + 1) = Nat.lcm (k + 1) (lcmUpTo k) := by
  unfold lcmUpTo
  rw [show Finset.Icc 2 (k + 1) = insert (k + 1) (Finset.Icc 2 k) by grind, Finset.lcm_insert]
  rfl

/-- `k! / lcm(2..k)`. -/
private def facQuot (k : ℕ) : ℕ := k.factorial / lcmUpTo k

private lemma facQuot_spec (k : ℕ) : k.factorial = lcmUpTo k * facQuot k :=
  (Nat.mul_div_cancel' (lcmUpTo_dvd_factorial k)).symm

private lemma facQuot_succ {k : ℕ} (hk : 1 ≤ k) :
    facQuot (k + 1) = Nat.gcd (k + 1) (lcmUpTo k) * facQuot k := by
  apply Nat.eq_of_mul_eq_mul_left (lcmUpTo_pos (k + 1))
  have hg := Nat.gcd_mul_lcm (k + 1) (lcmUpTo k)
  rw [← lcmUpTo_succ hk] at hg
  rw [← facQuot_spec, Nat.factorial_succ, facQuot_spec k, ← mul_assoc, ← hg]
  ring

private lemma facQuot_succ_ge {k : ℕ} (hk : 1 ≤ k) : facQuot k ≤ facQuot (k + 1) := by
  rw [facQuot_succ hk]
  have : 0 < Nat.gcd (k + 1) (lcmUpTo k) := Nat.gcd_pos_of_pos_right _ (lcmUpTo_pos k)
  nlinarith

private lemma facQuot_succ_ge_two {k : ℕ} (hk : 1 ≤ k) (hnp : ¬ (k + 1).Prime) (h4 : 4 ≤ k + 1) :
    2 * facQuot k ≤ facQuot (k + 1) := by
  rw [facQuot_succ hk]
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := k + 1) (by omega)
  have hple : p ≤ k := by
    rcases (Nat.le_of_dvd (by omega) hpd).lt_or_eq with h | rfl
    · omega
    · exact absurd hp hnp
  have := Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (lcmUpTo_pos k))
    (Nat.dvd_gcd hpd (dvd_lcmUpTo hp.two_le hple))
  have := hp.two_le
  nlinarith

private lemma facQuot_ge (m : ℕ) (hm : 6 ≤ m) : m - 1 ≤ facQuot m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 8 with h | h
    · obtain rfl | rfl : m = 6 ∨ m = 7 := by omega
      all_goals decide +kernel
    · by_cases hp : m.Prime
      · have h1 := ih (m - 1) (by omega) (by omega)
        have h2 := ih (m - 2) (by omega) (by omega)
        have hodd : Odd m := hp.odd_of_ne_two (by omega)
        have h2d : 2 ∣ m - 1 := by
          obtain ⟨t, ht⟩ := hodd
          exact ⟨t, by omega⟩
        have hnp : ¬ (m - 1).Prime := by
          intro hq
          rcases hq.eq_one_or_self_of_dvd 2 h2d with h | h <;> omega
        have h3 := facQuot_succ_ge_two (k := m - 2) (by omega) (by
          rw [show m - 2 + 1 = m - 1 by omega]; exact hnp) (by omega)
        have h4 := facQuot_succ_ge (k := m - 1) (by omega)
        rw [show m - 2 + 1 = m - 1 by omega] at h3
        rw [show m - 1 + 1 = m by omega] at h4
        omega
      · have h1 := ih (m - 1) (by omega) (by omega)
        have := facQuot_succ_ge_two (k := m - 1) (by omega) (by
          rw [show m - 1 + 1 = m by omega]; exact hp) (by omega)
        rw [show m - 1 + 1 = m by omega] at this
        omega

/-- **Kollár, Aside 3.99.10.** For every integer `m ≥ 6`, `(m - 1) · lcm(2, …, m) ≤ m!`. -/
@[mmp "lem_kr3e_factorial_over_lcm_bound"]
theorem sub_one_mul_lcm_le_factorial (m : ℕ) (hm : 6 ≤ m) :
    (m - 1) * lcmUpTo m ≤ m.factorial := by
  rw [facQuot_spec m, mul_comm (lcmUpTo m)]
  exact Nat.mul_le_mul_right _ (facQuot_ge m hm)

/-- **Kollár, Claim 3.99.9** (corrected). Let `m ≥ 1`, `L = lcm(2, …, m)` and `r ≥ 0`, and give
the variable `uᵢ` the degree `i`. Every monomial `U` with `deg U ≥ (r + m - 1) L` is a product
`U = U₁ U₂` of monomials with `deg U₁ = r L`. -/
@[mmp "lem_kr3e_weighted_monomial_split"]
theorem exists_weighted_monomial_split (m : ℕ) (hm : 1 ≤ m) (r : ℕ) (U : Fin m →₀ ℕ)
    (hU : (r + m - 1) * lcmUpTo m ≤ Finsupp.weight (monomialWeight m) U) :
    ∃ U₁ U₂ : Fin m →₀ ℕ, U = U₁ + U₂ ∧
      Finsupp.weight (monomialWeight m) U₁ = r * lcmUpTo m := by
  induction r generalizing U with
  | zero => exact ⟨0, U, by simp, by simp⟩
  | succ r ih =>
    set L := lcmUpTo m with hL
    have hLpos : 0 < L := lcmUpTo_pos m
    have hex : ∃ i : Fin m, L / monomialWeight m i ≤ U i := by
      by_contra hcon
      push Not at hcon
      have hlt : Finsupp.weight (monomialWeight m) U < m * L := by
        rw [Finsupp.weight_eq_sum]
        calc ∑ i, U i • monomialWeight m i < ∑ _i : Fin m, L := by
              apply Finset.sum_lt_sum_of_nonempty
              · exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩
              · intro i _
                have hw : 0 < monomialWeight m i := by simp [monomialWeight]
                have h6 : (U i + 1) * monomialWeight m i ≤ L :=
                  (Nat.mul_le_mul_right _ (hcon i)).trans
                    (Nat.div_mul_cancel (monomialWeight_dvd_lcmUpTo i)).le
                rw [smul_eq_mul]
                nlinarith
          _ = m * L := by simp
      have : (r + 1 + m - 1) * L ≥ m * L := Nat.mul_le_mul_right _ (by omega)
      omega
    obtain ⟨i, hi⟩ := hex
    set e : Fin m →₀ ℕ := Finsupp.single i (L / monomialWeight m i) with he
    have hwe : Finsupp.weight (monomialWeight m) e = L := by
      rw [he, Finsupp.weight_single, smul_eq_mul]
      exact Nat.div_mul_cancel (monomialWeight_dvd_lcmUpTo i)
    have hle : e ≤ U := Finsupp.single_le_iff.2 hi
    have hsplit : U = e + (U - e) := (add_tsub_cancel_of_le hle).symm
    have hwU : Finsupp.weight (monomialWeight m) U =
        L + Finsupp.weight (monomialWeight m) (U - e) := by
      conv_lhs => rw [hsplit]
      rw [map_add, hwe]
    have h' : (r + m - 1) * L ≤ Finsupp.weight (monomialWeight m) (U - e) := by
      have : (r + 1 + m - 1) * L = (r + m - 1) * L + L := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
    obtain ⟨U₁, U₂, h1, h2⟩ := ih (U - e) h'
    refine ⟨U₁ + e, U₂, ?_, ?_⟩
    · rw [add_right_comm, ← h1]
      exact hsplit.trans (add_comm _ _)
    · rw [map_add, h2, hwe, Nat.succ_mul]

end MMP.Resolution.Kollar
