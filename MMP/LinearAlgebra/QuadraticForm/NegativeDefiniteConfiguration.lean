/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Negative definite configurations (FA 2.19.3.1)

Let `Q` be a negative definite symmetric bilinear form on a real vector space and `E₁, …, E_n`
linearly independent vectors such that `Q(E_i, E_j) ≥ 0` for `i ≠ j`. If `F = ∑ α_i E_i` has
`Q(F, E_i) ≥ 0` for all `i`, then all `α_i ≤ 0`; if moreover the configuration is connected, then
`F = 0` or all `α_i < 0`.

## Main results

* `MMP.Flips.coeff_nonpos_of_pairing_nonneg`
* `MMP.Flips.eq_zero_or_coeff_neg_of_pairing_nonneg`

## Implementation notes

FA states the strict inequality without the connectedness hypothesis, where it is false: for
`Q = -I` on `ℝ²` and `F = -E₁`, `Q(F, E₁) = 1`, `Q(F, E₂) = 0`, `F ≠ 0` and `α₂ = 0`. The
connectedness hypothesis corrects this.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.19.3.1
-/

@[expose] public noncomputable section

namespace MMP.Flips

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

private lemma bilin_sum_smul_left (Q : LinearMap.BilinForm ℝ V) (E : ι → V) (β : ι → ℝ) (y : V) :
    Q (∑ j, β j • E j) y = ∑ j, β j * Q (E j) y := by
  simp [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]

/-- **FA Lemma 2.19.3.1, first part.** Let `Q` be a negative definite symmetric bilinear form on
a real vector space and `E₁, …, E_n` linearly independent vectors such that `Q(E_i, E_j) ≥ 0`
for `i ≠ j`. If `F = ∑ α_i E_i` satisfies `Q(F, E_i) ≥ 0` for all `i`, then `α_i ≤ 0` for all
`i`. -/
@[mmp "lem_fa2_negative_definite_nonneg_pairing_coefficients_nonpos"]
theorem coeff_nonpos_of_pairing_nonneg (Q : LinearMap.BilinForm ℝ V) (hQs : Q.IsSymm)
    (hQ : ∀ x, x ≠ 0 → Q x x < 0) (E : ι → V) (hEli : LinearIndependent ℝ E)
    (hE : ∀ i j, i ≠ j → 0 ≤ Q (E i) (E j)) (α : ι → ℝ)
    (hF : ∀ i, 0 ≤ Q (∑ j, α j • E j) (E i)) (i : ι) : α i ≤ 0 := by
  by_contra hi
  push Not at hi
  set Fp : V := ∑ j, max (α j) 0 • E j with hFp
  set Fm : V := ∑ j, max (-α j) 0 • E j with hFm
  have hsplit : ∑ j, α j • E j = Fp - Fm := by
    rw [hFp, hFm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul]
    congr 1
    rcases le_total (α j) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  have hFp0 : Fp ≠ 0 := by
    intro h0
    have := (Fintype.linearIndependent_iff.mp hEli) _ h0 i
    rw [max_eq_left hi.le] at this
    linarith
  have hneg := hQ Fp hFp0
  have hexp : Q Fp Fp = ∑ j, max (α j) 0 * Q (E j) Fp := by
    conv_lhs => rw [hFp]
    rw [bilin_sum_smul_left]
  obtain ⟨j, -, hj⟩ : ∃ j ∈ (Finset.univ : Finset ι), max (α j) 0 * Q (E j) Fp < 0 := by
    by_contra hc
    push Not at hc
    have := Finset.sum_nonneg hc
    linarith
  have hαj : 0 < α j := by
    by_contra h
    push Not at h
    rw [max_eq_right h] at hj
    simp at hj
  rw [max_eq_left hαj.le] at hj
  have hQj : Q (E j) Fp < 0 := by
    by_contra h; push Not at h; nlinarith
  have hm : 0 ≤ Q Fm (E j) := by
    rw [hFm, bilin_sum_smul_left]
    refine Finset.sum_nonneg fun k _ => ?_
    by_cases hk : k = j
    · subst hk; rw [max_eq_right (by linarith)]; simp
    · exact mul_nonneg (le_max_right _ _) (hE k j hk)
  have h1 := hF j
  rw [hsplit, LinearMap.map_sub₂, hQs.eq Fp (E j)] at h1
  linarith

/-- **FA Lemma 2.19.3.1, "strict inequality holds unless `F = 0`" (corrected).** In the situation
of `MMP.Flips.coeff_nonpos_of_pairing_nonneg`, assume moreover that the configuration is
connected: the graph on the indices with an edge between `i ≠ j` whenever `Q(E_i, E_j) > 0` is
connected. Then either `F = 0` or `α_i < 0` for all `i`. -/
@[mmp "lem_fa2_negative_definite_strict"]
theorem eq_zero_or_coeff_neg_of_pairing_nonneg (Q : LinearMap.BilinForm ℝ V) (hQs : Q.IsSymm)
    (hQ : ∀ x, x ≠ 0 → Q x x < 0) (E : ι → V) (hEli : LinearIndependent ℝ E)
    (hE : ∀ i j, i ≠ j → 0 ≤ Q (E i) (E j))
    (hconn : (SimpleGraph.fromRel fun i j => 0 < Q (E i) (E j)).Connected) (α : ι → ℝ)
    (hF : ∀ i, 0 ≤ Q (∑ j, α j • E j) (E i)) : ∑ j, α j • E j = 0 ∨ ∀ i, α i < 0 := by
  have hle := coeff_nonpos_of_pairing_nonneg Q hQs hQ E hEli hE α hF
  by_cases hall : ∀ i, α i < 0
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨b, hb⟩ := hall
  have hb0 : α b = 0 := le_antisymm (hle b) hb
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, α a ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by simp [h])
  obtain ⟨d, -, hd1, hd2⟩ :=
    (hconn.preconnected a b).some.exists_boundary_dart {k | α k ≠ 0} ha (by simpa using hb0)
  have hadj := d.adj
  rw [SimpleGraph.fromRel_adj] at hadj
  obtain ⟨-, hpos⟩ := hadj
  set u := d.fst
  set v := d.snd
  have hv : α v = 0 := by simpa using hd2
  have hu : α u < 0 := lt_of_le_of_ne (hle u) hd1
  have huv : 0 < Q (E u) (E v) := by
    rcases hpos with h | h
    · exact h
    · rwa [hQs.eq] at h
  have h1 := hF v
  rw [bilin_sum_smul_left] at h1
  have : ∑ l, α l * Q (E l) (E v) < ∑ _l : ι, (0 : ℝ) := by
    refine Finset.sum_lt_sum (fun l _ => ?_) ⟨u, Finset.mem_univ _, by nlinarith⟩
    by_cases hl : l = v
    · subst hl; simp [hv]
    · exact mul_nonpos_of_nonpos_of_nonneg (hle l) (hE l v hl)
  simp at this
  linarith

end MMP.Flips
