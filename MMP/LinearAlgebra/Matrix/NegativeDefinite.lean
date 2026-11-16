module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# A sufficient condition for negative definiteness

Let `A` be a real symmetric matrix whose off-diagonal entries are nonnegative. If some
nonnegative vector `w` has `∑ᵢ wᵢ Aᵢⱼ < 0` for every `j`, then `A` is negative definite.

This is the linear algebra behind the negative definiteness of the intersection matrix of the
exceptional curves of a generically finite morphism from a smooth surface (Kollár, *Lectures on
resolution of singularities*, Theorem 2.12): `w` is the vector of coefficients of the `Cᵢ` in an
effective Cartier divisor `W` with `-W` relatively ample.

## Main results

* `MMP.MatrixPosDef.posDef_neg_of_offDiag_nonneg_of_sum_mul_neg`

## Implementation notes

The source's proof maximises the quadratic form on a cube. The proof here is the identity
`xᵀ A x = ∑ᵢ wᵢ rᵢ yᵢ² - ½ ∑ᵢⱼ Aᵢⱼ wᵢ wⱼ (yᵢ - yⱼ)²` with `xᵢ = wᵢ yᵢ` and `rᵢ = ∑ⱼ Aᵢⱼ wⱼ`,
which needs no sign decomposition of `x`.
-/

@[expose] public section

open Finset

namespace MMP.MatrixPosDef

open _root_.Matrix

/-- A symmetric matrix with nonnegative off-diagonal entries and `∑ⱼ Aᵢⱼ wⱼ < 0` for a positive
vector `w` has negative quadratic form on every nonzero `x`. -/
theorem sum_sum_mul_mul_neg_of_offDiag_nonneg {n : Type*} [Fintype n] (A : Matrix n n ℝ)
    (hsymm : ∀ i j, A i j = A j i) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j) (w : n → ℝ)
    (hwpos : ∀ i, 0 < w i) (hAw : ∀ i, ∑ j, A i j * w j < 0) (x : n → ℝ) (hx0 : x ≠ 0) :
    ∑ i, ∑ j, x i * A i j * x j < 0 := by
  have hw : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  set y : n → ℝ := fun i => x i / w i with hy
  have hx : ∀ i, x i = w i * y i := fun i => by
    simp only [hy]
    field_simp [(hwpos i).ne']
  set r : n → ℝ := fun i => ∑ j, A i j * w j with hr
  have hS : 0 ≤ ∑ i, ∑ j, A i j * w i * w j * (y i - y j) ^ 2 :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => by
      by_cases hij : i = j
      · simp [hij]
      · exact mul_nonneg (mul_nonneg (mul_nonneg (hoff i j hij) (hw i)) (hw j)) (sq_nonneg _)
  have h1 : ∑ i, ∑ j, A i j * w i * w j * y i ^ 2 = ∑ i, w i * r i * y i ^ 2 := by
    refine sum_congr rfl fun i _ => ?_
    simp only [hr, mul_sum, sum_mul]
    exact sum_congr rfl fun j _ => by ring
  have h3 : ∑ i, ∑ j, A i j * w i * w j * y j ^ 2 = ∑ i, w i * r i * y i ^ 2 := by
    rw [sum_comm, ← h1]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hsymm j i]
    ring
  have h2 : ∑ i, ∑ j, x i * A i j * x j = ∑ i, ∑ j, A i j * w i * w j * (y i * y j) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hx i, hx j]
    ring
  have hexp : ∑ i, ∑ j, A i j * w i * w j * (y i - y j) ^ 2 =
      ∑ i, ∑ j, A i j * w i * w j * y i ^ 2 + ∑ i, ∑ j, A i j * w i * w j * y j ^ 2 -
        2 * ∑ i, ∑ j, A i j * w i * w j * (y i * y j) := by
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx0
  have hneg : ∑ i, w i * r i * y i ^ 2 < 0 := by
    refine (sum_lt_sum (fun i _ => ?_) ⟨i0, mem_univ _, ?_⟩).trans_eq sum_const_zero
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (hw i) (hAw i).le) (sq_nonneg _)
    · exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (hwpos i0) (hAw i0))
        (pow_pos (abs_pos.mpr (right_ne_zero_of_mul (hx i0 ▸ hi0))) 2 |>.trans_eq (sq_abs _))
  linarith

/-- **A symmetric matrix with nonnegative off-diagonal entries that is negative on a nonnegative
vector is negative definite.** Let `A` be a real symmetric matrix with `Aᵢⱼ ≥ 0` for `i ≠ j` and
`w ≥ 0` with `∑ᵢ wᵢ Aᵢⱼ < 0` for every `j`. Then `-A` is positive definite. -/
theorem posDef_neg_of_offDiag_nonneg_of_sum_mul_neg {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hsymm : ∀ i j, A i j = A j i) (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (w : n → ℝ) (hw : ∀ i, 0 ≤ w i) (hAw : ∀ j, ∑ i, w i * A i j < 0) : (-A).PosDef := by
  have hwpos : ∀ i, 0 < w i := fun i => (hw i).lt_of_ne' fun h => by
    have : 0 ≤ ∑ l, w l * A l i := sum_nonneg fun l _ => by
      by_cases hl : l = i
      · simp [hl, h]
      · exact mul_nonneg (hw l) (hoff l i hl)
    linarith [hAw i]
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · refine IsHermitian.neg ?_
    ext i j
    simp [conjTranspose_apply, hsymm j i]
  · have e : star x ⬝ᵥ ((-A) *ᵥ x) = -∑ i, ∑ j, x i * A i j * x j := by
      simp only [dotProduct, mulVec, Matrix.neg_apply, star_trivial, mul_sum, ← sum_neg_distrib]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [e, neg_pos]
    exact sum_sum_mul_mul_neg_of_offDiag_nonneg A hsymm hoff w hwpos
      (fun i => (sum_congr rfl fun j _ => by rw [hsymm i j, mul_comm]).trans_lt (hAw i)) x hx

end MMP.MatrixPosDef
