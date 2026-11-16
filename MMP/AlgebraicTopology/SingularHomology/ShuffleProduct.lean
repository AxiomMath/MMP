module

public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module

/-!
# The Leibniz rule for the shuffle product of lattice paths

A *lattice path* of length `n` in the grid `[p] × [q]` is a list of `n + 1` vertices
`(a_j, b_j) ∈ ℕ × ℕ`. The *shuffle sum* `∇_{p,q}` is the signed formal sum of the monotone
lattice paths from `(0, 0)` to `(p, q)` with unit steps; the sign of a path is `(-1)^N`, where `N`
is the number of pairs (a `y`-step, a later `x`-step). It is the universal Eilenberg–Zilber
shuffle map: applied to a `p`-simplex `σ` and a `q`-simplex `τ`, a path `(a, b)` gives the
simplex `j ↦ (σ(a_j), τ(b_j))` of the product.

The boundary of a lattice path is the alternating sum of its faces (delete the `i`-th vertex).
The Leibniz rule is
`∂ ∇_{p,q} = ∑_k (-1)^k δ^x_k ∇_{p-1,q} + (-1)^p ∑_l (-1)^l δ^y_l ∇_{p,q-1}`,
where `δ^x_k` relabels the first coordinates by the coface `δ_k : [p-1] → [p]`. It is proved by
induction on the length, decomposing a path by its first step.

## Main definitions

* `MMP.LatticePath.shuffleSum n p q`: the shuffle sum of length `n`.
* `MMP.LatticePath.bd n`: the boundary of formal sums of paths of length `n`.

## Main results

* `MMP.LatticePath.bd_shuffleSum`: the Leibniz rule.
* `MMP.LatticePath.mem_support_shuffleSum`: the paths of `∇_{p,q}` have `n + 1`
  vertices, in `[p] × [q]`.

## References

* [S. Eilenberg, S. MacLane, *On the groups H(Π, n), I*][eilenbergmaclane1953], §5.
-/

@[expose] public noncomputable section

open Finsupp

namespace MMP

namespace LatticePath

/-- The coface `δ_k : ℕ → ℕ`, skipping the value `k`. -/
def skip (k v : ℕ) : ℕ := if v < k then v else v + 1

/-- The first step `x`: prepend `(0, 0)` and shift the first coordinates. -/
def stepFst (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := (0, 0) :: l.map fun v ↦ (v.1 + 1, v.2)

/-- The first step `y`: prepend `(0, 0)` and shift the second coordinates. -/
def stepSnd (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := (0, 0) :: l.map fun v ↦ (v.1, v.2 + 1)

/-- Relabel the first coordinates along `δ_k`. -/
def cofaceFst (k : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := l.map fun v ↦ (skip k v.1, v.2)

/-- Relabel the second coordinates along `δ_k`. -/
def cofaceSnd (k : ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := l.map fun v ↦ (v.1, skip k v.2)

/-- The linear map of formal sums of paths induced by a map of paths. -/
abbrev lmap (f : List (ℕ × ℕ) → List (ℕ × ℕ)) : (List (ℕ × ℕ) →₀ ℤ) →ₗ[ℤ] (List (ℕ × ℕ) →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ f

/-- The shuffle sum `∇_{p,q}` in length `n` (zero unless `n = p + q`). -/
def shuffleSum : ℕ → ℕ → ℕ → (List (ℕ × ℕ) →₀ ℤ)
  | 0, p, q => if p = 0 ∧ q = 0 then Finsupp.single [(0, 0)] 1 else 0
  | n + 1, p, q =>
    (match p with
      | 0 => 0
      | p' + 1 => lmap stepFst (shuffleSum n p' q)) +
    (-1 : ℤ) ^ p • (match q with
      | 0 => 0
      | q' + 1 => lmap stepSnd (shuffleSum n p q'))

/-- `∇_{p-1,q}`, zero if `p = 0`. -/
def lowerFst (n p q : ℕ) : List (ℕ × ℕ) →₀ ℤ :=
  match p with
  | 0 => 0
  | p' + 1 => shuffleSum n p' q

/-- `∇_{p,q-1}`, zero if `q = 0`. -/
def lowerSnd (n p q : ℕ) : List (ℕ × ℕ) →₀ ℤ :=
  match q with
  | 0 => 0
  | q' + 1 => shuffleSum n p q'

/-- `lowerFst n 0 q` is zero. -/
@[simp] lemma lowerFst_zero (n q : ℕ) : lowerFst n 0 q = 0 := rfl
/-- `lowerFst n (p + 1) q` is the shuffle sum `∇_{p,q}`. -/
@[simp] lemma lowerFst_succ (n p q : ℕ) : lowerFst n (p + 1) q = shuffleSum n p q := rfl
/-- `lowerSnd n p 0` is zero. -/
@[simp] lemma lowerSnd_zero (n p : ℕ) : lowerSnd n p 0 = 0 := rfl
/-- `lowerSnd n p (q + 1)` is the shuffle sum `∇_{p,q}`. -/
@[simp] lemma lowerSnd_succ (n p q : ℕ) : lowerSnd n p (q + 1) = shuffleSum n p q := rfl

/-- The shuffle sum of length `n + 1` is the sum of the `x`-steps of `∇_{p-1,q}` and `(-1)^p`
times the `y`-steps of `∇_{p,q-1}`. -/
lemma shuffleSum_succ (n p q : ℕ) :
    shuffleSum (n + 1) p q =
      lmap stepFst (lowerFst n p q) + (-1 : ℤ) ^ p • lmap stepSnd (lowerSnd n p q) := by
  rcases p with _ | p <;> rcases q with _ | q <;> simp [shuffleSum, lowerFst, lowerSnd]

/-- The boundary of formal sums of paths with `n + 1` vertices. -/
def bd (n : ℕ) (x : List (ℕ × ℕ) →₀ ℤ) : List (ℕ × ℕ) →₀ ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i • lmap (fun l ↦ l.eraseIdx i) x

/-- The boundary is additive. -/
lemma bd_add (n : ℕ) (x y : List (ℕ × ℕ) →₀ ℤ) : bd n (x + y) = bd n x + bd n y := by
  simp only [bd, map_add, smul_add, Finset.sum_add_distrib]

/-- The boundary commutes with integer scalar multiplication. -/
lemma bd_smul (n : ℕ) (c : ℤ) (x : List (ℕ × ℕ) →₀ ℤ) : bd n (c • x) = c • bd n x := by
  simp only [bd, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

/-- The boundary of zero is zero. -/
@[simp] lemma bd_zero (n : ℕ) : bd n 0 = 0 := by simp [bd]

/-- The linear map induced by a composite of path maps is the composite of the linear maps. -/
lemma lmap_lmap (f g : List (ℕ × ℕ) → List (ℕ × ℕ)) (x : List (ℕ × ℕ) →₀ ℤ) :
    lmap f (lmap g x) = lmap (f ∘ g) x := by
  rw [lmap, lmap, lmap, Finsupp.lmapDomain_comp]
  rfl

/-- The coface `δ_0` is the successor. -/
lemma skip_zero (v : ℕ) : skip 0 v = v + 1 := by simp [skip]

/-- `δ_{k+1}(v + 1) = δ_k(v) + 1`. -/
lemma skip_succ_succ (k v : ℕ) : skip (k + 1) (v + 1) = skip k v + 1 := by
  simp only [skip]; split_ifs <;> omega

/-- `δ_{k+1}(0) = 0`. -/
lemma skip_succ_zero (k : ℕ) : skip (k + 1) 0 = 0 := by simp [skip]

/-- The boundary of the paths obtained by prepending an `x`-step: the face deleting the first
vertex is `δ^x_0`, and the remaining faces are the `x`-steps of the boundary, with sign `-1`. -/
lemma bd_stepFst (n : ℕ) (x : List (ℕ × ℕ) →₀ ℤ) :
    bd (n + 1) (lmap stepFst x) = lmap (cofaceFst 0) x - lmap stepFst (bd n x) := by
  rw [bd, Finset.sum_range_succ', bd, map_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib,
    add_comm]
  congr 1
  · simp only [pow_zero, one_smul, lmap_lmap]
    congr 2
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lmap_lmap, map_smul, lmap_lmap, pow_succ, mul_neg_one, neg_smul]
    congr 4
    funext l
    simp [stepFst, List.eraseIdx_map]

/-- The boundary of the paths obtained by prepending a `y`-step: the face deleting the first
vertex is `δ^y_0`, and the remaining faces are the `y`-steps of the boundary, with sign `-1`. -/
lemma bd_stepSnd (n : ℕ) (x : List (ℕ × ℕ) →₀ ℤ) :
    bd (n + 1) (lmap stepSnd x) = lmap (cofaceSnd 0) x - lmap stepSnd (bd n x) := by
  rw [bd, Finset.sum_range_succ', bd, map_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib,
    add_comm]
  congr 1
  · simp only [pow_zero, one_smul, lmap_lmap]
    congr 2
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [lmap_lmap, map_smul, lmap_lmap, pow_succ, mul_neg_one, neg_smul]
    congr 4
    funext l
    simp [stepSnd, List.eraseIdx_map]

/-- `δ^x_{k+1}` after an `x`-step is the `x`-step after `δ^x_k`. -/
lemma cofaceFst_succ_stepFst (k : ℕ) :
    cofaceFst (k + 1) ∘ stepFst = stepFst ∘ cofaceFst k := by
  funext l
  simp [cofaceFst, stepFst, skip_succ_zero, skip_succ_succ]

/-- `δ^x_{k+1}` commutes with a `y`-step. -/
lemma cofaceFst_succ_stepSnd (k : ℕ) :
    cofaceFst (k + 1) ∘ stepSnd = stepSnd ∘ cofaceFst (k + 1) := by
  funext l
  simp [cofaceFst, stepSnd, skip_succ_zero]

/-- `δ^y_{k+1}` commutes with an `x`-step. -/
lemma cofaceSnd_succ_stepFst (k : ℕ) :
    cofaceSnd (k + 1) ∘ stepFst = stepFst ∘ cofaceSnd (k + 1) := by
  funext l
  simp [cofaceSnd, stepFst, skip_succ_zero]

/-- `δ^y_{k+1}` after a `y`-step is the `y`-step after `δ^y_k`. -/
lemma cofaceSnd_succ_stepSnd (k : ℕ) :
    cofaceSnd (k + 1) ∘ stepSnd = stepSnd ∘ cofaceSnd k := by
  funext l
  simp [cofaceSnd, stepSnd, skip_succ_zero, skip_succ_succ]

/-- An `x`-step after `δ^y_0` equals a `y`-step after `δ^x_0`. -/
lemma stepFst_cofaceSnd_zero : stepFst ∘ cofaceSnd 0 = stepSnd ∘ cofaceFst 0 := by
  funext l
  simp [cofaceSnd, cofaceFst, stepSnd, stepFst, skip_zero]

/-- If `f ∘ g = f' ∘ g'`, the induced linear maps satisfy the same relation. -/
lemma lmap_comm {f g f' g' : List (ℕ × ℕ) → List (ℕ × ℕ)} (h : f ∘ g = f' ∘ g')
    (x : List (ℕ × ℕ) →₀ ℤ) : lmap f (lmap g x) = lmap f' (lmap g' x) := by
  rw [lmap_lmap, lmap_lmap, h]

/-- On formal sums, `δ^x_{k+1}` after an `x`-step is the `x`-step after `δ^x_k`. -/
lemma lmap_cofaceFst_succ_stepFst (k : ℕ) (x : List (ℕ × ℕ) →₀ ℤ) :
    lmap (cofaceFst (k + 1)) (lmap stepFst x) = lmap stepFst (lmap (cofaceFst k) x) :=
  lmap_comm (cofaceFst_succ_stepFst k) x

/-- On formal sums, `δ^x_{k+1}` commutes with a `y`-step. -/
lemma lmap_cofaceFst_succ_stepSnd (k : ℕ) (x : List (ℕ × ℕ) →₀ ℤ) :
    lmap (cofaceFst (k + 1)) (lmap stepSnd x) = lmap stepSnd (lmap (cofaceFst (k + 1)) x) :=
  lmap_comm (cofaceFst_succ_stepSnd k) x

/-- On formal sums, `δ^y_{k+1}` commutes with an `x`-step. -/
lemma lmap_cofaceSnd_succ_stepFst (k : ℕ) (x : List (ℕ × ℕ) →₀ ℤ) :
    lmap (cofaceSnd (k + 1)) (lmap stepFst x) = lmap stepFst (lmap (cofaceSnd (k + 1)) x) :=
  lmap_comm (cofaceSnd_succ_stepFst k) x

/-- On formal sums, `δ^y_{k+1}` after a `y`-step is the `y`-step after `δ^y_k`. -/
lemma lmap_cofaceSnd_succ_stepSnd (k : ℕ) (x : List (ℕ × ℕ) →₀ ℤ) :
    lmap (cofaceSnd (k + 1)) (lmap stepSnd x) = lmap stepSnd (lmap (cofaceSnd k) x) :=
  lmap_comm (cofaceSnd_succ_stepSnd k) x

/-- On formal sums, an `x`-step after `δ^y_0` equals a `y`-step after `δ^x_0`. -/
lemma lmap_stepFst_cofaceSnd_zero (x : List (ℕ × ℕ) →₀ ℤ) :
    lmap stepFst (lmap (cofaceSnd 0) x) = lmap stepSnd (lmap (cofaceFst 0) x) :=
  lmap_comm stepFst_cofaceSnd_zero x

/-- `(-1)^m (-1)^m = 1` in `ℤ`. -/
lemma neg_one_pow_mul_self' (m : ℕ) : (-1 : ℤ) ^ m * (-1) ^ m = 1 := by
  rw [← mul_pow]; simp

/-- `(-1)^m ((-1)^m x) = x` in `ℤ`. -/
lemma neg_one_pow_mul_self_mul (m : ℕ) (x : ℤ) : (-1 : ℤ) ^ m * ((-1) ^ m * x) = x := by
  rw [← mul_assoc, neg_one_pow_mul_self', one_mul]

/-- The Leibniz rule for the shuffle sum:
`∂ ∇_{p,q} = ∑_k (-1)^k δ^x_k ∇_{p-1,q} + (-1)^p ∑_l (-1)^l δ^y_l ∇_{p,q-1}`. -/
theorem bd_shuffleSum (n p q : ℕ) :
    bd (n + 1) (shuffleSum (n + 1) p q) =
      ∑ k ∈ Finset.range (p + 1), (-1 : ℤ) ^ k • lmap (cofaceFst k) (lowerFst n p q) +
        (-1 : ℤ) ^ p • ∑ l ∈ Finset.range (q + 1),
          (-1 : ℤ) ^ l • lmap (cofaceSnd l) (lowerSnd n p q) := by
  induction n generalizing p q with
  | zero =>
    rcases p with _ | _ | p <;> rcases q with _ | _ | q <;>
      simp [shuffleSum, lowerFst, lowerSnd, bd, Finset.sum_range_succ, stepFst, stepSnd,
        cofaceFst, cofaceSnd, skip]
  | succ n ih =>
    rw [shuffleSum_succ, bd_add, bd_smul, bd_stepFst, bd_stepSnd]
    rcases p with _ | p <;> rcases q with _ | q
    · simp
    · simp only [lowerFst_zero, lowerSnd_succ, map_zero, bd_zero, sub_zero, zero_add]
      rw [ih 0 q, shuffleSum_succ n 0 q]
      simp only [lowerFst_succ, lowerSnd_succ, lowerFst_zero, lowerSnd_zero, map_zero,
        smul_zero, Finset.sum_const_zero, add_zero, zero_add, sub_zero,
        Finset.sum_range_succ', map_add, map_sub,
        map_smul, map_sum, map_neg, smul_add, smul_sub, Finset.sum_add_distrib,
        lmap_cofaceFst_succ_stepFst, lmap_cofaceFst_succ_stepSnd, lmap_cofaceSnd_succ_stepFst,
        lmap_cofaceSnd_succ_stepSnd, Finset.smul_sum, smul_smul, pow_succ, pow_zero, one_mul,
        mul_neg, mul_one, neg_mul, neg_neg, neg_smul, one_smul, Finset.sum_neg_distrib,
        lmap_stepFst_cofaceSnd_zero]
      try simp only [smul_neg, neg_neg, zero_add, smul_add, Finset.smul_sum, smul_smul, mul_comm,
        Finset.sum_neg_distrib, neg_one_pow_mul_self', neg_one_pow_mul_self_mul, one_smul]
      abel
    · simp only [lowerFst_succ, lowerSnd_zero, map_zero, bd_zero, sub_zero, smul_zero, add_zero]
      rw [ih p 0, shuffleSum_succ n p 0]
      simp only [lowerFst_succ, lowerSnd_succ, lowerFst_zero, lowerSnd_zero, map_zero,
        smul_zero, Finset.sum_const_zero, add_zero, zero_add, sub_zero,
        Finset.sum_range_succ', map_add, map_sub,
        map_smul, map_sum, map_neg, smul_add, smul_sub, Finset.sum_add_distrib,
        lmap_cofaceFst_succ_stepFst, lmap_cofaceFst_succ_stepSnd, lmap_cofaceSnd_succ_stepFst,
        lmap_cofaceSnd_succ_stepSnd, Finset.smul_sum, smul_smul, pow_succ, pow_zero, one_mul,
        mul_neg, mul_one, neg_mul, neg_neg, neg_smul, one_smul, Finset.sum_neg_distrib,
        lmap_stepFst_cofaceSnd_zero]
      try simp only [smul_neg, neg_neg, zero_add, smul_add, Finset.smul_sum, smul_smul, mul_comm,
        Finset.sum_neg_distrib, neg_one_pow_mul_self', neg_one_pow_mul_self_mul, one_smul]
      abel
    · simp only [lowerFst_succ, lowerSnd_succ]
      rw [ih p (q + 1), ih (p + 1) q, shuffleSum_succ n p (q + 1), shuffleSum_succ n (p + 1) q]
      simp only [lowerFst_succ, lowerSnd_succ, Finset.sum_range_succ', map_add, map_sub,
        map_smul, map_sum, map_neg, smul_add, smul_sub, Finset.sum_add_distrib,
        lmap_cofaceFst_succ_stepFst, lmap_cofaceFst_succ_stepSnd, lmap_cofaceSnd_succ_stepFst,
        lmap_cofaceSnd_succ_stepSnd, Finset.smul_sum, smul_smul, pow_succ, pow_zero, one_mul,
        mul_neg, mul_one, neg_mul, neg_neg, neg_smul, one_smul, Finset.sum_neg_distrib,
        lmap_stepFst_cofaceSnd_zero]
      try simp only [smul_neg, neg_neg, zero_add, smul_add, Finset.smul_sum, smul_smul, mul_comm,
        Finset.sum_neg_distrib, neg_one_pow_mul_self', neg_one_pow_mul_self_mul, one_smul]
      abel

/-- A path in the support of `∇_{p,q}` in length `n` has `n + 1` vertices, all in `[p] × [q]`. -/
lemma mem_support_shuffleSum {n p q : ℕ} {l : List (ℕ × ℕ)}
    (h : l ∈ (shuffleSum n p q).support) : l.length = n + 1 ∧ ∀ v ∈ l, v.1 ≤ p ∧ v.2 ≤ q := by
  classical
  induction n generalizing p q l with
  | zero =>
    simp only [shuffleSum] at h
    split_ifs at h with hpq
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
      subst h
      simp [hpq.1, hpq.2]
    · simp at h
  | succ n ih =>
    rw [shuffleSum_succ] at h
    rcases Finset.mem_union.1 (Finsupp.support_add h) with h | h
    · rcases p with _ | p
      · simp at h
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      obtain ⟨h1, h2⟩ := ih hl'
      refine ⟨by simp [stepFst, h1], ?_⟩
      simp only [stepFst, List.mem_cons, List.mem_map]
      rintro v (rfl | ⟨w, hw, rfl⟩)
      · simp
      · exact ⟨by simpa using (h2 w hw).1, (h2 w hw).2⟩
    · have h := Finsupp.support_smul h
      rcases q with _ | q
      · simp at h
      obtain ⟨l', hl', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support h)
      obtain ⟨h1, h2⟩ := ih hl'
      refine ⟨by simp [stepSnd, h1], ?_⟩
      simp only [stepSnd, List.mem_cons, List.mem_map]
      rintro v (rfl | ⟨w, hw, rfl⟩)
      · simp
      · exact ⟨(h2 w hw).1, by simpa using (h2 w hw).2⟩

end LatticePath

end MMP
