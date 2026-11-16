module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel

/-!
# Barycentric subdivision of vertex chains

Let `P` be a type of points. A *vertex chain* of length `k` with coefficients in a commutative
ring `R` is a formal `R`-linear combination of `k`-tuples `v : Fin k → P`; a `k`-tuple stands for
the affine simplex with vertices `v 0, …, v (k - 1)`, of dimension `k - 1`, and the empty tuple
for the augmentation. The boundary `∂ [v] = ∑ i, (-1) ^ i [v ∘ Fin.succAbove i]` and the cone
`b · [v] = [b, v 0, …, v (k - 1)]` over a point `b` satisfy `∂ (b · c) = c - b · ∂ c`, and
`∂ ∘ ∂ = 0` follows from it.

Given a *barycentre* function `bary : (Fin k → P) → P` for every `k`, the barycentric subdivision
`S` and the subdivision homotopy `T` are defined recursively (Hatcher, §2.1, proof of Prop. 2.21):
`S [] = []`, `S [v] = b_v · S (∂ [v])`, and `T [] = 0`, `T [v] = b_v · ([v] - T (∂ [v]))`.
For every `bary`, `S` is a chain map and `∂ T + T ∂ = 1 - S` in positive length. A map of points
compatible with the barycentres commutes with all of these operators.

## Main definitions

* `MMP.VertexChain.bd`: the boundary.
* `MMP.VertexChain.cone`: the cone over a point.
* `MMP.VertexChain.subdiv`: the barycentric subdivision `S`.
* `MMP.VertexChain.subdivHomotopy`: the subdivision homotopy `T`.

## Main results

* `MMP.VertexChain.bd_bd`: `∂ ∘ ∂ = 0`.
* `MMP.VertexChain.bd_subdiv`: `∂ S = S ∂`.
* `MMP.VertexChain.bd_subdivHomotopy_add`: `∂ T + T ∂ = 1 - S`.
* `MMP.VertexChain.map_subdiv`, `map_subdivHomotopy`: naturality.

## References

* [A. Hatcher, *Algebraic Topology*][hatcher2002], §2.1, Prop. 2.21.
-/

@[expose] public noncomputable section

open Finsupp

namespace MMP

namespace VertexChain

variable (R : Type*) [CommRing R] (P : Type*)

/-- Vertex chains of length `k`: formal combinations of `k`-tuples of points. -/
abbrev Chain (k : ℕ) := (Fin k → P) →₀ R

variable {P}

/-- The boundary `∂ [v] = ∑ i, (-1) ^ i [v ∘ Fin.succAbove i]`. -/
def bd (k : ℕ) : Chain R P (k + 1) →ₗ[R] Chain R P k :=
  linearCombination R fun v ↦ ∑ i : Fin (k + 1), (-1 : R) ^ (i : ℕ) • single (v ∘ i.succAbove) 1

/-- The cone `b · [v] = [b, v 0, …]` over a point `b`. -/
def cone (b : P) (k : ℕ) : Chain R P k →ₗ[R] Chain R P (k + 1) :=
  lmapDomain R R fun v : Fin k → P ↦ (Fin.cons b v : Fin (k + 1) → P)

variable {R}

/-- The boundary of a single tuple: `∂ [v] = ∑ i, (-1) ^ i [v ∘ Fin.succAbove i]`. -/
lemma bd_single (k : ℕ) (v : Fin (k + 1) → P) :
    bd R k (single v 1) = ∑ i : Fin (k + 1), (-1 : R) ^ (i : ℕ) • single (v ∘ i.succAbove) 1 := by
  simp [bd]

/-- The cone over `b` of a single tuple: `b · [v] = [Fin.cons b v]`. -/
lemma cone_single (b : P) (k : ℕ) (v : Fin k → P) :
    cone R b k (single v 1) = single (Fin.cons b v) 1 := by
  simp [cone]

/-- A nonempty tuple is the cone over its first vertex of its tail: `[v] = v 0 · [Fin.tail v]`. -/
lemma single_eq_cone (k : ℕ) (v : Fin (k + 1) → P) :
    (single v 1 : Chain R P (k + 1)) = cone R (v 0) k (single (Fin.tail v) 1) := by
  rw [cone_single, Fin.cons_self_tail]

private lemma cons_comp_succAbove_succ {k : ℕ} (b : P) (v : Fin (k + 1) → P) (i : Fin (k + 1)) :
    (Fin.cons b v : Fin (k + 2) → P) ∘ i.succ.succAbove = Fin.cons b (v ∘ i.succAbove) := by
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp
  · simp [Fin.succ_succAbove_succ]

/-- `∂ (b · c) = c - b · ∂ c`. -/
lemma bd_cone (b : P) (k : ℕ) (c : Chain R P (k + 1)) :
    bd R (k + 1) (cone R b (k + 1) c) = c - cone R b k (bd R k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]; abel
  | single v a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      ← smul_sub]
    congr 1
    rw [cone_single, bd_single, Fin.sum_univ_succ, bd_single, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero, Fin.val_succ, pow_succ,
      map_smul, cone_single, cons_comp_succAbove_succ]
    have : (Fin.cons b v : Fin (k + 2) → P) ∘ Fin.succ = v := by funext j; simp
    rw [this, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [mul_neg_one, neg_smul]

/-- `∂ (b · c) = c` in length `0`. -/
lemma bd_cone_zero (b : P) (c : Chain R P 0) : bd R 0 (cone R b 0 c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, cone_single, bd_single]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul]
    congr 2

/-- `∂ ∘ ∂ = 0`. -/
lemma bd_bd (k : ℕ) (c : Chain R P (k + 2)) : bd R k (bd R (k + 1) c) = 0 := by
  induction k with
  | zero =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd, add_zero]
    | single v a =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, single_eq_cone,
        bd_cone, map_sub, bd_cone_zero, sub_self, smul_zero]
  | succ k ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd, add_zero]
    | single v a =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, single_eq_cone,
        bd_cone, map_sub, bd_cone, ih, map_zero, sub_zero, sub_self, smul_zero]

/-- A choice of barycentre for every nonempty finite tuple of points: `bary k v` is the
barycentre of the `k + 1` points `v`. -/
abbrev Bary (P : Type*) := ∀ k : ℕ, (Fin (k + 1) → P) → P

variable (bary : Bary P)

variable (R) in
/-- The barycentric subdivision `S [v] = b_v · S (∂ [v])`, `S [] = []`. -/
def subdiv : ∀ k : ℕ, Chain R P k →ₗ[R] Chain R P k
  | 0 => LinearMap.id
  | k + 1 => linearCombination R fun v ↦ cone R (bary k v) k (subdiv k (bd R k (single v 1)))

variable (R) in
/-- The subdivision homotopy `T [v] = b_v · ([v] - T (∂ [v]))`, `T [] = 0`. -/
def subdivHomotopy : ∀ k : ℕ, Chain R P k →ₗ[R] Chain R P (k + 1)
  | 0 => 0
  | k + 1 => linearCombination R fun v ↦
      cone R (bary k v) (k + 1) (single v 1 - subdivHomotopy k (bd R k (single v 1)))

/-- In length `0` the subdivision is the identity. -/
lemma subdiv_zero (c : Chain R P 0) : subdiv R bary 0 c = c := rfl

/-- The subdivision of a single tuple: `S [v] = b_v · S (∂ [v])`. -/
lemma subdiv_single (k : ℕ) (v : Fin (k + 1) → P) :
    subdiv R bary (k + 1) (single v 1) =
      cone R (bary k v) k (subdiv R bary k (bd R k (single v 1))) := by
  simp [subdiv]

/-- In length `0` the subdivision homotopy is zero. -/
lemma subdivHomotopy_zero (c : Chain R P 0) : subdivHomotopy R bary 0 c = 0 := rfl

/-- The subdivision homotopy of a single tuple: `T [v] = b_v · ([v] - T (∂ [v]))`. -/
lemma subdivHomotopy_single (k : ℕ) (v : Fin (k + 1) → P) :
    subdivHomotopy R bary (k + 1) (single v 1) =
      cone R (bary k v) (k + 1)
        (single v 1 - subdivHomotopy R bary k (bd R k (single v 1))) := by
  simp [subdivHomotopy]

/-- The subdivision is a chain map: `∂ S = S ∂`. -/
lemma bd_subdiv (k : ℕ) (c : Chain R P (k + 1)) :
    bd R k (subdiv R bary (k + 1) c) = subdiv R bary k (bd R k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      subdiv_single]
    congr 1
    cases k with
    | zero => rw [bd_cone_zero]
    | succ k =>
      rw [bd_cone, bd_subdiv k, bd_bd, map_zero, map_zero, sub_zero]

/-- The subdivision homotopy: `∂ T c + T ∂ c = c - S c`. -/
lemma bd_subdivHomotopy_add (k : ℕ) (c : Chain R P (k + 1)) :
    bd R (k + 1) (subdivHomotopy R bary (k + 1) c) + subdivHomotopy R bary k (bd R k c) =
      c - subdiv R bary (k + 1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add]; rw [add_add_add_comm, hc, hd]; abel
  | single v a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single]
    simp only [map_smul, ← smul_add, ← smul_sub]
    congr 1
    rw [subdivHomotopy_single, subdiv_single, bd_cone, map_sub]
    cases k with
    | zero =>
      simp only [subdivHomotopy_zero, map_zero, sub_zero, add_zero, subdiv_zero]
    | succ k =>
      have ih := bd_subdivHomotopy_add k (bd R (k + 1) (single v 1))
      rw [bd_bd, map_zero, add_zero] at ih
      rw [ih, sub_sub_cancel]
      abel

section map

variable {Q : Type*} (f : P → Q)

variable (R) in
/-- Push-forward of vertex chains along a map of points. -/
abbrev map (k : ℕ) : Chain R P k →ₗ[R] Chain R Q k := lmapDomain R R fun v ↦ f ∘ v

/-- The push-forward of a single tuple `[v]` along `f` is `[f ∘ v]`. -/
lemma map_single (k : ℕ) (v : Fin k → P) : map R f k (single v 1) = single (f ∘ v) 1 := by
  simp

/-- Push-forward along a map of points commutes with the boundary. -/
lemma map_bd (k : ℕ) (c : Chain R P (k + 1)) :
    map R f k (bd R k c) = bd R k (map R f (k + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      map_single, bd_single, bd_single, map_sum]
    simp only [map_smul, map_single]
    rfl

/-- Push-forward along `f` sends the cone over `b` to the cone over `f b`. -/
lemma map_cone (b : P) (k : ℕ) (c : Chain R P k) :
    map R f (k + 1) (cone R b k c) = cone R (f b) k (map R f k c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
      map_single, cone_single, cone_single, map_single]
    congr 2
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp

variable {bary} {bary' : Bary Q} (hf : ∀ k v, f (bary k v) = bary' k (f ∘ v))

include hf

/-- Push-forward along a map compatible with the barycentres commutes with subdivision. -/
lemma map_subdiv (k : ℕ) (c : Chain R P k) :
    map R f k (subdiv R bary k c) = subdiv R bary' k (map R f k c) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
        subdiv_single, map_single, subdiv_single, map_cone, ih, map_bd, map_single, hf]

/-- Push-forward along a map compatible with the barycentres commutes with the subdivision
homotopy. -/
lemma map_subdivHomotopy (k : ℕ) (c : Chain R P k) :
    map R f (k + 1) (subdivHomotopy R bary k c) = subdivHomotopy R bary' k (map R f k c) := by
  induction k with
  | zero => simp [subdivHomotopy_zero]
  | succ k ih =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_single, map_smul, map_smul, map_smul, map_smul,
        subdivHomotopy_single, map_single, subdivHomotopy_single, map_cone, map_sub, ih, map_bd,
        map_single, hf]

end map

end VertexChain

end MMP
