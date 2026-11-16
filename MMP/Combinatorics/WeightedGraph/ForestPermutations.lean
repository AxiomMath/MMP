/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Combinatorics.WeightedGraph.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Permutations along the edges of a forest

Let `G` be a graph without cycles on a finite vertex set and `σ` a permutation of the vertices
moving every vertex it moves to a neighbour. Then `σ` is an involution: if `σ (σ v) ≠ v`, the
orbit `σ v, σ² v, …, σⁿ v = v` is a walk from `σ v` to `v` avoiding the edge `{v, σ v}`, which
is therefore not a bridge, while every edge of a forest is a bridge. Consequently every cycle of
`σ` has length `≤ 2`, and `σ` is the product of its cycle factors, which are pairwise disjoint
transpositions of adjacent vertices.

This is applied to the underlying graph of a weighted graph `Γ` without cycles, and to
permutations of a subset `S` of its vertices (FA 3.1.8–3.1.9, where it is left as an exercise).

## Main results

* `MMP.Flips.perm_apply_apply_eq_self_of_isAcyclic`: `σ (σ v) = v`, for any acyclic graph.
* `MMP.Flips.WeightedGraph.perm_mul_self_eq_one_of_isAcyclic`: `σ * σ = 1`.
* `MMP.Flips.WeightedGraph.le_two_of_mem_cycleType_of_isAcyclic`: every cycle of `σ` has
  length `≤ 2`.
* `MMP.Flips.WeightedGraph.exists_adj_eq_swap_of_mem_cycleFactorsFinset_of_isAcyclic`: every
  cycle factor of `σ` is the transposition of two adjacent vertices.
* `MMP.Flips.WeightedGraph.subtypePerm_apply_apply_eq_self_of_isAcyclic`: the same involution
  statement for a permutation of a subset `S ⊆ V(Γ)`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.8),
  (3.1.9)
-/

@[expose] public noncomputable section

namespace MMP.Flips

open Equiv

/-- On an acyclic graph with finitely many vertices, a permutation moving each vertex it moves
to a neighbour is an involution. -/
theorem perm_apply_apply_eq_self_of_isAcyclic {α : Type*} [Finite α] {G : SimpleGraph α}
    (hG : G.IsAcyclic) (σ : Perm α) (hσ : ∀ v, σ v ≠ v → G.Adj v (σ v)) (v : α) :
    σ (σ v) = v := by
  by_contra h
  have hv : σ v ≠ v := fun e => h (by rw [e, e])
  have hbridge := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG (hσ v hv)
  rw [SimpleGraph.isBridge_iff] at hbridge
  -- Every point `σ^k v`, `k ≥ 1`, of the orbit is reachable from `σ v` without `{v, σ v}`.
  have key : ∀ k : ℕ, (G.deleteEdges {s(v, σ v)}).Reachable (σ v) ((σ ^ (k + 1)) v) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      set w := (σ ^ (k + 1)) v with hw
      have hstep : (σ ^ (k + 1 + 1)) v = σ w := by
        rw [hw, pow_succ', Perm.mul_apply]
      rw [hstep]
      by_cases hwv : w = v
      · rw [hwv]
      refine ih.trans ?_
      have hσw : σ w ≠ w := by
        intro e
        apply hv
        have : (σ ^ (k + 1)) (σ v) = (σ ^ (k + 1)) v := by
          rw [← Perm.mul_apply, ← pow_succ, pow_succ', Perm.mul_apply]
          exact e
        exact (σ ^ (k + 1)).injective this
      refine SimpleGraph.Adj.reachable ?_
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hσ w hσw, ?_⟩
      rw [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨h1, h2⟩)
      · exact hwv h1
      · exact h (h1 ▸ h2)
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_of_finite σ |>.exists_pow_eq_one
  have := key (n - 1)
  rw [Nat.sub_add_cancel hn, hpow, Perm.one_apply] at this
  exact hbridge this.symm

namespace WeightedGraph

variable {V : Type*} [Fintype V] {Γ : WeightedGraph V}

/-- Let `Γ` be a weighted graph without cycles and `σ` a permutation of its vertices with `v`
and `σ v` adjacent whenever `σ v ≠ v`. Then `σ (σ v) = v` for every vertex `v`. -/
@[mmp "lem_fa3_forest_permutations"]
theorem perm_apply_apply_eq_self_of_isAcyclic (hΓ : Γ.IsAcyclic) (σ : Perm V)
    (hσ : ∀ v, σ v ≠ v → Γ.underlyingGraph.Adj v (σ v)) (v : V) : σ (σ v) = v :=
  MMP.Flips.perm_apply_apply_eq_self_of_isAcyclic hΓ σ hσ v

/-- Under the hypotheses of `perm_apply_apply_eq_self_of_isAcyclic`, `σ` is an involution. -/
@[mmp "lem_fa3_forest_permutations"]
theorem perm_mul_self_eq_one_of_isAcyclic (hΓ : Γ.IsAcyclic) (σ : Perm V)
    (hσ : ∀ v, σ v ≠ v → Γ.underlyingGraph.Adj v (σ v)) : σ * σ = 1 :=
  Perm.ext fun v => perm_apply_apply_eq_self_of_isAcyclic hΓ σ hσ v

/-- Under the hypotheses of `perm_apply_apply_eq_self_of_isAcyclic`, every cycle of `σ` has
length `≤ 2`. -/
@[mmp "lem_fa3_forest_permutations"]
theorem le_two_of_mem_cycleType_of_isAcyclic [DecidableEq V] (hΓ : Γ.IsAcyclic) (σ : Perm V)
    (hσ : ∀ v, σ v ≠ v → Γ.underlyingGraph.Adj v (σ v)) {n : ℕ} (hn : n ∈ σ.cycleType) :
    n ≤ 2 := by
  have h2 : σ ^ 2 = 1 := by rw [sq]; exact perm_mul_self_eq_one_of_isAcyclic hΓ σ hσ
  exact Nat.le_of_dvd two_pos ((Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h2))

/-- Under the hypotheses of `perm_apply_apply_eq_self_of_isAcyclic`, every cycle factor of `σ`
is the transposition of two adjacent vertices. Together with
`Equiv.Perm.cycleFactorsFinset_pairwise_disjoint` and `Equiv.Perm.cycleFactorsFinset_noncommProd`,
`σ` is a product of disjoint transpositions of adjacent vertices. -/
@[mmp "lem_fa3_forest_permutations"]
theorem exists_adj_eq_swap_of_mem_cycleFactorsFinset_of_isAcyclic [DecidableEq V]
    (hΓ : Γ.IsAcyclic) (σ : Perm V) (hσ : ∀ v, σ v ≠ v → Γ.underlyingGraph.Adj v (σ v))
    {c : Perm V} (hc : c ∈ σ.cycleFactorsFinset) :
    ∃ u w, Γ.underlyingGraph.Adj u w ∧ c = swap u w := by
  have hmem : c.support.card ∈ σ.cycleType := by
    rw [Perm.cycleType_def]
    exact Multiset.mem_map_of_mem _ hc
  have hcard : c.support.card = 2 :=
    le_antisymm (le_two_of_mem_cycleType_of_isAcyclic hΓ σ hσ hmem)
      (Perm.mem_cycleFactorsFinset_iff.mp hc).1.two_le_card_support
  obtain ⟨u, w, huw, rfl⟩ := Perm.card_support_eq_two.mp hcard
  refine ⟨u, w, ?_, rfl⟩
  have hu : u ∈ (swap u w).support := by simp [huw]
  have hσu : σ u = w := by
    rw [← (Perm.mem_cycleFactorsFinset_iff.mp hc).2 u hu, swap_apply_left]
  exact hσu ▸ hσ u (hσu ▸ huw.symm)

/-- Let `Γ` be a weighted graph without cycles and `σ` a permutation of a subset `S` of its
vertices with `v` and `σ v` adjacent whenever `σ v ≠ v`. Then `σ (σ v) = v` for every `v ∈ S`. -/
@[mmp "lem_fa3_forest_permutations"]
theorem subtypePerm_apply_apply_eq_self_of_isAcyclic (hΓ : Γ.IsAcyclic) {S : Set V}
    (σ : Perm S) (hσ : ∀ v, σ v ≠ v → Γ.underlyingGraph.Adj v (σ v)) (v : S) :
    σ (σ v) = v :=
  MMP.Flips.perm_apply_apply_eq_self_of_isAcyclic (G := Γ.underlyingGraph.induce S)
    (hΓ.induce S) σ (fun v hv => by simpa using hσ v hv) v

/-- Under the hypotheses of `subtypePerm_apply_apply_eq_self_of_isAcyclic`, every cycle of the
permutation `σ` of `S` has length `≤ 2`. -/
@[mmp "lem_fa3_forest_permutations"]
theorem le_two_of_mem_cycleType_subtypePerm_of_isAcyclic [DecidableEq V] (hΓ : Γ.IsAcyclic)
    {S : Set V} [Fintype S] (σ : Perm S) (hσ : ∀ v, σ v ≠ v → Γ.underlyingGraph.Adj v (σ v))
    {n : ℕ} (hn : n ∈ σ.cycleType) : n ≤ 2 := by
  have h2 : σ ^ 2 = 1 :=
    Perm.ext fun v => by
      rw [sq, Perm.mul_apply, subtypePerm_apply_apply_eq_self_of_isAcyclic hΓ σ hσ v]; rfl
  exact Nat.le_of_dvd two_pos ((Perm.dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one h2))

end WeightedGraph

end MMP.Flips
