/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Combinatorics.WeightedGraph.Basic

/-!
# Shapes of weighted trees: stars, forks, branch values

Shapes of weighted trees with simple edges used in the classification of log terminal surface
singularities in Chapter 3 of Kollár et al., *Flips and abundance for algebraic threefolds* (FA):
stars with chains as arms, forked branches, two-fork graphs and the two shapes of FA Fig. 2,
together with the branch value `σ(Γ, v, Γ_i)` of a component of `Γ - v` and bonus and penalty
vertices.

A connected component `Γ_i` of `Γ - v` is recorded, as in `IsChainAttachedAtEnd`, by its vertex
set `C : Finset V`, and `Γ_i = Γ|_C`. A decomposition `Γ - v = Γ_1 ⊔ ⋯ ⊔ Γ_N` is recorded by
pairwise disjoint vertex sets whose union is `V \ {v}`. For a finset `S ⊆ C`, the determinant
`Δ(Γ_i|_S) = Δ(Γ|_S)` is `Γ.delta S`, since `Γ_i|_S` and `Γ|_S` carry the same data.

## Main definitions

* `MMP.Flips.WeightedGraph.HasSimpleEdges`: every edge of `Γ` is simple.
* `MMP.Flips.WeightedGraph.IsComponentOfRemoveVertex`: a component of `Γ - v`.
* `MMP.Flips.WeightedGraph.IsStar`: a star with arms `Γ_1, …, Γ_N` at `v` (FA 3.2.2–3.2.4).
* `MMP.Flips.WeightedGraph.IsForkedBranch`: a forked branch at `v` with fork `u` and arms
  `Γ_A, Γ_B` (FA Fig. 1, Fig. 2).
* `MMP.Flips.WeightedGraph.IsTwoForkGraph`: a two-fork graph with forks `v ≠ v'` (FA 3.2.5).
* `MMP.Flips.WeightedGraph.treePath`: the vertex set `path(u, w)` of the path in a tree
  (FA 3.1.9).
* `MMP.Flips.WeightedGraph.branchValue`: the branch value `σ(Γ, v, Γ_i)` (FA 3.2.1–3.2.7).
* `MMP.Flips.WeightedGraph.IsBonusVertex`, `IsPenaltyVertex`: `c_k(Γ) = 1`, `c_k(Γ) < 0`
  (FA 3.1.10).
* `MMP.Flips.WeightedGraph.IsFig2LeftShape`, `IsFig2RightShape`: the shapes of FA Fig. 2
  (FA 3.2.6).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.9),
  (3.1.10), (3.2.2)–(3.2.7), Fig. 1, Fig. 2
-/

@[expose] public noncomputable section

namespace MMP.Flips

namespace WeightedGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V)

/-! ### Simple edges and components of `Γ - v` -/

omit [DecidableEq V] in
/-- `Γ` is a weighted graph *with simple edges* (FA 3.1.1, 3.2): every edge of the underlying
graph is simple, i.e. `m_{jk} = 1` whenever `m_{jk} > 0`. -/
@[mmp "def_fa3_three_arm_star"]
def HasSimpleEdges : Prop :=
  ∀ j k, Γ.underlyingGraph.Adj j k → Γ.IsSimpleEdge j k

/-- The finset `C` is the vertex set of a *connected component* `Γ_i` of `Γ - v`: the image in
`V` of the support of a connected component of the underlying graph of `Γ - v`. -/
@[mmp "def_fa3_three_arm_star"]
def IsComponentOfRemoveVertex (v : V) (C : Finset V) : Prop :=
  ∃ c : (Γ.removeVertex v).underlyingGraph.ConnectedComponent,
    (C : Set V) = Subtype.val '' c.supp

/-! ### Stars -/

/-- `Γ` is a *star with arms `Γ_1, …, Γ_N` at the vertex `v`* (FA 3.2.2–3.2.4): `Γ` has simple
edges and its underlying graph is a tree, `deg v = N`, and the connected components of `Γ - v`
are exactly `Γ_1, …, Γ_N` (vertex sets `arms i`: each is a component, they are pairwise
disjoint, and they cover `V \ {v}`), each a chain attached to `v` at an end. We write
`Δ_i = Δ(Γ_i)`, which is `Γ.delta (arms i)`. -/
@[mmp "def_fa3_three_arm_star"]
structure IsStar (v : V) {N : ℕ} (arms : Fin N → Finset V) : Prop where
  hasSimpleEdges : Γ.HasSimpleEdges
  isTree : Γ.IsTree
  degree_eq : Γ.degree v = N
  /-- Each `arms i` is the vertex set of a connected component of `Γ - v`. -/
  isComponent : ∀ i, Γ.IsComponentOfRemoveVertex v (arms i)
  pairwise_disjoint : Pairwise fun i j => Disjoint (arms i) (arms j)
  biUnion_eq : univ.biUnion arms = univ \ {v}
  /-- Each arm `Γ_i` is a chain attached to `v` at an end. -/
  isChainAttachedAtEnd : ∀ i, Γ.IsChainAttachedAtEnd v (arms i)

/-! ### Forked branches -/

/-- For a vertex `v` of `Γ`, the component `Γ_i` of `Γ - v` with vertex set `C` is a *forked
branch at `v` with fork `u` and arms `Γ_A, Γ_B`* (FA Fig. 1, Fig. 2: an oval followed by a
fork): `Γ` has simple edges and its underlying graph is a tree, and `Γ_i` contains distinct
vertices `x_1, …, x_r = u` (`r ≥ 1`; here `x t = x_{t+1}` for `t : Fin r`) with `x_1` the unique
neighbour of `v` in `Γ_i`, `x_t` adjacent to `x_{t+1}`, each `x_t` (`t < r`) of degree `2` in
`Γ`, `u` of degree `3` in `Γ`, and `Γ_i - {x_1, …, x_r} = Γ_A ⊔ Γ_B` with `Γ_A`, `Γ_B` chains
attached to `u` at an end. We write `Δ_A = Δ(Γ_A)`, `Δ_B = Δ(Γ_B)`, which are `Γ.delta A` and
`Γ.delta B`. -/
@[mmp "def_fa3_fork_chain_branch"]
structure IsForkedBranch (v : V) (C : Finset V) (u : V) (A B : Finset V) : Prop where
  hasSimpleEdges : Γ.HasSimpleEdges
  isTree : Γ.IsTree
  isComponent : Γ.IsComponentOfRemoveVertex v C
  exists_spine : ∃ (r : ℕ) (hr : 0 < r) (x : Fin r → V),
    Function.Injective x ∧ x ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ = u ∧ (∀ t, x t ∈ C) ∧
    Γ.underlyingGraph.Adj v (x ⟨0, hr⟩) ∧
    (∀ w ∈ C, Γ.underlyingGraph.Adj v w → w = x ⟨0, hr⟩) ∧
    (∀ (t : ℕ) (ht : t + 1 < r), Γ.underlyingGraph.Adj (x ⟨t, by omega⟩) (x ⟨t + 1, ht⟩)) ∧
    (∀ (t : ℕ) (ht : t + 1 < r), Γ.degree (x ⟨t, by omega⟩) = 2) ∧
    Γ.degree u = 3 ∧
    C \ univ.image x = A ∪ B ∧ Disjoint A B ∧
    Γ.IsChainAttachedAtEnd u A ∧ Γ.IsChainAttachedAtEnd u B

/-- The component `Γ_i` of `Γ - v` with vertex set `C` is a *forked branch at `v`* (FA Fig. 2):
it is a forked branch at `v` with some fork `u` and some arms `Γ_A, Γ_B`. -/
@[mmp "def_fa3_fork_chain_branch"]
def IsForkedBranchAt (v : V) (C : Finset V) : Prop :=
  ∃ (u : V) (A B : Finset V), Γ.IsForkedBranch v C u A B

/-! ### Two-fork graphs -/

/-- `Γ` is a *two-fork graph with forks `v ≠ v'`*, with `Γ - v = Γ_1 ⊔ Γ_2 ⊔ Γ_3` (vertex sets
`C₁, C₂, C₃`) and arms `Γ_A, Γ_B` at `v'` (FA 3.2.5, Fig. 1): `Γ` has simple edges and its
underlying graph is a tree, `v ≠ v'`, `deg v = 3`, `C₁, C₂, C₃` are pairwise disjoint with union
`V \ {v}`, `Γ_1, Γ_2` are chains attached to `v` at an end and `Γ_3` is a forked branch at `v`
with fork `v'` and arms `Γ_A, Γ_B`. We write `Δ_i = Δ(Γ_i)`, which is `Γ.delta Cᵢ`. -/
@[mmp "def_fa3_two_fork_graph"]
structure IsTwoForkGraphWith (v v' : V) (C₁ C₂ C₃ A B : Finset V) : Prop where
  hasSimpleEdges : Γ.HasSimpleEdges
  isTree : Γ.IsTree
  ne : v ≠ v'
  degree_eq : Γ.degree v = 3
  disjoint₁₂ : Disjoint C₁ C₂
  disjoint₁₃ : Disjoint C₁ C₃
  disjoint₂₃ : Disjoint C₂ C₃
  union_eq : C₁ ∪ C₂ ∪ C₃ = univ \ {v}
  isChainAttachedAtEnd₁ : Γ.IsChainAttachedAtEnd v C₁
  isChainAttachedAtEnd₂ : Γ.IsChainAttachedAtEnd v C₂
  isForkedBranch₃ : Γ.IsForkedBranch v C₃ v' A B

/-- `Γ` is a *two-fork graph with forks `v ≠ v'`* (FA 3.2.5, Fig. 1): it is one for some
decomposition `Γ - v = Γ_1 ⊔ Γ_2 ⊔ Γ_3` and some arms `Γ_A, Γ_B` at `v'`. -/
@[mmp "def_fa3_two_fork_graph"]
def IsTwoForkGraph (v v' : V) : Prop :=
  ∃ C₁ C₂ C₃ A B : Finset V, Γ.IsTwoForkGraphWith v v' C₁ C₂ C₃ A B

/-! ### Paths in a tree and branch values -/

omit [DecidableEq V] in
/-- The vertex set `path(u, w) ⊆ V(Γ)` (FA 3.1.9): the vertices lying on a path from `u` to `w`
in the underlying graph. When the underlying graph has no cycles and `u, w` lie in the same
connected component, there is exactly one such path (`treePath_eq_support`), and this is its
vertex set; `path(u, u) = {u}` (`treePath_self`). -/
def treePath (u w : V) : Finset V :=
  open Classical in {x | ∃ p : Γ.Path u w, x ∈ p.1.support}

omit [DecidableEq V] in
/-- `x ∈ path(u, w)` iff `x` lies on some path from `u` to `w` in the underlying graph. -/
@[simp]
theorem mem_treePath_iff {u w x : V} :
    x ∈ Γ.treePath u w ↔ ∃ p : Γ.Path u w, x ∈ p.1.support := by
  simp [treePath]

omit [DecidableEq V] in
/-- `path(u, u) = {u}` (FA 3.1.9). -/
@[simp]
theorem treePath_self (u : V) : Γ.treePath u u = {u} := by
  ext x
  simp only [treePath, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨p, hp⟩
    rw [SimpleGraph.Path.loop_eq p] at hp
    simpa using hp
  · rintro rfl
    exact ⟨SimpleGraph.Path.nil, by simp⟩

/-- If the underlying graph of `Γ` has no cycles, `path(u, w)` is the vertex set of any (hence
the unique) path from `u` to `w` (FA 3.1.9). -/
theorem treePath_eq_support (hΓ : Γ.IsAcyclic) {u w : V} (p : Γ.Path u w) :
    Γ.treePath u w = p.1.support.toFinset := by
  ext x
  simp only [treePath, mem_filter, mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨q, hq⟩
    rwa [(hΓ.subsingleton_path u w).elim q p] at hq
  · exact fun hx => ⟨p, hx⟩

omit [DecidableEq V] in
/-- The neighbour `w_i` of `v` in the component `Γ_i` (vertex set `C`) of `Γ - v`
(FA 3.2.1–3.2.7): the unique `w ∈ C` adjacent to `v` if there is exactly one, and `v` itself
otherwise (a junk value, which does not occur for a component of `Γ - v` in a tree). -/
@[mmp "def_fa3_branch_value"]
def branchNeighbor (v : V) (C : Finset V) : V :=
  open Classical in
  if h : ∃! w, w ∈ C ∧ Γ.underlyingGraph.Adj v w then h.choose else v

/-- The *branch value* (FA 3.2.1–3.2.7, the "term" `T` of 3.2.7): for a vertex `v` of a tree
`Γ` with simple edges and a connected component `Γ_i` (vertex set `C`) of `Γ - v`, with `w_i`
the unique neighbour of `v` in `Γ_i`,
`σ(Γ, v, Γ_i) := ∑_{v_k ∈ Γ_i} Δ(Γ_i - path(w_i, v_k)) c_k(Γ)`.
Here `Δ(Γ_i - path(w_i, v_k)) = Γ.delta (C \ path(w_i, v_k))`. The function is defined for every
`C`; `branchValue_eq` computes it from the neighbour `w_i`. -/
@[mmp "def_fa3_branch_value"]
def branchValue (v : V) (C : Finset V) : ℚ :=
  ∑ k ∈ C, (Γ.delta (C \ Γ.treePath (Γ.branchNeighbor v C) k) : ℚ) * Γ.c k

/-- If `w` is the unique neighbour of `v` in `Γ_i` (vertex set `C`), then
`σ(Γ, v, Γ_i) = ∑_{v_k ∈ Γ_i} Δ(Γ_i - path(w, v_k)) c_k(Γ)` (FA 3.2.1–3.2.7). -/
@[mmp "def_fa3_branch_value"]
theorem branchValue_eq {v w : V} {C : Finset V} (hw : w ∈ C) (hvw : Γ.underlyingGraph.Adj v w)
    (huniq : ∀ w' ∈ C, Γ.underlyingGraph.Adj v w' → w' = w) :
    Γ.branchValue v C = ∑ k ∈ C, (Γ.delta (C \ Γ.treePath w k) : ℚ) * Γ.c k := by
  have h : ∃! w, w ∈ C ∧ Γ.underlyingGraph.Adj v w :=
    ⟨w, ⟨hw, hvw⟩, fun w' hw' => huniq w' hw'.1 hw'.2⟩
  have hn : Γ.branchNeighbor v C = w := by
    classical
    simp only [branchNeighbor, h, ↓reduceDIte]
    exact h.unique h.choose_spec.1 ⟨hw, hvw⟩
  rw [branchValue, hn]

/-! ### Bonus and penalty vertices -/

/-- The vertex `v_k` of `Γ` is a *bonus vertex* (FA 3.1.10): `c_k(Γ) = 1`. -/
@[mmp "def_fa3_bonus_vertex"]
def IsBonusVertex (k : V) : Prop := Γ.c k = 1

/-- The vertex `v_k` of `Γ` is a *penalty vertex* (FA 3.1.10): `c_k(Γ) < 0`. -/
@[mmp "def_fa3_penalty_vertex"]
def IsPenaltyVertex (k : V) : Prop := Γ.c k < 0

/-! ### The shapes of FA Fig. 2 -/

/-- `Γ` has *Fig. 2(a) shape at `v`* (FA 3.2.6, Fig. 2 (left)): `Γ` has simple edges and its
underlying graph is a tree, `deg v = 3`, and `Γ - v = Γ_1 ⊔ Γ_2 ⊔ Γ_3` (pairwise disjoint vertex
sets `C₁, C₂, C₃` with union `V \ {v}`) with `Γ_1` a chain attached to `v` at an end and
`Γ_2, Γ_3` forked branches at `v`. -/
@[mmp "def_fa3_fig2_left"]
def IsFig2LeftShape (v : V) : Prop :=
  Γ.HasSimpleEdges ∧ Γ.IsTree ∧ Γ.degree v = 3 ∧
  ∃ C₁ C₂ C₃ : Finset V, Disjoint C₁ C₂ ∧ Disjoint C₁ C₃ ∧ Disjoint C₂ C₃ ∧
    C₁ ∪ C₂ ∪ C₃ = univ \ {v} ∧
    Γ.IsChainAttachedAtEnd v C₁ ∧ Γ.IsForkedBranchAt v C₂ ∧ Γ.IsForkedBranchAt v C₃

/-- `Γ` has *Fig. 2(b) shape at `v`* (FA 3.2.6, Fig. 2 (right)): `Γ` has simple edges and its
underlying graph is a tree, `deg v = 4`, and `Γ - v = Γ_1 ⊔ ⋯ ⊔ Γ_4` (pairwise disjoint vertex
sets `C₁, …, C₄` with union `V \ {v}`) with `Γ_1, Γ_2, Γ_3` chains attached to `v` at an end
and `Γ_4` a forked branch at `v`. -/
@[mmp "def_fa3_fig2_right"]
def IsFig2RightShape (v : V) : Prop :=
  Γ.HasSimpleEdges ∧ Γ.IsTree ∧ Γ.degree v = 4 ∧
  ∃ C₁ C₂ C₃ C₄ : Finset V, Disjoint C₁ C₂ ∧ Disjoint C₁ C₃ ∧ Disjoint C₁ C₄ ∧
    Disjoint C₂ C₃ ∧ Disjoint C₂ C₄ ∧ Disjoint C₃ C₄ ∧
    C₁ ∪ C₂ ∪ C₃ ∪ C₄ = univ \ {v} ∧
    Γ.IsChainAttachedAtEnd v C₁ ∧ Γ.IsChainAttachedAtEnd v C₂ ∧
    Γ.IsChainAttachedAtEnd v C₃ ∧ Γ.IsForkedBranchAt v C₄

end WeightedGraph

end MMP.Flips
