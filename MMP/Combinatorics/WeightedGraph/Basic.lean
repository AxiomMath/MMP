/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Weighted dual graphs

The combinatorics of weighted graphs underlying Chapter 3 of Kollár et al., *Flips and abundance
for algebraic threefolds* (FA): the abstract graphs of which the dual graphs of the exceptional
curves of a resolution of a surface singularity are examples.

A weighted graph `Γ` has a finite vertex type `V`; each vertex `v` carries a weight `n_v ∈ ℤ`
(`Γ.weight`), a genus `p_v ∈ ℤ_{≥ 0}` (`Γ.genus`, valued in `ℕ`) and a boundary degree
`β_v ∈ ℚ_{≥ 0}` (`Γ.boundary`), and each pair of distinct vertices an edge weight
`m_{vw} = m_{wv} ∈ ℤ_{≥ 0}` (`Γ.edgeWeight`). The source assigns no edge weight to a pair
`(v, v)`; here the diagonal value is fixed to be `0` (`Γ.edgeWeight_self`), so that a weighted
graph is exactly the data of the source.

Orders on the vertices (`v_1, …, v_s` from left to right for a chain, `v_1, …, v_l` around a
circle) are given by equivalences `Fin s ≃ V`. An induced subgraph `Γ|_S` has the subtype `↥S`
of a finset `S` as its vertex type.

## Main definitions

* `MMP.Flips.WeightedGraph`: weighted graphs; `MMP.Flips.WeightedGraph.matrix`, the matrix
  `M(Γ)`; `MMP.Flips.WeightedGraph.underlyingGraph`, the underlying graph, with neighbours,
  degree, connectedness, cycles, trees and paths; simple edges; negative definiteness.
* `MMP.Flips.WeightedGraph.restrict`, `removeSet`, `removeVertex`: `Γ|_S`, `Γ - S`, `Γ - v`.
* `MMP.Flips.WeightedGraph.IsSubgraph`: `Γ' ⊆ Γ`.
* `MMP.Flips.WeightedGraph.IsChainOrder`, `IsWeightedChain`, `IsChainAttachedAtEnd`: weighted
  chains and chains attached to a vertex at an end.
* `MMP.Flips.WeightedGraph.IsCircleOrder`, `IsCircle`: circles of length `l ≥ 2`.
* `MMP.Flips.WeightedGraph.det`, `delta`: the determinant `Δ(S) = det(-M(Γ|_S))`.
* `MMP.Flips.WeightedGraph.c`, `d`: the numbers `c_j(Γ)` and `d_j(Γ)`.
* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector`: log discrepancy vectors.
* `MMP.Flips.WeightedGraph.IsRational`, `IsRationalTree`: rational graphs and rational trees.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.0.2),
  (3.1.1), (3.1.3), (3.1.5), (3.1.6.2), (3.1.7), (3.1.10), (3.1.11), (3.4.1)
-/

@[expose] public noncomputable section

namespace MMP.Flips

open Finset

/-- A *weighted graph* `Γ` (FA 3.1.1, 3.1.3, implicit): a finite set `V` of vertices (`n ≥ 0`
of them; here the finite type `V`) and, for each vertex `v_j`, a *weight* `n_j ∈ ℤ`, a *genus*
`p_j ∈ ℤ_{≥ 0}` and a *boundary degree* `β_j ∈ ℚ_{≥ 0}`, and for each `j ≠ k` an *edge weight*
`m_{jk} = m_{kj} ∈ ℤ_{≥ 0}`. The source gives no edge weight for `j = k`; the field
`edgeWeight_self` fixes that value to be `0`. -/
@[mmp "def_fa3_weighted_graph"]
structure WeightedGraph (V : Type*) [Fintype V] where
  /-- The weight `n_j ∈ ℤ` of the vertex `v_j`. -/
  weight : V → ℤ
  /-- The genus `p_j ∈ ℤ_{≥ 0}` of the vertex `v_j`. -/
  genus : V → ℕ
  /-- The boundary degree `β_j ∈ ℚ_{≥ 0}` of the vertex `v_j`. -/
  boundary : V → ℚ
  /-- `β_j ≥ 0`. -/
  boundary_nonneg : ∀ v, 0 ≤ boundary v
  /-- The edge weight `m_{jk} ∈ ℤ_{≥ 0}` between `v_j` and `v_k`. -/
  edgeWeight : V → V → ℕ
  /-- `m_{jk} = m_{kj}`. -/
  edgeWeight_symm : ∀ v w, edgeWeight v w = edgeWeight w v
  /-- The (unused) diagonal edge weight is `0`. -/
  edgeWeight_self : ∀ v, edgeWeight v v = 0

namespace WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V)

/-! ### The matrix and the underlying graph -/

/-- The matrix `M(Γ)` of a weighted graph (FA 3.1.1): the `n × n` matrix with `M_{jj} = -n_j`
and `M_{jk} = m_{jk}` for `j ≠ k`. -/
@[mmp "def_fa3_weighted_graph"]
def matrix : Matrix V V ℤ :=
  Matrix.of fun j k => if j = k then -Γ.weight j else (Γ.edgeWeight j k : ℤ)

/-- The matrix `M(Γ)` is symmetric. -/
@[mmp "def_fa3_weighted_graph"]
theorem matrix_isSymm : Γ.matrix.IsSymm := by
  ext j k
  simp only [matrix, Matrix.transpose_apply, Matrix.of_apply]
  by_cases h : j = k
  · subst h; rfl
  · simp [h, Ne.symm h, Γ.edgeWeight_symm]

omit [DecidableEq V] in
/-- The *underlying graph* of `Γ` (FA 3.1.1): it has an edge between `v_j` and `v_k` iff
`m_{jk} > 0` (for `j ≠ k`). -/
@[mmp "def_fa3_weighted_graph"]
def underlyingGraph : SimpleGraph V where
  Adj j k := j ≠ k ∧ 0 < Γ.edgeWeight j k
  symm := ⟨fun j k h => ⟨Ne.symm h.1, Γ.edgeWeight_symm j k ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Adjacency in the underlying graph of `Γ` is decidable. -/
instance : DecidableRel Γ.underlyingGraph.Adj := fun j k =>
  inferInstanceAs (Decidable (j ≠ k ∧ 0 < Γ.edgeWeight j k))

/-- The *neighbours* of `v_j` (FA 3.1.1): the vertices `v_k`, `k ≠ j`, with `m_{jk} > 0`. -/
@[mmp "def_fa3_weighted_graph"]
def neighbors (j : V) : Finset V := {k | k ≠ j ∧ 0 < Γ.edgeWeight j k}

/-- The *degree* `deg(v_j) = #{k ≠ j : m_{jk} > 0}` (FA 3.1.1). -/
@[mmp "def_fa3_weighted_graph"]
def degree (j : V) : ℕ := #{k | k ≠ j ∧ 0 < Γ.edgeWeight j k}

/-- `v_k` is a neighbour of `v_j` iff `v_j` and `v_k` are adjacent in the underlying graph. -/
theorem mem_neighbors {j k : V} : k ∈ Γ.neighbors j ↔ Γ.underlyingGraph.Adj j k := by
  simp [neighbors, underlyingGraph, ne_comm]

/-- Neighbours refer to the underlying graph. -/
@[mmp "def_fa3_weighted_graph"]
theorem neighbors_eq_neighborFinset (j : V) :
    Γ.neighbors j = Γ.underlyingGraph.neighborFinset j := by
  ext k
  rw [mem_neighbors, SimpleGraph.mem_neighborFinset]

/-- The degree refers to the underlying graph. -/
@[mmp "def_fa3_weighted_graph"]
theorem degree_eq_underlyingGraph_degree (j : V) :
    Γ.degree j = Γ.underlyingGraph.degree j := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← neighbors_eq_neighborFinset]
  rfl

omit [DecidableEq V] in
/-- `Γ` is *connected* (FA 3.1.1): its underlying graph is connected. -/
@[mmp "def_fa3_weighted_graph"]
def IsConnected : Prop := Γ.underlyingGraph.Connected

omit [DecidableEq V] in
/-- A *cycle* of `Γ` (FA 3.1.1): a cycle of its underlying graph. -/
@[mmp "def_fa3_weighted_graph"]
def IsCycle {u : V} (p : Γ.underlyingGraph.Walk u u) : Prop := p.IsCycle

omit [DecidableEq V] in
/-- `Γ` has no cycles (FA 3.1.1): its underlying graph is acyclic. -/
@[mmp "def_fa3_weighted_graph"]
def IsAcyclic : Prop := Γ.underlyingGraph.IsAcyclic

omit [DecidableEq V] in
/-- `Γ` is a *tree* (FA 3.1.1): its underlying graph is a tree (connected, without cycles; in
particular nonempty). -/
@[mmp "def_fa3_weighted_graph"]
def IsTree : Prop := Γ.underlyingGraph.IsTree

omit [DecidableEq V] in
/-- A *path* of `Γ` from `u` to `v` (FA 3.1.1): a path in its underlying graph. -/
@[mmp "def_fa3_weighted_graph"]
abbrev Path (u v : V) : Type _ := Γ.underlyingGraph.Path u v

omit [DecidableEq V] in
/-- The edge between `v_j` and `v_k` is *simple* (FA 3.1.1): `j ≠ k` and `m_{jk} = 1`. -/
@[mmp "def_fa3_weighted_graph"]
def IsSimpleEdge (j k : V) : Prop := j ≠ k ∧ Γ.edgeWeight j k = 1

/-- `Γ` is *negative definite* (FA 3.1.1): `M(Γ)` is negative definite, i.e. `-M(Γ)` is
positive definite. The integer matrix is regarded over `ℚ`, the field of the boundary degrees
and log discrepancies; for a symmetric matrix with rational entries this is the same as
negative definiteness over `ℝ` (the minors criterion). -/
@[mmp "def_fa3_weighted_graph"]
def IsNegDef : Prop := (-(Γ.matrix.map ((↑) : ℤ → ℚ))).PosDef

/-- The empty graph is negative definite (FA 3.1.1). -/
@[mmp "def_fa3_weighted_graph"]
theorem isNegDef_of_isEmpty [IsEmpty V] : Γ.IsNegDef := by
  refine ⟨?_, fun x hx => (hx (Subsingleton.elim x 0)).elim⟩
  ext j
  exact isEmptyElim j

/-! ### Induced subgraphs and subgraphs -/

omit [DecidableEq V] in
/-- The *induced subgraph* `Γ|_S` (FA 3.1.3, 3.1.7, implicit): the weighted graph with vertex
set `S` and all data `n_j, p_j, β_j, m_{jk}` restricted to `S`. -/
@[mmp "def_fa3_induced_subgraph"]
def restrict (S : Finset V) : WeightedGraph S where
  weight v := Γ.weight v
  genus v := Γ.genus v
  boundary v := Γ.boundary v
  boundary_nonneg v := Γ.boundary_nonneg v
  edgeWeight v w := Γ.edgeWeight v w
  edgeWeight_symm v w := Γ.edgeWeight_symm v w
  edgeWeight_self v := Γ.edgeWeight_self v

/-- `Γ - S := Γ|_{V \ S}` (FA 3.1.7). -/
@[mmp "def_fa3_induced_subgraph"]
abbrev removeSet (S : Finset V) : WeightedGraph ↥(univ \ S) := Γ.restrict (univ \ S)

/-- `Γ - v := Γ - {v}` (FA 3.1.7). -/
@[mmp "def_fa3_induced_subgraph"]
abbrev removeVertex (v : V) : WeightedGraph ↥(univ \ {v}) := Γ.removeSet {v}

omit [DecidableEq V] in
/-- `Γ'` is a *subgraph* of `Γ`, `Γ' ⊆ Γ` (FA 3.1.3): the vertex set of `Γ'` is a subset `S`
of `V(Γ)`, and `n'_j = n_j`, `p'_j ≤ p_j`, `β'_j ≤ β_j` for every vertex `v_j` of `Γ'` and
`m'_{jk} ≤ m_{jk}` for all `v_j ≠ v_k` in `V(Γ')`. -/
@[mmp "def_fa3_subgraph"]
structure IsSubgraph {S : Finset V} (Γ' : WeightedGraph S) (Γ : WeightedGraph V) : Prop where
  weight_eq : ∀ j : S, Γ'.weight j = Γ.weight j
  edgeWeight_le : ∀ j k : S, j ≠ k → Γ'.edgeWeight j k ≤ Γ.edgeWeight j k
  genus_le : ∀ j : S, Γ'.genus j ≤ Γ.genus j
  boundary_le : ∀ j : S, Γ'.boundary j ≤ Γ.boundary j

omit [DecidableEq V] in
/-- Every induced subgraph `Γ|_S` is a subgraph of `Γ` (FA 3.1.3). -/
@[mmp "def_fa3_subgraph"]
theorem restrict_isSubgraph (S : Finset V) : (Γ.restrict S).IsSubgraph Γ :=
  ⟨fun _ => rfl, fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ => le_rfl⟩

/-! ### Chains and circles -/

omit [DecidableEq V] in
/-- The enumeration `e : Fin s ≃ V` (`e i = v_{i+1}`) exhibits `Γ` as a *weighted chain*
(FA 3.1.11): all `p_j = 0`, `m_{i,i+1} = 1` for `1 ≤ i < s`, and all other `m_{jk} = 0`. There
is no condition on the `β_j`. -/
@[mmp "def_fa3_chain_graph"]
structure IsChainOrder {s : ℕ} (e : Fin s ≃ V) : Prop where
  genus_eq_zero : ∀ i, Γ.genus (e i) = 0
  edgeWeight_eq : ∀ i j : Fin s,
    Γ.edgeWeight (e i) (e j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0

omit [DecidableEq V] in
/-- `Γ` is a *weighted chain* (FA 3.1.11): `V(Γ) = {v_1, …, v_s}` (`s ≥ 0`) for an enumeration
exhibiting it as a chain. -/
@[mmp "def_fa3_chain_graph"]
def IsWeightedChain : Prop := ∃ (s : ℕ) (e : Fin s ≃ V), Γ.IsChainOrder e

omit [DecidableEq V] in
/-- The *weights from left to right* `n_1, …, n_s` of a chain enumerated by `e`
(FA 3.1.11). -/
@[mmp "def_fa3_chain_graph"]
def chainWeights {s : ℕ} (e : Fin s ≃ V) : Fin s → ℤ := fun i => Γ.weight (e i)

omit [DecidableEq V] in
/-- The *ends* `v_1, v_s` of a chain enumerated by `e : Fin s ≃ V` (FA 3.1.11); empty when
`s = 0`. -/
@[mmp "def_fa3_chain_graph"]
def chainEnds {s : ℕ} (e : Fin s ≃ V) : Finset V :=
  if h : 0 < s then {e ⟨0, h⟩, e ⟨s - 1, Nat.sub_lt h Nat.one_pos⟩} else ∅

/-- For a vertex `v` of the tree `Γ`, the finset `C` (the vertex set of a component `Γ_i` of
`Γ - v`) is a *chain attached to `v` at an end* (FA 3.1.11): `Γ` is a tree, `C` is the vertex
set of a connected component of the underlying graph of `Γ - v`, and `Γ_i = Γ|_C` is a weighted
chain, enumerated by some `e`, whose end `v_1 = e 0` is the unique vertex of `Γ_i` adjacent
to `v`. -/
@[mmp "def_fa3_chain_graph"]
def IsChainAttachedAtEnd (v : V) (C : Finset V) : Prop :=
  Γ.IsTree ∧
  (∃ c : (Γ.removeVertex v).underlyingGraph.ConnectedComponent,
    (C : Set V) = Subtype.val '' c.supp) ∧
  ∃ (s : ℕ) (hs : 0 < s) (e : Fin s ≃ C), (Γ.restrict C).IsChainOrder e ∧
    Γ.underlyingGraph.Adj v (e ⟨0, hs⟩) ∧
    ∀ w ∈ C, Γ.underlyingGraph.Adj v w → w = e ⟨0, hs⟩

omit [DecidableEq V] in
/-- The enumeration `e : Fin l ≃ V` exhibits `Γ` as a *circle* (FA 3.1.5, Fig. 3 Case (5)):
`l ≥ 2`, all `p_j = 0` and `β_j = 0`, and for `l ≥ 3`, `m_{j,j+1} = 1` (indices modulo `l`) and
all other `m_{jk} = 0`; for `l = 2`, `m_{12} = 2`. -/
@[mmp "def_fa3_circle_graph"]
structure IsCircleOrder {l : ℕ} (e : Fin l ≃ V) : Prop where
  two_le : 2 ≤ l
  genus_eq_zero : ∀ i, Γ.genus (e i) = 0
  boundary_eq_zero : ∀ i, Γ.boundary (e i) = 0
  edgeWeight_eq_of_three_le : 3 ≤ l → ∀ i j : Fin l, i ≠ j →
    Γ.edgeWeight (e i) (e j) =
      if ((i : ℕ) + 1) % l = j ∨ ((j : ℕ) + 1) % l = i then 1 else 0
  edgeWeight_eq_of_eq_two : ∀ h : l = 2,
    Γ.edgeWeight (e ⟨0, by omega⟩) (e ⟨1, by omega⟩) = 2

omit [DecidableEq V] in
/-- `Γ` is a *circle of length `l ≥ 2`* (FA 3.1.5): `V = {v_1, …, v_l}` for an enumeration
exhibiting it as a circle. -/
@[mmp "def_fa3_circle_graph"]
def IsCircle (l : ℕ) : Prop := ∃ e : Fin l ≃ V, Γ.IsCircleOrder e

/-! ### Determinants -/

/-- The determinant `Δ(Γ) = det(-M(Γ))` of a weighted graph (FA 3.1.7). -/
@[mmp "def_fa3_graph_determinant"]
def det : ℤ := (-Γ.matrix).det

/-- `Δ(S) := det(-M(Γ|_S))` for `S ⊆ V(Γ)` (FA 3.1.7). -/
@[mmp "def_fa3_graph_determinant"]
def delta (S : Finset V) : ℤ := (Γ.restrict S).det

/-- `Δ(∅) = 1` (FA 3.1.7). -/
@[mmp "def_fa3_graph_determinant"]
theorem delta_empty : Γ.delta ∅ = 1 :=
  Matrix.det_isEmpty

/-- For an induced subgraph `Γ' = Γ|_S`, `Δ(Γ') = Δ(S)` (FA 3.1.7). -/
@[mmp "def_fa3_graph_determinant"]
theorem det_restrict (S : Finset V) : (Γ.restrict S).det = Γ.delta S := rfl

/-- `Δ(Γ - S) = Δ(V \ S)` (FA 3.1.7). -/
@[mmp "def_fa3_graph_determinant"]
theorem det_removeSet (S : Finset V) : (Γ.removeSet S).det = Γ.delta (univ \ S) := rfl

/-! ### The numbers `c_j`, `d_j` and log discrepancy vectors -/

/-- `c_j(Γ) := 2 - 2p_j - β_j - ∑_{k ≠ j} m_{jk}` (FA 3.0.2, 3.1.10, graph version). -/
@[mmp "def_fa3_graph_cj"]
def c (j : V) : ℚ :=
  2 - 2 * Γ.genus j - Γ.boundary j - ∑ k ∈ univ.erase j, (Γ.edgeWeight j k : ℚ)

omit [DecidableEq V] in
/-- `d_j(Γ) := 2 - 2p_j - n_j - β_j` (FA 3.0.2, graph version). -/
@[mmp "def_fa3_graph_dj"]
def d (j : V) : ℚ := 2 - 2 * Γ.genus j - Γ.weight j - Γ.boundary j

/-- `a ∈ ℚ^{V(Γ)}` is a *log discrepancy vector* of `Γ` (FA 3.0.2 `(*)`, FA 3.1.3–3.1.5):
`∑_k a_k M(Γ)_{kj} = -c_j(Γ)` for every `j`. -/
@[mmp "def_fa3_graph_log_discrepancy_vector"]
def IsLogDiscrepancyVector (a : V → ℚ) : Prop :=
  ∀ j, ∑ k, a k * (Γ.matrix k j : ℚ) = -Γ.c j

/-! ### Rational graphs and rational trees -/

/-- `Γ` is *rational* (FA 3.4.1, implicit; Artin 1966): for every nonzero `z ∈ ℤ_{≥ 0}^{V(Γ)}`,
`1 + ½ (zᵀ M(Γ) z + ∑_j z_j (2p_j - 2 + n_j)) ≤ 0`. -/
@[mmp "def_fa3_graph_rational"]
def IsRational : Prop :=
  ∀ z : V → ℕ, z ≠ 0 →
    1 + (1 / 2 : ℚ) * ((∑ j, ∑ k, (z j : ℚ) * Γ.matrix j k * z k) +
      ∑ j, (z j : ℚ) * (2 * Γ.genus j - 2 + Γ.weight j)) ≤ 0

omit [DecidableEq V] in
/-- `Γ` is a *rational tree* (FA 3.1.6.2): `p_j = 0` and `n_j ≥ 2` for every vertex, every edge
is simple (`m_{jk} ∈ {0, 1}`), and the underlying graph is a tree (connected without cycles) or
empty. -/
@[mmp "def_fa3_rational_tree"]
structure IsRationalTree : Prop where
  genus_eq_zero : ∀ j, Γ.genus j = 0
  two_le_weight : ∀ j, 2 ≤ Γ.weight j
  edgeWeight_le_one : ∀ j k, Γ.edgeWeight j k ≤ 1
  isTree_or_isEmpty : Γ.IsTree ∨ IsEmpty V

end WeightedGraph

end MMP.Flips
