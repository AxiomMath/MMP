module
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
public import MMP.Combinatorics.WeightedGraph.BranchValues
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector

/-!
# Log discrepancies of weighted dual graphs

Let `Γ` be a negative definite weighted graph with simple edges whose underlying graph is a tree.
Its log discrepancy vector `a(Γ)` (any `a` with `Γ.IsLogDiscrepancyVector a`, unique by negative
definiteness) is given by the cofactor formula
`a(Γ)_j = Δ(Γ)⁻¹ ∑_k Δ(Γ - path(v_j, v_k)) c_k(Γ)`.
Grouping its terms by the components `Γ_i` of `Γ - v` gives the branch decomposition
`a(Γ)_v = Δ(Γ - v) / Δ(Γ) · (c_v(Γ) + ∑_i σ(Γ, v, Γ_i) / Δ(Γ_i))`.

Specialised to the shapes of FA 3.2, this gives the value of `a(Γ)` at the centre of a star with
`N` arms, `Δ_1 ⋯ Δ_N / Δ(Γ) · (∑_i 1 / Δ_i - (N - 2))`, and at a fork of a two-fork graph, and
from these the classification of the log canonical and log terminal configurations: a three-arm
star is log terminal for the platonic triples of arm determinants and has `a_v = 0` for the
euclidean ones; a four-arm star is log canonical at its centre only when all arms are
`(-2)`-curves; a star with five or more arms, and the graphs of Fig. 2, are not log canonical at
the marked vertex; a log canonical two-fork graph has four `(-2)`-leaves. Finally FA 3.3.1 lists
the boundaries a log canonical chain can carry.

## Main results

* `IsLogDiscrepancyVector.apply_eq_of_isTree`: the cofactor formula.
* `IsLogDiscrepancyVector.apply_eq_branchValue_of_isTree`: the branch decomposition.
* `IsLogDiscrepancyVector.apply_eq_of_isStar`, `apply_eq_of_isStar_three`,
  `apply_eq_of_isStar_four`: the value at the centre of a star.
* `IsLogDiscrepancyVector.forall_pos_of_isStar_three`,
  `IsLogDiscrepancyVector.apply_eq_zero_of_isStar_three`: platonic and euclidean three-arm stars.
* `IsLogDiscrepancyVector.forall_arms_eq_singleton_of_isStar_four`,
  `IsLogDiscrepancyVector.apply_neg_of_isStar_of_five_le`: stars with four and more arms.
* `IsLogDiscrepancyVector.apply_eq_of_isTwoForkGraphWith`,
  `IsLogDiscrepancyVector.eq_singleton_of_isTwoForkGraphWith`: two-fork graphs.
* `IsLogDiscrepancyVector.apply_neg_of_isFig2LeftShape`,
  `IsLogDiscrepancyVector.apply_neg_of_isFig2RightShape`: the graphs of Fig. 2.
* `IsLogDiscrepancyVector.boundary_cases_of_isChainOrder`: boundaries on log canonical chains.

## Implementation notes

`Δ(Γ)` is `Γ.det`, `Δ(Γ - path(v_j, v_k))` is `(Γ.removeSet (Γ.treePath j k)).det`, and the
determinant of a vertex set `C` is `Γ.delta C`. Components of `Γ - v`, star arms and the parts of
a two-fork graph are given by their vertex sets. The source's sorted triples of arm determinants
are equalities of multisets, so that no ordering of the arms is imposed.

For FA 3.3.1 the chain is enumerated by `e : Fin s ≃ V`, and the log discrepancy equations are
read as a linear recurrence on sequences extended by zero to `ℕ`. Summing them gives
`∑ β ∈ {1, 2}`. When `β` is `1` at an inner vertex `w_j`, convexity of the recurrence on either
side gives `(p + 1) a_{j-1} ≤ p a_j + 1` for the left part of length `p`, and the same on the
right; with the equation at `w_j` this forces both parts to be single vertices of weight `2`.
The source instead uses the branch decomposition and the chain determinant bound
`Δ ≥ length + 1`; the two inequalities are the same.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.1.10,
  3.2.1–3.2.7, 3.3.1
-/

namespace MMP.Flips.WeightedGraph

open Finset

/-! ### Determinant bounds -/

/-- A negative definite weighted graph has positive determinant `Δ(Γ) = Δ(V)`. -/
private theorem det_pos {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}
    (hneg : Γ.IsNegDef) : 0 < Γ.det := by
  have h := hneg.delta_pos univ
  rw [← det_restrict, WeightedGraph.det, ← Matrix.det_submatrix_equiv_self
    (Equiv.subtypeUnivEquiv mem_univ).symm] at h
  convert h using 1
  rw [WeightedGraph.det]
  congr 1
  ext x y
  simp only [WeightedGraph.matrix, Matrix.neg_apply, Matrix.of_apply, Matrix.submatrix_apply,
    Equiv.subtypeUnivEquiv_symm_apply, Subtype.ext_iff]
  rfl

/-- If all weights are at least `2`, a chain `C` attached to `v` at an end has `Δ(C) ≥ 2`. -/
private theorem two_le_delta {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hw' : ∀ j, 2 ≤ Γ.weight j) {v : V} {C : Finset V}
    (hC : Γ.IsChainAttachedAtEnd v C) : 2 ≤ Γ.delta C := by
  obtain ⟨-, -, s, hs, e, he, -, -⟩ := hC
  have := add_one_le_det_of_isChainOrder (Γ.restrict C) hs e he fun w => hw' w
  unfold WeightedGraph.delta
  push_cast at this
  omega

/-- If all weights are at least `2`, a chain `C` attached to `v` at an end has `Δ(C) ≥ 2`, and
`Δ(C) = 2` only if `C` is a single vertex of weight `2`. -/
private theorem two_le_delta_and_exists_singleton {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hw' : ∀ j, 2 ≤ Γ.weight j) {v : V} {C : Finset V}
    (hC : Γ.IsChainAttachedAtEnd v C) :
    2 ≤ Γ.delta C ∧ (Γ.delta C = 2 → ∃ u, C = {u} ∧ Γ.weight u = 2) := by
  refine ⟨two_le_delta hw' hC, fun h2 => ?_⟩
  obtain ⟨-, -, s, hs, e, he, -, -⟩ := hC
  obtain ⟨rfl, hwt⟩ :=
    (det_eq_two_iff_of_isChainOrder (Γ.restrict C) hs e he fun w => hw' w).1 h2
  exact ⟨e 0, eq_singleton_iff_unique_mem.2 ⟨(e 0).2, fun x hx =>
    congrArg Subtype.val (e.symm_apply_eq.1 (Subsingleton.elim (e.symm ⟨x, hx⟩) 0))⟩, hwt⟩

/-- If all weights are at least `2`, a chain `C` attached to `v` at an end contributes
`1 / Δ(C) ≤ 1 / 2` to the branch sum. -/
private theorem one_div_delta_le_half {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hw' : ∀ j, 2 ≤ Γ.weight j) {v : V} {C : Finset V}
    (hC : Γ.IsChainAttachedAtEnd v C) : 1 / (Γ.delta C : ℚ) ≤ 1 / 2 :=
  one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast two_le_delta hw' hC)

/-! ### The cofactor formula -/

section

open Matrix

/-- For a tree with simple edges, the `(k, j)` entry of the adjugate of `-M(Γ)` is
`Δ(Γ - path(j, k))`. -/
private theorem adjugate_neg_matrix_apply {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hs : Γ.HasSimpleEdges) (ht : Γ.IsTree) (j k : V) :
    (-Γ.matrix).adjugate k j = (Γ.removeSet (Γ.treePath j k)).det := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨j⟩).ne'
  rw [← neg_one_smul ℤ Γ.matrix, adjugate_smul, Matrix.smul_apply,
    adjugate_matrix_apply_of_isTree hs ht, hn]
  simp [pow_succ, ← mul_assoc, ← mul_pow]

/-- For a negative definite weighted tree `Γ` with simple edges, its log discrepancy vector `a`
satisfies `a_j = Δ(Γ)⁻¹ ∑_k Δ(Γ - path(v_j, v_k)) c_k(Γ)` for every vertex `v_j`. -/
@[mmp "lem_fa3_log_discrepancy_formula"]
public theorem IsLogDiscrepancyVector.apply_eq_of_isTree {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) (hs : Γ.HasSimpleEdges) (ht : Γ.IsTree)
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (j : V) :
    a j = (1 / (Γ.det : ℚ)) * ∑ k, ((Γ.removeSet (Γ.treePath j k)).det : ℚ) * Γ.c k := by
  set N : Matrix V V ℚ := (-Γ.matrix).map ((↑) : ℤ → ℚ)
  have hN : a ᵥ* N = Γ.c := funext fun i => by
    simpa [N, vecMul, dotProduct, neg_eq_iff_eq_neg] using ha i
  have hdet : N.det = Γ.det := by simp [N, WeightedGraph.det, Int.cast_det]
  have hu : IsUnit N.det := by
    rw [hdet]; exact (Int.cast_ne_zero.2 (det_pos hneg).ne').isUnit
  have hadj : N.adjugate = (-Γ.matrix).adjugate.map ((↑) : ℤ → ℚ) :=
    (RingHom.map_adjugate (Int.castRingHom ℚ) _).symm
  rw [← vecMul_one a, ← mul_nonsing_inv N hu, ← vecMul_vecMul, hN, Matrix.inv_def, vecMul_smul,
    Pi.smul_apply, hdet, Ring.inverse_eq_inv', smul_eq_mul, one_div]
  simp [vecMul, dotProduct, hadj, adjugate_neg_matrix_apply hs ht, mul_comm]

end

/-! ### The branch decomposition -/

section BranchDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}

/-- The inclusion of `Γ - v` into `Γ` as a graph homomorphism. -/
private def incl (v : V) :
    (Γ.removeVertex v).underlyingGraph →g Γ.underlyingGraph where
  toFun x := x.1
  map_rel' {x y} h := ⟨fun hxy => h.1 (Subtype.ext hxy), h.2⟩

private theorem mem_sdiff_singleton {v x : V} (hx : x ≠ v) : x ∈ (univ \ {v} : Finset V) := by
  simp [hx]

private theorem ne_of_mem_sdiff_singleton {v : V} (x : ↥(univ \ {v} : Finset V)) :
    (x : V) ≠ v :=
  fun e => (mem_sdiff.mp x.2).2 (mem_singleton.mpr e)

/-- An edge of `Γ` between vertices other than `v` is an edge of `Γ - v`. -/
private theorem adj_removeVertex {v x y : V} (hx : x ≠ v) (hy : y ≠ v)
    (h : Γ.underlyingGraph.Adj x y) :
    (Γ.removeVertex v).underlyingGraph.Adj ⟨x, mem_sdiff_singleton hx⟩
      ⟨y, mem_sdiff_singleton hy⟩ :=
  ⟨fun e => h.1 (congrArg Subtype.val e), h.2⟩

/-- A walk of `Γ` avoiding `v` connects its ends in `Γ - v`. -/
private theorem reachable_of_walk {v : V} :
    ∀ {x y : V} (p : Γ.underlyingGraph.Walk x y) (hp : ∀ z ∈ p.support, z ≠ v),
      (Γ.removeVertex v).underlyingGraph.Reachable
        ⟨x, mem_sdiff_singleton (hp x p.start_mem_support)⟩
        ⟨y, mem_sdiff_singleton (hp y p.end_mem_support)⟩
  | _, _, .nil, _ => SimpleGraph.Reachable.refl _
  | x, y, .cons (v := z) h p, hp => by
    have hz : z ≠ v := hp z (by simp)
    refine SimpleGraph.Reachable.trans (adj_removeVertex (hp x (by simp)) hz h).reachable
      (reachable_of_walk p fun w hw => hp w (by simp [hw]))

private theorem mem_of_isComponent {v : V} {C : Finset V}
    {c : (Γ.removeVertex v).underlyingGraph.ConnectedComponent}
    (hc : (C : Set V) = Subtype.val '' c.supp) {x : V} (hx : x ≠ v)
    (h : (Γ.removeVertex v).underlyingGraph.connectedComponentMk
      ⟨x, mem_sdiff_singleton hx⟩ = c) : x ∈ C := by
  have : x ∈ (C : Set V) := hc ▸ ⟨⟨x, mem_sdiff_singleton hx⟩, h, rfl⟩
  exact_mod_cast this

private theorem component_of_mem {v : V} {C : Finset V}
    {c : (Γ.removeVertex v).underlyingGraph.ConnectedComponent}
    (hc : (C : Set V) = Subtype.val '' c.supp) {x : V} (hx : x ∈ C) :
    ∃ hxv : x ≠ v, (Γ.removeVertex v).underlyingGraph.connectedComponentMk
      ⟨x, mem_sdiff_singleton hxv⟩ = c := by
  obtain ⟨x', hx'c, rfl⟩ : x ∈ Subtype.val '' c.supp := hc ▸ (show x ∈ (C : Set V) from hx)
  exact ⟨ne_of_mem_sdiff_singleton x', hx'c⟩

/-- For `w, k` in a component `C` of `Γ - v`, a path of `Γ` from `w` to `k` inside `C`. -/
private theorem exists_path_subset {v : V} {C : Finset V} (hC : Γ.IsComponentOfRemoveVertex v C)
    {w k : V} (hw : w ∈ C) (hk : k ∈ C) :
    ∃ q : Γ.Path w k, ∀ z ∈ q.1.support, z ∈ C := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨hwv, hwc⟩ := component_of_mem hc hw
  obtain ⟨hkv, hkc⟩ := component_of_mem hc hk
  have hr : (Γ.removeVertex v).underlyingGraph.Reachable ⟨w, mem_sdiff_singleton hwv⟩
      ⟨k, mem_sdiff_singleton hkv⟩ :=
    SimpleGraph.ConnectedComponent.exact (hwc.trans hkc.symm)
  let q := hr.some.toPath
  refine ⟨q.map (incl v) Subtype.val_injective, fun z hz => ?_⟩
  change z ∈ (q.1.map (incl v)).support at hz
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hz
  obtain ⟨z', hz', rfl⟩ := hz
  exact mem_of_isComponent hc (ne_of_mem_sdiff_singleton z')
    ((SimpleGraph.ConnectedComponent.sound (q.1.dropUntil z' hz').reachable).trans hkc)

/-- A component `C` of `Γ - v` of a connected graph contains a neighbour of `v`, if nonempty. -/
private theorem exists_adj {v : V} {C : Finset V} (hC : Γ.IsComponentOfRemoveVertex v C)
    (hconn : Γ.underlyingGraph.Connected) {k : V} (hk : k ∈ C) :
    ∃ w ∈ C, Γ.underlyingGraph.Adj v w := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨hkv, hkc⟩ := component_of_mem hc hk
  let p := (hconn.preconnected v k).some.toPath
  have hpath := p.2
  generalize (p : Γ.underlyingGraph.Walk v k) = q at hpath
  cases q with
  | nil => exact absurd rfl hkv
  | @cons _ w _ h q =>
    rw [SimpleGraph.Walk.cons_isPath_iff] at hpath
    have hq : ∀ z ∈ q.support, z ≠ v := fun z hz hzv => hpath.2 (hzv ▸ hz)
    refine ⟨w, mem_of_isComponent hc (hq w q.start_mem_support) ?_, h⟩
    exact (SimpleGraph.ConnectedComponent.sound (reachable_of_walk q hq)).trans hkc

/-- In a tree, `v` has at most one neighbour in a component `C` of `Γ - v`. -/
private theorem adj_unique {v : V} {C : Finset V} (hC : Γ.IsComponentOfRemoveVertex v C)
    (hac : Γ.underlyingGraph.IsAcyclic) {w w' : V} (hw : w ∈ C) (hw' : w' ∈ C)
    (h : Γ.underlyingGraph.Adj v w) (h' : Γ.underlyingGraph.Adj v w') : w' = w := by
  have hvC := notMem_of_isComponentOfRemoveVertex Γ hC
  obtain ⟨q, hq⟩ := exists_path_subset hC hw' hw
  let p₁ : Γ.Path v w := ⟨.cons h' q.1, q.2.cons fun hv => hvC (hq v hv)⟩
  let p₂ : Γ.Path v w := ⟨.cons h .nil, by simp [h.ne]⟩
  have := congrArg (fun p : Γ.Path v w => p.1.support) (hac.path_unique p₁ p₂)
  simp only [p₁, p₂, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.cons.injEq, true_and] at this
  have hm := q.1.start_mem_support
  rw [this] at hm
  simpa using hm

/-- In a tree, the path from `v` to `k ∈ C` is `v` followed by the path from the neighbour `w`
of `v` in `C` to `k`, which lies in `C`. -/
private theorem treePath_eq_insert {v : V} {C : Finset V} (hC : Γ.IsComponentOfRemoveVertex v C)
    (hac : Γ.IsAcyclic) {w k : V} (hw : w ∈ C) (hk : k ∈ C) (h : Γ.underlyingGraph.Adj v w) :
    Γ.treePath v k = insert v (Γ.treePath w k) ∧ Γ.treePath w k ⊆ C := by
  have hvC := notMem_of_isComponentOfRemoveVertex Γ hC
  obtain ⟨q, hq⟩ := exists_path_subset hC hw hk
  let p : Γ.Path v k := ⟨.cons h q.1, q.2.cons fun hv => hvC (hq v hv)⟩
  rw [Γ.treePath_eq_support hac p, Γ.treePath_eq_support hac q]
  refine ⟨by simp [p], fun z hz => hq z (by simpa using hz)⟩

section Components

variable {v : V} {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → Finset V}

/-- **The determinant of `Γ` minus a path into a branch.** For `k` in the component `C i` of
`Γ - v`, with `w` the neighbour of `v` in `C i`, the graph `Γ - path(v, k)` is the disjoint union,
without edges between the parts, of `C i - path(w, k)` and the other components. -/
private theorem delta_compl_treePath (hac : Γ.IsAcyclic)
    (hC : ∀ i, Γ.IsComponentOfRemoveVertex v (C i))
    (hdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hunion : univ.biUnion C = univ \ {v}) {i : ι} {w k : V} (hw : w ∈ C i) (hk : k ∈ C i)
    (hvw : Γ.underlyingGraph.Adj v w) :
    Γ.delta (univ \ Γ.treePath v k) =
      Γ.delta (C i \ Γ.treePath w k) * Γ.delta ((univ.erase i).biUnion C) := by
  obtain ⟨hpk, hsub⟩ := treePath_eq_insert (hC i) hac hw hk hvw
  have hvC (l : ι) := notMem_of_isComponentOfRemoveVertex Γ (hC l)
  have hset : univ \ Γ.treePath v k = (C i \ Γ.treePath w k) ∪ (univ.erase i).biUnion C := by
    ext x
    simp only [hpk, mem_sdiff, mem_univ, mem_insert, not_or, true_and, mem_union,
      mem_biUnion, mem_erase]
    constructor
    · rintro ⟨hxv, hxp⟩
      obtain ⟨l, -, hl⟩ := mem_biUnion.mp (hunion ▸ (by simp [hxv]) : x ∈ univ.biUnion C)
      by_cases hli : l = i
      · exact Or.inl ⟨hli ▸ hl, hxp⟩
      · exact Or.inr ⟨l, ⟨hli, trivial⟩, hl⟩
    · rintro (⟨hx, hxp⟩ | ⟨l, ⟨hli, -⟩, hl⟩)
      · exact ⟨fun h => hvC i (h ▸ hx), hxp⟩
      · exact ⟨fun h => hvC l (h ▸ hl), fun h => disjoint_left.mp (hdisj hli) hl (hsub h)⟩
  rw [hset, Γ.delta_union_of_edgeWeight_eq_zero (by
    rw [disjoint_biUnion_right]
    exact fun l hl => disjoint_of_subset_left sdiff_subset (hdisj (Ne.symm (ne_of_mem_erase hl))))]
  intro x hx y hy
  obtain ⟨l, hl, hyl⟩ := mem_biUnion.mp hy
  exact Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex (hC i) (sdiff_subset hx)
    (disjoint_left.mp (hdisj (ne_of_mem_erase hl)) hyl) fun h => hvC l (h ▸ hyl)

/-- `Δ(Γ - v) = Δ(Γ_i) ∏_{l ≠ i} Δ(Γ_l)`, solved for the product. -/
private theorem delta_biUnion_erase (hneg : Γ.IsNegDef)
    (hC : ∀ i, Γ.IsComponentOfRemoveVertex v (C i))
    (hdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hunion : univ.biUnion C = univ \ {v}) (i : ι) :
    (Γ.delta ((univ.erase i).biUnion C) : ℚ) =
      ((Γ.removeVertex v).det : ℚ) / Γ.delta (C i) := by
  have hpos : (0 : ℚ) < Γ.delta (C i) := by exact_mod_cast hneg.delta_pos (C i)
  change _ = ((Γ.delta (univ \ {v}) : ℤ) : ℚ) / _
  rw [← hunion, Γ.delta_biUnion_eq_prod hC hdisj, Γ.delta_biUnion_eq_prod hC hdisj,
    ← Finset.mul_prod_erase _ _ (mem_univ i)]
  push_cast
  field_simp

/-- The terms of the log discrepancy formula at `v` for the vertices of one branch `C i` sum to
`Δ(Γ - v) σ_i / Δ(Γ_i)`. -/
private theorem sum_branch (hneg : Γ.IsNegDef) (ht : Γ.IsTree)
    (hC : ∀ i, Γ.IsComponentOfRemoveVertex v (C i))
    (hdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hunion : univ.biUnion C = univ \ {v}) (i : ι) :
    ∑ k ∈ C i, ((Γ.removeSet (Γ.treePath v k)).det : ℚ) * Γ.c k =
      (Γ.removeVertex v).det * (Γ.branchValue v (C i) / Γ.delta (C i)) := by
  rcases (C i).eq_empty_or_nonempty with he | ⟨k₀, hk₀⟩
  · simp [he, branchValue]
  obtain ⟨w, hw, hvw⟩ := exists_adj (hC i) ht.connected hk₀
  rw [Γ.branchValue_eq hw hvw fun w' hw' h' => adj_unique (hC i) ht.isAcyclic hw hw' hvw h',
    Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [det_removeSet, delta_compl_treePath ht.isAcyclic hC hdisj hunion hw hk hvw, Int.cast_mul,
    delta_biUnion_erase hneg hC hdisj hunion]
  ring

end Components

end BranchDecomposition

/-- For a negative definite weighted tree `Γ` with simple edges, a vertex `v`, and the
connected components `Γ_i` of `Γ - v` (vertex sets `C i`), the log discrepancy vector `a` of
`Γ` satisfies `a_v = Δ(Γ - v) / Δ(Γ) · (c_v(Γ) + ∑_i σ(Γ, v, Γ_i) / Δ(Γ_i))`. -/
@[mmp "lem_fa3_log_discrepancy_branch_decomposition"]
public theorem IsLogDiscrepancyVector.apply_eq_branchValue_of_isTree {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) (hs : Γ.HasSimpleEdges)
    (ht : Γ.IsTree) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (v : V)
    {ι : Type*} [Fintype ι] (C : ι → Finset V) (hC : ∀ i, Γ.IsComponentOfRemoveVertex v (C i))
    (hdisj : Pairwise fun i j => Disjoint (C i) (C j))
    (hunion : Finset.univ.biUnion C = Finset.univ \ {v}) :
    a v = ((Γ.removeVertex v).det : ℚ) / (Γ.det : ℚ) *
      (Γ.c v + ∑ i, Γ.branchValue v (C i) / (Γ.delta (C i) : ℚ)) := by
  classical
  rw [ha.apply_eq_of_isTree hneg hs ht v, ← add_sum_erase _ _ (mem_univ v),
    ← sdiff_singleton_eq_erase, treePath_self]
  rw [sum_congr hunion.symm fun _ _ => rfl, sum_biUnion fun i _ j _ hij => hdisj hij,
    sum_congr rfl fun i _ => sum_branch hneg ht hC hdisj hunion i, ← mul_sum]
  ring

/-! ### Stars -/

/-- Let `Γ` be a negative definite weighted graph with all genera and boundary degrees `0` which
is a star with arms `arms : Fin N → Finset V` at `v`, and let `a` be its log discrepancy vector.
Then `a v = (∏ i, Δ_i) / Δ(Γ) · (∑ i, 1 / Δ_i - (N - 2))`, where `Δ_i = Γ.delta (arms i)`. -/
@[mmp "lem_fa3_star_log_discrepancy_formula"]
public theorem IsLogDiscrepancyVector.apply_eq_of_isStar {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) (hp : ∀ j, Γ.genus j = 0)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {N : ℕ} {arms : Fin N → Finset V}
    (hstar : Γ.IsStar v arms) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    a v = (∏ i, (Γ.delta (arms i) : ℚ)) / (Γ.det : ℚ) *
      (∑ i, 1 / (Γ.delta (arms i) : ℚ) - ((N : ℚ) - 2)) := by
  rw [ha.apply_eq_branchValue_of_isTree hneg hstar.hasSimpleEdges hstar.isTree v arms
      hstar.isComponent hstar.pairwise_disjoint hstar.biUnion_eq,
    det_removeSet, Γ.delta_sdiff_eq_prod_of_isStar hstar,
    Γ.c_eq_of_hasSimpleEdges hstar.hasSimpleEdges, hp, hβ, hstar.degree_eq]
  simp only [Γ.branchValue_eq_one_of_isChainAttachedAtEnd hstar.hasSimpleEdges
    (hstar.isChainAttachedAtEnd _) (fun k _ => hβ k)]
  push_cast
  ring

/-- Let `Γ` be a negative definite weighted graph with all genera and boundary degrees `0` which
is a star with three arms `arms : Fin 3 → Finset V` at `v`, and let `a` be its log discrepancy
vector. Then `a v = Δ_1 Δ_2 Δ_3 / Δ(Γ) · (1 / Δ_1 + 1 / Δ_2 + 1 / Δ_3 - 1)`, where
`Δ_i = Γ.delta (arms i)`. -/
@[mmp "lem_fa3_three_arm_formula"]
public theorem IsLogDiscrepancyVector.apply_eq_of_isStar_three {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) (hp : ∀ j, Γ.genus j = 0)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {arms : Fin 3 → Finset V}
    (hstar : Γ.IsStar v arms) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    a v = (Γ.delta (arms 0) : ℚ) * Γ.delta (arms 1) * Γ.delta (arms 2) / (Γ.det : ℚ) *
      (1 / (Γ.delta (arms 0) : ℚ) + 1 / (Γ.delta (arms 1) : ℚ) +
        1 / (Γ.delta (arms 2) : ℚ) - 1) := by
  rw [ha.apply_eq_of_isStar hneg hp hβ hstar, Fin.prod_univ_three, Fin.sum_univ_three]
  norm_num

/-- For the platonic triples `{x, y, z} = {2, 2, m}` (`m ≥ 2`), `{2, 3, 3}`, `{2, 3, 4}` and
`{2, 3, 5}`, one has `1 / x + 1 / y + 1 / z > 1`. -/
private theorem one_lt_inv_add_inv_add_inv {x y z : ℤ}
    (h : (∃ m : ℤ, 2 ≤ m ∧ ({x, y, z} : Multiset ℤ) = {2, 2, m}) ∨
      ({x, y, z} : Multiset ℤ) = {2, 3, 3} ∨ ({x, y, z} : Multiset ℤ) = {2, 3, 4} ∨
      ({x, y, z} : Multiset ℤ) = {2, 3, 5}) :
    1 < 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  have key : 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) =
      (({x, y, z} : Multiset ℤ).map fun t : ℤ => 1 / (t : ℚ)).sum := by
    simp [add_assoc]
  rw [key]
  rcases h with ⟨m, hm, h⟩ | h | h | h <;> rw [h]
  · have : (0 : ℚ) < 1 / (m : ℚ) := by
      have : (2 : ℚ) ≤ m := by exact_mod_cast hm
      positivity
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    push_cast
    linarith
  all_goals norm_num

/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which is a star
with three arms `arms : Fin 3 → Finset V` at `v`, and let `a` be its log discrepancy vector. If
the arm determinants `Δ_i = Γ.delta (arms i)` form one of the multisets `{2, 2, m}` (`m ≥ 2`),
`{2, 3, 3}`, `{2, 3, 4}`, `{2, 3, 5}`, then `a k > 0` for every vertex `k`. -/
@[mmp "lem_fa3_three_arm_lt_cases"]
public theorem IsLogDiscrepancyVector.forall_pos_of_isStar_three {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {arms : Fin 3 → Finset V}
    (hstar : Γ.IsStar v arms)
    (hcases : (∃ m : ℤ, 2 ≤ m ∧
        ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 2, m}) ∨
      ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 3} ∨
      ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 4} ∨
      ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 5})
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    ∀ k, 0 < a k := by
  rw [ha.forall_pos_iff_of_isStar hΓ hneg hβ hstar,
    ha.apply_eq_of_isStar_three hneg hΓ.genus_eq_zero hβ hstar]
  refine mul_pos (div_pos (mul_pos (mul_pos ?_ ?_) ?_) (by exact_mod_cast det_pos hneg))
    (sub_pos.2 (one_lt_inv_add_inv_add_inv hcases))
  all_goals exact_mod_cast hneg.delta_pos _

/-- The Euclidean triples `{2, 3, 6}`, `{2, 4, 4}`, `{3, 3, 3}` have reciprocal sum `1`. -/
private theorem inv_add_inv_add_inv_eq_one {x y z : ℤ}
    (h : ({x, y, z} : Multiset ℤ) = {2, 3, 6} ∨ ({x, y, z} : Multiset ℤ) = {2, 4, 4} ∨
      ({x, y, z} : Multiset ℤ) = {3, 3, 3}) :
    1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) = 1 := by
  have key : 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) =
      (({x, y, z} : Multiset ℤ).map fun t : ℤ => 1 / (t : ℚ)).sum := by
    simp [add_assoc]
  rw [key]
  rcases h with h | h | h <;> rw [h] <;> norm_num

/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which is a star
with three arms `arms : Fin 3 → Finset V` at `v`, and let `a` be its log discrepancy vector. If
the arm determinants `Δ_i = Γ.delta (arms i)` form one of the multisets `{2, 3, 6}`, `{2, 4, 4}`,
`{3, 3, 3}`, then `a v = 0`. -/
@[mmp "lem_fa3_three_arm_lc_not_lt_cases"]
public theorem IsLogDiscrepancyVector.apply_eq_zero_of_isStar_three {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {arms : Fin 3 → Finset V}
    (hstar : Γ.IsStar v arms)
    (hcases :
      ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 3, 6} ∨
      ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {2, 4, 4} ∨
      ({Γ.delta (arms 0), Γ.delta (arms 1), Γ.delta (arms 2)} : Multiset ℤ) = {3, 3, 3})
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    a v = 0 := by
  rw [ha.apply_eq_of_isStar_three hneg hΓ.genus_eq_zero hβ hstar,
    inv_add_inv_add_inv_eq_one hcases, sub_self, mul_zero]

/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which is a star
with four arms `arms : Fin 4 → Finset V` at `v`, and let `a` be its log discrepancy vector.
Then `a v = Δ_1 Δ_2 Δ_3 Δ_4 / Δ(Γ) · (1 / Δ_1 + 1 / Δ_2 + 1 / Δ_3 + 1 / Δ_4 - 2)`, where
`Δ_i = Γ.delta (arms i)`. -/
@[mmp "lem_fa3_four_arm_formula"]
public theorem IsLogDiscrepancyVector.apply_eq_of_isStar_four {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {arms : Fin 4 → Finset V}
    (hstar : Γ.IsStar v arms) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    a v = (Γ.delta (arms 0) : ℚ) * Γ.delta (arms 1) * Γ.delta (arms 2) * Γ.delta (arms 3) /
        (Γ.det : ℚ) *
      (1 / (Γ.delta (arms 0) : ℚ) + 1 / (Γ.delta (arms 1) : ℚ) +
        1 / (Γ.delta (arms 2) : ℚ) + 1 / (Γ.delta (arms 3) : ℚ) - 2) := by
  rw [ha.apply_eq_of_isStar hneg hΓ.genus_eq_zero hβ hstar, Fin.prod_univ_four,
    Fin.sum_univ_four]
  norm_num

/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which is a star
with four arms `arms : Fin 4 → Finset V` at `v`, and let `a` be its log discrepancy vector.
If `0 ≤ a v`, then every arm is a single vertex of weight `2`. -/
@[mmp "lem_fa3_four_arm_lc_only_if"]
public theorem IsLogDiscrepancyVector.forall_arms_eq_singleton_of_isStar_four {V : Type*}
    [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) (hβ : ∀ j, Γ.boundary j = 0) {v : V} {arms : Fin 4 → Finset V}
    (hstar : Γ.IsStar v arms) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (hv : 0 ≤ a v) :
    ∀ i, ∃ u, arms i = {u} ∧ Γ.weight u = 2 := by
  intro i
  have hd := fun j =>
    two_le_delta_and_exists_singleton hΓ.two_le_weight (hstar.isChainAttachedAtEnd j)
  have hpos : ∀ j, (0 : ℚ) < Γ.delta (arms j) := fun j => by exact_mod_cast hneg.delta_pos _
  have hle : ∀ j, 1 / (Γ.delta (arms j) : ℚ) ≤ 1 / 2 := fun j =>
    one_div_delta_le_half hΓ.two_le_weight (hstar.isChainAttachedAtEnd j)
  rw [ha.apply_eq_of_isStar_four hΓ hneg hβ hstar] at hv
  have hsum := nonneg_of_mul_nonneg_right hv (by
    have := hpos 0
    have := hpos 1
    have := hpos 2
    have := hpos 3
    have : (0 : ℚ) < Γ.det := by exact_mod_cast det_pos hneg
    positivity)
  have hi : 1 / 2 ≤ 1 / (Γ.delta (arms i) : ℚ) := by
    fin_cases i <;> dsimp <;> linarith [hle 0, hle 1, hle 2, hle 3]
  refine (hd i).2 (le_antisymm ?_ (hd i).1)
  exact_mod_cast (one_div_le_one_div (by norm_num) (hpos i)).1 hi

/-- If each of `N ≥ 5` rationals `q i` is at least `2`, then `∑ 1 / q i < N - 2`: the bracket
in the star formula for `a_v` is negative. -/
private theorem sum_one_div_sub_neg {N : ℕ} (hN : 5 ≤ N) {q : Fin N → ℚ} (hq : ∀ i, 2 ≤ q i) :
    ∑ i, 1 / q i - ((N : ℚ) - 2) < 0 := by
  have hsum : ∑ i, 1 / q i ≤ ∑ _i : Fin N, (1 / 2 : ℚ) :=
    sum_le_sum fun i _ => one_div_le_one_div_of_le (by norm_num) (hq i)
  have hN' : (5 : ℚ) ≤ N := by exact_mod_cast hN
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  linarith

/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which is a star
with `N ≥ 5` arms `arms : Fin N → Finset V` at `v`, and let `a` be its log discrepancy vector.
Then `a v < 0`. -/
@[mmp "lem_fa3_five_arm_not_lc"]
public theorem IsLogDiscrepancyVector.apply_neg_of_isStar_of_five_le {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {N : ℕ} (hN : 5 ≤ N) {arms : Fin N → Finset V}
    (hstar : Γ.IsStar v arms) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    a v < 0 := by
  rw [ha.apply_eq_of_isStar hneg hΓ.genus_eq_zero hβ hstar]
  have hq (i : Fin N) : (2 : ℚ) ≤ Γ.delta (arms i) := by
    exact_mod_cast two_le_delta hΓ.two_le_weight (hstar.isChainAttachedAtEnd i)
  refine mul_neg_of_pos_of_neg (div_pos (prod_pos fun i _ => by linarith [hq i]) ?_)
    (sum_one_div_sub_neg hN hq)
  exact_mod_cast det_pos hneg

/-! ### Two-fork graphs -/

section TwoFork

variable {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} {v v' : V}
  {C₁ C₂ C₃ A B : Finset V}

/-- The three branches of a two-fork graph are components of `Γ - v`. -/
private theorem isComponent_branches (htwo : Γ.IsTwoForkGraphWith v v' C₁ C₂ C₃ A B) :
    ∀ i, Γ.IsComponentOfRemoveVertex v (![C₁, C₂, C₃] i) := by
  intro i
  fin_cases i
  exacts [htwo.isChainAttachedAtEnd₁.2.1, htwo.isChainAttachedAtEnd₂.2.1,
    htwo.isForkedBranch₃.isComponent]

/-- The three branches of a two-fork graph are pairwise disjoint. -/
private theorem pairwise_disjoint_branches
    (htwo : Γ.IsTwoForkGraphWith v v' C₁ C₂ C₃ A B) :
    Pairwise fun i j => Disjoint (![C₁, C₂, C₃] i) (![C₁, C₂, C₃] j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  all_goals first
    | exact htwo.disjoint₁₂ | exact htwo.disjoint₁₃ | exact htwo.disjoint₂₃
    | exact htwo.disjoint₁₂.symm | exact htwo.disjoint₁₃.symm | exact htwo.disjoint₂₃.symm

/-- The three branches of a two-fork graph cover `Γ - v`. -/
private theorem biUnion_branches (htwo : Γ.IsTwoForkGraphWith v v' C₁ C₂ C₃ A B) :
    univ.biUnion ![C₁, C₂, C₃] = univ \ {v} := by
  rw [← htwo.union_eq]
  ext x
  simp [Fin.exists_fin_succ, or_assoc]

end TwoFork

/-- Let `Γ` be a negative definite two-fork graph with forks `v ≠ v'`, with all genera and
boundary degrees `0`, where `Γ - v = Γ_1 ⊔ Γ_2 ⊔ Γ_3` (vertex sets `C₁, C₂, C₃`) and `Γ_3` is a
forked branch with fork `v'` and arms `Γ_A, Γ_B` (vertex sets `A, B`), and let `a` be its log
discrepancy vector. Then
`a v = Δ_1 Δ_2 Δ_3 / Δ(Γ) · (1 / Δ_1 + 1 / Δ_2 + (1 - (Δ_A - 1)(Δ_B - 1)) / Δ_3 - 1)`, where
`Δ_i = Γ.delta Cᵢ`, `Δ_A = Γ.delta A` and `Δ_B = Γ.delta B`. -/
@[mmp "lem_fa3_two_fork_formula"]
public theorem IsLogDiscrepancyVector.apply_eq_of_isTwoForkGraphWith {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) (hp : ∀ j, Γ.genus j = 0)
    (hβ : ∀ j, Γ.boundary j = 0) {v v' : V} {C₁ C₂ C₃ A B : Finset V}
    (htwo : Γ.IsTwoForkGraphWith v v' C₁ C₂ C₃ A B) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) :
    a v = (Γ.delta C₁ : ℚ) * Γ.delta C₂ * Γ.delta C₃ / (Γ.det : ℚ) *
      (1 / (Γ.delta C₁ : ℚ) + 1 / (Γ.delta C₂ : ℚ) +
        (1 - ((Γ.delta A : ℚ) - 1) * ((Γ.delta B : ℚ) - 1)) / (Γ.delta C₃ : ℚ) - 1) := by
  have hC := isComponent_branches htwo
  have hdisj := pairwise_disjoint_branches htwo
  rw [ha.apply_eq_branchValue_of_isTree hneg htwo.hasSimpleEdges htwo.isTree v _ hC hdisj
      (biUnion_branches htwo), det_removeSet, ← biUnion_branches htwo,
    Γ.delta_biUnion_eq_prod hC hdisj,
    Γ.c_eq_of_hasSimpleEdges htwo.hasSimpleEdges, hp, hβ, htwo.degree_eq]
  simp only [Fin.prod_univ_three, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Γ.branchValue_eq_one_of_isChainAttachedAtEnd htwo.hasSimpleEdges
      htwo.isChainAttachedAtEnd₁ (fun k _ => hβ k),
    Γ.branchValue_eq_one_of_isChainAttachedAtEnd htwo.hasSimpleEdges
      htwo.isChainAttachedAtEnd₂ (fun k _ => hβ k),
    Γ.branchValue_eq_of_isForkedBranch htwo.isForkedBranch₃ (fun k _ => hp k) (fun k _ => hβ k)]
  push_cast
  ring

/-- If `x₁, x₂, y, z ≥ 2`, `x₃ > 0` and the two-fork bracket is nonnegative, then
`x₁ = x₂ = y = z = 2`. -/
private theorem eq_two_of_twoFork_bracket_nonneg {x₁ x₂ x₃ y z : ℚ} (h₁ : 2 ≤ x₁)
    (h₂ : 2 ≤ x₂) (h₃ : 0 < x₃) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (h : 0 ≤ 1 / x₁ + 1 / x₂ + (1 - (y - 1) * (z - 1)) / x₃ - 1) :
    x₁ = 2 ∧ x₂ = 2 ∧ y = 2 ∧ z = 2 := by
  have l₁ : 1 / x₁ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h₁
  have l₂ : 1 / x₂ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h₂
  have l₃ : (1 - (y - 1) * (z - 1)) / x₃ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by nlinarith) h₃.le
  have e₃ : (y - 1) * (z - 1) = 1 := by
    have : (1 - (y - 1) * (z - 1)) / x₃ = 0 := by linarith
    rw [div_eq_zero_iff, or_iff_left h₃.ne'] at this
    linarith
  have e₁ : 1 / x₁ = 1 / 2 := by linarith
  have e₂ : 1 / x₂ = 1 / 2 := by linarith
  exact ⟨by simpa using e₁, by simpa using e₂, by nlinarith, by nlinarith⟩

/-- Let `Γ` be a negative definite two-fork graph with forks `v ≠ v'`, with all genera and
boundary degrees `0` and all weights at least `2`, where `Γ - v = Γ_1 ⊔ Γ_2 ⊔ Γ_3` (vertex sets
`C₁, C₂, C₃`) and `Γ_3` is a forked branch with fork `v'` and arms `Γ_A, Γ_B` (vertex sets
`A, B`), and let `a` be its log discrepancy vector. If `0 ≤ a v`, then each of
`Γ_1, Γ_2, Γ_A, Γ_B` is a single vertex of weight `2`. -/
@[mmp "lem_fa3_two_fork_lc_only_if"]
public theorem IsLogDiscrepancyVector.eq_singleton_of_isTwoForkGraphWith {V : Type*}
    [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} (hneg : Γ.IsNegDef)
    (hp : ∀ j, Γ.genus j = 0) (hβ : ∀ j, Γ.boundary j = 0) (hw : ∀ j, 2 ≤ Γ.weight j)
    {v v' : V} {C₁ C₂ C₃ A B : Finset V} (htwo : Γ.IsTwoForkGraphWith v v' C₁ C₂ C₃ A B)
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (hv : 0 ≤ a v) :
    (∃ u, C₁ = {u} ∧ Γ.weight u = 2) ∧ (∃ u, C₂ = {u} ∧ Γ.weight u = 2) ∧
      (∃ u, A = {u} ∧ Γ.weight u = 2) ∧ (∃ u, B = {u} ∧ Γ.weight u = 2) := by
  have h₁ := two_le_delta_and_exists_singleton hw htwo.isChainAttachedAtEnd₁
  have h₂ := two_le_delta_and_exists_singleton hw htwo.isChainAttachedAtEnd₂
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hA, hB⟩ := htwo.isForkedBranch₃.exists_spine
  replace hA := two_le_delta_and_exists_singleton hw hA
  replace hB := two_le_delta_and_exists_singleton hw hB
  have h₃ : (0 : ℚ) < Γ.delta C₃ := by exact_mod_cast hneg.delta_pos C₃
  rw [ha.apply_eq_of_isTwoForkGraphWith hneg hp hβ htwo] at hv
  have hpre : (0 : ℚ) < Γ.delta C₁ * Γ.delta C₂ * Γ.delta C₃ / Γ.det := by
    have : (0 : ℚ) < Γ.det := by exact_mod_cast det_pos hneg
    have : (0 : ℚ) < Γ.delta C₁ := by exact_mod_cast hneg.delta_pos C₁
    have : (0 : ℚ) < Γ.delta C₂ := by exact_mod_cast hneg.delta_pos C₂
    positivity
  obtain ⟨d₁, d₂, dA, dB⟩ := eq_two_of_twoFork_bracket_nonneg (by exact_mod_cast h₁.1)
    (by exact_mod_cast h₂.1) h₃ (by exact_mod_cast hA.1) (by exact_mod_cast hB.1)
    (nonneg_of_mul_nonneg_right hv hpre)
  exact ⟨h₁.2 (by exact_mod_cast d₁), h₂.2 (by exact_mod_cast d₂),
    hA.2 (by exact_mod_cast dA), hB.2 (by exact_mod_cast dB)⟩

/-! ### The graphs of Fig. 2 -/

/-- In a negative definite rational tree with all boundary degrees `0`, a forked branch `C`
at `v` has nonpositive branch value over its determinant. -/
private theorem branchValue_div_nonpos {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {C : Finset V} (hC : Γ.IsForkedBranchAt v C) :
    Γ.branchValue v C / (Γ.delta C : ℚ) ≤ 0 := by
  obtain ⟨u, A, B, hF⟩ := hC
  rw [Γ.branchValue_eq_of_isForkedBranch hF (fun k _ => hΓ.genus_eq_zero k) (fun k _ => hβ k)]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hA, hB⟩ := hF.exists_spine
  have hA' : (2 : ℚ) ≤ Γ.delta A := by exact_mod_cast two_le_delta hΓ.two_le_weight hA
  have hB' : (2 : ℚ) ≤ Γ.delta B := by exact_mod_cast two_le_delta hΓ.two_le_weight hB
  have hC' : (0 : ℚ) < Γ.delta C := by exact_mod_cast hneg.delta_pos C
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hC'.le

/-- A forked branch at `v` is a component of `Γ - v`. -/
private theorem isComponent_of_isForkedBranchAt {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {v : V} {C : Finset V} (hC : Γ.IsForkedBranchAt v C) :
    Γ.IsComponentOfRemoveVertex v C :=
  let ⟨_, _, _, hF⟩ := hC; hF.isComponent

/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which has
Fig. 2(a) shape at `v`, and let `a` be its log discrepancy vector. Then `a v < 0`. -/
@[mmp "lem_fa3_fig2_left_negative"]
public theorem IsLogDiscrepancyVector.apply_neg_of_isFig2LeftShape {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} (hfig : Γ.IsFig2LeftShape v) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) :
    a v < 0 := by
  obtain ⟨hs, ht, hdeg, C₁, C₂, C₃, h12, h13, h23, hU, h1, h2, h3⟩ := hfig
  rw [ha.apply_eq_branchValue_of_isTree hneg hs ht v ![C₁, C₂, C₃]
      (fun i => by fin_cases i <;> first
        | exact h1.2.1 | exact isComponent_of_isForkedBranchAt h2
        | exact isComponent_of_isForkedBranchAt h3)
      (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm])
      (by rw [← hU]; ext x; simp [Fin.exists_fin_succ, or_assoc]),
    Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [Γ.branchValue_eq_one_of_isChainAttachedAtEnd hs h1 (fun k _ => hβ k),
    Γ.c_eq_of_hasSimpleEdges hs, hdeg, hΓ.genus_eq_zero, hβ]
  refine mul_neg_of_pos_of_neg (div_pos ?_ (by exact_mod_cast det_pos hneg)) ?_
  · rw [det_removeSet]; exact_mod_cast hneg.delta_pos _
  have l1 := one_div_delta_le_half hΓ.two_le_weight h1
  have l2 := branchValue_div_nonpos hΓ hneg hβ h2
  have l3 := branchValue_div_nonpos hΓ hneg hβ h3
  push_cast
  linarith

/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which has
Fig. 2(b) shape at `v`, and let `a` be its log discrepancy vector. Then `a v < 0`. -/
@[mmp "lem_fa3_fig2_right_negative"]
public theorem IsLogDiscrepancyVector.apply_neg_of_isFig2RightShape {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} (hfig : Γ.IsFig2RightShape v) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) :
    a v < 0 := by
  obtain ⟨hs, ht, hdeg, C₁, C₂, C₃, C₄, h12, h13, h14, h23, h24, h34, hU, h1, h2, h3, h4⟩ :=
    hfig
  rw [ha.apply_eq_branchValue_of_isTree hneg hs ht v ![C₁, C₂, C₃, C₄]
      (fun i => by fin_cases i <;> first
        | exact h1.2.1 | exact h2.2.1 | exact h3.2.1 | exact isComponent_of_isForkedBranchAt h4)
      (fun i j hij => by fin_cases i <;> fin_cases j <;> simp_all [disjoint_comm])
      (by rw [← hU]; ext x; simp [Fin.exists_fin_succ, or_assoc]),
    Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  rw [Γ.branchValue_eq_one_of_isChainAttachedAtEnd hs h1 (fun k _ => hβ k),
    Γ.branchValue_eq_one_of_isChainAttachedAtEnd hs h2 (fun k _ => hβ k),
    Γ.branchValue_eq_one_of_isChainAttachedAtEnd hs h3 (fun k _ => hβ k),
    Γ.c_eq_of_hasSimpleEdges hs, hdeg, hΓ.genus_eq_zero, hβ]
  refine mul_neg_of_pos_of_neg (div_pos ?_ (by exact_mod_cast det_pos hneg)) ?_
  · rw [det_removeSet]; exact_mod_cast hneg.delta_pos _
  have := one_div_delta_le_half hΓ.two_le_weight h1
  have := one_div_delta_le_half hΓ.two_le_weight h2
  have := one_div_delta_le_half hΓ.two_le_weight h3
  have := branchValue_div_nonpos hΓ hneg hβ h4
  push_cast
  linarith

/-! ### Boundaries on log canonical chains -/

/-- A function on `Fin s`, extended by zero to `ℕ`. -/
private def natExtend {s : ℕ} (F : Fin s → ℚ) (n : ℕ) : ℚ :=
  if h : n < s then F ⟨n, h⟩ else 0

private theorem natExtend_coe {s : ℕ} (F : Fin s → ℚ) (i : Fin s) :
    natExtend F i = F i := by
  simp [natExtend]

/-- Summing `F` against the adjacency of the chain on `Fin s` picks out the two neighbours. -/
private theorem sum_mul_adj {s : ℕ} (F : Fin s → ℚ) (i : Fin s) :
    ∑ t : Fin s, F t * (if (t : ℕ) + 1 = i ∨ (i : ℕ) + 1 = t then 1 else 0) =
      (if (i : ℕ) = 0 then 0 else natExtend F (i - 1)) + natExtend F (i + 1) := by
  have hsplit : ∀ t : Fin s, F t * (if (t : ℕ) + 1 = i ∨ (i : ℕ) + 1 = t then 1 else 0) =
      (if (t : ℕ) + 1 = i then F t else 0) + (if (t : ℕ) = i + 1 then F t else 0) := by
    intro t
    split_ifs <;> first | omega | simp
  rw [Finset.sum_congr rfl fun t _ => hsplit t, Finset.sum_add_distrib]
  congr 1
  · split_ifs with hi
    · exact Finset.sum_eq_zero fun t _ => if_neg (by omega)
    · rw [Finset.sum_eq_single ⟨i - 1, by omega⟩ (fun t _ ht => if_neg fun h =>
        ht (Fin.ext (by simp; omega))) (by simp), if_pos (by simp; omega)]
      simp [natExtend, show (i : ℕ) - 1 < s by omega]
  · unfold natExtend
    split_ifs with hlt
    · rw [Finset.sum_eq_single ⟨i + 1, hlt⟩ (fun t _ ht => if_neg fun h =>
        ht (Fin.ext h)) (by simp), if_pos rfl]
    · exact Finset.sum_eq_zero fun t _ => if_neg (by omega)

/-- Convexity of the chain recurrence: if `h 0 = 1` and `h i + h (i + 2) = W i h (i + 1)` with
`W i ≥ 2` and `h (i + 1) ≥ 0` for `i < m`, then `(m + 1) h m ≤ m h (m + 1) + 1`. -/
private theorem convex_bound (h W : ℕ → ℚ) (h0 : h 0 = 1) :
    ∀ m : ℕ, (∀ i < m, h i + h (i + 2) = W i * h (i + 1)) → (∀ i < m, 2 ≤ W i) →
      (∀ i < m, 0 ≤ h (i + 1)) → (m + 1) * h m ≤ m * h (m + 1) + 1
  | 0, _, _, _ => by simp [h0]
  | m + 1, hrec, hW, hnn => by
    have IH := convex_bound h W h0 m (fun i hi => hrec i (by omega)) (fun i hi => hW i (by omega))
      (fun i hi => hnn i (by omega))
    have key : h (m + 2) = W m * h (m + 1) - h m := by linarith [hrec m (by omega)]
    have hp : 0 ≤ ((m : ℚ) + 1) * (W m - 2) * h (m + 1) :=
      mul_nonneg (mul_nonneg (by positivity) (by linarith [hW m (by omega)])) (hnn m (by omega))
    rw [key]
    push_cast
    nlinarith

/-- The equation at an inner vertex `w_j` of weight `w ≥ 2`, `a_{j-1} + a_{j+1} = w a_j + 1`,
together with the convexity bounds `(j + 1) a_{j-1} ≤ j a_j + 1` and `(m + 1) a_{j+1} ≤ m a_j + 1`
of the two parts of lengths `j, m ≥ 1`, forces `j = m = 1` and `a_j = 0`: combined they give
`(j + 1)(m + 1) + (j + m + 2) a_j ≤ j + m + 2`. -/
private theorem eq_one_of_convex_bounds {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) {x y z w : ℚ}
    (hy : 0 ≤ y) (hw : 2 ≤ w) (hL : (j + 1) * x ≤ j * y + 1) (hR : (m + 1) * z ≤ m * y + 1)
    (hmid : x + z = w * y + 1) : j = 1 ∧ m = 1 ∧ y = 0 := by
  have hP : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have hQ : (1 : ℚ) ≤ m := by exact_mod_cast hm
  have hineq : ((j : ℚ) + 1) * (m + 1) + (j + m + 2) * y ≤ j + m + 2 := by
    have k1 := mul_le_mul_of_nonneg_left hL (show (0 : ℚ) ≤ m + 1 by linarith)
    have k2 := mul_le_mul_of_nonneg_left hR (show (0 : ℚ) ≤ j + 1 by linarith)
    have k3 : 0 ≤ ((j : ℚ) + 1) * (m + 1) * ((w - 2) * y) :=
      mul_nonneg (by positivity) (mul_nonneg (by linarith) hy)
    have k4 : ((j : ℚ) + 1) * (m + 1) * (x + z) = ((j : ℚ) + 1) * (m + 1) * (w * y + 1) := by
      rw [hmid]
    linarith
  have hjm : (j : ℚ) * m ≤ 1 := by nlinarith [mul_nonneg (show (0 : ℚ) ≤ j + m + 2 by linarith) hy]
  have hj1 : j = 1 := le_antisymm (by exact_mod_cast (show (j : ℚ) ≤ 1 by nlinarith)) hj
  have hm1 : m = 1 := le_antisymm (by exact_mod_cast (show (m : ℚ) ≤ 1 by nlinarith)) hm
  subst hj1 hm1
  norm_num at hineq
  exact ⟨rfl, rfl, le_antisymm (by linarith) hy⟩

private theorem sum_mul_sub_degree_eq {s' : ℕ} (G B W : ℕ → ℚ) (hGs : G (s' + 1) = 0)
    (heq : ∀ n < s' + 1, (if n = 0 then 0 else G (n - 1)) + G (n + 1) - W n * G n =
      B n + (if n = 0 then 0 else 1) + (if n + 1 < s' + 1 then 1 else 0) - 2) :
    ∑ n ∈ range (s' + 1), G n * (W n - ((if n = 0 then 0 else 1) +
      (if n + 1 < s' + 1 then 1 else 0))) = 2 - ∑ n ∈ range (s' + 1), B n := by
  have hsum := Finset.sum_congr rfl fun n (hn : n ∈ range (s' + 1)) => heq n (by simpa using hn)
  have h1 : ∑ n ∈ range (s' + 1), (if n = 0 then 0 else G (n - 1)) =
      ∑ n ∈ range (s' + 1), G n * (if n + 1 < s' + 1 then 1 else 0) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right, add_zero, lt_irrefl,
      mul_zero]
    exact Finset.sum_congr rfl fun n hn => by
      rw [if_pos (by simp at hn; omega), mul_one]
  have h2 : ∑ n ∈ range (s' + 1), G (n + 1) =
      ∑ n ∈ range (s' + 1), G n * (if n = 0 then 0 else 1) := by
    rw [Finset.sum_range_succ, hGs, Finset.sum_range_succ']
    simp
  have hA : ∑ n ∈ range (s' + 1), (if n = 0 then (0 : ℚ) else 1) = s' := by
    rw [Finset.sum_range_succ']; simp
  have hA' : ∑ n ∈ range (s' + 1), (if n + 1 < s' + 1 then (1 : ℚ) else 0) = s' := by
    rw [Finset.sum_range_succ, Finset.sum_congr rfl fun n hn => if_pos (by simp at hn; omega)]
    simp
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, h1, h2, hA, hA',
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hc : ∀ n, G n * W n = W n * G n := fun n => mul_comm _ _
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, hc]
  push_cast at hsum
  linarith

private theorem mul_sub_degree_nonneg {s' : ℕ} (G W : ℕ → ℚ) (hW : ∀ n < s' + 1, 2 ≤ W n)
    (hG : ∀ n, 0 ≤ G n) : ∀ n ∈ range (s' + 1), 0 ≤ G n * (W n - ((if n = 0 then 0 else 1) +
      (if n + 1 < s' + 1 then 1 else 0))) := by
  intro n hn
  have := hW n (by simpa using hn)
  refine mul_nonneg (hG n) ?_
  split_ifs <;> linarith

private theorem eq_one_of_recurrence_middle {s' j : ℕ} {G B W : ℕ → ℚ}
    (hW : ∀ n < s' + 1, 2 ≤ W n) (hG : ∀ n, 0 ≤ G n) (hGs : ∀ n, s' + 1 ≤ n → G n = 0)
    (heq : ∀ n < s' + 1, (if n = 0 then 0 else G (n - 1)) + G (n + 1) - W n * G n =
      B n + (if n = 0 then 0 else 1) + (if n + 1 < s' + 1 then 1 else 0) - 2)
    (hj : j < s' + 1) (hj0 : j ≠ 0) (hjs : ¬j + 1 = s' + 1)
    (hBn : ∀ n < s' + 1, B n = if n = j then 1 else 0) :
    j = 1 ∧ s' - j = 1 ∧ G j = 0 := by
  have hBj : ∀ n < s' + 1, n ≠ j → B n = 0 := fun n hn h => by rw [hBn n hn, if_neg h]
  have hL := convex_bound (fun i => if i = 0 then 1 else G (i - 1)) W (by simp) j
    (by
      intro i hi
      have := heq i (by omega)
      rw [hBj i (by omega) (by omega), if_pos (show i + 1 < s' + 1 by omega)] at this
      simp only [show i + 2 ≠ 0 by omega, show i + 1 ≠ 0 by omega, ↓reduceIte,
        show i + 2 - 1 = i + 1 by omega, show i + 1 - 1 = i by omega]
      split_ifs at this ⊢ with h0
      · subst h0; linarith
      · linarith)
    (fun i hi => hW i (by omega)) (fun i hi => by simp [hG])
  simp only [hj0, ↓reduceIte, show j + 1 ≠ 0 by omega, show j + 1 - 1 = j by omega] at hL
  set m := s' - j with hm
  have hR := convex_bound (fun i => if i = 0 then 1 else G (s' + 1 - i))
    (fun i => W (s' - i)) (by simp) m
    (by
      intro i hi
      have hn := heq (s' - i) (by omega)
      rw [hBj (s' - i) (by omega) (by omega)] at hn
      simp only [show s' - i ≠ 0 by omega, ↓reduceIte] at hn
      simp only [show i + 2 ≠ 0 by omega, show i + 1 ≠ 0 by omega, ↓reduceIte,
        show s' + 1 - (i + 2) = s' - i - 1 by omega, show s' + 1 - (i + 1) = s' - i by omega]
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp only [↓reduceIte, Nat.sub_zero, lt_irrefl, hGs (s' + 1) le_rfl] at hn ⊢
        linarith
      · rw [if_pos (show s' - i + 1 < s' + 1 by omega),
          show s' - i + 1 = s' + 1 - i by omega] at hn
        rw [if_neg (by omega)]
        linarith)
    (fun i hi => hW _ (by omega)) (fun i hi => by simp [hG])
  simp only [show m ≠ 0 by omega, show m + 1 ≠ 0 by omega, ↓reduceIte,
    show s' + 1 - m = j + 1 by omega, show s' + 1 - (m + 1) = j by omega] at hR
  have hmid := heq j hj
  rw [hBn j hj, if_pos rfl, if_pos (show j + 1 < s' + 1 by omega)] at hmid
  simp only [hj0, ↓reduceIte] at hmid
  exact eq_one_of_convex_bounds (Nat.one_le_iff_ne_zero.2 hj0)
    (show 1 ≤ m by omega) (hG j) (hW j hj) hL hR (by linarith)

private theorem boundary_middle_of_recurrence {s' j : ℕ} {G B W : ℕ → ℚ}
    (hW : ∀ n < s' + 1, 2 ≤ W n) (hG : ∀ n, 0 ≤ G n) (hGs : ∀ n, s' + 1 ≤ n → G n = 0)
    (heq : ∀ n < s' + 1, (if n = 0 then 0 else G (n - 1)) + G (n + 1) - W n * G n =
      B n + (if n = 0 then 0 else 1) + (if n + 1 < s' + 1 then 1 else 0) - 2)
    (hj : j < s' + 1) (hj0 : j ≠ 0) (hjs : ¬j + 1 = s' + 1)
    (hBn : ∀ n < s' + 1, B n = if n = j then 1 else 0) :
    s' + 1 = 3 ∧ ∀ n < s' + 1, B n = (if n = 1 then 1 else 0) ∧ (n ≠ 1 → W n = 2) := by
  have hBj : ∀ n < s' + 1, n ≠ j → B n = 0 := fun n hn h => by rw [hBn n hn, if_neg h]
  have hmid := heq j hj
  rw [hBn j hj, if_pos rfl, if_pos (show j + 1 < s' + 1 by omega)] at hmid
  simp only [hj0, ↓reduceIte] at hmid
  obtain ⟨hj1, hm1, hx0⟩ := eq_one_of_recurrence_middle hW hG hGs heq hj hj0 hjs hBn
  subst hj1
  have hs3 : s' = 2 := by omega
  subst hs3
  have e0 := heq 0 (by omega)
  have e2 := heq 2 (by omega)
  rw [hBj 0 (by omega) (by omega)] at e0
  rw [hBj 2 (by omega) (by omega), hGs 3 le_rfl] at e2
  norm_num [hx0] at e0 e2 hmid
  have hW0 := hW 0 (by omega)
  have hW2 := hW 2 (by omega)
  have hG0 := hG 0
  have hG2 := hG 2
  have h0' : 2 * G 0 ≤ 1 := by nlinarith
  have h2' : 2 * G 2 ≤ 1 := by nlinarith
  refine ⟨rfl, fun n hn => ⟨by rw [hBn n hn], fun hn1 => ?_⟩⟩
  interval_cases n
  · nlinarith
  · exact absurd rfl hn1
  · nlinarith

private theorem one_le_ends_of_recurrence {s' : ℕ} {G B W : ℕ → ℚ} (hs1 : s' ≠ 0)
    (hW : ∀ n < s' + 1, 2 ≤ W n) (hG : ∀ n, 0 ≤ G n) (hGs : ∀ n, s' + 1 ≤ n → G n = 0)
    {bN : ℕ → ℕ} (hB : ∀ n < s' + 1, B n = bN n)
    (heq : ∀ n < s' + 1, (if n = 0 then 0 else G (n - 1)) + G (n + 1) - W n * G n =
      B n + (if n = 0 then 0 else 1) + (if n + 1 < s' + 1 then 1 else 0) - 2)
    (hN2 : ∑ n ∈ range (s' + 1), bN n = 2) : 1 ≤ bN 0 ∧ 1 ≤ bN s' := by
  have hBsum : ∑ n ∈ range (s' + 1), B n = ((∑ n ∈ range (s' + 1), bN n : ℕ) : ℚ) := by
    push_cast
    exact Finset.sum_congr rfl fun n hn => hB n (by simpa using hn)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (mul_sub_degree_nonneg G W hW hG)).1 (by
    rw [sum_mul_sub_degree_eq G B W (hGs (s' + 1) le_rfl) heq, hBsum, hN2]; norm_num)
  have hG0 : G 0 = 0 := by
    have := hzero 0 (by simp)
    simp only [↓reduceIte, show 0 + 1 < s' + 1 by omega] at this
    exact (mul_eq_zero.1 this).resolve_right (by linarith [hW 0 (by omega)])
  have hGs' : G s' = 0 := by
    have := hzero s' (by simp)
    simp only [hs1, ↓reduceIte, lt_irrefl] at this
    exact (mul_eq_zero.1 this).resolve_right (by linarith [hW s' (by omega)])
  constructor
  · have e0 := heq 0 (by omega)
    simp only [↓reduceIte, show 0 + 1 < s' + 1 by omega, hG0, mul_zero, hB 0 (by omega)] at e0
    have := hG 1
    have : (1 : ℚ) ≤ bN 0 := by linarith
    exact_mod_cast this
  · have e1 := heq s' (by omega)
    simp only [hs1, ↓reduceIte, lt_irrefl, hGs', mul_zero, hB s' (by omega),
      hGs (s' + 1) le_rfl] at e1
    have := hG (s' - 1)
    have : (1 : ℚ) ≤ bN s' := by linarith
    exact_mod_cast this

private theorem boundary_two_of_recurrence {s' : ℕ} {G B W : ℕ → ℚ}
    (hW : ∀ n < s' + 1, 2 ≤ W n) (hG : ∀ n, 0 ≤ G n) (hGs : ∀ n, s' + 1 ≤ n → G n = 0)
    {bN : ℕ → ℕ} (hB : ∀ n < s' + 1, B n = bN n)
    (heq : ∀ n < s' + 1, (if n = 0 then 0 else G (n - 1)) + G (n + 1) - W n * G n =
      B n + (if n = 0 then 0 else 1) + (if n + 1 < s' + 1 then 1 else 0) - 2)
    (hN2 : ∑ n ∈ range (s' + 1), bN n = 2) :
    (2 ≤ s' + 1 ∧ ∀ n < s' + 1,
      B n = (if n = 0 then 1 else 0) + (if n + 1 = s' + 1 then 1 else 0)) ∨
    (s' + 1 = 1 ∧ ∀ n < s' + 1, B n = 2) := by
  by_cases hs1 : s' = 0
  · subst hs1
    refine Or.inr ⟨rfl, fun n hn => ?_⟩
    obtain rfl : n = 0 := by omega
    rw [hB 0 hn]
    have : ∑ n ∈ range (0 + 1), bN n = bN 0 := by simp
    exact_mod_cast (by omega : bN 0 = 2)
  refine Or.inl ⟨by omega, ?_⟩
  obtain ⟨hb0, hbs⟩ := one_le_ends_of_recurrence hs1 hW hG hGs hB heq hN2
  have hsub : ∑ n ∈ range (s' + 1), bN n =
      bN 0 + bN s' + ∑ n ∈ ((range (s' + 1)).erase 0).erase s', bN n := by
    have h1 := (Finset.add_sum_erase (range (s' + 1)) bN (show 0 ∈ range (s' + 1) by simp)).symm
    have h2 := Finset.add_sum_erase ((range (s' + 1)).erase 0) bN (show s' ∈ _ by simp [hs1])
    omega
  have hrest : ∑ n ∈ ((range (s' + 1)).erase 0).erase s', bN n = 0 := by omega
  intro n hn
  rw [hB n hn]
  by_cases h0 : n = 0
  · subst h0
    rw [if_pos rfl, if_neg (by omega)]
    norm_num
    exact_mod_cast (by omega : bN 0 = 1)
  by_cases hs : n + 1 = s' + 1
  · rw [show n = s' by omega, if_neg hs1, if_pos rfl]
    norm_num
    exact_mod_cast (by omega : bN s' = 1)
  have hs'' : n ≠ s' := by omega
  have := (Finset.sum_eq_zero_iff.1 hrest) n (by simp [h0, hn, hs''])
  rw [if_neg h0, if_neg hs, this]
  norm_num

/-- The case analysis of FA 3.3.1 for the extended sequences `G = a`, `B = β`, `W = n`. -/
private theorem boundary_cases_of_recurrence {s : ℕ} (hs : 0 < s) (G B W : ℕ → ℚ)
    (hW : ∀ n < s, 2 ≤ W n)
    (hG : ∀ n, 0 ≤ G n) (hGs : ∀ n, s ≤ n → G n = 0) (bN : ℕ → ℕ)
    (hB : ∀ n < s, B n = bN n) (hpos : ∃ n < s, 0 < B n)
    (heq : ∀ n < s, (if n = 0 then 0 else G (n - 1)) + G (n + 1) - W n * G n =
      B n + (if n = 0 then 0 else 1) + (if n + 1 < s then 1 else 0) - 2) :
    ((∀ n < s, B n = if n = 0 then 1 else 0) ∨ (∀ n < s, B n = if n + 1 = s then 1 else 0)) ∨
    (s = 3 ∧ ∀ n < s, B n = (if n = 1 then 1 else 0) ∧ (n ≠ 1 → W n = 2)) ∨
    (2 ≤ s ∧ ∀ n < s, B n = (if n = 0 then 1 else 0) + (if n + 1 = s then 1 else 0)) ∨
    (s = 1 ∧ ∀ n < s, B n = 2) := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hdeg := sum_mul_sub_degree_eq G B W (hGs (s' + 1) le_rfl) heq
  have hBsum : ∑ n ∈ range (s' + 1), B n = ((∑ n ∈ range (s' + 1), bN n : ℕ) : ℚ) := by
    push_cast
    exact Finset.sum_congr rfl fun n hn => hB n (by simpa using hn)
  set N := ∑ n ∈ range (s' + 1), bN n with hN
  have hle : N ≤ 2 := by
    have := Finset.sum_nonneg (mul_sub_degree_nonneg G W hW hG)
    exact_mod_cast (show (N : ℚ) ≤ 2 by linarith)
  obtain ⟨j, hj, hjpos⟩ := hpos
  have hbj : 1 ≤ bN j := by
    rw [hB j hj] at hjpos
    exact_mod_cast hjpos
  have hsplit : N = bN j + ∑ n ∈ (range (s' + 1)).erase j, bN n :=
    (Finset.add_sum_erase _ _ (by simpa using hj)).symm
  rcases (show N = 1 ∨ N = 2 by omega) with hN1 | hN2
  · have hrest : ∑ n ∈ (range (s' + 1)).erase j, bN n = 0 := by omega
    have hbj1 : bN j = 1 := by omega
    have hBn : ∀ n < s' + 1, B n = if n = j then 1 else 0 := by
      intro n hn
      rw [hB n hn]
      split_ifs with h
      · subst h; simp [hbj1]
      · have := (Finset.sum_eq_zero_iff.1 hrest) n (by simp [h, hn])
        simp [this]
    by_cases hj0 : j = 0
    · exact Or.inl (Or.inl fun n hn => by rw [hBn n hn, hj0])
    by_cases hjs : j + 1 = s' + 1
    · refine Or.inl (Or.inr fun n hn => ?_)
      rw [hBn n hn]
      congr 1
      apply propext
      omega
    exact Or.inr (Or.inl (boundary_middle_of_recurrence hW hG hGs heq hj hj0 hjs hBn))
  · exact Or.inr (Or.inr (boundary_two_of_recurrence hW hG hGs hB heq hN2))

private theorem IsChainOrder.natExtend_recurrence {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V} (he : Γ.IsChainOrder e) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) {G B W : ℕ → ℚ}
    (hGdef : G = natExtend (fun i => a (e i))) (hBdef : B = natExtend (fun i => Γ.boundary (e i)))
    (hWdef : W = natExtend (fun i => (Γ.weight (e i) : ℚ))) (i : Fin s) :
    (if (i : ℕ) = 0 then 0 else G (i - 1)) + G (i + 1) - W i * G i =
      B i + (if (i : ℕ) = 0 then 0 else 1) + (if (i : ℕ) + 1 < s then 1 else 0) - 2 := by
  have hmat : ∀ i t : Fin s, (Γ.matrix (e t) (e i) : ℚ) =
      (if (t : ℕ) + 1 = i ∨ (i : ℕ) + 1 = t then 1 else 0) -
        (if t = i then (Γ.weight (e i) : ℚ) else 0) := by
    intro i t
    by_cases h : t = i
    · subst h; simp [WeightedGraph.matrix]
    · simp only [WeightedGraph.matrix, Matrix.of_apply, e.injective.ne h, ↓reduceIte, h,
        he.edgeWeight_eq, sub_zero]
      split_ifs <;> simp
  have h := ha (e i)
  rw [← e.sum_comp (fun k => a k * (Γ.matrix k (e i) : ℚ))] at h
  simp only [hmat i, mul_sub, Finset.sum_sub_distrib] at h
  rw [sum_mul_adj (fun t => a (e t)) i] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  have hc : Γ.c (e i) = 2 - Γ.boundary (e i) -
      ((if (i : ℕ) = 0 then 0 else 1) + (if (i : ℕ) + 1 < s then 1 else 0)) := by
    unfold WeightedGraph.c
    rw [he.genus_eq_zero i, Finset.sum_erase _ (by simp [Γ.edgeWeight_self]),
      ← e.sum_comp (fun k => (Γ.edgeWeight (e i) k : ℚ))]
    have h1 : ∑ t, (Γ.edgeWeight (e i) (e t) : ℚ) =
        ∑ t : Fin s, 1 * (if (t : ℕ) + 1 = i ∨ (i : ℕ) + 1 = t then (1 : ℚ) else 0) := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [he.edgeWeight_eq, one_mul]
      by_cases h1 : (i : ℕ) + 1 = t
      · rw [if_pos (Or.inl h1), if_pos (Or.inr h1)]; simp
      by_cases h2 : (t : ℕ) + 1 = i
      · rw [if_pos (Or.inr h2), if_pos (Or.inl h2)]; simp
      rw [if_neg (by tauto), if_neg (by tauto)]; simp
    rw [h1, sum_mul_adj (fun _ : Fin s => (1 : ℚ)) i]
    simp only [natExtend, show (i : ℕ) - 1 < s by omega]
    split_ifs <;> simp
  rw [hc] at h
  simp only [hGdef, hBdef, hWdef, natExtend_coe]
  linarith

/-- Let `Γ` be a negative definite rational tree which is a weighted chain enumerated by
`e : Fin s ≃ V`, `s ≥ 1`, with integral boundary degrees not all zero, and let `a` be its log
discrepancy vector, with `a k ≥ 0` for all `k`. Then either (a) `β` is `1` at one end and `0`
elsewhere; or (b) `s = 3`, `β` is `1` at the middle vertex and `0` elsewhere, and both ends
have weight `2`; or (c) `s ≥ 2` and `β` is `1` at both ends and `0` elsewhere; or (d) `s = 1`
and `β = 2` at the single vertex. -/
@[mmp "lem_fa3_boundary_chain_cases"]
public theorem IsLogDiscrepancyVector.boundary_cases_of_isChainOrder {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    {s : ℕ} (hs : 0 < s) {e : Fin s ≃ V} (he : Γ.IsChainOrder e)
    (hβ : ∀ j, ∃ n : ℕ, Γ.boundary j = n) (hpos : ∃ j, 0 < Γ.boundary j)
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (hnonneg : ∀ k, 0 ≤ a k) :
    ((∀ i : Fin s, Γ.boundary (e i) = if (i : ℕ) = 0 then 1 else 0) ∨
      (∀ i : Fin s, Γ.boundary (e i) = if (i : ℕ) + 1 = s then 1 else 0)) ∨
    (s = 3 ∧ ∀ i : Fin s, Γ.boundary (e i) = (if (i : ℕ) = 1 then 1 else 0) ∧
      ((i : ℕ) ≠ 1 → Γ.weight (e i) = 2)) ∨
    (2 ≤ s ∧ ∀ i : Fin s, Γ.boundary (e i) =
      (if (i : ℕ) = 0 then 1 else 0) + (if (i : ℕ) + 1 = s then 1 else 0)) ∨
    (s = 1 ∧ ∀ i : Fin s, Γ.boundary (e i) = 2) := by
  obtain ⟨G, hGdef⟩ : ∃ G, G = natExtend (fun i => a (e i)) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = natExtend (fun i => Γ.boundary (e i)) := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W, W = natExtend (fun i => (Γ.weight (e i) : ℚ)) := ⟨_, rfl⟩
  have heqF := he.natExtend_recurrence ha hGdef hBdef hWdef
  have hcore := boundary_cases_of_recurrence hs G B W
    (fun n hn => by
      rw [hWdef, natExtend, dif_pos hn]; exact_mod_cast hΓ.two_le_weight _)
    (fun n => by rw [hGdef, natExtend]; split_ifs <;> simp [hnonneg])
    (fun n hn => by rw [hGdef, natExtend, dif_neg (not_lt.2 hn)])
    (fun n => if h : n < s then (hβ (e ⟨n, h⟩)).choose else 0)
    (fun n hn => by
      rw [hBdef, natExtend, dif_pos hn, dif_pos hn]; exact (hβ (e ⟨n, hn⟩)).choose_spec)
    (by
      obtain ⟨j, hj⟩ := hpos
      exact ⟨e.symm j, (e.symm j).2, by simpa [hBdef, natExtend_coe] using hj⟩)
    (fun n hn => by simpa using heqF ⟨n, hn⟩)
  have hBi : ∀ i : Fin s, Γ.boundary (e i) = B i := fun i => by rw [hBdef, natExtend_coe]
  have hWi : ∀ i : Fin s, (Γ.weight (e i) : ℚ) = W i := fun i => by rw [hWdef, natExtend_coe]
  rcases hcore with (h | h) | ⟨h3, h⟩ | ⟨h2, h⟩ | ⟨h1, h⟩
  · exact Or.inl (Or.inl fun i => (hBi i).trans (h i i.2))
  · exact Or.inl (Or.inr fun i => (hBi i).trans (h i i.2))
  · refine Or.inr (Or.inl ⟨h3, fun i => ⟨(hBi i).trans (h i i.2).1, fun hi => ?_⟩⟩)
    exact_mod_cast (hWi i).trans ((h i i.2).2 hi)
  · exact Or.inr (Or.inr (Or.inl ⟨h2, fun i => (hBi i).trans (h i i.2)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h1, fun i => (hBi i).trans (h i i.2)⟩))

end MMP.Flips.WeightedGraph
