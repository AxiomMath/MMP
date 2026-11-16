/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import MMP.Combinatorics.WeightedGraph.Shapes

/-!
# Determinants and branch values of weighted trees (FA 3.1.7, 3.2)

* `Δ(S₁ ⊔ S₂) = Δ(S₁) Δ(S₂)` when no edge joins `S₁` and `S₂` (FA 3.1.7);
* the branch value of a chain attached at an end, with `β = 0`, is `1` (FA 3.2.1–3.2.2: the only
  bonus vertex is the simple end);
* the branch value of a forked branch with arms `Γ_A`, `Γ_B` and `p = β = 0` is
  `1 - (Δ_A - 1)(Δ_B - 1)` (FA 3.2.5, 3.2.7).

## Main results

* `MMP.Flips.WeightedGraph.delta_union_of_edgeWeight_eq_zero`
* `MMP.Flips.WeightedGraph.delta_biUnion_eq_prod`: `Δ(⋃ C_i) = ∏ Δ(C_i)` for disjoint components
  of `Γ - v`
* `MMP.Flips.WeightedGraph.delta_sdiff_eq_prod_of_isStar`: `Δ(Γ - v) = ∏ Δ_i` for a star
* `MMP.Flips.WeightedGraph.c_eq_of_hasSimpleEdges`: `c_j = 2 - 2 p_j - β_j - deg(v_j)`
* `MMP.Flips.WeightedGraph.branchValue_eq_one_of_isChainAttachedAtEnd`
* `MMP.Flips.WeightedGraph.branchValue_eq_of_isForkedBranch`

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.1.7,
  3.2.1, 3.2.2, 3.2.5, 3.2.7
-/

@[expose] public noncomputable section

open Finset

namespace MMP.Flips.WeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V)

/-! ### Helper lemmas: components, chains and paths -/

/-- The vertex removed does not lie in a component of `Γ - v`. -/
theorem notMem_of_isComponentOfRemoveVertex {v : V} {C : Finset V}
    (hC : Γ.IsComponentOfRemoveVertex v C) : v ∉ C := by
  obtain ⟨c, hc⟩ := hC
  intro hv
  obtain ⟨w, -, hw⟩ : v ∈ Subtype.val '' c.supp := hc ▸ hv
  simpa [hw] using w.2

/-- **FA 3.1.7.** If `S = S₁ ⊔ S₂` with `m_{jk} = 0` for all `v_j ∈ S₁`, `v_k ∈ S₂`, then
`Δ(S) = Δ(S₁) Δ(S₂)`. -/
@[mmp "lem_fa3_graph_determinant_multiplicative"]
theorem delta_union_of_edgeWeight_eq_zero {S₁ S₂ : Finset V} (hd : Disjoint S₁ S₂)
    (h : ∀ j ∈ S₁, ∀ k ∈ S₂, Γ.edgeWeight j k = 0) :
    Γ.delta (S₁ ∪ S₂) = Γ.delta S₁ * Γ.delta S₂ := by
  let e := Equiv.Finset.union S₁ S₂ hd
  unfold delta det
  rw [← Matrix.det_reindex_self e.symm]
  have : Matrix.reindex e.symm e.symm (-(Γ.restrict (S₁ ∪ S₂)).matrix) =
      Matrix.fromBlocks (-(Γ.restrict S₁).matrix) 0 0 (-(Γ.restrict S₂).matrix) := by
    ext (i|i) (j|j) <;>
      simp only [Matrix.reindex_apply, Equiv.symm_symm, Matrix.submatrix_apply, Matrix.neg_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, e, Equiv.Finset.union_inl, Equiv.Finset.union_inr, matrix,
        Matrix.of_apply, restrict, Matrix.zero_apply]
    · simp only [Subtype.mk.injEq, Subtype.coe_inj]
    · have hij : (i : V) ≠ j := fun hij => Finset.disjoint_left.mp hd i.2 (hij ▸ j.2)
      simp [Subtype.ext_iff, hij, h i i.2 j j.2]
    · have hij : (i : V) ≠ j := fun hij => Finset.disjoint_left.mp hd j.2 (hij ▸ i.2)
      simp [Subtype.ext_iff, hij, Γ.edgeWeight_symm i j, h j j.2 i i.2]
    · simp only [Subtype.mk.injEq, Subtype.coe_inj]
  rw [this, Matrix.det_fromBlocks_zero₂₁]

/-- A vertex of a component `C` of `Γ - v` has no edge to a vertex outside `C ∪ {v}`. -/
theorem edgeWeight_eq_zero_of_isComponentOfRemoveVertex {v : V} {C : Finset V}
    (hC : Γ.IsComponentOfRemoveVertex v C) {k j : V} (hk : k ∈ C) (hj : j ∉ C) (hjv : j ≠ v) :
    Γ.edgeWeight k j = 0 := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨k', hk'c, rfl⟩ : k ∈ Subtype.val '' c.supp := hc ▸ hk
  by_contra hne
  have hjm : j ∈ (univ \ {v} : Finset V) := by simp [hjv]
  have hadj : (Γ.removeVertex v).underlyingGraph.Adj k' ⟨j, hjm⟩ :=
    ⟨fun h => hj (by subst h; exact hk), Nat.pos_of_ne_zero hne⟩
  refine hj (show j ∈ (C : Set V) from hc ▸ ⟨⟨j, hjm⟩, ?_, rfl⟩)
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hk'c ⊢
  rw [← hk'c, SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj]

/-- **FA 3.1.7 for components of `Γ - v`.** `Δ` is multiplicative over a family of pairwise
disjoint components of `Γ - v`: no edge joins two of them, so FA 3.1.7 applies one at a time. -/
theorem delta_biUnion_eq_prod {v : V} {ι : Type*} [DecidableEq ι] {C : ι → Finset V}
    (hC : ∀ i, Γ.IsComponentOfRemoveVertex v (C i))
    (hdisj : Pairwise fun i j => Disjoint (C i) (C j)) (s : Finset ι) :
    Γ.delta (s.biUnion C) = ∏ i ∈ s, Γ.delta (C i) := by
  induction s using Finset.induction_on with
  | empty => simp [Γ.delta_empty]
  | insert i s hi ih =>
    rw [biUnion_insert, prod_insert hi, ← ih]
    have hd : Disjoint (C i) (s.biUnion C) :=
      (disjoint_biUnion_right _ _ _).mpr fun l hl => hdisj fun h => hi (h ▸ hl)
    exact Γ.delta_union_of_edgeWeight_eq_zero hd fun j hj k hk =>
      Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex (hC i) hj (disjoint_right.mp hd hk)
        fun h => by
          obtain ⟨l, -, hl⟩ := mem_biUnion.mp hk
          exact Γ.notMem_of_isComponentOfRemoveVertex (hC l) (h ▸ hl)

/-- For a star with arms `Γ_1, …, Γ_N` at `v`, `Δ(Γ - v) = Δ(Γ_1) ⋯ Δ(Γ_N)`: the arms are
pairwise disjoint components of `Γ - v` covering it, so `delta_biUnion_eq_prod` applies. -/
theorem delta_sdiff_eq_prod_of_isStar {v : V} {N : ℕ} {arms : Fin N → Finset V}
    (hstar : Γ.IsStar v arms) : Γ.delta (univ \ {v}) = ∏ i, Γ.delta (arms i) := by
  rw [← hstar.biUnion_eq, Γ.delta_biUnion_eq_prod hstar.isComponent hstar.pairwise_disjoint]

/-- The number of neighbours of `i` among `0, …, s - 1` in the chain on `ℕ`. -/
private theorem sum_range_ite_succ_or_succ (s i : ℕ) :
    ∑ j ∈ range s, (if i + 1 = j ∨ j + 1 = i then 1 else 0 : ℕ) =
      (if 0 < i ∧ i - 1 < s then 1 else 0) + (if i + 1 < s then 1 else 0) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

omit [DecidableEq V] in
/-- Consecutive vertices of a chain are adjacent in `Γ`. -/
private theorem adj_of_isChainOrder {C : Finset V} {s : ℕ} {e : Fin s ≃ C}
    (he : (Γ.restrict C).IsChainOrder e) (t : ℕ) (ht : t + 1 < s) :
    Γ.underlyingGraph.Adj (e ⟨t, by omega⟩ : V) (e ⟨t + 1, ht⟩) := by
  have hw := he.edgeWeight_eq ⟨t, by omega⟩ ⟨t + 1, ht⟩
  simp only [true_or, ↓reduceIte] at hw
  refine ⟨fun h => ?_, ?_⟩
  · have := e.injective (Subtype.ext h)
    simp [Fin.ext_iff] at this
  · change 0 < (Γ.restrict C).edgeWeight _ _
    rw [hw]
    exact one_pos

/-- In a graph with simple edges, `c_j = 2 - 2 p_j - β_j - deg(v_j)`. -/
theorem c_eq_of_hasSimpleEdges (hs : Γ.HasSimpleEdges) (j : V) :
    Γ.c j = 2 - 2 * Γ.genus j - Γ.boundary j - Γ.degree j := by
  unfold c degree
  congr 1
  rw [Finset.card_filter, Finset.sum_erase _ (by simp [Γ.edgeWeight_self])]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j
  · subst hk
    simp [Γ.edgeWeight_self]
  · rcases Nat.eq_zero_or_pos (Γ.edgeWeight j k) with h0 | hpos
    · simp [h0]
    · simp [hk, (hs j k ⟨Ne.symm hk, hpos⟩).2]

/-- The numbers `c_k(Γ)` on a chain `C` attached to `v` at its end `e 0` (a component of `Γ - v`,
with simple edges and `β = 0` on `C`): `1` at the far end, `0` elsewhere. -/
private theorem c_of_isChainOrder (hs : Γ.HasSimpleEdges) {v : V} {C : Finset V}
    (hcomp : Γ.IsComponentOfRemoveVertex v C) {s : ℕ} (hs0 : 0 < s) (e : Fin s ≃ C)
    (he : (Γ.restrict C).IsChainOrder e) (hadj : Γ.underlyingGraph.Adj v (e ⟨0, hs0⟩))
    (huniq : ∀ w ∈ C, Γ.underlyingGraph.Adj v w → w = e ⟨0, hs0⟩)
    (hβ : ∀ k ∈ C, Γ.boundary k = 0) (i : Fin s) :
    Γ.c (e i) = if (i : ℕ) + 1 = s then 1 else 0 := by
  have hvC := Γ.notMem_of_isComponentOfRemoveVertex hcomp
  have hkC : (e i : V) ∈ C := (e i).2
  have hv : Γ.edgeWeight (e i) v = if (i : ℕ) = 0 then 1 else 0 := by
    split_ifs with hi
    · have : i = ⟨0, hs0⟩ := Fin.ext hi
      rw [Γ.edgeWeight_symm, this]
      exact (hs _ _ hadj).2
    · rw [Γ.edgeWeight_symm]
      by_contra hne
      have hadj' : Γ.underlyingGraph.Adj v (e i) :=
        ⟨fun h => hvC (h ▸ hkC), Nat.pos_of_ne_zero hne⟩
      have := e.injective (Subtype.ext (huniq _ hkC hadj'))
      exact hi (by rw [this])
  have hCsum : ∑ j ∈ C, Γ.edgeWeight (e i) j =
      (if 0 < (i : ℕ) ∧ (i : ℕ) - 1 < s then 1 else 0) +
        (if (i : ℕ) + 1 < s then 1 else 0) := by
    rw [← sum_range_ite_succ_or_succ, ← Finset.sum_coe_sort C,
      ← e.sum_comp (fun j : C => Γ.edgeWeight (e i) j),
      ← Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) + 1 = j ∨ j + 1 = (i : ℕ) then 1 else 0)]
    exact Finset.sum_congr rfl fun i' _ => he.edgeWeight_eq i i'
  have hsum : ∑ j ∈ univ.erase (e i : V), Γ.edgeWeight (e i) j =
      1 + (if (i : ℕ) + 1 < s then 1 else 0) := by
    rw [Finset.sum_erase _ (Γ.edgeWeight_self _), ← Finset.sum_add_sum_compl C, hCsum,
      Finset.sum_eq_single_of_mem v (by simpa using hvC) (fun j hj hjv =>
        Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex hcomp hkC (by simpa using hj) hjv), hv]
    have := i.2
    split_ifs <;> omega
  have hsumQ : (∑ j ∈ univ.erase (e i : V), (Γ.edgeWeight (e i) j : ℚ)) =
      ((1 + (if (i : ℕ) + 1 < s then 1 else 0) : ℕ) : ℚ) := by
    rw [← hsum]
    push_cast
    rfl
  unfold c
  rw [show Γ.genus (e i) = 0 from he.genus_eq_zero i, hβ _ hkC, hsumQ]
  have := i.2
  split_ifs <;> first | omega | (push_cast; norm_num)

/-- Summing `g k * c_k(Γ)` over a chain attached at an end picks out the far end. -/
private theorem sum_mul_c_of_isChainOrder (hs : Γ.HasSimpleEdges) {v : V} {C : Finset V}
    (hcomp : Γ.IsComponentOfRemoveVertex v C) {s : ℕ} (hs0 : 0 < s) (e : Fin s ≃ C)
    (he : (Γ.restrict C).IsChainOrder e) (hadj : Γ.underlyingGraph.Adj v (e ⟨0, hs0⟩))
    (huniq : ∀ w ∈ C, Γ.underlyingGraph.Adj v w → w = e ⟨0, hs0⟩)
    (hβ : ∀ k ∈ C, Γ.boundary k = 0) (g : V → ℚ) :
    ∑ k ∈ C, g k * Γ.c k = g (e ⟨s - 1, by omega⟩) := by
  rw [Finset.sum_eq_single_of_mem _ (e ⟨s - 1, by omega⟩).2]
  · rw [Γ.c_of_isChainOrder hs hcomp hs0 e he hadj huniq hβ, show (s - 1 : ℕ) + 1 = s by omega]
    simp
  · intro k hk hkl
    have hk' : (e (e.symm ⟨k, hk⟩) : V) = k := by simp
    have hne : ¬ ((e.symm ⟨k, hk⟩ : ℕ) + 1 = s) := by
      intro h
      apply hkl
      rw [← hk']
      exact congrArg (fun i => (e i : V)) (Fin.ext (by simp only []; omega))
    rw [← hk', Γ.c_of_isChainOrder hs hcomp hs0 e he hadj huniq hβ]
    simp only [hne, ↓reduceIte, mul_zero]

omit [Fintype V] [DecidableEq V] in
/-- A sequence of consecutively adjacent vertices gives a walk through them. -/
private theorem exists_walk_support_eq {G : SimpleGraph V} (f : ℕ → V) :
    ∀ m : ℕ, (∀ t < m, G.Adj (f t) (f (t + 1))) →
      ∃ p : G.Walk (f 0) (f m), p.support = (List.range (m + 1)).map f
  | 0, _ => ⟨SimpleGraph.Walk.nil, by simp⟩
  | m + 1, h => by
    obtain ⟨p, hp⟩ := exists_walk_support_eq f m (fun t ht => h t (by omega))
    refine ⟨p.concat (h m (by omega)), ?_⟩
    rw [SimpleGraph.Walk.support_concat, hp, List.range_succ (n := m + 1), List.map_append]
    simp

/-- In an acyclic graph, the path between the ends of an injective sequence of consecutively
adjacent vertices has the vertices of the sequence as its vertex set. -/
private theorem treePath_eq_image (hΓ : Γ.IsAcyclic) (f : ℕ → V) (m : ℕ)
    (h : ∀ t < m, Γ.underlyingGraph.Adj (f t) (f (t + 1)))
    (hinj : ∀ a ≤ m, ∀ b ≤ m, f a = f b → a = b) :
    Γ.treePath (f 0) (f m) = (range (m + 1)).image f := by
  obtain ⟨p, hp⟩ := exists_walk_support_eq f m h
  have hpath : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hp]
    exact List.Nodup.map_on (fun a ha b hb hab => hinj a (Nat.le_of_lt_succ (List.mem_range.mp ha))
      b (Nat.le_of_lt_succ (List.mem_range.mp hb)) hab) List.nodup_range
  rw [Γ.treePath_eq_support hΓ ⟨p, hpath⟩]
  ext y
  simp [hp]

/-- The path along a spine `x_1, …, x_r` has vertex set `{x_1, …, x_r}`. -/
private theorem treePath_spine (hΓ : Γ.IsAcyclic) {r : ℕ} (hr : 0 < r) (x : Fin r → V)
    (hxinj : Function.Injective x)
    (hxadj : ∀ (t : ℕ) (ht : t + 1 < r),
      Γ.underlyingGraph.Adj (x ⟨t, by omega⟩) (x ⟨t + 1, ht⟩)) :
    Γ.treePath (x ⟨0, hr⟩) (x ⟨r - 1, by omega⟩) = univ.image x := by
  let f : ℕ → V := fun t => if h : t < r then x ⟨t, h⟩ else x ⟨0, hr⟩
  have hf : ∀ t (ht : t < r), f t = x ⟨t, ht⟩ := fun t ht => dif_pos ht
  have key := Γ.treePath_eq_image hΓ f (r - 1)
    (fun t ht => by
      rw [hf t (by omega), hf (t + 1) (by omega)]
      exact hxadj t (by omega))
    (fun a ha b hb hab => by
      rw [hf a (by omega), hf b (by omega)] at hab
      simpa using hxinj hab)
  rw [hf 0 hr, hf (r - 1) (by omega)] at key
  rw [key]
  ext y
  simp only [mem_image, mem_range, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, by omega⟩, (hf t (by omega)).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, by omega, hf t t.2⟩

/-- Consecutive terms of a spine `x_1, …, x_r` followed by a chain `A` attached to `x_r` at an
end are adjacent. -/
private theorem adj_succ_of_spine_arm {r : ℕ} (hr : 0 < r) (x : Fin r → V)
    (hxadj : ∀ (t : ℕ) (ht : t + 1 < r),
      Γ.underlyingGraph.Adj (x ⟨t, by omega⟩) (x ⟨t + 1, ht⟩))
    {A : Finset V} {s : ℕ} (hs0 : 0 < s) (e : Fin s ≃ A) (he : (Γ.restrict A).IsChainOrder e)
    (hadj : Γ.underlyingGraph.Adj (x ⟨r - 1, by omega⟩) (e ⟨0, hs0⟩)) (f : ℕ → V)
    (hf : ∀ t (ht : t < r), f t = x ⟨t, ht⟩)
    (hf' : ∀ t (_ : r ≤ t) (ht' : t - r < s), f t = e ⟨t - r, ht'⟩) :
    ∀ t < r + s - 1, Γ.underlyingGraph.Adj (f t) (f (t + 1)) := by
  intro t ht
  rcases lt_or_ge (t + 1) r with h1 | h1
  · rw [hf t (by omega), hf (t + 1) h1]
    exact hxadj t h1
  · rcases eq_or_lt_of_le h1 with h2 | h2
    · rw [hf t (by omega), hf' (t + 1) h1 (by omega)]
      have e1 : x ⟨t, by omega⟩ = x ⟨r - 1, by omega⟩ := congrArg x (Fin.ext (by simp; omega))
      have e2 : (e ⟨t + 1 - r, by omega⟩ : V) = e ⟨0, hs0⟩ :=
        congrArg (fun i => (e i : V)) (Fin.ext (by simp; omega))
      rw [e1, e2]
      exact hadj
    · rw [hf' t (by omega) (by omega), hf' (t + 1) h1 (by omega)]
      have e2 : (e ⟨t + 1 - r, by omega⟩ : V) = e ⟨t - r + 1, by omega⟩ :=
        congrArg (fun i => (e i : V)) (Fin.ext (by simp; omega))
      rw [e2]
      exact Γ.adj_of_isChainOrder he (t - r) (by omega)

/-- The path along a spine `x_1, …, x_r` followed by a chain `A` attached to `x_r` at an end has
vertex set `{x_1, …, x_r} ∪ A`. -/
private theorem treePath_spine_arm (hΓ : Γ.IsAcyclic) {r : ℕ} (hr : 0 < r) (x : Fin r → V)
    (hxinj : Function.Injective x)
    (hxadj : ∀ (t : ℕ) (ht : t + 1 < r),
      Γ.underlyingGraph.Adj (x ⟨t, by omega⟩) (x ⟨t + 1, ht⟩))
    {A : Finset V} {s : ℕ} (hs0 : 0 < s) (e : Fin s ≃ A) (he : (Γ.restrict A).IsChainOrder e)
    (hadj : Γ.underlyingGraph.Adj (x ⟨r - 1, by omega⟩) (e ⟨0, hs0⟩))
    (hdisj : ∀ t, x t ∉ A) :
    Γ.treePath (x ⟨0, hr⟩) (e ⟨s - 1, by omega⟩) = univ.image x ∪ A := by
  let f : ℕ → V := fun t => if h : t < r then x ⟨t, h⟩ else
    if h' : t - r < s then (e ⟨t - r, h'⟩ : V) else x ⟨0, hr⟩
  have hf : ∀ t (ht : t < r), f t = x ⟨t, ht⟩ := fun t ht => dif_pos ht
  have hf' : ∀ t (_ : r ≤ t) (ht' : t - r < s), f t = e ⟨t - r, ht'⟩ := fun t ht ht' => by
    simp [f, show ¬ t < r by omega, ht']
  have key := Γ.treePath_eq_image hΓ f (r + s - 1)
    (Γ.adj_succ_of_spine_arm hr x hxadj hs0 e he hadj f hf hf')
    (fun a ha b hb hab => by
      rcases lt_or_ge a r with h1 | h1 <;> rcases lt_or_ge b r with h2 | h2
      · rw [hf a h1, hf b h2] at hab
        simpa using hxinj hab
      · rw [hf a h1, hf' b h2 (by omega)] at hab
        exact absurd (hab ▸ (e _).2) (hdisj _)
      · rw [hf' a h1 (by omega), hf b h2] at hab
        exact absurd (hab ▸ (e _).2) (hdisj _)
      · rw [hf' a h1 (by omega), hf' b h2 (by omega)] at hab
        have := e.injective (Subtype.ext hab)
        simp only [Fin.mk.injEq] at this
        omega)
  have e3 : (e ⟨r + s - 1 - r, by omega⟩ : V) = e ⟨s - 1, by omega⟩ :=
    congrArg (fun i => (e i : V)) (Fin.ext (by simp; omega))
  rw [hf 0 hr, hf' (r + s - 1) (by omega) (by omega), e3] at key
  rw [key]
  ext y
  simp only [mem_image, mem_range, mem_univ, true_and, mem_union]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases lt_or_ge t r with h1 | h1
    · exact Or.inl ⟨⟨t, h1⟩, (hf t h1).symm⟩
    · rw [hf' t h1 (by omega)]
      exact Or.inr (e _).2
  · rintro (⟨t, rfl⟩ | hy)
    · exact ⟨t, by omega, hf t t.2⟩
    · refine ⟨r + e.symm ⟨y, hy⟩, by omega, ?_⟩
      rw [hf' _ (by omega) (by simp)]
      have e4 : (⟨r + ↑(e.symm ⟨y, hy⟩) - r, by simp⟩ : Fin s) = e.symm ⟨y, hy⟩ :=
        Fin.ext (by simp)
      rw [e4]
      simp

/-- **FA 3.2.1–3.2.2 ("bonus vertices, namely the simple ends").** Let `Γ` be a weighted graph with
simple edges whose underlying graph is a tree, `v` a vertex and `Γ_i` (vertex set `C`) a
component of `Γ - v` which is a chain attached to `v` at an end, with `β_k = 0` on `Γ_i`. Then
`σ(Γ, v, Γ_i) = 1`. -/
@[mmp "lem_fa3_chain_branch_value"]
theorem branchValue_eq_one_of_isChainAttachedAtEnd (hs : Γ.HasSimpleEdges) {v : V}
    {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) (hβ : ∀ k ∈ C, Γ.boundary k = 0) :
    Γ.branchValue v C = 1 := by
  obtain ⟨htree, hcomp, s, hs0, e, he, hadj, huniq⟩ := hC
  rw [Γ.branchValue_eq (e ⟨0, hs0⟩).2 hadj huniq,
    Γ.sum_mul_c_of_isChainOrder hs hcomp hs0 e he hadj huniq hβ]
  have hP := Γ.treePath_spine htree.isAcyclic hs0 (fun t => (e t : V))
    (Subtype.val_injective.comp e.injective) (fun t ht => Γ.adj_of_isChainOrder he t ht)
  have himg : univ.image (fun t => (e t : V)) = C := by
    ext y
    simp only [mem_image, mem_univ, true_and]
    exact ⟨fun ⟨t, ht⟩ => ht ▸ (e t).2, fun hy => ⟨e.symm ⟨y, hy⟩, by simp⟩⟩
  rw [hP, himg, sdiff_self, bot_eq_empty, Γ.delta_empty]
  simp

/-- On a spine `x_1, …, x_r` ending at the fork `u`, with simple edges and `p = β = 0`, summing
`g k * c_k(Γ)` over the spine gives `-g u`. -/
private theorem sum_mul_c_spine (hs : Γ.HasSimpleEdges) {C : Finset V}
    (hp : ∀ k ∈ C, Γ.genus k = 0) (hβ : ∀ k ∈ C, Γ.boundary k = 0) {r : ℕ} (hr : 0 < r)
    (x : Fin r → V) {u : V} (hxu : x ⟨r - 1, Nat.sub_lt hr Nat.one_pos⟩ = u) (hxC : ∀ t, x t ∈ C)
    (hxdeg : ∀ (t : ℕ) (ht : t + 1 < r), Γ.degree (x ⟨t, by omega⟩) = 2) (hdegu : Γ.degree u = 3)
    (g : V → ℚ) : ∑ k ∈ univ.image x, g k * Γ.c k = g u * (-1) := by
  have hcx : ∀ k ∈ C, Γ.c k = 2 - Γ.degree k := fun k hk => by
    rw [Γ.c_eq_of_hasSimpleEdges hs, hp k hk, hβ k hk]
    simp
  rw [Finset.sum_eq_single_of_mem u (hxu ▸ mem_image_of_mem x (mem_univ _))]
  · rw [hcx u (hxu ▸ hxC _), hdegu]
    norm_num
  · intro k hk hku
    simp only [mem_image, mem_univ, true_and] at hk
    obtain ⟨⟨t, ht⟩, rfl⟩ := hk
    have ht' : t + 1 < r := by
      by_contra h
      apply hku
      rw [← hxu]
      exact congrArg x (Fin.ext (by simp only []; omega))
    rw [hcx _ (hxC _), hxdeg t ht']
    norm_num

/-- **FA 3.2.7 (first proof), 3.2.5: the rule for adding a fork.** Let `Γ` be a weighted graph with
simple edges whose underlying graph is a tree, `v` a vertex and `Γ_i` (vertex set `C`) a forked
branch at `v` with fork `u` and arms `Γ_A`, `Γ_B`, with `p = β = 0` on `Γ_i`. Then
`σ(Γ, v, Γ_i) = 1 - (Δ_A - 1)(Δ_B - 1)`. -/
@[mmp "lem_fa3_add_fork_rule"]
theorem branchValue_eq_of_isForkedBranch {v u : V} {C A B : Finset V}
    (hC : Γ.IsForkedBranch v C u A B) (hp : ∀ k ∈ C, Γ.genus k = 0)
    (hβ : ∀ k ∈ C, Γ.boundary k = 0) :
    Γ.branchValue v C = 1 - ((Γ.delta A : ℚ) - 1) * ((Γ.delta B : ℚ) - 1) := by
  obtain ⟨hs, htree, -, hspine⟩ := hC
  obtain ⟨r, hr, x, hxinj, hxu, hxC, hvx, hxuniq, hxadj, hxdeg, hdegu, hCAB, hAB, hA, hB⟩ :=
    hspine
  have hac : Γ.IsAcyclic := htree.isAcyclic
  obtain ⟨-, hAcomp, sA, hsA, eA, heA, hadjA, huniqA⟩ := hA
  obtain ⟨-, hBcomp, sB, hsB, eB, heB, hadjB, huniqB⟩ := hB
  rw [Γ.branchValue_eq (hxC _) hvx hxuniq]
  have hxsub : univ.image x ⊆ C := image_subset_iff.mpr fun t _ => hxC t
  have hAsub : A ⊆ C \ univ.image x := hCAB ▸ subset_union_left
  have hBsub : B ⊆ C \ univ.image x := hCAB ▸ subset_union_right
  have hxA : ∀ t, x t ∉ A := fun t ht =>
    (mem_sdiff.mp (hAsub ht)).2 (mem_image_of_mem x (mem_univ t))
  have hxB : ∀ t, x t ∉ B := fun t ht =>
    (mem_sdiff.mp (hBsub ht)).2 (mem_image_of_mem x (mem_univ t))
  have huA : u ∉ A := hxu ▸ hxA _
  have huB : u ∉ B := hxu ▸ hxB _
  -- the three paths
  have hPu := Γ.treePath_spine hac hr x hxinj hxadj
  rw [hxu] at hPu
  have hPA := Γ.treePath_spine_arm hac hr x hxinj hxadj hsA eA heA (hxu ▸ hadjA) hxA
  have hPB := Γ.treePath_spine_arm hac hr x hxinj hxadj hsB eB heB (hxu ▸ hadjB) hxB
  have hdAB : Γ.delta (A ∪ B) = Γ.delta A * Γ.delta B :=
    Γ.delta_union_of_edgeWeight_eq_zero hAB fun j hj k hk =>
      Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex hAcomp hj (Finset.disjoint_right.mp hAB hk)
        (fun h => huB (h ▸ hk))
  have hCA : C \ (univ.image x ∪ A) = B := by
    rw [← union_sdiff_cancel_left hAB, ← hCAB, sdiff_sdiff_left]
    rfl
  have hCB : C \ (univ.image x ∪ B) = A := by
    rw [← union_sdiff_cancel_right hAB, ← hCAB, sdiff_sdiff_left]
    rfl
  -- the numbers `c_k` on the spine
  have hsx := Γ.sum_mul_c_spine hs hp hβ hr x hxu hxC hxdeg hdegu
    fun k => (Γ.delta (C \ Γ.treePath (x ⟨0, hr⟩) k) : ℚ)
  rw [← Finset.sum_sdiff hxsub, hCAB, Finset.sum_union hAB,
    Γ.sum_mul_c_of_isChainOrder hs hAcomp hsA eA heA hadjA huniqA
      (fun k hk => hβ k (mem_sdiff.mp (hAsub hk)).1),
    Γ.sum_mul_c_of_isChainOrder hs hBcomp hsB eB heB hadjB huniqB
      (fun k hk => hβ k (mem_sdiff.mp (hBsub hk)).1), hsx, hPu, hPA, hPB, hCA, hCB, hCAB, hdAB]
  push_cast
  ring

end MMP.Flips.WeightedGraph
