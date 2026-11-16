module
public import MMP.AlgebraicGeometry.Singularities.Surface.WeightedGraphLogDiscrepancy

/-!
# Log canonical three-arm stars with integral boundary

Let `Γ` be a negative definite rational tree which is a star with three arms `Γ_1, Γ_2, Γ_3`
at a vertex `v`, with integral boundary degrees `β_j ∈ ℤ_{≥ 0}`, not all zero, and whose log
discrepancy vector `a(Γ)` is nonnegative. Then, after renumbering the arms, `Γ_1` and `Γ_2`
are single vertices of weight `2`, and `β` is `1` at the far end of `Γ_3` (the vertex of `Γ_3`
which is a leaf of `Γ`) and `0` elsewhere.

## Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.boundary_cases_of_isStar`

## Implementation notes

The source states the result for the weighted dual graph `Γ(f)` of the minimal resolution of a
surface germ. The proof uses only that `Γ(f)` is negative definite, which holds for every
weighted dual graph (`MMP.Flips.IsWeightedDualGraph.isNegDef`), so the result is stated for an
arbitrary negative definite weighted graph. The far end `ℓ` of the arm `Γ_3` is recorded as the
vertex of `Γ_3` of degree `1` in `Γ`: for an arm with at least two vertices this is the end not
adjacent to `v`, and for a single-vertex arm it is that vertex.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.3.1)
-/

@[expose] public section

namespace MMP.Flips.WeightedGraph

open Finset

section Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weighted graph `Γ[0]`: `Γ` with all boundary degrees set to `0`. -/
private def zeroBoundary (Γ : WeightedGraph V) : WeightedGraph V :=
  { Γ with boundary := 0, boundary_nonneg := fun _ => le_rfl }

private theorem c_eq_c_zeroBoundary_sub (Γ : WeightedGraph V) (k : V) :
    Γ.c k = (zeroBoundary Γ).c k - Γ.boundary k := by
  simp only [WeightedGraph.c, zeroBoundary, Pi.zero_apply]
  ring

/-- `σ(Γ, v, Γ_i) = 1 - ∑_{k ∈ Γ_i} Δ(Γ_i - path(w_i, k)) β_k` for a chain arm. -/
private theorem branchValue_eq_one_sub (Γ : WeightedGraph V) (hs : Γ.HasSimpleEdges) {v : V}
    {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) :
    Γ.branchValue v C = 1 - ∑ k ∈ C,
      (Γ.delta (C \ Γ.treePath (Γ.branchNeighbor v C) k) : ℚ) * Γ.boundary k := by
  obtain ⟨ht, hcomp, s, hs0, e, he, hadj, huniq⟩ := hC
  have h1 : (zeroBoundary Γ).branchValue v C = 1 :=
    (zeroBoundary Γ).branchValue_eq_one_of_isChainAttachedAtEnd hs
      ⟨ht, hcomp, s, hs0, e, ⟨he.genus_eq_zero, he.edgeWeight_eq⟩, hadj, huniq⟩
      (fun _ _ => rfl)
  rw [← h1]
  simp only [branchValue, c_eq_c_zeroBoundary_sub Γ, mul_sub, sum_sub_distrib]
  rfl

/-- A negative definite weighted graph has positive determinant. -/
private theorem det_pos {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) : 0 < Γ.det := by
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

private theorem branchNeighbor_eq (Γ : WeightedGraph V) {v w : V} {C : Finset V} (hw : w ∈ C)
    (hvw : Γ.underlyingGraph.Adj v w)
    (huniq : ∀ w' ∈ C, Γ.underlyingGraph.Adj v w' → w' = w) :
    Γ.branchNeighbor v C = w := by
  have h : ∃! w, w ∈ C ∧ Γ.underlyingGraph.Adj v w :=
    ⟨w, ⟨hw, hvw⟩, fun w' hw' => huniq w' hw'.1 hw'.2⟩
  classical
  simp only [branchNeighbor, h, ↓reduceDIte]
  exact h.unique h.choose_spec.1 ⟨hw, hvw⟩

/-- A chain with all weights `≥ 2` has determinant `≥ 2`, and `= 2` only for a single
`(-2)`-vertex. -/
private theorem two_le_delta_and {Γ : WeightedGraph V} (hw' : ∀ j, 2 ≤ Γ.weight j) {v : V}
    {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) :
    2 ≤ Γ.delta C ∧ (Γ.delta C = 2 → ∃ u, C = {u} ∧ Γ.weight u = 2) := by
  obtain ⟨-, -, s, hs, e, he, -, -⟩ := hC
  have hw : ∀ w, 2 ≤ (Γ.restrict C).weight w := fun w => hw' w
  refine ⟨?_, fun h2 => ?_⟩
  · have := add_one_le_det_of_isChainOrder (Γ.restrict C) hs e he hw
    unfold WeightedGraph.delta
    push_cast at this
    omega
  · obtain ⟨rfl, hwt⟩ := (det_eq_two_iff_of_isChainOrder (Γ.restrict C) hs e he hw).1 h2
    exact ⟨e 0, eq_singleton_iff_unique_mem.2 ⟨(e 0).2, fun x hx =>
      congrArg Subtype.val (e.symm_apply_eq.1 (Subsingleton.elim (e.symm ⟨x, hx⟩) 0))⟩, hwt⟩

omit [DecidableEq V] in
/-- Consecutive vertices of a chain are adjacent in `Γ`. -/
private theorem adj_of_isChainOrder (Γ : WeightedGraph V) {C : Finset V} {s : ℕ}
    {e : Fin s ≃ C} (he : (Γ.restrict C).IsChainOrder e) (t : ℕ) (ht : t + 1 < s) :
    Γ.underlyingGraph.Adj (e ⟨t, by omega⟩ : V) (e ⟨t + 1, ht⟩) := by
  have hw := he.edgeWeight_eq ⟨t, by omega⟩ ⟨t + 1, ht⟩
  simp only [true_or, ↓reduceIte] at hw
  refine ⟨fun h => ?_, ?_⟩
  · simpa [Fin.ext_iff] using e.injective (Subtype.ext h)
  · change 0 < (Γ.restrict C).edgeWeight _ _
    rw [hw]
    exact one_pos

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

/-- In an acyclic graph, `path(v_1, v_{t+1})` along a chain `v_1, …, v_s` is
`{v_1, …, v_{t+1}}`. -/
private theorem treePath_chain (Γ : WeightedGraph V) (hac : Γ.IsAcyclic) {C : Finset V}
    {s : ℕ} {e : Fin s ≃ C} (he : (Γ.restrict C).IsChainOrder e) (hs0 : 0 < s) (t : Fin s) :
    Γ.treePath (e ⟨0, hs0⟩) (e t) = (univ.filter fun j : Fin s => j ≤ t).image
      fun j => (e j : V) := by
  let f : ℕ → V := fun j => if h : j < s then e ⟨j, h⟩ else e ⟨0, hs0⟩
  have hf : ∀ j (hj : j < s), f j = e ⟨j, hj⟩ := fun j hj => by simp [f, hj]
  obtain ⟨p, hp⟩ := exists_walk_support_eq (G := Γ.underlyingGraph) f t (fun j hj => by
    rw [hf j (by omega), hf (j + 1) (by omega)]
    exact adj_of_isChainOrder Γ he j (by omega))
  have hpath : p.IsPath := by
    rw [SimpleGraph.Walk.isPath_def, hp]
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    rw [hf a (by omega), hf b (by omega)] at hab
    simpa using e.injective (Subtype.ext hab)
  rw [← hf 0 hs0, ← hf t t.2, Γ.treePath_eq_support hac ⟨p, hpath⟩]
  ext y
  simp only [hp, List.mem_toFinset, List.mem_map, List.mem_range, mem_image, mem_filter,
    mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, Fin.mk_le_of_le_val (by omega), (hf j (by omega)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, Nat.lt_succ_of_le (Fin.le_def.mp hj), hf j j.2⟩

/-- A tail `v_{t+2}, …, v_s` of a chain with all weights `≥ 2` has determinant `≥ 2`. -/
private theorem two_le_delta_tail {Γ : WeightedGraph V} (hw : ∀ j, 2 ≤ Γ.weight j)
    {C : Finset V} {s : ℕ} {e : Fin s ≃ C} (he : (Γ.restrict C).IsChainOrder e) (t : Fin s)
    (ht : (t : ℕ) + 1 < s) :
    2 ≤ Γ.delta ((univ.filter fun j : Fin s => t < j).image fun j => (e j : V)) := by
  classical
  set T := (univ.filter fun j : Fin s => t < j).image fun j => (e j : V)
  set m := s - 1 - t with hm
  have hm0 : 0 < m := by omega
  let g : Fin m → T := fun j => ⟨e ⟨t + 1 + j, by omega⟩, mem_image.2
    ⟨⟨t + 1 + j, by omega⟩, mem_filter.2 ⟨mem_univ _, show (t : ℕ) < t + 1 + j by omega⟩,
      rfl⟩⟩
  have hg : Function.Bijective g := by
    refine ⟨fun i j hij => ?_, fun y => ?_⟩
    · have h1 : (e ⟨t + 1 + i, by omega⟩ : V) = e ⟨t + 1 + j, by omega⟩ :=
        congrArg (fun y : T => (y : V)) hij
      have := e.injective (Subtype.ext h1)
      simp only [Fin.mk.injEq] at this
      exact Fin.ext (by omega)
    · obtain ⟨j, hj, hjy⟩ := mem_image.1 y.2
      have hj : (t : ℕ) < j := (mem_filter.1 hj).2
      refine ⟨⟨j - t - 1, by omega⟩, Subtype.ext ?_⟩
      simp only [g, ← hjy]
      congr 2
      ext
      simp only
      omega
  let e' : Fin m ≃ T := Equiv.ofBijective g hg
  have he' : (Γ.restrict T).IsChainOrder e' := by
    refine ⟨fun i => he.genus_eq_zero ⟨t + 1 + i, by omega⟩, fun i j => ?_⟩
    refine (he.edgeWeight_eq ⟨t + 1 + i, by omega⟩ ⟨t + 1 + j, by omega⟩).trans ?_
    simp only
    split_ifs <;> omega
  have := add_one_le_det_of_isChainOrder (Γ.restrict T) hm0 e' he' (fun w => hw w)
  unfold WeightedGraph.delta
  omega

/-- The far end of a chain arm `v_1, …, v_s`, `s ≥ 2`, attached to `v` only at `v_1` is a
leaf of `Γ`, adjacent to `v_{s-1}`. -/
private theorem degree_last_of_one_lt {Γ : WeightedGraph V} {v : V} {C : Finset V}
    (hcomp : Γ.IsComponentOfRemoveVertex v C) {s : ℕ} (hs1 : 1 < s)
    {e : Fin s ≃ C} (he : (Γ.restrict C).IsChainOrder e)
    (huniq : ∀ w ∈ C, Γ.underlyingGraph.Adj v w → w = e ⟨0, by omega⟩) :
    Γ.degree (e ⟨s - 1, by omega⟩) = 1 := by
  have hvC := Γ.notMem_of_isComponentOfRemoveVertex hcomp
  have hew : ∀ j : Fin s, Γ.edgeWeight (e ⟨s - 1, by omega⟩) (e j) =
      if s - 1 + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = s - 1 then 1 else 0 :=
    fun j => he.edgeWeight_eq _ _
  rw [WeightedGraph.degree, card_eq_one]
  refine ⟨e ⟨s - 2, by omega⟩, ?_⟩
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨-, hpos⟩
    by_cases hxv : x = v
    · subst hxv
      have hA : Γ.underlyingGraph.Adj x (e ⟨s - 1, by omega⟩) :=
        ⟨fun h => hvC (h ▸ (e _).2), Γ.edgeWeight_symm _ _ ▸ hpos⟩
      have := e.injective (Subtype.ext (huniq _ (e _).2 hA))
      simp only [Fin.mk.injEq] at this
      omega
    by_cases hxC : x ∈ C
    · obtain ⟨j, rfl⟩ : ∃ j, (e j : V) = x := ⟨e.symm ⟨x, hxC⟩, by simp⟩
      rw [hew] at hpos
      have := j.2
      split_ifs at hpos with h
      · congr 2
        ext
        simp only
        omega
      · omega
    · rw [Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex hcomp (e _).2 hxC hxv] at hpos
      exact (lt_irrefl _ hpos).elim
  · rintro rfl
    refine ⟨fun h => ?_, ?_⟩
    · have := e.injective (Subtype.ext h)
      simp only [Fin.mk.injEq] at this
      omega
    · rw [hew]
      simp only
      rw [if_pos (Or.inr (by omega))]
      exact one_pos

/-- The far end of a chain arm `v_1, …, v_s` attached to `v` at `v_1` is a leaf of `Γ`. -/
private theorem degree_last {Γ : WeightedGraph V} {v : V} {C : Finset V}
    (hcomp : Γ.IsComponentOfRemoveVertex v C) {s : ℕ} (hs0 : 0 < s) {e : Fin s ≃ C}
    (he : (Γ.restrict C).IsChainOrder e) (hadj : Γ.underlyingGraph.Adj v (e ⟨0, hs0⟩))
    (huniq : ∀ w ∈ C, Γ.underlyingGraph.Adj v w → w = e ⟨0, hs0⟩) :
    Γ.degree (e ⟨s - 1, by omega⟩) = 1 := by
  have hvC := Γ.notMem_of_isComponentOfRemoveVertex hcomp
  have hew : ∀ j : Fin s, Γ.edgeWeight (e ⟨s - 1, by omega⟩) (e j) =
      if s - 1 + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = s - 1 then 1 else 0 :=
    fun j => he.edgeWeight_eq _ _
  by_cases hs1 : s = 1
  · subst hs1
    rw [WeightedGraph.degree, card_eq_one]
    refine ⟨v, ?_⟩
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨-, hpos⟩
      by_contra hxv
      by_cases hxC : x ∈ C
      · obtain ⟨j, rfl⟩ : ∃ j, (e j : V) = x := ⟨e.symm ⟨x, hxC⟩, by simp⟩
        rw [hew, if_neg (by have := j.2; omega)] at hpos
        exact lt_irrefl _ hpos
      · rw [Γ.edgeWeight_eq_zero_of_isComponentOfRemoveVertex hcomp (e _).2 hxC hxv] at hpos
        exact lt_irrefl _ hpos
    · rintro rfl
      refine ⟨fun h => hvC (h ▸ (e _).2), ?_⟩
      rw [Γ.edgeWeight_symm]
      exact hadj.2
  · exact degree_last_of_one_lt hcomp (by omega) he huniq

/-- In a chain arm `Γ_i`, `Δ(Γ_i - path(w_i, k)) = 1` forces `k` to be a leaf of `Γ`. -/
private theorem degree_eq_one_of_delta_eq_one {Γ : WeightedGraph V} (hw : ∀ j, 2 ≤ Γ.weight j)
    {v : V} {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) {k : V} (hk : k ∈ C)
    (hD : Γ.delta (C \ Γ.treePath (Γ.branchNeighbor v C) k) = 1) : Γ.degree k = 1 := by
  obtain ⟨htree, hcomp, s, hs0, e, he, hadj, huniq⟩ := hC
  set t := e.symm ⟨k, hk⟩ with htdef
  have hkt : k = e t := by simp [htdef]
  rw [branchNeighbor_eq Γ (e ⟨0, hs0⟩).2 hadj huniq, hkt,
    treePath_chain Γ htree.isAcyclic he hs0 t] at hD
  have hset : C \ (univ.filter fun j : Fin s => j ≤ t).image (fun j => (e j : V)) =
      (univ.filter fun j : Fin s => t < j).image fun j => (e j : V) := by
    ext y
    simp only [mem_sdiff, mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
    constructor
    · rintro ⟨hy, hny⟩
      refine ⟨e.symm ⟨y, hy⟩, ?_, by simp⟩
      by_contra hle
      exact hny _ (not_lt.1 hle) (by simp)
    · rintro ⟨j, hj, rfl⟩
      refine ⟨(e j).2, fun j' hj' h => ?_⟩
      obtain rfl := e.injective (Subtype.ext h)
      exact absurd hj (not_lt.2 hj')
  rw [hset] at hD
  have hts : (t : ℕ) = s - 1 := by
    by_contra hne
    have := two_le_delta_tail hw he t (by omega)
    omega
  rw [hkt, show t = ⟨s - 1, by omega⟩ from Fin.ext hts]
  exact degree_last hcomp hs0 he hadj huniq

end Helpers

/-- If `∑ f k g k = 1` with integers `f ≥ 1` and `g ≥ 0`, exactly one `g k` is nonzero, and
there `f k = g k = 1`. -/
private theorem exists_of_sum_mul_eq_one {ι : Type*} {s : Finset ι} {f g : ι → ℤ}
    (hf : ∀ k ∈ s, 1 ≤ f k) (hg : ∀ k ∈ s, 0 ≤ g k) (h : ∑ k ∈ s, f k * g k = 1) :
    ∃ k ∈ s, f k = 1 ∧ g k = 1 ∧ ∀ k' ∈ s, k' ≠ k → g k' = 0 := by
  classical
  have hnn : ∀ k ∈ s, 0 ≤ f k * g k := fun k hk => mul_nonneg (by linarith [hf k hk]) (hg k hk)
  obtain ⟨k, hk, hne⟩ : ∃ k ∈ s, f k * g k ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [sum_eq_zero hc] at h
    exact zero_ne_one h
  have hsplit := add_sum_erase s (fun k => f k * g k) hk
  have hrest : 0 ≤ ∑ k' ∈ s.erase k, f k' * g k' :=
    sum_nonneg fun k' hk' => hnn k' (mem_of_mem_erase hk')
  have hfk := hf k hk
  have hgk := hg k hk
  have hgk1 : 1 ≤ g k := by
    rcases hgk.lt_or_eq with h' | h'
    · omega
    · simp [← h'] at hne
  have hprod : f k * g k = 1 := by nlinarith
  have hrest0 : ∑ k' ∈ s.erase k, f k' * g k' = 0 := by linarith
  refine ⟨k, hk, by nlinarith, by nlinarith, fun k' hk' hne' => ?_⟩
  have h0 := (sum_eq_zero_iff_of_nonneg fun k'' hk'' => hnn k'' (mem_of_mem_erase hk'')).1
    hrest0 k' (mem_erase.2 ⟨hne', hk'⟩)
  exact (mul_eq_zero.1 h0).resolve_left (by have := hf k' hk'; omega)

/-! ### The arithmetic of the sign of `a_v` -/

private theorem term_le_half {Δ S : ℤ} (hΔ : 2 ≤ Δ) (hS : 0 ≤ S) :
    (1 - (S : ℚ)) / Δ ≤ 1 / 2 := by
  have hΔ' : (2 : ℚ) ≤ Δ := by exact_mod_cast hΔ
  have hS' : (0 : ℚ) ≤ S := by exact_mod_cast hS
  rw [div_le_iff₀ (by linarith)]
  nlinarith

private theorem term_nonpos {Δ S : ℤ} (hΔ : 2 ≤ Δ) (hS : 1 ≤ S) :
    (1 - (S : ℚ)) / Δ ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (by linarith [(by exact_mod_cast hS : (1 : ℚ) ≤ S)])
    (by positivity)

private theorem eq_of_term_ge_half {Δ S : ℤ} (hΔ : 2 ≤ Δ) (hS : 0 ≤ S)
    (h : 1 / 2 ≤ (1 - (S : ℚ)) / Δ) : S = 0 ∧ Δ = 2 := by
  have hΔ' : (2 : ℚ) ≤ Δ := by exact_mod_cast hΔ
  obtain rfl : S = 0 := by
    by_contra hne
    linarith [term_nonpos hΔ (by omega : 1 ≤ S)]
  rw [le_div_iff₀ (by linarith)] at h
  exact ⟨rfl, le_antisymm (by exact_mod_cast (by push_cast at h; linarith : (Δ : ℚ) ≤ 2)) hΔ⟩

private theorem eq_of_term_nonneg {Δ S : ℤ} (hΔ : 2 ≤ Δ) (hS : 1 ≤ S)
    (h : 0 ≤ (1 - (S : ℚ)) / Δ) : S = 1 := by
  have hΔ' : (0 : ℚ) < Δ := by exact_mod_cast (by omega : 0 < Δ)
  rw [le_div_iff₀ hΔ', zero_mul, sub_nonneg] at h
  exact le_antisymm (by exact_mod_cast h) hS

/-- The integer analysis of `0 ≤ -1 - b + ∑_i (1 - S_i) / Δ_i`: when `b` or some `S_i` is
positive, `b = 0`, one `S_i` is `1`, and the other two arms have `S_l = 0` and `Δ_l = 2`. -/
private theorem arith {Δ S : Fin 3 → ℤ} {b : ℕ} (hΔ : ∀ i, 2 ≤ Δ i) (hS : ∀ i, 0 ≤ S i)
    (h : 0 ≤ -1 - (b : ℚ) + ∑ i, (1 - (S i : ℚ)) / Δ i) (hpos : 1 ≤ b ∨ ∃ i, 1 ≤ S i) :
    ∃ i, b = 0 ∧ S i = 1 ∧ ∀ l, l ≠ i → S l = 0 ∧ Δ l = 2 := by
  rw [Fin.sum_univ_three] at h
  have h0 := term_le_half (hΔ 0) (hS 0)
  have h1 := term_le_half (hΔ 1) (hS 1)
  have h2 := term_le_half (hΔ 2) (hS 2)
  have hb : (0 : ℚ) ≤ b := by positivity
  obtain hb1 | ⟨i, hi⟩ := hpos
  · linarith [(by exact_mod_cast hb1 : (1 : ℚ) ≤ b)]
  have hti := term_nonpos (hΔ i) hi
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  refine ⟨i, ?_, eq_of_term_nonneg (hΔ i) hi ?_, fun l hl => eq_of_term_ge_half (hΔ l) (hS l) ?_⟩
  · have : (b : ℚ) ≤ 0 := by obtain rfl | rfl | rfl := hi3 <;> linarith
    exact_mod_cast this.antisymm hb
  · obtain rfl | rfl | rfl := hi3 <;> linarith
  · have hl3 : l = 0 ∨ l = 1 ∨ l = 2 := by fin_cases l <;> simp
    obtain rfl | rfl | rfl := hi3 <;> obtain rfl | rfl | rfl := hl3 <;>
      first | exact absurd rfl hl | linarith

/-- On a star, if some boundary degree is positive then either the centre has positive
boundary degree or some arm has `1 ≤ ∑_{k ∈ arms i} D i k * n k`, for weights `D ≥ 1`. -/
private theorem one_le_or_exists_one_le_sum_of_isStar {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {v : V} {N : ℕ} {arms : Fin N → Finset V} (hstar : Γ.IsStar v arms)
    {n : V → ℕ} {D : Fin N → V → ℤ} (hD : ∀ i k, 1 ≤ D i k) (hj : ∃ j, 1 ≤ n j) :
    1 ≤ n v ∨ ∃ i, 1 ≤ ∑ k ∈ arms i, D i k * (n k : ℤ) := by
  obtain ⟨j, hj⟩ := hj
  by_cases hjv : j = v
  · exact Or.inl (hjv ▸ hj)
  obtain ⟨i, -, hji⟩ := mem_biUnion.1 (by rw [hstar.biUnion_eq]; simp [hjv] :
    j ∈ univ.biUnion arms)
  exact Or.inr ⟨i, le_trans (by nlinarith [hD i j, (by exact_mod_cast hj : (1 : ℤ) ≤ n j)])
    (single_le_sum (f := fun k => D i k * (n k : ℤ))
      (fun k _ => mul_nonneg (by linarith [hD i k]) (by positivity)) hji)⟩

/-- On a star, a boundary vanishing at the centre and at every arm vertex other than `k`, and
equal to `1` at `k`, is the indicator of `k`. -/
private theorem boundary_eq_single_of_isStar {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {v : V} {N : ℕ} {arms : Fin N → Finset V} (hstar : Γ.IsStar v arms)
    {n : V → ℕ} (hn : ∀ x, Γ.boundary x = n x) {k : V} (hk : n k = 1) (hv : n v = 0)
    (h : ∀ l, ∀ x ∈ arms l, x ≠ k → n x = 0) : Γ.boundary = Pi.single k 1 := by
  refine funext fun x => ?_
  rw [hn]
  by_cases hxk : x = k
  · subst hxk
    simp [hk]
  rw [Pi.single_eq_of_ne hxk]
  by_cases hxv : x = v
  · subst hxv
    simp [hv]
  obtain ⟨l, -, hxl⟩ := mem_biUnion.1 (by rw [hstar.biUnion_eq]; simp [hxv] :
    x ∈ univ.biUnion arms)
  simp [h l x hxl hxk]

/-- At the centre of a star, `a(Γ)_v ≥ 0` gives `c_v + ∑_i σ(Γ, v, Γ_i) / Δ(Γ_i) ≥ 0`: by the
branch decomposition `a(Γ)_v` is this quantity times `Δ(Γ - v) / Δ(Γ) > 0`. -/
private theorem c_add_sum_branchValue_div_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) {v : V} {N : ℕ} {arms : Fin N → Finset V}
    (hstar : Γ.IsStar v arms) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (hv : 0 ≤ a v) :
    0 ≤ Γ.c v + ∑ i, Γ.branchValue v (arms i) / Γ.delta (arms i) := by
  rw [ha.apply_eq_branchValue_of_isTree hneg hstar.hasSimpleEdges hstar.isTree v arms
    hstar.isComponent hstar.pairwise_disjoint hstar.biUnion_eq] at hv
  exact nonneg_of_mul_nonneg_right hv (div_pos (by exact_mod_cast hneg.delta_pos _)
    (by exact_mod_cast det_pos hneg))

/-- Let `Γ` be a negative definite rational tree which is a star with three arms `arms 0`,
`arms 1`, `arms 2` at `v`, with boundary degrees in `ℤ_{≥ 0}` not all zero, and let `a` be its
log discrepancy vector, with `a k ≥ 0` for all `k`. Then, for some renumbering `σ` of the arms,
the arms `arms (σ 0)` and `arms (σ 1)` are single vertices of weight `2`, and `β` is the
indicator of the vertex `ℓ` of `arms (σ 2)` which is a leaf of `Γ` (the far end of that arm). -/
@[mmp "lem_fa3_boundary_star_case"]
public theorem IsLogDiscrepancyVector.boundary_cases_of_isStar {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    {v : V} {arms : Fin 3 → Finset V} (hstar : Γ.IsStar v arms)
    (hβ : ∀ j, ∃ n : ℕ, Γ.boundary j = n) (hpos : ∃ j, 0 < Γ.boundary j)
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (hnonneg : ∀ k, 0 ≤ a k) :
    ∃ (σ : Equiv.Perm (Fin 3)) (u₁ u₂ ℓ : V),
      arms (σ 0) = {u₁} ∧ Γ.weight u₁ = 2 ∧
      arms (σ 1) = {u₂} ∧ Γ.weight u₂ = 2 ∧
      ℓ ∈ arms (σ 2) ∧ Γ.degree ℓ = 1 ∧ Γ.boundary = Pi.single ℓ 1 := by
  classical
  have hw := hΓ.two_le_weight
  have hs := hstar.hasSimpleEdges
  choose nβ hnβ using hβ
  let D : Fin 3 → V → ℤ := fun i k => Γ.delta (arms i \ Γ.treePath (Γ.branchNeighbor v (arms i)) k)
  let S : Fin 3 → ℤ := fun i => ∑ k ∈ arms i, D i k * (nβ k : ℤ)
  have hD : ∀ i k, 1 ≤ D i k := fun i k => hneg.delta_pos _
  have hnn : ∀ i k, 0 ≤ D i k * (nβ k : ℤ) := fun i k => mul_nonneg (by linarith [hD i k])
    (by positivity)
  have hσ : ∀ i, Γ.branchValue v (arms i) = 1 - (S i : ℚ) := fun i => by
    rw [branchValue_eq_one_sub Γ hs (hstar.isChainAttachedAtEnd i)]
    simp only [S, D, hnβ]
    push_cast
    rfl
  have hbr : 0 ≤ -1 - (nβ v : ℚ) + ∑ i, (1 - (S i : ℚ)) / Γ.delta (arms i) := by
    have h := c_add_sum_branchValue_div_nonneg hneg hstar ha (hnonneg v)
    rw [Γ.c_eq_of_hasSimpleEdges hs, hΓ.genus_eq_zero, hnβ, hstar.degree_eq] at h
    simp only [hσ] at h
    push_cast at h
    linarith
  have hpos' : 1 ≤ nβ v ∨ ∃ i, 1 ≤ S i := one_le_or_exists_one_le_sum_of_isStar hstar hD
    (hpos.imp fun j hj => by rw [hnβ] at hj; exact_mod_cast hj)
  obtain ⟨i, hb0, hSi, hl⟩ := arith (fun i => (two_le_delta_and hw
    (hstar.isChainAttachedAtEnd i)).1) (fun i => sum_nonneg fun k _ => hnn i k) hbr hpos'
  obtain ⟨k, hk, hDk, hnk, hrest⟩ := exists_of_sum_mul_eq_one (s := arms i)
    (fun k _ => hD i k) (fun k _ => by positivity) hSi
  have hzero : ∀ l, ∀ x ∈ arms l, x ≠ k → nβ x = 0 := fun l x hx hxk => by
    by_cases hli : l = i
    · subst hli
      exact_mod_cast hrest x hx hxk
    have h0 := (sum_eq_zero_iff_of_nonneg fun k _ => hnn l k).1 (hl l hli).1 x hx
    exact_mod_cast (mul_eq_zero.1 h0).resolve_left (by have := hD l x; omega)
  have hσne : ∀ t, t ≠ 2 → Equiv.swap i 2 t ≠ i := fun t ht h =>
    ht (by simpa using congrArg (Equiv.swap i 2) h)
  obtain ⟨u₁, hu₁, hw₁⟩ := (two_le_delta_and hw (hstar.isChainAttachedAtEnd _)).2
    (hl _ (hσne 0 (by decide))).2
  obtain ⟨u₂, hu₂, hw₂⟩ := (two_le_delta_and hw (hstar.isChainAttachedAtEnd _)).2
    (hl _ (hσne 1 (by decide))).2
  refine ⟨Equiv.swap i 2, u₁, u₂, k, hu₁, hw₁, hu₂, hw₂, by simpa using hk,
    degree_eq_one_of_delta_eq_one hw (hstar.isChainAttachedAtEnd i) hk hDk,
    boundary_eq_single_of_isStar hstar hnβ (by exact_mod_cast hnk) hb0 hzero⟩

end MMP.Flips.WeightedGraph

end
