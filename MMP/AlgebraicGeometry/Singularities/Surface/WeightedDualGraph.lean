module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.Combinatorics.WeightedGraph.Basic
import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
import MMP.AlgebraicGeometry.Intersection.SelfIntersectionHilbertDegree
import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.NormalThreefoldSlice
import MMP.AlgebraicGeometry.Positivity.RelativelyAmplePullbackIso

/-!
# Weighted dual graphs of surface germs and their log discrepancies

Let `(X, P; B)` be a surface germ with boundary over an algebraically closed field `k`, and let
`g : Y ⟶ X` be a resolution of `(X, P)` with exceptional curves `E_1, …, E_n`. The weighted dual
graph `Γ(g)` records the weights `n_j = -(E_j · E_j)`, the genera `p_j = p_a(E_j)`, the boundary
degrees `β_j = (g⁻¹_* B · E_j)` and the edge weights `m_{jk} = (E_j · E_k)`. It is a weighted
graph, its underlying graph is connected, and it is negative definite (Mumford). For the minimal
resolution every `d_j = 2 - 2p_j - n_j - β_j` is nonpositive.

For a negative definite weighted graph `Γ` with all `d_j ≤ 0`, the log discrepancy vector `a(Γ)`
satisfies `a_k ≤ 1`, with strict inequality when `Γ` is connected and some `d_j < 0`; log
discrepancies increase on passing to a subgraph, strictly on a proper subgraph when `Γ` is
connected, not Du Val and has no rational `(-1)`-curves.

Combining these, when the minimal resolution of `(X, P; B)` has `a(Γ) ≥ 0` (the log canonical
case), every edge weight is at most `2`, every genus is at most `1`, a genus-one curve is the
whole exceptional locus with no boundary, a cycle or a double edge forces `Γ` to be a circle of
rational curves, and otherwise `Γ` is a rational tree.

## Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.le_one`,
  `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.lt_one`: `a(Γ)_k ≤ 1`, resp. `< 1`.
* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.le_of_isSubgraph`,
  `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.lt_of_isSubgraph`: monotonicity, resp. strict
  monotonicity, of log discrepancies under passing to a subgraph.
* `MMP.Flips.IsWeightedDualGraph.preconnected`: the underlying graph of `Γ(g)` is preconnected.
* `MMP.Flips.IsGermResolution.exists_isWeightedDualGraph`: `Γ(g)` is a weighted graph.
* `MMP.Flips.IsWeightedDualGraph.isNegDef`: `Γ(g)` is negative definite.
* `MMP.Flips.IsMinimalGermResolution.d_nonpos`: `d_j(Γ(f)) ≤ 0` for the minimal resolution.
* `MMP.Flips.IsMinimalGermResolution.edgeWeight_le_two_of_logDiscrepancy_nonneg`,
  `MMP.Flips.IsMinimalGermResolution.genus_le_one_of_logDiscrepancy_nonneg`,
  `MMP.Flips.IsMinimalGermResolution.eq_one_and_boundary_eq_zero_of_genus_eq_one`,
  `MMP.Flips.IsMinimalGermResolution.isCircle_of_logDiscrepancy_nonneg`,
  `MMP.Flips.IsMinimalGermResolution.isRationalTree_of_logDiscrepancy_nonneg`: the shape of
  `Γ(f)` when `a(Γ(f)) ≥ 0`.

## Implementation notes

The connectedness of `Γ(g)` is stated as `SimpleGraph.Preconnected`, since
`SimpleGraph.Connected` also asserts that the vertex set is nonempty, which fails for a
resolution without exceptional curves; for `n ≥ 1` the two agree.

The source writes `d_j = -(K_Y · E_j) - β_j` by adjunction and argues on the sign of
`(K_Y · E_j)`; here the argument is a case split on `p_j`, with the adjunction formula unwound,
and needs no canonical divisor on `Y`.

In the circle criterion no shortest cycle is needed: the circle `Γ'` is built from any cycle,
and `Γ' = Γ|_S` (which excludes chords) is a consequence of strict monotonicity of log
discrepancies, not an input to it.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.0)–(3.1.6)
* [V. Alexeev, *Fractional indices of log del Pezzo surfaces*][Alexeev1989], 3.2.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips.WeightedGraph

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}

/-! ### Log discrepancies of weighted graphs -/

open Matrix in
/-- FA 2.19.3.1 over `ℚ`, in matrix form: if `-M` is positive definite, the off-diagonal entries
of `M` are nonnegative and `∑_k b_k M_{kj} ≥ 0` for every `j`, then every `b_k ≤ 0`. -/
private theorem coeff_nonpos_of_posDef_neg {M : Matrix V V ℚ} (hM : (-M).PosDef)
    (hoff : ∀ j k, j ≠ k → 0 ≤ M j k) (b : V → ℚ) (hb : ∀ j, 0 ≤ ∑ k, b k * M k j) (i : V) :
    b i ≤ 0 := by
  by_contra hi
  push Not at hi
  set p : V → ℚ := fun k => max (b k) 0 with hp
  have hp0 : p ≠ 0 := fun h => by simpa [hp, hi.le] using (congrFun h i).le.trans_lt hi
  -- for `b j > 0`, replacing `b` by its positive part only adds nonnegative off-diagonal terms
  have key (j : V) (hj : 0 < b j) : 0 ≤ ∑ k, p k * M k j :=
    (hb j).trans <| Finset.sum_le_sum fun k _ => by
      rcases eq_or_ne k j with rfl | hk
      · simp [hp, hj.le]
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hoff k j hk)
  have hnn : 0 ≤ ∑ j, p j * ∑ k, p k * M k j := Finset.sum_nonneg fun j _ => by
    rcases le_or_gt (b j) 0 with h | h
    · simp [hp, h]
    · exact mul_nonneg (le_max_right _ _) (key j h)
  have heq : star p ⬝ᵥ ((-M) *ᵥ p) = -∑ j, p j * ∑ k, p k * M k j := by
    have hs : ∀ j k, M j k = M k j := fun j k => by
      simpa using congrFun (congrFun hM.1.eq k) j
    simp only [star_trivial, dotProduct, Matrix.neg_mulVec, Pi.neg_apply, Matrix.mulVec,
      mul_neg, Finset.sum_neg_distrib, neg_inj, Finset.mul_sum, Matrix.neg_apply, neg_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [hs]; ring
  linarith [hM.dotProduct_mulVec_pos hp0]

/-- **Log discrepancies are at most one** (FA 3.1.2). If `Γ` is a negative definite weighted graph
with `d_j(Γ) ≤ 0` for every vertex `j`, then every entry of a log discrepancy vector `a` of `Γ`
satisfies `a_k ≤ 1`. -/
@[mmp "lem_fa3_log_discrepancies_at_most_one"]
public theorem IsLogDiscrepancyVector.le_one {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    (hΓ : Γ.IsNegDef) (hd : ∀ j, Γ.d j ≤ 0) (k : V) : a k ≤ 1 := by
  have hF := (isLogDiscrepancyVector_iff Γ a).mp ha
  have := coeff_nonpos_of_posDef_neg (M := Γ.matrix.map ((↑) : ℤ → ℚ)) hΓ
    (fun j k hjk => by simp [WeightedGraph.matrix, hjk]) (fun k => a k - 1)
    (fun j => by simp only [Matrix.map_apply]; rw [hF j]; linarith [hd j]) k
  linarith

/-- Off-diagonal entries of `M(Γ)` are nonnegative. -/
private lemma matrix_nonneg_of_ne {i u : V} (h : i ≠ u) : (0 : ℚ) ≤ Γ.matrix i u := by
  simp [WeightedGraph.matrix, h]

/-- An edge of the underlying graph has positive entry in `M(Γ)`. -/
private lemma matrix_pos_of_adj {v u : V} (h : Γ.underlyingGraph.Adj v u) :
    (0 : ℚ) < Γ.matrix v u := by
  simp only [WeightedGraph.matrix, Matrix.of_apply, if_neg h.1]
  exact_mod_cast h.2

/-- The strictness step: if `c ≤ 0` vanishes at `u` and is negative at a neighbour `v` of `u`,
then the pairing `c · M(Γ) e_u` is negative. -/
private lemma sum_mul_matrix_neg {c : V → ℚ} (hc : ∀ i, c i ≤ 0) {u v : V} (hu : c u = 0)
    (hv : c v < 0) (hadj : Γ.underlyingGraph.Adj v u) :
    ∑ i, c i * (Γ.matrix i u : ℚ) < 0 := by
  rw [← add_sum_erase _ _ (mem_univ v)]
  refine add_neg_of_neg_of_nonpos (mul_neg_of_neg_of_pos hv (matrix_pos_of_adj hadj))
    (sum_nonpos fun i _ => ?_)
  obtain rfl | hiu := eq_or_ne i u
  · simp [hu]
  · exact mul_nonpos_of_nonpos_of_nonneg (hc i) (matrix_nonneg_of_ne hiu)

/-- **Log discrepancies are less than one** (FA 3.1.2). If `Γ` is a negative definite weighted
graph with connected underlying graph, `d_j(Γ) ≤ 0` for every vertex `j` and `d_{j₀}(Γ) < 0` for
some vertex `j₀`, then every entry of a log discrepancy vector `a` of `Γ` satisfies `a_k < 1`. -/
@[mmp "lem_fa3_log_discrepancies_less_than_one"]
public theorem IsLogDiscrepancyVector.lt_one {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    (hΓ : Γ.IsNegDef) (hconn : Γ.IsConnected) (hd : ∀ j, Γ.d j ≤ 0) (hd₀ : ∃ j₀, Γ.d j₀ < 0)
    (k : V) : a k < 1 := by
  obtain ⟨j₀, hj₀⟩ := hd₀
  have hF := (isLogDiscrepancyVector_iff Γ a).mp ha
  have hle : ∀ i, a i - 1 ≤ 0 := fun i => sub_nonpos.mpr (ha.le_one hΓ hd i)
  refine lt_of_le_of_ne (ha.le_one hΓ hd k) fun hk => ?_
  -- some coefficient `a_w - 1` is nonzero, since `F · e_{j₀} = -d_{j₀} ≠ 0`
  obtain ⟨w, hw⟩ : ∃ w, a w ≠ 1 := by
    by_contra! h
    have := hF j₀
    simp [h] at this
    linarith
  obtain ⟨dt, -, hd1, hd2⟩ :=
    (hconn.preconnected w k).some.exists_boundary_dart {i | a i ≠ 1} hw (by simpa using hk)
  simp only [Set.mem_setOf_eq, not_not] at hd1 hd2
  have := sum_mul_matrix_neg hle (sub_eq_zero.mpr hd2)
    ((hle _).lt_of_ne (sub_ne_zero.mpr hd1)) dt.adj
  linarith [hF dt.toProd.2, hd dt.toProd.2]

/-- The `j`-th equation of a log discrepancy vector, with `c_j` unfolded and the edge weights
summed over all vertices (the diagonal one is `0`). -/
private theorem logDiscrepancy_eq {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (j : V) :
    2 - 2 * (Γ.genus j : ℚ) - Γ.boundary j +
      ∑ k, (a k * (Γ.matrix k j : ℚ) - Γ.edgeWeight j k) = 0 := by
  have he : ∑ k ∈ univ.erase j, (Γ.edgeWeight j k : ℚ) = ∑ k, (Γ.edgeWeight j k : ℚ) := by
    rw [← Finset.add_sum_erase _ _ (mem_univ j)]; simp [Γ.edgeWeight_self]
  rw [Finset.sum_sub_distrib, ha j]
  simp only [WeightedGraph.c, he]
  ring

/-- Off the diagonal, the `k`-th summand of the `j`-th equation of `Γ` only grows when the edge
weight `m_{kj}` is lowered to any `w ≤ m_{kj}`, provided `a_k ≤ 1`. -/
private theorem summand_le {a : V → ℚ} {j k : V} (hkj : k ≠ j)
    (hk : a k ≤ 1) {w : ℕ} (hw : w ≤ Γ.edgeWeight k j) :
    a k * (Γ.matrix k j : ℚ) - Γ.edgeWeight j k ≤ a k * w - w := by
  have hw' : (w : ℚ) ≤ Γ.edgeWeight k j := by exact_mod_cast hw
  simp only [WeightedGraph.matrix, Matrix.of_apply, if_neg hkj, Γ.edgeWeight_symm j k]
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.2 hk) (sub_nonneg.2 hw')]

/-- FA 3.1.3, the pairing step: if `a_k ≤ 1` for every vertex, then
`F = ∑_{k ∈ S} (a_k - a'_k) e_k` pairs nonnegatively with every `e_j` under `M(Γ')`. -/
private theorem sum_sub_mul_matrix_nonneg {S : Finset V} {Γ' : WeightedGraph S} {a : V → ℚ}
    {a' : S → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha' : Γ'.IsLogDiscrepancyVector a')
    (h : Γ'.IsSubgraph Γ) (hle1 : ∀ k, a k ≤ 1) (j : S) :
    0 ≤ ∑ k : S, (a k - a' k) * (Γ'.matrix k j : ℚ) := by
  have hsplit := (Finset.sum_filter_add_sum_filter_not univ (· ∈ S)
    fun k => a k * (Γ.matrix k j : ℚ) - Γ.edgeWeight j k).symm
  rw [Finset.filter_mem_eq_inter, univ_inter, ← Finset.sum_coe_sort S] at hsplit
  have hin := Finset.sum_le_sum fun (k : S) (_ : k ∈ univ) =>
    show a k * (Γ.matrix k j : ℚ) - Γ.edgeWeight j k ≤
        a k * (Γ'.matrix k j : ℚ) - Γ'.edgeWeight j k by
      by_cases hkj : k = j
      · subst hkj
        simp [WeightedGraph.matrix, h.weight_eq, Γ.edgeWeight_self, Γ'.edgeWeight_self]
      · have hkj' : (k : V) ≠ j := fun e => hkj (Subtype.ext e)
        simpa [WeightedGraph.matrix, hkj, Γ'.edgeWeight_symm j k] using
          summand_le hkj' (hle1 k) (h.edgeWeight_le k j hkj)
  have hout : ∑ k ∈ univ.filter (· ∉ S), (a k * (Γ.matrix k j : ℚ) - Γ.edgeWeight j k) ≤ 0 :=
    Finset.sum_nonpos fun k hk => by
      have hkj : k ≠ j := fun e => (Finset.mem_filter.1 hk).2 (e ▸ j.2)
      simpa using summand_le hkj (hle1 k) (Nat.zero_le _)
  have hp : (Γ'.genus j : ℚ) ≤ Γ.genus j := by exact_mod_cast h.genus_le j
  have := h.boundary_le j
  simp only [sub_mul, Finset.sum_sub_distrib]
  linarith [logDiscrepancy_eq ha j, logDiscrepancy_eq ha' j,
    (Finset.sum_sub_distrib (s := (univ : Finset S)) (fun k => a k * (Γ'.matrix k j : ℚ))
      fun k => (Γ'.edgeWeight j k : ℚ)),
    (Finset.sum_sub_distrib (s := (univ : Finset S)) (fun k => a' k * (Γ'.matrix k j : ℚ))
      fun k => (Γ'.edgeWeight j k : ℚ))]

/-- **Log discrepancies increase on passing to a subgraph** (FA 3.1.3). Let `Γ` be a negative
definite weighted graph with `d_j(Γ) ≤ 0` for every vertex `j`, and `Γ'` a subgraph of `Γ` on the
vertex set `S`. If `a` is a log discrepancy vector of `Γ` and `a'` one of `Γ'`, then
`a k ≤ a' k` for every `k ∈ S`. -/
@[mmp "lem_fa3_subgraph_log_discrepancy_monotone"]
public theorem IsLogDiscrepancyVector.le_of_isSubgraph {S : Finset V} {Γ' : WeightedGraph S}
    {a : V → ℚ} {a' : S → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    (ha' : Γ'.IsLogDiscrepancyVector a') (h : Γ'.IsSubgraph Γ) (hΓ : Γ.IsNegDef)
    (hd : ∀ j, Γ.d j ≤ 0) (k : S) : a k ≤ a' k := by
  have := coeff_nonpos_of_posDef_neg (M := Γ'.matrix.map ((↑) : ℤ → ℚ)) (h.isNegDef hΓ)
    (fun j k hjk => by simp [WeightedGraph.matrix, hjk]) (fun k => a k - a' k)
    (fun j => by simpa only [Matrix.map_apply] using
      sum_sub_mul_matrix_nonneg ha ha' h (ha.le_one hΓ hd) j) k
  linarith

/-- FA 3.1.3, the pairing identity: for log discrepancy vectors `a` of `Γ` and `a'` of a
subgraph `Γ'`, `∑_k (a_k - a'_k) M(Γ')_{kj} = R_j`, where
`R_j = 2(p_j - p'_j) + (β_j - β'_j) + ∑_{k ∈ S} (1 - a_k)(m_{kj} - m'_{kj})
  + ∑_{k ∉ S} (1 - a_k) m_{kj}`. -/
private theorem sum_sub_mul_matrix_eq {S : Finset V} {Γ' : WeightedGraph S} {a : V → ℚ}
    {a' : S → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha' : Γ'.IsLogDiscrepancyVector a')
    (h : Γ'.IsSubgraph Γ) (j : S) :
    ∑ k : S, (a k - a' k) * (Γ'.matrix k j : ℚ) =
      2 * ((Γ.genus j : ℚ) - Γ'.genus j) + (Γ.boundary j - Γ'.boundary j) +
      ∑ k : S, (1 - a k) * ((Γ.edgeWeight k j : ℚ) - Γ'.edgeWeight k j) +
      ∑ k ∈ Sᶜ, (1 - a k) * (Γ.edgeWeight k j : ℚ) := by
  have e1 := logDiscrepancy_eq ha j
  have e2 := logDiscrepancy_eq ha' j
  rw [← Finset.sum_add_sum_compl S, ← Finset.sum_coe_sort S] at e1
  have t1 : ∀ k : S, a k * (Γ.matrix k j : ℚ) - Γ.edgeWeight j k =
      (a k * (Γ'.matrix k j : ℚ) - Γ'.edgeWeight j k) -
        (1 - a k) * ((Γ.edgeWeight k j : ℚ) - Γ'.edgeWeight k j) := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      simp [WeightedGraph.matrix, h.weight_eq, Γ.edgeWeight_self, Γ'.edgeWeight_self]
    · have hkj' : (k : V) ≠ j := fun e => hkj (Subtype.ext e)
      simp only [WeightedGraph.matrix, Matrix.of_apply, if_neg hkj, if_neg hkj',
        Γ.edgeWeight_symm j k, Γ'.edgeWeight_symm j k]
      push_cast
      ring
  have t2 : ∀ k ∈ Sᶜ, a k * (Γ.matrix k j : ℚ) - Γ.edgeWeight j k =
      -((1 - a k) * (Γ.edgeWeight k j : ℚ)) := by
    intro k hk
    have hkj : k ≠ j := fun e => (Finset.mem_compl.1 hk) (e ▸ j.2)
    simp only [WeightedGraph.matrix, Matrix.of_apply, if_neg hkj, Γ.edgeWeight_symm j k]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => t1 k), Finset.sum_congr rfl t2, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib] at e1
  have e3 : ∑ k : S, (a k - a' k) * (Γ'.matrix k j : ℚ) =
      ∑ k : S, (a k * (Γ'.matrix k j : ℚ) - Γ'.edgeWeight j k) -
        ∑ k : S, (a' k * (Γ'.matrix k j : ℚ) - Γ'.edgeWeight j k) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e3]
  linarith

/-- If `a_j = a'_j` at a vertex `j ∈ S`, where `a ≤ a'` on `S` and `a < 1`, then every summand of
`R_j` vanishes and `a_k = a'_k` at every `Γ'`-neighbour of `j`; in particular `Γ'` agrees with `Γ`
at `j` (genus, boundary, every edge weight `m_{kj}`), and every `Γ`-neighbour of `j` is a vertex
of `S` at which `a = a'`. -/
private theorem isSubgraph_agree_of_logDiscrepancy_eq {S : Finset V} {Γ' : WeightedGraph S}
    {a : V → ℚ} {a' : S → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha' : Γ'.IsLogDiscrepancyVector a')
    (h : Γ'.IsSubgraph Γ) (hle : ∀ k : S, a k ≤ a' k) (hlt : ∀ k, a k < 1) (j : S)
    (hj : a j = a' j) :
    Γ'.genus j = Γ.genus j ∧ Γ'.boundary j = Γ.boundary j ∧
      (∀ k : S, Γ'.edgeWeight k j = Γ.edgeWeight k j) ∧
      (∀ k ∉ S, Γ.edgeWeight k j = 0) ∧
      (∀ k : S, 0 < Γ'.edgeWeight k j → a k = a' k) := by
  have hid := sum_sub_mul_matrix_eq ha ha' h j
  have hL : ∀ k : S, (a k - a' k) * (Γ'.matrix k j : ℚ) ≤ 0 := by
    intro k
    by_cases hkj : k = j
    · subst hkj
      simp [hj]
    · simp only [WeightedGraph.matrix, Matrix.of_apply, if_neg hkj]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hle k]) (by positivity)
  have hR1 : ∀ k : S, 0 ≤ (1 - a k) * ((Γ.edgeWeight k j : ℚ) - Γ'.edgeWeight k j) := by
    intro k
    refine mul_nonneg (by linarith [hlt k]) (sub_nonneg.2 ?_)
    by_cases hkj : k = j
    · subst hkj
      simp [Γ.edgeWeight_self, Γ'.edgeWeight_self]
    · exact_mod_cast h.edgeWeight_le k j hkj
  have hR2 : ∀ k ∈ Sᶜ, 0 ≤ (1 - a k) * (Γ.edgeWeight k j : ℚ) :=
    fun k _ => mul_nonneg (by linarith [hlt k]) (by positivity)
  have hp : (Γ'.genus j : ℚ) ≤ Γ.genus j := by exact_mod_cast h.genus_le j
  have hb := h.boundary_le j
  have sL := Finset.sum_nonpos fun k (_ : k ∈ univ) => hL k
  have sR1 := Finset.sum_nonneg fun k (_ : k ∈ univ) => hR1 k
  have sR2 := Finset.sum_nonneg hR2
  have zR1 := (Finset.sum_eq_zero_iff_of_nonneg fun k (_ : k ∈ univ) => hR1 k).1
    (by linarith)
  have zR2 := (Finset.sum_eq_zero_iff_of_nonneg hR2).1 (by linarith)
  have zL := (Finset.sum_eq_zero_iff_of_nonpos fun k (_ : k ∈ univ) => hL k).1 (by linarith)
  refine ⟨by exact_mod_cast (show (Γ'.genus j : ℚ) = Γ.genus j by linarith), by linarith,
    fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rcases mul_eq_zero.1 (zR1 k (mem_univ _)) with h1 | h1
    · linarith [hlt k]
    · exact_mod_cast (sub_eq_zero.1 h1).symm
  · rcases mul_eq_zero.1 (zR2 k (Finset.mem_compl.2 hk)) with h1 | h1
    · linarith [hlt k]
    · exact_mod_cast h1
  · have hkj : k ≠ j := by
      rintro rfl
      simp [Γ'.edgeWeight_self] at hk
    have := zL k (mem_univ _)
    simp only [WeightedGraph.matrix, Matrix.of_apply, if_neg hkj] at this
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact absurd h1 (by exact_mod_cast hk.ne')

/-- A weighted graph on `S` that agrees with `Γ` in every datum is `Γ.restrict S`. -/
private theorem eq_restrict_of_forall {S : Finset V} {Γ' : WeightedGraph S}
    (hw : ∀ j : S, Γ'.weight j = Γ.weight j) (hg : ∀ j : S, Γ'.genus j = Γ.genus j)
    (hb : ∀ j : S, Γ'.boundary j = Γ.boundary j)
    (he : ∀ j k : S, Γ'.edgeWeight j k = Γ.edgeWeight j k) : Γ' = Γ.restrict S := by
  cases Γ'
  simp only [WeightedGraph.restrict, WeightedGraph.mk.injEq]
  exact ⟨funext hw, funext hg, funext hb, funext fun j => funext fun k => he j k⟩

/-- **Log discrepancies strictly increase on passing to a proper subgraph** (FA 3.1.3). Let `Γ`
be a negative definite weighted graph with connected underlying graph, `d_j(Γ) ≤ 0` for every
vertex `j`, no vertex with `p_j = 0` and `n_j = 1`, and which is not a Du Val graph. Let `Γ'` be
a subgraph of `Γ` on the vertex set `S` with `Γ' ≠ Γ`, that is `S ≠ univ` or `Γ' ≠ Γ.restrict S`.
If `a` is a log discrepancy vector of `Γ` and `a'` one of `Γ'`, then `a k < a' k` for every
`k ∈ S`. -/
@[mmp "lem_fa3_subgraph_log_discrepancy_strict"]
public theorem IsLogDiscrepancyVector.lt_of_isSubgraph {S : Finset V} {Γ' : WeightedGraph S}
    {a : V → ℚ} {a' : S → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    (ha' : Γ'.IsLogDiscrepancyVector a') (h : Γ'.IsSubgraph Γ)
    (hne : S ≠ univ ∨ Γ' ≠ Γ.restrict S) (hΓ : Γ.IsNegDef) (hconn : Γ.IsConnected)
    (hd : ∀ j, Γ.d j ≤ 0) (hp : ∀ j, ¬(Γ.genus j = 0 ∧ Γ.weight j = 1)) (hduval : ¬Γ.IsDuVal)
    (k : S) : a k < a' k := by
  -- some `d_j(Γ)` is negative, otherwise `Γ` would be Du Val
  have hd₀ : ∃ j₀, Γ.d j₀ < 0 := by
    by_contra hcon
    push Not at hcon
    refine hduval (isDuVal_of_forall_d_eq_zero (fun j => ?_) hp
      fun j => le_antisymm (hd j) (hcon j))
    have := hΓ.diag_pos (i := j)
    simp [WeightedGraph.matrix] at this
    exact_mod_cast this
  have hlt := ha.lt_one hΓ hconn hd hd₀
  have hle : ∀ k : S, a k ≤ a' k := ha.le_of_isSubgraph ha' h hΓ hd
  refine lt_of_le_of_ne (hle k) fun hk => ?_
  -- the set of vertices of `S` where `a = a'` is closed under adjacency in `Γ`
  let P : V → Prop := fun v => ∃ hv : v ∈ S, a v = a' ⟨v, hv⟩
  have hstep : ∀ u v, Γ.underlyingGraph.Adj u v → P u → P v := by
    rintro u v ⟨_, huv⟩ ⟨hu, hau⟩
    obtain ⟨-, -, he, hout, hnb⟩ :=
      isSubgraph_agree_of_logDiscrepancy_eq ha ha' h hle hlt ⟨u, hu⟩ hau
    have huv' : 0 < Γ.edgeWeight v u := Γ.edgeWeight_symm u v ▸ huv
    by_cases hv : v ∈ S
    · exact ⟨hv, hnb ⟨v, hv⟩ (by rwa [he ⟨v, hv⟩])⟩
    · exact absurd (hout v hv) huv'.ne'
  have hwalk : ∀ {u v : V} (_ : Γ.underlyingGraph.Walk u v), P u → P v := by
    intro u v p
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hu => ih (hstep _ _ hadj hu)
  have hall : ∀ v, P v := fun v => hwalk (hconn.preconnected k v).some ⟨k.2, hk⟩
  have hagree := fun j : S => isSubgraph_agree_of_logDiscrepancy_eq ha ha' h hle hlt j (hall j).2
  rcases hne with hne | hne
  · exact hne (eq_univ_of_forall fun v => (hall v).1)
  · exact hne (eq_restrict_of_forall h.weight_eq (fun j => (hagree j).1)
      (fun j => (hagree j).2.1) fun j k => (hagree k).2.2.1 j)

end MMP.Flips.WeightedGraph

namespace MMP.Flips

open MMP.Mori

/-! ### The weighted dual graph of a resolution -/

/-- In a Noetherian space every point `y` of a closed set `F` lies on a maximal irreducible
subset `Z` of `F`, and `F ⊆ Z ∪ C` for a closed set `C` not containing `Z`. -/
private lemma exists_maximal_isIrreducible_subset {T : Type*} [TopologicalSpace T]
    [TopologicalSpace.NoetherianSpace T] {F : Set T} (hF : IsClosed F) {y : T} (hy : y ∈ F) :
    ∃ Z C : Set T, Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ F) Z ∧ IsClosed Z ∧ y ∈ Z ∧
      IsClosed C ∧ F ⊆ Z ∪ C ∧ ¬ Z ⊆ C := by
  obtain ⟨S, hSfin, hScl, hSirr, hSeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  obtain ⟨T₀, hT₀, hyT₀⟩ : y ∈ ⋃₀ S := hSeq ▸ hy
  obtain ⟨Z, hT₀Z, hZ⟩ := hSfin.exists_le_maximal hT₀
  have hZS : Z ∈ S := hZ.prop
  have hZF : Z ⊆ F := hSeq ▸ Set.subset_sUnion_of_mem hZS
  -- an irreducible subset of `F` lies in a member of `S`
  have hsub : ∀ {W : Set T}, IsIrreducible W → ∀ {S' : Set (Set T)}, S' ⊆ S →
      W ⊆ ⋃₀ S' → ∃ t ∈ S', W ⊆ t := by
    intro W hW S' hS' hWS
    have hfin : S'.Finite := hSfin.subset hS'
    obtain ⟨t, ht, hWt⟩ := (isIrreducible_iff_sUnion_isClosed.mp hW) hfin.toFinset
      (fun t ht => hScl t (hS' (hfin.mem_toFinset.mp ht))) (by simpa using hWS)
    exact ⟨t, hfin.mem_toFinset.mp ht, hWt⟩
  have hmax : Maximal (fun W : Set T => IsIrreducible W ∧ W ⊆ F) Z := by
    refine ⟨⟨hSirr Z hZS, hZF⟩, fun W hW hZW => ?_⟩
    obtain ⟨t, htS, hWt⟩ := hsub hW.1 le_rfl (hSeq ▸ hW.2)
    exact (hZ.2 htS (hZW.trans hWt)).trans' hWt
  refine ⟨Z, ⋃₀ (S \ {Z}), hmax, hScl Z hZS, hT₀Z hyT₀,
    (hSfin.subset Set.diff_subset).isClosed_sUnion fun t ht => hScl t ht.1, ?_, ?_⟩
  · intro x hx
    obtain ⟨t, htS, hxt⟩ := (hSeq ▸ hx : x ∈ ⋃₀ S)
    by_cases htZ : t = Z
    · exact Or.inl (htZ ▸ hxt)
    · exact Or.inr ⟨t, ⟨htS, htZ⟩, hxt⟩
  · intro hZC
    obtain ⟨t, ⟨htS, htZ⟩, hZt⟩ := hsub (hSirr Z hZS) Set.diff_subset hZC
    exact htZ (le_antisymm (hZ.2 htS hZt) hZt)

/-- A prime divisor in the support of `mapPrimeDivisors φ D` is `φ` of some prime divisor. -/
private theorem exists_eq_some_of_mem_support_mapPrimeDivisors {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)}
    {D : DivisorWithCoeffs R X} {Q : MMP.Mori.PrimeDivisor Y}
    (hQ : Q ∈ (DivisorWithCoeffs.mapPrimeDivisors φ D).support) : ∃ E, φ E = some Q := by
  classical
  by_contra! h
  refine Finsupp.mem_support_iff.mp hQ ?_
  clear hQ
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' hD hD' => rw [map_add, Finsupp.add_apply, hD, hD', add_zero]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single]
    rcases hφ : φ E with _ | Q'
    · rfl
    · simp [Finsupp.single_apply, show Q' ≠ Q from fun h' => h E (h' ▸ hφ)]

/-- The coefficient of `g⁻¹_*(D)` in `g⁻¹_* B` is that of `D` in `B`. -/
private theorem inverseTransformDivisor_apply_of_eq_some {X Y : Scheme.{u}} {R : Type*}
    [AddCommMonoid R] {g : Y ⟶ X} {D : MMP.Mori.PrimeDivisor X} {C : MMP.Mori.PrimeDivisor Y}
    (hD : inverseTransformPrimeDivisor g D = some C) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor g B C = B D :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hD (fun _ hD' =>
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective <|
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
        hD').1.symm.trans
      (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).1) B

section SmoothSurface

variable {k : Type u} [Field k] {Y : Scheme.{u}} {sY : Y ⟶ Spec (.of k)}
  [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y]

/-- On a smooth surface, `(C · C)` of a proper curve `C` is an integer: the degree on `C` of
the Cartier divisor `C`. -/
private theorem exists_int_isIntersectionNumber_self (hsm : IsSmoothScheme sY)
    {C : MMP.Mori.PrimeDivisor Y} (hC : IsProper (C.idealSheaf.subschemeι ≫ sY))
    (hdim : topologicalKrullDim C.idealSheaf.subscheme ≤ 1) :
    ∃ d : ℤ, IsIntersectionNumber sY (Finsupp.single C 1) C.idealSheaf d := by
  have hcart := MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm C
  have hQ := MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm C
  rw [← Int.cast_one, ← MMP.Threefold.Resolution.toQDivisor_single]
  exact ⟨_, hC, hdim, hQ, QDivisor.intersectionNumber_toQDivisor k sY _ hdim _ hcart hQ⟩

/-- **Effective divisors meet curves nonnegatively.** On a smooth integral surface, if `D` is an
effective `ℚ`-divisor none of whose components is the proper curve `C`, then `(D · C)` is
defined and nonnegative: it is `∑_D' D_{D'} ∑_{y ∈ C ∩ D'} i_y(C, D')`. -/
private theorem exists_nonneg_isIntersectionNumber [IsIntegral Y] (hY : MMP.Mori.IsVariety k sY)
    (hsm : IsSmoothScheme sY) (hdimY : topologicalKrullDim Y = 2) {C : MMP.Mori.PrimeDivisor Y}
    (hC : IsProper (C.idealSheaf.subschemeι ≫ sY))
    (hdim : topologicalKrullDim C.idealSheaf.subscheme ≤ 1) {D : QDivisor Y}
    (hD : ∀ C' ∈ D.support, 0 ≤ D C' ∧ C ≠ C') :
    ∃ β : ℚ, 0 ≤ β ∧ IsIntersectionNumber sY D C.idealSheaf β := by
  classical
  obtain ⟨d, hd⟩ := exists_int_isIntersectionNumber_self hsm hC hdim
  have h := isIntersectionNumber_sum D.support (isIntersectionNumber_zero hd) fun C' hC' =>
    (isIntersectionNumber_finsum_localIntersectionNumber_of_ne sY hY hsm hdimY (hD C' hC').2
      hC).2.1.smul (D C') (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)
  simp_rw [Finsupp.smul_single_one] at h
  rw [show ∑ C' ∈ D.support, Finsupp.single C' (D C') = D from Finsupp.sum_single D] at h
  exact ⟨_, Finset.sum_nonneg fun C' hC' => mul_nonneg (hD C' hC').1
    (finsum_nonneg fun y => finsum_nonneg fun _ => by positivity), h⟩

end SmoothSurface

section DualGraph

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}

/-- A common point of `E_j` and `E_l` (`j ≠ l`) makes `v_j` and `v_l` adjacent in `Γ`: the edge
weight `m_{lj} = (E_j · E_l)` is the sum of the positive local intersection numbers. -/
private lemma adj_of_mem_inter (hΓ : IsWeightedDualGraph sX P B f E Γ) {j l : Fin n}
    (hjl : j ≠ l) {y : Y} (hy : y ∈ ((E j).support ∩ (E l).support : Set Y)) :
    Γ.underlyingGraph.Adj l j := by
  have hg := hΓ.isGermResolution
  have hCD : E j ≠ E l := fun h => hjl (hΓ.isExceptionalCurveEnumeration.injective h)
  have hC := ((hΓ.isExceptionalCurveEnumeration.isGermExceptionalCurve j).isProper sX hg).2
  obtain ⟨hfin, hI, hpos⟩ := isIntersectionNumber_finsum_localIntersectionNumber_of_ne (f ≫ sX)
    hg.isVariety hg.isSmoothResolution.isSmoothScheme hg.topologicalKrullDim_eq hCD hC
  have heq := (hΓ.edgeWeight l j (Ne.symm hjl)).unique hI
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at heq
  refine ⟨Ne.symm hjl, ?_⟩
  rw [show Γ.edgeWeight l j = _ by exact_mod_cast heq]
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨y, hfin.mem_toFinset.mpr hy, hpos y hy⟩

/-- If the fibre `f⁻¹(P)` is preconnected and there is at least one exceptional curve, then
`f⁻¹(P)` is the union of the exceptional curves: an irreducible component of `f⁻¹(P)` which is
not a curve would be a closed point, isolated in the fibre. -/
private lemma exists_mem_support_of_isPreconnected (hΓ : IsWeightedDualGraph sX P B f E Γ)
    (hconn : _root_.IsPreconnected (f.base ⁻¹' {P})) (u : Fin n) {y : Y} (hy : f y = P) :
    ∃ j, y ∈ (E j).support := by
  have hg := hΓ.isGermResolution
  have hE := hΓ.isExceptionalCurveEnumeration
  have hYv := hg.isVariety
  have : IsIntegral Y := hYv.toIsIntegral
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : IsNoetherian Y := {}
  have hP : IsClosed ({P} : Set X) := hg.isSurfaceGerm.2.2.1
  have hFcl : IsClosed (f.base ⁻¹' {P}) := hP.preimage f.base.hom.continuous
  obtain ⟨Z, C, hZ, hZcl, hyZ, hCcl, hFZC, hZC⟩ := exists_maximal_isIrreducible_subset hFcl hy
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hZ.prop.1 hZcl
  have hξZ : ξ ∈ Z := hξ.mem
  have hEuF : ((E u).support : Set Y) ⊆ f.base ⁻¹' {P} :=
    (hE.isGermExceptionalCurve u).1.prop.2
  -- `ξ` is not a closed point: otherwise `{ξ}` would be open and closed in `f⁻¹(P)`
  have hξncl : ¬ IsClosed ({ξ} : Set Y) := by
    intro hcl
    have hZξ : Z = {ξ} := by rw [← hξ.def, hcl.closure_eq]
    have hξC : ξ ∉ C := fun h => hZC (hZξ ▸ Set.singleton_subset_iff.mpr h)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn {ξ} C hcl hCcl
        (hZξ ▸ hFZC) (by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
            iff_false, not_and]
          rintro - rfl
          exact hξC) with h | h
    · exact (((hE.isGermExceptionalCurve u).2).not_subsingleton)
        ((Set.subsingleton_singleton).anti (hEuF.trans h))
    · exact hξC (h (hZ.prop.2 hξZ))
  -- a closed point `c` of `Z` other than `ξ`
  obtain ⟨c, hcZ, hccl⟩ := hZcl.exists_closed_singleton ⟨ξ, hξZ⟩
  have hcξ : c ≠ ξ := fun h => hξncl (h ▸ hccl)
  have hξc : ξ ⤳ c := hξ.specializes hcZ
  have hco2 := MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hYv
    hg.topologicalKrullDim_eq hccl
  -- `ξ` is not the generic point of `Y`, since `f` is an isomorphism away from `P`
  have hξmax : ¬ IsMax ξ := by
    intro hmax
    have : IsIntegral X := hg.isSurfaceGerm.1.1.toIsIntegral
    have := hg.isSmoothResolution.isBirationalMorphism.isDominant
    have h2 : ξ ⤳ genericPoint Y := hmax (genericPoint_specializes ξ)
    have hgη : f (genericPoint Y) = P := hZ.prop.2 (h2.mem_closed hZcl hξZ)
    rw [map_genericPoint_of_isDominant] at hgη
    have : Subsingleton X := ⟨fun a b => by
      have ha := (genericPoint_specializes a).mem_closed hP (by rw [hgη]; rfl)
      have hb := (genericPoint_specializes b).mem_closed hP (by rw [hgη]; rfl)
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology X
    rw [hg.isSurfaceGerm.2.1] at h0
    exact absurd h0 (by decide)
  have hco : Order.coheight ξ = 1 := by
    have hcξlt : c < ξ := lt_of_le_not_ge hξc fun h =>
      hcξ ((h : c ⤳ ξ).mem_closed hccl rfl).symm
    have hlt : Order.coheight ξ < 2 := hco2 ▸ Order.coheight_strictAnti hcξlt
      (lt_of_le_of_lt (hco2 ▸ Order.coheight_anti hcξlt.le) (by decide))
    have hne : Order.coheight ξ ≠ 0 := fun h => hξmax (Order.coheight_eq_zero.mp h)
    generalize Order.coheight ξ = d at hlt hne ⊢
    induction d using ENat.recTopCoe with
    | top => exact absurd hlt (by decide)
    | coe d =>
      norm_cast at hlt hne ⊢
      omega
  let D : MMP.Mori.PrimeDivisor Y := AlgebraicGeometry.PrimeDivisor.ofCoheightOne ξ hco
  have hDsupp : (D.support : Set Y) = Z := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne, hξ.def]
  obtain ⟨j, hj⟩ := hE.exists_eq D ⟨hDsupp ▸ hZ,
    isCurveIn_idealSheaf_of_topologicalKrullDim_eq_two hYv hg.topologicalKrullDim_eq D⟩
  exact ⟨j, by rwa [hj, hDsupp]⟩

/-- A component of `g⁻¹_* B` does not lie over the closed point `P` of a surface germ. -/
private theorem map_genericPoint_ne_of_mem_support (hX : IsSurfaceGerm sX P)
    {C : MMP.Mori.PrimeDivisor Y} (hC : C ∈ (inverseTransformDivisor f B).support) :
    f.base C.genericPoint ≠ P := by
  intro hP
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  have h := MMP.Positivity.coheight_map_of_mem_biregularLocus f
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hD).2
  rw [hP, MMP.Threefold.Resolution.coheight_eq_two_of_isClosed hX.1.1 hX.2.1 hX.2.2.1,
    C.coheight_genericPoint] at h
  exact absurd h (by decide)

/-- The components of `f⁻¹_* B` have nonnegative coefficients and are not exceptional curves. -/
private theorem nonneg_and_ne_of_mem_support_inverseTransformDivisor
    (hg : IsGermResolution sX P f) (hB : IsSurfaceGermWithBoundary sX P B)
    {E C : MMP.Mori.PrimeDivisor Y} (hE : IsGermExceptionalCurve f P E)
    (hC : C ∈ (inverseTransformDivisor f B).support) :
    0 ≤ inverseTransformDivisor f B C ∧ E ≠ C := by
  obtain ⟨D, hD⟩ := exists_eq_some_of_mem_support_mapPrimeDivisors hC
  refine ⟨inverseTransformDivisor_apply_of_eq_some hD B ▸ (hB.2.2 D).1, fun hEC => ?_⟩
  refine map_genericPoint_ne_of_mem_support hg.isSurfaceGerm hC <| hE.1.prop.2 ?_
  rw [hEC, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

/-- The entries of `M(Γ)` are the intersection numbers `(E_j · E_l)`: the diagonal by the
`weight` field, the off-diagonal entries by the `edgeWeight` field. -/
private theorem isIntersectionNumber_matrix (hΓ : IsWeightedDualGraph sX P B f E Γ)
    (j l : Fin n) :
    IsIntersectionNumber (f ≫ sX) (Divisor.toQDivisor (Finsupp.single (E j) 1))
      (E l).idealSheaf (Γ.matrix j l) := by
  rw [MMP.Threefold.Resolution.toQDivisor_single, Int.cast_one]
  by_cases h : j = l
  · subst h; simpa [WeightedGraph.matrix] using hΓ.weight j
  · simpa [WeightedGraph.matrix, h] using hΓ.edgeWeight j l h

end DualGraph

/-- The underlying graph of the weighted dual graph `Γ(g)` of a resolution `g` of a surface germ
with boundary `(X, P; B)` is preconnected (FA 3.1.2–3.1.6). -/
@[mmp "lem_fa3_dual_graph_connected"]
public theorem IsWeightedDualGraph.preconnected {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X} {g : Y ⟶ X}
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B g E Γ) : Γ.underlyingGraph.Preconnected := by
  intro u v
  by_contra huv
  have hg := hΓ.isGermResolution
  have hE := hΓ.isExceptionalCurveEnumeration
  have : IsProper g := hg.isSmoothResolution.isProper
  have hconn := ((MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism
    (g ≫ sX) sX hg.isVariety hg.isSurfaceGerm.1 g
    hg.isSmoothResolution.isBirationalMorphism).2 P).isPreconnected
  set R : Set (Fin n) := {j | Γ.underlyingGraph.Reachable u j}
  have hEF : ∀ j, ((E j).support : Set Y) ⊆ g.base ⁻¹' {P} :=
    fun j => (hE.isGermExceptionalCurve j).1.prop.2
  have hgen : ∀ j, (E j).genericPoint ∈ ((E j).support : Set Y) := fun j => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hcl : ∀ S : Set (Fin n), IsClosed (⋃ j ∈ S, ((E j).support : Set Y)) := fun S =>
    (Set.toFinite S).isClosed_biUnion fun j _ => (E j).idealSheaf.support.isClosed
  obtain ⟨z, -, hzR, hzR'⟩ := isPreconnected_closed_iff.mp hconn _ _ (hcl R) (hcl Rᶜ)
    (fun y hy => (exists_mem_support_of_isPreconnected hΓ hconn u hy).elim fun j hj =>
      (em (j ∈ R)).imp (Set.mem_biUnion · hj) (Set.mem_biUnion · hj))
    ⟨_, hEF u (hgen u), Set.mem_biUnion (SimpleGraph.Reachable.refl u) (hgen u)⟩
    ⟨_, hEF v (hgen v), Set.mem_biUnion huv (hgen v)⟩
  simp only [Set.mem_iUnion] at hzR hzR'
  obtain ⟨j, hj, hzj⟩ := hzR
  obtain ⟨l, hl, hzl⟩ := hzR'
  exact hl (hj.trans
    (adj_of_mem_inter hΓ (fun h : j = l => hl (h ▸ hj)) ⟨hzj, hzl⟩).symm.reachable)

/-- For a resolution `g` of a surface germ with boundary `(X, P; B)` with exceptional curves
`E_1, …, E_n`, the weighted dual graph `Γ(g)` exists as a weighted graph (FA 3.1.1). Its
self-intersections `(E_j · E_j)` are integers, its genera `p_a(E_j)` are nonnegative integers
(`E_j` is an integral proper curve over an algebraically closed field), its boundary degrees
`(g⁻¹_* B · E_j)` are nonnegative rationals, and its edge weights `(E_j · E_k)` (`j ≠ k`) are
nonnegative integers (sums of local intersection numbers). -/
@[mmp "lem_fa3_dual_graph_is_weighted_graph"]
public theorem IsGermResolution.exists_isWeightedDualGraph {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X} {g : Y ⟶ X}
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} (hg : IsGermResolution sX P g)
    (hB : IsSurfaceGermWithBoundary sX P B) (hE : IsExceptionalCurveEnumeration g P E) :
    ∃ Γ : WeightedGraph (Fin n), IsWeightedDualGraph sX P B g E Γ := by
  classical
  have hsm := hg.isSmoothResolution.isSmoothScheme
  have hEc := hE.isGermExceptionalCurve
  have hprop j := (IsGermExceptionalCurve.isProper sX hg (hEc j)).2
  have hdim1 j : topologicalKrullDim (E j).idealSheaf.subscheme ≤ 1 := (hEc j).2.2.le
  choose d hd using fun j => exists_int_isIntersectionNumber_self hsm (hprop j) (hdim1 j)
  have hgen j : ∃ p : ℕ, IsArithmeticGenusOf (g ≫ sX) (E j) p := by
    haveI := (E j).integral
    haveI := hprop j
    obtain ⟨-, -, h0⟩ := arithmeticGenus_eq_finrank_cohomologyOverField_one
      ((E j).idealSheaf.subschemeι ≫ g ≫ sX) (hdim1 j)
    exact ⟨_, hprop j, Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k
      ((E j).idealSheaf.subschemeι ≫ g ≫ sX), Int.toNat_of_nonneg h0⟩
  choose p hp using hgen
  haveI := hg.isIntegral sX
  have hβ j : ∃ β : ℚ, 0 ≤ β ∧
      IsIntersectionNumber (g ≫ sX) (inverseTransformDivisor g B) (E j).idealSheaf β :=
    exists_nonneg_isIntersectionNumber hg.isVariety hsm hg.topologicalKrullDim_eq (hprop j)
      (hdim1 j) fun _ => nonneg_and_ne_of_mem_support_inverseTransformDivisor hg hB (hEc j)
  choose β hβ0 hβ using hβ
  let m : Fin n → Fin n → ℕ := fun j l => if j = l then 0 else
    ∑ᶠ y ∈ (E l).support ∩ (E j).support,
      localIntersectionNumber (g ≫ sX) y (Finsupp.single (E l) 1) (Finsupp.single (E j) 1)
  refine ⟨⟨fun j => -d j, p, β, hβ0, m, fun j l => ?_, fun j => if_pos rfl⟩, hB, hg, hE,
    fun j => by simpa using hd j, hp, hβ, fun j l hjl => ?_⟩
  · rcases eq_or_ne j l with rfl | hjl
    · rfl
    simp only [m, if_neg hjl, if_neg hjl.symm, Set.inter_comm (E l).support]
    exact finsum_mem_congr rfl fun y _ => by
      rw [localIntersectionNumber, localIntersectionNumber, sup_comm]
  · obtain ⟨hfin, h, -⟩ := isIntersectionNumber_finsum_localIntersectionNumber_of_ne (g ≫ sX)
      hg.isVariety hsm hg.topologicalKrullDim_eq (hE.injective.ne hjl.symm) (hprop l)
    simpa only [m, if_neg hjl, Nat.cast_finsum_mem hfin] using h

/-- A rational matrix is positive definite once its image over `ℝ` is. -/
private theorem posDef_of_posDef_map_ratCast {V : Type*} [Fintype V] {M : Matrix V V ℚ}
    (hM : (M.map ((↑) : ℚ → ℝ)).PosDef) : M.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hM ⊢
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    have := congrFun (congrFun hM.1 i) j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial] at this ⊢
    exact_mod_cast this
  · have hx' : (fun i => (x i : ℝ)) ≠ 0 := fun h => hx (funext fun i => by
      simpa using congrFun h i)
    have h := hM.2 hx'
    simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.map_apply] at h ⊢
    exact_mod_cast h

/-- **Mumford** (FA 3.1.0, 3.1.1). The weighted dual graph `Γ(g)` of a resolution `g` of a
surface germ with boundary `(X, P; B)` is negative definite: the intersection matrix
`((E_j · E_k))` of the exceptional curves is negative definite. -/
@[mmp "lem_fa3_dual_graph_negative_definite"]
public theorem IsWeightedDualGraph.isNegDef {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X} {g : Y ⟶ X}
    [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hΓ : IsWeightedDualGraph sX P B g E Γ) : Γ.IsNegDef := by
  have hg := hΓ.isGermResolution
  have hX := hΓ.isSurfaceGermWithBoundary.1.1
  have := hX.1.toQuasiCompact
  have := hX.2
  have := hg.isSmoothResolution.isProper
  have := hg.isIntegral sX
  have hsm := hg.isSmoothResolution.isSmoothScheme
  have hE := hΓ.isExceptionalCurveEnumeration
  choose C hC hCc using fun i => (hE.isGermExceptionalCurve i).exists_properCurve hg
  apply posDef_of_posDef_map_ratCast
  convert MMP.Threefold.Resolution.posDef_neg_intersectionMatrix_of_isBirationalMorphism
    hg.isVariety hsm hg.topologicalKrullDim_eq hX.1 rfl
    hg.isSmoothResolution.isBirationalMorphism E hE.injective C hC hCc using 1
  ext i j
  simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.of_apply]
  rw [(isIntersectionNumber_matrix hΓ i j).unique (isIntersectionNumber_of_properCurve _
    (MMP.Threefold.Mori.isQCartier_single_of_isSmoothScheme hsm (E i)) (C j) (E j) (hC j))]
  exact Rat.cast_neg _

/-! ### The minimal resolution -/

section Minimal

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {n : ℕ} {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}

/-- `n_j = -(E_j · E_j)` is positive: a diagonal entry of the positive definite `-M(Γ)`. -/
private lemma weight_pos (hΓ : IsWeightedDualGraph sX P B f E Γ) (j : Fin n) :
    0 < Γ.weight j := by
  simpa [WeightedGraph.matrix] using hΓ.isNegDef.diag_pos (i := j)

/-- On a minimal resolution a rational exceptional curve has `n_j ≥ 2`: since `E_j ≅ ℙ¹_k`,
`n_j = 1` would make `E_j` a smooth rational `(-1)`-curve. -/
private lemma two_le_weight_of_genus_eq_zero (hf : IsMinimalGermResolution sX P f)
    (hΓ : IsWeightedDualGraph sX P B f E Γ) {j : Fin n} (hp : Γ.genus j = 0) :
    2 ≤ Γ.weight j := by
  by_contra hlt
  have h1 : Γ.weight j = 1 := by have := weight_pos hΓ j; omega
  apply hf.2
  have hE := hΓ.isExceptionalCurveEnumeration.isGermExceptionalCurve j
  obtain ⟨hcurve, hprop⟩ := IsGermExceptionalCurve.isProper sX hf.1 hE
  have : IsIntegral (E j).idealSheaf.subscheme := hcurve.1
  obtain ⟨_, _, hg⟩ := hΓ.genus j
  obtain ⟨e, he⟩ := ((arithmeticGenus_nonneg_and_eq_zero_iff
    ((E j).idealSheaf.subschemeι ≫ f ≫ sX) hcurve.2).2).mp (by rw [← hg, hp]; rfl)
  refine ⟨E j, hE, ⟨⟨hcurve, hprop, e.hom, he, inferInstance,
    isBirationalMorphism_of_isIso _⟩, e, he⟩, ?_⟩
  simpa [h1] using hΓ.weight j

/-- On a minimal resolution no vertex has `p_j = 0` and `n_j = 1`. -/
private lemma not_genus_eq_zero_and_weight_eq_one (hf : IsMinimalGermResolution sX P f)
    (hΓ : IsWeightedDualGraph sX P B f E Γ) (j : Fin n) :
    ¬(Γ.genus j = 0 ∧ Γ.weight j = 1) := fun ⟨h0, h1⟩ => by
  have := two_le_weight_of_genus_eq_zero hf hΓ h0
  omega

end Minimal

/-- For a minimal resolution `f` of a surface germ with boundary `(X, P; B)` over an algebraically
closed field, with exceptional curves `E_1, …, E_n` and weighted dual graph `Γ = Γ(f)`, every
`d_j(Γ) = 2 - 2p_j - n_j - β_j` is nonpositive (FA 3.1.1). -/
@[mmp "lem_fa3_minimal_resolution_dj_nonpositive"]
public theorem IsMinimalGermResolution.d_nonpos {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X} {B : QDivisor X} {f : Y ⟶ X}
    [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] {n : ℕ}
    {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P B f E Γ) (j : Fin n) :
    Γ.d j ≤ 0 := by
  have hβ := Γ.boundary_nonneg j
  rw [WeightedGraph.d]
  rcases Nat.eq_zero_or_pos (Γ.genus j) with hp | hp
  · have : (2 : ℚ) ≤ Γ.weight j := by exact_mod_cast two_le_weight_of_genus_eq_zero hf hΓ hp
    simp only [hp, Nat.cast_zero]
    linarith
  · have : (1 : ℚ) ≤ Γ.genus j := by exact_mod_cast hp
    have : (1 : ℚ) ≤ Γ.weight j := by exact_mod_cast weight_pos hΓ j
    linarith

/-! ### Edge weights over a log canonical germ -/

section PairGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The weights at two distinct vertices of a negative definite graph are positive and their
product exceeds the square of the edge weight: the `2 × 2` principal minors of `-M(Γ)`. -/
private lemma weight_pos_and_sq_lt {Γ : WeightedGraph V} (hΓ : Γ.IsNegDef) {j l : V}
    (hjl : j ≠ l) :
    0 < (Γ.weight j : ℚ) ∧ 0 < (Γ.weight l : ℚ) ∧
      (Γ.edgeWeight j l : ℚ) ^ 2 < Γ.weight j * Γ.weight l := by
  have hP := hΓ.submatrix (show Function.Injective ![j, l] by
    intro x y h; fin_cases x <;> fin_cases y <;> simp_all [eq_comm])
  have h0 : (0 : ℚ) < Γ.weight j := by simpa [WeightedGraph.matrix] using hP.diag_pos (i := 0)
  have h1 : (0 : ℚ) < Γ.weight l := by simpa [WeightedGraph.matrix] using hP.diag_pos (i := 1)
  have h2 := hP.dotProduct_mulVec_pos (x := ![(Γ.edgeWeight j l : ℚ), Γ.weight j])
    fun h => by simpa [h0.ne'] using congrFun h 1
  simp [WeightedGraph.matrix, hjl, Ne.symm hjl, Γ.edgeWeight_symm l j, dotProduct,
    Matrix.mulVec, Fin.sum_univ_two] at h2
  have h3 : 0 < (Γ.weight j : ℚ) * (Γ.weight j * Γ.weight l - (Γ.edgeWeight j l : ℚ) ^ 2) := by
    linarith
  exact ⟨h0, h1, by linarith [pos_of_mul_pos_right h3 h0.le]⟩

/-- A sum over the two-element vertex set `{j, l}` has two terms. -/
private lemma sum_univ_pair {j l : V} (hjl : j ≠ l) {M : Type*} [AddCommMonoid M]
    (f : ({j, l} : Finset V) → M) : ∑ k, f k = f ⟨j, by simp⟩ + f ⟨l, by simp⟩ :=
  Fintype.sum_eq_add _ _ (by simpa using hjl) fun ⟨_, hx⟩ h =>
    absurd hx (by simpa [Subtype.ext_iff] using h)

/-- The two-vertex graph on `{v_j, v_l}` with the weights of `Γ`, edge weight `m_{jl}` and
`p' = β' = 0`. -/
private def pairGraph (Γ : WeightedGraph V) (j l : V) : WeightedGraph ({j, l} : Finset V) where
  weight v := Γ.weight v
  genus _ := 0
  boundary _ := 0
  boundary_nonneg _ := le_rfl
  edgeWeight v w := if v = w then 0 else Γ.edgeWeight j l
  edgeWeight_symm v w := by simp [eq_comm]
  edgeWeight_self v := by simp

private lemma pairGraph_isSubgraph (Γ : WeightedGraph V) (j l : V) :
    (pairGraph Γ j l).IsSubgraph Γ := by
  refine ⟨fun _ => rfl, ?_, fun _ => Nat.zero_le _, fun v => Γ.boundary_nonneg v⟩
  rintro ⟨v, hv⟩ ⟨w, hw⟩ hvw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
    simp_all [pairGraph, Γ.edgeWeight_symm]

/-- The log discrepancy vector of `pairGraph Γ j l`: with `m = m_{jl}` and
`D = n_j n_l - m² ≠ 0`, it is `(m - 2) (-(n_l + m), -(n_j + m)) / D`. -/
private lemma pairGraph_isLogDiscrepancyVector (Γ : WeightedGraph V) {j l : V} (hjl : j ≠ l)
    (hD : (Γ.weight j * Γ.weight l : ℚ) - (Γ.edgeWeight j l : ℚ) ^ 2 ≠ 0) :
    (pairGraph Γ j l).IsLogDiscrepancyVector fun v =>
      ((Γ.edgeWeight j l : ℚ) - 2) *
        -((if (v : V) = j then Γ.weight l else Γ.weight j) + Γ.edgeWeight j l) /
        (Γ.weight j * Γ.weight l - (Γ.edgeWeight j l : ℚ) ^ 2) := by
  generalize hD' : (Γ.weight j * Γ.weight l : ℚ) - (Γ.edgeWeight j l : ℚ) ^ 2 = D at hD ⊢
  rintro ⟨i, hi⟩
  simp only [WeightedGraph.c, WeightedGraph.matrix, pairGraph, Matrix.of_apply, Subtype.ext_iff,
    Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_univ_pair hjl]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl <;> simp [hjl, Ne.symm hjl] <;> field_simp <;> subst hD' <;> ring

/-- FA 3.1.6.1 for weighted graphs: nonnegative log discrepancies of a negative definite graph
with all `d_j ≤ 0` force `m_{jk} ≤ 2`. For `m_{jk} ≥ 3`, the log discrepancy of `pairGraph`
at `v_j` is negative, and `IsLogDiscrepancyVector.le_of_isSubgraph` bounds `a_j` by it. -/
private lemma edgeWeight_le_two {Γ : WeightedGraph V} (hΓ : Γ.IsNegDef)
    (hd : ∀ j, Γ.d j ≤ 0) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ j, 0 ≤ a j)
    (j l : V) : Γ.edgeWeight j l ≤ 2 := by
  obtain rfl | hjl := eq_or_ne j l
  · simp [Γ.edgeWeight_self]
  by_contra! hm
  obtain ⟨hnj, hnl, hD⟩ := weight_pos_and_sq_lt hΓ hjl
  have hle := ha.le_of_isSubgraph (pairGraph_isLogDiscrepancyVector Γ hjl (by linarith))
    (pairGraph_isSubgraph Γ j l) hΓ hd ⟨j, by simp⟩
  have hm3 : (3 : ℚ) ≤ Γ.edgeWeight j l := by exact_mod_cast hm
  have : ((Γ.edgeWeight j l : ℚ) - 2) * -(Γ.weight l + Γ.edgeWeight j l) /
      (Γ.weight j * Γ.weight l - (Γ.edgeWeight j l : ℚ) ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) (by linarith)
  simp only [if_true] at hle
  linarith [ha0 j]

end PairGraph

/-- **Edge weights are at most two over a log canonical germ** (FA 3.1.6.1). Let `f` be a minimal
resolution of a surface germ with boundary `(X, P; B)` over an algebraically closed field, with
exceptional curves `E_1, …, E_n` and weighted dual graph `Γ = Γ(f)`. If the log discrepancy vector
`a` of `Γ` has all entries `a_j ≥ 0`, then `m_{jl}(Γ) ≤ 2` for all `j, l` (for `j ≠ l` this is
`(E_j · E_l)`, and `m_{jj} = 0` by convention). -/
@[mmp "lem_fa3_lc_edge_weight_at_most_two"]
public theorem IsMinimalGermResolution.edgeWeight_le_two_of_logDiscrepancy_nonneg {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P B f E Γ)
    {a : Fin n → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ j, 0 ≤ a j) (j l : Fin n) :
    Γ.edgeWeight j l ≤ 2 :=
  edgeWeight_le_two hΓ.isNegDef (hf.d_nonpos hΓ) ha ha0 j l

/-! ### Genera over a log canonical germ -/

section GenusOne

variable {n : ℕ}

/-- The one-vertex weighted graph on `{v}` with weight `w`, genus `1`, boundary `0`. -/
private def genusOneVertex (v : Fin n) (w : ℤ) : WeightedGraph ({v} : Finset (Fin n)) where
  weight _ := w
  genus _ := 1
  boundary _ := 0
  boundary_nonneg _ := le_rfl
  edgeWeight _ _ := 0
  edgeWeight_symm _ _ := rfl
  edgeWeight_self _ := rfl

private lemma genusOneVertex_isLogDiscrepancyVector (v : Fin n) (w : ℤ) :
    (genusOneVertex v w).IsLogDiscrepancyVector 0 := by
  intro j
  simp [WeightedGraph.c, genusOneVertex]

/-- A vertex of genus at least `1` carries the one-vertex genus-`1` graph as a subgraph. -/
private lemma genusOneVertex_isSubgraph {Γ : WeightedGraph (Fin n)} {j : Fin n}
    (hj : 1 ≤ Γ.genus j) : (genusOneVertex j (Γ.weight j)).IsSubgraph Γ where
  weight_eq := by rintro ⟨i, hi⟩; obtain rfl := Finset.mem_singleton.mp hi; rfl
  edgeWeight_le _ _ _ := Nat.zero_le _
  genus_le := by rintro ⟨i, hi⟩; obtain rfl := Finset.mem_singleton.mp hi; exact hj
  boundary_le _ := Γ.boundary_nonneg _

variable {k : Type u} [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {P : X} {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y]
    [IsNormal Y] {E : Fin n → MMP.Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}

/-- If the one-vertex genus-`1` graph at a vertex `v_j` of genus `p_j ≥ 1` is a proper subgraph
of the dual graph of a minimal resolution, the log discrepancy `a_j` is negative: its own log
discrepancy vector is `0`, and `IsLogDiscrepancyVector.lt_of_isSubgraph` applies since `Γ` is
not Du Val (`p_j ≠ 0`). -/
private lemma logDiscrepancy_neg_of_ne (hf : IsMinimalGermResolution sX P f)
    (hΓ : IsWeightedDualGraph sX P B f E Γ) {a : Fin n → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    {j : Fin n} (hj : 1 ≤ Γ.genus j)
    (hne : ({j} : Finset (Fin n)) ≠ Finset.univ ∨
      genusOneVertex j (Γ.weight j) ≠ Γ.restrict {j}) :
    a j < 0 := by
  haveI : Nonempty (Fin n) := ⟨j⟩
  simpa using ha.lt_of_isSubgraph (genusOneVertex_isLogDiscrepancyVector j _)
    (genusOneVertex_isSubgraph hj) hne hΓ.isNegDef ⟨hΓ.preconnected⟩ (hf.d_nonpos hΓ)
    (not_genus_eq_zero_and_weight_eq_one hf hΓ) (fun h => by have := (h j).1; omega)
    ⟨j, Finset.mem_singleton_self j⟩

end GenusOne

/-- **No exceptional curve of genus `≥ 2` over a log canonical germ** (FA 3.1.6.1). Let `f` be a
minimal resolution of a surface germ with boundary `(X, P; B)` over an algebraically closed field,
with exceptional curves `E_1, …, E_n` and weighted dual graph `Γ = Γ(f)`. If the log discrepancy
vector `a` of `Γ` has all entries `a_j ≥ 0`, then `p_a(E_j) = p_j(Γ) ≤ 1` for every `j`. -/
@[mmp "lem_fa3_lc_no_genus_two_vertex"]
public theorem IsMinimalGermResolution.genus_le_one_of_logDiscrepancy_nonneg {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P B f E Γ)
    {a : Fin n → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ j, 0 ≤ a j) (j : Fin n) :
    Γ.genus j ≤ 1 := by
  by_contra! hj
  refine (ha0 j).not_gt (logDiscrepancy_neg_of_ne hf hΓ ha hj.le (.inr fun h => ?_))
  have := congrArg (fun G => G.genus ⟨j, Finset.mem_singleton_self j⟩) h
  simp [genusOneVertex, WeightedGraph.restrict] at this
  omega

/-- **A genus-one vertex forces a single vertex** (FA 3.1.6.2 with 3.1.4). Let `f` be a minimal
resolution of a surface germ with boundary `(X, P; B)` over an algebraically closed field, with
exceptional curves `E_1, …, E_n` and weighted dual graph `Γ = Γ(f)`. If the log discrepancy
vector `a` of `Γ` has all entries `a_k ≥ 0` and `p_a(E_j) = p_j(Γ) = 1` for some `j`, then
`n = 1` and `β_j(Γ) = 0`. -/
@[mmp "lem_fa3_lc_genus_one_forces_single_vertex"]
public theorem IsMinimalGermResolution.eq_one_and_boundary_eq_zero_of_genus_eq_one {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P B f E Γ)
    {a : Fin n → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ i, 0 ≤ a i) {j : Fin n}
    (hj : Γ.genus j = 1) :
    n = 1 ∧ Γ.boundary j = 0 := by
  by_contra hcon
  refine (ha0 j).not_gt (logDiscrepancy_neg_of_ne hf hΓ ha hj.ge ?_)
  by_cases hn : n = 1
  · refine .inr fun h => hcon ⟨hn, ?_⟩
    simpa [genusOneVertex, WeightedGraph.restrict] using
      (congrArg (fun G => G.boundary ⟨j, Finset.mem_singleton_self j⟩) h).symm
  · exact .inl fun h => hn (by simpa using (congrArg Finset.card h).symm)

/-! ### Cycles over a log canonical germ -/

section Circle

open Finset

/-- The edge weights of the circle of length `l` on `Fin l`. -/
private def circleEdgeWeight (l : ℕ) (p q : Fin l) : ℕ :=
  if p ≠ q ∧ (((p : ℕ) + 1) % l = q ∨ ((q : ℕ) + 1) % l = p) then (if l = 2 then 2 else 1) else 0

private lemma circleEdgeWeight_symm (l : ℕ) (p q : Fin l) :
    circleEdgeWeight l p q = circleEdgeWeight l q p := by
  unfold circleEdgeWeight
  by_cases h : p = q
  · subst h; rfl
  · simp only [ne_eq, h, not_false_eq_true, true_and, Ne.symm h, or_comm]

private lemma circleEdgeWeight_self (l : ℕ) (p : Fin l) : circleEdgeWeight l p p = 0 := by
  simp [circleEdgeWeight]

private lemma succ_mod_eq_iff {l i j : ℕ} (hi : i < l) (hj : j < l) :
    (i + 1) % l = j ↔ (i + 1 < l ∧ j = i + 1) ∨ (i + 1 = l ∧ j = 0) := by
  rcases Nat.lt_or_ge (i + 1) l with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have : i + 1 = l := by omega
    rw [this, Nat.mod_self]; omega

/-- Every vertex of a circle of length `l ≥ 2` has total edge weight `2`. -/
private lemma sum_circleEdgeWeight {l : ℕ} (hl : 2 ≤ l) (p : Fin l) :
    ∑ q, circleEdgeWeight l p q = 2 := by
  rcases Nat.lt_or_ge l 3 with h3 | h3
  · obtain rfl : l = 2 := by omega
    fin_cases p <;> decide
  · have hne : l ≠ 2 := by omega
    have hp := p.isLt
    set pp : ℕ := if (p : ℕ) + 1 = l then 0 else (p : ℕ) + 1 with hpp
    set pm : ℕ := if (p : ℕ) = 0 then l - 1 else (p : ℕ) - 1 with hpm
    have hpp' : pp < l := by rw [hpp]; split_ifs <;> omega
    have hpm' : pm < l := by rw [hpm]; split_ifs <;> omega
    have hfilt : (univ.filter fun q : Fin l => p ≠ q ∧
        (((p : ℕ) + 1) % l = q ∨ ((q : ℕ) + 1) % l = p)) = {⟨pp, hpp'⟩, ⟨pm, hpm'⟩} := by
      ext q
      have hq := q.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Fin.ext_iff, ne_eq]
      rw [succ_mod_eq_iff hp hq, succ_mod_eq_iff hq hp, hpp, hpm]
      split_ifs <;> omega
    have hdist : (⟨pp, hpp'⟩ : Fin l) ≠ ⟨pm, hpm'⟩ := by
      simp only [ne_eq, Fin.mk.injEq, hpp, hpm]
      split_ifs <;> omega
    unfold circleEdgeWeight
    rw [← Finset.sum_filter, hfilt, Finset.sum_pair hdist]
    simp [hne]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph carrying the edges of a circle on `v : Fin l ↪ V` is not Du Val: otherwise the
indicator vector `x` of the image of `v` would have `xᵀ M(Γ) x ≥ 0`, since every row of `M(Γ)`
restricted to the image sums to at least `∑_q circleEdgeWeight l p q - 2 = 0`. -/
private lemma not_isDuVal_of_circle {Γ : WeightedGraph V} (hΓ : Γ.IsNegDef)
    {l : ℕ} (hl : 2 ≤ l) (v : Fin l → V) (hv : Function.Injective v)
    (hedge : ∀ p q, circleEdgeWeight l p q ≤ Γ.edgeWeight (v p) (v q)) : ¬Γ.IsDuVal := by
  intro hdv
  set S : Finset V := univ.map ⟨v, hv⟩ with hS
  have hx : (fun y => if y ∈ S then (1 : ℚ) else 0) ≠ 0 := by
    intro h
    have := congrFun h (v ⟨0, by omega⟩)
    simp [S] at this
  have hpos := hΓ.dotProduct_mulVec_pos hx
  simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.neg_apply, Matrix.map_apply,
    ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero] at hpos
  simp only [Function.Embedding.coeFn_mk, Finset.sum_ite_mem, univ_inter, hS, Finset.sum_map,
    Finset.sum_neg_distrib] at hpos
  have hrow : ∀ p, 0 ≤ ∑ q, ((Γ.matrix (v p) (v q) : ℤ) : ℚ) := fun p =>
    calc (0 : ℚ) = ∑ q, ((circleEdgeWeight l p q : ℚ) - if p = q then 2 else 0) := by
          rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_circleEdgeWeight hl]; simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => by
          simp only [WeightedGraph.matrix, Matrix.of_apply, hv.eq_iff]
          split_ifs with h
          · subst h; simp [circleEdgeWeight_self, (hdv (v p)).2.1]
          · simpa using hedge p q
  linarith [Finset.sum_nonneg fun p (_ : p ∈ univ) => hrow p]

/-- **The circle criterion.** Let `Γ` be negative definite and connected with `d_j ≤ 0`, no
genus-`0` vertex of weight `1`, and `a(Γ) ≥ 0`. If `v : Fin l ↪ V` (`l ≥ 2`) carries the edges of
a circle of length `l` (with at least the circle's weights), then `v` is a bijection exhibiting
`Γ` as a circle: the circle `Γ'` on the image, with `p' = β' = 0`, is a subgraph with
`a(Γ') = 0`, and strict monotonicity of log discrepancies forces `Γ' = Γ`. -/
private lemma exists_isCircleOrder {Γ : WeightedGraph V} (hΓ : Γ.IsNegDef)
    (hconn : Γ.IsConnected) (hd : ∀ j, Γ.d j ≤ 0) (hp1 : ∀ j, ¬(Γ.genus j = 0 ∧ Γ.weight j = 1))
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ j, 0 ≤ a j)
    {l : ℕ} (hl : 2 ≤ l) (v : Fin l → V) (hv : Function.Injective v)
    (hedge : ∀ p q, circleEdgeWeight l p q ≤ Γ.edgeWeight (v p) (v q)) :
    ∃ e : Fin l ≃ V, Γ.IsCircleOrder e := by
  set S : Finset V := univ.map ⟨v, hv⟩
  have hmemS : ∀ p, v p ∈ S := fun p => by simp [S]
  let σ : Fin l ≃ S := Equiv.ofBijective (fun p => ⟨v p, hmemS p⟩) (by
    refine ⟨fun p q h => hv (congrArg Subtype.val h), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hx
    exact ⟨p, rfl⟩)
  have hσ : ∀ p, ((σ p : S) : V) = v p := fun _ => rfl
  let Γ' : WeightedGraph S :=
    { weight := fun x => Γ.weight x
      genus := fun _ => 0
      boundary := fun _ => 0
      boundary_nonneg := fun _ => le_rfl
      edgeWeight := fun x y => circleEdgeWeight l (σ.symm x) (σ.symm y)
      edgeWeight_symm := fun x y => circleEdgeWeight_symm _ _ _
      edgeWeight_self := fun x => circleEdgeWeight_self _ _ }
  have hsumS : ∀ x : S, ∑ y ∈ (univ : Finset S).erase x, (Γ'.edgeWeight x y : ℚ) = 2 := by
    intro x
    rw [Finset.sum_erase _ (by simp [Γ', circleEdgeWeight_self])]
    have := Equiv.sum_comp σ (fun y => (circleEdgeWeight l (σ.symm x) (σ.symm y) : ℚ))
    simp only [Equiv.symm_apply_apply] at this
    simp only [Γ']
    rw [← this, ← Nat.cast_sum, sum_circleEdgeWeight hl]
    norm_num
  have ha' : Γ'.IsLogDiscrepancyVector 0 := fun x => by
    simp only [WeightedGraph.c, hsumS] at *
    simp [Γ']
  have hsub : Γ'.IsSubgraph Γ := by
    refine ⟨fun _ => rfl, ?_, fun _ => Nat.zero_le _, fun _ => Γ.boundary_nonneg _⟩
    intro x y _
    obtain ⟨p, rfl⟩ := σ.surjective x
    obtain ⟨q, rfl⟩ := σ.surjective y
    show circleEdgeWeight l (σ.symm (σ p)) (σ.symm (σ q)) ≤ Γ.edgeWeight (v p) (v q)
    simpa using hedge p q
  have hnot : ¬(S ≠ univ ∨ Γ' ≠ Γ.restrict S) := by
    intro hne
    have := ha.lt_of_isSubgraph ha' hsub hne hΓ hconn hd hp1
      (not_isDuVal_of_circle hΓ hl v hv hedge) (σ ⟨0, by omega⟩)
    simp only [Pi.zero_apply] at this
    linarith [ha0 (σ ⟨0, by omega⟩ : V)]
  push Not at hnot
  obtain ⟨hSu, hΓ'⟩ := hnot
  have hsurj : Function.Surjective v := by
    intro y
    obtain ⟨p, -, hp⟩ := Finset.mem_map.1 (hSu ▸ mem_univ y : y ∈ S)
    exact ⟨p, hp⟩
  refine ⟨Equiv.ofBijective v ⟨hv, hsurj⟩, hl, fun p => ?_, fun p => ?_, ?_, ?_⟩
  · have := congrArg (fun G => G.genus (σ p)) hΓ'
    simp only [Γ', WeightedGraph.restrict] at this
    exact this.symm
  · have := congrArg (fun G => G.boundary (σ p)) hΓ'
    simp only [Γ', WeightedGraph.restrict] at this
    exact this.symm
  · intro h3 p q hpq
    have := congrArg (fun G => G.edgeWeight (σ p) (σ q)) hΓ'
    simp only [Γ', WeightedGraph.restrict, Equiv.symm_apply_apply, hσ] at this
    show Γ.edgeWeight (v p) (v q) = _
    rw [← this]
    simp [circleEdgeWeight, hpq, show l ≠ 2 by omega]
  · intro h2
    have := congrArg (fun G => G.edgeWeight (σ ⟨0, by omega⟩) (σ ⟨1, by omega⟩)) hΓ'
    simp only [Γ', WeightedGraph.restrict, Equiv.symm_apply_apply, hσ] at this
    show Γ.edgeWeight (v _) (v _) = 2
    rw [← this]
    simp [circleEdgeWeight, h2]

end Circle

/-- **A cycle forces a circle over a log canonical germ** (FA 3.1.5, 3.1.6.2). Let `f` be a
minimal resolution of a surface germ with boundary `(X, P; B)` over an algebraically closed field,
with exceptional curves `E_1, …, E_n` and weighted dual graph `Γ = Γ(f)`. If the log discrepancy
vector `a` of `Γ` has all entries `a_j ≥ 0`, every vertex has genus `p_j = 0`, and the underlying
graph of `Γ` has a cycle or an edge of weight `m_{jk} ≥ 2`, then `Γ` is a circle of length `n`. -/
@[mmp "lem_fa3_lc_cycle_forces_circle"]
public theorem IsMinimalGermResolution.isCircle_of_logDiscrepancy_nonneg {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P B f E Γ)
    {a : Fin n → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ j, 0 ≤ a j)
    (hp : ∀ j, Γ.genus j = 0) (hcyc : ¬ Γ.IsAcyclic ∨ ∃ j l, 2 ≤ Γ.edgeWeight j l) :
    Γ.IsCircle n := by
  have key : ∀ {l : ℕ} (hl : 2 ≤ l) (v : Fin l → Fin n), Function.Injective v →
      (∀ p q, circleEdgeWeight l p q ≤ Γ.edgeWeight (v p) (v q)) → Γ.IsCircle n := by
    intro l hl v hv hedge
    haveI : Nonempty (Fin n) := ⟨v ⟨0, by omega⟩⟩
    obtain ⟨e, he⟩ := exists_isCircleOrder hΓ.isNegDef ⟨hΓ.preconnected⟩ (hf.d_nonpos hΓ)
      (not_genus_eq_zero_and_weight_eq_one hf hΓ) ha ha0 hl v hv hedge
    obtain rfl : l = n := by simpa using Fintype.card_congr e
    exact ⟨e, he⟩
  rcases hcyc with hcyc | ⟨j, j', hjj'⟩
  · simp only [WeightedGraph.IsAcyclic, SimpleGraph.IsAcyclic, not_forall, not_not] at hcyc
    obtain ⟨u, c, hc⟩ := hcyc
    have h3 := hc.three_le_length
    have hgv : ∀ p : Fin c.length, c.getVert (((p : ℕ) + 1) % c.length) = c.getVert (p + 1) := by
      intro p
      rcases Nat.lt_or_ge ((p : ℕ) + 1) c.length with h | h
      · rw [Nat.mod_eq_of_lt h]
      · rw [show (p : ℕ) + 1 = c.length by omega, Nat.mod_self, c.getVert_zero,
          c.getVert_length]
    have hadj : ∀ p : Fin c.length, 0 < Γ.edgeWeight (c.getVert p)
        (c.getVert (((p : ℕ) + 1) % c.length)) := fun p => by
      rw [hgv]
      exact (c.adj_getVert_succ p.isLt).2
    refine key (l := c.length) (by omega) (fun p => c.getVert p) ?_ ?_
    · intro p q h
      exact Fin.ext (hc.getVert_injOn' (show (p : ℕ) ∈ {i | i ≤ c.length - 1} by
        simp only [Set.mem_setOf_eq]; omega) (show (q : ℕ) ∈ {i | i ≤ c.length - 1} by
        simp only [Set.mem_setOf_eq]; omega) h)
    · intro p q
      unfold circleEdgeWeight
      split_ifs with h h2
      · omega
      · rcases h.2 with h' | h'
        · have := hadj p; rw [h'] at this; exact this
        · have := hadj q; rw [h', Γ.edgeWeight_symm] at this; exact this
      · exact Nat.zero_le _
  · have hne : j ≠ j' := by rintro rfl; simp [Γ.edgeWeight_self] at hjj'
    refine key le_rfl ![j, j'] ?_ ?_
    · intro x y h
      fin_cases x <;> fin_cases y <;> simp_all [eq_comm]
    · intro p q
      fin_cases p <;> fin_cases q <;>
        simp [circleEdgeWeight, Γ.edgeWeight_self, hjj', Γ.edgeWeight_symm j' j]

/-! ### The tree case -/

/-- **The tree case of a log canonical germ** (FA 3.1.6.2). Let `f` be a minimal resolution of a
surface germ with boundary `(X, P; B)` over an algebraically closed field, with exceptional
curves `E_1, …, E_n` and weighted dual graph `Γ = Γ(f)`. If the log discrepancy vector `a` of
`Γ` has all entries `a_j ≥ 0`, and `Γ` is neither a single vertex with `p_1 = 1`, `β_1 = 0` nor a
circle, then `Γ` is a rational tree. -/
@[mmp "lem_fa3_lc_tree_case"]
public theorem IsMinimalGermResolution.isRationalTree_of_logDiscrepancy_nonneg {k : Type u}
    [Field k] [IsAlgClosed k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {P : X}
    {B : QDivisor X} {f : Y ⟶ X} [QuasiCompact (f ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y]
    {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y} {Γ : WeightedGraph (Fin n)}
    (hf : IsMinimalGermResolution sX P f) (hΓ : IsWeightedDualGraph sX P B f E Γ)
    {a : Fin n → ℚ} (ha : Γ.IsLogDiscrepancyVector a) (ha0 : ∀ j, 0 ≤ a j)
    (hsingle : ¬ (n = 1 ∧ ∀ j, Γ.genus j = 1 ∧ Γ.boundary j = 0))
    (hcirc : ¬ Γ.IsCircle n) :
    Γ.IsRationalTree := by
  have hp : ∀ j, Γ.genus j = 0 := by
    intro j
    have hle := hf.genus_le_one_of_logDiscrepancy_nonneg hΓ ha ha0 j
    by_contra hne
    have h1 : Γ.genus j = 1 := by omega
    obtain ⟨rfl, hβ⟩ := hf.eq_one_and_boundary_eq_zero_of_genus_eq_one hΓ ha ha0 h1
    exact hsingle ⟨rfl, fun i => Subsingleton.elim j i ▸ ⟨h1, hβ⟩⟩
  have hcyc : ¬ (¬ Γ.IsAcyclic ∨ ∃ j l, 2 ≤ Γ.edgeWeight j l) := fun h =>
    hcirc (hf.isCircle_of_logDiscrepancy_nonneg hΓ ha ha0 hp h)
  push Not at hcyc
  obtain ⟨hacyc, hedge⟩ := hcyc
  refine ⟨hp, fun j => two_le_weight_of_genus_eq_zero hf hΓ (hp j),
    fun j l => by have := hedge j l; omega, ?_⟩
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact Or.inr h
  · exact Or.inl ⟨⟨hΓ.preconnected⟩, hacyc⟩

end MMP.Flips
