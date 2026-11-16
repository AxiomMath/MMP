module

public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.Combinatorics.WeightedGraph.Shapes
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.Combinatorics.WeightedGraph.ForestPermutations
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection

/-!
# Determinants of weighted chains, curves, exceptional divisors and eventually free divisors

This file collects several basic results from [KollarFlips], §§2, 3 and 15.

* **Determinants of weighted graphs.** For a weighted graph `Γ` write `Δ(Γ) = det(-M(Γ))`. If `Γ`
  has simple edges and no cycles, `Δ` expands along a vertex `v` of weight `n_v` as
  `Δ(Γ) = n_v Δ(Γ - v) - ∑_{w ∼ v} Δ(Γ - v - w)`: in the permutation expansion of the
  determinant, the permutations fixing `v` give the first term, and a permutation sending `v` to a
  neighbour `w` with a nonzero term is, the graph being a forest, the transposition `(v w)` times a
  permutation of `V ∖ {v, w}`. For a chain `v_1, …, v_s` with all weights `≥ 2` the expansion at
  the end `v_1` gives `Δ(Γ - v_1) ≥ 1` and `Δ(Γ) ≥ Δ(Γ - v_1) + 1`, hence `Δ(Γ) ≥ s + 1`, and
  `Δ(Γ) = 2` exactly when the chain is a single vertex of weight `2`.
* **Intersection numbers of `ℝ`-Cartier divisors.** For a proper curve `C` on a normal variety the
  number `L · C` of a Cartier divisor is the degree of `𝒪_X(L)` along `C`, whichever
  normalization of `C` computes it, since a normalization is birational and so of degree one. So
  `L ↦ L · C` is additive and induces `Ca(X) ⊗ ℝ → ℝ`; hence `D · C = ∑ r_j (L_j · C)` does not
  depend on the presentation `D = ∑ r_j L_j` and is `ℝ`-linear in `D`.
* **Lifting curves.** Along a proper surjective morphism `h : A ⟶ B` of schemes of finite type
  over `ℂ`, every proper curve `C' ⊆ B` is the image of a proper curve: the closure of a point
  closed in the fibre of `h` over the generic point of `C'`.
* **Exceptional divisors of a birational map.** If `φ : X ⤏ Y` is a birational map of normal
  varieties which is a morphism in codimension one, only finitely many prime divisors of `Y` are
  `φ⁻¹`-exceptional, their generic points lying outside a dense open on which `φ⁻¹` is an
  isomorphism; if `φ` is an inverse of a proper morphism `g : Y ⟶ X`, these are the prime divisors
  exceptional over `X`.
* **Eventually free divisors.** If `p : X ⟶ Y` is a proper morphism of normal varieties with
  `p_* 𝒪_X = 𝒪_Y` and `L ∼_ℚ p^* N`, then `L` is eventually free iff `N` is. A complete linear
  system `|M|` is basepoint free exactly when every point `y` has a rational function `φ` with
  `M + div φ` effective and of coefficient zero along every prime divisor through `y`. This
  pulls back along the dominant `p`; conversely, `p_* 𝒪_X = 𝒪_Y` makes every such function on `X`
  for `p^* M` the pull-back of one on `Y` for `M`, and the stalk maps of `p` being local, it
  descends the vanishing condition along the surjective `p`.

## Main results

* `MMP.Flips.WeightedGraph.det_eq_weight_mul_delta_sub_sum_delta`: the vertex expansion of `Δ`.
* `MMP.Flips.WeightedGraph.one_le_delta_and_delta_add_one_le_det_of_isChainOrder`:
  `Δ(Γ - v_1) ≥ 1` and `Δ(Γ) ≥ Δ(Γ - v_1) + 1` for a chain with weights `≥ 2`.
* `MMP.Flips.WeightedGraph.add_one_le_det_of_isChainOrder`: `Δ(Γ) ≥ s + 1` for such a chain.
* `MMP.Flips.WeightedGraph.det_eq_two_iff_of_isChainOrder`: `Δ(Γ) = 2` iff `s = 1` and `n_1 = 2`.
* `MMP.Flips.IsRIntersectionNumber.eq_and_linear`: `D · C` is well defined and `ℝ`-linear.
* `MMP.Mori.ProperCurve.exists_map_eq`: proper curves lift along proper surjective morphisms.
* `MMP.Flips.RationalMap.finite_setOf_isInverseExceptional`: finiteness of the
  `φ⁻¹`-exceptional prime divisors, and their identification with the `g`-exceptional ones.
* `MMP.Flips.isEventuallyFree_iff_of_qLinearlyEquivalent_pullback`: eventual freeness under a
  crepant morphism with `p_* 𝒪_X = 𝒪_Y`.

## Implementation notes

A chain `v_1, …, v_s` is an enumeration `e : Fin s ≃ V` with `Γ.IsChainOrder e`, and
`Δ(Γ - S)` is `Γ.delta (univ \ S)`. The dimension count in the lifting of curves is topological:
`dim {a}⁻ = dim (fibre over ξ) + dim {ξ}⁻`, the fibre over the generic point `ξ` of `C'` being
the single point `a`; this replaces the transcendence-degree count of the source. The source
states the result on eventually free divisors for `L = K_X + Δ_X` and `N = K_Y + Δ_Y` with `Δ_X`,
`Δ_Y` arbitrary `ℚ`-divisors, that is, for arbitrary `ℚ`-divisors `L` and `N`; the condition
`p_* 𝒪_X = 𝒪_Y` is `∀ U, IsIso (p.app U)`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.7, 2.11.2,
  3.1.8, 3.1.11, (3.2.2)–(3.2.5), 15.4.4
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-! ### The vertex expansion of the determinant of a weighted forest -/

namespace MMP.Flips.WeightedGraph

open Finset Equiv

/-- The part of the permutation expansion of `det A` over the permutations agreeing with `π`
outside `T`, where `π` fixes `T` pointwise, is `sgn π ∏_{i ∉ T} A_{π i, i} · det A|_T`. -/
private theorem sum_perm_agree_eq {V : Type*} [Fintype V] [DecidableEq V] {R : Type*}
    [CommRing R] (A : Matrix V V R) (T : Finset V) (π : Perm V) (hπ : ∀ x ∈ T, π x = x) :
    ∑ σ ∈ univ.filter (fun σ : Perm V => ∀ x ∉ T, σ x = π x),
        Perm.sign σ • ∏ i, A (σ i) i =
      Perm.sign π • (∏ i ∈ Tᶜ, A (π i) i) *
        (A.submatrix ((↑) : T → V) ((↑) : T → V)).det := by
  have himage : univ.filter (fun σ : Perm V => ∀ x ∉ T, σ x = π x) =
      univ.image (fun τ : Perm T => π * Perm.ofSubtype τ) := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      have hT : ∀ x, (π⁻¹ * σ) x ∈ T ↔ x ∈ T := by
        intro x
        by_cases hx : x ∈ T
        · simp only [hx, iff_true]
          by_contra hy
          have hy' : π⁻¹ (σ x) ∉ T := hy
          have h1 : σ (π⁻¹ (σ x)) = σ x := by rw [h _ hy']; simp
          exact hy' (by rw [σ.injective h1]; exact hx)
        · simp [hx, h x hx]
      refine ⟨(π⁻¹ * σ).subtypePerm hT, ?_⟩
      rw [Perm.ofSubtype_subtypePerm]
      · group
      · intro x hx
        by_contra hxT
        exact hx (by simp [h x hxT])
    · rintro ⟨τ, rfl⟩ x hx
      rw [Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem τ hx]
  rw [himage, Finset.sum_image (fun a _ b _ hab =>
    Perm.ofSubtype_injective (mul_left_cancel hab)), Matrix.det_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Perm.sign_mul, Perm.sign_ofSubtype, ← Finset.prod_compl_mul_prod T]
  have h1 : ∏ i ∈ Tᶜ, A ((π * Perm.ofSubtype τ) i) i = ∏ i ∈ Tᶜ, A (π i) i :=
    Finset.prod_congr rfl fun i hi => by
      rw [Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem τ (Finset.mem_compl.mp hi)]
  have h2 : ∏ i ∈ T, A ((π * Perm.ofSubtype τ) i) i = ∏ i : T, A (τ i) i := by
    rw [← Finset.prod_coe_sort T]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Perm.mul_apply, Perm.ofSubtype_apply_of_mem τ i.2, hπ _ (τ ⟨i, i.2⟩).2]
  rw [h1, h2]
  simp only [Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul, Units.val_mul, Int.cast_mul]
  ring

section VertexExpansion

variable {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V)

/-- The entries of `-M(Γ)`. -/
private theorem neg_matrix_apply (i j : V) :
    (-Γ.matrix) i j = if i = j then Γ.weight i else -(Γ.edgeWeight i j : ℤ) := by
  simp only [Matrix.neg_apply, WeightedGraph.matrix, Matrix.of_apply]
  split_ifs <;> simp

/-- `Δ(S)` is the principal minor of `-M(Γ)` on `S`. -/
private theorem delta_eq_det_submatrix (S : Finset V) :
    Γ.delta S = ((-Γ.matrix).submatrix ((↑) : S → V) ((↑) : S → V)).det := by
  simp only [WeightedGraph.delta, WeightedGraph.det]
  congr 1
  ext i j
  simp only [Matrix.neg_apply, Matrix.submatrix_apply, WeightedGraph.matrix,
    Matrix.of_apply, WeightedGraph.restrict, Subtype.ext_iff]

/-- A permutation with a nonzero term in the expansion of `Δ(Γ)` moves every vertex to itself or
to a neighbour. -/
private theorem adj_apply_of_term_ne_zero {σ : Perm V}
    (hσ : Perm.sign σ • ∏ i, (-Γ.matrix) (σ i) i ≠ 0) {x : V} (hx : σ x ≠ x) :
    Γ.underlyingGraph.Adj x (σ x) := by
  have hx0 : (-Γ.matrix) (σ x) x ≠ 0 := fun h0 =>
    hσ (by rw [Finset.prod_eq_zero (f := fun i => (-Γ.matrix) (σ i) i) (mem_univ x) h0, smul_zero])
  rw [neg_matrix_apply, ite_eq_right hx, neg_ne_zero, Nat.cast_ne_zero] at hx0
  exact ⟨hx.symm, by rw [Γ.edgeWeight_symm]; omega⟩

/-- The permutations fixing `v` contribute `n_v Δ(Γ - v)`. -/
private theorem sum_apply_eq_self (v : V) :
    ∑ σ ∈ univ.filter (fun σ : Perm V => σ v = v), Perm.sign σ • ∏ i, (-Γ.matrix) (σ i) i =
      Γ.weight v * Γ.delta (univ \ {v}) := by
  have hfilt : univ.filter (fun σ : Perm V => σ v = v) =
      univ.filter (fun σ : Perm V => ∀ x ∉ univ \ {v}, σ x = (1 : Perm V) x) :=
    Finset.filter_congr fun σ _ => by simp
  have hc : (univ \ {v} : Finset V)ᶜ = {v} := by ext; simp
  rw [hfilt, sum_perm_agree_eq _ _ 1 (fun _ _ => rfl), delta_eq_det_submatrix]
  simp [hc, WeightedGraph.matrix]

/-- In a forest with simple edges, the permutations sending `v` to a neighbour `w` contribute
`-Δ(Γ - v - w)`: a nonzero term forces `σ w = v`, so `σ` agrees with the transposition `(v w)`
outside `V \ {v, w}`. -/
private theorem sum_apply_eq_neighbor (hs : Γ.HasSimpleEdges) (hΓ : Γ.IsAcyclic) {v w : V}
    (hw : w ∈ Γ.neighbors v) :
    ∑ σ ∈ univ.filter (fun σ : Perm V => σ v = w), Perm.sign σ • ∏ i, (-Γ.matrix) (σ i) i =
      -Γ.delta (univ \ {v, w}) := by
  have hadj := Γ.mem_neighbors.mp hw
  have hvw : v ≠ w := hadj.1
  have hT : ∀ x ∈ (univ \ {v, w} : Finset V), swap v w x = x := fun x hx => by
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hx
    exact swap_apply_of_ne_of_ne hx.1 hx.2
  rw [← Finset.sum_subset (s₁ := univ.filter
      (fun σ : Perm V => ∀ x ∉ (univ \ {v, w} : Finset V), σ x = swap v w x)),
    sum_perm_agree_eq _ _ _ hT, delta_eq_det_submatrix]
  · have hc : (univ \ {v, w} : Finset V)ᶜ = {v, w} := by ext; simp; tauto
    have h2 : Γ.edgeWeight v w = 1 := (hs v w hadj).2
    rw [hc, Finset.prod_pair hvw, Perm.sign_swap hvw, swap_apply_left, swap_apply_right,
      neg_matrix_apply, neg_matrix_apply, ite_eq_right hvw.symm, ite_eq_right hvw,
      Γ.edgeWeight_symm, h2]
    simp
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    simpa using hσ v (by simp)
  · intro σ hσ hnot
    simp only [mem_filter, mem_univ, true_and] at hσ hnot
    by_contra h0
    have hinv := WeightedGraph.perm_apply_apply_eq_self_of_isAcyclic hΓ σ
      (fun _ => adj_apply_of_term_ne_zero Γ h0) v
    rw [hσ] at hinv
    refine hnot fun x hx => ?_
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_not] at hx
    rcases hx with rfl | rfl
    · rw [hσ, swap_apply_left]
    · rw [hinv, swap_apply_right]

/-- The permutations sending `v` to a non-neighbour `w ≠ v` contribute nothing. -/
private theorem sum_apply_eq_of_notMem_neighbors {v w : V} (hwv : w ≠ v)
    (hw : w ∉ Γ.neighbors v) :
    ∑ σ ∈ univ.filter (fun σ : Perm V => σ v = w), Perm.sign σ • ∏ i, (-Γ.matrix) (σ i) i =
      0 := by
  refine Finset.sum_eq_zero fun σ hσ => ?_
  simp only [mem_filter, mem_univ, true_and] at hσ
  by_contra h0
  subst hσ
  exact hw (Γ.mem_neighbors.mpr (adj_apply_of_term_ne_zero Γ h0 hwv))

end VertexExpansion

/-- **Vertex expansion of `Δ`** (FA 3.1.8). If `Γ` has simple edges and no cycles, then for every
vertex `v`, `Δ(Γ) = n_v Δ(Γ - v) - ∑_{w ∼ v} Δ(Γ - v - w)`. -/
@[mmp "lem_fa3_determinant_vertex_expansion"]
public theorem det_eq_weight_mul_delta_sub_sum_delta {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : WeightedGraph V) (hs : Γ.HasSimpleEdges) (hΓ : Γ.IsAcyclic) (v : V) :
    Γ.det = Γ.weight v * Γ.delta (univ \ {v}) -
      ∑ w ∈ Γ.neighbors v, Γ.delta (univ \ {v, w}) := by
  have hsub : Γ.neighbors v ⊆ univ.erase v := fun w hw =>
    mem_erase.mpr ⟨(Γ.mem_neighbors.mp hw).1.symm, mem_univ _⟩
  rw [WeightedGraph.det, Matrix.det_apply, ← Finset.sum_fiberwise univ (fun σ : Perm V => σ v),
    ← Finset.add_sum_erase _ _ (mem_univ v), sum_apply_eq_self, sub_eq_add_neg,
    ← Finset.sum_neg_distrib, ← Finset.sum_subset hsub fun w hw hnw =>
      sum_apply_eq_of_notMem_neighbors Γ (mem_erase.mp hw).1 hnw]
  exact congrArg _ (Finset.sum_congr rfl fun w hw => sum_apply_eq_neighbor Γ hs hΓ hw)

/-! ### Determinants of chains -/

section Chain

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In a chain enumerated by `e`, `e i` and `e j` are adjacent iff `i` and `j` are consecutive. -/
private theorem IsChainOrder.adj_iff {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V}
    (he : Γ.IsChainOrder e) (i j : Fin s) :
    Γ.underlyingGraph.Adj (e i) (e j) ↔ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i) := by
  change e i ≠ e j ∧ 0 < Γ.edgeWeight (e i) (e j) ↔ _
  rw [he.edgeWeight_eq]
  split_ifs with h
  · refine ⟨fun _ => h, fun _ => ⟨fun hij => ?_, Nat.one_pos⟩⟩
    have := congrArg Fin.val (e.injective hij)
    omega
  · simp [h]

private theorem IsChainOrder.hasSimpleEdges {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V}
    (he : Γ.IsChainOrder e) : Γ.HasSimpleEdges := by
  intro u v huv
  refine ⟨huv.1, ?_⟩
  rw [← e.apply_symm_apply u, ← e.apply_symm_apply v] at huv ⊢
  rw [he.edgeWeight_eq, ite_eq_left ((he.adj_iff _ _).1 huv)]

/-- Along a walk avoiding the edge between positions `k` and `k + 1`, the position stays on one
side of `k`. -/
private theorem IsChainOrder.le_iff_of_walk {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V}
    (he : Γ.IsChainOrder e) (k : Fin s) (k' : Fin s) (hk : (k : ℕ) + 1 = k') {a b : V}
    (p : (Γ.underlyingGraph.deleteEdges {s(e k, e k')}).Walk a b) :
    ((e.symm a : ℕ) ≤ k ↔ (e.symm b : ℕ) ≤ k) := by
  induction p with
  | nil => rfl
  | @cons a c b h _ ih =>
    rw [← ih]
    rw [SimpleGraph.deleteEdges_adj] at h
    obtain ⟨h, hne⟩ := h
    rw [← e.apply_symm_apply a, ← e.apply_symm_apply c] at h hne
    rw [he.adj_iff] at h
    by_contra hc
    apply hne
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    rcases h with h | h
    · left
      constructor <;> congr 1 <;> ext <;> omega
    · right
      constructor <;> congr 1 <;> ext <;> omega

/-- A chain has no cycles: every edge `v_k v_{k+1}` is a bridge. -/
private theorem IsChainOrder.isAcyclic {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V}
    (he : Γ.IsChainOrder e) : Γ.IsAcyclic := by
  rw [WeightedGraph.IsAcyclic, SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  rw [← e.apply_symm_apply u, ← e.apply_symm_apply v] at huv p
  rw [he.adj_iff] at huv
  rcases huv with h | h
  · have := he.le_iff_of_walk _ _ h p
    simp only [Equiv.symm_apply_apply] at this
    omega
  · rw [Sym2.eq_swap] at p
    have := he.le_iff_of_walk _ _ h p
    simp only [Equiv.symm_apply_apply] at this
    omega

/-- The determinant of an induced subgraph of an induced subgraph. -/
private theorem delta_restrict (Γ : WeightedGraph V) (S : Finset V) (T : Finset S) :
    (Γ.restrict S).delta T = Γ.delta (T.map (Function.Embedding.subtype _)) := by
  let f : ↥T ≃ ↥(T.map (Function.Embedding.subtype _)) :=
    Equiv.ofBijective (fun i => ⟨i.1.1, mem_map_of_mem _ i.2⟩) (by
      constructor
      · intro i j hij
        have := congrArg Subtype.val hij
        exact Subtype.ext (Subtype.ext this)
      · rintro ⟨x, hx⟩
        obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
        exact ⟨⟨y, hy⟩, rfl⟩)
  unfold delta det
  rw [← Matrix.det_submatrix_equiv_self f]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.neg_apply, matrix, Matrix.of_apply,
    WeightedGraph.restrict, f, Subtype.ext_iff]
  split_ifs <;> first | rfl | simp_all

/-- At the end `v_1` of a chain with one vertex, there are no other vertices. -/
private theorem sdiff_zero_eq_empty (e : Fin 1 ≃ V) :
    (univ \ {e 0} : Finset V) = ∅ := by
  ext v
  simp only [mem_sdiff, mem_univ, mem_singleton, true_and, notMem_empty, iff_false, not_not]
  rw [← e.apply_symm_apply v, Subsingleton.elim (e.symm v) 0]

/-- The end `v_1` of a chain with one vertex has no neighbours. -/
private theorem IsChainOrder.neighbors_zero_eq_empty {Γ : WeightedGraph V} {e : Fin 1 ≃ V}
    (he : Γ.IsChainOrder e) : Γ.neighbors (e 0) = ∅ := by
  ext v
  rw [mem_neighbors, ← e.apply_symm_apply v, he.adj_iff]
  simp only [notMem_empty, iff_false]
  omega

/-- The only neighbour of the end `v_1` of a chain with at least two vertices is `v_2`. -/
private theorem IsChainOrder.neighbors_zero_eq_singleton {Γ : WeightedGraph V} {n : ℕ}
    {e : Fin (n + 2) ≃ V} (he : Γ.IsChainOrder e) : Γ.neighbors (e 0) = {e 1} := by
  ext v
  rw [mem_neighbors, ← e.apply_symm_apply v, he.adj_iff, mem_singleton, e.injective.eq_iff,
    Fin.ext_iff]
  simp only [Fin.val_zero, Fin.val_one]
  omega

/-- The enumeration `v_2, …, v_s` of `Γ - v_1`. -/
private noncomputable def tailEquiv {n : ℕ} (e : Fin (n + 2) ≃ V) :
    Fin (n + 1) ≃ ↥(univ \ {e 0} : Finset V) :=
  Equiv.ofBijective (fun i => ⟨e i.succ, by simp [e.injective.ne (Fin.succ_ne_zero i)]⟩) (by
    constructor
    · intro i j hij
      simp only [Subtype.mk.injEq] at hij
      exact Fin.succ_injective _ (e.injective hij)
    · rintro ⟨v, hv⟩
      have h0 : e.symm v ≠ 0 := by
        rintro h
        simp [← h] at hv
      obtain ⟨i, hi⟩ := Fin.exists_succ_eq.2 h0
      exact ⟨i, Subtype.ext (by simp [hi])⟩)

private theorem tailEquiv_apply {n : ℕ} (e : Fin (n + 2) ≃ V) (i : Fin (n + 1)) :
    (tailEquiv e i : V) = e i.succ := rfl

/-- Removing the end `v_1` of a chain leaves the chain `v_2, …, v_s`. -/
private theorem IsChainOrder.removeVertex_tailEquiv {Γ : WeightedGraph V} {n : ℕ}
    {e : Fin (n + 2) ≃ V} (he : Γ.IsChainOrder e) :
    (Γ.removeVertex (e 0)).IsChainOrder (tailEquiv e) := by
  refine ⟨fun i => he.genus_eq_zero i.succ, fun i j => ?_⟩
  change Γ.edgeWeight (e i.succ) (e j.succ) = _
  rw [he.edgeWeight_eq]
  simp only [Fin.val_succ, Nat.add_right_cancel_iff]

/-- `Δ((Γ - v_1) - v_2) = Δ(Γ - v_1 - v_2)`. -/
private theorem delta_removeVertex_sdiff_tailEquiv (Γ : WeightedGraph V) {n : ℕ}
    (e : Fin (n + 2) ≃ V) :
    (Γ.removeVertex (e 0)).delta (univ \ {tailEquiv e 0}) = Γ.delta (univ \ {e 0, e 1}) := by
  rw [delta_restrict]
  congr 1
  ext v
  simp only [mem_map, mem_sdiff, mem_univ, mem_singleton, true_and,
    Function.Embedding.coe_subtype, mem_insert, not_or, Subtype.ext_iff, tailEquiv_apply,
    Fin.succ_zero_eq_one]
  exact ⟨fun ⟨w, hw, hwv⟩ => hwv ▸ ⟨fun h => (mem_sdiff.1 w.2).2 (mem_singleton.2 h), hw⟩,
    fun ⟨h0, h1⟩ => ⟨⟨v, by simpa using h0⟩, h1, rfl⟩⟩

/-- For a chain of length `n + 1` with all weights `≥ 2`, `Δ(Γ - v_1) ≥ 1` and
`Δ(Γ) ≥ Δ(Γ - v_1) + 1`. -/
private theorem one_le_delta_and_delta_add_one_le_det_aux (n : ℕ) :
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V) (e : Fin (n + 1) ≃ V),
      Γ.IsChainOrder e → (∀ v, 2 ≤ Γ.weight v) →
        1 ≤ Γ.delta (univ \ {e 0}) ∧ Γ.delta (univ \ {e 0}) + 1 ≤ Γ.det := by
  induction n with
  | zero =>
    intro V _ _ Γ e he hw
    rw [det_eq_weight_mul_delta_sub_sum_delta Γ he.hasSimpleEdges he.isAcyclic (e 0),
      he.neighbors_zero_eq_empty, sdiff_zero_eq_empty e, delta_empty, sum_empty]
    have := hw (e 0)
    omega
  | succ n ih =>
    intro V _ _ Γ e he hw
    obtain ⟨h1, h2⟩ := ih _ (tailEquiv e) he.removeVertex_tailEquiv (fun v => hw v)
    rw [det_removeSet, delta_removeVertex_sdiff_tailEquiv] at *
    rw [det_eq_weight_mul_delta_sub_sum_delta Γ he.hasSimpleEdges he.isAcyclic (e 0),
      he.neighbors_zero_eq_singleton, sum_singleton]
    have := hw (e 0)
    exact ⟨by omega, by nlinarith⟩

end Chain

/-- **Lower bound for the determinant of a chain.** If `Γ` is a weighted chain enumerated by
`e : Fin s ≃ V` with `s ≥ 1` and all weights `≥ 2`, then with `v_1 = e 0`,
`Δ(Γ - v_1) ≥ 1` and `Δ(Γ) ≥ Δ(Γ - v_1) + 1`. -/
@[mmp "lem_fa3_chain_determinant_lower_bound"]
public theorem one_le_delta_and_delta_add_one_le_det_of_isChainOrder {V : Type*} [Fintype V]
    [DecidableEq V] (Γ : WeightedGraph V) {s : ℕ} (hs : 0 < s) (e : Fin s ≃ V)
    (he : Γ.IsChainOrder e) (hw : ∀ v, 2 ≤ Γ.weight v) :
    1 ≤ Γ.delta (univ \ {e ⟨0, hs⟩}) ∧ Γ.delta (univ \ {e ⟨0, hs⟩}) + 1 ≤ Γ.det := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  exact one_le_delta_and_delta_add_one_le_det_aux n Γ e he hw

/-- `Δ(Γ) ≥ n + 2` for a chain of length `n + 1` with all weights `≥ 2`. -/
private theorem add_two_le_det_aux (n : ℕ) :
    ∀ {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V) (e : Fin (n + 1) ≃ V),
      Γ.IsChainOrder e → (∀ v, 2 ≤ Γ.weight v) → (n : ℤ) + 2 ≤ Γ.det := by
  induction n with
  | zero =>
    intro V _ _ Γ e he hw
    have := one_le_delta_and_delta_add_one_le_det_of_isChainOrder Γ Nat.one_pos e he hw
    push_cast
    omega
  | succ n ih =>
    intro V _ _ Γ e he hw
    have hd : (n : ℤ) + 2 ≤ Γ.delta (univ \ {e ⟨0, n.succ.succ_pos⟩}) :=
      ih (Γ.removeVertex (e 0)) (tailEquiv e) he.removeVertex_tailEquiv fun v => hw v
    have := (one_le_delta_and_delta_add_one_le_det_of_isChainOrder Γ (Nat.succ_pos _) e he hw).2
    push_cast
    omega

/-- **The determinant of a chain is at least its length plus one.** If `Γ` is a weighted chain
enumerated by `e : Fin s ≃ V` with `s ≥ 1` and all weights `≥ 2`, then `s + 1 ≤ Γ.det`. -/
@[mmp "lem_fa3_chain_determinant_at_least_length"]
public theorem add_one_le_det_of_isChainOrder {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : WeightedGraph V) {s : ℕ} (hs : 0 < s) (e : Fin s ≃ V) (he : Γ.IsChainOrder e)
    (hw : ∀ v, 2 ≤ Γ.weight v) : (s : ℤ) + 1 ≤ Γ.det := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  have := add_two_le_det_aux n Γ e he hw
  push_cast
  omega

/-- The determinant of a one-vertex weighted graph is the weight of its vertex. -/
private theorem det_eq_weight_of_fin_one {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : WeightedGraph V) (e : Fin 1 ≃ V) : Γ.det = Γ.weight (e 0) := by
  rw [WeightedGraph.det, ← Matrix.det_submatrix_equiv_self e, Matrix.det_fin_one]
  simp [WeightedGraph.matrix]

/-- **A chain has determinant two iff it is a single `(-2)`-vertex.** If `Γ` is a weighted
chain enumerated by `e : Fin s ≃ V` with `s ≥ 1` and all weights `≥ 2`, then `Γ.det = 2` if
and only if `s = 1` and the weight of `e ⟨0, hs⟩` is `2`. -/
@[mmp "lem_fa3_chain_determinant_two"]
public theorem det_eq_two_iff_of_isChainOrder {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : WeightedGraph V) {s : ℕ} (hs : 0 < s) (e : Fin s ≃ V) (he : Γ.IsChainOrder e)
    (hw : ∀ v, 2 ≤ Γ.weight v) : Γ.det = 2 ↔ s = 1 ∧ Γ.weight (e ⟨0, hs⟩) = 2 := by
  constructor
  · intro h
    have hle := add_one_le_det_of_isChainOrder Γ hs e he hw
    obtain rfl : s = 1 := by omega
    exact ⟨rfl, (det_eq_weight_of_fin_one Γ e).symm.trans h⟩
  · rintro ⟨rfl, h2⟩
    exact (det_eq_weight_of_fin_one Γ e).trans h2

end MMP.Flips.WeightedGraph

/-! ### Intersection numbers of `ℝ`-Cartier divisors with proper curves -/

namespace MMP.Flips

open MMP.Mori TensorProduct

section RIntersection

variable {k : Type*} [Field k] {X : Scheme} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem ProperCurve.not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem ProperCurve.isCurve_comp (C : ProperCurve sX) {C' : Scheme} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine ProperCurve.not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem ProperCurve.isCurve_ι (C : ProperCurve sX) :
    AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) [IsDominant f] [LocallyOfFiniteType f]
    (hf : IsBirationalMorphism f) : degreeOver f = 1 := by
  let := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  rw [← (AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    hf.functionFieldMap_bijective).toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  have : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := ProperCurve.isCurve_comp C hν hdim
  have hc2 := ProperCurve.isCurve_ι C
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (ProperCurve.not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`, whichever normalization computes it. -/
private theorem IsCartierIntersectionNumber.eq_degreeOn {C : ProperCurve sX} {L : Divisor X}
    {hL : L.IsCartier} {d : ℤ} (h : IsCartierIntersectionNumber k sX C L hL d) :
    d = L.degreeOn k sX C.ι C.dim_le hL := by
  obtain ⟨C', ν, hν, hdim, hd⟩ := h
  have := hν.isFinite
  have : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  rw [hd]
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact degreeOn_normalization C hν hdim _

/-- `L ↦ L · C` as an additive map on Cartier divisors. -/
private noncomputable def degreeHom (C : ProperCurve sX) :
    Divisor.cartierSubgroup (X := X) →+ ℤ where
  toFun L := (L : Divisor X).degreeOn k sX C.ι C.dim_le L.2
  map_zero' := Divisor.degreeOn_zero' k sX C.ι C.dim_le
  map_add' L₁ L₂ := Divisor.degreeOn_add k sX C.ι C.dim_le L₁.1 L₂.1 L₁.2 L₂.2

/-- The additive extension `Ca(X) ⊗ ℝ → ℝ`, `L ⊗ r ↦ (L · C) r`. -/
private noncomputable def degreeTensor (C : ProperCurve sX) :
    Divisor.cartierSubgroup (X := X) ⊗[ℤ] ℝ →+ ℝ :=
  TensorProduct.liftAddHom (AddMonoidHom.mul.comp ((Int.castAddHom ℝ).comp (degreeHom k sX C)))
    fun n L r => by simp [mul_assoc, mul_left_comm]

private theorem degreeTensor_tmul (C : ProperCurve sX) (L : Divisor.cartierSubgroup (X := X))
    (r : ℝ) : degreeTensor k sX C (L ⊗ₜ r) = (degreeHom k sX C L : ℝ) * r := by
  simp [degreeTensor]

/-- The value of `D · C` computed from a presentation is the image of `∑ L_j ⊗ r_j`. -/
private theorem IsRIntersectionNumber.eq_degreeTensor {C : ProperCurve sX} {D : RDivisor X}
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (h : IsRIntersectionNumber k sX D r L C x) :
    ∃ hL : ∀ j, (L j).IsCartier, D = ∑ j, r j • Divisor.toRDivisor (L j) ∧
      x = degreeTensor k sX C (∑ j, (⟨L j, hL j⟩ : Divisor.cartierSubgroup (X := X)) ⊗ₜ r j) := by
  obtain ⟨hL, d, hD, hd, hx⟩ := h
  refine ⟨hL, hD, ?_⟩
  rw [hx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [degreeTensor_tmul, (hd j).eq_degreeOn, mul_comm]
  rfl

variable {k sX} in
/-- The pieces of a presentation of `D₁` and `D₂`, concatenated, present `a • D₁ + b • D₂`. -/
public theorem IsRIntersectionNumber.append {C : ProperCurve sX} {D₁ D₂ : RDivisor X}
    {m₁ m₂ : ℕ} {r₁ : Fin m₁ → ℝ} {L₁ : Fin m₁ → Divisor X} {r₂ : Fin m₂ → ℝ}
    {L₂ : Fin m₂ → Divisor X} {x₁ x₂ : ℝ} (a b : ℝ)
    (h₁ : IsRIntersectionNumber k sX D₁ r₁ L₁ C x₁)
    (h₂ : IsRIntersectionNumber k sX D₂ r₂ L₂ C x₂) :
    IsRIntersectionNumber k sX (a • D₁ + b • D₂) (Fin.append (a • r₁) (b • r₂))
      (Fin.append L₁ L₂) C (a * x₁ + b * x₂) := by
  obtain ⟨hL₁, d₁, hD₁, hd₁, hx₁⟩ := h₁
  obtain ⟨hL₂, d₂, hD₂, hd₂, hx₂⟩ := h₂
  have hL : ∀ j, (Fin.append L₁ L₂ j).IsCartier := fun j =>
    Fin.addCases (motive := fun j => (Fin.append L₁ L₂ j).IsCartier)
      (fun i => by simpa using hL₁ i) (fun i => by simpa using hL₂ i) j
  refine ⟨hL, Fin.append d₁ d₂, ?_, ?_, ?_⟩
  · simp [Fin.sum_univ_add, hD₁, hD₂, Finset.smul_sum, smul_smul]
  · intro j
    refine Fin.addCases
      (motive := fun j => IsCartierIntersectionNumber k sX C (Fin.append L₁ L₂ j) (hL j)
        (Fin.append d₁ d₂ j)) (fun i => ?_) (fun i => ?_) j
    · simpa using hd₁ i
    · simpa using hd₂ i
  · simp [Fin.sum_univ_add, hx₁, hx₂, Finset.mul_sum, mul_assoc]

end RIntersection

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The intersection number `D · C` of an `ℝ`-Cartier divisor with a proper curve is independent
of the presentation `D = ∑ r_j L_j`, and is `ℝ`-linear in `D`. -/
@[mmp "lem_fa2_r_intersection_number_well_defined"]
public theorem IsRIntersectionNumber.eq_and_linear (k : Type u) [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    (C : ProperCurve sX) :
    (∀ (D : RDivisor X) {m m' : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
        (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X) (x x' : ℝ),
        IsRIntersectionNumber k sX D r L C x → IsRIntersectionNumber k sX D r' L' C x' →
          x = x') ∧
    (∀ (D₁ D₂ : RDivisor X) {m₁ m₂ : ℕ} (r₁ : Fin m₁ → ℝ) (L₁ : Fin m₁ → Divisor X)
        (r₂ : Fin m₂ → ℝ) (L₂ : Fin m₂ → Divisor X) (x₁ x₂ : ℝ) (a b : ℝ),
        IsRIntersectionNumber k sX D₁ r₁ L₁ C x₁ → IsRIntersectionNumber k sX D₂ r₂ L₂ C x₂ →
          IsRIntersectionNumber k sX (a • D₁ + b • D₂) (Fin.append (a • r₁) (b • r₂))
            (Fin.append L₁ L₂) C (a * x₁ + b * x₂)) := by
  refine ⟨fun D m m' r L r' L' x x' h h' => ?_,
    fun D₁ D₂ m₁ m₂ r₁ L₁ r₂ L₂ x₁ x₂ a b h₁ h₂ => h₁.append a b h₂⟩
  obtain ⟨hL, hD, hx⟩ := h.eq_degreeTensor
  obtain ⟨hL', hD', hx'⟩ := h'.eq_degreeTensor
  rw [hx, hx', sum_tmul_eq_of_sum_smul_eq (fun j => ⟨L j, hL j⟩) r (fun j => ⟨L' j, hL' j⟩) r'
    (hD.symm.trans hD')]

end

end MMP.Flips

/-! ### Lifting proper curves along proper surjective morphisms -/

namespace MMP.Mori

open TopologicalSpace

/-- A nonempty fibre of a map out of a Noetherian T₀ space has a point closed in the fibre. -/
private lemma exists_closed_mem_fiber {X Y : Type*} [TopologicalSpace X] [T0Space X]
    [NoetherianSpace X] (f : X → Y) {y : Y} (hy : y ∈ Set.range f) :
    ∃ a, f a = y ∧ ∀ b, f b = y → a ⤳ b → b = a := by
  obtain ⟨x, hx⟩ := hy
  obtain ⟨⟨a, ha⟩, -, hcl⟩ := (isClosed_univ (X := f ⁻¹' {y})).exists_closed_singleton
    ⟨⟨x, hx⟩, Set.mem_univ _⟩
  refine ⟨a, ha, fun b hb hab => ?_⟩
  have : (⟨a, ha⟩ : f ⁻¹' {y}) ⤳ ⟨b, hb⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp hab
  exact congrArg Subtype.val (Set.mem_singleton_iff.mp (this.mem_closed hcl rfl))

/-- A one-point space has topological Krull dimension `0`. -/
private lemma topologicalKrullDim_eq_zero_of_subsingleton (X : Type*) [TopologicalSpace X]
    [Nonempty X] [Subsingleton X] : topologicalKrullDim X = 0 := by
  have : DiscreteTopology X := ⟨Subsingleton.elim _ _⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  have : Nonempty (IrreducibleCloseds X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) Order.krullDim_nonneg

/-- A proper morphism from a reduced scheme whose image is dense in a proper curve `C'` is proper
over `ℂ`: it factors through its scheme-theoretic image, which is `C'`. -/
private lemma ProperCurve.isProper_comp_of_closure_range {X B : Scheme.{0}}
    {sB : B ⟶ Spec (.of ℂ)} (C' : ProperCurve sB) (φ : X ⟶ B) [IsReduced X] [IsProper φ]
    (hφ : closure (Set.range φ.base) = closure {C'.point}) : IsProper (φ ≫ sB) := by
  have hker : φ.ker = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {C'.point}) := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    exact congrArg _ (Closeds.ext (by rw [Closeds.coe_closure, Closeds.coe_closure, hφ]))
  have : IsProper (φ.imageι ≫ sB) := by
    change IsProper (φ.ker.subschemeι ≫ sB); rw [hker]; exact C'.isProper_ι_comp
  have : IsProper (φ.toImage ≫ φ.imageι) := by rw [Scheme.Hom.toImage_imageι]; infer_instance
  have : IsProper φ.toImage := IsProper.of_comp _ φ.imageι
  rw [← Scheme.Hom.toImage_imageι φ, Category.assoc]
  infer_instance

/-- Let `h : A ⟶ B` be a proper surjective morphism of schemes of finite type over `ℂ`. Every
proper curve `C'` on `B` is the image of a proper curve `C` on `A`: `h` maps the generic point of
`C` to that of `C'`, and `h(C) = C'`. -/
@[mmp "lem_fa2_curve_lifting"]
public theorem ProperCurve.exists_map_eq {A B : Scheme.{0}} (sA : A ⟶ Spec (.of ℂ))
    (sB : B ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sA] [QuasiCompact sA]
    [LocallyOfFiniteType sB] [QuasiCompact sB] (h : A ⟶ B) [IsProper h] [Surjective h]
    (hh : h ≫ sB = sA) (C' : ProperCurve sB) :
    ∃ C : ProperCurve sA, h.base C.point = C'.point ∧
      h.base '' closure {C.point} = closure {C'.point} := by
  have : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian sA
  have : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace sA
  have : IsNoetherian A := ⟨⟩
  obtain ⟨a, haξ, hamax⟩ := exists_closed_mem_fiber h.base (h.surjective C'.point)
  set ι := curveSubschemeAtι a
  set φ := ι ≫ h
  have : IrreducibleSpace (curveSubschemeAt a) :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := a)).closure
  have hgen : ι (genericPoint _) = a :=
    Scheme.IdealSheafData.subschemeι_genericPoint_vanishingIdeal_closure a
  have hφgen : φ (genericPoint _) = C'.point := by simp [φ, hgen, haξ]
  have hclr : closure (Set.range φ.base) = closure {C'.point} := by
    rw [MMP.Flips.closure_range_eq_closure_genericPoint φ, hφgen]
  -- the generic fibre of `φ` is the single point `genericPoint`
  have : Subsingleton (φ.base ⁻¹' {φ.base (genericPoint _)}) := by
    suffices ∀ c, φ c = C'.point → c = genericPoint _ from
      ⟨fun u v => Subtype.ext ((this _ (u.2.trans hφgen)).trans (this _ (v.2.trans hφgen)).symm)⟩
    intro c hc
    have hca : a ⤳ ι c := specializes_iff_mem_closure.mpr (range_curveSubschemeAtι a ▸ ⟨c, rfl⟩)
    exact ι.isEmbedding.injective
      ((hamax _ (by rw [← hc, Scheme.Hom.comp_apply]) hca).trans hgen.symm)
  let e := φ.fiberHomeo (φ.base (genericPoint _))
  have : Subsingleton (φ.fiber (φ.base (genericPoint _))) := e.injective.subsingleton
  have : Nonempty (φ.fiber (φ.base (genericPoint _))) := ⟨e.symm ⟨genericPoint _, rfl⟩⟩
  have hcomp : φ ≫ sB = ι ≫ sA := by rw [Category.assoc, hh]
  have hdim : topologicalKrullDim (curveSubschemeAt a) = 1 := by
    rw [MMP.Flips.topologicalKrullDim_eq_fiber_add_closure_range φ ℂ (ι ≫ sA) sB hcomp,
      topologicalKrullDim_eq_zero_of_subsingleton (φ.fiber _), hclr, zero_add]
    exact C'.dim_eq
  refine ⟨⟨a, hdim, hcomp ▸ C'.isProper_comp_of_closure_range φ hclr⟩, haξ, ?_⟩
  rw [← h.isClosedMap.closure_image_eq_of_continuous h.continuous, Set.image_singleton, haξ]

end MMP.Mori

/-! ### Finiteness of the `φ⁻¹`-exceptional divisors -/

namespace MMP.Flips.RationalMap

open TopologicalSpace

private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (IrreducibleCloseds.closureSingleton (genericPoint X))).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- On a variety of dimension `n`, a divisor over `X` is exceptional iff its centre has
codimension at least two. -/
private theorem isExceptional_iff_two_le_coheight {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (D : ProperDivisorOver k sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  unfold ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint, hn]
  have h := topologicalKrullDim_closure_singleton_add_coheight sX (D.f D.E.genericPoint)
  rw [hn] at h
  exact withBot_add_two_le_iff h

private theorem source_ι_comp_eq_of_toRationalMap_eq {X Y : Scheme.{u}} [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

private theorem apply_hom_eq_of_isInverse {X Y : Scheme.{u}} [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

private theorem isSeparated_terminal {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- A rational map which is a morphism in codimension one is defined at the generic point of
every prime divisor. -/
private theorem IsMorphismInCodimOne.definedAt_genericPoint {X Y : Scheme.{u}}
    {φ : X.RationalMap Y} (hφ₁ : IsMorphismInCodimOne φ) (P : Mori.PrimeDivisor X) :
    Mori.RationalMap.DefinedAt φ P.genericPoint := by
  by_contra hnd
  have h2 := Mori.le_closedsCodimension_iff.mp hφ₁
    (IrreducibleCloseds.closureSingleton P.genericPoint)
    (closure_minimal (Set.singleton_subset_iff.mpr hnd) (Mori.RationalMap.dom φ).compl.isClosed)
  rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
    (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
    Order.coheight_orderIso, P.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- A prime divisor of `Y` whose generic point lies in the target of an isomorphism of dense opens
representing `φ` is a birational transform under `φ`. -/
private theorem exists_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (e : X.PartialIso Y) (F : Mori.PrimeDivisor Y)
    (hF : F.genericPoint ∈ e.target) :
    ∃ P : Mori.PrimeDivisor X,
      Mori.RationalMap.transformPrimeDivisor e.toRationalMap P = some F := by
  let u : e.target.toScheme := ⟨F.genericPoint, hF⟩
  let x : e.source.toScheme := e.iso.inv u
  have hx : Order.coheight (e.source.ι x) = 1 := by
    rw [coheight_eq_of_isOpenImmersion, coheight_eq_of_isOpenImmersion,
      ← coheight_eq_of_isOpenImmersion e.target.ι]
    exact F.coheight_genericPoint
  let P := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hx
  have hgP : P.genericPoint = e.source.ι x :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hx
  have hP : P.genericPoint ∈ e.toPartialMap.domain := by
    change P.genericPoint ∈ e.source
    rw [hgP]; exact x.2
  refine ⟨P, transformPrimeDivisor_eq_some_of_genericPoint_eq e.toPartialMap rfl hP ?_⟩
  have hxP : (⟨P.genericPoint, hP⟩ : e.source.toScheme) = x := Subtype.ext hgP
  change F.genericPoint = (e.iso.hom ≫ e.target.ι) ⟨P.genericPoint, hP⟩
  rw [hxP, Scheme.Hom.comp_apply]
  change F.genericPoint = e.target.ι ((e.iso.inv ≫ e.iso.hom) u)
  rw [Iso.inv_hom_id]
  rfl

private theorem finite_setOf_isInverseExceptional_of_isBirational {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : Mori.IsNormalVariety k sX) (hY : Mori.IsNormalVariety k sY)
    (φ : X.RationalMap Y) (hφ : Mori.RationalMap.IsBirational φ) :
    {F : Mori.PrimeDivisor Y | IsInverseExceptional φ F}.Finite := by
  have := hX.1.toIsIntegral
  have := hY.1.toIsIntegral
  have := hY.1.toLocallyOfFiniteType
  have : IsSeparated sY := hY.1.toIsSeparated
  have := isSeparated_terminal sY
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  -- the `φ⁻¹`-exceptional divisors have generic points outside the target of `e`
  have : AlgebraicGeometry.IsNoetherian Y := ⟨⟩
  obtain ⟨e, he⟩ := hφ
  obtain ⟨y₀⟩ : Nonempty e.target := (e.dense_target.nonempty).to_subtype
  have hη : genericPoint Y ∈ e.target :=
    ((genericPoint_spec Y).mem_open_set_iff e.target.isOpen).mpr ⟨y₀.1, trivial, y₀.2⟩
  refine Set.Finite.of_finite_image
    ((MMP.Mori.finite_coheight_eq_one_mem_closure_notMem (genericPoint Y) e.target hη).subset ?_)
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨F, hF, rfl⟩
  refine ⟨by rw [(genericPoint_spec Y).def]; trivial, fun hmem => ?_, F.coheight_genericPoint⟩
  obtain ⟨P, hP⟩ := exists_transformPrimeDivisor_eq_some e F hmem
  exact hF P (he ▸ hP)

private theorem map_genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}}
    [IsReduced X] [IsReduced Y] [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)]
    {φ : X.RationalMap Y} (g : Y ⟶ X) (e : Y.PartialIso X) (he : e.toRationalMap = g.toRationalMap)
    (he' : e.symm.toRationalMap = φ) {P : Mori.PrimeDivisor X} {F : Mori.PrimeDivisor Y}
    (hP : Mori.RationalMap.transformPrimeDivisor φ P = some F) :
    g F.genericPoint = P.genericPoint := by
  obtain ⟨g', hPd, hg'⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hP).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some hP g' hg' hPd]
  exact apply_hom_eq_of_isInverse g e he g' (hg'.trans he'.symm) hPd

private theorem transformPrimeDivisor_eq_some_of_map_genericPoint_eq {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : Mori.IsNormalVariety k sX) (hY : Mori.IsNormalVariety k sY)
    (φ : X.RationalMap Y) (hφ₁ : IsMorphismInCodimOne φ) (g : Y ⟶ X) [IsSeparated g]
    (hf : Mori.IsBirationalMorphism g) (e : Y.PartialIso X) (he : e.toRationalMap = g.toRationalMap)
    (he' : e.symm.toRationalMap = φ) {P : Mori.PrimeDivisor X} {F : Mori.PrimeDivisor Y}
    (h : g F.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor φ P = some F := by
  have := hX.1.toIsIntegral
  have := hY.1.toIsIntegral
  have := hX.1.toLocallyOfFiniteType
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated sY := hY.1.toIsSeparated
  have := isSeparated_terminal sX
  have := isSeparated_terminal sY
  have : IsNormal X := hX.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant g := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  -- `φ` is defined at `η_P`
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp (hφ₁.definedAt_genericPoint P)
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse g e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (g F.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (g (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing g hbij F.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing g hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap g hbij (hy.trans h.symm)

private theorem isInverseExceptional_iff_isExceptionalPrimeDivisor {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : Mori.IsNormalVariety k sX) (hY : Mori.IsNormalVariety k sY)
    (φ : X.RationalMap Y) (hφ₁ : IsMorphismInCodimOne φ) (g : Y ⟶ X) (hg : IsProper g)
    (hgs : g ≫ sX = sY) (hinv : Mori.RationalMap.IsInverse (X := Y) g.toRationalMap φ)
    (F : Mori.PrimeDivisor Y) :
    IsInverseExceptional φ F ↔ IsExceptionalPrimeDivisor sX g F := by
  have := hX.1.toIsIntegral
  have := hY.1.toIsIntegral
  have := hX.1.toLocallyOfFiniteType
  have := hY.1.toLocallyOfFiniteType
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated sY := hY.1.toIsSeparated
  have := isSeparated_terminal sX
  have := isSeparated_terminal sY
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : QuasiCompact sY := hY.1.toQuasiCompact
  have : IsNormal X := hX.2
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hY' : Mori.IsNormalVariety k (g ≫ sX) := hgs ▸ hY
  have hf : Mori.IsBirationalMorphism g := hinv.isBirational
  have : IsDominant g := hf.isDominant
  obtain ⟨e, he, he'⟩ := hinv
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  let D : ProperDivisorOver k sX := .mk ⟨Y, g, hY', hf, F⟩ hg
  have hD := isExceptional_iff_two_le_coheight hn D
  have hexc : IsExceptionalPrimeDivisor sX g F ↔ 2 ≤ Order.coheight (g F.genericPoint) :=
    ⟨fun h => hD.mp h.2.2.2, fun h => ⟨hY', hf, hg, hD.mpr h⟩⟩
  rw [hexc]
  constructor
  · intro hI
    by_contra hE
    -- `g(η_F)` is the generic point of a prime divisor `P`
    have hc : ¬ 2 ≤ codimension D.toDivisorOver.center := by
      rwa [MMP.Positivity.DivisorOver.codimension_center]
    rw [MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX] at hc
    simp only [not_forall, not_not] at hc
    obtain ⟨P, hv⟩ := hc
    exact hI P (transformPrimeDivisor_eq_some_of_map_genericPoint_eq hX hY φ hφ₁ g hf e he he'
      (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv))
  · intro hE P hP
    rw [map_genericPoint_eq_of_transformPrimeDivisor_eq_some g e he he' hP,
      P.coheight_genericPoint] at hE
    exact absurd hE (by decide)

/-- **FA 2.7.** Let `φ : X ⤏ Y` be a birational map of normal varieties over `k` which is a
morphism in codimension one. Then only finitely many prime divisors of `Y` are
`φ⁻¹`-exceptional. If `φ` is an inverse of a proper morphism `g : Y ⟶ X` over `k`, a prime
divisor `F` of `Y` is `φ⁻¹`-exceptional if and only if it is exceptional over `X`
(`MMP.Flips.IsExceptionalPrimeDivisor`). -/
@[mmp "lem_fa2_inverse_exceptional_divisors_finite"]
public theorem finite_setOf_isInverseExceptional {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : Mori.IsNormalVariety k sX) (hY : Mori.IsNormalVariety k sY)
    (φ : X.RationalMap Y) (hφ : Mori.RationalMap.IsBirational φ)
    (hφ₁ : IsMorphismInCodimOne φ) :
    {F : Mori.PrimeDivisor Y | IsInverseExceptional φ F}.Finite ∧
      ∀ (g : Y ⟶ X), IsProper g → g ≫ sX = sY →
        Mori.RationalMap.IsInverse (X := Y) g.toRationalMap φ →
        ∀ F : Mori.PrimeDivisor Y, IsInverseExceptional φ F ↔ IsExceptionalPrimeDivisor sX g F :=
  ⟨finite_setOf_isInverseExceptional_of_isBirational hX hY φ hφ,
    fun g hg hgs hinv =>
      isInverseExceptional_iff_isExceptionalPrimeDivisor hX hY φ hφ₁ g hg hgs hinv⟩

end MMP.Flips.RationalMap

/-! ### Eventually free divisors under crepant fibre-space morphisms -/

namespace MMP.Flips

open MMP.Mori MMP.Fourfold Opposite

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section BasepointFree

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

omit [IsIntegral X] in
private theorem coeff_add_principalDivisor (M : Divisor X) (φ : (RationalFunctions X)ˣ)
    (P : MMP.Mori.PrimeDivisor X) : (M + principalDivisor φ).coeff P = M.coeff P + P.ord φ := by
  rw [DivisorWithCoeffs.coeff_add, coeff_principalDivisor]

/-- `|M|` is basepoint free iff every point has a unit `φ` with `M + div φ` effective and of
coefficient zero along every prime divisor through the point. -/
private theorem isBasepointFree_iff (M : Divisor X) :
    M.IsBasepointFree ↔ ∀ x : X, ∃ φ : (RationalFunctions X)ˣ,
      (∀ P : MMP.Mori.PrimeDivisor X, 0 ≤ M.coeff P + P.ord φ) ∧
      ∀ P : MMP.Mori.PrimeDivisor X, x ∈ P.support → M.coeff P + P.ord φ = 0 := by
  have hcoeff : ∀ (σ : M.divisorialSubmodule ⊤) (hσ : σ ≠ 0) (P : MMP.Mori.PrimeDivisor X),
      (M.zeroDivisor σ hσ).coeff P =
        M.coeff P + P.ord (Divisor.isUnit_sectionToRationalFunctions hσ).unit := by
    intro σ hσ P
    rw [Divisor.zeroDivisor_eq, add_comm, coeff_add_principalDivisor]
  constructor
  · intro h x
    have hx : x ∉ (M.baseLocus : Set X) := by
      rw [show M.baseLocus = ⊥ from h]; exact fun h => h
    rw [Divisor.mem_baseLocus_iff] at hx
    push Not at hx
    obtain ⟨σ, hσ, hxσ⟩ := hx
    refine ⟨(Divisor.isUnit_sectionToRationalFunctions hσ).unit, fun P => ?_, fun P hP => ?_⟩
    · rw [← hcoeff σ hσ P]; exact Divisor.zeroDivisor_nonneg M σ hσ P
    · rw [← hcoeff σ hσ P]
      by_contra hne
      exact hxσ (DivisorWithCoeffs.support_subset_supp hne hP)
  · intro h
    refine le_bot_iff.mp fun x hx => ?_
    exfalso
    obtain ⟨φ, hφ0, hφx⟩ := h x
    let σ : M.divisorialSubmodule ⊤ :=
      ⟨fun Z => (φ : RationalFunctions X) Z.1, isDivisorialSection_of_unit φ fun P _ => hφ0 P⟩
    have hσφ : Divisor.sectionToRationalFunctions σ = (φ : RationalFunctions X) := rfl
    have hσ : σ ≠ 0 := by
      intro h0
      have h1 := congrArg Divisor.sectionToRationalFunctions h0
      rw [hσφ] at h1
      obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
        ⟨⟨_, irreducibleComponent_mem_irreducibleComponents (genericPoint X)⟩⟩
      have h2 := congrFun h1 Z
      exact ((φ.isUnit.map (Pi.evalRingHom _ Z)).ne_zero) (h2.trans (by
        change Divisor.sectionToRationalFunctions (0 : M.divisorialSubmodule ⊤) Z = 0
        rfl))
    have hu : (Divisor.isUnit_sectionToRationalFunctions hσ).unit = φ :=
      Units.ext (by rw [IsUnit.unit_spec]; exact hσφ)
    have hx' := (Divisor.mem_baseLocus_iff M x).mp hx σ hσ
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hx'
    rw [hcoeff σ hσ E, hu, hφx E hxE] at hE
    exact hE rfl

private theorem isBasepointFree_add_principalDivisor {M : Divisor X} (hM : M.IsBasepointFree)
    (ψ : (RationalFunctions X)ˣ) : (M + principalDivisor ψ).IsBasepointFree := by
  rw [isBasepointFree_iff] at hM ⊢
  intro x
  obtain ⟨φ, h0, hx⟩ := hM x
  have key : ∀ P : MMP.Mori.PrimeDivisor X,
      (M + principalDivisor ψ).coeff P + P.ord (ψ⁻¹ * φ) = M.coeff P + P.ord φ := by
    intro P
    rw [coeff_add_principalDivisor, PrimeDivisor.ord_mul, PrimeDivisor.ord_inv]
    ring
  exact ⟨ψ⁻¹ * φ, fun P => (key P).symm ▸ h0 P, fun P hP => (key P).trans (hx P hP)⟩

private theorem isBasepointFree_nsmul {M : Divisor X} (hM : M.IsBasepointFree) (n : ℕ) :
    (n • M).IsBasepointFree := by
  rw [isBasepointFree_iff] at hM ⊢
  intro x
  obtain ⟨φ, h0, hx⟩ := hM x
  have key : ∀ P : MMP.Mori.PrimeDivisor X,
      (n • M).coeff P + P.ord (φ ^ n) = n * (M.coeff P + P.ord φ) := by
    intro P
    rw [DivisorWithCoeffs.coeff_smul, PrimeDivisor.ord_pow, nsmul_eq_mul, nsmul_eq_mul]
    ring
  refine ⟨φ ^ n, fun P => ?_, fun P hP => ?_⟩
  · rw [key P]; exact mul_nonneg (by positivity) (h0 P)
  · rw [key P, hx P hP, mul_zero]

end BasepointFree

section Pullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y]
  [IsNormal Y] {p : X ⟶ Y}

/-- The pull-back of a Cartier divisor `G` has coefficient zero along every prime divisor meeting
`p⁻¹(Y ∖ Supp G)`. -/
private theorem coeff_eq_zero_of_isPullback {G : Divisor Y}
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp} {G' : Divisor X}
    (h : G.IsPullback p hB G') {x : X} (hx : p x ∉ G.supp) (F : MMP.Mori.PrimeDivisor X)
    (hF : x ∈ F.support) : G'.coeff F = 0 := by
  let U : Y.Opens := ⟨(G.supp : Set Y)ᶜ, G.isClosed_supp.isOpen_compl⟩
  have hloc : G.IsLocalEquation U 1 := by
    intro E ⟨y, hyE, hyU⟩
    rw [PrimeDivisor.ord_one]
    by_contra hne
    exact hyU (DivisorWithCoeffs.support_subset_supp hne hyE)
  have hF' : (F.support ∩ p ⁻¹ᵁ U).Nonempty := ⟨x, hF, hx⟩
  rw [h U 1 hloc F hF', pullbackComponent_eq hB hloc _ (mem_pointComponent _) 1 (by simp),
    map_one, PrimeDivisor.ordUnit_one]

variable [IsIntegral X] [IsIntegral Y] [CompactSpace X] [CompactSpace Y] [IsDominant p]

/-- If `|M|` is basepoint free, so is `|p^* M|`. -/
private theorem isBasepointFree_of_isPullback {M : Divisor Y} (hMc : M.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ M.supp} {M' : Divisor X}
    (h : M.IsPullback p hB M') (hM : M.IsBasepointFree) : M'.IsBasepointFree := by
  rw [isBasepointFree_iff] at hM ⊢
  intro x
  obtain ⟨φ, h0, hx⟩ := hM (p x)
  have hφ := map_componentGenericPoint_notMem_supp_of_isDominant p (principalDivisor φ)
  have hG := Divisor.IsPullback.add hMc (Divisor.isCartier_principalDivisor φ)
    (map_componentGenericPoint_notMem_supp_of_isDominant p _) h
    (Divisor.isPullback_principalDivisor φ hφ)
  refine ⟨pullbackRationalFunction p φ hφ, fun F => ?_, fun F hF => ?_⟩
  · rw [← coeff_add_principalDivisor]
    exact coeff_nonneg_of_isPullback_of_isEffectiveOn
      (hMc.add (Divisor.isCartier_principalDivisor φ)) (V := ⊤)
      (fun P _ => by rw [coeff_add_principalDivisor]; exact h0 P) hG F
      ((F.genericPoint_mem_iff _).mp trivial)
  · rw [← coeff_add_principalDivisor]
    refine coeff_eq_zero_of_isPullback hG (x := x) ?_ F hF
    intro hmem
    obtain ⟨E, hE, hxE⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    exact hE (by rw [coeff_add_principalDivisor]; exact hx E hxE)

omit [CompactSpace X] [CompactSpace Y] in
/-- A dominant morphism of integral schemes maps the generic point of `X` into every nonempty
open of `Y`. -/
private theorem map_componentGenericPoint_mem (Z : irreducibleComponents X) {U : Y.Opens}
    (hU : (U : Set Y).Nonempty) : p (componentGenericPoint X Z) ∈ U := by
  rw [componentGenericPoint_eq_genericPoint, map_genericPoint_of_isDominant]
  exact (genericPoint_spec Y).mem_open_set_iff U.isOpen |>.mpr (by simpa using hU)

omit [CompactSpace X] [CompactSpace Y] in
/-- For `p` dominant, `𝒪_{Y, p(η_X)}` is the function field of `Y`, so the stalk map at the
generic point of `X` is injective. -/
private theorem injective_stalkMap_componentGenericPoint (Z : irreducibleComponents X) :
    Function.Injective (p.stalkMap (componentGenericPoint X Z)).hom := by
  have hF : IsField (Y.presheaf.stalk (p (componentGenericPoint X Z))) := by
    have := RationalFunctions.isField_stalk Y (pointComponent (genericPoint Y))
    rwa [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant p,
      ← componentGenericPoint_eq_genericPoint Z] at this
  let := hF.toField
  exact (p.stalkMap (componentGenericPoint X Z)).hom.injective

variable (hp : ∀ U : Y.Opens, IsIso (p.app U))

include hp

/-- **Descent of regular functions.** If `p_* 𝒪_X = 𝒪_Y`, a rational function on `X` with no
poles on `p⁻¹U` is the pull-back of a regular function on `U`. -/
private theorem exists_section_of_ord_nonneg (U : Y.Opens) (Z : irreducibleComponents X)
    (hZ : p (componentGenericPoint X Z) ∈ U) (χ : (RationalFunctions X)ˣ)
    (hχ : ∀ F : MMP.Mori.PrimeDivisor X, (F.support ∩ p ⁻¹ᵁ U).Nonempty → 0 ≤ F.ord χ) :
    ∃ u : Γ(Y, U),
      (p.stalkMap _).hom (Y.presheaf.germ U _ hZ u) = (χ : RationalFunctions X) Z := by
  have hφ : (0 : Divisor X).IsDivisorialSection (p ⁻¹ᵁ U)
      fun Z' => (χ : RationalFunctions X) Z'.1 :=
    isDivisorialSection_of_unit χ fun P hP => by simpa using hχ P hP
  obtain ⟨s, hs⟩ := hφ.exists_eq
  refine ⟨inv (p.app U) s, ?_⟩
  rw [Scheme.Hom.germ_stalkMap_apply, IsIso.inv_hom_id_apply]
  exact congrFun hs ⟨Z, hZ⟩

/-- If `p_* 𝒪_X = 𝒪_Y`, every rational function `ψ` on `X` with `p^* M + div ψ` effective is the
pull-back of a rational function on `Y`. -/
private theorem exists_pullbackRationalFunction_eq_of_isPullback {M : Divisor Y}
    (hMc : M.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ M.supp} {M' : Divisor X}
    (h : M.IsPullback p hB M') (ψ : (RationalFunctions X)ˣ)
    (hψ : ∀ F : MMP.Mori.PrimeDivisor X, 0 ≤ M'.coeff F + F.ord ψ) :
    ∃ (φ : (RationalFunctions Y)ˣ) (hφ : ∀ Z : irreducibleComponents X,
      p (componentGenericPoint X Z) ∉ (principalDivisor φ).supp),
      pullbackRationalFunction p φ hφ = ψ := by
  have := subsingleton_irreducibleComponents (X := X)
  have := subsingleton_irreducibleComponents (X := Y)
  set Z : irreducibleComponents X := pointComponent (genericPoint X)
  let U : Y.Opens := ⟨(M.supp : Set Y)ᶜ, M.isClosed_supp.isOpen_compl⟩
  have hZU : p (componentGenericPoint X Z) ∈ U := hB Z
  obtain ⟨u, hu⟩ := exists_section_of_ord_nonneg hp U Z hZU ψ fun F ⟨x, hxF, hxU⟩ => by
    have := hψ F
    rwa [coeff_eq_zero_of_isPullback h hxU F hxF, zero_add] at this
  set b := Y.presheaf.germ U _ hZU u
  set W := pointComponent (p (componentGenericPoint X Z))
  have hW : p (componentGenericPoint X Z) ∈ W.1 := mem_pointComponent _
  have hb0 : (stalkToRationalFunctions Y hW).hom b ≠ 0 := by
    intro h0
    have hb : b = 0 := stalkToRationalFunctions_injective hW (h0.trans (map_zero _).symm)
    have := (ψ.isUnit.map (Pi.evalRingHom _ Z)).ne_zero
    rw [Pi.evalRingHom_apply, ← hu, hb, map_zero] at this
    exact this rfl
  let sY : RationalFunctions Y := fun W' => (stalkToRationalFunctions Y
    (mem_irreducibleComponent_of_irreducibleSpace W' (p (componentGenericPoint X Z)))).hom b
  have hsYW : sY W = (stalkToRationalFunctions Y hW).hom b := rfl
  have hsY : IsUnit sY := by
    refine Pi.isUnit_iff.mpr fun W' => ?_
    obtain rfl : W = W' := Subsingleton.elim _ _
    exact isUnit_of_ne_zero_stalk W hb0
  set φ := hsY.unit
  have hφ : (φ : RationalFunctions Y) = sY := hsY.unit_spec
  refine ⟨φ, map_componentGenericPoint_notMem_supp_of_isDominant p _, ?_⟩
  ext Z'
  obtain rfl : Z = Z' := Subsingleton.elim _ _
  obtain ⟨a', ha'⟩ := (Divisor.isLocalEquation_principalDivisor φ ⊤).exists_unit_stalk trivial
    (map_componentGenericPoint_notMem_supp_of_isDominant p _ Z) hW
  have haa : (a' : Y.presheaf.stalk _) = b :=
    stalkToRationalFunctions_injective hW (by rw [ha', hφ, hsYW])
  have hval : ((pullbackRationalFunction p φ
      (map_componentGenericPoint_notMem_supp_of_isDominant p _) : RationalFunctions X) Z) =
      (pullbackComponent p (map_componentGenericPoint_notMem_supp_of_isDominant p _)
        (Divisor.isLocalEquation_principalDivisor φ ⊤) Z trivial).val := rfl
  rw [hval]
  refine (congrArg Units.val (pullbackComponent_eq _ _ _ hW a' ha')).trans ?_
  change (p.stalkMap (componentGenericPoint X Z)).hom
    (a' : Y.presheaf.stalk (p (componentGenericPoint X Z))) = _
  rw [haa, hu]

/-- If `p_* 𝒪_X = 𝒪_Y`, a Cartier divisor whose pull-back is effective is effective. -/
private theorem coeff_nonneg_of_isPullback {G : Divisor Y} (hGc : G.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp} {G' : Divisor X}
    (h : G.IsPullback p hB G') (hG' : 0 ≤ G') (E : MMP.Mori.PrimeDivisor Y) : 0 ≤ G.coeff E := by
  have := subsingleton_irreducibleComponents (X := Y)
  obtain ⟨U, hU, g, hg⟩ := hGc E.genericPoint
  set Z : irreducibleComponents X := pointComponent (genericPoint X)
  have hZU : p (componentGenericPoint X Z) ∈ U := map_componentGenericPoint_mem Z ⟨_, hU⟩
  have hg' := h.isLocalEquation hg
  obtain ⟨u, hu⟩ := exists_section_of_ord_nonneg hp U Z hZU (pullbackLocalEquation p hB hg)
    fun F hF => by rw [← hg' F hF]; exact hG' F
  have hpc := pullbackLocalEquation_apply p hB hg Z hZU
  have hspec := (hg.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose_spec
  have hua : Y.presheaf.germ U _ hZU u =
      (hg.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose := by
    apply injective_stalkMap_componentGenericPoint Z
    rw [hu]
    exact congrArg Units.val hpc
  have hEU : (E.support ∩ U).Nonempty := (E.genericPoint_mem_iff U).mp hU
  have hord := ((Divisor.structureSheafToDivisorialSheaf (le_refl (0 : Divisor Y))).app U u).2 E
    hEU
  rw [Divisor.coe_structureSheafToDivisorialSheaf_app] at hord
  have hall : ∀ (W' : irreducibleComponents Y) (hW' : componentGenericPoint Y W' ∈ U),
      Y.presheaf.germ U _ hW' u = (g : RationalFunctions Y) W' := by
    intro W' hW'
    obtain rfl : pointComponent (p (componentGenericPoint X Z)) = W' := Subsingleton.elim _ _
    rw [← hspec, ← hua, stalkToRationalFunctions, TopCat.Presheaf.germ_stalkSpecializes_apply]
  have hcomp : (toRationalFunctionsPresheaf Y).app (op U) u
      ⟨E.component, E.componentGenericPoint_mem_of_nonempty hEU⟩ =
      (g : RationalFunctions Y) E.component := by
    rw [toRationalFunctionsPresheaf_app_apply]
    exact hall _ _
  rw [hcomp] at hord
  rw [hg E hEU]
  rcases hord with h0 | h1
  · exact absurd h0 ((g.isUnit.map (Pi.evalRingHom _ E.component)).ne_zero)
  · rwa [E.valuation_component, DivisorWithCoeffs.coeff_zero, neg_zero,
      WithZero.exp_le_exp] at h1

omit hp in
/-- A local equation `g` near `p x` of an effective divisor `G` whose pull-back misses `x` is a
unit at `p x`: it is regular there, and `p^* g` is a unit at `x`, the stalk map being local. -/
private theorem exists_isUnit_stalk_of_isPullback {G : Divisor Y}
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp} {G' : Divisor X}
    (h : G.IsPullback p hB G') (hG : 0 ≤ G) {x : X}
    (hx : ∀ F : MMP.Mori.PrimeDivisor X, x ∈ F.support → G'.coeff F = 0) {U : Y.Opens}
    (hyU : p x ∈ U) {g : (RationalFunctions Y)ˣ} (hg : G.IsLocalEquation U g) :
    ∃ r : Y.presheaf.stalk (p x), IsUnit r ∧ ∀ (W' : irreducibleComponents Y) (hW' : p x ∈ W'.1),
      (stalkToRationalFunctions Y hW').hom r = (g : RationalFunctions Y) W' := by
  have := subsingleton_irreducibleComponents (X := Y)
  set Z : irreducibleComponents X := pointComponent (genericPoint X)
  have hxZ : x ∈ Z.1 := mem_irreducibleComponent_of_irreducibleSpace Z x
  have hZU : p (componentGenericPoint X Z) ∈ U := map_componentGenericPoint_mem Z ⟨_, hyU⟩
  have hsec : (0 : Divisor Y).IsDivisorialSection U fun W => (g : RationalFunctions Y) W.1 :=
    isDivisorialSection_of_unit g fun P hP => by
      rw [DivisorWithCoeffs.coeff_zero, zero_add, ← hg P hP]; exact hG P
  obtain ⟨r, hr0⟩ := hsec.exists_stalk_eq hyU (mem_irreducibleComponent_of_irreducibleSpace
    (pointComponent (p (componentGenericPoint X Z))) (p x))
  have hr : ∀ (W' : irreducibleComponents Y) (hW' : p x ∈ W'.1),
      (stalkToRationalFunctions Y hW').hom r = (g : RationalFunctions Y) W' := by
    intro W' hW'
    obtain rfl : pointComponent (p (componentGenericPoint X Z)) = W' := Subsingleton.elim _ _
    exact hr0
  have hg' := h.isLocalEquation hg
  obtain ⟨c, hc⟩ := exists_unit_stalk_of_forall_ord_eq_zero hxZ (pullbackLocalEquation p hB hg)
    fun F hF => by rw [← hg' F ⟨x, hF, hyU⟩]; exact hx F hF
  have hsp : componentGenericPoint X Z ⤳ x :=
    (isGenericPoint_componentGenericPoint X Z).specializes hxZ
  have hsp' : p (componentGenericPoint X Z) ⤳ p x := p.base.hom.map_specializes hsp
  have hspec := (hg.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose_spec
  have hra : (Y.presheaf.stalkSpecializes hsp').hom r =
      (hg.exists_unit_stalk hZU (hB Z) (mem_pointComponent _)).choose := by
    apply stalkToRationalFunctions_injective (mem_pointComponent _)
    rw [hspec]
    change (Y.presheaf.stalkSpecializes hsp' ≫ Y.presheaf.stalkSpecializes _).hom r = _
    rw [TopCat.Presheaf.stalkSpecializes_comp]
    exact hr _ (mem_irreducibleComponent_of_irreducibleSpace _ _)
  have hrc : (p.stalkMap x).hom r = c := by
    apply stalkToRationalFunctions_injective hxZ
    rw [hc]
    have hpc := congrArg Units.val (pullbackLocalEquation_apply p hB hg Z hZU)
    change _ = ((Units.map (RationalFunctions.component X Z).toMonoidHom
      (pullbackLocalEquation p hB hg) : (X.presheaf.stalk (componentGenericPoint X Z))ˣ) :
        X.presheaf.stalk (componentGenericPoint X Z))
    rw [hpc]
    change (X.presheaf.stalkSpecializes hsp).hom _ = (p.stalkMap _).hom _
    rw [← hra, Scheme.Hom.stalkSpecializes_stalkMap_apply]
  exact ⟨r, isUnit_of_map_unit (p.stalkMap x).hom r (hrc ▸ c.isUnit), hr⟩

omit hp in
/-- An effective Cartier divisor `G` whose pull-back misses `x` misses `p x`: a local equation
`g` of `G` near `p x` is a unit at `p x`, so it has order zero along every prime divisor
through `p x`. -/
private theorem coeff_eq_zero_of_isPullback_of_nonneg {G : Divisor Y} (hGc : G.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ G.supp} {G' : Divisor X}
    (h : G.IsPullback p hB G') (hG : 0 ≤ G) {x : X}
    (hx : ∀ F : MMP.Mori.PrimeDivisor X, x ∈ F.support → G'.coeff F = 0)
    (E : MMP.Mori.PrimeDivisor Y) (hE : p x ∈ E.support) : G.coeff E = 0 := by
  obtain ⟨U, hyU, g, hg⟩ := hGc (p x)
  obtain ⟨r, hru, hr⟩ := exists_isUnit_stalk_of_isPullback h hG hx hyU hg
  have hyE : p x ∈ E.component.1 := mem_irreducibleComponent_of_irreducibleSpace _ _
  rw [hg E ⟨_, hE, hyU⟩, PrimeDivisor.ord_eq_ordUnit]
  have hspE : E.genericPoint ⤳ p x := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  refine E.ordUnit_eq_zero_of_isUnit (a := (Y.presheaf.stalkSpecializes hspE).hom r)
    (hru.map _) ?_
  rw [E.toComponent_stalkSpecializes hspE hyE, hr]
  rfl

/-- If `p_* 𝒪_X = 𝒪_Y` and `p` is surjective, `|M|` is basepoint free when `|p^* M|` is. -/
private theorem isBasepointFree_of_isPullback_of_surjective (hs : Function.Surjective p)
    {M : Divisor Y} (hMc : M.IsCartier)
    {hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ M.supp} {M' : Divisor X}
    (h : M.IsPullback p hB M') (hM' : M'.IsBasepointFree) : M.IsBasepointFree := by
  rw [isBasepointFree_iff] at hM' ⊢
  intro y
  obtain ⟨x, rfl⟩ := hs y
  obtain ⟨ψ, h0, hx⟩ := hM' x
  obtain ⟨φ, hφ, hφψ⟩ := exists_pullbackRationalFunction_eq_of_isPullback hp hMc h ψ h0
  have hGc := hMc.add (Divisor.isCartier_principalDivisor φ)
  have hG := Divisor.IsPullback.add hMc (Divisor.isCartier_principalDivisor φ)
    (map_componentGenericPoint_notMem_supp_of_isDominant p _) h
    (Divisor.isPullback_principalDivisor φ hφ)
  rw [hφψ] at hG
  have hG' : 0 ≤ M' + principalDivisor ψ := fun F => by
    rw [Finsupp.zero_apply, ← DivisorWithCoeffs.coeff_apply, coeff_add_principalDivisor]
    exact h0 F
  have hGnn : 0 ≤ M + principalDivisor φ := fun E => coeff_nonneg_of_isPullback hp hGc hG hG' E
  refine ⟨φ, fun E => by rw [← coeff_add_principalDivisor]; exact hGnn E, fun E hE => ?_⟩
  rw [← coeff_add_principalDivisor]
  exact coeff_eq_zero_of_isPullback_of_nonneg hGc hG hGnn
    (fun F hF => by rw [coeff_add_principalDivisor]; exact hx F hF) E hE

end Pullback

/-- A morphism with `p_* 𝒪_X = 𝒪_Y` onto an integral scheme is dominant: a nonempty open of `Y`
missing the image of `p` would have both `Γ(Y, V) ≅ Γ(X, ∅) = 0` and `1 ≠ 0` in its stalks. -/
private theorem isDominant_of_isIso_app {X Y : Scheme.{u}} [IsIntegral Y] (p : X ⟶ Y)
    (hp : ∀ U : Y.Opens, IsIso (p.app U)) : IsDominant p := by
  refine ⟨dense_iff_inter_open.mpr fun V hV ⟨y, hy⟩ => ?_⟩
  by_contra hempty
  let V' : Y.Opens := ⟨V, hV⟩
  have hbot : p ⁻¹ᵁ V' = ⊥ := TopologicalSpace.Opens.ext <| Set.eq_empty_iff_forall_notMem.mpr
    fun x hx => hempty ⟨p x, hx, x, rfl⟩
  have : Subsingleton Γ(X, p ⁻¹ᵁ V') := by rw [hbot]; infer_instance
  have : Subsingleton Γ(Y, V') := (ConcreteCategory.bijective_of_isIso (p.app V')).1.subsingleton
  have h10 := congrArg (Y.presheaf.germ V' y hy).hom (Subsingleton.elim (1 : Γ(Y, V')) 0)
  rw [map_one, map_zero] at h10
  exact one_ne_zero h10

/-- **Eventually free under a crepant fibre space** (FA 15.4.4). Let `p : X ⟶ Y` be a proper
morphism of normal varieties over `k` with `p_* 𝒪_X = 𝒪_Y`, `N` a `ℚ`-Cartier `ℚ`-divisor on `Y`
and `L` a `ℚ`-divisor on `X` with `L ∼_ℚ p^* N`. Then `L` is eventually free if and only if `N`
is eventually free. -/
@[mmp "lem_fa15_eventually_free_crepant_morphism"]
public theorem isEventuallyFree_iff_of_qLinearlyEquivalent_pullback (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsLocallyNoetherian Y] [IsNormal Y]
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k sY)
    (p : X ⟶ Y) [IsProper p] (hps : p ≫ sY = sX) (hp : ∀ U : Y.Opens, IsIso (p.app U))
    {L : QDivisor X} {N : QDivisor Y} (hN : N.IsQCartier)
    (hLN : ∃ hB : ∀ Z : irreducibleComponents X, p (componentGenericPoint X Z) ∉ N.supp,
      L.QLinearlyEquivalent (N.pullback hN hB)) :
    IsEventuallyFree k sX L ↔ IsEventuallyFree k sY N := by
  have := hX.1.toIsIntegral
  have := hY.1.toIsIntegral
  have : CompactSpace Y := by
    have := hY.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace sY
  have := isDominant_of_isIso_app p hp
  obtain ⟨hB, m, hm, φ, hφ⟩ := hLN
  constructor
  · rintro ⟨hX', k', hk', M, hM, hMc, hMf⟩
    obtain ⟨n, hn, D, hD, hDc⟩ := hN.exists_pos
    obtain ⟨D', hD', hDp⟩ := QDivisor.isPullback_pullback hN hB n hn D hD hDc
    refine ⟨hY, k' * m * n, by positivity, ((k' * m : ℕ) : ℤ) • D, ?_, hDc.zsmul _, ?_⟩
    · rw [map_zsmul, hD, smul_smul]; push_cast; ring_nf
    · refine isBasepointFree_of_isPullback_of_surjective hp p.surjective (hDc.zsmul _)
        (hDp.zsmul hDc _ (map_componentGenericPoint_notMem_supp_of_isDominant p _)) ?_
      have key : ((k' * m : ℕ) : ℤ) • D' =
          ((m * n : ℕ) • M) + principalDivisor (φ ^ (-((k' * n : ℕ) : ℤ))) := by
        apply Divisor.toQDivisor_injective
        ext E
        have h1 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hφ
        have h2 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hM
        have h3 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hD'
        simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
          DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_principalDivisor,
          PrimeDivisor.ord_zpow, map_zsmul, map_add, map_nsmul, zsmul_eq_mul, nsmul_eq_mul,
          smul_eq_mul] at h1 h2 h3 ⊢
        push_cast at h1 h2 h3 ⊢
        linear_combination ((k' : ℚ) * m) * h3 - ((m : ℚ) * n) * h2 - ((k' : ℚ) * n) * h1
      rw [key]
      exact isBasepointFree_add_principalDivisor (isBasepointFree_nsmul hMf _) _
  · rintro ⟨hX', k', hk', M, hM, hMc, hMf⟩
    obtain ⟨D', hD', hDp⟩ := QDivisor.isPullback_pullback hN hB k' hk' M hM hMc
    have hD'c : D'.IsCartier := isCartier_of_isPullback p hMc hDp
    refine ⟨hX, k' * m, by positivity, ((m : ℤ) • D') + principalDivisor (φ ^ (k' : ℤ)), ?_,
      (hD'c.zsmul _).add (Divisor.isCartier_principalDivisor _), ?_⟩
    · ext E
      have h1 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hφ
      have h3 := congrArg (fun G => DivisorWithCoeffs.coeff G E) hD'
      simp only [DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_sub,
        DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_principalDivisor,
        PrimeDivisor.ord_zpow, map_zsmul, map_add, zsmul_eq_mul, smul_eq_mul] at h1 h3 ⊢
      push_cast at h1 h3 ⊢
      linear_combination (m : ℚ) * h3 - (k' : ℚ) * h1
    · refine isBasepointFree_add_principalDivisor ?_ _
      simpa [natCast_zsmul] using
        isBasepointFree_nsmul (isBasepointFree_of_isPullback hMc hDp hMf) m

end MMP.Flips

end
