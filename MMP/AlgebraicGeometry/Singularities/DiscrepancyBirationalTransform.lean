module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Slc.NormalizedSections
public import MMP.AlgebraicGeometry.Singularities.PairClasses
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.Combinatorics.WeightedGraph.Basic
public import MMP.Combinatorics.WeightedGraph.Shapes
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.Divisor.Principal
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Chow.FieldSituation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal

/-!
# Flips and abundance: discrepancies, weighted graphs and slc curves

This file collects results from Kollár et al., *Flips and abundance for algebraic threefolds*,
on discrepancies of pairs, on the determinants of weighted dual graphs, and on normalized
pluricanonical sections of slc curves.

* Discrepancies (FA 1.15, 2.5). The discrepancy `a_ω(E, X, D)` of a divisor `E` over a normal
  variety `X` with respect to a `ℚ`-divisor `D` depends only on the valuation `ord_E`, and it
  agrees with the discrepancy `a(ord_E, D)` computed from a canonical divisor.
* `𝓕`-birational transforms (FA 2.7, 2.23.2). For `G = φ_*(D_X) + ∑ c_i F_i`, the discrepancy
  of `ord_{F_i}` with respect to `(Y, G)` is `-c_i`, and `c_i ≥ -a(F_i, D_X)` when `(X, D_X)` is
  log canonical.
* Surface germs (FA 3.0.2–3.0.3). The log discrepancy vector of a resolution of a surface germ
  consists of the log discrepancies of the exceptional curves when `K_X + B` is `ℝ`-Cartier near
  `P`; it is nonnegative when `(X, B)` is log canonical near `P`.
* Weighted graphs (FA 3.1). Subgraphs of negative definite graphs are negative definite, their
  determinants `Δ(S)` are positive, and the cofactors of the matrix of a weighted tree are
  `-(-1)^N Δ(Γ - path(u, w))`.
* A general codimension-two subvariety of a component `P` of a `ℚ`-divisor `D` meets `P` with
  multiplicity `1` and no other component of `D` (FA 4.9.1).
* On an slc curve the normalized sections of `𝒪(m(K_C + Δ))` form an affine subspace
  (FA 12.2.9).

## Main results

* `MMP.Flips.IsQDiscrepancyWith.eq`
* `MMP.Flips.IsQDiscrepancyWith.isDiscrepancy`
* `MMP.Flips.IsFBirationalTransform.isDiscrepancy_divisorialValuation`
* `MMP.Flips.IsFBirationalTransform.neg_le_of_isLogCanonical`
* `MMP.Flips.IsGermLogDiscrepancyVector.isLogDiscrepancy`
* `MMP.Flips.IsGermLogDiscrepancyVector.nonneg_of_isLogCanonical`
* `MMP.Flips.WeightedGraph.IsSubgraph.isNegDef`
* `MMP.Flips.WeightedGraph.IsNegDef.delta_pos`
* `MMP.Flips.WeightedGraph.adjugate_matrix_apply_of_isTree`
* `MMP.Flips.exists_codimension_eq_two_multiplicityAlong_eq`
* `MMP.Flips.NormalizationComponents.exists_affineSubspace_eq_setOf_isNormalizedSlcSection`

## Implementation notes

FA works over `ℂ`. Where the theory of canonical forms needs it the base field is assumed
perfect, so that `Ω^n_{k(X)/k}` is one-dimensional; elsewhere it is arbitrary. Discrepancies are
predicates on their values (`MMP.Flips.IsQDiscrepancyWith`, `MMP.Flips.IsDiscrepancy`), so an
equality of discrepancies is stated as "a value of one is a value of the other".

Mathlib's `Matrix.PosDef.det_pos` is stated over `RCLike` fields, which excludes `ℚ`; the
positivity of `Δ(S)` is proved by diagonalising the bilinear form of a positive definite matrix
over a linearly ordered field.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips.WeightedGraph

open Finset Matrix Equiv

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Termwise comparison of the quadratic forms of `-M(Γ')` at `x` and of `-M(Γ|_S)` at `|x|`. -/
private lemma abs_mul_neg_matrix_mul_abs_le {S : Finset V}
    {Γ' : WeightedGraph S} {Γ : WeightedGraph V} (h : Γ'.IsSubgraph Γ) (x : S → ℚ) (j k : S) :
    |x j| * (-(Γ.matrix.map ((↑) : ℤ → ℚ)) j k * |x k|) ≤
      x j * (-(Γ'.matrix.map ((↑) : ℤ → ℚ)) j k * x k) := by
  simp only [Matrix.neg_apply, map_apply, WeightedGraph.matrix, of_apply]
  by_cases hjk : j = k
  · subst hjk
    simp only [if_true, h.weight_eq j]
    rw [mul_left_comm |x j|, abs_mul_abs_self, mul_left_comm]
  · have hjk' : (j : V) ≠ k := fun e => hjk (Subtype.ext e)
    simp only [hjk, hjk', if_false, Int.cast_natCast]
    have hle : (Γ'.edgeWeight j k : ℚ) ≤ Γ.edgeWeight j k := by
      exact_mod_cast h.edgeWeight_le j k hjk
    have h1 : x j * x k ≤ |x j| * |x k| := by rw [← abs_mul]; exact le_abs_self _
    nlinarith [mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℚ) (Γ'.edgeWeight j k)),
      mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ |x j| * |x k|)]

/-- A subgraph `Γ' ⊆ Γ` of a negative definite weighted graph `Γ` is negative definite. -/
@[mmp "lem_fa3_subgraph_negative_definite"]
public theorem IsSubgraph.isNegDef {S : Finset V} {Γ' : WeightedGraph S} {Γ : WeightedGraph V}
    (h : Γ'.IsSubgraph Γ) (hΓ : Γ.IsNegDef) : Γ'.IsNegDef := by
  have hA := posDef_iff_dotProduct_mulVec.1 (hΓ.submatrix (e := ((↑) : S → V))
    Subtype.val_injective)
  refine posDef_iff_dotProduct_mulVec.2 ⟨by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact (Γ'.matrix_isSymm.map _).neg, ?_⟩
  intro x hx
  refine (hA.2 (x := fun j => |x j|) fun h0 => hx (funext fun j => by
    simpa using congrFun h0 j)).trans_le ?_
  simp only [dotProduct, mulVec, star_trivial, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
    abs_mul_neg_matrix_mul_abs_le h x j k

/-- A positive definite symmetric matrix over a linearly ordered field with trivial star has
positive determinant. -/
private theorem posDef_det_pos {K n : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [StarRing K] [TrivialStar K] [Fintype n] [DecidableEq n] {A : Matrix n n K}
    (hA : A.PosDef) : 0 < A.det := by
  letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  have hT : Aᵀ = A := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hsymm : LinearMap.IsSymm (Matrix.toBilin' A) := by
    refine ⟨fun x y => ?_⟩
    simp only [RingHom.id_apply, Matrix.toBilin'_apply']
    rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hT]
  obtain ⟨v₀, hv₀⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  let e := v₀.indexEquiv (Pi.basisFun K n)
  let v := v₀.reindex e
  have hv : ∀ i j, i ≠ j → Matrix.toBilin' A (v i) (v j) = 0 := fun i j h => by
    have h' : e.symm i ≠ e.symm j := e.symm.injective.ne h
    simpa [v, Module.Basis.reindex_apply] using hv₀ h'
  have key := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (Pi.basisFun K n) v
    (Matrix.toBilin' A)
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin'] at key
  have hd : LinearMap.BilinForm.toMatrix v (Matrix.toBilin' A) =
      Matrix.diagonal fun i => Matrix.toBilin' A (v i) (v i) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [h, hv i j h]
  have hpos : ∀ i, 0 < Matrix.toBilin' A (v i) (v i) := by
    intro i
    rw [Matrix.toBilin'_apply']
    simpa using hA.dotProduct_mulVec_pos (v.ne_zero i)
  have hdet := congrArg Matrix.det key
  rw [hd, Matrix.det_diagonal, det_mul, det_mul, det_transpose] at hdet
  have h1 : 0 < ∏ i, Matrix.toBilin' A (v i) (v i) := Finset.prod_pos fun i _ => hpos i
  nlinarith [mul_self_nonneg ((Pi.basisFun K n).toMatrix v).det]

/-- If `Γ` is negative definite, then `Δ(S) > 0` for every set `S` of vertices of `Γ`. -/
@[mmp "lem_fa3_graph_determinant_positive"]
public theorem IsNegDef.delta_pos {Γ : WeightedGraph V} (hΓ : Γ.IsNegDef) (S : Finset V) :
    0 < Γ.delta S := by
  have h : (0 : ℚ) < (-((Γ.restrict S).matrix.map ((↑) : ℤ → ℚ))).det :=
    posDef_det_pos ((Γ.restrict_isSubgraph S).isNegDef hΓ)
  rw [← Matrix.map_neg _ (Int.cast_neg), ← Int.cast_det] at h
  exact_mod_cast h

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

/-- In an acyclic graph, a permutation `σ` with `σ w = u` that sends every vertex other than
`w` to itself or to a neighbour agrees, on the path from `u` to `w`, with the cycle of that
path. -/
private theorem apply_eq_formPerm_of_admissible {G : SimpleGraph V} (hac : G.IsAcyclic)
    {u w : V} (p : G.Path u w) (σ : Perm V) (hσw : σ w = u)
    (hadm : ∀ i, i ≠ w → σ i ≠ i → G.Adj i (σ i)) :
    ∀ x ∈ p.1.support, σ x = p.1.support.formPerm x := by
  set f : ℕ → V := fun j => (σ ^ j) u with hf
  have hfs : ∀ j, f (j + 1) = σ (f j) := fun j => by
    simp only [hf, pow_succ', Perm.mul_apply]
  have hfa : ∀ a b, f (a + b) = (σ ^ b) (f a) := fun a b => by
    simp only [hf, ← Perm.mul_apply, ← pow_add, add_comm]
  have hex : ∃ k, f k = w := by
    refine ⟨orderOf σ - 1, ?_⟩
    have h1 : σ ^ (orderOf σ - 1) * σ = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos σ), pow_orderOf_eq_one]
    have := congrArg (fun g : Perm V => g w) h1
    simpa [hf, Perm.mul_apply, hσw] using this
  classical
  set k := Nat.find hex with hk
  have hkw : f k = w := Nat.find_spec hex
  have hmin : ∀ j < k, f j ≠ w := fun j hj => Nat.find_min hex hj
  have hadj : ∀ t < k, G.Adj (f t) (f (t + 1)) := by
    intro t ht
    rw [hfs]
    refine hadm _ (hmin t ht) fun hfix => hmin t ht ?_
    have := hfa t (k - t)
    rw [Nat.add_sub_cancel' ht.le, Perm.pow_apply_eq_self_of_apply_eq_self hfix] at this
    rw [← this, hkw]
  have hinj : ∀ a ≤ k, ∀ b ≤ k, f a = f b → a = b := by
    have key : ∀ a b, a < b → b ≤ k → f a ≠ f b := by
      intro a b hab hbk he
      have h1 : (σ ^ (b - a)) u = u := by
        have := hfa a (b - a)
        rw [Nat.add_sub_cancel' hab.le, ← he] at this
        simp only [hf] at this
        rw [← Perm.mul_apply, ← pow_add, add_comm, pow_add, Perm.mul_apply] at this
        exact (σ ^ a).injective this.symm
      have h2 := hfa (k - (b - a)) (b - a)
      rw [Nat.sub_add_cancel (by omega)] at h2
      have h3 : f (k - (b - a)) = w := by
        rw [← hkw, h2]
        simp only [hf]
        rw [← Perm.mul_apply, ← pow_add, add_comm, pow_add, Perm.mul_apply, h1]
      exact hmin _ (by omega) h3
    intro a ha b hb he
    rcases lt_trichotomy a b with h | h | h
    · exact absurd he (key a b h hb)
    · exact h
    · exact absurd he.symm (key b a h ha)
  obtain ⟨q, hq⟩ := exists_walk_support_eq f k hadj
  have hf0 : f 0 = u := by simp [hf]
  have hpath : (q.copy hf0 hkw).IsPath := by
    rw [SimpleGraph.Walk.isPath_copy, SimpleGraph.Walk.isPath_def, hq]
    refine List.Nodup.map_on (fun a ha b hb hab => hinj a ?_ b ?_ hab) List.nodup_range
    · have := List.mem_range.mp ha; omega
    · have := List.mem_range.mp hb; omega
  have hsupp : p.1.support = (List.range (k + 1)).map f := by
    rw [← hac.path_unique ⟨_, hpath⟩ p]
    simp [hq]
  intro x hx
  rw [hsupp] at hx ⊢
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hnd : ((List.range (k + 1)).map f).Nodup := hsupp ▸ p.2.support_nodup
  rw [List.formPerm_apply_getElem _ hnd]
  simp only [List.length_map, List.length_range] at hj ⊢
  simp only [List.getElem_map, List.getElem_range]
  rcases Nat.lt_or_ge (j + 1) (k + 1) with h | h
  · rw [Nat.mod_eq_of_lt h, hfs]
  · have hjk : j = k := by omega
    subst hjk
    rw [Nat.mod_self, hkw, hσw, hf0]

omit [Fintype V] in
/-- The cycle of the vertex list of a path sends its endpoint back to its start. -/
private theorem formPerm_support_apply_end {G : SimpleGraph V} {u w : V} (p : G.Walk u w)
    (hp : p.support.Nodup) : p.support.formPerm w = u := by
  have hlen : 0 < p.support.length := List.length_pos_of_mem p.start_mem_support
  have h1 : p.support[p.support.length - 1] = w := by
    rw [← List.getLast_eq_getElem (List.ne_nil_of_length_pos hlen)]
    exact p.getLast_support
  have h2 : p.support.formPerm p.support[p.support.length - 1] = u := by
    rw [List.formPerm_apply_getElem _ hp]
    simp only [Nat.sub_add_cancel hlen, Nat.mod_self]
    exact p.support_getElem_zero
  rwa [h1] at h2

/-- A permutation agreeing with the cycle `l.formPerm` on `l` is that cycle times a permutation
of the complement of `l`. -/
private theorem exists_formPerm_mul_ofSubtype_eq {l : List V} (σ : Perm V)
    (hσ : ∀ x ∈ l, σ x = l.formPerm x) :
    ∃ τ : Perm ↥(univ \ l.toFinset), l.formPerm * Perm.ofSubtype τ = σ := by
  set ρ := l.formPerm⁻¹ * σ with hρ
  have hρl : ∀ x ∈ l, ρ x = x := fun x hx => by
    rw [hρ, Perm.mul_apply, hσ x hx]
    exact l.formPerm.symm_apply_apply x
  have h₁ : ∀ x, ρ x ∈ univ \ l.toFinset ↔ x ∈ univ \ l.toFinset := fun x => by
    simp only [mem_sdiff, mem_univ, true_and, List.mem_toFinset]
    exact ⟨fun h hx => h (by rw [hρl x hx]; exact hx),
      fun h hx => h (by rw [← ρ.injective (hρl _ hx)]; exact hx)⟩
  refine ⟨ρ.subtypePerm h₁, ?_⟩
  rw [Perm.ofSubtype_subtypePerm h₁ fun x hx => by simpa using mt (hρl x) hx, hρ,
    mul_inv_cancel_left]

/-- A nonzero term of the Leibniz expansion of `M(Γ)` with row `u` replaced by the `w`-th unit
row comes from a permutation sending `w` to `u` and every other vertex to itself or to a
neighbour. -/
private theorem admissible_of_prod_ne_zero {Γ : WeightedGraph V} {u w : V} {σ : Perm V}
    (hσ : ∏ i, Γ.matrix.updateRow u (Pi.single w 1) (σ i) i ≠ 0) :
    σ w = u ∧ ∀ i, i ≠ w → σ i ≠ i → Γ.underlyingGraph.Adj i (σ i) := by
  have hall : ∀ i, Γ.matrix.updateRow u (Pi.single w 1) (σ i) i ≠ 0 := fun i hi =>
    hσ (Finset.prod_eq_zero (mem_univ i) hi)
  have hσw : σ w = u := by
    have h := hall (σ.symm u)
    rw [apply_symm_apply, Matrix.updateRow_self, Pi.single_apply] at h
    rw [← (by simpa using h : σ.symm u = w), apply_symm_apply]
  refine ⟨hσw, fun i hiw hfix => ⟨hfix.symm, ?_⟩⟩
  have h := hall i
  rw [Matrix.updateRow_ne fun h => hiw (σ.injective (h.trans hσw.symm))] at h
  simp only [matrix, Matrix.of_apply, hfix, ↓reduceIte, ne_eq, Nat.cast_eq_zero] at h
  rw [Γ.edgeWeight_symm]
  omega

/-- Along a path with simple edges, the entries of `M(Γ)` with row `u` replaced by the `w`-th
unit row that the cycle of the path picks out are all `1`. -/
private theorem updateRow_formPerm_apply_self {Γ : WeightedGraph V} (hs : Γ.HasSimpleEdges)
    {u w : V} (p : Γ.Path u w) {i : V} (hi : i ∈ p.1.support) :
    Γ.matrix.updateRow u (Pi.single w 1) (p.1.support.formPerm i) i = 1 := by
  set l := p.1.support
  have hnd : l.Nodup := p.2.support_nodup
  by_cases hci : l.formPerm i = u
  · have hiw : i = w :=
      l.formPerm.injective (hci.trans (formPerm_support_apply_end p.1 hnd).symm)
    rw [hci, Matrix.updateRow_self, hiw, Pi.single_eq_same]
  rw [Matrix.updateRow_ne hci]
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hi
  have hj1 : j + 1 < l.length := by
    by_contra hcon
    apply hci
    rw [List.formPerm_apply_getElem _ hnd]
    simp only [show j + 1 = l.length by omega, Nat.mod_self]
    exact p.1.support_getElem_zero
  rw [List.formPerm_apply_getElem _ hnd]
  simp only [Nat.mod_eq_of_lt hj1]
  have hadj : Γ.underlyingGraph.Adj l[j] l[j + 1] := p.1.isChain_adj_support.getElem j hj1
  simp only [matrix, Matrix.of_apply, hadj.ne.symm, ↓reduceIte]
  rw [(hs _ _ hadj.symm).2]
  rfl

/-- The matrix of the restriction of `Γ` to `S` is the corresponding submatrix of `M(Γ)`. -/
private theorem matrix_restrict (Γ : WeightedGraph V) (S : Finset V) :
    (Γ.restrict S).matrix = Γ.matrix.submatrix (↑) (↑) := by
  ext i j
  simp only [matrix, WeightedGraph.restrict, Matrix.of_apply, Matrix.submatrix_apply,
    Subtype.ext_iff]

/-- The sign of the cycle of a nonempty list without duplicates of length `L` is `-(-1)^L`. -/
private theorem sign_formPerm_of_nodup {l : List V} (hl : l.Nodup) (hne : l ≠ []) :
    (Perm.sign l.formPerm : ℤ) = -(-1) ^ l.length := by
  rcases Nat.lt_or_ge l.length 2 with h | h
  · obtain ⟨x, rfl⟩ : ∃ x, l = [x] := by
      match l, hne, h with
      | [x], _, _ => exact ⟨x, rfl⟩
      | _ :: _ :: _, _, h => simp at h
    simp
  · rw [(List.isCycle_formPerm hl h).sign, List.support_formPerm_of_nodup l hl
      (fun x hx => by simp [hx] at h), List.toFinset_card_of_nodup hl]
    push_cast
    ring

/-- For a weighted tree `Γ` with simple edges and `N` vertices, the `(u, w)` cofactor of
`M(Γ)` (the entry `adjugate M(Γ) w u`) is `-(-1)^N Δ(Γ - path(u, w))`. -/
@[mmp "lem_fa3_tree_cofactor"]
public theorem adjugate_matrix_apply_of_isTree {Γ : WeightedGraph V} (hs : Γ.HasSimpleEdges)
    (ht : Γ.IsTree) (u w : V) :
    Γ.matrix.adjugate w u = -(-1) ^ Fintype.card V * (Γ.removeSet (Γ.treePath u w)).det := by
  have ht' : Γ.underlyingGraph.IsTree := ht
  let p : Γ.Path u w := (ht'.connected.preconnected u w).some.toPath
  set l := p.1.support
  have hnd : l.Nodup := p.2.support_nodup
  set c : Perm V := l.formPerm
  set T : Finset V := univ \ l.toFinset with hT
  have hmemT : ∀ x, x ∈ T ↔ x ∉ l := fun x => by simp [hT]
  set B : Matrix V V ℤ := Γ.matrix.updateRow u (Pi.single w 1) with hB
  -- the nonzero terms of the Leibniz expansion are those of `c * τ`, `τ` a permutation of `T`
  have hterm (τ : Perm T) :
      Perm.sign (c * Perm.ofSubtype τ) • ∏ i, B ((c * Perm.ofSubtype τ) i) i =
      (Perm.sign c : ℤ) * (Perm.sign τ • ∏ i : T, Γ.matrix (τ i) i) := by
    simp only [map_mul, Perm.sign_ofSubtype, Units.smul_def, Units.val_mul, smul_eq_mul,
      mul_assoc]
    congr 2
    rw [← Finset.prod_sdiff (subset_univ l.toFinset), ← hT,
      Finset.prod_eq_one (s := l.toFinset) fun i hi => by
        have hi : i ∈ l := List.mem_toFinset.1 hi
        rw [Perm.mul_apply, Perm.ofSubtype_apply_of_not_mem τ (by simpa [hmemT] using hi)]
        exact updateRow_formPerm_apply_self hs p hi,
      mul_one, ← Finset.prod_coe_sort T]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hτi : (τ i : V) ∉ l := (hmemT _).1 (τ i).2
    rw [Perm.mul_apply, Perm.ofSubtype_apply_of_mem τ i.2, List.formPerm_apply_of_notMem hτi,
      hB, Matrix.updateRow_ne fun h => hτi (by rw [h]; exact p.1.start_mem_support)]
  rw [Matrix.adjugate_apply, Matrix.det_apply, ← hB,
    ← Finset.sum_subset (subset_univ (univ.image fun τ : Perm T => c * Perm.ofSubtype τ))
      fun σ _ hσ => by
      by_contra h
      obtain ⟨hσw, hadm⟩ := admissible_of_prod_ne_zero fun h0 => h (by rw [h0, smul_zero])
      obtain ⟨τ, rfl⟩ := exists_formPerm_mul_ofSubtype_eq σ
        (apply_eq_formPerm_of_admissible ht'.isAcyclic p σ hσw hadm)
      exact hσ (mem_image_of_mem _ (mem_univ τ)),
    Finset.sum_image fun τ₁ _ τ₂ _ h => Perm.ofSubtype_injective (mul_left_cancel h)]
  simp only [hterm]
  rw [← Finset.mul_sum, Γ.treePath_eq_support ht'.isAcyclic p, removeSet, WeightedGraph.det,
    Matrix.det_neg, ← hT, matrix_restrict, Matrix.det_apply,
    sign_formPerm_of_nodup hnd (List.ne_nil_of_mem p.1.start_mem_support)]
  have hcard : Fintype.card V = Fintype.card T + l.length := by
    rw [Fintype.card_coe, hT, ← List.toFinset_card_of_nodup hnd,
      card_sdiff_add_card_eq_card (subset_univ _), card_univ]
  rw [hcard, pow_add]
  rcases neg_one_pow_eq_or ℤ (Fintype.card T) with h | h <;> rw [h] <;> simp

end MMP.Flips.WeightedGraph

namespace MMP.Flips

open MMP.Mori

section QDiscrepancy

/-- If `C = m A` for a divisor `C` and a `ℚ`-divisor `A`, `m > 0`, then `A = (1/m) C`
coefficientwise. -/
private theorem coeff_eq_of_toQDivisor_eq_smul {Y : Scheme.{u}} {A : QDivisor Y} {m : ℕ}
    (hm : 0 < m) {C : Divisor Y} (hC : Divisor.toQDivisor C = (m : ℤ) • A)
    (Γ : Mori.PrimeDivisor Y) : (A.coeff Γ : ℝ) = 1 / (m : ℝ) * C.coeff Γ := by
  have := congrArg (fun B : QDivisor Y => ((B.coeff Γ : ℚ) : ℝ)) hC
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
    Int.cast_natCast] at this
  push_cast at this
  rw [this]
  field_simp

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- A presentation `div_X(ω) + D = ∑ r_j L_j` of `ℝ`-divisors, read coefficientwise. -/
private theorem ordForm_add_coeff_eq_sum {n : ℕ} {D : RDivisor X}
    {ω : RationalPluriForms sX n 1} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    (h : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (Γ : Mori.PrimeDivisor X) :
    (Γ.ordForm ω : ℝ) + D.coeff Γ = ∑ j, r j * (L j).coeff Γ := by
  simpa only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_sum_smul_toRDivisor] using congrArg (fun B : RDivisor X => B.coeff Γ) h

/-- A discrepancy with respect to a `ℚ`-divisor is a discrepancy computed with a one-term
presentation `div_X(ω) + D = (1/m) C`, `C` Cartier. -/
private theorem exists_presentation {n : ℕ} {D : QDivisor X} {ω : RationalPluriForms sX n 1}
    {E : ProperDivisorOver k sX} {a : ℚ} (h : IsQDiscrepancyWith sX n D ω E a) :
    ∃ (m : ℕ) (C : Divisor X) (C' : Divisor E.Y), 0 < m ∧ C.IsCartier ∧
      (∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + (QDivisor.toRDivisor D).coeff Γ =
        ∑ _i : Fin 1, (1 / (m : ℝ)) * C.coeff Γ) ∧
      (haveI := E.isLocallyNoetherian
       haveI := E.isNormal
       ∀ _i : Fin 1, ∃ hC, C.IsPullback E.f hC C') ∧
      (a : ℝ) =
        (E.toDivisorOver.ordPullback ω : ℝ) - ∑ _i : Fin 1, (1 / (m : ℝ)) * C'.coeff E.E := by
  obtain ⟨-, -, -, hq, hB, G, hG, rfl⟩ := h
  obtain ⟨m, hm, C, hC, hCc⟩ := hq.exists_pos
  obtain ⟨C', hC', hpb⟩ := hG m hm C hC hCc
  refine ⟨m, C, C', hm, hCc, fun Γ => ?_, fun _ => ⟨_, hpb⟩, ?_⟩
  · have := coeff_eq_of_toQDivisor_eq_smul hm hC Γ
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor, coeff_divisorOfForm] at this
    push_cast at this
    simp [this]
  · simp [coeff_eq_of_toQDivisor_eq_smul hm hC' E.E]

/-- **FA (1.6.2), 1.15: the discrepancy depends only on the valuation.** Let `X` be a normal
variety of dimension `n` over a perfect field and `D` a `ℚ`-divisor on `X`. If `a = a_ω(E, X, D)`
and `a' = a_{ω'}(E', X, D)` for divisors `(Y, f, E)`, `(Y', f', E')` over `X` with
`ord_E = ord_{E'}`, then `a = a'`. -/
@[mmp "lem_fa1a_discrepancy_independent_of_model"]
public theorem IsQDiscrepancyWith.eq [PerfectField k] {n : ℕ} {D : QDivisor X}
    {ω ω' : RationalPluriForms sX n 1} {E E' : ProperDivisorOver k sX} {a a' : ℚ}
    (h : IsQDiscrepancyWith sX n D ω E a) (h' : IsQDiscrepancyWith sX n D ω' E' a')
    (hE : E.valuation = E'.valuation) : a = a' := by
  obtain ⟨hX, hn, hω0, -⟩ := id h
  obtain ⟨-, -, hω0', -⟩ := id h'
  obtain ⟨m, C, C', -, hCc, hsum, hpb, ha⟩ := exists_presentation h
  obtain ⟨m', C₂, C₂', -, hCc₂, hsum₂, hpb₂, ha'⟩ := exists_presentation h'
  have := ordPullback_sub_sum_eq_of_valuation_eq hX hn hE hω0 hω0' (fun _ => hCc)
    (fun _ => hCc₂) hsum hsum₂ (fun _ => C') (fun _ => C₂') hpb hpb₂
  exact_mod_cast ha.trans (this.trans ha'.symm)

/-- **A discrepancy `a_ω(E, X, D)` is computed by any presentation.** If `a = a_ω(E, X, D)`, then
`a` is the discrepancy `a_{ω₀}(E, D)` of FA 2.5 computed with any nonzero rational form `ω₀` and
any presentation `div_X(ω₀) + D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isDiscrepancyWith_of_isQDiscrepancyWith [PerfectField k] {n : ℕ}
    {D : QDivisor X}
    {ω ω₀ : RationalPluriForms sX n 1} {E : ProperDivisorOver k sX} {a : ℚ}
    (h : IsQDiscrepancyWith sX n D ω E a) (hω₀ : ω₀ ≠ 0) {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hL : Divisor.toRDivisor (divisorOfForm ω₀) + QDivisor.toRDivisor D =
      ∑ j, r j • Divisor.toRDivisor (L j)) :
    IsDiscrepancyWith sX n (QDivisor.toRDivisor D) ω₀ r L E a := by
  obtain ⟨hX, hn, hω0, -⟩ := id h
  obtain ⟨_, C, C', -, hCc, hsum, hpb, ha⟩ := exists_presentation h
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j : Fin m =>
    MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨hX, hn, hω₀, hLc, hL, L', fun j => ⟨_, hL' j⟩,
    ha.trans (ordPullback_sub_sum_eq_of_valuation_eq hX hn rfl hω0 hω₀ (fun _ => hCc) hLc hsum
      (ordForm_add_coeff_eq_sum hL) (fun _ => C') L' hpb fun j => ⟨_, hL' j⟩)⟩

/-- The valuation `ord_E` of a divisor `(Y, f, E)` over `X` with `f` proper is a divisor of the
function field `k(X)`. -/
private theorem isDivisorOfFunctionField_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX) :
    IsDivisorOfFunctionField k sX E.valuation := by
  have := E.isIntegral
  have := E.isDominant
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (E.f ≫ sX)
  let := functionFieldMapAlgebra E.f
  have := isScalarTower_functionFieldMap sX E.f
  exact ⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E, AlgEquiv.ofBijective
    (IsScalarTower.toAlgHom k X.functionField E.Y.functionField)
    E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩

/-- **FA 1.15 and FA 2.5 give the same discrepancies.** Let `X` be a normal variety of dimension
`n` over a perfect field, `K` a canonical divisor and `D` a `ℚ`-divisor on `X` with `K + D`
`ℚ`-Cartier, and `(Y, f, E)` an exceptional divisor over `X`. If `a = a_ω(E, X, D)` for some
rational `n`-form `ω`, then `a` is the discrepancy `a(ord_E, D)` of the divisor `ord_E` of
`k(X)`. -/
@[mmp "lem_fa4_discrepancy_definitions_agree"]
public theorem IsQDiscrepancyWith.isDiscrepancy [PerfectField k] {n : ℕ} {K : Divisor X}
    {D : QDivisor X} {ω : RationalPluriForms sX n 1} {E : ProperDivisorOver k sX} {a : ℚ}
    (hK : K.IsCanonicalDivisor sX n) (hKD : (Divisor.toQDivisor K + D).IsQCartier)
    (hE : E.IsExceptional) (h : IsQDiscrepancyWith sX n D ω E a) :
    IsDiscrepancy sX n K (QDivisor.toRDivisor D) E.valuation (a : ℝ) := by
  obtain ⟨ω₀, hω₀0, hω₀⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq h.1 hK
  have hdiv : divisorOfForm ω₀ = K := DivisorWithCoeffs.ext' hω₀
  obtain ⟨m₀, hm₀, C₀, hC₀, hC₀c⟩ := hKD.exists_pos
  have hpres : Divisor.toRDivisor K + QDivisor.toRDivisor D =
      ∑ _j : Fin 1, (1 / (m₀ : ℝ)) • Divisor.toRDivisor C₀ := by
    refine DivisorWithCoeffs.ext' fun Γ => ?_
    have := coeff_eq_of_toQDivisor_eq_smul hm₀ hC₀ Γ
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toQDivisor] at this
    push_cast at this
    simp [coeff_sum_smul_toRDivisor, this]
  exact ⟨hK, ⟨1, _, _, fun _ => hC₀c, hpres⟩, ⟨isDivisorOfFunctionField_valuation E, E, rfl⟩,
    E, ω₀, 1, _, _, rfl, hdiv,
    isDiscrepancyWith_of_isQDiscrepancyWith h hω₀0 (fun _ => hC₀c) (hdiv ▸ hpres)⟩

end QDiscrepancy

section FBirationalTransform

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} [CompactSpace Y]
  [LocallyOfFiniteType sY]

/-- The coefficient of an `𝓕`-birational transform `G = φ_*(D_X) + ∑ c_i F_i` along a
`φ⁻¹`-exceptional prime divisor `F` is `c F`. -/
private theorem coeff_eq_of_isFBirationalTransform {n : ℕ} {K : Divisor X} {D_X : RDivisor X}
    {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : RDivisor Y}
    (h : IsFBirationalTransform sX sY n K D_X φ c G) {F : Mori.PrimeDivisor Y}
    (hF : RationalMap.IsInverseExceptional φ F) : G.coeff F = c F := by
  obtain ⟨-, -, -, -, -, -, Fs, hFs, -, -, rfl⟩ := h
  rw [DivisorWithCoeffs.coeff_add]
  change MMP.Mori.RationalMap.transformDivisor φ D_X F +
    (∑ F ∈ Fs, Finsupp.single F (c F)) F = c F
  rw [show MMP.Mori.RationalMap.transformDivisor φ D_X F = 0 from
      mapPrimeDivisors_apply_eq_zero_of_forall_ne hF D_X, zero_add, Finsupp.finset_sum_apply,
    Finset.sum_eq_single_of_mem F ((hFs F).mpr hF) fun b _ hb => Finsupp.single_eq_of_ne' hb]
  exact Finsupp.single_eq_same

/-- **FA 2.7, `a(F_i, D_{𝓕,Y}) = -c_i`.** Let `G = φ_*(D_X) + ∑ c_i F_i` be the
`𝓕`-birational transform of `D_X` under `φ : X ⤏ Y` (`MMP.Flips.IsFBirationalTransform`), and let
`K_Y` be a canonical divisor of `Y` with `K_Y + G` `ℝ`-Cartier. For every `φ⁻¹`-exceptional prime
divisor `F` of `Y`, the discrepancy of `ord_F` with respect to `(Y, G)` is `-c(F)`. -/
@[mmp "lem_fa2_f_birational_transform_discrepancy"]
public theorem IsFBirationalTransform.isDiscrepancy_divisorialValuation [PerfectField k] {n : ℕ}
    {K : Divisor X} {D_X : RDivisor X} {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ}
    {G : RDivisor Y} (h : IsFBirationalTransform sX sY n K D_X φ c G) {K_Y : Divisor Y}
    (hKY : K_Y.IsCanonicalDivisor sY n)
    (hKG : IsCartierCombination (Divisor.toRDivisor K_Y + G)) {F : Mori.PrimeDivisor Y}
    (hF : RationalMap.IsInverseExceptional φ F) :
    IsDiscrepancy sY n K_Y G F.divisorialValuation (-c F) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq h.2.1 hKY
  obtain rfl : divisorOfForm ω = K_Y := DivisorWithCoeffs.ext' fun Γ => by
    rw [coeff_divisorOfForm, hω]
  simpa [coeff_eq_of_isFBirationalTransform h hF] using
    MMP.Flips.isDiscrepancy_divisorialValuation (sX := sY) h.2.1 ω hω0 hKY hKG F

/-- **FA 2.23.2.** Let `G = φ_*(D_X) + ∑ c_i F_i` be an `𝓕`-birational transform of `D_X` under
`φ : X ⤏ Y` (`MMP.Flips.IsFBirationalTransform`) with `(X, D_X)` log canonical. For every
`φ⁻¹`-exceptional prime divisor `F` of `Y`, realized through `φ` by a divisor `E` over `X`, and
every value `a` of the discrepancy `a(E, D_X)`, one has `-a ≤ c(F)`. -/
@[mmp "lem_fa2_lc_source_zariski_decomposition"]
public theorem IsFBirationalTransform.neg_le_of_isLogCanonical {n : ℕ} {K : Divisor X}
    {D_X : RDivisor X} {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : RDivisor Y}
    (h : IsFBirationalTransform sX sY n K D_X φ c G) (hlc : IsLogCanonical sX n K D_X)
    {F : Mori.PrimeDivisor Y} (hF : RationalMap.IsInverseExceptional φ F)
    {E : ProperDivisorOver k sX} (hE : IsRealizedOver sX φ F E) {a : ℝ}
    (ha : IsDiscrepancy sX n K D_X E.valuation a) : -a ≤ c F := by
  obtain ⟨-, -, -, -, -, -, Fs, hFs, -, hc, -⟩ := h
  have hmin := (hc F ((hFs F).2 hF)).2 E a hE ha
  rwa [min_eq_right (by linarith [hlc.2.2.2 E.valuation ha.2.2.1 a ha])] at hmin

end FBirationalTransform

section GermResolution

open TopologicalSpace

/-- A `ℚ`-linear functional `l` with `l 1 = 1` fixes the rationals. -/
private theorem linearMap_ratCast {l : ℝ →ₗ[ℚ] ℚ} (hl : l 1 = 1) (q : ℚ) : l (q : ℝ) = q := by
  rw [show (q : ℝ) = q • (1 : ℝ) by simp [Rat.smul_def], map_smul, smul_eq_mul, hl, mul_one]

/-- A real number on which every `ℚ`-linear functional `λ` with `λ 1 = 1` takes the value `q`
is `q`. -/
private theorem eq_of_forall_linearMap (x : ℝ) (q : ℚ)
    (h : ∀ l : ℝ →ₗ[ℚ] ℚ, l 1 = 1 → l x = q) : x = q := by
  have h0 : ∀ l : ℝ →ₗ[ℚ] ℚ, l 1 = 1 → l (x - q) = 0 := fun l hl => by
    rw [map_sub, h l hl, linearMap_ratCast hl, sub_self]
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Module.Dual ℚ ℝ, l₀ 1 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff ℚ (1 : ℝ)).mp hc)
  set f₀ : ℝ →ₗ[ℚ] ℚ := (l₀ 1)⁻¹ • l₀ with hf₀
  have h1 : f₀ 1 = 1 := by simp [f₀, hl₀]
  rw [← sub_eq_zero]
  refine (Module.forall_dual_apply_eq_zero_iff ℚ (x - q)).mp fun μ => ?_
  have h2 := h0 (f₀ + μ - μ 1 • f₀) (by simp [h1])
  have h3 := h0 f₀ h1
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    h3] at h2
  linarith

/-- A rational multiple of a Cartier divisor is `ℚ`-Cartier. -/
private theorem isQCartier_smul_toQDivisor {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D : Divisor X} (hD : D.IsCartier) (q : ℚ) : (q • Divisor.toQDivisor D).IsQCartier := by
  refine ⟨q.den, by exact_mod_cast q.den_nz, q.num • D, ?_, hD.zsmul _⟩
  refine Finsupp.ext fun Γ => ?_
  change ((q.num * D Γ : ℤ) : ℚ) = (q.den : ℤ) • (q * (D Γ : ℚ))
  rw [zsmul_eq_mul, ← mul_assoc, Int.cast_natCast, mul_comm (q.den : ℚ) q, Rat.mul_den_eq_num]
  push_cast; ring

/-- The pull-back of a nonzero rational form along a birational morphism is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    {d : ℕ} (hd : topologicalKrullDim X = d) (g : Y ⟶ X) [IsIntegral Y] [IsDominant g]
    (hg : IsBirationalMorphism g) {m : ℤ} {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) :
    pullbackRationalPluriForms sX g τ ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg.functionFieldMap_bijective
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hd)
  have hpull : pullbackRationalPluriForms sX g τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

/-- A partial map representing the inverse of the rational map of `f` is a right inverse of `f`
on its domain. -/
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
    have hf : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
      ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
        (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm
    rw [hf, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- For a proper birational morphism `f : Y ⟶ X` of normal varieties, the transform of a prime
divisor `P` of `X` under `f⁻¹` is the prime divisor `E` of `Y` with `f(η_E) = η_P`. -/
private theorem transformPrimeDivisor_inverse_eq_some {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hX : IsNormalVariety k sX) (f : Y ⟶ X) [IsProper f] (hY : IsNormalVariety k (f ≫ sX))
    (hf : IsBirationalMorphism f) (P : Mori.PrimeDivisor X) (E : Mori.PrimeDivisor Y)
    (h : f E.genericPoint = P.genericPoint) :
    MMP.Mori.RationalMap.transformPrimeDivisor (MMP.Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsDominant f := hf.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have : IsSeparated (Y ↘ ⊤_ Scheme) := by
    rw [show (Y ↘ ⊤_ Scheme) = (f ≫ sX) ≫ (Spec (.of k) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  set g := MMP.Mori.RationalMap.IsBirational.inverse hf with hg_def
  have hdef : MMP.Mori.RationalMap.DefinedAt g P.genericPoint := by
    by_contra hnd
    have hcodim := MMP.Flips.RationalMap.isMorphismInCodimOne_inverse hX f hY.1 hf
    have h2 := le_closedsCodimension_iff.mp hcodim
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (MMP.Mori.RationalMap.dom g).compl.isClosed)
    have h3 : codimension (IrreducibleCloseds.closureSingleton P.genericPoint) = 1 := by
      rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
        (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
        Order.coheight_orderIso, P.coheight_genericPoint]
    rw [h3] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- If `g` is biregular at the generic point of a prime divisor `P` of `X` and `g(η_E) = η_P`,
then `g⁻¹_* P = E`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_mem {X Y : Scheme.{u}} (g : Y ⟶ X)
    (P : Mori.PrimeDivisor X) (E : Mori.PrimeDivisor Y)
    (hV : P.genericPoint ∈ biregularLocus g) (h : g E.genericPoint = P.genericPoint) :
    inverseTransformPrimeDivisor g P = some E := by
  have hPmem : P.genericPoint ∈ (P.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨P.genericPoint, hPmem, hV⟩, ?_⟩
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have h1 : inverseTransform g P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    change _ = (E.support : Set Y)
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure, inverseTransform,
      TopologicalSpace.Closeds.coe_closure]
    apply Set.Subset.antisymm
    · refine closure_minimal (fun y hy => ?_) isClosed_closure
      have hsp : g E.genericPoint ⤳ g y := by
        rw [h]
        have : g y ∈ (P.support : Set X) := hy.1
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
        exact specializes_iff_mem_closure.mpr this
      exact specializes_iff_mem_closure.mp
        (MMP.Mori.specializes_of_isIso_morphismRestrict g _ (h ▸ hV) hy.2 hsp)
    · refine closure_minimal (Set.singleton_subset_iff.mpr (subset_closure ?_)) isClosed_closure
      rw [Set.mem_preimage, h]
      exact ⟨hPmem, hV⟩
  have := E.integral
  rw [inverseTransformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- Two maps on prime divisors which agree on the support of a `ℚ`-divisor `D` have the same
linear extension on `D`, compatibly with `ℚ ⊆ ℝ`. -/
private theorem mapPrimeDivisors_toRDivisor_eq {X Y : Scheme.{u}}
    {φ ψ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)} (D : QDivisor X)
    (h : ∀ C ∈ D.support, φ C = ψ C) :
    DivisorWithCoeffs.mapPrimeDivisors φ (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (DivisorWithCoeffs.mapPrimeDivisors ψ D) := by
  have hs : ∀ (C : Mori.PrimeDivisor X) (q : ℚ),
      QDivisor.toRDivisor (Finsupp.single C q) = Finsupp.single C (q : ℝ) := fun C q =>
    Finsupp.mapRange_single (hf := map_zero _)
  have hs' : ∀ (o : Option (Mori.PrimeDivisor Y)) (q : ℚ),
      QDivisor.toRDivisor (o.elim 0 (Finsupp.single · q)) = o.elim 0 (Finsupp.single · (q : ℝ)) :=
    fun o q => by
      cases o
      · simp
      · exact Finsupp.mapRange_single (hf := map_zero _)
  classical
  revert h
  induction D using Finsupp.induction with
  | zero => intro; simp
  | single_add a b f ha hb ih =>
    intro h
    rw [Finsupp.support_single_add ha hb] at h
    rw [map_add, map_add, map_add, ih (fun C hC => h C (Finset.mem_cons_of_mem hC)), hs,
      DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single,
      h a (Finset.mem_cons_self _ _), map_add QDivisor.toRDivisor, hs']

/-- On a surface integral and locally of finite type over `k`, the closure of the generic point
of a prime divisor is one-dimensional. -/
private theorem topologicalKrullDim_closure_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 2) (Γ : Mori.PrimeDivisor Y) :
    topologicalKrullDim (closure {Γ.genericPoint} : Set Y) = 1 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY Γ.genericPoint
  rw [Γ.coheight_genericPoint, hdim] at h
  rw [show (2 : WithBot ℕ∞) = 1 + ((1 : ℕ∞) : WithBot ℕ∞) from rfl] at h
  simpa using h

/-- On a surface integral and locally of finite type over `k`, the generic point of a prime
divisor is not a closed point. -/
private theorem not_isClosed_genericPoint {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 2) (Γ : Mori.PrimeDivisor Y) :
    ¬ IsClosed ({Γ.genericPoint} : Set Y) := fun hcl => by
  have h := topologicalKrullDim_closure_genericPoint sY hdim Γ
  rw [hcl.closure_eq] at h
  have := topologicalKrullDim_zero_of_discreteTopology ({Γ.genericPoint} : Set Y)
  rw [h] at this
  exact absurd this (by decide)

section Resolution

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {P : X}
  {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [LocallyOfFiniteType (g ≫ sX)] [IsLocallyNoetherian Y]
  [IsNormal Y] [CompactSpace Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}

omit [IsLocallyNoetherian X] [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact (g ≫ sX)]
  [LocallyOfFiniteType (g ≫ sX)] [IsLocallyNoetherian Y] [CompactSpace Y] in
/-- On a resolution `g` of a surface germ `(X, P)`, a subset of `g⁻¹(P)` is not dense in `Y`:
otherwise the generic point of `X` would be `P`, making `X` a point. -/
private theorem closure_ne_univ_of_subset_preimage (hgr : IsGermResolution sX P g)
    (hg : IsBirationalMorphism g) {Z : Set Y} (hZP : Z ⊆ g.base ⁻¹' {P}) :
    closure Z ≠ Set.univ := fun h => by
  have : IsIntegral Y := hgr.isIntegral sX
  have : IsDominant g := hg.isDominant
  have hPcl : IsClosed ({P} : Set X) := hgr.isSurfaceGerm.2.2.1
  have h3 : genericPoint X = P := map_genericPoint_of_isDominant g ▸
    closure_minimal hZP (hPcl.preimage g.continuous) (h ▸ Set.mem_univ (genericPoint Y))
  have : Subsingleton X := by
    refine ⟨fun a b => ?_⟩
    have hu := (genericPoint_spec X).def
    rw [h3, hPcl.closure_eq] at hu
    exact ((hu ▸ Set.mem_univ a : a ∈ ({P} : Set X))).trans
      (hu ▸ Set.mem_univ b : b ∈ ({P} : Set X)).symm
  have := topologicalKrullDim_zero_of_discreteTopology X
  rw [hgr.isSurfaceGerm.2.1] at this
  exact absurd this (by decide)

/-- On a resolution of a surface germ `(X, P)`, a prime divisor of `Y` exceptional over `X` is
one of the exceptional curves `E_i`: it lies over a closed point, which is `P` since `g` is an
isomorphism over `X ∖ {P}`, so its support is a component of `g⁻¹(P)`. -/
private theorem exists_eq_of_isExceptionalPrimeDivisor (hgr : IsGermResolution sX P g)
    (hE : IsExceptionalCurveEnumeration g P E) (hg : IsBirationalMorphism g)
    {Γ : Mori.PrimeDivisor Y} (hΓ : IsExceptionalPrimeDivisor sX g Γ) : ∃ i, E i = Γ := by
  have : IsIntegral Y := hgr.isIntegral sX
  have hdimY : topologicalKrullDim Y = 2 := hgr.topologicalKrullDim_eq
  have hdimX : topologicalKrullDim X = 2 := hgr.isSurfaceGerm.2.1
  obtain ⟨_, _, _, hexc⟩ := hΓ
  set x := g Γ.genericPoint
  have hx : topologicalKrullDim (closure {x} : Set X) + 2 ≤ 2 := by
    unfold ProperDivisorOver.IsExceptional at hexc
    rwa [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hdimX] at hexc
  have hxcl : IsClosed ({x} : Set X) := by
    by_contra hn
    obtain ⟨c, -, hxc, hne⟩ := MMP.Mori.exists_isClosed_singleton_specializes hn
    have h1 := one_le_topologicalKrullDim_of_specializes_of_ne
      (x := (⟨x, subset_closure rfl⟩ : closure ({x} : Set X)))
      (y := ⟨c, specializes_iff_mem_closure.mp hxc⟩) ((subtype_specializes_iff _ _).mpr hxc)
      (fun h => hne (congrArg Subtype.val h))
    exact absurd ((add_le_add h1 (le_refl (2 : WithBot ℕ∞))).trans hx) (by decide)
  have hxP : x = P := by
    by_contra hne
    obtain ⟨U, hU, hiso⟩ := hgr.isIso_away
    obtain ⟨c, -, hηc, hne'⟩ := MMP.Mori.exists_isClosed_singleton_specializes
      (not_isClosed_genericPoint (g ≫ sX) hdimY Γ)
    have hgc : g c = x := by
      simpa [hxcl.closure_eq] using specializes_iff_mem_closure.mp (hηc.map g.continuous)
    have hxU : x ∈ U := by rw [← SetLike.mem_coe, hU]; exact hne
    exact hne' (hηc.antisymm (MMP.Mori.specializes_of_isIso_morphismRestrict g U
      (a := c) (b := Γ.genericPoint) (hgc ▸ hxU) hxU (by rw [hgc]))).eq
  have hsupp : (Γ.support : Set Y) = closure {Γ.genericPoint} :=
    AlgebraicGeometry.PrimeDivisor.support_eq_closure Γ
  have hsub : (Γ.support : Set Y) ⊆ g.base ⁻¹' {P} := by
    rw [hsupp]
    exact closure_minimal (by simpa using hxP) (hgr.isSurfaceGerm.2.2.1.preimage g.continuous)
  refine hE.exists_eq Γ ⟨⟨⟨hsupp ▸ isIrreducible_singleton.closure, hsub⟩,
    fun Z ⟨hZ, hZP⟩ hΓZ => ?_⟩, ⟨Γ.integral, ?_⟩⟩
  · have h := MMP.Mori.closure_singleton_eq_of_not_isClosed hdimY.le
      (not_isClosed_genericPoint (g ≫ sX) hdimY Γ) hZ.closure isClosed_closure
      (subset_closure (hΓZ (hsupp ▸ subset_closure rfl)))
      (closure_ne_univ_of_subset_preimage hgr hg hZP)
    intro z hz
    rw [hsupp, h]
    exact subset_closure hz
  · rw [MMP.Mori.topologicalKrullDim_subscheme_eq]
    change topologicalKrullDim (Γ.support : Set Y) = 1
    rw [hsupp]
    exact topologicalKrullDim_closure_genericPoint (g ≫ sX) hdimY Γ

/-- On a resolution of a surface germ `(X, P)`, the prime divisors of `Y` exceptional over `X`
are exactly the exceptional curves `E_i`: such a divisor lies over a closed point, which is `P`
since `g` is an isomorphism over `X ∖ {P}`, so its support is a component of `g⁻¹(P)`. -/
private theorem isExceptionalPrimeDivisor_iff (hgr : IsGermResolution sX P g)
    (hE : IsExceptionalCurveEnumeration g P E) (hY : IsNormalVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) (hp : IsProper g) (Γ : Mori.PrimeDivisor Y) :
    IsExceptionalPrimeDivisor sX g Γ ↔ ∃ i, E i = Γ := by
  refine ⟨exists_eq_of_isExceptionalPrimeDivisor hgr hE hg, ?_⟩
  rintro ⟨i, rfl⟩
  have hc := (hE.isGermExceptionalCurve i).1.prop
  refine ⟨hY, hg, hp, ?_⟩
  unfold ProperDivisorOver.IsExceptional
  have himg : ((ProperDivisorOver.mk ⟨Y, g, hY, hg, E i⟩ hp).center : Set X) = {P} := by
    rw [ProperDivisorOver.coe_center]
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hc.2 hy
    · rintro _ rfl
      obtain ⟨y, hy⟩ := hc.1.nonempty
      exact ⟨y, hy, hc.2 hy⟩
  rw [himg, hgr.isSurfaceGerm.2.1]
  calc _ ≤ (0 : WithBot ℕ∞) + 2 :=
        add_le_add (topologicalKrullDim_zero_of_discreteTopology ({P} : Set X)) le_rfl
    _ = 2 := zero_add _

/-- On a resolution of a surface germ, the pull-back of a nonzero rational `2`-form `ω` with
`div ω` canonical has canonical divisor of zeros and poles. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback [PerfectField k] [IsIntegral Y]
    [IsDominant g] (hgr : IsGermResolution sX P g) (hY : IsNormalVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) {ω : RationalPluriForms sX 2 1} (hω0 : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX 2) :
    (divisorOfForm (pullbackRationalPluriForms sX g ω)).IsCanonicalDivisor (g ≫ sX) 2 := by
  have := hgr.isVariety
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor_of_isSmoothScheme (g ≫ sX)
    hgr.isSmoothResolution.isSmoothScheme (n := 2) hgr.topologicalKrullDim_eq
  have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀
    (pullbackRationalPluriForms_ne_zero sX hK.topologicalKrullDim_eq g hg hω0)
  rw [one_smul] at h
  exact hK₀.of_linearlyEquivalent h

/-- On a resolution of a surface germ, the birational transform `g⁻¹_*` of `ℝ`-divisors agrees
with the inverse transform of `ℚ`-divisors: no prime divisor of `X` passes through `P`'s
generic point, and away from `P` both send a prime divisor to the one over its generic point. -/
private theorem birationalInverseTransform_toRDivisor (hgr : IsGermResolution sX P g)
    (hX : IsNormalVariety k sX) (hY : IsNormalVariety k (g ≫ sX)) (hg : IsBirationalMorphism g)
    [IsProper g] (D : QDivisor X) :
    birationalInverseTransform g hg (QDivisor.toRDivisor D) =
      QDivisor.toRDivisor (inverseTransformDivisor g D) := by
  have : IsIntegral Y := hgr.isIntegral sX
  obtain ⟨U, hU, hiso⟩ := hgr.isIso_away
  refine mapPrimeDivisors_toRDivisor_eq D fun C _ => ?_
  have hCU : C.genericPoint ∈ U := by
    rw [← SetLike.mem_coe, hU]
    exact fun hCP => not_isClosed_genericPoint sX hgr.isSurfaceGerm.2.1 C
      (hCP ▸ hgr.isSurfaceGerm.2.2.1)
  obtain ⟨u, hu⟩ : C.genericPoint ∈ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  have hgy : g ((g ⁻¹ᵁ U).ι ((inv (g ∣_ U)) u)) = C.genericPoint := by
    rw [← MMP.Mori.ι_morphismRestrict_apply, ← Scheme.Hom.comp_apply (inv (g ∣_ U)) (g ∣_ U),
      IsIso.inv_hom_id, ← hu]
    rfl
  have hco : Order.coheight ((g ⁻¹ᵁ U).ι ((inv (g ∣_ U)) u)) = 1 := by
    rw [coheight_eq_of_isOpenImmersion, coheight_eq_of_isOpenImmersion (inv (g ∣_ U)),
      ← C.coheight_genericPoint, ← hu, coheight_eq_of_isOpenImmersion]
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : Mori.PrimeDivisor Y, g Γ.genericPoint = C.genericPoint :=
    ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco,
      (congrArg g (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco)).trans hgy⟩
  rw [transformPrimeDivisor_inverse_eq_some hX g hY hg C Γ hΓ,
    inverseTransformPrimeDivisor_eq_some_of_mem g C Γ (le_biregularLocus (V := U) hiso hCU) hΓ]

/-- On a resolution of a surface germ, the pull-back `g^*L` of a Cartier divisor `L` of `X` is
numerically trivial on every exceptional curve, since `g` contracts it to a point. -/
private theorem isIntersectionNumber_pullback_zero (hgr : IsGermResolution sX P g)
    (hE : IsExceptionalCurveEnumeration g P E)
    (hX : IsNormalVariety k sX) {L : Divisor X} {L' : Divisor Y} (hL : L.IsCartier)
    (hpb : ∃ hB : ∀ Z : irreducibleComponents Y, g (componentGenericPoint Y Z) ∉ L.supp,
      L.IsPullback g hB L') (i : Fin n) :
    IsIntersectionNumber (g ≫ sX) (Divisor.toQDivisor L') (E i).idealSheaf 0 := by
  have hL' := hpb.choose_spec.isCartier hL
  obtain ⟨C, hC, hCc⟩ := (hE.isGermExceptionalCurve i).exists_properCurve hgr
  convert isIntersectionNumber_of_properCurve (k := k) (s := g ≫ sX)
    (Divisor.toQDivisor L') (QDivisor.isQCartier_toQDivisor hL') C (E i) hC using 1
  have := hgr.isVariety
  have : MMP.Mori.IsVariety k sX := hX.1
  have := C.isCurve
  have := hL.isInvertibleModule_divisorialSheaf
  have := hL'.isInvertibleModule_divisorialSheaf
  have hpt : ∃ w : X, Set.range (C.ι ≫ g) = {w} := ⟨g C.point, by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact hCc _ (C.range_ι ▸ ⟨z, rfl⟩)
    · rintro rfl
      exact ⟨genericPoint C.scheme, by simp [C.ι_genericPoint]⟩⟩
  have : IsProper ((C.ι ≫ g) ≫ sX) := by
    rw [Category.assoc]
    exact C.isProper_ι_comp
  have : MMP.Mori.IsCurve k ((C.ι ≫ g) ≫ sX) := by
    rw [Category.assoc]
    infer_instance
  rw [QDivisor.intersectionNumber_toQDivisor k (g ≫ sX) C.ι C.dim_le _ hL', Divisor.degreeOn,
    degreeOn_eq_of_iso k (g ≫ sX) C.ι _ (hpb.choose_spec.divisorialSheafIso (hBc := hL)),
    degreeOn_pullback_eq_degreeOn_comp (g ≫ sX) sX g C.ι rfl,
    degreeOn_eq_zero_of_range_eq_singleton sX (C.ι ≫ g) _ hpt]
  simp

/-- **The hard step.** Write `K_Y + g⁻¹_* B = ∑_t r_t g^*L_t + ∑_i c_i E_i` with real
coefficients, where each `g^*L_t` is Cartier and numerically trivial on the exceptional curves.
Applying a `ℚ`-linear functional `l` with `l 1 = 1` to the coefficients gives the equation of
`ℚ`-divisors `K_Y + g⁻¹_* B + ∑_i (1 - (1 + l(c_i))) E_i = ∑_t l(r_t) g^*L_t`, whose right side
is numerically trivial on every `E_i`: so `(1 + l(c_i))_i` is a log discrepancy vector. -/
private theorem isGermLogDiscrepancyVector_one_add {B : QDivisor X}
    {a : Fin n → ℚ} (ha : IsGermLogDiscrepancyVector sX P B g E a) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (g ≫ sX) 2) {m : ℕ} {r : Fin m → ℝ} {L' : Fin m → Divisor Y}
    (hL' : ∀ t, (L' t).IsCartier)
    (hL0 : ∀ t i, IsIntersectionNumber (g ≫ sX) (Divisor.toQDivisor (L' t)) (E i).idealSheaf 0)
    {c : Fin n → ℝ}
    (heq : Divisor.toRDivisor KY + QDivisor.toRDivisor (inverseTransformDivisor g B) =
      ∑ t, r t • Divisor.toRDivisor (L' t) + ∑ i, Finsupp.single (E i) (c i))
    {l : ℝ →ₗ[ℚ] ℚ} (hl : l 1 = 1) :
    IsGermLogDiscrepancyVector sX P B g E (fun i => 1 + l (c i)) := by
  classical
  obtain ⟨hB, hgr, hE, hlv⟩ := ha
  have hQ : Divisor.toQDivisor KY + inverseTransformDivisor g B +
      ∑ i, Finsupp.single (E i) (1 - (1 + l (c i))) =
      ∑ t, l (r t) • Divisor.toQDivisor (L' t) := by
    simp only [sub_add_cancel_left, Finsupp.single_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg,
      sub_eq_iff_eq_add]
    refine Finsupp.ext fun Γ => ?_
    have h := congrArg (fun D : RDivisor Y => l (D Γ)) heq
    simp only [Finsupp.add_apply, Finsupp.finset_sum_apply, map_add, map_sum,
      Finsupp.smul_apply, smul_eq_mul] at h ⊢
    have e1 : ∀ D : Divisor Y, l ((Divisor.toRDivisor D) Γ) = (Divisor.toQDivisor D) Γ :=
      fun D => by exact_mod_cast linearMap_ratCast hl (D Γ)
    have e2 : ∀ D : QDivisor Y, l ((QDivisor.toRDivisor D) Γ) = D Γ :=
      fun D => linearMap_ratCast hl (D Γ)
    have e3 : ∀ t, l (r t * (Divisor.toRDivisor (L' t)) Γ) =
        l (r t) * (Divisor.toQDivisor (L' t)) Γ := fun t => by
      change l (r t * ((L' t Γ : ℤ) : ℝ)) = l (r t) * ((L' t Γ : ℤ) : ℚ)
      rw [show r t * ((L' t Γ : ℤ) : ℝ) = ((L' t Γ : ℤ) : ℚ) • r t by
        rw [Rat.smul_def]; push_cast; ring, map_smul, smul_eq_mul, mul_comm]
    have e4 : ∀ i, l ((Finsupp.single (E i) (c i)) Γ) = (Finsupp.single (E i) (l (c i))) Γ :=
      fun i => by rw [Finsupp.single_apply, Finsupp.single_apply]; split_ifs <;> simp
    simpa only [e1, e2, e3, e4] using h
  rw [isGermLogDiscrepancyVector_iff_of_isCanonicalDivisor hKY]
  refine ⟨hB, hgr, hE, fun i => ?_⟩
  rw [hQ]
  simpa using isIntersectionNumber_sum Finset.univ (isIntersectionNumber_zero (hlv KY hKY i))
    (fun t _ => (hL0 t i).smul (l (r t)) (isQCartier_smul_toQDivisor (hL' t) _))

end Resolution

section LocalCartier

/-! ### `ℝ`-Cartier divisors near the point of a surface germ, and log discrepancies -/

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A divisor whose restriction to an open `V` is Cartier has a local equation near every point
of `V`: a local equation of `D|_V` on `W ⊆ V` is one of `D` on `W`, since the prime divisors of
`X` meeting `W` are the closures of those of `V` meeting `W`, with the same local rings. -/
private theorem exists_isLocalEquation_of_isCartier_restrictOpen {D : Divisor X} {V : X.Opens}
    (h : Divisor.IsCartier (D.restrictOpen V)) {x : X} (hx : x ∈ V) :
    ∃ W : X.Opens, x ∈ W ∧ ∃ φ : (RationalFunctions X)ˣ, D.IsLocalEquation W φ := by
  have : Nonempty V := ⟨⟨x, hx⟩⟩
  have : IsDominant V.ι := Opens.isDominant_ι (V.isOpen.dense ⟨x, hx⟩)
  obtain ⟨W, hxW, φ', hφ'⟩ := h ⟨x, hx⟩
  obtain ⟨g', hg', hφg'⟩ := MMP.Positivity.exists_ord_eq_of_units φ'
  obtain ⟨g, rfl⟩ := (functionFieldMap_bijective_of_isOpenImmersion V.ι ⊤
    ⟨⟨x, hx⟩, trivial⟩).2 g'
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (g := g)
    (fun h0 => hg' (by rw [h0, map_zero]))
  refine ⟨V.ι ''ᵁ W, ⟨⟨x, hx⟩, hxW, rfl⟩, φ, fun E hE => ?_⟩
  have hEW : E.genericPoint ∈ V.ι ''ᵁ W := (E.genericPoint_mem_iff _).2 hE
  obtain ⟨y, hyW, hy⟩ := hEW
  obtain ⟨E₀, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff V.ι E).2 ⟨y, hy⟩
  have hgp : V.ι E₀.genericPoint = V.ι y :=
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm.trans hy.symm
  have hE₀ : (E₀.support ∩ (W : Set V)).Nonempty := by
    rw [← PrimeDivisor.genericPoint_mem_iff]
    have : E₀.genericPoint = y := V.ι.isOpenEmbedding.injective hgp
    change E₀.genericPoint ∈ W
    rw [this]
    exact hyW
  have h1 := hφ' E₀ hE₀
  rw [DivisorWithCoeffs.coeff_restrictOpen] at h1
  rw [h1, hφg', hφ, MMP.Positivity.ord_functionFieldMap_of_isIso V.ι E₀ _
    (OpenWeilRestriction.genericPoint_primeDivisorMap _ _).symm]

/-- The smooth locus of a scheme locally of finite type over a field is smooth. -/
private theorem isSmoothScheme_smoothLocus_ι {k : Type u} [Field k] {Z : Scheme.{u}}
    (s : Z ⟶ Spec (.of k)) [LocallyOfFiniteType s] : IsSmoothScheme ((smoothLocus s).ι ≫ s) := by
  rw [isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
    ← Scheme.Hom.preimage_smoothLocus_eq, smoothLocus_eq_smoothLocus, Scheme.Opens.ι_preimage_self]

/-- On a surface germ `(X, P)`, a divisor that is Cartier on a neighbourhood `V` of `P` is
Cartier: away from `P` the surface is smooth, and there every divisor is Cartier. -/
private theorem isCartier_of_isCartier_restrictOpen {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {P : X} (hP : IsSurfaceGerm sX P)
    {D : Divisor X} {V : X.Opens} (hPV : P ∈ V) (h : Divisor.IsCartier (D.restrictOpen V)) :
    D.IsCartier := by
  intro x
  by_cases hx : x ∈ V
  · exact exists_isLocalEquation_of_isCartier_restrictOpen h hx
  · exact exists_isLocalEquation_of_isCartier_restrictOpen
      (MMP.Fourfold.isCartier_of_isSmoothScheme (isSmoothScheme_smoothLocus_ι sX) _)
      (hP.2.2.2 x fun e => hx (e ▸ hPV))

omit [IsIntegral X] in
/-- A finite `ℝ`-combination of Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_finsetSum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (M : ι → Divisor X) (hM : ∀ i ∈ s, (M i).IsCartier) :
    IsCartierCombination (∑ i ∈ s, c i • Divisor.toRDivisor (M i)) := by
  refine ⟨s.card, fun j => c (s.equivFin.symm j), fun j => M (s.equivFin.symm j),
    fun j => hM _ (s.equivFin.symm j).2, ?_⟩
  simp only [← toRDivisor_eq_mapCoeffs]
  rw [← Finset.sum_coe_sort s]
  exact (Equiv.sum_comp s.equivFin.symm (fun i : s => c i • Divisor.toRDivisor (M i))).symm

/-- On a surface germ `(X, P)`, an `ℝ`-divisor that is `ℝ`-Cartier on a neighbourhood `V` of `P`
is `ℝ`-Cartier. If `D|_V = ∑ r_j L_j`, extend each `L_j` to `X` by taking closures of its
components; the extensions are Cartier (`isCartier_of_isCartier_restrictOpen`), and the
remainder of `D` is supported on prime divisors not meeting `V`, each Cartier for the same
reason. -/
private theorem isCartierCombination_of_restrictOpen {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] {P : X} (hP : IsSurfaceGerm sX P)
    {D : RDivisor X} {V : X.Opens} (hPV : P ∈ V)
    (h : IsCartierCombination (D.restrictOpen V)) : IsCartierCombination D := by
  classical
  obtain ⟨m, r, L, hL, hD⟩ := h
  set ι := OpenWeilRestriction.primeDivisorMap V.ι with hι
  have hinj : Function.Injective ι := OpenWeilRestriction.primeDivisorMap_injective V.ι
  let L' : Fin m → Divisor X := fun j => Finsupp.mapDomain ι (L j)
  have hL' : ∀ j W, L' j (ι W) = L j W := fun j W => Finsupp.mapDomain_apply_of_injective hinj _ _
  let R : RDivisor X := D - ∑ j, r j • Divisor.toRDivisor (L' j)
  have hDW : ∀ W, D (ι W) = ∑ j, r j * (L j W : ℝ) := fun W => by
    have := congrArg (fun F : RDivisor V => F W) hD
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at this
    exact this
  have hRW : ∀ W, R (ι W) = 0 := fun W => by
    simp only [R, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
      hDW]
    refine sub_eq_zero.mpr (Finset.sum_congr rfl fun j _ => ?_)
    change _ = r j * (Divisor.toRDivisor (L' j)).coeff (ι W)
    rw [Divisor.coeff_toRDivisor]
    exact congrArg _ (by exact_mod_cast (hL' j W).symm)
  have hR0 : ∀ C ∈ R.support, ∀ W, ι W ≠ C := fun C hC W hW =>
    (Finsupp.mem_support_iff.mp hC) (hW ▸ hRW W)
  have hRsum : R = ∑ C ∈ R.support, R C • Divisor.toRDivisor (Finsupp.single C 1) := by
    conv_lhs => rw [← Finsupp.sum_single R]
    refine Finset.sum_congr rfl fun C _ => ?_
    ext Γ
    change (Finsupp.single C (R C)) Γ = R C * (Divisor.toRDivisor (Finsupp.single C 1)).coeff Γ
    rw [Divisor.coeff_toRDivisor]
    by_cases h : C = Γ <;> simp [DivisorWithCoeffs.coeff, h]
  have hDsum : D = ∑ i ∈ (Finset.univ : Finset (Fin m)).disjSum R.support,
      (Sum.elim r R i) • Divisor.toRDivisor
        (Sum.elim L' (fun C => Finsupp.single C (1 : ℤ)) i) := by
    rw [Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← hRsum]
    exact (add_sub_cancel _ _).symm
  rw [hDsum]
  refine isCartierCombination_finsetSum _ _ _ fun i hi => ?_
  refine isCartier_of_isCartier_restrictOpen hP hPV ?_
  rcases i with j | C
  · convert hL j using 1
    ext W
    exact hL' j W
  · have hC : C ∈ R.support := Finset.inr_mem_disjSum.mp hi
    have h0 : DivisorWithCoeffs.restrictOpen V (Finsupp.single C (1 : ℤ) : Divisor X) = 0 := by
      refine Finsupp.ext fun W => ?_
      change (Finsupp.single C (1 : ℤ)) (ι W) = 0
      simp [(hR0 C hC W).symm]
    simp only [Sum.elim_inr]
    rw [h0]
    exact Divisor.isCartier_zero

open scoped WithZero in
/-- An FA discrepancy `a(F, D_X)` (`MMP.Flips.IsDiscrepancy`) is computed on a divisor
`(Y, f, E)` over `X` with `ord_E = F`, and `1 + a` is the log discrepancy of that divisor in the
sense of `MMP.Intersection.IsLogDiscrepancy`: both are `1 + ord_E(f^*ω) - ∑ r_j coeff_E(f^*L_j)`
for a presentation `div(ω) + D_X = ∑ r_j L_j`. -/
private theorem IsDiscrepancy.exists_isLogDiscrepancy {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X}
    {D_X : RDivisor X} {F : Valuation X.functionField ℤᵐ⁰} {a : ℝ}
    (h : IsDiscrepancy sX n K D_X F a) :
    ∃ E : ProperDivisorOver k sX, E.valuation = F ∧
      MMP.Intersection.IsLogDiscrepancy sX n D_X E.toDivisorOver (1 + a) := by
  obtain ⟨hK, -, -, E, ω, m, r, L, hEF, rfl, hX, -, hω0, hLc, hL, L', hLpb, rfl⟩ := h
  refine ⟨E, hEF, hX, E.isProper, ω, hω0, ⟨_, hK, fun Γ => coeff_divisorOfForm ω Γ⟩, m, r, L,
    L', hLc, fun Γ => ?_, hLpb, by ring⟩
  have := congrArg (fun G : RDivisor X => G.coeff Γ) hL
  simp only [coeff_sum_smul_toRDivisor] at this
  rw [← this, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm]

end LocalCartier

/-- Restriction to an open commutes with the sum `K + B` of a divisor and a `ℚ`-divisor. -/
private theorem restrictOpen_toRDivisor_add {X : Scheme.{u}} (K : Divisor X) (B : QDivisor X)
    (U : X.Opens) :
    (Divisor.toRDivisor K + QDivisor.toRDivisor B).restrictOpen U =
      Divisor.toRDivisor (K.restrictOpen U) + (QDivisor.toRDivisor B).restrictOpen U :=
  Finsupp.ext fun W => by
    change (Divisor.toRDivisor K + QDivisor.toRDivisor B).coeff _ =
      (Divisor.toRDivisor (K.restrictOpen U)).coeff W + _
    rw [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, Divisor.coeff_toRDivisor]
    rfl

/-- Restriction to an open commutes with viewing a `ℚ`-divisor as an `ℝ`-divisor. -/
private theorem toRDivisor_restrictOpen {X : Scheme.{u}} (B : QDivisor X) (U : X.Opens) :
    QDivisor.toRDivisor (B.restrictOpen U) = (QDivisor.toRDivisor B).restrictOpen U :=
  Finsupp.ext fun W => by
    change (QDivisor.toRDivisor (B.restrictOpen U)).coeff W = _
    rw [QDivisor.coeff_toRDivisor]
    rfl

/-- Viewing `K + B` as an `ℝ`-divisor is additive. -/
private theorem toRDivisor_toQDivisor_add {X : Scheme.{u}} (K : Divisor X) (B : QDivisor X) :
    QDivisor.toRDivisor (Divisor.toQDivisor K + B) =
      Divisor.toRDivisor K + QDivisor.toRDivisor B :=
  Finsupp.ext fun Γ => by
    change (QDivisor.toRDivisor (Divisor.toQDivisor K + B)).coeff Γ =
      (Divisor.toRDivisor K + QDivisor.toRDivisor B).coeff Γ
    rw [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor]
    push_cast
    rfl

variable {k : Type u} [Field k] [PerfectField k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
  {P : X} {B : QDivisor X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y]
  [IsNormal Y] {n : ℕ} {E : Fin n → Mori.PrimeDivisor Y}

omit [CompactSpace X] [QuasiCompact (g ≫ sX)] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- If `(X, B)` is log canonical on an open `U`, the discrepancy `q` of `(X, B)` along a divisor
`Γ` over `X` whose generic point maps into `U` is at least `-1`: it is the discrepancy of the
restricted divisor over `U`, computed with a rational `2`-form whose divisor is `K_X|_U`. -/
private theorem neg_one_le_of_isDiscrepancy_of_isLogCanonical {U : X.Opens} [Nonempty U]
    [IsDominant U.ι] [CompactSpace U] {K : Divisor X}
    (hlogU : IsLogVariety k (U.ι ≫ sX) (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)))
    (hKU : Divisor.IsCanonicalDivisor (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K))
    (hKBU : IsCartierCombination (Divisor.toRDivisor (DivisorWithCoeffs.restrictOpen U K) +
      DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)))
    (hlcU : ∀ F, HasNonemptyCenter k (U.ι ≫ sX) F → ∀ a : ℝ,
      IsDiscrepancy (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)) F a → -1 ≤ a)
    (hpair : IsPairWith sX 2 K B) (hY : IsNormalVariety k (g ≫ sX))
    (hg : IsBirationalMorphism g) [IsProper g] {Γ : Mori.PrimeDivisor Y}
    (hΓ : g Γ.genericPoint ∈ U) {q : ℚ}
    (hq : Mori.IsDiscrepancy sX 2 K B ⟨Y, g, hY, hg, Γ⟩ q) : -1 ≤ (q : ℝ) := by
  classical
  let D : DivisorOver k sX := ⟨Y, g, hY, hg, Γ⟩
  have hcen : ((D.center : Set X) ∩ U).Nonempty :=
    ⟨_, by rw [DivisorOver.center_eq_closure_genericPoint]; exact subset_closure rfl, hΓ⟩
  obtain ⟨hYU, hfU, E', hE', -, hiff⟩ :=
    DivisorOver.exists_restrict_isDiscrepancy_iff hpair D U hcen
  have hlogU' := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ((hiff q).mp hq)
    (inferInstance : IsProper (g ∣_ U))
  have hXU : IsNormalVariety k (U.ι ≫ sX) := hlogU.isNormalVariety
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXU hKU
  have hωK : divisorOfForm ω = K.restrictOpen U := DivisorWithCoeffs.ext' fun Γ => by
    rw [coeff_divisorOfForm, hω]
  have : Nonempty (g ⁻¹ᵁ U) := ⟨⟨Γ.genericPoint, hΓ⟩⟩
  have := hYU.isIntegral
  have := hYU.isNormal
  have := hYU.isLocallyNoetherian
  have : LocallyOfFiniteType ((g ∣_ U) ≫ U.ι ≫ sX) := hYU.1.toLocallyOfFiniteType
  have : IsDominant (g ∣_ U) := hfU.isDominant
  have : CompactSpace (g ⁻¹ᵁ U) := QuasiCompact.compactSpace_of_compactSpace (g ∣_ U)
  have hKD : IsCartierCombination
      (Divisor.toRDivisor (divisorOfForm ω) + (QDivisor.toRDivisor B).restrictOpen U) :=
    hωK ▸ hKBU
  obtain ⟨G, hG, -⟩ := existsUnique_isRCartierPullback (g ∣_ U) hKD
  have hdU := isDiscrepancy_ordPullback_sub_coeff_pullback hXU ω hω0 (hωK ▸ hKU) hKD (g ∣_ U)
    hYU hfU hG E'
  rw [hωK] at hdU
  obtain ⟨E₂, hE₂, hlog₂⟩ := hdU.exists_isLogDiscrepancy
  have h2 := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₂
    (toRDivisor_restrictOpen B U ▸ hlogU') hE₂
  have h3 := hlcU _ hdU.2.2.1 _ hdU
  linarith

/-- **The log discrepancy vector consists of log discrepancies** (FA 3.0.2–3.0.3). If `a` is the
log discrepancy vector of `(X, P; B)` on a resolution `g` with exceptional curves `E_1, …, E_n`,
and `K_X + B` is `ℝ`-Cartier near `P` for a canonical divisor `K_X` (on some open neighbourhood
`U` of `P`, `(K_X + B)|_U` is `ℝ`-Cartier), then `a_j` is the log discrepancy `a_ℓ(E_j, B)` of the
divisor `(Y, g, E_j)` over `X`, for every `j`. -/
@[mmp "lem_fa3_log_discrepancy_vector_agrees"]
public theorem IsGermLogDiscrepancyVector.isLogDiscrepancy {a : Fin n → ℚ}
    (ha : IsGermLogDiscrepancyVector sX P B g E a) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2)
    (hKB : HoldsOnGerm {P} fun U : X.Opens =>
      IsCartierCombination
        (DivisorWithCoeffs.restrictOpen U (Divisor.toRDivisor K + QDivisor.toRDivisor B)))
    (j : Fin n) (hY : IsNormalVariety k (g ≫ sX)) (hg : IsBirationalMorphism g)
    (hp : IsProper g) :
    IsLogDiscrepancy sX 2 K (QDivisor.toRDivisor B)
      (ProperDivisorOver.mk ⟨Y, g, hY, hg, E j⟩ hp).valuation (a j) := by
  obtain ⟨(U : X.Opens), hPU, hKBU⟩ := hKB
  have hKB := isCartierCombination_of_restrictOpen ha.1.1 (hPU rfl) hKBU
  classical
  obtain ⟨hB, hgr, hE, -⟩ := id ha
  have hX : IsNormalVariety k sX := hB.1.1
  have : IsIntegral Y := hgr.isIntegral sX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (g ≫ sX)
  have : LocallyOfFiniteType (g ≫ sX) := hY.1.toLocallyOfFiniteType
  have : IsDominant g := hg.isDominant
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain rfl : divisorOfForm ω = K := DivisorWithCoeffs.ext' fun Γ => by
    rw [coeff_divisorOfForm, hω]
  obtain ⟨Ex, a', G, hEx, ⟨m, r, L, L', hLc, -, hLpb, rfl⟩, hdisc, heq⟩ :=
    discrepancy_formula hX (QDivisor.toRDivisor B) ω hω0 hK hKB g hY hg
  have hEx' : ∀ Γ, Γ ∈ Ex ↔ ∃ i, E i = Γ := fun Γ =>
    (hEx Γ).trans (isExceptionalPrimeDivisor_iff hgr hE hY hg hp Γ)
  have hsum : ∑ Γ ∈ Ex, Finsupp.single Γ (a' Γ) = ∑ i, Finsupp.single (E i) (a' (E i)) :=
    (Finset.sum_bij (fun i _ => E i) (fun i _ => (hEx' _).mpr ⟨i, rfl⟩)
      (fun i _ i' _ h => hE.injective h)
      (fun Γ hΓ => by obtain ⟨i, rfl⟩ := (hEx' Γ).mp hΓ; exact ⟨i, Finset.mem_univ _, rfl⟩)
      (fun i _ => rfl)).symm
  rw [birationalInverseTransform_toRDivisor hgr hX hY hg B, hsum] at heq
  have key (l : ℝ →ₗ[ℚ] ℚ) (hl : l 1 = 1) : l (a' (E j)) = a j - 1 := by
    obtain ⟨_, -, huniq⟩ := existsUnique_isGermLogDiscrepancyVector hB hgr hE
    have := congrFun ((huniq _ ha).trans (huniq _ (isGermLogDiscrepancyVector_one_add ha
      (isCanonicalDivisor_divisorOfForm_pullback hgr hY hg hω0 hK)
      (fun t => (hLpb t).choose_spec.isCartier (hLc t))
      (fun t => isIntersectionNumber_pullback_zero hgr hE hX (hLc t) (hLpb t)) heq hl)).symm) j
    linarith
  refine ⟨a' (E j), hdisc (E j) ((hEx' _).mpr ⟨j, rfl⟩), ?_⟩
  rw [eq_of_forall_linearMap (a' (E j)) (a j - 1) key]
  push_cast
  ring

/-- The source of a resolution of a surface germ is a normal variety over `k`. -/
private lemma isNormalVariety_of_isGermResolution {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsNormal Y] {P : X} {g : Y ⟶ X} [QuasiCompact (g ≫ sX)]
    (hg : IsGermResolution sX P g) : IsNormalVariety k (g ≫ sX) := by
  have : IsProper g := hg.isSmoothResolution.isProper
  have : IsIntegral Y := hg.isIntegral
  have : IsSeparated sX := hg.isSurfaceGerm.1.1.toIsSeparated
  have : LocallyOfFiniteType sX := hg.isSurfaceGerm.1.1.toLocallyOfFiniteType
  exact ⟨(isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    inferInstance⟩

/-- **Log canonical germs have nonnegative log discrepancy vectors** (FA 3.0.3). If `(X, B)` is
log canonical near `P` (on some open neighbourhood `U` of `P`, `(U, B|_U)` is log canonical with
canonical divisor `K_X|_U`) and `a` is the log discrepancy vector of `(X, P; B)` on a resolution
`g` of `(X, P)` with exceptional curves `E_1, …, E_n`, then `0 ≤ a_j` for every `j`. -/
@[mmp "lem_fa3_lc_implies_log_discrepancies_nonneg"]
public theorem IsGermLogDiscrepancyVector.nonneg_of_isLogCanonical {a : Fin n → ℚ}
    (ha : IsGermLogDiscrepancyVector sX P B g E a) {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX 2)
    (hlc : HoldsOnGerm {P} fun U : X.Opens => ∀ [Nonempty U],
      haveI : CompactSpace U := isCompact_iff_compactSpace.mp
        (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
      IsLogCanonical (U.ι ≫ sX) 2 (DivisorWithCoeffs.restrictOpen U K)
        (DivisorWithCoeffs.restrictOpen U (QDivisor.toRDivisor B)))
    (j : Fin n) : 0 ≤ a j := by
  classical
  obtain ⟨(U : X.Opens), hPU, hlcU⟩ := hlc
  have hPU : P ∈ U := hPU rfl
  have : Nonempty U := ⟨⟨P, hPU⟩⟩
  have : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨P, hPU⟩)
  have : CompactSpace U := isCompact_iff_compactSpace.mp
    (@NoetherianSpace.isCompact _ _ (haveI : IsNoetherian X := {}; inferInstance) _)
  obtain ⟨hlogU, hKU, hKBU, hlcU⟩ := hlcU
  obtain ⟨hB, hgr, hE, -⟩ := id ha
  have hX : IsNormalVariety k sX := hB.1.1
  have hY := isNormalVariety_of_isGermResolution hgr
  have hg := hgr.isSmoothResolution.isBirationalMorphism
  have hp := hgr.isSmoothResolution.isProper
  obtain ⟨a', hd, haj⟩ := ha.isLogDiscrepancy hK ⟨U, Set.singleton_subset_iff.mpr hPU,
    (restrictOpen_toRDivisor_add K B U ▸ hKBU : IsCartierCombination
      (DivisorWithCoeffs.restrictOpen U (Divisor.toRDivisor K + QDivisor.toRDivisor B)))⟩
    j hY hg hp
  have hpair : IsPairWith sX 2 K B := ⟨hX, hK, QDivisor.isQCartier_of_isCartierCombination
    ((toRDivisor_toQDivisor_add K B).symm ▸ hd.2.1)⟩
  let D : DivisorOver k sX := ⟨Y, g, hY, hg, E j⟩
  obtain ⟨q, hq⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair.isPair hK D
  obtain ⟨E₁, hE₁, hlog₁⟩ := hd.exists_isLogDiscrepancy
  have hlogD := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hq hp
  have h1 : 1 + a' = 1 + (q : ℝ) :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hlog₁ hlogD hE₁
  have hgP : g (E j).genericPoint = P := (hE.isGermExceptionalCurve j).1.prop.2 <| by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have := neg_one_le_of_isDiscrepancy_of_isLogCanonical hlogU hKU hKBU hlcU hpair hY hg
    (hgP ▸ hPU : g (E j).genericPoint ∈ U) hq
  have : ((a j : ℚ) : ℝ) = 1 + q := by rw [haj, h1]
  exact_mod_cast (by linarith : (0 : ℝ) ≤ a j)

end GermResolution

section CodimensionTwo

open TopologicalSpace IsLocalRing

/-- If `R → S` is a surjection of regular local rings with `dim S < dim R`, its kernel is not
contained in `𝔪_R²`: otherwise lifts of generators of `𝔪_S` generate `𝔪_R` by Nakayama, so
`dim R = μ(𝔪_R) ≤ μ(𝔪_S) = dim S`. -/
private theorem not_ker_le_sq {R S : Type*} [CommRing R] [CommRing S] [IsRegularLocalRing R]
    [IsRegularLocalRing S] (f : R →+* S) (hf : Function.Surjective f)
    (hdim : ringKrullDim S < ringKrullDim R) : ¬ RingHom.ker f ≤ maximalIdeal R ^ 2 := by
  intro hker
  have : IsLocalHom f := .of_surjective f hf
  have hmem (x : R) : x ∈ maximalIdeal R ↔ f x ∈ maximalIdeal S := by
    simp [mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]
  obtain ⟨s, hs, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal S)).exists_span_set_encard_eq_spanFinrank
  have hsfin : s.Finite := Set.finite_of_encard_eq_coe hs
  set g := Function.surjInv hf
  set t := g '' s
  have hst : ∀ y ∈ s, y ∈ maximalIdeal S := fun y hy => hspan ▸ Submodule.subset_span hy
  have ht : Ideal.span t = maximalIdeal R := by
    refine le_antisymm (Ideal.span_le.2 ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact (hmem _).2 (by rw [Function.surjInv_eq hf]; exact hst y hy)
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (I := maximalIdeal R) (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) ?_
      intro x hx
      have hfx : f x ∈ Ideal.map f (Ideal.span t) := by
        rw [Ideal.map_span, Set.image_image]
        simp only [g, Function.surjInv_eq hf, Set.image_id']
        have := (hmem x).1 hx
        rw [← hspan] at this
        exact this
      obtain ⟨a, ha, hfa⟩ := (Ideal.mem_map_iff_of_surjective f hf).1 hfx
      have hxa : x - a ∈ maximalIdeal R • maximalIdeal R := by
        rw [Ideal.smul_eq_mul, ← pow_two]
        exact hker (by simp [RingHom.mem_ker, hfa])
      have : x = a + (x - a) := by ring
      rw [this]
      exact Submodule.add_mem_sup ha hxa
  have hle : (maximalIdeal R).spanFinrank ≤ (maximalIdeal S).spanFinrank := by
    rw [← ht]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (hsfin.image g)).trans ?_
    refine (Set.ncard_image_le hsfin).trans ?_
    rw [Set.ncard, hs]
    simp
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := S)
  have : ringKrullDim R ≤ ringKrullDim S := by
    rw [← h1, ← h2]
    exact_mod_cast hle
  exact hdim.not_ge this

/-- A prime divisor whose ideal at `η_W` lies in `𝔪_W` but not in `𝔪_W²` has multiplicity `1`
along `W`. -/
private theorem multiplicityAlong_eq_one {X : Scheme.{u}} (Q : Mori.PrimeDivisor X)
    (W : IrreducibleCloseds X)
    (h1 : Q.idealSheaf.stalkIdeal W.isIrreducible.genericPoint ≤
      maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint))
    (h2 : ¬ Q.idealSheaf.stalkIdeal W.isIrreducible.genericPoint ≤
      maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint) ^ 2) :
    Q.multiplicityAlong W = 1 := by
  unfold Mori.PrimeDivisor.multiplicityAlong
  refine le_antisymm (iSup₂_le fun s hs => ?_) (le_iSup₂_of_le 1 (by simpa using h1) (by simp))
  by_contra hlt
  push Not at hlt
  have : 2 ≤ s := by exact_mod_cast (ENat.add_one_le_iff (by simp)).2 hlt
  exact h2 (hs.trans (Ideal.pow_le_pow_right this))

/-- A prime divisor not passing through `η_W` has multiplicity `0` along `W`. -/
private theorem multiplicityAlong_eq_zero {X : Scheme.{u}} (Q : Mori.PrimeDivisor X)
    (W : IrreducibleCloseds X) (h : W.isIrreducible.genericPoint ∉ Q.support) :
    Q.multiplicityAlong W = 0 := by
  unfold Mori.PrimeDivisor.multiplicityAlong
  rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _ h]
  refine le_antisymm (iSup₂_le fun s hs => ?_) bot_le
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · simp
  · exact absurd (top_le_iff.1 (hs.trans (Ideal.pow_le_self hs0.ne')))
      (maximalIdeal.isMaximal _).ne_top

/-- Below any nontrivial specialization `x ⤳ c` on a scheme locally of finite type over a field
sits an immediate specialization of `x`: take `w` with `x ⤳ w ⤳ c`, `w ≠ x`, of maximal residue
transcendence degree. -/
private theorem exists_isImmediateSpecialization_specializes {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {x c : X} (hxc : x ⤳ c)
    (hne : c ≠ x) : ∃ w, IsImmediateSpecialization x w ∧ w ⤳ c := by
  classical
  let m : X → ℕ := fun y => natTrdegResidueField k X f x - natTrdegResidueField k X f y
  obtain ⟨w, ⟨hxw, hwc, hwx⟩, hwmin⟩ := (measure m).wf.has_min {y | x ⤳ y ∧ y ⤳ c ∧ y ≠ x}
    ⟨c, hxc, specializes_rfl, hne⟩
  refine ⟨w, ⟨hxw, hwx.symm, fun z hxz hzw => ?_⟩, hwc⟩
  by_contra hz
  push Not at hz
  have h1 := natTrdegResidueField_lt_of_specializes k X f hzw hz.2
  have h2 := natTrdegResidueField_lt_of_specializes k X f hxz hz.1.symm
  exact hwmin z ⟨hxz, hzw.trans hwc, hz.1⟩ (show m z < m w by simp only [m]; omega)

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- **A general codimension-two subvariety of a component.** Let `X` be a normal variety of
dimension `≥ 2`, `D` a `ℚ`-divisor on `X` and `P` a component of `D`. Then there is an irreducible
closed subset `W ⊆ P` of codimension `2` in `X` with `𝒪_{X,η_W}` regular, along which `P` has
multiplicity `1` and every other component of `D` has multiplicity `0`; in particular the
multiplicity `∑_Γ D_Γ mult_W(Γ)` of `D` along `W` is the coefficient `D_P`. -/
@[mmp "lem_fa4_general_codim_two_in_component"]
public theorem exists_codimension_eq_two_multiplicityAlong_eq (hX : IsNormalVariety k sX)
    (hdim : 2 ≤ topologicalKrullDim X) (D : QDivisor X) {P : Mori.PrimeDivisor X}
    (hP : P ∈ D.support) :
    ∃ W : IrreducibleCloseds X, (W : Set X) ⊆ P.support ∧ codimension W = 2 ∧
      IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) ∧
      P.multiplicityAlong W = 1 ∧ ∀ Γ ∈ D.support, Γ ≠ P → Γ.multiplicityAlong W = 0 := by
  classical
  have hvar := hX.1
  have : LocallyOfFiniteType sX := hvar.toLocallyOfFiniteType
  set η : X := P.genericPoint
  have hηcoh : Order.coheight η = 1 := P.coheight_genericPoint
  have hηdim : ringKrullDim (X.presheaf.stalk η) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hηcoh]; rfl
  -- the regular locus of `X`
  have hRX : IsOpen (regularLocus X) := MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType sX
  have hηX : η ∈ regularLocus X := by
    have := P.isDiscreteValuationRing_localRing
    change IsRegularLocalRing (X.presheaf.stalk P.genericPoint)
    infer_instance
  -- the closed subscheme `P`
  set I := P.idealSheaf
  haveI : IsIntegral I.subscheme := P.integral
  set ι := I.subschemeι
  have hRZ : IsOpen (regularLocus I.subscheme) :=
    MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType (ι ≫ sX)
  have hηZ : genericPoint I.subscheme ∈ regularLocus I.subscheme :=
    MMP.Flips.isRegularLocalRing_of_isField (Field.toIsField _)
  have hιη : ι (genericPoint I.subscheme) = η := rfl
  -- the other components of `D` miss `η`
  have hother : ∀ Γ : Mori.PrimeDivisor X, Γ ≠ P → η ∉ Γ.support := by
    intro Γ hΓ hmem
    rw [Γ.support_eq_closure, ← specializes_iff_mem_closure] at hmem
    have hne : Γ.genericPoint ≠ η := fun h => hΓ (PrimeDivisor.genericPoint_injective h)
    have hlt := krullDimOfRing_stalk_lt_of_specialization k X sX hmem hne
    rw [hηdim, ringKrullDim_stalk_eq_coheight, Γ.coheight_genericPoint] at hlt
    exact lt_irrefl _ hlt
  -- the bad set
  set B : Set X := (regularLocus X)ᶜ ∪ ι '' (regularLocus I.subscheme)ᶜ ∪
    ⋃ Γ ∈ D.support.erase P, Γ.support with hB
  have hBc : IsClosed B := by
    refine (hRX.isClosed_compl.union ?_).union ?_
    · exact ι.isClosedEmbedding.isClosedMap _ hRZ.isClosed_compl
    · exact (Finset.finite_toSet _).isClosed_biUnion fun Γ _ => Γ.idealSheaf.support.isClosed
  have hηB : η ∉ B := by
    simp only [hB, Set.mem_union, Set.mem_compl_iff, Set.mem_image, Set.mem_iUnion,
      Finset.mem_erase, not_or, not_exists, not_and]
    refine ⟨⟨fun h => h hηX, fun z hz hzη => hz ?_⟩, fun Γ hΓ => hother Γ hΓ.1⟩
    rwa [show z = genericPoint I.subscheme from ι.isClosedEmbedding.injective hzη]
  have hηP : η ∈ P.support := by
    rw [P.support_eq_closure]; exact subset_closure rfl
  -- a closed point of `P ∖ B`
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  obtain ⟨c, ⟨hcP, hcB⟩, hcl⟩ := nonempty_inter_closedPoints (Z := (P.support : Set X) \ B)
    ⟨η, hηP, hηB⟩ ((I.support.isClosed.isLocallyClosed).inter hBc.isOpen_compl.isLocallyClosed)
  have hcl' : IsClosed ({c} : Set X) := hcl
  have hηc : η ⤳ c := by
    rw [specializes_iff_mem_closure, ← P.support_eq_closure]; exact hcP
  have hcη : c ≠ η := by
    intro hc
    rw [hc] at hcl'
    have h1 := topologicalKrullDimAt_eq_krullDimOfRing_stalk k X sX η hcl'
    rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX, hηdim] at h1
    rw [h1] at hdim
    exact absurd hdim (by decide)
  obtain ⟨w, himm, hwc⟩ := exists_isImmediateSpecialization_specializes sX hηc hcη
  have hwB : w ∉ B := fun h => hcB (hwc.mem_closed hBc h)
  have hwP : w ∈ P.support := himm.1.mem_closed I.support.isClosed hηP
  have hwdim : ringKrullDim (X.presheaf.stalk w) = 2 := by
    rw [krullDimOfRing_stalk_eq_add_one_of_isImmediateSpecialization k X sX η w himm
      (Or.inl inferInstance), hηdim]
    rfl
  -- the point of the subscheme over `w`
  obtain ⟨z, rfl⟩ : w ∈ Set.range ι := by rw [I.range_subschemeι]; exact hwP
  have himmZ : IsImmediateSpecialization (genericPoint I.subscheme) z := by
    refine ⟨(genericPoint_spec I.subscheme).specializes trivial,
      fun h => himm.2.1 (by rw [← hιη, h]), fun z' h1 h2 => ?_⟩
    rcases himm.2.2 (ι z') (h1.map ι.continuous) (h2.map ι.continuous) with h | h
    · exact Or.inl (ι.isClosedEmbedding.injective h)
    · exact Or.inr (ι.isClosedEmbedding.injective h)
  have hzdim : ringKrullDim (I.subscheme.presheaf.stalk z) = 1 := by
    rw [krullDimOfRing_stalk_eq_add_one_of_isImmediateSpecialization k I.subscheme (ι ≫ sX)
      _ z himmZ (Or.inl inferInstance), ringKrullDim_eq_zero_of_isField (Field.toIsField _)]
    rfl
  have hwX : IsRegularLocalRing (X.presheaf.stalk (ι z)) := by
    by_contra h; exact hwB (Or.inl (Or.inl h))
  have hzZ : IsRegularLocalRing (I.subscheme.presheaf.stalk z) := by
    by_contra h; exact hwB (Or.inl (Or.inr ⟨z, h, rfl⟩))
  have hsq : ¬ I.stalkIdeal (ι z) ≤ maximalIdeal (X.presheaf.stalk (ι z)) ^ 2 := by
    rw [← I.ker_stalkMap_subschemeι z]
    exact not_ker_le_sq _ (ι.stalkMap_surjective z) (by rw [hzdim, hwdim]; decide)
  -- the irreducible closed subset
  set W := IrreducibleCloseds.closureSingleton (ι z)
  have hgp : W.isIrreducible.genericPoint = ι z := by
    have h1 := W.isIrreducible.isGenericPoint_genericPoint_closure
    rw [W.isClosed.closure_eq] at h1
    exact h1.eq (isGenericPoint_closure (x := ι z))
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · exact (I.support.isClosed.closure_subset_iff).2 (Set.singleton_subset_iff.2 hwP)
  · rw [MMP.Flips.codimension_eq_coheight_genericPoint, hgp]
    rw [ringKrullDim_stalk_eq_coheight] at hwdim
    exact WithBot.coe_injective hwdim
  · rw [hgp]; exact hwX
  · refine multiplicityAlong_eq_one P W ?_ ?_
    · rw [hgp]; exact I.stalkIdeal_le_maximalIdeal_of_mem_support hwP
    · rw [hgp]; exact hsq
  · intro Γ hΓ hΓP
    refine multiplicityAlong_eq_zero Γ W ?_
    rw [hgp]
    intro h
    exact hwB (Or.inr (Set.mem_biUnion (Finset.mem_erase.2 ⟨hΓP, hΓ⟩) h))

end CodimensionTwo

end MMP.Flips

namespace MMP.Flips.NormalizationComponents

open MMP.Mori

section NormalizedSections

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Key

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- On the first exterior power, `ιMulti` is linear in its single argument. -/
private theorem ιMulti_one_add_smul (a b : R) (x y : M) :
    exteriorPower.ιMulti R 1 (fun _ : Fin 1 => a • x + b • y) =
      a • exteriorPower.ιMulti R 1 (fun _ => x) + b • exteriorPower.ιMulti R 1 (fun _ => y) := by
  have h1 := (exteriorPower.ιMulti R 1 (M := M)).map_update_add (fun _ => x) 0 (a • x) (b • y)
  have h2 := (exteriorPower.ιMulti R 1 (M := M)).map_update_smul (fun _ => x) 0 a x
  have h3 := (exteriorPower.ιMulti R 1 (M := M)).map_update_smul (fun _ => x) 0 b y
  have e : ∀ v : M, Function.update (fun _ : Fin 1 => x) 0 v = fun _ => v := fun v => by
    funext i; fin_cases i; simp
  simp only [e] at h1 h2 h3
  rw [h1, h2, h3]

end Key

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- A nonzero rational function of order `≥ 0` along `P` lies in `𝒪_{X,P}`. -/
private theorem mem_range_of_ord_nonneg (P : Mori.PrimeDivisor X) {f : X.functionField}
    (hf : f ≠ 0)
    (h : 0 ≤ X.ord f P.genericPoint) :
    f ∈ (algebraMap P.localRing X.functionField).range := by
  rw [← P.divisorialValuation_le_one_iff, P.divisorialValuation_eq_exp_neg_ord hf,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

/-- A nonzero element of `𝒪_{X,P}` has order `≥ 0` along `P`. -/
private theorem ord_nonneg_of_mem_range (P : Mori.PrimeDivisor X) {f : X.functionField}
    (hf : f ≠ 0)
    (h : f ∈ (algebraMap P.localRing X.functionField).range) :
    0 ≤ X.ord f P.genericPoint := by
  rw [← P.divisorialValuation_le_one_iff, P.divisorialValuation_eq_exp_neg_ord hf,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  omega

/-- The order of vanishing of `1` along a prime divisor is `0`. -/
private theorem ord_one (P : Mori.PrimeDivisor X) :
    X.ord (1 : X.functionField) P.genericPoint = 0 := by
  simpa using P.ord_algebraMap_of_isUnit (isUnit_one (M := P.localRing))

/-- The order of vanishing of `f ^ n` along a prime divisor is `n` times that of `f`. -/
private theorem ord_pow (P : Mori.PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) (n : ℕ) :
    X.ord (f ^ n) P.genericPoint = n * X.ord f P.genericPoint := by
  induction n with
  | zero => simpa using ord_one P
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hf) hf, ih]
    push_cast; ring

/-- The order of vanishing of `f⁻¹` along a prime divisor is minus that of `f`. -/
private theorem ord_inv (P : Mori.PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    X.ord f⁻¹ P.genericPoint = -X.ord f P.genericPoint := by
  have := Scheme.ord_mul (x := P.genericPoint) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one] at this
  omega

/-- For two local parameters `z, z'` at `P`, `(dz'/z')^m - (dz/z)^m` vanishes or has a pole of
order `< m` along `P`. -/
private theorem dlogPow_sub_dlogPow (P : Mori.PrimeDivisor X) {z z' : X.functionField}
    (hz : X.ord z P.genericPoint = 1) (hz' : X.ord z' P.genericPoint = 1) {m : ℕ} (hm : 0 < m) :
    dlogPow sX z' m - dlogPow sX z m = 0 ∨
      1 - (m : ℤ) ≤ P.ordForm (dlogPow sX z' m - dlogPow sX z m) := by
  classical
  let _ := stalkAlgebra sX P.genericPoint
  let _ := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX P.genericPoint
  by_cases hgen : ∃ σ : ⋀[P.localRing]^1 Ω[P.localRing⁄k], Submodule.span P.localRing {σ} = ⊤ ∧
      topFormsMap k P.localRing X.functionField 1 σ ≠ 0
  swap
  · right
    have : P.ordForm (dlogPow sX z' m - dlogPow sX z m) = 0 := by
      unfold PrimeDivisor.ordForm ordAt
      rw [dif_neg hgen]
    omega
  obtain ⟨σ, hσ, h0⟩ := hgen
  set β := topFormsMap k P.localRing X.functionField 1 σ with hβ
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hz0' : z' ≠ 0 := fun h => by simp [h] at hz'
  have hD : ∀ a : P.localRing, ∃ r : P.localRing, exteriorPower.ιMulti X.functionField 1
      (fun _ =>
        KaehlerDifferential.D k X.functionField (algebraMap P.localRing X.functionField a)) =
      algebraMap P.localRing X.functionField r • β := by
    intro a
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top
      (x := exteriorPower.ιMulti P.localRing 1 (fun _ => KaehlerDifferential.D k P.localRing a)))
    refine ⟨r, ?_⟩
    rw [algebraMap_smul, hβ, ← map_smul, hr, topFormsMap_ιMulti]
    simp only [KaehlerDifferential.map_D]
  set u := z' * z⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hz0' (inv_ne_zero hz0)
  have hzu : z' = u * z := by simp [u, hz0]
  have hordu : X.ord u P.genericPoint = 0 := by
    rw [hu, Scheme.ord_mul hz0' (inv_ne_zero hz0), ord_inv P hz0]; omega
  obtain ⟨az, haz⟩ := mem_range_of_ord_nonneg P hz0 (by omega)
  obtain ⟨au, hau⟩ := mem_range_of_ord_nonneg P hu0 (by omega)
  obtain ⟨av, hav⟩ := mem_range_of_ord_nonneg P (inv_ne_zero hu0) (by rw [ord_inv P hu0]; omega)
  obtain ⟨cz, hcz⟩ := hD az
  obtain ⟨cu, hcu⟩ := hD au
  rw [haz] at hcz
  rw [hau] at hcu
  set α := z⁻¹ * algebraMap P.localRing X.functionField cz with hα
  set δ := u⁻¹ * algebraMap P.localRing X.functionField cu with hδ
  have hωz : z⁻¹ • exteriorPower.ιMulti X.functionField 1
      (fun _ => KaehlerDifferential.D k X.functionField z) = α • β := by
    rw [hcz, smul_smul]
  have hωz' : z'⁻¹ • exteriorPower.ιMulti X.functionField 1
      (fun _ => KaehlerDifferential.D k X.functionField z') = (α + δ) • β := by
    rw [hzu, Derivation.leibniz, ιMulti_one_add_smul, hcz, hcu, smul_smul, smul_smul, ← add_smul,
      smul_smul]
    congr 1
    rw [hα, hδ]
    field_simp
  have hbo := ZTensorPower.basis_ofNat (topFormsBasis P.localRing hσ h0) m
  rw [topFormsBasis_apply] at hbo
  have hτ : ∀ (w a : X.functionField), w⁻¹ • exteriorPower.ιMulti X.functionField 1
      (fun _ => KaehlerDifferential.D k X.functionField w) = a • β →
      dlogPow sX w m = a ^ m • ZTensorPower.basis (topFormsBasis P.localRing hσ h0) m () := by
    intro w a h
    unfold dlogPow
    dsimp only
    rw [h]
    erw [hbo]
    exact tprod_const_smul _ _
  set F := (α + δ) ^ m - α ^ m with hF
  have hdiff : dlogPow sX z' m - dlogPow sX z m =
      F • ZTensorPower.basis (topFormsBasis P.localRing hσ h0) m () := by
    rw [hτ z' _ hωz', hτ z _ hωz, hF]
    exact (sub_smul _ _ _).symm
  by_cases hF0 : F = 0
  · left
    rw [hdiff, hF0, zero_smul]
    rfl
  right
  rw [P.ordForm_eq _ hσ h0, hdiff]
  erw [formCoeff_smul]
  simp only [formCoeff, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]
  -- `z^(m-1) F` is regular along `P`.
  set S := (algebraMap P.localRing X.functionField).range
  have hzS : z ∈ S := ⟨az, haz⟩
  have hzαS : z * α ∈ S := ⟨cz, by rw [hα, ← mul_assoc, mul_inv_cancel₀ hz0, one_mul]⟩
  have hδS : δ ∈ S := by
    rw [hδ, ← hav]
    exact S.mul_mem ⟨av, rfl⟩ ⟨cu, rfl⟩
  have hgeom := (Commute.all (α + δ) α).geom_sum₂_mul m
  rw [add_sub_cancel_left] at hgeom
  have hmem : z ^ (m - 1) * F ∈ S := by
    rw [hF, ← hgeom, mul_comm _ δ, ← mul_assoc, mul_comm (z ^ (m - 1)) δ, mul_assoc]
    refine S.mul_mem hδS ?_
    rw [Finset.mul_sum]
    refine S.sum_mem fun i hi => ?_
    have hi' : i + (m - 1 - i) = m - 1 := by
      have := Finset.mem_range.mp hi
      omega
    obtain ⟨j, hj⟩ : ∃ j, m - 1 - i = j := ⟨_, rfl⟩
    rw [hj] at hi' ⊢
    have : z ^ (m - 1) * ((α + δ) ^ i * α ^ j) =
        (z * α + z * δ) ^ i * (z * α) ^ j := by
      rw [← mul_add, mul_pow, mul_pow, ← hi', pow_add]
      ring
    rw [this]
    exact S.mul_mem (S.pow_mem (S.add_mem hzαS (S.mul_mem hzS hδS)) _) (S.pow_mem hzαS _)
  have hne : z ^ (m - 1) * F ≠ 0 := mul_ne_zero (pow_ne_zero _ hz0) hF0
  have h1 := ord_nonneg_of_mem_range P hne hmem
  rw [Scheme.ord_mul (pow_ne_zero _ hz0) hF0, ord_pow P hz0, hz] at h1
  push_cast [Nat.cast_sub (show 1 ≤ m from hm)] at h1
  omega

/-- `τ` vanishes or has order `≥ b` along `P`. -/
private def IsSmall (P : Mori.PrimeDivisor X) (b : ℚ) {d : ℕ} {n : ℤ}
    (τ : RationalPluriForms sX d n) : Prop :=
  τ = 0 ∨ b ≤ (P.ordForm τ : ℚ)

section IsSmall

variable {P : Mori.PrimeDivisor X} {b : ℚ} {d : ℕ} {n : ℤ}

private theorem IsSmall.add {τ τ' : RationalPluriForms sX d n} (h : IsSmall P b τ)
    (h' : IsSmall P b τ') : IsSmall P b (τ + τ') := by
  rcases h with h | h
  · rw [h, zero_add]; exact h'
  rcases h' with h' | h'
  · rw [h', add_zero]; exact Or.inr h
  by_cases h0 : τ + τ' = 0
  · exact Or.inl h0
  exact Or.inr ((le_min h h').trans (by exact_mod_cast P.min_ordForm_le_ordForm_add h0))

private theorem IsSmall.neg {τ : RationalPluriForms sX d n} (h : IsSmall P b τ) :
    IsSmall P b (-τ) := by
  rcases h with h | h
  · rw [h, neg_zero]; exact Or.inl rfl
  · exact Or.inr (by rwa [PrimeDivisor.ordForm_neg])

private theorem IsSmall.sub {τ τ' : RationalPluriForms sX d n} (h : IsSmall P b τ)
    (h' : IsSmall P b τ') : IsSmall P b (τ - τ') := by
  rw [sub_eq_add_neg]; exact h.add h'.neg

private theorem IsSmall.smul (c : k) {τ : RationalPluriForms sX d n} (h : IsSmall P b τ) :
    IsSmall P b (c • τ) := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]; exact Or.inl rfl
  rcases h with h | h
  · rw [h, smul_zero]; exact Or.inl rfl
  · exact Or.inr (by rwa [MMP.Fourfold.ordForm_const_smul P hc])

end IsSmall

/-- The defining condition of leading coefficients and of normalized sections is stable under
affine combinations: if `τⱼ - cⱼ (dzⱼ/zⱼ)^m` vanishes or has order `≥ b` along `P` for local
parameters `zⱼ` and `b ≤ 1 - m`, then so does `τ - c' (dz₃/z₃)^m` for
`τ = c(τ₁ - τ₂) + τ₃` and `c' = c(c₁ - c₂) + c₃`. -/
private theorem isSmall_affineCombination (P : Mori.PrimeDivisor X) {m : ℕ} (hm : 0 < m)
    {b : ℚ} (hb : b ≤ 1 - (m : ℚ)) (c c₁ c₂ c₃ : k) {τ₁ τ₂ τ₃ : RationalPluriForms sX 1 m}
    {z₁ z₂ z₃ : X.functionField} (hz₁ : X.ord z₁ P.genericPoint = 1)
    (hz₂ : X.ord z₂ P.genericPoint = 1) (hz₃ : X.ord z₃ P.genericPoint = 1)
    (h₁ : IsSmall P b (τ₁ - c₁ • dlogPow sX z₁ m)) (h₂ : IsSmall P b (τ₂ - c₂ • dlogPow sX z₂ m))
    (h₃ : IsSmall P b (τ₃ - c₃ • dlogPow sX z₃ m)) :
    IsSmall P b (c • (τ₁ - τ₂) + τ₃ - (c * (c₁ - c₂) + c₃) • dlogPow sX z₃ m) := by
  have hd : ∀ {w w' : X.functionField}, X.ord w P.genericPoint = 1 →
      X.ord w' P.genericPoint = 1 → IsSmall P b (dlogPow sX w' m - dlogPow sX w m) := by
    intro w w' hw hw'
    exact (dlogPow_sub_dlogPow P hw hw' hm).imp_right fun h => hb.trans (by exact_mod_cast h)
  have e : c • (τ₁ - τ₂) + τ₃ - (c * (c₁ - c₂) + c₃) • dlogPow sX z₃ m =
      c • ((τ₁ - c₁ • dlogPow sX z₁ m) - (τ₂ - c₂ • dlogPow sX z₂ m)) +
        (τ₃ - c₃ • dlogPow sX z₃ m) + (c * c₁) • (dlogPow sX z₁ m - dlogPow sX z₃ m) -
        (c * c₂) • (dlogPow sX z₂ m - dlogPow sX z₃ m) := by
    module
  rw [e]
  exact ((((h₁.sub h₂).smul c).add h₃).add ((hd hz₃ hz₁).smul _)).sub ((hd hz₃ hz₂).smul _)

/-- The global pluricanonical sections are closed under `c • (τ₁ - τ₂) + τ₃`. -/
private theorem pluricanonicalSections_affineCombination {d : ℕ} {n : ℤ} {G : Divisor X}
    (c : k) {τ₁ τ₂ τ₃ : RationalPluriForms sX d n}
    (h₁ : τ₁ ∈ pluricanonicalSections sX d n G ⊤) (h₂ : τ₂ ∈ pluricanonicalSections sX d n G ⊤)
    (h₃ : τ₃ ∈ pluricanonicalSections sX d n G ⊤) :
    c • (τ₁ - τ₂) + τ₃ ∈ pluricanonicalSections sX d n G ⊤ := by
  have hs : ∀ τ ∈ pluricanonicalSections sX d n G ⊤,
      c • τ ∈ pluricanonicalSections sX d n G ⊤ := by
    intro τ hτ
    rw [mem_pluricanonicalSections] at hτ ⊢
    refine ⟨fun h => by rw [hτ.1 h, smul_zero], fun Γ hΓ hne => ?_⟩
    have hc : c ≠ 0 := by rintro rfl; exact hne (zero_smul _ _)
    have hτ0 : τ ≠ 0 := by rintro rfl; exact hne (smul_zero _)
    rw [MMP.Fourfold.ordForm_const_smul Γ hc]
    exact hτ.2 Γ hΓ hτ0
  exact add_mem (hs _ (sub_mem h₁ h₂)) h₃

/-- A tensor power `τ^{⊗j}` of a form on a line is unique. -/
private theorem isTensorPowerOf_unique {K L : Type*} [Field K] [AddCommGroup L] [Module K L]
    {a n : ℤ} {τ : ZTensorPower K L a} {j : ℕ} {σ σ' : ZTensorPower K L n}
    (h : IsTensorPowerOf τ j σ) (h' : IsTensorPowerOf τ j σ') : σ = σ' := by
  obtain ⟨hn, b, hb⟩ := h
  obtain ⟨-, b', hb'⟩ := h'
  have hc : b' () = b.repr (b' ()) () • b () := by
    conv_lhs => rw [← b.sum_repr (b' ())]
    simp
  have hc0 : b.repr (b' ()) () ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hc
    exact b'.ne_zero () hc
  rw [hb, hb', ZTensorPower.basis_repr_of_eq_smul hc, ZTensorPower.basis_apply_of_eq_smul hc,
    smul_smul]
  congr 1
  rw [hn, zpow_mul, zpow_natCast, mul_pow, inv_pow, mul_comm, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ (zpow_ne_zero _ hc0)), one_mul]

section Normalized

variable {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
  {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
  (N : NormalizationComponents sC hC)

/-- `IsSmall P b τ` for an integer bound `b`: `τ` vanishes or has order `≥ b` along `P`. -/
private theorem isSmall_int_iff {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] (P : Mori.PrimeDivisor X) {d : ℕ} {n : ℤ} (b : ℤ)
    (τ : RationalPluriForms sX d n) : IsSmall P (b : ℚ) τ ↔ τ = 0 ∨ b ≤ P.ordForm τ := by
  unfold IsSmall
  exact_mod_cast Iff.rfl

/-- Leading coefficients along `P` are compatible with the affine combination
`c • (τ₁ - τ₂) + τ₃`. -/
private theorem isLeadingCoeff_affineCombination {m : ℕ} (hm : 0 < m) (i : N.ι)
    (P : Mori.PrimeDivisor (N.X i)) (c c₁ c₂ c₃ : k)
    {τ₁ τ₂ τ₃ : RationalPluriForms (N.n i ≫ sC) 1 m} (h₁ : N.IsLeadingCoeff i P τ₁ c₁)
    (h₂ : N.IsLeadingCoeff i P τ₂ c₂) (h₃ : N.IsLeadingCoeff i P τ₃ c₃) :
    N.IsLeadingCoeff i P (c • (τ₁ - τ₂) + τ₃) (c * (c₁ - c₂) + c₃) := by
  obtain ⟨z₁, hz₁, h₁⟩ := h₁
  obtain ⟨z₂, hz₂, h₂⟩ := h₂
  obtain ⟨z₃, hz₃, h₃⟩ := h₃
  refine ⟨z₃, hz₃, ?_⟩
  have key := isSmall_affineCombination P hm (b := ((1 - (m : ℤ) : ℤ) : ℚ))
    (by push_cast; exact le_rfl) c c₁ c₂ c₃ hz₁ hz₂ hz₃ ((isSmall_int_iff P _ _).2 h₁)
    ((isSmall_int_iff P _ _).2 h₂) ((isSmall_int_iff P _ _).2 h₃)
  exact (isSmall_int_iff P _ _).1 key

end Normalized

/-- **Normalized sections form an affine subspace** (FA 12.2.9). On an slc curve `(C, Δ)` over
`k` with normalization components `N`, the set of normalized sections
(`IsNormalizedSlcSection`) of `𝒪(m(K_C + Δ))` is empty or a `k`-affine subspace: it is the
set of points of a (possibly empty) `k`-affine subspace of the space of families of rational
`m`-canonical forms on the components `Cᵢ`. -/
@[mmp "lem_fa12a_normalized_sections_affine_subspace_curve"]
public theorem exists_affineSubspace_eq_setOf_isNormalizedSlcSection
    {k : Type u} [Field k] {C : Scheme.{u}} {sC : C ⟶ Spec (.of k)}
    {hC : ∀ U : C.Opens, IsCompact (U : Set C) → (irreducibleComponents U).Finite}
    (N : NormalizationComponents sC hC) (ε : EllipticNormalizationDatum k)
    (Δ : QWeilDivisor C) (m : ℕ) :
    letI : ∀ i, Module k (RationalPluriForms (N.n i ≫ sC) 1 m) := fun i =>
      Module.compHom _ (@algebraMap k (N.X i).functionField _ _ (functionFieldAlgebra (N.n i ≫ sC)))
    ∃ A : AffineSubspace k (∀ i : N.ι, RationalPluriForms (N.n i ≫ sC) 1 m),
      (A : Set (∀ i : N.ι, RationalPluriForms (N.n i ≫ sC) 1 m)) =
        {s | N.IsNormalizedSlcSection ε Δ m s} := by
  refine ⟨⟨{s | N.IsNormalizedSlcSection ε Δ m s}, ?_⟩, rfl⟩
  intro c p₁ p₂ p₃ h₁ h₂ h₃
  change N.IsNormalizedSlcSection ε Δ m (fun i => c • (p₁ i - p₂ i) + p₃ i)
  obtain ⟨hslc, hm, hint, ⟨hpole₃, hlead₃⟩, hnorm₃⟩ := h₃
  obtain ⟨-, -, -, ⟨hpole₁, hlead₁⟩, hnorm₁⟩ := h₁
  obtain ⟨-, -, -, ⟨hpole₂, hlead₂⟩, hnorm₂⟩ := h₂
  have hpole : ∀ {p : ∀ i : N.ι, RationalPluriForms (N.n i ≫ sC) 1 m},
      (∀ i (P : Mori.PrimeDivisor (N.X i)), p i ≠ 0 →
        0 ≤ ((P.ordForm (p i) : ℤ) : ℚ) + m * N.componentBoundaryCoeff Δ i P) →
      ∀ i P, IsSmall P (-(m * N.componentBoundaryCoeff Δ i P)) (p i) := by
    intro p hp i P
    by_cases h0 : p i = 0
    · exact Or.inl h0
    · exact Or.inr (by linarith [hp i P h0])
  refine ⟨hslc, hm, hint, ⟨fun i P hne => ?_, fun i j P P' he hd hne => ?_⟩, fun i => ?_⟩
  · have key := ((((hpole hpole₁ i P).sub (hpole hpole₂ i P)).smul c).add (hpole hpole₃ i P))
    rcases key with h | h
    · exact absurd h hne
    · linarith
  · obtain ⟨c₁, hl₁, hl₁'⟩ := hlead₁ i j P P' he hd hne
    obtain ⟨c₂, hl₂, hl₂'⟩ := hlead₂ i j P P' he hd hne
    obtain ⟨c₃, hl₃, hl₃'⟩ := hlead₃ i j P P' he hd hne
    refine ⟨c * (c₁ - c₂) + c₃, isLeadingCoeff_affineCombination N hm i P c c₁ c₂ c₃ hl₁ hl₂ hl₃,
      ?_⟩
    rw [show (-1 : k) ^ m * (c * (c₁ - c₂) + c₃) =
      c * ((-1) ^ m * c₁ - (-1) ^ m * c₂) + (-1) ^ m * c₃ by ring]
    exact isLeadingCoeff_affineCombination N hm j P' c _ _ _ hl₁' hl₂' hl₃'
  · obtain ⟨Δ₁, G₁, hΔ₁, hn₁⟩ := hnorm₁ i
    obtain ⟨Δ₂, G₂, hΔ₂, hn₂⟩ := hnorm₂ i
    obtain ⟨Δ₃, G₃, hΔ₃, hn₃⟩ := hnorm₃ i
    have e₁ : Δ₁ = Δ₃ := DivisorWithCoeffs.ext' fun P => (hΔ₁.2 P).trans (hΔ₃.2 P).symm
    have e₂ : Δ₂ = Δ₃ := DivisorWithCoeffs.ext' fun P => (hΔ₂.2 P).trans (hΔ₃.2 P).symm
    have g₁ : G₁ = G₃ := Divisor.toQDivisor_injective
      (by rw [hn₁.toQDivisor_eq, hn₃.toQDivisor_eq, e₁])
    have g₂ : G₂ = G₃ := Divisor.toQDivisor_injective
      (by rw [hn₂.toQDivisor_eq, hn₃.toQDivisor_eq, e₂])
    rw [e₁, g₁] at hn₁
    rw [e₂, g₂] at hn₂
    refine ⟨Δ₃, G₃, hΔ₃, { hn₃ with
      mem := pluricanonicalSections_affineCombination c hn₁.mem hn₂.mem hn₃.mem
      elliptic := ?_
      vanishes := ?_ }⟩
    · intro hp hg hΔ h12
      have e : p₁ i = p₂ i :=
        isTensorPowerOf_unique (hn₁.elliptic hp hg hΔ h12) (hn₂.elliptic hp hg hΔ h12)
      have : c • (p₁ i - p₂ i) + p₃ i = p₃ i := by rw [e, sub_self, smul_zero, zero_add]
      beta_reduce
      rw [this]
      exact hn₃.elliptic hp hg hΔ h12
    · intro hnot P hP
      obtain ⟨z₁, hz₁, hv₁⟩ := hn₁.vanishes hnot P hP
      obtain ⟨z₂, hz₂, hv₂⟩ := hn₂.vanishes hnot P hP
      obtain ⟨z₃, hz₃, hv₃⟩ := hn₃.vanishes hnot P hP
      refine ⟨z₃, hz₃, ?_⟩
      have hG : (m : ℚ) ≤ (G₃.coeff P : ℚ) := by
        have := congrArg (fun D => DivisorWithCoeffs.coeff D P) hn₃.toQDivisor_eq
        simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
        rw [this]
        push_cast
        nlinarith
      have hv : ∀ {τ : RationalPluriForms (N.n i ≫ sC) 1 m} {z : (N.X i).functionField},
          (τ - dlogPow (N.n i ≫ sC) z m = 0 ∨
            1 ≤ P.ordForm (τ - dlogPow (N.n i ≫ sC) z m) + G₃.coeff P) →
          IsSmall P ((1 - G₃.coeff P : ℤ) : ℚ) (τ - (1 : k) • dlogPow (N.n i ≫ sC) z m) := by
        intro τ z h
        rw [one_smul, isSmall_int_iff]
        exact h.imp_right fun h => by omega
      have key := isSmall_affineCombination P hm (by push_cast; linarith) c 1 1 1 hz₁ hz₂ hz₃
        (hv hv₁) (hv hv₂) (hv hv₃)
      rw [show c * (1 - 1) + 1 = (1 : k) by ring, one_smul, isSmall_int_iff] at key
      beta_reduce
      exact key.imp_right fun h => by omega

end NormalizedSections

end MMP.Flips.NormalizationComponents
