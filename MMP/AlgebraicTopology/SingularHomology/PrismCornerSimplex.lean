module

public import MMP.AlgebraicTopology.SingularHomology.ChartSimplexLocalHomology

/-!
# The corner simplex of a prism

Let `Δ = [v₀, …, vₙ]` and `Δ' = [w₀, …, w_{n'}]` be affine simplices of real vector spaces `H`
and `H'`. The *corner simplex* of the prism `Δ × Δ'` is the affine simplex of `H × H'` with
vertices `(v_{min(j, n)}, w_{j - n})`, `j = 0, …, n + n'`: the simplex of the shuffle
triangulation along the lattice path through the corner `(n, 0)`.

If `p` has barycentric coordinates `s` in `Δ`, `p'` has barycentric coordinates `s'` in `Δ'`
and `s_n + s'_0 > 1`, then `(p, p')` lies in the interior of the corner simplex, with
barycentric coordinates `s₀, …, s_{n-1}, s_n + s'_0 - 1, s'_1, …, s'_{n'}`. If `Δ` and `Δ'` are
positively oriented for bases `b`, `b'`, the corner simplex is positively oriented for the
product basis: its edge matrix is block triangular with diagonal blocks the edge matrices of
`Δ` and `Δ'`.

## Main definitions

* `MMP.ThomClass.cornerVertices`: the vertices of the corner simplex.

## Main results

* `MMP.ThomClass.isOrientedSimplexAroundZero_cornerVertices`: the corner simplex
  is an oriented simplex around `(p, p')` for the product orientation.
* `MMP.ThomClass.exists_isOrientedSimplexAroundZero_barycentric`: small oriented
  simplices around a point with prescribed barycentric coordinates.
-/

@[expose] public noncomputable section

open Set Topology Filter

namespace MMP

namespace ThomClass

section Corner

variable {H H' : Type*} [AddCommGroup H] [Module ℝ H] [AddCommGroup H'] [Module ℝ H']
  {n n' : ℕ}

/-- The vertices `(v_{min(j, n)}, w_{j - n})` of the corner simplex of the prism `Δ × Δ'`. -/
def cornerVertices (v : Fin (n + 1) → H) (w : Fin (n' + 1) → H') :
    Fin (n + n' + 1) → H × H' :=
  fun j ↦ (v ⟨min j n, by omega⟩, w ⟨j - n, by omega⟩)

/-- For `i < n`, the `i`-th vertex of the corner simplex is `(vᵢ, w₀)`. -/
lemma cornerVertices_castAdd (v : Fin (n + 1) → H) (w : Fin (n' + 1) → H') (i : Fin n) :
    cornerVertices v w (Fin.castAdd (n' + 1) i) = (v i.castSucc, w 0) := by
  simp only [cornerVertices, Prod.mk.injEq]
  constructor <;> congr 1 <;> ext <;> simp <;> omega

/-- For `k ≤ n'`, the `(n + k)`-th vertex of the corner simplex is `(vₙ, w_k)`. -/
lemma cornerVertices_natAdd (v : Fin (n + 1) → H) (w : Fin (n' + 1) → H') (k : Fin (n' + 1)) :
    cornerVertices v w (Fin.natAdd n k) = (v (Fin.last n), w k) := by
  simp only [cornerVertices, Prod.mk.injEq]
  constructor <;> congr 1 <;> ext <;> simp

/-- The barycentric coordinates `s₀, …, s_{n-1}, s_n + s'_0 - 1, s'_1, …, s'_{n'}` of
`(p, p')` in the corner simplex. -/
def cornerCoords (s : Fin (n + 1) → ℝ) (s' : Fin (n' + 1) → ℝ) : Fin (n + n' + 1) → ℝ :=
  fun j ↦ if h : (j : ℕ) < n then s ⟨j, by omega⟩ else
    if (j : ℕ) = n then s (Fin.last n) + s' 0 - 1 else s' ⟨j - n, by omega⟩

/-- For `i < n`, the `i`-th corner coordinate is `sᵢ`. -/
lemma cornerCoords_castAdd (s : Fin (n + 1) → ℝ) (s' : Fin (n' + 1) → ℝ) (i : Fin n) :
    cornerCoords s s' (Fin.castAdd (n' + 1) i) = s i.castSucc := by
  simp [cornerCoords, i.isLt]
  rfl

/-- The `n`-th corner coordinate is `s_n + s'_0 - 1`, and for `0 < k ≤ n'` the `(n + k)`-th
corner coordinate is `s'_k`. -/
lemma cornerCoords_natAdd (s : Fin (n + 1) → ℝ) (s' : Fin (n' + 1) → ℝ) (k : Fin (n' + 1)) :
    cornerCoords s s' (Fin.natAdd n k) =
      if k = 0 then s (Fin.last n) + s' 0 - 1 else s' k := by
  simp only [cornerCoords, Fin.coe_natAdd, add_lt_iff_neg_left, not_lt_zero', dite_false,
    add_eq_left, Fin.ext_iff, Fin.val_zero]
  split_ifs <;> first | rfl | (congr 1; ext; simp)

/-- A sum over `Fin (n + n' + 1)` splits as a sum over the first `n` indices plus a sum over
the last `n' + 1` indices. -/
lemma sum_fin_add {M : Type*} [AddCommMonoid M] (f : Fin (n + n' + 1) → M) :
    ∑ j, f j = ∑ i : Fin n, f (Fin.castAdd (n' + 1) i) + ∑ k : Fin (n' + 1), f (Fin.natAdd n k) :=
  Fin.sum_univ_add (a := n) (b := n' + 1) f

/-- The point `(p, p')` has barycentric coordinates `cornerCoords s s'` in the corner simplex. -/
lemma sum_cornerCoords_smul {v : Fin (n + 1) → H} {w : Fin (n' + 1) → H'} {p : H} {p' : H'}
    {s : Fin (n + 1) → ℝ} {s' : Fin (n' + 1) → ℝ} (hs1 : ∑ k, s k = 1) (hs : ∑ k, s k • v k = p)
    (hs1' : ∑ k, s' k = 1) (hs' : ∑ k, s' k • w k = p') :
    ∑ j, cornerCoords s s' j = 1 ∧ ∑ j, cornerCoords s s' j • cornerVertices v w j = (p, p') := by
  have hsum' : ∑ k : Fin (n' + 1), (if k = 0 then s (Fin.last n) + s' 0 - 1 else s' k) =
      s (Fin.last n) := by
    rw [Fin.sum_univ_succ, if_pos rfl]
    simp only [Fin.succ_ne_zero, if_false]
    rw [Fin.sum_univ_succ] at hs1'
    linarith
  refine ⟨?_, ?_⟩
  · rw [sum_fin_add]
    simp only [cornerCoords_castAdd, cornerCoords_natAdd]
    rw [hsum', ← Fin.sum_univ_castSucc, hs1]
  · rw [sum_fin_add]
    simp only [cornerCoords_castAdd, cornerCoords_natAdd, cornerVertices_castAdd,
      cornerVertices_natAdd]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst]
      rw [← Finset.sum_smul, hsum']
      rw [Fin.sum_univ_castSucc] at hs
      exact hs
    · simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd]
      have e1 : ∑ i : Fin n, s i.castSucc • w 0 = (1 - s (Fin.last n)) • w 0 := by
        rw [← Finset.sum_smul]
        congr 1
        rw [Fin.sum_univ_castSucc] at hs1
        linarith
      have e2 : ∑ k : Fin (n' + 1), (if k = 0 then s (Fin.last n) + s' 0 - 1 else s' k) • w k =
          (s (Fin.last n) + s' 0 - 1) • w 0 + ∑ k : Fin n', s' k.succ • w k.succ := by
        rw [Fin.sum_univ_succ, if_pos rfl]
        simp only [Fin.succ_ne_zero, if_false]
      have e3 : p' = s' 0 • w 0 + ∑ k : Fin n', s' k.succ • w k.succ := by
        rw [← hs', Fin.sum_univ_succ]
      rw [e1, e2, e3, ← add_assoc, ← add_smul]
      congr 2
      ring

variable [TopologicalSpace H] [ContinuousAdd H] [ContinuousSMul ℝ H] [TopologicalSpace H']
  [ContinuousAdd H'] [ContinuousSMul ℝ H']

/-- For `i < n`, the `(i + 1)`-th vertex of the corner simplex is `(v_{i+1}, w₀)`. -/
lemma cornerVertices_succ_castAdd (v : Fin (n + 1) → H) (w : Fin (n' + 1) → H') (i : Fin n) :
    cornerVertices v w (Fin.castAdd n' i).succ = (v i.succ, w 0) := by
  simp only [cornerVertices, Prod.mk.injEq]
  constructor <;> congr 1 <;> ext <;> simp <;> omega

/-- For `k < n'`, the `(n + k + 1)`-th vertex of the corner simplex is `(vₙ, w_{k+1})`. -/
lemma cornerVertices_succ_natAdd (v : Fin (n + 1) → H) (w : Fin (n' + 1) → H') (k : Fin n') :
    cornerVertices v w (Fin.natAdd n k).succ = (v (Fin.last n), w k.succ) := by
  simp only [cornerVertices, Prod.mk.injEq]
  constructor <;> congr 1 <;> ext <;> simp <;> omega

/-- The `0`-th vertex of the corner simplex is `(v₀, w₀)`. -/
lemma cornerVertices_zero (v : Fin (n + 1) → H) (w : Fin (n' + 1) → H') :
    cornerVertices v w 0 = (v 0, w 0) := by
  simp only [cornerVertices, Prod.mk.injEq]
  constructor <;> congr 1 <;> ext <;> simp

/-- **The corner simplex is positively oriented** for the product orientation. -/
lemma det_cornerVertices_pos {b : Module.Basis (Fin n) ℝ H} {b' : Module.Basis (Fin n') ℝ H'}
    {v : Fin (n + 1) → H} {w : Fin (n' + 1) → H'} (hv : 0 < b.det fun k ↦ v k.succ - v 0)
    (hw : 0 < b'.det fun k ↦ w k.succ - w 0) :
    0 < ((b.prod b').reindex finSumFinEquiv).det
      fun k ↦ cornerVertices v w k.succ - cornerVertices v w 0 := by
  rw [Module.Basis.det_reindex, Module.Basis.det_apply]
  have hm : (b.prod b').toMatrix ((fun k ↦ cornerVertices v w k.succ - cornerVertices v w 0) ∘
      finSumFinEquiv) = Matrix.fromBlocks (b.toMatrix fun k ↦ v k.succ - v 0)
        (Matrix.of fun a _ ↦ b.repr (v (Fin.last n) - v 0) a) 0
        (b'.toMatrix fun k ↦ w k.succ - w 0) := by
    ext r c
    rcases r with a | a <;> rcases c with i | k <;>
      simp [Module.Basis.toMatrix_apply, Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        cornerVertices_succ_castAdd, cornerVertices_succ_natAdd, cornerVertices_zero]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, ← Module.Basis.det_apply, ← Module.Basis.det_apply]
  exact mul_pos hv hw

/-- **The corner simplex is an oriented simplex around `(p, p')`.** -/
theorem isOrientedSimplexAroundZero_cornerVertices {b : Module.Basis (Fin n) ℝ H}
    {b' : Module.Basis (Fin n') ℝ H'} {v : Fin (n + 1) → H} {w : Fin (n' + 1) → H'} {p : H}
    {p' : H'} (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - p)
    (hw : IsOrientedSimplexAroundZero b' fun k ↦ w k - p') {s : Fin (n + 1) → ℝ}
    {s' : Fin (n' + 1) → ℝ} (hs0 : ∀ k, 0 < s k) (hs1 : ∑ k, s k = 1) (hs : ∑ k, s k • v k = p)
    (hs0' : ∀ k, 0 < s' k) (hs1' : ∑ k, s' k = 1) (hs' : ∑ k, s' k • w k = p')
    (hcorner : 1 < s (Fin.last n) + s' 0) :
    IsOrientedSimplexAroundZero ((b.prod b').reindex finSumFinEquiv)
      fun j ↦ cornerVertices v w j - (p, p') := by
  obtain ⟨h1, h2⟩ := sum_cornerCoords_smul (v := v) (w := w) hs1 hs hs1' hs'
  refine ⟨⟨cornerCoords s s', fun j ↦ ?_, h1, ?_⟩, ?_⟩
  · unfold cornerCoords
    split_ifs
    · exact hs0 _
    · linarith
    · exact hs0' _
  · simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul, h2, sub_self]
  · have := det_cornerVertices_pos (b := b) (b' := b') (v := v) (w := w)
      (by simpa using hv.2) (by simpa using hw.2)
    simpa using this

end Corner

section Barycentric

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousSMul ℝ V] {n : ℕ}

/-- **Small oriented simplices with prescribed barycentric coordinates.** Every neighbourhood
of a point `p` contains an affine simplex around `p`, positively oriented for `b`, in which `p`
has the prescribed barycentric coordinates `λ`. -/
theorem exists_isOrientedSimplexAroundZero_barycentric (b : Module.Basis (Fin n) ℝ V) (p : V)
    {W : Set V} (hW : W ∈ 𝓝 p) {l : Fin (n + 1) → ℝ} (hl0 : ∀ k, 0 < l k)
    (hl1 : ∑ k, l k = 1) :
    ∃ v : Fin (n + 1) → V, IsOrientedSimplexAroundZero b (fun k ↦ v k - p) ∧
      ∑ k, l k • v k = p ∧ range (affineSimplex v) ⊆ W := by
  set u : Fin (n + 1) → V := Fin.cons (-∑ j, b j) b
  have hu := isOrientedSimplexAroundZero_cons_neg_sum b
  set c : V := ∑ k, l k • u k
  set u' : Fin (n + 1) → V := fun k ↦ u k - c
  have hu'0 : ∑ k, l k • u' k = 0 := by
    simp only [u', smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hl1, one_smul, c,
      sub_self]
  have hu' : IsOrientedSimplexAroundZero b u' := by
    refine ⟨⟨l, hl0, hl1, hu'0⟩, ?_⟩
    have : (fun k : Fin n ↦ u' k.succ - u' 0) = fun k ↦ u k.succ - u 0 := by
      funext k; simp [u']
    rw [this]
    exact hu.2
  set K : Set V := (fun t : Fin (n + 1) → ℝ ↦ ∑ k, t k • u' k) '' stdSimplex ℝ (Fin (n + 1))
  have hK : IsCompact K := (isCompact_stdSimplex ℝ _).image
    (continuous_finset_sum _ fun k _ ↦ (continuous_apply k).smul continuous_const)
  obtain ⟨ε, hε0, -, hεK⟩ := FundamentalClass.exists_smul_mem_of_isCompact hK p hW
  refine ⟨fun k ↦ p + ε • u' k, ?_, ?_, ?_⟩
  · have : (fun k ↦ (p + ε • u' k) - p) = ε • u' := by funext k; simp
    rw [this]
    exact hu'.smul hε0
  · simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hl1, one_smul,
      smul_comm (l _) ε, ← Finset.smul_sum, hu'0, smul_zero, add_zero]
  · rintro _ ⟨t, rfl⟩
    rw [affineSimplex_apply]
    have hts : ∑ k, (t : Fin (n + 1) → ℝ) k = 1 := t.2.2
    have : ∑ k, (t : Fin (n + 1) → ℝ) k • (p + ε • u' k) =
        p + ε • ∑ k, (t : Fin (n + 1) → ℝ) k • u' k := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hts, one_smul,
        smul_comm (t _) ε, ← Finset.smul_sum]
    rw [this]
    exact hεK _ ⟨t, t.2, rfl⟩

/-- Pushing barycentric coordinates along a vertex map and evaluating is evaluating at the image
vertices: `∑ᵢ (g_* t)ᵢ vᵢ = ∑ⱼ tⱼ v_{g j}`. -/
lemma sum_stdSimplex_map_smul {m p : ℕ} (g : Fin (m + 1) → Fin (p + 1))
    (t : stdSimplex ℝ (Fin (m + 1))) (v : Fin (p + 1) → V) :
    ∑ i, ((stdSimplex.map g t : stdSimplex ℝ (Fin (p + 1))) : Fin (p + 1) → ℝ) i • v i =
      ∑ j, (t : Fin (m + 1) → ℝ) j • v (g j) := by
  change ∑ i, (FunOnFinite.linearMap ℝ ℝ g) t i • v i = _
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  rw [← Finset.sum_fiberwise Finset.univ g fun j ↦ (t : Fin (m + 1) → ℝ) j • v (g j)]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr ?_ fun j hj ↦ ?_
  · ext j; simp
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [hj]

end Barycentric

end ThomClass

end MMP
