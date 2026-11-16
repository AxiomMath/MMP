module

public import MMP.AlgebraicTopology.ThomClass.Basic
public import MMP.Topology.Algebra.Matrix.DetPosPath

/-!
# Oriented simplices around a point form a path-connected set

Let `V` be a real vector space with a basis `b` of `n` vectors. The tuples `v₀, …, vₙ` of
vertices of an affine simplex around `0`, positively oriented for `b`
(`MMP.ThomClass.IsOrientedSimplexAroundZero`), form a path-connected subset of
`V^{n+1}`. This is the input that makes the local orientation `[Δ] ∈ H_n(V, V - 0)` independent
of the oriented simplex `Δ`.

A tuple `v` around `0` is first translated, through tuples around `0`, until its barycentre is
`0`. A tuple `v` with barycentre `0` is the image of the standard tuple
`-(b₁ + ⋯ + bₙ), b₁, …, bₙ` under the linear map `L` with `L bₖ = vₖ`, of positive
determinant; a path from `1` to `L` in `GL⁺` (`MMP.MatrixDetPos.joinedIn_one_of_det_pos`) moves the
standard tuple to `v` through oriented tuples with barycentre `0`.

## Main results

* `MMP.ThomClass.isOrientedSimplexAroundZero_cons_neg_sum`: the standard tuple.
* `MMP.ThomClass.joinedIn_isOrientedSimplexAroundZero`: any two oriented tuples
  around `0` are joined by a path of oriented tuples around `0`.
-/

@[expose] public section

open Set

namespace MMP

namespace ThomClass

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (b : Module.Basis (Fin n) ℝ V)

/-- The standard tuple `-(b₁ + ⋯ + bₙ), b₁, …, bₙ` is an oriented simplex around `0`. -/
lemma isOrientedSimplexAroundZero_cons_neg_sum :
    IsOrientedSimplexAroundZero b (Fin.cons (-∑ j, b j) b) := by
  refine ⟨⟨fun _ ↦ 1 / (n + 1), fun _ ↦ by positivity, ?_, ?_⟩, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  · rw [Fin.sum_univ_succ]
    simp [← Finset.smul_sum]
  · have : (fun k : Fin n ↦ (Fin.cons (-∑ j, b j) b : Fin (n + 1) → V) k.succ -
        (Fin.cons (-∑ j, b j) b : Fin (n + 1) → V) 0) = fun k ↦ b k + ∑ j, b j := by
      funext k; simp
    rw [this, Module.Basis.det_apply]
    have hm : b.toMatrix (fun k ↦ b k + ∑ j, b j) =
        (1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.replicateCol Unit (fun _ : Fin n ↦ (1 : ℝ)) *
            Matrix.replicateRow Unit (fun _ : Fin n ↦ (1 : ℝ)) := by
      ext i k
      simp [Module.Basis.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm,
        Matrix.mul_apply]
    rw [hm, Matrix.det_one_add_replicateCol_mul_replicateRow]
    simp only [dotProduct, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    positivity

/-- The image of an oriented simplex around `0` under a linear map of positive determinant is an
oriented simplex around `0`. -/
lemma IsOrientedSimplexAroundZero.map_linearMap_of_det_pos {b} {v : Fin (n + 1) → V}
    (hv : IsOrientedSimplexAroundZero b v) {L : V →ₗ[ℝ] V}
    (hL : 0 < LinearMap.det L) : IsOrientedSimplexAroundZero b (L ∘ v) := by
  obtain ⟨⟨t, ht0, ht1, htv⟩, hdet⟩ := hv
  refine ⟨⟨t, ht0, ht1, ?_⟩, ?_⟩
  · simpa [map_sum] using congrArg L htv
  · have : (fun k : Fin n ↦ (L ∘ v) k.succ - (L ∘ v) 0) = L ∘ fun k ↦ v k.succ - v 0 := by
      funext k; simp
    rw [this, Module.Basis.det_comp]
    exact mul_pos hL hdet

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- An oriented tuple around `0` is joined, through oriented tuples around `0`, to its
translate with barycentre `0`. -/
lemma joinedIn_sub_barycentre {v : Fin (n + 1) → V} (hv : IsOrientedSimplexAroundZero b v) :
    JoinedIn {w | IsOrientedSimplexAroundZero b w} v
      (fun k ↦ v k - ((n : ℝ) + 1)⁻¹ • ∑ j, v j) := by
  set q : V := ((n : ℝ) + 1)⁻¹ • ∑ j, v j
  obtain ⟨⟨t, ht0, ht1, htv⟩, hdet⟩ := hv
  refine JoinedIn.ofLine (f := fun s : ℝ ↦ fun k ↦ v k - s • q) ?_ ?_ ?_ ?_
  · have : (fun s : ℝ ↦ fun k ↦ v k - s • q) = fun s k ↦ v k + (-s) • q := by
      funext s k; rw [neg_smul, sub_eq_add_neg]
    rw [this]
    exact (continuous_pi fun k ↦ continuous_const.add (continuous_neg.smul continuous_const))
      |>.continuousOn
  · funext k; simp
  · funext k; simp
  · rintro _ ⟨s, ⟨hs0, hs1⟩, rfl⟩
    have hsum : ∑ k, ((1 - s) * t k + s * ((n : ℝ) + 1)⁻¹) = 1 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ht1, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      push_cast
      ring
    refine ⟨⟨fun k ↦ (1 - s) * t k + s * ((n : ℝ) + 1)⁻¹, fun k ↦ ?_, hsum, ?_⟩, ?_⟩
    · rcases eq_or_lt_of_le hs1 with rfl | hs1
      · simp only [sub_self, zero_mul, one_mul, zero_add]
        positivity
      · have := ht0 k
        have : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
        nlinarith
    · have h1 : ∑ k, ((1 - s) * t k + s * ((n : ℝ) + 1)⁻¹) • v k =
          (1 - s) • ∑ k, t k • v k + s • q := by
        simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, q]
      have h2 : ∑ k, ((1 - s) * t k + s * ((n : ℝ) + 1)⁻¹) • (v k - s • q) =
          ∑ k, ((1 - s) * t k + s * ((n : ℝ) + 1)⁻¹) • v k -
            (∑ k, ((1 - s) * t k + s * ((n : ℝ) + 1)⁻¹)) • s • q := by
        simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
      rw [h2, h1, hsum, htv, smul_zero, zero_add, one_smul, sub_self]
    · simpa using hdet

/-- The standard tuple `-(b₁ + ⋯ + bₙ), b₁, …, bₙ` is joined, through oriented simplices
around `0`, to any oriented simplex around `0` with barycentre `0`. -/
lemma joinedIn_cons_neg_sum {v : Fin (n + 1) → V} (hv : IsOrientedSimplexAroundZero b v)
    (hv0 : ∑ k, v k = 0) :
    JoinedIn {w | IsOrientedSimplexAroundZero b w} (Fin.cons (-∑ j, b j) b) v := by
  set std : Fin (n + 1) → V := Fin.cons (-∑ j, b j) b
  have hstd := isOrientedSimplexAroundZero_cons_neg_sum b
  set L : V →ₗ[ℝ] V := b.constr ℝ fun j ↦ v j.succ
  have hLv : L ∘ std = v := by
    funext k
    refine Fin.cases ?_ (fun j ↦ ?_) k
    · have h := hv0
      rw [Fin.sum_univ_succ] at h
      simp only [std, Function.comp_apply, Fin.cons_zero, map_neg, map_sum, L,
        Module.Basis.constr_basis]
      rw [eq_neg_of_add_eq_zero_left h]
    · simp [std, L]
  have hdetL : 0 < LinearMap.det L := by
    have h := hv.2
    have : (fun k : Fin n ↦ v k.succ - v 0) = L ∘ fun k ↦ std k.succ - std 0 := by
      rw [← hLv]; funext k; simp
    rw [this, Module.Basis.det_comp] at h
    exact pos_of_mul_pos_left h hstd.2.le
  set M := LinearMap.toMatrix b b L
  have hM : 0 < M.det := by rwa [LinearMap.det_toMatrix]
  set Φ : Matrix (Fin n) (Fin n) ℝ → Fin (n + 1) → V := fun A k ↦ Matrix.toLin b b A (std k)
  have hΦ : Continuous Φ := by
    refine continuous_pi fun k ↦ ?_
    simp only [Φ, Matrix.toLin_apply]
    exact continuous_finsetSum _ fun i _ ↦
      ((continuous_apply i).comp (continuous_id.matrix_mulVec continuous_const)).smul
        continuous_const
  have h := (MMP.MatrixDetPos.joinedIn_one_of_det_pos hM).map hΦ.continuousOn
  have h0 : Φ 1 = std := by funext k; simp [Φ]
  have h1 : Φ M = v := by rw [← hLv]; funext k; simp [Φ, M]
  rw [h0, h1] at h
  refine h.mono ?_
  rintro _ ⟨A, hA, rfl⟩
  exact hstd.map_linearMap_of_det_pos (L := Matrix.toLin b b A) (by rwa [LinearMap.det_toLin])

/-- **Oriented simplices around `0` are path connected**: two tuples of vertices of affine
simplices around `0` positively oriented for `b` are joined by a path of such tuples. -/
theorem joinedIn_isOrientedSimplexAroundZero {v w : Fin (n + 1) → V}
    (hv : IsOrientedSimplexAroundZero b v) (hw : IsOrientedSimplexAroundZero b w) :
    JoinedIn {u | IsOrientedSimplexAroundZero b u} v w := by
  have hv' := joinedIn_sub_barycentre b hv
  have hw' := joinedIn_sub_barycentre b hw
  have hbar : ∀ u : Fin (n + 1) → V,
      ∑ k, (u k - ((n : ℝ) + 1)⁻¹ • ∑ j, u j) = 0 := fun u ↦ by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← Nat.cast_succ, mul_inv_cancel₀ (by positivity),
      one_smul, sub_self]
  exact hv'.trans (((joinedIn_cons_neg_sum b (hv'.target_mem) (hbar v)).symm).trans
    ((joinedIn_cons_neg_sum b hw'.target_mem (hbar w)).trans hw'.symm))

end ThomClass

end MMP
