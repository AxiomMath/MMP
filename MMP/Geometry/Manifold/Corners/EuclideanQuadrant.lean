module

public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# The boundary of the Euclidean quadrant, and its collar

The quadrant `Q = [0, ∞)^n`, the model `EuclideanQuadrant n` of manifolds with corners, has
interior the open quadrant `(0, ∞)^n` and frontier the set of its points with some coordinate
zero. A point of a manifold modelled on `Q` is a boundary point exactly when its image in the
preferred chart (or in any chart of the atlas, for a `C¹` manifold) has a zero coordinate.

The boundary `∂Q` has a global collar along the diagonal direction `𝟙 = (1, …, 1)`: the map
`∂Q × [0, ∞) → Q`, `(x, t) ↦ x + t • 𝟙`, is a homeomorphism, with inverse
`y ↦ (y - (min_i y_i) • 𝟙, min_i y_i)`. This is the local model of a collar of the boundary of
a manifold with corners, corners included.

## Main results

* `MMP.Topology.interior_range_modelWithCornersEuclideanQuadrant`
* `MMP.Topology.frontier_range_modelWithCornersEuclideanQuadrant`
* `MMP.Topology.isBoundaryPoint_iff_exists_extChartAt_eq_zero`
* `MMP.Topology.isBoundaryPoint_iff_exists_extend_eq_zero_of_mem_atlas`
* `MMP.Topology.quadrantCollar`: the collar homeomorphism `∂Q × [0, ∞) ≃ₜ Q`.
-/

@[expose] public section

open Set Function
open scoped Manifold

namespace MMP.Topology

variable {n : ℕ}

private theorem range_modelWithCornersEuclideanQuadrant (n : ℕ) :
    range (modelWithCornersEuclideanQuadrant n) = {y | ∀ i : Fin n, 0 ≤ y i} :=
  range_euclideanQuadrant n

/-- The interior of the quadrant `[0, ∞)^n` is the open quadrant `(0, ∞)^n`. -/
theorem interior_range_modelWithCornersEuclideanQuadrant (n : ℕ) :
    interior (range (modelWithCornersEuclideanQuadrant n)) = {y | ∀ i, 0 < y i} := by
  rw [range_modelWithCornersEuclideanQuadrant]
  exact interior_euclideanQuadrant n 2 0

/-- The frontier of the quadrant `[0, ∞)^n` is the set of its points with some coordinate zero. -/
theorem frontier_range_modelWithCornersEuclideanQuadrant (n : ℕ) :
    frontier (range (modelWithCornersEuclideanQuadrant n)) =
      {y | (∀ i, 0 ≤ y i) ∧ ∃ i, y i = 0} := by
  rw [frontier, (modelWithCornersEuclideanQuadrant n).isClosed_range.closure_eq,
    interior_range_modelWithCornersEuclideanQuadrant, range_modelWithCornersEuclideanQuadrant]
  ext y
  simp only [mem_diff, mem_setOf_eq, not_forall, not_lt]
  constructor
  · rintro ⟨h, i, hi⟩
    exact ⟨h, i, le_antisymm hi (h i)⟩
  · rintro ⟨h, i, hi⟩
    exact ⟨h, i, hi.le⟩

/-- A point of a manifold modelled on the quadrant is a boundary point exactly when its image
in the preferred extended chart has a zero coordinate. -/
theorem isBoundaryPoint_iff_exists_extChartAt_eq_zero {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanQuadrant n) M] {x : M} :
    (modelWithCornersEuclideanQuadrant n).IsBoundaryPoint x ↔
      ∃ i, extChartAt (modelWithCornersEuclideanQuadrant n) x x i = 0 := by
  rw [ModelWithCorners.isBoundaryPoint_iff, frontier_range_modelWithCornersEuclideanQuadrant]
  have hmem : extChartAt (modelWithCornersEuclideanQuadrant n) x x ∈
      range (modelWithCornersEuclideanQuadrant n) :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  rw [range_modelWithCornersEuclideanQuadrant] at hmem
  simp only [mem_setOf_eq]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨hmem, h⟩⟩

/-- On a `C¹` manifold modelled on the quadrant, a point is a boundary point exactly when its
image in any chart of the atlas containing it has a zero coordinate. -/
theorem isBoundaryPoint_iff_exists_extend_eq_zero_of_mem_atlas {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M] {k : WithTop ℕ∞}
    [IsManifold (modelWithCornersEuclideanQuadrant n) k M] (hk : k ≠ 0)
    {e : OpenPartialHomeomorph M (EuclideanQuadrant n)} (he : e ∈ atlas (EuclideanQuadrant n) M)
    {x : M} (hx : x ∈ e.source) :
    (modelWithCornersEuclideanQuadrant n).IsBoundaryPoint x ↔ ∃ i, (e x).1 i = 0 := by
  rw [← not_iff_not, ← ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint,
    ModelWithCorners.isInteriorPoint_iff_of_mem_atlas hk he hx]
  have hopen : IsOpen ((modelWithCornersEuclideanQuadrant n).symm ⁻¹' e.target) :=
    e.open_target.preimage (modelWithCornersEuclideanQuadrant n).continuous_symm
  have htarget : (e.extend (modelWithCornersEuclideanQuadrant n)).target =
      (modelWithCornersEuclideanQuadrant n).symm ⁻¹' e.target ∩
        range (modelWithCornersEuclideanQuadrant n) := e.extend_target
  have hint : interior (e.extend (modelWithCornersEuclideanQuadrant n)).target =
      (modelWithCornersEuclideanQuadrant n).symm ⁻¹' e.target ∩ {y | ∀ i, 0 < y i} := by
    rw [htarget, interior_inter, hopen.interior_eq,
      interior_range_modelWithCornersEuclideanQuadrant]
  rw [hint]
  have hxt : (modelWithCornersEuclideanQuadrant n).symm
      (e.extend (modelWithCornersEuclideanQuadrant n) x) ∈ e.target := by
    simp only [OpenPartialHomeomorph.extend_coe, comp_apply, ModelWithCorners.left_inv]
    exact e.map_source hx
  simp only [mem_inter_iff, mem_preimage, hxt, true_and, mem_setOf_eq, not_exists, not_forall]
  simp only [OpenPartialHomeomorph.extend_coe, comp_apply, modelWithCornersEuclideanQuadrant_apply]
  exact ⟨fun h i ↦ (h i).ne', fun h i ↦ lt_of_le_of_ne ((e x).2 i) (Ne.symm (h i))⟩

/-! ### The diagonal collar of the quadrant -/

/-- The diagonal vector `(1, …, 1)`. -/
noncomputable abbrev quadrantDiagonal (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun _ ↦ (1 : ℝ)

/-- The smallest coordinate of a vector of `ℝ^n`, `n ≠ 0`. -/
noncomputable abbrev minCoord (n : ℕ) [NeZero n] (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i ↦ y i

/-- The smallest coordinate of `y` is at most each coordinate of `y`. -/
theorem minCoord_le [NeZero n] (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    minCoord n y ≤ y i :=
  Finset.inf'_le _ (Finset.mem_univ i)

/-- A real number is at most the smallest coordinate of `y` iff it is at most every coordinate. -/
theorem le_minCoord_iff [NeZero n] {y : EuclideanSpace ℝ (Fin n)} {a : ℝ} :
    a ≤ minCoord n y ↔ ∀ i, a ≤ y i := by
  simp [minCoord, Finset.le_inf'_iff]

/-- The smallest coordinate of `y` is attained by some coordinate of `y`. -/
theorem exists_eq_minCoord [NeZero n] (y : EuclideanSpace ℝ (Fin n)) :
    ∃ i, y i = minCoord n y := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin n))
    fun i ↦ y i
  exact ⟨i, hi.symm⟩

/-- The smallest coordinate is a continuous function on `ℝ^n`. -/
theorem continuous_minCoord [NeZero n] : Continuous (minCoord n) :=
  Continuous.finset_inf'_apply _ fun i _ ↦ PiLp.continuous_apply 2 _ i

/-- Translating `y` by `t • (1, …, 1)` adds `t` to its smallest coordinate. -/
theorem minCoord_add_smul_diagonal [NeZero n] (y : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    minCoord n (y + t • quadrantDiagonal n) = minCoord n y + t := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_eq_minCoord y
    calc minCoord n (y + t • quadrantDiagonal n) ≤ (y + t • quadrantDiagonal n) i :=
          minCoord_le _ i
      _ = minCoord n y + t := by simp [hi]
  · refine le_minCoord_iff.2 fun i ↦ ?_
    have := minCoord_le y i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_one]
    linarith

/-- The diagonal collar of the boundary of the quadrant:
`∂Q × [0, ∞) ≃ₜ Q`, `(x, t) ↦ x + t • (1, …, 1)`. -/
noncomputable def quadrantCollar (n : ℕ) [NeZero n] :
    {x : EuclideanQuadrant n | ∃ i, x.1 i = 0} × Ici (0 : ℝ) ≃ₜ EuclideanQuadrant n where
  toFun p := ⟨p.1.1.1 + (p.2 : ℝ) • quadrantDiagonal n, fun i ↦ by
    have h1 := p.1.1.2 i
    have h2 : (0 : ℝ) ≤ p.2 := p.2.2
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, mul_one]
    linarith⟩
  invFun y :=
    (⟨⟨y.1 - minCoord n y.1 • quadrantDiagonal n, fun i ↦ by
        have := minCoord_le y.1 i
        simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, mul_one]
        linarith⟩, by
        obtain ⟨i, hi⟩ := exists_eq_minCoord y.1
        exact ⟨i, by simp [hi]⟩⟩,
      ⟨minCoord n y.1, by
        obtain ⟨i, hi⟩ := exists_eq_minCoord y.1
        exact hi ▸ y.2 i⟩)
  left_inv p := by
    obtain ⟨⟨x, i, hi⟩, t, ht⟩ := p
    have hmin : minCoord n x.1 = 0 :=
      le_antisymm (hi ▸ minCoord_le x.1 i) (le_minCoord_iff.2 x.2)
    have hm : minCoord n (x.1 + t • quadrantDiagonal n) = t := by
      rw [minCoord_add_smul_diagonal, hmin, zero_add]
    ext1
    · ext1; ext1; simp only; rw [hm]; abel
    · ext1; exact hm
  right_inv y := by
    ext1
    simp only
    abel
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_subtype_val.comp continuous_subtype_val).comp continuous_fst).add
      ((continuous_subtype_val.comp continuous_snd).smul continuous_const)
  continuous_invFun := by
    have hm : Continuous fun y : EuclideanQuadrant n ↦ minCoord n y.1 :=
      continuous_minCoord.comp continuous_subtype_val
    refine Continuous.prodMk ?_ ?_
    · exact (Continuous.subtype_mk (continuous_subtype_val.sub (hm.smul continuous_const)) _
        ).subtype_mk _
    · exact hm.subtype_mk _

/-- The collar sends `(x, t)` to `x + t • (1, …, 1)`. -/
@[simp]
theorem quadrantCollar_apply_coe [NeZero n]
    (p : {x : EuclideanQuadrant n | ∃ i, x.1 i = 0} × Ici (0 : ℝ)) :
    (quadrantCollar n p).1 = p.1.1.1 + (p.2 : ℝ) • quadrantDiagonal n := rfl

/-- The boundary component of the inverse collar is `y - (min_i y_i) • (1, …, 1)`. -/
@[simp]
theorem quadrantCollar_symm_apply_fst_coe [NeZero n] (y : EuclideanQuadrant n) :
    ((quadrantCollar n).symm y).1.1.1 = y.1 - minCoord n y.1 • quadrantDiagonal n := rfl

/-- The time component of the inverse collar is the smallest coordinate. -/
@[simp]
theorem quadrantCollar_symm_apply_snd_coe [NeZero n] (y : EuclideanQuadrant n) :
    (((quadrantCollar n).symm y).2 : ℝ) = minCoord n y.1 := rfl

/-- The collar restricts to the inclusion of the boundary at time `0`. -/
@[simp]
theorem quadrantCollar_apply_zero [NeZero n] (x : {x : EuclideanQuadrant n | ∃ i, x.1 i = 0}) :
    quadrantCollar n (x, ⟨0, mem_Ici.2 le_rfl⟩) = x.1 := by
  ext1; simp

end MMP.Topology
