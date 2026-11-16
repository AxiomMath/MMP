module

public import MMP.AlgebraicGeometry.Analytic.SchemeManifold
public import MMP.Analysis.Complex.OrientedConeSimplices
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.Basic
public import MMP.AlgebraicGeometry.ProjectiveSpace.NoetherNormalization
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.GenericCovering
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.LocallyContractible

/-!
# Fundamental cycles of flat chart cones on a smooth projective curve

Let `X` be a smooth projective complex curve. We develop the building blocks of finite real
singular `2`-cycles of `X^an` made of *flat chart cones*: triangles which, read on the unit
square through the collapse `squareCollapse : [0, 1]² → Δ²`, are `c⁻¹ ∘ g` for an étale chart
`c` and a `C²` map `g` whose Jacobian `Im(conj(∂₁ g) ∂₂ g)` has the sign
of the coefficient on an open neighbourhood of the square.

The local building block is the flat segment `y ↦ b + ρ(y) (c - b)`, `ρ = coneProfile`. Seen
from a point `P`, it turns at the rate `ρ'(y) Im(conj(b - P)(c - b))`, which has one sign on all
of `ℝ`. So the flat cone from `P` over a segment on whose left `P` lies has a reading of
nonnegative Jacobian (`exists_reading_coneSimplex_segmentCurve`). The path simplex of a flat
segment is the radial simplex with the same endpoints (`pathSimplex_segmentCurve`), so the edge
`u → v` is one singular simplex, whether it appears as the base or as a side of a cone.

Near a ramification point of index `e` of a map `X → ℙ¹`, a cone from the branch value lifts
through the `e`-th root of the profile. `rootProfile e` is again flat and smooth, with
`rootProfile e ^ e = coneProfile` (`rootProfile_pow`).

## Main definitions

* `MMP.Analytic.ChartConeCellulation.segmentCurve`: the flat segment from `b` to `c`.
* `MMP.Analytic.ChartConeCellulation.rootProfile`: the `e`-th root of the flat profile.
* `MMP.Analytic.ChartConeCellulation.simplexLifts`: the lifts of a singular simplex along a map.
* `MMP.Analytic.ChartConeCellulation.transferSimplex`: the transfer of a singular simplex, the
  sum of its lifts when there are finitely many.
* `MMP.Analytic.ChartConeCellulation.transfer`: the transfer of singular chains, sending a
  simplex to the sum of its lifts.

## Main results

* `MMP.Analytic.ChartConeCellulation.im_star_sub_mul_deriv_segmentCurve`: the turning of a flat
  segment around a point.
* `MMP.Analytic.ChartConeCellulation.exists_reading_coneSimplex_segmentCurve`: the reading of
  the flat cone over a segment.
* `MMP.Analytic.ChartConeCellulation.rootProfile_pow`: `rootProfile e ^ e = coneProfile`.
* `MMP.Analytic.ChartConeCellulation.bd_transfer_eq_zero_of_bijOn`,
  `MMP.Analytic.ChartConeCellulation.bijOn_comp_face_of_isCoveringMapOn`: the transfer of a cycle
  along a map whose lifts restrict bijectively to faces is a cycle, as for a covering.
* `MMP.Analytic.ChartConeCellulation.exists_isFinite_surjective_projectiveLine`: a smooth
  projective curve is a finite cover of `ℙ¹`.
* `MMP.Analytic.ChartConeCellulation.exists_finite_isCoveringMapOn_compl`: a proper surjective
  morphism of complex curves is a covering map off a finite set.
* `MMP.Analytic.ChartConeCellulation.exists_isFinite_isCoveringMapOn_projectiveLine`: the finite
  map `X → ℙ¹` and its finite branch set.

## Implementation notes

The intended cycle is the transfer, along a finite surjective morphism `f : X → ℙ¹`, of an explicit
cellulation of `ℙ¹(ℂ)`. In the coordinate `z`, a grid of squares is offset so that the finitely
many branch values lie in the open squares, at most one in each. In the coordinate `1 / z`
there is one cell around `∞`. Each cell is cut into flat cones from an interior apex, the branch
value of the cell if it has one. Over a cell with no branch value, `f` has `deg f` holomorphic
sections. Over a cell with branch value `s`, a lift of a cone from `s` is read in a normal-form
coordinate `w` with `w^e = f - s` as the cone with profile `rootProfile e` over an `e`-th root of
the base arc. Restricting lifts to faces is a bijection onto the lifts of the faces, so the sum
of all lifts is a cycle.

## References

* [S. Donaldson, *Riemann Surfaces*], §8 (triangulation by pulling back along a meromorphic
  function).
-/

@[expose] public noncomputable section

open Set Finsupp MMP.SingularChain
open CategoryTheory AlgebraicGeometry MMP
open MMP.Intersection.Scheme (dimension)
open MMP.Analytic MMP.Analytic.CurveCupPositivity

namespace MMP.Analytic.ChartConeCellulation

/-! ### The flat profile and its roots -/

section Profile

/-- The flat profile vanishes on `(-∞, 0]`. -/
theorem coneProfile_of_nonpos {x : ℝ} (hx : x ≤ 0) : coneProfile x = 0 := by
  simp [coneProfile, expNegInvGlue.zero_of_nonpos hx]

/-- The flat profile is nondecreasing: its derivative is nonnegative everywhere. -/
theorem deriv_coneProfile_nonneg (x : ℝ) : 0 ≤ deriv coneProfile x := by
  rcases le_or_gt x 0 with hx | hx
  · have hmin : IsLocalMin coneProfile x :=
      Filter.Eventually.of_forall fun y ↦ by
        simpa [coneProfile_of_nonpos hx] using coneProfile_nonneg y
    exact hmin.deriv_eq_zero.ge
  · exact (deriv_coneProfile_pos hx).le

/-- The `e`-th root `x ↦ ρ(e x) / ρ(e)` of the flat profile `ρ = coneProfile`. -/
def rootProfile (e : ℕ) (x : ℝ) : ℝ := coneProfile (e * x) / coneProfile e

/-- The root profile is `C^k` for every finite `k`. -/
theorem contDiff_rootProfile (e : ℕ) {k : WithTop ℕ∞} (hk : k ≠ ⊤) :
    ContDiff ℝ k (rootProfile e) :=
  ((contDiff_coneProfile hk).comp (contDiff_const.mul contDiff_id)).div_const _

/-- The root profile is continuous. -/
theorem continuous_rootProfile (e : ℕ) : Continuous (rootProfile e) :=
  (contDiff_rootProfile e (k := 0) (by simp)).continuous

/-- The root profile is differentiable. -/
theorem differentiable_rootProfile (e : ℕ) : Differentiable ℝ (rootProfile e) :=
  (contDiff_rootProfile e (k := 1) (by simp)).differentiable (by simp)

/-- The root profile vanishes at `0`. -/
@[simp]
theorem rootProfile_zero (e : ℕ) : rootProfile e 0 = 0 := by
  simp [rootProfile]

/-- For `0 < e`, the root profile takes the value `1` at `1`. -/
theorem rootProfile_one {e : ℕ} (he : 0 < e) : rootProfile e 1 = 1 := by
  rw [rootProfile, mul_one]
  exact div_self (coneProfile_pos (by exact_mod_cast he)).ne'

/-- The root profile is nonnegative. -/
theorem rootProfile_nonneg (e : ℕ) (x : ℝ) : 0 ≤ rootProfile e x :=
  div_nonneg (coneProfile_nonneg _) (coneProfile_nonneg _)

/-- For `0 < e`, the root profile is positive on `(0, ∞)`. -/
theorem rootProfile_pos {e : ℕ} (he : 0 < e) {x : ℝ} (hx : 0 < x) : 0 < rootProfile e x :=
  div_pos (coneProfile_pos (mul_pos (by exact_mod_cast he) hx))
    (coneProfile_pos (by exact_mod_cast he))

/-- The derivative of the root profile: `(rootProfile e)'(x) = e ρ'(e x) / ρ(e)`. -/
theorem deriv_rootProfile (e : ℕ) (x : ℝ) :
    deriv (rootProfile e) x = e * deriv coneProfile (e * x) / coneProfile e := by
  have h1 : HasDerivAt (fun y : ℝ ↦ (e : ℝ) * y) e x := by
    simpa using (hasDerivAt_id x).const_mul (e : ℝ)
  rw [show rootProfile e = fun y ↦ (coneProfile ∘ HMul.hMul (e : ℝ)) y / coneProfile e from rfl,
    (((differentiable_coneProfile (e * x)).hasDerivAt.comp x h1).div_const _).deriv]
  ring

/-- The root profile is nondecreasing: its derivative is nonnegative everywhere. -/
theorem deriv_rootProfile_nonneg (e : ℕ) (x : ℝ) : 0 ≤ deriv (rootProfile e) x := by
  rw [deriv_rootProfile]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg e) (deriv_coneProfile_nonneg _))
    (coneProfile_nonneg _)

/-- For `0 < e`, the derivative of the root profile is positive on `(0, ∞)`. -/
theorem deriv_rootProfile_pos {e : ℕ} (he : 0 < e) {x : ℝ} (hx : 0 < x) :
    0 < deriv (rootProfile e) x := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rw [deriv_rootProfile]
  exact div_pos (mul_pos he' (deriv_coneProfile_pos (mul_pos he' hx))) (coneProfile_pos he')

/-- The product of the root profile and its derivative is nonnegative. -/
theorem rootProfile_mul_deriv_nonneg (e : ℕ) (x : ℝ) :
    0 ≤ rootProfile e x * deriv (rootProfile e) x :=
  mul_nonneg (rootProfile_nonneg e x) (deriv_rootProfile_nonneg e x)

/-- **The `e`-th power of the root profile is the flat profile.** -/
theorem rootProfile_pow {e : ℕ} (he : 0 < e) (x : ℝ) : rootProfile e x ^ e = coneProfile x := by
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  rcases le_or_gt x 0 with hx | hx
  · rw [rootProfile, coneProfile_of_nonpos (mul_nonpos_of_nonneg_of_nonpos he'.le hx),
      coneProfile_of_nonpos hx, zero_div, zero_pow he.ne']
  · have hg : ∀ y : ℝ, 0 < y → expNegInvGlue y = Real.exp (-y⁻¹) := fun y hy ↦ by
      simp [expNegInvGlue, not_le.2 hy]
    simp only [rootProfile, coneProfile]
    rw [hg _ (mul_pos he' hx), hg _ he', hg _ hx, hg _ one_pos,
      div_div_div_cancel_right₀ (Real.exp_pos _).ne', div_pow, ← Real.exp_nat_mul,
      ← Real.exp_nat_mul]
    congr 1 <;> congr 1 <;> field_simp

end Profile

/-! ### Flat segments -/

section Segment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The flat segment `y ↦ b + ρ(y) (c - b)` from `b` to `c`, with `ρ = coneProfile`. -/
def segmentCurve (b c : E) (y : ℝ) : E := b + coneProfile y • (c - b)

/-- The flat segment is `C^k` for every finite `k`. -/
theorem contDiff_segmentCurve (b c : E) {k : WithTop ℕ∞} (hk : k ≠ ⊤) :
    ContDiff ℝ k (segmentCurve b c) :=
  contDiff_const.add ((contDiff_coneProfile hk).smul contDiff_const)

/-- The flat segment is continuous. -/
theorem continuous_segmentCurve (b c : E) : Continuous (segmentCurve b c) :=
  (contDiff_segmentCurve b c (k := 0) (by simp)).continuous

/-- The flat segment from `b` to `c` starts at `b`. -/
@[simp]
theorem segmentCurve_zero (b c : E) : segmentCurve b c 0 = b := by
  simp [segmentCurve]

/-- The flat segment from `b` to `c` ends at `c`. -/
@[simp]
theorem segmentCurve_one (b c : E) : segmentCurve b c 1 = c := by
  simp [segmentCurve]

/-- The flat segment from `b` to `c` has derivative `ρ'(y) (c - b)` at `y`. -/
theorem hasDerivAt_segmentCurve (b c : E) (y : ℝ) :
    HasDerivAt (segmentCurve b c) (deriv coneProfile y • (c - b)) y :=
  ((differentiable_coneProfile y).hasDerivAt.smul_const (c - b)).const_add b

/-- The derivative of the flat segment from `b` to `c` at `y` is `ρ'(y) (c - b)`. -/
theorem deriv_segmentCurve (b c : E) (y : ℝ) :
    deriv (segmentCurve b c) y = deriv coneProfile y • (c - b) :=
  (hasDerivAt_segmentCurve b c y).deriv

/-- **The path simplex of a flat segment is the radial simplex with the same endpoints.** So the
edge `b → c` is one singular simplex, as the base of a cone or as one of its sides. -/
theorem pathSimplex_segmentCurve (b c : E) :
    pathSimplex (continuous_segmentCurve b c).continuousOn =
      radialSimplex continuous_coneProfile b c := by
  ext t
  have h1 : t 1 ∈ Icc (0 : ℝ) 1 := ⟨stdSimplex_apply_nonneg t 1, by
    linarith [stdSimplex_two_add t, stdSimplex_apply_nonneg t 0]⟩
  change clampCurve (segmentCurve b c) (t 1) = b + coneProfile (t 1) • (c - b)
  rw [clampCurve_of_mem _ h1]
  rfl

end Segment

section SegmentTurning

variable {n : ℕ}

/-- **The turning of a flat segment.** Seen from `P`, the flat segment from `b` to `c` turns at
the rate `ρ'(y) Im(conj(b - P)(c - b))` in each coordinate, of constant sign along all of `ℝ`. -/
theorem im_star_sub_mul_deriv_segmentCurve (P b c : Fin n → ℂ) (y : ℝ) (i : Fin n) :
    (star (segmentCurve b c y i - P i) * deriv (segmentCurve b c) y i).im =
      deriv coneProfile y * (star (b i - P i) * (c i - b i)).im := by
  rw [deriv_segmentCurve]
  simp only [segmentCurve, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Complex.real_smul,
    star_add, star_sub, star_mul', Complex.star_def, Complex.conj_ofReal]
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- If `P` lies on the left of `b → c` in every coordinate, the flat segment from `b` to `c` turns
nonnegatively around `P` at every time `y`. -/
theorem im_star_sub_mul_deriv_segmentCurve_nonneg {P b c : Fin n → ℂ}
    (hleft : ∀ i, 0 ≤ (star (b i - P i) * (c i - b i)).im) (y : ℝ) (i : Fin n) :
    0 ≤ (star (segmentCurve b c y i - P i) * deriv (segmentCurve b c) y i).im := by
  rw [im_star_sub_mul_deriv_segmentCurve]
  exact mul_nonneg (deriv_coneProfile_nonneg y) (hleft i)

/-- **The reading of the flat cone over a segment.** If `P` lies on the left of `b → c` in every
coordinate and the cone from `P` over the flat segment lies, on the square, in the target of a
chart `e`, then the cone simplex pushed along `e⁻¹` is read through the collapse as `e⁻¹ ∘ g` for
the cone map `g`, `C²` with nonnegative Jacobian on an open neighbourhood of the square. -/
theorem exists_reading_coneSimplex_segmentCurve {Y : Type*} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y (Fin n → ℂ)) {P b c : Fin n → ℂ}
    (hleft : ∀ i, 0 ≤ (star (b i - P i) * (c i - b i)).im)
    (hT : MapsTo (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c)) unitSquare
      e.target) :
    ∃ (hσ : range (coneSimplex continuous_coneProfile coneProfile_zero P
        (continuous_segmentCurve b c).continuousOn) ⊆ e.target) (U : Set (ℝ × ℝ)),
      IsOpen U ∧ unitSquare ⊆ U ∧
      ContDiffOn ℝ 2 (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c)) U ∧
      MapsTo (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c)) U e.target ∧
      (∀ p ∈ unitSquare, mapSimplex e.symm e.continuousOn_symm
        (coneSimplex continuous_coneProfile coneProfile_zero P
          (continuous_segmentCurve b c).continuousOn) hσ
          (squareCollapse p) =
            e.symm (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c) p)) ∧
      ∀ p ∈ U, ∀ i : Fin n,
        0 ≤ (star (fderiv ℝ (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c)) p
            (1, 0) i) *
          fderiv ℝ (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c)) p (0, 1) i).im :=
  exists_reading_coneSimplex e P isOpen_univ (subset_univ _)
    (contDiff_segmentCurve b c (by simp)).contDiffOn
    (fun y _ i ↦ im_star_sub_mul_deriv_segmentCurve_nonneg hleft y i) hT

/-- The flat cone over a segment has positive Jacobian at interior points, when `P` lies strictly
on the left of `b → c`. -/
theorem im_star_fderiv_coneMap_segmentCurve_pos {P b c : Fin n → ℂ} {x y : ℝ} (hx : 0 < x)
    (hy : 0 < y) (i : Fin n) (hleft : 0 < (star (b i - P i) * (c i - b i)).im) :
    0 < (star (fderiv ℝ (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c)) (x, y)
        (1, 0) i) *
      fderiv ℝ (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c)) (x, y)
        (0, 1) i).im := by
  refine im_star_fderiv_coneMap_pos hx
    ((contDiff_segmentCurve b c (k := 1) (by simp)).differentiable (by simp) y) i ?_
  rw [im_star_sub_mul_deriv_segmentCurve]
  exact mul_pos (deriv_coneProfile_pos hy) hleft

/-- **The fan of flat cones over a polygon.** For vertices `v₀, …, v_{k-1}` in the coordinates of
a chart `e` and the flat cones from `P` over the flat segments `vⱼ → vⱼ₊₁` (indices mod `k`),
pushed along `e⁻¹`, the boundary of their sum is the sum of the edges `vⱼ → vⱼ₊₁`, each the
radial simplex `t ↦ vⱼ + ρ(t₁)(vⱼ₊₁ - vⱼ)` pushed along `e⁻¹`. -/
theorem bd_sum_single_mapSimplex_coneSimplex_segmentCurve {R : Type*} [CommRing R]
    {Y : Type*} [TopologicalSpace Y] {k : ℕ} (e : OpenPartialHomeomorph Y (Fin n → ℂ))
    (P : Fin n → ℂ) (v : Fin k → Fin n → ℂ)
    (hσ : ∀ j, range (coneSimplex continuous_coneProfile coneProfile_zero P
      (continuous_segmentCurve (v j) (v (finRotate k j))).continuousOn) ⊆ e.target)
    (hr : ∀ j, range (radialSimplex continuous_coneProfile (v j) (v (finRotate k j))) ⊆
      e.target) :
    bd R 1 (∑ j, single (mapSimplex e.symm e.continuousOn_symm _ (hσ j)) 1) =
      ∑ j, single (mapSimplex e.symm e.continuousOn_symm _ (hr j)) 1 := by
  rw [bd_sum_single_mapSimplex_coneSimplex e P (fun j ↦ segmentCurve (v j) (v (finRotate k j)))
    (fun j ↦ (continuous_segmentCurve _ _).continuousOn) hσ
    (fun j ↦ by simp)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [mapSimplex_comp_face]
  congr 1
  exact mapSimplex_congr _ _ (by
    rw [coneSimplex_comp_face_zero continuous_coneProfile coneProfile_zero coneProfile_one,
      pathSimplex_segmentCurve]) _ _

/-- The corners `(x₁, y₁), (x₂, y₁), (x₂, y₂), (x₁, y₂)` of an axis-parallel rectangle of `ℂ`,
counterclockwise. -/
def rectangleCorners (x₁ x₂ y₁ y₂ : ℝ) : Fin 4 → ℂ :=
  ![⟨x₁, y₁⟩, ⟨x₂, y₁⟩, ⟨x₂, y₂⟩, ⟨x₁, y₂⟩]

/-- **An interior point lies strictly on the left of every edge of a rectangle.** So the fan of
flat cones from an interior point over the edges of a rectangle has positive Jacobian at interior
points of the square (`im_star_fderiv_coneMap_segmentCurve_pos`). -/
theorem im_star_sub_mul_sub_rectangleCorners_pos {x₁ x₂ y₁ y₂ : ℝ} {P : ℂ}
    (hx : P.re ∈ Ioo x₁ x₂) (hy : P.im ∈ Ioo y₁ y₂) (j : Fin 4) :
    0 < (star (rectangleCorners x₁ x₂ y₁ y₂ j - P) *
      (rectangleCorners x₁ x₂ y₁ y₂ (finRotate 4 j) - rectangleCorners x₁ x₂ y₁ y₂ j)).im := by
  obtain ⟨hx₁, hx₂⟩ := hx
  obtain ⟨hy₁, hy₂⟩ := hy
  fin_cases j <;>
    simp [rectangleCorners, finRotate_apply, Complex.mul_im, Complex.conj_re,
      Complex.conj_im] <;> nlinarith

end SegmentTurning

/-! ### Transfer of chains along a map with finitely many lifts -/

section Transfer

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- The lifts `T'` of a singular simplex `T` of `Z` along `p : Y → Z`: `p ∘ T' = T`. -/
def simplexLifts (p : Y → Z) {k : ℕ} (T : Simplex Z k) : Set (Simplex Y k) :=
  {T' | p ∘ T' = T}

/-- `T'` is a lift of `T` along `p` exactly when `p ∘ T' = T`. -/
@[simp]
theorem mem_simplexLifts {p : Y → Z} {k : ℕ} {T : Simplex Z k} {T' : Simplex Y k} :
    T' ∈ simplexLifts p T ↔ p ∘ T' = T :=
  Iff.rfl

open Classical in
/-- The transfer of a singular simplex: the sum of its lifts when there are finitely many, and
`0` otherwise. -/
def transferSimplex (R : Type*) [CommRing R] (p : Y → Z) {k : ℕ} (T : Simplex Z k) :
    Chain R Y k :=
  if h : (simplexLifts p T).Finite then ∑ T' ∈ h.toFinset, single T' 1 else 0

/-- The transfer of a simplex with finitely many lifts is the sum of its lifts. -/
theorem transferSimplex_of_finite (R : Type*) [CommRing R] {p : Y → Z} {k : ℕ}
    {T : Simplex Z k} (h : (simplexLifts p T).Finite) :
    transferSimplex R p T = ∑ T' ∈ h.toFinset, single T' 1 := by
  classical
  rw [transferSimplex, dif_pos h]

/-- The transfer of a simplex with infinitely many lifts is `0`. -/
theorem transferSimplex_of_not_finite (R : Type*) [CommRing R] {p : Y → Z} {k : ℕ}
    {T : Simplex Z k} (h : ¬(simplexLifts p T).Finite) : transferSimplex R p T = 0 := by
  classical
  rw [transferSimplex, dif_neg h]

/-- The transfer of singular chains along `p`: the linear extension of `transferSimplex`, sending
a simplex to the sum of its lifts when there are finitely many, and to `0` otherwise. -/
def transfer (R : Type*) [CommRing R] (p : Y → Z) (k : ℕ) : Chain R Z k →ₗ[R] Chain R Y k :=
  linearCombination R (transferSimplex R p)

/-- The transfer of `r • T` is `r` times the transfer of the simplex `T`. -/
@[simp]
theorem transfer_single (R : Type*) [CommRing R] (p : Y → Z) {k : ℕ} (T : Simplex Z k) (r : R) :
    transfer R p k (single T r) = r • transferSimplex R p T := by
  simp [transfer]

/-- Restricting a lift of `T` to its `i`-th face gives a lift of the `i`-th face of `T`. -/
theorem mapsTo_comp_simplexLifts (p : Y → Z) {k : ℕ} (T : Simplex Z (k + 1)) (i : Fin (k + 2)) :
    MapsTo (fun T' : Simplex Y (k + 1) ↦ T'.comp (face k i)) (simplexLifts p T)
      (simplexLifts p (T.comp (face k i))) := fun T' hT' ↦ by
  funext t
  exact congrFun hT' (face k i t)

/-- **The transfer commutes with the boundary on a simplex whose lifts restrict bijectively to
the lifts of its faces.** -/
theorem bd_transferSimplex_of_bijOn (R : Type*) [CommRing R] (p : Y → Z) {k : ℕ}
    (T : Simplex Z (k + 1)) (hfin : (simplexLifts p T).Finite)
    (hbij : ∀ i, BijOn (fun T' : Simplex Y (k + 1) ↦ T'.comp (face k i)) (simplexLifts p T)
      (simplexLifts p (T.comp (face k i)))) :
    bd R k (transferSimplex R p T) = transfer R p k (bd R k (single T 1)) := by
  classical
  rw [transferSimplex_of_finite R hfin, map_sum, bd_single, map_sum]
  simp only [bd_single, map_smul, transfer_single, one_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.smul_sum]
  congr 1
  have hfin' : (simplexLifts p (T.comp (face k i))).Finite := (hbij i).image_eq ▸ hfin.image _
  have himg : hfin.toFinset.image (fun T' : Simplex Y (k + 1) ↦ T'.comp (face k i)) =
      hfin'.toFinset := by
    ext ε
    simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    rw [← (hbij i).image_eq]
    rfl
  rw [transferSimplex_of_finite R hfin', ← himg, Finset.sum_image fun a ha b hb hab ↦
    (hbij i).injOn (by simpa using ha) (by simpa using hb) hab]

/-- The transfer commutes with the boundary on a chain each of whose simplices has finitely many
lifts restricting bijectively to the lifts of its faces. -/
theorem bd_transfer_of_bijOn (R : Type*) [CommRing R] (p : Y → Z) {k : ℕ}
    (w : Chain R Z (k + 1)) (hfin : ∀ T ∈ w.support, (simplexLifts p T).Finite)
    (hbij : ∀ T ∈ w.support, ∀ i, BijOn (fun T' : Simplex Y (k + 1) ↦ T'.comp (face k i))
      (simplexLifts p T) (simplexLifts p (T.comp (face k i)))) :
    bd R k (transfer R p (k + 1) w) = transfer R p k (bd R k w) := by
  conv_lhs => rw [← w.sum_single]
  conv_rhs => rw [← w.sum_single]
  rw [Finsupp.sum, map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun T hT ↦ ?_
  rw [transfer_single, map_smul, bd_transferSimplex_of_bijOn R p T (hfin T hT) (hbij T hT),
    ← map_smul, ← map_smul, smul_single, smul_eq_mul, mul_one]

/-- **The transfer of a cycle is a cycle**, when every simplex of it has finitely many lifts
restricting bijectively to the lifts of its faces. -/
theorem bd_transfer_eq_zero_of_bijOn (R : Type*) [CommRing R] (p : Y → Z) {k : ℕ}
    (w : Chain R Z (k + 1)) (hw : bd R k w = 0)
    (hfin : ∀ T ∈ w.support, (simplexLifts p T).Finite)
    (hbij : ∀ T ∈ w.support, ∀ i, BijOn (fun T' : Simplex Y (k + 1) ↦ T'.comp (face k i))
      (simplexLifts p T) (simplexLifts p (T.comp (face k i)))) :
    bd R k (transfer R p (k + 1) w) = 0 := by
  rw [bd_transfer_of_bijOn R p w hfin hbij, hw, map_zero]

/-- **Lifts through a covering restrict bijectively to lifts of a face.** If `p` is a covering
map over a set `s` containing the image of a singular simplex `T`, restricting lifts of `T` to
the `i`-th face is a bijection onto the lifts of that face: lifts from the simply connected,
locally path connected simplex exist through every point of the fibre, and are unique. -/
theorem bijOn_comp_face_of_isCoveringMapOn {p : Y → Z} {s : Set Z} (hp : IsCoveringMapOn p s)
    {k : ℕ} (T : Simplex Z (k + 1)) (hT : ∀ t, T t ∈ s) (i : Fin (k + 2)) :
    BijOn (fun T' : Simplex Y (k + 1) ↦ T'.comp (face k i)) (simplexLifts p T)
      (simplexLifts p (T.comp (face k i))) := by
  haveI := Winding.simplyConnectedSpace_stdSimplex (k + 1)
  haveI := Winding.locallyPathConnectedSpace_stdSimplex (k + 1)
  haveI := Winding.simplyConnectedSpace_stdSimplex k
  haveI := Winding.locallyPathConnectedSpace_stdSimplex k
  let b₀ : stdSimplex ℝ (Fin (k + 1)) := ⟨_, single_mem_stdSimplex ℝ 0⟩
  refine ⟨mapsTo_comp_simplexLifts p T i, fun T₁ h₁ T₂ h₂ h ↦ ?_, fun ε hε ↦ ?_⟩
  · have h₀ : T₁ (face k i b₀) = T₂ (face k i b₀) :=
      congrArg (fun f : Simplex Y k ↦ f b₀) h
    have he : p (T₁ (face k i b₀)) = T (face k i b₀) := congrFun h₁ _
    obtain ⟨F, -, hF⟩ := hp.existsUnique_continuousMap_lifts T he hT
    exact (hF T₁ ⟨rfl, h₁⟩).trans (hF T₂ ⟨h₀.symm, h₂⟩).symm
  · have he : p (ε b₀) = T (face k i b₀) := congrFun hε b₀
    obtain ⟨F, ⟨hF0, hFp⟩, -⟩ := hp.existsUnique_continuousMap_lifts T he hT
    refine ⟨F, hFp, ?_⟩
    have he' : p (ε b₀) = (T.comp (face k i)) b₀ := he
    obtain ⟨G, -, hG⟩ := hp.existsUnique_continuousMap_lifts (T.comp (face k i)) he'
      (fun t ↦ hT _)
    exact (hG _ ⟨hF0, mapsTo_comp_simplexLifts p T i hFp⟩).trans (hG ε ⟨rfl, hε⟩).symm

end Transfer

/-! ### The generic covering as a covering map -/

section GenericCoveringMap

open MMP.UnderlyingSpace TopologicalSpace Topology

/-- **A proper surjective morphism of complex varieties of the same dimension is a covering map
over a nonempty Zariski open.** There is a nonempty Zariski open `W₀ ⊆ W` such that
`f : V(ℂ) → W(ℂ)` is a covering map over the `ℂ`-points of `W₀`. -/
theorem exists_isCoveringMapOn_mapFun {V W : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [W.Over (Spec (.of ℂ))] [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))]
    [QuasiCompact (V ↘ Spec (.of ℂ))] [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))]
    [QuasiCompact (W ↘ Spec (.of ℂ))] [IsSeparated (V ↘ Spec (.of ℂ))]
    (f : V ⟶ W) [f.IsOver (Spec (.of ℂ))] [IsProper f] (hf : Function.Surjective f)
    (hdim : dimension V = dimension W) {n : ℕ} (hn : (n : WithBot ℕ∞) = dimension W) :
    ∃ W₀ : W.Opens, (W₀ : Set W).Nonempty ∧
      IsCoveringMapOn (mapFun (K := ℂ) f)
        {w : UnderlyingSpace ℂ W | w.toHom (IsLocalRing.closedPoint ℂ) ∈ W₀} := by
  obtain ⟨W₀, hne, -, -, hcov⟩ := GenericCovering.exists_preimage_eq_iUnion_diffeomorph f hf hdim
  refine ⟨W₀, hne, ?_⟩
  haveI : T2Space (UnderlyingSpace ℂ V) := t2Space_of_isSeparated V
  have hclosed : IsClosedMap (mapFun (K := ℂ) f) := (isProperMap_map (K := ℂ) f).isClosedMap
  have key : ∀ w ∈ {w : UnderlyingSpace ℂ W | w.toHom (IsLocalRing.closedPoint ℂ) ∈ W₀},
      ∃ (ι : Type) (_ : Finite ι) (Ui : ι → Opens (UnderlyingSpace ℂ V)),
        mapFun (K := ℂ) f ⁻¹' {w} ⊆ ⋃ i, (Ui i : Set (UnderlyingSpace ℂ V)) ∧
        ∀ i, IsOpenEmbedding (Set.restrict (Ui i : Set (UnderlyingSpace ℂ V)) (mapFun f)) := by
    intro w hw
    obtain ⟨U, -, hwU, -, -, Ui, -, hpre, hreg, hφ⟩ := hcov w hw
    refine ⟨_, inferInstance, Ui, fun e he ↦ ?_, fun i ↦ ?_⟩
    · have : e ∈ mapFun f ⁻¹' (U : Set (UnderlyingSpace ℂ W)) := by
        rw [Set.mem_preimage, Set.mem_singleton_iff.1 he]
        exact hwU
      rwa [hpre] at this
    · letI := regularChartedSpace (𝕜 := ℂ) (X := W) hn
      letI := regularChartedSpace (𝕜 := ℂ) (X := V) (hn.trans hdim.symm)
      obtain ⟨φ, hφf⟩ := (hφ n hn).2 i
      let k : (Ui i : Set (UnderlyingSpace ℂ V)) ≃ₜ regularOpensInter (Ui i) :=
        { toFun := fun x ↦ ⟨⟨x.1, hreg i x.2⟩, x.2⟩
          invFun := fun y ↦ ⟨y.1.1, y.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
          continuous_invFun :=
            (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
      have hval : IsOpenEmbedding
          (fun y : regularOpensInter U ↦ (y.1.1 : UnderlyingSpace ℂ W)) :=
        (regularOpens ℂ W).2.isOpenEmbedding_subtypeVal.comp
          (regularOpensInter U).2.isOpenEmbedding_subtypeVal
      have heq : Set.restrict (Ui i : Set (UnderlyingSpace ℂ V)) (mapFun f) =
          (fun y : regularOpensInter U ↦ (y.1.1 : UnderlyingSpace ℂ W)) ∘ φ ∘ k := by
        funext x
        exact (hφf (k x)).symm
      rw [heq]
      exact hval.comp (φ.toHomeomorph.isOpenEmbedding.comp k.isOpenEmbedding)
  refine hclosed.isCoveringMapOn_of_isLocalHomeomorphOn (fun w hw ↦ ?_) ?_
  · obtain ⟨ι, _, Ui, hsub, hemb⟩ := key w hw
    refine Set.Finite.subset (Set.finite_iUnion fun i ↦
      (show (mapFun (K := ℂ) f ⁻¹' {w} ∩ (Ui i : Set (UnderlyingSpace ℂ V))).Subsingleton from
        fun e he e' he' ↦ congrArg Subtype.val ((hemb i).injective
          (a₁ := ⟨e, he.2⟩) (a₂ := ⟨e', he'.2⟩)
          (show mapFun f e = mapFun f e' by rw [he.1, he'.1]))).finite) fun e he ↦ ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsub he)
    exact Set.mem_iUnion.2 ⟨i, he, hi⟩
  · rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
    intro e he
    obtain ⟨ι, _, Ui, hsub, hemb⟩ := key _ he
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hsub (Set.mem_singleton _))
    exact ⟨Ui i, (Ui i).2.mem_nhds hi, hemb i⟩

/-- A space of dimension at most one has no chain `a ⤳ b ⤳ c` of three distinct points. -/
theorem false_of_specializes_of_topologicalKrullDim_le_one {Y : Type*} [TopologicalSpace Y]
    [T0Space Y] (hY : topologicalKrullDim Y ≤ 1) {a b c : Y} (hab : a ⤳ b) (hbc : b ⤳ c)
    (hab' : a ≠ b) (hbc' : b ≠ c) : False := by
  let f : Fin 3 → IrreducibleCloseds Y := fun i ↦
    ⟨closure {![c, b, a] i}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt : ∀ {x y : Y}, x ⤳ y → x ≠ y →
      (⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ : IrreducibleCloseds Y) <
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ := by
    intro x y hxy hne
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp hxy) fun h ↦ hne ?_
    have : y ⤳ x := specializes_iff_closure_subset.mpr
      (le_of_eq (congrArg IrreducibleCloseds.carrier h).symm)
    exact (hxy.antisymm this).eq
  have hmono : StrictMono f := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · exact hlt hbc hbc'
    · exact hlt hab hab'
  have : ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim Y :=
    Order.le_krullDim_iff.mpr ⟨LTSeries.mk 2 f hmono, rfl⟩
  simpa using this.trans hY

/-- **A curve has finitely many closed points off a nonempty open.** In an irreducible
Noetherian quasi-sober `T₀` space of dimension at most one, the closed points outside a nonempty
open set form a finite set: the complement is a finite union of irreducible closed sets
`closure {g}` with `g` not the generic point, and a closed point `c ≠ g` of `closure {g}` would
give a chain `η ⤳ g ⤳ c`. -/
theorem finite_setOf_isClosed_singleton_notMem {Y : Type*} [TopologicalSpace Y]
    [NoetherianSpace Y] [QuasiSober Y] [T0Space Y] [IrreducibleSpace Y]
    (hY : topologicalKrullDim Y ≤ 1) {O : Set Y} (hO : IsOpen O) (hne : O.Nonempty) :
    {y : Y | IsClosed ({y} : Set Y) ∧ y ∉ O}.Finite := by
  obtain ⟨T, hTf, hTc, hTi, hT⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hO.isClosed_compl
  have hη : genericPoint Y ∈ O :=
    ((genericPoint_spec Y).mem_open_set_iff hO).2 (by simpa using hne)
  choose g hg using fun t (ht : t ∈ T) ↦ QuasiSober.sober (hTi t ht) (hTc t ht)
  refine (Set.Finite.biUnion' (t := fun t ht ↦ ({g t ht} : Set Y)) hTf
    fun _ _ ↦ Set.finite_singleton _).subset fun y ⟨hyc, hyO⟩ ↦ ?_
  obtain ⟨t, ht, hyt⟩ := Set.mem_sUnion.1 (hT ▸ hyO : y ∈ ⋃₀ T)
  refine Set.mem_iUnion₂.2 ⟨t, ht, ?_⟩
  by_contra hne'
  have hgt : g t ht ∈ t := (hg t ht).mem
  have hgO : g t ht ∉ O := fun h ↦ (hT ▸ Set.mem_sUnion_of_mem hgt ht : g t ht ∈ Oᶜ) h
  have hgy : g t ht ⤳ y := by rwa [specializes_iff_mem_closure, (hg t ht).def]
  have hηg : genericPoint Y ⤳ g t ht := (genericPoint_spec Y).specializes (Set.mem_univ _)
  exact false_of_specializes_of_topologicalKrullDim_le_one hY hηg hgy
    (fun h ↦ hgO (h ▸ hη)) (Ne.symm hne')

/-- **The generic covering over the complement of a finite set.** A proper surjective morphism
`f : V → W` of complex varieties of the same dimension `1`, with `W` Noetherian, is a covering
map `V(ℂ) → W(ℂ)` over the complement of a finite set of points. -/
theorem exists_finite_isCoveringMapOn_compl {V W : Scheme.{0}} [V.Over (Spec (.of ℂ))]
    [W.Over (Spec (.of ℂ))] [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))]
    [QuasiCompact (V ↘ Spec (.of ℂ))] [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))]
    [QuasiCompact (W ↘ Spec (.of ℂ))] [IsSeparated (V ↘ Spec (.of ℂ))]
    [NoetherianSpace W] (f : V ⟶ W) [f.IsOver (Spec (.of ℂ))] [IsProper f]
    (hf : Function.Surjective f) (hdim : dimension V = dimension W)
    (hW : dimension W = (1 : ℕ)) :
    ∃ S : Set (UnderlyingSpace ℂ W), S.Finite ∧ IsCoveringMapOn (mapFun (K := ℂ) f) Sᶜ := by
  obtain ⟨W₀, hne, hcov⟩ := exists_isCoveringMapOn_mapFun f hf hdim hW.symm
  refine ⟨{w | w.toHom (IsLocalRing.closedPoint ℂ) ∉ W₀}, ?_,
    by simpa [Set.compl_setOf] using hcov⟩
  have hF := finite_setOf_isClosed_singleton_notMem (Y := W) (by rw [← dimension, hW]; rfl)
    W₀.2 hne
  exact (hF.preimage (f := fun w : UnderlyingSpace ℂ W ↦ (equivClosedPoints W w : W))
    (fun a _ b _ h ↦ (equivClosedPoints W).injective (Subtype.ext h))).subset
    fun w hw ↦ ⟨(equivClosedPoints W w).2, hw⟩

end GenericCoveringMap

/-! ### The curve -/

section Curve

open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]

/-- **A smooth projective curve is a finite cover of the projective line.** There is a finite
surjective morphism `X ⟶ ℙ¹ = Proj ℂ[x₀, x₁]` over `ℂ`, the projective line lying over `ℂ`
through `projToSpecCoeff ℂ 1`. -/
theorem exists_isFinite_surjective_projectiveLine
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))] :
    letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) :=
      ⟨projToSpecCoeff ℂ 1⟩
    ∃ f : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ 1),
      f.IsOver (Spec (.of ℂ)) ∧ IsFinite f ∧ Surjective f := by
  obtain ⟨N, i, hi, hover⟩ :=
    (inferInstance : AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))).isProjective
  haveI := hi
  set ι : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ N) :=
    i ≫ (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ N).iso.hom
  have hιo : ι ≫ projToSpecCoeff ℂ N = X ↘ Spec (.of ℂ) := by
    rw [Category.assoc,
      Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff, ← hover]
    rfl
  have hdim : topologicalKrullDim X = (1 : ℕ) := by
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 1
  obtain ⟨f, hff, hfs, hf⟩ := MMP.ProjectiveSpace.exists_isFinite_surjective ι hdim
  rw [hιo] at hf
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) := ⟨projToSpecCoeff ℂ 1⟩
  exact ⟨f, ⟨hf⟩, hff, hfs⟩

/-- **A finite map of a smooth projective curve to `ℙ¹` and its branch set.** There is a finite
surjective `f : X ⟶ ℙ¹ = Proj ℂ[x₀, x₁]` over `ℂ`, the projective line lying over `ℂ` through
`projToSpecCoeff ℂ 1`, and a finite set `S ⊆ ℙ¹(ℂ)` over whose complement `f : X(ℂ) → ℙ¹(ℂ)` is
a covering map. -/
theorem exists_isFinite_isCoveringMapOn_projectiveLine
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))] :
    letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) :=
      ⟨projToSpecCoeff ℂ 1⟩
    ∃ (f : X ⟶ AlgebraicGeometry.Proj (polyGrading ℂ 1)) (_ : f.IsOver (Spec (.of ℂ)))
      (_ : IsFinite f) (S : Set (UnderlyingSpace ℂ (AlgebraicGeometry.Proj (polyGrading ℂ 1)))),
      Surjective f ∧ S.Finite ∧ IsCoveringMapOn (UnderlyingSpace.mapFun (K := ℂ) f) Sᶜ := by
  letI : (AlgebraicGeometry.Proj (polyGrading ℂ 1)).Over (Spec (.of ℂ)) :=
    ⟨projToSpecCoeff ℂ 1⟩
  obtain ⟨f, hfo, hff, hfs⟩ := exists_isFinite_surjective_projectiveLine (X := X)
  haveI := hfo
  haveI := hff
  haveI : IsProper (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ)) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff ℂ 1
  haveI : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading ℂ 1)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (AlgebraicGeometry.Proj (polyGrading ℂ 1) ↘ Spec (.of ℂ))
  haveI : IsNoetherian (AlgebraicGeometry.Proj (polyGrading ℂ 1)) := {}
  haveI : IsIntegral (AlgebraicGeometry.Proj (polyGrading ℂ 1)) :=
    Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj ℂ 1
  have hP : dimension (AlgebraicGeometry.Proj (polyGrading ℂ 1)) = (1 : ℕ) :=
    (Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin ℂ (Nat.succ_pos 1)).trans (by simp)
  have hX : dimension X = (1 : ℕ) := by
    rw [dimension]
    exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of ℂ)) 1
  obtain ⟨S, hS, hcov⟩ := exists_finite_isCoveringMapOn_compl f hfs.surj (hX.trans hP.symm) hP
  exact ⟨f, hfo, hff, S, hfs, hS, hcov⟩

end Curve

end MMP.Analytic.ChartConeCellulation
