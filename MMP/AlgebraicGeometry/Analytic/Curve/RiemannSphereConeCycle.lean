module

public import MMP.AlgebraicGeometry.Analytic.Curve.ChartConeCellulation
public import MMP.AlgebraicGeometry.Analytic.Curve.FundamentalClassChartCriterion
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension

/-!
# A fundamental cycle of flat cones on the Riemann sphere

Let `T` be a space with two charts `z, u : T → ℂ` onto `ℂ`, related by `u = 1 / z` off `z = 0`,
and covering `T`: the Riemann sphere `ℙ¹(ℂ)` with its two standard charts. We build a finite
real singular `2`-cycle `w` of `T` out of flat cones read in the two charts.

In the chart `z`, a big square is cut into a grid of small squares, each a fan of four flat
cones from an interior apex over its edges. The rest of the sphere is one cell around `∞`, read
in the chart `u`: the fan of flat cones from `u = 0` over the arcs `1 / β`, `β` running clockwise
over the edges of the big square. Seen from `0`, the arc `1 / β` turns at the rate
`-Im(conj β β') / |β|⁴` (`im_star_mul_deriv_invCurve`), so clockwise edges give counterclockwise
arcs.

An edge `u → v` and its reverse `v → u` add up to the boundary of a degenerate flat cone and a
constant triangle, both of Jacobian zero (`single_edgeSimplex_add_edgeSimplex`). So the boundary
of the sum of all the fans, a sum of edges in which each edge of the grid occurs once in each
direction, is a boundary of a chain of Jacobian zero.

## Main definitions

* `MMP.Analytic.ChartConeCellulation.SphereCharts`: two charts of a space making it a sphere.
* `MMP.Analytic.ChartConeCellulation.edgeSimplex`, `flatConeSimplex`: the flat edge and the flat
  cone over a segment, pushed along an inverse chart.
* `MMP.Analytic.ChartConeCellulation.invCurve`: the arc `y ↦ 1 / β(y)` of a flat segment `β`.

## Main results

* `MMP.Analytic.ChartConeCellulation.bd_single_flatConeSimplex`: the boundary of a flat cone.
* `MMP.Analytic.ChartConeCellulation.single_edgeSimplex_add_edgeSimplex`: an edge and its
  reverse bound a chain of Jacobian zero.
* `MMP.Analytic.ChartConeCellulation.im_star_mul_deriv_invCurve`: the turning of an inverted
  flat segment.
* `MMP.Analytic.ChartConeCellulation.bd_sphereChain`: the flat cone chain of a grid on the sphere
  is a cycle.
* `MMP.Analytic.ChartConeCellulation.exists_cone_cycle_of_sphereCharts`: a fine fundamental cycle
  of flat cones on a sphere, with prescribed apices.
* `MMP.Analytic.ChartConeCellulation.isVarietyFundamentalClass_of_simplePoint`: a cycle with a
  simple point of an oriented chart triangle represents the fundamental class of a curve.
-/

@[expose] public noncomputable section

open Set Finsupp MMP.SingularChain
open MMP.Analytic MMP.Analytic.CurveCupPositivity

namespace MMP.Analytic.ChartConeCellulation

/-! ### Two charts making a sphere -/

/-- **Sphere charts** on `T`: two charts `z = chart 0` and `u = chart 1` onto `ℂ`, covering `T`,
with `u = 1 / z` wherever `z ≠ 0`, and the point `u = 0` (the point at `∞`) outside the domain
of `z`. The Riemann sphere `ℙ¹(ℂ)` with its two standard affine charts is the example. -/
structure SphereCharts (T : Type*) [TopologicalSpace T] where
  /-- The two charts, `z` and `u = 1 / z`. -/
  chart : Fin 2 → OpenPartialHomeomorph T (Fin 1 → ℂ)
  /-- Both charts are onto `ℂ`. -/
  target_eq : ∀ k, (chart k).target = univ
  /-- The domains of the two charts cover `T`. -/
  source_union : (chart 0).source ∪ (chart 1).source = univ
  /-- A point of nonzero `z`-coordinate lies in the domain of `u`. -/
  symm_mem_source_one : ∀ v : Fin 1 → ℂ, v 0 ≠ 0 → (chart 0).symm v ∈ (chart 1).source
  /-- Off `z = 0`, `u = 1 / z`. -/
  chart_one_symm : ∀ v : Fin 1 → ℂ, v 0 ≠ 0 →
    chart 1 ((chart 0).symm v) = fun _ ↦ (v 0)⁻¹
  /-- The point `u = 0` lies outside the domain of `z`. -/
  symm_zero_notMem : (chart 1).symm 0 ∉ (chart 0).source

namespace SphereCharts

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- On `z ≠ 0`, the point of `z`-coordinate `v` has `u`-coordinate `1 / v`. -/
theorem symm_one_inv (v : Fin 1 → ℂ) (hv : v 0 ≠ 0) :
    (E.chart 1).symm (fun _ ↦ (v 0)⁻¹) = (E.chart 0).symm v := by
  rw [← E.chart_one_symm v hv]
  exact (E.chart 1).left_inv (E.symm_mem_source_one v hv)

/-- Every point of `T` other than the point at `∞` lies in the domain of `z`. -/
theorem mem_source_zero_of_ne {x : T} (hx : x ≠ (E.chart 1).symm 0) : x ∈ (E.chart 0).source := by
  by_contra h0
  have h1 : x ∈ (E.chart 1).source := (E.source_union.symm ▸ mem_univ x).resolve_left h0
  set w := E.chart 1 x
  have hw : w 0 ≠ 0 := by
    intro hw0
    apply hx
    have : w = 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]; exact hw0
    rw [← this]
    exact ((E.chart 1).left_inv h1).symm
  set v : Fin 1 → ℂ := fun _ ↦ (w 0)⁻¹
  have hv : v 0 ≠ 0 := inv_ne_zero hw
  have hvw : (fun _ : Fin 1 ↦ (v 0)⁻¹) = w := funext fun i ↦ by
    rw [Subsingleton.elim i 0]; simp [v]
  have : (E.chart 0).symm v = x := by
    rw [← E.symm_one_inv v hv, hvw]
    exact (E.chart 1).left_inv h1
  exact h0 (this ▸ (E.chart 0).map_target (by rw [E.target_eq]; exact mem_univ _))

end SphereCharts

/-! ### Flat edges and flat cones pushed along a chart onto `ℂ` -/

section Push

variable {T : Type*} [TopologicalSpace T] (e : OpenPartialHomeomorph T (Fin 1 → ℂ))
  (he : e.target = univ)

/-- The flat edge `t ↦ e⁻¹(u + ρ(t₁)(v - u))` from `e⁻¹ u` to `e⁻¹ v`. -/
def edgeSimplex (u v : Fin 1 → ℂ) : Simplex T 1 :=
  mapSimplex e.symm e.continuousOn_symm (radialSimplex continuous_coneProfile u v)
    (by rw [he]; exact subset_univ _)

/-- The flat cone from `P` over the flat segment `b → c`, pushed along `e⁻¹`. -/
def flatConeSimplex (P b c : Fin 1 → ℂ) : Simplex T 2 :=
  mapSimplex e.symm e.continuousOn_symm
    (coneSimplex continuous_coneProfile coneProfile_zero P
      (continuous_segmentCurve b c).continuousOn)
    (by rw [he]; exact subset_univ _)

/-- The constant `k`-simplex at a point of `T`. -/
def pointSimplex (k : ℕ) (x : T) : Simplex T k := ContinuousMap.const _ x

/-- The boundary of a constant triangle is the constant edge at the same point. -/
theorem bd_single_pointSimplex (x : T) :
    bd ℂ 1 (single (pointSimplex 2 x) 1) = single (pointSimplex 1 x) 1 := by
  have h : ∀ k : Fin 3, (pointSimplex 2 x).comp (face 1 k) = pointSimplex 1 x := fun k ↦ by
    ext t; rfl
  rw [bd_single_two, h, h, h]
  abel

/-- **The boundary of a flat cone**: the base edge `b → c`, minus the side `P → c`, plus the side
`P → b`. -/
theorem bd_single_flatConeSimplex (P b c : Fin 1 → ℂ) :
    bd ℂ 1 (single (flatConeSimplex e he P b c) 1) =
      single (edgeSimplex e he b c) 1 - single (edgeSimplex e he P c) 1 +
        single (edgeSimplex e he P b) 1 := by
  rw [bd_single_two]
  simp only [flatConeSimplex, mapSimplex_comp_face]
  rw [mapSimplex_congr _ _ (coneSimplex_comp_face_zero continuous_coneProfile coneProfile_zero
      coneProfile_one P _) _ (by rw [he]; exact subset_univ _),
    mapSimplex_congr _ _ (coneSimplex_comp_face_one continuous_coneProfile coneProfile_zero P _) _
      (by rw [he]; exact subset_univ _),
    mapSimplex_congr _ _ (coneSimplex_comp_face_two continuous_coneProfile coneProfile_zero P _) _
      (by rw [he]; exact subset_univ _)]
  rw [mapSimplex_congr _ _ (pathSimplex_segmentCurve b c) _ (by rw [he]; exact subset_univ _)]
  simp only [segmentCurve_zero, segmentCurve_one]
  rfl

/-- The flat edge from a point to itself is constant. -/
theorem edgeSimplex_self (u : Fin 1 → ℂ) : edgeSimplex e he u u = pointSimplex 1 (e.symm u) := by
  ext t
  simp [edgeSimplex, radialSimplex, pointSimplex]

/-- **An edge and its reverse bound a chain of Jacobian zero**: the degenerate flat cone from `u`
over the segment `v → u`, plus the constant triangle at `u`. -/
theorem single_edgeSimplex_add_edgeSimplex (u v : Fin 1 → ℂ) :
    single (edgeSimplex e he u v) (1 : ℂ) + single (edgeSimplex e he v u) 1 =
      bd ℂ 1 (single (flatConeSimplex e he u v u) 1 + single (pointSimplex 2 (e.symm u)) 1) := by
  rw [map_add, bd_single_flatConeSimplex, bd_single_pointSimplex, edgeSimplex_self]
  abel

/-- The degenerate flat cone from `u` over `v → u` has Jacobian zero. -/
theorem im_star_sub_mul_sub_rev_eq_zero (u v : Fin 1 → ℂ) (i : Fin 1) :
    (star (v i - u i) * (u i - v i)).im = 0 := by
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

end Push

/-! ### Inverted flat segments -/

section Inversion

/-- The arc `y ↦ 1 / β(y)` of the flat segment `β = segmentCurve b c`, in `ℂ = Fin 1 → ℂ`. -/
def invCurve (b c : Fin 1 → ℂ) (y : ℝ) : Fin 1 → ℂ := fun _ ↦ (segmentCurve b c y 0)⁻¹

/-- A flat segment on whose line `0` does not lie never vanishes. -/
theorem segmentCurve_ne_zero {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0) (y : ℝ) :
    segmentCurve b c y 0 ≠ 0 := by
  intro h0
  apply h
  simp only [segmentCurve, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Complex.real_smul] at h0
  have E1 := congrArg Complex.re h0
  have E2 := congrArg Complex.im h0
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.sub_im, Complex.zero_re, Complex.zero_im] at E1 E2
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  linear_combination ((c 0).im - (b 0).im) * E1 - ((c 0).re - (b 0).re) * E2

/-- The derivative of the coordinate of the flat segment `b → c` at `y` is `ρ'(y) (c - b)`, `ρ` the
cone profile. -/
theorem hasDerivAt_segmentCurve_zero (b c : Fin 1 → ℂ) (y : ℝ) :
    HasDerivAt (fun y ↦ segmentCurve b c y 0) (deriv coneProfile y * (c 0 - b 0)) y := by
  have := (hasDerivAt_pi.1 (hasDerivAt_segmentCurve b c y)) 0
  simpa [Complex.real_smul] using this

/-- The derivative of the inverted flat segment `1 / β` at `y` is `-ρ'(y) (c - b) / β(y)²`, when
`0` is not on the line of `b → c`. -/
theorem hasDerivAt_invCurve {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0) (y : ℝ) :
    HasDerivAt (invCurve b c)
      (fun _ ↦ -((segmentCurve b c y 0) ^ 2)⁻¹ * (deriv coneProfile y * (c 0 - b 0))) y := by
  refine hasDerivAt_pi.2 fun _ ↦ ?_
  exact (hasDerivAt_inv (segmentCurve_ne_zero h y)).comp y (hasDerivAt_segmentCurve_zero b c y)

/-- The inverted flat segment `1 / β` is `C^k` for every finite `k`, when `0` is not on the line of
`b → c`. -/
theorem contDiff_invCurve {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0)
    {k : WithTop ℕ∞} (hk : k ≠ ⊤) : ContDiff ℝ k (invCurve b c) := by
  refine contDiff_pi.2 fun _ ↦ ?_
  exact ((contDiff_pi.1 (contDiff_segmentCurve b c hk)) 0).inv (segmentCurve_ne_zero h)

/-- **The turning of an inverted flat segment.** Seen from `0`, the arc `1 / β` of the flat
segment `β` from `b` to `c` turns at the rate `-ρ'(y) Im(conj b (c - b)) / |β(y)|⁴`. -/
theorem im_star_mul_deriv_invCurve {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0)
    (y : ℝ) (i : Fin 1) :
    (star (invCurve b c y i - 0) * deriv (invCurve b c) y i).im =
      -(deriv coneProfile y * (star (b 0) * (c 0 - b 0)).im) /
        Complex.normSq (segmentCurve b c y 0) ^ 2 := by
  rw [(hasDerivAt_invCurve h y).deriv, sub_zero]
  set β := segmentCurve b c y 0 with hβ
  have hβ0 : β ≠ 0 := segmentCurve_ne_zero h y
  have hseg : (star β * (deriv coneProfile y * (c 0 - b 0))).im =
      deriv coneProfile y * (star (b 0) * (c 0 - b 0)).im := by
    have := im_star_sub_mul_deriv_segmentCurve 0 b c y 0
    rw [deriv_segmentCurve] at this
    simpa [Complex.real_smul] using this
  have hn : (Complex.normSq β : ℂ) = star β * β := by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  have hn0 : (Complex.normSq β : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hβ0).ne'
  have key : star (β⁻¹) * (-(β ^ 2)⁻¹ * (deriv coneProfile y * (c 0 - b 0))) =
      -(star β * (deriv coneProfile y * (c 0 - b 0))) / ((Complex.normSq β : ℝ) : ℂ) ^ 2 := by
    have hsβ : star β ≠ 0 := star_ne_zero.2 hβ0
    rw [hn, star_inv₀]
    field_simp
  simp only [invCurve]
  rw [key, ← hseg, neg_div, Complex.neg_im, ← Complex.ofReal_pow, Complex.div_ofReal_im, neg_div]

/-- The arc `1 / β` turns counterclockwise around `0` when `0` lies strictly on the right of
`b → c`. -/
theorem im_star_mul_deriv_invCurve_nonneg {b c : Fin 1 → ℂ}
    (h : (star (b 0) * (c 0 - b 0)).im < 0) (y : ℝ) (i : Fin 1) :
    0 ≤ (star (invCurve b c y i - 0) * deriv (invCurve b c) y i).im := by
  rw [im_star_mul_deriv_invCurve h.ne]
  exact div_nonneg (by nlinarith [deriv_coneProfile_nonneg y]) (sq_nonneg _)

/-- The arc `1 / β` turns strictly counterclockwise around `0` at every `y > 0` when `0` lies
strictly on the right of `b → c`. -/
theorem im_star_mul_deriv_invCurve_pos {b c : Fin 1 → ℂ}
    (h : (star (b 0) * (c 0 - b 0)).im < 0) {y : ℝ} (hy : 0 < y) (i : Fin 1) :
    0 < (star (invCurve b c y i - 0) * deriv (invCurve b c) y i).im := by
  rw [im_star_mul_deriv_invCurve h.ne]
  have hβ := Complex.normSq_pos.2 (segmentCurve_ne_zero h.ne y)
  exact div_pos (by nlinarith [deriv_coneProfile_pos hy]) (by positivity)

/-- **The inverted arc read in the chart `u` is the flat edge read in the chart `z`.** -/
theorem mapSimplex_pathSimplex_invCurve {T : Type*} [TopologicalSpace T] (E : SphereCharts T)
    {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0) :
    mapSimplex (E.chart 1).symm (E.chart 1).continuousOn_symm
        (pathSimplex (contDiff_invCurve h (k := 0) (by simp)).continuous.continuousOn)
        (by rw [E.target_eq]; exact subset_univ _) =
      edgeSimplex (E.chart 0) (E.target_eq 0) b c := by
  ext t
  have h1 : t 1 ∈ Icc (0 : ℝ) 1 := ⟨stdSimplex_apply_nonneg t 1, by
    linarith [stdSimplex_two_add t, stdSimplex_apply_nonneg t 0]⟩
  simp only [mapSimplex_apply, edgeSimplex]
  change (E.chart 1).symm (clampCurve (invCurve b c) (t 1)) = _
  rw [clampCurve_of_mem _ h1]
  have := E.symm_one_inv (segmentCurve b c (t 1)) (segmentCurve_ne_zero h (t 1))
  exact this

end Inversion

/-! ### The grid chain and its boundary -/

section Grid

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- The data of a grid of `m × m` squares of side `h` with lower left corner `(x₀, y₀)` in the
chart `z`, with an apex in each square. -/
structure GridData where
  /-- The abscissa of the lower left corner. -/
  x₀ : ℝ
  /-- The ordinate of the lower left corner. -/
  y₀ : ℝ
  /-- The side of the small squares. -/
  h : ℝ
  /-- The number of squares along a side. -/
  m : ℕ
  /-- The apex of the square `(a, b)`. -/
  apex : ℕ → ℕ → Fin 1 → ℂ

namespace GridData

variable (G : GridData)

/-- The lattice point `(x₀ + a h, y₀ + b h)`. -/
def pt (a b : ℕ) : Fin 1 → ℂ := fun _ ↦ ⟨G.x₀ + a * G.h, G.y₀ + b * G.h⟩

/-- The corners of the square `(a, b)`, counterclockwise from the lower left one. -/
def corners (a b : ℕ) : Fin 4 → Fin 1 → ℂ :=
  ![G.pt a b, G.pt (a + 1) b, G.pt (a + 1) (b + 1), G.pt a (b + 1)]

end GridData

/-- The flat edge `u → v` in the chart `z`, as a chain. -/
abbrev edgeChain (u v : Fin 1 → ℂ) : Chain ℂ T 1 :=
  single (edgeSimplex (E.chart 0) (E.target_eq 0) u v) 1

/-- The correction chain of the pair `u, v`, of Jacobian zero, whose boundary is the edge `u → v`
plus the edge `v → u`. -/
def corrChain (u v : Fin 1 → ℂ) : Chain ℂ T 2 :=
  single (flatConeSimplex (E.chart 0) (E.target_eq 0) u v u) 1 +
    single (pointSimplex 2 ((E.chart 0).symm u)) 1

/-- The boundary of the correction chain of `u, v` is the edge `u → v` plus the edge `v → u`. -/
theorem bd_corrChain (u v : Fin 1 → ℂ) :
    bd ℂ 1 (corrChain E u v) = edgeChain E u v + edgeChain E v u :=
  (single_edgeSimplex_add_edgeSimplex _ _ u v).symm

/-- The fan of the square `(a, b)`: the flat cones from its apex over its four edges. -/
def cellFan (G : GridData) (a b : ℕ) : Chain ℂ T 2 :=
  ∑ j : Fin 4, single (flatConeSimplex (E.chart 0) (E.target_eq 0) (G.apex a b)
    (G.corners a b j) (G.corners a b (finRotate 4 j))) 1

/-- The boundary of the fan of the square `(a, b)` is the sum of its four edges, run
counterclockwise. -/
theorem bd_cellFan (G : GridData) (a b : ℕ) :
    bd ℂ 1 (cellFan E G a b) = edgeChain E (G.pt a b) (G.pt (a + 1) b) +
      edgeChain E (G.pt (a + 1) b) (G.pt (a + 1) (b + 1)) +
      edgeChain E (G.pt (a + 1) (b + 1)) (G.pt a (b + 1)) +
      edgeChain E (G.pt a (b + 1)) (G.pt a b) := by
  have := bd_sum_single_mapSimplex_coneSimplex_segmentCurve (R := ℂ) (E.chart 0) (G.apex a b)
    (G.corners a b) (fun j ↦ by rw [E.target_eq 0]; exact subset_univ _)
    (fun j ↦ by rw [E.target_eq 0]; exact subset_univ _)
  rw [cellFan]
  refine this.trans ?_
  rw [Fin.sum_univ_four]
  rfl

/-- The chain of the square `(a, b)`: its fan, minus the corrections of its top and left
edges. -/
def cellChain (G : GridData) (a b : ℕ) : Chain ℂ T 2 :=
  cellFan E G a b - corrChain E (G.pt a (b + 1)) (G.pt (a + 1) (b + 1)) -
    corrChain E (G.pt a b) (G.pt a (b + 1))

/-- The boundary of the chain of the square `(a, b)`: its bottom and right edges minus its top and
left edges, each run left to right or bottom to top. -/
theorem bd_cellChain (G : GridData) (a b : ℕ) :
    bd ℂ 1 (cellChain E G a b) =
      edgeChain E (G.pt a b) (G.pt (a + 1) b) +
          edgeChain E (G.pt (a + 1) b) (G.pt (a + 1) (b + 1)) -
        edgeChain E (G.pt a (b + 1)) (G.pt (a + 1) (b + 1)) -
        edgeChain E (G.pt a b) (G.pt a (b + 1)) := by
  rw [cellChain, map_sub, map_sub, bd_cellFan, bd_corrChain, bd_corrChain]
  abel

/-- The chain of the grid of squares. -/
def gridChain (G : GridData) : Chain ℂ T 2 :=
  ∑ a ∈ Finset.range G.m, ∑ b ∈ Finset.range G.m, cellChain E G a b

/-- The boundary of the grid chain: the bottom edges of the big square minus its top edges, plus
its right edges minus its left edges, each run left to right or bottom to top. -/
theorem bd_gridChain (G : GridData) :
    bd ℂ 1 (gridChain E G) =
      ∑ a ∈ Finset.range G.m, (edgeChain E (G.pt a 0) (G.pt (a + 1) 0) -
        edgeChain E (G.pt a G.m) (G.pt (a + 1) G.m)) +
      ∑ b ∈ Finset.range G.m, (edgeChain E (G.pt G.m b) (G.pt G.m (b + 1)) -
        edgeChain E (G.pt 0 b) (G.pt 0 (b + 1))) := by
  rw [gridChain, map_sum]
  simp only [map_sum, bd_cellChain]
  have hH : ∀ a, ∑ b ∈ Finset.range G.m, (edgeChain E (G.pt a b) (G.pt (a + 1) b) -
      edgeChain E (G.pt a (b + 1)) (G.pt (a + 1) (b + 1))) =
      edgeChain E (G.pt a 0) (G.pt (a + 1) 0) - edgeChain E (G.pt a G.m) (G.pt (a + 1) G.m) := by
    intro a
    have := Finset.sum_range_sub (fun b ↦ edgeChain E (G.pt a b) (G.pt (a + 1) b)) G.m
    rw [← neg_sub, ← this, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ ↦ by abel
  have hV : ∀ b, ∑ a ∈ Finset.range G.m, (edgeChain E (G.pt (a + 1) b) (G.pt (a + 1) (b + 1)) -
      edgeChain E (G.pt a b) (G.pt a (b + 1))) =
      edgeChain E (G.pt G.m b) (G.pt G.m (b + 1)) - edgeChain E (G.pt 0 b) (G.pt 0 (b + 1)) :=
    fun b ↦ Finset.sum_range_sub (fun a ↦ edgeChain E (G.pt a b) (G.pt a (b + 1))) G.m
  have hsplit : ∀ a b, edgeChain E (G.pt a b) (G.pt (a + 1) b) +
      edgeChain E (G.pt (a + 1) b) (G.pt (a + 1) (b + 1)) -
      edgeChain E (G.pt a (b + 1)) (G.pt (a + 1) (b + 1)) -
        edgeChain E (G.pt a b) (G.pt a (b + 1)) =
      (edgeChain E (G.pt a b) (G.pt (a + 1) b) -
        edgeChain E (G.pt a (b + 1)) (G.pt (a + 1) (b + 1))) +
      (edgeChain E (G.pt (a + 1) b) (G.pt (a + 1) (b + 1)) -
        edgeChain E (G.pt a b) (G.pt a (b + 1))) := fun a b ↦ by abel
  simp only [hsplit, Finset.sum_add_distrib, hH]
  rw [Finset.sum_comm (f := fun a b ↦ edgeChain E (G.pt (a + 1) b) (G.pt (a + 1) (b + 1)) -
    edgeChain E (G.pt a b) (G.pt a (b + 1)))]
  simp only [hV]

open Classical in
/-- The flat cone, in the chart `u`, from `0` over the inverted flat segment `b → c`, when `0` is
not on the line of `b → c` (and a constant triangle otherwise). -/
def infConeSimplex (b c : Fin 1 → ℂ) : Simplex T 2 :=
  if h : (star (b 0) * (c 0 - b 0)).im ≠ 0 then
    mapSimplex (E.chart 1).symm (E.chart 1).continuousOn_symm
      (coneSimplex continuous_coneProfile coneProfile_zero 0
        (contDiff_invCurve h (k := 0) (by simp)).continuous.continuousOn)
      (by rw [E.target_eq 1]; exact subset_univ _)
  else pointSimplex 2 ((E.chart 1).symm 0)

/-- The radial edge, in the chart `u`, from `0` to `1 / w`. -/
abbrev infRadialChain (w : Fin 1 → ℂ) : Chain ℂ T 1 :=
  single (mapSimplex (E.chart 1).symm (E.chart 1).continuousOn_symm
    (radialSimplex continuous_coneProfile 0 (fun _ ↦ (w 0)⁻¹))
    (by rw [E.target_eq 1]; exact subset_univ _)) 1

/-- The boundary of a flat cone around `∞`: the edge `b → c` in the chart `z`, minus the radial
edge to `1 / c`, plus the radial edge to `1 / b`, when `0` is not on the line of `b → c`. -/
theorem bd_infConeSimplex {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0) :
    bd ℂ 1 (single (infConeSimplex E b c) 1) =
      edgeChain E b c - infRadialChain E c + infRadialChain E b := by
  rw [infConeSimplex, dif_pos h, bd_single_two]
  simp only [mapSimplex_comp_face]
  rw [mapSimplex_congr _ _ (coneSimplex_comp_face_zero continuous_coneProfile coneProfile_zero
      coneProfile_one 0 _) _ (by rw [E.target_eq 1]; exact subset_univ _),
    mapSimplex_congr _ _ (coneSimplex_comp_face_one continuous_coneProfile coneProfile_zero 0 _) _
      (by rw [E.target_eq 1]; exact subset_univ _),
    mapSimplex_congr _ _ (coneSimplex_comp_face_two continuous_coneProfile coneProfile_zero 0 _) _
      (by rw [E.target_eq 1]; exact subset_univ _), mapSimplex_pathSimplex_invCurve E h]
  have h1 : invCurve b c 1 = fun _ ↦ (c 0)⁻¹ := funext fun _ ↦ by simp [invCurve]
  have h0 : invCurve b c 0 = fun _ ↦ (b 0)⁻¹ := funext fun _ ↦ by simp [invCurve]
  simp only [h1, h0]

namespace GridData

variable (G : GridData)

/-- The grid encloses the origin: `h > 0` and `x₀ < 0 < x₀ + m h`, `y₀ < 0 < y₀ + m h`. -/
structure Encloses : Prop where
  /-- The side of the squares is positive. -/
  h_pos : 0 < G.h
  /-- The left side of the big square lies left of the origin. -/
  x₀_neg : G.x₀ < 0
  /-- The bottom side of the big square lies below the origin. -/
  y₀_neg : G.y₀ < 0
  /-- The right side of the big square lies right of the origin. -/
  x_pos : 0 < G.x₀ + G.m * G.h
  /-- The top side of the big square lies above the origin. -/
  y_pos : 0 < G.y₀ + G.m * G.h

/-- The value of `Im(conj p (q - p))` for the lattice points `p = pt i j` and `q = pt i' j'`. -/
theorem im_star_pt_mul_sub (i j i' j' : ℕ) :
    (star (G.pt i j 0) * (G.pt i' j' 0 - G.pt i j 0)).im =
      (G.x₀ + i * G.h) * ((j' - j) * G.h) - (G.y₀ + j * G.h) * ((i' - i) * G.h) := by
  simp only [pt, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  ring

variable {G}

/-- For a grid enclosing the origin, the origin lies strictly on the right of each bottom edge of
the big square, run right to left. -/
theorem Encloses.bottom (hG : G.Encloses) (a : ℕ) :
    (star (G.pt (a + 1) 0 0) * (G.pt a 0 0 - G.pt (a + 1) 0 0)).im < 0 := by
  rw [im_star_pt_mul_sub]; push_cast; nlinarith [hG.h_pos, hG.y₀_neg]

/-- For a grid enclosing the origin, the origin lies strictly on the right of each top edge of the
big square, run left to right. -/
theorem Encloses.top (hG : G.Encloses) (a : ℕ) :
    (star (G.pt a G.m 0) * (G.pt (a + 1) G.m 0 - G.pt a G.m 0)).im < 0 := by
  rw [im_star_pt_mul_sub]; push_cast; nlinarith [hG.h_pos, hG.y_pos]

/-- For a grid enclosing the origin, the origin lies strictly on the right of each right edge of
the big square, run top to bottom. -/
theorem Encloses.right (hG : G.Encloses) (b : ℕ) :
    (star (G.pt G.m (b + 1) 0) * (G.pt G.m b 0 - G.pt G.m (b + 1) 0)).im < 0 := by
  rw [im_star_pt_mul_sub]; push_cast; nlinarith [hG.h_pos, hG.x_pos]

/-- For a grid enclosing the origin, the origin lies strictly on the right of each left edge of the
big square, run bottom to top. -/
theorem Encloses.left (hG : G.Encloses) (b : ℕ) :
    (star (G.pt 0 b 0) * (G.pt 0 (b + 1) 0 - G.pt 0 b 0)).im < 0 := by
  rw [im_star_pt_mul_sub]; push_cast; nlinarith [hG.h_pos, hG.x₀_neg]

end GridData

/-- The cell around `∞`: the flat cones, in the chart `u`, from `0` over the inverted edges of the
boundary of the grid, run clockwise. -/
def infChain (G : GridData) : Chain ℂ T 2 :=
  ∑ a ∈ Finset.range G.m, (single (infConeSimplex E (G.pt (a + 1) 0) (G.pt a 0)) 1 +
    single (infConeSimplex E (G.pt a G.m) (G.pt (a + 1) G.m)) 1) +
  ∑ b ∈ Finset.range G.m, (single (infConeSimplex E (G.pt G.m (b + 1)) (G.pt G.m b)) 1 +
    single (infConeSimplex E (G.pt 0 b) (G.pt 0 (b + 1))) 1)

/-- **The flat cone cycle of the sphere**: the grid, the cell around `∞`, and the corrections of
the bottom and right edges of the grid. -/
def sphereChain (G : GridData) : Chain ℂ T 2 :=
  gridChain E G + infChain E G - ∑ a ∈ Finset.range G.m, corrChain E (G.pt a 0) (G.pt (a + 1) 0) -
    ∑ b ∈ Finset.range G.m, corrChain E (G.pt G.m b) (G.pt G.m (b + 1))

/-- **The flat cone chain of the sphere is a cycle.** -/
theorem bd_sphereChain {G : GridData} (hG : G.Encloses) : bd ℂ 1 (sphereChain E G) = 0 := by
  have hb := fun a ↦ bd_infConeSimplex E (hG.bottom a).ne
  have ht := fun a ↦ bd_infConeSimplex E (hG.top a).ne
  have hr := fun b ↦ bd_infConeSimplex E (hG.right b).ne
  have hl := fun b ↦ bd_infConeSimplex E (hG.left b).ne
  rw [sphereChain, map_sub, map_sub, map_add, bd_gridChain, infChain, map_add, map_sum, map_sum,
    map_sum, map_sum]
  simp only [map_add, hb, ht, hr, hl, bd_corrChain]
  set R := infRadialChain E
  have hA : ∑ a ∈ Finset.range G.m, ((R (G.pt (a + 1) 0) - R (G.pt a 0)) +
      (R (G.pt a G.m) - R (G.pt (a + 1) G.m))) =
      (R (G.pt G.m 0) - R (G.pt 0 0)) + (R (G.pt 0 G.m) - R (G.pt G.m G.m)) := by
    rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun a ↦ R (G.pt a 0)),
      ← neg_sub (R (G.pt G.m G.m)), ← Finset.sum_range_sub (fun a ↦ R (G.pt a G.m)),
      ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun _ _ ↦ by abel
  have hB : ∑ b ∈ Finset.range G.m, ((R (G.pt G.m (b + 1)) - R (G.pt G.m b)) +
      (R (G.pt 0 b) - R (G.pt 0 (b + 1)))) =
      (R (G.pt G.m G.m) - R (G.pt G.m 0)) + (R (G.pt 0 0) - R (G.pt 0 G.m)) := by
    rw [Finset.sum_add_distrib, Finset.sum_range_sub (fun b ↦ R (G.pt G.m b)),
      ← neg_sub (R (G.pt 0 G.m)), ← Finset.sum_range_sub (fun b ↦ R (G.pt 0 b)),
      ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun _ _ ↦ by abel
  have hsum : ∀ {ι : Type} (s : Finset ι) (f g k : ι → Chain ℂ T 1),
      ∑ i ∈ s, f i + ∑ i ∈ s, g i - ∑ i ∈ s, k i = ∑ i ∈ s, (f i + g i - k i) := by
    intro ι s f g k
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  rw [show ∀ x y z w u v : Chain ℂ T 1, x + y + (z + w) - u - v = (x + z - u) + (y + w - v) from
    fun _ _ _ _ _ _ ↦ by abel, hsum, hsum]
  conv_lhs =>
    arg 1
    rw [Finset.sum_congr rfl (fun a _ ↦ show _ = (R (G.pt (a + 1) 0) - R (G.pt a 0)) +
      (R (G.pt a G.m) - R (G.pt (a + 1) G.m)) by abel)]
  conv_lhs =>
    arg 2
    rw [Finset.sum_congr rfl (fun b _ ↦ show _ = (R (G.pt G.m (b + 1)) - R (G.pt G.m b)) +
      (R (G.pt 0 b) - R (G.pt 0 (b + 1))) by abel)]
  rw [hA, hB]
  abel

end Grid

/-! ### The two kinds of triangles and their readings -/

section Forms

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- The triangles of positive orientation: flat cones in the chart `z` from a point on the left
of their base, and flat cones in the chart `u` from `0` over inverted segments on whose right `0`
lies. -/
def PosForm (σ : Simplex T 2) : Prop :=
  (∃ P b c : Fin 1 → ℂ, 0 < (star (b 0 - P 0) * (c 0 - b 0)).im ∧
    σ = flatConeSimplex (E.chart 0) (E.target_eq 0) P b c) ∨
  ∃ b c : Fin 1 → ℂ, (star (b 0) * (c 0 - b 0)).im < 0 ∧ σ = infConeSimplex E b c

/-- The triangles of Jacobian zero: degenerate flat cones in the chart `z` and constants. -/
def NegForm (σ : Simplex T 2) : Prop :=
  (∃ u v : Fin 1 → ℂ, σ = flatConeSimplex (E.chart 0) (E.target_eq 0) u v u) ∨
  ∃ x : T, σ = pointSimplex 2 x

/-- On the unit square, the flat cone from `P` over `b → c` is, through the collapse, `e⁻¹` of the
cone map from `P` over the flat segment `b → c`. -/
theorem flatConeSimplex_squareCollapse (e : OpenPartialHomeomorph T (Fin 1 → ℂ))
    (he : e.target = univ) (P b c : Fin 1 → ℂ) {p : ℝ × ℝ} (hp : p ∈ unitSquare) :
    flatConeSimplex e he P b c (squareCollapse p) =
      e.symm (CurveCupPositivity.coneMap coneProfile P (segmentCurve b c) p) := by
  rw [flatConeSimplex, mapSimplex_apply, coneSimplex_squareCollapse _ _ _ _ hp]

/-- The corner `(0, 0)` lies in the unit square. -/
theorem mem_unitSquare_zero_zero : ((0 : ℝ), (0 : ℝ)) ∈ unitSquare :=
  ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩

/-- The corner `(1, 0)` lies in the unit square. -/
theorem mem_unitSquare_one_zero : ((1 : ℝ), (0 : ℝ)) ∈ unitSquare :=
  ⟨⟨zero_le_one, le_rfl⟩, ⟨le_rfl, zero_le_one⟩⟩

/-- The corner `(1, 1)` lies in the unit square. -/
theorem mem_unitSquare_one_one : ((1 : ℝ), (1 : ℝ)) ∈ unitSquare :=
  ⟨⟨zero_le_one, le_rfl⟩, ⟨zero_le_one, le_rfl⟩⟩

/-- The vertices of the flat cone from `P` over `b → c`: the collapse sends `(0, 0)`, `(1, 0)` and
`(1, 1)` to `e⁻¹ P`, `e⁻¹ b` and `e⁻¹ c`. -/
theorem flatConeSimplex_vertex (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (he : e.target = univ)
    (P b c : Fin 1 → ℂ) :
    flatConeSimplex e he P b c (squareCollapse (0, 0)) = e.symm P ∧
    flatConeSimplex e he P b c (squareCollapse (1, 0)) = e.symm b ∧
    flatConeSimplex e he P b c (squareCollapse (1, 1)) = e.symm c := by
  refine ⟨?_, ?_, ?_⟩ <;>
  rw [flatConeSimplex_squareCollapse _ _ _ _ _ (by first
    | exact mem_unitSquare_zero_zero | exact mem_unitSquare_one_zero
    | exact mem_unitSquare_one_one)]
  <;> simp [CurveCupPositivity.coneMap]

/-- The vertices of the flat cone around `∞` over the inverted segment `b → c`: the point at `∞`
and the points of `z`-coordinates `b` and `c`, when `0` is not on the line of `b → c`. -/
theorem infConeSimplex_vertex {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0) :
    infConeSimplex E b c (squareCollapse (0, 0)) = (E.chart 1).symm 0 ∧
    infConeSimplex E b c (squareCollapse (1, 0)) = (E.chart 0).symm b ∧
    infConeSimplex E b c (squareCollapse (1, 1)) = (E.chart 0).symm c := by
  have key : ∀ p ∈ unitSquare, infConeSimplex E b c (squareCollapse p) =
      (E.chart 1).symm (CurveCupPositivity.coneMap coneProfile 0 (invCurve b c) p) := fun p hp ↦ by
    rw [infConeSimplex, dif_pos h, mapSimplex_apply, coneSimplex_squareCollapse _ _ _ _ hp]
  have hb : (b 0) ≠ 0 := by
    intro h0; apply h; simp [h0]
  have hc : (c 0) ≠ 0 := by
    intro h0; apply h; rw [h0, zero_sub, mul_neg, Complex.neg_im]
    simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [key _ mem_unitSquare_zero_zero]; simp [CurveCupPositivity.coneMap]
  · rw [key _ mem_unitSquare_one_zero]
    simp only [CurveCupPositivity.coneMap, coneProfile_one, one_smul, zero_add, sub_zero]
    rw [show invCurve b c 0 = fun _ ↦ (b 0)⁻¹ from funext fun _ ↦ by simp [invCurve]]
    exact E.symm_one_inv b hb
  · rw [key _ mem_unitSquare_one_one]
    simp only [CurveCupPositivity.coneMap, coneProfile_one, one_smul, zero_add, sub_zero]
    rw [show invCurve b c 1 = fun _ ↦ (c 0)⁻¹ from funext fun _ ↦ by simp [invCurve]]
    exact E.symm_one_inv c hc

/-- Each inverse chart of sphere charts is injective. -/
theorem symm_injective (k : Fin 2) : Function.Injective (E.chart k).symm := fun u v huv ↦ by
  have hu : u ∈ (E.chart k).target := by rw [E.target_eq]; exact mem_univ _
  have hv : v ∈ (E.chart k).target := by rw [E.target_eq]; exact mem_univ _
  rw [← (E.chart k).right_inv hu, ← (E.chart k).right_inv hv, huv]

/-- Each inverse chart of sphere charts takes values in the domain of the chart. -/
theorem symm_mem_source (k : Fin 2) (v : Fin 1 → ℂ) : (E.chart k).symm v ∈ (E.chart k).source :=
  (E.chart k).map_target (by rw [E.target_eq]; exact mem_univ _)

/-- **The positive triangles are not of Jacobian zero.** -/
theorem not_negForm_of_posForm {σ : Simplex T 2} (hσ : PosForm E σ) : ¬ NegForm E σ := by
  rintro (⟨u, v, rfl⟩ | ⟨x, rfl⟩)
  · rcases hσ with ⟨P, b, c, hpos, h⟩ | ⟨b, c, hneg, h⟩
    · have h0 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (0, 0))) h
      have h2 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (1, 1))) h
      simp only [(flatConeSimplex_vertex _ _ _ _ _).1, (flatConeSimplex_vertex _ _ _ _ _).2.2]
        at h0 h2
      have hP : P = c := symm_injective E 0 (h0.symm.trans h2)
      subst hP
      have : (star (b 0 - P 0) * (P 0 - b 0)).im = 0 := by
        have := im_star_sub_mul_sub_rev_eq_zero P b 0
        simpa using this
      linarith
    · have h0 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (0, 0))) h
      simp only [(flatConeSimplex_vertex _ _ _ _ _).1, (infConeSimplex_vertex E hneg.ne).1] at h0
      exact E.symm_zero_notMem (h0 ▸ symm_mem_source E 0 u)
  · rcases hσ with ⟨P, b, c, hpos, h⟩ | ⟨b, c, hneg, h⟩
    · have h1 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (1, 0))) h
      have h2 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (1, 1))) h
      simp only [(flatConeSimplex_vertex _ _ _ _ _).2.1, (flatConeSimplex_vertex _ _ _ _ _).2.2]
        at h1 h2
      have hbc : b = c := symm_injective E 0 (h1.symm.trans h2)
      subst hbc
      simp at hpos
    · have h1 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (1, 0))) h
      have h2 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (1, 1))) h
      simp only [(infConeSimplex_vertex E hneg.ne).2.1, (infConeSimplex_vertex E hneg.ne).2.2]
        at h1 h2
      have hbc : b = c := symm_injective E 0 (h1.symm.trans h2)
      subst hbc
      simp at hneg

/-- **Readings of the positive triangles.** A positive triangle is, through the collapse, the
read in one of the two charts of a flat cone map `CurveCupPositivity.coneMap coneProfile P γ`,
`C²` on an open neighbourhood of the square, with nonnegative Jacobian there and positive
Jacobian on the open square, and with apex `σ(s(0, 0)) = e⁻¹ P`. -/
theorem exists_reading_of_posForm {σ : Simplex T 2} (hσ : PosForm E σ) :
    ∃ (k : Fin 2) (P : Fin 1 → ℂ) (γ : ℝ → Fin 1 → ℂ) (U : Set (ℝ × ℝ)), ContDiff ℝ 2 γ ∧
      IsOpen U ∧ unitSquare ⊆ U ∧ ContDiffOn ℝ 2 (CurveCupPositivity.coneMap coneProfile P γ) U ∧
      (∀ p ∈ unitSquare, σ (squareCollapse p) =
        (E.chart k).symm (CurveCupPositivity.coneMap coneProfile P γ p)) ∧
      (∀ p ∈ U, ∀ i,
        0 ≤ FundamentalChartCycle.chartJacobian (CurveCupPositivity.coneMap coneProfile P γ) p i) ∧
      (∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∀ i,
        0 < FundamentalChartCycle.chartJacobian
          (CurveCupPositivity.coneMap coneProfile P γ) p i) := by
  rcases hσ with ⟨P, b, c, hpos, rfl⟩ | ⟨b, c, hneg, rfl⟩
  · obtain ⟨-, U, hUo, hsU, hg, -, -, hJ⟩ := exists_reading_coneSimplex_segmentCurve (E.chart 0)
      (P := P) (b := b) (c := c) (fun i ↦ by rw [Subsingleton.elim i 0]; exact hpos.le)
      (fun _ _ ↦ by rw [E.target_eq 0]; exact mem_univ _)
    refine ⟨0, P, segmentCurve b c, U, contDiff_segmentCurve b c (by simp), hUo, hsU, hg,
      fun p hp ↦ flatConeSimplex_squareCollapse _ _ _ _ _ hp, hJ, fun p hp i ↦ ?_⟩
    obtain ⟨x, y⟩ := p
    exact im_star_fderiv_coneMap_segmentCurve_pos hp.1.1 hp.2.1 i
      (by rw [Subsingleton.elim i 0]; exact hpos)
  · have hγ : ContDiffOn ℝ 2 (invCurve b c) univ := (contDiff_invCurve hneg.ne (by simp)).contDiffOn
    obtain ⟨hσr, U, hUo, hsU, hg, -, hread, hJ⟩ := exists_reading_coneSimplex (E.chart 1) 0
      isOpen_univ (subset_univ _) hγ
      (fun y _ i ↦ im_star_mul_deriv_invCurve_nonneg hneg y i)
      (fun _ _ ↦ by rw [E.target_eq 1]; exact mem_univ _)
    refine ⟨1, 0, invCurve b c, U, contDiff_invCurve hneg.ne (by simp), hUo, hsU, hg,
      fun p hp ↦ ?_, hJ, fun p hp i ↦ ?_⟩
    · rw [infConeSimplex, dif_pos hneg.ne]
      exact hread p hp
    · obtain ⟨x, y⟩ := p
      exact im_star_fderiv_coneMap_pos hp.1.1
        ((contDiff_invCurve hneg.ne (k := 1) (by simp)).differentiable (by simp) y) i
        (im_star_mul_deriv_invCurve_pos hneg hp.2.1 i)

/-- **Readings of the triangles of Jacobian zero.** -/
theorem exists_reading_of_negForm {σ : Simplex T 2} (hσ : NegForm E σ) :
    ∃ (k : Fin 2) (g : ℝ × ℝ → Fin 1 → ℂ) (U : Set (ℝ × ℝ)),
      IsOpen U ∧ unitSquare ⊆ U ∧ ContDiffOn ℝ 2 g U ∧
      (∀ p ∈ unitSquare, σ (squareCollapse p) = (E.chart k).symm (g p)) ∧
      ∀ p ∈ U, ∀ i, FundamentalChartCycle.chartJacobian g p i = 0 := by
  rcases hσ with ⟨u, v, rfl⟩ | ⟨x, rfl⟩
  · refine ⟨0, CurveCupPositivity.coneMap coneProfile u (segmentCurve v u), univ, isOpen_univ,
      subset_univ _,
      (contDiffOn_coneMap (contDiff_coneProfile (by simp))
        (contDiff_segmentCurve v u (by simp)).contDiffOn).mono fun p _ ↦ ⟨mem_univ _, mem_univ _⟩,
      fun p hp ↦ flatConeSimplex_squareCollapse _ _ _ _ _ hp, fun p _ i ↦ ?_⟩
    obtain ⟨x, y⟩ := p
    rw [FundamentalChartCycle.chartJacobian, im_star_fderiv_coneMap (differentiable_coneProfile x)
      ((contDiff_segmentCurve v u (k := 1) (by simp)).differentiable (by simp) y),
      im_star_sub_mul_deriv_segmentCurve, im_star_sub_mul_sub_rev_eq_zero]
    simp
  · have hx : x ∈ (E.chart 0).source ∪ (E.chart 1).source := by
      rw [E.source_union]; exact mem_univ x
    obtain ⟨k, hk⟩ : ∃ k : Fin 2, x ∈ (E.chart k).source := hx.elim (⟨0, ·⟩) (⟨1, ·⟩)
    refine ⟨k, fun _ ↦ E.chart k x, univ, isOpen_univ, subset_univ _, contDiffOn_const,
      fun p _ ↦ ((E.chart k).left_inv hk).symm, fun p _ i ↦ ?_⟩
    simp [FundamentalChartCycle.chartJacobian]

end Forms

/-! ### The terms of the sphere chain -/

section Terms

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

namespace GridData

variable (G : GridData)

/-- The open square `(a, b)` of the grid, in the coordinate `z`. -/
def openCell (a b : ℕ) : Set (Fin 1 → ℂ) :=
  {v | G.x₀ + a * G.h < (v 0).re ∧ (v 0).re < G.x₀ + (a + 1) * G.h ∧
    G.y₀ + b * G.h < (v 0).im ∧ (v 0).im < G.y₀ + (b + 1) * G.h}

/-- A good grid: it encloses the origin, and each of its squares contains its apex. -/
structure IsGood : Prop where
  /-- The grid encloses the origin. -/
  encloses : G.Encloses
  /-- Each square of the grid contains its apex in its interior. -/
  apex_mem : ∀ a < G.m, ∀ b < G.m, G.apex a b ∈ G.openCell a b

/-- The corners of the square `(a, b)` are the corners of the rectangle
`[x₀ + a h, x₀ + (a + 1) h] × [y₀ + b h, y₀ + (b + 1) h]`. -/
theorem corners_apply (a b : ℕ) (j : Fin 4) :
    G.corners a b j 0 = rectangleCorners (G.x₀ + a * G.h) (G.x₀ + (a + 1) * G.h)
      (G.y₀ + b * G.h) (G.y₀ + (b + 1) * G.h) j := by
  fin_cases j <;> simp [corners, pt, rectangleCorners] <;> push_cast <;> ring

variable {G}

/-- In a good grid, the apex of each square lies strictly on the left of each of its edges, run
counterclockwise. -/
theorem IsGood.left_pos (hG : G.IsGood) {a b : ℕ} (ha : a < G.m) (hb : b < G.m) (j : Fin 4) :
    0 < (star (G.corners a b j 0 - G.apex a b 0) *
      (G.corners a b (finRotate 4 j) 0 - G.corners a b j 0)).im := by
  obtain ⟨h1, h2, h3, h4⟩ := hG.apex_mem a ha b hb
  rw [corners_apply, corners_apply]
  exact im_star_sub_mul_sub_rectangleCorners_pos ⟨h1, h2⟩ ⟨h3, h4⟩ j

end GridData

/-- The positive part of the sphere chain: the fans of the squares and the cell around `∞`. -/
def posChain (G : GridData) : Chain ℂ T 2 :=
  ∑ a ∈ Finset.range G.m, ∑ b ∈ Finset.range G.m, cellFan E G a b + infChain E G

/-- The corrections of the sphere chain, of Jacobian zero. -/
def negChain (G : GridData) : Chain ℂ T 2 :=
  ∑ a ∈ Finset.range G.m, ∑ b ∈ Finset.range G.m,
      (corrChain E (G.pt a (b + 1)) (G.pt (a + 1) (b + 1)) +
        corrChain E (G.pt a b) (G.pt a (b + 1))) +
    ∑ a ∈ Finset.range G.m, corrChain E (G.pt a 0) (G.pt (a + 1) 0) +
    ∑ b ∈ Finset.range G.m, corrChain E (G.pt G.m b) (G.pt G.m (b + 1))

/-- The sphere chain is its positive part minus its corrections. -/
theorem sphereChain_eq (G : GridData) : sphereChain E G = posChain E G - negChain E G := by
  simp only [sphereChain, gridChain, cellChain, posChain, negChain, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  abel

/-- The chains with natural coefficients. -/
def natChains : AddSubmonoid (Chain ℂ T 2) where
  carrier := {f | ∀ σ, ∃ n : ℕ, f σ = n}
  zero_mem' := fun _ ↦ ⟨0, by simp⟩
  add_mem' := fun {f g} hf hg σ ↦ by
    obtain ⟨n, hn⟩ := hf σ
    obtain ⟨k, hk⟩ := hg σ
    exact ⟨n + k, by rw [Finsupp.add_apply, hn, hk]; push_cast; rfl⟩

/-- A simplex with coefficient `1` is a chain with natural coefficients. -/
theorem single_mem_natChains (τ : Simplex T 2) : single τ (1 : ℂ) ∈ natChains (T := T) :=
  fun σ ↦ by
    classical
    by_cases h : τ = σ
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [Finsupp.single_apply, h]⟩

/-- The correction chain of `u, v` has natural coefficients. -/
theorem corrChain_mem_natChains (u v : Fin 1 → ℂ) : corrChain E u v ∈ natChains (T := T) :=
  add_mem (single_mem_natChains _) (single_mem_natChains _)

/-- The fan of a square has natural coefficients. -/
theorem cellFan_mem_natChains (G : GridData) (a b : ℕ) : cellFan E G a b ∈ natChains (T := T) :=
  AddSubmonoid.sum_mem _ fun _ _ ↦ single_mem_natChains _

/-- The positive part of the sphere chain has natural coefficients. -/
theorem posChain_mem_natChains (G : GridData) : posChain E G ∈ natChains (T := T) := by
  refine add_mem (AddSubmonoid.sum_mem _ fun a _ ↦ AddSubmonoid.sum_mem _ fun b _ ↦
    cellFan_mem_natChains E G a b) ?_
  refine add_mem (AddSubmonoid.sum_mem _ fun a _ ↦ add_mem (single_mem_natChains _)
    (single_mem_natChains _)) (AddSubmonoid.sum_mem _ fun b _ ↦
      add_mem (single_mem_natChains _) (single_mem_natChains _))

/-- The corrections of the sphere chain have natural coefficients. -/
theorem negChain_mem_natChains (G : GridData) : negChain E G ∈ natChains (T := T) :=
  add_mem (add_mem (AddSubmonoid.sum_mem _ fun _ _ ↦ AddSubmonoid.sum_mem _ fun _ _ ↦
    add_mem (corrChain_mem_natChains E _ _) (corrChain_mem_natChains E _ _))
    (AddSubmonoid.sum_mem _ fun _ _ ↦ corrChain_mem_natChains E _ _))
    (AddSubmonoid.sum_mem _ fun _ _ ↦ corrChain_mem_natChains E _ _)

/-- The correction chain of `u, v` is supported on triangles of Jacobian zero. -/
theorem corrChain_mem_supported (u v : Fin 1 → ℂ) :
    corrChain E u v ∈ Finsupp.supported ℂ ℂ {σ | NegForm E σ} :=
  add_mem (Finsupp.single_mem_supported ℂ _ (Or.inl ⟨u, v, rfl⟩))
    (Finsupp.single_mem_supported ℂ _ (Or.inr ⟨_, rfl⟩))

/-- The corrections of the sphere chain are supported on triangles of Jacobian zero. -/
theorem negChain_mem_supported (G : GridData) :
    negChain E G ∈ Finsupp.supported ℂ ℂ {σ | NegForm E σ} :=
  add_mem (add_mem (Submodule.sum_mem _ fun _ _ ↦ Submodule.sum_mem _ fun _ _ ↦
    add_mem (corrChain_mem_supported E _ _) (corrChain_mem_supported E _ _))
    (Submodule.sum_mem _ fun _ _ ↦ corrChain_mem_supported E _ _))
    (Submodule.sum_mem _ fun _ _ ↦ corrChain_mem_supported E _ _)

/-- For a good grid, the positive part of the sphere chain is supported on triangles of positive
orientation. -/
theorem posChain_mem_supported {G : GridData} (hG : G.IsGood) :
    posChain E G ∈ Finsupp.supported ℂ ℂ {σ | PosForm E σ} := by
  refine add_mem (Submodule.sum_mem _ fun a ha ↦ Submodule.sum_mem _ fun b hb ↦
    Submodule.sum_mem _ fun j _ ↦ Finsupp.single_mem_supported ℂ _
      (Or.inl ⟨_, _, _, hG.left_pos (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) j, rfl⟩)) ?_
  refine add_mem (Submodule.sum_mem _ fun a _ ↦ add_mem
    (Finsupp.single_mem_supported ℂ _ (Or.inr ⟨_, _, hG.encloses.bottom a, rfl⟩))
    (Finsupp.single_mem_supported ℂ _ (Or.inr ⟨_, _, hG.encloses.top a, rfl⟩)))
    (Submodule.sum_mem _ fun b _ ↦ add_mem
      (Finsupp.single_mem_supported ℂ _ (Or.inr ⟨_, _, hG.encloses.right b, rfl⟩))
      (Finsupp.single_mem_supported ℂ _ (Or.inr ⟨_, _, hG.encloses.left b, rfl⟩)))

/-- Every triangle of the sphere chain is positive or of Jacobian zero. -/
theorem posForm_or_negForm {G : GridData} (hG : G.IsGood) {σ : Simplex T 2}
    (hσ : σ ∈ (sphereChain E G).support) : PosForm E σ ∨ NegForm E σ := by
  rw [Finsupp.mem_support_iff, sphereChain_eq, Finsupp.sub_apply] at hσ
  by_contra h
  push Not at h
  have h1 : posChain E G σ = 0 := Finsupp.notMem_support_iff.1 fun hm ↦
    h.1 (posChain_mem_supported E hG hm)
  have h2 : negChain E G σ = 0 := Finsupp.notMem_support_iff.1 fun hm ↦
    h.2 (negChain_mem_supported E G hm)
  exact hσ (by rw [h1, h2, sub_zero])

/-- The coefficients of the sphere chain are real. -/
theorem im_sphereChain_apply (G : GridData) (σ : Simplex T 2) : (sphereChain E G σ).im = 0 := by
  obtain ⟨n, hn⟩ := posChain_mem_natChains E G σ
  obtain ⟨k, hk⟩ := negChain_mem_natChains E G σ
  rw [sphereChain_eq, Finsupp.sub_apply, hn, hk]
  simp

/-- On a positive triangle, the sphere chain has a natural coefficient. -/
theorem sphereChain_apply_of_posForm (G : GridData) {σ : Simplex T 2} (hσ : PosForm E σ) :
    sphereChain E G σ = posChain E G σ := by
  have h2 : negChain E G σ = 0 := Finsupp.notMem_support_iff.1 fun hm ↦
    not_negForm_of_posForm E hσ (negChain_mem_supported E G hm)
  rw [sphereChain_eq, Finsupp.sub_apply, h2, sub_zero]

end Terms

/-! ### Where the triangles of the sphere chain lie -/

section Images

/-- The cone profile is monotone. -/
theorem monotone_coneProfile : Monotone coneProfile :=
  monotone_of_deriv_nonneg differentiable_coneProfile deriv_coneProfile_nonneg

/-- The cone profile is strictly monotone on `[0, ∞)`. -/
theorem strictMonoOn_coneProfile : StrictMonoOn coneProfile (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) continuous_coneProfile.continuousOn
    fun x hx ↦ deriv_coneProfile_pos ?_
  simpa using hx

/-- The cone profile is at most `1` on `(-∞, 1]`. -/
theorem coneProfile_le_one {x : ℝ} (hx : x ≤ 1) : coneProfile x ≤ 1 :=
  coneProfile_one ▸ monotone_coneProfile hx

/-- The cone profile maps `[0, 1]` into `[0, 1]`. -/
theorem coneProfile_mem_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : coneProfile x ∈ Icc (0 : ℝ) 1 :=
  ⟨coneProfile_nonneg x, coneProfile_le_one hx.2⟩

/-- On `[0, ∞)`, the cone profile vanishes only at `0`. -/
theorem coneProfile_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) : coneProfile x = 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ coneProfile_zero⟩
  by_contra hne
  exact (coneProfile_pos (lt_of_le_of_ne hx (Ne.symm hne))).ne' h

/-- Every number in `[0, 1]` is the cone profile of a point of `[0, 1]`. -/
theorem exists_coneProfile_eq {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ∃ x ∈ Icc (0 : ℝ) 1, coneProfile x = r := by
  have := intermediate_value_Icc zero_le_one continuous_coneProfile.continuousOn
  rw [coneProfile_zero, coneProfile_one] at this
  exact this hr

/-- For a point `t` of `Δ²`, `t₁ + t₂ ∈ [0, 1]`. -/
theorem stdSimplex_one_add_two_mem (t : stdSimplex ℝ (Fin 3)) : t 1 + t 2 ∈ Icc (0 : ℝ) 1 :=
  ⟨add_nonneg (stdSimplex_apply_nonneg t 1) (stdSimplex_apply_nonneg t 2), by
    linarith [stdSimplex_three_add t, stdSimplex_apply_nonneg t 0]⟩

/-- A point of `Δ²` with `t₁ + t₂ = 0` is the vertex `s(0, 0)`. -/
theorem eq_squareCollapse_zero_zero_of_add_eq_zero {t : stdSimplex ℝ (Fin 3)}
    (h : t 1 + t 2 = 0) : t = squareCollapse (0, 0) := by
  have h1 : t 1 = 0 := by linarith [stdSimplex_apply_nonneg t 1, stdSimplex_apply_nonneg t 2]
  have h2 : t 2 = 0 := by linarith [stdSimplex_apply_nonneg t 1, stdSimplex_apply_nonneg t 2]
  refine FundamentalChartCycle.stdSimplex_three_ext ?_ ?_
  · rw [h1, squareCollapse_apply_one mem_unitSquare_zero_zero]; simp
  · rw [h2, squareCollapse_apply_two mem_unitSquare_zero_zero]; simp

/-- The vertex `s(0, 0)` of `Δ²` has `t₁ + t₂ = 0`. -/
theorem add_eq_zero_of_eq_squareCollapse_zero_zero {t : stdSimplex ℝ (Fin 3)}
    (h : t = squareCollapse (0, 0)) : t 1 + t 2 = 0 := by
  subst h
  rw [squareCollapse_apply_one mem_unitSquare_zero_zero,
    squareCollapse_apply_two mem_unitSquare_zero_zero]
  simp

variable {T : Type*} [TopologicalSpace T]

/-- The value of a flat cone at a point of `Δ²`. -/
theorem flatConeSimplex_apply (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (he : e.target = univ)
    (P b c : Fin 1 → ℂ) (t : stdSimplex ℝ (Fin 3)) :
    flatConeSimplex e he P b c t = e.symm (P + coneProfile (t 1 + t 2) •
      (b + coneProfile (projIcc (0 : ℝ) 1 zero_le_one (t 2 / (t 1 + t 2))) • (c - b) - P)) :=
  rfl

/-- The value of a cone of the cell around `∞` at a point of `Δ²`. -/
theorem infConeSimplex_apply (E : SphereCharts T) {b c : Fin 1 → ℂ}
    (h : (star (b 0) * (c 0 - b 0)).im ≠ 0) (t : stdSimplex ℝ (Fin 3)) :
    infConeSimplex E b c t = (E.chart 1).symm (coneProfile (t 1 + t 2) •
      invCurve b c (projIcc (0 : ℝ) 1 zero_le_one (t 2 / (t 1 + t 2)))) := by
  rw [infConeSimplex, dif_pos h]
  change (E.chart 1).symm (0 + coneProfile (t 1 + t 2) • (clampCurve (invCurve b c)
    (t 2 / (t 1 + t 2)) - 0)) = _
  rw [zero_add, sub_zero]
  rfl

/-- A convex combination `p + r (q - p)`, `r ∈ [0, 1]`, of two points of an interval lies in it. -/
theorem add_mul_sub_mem_Icc {lo hi p q r : ℝ} (hp : p ∈ Icc lo hi) (hq : q ∈ Icc lo hi)
    (hr : r ∈ Icc (0 : ℝ) 1) : p + r * (q - p) ∈ Icc lo hi :=
  ⟨by nlinarith [hp.1, hq.1, hr.1, hr.2], by nlinarith [hp.2, hq.2, hr.1, hr.2]⟩

namespace GridData

variable (G : GridData)

/-- The closed square `(a, b)` of the grid, in the coordinate `z`. -/
def closedCell (a b : ℕ) : Set (Fin 1 → ℂ) :=
  {v | (v 0).re ∈ Icc (G.x₀ + a * G.h) (G.x₀ + (a + 1) * G.h) ∧
    (v 0).im ∈ Icc (G.y₀ + b * G.h) (G.y₀ + (b + 1) * G.h)}

/-- The grid lines. -/
def gridLines : Set (Fin 1 → ℂ) :=
  {v | (∃ i : ℕ, (v 0).re = G.x₀ + i * G.h) ∨ ∃ j : ℕ, (v 0).im = G.y₀ + j * G.h}

/-- The open big square. -/
def openSquare : Set (Fin 1 → ℂ) :=
  {v | G.x₀ < (v 0).re ∧ (v 0).re < G.x₀ + G.m * G.h ∧
    G.y₀ < (v 0).im ∧ (v 0).im < G.y₀ + G.m * G.h}

/-- The real part of the lattice point `pt a b` is `x₀ + a h`. -/
theorem pt_re (a b : ℕ) : (G.pt a b 0).re = G.x₀ + a * G.h := rfl

/-- The imaginary part of the lattice point `pt a b` is `y₀ + b h`. -/
theorem pt_im (a b : ℕ) : (G.pt a b 0).im = G.y₀ + b * G.h := rfl

variable {G}

/-- For `h > 0`, a point of the open square `(a, b)` lies in the closed square `(a', b')` only if
`(a, b) = (a', b')`. -/
theorem eq_of_mem_openCell_of_mem_closedCell (hh : 0 < G.h) {a b a' b' : ℕ} {v : Fin 1 → ℂ}
    (hv : v ∈ G.openCell a b) (hv' : v ∈ G.closedCell a' b') : a = a' ∧ b = b' := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  obtain ⟨⟨h5, h6⟩, ⟨h7, h8⟩⟩ := hv'
  have ha : (a : ℝ) < a' + 1 := by nlinarith
  have ha' : (a' : ℝ) < a + 1 := by nlinarith
  have hb : (b : ℝ) < b' + 1 := by nlinarith
  have hb' : (b' : ℝ) < b + 1 := by nlinarith
  exact ⟨by exact_mod_cast (show a = a' by
    have := (Nat.cast_lt (α := ℝ)).1 (by exact_mod_cast ha : ((a : ℕ) : ℝ) < ((a' + 1 : ℕ) : ℝ))
    have := (Nat.cast_lt (α := ℝ)).1 (by exact_mod_cast ha' : ((a' : ℕ) : ℝ) < ((a + 1 : ℕ) : ℝ))
    omega), by
    have := (Nat.cast_lt (α := ℝ)).1 (by exact_mod_cast hb : ((b : ℕ) : ℝ) < ((b' + 1 : ℕ) : ℝ))
    have := (Nat.cast_lt (α := ℝ)).1 (by exact_mod_cast hb' : ((b' : ℕ) : ℝ) < ((b + 1 : ℕ) : ℝ))
    omega⟩

/-- For `h > 0`, a point of an open square of the grid lies on no grid line. -/
theorem notMem_gridLines_of_mem_openCell (hh : 0 < G.h) {a b : ℕ} {v : Fin 1 → ℂ}
    (hv : v ∈ G.openCell a b) : v ∉ G.gridLines := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  rintro (⟨i, hi⟩ | ⟨j, hj⟩)
  · rw [hi] at h1 h2
    have : (a : ℝ) < i := by nlinarith
    have : (i : ℝ) < a + 1 := by nlinarith
    have h' : a < i := by exact_mod_cast ‹(a : ℝ) < i›
    have h'' : i < a + 1 := by exact_mod_cast ‹(i : ℝ) < a + 1›
    omega
  · rw [hj] at h3 h4
    have : (b : ℝ) < j := by nlinarith
    have : (j : ℝ) < b + 1 := by nlinarith
    have h' : b < j := by exact_mod_cast ‹(b : ℝ) < j›
    have h'' : j < b + 1 := by exact_mod_cast ‹(j : ℝ) < b + 1›
    omega

/-- For `h > 0`, the open square `(a, b)` with `a, b < m` lies in the open big square. -/
theorem mem_openSquare_of_mem_openCell (hh : 0 < G.h) {a b : ℕ} (ha : a < G.m) (hb : b < G.m)
    {v : Fin 1 → ℂ} (hv : v ∈ G.openCell a b) : v ∈ G.openSquare := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have ha' : (a : ℝ) + 1 ≤ G.m := by exact_mod_cast ha
  have hb' : (b : ℝ) + 1 ≤ G.m := by exact_mod_cast hb
  refine ⟨by nlinarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)], by nlinarith, by
    nlinarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)], by nlinarith⟩

/-- For `h > 0`, the corners of the square `(a, b)` lie in the closed square `(a, b)`. -/
theorem corners_mem_closedCell (hh : 0 < G.h) (a b : ℕ) (j : Fin 4) :
    G.corners a b j ∈ G.closedCell a b := by
  fin_cases j <;> simp only [corners, closedCell, mem_setOf_eq, mem_Icc] <;>
    simp [pt] <;> (try constructor) <;> (try constructor) <;> push_cast <;> nlinarith

end GridData

end Images

section ImagesTerms

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- The point `P + r (b + s (c - b) - P)` of a flat cone, in coordinates. -/
theorem conePoint_apply (P b c : Fin 1 → ℂ) (r s : ℝ) :
    ((P + r • (b + s • (c - b) - P)) 0) = P 0 + r * (b 0 + s * (c 0 - b 0) - P 0) := by
  simp [Complex.real_smul]

/-- If `I` contains `p + r (q - p)` for `p, q ∈ I` and `r ∈ [0, 1]`, then the point
`P + r (b + s (c - b) - P)` of a flat cone, `r, s ∈ [0, 1]`, has real part in `I` when `P`, `b` and
`c` do. -/
theorem conePoint_re_mem {I : Set ℝ} (hI : ∀ {p q r : ℝ}, p ∈ I → q ∈ I → r ∈ Icc (0 : ℝ) 1 →
      p + r * (q - p) ∈ I) {P b c : Fin 1 → ℂ} (hP : (P 0).re ∈ I) (hb : (b 0).re ∈ I)
    (hc : (c 0).re ∈ I) {r s : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ((P + r • (b + s • (c - b) - P)) 0).re ∈ I := by
  rw [conePoint_apply]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re]
  exact hI hP (hI hb hc hs) hr

/-- If `I` contains `p + r (q - p)` for `p, q ∈ I` and `r ∈ [0, 1]`, then the point
`P + r (b + s (c - b) - P)` of a flat cone, `r, s ∈ [0, 1]`, has imaginary part in `I` when `P`,
`b` and `c` do. -/
theorem conePoint_im_mem {I : Set ℝ} (hI : ∀ {p q r : ℝ}, p ∈ I → q ∈ I → r ∈ Icc (0 : ℝ) 1 →
      p + r * (q - p) ∈ I) {P b c : Fin 1 → ℂ} (hP : (P 0).im ∈ I) (hb : (b 0).im ∈ I)
    (hc : (c 0).im ∈ I) {r s : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    ((P + r • (b + s • (c - b) - P)) 0).im ∈ I := by
  rw [conePoint_apply]
  simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im]
  exact hI hP (hI hb hc hs) hr

/-- The cone profile of the projection of `x` onto `[0, 1]` lies in `[0, 1]`. -/
theorem projIcc_coneProfile_mem (x : ℝ) :
    coneProfile (projIcc (0 : ℝ) 1 zero_le_one x) ∈ Icc (0 : ℝ) 1 :=
  coneProfile_mem_Icc (projIcc (0 : ℝ) 1 zero_le_one x).2

/-- A flat cone over three points of a closed square of the grid lies in that square. -/
theorem flatConeSimplex_mem_closedCell (G : GridData) {a b : ℕ} {P u v : Fin 1 → ℂ}
    (hP : P ∈ G.closedCell a b) (hu : u ∈ G.closedCell a b) (hv : v ∈ G.closedCell a b)
    (t : stdSimplex ℝ (Fin 3)) :
    ∃ w ∈ G.closedCell a b, flatConeSimplex (E.chart 0) (E.target_eq 0) P u v t =
      (E.chart 0).symm w := by
  refine ⟨_, ⟨?_, ?_⟩, flatConeSimplex_apply _ _ P u v t⟩
  · exact conePoint_re_mem (fun hp hq hr ↦ add_mul_sub_mem_Icc hp hq hr) hP.1 hu.1 hv.1
      (coneProfile_mem_Icc (stdSimplex_one_add_two_mem t)) (projIcc_coneProfile_mem _)
  · exact conePoint_im_mem (fun hp hq hr ↦ add_mul_sub_mem_Icc hp hq hr) hP.2 hu.2 hv.2
      (coneProfile_mem_Icc (stdSimplex_one_add_two_mem t)) (projIcc_coneProfile_mem _)

/-- A degenerate flat cone over a horizontal or vertical pair of lattice points lies on the grid
lines. -/
theorem flatConeSimplex_mem_gridLines (G : GridData) {i j : ℕ} {v : Fin 1 → ℂ}
    (hv : v = G.pt (i + 1) j ∨ v = G.pt i (j + 1)) (t : stdSimplex ℝ (Fin 3)) :
    ∃ w ∈ G.gridLines, flatConeSimplex (E.chart 0) (E.target_eq 0) (G.pt i j) v (G.pt i j) t =
      (E.chart 0).symm w := by
  refine ⟨_, ?_, flatConeSimplex_apply _ _ _ v _ t⟩
  have hI : ∀ x : ℝ, ∀ {p q r : ℝ}, p ∈ Icc x x → q ∈ Icc x x → r ∈ Icc (0 : ℝ) 1 →
      p + r * (q - p) ∈ Icc x x := fun x _ _ _ hp hq hr ↦ add_mul_sub_mem_Icc hp hq hr
  have hr := coneProfile_mem_Icc (stdSimplex_one_add_two_mem t)
  have hs := projIcc_coneProfile_mem (t 2 / (t 1 + t 2))
  rcases hv with rfl | rfl
  · right
    refine ⟨j, ?_⟩
    have := conePoint_im_mem (hI (G.y₀ + j * G.h)) (P := G.pt i j) (b := G.pt (i + 1) j)
      (c := G.pt i j) ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ hr hs
    exact le_antisymm this.2 this.1
  · left
    refine ⟨i, ?_⟩
    have := conePoint_re_mem (hI (G.x₀ + i * G.h)) (P := G.pt i j) (b := G.pt i (j + 1))
      (c := G.pt i j) ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩ hr hs
    exact le_antisymm this.2 this.1

/-- **The apex of a flat cone is met only at the apex**, when the apex is off the base. -/
theorem flatConeSimplex_eq_symm_apex_iff (e : OpenPartialHomeomorph T (Fin 1 → ℂ))
    (he : e.target = univ) {P b c : Fin 1 → ℂ}
    (hoff : ∀ s ∈ Icc (0 : ℝ) 1, b + s • (c - b) ≠ P) (t : stdSimplex ℝ (Fin 3)) :
    flatConeSimplex e he P b c t = e.symm P ↔ t = squareCollapse (0, 0) := by
  have hinj : Function.Injective e.symm := fun u v huv ↦ by
    have hu : u ∈ e.target := by rw [he]; exact mem_univ _
    have hv : v ∈ e.target := by rw [he]; exact mem_univ _
    rw [← e.right_inv hu, ← e.right_inv hv, huv]
  rw [flatConeSimplex_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := hinj h
    rw [add_eq_left, smul_eq_zero] at h'
    rcases h' with h0 | h0
    · exact eq_squareCollapse_zero_zero_of_add_eq_zero
        ((coneProfile_eq_zero_iff (stdSimplex_one_add_two_mem t).1).1 h0)
    · exact absurd (sub_eq_zero.1 h0) (hoff _ (projIcc_coneProfile_mem _))
  · rw [add_eq_zero_of_eq_squareCollapse_zero_zero h, coneProfile_zero, zero_smul, add_zero]

end ImagesTerms

section TermsImages

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- The coordinate of the flat segment `b → c` at `y` is `b + ρ(y) (c - b)`, `ρ` the cone
profile. -/
theorem segmentCurve_apply_zero (b c : Fin 1 → ℂ) (y : ℝ) :
    segmentCurve b c y 0 = b 0 + coneProfile y * (c 0 - b 0) := by
  simp [segmentCurve, Complex.real_smul]

/-- **The cones of the cell around `∞` lie off the open big square**, or at `∞`. -/
theorem infConeSimplex_cases (G : GridData) {b c : Fin 1 → ℂ}
    (h : (star (b 0) * (c 0 - b 0)).im ≠ 0)
    (hout : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      (fun _ ↦ (b 0 + s * (c 0 - b 0)) / r) ∉ G.openSquare) (t : stdSimplex ℝ (Fin 3)) :
    infConeSimplex E b c t = (E.chart 1).symm 0 ∨
      ∃ v ∉ G.openSquare, infConeSimplex E b c t = (E.chart 0).symm v := by
  rw [infConeSimplex_apply E h]
  set r := coneProfile (t 1 + t 2)
  set y := projIcc (0 : ℝ) 1 zero_le_one (t 2 / (t 1 + t 2))
  rcases (coneProfile_nonneg (t 1 + t 2)).eq_or_lt with h0 | h0
  · left; rw [show r = 0 from h0.symm, zero_smul]
  · right
    have hβ := segmentCurve_ne_zero h (y : ℝ)
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    set v : Fin 1 → ℂ := fun _ ↦ segmentCurve b c y 0 / r
    have hv : v 0 ≠ 0 := div_ne_zero hβ hr0
    refine ⟨v, ?_, ?_⟩
    · have := hout r ⟨h0, coneProfile_le_one (stdSimplex_one_add_two_mem t).2⟩
        (coneProfile y) (projIcc_coneProfile_mem _)
      simpa [v, segmentCurve_apply_zero] using this
    · rw [← E.symm_one_inv v hv]
      congr 1
      funext i
      simp only [v, invCurve, Pi.smul_apply, Complex.real_smul, inv_div]
      field_simp

/-- **The cones of the cell around `∞` meet `∞` only at their apex.** -/
theorem infConeSimplex_eq_symm_zero_iff {b c : Fin 1 → ℂ}
    (h : (star (b 0) * (c 0 - b 0)).im ≠ 0) (t : stdSimplex ℝ (Fin 3)) :
    infConeSimplex E b c t = (E.chart 1).symm 0 ↔ t = squareCollapse (0, 0) := by
  rw [infConeSimplex_apply E h]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · have h' := symm_injective E 1 hx
    have h'' := congrFun h' 0
    simp only [Pi.smul_apply, Pi.zero_apply, invCurve, Complex.real_smul, mul_eq_zero,
      inv_eq_zero, Complex.ofReal_eq_zero] at h''
    rcases h'' with h0 | h0
    · exact eq_squareCollapse_zero_zero_of_add_eq_zero
        ((coneProfile_eq_zero_iff (stdSimplex_one_add_two_mem t).1).1 h0)
    · exact absurd h0 (segmentCurve_ne_zero h _)
  · rw [add_eq_zero_of_eq_squareCollapse_zero_zero hx, coneProfile_zero, zero_smul]

variable (G : GridData)

/-- The triangles of the fans of the grid. -/
def IsGridTerm (σ : Simplex T 2) : Prop :=
  ∃ a < G.m, ∃ b < G.m, ∃ j : Fin 4, σ = flatConeSimplex (E.chart 0) (E.target_eq 0)
    (G.apex a b) (G.corners a b j) (G.corners a b (finRotate 4 j))

/-- The triangles of the cell around `∞`. -/
def IsInfTerm (σ : Simplex T 2) : Prop :=
  ∃ a < G.m, σ = infConeSimplex E (G.pt (a + 1) 0) (G.pt a 0) ∨
    σ = infConeSimplex E (G.pt a G.m) (G.pt (a + 1) G.m) ∨
    σ = infConeSimplex E (G.pt G.m (a + 1)) (G.pt G.m a) ∨
    σ = infConeSimplex E (G.pt 0 a) (G.pt 0 (a + 1))

/-- The correction triangles. -/
def IsNegTerm (σ : Simplex T 2) : Prop :=
  ∃ i ≤ G.m, ∃ j ≤ G.m, (∃ v, (v = G.pt (i + 1) j ∨ v = G.pt i (j + 1)) ∧
    σ = flatConeSimplex (E.chart 0) (E.target_eq 0) (G.pt i j) v (G.pt i j)) ∨
    σ = pointSimplex 2 ((E.chart 0).symm (G.pt i j))

/-- The terms of the sphere chain. -/
def IsTerm (σ : Simplex T 2) : Prop := IsGridTerm E G σ ∨ IsInfTerm E G σ ∨ IsNegTerm E G σ

/-- For `i, j ≤ m`, the correction chain of the lattice point `pt i j` and its right or upper
neighbour is supported on the terms of the sphere chain. -/
theorem corrChain_mem_supported_isTerm {i j : ℕ} (hi : i ≤ G.m) (hj : j ≤ G.m)
    {v : Fin 1 → ℂ} (hv : v = G.pt (i + 1) j ∨ v = G.pt i (j + 1)) :
    corrChain E (G.pt i j) v ∈ Finsupp.supported ℂ ℂ {σ | IsTerm E G σ} :=
  add_mem (Finsupp.single_mem_supported ℂ _
      (Or.inr (Or.inr ⟨i, hi, j, hj, Or.inl ⟨v, hv, rfl⟩⟩)))
    (Finsupp.single_mem_supported ℂ _ (Or.inr (Or.inr ⟨i, hi, j, hj, Or.inr rfl⟩)))

/-- The sphere chain is supported on its terms. -/
theorem sphereChain_mem_supported_isTerm :
    sphereChain E G ∈ Finsupp.supported ℂ ℂ {σ | IsTerm E G σ} := by
  rw [sphereChain_eq]
  refine sub_mem (add_mem (Submodule.sum_mem _ fun a ha ↦ Submodule.sum_mem _ fun b hb ↦
    Submodule.sum_mem _ fun j _ ↦ Finsupp.single_mem_supported ℂ _
      (Or.inl ⟨a, Finset.mem_range.1 ha, b, Finset.mem_range.1 hb, j, rfl⟩)) ?_) ?_
  · refine add_mem (Submodule.sum_mem _ fun a ha ↦ add_mem
      (Finsupp.single_mem_supported ℂ _ (Or.inr (Or.inl ⟨a, Finset.mem_range.1 ha, Or.inl rfl⟩)))
      (Finsupp.single_mem_supported ℂ _ (Or.inr (Or.inl ⟨a, Finset.mem_range.1 ha,
        Or.inr (Or.inl rfl)⟩)))) (Submodule.sum_mem _ fun b hb ↦ add_mem
      (Finsupp.single_mem_supported ℂ _ (Or.inr (Or.inl ⟨b, Finset.mem_range.1 hb,
        Or.inr (Or.inr (Or.inl rfl))⟩)))
      (Finsupp.single_mem_supported ℂ _ (Or.inr (Or.inl ⟨b, Finset.mem_range.1 hb,
        Or.inr (Or.inr (Or.inr rfl))⟩))))
  · refine add_mem (add_mem (Submodule.sum_mem _ fun a ha ↦ Submodule.sum_mem _ fun b hb ↦
      add_mem (corrChain_mem_supported_isTerm E G (Finset.mem_range.1 ha).le
          (Finset.mem_range.1 hb) (Or.inl rfl))
        (corrChain_mem_supported_isTerm E G (Finset.mem_range.1 ha).le
          (Finset.mem_range.1 hb).le (Or.inr rfl)))
      (Submodule.sum_mem _ fun a ha ↦ corrChain_mem_supported_isTerm E G
        (Finset.mem_range.1 ha).le (Nat.zero_le _) (Or.inl rfl)))
      (Submodule.sum_mem _ fun b hb ↦ corrChain_mem_supported_isTerm E G le_rfl
        (Finset.mem_range.1 hb).le (Or.inr rfl))

/-- A triangle in the support of the sphere chain is one of its terms. -/
theorem isTerm_of_mem_support {σ : Simplex T 2} (hσ : σ ∈ (sphereChain E G).support) :
    IsTerm E G σ :=
  sphereChain_mem_supported_isTerm E G hσ

/-- Every point of a correction triangle is, in the chart `z`, on the grid lines. -/
theorem isNegTerm_mem_gridLines {σ : Simplex T 2} (hσ : IsNegTerm E G σ)
    (t : stdSimplex ℝ (Fin 3)) : ∃ w ∈ G.gridLines, σ t = (E.chart 0).symm w := by
  obtain ⟨i, -, j, -, ⟨v, hv, rfl⟩ | rfl⟩ := hσ
  · exact flatConeSimplex_mem_gridLines E G hv t
  · exact ⟨G.pt i j, Or.inl ⟨i, rfl⟩, rfl⟩

variable {G}

/-- For a good grid, each triangle of the fans of the grid lies, in the chart `z`, in the closed
square `(a, b)` of its fan, for some `a, b < m`. -/
theorem isGridTerm_mem_closedCell (hG : G.IsGood) {σ : Simplex T 2} (hσ : IsGridTerm E G σ) :
    ∃ a < G.m, ∃ b < G.m, ∀ t, ∃ w ∈ G.closedCell a b, σ t = (E.chart 0).symm w := by
  obtain ⟨a, ha, b, hb, j, rfl⟩ := hσ
  refine ⟨a, ha, b, hb, flatConeSimplex_mem_closedCell E G ?_ ?_ ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hG.apex_mem a ha b hb
    exact ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩
  · exact GridData.corners_mem_closedCell hG.encloses.h_pos a b j
  · exact GridData.corners_mem_closedCell hG.encloses.h_pos a b _

/-- A grid enclosing the origin has at least one square along a side. -/
theorem GridData.Encloses.m_pos (hG : G.Encloses) : 0 < G.m := by
  rcases Nat.eq_zero_or_pos G.m with h | h
  · have := hG.x_pos; rw [h] at this; simp at this; linarith [hG.x₀_neg]
  · exact h

/-- For a grid enclosing the origin, a triangle of the cell around `∞` is of positive orientation,
passes through the point at `∞` exactly at the vertex `s(0, 0)`, and each of its points is the
point at `∞` or, in the chart `z`, off the open big square. -/
theorem isInfTerm_cases (hG : G.Encloses) {σ : Simplex T 2} (hσ : IsInfTerm E G σ) :
    PosForm E σ ∧ (∀ t, σ t = (E.chart 1).symm 0 ↔ t = squareCollapse (0, 0)) ∧
      ∀ t, σ t = (E.chart 1).symm 0 ∨ ∃ v ∉ G.openSquare, σ t = (E.chart 0).symm v := by
  have hh := hG.h_pos
  obtain ⟨a, ha, h⟩ := hσ
  have hm : (a : ℝ) + 1 ≤ G.m := by exact_mod_cast ha
  rcases h with rfl | rfl | rfl | rfl
  · refine ⟨Or.inr ⟨_, _, hG.bottom a, rfl⟩, infConeSimplex_eq_symm_zero_iff E (hG.bottom a).ne,
      infConeSimplex_cases E G (hG.bottom a).ne fun r hr s _ hv ↦ ?_⟩
    have := hv.2.2.1
    simp only [Complex.div_ofReal_im, Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im,
      GridData.pt_im] at this
    rw [lt_div_iff₀ hr.1] at this
    push_cast at this
    nlinarith [hG.y₀_neg, hr.2]
  · refine ⟨Or.inr ⟨_, _, hG.top a, rfl⟩, infConeSimplex_eq_symm_zero_iff E (hG.top a).ne,
      infConeSimplex_cases E G (hG.top a).ne fun r hr s _ hv ↦ ?_⟩
    have := hv.2.2.2
    simp only [Complex.div_ofReal_im, Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im,
      GridData.pt_im] at this
    rw [div_lt_iff₀ hr.1] at this
    nlinarith [hG.y_pos, hr.2]
  · refine ⟨Or.inr ⟨_, _, hG.right a, rfl⟩, infConeSimplex_eq_symm_zero_iff E (hG.right a).ne,
      infConeSimplex_cases E G (hG.right a).ne fun r hr s _ hv ↦ ?_⟩
    have := hv.2.1
    simp only [Complex.div_ofReal_re, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re,
      GridData.pt_re] at this
    rw [div_lt_iff₀ hr.1] at this
    nlinarith [hG.x_pos, hr.2]
  · refine ⟨Or.inr ⟨_, _, hG.left a, rfl⟩, infConeSimplex_eq_symm_zero_iff E (hG.left a).ne,
      infConeSimplex_cases E G (hG.left a).ne fun r hr s _ hv ↦ ?_⟩
    have := hv.1
    simp only [Complex.div_ofReal_re, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re,
      GridData.pt_re] at this
    rw [lt_div_iff₀ hr.1] at this
    push_cast at this
    nlinarith [hG.x₀_neg, hr.2]

end TermsImages

section Apex

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- For chains `f, g` with natural coefficients, `(f + g) σ ≠ 0` when `f σ ≠ 0`. -/
theorem natChains_add_apply_ne_zero_left {f g : Chain ℂ T 2} (hf : f ∈ natChains (T := T))
    (hg : g ∈ natChains (T := T)) {σ : Simplex T 2} (h : f σ ≠ 0) : (f + g) σ ≠ 0 := by
  obtain ⟨n, hn⟩ := hf σ
  obtain ⟨k, hk⟩ := hg σ
  rw [Finsupp.add_apply, hn, hk]
  rw [hn] at h
  have : n ≠ 0 := by rintro rfl; exact h (by simp)
  exact_mod_cast (show n + k ≠ 0 by omega)

/-- For chains `f, g` with natural coefficients, `(f + g) σ ≠ 0` when `g σ ≠ 0`. -/
theorem natChains_add_apply_ne_zero_right {f g : Chain ℂ T 2} (hf : f ∈ natChains (T := T))
    (hg : g ∈ natChains (T := T)) {σ : Simplex T 2} (h : g σ ≠ 0) : (f + g) σ ≠ 0 := by
  rw [add_comm]; exact natChains_add_apply_ne_zero_left hg hf h

/-- A finite sum of chains with natural coefficients has nonzero coefficient at `σ` when one of its
terms does. -/
theorem natChains_sum_apply_ne_zero {ι : Type*} {s : Finset ι} {f : ι → Chain ℂ T 2}
    (hf : ∀ i ∈ s, f i ∈ natChains (T := T)) {i : ι} (hi : i ∈ s) {σ : Simplex T 2}
    (h : f i σ ≠ 0) : (∑ j ∈ s, f j) σ ≠ 0 := by
  classical
  rw [← Finset.add_sum_erase s f hi]
  exact natChains_add_apply_ne_zero_left (hf i hi)
    (AddSubmonoid.sum_mem _ fun j hj ↦ hf j (Finset.mem_of_mem_erase hj)) h

/-- A simplex with coefficient `1` has nonzero coefficient at itself. -/
theorem single_apply_self_ne_zero (σ : Simplex T 2) : single σ (1 : ℂ) σ ≠ 0 := by simp

/-- The cell around `∞` has natural coefficients. -/
theorem infChain_mem_natChains (G : GridData) : infChain E G ∈ natChains (T := T) :=
  add_mem (AddSubmonoid.sum_mem _ fun _ _ ↦ add_mem (single_mem_natChains _)
    (single_mem_natChains _)) (AddSubmonoid.sum_mem _ fun _ _ ↦
      add_mem (single_mem_natChains _) (single_mem_natChains _))

/-- The sum of the fans of the squares of the grid has natural coefficients. -/
theorem gridFans_mem_natChains (G : GridData) :
    ∑ a ∈ Finset.range G.m, ∑ b ∈ Finset.range G.m, cellFan E G a b ∈ natChains (T := T) :=
  AddSubmonoid.sum_mem _ fun a _ ↦ AddSubmonoid.sum_mem _ fun b _ ↦ cellFan_mem_natChains E G a b

/-- Each triangle of the fan of a square `(a, b)` with `a, b < m` has nonzero coefficient in the
positive part of the sphere chain. -/
theorem posChain_apply_gridTerm_ne_zero (G : GridData) {a b : ℕ} (ha : a < G.m) (hb : b < G.m)
    (j : Fin 4) : posChain E G (flatConeSimplex (E.chart 0) (E.target_eq 0) (G.apex a b)
      (G.corners a b j) (G.corners a b (finRotate 4 j))) ≠ 0 := by
  refine natChains_add_apply_ne_zero_left (gridFans_mem_natChains E G)
    (infChain_mem_natChains E G) ?_
  refine natChains_sum_apply_ne_zero (fun a _ ↦ AddSubmonoid.sum_mem _ fun b _ ↦
    cellFan_mem_natChains E G a b) (Finset.mem_range.2 ha) ?_
  refine natChains_sum_apply_ne_zero (fun b _ ↦ cellFan_mem_natChains E G a b)
    (Finset.mem_range.2 hb) ?_
  exact natChains_sum_apply_ne_zero (fun _ _ ↦ single_mem_natChains _) (Finset.mem_univ j)
    (single_apply_self_ne_zero _)

/-- Each flat cone around `∞` over an inverted bottom edge of the grid has nonzero coefficient in
the positive part of the sphere chain. -/
theorem posChain_apply_infBottom_ne_zero (G : GridData) {a : ℕ} (ha : a < G.m) :
    posChain E G (infConeSimplex E (G.pt (a + 1) 0) (G.pt a 0)) ≠ 0 := by
  refine natChains_add_apply_ne_zero_right (gridFans_mem_natChains E G)
    (infChain_mem_natChains E G) ?_
  refine natChains_add_apply_ne_zero_left (AddSubmonoid.sum_mem _ fun _ _ ↦ add_mem
    (single_mem_natChains _) (single_mem_natChains _)) (AddSubmonoid.sum_mem _ fun _ _ ↦
      add_mem (single_mem_natChains _) (single_mem_natChains _)) ?_
  refine natChains_sum_apply_ne_zero (fun _ _ ↦ add_mem (single_mem_natChains _)
    (single_mem_natChains _)) (Finset.mem_range.2 ha) ?_
  exact natChains_add_apply_ne_zero_left (single_mem_natChains _) (single_mem_natChains _)
    (single_apply_self_ne_zero _)

/-- The edges of a square of the grid lie on the grid lines. -/
theorem GridData.corners_segment_mem_gridLines (G : GridData) (a b : ℕ) (j : Fin 4) (s : ℝ) :
    G.corners a b j + s • (G.corners a b (finRotate 4 j) - G.corners a b j) ∈ G.gridLines := by
  rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) j with rfl | rfl | rfl | rfl
  · right; refine ⟨b, ?_⟩
    simp [GridData.corners, GridData.pt, Complex.real_smul, show (finRotate 4) 0 = 1 from rfl]
  · left; refine ⟨a + 1, ?_⟩
    simp [GridData.corners, GridData.pt, Complex.real_smul, show (finRotate 4) 1 = 2 from rfl]
  · right; refine ⟨b + 1, ?_⟩
    simp [GridData.corners, GridData.pt, Complex.real_smul, show (finRotate 4) 2 = 3 from rfl]
  · left; refine ⟨a, ?_⟩
    simp [GridData.corners, GridData.pt, Complex.real_smul, show (finRotate 4) 3 = 0 from rfl]

/-- A cone of a fan meets its apex only at the apex. -/
theorem gridTerm_eq_apex_iff {G : GridData} (hG : G.IsGood) {a b : ℕ} (ha : a < G.m)
    (hb : b < G.m) (j : Fin 4) (t : stdSimplex ℝ (Fin 3)) :
    flatConeSimplex (E.chart 0) (E.target_eq 0) (G.apex a b) (G.corners a b j)
        (G.corners a b (finRotate 4 j)) t = (E.chart 0).symm (G.apex a b) ↔
      t = squareCollapse (0, 0) :=
  flatConeSimplex_eq_symm_apex_iff _ _ (fun s _ h ↦
    GridData.notMem_gridLines_of_mem_openCell hG.encloses.h_pos (hG.apex_mem a ha b hb)
      (by rw [← h]; exact G.corners_segment_mem_gridLines a b j s)) t

end Apex

section SimplePoint

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- The real part of the point `P + r (b + s (c - b) - P)` of a flat cone. -/
theorem conePoint_re (P b c : Fin 1 → ℂ) (r s : ℝ) :
    ((P + r • (b + s • (c - b) - P)) 0).re =
      (P 0).re + r * ((b 0).re + s * ((c 0).re - (b 0).re) - (P 0).re) := by
  rw [conePoint_apply]; simp [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re]

/-- The imaginary part of the point `P + r (b + s (c - b) - P)` of a flat cone. -/
theorem conePoint_im (P b c : Fin 1 → ℂ) (r s : ℝ) :
    ((P + r • (b + s • (c - b) - P)) 0).im =
      (P 0).im + r * ((b 0).im + s * ((c 0).im - (b 0).im) - (P 0).im) := by
  rw [conePoint_apply]; simp [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im]

/-- The cone profile at `1 / 2` lies in `(0, 1)`. -/
theorem coneProfile_half_mem : coneProfile (1 / 2) ∈ Ioo (0 : ℝ) 1 :=
  ⟨coneProfile_pos (by norm_num), by
    have := strictMonoOn_coneProfile (by norm_num : (1 / 2 : ℝ) ∈ Ici 0)
      (by norm_num : (1 : ℝ) ∈ Ici 0) (by norm_num)
    rwa [coneProfile_one] at this⟩

/-- The cell around `∞` is supported on its triangles. -/
theorem infChain_mem_supported (G : GridData) :
    infChain E G ∈ Finsupp.supported ℂ ℂ {σ | IsInfTerm E G σ} := by
  refine add_mem (Submodule.sum_mem _ fun a ha ↦ add_mem
      (Finsupp.single_mem_supported ℂ _ ⟨a, Finset.mem_range.1 ha, Or.inl rfl⟩)
      (Finsupp.single_mem_supported ℂ _ ⟨a, Finset.mem_range.1 ha, Or.inr (Or.inl rfl)⟩))
    (Submodule.sum_mem _ fun b hb ↦ add_mem
      (Finsupp.single_mem_supported ℂ _ ⟨b, Finset.mem_range.1 hb, Or.inr (Or.inr (Or.inl rfl))⟩)
      (Finsupp.single_mem_supported ℂ _ ⟨b, Finset.mem_range.1 hb, Or.inr (Or.inr (Or.inr rfl))⟩))

variable {G : GridData}

/-- The cone of the fan of the square `(0, 0)` over its bottom edge. -/
abbrev simpleCone (E : SphereCharts T) (G : GridData) : Simplex T 2 :=
  flatConeSimplex (E.chart 0) (E.target_eq 0) (G.apex 0 0) (G.corners 0 0 0)
    (G.corners 0 0 (finRotate 4 0))

/-- For a good grid, a triangle of the fans of the grid other than that of index `(0, 0, 0)` is not
`simpleCone E G`. -/
theorem gridTerm_ne_simpleCone (hG : G.IsGood) {a b : ℕ} (ha : a < G.m) (hb : b < G.m)
    (j : Fin 4) (hne : (a, b, j) ≠ (0, 0, 0)) :
    flatConeSimplex (E.chart 0) (E.target_eq 0) (G.apex a b) (G.corners a b j)
      (G.corners a b (finRotate 4 j)) ≠ simpleCone E G := by
  have hh := hG.encloses.h_pos
  have hm := hG.encloses.m_pos
  intro h
  have h0 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (0, 0))) h
  have h1 := congrArg (fun τ : Simplex T 2 ↦ τ (squareCollapse (1, 0))) h
  simp only [(flatConeSimplex_vertex _ _ _ _ _).1, (flatConeSimplex_vertex _ _ _ _ _).2.1] at h0 h1
  have hP := symm_injective E 0 h0
  have hc := symm_injective E 0 h1
  obtain ⟨h1', h2', h3', h4'⟩ := hG.apex_mem 0 hm 0 hm
  obtain ⟨rfl, rfl⟩ := GridData.eq_of_mem_openCell_of_mem_closedCell hh (hG.apex_mem a ha b hb)
    (show G.apex a b ∈ G.closedCell 0 0 from hP ▸ ⟨⟨h1'.le, h2'.le⟩, ⟨h3'.le, h4'.le⟩⟩)
  apply hne
  have hj : j = 0 := by
    rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) j with rfl | rfl | rfl | rfl
    · rfl
    · have := congrArg (fun v : Fin 1 → ℂ ↦ (v 0).re) hc
      simp [GridData.corners, GridData.pt] at this; linarith
    · have := congrArg (fun v : Fin 1 → ℂ ↦ (v 0).re) hc
      simp [GridData.corners, GridData.pt] at this; linarith
    · have := congrArg (fun v : Fin 1 → ℂ ↦ (v 0).im) hc
      simp [GridData.corners, GridData.pt] at this; linarith
  rw [hj]

/-- For a grid enclosing the origin, no triangle of the cell around `∞` is `simpleCone E G`. -/
theorem infTerm_ne_simpleCone {σ : Simplex T 2} (hG : G.Encloses) (hσ : IsInfTerm E G σ) :
    σ ≠ simpleCone E G := by
  intro h
  have h0 := ((isInfTerm_cases E hG hσ).2.1 (squareCollapse (0, 0))).2 rfl
  rw [h, (flatConeSimplex_vertex _ _ _ _ _).1] at h0
  exact E.symm_zero_notMem (h0 ▸ symm_mem_source E 0 _)

/-- The simple cone has coefficient `1` in the positive chain. -/
theorem posChain_apply_simpleCone (hG : G.IsGood) : posChain E G (simpleCone E G) = 1 := by
  classical
  have hm := hG.encloses.m_pos
  have hinf : infChain E G (simpleCone E G) = 0 := Finsupp.notMem_support_iff.1 fun h ↦
    infTerm_ne_simpleCone E hG.encloses (infChain_mem_supported E G h) rfl
  rw [posChain, Finsupp.add_apply, hinf, add_zero, Finsupp.finset_sum_apply,
    Finset.sum_eq_single 0 (fun a ha ha0 ↦ ?_) (fun h ↦ absurd (Finset.mem_range.2 hm) h),
    Finsupp.finset_sum_apply,
    Finset.sum_eq_single 0 (fun b hb hb0 ↦ ?_) (fun h ↦ absurd (Finset.mem_range.2 hm) h),
    cellFan, Finsupp.finset_sum_apply, Finset.sum_eq_single (0 : Fin 4) (fun j _ hj ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ _) h)]
  · exact Finsupp.single_eq_same
  · rw [Finsupp.single_apply, if_neg]
    exact gridTerm_ne_simpleCone E hG hm hm j (by simp [hj])
  · rw [cellFan, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [Finsupp.single_apply, if_neg]
    exact gridTerm_ne_simpleCone E hG hm (Finset.mem_range.1 hb) j (by simp [hb0])
  · rw [Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun b hb ↦ ?_
    rw [cellFan, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ ↦ ?_
    rw [Finsupp.single_apply, if_neg]
    exact gridTerm_ne_simpleCone E hG (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) j
      (by simp [ha0])

end SimplePoint

section Density

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- The collapse of the square onto `Δ²` is continuous. -/
theorem continuous_squareCollapse : Continuous squareCollapse := by
  have h1 : Continuous fun p : ℝ × ℝ ↦ (projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) :=
    continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)
  have h2 : Continuous fun p : ℝ × ℝ ↦ (projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ) :=
    continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)
  refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
  fin_cases i
  · exact continuous_const.sub h1
  · exact h1.mul (continuous_const.sub h2)
  · exact h1.mul h2

/-- A point of the closed square whose image lies in an open set can be moved into the open
square. -/
theorem exists_mem_Ioo_of_mem_unitSquare (σ : Simplex T 2) {W : Set T} (hW : IsOpen W)
    {p : ℝ × ℝ} (hp : p ∈ unitSquare) (hpW : σ (squareCollapse p) ∈ W) :
    ∃ p' ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, σ (squareCollapse p') ∈ W := by
  have hc : Continuous fun q ↦ σ (squareCollapse q) := σ.continuous.comp continuous_squareCollapse
  have hcl : p ∈ closure (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) := by
    rw [closure_prod_eq, closure_Ioo zero_ne_one]; exact hp
  obtain ⟨p', hp'W, hp'⟩ := mem_closure_iff_nhds.1 hcl _ ((hW.preimage hc).mem_nhds hpW)
  exact ⟨p', hp', hp'W⟩

/-- The collapse of the square sends the left side `{0} × ℝ` to the vertex `s(0, 0)`. -/
theorem squareCollapse_zero_left (y : ℝ) : squareCollapse (0, y) = squareCollapse (0, 0) := by
  refine FundamentalChartCycle.stdSimplex_three_ext ?_ ?_ <;>
  simp [squareCollapse]

/-- A real number in `[0, m]`, `m > 0`, lies in `[a, a + 1]` for some `a < m`. -/
theorem exists_nat_lt_mem_Icc {m : ℕ} (hm : 0 < m) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) m) :
    ∃ a < m, (a : ℝ) ≤ u ∧ u ≤ a + 1 := by
  by_cases h : ⌊u⌋₊ < m
  · exact ⟨⌊u⌋₊, h, Nat.floor_le hu.1, (Nat.lt_floor_add_one u).le⟩
  · refine ⟨m - 1, by omega, ?_, ?_⟩
    · have : (m : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast not_lt.1 h
      have := Nat.floor_le hu.1
      push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
      linarith
    · push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
      linarith [hu.2]

/-- The point `P + r (c + s (c' - c) - P)` of a flat cone is hit at the image of the point
`(x, y)` of the square with `ρ(x) = r`, `ρ(y) = s`. -/
theorem exists_flatConeSimplex_eq (P c c' : Fin 1 → ℂ) {r s : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ p ∈ unitSquare, flatConeSimplex (E.chart 0) (E.target_eq 0) P c c' (squareCollapse p) =
      (E.chart 0).symm (P + r • (c + s • (c' - c) - P)) := by
  obtain ⟨x, hx, rfl⟩ := exists_coneProfile_eq hr
  obtain ⟨y, hy, rfl⟩ := exists_coneProfile_eq hs
  exact ⟨(x, y), ⟨hx, hy⟩, flatConeSimplex_squareCollapse _ _ _ _ _ ⟨hx, hy⟩⟩

/-- A point `w / M` of `[x₀, x₀ + m h]` lies in one of the `m` intervals
`[x₀ + a h, x₀ + (a + 1) h]`. -/
theorem exists_nat_lt_div_mem {m : ℕ} (hm : 0 < m) {x₀ h M w : ℝ} (hh : 0 < h) (hM : 0 < M)
    (h1 : M * x₀ ≤ w) (h2 : w ≤ M * (x₀ + m * h)) :
    ∃ a < m, x₀ + a * h ≤ w / M ∧ w / M ≤ x₀ + (a + 1) * h := by
  have h1' : x₀ ≤ w / M := by rw [le_div_iff₀ hM]; linarith
  have h2' : w / M ≤ x₀ + m * h := by rw [div_le_iff₀ hM]; linarith
  obtain ⟨a, ha, h3, h4⟩ := exists_nat_lt_mem_Icc hm (u := (w / M - x₀) / h)
    ⟨div_nonneg (by linarith) hh.le, by rw [div_le_iff₀ hh]; linarith⟩
  refine ⟨a, ha, ?_, ?_⟩
  · rw [le_div_iff₀ hh] at h3
    linarith
  · rw [div_le_iff₀ hh] at h4
    linarith

/-- Two points of `ℂ = Fin 1 → ℂ` with the same real and imaginary parts are equal. -/
theorem fin_one_ext {u v : Fin 1 → ℂ} (hre : (u 0).re = (v 0).re) (him : (u 0).im = (v 0).im) :
    u = v := funext fun i ↦ Subsingleton.elim i 0 ▸ Complex.ext hre him

/-- The maximum of four elements of a linear order is one of them. -/
theorem max_max_eq_or {α : Type*} [LinearOrder α] (a b c d : α) :
    max (max a b) (max c d) = a ∨ max (max a b) (max c d) = b ∨
      max (max a b) (max c d) = c ∨ max (max a b) (max c d) = d := by
  rcases max_choice (max a b) (max c d) with h | h <;> rw [h] <;>
    rcases max_choice a b with h' | h' <;> rcases max_choice c d with h'' | h'' <;>
    simp only [h', h'', true_or, or_true]

/-- **The fan of a rectangle covers it.** A point `z` of the closed rectangle with corners
`c₀, …, c₃` (counterclockwise from the lower left one) and an interior apex `P` is
`P + r (cⱼ + s (cⱼ₊₁ - cⱼ) - P)` for some edge `j` and `r, s ∈ [0, 1]`. -/
theorem exists_mem_fan_rectangle {x₁ x₂ y₁ y₂ : ℝ} {P z : Fin 1 → ℂ}
    (hx : (P 0).re ∈ Ioo x₁ x₂) (hy : (P 0).im ∈ Ioo y₁ y₂) (hzx : (z 0).re ∈ Icc x₁ x₂)
    (hzy : (z 0).im ∈ Icc y₁ y₂) :
    ∃ j : Fin 4, ∃ r ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
      z = P + r • ((fun _ ↦ rectangleCorners x₁ x₂ y₁ y₂ j) +
        s • ((fun _ ↦ rectangleCorners x₁ x₂ y₁ y₂ (finRotate 4 j)) -
          (fun _ ↦ rectangleCorners x₁ x₂ y₁ y₂ j)) - P) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  set px := (P 0).re
  set py := (P 0).im
  set dx := (z 0).re - px
  set dy := (z 0).im - py
  set A := dx / (x₂ - px)
  set B := -dx / (px - x₁)
  set C := dy / (y₂ - py)
  set D := -dy / (py - y₁)
  have ha : 0 < x₂ - px := by linarith
  have hb : 0 < px - x₁ := by linarith
  have hc : 0 < y₂ - py := by linarith
  have hd : 0 < py - y₁ := by linarith
  set M := max (max A B) (max C D)
  have hAM : A ≤ M := le_max_of_le_left (le_max_left _ _)
  have hBM : B ≤ M := le_max_of_le_left (le_max_right _ _)
  have hCM : C ≤ M := le_max_of_le_right (le_max_left _ _)
  have hDM : D ≤ M := le_max_of_le_right (le_max_right _ _)
  have hA1 : A ≤ 1 := (div_le_one ha).2 (by linarith [hzx.2])
  have hB1 : B ≤ 1 := (div_le_one hb).2 (by linarith [hzx.1])
  have hC1 : C ≤ 1 := (div_le_one hc).2 (by linarith [hzy.2])
  have hD1 : D ≤ 1 := (div_le_one hd).2 (by linarith [hzy.1])
  have hM1 : M ≤ 1 := max_le (max_le hA1 hB1) (max_le hC1 hD1)
  have hdxA : dx = A * (x₂ - px) := (div_mul_cancel₀ dx ha.ne').symm
  have hdxB : dx = -(B * (px - x₁)) := by
    rw [show B * (px - x₁) = -dx / (px - x₁) * (px - x₁) from rfl, div_mul_cancel₀ _ hb.ne']; ring
  have hdyC : dy = C * (y₂ - py) := (div_mul_cancel₀ dy hc.ne').symm
  have hdyD : dy = -(D * (py - y₁)) := by
    rw [show D * (py - y₁) = -dy / (py - y₁) * (py - y₁) from rfl, div_mul_cancel₀ _ hd.ne']; ring
  rcases le_or_gt M 0 with hM0 | hM0
  · -- `z = P`
    have hdx : dx = 0 := by nlinarith
    have hdy : dy = 0 := by nlinarith
    refine ⟨0, 0, ⟨le_rfl, zero_le_one⟩, 0, ⟨le_rfl, zero_le_one⟩, fin_one_ext ?_ ?_⟩ <;>
      simp <;> linarith
  have hMc : M = A ∨ M = B ∨ M = C ∨ M = D := max_max_eq_or A B C D
  refine (hMc.elim (fun h ↦ ?_) fun h ↦ h.elim (fun h ↦ ?_) fun h ↦ h.elim (fun h ↦ ?_)
    fun h ↦ ?_)
  · -- right edge `c₁ → c₂`
    refine ⟨1, M, ⟨hM0.le, hM1⟩, (dy / M + py - y₁) / (y₂ - y₁), ⟨?_, ?_⟩, fin_one_ext ?_ ?_⟩
    · apply div_nonneg _ (by linarith)
      have : -(py - y₁) ≤ dy / M := by rw [le_div_iff₀ hM0]; nlinarith
      linarith
    · rw [div_le_one (by linarith)]
      have : dy / M ≤ y₂ - py := by rw [div_le_iff₀ hM0]; nlinarith
      linarith
    · rw [conePoint_re]
      simp [rectangleCorners, show (finRotate 4) 1 = 2 from rfl]
      rw [← h] at hdxA
      linarith
    · rw [conePoint_im]
      simp [rectangleCorners, show (finRotate 4) 1 = 2 from rfl]
      field_simp [show y₂ - y₁ ≠ 0 by linarith, show x₂ - x₁ ≠ 0 by linarith, hM0.ne']
      linarith [show dy = (z 0).im - py from rfl, show dx = (z 0).re - px from rfl]
  · -- left edge `c₃ → c₀`
    refine ⟨3, M, ⟨hM0.le, hM1⟩, (y₂ - (dy / M + py)) / (y₂ - y₁), ⟨?_, ?_⟩, fin_one_ext ?_ ?_⟩
    · apply div_nonneg _ (by linarith)
      have : dy / M ≤ y₂ - py := by rw [div_le_iff₀ hM0]; nlinarith
      linarith
    · rw [div_le_one (by linarith)]
      have : -(py - y₁) ≤ dy / M := by rw [le_div_iff₀ hM0]; nlinarith
      linarith
    · rw [conePoint_re]
      simp [rectangleCorners, show (finRotate 4) 3 = 0 from rfl]
      rw [← h] at hdxB
      linarith
    · rw [conePoint_im]
      simp [rectangleCorners, show (finRotate 4) 3 = 0 from rfl]
      field_simp [show y₂ - y₁ ≠ 0 by linarith, show x₂ - x₁ ≠ 0 by linarith, hM0.ne']
      linarith [show dy = (z 0).im - py from rfl, show dx = (z 0).re - px from rfl]
  · -- top edge `c₂ → c₃`
    refine ⟨2, M, ⟨hM0.le, hM1⟩, (x₂ - (dx / M + px)) / (x₂ - x₁), ⟨?_, ?_⟩, fin_one_ext ?_ ?_⟩
    · apply div_nonneg _ (by linarith)
      have : dx / M ≤ x₂ - px := by rw [div_le_iff₀ hM0]; nlinarith
      linarith
    · rw [div_le_one (by linarith)]
      have : -(px - x₁) ≤ dx / M := by rw [le_div_iff₀ hM0]; nlinarith
      linarith
    · rw [conePoint_re]
      simp [rectangleCorners, show (finRotate 4) 2 = 3 from rfl]
      field_simp [show y₂ - y₁ ≠ 0 by linarith, show x₂ - x₁ ≠ 0 by linarith, hM0.ne']
      linarith [show dy = (z 0).im - py from rfl, show dx = (z 0).re - px from rfl]
    · rw [conePoint_im]
      simp [rectangleCorners, show (finRotate 4) 2 = 3 from rfl]
      rw [← h] at hdyC
      linarith
  · -- bottom edge `c₀ → c₁`
    refine ⟨0, M, ⟨hM0.le, hM1⟩, (dx / M + px - x₁) / (x₂ - x₁), ⟨?_, ?_⟩, fin_one_ext ?_ ?_⟩
    · apply div_nonneg _ (by linarith)
      have : -(px - x₁) ≤ dx / M := by rw [le_div_iff₀ hM0]; nlinarith
      linarith
    · rw [div_le_one (by linarith)]
      have : dx / M ≤ x₂ - px := by rw [div_le_iff₀ hM0]; nlinarith
      linarith
    · rw [conePoint_re]
      simp [rectangleCorners, show (finRotate 4) 0 = 1 from rfl]
      field_simp [show y₂ - y₁ ≠ 0 by linarith, show x₂ - x₁ ≠ 0 by linarith, hM0.ne']
      linarith [show dy = (z 0).im - py from rfl, show dx = (z 0).re - px from rfl]
    · rw [conePoint_im]
      simp [rectangleCorners, show (finRotate 4) 0 = 1 from rfl]
      rw [← h] at hdyD
      linarith

/-- A point `z = M (b + s (c - b))`, `M ≥ 1`, of the chart `z` is hit by the cone of the cell
around `∞` over the inverted segment `b → c`. -/
theorem exists_infConeSimplex_eq {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0)
    {z : Fin 1 → ℂ} {M s : ℝ} (hM : 1 ≤ M) (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : z 0 = M * (b 0 + s * (c 0 - b 0))) :
    ∃ p ∈ unitSquare, infConeSimplex E b c (squareCollapse p) = (E.chart 0).symm z := by
  have hM0 : 0 < M := by linarith
  obtain ⟨x, hx, hxM⟩ := exists_coneProfile_eq (r := M⁻¹)
    ⟨inv_nonneg.2 hM0.le, inv_le_one_of_one_le₀ hM⟩
  obtain ⟨y, hy, rfl⟩ := exists_coneProfile_eq hs
  have hq : segmentCurve b c y 0 ≠ 0 := segmentCurve_ne_zero h y
  have hz0 : z 0 ≠ 0 := by
    rw [hz, ← segmentCurve_apply_zero]; exact mul_ne_zero (by exact_mod_cast hM0.ne') hq
  refine ⟨(x, y), ⟨hx, hy⟩, ?_⟩
  rw [infConeSimplex, dif_pos h, mapSimplex_apply, coneSimplex_squareCollapse _ _ _ _ ⟨hx, hy⟩,
    ← E.symm_one_inv z hz0]
  congr 1
  funext i
  simp only [CurveCupPositivity.coneMap, zero_add, sub_zero, Pi.smul_apply, invCurve, hxM,
    Complex.real_smul, hz, ← segmentCurve_apply_zero]
  push_cast
  field_simp

/-- Each triangle of the cell around `∞` has nonzero coefficient in it. -/
theorem infChain_apply_ne_zero_of_isInfTerm {G : GridData} {σ : Simplex T 2}
    (hσ : IsInfTerm E G σ) : infChain E G σ ≠ 0 := by
  have hs : ∀ τ τ' : Simplex T 2, single τ (1 : ℂ) + single τ' 1 ∈ natChains (T := T) :=
    fun _ _ ↦ add_mem (single_mem_natChains _) (single_mem_natChains _)
  obtain ⟨a, ha, h | h | h | h⟩ := hσ <;> subst h
  · exact natChains_add_apply_ne_zero_left (AddSubmonoid.sum_mem _ fun _ _ ↦ hs _ _)
      (AddSubmonoid.sum_mem _ fun _ _ ↦ hs _ _) (natChains_sum_apply_ne_zero (fun _ _ ↦ hs _ _)
        (Finset.mem_range.2 ha) (natChains_add_apply_ne_zero_left (single_mem_natChains _)
          (single_mem_natChains _) (single_apply_self_ne_zero _)))
  · exact natChains_add_apply_ne_zero_left (AddSubmonoid.sum_mem _ fun _ _ ↦ hs _ _)
      (AddSubmonoid.sum_mem _ fun _ _ ↦ hs _ _) (natChains_sum_apply_ne_zero (fun _ _ ↦ hs _ _)
        (Finset.mem_range.2 ha) (natChains_add_apply_ne_zero_right (single_mem_natChains _)
          (single_mem_natChains _) (single_apply_self_ne_zero _)))
  · exact natChains_add_apply_ne_zero_right (AddSubmonoid.sum_mem _ fun _ _ ↦ hs _ _)
      (AddSubmonoid.sum_mem _ fun _ _ ↦ hs _ _) (natChains_sum_apply_ne_zero (fun _ _ ↦ hs _ _)
        (Finset.mem_range.2 ha) (natChains_add_apply_ne_zero_left (single_mem_natChains _)
          (single_mem_natChains _) (single_apply_self_ne_zero _)))
  · exact natChains_add_apply_ne_zero_right (AddSubmonoid.sum_mem _ fun _ _ ↦ hs _ _)
      (AddSubmonoid.sum_mem _ fun _ _ ↦ hs _ _) (natChains_sum_apply_ne_zero (fun _ _ ↦ hs _ _)
        (Finset.mem_range.2 ha) (natChains_add_apply_ne_zero_right (single_mem_natChains _)
          (single_mem_natChains _) (single_apply_self_ne_zero _)))

/-- Each triangle of the cell around `∞` has nonzero coefficient in the positive part of the sphere
chain. -/
theorem posChain_apply_ne_zero_of_isInfTerm {G : GridData} {σ : Simplex T 2}
    (hσ : IsInfTerm E G σ) : posChain E G σ ≠ 0 :=
  natChains_add_apply_ne_zero_right (gridFans_mem_natChains E G) (infChain_mem_natChains E G)
    (infChain_apply_ne_zero_of_isInfTerm E hσ)

/-- **The cell around `∞` covers the outside of the big square.** -/
theorem exists_infTerm_eq {G : GridData} (hG : G.Encloses) {z : Fin 1 → ℂ}
    (hz : ¬ ((z 0).re ∈ Icc G.x₀ (G.x₀ + G.m * G.h) ∧ (z 0).im ∈ Icc G.y₀ (G.y₀ + G.m * G.h))) :
    ∃ σ, IsInfTerm E G σ ∧ ∃ p ∈ unitSquare, σ (squareCollapse p) = (E.chart 0).symm z := by
  have hh := hG.h_pos
  have hm := hG.m_pos
  have hX1 := hG.x₀_neg
  have hX2 := hG.x_pos
  have hY1 := hG.y₀_neg
  have hY2 := hG.y_pos
  set X2 := G.x₀ + G.m * G.h
  set Y2 := G.y₀ + G.m * G.h
  set A := (z 0).re / X2
  set B := (z 0).re / G.x₀
  set C := (z 0).im / Y2
  set D := (z 0).im / G.y₀
  set M := max (max A B) (max C D)
  have hAM : A ≤ M := le_max_of_le_left (le_max_left _ _)
  have hBM : B ≤ M := le_max_of_le_left (le_max_right _ _)
  have hCM : C ≤ M := le_max_of_le_right (le_max_left _ _)
  have hDM : D ≤ M := le_max_of_le_right (le_max_right _ _)
  have hreA : (z 0).re = A * X2 := (div_mul_cancel₀ _ hX2.ne').symm
  have hreB : (z 0).re = B * G.x₀ := (div_mul_cancel₀ _ hX1.ne).symm
  have himC : (z 0).im = C * Y2 := (div_mul_cancel₀ _ hY2.ne').symm
  have himD : (z 0).im = D * G.y₀ := (div_mul_cancel₀ _ hY1.ne).symm
  have hM1 : 1 ≤ M := by
    by_contra hlt
    push Not at hlt
    apply hz
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith
  have hM0 : 0 < M := by linarith
  have hre1 : M * G.x₀ ≤ (z 0).re := by nlinarith
  have hre2 : (z 0).re ≤ M * X2 := by nlinarith
  have him1 : M * G.y₀ ≤ (z 0).im := by nlinarith
  have him2 : (z 0).im ≤ M * Y2 := by nlinarith
  have hMc : M = A ∨ M = B ∨ M = C ∨ M = D := max_max_eq_or A B C D
  rcases hMc with h | h | h | h
  · -- right side, run downwards
    obtain ⟨a, ha, h3, h4⟩ := exists_nat_lt_div_mem hm hh hM0 him1 him2
    refine ⟨_, ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩, exists_infConeSimplex_eq E
      (hG.right a).ne hM1 (s := (G.y₀ + (a + 1) * G.h - (z 0).im / M) / G.h)
      ⟨div_nonneg (by linarith) hh.le, by rw [div_le_iff₀ hh]; linarith⟩ ?_⟩
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, GridData.pt_re,
        GridData.pt_im, zero_mul, sub_zero]
      rw [← h] at hreA
      push_cast
      linarith
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, GridData.pt_re,
        GridData.pt_im, zero_mul, add_zero]
      push_cast
      field_simp
      ring
  · -- left side, run upwards
    obtain ⟨a, ha, h3, h4⟩ := exists_nat_lt_div_mem hm hh hM0 him1 him2
    refine ⟨_, ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩, exists_infConeSimplex_eq E
      (hG.left a).ne hM1 (s := ((z 0).im / M - G.y₀ - a * G.h) / G.h)
      ⟨div_nonneg (by linarith) hh.le, by rw [div_le_iff₀ hh]; linarith⟩ ?_⟩
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, GridData.pt_re,
        GridData.pt_im, zero_mul, sub_zero]
      rw [← h] at hreB
      push_cast
      linarith
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, GridData.pt_re,
        GridData.pt_im, zero_mul, add_zero]
      push_cast
      field_simp
      ring
  · -- top side, run eastwards
    obtain ⟨a, ha, h3, h4⟩ := exists_nat_lt_div_mem hm hh hM0 hre1 hre2
    refine ⟨_, ⟨a, ha, Or.inr (Or.inl rfl)⟩, exists_infConeSimplex_eq E
      (hG.top a).ne hM1 (s := ((z 0).re / M - G.x₀ - a * G.h) / G.h)
      ⟨div_nonneg (by linarith) hh.le, by rw [div_le_iff₀ hh]; linarith⟩ ?_⟩
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, GridData.pt_re,
        GridData.pt_im, zero_mul, sub_zero]
      push_cast
      field_simp
      ring
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, GridData.pt_re,
        GridData.pt_im, zero_mul, add_zero]
      rw [← h] at himC
      push_cast
      linarith
  · -- bottom side, run westwards
    obtain ⟨a, ha, h3, h4⟩ := exists_nat_lt_div_mem hm hh hM0 hre1 hre2
    refine ⟨_, ⟨a, ha, Or.inl rfl⟩, exists_infConeSimplex_eq E
      (hG.bottom a).ne hM1 (s := (G.x₀ + (a + 1) * G.h - (z 0).re / M) / G.h)
      ⟨div_nonneg (by linarith) hh.le, by rw [div_le_iff₀ hh]; linarith⟩ ?_⟩
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, GridData.pt_re,
        GridData.pt_im, zero_mul, sub_zero]
      push_cast
      field_simp
      ring
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_im, GridData.pt_re,
        GridData.pt_im, zero_mul, add_zero]
      rw [← h] at himD
      push_cast
      linarith

end Density

section Choice

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- A point `w` whose real and imaginary parts are within `h` of those of `u` lies within `2 h` of
`u`. -/
theorem dist_le_two_mul_of_near {w u : Fin 1 → ℂ} {h : ℝ} (hh : 0 ≤ h)
    (hre : (w 0).re ∈ Icc ((u 0).re - h) ((u 0).re + h))
    (him : (w 0).im ∈ Icc ((u 0).im - h) ((u 0).im + h)) : dist w u ≤ 2 * h := by
  refine (dist_pi_le_iff (by linarith)).2 fun i ↦ ?_
  rw [Subsingleton.elim i 0, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have h1 : |(w 0).re - (u 0).re| ≤ h := abs_le.2 ⟨by linarith [hre.1], by linarith [hre.2]⟩
  have h2 : |(w 0).im - (u 0).im| ≤ h := abs_le.2 ⟨by linarith [him.1], by linarith [him.2]⟩
  linarith

/-- A point of `[lo, lo + h]` lies in `[lo - h, lo + h]`. -/
theorem mem_Icc_sub_add_of_mem_Icc {lo x h : ℝ} (hx : x ∈ Icc lo (lo + h)) :
    x ∈ Icc (lo - h) (lo + h) := ⟨by linarith [hx.1, hx.2], hx.2⟩

/-- The grid and correction triangles lie within `h` of a lattice point of the grid. -/
theorem exists_near_lattice_of_isGridTerm_or_isNegTerm {G : GridData} (hG : G.IsGood)
    {σ : Simplex T 2}
    (hσ : IsGridTerm E G σ ∨ IsNegTerm E G σ) :
    ∃ i ≤ G.m, ∃ j ≤ G.m, ∀ t, ∃ w, σ t = (E.chart 0).symm w ∧
      (w 0).re ∈ Icc ((G.pt i j 0).re - G.h) ((G.pt i j 0).re + G.h) ∧
      (w 0).im ∈ Icc ((G.pt i j 0).im - G.h) ((G.pt i j 0).im + G.h) := by
  have hh := hG.encloses.h_pos
  rcases hσ with ⟨a, ha, b, hb, j, rfl⟩ | ⟨i, hi, j, hj, hσ⟩
  · refine ⟨a, ha.le, b, hb.le, fun t ↦ ?_⟩
    obtain ⟨w, hw, hwt⟩ := flatConeSimplex_mem_closedCell E G (a := a) (b := b)
      (P := G.apex a b) (by
        obtain ⟨h1, h2, h3, h4⟩ := hG.apex_mem a ha b hb
        exact ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩)
      (GridData.corners_mem_closedCell hh a b j) (GridData.corners_mem_closedCell hh a b _) t
    refine ⟨w, hwt, ?_, ?_⟩
    · rw [GridData.pt_re]; exact mem_Icc_sub_add_of_mem_Icc (by
        have := hw.1; rw [show G.x₀ + (a + 1) * G.h = G.x₀ + a * G.h + G.h by ring] at this
        exact this)
    · rw [GridData.pt_im]; exact mem_Icc_sub_add_of_mem_Icc (by
        have := hw.2; rw [show G.y₀ + (b + 1) * G.h = G.y₀ + b * G.h + G.h by ring] at this
        exact this)
  · refine ⟨i, hi, j, hj, fun t ↦ ?_⟩
    rcases hσ with ⟨v, hv, rfl⟩ | rfl
    · refine ⟨_, flatConeSimplex_apply _ _ _ v _ t, ?_, ?_⟩
      · refine conePoint_re_mem (fun hp hq hr ↦ add_mul_sub_mem_Icc hp hq hr)
          ⟨by linarith, by linarith⟩ ?_ ⟨by linarith, by linarith⟩
          (coneProfile_mem_Icc (stdSimplex_one_add_two_mem t)) (projIcc_coneProfile_mem _)
        rcases hv with rfl | rfl <;> simp only [GridData.pt_re] <;> push_cast <;>
          constructor <;> nlinarith
      · refine conePoint_im_mem (fun hp hq hr ↦ add_mul_sub_mem_Icc hp hq hr)
          ⟨by linarith, by linarith⟩ ?_ ⟨by linarith, by linarith⟩
          (coneProfile_mem_Icc (stdSimplex_one_add_two_mem t)) (projIcc_coneProfile_mem _)
        rcases hv with rfl | rfl <;> simp only [GridData.pt_im] <;> push_cast <;>
          constructor <;> nlinarith
    · exact ⟨_, rfl, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The cones of the cell around `∞` lie, in the chart `u`, in the ball of radius `1 / L` when
the sides of the big square are at distance at least `L` from `0`. -/
theorem exists_norm_le_one_div_of_isInfTerm {G : GridData} (hG : G.Encloses) {L : ℝ}
    (hL : 0 < L)
    (h1 : L ≤ -G.x₀) (h2 : L ≤ G.x₀ + G.m * G.h) (h3 : L ≤ -G.y₀) (h4 : L ≤ G.y₀ + G.m * G.h)
    {σ : Simplex T 2} (hσ : IsInfTerm E G σ) (t : stdSimplex ℝ (Fin 3)) :
    ∃ u : Fin 1 → ℂ, ‖u‖ ≤ 1 / L ∧ σ t = (E.chart 1).symm u := by
  have key : ∀ {b c : Fin 1 → ℂ} (h : (star (b 0) * (c 0 - b 0)).im ≠ 0),
      (∀ y : ℝ, L ≤ ‖segmentCurve b c y 0‖) →
      ∃ u : Fin 1 → ℂ, ‖u‖ ≤ 1 / L ∧ infConeSimplex E b c t = (E.chart 1).symm u := by
    intro b c h hβ
    refine ⟨_, ?_, infConeSimplex_apply E h t⟩
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_
    simp only [Pi.smul_apply, invCurve, norm_smul, norm_inv]
    have hr := coneProfile_mem_Icc (stdSimplex_one_add_two_mem t)
    have hb := hβ (projIcc (0 : ℝ) 1 zero_le_one (t 2 / (t 1 + t 2)))
    rw [Real.norm_of_nonneg hr.1]
    calc coneProfile (t 1 + t 2) * ‖segmentCurve b c _ 0‖⁻¹ ≤ ‖segmentCurve b c _ 0‖⁻¹ :=
          mul_le_of_le_one_left (inv_nonneg.2 (hL.trans_le hb).le) hr.2
      _ ≤ 1 / L := by
        rw [one_div]
        exact inv_anti₀ hL hb
  obtain ⟨a, ha, h | h | h | h⟩ := hσ <;> subst h
  · refine key (hG.bottom a).ne fun y ↦ (le_trans ?_ (Complex.abs_im_le_norm _))
    rw [segmentCurve_apply_zero]
    simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im, GridData.pt_im]
    push_cast
    rw [abs_of_neg (by linarith)]
    linarith
  · refine key (hG.top a).ne fun y ↦ (le_trans ?_ (Complex.abs_im_le_norm _))
    rw [segmentCurve_apply_zero]
    simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.sub_im, GridData.pt_im]
    rw [sub_self, mul_zero, add_zero, abs_of_pos (by linarith)]
    exact h4
  · refine key (hG.right a).ne fun y ↦ (le_trans ?_ (Complex.abs_re_le_norm _))
    rw [segmentCurve_apply_zero]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, GridData.pt_re]
    rw [sub_self, mul_zero, add_zero, abs_of_pos (by linarith)]
    exact h2
  · refine key (hG.left a).ne fun y ↦ (le_trans ?_ (Complex.abs_re_le_norm _))
    rw [segmentCurve_apply_zero]
    simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, GridData.pt_re]
    push_cast
    rw [abs_of_neg (by linarith)]
    linarith

/-- A finite subset of a metric space has a positive minimal distance between distinct points. -/
theorem exists_pos_le_dist_of_finite {α : Type*} [MetricSpace α] {F : Set α} (hF : F.Finite) :
    ∃ d > 0, ∀ x ∈ F, ∀ y ∈ F, x ≠ y → d ≤ dist x y := by
  classical
  set P := (hF.toFinset ×ˢ hF.toFinset).filter fun p : α × α ↦ p.1 ≠ p.2
  by_cases hP : P.Nonempty
  · refine ⟨(P.image fun p ↦ dist p.1 p.2).min' (hP.image _), ?_, fun x hx y hy hxy ↦ ?_⟩
    · obtain ⟨p, hp, hpm⟩ := Finset.mem_image.1
        (Finset.min'_mem (P.image fun p : α × α ↦ dist p.1 p.2) (hP.image _))
      rw [← hpm]
      exact dist_pos.2 (Finset.mem_filter.1 hp).2
    · exact Finset.min'_le _ _ (Finset.mem_image.2 ⟨(x, y), Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨hF.mem_toFinset.2 hx, hF.mem_toFinset.2 hy⟩, hxy⟩, rfl⟩)
  · refine ⟨1, one_pos, fun x hx y hy hxy ↦ absurd ⟨(x, y), Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hF.mem_toFinset.2 hx, hF.mem_toFinset.2 hy⟩, hxy⟩⟩ hP⟩

end Choice

/-! ### The geometry of the sphere chain -/

section Geometry

variable {T : Type*} [TopologicalSpace T] (E : SphereCharts T)

/-- **A good fine grid adapted to a finite set.** For a finite set `S ⊆ T` and open neighbourhoods
`B y` of the points `y` of `T`, there is a good grid whose squares contain the points of `S` in
the domain of `z`, at most one in each and as its apex, and all of whose triangles lie in some
`B y`.

Take a big square in the coordinate `z` containing `z(S)` in its interior and, by compactness of
`T \ z⁻¹(big square)` around `∞`, large enough that the cell around `∞` lies in `B ∞`. Choose the
side `h` below a Lebesgue number, for the cover `{z(B y)}`, of the closed big square, and below the
distances between the points of `z(S)`; and offset the grid lines off the finitely many real and
imaginary parts of the points of `z(S)`. -/
theorem exists_isGood_gridData (S : Set T) (hS : S.Finite) (B : T → Set T)
    (hBo : ∀ y, IsOpen (B y)) (hmem : ∀ y, y ∈ B y) :
    ∃ G : GridData, G.IsGood ∧
      (∀ s ∈ S, s ∈ (E.chart 0).source → ∃ a < G.m, ∃ b < G.m, G.apex a b = E.chart 0 s) ∧
      ∀ σ ∈ (sphereChain E G).support, ∃ y, range σ ⊆ B y := by
  classical
  have hcs : ∀ k, Continuous (E.chart k).symm := fun k ↦ continuousOn_univ.1 (by
    rw [← E.target_eq k]; exact (E.chart k).continuousOn_symm)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 ((hBo ((E.chart 1).symm 0)).preimage (hcs 1)) 0
    (hmem _)
  set S₀ := (E.chart 0) '' (S ∩ (E.chart 0).source)
  have hS₀ : S₀.Finite := (hS.subset inter_subset_left).image _
  obtain ⟨C, hC⟩ := hS₀.isBounded.subset_closedBall 0
  set L := max (2 / δ) C + 1
  have h2δ : 0 < 2 / δ := by positivity
  have hL : 0 < L := by linarith [le_max_left (2 / δ) C]
  have hLC : ∀ v ∈ S₀, |(v 0).re| < L ∧ |(v 0).im| < L := fun v hv ↦ by
    have h1 : ‖v‖ ≤ C := by simpa using hC hv
    have h2 : ‖v 0‖ ≤ ‖v‖ := norm_le_pi_norm v 0
    have h3 : C < L := by linarith [le_max_right (2 / δ) C]
    exact ⟨by linarith [Complex.abs_re_le_norm (v 0)], by linarith [Complex.abs_im_le_norm (v 0)]⟩
  have hLδ : 1 / L < δ := by
    have : 2 / δ < L := by linarith [le_max_left (2 / δ) C]
    rw [div_lt_iff₀ hL]
    rw [div_lt_iff₀ hδ] at this
    linarith
  obtain ⟨ε, hε, hleb⟩ := lebesgue_number_lemma_of_metric
    (isCompact_closedBall (0 : Fin 1 → ℂ) (8 * L))
    (c := fun w ↦ (E.chart 0).symm ⁻¹' B ((E.chart 0).symm w))
    (fun w ↦ (hBo _).preimage (hcs 0)) (fun w _ ↦ mem_iUnion.2 ⟨w, hmem _⟩)
  obtain ⟨d, hd, hdist⟩ := exists_pos_le_dist_of_finite hS₀
  set h := min (ε / 3) (min (d / 3) (L / 2))
  have hh : 0 < h := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hhε : h ≤ ε / 3 := min_le_left _ _
  have hhd : h ≤ d / 3 := (min_le_right _ _).trans (min_le_left _ _)
  have hhL : h ≤ L / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set N := ⌈(2 * L + h) / h⌉₊ + 1
  obtain ⟨x₀, hx₀, hx₀B⟩ := (Set.Ioo_infinite (show -L - h < -L by linarith)).exists_notMem_finset
    ((hS₀.toFinset ×ˢ Finset.range N).image fun p ↦ (p.1 0).re - p.2 * h)
  obtain ⟨y₀, hy₀, hy₀B⟩ := (Set.Ioo_infinite (show -L - h < -L by linarith)).exists_notMem_finset
    ((hS₀.toFinset ×ˢ Finset.range N).image fun p ↦ (p.1 0).im - p.2 * h)
  set m := ⌈2 * L / h⌉₊ + 1
  have hmh1 : 2 * L + h ≤ m * h := by
    have := Nat.le_ceil (2 * L / h)
    have h' : (m : ℝ) = ⌈2 * L / h⌉₊ + 1 := by push_cast [m]; ring
    rw [h']
    have : 2 * L / h * h = 2 * L := div_mul_cancel₀ _ hh.ne'
    nlinarith
  have hmh2 : m * h ≤ 2 * L + 2 * h := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * L / h by positivity)
    have h' : (m : ℝ) = ⌈2 * L / h⌉₊ + 1 := by push_cast [m]; ring
    rw [h']
    have : 2 * L / h * h = 2 * L := div_mul_cancel₀ _ hh.ne'
    nlinarith
  have hloc : ∀ (z₀ r : ℝ), z₀ ∈ Ioo (-L - h) (-L) → |r| < L →
      (∀ i < N, r ≠ z₀ + i * h) → ∃ a < m, z₀ + a * h < r ∧ r < z₀ + (a + 1) * h := by
    intro z₀ r hz₀ hr havoid
    obtain ⟨hr1, hr2⟩ := abs_lt.1 hr
    set u := (r - z₀) / h
    have hu0 : 0 ≤ u := div_nonneg (by linarith [hz₀.2]) hh.le
    set a := ⌊u⌋₊
    have ha1 : (a : ℝ) ≤ u := Nat.floor_le hu0
    have ha2 : u < a + 1 := Nat.lt_floor_add_one u
    have huN : u < (2 * L + h) / h := by
      rw [div_lt_div_iff_of_pos_right hh]; linarith [hz₀.1]
    have haN : a < N := by
      have : (a : ℝ) < ⌈(2 * L + h) / h⌉₊ + 1 := by
        linarith [Nat.le_ceil ((2 * L + h) / h)]
      exact_mod_cast this
    have hlo : z₀ + a * h ≤ r := by
      have := mul_le_mul_of_nonneg_right ha1 hh.le
      rw [div_mul_cancel₀ _ hh.ne'] at this; linarith
    have hhi : r < z₀ + (a + 1) * h := by
      have := mul_lt_mul_of_pos_right ha2 hh
      rw [div_mul_cancel₀ _ hh.ne'] at this; linarith
    refine ⟨a, ?_, lt_of_le_of_ne hlo (fun he ↦ havoid a haN he.symm), hhi⟩
    have : (a : ℝ) * h < m * h := by linarith [hz₀.1]
    exact_mod_cast lt_of_mul_lt_mul_right this hh.le
  let G₀ : GridData := ⟨x₀, y₀, h, m, fun _ _ ↦ 0⟩
  let ap : ℕ → ℕ → Fin 1 → ℂ := fun a b ↦
    if hx : ∃ s ∈ S₀, s ∈ G₀.openCell a b then hx.choose
    else fun _ ↦ ⟨x₀ + (a + 1 / 2) * h, y₀ + (b + 1 / 2) * h⟩
  let G : GridData := ⟨x₀, y₀, h, m, ap⟩
  have hEnc : G.Encloses := ⟨hh, by show x₀ < 0; linarith [hx₀.2],
    by show y₀ < 0; linarith [hy₀.2], by show 0 < x₀ + m * h; linarith [hx₀.1],
    by show 0 < y₀ + m * h; linarith [hy₀.1]⟩
  have hGood : G.IsGood := ⟨hEnc, fun a _ b _ ↦ by
    show ap a b ∈ G₀.openCell a b
    by_cases hx : ∃ s ∈ S₀, s ∈ G₀.openCell a b
    · simp only [ap, dif_pos hx]; exact hx.choose_spec.2
    · simp only [ap, dif_neg hx]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [G₀] <;> nlinarith⟩
  refine ⟨G, hGood, fun s hs hs0 ↦ ?_, fun σ hσ ↦ ?_⟩
  · have hw : E.chart 0 s ∈ S₀ := ⟨s, ⟨hs, hs0⟩, rfl⟩
    set w := E.chart 0 s
    obtain ⟨a, ha, ha1, ha2⟩ := hloc x₀ (w 0).re hx₀ (hLC w hw).1 fun i hi he ↦ hx₀B
      (Finset.mem_image.2 ⟨(w, i), Finset.mem_product.2 ⟨hS₀.mem_toFinset.2 hw,
        Finset.mem_range.2 hi⟩, by simp only; linarith⟩)
    obtain ⟨b, hb, hb1, hb2⟩ := hloc y₀ (w 0).im hy₀ (hLC w hw).2 fun i hi he ↦ hy₀B
      (Finset.mem_image.2 ⟨(w, i), Finset.mem_product.2 ⟨hS₀.mem_toFinset.2 hw,
        Finset.mem_range.2 hi⟩, by simp only; linarith⟩)
    have hwc : w ∈ G₀.openCell a b := ⟨ha1, ha2, hb1, hb2⟩
    have hx : ∃ s ∈ S₀, s ∈ G₀.openCell a b := ⟨w, hw, hwc⟩
    refine ⟨a, ha, b, hb, ?_⟩
    show ap a b = w
    simp only [ap, dif_pos hx]
    obtain ⟨hs'S, hs'c⟩ := hx.choose_spec
    by_contra hne
    have h1 := hdist _ hs'S _ hw hne
    obtain ⟨c1, c2, c3, c4⟩ := hs'c
    have h2 := dist_le_two_mul_of_near (w := hx.choose) (u := w) hh.le
      ⟨by simp only [G₀] at c1 c2; push_cast at c1 c2 ha1 ha2; nlinarith,
        by simp only [G₀] at c1 c2; push_cast at c1 c2 ha1 ha2; nlinarith⟩
      ⟨by simp only [G₀] at c3 c4; push_cast at c3 c4 hb1 hb2; nlinarith,
        by simp only [G₀] at c3 c4; push_cast at c3 c4 hb1 hb2; nlinarith⟩
    linarith
  · rcases isTerm_of_mem_support E G hσ with hg | hinf | hneg
    rotate_left
    · refine ⟨(E.chart 1).symm 0, ?_⟩
      rintro _ ⟨t, rfl⟩
      obtain ⟨u, hu, hut⟩ := exists_norm_le_one_div_of_isInfTerm E hEnc hL
        (by show L ≤ -x₀; linarith [hx₀.2])
        (by show L ≤ x₀ + m * h; linarith [hx₀.1]) (by show L ≤ -y₀; linarith [hy₀.2])
        (by show L ≤ y₀ + m * h; linarith [hy₀.1]) hinf t
      rw [hut]
      exact hball (mem_ball_zero_iff.2 (lt_of_le_of_lt hu hLδ))
    all_goals
      obtain ⟨i, hi, j, hj, hnear⟩ :=
        exists_near_lattice_of_isGridTerm_or_isNegTerm E hGood (by first
          | exact Or.inl hg | exact Or.inr hneg)
      have hi' : (i : ℝ) ≤ m := by exact_mod_cast hi
      have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
      have hu : G.pt i j ∈ Metric.closedBall (0 : Fin 1 → ℂ) (8 * L) := by
        rw [mem_closedBall_zero_iff]
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k ↦ ?_
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [show G.pt i j k = G.pt i j 0 from rfl, GridData.pt_re, GridData.pt_im]
        have e1 : |x₀ + i * h| ≤ 2 * L := abs_le.2
          ⟨by nlinarith [hx₀.1, Nat.cast_nonneg (α := ℝ) i], by nlinarith [hx₀.2]⟩
        have e2 : |y₀ + j * h| ≤ 2 * L := abs_le.2
          ⟨by nlinarith [hy₀.1, Nat.cast_nonneg (α := ℝ) j], by nlinarith [hy₀.2]⟩
        show |x₀ + i * h| + |y₀ + j * h| ≤ 8 * L
        linarith
      obtain ⟨y₁, hy₁⟩ := hleb _ hu
      refine ⟨(E.chart 0).symm y₁, ?_⟩
      rintro _ ⟨t, rfl⟩
      obtain ⟨w, hwt, hre, him⟩ := hnear t
      rw [hwt]
      exact hy₁ (Metric.mem_ball.2 (lt_of_le_of_lt (dist_le_two_mul_of_near hh.le hre him)
        (by linarith)))

/-- **The points of `S` are apices.** In a good grid whose squares have the points of `S ∩ dom z`
as apices, every point `s` of `S` is the apex `σ(s(0, 0))` of a positive triangle of the sphere
chain, and every triangle of the sphere chain through `s` is a positive triangle passing through
`s` only at its apex.

A point `s` with `z(s)` in the open square `(a, b)` lies on the four cones of that square, at
their apex only, and on no other triangle: the other cones lie in the other closed squares, the
corrections on the grid lines, and the cell around `∞` off the open big square. The point `∞` lies
only on the cones of the cell around `∞`, at their apex. -/
theorem apex_of_mem {G : GridData} (hG : G.IsGood) {S : Set T}
    (hS : ∀ s ∈ S, s ∈ (E.chart 0).source → ∃ a < G.m, ∃ b < G.m, G.apex a b = E.chart 0 s) :
    ∀ s ∈ S, (∃ σ, PosForm E σ ∧ posChain E G σ ≠ 0 ∧ σ (squareCollapse (0, 0)) = s) ∧
      ∀ σ ∈ (sphereChain E G).support, s ∈ range σ →
        PosForm E σ ∧ ∀ t, σ t = s ↔ t = squareCollapse (0, 0) := by
  have hh := hG.encloses.h_pos
  intro s hs
  by_cases hs0 : s ∈ (E.chart 0).source
  · obtain ⟨a, ha, b, hb, hab⟩ := hS s hs hs0
    have hPs : (E.chart 0).symm (G.apex a b) = s := by rw [hab]; exact (E.chart 0).left_inv hs0
    have hPcell := hG.apex_mem a ha b hb
    refine ⟨⟨_, Or.inl ⟨_, _, _, hG.left_pos ha hb 0, rfl⟩,
      posChain_apply_gridTerm_ne_zero E G ha hb 0, ?_⟩, fun σ hσ hsσ ↦ ?_⟩
    · rw [(flatConeSimplex_vertex _ _ _ _ _).1, hPs]
    obtain ⟨t, ht⟩ := hsσ
    rcases isTerm_of_mem_support E G hσ with ⟨a', ha', b', hb', j, rfl⟩ | hinf | hneg
    · obtain ⟨w, hw, hwt⟩ := flatConeSimplex_mem_closedCell E G (a := a') (b := b')
        (P := G.apex a' b') (by
          obtain ⟨h1, h2, h3, h4⟩ := hG.apex_mem a' ha' b' hb'
          exact ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩)
        (GridData.corners_mem_closedCell hh a' b' j)
        (GridData.corners_mem_closedCell hh a' b' _) t
      have hwP : w = G.apex a b := symm_injective E 0 (hwt.symm.trans (ht.trans hPs.symm))
      obtain ⟨rfl, rfl⟩ := GridData.eq_of_mem_openCell_of_mem_closedCell hh hPcell (hwP ▸ hw)
      refine ⟨Or.inl ⟨_, _, _, hG.left_pos ha hb j, rfl⟩, fun t' ↦ ?_⟩
      rw [← hPs]
      exact gridTerm_eq_apex_iff E hG ha hb j t'
    · rcases (isInfTerm_cases E hG.encloses hinf).2.2 t with h1 | ⟨v, hv, hvt⟩
      · exact (E.symm_zero_notMem (by rw [← h1, ht]; exact hs0)).elim
      · have : v = G.apex a b := symm_injective E 0 (hvt.symm.trans (ht.trans hPs.symm))
        exact absurd (this ▸ GridData.mem_openSquare_of_mem_openCell hh ha hb hPcell) hv
    · obtain ⟨w, hw, hwt⟩ := isNegTerm_mem_gridLines E G hneg t
      have : w = G.apex a b := symm_injective E 0 (hwt.symm.trans (ht.trans hPs.symm))
      exact absurd (this ▸ hw) (GridData.notMem_gridLines_of_mem_openCell hh hPcell)
  · have hs1 : s = (E.chart 1).symm 0 := by
      by_contra hne; exact hs0 (E.mem_source_zero_of_ne hne)
    have hm := hG.encloses.m_pos
    have hinf0 : IsInfTerm E G (infConeSimplex E (G.pt (0 + 1) 0) (G.pt 0 0)) :=
      ⟨0, hm, Or.inl rfl⟩
    refine ⟨⟨_, (isInfTerm_cases E hG.encloses hinf0).1,
      posChain_apply_infBottom_ne_zero E G hm, ?_⟩, fun σ hσ hsσ ↦ ?_⟩
    · rw [hs1]; exact (infConeSimplex_vertex E (hG.encloses.bottom 0).ne).1
    obtain ⟨t, ht⟩ := hsσ
    rcases isTerm_of_mem_support E G hσ with hgrid | hinf | hneg
    · obtain ⟨a', ha', b', hb', hcell⟩ := isGridTerm_mem_closedCell E hG hgrid
      obtain ⟨w, -, hwt⟩ := hcell t
      exact absurd (ht ▸ hwt ▸ symm_mem_source E 0 w) hs0
    · obtain ⟨hP, hiff, -⟩ := isInfTerm_cases E hG.encloses hinf
      exact ⟨hP, fun t' ↦ hs1 ▸ hiff t'⟩
    · obtain ⟨w, -, hwt⟩ := isNegTerm_mem_gridLines E G hneg t
      exact absurd (ht ▸ hwt ▸ symm_mem_source E 0 w) hs0

/-- **The positive triangles of the sphere chain are dense.** Every nonempty open set of `T` meets
a positive triangle of the sphere chain at the image of a point of the open square.

The closed triangles of the fans cover the closed big square and the cones of the cell around `∞`
cover the rest; and each closed triangle is the closure of the image of the open square. -/
theorem exists_posForm_mem_of_isOpen {G : GridData} (hG : G.IsGood) {W : Set T} (hW : IsOpen W)
    (hne : W.Nonempty) :
    ∃ σ, PosForm E σ ∧ posChain E G σ ≠ 0 ∧
      ∃ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, σ (squareCollapse p) ∈ W := by
  have hh := hG.encloses.h_pos
  have hm := hG.encloses.m_pos
  obtain ⟨x, hxW⟩ := hne
  have hcov : ∃ σ, PosForm E σ ∧ posChain E G σ ≠ 0 ∧
      ∃ p ∈ unitSquare, σ (squareCollapse p) = x := by
    by_cases hx : x = (E.chart 1).symm 0
    · have hinf : IsInfTerm E G (infConeSimplex E (G.pt (0 + 1) 0) (G.pt 0 0)) :=
        ⟨0, hm, Or.inl rfl⟩
      exact ⟨_, (isInfTerm_cases E hG.encloses hinf).1,
        posChain_apply_ne_zero_of_isInfTerm E hinf, (0, 0), mem_unitSquare_zero_zero,
        hx ▸ (infConeSimplex_vertex E (hG.encloses.bottom 0).ne).1⟩
    have hx0 := E.mem_source_zero_of_ne hx
    set z := E.chart 0 x
    have hxz : (E.chart 0).symm z = x := (E.chart 0).left_inv hx0
    by_cases hQ : (z 0).re ∈ Icc G.x₀ (G.x₀ + G.m * G.h) ∧
        (z 0).im ∈ Icc G.y₀ (G.y₀ + G.m * G.h)
    · obtain ⟨a, ha, ha1, ha2⟩ := exists_nat_lt_mem_Icc hm (u := ((z 0).re - G.x₀) / G.h)
        ⟨div_nonneg (by linarith [hQ.1.1]) hh.le, by rw [div_le_iff₀ hh]; linarith [hQ.1.2]⟩
      obtain ⟨b, hb, hb1, hb2⟩ := exists_nat_lt_mem_Icc hm (u := ((z 0).im - G.y₀) / G.h)
        ⟨div_nonneg (by linarith [hQ.2.1]) hh.le, by rw [div_le_iff₀ hh]; linarith [hQ.2.2]⟩
      rw [le_div_iff₀ hh] at ha1 hb1
      rw [div_le_iff₀ hh] at ha2 hb2
      obtain ⟨h1, h2, h3, h4⟩ := hG.apex_mem a ha b hb
      obtain ⟨j, r, hr, s, hs, hzj⟩ := exists_mem_fan_rectangle (P := G.apex a b) (z := z)
        ⟨h1, h2⟩ ⟨h3, h4⟩ ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      have hc : ∀ k : Fin 4, (fun _ : Fin 1 ↦ rectangleCorners (G.x₀ + a * G.h)
          (G.x₀ + (a + 1) * G.h) (G.y₀ + b * G.h) (G.y₀ + (b + 1) * G.h) k) =
          G.corners a b k := fun k ↦ funext fun i ↦ by
        rw [Subsingleton.elim i 0, GridData.corners_apply]
      rw [hc, hc] at hzj
      obtain ⟨p, hp, hpz⟩ := exists_flatConeSimplex_eq E (G.apex a b) (G.corners a b j)
        (G.corners a b (finRotate 4 j)) hr hs
      exact ⟨_, Or.inl ⟨_, _, _, hG.left_pos ha hb j, rfl⟩,
        posChain_apply_gridTerm_ne_zero E G ha hb j, p, hp, by rw [hpz, ← hzj, hxz]⟩
    · obtain ⟨σ, hσ, p, hp, hpz⟩ := exists_infTerm_eq E hG.encloses hQ
      exact ⟨σ, (isInfTerm_cases E hG.encloses hσ).1, posChain_apply_ne_zero_of_isInfTerm E hσ,
        p, hp, by rw [hpz, hxz]⟩
  obtain ⟨σ, hP, hne', p, hp, hpx⟩ := hcov
  obtain ⟨p', hp', hp'W⟩ := exists_mem_Ioo_of_mem_unitSquare σ hW hp (hpx ▸ hxW)
  exact ⟨σ, hP, hne', p', hp', hp'W⟩

/-- **A simple point of the sphere chain.** The centre of the square read of a cone of a fan is a
point over which that cone is injective and which no other triangle of the sphere chain meets; and
that cone has coefficient `1`. -/
theorem exists_simplePoint {G : GridData} (hG : G.IsGood) :
    ∃ σ₀, PosForm E σ₀ ∧ posChain E G σ₀ = 1 ∧ ∃ p₀ ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
      (∀ t, σ₀ t = σ₀ (squareCollapse p₀) → t = squareCollapse p₀) ∧
      ∀ σ ∈ (sphereChain E G).support, σ ≠ σ₀ → σ₀ (squareCollapse p₀) ∉ range σ := by
  have hh := hG.encloses.h_pos
  have hm := hG.encloses.m_pos
  obtain ⟨hr0, hr1⟩ := coneProfile_half_mem
  set r₀ := coneProfile (1 / 2)
  obtain ⟨hpx1, hpx2, hpy1, hpy2⟩ := hG.apex_mem 0 hm 0 hm
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul] at hpx1 hpx2 hpy1 hpy2
  set P := G.apex 0 0
  set w₀ : Fin 1 → ℂ := P + r₀ • (G.corners 0 0 0 + r₀ • (G.corners 0 0 (finRotate 4 0) -
    G.corners 0 0 0) - P)
  have hp₀ : ((1 : ℝ) / 2, (1 : ℝ) / 2) ∈ unitSquare := ⟨⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩⟩
  have hval : simpleCone E G (squareCollapse (1 / 2, 1 / 2)) = (E.chart 0).symm w₀ :=
    flatConeSimplex_squareCollapse _ _ _ _ _ hp₀
  have hc0re : (G.corners 0 0 0 0).re = G.x₀ := by simp [GridData.corners, GridData.pt]
  have hc0im : (G.corners 0 0 0 0).im = G.y₀ := by simp [GridData.corners, GridData.pt]
  have hc1re : (G.corners 0 0 (finRotate 4 0) 0).re = G.x₀ + G.h := by
    simp [GridData.corners, GridData.pt, show (finRotate 4) 0 = 1 from rfl]
  have hc1im : (G.corners 0 0 (finRotate 4 0) 0).im = G.y₀ := by
    simp [GridData.corners, GridData.pt, show (finRotate 4) 0 = 1 from rfl]
  have hwre : (w₀ 0).re = (P 0).re + r₀ * (G.x₀ + r₀ * G.h - (P 0).re) := by
    rw [conePoint_re, hc0re, hc1re]; ring
  have hwim : (w₀ 0).im = (P 0).im + r₀ * (G.y₀ - (P 0).im) := by
    rw [conePoint_im, hc0im, hc1im]; ring
  have hw₀ : w₀ ∈ G.openCell 0 0 := by
    simp only [GridData.openCell, mem_setOf_eq, Nat.cast_zero, zero_mul, add_zero, zero_add,
      one_mul, hwre, hwim]
    have e1 := mul_pos (sub_pos.2 hr1) (sub_pos.2 hpx1)
    have e2 := mul_pos (mul_pos hr0 hr0) hh
    have e3 := mul_pos (sub_pos.2 hr1) (sub_pos.2 hpx2)
    have e4 := mul_pos (mul_pos hr0 hh) (sub_pos.2 hr1)
    have e5 := mul_pos (sub_pos.2 hr1) (sub_pos.2 hpy1)
    have e6 := mul_pos (sub_pos.2 hr1) (sub_pos.2 hpy2)
    have e7 := mul_pos hr0 hh
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  refine ⟨simpleCone E G, Or.inl ⟨_, _, _, hG.left_pos hm hm 0, rfl⟩,
    posChain_apply_simpleCone E hG, (1 / 2, 1 / 2), ⟨⟨by norm_num, by norm_num⟩,
      ⟨by norm_num, by norm_num⟩⟩, fun t ht ↦ ?_, fun σ hσ hne hmem ↦ ?_⟩
  · -- injectivity over the simple point
    rw [hval, simpleCone, flatConeSimplex_apply] at ht
    have heq := symm_injective E 0 ht
    set R := coneProfile (t 1 + t 2)
    set y := projIcc (0 : ℝ) 1 zero_le_one (t 2 / (t 1 + t 2))
    have him := congrArg (fun v : Fin 1 → ℂ ↦ (v 0).im) heq
    have hre := congrArg (fun v : Fin 1 → ℂ ↦ (v 0).re) heq
    simp only [conePoint_im, conePoint_re, hc0re, hc0im, hc1re, hc1im] at him hre
    rw [hwim] at him
    rw [hwre] at hre
    have hR : R = r₀ := by
      have : (R - r₀) * (G.y₀ - (P 0).im) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · exact absurd h (by linarith)
    have hS : coneProfile y = r₀ := by
      rw [hR] at hre
      have : r₀ * G.h * (coneProfile y - r₀) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (mul_pos hr0 hh).ne'
      · linarith
    have hsum : t 1 + t 2 = 1 / 2 :=
      strictMonoOn_coneProfile.injOn (stdSimplex_one_add_two_mem t).1
        (by norm_num : (1 / 2 : ℝ) ∈ Ici 0) hR
    have hy : (y : ℝ) = 1 / 2 :=
      strictMonoOn_coneProfile.injOn y.2.1 (by norm_num : (1 / 2 : ℝ) ∈ Ici 0) hS
    have h2 : t 2 / (t 1 + t 2) ∈ Icc (0 : ℝ) 1 := by
      rw [hsum]
      exact ⟨by linarith [stdSimplex_apply_nonneg t 2], by
        linarith [stdSimplex_apply_nonneg t 1]⟩
    rw [show (y : ℝ) = t 2 / (t 1 + t 2) from coe_projIcc_of_mem h2, hsum] at hy
    have ht2 : t 2 = 1 / 4 := by field_simp at hy; linarith
    refine FundamentalChartCycle.stdSimplex_three_ext ?_ ?_
    · rw [squareCollapse_apply_one hp₀]; linarith
    · rw [squareCollapse_apply_two hp₀]; linarith
  · obtain ⟨t, ht⟩ := hmem
    rw [hval] at ht
    rcases isTerm_of_mem_support E G hσ with ⟨a, ha, b, hb, j, rfl⟩ | hinf | hneg
    · obtain ⟨w, hw, hwt⟩ := flatConeSimplex_mem_closedCell E G (a := a) (b := b)
        (P := G.apex a b) (by
          obtain ⟨h1, h2, h3, h4⟩ := hG.apex_mem a ha b hb
          exact ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩)
        (GridData.corners_mem_closedCell hh a b j) (GridData.corners_mem_closedCell hh a b _) t
      have hww : w = w₀ := symm_injective E 0 (hwt.symm.trans ht)
      obtain ⟨rfl, rfl⟩ := GridData.eq_of_mem_openCell_of_mem_closedCell hh hw₀ (hww ▸ hw)
      rw [flatConeSimplex_apply] at ht
      have heq := symm_injective E 0 ht
      set R := coneProfile (t 1 + t 2)
      set S := coneProfile (projIcc (0 : ℝ) 1 zero_le_one (t 2 / (t 1 + t 2)))
      have hRm : R ∈ Icc (0 : ℝ) 1 := coneProfile_mem_Icc (stdSimplex_one_add_two_mem t)
      have hSm : S ∈ Icc (0 : ℝ) 1 := projIcc_coneProfile_mem _
      have him := congrArg (fun v : Fin 1 → ℂ ↦ (v 0).im) heq
      have hre := congrArg (fun v : Fin 1 → ℂ ↦ (v 0).re) heq
      simp only [conePoint_im, conePoint_re] at him hre
      rw [hwim] at him
      rw [hwre] at hre
      rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) j with rfl | rfl | rfl | rfl
      · exact hne rfl
      · simp [GridData.corners, GridData.pt, show (finRotate 4) 1 = 2 from rfl] at him hre
        have key : R * (G.x₀ + G.h - (P 0).re) * S * G.h =
            r₀ * (G.y₀ - (P 0).im) * G.h * (1 - r₀) := by
          linear_combination (G.x₀ + G.h - (P 0).re) * him - (G.y₀ - (P 0).im) * hre
        have h1 : 0 ≤ R * (G.x₀ + G.h - (P 0).re) * S * G.h :=
          mul_nonneg (mul_nonneg (mul_nonneg hRm.1 (by linarith)) hSm.1) hh.le
        have h2 : r₀ * (G.y₀ - (P 0).im) * G.h * (1 - r₀) < 0 :=
          mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hr0 (by linarith))
            hh) (by linarith)
        linarith
      · simp [GridData.corners, GridData.pt, show (finRotate 4) 2 = 3 from rfl] at him
        nlinarith [hRm.1, hRm.2]
      · simp [GridData.corners, GridData.pt, show (finRotate 4) 3 = 0 from rfl] at him hre
        have key : R * (G.x₀ - (P 0).re) * G.h * (1 - S) =
            -(r₀ * r₀ * (G.y₀ - (P 0).im) * G.h) := by
          linear_combination (G.x₀ - (P 0).re) * him - (G.y₀ - (P 0).im) * hre
        have h1 : R * (G.x₀ - (P 0).re) * G.h * (1 - S) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos hRm.1 (by linarith)) hh.le) (by linarith [hSm.2])
        have h2 : 0 < -(r₀ * r₀ * (G.y₀ - (P 0).im) * G.h) := by
          have : r₀ * r₀ * (G.y₀ - (P 0).im) * G.h < 0 :=
            mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hr0 hr0) (by linarith)) hh
          linarith
        linarith
    · rcases (isInfTerm_cases E hG.encloses hinf).2.2 t with h1 | ⟨v, hv, hvt⟩
      · exact E.symm_zero_notMem (by rw [← h1, ht]; exact symm_mem_source E 0 _)
      · have : v = w₀ := symm_injective E 0 (hvt.symm.trans ht)
        exact hv (this ▸ GridData.mem_openSquare_of_mem_openCell hh hm hm hw₀)
    · obtain ⟨w, hw, hwt⟩ := isNegTerm_mem_gridLines E G hneg t
      have : w = w₀ := symm_injective E 0 (hwt.symm.trans ht)
      exact GridData.notMem_gridLines_of_mem_openCell hh hw₀ (this ▸ hw)

end Geometry

/-! ### Cycles of chart cones on the sphere -/

section Sphere

variable {T : Type*} [TopologicalSpace T]

/-- **A fine fundamental cycle of flat cones on a sphere, with prescribed apices.** For sphere
charts on `T`, a finite set `S ⊆ T` and open neighbourhoods `B y` of the points `y` of `T`, there
is a finite singular `2`-cycle `w = ∑ r_σ σ` of `T` with real coefficients such that:
* every triangle `σ` lies in some `B y` and is, on the unit square through the collapse, the read
  `e⁻¹ ∘ g_σ` in one of the two charts `e` of a `C²` map `g_σ`, with `r_σ` times the Jacobian
  nonnegative on an open neighbourhood `U_σ` of the square;
* the triangles meet every nonempty open set at a point where `r_σ` times the Jacobian is
  positive;
* some triangle `σ₀` with coefficient `1` has an interior point `p₀` of the square, with positive
  Jacobian, over whose image `σ₀` is injective and which no other triangle meets;
* every point `s ∈ S` is the apex `σ(s(0, 0))` of some triangle, and every triangle through `s`
  is a flat cone from `s`: its reading is `g_σ = CurveCupPositivity.coneMap coneProfile (e s) γ`
  for a `C²` curve `γ`, and it passes through `s` only at its apex.

The cycle is `sphereChain E G` for a good grid `G` (`exists_isGood_gridData`); it is a cycle by
`bd_sphereChain`, its coefficients are real and natural on the positive triangles
(`im_sphereChain_apply`, `sphereChain_apply_of_posForm`), and its triangles are positive or of
Jacobian zero (`posForm_or_negForm`), read by `exists_reading_of_posForm` and
`exists_reading_of_negForm`. -/
theorem exists_cone_cycle_of_sphereCharts (E : SphereCharts T) (S : Set T) (hS : S.Finite)
    (B : T → Set T) (hBo : ∀ y, IsOpen (B y)) (hmem : ∀ y, y ∈ B y) :
    ∃ (w : Simplex T (1 + 1) →₀ ℂ) (r : Simplex T (1 + 1) → ℝ) (k : Simplex T (1 + 1) → Fin 2)
      (g : Simplex T (1 + 1) → ℝ × ℝ → (Fin 1 → ℂ)) (U : Simplex T (1 + 1) → Set (ℝ × ℝ)),
      bd ℂ 1 w = 0 ∧
      (∀ σ ∈ w.support, w σ = r σ ∧ (∃ y, range σ ⊆ B y) ∧ IsOpen (U σ) ∧ unitSquare ⊆ U σ ∧
        ContDiffOn ℝ 2 (g σ) (U σ) ∧
        (∀ p ∈ unitSquare, σ (squareCollapse p) = (E.chart (k σ)).symm (g σ p)) ∧
        ∀ p ∈ U σ, ∀ i : Fin 1,
          0 ≤ r σ * FundamentalChartCycle.chartJacobian (g σ) p i) ∧
      (∀ W : Set T, IsOpen W → W.Nonempty →
        ∃ σ ∈ w.support, ∃ p ∈ unitSquare, σ (squareCollapse p) ∈ W ∧ ∀ i : Fin 1,
          0 < r σ * FundamentalChartCycle.chartJacobian (g σ) p i) ∧
      (∃ σ₀ ∈ w.support, ∃ p₀ ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1,
        w σ₀ = 1 ∧ (∀ i : Fin 1, 0 < FundamentalChartCycle.chartJacobian (g σ₀) p₀ i) ∧
        (∀ t, σ₀ t = σ₀ (squareCollapse p₀) → t = squareCollapse p₀) ∧
        ∀ σ ∈ w.support, σ ≠ σ₀ → σ₀ (squareCollapse p₀) ∉ range σ) ∧
      ∀ s ∈ S, (∃ σ ∈ w.support, σ (squareCollapse (0, 0)) = s) ∧
        ∀ σ ∈ w.support, s ∈ range σ →
          s ∈ (E.chart (k σ)).source ∧
          (∃ γ : ℝ → Fin 1 → ℂ, ContDiff ℝ 2 γ ∧
            g σ = CurveCupPositivity.coneMap coneProfile (E.chart (k σ) s) γ) ∧
          ∀ t, σ t = s ↔ t = squareCollapse (0, 0) := by
  obtain ⟨G, hG, hSG, hsmall⟩ := exists_isGood_gridData E S hS B hBo hmem
  set w := sphereChain E G with hwdef
  set r : Simplex T 2 → ℝ := fun σ ↦ (w σ).re
  have hwr : ∀ σ, w σ = r σ := fun σ ↦
    Complex.ext rfl (by simpa [r] using im_sphereChain_apply E G σ)
  have hpos : ∀ σ, PosForm E σ → 0 ≤ r σ := fun σ hσ ↦ by
    obtain ⟨n, hn⟩ := posChain_mem_natChains E G σ
    simp [r, w, sphereChain_apply_of_posForm E G hσ, hn]
  have hpos' : ∀ σ, PosForm E σ → posChain E G σ ≠ 0 → 0 < r σ := fun σ hσ hne ↦ by
    obtain ⟨n, hn⟩ := posChain_mem_natChains E G σ
    have hn0 : n ≠ 0 := by rintro rfl; exact hne (by simp [hn])
    simp only [r, w, sphereChain_apply_of_posForm E G hσ, hn, Complex.natCast_re]
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hsupp : ∀ σ, PosForm E σ → posChain E G σ ≠ 0 → σ ∈ w.support := fun σ hσ hne ↦ by
    rw [Finsupp.mem_support_iff, hwdef, sphereChain_apply_of_posForm E G hσ]; exact hne
  have H : ∀ σ ∈ w.support, ∃ (k : Fin 2) (g : ℝ × ℝ → Fin 1 → ℂ) (U : Set (ℝ × ℝ)),
      IsOpen U ∧ unitSquare ⊆ U ∧ ContDiffOn ℝ 2 g U ∧
      (∀ p ∈ unitSquare, σ (squareCollapse p) = (E.chart k).symm (g p)) ∧
      (∀ p ∈ U, ∀ i, 0 ≤ r σ * FundamentalChartCycle.chartJacobian g p i) ∧
      (PosForm E σ → (∀ p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, ∀ i,
          0 < FundamentalChartCycle.chartJacobian g p i) ∧
        ∃ (P : Fin 1 → ℂ) (γ : ℝ → Fin 1 → ℂ), ContDiff ℝ 2 γ ∧
          g = CurveCupPositivity.coneMap coneProfile P γ) := by
    intro σ hσ
    by_cases hP : PosForm E σ
    · obtain ⟨k, P, γ, U, hγ, hUo, hsU, hg, hread, hJ, hJ'⟩ := exists_reading_of_posForm E hP
      exact ⟨k, _, U, hUo, hsU, hg, hread, fun p hp i ↦ mul_nonneg (hpos σ hP) (hJ p hp i),
        fun _ ↦ ⟨hJ', P, γ, hγ, rfl⟩⟩
    · have hN := (posForm_or_negForm E hG hσ).resolve_left hP
      obtain ⟨k, g, U, hUo, hsU, hg, hread, hJ⟩ := exists_reading_of_negForm E hN
      exact ⟨k, g, U, hUo, hsU, hg, hread, fun p hp i ↦ by rw [hJ p hp i, mul_zero],
        fun h ↦ absurd h hP⟩
  choose! k g U hUo hsU hg hread hJ hJpos using H
  refine ⟨w, r, k, g, U, bd_sphereChain E hG.encloses, fun σ hσ ↦
    ⟨hwr σ, hsmall σ hσ, hUo σ hσ, hsU σ hσ, hg σ hσ, hread σ hσ, hJ σ hσ⟩, ?_, ?_, ?_⟩
  · intro W hW hne
    obtain ⟨σ, hP, hne', p, hp, hpW⟩ := exists_posForm_mem_of_isOpen E hG hW hne
    refine ⟨σ, hsupp σ hP hne', p, ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩, hpW,
      fun i ↦ mul_pos (hpos' σ hP hne') ((hJpos σ (hsupp σ hP hne') hP).1 p hp i)⟩
  · obtain ⟨σ₀, hP, h1, p₀, hp₀, hinj, havoid⟩ := exists_simplePoint E hG
    have hs := hsupp σ₀ hP (by rw [h1]; exact one_ne_zero)
    refine ⟨σ₀, hs, p₀, hp₀, ?_, (hJpos σ₀ hs hP).1 p₀ hp₀, hinj, havoid⟩
    rw [hwdef, sphereChain_apply_of_posForm E G hP, h1]
  · intro s hs
    obtain ⟨⟨σ, hP, hne', hσs⟩, hall⟩ := apex_of_mem E hG hSG s hs
    refine ⟨⟨σ, hsupp σ hP hne', hσs⟩, fun σ hσ hsσ ↦ ?_⟩
    obtain ⟨hPσ, hiff⟩ := hall σ hσ hsσ
    obtain ⟨-, P, γ, hγ, hgσ⟩ := hJpos σ hσ hPσ
    have hσ0 : σ (squareCollapse (0, 0)) = s := (hiff _).2 rfl
    have hs' : (E.chart (k σ)).symm P = s := by
      rw [← hσ0, hread σ hσ _ mem_unitSquare_zero_zero, hgσ]
      simp [CurveCupPositivity.coneMap]
    refine ⟨hs' ▸ symm_mem_source E _ P, ⟨γ, hγ, ?_⟩, hiff⟩
    rw [hgσ, ← hs', (E.chart (k σ)).right_inv (by rw [E.target_eq]; exact mem_univ _)]

end Sphere

/-! ### The fundamental class -/

section FundamentalClass

open CategoryTheory AlgebraicGeometry MMP MMP.SingularCochain
open MMP.FundamentalClass

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]

/-- **A cycle with a simple point of an oriented chart triangle is the fundamental cycle.** On a
smooth projective complex curve `X`, a finite `2`-cycle `z` of `X^an` with a triangle `σ₀` of
coefficient `1`, read in an étale chart as a `C²` map with positive Jacobian at an interior point
`p₀` of the square, injective over `x₀ = σ₀(s(p₀))`, with no other triangle of `z` through `x₀`,
represents the fundamental class of `X`.

The local pairing at `x₀` sees only `σ₀`, which is locally the class of a positively oriented
simplex of the chart at `x₀` of `X_reg(ℂ)`
(`MMP.Analytic.FundamentalChartCycle.exists_eq_of_mem_relCocycles_of_chartRead`); one point
detects the fundamental class
(`MMP.Analytic.FundamentalChartCycle.isVarietyFundamentalClass_finiteCycleClass_of_eval`). -/
theorem isVarietyFundamentalClass_of_simplePoint [IsComplexScheme X] [IsIntegral X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (z : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1) →₀ ℂ) (hz : bd ℂ 1 z = 0)
    {σ₀ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1)} (hσ₀ : σ₀ ∈ z.support)
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1)
    (g : ℝ × ℝ → (Fin 1 → ℂ)) (U : Set (ℝ × ℝ)) (hUo : IsOpen U) (hsq : unitSquare ⊆ U)
    (hg : ContDiffOn ℝ 2 g U) (hgT : MapsTo g U c.toOpenPartialHomeomorph.target)
    (hσ : ∀ p ∈ unitSquare, σ₀ (squareCollapse p) = c.toOpenPartialHomeomorph.symm (g p))
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1) (hz₀ : z σ₀ = 1)
    (hJ : ∀ i : Fin 1, 0 < FundamentalChartCycle.chartJacobian g p₀ i)
    (hinj : ∀ t, σ₀ t = σ₀ (squareCollapse p₀) → t = squareCollapse p₀)
    (hsimple : ∀ σ ∈ z.support, σ ≠ σ₀ → σ₀ (squareCollapse p₀) ∉ range σ) :
    IsVarietyFundamentalClass ℂ (PolarizationPositivity.natCast_one_eq_dimension
        (PolarizationPositivity.topologicalKrullDim_eq_one (X := X)))
      (PolarizationPositivity.finiteCycleClass (Y := TopCat.of (UnderlyingSpace ℂ X))
        (postcomp ℂ ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩ (1 + 1) z)
        (PolarizationPositivity.bd_postcomp_homeomorphUnderlyingSpace_eq_zero hz)) := by
  set hn := PolarizationPositivity.natCast_one_eq_dimension
    (PolarizationPositivity.topologicalKrullDim_eq_one (X := X))
  obtain ⟨x, hx, v, hv, hvt, Δ, hΔ, hloc⟩ :=
    FundamentalChartCycle.exists_eq_of_mem_relCocycles_of_chartRead hn σ₀ c g U hUo hsq hg hgT
      hσ hp₀ hJ hinj
  set f : C(Analytification.space (X ↘ Spec (.of ℂ)), TopCat.of (UnderlyingSpace ℂ X)) :=
    ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩
  refine FundamentalChartCycle.isVarietyFundamentalClass_finiteCycleClass_of_eval hn _ _ x hv
    hvt Δ hΔ fun φ hφ ↦ ?_
  rw [PolarizationPositivity.eval_postcomp, ← hloc φ hφ, SingularCochain.eval,
    Finsupp.linearCombination_apply,
    Finsupp.sum_eq_single σ₀ (fun σ hσ hne ↦ ?_) (fun _ ↦ zero_smul _ _), hz₀, one_smul]
  rw [hφ.1 (f.comp σ) ?_, smul_zero]
  rintro _ ⟨t, rfl⟩ hmemx
  apply hsimple σ (Finsupp.mem_support_iff.2 hσ) hne ⟨t, ?_⟩
  have : f (σ t) = f (σ₀ (squareCollapse p₀)) := (Set.mem_singleton_iff.1 hmemx).trans hx
  exact (ComplexPoints.homeomorphUnderlyingSpace (X := X)).injective this

end FundamentalClass

end MMP.Analytic.ChartConeCellulation
