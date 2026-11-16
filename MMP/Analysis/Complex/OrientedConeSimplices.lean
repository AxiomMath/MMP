module

public import MMP.AlgebraicTopology.SingularHomology.Excision.SmallChains
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Oriented cone simplices for fundamental cycles of Riemann surfaces

To compute `i ∫_X ω ∧ ω̄` on a compact Riemann surface `X` through a singular `2`-cycle, the cycle
is made of triangles read, through the collapse `s : [0, 1]² → Δ²` of the unit square onto the
standard triangle, as `C²` maps `g` from a neighbourhood of `[0, 1]²` into a chart, with Jacobian
`Im (\overline{∂₁ g} ∂₂ g)` of one sign on that neighbourhood.

The collapse sends the edge `x = 0` of the square to a vertex, so `∂₂ g` vanishes there and the
Jacobian of `g` vanishes along `x = 0`. For an affine triangle, `g (x, y) = A + x (B - A) +
x y (C - B)` has Jacobian `x Im (\overline{B - A} (C - B))`, which changes sign across `x = 0`: a
nondegenerate affine triangle has no such reading. The triangles used here are *cones* with a
flat radial profile: for a point `P` and a curve `γ`, the map
`g (x, y) = P + ρ(x) (γ(y) - P)`, with `ρ = exp(-1/x) / exp(-1)` for `x > 0` and `ρ = 0` for
`x ≤ 0`, is smooth in `x` and has Jacobian `ρ ρ' Im (\overline{γ - P} γ')`, nonnegative
everywhere when `γ` turns counterclockwise around `P`, and positive for `x > 0` where it turns
strictly.

The boundary of the cone over `γ` is the path `γ` minus the radial segment to `γ(1)` plus the
radial segment to `γ(0)`; the radial segments of the cones over consecutive arcs of a loop
cancel. A path and its reverse add up to the boundary of two degenerate triangles (the fold of
the path and a constant), whose Jacobians vanish identically.

## Main definitions

* `MMP.Analytic.CurveCupPositivity.coneProfile`: the flat radial profile `ρ`.
* `MMP.Analytic.CurveCupPositivity.coneMap`: the map `(x, y) ↦ P + ρ(x) (γ(y) - P)`.
* `MMP.Analytic.CurveCupPositivity.squareCollapse`: the collapse `[0, 1]² → Δ²`.
* `MMP.Analytic.CurveCupPositivity.foldMap`, `reverseCurve`: the fold and the reverse of a curve.
* `MMP.Analytic.CurveCupPositivity.coneSimplex`, `pathSimplex`, `radialSimplex`,
  `foldSimplex`: singular simplices of a normed space.
* `MMP.Analytic.CurveCupPositivity.mapSimplex`: a singular simplex pushed along a map continuous
  on a set containing its image (an inverse chart).

## Main results

* `MMP.Analytic.CurveCupPositivity.im_star_fderiv_coneMap`: the Jacobian of a cone.
* `MMP.Analytic.CurveCupPositivity.coneSimplex_squareCollapse`: the cone simplex read on the
  square is the cone map.
* `MMP.Analytic.CurveCupPositivity.bd_single_coneSimplex`,
  `MMP.Analytic.CurveCupPositivity.bd_single_foldSimplex`: their boundaries.
* `MMP.Analytic.CurveCupPositivity.single_pathSimplex_add_reverse`: a path plus its reverse is a
  boundary.
* `MMP.Analytic.CurveCupPositivity.exists_reading_coneSimplex`,
  `MMP.Analytic.CurveCupPositivity.exists_reading_foldSimplex`: their readings in a chart.
* `MMP.Analytic.CurveCupPositivity.bd_sum_single_mapSimplex_coneSimplex`: the boundary of the
  cones over a loop is the sum of their `0`-th faces, the pushed arcs.
-/

@[expose] public noncomputable section

open Set Finsupp MMP.SingularChain

namespace MMP.Analytic.CurveCupPositivity

/-! ### The flat radial profile -/

section Profile

/-- The flat radial profile `ρ(x) = exp(-1/x) / exp(-1)` for `x > 0`, `0` for `x ≤ 0`: smooth,
`ρ(0) = 0`, `ρ(1) = 1`, with `ρ ρ' ≥ 0` everywhere and `ρ, ρ' > 0` on `x > 0`. -/
def coneProfile (x : ℝ) : ℝ := expNegInvGlue x / expNegInvGlue 1

/-- The value `expNegInvGlue 1 = exp(-1)` is positive. -/
theorem expNegInvGlue_one_pos : 0 < expNegInvGlue 1 := expNegInvGlue.pos_of_pos one_pos

/-- The flat radial profile is `Cⁿ` for every finite `n`. -/
theorem contDiff_coneProfile {n : WithTop ℕ∞} (hn : n ≠ ⊤) : ContDiff ℝ n coneProfile := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ∞, n = m := by
    induction n with
    | top => exact absurd rfl hn
    | coe m => exact ⟨m, rfl⟩
  exact expNegInvGlue.contDiff.div_const _

/-- The flat radial profile is continuous. -/
theorem continuous_coneProfile : Continuous coneProfile :=
  (contDiff_coneProfile (n := 0) (by simp)).continuous

/-- The flat radial profile is differentiable. -/
theorem differentiable_coneProfile : Differentiable ℝ coneProfile :=
  (contDiff_coneProfile (n := 1) (by simp)).differentiable (by simp)

/-- `ρ(0) = 0`. -/
@[simp]
theorem coneProfile_zero : coneProfile 0 = 0 := by
  simp [coneProfile, expNegInvGlue.zero_of_nonpos le_rfl]

/-- `ρ(1) = 1`. -/
@[simp]
theorem coneProfile_one : coneProfile 1 = 1 := div_self expNegInvGlue_one_pos.ne'

/-- The flat radial profile is nonnegative. -/
theorem coneProfile_nonneg (x : ℝ) : 0 ≤ coneProfile x :=
  div_nonneg (expNegInvGlue.nonneg x) expNegInvGlue_one_pos.le

/-- The flat radial profile is positive on `x > 0`. -/
theorem coneProfile_pos {x : ℝ} (hx : 0 < x) : 0 < coneProfile x :=
  div_pos (expNegInvGlue.pos_of_pos hx) expNegInvGlue_one_pos

/-- For `x > 0`, the derivative of `ρ` at `x` is `exp(-1/x) x⁻² / exp(-1)`. -/
theorem hasDerivAt_coneProfile_of_pos {x : ℝ} (hx : 0 < x) :
    HasDerivAt coneProfile (Real.exp (-x⁻¹) * (x ^ 2)⁻¹ / expNegInvGlue 1) x := by
  have h : expNegInvGlue =ᶠ[nhds x] fun y ↦ Real.exp (-y⁻¹) := by
    filter_upwards [lt_mem_nhds hx] with y hy
    simp [expNegInvGlue, not_le.2 hy]
  have hd : HasDerivAt (fun y ↦ Real.exp (-y⁻¹)) (Real.exp (-x⁻¹) * (x ^ 2)⁻¹) x := by
    have := ((hasDerivAt_inv hx.ne').neg).exp
    convert this using 1
    simp
  exact (hd.congr_of_eventuallyEq h).div_const _

/-- The derivative `ρ'` is positive on `x > 0`. -/
theorem deriv_coneProfile_pos {x : ℝ} (hx : 0 < x) : 0 < deriv coneProfile x := by
  rw [(hasDerivAt_coneProfile_of_pos hx).deriv]
  have := expNegInvGlue_one_pos
  positivity

/-- `ρ ρ' > 0` on `x > 0`. -/
theorem coneProfile_mul_deriv_pos {x : ℝ} (hx : 0 < x) :
    0 < coneProfile x * deriv coneProfile x :=
  mul_pos (coneProfile_pos hx) (deriv_coneProfile_pos hx)

/-- `ρ ρ' ≥ 0` everywhere. -/
theorem coneProfile_mul_deriv_nonneg (x : ℝ) : 0 ≤ coneProfile x * deriv coneProfile x := by
  rcases le_or_gt x 0 with hx | hx
  · simp [coneProfile, expNegInvGlue.zero_of_nonpos hx]
  · exact (coneProfile_mul_deriv_pos hx).le

end Profile

/-! ### Cone maps and their Jacobians -/

section ConeMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cone `(x, y) ↦ P + ρ(x) (γ(y) - P)` from `P` over the curve `γ`, with radial profile
`ρ`. -/
def coneMap (ρ : ℝ → ℝ) (P : E) (γ : ℝ → E) (p : ℝ × ℝ) : E :=
  P + ρ p.1 • (γ p.2 - P)

/-- The value of the cone map at `p`. -/
theorem coneMap_apply (ρ : ℝ → ℝ) (P : E) (γ : ℝ → E) (p : ℝ × ℝ) :
    coneMap ρ P γ p = P + ρ p.1 • (γ p.2 - P) :=
  rfl

/-- If `ρ` is `Cᵏ` and `γ` is `Cᵏ` on `V`, the cone map is `Cᵏ` on `ℝ × V`. -/
theorem contDiffOn_coneMap {k : WithTop ℕ∞} {ρ : ℝ → ℝ} {P : E} {γ : ℝ → E} {V : Set ℝ}
    (hρ : ContDiff ℝ k ρ) (hγ : ContDiffOn ℝ k γ V) :
    ContDiffOn ℝ k (coneMap ρ P γ) (univ ×ˢ V) := by
  refine contDiffOn_const.add (ContDiffOn.smul (hρ.comp_contDiffOn contDiffOn_fst) ?_)
  exact (hγ.comp contDiffOn_snd fun p hp ↦ hp.2).sub contDiffOn_const

/-- The derivative of the cone map at `(x, y)` sends `(a, b)` to
`a ρ'(x) (γ(y) - P) + b ρ(x) γ'(y)`. -/
theorem hasFDerivAt_coneMap {ρ : ℝ → ℝ} {P : E} {γ : ℝ → E} {x y ρ' : ℝ} {γ' : E}
    (hρ : HasDerivAt ρ ρ' x) (hγ : HasDerivAt γ γ' y) :
    HasFDerivAt (coneMap ρ P γ)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ρ' • (γ y - P)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ρ x • γ')) (x, y) := by
  have h1 : HasFDerivAt (fun p : ℝ × ℝ ↦ ρ p.1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight ρ') (x, y) :=
    (hρ.hasFDerivAt.comp (x, y) (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, y)))).congr_fderiv
      (by ext <;> simp)
  have h2 : HasFDerivAt (fun p : ℝ × ℝ ↦ γ p.2 - P)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight γ') (x, y) :=
    ((hγ.hasFDerivAt.comp (x, y) (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y)))).sub_const
      P).congr_fderiv (by ext <;> simp)
  have h3 : HasFDerivAt (coneMap ρ P γ) _ (x, y) := (h1.smul h2).const_add P
  exact h3.congr_fderiv (by ext <;> simp [smul_smul, mul_comm])

/-- The partial derivative `∂₁` of the cone map at `(x, y)` is `ρ'(x) (γ(y) - P)`. -/
theorem fderiv_coneMap_one_zero {ρ : ℝ → ℝ} {P : E} {γ : ℝ → E} {x y : ℝ}
    (hρ : DifferentiableAt ℝ ρ x) (hγ : DifferentiableAt ℝ γ y) :
    fderiv ℝ (coneMap ρ P γ) (x, y) (1, 0) = deriv ρ x • (γ y - P) := by
  rw [(hasFDerivAt_coneMap (P := P) hρ.hasDerivAt hγ.hasDerivAt).fderiv]
  simp

/-- The partial derivative `∂₂` of the cone map at `(x, y)` is `ρ(x) γ'(y)`. -/
theorem fderiv_coneMap_zero_one {ρ : ℝ → ℝ} {P : E} {γ : ℝ → E} {x y : ℝ}
    (hρ : DifferentiableAt ℝ ρ x) (hγ : DifferentiableAt ℝ γ y) :
    fderiv ℝ (coneMap ρ P γ) (x, y) (0, 1) = ρ x • deriv γ y := by
  rw [(hasFDerivAt_coneMap (P := P) hρ.hasDerivAt hγ.hasDerivAt).fderiv]
  simp

/-- For real `a, b` and complex `u, v`, `Im (a ū (b v)) = b a Im (ū v)`. -/
theorem im_ofReal_mul_star_mul_ofReal_mul (a b : ℝ) (u v : ℂ) :
    ((a : ℂ) * star u * ((b : ℂ) * v)).im = b * a * (star u * v).im := by
  rw [show (a : ℂ) * star u * ((b : ℂ) * v) = ((b * a : ℝ) : ℂ) * (star u * v) by
    push_cast; ring, Complex.im_ofReal_mul]

/-- **The Jacobian of a cone.** In each complex coordinate, the Jacobian
`Im (\overline{∂₁ g} ∂₂ g)` of the cone `g (x, y) = P + ρ(x) (γ(y) - P)` is
`ρ(x) ρ'(x) Im (\overline{γ(y) - P} γ'(y))`. -/
theorem im_star_fderiv_coneMap {n : ℕ} {ρ : ℝ → ℝ} {P : Fin n → ℂ} {γ : ℝ → Fin n → ℂ}
    {x y : ℝ} (hρ : DifferentiableAt ℝ ρ x) (hγ : DifferentiableAt ℝ γ y) (i : Fin n) :
    (star (fderiv ℝ (coneMap ρ P γ) (x, y) (1, 0) i) *
        fderiv ℝ (coneMap ρ P γ) (x, y) (0, 1) i).im =
      ρ x * deriv ρ x * (star (γ y i - P i) * deriv γ y i).im := by
  rw [fderiv_coneMap_one_zero hρ hγ, fderiv_coneMap_zero_one hρ hγ]
  simp only [Pi.smul_apply, Pi.sub_apply, Complex.real_smul, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  exact im_ofReal_mul_star_mul_ofReal_mul _ _ _ _

/-- **Cones with the flat profile are oriented.** If `γ` turns counterclockwise around `P` in
the coordinate `i`, the Jacobian of the cone with profile `coneProfile` is nonnegative. -/
theorem im_star_fderiv_coneMap_nonneg {n : ℕ} {P : Fin n → ℂ} {γ : ℝ → Fin n → ℂ} {x y : ℝ}
    (hγ : DifferentiableAt ℝ γ y) (i : Fin n) (hturn : 0 ≤ (star (γ y i - P i) * deriv γ y i).im) :
    0 ≤ (star (fderiv ℝ (coneMap coneProfile P γ) (x, y) (1, 0) i) *
        fderiv ℝ (coneMap coneProfile P γ) (x, y) (0, 1) i).im := by
  rw [im_star_fderiv_coneMap (differentiable_coneProfile x) hγ]
  exact mul_nonneg (coneProfile_mul_deriv_nonneg x) hturn

/-- If `γ` turns strictly counterclockwise around `P` in the coordinate `i`, the Jacobian of the
cone with profile `coneProfile` is positive at every `(x, y)` with `x > 0`. -/
theorem im_star_fderiv_coneMap_pos {n : ℕ} {P : Fin n → ℂ} {γ : ℝ → Fin n → ℂ} {x y : ℝ}
    (hx : 0 < x) (hγ : DifferentiableAt ℝ γ y) (i : Fin n)
    (hturn : 0 < (star (γ y i - P i) * deriv γ y i).im) :
    0 < (star (fderiv ℝ (coneMap coneProfile P γ) (x, y) (1, 0) i) *
        fderiv ℝ (coneMap coneProfile P γ) (x, y) (0, 1) i).im := by
  rw [im_star_fderiv_coneMap (differentiable_coneProfile x) hγ]
  exact mul_pos (coneProfile_mul_deriv_pos hx) hturn

/-- The fold `(x, y) ↦ γ (x (1 - y))` of a curve: a map of rank at most one. -/
def foldMap (γ : ℝ → E) (p : ℝ × ℝ) : E := γ (p.1 * (1 - p.2))

/-- The value of the fold of `γ` at `p` is `γ (p₁ (1 - p₂))`. -/
theorem foldMap_apply (γ : ℝ → E) (p : ℝ × ℝ) : foldMap γ p = γ (p.1 * (1 - p.2)) :=
  rfl

/-- If `γ` is `Cᵏ` on `V`, its fold is `Cᵏ` on the preimage of `V` under
`(x, y) ↦ x (1 - y)`. -/
theorem contDiffOn_foldMap {k : WithTop ℕ∞} {γ : ℝ → E} {V : Set ℝ} (hγ : ContDiffOn ℝ k γ V) :
    ContDiffOn ℝ k (foldMap γ) ((fun p : ℝ × ℝ ↦ p.1 * (1 - p.2)) ⁻¹' V) :=
  hγ.comp (by fun_prop) fun _ hp ↦ hp

/-- **The fold has zero Jacobian.** -/
theorem im_star_fderiv_foldMap {n : ℕ} {γ : ℝ → Fin n → ℂ} {x y : ℝ}
    (hγ : DifferentiableAt ℝ γ (x * (1 - y))) (i : Fin n) :
    (star (fderiv ℝ (foldMap γ) (x, y) (1, 0) i) * fderiv ℝ (foldMap γ) (x, y) (0, 1) i).im =
      0 := by
  have hm : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 * (1 - p.2))
      ((1 - y) • ContinuousLinearMap.fst ℝ ℝ ℝ - x • ContinuousLinearMap.snd ℝ ℝ ℝ) (x, y) :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := (x, y))).mul
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y))).const_sub 1)).congr_fderiv (by ext <;> simp)
  have hc := hγ.hasDerivAt.hasFDerivAt.comp (x, y) hm.differentiableAt.hasFDerivAt
  rw [show foldMap γ = γ ∘ fun p : ℝ × ℝ ↦ p.1 * (1 - p.2) from rfl, hc.fderiv]
  have e1 : fderiv ℝ (fun p : ℝ × ℝ ↦ p.1 * (1 - p.2)) (x, y) (1, 0) = 1 - y := by
    rw [hm.fderiv]; simp
  have e2 : fderiv ℝ (fun p : ℝ × ℝ ↦ p.1 * (1 - p.2)) (x, y) (0, 1) = -x := by
    rw [hm.fderiv]; simp
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.toSpanSingleton_apply, e1, e2, Pi.smul_apply, Complex.real_smul,
    star_mul', Complex.star_def, Complex.conj_ofReal]
  simp only [Complex.mul_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

end ConeMap

/-! ### The collapse of the square and the faces of `Δ²` -/

section Collapse

/-- The point `(1 - x, x (1 - y), x y)` of `Δ²`, for `x, y` clamped to `[0, 1]`: the collapse of
the unit square onto the standard triangle, the edge `x = 0` going to the vertex `0`. -/
def squareCollapse (p : ℝ × ℝ) : stdSimplex ℝ (Fin 3) :=
  ⟨![1 - (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ),
      (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) *
        (1 - (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)),
      (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) *
        (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)], by
    have hx := (Set.projIcc (0 : ℝ) 1 zero_le_one p.1).2
    have hy := (Set.projIcc (0 : ℝ) 1 zero_le_one p.2).2
    refine ⟨fun i ↦ ?_, ?_⟩
    · fin_cases i
      · show 0 ≤ 1 - (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ)
        linarith [hx.2]
      · show 0 ≤ (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) *
          (1 - (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ))
        exact mul_nonneg hx.1 (by linarith [hy.2])
      · show 0 ≤ (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) *
          (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)
        exact mul_nonneg hx.1 hy.1
    · rw [Fin.sum_univ_three]
      show 1 - (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) +
        (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) *
          (1 - (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)) +
        (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) *
          (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ) = 1
      ring⟩

/-- The projection onto `[0, 1]` fixes the points of `[0, 1]`. -/
theorem coe_projIcc_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) = t := by
  rw [Set.projIcc_of_mem _ ht]

/-- On the unit square, the coordinate `1` of `squareCollapse (x, y)` is `x (1 - y)`. -/
theorem squareCollapse_apply_one {p : ℝ × ℝ} (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    squareCollapse p 1 = p.1 * (1 - p.2) := by
  show (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) *
    (1 - (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ)) = _
  rw [coe_projIcc_of_mem hp.1, coe_projIcc_of_mem hp.2]

/-- On the unit square, the coordinate `2` of `squareCollapse (x, y)` is `x y`. -/
theorem squareCollapse_apply_two {p : ℝ × ℝ} (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    squareCollapse p 2 = p.1 * p.2 := by
  show (Set.projIcc (0 : ℝ) 1 zero_le_one p.1 : ℝ) *
    (Set.projIcc (0 : ℝ) 1 zero_le_one p.2 : ℝ) = _
  rw [coe_projIcc_of_mem hp.1, coe_projIcc_of_mem hp.2]

/-- On the unit square, `x (1 - y) ∈ [0, 1]`. -/
theorem mul_one_sub_mem_Icc {p : ℝ × ℝ} (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    p.1 * (1 - p.2) ∈ Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg hp.1.1 (by linarith [hp.2.2]), by
    calc p.1 * (1 - p.2) ≤ 1 * 1 :=
          mul_le_mul hp.1.2 (by linarith [hp.2.1]) (by linarith [hp.2.2]) zero_le_one
      _ = 1 := one_mul 1⟩

/-- The coordinates of a point of `Δ¹` sum to `1`. -/
theorem stdSimplex_two_add (x : stdSimplex ℝ (Fin 2)) : x 0 + x 1 = 1 :=
  stdSimplex.add_eq_one x

/-- The coordinates of a point of `Δ²` sum to `1`. -/
theorem stdSimplex_three_add (t : stdSimplex ℝ (Fin 3)) : t 0 + t 1 + t 2 = 1 := by
  have := t.2.2
  rw [Fin.sum_univ_three] at this
  exact this

/-- The coordinates of a point of the standard simplex are nonnegative. -/
theorem stdSimplex_apply_nonneg {m : ℕ} (x : stdSimplex ℝ (Fin m)) (i : Fin m) : 0 ≤ x i :=
  x.2.1 i

/-- Each coordinate is a continuous function on the standard simplex. -/
theorem stdSimplex_continuous_apply {m : ℕ} (i : Fin m) :
    Continuous fun x : stdSimplex ℝ (Fin m) ↦ x i :=
  (continuous_apply i).comp continuous_subtype_val

/-- The coordinate `1` of the image of a point of `Δ¹` under the `k`-th face map into `Δ²`. -/
theorem face_apply_one (k : Fin 3) (x : stdSimplex ℝ (Fin 2)) :
    (face 1 k x) 1 = if k = 0 then x 0 else if k = 1 then 0 else x 1 := by
  fin_cases k <;>
  · simp only [face, ContinuousMap.coe_mk, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_filter, Fin.sum_univ_two]
    simp [Fin.succAbove, Fin.lt_def]

/-- The coordinate `2` of the image of a point of `Δ¹` under the `k`-th face map into `Δ²`. -/
theorem face_apply_two (k : Fin 3) (x : stdSimplex ℝ (Fin 2)) :
    (face 1 k x) 2 = if k = 2 then 0 else x 1 := by
  fin_cases k <;>
  · simp only [face, ContinuousMap.coe_mk, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_filter, Fin.sum_univ_two]
    simp [Fin.succAbove, Fin.lt_def]

/-- The coordinate `1` of the `0`-th face of `x ∈ Δ¹` is `x₀`. -/
theorem face_zero_apply_one (x : stdSimplex ℝ (Fin 2)) : (face 1 0 x) 1 = x 0 := by
  rw [face_apply_one]; simp

/-- The coordinate `2` of the `0`-th face of `x ∈ Δ¹` is `x₁`. -/
theorem face_zero_apply_two (x : stdSimplex ℝ (Fin 2)) : (face 1 0 x) 2 = x 1 := by
  rw [face_apply_two]; simp

/-- The coordinate `1` of the `1`-st face of `x ∈ Δ¹` is `0`. -/
theorem face_one_apply_one (x : stdSimplex ℝ (Fin 2)) : (face 1 1 x) 1 = 0 := by
  rw [face_apply_one]; simp

/-- The coordinate `2` of the `1`-st face of `x ∈ Δ¹` is `x₁`. -/
theorem face_one_apply_two (x : stdSimplex ℝ (Fin 2)) : (face 1 1 x) 2 = x 1 := by
  rw [face_apply_two]; simp

/-- The coordinate `1` of the `2`-nd face of `x ∈ Δ¹` is `x₁`. -/
theorem face_two_apply_one (x : stdSimplex ℝ (Fin 2)) : (face 1 2 x) 1 = x 1 := by
  rw [face_apply_one]; simp

/-- The coordinate `2` of the `2`-nd face of `x ∈ Δ¹` is `0`. -/
theorem face_two_apply_two (x : stdSimplex ℝ (Fin 2)) : (face 1 2 x) 2 = 0 := by
  rw [face_apply_two]; simp

end Collapse

/-! ### Cone, path, radial and fold simplices -/

section Simplices

/-- The boundary of a singular triangle. -/
theorem bd_single_two {R : Type*} [CommRing R] {Z : Type*} [TopologicalSpace Z]
    (σ : Simplex Z 2) :
    bd R 1 (single σ 1) = single (σ.comp (face 1 0)) 1 - single (σ.comp (face 1 1)) 1 +
      single (σ.comp (face 1 2)) 1 := by
  rw [bd_single, Fin.sum_univ_three]
  simp [sub_eq_add_neg]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve `γ` clamped to `[0, 1]`: `r ↦ γ (max 0 (min 1 r))`. -/
def clampCurve (γ : ℝ → E) (r : ℝ) : E := γ (Set.projIcc (0 : ℝ) 1 zero_le_one r)

/-- The clamped curve agrees with `γ` on `[0, 1]`. -/
theorem clampCurve_of_mem (γ : ℝ → E) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    clampCurve γ r = γ r := by
  rw [clampCurve, coe_projIcc_of_mem hr]

/-- A curve continuous on `[0, 1]` clamps to a continuous curve on `ℝ`. -/
theorem continuous_clampCurve {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) :
    Continuous (clampCurve γ) :=
  hγ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun r ↦
    (Set.projIcc (0 : ℝ) 1 zero_le_one r).2

/-- For `γ` continuous on `[0, 1]`, the distance from `P` to the clamped curve is bounded. -/
theorem exists_norm_clampCurve_sub_le {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) (P : E) :
    ∃ M, ∀ r, ‖clampCurve γ r - P‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hγ).isBounded.exists_norm_le
  refine ⟨M + ‖P‖, fun r ↦ ?_⟩
  have := hM _ ⟨_, (Set.projIcc (0 : ℝ) 1 zero_le_one r).2, rfl⟩
  calc ‖clampCurve γ r - P‖ ≤ ‖clampCurve γ r‖ + ‖P‖ := norm_sub_le _ _
    _ ≤ M + ‖P‖ := by gcongr; exact this

/-- The value at `t ∈ Δ²` of the cone from `P` over `γ`: radius `t₁ + t₂`, angle
`t₂ / (t₁ + t₂)`. -/
def coneValue (ρ : ℝ → ℝ) (P : E) (γ : ℝ → E) (t : stdSimplex ℝ (Fin 3)) : E :=
  P + ρ (t 1 + t 2) • (clampCurve γ (t 2 / (t 1 + t 2)) - P)

/-- For `ρ` continuous with `ρ(0) = 0` and `γ` continuous on `[0, 1]`, the cone value is a
continuous function on `Δ²`. -/
theorem continuous_coneValue {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) (P : E)
    {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) : Continuous (coneValue ρ P γ) := by
  have hs : Continuous fun t : stdSimplex ℝ (Fin 3) ↦ t 1 + t 2 :=
    (stdSimplex_continuous_apply 1).add (stdSimplex_continuous_apply 2)
  have hc := continuous_clampCurve hγ
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  by_cases h0 : t 1 + t 2 = 0
  · obtain ⟨M, hM⟩ := exists_norm_clampCurve_sub_le hγ P
    have hv : coneValue ρ P γ t = P + 0 := by simp [coneValue, h0, hρ0]
    rw [ContinuousAt, hv]
    refine tendsto_const_nhds.add ?_
    have hρt : Filter.Tendsto (fun τ : stdSimplex ℝ (Fin 3) ↦ ρ (τ 1 + τ 2)) (nhds t) (nhds 0) := by
      have := (hρ.tendsto _).comp (hs.tendsto t)
      rwa [Function.comp_def, h0, hρ0] at this
    refine hρt.zero_smul_isBoundedUnder_le ?_
    exact Filter.isBoundedUnder_of ⟨M, fun τ ↦ hM _⟩
  · refine continuousAt_const.add (ContinuousAt.smul (hρ.continuousAt.comp hs.continuousAt) ?_)
    refine (hc.continuousAt.comp ?_).sub continuousAt_const
    exact ((stdSimplex_continuous_apply 2).continuousAt.div hs.continuousAt h0)

/-- The singular `2`-simplex `t ↦ P + ρ(t₁ + t₂) (γ (t₂ / (t₁ + t₂)) - P)` of `E`: the cone from
`P` over `γ`, with radial profile `ρ`. -/
def coneSimplex {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) (P : E) {γ : ℝ → E}
    (hγ : ContinuousOn γ (Icc 0 1)) : Simplex E 2 :=
  ⟨coneValue ρ P γ, continuous_coneValue hρ hρ0 P hγ⟩

/-- The singular `1`-simplex `t ↦ γ (t₁)` of `E`. -/
def pathSimplex {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) : Simplex E 1 :=
  ⟨fun t ↦ clampCurve γ (t 1), (continuous_clampCurve hγ).comp (stdSimplex_continuous_apply 1)⟩

/-- The radial singular `1`-simplex `t ↦ P + ρ(t₁) (v - P)` of `E`. -/
def radialSimplex {ρ : ℝ → ℝ} (hρ : Continuous ρ) (P v : E) : Simplex E 1 :=
  ⟨fun t ↦ P + ρ (t 1) • (v - P),
    continuous_const.add ((hρ.comp (stdSimplex_continuous_apply (m := 2) 1)).smul
      continuous_const)⟩

/-- The degenerate singular `2`-simplex `t ↦ γ (t₁)` of `E`, the fold of the path `γ`. -/
def foldSimplex {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) : Simplex E 2 :=
  ⟨fun t ↦ clampCurve γ (t 1), (continuous_clampCurve hγ).comp (stdSimplex_continuous_apply 1)⟩

/-- The constant singular `k`-simplex. -/
def constSimplex (k : ℕ) (v : E) : Simplex E k := ContinuousMap.const _ v

/-- The value of the path simplex at `t ∈ Δ¹`. -/
@[simp]
theorem pathSimplex_apply {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1))
    (t : stdSimplex ℝ (Fin 2)) : pathSimplex hγ t = clampCurve γ (t 1) :=
  rfl

/-- The value of the radial simplex at `t ∈ Δ¹`. -/
@[simp]
theorem radialSimplex_apply {ρ : ℝ → ℝ} (hρ : Continuous ρ) (P v : E)
    (t : stdSimplex ℝ (Fin 2)) : radialSimplex hρ P v t = P + ρ (t 1) • (v - P) :=
  rfl

/-- The value of the fold simplex at `t ∈ Δ²`. -/
@[simp]
theorem foldSimplex_apply {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1))
    (t : stdSimplex ℝ (Fin 3)) : foldSimplex hγ t = clampCurve γ (t 1) :=
  rfl

/-- The value of a constant simplex. -/
@[simp]
theorem constSimplex_apply (k : ℕ) (v : E) (t : stdSimplex ℝ (Fin (k + 1))) :
    constSimplex k v t = v :=
  rfl

/-- The value of the cone simplex at `t ∈ Δ²`. -/
@[simp]
theorem coneSimplex_apply {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) (P : E) {γ : ℝ → E}
    (hγ : ContinuousOn γ (Icc 0 1)) (t : stdSimplex ℝ (Fin 3)) :
    coneSimplex hρ hρ0 P hγ t = P + ρ (t 1 + t 2) • (clampCurve γ (t 2 / (t 1 + t 2)) - P) :=
  rfl

/-- **The cone simplex read on the square is the cone map.** -/
theorem coneSimplex_squareCollapse {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) (P : E)
    {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) {p : ℝ × ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    coneSimplex hρ hρ0 P hγ (squareCollapse p) = coneMap ρ P γ p := by
  rw [coneSimplex_apply, squareCollapse_apply_one hp, squareCollapse_apply_two hp, coneMap_apply]
  have hs : p.1 * (1 - p.2) + p.1 * p.2 = p.1 := by ring
  rw [hs]
  rcases eq_or_ne p.1 0 with h0 | h0
  · simp [h0, hρ0]
  · rw [mul_div_cancel_left₀ _ h0, clampCurve_of_mem γ hp.2]

/-- For `ρ(1) = 1`, the `0`-th face of the cone simplex is the path `γ`. -/
theorem coneSimplex_comp_face_zero {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0)
    (hρ1 : ρ 1 = 1) (P : E) {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) :
    (coneSimplex hρ hρ0 P hγ).comp (face 1 0) = pathSimplex hγ := by
  ext t
  simp only [ContinuousMap.comp_apply, coneSimplex_apply, face_zero_apply_one,
    face_zero_apply_two, stdSimplex_two_add, div_one, hρ1, one_smul, add_sub_cancel]
  rfl

/-- The `1`-st face of the cone simplex is the radial segment from `P` to `γ(1)`. -/
theorem coneSimplex_comp_face_one {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) (P : E)
    {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) :
    (coneSimplex hρ hρ0 P hγ).comp (face 1 1) = radialSimplex hρ P (γ 1) := by
  ext t
  simp only [ContinuousMap.comp_apply, coneSimplex_apply, face_one_apply_one,
    face_one_apply_two, zero_add]
  show P + ρ (t 1) • (clampCurve γ (t 1 / t 1) - P) = P + ρ (t 1) • (γ 1 - P)
  rcases eq_or_ne (t 1) 0 with h0 | h0
  · simp [h0, hρ0]
  · rw [div_self h0, clampCurve_of_mem γ ⟨zero_le_one, le_rfl⟩]

/-- The `2`-nd face of the cone simplex is the radial segment from `P` to `γ(0)`. -/
theorem coneSimplex_comp_face_two {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρ0 : ρ 0 = 0) (P : E)
    {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) :
    (coneSimplex hρ hρ0 P hγ).comp (face 1 2) = radialSimplex hρ P (γ 0) := by
  ext t
  simp only [ContinuousMap.comp_apply, coneSimplex_apply, face_two_apply_one,
    face_two_apply_two, add_zero, zero_div]
  show P + ρ (t 1) • (clampCurve γ 0 - P) = P + ρ (t 1) • (γ 0 - P)
  rw [clampCurve_of_mem γ ⟨le_rfl, zero_le_one⟩]

/-- **The boundary of a cone**: the path `γ`, minus the radial segment to `γ(1)`, plus the
radial segment to `γ(0)`. -/
theorem bd_single_coneSimplex {R : Type*} [CommRing R] {ρ : ℝ → ℝ} (hρ : Continuous ρ)
    (hρ0 : ρ 0 = 0) (hρ1 : ρ 1 = 1) (P : E) {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) :
    bd R 1 (single (coneSimplex hρ hρ0 P hγ) 1) =
      single (pathSimplex hγ) 1 - single (radialSimplex hρ P (γ 1)) 1 +
        single (radialSimplex hρ P (γ 0)) 1 := by
  rw [bd_single_two, coneSimplex_comp_face_zero hρ hρ0 hρ1, coneSimplex_comp_face_one,
    coneSimplex_comp_face_two]

/-- The reverse `r ↦ γ (1 - r)` of a curve. -/
def reverseCurve (γ : ℝ → E) (r : ℝ) : E := γ (1 - r)

/-- The value of the reverse of `γ` at `r` is `γ (1 - r)`. -/
theorem reverseCurve_apply (γ : ℝ → E) (r : ℝ) : reverseCurve γ r = γ (1 - r) :=
  rfl

/-- The reverse of a curve continuous on `[0, 1]` is continuous on `[0, 1]`. -/
theorem continuousOn_reverseCurve {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) :
    ContinuousOn (reverseCurve γ) (Icc 0 1) :=
  hγ.comp (by fun_prop) fun r hr ↦ ⟨by linarith [hr.2], by linarith [hr.1]⟩

/-- **The boundary of a fold**: the reversed path, minus a constant, plus the path. -/
theorem bd_single_foldSimplex {R : Type*} [CommRing R] {γ : ℝ → E}
    (hγ : ContinuousOn γ (Icc 0 1)) :
    bd R 1 (single (foldSimplex hγ) 1) =
      single (pathSimplex (continuousOn_reverseCurve hγ)) 1 - single (constSimplex 1 (γ 0)) 1 +
        single (pathSimplex hγ) 1 := by
  have e0 : (foldSimplex hγ).comp (face 1 0) = pathSimplex (continuousOn_reverseCurve hγ) := by
    ext t
    simp only [ContinuousMap.comp_apply, foldSimplex, pathSimplex, ContinuousMap.coe_mk,
      face_zero_apply_one]
    have ht : t 0 = 1 - t 1 := by linarith [stdSimplex_two_add t]
    have h1 : t 1 ∈ Icc (0 : ℝ) 1 :=
      ⟨stdSimplex_apply_nonneg t 1, by linarith [stdSimplex_apply_nonneg t 0, stdSimplex_two_add t]⟩
    have h0 : t 0 ∈ Icc (0 : ℝ) 1 :=
      ⟨stdSimplex_apply_nonneg t 0, by linarith [stdSimplex_apply_nonneg t 1, stdSimplex_two_add t]⟩
    rw [clampCurve_of_mem _ h0, clampCurve_of_mem _ h1, ht]
    rfl
  have e1 : (foldSimplex hγ).comp (face 1 1) = constSimplex 1 (γ 0) := by
    ext t
    simp only [ContinuousMap.comp_apply, foldSimplex, ContinuousMap.coe_mk, face_one_apply_one]
    rw [clampCurve_of_mem _ ⟨le_rfl, zero_le_one⟩]
    rfl
  have e2 : (foldSimplex hγ).comp (face 1 2) = pathSimplex hγ := by
    ext t
    simp only [ContinuousMap.comp_apply, foldSimplex, ContinuousMap.coe_mk, face_two_apply_one]
    rfl
  rw [bd_single_two, e0, e1, e2]

/-- The boundary of a constant `2`-simplex is the constant `1`-simplex. -/
theorem bd_single_constSimplex {R : Type*} [CommRing R] (v : E) :
    bd R 1 (single (constSimplex 2 v) 1) = single (constSimplex 1 v) 1 := by
  have e : ∀ k : Fin 3, (constSimplex 2 v).comp (face 1 k) = constSimplex 1 v := fun k ↦ by
    ext t; rfl
  rw [bd_single_two, e, e, e, sub_add_cancel]

/-- **A path and its reverse bound** the fold of the path plus a constant triangle. -/
theorem single_pathSimplex_add_reverse {R : Type*} [CommRing R] {γ : ℝ → E}
    (hγ : ContinuousOn γ (Icc 0 1)) :
    single (pathSimplex hγ) (1 : R) + single (pathSimplex (continuousOn_reverseCurve hγ)) 1 =
      bd R 1 (single (foldSimplex hγ) 1 + single (constSimplex 2 (γ 0)) 1) := by
  rw [map_add, bd_single_foldSimplex, bd_single_constSimplex]
  abel

/-- The fold simplex read on the square through `squareCollapse` is the fold map. -/
theorem foldSimplex_squareCollapse {γ : ℝ → E} (hγ : ContinuousOn γ (Icc 0 1)) {p : ℝ × ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :
    foldSimplex hγ (squareCollapse p) = foldMap γ p := by
  show clampCurve γ (squareCollapse p 1) = γ (p.1 * (1 - p.2))
  rw [squareCollapse_apply_one hp]
  exact clampCurve_of_mem γ (mul_one_sub_mem_Icc hp)

end Simplices

/-! ### Pushing simplices along inverse charts -/

section Push

variable {E : Type*} [TopologicalSpace E] {Y : Type*} [TopologicalSpace Y]

/-- The singular simplex `φ ∘ σ` of `Y`, for a map `φ` continuous on a set `S` containing the
image of `σ` (for instance an inverse chart on its domain). -/
def mapSimplex {k : ℕ} (φ : E → Y) {S : Set E} (hφ : ContinuousOn φ S) (σ : Simplex E k)
    (hσ : range σ ⊆ S) : Simplex Y k :=
  ⟨φ ∘ σ, hφ.comp_continuous σ.continuous fun t ↦ hσ ⟨t, rfl⟩⟩

/-- The value of the pushed simplex at `t` is `φ (σ t)`. -/
@[simp]
theorem mapSimplex_apply {k : ℕ} (φ : E → Y) {S : Set E} (hφ : ContinuousOn φ S)
    (σ : Simplex E k) (hσ : range σ ⊆ S) (t : stdSimplex ℝ (Fin (k + 1))) :
    mapSimplex φ hφ σ hσ t = φ (σ t) :=
  rfl

/-- If the image of a simplex lies in `S`, so does the image of each of its faces. -/
theorem range_comp_subset {k : ℕ} {σ : Simplex E (k + 1)} {S : Set E} (hσ : range σ ⊆ S)
    (i : Fin (k + 2)) : range (σ.comp (face k i)) ⊆ S :=
  fun _ ⟨t, ht⟩ ↦ hσ ⟨_, ht⟩

/-- The `i`-th face of a pushed simplex is the push of the `i`-th face. -/
theorem mapSimplex_comp_face {k : ℕ} (φ : E → Y) {S : Set E} (hφ : ContinuousOn φ S)
    (σ : Simplex E (k + 1)) (hσ : range σ ⊆ S) (i : Fin (k + 2)) :
    (mapSimplex φ hφ σ hσ).comp (face k i) =
      mapSimplex φ hφ (σ.comp (face k i)) (range_comp_subset hσ i) :=
  rfl

/-- Equal simplices have equal pushes, whatever the proofs that their images lie in `S`. -/
theorem mapSimplex_congr {k : ℕ} (φ : E → Y) {S : Set E} (hφ : ContinuousOn φ S)
    {σ τ : Simplex E k} (h : σ = τ) (hσ : range σ ⊆ S) (hτ : range τ ⊆ S) :
    mapSimplex φ hφ σ hσ = mapSimplex φ hφ τ hτ := by
  subst h; rfl

/-- The boundary of a pushed simplex is the push of its boundary. -/
theorem bd_single_mapSimplex {R : Type*} [CommRing R] {k : ℕ} (φ : E → Y) {S : Set E}
    (hφ : ContinuousOn φ S) (σ : Simplex E (k + 1)) (hσ : range σ ⊆ S) :
    bd R k (single (mapSimplex φ hφ σ hσ) 1) = ∑ i : Fin (k + 2), (-1 : R) ^ (i : ℕ) •
      single (mapSimplex φ hφ (σ.comp (face k i)) (range_comp_subset hσ i)) 1 := by
  rw [bd_single]
  rfl

end Push

/-! ### Readings of cone and fold simplices in a chart -/

section Reading

variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}

/-- The unit square `[0, 1]²`. -/
abbrev unitSquare : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

/-- **An open neighbourhood of the square on which a map stays in an open set.** If `g` is
continuous on an open set `W ⊇ [0, 1]²` and maps the square into the open set `T`, then
`W ∩ g⁻¹ T` is an open neighbourhood of the square mapped into `T`. -/
theorem exists_isOpen_mapsTo_of_square {E : Type*} [TopologicalSpace E] {g : ℝ × ℝ → E}
    {W : Set (ℝ × ℝ)} {T : Set E} (hW : IsOpen W) (hsW : unitSquare ⊆ W) (hg : ContinuousOn g W)
    (hT : IsOpen T) (hsT : MapsTo g unitSquare T) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ unitSquare ⊆ U ∧ U ⊆ W ∧ MapsTo g U T :=
  ⟨W ∩ g ⁻¹' T, hg.isOpen_inter_preimage hW hT, fun p hp ↦ ⟨hsW hp, hsT hp⟩,
    inter_subset_left, fun _ hp ↦ hp.2⟩

/-- If `[0, 1] ⊆ V`, the unit square lies in `ℝ × V`. -/
theorem unitSquare_subset_univ_prod {V : Set ℝ} (hV : Icc (0 : ℝ) 1 ⊆ V) :
    unitSquare ⊆ univ ×ˢ V :=
  fun _ hp ↦ ⟨mem_univ _, hV hp.2⟩

/-- **The reading of a cone simplex in a chart.** Let `e` be a chart of `Y` with values in
`ℂⁿ`, `γ` a curve `C²` on an open set `V ⊇ [0, 1]`, turning counterclockwise around `P` in
every coordinate on `V`, and suppose the cone from `P` over `γ` on the square lies in the
target of `e`. Then the cone simplex pushed along `e⁻¹` is read on the square, through the
collapse, as `e⁻¹ ∘ g` for the cone map `g`, which is `C²` on an open neighbourhood `U` of the
square, maps `U` into the target of `e`, and has nonnegative Jacobian on `U` in every
coordinate. -/
theorem exists_reading_coneSimplex (e : OpenPartialHomeomorph Y (Fin n → ℂ)) (P : Fin n → ℂ)
    {γ : ℝ → Fin n → ℂ} {V : Set ℝ} (hVo : IsOpen V) (hV : Icc (0 : ℝ) 1 ⊆ V)
    (hγ : ContDiffOn ℝ 2 γ V)
    (hturn : ∀ y ∈ V, ∀ i, 0 ≤ (star (γ y i - P i) * deriv γ y i).im)
    (hT : MapsTo (coneMap coneProfile P γ) unitSquare e.target) :
    ∃ (hσ : range (coneSimplex continuous_coneProfile coneProfile_zero P
        (hγ.continuousOn.mono hV)) ⊆ e.target) (U : Set (ℝ × ℝ)),
      IsOpen U ∧ unitSquare ⊆ U ∧ ContDiffOn ℝ 2 (coneMap coneProfile P γ) U ∧
      MapsTo (coneMap coneProfile P γ) U e.target ∧
      (∀ p ∈ unitSquare, mapSimplex e.symm e.continuousOn_symm
        (coneSimplex continuous_coneProfile coneProfile_zero P (hγ.continuousOn.mono hV)) hσ
          (squareCollapse p) = e.symm (coneMap coneProfile P γ p)) ∧
      ∀ p ∈ U, ∀ i : Fin n, 0 ≤ (star (fderiv ℝ (coneMap coneProfile P γ) p (1, 0) i) *
        fderiv ℝ (coneMap coneProfile P γ) p (0, 1) i).im := by
  have hc : ContDiffOn ℝ 2 (coneMap coneProfile P γ) (univ ×ˢ V) :=
    contDiffOn_coneMap (contDiff_coneProfile (by simp)) hγ
  have hσ : range (coneSimplex continuous_coneProfile coneProfile_zero P
      (hγ.continuousOn.mono hV)) ⊆ e.target := by
    rintro _ ⟨t, rfl⟩
    have h1 := stdSimplex_apply_nonneg t 1
    have h2 := stdSimplex_apply_nonneg t 2
    have hs1 : t 1 + t 2 ≤ 1 := by
      linarith [stdSimplex_three_add t, stdSimplex_apply_nonneg t 0]
    have hu : t 2 / (t 1 + t 2) ∈ Icc (0 : ℝ) 1 := by
      rcases eq_or_lt_of_le (add_nonneg h1 h2 : 0 ≤ t 1 + t 2) with h0 | h0
      · rw [← h0, div_zero]; exact ⟨le_rfl, zero_le_one⟩
      · exact ⟨div_nonneg h2 h0.le, (div_le_one h0).2 (by linarith)⟩
    have hp : (t 1 + t 2, t 2 / (t 1 + t 2)) ∈ unitSquare := ⟨⟨add_nonneg h1 h2, hs1⟩, hu⟩
    have := hT hp
    simp only [coneMap_apply] at this
    show P + coneProfile (t 1 + t 2) • (clampCurve γ (t 2 / (t 1 + t 2)) - P) ∈ e.target
    rw [clampCurve_of_mem _ hu]
    exact this
  obtain ⟨U, hUo, hsU, hUW, hUT⟩ := exists_isOpen_mapsTo_of_square (isOpen_univ.prod hVo)
    (unitSquare_subset_univ_prod hV) hc.continuousOn e.open_target hT
  refine ⟨hσ, U, hUo, hsU, hc.mono hUW, hUT, fun p hp ↦ ?_, fun p hp i ↦ ?_⟩
  · rw [mapSimplex_apply, coneSimplex_squareCollapse _ _ _ _ hp]
  · obtain ⟨x, y⟩ := p
    have hy : y ∈ V := (hUW hp).2
    have hd : DifferentiableAt ℝ γ y :=
      (hγ.contDiffAt (hVo.mem_nhds hy)).differentiableAt (by norm_num)
    exact im_star_fderiv_coneMap_nonneg hd i (hturn y hy i)

/-- **The reading of a fold simplex in a chart**: through the collapse, the fold of a curve `γ`
`C²` on an open set `V ⊇ [0, 1]` with values in the target of `e` is read as `e⁻¹ ∘ g` for the
fold map `g`, `C²` on an open neighbourhood of the square, with zero Jacobian there. -/
theorem exists_reading_foldSimplex (e : OpenPartialHomeomorph Y (Fin n → ℂ))
    {γ : ℝ → Fin n → ℂ} {V : Set ℝ} (hVo : IsOpen V) (hV : Icc (0 : ℝ) 1 ⊆ V)
    (hγ : ContDiffOn ℝ 2 γ V) (hT : MapsTo γ (Icc 0 1) e.target) :
    ∃ (hσ : range (foldSimplex (hγ.continuousOn.mono hV)) ⊆ e.target) (U : Set (ℝ × ℝ)),
      IsOpen U ∧ unitSquare ⊆ U ∧ ContDiffOn ℝ 2 (foldMap γ) U ∧
      MapsTo (foldMap γ) U e.target ∧
      (∀ p ∈ unitSquare, mapSimplex e.symm e.continuousOn_symm
        (foldSimplex (hγ.continuousOn.mono hV)) hσ (squareCollapse p) =
          e.symm (foldMap γ p)) ∧
      ∀ p ∈ U, ∀ i : Fin n, (star (fderiv ℝ (foldMap γ) p (1, 0) i) *
        fderiv ℝ (foldMap γ) p (0, 1) i).im = 0 := by
  set m : ℝ × ℝ → ℝ := fun p ↦ p.1 * (1 - p.2)
  have hm : Continuous m := by fun_prop
  have hc : ContDiffOn ℝ 2 (foldMap γ) (m ⁻¹' V) := contDiffOn_foldMap hγ
  have hms : MapsTo m unitSquare (Icc 0 1) := fun _ hp ↦ mul_one_sub_mem_Icc hp
  have hσ : range (foldSimplex (hγ.continuousOn.mono hV)) ⊆ e.target := by
    rintro _ ⟨t, rfl⟩
    have h1 : t 1 ∈ Icc (0 : ℝ) 1 := ⟨stdSimplex_apply_nonneg t 1, by
      linarith [stdSimplex_three_add t, stdSimplex_apply_nonneg t 0, stdSimplex_apply_nonneg t 2]⟩
    show clampCurve γ (t 1) ∈ e.target
    rw [clampCurve_of_mem _ h1]
    exact hT h1
  obtain ⟨U, hUo, hsU, hUW, hUT⟩ := exists_isOpen_mapsTo_of_square (hVo.preimage hm)
    (fun p hp ↦ hV (hms hp)) hc.continuousOn e.open_target (fun p hp ↦ hT (hms hp))
  refine ⟨hσ, U, hUo, hsU, hc.mono hUW, hUT, fun p hp ↦ ?_, fun p hp i ↦ ?_⟩
  · rw [mapSimplex_apply, foldSimplex_squareCollapse _ hp]
  · obtain ⟨x, y⟩ := p
    have hy : x * (1 - y) ∈ V := hUW hp
    exact im_star_fderiv_foldMap
      ((hγ.contDiffAt (hVo.mem_nhds hy)).differentiableAt (by norm_num)) i

end Reading

/-! ### The cones over a loop -/

section Loop

variable {Y : Type*} [TopologicalSpace Y] {n : ℕ}

/-- Consecutive cones over a loop share their radial edges: the edge `1` of the cone over the
arc `γ j` is the edge `2` of the cone over the next arc. -/
theorem mapSimplex_coneSimplex_comp_face_one_eq (e : OpenPartialHomeomorph Y (Fin n → ℂ))
    (P : Fin n → ℂ) {γ γ' : ℝ → Fin n → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hγ' : ContinuousOn γ' (Icc 0 1))
    (hσ : range (coneSimplex continuous_coneProfile coneProfile_zero P hγ) ⊆ e.target)
    (hσ' : range (coneSimplex continuous_coneProfile coneProfile_zero P hγ') ⊆ e.target)
    (h : γ 1 = γ' 0) :
    (mapSimplex e.symm e.continuousOn_symm _ hσ).comp (face 1 1) =
      (mapSimplex e.symm e.continuousOn_symm _ hσ').comp (face 1 2) := by
  ext t
  have h1 := congrArg (fun f : Simplex (Fin n → ℂ) 1 ↦ f t)
    (coneSimplex_comp_face_one continuous_coneProfile coneProfile_zero P hγ)
  have h2 := congrArg (fun f : Simplex (Fin n → ℂ) 1 ↦ f t)
    (coneSimplex_comp_face_two continuous_coneProfile coneProfile_zero P hγ')
  simp only [ContinuousMap.comp_apply] at h1 h2
  simp only [ContinuousMap.comp_apply, mapSimplex_apply, h1, h2, h]

/-- **The boundary of the cones over a loop.** For arcs `γ₀, …, γ_{k-1}` closing up into a loop
(`γ_j(1) = γ_{j+1}(0)`, indices mod `k`) and cones from `P` lying in the target of a chart `e`,
the boundary of the sum of the cones pushed along `e⁻¹` is the sum of their `0`-th faces (the
pushed arcs, by `coneSimplex_comp_face_zero`): the radial edges cancel. -/
theorem bd_sum_single_mapSimplex_coneSimplex {R : Type*} [CommRing R] {k : ℕ}
    (e : OpenPartialHomeomorph Y (Fin n → ℂ)) (P : Fin n → ℂ) (γ : Fin k → ℝ → Fin n → ℂ)
    (hγ : ∀ j, ContinuousOn (γ j) (Icc 0 1))
    (hσ : ∀ j, range (coneSimplex continuous_coneProfile coneProfile_zero P (hγ j)) ⊆ e.target)
    (hclose : ∀ j, γ j 1 = γ (finRotate k j) 0) :
    bd R 1 (∑ j, single (mapSimplex e.symm e.continuousOn_symm _ (hσ j)) 1) =
      ∑ j, single ((mapSimplex e.symm e.continuousOn_symm _ (hσ j)).comp (face 1 0)) 1 := by
  rw [map_sum]
  simp only [bd_single_two]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hrot : ∑ j, single ((mapSimplex e.symm e.continuousOn_symm _ (hσ j)).comp (face 1 1))
      (1 : R) = ∑ j, single ((mapSimplex e.symm e.continuousOn_symm _ (hσ j)).comp (face 1 2))
        (1 : R) := by
    rw [← Equiv.sum_comp (finRotate k) (fun j ↦ single
      ((mapSimplex e.symm e.continuousOn_symm _ (hσ j)).comp (face 1 2)) (1 : R))]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [mapSimplex_coneSimplex_comp_face_one_eq e P (hγ j) (hγ (finRotate k j)) (hσ j)
      (hσ (finRotate k j)) (hclose j)]
  rw [hrot]
  abel

end Loop

end MMP.Analytic.CurveCupPositivity
