module

public import MMP.AlgebraicGeometry.Analytic.Curve.AmpleChernClassPositivity
public import MMP.AlgebraicGeometry.Analytic.SchemeManifold
public import MMP.Analysis.Complex.OrientedConeSimplices
public import MMP.AlgebraicTopology.FundamentalClass.Exists
public import MMP.AlgebraicTopology.OrientationClass.CapUniqueness
public import MMP.AlgebraicTopology.PoincareDuality.LocalPackage
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RegularOpensSmooth

/-!
# Detecting the fundamental class of a curve by one oriented chart triangle

Let `X` be a smooth projective complex curve. This file gives the local criterion that turns a
finite singular `2`-cycle of oriented chart triangles into a fundamental class of `X`.

The class of a cycle `z` is detected at one point. By Fulton's Lemma 19.1.1
(`MMP.existsUnique_isVarietyFundamentalClass`) the class `[z]` is `λ [X]` for a
scalar `λ`. At a point `x₀` covered by exactly one triangle `σ₀` of `z`, at an interior point of
the square where the chart read of `σ₀` has positive Jacobian and is injective over `x₀`, the
local homology `H₂(X, X - x₀)` sees `[z]` as `r_{σ₀}` times the class of `σ₀`, which is the class
of a positively oriented chart simplex; a relative cocycle detecting the latter
(`MMP.SingularChain.exists_mem_relCocycles_eval_chartSimplexIn`) forces `λ = 1`
(`MMP.FundamentalClass.IsLocallyClassOf.eq_one_of_smul`).

## Main results

* `MMP.Analytic.FundamentalChartCycle.isAlgebraicChart_etaleChartUnderlying`: étale coordinate
  charts are algebraic charts.
* `MMP.Analytic.FundamentalChartCycle.exists_isLocallyHomologous_of_chartRead`: a chart triangle
  is, at a simple interior point of positive Jacobian, locally an oriented chart simplex.
* `MMP.Analytic.FundamentalChartCycle.isVarietyFundamentalClass_finiteCycleClass_of_eval`:
  a class of `H₂` of a curve which is locally, at one regular point, the class of a positively
  oriented chart simplex is the fundamental class.
* `MMP.Analytic.FundamentalChartCycle.exists_eq_of_mem_relCocycles_of_chartRead`: a relative
  cocycle at a simple point of positive Jacobian takes the same value on the chart triangle as on
  an oriented chart simplex of the regular chart.

## Implementation notes

Affine triangles read through the collapse have Jacobian `x · k`, which changes sign across the
edge `x = 0` of the square; since the sign condition is required on an open neighbourhood of the
square and a `C²` extension of the read has its first derivatives fixed along that edge, the
triangles to use are the radially reparametrised cones of
`MMP.Analytic.CurveCupPositivity.coneSimplex`, whose Jacobian `ρ ρ' · Im(conj(γ - P) γ')` is
flat at `x = 0`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [A. Hatcher, *Algebraic Topology*][hatcher2002], §3.3.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Set MMP
open MMP.SingularChain MMP.SingularCochain
open MMP.FundamentalClass MMP.UnderlyingSpace
open MMP.ThomClass
open MMP.Analytic MMP.Analytic.CurveCupPositivity
open scoped Manifold

namespace MMP.Analytic.FundamentalChartCycle

section Detection

/-- **A multiple of the fundamental class is detected at one point.** On a manifold, if `ν` is
a multiple `r • μ` of a fundamental class `μ` and `ν` is, at one point `x`, locally the class of a
positively oriented simplex of the chart at `x`, then `ν = μ`: a relative cocycle of
`(M, M - x)` detecting the simplex forces `r = 1`. -/
theorem eq_of_isLocallyClassOf_chartAt {R : Type} [CommRing R] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [FiniteDimensional ℝ H] {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace H M] {m : ℕ} {b : Module.Basis (Fin (m + 1)) ℝ H}
    {μ ν : MMP.borelMooreHomology R (ModuleCat.of R R) (TopCat.of M) (m + 1 : ℕ)}
    (hμ : IsFundamentalClass R b μ) (hν : ∃ r : R, ν = r • μ) (x : M)
    {v : Fin (m + 2) → H} (hv : IsOrientedSimplexAroundZero b fun k ↦ v k - chartAt H x x)
    (hvt : range (affineSimplex v) ⊆ (chartAt H x).target)
    (h : IsLocallyClassOf R ν x (chartSimplexOf (chartAt H x) v hvt)) : ν = μ := by
  obtain ⟨r, rfl⟩ := hν
  have hμx := hμ.isLocallyClassOf (chart_mem_atlas H x) (mem_chart_source H x) hv hvt
  obtain ⟨φ, hφ, hφ1⟩ := SingularChain.exists_mem_relCocycles_eval_chartSimplexIn (R := R) b
    (chartAt H x) (mem_chart_source H x) hv hvt
  have hφ1' : φ (chartSimplexOf (chartAt H x) v hvt) = 1 := by
    rw [← hφ1, eval_single_one]
    rfl
  rw [hμx.eq_one_of_smul h hφ hφ1', one_smul]

variable {V : Scheme.{0}} [V.Over (Spec (.of ℂ))] [IsComplexScheme V] [IsIntegral V]

/-- **The fundamental cycle of a curve is detected at one point.** A finite `2`-cycle `w` of
`V(ℂ)`, for a complex curve `V`, represents the fundamental class as soon as, at one regular
point `x`, `⟨φ, w⟩ = φ(Δ)` for every relative cocycle `φ` of `(V(ℂ), V(ℂ) - x)`, where `Δ` is the
image in `V(ℂ)` of a positively oriented simplex of the chart at `x` of `V_reg(ℂ)`: by Fulton's
Lemma 19.1.1 the class of `w` is `λ [V]`, and the local pairing at `x` forces `λ = 1`. -/
theorem isVarietyFundamentalClass_finiteCycleClass_of_eval
    (hn : ((1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim V)
    (w : Chain ℂ (TopCat.of (UnderlyingSpace ℂ V)) (1 + 1)) (hw : bd ℂ 1 w = 0)
    (x : regularOpens ℂ V) {v : Fin (1 + 2) → EuclideanSpace ℂ (Fin 1)}
    (hv : letI := regularChartedSpace (𝕜 := ℂ) hn
      IsOrientedSimplexAroundZero (euclideanComplexOrientationBasis 1)
        fun k ↦ v k - chartAt (EuclideanSpace ℂ (Fin 1)) x x)
    (hvt : letI := regularChartedSpace (𝕜 := ℂ) hn
      range (affineSimplex v) ⊆ (chartAt (EuclideanSpace ℂ (Fin 1)) x).target)
    (Δ : Simplex (TopCat.of (UnderlyingSpace ℂ V)) (1 + 1))
    (hΔ : letI := regularChartedSpace (𝕜 := ℂ) hn
      ∀ t, Δ t = ((chartAt (EuclideanSpace ℂ (Fin 1)) x).symm (affineSimplex v t) :
        UnderlyingSpace ℂ V))
    (h : ∀ φ ∈ relCocycles ℂ ({x.1}ᶜ : Set (TopCat.of (UnderlyingSpace ℂ V))) (1 + 1),
      eval φ w = φ Δ) :
    IsVarietyFundamentalClass ℂ hn (PolarizationPositivity.finiteCycleClass w hw) := by
  let := regularChartedSpace (𝕜 := ℂ) hn
  obtain ⟨c, hc, -, hbij⟩ := existsUnique_isVarietyFundamentalClass ℂ hn
  have hloc : IsLocallyClassOf ℂ (PolarizationPositivity.finiteCycleClass w hw) x.1 Δ :=
    PolarizationPositivity.isLocallyClassOf_finiteCycleClass_of_eval h
  have hΔ' : Δ = inclChainSimplex _
      (chartSimplexOf (chartAt (EuclideanSpace ℂ (Fin 1)) x) v hvt) :=
    ContinuousMap.ext hΔ
  rw [hΔ'] at hloc
  obtain ⟨r, hr⟩ := hbij.2 (PolarizationPositivity.finiteCycleClass w hw)
  have heq := eq_of_isLocallyClassOf_chartAt hc ⟨r, by rw [← hr, map_smul]⟩ x hv hvt
    (IsLocallyClassOf.restrict _ hloc)
  unfold IsVarietyFundamentalClass
  rw [heq]
  exact hc

end Detection

section LocalHomology

open Topology Filter Metric

/-- **Maps with a single point over `f x` preserve local homology classes at `x`**: if `σ₁`
and `σ₂` have the same class in `H_n(X, X - x; ℤ)` and `x` is the only point of `X` over `f x`,
then `f ∘ σ₁` and `f ∘ σ₂` have the same class in `H_n(Y, Y - f x; ℤ)`. -/
theorem isLocallyHomologous_comp_of_forall_eq {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x : X} {n : ℕ} {σ₁ σ₂ : Simplex X n}
    (h : IsLocallyHomologous x σ₁ σ₂) (f : C(X, Y)) (hf : ∀ y, f y = f x → y = x) :
    IsLocallyHomologous (f x) (f.comp σ₁) (f.comp σ₂) := by
  obtain ⟨c, d, hd, h⟩ := h
  refine ⟨postcomp ℤ f (n + 1) c, postcomp ℤ f n d,
    postcomp_mem_inside f (U := ({x}ᶜ : Set X)) (V := ({f x}ᶜ : Set Y))
      (fun y (hy : y ≠ x) (hfy : f y = f x) ↦ hy (hf y hfy)) hd, ?_⟩
  have := congrArg (postcomp ℤ f n) h
  rwa [map_sub, map_add, postcomp_single, postcomp_single, postcomp_bd] at this

/-- Two points of `Δ²` with the same last two barycentric coordinates are equal. -/
theorem stdSimplex_three_ext {s t : stdSimplex ℝ (Fin 3)} (h1 : s 1 = t 1) (h2 : s 2 = t 2) :
    s = t := by
  have hs := stdSimplex_three_add s
  have ht := stdSimplex_three_add t
  apply Subtype.ext
  funext i
  fin_cases i
  · change s 0 = t 0
    linarith
  · exact h1
  · exact h2

/-- The normaliser `max 1 (a⁺ + b⁺)` of `triangleRetraction`. -/
abbrev triangleRetractionScale (p : ℝ × ℝ) : ℝ := max 1 (max p.1 0 + max p.2 0)

/-- The normaliser `triangleRetractionScale p` is positive. -/
theorem triangleRetractionScale_pos (p : ℝ × ℝ) : 0 < triangleRetractionScale p :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- **The retraction of the plane onto the standard triangle** `{(a, b) | a, b ≥ 0, a + b ≤ 1}`,
seen in `Δ²` through the barycentric coordinates `(1 - a - b, a, b)`:
`(a, b) ↦ (a⁺, b⁺) / max 1 (a⁺ + b⁺)`. -/
def triangleRetraction : C(ℝ × ℝ, stdSimplex ℝ (Fin 3)) where
  toFun p := ⟨![1 - max p.1 0 / triangleRetractionScale p - max p.2 0 / triangleRetractionScale p,
      max p.1 0 / triangleRetractionScale p, max p.2 0 / triangleRetractionScale p], by
    have hm := triangleRetractionScale_pos p
    have ha : 0 ≤ max p.1 0 / triangleRetractionScale p := div_nonneg (le_max_right _ _) hm.le
    have hb : 0 ≤ max p.2 0 / triangleRetractionScale p := div_nonneg (le_max_right _ _) hm.le
    have hab : max p.1 0 / triangleRetractionScale p + max p.2 0 / triangleRetractionScale p ≤
        1 := by
      rw [← add_div, div_le_one hm]
      exact le_max_right _ _
    refine ⟨fun i ↦ ?_, ?_⟩
    · fin_cases i
      · change 0 ≤ 1 - _ - _
        linarith
      · exact ha
      · exact hb
    · rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      ring⟩
  continuous_toFun := by
    have hm : Continuous triangleRetractionScale := by
      unfold triangleRetractionScale
      fun_prop
    have h1 : Continuous fun p : ℝ × ℝ ↦ max p.1 0 / triangleRetractionScale p :=
      (continuous_fst.max continuous_const).div hm fun p ↦ (triangleRetractionScale_pos p).ne'
    have h2 : Continuous fun p : ℝ × ℝ ↦ max p.2 0 / triangleRetractionScale p :=
      (continuous_snd.max continuous_const).div hm fun p ↦ (triangleRetractionScale_pos p).ne'
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    fin_cases i
    · exact (continuous_const.sub h1).sub h2
    · exact h1
    · exact h2

/-- The first barycentric coordinate of `triangleRetraction p` is
`max p.1 0 / triangleRetractionScale p`. -/
theorem triangleRetraction_apply_one (p : ℝ × ℝ) :
    triangleRetraction p 1 = max p.1 0 / triangleRetractionScale p :=
  rfl

/-- The second barycentric coordinate of `triangleRetraction p` is
`max p.2 0 / triangleRetractionScale p`. -/
theorem triangleRetraction_apply_two (p : ℝ × ℝ) :
    triangleRetraction p 2 = max p.2 0 / triangleRetractionScale p :=
  rfl

/-- On the standard triangle, `triangleRetraction` is the barycentric parametrisation. -/
theorem triangleRetraction_apply_of_mem {p : ℝ × ℝ} (h1 : 0 ≤ p.1) (h2 : 0 ≤ p.2)
    (h12 : p.1 + p.2 ≤ 1) :
    triangleRetraction p 1 = p.1 ∧ triangleRetraction p 2 = p.2 := by
  have hm : triangleRetractionScale p = 1 := by
    unfold triangleRetractionScale
    rw [max_eq_left h1, max_eq_left h2, max_eq_left h12]
  rw [triangleRetraction_apply_one, triangleRetraction_apply_two, hm, max_eq_left h1,
    max_eq_left h2, div_one, div_one]
  exact ⟨rfl, rfl⟩

/-- `triangleRetraction` is a retraction: it fixes every point `t` of `Δ²`. -/
theorem triangleRetraction_coord (t : stdSimplex ℝ (Fin 3)) :
    triangleRetraction (t 1, t 2) = t := by
  have h := stdSimplex_three_add t
  have h0 := stdSimplex_apply_nonneg t 0
  obtain ⟨e1, e2⟩ := triangleRetraction_apply_of_mem (p := (t 1, t 2))
    (stdSimplex_apply_nonneg t 1) (stdSimplex_apply_nonneg t 2) (by simp only; linarith)
  exact stdSimplex_three_ext e1 e2

/-- An interior point of `Δ²` has a single point of the plane over it. -/
theorem eq_of_triangleRetraction_eq {p : ℝ × ℝ} {t : stdSimplex ℝ (Fin 3)}
    (h : triangleRetraction p = t) (h0 : 0 < t 0) (h1 : 0 < t 1) (h2 : 0 < t 2) :
    p = (t 1, t 2) := by
  have hs := stdSimplex_three_add t
  have hm := triangleRetractionScale_pos p
  have e1 : max p.1 0 / triangleRetractionScale p = t 1 := by
    rw [← triangleRetraction_apply_one, h]
  have e2 : max p.2 0 / triangleRetractionScale p = t 2 := by
    rw [← triangleRetraction_apply_two, h]
  have hle : max p.1 0 + max p.2 0 ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have hM : triangleRetractionScale p = max p.1 0 + max p.2 0 := max_eq_right hlt.le
    have : t 1 + t 2 = 1 := by
      rw [← e1, ← e2, ← add_div, hM]
      exact div_self (hM ▸ hm.ne')
    linarith
  have hM : triangleRetractionScale p = 1 := max_eq_left hle
  rw [hM, div_one] at e1 e2
  have hp1 : max p.1 0 = p.1 := by
    rcases le_total p.1 0 with h' | h'
    · rw [max_eq_right h'] at e1
      linarith
    · exact max_eq_left h'
  have hp2 : max p.2 0 = p.2 := by
    rcases le_total p.2 0 with h' | h'
    · rw [max_eq_right h'] at e2
      linarith
    · exact max_eq_left h'
  exact Prod.ext (hp1 ▸ e1) (hp2 ▸ e2)

/-- The vertices `(0, 0)`, `(1, 0)`, `(0, 1)` of the standard triangle of the plane. -/
abbrev stdTriangleVertices : Fin (1 + 1 + 1) → ℝ × ℝ := ![(0, 0), (1, 0), (0, 1)]

/-- The affine simplex on `stdTriangleVertices` sends `t ∈ Δ²` to `(t 1, t 2)`. -/
theorem affineSimplex_stdTriangleVertices (t : stdSimplex ℝ (Fin (1 + 1 + 1))) :
    affineSimplex stdTriangleVertices t = (t 1, t 2) := by
  rw [affineSimplex_apply]
  simp [Fin.sum_univ_three]

/-- The coordinates of `u ∈ ℂ¹` in the real basis `e₁, i e₁` are `Re u₀, Im u₀`. -/
theorem complexOrientationBasis_one_repr (u : Fin 1 → ℂ) :
    (complexOrientationBasis 1).repr u 0 = (u 0).re ∧
      (complexOrientationBasis 1).repr u 1 = (u 0).im := by
  have h0 : complexOrientationBasis 1 0 = fun _ ↦ 1 := by
    have := complexOrientationBasis_apply 1 0 0
    rw [show finCongr (Nat.mul_comm 1 2) (finProdFinEquiv ((0 : Fin 1), (0 : Fin 2))) = 0 from
      Fin.ext rfl] at this
    rw [this]
    funext j
    simp [Subsingleton.elim j 0]
  have h1 : complexOrientationBasis 1 1 = fun _ ↦ Complex.I := by
    have := complexOrientationBasis_apply 1 0 1
    rw [show finCongr (Nat.mul_comm 1 2) (finProdFinEquiv ((0 : Fin 1), (1 : Fin 2))) = 1 from
      Fin.ext rfl] at this
    rw [this]
    funext j
    simp [Subsingleton.elim j 0]
  have hu : u = (u 0).re • complexOrientationBasis 1 0 +
      (u 0).im • complexOrientationBasis 1 1 := by
    rw [h0, h1]
    funext j
    fin_cases j
    simp
  constructor
  · conv_lhs => rw [hu]
    simp
  · conv_lhs => rw [hu]
    simp

/-- The determinant of two vectors of `ℂ¹` in the real basis `e₁, i e₁`:
`Re u₀ Im w₀ - Re w₀ Im u₀ = Im(conj u₀ · w₀)`. -/
theorem complexOrientationBasis_one_det (u : Fin (2 * 1) → (Fin 1 → ℂ)) :
    (complexOrientationBasis 1).det u = (u 0 0).re * (u 1 0).im - (u 1 0).re * (u 0 0).im := by
  rw [Module.Basis.det_apply]
  change Matrix.det (n := Fin 2) _ = _
  rw [Matrix.det_fin_two]
  simp only [Module.Basis.toMatrix_apply]
  obtain ⟨a0, a1⟩ := complexOrientationBasis_one_repr (u 0)
  obtain ⟨b0, b1⟩ := complexOrientationBasis_one_repr (u 1)
  change (complexOrientationBasis 1).repr (u 0) 0 * (complexOrientationBasis 1).repr (u 1) 1 -
    (complexOrientationBasis 1).repr (u 1) 0 * (complexOrientationBasis 1).repr (u 0) 1 = _
  rw [a0, a1, b0, b1]

/-- The standard triangle is an oriented simplex around each point of its interior. -/
theorem isOrientedSimplexAroundZero_stdTriangleVertices {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < 1) :
    IsOrientedSimplexAroundZero (Module.Basis.finTwoProd ℝ)
      fun k ↦ stdTriangleVertices k - (a, b) := by
  refine ⟨⟨![1 - a - b, a, b], fun k ↦ ?_, ?_, ?_⟩, ?_⟩
  · fin_cases k
    · change 0 < 1 - a - b
      linarith
    · exact ha
    · exact hb
  · simp [Fin.sum_univ_succ]
  · refine Prod.ext ?_ ?_ <;> simp [Fin.sum_univ_succ] <;> ring
  · have : (fun k : Fin 2 ↦ (stdTriangleVertices k.succ - (a, b)) -
        (stdTriangleVertices 0 - (a, b))) = ![(1, 0), (0, 1)] := by
      funext k
      fin_cases k <;> simp
    rw [this]
    simp [Module.Basis.det_apply, Module.Basis.toMatrix_apply, Matrix.det_fin_two]

/-- Over the image `squareCollapse p₀` of an interior point `p₀` of the square,
`triangleRetraction` has the single point `(p₀.1 (1 - p₀.2), p₀.1 p₀.2)`. -/
theorem eq_of_triangleRetraction_eq_squareCollapse {p₀ p : ℝ × ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
    (h : triangleRetraction p = squareCollapse p₀) : p = (p₀.1 * (1 - p₀.2), p₀.1 * p₀.2) := by
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hp₀
  have hsq : p₀ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := ⟨⟨hx0.le, hx1.le⟩, hy0.le, hy1.le⟩
  have hsq1 := squareCollapse_apply_one hsq
  have hsq2 := squareCollapse_apply_two hsq
  have hs0 : 0 < squareCollapse p₀ 0 := by
    have := stdSimplex_three_add (squareCollapse p₀)
    rw [hsq1, hsq2] at this
    nlinarith
  have := eq_of_triangleRetraction_eq h hs0
    (by rw [hsq1]; exact mul_pos hx0 (by linarith)) (by rw [hsq2]; exact mul_pos hx0 hy0)
  rw [this, hsq1, hsq2]

/-- **Excision through `triangleRetraction`.** If `σ` is injective over the image of an
interior point `p₀` of the square, then at that image `σ` is locally homologous to
`σ ∘ triangleRetraction ∘ Δ` for every oriented affine triangle `Δ` of the plane around
`(p₀.1 (1 - p₀.2), p₀.1 p₀.2)`. -/
theorem isLocallyHomologous_comp_triangleRetraction {T : Type*} [TopologicalSpace T]
    (σ : Simplex T (1 + 1)) {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
    (hinj : ∀ t, σ t = σ (squareCollapse p₀) → t = squareCollapse p₀)
    {u : Fin (1 + 2) → ℝ × ℝ}
    (hu : IsOrientedSimplexAroundZero (Module.Basis.finTwoProd ℝ)
      fun k ↦ u k - (p₀.1 * (1 - p₀.2), p₀.1 * p₀.2)) :
    IsLocallyHomologous (σ (squareCollapse p₀)) σ
      ((σ.comp triangleRetraction).comp (affineSimplex u)) := by
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := id hp₀
  have hsq : p₀ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := ⟨⟨hx0.le, hx1.le⟩, hy0.le, hy1.le⟩
  have hR : triangleRetraction (p₀.1 * (1 - p₀.2), p₀.1 * p₀.2) = squareCollapse p₀ := by
    have := triangleRetraction_coord (squareCollapse p₀)
    rwa [squareCollapse_apply_one hsq, squareCollapse_apply_two hsq] at this
  have hw := isOrientedSimplexAroundZero_stdTriangleVertices (mul_pos hx0 (sub_pos.2 hy1))
    (mul_pos hx0 hy0) (by linarith)
  have hplane : IsLocallyHomologous (p₀.1 * (1 - p₀.2), p₀.1 * p₀.2)
      (affineSimplex stdTriangleVertices) (affineSimplex u) :=
    isLocallyHomologous_of_isOrientedSimplexAroundZero (OpenPartialHomeomorph.refl (ℝ × ℝ))
      (Set.mem_univ _) hw (Set.subset_univ _) hu (Set.subset_univ _) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hmap := isLocallyHomologous_comp_of_forall_eq hplane (σ.comp triangleRetraction)
    fun p hp ↦ eq_of_triangleRetraction_eq_squareCollapse hp₀
      (hinj (triangleRetraction p) (hp.trans (congrArg σ hR)))
  have hσw : (σ.comp triangleRetraction).comp (affineSimplex stdTriangleVertices) = σ := by
    refine ContinuousMap.ext fun t ↦ ?_
    change σ (triangleRetraction (affineSimplex stdTriangleVertices t)) = σ t
    rw [affineSimplex_stdTriangleVertices, triangleRetraction_coord]
  rwa [show (σ.comp triangleRetraction) (p₀.1 * (1 - p₀.2), p₀.1 * p₀.2) =
    σ (squareCollapse p₀) from congrArg σ hR, hσw] at hmap

/-- The inverse `(a, b) ↦ (a + b, b / (a + b))` of the collapse of the square onto the
standard triangle, away from the vertex `(0, 0)`. -/
def triangleToSquare (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 + p.2, p.2 * (p.1 + p.2)⁻¹)

/-- `triangleToSquare` maps the open standard triangle into the unit square. -/
theorem triangleToSquare_mem {p : ℝ × ℝ} (h1 : 0 < p.1) (h2 : 0 < p.2) (h12 : p.1 + p.2 < 1) :
    triangleToSquare p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  have hs : 0 < p.1 + p.2 := by linarith
  refine ⟨⟨hs.le, h12.le⟩, ⟨(mul_pos h2 (inv_pos.2 hs)).le, ?_⟩⟩
  change p.2 * (p.1 + p.2)⁻¹ ≤ 1
  rw [← div_eq_mul_inv, div_le_one hs]
  linarith

/-- On the open standard triangle, `triangleRetraction` is `squareCollapse ∘ triangleToSquare`. -/
theorem triangleRetraction_eq_squareCollapse_triangleToSquare {p : ℝ × ℝ} (h1 : 0 < p.1)
    (h2 : 0 < p.2) (h12 : p.1 + p.2 < 1) :
    triangleRetraction p = squareCollapse (triangleToSquare p) := by
  have hs : p.1 + p.2 ≠ 0 := by linarith
  obtain ⟨e1, e2⟩ := triangleRetraction_apply_of_mem h1.le h2.le h12.le
  apply stdSimplex_three_ext
  · rw [e1, squareCollapse_apply_one (triangleToSquare_mem h1 h2 h12)]
    change p.1 = (p.1 + p.2) * (1 - p.2 * (p.1 + p.2)⁻¹)
    field_simp
    ring
  · rw [e2, squareCollapse_apply_two (triangleToSquare_mem h1 h2 h12)]
    change p.2 = (p.1 + p.2) * (p.2 * (p.1 + p.2)⁻¹)
    field_simp

/-- `triangleToSquare` is continuous away from the line `a + b = 0`. -/
theorem continuousOn_triangleToSquare :
    ContinuousOn triangleToSquare {p : ℝ × ℝ | p.1 + p.2 ≠ 0} :=
  ((continuous_fst.add continuous_snd).continuousOn).prodMk
    (continuous_snd.continuousOn.mul ((continuous_fst.add continuous_snd).continuousOn.inv₀
      fun _ hp ↦ hp))

/-- `triangleToSquare` inverts the collapse `(x, y) ↦ (x (1 - y), x y)` for `x ≠ 0`. -/
theorem triangleToSquare_mul {x : ℝ} (hx : x ≠ 0) (y : ℝ) :
    triangleToSquare (x * (1 - y), x * y) = (x, y) := by
  have hxy : x * (1 - y) + x * y = x := by ring
  refine Prod.ext hxy ?_
  change x * y * (x * (1 - y) + x * y)⁻¹ = y
  rw [hxy]
  field_simp

/-- The derivative of `triangleToSquare` at a point `q` with `q.1 + q.2 ≠ 0`, on the standard
basis. -/
theorem hasFDerivAt_triangleToSquare {q : ℝ × ℝ} (hq : q.1 + q.2 ≠ 0) :
    ∃ L : ℝ × ℝ →L[ℝ] ℝ × ℝ, HasFDerivAt triangleToSquare L q ∧
      L (1, 0) = (1, -q.2 * ((q.1 + q.2) ^ 2)⁻¹) ∧
      L (0, 1) = (1, q.1 * ((q.1 + q.2) ^ 2)⁻¹) := by
  have hsum : HasFDerivAt (fun p : ℝ × ℝ ↦ p.1 + p.2)
      (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) q :=
    hasFDerivAt_fst.add hasFDerivAt_snd
  refine ⟨_, hsum.prodMk (hasFDerivAt_snd.fun_mul ((hasFDerivAt_inv hq).comp q hsum)), ?_, ?_⟩
  · exact Prod.ext (by simp) (by simp)
  · refine Prod.ext (by simp) ?_
    simp
    field_simp
    ring

/-- **A linear map of positive Jacobian composed with the derivative of `triangleToSquare`
preserves the complex orientation**: `M` is the derivative of `triangleToSquare` at `(a, b)`,
`a + b > 0`. -/
theorem complexOrientationBasis_one_det_comp_pos {D : ℝ × ℝ →L[ℝ] (Fin 1 → ℂ)}
    {M : ℝ × ℝ →L[ℝ] ℝ × ℝ} {a b : ℝ} (hab : 0 < a + b)
    (hM₁ : M (1, 0) = (1, -b * ((a + b) ^ 2)⁻¹)) (hM₂ : M (0, 1) = (1, a * ((a + b) ^ 2)⁻¹))
    (hD : 0 < (star (D (1, 0) 0) * D (0, 1) 0).im) :
    0 < (complexOrientationBasis 1).det
      (((D.comp M : ℝ × ℝ →L[ℝ] (Fin 1 → ℂ)) : ℝ × ℝ → Fin 1 → ℂ) ∘
        Module.Basis.finTwoProd ℝ) := by
  set A := D (1, 0)
  set B := D (0, 1)
  have key : ∀ s t : ℝ, D (s, t) = s • A + t • B := by
    intro s t
    rw [show ((s, t) : ℝ × ℝ) = s • ((1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ)) by
      refine Prod.ext ?_ ?_ <;> simp, map_add, map_smul, map_smul]
  simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im] at hD
  have hfun : ((D.comp M : ℝ × ℝ → Fin 1 → ℂ) ∘ Module.Basis.finTwoProd ℝ) =
      ![D.comp M (1, 0), D.comp M (0, 1)] := by
    funext i
    fin_cases i <;> simp
  rw [hfun, complexOrientationBasis_one_det]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.comp_apply, hM₁,
    hM₂, key, Pi.add_apply, Pi.smul_apply, Complex.add_re, Complex.add_im, Complex.smul_re,
    Complex.smul_im, smul_eq_mul, one_mul]
  have hc : a * ((a + b) ^ 2)⁻¹ - -b * ((a + b) ^ 2)⁻¹ = (a + b)⁻¹ := by
    field_simp
    ring
  nlinarith [mul_pos (inv_pos.2 hab) hD]

/-- A linear map commutes with affine simplices. -/
theorem affineSimplex_comp_linearMap {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] [AddCommGroup W] [Module ℝ W]
    [TopologicalSpace W] [ContinuousAdd W] [ContinuousSMul ℝ W] {n : ℕ} (L : V →ₗ[ℝ] W)
    (v : Fin (n + 1) → V) (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex (fun k ↦ L (v k)) t = L (affineSimplex v t) := by
  rw [affineSimplex_apply, affineSimplex_apply, map_sum]
  simp only [map_smul]

/-- The identification `ℂ¹ ≃ EuclideanSpace ℂ (Fin 1)` carries a positively oriented simplex
around `z` to a positively oriented simplex around the image of `z`. -/
theorem isOrientedSimplexAroundZero_euclideanEquiv_symm {w : Fin (1 + 2) → (Fin 1 → ℂ)}
    {z : Fin 1 → ℂ} (hw : IsOrientedSimplexAroundZero (complexOrientationBasis 1)
      fun k ↦ w k - z) :
    IsOrientedSimplexAroundZero (euclideanComplexOrientationBasis 1) fun k ↦
      (EuclideanSpace.equiv (Fin 1) ℂ).symm (w k) - (EuclideanSpace.equiv (Fin 1) ℂ).symm z := by
  set Lr : (Fin 1 → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1) :=
    ((EuclideanSpace.equiv (Fin 1) ℂ).symm.toLinearEquiv.restrictScalars ℝ).toLinearMap
  have hLr : ∀ u, Lr u = (EuclideanSpace.equiv (Fin 1) ℂ).symm u := fun _ ↦ rfl
  have hdet : 0 < (euclideanComplexOrientationBasis 1).det (Lr ∘ complexOrientationBasis 1) := by
    have : (Lr ∘ complexOrientationBasis 1) = ⇑(euclideanComplexOrientationBasis 1) := by
      funext i
      rw [Function.comp_apply, hLr, euclideanComplexOrientationBasis_apply]
      rfl
    rw [this, Module.Basis.det_self]
    exact one_pos
  convert hw.map_linearMap Lr hdet using 1
  funext k
  simp only [Function.comp_apply, map_sub, hLr]

end LocalHomology

section EtaleChart

open scoped ContDiff

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] {n : ℕ}

/-- An étale coordinate chart of `X^an`, read on Fulton's underlying space `X(ℂ)` and with
values in `EuclideanSpace ℂ (Fin n)`. -/
def etaleChartUnderlying (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) :
    OpenPartialHomeomorph (UnderlyingSpace ℂ X) (EuclideanSpace ℂ (Fin n)) :=
  (ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm.toOpenPartialHomeomorph.trans
    (c.toOpenPartialHomeomorph.trans
      (EuclideanSpace.equiv (Fin n) ℂ).symm.toHomeomorph.toOpenPartialHomeomorph)

/-- `etaleChartUnderlying c` sends `p` to the image under `c` of the point of `X^an`
corresponding to `p`, read in `EuclideanSpace ℂ (Fin n)`. -/
theorem etaleChartUnderlying_apply (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n)
    (p : UnderlyingSpace ℂ X) :
    etaleChartUnderlying c p = (EuclideanSpace.equiv (Fin n) ℂ).symm
      (c.toOpenPartialHomeomorph ((ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm p)) :=
  rfl

/-- The inverse of `etaleChartUnderlying c` is the inverse of `c`, followed by the
identification of `X^an` with `X(ℂ)`. -/
theorem etaleChartUnderlying_symm_apply
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) (k : EuclideanSpace ℂ (Fin n)) :
    (etaleChartUnderlying c).symm k = ComplexPoints.homeomorphUnderlyingSpace (X := X)
      (c.toOpenPartialHomeomorph.symm (EuclideanSpace.equiv (Fin n) ℂ k)) :=
  rfl

/-- A point of `X(ℂ)` lies in the source of `etaleChartUnderlying c` if and only if the
corresponding point of `X^an` lies in the source of `c`. -/
theorem mem_etaleChartUnderlying_source
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) {p : UnderlyingSpace ℂ X} :
    p ∈ (etaleChartUnderlying c).source ↔
      (ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm p ∈
        c.toOpenPartialHomeomorph.source := by
  simp [etaleChartUnderlying]

/-- A point `k` lies in the target of `etaleChartUnderlying c` if and only if its
coordinates lie in the target of `c`. -/
theorem mem_etaleChartUnderlying_target
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) {k : EuclideanSpace ℂ (Fin n)} :
    k ∈ (etaleChartUnderlying c).target ↔
      EuclideanSpace.equiv (Fin n) ℂ k ∈ c.toOpenPartialHomeomorph.target := by
  simp [etaleChartUnderlying]

/-- **Étale coordinate charts are algebraic charts**: regular functions are analytic in étale
coordinates (`MMP.Analytic.ComplexPoints.EtaleCoordinateChart.exists_analyticOnNhd`), and the
coordinates are regular functions. -/
theorem isAlgebraicChart_etaleChartUnderlying [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) n) :
    IsAlgebraicChart (etaleChartUnderlying c) := by
  set Hm := ComplexPoints.homeomorphUnderlyingSpace (X := X)
  set Lh := EuclideanSpace.equiv (Fin n) ℂ
  have hW : ∀ {q}, q ∈ (etaleChartUnderlying c).source → Hm.symm q ∈ c.W := fun hq ↦ by
    have := (mem_etaleChartUnderlying_source c).1 hq
    rwa [ComplexPoints.EtaleCoordinateChart.source_toOpenPartialHomeomorph] at this
  constructor
  · intro V a
    obtain ⟨G, hGa, hG⟩ := c.exists_analyticOnNhd V a
    set S := c.toOpenPartialHomeomorph.target ∩
      c.toOpenPartialHomeomorph.symm ⁻¹' ComplexPoints.chart V
    have hcd : ContDiffOn ℂ ω (fun k ↦ G (Lh k)) (Lh ⁻¹' S) :=
      ContDiffOn.comp (fun k hk ↦ (hGa k hk).contDiffAt.contDiffWithinAt)
        Lh.contDiff.contDiffOn (Set.mapsTo_preimage _ _)
    refine (hcd.mono ?_).congr ?_
    · rintro k ⟨hk, hkV⟩
      exact ⟨(mem_etaleChartUnderlying_target c).1 hk, le_antisymm le_top hkV⟩
    · rintro k ⟨hk, hkV⟩
      have hkT := (mem_etaleChartUnderlying_target c).1 hk
      have hW := c.toOpenPartialHomeomorph_symm_mem hkT
      have hyV : c.toOpenPartialHomeomorph.symm (Lh k) ∈ ComplexPoints.chart V :=
        le_antisymm le_top hkV
      change evalExt V a ((etaleChartUnderlying c).symm k) = G (Lh k)
      have := hG _ hW hyV
      rw [c.toOpenPartialHomeomorph.right_inv hkT] at this
      rw [etaleChartUnderlying_symm_apply]
      exact (evalExt_of_le _ (ComplexPoints.top_le_preimage_of_mem_chart ⟨_, hyV⟩)).trans this
  · intro p hp
    refine ⟨c.U, Fin n, inferInstance, c.z, (Lh.symm : (Fin n → ℂ) →L[ℂ] _),
      ComplexPoints.top_le_preimage_of_mem_chart ⟨Hm.symm p, c.subset (hW hp)⟩,
      fun q hq hqV ↦ ?_⟩
    rw [etaleChartUnderlying_apply, ContinuousLinearEquiv.coe_coe]
    refine congrArg Lh.symm (funext fun i ↦ ?_)
    rw [c.toOpenPartialHomeomorph_apply (hW hq) i, evalExt_of_le _ hqV]
    rfl

end EtaleChart

section Curve

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [AlgebraicGeometry.IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))]

/-- The Jacobian `Im(conj(∂₁ gᵢ) · ∂₂ gᵢ)` of the `i`-th coordinate of a map `g : ℝ² → ℂⁿ` at
`p`: positive exactly where `g` preserves the complex orientation of the `i`-th factor. -/
abbrev chartJacobian {n : ℕ} (g : ℝ × ℝ → (Fin n → ℂ)) (p : ℝ × ℝ) (i : Fin n) : ℝ :=
  (star (fderiv ℝ g p (1, 0) i) * fderiv ℝ g p (0, 1) i).im

/-- **A chart triangle is locally an oriented affine chart simplex at a simple interior
point.** Let `e` be an open partial homeomorphism of a space `T` into `ℂ`, and `σ` a singular
triangle of `T` which on the unit square is the read `e⁻¹ ∘ g` of a `C²` map `g`, defined on an
open neighbourhood of the square and with values in the target of `e`. At an interior point `p₀`
of the square where the Jacobian of `g` is positive and over whose image `x₀ = σ(s(p₀))` the
triangle is injective, `σ` has the class in `H₂(T, T - x₀; ℤ)` of `e⁻¹ ∘ Δ` for an affine
simplex `Δ` of `e(T)` around `e(x₀)` positively oriented for the complex orientation.

Near `s(p₀)` the collapse `s` has positive Jacobian `x`, so by injectivity over `x₀` the triangle
is locally homologous at `x₀` to `σ ∘ s ∘ Δ₀` for a small affine triangle `Δ₀` of the square
around `p₀` (excision in `Δ²`, then `IsLocallyHomologous.map`), which is `e⁻¹ ∘ g ∘ Δ₀`; and
`MMP.FundamentalClass.isLocallyHomologous_of_hasFDerivAt` replaces `g ∘ Δ₀` by
the affine simplex of its linearisation at `p₀`. -/
theorem exists_isLocallyHomologous_of_chartRead {T : Type*} [TopologicalSpace T] [T2Space T]
    (e : OpenPartialHomeomorph T (Fin 1 → ℂ)) (σ : Simplex T (1 + 1))
    (g : ℝ × ℝ → (Fin 1 → ℂ)) (U : Set (ℝ × ℝ)) (hUo : IsOpen U)
    (hsq : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U) (hg : ContDiffOn ℝ 2 g U)
    (hgT : Set.MapsTo g U e.target)
    (hσ : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, σ (squareCollapse p) = e.symm (g p))
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
    (hJ : ∀ i : Fin 1, 0 < chartJacobian g p₀ i)
    (hinj : ∀ t, σ t = σ (squareCollapse p₀) → t = squareCollapse p₀) :
    ∃ (v : Fin (1 + 2) → (Fin 1 → ℂ))
      (_ : IsOrientedSimplexAroundZero (complexOrientationBasis 1)
        fun k ↦ v k - e (σ (squareCollapse p₀)))
      (_ : range (affineSimplex v) ⊆ e.target) (Δ : Simplex T (1 + 1)),
      (∀ t, Δ t = e.symm (affineSimplex v t)) ∧
        IsLocallyHomologous (σ (squareCollapse p₀)) σ Δ := by
  obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := id hp₀
  have hp₀sq : p₀ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨⟨hx0.le, hx1.le⟩, ⟨hy0.le, hy1.le⟩⟩
  have hx₀ : σ (squareCollapse p₀) = e.symm (g p₀) := hσ p₀ hp₀sq
  have hgp : g p₀ ∈ e.target := hgT (hsq hp₀sq)
  have hex₀ : e (σ (squareCollapse p₀)) = g p₀ := by rw [hx₀, e.right_inv hgp]
  set q' : ℝ × ℝ := (p₀.1 * (1 - p₀.2), p₀.1 * p₀.2)
  have hq' : q'.1 + q'.2 = p₀.1 := show p₀.1 * (1 - p₀.2) + p₀.1 * p₀.2 = p₀.1 by ring
  have hq's : 0 < q'.1 + q'.2 := by
    rw [hq']
    exact hx0
  set V : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 < 1}
  have hVo : IsOpen V := (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hq'V : q' ∈ V := ⟨mul_pos hx0 (by linarith), mul_pos hx0 hy0, hq'.trans_lt hx1⟩
  have hΨV : ∀ p ∈ V, σ (triangleRetraction p) = e.symm (g (triangleToSquare p)) := by
    rintro p ⟨h1, h2, h12⟩
    rw [triangleRetraction_eq_squareCollapse_triangleToSquare h1 h2 h12]
    exact hσ _ (triangleToSquare_mem h1 h2 h12)
  have hfc : ContinuousOn (fun p ↦ g (triangleToSquare p)) V :=
    hg.continuousOn.comp (continuousOn_triangleToSquare.mono fun p hp ↦ (add_pos hp.1 hp.2.1).ne')
      fun p hp ↦ hsq (triangleToSquare_mem hp.1 hp.2.1 hp.2.2)
  have hΘq : triangleToSquare q' = p₀ := triangleToSquare_mul hx0.ne' p₀.2
  obtain ⟨LΘ, hΘd, hLΘ1, hLΘ2⟩ := hasFDerivAt_triangleToSquare hq's.ne'
  have hgd : HasFDerivAt g (fderiv ℝ g p₀) (triangleToSquare q') := by
    rw [hΘq]
    exact ((hg.contDiffAt (hUo.mem_nhds (hsq hp₀sq))).differentiableAt two_ne_zero).hasFDerivAt
  set L : ℝ × ℝ →L[ℝ] (Fin 1 → ℂ) := (fderiv ℝ g p₀).comp LΘ
  have hdet : 0 < (complexOrientationBasis 1).det
      ((L : ℝ × ℝ → Fin 1 → ℂ) ∘ Module.Basis.finTwoProd ℝ) :=
    complexOrientationBasis_one_det_comp_pos (D := fderiv ℝ g p₀) hq's hLΘ1 hLΘ2 (hJ 0)
  obtain ⟨δ, hδ, hloc⟩ := isLocallyHomologous_of_hasFDerivAt (X := T)
    (Module.Basis.finTwoProd ℝ) (complexOrientationBasis 1) e.open_target e.continuousOn_symm
    e.symm.injOn (hVo.mem_nhds hq'V) hfc (q := g p₀) (congrArg g hΘq) hgp (hgd.comp q' hΘd) hdet
  obtain ⟨u, hu, huW⟩ := exists_isOrientedSimplexAroundZero_subset (Module.Basis.finTwoProd ℝ) q'
    (Filter.inter_mem (Metric.ball_mem_nhds q' hδ) (hVo.mem_nhds hq'V))
  obtain ⟨hAO, hA⟩ := hloc u hu (huW.trans Set.inter_subset_left)
  set v : Fin (1 + 2) → (Fin 1 → ℂ) := fun k ↦ g p₀ + L (u k - q')
  let Δ : Simplex T (1 + 1) :=
    ⟨fun t ↦ e.symm (affineSimplex v t),
      e.continuousOn_symm.comp_continuous (affineSimplex v).continuous hAO⟩
  have h2 := hA ((σ.comp triangleRetraction).comp (affineSimplex u)) Δ
    (fun t ↦ hΨV _ (huW ⟨t, rfl⟩).2) (fun t ↦ rfl)
  refine ⟨v, ?_, Set.range_subset_iff.2 hAO, Δ, fun t ↦ rfl, ?_⟩
  · convert hu.map_linearMap (bH := complexOrientationBasis 1)
      (L : ℝ × ℝ →ₗ[ℝ] (Fin 1 → ℂ)) hdet using 1
    funext k
    simp [v, hex₀]
  · rw [← hx₀] at h2
    exact (isLocallyHomologous_comp_triangleRetraction σ hp₀ hinj hu).trans h2

/-- **Étale charts and the algebraic charts of `X_reg(ℂ)` induce the same local orientation.**
Let `c` be an étale coordinate chart of a smooth complex curve `X` and `x₀` a point of its
domain. Then `x₀` is a regular point of `X(ℂ)`, and for every affine simplex `Δ_c` of `c(X)`
around `c(x₀)` positively oriented for the complex orientation, `c⁻¹ ∘ Δ_c`, transported to
`X(ℂ)`, has the class in `H₂(X(ℂ), X(ℂ) - x₀; ℤ)` of a positively oriented simplex of the chart
at `x₀` of `X_reg(ℂ)`.

Read on `X(ℂ)`, the étale chart is itself an algebraic chart
(`MMP.Analytic.FundamentalChartCycle.isAlgebraicChart_etaleChartUnderlying`), hence a chart of the
complex manifold `X_reg(ℂ)`, whose atlas is oriented, and
`MMP.FundamentalClass.isLocallyHomologous_chartSimplexOf` compares the two chart
simplices; every point is regular by
`MMP.regularOpens_eq_top_of_smoothOfRelativeDimension`. -/
theorem exists_isLocallyHomologous_regularChart [IsComplexScheme X] [IsIntegral X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (hn : ((1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X)
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1)
    {x₀ : Analytification.space (X ↘ Spec (.of ℂ))} (hx₀ : x₀ ∈ c.toOpenPartialHomeomorph.source)
    {w : Fin (1 + 2) → (Fin 1 → ℂ)}
    (hw : IsOrientedSimplexAroundZero (complexOrientationBasis 1)
      fun k ↦ w k - c.toOpenPartialHomeomorph x₀)
    (hwt : range (affineSimplex w) ⊆ c.toOpenPartialHomeomorph.target)
    (Δc : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1))
    (hΔc : ∀ t, Δc t = c.toOpenPartialHomeomorph.symm (affineSimplex w t)) :
    letI := regularChartedSpace (𝕜 := ℂ) hn
    ∃ (x : regularOpens ℂ X) (_ : x.1 = ComplexPoints.homeomorphUnderlyingSpace (X := X) x₀)
      (v : Fin (1 + 2) → EuclideanSpace ℂ (Fin 1))
      (_ : IsOrientedSimplexAroundZero (euclideanComplexOrientationBasis 1)
        fun k ↦ v k - chartAt (EuclideanSpace ℂ (Fin 1)) x x)
      (_ : range (affineSimplex v) ⊆ (chartAt (EuclideanSpace ℂ (Fin 1)) x).target)
      (Δ : Simplex (TopCat.of (UnderlyingSpace ℂ X)) (1 + 1)),
      (∀ t, Δ t = ((chartAt (EuclideanSpace ℂ (Fin 1)) x).symm (affineSimplex v t) :
        UnderlyingSpace ℂ X)) ∧
      IsLocallyHomologous (X := UnderlyingSpace ℂ X) x.1
        ((⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩ :
          C(Analytification.space (X ↘ Spec (.of ℂ)), TopCat.of (UnderlyingSpace ℂ X))).comp Δc)
        Δ := by
  let := regularChartedSpace (𝕜 := ℂ) hn
  have htop := regularOpens_eq_top_of_smoothOfRelativeDimension (X := X) 1
  set Hm := ComplexPoints.homeomorphUnderlyingSpace (X := X)
  set Lh := EuclideanSpace.equiv (Fin 1) ℂ
  set E1 := etaleChartUnderlying c
  have hreg : Hm x₀ ∈ regularOpens ℂ X := by
    rw [htop]
    exact TopologicalSpace.Opens.mem_top _
  set x : regularOpens ℂ X := ⟨Hm x₀, hreg⟩
  have hne : Nonempty (regularOpens ℂ X) := ⟨x⟩
  set E1r := E1.subtypeRestr hne
  have hE1ra : E1r ∈ atlas (EuclideanSpace ℂ (Fin 1)) (regularOpens ℂ X) :=
    ⟨E1, hne, isAlgebraicChart_etaleChartUnderlying c, rfl⟩
  have hxs : x ∈ E1r.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    change Hm x₀ ∈ E1.source
    rw [mem_etaleChartUnderlying_source, Homeomorph.symm_apply_apply]
    exact hx₀
  have hE1rx : E1r x = Lh.symm (c.toOpenPartialHomeomorph x₀) := by
    change E1 (Hm x₀) = _
    rw [etaleChartUnderlying_apply, Homeomorph.symm_apply_apply]
  set bE' := euclideanComplexOrientationBasis 1
  set v₁ : Fin (1 + 2) → EuclideanSpace ℂ (Fin 1) := fun k ↦ Lh.symm (w k)
  have haff : ∀ t, affineSimplex v₁ t = Lh.symm (affineSimplex w t) :=
    affineSimplex_comp_linearMap (Lh.symm.toLinearEquiv.restrictScalars ℝ).toLinearMap w
  have hv₁ : IsOrientedSimplexAroundZero bE' fun k ↦ v₁ k - E1r x := by
    rw [hE1rx]
    exact isOrientedSimplexAroundZero_euclideanEquiv_symm hw
  have hvt₁ : range (affineSimplex v₁) ⊆ E1r.target := by
    rintro _ ⟨t, rfl⟩
    rw [mem_subtypeRestr_target_iff]
    refine ⟨?_, by rw [htop]; exact TopologicalSpace.Opens.mem_top _⟩
    rw [mem_etaleChartUnderlying_target, haff, ContinuousLinearEquiv.apply_symm_apply]
    exact hwt ⟨t, rfl⟩
  obtain ⟨v₂, hv₂, hv₂t⟩ := exists_isOrientedSimplexAroundZero_subset bE'
    (chartAt (EuclideanSpace ℂ (Fin 1)) x x)
    ((chartAt (EuclideanSpace ℂ (Fin 1)) x).open_target.mem_nhds (mem_chart_target _ x))
  have := isManifold_regularOpens (𝕜 := ℂ) (X := X) hn
  have : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 1)) 1 (regularOpens ℂ X) :=
    IsManifold.of_le le_top
  have hZ := isOrientedAtlas_of_isManifold_complex (E := EuclideanSpace ℂ (Fin 1))
    (regularOpens ℂ X)
  have hloc := isLocallyHomologous_chartSimplexOf hZ bE' hE1ra (chart_mem_atlas _ x) hxs
    (mem_chart_source _ x) hv₁ hvt₁ hv₂ hv₂t
  set sv : C(regularOpens ℂ X, UnderlyingSpace ℂ X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hmap := hloc.map sv Subtype.val_injective
  refine ⟨x, rfl, v₂, hv₂, hv₂t, sv.comp (chartSimplexOf _ v₂ hv₂t), fun t ↦ rfl, ?_⟩
  have hΔeq : (⟨_, Hm.continuous⟩ : C(Analytification.space (X ↘ Spec (.of ℂ)),
      TopCat.of (UnderlyingSpace ℂ X))).comp Δc = sv.comp (chartSimplexOf E1r v₁ hvt₁) := by
    refine ContinuousMap.ext fun t ↦ ?_
    change Hm (Δc t) = ((E1r.symm (affineSimplex v₁ t) : regularOpens ℂ X) : UnderlyingSpace ℂ X)
    rw [coe_subtypeRestr_symm_apply E1 hne (hvt₁ ⟨t, rfl⟩), etaleChartUnderlying_symm_apply,
      hΔc t, haff t, ContinuousLinearEquiv.apply_symm_apply]
  rwa [hΔeq]

/-- **The local class of an oriented chart triangle at a simple interior point.** Let `σ` be a
singular triangle of `X^an` which on the unit square is the read `c⁻¹ ∘ g` in an étale chart `c`
of a `C²` map `g`, and let `p₀` be an interior point of the square at which the Jacobian of `g`
is positive and over whose image `x₀ = σ(s(p₀))` the triangle is injective. Then `x₀` is a
regular point of `X(ℂ)`, and in the local homology `H₂(X(ℂ), X(ℂ) - x₀)` the triangle is the
class of a positively oriented simplex `Δ` of the chart at `x₀` of `X_reg(ℂ)`: every relative
cocycle takes the same value on both.

Near `s(p₀)` the collapse `s` is a diffeomorphism of positive Jacobian onto a neighbourhood in
`Δ²`, so `σ` is near `s(p₀)` an orientation-preserving local homeomorphism of class `C²` in the
chart `c`, and by injectivity over `x₀` it is locally, at `x₀`, the class of an affine simplex
around `c(x₀)` (excision and
`MMP.FundamentalClass.isLocallyHomologous_of_hasFDerivAt`);
the transition from `c` to the algebraic chart at `x₀` is holomorphic with nonzero derivative,
of positive real Jacobian determinant `|f'|²`
(`MMP.FundamentalClass.isLocallyHomologous_chartSimplexOf_of_det_pos`). -/
theorem exists_eq_of_mem_relCocycles_of_chartRead [IsComplexScheme X] [IsIntegral X]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (hn : ((1 : ℕ) : WithBot ℕ∞) = topologicalKrullDim X)
    (σ : Simplex (Analytification.space (X ↘ Spec (.of ℂ))) (1 + 1))
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1)
    (g : ℝ × ℝ → (Fin 1 → ℂ)) (U : Set (ℝ × ℝ)) (hUo : IsOpen U)
    (hsq : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ⊆ U) (hg : ContDiffOn ℝ 2 g U)
    (hgT : Set.MapsTo g U c.toOpenPartialHomeomorph.target)
    (hσ : ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      σ (squareCollapse p) = c.toOpenPartialHomeomorph.symm (g p))
    {p₀ : ℝ × ℝ} (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1)
    (hJ : ∀ i : Fin 1, 0 < chartJacobian g p₀ i)
    (hinj : ∀ t, σ t = σ (squareCollapse p₀) → t = squareCollapse p₀) :
    letI := regularChartedSpace (𝕜 := ℂ) hn
    ∃ (x : regularOpens ℂ X) (_ : x.1 = ComplexPoints.homeomorphUnderlyingSpace (X := X)
        (σ (squareCollapse p₀)))
      (v : Fin (1 + 2) → EuclideanSpace ℂ (Fin 1))
      (_ : IsOrientedSimplexAroundZero (euclideanComplexOrientationBasis 1)
        fun k ↦ v k - chartAt (EuclideanSpace ℂ (Fin 1)) x x)
      (_ : range (affineSimplex v) ⊆ (chartAt (EuclideanSpace ℂ (Fin 1)) x).target)
      (Δ : Simplex (TopCat.of (UnderlyingSpace ℂ X)) (1 + 1)),
      (∀ t, Δ t = ((chartAt (EuclideanSpace ℂ (Fin 1)) x).symm (affineSimplex v t) :
        UnderlyingSpace ℂ X)) ∧
      ∀ φ ∈ relCocycles ℂ ({x.1}ᶜ : Set (TopCat.of (UnderlyingSpace ℂ X))) (1 + 1),
        φ ((⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩ :
          C(Analytification.space (X ↘ Spec (.of ℂ)), TopCat.of (UnderlyingSpace ℂ X))).comp σ) =
          φ Δ := by
  obtain ⟨w, hw, hwt, Δc, hΔc, hloc⟩ := exists_isLocallyHomologous_of_chartRead
    c.toOpenPartialHomeomorph σ g U hUo hsq hg hgT hσ hp₀ hJ hinj
  have hp₀' : p₀ ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 :=
    ⟨Set.Ioo_subset_Icc_self hp₀.1, Set.Ioo_subset_Icc_self hp₀.2⟩
  have hx₀ : σ (squareCollapse p₀) ∈ c.toOpenPartialHomeomorph.source := by
    rw [hσ p₀ hp₀']
    exact c.toOpenPartialHomeomorph.map_target (hgT (hsq hp₀'))
  obtain ⟨x, hx, v, hv, hvt, Δ, hΔ, hloc'⟩ :=
    exists_isLocallyHomologous_regularChart hn c hx₀ hw hwt Δc hΔc
  set f : C(Analytification.space (X ↘ Spec (.of ℂ)), TopCat.of (UnderlyingSpace ℂ X)) :=
    ⟨_, (ComplexPoints.homeomorphUnderlyingSpace (X := X)).continuous⟩
  have hmap := hloc.map f (ComplexPoints.homeomorphUnderlyingSpace (X := X)).injective
  rw [show f (σ (squareCollapse p₀)) = x.1 from hx.symm] at hmap
  exact ⟨x, hx, v, hv, hvt, Δ, hΔ, fun φ hφ ↦ (hmap.apply_eq hφ).trans (hloc'.apply_eq hφ)⟩

end Curve

end MMP.Analytic.FundamentalChartCycle
