module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.Analysis.Complex.AvoidanceChart
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Divisor.Basic
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartDense
import MMP.AlgebraicGeometry.Analytic.BorelMoore
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Morphisms.Smooth.RegularParameters
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Analytic.PluriformDensity
import MMP.AlgebraicGeometry.Resolution.TransformRestriction
import MMP.AlgebraicGeometry.Divisor.NormalizationBranchesCofinite
import MMP.Analysis.Complex.CauchyTransformRungeMontel

/-!
# Holomorphic charts on smooth complex varieties, and branch counts of boundary divisors

**Holomorphic charts.** Let `P = ℂ[z₁, …, z_d, y₁, …, y_c]`, let `F₁, …, F_c, h ∈ P`, and let
`A = (P/(F₁, …, F_c))_h` be smooth over `ℂ`. A `ℂ`-point `p` of `Spec A` is a point of the
complex zero locus `Z = {F = 0, h ≠ 0} ⊆ ℂ^{d+c}`. If `det(∂F_i/∂y_j)` does not vanish at `p`,
then near `p` the zero locus is the graph of a holomorphic function of `z` over an open subset
of `ℂ^d`, and composing with this chart gives an injective ring homomorphism
`A_{𝔪_p} → 𝒪_{ℂ^d, z(p)}`. The chart comes from the analytic inverse function theorem applied
to `(z, y) ↦ (z, F(z, y))`. Injectivity follows because the classes of `zᵢ - zᵢ(p)` form a basis
of `𝔪_p/𝔪_p²`: an element with zero holomorphic germ then lies in every `𝔪_p^q`, and Krull's
intersection theorem finishes the argument.

**Avoidance charts.** Let `X` be a smooth complex variety and `U ⊆ X` a dense Zariski-open
subset. Every `ℂ`-point of `X` has an open neighbourhood in the complex realization that is
homeomorphic to the ball of an analytic avoidance chart, and this homeomorphism carries the
points lying over `X \ U` exactly onto the excluded set of the chart.

**Fundamental groups.** For `V` a connected smooth complex variety and `U ⊆ V` dense open, the
map `π₁(U^an, u) → π₁(V^an, u)` is surjective. Avoidance charts make the points over `U` locally
path connected and dense, and inside each chart paths with the same endpoints are homotopic. A
Lebesgue subdivision then deforms any loop into a loop over `U`.

**Branch counts.** Let `Y` be a normal complex fourfold and `Q` a finite set of prime divisors.
Every irreducible surface `V ⊆ ⋃ Q` has branch count `r_V ≥ 1`, and `r_V > 1` for only finitely
many `V`.

## Main results

* `MMP.Analytic.exists_holomorphic_chart_of_det_pderiv_ne_zero`: the holomorphic chart of a
  standard smooth presentation, and injectivity of the germ map.
* `MMP.Analytic.exists_analyticAvoidanceChart_of_dense`: avoidance charts.
* `MMP.Analytic.isOpenEmbedding_realize_ι_and_range`: the `ℂ`-points of a Zariski-open subset
  form an open subset of the `ℂ`-points of the variety.
* `MMP.Analytic.surjective_fundamentalGroupMap_realize_ι_of_dense`: surjectivity on `π₁`.
* `MMP.Fourfold.one_le_boundaryBranchCount_and_finite_setOf_one_lt`: finiteness of the branch
  excess.

## Implementation notes

The point `p` is a `ℂ`-algebra homomorphism `φ : A →ₐ[ℂ] ℂ` with `𝔪_p = ker φ`. Germs are taken
at `z(p)` in the coordinates `z`. Vanishing to order `n` at a point is expressed by
`Asymptotics.IsBigO` against `‖w - p‖ ^ n`, so the Taylor-series comparison is carried out
without power series. The avoidance charts are the algebraic charts
`MMP.UnderlyingSpace.exists_isAlgebraicChart` of the regular part, transported
along `MMP.Analytic.ComplexPoints.homeomorphUnderlyingSpace`. That some defining function does
not vanish identically on a chart follows from density of the points over `U`
(`MMP.UnderlyingSpace.dense_regularPart_diff`). The finitely supported branch
excess `V ↦ r_V - 1` is stated as two facts: `1 ≤ r_V`, and the set `{V | 1 < r_V}` is finite.

## References

* [Serre, *Géométrie algébrique et géométrie analytique*]
* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

@[expose] public section

open Filter Topology

namespace MMP.Analytic

/-! ### Holomorphic charts of a standard smooth presentation -/

section StandardSmoothChart

open Asymptotics MvPolynomial

variable {d c : ℕ}

/-- The derivative of a polynomial function is given by its partial derivatives. -/
private theorem hasFDerivAt_eval {σ : Type*} [Fintype σ] [DecidableEq σ]
    (q : MvPolynomial σ ℂ) (x : σ → ℂ) :
    HasFDerivAt (fun y : σ → ℂ => eval y q)
      (∑ v, eval x (pderiv v q) • (ContinuousLinearMap.proj v : (σ → ℂ) →L[ℂ] ℂ)) x := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a x
  | add a b ha hb =>
    have := ha.add hb
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact this
  | mul_X a i ha =>
    have := ha.mul (hasFDerivAt_apply i x)
    simp only [map_mul, eval_X]
    refine this.congr_fderiv ?_
    ext u
    simp [Finset.sum_add_distrib, add_mul, Pi.single_apply, Finset.sum_mul, mul_comm,
      mul_left_comm, Finset.mul_sum]
    simp only [apply_ite (eval x), map_zero, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- The map `(z, y) ↦ (z, F(z, y))`. -/
private noncomputable def graphMap (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ)
    (x : Fin d ⊕ Fin c → ℂ) :
    Fin d ⊕ Fin c → ℂ :=
  Sum.elim (fun i => x (Sum.inl i)) (fun j => eval x (F j))

/-- The derivative of `graphMap F`. -/
private theorem hasFDerivAt_graphMap (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ)
    (x : Fin d ⊕ Fin c → ℂ) :
    HasFDerivAt (graphMap F) (ContinuousLinearMap.pi fun v => Sum.elim
      (fun i => (ContinuousLinearMap.proj (Sum.inl i) : (Fin d ⊕ Fin c → ℂ) →L[ℂ] ℂ))
      (fun j => ∑ v, eval x (pderiv v (F j)) •
        (ContinuousLinearMap.proj v : (Fin d ⊕ Fin c → ℂ) →L[ℂ] ℂ)) v) x := by
  rw [hasFDerivAt_pi]
  rintro (i | j)
  · exact hasFDerivAt_apply _ x
  · exact hasFDerivAt_eval (F j) x

/-- The derivative of `graphMap F` is injective where `det(∂Fᵢ/∂yⱼ) ≠ 0`. -/
private theorem injective_graphMap_fderiv (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ)
    (x : Fin d ⊕ Fin c → ℂ)
    (hdet : eval x (Matrix.of fun i j => pderiv (Sum.inr j) (F i)).det ≠ 0) :
    Function.Injective (ContinuousLinearMap.pi fun v => Sum.elim
      (fun i => (ContinuousLinearMap.proj (Sum.inl i) : (Fin d ⊕ Fin c → ℂ) →L[ℂ] ℂ))
      (fun j => ∑ v, eval x (pderiv v (F j)) •
        (ContinuousLinearMap.proj v : (Fin d ⊕ Fin c → ℂ) →L[ℂ] ℂ)) v) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have h1 : ∀ i, u (Sum.inl i) = 0 := fun i => by simpa using congrFun hu (Sum.inl i)
  have h2 : ∀ j, ∑ v, eval x (pderiv v (F j)) * u v = 0 := fun j => by
    simpa using congrFun hu (Sum.inr j)
  set M := (eval x).mapMatrix (Matrix.of fun i j => pderiv (Sum.inr j) (F i))
  have hM : M.det ≠ 0 := by rwa [← RingHom.map_det]
  have hMu : M.mulVec (fun k => u (Sum.inr k)) = 0 := by
    funext j
    have := h2 j
    rw [Fintype.sum_sum_type] at this
    simpa [Matrix.mulVec, dotProduct, M, mul_comm, h1] using this
  funext v
  rcases v with i | k
  · exact h1 i
  · exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hMu) k

/-- **Holomorphic chart of the zero locus.** Near a zero `x₀` of `F` with `h(x₀) ≠ 0` and
`det(∂Fᵢ/∂yⱼ)(x₀) ≠ 0`, the projection to `z` restricts to a bijection from the zero locus onto
an open set, with holomorphic inverse. -/
private theorem exists_chart (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ)
    (h : MvPolynomial (Fin d ⊕ Fin c) ℂ) (x₀ : Fin d ⊕ Fin c → ℂ)
    (hF : ∀ j, eval x₀ (F j) = 0) (hh : eval x₀ h ≠ 0)
    (hdet : eval x₀ (Matrix.of fun i j => pderiv (Sum.inr j) (F i)).det ≠ 0) :
    ∃ (U : Set (Fin d ⊕ Fin c → ℂ)) (V : Set (Fin d → ℂ))
      (g : (Fin d → ℂ) → Fin d ⊕ Fin c → ℂ),
      U ∈ 𝓝 x₀ ∧ IsOpen V ∧ (fun i => x₀ (Sum.inl i)) ∈ V ∧ DifferentiableOn ℂ g V ∧
      (∀ w ∈ V, g w ∈ {x | (∀ i, eval x (F i) = 0) ∧ eval x h ≠ 0} ∩ U ∧
        (fun i => g w (Sum.inl i)) = w) ∧
      (∀ x ∈ {x | (∀ i, eval x (F i) = 0) ∧ eval x h ≠ 0} ∩ U,
        (fun i => x (Sum.inl i)) ∈ V ∧ g (fun i => x (Sum.inl i)) = x) := by
  set L := ContinuousLinearMap.pi fun v => Sum.elim
      (fun i => (ContinuousLinearMap.proj (Sum.inl i) : (Fin d ⊕ Fin c → ℂ) →L[ℂ] ℂ))
      (fun j => ∑ v, eval x₀ (pderiv v (F j)) •
        (ContinuousLinearMap.proj v : (Fin d ⊕ Fin c → ℂ) →L[ℂ] ℂ)) v
  let f' : (Fin d ⊕ Fin c → ℂ) ≃L[ℂ] (Fin d ⊕ Fin c → ℂ) :=
    (LinearEquiv.ofInjectiveEndo L.toLinearMap
      (injective_graphMap_fderiv F x₀ hdet)).toContinuousLinearEquiv
  have hf' : HasFDerivAt (graphMap F) (f' : (Fin d ⊕ Fin c → ℂ) →L[ℂ] _) x₀ :=
    (hasFDerivAt_graphMap F x₀).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have han : AnalyticAt ℂ (graphMap F) x₀ := by
    refine analyticAt_pi_iff.2 fun v => ?_
    rcases v with i | j
    · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ⊕ Fin c => ℂ)
        (Sum.inl i)).analyticAt _
    · have := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (A := ℂ) (B := ℂ) (z := x₀)
        (f := fun x => x) (fun i => (ContinuousLinearMap.proj (R := ℂ)
          (φ := fun _ : Fin d ⊕ Fin c => ℂ) i).analyticAt _) (F j)
      simpa [graphMap, MvPolynomial.coe_aeval_eq_eval] using this
  obtain ⟨e, hx₀, -, hfe, -, hsymm⟩ :=
    MMP.Analytic.exists_openPartialHomeomorph_analyticOnNhd_symm han hf'
  let emb : (Fin d → ℂ) → Fin d ⊕ Fin c → ℂ := fun w => Sum.elim w (fun _ => 0)
  have hemb : Differentiable ℂ emb := by
    refine differentiable_pi.2 fun v => ?_
    rcases v with i | j
    · exact differentiable_apply i
    · exact differentiable_const _
  have hΦ : ∀ x, (∀ j, eval x (F j) = 0) → graphMap F x = emb (fun i => x (Sum.inl i)) := by
    intro x hx
    funext v
    rcases v with i | j
    · rfl
    · exact hx j
  let g : (Fin d → ℂ) → Fin d ⊕ Fin c → ℂ := fun w => e.symm (emb w)
  have hgc : ContinuousOn g (emb ⁻¹' e.target) :=
    e.continuousOn_symm.comp hemb.continuous.continuousOn fun w hw => hw
  have hgs : ∀ w ∈ emb ⁻¹' e.target, g w ∈ e.source ∧ graphMap F (g w) = emb w :=
    fun w hw => ⟨e.map_target hw, (hfe (e.map_target hw)).trans (e.right_inv hw)⟩
  refine ⟨e.source ∩ {x | eval x h ≠ 0}, emb ⁻¹' e.target ∩ g ⁻¹' {x | eval x h ≠ 0}, g,
    Filter.inter_mem (e.open_source.mem_nhds hx₀)
      ((isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const).mem_nhds hh),
    hgc.isOpen_inter_preimage (e.open_target.preimage hemb.continuous)
      (isOpen_ne_fun (MvPolynomial.continuous_eval h) continuous_const), ?_, ?_, ?_, ?_⟩
  · have h1 : emb (fun i => x₀ (Sum.inl i)) = e x₀ := (hΦ x₀ hF).symm.trans (hfe hx₀)
    have h2 : g (fun i => x₀ (Sum.inl i)) = x₀ := by
      simp only [g, h1, e.left_inv hx₀]
    refine ⟨show emb _ ∈ e.target from h1 ▸ e.map_source hx₀, ?_⟩
    simpa only [Set.mem_preimage, Set.mem_setOf_eq, h2] using hh
  · intro w hw
    exact ((hsymm _ hw.1).differentiableAt.comp w (hemb w)).differentiableWithinAt
  · intro w hw
    obtain ⟨hs, hg⟩ := hgs w hw.1
    refine ⟨⟨⟨fun j => ?_, hw.2⟩, hs, hw.2⟩, ?_⟩
    · simpa [graphMap, emb] using congrFun hg (Sum.inr j)
    · funext i
      simpa [graphMap, emb] using congrFun hg (Sum.inl i)
  · rintro x ⟨⟨hxF, hxh⟩, hxs, -⟩
    have h1 : emb (fun i => x (Sum.inl i)) = e x := (hΦ x hxF).symm.trans (hfe hxs)
    have h2 : g (fun i => x (Sum.inl i)) = x := by simp only [g, h1, e.left_inv hxs]
    refine ⟨⟨show emb _ ∈ e.target from h1 ▸ e.map_source hxs, ?_⟩, h2⟩
    simpa only [Set.mem_preimage, Set.mem_setOf_eq, h2] using hxh

section OrderIdeal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The holomorphic germs at `p` vanishing to order at least `n`: those with a representative
that is `O(‖w - p‖ ^ n)` near `p`. -/
private def orderIdeal (p : E) (n : ℕ) : Ideal (holGerms p) where
  carrier := {x | ∃ f : E → ℂ, (f : Germ (𝓝 p) ℂ) = x ∧ f =O[𝓝 p] fun w => ‖w - p‖ ^ n}
  zero_mem' := ⟨0, rfl, isBigO_zero _ _⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, hfO⟩ ⟨g, hg, hgO⟩
    exact ⟨f + g, by rw [Subring.coe_add, ← hf, ← hg]; rfl, hfO.add hgO⟩
  smul_mem' := by
    rintro x _ ⟨f, hf, hfO⟩
    obtain ⟨u, hu, hud⟩ := x.2
    refine ⟨fun w => u w * f w, ?_, ?_⟩
    · rw [smul_eq_mul, Subring.coe_mul, ← hf, ← hu]; rfl
    · have h1 : u =O[𝓝 p] fun _ => (1 : ℝ) :=
        hud.self_of_nhds.continuousAt.tendsto.isBigO_one ℝ
      simpa only [one_mul] using h1.mul hfO

/-- Orders of vanishing add under multiplication. -/
private theorem mul_le_orderIdeal (p : E) (a b : ℕ) :
    orderIdeal p a * orderIdeal p b ≤ orderIdeal p (a + b) := by
  refine Ideal.mul_le.2 ?_
  rintro _ ⟨f, hf, hfO⟩ _ ⟨g, hg, hgO⟩
  refine ⟨fun w => f w * g w, by rw [Subring.coe_mul, ← hf, ← hg]; rfl, ?_⟩
  simpa only [← pow_add] using hfO.mul hgO

/-- A germ vanishing at the base point vanishes to order one. -/
private theorem mem_orderIdeal_one (p : E) (x : holGerms p)
    (hx : Germ.value (x : Germ (𝓝 p) ℂ) = 0) : x ∈ orderIdeal p 1 := by
  obtain ⟨f, hf, hfd⟩ := x.2
  rw [← hf, Germ.value_ofFun] at hx
  refine ⟨f, hf, ?_⟩
  simpa [hx] using hfd.self_of_nhds.hasFDerivAt.isBigO_sub.norm_right

/-- Powers of an ideal of germs vanishing to order one vanish to the corresponding order. -/
private theorem pow_le_orderIdeal (p : E) (I : Ideal (holGerms p)) (hI : I ≤ orderIdeal p 1) :
    ∀ n, I ^ n ≤ orderIdeal p n
  | 0 => by
    rw [pow_zero, Ideal.one_eq_top]
    intro x _
    obtain ⟨u, hu, hud⟩ := x.2
    exact ⟨u, hu, by simpa using hud.self_of_nhds.continuousAt.tendsto.isBigO_one ℝ⟩
  | n + 1 => by
    rw [pow_succ]
    exact (Ideal.mul_mono (pow_le_orderIdeal p I hI n) hI).trans (mul_le_orderIdeal p n 1)

end OrderIdeal

/-- The polynomials whose function is `O(‖v‖ ^ m)` at the origin. -/
private def vanishIdeal (d m : ℕ) : Ideal (MvPolynomial (Fin d) ℂ) where
  carrier := {r | (fun v => eval v r) =O[𝓝 (0 : Fin d → ℂ)] fun v => ‖v‖ ^ m}
  zero_mem' := by simpa using isBigO_zero _ _
  add_mem' := fun ha hb => by simpa using ha.add hb
  smul_mem' := fun c r hr => by
    have h1 : (fun v => eval v c) =O[𝓝 (0 : Fin d → ℂ)] fun _ => (1 : ℝ) :=
      ((MvPolynomial.continuous_eval c).tendsto 0).isBigO_one ℝ
    simpa using h1.mul hr

/-- Every polynomial in `(X)^m` vanishes to order `m` at the origin. -/
private theorem pow_idealOfVars_le (d : ℕ) : ∀ m, idealOfVars (Fin d) ℂ ^ m ≤ vanishIdeal d m
  | 0 => by
    rw [pow_zero, Ideal.one_eq_top]
    intro r _
    change (fun v => eval v r) =O[𝓝 0] fun v => ‖v‖ ^ 0
    simp only [pow_zero]
    exact ((MvPolynomial.continuous_eval r).tendsto 0).isBigO_one ℝ
  | m + 1 => by
    rw [pow_succ]
    refine Ideal.mul_le.2 fun r hr s hs => ?_
    have h1 : idealOfVars (Fin d) ℂ ≤ vanishIdeal d 1 := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      refine isBigO_of_le _ fun v => ?_
      simpa using norm_le_pi_norm v i
    have := (pow_idealOfVars_le d m hr).mul (h1 hs)
    change (fun v => eval v (r * s)) =O[𝓝 0] fun v => ‖v‖ ^ (m + 1)
    simpa only [map_mul, pow_succ, pow_zero, one_mul] using this

/-- A homogeneous component of degree `k` scales by `s ^ k`. -/
private theorem eval_smul_homogeneousComponent (k : ℕ) (f : MvPolynomial (Fin d) ℂ) (s : ℂ)
    (u : Fin d → ℂ) :
    eval (s • u) (homogeneousComponent k f) = s ^ k * eval u (homogeneousComponent k f) := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hdeg : x.degree = k := by
    rw [mem_support_iff, coeff_homogeneousComponent] at hx
    by_contra h
    exact hx (if_neg h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [show ∑ i ∈ x.support, x i = k from hdeg]
  ring

/-- If `s ^ k * c = O(‖s‖ ^ (k + 1))` at `0`, then `c = 0`. -/
private theorem eq_zero_of_isBigO_pow (k : ℕ) (c : ℂ)
    (h : (fun s : ℂ => s ^ k * c) =O[𝓝 0] fun s => ‖s‖ ^ (k + 1)) : c = 0 := by
  have h1 := (h.mono (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)).mul
    (isBigO_refl (fun s : ℂ => (s ^ k)⁻¹) (𝓝[≠] 0)).norm_right
  have h2 : (fun _ : ℂ => c) =O[𝓝[≠] 0] fun s : ℂ => ‖s‖ := by
    refine (h1.congr' ?_ ?_)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      field_simp [pow_ne_zero k hs]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hs
      simp only [norm_inv, norm_pow]
      field_simp
      ring
  have h3 : Tendsto (fun _ : ℂ => c) (𝓝[≠] 0) (𝓝 0) := by
    refine h2.trans_tendsto ?_
    have : Tendsto (fun s : ℂ => ‖s‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm.tendsto (0 : ℂ))
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique tendsto_const_nhds h3

/-- A polynomial whose function vanishes to order `n` at the origin lies in the `n`-th power of
the ideal of the variables. -/
private theorem mem_pow_idealOfVars_of_isBigO (f : MvPolynomial (Fin d) ℂ) (n : ℕ)
    (hf : (fun v => eval v f) =O[𝓝 0] fun v : Fin d → ℂ => ‖v‖ ^ n) :
    f ∈ idealOfVars (Fin d) ℂ ^ n := by
  classical
  by_contra hne
  have hex : ∃ k, k < n ∧ homogeneousComponent k f ≠ 0 := by
    rw [mem_pow_idealOfVars_iff'] at hne
    push Not at hne
    obtain ⟨x, hx, hcx⟩ := hne
    refine ⟨x.degree, hx, fun h0 => hcx ?_⟩
    have := MvPolynomial.ext_iff.mp h0 x
    rwa [coeff_homogeneousComponent, if_pos rfl, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at this
  set k := Nat.find hex with hkdef
  obtain ⟨hkn, hk0⟩ := Nat.find_spec hex
  have hmin : ∀ j < k, homogeneousComponent j f = 0 := fun j hj => by
    by_contra h
    exact Nat.find_min hex hj ⟨hj.trans hkn, h⟩
  have hr : f - homogeneousComponent k f ∈ idealOfVars (Fin d) ℂ ^ (k + 1) := by
    rw [mem_pow_idealOfVars_iff']
    intro y hy
    rw [coeff_sub, coeff_homogeneousComponent]
    by_cases hyk : y.degree = k
    · rw [if_pos hyk, sub_self]
    · rw [if_neg hyk, sub_zero]
      have hlt : y.degree < k := by omega
      have := MvPolynomial.ext_iff.mp (hmin _ hlt) y
      rwa [coeff_homogeneousComponent, if_pos rfl, AddMonoidAlgebra.coeff_zero,
        Finsupp.zero_apply] at this
  have hrO := pow_idealOfVars_le d (k + 1) hr
  obtain ⟨u, hu⟩ : ∃ u, eval u (homogeneousComponent k f) ≠ 0 := by
    by_contra h
    push Not at h
    exact hk0 (MvPolynomial.funext fun u => by simpa using h u)
  have hT : Tendsto (fun s : ℂ => s • u) (𝓝 0) (𝓝 0) := by
    have : Continuous fun s : ℂ => s • u := by fun_prop
    simpa using this.tendsto 0
  have hnorm : ∀ m : ℕ, (fun s : ℂ => ‖s • u‖ ^ m) =O[𝓝 0] fun s : ℂ => ‖s‖ ^ m := fun m =>
    isBigO_of_le' (c := ‖u‖ ^ m) _ fun s => by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
      simp
  have hpow : (fun s : ℂ => ‖s‖ ^ n) =O[𝓝 0] fun s : ℂ => ‖s‖ ^ (k + 1) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with s hs
    rw [Metric.mem_ball, dist_zero_right] at hs
    simp only [norm_pow, norm_norm, one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) hs.le hkn
  have h1 := ((hf.comp_tendsto hT).trans ((hnorm n).trans hpow))
  have h2 := (hrO.comp_tendsto hT).trans (hnorm (k + 1))
  have h3 : (fun s : ℂ => s ^ k * eval u (homogeneousComponent k f)) =O[𝓝 0]
      fun s => ‖s‖ ^ (k + 1) := by
    refine (h1.sub h2).congr' (Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    simp [Function.comp_def, eval_smul_homogeneousComponent]
  exact hu (eq_zero_of_isBigO_pow k _ h3)

/-- Polynomial expressions in `t` go to the corresponding polynomial germs in `w - z₀`. -/
private theorem coe_aeval_eq {S : Type*} [CommRing S] [Algebra ℂ S] {z₀ : Fin d → ℂ}
    (ρA : S →+* holGerms z₀)
    (hC : ∀ c : ℂ, (ρA (algebraMap ℂ S c) : Germ (𝓝 z₀) ℂ) = ((fun _ => c : (Fin d → ℂ) → ℂ) :
      Germ (𝓝 z₀) ℂ))
    (t : Fin d → S)
    (ht : ∀ i, (ρA (t i) : Germ (𝓝 z₀) ℂ) = ((fun w => w i - z₀ i : (Fin d → ℂ) → ℂ) :
      Germ (𝓝 z₀) ℂ)) (f : MvPolynomial (Fin d) ℂ) :
    (ρA (aeval t f) : Germ (𝓝 z₀) ℂ) =
      ((fun w => eval (w - z₀) f : (Fin d → ℂ) → ℂ) : Germ (𝓝 z₀) ℂ) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, hC]
    exact Germ.coe_eq.2 (Eventually.of_forall fun w => by simp)
  | add p q hp hq =>
    rw [map_add, map_add, Subring.coe_add, hp, hq, ← Germ.coe_add]
    exact Germ.coe_eq.2 (Eventually.of_forall fun w => by simp)
  | mul_X p i hp =>
    rw [map_mul, map_mul, Subring.coe_mul, hp, aeval_X, ht, ← Germ.coe_mul]
    exact Germ.coe_eq.2 (Eventually.of_forall fun w => by simp)

/-- If a polynomial `f` in `t` maps into the germs vanishing to order `n`, then `f` lies in the
`n`-th power of the ideal of the variables. -/
private theorem mem_pow_idealOfVars_of_mem_orderIdeal {S : Type*} [CommRing S] [Algebra ℂ S]
    {z₀ : Fin d → ℂ} (ρA : S →+* holGerms z₀)
    (hC : ∀ c : ℂ, (ρA (algebraMap ℂ S c) : Germ (𝓝 z₀) ℂ) = ((fun _ => c : (Fin d → ℂ) → ℂ) :
      Germ (𝓝 z₀) ℂ))
    (t : Fin d → S)
    (ht : ∀ i, (ρA (t i) : Germ (𝓝 z₀) ℂ) = ((fun w => w i - z₀ i : (Fin d → ℂ) → ℂ) :
      Germ (𝓝 z₀) ℂ)) (f : MvPolynomial (Fin d) ℂ) (n : ℕ)
    (hf : ρA (aeval t f) ∈ orderIdeal z₀ n) : f ∈ idealOfVars (Fin d) ℂ ^ n := by
  obtain ⟨u, hu, huO⟩ := hf
  have hfO : (fun w => eval (w - z₀) f) =O[𝓝 z₀] fun w => ‖w - z₀‖ ^ n :=
    huO.congr' (Germ.coe_eq.1 (hu.trans (coe_aeval_eq ρA hC t ht f))) EventuallyEq.rfl
  have hT : Tendsto (fun v : Fin d → ℂ => v + z₀) (𝓝 0) (𝓝 z₀) := by
    have : Continuous fun v : Fin d → ℂ => v + z₀ := by fun_prop
    simpa using this.tendsto 0
  refine mem_pow_idealOfVars_of_isBigO f n ?_
  simpa [Function.comp_def] using hfO.comp_tendsto hT

/-- **Algebraic germs are determined by their holomorphic germs.** Let `S` be a smooth noetherian
`ℂ`-algebra with a point `σ`, and `ρA : S →+* holGerms z₀` a ring map compatible with values at the
base point and with constants, sending elements `tᵢ` to the coordinate germs `wᵢ - z₀ᵢ`. If the
classes of the `tᵢ` span `𝔪/𝔪²` for `𝔪 = ker σ`, then every element killed by `ρA` vanishes in
the local ring `S_𝔪`, i.e. some `m ∉ 𝔪` annihilates it. -/
private theorem exists_mul_eq_zero_of_germ_eq_zero {S : Type*} [CommRing S] [Algebra ℂ S]
    [Algebra.FormallySmooth ℂ S] [IsNoetherianRing S] (σ : S →ₐ[ℂ] ℂ) [(RingHom.ker σ).IsPrime]
    {z₀ : Fin d → ℂ}
    (ρA : S →+* holGerms z₀) (hev : ∀ a, Germ.value (ρA a : Germ (𝓝 z₀) ℂ) = σ a)
    (hC : ∀ c : ℂ, (ρA (algebraMap ℂ S c) : Germ (𝓝 z₀) ℂ) = ((fun _ => c : (Fin d → ℂ) → ℂ) :
      Germ (𝓝 z₀) ℂ))
    (t : Fin d → S)
    (ht : ∀ i, (ρA (t i) : Germ (𝓝 z₀) ℂ) = ((fun w => w i - z₀ i : (Fin d → ℂ) → ℂ) :
      Germ (𝓝 z₀) ℂ))
    (htm : ∀ i, t i ∈ RingHom.ker σ)
    (hspan : Submodule.span ℂ (Set.range fun i => (RingHom.ker σ).toCotangent ⟨t i, htm i⟩) = ⊤)
    (a : S) (ha : ρA a = 0) :
    ∃ m : (RingHom.ker σ).primeCompl, (m : S) * a = 0 := by
  have hm1 : (RingHom.ker σ).map ρA ≤ orderIdeal z₀ 1 :=
    Ideal.map_le_iff_le_comap.2 fun a ha => mem_orderIdeal_one _ _ ((hev a).trans ha)
  have hmn : ∀ n, (RingHom.ker σ ^ n).map ρA ≤ orderIdeal z₀ n := fun n => by
    rw [Ideal.map_pow]
    exact pow_le_orderIdeal _ _ hm1 n
  have hli : LinearIndependent ℂ fun i => (RingHom.ker σ).toCotangent ⟨t i, htm i⟩ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    set f : MvPolynomial (Fin d) ℂ := ∑ j, C (c j) * X j
    have hft : aeval t f = ∑ j, c j • t j := by
      simp [f, Algebra.smul_def]
    have hfm : aeval t f ∈ RingHom.ker σ ^ 2 := by
      have h0 : (RingHom.ker σ).toCotangent (∑ j, c j • (⟨t j, htm j⟩ : RingHom.ker σ)) = 0 := by
        rw [map_sum]
        simp_rw [LinearMap.map_smul_of_tower]
        exact hc
      simpa [hft] using (Ideal.toCotangent_eq_zero _ _).1 h0
    have := mem_pow_idealOfVars_of_mem_orderIdeal ρA hC t ht f 2
      (hmn 2 (Ideal.mem_map_of_mem _ hfm))
    rw [mem_pow_idealOfVars_iff'] at this
    have h2 := this (Finsupp.single i 1) (by simp)
    simpa [f, coeff_sum, coeff_C_mul, coeff_X', Finsupp.single_eq_single_iff] using h2
  let b := Module.Basis.mk hli hspan.ge
  have hb : ∀ i, ∃ hi : t i ∈ RingHom.ker σ, (RingHom.ker σ).toCotangent ⟨t i, hi⟩ = b i :=
    fun i => ⟨htm i, by simp [b]⟩
  have hpow : ∀ n, a ∈ RingHom.ker σ ^ n := by
    intro n
    let e := MMP.quotientPowAevalEquiv σ b t hb n
    have he := MMP.quotientPowAevalEquiv_mk σ b t hb n
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e.symm (Ideal.Quotient.mk _ a))
    have hfa : Ideal.Quotient.mk (RingHom.ker σ ^ n) (aeval t f) = Ideal.Quotient.mk _ a :=
      (he f).symm.trans ((congrArg e hf).trans (e.apply_symm_apply _))
    have hsub : aeval t f - a ∈ RingHom.ker σ ^ n := Ideal.Quotient.eq.1 hfa
    have hmem : ρA (aeval t f) ∈ orderIdeal z₀ n := by
      have := hmn n (Ideal.mem_map_of_mem ρA hsub)
      rwa [map_sub, ha, sub_zero] at this
    have hmk : Ideal.Quotient.mk (idealOfVars (Fin d) ℂ ^ n) f = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2
        (mem_pow_idealOfVars_of_mem_orderIdeal ρA hC t ht f n hmem)
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hfa, ← he, hmk, map_zero]
  have : algebraMap S (Localization.AtPrime (RingHom.ker σ)) a ∈
      ⨅ n, (IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker σ))) ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hpow n)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top,
    Ideal.mem_bot] at this
  exact (IsLocalization.map_eq_zero_iff (RingHom.ker σ).primeCompl _ a).1 this

/-- **First-order Taylor expansion.** Let `ι : ℂ[x] → A` be a ring map compatible with constants
and `I ⊆ A` an ideal containing every `ι q - q(x₀)`. Then `ι q` agrees with its linearization
`q(x₀) + ∑ᵥ (∂ᵥq)(x₀) ι(xᵥ - x₀ᵥ)` modulo `I²`. -/
private theorem sub_sum_pderiv_smul_mem_sq {σ : Type*} [Fintype σ] [DecidableEq σ] {A : Type*}
    [CommRing A] [Algebra ℂ A] (ι : MvPolynomial σ ℂ →+* A)
    (hιC : ∀ a, ι (C a) = algebraMap ℂ A a) (I : Ideal A) (x₀ : σ → ℂ)
    (hI : ∀ q, ι q - algebraMap ℂ A (eval x₀ q) ∈ I) (q : MvPolynomial σ ℂ) :
    ι q - algebraMap ℂ A (eval x₀ q) - ∑ v, eval x₀ (pderiv v q) • ι (X v - C (x₀ v)) ∈
      I ^ 2 := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [hιC]
  | add p q hp hq =>
    convert add_mem hp hq using 1
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    ring
  | mul_X p i hp =>
    have hs : ι (X i) = ι (X i - C (x₀ i)) + algebraMap ℂ A (x₀ i) := by
      rw [map_sub, hιC]; ring
    have key : ι (p * X i) - algebraMap ℂ A (eval x₀ (p * X i)) -
        ∑ v, eval x₀ (pderiv v (p * X i)) • ι (X v - C (x₀ v)) =
        x₀ i • (ι p - algebraMap ℂ A (eval x₀ p) -
          ∑ v, eval x₀ (pderiv v p) • ι (X v - C (x₀ v))) +
        (ι p - algebraMap ℂ A (eval x₀ p)) * ι (X i - C (x₀ i)) := by
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X,
        add_smul, Finset.sum_add_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
        map_zero, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [hs]
      simp only [Algebra.smul_def, map_mul, Finset.mul_sum, Finset.sum_mul, apply_ite (eval x₀),
        apply_ite (algebraMap ℂ A), map_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true]
      simp only [mul_sub, Finset.mul_sum, mul_assoc]
      ring
    have hsi : ι (X i - C (x₀ i)) ∈ I := by
      have := hI (X i - C (x₀ i))
      rwa [map_sub (eval x₀), eval_X, eval_C, sub_self, map_zero, sub_zero] at this
    rw [key]
    refine add_mem (Submodule.smul_of_tower_mem _ _ hp) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (hI p) hsi

/-- **The cotangent space of a standard presentation at a point.** Let `ι : ℂ[z, y] → A` be a
ring map compatible with constants and killing the relations `Fⱼ`, such that every element of `A`
is `ι q * b` with `b` a unit. At a point `φ : A → ℂ` where `det(∂Fᵢ/∂yⱼ)` does not vanish, the
classes of the `ι(zᵢ - zᵢ(φ))` span `𝔪/𝔪²` for `𝔪 = ker φ`: by first-order Taylor expansion every
class is a combination of the `[ι(xᵥ - xᵥ(φ))]`, and the linear parts of the relations `Fⱼ`
express each `dyⱼ` through the `dzᵢ`. -/
private theorem span_toCotangent_eq_top_of_forall_eq_mul {A : Type*} [CommRing A]
    [Algebra ℂ A] (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ)
    (ι : MvPolynomial (Fin d ⊕ Fin c) ℂ →+* A) (hιC : ∀ a, ι (C a) = algebraMap ℂ A a)
    (hιF : ∀ j, ι (F j) = 0) (hsurj : ∀ a : A, ∃ q b, IsUnit b ∧ a = ι q * b)
    (φ : A →ₐ[ℂ] ℂ)
    (hdet : MvPolynomial.eval (fun v => φ (ι (X v)))
        (Matrix.of fun i j => MvPolynomial.pderiv (Sum.inr j) (F i)).det ≠ 0)
    (htm : ∀ i, ι (X (Sum.inl i) - C (φ (ι (X (Sum.inl i))))) ∈ RingHom.ker φ) :
    Submodule.span ℂ (Set.range fun i => (RingHom.ker φ).toCotangent ⟨_, htm i⟩) = ⊤ := by
  let x₀ : Fin d ⊕ Fin c → ℂ := fun v => φ (ι (X v))
  have hev : ∀ q, φ (ι q) = eval x₀ q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => rw [hιC, φ.commutes, eval_C, Algebra.algebraMap_self, RingHom.id_apply]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p i hp => rw [map_mul, map_mul, hp, map_mul, eval_X]
  have hI : ∀ q, ι q - algebraMap ℂ _ (eval x₀ q) ∈ RingHom.ker φ := fun q => by
    rw [RingHom.mem_ker, map_sub, hev, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  have hT := sub_sum_pderiv_smul_mem_sq ι hιC (RingHom.ker φ) x₀ hI
  have hs : ∀ v, ι (X v - C (x₀ v)) ∈ RingHom.ker φ := fun v => by
    have := hI (X v - C (x₀ v))
    rwa [map_sub (eval x₀), eval_X, eval_C, sub_self, map_zero, sub_zero] at this
  let e : Fin d ⊕ Fin c → (RingHom.ker φ).Cotangent := fun v =>
    (RingHom.ker φ).toCotangent ⟨_, hs v⟩
  have hsum : ∀ γ : Fin d ⊕ Fin c → ℂ, ∑ v, γ v • e v =
      (RingHom.ker φ).toCotangent ⟨∑ v, γ v • ι (X v - C (x₀ v)),
        Submodule.sum_mem _ fun v _ => Submodule.smul_of_tower_mem _ _ (hs v)⟩ := by
    intro γ
    have : (⟨∑ v, γ v • ι (X v - C (x₀ v)),
        Submodule.sum_mem _ fun v _ => Submodule.smul_of_tower_mem _ _ (hs v)⟩ :
          RingHom.ker φ) = ∑ v, γ v • (⟨_, hs v⟩ : RingHom.ker φ) := by
      ext; simp
    rw [this, map_sum]
    simp_rw [LinearMap.map_smul_of_tower]
    rfl
  -- the classes of all the `xᵥ - x₀ᵥ` span the cotangent space
  have hall : Submodule.span ℂ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨⟨a, ha⟩, rfl⟩ := (RingHom.ker φ).toCotangent_surjective x
    obtain ⟨q, b, hbu, hab⟩ := hsurj a
    have hb0 : φ b ≠ 0 := (hbu.map φ).ne_zero
    have ha' := ha
    rw [hab] at ha'
    have hq0 : eval x₀ q = 0 := by
      rw [RingHom.mem_ker, map_mul, hev] at ha'
      exact (mul_eq_zero.1 ha').resolve_right hb0
    have hx : (RingHom.ker φ).toCotangent ⟨_, ha⟩ =
        ∑ v, (φ b * eval x₀ (pderiv v q)) • e v := by
      rw [hsum, Ideal.toCotangent_eq]
      change a - _ ∈ _
      rw [hab]
      have hbm : b - algebraMap ℂ _ (φ b) ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
          RingHom.id_apply, sub_self]
      have hιq : ι q ∈ RingHom.ker φ := by simpa [hq0] using hI q
      have hTq := hT q
      rw [hq0, map_zero, sub_zero] at hTq
      have : ι q * b - ∑ v, (φ b * eval x₀ (pderiv v q)) • ι (X v - C (x₀ v)) =
          ι q * (b - algebraMap ℂ _ (φ b)) + φ b • (ι q -
            ∑ v, eval x₀ (pderiv v q) • ι (X v - C (x₀ v))) := by
        rw [smul_sub, Finset.smul_sum]
        simp only [smul_smul]
        rw [Algebra.smul_def (φ b) (ι q)]
        ring
      rw [this, pow_two]
      exact add_mem (Ideal.mul_mem_mul hιq hbm)
        (Submodule.smul_of_tower_mem _ _ (pow_two (RingHom.ker φ) ▸ hTq))
    rw [hx]
    exact Submodule.sum_mem _ fun v _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self v))
  -- the linear parts of the relations
  have hrel : ∀ j, ∑ v, eval x₀ (pderiv v (F j)) • e v = 0 := by
    intro j
    have hF0 : eval x₀ (F j) = 0 := by rw [← hev, hιF, map_zero]
    have := hT (F j)
    rw [hιF j, hF0, map_zero, sub_zero, zero_sub, neg_mem_iff] at this
    rw [hsum]
    exact (Ideal.toCotangent_eq_zero _ _).2 this
  set W := Submodule.span ℂ (Set.range fun i => e (Sum.inl i)) with hW
  have hinr : ∀ k, e (Sum.inr k) ∈ W := by
    intro k
    rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro ℓ
    let u : Fin c → ℂ := fun k => ℓ (Submodule.Quotient.mk (e (Sum.inr k)))
    set M := (eval x₀).mapMatrix (Matrix.of fun i j => pderiv (Sum.inr j) (F i))
    have hM : M.det ≠ 0 := by rwa [← RingHom.map_det]
    have hMu : M.mulVec u = 0 := by
      funext j
      have hz : ∀ i, W.mkQ (e (Sum.inl i)) = 0 := fun i =>
        (Submodule.Quotient.mk_eq_zero W).2 (Submodule.subset_span (Set.mem_range_self i))
      have := congrArg (ℓ ∘ₗ W.mkQ) (hrel j)
      rw [map_sum, map_zero, Fintype.sum_sum_type] at this
      simp only [LinearMap.map_smul_of_tower, LinearMap.comp_apply, hz, map_zero, smul_zero,
        Finset.sum_const_zero, zero_add, smul_eq_mul, Submodule.mkQ_apply] at this
      simpa [Matrix.mulVec, dotProduct, M, u] using this
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hM hMu) k
  refine eq_top_iff.2 (hall ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨v | k, rfl⟩
  · exact Submodule.subset_span (Set.mem_range_self v)
  · exact hinr k

/-- In `A = (ℂ[z, y]/(F))_h`, the image of a constant polynomial is the scalar. -/
private theorem algebraMap_mk_C (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ)
    (h : MvPolynomial (Fin d ⊕ Fin c) ℂ) (a : ℂ) :
    algebraMap _ (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))
      (Ideal.Quotient.mk (Ideal.span (Set.range F)) (C a)) = algebraMap ℂ _ a := by
  rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap,
    ← IsScalarTower.algebraMap_apply]

/-- In `A = (ℂ[z, y]/(F))_h`, the relations `Fⱼ` vanish. -/
private theorem algebraMap_mk_relation (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ)
    (h : MvPolynomial (Fin d ⊕ Fin c) ℂ) (j : Fin c) :
    algebraMap _ (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))
      (Ideal.Quotient.mk (Ideal.span (Set.range F)) (F j)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self j)), map_zero]

/-- In the standard presentation `A = (ℂ[z, y]/(F))_h`, at a point `φ` where `det(∂Fᵢ/∂yⱼ)` does
not vanish, the classes of the `zᵢ - zᵢ(p)` span the cotangent space `𝔪_p/𝔪_p²`. -/
private theorem span_toCotangent_eq_top
    (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ) (h : MvPolynomial (Fin d ⊕ Fin c) ℂ)
    (φ : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →ₐ[ℂ] ℂ)
    (hdet : MvPolynomial.eval
        (fun v => φ (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span (Set.range F))
          (MvPolynomial.X v))))
        (Matrix.of fun i j => MvPolynomial.pderiv (Sum.inr j) (F i)).det ≠ 0)
    (htm : ∀ i, algebraMap _ (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))
      (Ideal.Quotient.mk (Ideal.span (Set.range F)) (X (Sum.inl i) - C (φ (algebraMap _ _
        (Ideal.Quotient.mk (Ideal.span (Set.range F)) (X (Sum.inl i))))))) ∈ RingHom.ker φ) :
    Submodule.span ℂ (Set.range fun i => (RingHom.ker φ).toCotangent ⟨_, htm i⟩) = ⊤ := by
  let ι : MvPolynomial (Fin d ⊕ Fin c) ℂ →+* _ :=
    (algebraMap _ (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))).comp
      (Ideal.Quotient.mk (Ideal.span (Set.range F)))
  have hsurj : ∀ a, ∃ q b, IsUnit b ∧ a = ι q * b := by
    intro a
    obtain ⟨⟨y, r⟩, hyr⟩ := IsLocalization.mk'_surjective
      (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range F)) y
    refine ⟨q, IsLocalization.mk' _
      (1 : MvPolynomial (Fin d ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range F)) r,
      ?_, ?_⟩
    · exact IsUnit.of_mul_eq_one ((algebraMap _ _) (r : MvPolynomial (Fin d ⊕ Fin c) ℂ ⧸
        Ideal.span (Set.range F))) (by rw [IsLocalization.mk'_spec, map_one])
    · rw [← hyr]
      exact IsLocalization.mk'_eq_mul_mk'_one _ _
  exact span_toCotangent_eq_top_of_forall_eq_mul F ι (algebraMap_mk_C F h)
    (algebraMap_mk_relation F h) hsurj φ hdet htm

/-- A holomorphic germ whose value at the base point is nonzero is a unit. -/
private theorem isUnit_of_value_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} (x : holGerms p) (hx : Germ.value (x : Germ (𝓝 p) ℂ) ≠ 0) : IsUnit x := by
  obtain ⟨f, hfx, hf⟩ := x.2
  rw [← hfx, Germ.value_ofFun] at hx
  have hne : ∀ᶠ y in 𝓝 p, f y ≠ 0 :=
    (hf.self_of_nhds.continuousAt).eventually_ne hx
  refine IsUnit.of_mul_eq_one (b := ⟨(f⁻¹ : E → ℂ), coe_mem_holGerms ((hf.and hne).mono
    fun y hy => hy.1.inv hy.2)⟩) (Subtype.ext ?_)
  change (x : Germ (𝓝 p) ℂ) * ((f⁻¹ : E → ℂ) : Germ (𝓝 p) ℂ) = ((1 : E → ℂ) : Germ (𝓝 p) ℂ)
  rw [← hfx]
  exact Germ.coe_eq.2 (hne.mono fun y hy => by simp [hy])

/-- A localization map `S_M → P` lifted from `g : R → P` is injective as soon as every element of
the kernel of `g` is killed by an element of `M`. -/
private theorem injective_lift_of_forall_mul_eq_zero {R S P : Type*} [CommRing R] [CommRing S]
    [CommRing P] {M : Submonoid R} [Algebra R S] [IsLocalization M S] {g : R →+* P}
    (hg : ∀ y : M, IsUnit (g y)) (h : ∀ a, g a = 0 → ∃ m : M, (m : R) * a = 0) :
    Function.Injective (IsLocalization.lift (S := S) hg) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  rw [IsLocalization.lift_mk'_spec, mul_zero] at hx
  exact (IsLocalization.mk'_eq_zero_iff a s).2 (h a hx)

/-- **Holomorphic chart of a standard smooth presentation.** Let
`A = (ℂ[z, y]/(F₁, …, F_c))_h` be smooth over `ℂ`, and let `φ : A →ₐ[ℂ] ℂ` be a point at which
`det(∂Fᵢ/∂yⱼ)` does not vanish. Then near `p = (φ(z), φ(y))` the complex zero locus
`{F = 0, h ≠ 0}` is the image of a holomorphic inverse `g` of the projection to `z`, defined on
an open `V ∋ φ(z)`, and the ring homomorphism `A_{ker φ} → holGerms (φ(z))`, sending the class
of a polynomial `q` to the germ of `w ↦ q(g w)`, is injective. -/
@[mmp "lem_mmp_foundation_standard_smooth_holomorphic_chart"]
public theorem exists_holomorphic_chart_of_det_pderiv_ne_zero
    (F : Fin c → MvPolynomial (Fin d ⊕ Fin c) ℂ) (h : MvPolynomial (Fin d ⊕ Fin c) ℂ)
    [Algebra.Smooth ℂ (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h))]
    (φ : Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h) →ₐ[ℂ] ℂ)
    (hdet : MvPolynomial.eval
        (fun v => φ (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span (Set.range F))
          (MvPolynomial.X v))))
        (Matrix.of fun i j => MvPolynomial.pderiv (Sum.inr j) (F i)).det ≠ 0) :
    let Q := MvPolynomial (Fin d ⊕ Fin c) ℂ ⧸ Ideal.span (Set.range F)
    let A := Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
    let ι : MvPolynomial (Fin d ⊕ Fin c) ℂ →+* A :=
      (algebraMap Q A).comp (Ideal.Quotient.mk (Ideal.span (Set.range F)))
    let x₀ : Fin d ⊕ Fin c → ℂ := fun v => φ (ι (MvPolynomial.X v))
    let z₀ : Fin d → ℂ := fun i => x₀ (Sum.inl i)
    let Z : Set (Fin d ⊕ Fin c → ℂ) :=
      {x | (∀ i, MvPolynomial.eval x (F i) = 0) ∧ MvPolynomial.eval x h ≠ 0}
    ∃ (U : Set (Fin d ⊕ Fin c → ℂ)) (V : Set (Fin d → ℂ))
      (g : (Fin d → ℂ) → Fin d ⊕ Fin c → ℂ),
      U ∈ 𝓝 x₀ ∧ IsOpen V ∧ z₀ ∈ V ∧ DifferentiableOn ℂ g V ∧
      (∀ w ∈ V, g w ∈ Z ∩ U ∧ (fun i => g w (Sum.inl i)) = w) ∧
      (∀ x ∈ Z ∩ U, (fun i => x (Sum.inl i)) ∈ V ∧ g (fun i => x (Sum.inl i)) = x) ∧
      haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
      ∃ ψ : Localization.AtPrime (RingHom.ker φ) →+* holGerms z₀,
        (∀ q : MvPolynomial (Fin d ⊕ Fin c) ℂ,
          (ψ (algebraMap A _ (ι q)) : Germ (𝓝 z₀) ℂ) =
            ((fun w => MvPolynomial.eval (g w) q : (Fin d → ℂ) → ℂ) : Germ (𝓝 z₀) ℂ)) ∧
        Function.Injective ψ := by
  intro Q A ι x₀ z₀ Z
  have hev : ∀ q, eval x₀ q = φ (ι q) := by
    intro q
    have : (eval x₀) = (φ : A →+* ℂ).comp ι := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun v => ?_)
      · rw [RingHom.comp_apply, eval_C]
        change a = φ (algebraMap Q A (Ideal.Quotient.mk _ (C a)))
        rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap,
          ← IsScalarTower.algebraMap_apply, φ.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      · simp only [eval_X, RingHom.comp_apply]
        rfl
    exact congrArg (fun f : MvPolynomial (Fin d ⊕ Fin c) ℂ →+* ℂ => f q) this
  have hF : ∀ j, eval x₀ (F j) = 0 := fun j => by
    rw [hev]; exact (congrArg φ (algebraMap_mk_relation F h j)).trans (map_zero φ)
  have hh : eval x₀ h ≠ 0 := by
    rw [hev]
    exact ((IsLocalization.Away.algebraMap_isUnit (R := Q) (S := A)
      (Ideal.Quotient.mk _ h)).map φ).ne_zero
  obtain ⟨U, V, g, hU, hV, hz₀, hgd, hgV, hgZ⟩ := exists_chart F h x₀ hF hh hdet
  have hgz₀ : g z₀ = x₀ := (hgZ x₀ ⟨⟨hF, hh⟩, mem_of_mem_nhds hU⟩).2
  have hdiff : ∀ q : MvPolynomial (Fin d ⊕ Fin c) ℂ, ∀ᶠ w in 𝓝 z₀,
      DifferentiableAt ℂ (fun w => eval (g w) q) w :=
    fun q => Filter.eventually_of_mem (hV.mem_nhds hz₀) fun w hw =>
      (hasFDerivAt_eval q (g w)).differentiableAt.comp w (hgd.differentiableAt (hV.mem_nhds hw))
  let ρ : MvPolynomial (Fin d ⊕ Fin c) ℂ →+* holGerms z₀ :=
    ((Germ.coeRingHom (𝓝 z₀)).comp (RingHom.pi fun w => eval (g w))).codRestrict _
      fun q => coe_mem_holGerms (hdiff q)
  have hρ : ∀ q, (ρ q : Germ (𝓝 z₀) ℂ) = ((fun w => eval (g w) q : (Fin d → ℂ) → ℂ) :
      Germ (𝓝 z₀) ℂ) := fun q => rfl
  let ev : holGerms z₀ →+* ℂ := Germ.valueRingHom.comp (holGerms z₀).subtype
  have hevρ : ∀ q, ev (ρ q) = φ (ι q) := fun q => by
    change eval (g z₀) q = _
    rw [hgz₀, hev]
  have hρker : Ideal.span (Set.range F) ≤ RingHom.ker ρ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    refine Subtype.ext ((hρ _).trans (Germ.coe_eq.2
      (Filter.eventually_of_mem (hV.mem_nhds hz₀) fun w hw => ?_)))
    exact (hgV w hw).1.1.1 j
  let ρQ : Q →+* holGerms z₀ := Ideal.Quotient.lift _ ρ hρker
  have hρQh : IsUnit (ρQ (Ideal.Quotient.mk _ h)) := by
    refine isUnit_of_value_ne_zero _ ?_
    change ev (ρ h) ≠ 0
    rw [hevρ, ← hev]
    exact hh
  let ρA : A →+* holGerms z₀ := IsLocalization.Away.lift _ hρQh
  have hρAι : ∀ q, ρA (ι q) = ρ q := fun q => by
    change IsLocalization.Away.lift _ hρQh (algebraMap Q A (Ideal.Quotient.mk _ q)) = ρ q
    rw [IsLocalization.Away.lift_eq]
    exact Ideal.Quotient.lift_mk _ _ _
  have hevA : ∀ a, ev (ρA a) = φ a := by
    intro a
    have : ev.comp ρA = (φ : A →+* ℂ) := by
      refine IsLocalization.ringHom_ext (R := Q)
        (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) ?_
      refine Ideal.Quotient.ringHom_ext (RingHom.ext fun q => ?_)
      exact (congrArg ev (hρAι q)).trans (hevρ q)
    exact congrArg (fun f : A →+* ℂ => f a) this
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  let ψ : Localization.AtPrime (RingHom.ker φ) →+* holGerms z₀ :=
    IsLocalization.lift (M := (RingHom.ker φ).primeCompl) (g := ρA) fun s =>
      isUnit_of_value_ne_zero _ (by
        change ev (ρA s) ≠ 0
        rw [hevA]
        exact s.2)
  have hψ : ∀ q : MvPolynomial (Fin d ⊕ Fin c) ℂ,
      (ψ (algebraMap A _ (ι q)) : Germ (𝓝 z₀) ℂ) =
        ((fun w => MvPolynomial.eval (g w) q : (Fin d → ℂ) → ℂ) : Germ (𝓝 z₀) ℂ) := fun q => by
    simp only [ψ]
    rw [IsLocalization.lift_eq, hρAι, hρ]
  let t : Fin d → A := fun i => ι (X (Sum.inl i) - C (z₀ i))
  have hρt : ∀ i, (ρA (t i) : Germ (𝓝 z₀) ℂ) =
      ((fun w => w i - z₀ i : (Fin d → ℂ) → ℂ) : Germ (𝓝 z₀) ℂ) := by
    intro i
    rw [hρAι, hρ]
    exact Germ.coe_eq.2 (Filter.eventually_of_mem (hV.mem_nhds hz₀) fun w hw => by
      simp [congrFun (hgV w hw).2 i])
  have hρC : ∀ a : ℂ, (ρA (algebraMap ℂ A a) : Germ (𝓝 z₀) ℂ) =
      ((fun _ => a : (Fin d → ℂ) → ℂ) : Germ (𝓝 z₀) ℂ) := fun a => by
    rw [← algebraMap_mk_C F h a]
    change (ρA (ι (C a)) : Germ (𝓝 z₀) ℂ) = _
    rw [hρAι, hρ]
    exact Germ.coe_eq.2 (Eventually.of_forall fun w => by simp)
  have htm : ∀ i, t i ∈ RingHom.ker φ := fun i => by
    rw [RingHom.mem_ker, ← hevA]
    change Germ.value (ρA (t i) : Germ (𝓝 z₀) ℂ) = 0
    rw [hρt, Germ.value_ofFun, sub_self]
  exact ⟨U, V, g, hU, hV, hz₀, hgd, hgV, hgZ, ψ, hψ, injective_lift_of_forall_mul_eq_zero _
    (exists_mul_eq_zero_of_germ_eq_zero φ ρA hevA hρC t hρt htm
      (span_toCotangent_eq_top F h φ hdet htm))⟩

end StandardSmoothChart

/-! ### Avoidance charts on a smooth complex variety -/

section AvoidanceCharts

open CategoryTheory AlgebraicGeometry MMP.UnderlyingSpace

universe u

/-- On an affine open `V` of a locally Noetherian scheme, the trace of a closed subset `Z` is cut
out by finitely many sections over `V`. -/
private lemma exists_fin_forall_notMem_basicOpen_iff {X : Scheme.{u}} [IsLocallyNoetherian X]
    {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X} (hZ : IsClosed Z) :
    ∃ (r : ℕ) (g : Fin r → Γ(X, V)), ∀ y ∈ V, y ∈ Z ↔ ∀ i, y ∉ X.basicOpen (g i) := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1
    (hZ.preimage hV.fromSpec.continuous)
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨r, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)
  refine ⟨r, g, fun y hy => ?_⟩
  obtain ⟨q, rfl⟩ : y ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have h1 : hV.fromSpec q ∈ Z ↔ (I : Set Γ(X, V)) ⊆ (q : PrimeSpectrum Γ(X, V)).asIdeal :=
    (Set.ext_iff.1 hI q).trans (PrimeSpectrum.mem_zeroLocus _ _)
  refine h1.trans ?_
  rw [← hg, SetLike.coe_subset_coe, Submodule.span_le, Set.range_subset_iff]
  refine forall_congr' fun i => ?_
  have h2 : hV.fromSpec q ∈ X.basicOpen (g i) ↔ q ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen (g i) := Iff.rfl
  rw [h2, hV.fromSpec_preimage_basicOpen]
  exact (not_not.symm).trans (not_congr (PrimeSpectrum.mem_basicOpen _ _).symm)

/-- At a `ℂ`-point `q` lying over the affine open `V`, membership of its image in `Z` is the
common vanishing at `q` of sections `g i` cutting `Z` out of `V`. -/
private lemma mem_iff_forall_evalExt_eq_zero {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    {V : X.Opens} {Z : Set X} {r : ℕ} {g : Fin r → Γ(X, V)}
    (hg : ∀ y ∈ V, y ∈ Z ↔ ∀ i, y ∉ X.basicOpen (g i)) {q : UnderlyingSpace ℂ X}
    (hq : ⊤ ≤ q.toHom ⁻¹ᵁ V) :
    q.toHom (IsLocalRing.closedPoint ℂ) ∈ Z ↔ ∀ i, evalExt V (g i) q = 0 := by
  refine (hg _ ((top_le_preimage_iff _ _).1 hq)).trans (forall_congr' fun i => ?_)
  rw [evalExt_of_le _ hq, ← not_iff_not, not_not, ← top_le_preimage_iff,
    top_le_preimage_basicOpen_iff _ hq]

/-- **Avoidance charts on a smooth complex variety.** Let `X` be a smooth variety over `ℂ` and
`U` a dense open subset of `X`. Every `ℂ`-point `x` has an open neighbourhood `W` in the
complex realization and a homeomorphism `e` of `W` onto the ball of an analytic avoidance chart
`C` such that a point of `W` lies over `X \ U` if and only if its image under `e` lies in the
excluded subset of `C`. -/
@[mmp "lem_mmp_smooth_algebraic_avoidance_charts"]
public theorem exists_analyticAvoidanceChart_of_dense {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hX : MMP.Mori.IsVariety ℂ sX) [Smooth sX] (U : X.Opens) (hU : Dense (U : Set X))
    (x : ComplexPoints sX) :
    ∃ (W : Set (ComplexPoints sX)) (n : ℕ) (C : MMP.Fourfold.AnalyticAvoidanceChart n)
      (e : W ≃ₜ C.ball), IsOpen W ∧ x ∈ W ∧
      ∀ w : W, (w : ComplexPoints sX).toScheme ∉ U ↔ (e w : EuclideanSpace ℂ (Fin n)) ∈
        C.excludedSet := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := hX.toLocallyOfFiniteType
  haveI : QuasiCompact (X ↘ Spec (.of ℂ)) := hX.toQuasiCompact
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))
  let Hm : ComplexPoints sX ≃ₜ UnderlyingSpace ℂ X := ComplexPoints.homeomorphUnderlyingSpace
  have hpt : ∀ w : ComplexPoints sX,
      (Hm w).toHom (IsLocalRing.closedPoint ℂ) = w.toScheme := fun w =>
    congrArg w.hom (Subsingleton.elim _ _)
  have hp : Hm x ∈ regularPart ℂ X := by
    rw [mem_regularPart_iff, hpt]
    exact (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).1 ‹_› _
  obtain ⟨m, e, hpe, he, -⟩ := exists_isAlgebraicChart (Hm x) hp
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x.toScheme) (U := ⊤) trivial
  obtain ⟨r, g, hg⟩ :=
    exists_fin_forall_notMem_basicOpen_iff hV (Z := (U : Set X)ᶜ) U.isOpen.isClosed_compl
  set S := e.target ∩ e.symm ⁻¹' {q : UnderlyingSpace ℂ X | ⊤ ≤ q.toHom ⁻¹ᵁ V}
  have hSo : IsOpen S := e.isOpen_inter_preimage_symm (isOpen_setOf_le_preimage V)
  have hpS : e (Hm x) ∈ S := ⟨e.map_source hpe, by
    rw [Set.mem_preimage, e.left_inv hpe, Set.mem_setOf_eq, top_le_preimage_iff, hpt]
    exact hxV⟩
  obtain ⟨ε, hε, hεS⟩ := Metric.isOpen_iff.1 hSo _ hpS
  set B := Metric.ball (e (Hm x)) ε
  set O := e.source ∩ e ⁻¹' B
  have hOo : IsOpen O := e.isOpen_inter_preimage Metric.isOpen_ball
  have hOV : ∀ q ∈ O, ⊤ ≤ q.toHom ⁻¹ᵁ V := fun q hq => by
    have := (hεS hq.2).2
    rwa [Set.mem_preimage, e.left_inv hq.1] at this
  have hne : ∃ i, ∃ k ∈ B, evalExt V (g i) (e.symm k) ≠ 0 := by
    obtain ⟨q, hqO, -, hqU⟩ := (dense_regularPart_diff U.isOpen.isClosed_compl
      (Set.compl_ne_univ.2 hU.nonempty)).inter_open_nonempty O hOo
      ⟨Hm x, hpe, Metric.mem_ball_self hε⟩
    obtain ⟨i, hi⟩ := not_forall.1 ((mem_iff_forall_evalExt_eq_zero hg (hOV q hqO)).not.1 hqU)
    exact ⟨i, e q, hqO.2, by rwa [e.left_inv hqO.1]⟩
  let C : MMP.Fourfold.AnalyticAvoidanceChart m :=
    { center := e (Hm x)
      radius := ε
      r := r
      f := fun i k => evalExt V (g i) (e.symm k)
      analyticOnNhd := fun i => (Metric.isOpen_ball.analyticOn_iff_analyticOnNhd).1
        ((contDiffOn_omega_iff_analyticOn Metric.isOpen_ball.uniqueDiffOn).1
          ((he.contDiffOn_evalExt V (g i)).mono hεS))
      exists_ne_zero := hne }
  have hinv : ∀ k ∈ B, Hm.symm (e.symm k) ∈ Hm ⁻¹' O := fun k hk => by
    change Hm (Hm.symm _) ∈ O
    rw [Hm.apply_symm_apply]
    exact ⟨e.map_target (hεS hk).1, show e (e.symm k) ∈ B by rwa [e.right_inv (hεS hk).1]⟩
  let E : (Hm ⁻¹' O) ≃ₜ C.ball :=
    { toFun := fun w => ⟨e (Hm w), w.2.2⟩
      invFun := fun k => ⟨Hm.symm (e.symm k), hinv k k.2⟩
      left_inv := fun w => Subtype.ext (by
        change Hm.symm (e.symm (e (Hm w))) = w
        rw [e.left_inv w.2.1, Hm.symm_apply_apply])
      right_inv := fun k => Subtype.ext (by
        change e (Hm (Hm.symm (e.symm k))) = k
        rw [Hm.apply_symm_apply, e.right_inv (hεS k.2).1])
      continuous_toFun := (e.continuousOn.comp_continuous
        (Hm.continuous.comp continuous_subtype_val) fun w => w.2.1).subtype_mk _
      continuous_invFun :=
        ((Hm.symm.continuous.comp_continuousOn e.continuousOn_symm).comp_continuous
          continuous_subtype_val fun k => (hεS k.2).1).subtype_mk fun k => hinv k k.2 }
  refine ⟨Hm ⁻¹' O, m, C, E, hOo.preimage Hm.continuous, ⟨hpe, Metric.mem_ball_self hε⟩,
    fun w => ?_⟩
  change _ ↔ e (Hm w) ∈ B ∧ ∀ i, evalExt V (g i) (e.symm (e (Hm w))) = 0
  rw [e.left_inv w.2.1, ← hpt]
  exact (mem_iff_forall_evalExt_eq_zero hg (hOV _ w.2)).trans ⟨fun h => ⟨w.2.2, h⟩, And.right⟩

end AvoidanceCharts

/-! ### Fundamental groups of dense open subsets -/

section FundamentalGroup

open CategoryTheory AlgebraicGeometry unitInterval

/-- A path between points of the image of an embedding `f`, lying in that image, lifts along
`f`. -/
private theorem exists_path_map_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) {a b : X} (γ : Path (f a) (f b))
    (hγ : Set.range γ ⊆ Set.range f) : ∃ γ' : Path a b, γ'.map hf.continuous = γ := by
  let φ := hf.toHomeomorph
  have hφ : ∀ y, f (φ.symm y) = y := fun y => congrArg Subtype.val (φ.apply_symm_apply y)
  exact ⟨{ toFun := fun t => φ.symm ⟨γ t, hγ ⟨t, rfl⟩⟩
           continuous_toFun := φ.symm.continuous.comp (γ.continuous.subtype_mk _)
           source' := hf.injective (by rw [hφ]; exact γ.source)
           target' := hf.injective (by rw [hφ]; exact γ.target) },
    Path.ext <| funext fun _ => hφ _⟩

/-- Let `S` be a subset of a space `X`. Suppose every point has an open neighbourhood `W` in
which paths with common endpoints are homotopic, any two points of `W ∩ S` are joined inside
`W ∩ S`, and every point of `W` is joined, inside any of its open neighbourhoods, to a point of
`S`. Then every path between two points of `S` is homotopic to a path lying in `S`. -/
private theorem exists_path_range_subset_homotopic {X : Type*} [TopologicalSpace X] (S : Set X)
    (hG : ∀ x, ∃ W, IsOpen W ∧ x ∈ W ∧
      (∀ a b (p q : Path a b), Set.range p ⊆ W → Set.range q ⊆ W → p.Homotopic q) ∧
      (∀ a ∈ W ∩ S, ∀ b ∈ W ∩ S, JoinedIn (W ∩ S) a b) ∧
      ∀ y ∈ W, ∀ O, IsOpen O → y ∈ O → ∃ s ∈ S, JoinedIn O y s)
    {a b : X} (ha : a ∈ S) (hb : b ∈ S) (γ : Path a b) :
    ∃ ℓ : Path a b, Set.range ℓ ⊆ S ∧ ℓ.Homotopic γ := by
  choose W hWo hxW hW1 hW2 hW3 using hG
  have hL : ∀ x O, IsOpen O → x ∈ O → ∃ s ∈ S, JoinedIn O x s := fun x => hW3 x x (hxW x)
  obtain ⟨t, ht0, htm, ⟨n, htn⟩, hc⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (c := fun x => γ ⁻¹' W x) (fun x => (hWo x).preimage γ.continuous)
    (fun s _ => Set.mem_iUnion.2 ⟨γ s, hxW _⟩)
  choose i hi using hc
  have hmem : ∀ m, γ (t m) ∈ W (i m) := fun m =>
    hi m ⟨le_rfl, htm (Nat.le_succ m)⟩
  have hmem' : ∀ m, γ (t (m + 1)) ∈ W (i m) := fun m =>
    hi m ⟨htm (Nat.le_succ m), le_rfl⟩
  have hγ0 : γ 0 ∈ S := by rwa [γ.source]
  have key : ∀ m, ∃ s ∈ S, ∃ δ : Path (γ (t m)) s, Set.range δ ⊆ W (i m) ∧
      ∃ ℓ : Path (γ 0) s, Set.range ℓ ⊆ S ∧
        Path.Homotopic.Quotient.mk ((γ.subpath 0 (t m)).trans δ) =
          Path.Homotopic.Quotient.mk ℓ := by
    intro m
    induction m with
    | zero =>
      have aux : ∀ r : I, r = 0 → γ r ∈ W (i 0) → ∃ s ∈ S, ∃ δ : Path (γ r) s,
          Set.range δ ⊆ W (i 0) ∧ ∃ ℓ : Path (γ 0) s, Set.range ℓ ⊆ S ∧
          Path.Homotopic.Quotient.mk ((γ.subpath 0 r).trans δ) = Path.Homotopic.Quotient.mk ℓ := by
        rintro r rfl hr
        refine ⟨γ 0, hγ0, Path.refl _, by simpa using hr, Path.refl _, by simpa using hγ0, ?_⟩
        simp [Path.subpath_self, Path.Homotopic.Quotient.mk_trans]
      exact aux _ ht0 (hmem 0)
    | succ m ih =>
      obtain ⟨s, hs, δ, hδ, ℓ, hℓ, hq⟩ := ih
      obtain ⟨s', hs', hJ⟩ := hL _ _ ((hWo (i m)).inter (hWo (i (m + 1))))
        ⟨hmem' m, hmem (m + 1)⟩
      set δ' := hJ.somePath
      have hδ' : Set.range δ' ⊆ W (i m) ∩ W (i (m + 1)) := Set.range_subset_iff.2 hJ.somePath_mem
      let ρ := (δ.symm.trans (γ.subpath (t m) (t (m + 1)))).trans δ'
      have hρ : Set.range ρ ⊆ W (i m) := by
        simp only [ρ, Path.trans_range, Path.symm_range, Set.union_subset_iff]
        refine ⟨⟨hδ, ?_⟩, hδ'.trans Set.inter_subset_left⟩
        rw [Path.range_subpath_of_le _ _ _ (htm (Nat.le_succ m))]
        rintro _ ⟨τ, hτ, rfl⟩; exact hi m hτ
      have hsW : s ∈ W (i m) := by simpa using hδ ⟨1, rfl⟩
      have hs'W : s' ∈ W (i m) := by simpa using (hδ' ⟨1, rfl⟩).1
      have hJ2 := hW2 (i m) s ⟨hsW, hs⟩ s' ⟨hs'W, hs'⟩
      set α := hJ2.somePath
      have hα : Set.range α ⊆ W (i m) ∩ S := Set.range_subset_iff.2 hJ2.somePath_mem
      have hρα := hW1 (i m) _ _ ρ α hρ (hα.trans Set.inter_subset_left)
      refine ⟨s', hs', δ', hδ'.trans Set.inter_subset_right, ℓ.trans α, ?_, ?_⟩
      · rw [Path.trans_range]; exact Set.union_subset hℓ (hα.trans Set.inter_subset_right)
      · rw [Path.Homotopic.Quotient.mk_trans ℓ α, ← hq, ← Path.Homotopic.Quotient.eq.2 hρα,
          Path.Homotopic.Quotient.mk_trans _ δ', ← Path.Homotopic.Quotient.eq.2
          ⟨Path.Homotopy.subpathTransSubpath γ 0 (t m) (t (m + 1))⟩]
        simp only [ρ, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
          Path.Homotopic.Quotient.trans_assoc]
        simp [← Path.Homotopic.Quotient.trans_assoc]
  obtain ⟨s, hs, δ, hδ, ℓ, hℓ, hq⟩ := key n
  have fin : ∀ r : I, r = 1 → ∀ (ρ : Path (γ 0) (γ r)), Set.range ρ ⊆ S →
      Path.Homotopic.Quotient.mk (γ.subpath 0 r) = Path.Homotopic.Quotient.mk ρ →
      ∃ ℓ : Path a b, Set.range ℓ ⊆ S ∧ ℓ.Homotopic γ := by
    rintro r rfl ρ hρ hq
    refine ⟨ρ.cast γ.source.symm γ.target.symm, by simpa using hρ, ?_⟩
    have := Path.Homotopic.pathCast (Path.Homotopic.Quotient.eq.1 hq).symm γ.source.symm
      γ.target.symm
    rw [Path.subpath_zero_one] at this
    convert this using 1
    ext; simp
  have hbW : γ (t n) ∈ W (i n) ∩ S := ⟨hmem n, by rw [htn n le_rfl, γ.target]; exact hb⟩
  have hsW : s ∈ W (i n) := by simpa using hδ ⟨1, rfl⟩
  have hJ := hW2 (i n) _ hbW s ⟨hsW, hs⟩
  have hα : Set.range hJ.somePath ⊆ W (i n) ∩ S := Set.range_subset_iff.2 hJ.somePath_mem
  have hδα := hW1 (i n) _ _ δ hJ.somePath hδ (hα.trans Set.inter_subset_left)
  refine fin _ (htn n le_rfl) (ℓ.trans hJ.somePath.symm) ?_ ?_
  · rw [Path.trans_range, Path.symm_range]
    exact Set.union_subset hℓ (hα.trans Set.inter_subset_right)
  · rw [Path.Homotopic.Quotient.mk_trans, ← hq, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.eq.2 hδα, Path.Homotopic.Quotient.mk_symm]
    simp

/-- An open subset `W` homeomorphic to the ball of an analytic avoidance chart, with `W ∩ S`
corresponding to the complement of the excluded set: paths in `W` with common endpoints are
homotopic, `W ∩ S` is path connected, and every point of `W` is joined to a point of `S` inside
any of its open neighbourhoods. -/
private theorem avoidanceChart_path_props {X : Type*} [TopologicalSpace X] (S : Set X)
    {W : Set X} {n : ℕ}
    (C : MMP.Fourfold.AnalyticAvoidanceChart n) (e : W ≃ₜ C.ball)
    (hS : ∀ w : W, (w : X) ∈ S ↔ (e w : EuclideanSpace ℂ (Fin n)) ∉ C.excludedSet) :
    (∀ a b (p q : Path a b), Set.range p ⊆ W → Set.range q ⊆ W → p.Homotopic q) ∧
    (∀ a ∈ W ∩ S, ∀ b ∈ W ∩ S, JoinedIn (W ∩ S) a b) ∧
    (∀ x ∈ W, ∀ O, IsOpen O → x ∈ O → ∃ s ∈ S, JoinedIn O x s) := by
  set g : C.ball → X := fun y => (e.symm y : X)
  have hg : Continuous g := continuous_subtype_val.comp e.symm.continuous
  have hgS : ∀ y : C.ball, (y : EuclideanSpace ℂ (Fin n)) ∉ C.excludedSet → g y ∈ W ∩ S :=
    fun y hy => ⟨(e.symm y).2, (hS _).2 (by simpa using hy)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a b p q hp hq
    haveI : ContractibleSpace C.ball :=
      (convex_ball C.center C.radius).contractibleSpace C.ball_nonempty
    haveI : ContractibleSpace W := e.contractibleSpace
    haveI := SimplyConnectedSpace.ofContractible W
    have ha : a ∈ W := hp ⟨0, p.source⟩
    have hb : b ∈ W := hp ⟨1, p.target⟩
    obtain ⟨p', hp'⟩ := exists_path_map_eq (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) IsEmbedding.subtypeVal p
      (by rwa [Subtype.range_coe])
    obtain ⟨q', hq'⟩ := exists_path_map_eq (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) IsEmbedding.subtypeVal q
      (by rwa [Subtype.range_coe])
    rw [← hp', ← hq']
    exact (SimplyConnectedSpace.paths_homotopic p' q').map ⟨Subtype.val, continuous_subtype_val⟩
  · intro a ha b hb
    have hT : IsPathConnected (g '' (Subtype.val ⁻¹' (C.ball \ C.excludedSet))) :=
      ((MMP.Fourfold.AnalyticAvoidanceChart.isPathConnected_ball_diff_excludedSet C).preimage_coe
        Set.diff_subset).image hg
    have hmem : ∀ c ∈ W ∩ S, c ∈ g '' (Subtype.val ⁻¹' (C.ball \ C.excludedSet)) := by
      rintro c ⟨hcW, hcS⟩
      exact ⟨e ⟨c, hcW⟩, ⟨(e ⟨c, hcW⟩).2, (hS ⟨c, hcW⟩).1 hcS⟩, by simp [g]⟩
    refine (hT.joinedIn a (hmem a ha) b (hmem b hb)).mono ?_
    rintro _ ⟨y, hy, rfl⟩
    exact hgS y hy.2
  · intro x hx O hO hxO
    set y0 := e ⟨x, hx⟩
    obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.1 (hO.preimage hg)
    have hy0t : (y0 : EuclideanSpace ℂ (Fin n)) ∈ t := by
      have : y0 ∈ g ⁻¹' O := by simpa [g, y0] using hxO
      rwa [← hte] at this
    obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.1 (ht.inter C.isOpen_ball) _ ⟨hy0t, y0.2⟩
    have hcl : (y0 : EuclideanSpace ℂ (Fin n)) ∈ closure (C.ball \ C.excludedSet) :=
      MMP.Fourfold.AnalyticAvoidanceChart.ball_subset_closure_ball_diff_excludedSet C y0.2
    obtain ⟨z, hz, hdz⟩ := (@Metric.mem_closure_iff (EuclideanSpace ℂ (Fin n)) _ _ _).1 hcl ε hε
    have hsub : Metric.ball (y0 : EuclideanSpace ℂ (Fin n)) ε ⊆ C.ball :=
      fun w hw => (hεt hw).2
    have hF := ((convex_ball (y0 : EuclideanSpace ℂ (Fin n)) ε).isPathConnected
      ⟨_, Metric.mem_ball_self hε⟩).preimage_coe hsub
    have hzb : z ∈ Metric.ball (y0 : EuclideanSpace ℂ (Fin n)) ε := by
      rwa [Metric.mem_ball, dist_comm]
    have hJ := (hF.joinedIn y0 (Metric.mem_ball_self hε) ⟨z, hz.1⟩ hzb).map hg.continuousOn
    refine ⟨g ⟨z, hz.1⟩, (hgS ⟨z, hz.1⟩ hz.2).2, ?_⟩
    have hgy0 : g y0 = x := by simp [g, y0]
    rw [hgy0] at hJ
    refine hJ.mono ?_
    rintro _ ⟨w, hw, rfl⟩
    have : w ∈ Subtype.val ⁻¹' t := (hεt hw).1
    rwa [hte] at this

/-- The realization of the inclusion of an open subset `U` of a complex variety is an open
embedding, whose image is the set of `ℂ`-points lying over `U`. -/
public theorem isOpenEmbedding_realize_ι_and_range {V : Scheme.{0}} (sV : V ⟶ Spec (.of ℂ))
    (hV : MMP.Mori.IsVariety ℂ sV) (U : V.Opens) :
    IsOpenEmbedding (ComplexPoints.realize (sX := U.ι ≫ sV) (sY := sV) U.ι rfl) ∧
    Set.range (ComplexPoints.realize (sX := U.ι ≫ sV) U.ι rfl) = {x | x.toScheme ∈ U} := by
  have hinj : Function.Injective (ComplexPoints.realize (sX := U.ι ≫ sV) U.ι rfl) := by
    intro x y h
    ext1
    have := congrArg ComplexPoints.hom h
    simp only [ComplexPoints.realize_hom] at this
    exact (cancel_mono U.ι).1 this
  refine ⟨?_, ?_⟩
  · haveI := hV.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
    exact (ComplexPoints.isLocalHomeomorph_realize_of_etale U.ι rfl).isOpenEmbedding_of_injective
      hinj
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      change (x.hom ≫ U.ι) _ ∈ U
      rw [Scheme.Hom.comp_apply]
      exact (x.hom default).2
    · intro hy
      have hr : Set.range y.hom ⊆ Set.range U.ι := by
        rintro _ ⟨p, rfl⟩
        rw [Scheme.Opens.range_ι, Subsingleton.elim p default]
        exact hy
      refine ⟨⟨IsOpenImmersion.lift U.ι y.hom hr, ?_⟩, ?_⟩
      · rw [← Category.assoc, IsOpenImmersion.lift_fac, y.hom_comp_structure]
      · ext1; exact IsOpenImmersion.lift_fac _ _ _

/-- **Fundamental groups of dense opens surject.** Let `V` be a connected smooth variety over
`ℂ`, `U` a dense open subset and `u` a `ℂ`-point of `U`. Then the map of topological fundamental
groups of complex realizations induced by the inclusion `U ⊆ V` is surjective. -/
@[mmp "thm_mmp_dense_open_pi1_surjective"]
public theorem surjective_fundamentalGroupMap_realize_ι_of_dense {V : Scheme.{0}}
    (sV : V ⟶ Spec (.of ℂ)) (hV : MMP.Mori.IsVariety ℂ sV) [Smooth sV] [ConnectedSpace V]
    (U : V.Opens) (hU : Dense (U : Set V)) (u : ComplexPoints (U.ι ≫ sV)) :
    Function.Surjective
      (FundamentalGroup.map
        ⟨ComplexPoints.realize U.ι rfl, ComplexPoints.continuous_realize U.ι rfl⟩ u) := by
  obtain ⟨hemb, hrange⟩ := isOpenEmbedding_realize_ι_and_range sV hV U
  set S : Set (ComplexPoints sV) := {x | x.toScheme ∈ U}
  have hchart : ∀ x : ComplexPoints sV, ∃ W, IsOpen W ∧ x ∈ W ∧
      (∀ a b (p q : Path a b), Set.range p ⊆ W → Set.range q ⊆ W → p.Homotopic q) ∧
      (∀ a ∈ W ∩ S, ∀ b ∈ W ∩ S, JoinedIn (W ∩ S) a b) ∧
      ∀ y ∈ W, ∀ O, IsOpen O → y ∈ O → ∃ s ∈ S, JoinedIn O y s := fun x => by
    obtain ⟨W, n, C, e, hWo, hxW, hiff⟩ :=
      MMP.Analytic.exists_analyticAvoidanceChart_of_dense sV hV U hU x
    exact ⟨W, hWo, hxW, avoidanceChart_path_props S C e fun w => (not_iff_comm.1 (hiff w)).symm⟩
  intro g
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  have hu : ComplexPoints.realize U.ι rfl u ∈ S := hrange ▸ ⟨u, rfl⟩
  obtain ⟨ℓ, hℓS, hℓγ⟩ := exists_path_range_subset_homotopic S hchart hu hu γ
  obtain ⟨ℓ', hℓ'⟩ := exists_path_map_eq hemb.isEmbedding ℓ (hrange ▸ hℓS)
  refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk ℓ'), ?_⟩
  change FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (ℓ'.map _)) = g
  rw [hℓ', (Path.Homotopic.Quotient.eq.2 hℓγ).trans hγ]

end FundamentalGroup

end MMP.Analytic

/-! ### Finiteness of the branch excess -/

namespace MMP.Fourfold

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-- The normalization of a prime divisor of a scheme locally of finite type over a field has
finite fibres. -/
private lemma finite_preimage_singleton_primeDivisorNormalization {k : Type} [Field k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (S : MMP.Mori.PrimeDivisor Y) (y : Y) :
    (primeDivisorNormalization S ⁻¹' {y}).Finite := by
  haveI := S.integral
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    Scheme.isFinite_normalization
      (isNagataScheme_of_locallyOfFiniteType_over_field k (S.idealSheaf.subschemeι ≫ sY))
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  exact (primeDivisorNormalization S).finite_preimage_singleton y

/-- Over a scheme locally of finite type over a field, only finitely many prime divisors of the
normalizations `S^ν` (`S ∈ Q`) map onto a given irreducible closed subset `V`: their generic
points all lie in the fibres over the generic point of `V`, which are finite. -/
private lemma finite_branches {k : Type} [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] (Q : Finset (MMP.Mori.PrimeDivisor Y)) (V : IrreducibleCloseds Y) :
    {P : (S : Q) × MMP.Mori.PrimeDivisor
        (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor Y)) |
      primeDivisorNormalization (P.1 : MMP.Mori.PrimeDivisor Y) '' P.2.support = V}.Finite := by
  obtain ⟨η, hη⟩ := QuasiSober.sober V.isIrreducible V.isClosed
  refine (Set.finite_iUnion fun S : Q =>
    (((finite_preimage_singleton_primeDivisorNormalization sY S.1 η).preimage
      PrimeDivisor.genericPoint_injective.injOn).image (Sigma.mk S))).subset ?_
  rintro ⟨S, P⟩ hSP
  have := (isGenericPoint_closure (x := P.genericPoint)).image
    (primeDivisorNormalization (S : MMP.Mori.PrimeDivisor Y)).continuous
  rw [← PrimeDivisor.support_eq_closure, hSP, V.isClosed.closure_eq] at this
  exact Set.mem_iUnion.2 ⟨S, P, this.eq hη, rfl⟩

/-- On an integral scheme locally of finite type over a field, an irreducible closed subset has
dimension plus codimension equal to the dimension of the scheme. -/
private lemma topologicalKrullDim_add_codimension {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (V : IrreducibleCloseds Y) :
    topologicalKrullDim (V : Set Y) + codimension V = topologicalKrullDim Y := by
  obtain ⟨η, hη⟩ := QuasiSober.sober V.isIrreducible V.isClosed
  obtain rfl : IrreducibleCloseds.closureSingleton η = V := SetLike.coe_injective hη
  rw [MMP.Flips.codimension_closureSingleton]
  exact MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY η

/-- **Finiteness of the branch excess.** Let `Y` be a normal complex fourfold and `Q` a finite
set of prime divisors of `Y`. Every irreducible surface `V ⊆ ⋃_{S ∈ Q} S` has branch count
`1 ≤ boundaryBranchCount Q V`, and only finitely many of them have branch count `> 1`. -/
@[mmp "thm_oai4_branch_b"]
public theorem one_le_boundaryBranchCount_and_finite_setOf_one_lt {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) (hY : MMP.Mori.IsNormalVariety ℂ sY)
    (hdim : topologicalKrullDim Y = 4) (Q : Finset (MMP.Mori.PrimeDivisor Y)) :
    (∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 2 →
        (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) → 1 ≤ boundaryBranchCount Q V) ∧
      {V : IrreducibleCloseds Y | topologicalKrullDim (V : Set Y) = 2 ∧
        (V : Set Y) ⊆ ⋃ S ∈ Q, (S.support : Set Y) ∧ 1 < boundaryBranchCount Q V}.Finite := by
  haveI : IsVariety ℂ sY := hY.1
  refine ⟨fun V hV hVQ => ?_, (finite_setOf_nontrivial_normalizationBranches sY Q).subset
    fun V ⟨_, _, h1⟩ => (Set.one_lt_ncard (finite_branches sY Q V)).1 h1⟩
  have hcod : codimension V = 2 := by
    have h := topologicalKrullDim_add_codimension sY V
    rw [hV, hdim] at h
    exact WithTop.add_left_cancel (by decide)
      (WithBot.coe_injective (by push_cast; exact h) : (2 + codimension V : ℕ∞) = 2 + 2)
  obtain ⟨i, P, hP⟩ := exists_primeDivisor_image_primeDivisorNormalization_eq sY
    (fun S : Q => S.1) V hcod (by simpa [Set.iUnion_subtype] using hVQ)
  exact (Set.ncard_pos (finite_branches sY Q V)).2 ⟨⟨i, P⟩, hP⟩

end MMP.Fourfold

end
