module

public import MMP.Geometry.Manifold.Corners.BoundaryRate
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Geometry.Manifold.Sheaf.Basic

/-!
# A smoothed distance to the boundary of an embedded manifold with corners

Let `e : M → F` be a `C²` embedding, with injective derivative, of a compact manifold with
corners modelled on the quadrant into a Euclidean space, and let `B = e(∂M)`. The distance
`d_B` to `B` is not smooth, but its mollification `ρ̃ = φ_ε ⋆ d_B` is `C²`, and `|ρ̃ - d_B| ≤ ε`.
We show that `ρ̃ ∘ e` has nonzero derivative at every point `p` with `κ ≤ d_B (e p) ≤ D₀`, for
a fixed `D₀ > 0` and all `ε` small compared with `κ`.

In a chart `u` around a boundary point, with `g = e ∘ u⁻¹`, let `z` be a point near `e(M)` and
`b = g u_b` a nearest point of `B` to `z`. The first-order conditions for `b` on the faces
through `u_b`, together with the fact that the nearest point of `e(M)` to `z` is `g u_z` with
`u_z` in the open quadrant, force `u_b` to lie on a single face `{u_i = 0}` and give
`⟪z - b, Dg(u_b) 𝟙⟫ > c ‖z - b‖`, where `𝟙 = (1, …, 1)`. So `d_B` increases at a definite rate
along `Dg 𝟙`, and so does its mollification.

## Main results

* `MMP.Topology.exists_contDiff_abs_sub_le_of_lipschitzWith`
* `MMP.Topology.exists_rate_infDist_boundary`
* `MMP.Topology.exists_regular_smoothing_infDist_boundary`
-/

open Set Filter Topology Metric Function
open scoped Manifold ContDiff Convolution

namespace MMP.Topology

public section

section Mollify

variable {N : ℕ}

/-- **Mollifying a `1`-Lipschitz function.** For `ε > 0` there is a `C²` function `ρ` with
`|ρ - f| ≤ ε` whose derivative at `x` in a direction `w` is at least `c` as soon as `f`
increases at rate `c` along `w` on the ball of radius `ε` around `x`. -/
theorem exists_contDiff_abs_sub_le_of_lipschitzWith {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : LipschitzWith 1 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ 2 ρ ∧ (∀ y, |ρ y - f y| ≤ ε) ∧
      ∀ x w (c s₀ : ℝ), 0 < s₀ →
        (∀ y ∈ ball x ε, ∀ s ∈ Ioc 0 s₀, f y + c * s ≤ f (y + s • w)) →
        c ≤ fderiv ℝ ρ x w := by
  set φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin N)) :=
    ⟨ε / 2, ε, by positivity, by linarith⟩
  set ψ := φ.normed MeasureTheory.volume with hψ
  set ρ := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] f with hρ
  have hfc : Continuous f := hf.continuous
  have hψc : Continuous ψ := φ.continuous_normed
  have hρc : ContDiff ℝ 2 ρ :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hfc.locallyIntegrable
  have hρe : ∀ z, ρ z = ∫ t, ψ t * f (z - t) := fun z ↦ by
    rw [hρ, MeasureTheory.convolution_lsmul]; rfl
  have hint : ∀ z, MeasureTheory.Integrable (fun t ↦ ψ t * f (z - t)) := fun z ↦
    (hψc.mul (hfc.comp (continuous_const.sub continuous_id))
      ).integrable_of_hasCompactSupport (φ.hasCompactSupport_normed.mul_right)
  refine ⟨ρ, hρc, fun y ↦ ?_, fun x w c s₀ hs₀ hmono ↦ ?_⟩
  · have := φ.dist_normed_convolution_le (μ := MeasureTheory.volume) (x₀ := y) (g := f)
      hfc.aestronglyMeasurable fun z hz ↦ by
        have h := hf.dist_le_mul z y
        simp only [NNReal.coe_one, one_mul] at h
        exact h.trans (mem_ball.1 hz).le
    rwa [Real.dist_eq] at this
  · -- the increments of `ρ` along `w`
    have hinc : ∀ s ∈ Ioc 0 s₀, c * s ≤ ρ (x + s • w) - ρ x := by
      intro s hs
      rw [hρe, hρe, ← MeasureTheory.integral_sub (hint _) (hint _)]
      have h1 : ∫ t, ψ t * (c * s) = c * s := by
        rw [MeasureTheory.integral_mul_const, φ.integral_normed, one_mul]
      rw [← h1]
      refine MeasureTheory.integral_mono ((hψc.mul
        continuous_const).integrable_of_hasCompactSupport
        φ.hasCompactSupport_normed.mul_right) ((hint _).sub (hint _)) fun t ↦ ?_
      simp only
      rw [← mul_sub]
      by_cases ht : ψ t = 0
      · rw [ht, zero_mul, zero_mul]
      · have htb : t ∈ ball (0 : EuclideanSpace ℝ (Fin N)) ε := by
          have : t ∈ Function.support ψ := ht
          rwa [hψ, φ.support_normed_eq] at this
        have hy : x - t ∈ ball x ε := by
          rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]
          simpa using htb
        have h := hmono (x - t) hy s hs
        rw [show x - t + s • w = x + s • w - t by abel] at h
        exact mul_le_mul_of_nonneg_left (by linarith) (φ.nonneg_normed t)
    -- the derivative along the line
    have hd : HasDerivAt (fun s : ℝ ↦ ρ (x + s • w)) (fderiv ℝ ρ x w) 0 := by
      have h1 : HasDerivAt (fun s : ℝ ↦ x + s • w) w 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
      have h2 : HasFDerivAt ρ (fderiv ℝ ρ x) (x + (0 : ℝ) • w) := by
        rw [zero_smul, add_zero]
        exact (hρc.differentiable (by norm_num) x).hasFDerivAt
      exact h2.comp_hasDerivAt (0 : ℝ) h1
    refine ge_of_tendsto hd.tendsto_slope_zero_right ?_
    filter_upwards [Ioc_mem_nhdsGT hs₀] with s hs
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [le_inv_mul_iff₀ hs.1]
    linarith [hinc s hs]

end Mollify

variable {n N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
  [IsManifold (modelWithCornersEuclideanQuadrant n) 2 M]

/-- The rate estimate near one boundary point `q₀`, in the chart at `q₀`. -/
theorem exists_local_rate_infDist_boundary [CompactSpace M]
    {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 e)
    (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective
      (mfderiv (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e x))
    {q₀ : M} (hq₀ : q₀ ∈ (modelWithCornersEuclideanQuadrant n).boundary M) :
    ∃ ρ₀ > 0, ∃ c > 0, ∀ p, dist (e p) (e q₀) < ρ₀ →
      p ∈ (chartAt (EuclideanQuadrant n) q₀).source ∧
      (p ∉ (modelWithCornersEuclideanQuadrant n).boundary M →
        extChartAt (modelWithCornersEuclideanQuadrant n) q₀ p ∈
          interior (range (modelWithCornersEuclideanQuadrant n))) ∧
      Injective (fderivWithin ℝ
          (e ∘ (extChartAt (modelWithCornersEuclideanQuadrant n) q₀).symm)
          (range (modelWithCornersEuclideanQuadrant n))
          (extChartAt (modelWithCornersEuclideanQuadrant n) q₀ p)) ∧
      ∀ z, dist z (e q₀) < ρ₀ →
        infDist z (range e) ≤
          infDist z (e '' (modelWithCornersEuclideanQuadrant n).boundary M) / 2 →
        ∀ b ∈ e '' (modelWithCornersEuclideanQuadrant n).boundary M,
          dist z b = infDist z (e '' (modelWithCornersEuclideanQuadrant n).boundary M) →
          c * ‖z - b‖ ≤ inner ℝ (z - b) (fderivWithin ℝ
            (e ∘ (extChartAt (modelWithCornersEuclideanQuadrant n) q₀).symm)
            (range (modelWithCornersEuclideanQuadrant n))
            (extChartAt (modelWithCornersEuclideanQuadrant n) q₀ p) (quadrantDiagonal n)) := by
  set I := modelWithCornersEuclideanQuadrant n with hI
  set B := e '' I.boundary M with hB
  set φ := extChartAt I q₀ with hφ
  set g := e ∘ φ.symm with hgdef
  set u₀ := φ q₀ with hu₀
  have hrange : range I = {y | ∀ i : Fin n, 0 ≤ y i} := range_euclideanQuadrant n
  have hu₀r : u₀ ∈ range I := extChartAt_target_subset_range q₀ (mem_extChartAt_target q₀)
  have hgc : ContDiffWithinAt ℝ 2 g (range I) u₀ := by
    have := (contMDiffAt_iff.1 (he q₀)).2
    rwa [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at this
  have hmd : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e q₀ :=
    (he q₀).mdifferentiableAt (by norm_num)
  have hinj' : Function.Injective (fderivWithin ℝ g (range I) u₀) := by
    have h := hinj q₀
    rw [hmd.mfderiv, writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp] at h
    intro a b hab
    exact h hab
  obtain ⟨r₀, hr₀, L, hL, m, hm, Λ, hΛ, hgS₀, hDL₀, hDm₀, hDΛ₀⟩ :=
    exists_bounds_of_contDiffWithinAt I.convex_range I.uniqueDiffOn hu₀r hgc hinj'
  obtain ⟨rt, hrt, hrtT⟩ := Metric.mem_nhdsWithin_iff.1
    (extChartAt_target_mem_nhdsWithin (I := I) q₀)
  set δ1 := ‖quadrantDiagonal n‖ with hδ1
  set R := min (min r₀ rt) (min (m / (16 * L)) (min (1 / (2 * L))
    (m ^ 2 / (32 * (Λ + 1) * L * (δ1 + 1))))) with hR
  have hR0 : 0 < R := lt_min (lt_min hr₀ hrt) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have hRr₀ : R ≤ r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hRrt : R ≤ rt := (min_le_left _ _).trans (min_le_right _ _)
  have hR1 : R ≤ m / (16 * L) := (min_le_right _ _).trans (min_le_left _ _)
  have hR2 : R ≤ 1 / (2 * L) := (min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _))
  have hR3 : R ≤ m ^ 2 / (32 * (Λ + 1) * L * (δ1 + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set S := {u : EuclideanSpace ℝ (Fin n) | ∀ i, 0 ≤ u i} ∩ ball u₀ R with hS
  have hSsub : S ⊆ range I ∩ ball u₀ r₀ := fun u hu ↦
    ⟨by rw [hrange]; exact hu.1, ball_subset_ball hRr₀ hu.2⟩
  have hStarget : S ⊆ φ.target := fun u hu ↦
    hrtT ⟨ball_subset_ball hRrt hu.2, by rw [hrange]; exact hu.1⟩
  -- the chart region and its image
  set O := φ.source ∩ φ ⁻¹' ball u₀ R with hO
  have hOn : O ∈ 𝓝 q₀ := inter_mem (extChartAt_source_mem_nhds q₀)
    ((continuousAt_extChartAt q₀).preimage_mem_nhds (ball_mem_nhds _ hR0))
  rw [hemb.isInducing.nhds_eq_comap] at hOn
  obtain ⟨V, hV, hVO⟩ := mem_comap.1 hOn
  obtain ⟨ρ₁, hρ₁, hρ₁V⟩ := Metric.mem_nhds_iff.1 hV
  have hball : ∀ p, dist (e p) (e q₀) < ρ₁ → p ∈ O := fun p hp ↦ hVO (hρ₁V hp)
  have hmemS : ∀ p ∈ O, φ p ∈ S := fun p hp ↦
    ⟨by rw [← hrange]; exact extChartAt_target_subset_range q₀ (φ.map_source hp.1), hp.2⟩
  have hgφ : ∀ p ∈ O, g (φ p) = e p := fun p hp ↦ by
    simp only [hgdef, comp_apply, φ.left_inv hp.1]
  have hsrc : ∀ p ∈ O, p ∈ (chartAt (EuclideanQuadrant n) q₀).source := fun p hp ↦ by
    have := hp.1; rwa [hφ, extChartAt_source] at this
  have hbd : ∀ p ∈ O, (p ∈ I.boundary M ↔ ∃ i, φ p i = 0) := fun p hp ↦
    isBoundaryPoint_iff_exists_extend_eq_zero_of_mem_atlas (k := 2) (by norm_num)
      (chart_mem_atlas _ q₀) (hsrc p hp)
  -- the constants
  refine ⟨min (ρ₁ / 2) (m ^ 2 / (8 * L)), lt_min (by positivity) (by positivity),
    m ^ 2 / (8 * (Λ + 1)), by positivity, fun p hp ↦ ?_⟩
  have hpO := hball p (hp.trans_le ((min_le_left _ _).trans (half_le_self hρ₁.le)))
  have hpS := hmemS p hpO
  refine ⟨hsrc p hpO, fun hpB ↦ ?_, fun h₁ h₂ hh ↦ ?_, fun z hz hzA b hb hzb ↦ ?_⟩
  · rw [interior_range_modelWithCornersEuclideanQuadrant]
    intro i
    refine lt_of_le_of_ne (hpS.1 i) fun h0 ↦ hpB ((hbd p hpO).2 ⟨i, h0.symm⟩)
  · have h0 : fderivWithin ℝ g (range I) (φ p) (h₁ - h₂) = 0 := by rw [map_sub, hh, sub_self]
    have := hDm₀ (φ p) (hSsub hpS) (h₁ - h₂)
    rw [h0, norm_zero] at this
    have : ‖h₁ - h₂‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (h₁ - h₂)]) (norm_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · rcases (norm_nonneg (z - b)).eq_or_lt with h0 | hpos
    · have hzb0 : z - b = 0 := norm_eq_zero.1 h0.symm
      rw [← h0, mul_zero, hzb0, inner_zero_left]
    have hz' : dist z (e q₀) < ρ₁ / 2 := hz.trans_le (min_le_left _ _)
    have hzL : dist z (e q₀) < m ^ 2 / (8 * L) := hz.trans_le (min_le_right _ _)
    have hq₀B : e q₀ ∈ B := ⟨q₀, hq₀, rfl⟩
    have hzbq : ‖z - b‖ ≤ dist z (e q₀) := by
      rw [← dist_eq_norm, hzb]; exact infDist_le_dist_of_mem hq₀B
    -- the nearest point of `e(M)`
    obtain ⟨_, ⟨pz, rfl⟩, hpz⟩ := (isCompact_range hemb.continuous).exists_infDist_eq_dist
      ⟨e q₀, mem_range_self _⟩ z
    have hpzO : pz ∈ O := hball pz (by
      have := infDist_le_dist_of_mem (mem_range_self (f := e) q₀) (x := z)
      have := dist_triangle (e pz) z (e q₀)
      rw [dist_comm (e pz) z, ← hpz] at this
      linarith)
    obtain ⟨q, hq, rfl⟩ := hb
    have hqO : q ∈ O := hball q (by
      have := dist_triangle (e q) z (e q₀)
      have h1 : dist z (e q) ≤ dist z (e q₀) := by rwa [dist_eq_norm]
      rw [dist_comm (e q) z] at this
      linarith)
    have hzbpos : 0 < infDist z B := by rwa [← hzb, dist_eq_norm]
    have hpzB : pz ∉ I.boundary M := fun h ↦ by
      have := infDist_le_dist_of_mem (show e pz ∈ B from ⟨pz, h, rfl⟩) (x := z)
      rw [← hpz] at this
      linarith
    obtain ⟨i₀, hi₀⟩ := (hbd q hqO).1 hq
    have key := inner_sub_ge_of_isMinOn_boundary (g := g)
      (D := fderivWithin ℝ g (range I)) hS
      (fun w hw ↦ (hgS₀ w (hSsub hw)).mono hSsub) hm hL hΛ
      (fun u hu v hv ↦ hDL₀ u (hSsub hu) v (hSsub hv))
      (fun u hu h ↦ hDm₀ u (hSsub hu) h) (fun u hu ↦ hDΛ₀ u (hSsub hu)) (r := 2 * R)
      (fun u hu v hv ↦ by
        rw [← dist_eq_norm]
        have := dist_triangle v u₀ u
        rw [dist_comm u₀ u] at this
        have h1 := mem_ball.1 hu.2
        have h2 := mem_ball.1 hv.2
        linarith)
      (by rw [le_div_iff₀ (by positivity)] at hR1; nlinarith)
      (by rw [le_div_iff₀ (by positivity)] at hR2; nlinarith)
      (by
        rw [le_div_iff₀ (by positivity)] at hR3
        have h1 : 0 ≤ (Λ + 1) * R * L := by positivity
        nlinarith [norm_nonneg (quadrantDiagonal n)])
      (z := z) (hmemS pz hpzO)
      (fun i ↦ lt_of_le_of_ne ((hmemS pz hpzO).1 i)
        fun h0 ↦ hpzB ((hbd pz hpzO).2 ⟨i, h0.symm⟩))
      (fun w hw ↦ by
        rw [hgφ pz hpzO, ← dist_eq_norm, ← dist_eq_norm, ← hpz]
        exact infDist_le_dist_of_mem (mem_range_self _))
      (hmemS q hqO) hi₀
      (fun w hw ⟨i, hwi⟩ ↦ by
        rw [hgφ q hqO, ← dist_eq_norm, ← dist_eq_norm, hzb]
        have hwt := hStarget hw
        have hsO : φ.symm w ∈ O := ⟨φ.map_target hwt, by
          change φ (φ.symm w) ∈ ball u₀ R
          rw [φ.right_inv hwt]
          exact hw.2⟩
        have : φ.symm w ∈ I.boundary M :=
          (hbd _ hsO).2 ⟨i, by rw [φ.right_inv hwt]; exact hwi⟩
        exact infDist_le_dist_of_mem ⟨φ.symm w, this, rfl⟩)
      (by
        rw [hgφ pz hpzO, hgφ q hqO, ← dist_eq_norm, ← dist_eq_norm, ← hpz, hzb]
        exact hzA)
      (by
        rw [hgφ pz hpzO, ← dist_eq_norm, ← hpz]
        have h1 : infDist z B ≤ dist z (e q₀) := infDist_le_dist_of_mem hq₀B
        have h3 := (lt_div_iff₀ (by positivity)).1 hzL
        have h4 : infDist z (range e) ≤ dist z (e q₀) / 2 := by linarith
        have e1 := mul_le_mul_of_nonneg_right h4 hL.le
        nlinarith)
      (φ p) hpS
    rwa [hgφ q hqO] at key

/-- **The distance to the boundary grows along the diagonal.** There are `D₀, c, lam > 0` such
that each point `p` with `0 < d_B (e p) ≤ D₀` is interior in some chart `u`, and for every `z`
within `lam` of `e p` that is at most half as far from `e(M)` as from `B = e(∂M)`, and every
nearest point `b` of `B` to `z`, `⟪z - b, Dg 𝟙⟫ ≥ c ‖z - b‖`, with `g = e ∘ u⁻¹` and its
derivative `Dg` taken at `u p`, which is injective. -/
theorem exists_rate_infDist_boundary [CompactSpace M]
    {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 e)
    (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective
      (mfderiv (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e x)) :
    ∃ D₀ > 0, ∃ c > 0, ∃ lam > 0, ∀ p,
      0 < infDist (e p) (e '' (modelWithCornersEuclideanQuadrant n).boundary M) →
      infDist (e p) (e '' (modelWithCornersEuclideanQuadrant n).boundary M) ≤ D₀ →
      ∃ x₀, p ∈ (chartAt (EuclideanQuadrant n) x₀).source ∧
        extChartAt (modelWithCornersEuclideanQuadrant n) x₀ p ∈
          interior (range (modelWithCornersEuclideanQuadrant n)) ∧
        Injective (fderivWithin ℝ
          (e ∘ (extChartAt (modelWithCornersEuclideanQuadrant n) x₀).symm)
          (range (modelWithCornersEuclideanQuadrant n))
          (extChartAt (modelWithCornersEuclideanQuadrant n) x₀ p)) ∧
        ∀ z, dist z (e p) < lam →
          infDist z (range e) ≤
            infDist z (e '' (modelWithCornersEuclideanQuadrant n).boundary M) / 2 →
          ∀ b ∈ e '' (modelWithCornersEuclideanQuadrant n).boundary M,
            dist z b = infDist z (e '' (modelWithCornersEuclideanQuadrant n).boundary M) →
            c * ‖z - b‖ ≤ inner ℝ (z - b) (fderivWithin ℝ
              (e ∘ (extChartAt (modelWithCornersEuclideanQuadrant n) x₀).symm)
              (range (modelWithCornersEuclideanQuadrant n))
              (extChartAt (modelWithCornersEuclideanQuadrant n) x₀ p) (quadrantDiagonal n)) := by
  set I := modelWithCornersEuclideanQuadrant n with hI
  set B := e '' I.boundary M with hB
  have hBcl : IsClosed (I.boundary M) :=
    ModelWithCorners.isClosed_boundary (I := I) (M := M) (n := 2) (by simp)
  have hB'c : IsCompact B := hBcl.isCompact.image hemb.continuous
  have hloc : ∀ q : I.boundary M, ∃ ρ₀ > 0, ∃ c > 0, ∀ p, dist (e p) (e q) < ρ₀ →
      p ∈ (chartAt (EuclideanQuadrant n) (q : M)).source ∧
      (p ∉ I.boundary M → extChartAt I (q : M) p ∈ interior (range I)) ∧
      Injective (fderivWithin ℝ (e ∘ (extChartAt I (q : M)).symm) (range I)
        (extChartAt I (q : M) p)) ∧
      ∀ z, dist z (e q) < ρ₀ → infDist z (range e) ≤ infDist z B / 2 →
        ∀ b ∈ B, dist z b = infDist z B →
          c * ‖z - b‖ ≤ inner ℝ (z - b) (fderivWithin ℝ (e ∘ (extChartAt I (q : M)).symm)
            (range I) (extChartAt I (q : M) p) (quadrantDiagonal n)) := fun q ↦
    exists_local_rate_infDist_boundary he hemb hinj q.2
  choose ρ₀ hρ₀ c hc hpt using hloc
  obtain ⟨t, ht⟩ := hBcl.isCompact.elim_finite_subcover
    (fun q : I.boundary M ↦ e ⁻¹' ball (e q) (ρ₀ q / 2))
    (fun q ↦ isOpen_ball.preimage hemb.continuous)
    (fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, by simp [hρ₀]⟩)
  obtain ⟨lam, hlam, hleb⟩ := lebesgue_number_lemma_of_metric
    (c := fun q : t ↦ ball (e (q : I.boundary M)) (ρ₀ q / 2)) hB'c (fun _ ↦ isOpen_ball)
    (by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion.2 ⟨⟨q, hq⟩, hxq⟩)
  set c₀ := (∑ q ∈ t, (c q)⁻¹ + 1)⁻¹ with hc₀
  have hsum : 0 ≤ ∑ q ∈ t, (c q)⁻¹ := Finset.sum_nonneg fun q _ ↦ (inv_pos.2 (hc q)).le
  have hc₀le : ∀ q ∈ t, c₀ ≤ c q := by
    intro q hq
    rw [hc₀, inv_le_comm₀ (by positivity) (hc q)]
    have : (c q)⁻¹ ≤ ∑ y ∈ t, (c y)⁻¹ :=
      Finset.single_le_sum (f := fun y ↦ (c y)⁻¹) (fun y _ ↦ (inv_pos.2 (hc y)).le) hq
    linarith
  refine ⟨lam / 4, by positivity, c₀, by positivity, lam / 4, by positivity,
    fun p hp0 hpD ↦ ?_⟩
  have hBne : B.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, infDist_empty] at hp0
    exact lt_irrefl _ hp0
  obtain ⟨b₀, hb₀B, hb₀⟩ := hB'c.exists_infDist_eq_dist hBne (e p)
  obtain ⟨⟨q, hqt⟩, hq⟩ := hleb b₀ hb₀B
  have hpq : dist (e p) (e q) < ρ₀ q := by
    have : e p ∈ ball b₀ lam := by rw [mem_ball, ← hb₀]; linarith
    have := mem_ball.1 (hq this)
    linarith [hρ₀ q]
  obtain ⟨hsrc, hint, hinj', hrate⟩ := hpt q p hpq
  have hpB : p ∉ I.boundary M := fun h ↦ hp0.ne' (infDist_zero_of_mem ⟨p, h, rfl⟩)
  refine ⟨q, hsrc, hint hpB, hinj', fun z hz hzA b hb hzb ↦ ?_⟩
  have hzq : dist z (e q) < ρ₀ q := by
    have : z ∈ ball b₀ lam := by
      rw [mem_ball]
      have := dist_triangle z (e p) b₀
      rw [← hb₀] at this
      linarith
    have := mem_ball.1 (hq this)
    linarith [hρ₀ q]
  exact (mul_le_mul_of_nonneg_right (hc₀le q hqt) (norm_nonneg _)).trans
    (hrate z hzq hzA b hb hzb)

/-- **Regular smoothing of the distance to the boundary.** For an embedding `e` of a compact
manifold with corners into `ℝ^N`, there is `D₀ > 0` such that, for every `κ > 0` and every
small enough `ε > 0`, some `C²` function `ρ̃` with `|ρ̃ - d_B| ≤ ε`, `B = e(∂M)`, has `ρ̃ ∘ e` with
nonzero derivative at every point `p` with `κ ≤ d_B (e p) ≤ D₀`; such a point is interior in a chart
at `x₀`, in which `e` has injective derivative. -/
theorem exists_regular_smoothing_infDist_boundary [CompactSpace M]
    {e : M → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) 2 e)
    (hemb : IsEmbedding e)
    (hinj : ∀ x, Injective
      (mfderiv (modelWithCornersEuclideanQuadrant n) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) e x)) :
    ∃ D₀ > 0, ∀ κ > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∃ ρ : EuclideanSpace ℝ (Fin N) → ℝ, ContDiff ℝ 2 ρ ∧
        (∀ y, |ρ y - infDist y (e '' (modelWithCornersEuclideanQuadrant n).boundary M)| ≤ ε) ∧
        ∀ p, infDist (e p) (e '' (modelWithCornersEuclideanQuadrant n).boundary M) ∈
            Icc κ D₀ →
          ∃ x₀, p ∈ (chartAt (EuclideanQuadrant n) x₀).source ∧
            extChartAt (modelWithCornersEuclideanQuadrant n) x₀ p ∈
              interior (range (modelWithCornersEuclideanQuadrant n)) ∧
            fderivWithin ℝ ((ρ ∘ e) ∘ (extChartAt (modelWithCornersEuclideanQuadrant n) x₀).symm)
              (range (modelWithCornersEuclideanQuadrant n))
              (extChartAt (modelWithCornersEuclideanQuadrant n) x₀ p) ≠ 0 ∧
            Injective (fderivWithin ℝ
              (e ∘ (extChartAt (modelWithCornersEuclideanQuadrant n) x₀).symm)
              (range (modelWithCornersEuclideanQuadrant n))
              (extChartAt (modelWithCornersEuclideanQuadrant n) x₀ p)) := by
  set I := modelWithCornersEuclideanQuadrant n with hI
  set B := e '' I.boundary M with hB
  obtain ⟨D₀, hD₀, c, hc, lam, hlam, hrate⟩ := exists_rate_infDist_boundary he hemb hinj
  refine ⟨D₀, hD₀, fun κ hκ ↦ ⟨min (lam / 2) (κ / 6), lt_min (by positivity) (by positivity),
    fun ε hε hεle ↦ ?_⟩⟩
  have hε1 : ε ≤ lam / 2 := hεle.trans (min_le_left _ _)
  have hε2 : ε ≤ κ / 6 := hεle.trans (min_le_right _ _)
  obtain ⟨ρ, hρc, hρd, hρm⟩ :=
    exists_contDiff_abs_sub_le_of_lipschitzWith (lipschitz_infDist_pt B) hε
  refine ⟨ρ, hρc, hρd, fun p hp ↦ ?_⟩
  obtain ⟨x₀, hx₀, hint, hinj₀, hz⟩ :=
    hrate p (hκ.trans_le hp.1) hp.2
  refine ⟨x₀, hx₀, hint, ?_, hinj₀⟩
  set φ := extChartAt I x₀ with hφ
  set w := fderivWithin ℝ (e ∘ φ.symm) (range I) (φ p) (quadrantDiagonal n) with hw
  -- `d_B` increases at rate `c / 2` along `w` near `e p`
  have hB0 : B.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have := hp.1
    rw [h, infDist_empty] at this
    linarith
  have hBc : IsCompact B := ((ModelWithCorners.isClosed_boundary (I := I) (M := M) (n := 2)
    (by simp)).isCompact).image hemb.continuous
  set s₀ := min (κ / (c + 1)) (min (κ / (6 * (‖w‖ + 1))) (min (lam / (4 * (‖w‖ + 1)))
    (c * κ / (2 * (‖w‖ ^ 2 + 1))))) with hs₀
  have hs₀0 : 0 < s₀ := lt_min (by positivity)
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hderiv := hρm (e p) w (c / 2) s₀ hs₀0 fun y hy s hs ↦ by
    have hsw : s * ‖w‖ ≤ κ / 6 ∧ s * ‖w‖ ≤ lam / 4 := by
      have h1 : s ≤ κ / (6 * (‖w‖ + 1)) := hs.2.trans ((min_le_right _ _).trans
        (min_le_left _ _))
      have h2 : s ≤ lam / (4 * (‖w‖ + 1)) := hs.2.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
      constructor
      · rw [le_div_iff₀ (by positivity)] at h1; nlinarith [norm_nonneg w, hs.1]
      · rw [le_div_iff₀ (by positivity)] at h2; nlinarith [norm_nonneg w, hs.1]
    have hs3 : s * (‖w‖ ^ 2 + 1) ≤ c * κ / 2 := by
      have h3 : s ≤ c * κ / (2 * (‖w‖ ^ 2 + 1)) := hs.2.trans ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
      rw [le_div_iff₀ (by positivity)] at h3; linarith
    have hs4 : c * s ≤ κ := by
      have h4 : s ≤ κ / (c + 1) := hs.2.trans (min_le_left _ _)
      rw [le_div_iff₀ (by positivity)] at h4; nlinarith [hs.1]
    set z := y + s • w with hzdef
    have hyp : dist y (e p) < ε := hy
    have hzy : dist z y = s * ‖w‖ := by
      rw [hzdef, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1.le]
    have hzp : dist z (e p) < lam := by
      have := dist_triangle z y (e p); linarith
    have hfp : infDist (e p) B ≥ κ := hp.1
    have hfz : infDist z B ≥ 2 * κ / 3 := by
      have := infDist_le_infDist_add_dist (x := e p) (y := z) (s := B)
      rw [dist_comm] at this
      have := dist_triangle z y (e p)
      linarith
    have hAz : infDist z (range e) ≤ infDist z B / 2 := by
      have := infDist_le_dist_of_mem (mem_range_self (f := e) p) (x := z)
      have := dist_triangle z y (e p)
      linarith
    obtain ⟨b, hbB, hbz⟩ := hBc.exists_infDist_eq_dist hB0 z
    have hcz := hz z hzp hAz b hbB hbz.symm
    -- `d_B y ≤ ‖y - b‖`
    have hyb : infDist y B ≤ ‖y - b‖ := by
      rw [← dist_eq_norm]; exact infDist_le_dist_of_mem hbB
    have hexp : ‖y - b‖ ^ 2 = ‖z - b‖ ^ 2 - 2 * s * inner ℝ (z - b) w + s ^ 2 * ‖w‖ ^ 2 := by
      have : y - b = (z - b) - s • w := by rw [hzdef]; abel
      rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_of_nonneg hs.1.le]
      ring
    have hzb : ‖z - b‖ = infDist z B := by rw [← dist_eq_norm, hbz]
    by_contra hcon
    push Not at hcon
    have hd0 : 0 ≤ infDist y B := infDist_nonneg
    have hlow : infDist z B - c / 2 * s < infDist y B := by linarith
    have hpos : 0 ≤ infDist z B - c / 2 * s := by linarith
    have hsq : (infDist z B - c / 2 * s) ^ 2 < (infDist y B) ^ 2 :=
      pow_lt_pow_left₀ hlow hpos (by norm_num)
    have hyb2 : (infDist y B) ^ 2 ≤ ‖y - b‖ ^ 2 := pow_le_pow_left₀ hd0 hyb 2
    rw [hexp, hzb] at hyb2
    have hin : c * infDist z B ≤ inner ℝ (z - b) w := by rwa [← hzb]
    have h5 := lt_of_lt_of_le hsq hyb2
    have h6 : 2 * s * (c * infDist z B) ≤ 2 * s * inner ℝ (z - b) w :=
      mul_le_mul_of_nonneg_left hin (by linarith [hs.1])
    have key : s * (c * infDist z B) < s * (s * ‖w‖ ^ 2) := by
      nlinarith [h5, h6, sq_nonneg (c * s)]
    have key2 := lt_of_mul_lt_mul_left key hs.1.le
    have : c * (2 * κ / 3) ≤ c * infDist z B := mul_le_mul_of_nonneg_left hfz hc.le
    nlinarith [hs.1]
  -- the chain rule
  have hgc : ContDiffWithinAt ℝ 2 (e ∘ φ.symm) (range I) (φ p) :=
    contMDiffWithinAt_iff_contDiffWithinAt.1
      ((contMDiffAt_iff_source_of_mem_source hx₀).1 (he p))
  have hgd : HasFDerivWithinAt (e ∘ φ.symm) (fderivWithin ℝ (e ∘ φ.symm) (range I) (φ p))
      (range I) (φ p) := (hgc.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  have hgp : (e ∘ φ.symm) (φ p) = e p := by
    simp only [comp_apply]
    rw [φ.left_inv (by rwa [hφ, extChartAt_source])]
  have hρd' : HasFDerivAt ρ (fderiv ℝ ρ (e p)) ((e ∘ φ.symm) (φ p)) := by
    rw [hgp]; exact (hρc.differentiable (by norm_num) _).hasFDerivAt
  have hcomp := hρd'.comp_hasFDerivWithinAt (φ p) hgd
  have heq : fderivWithin ℝ ((ρ ∘ e) ∘ φ.symm) (range I) (φ p) =
      (fderiv ℝ ρ (e p)).comp (fderivWithin ℝ (e ∘ φ.symm) (range I) (φ p)) :=
    hcomp.fderivWithin (I.uniqueDiffOn _ (interior_subset hint))
  intro h0
  have := congrArg (fun L ↦ L (quadrantDiagonal n)) (heq.symm.trans h0)
  simp only [ContinuousLinearMap.coe_comp, comp_apply, zero_apply] at this
  rw [← hw] at this
  linarith

end

end MMP.Topology
