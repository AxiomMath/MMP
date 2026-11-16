module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Liouville's theorem with polynomial growth

An entire function `f : ℂ → ℂ` with `‖f z‖ ≤ C (1 + ‖z‖)^N` for all `z` is a polynomial of
degree at most `N`. For `N = 0` this is Liouville's theorem; in general, the difference quotient
`(f z - f 0) / z` is entire and grows like `(1 + ‖z‖)^(N - 1)`, and we induct on `N`.

## Main results

* `MMP.LiouvilleGrowth.exists_polynomial_of_norm_le_mul_one_add_pow`: an entire function with
  `‖f z‖ ≤ C (1 + ‖z‖)^N` is a polynomial of degree at most `N`.
* `MMP.LiouvilleGrowth.exists_polynomial_of_differentiableOn_compl_finite`: the same for a
  function holomorphic off a finite set and bounded there by `C (1 + ‖z‖)^N` (the points of the
  finite set are removable).

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open Polynomial

namespace MMP.LiouvilleGrowth

/-- **Liouville's theorem with polynomial growth.** An entire function `f` with
`‖f z‖ ≤ C (1 + ‖z‖)^N` for all `z` is a polynomial of degree at most `N`. -/
theorem exists_polynomial_of_norm_le_mul_one_add_pow {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {C : ℝ} {N : ℕ} (hb : ∀ z, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ p : ℂ[X], p.natDegree ≤ N ∧ ∀ z, f z = p.eval z := by
  induction N generalizing f C with
  | zero =>
    refine ⟨Polynomial.C (f 0), by simp, fun z ↦ ?_⟩
    rw [eval_C]
    refine hf.apply_eq_apply_of_bounded ?_ z 0
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    rintro _ ⟨w, rfl⟩
    simpa using hb w
  | succ N ih =>
    have hC : 0 ≤ C := by
      have h0 := hb 0
      have : 0 < (1 + ‖(0:ℂ)‖) ^ (N + 1) := by positivity
      nlinarith [norm_nonneg (f 0)]
    have hslope : ∀ z, z * dslope f 0 z = f z - f 0 := fun z ↦ by
      simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope f 0 z
    set g := dslope f 0
    have hg : Differentiable ℂ g := by
      rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
      exact hf.differentiableOn
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn
      hg.continuous.continuousOn
    have hbg : ∀ z, ‖g z‖ ≤ (max M 0 + 2 * C + ‖f 0‖) * (1 + ‖z‖) ^ N := by
      intro z
      have h1 : 1 ≤ (1 + ‖z‖) ^ N := one_le_pow₀ (by linarith [norm_nonneg z])
      by_cases hz : ‖z‖ ≤ 1
      · have := hM z (by simpa using hz)
        have : 0 ≤ (2 * C + ‖f 0‖) * (1 + ‖z‖) ^ N := by positivity
        nlinarith [le_max_left M 0, le_max_right M 0]
      · have hz : 1 < ‖z‖ := lt_of_not_ge hz
        have hgz : ‖g z‖ * ‖z‖ ≤ C * (1 + ‖z‖) ^ (N + 1) + ‖f 0‖ := by
          rw [← norm_mul, mul_comm, hslope z]
          exact (norm_sub_le _ _).trans (by linarith [hb z])
        have hpow : (1 + ‖z‖) ^ (N + 1) ≤ 2 * ‖z‖ * (1 + ‖z‖) ^ N := by
          rw [pow_succ]
          have : 0 ≤ (1 + ‖z‖) ^ N := by positivity
          nlinarith
        have hzpos : 0 < ‖z‖ := by linarith
        have key : ‖g z‖ * ‖z‖ ≤ ((2 * C + ‖f 0‖) * (1 + ‖z‖) ^ N) * ‖z‖ := by
          have : ‖f 0‖ ≤ ‖f 0‖ * (1 + ‖z‖) ^ N * ‖z‖ := by
            have : 1 ≤ (1 + ‖z‖) ^ N * ‖z‖ := by nlinarith
            nlinarith [norm_nonneg (f 0)]
          nlinarith [mul_le_mul_of_nonneg_left hpow hC]
        have := le_of_mul_le_mul_right key hzpos
        have : 0 ≤ max M 0 * (1 + ‖z‖) ^ N := by positivity
        nlinarith
    obtain ⟨q, hq, hgq⟩ := ih hg hbg
    refine ⟨Polynomial.C (f 0) + X * q, ?_, fun z ↦ ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      refine (natDegree_mul_le).trans ?_
      simp only [natDegree_X]
      omega
    · simp only [eval_add, eval_C, eval_mul, eval_X, ← hgq z]
      linear_combination -(hslope z)

open Filter Topology Set in
/-- **Removable singularities and polynomial growth.** A function `f : ℂ → ℂ` which is
holomorphic off a finite set `S` and satisfies `‖f z‖ ≤ C (1 + ‖z‖)^N` off `S` agrees off `S` with
a polynomial of degree at most `N`: the bound makes each point of `S` a removable singularity,
and the extension is entire with polynomial growth. -/
theorem exists_polynomial_of_differentiableOn_compl_finite {f : ℂ → ℂ} {S : Set ℂ}
    (hS : S.Finite) (hf : DifferentiableOn ℂ f Sᶜ) {C : ℝ} {N : ℕ}
    (hb : ∀ z ∉ S, ‖f z‖ ≤ C * (1 + ‖z‖) ^ N) :
    ∃ p : ℂ[X], p.natDegree ≤ N ∧ ∀ z ∉ S, f z = p.eval z := by
  induction S, hS using Set.Finite.induction_on generalizing f with
  | empty =>
    obtain ⟨p, hp, hfp⟩ := exists_polynomial_of_norm_le_mul_one_add_pow
      (f := f) (fun z ↦ (hf z (by simp)).differentiableAt (by simp)) (fun z ↦ hb z (by simp))
    exact ⟨p, hp, fun z _ ↦ hfp z⟩
  | @insert a T haT hT ih =>
    have hTc : Tᶜ ∈ 𝓝 a := hT.isClosed.isOpen_compl.mem_nhds haT
    set f' := Function.update f a (limUnder (𝓝[≠] a) f)
    have hball : DifferentiableOn ℂ f' (Tᶜ ∩ Metric.ball a 1) := by
      refine Complex.differentiableOn_update_limUnder_of_bddAbove
        (inter_mem hTc (Metric.ball_mem_nhds a one_pos)) ?_ ?_
      · refine hf.mono ?_
        rintro z ⟨⟨hzT, -⟩, hza⟩
        simp only [mem_compl_iff, mem_insert_iff, not_or]
        exact ⟨hza, hzT⟩
      · refine ⟨C * (1 + (‖a‖ + 1)) ^ N, ?_⟩
        rintro _ ⟨z, ⟨⟨hzT, hzb⟩, hza⟩, rfl⟩
        have hz : z ∉ insert a T := by simp only [mem_insert_iff, not_or]; exact ⟨hza, hzT⟩
        have hC : 0 ≤ C := by
          have := hb z hz
          have : 0 < (1 + ‖z‖) ^ N := by positivity
          nlinarith [norm_nonneg (f z)]
        refine (hb z hz).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hC)
        have : ‖z‖ ≤ ‖a‖ + 1 := by
          have := norm_le_norm_add_norm_sub' z a
          rw [Metric.mem_ball, dist_eq_norm] at hzb
          linarith
        linarith
    have hdiff : DifferentiableOn ℂ f' Tᶜ := by
      intro z hzT
      by_cases hza : z = a
      · subst hza
        exact (hball.differentiableAt
          (inter_mem hTc (Metric.ball_mem_nhds z one_pos))).differentiableWithinAt
      · have hopen : (insert a T)ᶜ ∈ 𝓝 z :=
          (hT.insert a).isClosed.isOpen_compl.mem_nhds (by simpa [hza] using hzT)
        have hd : DifferentiableAt ℂ f z :=
          (hf z (by simpa [hza] using hzT)).differentiableAt hopen
        refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
        filter_upwards [hopen] with w hw
        have : w ≠ a := fun h ↦ hw (h ▸ mem_insert _ _)
        simp [f', this]
    have hb' : ∀ z ∉ T, ‖f' z‖ ≤ C * (1 + ‖z‖) ^ N := by
      intro z hzT
      by_cases hza : z = a
      · subst hza
        have hcont : ContinuousAt f' z :=
          (hdiff.differentiableAt (hT.isClosed.isOpen_compl.mem_nhds hzT)).continuousAt
        have h1 : Tendsto (fun w ↦ ‖f' w‖) (𝓝[≠] z) (𝓝 ‖f' z‖) :=
          (hcont.norm).tendsto.mono_left nhdsWithin_le_nhds
        have h2 : Tendsto (fun w : ℂ ↦ C * (1 + ‖w‖) ^ N) (𝓝[≠] z)
            (𝓝 (C * (1 + ‖z‖) ^ N)) :=
          ((continuous_const.mul ((continuous_const.add continuous_norm).pow N)).tendsto
            z).mono_left nhdsWithin_le_nhds
        refine le_of_tendsto_of_tendsto h1 h2 ?_
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hTc] with w hw hwT
        have : w ≠ z := hw
        simp only [f', Function.update_of_ne this]
        exact hb w (by simpa [this] using hwT)
      · simp only [f', Function.update_of_ne hza]
        exact hb z (by simpa [hza] using hzT)
    obtain ⟨p, hp, hfp⟩ := ih hdiff hb'
    refine ⟨p, hp, fun z hz ↦ ?_⟩
    simp only [mem_insert_iff, not_or] at hz
    rw [← hfp z hz.2]
    simp [f', Function.update_of_ne hz.1]

end MMP.LiouvilleGrowth
