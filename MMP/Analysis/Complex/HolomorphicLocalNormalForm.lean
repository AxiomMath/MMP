module

public import MMP.Geometry.Manifold.SmoothLevelSet
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Holomorphic local normal form of `v πᵐ`

Let `E` be a finite-dimensional complex normed space, `O ⊆ E` open, and `π, v` holomorphic on `O`
with `v` nowhere zero, `π(k₀) = 0` and `dπ(k₀) ≠ 0` at a point `k₀ ∈ O`. On a small ball around
`k₀` the function `v / v(k₀)` takes values in the disc `|z - 1| < 1`, so it has a holomorphic
logarithm `w`, and `g = π · exp((log v(k₀) + w) / m)` is a holomorphic function with
`gᵐ = v πᵐ` and `dg(k₀) = exp(log v(k₀) / m) dπ(k₀) ≠ 0`. Completing `g` by a linear projection
onto `ker dg(k₀)` to the map `k ↦ (g k, P k)` and applying the inverse function theorem
(`MMP.SmoothLevelSet.localDiffeo`) gives holomorphic coordinates around `k₀`, with
values in `ℂ × F` (`dim F = dim E - 1`) and convex image, whose first coordinate is `g`. In these
coordinates the zero set of `v πᵐ` is the hyperplane `{0} × F`.

## Main results

* `MMP.LocalNormalForm.exists_pow_eq_mul_pow_of_fderiv_ne_zero`: the coordinates
  and the function `g` above.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
-/

@[expose] public noncomputable section

open Set Topology Filter Metric
open scoped ContDiff

namespace MMP

namespace LocalNormalForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] in
/-- A nonzero continuous linear form is surjective. -/
lemma surjective_of_ne_zero {φ : E →L[ℂ] ℂ} (h : φ ≠ 0) : Function.Surjective φ := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra hc
    exact h (ContinuousLinearMap.ext fun x ↦ not_not.1 fun hx ↦ hc ⟨x, hx⟩)
  intro z
  refine ⟨(z / φ v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]

/-- **Holomorphic local normal form.** Let `π, v` be holomorphic on the open set `O ∋ k₀`, with `v`
nowhere zero on `O`, `π(k₀) = 0` and `dπ(k₀) ≠ 0`, and let `m ≥ 1`. Then there are a holomorphic
function `g` and holomorphic coordinates `ψ` around `k₀`, with values in `ℂ × F` for any `F` of
dimension `dim E - 1`, defined on a subset of `O` and with convex image, such that the first
coordinate of `ψ` is `g`, `v πᵐ = gᵐ`, and `dg` vanishes nowhere on the source of `ψ`. -/
theorem exists_pow_eq_mul_pow_of_fderiv_ne_zero (hF : Module.finrank ℂ F + 1 = Module.finrank ℂ E)
    {O : Set E} (hO : IsOpen O) {k₀ : E} (hk₀ : k₀ ∈ O) {π v : E → ℂ}
    (hπ : ContDiffOn ℂ ω π O) (hv : ContDiffOn ℂ ω v O) (hv0 : ∀ k ∈ O, v k ≠ 0)
    (hπ0 : π k₀ = 0) (hdπ : fderiv ℂ π k₀ ≠ 0) {m : ℕ} (hm : 0 < m) :
    ∃ (g : E → ℂ) (ψ : OpenPartialHomeomorph E (ℂ × F)),
      k₀ ∈ ψ.source ∧ ψ.source ⊆ O ∧ Convex ℝ ψ.target ∧
      ContDiffOn ℂ ω ψ ψ.source ∧ ContDiffOn ℂ ω ψ.symm ψ.target ∧ ContDiffOn ℂ ω g ψ.source ∧
      (∀ k ∈ ψ.source, (ψ k).1 = g k) ∧ (∀ k ∈ ψ.source, v k * π k ^ m = g k ^ m) ∧
      ∀ k ∈ ψ.source, fderiv ℂ g k ≠ 0 := by
  -- a holomorphic logarithm of `v / v(k₀)` near `k₀`
  set c := v k₀ with hc
  have hc0 : c ≠ 0 := hv0 k₀ hk₀
  have hvc : ContinuousAt (fun k ↦ v k / c - 1) k₀ :=
    (((hv.continuousOn.continuousAt (hO.mem_nhds hk₀)).div_const c).sub continuousAt_const)
  have hev : ∀ᶠ k in 𝓝 k₀, k ∈ O ∧ ‖v k / c - 1‖ < 1 := by
    have h1 : ∀ᶠ k in 𝓝 k₀, k ∈ O := hO.mem_nhds hk₀
    have h0 : (fun k ↦ v k / c - 1) k₀ ∈ ball (0 : ℂ) 1 := by
      simp only [← hc, div_self hc0, sub_self]
      exact mem_ball_self one_pos
    have h2 := hvc.eventually (isOpen_ball.mem_nhds h0)
    exact h1.and (h2.mono fun k hk ↦ mem_ball_zero_iff.1 hk)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set B := ball k₀ r
  have hBO : B ⊆ O := fun k hk ↦ (hball k hk).1
  have hslit : ∀ k ∈ B, v k / c ∈ Complex.slitPlane := fun k hk ↦ by
    have := Complex.mem_slitPlane_of_norm_lt_one (hball k hk).2
    rwa [add_sub_cancel] at this
  set w : E → ℂ := fun k ↦ Complex.log (v k / c)
  have hw : ContDiffOn ℂ ω w B := fun k hk ↦ by
    have := (Complex.contDiffAt_log (n := ω) (hslit k hk)).comp_contDiffWithinAt
      (f := fun k ↦ v k / c) k ((hv.mono hBO).div_const c k hk)
    exact this
  set g : E → ℂ := fun k ↦ π k * Complex.exp ((Complex.log c + w k) / m)
  have hg : ContDiffOn ℂ ω g B :=
    (hπ.mono hBO).mul (Complex.contDiff_exp.comp_contDiffOn
      ((contDiffOn_const.add hw).div_const _))
  have hgm : ∀ k ∈ B, v k * π k ^ m = g k ^ m := by
    intro k hk
    have hvk : v k / c ≠ 0 := div_ne_zero (hv0 k (hBO hk)) hc0
    simp only [g, mul_pow, ← Complex.exp_nat_mul]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hm.ne' : (m : ℂ) ≠ 0), Complex.exp_add,
      Complex.exp_log hc0, Complex.exp_log hvk, mul_div_cancel₀ _ hc0, mul_comm]
  -- the differential of `g` at `k₀`
  have hk₀B : k₀ ∈ B := mem_ball_self hr
  have hdiffB : ∀ {f : E → ℂ}, ContDiffOn ℂ ω f B → ∀ k ∈ B, DifferentiableAt ℂ f k :=
    fun hf k hk ↦ (hf.contDiffAt (isOpen_ball.mem_nhds hk)).differentiableAt (by simp)
  have hdg0 : fderiv ℂ g k₀ ≠ 0 := by
    have hE : DifferentiableAt ℂ (fun k ↦ Complex.exp ((Complex.log c + w k) / m)) k₀ :=
      hdiffB (Complex.contDiff_exp.comp_contDiffOn ((contDiffOn_const.add hw).div_const _)) k₀
        hk₀B
    rw [fderiv_fun_mul (hdiffB (hπ.mono hBO) k₀ hk₀B) hE, hπ0, zero_smul, zero_add]
    exact smul_ne_zero (Complex.exp_ne_zero _) hdπ
  -- the open set where `dg ≠ 0`, on which `g` is a submersion
  set O' := {k ∈ B | fderiv ℂ g k ≠ 0}
  have hO' : IsOpen O' :=
    (hg.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).isOpen_inter_preimage isOpen_ball
      isOpen_compl_singleton
  have hsub : SmoothLevelSet.IsSubmersionOn (𝕜 := ℂ) ω O' g :=
    { isOpen := hO'
      contDiffOn := hg.mono fun k hk ↦ hk.1
      one_le := by simp
      surjective := fun k hk ↦ surjective_of_ne_zero hk.1.2 }
  have hz : k₀ ∈ SmoothLevelSet.levelSet O' g := ⟨⟨hk₀B, hdg0⟩, by simp [g, hπ0]⟩
  set ψ₀ := SmoothLevelSet.localDiffeo hsub hz
  -- identify the kernel of `dg(k₀)` with `F`
  have hker : Module.finrank ℂ (SmoothLevelSet.ker ℂ g k₀) = Module.finrank ℂ F := by
    have h1 := SmoothLevelSet.finrank_ker hsub hz
    rw [finrank_euclideanSpace_fin, SmoothLevelSet.dim, Module.finrank_self] at h1
    omega
  set L : (ℂ × SmoothLevelSet.ker ℂ g k₀) ≃L[ℂ] ℂ × F :=
    (ContinuousLinearEquiv.refl ℂ ℂ).prodCongr (ContinuousLinearEquiv.ofFinrankEq hker)
  set ψ₁ := ψ₀.trans L.toHomeomorph.toOpenPartialHomeomorph
  have hψ₁k₀ : k₀ ∈ ψ₁.source := by
    simp only [ψ₁, OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source,
      preimage_univ, inter_univ]
    exact SmoothLevelSet.mem_localDiffeo_source hsub hz
  obtain ⟨ρ, hρ, hρt⟩ := Metric.isOpen_iff.1 ψ₁.open_target _ (ψ₁.map_source hψ₁k₀)
  set ψ := (ψ₁.symm.restrOpen (ball (ψ₁ k₀) ρ) isOpen_ball).symm
  have hψt : ψ.target = ball (ψ₁ k₀) ρ := by
    simp only [ψ, OpenPartialHomeomorph.symm_target, OpenPartialHomeomorph.restrOpen_source,
      OpenPartialHomeomorph.symm_source]
    exact inter_eq_right.2 hρt
  have hψsrc : ψ.source = ψ₁.source ∩ ψ₁ ⁻¹' ball (ψ₁ k₀) ρ := rfl
  have hψ₁s : ψ₁.source = ψ₀.source := by
    simp [ψ₁]
  have hψs : ψ.source ⊆ ψ₀.source := fun k hk ↦ by
    rw [hψsrc, hψ₁s] at hk
    exact hk.1
  have hψ0 : ψ.source ⊆ O' := fun k hk ↦
    SmoothLevelSet.goodSet_subset k₀ (SmoothLevelSet.localDiffeo_source_subset hsub hz (hψs hk))
  have hψapp : ∀ k, ψ k = L (ψ₀ k) := fun _ ↦ rfl
  have hψ₀app : ∀ k, ψ₀ k = (g k, SmoothLevelSet.proj ℂ g k₀ k) := fun _ ↦ rfl
  refine ⟨g, ψ, ?_, fun k hk ↦ hBO (hψ0 hk).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hψsrc]
    exact ⟨hψ₁k₀, mem_ball_self hρ⟩
  · rw [hψt]
    exact convex_ball _ _
  · intro k hk
    refine ContDiffAt.contDiffWithinAt ?_
    have : (ψ : E → ℂ × F) = fun k ↦ L (SmoothLevelSet.prodFun ℂ g k₀ k) := rfl
    rw [this]
    exact L.contDiff.contDiffAt.comp _ (SmoothLevelSet.contDiffAt_prodFun hsub (hψ0 hk))
  · intro q hq
    refine ContDiffAt.contDiffWithinAt ?_
    have hq' : L.symm q ∈ ψ₀.target := by
      have := ψ.map_target hq
      have h1 : ψ₀ (ψ.symm q) ∈ ψ₀.target := ψ₀.map_source (hψs this)
      have h2 : ψ (ψ.symm q) = q := ψ.right_inv hq
      rw [hψapp] at h2
      rw [← h2, L.symm_apply_apply]
      exact h1
    have heq : (ψ.symm : ℂ × F → E) =ᶠ[𝓝 q] fun q ↦ ψ₀.symm (L.symm q) := by
      filter_upwards [ψ.open_target.mem_nhds hq] with q' _
      rfl
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq
    exact (SmoothLevelSet.contDiffAt_localDiffeo_symm hsub hz hq').comp _
      L.symm.contDiff.contDiffAt
  · exact hg.mono fun k hk ↦ (hψ0 hk).1
  · intro k _
    rw [hψapp, hψ₀app]
    rfl
  · exact fun k hk ↦ hgm k (hψ0 hk).1
  · exact fun k hk ↦ (hψ0 hk).2

end LocalNormalForm

end MMP
