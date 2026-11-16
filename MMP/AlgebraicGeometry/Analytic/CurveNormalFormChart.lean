module

public import MMP.AlgebraicTopology.ComplexVectorBundle.FirstChernClass
public import MMP.AlgebraicGeometry.Analytic.SchemeManifold

/-!
# Analytic normal form of a regular function on a smooth complex curve

A holomorphic function `G` of one variable which is not locally constant at `z₀` is, near `z₀`,
of the form `G z₀ + ψ ^ n` with `n ≥ 1` and `ψ` a local analytic coordinate centred at `z₀`.
Transported through an étale coordinate chart of the complex manifold `X^an` of a scheme `X`
smooth of relative dimension one over `ℂ`, this gives the local normal form `h = h(a) + φ ^ e` of
a regular function `h` that is not locally constant at a point `a` of `X^an`, for a coordinate
`φ` centred at `a` whose inverse is analytic when read in the chart.

## Main results

* `MMP.Analytic.exists_analyticAt_pow_normalForm`: the local normal form `G = G z₀ + ψ ^ n` of a
  non-constant analytic function of one variable.
* `MMP.Analytic.exists_analytic_openPartialHomeomorph`: a function analytic at `z₀` with nonzero
  derivative restricts to an analytic open partial homeomorphism with analytic inverse.
* `MMP.Analytic.exists_analytic_normalForm_chart`: the normal form of a regular function on a
  smooth complex curve, in an étale coordinate chart.

## References

* [P. Griffiths, J. Harris, *Principles of algebraic geometry*][GriffithsHarris], §0.1.
-/

@[expose] public section

open AlgebraicGeometry
open scoped Topology

namespace MMP.Analytic

open InvertibleModule (evalExt evalExt_of_mem)

/-- **Analytic local normal form.** A function analytic at `z₀` and not locally constant there
is `G z₀ + ψ ^ n` near `z₀`, for some `n ≥ 1` and a function `ψ` analytic at `z₀` with
`ψ z₀ = 0` and `deriv ψ z₀ ≠ 0`. -/
theorem exists_analyticAt_pow_normalForm {G : ℂ → ℂ} {z₀ : ℂ} (hG : AnalyticAt ℂ G z₀)
    (hnc : ¬ ∀ᶠ z in 𝓝 z₀, G z = G z₀) :
    ∃ (n : ℕ) (ψ : ℂ → ℂ), 0 < n ∧ AnalyticAt ℂ ψ z₀ ∧ deriv ψ z₀ ≠ 0 ∧ ψ z₀ = 0 ∧
      ∀ᶠ z in 𝓝 z₀, G z = G z₀ + ψ z ^ n := by
  have hH : AnalyticAt ℂ (fun z ↦ G z - G z₀) z₀ := hG.sub analyticAt_const
  have hH0 : ¬ ∀ᶠ z in 𝓝 z₀, G z - G z₀ = 0 := by
    simpa [sub_eq_zero] using hnc
  obtain ⟨n, g, hg, hg0, hgeq⟩ := (hH.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hH0
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have := hgeq.self_of_nhds
      simp at this
      exact absurd this.symm hg0
    · exact hn
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq (g z₀) hn
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl; rw [zero_pow hn.ne'] at hc₀; exact hg0 hc₀.symm
  set k : ℂ → ℂ := fun z ↦ c₀ * Complex.exp (Complex.log (g z / g z₀) / n)
  have hslit : g z₀ / g z₀ ∈ Complex.slitPlane := by
    rw [div_self hg0]; exact Complex.one_mem_slitPlane
  have h1 : AnalyticAt ℂ (fun z ↦ g z / g z₀) z₀ := hg.div_const
  have h2 : AnalyticAt ℂ (fun z ↦ Complex.log (g z / g z₀)) z₀ :=
    (analyticAt_clog hslit).comp_of_eq h1 rfl
  have hk : AnalyticAt ℂ k z₀ := analyticAt_const.mul (h2.div_const).cexp
  have hkz₀ : k z₀ = c₀ := by simp [k, div_self hg0]
  have hkn : ∀ᶠ z in 𝓝 z₀, k z ^ n = g z := by
    filter_upwards [hg.continuousAt.eventually_ne hg0] with z hz
    simp only [k, mul_pow, ← Complex.exp_nat_mul, hc₀]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne'), Complex.exp_log (div_ne_zero hz hg0),
      mul_div_cancel₀ _ hg0]
  set ψ : ℂ → ℂ := fun z ↦ (z - z₀) * k z
  have hψ : AnalyticAt ℂ ψ z₀ := (analyticAt_id.sub analyticAt_const).mul hk
  have hψd : HasDerivAt ψ (k z₀) z₀ := by
    have := ((hasDerivAt_id z₀).sub_const z₀).mul hk.differentiableAt.hasDerivAt
    have h' : HasDerivAt ψ _ z₀ := this
    convert h' using 1
    simp
  refine ⟨n, ψ, hn, hψ, by rw [hψd.deriv, hkz₀]; exact hc₀0, by simp [ψ], ?_⟩
  filter_upwards [hgeq, hkn] with z hz hkz
  simp only [smul_eq_mul] at hz
  simp only [ψ, mul_pow, hkz]
  rw [← hz]
  ring

/-- **An analytic coordinate.** If `ψ` is analytic at `z₀` with `deriv ψ z₀ ≠ 0`, it restricts to
an open partial homeomorphism around `z₀`, contained in a given neighbourhood `N`, agreeing with `ψ`
on its source, and analytic with analytic inverse. -/
theorem exists_analytic_openPartialHomeomorph {ψ : ℂ → ℂ} {z₀ : ℂ}
    (hψ : AnalyticAt ℂ ψ z₀) (hd : deriv ψ z₀ ≠ 0) {N : Set ℂ} (hN : N ∈ 𝓝 z₀) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z₀ ∈ e.source ∧ e.source ⊆ N ∧ Set.EqOn e ψ e.source ∧
      (∀ z ∈ e.source, AnalyticAt ℂ e z) ∧ ∀ w ∈ e.target, AnalyticAt ℂ e.symm w := by
  have hs : HasStrictDerivAt ψ (deriv ψ z₀) z₀ := hψ.hasStrictDerivAt
  set e₀ := (hs.hasStrictFDerivAt_equiv hd).toOpenPartialHomeomorph ψ
  -- the open set where `ψ` is analytic with nonzero derivative
  have hev : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ ψ z ∧ deriv ψ z ≠ 0 :=
    hψ.eventually_analyticAt.and ((hψ.deriv.continuousAt).eventually_ne hd)
  obtain ⟨V, hVsub, hVo, hz₀V⟩ := mem_nhds_iff.1 (Filter.inter_mem hev hN)
  set e := e₀.restrOpen V hVo
  have hz₀e : z₀ ∈ e₀.source := (hs.hasStrictFDerivAt_equiv hd).mem_toOpenPartialHomeomorph_source
  refine ⟨e, ⟨hz₀e, hz₀V⟩, fun z hz ↦ (hVsub hz.2).2, fun z _ ↦ rfl, fun z hz ↦ ?_, fun w hw ↦ ?_⟩
  · exact (hVsub hz.2).1.1
  · have hws : e.symm w ∈ e.source := e.map_target hw
    have ha := (hVsub hws.2).1
    refine e.analyticAt_symm hw (i := (ContinuousLinearEquiv.unitsEquivAut ℂ
      (Units.mk0 _ ha.2))) ha.1 ?_
    change fderiv ℂ ψ (e.symm w) = _
    refine ContinuousLinearMap.ext_ring ?_
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquivAut_apply,
      Units.val_mk0, one_mul]
    rfl

/-- **Analytic normal form of a regular function on a curve.** In a one-dimensional étale chart
`c` at `a`, a regular function `h` that is not locally constant at `a` is `h a + φ ^ e` for a
coordinate `φ` centred at `a` whose inverse, read in `c`, is analytic. -/
theorem exists_analytic_normalForm_chart {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of ℂ))]
    (c : ComplexPoints.EtaleCoordinateChart (X ↘ Spec (.of ℂ)) 1) (V : X.Opens) (h : Γ(X, V))
    {a : ComplexPoints (X ↘ Spec (.of ℂ))} (haW : a ∈ c.W)
    (haV : a ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V)
    (hnc : ¬ ∀ᶠ y in 𝓝 a, evalExt V h y = evalExt V h a) :
    ∃ (e : ℕ) (φ : OpenPartialHomeomorph (ComplexPoints (X ↘ Spec (.of ℂ))) ℂ), 0 < e ∧
      a ∈ φ.source ∧ φ.source ⊆ c.W ∩ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V ∧
      φ a = 0 ∧ (∀ x ∈ φ.source, evalExt V h x = evalExt V h a + φ x ^ e) ∧
      ∀ w ∈ φ.target, AnalyticAt ℂ (fun w ↦ c.toOpenPartialHomeomorph (φ.symm w)) w := by
  set κ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ
  set e₀ := c.toOpenPartialHomeomorph
  have hsrc : e₀.source = c.W := c.source_toOpenPartialHomeomorph
  obtain ⟨G, hG, hGe⟩ := c.exists_analyticOnNhd V h
  set T := e₀.target ∩ e₀.symm ⁻¹' ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V
  have hTo : IsOpen T := e₀.isOpen_inter_preimage_symm (ComplexPoints.isOpen_chart _ V)
  have hae : a ∈ e₀.source := hsrc ▸ haW
  have hT : e₀ a ∈ T := ⟨e₀.map_source hae, by rw [Set.mem_preimage, e₀.left_inv hae]; exact haV⟩
  set G' : ℂ → ℂ := fun z ↦ G (κ.symm z)
  set z₀ := κ (e₀ a)
  have hG' : AnalyticAt ℂ G' z₀ := by
    have h1 : AnalyticAt ℂ G (κ.symm z₀) := by
      simp only [z₀, ContinuousLinearEquiv.symm_apply_apply]; exact hG _ hT
    exact h1.comp ((κ.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).analyticAt _)
  have hrep : ∀ y ∈ c.W, y ∈ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V →
      evalExt V h y = G' (κ (e₀ y)) := by
    intro y hyW hyV
    rw [evalExt_of_mem _ hyV, hGe y hyW hyV]
    simp only [G', ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hnbhd : c.W ∩ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V ∈ 𝓝 a :=
    (c.isOpen.inter (ComplexPoints.isOpen_chart _ V)).mem_nhds ⟨haW, haV⟩
  have hcont : ContinuousAt (fun y ↦ κ (e₀ y)) a :=
    κ.continuous.continuousAt.comp (e₀.continuousAt hae)
  have hnc' : ¬ ∀ᶠ z in 𝓝 z₀, G' z = G' z₀ := by
    intro hev
    apply hnc
    filter_upwards [hcont.eventually hev, hnbhd] with y h1 h2
    rw [hrep y h2.1 h2.2, hrep a haW haV, h1]
  obtain ⟨n, ψ, hn, hψa, hψd, hψ0, hψeq⟩ := exists_analyticAt_pow_normalForm hG' hnc'
  have hN : {z | G' z = G' z₀ + ψ z ^ n} ∩ κ.symm ⁻¹' T ∈ 𝓝 z₀ := by
    refine Filter.inter_mem hψeq ?_
    refine κ.symm.continuous.continuousAt.preimage_mem_nhds (hTo.mem_nhds ?_)
    simpa [z₀] using hT
  obtain ⟨E, hz₀E, hEN, hEψ, -, hEsymm⟩ := exists_analytic_openPartialHomeomorph hψa hψd hN
  set c' := e₀.transHomeomorph κ.toHomeomorph
  set φ := c'.trans E
  have hφsrc : ∀ y, y ∈ φ.source ↔ y ∈ c.W ∧ κ (e₀ y) ∈ E.source := by
    intro y
    simp [φ, c', hsrc]
  have hφapp : ∀ y, φ y = E (κ (e₀ y)) := fun y ↦ rfl
  have hφV : ∀ y ∈ φ.source, y ∈ c.W ∩ ComplexPoints.chart (sX := X ↘ Spec (.of ℂ)) V := by
    intro y hy
    obtain ⟨hyW, hyE⟩ := (hφsrc y).1 hy
    have := (hEN hyE).2
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply] at this
    refine ⟨hyW, ?_⟩
    have h2 := this.2
    rwa [Set.mem_preimage, e₀.left_inv (hsrc ▸ hyW)] at h2
  refine ⟨n, φ, hn, (hφsrc a).2 ⟨haW, hz₀E⟩, hφV, ?_, fun x hx ↦ ?_, fun w hw ↦ ?_⟩
  · rw [hφapp, hEψ hz₀E]; exact hψ0
  · obtain ⟨hxW, hxV⟩ := hφV x hx
    have hxE := ((hφsrc x).1 hx).2
    rw [hrep x hxW hxV, hrep a haW haV, hφapp, hEψ hxE]
    exact (hEN hxE).1
  · have htgt : ∀ w' ∈ φ.target, w' ∈ E.target ∧ κ.symm (E.symm w') ∈ e₀.target := by
      intro w' hw'
      rw [OpenPartialHomeomorph.trans_target] at hw'
      refine ⟨hw'.1, ?_⟩
      have h2 := hw'.2
      simp only [c', Set.mem_preimage, OpenPartialHomeomorph.transHomeomorph_target] at h2
      exact h2
    have hev : (fun w ↦ e₀ (φ.symm w)) =ᶠ[𝓝 w] fun w ↦ κ.symm (E.symm w) := by
      filter_upwards [φ.open_target.mem_nhds hw] with w' hw'
      have h1 : φ.symm w' = e₀.symm (κ.symm (E.symm w')) := rfl
      rw [h1, e₀.right_inv (htgt w' hw').2]
    refine AnalyticAt.congr ?_ hev.symm
    exact ((κ.symm : ℂ →L[ℂ] (Fin 1 → ℂ)).analyticAt _).comp (hEsymm w (htgt w hw).1)

end MMP.Analytic
