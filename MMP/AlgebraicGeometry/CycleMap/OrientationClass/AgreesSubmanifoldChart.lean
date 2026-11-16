module

public import MMP.AlgebraicTopology.OrientationClass.AgreesSubmanifold
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AgreesSubmanifoldRank

/-!
# Chart lemmas for the orientation class of a regular imbedding of non-singular schemes

Bundle-agnostic ingredients of the disc criterion for the orientation class of a regular
imbedding `X ⊆ Y` of non-singular complex schemes: they mention neither the vector bundle `E`
with its section `s` nor the regularity of the imbedding, and serve both Fulton-style vector
bundles and the Stacks vector bundles `𝐕(ℰ)`.

## Main definitions

* `MMP.IsNonsingularPair`: `Y(ℂ)` has an atlas of algebraic charts modelled on `E`, the local
  rings of `Y` at complex points are regular of dimension `dim E`, those of `X` regular.

## Main results

* `MMP.hasFDerivAt_apply_of_continuousAt_of_eq_zero`: the derivative of
  `k ↦ M(k) (w k)` at a zero of `w`, for `M` only continuous.
* `MMP.chartDeriv_restrict`: the differential of a restriction is the differential of the
  section.
* `MMP.finrank_add_of_isCompl`: the real dimension count of a transversal frame.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Filter Topology Asymptotics

namespace MMP

section Analysis

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- **Derivative of `M(k) (w k)` at a zero of `w`, for `M` only continuous.** If `w` is
differentiable at `z` with `w z = 0` and `M` is continuous at `z`, then `k ↦ M(k) (w k)` is
differentiable at `z`, with derivative `M(z) ∘ Dw`. -/
theorem hasFDerivAt_apply_of_continuousAt_of_eq_zero {Mf : E → G →L[𝕜] H} {w : E → G}
    {Dw : E →L[𝕜] G} {z : E} (hM : ContinuousAt Mf z) (hw : HasFDerivAt w Dw z) (hw0 : w z = 0) :
    HasFDerivAt (fun k ↦ Mf k (w k)) ((Mf z).comp Dw) z := by
  have h1 : HasFDerivAt (fun k ↦ Mf z (w k)) ((Mf z).comp Dw) z := (Mf z).hasFDerivAt.comp z hw
  have h2 : HasFDerivAt (fun k ↦ (Mf k - Mf z) (w k)) (0 : E →L[𝕜] H) z := by
    refine HasFDerivAt.of_isLittleO ?_
    simp only [sub_self, ContinuousLinearMap.zero_apply, sub_zero, hw0, map_zero]
    obtain ⟨C, hC, hCw⟩ := hw.isBigO_sub.exists_pos
    rw [IsLittleO]
    intro c hc
    rw [IsBigOWith] at hCw
    have hMz : ∀ᶠ k in 𝓝 z, ‖Mf k - Mf z‖ ≤ c / C := by
      have ht : Tendsto (fun k ↦ Mf k - Mf z) (𝓝 z) (𝓝 0) :=
        tendsto_sub_nhds_zero_iff.2 hM.tendsto
      exact (ht.norm.eventually (ge_mem_nhds (by simpa using div_pos hc hC)))
    refine IsBigOWith.of_bound ?_
    filter_upwards [hMz, hCw] with k hk hk'
    rw [hw0, sub_zero] at hk'
    calc ‖(Mf k - Mf z) (w k)‖ ≤ ‖Mf k - Mf z‖ * ‖w k‖ := (Mf k - Mf z).le_opNorm _
      _ ≤ c / C * (C * ‖k - z‖) := by gcongr
      _ = c * ‖k - z‖ := by field_simp
  have h := h1.add h2
  rw [add_zero] at h
  convert h using 1
  ext k
  simp

end Analysis

open UnderlyingSpace

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]

section Differential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {e : OpenPartialHomeomorph (UnderlyingSpace ℂ Y) E}

/-- The differential of a restriction is the differential of the section. -/
lemma chartDeriv_restrict {V W : Y.Opens} (h : W ≤ V) {p : UnderlyingSpace ℂ Y}
    (hp : p ∈ e.source) (hpW : ⊤ ≤ p.toHom ⁻¹ᵁ W) (a : Γ(Y, V)) :
    chartDeriv e W p (Y.presheaf.map (homOfLE h).op a) = chartDeriv e V p a := by
  have heq : (fun k ↦ evalExt W (Y.presheaf.map (homOfLE h).op a) (e.symm k)) =ᶠ[𝓝 (e p)]
      fun k ↦ evalExt V a (e.symm k) := by
    filter_upwards [eventually_mem_target_and_le hp hpW] with k hk
    rw [evalExt_of_le _ hk.2, eval_restrict, evalExt_of_le]
  rw [chartDeriv, heq.fderiv_eq]
  rfl

end Differential

section Agrees

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- The real dimension count of a transversal frame: if `L : ℂ^d → E` is a real linear injection
whose image is complementary to a complex subspace `W` of `E`, then `dim W + d = dim E`. -/
lemma finrank_add_of_isCompl {d : ℕ} (L : (Fin d → ℂ) →L[ℝ] E) (hinj : Function.Injective L)
    (W : Submodule ℂ E)
    (hc : IsCompl (LinearMap.range (L : (Fin d → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ)) :
    Module.finrank ℂ W + d = Module.finrank ℂ E := by
  have h1 := Submodule.finrank_add_eq_of_isCompl hc
  have h2 : Module.finrank ℝ (LinearMap.range (L : (Fin d → ℂ) →ₗ[ℝ] E)) = 2 * d := by
    rw [LinearMap.finrank_range_of_inj hinj, finrank_real_of_complex,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have h3 : Module.finrank ℝ (W.restrictScalars ℝ) = 2 * Module.finrank ℂ W :=
    finrank_real_of_complex W
  rw [h2, h3, finrank_real_of_complex E] at h1
  omega

/-- The non-singularity hypotheses of `IsRegularImbeddingOrientationClass.isOrientationClass`:
`Y(ℂ)` has an atlas of algebraic charts modelled on `E`, the local rings of `Y` are regular of
dimension `dim E`, and those of `X` are regular. -/
structure IsNonsingularPair (i : X ⟶ Y) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [ChartedSpace E (UnderlyingSpace ℂ Y)] : Prop where
  /-- Every chart of the atlas of `Y(ℂ)` is algebraic. -/
  isAlgebraicChart : ∀ e ∈ atlas E (UnderlyingSpace ℂ Y), IsAlgebraicChart e
  /-- The local ring of `Y` at each `ℂ`-point is regular of dimension `dim E`. -/
  regular_Y : ∀ y : UnderlyingSpace ℂ Y,
    IsRegularLocalRing (Y.presheaf.stalk (y.toHom (IsLocalRing.closedPoint ℂ))) ∧
      ringKrullDim (Y.presheaf.stalk (y.toHom (IsLocalRing.closedPoint ℂ))) = Module.finrank ℂ E
  /-- The local ring of `X` at each `ℂ`-point is regular. -/
  regular_X : ∀ x : UnderlyingSpace ℂ X,
    IsRegularLocalRing (X.presheaf.stalk (x.toHom (IsLocalRing.closedPoint ℂ)))

end Agrees

end MMP
