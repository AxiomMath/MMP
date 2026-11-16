module

public import MMP.AlgebraicTopology.ComplexSubmanifold
public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Analysis
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Chart transitions of a complex manifold (Fulton, §19.1)

For a complex manifold `P` (Mathlib's `IsManifold 𝓘(ℂ, E) 1 P`) and charts `e`, `e₂` of `P`
defined at `p`, the transition `v ↦ e₂ (e⁻¹ v)` is `C¹` over `ℂ` at `e p`, with invertible
derivative. These are the facts about the ambient manifold used by the slice parametrization of a
complex submanifold (step (A) of `lem_ext_c19_orientation_class_cap_fundamental`).

## Main results

* `MMP.contDiffAt_chart_transition`.
* `MMP.injective_fderiv_chart_transition`.
* `MMP.exists_injective_isCompl_range`, `MMP.finrank_add_finrank_of_isCompl`:
  complex complements of the tangent space and their dimension.
* `MMP.exists_hasFDerivAt_sliceDisc`: the fibre discs `w ↦ e⁻¹(e y + K ρ(ψ w))`
  of a slice parametrization are transversal discs of the complex submanifold `M`.
-/

@[expose] public noncomputable section

open Set Filter Topology Manifold

namespace MMP

open MMP

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {P : Type*} [TopologicalSpace P]
  [ChartedSpace E P] [IsManifold 𝓘(ℂ, E) 1 P]

/-- In a complex manifold, the transition `v ↦ e₂ (e⁻¹ v)` between two charts defined at `p` is
`C¹` over `ℂ` at `e p`. -/
theorem contDiffAt_chart_transition {e e₂ : OpenPartialHomeomorph P E} (he : e ∈ atlas E P)
    (he₂ : e₂ ∈ atlas E P) {p : P} (hp : p ∈ e.source) (hp₂ : p ∈ e₂.source) :
    ContDiffAt ℂ 1 (fun v ↦ e₂ (e.symm v)) (e p) := by
  have h := (contDiffGroupoid 1 𝓘(ℂ, E)).compatible he he₂
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  have h1 : ContDiffOn ℂ 1 (e.symm.trans e₂) (e.symm.trans e₂).source := by
    simpa [contDiffPregroupoid] using h.1
  have hmem : e p ∈ (e.symm.trans e₂).source := by
    rw [OpenPartialHomeomorph.trans_source]
    exact ⟨e.map_source hp, by rwa [mem_preimage, e.left_inv hp]⟩
  exact h1.contDiffAt ((e.symm.trans e₂).open_source.mem_nhds hmem)

/-- In a complex manifold, the derivative of the transition `v ↦ e₂ (e⁻¹ v)` at `e p` is
injective (it is invertible, with inverse the derivative of the inverse transition). -/
theorem injective_fderiv_chart_transition {e e₂ : OpenPartialHomeomorph P E}
    (he : e ∈ atlas E P) (he₂ : e₂ ∈ atlas E P) {p : P} (hp : p ∈ e.source)
    (hp₂ : p ∈ e₂.source) :
    Function.Injective (fderiv ℂ (fun v ↦ e₂ (e.symm v)) (e p)) := by
  have h1 := (contDiffAt_chart_transition he he₂ hp hp₂).differentiableAt one_ne_zero
  have h2 := (contDiffAt_chart_transition he₂ he hp₂ hp).differentiableAt one_ne_zero
  have hτ : (fun v ↦ e₂ (e.symm v)) (e p) = e₂ p := by simp [e.left_inv hp]
  rw [← hτ] at h2
  have hid : (fun v ↦ e (e₂.symm v)) ∘ (fun v ↦ e₂ (e.symm v)) =ᶠ[𝓝 (e p)] id := by
    filter_upwards [(e.isOpen_inter_preimage_symm e₂.open_source).mem_nhds
      ⟨e.map_source hp, by rwa [mem_preimage, e.left_inv hp]⟩] with v hv
    simp only [Function.comp_apply, id_eq]
    rw [e₂.left_inv hv.2, e.right_inv hv.1]
  have huniq := ((h2.hasFDerivAt.comp (e p) h1.hasFDerivAt).congr_of_eventuallyEq
    hid.symm).unique (hasFDerivAt_id (e p))
  exact Function.LeftInverse.injective fun a ↦ by simpa using DFunLike.congr_fun huniq a

section Complement

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [FiniteDimensional ℂ E]

/-- A complex subspace `W` of `E` of codimension `dim F` has a complement which is the image of
an injective complex linear map `K : F → E`. -/
theorem exists_injective_isCompl_range (W : Submodule ℂ E)
    (h : Module.finrank ℂ F + Module.finrank ℂ W = Module.finrank ℂ E) :
    ∃ K : F →L[ℂ] E, Function.Injective K ∧ IsCompl W (LinearMap.range (K : F →ₗ[ℂ] E)) := by
  obtain ⟨C, hC⟩ := W.exists_isCompl
  have hfin : Module.finrank ℂ F = Module.finrank ℂ C := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    omega
  let φ : F ≃ₗ[ℂ] C := LinearEquiv.ofFinrankEq F C hfin
  refine ⟨LinearMap.toContinuousLinearMap (C.subtype ∘ₗ (φ : F →ₗ[ℂ] C)),
    fun a b hab ↦ φ.injective (Subtype.ext hab), ?_⟩
  simpa [LinearMap.range_comp] using hC

/-- If an injective real linear map `L : ℂ^d → E` has image complementary to the complex
subspace `W`, then `W` has complex codimension `d`. -/
theorem finrank_add_finrank_of_isCompl {d : ℕ} {L : (Fin d → ℂ) →L[ℝ] E}
    (hL : Function.Injective L) {W : Submodule ℂ E}
    (hc : IsCompl (LinearMap.range (L : (Fin d → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ)) :
    d + Module.finrank ℂ W = Module.finrank ℂ E := by
  have h1 := Submodule.finrank_add_eq_of_isCompl hc
  rw [LinearMap.finrank_range_of_inj hL, finrank_real_of_complex (Fin d → ℂ),
    finrank_real_of_complex E] at h1
  have h2 : Module.finrank ℝ (W.restrictScalars ℝ) = 2 * Module.finrank ℂ W :=
    finrank_real_of_complex _
  rw [h2, Module.finrank_fin_fun] at h1
  omega

end Complement

section Disc

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] {M : Set P} [ChartedSpace E' M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The chain rule for charts of a subset `M ⊆ P`: if `e'` is a chart of `M` and `e`, `c` are
charts of `P` at `y ∈ M`, the derivative of `c ∘ e'⁻¹` at `e' y` is the derivative of the
transition `c ∘ e⁻¹` at `e y` composed with the derivative of `e ∘ e'⁻¹`. -/
theorem fderiv_chart_comp_symm_eq_comp {e' : OpenPartialHomeomorph M E'}
    {e c : OpenPartialHomeomorph P E} (he : e ∈ atlas E P) (hc : c ∈ atlas E P) {y : M}
    (hy' : y ∈ e'.source) (hy : (y : P) ∈ e.source) (hyc : (y : P) ∈ c.source)
    (hg : DifferentiableAt ℂ (fun z ↦ e (e'.symm z : P)) (e' y)) :
    fderiv ℂ (fun z ↦ c (e'.symm z : P)) (e' y) =
      (fderiv ℂ (fun v ↦ c (e.symm v)) (e y)).comp
        (fderiv ℂ (fun z ↦ e (e'.symm z : P)) (e' y)) := by
  have hyt : e' y ∈ e'.target := e'.map_source hy'
  have hsy : e'.symm (e' y) = y := e'.left_inv hy'
  set T := fderiv ℂ (fun v ↦ c (e.symm v)) (e y)
  have hτ : HasFDerivAt (fun v ↦ c (e.symm v)) T (e y) :=
    ((contDiffAt_chart_transition he hc hy hyc).differentiableAt one_ne_zero).hasFDerivAt
  have hgy : (fun z ↦ e (e'.symm z : P)) (e' y) = e y := by simp only [hsy]
  rw [← hgy] at hτ
  refine ((hτ.comp (e' y) hg.hasFDerivAt).congr_of_eventuallyEq ?_).fderiv
  have h1 : ∀ᶠ z in 𝓝 (e' y), ((e'.symm z : M) : P) ∈ e.source := by
    refine (continuous_subtype_val.continuousAt.comp (e'.continuousAt_symm hyt)).preimage_mem_nhds
      ?_
    simp only [Function.comp_apply, hsy]
    exact e.open_source.mem_nhds hy
  filter_upwards [h1] with z hz
  simp only [Function.comp_apply, e.left_inv hz]

/-- The disc `w ↦ τ (x + K (ρ (ψ w)))` has real derivative `T ∘ K ∘ ψ` at `0`, when `τ` has
complex derivative `T` at `x`, `ρ 0 = 0` and `ρ` has derivative the identity at `0`. -/
theorem hasFDerivAt_comp_add_comp {τ : E → E} {T : E →L[ℂ] E} {x : E} (hτ : HasFDerivAt τ T x)
    (K : F →L[ℂ] E) {ρ : F → F} (hρ : HasFDerivAt ρ (ContinuousLinearMap.id ℝ F) 0)
    (hρ0 : ρ 0 = 0) {r : ℕ} (ψ : (Fin r → ℂ) ≃L[ℂ] F) :
    HasFDerivAt (fun w ↦ τ (x + K (ρ (ψ w))))
      ((T.comp (K.comp (ψ : (Fin r → ℂ) →L[ℂ] F))).restrictScalars ℝ) 0 := by
  have hin : HasFDerivAt (fun w : Fin r → ℂ ↦ x + K (ρ (ψ w)))
      ((K.restrictScalars ℝ).comp ((ContinuousLinearMap.id ℝ F).comp
        ((ψ : (Fin r → ℂ) →L[ℂ] F).restrictScalars ℝ))) 0 := by
    have hρ' : HasFDerivAt ρ (ContinuousLinearMap.id ℝ F) (ψ 0) := by rwa [map_zero]
    exact ((K.restrictScalars ℝ).hasFDerivAt.comp 0
      (hρ'.comp 0 ((ψ : (Fin r → ℂ) →L[ℂ] F).restrictScalars ℝ).hasFDerivAt)).const_add x
  have hin0 : x + K (ρ (ψ 0)) = x := by simp [hρ0]
  have hτR : HasFDerivAt τ (T.restrictScalars ℝ) (x + K (ρ (ψ 0))) := by
    rw [hin0]
    exact hτ.restrictScalars ℝ
  exact hτR.comp 0 hin

/-- **The fibre discs of a slice parametrization are transversal discs.** Let `M ⊆ P` be a
complex submanifold, `e'` a chart of `M` and `e` a chart of `P`, both defined at `y ∈ M`, and
`K : F → E` complex linear and injective with image complementary to the image of the derivative
`g'(e' y)` of `g = e ∘ e'⁻¹`. For `ρ : F → F` with `ρ 0 = 0` and derivative the identity at `0`,
and a complex frame `ψ : ℂ^r ≅ F`, the disc `w ↦ e⁻¹(e y + K (ρ (ψ w)))` through `y` is
differentiable at `0` in the chart of `P` at `y`, with an injective derivative `L`, complex
linear, whose image is complementary to the tangent cone `W` of `M` at `y`. -/
theorem exists_hasFDerivAt_sliceDisc [FiniteDimensional ℂ E] (hM : IsComplexSubmanifold E E' M)
    {e' : OpenPartialHomeomorph M E'} (he' : e' ∈ atlas E' M) {e : OpenPartialHomeomorph P E}
    (he : e ∈ atlas E P) {y : M} (hy' : y ∈ e'.source) (hy : (y : P) ∈ e.source)
    (K : F →L[ℂ] E) (hK : Function.Injective K)
    (hc : IsCompl (LinearMap.range (fderiv ℂ (fun z ↦ e (e'.symm z : P)) (e' y) : E' →ₗ[ℂ] E))
      (LinearMap.range (K : F →ₗ[ℂ] E)))
    {ρ : F → F} (hρ : HasFDerivAt ρ (ContinuousLinearMap.id ℝ F) 0) (hρ0 : ρ 0 = 0) {r : ℕ}
    (ψ : (Fin r → ℂ) ≃L[ℂ] F) :
    ∃ L : (Fin r → ℂ) →L[ℝ] E,
      HasFDerivAt (fun w ↦ chartAt E (y : P) (e.symm (e y + K (ρ (ψ w))))) L 0 ∧
      Function.Injective L ∧
      ∃ W : Submodule ℂ E,
        tangentConeAt ℝ (chartAt E (y : P) '' (M ∩ (chartAt E (y : P)).source))
          (chartAt E (y : P) y) = W ∧
        IsCompl (LinearMap.range (L : (Fin r → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ) ∧
        ∀ (c : ℂ) (v : Fin r → ℂ), L (c • v) - c • L v ∈ W := by
  set c₂ := chartAt E (y : P)
  have hy₂ : (y : P) ∈ c₂.source := mem_chart_source E (y : P)
  set T := fderiv ℂ (fun v ↦ c₂ (e.symm v)) (e y)
  have hτ : HasFDerivAt (fun v ↦ c₂ (e.symm v)) T (e y) :=
    ((contDiffAt_chart_transition he (chart_mem_atlas E (y : P)) hy hy₂).differentiableAt
      one_ne_zero).hasFDerivAt
  have hTi : Function.Injective T := injective_fderiv_chart_transition he
    (chart_mem_atlas E (y : P)) hy hy₂
  have hyt : e' y ∈ e'.target := e'.map_source hy'
  have hsy : e'.symm (e' y) = y := e'.left_inv hy'
  obtain ⟨hgc, -⟩ := hM e' he' e he (e' y) hyt (by rwa [hsy])
  obtain ⟨hdc, hdi⟩ := hM e' he' c₂ (chart_mem_atlas E (y : P)) (e' y) hyt (by rwa [hsy])
  set Dg := fderiv ℂ (fun z ↦ e (e'.symm z : P)) (e' y)
  set Dc := fderiv ℂ (fun z ↦ c₂ (e'.symm z : P)) (e' y)
  have hdc' : HasFDerivAt (fun z ↦ c₂ (e'.symm z : P)) Dc (e' y) :=
    (hdc.differentiableAt one_ne_zero).hasFDerivAt
  have hDc : Dc = T.comp Dg := fderiv_chart_comp_symm_eq_comp he (chart_mem_atlas E (y : P)) hy'
    hy hy₂ (hgc.differentiableAt one_ne_zero)
  set L₀ : (Fin r → ℂ) →L[ℂ] E := T.comp (K.comp (ψ : (Fin r → ℂ) →L[ℂ] F))
  refine ⟨L₀.restrictScalars ℝ, hasFDerivAt_comp_add_comp hτ K hρ hρ0 ψ,
    fun _ _ hab ↦ ψ.injective (hK (hTi hab)), LinearMap.range (Dc : E' →ₗ[ℂ] E),
    tangentConeAt_image_chart_eq_range hy' hy₂ hdc' (hDc ▸ hdi), ?_, ?_⟩
  · have hbij : Function.Bijective T :=
      ⟨hTi, LinearMap.surjective_of_injective (f := (T : E →ₗ[ℂ] E)) hTi⟩
    set Te : E ≃ₗ[ℂ] E := LinearEquiv.ofBijective (T : E →ₗ[ℂ] E) hbij
    have h1 : LinearMap.range ((L₀.restrictScalars ℝ : (Fin r → ℂ) →L[ℝ] E) :
        (Fin r → ℂ) →ₗ[ℝ] E) =
        ((LinearMap.range (K : F →ₗ[ℂ] E)).map (Te : E →ₗ[ℂ] E)).restrictScalars ℝ := by
      ext v
      simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, Submodule.restrictScalars_mem,
        Submodule.mem_map]
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨K (ψ w), ⟨ψ w, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        exact ⟨ψ.symm w, by simp [L₀, Te]⟩
    have h2 : LinearMap.range (Dc : E' →ₗ[ℂ] E) =
        (LinearMap.range (Dg : E' →ₗ[ℂ] E)).map (Te : E →ₗ[ℂ] E) := by
      rw [hDc]
      exact LinearMap.range_comp (Dg : E' →ₗ[ℂ] E) (T : E →ₗ[ℂ] E)
    rw [h1, h2]
    exact (Submodule.isCompl_restrictScalars_iff ℝ).mpr (Submodule.isCompl_map Te hc.symm)
  · intro c v
    simp [L₀, map_smul]

end Disc

end MMP
