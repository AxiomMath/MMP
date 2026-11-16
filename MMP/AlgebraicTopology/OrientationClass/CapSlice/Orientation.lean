module

public import MMP.AlgebraicTopology.OrientationClass.CapLocalDegree
public import MMP.AlgebraicTopology.OrientationClass.CapComplexBasis
public import MMP.AlgebraicTopology.FundamentalClass.ChartBall
public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Chart
public import MMP.AlgebraicTopology.FundamentalClass.Product

/-!
# The slice map preserves complex orientations (Fulton, §19.1)

Let `U` be a space with one chart `g : U → E'`, `P` a complex manifold modelled on `E` and
`f : U × F → P` an open imbedding which on `Ω = U × ball(0, 1/2)` is
`f (y, w) = e⁻¹(γ (g y) + K w)` for a chart `e` of `P`, a map `γ : E' → E` complex
differentiable at the points of `g U` and a complex linear `K : F → E` with
`γ'(g y) ⊕ K : E' × F ≅ E`. Then `f : Ω ≅ f(Ω)` is orientation preserving from any complex
orientation of `E' × F` to the complex orientation of `E`: in charts it is the holomorphic map
`(z, w) ↦ e₁ (e⁻¹ (γ z + K w))` with bijective complex derivative.

## Main definitions

* `MMP.sliceCore`: the open set `U × ball(0, 1/2)` of `U × F`.
* `MMP.sliceCoreHomeomorph`: `f : Ω ≅ f(Ω)` for an open imbedding `f`.

## Main results

* `MMP.isOrientationPreserving_sliceCoreHomeomorph`.
-/

@[expose] public noncomputable section

open Set Filter Topology Manifold

universe u

namespace MMP

open FundamentalClass ThomClass

section ModelProd

variable {H H' : Type*}

/-- The product norm on `ModelProd H H'`, that of `H × H'`. -/
instance [NormedAddCommGroup H] [NormedAddCommGroup H'] : NormedAddCommGroup (ModelProd H H') :=
  inferInstanceAs (NormedAddCommGroup (H × H'))

/-- `ModelProd H H'` is a real normed space, as `H × H'` is. -/
instance [NormedAddCommGroup H] [NormedAddCommGroup H'] [NormedSpace ℝ H] [NormedSpace ℝ H'] :
    NormedSpace ℝ (ModelProd H H') :=
  inferInstanceAs (NormedSpace ℝ (H × H'))

/-- `ModelProd H H'` is finite dimensional over `ℝ` when `H` and `H'` are. -/
instance [NormedAddCommGroup H] [NormedAddCommGroup H'] [NormedSpace ℝ H] [NormedSpace ℝ H']
    [FiniteDimensional ℝ H] [FiniteDimensional ℝ H'] : FiniteDimensional ℝ (ModelProd H H') :=
  inferInstanceAs (FiniteDimensional ℝ (H × H'))

end ModelProd

section SliceCore

variable (U : Type u) [TopologicalSpace U] (F : Type u) [NormedAddCommGroup F]

/-- The open set `U × ball(0, 1/2)` of `U × F`. -/
def sliceCore : TopologicalSpace.Opens (U × F) :=
  ⟨{p | ‖p.2‖ < 1 / 2}, isOpen_lt (continuous_norm.comp continuous_snd) continuous_const⟩

variable {U F} {P : Type u} [TopologicalSpace P] {f : U × F → P}

/-- The image `f(U × ball(0, 1/2))` under an open imbedding, an open set of `P`. -/
def sliceCoreImage (hf : IsOpenEmbedding f) : TopologicalSpace.Opens P :=
  ⟨f '' (sliceCore U F), hf.isOpenMap _ (sliceCore U F).isOpen⟩

/-- The homeomorphism `U × ball(0, 1/2) ≅ f(U × ball(0, 1/2))` induced by an open imbedding
`f`. -/
def sliceCoreHomeomorph (hf : IsOpenEmbedding f) : sliceCore U F ≃ₜ sliceCoreImage hf :=
  (hf.isEmbedding.comp IsEmbedding.subtypeVal).toHomeomorph.trans
    (Homeomorph.setCongr (by rw [range_comp, Subtype.range_coe]; rfl))

/-- The point `sliceCoreHomeomorph hf p` of `P` is `f p`. -/
@[simp]
lemma coe_sliceCoreHomeomorph_apply (hf : IsOpenEmbedding f) (p : sliceCore U F) :
    (sliceCoreHomeomorph hf p : P) = f p :=
  rfl

end SliceCore

section SliceOrientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : Type u} [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℂ, E) 1 P]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {U : Type u} [TopologicalSpace U] [ChartedSpace E' U]

/-- **The slice map preserves complex orientations**. Let `U` have the single chart `g`, and
`f : U × F → P` be an open imbedding into the complex manifold `P` with
`f (y, w) = e⁻¹(γ (g y) + K w)` on `U × ball(0, 1/2)`, for a chart `e` of `P`, a map `γ` complex
differentiable at `g y` with `γ'(g y) ⊕ K` bijective. Then
`f : U × ball(0, 1/2) ≅ f(U × ball(0, 1/2))` is orientation preserving from every basis `b` of
`E' × F` for which complex linear isomorphisms `E' × F ≅ E` have positive determinant (for
instance `b = complexRealBasis c`, `complexRealBasis_det_pos`) to the complex orientation of
`E`. -/
theorem isOrientationPreserving_sliceCoreHomeomorph {f : U × F → P} (hf : IsOpenEmbedding f)
    (g : OpenPartialHomeomorph U E') (hatlas : ∀ c ∈ atlas E' U, c = g)
    {e : OpenPartialHomeomorph P E} (he : e ∈ atlas E P) {γ : E' → E} (K : F →L[ℂ] E)
    (hfe : ∀ y w, ‖w‖ < 1 / 2 → γ (g y) + K w ∈ e.target ∧ f (y, w) = e.symm (γ (g y) + K w))
    (hγ : ∀ y, DifferentiableAt ℂ γ (g y) ∧
      Function.Bijective ((fderiv ℂ γ (g y)).coprod K))
    (b : Module.Basis (Fin (2 * Module.finrank ℂ E)) ℝ (ModelProd E' F))
    (hb : ∀ L : (E' × F) →ₗ[ℂ] E, Function.Injective L →
      0 < (complexOrientationBasisOf E).det ((L.restrictScalars ℝ) ∘ b)) :
    IsOrientationPreserving b (complexOrientationBasisOf E) (sliceCoreHomeomorph hf) := by
  apply isOrientationPreserving_of_hasFDerivAt
  rintro e₂ ⟨_, ⟨p, rfl⟩, he₂⟩ e₁ ⟨_, ⟨q, rfl⟩, he₁⟩ x hx hx'
  rw [mem_singleton_iff] at he₂ he₁
  subst he₂ he₁
  set c₂ := chartAt (ModelProd E' F) (p : U × F)
  set c₁ := chartAt E (q : P)
  have hc : c₂ = g.prod (OpenPartialHomeomorph.refl F) := by
    change (chartAt E' (p : U × F).1).prod (chartAt F (p : U × F).2) = _
    rw [hatlas _ (chart_mem_atlas _ _), chartAt_self_eq]
  obtain ⟨⟨y₀, w₀⟩, hw₀⟩ := x
  have hw₀' : ‖w₀‖ < 1 / 2 := hw₀
  have hx₂ : (c₂.subtypeRestr ⟨p⟩) ⟨(y₀, w₀), hw₀⟩ = (g y₀, w₀) := by
    change c₂ (y₀, w₀) = _
    rw [hc]
    rfl
  obtain ⟨hv₀, hfv₀⟩ := hfe y₀ w₀ hw₀'
  set v₀ := γ (g y₀) + K w₀
  have hfx : f (y₀, w₀) ∈ c₁.source := by
    have h := hx'
    rw [OpenPartialHomeomorph.subtypeRestr_source] at h
    exact h
  have hsv₀ : e.symm v₀ ∈ e.source := e.map_target hv₀
  set T : E → E := fun v ↦ c₁ (e.symm v)
  set G : E' × F → E := fun z ↦ γ z.1 + K z.2
  have hT := (contDiffAt_chart_transition he (chart_mem_atlas E (q : P)) hsv₀
    (by rw [← hfv₀]; exact hfx)).differentiableAt one_ne_zero
  rw [e.right_inv hv₀] at hT
  have hTi := injective_fderiv_chart_transition he (chart_mem_atlas E (q : P)) hsv₀
    (by rw [← hfv₀]; exact hfx)
  rw [e.right_inv hv₀] at hTi
  have hG : HasFDerivAt G ((fderiv ℂ γ (g y₀)).coprod K) (g y₀, w₀) := by
    rw [show (fderiv ℂ γ (g y₀)).coprod K = (fderiv ℂ γ (g y₀)).comp
      (ContinuousLinearMap.fst ℂ E' F) + K.comp (ContinuousLinearMap.snd ℂ E' F) from
      ContinuousLinearMap.ext fun _ ↦ rfl]
    exact ((hγ y₀).1.hasFDerivAt.comp (g y₀, w₀) hasFDerivAt_fst).add
      (K.hasFDerivAt.comp (g y₀, w₀) hasFDerivAt_snd)
  set D : (E' × F) →L[ℂ] E := (fderiv ℂ T v₀).comp ((fderiv ℂ γ (g y₀)).coprod K)
  have hTG : HasFDerivAt (T ∘ G) D (g y₀, w₀) := hT.hasFDerivAt.comp (g y₀, w₀) hG
  have hDi : Function.Injective D := hTi.comp (hγ y₀).2.1
  refine ⟨D.restrictScalars ℝ, ?_, hb (D : (E' × F) →ₗ[ℂ] E) hDi⟩
  rw [hx₂]
  refine (hTG.restrictScalars ℝ).congr_of_eventuallyEq ?_
  have hmem : (g y₀, w₀) ∈ (c₂.subtypeRestr ⟨p⟩).target := by
    rw [← hx₂]
    exact (c₂.subtypeRestr ⟨p⟩).map_source hx
  filter_upwards [(c₂.subtypeRestr ⟨p⟩).open_target.mem_nhds hmem] with z hz
  have hs := coe_subtypeRestr_symm_apply c₂ ⟨p⟩ hz
  have hzt : z ∈ c₂.target := by
    have h := hz
    rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target] at h
    exact h.1
  rw [hc, OpenPartialHomeomorph.prod_target] at hzt
  have hΩ : ‖((c₂.subtypeRestr ⟨p⟩).symm z : U × F).2‖ < 1 / 2 :=
    ((c₂.subtypeRestr ⟨p⟩).symm z).2
  rw [hs, hc] at hΩ
  change ‖z.2‖ < 1 / 2 at hΩ
  change c₁ (f (((c₂.subtypeRestr ⟨p⟩).symm z : U × F))) = c₁ (e.symm (γ z.1 + K z.2))
  rw [hs, hc]
  change c₁ (f (g.symm z.1, z.2)) = _
  rw [(hfe (g.symm z.1) z.2 hΩ).2, g.right_inv hzt.1]

end SliceOrientation

end MMP
