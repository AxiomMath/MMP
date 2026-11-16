module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Complex submanifolds of a complex manifold (Fulton, §19.1)

A subset `M` of a complex manifold `P` (modelled on `E`), itself a charted space modelled on
`E'`, is a *complex submanifold* when its inclusion is a holomorphic immersion in the charts: for
every chart `e'` of `M` and every chart `e` of `P`, the transition `z ↦ e (e'⁻¹ z)` is complex
differentiable with an injective derivative wherever it is defined. Since `M` carries the subspace
topology and its charts are homeomorphisms onto open subsets of `E'`, the inclusion is then a
holomorphic immersion which is a topological imbedding, i.e. `M` is an imbedded complex
submanifold of `P`.

This is what fixes the orientation of `M` relative to that of `P`: with the conjugate complex
structure on `M` (charts `z ↦ conj (e' z)`) the fundamental class `μ_M` changes sign by
`(-1)^{dim M}`, while the orientation class `u_{M,P}` and `μ_P` do not.

## Main definitions

* `MMP.IsComplexSubmanifold`: the inclusion `M ⊆ P` is holomorphic (`C¹` over
  `ℂ`) with injective derivative in every pair of charts.

## Main results

* `MMP.tangentConeAt_image_eq_range`: the tangent cone at `f y` of the image of a
  neighbourhood of `y` under a map differentiable at `y` with injective derivative `L`, which is a
  homeomorphism onto its image near `y`, is the range of `L`.
* `MMP.tangentConeAt_image_chart_eq_range`: in any pair of charts `e'` of `M`
  and `e` of `P` at `x`, the tangent cone of `M` at `x` in `e` is the range of the derivative of
  `e ∘ e'⁻¹` at `e' x`.
* `MMP.IsComplexSubmanifold.exists_tangentConeAt_eq`: for a complex submanifold
  `M`, the tangent cone of `M` at `x` in the chart of `P` at `x` is (the underlying set of) a
  complex subspace `W` of `E` (the subspace `W` of `TubularNeighbourhood.IsOrientationCompatible`).
-/

@[expose] public noncomputable section

open Set Filter Topology Asymptotics

namespace MMP

section TangentCone

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [FiniteDimensional ℝ E]

/-- If `f` has injective derivative `L` at `y` and is a homeomorphism onto its image near `y` on
`O`, then the tangent cone of `f '' O` at `f y` lies in the range of `L`. -/
theorem tangentConeAt_image_subset_range {f : E' → E} {L : E' →L[ℝ] E} {O : Set E'} {y : E'}
    (hf : HasFDerivAt f L y) (hL : Function.Injective L)
    (hinv : comap f (𝓝 (f y)) ⊓ 𝓟 O ≤ 𝓝 y) :
    tangentConeAt ℝ (f '' O) (f y) ⊆ range L := by
  intro w hw
  obtain ⟨K₀, hK₀⟩ := (L : E' →ₗ[ℝ] E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hL)
  let K : E →L[ℝ] E' := LinearMap.toContinuousLinearMap K₀
  have hKL : ∀ v, K (L v) = v := fun v ↦ congrArg (fun g : E' →ₗ[ℝ] E' ↦ g v) hK₀
  let Q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - L.comp K
  have hQL : ∀ v, Q (L v) = 0 := fun v ↦ by simp [Q, hKL]
  obtain ⟨α, l, hl, c, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hw
  have hex : ∀ᶠ n in l, ∃ z ∈ O, f z = f y + d n := hds.mono fun n hn ↦ hn
  choose! z hzO hfz using fun n (h : ∃ z ∈ O, f z = f y + d n) ↦ h
  have hzO' : ∀ᶠ n in l, z n ∈ O := hex.mono fun n hn ↦ hzO n hn
  have hfz' : ∀ᶠ n in l, f (z n) = f y + d n := hex.mono fun n hn ↦ hfz n hn
  have hfzt : Tendsto (f ∘ z) l (𝓝 (f y)) := by
    have : Tendsto (fun n ↦ f y + d n) l (𝓝 (f y)) := by
      simpa using tendsto_const_nhds.add hd0
    exact this.congr' (hfz'.mono fun n hn ↦ hn.symm)
  have hzt : Tendsto z l (𝓝 y) :=
    (tendsto_inf.2 ⟨tendsto_comap_iff.2 hfzt, tendsto_principal.2 hzO'⟩).mono_right hinv
  set u : α → E' := fun n ↦ z n - y
  set r : α → E := fun n ↦ f (z n) - f y - L (u n)
  have hr : r =o[l] u := hf.isLittleO.comp_tendsto hzt
  have hdr : ∀ᶠ n in l, d n = L (u n) + r n := hfz'.mono fun n hn ↦ by
    simp only [r, hn]; abel
  have hu : u =O[l] d := by
    have h1 : (fun n ↦ K (r n)) =o[l] u := (K.isBigO_comp r l).trans_isLittleO hr
    refine h1.right_isBigO_add.trans
      ((K.isBigO_comp d l).congr' (hdr.mono fun n hn ↦ ?_) EventuallyEq.rfl)
    simp [hn, map_add, hKL, add_comm]
  have hrd : r =o[l] d := hr.trans_isBigO hu
  have hcr : (fun n ↦ c n • r n) =o[l] (fun _ ↦ (1 : ℝ)) :=
    ((isBigO_refl c l).smul_isLittleO hrd).trans_isBigO (hcd.isBigO_one ℝ)
  have hQ1 : Tendsto (fun n ↦ Q (c n • d n)) l (𝓝 (Q w)) := (Q.continuous.tendsto w).comp hcd
  have hQ2 : Tendsto (fun n ↦ Q (c n • d n)) l (𝓝 0) := by
    have h0 : Tendsto (fun n ↦ Q (c n • r n)) l (𝓝 0) := by
      simpa [Function.comp_def] using
        (Q.continuous.tendsto 0).comp (isLittleO_one_iff ℝ |>.1 hcr)
    refine h0.congr' (hdr.mono fun n hn ↦ ?_)
    simp only [hn, smul_add, map_add, map_smul, hQL, smul_zero, zero_add]
  have hQw : Q w = 0 := tendsto_nhds_unique hQ1 hQ2
  exact ⟨K w, (sub_eq_zero.1 (show w - L (K w) = 0 by simpa [Q] using hQw)).symm⟩

/-- **Tangent cone of an immersed image.** Let `f` be differentiable at `y` with injective
derivative `L`, and a homeomorphism onto its image near `y` on the neighbourhood `O` of `y` (points
of `O` whose images tend to `f y` tend to `y`). Then the tangent cone of `f '' O` at `f y` is the
range of `L`. -/
theorem tangentConeAt_image_eq_range {f : E' → E} {L : E' →L[ℝ] E} {O : Set E'} {y : E'}
    (hO : O ∈ 𝓝 y) (hf : HasFDerivAt f L y) (hL : Function.Injective L)
    (hinv : comap f (𝓝 (f y)) ⊓ 𝓟 O ≤ 𝓝 y) :
    tangentConeAt ℝ (f '' O) (f y) = range L := by
  refine subset_antisymm (tangentConeAt_image_subset_range hf hL hinv) ?_
  rintro _ ⟨v, rfl⟩
  have := hf.hasFDerivWithinAt.mapsTo_tangent_cone (s := O)
  rw [tangentConeAt_of_mem_nhds hO] at this
  exact this (mem_univ v)

end TangentCone

section Submanifold

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {P : Type*} [TopologicalSpace P] [ChartedSpace E P] {M : Set P}
  [ChartedSpace E' M]

variable (E E' M)

/-- `M ⊆ P` is a *complex submanifold* of the complex manifold `P` (Fulton, §19.1), for the
charted-space structure on `M` modelled on `E'`: in every chart `e'` of `M` and every chart `e` of
`P`, the transition `z ↦ e (e'⁻¹ z)` is holomorphic (continuously complex differentiable,
`ContDiffAt ℂ 1`), with an injective (complex linear) derivative, at every point `z` of the
target of `e'` with `e'⁻¹ z` in the source of `e`. Since `M` has the subspace topology, `M` is
then an imbedded complex submanifold. (A complex differentiable map is analytic, so asking for
`ContDiffAt ℂ 1` rather than complex differentiability is the same condition; Mathlib has the
implication only in one variable, hence the stronger-looking form.) -/
def IsComplexSubmanifold : Prop :=
  ∀ e' ∈ atlas E' M, ∀ e ∈ atlas E P, ∀ y ∈ e'.target, ((e'.symm y : M) : P) ∈ e.source →
    ContDiffAt ℂ 1 (fun z ↦ e (e'.symm z : P)) y ∧
      Function.Injective (fderiv ℂ (fun z ↦ e (e'.symm z : P)) y)

variable {E E' M}

/-- The chart transition `z ↦ e (e'⁻¹ z)` from a chart `e'` of `M ⊆ P` to a chart `e` of `P` is a
homeomorphism onto its image near `e' x`: points of its domain whose images tend to `e x` tend to
`e' x`. -/
theorem comap_chartTransition_inf_principal_le_nhds {P E E' : Type*} [TopologicalSpace P]
    [TopologicalSpace E] [TopologicalSpace E'] {M : Set P} {e' : OpenPartialHomeomorph M E'}
    {e : OpenPartialHomeomorph P E} {x : M} (hxe' : x ∈ e'.source) (hxe : (x : P) ∈ e.source) :
    comap (fun z ↦ e (e'.symm z : P)) (𝓝 (e x)) ⊓
        𝓟 (e'.target ∩ (fun z ↦ (e'.symm z : P)) ⁻¹' e.source) ≤ 𝓝 (e' x) := by
  set G := comap (fun z ↦ e (e'.symm z : P)) (𝓝 (e x)) ⊓
    𝓟 (e'.target ∩ (fun z ↦ (e'.symm z : P)) ⁻¹' e.source)
  have hfG : Tendsto (fun z ↦ e (e'.symm z : P)) G (𝓝 (e x)) :=
    tendsto_comap.mono_left inf_le_left
  have hOG : ∀ᶠ z in G, z ∈ e'.target ∩ (fun z ↦ (e'.symm z : P)) ⁻¹' e.source :=
    mem_inf_of_right (mem_principal_self _)
  have h1 : Tendsto (fun z ↦ (e'.symm z : P)) G (𝓝 (x : P)) := by
    have h := (e.continuousAt_symm (e.map_source hxe)).tendsto.comp hfG
    rw [Function.comp_def, e.left_inv hxe] at h
    exact h.congr' (hOG.mono fun z hz ↦ e.left_inv hz.2)
  have h2 : Tendsto e'.symm G (𝓝 x) := Topology.IsInducing.subtypeVal.tendsto_nhds_iff.2 h1
  have h3 : Tendsto (fun z ↦ e' (e'.symm z)) G (𝓝 (e' x)) :=
    (e'.continuousAt hxe').tendsto.comp h2
  exact (h3.congr' (hOG.mono fun z hz ↦ e'.right_inv hz.1) : Tendsto id G (𝓝 (e' x)))

/-- **The tangent space of an immersed subset in a chart.** Let `e'` be a chart of `M` and `e`
a chart of `P`, both defined at `x ∈ M`, such that the transition `z ↦ e (e'⁻¹ z)` is
differentiable at `e' x` with an injective derivative `L`. Then the tangent cone of `M` at `x`
in the chart `e` is the range of `L` (the image of `T_x M`). -/
theorem tangentConeAt_image_chart_eq_range [FiniteDimensional ℂ E]
    {e' : OpenPartialHomeomorph M E'} {e : OpenPartialHomeomorph P E} {x : M}
    (hxe' : x ∈ e'.source) (hxe : (x : P) ∈ e.source) {L : E' →L[ℂ] E}
    (hL : HasFDerivAt (fun z ↦ e (e'.symm z : P)) L (e' x)) (hLi : Function.Injective L) :
    tangentConeAt ℝ (e '' (M ∩ e.source)) (e x) =
      (LinearMap.range (L : E' →ₗ[ℂ] E) : Set E) := by
  have : FiniteDimensional ℝ E := FiniteDimensional.complexToReal E
  set f : E' → E := fun z ↦ e (e'.symm z : P)
  set y := e' x
  have hy : y ∈ e'.target := e'.map_source hxe'
  have hsy : e'.symm y = x := e'.left_inv hxe'
  have hfy : f y = e x := by simp only [f, hsy]
  set O : Set E' := e'.target ∩ (fun z ↦ (e'.symm z : P)) ⁻¹' e.source
  have hO : O ∈ 𝓝 y := by
    refine inter_mem (e'.open_target.mem_nhds hy) ?_
    refine (continuous_subtype_val.continuousAt.comp
      (e'.continuousAt_symm hy)).preimage_mem_nhds ?_
    simpa only [Function.comp_apply, hsy] using e.open_source.mem_nhds hxe
  have hinv : comap f (𝓝 (f y)) ⊓ 𝓟 O ≤ 𝓝 y := by
    rw [hfy]
    exact comap_chartTransition_inf_principal_le_nhds hxe' hxe
  have hLR : HasFDerivAt f (L.restrictScalars ℝ) y := hL.restrictScalars ℝ
  have hcone := tangentConeAt_image_eq_range hO hLR hLi hinv
  rw [hfy] at hcone
  obtain ⟨V, hV, hVe'⟩ := isOpen_induced_iff.1 e'.open_source
  have hxV : (x : P) ∈ V := show x ∈ Subtype.val ⁻¹' V from hVe'.symm ▸ hxe'
  set T : Set E := e.target ∩ e.symm ⁻¹' V
  have hT : T ∈ 𝓝 (e x) := by
    refine inter_mem (e.open_target.mem_nhds (e.map_source hxe)) ?_
    refine (e.continuousAt_symm (e.map_source hxe)).preimage_mem_nhds ?_
    rw [e.left_inv hxe]
    exact hV.mem_nhds hxV
  have hsub1 : f '' O ⊆ e '' (M ∩ e.source) := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨(e'.symm z : P), ⟨(e'.symm z).2, hz.2⟩, rfl⟩
  have hsub2 : e '' (M ∩ e.source) ∩ T ⊆ f '' O := by
    rintro _ ⟨⟨p, ⟨hpM, hpe⟩, rfl⟩, -, hpV⟩
    rw [mem_preimage, e.left_inv hpe] at hpV
    set m : M := ⟨p, hpM⟩
    have hm : m ∈ e'.source := by rwa [← hVe']
    refine ⟨e' m, ⟨e'.map_source hm, ?_⟩, ?_⟩
    · simpa only [mem_preimage, e'.left_inv hm] using hpe
    · simp only [f, e'.left_inv hm, m]
  have hrange : (LinearMap.range (L : E' →ₗ[ℂ] E) : Set E) = range (L.restrictScalars ℝ) := by
    rw [LinearMap.coe_range]; rfl
  rw [hrange]
  apply subset_antisymm
  · rw [← tangentConeAt_inter_nhds hT, ← hcone]
    exact tangentConeAt_mono hsub2
  · rw [← hcone]
    exact tangentConeAt_mono hsub1

/-- For a complex submanifold `M` of `P` and `x ∈ M`, the tangent cone of `M` at `x` in the chart
of `P` at `x` is a complex subspace of `E` (the condition on `W` in
`TubularNeighbourhood.IsOrientationCompatible`). -/
theorem IsComplexSubmanifold.exists_tangentConeAt_eq [FiniteDimensional ℂ E]
    (hM : IsComplexSubmanifold E E' M) (x : M) :
    ∃ W : Submodule ℂ E,
      tangentConeAt ℝ (chartAt E (x : P) '' (M ∩ (chartAt E (x : P)).source))
        (chartAt E (x : P) x) = W := by
  have hy := (chartAt E' x).map_source (mem_chart_source E' x)
  obtain ⟨hc, hLi⟩ := hM _ (chart_mem_atlas E' x) _ (chart_mem_atlas E (x : P)) _ hy
    (by rw [(chartAt E' x).left_inv (mem_chart_source E' x)]; exact mem_chart_source E (x : P))
  exact ⟨_, tangentConeAt_image_chart_eq_range (mem_chart_source E' x)
    (mem_chart_source E (x : P)) (hc.differentiableAt one_ne_zero).hasFDerivAt hLi⟩

end Submanifold

end MMP
