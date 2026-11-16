module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Geometry.Manifold.VectorField.Pullback
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PicardGroup

/-!
# Flows of stratified horizontal vector fields

Let `g : Z → B` be a holomorphic map from a complex manifold of dimension `n` to a complex curve,
and let `E = ⋃ i, D i` be a simple normal crossing divisor on `Z`, proper over `B`, such that `g`
is a submersion near `E` and on every stratum of `E`. This file builds the stratified Ehresmann
flows of `g` near `E`: over a small disk of a chart `ψ` of `B`, the real coordinate fields
`∂_s, ∂_u` of the disk lift to vector fields on `Z` tangent to every component `D i`, whose flows
translate `ψ ∘ g` and preserve every `D i`.

The construction follows the classical route. A complex manifold is a real smooth manifold with the
same charts. In a chart straightening the components through a point, a coordinate vector `eⱼ`
transverse to these components and to the fibres of `g` gives a local lift `(ξ / ∂ⱼh) • eⱼ`, where
`h` is `ψ ∘ g` read in the chart; such local lifts are glued by a smooth partition of unity, cut
off to a compact support, and integrated with the Picard–Lindelöf theorem. Uniqueness of integral
curves gives the group law of the flow and its invariance of the components, and the local flows
of the Picard–Lindelöf theorem make it continuous in time and initial point.

That `∂ⱼh` is `C¹` needs the regularity of holomorphic functions of several variables, which is
proved here from the one-variable Cauchy formula along lines.

## Main definitions

* `MMP.Analytic.StratifiedFlows.chartRep`: the representative of a vector field in a chart.
* `MMP.Analytic.StratifiedFlows.IsTangentToStrata`: a vector field on `Z` tangent, in every
  holomorphic chart straightening a component `D i`, to the corresponding coordinate hyperplane.

## Main results

* `MMP.Analytic.StratifiedFlows.isManifold_real_of_complex`: a complex manifold is a real smooth
  manifold.
* `MMP.Analytic.StratifiedFlows.contDiffOn_one_of_differentiableOn`,
  `MMP.Analytic.StratifiedFlows.differentiableOn_fderiv_apply`: a complex differentiable function
  on an open subset of `ℂⁿ` is `C¹`, and its directional derivatives are complex differentiable.
* `MMP.Analytic.StratifiedFlows.exists_global_flow`: a compactly supported `C¹` vector field on a
  Hausdorff boundaryless manifold has a complete flow, continuous in time and initial point.
* `MMP.Analytic.StratifiedFlows.mem_iff_of_isMIntegralCurve_of_isTangentToStrata`: the integral
  curves of a field tangent to the strata preserve every component.
* `MMP.Analytic.StratifiedFlows.exists_horizontal_field`: horizontal lifts tangent to the strata.
* `MMP.Analytic.StratifiedFlows.exists_horizontal_flows`: uniform horizontal flows over a small
  disk, moving a decreasing chain of neighbourhoods of `E` into each other.

## Implementation notes

* Vector fields are sections `v : (x : Z) → TangentSpace 𝓘(ℝ, E) x` of the real tangent bundle,
  read in the preferred charts; integral curves are Mathlib's `IsMIntegralCurve`.
* The flow is built for a field vanishing outside a compact set, so that it is complete; the
  horizontal field is cut off by a smooth bump function equal to one near `E` over a closed disk.
* Continuity of the flow is proved near time `0` from the continuous local flows of the
  Picard–Lindelöf theorem, and extended to all times by the group law.

## References

* [J. M. Lee, *Introduction to Smooth Manifolds*][lee2012], Chapter 9.
-/

@[expose] public section

open Set Bundle Filter Topology Metric
open scoped Manifold ContDiff

namespace MMP.Analytic.StratifiedFlows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- In a chart `e` of the maximal atlas, the vector field on `U` whose representative is a `C¹`
map `f` is a `C¹` section of the tangent bundle. -/
theorem contMDiffOn_section_of_chart {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {f : E → E} {U : Set M}
    (hU : U ⊆ e.source) (hf : ContDiffOn ℝ 1 f (e '' U)) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x => (⟨x, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) (f (e x))⟩ :
        TangentBundle 𝓘(ℝ, E) M)) U := by
  have h1 := (ContMDiffOn.contMDiffOn_tangentMapWithin (contMDiffOn_symm_of_mem_maximalAtlas he)
    (m := 1) (by simp) e.open_target.uniqueMDiffOn)
  have hW : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun y : E => (⟨y, f y⟩ : TangentBundle 𝓘(ℝ, E) E)) (e '' U) := fun y hy =>
    contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.2 (hf y hy)
  have he1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e U :=
    (ContMDiffOn.of_le (contMDiffOn_of_mem_maximalAtlas he) (by exact_mod_cast le_top)).mono hU
  have h2 := h1.comp (hW.comp he1 (mapsTo_image e U)) (fun x hx => e.map_source (hU hx))
  refine h2.congr fun x hx => ?_
  simp only [Function.comp_apply, tangentMapWithin]
  rw [mfderivWithin_of_isOpen e.open_target (e.map_source (hU hx))]
  congr 1
  exact (e.left_inv (hU hx)).symm

/-- The representative, in the chart `e`, of a vector field `v`. -/
noncomputable def chartRep (e : OpenPartialHomeomorph M E)
    (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) : E → E :=
  fun y => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e.symm y) (v (e.symm y))

theorem chartRep_apply (e : OpenPartialHomeomorph M E)
    (v : (x : M) → TangentSpace 𝓘(ℝ, E) x) (y : E) :
    chartRep e v y = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e.symm y) (v (e.symm y)) :=
  rfl

/-- The representative in a chart of the maximal atlas of a `C¹` vector field is `C¹` on the
target of the chart. -/
theorem contDiffOn_chartRep {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M))) :
    ContDiffOn ℝ 1 (chartRep e v) e.target := by
  have h1 := (ContMDiffOn.contMDiffOn_tangentMapWithin (contMDiffOn_of_mem_maximalAtlas he)
    (m := 1) (by simp) e.open_source.uniqueMDiffOn)
  have h0 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e.symm e.target :=
    ContMDiffOn.of_le (contMDiffOn_symm_of_mem_maximalAtlas he) (by exact_mod_cast le_top)
  have h2 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun y => (tangentMapWithin 𝓘(ℝ, E) 𝓘(ℝ, E) e e.source ⟨e.symm y, v (e.symm y)⟩).2)
      e.target := by
    refine (contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).comp_contMDiffOn
      (h1.comp (hv.comp_contMDiffOn h0) ?_)
    intro y hy
    exact e.map_target hy
  rw [← contMDiffOn_iff_contDiffOn]
  refine h2.congr fun y hy => ?_
  simp only [tangentMapWithin, chartRep_apply]
  rw [mfderivWithin_of_isOpen e.open_source (e.map_target hy)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Along a curve tangent to `v`, the derivative of `f ∘ γ` is `df (v)`. -/
theorem hasDerivAt_comp_of_hasMFDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {v : (x : M) → TangentSpace 𝓘(ℝ, E) x} {γ : ℝ → M} {t : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))))
    {f : M → F} (hf : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, F) f (γ t)) :
    HasDerivAt (f ∘ γ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (γ t) (v (γ t)) : F) t := by
  have h := hf.hasMFDerivAt.comp t hγ
  rw [hasMFDerivAt_iff_hasFDerivAt] at h
  refine hasDerivAt_iff_hasFDerivAt.2 (h.congr_fderiv ?_)
  ext
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f (γ t) ((1 : ℝ) • v (γ t)) = (1 : ℝ) • _
  rw [one_smul, one_smul]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
/-- A solution of the chart equation `β' = chartRep e v β` is, read back through `e`, a curve
tangent to `v`. -/
theorem hasMFDerivAt_symm_comp {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    {β : ℝ → E} {t : ℝ} (hβt : β t ∈ e.target) (hβ : HasDerivAt β (chartRep e v (β t)) t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (e.symm ∘ β) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v (e.symm (β t)))) := by
  have he1 : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by exact_mod_cast le_top) he
  have hsymm := (mdifferentiableAt_symm_of_mem_maximalAtlas he1 hβt).hasMFDerivAt
  have hβ' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) β t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (chartRep e v (β t)) : ℝ →L[ℝ] E) :=
    hasMFDerivAt_iff_hasFDerivAt.2 hβ.hasFDerivAt
  refine (hsymm.comp t hβ').congr_mfderiv ?_
  have hmd : e.MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) :=
    ⟨fun x hx => (mdifferentiableAt_of_mem_maximalAtlas he1 hx).mdifferentiableWithinAt,
      fun y hy => (mdifferentiableAt_symm_of_mem_maximalAtlas he1 hy).mdifferentiableWithinAt⟩
  have key := hmd.symm_comp_deriv (e.map_target hβt)
  rw [e.right_inv hβt] at key
  ext
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (β t) ((1 : ℝ) • chartRep e v (β t)) =
    (1 : ℝ) • v (e.symm (β t))
  rw [one_smul, one_smul]
  exact (DFunLike.congr_fun key (v (e.symm (β t))))

/-- A curve with constant velocity `f'` on an open interval is affine there. -/
theorem eq_add_smul_of_hasDerivAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {f' : F} {a b : ℝ} (hf : ∀ t ∈ Ioo a b, HasDerivAt f f' t) {s t : ℝ}
    (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) : f t = f s + (t - s) • f' := by
  have hg : ∀ u ∈ Ioo a b, HasDerivAt (fun u => f u - u • f') 0 u := by
    intro u hu
    convert (hf u hu).sub ((hasDerivAt_id u).smul_const f') using 1
    · rfl
    · simp
  have := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun u hu => (hg u hu).differentiableAt.differentiableWithinAt)
    (fun u hu => (hg u hu).deriv) ht hs
  rw [sub_smul]
  linear_combination (norm := module) this

section ComplexToReal

variable {n : ℕ}

/-- Holomorphic changes of coordinates are real smooth. -/
theorem contDiffGroupoid_complex_le_real :
    contDiffGroupoid ∞ 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ≤
      contDiffGroupoid ∞ 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) := by
  intro e he
  have he' := mem_groupoid_of_pregroupoid.mp he
  refine mem_groupoid_of_pregroupoid.mpr ?_
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, range_id, inter_univ,
    modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp, preimage_id_eq] at he' ⊢
  exact ⟨he'.1.restrict_scalars ℝ, he'.2.restrict_scalars ℝ⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]

/-- A complex manifold is a real smooth manifold, with the same charts. -/
theorem isManifold_real_of_complex [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M where
  compatible he he' := contDiffGroupoid_complex_le_real (HasGroupoid.compatible he he')

/-- Every holomorphic chart is a real smooth chart. -/
theorem maximalAtlas_complex_subset_real :
    IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ M ⊆
      IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ M :=
  StructureGroupoid.maximalAtlas_mono contDiffGroupoid_complex_le_real

/-- A complex derivative of a function is also its real derivative. -/
theorem hasMFDerivAt_real_of_complex {f : M → ℂ} {x : M}
    {L : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ}
    (h : HasMFDerivAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) f x L) :
    HasMFDerivAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) f x (L.restrictScalars ℝ) :=
  ⟨h.1, h.2.restrictScalars ℝ⟩

/-- A complex differentiable function on a complex manifold is real differentiable. -/
theorem mdifferentiableAt_real_of_complex {f : M → ℂ} {x : M}
    (h : MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) f x) :
    MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) f x :=
  (hasMFDerivAt_real_of_complex h.hasMFDerivAt).mdifferentiableAt

/-- The real derivative of a complex differentiable function is its complex derivative, viewed as
a real linear map. -/
theorem mfderiv_real_eq_of_complex {f : M → ℂ} {x : M}
    (h : MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) f x) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) f x =
      (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) f x).restrictScalars ℝ :=
  (hasMFDerivAt_real_of_complex h.hasMFDerivAt).mfderiv

end ComplexToReal

section Hyperplane

variable {E E' F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]

/-- A map carrying the kernel of `ℓ` (near `y`) into the kernel of `ℓ'` has a derivative at `y`
carrying `ker ℓ` into `ker ℓ'`. -/
theorem map_fderiv_ker_of_mapsTo_ker {T : E → E'} {T' : E →L[ℝ] E'} {y : E}
    (hT : HasFDerivAt T T' y) {ℓ : E →L[ℝ] F₁} {ℓ' : E' →L[ℝ] F₂} {U : Set E} (hU : U ∈ 𝓝 y)
    (hmaps : ∀ z ∈ U, ℓ z = 0 → ℓ' (T z) = 0) (hy : ℓ y = 0) {w : E} (hw : ℓ w = 0) :
    ℓ' (T' w) = 0 := by
  have hc : HasDerivAt (fun s : ℝ => y + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have hT0 : HasFDerivAt T T' (y + (0 : ℝ) • w) := by simpa using hT
  have h1 : HasDerivAt (fun s : ℝ => ℓ' (T (y + s • w))) (ℓ' (T' w)) 0 :=
    ℓ'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hT0.comp_hasDerivAt (0 : ℝ) hc)
  have hev : (fun s : ℝ => ℓ' (T (y + s • w))) =ᶠ[𝓝 0] fun _ => (0 : F₂) := by
    have hcont : Tendsto (fun s : ℝ => y + s • w) (𝓝 0) (𝓝 y) := by
      simpa using hc.continuousAt.tendsto
    filter_upwards [hcont hU] with s hs
    exact hmaps _ hs (by simp [hy, hw])
  exact h1.unique ((hasDerivAt_const (0 : ℝ) (0 : F₂)).congr_of_eventuallyEq hev)

end Hyperplane

section NormedFlow

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Picard–Lindelöf with a confined flow.** Under the hypotheses of the Picard–Lindelöf theorem,
there is a local flow, continuous in the initial point and time, whose trajectories stay in the
closed ball of radius `a`. -/
theorem exists_flow_mem_closedBall {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : E} {a r L K : ℝ≥0} (hf : IsPicardLindelof f t₀ x₀ a r L K) :
    ∃ α : E → ℝ → E, (∀ x ∈ closedBall x₀ r, α x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α x) (f t (α x t)) (Icc tmin tmax) t ∧
        α x t ∈ closedBall x₀ a) ∧
      ContinuousOn (fun p : E × ℝ => α p.1 p.2) (closedBall x₀ r ×ˢ Icc tmin tmax) := by
  classical
  have (x) (hx : x ∈ closedBall x₀ r) := ODE.FunSpace.exists_isFixedPt_next hf hx
  choose α hα using this
  set α' := fun (x : E) ↦ if hx : x ∈ closedBall x₀ r then
    α x hx |>.compProj else 0 with hα'
  have h1 : ∀ x ∈ closedBall x₀ r, α' x t₀ = x ∧
      ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (α' x) (f t (α' x t)) (Icc tmin tmax) t ∧
        α' x t ∈ closedBall x₀ a := by
    intro x hx
    refine ⟨?_, fun t ht ↦ ⟨?_, ?_⟩⟩
    · rw [hα']
      beta_reduce
      rw [dite_eq_left hx, ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
    · rw [hα']
      beta_reduce
      rw [dite_eq_left hx, ODE.FunSpace.compProj_apply]
      apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hf.continuousOn_uncurry
        (α x hx |>.continuous_compProj.continuousOn)
        (fun _ ht' ↦ α x hx |>.compProj_mem_closedBall hf.mul_max_le)
        x ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hα]
      rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]
    · rw [hα']
      beta_reduce
      rw [dite_eq_left hx]
      exact (α x hx).compProj_mem_closedBall hf.mul_max_le
  refine ⟨α', h1, ?_⟩
  obtain ⟨L', h⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hlip : ∀ t ∈ Icc tmin tmax, LipschitzOnWith L' (α' · t) (closedBall x₀ r) := by
    refine fun t ht ↦ LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
    simp_rw [hα']
    rw [dite_eq_left hx, dite_eq_left hy, ODE.FunSpace.compProj_apply,
      ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply, ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t₀⟩
    exact ContinuousMap.dist_le_iff_of_nonempty.mp
      (h x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)) _
  exact continuousOn_prod_of_continuousOn_lipschitzOnWith (fun p : E × ℝ => α' p.1 p.2) L'
    (fun x hx ↦ HasDerivWithinAt.continuousOn fun t ht => ((h1 x hx).2 t ht).1) hlip

/-- **Local flow of a `C¹` vector field**, confined to a given neighbourhood `U` of the initial
point. -/
theorem exists_local_flow_of_contDiffAt {f : E → E} {y₀ : E} {U : Set E} (hU : U ∈ 𝓝 y₀)
    (hf : ContDiffAt ℝ 1 f y₀) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ α : E → ℝ → E,
      (∀ y ∈ closedBall y₀ r, α y 0 = y ∧
        ∀ t ∈ Ioo (-ε) ε, HasDerivAt (α y) (f (α y t)) t ∧ α y t ∈ U) ∧
      ContinuousOn (fun p : E × ℝ => α p.1 p.2) (closedBall y₀ r ×ˢ Ioo (-ε) ε) := by
  obtain ⟨K, s, hs, hl⟩ := hf.exists_lipschitzOnWith
  obtain ⟨a, ha, has⟩ := Metric.mem_nhds_iff.mp (inter_mem hs hU)
  have hsub : closedBall y₀ (a / 2) ⊆ s ∩ U :=
    (closedBall_subset_ball (half_lt_self ha)).trans has
  set L : ℝ := K * a + ‖f y₀‖ + 1 with hL
  have hL0 : 0 < L := by positivity
  have hb : ∀ x ∈ closedBall y₀ (a / 2), ‖f x‖ ≤ L := by
    intro x hx
    calc ‖f x‖ ≤ ‖f x - f y₀‖ + ‖f y₀‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖x - y₀‖ + ‖f y₀‖ := by
        gcongr
        exact hl.norm_sub_le (hsub hx).1 (mem_of_mem_nhds hs)
      _ ≤ K * a + ‖f y₀‖ := by
        gcongr
        have : ‖x - y₀‖ ≤ a / 2 := mem_closedBall_iff_norm.mp hx
        linarith
      _ ≤ L := by linarith
  set ε : ℝ := a / 4 / L with hε
  have hε0 : 0 < ε := by positivity
  have hpl : IsPicardLindelof (fun _ ↦ f) (tmin := -ε) (tmax := ε) ⟨0, by simp [hε0.le]⟩ y₀
      ⟨a / 2, by positivity⟩ ⟨a / 4, by positivity⟩ ⟨L, hL0.le⟩ K := by
    apply IsPicardLindelof.of_time_independent hb (hl.mono fun x hx => (hsub hx).1)
    change L * max (ε - 0) (0 - -ε) ≤ a / 2 - a / 4
    rw [sub_zero, zero_sub, neg_neg, max_self, hε, mul_div_cancel₀ _ hL0.ne']
    linarith
  obtain ⟨α, hα, hαc⟩ := exists_flow_mem_closedBall hpl
  refine ⟨a / 4, by positivity, ε, hε0, α, fun y hy => ⟨(hα y hy).1, fun t ht => ?_⟩, ?_⟩
  · have ht' : t ∈ Icc (-ε) ε := Ioo_subset_Icc_self ht
    obtain ⟨hd, hm⟩ := (hα y hy).2 t ht'
    exact ⟨hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2), (hsub hm).2⟩
  · exact hαc.mono (prod_mono subset_rfl Ioo_subset_Icc_self)

end NormedFlow

section ManifoldFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {v : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- **Local flows.** A `C¹` vector field has, near every point, a local flow defined for a uniform
time, continuous in time and initial point. -/
theorem exists_local_flow
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (x₀ : M) :
    ∃ N : Set M, IsOpen N ∧ x₀ ∈ N ∧ ∃ τ > (0 : ℝ), ∃ Φ : ℝ → M → M,
      ContinuousOn (fun p : ℝ × M => Φ p.1 p.2) (Ioo (-τ) τ ×ˢ N) ∧
      ∀ x ∈ N, Φ 0 x = x ∧ IsMIntegralCurveOn (Φ · x) v (Ioo (-τ) τ) := by
  set e := chartAt E x₀ with he_def
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := IsManifold.chart_mem_maximalAtlas x₀
  have hx₀ : x₀ ∈ e.source := mem_chart_source E x₀
  have hT : e.target ∈ 𝓝 (e x₀) := e.open_target.mem_nhds (e.map_source hx₀)
  have hf : ContDiffAt ℝ 1 (chartRep e v) (e x₀) := (contDiffOn_chartRep he hv).contDiffAt hT
  obtain ⟨r, hr, ε, hε, α, hα, hαc⟩ := exists_local_flow_of_contDiffAt hT hf
  refine ⟨e.source ∩ e ⁻¹' ball (e x₀) r, e.isOpen_inter_preimage isOpen_ball,
    ⟨hx₀, mem_ball_self hr⟩, ε, hε, fun t x => e.symm (α (e x) t), ?_, ?_⟩
  · have h1 : ContinuousOn (fun p : ℝ × M => (e p.2, p.1))
        (Ioo (-ε) ε ×ˢ (e.source ∩ e ⁻¹' ball (e x₀) r)) :=
      (e.continuousOn.comp continuousOn_snd fun p hp => hp.2.1).prodMk continuousOn_fst
    have h2 := hαc.comp h1 fun p hp => ⟨ball_subset_closedBall hp.2.2, hp.1⟩
    refine e.continuousOn_symm.comp h2 fun p hp => ?_
    exact ((hα _ (ball_subset_closedBall hp.2.2)).2 p.1 hp.1).2
  · intro x hx
    have hy : e x ∈ closedBall (e x₀) r := ball_subset_closedBall hx.2
    refine ⟨by simp only [(hα _ hy).1, e.left_inv hx.1], fun t ht => ?_⟩
    obtain ⟨hd, hm⟩ := (hα _ hy).2 t ht
    exact (hasMFDerivAt_symm_comp he hm hd).hasMFDerivWithinAt

/-- A uniform positive time for the local flows over a compact set. -/
theorem exists_uniform_local_flow
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {K : Set M} (hK : IsCompact K) :
    ∃ τ > (0 : ℝ), ∀ x ∈ K, ∃ N : Set M, IsOpen N ∧ x ∈ N ∧ ∃ Φ : ℝ → M → M,
      ContinuousOn (fun p : ℝ × M => Φ p.1 p.2) (Ioo (-τ) τ ×ˢ N) ∧
      ∀ y ∈ N, Φ 0 y = y ∧ IsMIntegralCurveOn (Φ · y) v (Ioo (-τ) τ) := by
  choose N hNo hxN τ hτ Φ hΦc hΦ using exists_local_flow hv
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover N fun x _ => (hNo x).mem_nhds (hxN x)
  obtain ⟨τ₀, hτ₀, hτ₀le⟩ : ∃ τ₀ > (0 : ℝ), ∀ y ∈ t, τ₀ ≤ τ y := by
    rcases t.eq_empty_or_nonempty with ht | ht
    · exact ⟨1, one_pos, by simp [ht]⟩
    · obtain ⟨y, hy, hmin⟩ := t.exists_min_image τ ht
      exact ⟨τ y, hτ y, hmin⟩
  refine ⟨τ₀, hτ₀, fun x hx => ?_⟩
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (hKt hx)
  have hsub : Ioo (-τ₀) τ₀ ⊆ Ioo (-τ y) (τ y) :=
    Ioo_subset_Ioo (neg_le_neg (hτ₀le y hyt)) (hτ₀le y hyt)
  exact ⟨N y, hNo y, hxy, Φ y, (hΦc y).mono (prod_mono hsub subset_rfl),
    fun z hz => ⟨(hΦ y z hz).1, (hΦ y z hz).2.mono hsub⟩⟩

variable [T2Space M]

/-- **Global flow of a compactly supported vector field.** A `C¹` vector field vanishing outside a
compact set `K` has a complete flow: a continuous map `F : ℝ → M → M` whose orbits are integral
curves, satisfying the group law and fixing every point outside `K`. -/
theorem exists_global_flow
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x ∉ K, v x = 0) :
    ∃ F : ℝ → M → M, (∀ x, F 0 x = x) ∧ (∀ x, IsMIntegralCurve (F · x) v) ∧
      (∀ s t x, F s (F t x) = F (s + t) x) ∧ Continuous (fun p : ℝ × M => F p.1 p.2) ∧
      ∀ t, ∀ x ∉ K, F t x = x := by
  obtain ⟨τ, hτ, hloc⟩ := exists_uniform_local_flow hv hK
  have hcurve : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurveOn γ v (Ioo (-τ) τ) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨N, -, hxN, Φ, -, hΦ⟩ := hloc x hx
      exact ⟨(Φ · x), (hΦ x hxN).1, (hΦ x hxN).2⟩
    · exact ⟨fun _ => x, rfl, (isMIntegralCurve_const (hvK x hx)).isMIntegralCurveOn _⟩
  choose γ hγ0 hγ using exists_isMIntegralCurve_of_isMIntegralCurveOn hv hτ hcurve
  set F : ℝ → M → M := fun t x => γ x t with hFdef
  have hF0 : ∀ x, F 0 x = x := hγ0
  have hF : ∀ x, IsMIntegralCurve (F · x) v := hγ
  clear_value F
  have hgroup : ∀ s t x, F s (F t x) = F (s + t) x := by
    intro s t x
    have h1 : IsMIntegralCurve ((F · x) ∘ (· + t)) v := (hF x).comp_add t
    have := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv (hF (F t x)) h1
      (by simp [hF0])
    exact congrFun this s
  have hout : ∀ t, ∀ x ∉ K, F t x = x := by
    intro t x hx
    have := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv (hF x)
      (isMIntegralCurve_const (hvK x hx)) (hF0 x)
    exact congrFun this t
  have hKc : IsClosed K := hK.isClosed
  -- continuity for small times
  have hsmall : ∀ x, ∀ t ∈ Ioo (-τ) τ, ContinuousAt (fun p : ℝ × M => F p.1 p.2) (t, x) := by
    intro x t ht
    by_cases hx : x ∈ K
    · obtain ⟨N, hNo, hxN, Φ, hΦc, hΦ⟩ := hloc x hx
      have heq : EqOn (fun p : ℝ × M => F p.1 p.2) (fun p : ℝ × M => Φ p.1 p.2)
          (Ioo (-τ) τ ×ˢ N) := by
        intro p hp
        have := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
          (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨by linarith, hτ⟩) hv
          ((hF p.2).isMIntegralCurveOn _) (hΦ p.2 hp.2).2 (by simp [hF0, (hΦ p.2 hp.2).1])
        exact this hp.1
      have hopen : IsOpen (Ioo (-τ) τ ×ˢ N) := isOpen_Ioo.prod hNo
      exact ((hΦc.congr heq).continuousAt (hopen.mem_nhds ⟨ht, hxN⟩))
    · have heq : (fun p : ℝ × M => F p.1 p.2) =ᶠ[𝓝 (t, x)] Prod.snd := by
        filter_upwards [(isOpen_univ.prod hKc.isOpen_compl).mem_nhds
          (show (t, x) ∈ univ ×ˢ Kᶜ from ⟨trivial, hx⟩)] with p hp
        exact hout p.1 p.2 hp.2
      exact continuousAt_snd.congr heq.symm
  -- each time-`t` map is continuous
  have hiter : ∀ (k : ℕ) (s : ℝ) (x : M), F (k * s) x = (F s)^[k] x := by
    intro k s x
    induction k with
    | zero => simp [hF0]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ← ih, hgroup]
      congr 1
      push_cast
      ring
  have hFt : ∀ t, Continuous (F t) := by
    intro t
    obtain ⟨k, hk⟩ := exists_nat_gt (|t| / τ)
    have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
    have hs : t / k ∈ Ioo (-τ) τ := by
      rw [mem_Ioo, ← abs_lt, abs_div, abs_of_pos hk0, div_lt_iff₀ hk0]
      rw [div_lt_iff₀ hτ] at hk
      linarith
    have hc : Continuous (F (t / k)) := continuous_iff_continuousAt.2 fun x =>
      (hsmall x _ hs).comp (Continuous.prodMk_right (t / k)).continuousAt
    have : F t = (F (t / k))^[k] := by
      funext x
      rw [← hiter, mul_div_cancel₀ _ hk0.ne']
    rw [this]
    exact hc.iterate k
  refine ⟨F, hF0, hF, hgroup, continuous_iff_continuousAt.2 fun p => ?_, hout⟩
  have hrep : (fun q : ℝ × M => F q.1 q.2) =
      (fun q : ℝ × M => F q.1 q.2) ∘ (fun q : ℝ × M => (q.1 - p.1, F p.1 q.2)) := by
    funext q
    simp only [Function.comp_apply, hgroup, sub_add_cancel]
  rw [hrep]
  refine ContinuousAt.comp ?_ ((continuous_fst.sub continuous_const).prodMk
    ((hFt p.1).comp continuous_snd)).continuousAt
  simp only [sub_self]
  exact hsmall _ 0 ⟨by linarith, hτ⟩

omit [T2Space M] in
/-- **Invariance of a flat closed set.** Let `S` be a closed set which near each of its points is,
in some chart `e`, the trace on `e.target` of the kernel of a continuous linear map `ℓ` admitting a
projection `P` onto its kernel. If `v` is tangent to `S` in these charts, then an integral curve of
`v` either stays in `S` or never meets it. -/
theorem mem_iff_of_isMIntegralCurve {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hv : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1 (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {S : Set M} (hS : IsClosed S)
    (hloc : ∀ x₀ ∈ S, ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M, x₀ ∈ e.source ∧
      ∃ (ℓ : E →L[ℝ] F) (P : E →L[ℝ] E), (∀ y, ℓ (P y) = 0) ∧ (∀ y, ℓ y = 0 → P y = y) ∧
        ℓ (e x₀) = 0 ∧ (∀ y ∈ e.target, ℓ y = 0 → e.symm y ∈ S) ∧
        ∀ y ∈ e.target, ℓ y = 0 → ℓ (chartRep e v y) = 0)
    {γ : ℝ → M} (hγ : IsMIntegralCurve γ v) (t : ℝ) : γ t ∈ S ↔ γ 0 ∈ S := by
  set A : Set ℝ := γ ⁻¹' S with hA
  have hAc : IsClosed A := hS.preimage hγ.continuous
  have hAo : IsOpen A := by
    refine isOpen_iff_mem_nhds.2 fun t₀ ht₀ => ?_
    obtain ⟨e, he, hx₀, ℓ, P, hℓP, hPℓ, hℓ₀, hback, htan⟩ := hloc (γ t₀) ht₀
    set y₀ := e (γ t₀)
    have hT : e.target ∈ 𝓝 y₀ := e.open_target.mem_nhds (e.map_source hx₀)
    have hPy₀ : P y₀ = y₀ := hPℓ y₀ hℓ₀
    have hf : ContDiffAt ℝ 1 (chartRep e v) y₀ := (contDiffOn_chartRep he hv).contDiffAt hT
    have hf' : ContDiffAt ℝ 1 (fun y => P (chartRep e v (P y))) y₀ := by
      have h1 : ContDiffAt ℝ 1 (chartRep e v) (P y₀) := by rwa [hPy₀]
      exact P.contDiff.contDiffAt.comp y₀ (h1.comp y₀ P.contDiff.contDiffAt)
    obtain ⟨r, hr, ε, hε, α, hα, -⟩ := exists_local_flow_of_contDiffAt hT hf'
    obtain ⟨hα0, hαd⟩ := hα y₀ (mem_closedBall_self hr.le)
    set β : ℝ → E := fun s => α y₀ (s - t₀) with hβ
    have hI : ∀ s ∈ Ioo (t₀ - ε) (t₀ + ε), s - t₀ ∈ Ioo (-ε) ε := fun s hs =>
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    -- the solution stays in the kernel of `ℓ`
    have hker : ∀ s ∈ Ioo (-ε) ε, ℓ (α y₀ s) = 0 := by
      intro s hs
      have hd : ∀ u ∈ Ioo (-ε) ε, HasDerivAt (fun u => ℓ (α y₀ u)) 0 u := by
        intro u hu
        have := ℓ.hasFDerivAt.comp_hasDerivAt u (hαd u hu).1
        rw [hℓP] at this
        exact this
      have := eq_add_smul_of_hasDerivAt hd (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩) hs
      simpa [hα0, hℓ₀] using this
    have hβd : ∀ s ∈ Ioo (t₀ - ε) (t₀ + ε), β s ∈ e.target ∧ ℓ (β s) = 0 ∧
        HasDerivAt β (chartRep e v (β s)) s := by
      intro s hs
      obtain ⟨hd, hm⟩ := hαd _ (hI s hs)
      have hk := hker _ (hI s hs)
      refine ⟨hm, hk, ?_⟩
      have hd' : HasDerivAt β (P (chartRep e v (P (α y₀ (s - t₀))))) s :=
        hd.comp_sub_const s t₀
      rw [hPℓ _ hk, hPℓ _ (htan _ hm hk)] at hd'
      exact hd'
    have hnhds : Ioo (t₀ - ε) (t₀ + ε) ∈ 𝓝 t₀ := Ioo_mem_nhds (by linarith) (by linarith)
    have hγ' : IsMIntegralCurveAt (e.symm ∘ β) v t₀ := by
      filter_upwards [hnhds] with s hs
      obtain ⟨hm, -, hd⟩ := hβd s hs
      exact hasMFDerivAt_symm_comp he hm hd
    have h0 : γ t₀ = (e.symm ∘ β) t₀ := by
      simp only [Function.comp_apply, hβ, sub_self, hα0]
      exact (e.left_inv hx₀).symm
    have heq := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless hv.contMDiffAt
      (hγ.isMIntegralCurveAt t₀) hγ' h0
    filter_upwards [heq, hnhds] with s hs hs'
    obtain ⟨hm, hk, -⟩ := hβd s hs'
    change γ s ∈ S
    rw [hs]
    exact hback _ hm hk
  rcases isClopen_iff.mp ⟨hAc, hAo⟩ with h | h
  · have h1 : γ t ∉ S := fun ht => (h ▸ (show t ∈ A from ht) : t ∈ (∅ : Set ℝ))
    have h2 : γ 0 ∉ S := fun ht => (h ▸ (show (0 : ℝ) ∈ A from ht) : (0 : ℝ) ∈ (∅ : Set ℝ))
    exact iff_of_false h1 h2
  · have h1 : t ∈ A := h ▸ mem_univ t
    have h2 : (0 : ℝ) ∈ A := h ▸ mem_univ 0
    exact iff_of_true h1 h2

end ManifoldFlow

section SNC

variable {n : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℂ (Fin n)) Z]
  {ι : Type*} {D : ι → Set Z}

/-- The `k`-th coordinate `y ↦ y k` of `ℂⁿ`, as a real continuous linear map. -/
noncomputable def coordCLM (k : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℝ] ℂ :=
  (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ

/-- `coordCLM k` sends `y` to its `k`-th coordinate. -/
@[simp] theorem coordCLM_apply (k : Fin n) (y : EuclideanSpace ℂ (Fin n)) :
    coordCLM k y = y k := rfl

/-- The projection killing the `k`-th coordinate. -/
noncomputable def killCoord (k : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (ContinuousLinearMap.id ℂ _ - (EuclideanSpace.proj k :
    EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).smulRight (EuclideanSpace.single k (1 : ℂ))).restrictScalars ℝ

/-- `killCoord k y` is `y` minus its `k`-th coordinate times the `k`-th basis vector. -/
theorem killCoord_apply (k : Fin n) (y : EuclideanSpace ℂ (Fin n)) :
    killCoord k y = y - y k • EuclideanSpace.single k (1 : ℂ) := rfl

/-- The `k`-th coordinate of `killCoord k y` vanishes. -/
@[simp] theorem killCoord_apply_self (k : Fin n) (y : EuclideanSpace ℂ (Fin n)) :
    killCoord k y k = 0 := by
  simp [killCoord_apply]

/-- `killCoord k` fixes every vector whose `k`-th coordinate vanishes. -/
theorem killCoord_eq_self (k : Fin n) {y : EuclideanSpace ℂ (Fin n)} (hy : y k = 0) :
    killCoord k y = y := by
  simp [killCoord_apply, hy]

omit [ChartedSpace (EuclideanSpace ℂ (Fin n)) Z] in
/-- A chart straightening a set onto a coordinate hyperplane carries its points into the
hyperplane. -/
theorem apply_eq_zero_of_image_eq {φ : OpenPartialHomeomorph Z (EuclideanSpace ℂ (Fin n))}
    {S : Set Z} {k : Fin n} (h : φ '' (S ∩ φ.source) = φ.target ∩ {y | y k = 0}) {x : Z}
    (hx : x ∈ S) (hxs : x ∈ φ.source) : φ x k = 0 :=
  (h.subset ⟨x, ⟨hx, hxs⟩, rfl⟩).2

omit [ChartedSpace (EuclideanSpace ℂ (Fin n)) Z] in
/-- A chart straightening a set onto a coordinate hyperplane carries the hyperplane back into the
set. -/
theorem symm_mem_of_image_eq {φ : OpenPartialHomeomorph Z (EuclideanSpace ℂ (Fin n))}
    {S : Set Z} {k : Fin n} (h : φ '' (S ∩ φ.source) = φ.target ∩ {y | y k = 0})
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ φ.target) (hyk : y k = 0) : φ.symm y ∈ S := by
  obtain ⟨x, ⟨hx, hxs⟩, rfl⟩ := h.symm.subset ⟨hy, hyk⟩
  rwa [φ.left_inv hxs]

variable [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z]

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z] in
/-- The components of a divisor given by simultaneous coordinate charts are closed. -/
theorem isClosed_of_snc
    (hD : ∀ x : Z, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z,
      x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
        (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
        ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0}) (i : ι) :
    IsClosed (D i) := by
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun x hx => ?_)
  obtain ⟨φ, -, hxs, s, c, hout, hin⟩ := hD x
  by_cases hi : i ∈ s
  · have hk := hin ⟨i, hi⟩
    have hφx : φ x (c ⟨i, hi⟩) ≠ 0 := by
      intro h0
      exact hx (by simpa [φ.left_inv hxs] using
        symm_mem_of_image_eq hk (φ.map_source hxs) h0)
    have hopen : IsOpen (φ.source ∩ φ ⁻¹' {y | y (c ⟨i, hi⟩) ≠ 0}) :=
      φ.isOpen_inter_preimage (isOpen_ne_fun (by fun_prop) continuous_const)
    filter_upwards [hopen.mem_nhds ⟨hxs, hφx⟩] with z hz hzD
    exact hz.2 (apply_eq_zero_of_image_eq hk hzD hz.1)
  · filter_upwards [φ.open_source.mem_nhds hxs] with z hz hzD
    have := hout i hi
    exact (this.subset ⟨hzD, hz⟩ : z ∈ (∅ : Set Z))

/-- A tangent vector `w` at `x` is *tangent to the strata* of `D` if, in every holomorphic chart
straightening a component `D i` through `x` onto a coordinate hyperplane, it lies in that
hyperplane. -/
def IsTangentToStrataAt (D : ι → Set Z) (x : Z)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) : Prop :=
  ∀ i, x ∈ D i → ∀ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z,
    x ∈ φ.source → ∀ k : Fin n, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y k = 0} →
      coordCLM k (mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) φ x w) = 0

/-- A vector field is *tangent to the strata* of `D` if it is so at every point. -/
def IsTangentToStrata (D : ι → Set Z)
    (v : (x : Z) → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) : Prop :=
  ∀ x, IsTangentToStrataAt D x (v x)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z] in
set_option backward.isDefEq.respectTransparency false in
/-- The zero vector is tangent to the strata. -/
theorem isTangentToStrataAt_zero (D : ι → Set Z) (x : Z) :
    IsTangentToStrataAt D x (0 : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) :=
  fun _ _ _ _ _ k _ => by
    rw [map_zero]
    exact map_zero (coordCLM k)

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z] in
set_option backward.isDefEq.respectTransparency false in
/-- The sum of two vectors tangent to the strata is tangent to the strata. -/
theorem IsTangentToStrataAt.add {x : Z} {w₁ w₂ : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x}
    (h₁ : IsTangentToStrataAt D x w₁) (h₂ : IsTangentToStrataAt D x w₂) :
    IsTangentToStrataAt D x (w₁ + w₂) := fun i hi φ hφ hxs k hk => by
  rw [map_add]
  exact (map_add (coordCLM k) _ _).trans (by rw [h₁ i hi φ hφ hxs k hk, h₂ i hi φ hφ hxs k hk,
    add_zero])

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z] in
set_option backward.isDefEq.respectTransparency false in
/-- A real multiple of a vector tangent to the strata is tangent to the strata. -/
theorem IsTangentToStrataAt.smul {x : Z} {w : TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x}
    (h : IsTangentToStrataAt D x w) (a : ℝ) : IsTangentToStrataAt D x (a • w) :=
  fun i hi φ hφ hxs k hk => by
    rw [map_smul]
    exact (map_smul (coordCLM k) a _).trans (by rw [h i hi φ hφ hxs k hk, smul_zero])

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z] in
/-- A vector field tangent to the strata stays tangent to the strata after multiplication by a
real function. -/
theorem IsTangentToStrata.smul {v : (x : Z) → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x}
    (hv : IsTangentToStrata D v) (χ : Z → ℝ) : IsTangentToStrata D (fun x => χ x • v x) :=
  fun x => (hv x).smul (χ x)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ Z] [T2Space Z]

omit [T2Space Z] in
/-- **The flow of a field tangent to the strata preserves every component.** -/
theorem mem_iff_of_isMIntegralCurve_of_isTangentToStrata
    (hD : ∀ x : Z, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z,
      x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
        (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
        ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0})
    {v : (x : Z) → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x}
    (hv : ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)).tangent 1
      (fun x => (⟨x, v x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) Z)))
    (htan : IsTangentToStrata D v)
    {γ : ℝ → Z} (hγ : IsMIntegralCurve γ v) (i : ι) (t : ℝ) : γ t ∈ D i ↔ γ 0 ∈ D i := by
  refine mem_iff_of_isMIntegralCurve (F := ℂ) hv (isClosed_of_snc hD i) (fun x₀ hx₀ => ?_) hγ t
  obtain ⟨φ, hφ, hxs, s, c, hout, hin⟩ := hD x₀
  have hi : i ∈ s := by
    by_contra hi
    exact ((hout i hi).subset ⟨hx₀, hxs⟩ : x₀ ∈ (∅ : Set Z))
  set k := c ⟨i, hi⟩
  have hk := hin ⟨i, hi⟩
  refine ⟨φ, maximalAtlas_complex_subset_real hφ, hxs, coordCLM k, killCoord k,
    fun y => killCoord_apply_self k y, fun y hy => killCoord_eq_self k hy,
    apply_eq_zero_of_image_eq hk hx₀ hxs, fun y hy hyk => symm_mem_of_image_eq hk hy hyk,
    fun y hy hyk => ?_⟩
  have hmem := symm_mem_of_image_eq hk hy hyk
  exact htan _ i hmem φ hφ (φ.map_target hy) k hk

end SNC

section HolomorphicRegularity

/-! ### Regularity of holomorphic functions of several variables

A complex differentiable function `f` on an open subset of `ℂⁿ` has, along every direction `v`,
the derivative given by the one-variable Cauchy formula
`2πi • Df(z) v = ∮_{|t| = δ} t⁻² • f (z + t • v)`.
The right side is continuous in `z`, so `f` is `C¹`; differentiating under the integral sign, it is
complex differentiable in `z`, so the directional derivatives of `f` are again complex
differentiable. -/

open Complex Real MeasureTheory intervalIntegral
open scoped NNReal

variable {n : ℕ} {f : EuclideanSpace ℂ (Fin n) → ℂ} {U : Set (EuclideanSpace ℂ (Fin n))}

/-- **Cauchy's formula for a directional derivative.** If the closed disk `{z + t • v | ‖t‖ ≤ δ}`
lies in `U`, then `∮_{|t| = δ} t⁻² • f (z + t • v) = 2πi • Df(z) v`. -/
theorem circleIntegral_eq_two_pi_I_smul_fderiv (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {z v : EuclideanSpace ℂ (Fin n)} {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ t : ℂ, ‖t‖ ≤ δ → z + t • v ∈ U) :
    (∮ t in C(0, δ), (1 / t ^ 2) • f (z + t • v)) = (2 * π * I) • fderiv ℂ f z v := by
  have hline : ∀ t : ℂ, HasDerivAt (fun t : ℂ => z + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add z
  have hφ : DifferentiableOn ℂ (fun t : ℂ => f (z + t • v)) (closedBall 0 δ) := by
    intro t ht
    have ht' : ‖t‖ ≤ δ := by simpa using ht
    exact ((hf.differentiableAt (hU.mem_nhds (hball t ht'))).comp t
      (hline t).differentiableAt).differentiableWithinAt
  have h := hφ.deriv_eq_smul_circleIntegral hδ
  simp only [sub_zero] at h
  rw [h]
  congr 1
  have hz : z + (0 : ℂ) • v ∈ U := by simpa using hball 0 (by simp [hδ.le])
  have := (hf.differentiableAt (hU.mem_nhds hz)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) (hline 0)
  simp only [zero_smul, add_zero] at this
  exact this.deriv

/-- The Cauchy integral `∮_{|t| = δ} t⁻² • f (z + t • v)` written as an interval integral over
`θ ∈ [0, 2π]`. -/
theorem circleIntegral_eq_intervalIntegral (z v : EuclideanSpace ℂ (Fin n)) (δ : ℝ) :
    (∮ t in C(0, δ), (1 / t ^ 2) • f (z + t • v)) =
      ∫ θ in (0 : ℝ)..2 * π, (circleMap 0 δ θ * I * (1 / circleMap 0 δ θ ^ 2)) •
        f (z + circleMap 0 δ θ • v) := by
  simp only [circleIntegral, deriv_circleMap, smul_smul]

/-- The Cauchy integral of a continuous function is continuous in the base point. -/
theorem continuousOn_circleIntegral (hf : ContinuousOn f U)
    {S : Set (EuclideanSpace ℂ (Fin n))} {v : EuclideanSpace ℂ (Fin n)} {δ : ℝ} (hδ : 0 < δ)
    (hball : ∀ z ∈ S, ∀ t : ℂ, ‖t‖ ≤ δ → z + t • v ∈ U) :
    ContinuousOn (fun z => ∮ t in C(0, δ), (1 / t ^ 2) • f (z + t • v)) S := by
  simp_rw [circleIntegral_eq_intervalIntegral]
  rw [continuousOn_iff_continuous_domRestrict]
  have hcm : ∀ θ, ‖circleMap 0 δ θ‖ ≤ δ := fun θ => by simp [abs_of_pos hδ]
  have hc : Continuous fun θ : ℝ => circleMap 0 δ θ * I * (1 / circleMap 0 δ θ ^ 2) := by
    refine ((continuous_circleMap 0 δ).mul continuous_const).mul ?_
    exact continuous_const.div ((continuous_circleMap 0 δ).pow 2)
      fun θ => pow_ne_zero 2 (circleMap_ne_center hδ.ne')
  have hF : Continuous (Function.uncurry fun (p : S) (θ : ℝ) =>
      (circleMap 0 δ θ * I * (1 / circleMap 0 δ θ ^ 2)) • f ((p : EuclideanSpace ℂ (Fin n)) +
        circleMap 0 δ θ • v)) := by
    refine (hc.comp continuous_snd).smul ?_
    refine hf.comp_continuous ((continuous_subtype_val.comp continuous_fst).add
      (((continuous_circleMap 0 δ).comp continuous_snd).smul continuous_const)) ?_
    rintro ⟨p, θ⟩
    exact hball p p.2 _ (hcm θ)
  exact continuous_parametric_intervalIntegral_of_continuous' hF 0 (2 * π)

/-- A complex differentiable function of several variables is `C¹`. -/
theorem contDiffOn_one_of_differentiableOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ContDiffOn ℂ 1 f U := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨hf, by simp, ?_⟩
  rw [contDiffOn_zero, continuousOn_clm_apply]
  intro v z₀ hz₀
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set δ : ℝ := R / (2 * (‖v‖ + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hball : ∀ z ∈ closedBall z₀ (R / 2), ∀ t : ℂ, ‖t‖ ≤ δ → z + t • v ∈ U := by
    intro z hz t ht
    apply hRU
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖z - z₀‖ ≤ R / 2 := mem_closedBall_iff_norm.mp hz
    have h2 : ‖t • v‖ ≤ δ * ‖v‖ := by
      rw [norm_smul]; gcongr
    have h3 : δ * ‖v‖ < R / 2 := by
      rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    calc ‖z + t • v - z₀‖ = ‖(z - z₀) + t • v‖ := by congr 1; abel
      _ ≤ ‖z - z₀‖ + ‖t • v‖ := norm_add_le _ _
      _ < R := by linarith
  have hK := continuousOn_circleIntegral hf.continuousOn hδ hball
  have heq : EqOn (fun z => fderiv ℂ f z v)
      (fun z => (2 * π * I)⁻¹ • ∮ t in C(0, δ), (1 / t ^ 2) • f (z + t • v))
      (closedBall z₀ (R / 2)) := by
    intro z hz
    simp only
    rw [circleIntegral_eq_two_pi_I_smul_fderiv hU hf hδ (hball z hz), smul_smul,
      inv_mul_cancel₀ (by simp [pi_ne_zero, I_ne_zero]), one_smul]
  exact (((continuousOn_const (c := (2 * π * I)⁻¹)).smul hK).congr heq).continuousAt
    (closedBall_mem_nhds z₀ (by positivity))
    |>.continuousWithinAt

/-- The directional derivatives of a complex differentiable function of several variables are
complex differentiable. -/
theorem differentiableOn_fderiv_apply (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (v : EuclideanSpace ℂ (Fin n)) : DifferentiableOn ℂ (fun z => fderiv ℂ f z v) U := by
  intro z₀ hz₀
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set Q := closedBall z₀ (R / 2)
  have hQU : Q ⊆ U := (closedBall_subset_ball (by linarith)).trans hRU
  have hC1 := contDiffOn_one_of_differentiableOn hU hf
  have hfc : ContinuousOn (fderiv ℂ f) U := hC1.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ (R / 2)).exists_bound_of_continuousOn
    (hfc.mono hQU)
  set Lf : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hLip : LipschitzOnWith Lf f Q := by
    refine Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℂ)
      (fun z hz => hf.differentiableAt (hU.mem_nhds (hQU hz))) (fun z hz => ?_)
      (convex_closedBall _ _)
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hC z hz).trans (le_max_left _ _)
  set δ : ℝ := R / (4 * (‖v‖ + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hball : ∀ z ∈ closedBall z₀ (R / 4), ∀ t : ℂ, ‖t‖ ≤ δ → z + t • v ∈ Q := by
    intro z hz t ht
    rw [mem_closedBall, dist_eq_norm]
    have h1 : ‖z - z₀‖ ≤ R / 4 := mem_closedBall_iff_norm.mp hz
    have h2 : ‖t • v‖ ≤ δ * ‖v‖ := by
      rw [norm_smul]; gcongr
    have h3 : δ * ‖v‖ ≤ R / 4 := by
      rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    calc ‖z + t • v - z₀‖ = ‖(z - z₀) + t • v‖ := by congr 1; abel
      _ ≤ ‖z - z₀‖ + ‖t • v‖ := norm_add_le _ _
      _ ≤ R / 2 := by linarith
  have hcm : ∀ θ, ‖circleMap 0 δ θ‖ ≤ δ := fun θ => by simp [abs_of_pos hδ]
  set c : ℝ → ℂ := fun θ => circleMap 0 δ θ * I * (1 / circleMap 0 δ θ ^ 2) with hcdef
  have hc : Continuous c := by
    refine ((continuous_circleMap 0 δ).mul continuous_const).mul ?_
    exact continuous_const.div ((continuous_circleMap 0 δ).pow 2)
      fun θ => pow_ne_zero 2 (circleMap_ne_center hδ.ne')
  set F : EuclideanSpace ℂ (Fin n) → ℝ → ℂ := fun z θ => c θ • f (z + circleMap 0 δ θ • v)
  have hFc : ∀ z ∈ closedBall z₀ (R / 4), Continuous (F z) := by
    intro z hz
    refine hc.smul (hf.continuousOn.comp_continuous (continuous_const.add
      ((continuous_circleMap 0 δ).smul continuous_const)) fun θ => hQU (hball z hz _ (hcm θ)))
  set F' : ℝ → EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
    fun θ => c θ • fderiv ℂ f (z₀ + circleMap 0 δ θ • v)
  have hz₀' : z₀ ∈ closedBall z₀ (R / 4) := mem_closedBall_self (by positivity)
  have hF'c : Continuous F' := by
    refine hc.smul (hfc.comp_continuous (continuous_const.add
      ((continuous_circleMap 0 δ).smul continuous_const)) fun θ => hQU (hball z₀ hz₀' _ (hcm θ)))
  have hderiv := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (a := 0) (b := 2 * π) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun θ => ‖c θ‖ * Lf) (s := ball z₀ (R / 4))
    (ball_mem_nhds z₀ (by positivity))
    (by
      filter_upwards [ball_mem_nhds z₀ (by positivity : 0 < R / 4)] with z hz
      exact (hFc z (ball_subset_closedBall hz)).aestronglyMeasurable)
    ((hFc z₀ hz₀').intervalIntegrable _ _)
    hF'c.aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ => by
      refine LipschitzOnWith.of_dist_le_mul fun z hz z' hz' => ?_
      have hle := hLip.dist_le_mul _ (hball z (ball_subset_closedBall hz) _ (hcm θ)) _
        (hball z' (ball_subset_closedBall hz') _ (hcm θ))
      rw [dist_eq_norm, dist_eq_norm] at hle
      have hzz : z + circleMap 0 δ θ • v - (z' + circleMap 0 δ θ • v) = z - z' := by abel
      rw [hzz] at hle
      have key : ‖c θ‖ * ‖f (z + circleMap 0 δ θ • v) - f (z' + circleMap 0 δ θ • v)‖ ≤
          ‖c θ‖ * Lf * ‖z - z'‖ := by
        rw [mul_assoc]; gcongr
      simp only [F, dist_eq_norm, ← smul_sub, norm_smul]
      rw [Real.coe_nnabs]
      exact key.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
    ((hc.norm.mul continuous_const).intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun θ _ => by
      have hmem : z₀ + circleMap 0 δ θ • v ∈ U := hQU (hball z₀ hz₀' _ (hcm θ))
      have h1 := (hf.differentiableAt (hU.mem_nhds hmem)).hasFDerivAt.comp z₀
        ((hasFDerivAt_id z₀).add_const (circleMap 0 δ θ • v))
      exact h1.const_smul (c θ))
  have hK : DifferentiableAt ℂ (fun z => ∫ θ in (0 : ℝ)..2 * π, F z θ) z₀ :=
    hderiv.2.differentiableAt
  have heq : (fun z => fderiv ℂ f z v) =ᶠ[𝓝 z₀]
      fun z => (2 * π * I)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, F z θ := by
    filter_upwards [closedBall_mem_nhds z₀ (by positivity : 0 < R / 4)] with z hz
    have := circleIntegral_eq_two_pi_I_smul_fderiv hU hf hδ
      (fun t ht => hQU (hball z hz t ht))
    rw [circleIntegral_eq_intervalIntegral] at this
    simp only [F, c]
    rw [this, smul_smul, inv_mul_cancel₀ (by simp [pi_ne_zero, I_ne_zero]), one_smul]
  exact (((differentiableAt_const ((2 * π * I)⁻¹)).smul hK).congr_of_eventuallyEq
    heq).differentiableWithinAt

end HolomorphicRegularity

section Lifts

variable {n : ℕ} {Z B : Type*} [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℂ (Fin n)) Z]
  [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z]
  [TopologicalSpace B] [ChartedSpace ℂ B] {g : Z → B}

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z] in
set_option backward.isDefEq.respectTransparency false in
/-- If `dg_x₀ w ≠ 0`, then the derivative of `g` read in a chart `φ` of `Z` and a chart `ψ` of `B`
does not vanish on the image of `w` in the chart `φ`. -/
theorem fderiv_chart_comp_ne_zero {ψ : OpenPartialHomeomorph B ℂ}
    (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ B)
    {φ : OpenPartialHomeomorph Z (EuclideanSpace ℂ (Fin n))}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z) {x₀ : Z}
    (hx₀ : x₀ ∈ φ.source) (hgx₀ : g x₀ ∈ ψ.source)
    (hgd : MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀)
    {w : EuclideanSpace ℂ (Fin n)}
    (hw : mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀ w ≠ 0) :
    fderiv ℂ (ψ ∘ g ∘ φ.symm) (φ x₀)
      (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) φ x₀ w) ≠ 0 := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hψ1 := IsManifold.maximalAtlas_subset_of_le h1 hψ
  have hφ1 := IsManifold.maximalAtlas_subset_of_le h1 hφ
  have hψd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ψ (g x₀) :=
    mdifferentiableAt_of_mem_maximalAtlas hψ1 hgx₀
  have hφd := mdifferentiableAt_of_mem_maximalAtlas hφ1 hx₀
  have hφsd := mdifferentiableAt_symm_of_mem_maximalAtlas hφ1 (φ.map_source hx₀)
  have hG : MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (ψ ∘ g) x₀ :=
    hψd.comp x₀ hgd
  have hG' : MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (ψ ∘ g) (φ.symm (φ x₀)) := by
    rwa [φ.left_inv hx₀]
  have hh : MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (ψ ∘ g ∘ φ.symm) (φ x₀) :=
    hG'.comp (φ x₀) hφsd
  have key1 : mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ((ψ ∘ g ∘ φ.symm) ∘ φ) x₀ =
      (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (ψ ∘ g ∘ φ.symm) (φ x₀)).comp
        (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) φ x₀) :=
    mfderiv_comp x₀ hh hφd
  have key0 : mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ((ψ ∘ g ∘ φ.symm) ∘ φ) x₀ =
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (ψ ∘ g) x₀ := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [φ.open_source.mem_nhds hx₀] with z hz
    simp [φ.left_inv hz]
  have key2 : mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (ψ ∘ g) x₀ =
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ (g x₀)).comp (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀) :=
    mfderiv_comp x₀ hψd hgd
  have hψmd : ψ.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) :=
    ⟨fun x hx => (mdifferentiableAt_of_mem_maximalAtlas hψ1 hx).mdifferentiableWithinAt,
      fun y hy => (mdifferentiableAt_symm_of_mem_maximalAtlas hψ1 hy).mdifferentiableWithinAt⟩
  have key3 := hψmd.symm_comp_deriv hgx₀
  rw [show fderiv ℂ (ψ ∘ g ∘ φ.symm) (φ x₀)
      (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) φ x₀ w) =
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (ψ ∘ g ∘ φ.symm) (φ x₀)
        (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) φ x₀ w) by
    rw [mfderiv_eq_fderiv]; rfl]
  intro h0
  apply hw
  have e1 := DFunLike.congr_fun key1 w
  rw [key0, key2] at e1
  have e2 : mfderiv 𝓘(ℂ) 𝓘(ℂ) ψ (g x₀) (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀ w) = 0 :=
    e1.trans h0
  have e3 := DFunLike.congr_fun key3 (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀ w)
  simp only [ContinuousLinearMap.comp_apply] at e3
  rw [e2, map_zero] at e3
  exact e3.symm

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z] in
set_option backward.isDefEq.respectTransparency false in
/-- A tangent vector to a set `S` (read in the preferred chart at `x₀`) is carried by the
derivative of a chart `φ` into every coordinate hyperplane containing `φ (S ∩ φ.source)`. -/
theorem mfderiv_apply_eq_zero_of_mem_tangentCone
    {φ : OpenPartialHomeomorph Z (EuclideanSpace ℂ (Fin n))}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z) {x₀ : Z}
    (hx₀ : x₀ ∈ φ.source) {S : Set Z} {k : Fin n} (hSk : ∀ z ∈ S, z ∈ φ.source → φ z k = 0)
    (hx₀S : φ x₀ k = 0) {w : EuclideanSpace ℂ (Fin n)}
    (hw : w ∈ tangentConeAt ℂ ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).target ∩
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹' S)
      (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₀)) :
    (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
      (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) φ x₀ w) = 0 := by
  have h1 : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hφd := mdifferentiableAt_of_mem_maximalAtlas
    (IsManifold.maximalAtlas_subset_of_le h1 hφ) hx₀
  set p := extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₀
  set T := writtenInExtChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ φ
  have hT : HasFDerivWithinAt T
      (fderivWithin ℂ T (range 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) p)
      (range 𝓘(ℂ, EuclideanSpace ℂ (Fin n))) p :=
    hφd.differentiableWithinAt_writtenInExtChartAt.hasFDerivWithinAt
  rw [hφd.mfderiv_abuse]
  set S' := ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).target ∩
    (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹' S) ∩
      (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹' φ.source
  have hnhds : (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹' φ.source ∈ 𝓝 p := by
    apply (continuousAt_extChartAt_symm x₀).preimage_mem_nhds
    rw [extChartAt_to_inv]
    exact φ.open_source.mem_nhds hx₀
  have hw' : w ∈ tangentConeAt ℂ S' p := by
    rwa [tangentConeAt_inter_nhds hnhds]
  set ℓ : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ := EuclideanSpace.proj k
  have hℓT := (ℓ.hasFDerivAt.comp_hasFDerivWithinAt p (hT.mono (subset_univ S' |>.trans
    (by simp)))).mapsTo_tangent_cone hw'
  have himg : (ℓ ∘ T) '' S' ⊆ {0} := by
    rintro _ ⟨z, ⟨⟨-, hzS⟩, hzs⟩, rfl⟩
    simp only [mem_singleton_iff]
    simp only [Function.comp_apply, T, writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_eq, ℓ, PiLp.proj_apply]
    exact hSk _ hzS hzs
  have hp : (ℓ ∘ T) p = 0 := by
    simp only [Function.comp_apply, T, writtenInExtChartAt, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, id_eq, ℓ, PiLp.proj_apply, p, extChartAt_to_inv]
    exact hx₀S
  have hcone := tangentConeAt_mono himg hℓT
  rw [hp] at hcone
  have hacc : ¬AccPt (0 : ℂ) (𝓟 {0}) := by
    rw [accPt_iff_frequently]
    simp
  have := tangentConeAt_subset_zero hacc hcone
  rw [Set.mem_zero] at this
  exact this

/-- A nonzero value of a linear form on a vector is seen on some coordinate vector along which the
vector has a nonzero component. -/
theorem exists_coord_ne_zero_of_apply_ne_zero {F : Type*} [AddCommGroup F] [Module ℂ F]
    (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] F) {w : EuclideanSpace ℂ (Fin n)} (hw : L w ≠ 0) :
    ∃ j, w j ≠ 0 ∧ L (EuclideanSpace.single j 1) ≠ 0 := by
  have hsum : L w = ∑ j, w j • L (EuclideanSpace.single j 1) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w]
    simp [map_sum, map_smul]
  rw [hsum] at hw
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  exact ⟨j, left_ne_zero_of_smul hj, right_ne_zero_of_smul hj⟩

variable {ι : Type*} {D : ι → Set Z}

omit [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z] in
set_option backward.isDefEq.respectTransparency false in
/-- **A coordinate direction transverse to the fibres and tangent to the strata.** In a chart `φ`
straightening the components of `D` through `x₀`, some coordinate vector `e_j`, with `j` not
among the coordinates of the components through `x₀`, is not killed by the derivative of `g`. -/
theorem exists_good_coordinate
    (hg : MDifferentiable 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g)
    {ψ : OpenPartialHomeomorph B ℂ} (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ B)
    {φ : OpenPartialHomeomorph Z (EuclideanSpace ℂ (Fin n))}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z) {x₀ : Z}
    (hx₀ : x₀ ∈ φ.source) (hgx₀ : g x₀ ∈ ψ.source) {s : Finset ι} (c : s ↪ Fin n)
    (hin : ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0})
    (hstrata : x₀ ∈ ⋃ i, D i → ∃ v ∈ tangentConeAt ℂ
        ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).target ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹' ⋂ (i) (_ : x₀ ∈ D i), D i)
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₀),
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀ v ≠ 0)
    (hsub : x₀ ∉ ⋃ i, D i →
      Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀)) :
    ∃ j : Fin n, (∀ i (hi : i ∈ s), x₀ ∈ D i → c ⟨i, hi⟩ ≠ j) ∧
      fderiv ℂ (ψ ∘ g ∘ φ.symm) (φ x₀) (EuclideanSpace.single j 1) ≠ 0 := by
  obtain ⟨w, hw, hw0⟩ : ∃ w : EuclideanSpace ℂ (Fin n),
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀ w ≠ 0 ∧
      ∀ i (hi : i ∈ s), x₀ ∈ D i →
        (EuclideanSpace.proj (c ⟨i, hi⟩) : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)
          (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) φ x₀ w) = 0 := by
    by_cases hxE : x₀ ∈ ⋃ i, D i
    · obtain ⟨w, hwc, hw⟩ := hstrata hxE
      refine ⟨w, hw, fun i hi hxi => ?_⟩
      have hk := hin ⟨i, hi⟩
      refine mfderiv_apply_eq_zero_of_mem_tangentCone hφ hx₀ (fun z hz hzs => ?_)
        (apply_eq_zero_of_image_eq hk hxi hx₀) hwc
      exact apply_eq_zero_of_image_eq hk (mem_iInter₂.mp hz i hxi) hzs
    · obtain ⟨w, hw⟩ := hsub hxE (1 : ℂ)
      refine ⟨w, by rw [hw]; exact (one_ne_zero : (1 : ℂ) ≠ 0), fun i _ hxi => ?_⟩
      exact absurd (mem_iUnion.mpr ⟨i, hxi⟩) hxE
  have hL := fderiv_chart_comp_ne_zero hψ hφ hx₀ hgx₀ (hg x₀) hw
  obtain ⟨j, hwj, hj⟩ := exists_coord_ne_zero_of_apply_ne_zero
    (fderiv ℂ (ψ ∘ g ∘ φ.symm) (φ x₀) : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] ℂ) hL
  refine ⟨j, fun i hi hxi hij => hwj ?_, hj⟩
  have := hw0 i hi hxi
  rw [hij] at this
  exact this

set_option backward.isDefEq.respectTransparency false in
/-- **Local horizontal lifts.** Near every point `x₀` over the source of a chart `ψ` of `B`, there
is a local `C¹` vector field `V` with `d(ψ ∘ g)(V) = ξ`, tangent to the strata of `D`. In a chart
`φ` straightening the components through `x₀` it is `(ξ / ∂ⱼh) • eⱼ`, for `h = ψ ∘ g ∘ φ⁻¹` and a
coordinate `j` transverse to these components. -/
theorem exists_local_lift [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ Z]
    (hg : MDifferentiable 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g)
    (hD : ∀ x : Z, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z,
      x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
        (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
        ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0})
    {ψ : OpenPartialHomeomorph B ℂ} (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ B) (ξ : ℂ)
    {x₀ : Z} (hgx₀ : g x₀ ∈ ψ.source)
    (hstrata : x₀ ∈ ⋃ i, D i → ∃ v ∈ tangentConeAt ℂ
        ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).target ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀).symm ⁻¹' ⋂ (i) (_ : x₀ ∈ D i), D i)
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x₀ x₀),
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀ v ≠ 0)
    (hsub : x₀ ∉ ⋃ i, D i →
      Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x₀)) :
    ∃ U ∈ 𝓝 x₀, ∃ V : (x : Z) → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x,
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)).tangent 1
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) Z)) U ∧
      ∀ y ∈ U, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) (ψ ∘ g) y (V y) = ξ ∧
        IsTangentToStrataAt D y (V y) := by
  classical
  have h1 : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  obtain ⟨φ, hφ, hx₀s, s, c, hout, hin⟩ := hD x₀
  have hφR := maximalAtlas_complex_subset_real hφ
  have hφR1 := IsManifold.maximalAtlas_subset_of_le h1 hφR
  have hφ1 := IsManifold.maximalAtlas_subset_of_le h1 hφ
  have hψ1 := IsManifold.maximalAtlas_subset_of_le h1 hψ
  obtain ⟨j, hjc, hj⟩ := exists_good_coordinate hg hψ hφ hx₀s hgx₀ c hin hstrata hsub
  set h : EuclideanSpace ℂ (Fin n) → ℂ := ψ ∘ g ∘ φ.symm with hhdef
  set O : Set (EuclideanSpace ℂ (Fin n)) := φ.target ∩ φ.symm ⁻¹' (g ⁻¹' ψ.source)
  have hO : IsOpen O :=
    φ.isOpen_inter_preimage_symm (ψ.open_source.preimage hg.continuous)
  have hGd : ∀ y, g y ∈ ψ.source →
      MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) (ψ ∘ g) y := fun y hy =>
    (mdifferentiableAt_of_mem_maximalAtlas hψ1 hy).comp y (hg y)
  have hhd : DifferentiableOn ℂ h O := by
    intro z hz
    have hm : MDifferentiableAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) h z :=
      (hGd _ hz.2).comp z (mdifferentiableAt_symm_of_mem_maximalAtlas hφ1 hz.1)
    exact (mdifferentiableAt_iff_differentiableAt.1 hm).differentiableWithinAt
  set ej : EuclideanSpace ℂ (Fin n) := EuclideanSpace.single j (1 : ℂ)
  set dh : EuclideanSpace ℂ (Fin n) → ℂ := fun z => fderiv ℂ h z ej
  have hdh : ContDiffOn ℂ 1 dh O :=
    contDiffOn_one_of_differentiableOn hO (differentiableOn_fderiv_apply hO hhd ej)
  set O' := O ∩ dh ⁻¹' {0}ᶜ
  have hO' : IsOpen O' := hdh.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  set W : Set Z := ⋂ i ∈ s, ({_y | x₀ ∈ D i} ∪ (D i)ᶜ)
  have hW : IsOpen W := by
    refine isOpen_biInter_finset fun i _ => (isOpen_const).union ?_
    exact (isClosed_of_snc hD i).isOpen_compl
  set U : Set Z := (φ.source ∩ φ ⁻¹' O') ∩ W
  have hUo : IsOpen U := (φ.isOpen_inter_preimage hO').inter hW
  have hx₀U : x₀ ∈ U := by
    refine ⟨⟨hx₀s, ⟨⟨φ.map_source hx₀s, ?_⟩, ?_⟩⟩, ?_⟩
    · simpa [φ.left_inv hx₀s] using hgx₀
    · exact hj
    · exact mem_iInter₂.mpr fun i _ => em _
  set Uf : EuclideanSpace ℂ (Fin n) → EuclideanSpace ℂ (Fin n) := fun z => (ξ / dh z) • ej
  have hUf : ContDiffOn ℂ 1 Uf O' :=
    (contDiffOn_const.div (hdh.mono inter_subset_left) fun z hz => hz.2).smul contDiffOn_const
  have hUsrc : U ⊆ φ.source := fun y hy => hy.1.1
  have himg : φ '' U ⊆ O' := image_subset_iff.mpr fun y hy => hy.1.2
  refine ⟨U, hUo.mem_nhds hx₀U,
    fun y => mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) φ.symm (φ y)
      (Uf (φ y)),
    contMDiffOn_section_of_chart hφR hUsrc ((hUf.restrict_scalars ℝ).mono himg),
    fun y hy => ⟨?_, ?_⟩⟩
  · -- the lift is horizontal
    have hys := hUsrc hy
    have hz : φ y ∈ O' := himg ⟨y, hy, rfl⟩
    have hyψ : g y ∈ ψ.source := by simpa [φ.left_inv hys] using hz.1.2
    have hGR := mdifferentiableAt_real_of_complex (hGd y hyψ)
    have hsymm := mdifferentiableAt_symm_of_mem_maximalAtlas hφR1 (φ.map_source hys)
    rw [← mfderiv_comp_apply_of_eq _ hGR hsymm (φ.left_inv hys), mfderiv_eq_fderiv]
    have hhz : DifferentiableAt ℂ h (φ y) := hhd.differentiableAt (hO.mem_nhds hz.1)
    rw [show ((ψ ∘ g) ∘ φ.symm) = h from rfl, hhz.fderiv_restrictScalars ℝ]
    change fderiv ℂ h (φ y) ((ξ / dh (φ y)) • ej) = ξ
    rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ _ hz.2
  · -- the lift is tangent to the strata
    intro i hyi φ' hφ' hys' k hk
    have hys := hUsrc hy
    have hi : i ∈ s := by
      by_contra hi
      exact ((hout i hi).subset ⟨hyi, hys⟩ : y ∈ (∅ : Set Z))
    have hx₀i : x₀ ∈ D i := by
      rcases mem_iInter₂.mp hy.2 i hi with h' | h'
      · exact h'
      · exact absurd hyi h'
    have hcj := hjc i hi hx₀i
    have hφ'R1 := IsManifold.maximalAtlas_subset_of_le h1 (maximalAtlas_complex_subset_real hφ')
    have hφ'd := mdifferentiableAt_of_mem_maximalAtlas hφ'R1 hys'
    have hsymm := mdifferentiableAt_symm_of_mem_maximalAtlas hφR1 (φ.map_source hys)
    have hφ'd' : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        φ' (φ.symm (φ y)) := by rwa [φ.left_inv hys]
    have hT : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
        (φ' ∘ φ.symm) (φ y) := hφ'd'.comp _ hsymm
    rw [← mfderiv_comp_apply_of_eq _ hφ'd hsymm (φ.left_inv hys), mfderiv_eq_fderiv]
    have hTd := (mdifferentiableAt_iff_differentiableAt.1 hT).hasFDerivAt
    have hk' := hin ⟨i, hi⟩
    refine map_fderiv_ker_of_mapsTo_ker hTd (ℓ := coordCLM (c ⟨i, hi⟩)) (ℓ' := coordCLM k)
      (U := φ.target ∩ φ.symm ⁻¹' φ'.source)
      ((φ.isOpen_inter_preimage_symm φ'.open_source).mem_nhds
        ⟨φ.map_source hys, by simpa [φ.left_inv hys] using hys'⟩) ?_ ?_ ?_
    · intro z hz hz0
      have hmem := symm_mem_of_image_eq hk' hz.1 hz0
      exact apply_eq_zero_of_image_eq hk hmem hz.2
    · exact apply_eq_zero_of_image_eq hk' hyi hys
    · simp [Uf, ej, coordCLM_apply, hcj]

set_option backward.isDefEq.respectTransparency false in
/-- **Horizontal lifts.** Over a closed set `C` lying over the source of a chart `ψ` of `B`, on
which `g` is a submersion off `E` and a submersion on the strata along `E`, there is a global `C¹`
vector field `V` on `Z` with `d(ψ ∘ g)(V) = ξ` on `C`, tangent to the strata of `D` everywhere. -/
theorem exists_horizontal_field [IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ Z] [T2Space Z]
    [SigmaCompactSpace Z]
    (hg : MDifferentiable 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g)
    (hD : ∀ x : Z, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z,
      x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
        (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
        ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0})
    {ψ : OpenPartialHomeomorph B ℂ} (hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ B) (ξ : ℂ)
    {C : Set Z} (hC : IsClosed C) (hCψ : C ⊆ g ⁻¹' ψ.source)
    (hstrata : ∀ x ∈ C, x ∈ ⋃ i, D i → ∃ v ∈ tangentConeAt ℂ
        ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).target ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' ⋂ (i) (_ : x ∈ D i), D i)
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x),
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x v ≠ 0)
    (hsub : ∀ x ∈ C, x ∉ ⋃ i, D i →
      Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x)) :
    ∃ V : (x : Z) → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)).tangent 1
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) Z)) ∧
      (∀ x ∈ C, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) (ψ ∘ g) x (V x) = ξ) ∧
      IsTangentToStrata D V := by
  set t : (x : Z) → Set (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x) := fun x =>
    {w | (x ∈ C → mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) (ψ ∘ g) x w = ξ) ∧
      IsTangentToStrataAt D x w} with ht
  have hconv : ∀ x, Convex ℝ (t x) := by
    intro x w₁ hw₁ w₂ hw₂ a b ha hb hab
    refine ⟨fun hx => ?_, (hw₁.2.smul a).add (hw₂.2.smul b)⟩
    rw [map_add, map_smul, map_smul, hw₁.1 hx, hw₂.1 hx, ← add_smul, hab, one_smul]
  have hloc : ∀ x₀ : Z, ∃ U ∈ 𝓝 x₀, ∃ V : (x : Z) → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x,
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)).tangent 1
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) Z)) U ∧
      ∀ y ∈ U, V y ∈ t y := by
    intro x₀
    by_cases hx₀ : x₀ ∈ C
    · obtain ⟨U, hU, V, hV, hVt⟩ := exists_local_lift hg hD hψ ξ (hCψ hx₀) (hstrata x₀ hx₀)
        (hsub x₀ hx₀)
      exact ⟨U, hU, V, hV, fun y hy => ⟨fun _ => (hVt y hy).1, (hVt y hy).2⟩⟩
    · refine ⟨Cᶜ, hC.isOpen_compl.mem_nhds hx₀, fun _ => 0, ?_, fun y hy => ⟨fun h => absurd h hy,
        isTangentToStrataAt_zero D y⟩⟩
      exact (contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))).contMDiffOn
  obtain ⟨σ, hσ⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n))) t hconv hloc
  exact ⟨⇑σ, σ.contMDiff, fun x hx => (hσ x).1 hx, fun x => (hσ x).2⟩

end Lifts

section Continuation

/-- **Tube lemma.** The points whose orbit stays in an open set over a compact time interval form
an open set. -/
theorem isOpen_setOf_forall_mem_Icc {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {F : ℝ → X → Y} (hF : Continuous (fun p : ℝ × X => F p.1 p.2)) {U : Set Y} (hU : IsOpen U)
    (a b : ℝ) : IsOpen {x | ∀ s ∈ Icc a b, F s x ∈ U} :=
  let G : C(X × ℝ, Y) := ⟨fun p => F p.2 p.1, hF.comp continuous_swap⟩
  (ContinuousMap.isOpen_setOf_mapsTo isCompact_Icc hU).preimage G.curry.continuous

variable {Z B : Type*} [TopologicalSpace Z] [TopologicalSpace B] [T2Space B]

/-- **Continuation along a curve.** Let `γ` be a continuous curve whose image under `ψ ∘ g` moves
with constant velocity `ζ` while `γ` stays in an open set `O`, and suppose that `O` contains every
point of a set `E` over the closed ball `closedBall c R` of the chart `ψ`. If `γ` stays in `E`, it
keeps moving with velocity `ζ` as long as its image stays in the ball. -/
theorem eq_symm_add_of_forall_hasDerivAt {g : Z → B} (hg : Continuous g)
    {ψ : OpenPartialHomeomorph B ℂ} {c : ℂ} {R : ℝ} (hRt : closedBall c R ⊆ ψ.target)
    {O E : Set Z} (hO : IsOpen O) (hOψ : O ⊆ g ⁻¹' ψ.source)
    (hEO : ∀ x ∈ E, g x ∈ ψ.source → ψ (g x) ∈ closedBall c R → x ∈ O)
    {γ : ℝ → Z} (hγ : Continuous γ) (hγE : ∀ u, γ u ∈ E) {ζ : ℂ}
    (hder : ∀ u, γ u ∈ O → HasDerivAt (fun u => ψ (g (γ u))) ζ u)
    (h0 : g (γ 0) ∈ ψ.source) {s : ℝ} (hs : 0 ≤ s) (hR : ‖ψ (g (γ 0)) - c‖ + s * ‖ζ‖ < R) :
    g (γ s) = ψ.symm (ψ (g (γ 0)) + (s : ℂ) * ζ) := by
  set a : ℝ → ℂ := fun u => ψ (g (γ 0)) + (u : ℂ) * ζ with ha
  have haR : ∀ u ∈ Icc 0 s, a u ∈ ball c R := by
    intro u hu
    rw [mem_ball, dist_eq_norm]
    calc ‖a u - c‖ = ‖(ψ (g (γ 0)) - c) + (u : ℂ) * ζ‖ := by simp only [ha]; ring_nf
      _ ≤ ‖ψ (g (γ 0)) - c‖ + u * ‖ζ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
      _ ≤ ‖ψ (g (γ 0)) - c‖ + s * ‖ζ‖ := by gcongr; exact hu.2
      _ < R := hR
  have hac : Continuous a := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  set G : Set ℝ := {u | g (γ u) = ψ.symm (a u)}
  have hGc : IsClosed (G ∩ Icc 0 s) := by
    have hcont : ContinuousOn (fun u => (g (γ u), ψ.symm (a u))) (Icc 0 s) :=
      (hg.comp hγ).continuousOn.prodMk (ψ.continuousOn_symm.comp hac.continuousOn
        fun u hu => hRt (ball_subset_closedBall (haR u hu)))
    have := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_diagonal
    rw [inter_comm]
    convert this using 1
    ext u
    simp [G, mem_diagonal_iff]
  have hG0 : (0 : ℝ) ∈ G := by
    change g (γ 0) = ψ.symm (a 0)
    simp [ha, ψ.left_inv h0]
  have hstep : ∀ u ∈ G ∩ Ico 0 s, G ∈ 𝓝[>] u := by
    rintro u ⟨hu, hu0, hus⟩
    have hau : a u ∈ closedBall c R := ball_subset_closedBall (haR u ⟨hu0, hus.le⟩)
    have hauT : a u ∈ ψ.target := hRt hau
    have hgu : g (γ u) ∈ ψ.source := by rw [hu]; exact ψ.map_target hauT
    have hψu : ψ (g (γ u)) = a u := by rw [hu, ψ.right_inv hauT]
    have hγO : γ u ∈ O := hEO _ (hγE u) hgu (by rwa [hψu])
    obtain ⟨δ, hδ, hδO⟩ := Metric.mem_nhds_iff.mp (hγ.continuousAt.preimage_mem_nhds
      (hO.mem_nhds hγO))
    rw [Real.ball_eq_Ioo] at hδO
    have hd : ∀ w ∈ Ioo (u - δ) (u + δ), HasDerivAt (fun u => ψ (g (γ u))) ζ w :=
      fun w hw => hder w (hδO hw)
    refine mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset
      (Ioo_mem_nhds (by linarith : u - δ < u) (by linarith : u < u + δ)) fun w hw => ?_)
    have hlin := eq_add_smul_of_hasDerivAt hd
      (show u ∈ Ioo (u - δ) (u + δ) from ⟨by linarith, by linarith⟩) hw
    have hwO : γ w ∈ O := hδO hw
    change g (γ w) = ψ.symm (a w)
    have hψw : ψ (g (γ w)) = a w := by
      rw [hlin, hψu, ha, Complex.real_smul]
      push_cast
      ring
    rw [← hψw, ψ.left_inv (hOψ hwO)]
  exact (hGc.Icc_subset_of_forall_mem_nhdsWithin hG0 hstep) ⟨hs, le_rfl⟩

end Continuation

section Main

variable {n : ℕ} {Z B : Type*} [TopologicalSpace Z] [T2Space Z] [SecondCountableTopology Z]
  [ChartedSpace (EuclideanSpace ℂ (Fin n)) Z] [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z]
  [TopologicalSpace B] [T2Space B] [ChartedSpace ℂ B] [IsManifold 𝓘(ℂ) ∞ B]
  {g : Z → B} {ι : Type*} {D : ι → Set Z}

set_option backward.isDefEq.respectTransparency false in
/-- **Uniform horizontal flows.** Let `g : Z → B` be holomorphic from a complex manifold to a
complex curve, and `E = ⋃ i, D i` a simple normal crossing divisor, proper over `B`, such that `g`
is a submersion near `E` and on the strata of `E`. In the preferred chart `ψ` of `B` at `b`, there
are a time `ε > 0`, a decreasing chain of open sets `Ω k` of `Z`, the first five of them containing
`E` over the disk of radius `ε`, and for each of the directions `ξ = 1, i` a map `F ξ` (the flow
of a horizontal field lifting `ξ`): for `|t| < ε` it moves `Ω (k + 1)` into `Ω k`, translates
`ψ ∘ g` by `t ξ`, is undone by the time `-t` map, preserves every `D i`, and is continuous in time
and initial point on `Ω 1`. -/
theorem exists_horizontal_flows
    (hg : MDifferentiable 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g)
    (hD : ∀ x : Z, ∃ φ ∈ IsManifold.maximalAtlas 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ Z,
      x ∈ φ.source ∧ ∃ (s : Finset ι) (c : s ↪ Fin n),
        (∀ i ∉ s, D i ∩ φ.source = ∅) ∧
        ∀ i : s, φ '' (D i ∩ φ.source) = φ.target ∩ {y | y (c i) = 0})
    (hproper : IsProperMap (fun x : (⋃ i, D i : Set Z) => g x))
    (hsubmersion : ∃ W : Set Z, IsOpen W ∧ (⋃ i, D i) ⊆ W ∧
      ∀ x ∈ W, Function.Surjective (mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x))
    (hstrata : ∀ x ∈ ⋃ i, D i, ∃ v ∈ tangentConeAt ℂ
        ((extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).target ∩
          (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x).symm ⁻¹' ⋂ (i) (_ : x ∈ D i), D i)
        (extChartAt 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) x x),
      mfderiv 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) g x v ≠ 0)
    (b : B) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ (Ω : ℕ → Set Z) (F : ℂ → ℝ → Z → Z),
      (∀ k, IsOpen (Ω k)) ∧ (∀ k, Ω (k + 1) ⊆ Ω k) ∧
      Ω 0 ⊆ g ⁻¹' (chartAt ℂ b).source ∧
      (∀ k ≤ 4, (⋃ i, D i) ∩ g ⁻¹' ((chartAt ℂ b).source ∩
          (chartAt ℂ b) ⁻¹' Metric.ball (chartAt ℂ b b) ε) ⊆ Ω k) ∧
      ∀ ξ ∈ ({1, Complex.I} : Set ℂ),
        (∀ x ∈ Ω 0, F ξ 0 x = x) ∧
        ContinuousOn (fun p : ℝ × Z => F ξ p.1 p.2) (Ioo (-ε) ε ×ˢ Ω 1) ∧
        ∀ k, ∀ x ∈ Ω (k + 1), ∀ t ∈ Ioo (-ε) ε,
          F ξ t x ∈ Ω k ∧ chartAt ℂ b (g (F ξ t x)) = chartAt ℂ b (g x) + t * ξ ∧
          F ξ (-t) (F ξ t x) = x ∧ ∀ i, (F ξ t x ∈ D i ↔ x ∈ D i) := by
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) ∞ Z := isManifold_real_of_complex
  have : LocallyCompactSpace Z := ChartedSpace.locallyCompactSpace (EuclideanSpace ℂ (Fin n)) Z
  have h1 : (1 : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have hgc : Continuous g := hg.continuous
  set E : Set Z := ⋃ i, D i with hEdef
  set ψ := chartAt ℂ b with hψdef
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ∞ B := IsManifold.chart_mem_maximalAtlas b
  have hψ1 := IsManifold.maximalAtlas_subset_of_le h1 hψ
  set c := ψ b with hcdef
  obtain ⟨W, hWo, hEW, hWs⟩ := hsubmersion
  -- a closed disk in the chart
  obtain ⟨R, hR, hRt⟩ : ∃ R > 0, closedBall c R ⊆ ψ.target := by
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp
      (ψ.open_target.mem_nhds (ψ.map_source (mem_chart_source ℂ b)))
    exact ⟨r / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hrt⟩
  -- the part of `E` over the closed disk is compact
  have hKB : IsCompact (ψ.symm '' closedBall c R) :=
    (isCompact_closedBall c R).image_of_continuousOn (ψ.continuousOn_symm.mono hRt)
  set L : Set Z := Subtype.val '' ((fun x : E => g x) ⁻¹' (ψ.symm '' closedBall c R))
  have hLc : IsCompact L := (hproper.isCompact_preimage hKB).image continuous_subtype_val
  have hLmem : ∀ x ∈ E, g x ∈ ψ.source → ψ (g x) ∈ closedBall c R → x ∈ L := by
    intro x hx hxs hxR
    exact ⟨⟨x, hx⟩, ⟨ψ (g x), hxR, ψ.left_inv hxs⟩, rfl⟩
  have hLsub : L ⊆ W ∩ g ⁻¹' ψ.source := by
    rintro _ ⟨⟨x, hx⟩, ⟨y, hy, hyx⟩, rfl⟩
    refine ⟨hEW hx, ?_⟩
    have hyx' : ψ.symm y = g x := hyx
    change g x ∈ ψ.source
    rw [← hyx']
    exact ψ.map_target (hRt hy)
  have hO₁ : IsOpen (W ∩ g ⁻¹' ψ.source) := hWo.inter (ψ.open_source.preimage hgc)
  obtain ⟨K₁, hK₁c, hLK₁, hK₁O₁⟩ := exists_compact_between hLc hO₁ hLsub
  obtain ⟨K₂, hK₂c, hLK₂, hK₂K₁⟩ := exists_compact_between hLc isOpen_interior hLK₁
  -- horizontal fields over `K₁`
  have hfield : ∀ ξ : ℂ, ∃ V : (x : Z) → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin n)).tangent 1
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) Z)) ∧
      (∀ x ∈ K₁, mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) (ψ ∘ g) x (V x) = ξ) ∧
      IsTangentToStrata D V := fun ξ =>
    exists_horizontal_field hg hD hψ ξ hK₁c.isClosed (fun x hx => (hK₁O₁ hx).2)
      (fun x _ hxE => hstrata x hxE) (fun x hx _ => hWs x (hK₁O₁ hx).1)
  choose V hVs hVξ hVt using hfield
  -- a cutoff, equal to one on `K₂` and supported in `K₁`
  obtain ⟨χ, hχ0, hχ1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed
    𝓘(ℝ, EuclideanSpace ℂ (Fin n)) (n := 1) isOpen_interior.isClosed_compl hK₂c.isClosed
    (disjoint_compl_left_iff_subset.mpr hK₂K₁)
  set V' : ℂ → (x : Z) → TangentSpace 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) x :=
    fun ξ x => χ x • V ξ x with hV'def
  have hV's : ∀ ξ, ContMDiff 𝓘(ℝ, EuclideanSpace ℂ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin n)).tangent 1
      (fun x => (⟨x, V' ξ x⟩ : TangentBundle 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) Z)) := fun ξ =>
    χ.contMDiff.smul_section (hVs ξ)
  have hV'K : ∀ ξ, ∀ x ∉ K₁, V' ξ x = 0 := by
    intro ξ x hx
    have : χ x = 0 := hχ0 (fun h => hx (interior_subset h))
    simp [hV'def, this]
  have hV't : ∀ ξ, IsTangentToStrata D (V' ξ) := fun ξ => (hVt ξ).smul χ
  -- the flows
  have hflow := fun ξ => exists_global_flow (hV's ξ) hK₁c (hV'K ξ)
  choose F hF0 hFint hFgrp hFcont hFout using hflow
  set O : Set Z := interior K₂
  have hOψ : O ⊆ g ⁻¹' ψ.source := fun x hx => (hK₁O₁ (hK₂K₁ (interior_subset hx) |>
    interior_subset)).2
  have hGd : ∀ y ∈ O, MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) (ψ ∘ g) y :=
    fun y hy => mdifferentiableAt_real_of_complex
      ((mdifferentiableAt_of_mem_maximalAtlas hψ1 (hOψ hy)).comp y (hg y))
  have hderO : ∀ ξ x u, F ξ u x ∈ O → HasDerivAt (fun u => ψ (g (F ξ u x))) ξ u := by
    intro ξ x u hu
    have h := hasDerivAt_comp_of_hasMFDerivAt (hFint ξ x u) (hGd _ hu)
    have hχy : χ (F ξ u x) = 1 := hχ1 (interior_subset hu)
    have hK : F ξ u x ∈ K₁ := interior_subset (hK₂K₁ (interior_subset hu))
    have : mfderiv 𝓘(ℝ, EuclideanSpace ℂ (Fin n)) 𝓘(ℝ, ℂ) (ψ ∘ g) (F ξ u x)
        (V' ξ (F ξ u x)) = ξ := by
      simp only [hV'def, hχy, one_smul]
      exact hVξ ξ _ hK
    rw [this] at h
    exact h
  have hDinv : ∀ ξ x t i, F ξ t x ∈ D i ↔ x ∈ D i := by
    intro ξ x t i
    have := mem_iff_of_isMIntegralCurve_of_isTangentToStrata hD (hV's ξ) (hV't ξ) (hFint ξ x) i t
    rwa [hF0] at this
  have hEO : ∀ y ∈ E, g y ∈ ψ.source → ψ (g y) ∈ closedBall c R → y ∈ O :=
    fun y hy h1 h2 => hLK₂ (hLmem y hy h1 h2)
  have hcurve : ∀ ξ x, Continuous fun u => F ξ u x := fun ξ x =>
    (hFcont ξ).comp (continuous_id.prodMk continuous_const)
  -- trajectories through `E` over the disk move linearly
  have hFE : ∀ ξ : ℂ, ‖ξ‖ = 1 → ∀ x ∈ E, g x ∈ ψ.source → ∀ s : ℝ,
      ‖ψ (g x) - c‖ + |s| < R →
        F ξ s x ∈ E ∧ g (F ξ s x) ∈ ψ.source ∧ ψ (g (F ξ s x)) = ψ (g x) + s * ξ := by
    intro ξ hξ x hx hxs s hs
    have hEmem : ∀ u, F ξ u x ∈ E := fun u => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨i, (hDinv ξ x u i).2 hi⟩
    have key : g (F ξ s x) = ψ.symm (ψ (g x) + s * ξ) := by
      rcases le_or_gt 0 s with h0 | h0
      · have := eq_symm_add_of_forall_hasDerivAt hgc hRt isOpen_interior hOψ hEO (hcurve ξ x)
          hEmem (hderO ξ x) (by rwa [hF0]) h0
          (by rw [hF0, hξ, mul_one]; rwa [abs_of_nonneg h0] at hs)
        rwa [hF0] at this
      · have hder' : ∀ u, F ξ (-u) x ∈ O →
            HasDerivAt (fun u => ψ (g (F ξ (-u) x))) (-ξ) u := by
          intro u hu
          have h' := (hderO ξ x (-u) hu).scomp u (hasDerivAt_neg u)
          rw [neg_one_smul] at h'
          exact h'
        have hγ0 : F ξ (-0) x = x := by rw [neg_zero, hF0]
        have := eq_symm_add_of_forall_hasDerivAt (γ := fun u => F ξ (-u) x) hgc hRt
          isOpen_interior hOψ hEO ((hcurve ξ x).comp continuous_neg) (fun u => hEmem _) hder'
          (show g (F ξ (-0) x) ∈ ψ.source by rwa [hγ0]) (s := -s) (by linarith)
          (show ‖ψ (g (F ξ (-0) x)) - c‖ + -s * ‖-ξ‖ < R by
            rw [hγ0, norm_neg, hξ, mul_one]; rwa [abs_of_neg h0] at hs)
        simp only [neg_neg, hγ0] at this
        rw [this]
        congr 1
        push_cast
        ring
    have hT : ψ (g x) + s * ξ ∈ ψ.target := by
      apply hRt
      rw [mem_closedBall, dist_eq_norm]
      calc ‖ψ (g x) + s * ξ - c‖ = ‖(ψ (g x) - c) + s * ξ‖ := by ring_nf
        _ ≤ ‖ψ (g x) - c‖ + |s| := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ R := hs.le
    refine ⟨hEmem s, by rw [key]; exact ψ.map_target hT, by rw [key, ψ.right_inv hT]⟩
  have hξnorm : ∀ ξ ∈ ({1, Complex.I} : Set ℂ), ‖ξ‖ = 1 := by
    intro ξ hξ
    rcases hξ with rfl | rfl <;> simp
  -- the chain of neighbourhoods
  set ε : ℝ := R / 6 with hεdef
  have hε : 0 < ε := by positivity
  set Ω₀ : Set Z := O ∩ (fun x => ψ (g x)) ⁻¹' ball c R
  let Ω : ℕ → Set Z := fun k => Nat.rec Ω₀ (fun _ S => S ∩ {x | ∀ ξ ∈ ({1, Complex.I} : Set ℂ),
    ∀ s ∈ Icc (-ε) ε, F ξ s x ∈ S}) k
  have hΩ0 : Ω 0 = Ω₀ := rfl
  have hΩs : ∀ k, Ω (k + 1) = Ω k ∩ {x | ∀ ξ ∈ ({1, Complex.I} : Set ℂ),
      ∀ s ∈ Icc (-ε) ε, F ξ s x ∈ Ω k} := fun k => rfl
  have hΩo : ∀ k, IsOpen (Ω k) := by
    intro k
    induction k with
    | zero =>
      rw [hΩ0]
      exact (ψ.continuousOn.comp hgc.continuousOn fun x hx => hOψ hx).isOpen_inter_preimage
        isOpen_interior isOpen_ball
    | succ k ih =>
      rw [hΩs]
      have hset : {x | ∀ ξ ∈ ({1, Complex.I} : Set ℂ), ∀ s ∈ Icc (-ε) ε, F ξ s x ∈ Ω k} =
          {x | ∀ s ∈ Icc (-ε) ε, F 1 s x ∈ Ω k} ∩
            {x | ∀ s ∈ Icc (-ε) ε, F Complex.I s x ∈ Ω k} := by
        ext x
        simp only [mem_insert_iff, mem_singleton_iff, mem_ofPred_eq, mem_inter_iff,
          forall_eq_or_imp, forall_eq]
      rw [hset]
      exact ih.inter ((isOpen_setOf_forall_mem_Icc (hFcont 1) ih _ _).inter
        (isOpen_setOf_forall_mem_Icc (hFcont Complex.I) ih _ _))
  have hΩsub : ∀ k, Ω (k + 1) ⊆ Ω k := fun k => by rw [hΩs]; exact inter_subset_left
  have hΩ0sub : ∀ k, Ω k ⊆ Ω 0 := by
    intro k
    induction k with
    | zero => exact subset_rfl
    | succ k ih => exact (hΩsub k).trans ih
  have hclaim : ∀ k : ℕ, ∀ x ∈ E, g x ∈ ψ.source → ‖ψ (g x) - c‖ < R - k * ε → x ∈ Ω k := by
    intro k
    induction k with
    | zero =>
      intro x hx hxs hxd
      simp only [CharP.cast_eq_zero, zero_mul, sub_zero] at hxd
      refine ⟨hEO x hx hxs ?_, ?_⟩
      · exact mem_closedBall_iff_norm.mpr hxd.le
      · exact mem_ball_iff_norm.mpr hxd
    | succ k ih =>
      intro x hx hxs hxd
      push_cast at hxd
      rw [hΩs]
      refine ⟨ih x hx hxs (by nlinarith), fun ξ hξ s hsI => ?_⟩
      have hs : |s| ≤ ε := abs_le.mpr ⟨hsI.1, hsI.2⟩
      have hk0 : (0 : ℝ) ≤ k * ε := by positivity
      obtain ⟨hE', hs', hψ'⟩ := hFE ξ (hξnorm ξ hξ) x hx hxs s (by linarith)
      refine ih _ hE' hs' ?_
      rw [hψ']
      calc ‖ψ (g x) + s * ξ - c‖ = ‖(ψ (g x) - c) + s * ξ‖ := by ring_nf
        _ ≤ ‖ψ (g x) - c‖ + |s| := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, hξnorm ξ hξ, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ < R - k * ε := by linarith
  refine ⟨ε, hε, Ω, F, hΩo, hΩsub, fun x hx => hOψ hx.1, ?_, fun ξ hξ => ⟨fun x _ => hF0 ξ x,
    (hFcont ξ).continuousOn, fun k x hx t ht => ?_⟩⟩
  · intro k hk x ⟨hx, hxs, hxb⟩
    refine hclaim k x hx hxs ?_
    rw [mem_preimage, mem_ball, dist_eq_norm] at hxb
    have : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    nlinarith
  · have hJ : ∀ u ∈ Ioo (-ε) ε, F ξ u x ∈ Ω k := by
      intro u hu
      rw [hΩs] at hx
      exact hx.2 ξ hξ u (Ioo_subset_Icc_self hu)
    refine ⟨hJ t ht, ?_, ?_, fun i => hDinv ξ x t i⟩
    · have hd : ∀ u ∈ Ioo (-ε) ε, HasDerivAt (fun u => ψ (g (F ξ u x))) ξ u :=
        fun u hu => hderO ξ x u (hΩ0sub k (hJ u hu)).1
      have := eq_add_smul_of_hasDerivAt hd (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩) ht
      simp only [hF0, sub_zero, Complex.real_smul] at this
      exact this
    · rw [hFgrp, neg_add_cancel, hF0]

end Main

end MMP.Analytic.StratifiedFlows
