module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The zero set of a submersion is a manifold

Let `𝕜` be `ℝ` or `ℂ`, let `E` and `F` be finite-dimensional normed spaces over `𝕜`, let
`U ⊆ E` be open and let `f : U → F` be `C^n` (`1 ≤ n`, `n = ω` allowed) with surjective
derivative at every zero of `f` in `U`. Then the zero set `Z = {x ∈ U | f x = 0}` is a
`C^n` manifold of dimension `dim E - dim F`, modelled on `𝕜^(dim E - dim F)`.

At a zero `z`, let `G = ker f'(z)` and choose a linear projection `P : E → G`. The map
`x ↦ (f x, P x)` has invertible derivative at `z`, so by the inverse function theorem it is a
local diffeomorphism `ψ_z` near `z`; it sends `Z` to `{0} × G`, and `x ↦ P x` is a chart of `Z`
near `z`. Two such charts differ by `k ↦ P₂ (ψ₁⁻¹ (0, k))`, which is `C^n` because the inverse of
`ψ₁` is.

For `𝕜 = ℂ` and `n = ω` (or `n = ∞`), this exhibits the zero set of a holomorphic submersion as
a complex manifold.

## Main definitions

* `MMP.SmoothLevelSet.levelSet U f`: the zero set `{x ∈ U | f x = 0}`.
* `MMP.SmoothLevelSet.chartedSpace`: its charts, modelled on
  `EuclideanSpace 𝕜 (Fin (finrank 𝕜 E - finrank 𝕜 F))`.

## Main results

* `MMP.SmoothLevelSet.isManifold`: the zero set of a `C^n` submersion is a `C^n`
  manifold of dimension `dim E - dim F`.

## Implementation notes

The chart at `z` is built on the restriction of the inverse function theorem's local
homeomorphism to the open set of points at which the derivative of `x ↦ (f x, P x)` is still
invertible, so that its inverse is `C^n` on the whole target.
-/

@[expose] public noncomputable section

open Set Topology Module Manifold

namespace MMP

namespace SmoothLevelSet

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The zero set `{x ∈ U | f x = 0}` of `f` on `U`. -/
def levelSet (U : Set E) (f : E → F) : Set E :=
  {x | x ∈ U ∧ f x = 0}

omit [FiniteDimensional 𝕜 E] in
/-- A point lies in `levelSet U f` iff it lies in `U` and is a zero of `f`. -/
@[simp]
lemma mem_levelSet {U : Set E} {f : E → F} {x : E} : x ∈ levelSet U f ↔ x ∈ U ∧ f x = 0 :=
  Iff.rfl

/-- The hypotheses on `(U, f)`: `U` open, `f` of class `C^n` on `U` with `1 ≤ n`, and the
derivative of `f` surjective at each zero of `f` in `U`. -/
structure IsSubmersionOn (n : WithTop ℕ∞) (U : Set E) (f : E → F) : Prop where
  /-- The set `U` is open. -/
  isOpen : IsOpen U
  /-- The map `f` is `C^n` on `U`. -/
  contDiffOn : ContDiffOn 𝕜 n f U
  /-- The smoothness exponent satisfies `1 ≤ n`. -/
  one_le : 1 ≤ n
  /-- The derivative of `f` is surjective at every zero of `f` in `U`. -/
  surjective : ∀ x ∈ levelSet U f, Function.Surjective (fderiv 𝕜 f x)

variable {n : WithTop ℕ∞} {U : Set E} {f : E → F}

namespace IsSubmersionOn

variable (h : IsSubmersionOn (𝕜 := 𝕜) n U f)

include h

omit [FiniteDimensional 𝕜 E] in
/-- The smoothness exponent of a submersion is nonzero. -/
lemma n_ne_zero : n ≠ 0 :=
  (zero_lt_one.trans_le h.one_le).ne'

omit [FiniteDimensional 𝕜 E] in
/-- A submersion on `U` is `C^n` at every point of `U`. -/
lemma contDiffAt {x : E} (hx : x ∈ U) : ContDiffAt 𝕜 n f x :=
  h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hx)

omit [FiniteDimensional 𝕜 E] in
/-- A submersion on `U` has derivative `fderiv 𝕜 f x` at every point `x` of `U`. -/
lemma hasFDerivAt {x : E} (hx : x ∈ U) : HasFDerivAt f (fderiv 𝕜 f x) x :=
  ((h.contDiffAt hx).differentiableAt h.n_ne_zero).hasFDerivAt

end IsSubmersionOn

variable (𝕜) in
/-- The kernel `G = ker f'(z)` at a zero `z`. -/
abbrev ker (f : E → F) (z : E) : Submodule 𝕜 E := LinearMap.ker (fderiv 𝕜 f z : E →ₗ[𝕜] F)

variable (𝕜) in
/-- A continuous linear projection of `E` onto `ker f'(z)`. -/
def proj (f : E → F) (z : E) : E →L[𝕜] ker 𝕜 f z :=
  LinearMap.toContinuousLinearMap
    (Submodule.projectionOnto _ _ (Classical.choose_spec (ker 𝕜 f z).exists_isCompl))

/-- The projection onto `ker f'(z)` restricts to the identity on `ker f'(z)`. -/
lemma proj_apply_ker (z : E) (x : ker 𝕜 f z) : proj 𝕜 f z x = x :=
  Submodule.projectionOnto_apply_left _ x

variable (𝕜) in
/-- The map `x ↦ (f x, P x)`. -/
def prodFun (f : E → F) (z : E) (x : E) : F × ker 𝕜 f z :=
  (f x, proj 𝕜 f z x)

variable (𝕜) in
/-- The derivative `(f'(x), P)` of `prodFun 𝕜 f z` at `x`. -/
def prodDeriv (f : E → F) (z : E) (x : E) : E →L[𝕜] F × ker 𝕜 f z :=
  (fderiv 𝕜 f x).prod (proj 𝕜 f z)

variable (𝕜) in
/-- The open set of points of `U` at which `x ↦ (f x, P x)` has invertible derivative. -/
def goodSet (U : Set E) (f : E → F) (z : E) : Set E :=
  U ∩ prodDeriv 𝕜 f z ⁻¹' range ((↑) : (E ≃L[𝕜] F × ker 𝕜 f z) → _)

variable (h : IsSubmersionOn (𝕜 := 𝕜) n U f)

include h in
/-- The set `goodSet 𝕜 U f z` is open. -/
lemma isOpen_goodSet (z : E) : IsOpen (goodSet 𝕜 U f z) := by
  have := FiniteDimensional.complete 𝕜 E
  have hcont : ContinuousOn (prodDeriv 𝕜 f z) U :=
    (ContinuousLinearMap.prodL 𝕜 (E := E) (F := F) (G := ker 𝕜 f z)).continuous.comp_continuousOn
      ((h.contDiffOn.continuousOn_fderiv_of_isOpen h.isOpen h.one_le).prodMk continuousOn_const)
  exact hcont.isOpen_inter_preimage h.isOpen ContinuousLinearEquiv.isOpen

/-- The set `goodSet 𝕜 U f z` is contained in `U`. -/
lemma goodSet_subset (z : E) : goodSet 𝕜 U f z ⊆ U := inter_subset_left

include h in
/-- At a zero `z` of `f` in `U`, the derivative `x ↦ (f'(z) x, P x)` is bijective. -/
lemma bijective_prodDeriv {z : E} (hz : z ∈ levelSet U f) :
    Function.Bijective (prodDeriv 𝕜 f z z) := by
  refine ⟨fun x y hxy ↦ ?_, fun ⟨y, k⟩ ↦ ?_⟩
  · simp only [prodDeriv, ContinuousLinearMap.prod_apply, Prod.mk.injEq] at hxy
    have hk : x - y ∈ ker 𝕜 f z := by
      rw [LinearMap.mem_ker, map_sub, ContinuousLinearMap.coe_coe, hxy.1, sub_self]
    have := proj_apply_ker (𝕜 := 𝕜) (f := f) z ⟨x - y, hk⟩
    rw [map_sub, hxy.2, sub_self] at this
    exact sub_eq_zero.mp (congrArg Subtype.val this).symm
  · obtain ⟨e, he⟩ := h.surjective z hz y
    refine ⟨e - proj 𝕜 f z e + k, ?_⟩
    have h₁ : fderiv 𝕜 f z (proj 𝕜 f z e) = 0 := (proj 𝕜 f z e).2
    have h₂ : fderiv 𝕜 f z k = 0 := k.2
    simp only [prodDeriv, ContinuousLinearMap.prod_apply, map_add, map_sub]
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, Prod.fst_sub]
      rw [h₁, h₂, he, sub_zero, add_zero]
    · simp only [Prod.snd_add, Prod.snd_sub]
      rw [proj_apply_ker, proj_apply_ker, sub_self, zero_add]

include h in
/-- A zero `z` of `f` in `U` lies in `goodSet 𝕜 U f z`. -/
lemma mem_goodSet {z : E} (hz : z ∈ levelSet U f) : z ∈ goodSet 𝕜 U f z :=
  ⟨hz.1, (LinearEquiv.ofBijective (prodDeriv 𝕜 f z z : E →ₗ[𝕜] _)
    (bijective_prodDeriv h hz)).toContinuousLinearEquiv, ContinuousLinearMap.ext fun _ ↦ rfl⟩

include h in
/-- The map `x ↦ (f x, P x)` has derivative `prodDeriv 𝕜 f z x` at every point of `U`. -/
lemma hasFDerivAt_prodFun {z x : E} (hx : x ∈ U) :
    HasFDerivAt (prodFun 𝕜 f z) (prodDeriv 𝕜 f z x) x :=
  (h.hasFDerivAt hx).prodMk (proj 𝕜 f z).hasFDerivAt

include h in
/-- The map `x ↦ (f x, P x)` is `C^n` at every point of `U`. -/
lemma contDiffAt_prodFun {z x : E} (hx : x ∈ U) : ContDiffAt 𝕜 n (prodFun 𝕜 f z) x :=
  (h.contDiffAt hx).prodMk (proj 𝕜 f z).contDiff.contDiffAt

/-- The invertible derivative of `x ↦ (f x, P x)` at a good point. -/
def derivEquiv {z x : E} (hx : x ∈ goodSet 𝕜 U f z) : E ≃L[𝕜] F × ker 𝕜 f z :=
  Classical.choose hx.2

/-- The underlying continuous linear map of `derivEquiv hx` is `prodDeriv 𝕜 f z x`. -/
lemma coe_derivEquiv {z x : E} (hx : x ∈ goodSet 𝕜 U f z) :
    (derivEquiv hx : E →L[𝕜] F × ker 𝕜 f z) = prodDeriv 𝕜 f z x :=
  Classical.choose_spec hx.2

include h in
/-- The map `x ↦ (f x, P x)` has derivative `derivEquiv hx` at a good point `x`. -/
lemma hasFDerivAt_derivEquiv {z x : E} (hx : x ∈ goodSet 𝕜 U f z) :
    HasFDerivAt (prodFun 𝕜 f z) (derivEquiv hx : E →L[𝕜] F × ker 𝕜 f z) x :=
  coe_derivEquiv hx ▸ hasFDerivAt_prodFun h hx.1

/-- The local diffeomorphism `ψ_z : x ↦ (f x, P x)` near a zero `z`, restricted to the points at
which its derivative stays invertible. -/
def localDiffeo {z : E} (hz : z ∈ levelSet U f) : OpenPartialHomeomorph E (F × ker 𝕜 f z) :=
  haveI := FiniteDimensional.complete 𝕜 E
  ((contDiffAt_prodFun h (z := z) hz.1).toOpenPartialHomeomorph (prodFun 𝕜 f z)
    (hasFDerivAt_derivEquiv h (mem_goodSet h hz)) h.n_ne_zero).restrOpen
    (goodSet 𝕜 U f z) (isOpen_goodSet h z)

/-- The local diffeomorphism `ψ_z` sends `x` to `(f x, P x)`. -/
lemma localDiffeo_apply {z : E} (hz : z ∈ levelSet U f) (x : E) :
    localDiffeo h hz x = prodFun 𝕜 f z x :=
  rfl

/-- The zero `z` lies in the source of `ψ_z`. -/
lemma mem_localDiffeo_source {z : E} (hz : z ∈ levelSet U f) : z ∈ (localDiffeo h hz).source :=
  haveI := FiniteDimensional.complete 𝕜 E
  ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, mem_goodSet h hz⟩

/-- The source of `ψ_z` is contained in `goodSet 𝕜 U f z`. -/
lemma localDiffeo_source_subset {z : E} (hz : z ∈ levelSet U f) :
    (localDiffeo h hz).source ⊆ goodSet 𝕜 U f z :=
  fun _ hx ↦ hx.2

/-- The inverse of `ψ_z` is `C^n` at every point of its target. -/
lemma contDiffAt_localDiffeo_symm {z : E} (hz : z ∈ levelSet U f) {q : F × ker 𝕜 f z}
    (hq : q ∈ (localDiffeo h hz).target) : ContDiffAt 𝕜 n (localDiffeo h hz).symm q := by
  have := FiniteDimensional.complete 𝕜 E
  have hs : (localDiffeo h hz).symm q ∈ goodSet 𝕜 U f z :=
    localDiffeo_source_subset h hz ((localDiffeo h hz).map_target hq)
  exact (localDiffeo h hz).contDiffAt_symm hq (hasFDerivAt_derivEquiv h hs)
    (contDiffAt_prodFun h hs.1)

/-- The dimension `dim E - dim F` of the zero set. -/
abbrev dim (𝕜 E F : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] : ℕ :=
  finrank 𝕜 E - finrank 𝕜 F

include h in
/-- At a zero `z`, the dimension of `ker f'(z)` equals that of the model
space `𝕜^(dim E - dim F)`. -/
lemma finrank_ker {z : E} (hz : z ∈ levelSet U f) :
    finrank 𝕜 (ker 𝕜 f z) = finrank 𝕜 (EuclideanSpace 𝕜 (Fin (dim 𝕜 E F))) := by
  rw [finrank_euclideanSpace_fin, dim]
  have h1 : finrank 𝕜 (LinearMap.range (fderiv 𝕜 f z : E →ₗ[𝕜] F)) + finrank 𝕜 (ker 𝕜 f z) =
      finrank 𝕜 E :=
    LinearMap.finrank_range_add_finrank_ker _
  have hr : LinearMap.range (fderiv 𝕜 f z : E →ₗ[𝕜] F) = ⊤ :=
    LinearMap.range_eq_top.mpr (h.surjective z hz)
  rw [hr, finrank_top] at h1
  omega

/-- A linear identification of `ker f'(z)` with the model space. -/
def kerEquiv {z : E} (hz : z ∈ levelSet U f) :
    ker 𝕜 f z ≃L[𝕜] EuclideanSpace 𝕜 (Fin (dim 𝕜 E F)) :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_ker h hz)

/-- For `(0, k)` in the target of `ψ_z`, the point `ψ_z⁻¹ (0, k)` lies in the zero set. -/
lemma localDiffeo_symm_mem_levelSet {z : E} (hz : z ∈ levelSet U f) {k : ker 𝕜 f z}
    (hk : ((0 : F), k) ∈ (localDiffeo h hz).target) :
    (localDiffeo h hz).symm (0, k) ∈ levelSet U f :=
  ⟨goodSet_subset z (localDiffeo_source_subset h hz ((localDiffeo h hz).map_target hk)),
    congrArg Prod.fst ((localDiffeo h hz).right_inv hk)⟩

open scoped Classical in
/-- The inverse of the chart at `z`: `k ↦ ψ_z⁻¹ (0, k)`, extended by `z` off the target. -/
def chartInv {z : E} (hz : z ∈ levelSet U f) (k : EuclideanSpace 𝕜 (Fin (dim 𝕜 E F))) :
    levelSet U f :=
  if hk : ((0 : F), (kerEquiv h hz).symm k) ∈ (localDiffeo h hz).target then
    ⟨_, localDiffeo_symm_mem_levelSet h hz hk⟩
  else ⟨z, hz⟩

/-- On the target, `chartInv` is `k ↦ ψ_z⁻¹ (0, k)`. -/
lemma chartInv_of_mem {z : E} (hz : z ∈ levelSet U f) {k : EuclideanSpace 𝕜 (Fin (dim 𝕜 E F))}
    (hk : ((0 : F), (kerEquiv h hz).symm k) ∈ (localDiffeo h hz).target) :
    chartInv h hz k = ⟨_, localDiffeo_symm_mem_levelSet h hz hk⟩ := by
  simp [chartInv, hk]

/-- The chart of the zero set at a zero `z`: `x ↦ P x`, read in the model space. -/
def chart {z : E} (hz : z ∈ levelSet U f) :
    OpenPartialHomeomorph (levelSet U f) (EuclideanSpace 𝕜 (Fin (dim 𝕜 E F))) where
  toFun x := kerEquiv h hz (proj 𝕜 f z x.1)
  invFun := chartInv h hz
  source := {x | x.1 ∈ (localDiffeo h hz).source}
  target := {k | ((0 : F), (kerEquiv h hz).symm k) ∈ (localDiffeo h hz).target}
  map_source' x hx := by
    have := (localDiffeo h hz).map_source hx
    rw [localDiffeo_apply, prodFun, x.2.2] at this
    simpa using this
  map_target' k hk := by
    rw [mem_ofPred_eq, chartInv_of_mem h hz hk]
    exact (localDiffeo h hz).map_target hk
  left_inv' x hx := by
    have hx' : ((0 : F), (kerEquiv h hz).symm (kerEquiv h hz (proj 𝕜 f z x.1))) =
        localDiffeo h hz x.1 := by
      rw [localDiffeo_apply, prodFun, x.2.2, ContinuousLinearEquiv.symm_apply_apply]
    rw [chartInv_of_mem h hz (hx' ▸ (localDiffeo h hz).map_source hx)]
    exact Subtype.ext ((congrArg (localDiffeo h hz).symm hx').trans
      ((localDiffeo h hz).left_inv hx))
  right_inv' k hk := by
    rw [chartInv_of_mem h hz hk]
    have := congrArg Prod.snd ((localDiffeo h hz).right_inv hk)
    rw [localDiffeo_apply, prodFun] at this
    simp only at this
    rw [this, ContinuousLinearEquiv.apply_symm_apply]
  open_source := (localDiffeo h hz).open_source.preimage continuous_subtype_val
  open_target := (localDiffeo h hz).open_target.preimage
    (continuous_const.prodMk (kerEquiv h hz).symm.continuous)
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous fun k : {k | ((0 : F), (kerEquiv h hz).symm k) ∈
        (localDiffeo h hz).target} ↦
        (⟨(localDiffeo h hz).symm (0, (kerEquiv h hz).symm k.1),
          localDiffeo_symm_mem_levelSet h hz k.2⟩ : levelSet U f) :=
      ((localDiffeo h hz).continuousOn_symm.comp_continuous
        (continuous_const.prodMk ((kerEquiv h hz).symm.continuous.comp continuous_subtype_val))
        fun k ↦ k.2).subtype_mk _
    convert hc using 1
    funext k
    exact chartInv_of_mem h hz k.2

/-- The chart at `z` sends `x` to `P x`, read in the model space. -/
lemma chart_apply {z : E} (hz : z ∈ levelSet U f) (x : levelSet U f) :
    chart h hz x = kerEquiv h hz (proj 𝕜 f z x.1) :=
  rfl

/-- The zero `z` lies in the source of the chart at `z`. -/
lemma mem_chart_source {z : E} (hz : z ∈ levelSet U f) :
    (⟨z, hz⟩ : levelSet U f) ∈ (chart h hz).source :=
  mem_localDiffeo_source h hz

/-- On its target, the inverse of the chart at `z` is `k ↦ ψ_z⁻¹ (0, k)`. -/
lemma coe_chart_symm {z : E} (hz : z ∈ levelSet U f) {k : EuclideanSpace 𝕜 (Fin (dim 𝕜 E F))}
    (hk : k ∈ (chart h hz).target) :
    ((chart h hz).symm k : E) = (localDiffeo h hz).symm (0, (kerEquiv h hz).symm k) :=
  congrArg Subtype.val (chartInv_of_mem h hz hk)

/-- The charts of the zero set of a `C^n` submersion, modelled on `𝕜^(dim E - dim F)`. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (EuclideanSpace 𝕜 (Fin (dim 𝕜 E F))) (levelSet U f) where
  atlas := range fun x : levelSet U f ↦ chart h x.2
  chartAt x := chart h x.2
  mem_chart_source x := mem_chart_source h x.2
  chart_mem_atlas x := mem_range_self x

/-- The transition map between two charts of the zero set is `C^n`. -/
lemma contDiffOn_chart_symm_trans {z₁ z₂ : E} (hz₁ : z₁ ∈ levelSet U f)
    (hz₂ : z₂ ∈ levelSet U f) :
    ContDiffOn 𝕜 n ((chart h hz₁).symm.trans (chart h hz₂))
      ((chart h hz₁).symm.trans (chart h hz₂)).source := by
  intro k hk
  have hk₁ : k ∈ (chart h hz₁).target := hk.1
  refine ContDiffAt.contDiffWithinAt ?_
  have heq : ((chart h hz₁).symm.trans (chart h hz₂) : _ → _) =ᶠ[𝓝 k]
      fun k ↦ kerEquiv h hz₂ (proj 𝕜 f z₂ ((localDiffeo h hz₁).symm
        (0, (kerEquiv h hz₁).symm k))) := by
    filter_upwards [(chart h hz₁).open_target.mem_nhds hk₁] with k' hk'
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chart_apply,
      coe_chart_symm h hz₁ hk']
  refine ContDiffAt.congr_of_eventuallyEq ?_ heq
  refine (kerEquiv h hz₂).contDiff.contDiffAt.comp _ ((proj 𝕜 f z₂).contDiff.contDiffAt.comp _ ?_)
  exact ContDiffAt.comp (g := (localDiffeo h hz₁).symm)
    (f := fun k ↦ ((0 : F), (kerEquiv h hz₁).symm k)) k (contDiffAt_localDiffeo_symm h hz₁ hk₁)
    (contDiff_const.prodMk (kerEquiv h hz₁).symm.contDiff).contDiffAt

/-- **The zero set of a submersion is a manifold.** If `f` is `C^n` (`1 ≤ n`) on the open set
`U ⊆ E` with surjective derivative at every zero, the zero set `{x ∈ U | f x = 0}` is a `C^n`
manifold of dimension `dim E - dim F`. -/
theorem isManifold :
    letI := chartedSpace h
    IsManifold 𝓘(𝕜, EuclideanSpace 𝕜 (Fin (dim 𝕜 E F))) n (levelSet U f) := by
  let := chartedSpace h
  refine isManifold_of_contDiffOn _ _ _ ?_
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp, range_id, inter_univ, preimage_id_eq, id_eq]
  exact contDiffOn_chart_symm_trans h x.2 x'.2

end SmoothLevelSet

end MMP
