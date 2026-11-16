module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Complex.Basic

/-!
# Fibrewise linear maps between vector bundles

Let `E₁`, `E₂` be complex topological vector bundles on `B` with finite-dimensional model fibres,
and `φ b : E₁ b →ₗ[ℂ] E₂ b` a family of linear maps. We call `φ` *continuous at* a point `p` of the
total space of `E₁` when the total-space map `p ↦ (π p, φ (π p) p.2)` is.

* A locally finite combination `∑ᶠ i, ρᵢ(b) • φᵢ b` of such families is continuous at `p` if every
  `φᵢ` whose weight `ρᵢ` does not vanish near `π p` is continuous at `p` and `ρᵢ` is continuous at
  `π p` (gluing with a partition of unity).
* If `φ` is continuous along the fibre over `b₀`, the fibres have equal rank, and `φ b₀` is
  injective, then `φ b` is injective for `b` near `b₀`.
* Every linear map between fibres is continuous, so a linear equivalence of fibres is a
  continuous linear equivalence.

## Main results

* `MMP.continuousAt_totalSpace_finsum_smul`
* `MMP.eventually_injective_of_continuousAt_totalSpace`
* `MMP.fibreContinuousLinearEquiv`
-/

@[expose] public noncomputable section

open Bundle Set Topology Filter

namespace MMP

variable {B : Type*} [TopologicalSpace B]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  {E₁ : B → Type*} [∀ b, AddCommMonoid (E₁ b)] [∀ b, Module ℂ (E₁ b)] [∀ b, TopologicalSpace (E₁ b)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle ℂ F₁ E₁]
  {E₂ : B → Type*} [∀ b, AddCommMonoid (E₂ b)] [∀ b, Module ℂ (E₂ b)] [∀ b, TopologicalSpace (E₂ b)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle ℂ F₂ E₂]

variable (F₂) in
/-- The total-space map `p ↦ (π p, φ (π p) p.2)` of a fibrewise map. -/
def totalSpaceMap (φ : ∀ b, E₁ b →ₗ[ℂ] E₂ b) (p : TotalSpace F₁ E₁) : TotalSpace F₂ E₂ :=
  ⟨p.proj, φ p.proj p.2⟩

omit [NormedSpace ℂ F₁] [VectorBundle ℂ F₁ E₁] in
/-- **Gluing fibrewise maps.** A locally finite combination `∑ᶠ i, ρᵢ(b) • φᵢ b` is continuous at
`p₀` if for every `i` with `π p₀` in the support of `ρᵢ`, `ρᵢ` is continuous at `π p₀` and `φᵢ` at
`p₀`. -/
theorem continuousAt_totalSpace_finsum_smul {ι : Type*} (ρ : ι → B → ℂ)
    (hρ : LocallyFinite fun i ↦ Function.support (ρ i)) (φ : ι → ∀ b, E₁ b →ₗ[ℂ] E₂ b)
    (p₀ : TotalSpace F₁ E₁)
    (h : ∀ i, p₀.proj ∈ tsupport (ρ i) →
      ContinuousAt (ρ i) p₀.proj ∧ ContinuousAt (totalSpaceMap F₂ (φ i)) p₀) :
    ContinuousAt (totalSpaceMap F₂ fun b ↦ ∑ᶠ i, ρ i b • φ i b) p₀ := by
  classical
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨FiberBundle.continuous_proj F₁ E₁ |>.continuousAt, ?_⟩
  set b₀ := p₀.proj
  set e := trivializationAt F₂ E₂ b₀
  obtain ⟨t, ht, hfin⟩ := hρ b₀
  set I := hfin.toFinset
  have hb₀ : b₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F₂ E₂ b₀
  have hev : (fun p : TotalSpace F₁ E₁ ↦ (e (totalSpaceMap F₂ (fun b ↦ ∑ᶠ i, ρ i b • φ i b) p)).2)
      =ᶠ[𝓝 p₀] fun p ↦ ∑ i ∈ I, ρ i p.proj • (e (totalSpaceMap F₂ (φ i) p)).2 := by
    have h1 : ∀ᶠ p : TotalSpace F₁ E₁ in 𝓝 p₀, p.proj ∈ t ∩ e.baseSet :=
      (FiberBundle.continuous_proj F₁ E₁).continuousAt.preimage_mem_nhds
        (inter_mem ht (e.open_baseSet.mem_nhds hb₀))
    filter_upwards [h1] with p ⟨hpt, hpe⟩
    have hsupp : (Function.support fun i ↦ ρ i p.proj • φ i p.proj) ⊆ I := fun i hi ↦
      hfin.mem_toFinset.2 ⟨p.proj, fun h0 ↦ hi (by simp only [h0, zero_smul]), hpt⟩
    simp only [totalSpaceMap]
    rw [← e.coe_linearMapAt_of_mem (R := ℂ) hpe |> congrFun |> fun h ↦ h _,
      finsum_eq_sum_of_support_subset _ hsupp, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [LinearMap.smul_apply, map_smul, e.coe_linearMapAt_of_mem hpe]
  refine ContinuousAt.congr ?_ hev.symm
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  by_cases hi : b₀ ∈ tsupport (ρ i)
  · obtain ⟨hρi, hφi⟩ := h i hi
    exact (hρi.comp (FiberBundle.continuous_proj F₁ E₁).continuousAt).smul
      (continuous_snd.continuousAt.comp ((e.continuousOn.continuousAt
        (e.open_source.mem_nhds (e.mem_source.2 hb₀))).comp hφi))
  · have h0' : (fun p : TotalSpace F₁ E₁ ↦ ρ i p.proj • (e (totalSpaceMap F₂ (φ i) p)).2) =ᶠ[𝓝 p₀]
        fun _ ↦ 0 := by
      filter_upwards [(FiberBundle.continuous_proj F₁ E₁).continuousAt.preimage_mem_nhds
        (notMem_tsupport_iff_eventuallyEq.1 hi)] with p hp
      simp_all
    exact continuousAt_const.congr h0'.symm

omit [VectorBundle ℂ F₁ E₁] [(b : B) → TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂]
  [VectorBundle ℂ F₂ E₂] in
/-- **Fibrewise maps given in trivializations.** If near `π p₀`, in linear trivializations `e₁`,
`e₂`, the fibrewise map `φ` is the family `A b : F₁ →L F₂`, continuous at `π p₀`, then `φ` is
continuous at `p₀`. -/
theorem continuousAt_totalSpaceMap_of_trivialization
    (e₁ : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [e₁.IsLinear ℂ]
    (e₂ : Trivialization F₂ (TotalSpace.proj : TotalSpace F₂ E₂ → B)) [e₂.IsLinear ℂ]
    (A : B → F₁ →L[ℂ] F₂) (φ : ∀ b, E₁ b →ₗ[ℂ] E₂ b) {p₀ : TotalSpace F₁ E₁}
    (h₁ : p₀.proj ∈ e₁.baseSet) (h₂ : p₀.proj ∈ e₂.baseSet) (hA : ContinuousAt A p₀.proj)
    (hφ : ∀ᶠ b in 𝓝 p₀.proj, ∀ v, e₂.linearMapAt ℂ b (φ b v) = A b (e₁.linearMapAt ℂ b v)) :
    ContinuousAt (totalSpaceMap F₂ φ) p₀ := by
  have hproj := (FiberBundle.continuous_proj F₁ E₁).continuousAt (x := p₀)
  have hU : ∀ᶠ p : TotalSpace F₁ E₁ in 𝓝 p₀, p.proj ∈ e₁.baseSet ∩ e₂.baseSet ∧
      ∀ v, e₂.linearMapAt ℂ p.proj (φ p.proj v) = A p.proj (e₁.linearMapAt ℂ p.proj v) :=
    hproj.eventually (Filter.Eventually.and
      ((e₁.open_baseSet.inter e₂.open_baseSet).mem_nhds ⟨h₁, h₂⟩) hφ)
  have hev : (fun p : TotalSpace F₁ E₁ ↦ e₂.toOpenPartialHomeomorph.symm
      (p.proj, A p.proj (e₁ p).2)) =ᶠ[𝓝 p₀] totalSpaceMap F₂ φ := by
    filter_upwards [hU] with p ⟨⟨hp₁, hp₂⟩, hpφ⟩
    rw [← e₂.mk_symm hp₂, totalSpaceMap]
    congr 1
    rw [← e₁.coe_linearMapAt_of_mem (R := ℂ) hp₁ |> congrFun |> fun h ↦ h p.2, ← hpφ,
      ← e₂.symmₗ_apply (R := ℂ) hp₂, e₂.symmₗ_linearMapAt hp₂]
  refine ContinuousAt.congr ?_ hev
  have he₁ : ContinuousAt (fun p : TotalSpace F₁ E₁ ↦ (e₁ p).2) p₀ :=
    ContinuousAt.comp (g := Prod.snd) continuous_snd.continuousAt
      (e₁.continuousOn.continuousAt (e₁.open_source.mem_nhds (e₁.mem_source.2 h₁)))
  exact ContinuousAt.comp (g := e₂.toOpenPartialHomeomorph.symm)
    (e₂.toOpenPartialHomeomorph.continuousAt_symm (e₂.mem_target.2 h₂))
    (hproj.prodMk ((hA.comp hproj).clm_apply he₁))

omit [(b : B) → TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁] [VectorBundle ℂ F₁ E₁] in
/-- The linear map of a pulled-back trivialization at `b` is that of the trivialization at
`f b`. -/
lemma pullback_linearMapAt {B' : Type*} [TopologicalSpace B'] (f : C(B', B))
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [e.IsLinear ℂ] {b : B'}
    (hb : f b ∈ e.baseSet) (v : E₁ (f b)) :
    (e.pullback f).linearMapAt ℂ b v = e.linearMapAt ℂ (f b) v := by
  rw [Trivialization.coe_linearMapAt_of_mem _ (show b ∈ (e.pullback f).baseSet from hb),
    Trivialization.coe_linearMapAt_of_mem _ hb]
  rfl

/-- An injective continuous linear endomorphism of a finite-dimensional space is a unit. -/
lemma isUnit_of_injective_clm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {f : V →L[ℂ] V} (hf : Function.Injective f) : IsUnit f :=
  ⟨(ContinuousLinearEquiv.unitsEquiv ℂ V).symm (LinearEquiv.ofBijective (f : V →ₗ[ℂ] V)
    ⟨hf, (f : V →ₗ[ℂ] V).injective_iff_surjective.1 hf⟩).toContinuousLinearEquiv,
    ContinuousLinearMap.ext fun _ ↦ rfl⟩

section FiniteDimensional

variable [FiniteDimensional ℂ F₁] [FiniteDimensional ℂ F₂]

omit [FiniteDimensional ℂ F₂] in
variable (F₁ F₂) in
include F₁ F₂ in
/-- A linear map between fibres of vector bundles with finite-dimensional model fibre is
continuous. -/
lemma continuous_fibre_linearMap {b₁ b₂ : B} (f : E₁ b₁ →ₗ[ℂ] E₂ b₂) : Continuous f := by
  let c₁ := (trivializationAt F₁ E₁ b₁).continuousLinearEquivAt ℂ b₁
    (FiberBundle.mem_baseSet_trivializationAt F₁ E₁ b₁)
  let c₂ := (trivializationAt F₂ E₂ b₂).continuousLinearEquivAt ℂ b₂
    (FiberBundle.mem_baseSet_trivializationAt F₂ E₂ b₂)
  let g : F₁ →ₗ[ℂ] F₂ := (c₂ : E₂ b₂ →ₗ[ℂ] F₂) ∘ₗ f ∘ₗ (c₁.symm : F₁ →ₗ[ℂ] E₁ b₁)
  rw [show ⇑f = c₂.symm ∘ g ∘ c₁ by funext v; simp [g]]
  exact c₂.symm.continuous.comp (g.continuous_of_finiteDimensional.comp c₁.continuous)

variable (F₁ F₂) in
/-- A linear equivalence between fibres of vector bundles with finite-dimensional model fibres, as
a continuous linear equivalence. -/
def fibreContinuousLinearEquiv {b₁ b₂ : B} (f : E₁ b₁ ≃ₗ[ℂ] E₂ b₂) : E₁ b₁ ≃L[ℂ] E₂ b₂ where
  __ := f
  continuous_toFun := continuous_fibre_linearMap F₁ F₂ (f : E₁ b₁ →ₗ[ℂ] E₂ b₂)
  continuous_invFun := continuous_fibre_linearMap F₂ F₁
    (f.symm : E₂ b₂ →ₗ[ℂ] E₁ b₁)

/-- The continuous linear equivalence `fibreContinuousLinearEquiv F₁ F₂ f` agrees with `f`
pointwise. -/
@[simp]
lemma fibreContinuousLinearEquiv_apply {b₁ b₂ : B} (f : E₁ b₁ ≃ₗ[ℂ] E₂ b₂) (v : E₁ b₁) :
    fibreContinuousLinearEquiv F₁ F₂ f v = f v :=
  rfl

omit [FiniteDimensional ℂ F₂] [(b : B) → TopologicalSpace (E₁ b)] [FiberBundle F₁ E₁]
  [VectorBundle ℂ F₁ E₁] [(b : B) → TopologicalSpace (E₂ b)] [FiberBundle F₂ E₂]
  [VectorBundle ℂ F₂ E₂] in
/-- **Continuity of a fibrewise map in trivializations.** If `φ` is continuous along the fibre
over `b₀`, then in linear trivializations `e₁`, `e₂` around `b₀`, the family of maps
`b ↦ ψ ∘ e₂ ∘ φ b ∘ e₁⁻¹ : F₁ →L G` is continuous at `b₀`. -/
theorem continuousAt_linearMapAt_comp_symmₗ {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (ψ : F₂ →L[ℂ] G) (φ : ∀ b, E₁ b →ₗ[ℂ] E₂ b)
    (e₁ : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [e₁.IsLinear ℂ]
    (e₂ : Trivialization F₂ (TotalSpace.proj : TotalSpace F₂ E₂ → B)) [e₂.IsLinear ℂ] {b₀ : B}
    (hb₁ : b₀ ∈ e₁.baseSet) (hb₂ : b₀ ∈ e₂.baseSet)
    (hφ : ∀ v : E₁ b₀, ContinuousAt (totalSpaceMap F₂ φ) (⟨b₀, v⟩ : TotalSpace F₁ E₁)) :
    ContinuousAt (fun b ↦ LinearMap.toContinuousLinearMap
      ((ψ : F₂ →ₗ[ℂ] G) ∘ₗ e₂.linearMapAt ℂ b ∘ₗ φ b ∘ₗ e₁.symmₗ ℂ b)) b₀ := by
  refine continuousAt_clm_apply.2 fun v ↦ ?_
  have hev : (fun b ↦ ψ (e₂ (totalSpaceMap F₂ φ (e₁.toOpenPartialHomeomorph.symm (b, v)))).2)
      =ᶠ[𝓝 b₀] fun b ↦ LinearMap.toContinuousLinearMap
        ((ψ : F₂ →ₗ[ℂ] G) ∘ₗ e₂.linearMapAt ℂ b ∘ₗ φ b ∘ₗ e₁.symmₗ ℂ b) v := by
    filter_upwards [(e₁.open_baseSet.inter e₂.open_baseSet).mem_nhds ⟨hb₁, hb₂⟩]
      with b ⟨h1, h2⟩
    simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_coe, e₂.coe_linearMapAt_of_mem h2, e₁.symmₗ_apply h1]
    rw [← e₁.mk_symm h1]
    rfl
  refine ContinuousAt.congr ?_ hev
  have hsymm : ContinuousAt (fun b ↦ e₁.toOpenPartialHomeomorph.symm (b, v)) b₀ :=
    (e₁.toOpenPartialHomeomorph.continuousAt_symm (e₁.mem_target.2 hb₁)).comp
      (continuousAt_id.prodMk continuousAt_const)
  have hpt : e₁.toOpenPartialHomeomorph.symm (b₀, v) =
      (⟨b₀, e₁.symm b₀ v⟩ : TotalSpace F₁ E₁) := (e₁.mk_symm hb₁ v).symm
  have hφ' : ContinuousAt (totalSpaceMap F₂ φ) (e₁.toOpenPartialHomeomorph.symm (b₀, v)) :=
    hpt ▸ hφ _
  have hsrc : totalSpaceMap F₂ φ (e₁.toOpenPartialHomeomorph.symm (b₀, v)) ∈ e₂.source := by
    rw [e₂.mem_source, hpt]
    exact hb₂
  have h3 : ContinuousAt
      (fun b ↦ totalSpaceMap F₂ φ (e₁.toOpenPartialHomeomorph.symm (b, v))) b₀ :=
    ContinuousAt.comp (g := totalSpaceMap F₂ φ) hφ' hsymm
  have h4 : ContinuousAt
      (fun b ↦ e₂ (totalSpaceMap F₂ φ (e₁.toOpenPartialHomeomorph.symm (b, v)))) b₀ :=
    ContinuousAt.comp (g := e₂) (e₂.continuousOn.continuousAt
      (e₂.open_source.mem_nhds hsrc)) h3
  exact ψ.continuous.continuousAt.comp (continuous_snd.continuousAt.comp h4)

/-- **Injectivity of a fibrewise map is an open condition.** If `φ` is continuous along the fibre
over `b₀`, the model fibres have the same dimension and `φ b₀` is injective, then `φ b` is
injective for every `b` near `b₀`. -/
theorem eventually_injective_of_continuousAt_totalSpace
    (hF : Module.finrank ℂ F₁ = Module.finrank ℂ F₂) (φ : ∀ b, E₁ b →ₗ[ℂ] E₂ b) {b₀ : B}
    (hφ : ∀ v : E₁ b₀, ContinuousAt (totalSpaceMap F₂ φ) (⟨b₀, v⟩ : TotalSpace F₁ E₁))
    (h₀ : Function.Injective (φ b₀)) : ∀ᶠ b in 𝓝 b₀, Function.Injective (φ b) := by
  set e₁ := trivializationAt F₁ E₁ b₀
  set e₂ := trivializationAt F₂ E₂ b₀
  have hb₁ : b₀ ∈ e₁.baseSet := FiberBundle.mem_baseSet_trivializationAt F₁ E₁ b₀
  have hb₂ : b₀ ∈ e₂.baseSet := FiberBundle.mem_baseSet_trivializationAt F₂ E₂ b₀
  let ψ : F₂ ≃L[ℂ] F₁ := ContinuousLinearEquiv.ofFinrankEq hF.symm
  let A : B → F₁ →L[ℂ] F₁ := fun b ↦ LinearMap.toContinuousLinearMap
    ((ψ : F₂ →ₗ[ℂ] F₁) ∘ₗ e₂.linearMapAt ℂ b ∘ₗ φ b ∘ₗ e₁.symmₗ ℂ b)
  have hA : ContinuousAt A b₀ :=
    continuousAt_linearMapAt_comp_symmₗ (ψ : F₂ →L[ℂ] F₁) φ e₁ e₂ hb₁ hb₂ hφ
  have hinj : ∀ b ∈ e₁.baseSet ∩ e₂.baseSet,
      Function.Injective (A b) → Function.Injective (φ b) := by
    rintro b ⟨h1, h2⟩ hAb w w' hww'
    have key : ∀ u, e₁.symmₗ ℂ b (e₁.linearMapAt ℂ b u) = u := fun u ↦ e₁.symmₗ_linearMapAt h1 u
    have : A b (e₁.linearMapAt ℂ b w) = A b (e₁.linearMapAt ℂ b w') := by
      simp only [A, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
        Function.comp_apply, key, hww']
    rw [← key w, ← key w', hAb this]
  have hA₀ : Function.Injective (A b₀) := by
    intro v v' hvv'
    simp only [A, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
      Function.comp_apply] at hvv'
    have h1 := ψ.injective hvv'
    rw [e₂.coe_linearMapAt_of_mem hb₂] at h1
    have h2 := congrArg (e₂.symm b₀) h1
    rw [e₂.symm_apply_apply_mk hb₂, e₂.symm_apply_apply_mk hb₂] at h2
    have h4 := congrArg (e₁.linearMapAt ℂ b₀) (h₀ h2)
    rwa [e₁.linearMapAt_symmₗ hb₁, e₁.linearMapAt_symmₗ hb₁] at h4
  have hdet : ∀ b, (A b).det ≠ 0 → Function.Injective (A b) := fun b hb ↦
    ((Module.End.isUnit_iff _).1
      ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb))).1
  have hdet₀ : (A b₀).det ≠ 0 :=
    ((LinearMap.isUnit_iff_isUnit_det _).1 ((Module.End.isUnit_iff _).2
      ⟨hA₀, (A b₀ : F₁ →ₗ[ℂ] F₁).injective_iff_surjective.1 hA₀⟩)).ne_zero
  filter_upwards [(ContinuousLinearMap.continuous_det.continuousAt.comp hA).eventually_ne hdet₀,
    (e₁.open_baseSet.inter e₂.open_baseSet).mem_nhds ⟨hb₁, hb₂⟩] with b hb hbU
  exact hinj b hbU (hdet b hb)

end FiniteDimensional

end MMP
