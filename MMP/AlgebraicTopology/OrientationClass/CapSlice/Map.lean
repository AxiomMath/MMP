module

public import MMP.AlgebraicTopology.OrientationClass.CapSlice
public import MMP.AlgebraicTopology.OrientationClass.CapSlice.Chart

/-!
# The slice parametrization of a complex submanifold (Fulton, §19.1)

Let `M` be a complex submanifold of the complex manifold `P`, `u` its orientation class, `x ∈ M`,
`e'` a chart of `M` at `x` and `e` the chart of `P` at `x`. Choose a complex complement `K(F)` of
the tangent space `T_x M = g'(e' x)(E')`, `g = e ∘ e'⁻¹`, and a homeomorphism-like `ρ : F → F`
onto a bounded set with `ρ(0) = 0`, `ρ'(0) = id`. For a small chart ball `U ⊆ M` at `x` and a small
`c > 0`, the map
`f : U × F → P`, `f (y, w) = e⁻¹(e y + c K (ρ w))`
is continuous, restricts to the inclusion on `U × {0}`, meets `M` only on `U × {0}` (by the inverse
function theorem for `(z, w) ↦ g z + K w`), and its fibre discs are transversal discs of `M`.
Hence `f^* u = pr^* u₀`.

## Main results

* `MMP.IsOrientationClass.exists_sliceMap`, and
  `MMP.IsOrientationClass.exists_sliceMap_radialShrink` for `ρ = radialShrink`.
-/

@[expose] public noncomputable section

open Set Bundle CategoryTheory Filter Topology Metric Manifold

universe u

namespace MMP

open MMP

open BorelMooreCap ThomClass

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] [IsManifold 𝓘(ℂ, E) 1 P] {M : Set P}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] [FiniteDimensional ℂ E']
  [ChartedSpace E' M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

/-- A partial homeomorphism is an open map on an open subset of its source. -/
theorem isOpenMap_restrict_opens_of_subset_source {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) (U : TopologicalSpace.Opens X)
    (hU : (U : Set X) ⊆ e.source) : IsOpenMap fun y : U ↦ e y := fun S hS ↦ by
  rw [show (fun y : U ↦ e y) '' S = e '' (Subtype.val '' S) by rw [image_image]]
  exact e.isOpen_image_of_subset_source (U.isOpen.isOpenMap_subtype_val S hS)
    (by rintro _ ⟨y, -, rfl⟩; exact hU y.2)

/-- A map `f = e⁻¹ ∘ Φ ∘ T`, with `e`, `Φ` partial homeomorphisms and `T` an open injective map
into the source of `Φ` landing in the target of `e`, is an open embedding once continuous. -/
theorem isOpenEmbedding_of_eq_symm_comp {α X Y Z : Type*} [TopologicalSpace α]
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : OpenPartialHomeomorph X Z) (Φ : OpenPartialHomeomorph Y Z) {T : α → Y}
    (hTo : IsOpenMap T) (hTi : Function.Injective T) (hTs : ∀ p, T p ∈ Φ.source)
    (hΦT : ∀ p, Φ (T p) ∈ e.target) {f : α → X} (hf : Continuous f)
    (hfT : ∀ p, f p = e.symm (Φ (T p))) : IsOpenEmbedding f := by
  refine .of_continuous_injective_isOpenMap hf (fun p q hpq ↦ ?_) fun S hS ↦ ?_
  · rw [hfT, hfT] at hpq
    have h := congrArg e hpq
    rw [e.right_inv (hΦT p), e.right_inv (hΦT q)] at h
    exact hTi (Φ.injOn (hTs p) (hTs q) h)
  · rw [show f '' S = e.symm '' (Φ '' (T '' S)) by
      rw [image_image, image_image]
      exact image_congr fun p _ ↦ hfT p]
    refine e.symm.isOpen_image_of_subset_source
      (Φ.isOpen_image_of_subset_source (hTo S hS) ?_) ?_
    · rintro _ ⟨p, -, rfl⟩
      exact hTs p
    · rintro _ ⟨_, ⟨p, -, rfl⟩, rfl⟩
      rw [e.symm_source]
      exact hΦT p

/-- **Step (A) of `u_{M,P} ∩ μ_P = μ_M`: the slice parametrization.** Let `M` be a complex
submanifold of `P` with orientation class `u`, `x ∈ M` and `e'` a chart of `M` at `x`. For every
continuous, injective and open `ρ : F → F` with values in the unit ball, `ρ 0 = 0` and
`ρ'(0) = id`, there are an open neighbourhood `U ⊆ e'.source` of `x` in `M`, a complex linear
`K : F → E` and the map `f : U × F → P`, `f (y, w) = e⁻¹(e y + K (ρ w))` (`e` the chart of `P` at
`x`), an open imbedding with `K` injective, `f (y, 0) = y`, `e y + K (ρ w)` in the image of `e`,
`range (g'(e' y)) ⊕ range K = E` for `y ∈ U` (`g = e ∘ e'⁻¹`), `U = e'⁻¹ (ball (e' x) ε)` with the
ball in the image of `e'`, `f⁻¹(M) ⊆ U × {0}`, and `f^* u = pr^* u₀` for the local orientation
class `u₀` of `F` at `0`. -/
theorem IsOrientationClass.exists_sliceMap (hM : IsComplexSubmanifold E E' M)
    {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u) (x : M) {e' : OpenPartialHomeomorph M E'}
    (he' : e' ∈ atlas E' M) (hx : x ∈ e'.source) {ρ : F → F} (hρc : Continuous ρ)
    (hρi : Function.Injective ρ) (hρo : IsOpenMap ρ) (hρ0 : ρ 0 = 0)
    (hρd : HasFDerivAt ρ (ContinuousLinearMap.id ℝ F) 0) (hρb : ∀ w, ‖ρ w‖ < 1) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧ (U : Set M) ⊆ e'.source ∧
      ∃ (K : F →L[ℂ] E) (f : TopCat.of (TopCat.of U × TopCat.of F) ⟶ P), Function.Injective K ∧
        (∀ p, f p = (chartAt E (x : P)).symm (chartAt E (x : P) ((p.1 : M) : P) + K (ρ p.2))) ∧
        (∀ y : U, f (y, 0) = ((y : M) : P)) ∧ IsOpenEmbedding f ∧
        (∀ p : TopCat.of (TopCat.of U) × TopCat.of F,
          chartAt E (x : P) ((p.1 : M) : P) + K (ρ p.2) ∈ (chartAt E (x : P)).target) ∧
        (∀ y : U, ((y : M) : P) ∈ (chartAt E (x : P)).source ∧
          IsCompl (LinearMap.range (fderiv ℂ (fun z ↦ chartAt E (x : P) (e'.symm z : P)) (e' y) :
            E' →ₗ[ℂ] E)) (LinearMap.range (K : F →ₗ[ℂ] E))) ∧
        (∃ ε > 0, Metric.ball (e' x) ε ⊆ e'.target ∧
          (U : Set M) = e'.source ∩ e' ⁻¹' Metric.ball (e' x) ε) ∧
        ∃ h : (zeroSlice (TopCat.of U) F)ᶜ ⊆ f ⁻¹' Mᶜ,
          ∀ u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0}
              (2 * Module.finrank ℂ F : ℕ),
            IsLocalOrientationClass R (complexOrientationBasisOf F) (0 : TopCat.of F) u₀ →
            (relativeSingularCohomology.map R (ModuleCat.of R R) f h
                (2 * Module.finrank ℂ F : ℕ)).hom u =
              (cohomologyWithSupports.pullback R (ModuleCat.of R R)
                (prSnd (TopCat.of U) (TopCat.of F)) {0} (2 * Module.finrank ℂ F : ℕ)).hom u₀ := by
  set e := chartAt E (x : P) with he_def
  have hxe : (x : P) ∈ e.source := mem_chart_source E (x : P)
  set z₀ := e' x
  have hz₀ : z₀ ∈ e'.target := e'.map_source hx
  have hsx : e'.symm z₀ = x := e'.left_inv hx
  obtain ⟨hgc, hgi⟩ := hM e' he' e (chart_mem_atlas E (x : P)) z₀ hz₀ (by rwa [hsx])
  set g : E' → E := fun z ↦ e (e'.symm z : P)
  set Dg := fderiv ℂ g z₀
  have hg : HasFDerivAt g Dg z₀ := (hgc.differentiableAt one_ne_zero).hasFDerivAt
  obtain ⟨ψ₀, L₀, -, hinj₀, W₀, hTW₀, hc₀, -⟩ := hu.1 x
  have hW₀ : W₀ = LinearMap.range (Dg : E' →ₗ[ℂ] E) :=
    SetLike.coe_injective (hTW₀.symm.trans (tangentConeAt_image_chart_eq_range hx hxe hg hgi))
  have hdim : Module.finrank ℂ F + Module.finrank ℂ (LinearMap.range (Dg : E' →ₗ[ℂ] E)) =
      Module.finrank ℂ E := by
    subst hW₀
    simpa using finrank_add_finrank_of_isCompl hinj₀ hc₀
  obtain ⟨K₁, hK₁i, hK₁c⟩ := exists_injective_isCompl_range (F := F) _ hdim
  set G : E' × F → E := fun p ↦ g p.1 + K₁ p.2
  have hbij := (bijective_coprod_iff Dg K₁).2 ⟨hgi, hK₁i, hK₁c⟩
  have : CompleteSpace E := FiniteDimensional.complete ℂ E
  have : CompleteSpace (E' × F) := FiniteDimensional.complete ℂ (E' × F)
  set A₀ : (E' × F) ≃L[ℂ] E := ContinuousLinearEquiv.ofBijective (Dg.coprod K₁)
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have hA₀ : (A₀ : (E' × F) →L[ℂ] E) = Dg.coprod K₁ := ContinuousLinearMap.ext fun _ ↦ rfl
  have hGs : HasStrictFDerivAt G (A₀ : (E' × F) →L[ℂ] E) (z₀, 0) := by
    rw [hA₀]
    exact hasStrictFDerivAt_add_comp hgc K₁ 0
  set Φ := hGs.toOpenPartialHomeomorph G
  have hΦ : ⇑Φ = G := hGs.toOpenPartialHomeomorph_coe
  have hS : (z₀, (0 : F)) ∈ Φ.source := hGs.mem_toOpenPartialHomeomorph_source
  have hev := eventually_isCompl_range_fderiv hgc K₁ hgi hK₁i hK₁c
  have hO : ∀ᶠ z in 𝓝 z₀, z ∈ e'.target ∧ ((e'.symm z : M) : P) ∈ e.source := by
    refine Filter.Eventually.and (e'.open_target.mem_nhds hz₀) ?_
    have hc' : ContinuousAt (fun z ↦ ((e'.symm z : M) : P)) z₀ :=
      continuous_subtype_val.continuousAt.comp (e'.continuousAt_symm hz₀)
    refine hc'.preimage_mem_nhds ?_
    simpa only [hsx] using e.open_source.mem_nhds hxe
  have hgood : e'.source ∩ e' ⁻¹' {z | (z, (0 : F)) ∈ Φ.source} ∈ 𝓝 x := by
    refine inter_mem (e'.open_source.mem_nhds hx) ((e'.continuousAt hx).preimage_mem_nhds ?_)
    exact (Φ.open_source.preimage (continuous_id.prodMk continuous_const)).mem_nhds hS
  obtain ⟨Q, hQ, hQgood⟩ := (mem_nhds_subtype M x _).1 hgood
  obtain ⟨Q', hQ'Q, hQ'o, hxQ'⟩ := mem_nhds_iff.1 hQ
  have hGc : ContinuousAt G (z₀, 0) := hGs.hasFDerivAt.continuousAt
  have hG0 : G (z₀, 0) = e x := by simp [G, g, hsx]
  have hT : {p : E' × F | p ∈ Φ.source ∧ G p ∈ e.target ∧ e.symm (G p) ∈ Q' ∩ e.source ∧
      (p.1 ∈ e'.target ∧ ((e'.symm p.1 : M) : P) ∈ e.source) ∧
      (Function.Injective (fderiv ℂ g p.1) ∧ IsCompl (LinearMap.range (fderiv ℂ g p.1 :
        E' →ₗ[ℂ] E)) (LinearMap.range (K₁ : F →ₗ[ℂ] E)))} ∈ 𝓝 (z₀, (0 : F)) := by
    have h1 : e.target ∩ e.symm ⁻¹' (Q' ∩ e.source) ∈ 𝓝 (G (z₀, 0)) := by
      rw [hG0]
      refine (e.isOpen_inter_preimage_symm (hQ'o.inter e.open_source)).mem_nhds
        ⟨e.map_source hxe, ?_⟩
      rw [mem_preimage, e.left_inv hxe]
      exact ⟨hxQ', hxe⟩
    have h2 := hGc.preimage_mem_nhds h1
    have h3 : ∀ᶠ p : E' × F in 𝓝 (z₀, 0), (p.1 ∈ e'.target ∧ ((e'.symm p.1 : M) : P) ∈ e.source) ∧
        (Function.Injective (fderiv ℂ g p.1) ∧ IsCompl (LinearMap.range (fderiv ℂ g p.1 :
          E' →ₗ[ℂ] E)) (LinearMap.range (K₁ : F →ₗ[ℂ] E))) :=
      (continuous_fst.tendsto (z₀, (0 : F))).eventually (hO.and hev)
    filter_upwards [Φ.open_source.mem_nhds hS, h2, h3] with p hp1 hp2 hp3
    exact ⟨hp1, hp2.1, hp2.2, hp3⟩
  obtain ⟨ε, hε, hεT⟩ := Metric.mem_nhds_iff.1 hT
  rw [← ball_prod_same] at hεT
  set c : ℝ := ε / 2
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  set K : F →L[ℂ] E := (c : ℂ) • K₁
  have hKw : ∀ w, K w = K₁ ((c : ℂ) • w) := fun w ↦ by simp [K]
  have hcw : ∀ w, (c : ℂ) • ρ w ∈ ball (0 : F) ε := fun w ↦ by
    rw [mem_ball_zero_iff, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (by positivity : (0 : ℝ) < c)]
    have := hρb w
    calc c * ‖ρ w‖ ≤ c * 1 := by gcongr
      _ < ε := by
        simp only [c]
        linarith
  let U : TopologicalSpace.Opens M := ⟨e'.source ∩ e' ⁻¹' ball z₀ ε,
    e'.isOpen_inter_preimage isOpen_ball⟩
  have hUT : ∀ (y : U) (w : F), (e' y, (c : ℂ) • ρ w) ∈ _ := fun y w ↦ hεT ⟨y.2.2, hcw w⟩
  have hyU : ∀ y : U, (y : M) ∈ e'.source := fun y ↦ y.2.1
  have hye : ∀ y : U, ((y : M) : P) ∈ e.source := fun y ↦ by
    simpa only [e'.left_inv (hyU y)] using (hUT y 0).2.2.2.1.2
  have hGy : ∀ (y : U) (w : F), G (e' y, (c : ℂ) • ρ w) = e ((y : M) : P) + K (ρ w) :=
    fun y w ↦ by simp only [G, g, e'.left_inv (hyU y), hKw]
  have htarget : ∀ p : TopCat.of (TopCat.of U) × TopCat.of F,
      e ((p.1 : M) : P) + K (ρ p.2) ∈ e.target := fun p ↦ by
    rw [← hGy]
    exact (hUT p.1 p.2).2.1
  have hcont : Continuous fun p : TopCat.of (TopCat.of U) × TopCat.of F ↦
      e.symm (e ((p.1 : M) : P) + K (ρ p.2)) := by
    have h1 : Continuous fun p : TopCat.of (TopCat.of U) × TopCat.of F ↦ e ((p.1 : M) : P) :=
      e.continuousOn.comp_continuous
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst))
        fun p ↦ hye p.1
    exact e.continuousOn_symm.comp_continuous (h1.add (K.continuous.comp
      (hρc.comp continuous_snd))) htarget
  let f : TopCat.of (TopCat.of U × TopCat.of F) ⟶ P := TopCat.ofHom ⟨_, hcont⟩
  have hf : ∀ p, f p = e.symm (e ((p.1 : M) : P) + K (ρ p.2)) := fun _ ↦ rfl
  have hf0 : ∀ y : U, f (y, 0) = ((y : M) : P) := fun y ↦ by
    rw [hf, hρ0, map_zero, add_zero, e.left_inv (hye y)]
  have hfM : ∀ p, f p ∈ M → p.2 = 0 := by
    rintro ⟨y, w⟩ hm
    have hT' := hUT y w
    have hfQ : f (y, w) ∈ Q' := by
      rw [hf, ← hGy]
      exact hT'.2.2.1.1
    have hgd := hQgood (show (⟨f (y, w), hm⟩ : M) ∈ Subtype.val ⁻¹' Q from hQ'Q hfQ)
    set m : M := ⟨f (y, w), hm⟩
    have h1 : Φ (e' m, 0) = Φ (e' y, (c : ℂ) • ρ w) := by
      rw [hΦ]
      simp only [G, map_zero, add_zero, g, e'.left_inv hgd.1]
      change e (f (y, w)) = _
      rw [hf, ← hGy, e.right_inv hT'.2.1]
    have h2 := Φ.injOn hgd.2 hT'.1 h1
    exact hρi (((smul_eq_zero.1 (congrArg Prod.snd h2).symm).resolve_left hc0).trans hρ0.symm)
  have hh : (zeroSlice (TopCat.of U) F)ᶜ ⊆ f ⁻¹' Mᶜ := fun p hp hm ↦
    hp (mem_singleton_iff.2 (hfM p hm))
  let T : TopCat.of (TopCat.of U) × TopCat.of F → E' × F := fun p ↦ (e' p.1, (c : ℂ) • ρ p.2)
  have hfT : ∀ p, f p = e.symm (Φ (T p)) := fun p ↦ by
    rw [hf, hΦ, hGy]
  have hΦT : ∀ p, Φ (T p) ∈ e.target := fun p ↦ by
    rw [hΦ]
    exact (hUT p.1 p.2).2.1
  have hT1o : IsOpenMap fun y : TopCat.of U ↦ e' (y : M) :=
    isOpenMap_restrict_opens_of_subset_source e' U fun _ hy ↦ hy.1
  have hT2o : IsOpenMap fun w : F ↦ (c : ℂ) • ρ w :=
    (Homeomorph.smulOfNeZero (c : ℂ) hc0).isOpenMap.comp hρo
  have hTo : IsOpenMap T := hT1o.prodMap hT2o
  have hTi : Function.Injective T := by
    rintro ⟨y, w⟩ ⟨y', w'⟩ h
    simp only [T, Prod.mk.injEq] at h
    refine Prod.ext (Subtype.ext ?_) (hρi (smul_right_injective F hc0 h.2))
    exact e'.injOn (hyU y) (hyU y') h.1
  have hfo : IsOpenEmbedding f := isOpenEmbedding_of_eq_symm_comp e Φ hTo hTi
    (fun p ↦ (hUT p.1 p.2).1) hΦT f.hom.continuous hfT
  have hK : Function.Injective K := fun a b hab ↦ by
    rw [hKw, hKw] at hab
    exact smul_right_injective F hc0 (hK₁i hab)
  have hcK : ∀ y : U, IsCompl (LinearMap.range (fderiv ℂ g (e' y) : E' →ₗ[ℂ] E))
      (LinearMap.range (K : F →ₗ[ℂ] E)) := fun y ↦ by
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.range_smul _ _ hc0]
    exact (hUT y 0).2.2.2.2.2
  have hball : Metric.ball z₀ ε ⊆ e'.target := fun z hz ↦
    (hεT (show (z, (0 : F)) ∈ Metric.ball z₀ ε ×ˢ Metric.ball (0 : F) ε from
      ⟨hz, mem_ball_self hε⟩)).2.2.2.1.1
  refine ⟨U, ⟨hx, by simpa [z₀] using hε⟩, fun y hy ↦ hy.1, K, f, hK, hf, hf0, hfo, htarget,
    fun y ↦ ⟨hye y, hcK y⟩, ⟨ε, hε, hball, rfl⟩, hh, fun u₀ hu₀ ↦ ?_⟩
  refine hu.map_eq_pullback_prSnd (TopCat.of U) R E' f hh (fun y ↦ by simp [hf0])
    (fun y ψ ↦ ?_) hu₀
  rw [hf0]
  exact exists_hasFDerivAt_sliceDisc hM he' (chart_mem_atlas E (x : P)) (hyU y) (hye y) K hK
    (hcK y) hρd hρ0 ψ

/-- **Step (A), with `ρ = radialShrink`.** For a complex submanifold `M` of `P` with orientation
class `u`, `x ∈ M` and a chart `e'` of `M` at `x`, there are an open neighbourhood `U ⊆ e'.source`
of `x` in `M`, a complex linear `K : F → E` and the slice map
`f (y, w) = e⁻¹(e y + K (radialShrink w))` (`e` the chart of `P` at `x`), an open imbedding
with `f (y, 0) = y`,
`f⁻¹(M) ⊆ U × {0}` and `f^* u = pr^* u₀`. -/
theorem IsOrientationClass.exists_sliceMap_radialShrink (hM : IsComplexSubmanifold E E' M)
    {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u) (x : M) {e' : OpenPartialHomeomorph M E'}
    (he' : e' ∈ atlas E' M) (hx : x ∈ e'.source) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧ (U : Set M) ⊆ e'.source ∧
      ∃ (K : F →L[ℂ] E) (f : TopCat.of (TopCat.of U × TopCat.of F) ⟶ P), Function.Injective K ∧
        (∀ p, f p = (chartAt E (x : P)).symm
          (chartAt E (x : P) ((p.1 : M) : P) + K (radialShrink p.2))) ∧
        (∀ y : U, f (y, 0) = ((y : M) : P)) ∧ IsOpenEmbedding f ∧
        (∀ p : TopCat.of (TopCat.of U) × TopCat.of F,
          chartAt E (x : P) ((p.1 : M) : P) + K (radialShrink p.2) ∈ (chartAt E (x : P)).target) ∧
        (∀ y : U, ((y : M) : P) ∈ (chartAt E (x : P)).source ∧
          IsCompl (LinearMap.range (fderiv ℂ (fun z ↦ chartAt E (x : P) (e'.symm z : P)) (e' y) :
            E' →ₗ[ℂ] E)) (LinearMap.range (K : F →ₗ[ℂ] E))) ∧
        (∃ ε > 0, Metric.ball (e' x) ε ⊆ e'.target ∧
          (U : Set M) = e'.source ∩ e' ⁻¹' Metric.ball (e' x) ε) ∧
        ∃ h : (zeroSlice (TopCat.of U) F)ᶜ ⊆ f ⁻¹' Mᶜ,
          ∀ u₀ : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of F) {0}
              (2 * Module.finrank ℂ F : ℕ),
            IsLocalOrientationClass R (complexOrientationBasisOf F) (0 : TopCat.of F) u₀ →
            (relativeSingularCohomology.map R (ModuleCat.of R R) f h
                (2 * Module.finrank ℂ F : ℕ)).hom u =
              (cohomologyWithSupports.pullback R (ModuleCat.of R R)
                (prSnd (TopCat.of U) (TopCat.of F)) {0} (2 * Module.finrank ℂ F : ℕ)).hom u₀ :=
  hu.exists_sliceMap R hM x he' hx continuous_radialShrink injective_radialShrink
    isOpenMap_radialShrink radialShrink_zero hasFDerivAt_radialShrink_zero norm_radialShrink_lt_one

end MMP
