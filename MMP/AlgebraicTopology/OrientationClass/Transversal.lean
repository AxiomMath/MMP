module

public import MMP.AlgebraicTopology.OrientationClass.Independent
public import MMP.AlgebraicTopology.OrientationClass.ZeroSection
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
/-!
# Orientation classes and transversal maps (Fulton, §19.1)

Let `M ⊆ P` be a closed complex submanifold of codimension `d` of a complex manifold `P`, and
`f : P' → P` a holomorphic map transversal to `M`, so that `M' = f⁻¹(M)` is a closed complex
submanifold of `P'` of codimension `d`. Then `f^* u_{M,P} = u_{M',P'}` in
`H^{2d}(P', P' - M')`. In particular, for a holomorphic section `s` of a holomorphic vector
bundle `E` of rank `r` on `P` transversal to the zero section, with zero locus `M`,
`u_{M,P} = s^* u_E`.

The proof rests on a **disc criterion** (`IsOrientationClass.eval_comp_affineSimplex_eq_one`):
if `u` is the orientation class of `M`, a representing relative cocycle of `u` takes the value
`1` on `A ∘ Δ` for every oriented affine simplex `Δ` around `0` in `ℂ^d` and every continuous
"transversal disc" `A : ℂ^d → P` through `x ∈ M` meeting `M` only at `0`, differentiable at `0` in
the chart at `x` with an injective derivative complementary to the tangent space of `M` and
complex linear modulo it. (The fibre discs of a compatible tubular neighbourhood are such discs,
which is how `IsOrientationClass` is phrased.) For a transversal `f`, the composite `f ∘ A'` of
a transversal disc of `M'` is a transversal disc of `M`: the derivative `D` of `f` maps the
tangent cone of `M'` into that of `M` and induces a surjection, hence (both have dimension `d`)
an isomorphism, of the normal spaces `E'/T_{x'}M' → E/T_{f x'}M`.

## Main definitions

* `MMP.sectionHom`: a continuous section of a vector bundle, as a map into the total space.
* `MMP.IsTransversalTo`: a map `f : P' → P` of charted spaces modelled on complex
  normed spaces is holomorphic at every point of `f⁻¹(M)` and transversal to `M` there:
  `Df(T_{x'}P') + T_{f x'}M = T_{f x'}P`.

## Main results

* `MMP.IsOrientationClass.eval_comp_affineSimplex_eq_one`: the disc criterion.
* `MMP.IsOrientationClass.pullback_of_isTransversalTo`: **`f^* u_{M,P} =
  u_{M',P'}`** for `f` transversal to `M`.
* `MMP.isOrientationClass_pullback_thomClass_of_isTransversalTo`:
  **`u_{M,P} = s^* u_E`** for a section `s` transversal to the zero section.

## Implementation notes

The tangent space `T_x M` of `M` at `x` is the tangent cone of `M` in the chart at `x`
(`tangentConeAt`), as in `TubularNeighbourhood.IsOrientationCompatible`; the derivative of `f`
is Mathlib's `mfderiv` for the models `𝓘(ℂ, E')`, `𝓘(ℂ, E)` (holomorphic: `MDifferentiableAt`),
which in these charts is the Fréchet derivative of `chartAt E (f x) ∘ f ∘ (chartAt E' x).symm`.
The hypothesis that `M' = f⁻¹(M)` is a closed complex submanifold of codimension `d` with normal
bundle `N'` is the datum of a compatible tubular neighbourhood `φ' : N' → P'` with fibre of rank
`d`, as in `IsOrientationClass`. The section `s` is a continuous map `P → E` of the base into the
total space with `π ∘ s = id`; its zero locus is `s⁻¹(0_E)`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
* [R. Bott, L. Tu, *Differential forms in algebraic topology*][botttu1982], §6.
-/

@[expose] public noncomputable section

open Set Bundle CategoryTheory Topology Finsupp Manifold

universe u

namespace MMP

open SingularChain SingularCochain ThomClass

section DiscCriterion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] {M : Set P}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

/-- **Disc criterion.** If `u` is the orientation class of `M ⊆ P` (relative to a compatible
tubular neighbourhood `φ`) and `α` is a relative cocycle representing it, then `α` takes the value
`1` on `A ∘ Δ` for every oriented affine simplex `Δ` around `0` in `ℂ^d` and every continuous disc
`A : ℂ^d → P` with `A 0 = x ∈ M`, meeting `M` only at `0`, differentiable at `0` in the chart at
`x` with an injective derivative `L` whose image is complementary to the tangent cone `W` of `M`
at `x` and which is complex linear modulo `W`. -/
theorem IsOrientationClass.eval_comp_affineSimplex_eq_one {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u)
    {α : Simplex P (2 * Module.finrank ℂ F) → R}
    (hα : α ∈ relCocycles R (Mᶜ : Set P) (2 * Module.finrank ℂ F))
    (hrep : relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * Module.finrank ℂ F) u =
      Submodule.Quotient.mk ⟨α, hα⟩)
    {x : P} (hx : x ∈ M) (A : C(Fin (Module.finrank ℂ F) → ℂ, P)) (hA0 : A 0 = x)
    (hAM : ∀ v, A v ∈ M → v = 0) {L : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] E}
    (hA : HasFDerivAt (fun v ↦ chartAt E x (A v)) L 0) (hinj : Function.Injective L)
    (W : Submodule ℂ E)
    (hTW : tangentConeAt ℝ (chartAt E x '' (M ∩ (chartAt E x).source)) (chartAt E x x) = W)
    (hc : IsCompl (LinearMap.range (L : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] E))
      (W.restrictScalars ℝ))
    (hl : ∀ (c : ℂ) (v : Fin (Module.finrank ℂ F) → ℂ), L (c • v) - c • L v ∈ W)
    {v : Fin (2 * Module.finrank ℂ F + 1) → (Fin (Module.finrank ℂ F) → ℂ)}
    (hv : IsOrientedSimplexAroundZero (complexOrientationBasis (Module.finrank ℂ F)) v) :
    eval α (single (A.comp (affineSimplex v)) 1) = 1 := by
  have hu' := (isThomClass_thomPullback_iff R φ hα hrep).1 hu.2
  obtain ⟨ψ₀, L₀, hL₀, hinj₀, W₀, hTW₀, hc₀, hl₀⟩ := hu.1 ⟨x, hx⟩
  obtain rfl : W₀ = W := SetLike.coe_injective (hTW₀.symm.trans hTW)
  obtain ⟨k, p, hpL, hpL', hpW⟩ := exists_frameChange W₀ L₀ L hc₀ hc hinj₀ hinj hl₀ hl
    (ContinuousLinearEquiv.refl ℂ _)
  let B := φ.fibreDisc ⟨x, hx⟩ (k.trans ψ₀)
  let kL : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ F) → ℂ) :=
    (k : (Fin (Module.finrank ℂ F) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ F) → ℂ)).restrictScalars ℝ
  have hB : HasFDerivAt (fun v ↦ chartAt E x (B v)) (L₀.comp kL) 0 := by
    have hL0 : HasFDerivAt (fun v ↦ chartAt E x (φ (TotalSpace.mk ⟨x, hx⟩ (ψ₀ v)))) L₀
        (kL 0) := by
      rwa [map_zero]
    exact hL0.comp 0 kL.hasFDerivAt
  have hT : tangentConeAt ℝ (chartAt E x '' (M ∩ (chartAt E x).source)) (chartAt E x x) ⊆
      LinearMap.ker (p : E →ₗ[ℝ] (Fin (Module.finrank ℂ F) → ℂ)) := by
    rw [hTW₀]
    exact fun w hw ↦ LinearMap.mem_ker.2 (hpW w hw)
  obtain ⟨δ, hδ, hloc⟩ := exists_eval_comp_eq_of_hasFDerivAt (M := M) B A
    (φ.fibreDisc_zero ⟨x, hx⟩ _) hA0 hB hA p (fun w ↦ hpL w) (fun w ↦ by simpa using hpL' w) hT
  obtain ⟨c, hc0, hcδ⟩ := exists_range_affineSimplex_smul_subset_ball v hδ
  calc eval α (single (A.comp (affineSimplex v)) 1)
      = eval α (single (A.comp (affineSimplex (c • v))) 1) :=
        eval_comp_affineSimplex_smul A hAM R hα hv hc0
    _ = eval α (single (B.comp (affineSimplex (c • v))) 1) :=
        (hloc R hα _ hcδ fun t ht ↦ (hv.smul hc0).affineSimplex_ne_zero t ht).symm
    _ = 1 := hu' ⟨x, hx⟩ _ _ (hv.smul hc0)

end DiscCriterion

section FrameIndependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {P : TopCat.{u}} [ChartedSpace E P] {M : Set P}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]

/-- The compatibility of a tubular neighbourhood with the complex orientations holds for every
complex frame `ψ : ℂ^d ≅ N_x`: the fibre disc `v ↦ e (φ (ψ v))` is differentiable at `0` with an
injective derivative complementary to the tangent cone `W` of `M` and complex linear modulo
`W`. -/
theorem TubularNeighbourhood.IsOrientationCompatible.exists_hasFDerivAt_fibreDisc
    {φ : TubularNeighbourhood F N} (hφ : φ.IsOrientationCompatible (E := E)) (x : M)
    (ψ : (Fin (Module.finrank ℂ F) → ℂ) ≃L[ℂ] N x) :
    ∃ L : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] E,
      HasFDerivAt (fun v ↦ chartAt E (x : P) (φ.fibreDisc x ψ v)) L 0 ∧
        Function.Injective L ∧
        ∃ W : Submodule ℂ E,
          tangentConeAt ℝ (chartAt E (x : P) '' (M ∩ (chartAt E (x : P)).source))
              (chartAt E (x : P) x) = W ∧
          IsCompl (LinearMap.range (L : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] E))
            (W.restrictScalars ℝ) ∧
          ∀ (c : ℂ) (v : Fin (Module.finrank ℂ F) → ℂ), L (c • v) - c • L v ∈ W := by
  obtain ⟨ψ₀, L₀, hL₀, hinj₀, W, hTW, hc₀, hl₀⟩ := hφ x
  set h := ψ.trans ψ₀.symm
  let hL₁ : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ F) → ℂ) :=
    (h : (Fin (Module.finrank ℂ F) → ℂ) →L[ℂ] (Fin (Module.finrank ℂ F) → ℂ)).restrictScalars ℝ
  have hh : ∀ v, hL₁ v = h v := fun v ↦ rfl
  have hfun : (fun v ↦ chartAt E (x : P) (φ.fibreDisc x ψ v)) =
      (fun v ↦ chartAt E (x : P) (φ (TotalSpace.mk x (ψ₀ v)))) ∘ hL₁ := funext fun w ↦ by
    simp [TubularNeighbourhood.fibreDisc_apply, hL₁, h]
  have hL0 : HasFDerivAt (fun v ↦ chartAt E (x : P) (φ (TotalSpace.mk x (ψ₀ v)))) L₀
      (hL₁ 0) := by
    rwa [map_zero]
  refine ⟨L₀.comp hL₁, hfun ▸ hL0.comp 0 hL₁.hasFDerivAt, hinj₀.comp h.injective, W, hTW, ?_,
    fun c v ↦ ?_⟩
  · have hr : LinearMap.range ((L₀.comp hL₁ : (Fin (Module.finrank ℂ F) → ℂ) →L[ℝ] E) :
        (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] E) =
        LinearMap.range (L₀ : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℝ] E) := by
      ext y
      simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
        Function.comp_apply]
      exact ⟨fun ⟨v, hv⟩ ↦ ⟨hL₁ v, hv⟩, fun ⟨v, hv⟩ ↦ ⟨h.symm v, by simpa [hh] using hv⟩⟩
    rwa [hr]
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, hh, map_smul]
    exact hl₀ c (h v)

end FrameIndependence

section Transversal

/-- **Transversality on normal spaces.** Let `W ⊆ E`, `W' ⊆ E'` be complex subspaces of the same
codimension `r` (witnessed by real linear injections `L₀ : ℂ^r → E`, `L : ℂ^r → E'` complementary
to them and complex linear modulo them), and `D : E' → E` complex linear with `D(W') ⊆ W` and
`D(E') + W = E`. Then `D ∘ L` is again injective, complementary to `W` and complex linear modulo
`W`: `D` induces an isomorphism `E'/W' ≅ E/W`. -/
theorem injective_isCompl_comp_of_transversal {E E' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] {r : ℕ}
    (W : Submodule ℂ E) (W' : Submodule ℂ E') (D : E' →L[ℂ] E)
    (hDW : ∀ w ∈ W', D w ∈ W) (hD : ∀ e, ∃ w, e - D w ∈ W)
    (L₀ : (Fin r → ℂ) →L[ℝ] E)
    (hc₀ : IsCompl (LinearMap.range (L₀ : (Fin r → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ))
    (hinj₀ : Function.Injective L₀) (hl₀ : ∀ (c : ℂ) v, L₀ (c • v) - c • L₀ v ∈ W)
    (L : (Fin r → ℂ) →L[ℝ] E')
    (hc : IsCompl (LinearMap.range (L : (Fin r → ℂ) →ₗ[ℝ] E')) (W'.restrictScalars ℝ))
    (hinj : Function.Injective L) (hl : ∀ (c : ℂ) v, L (c • v) - c • L v ∈ W') :
    Function.Injective ((D.restrictScalars ℝ).comp L) ∧
      IsCompl (LinearMap.range (((D.restrictScalars ℝ).comp L : (Fin r → ℂ) →L[ℝ] E) :
        (Fin r → ℂ) →ₗ[ℝ] E)) (W.restrictScalars ℝ) ∧
      ∀ (c : ℂ) v,
        (D.restrictScalars ℝ).comp L (c • v) - c • (D.restrictScalars ℝ).comp L v ∈ W := by
  set eL := quotientEquivOfIsCompl W' L hc hinj hl
  set e₀ := quotientEquivOfIsCompl W L₀ hc₀ hinj₀ hl₀
  let Dq : (E' ⧸ W') →ₗ[ℂ] (E ⧸ W) := W'.mapQ W (D : E' →ₗ[ℂ] E) fun w hw ↦ hDW w hw
  have hDq : ∀ y, Dq (W'.mkQ y) = W.mkQ (D y) := fun y ↦ rfl
  have hsurj : Function.Surjective Dq := by
    intro q
    obtain ⟨e, rfl⟩ := W.mkQ_surjective q
    obtain ⟨w, hw⟩ := hD e
    exact ⟨W'.mkQ w, ((Submodule.Quotient.eq W).2 hw).symm⟩
  have : FiniteDimensional ℂ (E' ⧸ W') := LinearEquiv.finiteDimensional eL
  have : FiniteDimensional ℂ (E ⧸ W) := LinearEquiv.finiteDimensional e₀
  have hfr : Module.finrank ℂ (E' ⧸ W') = Module.finrank ℂ (E ⧸ W) := by
    rw [← eL.finrank_eq, ← e₀.finrank_eq]
  have hDinj : Function.Injective Dq :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).2 hsurj
  let G : (Fin r → ℂ) →ₗ[ℂ] (E ⧸ W) := Dq ∘ₗ (eL : (Fin r → ℂ) →ₗ[ℂ] E' ⧸ W')
  have hG : ∀ v, G v = W.mkQ (D (L v)) := fun v ↦ by
    change Dq (quotientEquivOfIsCompl W' L hc hinj hl v) = _
    rw [quotientEquivOfIsCompl_apply]
    exact hDq _
  have hGinj : Function.Injective G := hDinj.comp eL.injective
  have hGsurj : Function.Surjective G := hsurj.comp eL.surjective
  refine ⟨fun v w h ↦ hGinj (by rw [hG, hG]; exact congrArg W.mkQ h), ⟨?_, ?_⟩, fun c v ↦ ?_⟩
  · rw [Submodule.disjoint_def]
    rintro y ⟨v, rfl⟩ hy
    obtain rfl : v = 0 :=
      hGinj (by rw [hG, map_zero]; exact (Submodule.Quotient.mk_eq_zero W).2 hy)
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro e _
    obtain ⟨v, hv⟩ := hGsurj (W.mkQ e)
    rw [hG] at hv
    rw [show e = D (L v) + (e - D (L v)) by abel]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ((Submodule.Quotient.eq W).1 hv.symm)
  · simpa [map_sub, map_smul] using hDW _ (hl c v)

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E'] {P P' : Type*} [TopologicalSpace P] [TopologicalSpace P'] [ChartedSpace E P]
  [ChartedSpace E' P']

/-- For a map holomorphic at `x` (Mathlib's `MDifferentiableAt` for the models `𝓘(ℂ, E')`,
`𝓘(ℂ, E)`), its derivative `mfderiv` is the Fréchet derivative of
`chartAt E (f x) ∘ f ∘ (chartAt E' x).symm` at `chartAt E' x x`. -/
theorem hasFDerivAt_chartAt_comp_of_mdifferentiableAt {f : P' → P} {x : P'}
    (hf : MDifferentiableAt 𝓘(ℂ, E') 𝓘(ℂ, E) f x) :
    HasFDerivAt (fun z ↦ chartAt E (f x) (f ((chartAt E' x).symm z)))
      (mfderiv 𝓘(ℂ, E') 𝓘(ℂ, E) f x : E' →L[ℂ] E) (chartAt E' x x) := by
  have h := hf.hasMFDerivAt
  rw [HasMFDerivAt] at h
  have h2 := h.2
  simp only [modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ] at h2
  exact h2

/-- The derivative of a holomorphic map `f` at `x` maps the tangent cone of `f⁻¹(M)` at `x` into
the tangent cone of `M` at `f x` (both in the charts at these points). -/
theorem mapsTo_tangentConeAt_of_mdifferentiableAt (M : Set P) {f : P' → P} {x : P'}
    (hf : MDifferentiableAt 𝓘(ℂ, E') 𝓘(ℂ, E) f x) :
    MapsTo (fun w : E' ↦ (mfderiv 𝓘(ℂ, E') 𝓘(ℂ, E) f x w : E))
      (tangentConeAt ℝ (chartAt E' x '' (f ⁻¹' M ∩ (chartAt E' x).source)) (chartAt E' x x))
      (tangentConeAt ℝ (chartAt E (f x) '' (M ∩ (chartAt E (f x)).source))
        (chartAt E (f x) (f x))) := by
  have hg := (hasFDerivAt_chartAt_comp_of_mdifferentiableAt hf).restrictScalars ℝ
  have hxs : x ∈ (chartAt E' x).source := mem_chart_source E' x
  have hU : (chartAt E' x).symm ⁻¹' (f ⁻¹' (chartAt E (f x)).source) ∈
      𝓝 (chartAt E' x x) := by
    have hc : ContinuousAt (fun z ↦ f ((chartAt E' x).symm z)) (chartAt E' x x) :=
      ContinuousAt.comp (f := (chartAt E' x).symm) (g := f)
        (by rw [(chartAt E' x).left_inv hxs]; exact hf.continuousAt)
        ((chartAt E' x).continuousAt_symm ((chartAt E' x).map_source hxs))
    exact hc.preimage_mem_nhds (by
      rw [(chartAt E' x).left_inv hxs]
      exact (chartAt E (f x)).open_source.mem_nhds (mem_chart_source E (f x)))
  rw [← tangentConeAt_inter_nhds hU]
  intro w hw
  have h1 := (hg.hasFDerivWithinAt (s := chartAt E' x '' (f ⁻¹' M ∩ (chartAt E' x).source) ∩
    (chartAt E' x).symm ⁻¹' (f ⁻¹' (chartAt E (f x)).source))).mapsTo_tangent_cone hw
  rw [(chartAt E' x).left_inv hxs] at h1
  refine tangentConeAt_mono ?_ h1
  rintro _ ⟨_, ⟨⟨y, ⟨hyM, hys⟩, rfl⟩, hyU⟩, rfl⟩
  have hy : (chartAt E' x).symm (chartAt E' x y) = y := (chartAt E' x).left_inv hys
  simp only [mem_preimage, hy] at hyU
  exact ⟨f y, ⟨hyM, hyU⟩, by beta_reduce; rw [hy]⟩

variable (E E') in
/-- A map `f : P' → P` of charted spaces modelled on complex normed spaces is *transversal to*
`M ⊆ P` (Fulton, §19.1) if at every point `x ∈ f⁻¹(M)` it is holomorphic (Mathlib's
`MDifferentiableAt` for the models `𝓘(ℂ, E')`, `𝓘(ℂ, E)`) and
`Df(T_x P') + T_{f x} M = T_{f x} P`: every vector of `E` is the image of a vector of `E'` under
the derivative `mfderiv`, modulo the tangent cone of `M` at `f x` in the chart at `f x` (its
tangent space `T_{f x} M`, for a submanifold). -/
def IsTransversalTo (f : P' → P) (M : Set P) : Prop :=
  ∀ x ∈ f ⁻¹' M, MDifferentiableAt 𝓘(ℂ, E') 𝓘(ℂ, E) f x ∧
    ∀ v : E, ∃ w : E', v - (show E' →L[ℂ] E from mfderiv 𝓘(ℂ, E') 𝓘(ℂ, E) f x) w ∈
      tangentConeAt ℝ (chartAt E (f x) '' (M ∩ (chartAt E (f x)).source)) (chartAt E (f x) (f x))

end Transversal

section Pullback

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {P P' : TopCat.{u}} [ChartedSpace E P] [ChartedSpace E' P'] {M : Set P}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {N : M → Type u} [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
  [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
  (R : Type u) [CommRing R]

/-- Evaluating the pullback `g^* α` of an `n`-cochain along `g : Y' ⟶ Y` on a singular simplex
`σ` of `Y'` is evaluating `α` on the simplex `g ∘ σ` of `Y`. -/
lemma eval_cochainPullback_single {Y' Y : TopCat.{u}} (g : Y' ⟶ Y) {n : ℕ}
    (α : Simplex Y n → R) (σ : Simplex Y' n) :
    eval (cochainPullback R g n α) (single σ 1) = eval α (single (g.hom.comp σ) 1) := by
  simp only [linearCombination_single, one_smul]
  rfl

/-- **The orientation class pulls back along transversal maps** (Fulton, §19.1): let `M ⊆ P`,
`f : P' → P` a map of complex manifolds holomorphic at the points of `M' = f⁻¹(M)` and transversal
to `M` there (`MMP.IsTransversalTo`), and `M'` a submanifold of `P'` of the same
codimension `d` with normal bundle `N'`, i.e. with a tubular neighbourhood `φ' : N' → P'` of rank
`d` compatible with the complex orientations. If `u` is the orientation class `u_{M,P}` (relative
to a compatible `φ`), then `f^* u ∈ H^{2d}(P', P' - M')` is the orientation class
`u_{M',P'}`: `f^* u_{M,P} = u_{M',P'}`. (For `M'` closed, the orientation class is unique,
`MMP.IsOrientationClass.eq`.) -/
theorem IsOrientationClass.pullback_of_isTransversalTo (f : P' ⟶ P)
    (hf : IsTransversalTo E E' f M) {φ : TubularNeighbourhood F N}
    {u : cohomologyWithSupports R (ModuleCat.of R R) P M (2 * Module.finrank ℂ F : ℕ)}
    (hu : IsOrientationClass E R φ u)
    {N' : (f ⁻¹' M : Set P') → Type u} [∀ x, AddCommGroup (N' x)] [∀ x, Module ℂ (N' x)]
    [∀ x, TopologicalSpace (N' x)] [TopologicalSpace (TotalSpace F N')] [FiberBundle F N']
    [_root_.VectorBundle ℂ F N'] (φ' : TubularNeighbourhood (P := P') F N')
    (hφ' : φ'.IsOrientationCompatible (E := E')) :
    IsOrientationClass E' R φ'
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f M
        (2 * Module.finrank ℂ F : ℕ)).hom u) := by
  refine ⟨hφ', ?_⟩
  obtain ⟨⟨α, hα⟩, hrep⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R (Mᶜ : Set P) (2 * Module.finrank ℂ F) u)
  have hsub : ((f ⁻¹' M)ᶜ : Set P') ⊆ f ⁻¹' (Mᶜ : Set P) := fun _ hx ↦ hx
  have hα' : cochainPullback R f (2 * Module.finrank ℂ F) α ∈
      relCocycles R ((f ⁻¹' M)ᶜ : Set P') (2 * Module.finrank ℂ F) :=
    cochainPullback_mem_relCocycles f hsub hα
  have hrep' : relativeSingularCohomologyEquiv R ((f ⁻¹' M)ᶜ : Set P') (2 * Module.finrank ℂ F)
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) f M
        (2 * Module.finrank ℂ F : ℕ)).hom u) =
      Submodule.Quotient.mk ⟨cochainPullback R f (2 * Module.finrank ℂ F) α, hα'⟩ :=
    (relativeSingularCohomologyEquiv_map (R := R) f hsub (2 * Module.finrank ℂ F) u).trans
      (by rw [← hrep, relCohomologyMap_mk])
  rw [isThomClass_thomPullback_iff R φ' hα' hrep']
  intro x' ψ' v hv
  rw [eval_cochainPullback_single]
  obtain ⟨hfd, htr⟩ := hf x' x'.2
  set D : E' →L[ℂ] E := mfderiv 𝓘(ℂ, E') 𝓘(ℂ, E) f x' with hDdef
  -- the fibre disc of `φ'` at `x'`
  obtain ⟨L', hL', hinj', W', hTW', hc', hl'⟩ := hφ'.exists_hasFDerivAt_fibreDisc x' ψ'
  -- the normal data of `M` at `f x'`
  obtain ⟨ψ₀, L₀, -, hinj₀, W, hTW, hc₀, hl₀⟩ := hu.1 ⟨f x', x'.2⟩
  have hDW : ∀ w ∈ W', D w ∈ W := fun w hw ↦ by
    have h := mapsTo_tangentConeAt_of_mdifferentiableAt M hfd
      (show w ∈ tangentConeAt ℝ (chartAt E' (x' : P') '' (f ⁻¹' M ∩ (chartAt E' (x' : P')).source))
        (chartAt E' (x' : P') x') from hTW' ▸ hw)
    exact (hTW ▸ h : D w ∈ (W : Set E))
  have hD : ∀ e, ∃ w, e - D w ∈ W := fun e ↦ by
    obtain ⟨w, hw⟩ := htr e
    exact ⟨w, (hTW ▸ hw : e - D w ∈ (W : Set E))⟩
  obtain ⟨hinjD, hcD, hlD⟩ := injective_isCompl_comp_of_transversal W W' D hDW hD L₀ hc₀ hinj₀
    hl₀ L' hc' hinj' hl'
  -- the disc `f ∘ φ'(ψ' ·)` through `f x' ∈ M`
  let A : C(Fin (Module.finrank ℂ F) → ℂ, P) := f.hom.comp (φ'.fibreDisc x' ψ')
  have hA0 : A 0 = f x' := congrArg f (φ'.fibreDisc_zero x' ψ')
  have hAM : ∀ w, A w ∈ M → w = 0 := fun w hw ↦ φ'.eq_zero_of_fibreDisc_mem x' ψ' w hw
  have hA : HasFDerivAt (fun w ↦ chartAt E (f x') (A w)) ((D.restrictScalars ℝ).comp L') 0 := by
    have hg := (hasFDerivAt_chartAt_comp_of_mdifferentiableAt hfd).restrictScalars ℝ
    rw [← congrArg (chartAt E' (x' : P')) (φ'.fibreDisc_zero x' ψ')] at hg
    have hcomp := hg.comp (0 : Fin (Module.finrank ℂ F) → ℂ) hL'
    refine hcomp.congr_of_eventuallyEq ?_
    have hmem : φ'.fibreDisc x' ψ' ⁻¹' (chartAt E' (x' : P')).source ∈
        𝓝 (0 : Fin (Module.finrank ℂ F) → ℂ) :=
      (φ'.fibreDisc x' ψ').continuous.continuousAt.preimage_mem_nhds (by
        rw [φ'.fibreDisc_zero]
        exact (chartAt E' (x' : P')).open_source.mem_nhds (mem_chart_source E' (x' : P')))
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, A, ContinuousMap.comp_apply]
    rw [(chartAt E' (x' : P')).left_inv hw]
  exact hu.eval_comp_affineSimplex_eq_one R hα hrep.symm x'.2 A hA0 hAM hA hinjD W hTW hcD hlD hv

end Pullback

section Section

section SectionHom

variable {B : Type u} [TopologicalSpace B] {F : Type*} {V : B → Type u}
  [TopologicalSpace (TotalSpace F V)]

/-- A continuous section `s` of a vector bundle `V` on `B`, as a continuous map
`B → V` into the total space. -/
def sectionHom {s : (x : B) → V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x)) :
    TopCat.of B ⟶ TopCat.of (TotalSpace F V) :=
  TopCat.ofHom ⟨fun x ↦ TotalSpace.mk' F x (s x), hs⟩

@[simp]
lemma sectionHom_apply {s : (x : B) → V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (x : B) : sectionHom hs x = TotalSpace.mk' F x (s x) :=
  rfl

/-- A point `x` lies in the preimage of the zero section under a section `s` iff `s x = 0`. -/
lemma mem_sectionHom_preimage_range_zeroSection_iff [∀ x, AddCommGroup (V x)] {s : (x : B) → V x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x)) {x : B} :
    x ∈ sectionHom hs ⁻¹' range (zeroSection F V) ↔ s x = 0 :=
  ThomClass.mem_range_zeroSection_iff F V

end SectionHom

variable {B : Type u} [TopologicalSpace B]
  {HB : Type*} [NormedAddCommGroup HB] [NormedSpace ℂ HB] [FiniteDimensional ℂ HB]
  [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {V : B → Type u} [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [_root_.VectorBundle ℂ F V]

/-- **The orientation class of the zero locus of a transversal section** (Fulton, §19.1): let `V`
be a vector bundle of rank `r` on a complex manifold `B` (charts modelled on `HB`) and `s` a
section holomorphic at its zeros and transversal to the zero section there (`s : B → V` is
`MMP.IsTransversalTo` the zero section `0_V`, for the charts
`totalSpaceChartedSpace` of the total space), with zero locus
`M = s⁻¹(0_V) = {x | s x = 0}` (`mem_sectionHom_preimage_range_zeroSection_iff`), a submanifold of
codimension `r` with normal bundle `N`, i.e. with a tubular neighbourhood `φ : N → B` of rank `r`
compatible with the complex orientations. Then `u_{M,B} = s^* u_V` in `H^{2r}(B, B - M)`: the
pull-back `s^* u_V` of the Thom class is the orientation class of `M`. -/
theorem isOrientationClass_pullback_thomClass_of_isTransversalTo (R : Type u) [CommRing R]
    {s : (x : B) → V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    {N : (sectionHom hs ⁻¹' range (zeroSection F V) : Set B) → Type u}
    [∀ x, AddCommGroup (N x)] [∀ x, Module ℂ (N x)] [∀ x, TopologicalSpace (N x)]
    [TopologicalSpace (TotalSpace F N)] [FiberBundle F N] [_root_.VectorBundle ℂ F N]
    (φ : TubularNeighbourhood (P := TopCat.of B) F N)
    (htr : letI := totalSpaceChartedSpace (HB := HB) (F := F) (E := V)
      IsTransversalTo (HB × F) HB (sectionHom hs) (range (zeroSection F V)))
    (hφ : φ.IsOrientationCompatible (E := HB)) :
    IsOrientationClass HB R φ
      ((cohomologyWithSupports.pullback R (ModuleCat.of R R) (sectionHom hs)
        (range (zeroSection F V)) (2 * Module.finrank ℂ F : ℕ)).hom (thomClass R F V)) := by
  let _ := totalSpaceChartedSpace (HB := HB) (F := F) (E := V)
  exact (isOrientationClass_zeroSection_thomClass F V R).pullback_of_isTransversalTo R
    (sectionHom hs) htr φ hφ

end Section

end MMP
