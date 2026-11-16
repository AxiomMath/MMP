module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.AlgebraicChartDifferential

/-!
# Morphisms are holomorphic in algebraic charts (Fulton, §19.1)

Let `ι : V → X` be a morphism of schemes over `𝕜 = ℝ` or `ℂ`, and `e`, `e'` algebraic charts of
`V(𝕜)` and `X(𝕜)`. Near a point `q` of the source of `e` with `ι(q)` in the source of `e'`, the
chart expression `e' ∘ ι ∘ e⁻¹` is `C^ω`: the coordinates of `e'` are locally linear in finitely
many regular functions on `X`, and their pull-backs along `ι` are regular functions on `V`, which
are `C^ω` read through `e⁻¹`.

If `ι` is a closed immersion and the model space of `e` is finite dimensional, the derivative of
`e' ∘ ι ∘ e⁻¹` at `e(q)` is injective: on an affine open `U ∋ ι(q)` every regular function on
`ι⁻¹(U)` is the pull-back of one on `U`, so its differential at `q` factors through that
derivative, and these differentials span the dual of the model space of `e`.

## Main results

* `MMP.UnderlyingSpace.IsAlgebraicChart.contDiffAt_comp_mapFun`: `e' ∘ ι ∘ e⁻¹` is
  `C^ω` at `e(q)`.
* `MMP.UnderlyingSpace.IsAlgebraicChart.injective_fderiv_comp_mapFun`: for a closed
  immersion `ι`, its derivative at `e(q)` is injective.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology Set
open scoped ContDiff

universe u

namespace MMP

open MMP

namespace UnderlyingSpace

open MMP.UnderlyingSpace

variable {𝕜 : Type u} [RCLike 𝕜] {V X : Scheme.{u}} [V.Over (Spec (.of 𝕜))]
  [X.Over (Spec (.of 𝕜))] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] (ι : V ⟶ X) [ι.IsOver (Spec (.of 𝕜))]
  {e : OpenPartialHomeomorph (UnderlyingSpace 𝕜 V) E}
  {e' : OpenPartialHomeomorph (UnderlyingSpace 𝕜 X) F} {q : UnderlyingSpace 𝕜 V}

/-- A `𝕜`-point `q` of `V` factors through the open `ι⁻¹(U)` if and only if its image
`mapFun ι q` factors through the open `U` of `X`. -/
lemma _root_.MMP.UnderlyingSpace.top_le_toHom_preimage_preimage_iff (U : X.Opens) :
    ⊤ ≤ q.toHom ⁻¹ᵁ (ι ⁻¹ᵁ U) ↔ ⊤ ≤ (mapFun ι q).toHom ⁻¹ᵁ U := by
  rw [toHom_mapFun, Scheme.Hom.comp_preimage]

namespace IsAlgebraicChart

open MMP.UnderlyingSpace.IsAlgebraicChart

/-- **Morphisms are `C^ω` in algebraic charts.** For a morphism `ι : V → X` over `𝕜` and
algebraic charts `e` of `V(𝕜)` and `e'` of `X(𝕜)`, the chart expression `e' ∘ ι ∘ e⁻¹` is `C^ω`
at `e(q)`, for `q` in the source of `e` with `ι(q)` in the source of `e'`. -/
theorem _root_.MMP.UnderlyingSpace.IsAlgebraicChart.contDiffAt_comp_mapFun (he : IsAlgebraicChart e) (he' : IsAlgebraicChart e')
    (hq : q ∈ e.source) (hq' : mapFun ι q ∈ e'.source) :
    ContDiffAt 𝕜 ω (fun y ↦ e' (mapFun ι (e.symm y))) (e q) := by
  obtain ⟨U, κ, _, a, L, hU, hL⟩ := he'.exists_eq_evalExt _ hq'
  set S := e.target ∩ e.symm ⁻¹' {p : UnderlyingSpace 𝕜 V | ⊤ ≤ p.toHom ⁻¹ᵁ (ι ⁻¹ᵁ U)}
  have hSo : IsOpen S := e.isOpen_inter_preimage_symm (isOpen_setOf_le_preimage _)
  set T := e.target ∩ e.symm ⁻¹' (mapFun ι ⁻¹' e'.source)
  have hTo : IsOpen T :=
    e.isOpen_inter_preimage_symm (e'.open_source.preimage (map (K := 𝕜) ι).continuous)
  have hmem : S ∩ T ∈ 𝓝 (e q) := (hSo.inter hTo).mem_nhds
    ⟨⟨e.map_source hq, by
      simpa [e.left_inv hq] using (top_le_toHom_preimage_preimage_iff ι U).2 hU⟩,
      e.map_source hq, by simpa [e.left_inv hq] using hq'⟩
  have hF : ContDiffOn 𝕜 ω
      (fun y ↦ L fun l ↦ evalExt (ι ⁻¹ᵁ U) (ι.app U (a l)) (e.symm y)) S :=
    L.contDiff.comp_contDiffOn (contDiffOn_pi.2 fun l ↦ he.contDiffOn_evalExt _ _)
  refine (hF.contDiffAt (Filter.mem_of_superset hmem inter_subset_left)).congr_of_eventuallyEq ?_
  filter_upwards [hmem] with y hy
  rw [hL _ hy.2.2 ((top_le_toHom_preimage_preimage_iff ι U).1 hy.1.2)]
  simp only [evalExt_mapFun]

/-- **Closed immersions are immersions in algebraic charts.** For a closed immersion
`ι : V → X` over `𝕜`, algebraic charts `e` of `V(𝕜)` (with finite-dimensional model) and `e'` of
`X(𝕜)`, the derivative of `e' ∘ ι ∘ e⁻¹` at `e(q)` is injective: the differentials at `q` of the
regular functions on `V` near `q`, which span the dual of the model of `e`, are pull-backs of
regular functions on `X` and so factor through it. -/
theorem _root_.MMP.UnderlyingSpace.IsAlgebraicChart.injective_fderiv_comp_mapFun [IsClosedImmersion ι] [FiniteDimensional 𝕜 E]
    (he : IsAlgebraicChart e) (he' : IsAlgebraicChart e') (hq : q ∈ e.source)
    (hq' : mapFun ι q ∈ e'.source) :
    Function.Injective (fderiv 𝕜 (fun y ↦ e' (mapFun ι (e.symm y))) (e q)) := by
  set Φ : E → F := fun y ↦ e' (mapFun ι (e.symm y))
  have hΦ : DifferentiableAt 𝕜 Φ (e q) :=
    (he.contDiffAt_comp_mapFun ι he' hq hq').differentiableAt (by simp)
  obtain ⟨U, hUa, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := (mapFun ι q).toHom (IsLocalRing.closedPoint 𝕜)) (U := ⊤) trivial
  have hU : ⊤ ≤ (mapFun ι q).toHom ⁻¹ᵁ U := (top_le_preimage_iff _ U).2 hxU
  have hU' := (top_le_toHom_preimage_preimage_iff ι U).2 hU
  have hspan := span_chartDeriv_eq_top he hq (hUa.preimage ι) hU'
  have hΦq : Φ (e q) = e' (mapFun ι q) := by simp only [Φ, e.left_inv hq]
  have hTo : IsOpen (e.target ∩ e.symm ⁻¹' (mapFun ι ⁻¹' e'.source)) :=
    e.isOpen_inter_preimage_symm (e'.open_source.preimage (map (K := 𝕜) ι).continuous)
  have hfac : ∀ a : Γ(X, U), chartDeriv e (ι ⁻¹ᵁ U) q (ι.app U a) =
      (fderiv 𝕜 (fun z ↦ evalExt U a (e'.symm z)) (Φ (e q))).comp (fderiv 𝕜 Φ (e q)) := by
    intro a
    have hh := differentiableAt_evalExt he' hq' hU a
    rw [← hΦq] at hh
    rw [← fderiv_comp _ hh hΦ, chartDeriv]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hTo.mem_nhds ⟨e.map_source hq, by simpa [e.left_inv hq] using hq'⟩] with y hy
    simp only [Function.comp_apply, Φ, e'.left_inv hy.2, evalExt_mapFun]
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun f ↦ ?_
  have hf : f ∈ Submodule.span 𝕜 (range (chartDeriv e (ι ⁻¹ᵁ U) q)) := hspan ▸ Submodule.mem_top
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b, rfl⟩ := hf
    obtain ⟨a, rfl⟩ := ι.app_surjective U hUa b
    rw [hfac, ContinuousLinearMap.comp_apply, hw, map_zero]
  | zero => simp
  | add f g _ _ hf hg => simp [hf, hg]
  | smul c f _ hf => simp [hf]

end IsAlgebraicChart

end UnderlyingSpace

end MMP
