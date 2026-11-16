module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HomotopyInfraGeneric
import MMP.AlgebraicGeometry.SpecOverSpecSelf
public import MMP.AlgebraicTopology.OrientationClass.CapProductPointClass
public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.AgreesSubmanifoldChart
public import MMP.AlgebraicGeometry.CycleMap.Stacks.LocalizedFirstChern.ThomChartGeneric
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HomeomorphGeneric

/-!
# Points of a smooth complex curve: charts, orientation and local orientation classes

Bundle-free part of the orientation class of a point of a smooth complex curve (Fulton §19.2).
For a smooth complex curve `T` and `t ∈ T(ℂ)`: the image of `t : Spec ℂ → T` is `{t}`, the pair
`(t, T)` satisfies the non-singularity hypotheses of the disc criterion, the real basis
`curveOrientationBasis` of the chart model induces the complex orientation, and a class of
`H²(T, T - t)` with the disc values of an orientation class is the local orientation class.

## Main definitions

* `MMP.UnderlyingSpace.curveOrientationBasis`: the real basis `A 1, A i` of the
  model `ℂ^{dim T} = ℂ` of a curve, inducing its complex orientation.

## Main results

* `MMP.UnderlyingSpace.range_map_toHom`: the image of the point `t : Spec ℂ → T` is `{t}`.
* `MMP.UnderlyingSpace.isNonsingularPair_toHom`: the disc criterion's hypotheses for `t`.
* `MMP.UnderlyingSpace.isLocalOrientationClass_forget_of_eval_comp_affineSimplex_eq_one`: the disc
  values characterise the local orientation class.
* `MMP.UnderlyingSpace.curveOrientationBasis_det_pos`: complex linear injections preserve the
  orientation.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Set Topology Metric Filter
open scoped Manifold ContDiff

namespace MMP

open ThomClass SingularChain SingularCochain FundamentalClass

namespace UnderlyingSpace

section Points

variable {K : Type} [Field K] {T : Scheme.{0}} [T.Over (Spec (.of K))]

/-- A `K`-point `t : Spec K → T` is a morphism over `K`. -/
instance isOver_toHom (t : UnderlyingSpace K T) : t.toHom.IsOver (Spec (.of K)) :=
  ⟨by rw [t.toHom_comp_over, MMP.specOverSpec_over_self]⟩

variable [TopologicalSpace K]

/-- The image of the point `t : Spec K → T` in `T(K)` is `{t}`. -/
theorem range_map_toHom (t : UnderlyingSpace K T) :
    range (UnderlyingSpace.map (K := K) t.toHom) = {t} := by
  ext s
  simp only [mem_range, mem_singleton_iff]
  constructor
  · rintro ⟨p, rfl⟩
    refine UnderlyingSpace.ext ?_
    change (mapFun t.toHom p).toHom = _
    rw [toHom_mapFun]
    have hp := p.toHom_comp_over
    rw [MMP.specOverSpec_over_self, Category.comp_id] at hp
    rw [hp, Category.id_comp]
  · rintro rfl
    let p : UnderlyingSpace K (Spec (.of K)) :=
      ⟨𝟙 _, by rw [MMP.specOverSpec_over_self, Category.comp_id]⟩
    refine ⟨p, UnderlyingSpace.ext ?_⟩
    change (mapFun s.toHom p).toHom = _
    rw [toHom_mapFun]
    exact Category.id_comp _

end Points

/-- The point `Spec ℂ` is a complex scheme: it is a smooth variety over itself. -/
instance _root_.MMP.IsComplexScheme.spec : IsComplexScheme (Spec (.of ℂ)) :=
  haveI : IsSmoothVariety ℂ (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
    isSmoothVariety_of_eq_id (MMP.specOverSpec_over_self ℂ)
  IsComplexScheme.of_isSmoothVariety _

section Curve

variable {T : Scheme.{0}} [T.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (T ↘ Spec (.of ℂ))]

/-- The point `t : Spec ℂ → T` of a smooth complex variety of relative dimension `n`, with the
algebraic charts of `T(ℂ)`, satisfies the non-singularity hypotheses of the disc criterion. -/
theorem isNonsingularPair_toHom {n : ℕ} [SmoothOfRelativeDimension n (T ↘ Spec (.of ℂ))]
    (t : UnderlyingSpace ℂ T) : IsNonsingularPair t.toHom (EuclideanSpace ℂ (Fin n)) where
  isAlgebraicChart _ he := isAlgebraicChart_of_mem_atlas he
  regular_Y y := ⟨isRegularLocalRing_stalk_of_isSmoothVariety y, by
    rw [ringKrullDim_stalk_eq_of_smoothOfRelativeDimension (n := n), finrank_euclideanSpace,
      Fintype.card_fin]⟩
  regular_X x :=
    haveI : IsSmoothVariety ℂ (Spec (.of ℂ) ↘ Spec (.of ℂ)) :=
      isSmoothVariety_of_eq_id (MMP.specOverSpec_over_self ℂ)
    isRegularLocalRing_stalk_of_isSmoothVariety x

/-- The model `ℂ¹` of the charts of a curve, as `Fin 1 → ℂ`. -/
def curveChartEquiv : (Fin 1 → ℂ) ≃L[ℂ] EuclideanSpace ℂ (Fin 1) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- The real basis `A 1, A i` of the model `ℂ¹` of the charts of a curve, `A` the identification
`curveChartEquiv`: it induces the complex orientation. -/
def curveOrientationBasis : Module.Basis (Fin (2 * 1)) ℝ (EuclideanSpace ℂ (Fin 1)) :=
  (complexOrientationBasis 1).map (curveChartEquiv.toLinearEquiv.restrictScalars ℝ)

/-- The identification `curveChartEquiv` carries the complex orientation basis of `ℂ¹` to a family
of positive determinant for `curveOrientationBasis`. -/
theorem curveOrientationBasis_det_curveChartEquiv :
    0 < curveOrientationBasis.det
      (⇑(((curveChartEquiv : (Fin 1 → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin 1)).restrictScalars ℝ :
        (Fin 1 → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin 1)) : (Fin 1 → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1)) ∘
        complexOrientationBasis 1) := by
  rw [curveOrientationBasis, Module.Basis.det_map]
  have h : ⇑((curveChartEquiv.toLinearEquiv.restrictScalars ℝ).symm) ∘
      (⇑(((curveChartEquiv : (Fin 1 → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin 1)).restrictScalars ℝ :
        (Fin 1 → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin 1)) : (Fin 1 → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1)) ∘
        ⇑(complexOrientationBasis 1)) = complexOrientationBasis 1 := by
    funext k
    simp
  rw [h, Module.Basis.det_self]
  exact one_pos

/-- The tangent cone of a point is `0`. -/
lemma tangentConeAt_singleton_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    tangentConeAt ℝ ({x} : Set E) x = {0} := by
  refine Subset.antisymm (tangentConeAt_subset_zero ?_) ?_
  · rw [accPt_iff_nhds]
    push Not
    exact ⟨univ, univ_mem, fun y hy ↦ hy.2⟩
  · rintro _ rfl
    exact zero_mem_tangentConeAt (subset_closure rfl)

/-- In the chart at `t` of a smooth complex curve, the tangent cone of the point `{t}` is `0`. -/
theorem tangentConeAt_chartAt_range_map_toHom
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (t : UnderlyingSpace ℂ T) :
    tangentConeAt ℝ (chartAt (EuclideanSpace ℂ (Fin 1)) t ''
        (range (UnderlyingSpace.map (K := ℂ) t.toHom) ∩
          (chartAt (EuclideanSpace ℂ (Fin 1)) t).source))
      (chartAt (EuclideanSpace ℂ (Fin 1)) t t) =
      ((⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin 1))) : Set (EuclideanSpace ℂ (Fin 1))) := by
  rw [range_map_toHom, singleton_inter_of_mem (mem_chart_source _ t), image_singleton,
    Submodule.bot_coe]
  exact tangentConeAt_singleton_self _

/-- The tangent cones of the point `{t}` of a smooth complex curve are complex subspaces of
codimension one of the model `ℂ¹`. -/
theorem exists_tangentConeAt_chartAt_range_map_toHom
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (t : UnderlyingSpace ℂ T) :
    ∀ x ∈ range (UnderlyingSpace.map (K := ℂ) t.toHom),
      ∃ W : Submodule ℂ (EuclideanSpace ℂ (Fin 1)),
        tangentConeAt ℝ (chartAt (EuclideanSpace ℂ (Fin 1)) x ''
          (range (UnderlyingSpace.map (K := ℂ) t.toHom) ∩
            (chartAt (EuclideanSpace ℂ (Fin 1)) x).source))
          (chartAt (EuclideanSpace ℂ (Fin 1)) x x) = W ∧
        Module.finrank ℂ W + 1 = Module.finrank ℂ (EuclideanSpace ℂ (Fin 1)) := fun x hx' ↦ by
  rw [range_map_toHom, mem_singleton_iff] at hx'
  subst hx'
  refine ⟨⊥, tangentConeAt_chartAt_range_map_toHom hT x, ?_⟩
  rw [finrank_bot, finrank_euclideanSpace, Fintype.card_fin]

/-- The point `t` lies in the image of `t : Spec ℂ → T`. -/
theorem mem_range_map_toHom_self (t : UnderlyingSpace ℂ T) :
    t ∈ range (UnderlyingSpace.map (K := ℂ) t.toHom) :=
  (range_map_toHom t).symm ▸ mem_singleton t

/-- A transversal disc at a point `t` of a smooth complex curve: a continuous map `B` from `ℂ¹`
which, near `0`, is the inverse chart at `t` of the translate by `e t` of `curveChartEquiv`, and
meets `t` only at `0`. -/
theorem exists_disc_chartAt (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ)))
    (t : UnderlyingSpace ℂ T) :
    ∃ ρ > 0, ∃ B : C(Fin 1 → ℂ, TopCat.of (UnderlyingSpace ℂ T)),
      (∀ x : Fin 1 → ℂ, ‖x‖ ≤ ρ → chartAt (EuclideanSpace ℂ (Fin 1)) t t + curveChartEquiv x ∈
        (chartAt (EuclideanSpace ℂ (Fin 1)) t).target) ∧
      (∀ v : Fin 1 → ℂ, ‖v‖ < ρ → B v = (chartAt (EuclideanSpace ℂ (Fin 1)) t).symm
        (chartAt (EuclideanSpace ℂ (Fin 1)) t t + curveChartEquiv v)) ∧
      B 0 = t ∧ ∀ v, B v = t → v = 0 := by
  set E := EuclideanSpace ℂ (Fin 1)
  set A := curveChartEquiv
  set e := chartAt E t
  have ht : t ∈ e.source := mem_chart_source E t
  obtain ⟨δ, hδ, hδt⟩ := Metric.isOpen_iff.1 e.open_target (e t) (e.map_source ht)
  set a := ‖(A : (Fin 1 → ℂ) →L[ℂ] E)‖
  set ρ := δ / (a + 1)
  have ha : 0 ≤ a := norm_nonneg _
  have hρ : 0 < ρ := by positivity
  have hmem : ∀ x : Fin 1 → ℂ, ‖x‖ ≤ ρ → e t + A x ∈ e.target := fun x hx ↦ hδt (by
    have h₁ : ‖A x‖ ≤ a * ‖x‖ := (A : (Fin 1 → ℂ) →L[ℂ] E).le_opNorm x
    have h₂ : (a + 1) * ρ = δ := by
      simp only [ρ]
      field_simp
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    nlinarith [norm_nonneg x])
  have hBc : Continuous fun v : Fin 1 → ℂ ↦ e.symm (e t + A (radialRetraction ρ v)) :=
    e.continuousOn_symm.comp_continuous
      (continuous_const.add (A.continuous.comp (continuous_radialRetraction hρ)))
      (fun v ↦ hmem _ (norm_radialRetraction_le hρ.le v))
  let B : C(Fin 1 → ℂ, TopCat.of (UnderlyingSpace ℂ T)) := ⟨_, hBc⟩
  refine ⟨ρ, hρ, B, hmem, fun v hv ↦ ?_, ?_, fun v hv ↦ ?_⟩
  · change e.symm (e t + A (radialRetraction ρ v)) = _
    rw [radialRetraction_of_norm_lt hv]
  · change e.symm (e t + A (radialRetraction ρ 0)) = t
    rw [radialRetraction_of_norm_lt (by simpa using hρ), map_zero, add_zero, e.left_inv ht]
  · have h : e (B v) = e t + A (radialRetraction ρ v) :=
      e.right_inv (hmem _ (norm_radialRetraction_le hρ.le v))
    rw [hv] at h
    exact eq_zero_of_radialRetraction_eq_zero hρ
      ((map_eq_zero_iff A A.injective).1 (add_eq_left.1 h.symm))

open Finsupp in
/-- **A class of `H²(T, T - t)` with the disc values of an orientation class is the local
orientation class.** For a smooth complex curve `T` and `t ∈ T(ℂ)`, a class `u` such that a
representing cocycle takes the value `1` on `B ∘ Δ` for every transversal disc `B` of `{t}` and
every oriented affine simplex `Δ` around `0` in `ℂ` (the conclusion of the disc criterion for
orientation classes of regular imbeddings), viewed in `H²(T, T - t)`, is the local orientation
class of the complex manifold `T(ℂ)` at `t` for its complex orientation
(`curveOrientationBasis`). -/
theorem isLocalOrientationClass_forget_of_eval_comp_affineSimplex_eq_one (R : Type)
    [CommRing R] (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of ℂ))) (t : UnderlyingSpace ℂ T)
    {u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ T))
      (range (UnderlyingSpace.map (K := ℂ) t.toHom)) (2 * 1 : ℕ)}
    (hdisc : ∀ {α : SingularChain.Simplex (TopCat.of (UnderlyingSpace ℂ T)) (2 * 1) → R}
      (hα : α ∈ relCocycles R ((range (UnderlyingSpace.map (K := ℂ) t.toHom))ᶜ :
        Set (TopCat.of (UnderlyingSpace ℂ T))) (2 * 1)),
      relativeSingularCohomologyEquiv R ((range (UnderlyingSpace.map (K := ℂ) t.toHom))ᶜ :
        Set (TopCat.of (UnderlyingSpace ℂ T))) (2 * 1) u = Submodule.Quotient.mk ⟨α, hα⟩ →
      ∀ (B : C(Fin 1 → ℂ, TopCat.of (UnderlyingSpace ℂ T))), B 0 = t →
      (∀ v, B v ∈ range (UnderlyingSpace.map (K := ℂ) t.toHom) → v = 0) →
      ∀ {L : (Fin 1 → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin 1)},
      HasFDerivAt (fun v ↦ chartAt (EuclideanSpace ℂ (Fin 1)) t (B v)) L 0 →
      Function.Injective L →
      IsCompl (LinearMap.range (L : (Fin 1 → ℂ) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1)))
        ((⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin 1))).restrictScalars ℝ) →
      (∀ (c : ℂ) (v : Fin 1 → ℂ), L (c • v) - c • L v ∈
        (⊥ : Submodule ℂ (EuclideanSpace ℂ (Fin 1)))) →
      ∀ {v : Fin (2 * 1 + 1) → (Fin 1 → ℂ)},
      IsOrientedSimplexAroundZero (complexOrientationBasis 1) v →
      SingularCochain.eval α (single (B.comp (affineSimplex v)) 1) = 1) :
    IsLocalOrientationClass R curveOrientationBasis t
      ((cohomologyWithSupports.forget R (ModuleCat.of R R) _ (range_map_toHom t).le _).hom u) := by
  set E := EuclideanSpace ℂ (Fin 1)
  set A := curveChartEquiv
  obtain ⟨⟨α, hα⟩, hrep⟩ := Submodule.Quotient.mk_surjective _
    (relativeSingularCohomologyEquiv R ((range (UnderlyingSpace.map (K := ℂ) t.toHom))ᶜ :
      Set (TopCat.of (UnderlyingSpace ℂ T))) (2 * 1) u)
  have hα' : α ∈ relCocycles R ({t}ᶜ : Set (TopCat.of (UnderlyingSpace ℂ T))) (2 * 1) := by
    simpa only [range_map_toHom] using hα
  set e := chartAt E t
  have ht : t ∈ e.source := mem_chart_source E t
  obtain ⟨ρ, hρ, B, hmem, hBe, hB0, hBt⟩ := exists_disc_chartAt hT t
  set L : (Fin 1 → ℂ) →L[ℝ] E := (A : (Fin 1 → ℂ) →L[ℂ] E).restrictScalars ℝ
  have hB : HasFDerivAt (fun v ↦ e (B v)) L 0 := by
    refine (L.hasFDerivAt.const_add (e t)).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : Fin 1 → ℂ) hρ] with v hv
    rw [mem_ball_zero_iff] at hv
    rw [hBe v hv]
    exact e.right_inv (hmem v hv.le)
  have hc : IsCompl (LinearMap.range (L : (Fin 1 → ℂ) →ₗ[ℝ] E))
      ((⊥ : Submodule ℂ E).restrictScalars ℝ) := by
    rw [Submodule.restrictScalars_bot, LinearMap.range_eq_top.2
      (show Function.Surjective (L : (Fin 1 → ℂ) →ₗ[ℝ] E) from A.surjective)]
    exact isCompl_top_bot
  obtain ⟨v, hv, hvs⟩ := exists_isOrientedSimplexAroundZero_subset (complexOrientationBasis 1)
    (0 : Fin 1 → ℂ) (ball_mem_nhds 0 hρ)
  simp only [sub_zero] at hv
  have key := hdisc hα hrep.symm B hB0
    (fun v hv ↦ hBt v (by rwa [range_map_toHom, mem_singleton_iff] at hv)) hB A.injective hc
    (fun c v ↦ by simp [L]) hv
  have hsum (s : stdSimplex ℝ (Fin (2 * 1 + 1))) :
      affineSimplex (fun k ↦ e t + L (v k)) s = e t + L (affineSimplex v s) := by
    simpa only [sub_zero] using affineSimplex_affine 0 (e t) L v s
  have hwt : range (affineSimplex fun k ↦ e t + L (v k)) ⊆ e.target := by
    rintro _ ⟨s, rfl⟩
    rw [hsum]
    exact hmem _ (mem_ball_zero_iff.1 (hvs ⟨s, rfl⟩)).le
  have hcomp : B.comp (affineSimplex v) = chartSimplexOf e _ hwt := by
    refine ContinuousMap.ext fun s ↦ ?_
    rw [chartSimplexOf_apply, hsum]
    exact hBe _ (mem_ball_zero_iff.1 (hvs ⟨s, rfl⟩))
  have hv' := hv.map_linearMap (L : (Fin 1 → ℂ) →ₗ[ℝ] E) curveOrientationBasis_det_curveChartEquiv
  have hw' : IsOrientedSimplexAroundZero curveOrientationBasis
      (fun k ↦ (e t + L (v k)) - e t) := by
    simp only [add_sub_cancel_left]
    exact hv'
  refine ⟨α, hα', isChartOrientedCocycle_of_eval (isOrientedAtlas_of_isManifold_complex _) _ hα'
    (chart_mem_atlas E t) ht hw' hwt (hcomp ▸ key), ?_⟩
  simp only [cohomologyWithSupports.forget]
  erw [relativeSingularCohomologyEquiv_map]
  rw [← hrep]
  rfl

/-- A complex linear injective map from the model of the charts of a curve to `ℂ` preserves the
orientations given by `curveOrientationBasis` and `1, i`. -/
theorem curveOrientationBasis_det_pos {D : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ}
    (hD : Function.Injective D) :
    0 < Complex.basisOneI.det
      (((D.restrictScalars ℝ : EuclideanSpace ℂ (Fin 1) →L[ℝ] ℂ) :
        EuclideanSpace ℂ (Fin 1) → ℂ) ∘ curveOrientationBasis) := by
  set A := curveChartEquiv
  let M : ℂ →ₗ[ℂ] ℂ := (D : EuclideanSpace ℂ (Fin 1) →ₗ[ℂ] ℂ) ∘ₗ
    (A : (Fin 1 → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin 1)) ∘ₗ
    ((LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm : ℂ →ₗ[ℂ] (Fin 1 → ℂ))
  have hM : Function.Injective M :=
    hD.comp (A.injective.comp (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.injective)
  have hcomp : (((D.restrictScalars ℝ :
      EuclideanSpace ℂ (Fin 1) →L[ℝ] ℂ) :
        EuclideanSpace ℂ (Fin 1) → ℂ) ∘ curveOrientationBasis) =
      (M.restrictScalars ℝ) ∘ Complex.basisOneI := by
    funext k
    rw [← complexOrientationBasis_one_map]
    simp only [curveOrientationBasis, M, A, Module.Basis.map_apply, Function.comp_apply,
      ContinuousLinearMap.coe_restrictScalars', LinearMap.coe_restrictScalars, LinearMap.coe_comp,
      LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe, LinearEquiv.restrictScalars_apply,
      ContinuousLinearEquiv.coe_toLinearEquiv]
    congr 2
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  rw [hcomp, basis_det_comp_self, LinearMap.det_restrictScalars, Algebra.norm_complex_apply,
    Complex.normSq_pos]
  exact (LinearEquiv.isUnit_det' (LinearEquiv.ofInjectiveEndo _ hM)).ne_zero

end Curve

end UnderlyingSpace

end MMP
