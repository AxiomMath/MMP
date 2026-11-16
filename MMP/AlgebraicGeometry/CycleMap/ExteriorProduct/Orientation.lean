module

public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Homeomorph
public import MMP.AlgebraicTopology.FundamentalClass.Product
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.FundamentalClassVariety
public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.CycleClassPushforwardOrientation
public import MMP.AlgebraicGeometry.CycleMap.OpenRestriction.Fundamental
public import MMP.AlgebraicGeometry.CycleMap.ExteriorProduct.Chart

/-!
# The product of the complex orientations (Fulton, Example 19.1.9)

For complex varieties `V`, `W` of dimensions `k`, `l`, the identification
`V_reg(ℂ) × W_reg(ℂ) ≃ₜ (V × W)_reg(ℂ) ∩ (V_reg(ℂ) × W_reg(ℂ))` is orientation preserving, from the
product of the complex orientations (the real basis `e₁, i e₁, …, e_k, i e_k, f₁, i f₁, …`) to the
complex orientation of the algebraic charts of `(V × W)_reg(ℂ)`. In a product chart
`e × e'` of `V_reg(ℂ) × W_reg(ℂ)` and an algebraic chart `c` of `(V × W)_reg(ℂ)` the chart
expression is the transition map between the algebraic charts `e × e'` and `c` of `(V × W)(ℂ)`
(`MMP.UnderlyingSpace.isAlgebraicChart_productChart`), so it is holomorphic with a
holomorphic local inverse; its complex derivative is injective, and has positive real determinant
for the real bases attached to complex bases.

## Main results

* `MMP.OpenPartialHomeomorph.injective_fderiv`: a partial homeomorphism differentiable at a point,
  with inverse differentiable at its image, has an injective derivative there.
* `MMP.prod_euclideanComplexOrientationBasis_reindex`: the product of the complex
  orientation bases of `ℂᵏ` and `ℂˡ` is the real basis of the product complex basis.
* `MMP.isOrientationPreserving_regularProdHomeomorph`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], Example 19.1.9.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Topology
open scoped ContDiff
open MMP.UnderlyingSpace MMP.FundamentalClass

namespace MMP

open MMP.Intersection.Scheme (dimension)

/-- A partial homeomorphism differentiable at `x` whose inverse is differentiable at its image has
an injective derivative at `x`. -/
lemma OpenPartialHomeomorph.injective_fderiv {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] (F : OpenPartialHomeomorph E E') {x : E} (hx : x ∈ F.source)
    (hF : DifferentiableAt 𝕜 F x) (hF' : DifferentiableAt 𝕜 F.symm (F x)) :
    Function.Injective (fderiv 𝕜 F x) := by
  have hcomp : (fderiv 𝕜 F.symm (F x)).comp (fderiv 𝕜 F x) = ContinuousLinearMap.id 𝕜 E := by
    rw [← fderiv_comp x hF' hF, ← fderiv_id (𝕜 := 𝕜) (x := x)]
    exact Filter.EventuallyEq.fderiv_eq (F.eventually_left_inverse hx)
  refine Function.LeftInverse.injective (g := fderiv 𝕜 F.symm (F x)) fun v ↦ ?_
  have := congrArg (fun L : E →L[𝕜] E ↦ L v) hcomp
  simpa using this

/-- The product (in the order `ℂᵏ` then `ℂˡ`) of the complex orientation bases of `ℂᵏ` and `ℂˡ`
is the real basis attached to the product of the standard complex bases. -/
lemma prod_euclideanComplexOrientationBasis_reindex (k l : ℕ) :
    ((euclideanComplexOrientationBasis k).prod (euclideanComplexOrientationBasis l)).reindex
        (finSumFinEquiv.trans (finCongr (by ring : 2 * k + 2 * l = 2 * (k + l)))) =
      complexRealBasis
        (((Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin k → ℂ))).prod
          (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin l → ℂ)))).reindex
            finSumFinEquiv) := by
  rw [euclideanComplexOrientationBasis_eq_complexRealBasis,
    euclideanComplexOrientationBasis_eq_complexRealBasis]
  have h := prod_complexRealBasis (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin k → ℂ)))
    (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin l → ℂ)))
  refine Module.Basis.eq_of_apply_eq fun i ↦ ?_
  have := congrArg (fun b ↦ b ((finCongr (by ring : 2 * k + 2 * l = 2 * (k + l))).symm i)) h
  simp only [Module.Basis.reindex_apply] at this ⊢
  rw [Equiv.symm_trans_apply, this]
  congr 1

variable (V W : Scheme.{0}) [V.Over (Spec (.of ℂ))] [W.Over (Spec (.of ℂ))]
  [IsIntegral V] [LocallyOfFiniteType (V ↘ Spec (.of ℂ))] [QuasiCompact (V ↘ Spec (.of ℂ))]
  [IsIntegral W] [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))]
  [IsIntegral (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))]
  [LocallyOfFiniteType (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))]
  [QuasiCompact (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)) ↘ Spec (.of ℂ))]

/-- **The product of complex orientations is the complex orientation of the product.** -/
theorem isOrientationPreserving_regularProdHomeomorph {k l : ℕ}
    (hk : (k : WithBot ℕ∞) = dimension V) (hl : (l : WithBot ℕ∞) = dimension W)
    (hkl : ((k + l : ℕ) : WithBot ℕ∞) =
      dimension (pullback (V ↘ Spec (.of ℂ)) (W ↘ Spec (.of ℂ)))) :
    letI := regularChartedSpace (𝕜 := ℂ) hk
    letI := regularChartedSpace (𝕜 := ℂ) hl
    letI := regularChartedSpace (𝕜 := ℂ) hkl
    IsOrientationPreserving
      (H := ModelProd (EuclideanSpace ℂ (Fin k)) (EuclideanSpace ℂ (Fin l)))
      (((euclideanComplexOrientationBasis k).prod (euclideanComplexOrientationBasis l)).reindex
        (finSumFinEquiv.trans (finCongr (by ring))))
      (euclideanComplexOrientationBasis (k + l)) (regularProdHomeomorph V W) := by
  letI := regularChartedSpace (𝕜 := ℂ) hk
  letI := regularChartedSpace (𝕜 := ℂ) hl
  letI := regularChartedSpace (𝕜 := ℂ) hkl
  refine isOrientationPreserving_of_hasFDerivAt _ _ _ fun e he e' he' x hx hx' ↦ ?_
  obtain ⟨e₁, ⟨cV, hV, hcV, rfl⟩, e₂, ⟨cW, hW, hcW, rfl⟩, rfl⟩ := he
  obtain ⟨_, ⟨z, rfl⟩, he'⟩ := he'
  rw [Set.mem_singleton_iff] at he'
  subst he'
  set c := (exists_isAlgebraicChart_of_dimension_eq hkl z.1.1 (mem_regularOpens.1 z.1.2)).choose
  have hc : IsAlgebraicChart c :=
    (exists_isAlgebraicChart_of_dimension_eq hkl z.1.1 (mem_regularOpens.1 z.1.2)).choose_spec.2
  have hx₁' : x.1 ∈ (cV.subtypeRestr hV).source := hx.1
  have hx₂' : x.2 ∈ (cW.subtypeRestr hW).source := hx.2
  have hx₁ : x.1.1 ∈ cV.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hx₁'
    exact hx₁'
  have hx₂ : x.2.1 ∈ cW.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hx₂'
    exact hx₂'
  have hxc : ((regularProdHomeomorph V W) x).1.1 ∈ c.source := by
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hx'
    change _ ∈ (c.subtypeRestr ⟨z.1⟩).source at hx'
    rw [OpenPartialHomeomorph.subtypeRestr_source] at hx'
    exact hx'
  set P := productChart cV cW
  have hP : IsAlgebraicChart P := isAlgebraicChart_productChart hcV hcW
  set F := P.symm.trans c
  set y₀ : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin l) := (cV x.1.1, cW x.2.1)
  have hPy₀ : P.symm y₀ = ((regularProdHomeomorph V W) x).1.1 := by
    rw [productChart_symm_apply, cV.left_inv hx₁, cW.left_inv hx₂]
    rfl
  have hy₀ : y₀ ∈ F.source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
    refine ⟨(mem_productChart_target cV cW).2 ⟨cV.map_source hx₁, cW.map_source hx₂⟩, ?_⟩
    rw [Set.mem_preimage, hPy₀]
    exact hxc
  have hFeq : (fun y : EuclideanSpace ℂ (Fin k) × EuclideanSpace ℂ (Fin l) ↦
      (((chartAt (EuclideanSpace ℂ (Fin (k + l))) z.1).subtypeRestr ⟨z⟩ :
        OpenPartialHomeomorph _ _) ((regularProdHomeomorph V W)
          (((cV.subtypeRestr hV).prod (cW.subtypeRestr hW)).symm y)))) =ᶠ[𝓝 y₀] F := by
    have hT : (cV.subtypeRestr hV).target ×ˢ (cW.subtypeRestr hW).target ∈ 𝓝 y₀ :=
      ((cV.subtypeRestr hV).open_target.prod (cW.subtypeRestr hW).open_target).mem_nhds
        ⟨(cV.subtypeRestr hV).map_source hx₁', (cW.subtypeRestr hW).map_source hx₂'⟩
    filter_upwards [hT] with y hy
    change c ((productHomeomorph ℂ V W).symm (((cV.subtypeRestr hV).symm y.1).1,
      ((cW.subtypeRestr hW).symm y.2).1)) = c ((productHomeomorph ℂ V W).symm (cV.symm y.1,
        cW.symm y.2))
    rw [cV.subtypeRestr_symm_eqOn hV hy.1, cW.subtypeRestr_symm_eqOn hW hy.2]
    rfl
  have hFd : ContDiffAt ℂ ω F y₀ :=
    (hP.contDiffOn_symm_trans₂ hc).contDiffAt (F.open_source.mem_nhds hy₀)
  have hFsymm : (F.symm : EuclideanSpace ℂ (Fin (k + l)) → _) = c.symm.trans P := by
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
  have hGd : ContDiffAt ℂ ω F.symm (F y₀) := by
    rw [hFsymm]
    refine (hc.contDiffOn_symm_trans₂ hP).contDiffAt ((c.symm.trans P).open_source.mem_nhds ?_)
    rw [← OpenPartialHomeomorph.symm_symm (c.symm.trans P), ← OpenPartialHomeomorph.symm_target,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.symm_symm]
    exact F.map_source hy₀
  have hinj := OpenPartialHomeomorph.injective_fderiv F hy₀ (hFd.differentiableAt (by simp))
    (hGd.differentiableAt (by simp))
  refine ⟨(fderiv ℂ F y₀).restrictScalars ℝ, ?_, ?_⟩
  · exact ((hFd.differentiableAt (by simp)).hasFDerivAt.restrictScalars ℝ).congr_of_eventuallyEq
      hFeq
  · rw [prod_euclideanComplexOrientationBasis_reindex,
      euclideanComplexOrientationBasis_eq_complexRealBasis]
    have key := complexRealBasis_det_pos
      (((Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin k → ℂ))).prod
        (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin l → ℂ)))).reindex finSumFinEquiv)
      (Module.Basis.ofEquivFun (WithLp.linearEquiv 2 ℂ (Fin (k + l) → ℂ)))
      (L := ((fderiv ℂ F y₀ : _ →L[ℂ] _) : _ →ₗ[ℂ] _)) hinj
    exact key

end MMP
