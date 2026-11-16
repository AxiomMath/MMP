module

public import MMP.AlgebraicGeometry.Variety.SmoothVarietyConstructions
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.ProjectiveLineBridge
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension

/-!
# The base of Stacks' deformation to the normal cone: the projective line over `ℂ`

The deformation map `ρ : M° ⟶ 𝐏¹_ℂ` of Stacks' deformation to the normal cone
(`MMP.Chow.strictTransformComplToLine`) has target Stacks' projective line
`𝐏¹_ℂ = Stacks.Chow.relativeProjectiveLine (Spec ℂ)`. The topological steps of Fulton's proof of
Theorem 19.2 (the family chain, the orientation classes of the points `0` and `∞`) need it to be
a smooth curve: this file proves it is smooth of relative dimension one over `ℂ`, through the
identification of `𝐏¹_ℂ` with the polynomial model `Proj ℂ[T₀, T₁]`.

## Main results

* `MMP.Chow.smoothOfRelativeDimension_relativeProjectiveLine`: `𝐏¹_K` is smooth of relative
  dimension one over a field `K`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveLineBridge Stacks.AlgebraicGeometry.ProjBaseChange

namespace MMP.Chow

/-- **`𝐏¹_K` is smooth of relative dimension one over `K`**: it is identified over `K` with
the polynomial model `Proj K[T₀, T₁]`
(`ProjectiveLineBridge.relativeProjectiveLineIsoProjectiveSpaceOver`,
`ProjBaseChange.polynomialComparison`). -/
theorem smoothOfRelativeDimension_relativeProjectiveLine (K : Type) [Field K] :
    SmoothOfRelativeDimension 1
      (Stacks.Chow.relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K)) := by
  have h := Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff K 1
  have e1 := relativeProjectiveLineIsoProjectiveSpaceOver_hom_fst (Spec (.of K))
  have : Stacks.Chow.relativeProjectiveLine (Spec (.of K)) ↘ Spec (.of K) =
      (relativeProjectiveLineIsoProjectiveSpaceOver (Spec (.of K))).hom ≫
        (polynomialComparison K 1).iso.hom ≫
          Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 1 := by
    rw [h, e1]
    rfl
  have h₀ := Stacks.AlgebraicGeometry.ProjPolyChart.smoothOfRelativeDimension_projToSpecCoeff K 1
  have h₂ : SmoothOfRelativeDimension (0 + (0 + 1))
      ((relativeProjectiveLineIsoProjectiveSpaceOver (Spec (.of K))).hom ≫
        (polynomialComparison K 1).iso.hom ≫
          Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 1) :=
    inferInstance
  rw [this]
  rwa [zero_add, zero_add] at h₂

end MMP.Chow
