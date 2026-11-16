module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartManifold
public import MMP.AlgebraicGeometry.Dimension.SmoothOfRelativeDimension

/-!
# A smooth complex scheme is its own regular part

If `X` is smooth of relative dimension `n` over `ℂ`, every closed point of `X` is regular, so the
regular part `X_reg(ℂ)` of the complex points is all of `X(ℂ)`.

## Main results

* `MMP.regularOpens_eq_top_of_smoothOfRelativeDimension`: `X_reg(ℂ) = X(ℂ)` for `X` smooth of
  relative dimension `n` over `ℂ`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MMP.UnderlyingSpace

namespace MMP

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [QuasiCompact (X ↘ Spec (.of ℂ))]

/-- A scheme smooth of relative dimension `n` over `ℂ` is its own regular part:
`X_reg(ℂ) = X(ℂ)`. -/
theorem regularOpens_eq_top_of_smoothOfRelativeDimension (n : ℕ)
    [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))] : regularOpens ℂ X = ⊤ := by
  haveI := SmoothOfRelativeDimension.smooth n (X ↘ Spec (.of ℂ))
  ext p
  simp only [Opens.coe_top, Set.mem_univ, iff_true, SetLike.mem_coe]
  rw [mem_regularOpens, mem_regularPart_iff]
  exact (isRegular_of_smooth_over_regular (X ↘ Spec (.of ℂ))).isRegularLocalRing_stalk _

end MMP
