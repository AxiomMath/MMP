module

public import MMP.AlgebraicGeometry.Chow.CycleClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# The cycle class of an integral closed subscheme

Let `X` be a complex scheme and `W ⊆ X` an integral closed subscheme of delta-dimension `k`
over `Stacks.Chow.fieldChowSituation ℂ`. Its fundamental cycle `[W]_k` (Stacks 02QU) is the
prime cycle of its generic point, so its cycle class is the cycle class `cl_X(ξ_W)` of that
point.

## Main results

* `MMP.Chow.cycleAssociatedToClosedSubscheme_eq_pointCycle`: `[W]_k = [ξ_W]`.
* `MMP.Chow.cycleClass_cycleAssociatedToClosedSubscheme`: `cl_X([W]_k) = cl_X(ξ_W)`.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow

namespace MMP.Chow

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [IsComplexScheme X]

/-- **Stacks 02QU.** The fundamental cycle `[W]_k` of an integral closed subscheme of
delta-dimension `k` is the prime cycle of its generic point. -/
theorem cycleAssociatedToClosedSubscheme_eq_pointCycle (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) {k : ℤ}
    (hDim : schemeDeltaDimension (fieldChowSituation ℂ) (W.subschemeι ≫ X ↘ Spec (.of ℂ)) =
      (k : EInt)) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) W.subschemeι k =
      pointCycle (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) k (genericPointOf W hW)
        (relativeDimension_genericPointOf _ _ W hW hDim) := by
  refine Subtype.ext ?_
  ext y
  rw [pointCycle_apply]
  by_cases hy : y = genericPointOf W hW
  · subst hy
    rw [if_pos rfl, cycleAssociatedToClosedSubscheme_integral_apply _ _ W hW hDim]
  · rw [if_neg hy, cycleAssociatedToClosedSubscheme_integral_apply_of_ne _ _ W hW k hy]

variable (R : Type) [CommRing R]

/-- The cycle class of the fundamental cycle of an integral closed subscheme of delta-dimension
`k` is the cycle class of its generic point. -/
theorem cycleClass_cycleAssociatedToClosedSubscheme (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) {k : ℕ}
    (hDim : schemeDeltaDimension (fieldChowSituation ℂ) (W.subschemeι ≫ X ↘ Spec (.of ℂ)) =
      ((k : ℤ) : EInt)) :
    cycleClass R k
        (cycleAssociatedToClosedSubscheme (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
          W.subschemeι k) =
      pointCycleClass R (genericPointOf W hW) (relativeDimension_genericPointOf _ _ W hW hDim) := by
  rw [cycleAssociatedToClosedSubscheme_eq_pointCycle W hW hDim, cycleClass_pointCycle]

end MMP.Chow
