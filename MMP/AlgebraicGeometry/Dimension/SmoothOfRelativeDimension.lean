module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# Dimension of a scheme smooth of relative dimension `n` over a field

A nonempty scheme `Y` smooth of relative dimension `n` over a field (Mathlib's
`SmoothOfRelativeDimension n (Y ↘ Spec K)`) has topological Krull dimension `n`. This is
Stacks' `AlgebraicGeometry.topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field`, put in
the form `(n : WithBot ℕ∞) = topologicalKrullDim Y` that fundamental classes of varieties take.

## Main results

* `MMP.natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension`: `n = dim Y` for a nonempty
  `Y` smooth of relative dimension `n` over a field.
* `MMP.natCast_eq_dimension_of_isVariety`: the same for an integral `Y`, which is
  nonempty.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP

/-- A nonempty scheme smooth of relative dimension `n` over a field has topological Krull
dimension `n`. -/
theorem natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension {K : Type u} [Field K]
    (Y : Scheme.{u}) [Y.Over (Spec (.of K))] [Nonempty Y] (n : ℕ)
    [SmoothOfRelativeDimension n (Y ↘ Spec (.of K))] :
    (n : WithBot ℕ∞) = topologicalKrullDim Y :=
  (topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field n (Y ↘ Spec (.of K))).symm

/-- An integral scheme smooth of relative dimension `n` over a field has topological Krull
dimension `n`, in the form used by fundamental classes of varieties. -/
theorem natCast_eq_dimension_of_isVariety {K : Type u} [Field K] (Y : Scheme.{u})
    [Y.Over (Spec (.of K))] [IsIntegral Y] (n : ℕ)
    [SmoothOfRelativeDimension n (Y ↘ Spec (.of K))] :
    (n : WithBot ℕ∞) = topologicalKrullDim Y :=
  natCast_eq_topologicalKrullDim_of_smoothOfRelativeDimension (K := K) Y n

end MMP
