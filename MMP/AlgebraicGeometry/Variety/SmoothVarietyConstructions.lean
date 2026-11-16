module

public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Product
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepOpen

/-!
# Constructions of smooth varieties

Three ways of producing a smooth variety (Stacks' `AlgebraicGeometry.IsSmoothVariety`: an
integral scheme, separated and of finite type over a field, with smooth structure morphism):

* projective space `ℙⁿ_k = Proj k[x₀, …, xₙ]`, with its structure morphism
  `Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`;
* a nonempty open subscheme of a smooth variety;
* the fibre product of two smooth varieties over an algebraically closed field.

## Main results

* `MMP.isSmoothVariety_projToSpecCoeff`: `ℙⁿ_k` is a smooth variety over `k`.
* `MMP.isSmoothVariety_opens_ι`: a nonempty open subscheme of a smooth variety is one.
* `MMP.isSmoothVariety_pullback`: over an algebraically closed field, the product of two smooth
  varieties is a smooth variety.

## Implementation notes

Each is the corresponding statement for varieties in Stacks (integrality of `Proj`,
`isVariety_opens_ι`, Tag 05P3 `isVariety_pullback`) together with the stability of smoothness
under composition, base change and open immersions.

## References

* [Stacks Project, Tag 04L1](https://stacks.math.columbia.edu/tag/04L1)
* [Stacks Project, Tag 05P3](https://stacks.math.columbia.edu/tag/05P3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace MMP

variable (k : Type u) [Field k]

/-- **Projective space is a smooth variety**: `ℙⁿ_k = Proj k[x₀, …, xₙ]` is integral, proper
and smooth over `k`. -/
instance isSmoothVariety_projToSpecCoeff (n : ℕ) :
    IsSmoothVariety k (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k n) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff k n
  have := Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff k n
  exact { }

/-- **A nonempty open subscheme of a smooth variety is a smooth variety.** -/
instance isSmoothVariety_opens_ι {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSmoothVariety k f]
    (U : X.Opens) [Nonempty U] : IsSmoothVariety k (U.ι ≫ f) :=
  (isSmoothVariety_iff k _).2
    ⟨Stacks.Intersection.RationalEquivalenceProduct.isVariety_opens_ι k f U, inferInstance⟩

/-- **Over an algebraically closed field the product of two smooth varieties is a smooth
variety** (Stacks Tag 05P3 for the variety part; smoothness is stable under base change and
composition). -/
instance isSmoothVariety_pullback [IsAlgClosed k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (g : Y ⟶ Spec (.of k)) [IsSmoothVariety k f] [IsSmoothVariety k g] :
    IsSmoothVariety k (pullback.fst f g ≫ f) :=
  (isSmoothVariety_iff k _).2 ⟨isVariety_pullback k f g, inferInstance⟩

end MMP
