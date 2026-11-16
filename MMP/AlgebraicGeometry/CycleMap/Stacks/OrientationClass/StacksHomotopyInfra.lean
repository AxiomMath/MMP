module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.HomotopyInfraGeneric
public import MMP.AlgebraicGeometry.RegularImmersion.OfSmooth

/-!
# A point of a smooth variety is a regular closed immersion

For a smooth variety `T` of relative dimension `n` over a field `K`, a `K`-point
`t : Spec K → T` is a regular closed immersion of codimension `n`
(`Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim`): it is a closed
immersion of smooth `K`-schemes of relative dimensions `0` and `n` (Stacks 067U, EGA IV 17.12.1,
`MMP.isRegularClosedImmersionOfCodim_of_smoothOfRelativeDimension`).

## Main results

* `MMP.UnderlyingSpace.isRegularClosedImmersionOfCodim_toHom`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2.
* [Stacks Project, Tag 067U](https://stacks.math.columbia.edu/tag/067U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.RegularIdealSheaf (IsRegularClosedImmersionOfCodim)

universe u

namespace MMP.UnderlyingSpace

variable {K : Type u} [Field K] {T : Scheme.{u}} [T.Over (Spec (.of K))]
  [IsSmoothVariety K (T ↘ Spec (.of K))]

/-- **A `K`-point of a smooth variety of relative dimension `n` is a regular closed immersion**
of codimension `n`. -/
theorem isRegularClosedImmersionOfCodim_toHom {n : ℕ}
    [SmoothOfRelativeDimension n (T ↘ Spec (.of K))] (t : UnderlyingSpace K T) :
    IsRegularClosedImmersionOfCodim t.toHom n := by
  haveI : SmoothOfRelativeDimension 0 (t.toHom ≫ T ↘ Spec (.of K)) := by
    rw [t.toHom_comp_over]; infer_instance
  haveI : SmoothOfRelativeDimension (0 + n) (T ↘ Spec (.of K)) := by
    rwa [Nat.zero_add]
  exact isRegularClosedImmersionOfCodim_of_smoothOfRelativeDimension t.toHom (T ↘ Spec (.of K))
    (n := 0) (m := n)

/-- A `K`-point of a smooth curve is a regular closed immersion of codimension one. -/
theorem isRegularClosedImmersionOfCodim_toHom_of_dim_eq_one
    (hT : SmoothOfRelativeDimension 1 (T ↘ Spec (.of K))) (t : UnderlyingSpace K T) :
    IsRegularClosedImmersionOfCodim t.toHom 1 :=
  isRegularClosedImmersionOfCodim_toHom t

end MMP.UnderlyingSpace
