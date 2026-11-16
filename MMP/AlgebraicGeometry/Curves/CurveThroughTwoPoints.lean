module

public import MMP.AlgebraicGeometry.Cohomology.HigherDirectImageFibreDim

/-!
# A curve through two closed points of a variety over an algebraically closed field

Let `X` be a variety of dimension at least one over an algebraically closed field `k` of
arbitrary characteristic. Any two closed points `x` and `y` of `X`, possibly equal, lie on a
closed curve: there is a closed immersion `i : C ⟶ X` such that `C` is a curve over `k`
(via `i ≫ f`) and `x`, `y` lie in the range of `i`.

## Main results

* `MMP.Mori.exists_isClosedImmersion_isCurve_of_mem_closedPoints_of_isAlgClosed`: the curve
  through two closed points.

## Implementation notes

A closed curve of `X` is recorded as a closed immersion `i : C ⟶ X` such that `i ≫ f` is a
curve over `k` in the sense of `MMP.Mori.IsCurve` (an integral, separated, finite type
`k`-scheme of Krull dimension one), so that the curve keeps its scheme structure. The
dimension hypothesis is `1 ≤ topologicalKrullDim X`, and points are taken in
`closedPoints X`. The statement holds over an arbitrary field
(`MMP.Mori.exists_isClosedImmersion_isCurve_of_mem_closedPoints`), from which it follows.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*][KM98]
-/

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

universe u

/-- On a variety `X` of dimension at least one over an algebraically closed field `k`, any two
closed points `x` and `y` (possibly equal) lie on a closed curve: there is a closed immersion
`i : C ⟶ X` such that `C` is a curve over `k` via `i ≫ f` and `x`, `y` lie in the range of
`i`. This is the special case over an algebraically closed field of
`MMP.Mori.exists_isClosedImmersion_isCurve_of_mem_closedPoints`, which holds over an arbitrary
field. -/
@[mmp "lem_mmp_foundation_km1a_curve_two_points"]
public theorem exists_isClosedImmersion_isCurve_of_mem_closedPoints_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f]
    (hdim : 1 ≤ topologicalKrullDim X) {x y : X}
    (hx : x ∈ closedPoints X) (hy : y ∈ closedPoints X) :
    ∃ (C : Scheme.{u}) (i : C ⟶ X),
      IsClosedImmersion i ∧ IsCurve k (i ≫ f) ∧ x ∈ Set.range i ∧ y ∈ Set.range i :=
  exists_isClosedImmersion_isCurve_of_mem_closedPoints f hdim hx hy

end MMP.Mori
