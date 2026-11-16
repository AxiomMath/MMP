module

public import MMP.AlgebraicGeometry.Intersection.RelativeNumericalDuality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective

/-!
# Finite dimension of relative numerical divisor classes

Let `k` be an algebraically closed field of characteristic zero and `h : Y ⟶ Z` a projective
morphism of quasi-projective `k`-varieties. The real vector space `N¹(Y/Z)` of `ℝ`-Cartier
divisors on `Y` modulo those of degree zero on every curve contracted by `h` is
finite-dimensional, and it is spanned by the classes of Cartier divisors.

## Main results

* `MMP.Fourfold.RelativeNumericalDivisorClasses.finiteDimensional_and_span_ofCartier_eq_top`:
  `N¹(Y/Z)` is finite-dimensional and spanned by the classes of Cartier divisors.

## Implementation notes

`N¹(Y/Z)` is `MMP.Fourfold.RelativeNumericalDivisorClasses`, the quotient of
`MMP.Mori.KCartierDivisor ℝ Y` by the kernel of the degrees on contracted curves, and the class
of a Cartier divisor `E` is the class of `MMP.Mori.KCartierDivisor.ofCartier ℝ E`. The ground
field is any algebraically closed field of characteristic zero, of which `ℂ` is the case of the
source.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][Kollar1992], 18.12
-/

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

namespace RelativeNumericalDivisorClasses

/-- **Finiteness of `N¹(Y/Z)`.** Let `k` be algebraically closed of characteristic zero and
`h : Y ⟶ Z` a projective morphism of quasi-projective `k`-varieties. Then the real vector space
`MMP.Fourfold.RelativeNumericalDivisorClasses sY h` of `ℝ`-Cartier divisors modulo numerical
equivalence over `Z` is finite-dimensional, and it is spanned by the classes of Cartier
divisors. -/
@[mmp "lem_mmp_foundation_fa18_relative_numerical_divisors_finite"]
public theorem finiteDimensional_and_span_ofCartier_eq_top {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {Y Z : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [IsQuasiProjectiveVariety k sY] [IsQuasiProjectiveVariety k sZ] (h : Y ⟶ Z)
    (hproj : IsProjective h) (hh : h ≫ sZ = sY) :
    FiniteDimensional ℝ (RelativeNumericalDivisorClasses sY h) ∧
      Submodule.span ℝ (Set.range fun E : Y.CartierDivisor =>
        relativeNumericalDivisorClass sY h (MMP.Mori.KCartierDivisor.ofCartier ℝ E)) = ⊤ :=
  have := hproj.isProper
  (MMP.Mori.RelativeNumericalCurveClasses.exists_linearEquiv_dual_of_isProper sY sZ h hh).2.2.2

end RelativeNumericalDivisorClasses

end MMP.Fourfold

end
