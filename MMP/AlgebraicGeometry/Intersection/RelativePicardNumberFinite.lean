module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Positivity
public import MMP.AlgebraicGeometry.Intersection.NumericalDivisorsFinitelyGenerated

/-!
# Finite relative Picard number with projective source

Let `π : X ⟶ S` be a projective morphism of complex varieties with `X` normal and projective.
Then the relative Picard number `ρ(X/S) = dim N¹(X/S)` is finite.

## Main results

* `RelativeNumericalDivisorClasses.finiteDimensional_of_finiteDimensional_numericalDivisorClasses`
* `RelativeNumericalDivisorClasses.finiteDimensional_of_isProjectiveVariety`

## Implementation notes

`N¹(X/S)` is `MMP.Fourfold.RelativeNumericalDivisorClasses sX π`, the real vector space of
`ℝ`-Cartier divisors modulo numerical equivalence over `S`. A divisor that is numerically trivial
on `X` is numerically trivial over `S`, so `N¹(X/S)` is a quotient of `N¹(X)`. `N¹(X)` is finite
dimensional by `MMP.Fourfold.exists_finset_cartierDivisor_degree_eq_sum_and_finiteDimensional`
(lem_mmp_projective_numerical_divisors_finite).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], §6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MMP.Fourfold

universe u

namespace MMP.Fourfold

namespace RelativeNumericalDivisorClasses

/-- If `N¹(X)` is finite dimensional then so is `N¹(X/S)` for any morphism `π : X ⟶ S`: a divisor
numerically trivial on `X` is numerically trivial over `S`, so `N¹(X/S)` is a quotient of
`N¹(X)`. -/
theorem finiteDimensional_of_finiteDimensional_numericalDivisorClasses {k : Type u} [Field k]
    {X S : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (π : X ⟶ S)
    [FiniteDimensional ℝ (NumericalDivisorClasses sX)] :
    FiniteDimensional ℝ (RelativeNumericalDivisorClasses sX π) := by
  have hle : numericallyTrivialDivisors sX ≤ LinearMap.ker (relativeDegreeMap sX π) :=
    fun D hD => funext fun C => (mem_numericallyTrivialDivisors.1 hD) C.1
  exact Module.Finite.of_surjective _ (Submodule.factor_surjective hle)

/-- **Finiteness of the relative Picard number.** Let `X` be a normal projective complex variety,
`S` a complex variety and `π : X ⟶ S` a projective morphism over `ℂ`. Then `N¹(X/S)`, the real
vector space of `ℝ`-Cartier divisors modulo numerical equivalence over `S`, is
finite-dimensional. -/
@[mmp "lem_mmp_foundation_projective_relative_picard_finite"]
theorem finiteDimensional_of_isProjectiveVariety {X S : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ))
    [IsProjectiveVariety ℂ sX] [IsNormal X]
    [IsVariety ℂ sS] (π : X ⟶ S) (hπ : IsProjective π) (hπS : π ≫ sS = sX) :
    FiniteDimensional ℝ (RelativeNumericalDivisorClasses sX π) := by
  obtain ⟨_, hP⟩ := (isProjectiveVariety_iff_isProjective' ℂ sX).1 ‹_›
  have := (exists_finset_cartierDivisor_degree_eq_sum_and_finiteDimensional sX hP).2
  exact finiteDimensional_of_finiteDimensional_numericalDivisorClasses sX π

end RelativeNumericalDivisorClasses

end MMP.Fourfold
