module

public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.Intersection.NumericalDivisorsFinitelyGenerated

/-!
# Finiteness of the Picard number of a projective complex variety

Let `X` be a projective variety over `ℂ`. Its Picard number
`ρ(X) = dim_ℝ N₁(X) ∈ ℕ ∪ {∞}` (`MMP.Mori.picardNumber`) is finite. Here `N₁(X)`
(`MMP.Mori.NumericalCurveClasses`) is the space of real 1-cycles on `X` modulo the cycles of
degree zero against every invertible sheaf, that is, against every Cartier divisor.

The real space `N¹(X)_ℝ` of `ℝ`-Cartier divisors modulo numerical equivalence is
finite-dimensional
(`MMP.Fourfold.exists_finset_cartierDivisor_degree_eq_sum_and_finiteDimensional`). The
intersection pairing `N₁(X) → N¹(X)_ℝ^*` is injective on the integral scheme `X`
(`MMP.Fourfold.numericalPairing_flip_injective`): a curve class of degree zero against every
Cartier divisor is numerically trivial, since every invertible sheaf on `X` is `𝒪_X(E)` for a
Cartier divisor `E`. So `N₁(X)` is finite-dimensional, and `ρ(X) = dim_ℝ N₁(X) < ∞`.

## Main results

* `MMP.Mori.picardNumber_lt_top_of_isProjectiveVariety`: `ρ(X) < ∞` for a projective
  complex variety `X`.

## Implementation notes

The source maps a cycle `z` to `(D₁ · z, …, D_r · z) ∈ ℝʳ` for Cartier divisors `Dⱼ` whose
classes generate the numerical divisor group. The injection used here into the dual of
`N¹(X)_ℝ`, a space spanned by the classes of the `Dⱼ`, is the same map up to the
identification of that dual with a subspace of `ℝʳ`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Chapter 1.
-/

@[expose] public section

open AlgebraicGeometry

namespace MMP.Mori

/-- The Picard number `ρ(X) = dim_ℝ N₁(X)` of a projective complex variety `X` is finite. -/
@[mmp "lem_mmp_foundation_projective_picard_finite"]
public theorem picardNumber_lt_top_of_isProjectiveVariety {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [IsProjectiveVariety ℂ sX] : picardNumber sX < ⊤ := by
  obtain ⟨_, hP⟩ := (isProjectiveVariety_iff_isProjective' ℂ sX).1 ‹_›
  have := (MMP.Fourfold.exists_finset_cartierDivisor_degree_eq_sum_and_finiteDimensional
    sX hP).2
  have : FiniteDimensional ℝ (NumericalCurveClasses sX) :=
    Module.Finite.of_injective _ (MMP.Fourfold.numericalPairing_flip_injective sX)
  exact Cardinal.toENat_lt_top.mpr (Module.rank_lt_aleph0 ℝ _)

end MMP.Mori
