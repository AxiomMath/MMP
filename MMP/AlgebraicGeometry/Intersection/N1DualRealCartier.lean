module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProper

/-!
# Linear functionals on `N₁(X)` are real Cartier evaluations

Let `k` be an algebraically closed field of characteristic zero and `X` a proper variety over
`k`. Every real linear form on the finite-dimensional space `N₁(X)` of numerical classes of
curves is `z ↦ (z · D)` for some `ℝ`-Cartier divisor `D`, that is, for a finite real linear
combination of Cartier divisors. Consequently the intersection pairing identifies the space
`N¹(X)_ℝ` of `ℝ`-Cartier divisors modulo those of degree zero on every curve with the dual of
`N₁(X)`. Only numerical equivalence is involved; nothing is asserted about the Néron–Severi
group.

Since `N₁(X)` is finite dimensional and the intersection pairing separates its points, the
induced map `N¹(X)_ℝ → N₁(X)^*` is surjective (`LinearMap.flip_injective_iff₂`); it is
injective by the definition of numerical equivalence of divisors.

## Main results

* `MMP.Mori.NumericalCurveClasses.exists_intersectionNumber_eq_and_bijective_numericalPairing`:
  every `φ ∈ N₁(X)^*` is `MMP.Mori.NumericalCurveClasses.intersectionNumber D` for an
  `ℝ`-Cartier divisor `D`, and `MMP.Fourfold.numericalPairing : N¹(X)_ℝ → N₁(X)^*` is bijective.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Chapter 1.
-/

@[expose] public section

open AlgebraicGeometry

namespace MMP.Mori

/-- On a proper variety `X` over an algebraically closed field of characteristic zero, every real
linear form on `N₁(X)` is the evaluation `z ↦ (z · D)` of an `ℝ`-Cartier divisor `D`, and the
intersection pairing `N¹(X)_ℝ → N₁(X)^*` is a bijection. -/
@[mmp "lem_mmp_foundation_n1_functionals_real_cartier"]
public theorem NumericalCurveClasses.exists_intersectionNumber_eq_and_bijective_numericalPairing
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProperVariety k sX] :
    (∀ φ : Module.Dual ℝ (NumericalCurveClasses sX),
        ∃ D : KCartierDivisor ℝ X, NumericalCurveClasses.intersectionNumber D = φ) ∧
      Function.Bijective (MMP.Fourfold.numericalPairing sX) := by
  haveI := NumericalCurveClasses.finiteDimensional_of_isProperVariety sX
  have hsurj : Function.Surjective (MMP.Fourfold.numericalPairing sX) :=
    LinearMap.flip_injective_iff₂.mp (MMP.Fourfold.numericalPairing_flip_injective sX)
  refine ⟨fun φ => ?_, MMP.Fourfold.numericalPairing_injective sX, hsurj⟩
  obtain ⟨d, rfl⟩ := hsurj φ
  obtain ⟨D, rfl⟩ := (MMP.Fourfold.numericallyTrivialDivisors sX).mkQ_surjective d
  exact ⟨D, Submodule.linearMap_qext _ (LinearMap.ext fun Z => rfl)⟩

end MMP.Mori
