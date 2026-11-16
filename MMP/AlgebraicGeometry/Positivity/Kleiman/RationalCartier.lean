module

public import MMP.AlgebraicGeometry.Positivity.Kleiman.AbsoluteCartier

/-!
# Kleiman's criterion for `ℚ`-Cartier divisors

Let `k` be an algebraically closed field of characteristic zero and `X` a projective variety
over `k`. Let `D = ∑ⱼ cⱼ Dⱼ` be a `ℚ`-linear combination of Cartier divisors such that
`(D · z) > 0` for every nonzero class `z` of the closed cone of curves `NE̅(X) ⊆ N₁(X)`. Then for
every positive integer `m` such that all `m cⱼ` are integers, the Cartier divisor
`mD = ∑ⱼ (m cⱼ) Dⱼ` is ample.

## Main results

* `MMP.Mori.isAmple_cartierSheaf_realization_of_forall_closedConeOfCurves_pos`: the criterion.

## Implementation notes

The value `D(z)` of a `ℚ`-Cartier divisor is that of the `ℝ`-Cartier divisor with the same
coefficients, `MMP.Fourfold.KCartierDivisor.toReal D`. The Cartier divisor `mD` is
`KCartierDivisor.realization (m • D) h`, where `h` says that `m • D` has integral coefficients;
ampleness of a Cartier divisor is ampleness of its invertible sheaf. By additivity of the degree
along a curve, `(mD · z) = m (D · z)` on `N₁(X)`, so `mD` is positive on `NE̅(X) ∖ 0`, hence
ample by `MMP.Mori.isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.18
* [S. Kleiman, *Toward a numerical theory of ampleness*][Kle66]
-/

section

open AlgebraicGeometry CategoryTheory MMP.Mori

namespace MMP.FourfoldProofs.MmpFoundationCharZeroRationalCartierKleimanProof

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- The degree along a proper curve, as an additive map on Cartier divisors. -/
private noncomputable def degreeSheafHom (C : ProperCurve sX) : X.CartierDivisor →+ ℤ :=
  AddMonoidHom.mk' (fun B => C.degree k (MMP.CartierDivisor.sheaf B)) fun B B' =>
    (degreeOn_eq_of_iso k sX C.ι C.dim_le (MMP.CartierDivisorSheaf.sheafMulIso B B')).symm.trans
      (degreeOn_tensorSheaf k sX C.ι C.dim_le _ _ (hLM :=
        Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
          X.ringCatSheaf.2 _ _))

/-- `(C · ∑ c_B B) = (C · c)` for the realization of an integral `ℚ`-Cartier divisor `c`. -/
private theorem intersectionNumber_ofCartier_realization (C : ProperCurve sX)
    (c : KCartierDivisor ℚ X) (h : ∀ D, ∃ n : ℤ, c D = n) :
    (C.cycle ℝ).intersectionNumber
        (KCartierDivisor.ofCartier ℝ (KCartierDivisor.realization c h)) =
      (C.cycle ℝ).intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal c) := by
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle,
    OneCycle.intersectionNumber_eq_sum]
  simp only [MMP.Fourfold.KCartierDivisor.toReal, Finsupp.mapRange.addMonoidHom_apply]
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp only [ProperCurve.cycle, Finsupp.sum_single_index, zero_mul, one_mul]
  change ((degreeSheafHom C (KCartierDivisor.realization c h) : ℤ) : ℝ) = _
  rw [KCartierDivisor.realization, Finsupp.sum, map_sum, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun D _ => ?_
  rw [map_zsmul, smul_eq_mul, Int.cast_mul]
  congr 1
  change _ = ((c D : ℚ) : ℝ)
  exact_mod_cast (Classical.choose_spec (h D)).symm

/-- On `N₁(X)`, the realization of an integral `ℚ`-Cartier divisor `c` defines the same linear
form as `c`. -/
private theorem intersectionNumber_ofCartier_realization_eq (c : KCartierDivisor ℚ X)
    (h : ∀ D, ∃ n : ℤ, c D = n) :
    NumericalCurveClasses.intersectionNumber (sX := sX)
        (KCartierDivisor.ofCartier ℝ (KCartierDivisor.realization c h)) =
      NumericalCurveClasses.intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal c) :=
  Submodule.linearMap_qext _ <| Finsupp.lhom_ext' fun C =>
    LinearMap.ext_ring (intersectionNumber_ofCartier_realization C c h)

/-- On `N₁(X)`, the realization of `m • D` for a `ℚ`-Cartier divisor `D` defines `m` times the
linear form of `D`. -/
private theorem intersectionNumber_realization_nsmul (D : KCartierDivisor ℚ X) (m : ℕ)
    (h : ∀ E, ∃ n : ℤ, ((m : ℚ) • D) E = n) :
    NumericalCurveClasses.intersectionNumber (sX := sX)
        (KCartierDivisor.ofCartier ℝ (KCartierDivisor.realization ((m : ℚ) • D) h)) =
      m • NumericalCurveClasses.intersectionNumber (MMP.Fourfold.KCartierDivisor.toReal D) := by
  rw [intersectionNumber_ofCartier_realization_eq, Nat.cast_smul_eq_nsmul, map_nsmul]
  exact Submodule.linearMap_qext _ (map_nsmul OneCycle.intersectionPairing m _)

end MMP.FourfoldProofs.MmpFoundationCharZeroRationalCartierKleimanProof

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace MMP.Mori

/-- **Kleiman's criterion for `ℚ`-Cartier divisors.** On a projective variety `X` over an
algebraically closed field of characteristic zero, let `D` be a `ℚ`-Cartier divisor with
`(D · z) > 0` for every nonzero `z ∈ NE̅(X)`. Then for every positive integer `m` for which
`m • D` has integral coefficients, the Cartier divisor `mD` is ample. -/
@[mmp "lem_mmp_foundation_char_zero_rational_cartier_kleiman"]
public theorem isAmple_cartierSheaf_realization_of_forall_closedConeOfCurves_pos {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsProjectiveVariety k sX] (D : KCartierDivisor ℚ X)
    (hpos : ∀ z ∈ closedConeOfCurves sX, z ≠ 0 →
      0 < NumericalCurveClasses.intersectionNumber (Fourfold.KCartierDivisor.toReal D) z)
    (m : ℕ) (hm : 0 < m) (h : ∀ E, ∃ n : ℤ, ((m : ℚ) • D) E = n) :
    Stacks.Ample.IsAmple X
      (MMP.CartierDivisor.sheaf (KCartierDivisor.realization ((m : ℚ) • D) h)) := by
  refine (isAmple_cartierSheaf_iff_forall_closedConeOfCurves_pos sX _).mpr fun z hz hz0 => ?_
  open FourfoldProofs.MmpFoundationCharZeroRationalCartierKleimanProof in
  rw [intersectionNumber_realization_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact mul_pos (by exact_mod_cast hm) (hpos z hz hz0)

end MMP.Mori

end
