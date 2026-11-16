module

public import MMP.AlgebraicGeometry.Positivity.AmpleNumerical

/-!
# Ample plus nef is ample

Let `Y` be a normal projective variety over a field `k`, `A` an ample `ℚ`-divisor, `Nᵢ`
(`i ∈ s`, a finite, possibly empty, index set) nef `ℚ`-divisors, and `B` a `ℚ`-Cartier
`ℚ`-divisor numerically equivalent to `A + ∑ᵢ Nᵢ`. Then `B` is ample. Taking
`B = A + ∑ᵢ Nᵢ` (numerically equivalent to itself by
`MMP.Mori.QDivisor.NumericallyEquivalent.refl`) shows that `A + ∑ᵢ Nᵢ` is ample. The proof is
Kleiman's criterion: `B` is strictly positive on the closed cone of curves minus the origin.

## Main results

* `MMP.Mori.QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef`

## Implementation notes

The nef summands are indexed by a `Finset` of an arbitrary type rather than by `1, …, k`; the
case `k = 0` is `s = ∅`. Both nefness (`QDivisor.IsNef`) and numerical equivalence
(`QDivisor.NumericallyEquivalent`) include `ℚ`-Cartierness, so "`Nᵢ`, `B` `ℚ`-Cartier" is
carried by `hN` and `hB`; ampleness `QDivisor.IsAmple` includes it for `A`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori.QDivisor

/-- The zero `ℚ`-divisor is nef, being numerically trivial. -/
private theorem isNef_zero {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    [IsNormal X] [IsLocallyNoetherian X] [QuasiCompact sX] :
    (0 : QDivisor X).IsNef k sX :=
  have ⟨h0, h⟩ := (isNumericallyTrivial_iff 0).mp
    (NumericallyEquivalent.refl (k := k) (sX := sX) isQCartier_zero)
  ⟨h0, fun C i _ _ _ hC => (h C i hC).ge⟩

/-- **Ample plus nef is ample.** On a normal projective variety `Y` over a field `k`, let `A` be
an ample `ℚ`-divisor, `N i` (`i ∈ s`) nef `ℚ`-divisors, and `B` a `ℚ`-divisor numerically
equivalent to `A + ∑ i ∈ s, N i`. Then `B` is ample. -/
@[mmp "lem_km3a_nef_plus_ample_ample"]
theorem isAmple_of_numericallyEquivalent_add_sum_of_isNef {k : Type} [Field k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sY] [IsNormal Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] [QuasiCompact sY]
    {ι : Type*} (s : Finset ι) {A B : QDivisor Y} (N : ι → QDivisor Y) (hA : A.IsAmple)
    (hN : ∀ i ∈ s, (N i).IsNef k sY)
    (hB : B.NumericallyEquivalent k sY (A + ∑ i ∈ s, N i)) :
    B.IsAmple := by
  have hsum : (∑ i ∈ s, N i).IsNef k sY :=
    Finset.sum_induction _ (IsNef k sY) (fun _ _ => .add) (isNef_zero sY) hN
  obtain ⟨m, hm, D, hD, hDc⟩ := hB.1.exists_pos
  have hD' : Divisor.toQDivisor D = (m : ℚ) • B := by
    rw [hD]; exact (Int.cast_smul_eq_zsmul ℚ (m : ℤ) B).symm
  exact ⟨m, hm, D, hD', hDc,
    isAmple_of_numericallyEquivalent_add_of_isNef sY hA hsum hB m hm D hD' hDc⟩

end MMP.Mori.QDivisor

end
