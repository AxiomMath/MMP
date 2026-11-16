module

public import MMP.AlgebraicGeometry.Positivity.NefBigOfAmpleApproximation

/-!
# Ample `ℚ`-divisors are nef and big

Let `Y` be a normal projective variety over a field `k` and `B` an ample `ℚ`-divisor on `Y`, so
that some positive multiple `mB` is a Cartier divisor with ample invertible sheaf `𝒪_Y(mB)`.
Then `B` is nef and big. Nefness holds because `(mB · C) > 0` for every closed curve `C ⊆ Y`;
bigness because `h⁰(Y, 𝒪_Y(rmB))` grows like `rⁿ` with `n = dim Y`.

## Main results

* `MMP.Mori.QDivisor.isNef_and_isBig_of_isAmple`: an ample `ℚ`-divisor is nef and big.

## Implementation notes

An ample `ℚ`-divisor in the sense of `MMP.Mori.QDivisor.IsAmple` is `ℚ`-Cartier by definition,
so the hypothesis "ample `ℚ`-Cartier" is the single hypothesis `B.IsAmple`. The base field is
arbitrary. An ample Cartier divisor `D` is nef and big, being approximated by the constant family
of ample `ℚ`-divisors `A_n = D` with effective error `E = 0`; if `mB = D`, then nefness of `B`
follows from `(B · C) = (1 / m) (D · C) ≥ 0`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.1
-/

namespace MMP.FourfoldProofs.Km3aAmpleNefBigProof

open CategoryTheory AlgebraicGeometry MMP.Mori

variable {k : Type} [Field k] {X : Scheme.{0}} (sX : X ⟶ Spec (.of k))

/-- An ample Cartier divisor is nef and big. -/
private theorem isNef_and_isBig_of_isAmple [MMP.Mori.IsProjectiveVariety k sX]
    [IsLocallyNoetherian X] [CompactSpace X] [IsNormal X] {D : Divisor X} (hD : D.IsCartier)
    (hA : D.IsAmple hD) :
    D.IsNef k sX ∧ D.IsBig k sX :=
  Divisor.isNef_and_isBig_of_numericallyEquivalent_isAmple_add_smul sX D hD 0 le_rfl
    QDivisor.isQCartier_zero (fun _ => Divisor.toQDivisor D) <|
    Set.infinite_univ.mono fun _ _ => ⟨⟨1, one_pos, D, by simp, hD, hA⟩,
      by simpa using .refl (QDivisor.isQCartier_toQDivisor hD)⟩

/-- A `ℚ`-divisor with a positive multiple that is a nef Cartier divisor is nef. -/
private theorem isNef_of_toQDivisor_eq_smul [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] {B : QDivisor X} {m : ℕ} (hm : 0 < m) {D : Divisor X}
    (hDB : Divisor.toQDivisor D = (m : ℚ) • B) (hN : D.IsNef k sX) : B.IsNef k sX := by
  obtain ⟨hD, hN⟩ := hN
  have hmB : Divisor.toQDivisor D = (m : ℤ) • B := by
    rw [hDB, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]
  have hB : B.IsQCartier := ⟨m, by exact_mod_cast hm.ne', D, hmB, hD⟩
  refine ⟨hB, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_eq_of_smul k sX i hC.le B hB hm D hD hmB]
  exact div_nonneg (by exact_mod_cast hN C i hC) m.cast_nonneg

end MMP.FourfoldProofs.Km3aAmpleNefBigProof

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

namespace QDivisor

/-- **Ample implies nef and big.** On a normal projective variety `Y` over a field `k`, an ample
`ℚ`-divisor `B` is nef and big. -/
@[mmp "lem_km3a_ample_nef_big"]
public theorem isNef_and_isBig_of_isAmple {k : Type} [Field k]
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsProjectiveVariety k sY] [IsNormal Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] [QuasiCompact sY]
    {B : QDivisor Y} (hB : B.IsAmple) :
    B.IsNef k sY ∧ B.IsBig k sY := by
  obtain ⟨m, hm, D, hDB, hD, hA⟩ := hB
  have hND := MMP.FourfoldProofs.Km3aAmpleNefBigProof.isNef_and_isBig_of_isAmple sY hD hA
  exact ⟨MMP.FourfoldProofs.Km3aAmpleNefBigProof.isNef_of_toQDivisor_eq_smul sY hm hDB hND.1,
    m, hm, D, hDB, hD, hND.2⟩

end QDivisor

end MMP.Mori

end
