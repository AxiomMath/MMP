module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Positivity.BaseLocusSum

/-!
# Below the nef threshold (KM 3.4, convexity of the nef cone)

For a rationality datum `(X, Δ, a, H)` with nef threshold `r`, `x ∈ ℚ_{>0}` and `0 ≤ t ≤ rx`, the
`ℝ`-divisor `xH + t(K_X + Δ)` is nef.

## Main results

* `MMP.Positivity.IsRationalityDatum.isNefCombination_of_le`
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace MMP.Positivity

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]

omit [CompactSpace X] in
/-- **Convexity of the nef cone** (used throughout KM 3.4). Let `(X, Δ, a, H)` be a rationality
datum with nef threshold `r`, and let `x ∈ ℚ_{>0}` and `t ∈ ℝ` with `0 ≤ t ≤ rx`. Then the
`ℝ`-divisor `xH + t(K_X + Δ)` is nef. -/
@[mmp "lem_km3b_below_threshold_nef"]
theorem IsRationalityDatum.isNefCombination_of_le {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {a : ℤ} {H : Divisor X} (hD : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    {x : ℚ} (hx : 0 < x) {t : ℝ} (ht0 : 0 ≤ t) (htr : t ≤ r * x) :
    QDivisor.IsNefCombination k sX (x • Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) t := by
  obtain ⟨hHC, hHnef⟩ := hD.isNef_H
  obtain ⟨hHq, hKq, hrC⟩ := hr.1
  set N : ℕ := x.num.toNat with hN
  have hNnum : (N : ℚ) = x.num := by
    rw [hN]; exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hx.le)
  have hEq : Divisor.toQDivisor (N • H) = ((x.den : ℕ) : ℤ) • (x • Divisor.toQDivisor H) := by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
    congr 1
    rw [hNnum, Int.cast_natCast, mul_comm]
    exact (Rat.mul_den_eq_num x).symm
  have hq : (x • Divisor.toQDivisor H).IsQCartier :=
    ⟨x.den, by exact_mod_cast x.den_ne_zero, N • H, hEq, hHC.nsmul N⟩
  refine ⟨hq, hKq, fun C i _ _ _ hC => ?_⟩
  have h1 := QDivisor.intersectionNumber_eq_of_smul k sX i hC.le (x • Divisor.toQDivisor H) hq
    x.den_pos (N • H) (hHC.nsmul N) hEq
  rw [Divisor.degreeOn_nsmul' k sX i hC.le H hHC N] at h1
  have h2 := QDivisor.intersectionNumber_toQDivisor k sX i hC.le H hHC hHq
  have h3 := hrC C i hC
  have h4 := hHnef C i hC
  rw [h2] at h3
  have hx' : ((((N : ℤ) * Divisor.degreeOn k sX i hC.le H hHC : ℤ) : ℚ) / x.den : ℚ) =
      x * Divisor.degreeOn k sX i hC.le H hHC := by
    have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    push_cast
    rw [hNnum, div_eq_iff hden, mul_right_comm, Rat.mul_den_eq_num]
  rw [h1, hx']
  push_cast at h3 h4 ⊢
  set d : ℝ := (Divisor.degreeOn k sX i hC.le H hHC : ℝ)
  set κ : ℝ := ((Divisor.toQDivisor K + Δ).intersectionNumber k sX i hC.le hKq : ℝ)
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  rcases le_or_gt 0 κ with hκ | hκ
  · positivity
  · nlinarith [mul_nonneg hx0.le h3, mul_le_mul_of_nonpos_right htr hκ.le]

end MMP.Positivity
