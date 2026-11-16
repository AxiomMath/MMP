module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.BasepointFree.ProofData
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Basic
import MMP.AlgebraicGeometry.MMP.BasepointFree.AdaptedResolution
import MMP.AlgebraicGeometry.Positivity.NefThresholdConvexity
import MMP.AlgebraicGeometry.Intersection.CurveDegreeAdditive
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Abundance.Basic

/-!
# Strictly below the nef threshold: nef and big

Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r`, and let `x, t ∈ ℚ` with
`x > 0` and `0 ≤ t < rx`. Then the `ℚ`-Cartier `ℚ`-divisor `xH + t(K_X + Δ)` is nef and big.

## Main results

* `MMP.Positivity.IsRationalityDatum.isNef_and_isBig_of_lt`

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.4
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.Positivity

section Helpers

variable {k : Type} [Field k] {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]

/-- A nonnegative rational multiple of a nef `ℚ`-divisor is nef. -/
private theorem isNef_smul {D : QDivisor X} (hD : D.IsNef k sX) {q : ℚ} (hq : 0 ≤ q) :
    (q • D).IsNef k sX := by
  obtain ⟨hDq, h⟩ := hD
  have hqD : (q • D).IsQCartier := MMP.Flips.QDivisor.IsQCartier.qsmul hDq q
  refine ⟨hqD, fun C i _ _ _ hC => ?_⟩
  rw [MMP.Fourfold.intersectionNumber_smul sX i hC.le D hDq q hqD]
  exact mul_nonneg hq (h C i hC)

/-- If `H + tK` is nef in the sense of `QDivisor.IsNefCombination` with `t` rational, the
`ℚ`-divisor `H + tK` is nef. -/
private theorem isNef_add_smul_of_isNefCombination {H K : QDivisor X} {t : ℚ}
    (h : QDivisor.IsNefCombination k sX H K t) : (H + t • K).IsNef k sX := by
  obtain ⟨hH, hK, hC⟩ := h
  have htK : (t • K).IsQCartier := MMP.Flips.QDivisor.IsQCartier.qsmul hK t
  have hq : (H + t • K).IsQCartier := hH.add htK
  refine ⟨hq, fun C i _ _ _ hC' => ?_⟩
  rw [QDivisor.intersectionNumber_add' k sX i hC'.le H (t • K) hH htK hq,
    MMP.Fourfold.intersectionNumber_smul sX i hC'.le K hK t htK]
  exact_mod_cast hC C i hC'

/-- A positive integral multiple of a big divisor is big. -/
private theorem isBig_zsmul {H : Divisor X} (hH : H.IsBig k sX) {N : ℤ} (hN : 0 < N) :
    (N • H).IsBig k sX := by
  obtain ⟨n, hn, c, hc, k₀, h⟩ := hH
  refine ⟨n, hn, c * (N : ℝ) ^ n, by positivity, max k₀ 0, fun m hm => ?_⟩
  have hm0 : 0 ≤ m := le_trans (le_max_right _ _) hm
  have hmN : k₀ ≤ m * N := by
    nlinarith [le_trans (le_max_left _ _) hm]
  have := h (m * N) hmN
  rw [smul_smul]
  push_cast at this
  rw [mul_pow] at this
  linarith

/-- A positive rational multiple of a big Cartier divisor is big. -/
private theorem isBig_smul_toQDivisor {H : Divisor X} (hHc : H.IsCartier) (hH : H.IsBig k sX)
    {c : ℚ} (hc : 0 < c) : (c • Divisor.toQDivisor H).IsBig k sX := by
  refine ⟨c.den, c.den_pos, c.num • H, ?_, hHc.zsmul _, isBig_zsmul hH (Rat.num_pos.2 hc)⟩
  rw [map_zsmul, smul_smul, ← Int.cast_smul_eq_zsmul ℚ, Rat.den_mul_eq_num]

/-- Let `H` be a nef and big Cartier divisor and `L` a `ℚ`-divisor. If `0 < x`, `0 ≤ t < t'`
and `xH + t'L` is nef, then `xH + tL` is nef and big. -/
private theorem isNef_and_isBig_add_smul_of_lt [IsAlgClosed k] [CharZero k]
    [MMP.Mori.IsProperVariety k sX] {H : Divisor X} (hHc : H.IsCartier)
    (hHnef : (Divisor.toQDivisor H).IsNef k sX) (hHbig : H.IsBig k sX) {L : QDivisor X}
    {x t t' : ℚ} (hx : 0 < x) (ht0 : 0 ≤ t) (htt' : t < t')
    (hN : (x • Divisor.toQDivisor H + t' • L).IsNef k sX) :
    (x • Divisor.toQDivisor H + t • L).IsNef k sX ∧
      (x • Divisor.toQDivisor H + t • L).IsBig k sX := by
  have ht'0 : 0 < t' := ht0.trans_lt htt'
  have hs1 : t / t' < 1 := (div_lt_one ht'0).2 htt'
  have hEq : x • Divisor.toQDivisor H + t • L = ((1 - t / t') * x) • Divisor.toQDivisor H +
      (t / t') • (x • Divisor.toQDivisor H + t' • L) := by
    conv_lhs => rw [← div_mul_cancel₀ t ht'0.ne']
    module
  rw [hEq]
  exact QDivisor.IsNef.isNef_and_isBig_add (isNef_smul hHnef (by nlinarith))
    (isBig_smul_toQDivisor hHc hHbig (by nlinarith)) (isNef_smul hN (by positivity))

end Helpers

public section

/-- **Strictly below the nef threshold the combination is nef and big** (used throughout
KM 3.4). Let `(X, Δ, a, H)` be a rationality datum with nef threshold `r`, and let `x, t ∈ ℚ`
with `x > 0` and `0 ≤ t < rx`. Then the `ℚ`-divisor `xH + t(K_X + Δ)` is nef and big. -/
@[mmp "lem_km3b_below_threshold_nef_big"]
theorem IsRationalityDatum.isNef_and_isBig_of_lt {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X}
    {Δ : QDivisor X} {a : ℤ} {H : Divisor X} (hD : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    {x t : ℚ} (hx : 0 < x) (ht0 : 0 ≤ t) (htr : (t : ℝ) < r * x) :
    (x • Divisor.toQDivisor H + t • (Divisor.toQDivisor K + Δ)).IsNef k sX ∧
      (x • Divisor.toQDivisor H + t • (Divisor.toQDivisor K + Δ)).IsBig k sX := by
  haveI := hD.isProperVariety
  obtain ⟨t', htt', ht'r⟩ := exists_rat_btwn htr
  have htt'q : t < t' := by exact_mod_cast htt'
  exact isNef_and_isBig_add_smul_of_lt hD.isCartier_H
    ((QDivisor.isNef_toQDivisor_iff H hD.isCartier_H).2 hD.isNef_H) hD.isBig_H hx ht0 htt'q
    (isNef_add_smul_of_isNefCombination (IsRationalityDatum.isNefCombination_of_le hD hr hx
      (by exact_mod_cast ht0.trans htt'q.le) ht'r.le))

end

end MMP.Positivity
