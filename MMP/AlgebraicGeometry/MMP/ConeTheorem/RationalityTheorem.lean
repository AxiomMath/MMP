module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.DenominatorBound

@[expose] public section

section

/-!
# The rationality theorem

Let `(X, Δ)` be a proper klt pair over an algebraically closed field `k` of characteristic zero,
with `Δ` effective and `K_X + Δ` not nef, let `a > 0` be an integer with `a(K_X + Δ)` Cartier,
and let `H` be a nef and big Cartier divisor on `X`, so that `(X, Δ, a, H)` is a rationality
datum. If `r` is the nef threshold of `H` with respect to `K_X + Δ`, the largest real `t` with
`H + t(K_X + Δ)` nef, then `r = u / v` with integers `u, v` and `0 < v ≤ a(dim X + 1)`.
The threshold is nonnegative since `H` is nef; for `r = 0` take `u = 0`, `v = 1`, and for
`r > 0` this is `MMP.Mori.IsRationalityDatum.exists_eq_div_of_isNefThreshold`.

## Main results

* `MMP.Mori.IsRationalityDatum.exists_den_le_of_isNefThreshold`: the nef threshold of a
  rationality datum is `u / v` with `0 < v ≤ a(n + 1)`.

## Implementation notes

The dimension `n` of `X` is the one carried by the klt pair inside `IsRationalityDatum`, so
`a(dim X + 1)` is `a * (n + 1)`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.5
-/

public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **The rationality theorem** (Kollár–Mori, Theorem 3.5). Let `(X, Δ, a, H)` be a rationality
datum of dimension `n` and `r` the nef threshold of `H` with respect to `K_X + Δ`. Then `r = u / v`
with `u, v ∈ ℤ` and `0 < v ≤ a(n + 1)`. -/
@[mmp "thm_km3b_rationality_theorem"]
public theorem IsRationalityDatum.exists_den_le_of_isNefThreshold {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X}
    (hD : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r) :
    ∃ u v : ℤ, 0 < v ∧ v ≤ a * (n + 1) ∧ r = u / v := by
  haveI : IsProper sX := hD.isProperVariety.toIsProper
  obtain ⟨-, hKq, -⟩ := hr.1
  obtain ⟨r₀, hr₀, -, -, -, -, huniq⟩ := MMP.Positivity.exists_isNefThreshold hKq hD.not_isNef
    ((QDivisor.isNef_toQDivisor_iff H hD.isCartier_H).mpr hD.isNef_H)
  rcases (((huniq r).1 hr) ▸ hr₀ : 0 ≤ r).lt_or_eq with hpos | hzero
  · exact hD.exists_eq_div_of_isNefThreshold hr hpos
  · exact ⟨0, 1, one_pos, by nlinarith [hD.pos], by simp [← hzero]⟩

end MMP.Mori

end
