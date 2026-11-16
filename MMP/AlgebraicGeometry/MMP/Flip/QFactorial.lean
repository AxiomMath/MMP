module

public import MMP.AlgebraicGeometry.MMP.Flip.WeilDivisorFormula

/-!
# A flip of a `ℚ`-factorial dlt pair is `ℚ`-factorial

Let `(X, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field `k` of
characteristic zero, `R` a `(K_X + Δ)`-negative extremal ray of `NE̅(X)`, `g : X ⟶ Y` a
contraction of `R`, and `g⁺ : X⁺ ⟶ Y` a `(K + Δ)`-flip of `g`. Then `X⁺` is `ℚ`-factorial.
Indeed, by `MMP.Mori.exists_linearlyEquivalent_pullback_of_isFlip`, for every Weil divisor `D⁺`
on `X⁺` some multiple `m D⁺` is linearly equivalent to a difference of Cartier divisors.

## Main results

* `MMP.Mori.isQFactorial_of_isFlip`: the flip `X⁺` is `ℚ`-factorial.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori],
  Proposition 3.37(1)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

/-- **A flip of a `ℚ`-factorial dlt pair is `ℚ`-factorial** (Kollár–Mori, Proposition 3.37(1)).
Let `(X, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field of
characteristic zero with canonical divisor `K`, `R` a `(K + Δ)`-negative extremal ray of
`NE̅(X)`, `g : X ⟶ Y` a contraction of `R`, and `g⁺ : X⁺ ⟶ Y` a `(K + Δ)`-flip of `g`.
Then `X⁺` is `ℚ`-factorial. -/
@[mmp "prop_km3c_flip_qfactorial"]
public theorem isQFactorial_of_isFlip
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX]
    (hQ : MMP.Fourfold.IsQFactorial sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hdlt : IsDltPair sX n K Δ) {R : Set (NumericalCurveClasses sX)}
    (hRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hR : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2) R)
    {Y : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of k)} {g : X ⟶ Y}
    (hg : IsContractionOfFace k sX sY R g)
    {X' : Scheme.{0}} [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX' : X' ⟶ Spec (.of k)} {gp : X' ⟶ Y} (hflip : IsFlip sX sY sX' K Δ g gp) :
    MMP.Fourfold.IsQFactorial sX' := by
  refine ⟨hflip.isNormalVariety, fun D' => ?_⟩
  obtain ⟨m, hm, r, hc, DY, hDY, hB, hlin⟩ :=
    exists_linearlyEquivalent_pullback_of_isFlip hQ hdlt hRay hR hg hflip D'
  refine ⟨m, hm, ?_⟩
  have hsum : ((m : ℤ) • D' + hc.toDivisor).IsCartier :=
    Divisor.IsCartier.of_linearlyEquivalent hlin
      ((Divisor.isPullback_pullback hDY hB).isCartier hDY)
  have h := hsum.sub hc.isCartier_toDivisor
  rwa [add_sub_cancel_right] at h

end MMP.Mori
