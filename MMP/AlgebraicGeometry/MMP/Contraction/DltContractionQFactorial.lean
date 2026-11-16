module

public import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialQFactorialPullback
public import MMP.AlgebraicGeometry.MMP.Contraction.FiberTypeQFactorialPullback
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary

/-!
# Divisorial and fibre type contractions of `ℚ`-factorial dlt pairs

Let `X` be a `ℚ`-factorial projective variety over an algebraically closed field `k` of
characteristic zero, `(X, Δ)` a dlt pair, `R` a `(K_X + Δ)`-negative extremal ray of the closed
cone of curves `NE̅(X)`, and `g : X ⟶ Z` a contraction of `R`. If `g` is a divisorial
contraction or a contraction of fibre type, then `Z` is `ℚ`-factorial.

## Main results

* `MMP.Mori.isQFactorial_of_isDltPair_of_isDivisorialContraction_or_isFiberTypeContraction`:
  the statement above.

## Implementation notes

The contraction is given as `MMP.Mori.IsDivisorialContraction` or
`MMP.Mori.IsFiberTypeContraction`; each carries the extremality of `R` and the contraction
`MMP.Mori.IsContractionOfFace` (so `Z` is projective over `k`). The negativity of `R` is
`MMP.Mori.IsNegativeExtremalFace` for the linear form `(K + Δ) · _`. `MMP.Fourfold.IsQFactorial`
is stated for a locally noetherian normal scheme, so `Z` carries the instance arguments
`[IsLocallyNoetherian Z] [IsNormal Z]`; both hold for the target of a contraction of a normal
projective variety, so they do not restrict the statement.

For small rational `δ > 0` the pair `(X, (1 - δ)Δ)` is klt and `R` is still
`(K_X + (1 - δ)Δ)`-negative: since `R` is a ray, negativity is a single strict inequality, which
persists under small perturbation. The contraction theorem then gives `(R, g)` the pullback
property for line bundles, and the divisorial and fibre type cases give that `Z` is `ℚ`-factorial.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori],
  Proposition 3.36(1)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- The curve form of `D + (1 - δ)Δ` is that of `D + Δ` minus `δ` times that of `Δ`. -/
private theorem curveForm_add_one_sub_smul_apply {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] (D Δ : QDivisor X) (δ : ℚ)
    (h : (D + (1 - δ) • Δ).IsQCartier) (hDΔ : (D + Δ).IsQCartier) (hΔ : Δ.IsQCartier)
    (hδΔ : ((-δ) • Δ).IsQCartier) (z : NumericalCurveClasses sX) :
    MMP.Fourfold.QDivisor.curveForm sX (D + (1 - δ) • Δ) h z =
      MMP.Fourfold.QDivisor.curveForm sX (D + Δ) hDΔ z -
        (δ : ℝ) * MMP.Fourfold.QDivisor.curveForm sX Δ hΔ z := by
  have e : D + (1 - δ) • Δ = (D + Δ) + (-δ) • Δ := by
    rw [sub_smul, one_smul, neg_smul]; abel
  have key : MMP.Fourfold.QDivisor.curveForm sX (D + (1 - δ) • Δ) h =
      MMP.Fourfold.QDivisor.curveForm sX (D + Δ) hDΔ -
        (δ : ℝ) • MMP.Fourfold.QDivisor.curveForm sX Δ hΔ := by
    refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply,
      MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      MMP.Fourfold.intersectionNumber_congr sX C.ι C.dim_le h (e ▸ h) e,
      QDivisor.intersectionNumber_add' k sX C.ι C.dim_le _ _ hDΔ hδΔ,
      QDivisor.intersectionNumber_smul k sX C.ι C.dim_le _ _ hΔ hδΔ]
    push_cast; simp [smul_eq_mul]; ring
  rw [key]; rfl

/-- **Divisorial and fibre type contractions preserve `ℚ`-factoriality** (Kollár–Mori,
Proposition 3.36(1)). Let `X` be a `ℚ`-factorial projective variety over an algebraically closed
field `k` of characteristic zero, `(X, Δ)` a dlt pair with canonical divisor `K`, `R` a
`(K + Δ)`-negative extremal face of `NE̅(X)`, and `g : X ⟶ Z` a contraction of the extremal ray
`R` which is divisorial or of fibre type. Then `Z` is `ℚ`-factorial. -/
@[mmp "prop_km3c_divisorial_or_fano_contraction_qfactorial"]
public theorem isQFactorial_of_isDltPair_of_isDivisorialContraction_or_isFiberTypeContraction
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX]
    (hQ : MMP.Fourfold.IsQFactorial sX) {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hdlt : IsDltPair sX n K Δ) {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2) R)
    {Z : Scheme.{0}} [IsLocallyNoetherian Z] [IsNormal Z] {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z}
    (hg : IsDivisorialContraction k sX sZ R g ∨ IsFiberTypeContraction k sX sZ R g) :
    MMP.Fourfold.IsQFactorial sZ := by
  have hRay : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R := by
    rcases hg with hg | hg
    exacts [hg.isExtremalRay, hg.isExtremalRay]
  have hcon : IsContractionOfFace k sX sZ R g := by
    rcases hg with hg | hg
    exacts [hg.isContractionOfFace, hg.isContractionOfFace]
  obtain ⟨v, hv0, hRv⟩ := hRay.2
  have hqC := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ
  set L := MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hdlt.1.2.2
  set M := MMP.Fourfold.QDivisor.curveForm sX Δ (hqC Δ)
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul ℝ v⟩
  have ha : L v < 0 := hR.2.2 v hvR hv0
  obtain ⟨δ₀, hδ₀, hklt⟩ := hdlt.exists_forall_isKltPair_one_sub_smul hQ
    (isQuasiProjective_of_isProjective
      (AlgebraicGeometry.IsProjectiveVariety.isProjective (k := k) (f := sX)).isProjective)
  have hε : 0 < -L v / (|M v| + 1) := div_pos (neg_pos.mpr ha) (by positivity)
  obtain ⟨δ, hδpos, hδlt⟩ := exists_rat_btwn
    (lt_min hε (lt_min (Rat.cast_pos.mpr hδ₀) one_pos))
  simp only [lt_min_iff] at hδlt
  obtain ⟨hδε, hδδ₀, hδ1⟩ := hδlt
  have hδpos' : (0 : ℚ) < δ := mod_cast hδpos
  have hδ1' : δ < 1 := mod_cast hδ1
  have hk := hklt δ hδpos' (mod_cast hδδ₀)
  have hform : ∀ z, MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + (1 - δ) • Δ)
      hk.1.2.2 z = L z - (δ : ℝ) * M z := fun z =>
    curveForm_add_one_sub_smul_apply sX _ Δ δ hk.1.2.2 hdlt.1.2.2 (hqC Δ) (hqC _) z
  have hvneg : L v - (δ : ℝ) * M v < 0 := by
    have h1 : (δ : ℝ) * (|M v| + 1) < -L v := (lt_div_iff₀ (by positivity)).mp hδε
    have h2 : -(δ : ℝ) * M v ≤ δ * |M v| := by
      rw [neg_mul, ← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_le_abs _) hδpos.le
    nlinarith
  have hneg : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + (1 - δ) • Δ) hk.1.2.2) R := by
    refine ⟨hR.1, hR.2.1, fun z hz hz0 => ?_⟩
    rw [hRv] at hz
    obtain ⟨c, hc, rfl⟩ := hz
    have hc0 : 0 < c := lt_of_le_of_ne hc (by rintro rfl; exact hz0 (zero_smul ℝ v))
    rw [hform, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  have hΔeff : ((1 - δ) • Δ).IsEffective := by
    rw [DivisorWithCoeffs.isEffective_iff_nonneg]
    have : 0 ≤ Δ := DivisorWithCoeffs.isEffective_iff_nonneg.mp (fun P => (hdlt.2.1 P).1)
    exact smul_nonneg (by linarith) this
  have hpb := fun (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
      (hL : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R → C.degree k L = 0) =>
    exists_isInvertible_iso_pullback_of_isContractionOfFace hk hΔeff hneg hcon L hL
  rcases hg with hg | hg
  · obtain ⟨E, hE⟩ := hg.exists_primeDivisor
    exact
      (exists_properCurve_and_curveForm_single_ne_zero_and_isQFactorial_of_isDivisorialContraction
        hQ hg hE fun L _ hL => hpb L inferInstance hL).2.2
  · exact isQFactorial_of_isFiberTypeContraction_of_forall_exists_iso_pullback hQ hg
      fun L _ hL => hpb L inferInstance hL

end

end MMP.Mori

end
