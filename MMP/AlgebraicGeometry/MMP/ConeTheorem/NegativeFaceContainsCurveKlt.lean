module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.KltConeContraction

/-!
# Nonzero negative extremal faces contain the class of a curve, over `k`

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero
and `(X, Δ)` a klt pair with `Δ` effective. Every `(K_X + Δ)`-negative extremal face `F ≠ {0}`
of the closed cone of curves `NE̅(X)` contains the numerical class `[C]` of an irreducible curve
`C ⊆ X`. The proof here runs through the cone theorem: a nonzero `z ∈ F` is
`η + ∑ rⱼ [Cⱼ]` with `((K_X + Δ) · η) ≥ 0`, and extremality of `F` puts some `[Cⱼ]` in `F`.

## Main results

* `MMP.Mori.exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace'`: the statement
  above.

## Implementation notes

An irreducible curve `C ⊆ X` is a `MMP.Mori.ProperCurve` and its class `[C] ∈ N₁(X)` is
`OneCycle.numericalClass sX (C.cycle ℝ)`. The form `z ↦ ((K_X + Δ) · z)` is
`MMP.Fourfold.QDivisor.curveForm` of `K_X + Δ`. The statement coincides with
`MMP.Mori.exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace`, which is proved
through a supporting divisor instead of the cone theorem.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.3 Step 8,
  3.25
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- If `T ⊆ N` and `F` is an extremal face of the convex cone `N`, a point of the cone hull of
`T` lying in `F` lies in the cone hull of `T ∩ F`. -/
private theorem mem_hull_inter_of_isExtremalFace {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : PointedCone ℝ V} {F T : Set V} (hF : IsExtremalFace ℝ (N : Set V) F)
    (hT : T ⊆ N) {w : V} (hw : w ∈ PointedCone.hull ℝ T) (hwF : w ∈ F) :
    w ∈ PointedCone.hull ℝ (T ∩ F) := by
  have hTN : PointedCone.hull ℝ T ≤ N := Submodule.span_le.mpr hT
  induction hw using Submodule.span_induction with
  | mem t ht => exact PointedCone.subset_hull ⟨ht, hwF⟩
  | zero => exact zero_mem _
  | add u v hu hv ihu ihv =>
    obtain ⟨huF, hvF⟩ := hF.2.2.2 u (hTN hu) v (hTN hv) hwF
    exact add_mem (ihu huF) (ihv hvF)
  | smul c u hu ih =>
    rcases eq_or_lt_of_le c.2 with hc | hc
    · have : c = 0 := Subtype.ext hc.symm
      simp [this]
    · have huF : u ∈ F := by
        have := hF.2.1.2 _ hwF (c : ℝ)⁻¹ (inv_pos.mpr hc)
        rwa [Nonneg.mk_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at this
      exact Submodule.smul_mem _ c (ih huF)

/-- A nonzero point of an extremal face `F` of the convex cone `N`, lying in the cone hull of
some `T ⊆ N`, forces a point of `T` into `F`. -/
private theorem exists_mem_of_mem_hull_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    {N : PointedCone ℝ V} {F T : Set V} (hF : IsExtremalFace ℝ (N : Set V) F)
    (hT : T ⊆ N) {w : V} (hw : w ∈ PointedCone.hull ℝ T) (hwF : w ∈ F) (hw0 : w ≠ 0) :
    ∃ t ∈ T, t ∈ F := by
  by_contra h
  have hw' := mem_hull_inter_of_isExtremalFace hF hT hw hwF
  rw [(Set.eq_empty_of_forall_notMem fun t ht => h ⟨t, ht⟩ : T ∩ F = ∅), PointedCone.hull,
    Submodule.span_empty, Submodule.mem_bot] at hw'
  exact hw0 hw'

/-- **Nonzero negative extremal faces contain curve classes** (Kollár–Mori 3.3, Step 8, over
`k`). Let `X` be a projective variety over an algebraically closed field `k` of characteristic
zero, `(X, Δ)` a klt pair with canonical divisor `K` and `Δ` effective, and `F ≠ {0}` a
`(K + Δ)`-negative extremal face of `NE̅(X)`. Then `F` contains the class `[C]` of some
irreducible curve `C ⊆ X`. -/
@[mmp "lem_km3c_negative_face_contains_curve_over_k"]
public theorem exists_properCurve_numericalClass_mem_of_isNegativeExtremalFace' {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {F : Set (NumericalCurveClasses sX)}
    (hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) F)
    (hF0 : F ≠ {0}) :
    ∃ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ F := by
  obtain ⟨⟨S, -, -, hcone⟩, -, -⟩ := cone_and_contraction_and_descent_of_isKltPair hklt hΔ
  obtain ⟨z, hzF, hz0⟩ : ∃ z ∈ F, z ≠ 0 := by
    by_contra h
    push Not at h
    exact hF0 (Set.eq_singleton_iff_unique_mem.mpr ⟨hF.1.2.1.1, h⟩)
  have hzN := hF.1.1 hzF
  rw [hcone] at hzN
  obtain ⟨η, ⟨hηN, hηK⟩, w, hw, rfl⟩ := hzN
  have hT : (fun C : ProperCurve sX => OneCycle.numericalClass sX (C.cycle ℝ)) '' S ⊆
      (closedConeOfCurves sX : Set _) := by
    rintro _ ⟨C, -, rfl⟩
    exact coneOfCurves_le_closedConeOfCurves sX (numericalClass_cycle_mem_coneOfCurves sX C)
  have hwN : w ∈ closedConeOfCurves sX := (Submodule.span_le.mpr hT : PointedCone.hull ℝ _ ≤ _) hw
  obtain ⟨_, ⟨C, -, rfl⟩, hC⟩ := exists_mem_of_mem_hull_of_ne_zero hF.1 hT hw
    (hF.1.2.2.2 η hηN w hwN hzF).2 <| by
      rintro rfl
      simp only [add_zero] at hzF hz0
      exact not_lt.mpr hηK (hF.2.2 η hzF hz0)
  exact ⟨C, hC⟩

end MMP.Mori

end
