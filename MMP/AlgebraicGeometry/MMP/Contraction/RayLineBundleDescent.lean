module

public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent

section

/-!
# Line bundles on the contraction of a negative extremal ray

Let `X` be a projective variety over an algebraically closed field `k` of characteristic zero,
`(X, Δ)` a klt pair with `Δ` effective, `R` an extremal ray of the closed cone of curves `NE̅(X)`
on which `K_X + Δ` is negative away from `0`, `g : X ⟶ Z` a contraction of `R`, and `C ⊆ X` an
irreducible curve with `R = ℝ_{≥0}[C]`. An invertible sheaf `M` on `X` has `(M · C) = 0` if and
only if `M ≅ g^* L` for an invertible sheaf `L` on `Z`: this is exactness at `Pic X` of
`0 → Pic Z → Pic X → ℤ`, `M ↦ (M · C)`.

## Main results

* `MMP.Mori.degree_eq_zero_iff_exists_iso_pullback_of_isContractionOfFace`: the statement above.

## Implementation notes

An irreducible curve is a `MMP.Mori.ProperCurve`, its class is
`OneCycle.numericalClass sX (C.cycle ℝ)`, and `(M · C)` is `MMP.Mori.ProperCurve.degree`. A
contraction of `R` is `MMP.Mori.IsContractionOfFace` for the ray `R`. A line bundle is an
invertible sheaf of `𝒪`-modules and `g^*` is `AlgebraicGeometry.Scheme.Modules.pullback g`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Corollary 3.17
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **Exactness at `Pic X`** (Kollár–Mori 3.17). Let `X` be a projective variety over an
algebraically closed field `k` of characteristic zero, `(X, Δ)` a klt pair with canonical divisor
`K` and `Δ` effective, `R` an extremal ray of `NE̅(X)` with `(K + Δ) · u < 0` for `0 ≠ u ∈ R`,
`g : X ⟶ Z` a contraction of `R`, and `C ⊆ X` a curve with `R = ℝ_{≥0}[C]`. Then an invertible
sheaf `M` on `X` has `deg_C M = 0` if and only if `M ≅ g^* L` for an invertible sheaf `L` on
`Z`. -/
@[mmp "thm_km3b_pic_exact_sequence"]
public theorem degree_eq_zero_iff_exists_iso_pullback_of_isContractionOfFace {k : Type}
    [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)}
    [AlgebraicGeometry.IsProjectiveVariety k sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    (hneg : ∀ u ∈ R, u ≠ 0 →
      MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2 u < 0)
    {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of k)} {g : X ⟶ Z} (hg : IsContractionOfFace k sX sZ R g)
    (C : ProperCurve sX)
    (hC : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w})
    (M : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    C.degree k M = 0 ↔
      ∃ L : Z.Modules, SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L ∧
        Nonempty (M ≅ (Scheme.Modules.pullback g).obj L) := by
  have hdeg : ∀ (C' : ProperCurve sX) (N : X.Modules)
      [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N],
      (C'.degree k N : ℝ) =
        NumericalCurveClasses.degree sX N (OneCycle.numericalClass sX (C'.cycle ℝ)) := by
    intro C' N _
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  constructor
  · intro h0
    have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hklt.1.2.2) R :=
      ⟨hR.1, hR.1.2.2.1, hneg⟩
    refine exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hΔ hF hg M
      fun C' hC' => ?_
    rw [hC] at hC'
    obtain ⟨c, -, hc⟩ := hC'
    have h := hdeg C' M
    rw [← hc, map_smul, ← hdeg C M, h0, Int.cast_zero, smul_zero] at h
    exact_mod_cast h
  · rintro ⟨L, hL, ⟨e⟩⟩
    have hsZ := hg.isProjectiveVariety_target
    have hCR : C.IsContractedBy g :=
      (hg.isContractedBy_iff C).mpr (hC ▸ ⟨1, zero_le_one, one_smul _ _⟩)
    rw [show C.degree k M = C.degree k ((Scheme.Modules.pullback g).obj L) from
      degreeOn_eq_of_iso k sX C.ι C.dim_le e]
    exact C.degree_pullback_eq_zero_of_isContractedBy g hg.comp_eq hCR L

end MMP.Mori

end
