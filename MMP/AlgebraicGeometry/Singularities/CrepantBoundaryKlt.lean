module

public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical

/-!
# Coefficients of the crepant boundary of a klt pair

Let `(X, Δ)` be a klt pair and `f : Y → X` a birational morphism from a normal variety.
Every coefficient of the crepant boundary `Δ_Y` of `(X, Δ)` on `Y` is `< 1`
(used in KM 3.2 Step 1 and 3.5 Steps 0, 3).

## Main results

* `MMP.Positivity.IsKltPair.coeff_lt_one_of_isCrepantBoundary`

## Implementation notes

The base field is assumed perfect, so that a non-exceptional divisor over `X` is a prime divisor
of `X` with the same discrepancy (KM work over an algebraically closed field). No properness of
`f` is needed.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **The crepant boundary of a klt pair has coefficients `< 1`** (used in KM 3.2, 3.5). Let
`(X, Δ)` be a klt pair, `f : Y → X` a birational morphism from a normal variety and `Δ_Y`
the crepant boundary of `(X, Δ)` on `Y`. Then every coefficient of `Δ_Y` is `< 1`. -/
@[mmp "lem_km3a_klt_crepant_boundary_coefficients"]
theorem IsKltPair.coeff_lt_one_of_isCrepantBoundary {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    (hklt : IsKltPair sX n K Δ) {Y : Scheme.{u}} {f : Y ⟶ X}
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {ΔY : QDivisor Y}
    (hΔY : IsCrepantBoundary sX n K Δ f hY hf ΔY) (F : Mori.PrimeDivisor Y) :
    ΔY.coeff F < 1 := by
  have ha := hΔY F
  have hco : ∀ P : Mori.PrimeDivisor X, Δ.coeff P < 1 := roundDown_nonpos_iff.mp hklt.2.2
  suffices h : (-1 : ℚ) < -ΔY.coeff F by linarith
  set D : DivisorOver k sX := ⟨Y, f, hY, hf, F⟩
  by_cases hE : D.IsExceptional
  · have h1 := discrep_le hE ha
    have h2 := lt_of_lt_of_le hklt.2.1 h1
    have h3 : ((-1 : ℝ) : EReal) < (((-ΔY.coeff F : ℚ) : ℝ) : EReal) := by simpa using h2
    exact_mod_cast EReal.coe_lt_coe_iff.mp h3
  · obtain ⟨P, hv⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hklt.1.1 D hE
    obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hmτ⟩ := ha
    have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
    rw [MMP.Threefold.Mori.ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
      DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
    have hx : D.f D.E.genericPoint = P.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
    have hPU : (P.support ∩ (U : Set X)).Nonempty := by
      refine ⟨P.genericPoint, ?_, hx ▸ hU⟩
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
    have e := hτ.2 P hPU
    have hm0 : (m : ℚ) ≠ 0 := by positivity
    have : -ΔY.coeff F = -Δ.coeff P := by
      apply mul_left_cancel₀ hm0
      linear_combination hmτ + e
    rw [this]
    linarith [hco P]

end MMP.Positivity
