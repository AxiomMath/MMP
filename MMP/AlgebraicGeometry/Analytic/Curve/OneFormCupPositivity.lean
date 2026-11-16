module

public import MMP.AlgebraicGeometry.Analytic.Curve.OneFormCupPositivityChartCycle
public import MMP.AlgebraicGeometry.Analytic.Curve.FundamentalChartCycle

/-!
# Curve cup positivity, unconditionally

The curve cup positivity, proved under the hypothesis `HasFundamentalChartCycle X`, with that
hypothesis discharged by `MMP.Analytic.ChartConeCellulation.hasFundamentalChartCycle`: every
smooth projective curve over `ℂ` has fine fundamental chart cycles.

## Main results

* `MMP.Fourfold.Polarization.exists_pos_smul_cup_curve`: on a smooth projective curve, for a
  holomorphic one-form `ω ≠ 0` with de Rham class `α` and `L` ample, `i (α ∪ conj α)` is a positive
  multiple of `c₁(L)` in `H²(X^an; ℂ)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite MMP
open MMP.SingularChain MMP.SingularCochain
open MMP.Analytic

namespace MMP.Fourfold.Polarization

variable {n : ℕ} {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]
  [IsProjectiveVariety ℂ (X ↘ Spec (.of ℂ))] [SmoothOfRelativeDimension n (X ↘ Spec (.of ℂ))]

/-- **Positivity on a curve.** For a holomorphic one-form `ω ≠ 0` and `L` ample,
`i [ω] ∪ \overline{[ω]}` is a positive multiple of `c₁(L)` in `H²(X^an; ℂ)`. -/
theorem exists_pos_smul_cup_curve (h1 : n = 1)
    {ω : Γ((X ↘ Spec (.of ℂ)).relativeDifferentialForms ((1 : ℕ) : ℤ), ⊤)}
    {α : analyticSingularCohomology ℂ (X ↘ Spec (.of ℂ)) 1} (hω : ω ≠ 0) (hα : IsDR X ω α)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : MMP.Intersection.IsAmple ℂ L) :
    ∃ s : ℝ, 0 < s ∧
      Complex.I • cupNatUniv ℂ (Analytification.space (X ↘ Spec (.of ℂ))) 1 1 α (conjH X α) =
        (s : ℂ) •
          singularCohomology.mapCoeff (Int.castRingHom ℂ) 2 (algebraicFirstChernClass L) := by
  subst h1
  exact HasFundamentalChartCycle.exists_pos_smul_cup_curve
    MMP.Analytic.ChartConeCellulation.hasFundamentalChartCycle rfl hω hα L hL

end MMP.Fourfold.Polarization
