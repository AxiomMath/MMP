module
public import MMP.AlgebraicGeometry.Analytic.ComplexRealization
public import MMP.AlgebraicGeometry.Divisor.Canonical.PluricanonicalForms

/-!
# The density of a rational pluriform on a chart

Let `X` be a smooth complex variety of dimension `n`, `m > 0`, and `s` a rational section of
`ω_X^{⊗m}`, i.e. an element of `ω^{⊗m}_{ℂ(X)} = (Ω^n_{ℂ(X)/ℂ})^{⊗m}`. Let `z_1, …, z_n` be étale
coordinates on a Zariski open `U`, and `W ⊆ U(ℂ)` an open subset of `X^an` on which
`z = (z_1, …, z_n)` is an open embedding into `ℂⁿ`. Write `s = φ · (dz_1 ∧ ⋯ ∧ dz_n)^{⊗m}` with
`φ ∈ ℂ(X)`. The *chart measure* of `s` on `W` is `|φ|^{2/m} dλ`, where `λ` is Lebesgue measure on
`ℂⁿ = ℝ^{2n}` transported to `W` by `z`, and the density `|φ|^{2/m}` is evaluated where `φ` is
regular.

## Main definitions

* `MMP.Analytic.ComplexPoints.pluriformCoeff`: the coefficient `φ ∈ ℂ(X)` of
  `s = φ · (dz_1 ∧ ⋯ ∧ dz_n)^{⊗m}`.
* `MMP.Analytic.ComplexPoints.pluriformDensity`: the density `y ↦ |φ(y)|^{2/m}` on `X^an`,
  evaluated where `φ` is regular.
* `MMP.Analytic.ComplexPoints.pluriformChartMeasure`: the measure `|φ|^{2/m} dλ` on `X^an`,
  supported on the chart `W`.

## Implementation notes

* The coefficient `φ` is the coordinate of `s` along the basis `(dz_1 ∧ ⋯ ∧ dz_n)^{⊗m}` of the
  line `ω^{⊗m}_{ℂ(X)}` (`MMP.Mori.ZTensorPower.basis`); for étale coordinates
  `dz_1 ∧ ⋯ ∧ dz_n` is nonzero and spans `Ω^n_{ℂ(X)/ℂ}`. Otherwise the coefficient is `0`.
* The value of `φ` at a point `y` is `g(y)` for any regular function `g` on an open `V ∋ y` with
  image `φ` in `ℂ(X)`; all such values agree, and the density is written as the supremum of
  `|g(y)|^{2/m}` over them. Where `φ` is not regular the supremum is empty and the density is
  `0`; this locus is a proper Zariski closed subset, hence Lebesgue-null.
* Lebesgue measure on `ℂⁿ` is `MeasureTheory.volume` on `Fin n → ℂ`, the product of Lebesgue
  measure on `ℂ = ℝ²`. It is pulled back to `W` along the open embedding `z` and pushed forward
  to `X^an` by the inclusion, so the chart measure is a measure on `X^an` vanishing off `W`.
* The measurable structure on `X^an` is a parameter; the intended one is the Borel structure of
  the analytic topology.

## References

* [Kollár–Mori, *Birational geometry of algebraic varieties*]
-/

open CategoryTheory AlgebraicGeometry Topology MeasureTheory

namespace MMP.Analytic.ComplexPoints

@[expose] public section

/-- The coefficient `φ ∈ ℂ(X)` of a rational `m`-canonical form `s` along the basis
`(dz_1 ∧ ⋯ ∧ dz_n)^{⊗m}` of `ω^{⊗m}_{ℂ(X)}`, i.e. `s = φ · (dz_1 ∧ ⋯ ∧ dz_n)^{⊗m}`. It is `0`
when `dz_1 ∧ ⋯ ∧ dz_n` does not span `Ω^n_{ℂ(X)/ℂ}` (which does not happen for étale
coordinates). -/
public noncomputable def pluriformCoeff {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X]
    {n m : ℕ}
    (s : MMP.Mori.RationalPluriForms sX n m) (U : X.Opens) [Nonempty U]
    (z : Fin n → Γ(X, U)) : X.functionField :=
  letI := MMP.Mori.functionFieldAlgebra sX
  -- `dz_1 ∧ ⋯ ∧ dz_n` in `Ω^n_{ℂ(X)/ℂ}`
  let dz : ⋀[X.functionField]^n Ω[X.functionField⁄ℂ] :=
    exteriorPower.ιMulti X.functionField n
      (fun i ↦ KaehlerDifferential.D ℂ X.functionField (X.germToFunctionField U (z i)))
  by
    classical
    exact if h : Submodule.span X.functionField {dz} = ⊤ ∧ dz ≠ 0 then
      (MMP.Mori.ZTensorPower.basis (MMP.Mori.basisOfSpanSingleton h.1 h.2) (m : ℤ)).repr
        (show MMP.Mori.ZTensorPower X.functionField _ (m : ℤ) from s) ()
    else 0

/-- The density `y ↦ |φ(y)|^{2/m}` on `X^an` of a rational function `φ ∈ ℂ(X)`: the supremum of
`|g(y)|^{2/m}` over regular functions `g` on opens `V ∋ y` whose image in `ℂ(X)` is `φ`. All
these values agree, and the supremum is `0` where `φ` is not regular. -/
public noncomputable def pluriformDensity {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsIntegral X]
    (m : ℕ)
    (φ : X.functionField) : ComplexPoints sX → ENNReal := fun y ↦
  ⨆ (V : X.Opens) (g : Γ(X, V)) (hy : y ∈ chart V) (hg : genericPoint X ∈ V)
    (_ : X.presheaf.germ V (genericPoint X) hg g = φ),
    ENNReal.ofReal (‖eval V g ⟨y, hy⟩‖ ^ (2 / m : ℝ))

/-- **The chart measure of a rational pluriform.** Let `X` be a smooth complex variety of
dimension `n`, `m > 0`, `s` a rational section of `ω_X^{⊗m}`, `z` étale coordinates on `U`, and
`W ⊆ U(ℂ)` an open subset of `X^an` on which `z` is an open embedding into `ℂⁿ`. Writing
`s = φ · (dz_1 ∧ ⋯ ∧ dz_n)^{⊗m}` with `φ ∈ ℂ(X)`, this is the measure `|φ|^{2/m} dλ` on `W`,
with `λ` Lebesgue measure on `ℂⁿ = ℝ^{2n}` transported by `z`, and the density taken where `φ`
is regular; it vanishes off `W`. -/
@[mmp "def_mmp_analytic_pluriform_density"]
public noncomputable def pluriformChartMeasure {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) {n : ℕ}
    [AlgebraicGeometry.IsVariety ℂ sX] [SmoothOfRelativeDimension n sX]
    [MeasurableSpace (ComplexPoints sX)] {m : ℕ} (_hm : 0 < m)
    (s : MMP.Mori.RationalPluriForms sX n m) (U : X.Opens) [Nonempty U]
    (z : Fin n → Γ(X, U))
    (_hz : Etale (AffineSpace.homOfVector (U.ι ≫ sX)
      (fun i : ULift.{0} (Fin n) ↦ U.topIso.inv (z i.down))))
    (W : Set (ComplexPoints sX)) (hW : W ⊆ chart U) (_hWo : IsOpen W)
    (_hWz : IsOpenEmbedding (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)) :
    Measure (ComplexPoints sX) :=
  ((Measure.comap (fun y : W ↦ fun i ↦ eval U (z i) ⟨y.1, hW y.2⟩)
      (volume : Measure (Fin n → ℂ))).map Subtype.val).withDensity
    (pluriformDensity sX m (pluriformCoeff sX s U z))

end

end MMP.Analytic.ComplexPoints
