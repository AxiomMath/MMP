module

public import MMP.AlgebraicGeometry.Singularities.LocalGenerator

/-!
# The divisor of a rational pluricanonical form

On a normal variety `X` over a perfect field with canonical divisor `K_X`, the divisor of every
nonzero rational `m`-canonical form is linearly equivalent to `mK_X`.

## Main results

* `MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul`

## Implementation notes

The base field is assumed perfect, as for `MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq`
(KM work over an algebraically closed field).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity

open MMP.Mori

variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **The divisor of a rational form** (implicit in KM). Let `X` be a normal variety, `K_X` a
canonical divisor, `m ∈ ℤ` and `τ ≠ 0` a rational `m`-canonical form. Then `div(τ) ∼ mK_X`. -/
@[mmp "lem_km2a_divisor_of_rational_form"]
theorem linearlyEquivalent_divisorOfForm_zsmul (hX : IsNormalVariety k sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {m : ℤ} {τ : RationalPluriForms sX n m}
    (hτ : τ ≠ 0) :
    Divisor.LinearlyEquivalent (divisorOfForm τ) (m • K) := by
  have hn := hK.topologicalKrullDim_eq
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := exists_basis_topForms hX hn
  obtain ⟨ω, hω0, hω⟩ := IsCanonicalDivisor.exists_ordForm_eq hX hK
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  set e := (ZTensorPower.basis b m).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero (zpow_ne_zero m hc)))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 ω hω0
  have e2 := hN m τ hτ
  rw [← hc_def, hω Γ] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ,
    Scheme.ord_mul he (inv_ne_zero (zpow_ne_zero m hc)), ← zpow_neg_one,
    ord_zpow _ (zpow_ne_zero m hc), ord_zpow _ hc, coeff_divisorOfForm, e2]
  simp only [DivisorWithCoeffs.coeff_smul, smul_eq_mul]
  rw [e1]
  ring

end MMP.Positivity
