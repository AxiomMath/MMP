module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The blow-up of a closed point is an isomorphism off the exceptional curve (Kollár 1.36)

Let `S` be a Noetherian scheme and `0 ∈ S` a closed point, with blow-up `π : B₀S → S`
(`AlgebraicGeometry.blowUp` of the ideal of the reduced point, structure morphism
`AlgebraicGeometry.blowUpToBase`) and exceptional curve `E = π⁻¹(0)`
(`AlgebraicGeometry.exceptionalIdeal`). Then `π` restricts to an isomorphism
`B₀S ∖ E → S ∖ {0}`.

That a blow-up is an isomorphism off its centre (Kollár 3.7) and that the blow-up of an
effective Cartier divisor is an isomorphism (Kollár 2.3) are StacksDraft's
`AlgebraicGeometry.isIso_blowUp_restrict_compl_support` and
`Stacks.Blowup.isIso_blowUpToBase_of_isEffectiveCartierDivisor`, recorded as library coverage.

## Main statements

* `MMP.Resolution.Kollar.preimage_compl_eq_compl_support_exceptionalIdeal`: `π⁻¹(S ∖ {0})` is the
  complement `B₀S ∖ E` of the exceptional curve.
* `MMP.Resolution.Kollar.isIso_blowUpToBase_restrict_compl_point`: `π` restricts to an
  isomorphism `π⁻¹(S ∖ {0}) = B₀S ∖ E → S ∖ {0}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace MMP.Resolution.Kollar

variable {S : Scheme.{u}} {o : S} (ho : IsClosed ({o} : Set S))

/-- The ideal sheaf of the reduced closed point `0 ∈ S`, the centre of the blow-up `B₀S`. -/
noncomputable abbrev pointIdeal : S.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨{o}, ho⟩

/-- The open complement `S ∖ {0}` of a closed point. -/
def complPoint : S.Opens := ⟨({o} : Set S)ᶜ, ho.isOpen_compl⟩

/-- **Kollár 1.36.** The preimage of `S ∖ {0}` under the blow-up `π : B₀S → S` of a closed point
is the complement `B₀S ∖ E` of the exceptional curve `E = π⁻¹(0)`. -/
@[mmp "lem_kr1b_blowup_iso_off_exceptional"]
theorem preimage_compl_eq_compl_support_exceptionalIdeal :
    ((blowUpToBase (pointIdeal ho) ⁻¹ᵁ complPoint ho : (blowUp (pointIdeal ho)).Opens) :
        Set (blowUp (pointIdeal ho))) =
      ((exceptionalIdeal (pointIdeal ho)).support : Set (blowUp (pointIdeal ho)))ᶜ := by
  simp [exceptionalIdeal, complPoint, pointIdeal, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- **Kollár 1.36**, "`π : B₀S ∖ E ≅ S ∖ {0}`". The blow-up `π : B₀S → S` of a closed point
restricts to an isomorphism `π⁻¹(S ∖ {0}) → S ∖ {0}`, and `π⁻¹(S ∖ {0}) = B₀S ∖ E` by
`preimage_compl_eq_compl_support_exceptionalIdeal`. -/
@[mmp "lem_kr1b_blowup_iso_off_exceptional"]
theorem isIso_blowUpToBase_restrict_compl_point :
    IsIso (blowUpToBase (pointIdeal ho) ∣_ complPoint ho) := by
  have h : complPoint ho = ⟨((pointIdeal ho).support : Set S)ᶜ,
      (pointIdeal ho).support.isClosed.isOpen_compl⟩ := by
    ext1
    simp [complPoint, pointIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rw [h]
  exact isIso_blowUp_restrict_compl_support _

end MMP.Resolution.Kollar
