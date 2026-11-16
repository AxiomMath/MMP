/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.Attr
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoStepTower
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Birational
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# The blow-up of a variety is a projective birational variety over it

Let `X` be a variety over a field `k`, with structure morphism `f : X ⟶ Spec k`, and let
`0 ≠ I ⊆ 𝒪_X` be a quasi-coherent ideal sheaf. Since `X` is Noetherian, `I` is coherent. The
blow-up `π : B_I X ⟶ X` is then projective, hence proper ([Stacks, Tags 02NS and 01WC]); its
source is integral ([Stacks, Tag 02ND]) and `π` is birational ([Stacks, Tag 02OS]). Composing
with `f`, the structure morphism `π ≫ f` is separated and of finite type, so `B_I X` is a variety
over `k`.

## Main results

* `MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational`: `B_I X` is a
  variety over `k`, and `π` is projective and birational.

## Implementation notes

The ideal sheaf is a quasi-coherent `X.IdealSheafData`; its coherence (finite type) is not a
hypothesis, since on the locally Noetherian scheme `X` it is automatic
(`AlgebraicGeometry.TwoStepTower.isFiniteType_of_isLocallyNoetherian`). Nonzero is `I ≠ ⊥`.
The variety structure on `B_I X` is the composite `blowUpToBase I ≫ f`.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [KM98], §0.4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Flips.ResolutionInputs

/-- **The blow-up of a variety in a nonzero ideal sheaf.** Let `X` be a variety over `k` with
structure morphism `f` and `I ≠ 0` a (coherent) ideal sheaf on `X`. Then `B_I X`, with structure
morphism `blowUpToBase I ≫ f`, is a variety over `k`, and `π = blowUpToBase I` is projective and
birational. -/
@[mmp "lem_mmp_foundation_kr_blowup_variety_projective"]
theorem isVariety_blowUp_and_isProjective_and_isBirational {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [hX : IsVariety k f] (I : X.IdealSheafData)
    (hI : I ≠ ⊥) :
    IsVariety k (blowUpToBase I ≫ f) ∧ IsProjective (blowUpToBase I) ∧
      IsBirational (blowUpToBase I) := by
  have : IsIntegral X := hX.toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hft : I.IsFiniteType := TwoStepTower.isFiniteType_of_isLocallyNoetherian I
  have hproj : IsProjective (blowUpToBase I) := Stacks.Blowup.isProjective_blowUpToBase I hft
  have : IsProper (blowUpToBase I) := hproj.isProper
  have : IsIntegral (blowUp I) := isIntegral_blowUp I hI
  exact ⟨{ }, hproj, isBirational_blowUpToBase I hI⟩

end MMP.Flips.ResolutionInputs

end
