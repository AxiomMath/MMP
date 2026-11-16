module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting
public import MMP.AlgebraicGeometry.Singularities.KltRationalSingularities

/-!
# Vanishing of higher direct images for the resolution of a local setting

In a local setting `(Y, Θ, T, π)`, the pair `(Y, 0)` is klt and `π` is a projective resolution,
so `Y` has rational singularities: `𝒪_Y ⟶ π_* 𝒪_Ỹ` is an isomorphism and the higher direct
images `R^i π_* 𝒪_Ỹ` vanish for `i > 0`.

## Main results

* `MMP.Fourfold.IsLocalSetting.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived`
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

variable {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
  {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}

/-- In a local setting `(Y, Θ, T, π)`, the canonical map `𝒪_Y ⟶ π_* 𝒪_Ỹ` is an isomorphism and
the higher direct images `R^i π_* 𝒪_Ỹ` vanish for `i > 0`; that is, `𝒪_Y ⟶ Rπ_* 𝒪_Ỹ` is an
isomorphism. -/
@[mmp "lem_mmp_terminal_fourfold_resolution_vanishing"]
public theorem IsLocalSetting.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived
    (h : IsLocalSetting sY Θ T π) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom) ∧
      ∀ i : ℕ, 0 < i → IsZero (((Scheme.Modules.pushforward π).rightDerived i).obj
        (SheafOfModules.unit Yt.ringCatSheaf)) :=
  IsKltPair.isIso_unitToPushforwardObjUnit_and_isZero_rightDerived
    h.isProjectiveVariety h.isKltTerminalPair.1 h.isResolution

end MMP.Fourfold
