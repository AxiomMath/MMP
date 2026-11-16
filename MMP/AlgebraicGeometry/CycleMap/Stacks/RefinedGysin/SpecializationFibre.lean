module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationSpace
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreResidualGysin
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreBaseChange
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism

/-!
# The deformation `M° ⟶ 𝐏¹_ℂ` and its fibre at infinity

Let `X` be a scheme over `ℂ` and `Z ⊆ X` the closed subscheme of a quasi-coherent ideal sheaf `ℐ`,
with Stacks' deformation space `b : W ⟶ 𝐏¹_X` (Stacks 0FBG) and its open part `M° = W ∖ X'`
(`MMP.Chow.isComplexScheme_strictTransformComplAtInfinity`). The *deformation map*
`ρ : M° ⟶ 𝐏¹_ℂ` is `M° ⊆ W ⟶ 𝐏¹_X ⟶ 𝐏¹_ℂ`, a morphism over `ℂ`. Its fibre at infinity is the
normal cone: the inverse image of the divisor at infinity of `𝐏¹_ℂ` along `ρ` is the fibre at
infinity `W_∞ ∩ M°`, which for `Z ⊆ X` cut out by a closed immersion `i` is `C_ZX` (Stacks 0FBH,
`Stacks.Chow.normalConeIsoFibreAtInfinityCompl`).

## Main definitions

* `MMP.Chow.strictTransformComplToLine`: `ρ : M° ⟶ 𝐏¹_ℂ`.
* `MMP.Chow.normalConeIsoLineInfinityFibre`: `C_ZX ≅ ρ⁻¹(∞)`, as closed subschemes of `M°`.

## Main results

* `MMP.Chow.isOver_strictTransformComplToLine`: `ρ` is a morphism over `ℂ`.
* `MMP.Chow.comap_lineInfinityDivisor_strictTransformComplToLine`: `ρ⁻¹(∞) = W_∞ ∩ M°`.
* `MMP.Chow.isEffectiveCartierDivisor_lineInfinityFibre`: `ρ⁻¹(∞)` is an effective Cartier
  divisor on `M°` (it is the exceptional divisor `E ∩ M°`).
* `MMP.Chow.normalConeIsoLineInfinityFibre_hom_subschemeι`: `C_ZX ≅ ρ⁻¹(∞) ⊆ M°` is the
  closed immersion `C_ZX ⟶ M°` of Stacks 0FBH.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [W. Fulton, *Intersection Theory*][fulton1998], §5.1 and §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

namespace MMP.Chow

attribute [local instance] blowupAtInfinityOver strictTransformComplAtInfinityOver

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (ℐ : X.IdealSheafData)

/-- **The deformation map `ρ : M° ⟶ 𝐏¹_ℂ`**: `M° = W ∖ X' ⊆ W ⟶ 𝐏¹_X ⟶ 𝐏¹_ℂ`. -/
def strictTransformComplToLine :
    (strictTransformComplAtInfinity ℐ).toScheme ⟶ relativeProjectiveLine (Spec (.of ℂ)) :=
  (strictTransformComplAtInfinity ℐ).ι ≫ blowupAtInfinityToLine ℐ ≫
    projectiveLineBaseChange (X ↘ Spec (.of ℂ))

/-- **`ρ : M° ⟶ 𝐏¹_ℂ` is a morphism over `ℂ`.** -/
theorem isOver_strictTransformComplToLine :
    (strictTransformComplToLine ℐ).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change ((strictTransformComplAtInfinity ℐ).ι ≫ blowupAtInfinityToLine ℐ ≫
        projectiveLineBaseChange (X ↘ Spec (.of ℂ))) ≫
          relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ) =
      (strictTransformComplAtInfinity ℐ).ι ≫
        (blowupAtInfinityToLine ℐ ≫ relativeProjectiveLine X ↘ X) ≫ X ↘ Spec (.of ℂ)
    simp only [Category.assoc, projectiveLineBaseChange_over]⟩

/-- **The fibre of `ρ` at infinity is `W_∞ ∩ M°`**: the inverse image along `ρ : M° ⟶ 𝐏¹_ℂ` of
the divisor at infinity of `𝐏¹_ℂ` is the inverse image along `M° ⊆ W` of the fibre at infinity
`W_∞ = b⁻¹((𝐏¹_X)_∞)`. -/
theorem comap_lineInfinityDivisor_strictTransformComplToLine :
    (lineInfinityDivisor (Spec (.of ℂ))).comap (strictTransformComplToLine ℐ) =
      (fibreIdealAtInfinity ℐ).comap (strictTransformComplAtInfinity ℐ).ι := by
  rw [strictTransformComplToLine, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_comp, comap_lineInfinityDivisor_projectiveLineBaseChange]
  rfl

/-- **`ρ⁻¹(∞)` is an effective Cartier divisor on `M°`**: on `M° = W ∖ X'` the fibre at infinity
`W_∞ = E + X'` is the exceptional divisor `E` (Stacks 0FBG (4)). -/
theorem isEffectiveCartierDivisor_lineInfinityFibre :
    Stacks.Divisors.IsEffectiveCartierDivisor
      ((lineInfinityDivisor (Spec (.of ℂ))).comap (strictTransformComplToLine ℐ)) := by
  rw [comap_lineInfinityDivisor_strictTransformComplToLine, comap_fibreIdealAtInfinity_ι_compl]
  exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
    (isEffectiveCartierDivisor_exceptionalIdealAtInfinity ℐ) _

variable {Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **`C_ZX ≅ ρ⁻¹(∞)`** (Stacks 0FBH): the normal cone of a closed immersion `i : Z ⟶ X` is the
fibre at infinity of the deformation map `ρ : M° ⟶ 𝐏¹_ℂ`, as closed subschemes of `M°`. -/
def normalConeIsoLineInfinityFibre :
    Stacks.Conormal.normalCone i ≅
      ((lineInfinityDivisor (Spec (.of ℂ))).comap (strictTransformComplToLine i.ker)).subscheme :=
  normalConeIsoFibreAtInfinityCompl i ≪≫ eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (comap_lineInfinityDivisor_strictTransformComplToLine i.ker).symm)

/-- The identification `C_ZX ≅ ρ⁻¹(∞)` followed by the inclusion `ρ⁻¹(∞) ⊆ M°` is the closed
immersion `C_ZX ⟶ M°` of Stacks 0FBH. -/
@[reassoc (attr := simp)]
theorem normalConeIsoLineInfinityFibre_hom_subschemeι :
    (normalConeIsoLineInfinityFibre i).hom ≫
        ((lineInfinityDivisor (Spec (.of ℂ))).comap
          (strictTransformComplToLine i.ker)).subschemeι =
      normalConeToStrictTransformComplAtInfinity i := by
  rw [normalConeIsoLineInfinityFibre, Iso.trans_hom, eqToIso.hom, Category.assoc,
    subschemeι_eqToHom (comap_lineInfinityDivisor_strictTransformComplToLine i.ker).symm,
    normalConeIsoFibreAtInfinityCompl_hom_subschemeι]

end MMP.Chow
