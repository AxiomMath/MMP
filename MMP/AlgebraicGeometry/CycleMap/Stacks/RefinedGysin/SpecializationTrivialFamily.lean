module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationFibre
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreLineAtInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreLineRegular

/-!
# The trivial family `𝐏¹_Z ⊆ M°` of Stacks' deformation to the normal cone

Let `X` be a scheme, `Z ⊆ X` cut out by `ℐ`, `b : W ⟶ 𝐏¹_X` the blowup at infinity and
`M° = W ∖ X'` (Stacks 0FBG). The closed immersion `𝐏¹_Z ⟶ W` of Stacks 0FBG (8)
(`Stacks.Chow.lineToBlowupAtInfinity`) misses the strict transform `X'`, so it factors through
the open `M°`: this is the *trivial family* `Z × 𝐏¹ ⊆ M°` of Fulton's proof of Theorem 19.2.
It is a closed immersion, regular of codimension `r` when `Z ⟶ X` is (Stacks 0FE9 restricted to
the open `M°`), and over `ℂ` its composite with the deformation map `ρ : M° ⟶ 𝐏¹_ℂ` is the
projection `𝐏¹_Z ⟶ 𝐏¹_ℂ`.

## Main definitions

* `MMP.Chow.lineToStrictTransformCompl`: `𝐏¹_Z ⟶ M°`.

## Main results

* `MMP.Chow.isClosedImmersion_lineToStrictTransformCompl`.
* `MMP.Chow.isRegularClosedImmersionOfCodim_lineToStrictTransformCompl`.
* `MMP.Chow.lineToStrictTransformCompl_comp_strictTransformComplToLine`: `ρ ∘ (𝐏¹_Z ⊆ M°)` is
  the projection `𝐏¹_Z ⟶ 𝐏¹_ℂ`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FE9](https://stacks.math.columbia.edu/tag/0FE9)
* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace MMP.Chow

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-- The closed immersion `𝐏¹_Z ⟶ W` lands in `M° = W ∖ X'`. -/
theorem range_lineToBlowupAtInfinity_subset :
    Set.range (lineToBlowupAtInfinity ℐ) ⊆
      (strictTransformComplAtInfinity ℐ : Set (blowupAtInfinity ℐ)) := by
  rintro _ ⟨w, rfl⟩
  exact lineToBlowupAtInfinity_notMem_support_strictTransformIdealAtInfinity ℐ w

/-- **The trivial family `𝐏¹_Z ⟶ M°`**: the closed immersion `𝐏¹_Z ⟶ W` of Stacks 0FBG (8),
as a morphism into the open `M° = W ∖ X'`. -/
def lineToStrictTransformCompl :
    relativeProjectiveLine ℐ.subscheme ⟶ (strictTransformComplAtInfinity ℐ).toScheme :=
  IsOpenImmersion.lift (strictTransformComplAtInfinity ℐ).ι (lineToBlowupAtInfinity ℐ) (by
    rw [Scheme.Opens.range_ι]
    exact range_lineToBlowupAtInfinity_subset ℐ)

/-- The composite of `𝐏¹_Z ⟶ M°` with the open immersion `M° ⊆ W` is `𝐏¹_Z ⟶ W`. -/
@[reassoc (attr := simp)]
theorem lineToStrictTransformCompl_ι :
    lineToStrictTransformCompl ℐ ≫ (strictTransformComplAtInfinity ℐ).ι =
      lineToBlowupAtInfinity ℐ :=
  IsOpenImmersion.lift_fac _ _ _

/-- `𝐏¹_Z ⟶ M°` is the base change of `𝐏¹_Z ⟶ W` along the open immersion `M° ⊆ W`. -/
theorem isPullback_lineToStrictTransformCompl :
    IsPullback (𝟙 _) (lineToStrictTransformCompl ℐ) (lineToBlowupAtInfinity ℐ)
      (strictTransformComplAtInfinity ℐ).ι :=
  (IsPullback.of_vert_isIso_mono ⟨by simp⟩).flip

/-- **`𝐏¹_Z ⟶ M°` is a closed immersion.** -/
instance isClosedImmersion_lineToStrictTransformCompl :
    IsClosedImmersion (lineToStrictTransformCompl ℐ) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (isPullback_lineToStrictTransformCompl ℐ) inferInstance

/-- **`𝐏¹_Z ⟶ M°` is regular of codimension `r` when `Z ⟶ X` is** (Stacks 0FE9, restricted to
the open `M°`). -/
theorem isRegularClosedImmersionOfCodim_lineToStrictTransformCompl {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] {r : ℕ} (hreg : IsRegularClosedImmersionOfCodim i r) :
    IsRegularClosedImmersionOfCodim (lineToStrictTransformCompl i.ker) r :=
  IsRegularClosedImmersionOfCodim.of_isPullback (isPullback_lineToStrictTransformCompl i.ker)
    (isRegularClosedImmersionOfCodim_lineToBlowupAtInfinity i hreg)

end MMP.Chow

namespace MMP.Chow

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] (ℐ : X.IdealSheafData)

/-- **`ρ ∘ (𝐏¹_Z ⊆ M°)` is the projection `𝐏¹_Z ⟶ 𝐏¹_ℂ`**: the trivial family lies over `𝐏¹_ℂ`
through its second factor. -/
theorem lineToStrictTransformCompl_comp_strictTransformComplToLine :
    lineToStrictTransformCompl ℐ ≫ strictTransformComplToLine ℐ =
      projectiveLineBaseChange (ℐ.subschemeι ≫ X ↘ Spec (.of ℂ)) := by
  rw [strictTransformComplToLine, lineToStrictTransformCompl_ι_assoc, ← Category.assoc,
    lineToBlowupAtInfinity_comp, projectiveLineBaseChange_comp]

end MMP.Chow
