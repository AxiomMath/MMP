module

public import MMP.AlgebraicGeometry.Analytic.ComplexPoints.OpenSubscheme
public import MMP.AlgebraicGeometry.Variety.SmoothEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ProjectiveLine

/-!
# Stacks' deformation to the normal cone is a complex scheme

Let `X` be a complex scheme and `Z ⊆ X` the closed subscheme cut out by a quasi-coherent ideal
sheaf `ℐ`. Stacks' deformation to the normal cone (Tag 0FBG) is the blowup
`b : W ⟶ 𝐏¹_X` of `𝐏¹_X` in the centre `∞(Z)` (`Stacks.Chow.blowupAtInfinity`), and the open
complement `M° = W ∖ X'` of the strict transform `X'` of `X × ∞`
(`Stacks.Chow.strictTransformComplAtInfinity`). This file puts `𝐏¹_X`, `W` and `M°` over `ℂ`
through their projections to `X`, and proves that they are complex schemes: each is projective
over a complex scheme, or open in one.

## Main definitions

* `MMP.Chow.relativeProjectiveLineOver`, `MMP.Chow.blowupAtInfinityOver`,
  `MMP.Chow.strictTransformComplAtInfinityOver`: `𝐏¹_X`, `W` and `M°` over `ℂ` through `X`.

## Main results

* `MMP.Chow.isComplexScheme_of_isProjective_hom`: a scheme projective over a complex scheme is
  a complex scheme.
* `MMP.Chow.isProjective_relativeProjectiveLine_over`: `𝐏¹_X ⟶ X` is projective for `X` over a
  field.
* `MMP.Chow.isComplexScheme_relativeProjectiveLine`,
  `MMP.Chow.isComplexScheme_blowupAtInfinity`,
  `MMP.Chow.isComplexScheme_strictTransformComplAtInfinity`.

## Implementation notes

The structures over `ℂ` are definitions, used as local instances: a global instance
`(relativeProjectiveLine X).Over (Spec ℂ)` would clash, for `X = Spec ℂ`, with the structure
morphism of `𝐏¹_ℂ`.

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [W. Fulton, *Intersection Theory*][fulton1998], §19.1 and §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

namespace MMP.Chow

/-- **A scheme projective over a complex scheme is a complex scheme.** If `f : X ⟶ Y` is a
projective morphism over `ℂ` and `Y` is a complex scheme, then `X` admits a closed immersion over
`ℂ` into a smooth variety: a projective bundle over a smooth variety containing `Y`. -/
theorem isComplexScheme_of_isProjective_hom {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [IsComplexScheme Y] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]
    (hf : IsProjective f) : IsComplexScheme X := by
  obtain ⟨M, _, hM, i, hi, _⟩ := IsComplexScheme.exists_isClosedImmersion (X := Y)
  obtain ⟨N, t, j, hN, hj, hjt⟩ :=
    exists_isClosedImmersion_isSmoothVariety_of_isProjective (M ↘ Spec (.of ℂ)) i f hf
  have hover : j ≫ t = X ↘ Spec (.of ℂ) := by
    rw [hjt, comp_over i, comp_over f]
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) :=
    hover ▸ (inferInstance : LocallyOfFiniteType (j ≫ t))
  have : QuasiCompact (X ↘ Spec (.of ℂ)) := hover ▸ (inferInstance : QuasiCompact (j ≫ t))
  let : N.Over (Spec (.of ℂ)) := ⟨t⟩
  exact { exists_isClosedImmersion := ⟨N, inferInstance, hN, j, ⟨hover⟩, hj⟩ }

/-- **`𝐏¹_X ⟶ X` is projective** for a scheme `X` over a field `K`: it is the base change along
`X ⟶ Spec K` of the projective morphism `𝐏¹_K ⟶ Spec K` (Stacks 02V6). -/
theorem isProjective_relativeProjectiveLine_over (K : Type) [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (.of K)) : IsProjective (relativeProjectiveLine X ↘ X) := by
  have h := isPullback_projectiveLineBaseChange f
  have hP := IsProjective.pullback_fst f
    (Stacks.WeilCohomology.isProjectiveMorphism_relativeProjectiveLine_spec K).isProjective
  rw [← h.isoPullback_hom_fst]
  exact hP.comp_iso _

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))]

/-- `𝐏¹_X` over `ℂ`, through its projection to `X`. -/
abbrev relativeProjectiveLineOver : (relativeProjectiveLine X).Over (Spec (.of ℂ)) :=
  ⟨relativeProjectiveLine X ↘ X ≫ X ↘ Spec (.of ℂ)⟩

attribute [local instance] relativeProjectiveLineOver

/-- The projection `𝐏¹_X ⟶ X` is a morphism over `ℂ`. -/
theorem isOver_relativeProjectiveLine_over :
    (relativeProjectiveLine X ↘ X).IsOver (Spec (.of ℂ)) :=
  ⟨rfl⟩

/-- **`𝐏¹_X` is a complex scheme** for a complex scheme `X`. -/
theorem isComplexScheme_relativeProjectiveLine [IsComplexScheme X] :
    IsComplexScheme (relativeProjectiveLine X) :=
  haveI := isOver_relativeProjectiveLine_over (X := X)
  isComplexScheme_of_isProjective_hom (relativeProjectiveLine X ↘ X)
    (isProjective_relativeProjectiveLine_over ℂ (X ↘ Spec (.of ℂ)))

variable (ℐ : X.IdealSheafData)

/-- Stacks' deformation space `W = Bl_{∞(Z)} 𝐏¹_X` over `ℂ`, through its projection to `X`. -/
abbrev blowupAtInfinityOver : (blowupAtInfinity ℐ).Over (Spec (.of ℂ)) :=
  ⟨blowupAtInfinityToBase ℐ ≫ X ↘ Spec (.of ℂ)⟩

attribute [local instance] blowupAtInfinityOver

/-- The blowup morphism `b : W ⟶ 𝐏¹_X` is a morphism over `ℂ`. -/
theorem isOver_blowupAtInfinityToLine : (blowupAtInfinityToLine ℐ).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change blowupAtInfinityToLine ℐ ≫ relativeProjectiveLine X ↘ X ≫ X ↘ Spec (.of ℂ) =
      (blowupAtInfinityToLine ℐ ≫ relativeProjectiveLine X ↘ X) ≫ X ↘ Spec (.of ℂ)
    rw [Category.assoc]⟩

/-- The projection `W ⟶ X` is a morphism over `ℂ`. -/
theorem isOver_blowupAtInfinityToBase : (blowupAtInfinityToBase ℐ).IsOver (Spec (.of ℂ)) :=
  ⟨rfl⟩

/-- **Stacks' deformation space `W = Bl_{∞(Z)} 𝐏¹_X` is a complex scheme** for a closed
subscheme `Z` of a complex scheme `X`: the blowup is projective over the complex scheme `𝐏¹_X`
(Stacks 02NS, the centre being of finite type as `𝐏¹_X` is Noetherian). -/
theorem isComplexScheme_blowupAtInfinity [IsComplexScheme X] :
    IsComplexScheme (blowupAtInfinity ℐ) := by
  have := isComplexScheme_relativeProjectiveLine (X := X)
  have := isOver_blowupAtInfinityToLine ℐ
  have : IsNoetherian (Spec (CommRingCat.of ℂ)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing ℂ))
  have : IsLocallyNoetherian (relativeProjectiveLine X) :=
    LocallyOfFiniteType.isLocallyNoetherian (relativeProjectiveLine X ↘ Spec (.of ℂ))
  have hI : (infinityCentreIdeal ℐ).IsFiniteType := fun U =>
    haveI := IsLocallyNoetherian.component_noetherian U
    IsNoetherian.noetherian ((infinityCentreIdeal ℐ).ideal U)
  exact isComplexScheme_of_isProjective_hom (blowupAtInfinityToLine ℐ)
    (Stacks.Blowup.isProjective_blowUpToBase _ hI)

/-- Stacks' open deformation space `M° = W ∖ X'` over `ℂ`, through `M° ⊆ W ⟶ X`. -/
abbrev strictTransformComplAtInfinityOver :
    (strictTransformComplAtInfinity ℐ).toScheme.Over (Spec (.of ℂ)) :=
  ⟨(strictTransformComplAtInfinity ℐ).ι ≫ blowupAtInfinity ℐ ↘ Spec (.of ℂ)⟩

attribute [local instance] strictTransformComplAtInfinityOver

/-- The open immersion `M° ⟶ W` is a morphism over `ℂ`. -/
theorem isOver_strictTransformComplAtInfinity_ι :
    (strictTransformComplAtInfinity ℐ).ι.IsOver (Spec (.of ℂ)) :=
  ⟨rfl⟩

/-- **Stacks' open deformation space `M° = W ∖ X'` is a complex scheme** (Fulton, proof of
Theorem 19.2): an open subscheme of the complex scheme `W`. -/
theorem isComplexScheme_strictTransformComplAtInfinity [IsComplexScheme X] :
    IsComplexScheme (strictTransformComplAtInfinity ℐ).toScheme :=
  haveI := isComplexScheme_blowupAtInfinity ℐ
  haveI := isOver_strictTransformComplAtInfinity_ι ℐ
  isComplexScheme_opens _

end MMP.Chow
