module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationStatement
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationTrivialFamily
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationLine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition

/-!
# The deformation to the normal cone on a test scheme

Let `f : X ⟶ Y` be a closed immersion of complex schemes, `g : Y' ⟶ Y` a morphism of complex
schemes and `X' = X ×_Y Y'`. Stacks' construction of the Gysin class (Stacks 0FBK) caps a class
`α ∈ A_k(Y')` with the class at infinity `C` of the blowup `b : W ⟶ 𝐏¹_Y` of Stacks 0FBG
(`Stacks.Chow.gysinAtInfinityClass`) on the test scheme `g`, that is on the base change
`W' = W ×_Y Y'` (`Stacks.Chow.modificationBaseChange`): `C ∩ α = i_∞^* β` for a lift `β` of `α`
to `W'`. This file equips `W'` with what Fulton's family argument (the proof of Theorem 19.2)
needs:

* `W'` is a complex scheme (`MMP.Chow.isComplexScheme_testDeformationSpace`): it is projective
  over `Y'`;
* the deformation map `ρ' : W' ⟶ W ⟶ 𝐏¹_Y ⟶ 𝐏¹_ℂ` (`MMP.Chow.testDeformationToLine`);
* the trivial family `e : X' × 𝐏¹_ℂ ⟶ W'` (`MMP.Chow.testTrivialFamily`), a closed immersion
  over `ℂ` with `ρ' ∘ e = pr₂`: the base change along `W' ⟶ W` of the closed immersion
  `𝐏¹_X ⟶ W` of Stacks 0FBG (8) (`MMP.Chow.isPullback_testLineMap`).

## Main definitions

* `MMP.Chow.testDeformationSpace`, `MMP.Chow.testDeformationSpaceOver`
* `MMP.Chow.testDeformationToLine`
* `MMP.Chow.testLineMap`, `MMP.Chow.testTrivialFamily`

## Main results

* `MMP.Chow.isComplexScheme_testDeformationSpace`
* `MMP.Chow.isPullback_testLineMap`
* `MMP.Chow.isClosedImmersion_testTrivialFamily`
* `MMP.Chow.testTrivialFamily_comp_testDeformationToLine`

## References

* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

namespace MMP.Chow

attribute [local instance low] fibreProductOver

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [IsClosedImmersion f] (g : Y' ⟶ Y)

/-- **The deformation space on the test scheme `g`**: `W' = W ×_Y Y'` for Stacks' blowup
`W ⟶ 𝐏¹_Y` at infinity in the centre `∞(X)` (Stacks 0FBG), the scheme on which Stacks' class
at infinity caps classes of `Y'` (`Stacks.Chow.modificationBaseChange`). -/
abbrev testDeformationSpace : Scheme.{0} :=
  modificationBaseChange (Y ↘ Spec (.of ℂ))
    (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g

/-- `W' = W ×_Y Y'` over `ℂ`, through `W' ⟶ W ⟶ Y`: the structure morphism of the Chow groups
of `W'` in Stacks' construction (`Stacks.Chow.modificationBaseChangeOver`). -/
abbrev testDeformationSpaceOver : (testDeformationSpace f g).Over (Spec (.of ℂ)) :=
  ⟨modificationBaseChangeOver (Y ↘ Spec (.of ℂ))
    (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g⟩

attribute [local instance] testDeformationSpaceOver

omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The structure morphism `W ⟶ Y` of Stacks' modification is the projection of the blowup at
infinity. -/
theorem modificationProjection_testDeformationSpace :
    modificationProjection (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) =
      blowupAtInfinityToBase f.ker :=
  modificationProjection_blowupAtInfinityToProjectiveLineProduct _ _

omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The projection `W' ⟶ Y'` is a morphism over `ℂ` when `g` is. -/
theorem isOver_testDeformationSpace_snd [g.IsOver (Spec (.of ℂ))] :
    (pullback.snd (modificationProjection (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) g).IsOver
        (Spec (.of ℂ)) :=
  ⟨by
    change _ ≫ Y' ↘ Spec (.of ℂ) = pullback.fst _ g ≫ _ ≫ Y ↘ Spec (.of ℂ)
    rw [← comp_over g, pullback.condition_assoc]⟩

omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **The blowup at infinity of a complex scheme is projective over it**: `W ⟶ 𝐏¹_Y` is a
blowup in a centre of finite type (Stacks 02NS) and `𝐏¹_Y ⟶ Y` is projective, over the
quasi-compact, quasi-separated `Y` (Stacks 0C4P). -/
theorem isProjective_blowupAtInfinityToBase [IsComplexScheme Y] :
    IsProjective (blowupAtInfinityToBase f.ker) := by
  have : IsNoetherian (Spec (CommRingCat.of ℂ)) :=
    isNoetherian_Spec.mpr (inferInstanceAs (IsNoetherianRing ℂ))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of ℂ))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of ℂ))
  have : IsNoetherian Y := {}
  have : IsLocallyNoetherian (relativeProjectiveLine Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (relativeProjectiveLine Y ↘ Y)
  have hI : (infinityCentreIdeal f.ker).IsFiniteType := fun U =>
    haveI := IsLocallyNoetherian.component_noetherian U
    IsNoetherian.noetherian ((infinityCentreIdeal f.ker).ideal U)
  exact IsProjective.comp (Stacks.Blowup.isProjective_blowUpToBase _ hI)
    (isProjective_relativeProjectiveLine_over ℂ (Y ↘ Spec (.of ℂ)))

omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **`W' = W ×_Y Y'` is a complex scheme**: it is projective over the complex scheme `Y'`, as
a base change of the projective `W ⟶ Y`. -/
theorem isComplexScheme_testDeformationSpace [IsComplexScheme Y] [IsComplexScheme Y']
    [g.IsOver (Spec (.of ℂ))] :
    IsComplexScheme (testDeformationSpace f g) := by
  have := isOver_testDeformationSpace_snd f g
  refine isComplexScheme_of_isProjective_hom (pullback.snd _ g) ?_
  refine IsProjective.of_isPullback (IsPullback.of_hasPullback _ g).flip ?_
  rw [modificationProjection_testDeformationSpace]
  exact isProjective_blowupAtInfinityToBase f

/-- **The deformation map on the test scheme**, `ρ' : W' ⟶ W ⟶ 𝐏¹_Y ⟶ 𝐏¹_ℂ`. -/
def testDeformationToLine : testDeformationSpace f g ⟶ relativeProjectiveLine (Spec (.of ℂ)) :=
  pullback.fst _ g ≫ blowupAtInfinityToLine f.ker ≫ projectiveLineBaseChange (Y ↘ Spec (.of ℂ))

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- `ρ' : W' ⟶ 𝐏¹_ℂ` is a morphism over `ℂ`. -/
theorem isOver_testDeformationToLine : (testDeformationToLine f g).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change (pullback.fst _ g ≫ blowupAtInfinityToLine f.ker ≫
        projectiveLineBaseChange (Y ↘ Spec (.of ℂ))) ≫ pullback.fst _ _ =
      pullback.fst _ g ≫ (blowupAtInfinityToLine f.ker ≫
        (relativeProjectiveLineIsoProjectiveLineProduct (Y ↘ Spec (.of ℂ))).hom) ≫
          pullback.fst _ _ ≫ Y ↘ Spec (.of ℂ)
    simp only [Category.assoc, relativeProjectiveLineIsoProjectiveLineProduct_hom_fst_assoc]
    exact congrArg (pullback.fst _ g ≫ blowupAtInfinityToLine f.ker ≫ ·)
      (projectiveLineBaseChange_over (Y ↘ Spec (.of ℂ)))⟩

/-- The trivial family `𝐏¹_X ⟶ W` of Stacks 0FBG (8), read on `𝐏¹_X` through `X ≅ V(ker f)`. -/
def lineToBlowupAtInfinityOfClosedImmersion :
    relativeProjectiveLine X ⟶ blowupAtInfinity f.ker :=
  projectiveLineBaseChange f.toImage ≫ lineToBlowupAtInfinity f.ker

omit [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The trivial family `𝐏¹_X ⟶ W` followed by `W ⟶ Y` is `𝐏¹_X ⟶ X ⟶ Y`. -/
@[reassoc]
theorem lineToBlowupAtInfinityOfClosedImmersion_comp :
    lineToBlowupAtInfinityOfClosedImmersion f ≫ blowupAtInfinityToLine f.ker =
      projectiveLineBaseChange f := by
  rw [lineToBlowupAtInfinityOfClosedImmersion, Category.assoc, lineToBlowupAtInfinity_comp,
    ← projectiveLineBaseChange_comp, Scheme.Hom.toImage_imageι]

omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The trivial family `𝐏¹_X ⟶ W` followed by the projection `W ⟶ Y` is `𝐏¹_X ⟶ X ⟶ Y`. -/
@[reassoc]
theorem lineToBlowupAtInfinityOfClosedImmersion_modificationProjection :
    lineToBlowupAtInfinityOfClosedImmersion f ≫ modificationProjection (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) =
      relativeProjectiveLine X ↘ X ≫ f := by
  rw [modificationProjection, blowupAtInfinityToProjectiveLineProduct, Category.assoc,
    lineToBlowupAtInfinityOfClosedImmersion_comp_assoc,
    relativeProjectiveLineIsoProjectiveLineProduct_hom_fst, projectiveLineBaseChange_over]

/-- The trivial family `𝐏¹_X ⟶ W` is a closed immersion. -/
instance isClosedImmersion_lineToBlowupAtInfinityOfClosedImmersion :
    IsClosedImmersion (lineToBlowupAtInfinityOfClosedImmersion f) := by
  rw [lineToBlowupAtInfinityOfClosedImmersion]
  infer_instance

/-- **The trivial family on the test scheme**, `𝐏¹_{X'} ⟶ W' = W ×_Y Y'`: the base change of
`𝐏¹_X ⟶ W` along `W' ⟶ W`. -/
def testLineMap : relativeProjectiveLine (pullback f g) ⟶ testDeformationSpace f g :=
  pullback.lift (projectiveLineBaseChange (pullback.fst f g) ≫
      lineToBlowupAtInfinityOfClosedImmersion f)
    (relativeProjectiveLine (pullback f g) ↘ pullback f g ≫ pullback.snd f g) (by
      rw [Category.assoc, lineToBlowupAtInfinityOfClosedImmersion_modificationProjection,
        ← Category.assoc, projectiveLineBaseChange_over, Category.assoc, Category.assoc,
        pullback.condition])

omit [Y'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The trivial family `𝐏¹_{X'} ⟶ W'` followed by `W' ⟶ W` is `𝐏¹_{X'} ⟶ 𝐏¹_X ⟶ W`. -/
@[reassoc (attr := simp)]
theorem testLineMap_fst :
    testLineMap f g ≫ pullback.fst _ g =
      projectiveLineBaseChange (pullback.fst f g) ≫ lineToBlowupAtInfinityOfClosedImmersion f :=
  pullback.lift_fst _ _ _

omit [Y'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The trivial family `𝐏¹_{X'} ⟶ W'` followed by `W' ⟶ Y'` is `𝐏¹_{X'} ⟶ X' ⟶ Y'`. -/
@[reassoc (attr := simp)]
theorem testLineMap_snd :
    testLineMap f g ≫ pullback.snd _ g =
      relativeProjectiveLine (pullback f g) ↘ pullback f g ≫ pullback.snd f g :=
  pullback.lift_snd _ _ _

omit [Y'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **`𝐏¹_{X'} = 𝐏¹_X ×_W W'`**: the trivial family on the test scheme is the base change of the
trivial family `𝐏¹_X ⟶ W` along `W' ⟶ W`. -/
theorem isPullback_testLineMap :
    IsPullback (testLineMap f g) (projectiveLineBaseChange (pullback.fst f g))
      (pullback.fst _ g) (lineToBlowupAtInfinityOfClosedImmersion f) := by
  have outer : IsPullback (testLineMap f g ≫ pullback.snd _ g)
      (projectiveLineBaseChange (pullback.fst f g)) g
      (lineToBlowupAtInfinityOfClosedImmersion f ≫ modificationProjection (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) := by
    rw [testLineMap_snd, lineToBlowupAtInfinityOfClosedImmersion_modificationProjection]
    exact (isPullback_projectiveLineBaseChange (pullback.fst f g)).paste_horiz
      (IsPullback.of_hasPullback f g).flip
  exact IsPullback.of_right outer (testLineMap_fst f g) (IsPullback.of_hasPullback _ g).flip

/-- **The trivial family on the test scheme is a closed immersion.** -/
instance isClosedImmersion_testLineMap : IsClosedImmersion (testLineMap f g) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_testLineMap f g).flip
    inferInstance

/-- **The trivial family `e : X' × 𝐏¹_ℂ ⟶ W'`** of Fulton's proof of Theorem 19.2, on the test
scheme: `X' ×_ℂ 𝐏¹_ℂ ≅ 𝐏¹_{X'}` followed by `𝐏¹_{X'} ⟶ W'`. -/
def testTrivialFamily :
    pullback (pullback f g ↘ Spec (.of ℂ)) (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ)) ⟶
      testDeformationSpace f g :=
  (relativeProjectiveLineIsoProjectiveLineProduct (pullback f g ↘ Spec (.of ℂ))).inv ≫
    testLineMap f g

/-- The trivial family `X' × 𝐏¹_ℂ ⟶ W'` on the test scheme is a closed immersion. -/
instance isClosedImmersion_testTrivialFamily : IsClosedImmersion (testTrivialFamily f g) := by
  rw [testTrivialFamily]
  infer_instance

variable [f.IsOver (Spec (.of ℂ))]

omit [Y'.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **`ρ' ∘ e = pr₂`**: the trivial family on the test scheme lies over `𝐏¹_ℂ` through its second
factor. -/
theorem testTrivialFamily_comp_testDeformationToLine :
    testTrivialFamily f g ≫ testDeformationToLine f g = pullback.snd _ _ := by
  rw [testTrivialFamily, testDeformationToLine, Category.assoc, testLineMap_fst_assoc,
    lineToBlowupAtInfinityOfClosedImmersion_comp_assoc, ← projectiveLineBaseChange_comp,
    ← projectiveLineBaseChange_comp, Iso.inv_comp_eq,
    relativeProjectiveLineIsoProjectiveLineProduct_hom_snd]
  congr 1
  rw [comp_over f]
  rfl

omit [Y'.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **The trivial family `e : X' × 𝐏¹_ℂ ⟶ W'` is a morphism over `ℂ`.** -/
theorem isOver_testTrivialFamily : (testTrivialFamily f g).IsOver (Spec (.of ℂ)) :=
  ⟨by
    rw [← comp_over (pullback.fst (pullback f g ↘ Spec (.of ℂ))
      (relativeProjectiveLine (Spec (.of ℂ)) ↘ Spec (.of ℂ))) (Spec (.of ℂ))]
    change testTrivialFamily f g ≫ pullback.fst _ g ≫ _ ≫ Y ↘ Spec (.of ℂ) =
      pullback.fst _ _ ≫ pullback.fst f g ≫ X ↘ Spec (.of ℂ)
    rw [testTrivialFamily, Category.assoc, testLineMap_fst_assoc,
      ← Category.assoc (lineToBlowupAtInfinityOfClosedImmersion f),
      lineToBlowupAtInfinityOfClosedImmersion_modificationProjection, Iso.inv_comp_eq,
      relativeProjectiveLineIsoProjectiveLineProduct_hom_fst_assoc, Category.assoc,
      comp_over f, ← Category.assoc, projectiveLineBaseChange_over, Category.assoc]⟩

end MMP.Chow
