module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationTestSpace
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationFibrePoints
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityLift

/-!
# The fibres at `0` and `∞` of the deformation on a test scheme

Let `f : X ⟶ Y` be a closed immersion of complex schemes, `g : Y' ⟶ Y`, and
`ρ' : W' = W ×_Y Y' ⟶ 𝐏¹_ℂ` the deformation map on the test scheme
(`MMP.Chow.testDeformationToLine`). This file gives the two fibres of `ρ'` that Fulton's proof
of Theorem 19.2 reads the family chain on:

* at `0`, the section `σ' : Y' ⟶ W'` (`MMP.Chow.testZeroSection`), base change of the lift
  `σ : Y ⟶ W` of the zero section of `𝐏¹_Y` (`MMP.Chow.blowupZeroSection`);
* at `∞`, the closed immersion `W_∞ ×_Y Y' ⟶ W'` of Stacks' construction of the class at infinity
  (`Stacks.Chow.modificationInfinityBaseChange`), on whose source `C ∩ α` lives.

Both land in the corresponding fibre of `ρ'`, and on `ℂ`-points they give proper maps into
`ρ'(ℂ)⁻¹(0)` and `ρ'(ℂ)⁻¹(∞)` (`MMP.Chow.fibrePointsHom`).

## Main definitions

* `MMP.Chow.testZeroSection`, `MMP.Chow.testInfinityFibre`, `MMP.Chow.testInfinityInclusion`
* `MMP.Chow.fibrePointsHom`

## Main results

* `MMP.Chow.testZeroSection_comp_testDeformationToLine`
* `MMP.Chow.testInfinityInclusion_comp_testDeformationToLine`
* `MMP.Chow.isProperMap_fibrePointsHom`

## References

* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
  MMP.borelMooreHomology

namespace MMP.Chow

attribute [local instance low] fibreProductOver
attribute [local instance] testDeformationSpaceOver blowupAtInfinityOver

/-! ### Points of a fibre -/

section FibrePoints

variable {Z M T : Scheme.{0}} [Z.Over (Spec (.of ℂ))] [M.Over (Spec (.of ℂ))]
  [T.Over (Spec (.of ℂ))] (σ : Z ⟶ M) [σ.IsOver (Spec (.of ℂ))] (ρ : M ⟶ T)
  [ρ.IsOver (Spec (.of ℂ))] (t : UnderlyingSpace ℂ T)

/-- A morphism `σ : Z ⟶ M` with `ρ ∘ σ` constant at `t` lands, on `ℂ`-points, in `ρ(ℂ)⁻¹(t)`. -/
theorem map_mem_preimage_singleton (h : σ ≫ ρ = Z ↘ Spec (.of ℂ) ≫ t.toHom)
    (z : UnderlyingSpace ℂ Z) :
    UnderlyingSpace.map (K := ℂ) σ z ∈
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t}) := by
  refine UnderlyingSpace.ext ?_
  change (z.toHom ≫ σ) ≫ ρ = t.toHom
  rw [Category.assoc, h, ← Category.assoc, z.toHom_comp_over, Category.id_comp]

/-- **`Z(ℂ) ⟶ ρ(ℂ)⁻¹(t)`** for `σ : Z ⟶ M` with `ρ ∘ σ` constant at `t`. -/
def fibrePointsHom (h : σ ≫ ρ = Z ↘ Spec (.of ℂ) ≫ t.toHom) :
    TopCat.of (UnderlyingSpace ℂ Z) ⟶
      TopCat.of ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ρ) :
        TopCat.of (UnderlyingSpace ℂ M) ⟶ TopCat.of (UnderlyingSpace ℂ T)) ⁻¹' {t}) :=
  TopCat.ofHom ⟨fun z ↦ ⟨UnderlyingSpace.map (K := ℂ) σ z, map_mem_preimage_singleton σ ρ t h z⟩,
    (UnderlyingSpace.map (K := ℂ) σ).continuous.subtype_mk _⟩

/-- `Z(ℂ) ⟶ ρ(ℂ)⁻¹(t) ⊆ M(ℂ)` is `σ(ℂ)`. -/
theorem fibrePointsHom_comp_subsetInclusion (h : σ ≫ ρ = Z ↘ Spec (.of ℂ) ≫ t.toHom) :
    fibrePointsHom σ ρ t h ≫ subsetInclusion _ = TopCat.ofHom (UnderlyingSpace.map (K := ℂ) σ) :=
  rfl

/-- `Z(ℂ) ⟶ ρ(ℂ)⁻¹(t)` is proper for a closed immersion `σ`. -/
theorem isProperMap_fibrePointsHom [IsClosedImmersion σ]
    (h : σ ≫ ρ = Z ↘ Spec (.of ℂ) ≫ t.toHom) : IsProperMap (fibrePointsHom σ ρ t h) :=
  isProperMap_of_comp_of_inj (g := Subtype.val) (fibrePointsHom σ ρ t h).hom.continuous
    continuous_subtype_val
    (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) σ).isProperMap Subtype.val_injective

end FibrePoints

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [IsClosedImmersion f] (g : Y' ⟶ Y)

/-! ### The fibre at zero -/

omit [Y.Over (Spec (.of ℂ))] in
/-- The lift `σ : Y ⟶ W` of the zero section is a section of `W ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem blowupZeroSection_comp_blowupAtInfinityToBase (ℐ : Y.IdealSheafData) :
    blowupZeroSection ℐ ≫ blowupAtInfinityToBase ℐ = 𝟙 Y := by
  rw [blowupAtInfinityToBase, blowupZeroSection_comp_blowupAtInfinityToLine_assoc,
    lineZeroSection_comp]

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] in
/-- The lift `σ : Y ⟶ W` of the zero section is a morphism over `ℂ`. -/
theorem isOver_blowupZeroSection (ℐ : Y.IdealSheafData) :
    (blowupZeroSection ℐ).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change blowupZeroSection ℐ ≫ blowupAtInfinityToBase ℐ ≫ Y ↘ Spec (.of ℂ) = Y ↘ Spec (.of ℂ)
    rw [blowupZeroSection_comp_blowupAtInfinityToBase_assoc]⟩

/-- **The section at zero on the test scheme**, `σ' : Y' ⟶ W' = W ×_Y Y'`: the base change of
the lift `σ : Y ⟶ W` of the zero section of `𝐏¹_Y`. -/
def testZeroSection : Y' ⟶ testDeformationSpace f g :=
  pullback.lift (g ≫ blowupZeroSection f.ker) (𝟙 Y') (by
    rw [modificationProjection_testDeformationSpace, Category.assoc,
      blowupZeroSection_comp_blowupAtInfinityToBase, Category.comp_id, Category.id_comp])

omit [Y'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The first component of `σ'` is `σ ∘ g`. -/
@[reassoc (attr := simp)]
theorem testZeroSection_fst :
    testZeroSection f g ≫ pullback.fst _ g = g ≫ blowupZeroSection f.ker :=
  pullback.lift_fst _ _ _

omit [Y'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- `σ'` is a section of the projection `W' ⟶ Y'`. -/
@[reassoc (attr := simp)]
theorem testZeroSection_snd : testZeroSection f g ≫ pullback.snd _ g = 𝟙 Y' :=
  pullback.lift_snd _ _ _

omit [Y'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The projection `W' ⟶ Y'` is projective. -/
theorem isProjective_testDeformationSpace_snd [IsComplexScheme Y] :
    IsProjective (pullback.snd (modificationProjection (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) g) := by
  refine IsProjective.of_isPullback (IsPullback.of_hasPullback _ g).flip ?_
  rw [modificationProjection_testDeformationSpace]
  exact isProjective_blowupAtInfinityToBase f

omit [Y'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **The section at zero on the test scheme is a closed immersion**: a section of the separated
`W' ⟶ Y'`. -/
theorem isClosedImmersion_testZeroSection [IsComplexScheme Y] :
    IsClosedImmersion (testZeroSection f g) := by
  have := (isProjective_testDeformationSpace_snd f g).isProper
  have : IsClosedImmersion (testZeroSection f g ≫ pullback.snd _ g) := by
    rw [testZeroSection_snd]
    infer_instance
  exact IsClosedImmersion.of_comp (testZeroSection f g) (pullback.snd _ g)

omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The section at zero on the test scheme is a morphism over `ℂ`. -/
theorem isOver_testZeroSection [g.IsOver (Spec (.of ℂ))] :
    (testZeroSection f g).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change testZeroSection f g ≫ pullback.fst _ g ≫ _ ≫ Y ↘ Spec (.of ℂ) = Y' ↘ Spec (.of ℂ)
    rw [testZeroSection_fst_assoc, modificationProjection_testDeformationSpace,
      blowupZeroSection_comp_blowupAtInfinityToBase_assoc, comp_over g]⟩

omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **`ρ' ∘ σ' = 0`**: the section at zero lands in the fibre at zero of the deformation map. -/
theorem testZeroSection_comp_testDeformationToLine [g.IsOver (Spec (.of ℂ))] :
    testZeroSection f g ≫ testDeformationToLine f g =
      Y' ↘ Spec (.of ℂ) ≫ lineZeroComplexPoint.toHom := by
  change _ = Y' ↘ Spec (.of ℂ) ≫ lineZeroSection (Spec (.of ℂ))
  rw [testDeformationToLine, testZeroSection_fst_assoc,
    blowupZeroSection_comp_blowupAtInfinityToLine_assoc,
    (isPullback_lineZeroSection_projectiveLineBaseChange (Y ↘ Spec (.of ℂ))).w, ← Category.assoc,
    comp_over g]

/-! ### The fibre at infinity -/

/-- **The fibre at infinity on the test scheme**, `W_∞ ×_Y Y'`: the scheme on which Stacks' class
at infinity caps classes of `Y'` (Stacks 0F9J). -/
abbrev testInfinityFibre : Scheme.{0} :=
  pullback (modificationProjectionAtInfinity (Y ↘ Spec (.of ℂ))
    (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) g

/-- `W_∞ ×_Y Y'` over `ℂ`, through `W_∞ ×_Y Y' ⟶ W_∞ ⟶ Y`
(`Stacks.Chow.modificationInfinityBaseChangeOver`). -/
abbrev testInfinityFibreOver : (testInfinityFibre f g).Over (Spec (.of ℂ)) :=
  ⟨modificationInfinityBaseChangeOver (Y ↘ Spec (.of ℂ))
    (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g⟩

attribute [local instance] testInfinityFibreOver

/-- **The inclusion `W_∞ ×_Y Y' ⟶ W'` of the fibre at infinity** on the test scheme. -/
abbrev testInfinityInclusion : testInfinityFibre f g ⟶ testDeformationSpace f g :=
  modificationInfinityBaseChange (Y ↘ Spec (.of ℂ))
    (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The inclusion of the fibre at infinity is a morphism over `ℂ`. -/
theorem isOver_testInfinityInclusion : (testInfinityInclusion f g).IsOver (Spec (.of ℂ)) :=
  ⟨modificationInfinityBaseChange_over _ _ g⟩

omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The complex scheme structure on the fibre at infinity: it is closed in `W'`. -/
theorem isComplexScheme_testInfinityFibre [IsComplexScheme Y] [IsComplexScheme Y']
    [g.IsOver (Spec (.of ℂ))] : IsComplexScheme (testInfinityFibre f g) :=
  haveI := isComplexScheme_testDeformationSpace f g
  haveI := isOver_testInfinityInclusion f g
  isComplexScheme_of_isClosedImmersion (testInfinityInclusion f g)

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] in
omit [IsClosedImmersion f] in
/-- The inclusion `W_∞ ⟶ W` followed by `W ⟶ 𝐏¹_Y` is `W_∞ ⟶ Y ⟶ 𝐏¹_Y` through the infinity
section. -/
@[reassoc]
theorem modificationInclusionAtInfinity_comp_blowupAtInfinityToLine :
    modificationInclusionAtInfinity (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) ≫
          blowupAtInfinityToLine f.ker =
      pullback.snd _ _ ≫ lineInfinitySection Y := by
  rw [← cancel_mono (relativeProjectiveLineIsoProjectiveLineProduct (Y ↘ Spec (.of ℂ))).hom,
    Category.assoc, Category.assoc,
    lineInfinitySection_comp_relativeProjectiveLineIsoProjectiveLineProduct_hom]
  exact pullback.condition

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **`ρ' = ∞` on the fibre at infinity**: the inclusion `W_∞ ×_Y Y' ⟶ W'` lands in the fibre at
infinity of the deformation map. -/
theorem testInfinityInclusion_comp_testDeformationToLine :
    testInfinityInclusion f g ≫ testDeformationToLine f g =
      testInfinityFibre f g ↘ Spec (.of ℂ) ≫ lineInfinityComplexPoint.toHom := by
  change _ = modificationInfinityBaseChangeOver _ _ g ≫ lineInfinitySection (Spec (.of ℂ))
  rw [testDeformationToLine, reassoc_of% (modificationInfinityBaseChange_comp_fst _ _ g),
    Category.assoc,
    modificationInclusionAtInfinity_comp_blowupAtInfinityToLine_assoc,
    (isPullback_lineInfinitySection_projectiveLineBaseChange (Y ↘ Spec (.of ℂ))).w]
  simp only [Category.assoc]
  congr 1
  rw [pullback.condition_assoc, reassoc_of% (infinitySection_comp_fst (Y ↘ Spec (.of ℂ)))]

end MMP.Chow
