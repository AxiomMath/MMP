module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationFibreCap
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import MMP.AlgebraicGeometry.CycleMap.OrientationClass.SpecializationFibreGeneric

/-!
# The specialization at infinity of Fulton's proof of Theorem 19.2

Let `f : X ⟶ Y` be a closed immersion of complex schemes, `g : Y' ⟶ Y`, `ρ' : W' ⟶ 𝐏¹_ℂ` the
deformation map on the test scheme `W' = W ×_Y Y'` and `W_∞ ×_Y Y' ⊆ W'` its fibre at infinity.
For a lift `β ∈ A_{m+d+1}(W')` of `α ∈ A_{m+d}(Y')` (Stacks 0F9J) and an orientation class `u_∞`
of the point `∞ ∈ 𝐏¹(ℂ)`,

  `ρ'^* u_∞ ∩ cl(β) = cl(C ∩ α)`  in `H_{2(m+d)}(ρ'⁻¹(∞))`

(`MMP.Chow.specializationAtInfinity`, the Prop `MMP.Chow.SpecializationAtInfinity`). By Stacks
0F9J, `C ∩ α = i_∞^* β` is the Gysin map of the pulled-back canonical section of `𝒪(D_∞)`, whose
zero scheme is the fibre `ρ'⁻¹(∞)` and on which `𝒪(D_∞)` is trivial; so this is the fibre
specialization formula `MMP.Chow.capProductSupportPullback_chowCycleClass_eq_gysin`.

## Main results

* `MMP.Chow.complexParameterPoint`: a complex point of a smooth complex variety as a parameter
  point.
* `MMP.Chow.specializationAtInfinity`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology Stacks.Chow
open MMP.UnderlyingSpace MMP.borelMooreHomology
open scoped MMP.SubschemeOver

namespace MMP.Chow

/-! ### Complex points as parameter points -/

section ComplexParameterPoint

variable {B : Scheme.{0}} [B.Over (Spec (.of ℂ))] [IsSmoothVariety ℂ (B ↘ Spec (.of ℂ))]

/-- The local rings of a smooth complex variety are regular. -/
theorem isRegularLocalRing_stalk_of_isSmoothVariety (b : B) :
    IsRegularLocalRing (B.presheaf.stalk b) :=
  ((show IsRegular B ↔ IsLocallyNoetherian B ∧ ∀ x : B, IsRegularLocalRing (B.presheaf.stalk x)
    from (isRegular_tfae B).out 1 2).mp (isRegular_of_smooth_over_field (B ↘ Spec (.of ℂ)))).2 b

/-- A complex point of a smooth complex variety, as a parameter point. -/
def complexParameterPoint (p : UnderlyingSpace ℂ B) : ParameterPoint B :=
  ParameterPoint.ofSection ℂ p.toHom p.toHom_comp_over
    (isRegularLocalRing_stalk_of_isSmoothVariety _)

/-- The complex point of `complexParameterPoint p` is `p`. -/
theorem complexPoint_complexParameterPoint (p : UnderlyingSpace ℂ B) :
    (complexParameterPoint p).complexPoint = p := by
  rw [UnderlyingSpace.eq_iff_toHom_closedPoint_eq, ParameterPoint.complexPoint_toHom_closedPoint]
  rfl

/-- The ideal sheaf of the closed immersion of `complexParameterPoint p` is the kernel of the
morphism `Spec ℂ ⟶ B` defined by `p`. -/
theorem ker_ι_complexParameterPoint (p : UnderlyingSpace ℂ B) :
    (complexParameterPoint p).ι.ker = p.toHom.ker := by
  rw [← ParameterPoint.ker_toHom_complexPoint, complexPoint_complexParameterPoint]

end ComplexParameterPoint

/-! ### The specialization at infinity -/

section Infinity

attribute [local instance low] fibreProductOver
attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct testDeformationSpaceOver blowupAtInfinityOver
  testInfinityFibreOver isLocallyNoetherian_of_isComplexScheme

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ} (R : Type) [CommRing R]

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [LocallyOfFiniteType g] in
omit [IsClosedImmersion f] in
/-- Stacks' map `W ×_Y Y' ⟶ 𝐏¹_ℂ` is the deformation map `ρ'` on the test scheme. -/
theorem modificationBaseChangeToRelativeLine_eq_testDeformationToLine :
    modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g =
      testDeformationToLine f g := by
  simp only [modificationBaseChangeToRelativeLine, modificationBaseChangeToLine,
    blowupAtInfinityToProjectiveLineProduct, Category.assoc,
    relativeProjectiveLineIsoProjectiveLineProduct_hom_snd]
  rfl

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [LocallyOfFiniteType g] in
omit [IsClosedImmersion f] in
/-- **The zero scheme of the section at infinity is `ρ'⁻¹(∞)`** (Stacks 0F9J). -/
theorem zeroScheme_modificationInfinitySection_eq_comap :
    Stacks.Divisors.zeroScheme (testDeformationSpace f g)
        (modificationInfinityModule (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)
        (modificationInfinitySection (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g) =
      (complexParameterPoint lineInfinityComplexPoint).ι.ker.comap (testDeformationToLine f g) := by
  rw [zeroScheme_lineInfinityModuleSection, ker_ι_complexParameterPoint,
    modificationBaseChangeToRelativeLine_eq_testDeformationToLine]
  rfl

omit [X.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [IsComplexScheme X] in
omit [Y'.Over (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] [IsComplexScheme Y] [IsComplexScheme Y']
    [IsClosedImmersion f] [LocallyOfFiniteType g] in
/-- The identification of the zero scheme at infinity with `W_∞ ×_Y Y'` is a morphism over
`ℂ`. -/
theorem isOver_modificationInfinityZeroSchemeIso_hom :
    (modificationInfinityZeroSchemeIso (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g).hom.IsOver
        (Spec (.of ℂ)) :=
  ⟨modificationInfinityZeroSchemeIso_over (fieldChowSituation ℂ) _ _ g⟩

omit [f.IsOver (Spec (.of ℂ))] [IsComplexScheme X] in
omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The cycle class of the Gysin map at infinity, read through the zero scheme. -/
theorem chowCycleClass_chowPushforwardOfIso_modificationInfinityZeroSchemeIso {k : ℕ} :
    haveI := isComplexScheme_testDeformationSpace f g
    haveI := isComplexScheme_testInfinityFibre f g
    haveI := isOver_modificationInfinityZeroSchemeIso_hom f g
    ∀ γ : chowGroup (fieldChowSituation ℂ)
      ((Stacks.Divisors.zeroScheme (testDeformationSpace f g)
        (modificationInfinityModule (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)
        (modificationInfinitySection (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)).subschemeι ≫
        testDeformationSpace f g ↘ Spec (.of ℂ)) (k : ℤ),
    chowCycleClass R k (chowPushforwardOfIso (fieldChowSituation ℂ) _ _
        (modificationInfinityZeroSchemeIso (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g).hom
        (modificationInfinityZeroSchemeIso_over (fieldChowSituation ℂ) _ _ g) (k : ℤ) γ) =
      pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (map (K := ℂ) (modificationInfinityZeroSchemeIso (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g).hom))
        (isProperMap_map (K := ℂ) _) (2 * k : ℕ)
        (chowCycleClass R k (chowGroupCongr (fieldChowSituation ℂ)
          (q' := (Stacks.Divisors.zeroScheme (testDeformationSpace f g)
            (modificationInfinityModule (Y ↘ Spec (.of ℂ))
              (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)
            (modificationInfinitySection (Y ↘ Spec (.of ℂ))
              (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)).subscheme ↘
                Spec (.of ℂ)) rfl (k : ℤ) γ)) := by
  have := isComplexScheme_testDeformationSpace f g
  have := isComplexScheme_testInfinityFibre f g
  have := isOver_modificationInfinityZeroSchemeIso_hom f g
  intro γ
  induction γ using QuotientAddGroup.induction_on with
  | H c => exact cycleClass_properPushforward R _ _

omit [IsComplexScheme X] in
/-- **The specialization at infinity** (Fulton, proof of Theorem 19.2): for every lift `β` of
`α` (Stacks 0F9J) and every orientation class `u_∞` of `∞ ∈ 𝐏¹(ℂ)`,
`ρ'^* u_∞ ∩ cl(β) = cl(C ∩ α)` in `H_{2(m+d)}(ρ'⁻¹(∞))`. -/
theorem specializationAtInfinity (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) :
    SpecializationAtInfinity f g R m α := by
  have := isComplexScheme_testDeformationSpace f g
  have := isComplexScheme_testInfinityFibre f g
  have := isOver_testTrivialFamily f g
  have := isOver_testDeformationToLine f g
  have := isOver_testInfinityInclusion f g
  have := isOver_modificationInfinityZeroSchemeIso_hom f g
  intro β hβ u₁ hu₁
  have hgc := gysinCapAtInfinity_eq_of_isModificationLift (fieldChowSituation ℂ)
    (Y ↘ Spec (.of ℂ)) (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
    ((m + d : ℕ) : ℤ) (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
      (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α) β hβ
  rw [hgc]
  have hT := smoothOfRelativeDimension_relativeProjectiveLine ℂ
  let κ := TopCat.ofHom (map (K := ℂ) (modificationInfinityZeroSchemeIso (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g).hom) ≫
    fibrePointsHom (testInfinityInclusion f g) (testDeformationToLine f g)
      lineInfinityComplexPoint (testInfinityInclusion_comp_testDeformationToLine f g)
  have hκ : IsProperMap κ :=
    (isProperMap_fibrePointsHom (testInfinityInclusion f g) (testDeformationToLine f g)
      lineInfinityComplexPoint (testInfinityInclusion_comp_testDeformationToLine f g)).comp
      (isProperMap_map (K := ℂ) (modificationInfinityZeroSchemeIso (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g).hom)
  have hκι : κ ≫ subsetInclusion _ = TopCat.ofHom (map (K := ℂ)
      (Stacks.Divisors.zeroScheme (testDeformationSpace f g)
        (modificationInfinityModule (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)
        (modificationInfinitySection (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)).subschemeι) := by
    refine ConcreteCategory.hom_ext _ _ fun p ↦ UnderlyingSpace.ext ?_
    change (map (K := ℂ) (testInfinityInclusion f g) (map (K := ℂ)
      (modificationInfinityZeroSchemeIso (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g).hom p)).toHom = _
    simp only [toHom_map, Category.assoc, modificationInfinityZeroSchemeIso_hom_comp]
    rfl
  have key := capProductSupportPullback_chowCycleClass_eq_gysin_of_eq R
    (testDeformationToLine f g)
    (modificationInfinityModule (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)
    (modificationInfinitySection (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)
    (complexParameterPoint lineInfinityComplexPoint) hT
    (zeroScheme_modificationInfinitySection_eq_comap f g)
    (isTrivial_modificationInfinityModule (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g) lineInfinityComplexPoint
    (complexPoint_complexParameterPoint _)
    (hasProperNeighbourhoodDeformations_testFibre f g lineInfinityComplexPoint)
    κ hκ hκι (MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass R
      hT lineInfinityComplexPoint hu₁) (k := m + d) β
  refine key.trans ?_
  have h2 := chowCycleClass_chowPushforwardOfIso_modificationInfinityZeroSchemeIso f g R
    (k := m + d) ((gysinSystemOfInvertible (fieldChowSituation ℂ)).onChow
      (testDeformationSpace f g ↘ Spec (.of ℂ))
      (modificationInfinityModule (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)
      (modificationInfinitySection (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g) ((m + d : ℕ) : ℤ) β)
  rw [show chowCycleClass R (m + d) (modificationInfinityGysin (fieldChowSituation ℂ)
      (Y ↘ Spec (.of ℂ)) (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
      ((m + d : ℕ) : ℤ) β) = _ from h2]
  congr 1
  exact pushforward_comp_apply' R _ _ _ _ _ _

end Infinity

end MMP.Chow
