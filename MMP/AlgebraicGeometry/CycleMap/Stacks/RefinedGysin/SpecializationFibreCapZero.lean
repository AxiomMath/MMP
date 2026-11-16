module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationFibreCapInfinity
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityPushforward

/-!
# The specialization at zero of Fulton's proof of Theorem 19.2

Let `f : X ⟶ Y` be a closed immersion of complex schemes, `g : Y' ⟶ Y`, `ρ' : W' ⟶ 𝐏¹_ℂ` the
deformation map on the test scheme `W' = W ×_Y Y'` and `σ' : Y' ⟶ W'` the section at zero. For a
lift `β ∈ A_{m+d+1}(W')` of `α ∈ A_{m+d}(Y')` (Stacks 0F9J) and an orientation class `u_0` of
the point `0 ∈ 𝐏¹(ℂ)`,

  `ρ'^* u_0 ∩ cl(β) = σ'_* cl(α)`  in `H_{2(m+d)}(ρ'⁻¹(0))`

(`MMP.Chow.specializationAtZero`, the Prop `MMP.Chow.SpecializationAtZero`). The fibre
`ρ'⁻¹(0)` is the zero scheme `D_0` of the pulled-back canonical section of `𝒪(D_0)`, on which
`𝒪(D_0)` is trivial, so `ρ'^* u_0 ∩ cl(β) = cl(i_0^* β)`
(`MMP.Chow.capProductSupportPullback_chowCycleClass_eq_gysin`); and `i_0^* β = α` on `D_0`, read
through `Y' ≅ D_0` (Stacks 0F9J and 02TR,
`MMP.Chow.onChow_lineZeroModule_eq_of_isModificationLift`, the `D_0`-level form of
`Stacks.Chow.chowPushforward_zeroGysin_of_isModificationLift`).

## Main results

* `MMP.Chow.onChow_lineZeroModule_eq_of_isModificationLift`: `i_0^* β = α` on `D_0`.
* `MMP.Chow.testZeroSection_eq_modificationSectionAtZeroBaseChange`: `σ'` is Stacks' section at
  zero.
* `MMP.Chow.specializationAtZero`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Topology Stacks.Chow
open MMP.UnderlyingSpace MMP.borelMooreHomology
open scoped MMP.SubschemeOver

namespace MMP.Chow

/-! ### `i_0^* β = α` on the fibre at zero -/

section ZeroGysin

variable (C : ChowSituation.{0}) {X W T : Scheme.{0}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b] (g : T ⟶ X) [LocallyOfFiniteType g]

/-- The identification `T ≅ D_0` of the test scheme with the pulled-back divisor `D_0` of
`W ×_X T`, through the chart over `𝐀¹_X`. -/
def zeroDivisorIso (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    T ⟶ (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
      (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
      (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subscheme :=
  haveI := isIso_modificationAffineZeroScheme_comp f b g hA
  inv ((modificationAffineZeroScheme f b g).subschemeι ≫ modificationAffineChartProjection f b g) ≫
    modificationAffineZeroSchemeMap f b g

/-- The morphism `zeroDivisorIso : T ⟶ D_0` is an isomorphism. -/
instance isIso_zeroDivisorIso (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    IsIso (zeroDivisorIso C f b g hA) := by
  have := isIso_modificationAffineZeroScheme_comp f b g hA
  unfold zeroDivisorIso
  infer_instance

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] in
/-- `T ≅ D_0 ⊆ W ×_X T` is the base-changed section at zero. -/
theorem zeroDivisorIso_comp_subschemeι
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    zeroDivisorIso C f b g hA ≫ (Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι =
      modificationSectionAtZeroBaseChange f b (isIso_modificationFibreAtZeroProjection f b hA)
        (modificationSectionAtZero_comp_projection f b hA) g := by
  rw [modificationSectionAtZeroBaseChange_eq f b g hA, zeroDivisorIso, Category.assoc,
    Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι]

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] in
/-- `T ≅ D_0` is a morphism over the base. -/
theorem zeroDivisorIso_over (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) :
    zeroDivisorIso C f b g hA ≫ ((Stacks.Divisors.zeroScheme (modificationBaseChange f b g)
        (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))).subschemeι ≫
          modificationBaseChangeOver f b g) = g ≫ f := by
  rw [← Category.assoc, zeroDivisorIso_comp_subschemeι C, modificationSectionAtZeroBaseChange_over]

/-- **Stacks 0F9J, `i_0^* β = α` on the fibre at zero** (Stacks 02TR). For a lift `β` of `α`, the
Gysin map at the pulled-back divisor `D_0` sends `β` to `α`, read on `D_0` through `T ≅ D_0`. -/
theorem onChow_lineZeroModule_eq_of_isModificationLift
    (hA : IsIso (pullback.snd b (projectiveLineAffineChart f))) (k : ℤ)
    (α : chowGroup C (g ≫ f) k) (β : chowGroup C (modificationBaseChangeOver f b g) (k + 1))
    (hβ : IsModificationLift C f b hA g k α β) :
    (gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
        (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)) k β =
      chowPushforwardOfIso C (g ≫ f) _ (zeroDivisorIso C f b g hA) (zeroDivisorIso_over C f b g hA)
        k α := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by ring⟩
  have := flat_modificationAffineChartProjection f b g hA
  have := isIso_modificationAffineZeroScheme_comp f b g hA
  have hj := Stacks.Divisors.zeroSchemePullbackMap_comp_structureMorphism
    (modificationAffineChartι f b g) (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
    (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g))
    (modificationBaseChangeOver f b g) (modificationAffineChartOver C f b g) rfl
  have hnat := gysinSystemOfInvertible_isNaturalUnderOpensRestriction C
    (modificationBaseChangeOver f b g) (modificationAffineChartOver C f b g)
    (modificationAffineChartι f b g) rfl
    (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
    (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)) (k' + 1)
    (modificationAffineZeroSchemeMap f b g)
    (Stacks.Divisors.zeroSchemePullbackMap_comp_subschemeι _ _ _) hj β
  unfold IsModificationLift at hβ
  rw [hβ, gysinSystemOfInvertible_onChow_flatPullbackChow_of_isIso C
      (modificationAffineChartOver C f b g) (g ≫ f) (modificationAffineChartProjection f b g)
      (modificationAffineChartProjection_over C f b g)
      (relativeDimension_modificationAffineChartProjection f b g hA) _ _
      (isRelativeEffectiveCartierDivisor_modificationAffineZeroScheme f b g hA) k' α,
    chowGroupRestrict_of_isIso] at hnat
  have key : (gysinSystemOfInvertible C).onChow (modificationBaseChangeOver f b g)
      (lineZeroModule (modificationBaseChangeToRelativeLine f b g))
      (lineZeroModuleSection (modificationBaseChangeToRelativeLine f b g)) (k' + 1) β =
      chowPushforwardOfIso C _ _ (modificationAffineZeroSchemeMap f b g) hj (k' + 1)
        (chowPushforwardOfIso C (g ≫ f) _
          (inv ((modificationAffineZeroScheme f b g).subschemeι ≫
            modificationAffineChartProjection f b g))
          (by rw [IsIso.inv_comp_eq, Category.assoc, modificationAffineChartProjection_over])
          (k' + 1) α) := by
    rw [← hnat]
    exact ((chowGroupEquivOfIso C _ _ (modificationAffineZeroSchemeMap f b g) hj
      (k' + 1)).apply_symm_apply _).symm
  rw [key, chowPushforwardOfIso_comp_apply]
  rfl

end ZeroGysin

/-- Proper push-forward of cycles commutes with transport along an equality of structure
morphisms of the source. -/
theorem properPushforward_cycleGroupStructureCongr {A B : Scheme.{0}}
    {sA sA' : A ⟶ (fieldChowSituation ℂ).S} [LocallyOfFiniteType sA] [LocallyOfFiniteType sA']
    (sB : B ⟶ (fieldChowSituation ℂ).S) [LocallyOfFiniteType sB] (u : A ⟶ B) [IsProper u]
    (hq : sA = sA') (hu : u ≫ sB = sA) (hu' : u ≫ sB = sA') (k : ℤ)
    (c : CycleGroup (fieldChowSituation ℂ) sA k) :
    properPushforward (fieldChowSituation ℂ) sA' sB u hu' k
        (cycleGroupStructureCongr (fieldChowSituation ℂ) hq k c) =
      properPushforward (fieldChowSituation ℂ) sA sB u hu k c := by
  subst hq
  rfl

/-! ### The specialization at zero -/

section Zero

attribute [local instance low] fibreProductOver
attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct testDeformationSpaceOver blowupAtInfinityOver
  isLocallyNoetherian_of_isComplexScheme

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ} (R : Type) [CommRing R]

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [LocallyOfFiniteType g] in
omit [IsClosedImmersion f] in
/-- The lift `σ : Y ⟶ W` of the zero section is Stacks' section at zero of the modification. -/
theorem blowupZeroSection_eq_modificationSectionAtZero :
    blowupZeroSection f.ker =
      modificationSectionAtZero (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
        (isIso_modificationFibreAtZeroProjection _ _
          (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
            (Y ↘ Spec (.of ℂ)))) := by
  have hA := isIso_modificationFibreAtZeroProjection _ _
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
  have hw : blowupZeroSection f.ker ≫
      blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)) =
        𝟙 Y ≫ zeroSection (Y ↘ Spec (.of ℂ)) := by
    rw [blowupAtInfinityToProjectiveLineProduct,
      blowupZeroSection_comp_blowupAtInfinityToLine_assoc,
      Category.id_comp, zeroSection_eq]
    rfl
  have hl : pullback.lift _ _ hw = inv (modificationFibreAtZeroProjection (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))) := by
    rw [← cancel_mono (modificationFibreAtZeroProjection (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))), IsIso.inv_hom_id]
    exact pullback.lift_snd _ _ hw
  rw [modificationSectionAtZero, ← hl, pullback.lift_fst]

omit [f.IsOver (Spec (.of ℂ))] [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y]
    [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y'.Over (Spec (.of ℂ))] [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- **The section at zero `σ' : Y' ⟶ W'` is Stacks' base-changed section at zero.** -/
theorem testZeroSection_eq_modificationSectionAtZeroBaseChange :
    testZeroSection f g =
      modificationSectionAtZeroBaseChange (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
        (isIso_modificationFibreAtZeroProjection _ _
          (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))))
        (modificationSectionAtZero_comp_projection _ _
          (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
            (Y ↘ Spec (.of ℂ)))) g := by
  refine pullback.hom_ext ?_ ?_
  · rw [testZeroSection_fst, modificationSectionAtZeroBaseChange, pullback.lift_fst,
      blowupZeroSection_eq_modificationSectionAtZero]
  · rw [testZeroSection_snd, modificationSectionAtZeroBaseChange_comp_snd]

omit [X.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [LocallyOfFiniteType g] in
omit [IsClosedImmersion f] in
/-- **The zero scheme of the section at zero is `ρ'⁻¹(0)`.** -/
theorem zeroScheme_lineZeroModuleSection_eq_comap :
    Stacks.Divisors.zeroScheme (testDeformationSpace f g)
        (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)) =
      (complexParameterPoint lineZeroComplexPoint).ι.ker.comap (testDeformationToLine f g) := by
  rw [zeroScheme_lineZeroModuleSection, ker_ι_complexParameterPoint,
    modificationBaseChangeToRelativeLine_eq_testDeformationToLine]
  rfl

omit [X.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y]
    [IsComplexScheme Y'] [IsClosedImmersion f] [LocallyOfFiniteType g] in
/-- `Y' ≅ D_0` is a morphism over `ℂ`. -/
theorem isOver_zeroDivisorIso :
    (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
      (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
        (Y ↘ Spec (.of ℂ)))).IsOver (Spec (.of ℂ)) :=
  ⟨by
    change _ ≫ (Stacks.Divisors.zeroScheme _ _ _).subschemeι ≫ modificationBaseChangeOver _ _ g = _
    rw [zeroDivisorIso_over, comp_over g]⟩

omit [f.IsOver (Spec (.of ℂ))] [IsComplexScheme X] in
omit [X.Over (Spec (.of ℂ))] [IsClosedImmersion f] in
/-- The cycle class of `α`, carried to `D_0` along `Y' ≅ D_0`. -/
theorem chowCycleClass_chowPushforwardOfIso_zeroDivisorIso {k : ℕ} :
    haveI := isComplexScheme_testDeformationSpace f g
    haveI := isOver_zeroDivisorIso f g
    ∀ α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (k : ℤ),
    chowCycleClass R k (chowGroupCongr (fieldChowSituation ℂ)
        (q := (Stacks.Divisors.zeroScheme (testDeformationSpace f g)
          (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))).subschemeι ≫
              testDeformationSpace f g ↘ Spec (.of ℂ))
        (q' := (Stacks.Divisors.zeroScheme (testDeformationSpace f g)
          (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))).subscheme ↘
              Spec (.of ℂ)) rfl (k : ℤ)
        (chowPushforwardOfIso (fieldChowSituation ℂ) (g ≫ Y ↘ Spec (.of ℂ))
          ((Stacks.Divisors.zeroScheme (testDeformationSpace f g)
            (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
              (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
            (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
              (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))).subschemeι ≫
                testDeformationSpace f g ↘ Spec (.of ℂ))
          (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
            (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
              (Y ↘ Spec (.of ℂ))))
          (zeroDivisorIso_over _ _ _ g _) (k : ℤ)
          (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
            (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm (k : ℤ) α))) =
      pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (map (K := ℂ) (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
          (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
            (Y ↘ Spec (.of ℂ))))))
        (isProperMap_map (K := ℂ) _) (2 * k : ℕ) (chowCycleClass R k α) := by
  have := isComplexScheme_testDeformationSpace f g
  have := isOver_zeroDivisorIso f g
  intro α
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    rw [chowGroupCongr_mk]
    erw [chowPushforwardOfIso_mk]
    erw [properPushforward_cycleGroupStructureCongr]
    exact cycleClass_properPushforward R _ c

omit [IsComplexScheme X] in
/-- **The specialization at zero** (Fulton, proof of Theorem 19.2): for every lift `β` of `α`
(Stacks 0F9J) and every orientation class `u_0` of `0 ∈ 𝐏¹(ℂ)`,
`ρ'^* u_0 ∩ cl(β) = σ'_* cl(α)` in `H_{2(m+d)}(ρ'⁻¹(0))`. -/
theorem specializationAtZero (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) :
    SpecializationAtZero f g R m α := by
  have := isComplexScheme_testDeformationSpace f g
  have := isOver_testTrivialFamily f g
  have := isOver_testDeformationToLine f g
  have := isOver_testZeroSection f g
  have := isClosedImmersion_testZeroSection f g
  have := isOver_zeroDivisorIso f g
  intro β hβ u₀ hu₀
  have hT := smoothOfRelativeDimension_relativeProjectiveLine ℂ
  have hA := isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))
  have hζ : (gysinSystemOfInvertible (fieldChowSituation ℂ)).onChow
      (testDeformationSpace f g ↘ Spec (.of ℂ))
      (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
      (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
      ((m + d : ℕ) : ℤ) β =
      chowPushforwardOfIso (fieldChowSituation ℂ) (g ≫ Y ↘ Spec (.of ℂ))
        ((Stacks.Divisors.zeroScheme (testDeformationSpace f g)
          (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))).subschemeι ≫
              testDeformationSpace f g ↘ Spec (.of ℂ))
        (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g hA)
        (zeroDivisorIso_over _ _ _ g _) ((m + d : ℕ) : ℤ)
        (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
          (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α) :=
    onChow_lineZeroModule_eq_of_isModificationLift (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g hA
      ((m + d : ℕ) : ℤ) (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
        (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm ((m + d : ℕ) : ℤ) α) β hβ
  have hσ : zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g hA ≫
        (Stacks.Divisors.zeroScheme (testDeformationSpace f g)
          (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
          (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))).subschemeι =
      testZeroSection f g :=
    (zeroDivisorIso_comp_subschemeι _ _ _ g hA).trans
      (testZeroSection_eq_modificationSectionAtZeroBaseChange f g).symm
  let κ := TopCat.ofHom (map (K := ℂ) (inv (zeroDivisorIso (fieldChowSituation ℂ)
      (Y ↘ Spec (.of ℂ)) (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
        hA))) ≫
    fibrePointsHom (testZeroSection f g) (testDeformationToLine f g) lineZeroComplexPoint
      (testZeroSection_comp_testDeformationToLine f g)
  have hκ : IsProperMap κ :=
    (isProperMap_fibrePointsHom (testZeroSection f g) (testDeformationToLine f g)
      lineZeroComplexPoint (testZeroSection_comp_testDeformationToLine f g)).comp
      (isProperMap_map (K := ℂ) (inv (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g hA)))
  have hκι : κ ≫ subsetInclusion _ = TopCat.ofHom (map (K := ℂ)
      (Stacks.Divisors.zeroScheme (testDeformationSpace f g)
        (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
        (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
          (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))).subschemeι) := by
    refine ConcreteCategory.hom_ext _ _ fun p ↦ UnderlyingSpace.ext ?_
    change (map (K := ℂ) (testZeroSection f g) (map (K := ℂ)
      (inv (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g hA)) p)).toHom = _
    simp only [toHom_map, Category.assoc, ← hσ, IsIso.inv_hom_id_assoc]
    rfl
  have key := capProductSupportPullback_chowCycleClass_eq_gysin_of_eq R
    (testDeformationToLine f g)
    (lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
    (lineZeroModuleSection (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g))
    (complexParameterPoint lineZeroComplexPoint) hT
    (zeroScheme_lineZeroModuleSection_eq_comap f g)
    (isTrivial_lineZeroModule (modificationBaseChangeToRelativeLine (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g)) lineZeroComplexPoint
    (complexPoint_complexParameterPoint _)
    (hasProperNeighbourhoodDeformations_testFibre f g lineZeroComplexPoint)
    κ hκ hκι (MMP.Modules.isLocalOrientationClass_forget_of_isRegularImbeddingOrientationClass R
      hT lineZeroComplexPoint hu₀) (k := m + d) β
  refine key.trans ?_
  rw [hζ, chowCycleClass_chowPushforwardOfIso_zeroDivisorIso f g R]
  congr 1
  have e1 := pushforward_comp_apply' R
    (TopCat.ofHom (map (K := ℂ) (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
      (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g hA))) κ
    (isProperMap_map (K := ℂ) _) hκ (2 * (m + d) : ℕ) (chowCycleClass R (m + d) α)
  have hmap : TopCat.ofHom (map (K := ℂ) (zeroDivisorIso (fieldChowSituation ℂ)
      (Y ↘ Spec (.of ℂ)) (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g
        hA)) ≫ κ =
      fibrePointsHom (testZeroSection f g) (testDeformationToLine f g) lineZeroComplexPoint
        (testZeroSection_comp_testDeformationToLine f g) := by
    refine ConcreteCategory.hom_ext _ _ fun p ↦ Subtype.ext (UnderlyingSpace.ext ?_)
    change (map (K := ℂ) (testZeroSection f g) (map (K := ℂ)
      (inv (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g hA))
      (map (K := ℂ) (zeroDivisorIso (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g hA) p))).toHom =
      (map (K := ℂ) (testZeroSection f g) p).toHom
    simp only [toHom_map, Category.assoc, IsIso.hom_inv_id_assoc]
  erw [← e1]
  exact pushforward_apply_eq_of_hom_eq R (ModuleCat.of R R) hmap _ _ _ _

end Zero

end MMP.Chow
