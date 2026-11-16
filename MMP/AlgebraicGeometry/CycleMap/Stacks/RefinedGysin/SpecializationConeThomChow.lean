module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationConeThomSpace
public import MMP.AlgebraicGeometry.CycleMap.Stacks.Pushforward

/-!
# The specialized cone class on the test scheme

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes, `g : Y' ⟶ Y`
and `α ∈ A_k(Y')`. The specialization `(ι_* ∘ j^* ∘ C) ∩ α` of `α` to the normal cone
(`MMP.Chow.specializedConeClass`) is, on the test scheme, the push-forward along the isomorphism
`ψ : C' = C_X Y ×_Y Y' ⟶ 𝐕(E')` (`MMP.Chow.coneTestToBundle`) of the restriction to the open
`C' ⊆ W_∞ ×_Y Y'` (`MMP.Chow.coneTestMap`) of Stacks' class at infinity `C ∩ α`
(`Stacks.Chow.gysinCapAtInfinity`): this is Stacks' construction preceding 0FBK on the test scheme
(`Stacks.Chow.virtualNormalConeClass_cap_heq`). Its cycle class is then the push-forward of the
cycle class of `j^*(C ∩ α)`.

## Main results

* `MMP.Chow.specializedConeClass_eq_properChowPushforward`:
  `(ι_* ∘ j^* ∘ C) ∩ α = ψ_* j^*(C ∩ α)`.
* `MMP.Chow.chowCycleClass_specializedConeClass`:
  `cl((ι_* ∘ j^* ∘ C) ∩ α) = ψ_* cl(j^*(C ∩ α))`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules

namespace MMP.Chow

attribute [local instance low] fibreProductOver
attribute [local instance] isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct testDeformationSpaceOver blowupAtInfinityOver
  testInfinityFibreOver isLocallyNoetherian_of_isComplexScheme
  isFiniteLocallyFreeOfRank_normalBundleOfRegular isQuasicoherent_fibreNormalModule
  isFiniteLocallyFreeOfRank_fibreNormalModule isComplexScheme_totalSpace_fibreNormalModule
  coneTestSpaceOver

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ} (hf : IsRegularClosedImmersionOfCodim f d)

/-- **The specialized cone class on the test scheme** (Stacks, construction preceding 0FBK):
`(ι_* ∘ j^* ∘ C) ∩ α`, read on `𝐕(E')`, is the push-forward along `ψ : C' ⟶ 𝐕(E')` of the
restriction to the open `C' ⊆ W_∞ ×_Y Y'` of Stacks' class at infinity `C ∩ α`. -/
theorem specializedConeClass_eq_properChowPushforward (k : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) k) :
    haveI := isComplexScheme_coneTestSpace f g hf
    haveI := isOver_coneTestToBundle f g hf
    haveI := isOver_coneTestMap f g hf
    haveI := isComplexScheme_testInfinityFibre f g
    specializedConeClass f g hf k α =
      properChowPushforward (fieldChowSituation ℂ) (coneTestSpace f g hf ↘ Spec (.of ℂ))
        (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ)) (coneTestToBundle f g hf)
        (comp_over _ _) k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ (comp_over _ _) k)
        (chowGroupRestrict (fieldChowSituation ℂ) (testInfinityFibre f g ↘ Spec (.of ℂ))
          (coneTestSpace f g hf ↘ Spec (.of ℂ)) (coneTestMap f g hf) (comp_over _ _) k
          (gysinCapAtInfinity (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
            (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
            (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
              (Y ↘ Spec (.of ℂ))) g k
            (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
              (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm k α))) := by
  have := isComplexScheme_coneTestSpace f g hf
  have := isOver_coneTestToBundle f g hf
  have := isOver_coneTestMap f g hf
  have := isComplexScheme_testInfinityFibre f g
  have : IsIso (normalBundleOfRegular f hf).normalConeEmbedding :=
    VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion hf.isRegularImmersion
  have hb := isIso_bivariantPushforwardBaseChange_normalConeEmbedding f g
    (normalBundleOfRegular f hf)
  set α' := chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
    (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm (k : ℤ) α
  set γ := gysinCapAtInfinity (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
    (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
    (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ))) g k α'
  have hcap := virtualNormalConeClass_cap_heq (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
    (Y ↘ Spec (.of ℂ)) f (comp_over f _) (normalBundleOfRegular f hf) g k α'
  have : LocallyOfFiniteType (pullback.fst (Scheme.Modules.vectorBundleToBase X
      (dualSheaf (normalBundleOfRegular f hf).bundle) ≫ f) g ≫
        Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle) ≫
          X ↘ Spec (.of ℂ)) := by
    rw [← fibreNormalConeIso_hom_comp_over f g hf]
    infer_instance
  have H2 : flatPullbackChow (fieldChowSituation ℂ) (coneTestSpace f g hf ↘ Spec (.of ℂ))
      (testInfinityFibre f g ↘ Spec (.of ℂ)) (coneTestMap f g hf) (comp_over _ _) 0
      (relativeDimension_of_isOpenImmersion _) ((k : ℤ) - 0)
      (flatPullbackDescends (fieldChowSituation ℂ) _ _ _ _ _ _ _)
      ((gysinAtInfinityClass (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
        (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
        (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
          (Y ↘ Spec (.of ℂ)))).cap g k α') ≍
      chowGroupRestrict (fieldChowSituation ℂ) (testInfinityFibre f g ↘ Spec (.of ℂ))
          (coneTestSpace f g hf ↘ Spec (.of ℂ)) (coneTestMap f g hf) (comp_over _ _) k γ :=
    (flatPullbackChow_heq_congr (fieldChowSituation ℂ) _ _ (coneTestMap f g hf)
      (coneTestMap f g hf) _ _ rfl rfl _ (relativeDimension_of_isOpenImmersion _) (sub_zero (k : ℤ))
      _ (flatPullbackDescends (fieldChowSituation ℂ) _ _ _ _ _ _ _) _ γ
      (chowGroupDegreeEquiv_heq (fieldChowSituation ℂ) _ (sub_zero (k : ℤ)).symm γ)).trans
      (heq_chowGroupRestrict_flatPullbackChow (fieldChowSituation ℂ) _ _ (coneTestMap f g hf)
        _ _ k (flatPullbackDescends (fieldChowSituation ℂ) _ _ _ _ _ _ _) γ).symm
  have : LocallyOfFiniteType (pullback.fst ((normalBundleOfRegular f hf).normalConeEmbedding ≫
      (normalBundleOfRegular f hf).projection ≫ f) g ≫ Stacks.Conormal.normalConeToBase f ≫
      X ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (coneTestSpace f g hf ↘ Spec (.of ℂ)))
  have : IsIso (coneTestToBundleBase f g hf) := hb
  have hu := bivariantPushforwardBaseChange_comp_structure (C := fieldChowSituation ℂ)
    (sY := (normalBundleOfRegular f hf).projection ≫ X ↘ Spec (.of ℂ))
    ((normalBundleOfRegular f hf).normalConeEmbedding_projection_assoc (X ↘ Spec (.of ℂ)))
    ((normalBundleOfRegular f hf).projection ≫ f) g
  have H : (virtualNormalConeClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
      (comp_over f _) (normalBundleOfRegular f hf)).cap g k α' ≍
      properChowPushforward (fieldChowSituation ℂ) (coneTestSpace f g hf ↘ Spec (.of ℂ))
        (pullback.fst (Scheme.Modules.vectorBundleToBase X
          (dualSheaf (normalBundleOfRegular f hf).bundle) ≫ f) g ≫
          Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle) ≫
            X ↘ Spec (.of ℂ))
        (coneTestToBundleBase f g hf) hu k
        (properPushforwardDescends (fieldChowSituation ℂ) _ _ _ _ _)
        (chowGroupRestrict (fieldChowSituation ℂ) (testInfinityFibre f g ↘ Spec (.of ℂ))
          (coneTestSpace f g hf ↘ Spec (.of ℂ)) (coneTestMap f g hf) (comp_over _ _) k γ) :=
    hcap.trans (properChowPushforward_heq_congr (fieldChowSituation ℂ) _ _ _ hu
      (by simp) _ _ _ _ H2)
  have hcomp := properChowPushforward_comp_apply (fieldChowSituation ℂ)
    (coneTestSpace f g hf ↘ Spec (.of ℂ))
    (pullback.fst (Scheme.Modules.vectorBundleToBase X
      (dualSheaf (normalBundleOfRegular f hf).bundle) ≫ f) g ≫
      Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle) ≫
        X ↘ Spec (.of ℂ))
    (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ))
    (coneTestToBundleBase f g hf) (fibreNormalConeIso f g hf).hom
    (coneTestToBundle f g hf) rfl hu (fibreNormalConeIso_hom_comp_over f g hf) (comp_over _ _) k
    (properPushforwardDescends (fieldChowSituation ℂ) _ _ _ _ _)
    (properPushforwardDescends (fieldChowSituation ℂ) _ _ _ _ _)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ (comp_over _ _) k)
    (chowGroupRestrict (fieldChowSituation ℂ) (testInfinityFibre f g ↘ Spec (.of ℂ))
      (coneTestSpace f g hf ↘ Spec (.of ℂ)) (coneTestMap f g hf) (comp_over _ _) k γ)
  rw [hcomp]
  exact eq_of_heq (chowPushforwardOfIso_heq_congr (fieldChowSituation ℂ) _ _ _ _ rfl _ _ H)

variable (R : Type) [CommRing R]

/-- **The cycle class of the specialized cone class** (Fulton, proof of Theorem 19.2):
`cl((ι_* ∘ j^* ∘ C) ∩ α) = ψ_* cl(j^*(C ∩ α))` in `H_{2k}(𝐕(E')(ℂ))`, for the isomorphism
`ψ : C' ⟶ 𝐕(E')` and the restriction `j^*(C ∩ α)` of Stacks' class at infinity to the open
`C' ⊆ W_∞ ×_Y Y'`. -/
theorem chowCycleClass_specializedConeClass (k : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) k) :
    haveI := isComplexScheme_coneTestSpace f g hf
    haveI := isOver_coneTestToBundle f g hf
    haveI := isOver_coneTestMap f g hf
    haveI := isComplexScheme_testInfinityFibre f g
    chowCycleClass R k (specializedConeClass f g hf k α) =
      borelMooreHomology.pushforward R (ModuleCat.of R R)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) (coneTestToBundle f g hf)))
        (UnderlyingSpace.isProperMap_map (K := ℂ) _) (2 * k : ℕ)
        (chowCycleClass R k
          (chowGroupRestrict (fieldChowSituation ℂ) (testInfinityFibre f g ↘ Spec (.of ℂ))
            (coneTestSpace f g hf ↘ Spec (.of ℂ)) (coneTestMap f g hf) (comp_over _ _) k
            (gysinCapAtInfinity (fieldChowSituation ℂ) (Y ↘ Spec (.of ℂ))
              (blowupAtInfinityToProjectiveLineProduct f.ker (Y ↘ Spec (.of ℂ)))
              (isIso_pullback_snd_blowupAtInfinityToProjectiveLineProduct f.ker
                (Y ↘ Spec (.of ℂ))) g k
              (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
                (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm k α)))) := by
  have := isComplexScheme_coneTestSpace f g hf
  have := isOver_coneTestToBundle f g hf
  have := isOver_coneTestMap f g hf
  have := isComplexScheme_testInfinityFibre f g
  rw [specializedConeClass_eq_properChowPushforward]
  exact chowCycleClass_properChowPushforward_of_isProper R (coneTestToBundle f g hf) _

end MMP.Chow
