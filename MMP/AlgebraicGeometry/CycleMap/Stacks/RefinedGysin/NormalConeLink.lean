module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.SpecializationStatement

/-!
# Stacks 0FBK on the vector bundle `𝐕(E')`: `π^*(f^! α)` is the specialization of `α`

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes, `g : Y' ⟶ Y`,
`X' = X ×_Y Y'`, and `π : 𝐕(E') ⟶ X'` the vector bundle of `E' = (X' ⟶ X)^*(𝒩^∨)`
(`MMP.Chow.fibreNormalModule`), `𝒩` the normal sheaf of `f`. The defining relation of the Gysin
class of Stacks 0FBK, `p^* ∘ c(X ⟶ Y, 𝒩) = ι_* ∘ j^* ∘ C`, on the test scheme `g`, says that the
flat pull-back along `π` of `f^! α = c(X ⟶ Y, 𝒩) ∩ α` is the specialization
`(ι_* ∘ j^* ∘ C) ∩ α` of `α` to the normal cone, read on `𝐕(E') ≅ N ×_Y Y'`
(`MMP.Chow.flatPullbackChow_proj_regularNormalGysinClass_cap_eq`).

The flat pull-back of Stacks 0FBK on the test scheme `g` is along `N ×_Y Y' ⟶ X'`, which is
`N ×_Y Y' ≅ 𝐕(E')` followed by `π` (`bundleTestBaseChange_eq_fibreNormalConeIso_hom_comp_proj`);
flat pull-back along an isomorphism is push-forward along its inverse, and Stacks 02RD composes
the two.

## Main results

* `MMP.Chow.flatPullbackChow_proj_regularNormalGysinClass_cap_heq`
* `MMP.Chow.flatPullbackChow_proj_regularNormalGysinClass_cap_eq`

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules

namespace MMP.Chow

attribute [local instance] fibreProductOver isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct isLocallyNoetherian_of_isComplexScheme
  isFiniteLocallyFreeOfRank_normalBundleOfRegular isQuasicoherent_fibreNormalModule
  isFiniteLocallyFreeOfRank_fibreNormalModule isComplexScheme_totalSpace_fibreNormalModule

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ}

omit [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [IsComplexScheme Y] in
/-- The projection `N = 𝐕(𝒩^∨) ⟶ X` of the normal bundle is locally of finite type. -/
theorem locallyOfFiniteType_normalBundleToBase (hf : IsRegularClosedImmersionOfCodim f d) :
    LocallyOfFiniteType
      (Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle)) :=
  locallyOfFiniteType_vectorBundleToBase _ d

attribute [local instance] locallyOfFiniteType_normalBundleToBase

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
/-- **The flat pull-back of Stacks 0FBK on the test scheme `g` is `N ×_Y Y' ≅ 𝐕(E')` followed
by `π : 𝐕(E') ⟶ X'`.** -/
theorem bundleTestBaseChange_eq_fibreNormalConeIso_hom_comp_proj
    (hf : IsRegularClosedImmersionOfCodim f d) :
    bundleTestBaseChange f
        (Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle)) g =
      (fibreNormalConeIso f g hf).hom ≫ proj (fibreNormalModule f g hf) := by
  rw [bundleTestBaseChange_eq, fibreNormalConeIso_hom_proj]

/-- **Stacks 0FBK on `𝐕(E')`, heterogeneously.** For `α ∈ A_k(Y')`, the flat pull-back along
`π : 𝐕(E') ⟶ X'` of `f^! α = c(X ⟶ Y, 𝒩) ∩ α ∈ A_{k-d}(X')` is the specialization
`(ι_* ∘ j^* ∘ C) ∩ α` of `α`, read on `𝐕(E') ≅ N ×_Y Y'`; the two sides lie in degrees
`(k - d) + d` and `k`. -/
theorem flatPullbackChow_proj_regularNormalGysinClass_cap_heq
    (hf : IsRegularClosedImmersionOfCodim f d) (k : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (g ≫ Y ↘ Spec (.of ℂ)) k) :
    haveI := locallyOfFiniteType_proj (fibreNormalModule f g hf) d
    haveI := flat_proj (fibreNormalModule f g hf) d
    flatPullbackChow (fieldChowSituation ℂ)
        (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ)) (pullback f g ↘ Spec (.of ℂ))
        (proj (fibreNormalModule f g hf)) rfl d (relativeDimension_proj _ d) ((k : ℤ) - d)
        (flatPullbackDescends _ _ _ _ _ _ _ _)
        ((regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ))
          f (comp_over f _) hf).cap g (k : ℤ) α) ≍
      chowPushforwardOfIso (fieldChowSituation ℂ) _ _ (fibreNormalConeIso f g hf).hom
        (fibreNormalConeIso_hom_comp_over f g hf) (k : ℤ)
        ((virtualNormalConeClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
          (comp_over f _) (normalBundleOfRegular f hf)).cap g (k : ℤ) α) := by
  have := locallyOfFiniteType_proj (fibreNormalModule f g hf) d
  have := flat_proj (fibreNormalModule f g hf) d
  have : IsOpenImmersion (fibreNormalConeIso f g hf).hom := IsOpenImmersion.of_isIso _
  have hψ0 : AlgebraicGeometry.RelativeDimension (fibreNormalConeIso f g hf).hom 0 :=
    relativeDimension_of_isOpenImmersion _
  have hflat := VirtualNormalBundle.flat_projection_of_rank (normalBundleOfRegular f hf) d
  have : LocallyOfFiniteType (normalBundleOfRegular f hf).projection :=
    locallyOfFiniteType_normalBundleToBase f hf
  have : LocallyOfFiniteType (pullback.fst ((normalBundleOfRegular f hf).projection ≫ f) g ≫
      (normalBundleOfRegular f hf).projection ≫ X ↘ Spec (.of ℂ)) := inferInstance
  have hb1 : LocallyOfFiniteType (bundleTestBaseChange f
      (Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle)) g) :=
    locallyOfFiniteType_bundleTestBaseChange _ _ g
  have hb2 : Flat (bundleTestBaseChange f
      (Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle)) g) :=
    flat_bundleTestBaseChange _ _ hflat g
  generalize hx : (regularNormalGysinClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
    (Y ↘ Spec (.of ℂ)) f (comp_over f _) hf).cap g (k : ℤ) α = x
  -- Stacks 0FBK on the test scheme `g`.
  have h0 := bundleFlatPullbackChow_virtualNormalBundleClass_cap (fieldChowSituation ℂ)
    (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f (comp_over f _) (normalBundleOfRegular f hf) d g
    (k : ℤ) α
  change _ ≍ _ at h0
  rw [show (virtualNormalBundleClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      (Y ↘ Spec (.of ℂ)) f (comp_over f _) (normalBundleOfRegular f hf) d).cap g (k : ℤ) α = x
    from hx] at h0
  -- The flat pull-back along `N ×_Y Y' ⟶ X'` is `ψ^* ∘ π^*` (Stacks 02RD).
  have h1 := flatPullbackChow_comp_heq (fieldChowSituation ℂ)
    (flatPullbackDescends (fieldChowSituation ℂ)) _
    (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ)) (pullback f g ↘ Spec (.of ℂ))
    (fibreNormalConeIso f g hf).hom (proj (fibreNormalModule f g hf))
    (fibreNormalConeIso_hom_comp_over f g hf) rfl 0 d hψ0 (relativeDimension_proj _ d)
    ((k : ℤ) - d) x
  generalize hy : flatPullbackChow (fieldChowSituation ℂ)
    (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ)) (pullback f g ↘ Spec (.of ℂ))
    (proj (fibreNormalModule f g hf)) rfl d (relativeDimension_proj _ d) ((k : ℤ) - d)
    (flatPullbackDescends _ _ _ _ _ _ _ _) x = y at h1 ⊢
  -- Flat pull-back along the isomorphism `ψ` is push-forward along `ψ⁻¹`.
  have h2 := flatPullbackChow_heq_chowPushforwardOfIso (fieldChowSituation ℂ) _ _
    (fibreNormalConeIso f g hf).hom (fibreNormalConeIso_hom_comp_over f g hf) hψ0
    ((k : ℤ) - d + d) (flatPullbackDescends (fieldChowSituation ℂ) _ _ _ _ _ _ _) y
  have h3 := chowPushforwardOfIso_inv_comp (fieldChowSituation ℂ) _ _
    (inv (fibreNormalConeIso f g hf).hom)
    (by rw [IsIso.inv_comp_eq, fibreNormalConeIso_hom_comp_over]) ((k : ℤ) - d + d) y
  rw [chowPushforwardOfIso_congr (fieldChowSituation ℂ) _ _
    (inv (inv (fibreNormalConeIso f g hf).hom)) (fibreNormalConeIso f g hf).hom IsIso.inv_inv _
    (fibreNormalConeIso_hom_comp_over f g hf)] at h3
  -- The cone class is `ψ⁻¹_* π^* (f^! α)`.
  have hcone : (virtualNormalConeClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ))
      (Y ↘ Spec (.of ℂ)) f (comp_over f _) (normalBundleOfRegular f hf)).cap g (k : ℤ) α ≍
      chowPushforwardOfIso (fieldChowSituation ℂ) _ _ (inv (fibreNormalConeIso f g hf).hom)
        (by rw [IsIso.inv_comp_eq, fibreNormalConeIso_hom_comp_over]) ((k : ℤ) - d + d) y := by
    refine h0.symm.trans ?_
    refine HEq.trans ?_ (h1.symm.trans h2)
    exact @flatPullbackChow_heq_congr (fieldChowSituation ℂ) _ _
      (pullback.fst ((normalBundleOfRegular f hf).projection ≫ f) g ≫
        (normalBundleOfRegular f hf).projection ≫ X ↘ Spec (.of ℂ)) inferInstance
      (pullback f g ↘ Spec (.of ℂ)) inferInstance
      (bundleTestBaseChange f
        (Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle)) g)
      ((fibreNormalConeIso f g hf).hom ≫ proj (fibreNormalModule f g hf)) hb1 hb2
      (bundleTestBaseChange_eq_fibreNormalConeIso_hom_comp_proj f g hf ▸ hb1)
      (bundleTestBaseChange_eq_fibreNormalConeIso_hom_comp_proj f g hf ▸ hb2) _ _
      (bundleTestBaseChange_eq_fibreNormalConeIso_hom_comp_proj f g hf) _ _ (zero_add d).symm
      _ _ _ _ rfl _ _ x x HEq.rfl
  refine HEq.trans ?_ (chowPushforwardOfIso_heq_congr (fieldChowSituation ℂ) _ _
    (fibreNormalConeIso f g hf).hom (fibreNormalConeIso_hom_comp_over f g hf) (by omega) _ _
    hcone).symm
  exact (heq_of_eq h3).symm

end MMP.Chow
