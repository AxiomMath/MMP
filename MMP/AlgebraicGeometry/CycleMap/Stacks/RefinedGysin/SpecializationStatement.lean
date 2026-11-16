module

public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.Statement
public import MMP.AlgebraicGeometry.CycleMap.Stacks.RefinedGysin.ZeroSection
public import MMP.AlgebraicGeometry.CycleMap.Stacks.OrientationClass.ZeroSectionCycle.StacksComplex

/-!
# The specialization step of Fulton's proof of Theorem 19.2, on Stacks' Chow groups

Let `f : X ⟶ Y` be a regular closed immersion of codimension `d` of complex schemes, `g : Y' ⟶ Y`,
`X' = X ×_Y Y'`, and `𝒩 = 𝒞_{X/Y}^∨` the normal sheaf of `f`
(`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`), with vector bundle
`q : N = 𝐕(𝒩^∨) ⟶ X`. Stacks' construction of the Gysin class (Stacks 0FBK) specializes a class
`α ∈ A_k(Y')` to the normal cone: `(ι_* ∘ j^* ∘ C) ∩ α ∈ A_k(N ×_Y Y')`
(`Stacks.Chow.virtualNormalConeClass`), where `C` is the Gysin class at infinity of the
deformation to the normal cone (Stacks 0F9J), `j^*` the restriction to the normal cone
`C_{X'}Y' ⊆ W_∞` and `ι_*` the push-forward along `C_{X'}Y' ⊆ N ×_Y Y'`. For `α = [V]` this is the
cycle `[C_{V ∩ X'}V]` of the normal cone of `V ∩ X'` in `V`.

`N ×_Y Y' = N ×_X X'` is the vector bundle `𝐕(E')` of `E' = (X' ⟶ X)^*(𝒩^∨)` over `X'`
(`MMP.Chow.fibreNormalConeIso`), whose Thom class is `u_{E'}`. **Fulton's specialization step**
(the topological heart of the proof of Theorem 19.2, "Deformation") says that capping the cycle
class of the specialized cycle with the Thom class gives `g^* u ∩ cl(α)`:

  `u_{E'} ∩ cl_{𝐕(E')}((ι_* ∘ j^* ∘ C) ∩ α) = g^* u ∩ cl_{Y'}(α)`  in `H_{2m}(g⁻¹(X(ℂ)))`,

for every orientation class `u` of `f` and `α ∈ A_{m+d}(Y')`, the left side read in
`H_{2m}(g⁻¹(X(ℂ)))` through `0(X'(ℂ)) ≅ X'(ℂ) ≅ g⁻¹(X(ℂ))`. This file states it
(`MMP.Chow.SpecializationFormula`).

## Main definitions

* `MMP.Chow.normalBundleOfRegular`: the virtual normal bundle `𝒩 = 𝒞_{X/Y}^∨` of `f`.
* `MMP.Chow.fibreNormalModule`: `E' = (X' ⟶ X)^*(𝒩^∨)` on `X'`.
* `MMP.Chow.fibreNormalConeIso`: `N ×_Y Y' ≅ 𝐕(E')`.
* `MMP.Chow.specializedConeClass`: `(ι_* ∘ j^* ∘ C) ∩ α`, read on `𝐕(E')`.
* `MMP.Chow.SpecializationFormula`: the specialization step for one class `α`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.2, proof of Theorem 19.2.
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set Stacks.Chow MMP.UnderlyingSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf Stacks.AlgebraicGeometry.ReflexiveModules
open MMP.Modules

namespace MMP.Chow

attribute [local instance] fibreProductOver isOver_fibreProduct_fst isOver_fibreProduct_snd
  isComplexScheme_fibreProduct

variable {X Y Y' : Scheme.{0}} [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [Y'.Over (Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))] (g : Y' ⟶ Y)
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme X] [IsComplexScheme Y] [IsComplexScheme Y']
  [IsClosedImmersion f] [LocallyOfFiniteType g] {d : ℕ}

/-- The source of a closed immersion of complex schemes is locally Noetherian. -/
theorem isLocallyNoetherian_of_isComplexScheme : IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of ℂ))

attribute [local instance] isLocallyNoetherian_of_isComplexScheme

/-- **The normal sheaf `𝒩 = 𝒞_{X/Y}^∨` of a regular closed immersion**, as a virtual normal bundle
in the sense of Stacks 0FBQ (`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`): the one
whose class `c(X ⟶ Y, 𝒩)` is `Stacks.Chow.regularNormalGysinClass`. -/
abbrev normalBundleOfRegular (hf : IsRegularClosedImmersionOfCodim f d) :
    VirtualNormalBundle f :=
  VirtualNormalBundle.ofIsRegularImmersion f hf.isRegularImmersion

omit [Y.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))] [IsComplexScheme Y] in
/-- The normal sheaf of a regular closed immersion of codimension `d` has rank `d`. -/
theorem isFiniteLocallyFreeOfRank_normalBundleOfRegular (hf : IsRegularClosedImmersionOfCodim f d) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} (normalBundleOfRegular f hf).bundle d :=
  haveI := hf.isFiniteLocallyFreeOfRank_conormalModule
  inferInstance

attribute [local instance] isFiniteLocallyFreeOfRank_normalBundleOfRegular

/-- **`E' = (X' ⟶ X)^*(𝒩^∨)`**, on `X' = X ×_Y Y'`: the module whose vector bundle is
`N ×_Y Y'`. -/
abbrev fibreNormalModule (hf : IsRegularClosedImmersionOfCodim f d) : (pullback f g).Modules :=
  (Scheme.Modules.pullback (pullback.fst f g)).obj (dualSheaf (normalBundleOfRegular f hf).bundle)

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
/-- The module `E' = (X' ⟶ X)^*(𝒩^∨)` is quasi-coherent. -/
theorem isQuasicoherent_fibreNormalModule (hf : IsRegularClosedImmersionOfCodim f d) :
    (fibreNormalModule f g hf).IsQuasicoherent :=
  inferInstance

attribute [local instance] isQuasicoherent_fibreNormalModule

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
/-- The module `E' = (X' ⟶ X)^*(𝒩^∨)` is finite locally free of rank `d`. -/
theorem isFiniteLocallyFreeOfRank_fibreNormalModule (hf : IsRegularClosedImmersionOfCodim f d) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{0, 0, 0} (fibreNormalModule f g hf) d :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (pullback.fst f g) _ d

attribute [local instance] isFiniteLocallyFreeOfRank_fibreNormalModule

omit [IsComplexScheme Y] [LocallyOfFiniteType g] in
/-- The vector bundle `𝐕(E')` of `E' = (X' ⟶ X)^*(𝒩^∨)` is a complex scheme. -/
theorem isComplexScheme_totalSpace_fibreNormalModule (hf : IsRegularClosedImmersionOfCodim f d) :
    IsComplexScheme (totalSpace (fibreNormalModule f g hf)) :=
  isComplexScheme_totalSpace _ d

attribute [local instance] isComplexScheme_totalSpace_fibreNormalModule

/-- **`N ×_Y Y' ≅ 𝐕(E')`**: the base change along `g` of the vector bundle `N ⟶ X ⟶ Y` of the
normal sheaf is the vector bundle of `E' = (X' ⟶ X)^*(𝒩^∨)` over `X' = X ×_Y Y'`, through
`N ×_Y Y' ≅ N ×_X X'` (pasting) and `𝐕(𝒩^∨) ×_X X' ≅ 𝐕(E')` (Stacks 01CI). The projection
`N ⟶ X` is written out as `Scheme.Modules.vectorBundleToBase`, which
`Stacks.Chow.VirtualNormalBundle.projection` unfolds to. -/
def fibreNormalConeIso (hf : IsRegularClosedImmersionOfCodim f d) :
    pullback (Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle) ≫
        f) g ≅ totalSpace (fibreNormalModule f g hf) :=
  (pullbackRightPullbackFstIso f g
      (Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle))).symm ≪≫
    Scheme.Modules.vectorBundlePullbackIso (pullback.fst f g)
      (dualSheaf (normalBundleOfRegular f hf).bundle)

omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
  [g.IsOver (Spec (.of ℂ))] [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
/-- Under `N ×_Y Y' ≅ 𝐕(E')`, the projection `𝐕(E') ⟶ X'` is the projection `N ×_X X' ⟶ X'`,
precomposed with the pasting isomorphism `N ×_Y Y' ≅ N ×_X X'`. -/
theorem fibreNormalConeIso_hom_proj (hf : IsRegularClosedImmersionOfCodim f d) :
    (fibreNormalConeIso f g hf).hom ≫ proj (fibreNormalModule f g hf) =
      (pullbackRightPullbackFstIso f g (Scheme.Modules.vectorBundleToBase X
          (dualSheaf (normalBundleOfRegular f hf).bundle))).inv ≫
        pullback.snd _ (pullback.fst f g) := by
  rw [fibreNormalConeIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Scheme.Modules.vectorBundlePullbackIso_hom_vectorBundleToBase]

omit [IsComplexScheme Y] [IsComplexScheme Y'] [LocallyOfFiniteType g] in
omit [Y.Over (Spec (.of ℂ))] [Y'.Over (Spec (.of ℂ))] [f.IsOver (Spec (.of ℂ))]
    [g.IsOver (Spec (.of ℂ))] in
/-- The isomorphism `N ×_Y Y' ≅ 𝐕(E')` commutes with the structure morphisms to `Spec ℂ`, that of
`N ×_Y Y'` being `N ×_Y Y' ⟶ N ⟶ X ⟶ Spec ℂ`. -/
theorem fibreNormalConeIso_hom_comp_over (hf : IsRegularClosedImmersionOfCodim f d) :
    (fibreNormalConeIso f g hf).hom ≫ totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ) =
      pullback.fst (Scheme.Modules.vectorBundleToBase X
          (dualSheaf (normalBundleOfRegular f hf).bundle) ≫ f) g ≫
        Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle) ≫
          X ↘ Spec (.of ℂ) := by
  rw [← comp_over (proj (fibreNormalModule f g hf)) (Spec (.of ℂ)),
    ← comp_over (pullback.fst f g) (Spec (.of ℂ)), reassoc_of% (fibreNormalConeIso_hom_proj f g hf),
    ← pullback.condition_assoc, pullbackRightPullbackFstIso_inv_fst_assoc]

variable (R : Type) [CommRing R]

/-- **The specialization `(ι_* ∘ j^* ∘ C) ∩ α ∈ A_k(N ×_Y Y')` of `α ∈ A_k(Y')` to the normal
cone** (the construction of Stacks 0FBK, `Stacks.Chow.virtualNormalConeClass`), read on
`𝐕(E') ≅ N ×_Y Y'`. For `α = [V]` it is the class of the normal cone `[C_{V ∩ X'}V]`. -/
def specializedConeClass (hf : IsRegularClosedImmersionOfCodim f d) (k : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) k) :
    chowGroup (fieldChowSituation ℂ) (totalSpace (fibreNormalModule f g hf) ↘ Spec (.of ℂ)) k :=
  haveI : LocallyOfFiniteType (pullback.fst (Scheme.Modules.vectorBundleToBase X
      (dualSheaf (normalBundleOfRegular f hf).bundle) ≫ f) g ≫
        Scheme.Modules.vectorBundleToBase X (dualSheaf (normalBundleOfRegular f hf).bundle) ≫
          X ↘ Spec (.of ℂ)) := by
    rw [← fibreNormalConeIso_hom_comp_over f g hf]
    infer_instance
  chowPushforwardOfIso (fieldChowSituation ℂ) _ _ (fibreNormalConeIso f g hf).hom
    (fibreNormalConeIso_hom_comp_over f g hf) k
    ((virtualNormalConeClass (fieldChowSituation ℂ) (X ↘ Spec (.of ℂ)) (Y ↘ Spec (.of ℂ)) f
        (comp_over f _) (normalBundleOfRegular f hf)).cap g (k : ℤ)
      (chowGroupCongr (fieldChowSituation ℂ) (q := Y' ↘ Spec (.of ℂ))
        (q' := g ≫ Y ↘ Spec (.of ℂ)) (comp_over g _).symm (k : ℤ) α))

/-- **Fulton's specialization step in the proof of Theorem 19.2, for one class.** For a regular
closed immersion `f : X ⟶ Y` of codimension `d` with orientation class `u`, `g : Y' ⟶ Y` and
`α ∈ A_{m+d}(Y')`: the cap product `u_{E'} ∩ cl((ι_* ∘ j^* ∘ C) ∩ α)` of the Thom class of
`𝐕(E') = N ×_Y Y'` with the cycle class of the specialization of `α` to the normal cone
(`MMP.Chow.specializedConeClass`), read in `H_{2m}(g⁻¹(X(ℂ)))` through
`0(X'(ℂ)) ≅ X'(ℂ) ≅ g⁻¹(X(ℂ))`, is `g^* u ∩ cl_{Y'}(α)`. -/
def SpecializationFormula (hf : IsRegularClosedImmersionOfCodim f d)
    (u : cohomologyWithSupports R (ModuleCat.of R R) (TopCat.of (UnderlyingSpace ℂ Y))
      (range (UnderlyingSpace.map (K := ℂ) f)) (2 * d : ℕ)) (m : ℕ)
    (α : chowGroup (fieldChowSituation ℂ) (Y' ↘ Spec (.of ℂ)) (m + d : ℕ)) : Prop :=
  MMP.Modules.IsRegularImbeddingOrientationClass R f d u →
    borelMooreHomology.pushforward R (ModuleCat.of R R)
        (fibreSquarePointsHom (IsPullback.of_hasPullback f g).flip)
        (isProperMap_fibreSquarePointsHom (IsPullback.of_hasPullback f g).flip) (2 * m : ℕ)
        (BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul m d)
          (borelMooreHomology.pushforward R (ModuleCat.of R R)
            (zeroSectionInvHom (fibreNormalModule f g hf))
            (isProperMap_zeroSectionInvHom (fibreNormalModule f g hf)) _
            (borelMooreHomology.capProductSupport R _ isClosed_range_zeroSection
              (hasProperNeighbourhoodDeformations_range_zeroSection (fibreNormalModule f g hf))
              ((2 * d : ℕ) : ℤ) ((2 * (m + d) : ℕ) : ℤ) (thomClass R (fibreNormalModule f g hf) d)
              (chowCycleClass R (m + d) (specializedConeClass f g hf (m + d) α))))) =
      BorelMooreCross.congrDegree R _ (two_mul_add_sub_two_mul_eq m d)
        (borelMooreHomology.capProductSupportPullback R
          (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g))
          (isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) f).isClosed_range
          (hasProperNeighbourhoodDeformations_preimage_range_map f g)
          ((2 * d : ℕ) : ℤ) ((2 * (m + d) : ℕ) : ℤ) u (chowCycleClass R (m + d) α))

end MMP.Chow
