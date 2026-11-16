/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClassBaseChange

/-!
# The class `ι_* ∘ j^* ∘ C` under base change

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a
closed immersion with a virtual normal bundle `𝒩`, and let `Z' = Z ×_X X'` be a cartesian square
with `f : X' ⟶ X` locally of finite type, `i' : Z' ⟶ X'` and the base-changed virtual normal bundle
`g^*𝒩` of Stacks 0FBJ. The class `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)` of the construction preceding
Stacks 0FBK (`Stacks.Chow.virtualNormalConeClass`) is compatible with base change: on a test
scheme `t : T ⟶ X'` the class of `(i', g^*𝒩)` caps as the class of `(i, 𝒩)` does on `t ≫ f`,
through the identification `V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T`.

This is the computation at the heart of the proof of the base-change clause of Stacks 0FBK
(`Stacks.Chow.virtualNormalGysinClass_cap_baseChange`), read before the inverse of flat pullback
to the vector bundle is applied. It is no restriction on `f`: neither flatness nor anything else.

## Main results

* `MMP.Chow.bundleTestBaseChangeIso_hom_comp_structure` — the identification
  `V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T` lies over the base.
* `MMP.Chow.virtualNormalConeClass_cap_baseChange` — the base-change compatibility of
  `ι_* ∘ j^* ∘ C` on cap operations.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
* [Stacks Project, Tag 0GUH](https://stacks.math.columbia.edu/tag/0GUH)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace MMP.Chow

variable (C : ChowSituation.{u}) {Z X Z' X' : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (i' : Z' ⟶ X') [IsClosedImmersion i'] (g : Z' ⟶ Z)
  (f : X' ⟶ X) [LocallyOfFiniteType f] (sq : IsPullback i' g f i) (𝒩 : VirtualNormalBundle i)

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] [LocallyOfFiniteType f] in
include hi in
/-- The identification `V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T` of a test scheme `t : T ⟶ X'` lies over
the base. -/
theorem bundleTestBaseChangeIso_hom_comp_structure (sZ' : Z' ⟶ C.S)
    (hi' : i' ≫ (f ≫ sX) = sZ') {T : Scheme.{u}} (t : T ⟶ X') :
    (bundleTestBaseChangeIso i i' g f sq 𝒩 t).hom ≫
        (pullback.fst ((𝒩.baseChange i i' g f sq).projection ≫ i') t ≫
          ((𝒩.baseChange i i' g f sq).projection ≫ sZ')) =
      pullback.fst (𝒩.projection ≫ i) (t ≫ f) ≫ (𝒩.projection ≫ sZ) := by
  subst hi'
  have hw := (𝒩.isPullback_baseChangeTotalSpaceMap i i' g f sq).w
  rw [← hi, ← Category.assoc i', sq.w, Category.assoc, ← Category.assoc
    (𝒩.baseChange i i' g f sq).projection, ← hw]
  simp only [Category.assoc]
  rw [bundleTestBaseChangeIso_hom_fst_assoc]

/-- **`ι_* ∘ j^* ∘ C` is compatible with base change.** For a cartesian square `Z' = Z ×_X X'`
and a test scheme `t : T ⟶ X'`, the class `ι'_* ∘ j'^* ∘ C'` of `(i', g^*𝒩)` caps `α` as
`ι_* ∘ j^* ∘ C` of `(i, 𝒩)` does on `t ≫ f`, through `V(𝒩) ×_X T ≅ V(g^*𝒩) ×_{X'} T`.

The proof is that of the base-change clause of Stacks 0FBK: the class at infinity `C` restricts
to `C'` (Stacks 0GUH and 0FAQ), flat pullback to the open `C_ZX ×_X T` of `W_∞ ×_X T` commutes
with proper pushforward (Stacks 02RG, `C_{Z'}X' ×_{X'} T` being the inverse image of
`C_ZX ×_X T`), and the closed immersions `ι` are compatible with base change. -/
theorem virtualNormalConeClass_cap_baseChange (sZ' : Z' ⟶ C.S) [LocallyOfFiniteType sZ']
    (hi' : i' ≫ (f ≫ sX) = sZ') {T : Scheme.{u}} (t : T ⟶ X') [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ (f ≫ sX)) k) :
    (virtualNormalConeClass C sZ' (f ≫ sX) i' hi' (𝒩.baseChange i i' g f sq)).cap t k α =
      chowPushforwardOfIso C (pullback.fst (𝒩.projection ≫ i) (t ≫ f) ≫ (𝒩.projection ≫ sZ))
        (pullback.fst ((𝒩.baseChange i i' g f sq).projection ≫ i') t ≫
          ((𝒩.baseChange i i' g f sq).projection ≫ sZ'))
        (bundleTestBaseChangeIso i i' g f sq 𝒩 t).hom
        (bundleTestBaseChangeIso_hom_comp_structure C sZ sX i hi i' g f sq 𝒩 sZ' hi' t) (k - 0)
        ((virtualNormalConeClass C sZ sX i hi 𝒩).cap (t ≫ f) k
          (chowGroupCongr C (Category.assoc t f sX).symm k α)) := by
  subst hi'
  set 𝒩' := 𝒩.baseChange i i' g f sq
  have hE := bundleTestBaseChangeIso_hom_comp_structure C sZ sX i hi i' g f sq 𝒩 _ rfl t
  have := locallyOfFiniteType_normalConeToBase C sX i
  have := locallyOfFiniteType_normalConeToBase C (f ≫ sX) i'
  have hNF := virtualNormalConeClass_cap_heq C sZ sX i hi 𝒩 (t ≫ f) k
    (chowGroupCongr C (Category.assoc t f sX).symm k α)
  have hNF' := virtualNormalConeClass_cap_heq C (i' ≫ (f ≫ sX)) (f ≫ sX) i' rfl 𝒩' t k α
  refine eq_of_heq (HEq.symm ?_)
  refine (chowPushforwardOfIso_heq_congr C _ _ _ hE (by ring) _ _ hNF).trans
    (HEq.trans ?_ hNF'.symm)
  apply heq_of_eq
  rw [eq_of_heq (gysinAtInfinityClass_cap_heq_blowupAtInfinityComap C sX f i.ker i'.ker
    (ker_eq_comap_of_isPullback f sq) t k α)]
  have hsq := isPullback_normalConeTestBaseChange sX i i' g f sq 𝒩 t
  have : IsProper (normalConeTestBaseChange sX i i' g f sq 𝒩 t) :=
    MorphismProperty.of_isPullback hsq inferInstance
  rw [flatPullbackChow_properChowPushforward_of_isProper C
    (modificationInfinityBaseChangeOver (f ≫ sX)
      (blowupAtInfinityToProjectiveLineProduct i'.ker (f ≫ sX)) t)
    (modificationInfinityBaseChangeOver sX (blowupAtInfinityToProjectiveLineProduct i.ker sX)
      (t ≫ f))
    (pullback.fst (𝒩'.normalConeEmbedding ≫ 𝒩'.projection ≫ i') t ≫
      (Stacks.Conormal.normalConeToBase i' ≫ i' ≫ (f ≫ sX)))
    (pullback.fst (𝒩.normalConeEmbedding ≫ 𝒩.projection ≫ i) (t ≫ f) ≫
      (Stacks.Conormal.normalConeToBase i ≫ sZ))
    (blowupAtInfinityFibreTestComap sX f i.ker i'.ker (ker_eq_comap_of_isPullback f sq) t)
    (normalConeTestMap sX i 𝒩 (t ≫ f))
    (normalConeTestMap (f ≫ sX) i' 𝒩' t)
    (normalConeTestBaseChange sX i i' g f sq 𝒩 t) hsq
    (by simp [modificationInfinityBaseChangeOver, blowupAtInfinityComap_toBase_assoc])
    (normalConeTestMap_comp_structureMorphism sZ sX i hi 𝒩 (t ≫ f))
    (normalConeTestMap_comp_structureMorphism (i' ≫ (f ≫ sX)) (f ≫ sX) i' rfl 𝒩' t) 0
    (relativeDimension_of_isOpenImmersion _) (k - 0)]
  exact chowPushforwardOfIso_properChowPushforward_properChowPushforward C _ _ _ _ _ _ _ _
    (normalConeTestBaseChange_comp_bivariantPushforwardBaseChange sX i i' g f sq 𝒩 t)
    _ _ _ _ _ _ _ _ _

end MMP.Chow

end
