/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Chow.NormalCone.ConeClassBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalConeFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.ClosedCoverProduct
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.RegularImmersionStructureSheaf

/-!
# The class `ι_* ∘ j^* ∘ C` on the fundamental class of an arbitrary test scheme

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `i : Z ⟶ X` be a
closed immersion with a virtual normal bundle `𝒩`, with vector bundle `N`, and let
`ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)` be the class of the construction preceding Stacks 0FBK
(`Stacks.Chow.virtualNormalConeClass`). For a test scheme `t : T ⟶ X` with `dim_δ(T) ≤ n`, with
no flatness assumption, this file proves

  `(ι_* ∘ j^* ∘ C) ∩ [T]_n = κ_*[C_{Z ×_X T} T]_n`

in `A_n(N ×_X T)`, where `κ : C_{Z ×_X T} T ⟶ N ×_X T` is the closed immersion of the normal cone
of `Z ×_X T ⊆ T` into the pulled-back vector bundle, given by the comparison of normal cones
`C_{Z ×_X T} T ⟶ C_ZX` followed by `ι : C_ZX ⟶ N`, and by the inclusion of `Z ×_X T` into `T`.
This is Fulton's Proposition 5.2 in the language of Stacks: the specialization of `[T]` to the
normal cone is the class of the normal cone of the intersection.

Stacks proves the case of a flat test scheme
(`Stacks.Chow.virtualNormalConeClass_cap_fundamentalChowClass`), where `C_ZX ×_X T` is the normal
cone of `Z ×_X T` in `T`. The general case follows: the class of `(i, 𝒩)` capped on `t` is the
class of the base change `(Z ×_X T ⟶ T, g^*𝒩)` capped on the identity of `T`
(`MMP.Chow.virtualNormalConeClass_cap_baseChange`), and the identity is flat.

## Main definitions

* `MMP.Chow.normalConeToTestBundle` — the closed immersion `κ : C_{Z ×_X T} T ⟶ N ×_X T`.

## Main results

* `MMP.Chow.virtualNormalConeClass_cap_fundamentalChowClass_eq_normalCone` —
  `(ι_* ∘ j^* ∘ C) ∩ [T]_n = κ_*[C_{Z ×_X T} T]_n` for every test scheme with `dim_δ(T) ≤ n`.
* `MMP.Chow.virtualNormalConeClass_cap_cycle_integral` — the case of Fulton's Proposition 5.2
  used for Theorem 19.2: a regular closed immersion `X ⟶ Y` of codimension `d` with its normal
  bundle, a morphism `Y' ⟶ Y` and an integral closed subscheme `V ⊆ Y'` with `dim_δ(V) ≤ k`.

## References

* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Fulton, *Intersection theory*, Proposition 5.2]
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

namespace MMP.Chow

/-- Fundamental classes for equal structure morphisms are heterogeneously equal. -/
theorem fundamentalChowClass_heq_of_eq (C : ChowSituation.{u}) {T : Scheme.{u}} {s s' : T ⟶ C.S}
    [LocallyOfFiniteType s] [LocallyOfFiniteType s'] (h : s = s') (k : ℤ) :
    fundamentalChowClass C s k ≍ fundamentalChowClass C s' k := by
  subst h
  rfl

/-- Proper pushforward along two equal proper morphisms gives the same class. -/
theorem properChowPushforward_eq_of_eq (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    {u₁ u₂ : A ⟶ B} [IsProper u₁] [IsProper u₂] (h : u₁ = u₂) (hu₁ : u₁ ≫ sB = sA)
    (hu₂ : u₂ ≫ sB = sA) (k : ℤ) (z : chowGroup C sA k) :
    properChowPushforward C sA sB u₁ hu₁ k (properPushforwardDescends C _ _ _ _ _) z =
      properChowPushforward C sA sB u₂ hu₂ k (properPushforwardDescends C _ _ _ _ _) z := by
  subst h
  rfl

/-- Proper pushforward into the base changes `N ×_X T` along two equal test morphisms, along
morphisms that agree after the comparison `pullback.congrHom` of the two base changes, gives
heterogeneously equal classes. -/
theorem properChowPushforward_pullback_congrHom_heq (C : ChowSituation.{u}) {A N X T : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (P : N ⟶ X) (sN : N ⟶ C.S) {h₁ h₂ : T ⟶ X}
    (e : h₁ = h₂) [LocallyOfFiniteType (pullback.fst P h₁ ≫ sN)]
    [LocallyOfFiniteType (pullback.fst P h₂ ≫ sN)] (m : A ⟶ pullback P h₁) [IsProper m]
    [IsProper (m ≫ (pullback.congrHom rfl e).hom)]
    (hm : m ≫ (pullback.fst P h₁ ≫ sN) = sA)
    (hm' : (m ≫ (pullback.congrHom rfl e).hom) ≫ (pullback.fst P h₂ ≫ sN) = sA) (k : ℤ)
    (z : chowGroup C sA k) :
    properChowPushforward C sA (pullback.fst P h₁ ≫ sN) m hm k
        (properPushforwardDescends C _ _ _ _ _) z ≍
      properChowPushforward C sA (pullback.fst P h₂ ≫ sN) (m ≫ (pullback.congrHom rfl e).hom) hm'
        k (properPushforwardDescends C _ _ _ _ _) z := by
  subst e
  have hid : m ≫ (pullback.congrHom (rfl : P = P) (rfl : h₁ = h₁)).hom = m := by
    refine pullback.hom_ext ?_ ?_ <;> simp
  exact heq_of_eq (properChowPushforward_eq_of_eq C sA _ hid.symm hm hm' k z)

section ConeGeometry

variable {S Z X : Scheme.{u}} (sX : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
  (𝒩 : VirtualNormalBundle i) {T : Scheme.{u}} (t : T ⟶ X)

omit [IsClosedImmersion i] in
/-- `Z ×_X T` is the base change of `Z` along `t`, as the cartesian square
`Z ×_X T ⟶ T`, `Z ×_X T ⟶ Z` over `t` and `i`. -/
theorem isPullback_pullbackSnd_pullbackFst :
    IsPullback (pullback.snd i t) (pullback.fst i t) t i :=
  (IsPullback.of_hasPullback i t).flip

/-- **The closed immersion `κ : C_{Z ×_X T} T ⟶ N ×_X T`** of the normal cone of `Z ×_X T ⊆ T`
into the base change of the vector bundle `N` of `𝒩` along a test scheme `t : T ⟶ X`. It is the
inclusion `ι'` of the normal cone into the vector bundle of the base-changed virtual normal
bundle `g^*𝒩` (Stacks 0FBJ), followed by the identification `V(g^*𝒩) ≅ N ×_X T`; its components
are computed by `MMP.Chow.normalConeToTestBundle_fst` and `MMP.Chow.normalConeToTestBundle_snd`. -/
def normalConeToTestBundle :
    Stacks.Conormal.normalCone (pullback.snd i t) ⟶ pullback (𝒩.projection ≫ i) t :=
  letI 𝒩' := 𝒩.baseChange i (pullback.snd i t) (pullback.fst i t) t
    (isPullback_pullbackSnd_pullbackFst i t)
  inv (pullback.fst (𝒩'.normalConeEmbedding ≫ 𝒩'.projection ≫ pullback.snd i t) (𝟙 T)) ≫
    bivariantPushforwardBaseChange 𝒩'.normalConeEmbedding (𝒩'.projection ≫ pullback.snd i t)
      (𝟙 T) ≫
    inv (bundleTestBaseChangeIso i (pullback.snd i t) (pullback.fst i t) t
      (isPullback_pullbackSnd_pullbackFst i t) 𝒩 (𝟙 T)).hom ≫
    (pullback.congrHom rfl (Category.id_comp t)).hom

/-- The closed immersion `κ : C_{Z ×_X T} T ⟶ N ×_X T` is proper. -/
instance isProper_normalConeToTestBundle : IsProper (normalConeToTestBundle i 𝒩 t) := by
  unfold normalConeToTestBundle
  infer_instance

/-- The first component of `κ : C_{Z ×_X T} T ⟶ N ×_X T` is the comparison
`C_{Z ×_X T} T ⟶ C_ZX` of the normal cones followed by `ι : C_ZX ⟶ N`. -/
@[reassoc]
theorem normalConeToTestBundle_fst :
    normalConeToTestBundle i 𝒩 t ≫ pullback.fst (𝒩.projection ≫ i) t =
      normalConeBaseChangeMap t sX i (pullback.snd i t)
          (ker_eq_comap_of_isPullback t (isPullback_pullbackSnd_pullbackFst i t)) ≫
        𝒩.normalConeEmbedding := by
  have he := (IsIso.inv_comp_eq _).mpr (bundleTestBaseChangeIso_hom_fst i (pullback.snd i t)
    (pullback.fst i t) t (isPullback_pullbackSnd_pullbackFst i t) 𝒩 (𝟙 T)).symm
  unfold normalConeToTestBundle
  simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  rw [he, bivariantPushforwardBaseChange_fst_assoc, IsIso.inv_hom_id_assoc,
    normalConeBaseChangeMap_comp_normalConeEmbedding sX i (pullback.snd i t) (pullback.fst i t) t
      (isPullback_pullbackSnd_pullbackFst i t) 𝒩]

/-- The second component of `κ : C_{Z ×_X T} T ⟶ N ×_X T` is the projection of the normal cone
to `Z ×_X T` followed by the inclusion of `Z ×_X T` into `T`. -/
@[reassoc]
theorem normalConeToTestBundle_snd :
    normalConeToTestBundle i 𝒩 t ≫ pullback.snd (𝒩.projection ≫ i) t =
      Stacks.Conormal.normalConeToBase (pullback.snd i t) ≫ pullback.snd i t := by
  have he := (IsIso.inv_comp_eq _).mpr (bundleTestBaseChangeIso_hom_snd i (pullback.snd i t)
    (pullback.fst i t) t (isPullback_pullbackSnd_pullbackFst i t) 𝒩 (𝟙 T)).symm
  unfold normalConeToTestBundle
  simp only [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  rw [he, bivariantPushforwardBaseChange_snd, IsIso.inv_comp_eq]
  refine (Category.comp_id _).symm.trans ((pullback.condition).symm.trans ?_)
  simp only [VirtualNormalBundle.normalConeEmbedding_projection_assoc]

end ConeGeometry

section Cone

variable (C : ChowSituation.{u}) {Z X : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i]
  (hi : i ≫ sX = sZ) (𝒩 : VirtualNormalBundle i) {T : Scheme.{u}} (t : T ⟶ X)

omit [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX] in
include hi in
/-- `κ : C_{Z ×_X T} T ⟶ N ×_X T` is a morphism over the base. -/
theorem normalConeToTestBundle_comp_structure :
    normalConeToTestBundle i 𝒩 t ≫ (pullback.fst (𝒩.projection ≫ i) t ≫ 𝒩.projection ≫ sZ) =
      Stacks.Conormal.normalConeToBase (pullback.snd i t) ≫ pullback.snd i t ≫ t ≫ sX := by
  rw [← Category.assoc, normalConeToTestBundle_fst sX i 𝒩 t, Category.assoc,
    VirtualNormalBundle.normalConeEmbedding_projection_assoc, ← hi,
    ← Category.assoc (normalConeBaseChangeMap _ _ _ _ _),
    normalConeBaseChangeMap_toBase t sX i (pullback.snd i t) _ (pullback.fst i t)
      (isPullback_pullbackSnd_pullbackFst i t).w, Category.assoc, pullback.condition_assoc]

/-- **The computation on `𝟙 T ≫ t`**, for a cartesian square `Z' = Z ×_X T`: the class of
`(i, 𝒩)` caps `[T]_n` to the pushforward of `[C_{Z'}T]_n` along `C_{Z'}T ≅ C_{Z'}T ×_T T`, the
base change of `ι' : C_{Z'}T ⟶ V(g^*𝒩)` along `𝟙 T`, and `V(g^*𝒩) ×_T T ≅ N ×_X T`. -/
theorem virtualNormalConeClass_cap_eq_of_isPullback [LocallyOfFiniteType t] {Z' : Scheme.{u}}
    (i' : Z' ⟶ T) [IsClosedImmersion i'] (g : Z' ⟶ Z) (sq : IsPullback i' g t i) (n : ℤ)
    (hT : schemeDeltaDimension C (𝟙 T ≫ (t ≫ sX)) ≤ (n : EInt)) :
    haveI := locallyOfFiniteType_normalConeToBase C (t ≫ sX) i'
    (virtualNormalConeClass C sZ sX i hi 𝒩).cap (𝟙 T ≫ t) n
        (chowGroupCongr C (Category.assoc (𝟙 T) t sX).symm n
          (fundamentalChowClass C (𝟙 T ≫ (t ≫ sX)) n)) =
      properChowPushforward C (Stacks.Conormal.normalConeToBase i' ≫ i' ≫ (t ≫ sX))
        (pullback.fst (𝒩.projection ≫ i) (𝟙 T ≫ t) ≫ (𝒩.projection ≫ sZ))
        (inv (pullback.fst ((𝒩.baseChange i i' g t sq).normalConeEmbedding ≫
            (𝒩.baseChange i i' g t sq).projection ≫ i') (𝟙 T)) ≫
          bivariantPushforwardBaseChange (𝒩.baseChange i i' g t sq).normalConeEmbedding
            ((𝒩.baseChange i i' g t sq).projection ≫ i') (𝟙 T) ≫
          inv (bundleTestBaseChangeIso i i' g t sq 𝒩 (𝟙 T)).hom)
        (by
          simp only [Category.assoc]
          rw [IsIso.inv_comp_eq, ← bundleTestBaseChangeIso_hom_comp_structure C sZ sX i hi i' g t
              sq 𝒩 (i' ≫ (t ≫ sX)) rfl (𝟙 T), IsIso.inv_hom_id_assoc,
            bivariantPushforwardBaseChange_comp_structure
              (by rw [VirtualNormalBundle.normalConeEmbedding_projection_assoc])])
        (n - 0) (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C (Stacks.Conormal.normalConeToBase i' ≫ i' ≫ (t ≫ sX))
          (n - 0)) := by
  have := locallyOfFiniteType_normalConeToBase C (t ≫ sX) i'
  have hE := bundleTestBaseChangeIso_hom_comp_structure C sZ sX i hi i' g t sq 𝒩 _ rfl (𝟙 T)
  have hbc := virtualNormalConeClass_cap_baseChange C sZ sX i hi i' g t sq 𝒩
    (i' ≫ (t ≫ sX)) rfl (𝟙 T) n (fundamentalChowClass C (𝟙 T ≫ (t ≫ sX)) n)
  rw [virtualNormalConeClass_cap_fundamentalChowClass C (i' ≫ (t ≫ sX)) (t ≫ sX) i' rfl
    (𝒩.baseChange i i' g t sq) (𝟙 T) n hT] at hbc
  have hp : inv (pullback.fst ((𝒩.baseChange i i' g t sq).normalConeEmbedding ≫
        (𝒩.baseChange i i' g t sq).projection ≫ i') (𝟙 T)) ≫
      (pullback.fst ((𝒩.baseChange i i' g t sq).normalConeEmbedding ≫
        (𝒩.baseChange i i' g t sq).projection ≫ i') (𝟙 T) ≫
          Stacks.Conormal.normalConeToBase i' ≫ i' ≫ (t ≫ sX)) =
      Stacks.Conormal.normalConeToBase i' ≫ i' ≫ (t ≫ sX) := IsIso.inv_hom_id_assoc _ _
  rw [← chowPushforwardOfIso_fundamentalChowClass C _ _ _ hp (n - 0),
    ← properChowPushforward_eq_chowPushforwardOfIso C _ _ _ hp (n - 0)
      (properPushforwardDescends C _ _ _ _ _)] at hbc
  have hinv := chowPushforwardOfIso_inv_comp C _ _ (bundleTestBaseChangeIso i i' g t sq 𝒩 (𝟙 T)).hom
    hE (n - 0) ((virtualNormalConeClass C sZ sX i hi 𝒩).cap (𝟙 T ≫ t) n
      (chowGroupCongr C (Category.assoc (𝟙 T) t sX).symm n
        (fundamentalChowClass C (𝟙 T ≫ (t ≫ sX)) n)))
  rw [← hbc] at hinv
  rw [← hinv]
  exact chowPushforwardOfIso_properChowPushforward_properChowPushforward C _ _ _ _ _ _ _ _
    rfl _ _ _ _ _ _ _ _ _

/-- **`(ι_* ∘ j^* ∘ C) ∩ [T]_n = κ_*[C_{Z ×_X T} T]_n`, with no flatness.** For a closed immersion
`i : Z ⟶ X` with a virtual normal bundle `𝒩` and any test scheme `t : T ⟶ X` locally of finite
type with `dim_δ(T) ≤ n`, the class `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ X)` of the construction preceding
Stacks 0FBK caps the fundamental class of `T` to the pushforward, along the closed immersion
`κ : C_{Z ×_X T} T ⟶ N ×_X T` (`MMP.Chow.normalConeToTestBundle`), of the fundamental class of
the normal cone of `Z ×_X T` in `T`.

This is Fulton's Proposition 5.2: the specialization of `[T]` is the class of the normal cone of
the intersection. The class of `(i, 𝒩)` on `t` is the class of the base change
`(Z ×_X T ⟶ T, g^*𝒩)` on the identity of `T` (`MMP.Chow.virtualNormalConeClass_cap_baseChange`),
which is flat, so the flat case of the proof of Stacks 0FBM applies
(`Stacks.Chow.virtualNormalConeClass_cap_fundamentalChowClass`). -/
theorem virtualNormalConeClass_cap_fundamentalChowClass_eq_normalCone [LocallyOfFiniteType t]
    (n : ℤ) (hT : schemeDeltaDimension C (t ≫ sX) ≤ (n : EInt)) :
    haveI := locallyOfFiniteType_normalConeToBase C (t ≫ sX) (pullback.snd i t)
    (virtualNormalConeClass C sZ sX i hi 𝒩).cap t n (fundamentalChowClass C (t ≫ sX) n) =
      properChowPushforward C
        (Stacks.Conormal.normalConeToBase (pullback.snd i t) ≫ pullback.snd i t ≫ t ≫ sX)
        (pullback.fst (𝒩.projection ≫ i) t ≫ 𝒩.projection ≫ sZ)
        (normalConeToTestBundle i 𝒩 t)
        (normalConeToTestBundle_comp_structure C sZ sX i hi 𝒩 t)
        (n - 0) (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C
          (Stacks.Conormal.normalConeToBase (pullback.snd i t) ≫ pullback.snd i t ≫ t ≫ sX)
          (n - 0)) := by
  have := locallyOfFiniteType_normalConeToBase C (t ≫ sX) (pullback.snd i t)
  have hx : fundamentalChowClass C (t ≫ sX) n ≍
      chowGroupCongr C (Category.assoc (𝟙 T) t sX).symm n
        (fundamentalChowClass C (𝟙 T ≫ (t ≫ sX)) n) :=
    (fundamentalChowClass_heq_of_eq C (Category.id_comp (t ≫ sX)).symm n).trans
      (chowGroupCongr_heq C _ n _).symm
  refine eq_of_heq ((BivariantClass.cap_heq_of_eq (m' := 𝟙 T ≫ t) _ (Category.id_comp t).symm n
    hx).trans ?_)
  rw [virtualNormalConeClass_cap_eq_of_isPullback C sZ sX i hi 𝒩 t (pullback.snd i t)
    (pullback.fst i t) (isPullback_pullbackSnd_pullbackFst i t) n (by simpa using hT)]
  exact properChowPushforward_pullback_congrHom_heq C _ (𝒩.projection ≫ i) (𝒩.projection ≫ sZ)
    (Category.id_comp t) _ _ _ (n - 0) _

end Cone

/-! ### Fulton's Proposition 5.2 on an integral subscheme -/

/-- **Fulton's Proposition 5.2 on Stacks Chow groups, for Theorem 19.2.** Let `f : X ⟶ Y` be a
regular closed immersion of codimension `d`, with normal bundle `N = 𝐕(𝒞_{X/Y}^∨)`
(`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`), let `g : Y' ⟶ Y` be a morphism and let
`v : V ⟶ Y'` be an integral closed subscheme with `dim_δ(V) ≤ k`, both locally of finite type.
Then the class `ι_* ∘ j^* ∘ C ∈ A⁰(N ⟶ Y)` of the construction preceding Stacks 0FBK, capped
along `v ≫ g` with the cycle class `[V]_k`, is the pushforward to `N ×_Y V` of the class of the
normal cone `C_{V ∩ X} V` of `V ∩ X = X ×_Y V` in `V`, along the closed immersion `κ` of
`MMP.Chow.normalConeToTestBundle`.

This is the special case `t = v ≫ g` of
`MMP.Chow.virtualNormalConeClass_cap_fundamentalChowClass_eq_normalCone`; neither the regularity
of `f` nor the integrality of `V` is used. -/
theorem virtualNormalConeClass_cap_cycle_integral (C : ChowSituation.{u}) {X Y Y' V : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsClosedImmersion f] (hf : f ≫ sY = sX) {d : ℕ}
    (hreg : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsRegularClosedImmersionOfCodim f d)
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] (v : V ⟶ Y') [IsClosedImmersion v] [IsIntegral V]
    (k : ℤ) (hV : schemeDeltaDimension C (v ≫ g ≫ sY) ≤ (k : EInt)) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI := locallyOfFiniteType_normalConeToBase C ((v ≫ g) ≫ sY) (pullback.snd f (v ≫ g))
    (virtualNormalConeClass C sX sY f hf
        (VirtualNormalBundle.ofIsRegularImmersion f hreg.isRegularImmersion)).cap (v ≫ g) k
        (fundamentalChowClass C ((v ≫ g) ≫ sY) k) =
      properChowPushforward C
        (Stacks.Conormal.normalConeToBase (pullback.snd f (v ≫ g)) ≫ pullback.snd f (v ≫ g) ≫
          (v ≫ g) ≫ sY)
        (pullback.fst ((VirtualNormalBundle.ofIsRegularImmersion f
            hreg.isRegularImmersion).projection ≫ f) (v ≫ g) ≫
          (VirtualNormalBundle.ofIsRegularImmersion f hreg.isRegularImmersion).projection ≫ sX)
        (normalConeToTestBundle f
          (VirtualNormalBundle.ofIsRegularImmersion f hreg.isRegularImmersion) (v ≫ g))
        (normalConeToTestBundle_comp_structure C sX sY f hf _ (v ≫ g)) (k - 0)
        (properPushforwardDescends C _ _ _ _ _)
        (fundamentalChowClass C
          (Stacks.Conormal.normalConeToBase (pullback.snd f (v ≫ g)) ≫ pullback.snd f (v ≫ g) ≫
            (v ≫ g) ≫ sY) (k - 0)) :=
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  virtualNormalConeClass_cap_fundamentalChowClass_eq_normalCone C sX sY f hf
    (VirtualNormalBundle.ofIsRegularImmersion f hreg.isRegularImmersion) (v ≫ g) k
    (by simpa only [Category.assoc] using hV)

end MMP.Chow

end
