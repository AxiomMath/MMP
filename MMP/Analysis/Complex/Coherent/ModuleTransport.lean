module

public import MMP.Analysis.Complex.Submanifold
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import MMP.Topology.Sheaves.OpensMapCocontinuous
public import MMP.Algebra.Category.ModuleCat.Sheaf.FiniteTypePushforward
public import MMP.CategoryTheory.Sites.OverPost

/-!
# Sheaves of modules on an open subset of an open set of `ℂⁿ`

Let `D ⊆ ℂⁿ` be open and `W` an open subset of `D`. The restriction `𝒮|_W` of a sheaf of
`𝒪_D`-modules lives on the slice site `Over W`, while the theorems about coherent sheaves are
stated for modules over the sheaf `𝒪_{W'}` of holomorphic functions of a complex manifold, here
the image `W' ⊆ ℂⁿ` of `W`. This file identifies the two settings.

The site `Opens W'` is equivalent to `Over W` (through the homeomorphism `W ≃ₜ W'` and
`TopologicalSpace.Opens.overEquivalence`), and along this equivalence the sheaf of rings
`𝒪_D|_W` corresponds to `𝒪_{W'}`: a function on an open subset of `W'` is holomorphic exactly
when its composite with the identification of the corresponding open subset of `D` is. The
pushforward of sheaves of modules along these isomorphisms of sheaves of rings is then an
equivalence between sheaves of `𝒪_D|_W`-modules and sheaves of `𝒪_{W'}`-modules, which does not
change the groups of sections.

## Main definitions

* `MMP.Analytic.imageOpens W`: the image `W' ⊆ ℂⁿ` of an open subset `W` of `D`.
* `MMP.Analytic.imageOverEquivalence W`: the equivalence of sites `Opens W' ≌ Over W`.
* `MMP.Analytic.imageRingHom W`, `MMP.Analytic.imageRingInv W`: the morphisms of sheaves of
  rings between `𝒪_{W'}` and `𝒪_D|_W` along this equivalence.
* `MMP.Analytic.imageModuleEquivalence W`: the equivalence between sheaves of `𝒪_D|_W`-modules
  and sheaves of `𝒪_{W'}`-modules.

## Main results

* `imageOverEquivalence W` is an equivalence of sites: both legs are cocontinuous and its functor
  is a dense subsite (instances).
* `MMP.Analytic.isFiniteType_imageModuleEquivalence_functor_obj`: the transport of a module of
  finite type is of finite type; `isFiniteType_imageModuleEquivalence_functor_obj_over` for the
  transport of a restriction `T|_W`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped Manifold ContDiff

namespace MMP.Analytic

variable {n : ℕ} {D : Opens (EuclideanSpace ℂ (Fin n))}

/-- The image in `ℂⁿ` of an open subset `W` of an open set `D ⊆ ℂⁿ`. -/
def imageOpens (W : Opens (TopCat.of D)) : Opens (EuclideanSpace ℂ (Fin n)) :=
  ⟨Subtype.val '' (W : Set D), D.isOpenEmbedding'.isOpenMap _ W.isOpen⟩

/-- A point of `ℂⁿ` lies in `imageOpens W` iff it is a point of `W`. -/
lemma mem_imageOpens {W : Opens (TopCat.of D)} {z : EuclideanSpace ℂ (Fin n)} :
    z ∈ imageOpens W ↔ ∃ x : D, x ∈ W ∧ (x : EuclideanSpace ℂ (Fin n)) = z := Iff.rfl

/-- A point of `imageOpens W` lies in `D`. -/
lemma mem_of_mem_imageOpens {W : Opens (TopCat.of D)} {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ imageOpens W) : z ∈ D := by
  obtain ⟨x, -, rfl⟩ := hz
  exact x.2

/-- A point of `imageOpens W`, viewed as a point of `D`, lies in `W`. -/
lemma mem_of_mem_imageOpens' {W : Opens (TopCat.of D)} {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ imageOpens W) : (⟨z, mem_of_mem_imageOpens hz⟩ : D) ∈ W := by
  obtain ⟨x, hx, rfl⟩ := hz
  exact hx

/-- The homeomorphism between an open subset `W` of `D` and its image in `ℂⁿ`. -/
def imageHomeomorph (W : Opens (TopCat.of D)) : W ≃ₜ imageOpens W where
  toFun x := ⟨x.1.1, x.1, x.2, rfl⟩
  invFun y := ⟨⟨y.1, mem_of_mem_imageOpens y.2⟩, mem_of_mem_imageOpens' y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The equivalence of sites `Opens W' ≌ Over W` for the image `W' ⊆ ℂⁿ` of `W`. -/
def imageOverEquivalence (W : Opens (TopCat.of D)) :
    Opens (TopCat.of (imageOpens W)) ≌ Over W :=
  (Opens.mapMapIso (X := TopCat.of W) (Y := TopCat.of (imageOpens W))
    (TopCat.isoOfHomeo (imageHomeomorph W))).trans W.overEquivalence.symm

/-- A point `x` of `D` lies in the open set of `D` corresponding to `V ⊆ W'` iff `x` lies in `W'`
and, as a point of `W'`, in `V`. -/
lemma imageOverEquivalence_functor_obj_left (W : Opens (TopCat.of D))
    (V : Opens (TopCat.of (imageOpens W))) (x : D) :
    x ∈ ((imageOverEquivalence W).functor.obj V).left ↔
      ∃ h : (x : EuclideanSpace ℂ (Fin n)) ∈ imageOpens W, ⟨x.1, h⟩ ∈ V := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, y.2, rfl⟩, hy⟩
  · rintro ⟨h, hV⟩
    exact ⟨⟨x, mem_of_mem_imageOpens' h⟩, hV, rfl⟩

/-- A point `y` of `W'` lies in the open set of `W'` corresponding to `X` iff `y`, as a point of
`D`, lies in `X`. -/
lemma imageOverEquivalence_inverse_obj (W : Opens (TopCat.of D)) (X : Over W)
    (y : imageOpens W) :
    y ∈ (imageOverEquivalence W).inverse.obj X ↔
      (⟨y.1, mem_of_mem_imageOpens y.2⟩ : D) ∈ X.left := Iff.rfl

/-- The functor of `imageOverEquivalence W` is continuous. -/
instance (W : Opens (TopCat.of D)) : (imageOverEquivalence W).functor.IsContinuous
    (Opens.grothendieckTopology (TopCat.of (imageOpens W)))
    ((Opens.grothendieckTopology (TopCat.of D)).over W) := by
  have : (Opens.mapMapIso (X := TopCat.of W) (Y := TopCat.of (imageOpens W))
      (TopCat.isoOfHomeo (imageHomeomorph W))).functor.IsContinuous
      (Opens.grothendieckTopology (TopCat.of (imageOpens W)))
      (Opens.grothendieckTopology (TopCat.of W)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
      (coverPreserving_opens_map _)
  exact Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (TopCat.of W)) _

/-- The inverse of `imageOverEquivalence W` is continuous. -/
instance (W : Opens (TopCat.of D)) : (imageOverEquivalence W).inverse.IsContinuous
    ((Opens.grothendieckTopology (TopCat.of D)).over W)
    (Opens.grothendieckTopology (TopCat.of (imageOpens W))) := by
  have : (Opens.mapMapIso (X := TopCat.of W) (Y := TopCat.of (imageOpens W))
      (TopCat.isoOfHomeo (imageHomeomorph W))).inverse.IsContinuous
      (Opens.grothendieckTopology (TopCat.of W))
      (Opens.grothendieckTopology (TopCat.of (imageOpens W))) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map _)
      (coverPreserving_opens_map _)
  exact Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology (TopCat.of W)) _

/-- The functor of `imageOverEquivalence W` is cocontinuous. -/
instance (W : Opens (TopCat.of D)) : (imageOverEquivalence W).functor.IsCocontinuous
    (Opens.grothendieckTopology (TopCat.of (imageOpens W)))
    ((Opens.grothendieckTopology (TopCat.of D)).over W) :=
  haveI := MMP.isCocontinuous_mapMapIso_functor (X := TopCat.of W)
    (Y := TopCat.of (imageOpens W)) (TopCat.isoOfHomeo (imageHomeomorph W))
  isCocontinuous_comp _ _ _ (Opens.grothendieckTopology (TopCat.of W))

/-- The inverse of `imageOverEquivalence W` is cocontinuous. -/
instance (W : Opens (TopCat.of D)) : (imageOverEquivalence W).inverse.IsCocontinuous
    ((Opens.grothendieckTopology (TopCat.of D)).over W)
    (Opens.grothendieckTopology (TopCat.of (imageOpens W))) :=
  haveI := MMP.isCocontinuous_mapMapIso_inverse (X := TopCat.of W)
    (Y := TopCat.of (imageOpens W)) (TopCat.isoOfHomeo (imageHomeomorph W))
  isCocontinuous_comp _ _ _ (Opens.grothendieckTopology (TopCat.of W))

/-- The functor of `imageOverEquivalence W` is a dense subsite. -/
instance (W : Opens (TopCat.of D)) : (imageOverEquivalence W).functor.IsDenseSubsite
    (Opens.grothendieckTopology (TopCat.of (imageOpens W)))
    ((Opens.grothendieckTopology (TopCat.of D)).over W) :=
  Equivalence.isDenseSubsite_functor_of_isCocontinuous _ _ _

/-- The inverse of `imageOverEquivalence W` is a dense subsite. -/
instance (W : Opens (TopCat.of D)) : (imageOverEquivalence W).inverse.IsDenseSubsite
    ((Opens.grothendieckTopology (TopCat.of D)).over W)
    (Opens.grothendieckTopology (TopCat.of (imageOpens W))) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- A map between open subsets of open sets of `ℂⁿ` which commutes with the inclusions into
`ℂⁿ` is holomorphic. -/
lemma contMDiff_of_val_val {D₁ D₂ : Opens (EuclideanSpace ℂ (Fin n))}
    {A : Opens (TopCat.of D₁)} {B : Opens (TopCat.of D₂)} (θ : A → B)
    (h : ∀ x, ((θ x : D₂) : EuclideanSpace ℂ (Fin n)) = ((x : D₁) : EuclideanSpace ℂ (Fin n))) :
    ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ θ := by
  rw [← ContMDiff.subtypeVal_comp_iff B, ← ContMDiff.subtypeVal_comp_iff D₂]
  have : (Subtype.val ∘ Subtype.val ∘ θ : A → EuclideanSpace ℂ (Fin n)) =
      Subtype.val ∘ Subtype.val := funext h
  rw [this]
  exact contMDiff_subtype_val.comp contMDiff_subtype_val

/-- Precomposition with a holomorphic map, as a ring homomorphism of holomorphic functions. -/
def precompRingHom {D₁ D₂ : Opens (EuclideanSpace ℂ (Fin n))}
    {A : Opens (TopCat.of D₁)} {B : Opens (TopCat.of D₂)} (θ : A → B)
    (hθ : ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ∞ θ) :
    𝒪[n, D₂].presheaf.obj (op B) →+* 𝒪[n, D₁].presheaf.obj (op A) where
  toFun g := ⟨fun x => g (θ x),
    (show ContMDiff 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) 𝓘(ℂ) ∞ (g : B → ℂ) from g.2).comp hθ⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- `precompRingHom θ hθ g` sends `x` to `g (θ x)`. -/
@[simp]
lemma precompRingHom_apply {D₁ D₂ : Opens (EuclideanSpace ℂ (Fin n))}
    {A : Opens (TopCat.of D₁)} {B : Opens (TopCat.of D₂)} (θ : A → B) (hθ) (g) (x : A) :
    precompRingHom θ hθ g x = g (θ x) := rfl

/-! ### The sheaves of rings -/

variable (W : Opens (TopCat.of D))

/-- The point of `V ⊆ W'` corresponding to a point of the matching open subset of `D`. -/
def imagePoint (V : Opens (TopCat.of (imageOpens W)))
    (x : ((imageOverEquivalence W).functor.obj V).left) : V :=
  ⟨⟨x.1.1, x.1, ((imageOverEquivalence W).functor.obj V).hom.le x.2, rfl⟩,
    ((imageOverEquivalence_functor_obj_left W V x.1).1 x.2).2⟩

/-- The point of `X ⊆ D` corresponding to a point of the matching open subset of `W'`. -/
def imagePointInv (X : Over W) (y : (imageOverEquivalence W).inverse.obj X) : X.left :=
  ⟨⟨y.1.1, mem_of_mem_imageOpens y.1.2⟩, (imageOverEquivalence_inverse_obj W X y.1).1 y.2⟩

/-- The morphism of sheaves of rings `𝒪_{W'} ⟶ 𝒪_D|_W` along `Opens W' ≌ Over W`. -/
def imageRingHom : holomorphicRingCatSheaf n (imageOpens W) ⟶
    ((imageOverEquivalence W).functor.sheafPushforwardContinuous RingCat.{0}
      (Opens.grothendieckTopology (TopCat.of (imageOpens W)))
      ((Opens.grothendieckTopology (TopCat.of D)).over W)).obj
      ((holomorphicRingCatSheaf n D).over W) where
  hom :=
    { app := fun V => RingCat.ofHom (precompRingHom (imagePoint W V.unop)
        (contMDiff_of_val_val _ fun _ => rfl))
      naturality := fun _ _ _ => by ext; rfl }

/-- The morphism of sheaves of rings `𝒪_D|_W ⟶ 𝒪_{W'}` along `Over W ≌ Opens W'`. -/
def imageRingInv : (holomorphicRingCatSheaf n D).over W ⟶
    ((imageOverEquivalence W).inverse.sheafPushforwardContinuous RingCat.{0}
      ((Opens.grothendieckTopology (TopCat.of D)).over W)
      (Opens.grothendieckTopology (TopCat.of (imageOpens W)))).obj
      (holomorphicRingCatSheaf n (imageOpens W)) where
  hom :=
    { app := fun X => RingCat.ofHom (precompRingHom (imagePointInv W X.unop)
        (contMDiff_of_val_val _ fun _ => rfl))
      naturality := fun _ _ _ => by ext; rfl }

/-! ### The equivalence of categories of sheaves of modules -/

/-- Sheaves of `𝒪_D|_W`-modules are sheaves of `𝒪_{W'}`-modules, for the image `W' ⊆ ℂⁿ` of an
open subset `W` of `D`. The functor does not change sections:
`((imageModuleEquivalence W).functor.obj M).val.obj (op V) = M.val.obj (op (e V))` for the
equivalence of sites `e = imageOverEquivalence W`. -/
def imageModuleEquivalence :
    SheafOfModules.{0} ((holomorphicRingCatSheaf n D).over W) ≌
      SheafOfModules.{0} (holomorphicRingCatSheaf n (imageOpens W)) :=
  SheafOfModules.pushforwardPushforwardEquivalence (imageOverEquivalence W) (imageRingHom W)
    (imageRingInv W) (by ext X g; rfl) (by ext V g; rfl)

/-- The functor `imageModuleEquivalence W` does not change sections. -/
lemma imageModuleEquivalence_functor_obj_val_obj
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n D).over W))
    (V : Opens (TopCat.of (imageOpens W))) :
    (((imageModuleEquivalence W).functor.obj M).val.obj (op V) : Type) =
      M.val.obj (op ((imageOverEquivalence W).functor.obj V)) := rfl

/-- The inverse of `imagePoint W V`. -/
def imagePointSymm (V : Opens (TopCat.of (imageOpens W))) (y : V) :
    ((imageOverEquivalence W).functor.obj V).left :=
  ⟨⟨y.1.1, mem_of_mem_imageOpens y.1.2⟩,
    (imageOverEquivalence_functor_obj_left W V _).2 ⟨y.1.2, y.2⟩⟩

/-- The sheaf of rings `𝒪_{W'}`, as a module over itself, is the transport of `𝒪_D|_W`. -/
def imageUnitIso : SheafOfModules.unit (holomorphicRingCatSheaf n (imageOpens W)) ≅
    (imageModuleEquivalence W).functor.obj (SheafOfModules.unit _) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk
    (fun V => LinearEquiv.toModuleIso
      (show (SheafOfModules.unit (holomorphicRingCatSheaf n (imageOpens W))).val.obj V ≃ₗ[
          (holomorphicRingCatSheaf n (imageOpens W)).obj.obj V]
          ((imageModuleEquivalence W).functor.obj (SheafOfModules.unit _)).val.obj V from
      { toFun := precompRingHom (imagePoint W V.unop) (contMDiff_of_val_val _ fun _ => rfl)
        invFun := precompRingHom (imagePointSymm W V.unop) (contMDiff_of_val_val _ fun _ => rfl)
        map_add' := map_add _
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }))
    (fun _ _ _ => rfl)

/-- `imageModuleEquivalence W` sends the free `𝒪_D|_W`-module on `I` to the free
`𝒪_{W'}`-module on `I`. -/
def imageFreeIso (I : Type) :
    SheafOfModules.free (R := holomorphicRingCatSheaf n (imageOpens W)) I ≅
      (imageModuleEquivalence W).functor.obj (SheafOfModules.free I) :=
  SheafOfModules.mapFreeIso _ I (imageUnitIso W)

/-- The ring map `imageRingHom W` is an isomorphism: its inverse is precomposition with
`imagePointSymm`. -/
instance : IsIso (imageRingHom W) :=
  ⟨⟨{ hom :=
      { app := fun V => RingCat.ofHom (precompRingHom (imagePointSymm W V.unop)
          (contMDiff_of_val_val _ fun _ => rfl))
        naturality := fun _ _ _ => by ext; rfl } },
    Sheaf.hom_ext (by ext; rfl), Sheaf.hom_ext (by ext; rfl)⟩⟩

/-- The transport of a sheaf of modules of finite type along `imageModuleEquivalence W` is of
finite type. -/
theorem isFiniteType_imageModuleEquivalence_functor_obj
    (M : SheafOfModules.{0} ((holomorphicRingCatSheaf n D).over W)) [M.IsFiniteType] :
    ((imageModuleEquivalence W).functor.obj M).IsFiniteType := by
  have := fun X => MMP.isDenseSubsite_overPost
    (Opens.grothendieckTopology (TopCat.of (imageOpens W)))
    ((Opens.grothendieckTopology (TopCat.of D)).over W) (imageOverEquivalence W) X
  have h0 : IsIso (imageRingHom W) := inferInstance
  exact MMP.isFiniteType_pushforward_of_isLeftAdjoint (imageOverEquivalence W).functor
    (imageRingHom W) (imageUnitIso W).symm (hφ := h0)

/-- The transport of the restriction `T|_W` of a sheaf of `𝒪_D`-modules of finite type is of
finite type. -/
theorem isFiniteType_imageModuleEquivalence_functor_obj_over
    (T : SheafOfModules.{0} (holomorphicRingCatSheaf n D)) [T.IsFiniteType] :
    ((imageModuleEquivalence W).functor.obj (T.over W)).IsFiniteType :=
  haveI := MMP.isFiniteType_over W T
  isFiniteType_imageModuleEquivalence_functor_obj W (T.over W)

end MMP.Analytic
