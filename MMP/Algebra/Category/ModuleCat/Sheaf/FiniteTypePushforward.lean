module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Pushforward of sheaves of modules of finite type

Let `G : D ⥤ C` be a continuous and cocontinuous functor between sites, `R` a sheaf of rings
on `C`, `S` one on `D`, and `φ : S ⟶ G_* R` a morphism of sheaves of rings with
`G_* 𝟙_R ≅ 𝟙_S`. Local generators of an `R`-module `M` over a covering family `Xᵢ` of `C`
give local generators of `G_* M` over the objects `Y` of `D` with a map `G Y ⟶ Xᵢ`: these
cover `D` since `G` is cocontinuous, and the generators are transported along the
pushforward functors `Over Y ⥤ Over Xᵢ`, provided these preserve colimits. In particular the
pushforward of a module of finite type is of finite type; this holds whenever `G` is a left
adjoint and `φ` is an isomorphism, for instance for an equivalence of sites.

This is the analogue for `SheafOfModules.LocalGeneratorsData` of Mathlib's
`SheafOfModules.QuasicoherentData.pushforward`.

## Main definitions

* `MMP.localGeneratorsDataPushforward`: the pushforward of local generators.

## Main results

* `MMP.isFiniteType_pushforward`: `G_* M` is of finite type if `M` is.
* `MMP.isFiniteType_pushforward_of_isLeftAdjoint`: the same when `G` is a left adjoint and `φ`
  is an isomorphism.
* `MMP.isFiniteType_of_iso`: being of finite type is invariant under isomorphism.
* `MMP.isFiniteType_of_epi`: a quotient of a module of finite type is of finite type.
* `MMP.isFiniteType_over`: the restriction `M.over X` of a module of finite type is of finite
  type (`Over.forget X` is left adjoint to `Over.star X`).
-/

@[expose] public section

universe u v₁ v₂ u₁ u₂

open CategoryTheory Limits SheafOfModules

namespace MMP

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  {D : Type u₂} [Category.{v₂, u₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : D), HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : D), (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)

/-- The pushforward of local generators of a sheaf of modules along a continuous and
cocontinuous functor. -/
@[simps I X]
noncomputable def localGeneratorsDataPushforward (η : (pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      SheafOfModules.pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.LocalGeneratorsData) :
    LocalGeneratorsData ((SheafOfModules.pushforward φ).obj M) where
  I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
  X i := i.1
  coversTop Y := by
    refine K.superset_covering ?_ <| G.cover_lift K _ (P.coversTop (G.obj Y))
    intro Z g ⟨i, ⟨v⟩⟩
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
  generators i := by
    letI overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
      SheafOfModules.pushforward (𝟙 _)
    letI G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
    letI ψ : S.over i.1 ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1) (J.over (P.X i.2.1))).obj
          (R.over (P.X i.2.1)) :=
      ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
    letI e : (SheafOfModules.pushforward ψ).obj (unit (R.over (P.X i.snd.fst))) ≅
      unit (S.over i.fst) := overS.mapIso η
    haveI : PreservesColimitsOfSize.{u, u, _} (SheafOfModules.pushforward ψ) := h _ _ _
    exact (P.generators i.2.1).map (SheafOfModules.pushforward ψ) e.symm

/-- The pushforward of local generators of finite type consists of local generators of finite
type. -/
instance isFiniteType_localGeneratorsDataPushforward
    (η : (SheafOfModules.pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      SheafOfModules.pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} (P : M.LocalGeneratorsData) [P.IsFiniteType] :
    (localGeneratorsDataPushforward G φ η h P).IsFiniteType where
  isFiniteType i := ⟨(LocalGeneratorsData.IsFiniteType.isFiniteType (p := P) i.2.1).finite⟩

/-- The pushforward of a sheaf of modules of finite type along a continuous and cocontinuous
functor is of finite type. -/
theorem isFiniteType_pushforward (η : (SheafOfModules.pushforward φ).obj (unit R) ≅ unit S)
    [∀ (X : D), (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u} <|
      SheafOfModules.pushforward.{u} (R := (R.over Y)) (F := Over.post (X := X) G ⋙ Over.map f)
        (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  exact ⟨⟨(localGeneratorsDataPushforward G φ η h P).shrink,
    ⟨fun _ => ⟨(LocalGeneratorsData.IsFiniteType.isFiniteType (p := P) _).finite⟩⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The pushforward of a sheaf of modules of finite type along a left adjoint continuous and
cocontinuous functor, for an isomorphism of sheaves of rings, is of finite type. -/
theorem isFiniteType_pushforward_of_isLeftAdjoint
    (η : (SheafOfModules.pushforward φ).obj (unit R) ≅ unit S)
    [G.IsLeftAdjoint] [hφ : IsIso φ]
    [∀ X, Functor.IsContinuous (Over.post (X := X) G) (K.over _) (J.over _)]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := by
  apply +allowSynthFailures isFiniteType_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) := Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

/-- The restriction `M.over X` of a sheaf of modules of finite type is of finite type. -/
theorem isFiniteType_over {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (X₀ : C)
    [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ (X : Over X₀), HasSheafify ((J.over X₀).over X) AddCommGrpCat.{u}]
    [∀ (X : Over X₀), ((J.over X₀).over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasBinaryProducts C] [HasPullbacks C]
    [∀ X, Functor.IsContinuous (Over.post (X := X) (Over.forget X₀)) ((J.over X₀).over _)
      (J.over _)]
    (M : SheafOfModules.{u} R) [M.IsFiniteType] : (M.over X₀).IsFiniteType := by
  haveI : (Over.forget X₀).IsLeftAdjoint := ⟨_, ⟨Over.forgetAdjStar X₀⟩⟩
  exact isFiniteType_pushforward_of_isLeftAdjoint (Over.forget X₀) (𝟙 _) (Iso.refl _)
    (hφ := inferInstance)

/-- Being of finite type is invariant under isomorphism: local generators of `M` give local
generators of `N` along `e : M ≅ N`. -/
theorem isFiniteType_of_iso {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  exact ⟨⟨{ I := P.I, X := P.X, coversTop := P.coversTop,
              generators := fun i => (P.generators i).ofEpi (Hom.over e.hom (P.X i)) },
    ⟨fun i => by
      haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := P) i
      exact inferInstanceAs ((P.generators i).ofEpi (Hom.over e.hom (P.X i))).IsFiniteType⟩⟩⟩

/-- A quotient of a sheaf of modules of finite type is of finite type: the images of local
generators of `M` along an epimorphism `M ⟶ N` generate `N` locally (restriction to a slice is a
left adjoint, so it preserves epimorphisms). -/
theorem isFiniteType_of_epi {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasBinaryProducts C]
    [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
    [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (e : M ⟶ N) [Epi e] [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  haveI : ∀ X : C, Epi (Hom.over e X) := fun X => by
    haveI : (overFunctor R X).IsLeftAdjoint := by unfold overFunctor; infer_instance
    exact (overFunctor R X).map_epi e
  exact ⟨⟨{ I := P.I, X := P.X, coversTop := P.coversTop,
              generators := fun i => (P.generators i).ofEpi (Hom.over e (P.X i)) },
    ⟨fun i => by
      haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := P) i
      exact inferInstanceAs ((P.generators i).ofEpi (Hom.over e (P.X i))).IsFiniteType⟩⟩⟩

end MMP
