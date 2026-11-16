module

public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelsMaps
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ReflectIso

/-!
# The unit and cocycle conditions for spread-out morphisms of modules

Let `μ` be the morphisms of a finite system of modules of finite presentation on a diagram over a
cofiltered limit, satisfying the unit and cocycle conditions, and let `Ψ φ` be models of the
morphisms `μ φ` at a stage. The unit and cocycle conditions for the models `Ψ φ` hold after
pulling back to the limit, since there they are the conditions for `μ`; so they hold at a later
stage (Stacks 01ZR (3)), and then at every still later stage.

## Main definitions

* `MMP.CoefficientModels.MapStageData.stageHom`: the model of the morphism `μ φ`, moved to a
  later stage.

## Main results

* `MMP.CoefficientModels.MapStageData.transport_proj_stageHom`: the models moved to any later
  stage still pull back to `μ φ`.
* `MMP.CoefficientModels.MapStageData.exists_unit_cocycle`: from some stage on, the models of
  the morphisms satisfy the unit and cocycle conditions.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits (canHom canIso canHom_comp canHom_naturality)

universe u

namespace MMP.CoefficientModels

section Transport

variable {U V W T₁ T₂ : Scheme.{u}} {A : T₁.Modules} {B : T₂.Modules}

/-- Two morphisms with equal transports along `r` have equal transports along any composite
`r' ≫ r`. -/
theorem transport_comp_left_eq {r : V ⟶ W} {s₁ : W ⟶ T₁} {s₂ : W ⟶ T₂} {t₁ : V ⟶ T₁}
    {t₂ : V ⟶ T₂} {h₁ : r ≫ s₁ = t₁} {h₂ : r ≫ s₂ = t₂}
    {Ψ Ψ' : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B}
    (h : transport r h₁ h₂ Ψ = transport r h₁ h₂ Ψ') (r' : U ⟶ V) {u₁ : U ⟶ T₁} {u₂ : U ⟶ T₂}
    (k₁ : (r' ≫ r) ≫ s₁ = u₁) (k₂ : (r' ≫ r) ≫ s₂ = u₂) :
    transport (r' ≫ r) k₁ k₂ Ψ = transport (r' ≫ r) k₁ k₂ Ψ' := by
  have k₁' : r' ≫ t₁ = u₁ := by rw [← h₁, ← Category.assoc, k₁]
  have k₂' : r' ≫ t₂ = u₂ := by rw [← h₂, ← Category.assoc, k₂]
  rw [← transport_transport r h₁ h₂ r' k₁' k₂' k₁ k₂, h, transport_transport]

/-- Transport of the identification of pullbacks along equal morphisms, with the resulting
equality of morphisms given. -/
theorem transport_pullbackCongr_of_eq (r : V ⟶ W) {s₁ s₂ : W ⟶ T₁} (hs : s₁ = s₂)
    {t₁ t₂ : V ⟶ T₁} (h₁ : r ≫ s₁ = t₁) (h₂ : r ≫ s₂ = t₂) (ht : t₁ = t₂) :
    transport r h₁ h₂ ((Scheme.Modules.pullbackCongr hs).hom.app A) =
      (Scheme.Modules.pullbackCongr ht).hom.app A :=
  transport_pullbackCongr r hs h₁ h₂

/-- A transport is an isomorphism exactly when the pullback of the morphism is. -/
theorem isIso_transport_iff (r : V ⟶ W) {s₁ : W ⟶ T₁} {s₂ : W ⟶ T₂} {t₁ : V ⟶ T₁}
    {t₂ : V ⟶ T₂} (h₁ : r ≫ s₁ = t₁) (h₂ : r ≫ s₂ = t₂)
    (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B) :
    IsIso (transport r h₁ h₂ Ψ) ↔ IsIso ((Scheme.Modules.pullback r).map Ψ) := by
  refine ⟨fun _ => ?_, fun _ => ?_⟩
  · rw [pullback_map_eq_transport r h₁ h₂ Ψ]
    infer_instance
  · rw [transport]
    infer_instance

end Transport

section Canonical

variable {X₁ X₂ Y₁ Y₂ Y₃ T₁ T₂ T₃ : Scheme.{u}} {N₁ : T₁.Modules} {N₂ : T₂.Modules}
  {N₃ : T₃.Modules}

/-- The unit condition, restated from canonical form in terms of `pullbackId`. -/
theorem pullbackCongr_comp_canIso_inv {f : Y₁ ⟶ Y₁} (hf : 𝟙 Y₁ = f) (s : Y₁ ⟶ T₁)
    (hs : s = f ≫ s) :
    (Scheme.Modules.pullbackCongr hs).hom.app N₁ ≫ (canIso f s (f ≫ s) rfl N₁).inv =
      (Scheme.Modules.pullbackId Y₁).inv.app ((Scheme.Modules.pullback s).obj N₁) ≫
        (Scheme.Modules.pullbackCongr hf).hom.app ((Scheme.Modules.pullback s).obj N₁) := by
  have h := limitMap_id_aux hf (Iso.refl ((Scheme.Modules.pullback s).obj N₁))
  simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  haveI : Mono (canHom f s (f ≫ s) rfl N₁) := IsIso.mono_of_iso _
  rw [← cancel_mono (canHom f s (f ≫ s) rfl N₁), Category.assoc,
    ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, Iso.inv_hom_id, Category.comp_id,
    Category.assoc, Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, h]

/-- The cocycle condition, restated from canonical form in terms of `pullbackComp`. -/
theorem comp_canIso_inv_eq (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) {F : Y₁ ⟶ Y₃} (hF : f ≫ g = F)
    (s₁ : Y₁ ⟶ T₁) (s₂ : Y₂ ⟶ T₂) (s₃ : Y₃ ⟶ T₃)
    (Ψ₁ : (Scheme.Modules.pullback s₁).obj N₁ ⟶ (Scheme.Modules.pullback (f ≫ s₂)).obj N₂)
    (Ψ₂ : (Scheme.Modules.pullback s₂).obj N₂ ⟶ (Scheme.Modules.pullback (g ≫ s₃)).obj N₃)
    (Ψ₃ : (Scheme.Modules.pullback s₁).obj N₁ ⟶ (Scheme.Modules.pullback (F ≫ s₃)).obj N₃)
    (hc : f ≫ g ≫ s₃ = F ≫ s₃)
    (h : Ψ₃ = Ψ₁ ≫ transport f rfl rfl Ψ₂ ≫ (Scheme.Modules.pullbackCongr hc).hom.app N₃) :
    Ψ₃ ≫ (canIso F s₃ (F ≫ s₃) rfl N₃).inv =
      (Ψ₁ ≫ (canIso f s₂ (f ≫ s₂) rfl N₂).inv) ≫
        (Scheme.Modules.pullback f).map (Ψ₂ ≫ (canIso g s₃ (g ≫ s₃) rfl N₃).inv) ≫
          (Scheme.Modules.pullbackComp f g).hom.app _ ≫
            (Scheme.Modules.pullbackCongr hF).hom.app _ := by
  have key := limitMap_comp_aux f g hF (Iso.refl ((Scheme.Modules.pullback s₃).obj N₃))
  simp only [Iso.refl_hom] at key
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at key
  haveI : Mono (canHom F s₃ (F ≫ s₃) rfl N₃) := IsIso.mono_of_iso _
  rw [← cancel_mono (canHom F s₃ (F ≫ s₃) rfl N₃)]
  simp only [Category.assoc, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom,
    Iso.inv_hom_id, Category.comp_id, Functor.map_comp]
  simp only [Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]
  rw [key, h, transport]
  simp only [Category.assoc, ← Functor.map_comp_assoc,
    ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, Iso.inv_hom_id, Category.comp_id]

/-- The descent identity, restated from canonical form in terms of the identifications of the
pullbacks of the models. -/
theorem descent_eq {M₁ : X₁.Modules} {M₂ : X₂.Modules} (p₁ : X₁ ⟶ Y₁) (p₂ : X₂ ⟶ Y₂)
    (a : X₁ ⟶ X₂) (f : Y₁ ⟶ Y₂) (hp : a ≫ p₂ = p₁ ≫ f) (σ₁ : Y₁ ⟶ T₁) (σ₂ : Y₂ ⟶ T₂)
    {P₁ : X₁ ⟶ T₁} {P₂ : X₂ ⟶ T₂} (h₁ : p₁ ≫ σ₁ = P₁) (h₂ : p₂ ≫ σ₂ = P₂)
    (h₁₂ : p₁ ≫ f ≫ σ₂ = a ≫ P₂) (θ₀₁ : M₁ ≅ (Scheme.Modules.pullback P₁).obj N₁)
    (θ₀₂ : M₂ ≅ (Scheme.Modules.pullback P₂).obj N₂)
    (θ₁ : (Scheme.Modules.pullback p₁).obj ((Scheme.Modules.pullback σ₁).obj N₁) ≅ M₁)
    (θ₂ : (Scheme.Modules.pullback p₂).obj ((Scheme.Modules.pullback σ₂).obj N₂) ≅ M₂)
    (hθ₁ : θ₁.hom = canHom p₁ σ₁ P₁ h₁ N₁ ≫ θ₀₁.inv)
    (hθ₂ : θ₂.hom = canHom p₂ σ₂ P₂ h₂ N₂ ≫ θ₀₂.inv)
    (μ : M₁ ⟶ (Scheme.Modules.pullback a).obj M₂)
    (Ψ : (Scheme.Modules.pullback σ₁).obj N₁ ⟶ (Scheme.Modules.pullback (f ≫ σ₂)).obj N₂)
    (hΨ : transport p₁ h₁ h₁₂ Ψ = θ₀₁.inv ≫ μ ≫ (Scheme.Modules.pullback a).map θ₀₂.hom ≫
      canHom a P₂ (a ≫ P₂) rfl N₂) :
    θ₁.inv ≫ (Scheme.Modules.pullback p₁).map (Ψ ≫ (canIso f σ₂ (f ≫ σ₂) rfl N₂).inv) ≫
        (Scheme.Modules.pullbackComp p₁ f).hom.app _ ≫
        (Scheme.Modules.pullbackCongr hp).inv.app _ ≫
        (Scheme.Modules.pullbackComp a p₂).inv.app _ ≫
        (Scheme.Modules.pullback a).map θ₂.hom = μ := by
  have hμ : μ = θ₀₁.hom ≫ transport p₁ h₁ h₁₂ Ψ ≫ (canIso a P₂ (a ≫ P₂) rfl N₂).inv ≫
      (Scheme.Modules.pullback a).map θ₀₂.inv := by
    rw [hΨ]
    simp only [Category.assoc, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom,
      Iso.hom_inv_id, Iso.hom_inv_id_assoc, ← Functor.map_comp]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hθ₁' : θ₁.inv = θ₀₁.hom ≫ (canIso p₁ σ₁ P₁ h₁ N₁).inv := by
    rw [← cancel_epi θ₁.hom, Iso.hom_inv_id, hθ₁, Category.assoc, Iso.inv_hom_id_assoc,
      ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, Iso.hom_inv_id]
  have c₁ := canHom_comp a p₂ σ₂ (a ≫ p₂) P₂ (a ≫ P₂) rfl h₂ (by rw [Category.assoc, h₂]) rfl N₂
  have c₂ := canHom_comp p₁ f σ₂ (a ≫ p₂) (f ≫ σ₂) (a ≫ P₂) hp.symm rfl
    (by rw [Category.assoc, h₂]) h₁₂ N₂
  have e₁ : (Scheme.Modules.pullbackComp a p₂).inv.app ((Scheme.Modules.pullback σ₂).obj N₂) ≫
      canHom a p₂ (a ≫ p₂) rfl ((Scheme.Modules.pullback σ₂).obj N₂) = 𝟙 _ := by
    rw [Stacks.AlgebraicGeometry.ModuleLimits.canHom_rfl, Iso.inv_hom_id_app]
  have e₂ : (Scheme.Modules.pullbackComp p₁ f).hom.app ((Scheme.Modules.pullback σ₂).obj N₂) ≫
      (Scheme.Modules.pullbackCongr hp).inv.app ((Scheme.Modules.pullback σ₂).obj N₂) =
      canHom p₁ f (a ≫ p₂) hp.symm ((Scheme.Modules.pullback σ₂).obj N₂) := by
    simp [canHom, Scheme.Modules.pullbackCongr]
  have core : (Scheme.Modules.pullback p₁).map (canIso f σ₂ (f ≫ σ₂) rfl N₂).inv ≫
      (Scheme.Modules.pullbackComp p₁ f).hom.app ((Scheme.Modules.pullback σ₂).obj N₂) ≫
      (Scheme.Modules.pullbackCongr hp).inv.app ((Scheme.Modules.pullback σ₂).obj N₂) ≫
      (Scheme.Modules.pullbackComp a p₂).inv.app ((Scheme.Modules.pullback σ₂).obj N₂) ≫
      (Scheme.Modules.pullback a).map (canHom p₂ σ₂ P₂ h₂ N₂) =
      canHom p₁ (f ≫ σ₂) (a ≫ P₂) h₁₂ N₂ ≫ (canIso a P₂ (a ≫ P₂) rfl N₂).inv := by
    haveI : Mono (canHom a P₂ (a ≫ P₂) rfl N₂) := IsIso.mono_of_iso _
    rw [← cancel_mono (canHom a P₂ (a ≫ P₂) rfl N₂)]
    simp only [Category.assoc]
    rw [c₁, reassoc_of% e₁, reassoc_of% e₂, ← c₂, ← Functor.map_comp_assoc]
    simp only [← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, Iso.inv_hom_id,
      Category.comp_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hμ, hθ₁', hθ₂, transport]
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% core]

end Canonical

namespace DiagramStageData

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D} {n : ℕ}
  {J : Type u} [SmallCategory J] {X : J ⥤ Over c.pt}
  {ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt} (d : DiagramStageData D c n X ι)

/-- The model of an endomorphism equal to the identity is the identity. -/
theorem stageLift_eq_id {m : Over d.i₀} (bm : m ⟶ d.m₂) {j : J} (f : j ⟶ j) (hf : f = 𝟙 j) :
    stageLift (d.H f) (d.H_w f) (bm ≫ d.b₂) = 𝟙 _ := by
  subst hf
  exact congrArg CommaMorphism.left ((d.diagram bm).map_id j)

/-- The models of the arrows compose. -/
theorem stageLift_comp_stageLift {m : Over d.i₀} (bm : m ⟶ d.m₂) {j j' j'' : J} (φ : j ⟶ j')
    (ψ : j' ⟶ j'') (f : j ⟶ j'') (hf : φ ≫ ψ = f) :
    stageLift (d.H φ) (d.H_w φ) (bm ≫ d.b₂) ≫ stageLift (d.H ψ) (d.H_w ψ) (bm ≫ d.b₂) =
      stageLift (d.H f) (d.H_w f) (bm ≫ d.b₂) := by
  subst hf
  exact (congrArg CommaMorphism.left ((d.diagram bm).map_comp φ ψ)).symm

end DiagramStageData

section MapStageData

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D} {n : ℕ}
  {J : Type u} [SmallCategory J] {X : J ⥤ Over c.pt}
  {ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt} {d : DiagramStageData D c n X ι}
  {E : Type*} [Category E] {π : E ⥤ J} {M : ∀ e, (X.obj (π.obj e)).left.Modules}
  {md : ModuleStageData d π M}
  {μ : ∀ {e e' : E} (φ : e ⟶ e'),
    M e ⟶ (Scheme.Modules.pullback (X.map (π.map φ)).left).obj (M e')}

namespace ModuleStageData

variable (md)

/-- The stage map to the model of `π.obj e` is unchanged by precomposing with the stage lift of
the identity arrow `π.map (𝟙 e)`. -/
theorem stageMap_eq_stageLift_id {m : Over d.i₀} (bm : m ⟶ md.m₃) (e : E) :
    stageMap D (d.W (π.obj e)) (bm ≫ md.bₑ e) =
      stageLift (d.H (π.map (𝟙 e))) (d.H_w _) ((bm ≫ md.b₃) ≫ d.b₂) ≫
        stageMap D (d.W (π.obj e)) (bm ≫ md.bₑ e) := by
  rw [d.stageLift_eq_id _ _ (π.map_id e), Category.id_comp]

/-- The stage lifts of `π.map φ` and `π.map ψ`, followed by a stage map, compose to the stage lift
of `π.map (φ ≫ ψ)` followed by the same stage map. -/
theorem stageLift_stageLift_stageMap {m : Over d.i₀} (bm : m ⟶ md.m₃) {e e' e'' : E}
    (φ : e ⟶ e') (ψ : e' ⟶ e'') :
    stageLift (d.H (π.map φ)) (d.H_w _) ((bm ≫ md.b₃) ≫ d.b₂) ≫
        stageLift (d.H (π.map ψ)) (d.H_w _) ((bm ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e'')) (bm ≫ md.bₑ e'') =
      stageLift (d.H (π.map (φ ≫ ψ))) (d.H_w _) ((bm ≫ md.b₃) ≫ d.b₂) ≫
        stageMap D (d.W (π.obj e'')) (bm ≫ md.bₑ e'') := by
  rw [← Category.assoc, d.stageLift_comp_stageLift _ _ _ _ (π.map_comp φ ψ).symm]

/-- The identification of the pullback of the model of `M e` with `M e`, in canonical form. -/
theorem moduleIso_hom {m : Over d.i₀} (bm : m ⟶ md.m₃) (e : E) :
    (md.moduleIso bm e).hom = canHom (d.proj m (π.obj e)) (stageMap D (d.W (π.obj e))
      (bm ≫ md.bₑ e)) (d.proj (md.mₑ e) (π.obj e)) (md.proj_stageMap_bₑ bm e) (md.N₀ e) ≫
        (md.θ₀ e).inv := by
  simp only [moduleIso, stageModuleIso, Iso.symm_hom, canHom, Category.assoc]
  rfl

end ModuleStageData

namespace MapStageData

variable (ms : MapStageData md μ)

/-- The stage map along `bm` followed by the stage map along `ms.ba ≫ md.bₑ e` is the stage map
along `(bm ≫ ms.ba) ≫ md.bₑ e`. -/
theorem stageMap_stageMap_bₑ {m : Over d.i₀} (bm : m ⟶ ms.a) (e : E) :
    stageMap D (d.W (π.obj e)) bm ≫ stageMap D (d.W (π.obj e)) (ms.ba ≫ md.bₑ e) =
      stageMap D (d.W (π.obj e)) ((bm ≫ ms.ba) ≫ md.bₑ e) := by
  rw [← stageMap_comp, Category.assoc]

/-- The stage map along `bm` commutes with the stage lift of `π.map φ` followed by the stage map
to the model of `π.obj e'`. -/
theorem stageMap_stageLift_stageMap_bₑ {m : Over d.i₀} (bm : m ⟶ ms.a) {e e' : E}
    (φ : e ⟶ e') :
    stageMap D (d.W (π.obj e)) bm ≫ stageLift (d.H (π.map φ)) (d.H_w _)
        ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫ stageMap D (d.W (π.obj e')) (ms.ba ≫ md.bₑ e') =
      stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
        stageMap D (d.W (π.obj e')) ((bm ≫ ms.ba) ≫ md.bₑ e') := by
  rw [← Category.assoc, ← stageLift_stageMap (d.H (π.map φ)) (d.H_w _) bm
      ((ms.ba ≫ md.b₃) ≫ d.b₂) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) (by simp only [Category.assoc]),
    Category.assoc, ← stageMap_comp]
  simp only [Category.assoc]

/-- The model of the morphism `μ φ`, moved to a stage `m` later than the stage `ms.a`. -/
def stageHom {m : Over d.i₀} (bm : m ⟶ ms.a) {e e' : E} (φ : e ⟶ e') :
    (Scheme.Modules.pullback (stageMap D (d.W (π.obj e)) ((bm ≫ ms.ba) ≫ md.bₑ e))).obj
        (md.N₀ e) ⟶
      (Scheme.Modules.pullback (stageLift (d.H (π.map φ)) (d.H_w _)
        (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e')) ((bm ≫ ms.ba) ≫ md.bₑ e'))).obj (md.N₀ e') :=
  transport (stageMap D (d.W (π.obj e)) bm) (ms.stageMap_stageMap_bₑ bm e)
    (ms.stageMap_stageLift_stageMap_bₑ bm φ) (ms.Ψ φ)

/-- `ms.stageHom bm φ` is the transport of `ms.Ψ φ` along the stage map along `bm`. -/
theorem stageHom_def {m : Over d.i₀} (bm : m ⟶ ms.a) {e e' : E} (φ : e ⟶ e') :
    ms.stageHom bm φ = transport (stageMap D (d.W (π.obj e)) bm) (ms.stageMap_stageMap_bₑ bm e)
      (ms.stageMap_stageLift_stageMap_bₑ bm φ) (ms.Ψ φ) := rfl

/-- **The models moved to a later stage still pull back to `μ φ`.** -/
theorem transport_proj_stageHom {m : Over d.i₀} (bm : m ⟶ ms.a) {e e' : E} (φ : e ⟶ e') :
    transport (d.proj m (π.obj e)) (md.proj_stageMap_bₑ (bm ≫ ms.ba) e)
      (md.proj_stageLift_stageMap_bₑ (bm ≫ ms.ba) _ φ) (ms.stageHom bm φ) = md.limitMap μ φ := by
  have l₁ : (d.proj m (π.obj e) ≫ stageMap D _ bm) ≫ stageMap D _ (ms.ba ≫ md.bₑ e) =
      d.proj (md.mₑ e) (π.obj e) := by
    rw [d.proj_stageMap, md.proj_stageMap_bₑ]
  have l₂ : (d.proj m (π.obj e) ≫ stageMap D _ bm) ≫
      stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
        stageMap D (d.W (π.obj e')) (ms.ba ≫ md.bₑ e') =
      (X.map (π.map φ)).left ≫ d.proj (md.mₑ e') (π.obj e') := by
    rw [d.proj_stageMap, md.proj_stageLift_stageMap_bₑ]
  rw [stageHom, transport_transport _ _ _ _ _ _ l₁ l₂, ← ms.transport_proj φ]
  exact transport_congr (d.proj_stageMap m bm _) _ _ _ _ _

/-- The right side of the cocycle condition for the models at the stage `ms.a`. -/
def cocycleHom {e e' e'' : E} (φ : e ⟶ e') (ψ : e' ⟶ e'') :
    (Scheme.Modules.pullback (stageMap D (d.W (π.obj e)) (ms.ba ≫ md.bₑ e))).obj (md.N₀ e) ⟶
      (Scheme.Modules.pullback (stageLift (d.H (π.map (φ ≫ ψ))) (d.H_w _)
        ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e'')) (ms.ba ≫ md.bₑ e''))).obj (md.N₀ e'') :=
  ms.Ψ φ ≫ transport (stageLift (d.H (π.map φ)) (d.H_w (π.map φ)) ((ms.ba ≫ md.b₃) ≫ d.b₂))
    (s₁ := stageMap D (d.W (π.obj e')) (ms.ba ≫ md.bₑ e'))
    (s₂ := stageLift (d.H (π.map ψ)) (d.H_w (π.map ψ)) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
      stageMap D (d.W (π.obj e'')) (ms.ba ≫ md.bₑ e''))
    (A := md.N₀ e') (B := md.N₀ e'') rfl rfl (ms.Ψ ψ) ≫
    (Scheme.Modules.pullbackCongr (md.stageLift_stageLift_stageMap ms.ba φ ψ)).hom.app (md.N₀ e'')

/-- The right side of the cocycle condition at a later stage is the transport of the one at the
stage `ms.a`. -/
theorem stageHom_comp_transport_stageHom {m : Over d.i₀} (bm : m ⟶ ms.a) {e e' e'' : E}
    (φ : e ⟶ e') (ψ : e' ⟶ e'') :
    ms.stageHom bm φ ≫ transport (stageLift (d.H (π.map φ)) (d.H_w _)
        (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂)) rfl rfl (ms.stageHom bm ψ) ≫
      (Scheme.Modules.pullbackCongr
        (md.stageLift_stageLift_stageMap (bm ≫ ms.ba) φ ψ)).hom.app (md.N₀ e'') =
    transport (stageMap D (d.W (π.obj e)) bm) (ms.stageMap_stageMap_bₑ bm e)
      (ms.stageMap_stageLift_stageMap_bₑ bm (φ ≫ ψ)) (ms.cocycleHom φ ψ) := by
  have hsl : stageMap D (d.W (π.obj e)) bm ≫
      stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) =
      stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
        stageMap D (d.W (π.obj e')) bm :=
    (stageLift_stageMap (d.H (π.map φ)) (d.H_w _) bm ((ms.ba ≫ md.b₃) ≫ d.b₂)
      (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) (by simp only [Category.assoc])).symm
  have hmid : stageMap D (d.W (π.obj e)) bm ≫
      stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
        stageLift (d.H (π.map ψ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e'')) (ms.ba ≫ md.bₑ e'') =
      stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
        stageLift (d.H (π.map ψ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e'')) ((bm ≫ ms.ba) ≫ md.bₑ e'') := by
    rw [← Category.assoc, hsl, Category.assoc, ms.stageMap_stageLift_stageMap_bₑ]
  have key : transport (stageMap D (d.W (π.obj e)) bm) (ms.stageMap_stageLift_stageMap_bₑ bm φ)
      hmid (transport (stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂)) rfl rfl
        (ms.Ψ ψ)) =
      transport (stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂)) rfl rfl
        (ms.stageHom bm ψ) := by
    have l₁ : (stageMap D (d.W (π.obj e)) bm ≫
        stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂)) ≫
          stageMap D (d.W (π.obj e')) (ms.ba ≫ md.bₑ e') =
        stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e')) ((bm ≫ ms.ba) ≫ md.bₑ e') := by
      rw [Category.assoc, ms.stageMap_stageLift_stageMap_bₑ]
    have l₂ : (stageMap D (d.W (π.obj e)) bm ≫
        stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂)) ≫
          stageLift (d.H (π.map ψ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
            stageMap D (d.W (π.obj e'')) (ms.ba ≫ md.bₑ e'') =
        stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
          stageLift (d.H (π.map ψ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
            stageMap D (d.W (π.obj e'')) ((bm ≫ ms.ba) ≫ md.bₑ e'') := by
      rw [Category.assoc]; exact hmid
    have l₁' : (stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
        stageMap D (d.W (π.obj e')) bm) ≫ stageMap D (d.W (π.obj e')) (ms.ba ≫ md.bₑ e') =
        stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e')) ((bm ≫ ms.ba) ≫ md.bₑ e') := by
      rw [Category.assoc, ms.stageMap_stageMap_bₑ]
    have l₂' : (stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
        stageMap D (d.W (π.obj e')) bm) ≫
          stageLift (d.H (π.map ψ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
            stageMap D (d.W (π.obj e'')) (ms.ba ≫ md.bₑ e'') =
        stageLift (d.H (π.map φ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
          stageLift (d.H (π.map ψ)) (d.H_w _) (((bm ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
            stageMap D (d.W (π.obj e'')) ((bm ≫ ms.ba) ≫ md.bₑ e'') := by
      rw [Category.assoc, ms.stageMap_stageLift_stageMap_bₑ]
    rw [transport_transport _ rfl rfl _ _ _ l₁ l₂, stageHom,
      transport_transport _ _ _ _ _ _ l₁' l₂']
    exact transport_congr hsl _ _ _ _ _
  rw [cocycleHom, transport_comp _ _ (ms.stageMap_stageLift_stageMap_bₑ bm φ),
    transport_comp _ _ hmid,
    transport_pullbackCongr_of_eq _ _ _ _ (md.stageLift_stageLift_stageMap (bm ≫ ms.ba) φ ψ), key,
    stageHom_def ms bm φ]

end MapStageData

section Limit

variable [IsCofiltered I] [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

omit [Category E] in
/-- **Two morphisms at a stage whose transports to the limit agree have equal transports to
every stage later than some stage** (Stacks 01ZR (3)), for the stages of the model of an object
of the diagram. -/
theorem _root_.MMP.CoefficientModels.DiagramStageData.exists_stageMap_transport_eq
    (d : DiagramStageData D c n X ι) (hc : IsLimit c) (j : J) {a : Over d.i₀}
    {T₁ T₂ : Scheme.{u}} {A : T₁.Modules} {B : T₂.Modules} (s₁ : stageObj D (d.W j) a ⟶ T₁)
    (s₂ : stageObj D (d.W j) a ⟶ T₂)
    (hA : ((Scheme.Modules.pullback s₁).obj A).IsFinitePresentation)
    (hB : ((Scheme.Modules.pullback s₂).obj B).IsFinitePresentation)
    {t₁ : (X.obj j).left ⟶ T₁} {t₂ : (X.obj j).left ⟶ T₂} (h₁ : d.proj a j ≫ s₁ = t₁)
    (h₂ : d.proj a j ≫ s₂ = t₂)
    (Ψ Ψ' : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B)
    (h : transport (d.proj a j) h₁ h₂ Ψ = transport (d.proj a j) h₁ h₂ Ψ') :
    ∃ (k : Over d.i₀) (ek : k ⟶ a), ∀ {m : Over d.i₀} (y : m ⟶ k) {u₁ : stageObj D (d.W j) m ⟶ T₁}
      {u₂ : stageObj D (d.W j) m ⟶ T₂} (k₁ : stageMap D (d.W j) (y ≫ ek) ≫ s₁ = u₁)
      (k₂ : stageMap D (d.W j) (y ≫ ek) ≫ s₂ = u₂),
      transport (stageMap D (d.W j) (y ≫ ek)) k₁ k₂ Ψ =
        transport (stageMap D (d.W j) (y ≫ ek)) k₁ k₂ Ψ' := by
  have {a b : Over d.i₀} (f : a ⟶ b) : IsAffineHom ((stageDiagram D (d.W j)).map f) :=
    isAffineHom_stageMap D (d.W j) f
  have (a : Over d.i₀) : CompactSpace ((stageDiagram D (d.W j)).obj a) :=
    compactSpace_stageObj D (d.W j) (d.finitePresentation j) a
  have (a : Over d.i₀) : QuasiSeparatedSpace ((stageDiagram D (d.W j)).obj a) :=
    quasiSeparatedSpace_stageObj D (d.W j) (d.finitePresentation j) a
  obtain ⟨k, ek, hk⟩ := exists_transport_eq_transport_of_isLimit (stageDiagram D (d.W j))
    (legCone D (d.W j) c (X.obj j) (d.g j) (d.isPullback j))
    (isLimitLegCone D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) hc) a s₁ s₂ (hA := hA)
    (hB := hB) h₁ h₂ Ψ Ψ' h
  refine ⟨k, ek, fun {m} y u₁ u₂ k₁ k₂ => ?_⟩
  have k₁' : (stageMap D (d.W j) y ≫ stageMap D (d.W j) ek) ≫ s₁ = u₁ := by
    rwa [← stageMap_comp]
  have k₂' : (stageMap D (d.W j) y ≫ stageMap D (d.W j) ek) ≫ s₂ = u₂ := by
    rwa [← stageMap_comp]
  exact (transport_congr (stageMap_comp D (d.W j) y ek) k₁ k₂ k₁' k₂' Ψ).trans
    ((transport_comp_left_eq hk (stageMap D (d.W j) y) k₁' k₂').trans
      (transport_congr (stageMap_comp D (d.W j) y ek) k₁ k₂ k₁' k₂' Ψ').symm)

omit [Category E] in
/-- **A morphism at a stage whose transport to the limit is an isomorphism has isomorphisms as
transports to every stage later than some stage** (Stacks 01ZR (2), (3)), for the stages of the
model of an object of the diagram. -/
theorem _root_.MMP.CoefficientModels.DiagramStageData.exists_stageMap_isIso_transport
    (d : DiagramStageData D c n X ι) (hc : IsLimit c) (j : J) {a : Over d.i₀}
    {T₁ T₂ : Scheme.{u}} {A : T₁.Modules} {B : T₂.Modules} (s₁ : stageObj D (d.W j) a ⟶ T₁)
    (s₂ : stageObj D (d.W j) a ⟶ T₂)
    (hA : ((Scheme.Modules.pullback s₁).obj A).IsFinitePresentation)
    (hB : ((Scheme.Modules.pullback s₂).obj B).IsFinitePresentation)
    {t₁ : (X.obj j).left ⟶ T₁} {t₂ : (X.obj j).left ⟶ T₂} (h₁ : d.proj a j ≫ s₁ = t₁)
    (h₂ : d.proj a j ≫ s₂ = t₂)
    (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B)
    (h : IsIso (transport (d.proj a j) h₁ h₂ Ψ)) :
    ∃ (k : Over d.i₀) (ek : k ⟶ a), ∀ {m : Over d.i₀} (y : m ⟶ k) {u₁ : stageObj D (d.W j) m ⟶ T₁}
      {u₂ : stageObj D (d.W j) m ⟶ T₂} (k₁ : stageMap D (d.W j) (y ≫ ek) ≫ s₁ = u₁)
      (k₂ : stageMap D (d.W j) (y ≫ ek) ≫ s₂ = u₂),
      IsIso (transport (stageMap D (d.W j) (y ≫ ek)) k₁ k₂ Ψ) := by
  have {a b : Over d.i₀} (f : a ⟶ b) : IsAffineHom ((stageDiagram D (d.W j)).map f) :=
    isAffineHom_stageMap D (d.W j) f
  have (a : Over d.i₀) : CompactSpace ((stageDiagram D (d.W j)).obj a) :=
    compactSpace_stageObj D (d.W j) (d.finitePresentation j) a
  have (a : Over d.i₀) : QuasiSeparatedSpace ((stageDiagram D (d.W j)).obj a) :=
    quasiSeparatedSpace_stageObj D (d.W j) (d.finitePresentation j) a
  rw [isIso_transport_iff] at h
  obtain ⟨k, ek, hk⟩ :=
    @Stacks.AlgebraicGeometry.ModuleLimits.exists_isIso_pullback_map_of_isLimit _ _ _
      (stageDiagram D (d.W j)) _ (legCone D (d.W j) c (X.obj j) (d.g j) (d.isPullback j))
      (isLimitLegCone D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) hc) _ _ a _ _ hA hB Ψ h
  refine ⟨k, ek, fun {m} y u₁ u₂ k₁ k₂ => ?_⟩
  have : IsIso ((Scheme.Modules.pullback (stageMap D (d.W j) ek)).map Ψ) := hk
  rw [isIso_transport_iff]
  exact (Stacks.AlgebraicGeometry.ModuleLimits.isIso_pullback_map_comp_iff (stageMap D (d.W j) y)
    (stageMap D (d.W j) ek) _ (stageMap_comp D (d.W j) y ek).symm Ψ).mp inferInstance

end Limit

namespace MapStageData

variable (ms : MapStageData md μ)

/-- At the limit, the model of `μ (𝟙 e)` is the identification along the model of the identity
arrow. -/
theorem transport_proj_Ψ_id
    (hμid : ∀ e, μ (𝟙 e) = (Scheme.Modules.pullbackId _).inv.app (M e) ≫
      (Scheme.Modules.pullbackCongr (by simp)).hom.app (M e)) (e : E) :
    transport (d.proj ms.a (π.obj e)) (md.proj_stageMap_bₑ ms.ba e)
        (md.proj_stageLift_stageMap_bₑ ms.ba _ (𝟙 e)) (ms.Ψ (𝟙 e)) =
      transport (d.proj ms.a (π.obj e)) (md.proj_stageMap_bₑ ms.ba e)
        (md.proj_stageLift_stageMap_bₑ ms.ba _ (𝟙 e))
        ((Scheme.Modules.pullbackCongr (md.stageMap_eq_stageLift_id ms.ba e)).hom.app
          (md.N₀ e)) := by
  rw [ms.transport_proj, md.limitMap_id μ hμid, transport_pullbackCongr]

/-- At the limit, the model of `μ (φ ≫ ψ)` is the composite of the models. -/
theorem transport_proj_Ψ_comp
    (hμcomp : ∀ {e e' e'' : E} (φ : e ⟶ e') (ψ : e' ⟶ e''), μ (φ ≫ ψ) =
      μ φ ≫ (Scheme.Modules.pullback (X.map (π.map φ)).left).map (μ ψ) ≫
        (Scheme.Modules.pullbackComp _ _).hom.app (M e'') ≫
        (Scheme.Modules.pullbackCongr (by simp)).hom.app (M e''))
    {e e' e'' : E} (φ : e ⟶ e') (ψ : e' ⟶ e'') :
    transport (d.proj ms.a (π.obj e)) (md.proj_stageMap_bₑ ms.ba e)
        (md.proj_stageLift_stageMap_bₑ ms.ba _ (φ ≫ ψ)) (ms.Ψ (φ ≫ ψ)) =
      transport (d.proj ms.a (π.obj e)) (md.proj_stageMap_bₑ ms.ba e)
        (md.proj_stageLift_stageMap_bₑ ms.ba _ (φ ≫ ψ)) (ms.cocycleHom φ ψ) := by
  have mid₂ : d.proj ms.a (π.obj e) ≫
      stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
        stageLift (d.H (π.map ψ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e'')) (ms.ba ≫ md.bₑ e'') =
      (X.map (π.map φ)).left ≫ (X.map (π.map ψ)).left ≫ d.proj (md.mₑ e'') (π.obj e'') := by
    rw [d.proj_stageLift_assoc, d.proj_stageLift_assoc, md.proj_stageMap_bₑ]
  have key : transport (d.proj ms.a (π.obj e)) (md.proj_stageLift_stageMap_bₑ ms.ba _ φ) mid₂
      (transport (stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂)) rfl rfl
        (ms.Ψ ψ)) =
      transport (X.map (π.map φ)).left rfl rfl (md.limitMap μ ψ) := by
    have l₁ : (d.proj ms.a (π.obj e) ≫
        stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂)) ≫
          stageMap D (d.W (π.obj e')) (ms.ba ≫ md.bₑ e') =
        (X.map (π.map φ)).left ≫ d.proj (md.mₑ e') (π.obj e') := by
      rw [Category.assoc, md.proj_stageLift_stageMap_bₑ]
    have l₂ : (d.proj ms.a (π.obj e) ≫
        stageLift (d.H (π.map φ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂)) ≫
          stageLift (d.H (π.map ψ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
            stageMap D (d.W (π.obj e'')) (ms.ba ≫ md.bₑ e'') =
        (X.map (π.map φ)).left ≫ (X.map (π.map ψ)).left ≫ d.proj (md.mₑ e'') (π.obj e'') := by
      rw [Category.assoc]; exact mid₂
    have l₁' : ((X.map (π.map φ)).left ≫ d.proj ms.a (π.obj e')) ≫
        stageMap D (d.W (π.obj e')) (ms.ba ≫ md.bₑ e') =
        (X.map (π.map φ)).left ≫ d.proj (md.mₑ e') (π.obj e') := by
      rw [Category.assoc, md.proj_stageMap_bₑ]
    have l₂' : ((X.map (π.map φ)).left ≫ d.proj ms.a (π.obj e')) ≫
        stageLift (d.H (π.map ψ)) (d.H_w _) ((ms.ba ≫ md.b₃) ≫ d.b₂) ≫
          stageMap D (d.W (π.obj e'')) (ms.ba ≫ md.bₑ e'') =
        (X.map (π.map φ)).left ≫ (X.map (π.map ψ)).left ≫ d.proj (md.mₑ e'') (π.obj e'') := by
      rw [Category.assoc, md.proj_stageLift_stageMap_bₑ]
    rw [transport_transport _ rfl rfl _ _ _ l₁ l₂, ← ms.transport_proj ψ,
      transport_transport _ _ _ _ rfl rfl l₁' l₂']
    exact transport_congr (d.proj_stageLift ms.a _ (π.map φ)) _ _ _ _ _
  rw [ms.transport_proj, md.limitMap_comp μ hμcomp, cocycleHom,
    transport_comp _ _ (md.proj_stageLift_stageMap_bₑ ms.ba _ φ),
    transport_comp _ _ mid₂, ms.transport_proj, key, transport_pullbackCongr]

/-- The model of the morphism `μ φ` at a stage later than `ms.a`, as a morphism into the pullback
of the model of `M e'` along the model of the arrow. -/
def modelHom {m : Over d.i₀} (x : m ⟶ ms.a) {e e' : E} (φ : e ⟶ e') :
    md.module (x ≫ ms.ba) e ⟶ (Scheme.Modules.pullback
      ((d.diagram ((x ≫ ms.ba) ≫ md.b₃)).map (π.map φ)).left).obj (md.module (x ≫ ms.ba) e') :=
  ms.stageHom x φ ≫ (canIso (stageLift (d.H (π.map φ)) (d.H_w _) (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂))
    (stageMap D (d.W (π.obj e')) ((x ≫ ms.ba) ≫ md.bₑ e')) _ rfl (md.N₀ e')).inv

/-- `ms.modelHom x φ` is `ms.stageHom x φ` followed by the inverse of the canonical isomorphism
of iterated pullbacks. -/
theorem modelHom_def {m : Over d.i₀} (x : m ⟶ ms.a) {e e' : E} (φ : e ⟶ e') :
    ms.modelHom x φ = ms.stageHom x φ ≫ (canIso (stageLift (d.H (π.map φ)) (d.H_w _)
      (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂)) (stageMap D (d.W (π.obj e')) ((x ≫ ms.ba) ≫ md.bₑ e'))
        _ rfl (md.N₀ e')).inv := rfl

/-- The unit condition for the model morphisms. -/
theorem modelHom_id {m : Over d.i₀} (x : m ⟶ ms.a) (e : E)
    (hu : ms.stageHom x (𝟙 e) = (Scheme.Modules.pullbackCongr
      (md.stageMap_eq_stageLift_id (x ≫ ms.ba) e)).hom.app (md.N₀ e))
    (h : 𝟙 _ = ((d.diagram ((x ≫ ms.ba) ≫ md.b₃)).map (π.map (𝟙 e))).left) :
    ms.modelHom x (𝟙 e) = (Scheme.Modules.pullbackId _).inv.app (md.module (x ≫ ms.ba) e) ≫
      (Scheme.Modules.pullbackCongr h).hom.app (md.module (x ≫ ms.ba) e) := by
  rw [modelHom_def, hu]
  exact pullbackCongr_comp_canIso_inv h _ _

/-- The cocycle condition for the model morphisms. -/
theorem modelHom_comp {m : Over d.i₀} (x : m ⟶ ms.a) {e e' e'' : E} (φ : e ⟶ e')
    (ψ : e' ⟶ e'')
    (hc : ms.stageHom x (φ ≫ ψ) = ms.stageHom x φ ≫ transport (stageLift (d.H (π.map φ))
      (d.H_w _) (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂)) rfl rfl (ms.stageHom x ψ) ≫
        (Scheme.Modules.pullbackCongr
          (md.stageLift_stageLift_stageMap (x ≫ ms.ba) φ ψ)).hom.app (md.N₀ e''))
    (hF : ((d.diagram ((x ≫ ms.ba) ≫ md.b₃)).map (π.map φ)).left ≫
      ((d.diagram ((x ≫ ms.ba) ≫ md.b₃)).map (π.map ψ)).left =
        ((d.diagram ((x ≫ ms.ba) ≫ md.b₃)).map (π.map (φ ≫ ψ))).left) :
    ms.modelHom x (φ ≫ ψ) = ms.modelHom x φ ≫
      (Scheme.Modules.pullback ((d.diagram ((x ≫ ms.ba) ≫ md.b₃)).map (π.map φ)).left).map
        (ms.modelHom x ψ) ≫ (Scheme.Modules.pullbackComp _ _).hom.app _ ≫
        (Scheme.Modules.pullbackCongr hF).hom.app (md.module (x ≫ ms.ba) e'') := by
  have hF' : stageLift (d.H (π.map φ)) (d.H_w _) (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) ≫
      stageLift (d.H (π.map ψ)) (d.H_w _) (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) =
        stageLift (d.H (π.map (φ ≫ ψ))) (d.H_w _) (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂) := hF
  rw [modelHom_def, modelHom_def, modelHom_def]
  exact comp_canIso_inv_eq (stageLift (d.H (π.map φ)) (d.H_w _) (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂))
    (stageLift (d.H (π.map ψ)) (d.H_w _) (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂)) hF' _ _ _ _ _ _ _ hc

/-- **The model morphisms pull back to the given morphisms**, through the identifications of the
pullbacks of the models of the modules. -/
theorem modelHom_descent {m : Over d.i₀} (x : m ⟶ ms.a) {e e' : E} (φ : e ⟶ e') :
    (md.moduleIso (x ≫ ms.ba) e).inv ≫
        (Scheme.Modules.pullback (d.proj m (π.obj e))).map (ms.modelHom x φ) ≫
        (Scheme.Modules.pullbackComp (d.proj m (π.obj e))
          ((d.diagram ((x ≫ ms.ba) ≫ md.b₃)).map (π.map φ)).left).hom.app _ ≫
        (Scheme.Modules.pullbackCongr (d.proj_map ((x ≫ ms.ba) ≫ md.b₃) (π.map φ))).inv.app _ ≫
        (Scheme.Modules.pullbackComp (X.map (π.map φ)).left (d.proj m (π.obj e'))).inv.app _ ≫
        (Scheme.Modules.pullback (X.map (π.map φ)).left).map (md.moduleIso (x ≫ ms.ba) e').hom =
      μ φ := by
  rw [modelHom_def]
  exact descent_eq _ _ _ _ (d.proj_map ((x ≫ ms.ba) ≫ md.b₃) (π.map φ)) _ _
    (md.proj_stageMap_bₑ (x ≫ ms.ba) e) (md.proj_stageMap_bₑ (x ≫ ms.ba) e')
    (md.proj_stageLift_stageMap_bₑ (x ≫ ms.ba) _ φ) (md.θ₀ e) (md.θ₀ e') _ _
    (md.moduleIso_hom (x ≫ ms.ba) e) (md.moduleIso_hom (x ≫ ms.ba) e') (μ φ) (ms.stageHom x φ)
    ((ms.transport_proj_stageHom x φ).trans (by rw [ModuleStageData.limitMap]))

variable [IsCofiltered I] [∀ i j : I, Subsingleton (i ⟶ j)]
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- **From some stage on, the models of the morphisms satisfy the unit and cocycle conditions**
(Stacks 01ZR (3)): there is a stage at and after which the models of `μ (𝟙 e)` and
`μ (φ ≫ ψ)` satisfy the unit and cocycle conditions. -/
theorem exists_unit_cocycle (hc : IsLimit c) [FinCategory E]
    (hμid : ∀ e, μ (𝟙 e) = (Scheme.Modules.pullbackId _).inv.app (M e) ≫
      (Scheme.Modules.pullbackCongr (by simp)).hom.app (M e))
    (hμcomp : ∀ {e e' e'' : E} (φ : e ⟶ e') (ψ : e' ⟶ e''), μ (φ ≫ ψ) =
      μ φ ≫ (Scheme.Modules.pullback (X.map (π.map φ)).left).map (μ ψ) ≫
        (Scheme.Modules.pullbackComp _ _).hom.app (M e'') ≫
        (Scheme.Modules.pullbackCongr (by simp)).hom.app (M e'')) :
    ∃ (b : Over d.i₀) (bb : b ⟶ ms.a), ∀ {m : Over d.i₀} (bm : m ⟶ b),
      (∀ e, ms.stageHom (bm ≫ bb) (𝟙 e) = (Scheme.Modules.pullbackCongr
          (md.stageMap_eq_stageLift_id ((bm ≫ bb) ≫ ms.ba) e)).hom.app (md.N₀ e)) ∧
      (∀ {e e' e'' : E} (φ : e ⟶ e') (ψ : e' ⟶ e''), ms.stageHom (bm ≫ bb) (φ ≫ ψ) =
        ms.stageHom (bm ≫ bb) φ ≫ transport (stageLift (d.H (π.map φ)) (d.H_w _)
          ((((bm ≫ bb) ≫ ms.ba) ≫ md.b₃) ≫ d.b₂)) rfl rfl (ms.stageHom (bm ≫ bb) ψ) ≫
        (Scheme.Modules.pullbackCongr
          (md.stageLift_stageLift_stageMap ((bm ≫ bb) ≫ ms.ba) φ ψ)).hom.app (md.N₀ e'')) := by
  classical
  have hu : ∀ e : E, ∃ (k : Over d.i₀) (ek : k ⟶ ms.a), ∀ {m : Over d.i₀} (x : m ⟶ ms.a)
      (_ : m ⟶ k), ms.stageHom x (𝟙 e) = (Scheme.Modules.pullbackCongr
          (md.stageMap_eq_stageLift_id (x ≫ ms.ba) e)).hom.app (md.N₀ e) := fun e => by
    have := md.isFinitePresentation e
    obtain ⟨k, ek, hk⟩ := d.exists_stageMap_transport_eq hc (π.obj e) _ _
      (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ (md.N₀ e))
      (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ (md.N₀ e))
      _ _ _ _ (ms.transport_proj_Ψ_id hμid e)
    refine ⟨k, ek, fun {m} x y => ?_⟩
    obtain rfl : x = y ≫ ek := Subsingleton.elim _ _
    rw [stageHom_def, hk y, transport_pullbackCongr_of_eq _ _ _ _
      (md.stageMap_eq_stageLift_id ((y ≫ ek) ≫ ms.ba) e)]
  have hco : ∀ (e e' e'' : E) (φ : e ⟶ e') (ψ : e' ⟶ e''), ∃ (k : Over d.i₀)
      (ek : k ⟶ ms.a), ∀ {m : Over d.i₀} (x : m ⟶ ms.a) (_ : m ⟶ k),
      ms.stageHom x (φ ≫ ψ) =
        ms.stageHom x φ ≫ transport (stageLift (d.H (π.map φ)) (d.H_w _)
          (((x ≫ ms.ba) ≫ md.b₃) ≫ d.b₂)) rfl rfl (ms.stageHom x ψ) ≫
        (Scheme.Modules.pullbackCongr
          (md.stageLift_stageLift_stageMap (x ≫ ms.ba) φ ψ)).hom.app (md.N₀ e'') :=
      fun e e' e'' φ ψ => by
    have := md.isFinitePresentation e
    have := md.isFinitePresentation e''
    obtain ⟨k, ek, hk⟩ := d.exists_stageMap_transport_eq hc (π.obj e) _ _
      (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ (md.N₀ e))
      (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ (md.N₀ e''))
      _ _ _ _ (ms.transport_proj_Ψ_comp hμcomp φ ψ)
    refine ⟨k, ek, fun {m} x y => ?_⟩
    obtain rfl : x = y ≫ ek := Subsingleton.elim _ _
    rw [stageHom_def ms _ (φ ≫ ψ), hk y, ← stageHom_comp_transport_stageHom]
  choose ku eku hku using hu
  choose kc ekc hkc using hco
  obtain ⟨b, hb⟩ := IsCofiltered.inf_objs_exists
    (insert ms.a (Finset.univ.image ku ∪ Finset.univ.image
      (fun x : Σ (e e' e'' : E), (e ⟶ e') × (e' ⟶ e'') =>
        kc x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)))
  have bu : ∀ e, b ⟶ ku e := fun e => (hb (Finset.mem_insert_of_mem (Finset.mem_union_left _
    (Finset.mem_image_of_mem _ (Finset.mem_univ e))))).some
  have bc : ∀ {e e' e'' : E} (φ : e ⟶ e') (ψ : e' ⟶ e''), b ⟶ kc e e' e'' φ ψ :=
    fun {e e' e''} φ ψ => (hb (Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (Finset.mem_univ ⟨e, e', e'', φ, ψ⟩))))).some
  exact ⟨b, (hb (Finset.mem_insert_self _ _)).some, fun {m} bm =>
    ⟨fun e => hku e _ (bm ≫ bu e), fun {e e' e''} φ ψ => hkc e e' e'' φ ψ _ (bm ≫ bc φ ψ)⟩⟩

/-- **From some stage on, the model morphisms of isomorphisms are isomorphisms** (Stacks 01ZR
(2), (3)). -/
theorem exists_isIso (hc : IsLimit c) [FinCategory E] :
    ∃ (b : Over d.i₀) (bb : b ⟶ ms.a), ∀ {m : Over d.i₀} (bm : m ⟶ b) {e e' : E}
      (φ : e ⟶ e'), IsIso (μ φ) → IsIso (ms.modelHom (bm ≫ bb) φ) := by
  classical
  have key : ∀ (e e' : E) (φ : e ⟶ e'), ∃ (k : Over d.i₀) (_ : k ⟶ ms.a), IsIso (μ φ) →
      ∀ {m : Over d.i₀} (x : m ⟶ ms.a) (_ : m ⟶ k), IsIso (ms.modelHom x φ) := by
    intro e e' φ
    by_cases hφ : IsIso (μ φ)
    · have := md.isFinitePresentation e
      have := md.isFinitePresentation e'
      have hl : IsIso (transport (d.proj ms.a (π.obj e)) (md.proj_stageMap_bₑ ms.ba e)
          (md.proj_stageLift_stageMap_bₑ ms.ba _ φ) (ms.Ψ φ)) := by
        rw [ms.transport_proj, ModuleStageData.limitMap]
        infer_instance
      obtain ⟨k, ek, hk⟩ := d.exists_stageMap_isIso_transport hc (π.obj e) _ _
        (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ (md.N₀ e))
        (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback _ (md.N₀ e'))
        _ _ _ hl
      refine ⟨k, ek, fun _ {m} x y => ?_⟩
      obtain rfl : x = y ≫ ek := Subsingleton.elim _ _
      rw [modelHom_def, stageHom_def]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _
        (hk y (ms.stageMap_stageMap_bₑ _ e) (ms.stageMap_stageLift_stageMap_bₑ _ φ))
        (Iso.isIso_inv _)
    · exact ⟨ms.a, 𝟙 _, fun h => absurd h hφ⟩
  choose k ek hk using key
  obtain ⟨b, hb⟩ := IsCofiltered.inf_objs_exists (insert ms.a (Finset.univ.image
    (fun x : Σ (e e' : E), (e ⟶ e') => k x.1 x.2.1 x.2.2)))
  have bk : ∀ {e e' : E} (φ : e ⟶ e'), b ⟶ k e e' φ := fun {e e'} φ =>
    (hb (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ ⟨e, e', φ⟩)))).some
  exact ⟨b, (hb (Finset.mem_insert_self _ _)).some, fun {m} bm {e e'} φ hφ =>
    hk e e' φ hφ _ (bm ≫ bk φ)⟩

end MapStageData

end MapStageData

end MMP.CoefficientModels

end
