module

public import MMP.AlgebraicGeometry.SpreadingOut.CoefficientModelsModules
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackCanonical
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.LocalDescentRefine
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.EventualMapEq

/-!
# Spreading out morphisms between pulled-back modules

A morphism `Ψ : s₁^* A ⟶ s₂^* B` between pullbacks of two modules along morphisms `s₁, s₂` out of
a scheme `W` pulls back along `r : V ⟶ W` to a morphism `(r ≫ s₁)^* A ⟶ (r ≫ s₂)^* B`, the
pullback of `Ψ` conjugated by the canonical identifications of iterated pullbacks. Writing the
morphisms of a system of modules on the stages of a cofiltered limit in this form, with `A` and
`B` fixed modules on fixed stage schemes, makes moving to a later stage, and to the limit,
functorial on the nose.

## Main definitions

* `MMP.CoefficientModels.transport`: the pullback of `Ψ : s₁^* A ⟶ s₂^* B` along `r`, as a
  morphism `t₁^* A ⟶ t₂^* B` for given composites `r ≫ s₁ = t₁` and `r ≫ s₂ = t₂`.
* `MMP.CoefficientModels.ModuleStageData.limitMap`: the morphisms `μ φ` of a system of modules,
  written between the pullbacks of the models of the modules to the limit.
* `MMP.CoefficientModels.MapStageData`: models of the morphisms of a system of modules at a
  stage, whose transports to the limit are the given morphisms.

## Main results

* `MMP.CoefficientModels.transport_comp` and `MMP.CoefficientModels.transport_transport`:
  transport respects composition of morphisms and composition of the morphisms of schemes.
* `MMP.CoefficientModels.exists_transport_eq_of_isLimit`: a morphism at the limit of a
  cofiltered diagram between pullbacks of modules of finite presentation on a stage is the
  transport of a morphism at a later stage (Stacks 01ZR (2)).
* `MMP.CoefficientModels.exists_transport_eq_transport_of_isLimit`: two morphisms at a stage
  whose transports to the limit agree have equal transports to a later stage (Stacks 01ZR (3)).
* `MMP.CoefficientModels.ModuleStageData.limitMap_id` and
  `MMP.CoefficientModels.ModuleStageData.limitMap_comp`: the unit and cocycle conditions of the
  system, in this form.
* `MMP.CoefficientModels.exists_mapStageData`: the morphisms of a finite system of modules of
  finite presentation have models (Stacks 01ZR (2)).

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

variable {U V W T₁ T₂ T₃ : Scheme.{u}} {A : T₁.Modules} {B : T₂.Modules} {C : T₃.Modules}

/-- The pullback along `r : V ⟶ W` of a morphism `Ψ : s₁^* A ⟶ s₂^* B`, written as a morphism
`t₁^* A ⟶ t₂^* B` for given composites `r ≫ s₁ = t₁` and `r ≫ s₂ = t₂`. -/
def transport (r : V ⟶ W) {s₁ : W ⟶ T₁} {s₂ : W ⟶ T₂} {t₁ : V ⟶ T₁} {t₂ : V ⟶ T₂}
    (h₁ : r ≫ s₁ = t₁) (h₂ : r ≫ s₂ = t₂)
    (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B) :
    (Scheme.Modules.pullback t₁).obj A ⟶ (Scheme.Modules.pullback t₂).obj B :=
  (canIso r s₁ t₁ h₁ A).inv ≫ (Scheme.Modules.pullback r).map Ψ ≫ canHom r s₂ t₂ h₂ B

variable (r : V ⟶ W) {s₁ : W ⟶ T₁} {s₂ : W ⟶ T₂} {s₃ : W ⟶ T₃} {t₁ : V ⟶ T₁} {t₂ : V ⟶ T₂}
  {t₃ : V ⟶ T₃} (h₁ : r ≫ s₁ = t₁) (h₂ : r ≫ s₂ = t₂) (h₃ : r ≫ s₃ = t₃)

/-- The pullback of `Ψ` along `r` is its transport conjugated by the canonical identifications. -/
theorem pullback_map_eq_transport
    (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B) :
    (Scheme.Modules.pullback r).map Ψ =
      canHom r s₁ t₁ h₁ A ≫ transport r h₁ h₂ Ψ ≫ (canIso r s₂ t₂ h₂ B).inv := by
  simp [transport, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]

/-- The canonical identification followed by the transport of `Ψ` is the pullback of `Ψ` along `r`
followed by the canonical identification. -/
@[reassoc]
theorem canHom_comp_transport
    (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B) :
    canHom r s₁ t₁ h₁ A ≫ transport r h₁ h₂ Ψ =
      (Scheme.Modules.pullback r).map Ψ ≫ canHom r s₂ t₂ h₂ B := by
  simp [transport, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]

/-- Transport along `r` respects composition of morphisms. -/
@[reassoc]
theorem transport_comp
    (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B)
    (Ψ' : (Scheme.Modules.pullback s₂).obj B ⟶ (Scheme.Modules.pullback s₃).obj C) :
    transport r h₁ h₃ (Ψ ≫ Ψ') = transport r h₁ h₂ Ψ ≫ transport r h₂ h₃ Ψ' := by
  simp [transport, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]

/-- Transport along `r` sends the identity to the identity. -/
@[simp]
theorem transport_id :
    transport r h₁ h₁ (𝟙 ((Scheme.Modules.pullback s₁).obj A)) = 𝟙 _ := by
  simp [transport, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]

/-- Two morphisms have equal transports along `r` if and only if they have equal pullbacks
along `r`. -/
theorem transport_eq_transport_iff
    (Ψ Ψ' : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B) :
    transport r h₁ h₂ Ψ = transport r h₁ h₂ Ψ' ↔
      (Scheme.Modules.pullback r).map Ψ = (Scheme.Modules.pullback r).map Ψ' := by
  rw [pullback_map_eq_transport r h₁ h₂ Ψ, pullback_map_eq_transport r h₁ h₂ Ψ',
    ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, cancel_epi, Iso.cancel_iso_inv_right]

/-- **Transport is functorial in the morphism of schemes**: transporting along `r` and then
along `r'` is transporting along `r' ≫ r`. -/
theorem transport_transport (r' : U ⟶ V) {u₁ : U ⟶ T₁} {u₂ : U ⟶ T₂} (k₁ : r' ≫ t₁ = u₁)
    (k₂ : r' ≫ t₂ = u₂) (l₁ : (r' ≫ r) ≫ s₁ = u₁) (l₂ : (r' ≫ r) ≫ s₂ = u₂)
    (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B) :
    transport r' k₁ k₂ (transport r h₁ h₂ Ψ) = transport (r' ≫ r) l₁ l₂ Ψ := by
  have c₁ := canHom_comp r' r s₁ (r' ≫ r) t₁ u₁ rfl h₁ l₁ k₁ A
  have c₂ := canHom_comp r' r s₂ (r' ≫ r) t₂ u₂ rfl h₂ l₂ k₂ B
  haveI : Epi (canHom r' r (r' ≫ r) rfl _ ≫ canHom (r' ≫ r) s₁ u₁ l₁ A) :=
    epi_comp' (IsIso.epi_of_iso _) (IsIso.epi_of_iso _)
  rw [← cancel_epi (canHom r' r (r' ≫ r) rfl _ ≫ canHom (r' ≫ r) s₁ u₁ l₁ A)]
  calc (canHom r' r (r' ≫ r) rfl _ ≫ canHom (r' ≫ r) s₁ u₁ l₁ A) ≫
        transport r' k₁ k₂ (transport r h₁ h₂ Ψ)
      = (Scheme.Modules.pullback r').map (canHom r s₁ t₁ h₁ A ≫ transport r h₁ h₂ Ψ) ≫
          canHom r' t₂ u₂ k₂ B := by
        rw [← c₁, Category.assoc, canHom_comp_transport, Functor.map_comp_assoc]
    _ = (Scheme.Modules.pullback r').map ((Scheme.Modules.pullback r).map Ψ) ≫
          canHom r' r (r' ≫ r) rfl _ ≫ canHom (r' ≫ r) s₂ u₂ l₂ B := by
        rw [canHom_comp_transport, Functor.map_comp_assoc, c₂]
    _ = (canHom r' r (r' ≫ r) rfl _ ≫ canHom (r' ≫ r) s₁ u₁ l₁ A) ≫
          transport (r' ≫ r) l₁ l₂ Ψ := by
        rw [Category.assoc, canHom_comp_transport, ← Category.assoc, ← Category.assoc,
          canHom_naturality]

omit r h₁ h₂ in
/-- Transport along equal morphisms of schemes gives the same morphism. -/
theorem transport_congr {r r' : V ⟶ W} (hr : r = r') (h₁ : r ≫ s₁ = t₁) (h₂ : r ≫ s₂ = t₂)
    (h₁' : r' ≫ s₁ = t₁) (h₂' : r' ≫ s₂ = t₂)
    (Ψ : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B) :
    transport r h₁ h₂ Ψ = transport r' h₁' h₂' Ψ := by
  subst hr
  rfl

/-- The canonical identification along the identity is `pullbackId`. -/
theorem canHom_id_left {X T : Scheme.{u}} (g : X ⟶ T) (F : T.Modules) :
    canHom (𝟙 X) g g (Category.id_comp g) F =
      (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback g).obj F) := by
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality g) F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at key
  erw [Category.comp_id] at key
  haveI : Epi ((Scheme.Modules.pullbackComp (𝟙 X) g).inv.app F) := IsIso.epi_of_iso _
  rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 X) g).inv.app F), key]
  simp [canHom, Scheme.Modules.pullbackCongr]

/-- The canonical identification `q^* g^* F ⟶ pi^* F` followed by the identification of
pullbacks along `pi = pi'` is the canonical identification `q^* g^* F ⟶ pi'^* F`. -/
theorem canHom_comp_pullbackCongr {X Y T : Scheme.{u}} (q : X ⟶ Y) (g : Y ⟶ T) {pi pi' : X ⟶ T}
    (h : q ≫ g = pi) (h' : pi = pi') (F : T.Modules) :
    canHom q g pi h F ≫ (Scheme.Modules.pullbackCongr h').hom.app F =
      canHom q g pi' (h.trans h') F := by
  subst h'
  simp [Scheme.Modules.pullbackCongr]

/-- Transport of the identification of pullbacks along equal morphisms is again such an
identification. -/
theorem transport_pullbackCongr {s₁ s₂ : W ⟶ T₁} (hs : s₁ = s₂) {t₁ t₂ : V ⟶ T₁}
    (h₁ : r ≫ s₁ = t₁) (h₂ : r ≫ s₂ = t₂) :
    transport r h₁ h₂ ((Scheme.Modules.pullbackCongr hs).hom.app A) =
      (Scheme.Modules.pullbackCongr (h₁.symm.trans (hs ▸ h₂))).hom.app A := by
  subst hs h₁ h₂
  simp [transport, Scheme.Modules.pullbackCongr, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]

end Transport

section Limit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  {T₁ T₂ : Scheme.{u}} {A : T₁.Modules} {B : T₂.Modules}

/-- **A morphism at the limit between pullbacks of modules of finite presentation on a stage is
the transport of a morphism at a later stage** (Stacks 01ZR (2)). -/
theorem exists_transport_eq_of_isLimit (hc : IsLimit c) (i : I) (s₁ : D.obj i ⟶ T₁)
    (s₂ : D.obj i ⟶ T₂) [hA : ((Scheme.Modules.pullback s₁).obj A).IsFinitePresentation]
    [hB : ((Scheme.Modules.pullback s₂).obj B).IsFinitePresentation] {t₁ : c.pt ⟶ T₁}
    {t₂ : c.pt ⟶ T₂} (h₁ : c.π.app i ≫ s₁ = t₁) (h₂ : c.π.app i ≫ s₂ = t₂)
    (φ : (Scheme.Modules.pullback t₁).obj A ⟶ (Scheme.Modules.pullback t₂).obj B) :
    ∃ (k : I) (e : k ⟶ i) (Ψ : (Scheme.Modules.pullback (D.map e ≫ s₁)).obj A ⟶
        (Scheme.Modules.pullback (D.map e ≫ s₂)).obj B),
      transport (c.π.app k) (by rw [← Category.assoc, c.w e, h₁])
        (by rw [← Category.assoc, c.w e, h₂]) Ψ = φ := by
  let φ' := canHom (c.π.app i) s₁ t₁ h₁ A ≫ φ ≫ (canIso (c.π.app i) s₂ t₂ h₂ B).inv
  obtain ⟨k, e, Φ, hΦ⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_canonical_eq_of_isLimit
    D c hc i _ _ inferInstance inferInstance φ'
  let Ψ := (canIso (D.map e) s₁ _ rfl A).inv ≫ Φ ≫ canHom (D.map e) s₂ _ rfl B
  have hΨ : canHom (D.map e) s₁ _ rfl A ≫ Ψ = Φ ≫ canHom (D.map e) s₂ _ rfl B := by
    simp [Ψ, ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]
  refine ⟨k, e, Ψ, ?_⟩
  have k₁ : c.π.app k ≫ D.map e ≫ s₁ = t₁ := by rw [← Category.assoc, c.w e, h₁]
  have k₂ : c.π.app k ≫ D.map e ≫ s₂ = t₂ := by rw [← Category.assoc, c.w e, h₂]
  have c₁ := canHom_comp (c.π.app k) (D.map e) s₁ (c.π.app i) _ t₁ (c.w e) rfl h₁ k₁ A
  have c₂ := canHom_comp (c.π.app k) (D.map e) s₂ (c.π.app i) _ t₂ (c.w e) rfl h₂ k₂ B
  haveI : Epi ((Scheme.Modules.pullback (c.π.app k)).map (canHom (D.map e) s₁ _ rfl A) ≫
      canHom (c.π.app k) _ t₁ k₁ A) :=
    epi_comp' (IsIso.epi_of_iso _) (IsIso.epi_of_iso _)
  rw [← cancel_epi ((Scheme.Modules.pullback (c.π.app k)).map (canHom (D.map e) s₁ _ rfl A) ≫
    canHom (c.π.app k) _ t₁ k₁ A), Category.assoc, canHom_comp_transport,
    ← Functor.map_comp_assoc, hΨ, Functor.map_comp_assoc, c₂, ← Category.assoc, hΦ, c₁]
  simp [φ', ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]

/-- **Two morphisms at a stage whose transports to the limit agree have equal transports to a
later stage** (Stacks 01ZR (3)). -/
theorem exists_transport_eq_transport_of_isLimit (hc : IsLimit c) (i : I) (s₁ : D.obj i ⟶ T₁)
    (s₂ : D.obj i ⟶ T₂) [hA : ((Scheme.Modules.pullback s₁).obj A).IsFinitePresentation]
    [hB : ((Scheme.Modules.pullback s₂).obj B).IsFinitePresentation] {t₁ : c.pt ⟶ T₁}
    {t₂ : c.pt ⟶ T₂} (h₁ : c.π.app i ≫ s₁ = t₁) (h₂ : c.π.app i ≫ s₂ = t₂)
    (Ψ Ψ' : (Scheme.Modules.pullback s₁).obj A ⟶ (Scheme.Modules.pullback s₂).obj B)
    (h : transport (c.π.app i) h₁ h₂ Ψ = transport (c.π.app i) h₁ h₂ Ψ') :
    ∃ (k : I) (e : k ⟶ i), transport (D.map e) rfl rfl Ψ = transport (D.map e) rfl rfl Ψ' := by
  rw [transport_eq_transport_iff] at h
  obtain ⟨k, e, he⟩ := Stacks.AlgebraicGeometry.ModuleLimits.exists_pullback_map_eq_of_isLimit
    D c hc i _ _ Ψ Ψ' h
  exact ⟨k, e, (transport_eq_transport_iff _ _ _ _ _).mpr he⟩

end Limit

/-! ### The morphisms of a system of modules, in canonical form at the limit -/

section LimitMap

/-- Pulling back the identification `M ≅ P^* N` along an endomorphism equal to the identity. -/
theorem limitMap_id_aux {X T : Scheme.{u}} {f : X ⟶ X} (hf : 𝟙 X = f) {P : X ⟶ T}
    {M : X.Modules} {N : T.Modules} (θ : M ≅ (Scheme.Modules.pullback P).obj N) :
    θ.inv ≫ (Scheme.Modules.pullbackId X).inv.app M ≫
        (Scheme.Modules.pullbackCongr hf).hom.app M ≫
        (Scheme.Modules.pullback f).map θ.hom ≫ canHom f P (f ≫ P) rfl N =
      (Scheme.Modules.pullbackCongr (by rw [← hf, Category.id_comp])).hom.app N := by
  subst hf
  have hn := (Scheme.Modules.pullbackId X).inv.naturality θ.hom
  simp only [Functor.id_map, Functor.id_obj] at hn
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  rw [← Category.assoc ((Scheme.Modules.pullbackId X).inv.app M), ← hn,
    show canHom (𝟙 X) P (𝟙 X ≫ P) rfl N = canHom (𝟙 X) P P (Category.id_comp P) N ≫
      (Scheme.Modules.pullbackCongr (Category.id_comp P).symm).hom.app N from
      (canHom_comp_pullbackCongr _ _ _ _ N).symm, canHom_id_left]
  simp [Scheme.Modules.pullbackCongr]

/-- Pulling back an identification `θ : M ≅ P^* N` along a composite `F = f ≫ g`, followed by the
canonical identification, agrees with pulling it back along `g` and then along `f`. -/
theorem limitMap_comp_aux {X X' X'' T : Scheme.{u}} (f : X ⟶ X') (g : X' ⟶ X'') {F : X ⟶ X''}
    (hF : f ≫ g = F) {P : X'' ⟶ T} {M : X''.Modules} {N : T.Modules}
    (θ : M ≅ (Scheme.Modules.pullback P).obj N) :
    (Scheme.Modules.pullbackComp f g).hom.app M ≫ (Scheme.Modules.pullbackCongr hF).hom.app M ≫
        (Scheme.Modules.pullback F).map θ.hom ≫ canHom F P (F ≫ P) rfl N =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map θ.hom) ≫
        (Scheme.Modules.pullback f).map (canHom g P (g ≫ P) rfl N) ≫
        canHom f (g ≫ P) (f ≫ g ≫ P) rfl N ≫
        (Scheme.Modules.pullbackCongr (by rw [← hF, Category.assoc])).hom.app N := by
  subst hF
  have c := canHom_comp f g P (f ≫ g) (g ≫ P) (f ≫ g ≫ P) rfl rfl (Category.assoc _ _ _) rfl N
  rw [← Category.assoc ((Scheme.Modules.pullback f).map (canHom g P (g ≫ P) rfl N)), c]
  have hn := Stacks.AlgebraicGeometry.ModuleLimits.canHom_naturality f g (f ≫ g) rfl θ.hom
  simp only [Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map θ.hom)),
    hn, Category.assoc (canHom f g (f ≫ g) rfl M), canHom_comp_pullbackCongr]
  simp [canHom, Scheme.Modules.pullbackCongr]

variable {I : Type u} [SmallCategory I] {D : I ⥤ Scheme.{u}} {c : Cone D} {n : ℕ}
  {J : Type u} [SmallCategory J] {X : J ⥤ Over c.pt}
  {ι : ∀ j, (X.obj j).left ⟶ projectiveSpaceOver n c.pt} {d : DiagramStageData D c n X ι}
  {E : Type*} [Category E] {π : E ⥤ J} {M : ∀ e, (X.obj (π.obj e)).left.Modules}
  (md : ModuleStageData d π M)
  (μ : ∀ {e e' : E} (φ : e ⟶ e'),
    M e ⟶ (Scheme.Modules.pullback (X.map (π.map φ)).left).obj (M e'))

namespace ModuleStageData

/-- The morphism `μ φ`, written between the pullbacks of the models `N₀ e` and `N₀ e'` to the
limit along the projections to their stages. -/
def limitMap {e e' : E} (φ : e ⟶ e') :
    (Scheme.Modules.pullback (d.proj (md.mₑ e) (π.obj e))).obj (md.N₀ e) ⟶
      (Scheme.Modules.pullback ((X.map (π.map φ)).left ≫ d.proj (md.mₑ e') (π.obj e'))).obj
        (md.N₀ e') :=
  (md.θ₀ e).inv ≫ μ φ ≫ (Scheme.Modules.pullback (X.map (π.map φ)).left).map (md.θ₀ e').hom ≫
    canHom _ _ _ rfl (md.N₀ e')

/-- Under the unit condition on `μ`, `md.limitMap μ (𝟙 e)` is the identification of pullbacks
along equal morphisms. -/
theorem limitMap_id
    (hμid : ∀ e, μ (𝟙 e) = (Scheme.Modules.pullbackId _).inv.app (M e) ≫
      (Scheme.Modules.pullbackCongr (by simp)).hom.app (M e)) (e : E) :
    md.limitMap μ (𝟙 e) = (Scheme.Modules.pullbackCongr (by simp)).hom.app (md.N₀ e) := by
  rw [limitMap, hμid]
  simp only [Category.assoc]
  exact limitMap_id_aux _ (md.θ₀ e)

/-- Under the cocycle condition on `μ`, `md.limitMap μ (φ ≫ ψ)` is `md.limitMap μ φ` followed by
the transport of `md.limitMap μ ψ`, up to the identification of pullbacks. -/
theorem limitMap_comp
    (hμcomp : ∀ {e e' e'' : E} (φ : e ⟶ e') (ψ : e' ⟶ e''), μ (φ ≫ ψ) =
      μ φ ≫ (Scheme.Modules.pullback (X.map (π.map φ)).left).map (μ ψ) ≫
        (Scheme.Modules.pullbackComp _ _).hom.app (M e'') ≫
        (Scheme.Modules.pullbackCongr (by simp)).hom.app (M e''))
    {e e' e'' : E} (φ : e ⟶ e') (ψ : e' ⟶ e'') :
    md.limitMap μ (φ ≫ ψ) = md.limitMap μ φ ≫ transport (X.map (π.map φ)).left rfl rfl
      (md.limitMap μ ψ) ≫ (Scheme.Modules.pullbackCongr (by simp)).hom.app (md.N₀ e'') := by
  rw [limitMap, hμcomp]
  simp only [limitMap, transport, Category.assoc, Functor.map_comp,
    ← Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom, Iso.hom_inv_id_assoc,
    Iso.map_hom_inv_id_assoc]
  simp only [Stacks.AlgebraicGeometry.ModuleLimits.canIso_hom]
  rw [limitMap_comp_aux _ _ _ (md.θ₀ e'')]

/-! ### Spreading out the morphisms of a system of modules -/

/-- The projection to the model at a stage `m` later than `md.m₃`, followed by the transition
to the stage `md.mₑ e`, is the projection to the model at `md.mₑ e`. -/
theorem proj_stageMap_bₑ {m : Over d.i₀} (bm : m ⟶ md.m₃) (e : E) :
    d.proj m (π.obj e) ≫ stageMap D (d.W (π.obj e)) (bm ≫ md.bₑ e) =
      d.proj (md.mₑ e) (π.obj e) :=
  d.proj_stageMap m _ _

/-- For an arrow `φ : e ⟶ e'`, the projection to the model at a stage `m` later than `md.m₃`,
followed by the model of `π.map φ` and the transition to the stage `md.mₑ e'`, is the morphism
`(X.map (π.map φ)).left` followed by the projection to the model at `md.mₑ e'`. -/
theorem proj_stageLift_stageMap_bₑ {m : Over d.i₀} (bm : m ⟶ md.m₃) (b : m ⟶ d.m₁) {e e' : E}
    (φ : e ⟶ e') :
    d.proj m (π.obj e) ≫ stageLift (d.H (π.map φ)) (d.H_w (π.map φ)) b ≫
        stageMap D (d.W (π.obj e')) (bm ≫ md.bₑ e') =
      (X.map (π.map φ)).left ≫ d.proj (md.mₑ e') (π.obj e') := by
  rw [d.proj_stageLift_assoc, d.proj_stageMap]

end ModuleStageData

/-- Models of the morphisms `μ φ` of a system of modules with models `md`: a stage `a` later
than `md.m₃` and, for each arrow `φ : e ⟶ e'`, a morphism at the stage `a` from the model of
`M e` to the pullback of the model of `M e'` along the model of the arrow, in canonical form,
whose transport to the limit is `μ φ`. -/
structure MapStageData where
  /-- The stage at which the morphisms are modelled. -/
  a : Over d.i₀
  /-- The transition from `a` to `md.m₃`. -/
  ba : a ⟶ md.m₃
  /-- The models of the morphisms. -/
  Ψ {e e' : E} (φ : e ⟶ e') :
    (Scheme.Modules.pullback (stageMap D (d.W (π.obj e)) (ba ≫ md.bₑ e))).obj (md.N₀ e) ⟶
      (Scheme.Modules.pullback (stageLift (d.H (π.map φ)) (d.H_w (π.map φ))
        ((ba ≫ md.b₃) ≫ d.b₂) ≫ stageMap D (d.W (π.obj e')) (ba ≫ md.bₑ e'))).obj (md.N₀ e')
  /-- The transport of the model `Ψ φ` to the limit is `md.limitMap μ φ`. -/
  transport_proj {e e' : E} (φ : e ⟶ e') :
    transport (d.proj a (π.obj e)) (md.proj_stageMap_bₑ ba e)
      (md.proj_stageLift_stageMap_bₑ ba _ φ) (Ψ φ) = md.limitMap μ φ

variable [IsCofiltered I] [∀ i j : I, Subsingleton (i ⟶ j)]
  [∀ {i j : I} (e : i ⟶ j), IsAffineHom (D.map e)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

namespace ModuleStageData

omit [∀ i j : I, Subsingleton (i ⟶ j)] in
/-- For an arrow `φ : e ⟶ e'`, the morphism `md.limitMap μ φ` at the limit is the transport of a
morphism at a stage later than `md.m₃`. -/
theorem exists_transport_eq_limitMap (hc : IsLimit c) {e e' : E} (φ : e ⟶ e') :
    ∃ (k : Over d.i₀) (ek : k ⟶ md.m₃)
      (Ψ : (Scheme.Modules.pullback (stageMap D (d.W (π.obj e)) ek ≫
          stageMap D (d.W (π.obj e)) (md.bₑ e))).obj (md.N₀ e) ⟶
        (Scheme.Modules.pullback (stageMap D (d.W (π.obj e)) ek ≫
          stageLift (d.H (π.map φ)) (d.H_w (π.map φ)) (md.b₃ ≫ d.b₂) ≫
            stageMap D (d.W (π.obj e')) (md.bₑ e'))).obj (md.N₀ e')),
      transport (d.proj k (π.obj e))
        (by rw [← Category.assoc, d.proj_stageMap, d.proj_stageMap])
        (by rw [← Category.assoc, d.proj_stageMap, d.proj_stageLift_assoc, d.proj_stageMap]) Ψ =
      md.limitMap μ φ := by
  let j := π.obj e
  have {a b : Over d.i₀} (f : a ⟶ b) : IsAffineHom ((stageDiagram D (d.W j)).map f) :=
    isAffineHom_stageMap D (d.W j) f
  have (a : Over d.i₀) : CompactSpace ((stageDiagram D (d.W j)).obj a) :=
    compactSpace_stageObj D (d.W j) (d.finitePresentation j) a
  have (a : Over d.i₀) : QuasiSeparatedSpace ((stageDiagram D (d.W j)).obj a) :=
    quasiSeparatedSpace_stageObj D (d.W j) (d.finitePresentation j) a
  have := md.isFinitePresentation e
  have := md.isFinitePresentation e'
  have h₁ := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback
    (stageMap D (d.W j) (md.bₑ e)) (md.N₀ e)
  have h₂ := Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback
    (stageLift (d.H (π.map φ)) (d.H_w (π.map φ)) (md.b₃ ≫ d.b₂) ≫
      stageMap D (d.W (π.obj e')) (md.bₑ e')) (md.N₀ e')
  exact exists_transport_eq_of_isLimit (stageDiagram D (d.W j))
    (legCone D (d.W j) c (X.obj j) (d.g j) (d.isPullback j))
    (isLimitLegCone D (d.W j) c (X.obj j) (d.g j) (d.isPullback j) hc) md.m₃
    (stageMap D (d.W j) (md.bₑ e))
    (stageLift (d.H (π.map φ)) (d.H_w (π.map φ)) (md.b₃ ≫ d.b₂) ≫
      stageMap D (d.W (π.obj e')) (md.bₑ e'))
    (hA := h₁) (hB := h₂) (d.proj_stageMap md.m₃ (md.bₑ e) j)
    ((d.proj_stageLift_assoc md.m₃ _ (π.map φ) _).trans (congrArg _ (d.proj_stageMap _ _ _)))
    (md.limitMap μ φ)

end ModuleStageData

/-- **The morphisms of a finite system of modules of finite presentation on the diagram have
models** (Stacks 01ZR (2)). -/
theorem exists_mapStageData (hc : IsLimit c) [FinCategory E] :
    Nonempty (MapStageData md μ) := by
  classical
  choose k ek Ψ' hΨ' using fun e e' (φ : e ⟶ e') => md.exists_transport_eq_limitMap μ hc φ
  obtain ⟨a, ha⟩ := IsCofiltered.inf_objs_exists
    (insert md.m₃ (Finset.univ.image fun x : Σ (e : E) (e' : E), (e ⟶ e') => k x.1 x.2.1 x.2.2))
  have ba : a ⟶ md.m₃ := (ha (Finset.mem_insert_self _ _)).some
  have bk : ∀ e e' (φ : e ⟶ e'), a ⟶ k e e' φ := fun e e' φ =>
    (ha (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Finset.mem_univ ⟨e, e', φ⟩)))).some
  refine ⟨⟨a, ba, fun {e e'} φ => transport (stageMap D (d.W (π.obj e)) (bk e e' φ)) ?_ ?_
    (Ψ' e e' φ), fun {e e'} φ => ?_⟩⟩
  · rw [← Category.assoc, ← stageMap_comp, ← stageMap_comp]
    exact congrArg _ (Subsingleton.elim _ _)
  · rw [← Category.assoc, ← stageMap_comp, ← Category.assoc,
      ← stageLift_stageMap (d.H (π.map φ)) (d.H_w (π.map φ)) (bk e e' φ ≫ ek e e' φ)
        (md.b₃ ≫ d.b₂) ((ba ≫ md.b₃) ≫ d.b₂) (Subsingleton.elim _ _),
      Category.assoc, ← stageMap_comp]
    exact congrArg (_ ≫ ·) (congrArg _ (Subsingleton.elim _ _))
  · rw [transport_transport, ← hΨ' e e' φ]
    · exact transport_congr (d.proj_stageMap a _ _) _ _ _ _ _
    · rw [d.proj_stageMap, ← Category.assoc, d.proj_stageMap, d.proj_stageMap]
    · rw [d.proj_stageMap, ← Category.assoc, d.proj_stageMap, d.proj_stageLift_assoc,
        d.proj_stageMap]

end LimitMap

end MMP.CoefficientModels

end
