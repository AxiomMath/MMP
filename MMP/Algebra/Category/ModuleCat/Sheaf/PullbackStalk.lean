module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStalkColimit

/-!
# The stalk of a pullback of sheaves of modules on ringed spaces

Let `g : T → T'` be a continuous map, `R` and `R'` sheaves of commutative rings on `T` and `T'`,
and `φ : R' ⟶ g_* R` a morphism of sheaves of rings, inducing `ψ : R'_{g x} → R_x` on stalks.
For any left adjoint `F` of the pushforward `g_*` of sheaves of modules along `φ` (for instance
Mathlib's `SheafOfModules.pullback φ`), the stalk of `F N` at `x` is

`(F N)_x ≅ R_x ⊗_{R'_{g x}} N_{g x}`,

naturally in `N`, and the isomorphism sends `1 ⊗ germ t` to the germ of the section of `F N`
attached to `t` by the unit of the adjunction.

The argument is formal. The stalk functor at `x` on sheaves of `R`-modules is left adjoint to
the skyscraper functor at `x`; the pushforward of the skyscraper at `x` with value `A` is the
skyscraper at `g x` with value `A` read over `R'_{g x}` along `ψ`; so the two composites
`F ⋙ stalk_x` and `stalk_{g x} ⋙ extendScalars ψ` have isomorphic right adjoints, and
conjugation identifies them.

## Main definitions

* `MMP.ModuleSkyscraper.skySheaf`, `MMP.ModuleSkyscraper.skySheafFunctor`: the skyscraper sheaf
  of modules at a point.
* `MMP.ModuleSkyscraper.sheafStalkFunctor`: the stalk functor on sheaves of modules, valued in
  modules over the stalk of the commutative ring sheaf.
* `MMP.ModuleSkyscraper.sheafStalkSkyAdjunction`: the stalk functor is left adjoint to the
  skyscraper functor.
* `MMP.ModuleSkyscraper.pushforwardSkyIso`: the pushforward of a skyscraper is a skyscraper.
* `MMP.ModuleSkyscraper.stalkIso`: the stalk formula.

## Main results

* `MMP.ModuleSkyscraper.stalkIso_hom_app_one_tmul_germ`: the stalk formula on `1 ⊗ germ t`.

## Implementation notes

For schemes the same argument is carried out in StacksDraft
(`Stacks.ModuleSkyscraper.pullbackStalkIso`); here the spaces are arbitrary topological spaces
with sheaves of commutative rings, the morphism of ring sheaves is arbitrary, and the left
adjoint of the pushforward is any one, as needed for ringed spaces that are not schemes.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Stacks.ModuleSkyscraper
open scoped ChangeOfRings

universe u

namespace MMP.ModuleSkyscraper

section Sky

variable {T : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} T) (x : T)

/-- The sheaf of rings underlying a sheaf of commutative rings. -/
abbrev ringSheaf : TopCat.Sheaf RingCat.{u} T :=
  (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R

/-- The skyscraper sheaf of `R`-modules at `x` with value `A`. -/
def skySheaf (A : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R.obj x)) :
    SheafOfModules.{u} (ringSheaf R) :=
  ⟨skyPresheaf A, skyAb_isSheaf x ↑A⟩

/-- The skyscraper functor at `x` into sheaves of `R`-modules. -/
def skySheafFunctor :
    ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R.obj x) ⥤
      SheafOfModules.{u} (ringSheaf R) where
  obj A := skySheaf R x A
  map φ := ⟨(skyPresheafFunctor R.obj x).map φ⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The stalk functor at `x` on sheaves of `R`-modules, valued in modules over `R_x`. -/
def sheafStalkFunctor :
    SheafOfModules.{u} (ringSheaf R) ⥤
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R.obj x) :=
  SheafOfModules.forget (ringSheaf R) ⋙ presheafStalkFunctor R.obj x

/-- The stalk functor on sheaves of modules is left adjoint to the skyscraper functor. -/
def sheafStalkSkyAdjunction : sheafStalkFunctor R x ⊣ skySheafFunctor R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M A ↦ (homEquivSky M.val A).trans
        { toFun := fun β ↦ ⟨β⟩
          invFun := fun β ↦ β.val
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      homEquiv_naturality_left_symm := fun f g ↦ fromStalkLinear_comp (x := x) f.val g.val
      homEquiv_naturality_right := fun _ _ ↦ rfl }

end Sky

section Pushforward

variable {T T' : TopCat.{u}} (g : T ⟶ T') {R : TopCat.Sheaf CommRingCat.{u} T}
  {R' : TopCat.Sheaf CommRingCat.{u} T'}
  [(Opens.map g).IsContinuous (Opens.grothendieckTopology T') (Opens.grothendieckTopology T)]
  (φ : ringSheaf R' ⟶ ((Opens.map g).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology T') (Opens.grothendieckTopology T)).obj (ringSheaf R))
  (x : T) (ψ : TopCat.Presheaf.stalk (C := CommRingCat.{u}) R'.obj (g x) →+*
    TopCat.Presheaf.stalk (C := CommRingCat.{u}) R.obj x)
  (hψ : ∀ (V : Opens T') (hx : g x ∈ V) (r : R'.obj.obj (op V)),
    ψ (TopCat.Presheaf.germ (C := CommRingCat.{u}) R'.obj V (g x) hx r) =
      TopCat.Presheaf.germ (C := CommRingCat.{u}) R.obj ((Opens.map g).obj V) x hx
        (φ.hom.app (op V) r))

include hψ

/-- The pushforward of the skyscraper at `x` with value `A` is the skyscraper at `g x` with
value `A` read over `R'_{g x}` along `ψ`. -/
def pushforwardSkyObjIso
    (A : ModuleCat.{u} (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R.obj x)) :
    (SheafOfModules.pushforward.{u} φ).obj (skySheaf R x A) ≅
      skySheaf R' (g x) ((ModuleCat.restrictScalars ψ).obj A) where
  hom := ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun s p ↦ s ⟨p.down⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl } }
    (fun V r s ↦ funext fun p ↦ by
      change (TopCat.Presheaf.germ (C := CommRingCat.{u}) R.obj ((Opens.map g).obj V.unop) x
          p.down).hom (φ.hom.app V r) • s ⟨p.down⟩ =
        ψ ((TopCat.Presheaf.germ (C := CommRingCat.{u}) R'.obj V.unop (g x) p.down).hom r) •
          s ⟨p.down⟩
      rw [hψ V.unop p.down r])⟩
  inv := ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        { toFun := fun s p ↦ s ⟨p.down⟩
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl } }
    (fun V r s ↦ funext fun p ↦ by
      change ψ ((TopCat.Presheaf.germ (C := CommRingCat.{u}) R'.obj V.unop (g x) p.down).hom r) •
          s ⟨p.down⟩ =
        (TopCat.Presheaf.germ (C := CommRingCat.{u}) R.obj ((Opens.map g).obj V.unop) x
          p.down).hom (φ.hom.app V r) • s ⟨p.down⟩
      rw [hψ V.unop p.down r])⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- `pushforwardSkyObjIso`, naturally in the value. -/
def pushforwardSkyIso :
    skySheafFunctor R x ⋙ SheafOfModules.pushforward.{u} φ ≅
      ModuleCat.restrictScalars ψ ⋙ skySheafFunctor R' (g x) :=
  NatIso.ofComponents (pushforwardSkyObjIso g φ x ψ hψ) (fun _ ↦ rfl)

variable {F : SheafOfModules.{u} (ringSheaf R') ⥤ SheafOfModules.{u} (ringSheaf R)}
  (adj : F ⊣ SheafOfModules.pushforward.{u} φ)

/-- **The stalk of a pullback** (Stacks 0098). For a left adjoint `F` of the pushforward along
`φ`, the stalk of `F N` at `x` is `R_x ⊗_{R'_{g x}} N_{g x}`, naturally in `N`. -/
def stalkIso :
    sheafStalkFunctor R' (g x) ⋙ ModuleCat.extendScalars ψ ≅ F ⋙ sheafStalkFunctor R x :=
  (conjugateIsoEquiv (adj.comp (sheafStalkSkyAdjunction R x))
    ((sheafStalkSkyAdjunction R' (g x)).comp (ModuleCat.extendRestrictScalarsAdj ψ))).symm
    (pushforwardSkyIso g φ x ψ hψ)

/-- **The stalk formula on a unital tensor.** For a section `t` of `N` over an open `V`
containing `g x`, the stalk formula sends `1 ⊗ germ_{g x} t` to the germ at `x` of the section
of `F N` attached to `t` by the unit of `F ⊣ g_*`. -/
theorem stalkIso_hom_app_one_tmul_germ (N : SheafOfModules.{u} (ringSheaf R'))
    (V : Opens T') (hx : g x ∈ V) (t : N.val.obj (op V)) :
    ((stalkIso g φ x ψ hψ adj).hom.app N).hom
        ((1 : TopCat.Presheaf.stalk (C := CommRingCat.{u}) R.obj x) ⊗ₜ[
          TopCat.Presheaf.stalk (C := CommRingCat.{u}) R'.obj (g x), ψ]
          ((TopCat.Presheaf.germ N.val.presheaf V (g x) hx).hom t)) =
      (TopCat.Presheaf.germ (F.obj N).val.presheaf ((Opens.map g).obj V) x hx).hom
        (((adj.unit.app N).val.app (op V)).hom t) := by
  have h := unit_conjugateEquiv (adj.comp (sheafStalkSkyAdjunction R x))
    ((sheafStalkSkyAdjunction R' (g x)).comp (ModuleCat.extendRestrictScalarsAdj ψ))
    (stalkIso g φ x ψ hψ adj).hom N
  have hc : conjugateEquiv (adj.comp (sheafStalkSkyAdjunction R x))
      ((sheafStalkSkyAdjunction R' (g x)).comp (ModuleCat.extendRestrictScalarsAdj ψ))
      (stalkIso g φ x ψ hψ adj).hom = (pushforwardSkyIso g φ x ψ hψ).hom := by
    simp only [stalkIso, conjugateIsoEquiv_symm_apply_hom, Equiv.apply_symm_apply]
  rw [hc] at h
  exact (congrArg (fun u => (u.val.app (op V)).hom t ⟨hx⟩) h).symm

end Pushforward

section Exactness

open Limits

variable {T : TopCat.{u}} (R : TopCat.Sheaf CommRingCat.{u} T)

/-- The stalk functor on presheaves of abelian groups preserves finite limits: it is a filtered
colimit. -/
theorem preservesFiniteLimits_stalkFunctor (x : T) :
    PreservesFiniteLimits (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
  unfold TopCat.Presheaf.stalkFunctor
  have : PreservesLimits ((Functor.whiskeringLeft (OpenNhds x)ᵒᵖ (Opens T)ᵒᵖ
      AddCommGrpCat.{u}).obj (OpenNhds.inclusion x).op) := inferInstance
  exact comp_preservesFiniteLimits _ _

/-- The stalk of a sheaf of modules, read as an abelian group, is the stalk of the underlying
sheaf of abelian groups. -/
def sheafStalkFunctorCompForget₂Iso (x : T) :
    sheafStalkFunctor R x ⋙ forget₂ _ AddCommGrpCat.{u} ≅
      SheafOfModules.toSheaf.{u} (ringSheaf R) ⋙ sheafToPresheaf _ _ ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The stalk functor on sheaves of modules preserves finite limits. -/
theorem preservesFiniteLimits_sheafStalkFunctor (x : T) :
    PreservesFiniteLimits (sheafStalkFunctor R x) := by
  have := preservesFiniteLimits_stalkFunctor x
  have : PreservesFiniteLimits (sheafStalkFunctor R x ⋙ forget₂ _ AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso (sheafStalkFunctorCompForget₂Iso R x).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget₂ _ AddCommGrpCat.{u})

/-- A functor into sheaves of modules preserves finite limits as soon as its composite with
every stalk functor does: stalks detect isomorphisms. -/
theorem preservesFiniteLimits_of_forall_comp_sheafStalkFunctor {C : Type*} [Category C]
    [HasFiniteLimits C] (F : C ⥤ SheafOfModules.{u} (ringSheaf R))
    (h : ∀ x, PreservesFiniteLimits (F ⋙ sheafStalkFunctor R x)) : PreservesFiniteLimits F := by
  refine ⟨fun J _ _ ↦ ⟨fun {K} ↦ ?_⟩⟩
  suffices IsIso (limit.post K F) from preservesLimit_of_isIso_post F K
  have hx : ∀ x, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((SheafOfModules.toSheaf.{u} (ringSheaf R)).map (limit.post K F)).hom) := by
    intro x
    have := preservesFiniteLimits_sheafStalkFunctor R x
    have := h x
    have hS : IsIso ((sheafStalkFunctor R x).map (limit.post K F)) := by
      have : IsIso ((sheafStalkFunctor R x).map (limit.post K F) ≫
          limit.post (K ⋙ F) (sheafStalkFunctor R x)) := by
        rw [limit.post_post]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (limit.post (K ⋙ F) (sheafStalkFunctor R x))
    change IsIso ((forget₂ _ AddCommGrpCat.{u}).map ((sheafStalkFunctor R x).map (limit.post K F)))
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf.{u} (ringSheaf R)).map (limit.post K F)) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{u} (ringSheaf R))

end Exactness

end MMP.ModuleSkyscraper

end
