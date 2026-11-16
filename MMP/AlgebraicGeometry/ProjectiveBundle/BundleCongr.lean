module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients

/-!
# Projective bundles of isomorphic modules

An isomorphism `α : F ≅ G` of quasi-coherent modules on `X` induces an isomorphism
`𝐏(F) ≅ 𝐏(G)` of Stacks' projective bundles over `X` (`Stacks.RelativeProj.symGradedBundle`):
both represent the invertible quotients of the pullbacks of `F ≅ G` (Stacks, Tag 01O4).

* `MMP.ProjectiveBundleCongr.bundleIso`: the isomorphism `𝐏(F) ≅ 𝐏(G)`.
* `MMP.ProjectiveBundleCongr.bundleIso_hom_toBase`, `bundleIso_inv_toBase`: it lies over `X`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace MMP.ProjectiveBundleCongr

open Stacks.RelativeProj

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

variable {X : Scheme.{u}} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent] (α : F ≅ G)

/-- For a module isomorphism `α : F ≅ G` and `f : T ⟶ X`, the bijection between the morphisms
`T ⟶ 𝐏(F)` and `T ⟶ 𝐏(G)` over `f`: both classify the invertible quotients of `f^*F ≅ f^*G`. -/
def overEquiv {T : Scheme.{u}} (f : T ⟶ X) :
    { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f } ≃
      { g : T ⟶ (symGradedBundle G).scheme // g ≫ (symGradedBundle G).toBase = f } :=
  (symGradedOverEquiv ((Scheme.Modules.pullback f).obj F) (Iso.refl _)).trans
    (symGradedOverEquiv ((Scheme.Modules.pullback f).obj F)
      ((Scheme.Modules.pullback f).mapIso α)).symm

/-- The bijection `ProjectiveBundleCongr.overEquiv` is natural in the test scheme. -/
theorem overEquiv_comp {T T' : Scheme.{u}} (k : T' ⟶ T) (f : T ⟶ X)
    (g : { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f }) :
    overEquiv α (k ≫ f) ⟨k ≫ g.1, by rw [Category.assoc, g.2]⟩ =
      ⟨k ≫ (overEquiv α f g).1, by rw [Category.assoc, (overEquiv α f g).2]⟩ := by
  have hA := symGradedOverEquiv_comp ((Scheme.Modules.pullback f).obj F) (Iso.refl _) k
    ((Scheme.Modules.pullback (k ≫ f)).obj F) ((Scheme.Modules.pullbackComp k f).app F).symm g
  have hB := symGradedOverEquiv_comp ((Scheme.Modules.pullback f).obj F)
    ((Scheme.Modules.pullback f).mapIso α) k
    ((Scheme.Modules.pullback (k ≫ f)).obj F) ((Scheme.Modules.pullbackComp k f).app F).symm
    (overEquiv α f g)
  have e1 : ((Scheme.Modules.pullbackComp k f).app F).symm ≪≫
      (Scheme.Modules.pullback k).mapIso (Iso.refl ((Scheme.Modules.pullback f).obj F)) ≪≫
        (Scheme.Modules.pullbackComp k f).app F = Iso.refl _ := by
    ext1; simp
  have e2 : ((Scheme.Modules.pullbackComp k f).app F).symm ≪≫
      (Scheme.Modules.pullback k).mapIso ((Scheme.Modules.pullback f).mapIso α) ≪≫
        (Scheme.Modules.pullbackComp k f).app G = (Scheme.Modules.pullback (k ≫ f)).mapIso α := by
    ext1
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Iso.app_hom]
    rw [← Functor.comp_map, (Scheme.Modules.pullbackComp k f).hom.naturality,
      Iso.inv_hom_id_app_assoc]
  rw [e1] at hA
  rw [e2] at hB
  have hgh : symGradedOverEquiv ((Scheme.Modules.pullback f).obj F)
      ((Scheme.Modules.pullback f).mapIso α) (overEquiv α f g) =
      symGradedOverEquiv ((Scheme.Modules.pullback f).obj F) (Iso.refl _) g := by
    simp [overEquiv]
  rw [hgh, ← hA] at hB
  simp only [overEquiv, Equiv.trans_apply]
  rw [Equiv.symm_apply_eq]
  exact hB.symm

/-- Naturality of `ProjectiveBundleCongr.overEquiv`, along an equation of structure morphisms. -/
theorem overEquiv_comp_of_eq {T T' : Scheme.{u}} (k : T' ⟶ T) (f : T ⟶ X) (f' : T' ⟶ X)
    (hk : k ≫ f = f')
    (g : { g : T ⟶ (symGradedBundle F).scheme // g ≫ (symGradedBundle F).toBase = f }) :
    (overEquiv α f' ⟨k ≫ g.1, by rw [Category.assoc, g.2, hk]⟩).1 = k ≫ (overEquiv α f g).1 := by
  subst hk
  exact congrArg Subtype.val (overEquiv_comp α k f g)

/-- Naturality of the inverse of `ProjectiveBundleCongr.overEquiv`. -/
theorem overEquiv_symm_comp_of_eq {T T' : Scheme.{u}} (k : T' ⟶ T) (f : T ⟶ X) (f' : T' ⟶ X)
    (hk : k ≫ f = f')
    (g : { g : T ⟶ (symGradedBundle G).scheme // g ≫ (symGradedBundle G).toBase = f }) :
    ((overEquiv α f').symm ⟨k ≫ g.1, by rw [Category.assoc, g.2, hk]⟩).1 =
      k ≫ ((overEquiv α f).symm g).1 := by
  subst hk
  have h := overEquiv_comp α k f ((overEquiv α f).symm g)
  simp only [Equiv.apply_symm_apply] at h
  rw [← h, Equiv.symm_apply_apply]

/-- **A module isomorphism `F ≅ G` induces an isomorphism `𝐏(F) ≅ 𝐏(G)` over the base.** -/
def bundleIso : (symGradedBundle F).scheme ≅ (symGradedBundle G).scheme where
  hom := (overEquiv α (symGradedBundle F).toBase ⟨𝟙 _, Category.id_comp _⟩).1
  inv := ((overEquiv α (symGradedBundle G).toBase).symm ⟨𝟙 _, Category.id_comp _⟩).1
  hom_inv_id := by
    rw [← overEquiv_symm_comp_of_eq α _ _ _ (overEquiv α _ _).2]
    simp only [Category.comp_id, Subtype.coe_eta, Equiv.symm_apply_apply]
  inv_hom_id := by
    rw [← overEquiv_comp_of_eq α _ _ _ ((overEquiv α _).symm _).2]
    simp only [Category.comp_id, Subtype.coe_eta, Equiv.apply_symm_apply]

/-- The isomorphism `𝐏(F) ≅ 𝐏(G)` lies over `X`. -/
@[reassoc (attr := simp)]
theorem bundleIso_hom_toBase :
    (bundleIso α).hom ≫ (symGradedBundle G).toBase = (symGradedBundle F).toBase :=
  (overEquiv α (symGradedBundle F).toBase ⟨𝟙 _, Category.id_comp _⟩).2

/-- The inverse of the isomorphism `𝐏(F) ≅ 𝐏(G)` lies over `X`. -/
@[reassoc (attr := simp)]
theorem bundleIso_inv_toBase :
    (bundleIso α).inv ≫ (symGradedBundle F).toBase = (symGradedBundle G).toBase :=
  ((overEquiv α (symGradedBundle G).toBase).symm ⟨𝟙 _, Category.id_comp _⟩).2

end MMP.ProjectiveBundleCongr
