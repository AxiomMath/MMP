module

public import MMP.AlgebraicTopology.ConstantSheafSingularCohomology
public import MMP.Topology.Sheaves.GodementFlasqueResolution
public import MMP.AlgebraicTopology.SingularCohomology.CochainModels
public import MMP.Topology.Sheaves.RationalSheafForget
public import MMP.AlgebraicGeometry.Analytic.BettiRestriction
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleSheafAcyclicity
public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveResolutionDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Homology.DerivedIndexing.Composite

/-!
# Rational sheaf cohomology of the constant sheaf is singular cohomology

Let `X` be a metrizable, locally contractible space and `J^•` an injective resolution of the
constant sheaf `ℚ_X` in sheaves of `ℚ`-vector spaces on `X`. Then
`H^n(Γ(X, J^•)) ≅ H^n(X; ℚ)`, singular cohomology with rational coefficients, and these
isomorphisms are natural: for a continuous map `f : Y → X` and a map of complexes
`J^• ⟶ f_* J'^•` over the canonical morphism `ℚ_X ⟶ f_* ℚ_Y`, the induced map on cohomology of
global sections is the pullback `f^*` on singular cohomology.

In the bounded below derived category this reads `H^n(RΓ(X, ℚ_X)) ≅ H^n(X; ℚ)`, where the
pullback on the left is `RΓ(X, -)` of the structural unit `ℚ_X ⟶ Rf_* ℚ_Y` followed by
`RΓ(X, Rf_* -) ≅ RΓ(Y, -)`.

The proof forgets the `ℚ`-module structure. Forgetting is exact and preserves injective
objects, so `J^•` becomes an injective resolution of the underlying abelian sheaf of `ℚ_X`,
which is the constant abelian sheaf `ℚ`. Its cohomology is then compared with singular
cohomology by the comparison for abelian constant sheaves, and an additive isomorphism of
`ℚ`-vector spaces is `ℚ`-linear. The derived form computes `RΓ` on an injective resolution,
where the unit of the right derived functor is invertible, and compares the structural unit
with a map of resolutions in the bounded below homotopy category.

## Main results

* `MMP.Analytic.constantCommuteCompose_unit`: the identification of the constant sheaf after
  forgetting the coefficients carries the unit of one constant-sheaf adjunction to the other.
* `MMP.Analytic.exists_homology_globalSections_injectiveResolution_iso_relCohomology`: the
  natural isomorphism `H^n(Γ(X, J^•)) ≅ H^n(X; ℚ)`.
* `MMP.Analytic.exists_homology_rightDerivedFunctorPlus_globalSections_iso_relCohomology`: the
  natural isomorphism `H^n(RΓ(X, ℚ_X)) ≅ H^n(X; ℚ)` in the bounded below derived category.

## Implementation notes

Singular cohomology is `MMP.SingularCochain.relCohomology ℚ ∅ n`, the cohomology of the pair
`(X, ∅)`; `MMP.SingularCochain.relativeSingularCohomologyEquiv` identifies it with
`MMP.cohomologyWithSupports ℚ ℚ X univ n`. The isomorphisms are asserted to
exist together with their naturality, as is the comparison for abelian constant sheaves
(`MMP.Analytic.exists_sheafCohomology_constantSheaf_iso_singularCohomology`) they are built from.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite
open MMP MMP.SingularCochain MMP.Topology.SingularCochain

set_option backward.isDefEq.respectTransparency false

attribute [local instance] MMP.Analytic.globalSections_additive MMP.Analytic.pushforward_additive

namespace MMP.Analytic

/-! ### The constant sheaf after forgetting the coefficients -/

section ConstantForget

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {D B : Type*} [Category* D]
  [Category* B] [HasWeakSheafify J D] [HasWeakSheafify J B] (U : D ⥤ B)
  [J.PreservesSheafification U] [J.HasSheafCompose U] {T : C} (hT : IsTerminal T)

/-- The isomorphism `(constant sheaf M) ∘ U ≅ constant sheaf (U M)` carries the image under `U`
of the unit `M ⟶ Γ(T, M_C)` of the constant-sheaf adjunction to the unit
`U M ⟶ Γ(T, (U M)_C)`. -/
theorem constantCommuteCompose_unit (M : D) :
    U.map ((constantSheafAdj J D hT).unit.app M) ≫
        ((sheafSections J B).obj (op T)).map ((constantCommuteCompose J U).hom.app M) =
      (constantSheafAdj J B hT).unit.app (U.obj M) := by
  let adj := constantSheafAdj J D hT
  let adj' := constantSheafAdj J B hT
  let e := constantCommuteCompose J U
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  erw [adj'.left_triangle_components (U.obj M), CategoryTheory.Functor.map_comp, Category.assoc]
  have h1 := e.hom.naturality (adj.unit.app M)
  have h2 := constantSheafAdj_counit_w J U ((constantSheaf J D).obj M) hT
  simp only [Functor.comp_map] at h1
  rw [← cancel_epi (e.hom.app M)]
  erw [adj'.counit_naturality (e.hom.app M), ← Category.assoc, ← Category.assoc, ← h1]
  simp only [Category.assoc]
  erw [reassoc_of% h2, ← CategoryTheory.Functor.map_comp_assoc, adj.left_triangle_components M,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end ConstantForget

/-! ### Forgetting the `ℚ`-module structure -/

section Rational

variable {X Y : TopCat.{0}}

/-- The forgetful functor on sheaves. -/
private abbrev forgetSheaf (X : TopCat.{0}) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) X ⥤ TopCat.Sheaf AddCommGrpCat.{0} X :=
  sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0})

/-- Forgetting the `ℚ`-module structure commutes with sheafification. Supplied by name: instance
search for it does not terminate. -/
private instance (priority := high) preservesSheafification_forget (X : TopCat.{0}) :
    (Opens.grothendieckTopology X).PreservesSheafification (forget₂ (ModuleCat.{0} ℚ)
        AddCommGrpCat.{0}) :=
  GrothendieckTopology.instPreservesSheafification _ _

private instance preservesFiniteLimits_forget (X : TopCat.{0}) :
    PreservesFiniteLimits (forgetSheaf X) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteLimits_sheafCompose_forget₂.{0, 0, 0, 0} _ ℚ

private instance preservesFiniteColimits_forget (X : TopCat.{0}) :
    PreservesFiniteColimits (forgetSheaf X) :=
  Stacks.Cohomology.ModuleSheaf.preservesFiniteColimits_sheafCompose_forget₂.{0, 0, 0, 0} _ ℚ

private instance additive_forget (X : TopCat.{0}) : (forgetSheaf X).Additive :=
  Functor.additive_of_preserves_binary_products _

private instance preservesInjectiveObjects_forget (X : TopCat.{0}) :
    (forgetSheaf X).PreservesInjectiveObjects :=
  MMP.Topology.preservesInjectiveObjects_sheafCompose_forget₂_rat X

/-- The constant sheaf `ℚ_X` of `ℚ`-vector spaces. -/
private abbrev ratConst (X : TopCat.{0}) : TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- The constant abelian sheaf `ℚ_X`. -/
private abbrev abConst (X : TopCat.{0}) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (AddCommGrpCat.of ℚ)

/-- The underlying abelian sheaf of `ℚ_X` is the constant abelian sheaf `ℚ`. -/
private abbrev forgetConstIso (X : TopCat.{0}) : (forgetSheaf X).obj (ratConst X) ≅ abConst X :=
  (constantCommuteCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} ℚ)
      AddCommGrpCat.{0})).app (ModuleCat.of ℚ ℚ)

/-- The canonical morphism `f⁻¹ ℚ_X ⟶ ℚ_Y` of constant abelian sheaves. -/
private abbrev toConstAb (f : Y ⟶ X) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).obj (abConst X) ⟶ abConst Y :=
  (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f)).homEquiv
        (AddCommGrpCat.of ℚ) (abConst Y)).symm
    ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{0} isTerminalTop).unit.app
        (AddCommGrpCat.of ℚ) ≫ (abConst Y).obj.map (homOfLE le_top).op)

/-- The image of an injective resolution of `ℚ_X` is an injective resolution of the constant
abelian sheaf `ℚ`. -/
private def forgetResolution (J : InjectiveResolution (ratConst X)) :
    InjectiveResolution (abConst X) where
  cocomplex := ((forgetSheaf X).mapHomologicalComplex _).obj J.cocomplex
  injective := ((forgetSheaf X).mapInjectiveResolution J).injective
  ι := (CochainComplex.single₀ _).map (forgetConstIso X).inv ≫
    ((forgetSheaf X).mapInjectiveResolution J).ι

/-- The unit of `ℚ_X` read in abelian sheaves. -/
private lemma unit_comp_map_forgetConstIso_inv (X : TopCat.{0}) :
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop).unit.app
        (AddCommGrpCat.of ℚ) ≫
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj (op ⊤)).map
        (forgetConstIso X).inv =
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map ((constantSheafAdj
          (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)
        isTerminalTop).unit.app (ModuleCat.of ℚ ℚ)) := by
  erw [← constantCommuteCompose_unit (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{0} ℚ)
      AddCommGrpCat.{0}) isTerminalTop
    (ModuleCat.of ℚ ℚ), Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.app_inv,
        Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The main compatibility.** After forgetting, the canonical morphism `ℚ_X ⟶ f_* ℚ_Y` of
sheaves of `ℚ`-vector spaces is the adjunct of the canonical morphism `f⁻¹ ℚ_X ⟶ ℚ_Y` of
abelian sheaves. -/
private lemma forgetConstIso_inv_comp_map_constUnit (f : Y ⟶ X) :
    (forgetConstIso X).inv ≫ (forgetSheaf X).map (constUnit f) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app (abConst X) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (toConstAb f)) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (forgetConstIso Y).inv := by
  let adj₁ := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{0} isTerminalTop
  let adjP := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f
  apply (adj₁.homEquiv _ _).injective
  have hc : adj₁.homEquiv _ _ (adjP.homEquiv _ _ (toConstAb f)) =
      (constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{0} isTerminalTop).unit.app
        (AddCommGrpCat.of ℚ) ≫ (abConst Y).obj.map (homOfLE le_top).op :=
    (congrArg (fun e ↦ e (toConstAb f)) (congrFun (congrFun
      (Adjunction.comp_homEquiv adj₁ adjP) (AddCommGrpCat.of ℚ)) (abConst Y))).symm.trans
      (Equiv.apply_symm_apply _ _)
  have hres : (abConst Y).obj.map (homOfLE (le_top : (Opens.map f).obj ⊤ ≤ ⊤)).op = 𝟙 _ :=
    (abConst Y).obj.map_id _
  have hL : adj₁.homEquiv _ _ ((forgetConstIso X).inv ≫ (forgetSheaf X).map (constUnit f)) =
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map ((constantSheafAdj
        (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) isTerminalTop).unit.app
          (ModuleCat.of ℚ ℚ)) := by
    rw [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp, ← Category.assoc,
      unit_comp_map_forgetConstIso_inv]
    have hQ := homEquiv_constUnit f
    rw [Adjunction.homEquiv_unit] at hQ
    change (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map _ ≫
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map _ = _
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map hQ
  have hR : adj₁.homEquiv _ _ (((adjP.unit.app (abConst X) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (toConstAb f)) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (forgetConstIso Y).inv)) =
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map ((constantSheafAdj
        (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) isTerminalTop).unit.app
          (ModuleCat.of ℚ ℚ)) := by
    rw [adj₁.homEquiv_naturality_right, ← Adjunction.homEquiv_unit, hc, hres]
    erw [Category.comp_id]
    exact unit_comp_map_forgetConstIso_inv Y
  exact hL.trans hR.symm

/-- In degree zero, the comparison of single complexes along the forgetful functor is the
identity. -/
private lemma singleMapHomologicalComplex_inv_app_f_zero (X : TopCat.{0})
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) X) :
    ((HomologicalComplex.singleMapHomologicalComplex (forgetSheaf X) (ComplexShape.up ℕ) 0).inv.app
      F).f 0 = 𝟙 _ := by
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq]

private lemma forgetResolution_ι_f_zero (J : InjectiveResolution (ratConst X)) :
    (forgetResolution J).ι.f 0 = (forgetConstIso X).inv ≫ (forgetSheaf X).map (J.ι.f 0) := by
  change (forgetConstIso X).inv ≫ ((HomologicalComplex.singleMapHomologicalComplex (forgetSheaf X)
    (ComplexShape.up ℕ) 0).inv.app (ratConst X)).f 0 ≫ (forgetSheaf X).map (J.ι.f 0) = _
  rw [singleMapHomologicalComplex_inv_app_f_zero]
  erw [Category.id_comp]

/-- A map of resolutions over `ℚ_X ⟶ f_* ℚ_Y` is, after forgetting, a map of resolutions over
the adjunct of `f⁻¹ ℚ_X ⟶ ℚ_Y`. -/
private lemma forgetResolution_ι_f_zero_comp (f : Y ⟶ X) (J : InjectiveResolution (ratConst X))
    (J' : InjectiveResolution (ratConst Y))
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map
      (J'.ι.f 0)) :
    (forgetResolution J).ι.f 0 ≫ (((forgetSheaf X).mapHomologicalComplex _).map g).f 0 =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).unit.app (abConst X) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map (toConstAb f)) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{0} f).map ((forgetResolution J').ι.f 0) := by
  rw [forgetResolution_ι_f_zero, forgetResolution_ι_f_zero, Category.assoc,
    Functor.mapHomologicalComplex_map_f, ← CategoryTheory.Functor.map_comp, hg,
    CategoryTheory.Functor.map_comp, ← Category.assoc, forgetConstIso_inv_comp_map_constUnit,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- The comparison `H^n(Γ(X, J^•)) ≅ H^n(X; ℚ)` after forgetting the `ℚ`-module structure, built
from a comparison `E` of abelian sheaf cohomology with singular cohomology. -/
private def abIso (X : TopCat.{0}) (n : ℕ)
    (E : (sheafCohomology X n).obj (abConst X) ≅ (abCochainFunctor.obj (op X)).homology n)
    (J : InjectiveResolution (ratConst X)) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj (((((sheafSections
        (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).obj
            J.cocomplex).homology n) ≅
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj (ModuleCat.of ℚ (relCohomology ℚ
          ((Set.univ : Set X)ᶜ) n)) :=
  ((StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso (forget₂ (ModuleCat.{0}
      ℚ) AddCommGrpCat.{0})
      (ComplexShape.up ℕ) n).app _).symm ≪≫
    ((forgetResolution J).isoRightDerivedObj (globalSections X) n).symm ≪≫
    ((sheafCohomologyIso X n).app (abConst X)).symm ≪≫ E ≪≫ abCohomologyIso X n

private lemma abIso_naturality (f : Y ⟶ X) (n : ℕ)
    (EX : (sheafCohomology X n).obj (abConst X) ≅ (abCochainFunctor.obj (op X)).homology n)
    (EY : (sheafCohomology Y n).obj (abConst Y) ≅ (abCochainFunctor.obj (op Y)).homology n)
    (hE : EX.hom ≫ HomologicalComplex.homologyMap (abCochainFunctor.map f.op) n =
      sheafCohomologyPullback f (abConst X) n ≫ (sheafCohomology Y n).map (toConstAb f) ≫ EY.hom)
    (J : InjectiveResolution (ratConst X)) (J' : InjectiveResolution (ratConst Y))
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map
      (J'.ι.f 0)) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map (HomologicalComplex.homologyMap
        ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
            (op ⊤)).mapHomologicalComplex _).map g) n) ≫
        (abIso Y n EY J').hom =
      (abIso X n EX J).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map (ModuleCat.ofHom (relCohomologyMap ℚ f
            (compl_univ_subset_preimage f) n)) := by
  have h1 := (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso (forget₂
      (ModuleCat.{0} ℚ) AddCommGrpCat.{0})
    (ComplexShape.up ℕ) n).inv.naturality ((((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).map g)
  dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at h1
  have h2 := sheafCohomologyIso_pullback f (abConst X) (abConst Y) (toConstAb f)
    (forgetResolution J) (forgetResolution J') (((forgetSheaf X).mapHomologicalComplex _).map g)
    (forgetResolution_ι_f_zero_comp f J J' g hg) n
  have h2' : HomologicalComplex.homologyMap
        (((globalSections X).mapHomologicalComplex _).map
          (((forgetSheaf X).mapHomologicalComplex _).map g)) n ≫
        ((forgetResolution J').isoRightDerivedObj (globalSections Y) n).inv ≫
        (sheafCohomologyIso Y n).inv.app (abConst Y) =
      ((forgetResolution J).isoRightDerivedObj (globalSections X) n).inv ≫
        (sheafCohomologyIso X n).inv.app (abConst X) ≫
        sheafCohomologyPullback f (abConst X) n ≫ (sheafCohomology Y n).map (toConstAb f) := by
    haveI : Epi ((sheafCohomologyIso X n).hom.app (abConst X)) :=
      IsIso.epi_of_iso ((sheafCohomologyIso X n).app (abConst X)).hom
    rw [← cancel_epi ((forgetResolution J).isoRightDerivedObj (globalSections X) n).hom,
      ← cancel_epi ((sheafCohomologyIso X n).hom.app (abConst X))]
    simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id_app_assoc]
    rw [← reassoc_of% h2]
    simp [-sheafCohomologyIso_hom_app]
  simp only [abIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Category.assoc]
  erw [reassoc_of% h1]
  congr 1
  erw [reassoc_of% h2']
  rw [← reassoc_of% hE]
  erw [abCohomologyIso_hom_naturality f n]

/-- An additive isomorphism between `ℚ`-vector spaces is `ℚ`-linear. -/
private def ratIsoOfForget {M N : ModuleCat.{0} ℚ} (φ : (forget₂ (ModuleCat.{0} ℚ)
    AddCommGrpCat.{0}).obj M ≅ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj N) : M ≅ N where
  hom := ModuleCat.ofHom (AddMonoidHom.toRatLinearMap (M := M) (M₂ := N) φ.hom.hom)
  inv := ModuleCat.ofHom (AddMonoidHom.toRatLinearMap (M := N) (M₂ := M) φ.inv.hom)
  hom_inv_id := by
    ext x
    exact congrArg (fun t : (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj M ⟶ (forget₂
        (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj M ↦ t.hom x) φ.hom_inv_id
  inv_hom_id := by
    ext x
    exact congrArg (fun t : (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj N ⟶ (forget₂
        (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj N ↦ t.hom x) φ.inv_hom_id

private lemma map_ratIsoOfForget_hom {M N : ModuleCat.{0} ℚ} (φ : (forget₂ (ModuleCat.{0} ℚ)
    AddCommGrpCat.{0}).obj M ≅ (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj N) :
    (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map (ratIsoOfForget φ).hom = φ.hom := by
  ext x
  rfl

end Rational

/-- **Rational sheaf cohomology of the constant sheaf is singular cohomology, naturally.** Let
`X` be a metrizable, locally contractible space and `J^•` an injective resolution of the constant
sheaf `ℚ_X` of `ℚ`-vector spaces. Then `H^n(Γ(X, J^•)) ≅ H^n(X, ∅; ℚ)`, singular cohomology with
rational coefficients. For a continuous map `f : Y ⟶ X` between such spaces, injective
resolutions `J^•` of `ℚ_X` and `J'^•` of `ℚ_Y`, and a map of complexes `g : J^• ⟶ f_* J'^•`
over the canonical morphism `ℚ_X ⟶ f_* ℚ_Y` (`MMP.Analytic.constUnit`), the map induced by `g`
on `H^n` of global sections is the pullback `f^*` of singular cohomology. -/
theorem exists_homology_globalSections_injectiveResolution_iso_relCohomology :
    let QX : ∀ X : TopCat.{0}, TopCat.Sheaf (ModuleCat.{0} ℚ) X := fun X ↦
      (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
    ∃ e : ∀ (X : TopCat.{0}) [MetrizableSpace X], LocallyContractibleSpace X →
        ∀ (J : InjectiveResolution (QX X)) (n : ℕ),
          ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
            (op ⊤)).mapHomologicalComplex _).obj J.cocomplex).homology n ≅
            ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set X)ᶜ) n),
      ∀ (X Y : TopCat.{0}) [MetrizableSpace X] [MetrizableSpace Y]
        (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) (f : Y ⟶ X)
        (J : InjectiveResolution (QX X)) (J' : InjectiveResolution (QX Y))
        (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex
          _).obj J'.cocomplex)
        (_ : J.ι.f 0 ≫ g.f 0 =
          constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map (J'.ι.f 0)) (n : ℕ),
        HomologicalComplex.homologyMap ((((sheafSections (Opens.grothendieckTopology X)
            (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).map g) n ≫
            (e Y hY J' n).hom =
          (e X hX J n).hom ≫
            ModuleCat.ofHom (relCohomologyMap ℚ f (compl_univ_subset_preimage f) n) := by
  intro QX
  obtain ⟨E, hE⟩ := exists_sheafCohomology_constantSheaf_iso_singularCohomology
    (AddCommGrpCat.of ℚ)
  refine ⟨fun X _ hX J n ↦ ratIsoOfForget (abIso X n (E X hX n) J), ?_⟩
  intro X Y _ _ hX hY f J J' g hg n
  apply (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, map_ratIsoOfForget_hom,
    map_ratIsoOfForget_hom]
  exact abIso_naturality f n (E X hX n) (E Y hY n) (hE X Y hX hY f n) J J' g hg

end MMP.Analytic

/-! ### Bounded below right derived functors computed on injective resolutions -/

namespace MMP.Analytic

section DerivedResolution

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.DerivedIndexing

variable {A B Dc : Type*} [Category* A] [Category* B] [Category* Dc] [Abelian A] [Abelian B]
  [Abelian Dc] [EnoughInjectives A] [EnoughInjectives B]

/-- An injective resolution, as an object of the bounded below homotopy category. -/
private abbrev resPlusObj {a : A} (J : InjectiveResolution a) : HomotopyCategory.Plus A :=
  (HomotopyCategory.Plus.quotient A).obj J.plusObj

/-- The augmentation `a[0] ⟶ J^•` in the bounded below homotopy category. -/
private def resPlusι {a : A} (J : InjectiveResolution a) :
    (HomotopyCategory.Plus.singleFunctor A 0).obj a ⟶ resPlusObj J :=
  (HomotopyCategory.Plus.ι A).preimage ((HomotopyCategory.quotient A _).map J.ι')

omit [EnoughInjectives A] in
private lemma ι_map_resPlusι {a : A} (J : InjectiveResolution a) :
    (HomotopyCategory.Plus.ι A).map (resPlusι J) = (HomotopyCategory.quotient A _).map J.ι' :=
  Functor.map_preimage _ _

private instance isIso_Qh_map_resPlusι {a : A} (J : InjectiveResolution a) :
    IsIso (DerivedCategory.Plus.Qh.map (resPlusι J)) :=
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _ (by
    change HomotopyCategory.quasiIso A _ ((HomotopyCategory.Plus.ι A).map (resPlusι J))
    rw [ι_map_resPlusι, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)

/-- `H^n(RG(a[0])) ≅ H^n(G(J^•))`, for an injective resolution `J^•` of `a`, the right-hand side
read in the homotopy category of `ℕ`-indexed complexes. -/
private def resHomologyIso (G : A ⥤ Dc) [G.Additive] {a : A} (J : InjectiveResolution a)
    (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor Dc n).obj
        (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
          ((HomotopyCategory.Plus.singleFunctor A 0).obj a))) ≅
      (HomotopyCategory.homologyFunctor Dc (ComplexShape.up ℕ) n).obj
        ((G.mapHomotopyCategory (ComplexShape.up ℕ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).obj J.cocomplex)) :=
  (DerivedCategory.Plus.homologyFunctor Dc n).mapIso
      (G.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Qh.map (resPlusι J))) ≪≫
        (asIso (G.rightDerivedFunctorPlusUnith.app (resPlusObj J))).symm) ≪≫
    (plusHomologyIso (D := Dc) (n : ℤ)).app (G.mapHomotopyCategoryPlus.obj (resPlusObj J)) ≪≫
    (extendMapHomologyIso G J.cocomplex n).symm

/-- A map of complexes `J^• ⟶ F(J'^•)`, in the bounded below homotopy category. -/
private def resPlusHom (F : B ⥤ A) [F.Additive] {a : A} {b : B} (J : InjectiveResolution a)
    (J' : InjectiveResolution b) (g : J.cocomplex ⟶ (F.mapHomologicalComplex _).obj J'.cocomplex) :
    resPlusObj J ⟶ F.mapHomotopyCategoryPlus.obj (resPlusObj J') :=
  (HomotopyCategory.Plus.ι A).preimage ((HomotopyCategory.quotient A _).map
    ((ComplexShape.embeddingUpNat.extendFunctor A).map g ≫
      (mapExtendIso F ComplexShape.embeddingUpNat J'.cocomplex).hom))

omit [EnoughInjectives A] [EnoughInjectives B] in
private lemma ι_map_resPlusHom (F : B ⥤ A) [F.Additive] {a : A} {b : B}
    (J : InjectiveResolution a) (J' : InjectiveResolution b)
    (g : J.cocomplex ⟶ (F.mapHomologicalComplex _).obj J'.cocomplex) :
    (HomotopyCategory.Plus.ι A).map (resPlusHom F J J' g) = (HomotopyCategory.quotient A _).map
      ((ComplexShape.embeddingUpNat.extendFunctor A).map g ≫
        (mapExtendIso F ComplexShape.embeddingUpNat J'.cocomplex).hom) :=
  Functor.map_preimage _ _

omit [EnoughInjectives A] [EnoughInjectives B] in
/-- A map of resolutions over `x : a ⟶ F b` intertwines the augmentations. -/
private lemma resPlusι_comp_resPlusHom (F : B ⥤ A) [F.Additive] {a : A} {b : B}
    (x : a ⟶ F.obj b) (J : InjectiveResolution a) (J' : InjectiveResolution b)
    (g : J.cocomplex ⟶ (F.mapHomologicalComplex _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = x ≫ F.map (J'.ι.f 0)) :
    resPlusι J ≫ resPlusHom F J J' g =
      singleHom F x ≫ F.mapHomotopyCategoryPlus.map (resPlusι J') := by
  apply (HomotopyCategory.Plus.ι A).map_injective
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ι_map_resPlusι,
    ι_map_resPlusHom, ι_map_singleHom, ι_map_mapHomotopyCategoryPlus_map, ι_map_resPlusι,
    Functor.mapHomotopyCategory_map, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  congr 1
  refine HomologicalComplex.from_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, InjectiveResolution.ι'_f_zero,
    InjectiveResolution.ι'_f_zero, HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    mapExtendIso_hom_f_eq F ComplexShape.embeddingUpNat J'.cocomplex (i := 0) (i' := 0) rfl]
  erw [HomologicalComplex.extendMap_f g ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl]
  simp only [InjectiveResolution.cochainComplexXIso, Category.assoc, Iso.inv_hom_id_assoc,
    CategoryTheory.Functor.map_comp]
  rw [reassoc_of% hg]
  simp

/-- **The derived unit read on injective resolutions**, in `D⁺`: for a map of resolutions
`g : J^• ⟶ F(J'^•)` over `x : a ⟶ F b`, `RG` of the unit `a[0] ⟶ RF(b[0])` followed by
`RG ∘ RF ≅ R(G ∘ F)` is, after the identifications of both sides with `G(J^•)` and
`G(F(J'^•))`, the class of `G(g)`. -/
private lemma map_derivedUnit_comp_rightDerivedFunctorPlusCompIso_inv (F : B ⥤ A) (G : A ⥤ Dc)
    [F.Additive] [G.Additive] [F.PreservesInjectiveObjects] {a : A} {b : B} (x : a ⟶ F.obj b)
    (J : InjectiveResolution a) (J' : InjectiveResolution b)
    (g : J.cocomplex ⟶ (F.mapHomologicalComplex _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = x ≫ F.map (J'.ι.f 0)) :
    G.rightDerivedFunctorPlus.map (derivedUnit F x) ≫
        (Functor.rightDerivedFunctorPlusCompIso F G).inv.app _ ≫
        (F ⋙ G).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (resPlusι J')) ≫
        inv ((F ⋙ G).rightDerivedFunctorPlusUnith.app (resPlusObj J')) =
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (resPlusι J)) ≫
        inv (G.rightDerivedFunctorPlusUnith.app (resPlusObj J)) ≫
        DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map (resPlusHom F J J' g)) := by
  have h3 := Functor.rightDerivedFunctorPlusComp_fac_app F G (resPlusObj J')
  have hid : (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).inv.app
      (resPlusObj J') = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    rfl
  rw [hid, DerivedCategory.Plus.Qh.map_id, Category.id_comp] at h3
  have : IsIso (G.rightDerivedFunctorPlusUnith.app
      (F.mapHomotopyCategoryPlus.obj (resPlusObj J'))) := by
    have : IsIso (G.rightDerivedFunctorPlusUnith.app
        (F.mapHomotopyCategoryPlus.obj (resPlusObj J')) ≫ G.rightDerivedFunctorPlus.map
        (F.rightDerivedFunctorPlusUnith.app (resPlusObj J'))) := by
      rw [← h3]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app (resPlusObj J')))
  have key3 : G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app (resPlusObj J')) ≫
      (Functor.rightDerivedFunctorPlusCompIso F G).inv.app
        (DerivedCategory.Plus.Qh.obj (resPlusObj J')) ≫
      inv ((F ⋙ G).rightDerivedFunctorPlusUnith.app (resPlusObj J')) =
      inv (G.rightDerivedFunctorPlusUnith.app (F.mapHomotopyCategoryPlus.obj (resPlusObj J'))) := by
    rw [← cancel_epi (G.rightDerivedFunctorPlusUnith.app _), IsIso.hom_inv_id,
      ← Category.assoc, ← h3, Category.assoc, ← Functor.rightDerivedFunctorPlusCompIso_hom,
      Iso.hom_inv_id_app_assoc, IsIso.hom_inv_id]
  have h1 := ((Functor.rightDerivedFunctorPlusCompIso F G).inv.naturality
    (DerivedCategory.Plus.Qh.map (resPlusι J'))).symm
  dsimp only [Functor.comp_map] at h1
  have h2 : derivedUnit F x ≫ F.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map (resPlusι J')) =
      DerivedCategory.Plus.Qh.map (resPlusι J) ≫
        DerivedCategory.Plus.Qh.map (resPlusHom F J J' g) ≫
        F.rightDerivedFunctorPlusUnith.app (resPlusObj J') := by
    have hn := F.rightDerivedFunctorPlusUnith.naturality (resPlusι J')
    dsimp only [Functor.comp_map] at hn
    rw [derivedUnit, Category.assoc, ← hn, ← Category.assoc,
      ← DerivedCategory.Plus.Qh.map_comp, ← resPlusι_comp_resPlusHom F x J J' g hg,
      DerivedCategory.Plus.Qh.map_comp, Category.assoc]
  have h4 := G.rightDerivedFunctorPlusUnith.naturality (resPlusHom F J J' g)
  dsimp only [Functor.comp_map] at h4
  rw [reassoc_of% h1, ← G.rightDerivedFunctorPlus.map_comp_assoc, h2]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc, key3]
  congr 1
  rw [IsIso.eq_inv_comp, ← Category.assoc, ← h4, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- **Naturality of `H^n(RG(a[0])) ≅ H^n(G(J^•))`.** For a map of resolutions
`g : J^• ⟶ F(J'^•)` over `x : a ⟶ F b`, the map `H^n(RG(a[0])) ⟶ H^n(R(G ∘ F)(b[0]))` induced
by the unit `a[0] ⟶ RF(b[0])` is the map induced by `G(g)`. -/
private theorem resHomologyIso_naturality (F : B ⥤ A) (G : A ⥤ Dc) [F.Additive] [G.Additive]
    [F.PreservesInjectiveObjects] {a : A} {b : B} (x : a ⟶ F.obj b) (J : InjectiveResolution a)
    (J' : InjectiveResolution b) (g : J.cocomplex ⟶ (F.mapHomologicalComplex _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 = x ≫ F.map (J'.ι.f 0)) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor Dc n).map
        (G.rightDerivedFunctorPlus.map (derivedUnit F x) ≫
          (Functor.rightDerivedFunctorPlusCompIso F G).inv.app _) ≫
        (resHomologyIso (F ⋙ G) J' n).hom =
      (resHomologyIso G J n).hom ≫
        (HomotopyCategory.homologyFunctor Dc (ComplexShape.up ℕ) n).map
          ((G.mapHomotopyCategory (ComplexShape.up ℕ)).map
            ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).map g)) := by
  have hP := (plusHomologyIso (D := Dc) (n : ℤ)).hom.naturality
    (G.mapHomotopyCategoryPlus.map (resPlusHom F J J' g))
  dsimp only [Functor.comp_map] at hP
  rw [ι_map_mapHomotopyCategoryPlus_map, ι_map_resPlusHom] at hP
  have hN := extendMapHomologyIso_hom_naturality G g n
  have hE : (extendMapHomologyIso G J.cocomplex n).inv ≫
      (HomotopyCategory.homologyFunctor Dc (ComplexShape.up ℕ) n).map
        ((G.mapHomotopyCategory (ComplexShape.up ℕ)).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℕ)).map g)) =
      (HomotopyCategory.homologyFunctor Dc (ComplexShape.up ℤ) (n : ℤ)).map
        ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((ComplexShape.embeddingUpNat.extendFunctor A).map g ≫
              (mapExtendIso F ComplexShape.embeddingUpNat J'.cocomplex).hom))) ≫
        (extendMapHomologyIso (F ⋙ G) J'.cocomplex n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, extendMapHomologyIso_hom_comp,
      mapExtendHomotopyNatIso_hom_app, reassoc_of% hN]
    congr 1
    rw [extendHomotopyFunctor_map_quotient_map]
    simp only [← CategoryTheory.Functor.map_comp]
  simp only [resHomologyIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_inv,
    Iso.app_hom, Category.assoc]
  rw [hE, ← reassoc_of% hP, ← (DerivedCategory.Plus.homologyFunctor Dc n).map_comp_assoc,
    ← (DerivedCategory.Plus.homologyFunctor Dc n).map_comp_assoc]
  simp only [asIso_hom, Category.assoc]
  rw [map_derivedUnit_comp_rightDerivedFunctorPlusCompIso_inv F G x J J' g hg]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

/-- A map from an object into the kernel of the first differential of a complex of injectives
extends to a map of complexes out of any injective resolution of the object. -/
private lemma exists_hom_of_injective {C : Type*} [Category* C] [Abelian C] {Z : C}
    (I : InjectiveResolution Z) (K : CochainComplex C ℕ) (hK : ∀ n, Injective (K.X n))
    (φ : Z ⟶ K.X 0) (hφ : φ ≫ K.d 0 1 = 0) :
    ∃ g : I.cocomplex ⟶ K, I.ι.f 0 ≫ g.f 0 = φ := by
  let g0 : I.cocomplex.X 0 ⟶ K.X 0 := Injective.factorThru φ (I.ι.f 0)
  have hg0 : I.ι.f 0 ≫ g0 = φ := Injective.comp_factorThru _ _
  let g1 : I.cocomplex.X 1 ⟶ K.X 1 := I.exact₀.descToInjective (g0 ≫ K.d 0 1) (by
    change I.ι.f 0 ≫ g0 ≫ K.d 0 1 = 0
    rw [reassoc_of% hg0, hφ])
  have hg1 : I.cocomplex.d 0 1 ≫ g1 = g0 ≫ K.d 0 1 := I.exact₀.comp_descToInjective _ _
  refine ⟨CochainComplex.mkHom _ _ g0 g1 hg1.symm fun n ⟨g, g', w⟩ =>
    ⟨(I.exact_succ n).descToInjective (g' ≫ K.d (n + 1) (n + 2))
      (by simp [reassoc_of% w.symm]), ((I.exact_succ n).comp_descToInjective _ _).symm⟩, ?_⟩
  rwa [CochainComplex.mkHom_f_0]

end DerivedResolution

/-- Sections over an object are an additive functor on sheaves with values in a preadditive
category, being restriction to presheaves followed by evaluation. -/
instance additive_sheafSections_obj {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (A : Type*) [Category* A] [Preadditive A] [HasSheafify J A] (U : Cᵒᵖ) :
    ((sheafSections J A).obj U).Additive :=
  inferInstanceAs (sheafToPresheaf J A ⋙ (evaluation Cᵒᵖ A).obj U).Additive

/-- Global sections of sheaves of `ℚ`-vector spaces on a space, as a functor on
`TopCat.Sheaf`, are additive. -/
instance additive_sheafSections_obj_top (X : TopCat.{0}) :
    @Functor.Additive (TopCat.Sheaf (ModuleCat.{0} ℚ) X) (ModuleCat.{0} ℚ) _ _ _ _
      ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (op ⊤)) :=
  additive_sheafSections_obj _ _ _

attribute [local instance] HasDerivedCategory.standard pushforward_preservesInjectiveObjects
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Rational sheaf cohomology of the constant sheaf is singular cohomology, in `D⁺`.** For a
metrizable, locally contractible space `X`, `H^n(RΓ(X, ℚ_X)) ≅ H^n(X, ∅; ℚ)`, where `RΓ(X, -)`
is the right derived functor of global sections on the bounded below derived category of sheaves
of `ℚ`-vector spaces and `ℚ_X` is placed in degree `0`. These isomorphisms are natural in
continuous maps `f : Y ⟶ X` between such spaces: the pullback on sheaf cohomology,
`RΓ(X, -)` of the structural unit `ℚ_X ⟶ Rf_* ℚ_Y` (`MMP.Analytic.derivedUnit` of
`MMP.Analytic.constUnit`) followed by `RΓ(X, Rf_* -) ≅ RΓ(Y, -)`, is the pullback `f^*` of
singular cohomology. -/
theorem exists_homology_rightDerivedFunctorPlus_globalSections_iso_relCohomology :
    let QX : ∀ X : TopCat.{0}, TopCat.Sheaf (ModuleCat.{0} ℚ) X := fun X ↦
      (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)
    ∃ e : ∀ (X : TopCat.{0}) [MetrizableSpace X], LocallyContractibleSpace X → ∀ n : ℕ,
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℚ) n).obj
          (((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
              (op ⊤)).rightDerivedFunctorPlus.obj
            (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor
              (TopCat.Sheaf (ModuleCat.{0} ℚ) X) 0).obj (QX X)))) ≅
          ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set X)ᶜ) n),
      ∀ (X Y : TopCat.{0}) [MetrizableSpace X] [MetrizableSpace Y]
        (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) (f : Y ⟶ X) (n : ℕ),
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℚ) n).map
            (((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
                (op ⊤)).rightDerivedFunctorPlus.map
                (derivedUnit (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) (constUnit f)) ≫
              (Functor.rightDerivedFunctorPlusCompIso (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f)
                ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
                    (op ⊤))).inv.app _) ≫ (e Y hY n).hom =
          (e X hX n).hom ≫
            ModuleCat.ofHom (relCohomologyMap ℚ f (compl_univ_subset_preimage f) n) := by
  intro QX
  obtain ⟨E, hE⟩ := exists_homology_globalSections_injectiveResolution_iso_relCohomology
  refine ⟨fun X _ hX n ↦ resHomologyIso ((sheafSections (Opens.grothendieckTopology X)
      (ModuleCat.{0} ℚ)).obj (op ⊤)) (injectiveResolution (QX X)) n ≪≫
    (HomotopyCategory.homologyFunctorFactors _ _ n).app _ ≪≫
      E X hX (injectiveResolution (QX X)) n, ?_⟩
  intro X Y _ _ hX hY f n
  let P := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f
  let JX := injectiveResolution (QX X)
  let JY := injectiveResolution (QX Y)
  obtain ⟨g, hg⟩ := exists_hom_of_injective JX ((P.mapHomologicalComplex _).obj JY.cocomplex)
    (fun k ↦ P.injective_obj (JY.cocomplex.X k)) (constUnit f ≫ P.map (JY.ι.f 0)) (by
      rw [Category.assoc, Functor.mapHomologicalComplex_obj_d, ← CategoryTheory.Functor.map_comp,
        JY.ι_f_zero_comp_complex_d, Functor.map_zero, Limits.comp_zero])
  have h1 : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{0} ℚ) n).map
        (((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
            (op ⊤)).rightDerivedFunctorPlus.map (derivedUnit P (constUnit f)) ≫
          (Functor.rightDerivedFunctorPlusCompIso P ((sheafSections (Opens.grothendieckTopology X)
              (ModuleCat.{0} ℚ)).obj (op ⊤))).inv.app _) ≫
        (resHomologyIso ((sheafSections (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj
            (op ⊤)) JY n).hom =
      (resHomologyIso ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
          (op ⊤)) JX n).hom ≫
        (HomotopyCategory.homologyFunctor (ModuleCat.{0} ℚ) (ComplexShape.up ℕ) n).map
          ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
              (op ⊤)).mapHomotopyCategory (ComplexShape.up ℕ)).map
            ((HomotopyCategory.quotient _ (ComplexShape.up ℕ)).map g)) :=
    resHomologyIso_naturality P ((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0}
        ℚ)).obj (op ⊤)) (constUnit f) JX JY g hg n
  have h2 := (HomotopyCategory.homologyFunctorFactors (ModuleCat.{0} ℚ) (ComplexShape.up ℕ)
    n).hom.naturality ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
        (op ⊤)).mapHomologicalComplex _).map g)
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [reassoc_of% h1]
  congr 1
  rw [Functor.mapHomotopyCategory_map]
  dsimp only [Functor.comp_map, HomologicalComplex.homologyFunctor_map] at h2
  erw [reassoc_of% h2]
  exact congrArg _ (hE X Y hX hY f JX JY g hg n)

end MMP.Analytic
