module

public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.Analytic.SmoothCentreSlices
import MMP.AlgebraicGeometry.Analytic.BettiRestriction
import MMP.AlgebraicGeometry.Analytic.RationalSheafCohomologySingular
import MMP.AlgebraicGeometry.Analytic.RationalSingularComparison
import MMP.AlgebraicTopology.ThomClass.Natural
import MMP.AlgebraicTopology.SingularCohomology.CupProduct.Comparison
import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByInitial
import StacksFrontier.Homology.DerivedIndexing.Composite
import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso

/-!
# Pullback along a smooth blowup of pure codimension is a retract of presheaves

Let `b : V' ⟶ V` be the blowup of a smooth complex variety along a smooth closed centre all of
whose components have codimension `c ≥ 2`. Then the presheaf `U ↦ H^q(U; ℚ)` on `V^an` is a
retract of the presheaf `U ↦ H^q(b⁻¹(U); ℚ)`, both in singular cohomology.

The derived splitting `ℚ_V ⊞ ⨁ i_* ℚ_T[-2a] ≅ Rb_* ℚ_{V'}` makes `ℚ_V` a retract of
`Rb_* ℚ_{V'}` in the bounded below derived category of sheaves of `ℚ`-vector spaces on `V^an`.
The functor `K ↦ H^q(R forget(K))`, from that derived category to presheaves, carries it to a
retract of presheaves. Computed on an injective resolution `J` of the constant sheaf, its value
on `ℚ` is `U ↦ H^q(Γ(U, J))`, and on `Rb_* ℚ` it is `U ↦ H^q(Γ(b⁻¹ U, J'))`. Restricting an
injective resolution to an open subset gives an injective resolution of the constant sheaf of
the open subset, and the comparison of sheaf cohomology with singular cohomology, natural in
continuous maps, identifies these presheaves with the singular ones.

## Main results

* `MMP.Fourfold.nonempty_retract_directImagePresheaf_blowUp_of_codimension`.

## References

* [B. Iversen, *Cohomology of sheaves*], II.5, III.1.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology
open MMP.Analytic MMP.Analytic.ComplexPoints MMP MMP.SingularCochain

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

set_option backward.isDefEq.respectTransparency false

attribute [local instance] HasDerivedCategory.standard pushforward_additive
  pushforward_preservesInjectiveObjects
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace MMP.Fourfold

/-- The constant sheaf `ℚ` on a space. -/
private noncomputable abbrev constSheafRat (Z : TopCat.{0}) : TopCat.Sheaf (ModuleCat.{0} ℚ) Z :=
  (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)

/-- The inverse image of the constant sheaf is the constant sheaf. -/
private noncomputable def constPullbackIso {Z Z' : TopCat.{0}} (f : Z' ⟶ Z) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj (constSheafRat Z) ≅ constSheafRat Z' :=
  haveI := isIso_homEquiv_symm_constUnit f
  asIso (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).homEquiv _ _).symm
    (constUnit f))

/-- An injective resolution of `Z` is one of any object isomorphic to `Z`. -/
private noncomputable def InjectiveResolution.ofIso {C : Type*} [Category C] [Abelian C]
    {Z Z' : C} (e : Z' ≅ Z) (J : InjectiveResolution Z) : InjectiveResolution Z' where
  cocomplex := J.cocomplex
  ι := (CochainComplex.single₀ C).map e.hom ≫ J.ι

section Restrict

open TopCat.Presheaf TopCat.Presheaf.ExtensionByInitial

variable {Y : TopCat.{0}} (U : Opens Y)

/-- The presheaf-level extension by zero of presheaves of `ℚ`-vector spaces preserves finite
limits. -/
private lemma preservesFiniteLimits_extendByInitialFunctor_rat :
    PreservesFiniteLimits (extendByInitialFunctor (C := ModuleCat.{0} ℚ) U) := by
  apply preservesFiniteLimits_of_evaluation
  intro V
  by_cases hV : V.unop ≤ U
  · let e : (evaluation (Opens (sp U))ᵒᵖ (ModuleCat.{0} ℚ)).obj
            (Opposite.op ((Opens.map U.inclusion').obj V.unop)) ≅
          extendByInitialFunctor (C := ModuleCat.{0} ℚ) U ⋙
            (evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj V :=
      NatIso.ofComponents (fun F =>
        (eqToIso (ExtensionByInitial.obj_of_le U F hV)).symm) (fun _ => by
          simp [extendByInitialFunctor, extendByInitial, ExtensionByInitial.map,
            ExtensionByInitial.mapNat, ExtensionByInitial.appMap, hV])
    let _ : PreservesFiniteLimits
        ((evaluation (Opens (sp U))ᵒᵖ (ModuleCat.{0} ℚ)).obj
          (Opposite.op ((Opens.map U.inclusion').obj V.unop))) :=
      instPreservesFiniteLimitsFunctorObjEvaluationOfHasFiniteLimits _
    exact preservesFiniteLimits_of_natIso e
  · let e : (Functor.const (TopCat.Presheaf (ModuleCat.{0} ℚ) (sp U))).obj
            (⊥_ (ModuleCat.{0} ℚ)) ≅
          extendByInitialFunctor (C := ModuleCat.{0} ℚ) U ⋙
            (evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj V :=
      NatIso.ofComponents (fun F =>
        (eqToIso (ExtensionByInitial.obj_of_not_le U F hV)).symm)
          (fun _ => initialIsInitial.hom_ext _ _)
    let _ : PreservesFiniteLimits
        ((Functor.const (TopCat.Presheaf (ModuleCat.{0} ℚ) (sp U))).obj
          (⊥_ (ModuleCat.{0} ℚ))) :=
      ⟨fun J _ _ =>
        (((Functor.const (TopCat.Presheaf (ModuleCat.{0} ℚ) (sp U))).obj
            (⊥_ (ModuleCat.{0} ℚ))).preservesLimitsOfShape_of_isZero
          (((Functor.const (TopCat.Presheaf (ModuleCat.{0} ℚ) (sp U))).obj
            (⊥_ (ModuleCat.{0} ℚ))).isZero (fun _ => by
              dsimp
              exact (isZero_zero (C := ModuleCat.{0} ℚ)).of_iso
                HasZeroObject.zeroIsoInitial.symm)) J)⟩
    exact preservesFiniteLimits_of_natIso e

/-- Extension by zero of sheaves of `ℚ`-vector spaces preserves monomorphisms. -/
private lemma preservesMonomorphisms_extendByInitialSheaf_rat :
    (extendByInitialSheaf (C := ModuleCat.{0} ℚ) U).PreservesMonomorphisms := by
  have := preservesFiniteLimits_extendByInitialFunctor_rat U
  have : PreservesFiniteLimits
      (presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)) := inferInstance
  have hL : PreservesFiniteLimits (extendByInitialSheaf (C := ModuleCat.{0} ℚ) U) := by
    change PreservesFiniteLimits (sheafToPresheaf _ _ ⋙ (extendByInitialFunctor U ⋙
      presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)))
    infer_instance
  exact @preservesMonomorphisms_of_preservesLimitsOfShape _ _ _ _ _
    (hL.preservesFiniteLimits WalkingCospan)

/-- Restriction to an open subset, as a functor of sheaves of `ℚ`-vector spaces. -/
private noncomputable abbrev resF : TopCat.Sheaf (ModuleCat.{0} ℚ) Y ⥤
    TopCat.Sheaf (ModuleCat.{0} ℚ) (sp U) :=
  Opens.sheafRestrict (C := ModuleCat.{0} ℚ) U

/-- Restriction to an open subset preserves injective sheaves of `ℚ`-vector spaces. -/
private lemma preservesInjectiveObjects_sheafRestrict : (resF U).PreservesInjectiveObjects :=
  have := preservesMonomorphisms_extendByInitialSheaf_rat U
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (extendByInitialSheafAdjunction U)

/-- `j^{-1} ⊣ j_*` for the inclusion `j` of an open subset. -/
private noncomputable abbrev resAdj :
    resF U ⊣ TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion' :=
  sheafRestrictPushforwardAdjunction U

private lemma preservesFiniteLimits_sheafRestrict : PreservesFiniteLimits (resF U) :=
  haveI : (resF U).IsRightAdjoint := (extendByInitialSheafAdjunction U).isRightAdjoint
  inferInstance

private lemma preservesFiniteColimits_sheafRestrict : PreservesFiniteColimits (resF U) :=
  haveI : (resF U).IsLeftAdjoint := (resAdj U).isLeftAdjoint
  inferInstance

private lemma additive_sheafRestrict : (resF U).Additive :=
  have := preservesFiniteLimits_sheafRestrict U
  Functor.additive_of_preserves_binary_products _

attribute [local instance] preservesInjectiveObjects_sheafRestrict
  preservesFiniteLimits_sheafRestrict
  preservesFiniteColimits_sheafRestrict additive_sheafRestrict

/-- `ℚ_Y|_U ≅ ℚ_U`, through the uniqueness of left adjoints of `j_*`. -/
private noncomputable def restrictConstIso :
    (resF U).obj (constSheafRat Y) ≅ constSheafRat (sp U) :=
  ((resAdj U).leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) U.inclusion')).app _ ≪≫
    constPullbackIso U.inclusion'

/-- `ℚ_Y ⟶ j_* ℚ_U` is the adjunct of `restrictConstIso`. -/
private lemma unit_comp_map_restrictConstIso_hom :
    (resAdj U).unit.app (constSheafRat Y) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').map (restrictConstIso U).hom =
      constUnit U.inclusion' := by
  simp only [restrictConstIso, Iso.trans_hom, Iso.app_hom, Functor.map_comp]
  rw [← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
  change (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) U.inclusion').unit.app _ ≫
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) U.inclusion').map
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) U.inclusion').homEquiv
        _ _).symm (constUnit U.inclusion')) = _
  exact ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) U.inclusion').homEquiv_unit
    _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- The restriction of an injective resolution of `ℚ_Y` to an open subset `U` is an injective
resolution of `ℚ_U`. -/
private noncomputable def restrictResolution (J : InjectiveResolution (constSheafRat Y)) :
    InjectiveResolution (constSheafRat (sp U)) where
  cocomplex := ((resF U).mapHomologicalComplex _).obj J.cocomplex
  injective := ((resF U).mapInjectiveResolution J).injective
  ι := (CochainComplex.single₀ _).map (restrictConstIso U).inv ≫
    ((resF U).mapInjectiveResolution J).ι
  quasiIso := by
    have := ((resF U).mapInjectiveResolution J).quasiIso
    infer_instance

private lemma restrictResolution_ι_f_zero (J : InjectiveResolution (constSheafRat Y)) :
    (restrictResolution U J).ι.f 0 = (restrictConstIso U).inv ≫ (resF U).map (J.ι.f 0) := by
  change (restrictConstIso U).inv ≫ ((HomologicalComplex.singleMapHomologicalComplex
    (resF U) (ComplexShape.up ℕ) 0).inv.app (constSheafRat Y)).f 0 ≫ (resF U).map (J.ι.f 0) = _
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    eqToIso.hom, eqToIso.inv, eqToHom_refl, Category.id_comp]
  rfl

end Restrict

/-! ### Homology of a complex of presheaves, open by open -/

section Pointwise

variable {Y : TopCat.{0}}

private instance evaluation_preservesZeroMorphisms (U : (Opens Y)ᵒᵖ) :
    Functor.PreservesZeroMorphisms (C := TopCat.Presheaf (ModuleCat.{0} ℚ) Y)
      ((evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj U) :=
  inferInstanceAs ((evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj U).PreservesZeroMorphisms

private instance evaluation_preservesHomology (U : (Opens Y)ᵒᵖ) :
    Functor.PreservesHomology (C := TopCat.Presheaf (ModuleCat.{0} ℚ) Y)
      ((evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj U) :=
  inferInstanceAs ((evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj U).PreservesHomology

/-- The value on `U` of the homology of a complex of presheaves is the homology of the complex of
values on `U`. -/
private noncomputable def evHomologyIso
    (K : CochainComplex (TopCat.Presheaf (ModuleCat.{0} ℚ) Y) ℕ) (q : ℕ) (U : Opens Y) :
    (K.homology q).obj (op U) ≅
      ((((evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj (op U)).mapHomologicalComplex _).obj
        K).homology q :=
  ((K.sc q).mapHomologyIso ((evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).obj (op U))).symm

private lemma evHomologyIso_naturality
    (K : CochainComplex (TopCat.Presheaf (ModuleCat.{0} ℚ) Y) ℕ) (q : ℕ) {U U' : Opens Y}
    (h : U' ≤ U) :
    (K.homology q).map (homOfLE h).op ≫ (evHomologyIso K q U').hom =
      (evHomologyIso K q U).hom ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex
          ((evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).map (homOfLE h).op) _).app K) q := by
  change ((evaluation (Opens Y)ᵒᵖ (ModuleCat.{0} ℚ)).map (homOfLE h).op).app
    ((K.sc q).homology) ≫ _ = _
  rw [NatTrans.app_homology]
  simp only [evHomologyIso, Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

end Pointwise

/-! ### Sections of an injective resolution over the opens of a space -/

section Sections

open TopCat.Presheaf TopCat.Presheaf.ExtensionByInitial

variable {Y : TopCat.{0}}

attribute [local instance] preservesInjectiveObjects_sheafRestrict
  preservesFiniteLimits_sheafRestrict preservesFiniteColimits_sheafRestrict additive_sheafRestrict

/-- The complex of sections over `W` of a complex of sheaves. -/
private noncomputable abbrev secC (I : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) Y) ℕ)
    (W : Opens Y) : CochainComplex (ModuleCat.{0} ℚ) ℕ :=
  (((sheafSections (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj
    (op W)).mapHomologicalComplex _).obj I

/-- Restriction of sections `Γ(W, I) ⟶ Γ(W', I)`. -/
private noncomputable abbrev secRes (I : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) Y) ℕ)
    {W W' : Opens Y} (h : W' ≤ W) : secC I W ⟶ secC I W' :=
  (NatTrans.mapHomologicalComplex
    ((sheafSections (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).map (homOfLE h).op) _).app I

/-- Global sections of sheaves on a space. -/
private noncomputable abbrev topSec (Z : TopCat.{0}) :
    TopCat.Sheaf (ModuleCat.{0} ℚ) Z ⥤ ModuleCat.{0} ℚ :=
  (sheafSections (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj (op ⊤)

/-- `Γ(W, I) ≅ Γ(W, I|_W)`. -/
private noncomputable def secTopIso (I : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) Y) ℕ)
    (W : Opens Y) :
    secC I W ≅ ((topSec (sp W)).mapHomologicalComplex _).obj
      (((resF W).mapHomologicalComplex _).obj I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (I.X n).obj.mapIso (eqToIso (Opens.isOpenEmbedding_obj_top W)).op)
    (fun i j _ => (I.d i j).hom.naturality _)

/-- The inclusion of opens `W' ⊆ W`, as a map of spaces. -/
private noncomputable abbrev incl {W W' : Opens Y} (h : W' ≤ W) : sp W' ⟶ sp W :=
  (Opens.toTopCat Y).map (homOfLE h)

/-- Restriction `G|_W ⟶ ι_* (G|_{W'})` along the inclusion `ι : W' ⟶ W`. -/
private noncomputable def resRes {W W' : Opens Y} (h : W' ≤ W)
    (G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) :
    (resF W).obj G ⟶
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (incl h)).obj ((resF W').obj G) :=
  ObjectProperty.homMk
    { app := fun V => G.obj.map (homOfLE (by
          rintro _ ⟨y, hy, rfl⟩
          exact ⟨incl h y, hy, rfl⟩)).op
      naturality := by
        intro V V' i
        change G.obj.map _ ≫ G.obj.map _ = G.obj.map _ ≫ G.obj.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl }

private lemma resRes_naturality {W W' : Opens Y} (h : W' ≤ W)
    {G G' : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (φ : G ⟶ G') :
    (resF W).map φ ≫ resRes h G' =
      resRes h G ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (incl h)).map ((resF W').map φ) := by
  apply Sheaf.hom_ext
  ext V : 2
  exact (φ.hom.naturality _).symm

/-- The restriction maps `I|_W ⟶ ι_* (I|_{W'})`, as a map of complexes. -/
private noncomputable def resResC {W W' : Opens Y} (h : W' ≤ W)
    (I : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) Y) ℕ) :
    ((resF W).mapHomologicalComplex _).obj I ⟶
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (incl h)).mapHomologicalComplex _).obj
        (((resF W').mapHomologicalComplex _).obj I) where
  f n := resRes h (I.X n)
  comm' i j _ := (resRes_naturality h (I.d i j)).symm

private lemma restrictConstIso_inv_comp_resRes {W W' : Opens Y} (h : W' ≤ W) :
    (restrictConstIso W).inv ≫ resRes h (constSheafRat Y) =
      constUnit (incl h) ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (incl h)).map (restrictConstIso W').inv := by
  rw [← cancel_epi (restrictConstIso W).hom, Iso.hom_inv_id_assoc]
  apply ((resAdj W).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h1 : (resAdj W).unit.app (constSheafRat Y) ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) W.inclusion').map (resRes h (constSheafRat Y)) =
      (resAdj W').unit.app (constSheafRat Y) := by
    apply Sheaf.hom_ext
    ext V : 2
    change (constSheafRat Y).obj.map _ ≫ (constSheafRat Y).obj.map _ = (constSheafRat Y).obj.map _
    rw [← Functor.map_comp]
    rfl
  rw [h1, Functor.map_comp, Functor.map_comp, ← Category.assoc,
    unit_comp_map_restrictConstIso_hom, ← Category.assoc, ← constUnit_comp]
  have h2 : (resAdj W').unit.app (constSheafRat Y) = constUnit W'.inclusion' ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) W'.inclusion').map (restrictConstIso W').inv := by
    rw [← unit_comp_map_restrictConstIso_hom W', Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h2

private lemma restrictResolution_ι_f_zero_comp_resResC (I : InjectiveResolution (constSheafRat Y))
    {W W' : Opens Y} (h : W' ≤ W) :
    (restrictResolution W I).ι.f 0 ≫ (resResC h I.cocomplex).f 0 =
      constUnit (incl h) ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (incl h)).map
        ((restrictResolution W' I).ι.f 0) := by
  have e : (resF W).map (I.ι.f 0) ≫ resRes h (I.cocomplex.X 0) =
      resRes h (constSheafRat Y) ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (incl h)).map
        ((resF W').map (I.ι.f 0)) := resRes_naturality h (I.ι.f 0)
  rw [restrictResolution_ι_f_zero, restrictResolution_ι_f_zero, Category.assoc]
  change _ ≫ (resF W).map (I.ι.f 0) ≫ resRes h (I.cocomplex.X 0) = _
  rw [e, ← Category.assoc, restrictConstIso_inv_comp_resRes, Category.assoc,
    ← Functor.map_comp]

/-- The chosen identification of rational sheaf cohomology with singular cohomology. -/
private noncomputable def eSing :
    ∀ (X : TopCat.{0}) [MetrizableSpace X], LocallyContractibleSpace X →
      ∀ (J : InjectiveResolution (constSheafRat X)) (n : ℕ),
        ((((sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj
          (op ⊤)).mapHomologicalComplex _).obj J.cocomplex).homology n ≅
          ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set X)ᶜ) n) :=
  exists_homology_globalSections_injectiveResolution_iso_relCohomology.choose

private lemma eSing_naturality (X Y : TopCat.{0}) [MetrizableSpace X] [MetrizableSpace Y]
    (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) (f : Y ⟶ X)
    (J : InjectiveResolution (constSheafRat X)) (J' : InjectiveResolution (constSheafRat Y))
    (g : J.cocomplex ⟶ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).mapHomologicalComplex
      _).obj J'.cocomplex)
    (hg : J.ι.f 0 ≫ g.f 0 =
      constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map (J'.ι.f 0))
    (n : ℕ) :
    HomologicalComplex.homologyMap ((((sheafSections (Opens.grothendieckTopology X)
        (ModuleCat.{0} ℚ)).obj (op ⊤)).mapHomologicalComplex _).map g) n ≫
        (eSing Y hY J' n).hom =
      (eSing X hX J n).hom ≫
        ModuleCat.ofHom (relCohomologyMap ℚ f (fun z hz => absurd (Set.mem_univ z) hz) n) :=
  exists_homology_globalSections_injectiveResolution_iso_relCohomology.choose_spec
    X Y hX hY f J J' g hg n

/-- `H^q(Γ(W, I)) ≅ H^q(W; ℚ)` for an injective resolution `I` of `ℚ_Y`. -/
private noncomputable def secIso (I : InjectiveResolution (constSheafRat Y))
    (hY : ∀ W : Opens Y, MetrizableSpace W ∧ LocallyContractibleSpace W) (q : ℕ) (W : Opens Y) :
    (secC I.cocomplex W).homology q ≅
      ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set (sp W))ᶜ) q) :=
  haveI : MetrizableSpace (sp W) := (hY W).1
  (HomologicalComplex.homologyFunctor _ _ q).mapIso (secTopIso I.cocomplex W) ≪≫
    eSing (sp W) (hY W).2 (restrictResolution W I) q

private lemma secIso_naturality (I : InjectiveResolution (constSheafRat Y))
    (hY : ∀ W : Opens Y, MetrizableSpace W ∧ LocallyContractibleSpace W) (q : ℕ)
    {W W' : Opens Y} (h : W' ≤ W) :
    HomologicalComplex.homologyMap (secRes I.cocomplex h) q ≫ (secIso I hY q W').hom =
      (secIso I hY q W).hom ≫ ModuleCat.ofHom
        (relCohomologyMap ℚ (incl h) (fun z hz => absurd (Set.mem_univ z) hz) q) := by
  have : MetrizableSpace (sp W) := (hY W).1
  have : MetrizableSpace (sp W') := (hY W').1
  have hE := eSing_naturality (sp W) (sp W') (hY W).2 (hY W').2 (incl h)
    (restrictResolution W I) (restrictResolution W' I) (resResC h I.cocomplex)
    (restrictResolution_ι_f_zero_comp_resResC I h) q
  have hC : secRes I.cocomplex h ≫ (secTopIso I.cocomplex W').hom =
      (secTopIso I.cocomplex W).hom ≫
        ((topSec (sp W)).mapHomologicalComplex _).map (resResC h I.cocomplex) := by
    ext n : 1
    simp only [HomologicalComplex.comp_f]
    change (I.cocomplex.X n).obj.map _ ≫ (I.cocomplex.X n).obj.map _ =
      (I.cocomplex.X n).obj.map _ ≫ (I.cocomplex.X n).obj.map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  simp only [secIso, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc, hC, HomologicalComplex.homologyMap_comp_assoc]
  exact congrArg (_ ≫ ·) hE

end Sections

/-! ### The presheaf of sections cohomology is the presheaf of singular cohomology -/

section DirectImage

open TopCat.Presheaf.ExtensionByInitial

/-- `H^q(Z; ℚ)`, read as cocycles modulo coboundaries. -/
private noncomputable def singIso (Z : TopCat.{0}) (q : ℕ) :
    rationalCohomology Z q ≅ ModuleCat.of ℚ (relCohomology ℚ ((Set.univ : Set Z)ᶜ) q) :=
  (relativeSingularCohomologyEquiv ℚ ((Set.univ : Set Z)ᶜ) q).toModuleIso

private lemma singIso_inv_naturality {Z Z' : TopCat.{0}} (f : Z' ⟶ Z) (q : ℕ) :
    ModuleCat.ofHom (relCohomologyMap ℚ f (fun z hz => absurd (Set.mem_univ z) hz) q) ≫
        (singIso Z' q).inv =
      (singIso Z q).inv ≫ rationalCohomologyMap f q := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  ext x
  exact (relativeSingularCohomologyEquiv_map (R := ℚ) f _ q x).symm

/-- For a continuous map `f : Y' ⟶ Y` and an injective resolution `I` of `ℚ_{Y'}`, the presheaf
`U ↦ H^q(Γ(f⁻¹ U, I))` is the presheaf `U ↦ H^q(f⁻¹ U; ℚ)`. -/
private noncomputable def directImageIso {Y' Y : TopCat.{0}} (f : Y' ⟶ Y)
    (I : InjectiveResolution (constSheafRat Y'))
    (hY : ∀ W : Opens Y', MetrizableSpace W ∧ LocallyContractibleSpace W) (q : ℕ) :
    (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Y).mapHomologicalComplex _).obj
          I.cocomplex).homology q ≅ directImagePresheaf f q :=
  NatIso.ofComponents
    (fun U => evHomologyIso _ q U.unop ≪≫ secIso I hY q ((Opens.map f).obj U.unop) ≪≫
      (singIso (preimageSpace f U.unop) q).symm)
    (by
      intro U U' i
      have hi : i = (homOfLE i.unop.le).op := rfl
      have h' : (Opens.map f).obj U'.unop ≤ (Opens.map f).obj U.unop :=
        (Opens.map f).monotone i.unop.le
      have e1 := evHomologyIso_naturality ((((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        TopCat.Sheaf.forget (ModuleCat.{0} ℚ) Y).mapHomologicalComplex _).obj
          I.cocomplex)) q i.unop.le
      have e2 := secIso_naturality I hY q h'
      have e3 := singIso_inv_naturality (preimageInclusion f i.unop.le) q
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [hi, reassoc_of% e1]
      erw [reassoc_of% e2]
      erw [e3]
      rfl)

end DirectImage

/-! ### Right derived functors computed on injective resolutions -/

section DerivedResolution

open Stacks.DerivedIndexing

variable {A Dc : Type*} [Category* A] [Category* Dc] [Abelian A] [Abelian Dc] [EnoughInjectives A]

/-- An injective resolution, as an object of the bounded below homotopy category. -/
private noncomputable abbrev resPlusObj {a : A} (J : InjectiveResolution a) :
    HomotopyCategory.Plus A :=
  (HomotopyCategory.Plus.quotient A).obj J.plusObj

/-- The augmentation `a[0] ⟶ J^•` in the bounded below homotopy category. -/
private noncomputable def resPlusι {a : A} (J : InjectiveResolution a) :
    (HomotopyCategory.Plus.singleFunctor A 0).obj a ⟶ resPlusObj J :=
  (HomotopyCategory.Plus.ι A).preimage ((HomotopyCategory.quotient A _).map J.ι')

private instance isIso_Qh_map_resPlusι {a : A} (J : InjectiveResolution a) :
    IsIso (DerivedCategory.Plus.Qh.map (resPlusι J)) :=
  Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) _ (by
    change HomotopyCategory.quasiIso A _ ((HomotopyCategory.Plus.ι A).map (resPlusι J))
    rw [resPlusι, Functor.map_preimage, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance)

/-- `H^n(RG(a[0])) ≅ H^n(G(J^•))`, for an injective resolution `J^•` of `a`. -/
private noncomputable def resHomologyIso (G : A ⥤ Dc) [G.Additive] {a : A}
    (J : InjectiveResolution a) (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor Dc n).obj
        (G.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
          ((HomotopyCategory.Plus.singleFunctor A 0).obj a))) ≅
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).homology n :=
  (DerivedCategory.Plus.homologyFunctor Dc n).mapIso
      (G.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Qh.map (resPlusι J))) ≪≫
        (asIso (G.rightDerivedFunctorPlusUnith.app (resPlusObj J))).symm) ≪≫
    (plusHomologyIso (D := Dc) (n : ℤ)).app (G.mapHomotopyCategoryPlus.obj (resPlusObj J)) ≪≫
    (extendMapHomologyIso G J.cocomplex n).symm ≪≫
    (HomotopyCategory.homologyFunctorFactors Dc (ComplexShape.up ℕ) n).app _

end DerivedResolution

/-! ### The retraction -/

/-- The opens of the complex realization of a separated scheme of finite type over `ℂ` are
metrizable and locally contractible. -/
private lemma metrizable_locallyContractible_opens {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsSeparated sX] [LocallyOfFiniteType sX] [QuasiCompact sX] :
    ∀ W : Opens (analyticSpace sX), MetrizableSpace W ∧ LocallyContractibleSpace W := by
  obtain ⟨h1, h2⟩ := metrizableSpace_and_stronglyLocallyContractibleSpace sX
  have : MetrizableSpace (analyticSpace sX) := h1
  have : StronglyLocallyContractibleSpace (analyticSpace sX) := h2
  intro W
  have : StronglyLocallyContractibleSpace W := W.isOpen.stronglyLocallyContractibleSpace
  exact ⟨IsEmbedding.subtypeVal.metrizableSpace,
    StronglyLocallyContractibleSpace.locallyContractible⟩

/-- **Pullback along a smooth blowup of pure codimension at least two is a retract of
presheaves.** Let `b : V' ⟶ V` be the blowup of a smooth complex variety `V` along a smooth
closed centre `Z` all of whose components have codimension `c ≥ 2`. Then for every `q` the
presheaf `U ↦ H^q(U; ℚ)` on `V^an` is a retract of the presheaf `U ↦ H^q(b⁻¹(U); ℚ)` (singular
cohomology). -/
public theorem nonempty_retract_directImagePresheaf_blowUp_of_codimension {V : Scheme.{0}}
    [IsIntegral V] (s : V ⟶ Spec (.of ℂ)) [IsSeparated s] [LocallyOfFiniteType s]
    [QuasiCompact s] (Z : V.IdealSheafData) (hs : MMP.Mori.IsSmoothScheme s)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) (c : ℕ) (hc : 2 ≤ c)
    (hcodim : ∀ W : IrreducibleCloseds V,
      Maximal (fun W' : IrreducibleCloseds V ↦ (W' : Set V) ⊆ Z.support) W → codimension W = c)
    (q : ℕ) :
    Nonempty (Retract (directImagePresheaf (𝟙 (analyticSpace s)) q)
      (directImagePresheaf (analyticMap (sY := s) (blowUpToBase Z) rfl) q)) := by
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨⟨E, -⟩, -⟩ := MMP.Conductor.exists_biprod_iso_rightDerivedFunctorPlus_blowUpToBase s Z
    ⟨hs, hZ⟩ c hc hcodim
  let bAn := analyticMap (sY := s) (blowUpToBase Z) rfl
  let F := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) bAn
  let Ψ := TopCat.Sheaf.forget (ModuleCat.{0} ℚ) (analyticSpace s)
  have : Ψ.Additive := ⟨fun {_ _ _ _} => rfl⟩
  let Φ := Ψ.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.homologyFunctor (TopCat.Presheaf (ModuleCat.{0} ℚ) (analyticSpace s)) q
  let r0 : Retract _ _ :=
    { i := biprod.inl ≫ E.hom, r := E.inv ≫ biprod.fst, retract := by simp }
  let I := injectiveResolution (constSheafRat (analyticSpace s))
  let J := injectiveResolution ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) bAn).obj
    (constSheafRat (analyticSpace s)))
  let J' : InjectiveResolution (constSheafRat (analyticSpace (blowUpToBase Z ≫ s))) :=
    InjectiveResolution.ofIso (constPullbackIso bAn).symm J
  let isoA : Φ.obj (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor _ 0).obj
      (constSheafRat (analyticSpace s)))) ≅ directImagePresheaf (𝟙 (analyticSpace s)) q :=
    resHomologyIso Ψ I q ≪≫
      directImageIso (𝟙 (analyticSpace s)) I (metrizable_locallyContractible_opens s) q
  let isoB : Φ.obj (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj
      ((HomotopyCategory.Plus.singleFunctor _ 0).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) bAn).obj (constSheafRat (analyticSpace s)))))) ≅
      directImagePresheaf bAn q :=
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
        ((Functor.rightDerivedFunctorPlusCompIso F Ψ).app _).symm ≪≫
      resHomologyIso (F ⋙ Ψ) J q ≪≫
      directImageIso bAn J' (metrizable_locallyContractible_opens _) q
  exact ⟨(Retract.ofIso isoA.symm).trans ((r0.map Φ).trans (Retract.ofIso isoB))⟩

end MMP.Fourfold
