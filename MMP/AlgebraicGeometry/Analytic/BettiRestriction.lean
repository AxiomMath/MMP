module

public import MMP.AlgebraicGeometry.Analytic.PluriformDensity
public import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme

/-!
# Retractions of the rational structural unit and pullback on sheaf cohomology

For a continuous map `f : Z' ⟶ Z` of topological spaces, the constant sheaves `ℚ_Z` and
`ℚ_{Z'}` are related by the canonical morphism `ℚ_Z ⟶ f_* ℚ_{Z'}`, adjoint to the unit section
of `ℚ_{Z'}`; followed by the comparison `f_* ⟶ Rf_*` it gives the *structural unit*
`ℚ_Z ⟶ Rf_* ℚ_{Z'}` in the bounded below derived category of sheaves of `ℚ`-vector spaces on
`Z`. Pullback `H^k(Z, ℚ) ⟶ H^k(Z', ℚ)` on sheaf cohomology is `RΓ(Z, -)` of the structural unit
followed by the identification `RΓ(Z, Rf_* -) ≅ RΓ(Z', -)`.

The property "the structural unit has a retraction" is stable under composition, holds for the
identity, passes to the restriction over any subset of the base when `f` is proper (proper base
change), and implies that pullback on sheaf cohomology is split injective in every degree. Most of
this is proved for a morphism `x : a ⟶ F b` and the induced unit `a[0] ⟶ RF(b[0])`, for additive
functors between abelian categories with enough injectives.

## Main definitions

* `MMP.Analytic.constUnit`: the canonical morphism `ℚ_Z ⟶ f_* ℚ_{Z'}`.
* `MMP.Analytic.derivedUnit`: the morphism `a[0] ⟶ RF(b[0])` induced by `x : a ⟶ F b`.
* `MMP.Analytic.HasUnitRetraction`: that morphism has a retraction.

## Main results

* `MMP.Analytic.isIso_homEquiv_symm_constUnit`: the inverse image of a constant sheaf is
  constant.
* `MMP.Analytic.hasUnitRetraction_comp`, `MMP.Analytic.hasUnitRetraction_of_comp`: retractions
  of units compose, and descend from a composite to its last factor.
* `MMP.Analytic.HasUnitRetraction.of_baseChange`: retractions of units survive an invertible
  derived base change.
* `MMP.Analytic.hasUnitRetraction_constUnit_of_isPullback`: proper base change of a retraction
  of the structural unit.
* `MMP.Analytic.hasUnitRetraction_constUnit_restrictPreimage`: for a proper morphism of schemes
  of finite type over `ℂ`, restriction over any set of points of the base.
* `MMP.Analytic.exists_retraction_homology_of_hasUnitRetraction`: a retraction of the unit splits
  the induced map on cohomology.

## References

* [Iversen, *Cohomology of sheaves*], II.5 and VII.1.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite

attribute [local instance] HasDerivedCategory.standard

namespace MMP.Analytic

/-! ### Morphisms out of single complexes in the bounded below homotopy category -/

section SingleHom

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C]

/-- The morphism `a[0] ⟶ F(b[0])` of the bounded below homotopy category induced by a morphism
`x : a ⟶ F b`. -/
def singleHom (F : A ⥤ B) [F.Additive] {a : B} {b : A} (x : a ⟶ F.obj b) :
    (HomotopyCategory.Plus.singleFunctor B 0).obj a ⟶
      F.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj b) :=
  (HomotopyCategory.Plus.ι _).preimage ((HomotopyCategory.quotient _ _).map
    ((HomologicalComplex.single _ _ 0).map x ≫
      (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b))

/-- The image of `singleHom F x` in the homotopy category is the class of the composite of
`x[0]` with the identification `(F b)[0] ≅ F(b[0])`. -/
lemma ι_map_singleHom (F : A ⥤ B) [F.Additive] {a : B} {b : A} (x : a ⟶ F.obj b) :
    (HomotopyCategory.Plus.ι _).map (singleHom F x) = (HomotopyCategory.quotient _ _).map
    ((HomologicalComplex.single _ _ 0).map x ≫
      (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b) :=
  Functor.map_preimage _ _

/-- `singleHom F (x ≫ F.map z)` is `singleHom F x` followed by `F` applied to `z[0]`. -/
lemma singleHom_comp_map (F : A ⥤ B) [F.Additive] {a : B} {b b' : A} (x : a ⟶ F.obj b)
    (z : b ⟶ b') :
    singleHom F (x ≫ F.map z) =
      singleHom F x ≫ F.mapHomotopyCategoryPlus.map
        ((HomotopyCategory.Plus.singleFunctor A 0).map z) := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  rw [CategoryTheory.Functor.map_comp, ι_map_singleHom, ι_map_singleHom]
  have h : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (x ≫ F.map z) ≫
      (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b' =
      ((HomologicalComplex.single _ _ 0).map x ≫
        (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b) ≫
        (F.mapHomologicalComplex _).map ((HomologicalComplex.single _ _ 0).map z) := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      Functor.mapHomologicalComplex_map_f, CategoryTheory.Functor.map_comp, Category.assoc]
    simp
  exact (congrArg (HomotopyCategory.quotient B (.up ℤ)).map h).trans
    (CategoryTheory.Functor.map_comp _ _ _)

/-- `singleHom F (y ≫ x)` is `y[0]` followed by `singleHom F x`. -/
lemma singleHom_map_comp (F : A ⥤ B) [F.Additive] {a a' : B} {b : A} (y : a' ⟶ a)
    (x : a ⟶ F.obj b) :
    singleHom F (y ≫ x) = (HomotopyCategory.Plus.singleFunctor B 0).map y ≫ singleHom F x := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  rw [CategoryTheory.Functor.map_comp, ι_map_singleHom, ι_map_singleHom]
  have h : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (y ≫ x) ≫
      (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b =
      (HomologicalComplex.single _ _ 0).map y ≫ ((HomologicalComplex.single _ _ 0).map x ≫
        (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b) := by
    simp
  exact (congrArg (HomotopyCategory.quotient B (.up ℤ)).map h).trans
    (CategoryTheory.Functor.map_comp _ _ _)

/-- `singleHom` of a composite functor is the composite of the `singleHom`s. -/
lemma singleHom_comp (F₁ : A ⥤ B) (F₂ : B ⥤ C) [F₁.Additive] [F₂.Additive] {c : C} {b : B}
    {a : A} (x₂ : c ⟶ F₂.obj b) (x₁ : b ⟶ F₁.obj a) :
    singleHom (F₁ ⋙ F₂) (x₂ ≫ F₂.map x₁) =
      singleHom F₂ x₂ ≫ F₂.mapHomotopyCategoryPlus.map (singleHom F₁ x₁) := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  have e1 : (HomotopyCategory.Plus.ι _).map (F₂.mapHomotopyCategoryPlus.map (singleHom F₁ x₁)) =
      (HomotopyCategory.quotient _ _).map ((F₂.mapHomologicalComplex _).map
        ((HomologicalComplex.single _ _ 0).map x₁ ≫
          (HomologicalComplex.singleMapHomologicalComplex F₁ _ 0).inv.app a)) :=
    (congrArg (F₂.mapHomotopyCategory _).map (ι_map_singleHom F₁ x₁)).trans
      (Functor.mapHomotopyCategory_map _ _)
  have h : (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map (x₂ ≫ F₂.map x₁) ≫
      (HomologicalComplex.singleMapHomologicalComplex (F₁ ⋙ F₂) _ 0).inv.app a =
      ((HomologicalComplex.single _ _ 0).map x₂ ≫
        (HomologicalComplex.singleMapHomologicalComplex F₂ _ 0).inv.app b) ≫
        (F₂.mapHomologicalComplex _).map ((HomologicalComplex.single _ _ 0).map x₁ ≫
          (HomologicalComplex.singleMapHomologicalComplex F₁ _ 0).inv.app a) := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      Functor.mapHomologicalComplex_map_f, CategoryTheory.Functor.map_comp, Category.assoc,
      Functor.comp_map, Functor.comp_obj]
    simp
  refine (ι_map_singleHom _ _).trans (Eq.trans ?_ (CategoryTheory.Functor.map_comp _ _ _).symm)
  exact (congrArg (HomotopyCategory.quotient C (.up ℤ)).map h).trans
    ((CategoryTheory.Functor.map_comp _ _ _).trans
      (congrArg₂ (· ≫ ·) (ι_map_singleHom _ _).symm e1.symm))

end SingleHom

/-! ### The canonical morphism `ℚ_Z ⟶ f_* ℚ_{Z'}` -/

section ConstUnit

variable {Z Z' Z'' : TopCat.{0}}

/-- The canonical morphism `ℚ_Z ⟶ f_* ℚ_{Z'}` of sheaves of `ℚ`-vector spaces on `Z`, for a
continuous map `f : Z' ⟶ Z`: the adjoint, under `constantSheaf ⊣ Γ(Z, -)`, of the unit section
`ℚ ⟶ Γ(Z', ℚ_{Z'}) = Γ(Z, f_* ℚ_{Z'})`. -/
def constUnit (f : Z' ⟶ Z) :
    (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).obj
        ((constantSheaf (Opens.grothendieckTopology Z') (ModuleCat.{0} ℚ)).obj
          (ModuleCat.of ℚ ℚ)) :=
  ((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).homEquiv _ _).symm
    ((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).unit.app _)

/-- Under `constantSheafAdj`, `constUnit f` corresponds to the unit section of the constant
sheaf `ℚ_{Z'}`. -/
lemma homEquiv_constUnit (f : Z' ⟶ Z) :
    (constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ) isTerminalTop).homEquiv _ _
      (constUnit f) =
      (constantSheafAdj (Opens.grothendieckTopology Z') (ModuleCat.{0} ℚ) isTerminalTop).unit.app
        (ModuleCat.of ℚ ℚ) :=
  Equiv.apply_symm_apply _ _

/-- The canonical morphisms compose: `ℚ_Z ⟶ (g ≫ f)_* ℚ_{Z''}` is `ℚ_Z ⟶ f_* ℚ_{Z'}` followed by
`f_*` of `ℚ_{Z'} ⟶ g_* ℚ_{Z''}`. -/
lemma constUnit_comp (f : Z' ⟶ Z) (g : Z'' ⟶ Z') :
    constUnit (g ≫ f) = constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map
      (constUnit g) := by
  apply ((constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)
    isTerminalTop).homEquiv _ _).injective
  refine (homEquiv_constUnit (g ≫ f)).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_naturality_right _ _ _).symm
  refine (homEquiv_constUnit g).symm.trans ?_
  exact (Adjunction.homEquiv_unit _ _ _ _).trans
    (congrArg (· ≫ _) (homEquiv_constUnit f).symm)

/-- **The inverse image of the constant sheaf is constant**: the morphism `f⁻¹ ℚ_Z ⟶ ℚ_{Z'}`
adjoint to `constUnit f` is an isomorphism. -/
lemma isIso_homEquiv_symm_constUnit (f : Z' ⟶ Z) :
    IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).homEquiv _ _).symm
      (constUnit f)) := by
  let A := constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ) isTerminalTop
  let A' := constantSheafAdj (Opens.grothendieckTopology Z') (ModuleCat.{0} ℚ) isTerminalTop
  let P := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f
  let adj1 : constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ) ⋙
      TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ⊣
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        (sheafSections (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj (op ⊤) :=
    A.comp P
  let adj2 : constantSheaf (Opens.grothendieckTopology Z') (ModuleCat.{0} ℚ) ⊣
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        (sheafSections (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj (op ⊤) := A'
  have key : ((P.homEquiv _ _).symm (constUnit f)) =
      (adj1.leftAdjointUniq adj2).hom.app (ModuleCat.of ℚ ℚ) := by
    apply (P.homEquiv _ _).injective
    refine (Equiv.apply_symm_apply _ _).trans ?_
    apply (A.homEquiv _ _).injective
    refine (homEquiv_constUnit f).trans ?_
    refine (Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 _).symm.trans ?_
    refine Eq.trans ?_ (congrArg (A.homEquiv _ _) (P.homEquiv_unit _ _ _)).symm
    refine Eq.trans ?_ (A.homEquiv_unit (ModuleCat.of ℚ ℚ)
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).obj
        ((constantSheaf (Opens.grothendieckTopology Z') (ModuleCat.{0} ℚ)).obj
          (ModuleCat.of ℚ ℚ)))
      (P.unit.app _ ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map
        ((adj1.leftAdjointUniq adj2).hom.app (ModuleCat.of ℚ ℚ)))).symm
    exact (congrArg (· ≫ _) (Adjunction.comp_unit_app A P (ModuleCat.of ℚ ℚ))).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_comp
        ((sheafSections (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj (op ⊤))
        (P.unit.app _) ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map
          ((adj1.leftAdjointUniq adj2).hom.app (ModuleCat.of ℚ ℚ)))).symm))
  rw [key]
  exact Iso.isIso_hom ((adj1.leftAdjointUniq adj2).app _)

/-- The mate `τ : F ⋙ G ⟶ G' ⋙ F'` of `e : P' ⋙ F ≅ F' ⋙ P`, read through the adjunction
`G ⊣ P`: transposing `G x ≫ τ_b ≫ F' y` gives `x ≫ F (y♭) ≫ e`. -/
lemma homEquiv_map_comp_mate_app_comp {A' B' C' D' : Type*} [Category* A'] [Category* B']
    [Category* C'] [Category* D'] {G : B' ⥤ D'} {P : D' ⥤ B'} (adj : G ⊣ P) {G' : A' ⥤ C'}
    {P' : C' ⥤ A'} (adj' : G' ⊣ P') (F : A' ⥤ B') (F' : C' ⥤ D') (e : P' ⋙ F ≅ F' ⋙ P)
    {a : B'} {b : A'} {c : C'} (x : a ⟶ F.obj b) (y : G'.obj b ⟶ c) :
    adj.homEquiv _ _ (G.map x ≫ (Stacks.Cohomology.BaseChange.mate adj adj' F F' e).app b ≫
      F'.map y) = x ≫ F.map (adj'.homEquiv _ _ y) ≫ e.hom.app c := by
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_unit,
    CategoryTheory.Functor.map_comp, ← Category.assoc (adj.unit.app _),
    Stacks.Cohomology.BaseChange.unit_comp_map_mate, Adjunction.homEquiv_unit]
  have hn := e.hom.naturality y
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc, hn, CategoryTheory.Functor.map_comp]

end ConstUnit

/-! ### Units `a ⟶ RF b` induced by morphisms `a ⟶ F b` -/

section DerivedUnit

variable {A B C : Type*} [Category* A] [Category* B] [Category* C] [Abelian A] [Abelian B]
  [Abelian C] [EnoughInjectives A] [EnoughInjectives B]

/-- The morphism `a[0] ⟶ RF(b[0])` of bounded below derived categories induced by `x : a ⟶ F b`:
`x` in degree `0` followed by the comparison `F ⟶ RF`. For `F = f_*` and `x` the canonical
morphism `ℚ_Z ⟶ f_* ℚ_{Z'}` this is the structural unit `ℚ_Z ⟶ Rf_* ℚ_{Z'}`. -/
def derivedUnit (F : A ⥤ B) [F.Additive] {a : B} {b : A} (x : a ⟶ F.obj b) :
    DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj a) ⟶
      F.rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj b)) :=
  DerivedCategory.Plus.Qh.map (singleHom F x) ≫ F.rightDerivedFunctorPlusUnith.app _

/-- The unit induced by `x ≫ F z` is the unit induced by `x` followed by `RF` of `z`. -/
lemma derivedUnit_comp_map (F : A ⥤ B) [F.Additive] {a : B} {b b' : A} (x : a ⟶ F.obj b)
    (z : b ⟶ b') :
    derivedUnit F (x ≫ F.map z) = derivedUnit F x ≫ F.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor A 0).map z)) := by
  have hnat := F.rightDerivedFunctorPlusUnith.naturality
    ((HomotopyCategory.Plus.singleFunctor A 0).map z)
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  simp only [derivedUnit, singleHom_comp_map, CategoryTheory.Functor.map_comp, Category.assoc, hnat]

/-- The unit of a composite functor, followed by `R(F₁ ⋙ F₂) ≅ RF₂ ∘ RF₁`, is the composite of
the units. -/
lemma derivedUnit_comp (F₁ : A ⥤ B) (F₂ : B ⥤ C) [F₁.Additive] [F₂.Additive] {c : C} {b : B}
    {a : A} (x₂ : c ⟶ F₂.obj b) (x₁ : b ⟶ F₁.obj a) :
    derivedUnit (F₁ ⋙ F₂) (x₂ ≫ F₂.map x₁) ≫
        (Functor.rightDerivedFunctorPlusComp F₁ F₂).app _ =
      derivedUnit F₂ x₂ ≫ F₂.rightDerivedFunctorPlus.map (derivedUnit F₁ x₁) := by
  have hfac := Functor.rightDerivedFunctorPlusComp_fac_app F₁ F₂
    ((HomotopyCategory.Plus.singleFunctor A 0).obj a)
  have hnat := F₂.rightDerivedFunctorPlusUnith.naturality (singleHom F₁ x₁)
  have hid : DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (F₁ ⋙ F₂))).inv.app ((HomotopyCategory.Plus.singleFunctor A 0).obj a)) = 𝟙 _ :=
    DerivedCategory.Plus.Qh.map_id _
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  simp only [derivedUnit, Category.assoc, hfac, hid, singleHom_comp]
  erw [Category.id_comp, CategoryTheory.Functor.map_comp, Category.assoc, reassoc_of% hnat]
  rw [CategoryTheory.Functor.map_comp]

/-- The unit induced by `x` has a retraction. -/
def HasUnitRetraction (F : A ⥤ B) [F.Additive] {a : B} {b : A} (x : a ⟶ F.obj b) : Prop :=
  ∃ r, derivedUnit F x ≫ r = 𝟙 _

/-- Units with retractions compose. -/
theorem hasUnitRetraction_comp (F₁ : A ⥤ B) (F₂ : B ⥤ C) [F₁.Additive] [F₂.Additive]
    [F₁.PreservesInjectiveObjects] {c : C} {b : B} {a : A} {x₂ : c ⟶ F₂.obj b}
    {x₁ : b ⟶ F₁.obj a} (h₂ : HasUnitRetraction F₂ x₂) (h₁ : HasUnitRetraction F₁ x₁) :
    HasUnitRetraction (F₁ ⋙ F₂) (x₂ ≫ F₂.map x₁) := by
  obtain ⟨r₂, hr₂⟩ := h₂
  obtain ⟨r₁, hr₁⟩ := h₁
  refine ⟨(Functor.rightDerivedFunctorPlusComp F₁ F₂).app _ ≫
    F₂.rightDerivedFunctorPlus.map r₁ ≫ r₂, ?_⟩
  rw [reassoc_of% (derivedUnit_comp F₁ F₂ x₂ x₁), ← CategoryTheory.Functor.map_comp_assoc, hr₁,
    CategoryTheory.Functor.map_id, Category.id_comp, hr₂]

/-- If the unit of a composite `x₂ ≫ F₂ x₁` has a retraction, so has the unit of `x₂`. -/
theorem hasUnitRetraction_of_comp (F₁ : A ⥤ B) (F₂ : B ⥤ C) [F₁.Additive] [F₂.Additive]
    [F₁.PreservesInjectiveObjects] {c : C} {b : B} {a : A} {x₂ : c ⟶ F₂.obj b}
    {x₁ : b ⟶ F₁.obj a} (h : HasUnitRetraction (F₁ ⋙ F₂) (x₂ ≫ F₂.map x₁)) :
    HasUnitRetraction F₂ x₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨F₂.rightDerivedFunctorPlus.map (derivedUnit F₁ x₁) ≫
    inv ((Functor.rightDerivedFunctorPlusComp F₁ F₂).app _) ≫ r, ?_⟩
  rw [← Category.assoc, ← derivedUnit_comp F₁ F₂ x₂ x₁, Category.assoc, IsIso.hom_inv_id_assoc,
    hr]

/-- Retractions transfer along isomorphisms of the target: if the unit of `x` has a retraction
and `z` is invertible, so has the unit of `x ≫ F z`. -/
theorem HasUnitRetraction.comp_map {F : A ⥤ B} [F.Additive] {a : B} {b b' : A}
    {x : a ⟶ F.obj b} (h : HasUnitRetraction F x) (z : b ⟶ b') [IsIso z] :
    HasUnitRetraction F (x ≫ F.map z) := by
  obtain ⟨r, hr⟩ := h
  refine ⟨F.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map
    ((HomotopyCategory.Plus.singleFunctor A 0).map (inv z))) ≫ r, ?_⟩
  rw [derivedUnit_comp_map, Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
    CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp, hr]

/-- **A retraction of the unit splits the induced map on cohomology.** If `F` preserves injective
objects, the unit `a[0] ⟶ RF(b[0])` has a retraction and `Γ` is additive, then in every degree
`k` the map `Hᵏ(RΓ(a)) ⟶ Hᵏ(RΓ(RF b)) ≅ Hᵏ(R(F ⋙ Γ)(b))` has a retraction. -/
theorem exists_retraction_homology_of_hasUnitRetraction {D : Type*} [Category* D] [Abelian D]
    (F : A ⥤ B) (Γ : B ⥤ D) [F.Additive] [Γ.Additive] [F.PreservesInjectiveObjects] {a : B}
    {b : A} {x : a ⟶ F.obj b} (h : HasUnitRetraction F x) (k : ℤ) :
    ∃ r, (DerivedCategory.Plus.homologyFunctor D k).map
      (Γ.rightDerivedFunctorPlus.map (derivedUnit F x) ≫
        (Functor.rightDerivedFunctorPlusCompIso F Γ).inv.app _) ≫ r = 𝟙 _ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨(DerivedCategory.Plus.homologyFunctor D k).map
    ((Functor.rightDerivedFunctorPlusCompIso F Γ).hom.app _ ≫ Γ.rightDerivedFunctorPlus.map r),
      ?_⟩
  rw [← CategoryTheory.Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
    ← CategoryTheory.Functor.map_comp, hr, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]

/-- If the unit of `w ≫ x` has a retraction and `w` is invertible, so has the unit of `x`. -/
theorem HasUnitRetraction.of_iso_comp {F : A ⥤ B} [F.Additive] {a a' : B} {b : A}
    {x : a ⟶ F.obj b} (w : a' ⟶ a) [IsIso w] (h : HasUnitRetraction F (w ≫ x)) :
    HasUnitRetraction F x := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r ≫ DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor B 0).map w), ?_⟩
  have e : derivedUnit F (w ≫ x) = DerivedCategory.Plus.Qh.map
      ((HomotopyCategory.Plus.singleFunctor B 0).map w) ≫ derivedUnit F x := by
    simp only [derivedUnit, singleHom_map_comp, CategoryTheory.Functor.map_comp, Category.assoc]
  have hw : DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor B 0).map w) ≫
      derivedUnit F x ≫ r = 𝟙 _ := by rw [← Category.assoc, ← e, hr]
  rw [← cancel_epi (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.singleFunctor B 0).map w)),
    ← Category.assoc, ← Category.assoc, Category.assoc _ _ r, hw, Category.id_comp,
    Category.comp_id]

/-- For an exact functor and an isomorphism `x`, the induced unit is an isomorphism, so it has a
retraction. -/
theorem hasUnitRetraction_of_isIso (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {a : B} {b : A} (x : a ⟶ F.obj b) [IsIso x] :
    HasUnitRetraction F x := by
  have h1 : singleHom F x = (HomotopyCategory.Plus.singleFunctor B 0).map x ≫
      singleHom F (𝟙 (F.obj b)) := by
    rw [← singleHom_map_comp, Category.comp_id]
  have : IsIso (singleHom F (𝟙 (F.obj b))) := by
    have e := ι_map_singleHom F (𝟙 (F.obj b))
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at e
    have : IsIso ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app
      b) := inferInstance
    have : IsIso ((HomotopyCategory.Plus.ι B).map (singleHom F (𝟙 (F.obj b)))) := by
      rw [e]
      exact Functor.map_isIso _ _
    exact isIso_of_fully_faithful (HomotopyCategory.Plus.ι B) _
  have : IsIso (singleHom F x) := by
    rw [h1]
    infer_instance
  have : IsIso F.rightDerivedFunctorPlusUnith := Stacks.Cohomology.BaseChange.exactUnit_isIso F
  have i2 : IsIso (F.rightDerivedFunctorPlusUnith.app
    ((HomotopyCategory.Plus.singleFunctor A 0).obj b)) := NatIso.isIso_app_of_isIso _ _
  have : IsIso (derivedUnit F x) := IsIso.comp_isIso
  exact ⟨inv (derivedUnit F x), IsIso.hom_inv_id _⟩

end DerivedUnit

/-! ### Units under base change -/

section BaseChange

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]

/-- The identification `G(a[0]) ≅ (G a)[0]` in the bounded below homotopy category. -/
def singleIso (G : B ⥤ D) [G.Additive] (a : B) :
    G.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor B 0).obj a) ≅
      (HomotopyCategory.Plus.singleFunctor D 0).obj (G.obj a) :=
  (HomotopyCategory.Plus.ι D).preimageIso ((HomotopyCategory.quotient _ _).mapIso
    ((HomologicalComplex.singleMapHomologicalComplex G _ 0).app a))

/-- The image of `(singleIso G a).hom` in the homotopy category is the class of the canonical
morphism `G(a[0]) ⟶ (G a)[0]`. -/
lemma ι_map_singleIso_hom (G : B ⥤ D) [G.Additive] (a : B) :
    (HomotopyCategory.Plus.ι _).map (singleIso G a).hom = (HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex G _ 0).hom.app a) :=
  Functor.map_preimage _ _

/-- The image of `(singleIso G a).inv` in the homotopy category is the class of the canonical
morphism `(G a)[0] ⟶ G(a[0])`. -/
lemma ι_map_singleIso_inv (G : B ⥤ D) [G.Additive] (a : B) :
    (HomotopyCategory.Plus.ι _).map (singleIso G a).inv = (HomotopyCategory.quotient _ _).map
      ((HomologicalComplex.singleMapHomologicalComplex G _ 0).inv.app a) :=
  Functor.map_preimage _ _

variable (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]

/-- `singleHom` read through a degreewise transformation `τ : F ⋙ G ⟶ G' ⋙ F'`. -/
lemma map_singleHom_comp_mapPlus (τ : F ⋙ G ⟶ G' ⋙ F') {a : B} {b : A} (x : a ⟶ F.obj b) :
    G.mapHomotopyCategoryPlus.map (singleHom F x) ≫
        (Stacks.Cohomology.BaseChange.mapPlus τ).app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj b) =
      (singleIso G a).hom ≫ singleHom F' (G.map x ≫ τ.app b) ≫
        F'.mapHomotopyCategoryPlus.map (singleIso G' b).inv := by
  apply (HomotopyCategory.Plus.ι _).map_injective
  have e1 : (HomotopyCategory.Plus.ι _).map (G.mapHomotopyCategoryPlus.map (singleHom F x)) =
      (HomotopyCategory.quotient _ _).map ((G.mapHomologicalComplex _).map
        ((HomologicalComplex.single _ _ 0).map x ≫
          (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b)) :=
    (congrArg (G.mapHomotopyCategory _).map (ι_map_singleHom F x)).trans
      (Functor.mapHomotopyCategory_map _ _)
  have e2 : (HomotopyCategory.Plus.ι _).map ((Stacks.Cohomology.BaseChange.mapPlus τ).app
      ((HomotopyCategory.Plus.singleFunctor A 0).obj b)) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex τ _).app
        ((HomologicalComplex.single _ _ 0).obj b)) := rfl
  have e3 : (HomotopyCategory.Plus.ι _).map
      (F'.mapHomotopyCategoryPlus.map (singleIso G' b).inv) =
      (HomotopyCategory.quotient _ _).map ((F'.mapHomologicalComplex _).map
        ((HomologicalComplex.singleMapHomologicalComplex G' _ 0).inv.app b)) :=
    (congrArg (F'.mapHomotopyCategory _).map (ι_map_singleIso_inv G' b)).trans
      (Functor.mapHomotopyCategory_map _ _)
  have h' : (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).inv.app a ≫
      (G.mapHomologicalComplex _).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map x ≫
          (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b) ≫
        (NatTrans.mapHomologicalComplex τ _).app ((HomologicalComplex.single _ _ 0).obj b) =
      ((HomologicalComplex.single _ _ 0).map (G.map x ≫ τ.app b) ≫
          (HomologicalComplex.singleMapHomologicalComplex F' _ 0).inv.app (G'.obj b)) ≫
        (F'.mapHomologicalComplex _).map
          ((HomologicalComplex.singleMapHomologicalComplex G' _ 0).inv.app b) := by
    apply HomologicalComplex.from_single_hom_ext
    have hn := τ.naturality ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 b).inv)
    simp only [Functor.comp_map, Functor.comp_obj] at hn
    simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
      CategoryTheory.Functor.map_comp, Category.assoc, Functor.comp_map, Functor.comp_obj]
    have hG : ∀ {X Y : B} (e : X ≅ Y) {W : D} (k : G.obj Y ⟶ W),
        G.map e.inv ≫ G.map e.hom ≫ k = k := by
      intro X Y e W k
      rw [← CategoryTheory.Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
    have hF : ∀ {X Y : C} (e : X ≅ Y) {W : D} (k : F'.obj Y ⟶ W),
        F'.map e.inv ≫ F'.map e.hom ≫ k = k := by
      intro X Y e W k
      rw [← CategoryTheory.Functor.map_comp_assoc, e.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp]
    simp only [hG, hF, Iso.inv_hom_id_assoc, hn]
  have h : (G.mapHomologicalComplex _).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map x ≫
          (HomologicalComplex.singleMapHomologicalComplex F _ 0).inv.app b) ≫
        (NatTrans.mapHomologicalComplex τ _).app ((HomologicalComplex.single _ _ 0).obj b) =
      (HomologicalComplex.singleMapHomologicalComplex G _ 0).hom.app a ≫
        ((HomologicalComplex.single _ _ 0).map (G.map x ≫ τ.app b) ≫
          (HomologicalComplex.singleMapHomologicalComplex F' _ 0).inv.app (G'.obj b)) ≫
        (F'.mapHomologicalComplex _).map
          ((HomologicalComplex.singleMapHomologicalComplex G' _ 0).inv.app b) := by
    rw [← h', Iso.hom_inv_id_app_assoc]
  refine (CategoryTheory.Functor.map_comp _ _ _).trans ?_
  refine (congrArg₂ (· ≫ ·) e1 e2).trans ?_
  refine (CategoryTheory.Functor.map_comp _ _ _).symm.trans ?_
  refine (congrArg (HomotopyCategory.quotient D (ComplexShape.up ℤ)).map h).trans ?_
  refine (CategoryTheory.Functor.map_comp _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_comp _ _ _)).trans ?_
  have e4 : (HomotopyCategory.Plus.ι D).map ((singleIso G a).hom ≫
      singleHom F' (G.map x ≫ τ.app b) ≫ F'.mapHomotopyCategoryPlus.map (singleIso G' b).inv) =
      (HomotopyCategory.Plus.ι D).map (singleIso G a).hom ≫
        (HomotopyCategory.Plus.ι D).map (singleHom F' (G.map x ≫ τ.app b)) ≫
        (HomotopyCategory.Plus.ι D).map (F'.mapHomotopyCategoryPlus.map (singleIso G' b).inv) := by
    simp only [CategoryTheory.Functor.map_comp]
  refine Eq.trans ?_ e4.symm
  exact congrArg₂ (· ≫ ·) (ι_map_singleIso_hom G a).symm
    (congrArg₂ (· ≫ ·) (ι_map_singleHom F' _).symm e3.symm)

/-- The base change morphism of `Stacks.Cohomology.BaseChange.derived`, applied to the unit
induced by `x : a ⟶ F b`, is the unit induced by `G x ≫ τ_b`, up to the identifications
`G(a[0]) ≅ (G a)[0]` and `RG'(b[0]) ≅ (G' b)[0]`. -/
lemma map_derivedUnit_comp_derived (τ : F ⋙ G ⟶ G' ⋙ F')
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus) {a : B} {b : A} (x : a ⟶ F.obj b) :
    G.rightDerivedFunctorPlus.map (derivedUnit F x) ≫
        (Stacks.Cohomology.BaseChange.derived F F' G G' τ e).app _ =
      e.inv.app ((HomotopyCategory.Plus.singleFunctor B 0).obj a) ≫
        DerivedCategory.Plus.Qh.map (singleIso G a).hom ≫ derivedUnit F' (G.map x ≫ τ.app b) ≫
        F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (singleIso G' b).inv ≫
          G'.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.singleFunctor A 0).obj b)) := by
  have hO := NatTrans.congr_app (Stacks.Cohomology.BaseChange.derived_fac F F' G G' τ e)
    ((HomotopyCategory.Plus.singleFunctor A 0).obj b)
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
    Stacks.Cohomology.BaseChange.onHomotopy, Functor.whiskerRight_comp, Category.assoc,
    Functor.associator_inv_app, Category.comp_id] at hO
  have i1 : DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (F ⋙ G))).hom.app ((HomotopyCategory.Plus.singleFunctor A 0).obj b)) = 𝟙 _ :=
    DerivedCategory.Plus.Qh.map_id _
  have i2 : DerivedCategory.Plus.Qh.map ((Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (G' ⋙ F'))).inv.app ((HomotopyCategory.Plus.singleFunctor A 0).obj b)) = 𝟙 _ :=
    DerivedCategory.Plus.Qh.map_id _
  rw [i1, i2] at hO
  erw [Category.id_comp, Category.id_comp] at hO
  have hn1 := e.inv.naturality (singleHom F x)
  have hn2 := F'.rightDerivedFunctorPlusUnith.naturality (singleIso G' b).inv
  simp only [Functor.comp_map, Functor.comp_obj] at hn1 hn2
  have hm := congrArg DerivedCategory.Plus.Qh.map (map_singleHom_comp_mapPlus F F' G G' τ x)
  have hm' : DerivedCategory.Plus.Qh.map (G.mapHomotopyCategoryPlus.map (singleHom F x)) ≫
      DerivedCategory.Plus.Qh.map ((Stacks.Cohomology.BaseChange.mapPlus τ).app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj b)) =
      DerivedCategory.Plus.Qh.map (singleIso G a).hom ≫
        DerivedCategory.Plus.Qh.map (singleHom F' (G.map x ≫ τ.app b)) ≫
        DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map (singleIso G' b).inv) :=
    (CategoryTheory.Functor.map_comp DerivedCategory.Plus.Qh _ _).symm.trans (hm.trans
      ((CategoryTheory.Functor.map_comp DerivedCategory.Plus.Qh _ _).trans
        (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_comp DerivedCategory.Plus.Qh _ _))))
  rw [derivedUnit, CategoryTheory.Functor.map_comp, Category.assoc, hO]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hn1).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hm').trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc
    (DerivedCategory.Plus.Qh.map (singleHom F' (G.map x ≫ τ.app b)))
    (F'.rightDerivedFunctorPlusUnith.app _) _).symm
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hn2).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact (CategoryTheory.Functor.map_comp _ _ _).symm

/-- **Retractions of units are stable under base change.** Let `τ : F ⋙ G ⟶ G' ⋙ F'` be a
degreewise base change transformation whose descent to bounded below derived categories is
invertible at `b[0]`, with the comparison `G' ⟶ RG'` invertible (for instance, `G'` exact). If
the unit induced by `x : a ⟶ F b` has a retraction, so has the unit induced by `G x ≫ τ_b`. -/
theorem HasUnitRetraction.of_baseChange (τ : F ⋙ G ⟶ G' ⋙ F')
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
    [IsIso G'.rightDerivedFunctorPlusUnith] {a : B} {b : A} {x : a ⟶ F.obj b}
    (hBC : IsIso ((Stacks.Cohomology.BaseChange.derived F F' G G' τ e).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj b))))
    (h : HasUnitRetraction F x) : HasUnitRetraction F' (G.map x ≫ τ.app b) := by
  obtain ⟨ρ, hρ⟩ := h
  have key := map_derivedUnit_comp_derived F F' G G' τ e x
  let P := e.inv.app ((HomotopyCategory.Plus.singleFunctor B 0).obj a) ≫
    DerivedCategory.Plus.Qh.map (singleIso G a).hom
  let N := F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map (singleIso G' b).inv ≫
    G'.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.singleFunctor A 0).obj b))
  have hk : P ≫ derivedUnit F' (G.map x ≫ τ.app b) ≫ N =
      G.rightDerivedFunctorPlus.map (derivedUnit F x) ≫
        (Stacks.Cohomology.BaseChange.derived F F' G G' τ e).app _ := by
    rw [key]
    simp only [P, N, Category.assoc]
  refine ⟨N ≫ inv ((Stacks.Cohomology.BaseChange.derived F F' G G' τ e).app _) ≫
    G.rightDerivedFunctorPlus.map ρ ≫ P, ?_⟩
  rw [← cancel_epi P, ← Category.assoc, ← Category.assoc, Category.assoc P, hk, Category.assoc,
    IsIso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp_assoc, hρ,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end BaseChange

/-! ### Proper base change of the structural unit -/

section Topology

variable {X X' S S' : TopCat.{0}}

/-- For equal maps `k₁ = k₂`, `constUnit k₁` followed by the induced identification of
pushforwards is `constUnit k₂`. -/
lemma constUnit_comp_eqToIso {k₁ k₂ : X' ⟶ S} (h : k₁ = k₂) :
    constUnit k₁ ≫ (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)) h)).hom.app
      ((constantSheaf (Opens.grothendieckTopology X') (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)) =
      constUnit k₂ := by
  subst h
  exact Category.comp_id _

/-- For a commutative square `g' ≫ f = f' ≫ g`, the base change transformation
`g⁻¹ f_* ⟶ f'_* g'⁻¹` carries `g⁻¹` of `ℚ_S ⟶ f_* ℚ_X` to `ℚ_{S'} ⟶ f'_* ℚ_{X'}`, through
`g⁻¹ ℚ_S ≅ ℚ_{S'}` and `g'⁻¹ ℚ_X ≅ ℚ_{X'}`. -/
lemma map_constUnit_comp_mate (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hw : g' ≫ f = f' ≫ g) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).map (constUnit f) ≫
      (Stacks.Cohomology.BaseChange.mate
        (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g')
        (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f)
        (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f')
        (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)) hw))).app _ ≫
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f').map
        (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g').homEquiv _ _).symm
          (constUnit g')) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g).homEquiv _ _).symm
        (constUnit g) ≫ constUnit f' := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g
  let adj' := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g'
  apply (adj.homEquiv _ _).injective
  refine (homEquiv_map_comp_mate_app_comp adj adj' _ _ _ (constUnit f) _).trans ?_
  refine (congrArg (fun t ↦ constUnit f ≫ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map t ≫ _)
    (Equiv.apply_symm_apply _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (constUnit_comp f g').symm).trans ?_
  refine (constUnit_comp_eqToIso hw).trans ?_
  refine (constUnit_comp g f').trans ?_
  refine Eq.trans ?_ (adj.homEquiv_naturality_right ((adj.homEquiv _ _).symm (constUnit g))
    (constUnit f')).symm
  exact congrArg (· ≫ _) (Equiv.apply_symm_apply _ _).symm

/-- Direct image of sheaves of `ℚ`-vector spaces is additive. -/
lemma pushforward_additive (f : X ⟶ S) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Inverse image of sheaves of `ℚ`-vector spaces is additive. -/
lemma pullback_additive (f : X ⟶ S) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).Additive :=
  haveI : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

/-- Inverse image of sheaves of `ℚ`-vector spaces is left exact. -/
lemma pullback_preservesFiniteLimits (f : X ⟶ S) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f) := by
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

attribute [local instance] pullback_additive pullback_preservesFiniteLimits

/-- Direct image of sheaves of `ℚ`-vector spaces carries injective sheaves to injective sheaves:
its left adjoint, inverse image, is exact. -/
lemma pushforward_preservesInjectiveObjects (f : X ⟶ S) :
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)

attribute [local instance] pushforward_additive pushforward_preservesInjectiveObjects

/-- **The structural unit has a retraction after proper base change.** For a cartesian square of
topological spaces with `f` proper (separated and universally closed), if `ℚ_S ⟶ Rf_* ℚ_X` has a
retraction, so has `ℚ_{S'} ⟶ Rf'_* ℚ_{X'}`. -/
theorem hasUnitRetraction_constUnit_of_isPullback (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S)
    (g' : X' ⟶ X) (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{0, 0, 0} (f.hom : X → S))
    (h : HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) (constUnit f)) :
    HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f') (constUnit f') := by
  have : IsIso (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso _
  have : IsIso (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g').rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso _
  have hBC := (MMP.isIso_baseChange_of_isProperMap f f' g g' hcart hf).2 ℚ
    (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor _ 0).obj
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ))))
  have h1 := HasUnitRetraction.of_baseChange (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f)
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f') (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g)
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g') _ _ hBC h
  have := isIso_homEquiv_symm_constUnit g'
  have := isIso_homEquiv_symm_constUnit g
  have h2 := h1.comp_map
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g').homEquiv _ _).symm
      (constUnit g'))
  rw [Category.assoc, map_constUnit_comp_mate f f' g g' hcart.w] at h2
  exact h2.of_iso_comp _

/-- `constUnit (𝟙 Z)` is the identity. -/
lemma constUnit_id (Z : TopCat.{0}) : constUnit (𝟙 Z) = 𝟙 _ :=
  (congrArg _ (Adjunction.homEquiv_id _ _).symm).trans (Equiv.symm_apply_apply _ _)

/-- The structural unit of the identity has a retraction. -/
theorem hasUnitRetraction_constUnit_id (Z : TopCat.{0}) :
    HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (𝟙 Z)) (constUnit (𝟙 Z)) := by
  have : PreservesFiniteLimits (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (𝟙 Z)) :=
    inferInstanceAs (PreservesFiniteLimits (𝟭 _))
  have : PreservesFiniteColimits (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (𝟙 Z)) :=
    inferInstanceAs (PreservesFiniteColimits (𝟭 _))
  have : IsIso (C := TopCat.Sheaf (ModuleCat.{0} ℚ) Z) (constUnit (𝟙 Z)) :=
    ⟨⟨𝟙 _, (congrArg (· ≫ _) (constUnit_id Z)).trans (Category.id_comp _),
      (congrArg (_ ≫ ·) (constUnit_id Z)).trans (Category.comp_id _)⟩⟩
  exact hasUnitRetraction_of_isIso _ _

/-- If the derived unit of the adjunction unit `ℚ_S ⟶ f_* f⁻¹ ℚ_S` has a retraction, so has the
structural unit `ℚ_S ⟶ Rf_* ℚ_X`: the two differ by `f⁻¹ ℚ_S ≅ ℚ_X`. -/
theorem hasUnitRetraction_constUnit_of_unit (f : X ⟶ S)
    (h : HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app
        ((constantSheaf (Opens.grothendieckTopology S) (ModuleCat.{0} ℚ)).obj
          (ModuleCat.of ℚ ℚ)))) :
    HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) (constUnit f) := by
  have := isIso_homEquiv_symm_constUnit f
  have h2 := h.comp_map
    (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).homEquiv _ _).symm
      (constUnit f))
  have e : constUnit f =
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app _ ≫
        (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).map
          (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).homEquiv _ _).symm
            (constUnit f)) :=
    ((Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)).symm
  exact (congrArg (HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f)) e).mpr h2

/-- Having a retraction of the structural unit depends only on the map. -/
lemma hasUnitRetraction_constUnit_congr {f₁ f₂ : X ⟶ S} (h : f₁ = f₂) :
    HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f₁) (constUnit f₁) ↔
      HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f₂) (constUnit f₂) := by
  subst h
  rfl

/-- Retractions of structural units compose. -/
theorem hasUnitRetraction_constUnit_comp {Z : TopCat.{0}} {f : X ⟶ S} {g : Z ⟶ X}
    (hf : HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) (constUnit f))
    (hg : HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g) (constUnit g)) :
    HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (g ≫ f)) (constUnit (g ≫ f)) := by
  have h := hasUnitRetraction_comp (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g)
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) hf hg
  exact (congrArg (HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (g ≫ f)))
    (constUnit_comp f g)).mpr h

/-- If the structural unit of `g ≫ f` has a retraction, so has that of `f`. -/
theorem hasUnitRetraction_constUnit_of_comp {Z : TopCat.{0}} {f : X ⟶ S} {g : Z ⟶ X}
    (h : HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (g ≫ f))
      (constUnit (g ≫ f))) :
    HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) (constUnit f) := by
  have h' := (congrArg (HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (g ≫ f)))
    (constUnit_comp f g)).mp h
  exact hasUnitRetraction_of_comp (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g)
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f) h'

end Topology

section Analytic

open AlgebraicGeometry ComplexPoints

attribute [local instance] pushforward_additive pushforward_preservesInjectiveObjects

/-- **Restriction of the structural unit over a subset of the base.** Let `f : X ⟶ S` be a proper
morphism of schemes of finite type over `ℂ`. If the structural unit `ℚ_{S^an} ⟶ R(f^an)_* ℚ_{X^an}`
has a retraction, then for every set `Q` of points of `S` so has the structural unit of the
restriction `(f^an)⁻¹(Q^an) ⟶ Q^an`. -/
theorem hasUnitRetraction_constUnit_restrictPreimage {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sS : S ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] [QuasiCompact sX] [LocallyOfFiniteType sS]
    [QuasiCompact sS] (f : X ⟶ S) [IsProper f] (hf : f ≫ sS = sX)
    (h : HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (analyticMap f hf))
      (constUnit (analyticMap f hf))) (Q : Set S) :
    let fAn := analyticMap f hf
    let Qan : Set (analyticSpace sS) := {x | toScheme x ∈ Q}
    let fQ : TopCat.of (fAn ⁻¹' Qan) ⟶ TopCat.of Qan :=
      TopCat.ofHom ⟨Qan.restrictPreimage fAn, fAn.hom.continuous.restrictPreimage⟩
    HasUnitRetraction (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) fQ) (constUnit fQ) := by
  intro fAn Qan fQ
  have hp := isSeparatedMap_and_isProperMap_realize f hf
  exact hasUnitRetraction_constUnit_of_isPullback _ _ _ _ (isPullback_restrictPreimage fAn Qan)
    ⟨hp.1, hp.2.isUniversallyClosedMap⟩ h

end Analytic

end MMP.Analytic
