module

public import StacksFrontier.Topology.Sheaves.Functors.Pullback.UnitOnSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SubsingletonSectionsStalk

/-!
# The stalk of a cohomology sheaf from a base change to a point

Let `g : ⋆ ⟶ Y` pick out a point `y` of a space `Y`, let `f' : X' ⟶ ⋆` be the map of a space to
the point, and let `β : g⁻¹ L ≅ Rf'_* N` be an isomorphism in `D⁺(⋆)` for bounded below complexes
of sheaves `L` on `Y` and `N` on `X'`. Then the stalk at `y` of the cohomology sheaf `Hᵠ L` is the
hypercohomology `Hᵠ(X', N) = Hᵠ(RΓ(X', N))`: the stalk at `y` is the stalk of `g⁻¹` at the point,
an exact functor commutes with cohomology, the stalk at the point is the global sections, and
global sections on `X'` are `f'_*` followed by the global sections on the point.

With `β` the proper base change isomorphism for the fibre square over `y`, this is the stalk
formula `(Rᵠ f_* K)_y ≅ Hᵠ(f⁻¹ y, K|_{f⁻¹ y})`. The isomorphism is built from natural isomorphisms
only, so it is natural in `(L, N)` along any pair of morphisms compatible with `β`
(`MMP.Analytic.stalkHomologyIso_hom_naturality`); this is what computes the map induced on stalks
by a morphism of complexes.

## Main definitions

* `MMP.Analytic.homologyIsoOfExact`: `Φ(Hᵠ M) ≅ Hᵠ(RΦ M)` for an exact functor `Φ`.
* `MMP.Analytic.stalkHomologyIso`: `(Hᵠ L)_y ≅ Hᵠ(RΓ(X', N))`, given `β : g⁻¹ L ≅ Rf'_* N`.

## Main results

* `MMP.Analytic.ambientStalkHom_naturality`: the stalk comparison `F_{f x} ⟶ (f⁻¹ F)_x` is
  natural in `F`.
* `MMP.Analytic.homologyIsoOfExact_hom_naturality`: `homologyIsoOfExact` is natural in `M`.
* `MMP.Analytic.stalkHomologyIso_hom_naturality`: `stalkHomologyIso` is natural in `(L, N)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace MMP.Analytic

attribute [local instance] HasDerivedCategory.standard

/-- An exact functor `Φ` commutes with cohomology on bounded below derived categories:
`Φ(Hᵠ M) ≅ Hᵠ(RΦ M)`. -/
noncomputable def homologyIsoOfExact {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (Φ : A ⥤ B) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (q : ℤ) (M : DerivedCategory.Plus A) :
    Φ.obj ((DerivedCategory.Plus.homologyFunctor A q).obj M) ≅
      (DerivedCategory.Plus.homologyFunctor B q).obj (Φ.rightDerivedFunctorPlus.obj M) :=
  ((Φ.mapDerivedCategoryHomologyIso q).app M.obj).symm ≪≫
    (DerivedCategory.homologyFunctor B q).mapIso (DerivedCategory.Plus.ι.mapIso
      ((Φ.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).app M).symm)

/-- `homologyIsoOfExact` is natural in the complex. -/
@[reassoc]
theorem homologyIsoOfExact_hom_naturality {A B : Type*} [Category* A] [Category* B]
    [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
    (Φ : A ⥤ B) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ] (q : ℤ)
    {M M' : DerivedCategory.Plus A} (f : M ⟶ M') :
    Φ.map ((DerivedCategory.Plus.homologyFunctor A q).map f) ≫
        (homologyIsoOfExact Φ q M').hom =
      (homologyIsoOfExact Φ q M).hom ≫
        (DerivedCategory.Plus.homologyFunctor B q).map (Φ.rightDerivedFunctorPlus.map f) := by
  have h1 := (Φ.mapDerivedCategoryHomologyIso q).inv.naturality (DerivedCategory.Plus.ι.map f)
  have h2 := (Φ.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).inv.naturality f
  change Φ.map ((DerivedCategory.homologyFunctor A q).map (DerivedCategory.Plus.ι.map f)) ≫
      ((Φ.mapDerivedCategoryHomologyIso q).inv.app M'.obj ≫
        (DerivedCategory.homologyFunctor B q).map (DerivedCategory.Plus.ι.map
          ((Φ.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).inv.app M'))) =
    ((Φ.mapDerivedCategoryHomologyIso q).inv.app M.obj ≫
        (DerivedCategory.homologyFunctor B q).map (DerivedCategory.Plus.ι.map
          ((Φ.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus).inv.app M))) ≫
      (DerivedCategory.homologyFunctor B q).map
        (DerivedCategory.Plus.ι.map (Φ.rightDerivedFunctorPlus.map f))
  have h2' := congrArg (fun g => (DerivedCategory.homologyFunctor B q).map
    (DerivedCategory.Plus.ι.map g)) h2
  simp only [Functor.map_comp] at h2'
  exact (Category.assoc _ _ _).symm.trans ((h1 =≫ _).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h2').trans (Category.assoc _ _ _).symm)))

/-- The stalk comparison `F_{f x} ⟶ (f⁻¹ F)_x` is natural in the sheaf `F`. -/
@[reassoc]
theorem ambientStalkHom_naturality {C : Type 1} [Category.{0} C] [HasColimits C]
    [HasLimits C] {FC : C → C → Type*} {CC : C → Type} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [PreservesFilteredColimits (CategoryTheory.forget C)]
    [PreservesLimits (CategoryTheory.forget C)] [(CategoryTheory.forget C).ReflectsIsomorphisms]
    {X Y : TopCat.{0}} (f : X ⟶ Y) {F F' : TopCat.Sheaf C Y} (φ : F ⟶ F') (x : X) :
    Stacks.Topology.ambientStalkHom f F x ≫
        (TopCat.Presheaf.stalkFunctor C x).map ((TopCat.Sheaf.pullback C f).map φ).hom =
      (TopCat.Presheaf.stalkFunctor C (f x)).map φ.hom ≫
        Stacks.Topology.ambientStalkHom f F' x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  have h1 := Stacks.Topology.germ_unit_app f F U x hU s
  have h2 := Stacks.Topology.germ_unit_app f F' U x hU (φ.hom.app (Opposite.op U) s)
  have h3 := TopCat.Presheaf.stalkFunctor_map_germ_apply U (f x) hU φ.hom s
  have h4 := TopCat.Presheaf.stalkFunctor_map_germ_apply ((TopologicalSpace.Opens.map f).obj U)
    x hU ((TopCat.Sheaf.pullback C f).map φ).hom
    (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (Opposite.op U) s)
  have h5 : ((TopCat.Sheaf.pullback C f).map φ).hom.app
      (Opposite.op ((TopologicalSpace.Opens.map f).obj U))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (Opposite.op U) s) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F').hom.app (Opposite.op U)
        (φ.hom.app (Opposite.op U) s) := by
    have h := ConcreteCategory.congr_hom (congrArg (fun ψ => ψ.hom.app (Opposite.op U))
      ((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.naturality φ)) s
    exact ((ConcreteCategory.comp_apply
      (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F).hom.app (Opposite.op U))
      (((TopCat.Sheaf.pushforward C f).map ((TopCat.Sheaf.pullback C f).map φ)).hom.app
        (Opposite.op U)) s).symm.trans h.symm).trans
      (ConcreteCategory.comp_apply (φ.hom.app (Opposite.op U))
        (((TopCat.Sheaf.pullbackPushforwardAdjunction C f).unit.app F').hom.app
          (Opposite.op U)) s)
  have key := (congrArg _ h1.symm).trans (h4.trans ((congrArg _ h5).trans
    (h2.trans (congrArg _ h3.symm))))
  exact ((ConcreteCategory.comp_apply _ _ s).trans (ConcreteCategory.comp_apply _ _ _)).trans
    (key.trans ((ConcreteCategory.comp_apply _ _ _).symm.trans
      (ConcreteCategory.comp_apply _ _ s).symm))

/-- For a space `X'` over the point, `f'_*` followed by the stalk at the point is the global
sections functor on `X'`. -/
noncomputable def pushforwardStalkIsoSections {C : Type 1} [Category.{0} C] [HasColimits C]
    {X' : TopCat.{0}} (f' : X' ⟶ TopCat.of PUnit.{1}) :
    TopCat.Sheaf.pushforward C f' ⋙ TopCat.Sheaf.forget C (TopCat.of PUnit.{1}) ⋙
        TopCat.Presheaf.stalkFunctor C PUnit.unit ≅
      TopCat.Sheaf.forget C X' ⋙ (evaluation _ C).obj (Opposite.op ⊤) :=
  (NatIso.ofComponents (fun N => @asIso _ _ _ _ (TopCat.Presheaf.germ
      ((TopCat.Sheaf.pushforward C f').obj N).presheaf ⊤ PUnit.unit trivial)
      (Stacks.Topology.isIso_germ_of_subsingleton _ _ _ _)) (fun φ =>
    (TopCat.Presheaf.stalkFunctor_map_germ ⊤ PUnit.unit trivial
      ((TopCat.Sheaf.pushforward C f').map φ).hom).symm)).symm

variable {C : Type 1} [Category.{0} C] [HasColimits C]
    [HasLimits C] {FC : C → C → Type*} {CC : C → Type} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [PreservesFilteredColimits (CategoryTheory.forget C)]
    [PreservesLimits (CategoryTheory.forget C)] [(CategoryTheory.forget C).ReflectsIsomorphisms]
    [Abelian C] [HasDerivedCategory C] {Y X' : TopCat.{0}} (y : Y)
    (f' : X' ⟶ TopCat.of PUnit.{1})
    [EnoughInjectives (TopCat.Sheaf C Y)] [EnoughInjectives (TopCat.Sheaf C X')]
    [EnoughInjectives (TopCat.Sheaf C (TopCat.of PUnit.{1}))]
    [(TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y, continuous_const⟩)).Additive]
    [PreservesFiniteLimits
      (TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y, continuous_const⟩))]
    [(TopCat.Sheaf.pushforward C f').Additive]
    [(TopCat.Sheaf.forget C X' ⋙ (evaluation _ C).obj (Opposite.op ⊤)).Additive]

/-- **The stalk formula from base change to a point.** Let `g : ⋆ ⟶ Y` pick out `y` and let
`f' : X' ⟶ ⋆`. An isomorphism `β : g⁻¹ L ≅ Rf'_* N` in `D⁺(⋆)` identifies the stalk at `y` of
`Hᵠ L` with the hypercohomology `Hᵠ(X', N)`. -/
noncomputable def stalkHomologyIso
    {L : DerivedCategory.Plus (TopCat.Sheaf C Y)} {N : DerivedCategory.Plus (TopCat.Sheaf C X')}
    (β : (TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y,
        continuous_const⟩)).rightDerivedFunctorPlus.obj L ≅
      (TopCat.Sheaf.pushforward C f').rightDerivedFunctorPlus.obj N) (q : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor _ q).obj L).presheaf.stalk y ≅
      (DerivedCategory.Plus.homologyFunctor C q).obj
        ((TopCat.Sheaf.forget C X' ⋙
          (evaluation _ C).obj (Opposite.op ⊤)).rightDerivedFunctorPlus.obj N) :=
  let g : TopCat.of PUnit.{1} ⟶ Y := TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  let σ := TopCat.Sheaf.forget C (TopCat.of PUnit.{1}) ⋙
    TopCat.Presheaf.stalkFunctor C PUnit.unit
  asIso (Stacks.Topology.ambientStalkHom g _ PUnit.unit) ≪≫
    σ.mapIso (homologyIsoOfExact (TopCat.Sheaf.pullback C g) q L ≪≫
      (DerivedCategory.Plus.homologyFunctor _ q).mapIso β) ≪≫
    homologyIsoOfExact σ q _ ≪≫ (DerivedCategory.Plus.homologyFunctor C q).mapIso
      (((Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic _ σ
        (fun _ _ => σ.rightAcyclic_of_exact _)).app N).symm ≪≫
      (Functor.rightDerivedFunctorPlusNatIso (pushforwardStalkIsoSections f')).app N)

/-- **Naturality of the stalk formula.** For morphisms `φ : L ⟶ L'` and `ψ : N ⟶ N'` compatible
with `β` and `β'`, the stalk at `y` of `Hᵠ φ` corresponds to `Hᵠ(RΓ(X', ψ))`. -/
@[reassoc]
theorem stalkHomologyIso_hom_naturality
    {L L' : DerivedCategory.Plus (TopCat.Sheaf C Y)}
    {N N' : DerivedCategory.Plus (TopCat.Sheaf C X')}
    (β : (TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y,
        continuous_const⟩)).rightDerivedFunctorPlus.obj L ≅
      (TopCat.Sheaf.pushforward C f').rightDerivedFunctorPlus.obj N)
    (β' : (TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y,
        continuous_const⟩)).rightDerivedFunctorPlus.obj L' ≅
      (TopCat.Sheaf.pushforward C f').rightDerivedFunctorPlus.obj N')
    (φ : L ⟶ L') (ψ : N ⟶ N')
    (hβ : (TopCat.Sheaf.pullback C (TopCat.ofHom ⟨fun _ : PUnit.{1} => y,
        continuous_const⟩)).rightDerivedFunctorPlus.map φ ≫ β'.hom =
      β.hom ≫ (TopCat.Sheaf.pushforward C f').rightDerivedFunctorPlus.map ψ) (q : ℤ) :
    (TopCat.Presheaf.stalkFunctor C y).map
        ((DerivedCategory.Plus.homologyFunctor _ q).map φ).hom ≫
        (stalkHomologyIso y f' β' q).hom =
      (stalkHomologyIso y f' β q).hom ≫
        (DerivedCategory.Plus.homologyFunctor C q).map
          ((TopCat.Sheaf.forget C X' ⋙
            (evaluation _ C).obj (Opposite.op ⊤)).rightDerivedFunctorPlus.map ψ) := by
  let g : TopCat.of PUnit.{1} ⟶ Y := TopCat.ofHom ⟨fun _ => y, continuous_const⟩
  let σ := TopCat.Sheaf.forget C (TopCat.of PUnit.{1}) ⋙
    TopCat.Presheaf.stalkFunctor C PUnit.unit
  have n1 := ambientStalkHom_naturality g ((DerivedCategory.Plus.homologyFunctor _ q).map φ)
    PUnit.unit
  have n2 := homologyIsoOfExact_hom_naturality (TopCat.Sheaf.pullback C g) q φ
  have n3 := congrArg ((DerivedCategory.Plus.homologyFunctor _ q).map) hβ
  rw [Functor.map_comp, Functor.map_comp] at n3
  have n4 := homologyIsoOfExact_hom_naturality σ q
    ((TopCat.Sheaf.pushforward C f').rightDerivedFunctorPlus.map ψ)
  let H := DerivedCategory.Plus.homologyFunctor C q
  let H₀ := DerivedCategory.Plus.homologyFunctor (TopCat.Sheaf C (TopCat.of PUnit.{1})) q
  let c := Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic
    (TopCat.Sheaf.pushforward C f') σ (fun _ _ => σ.rightAcyclic_of_exact _)
  let n := Functor.rightDerivedFunctorPlusNatIso (pushforwardStalkIsoSections (C := C) f')
  let RΓ :=
    (TopCat.Sheaf.forget C X' ⋙ (evaluation _ C).obj (Opposite.op ⊤)).rightDerivedFunctorPlus
  let Rf := (TopCat.Sheaf.pushforward C f').rightDerivedFunctorPlus
  have n7 : H.map (σ.rightDerivedFunctorPlus.map (Rf.map ψ)) ≫
      H.map (c.inv.app N' ≫ n.hom.app N') =
      H.map (c.inv.app N ≫ n.hom.app N) ≫ H.map (RΓ.map ψ) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map ((c.symm ≪≫ n).hom.naturality ψ)).trans
      (H.map_comp _ _))
  let a := Stacks.Topology.ambientStalkHom g ((DerivedCategory.Plus.homologyFunctor _ q).obj L)
    PUnit.unit
  let a' := Stacks.Topology.ambientStalkHom g ((DerivedCategory.Plus.homologyFunctor _ q).obj L')
    PUnit.unit
  let A := (homologyIsoOfExact (TopCat.Sheaf.pullback C g) q L).hom
  let A' := (homologyIsoOfExact (TopCat.Sheaf.pullback C g) q L').hom
  let S := (homologyIsoOfExact σ q (Rf.obj N)).hom
  let S' := (homologyIsoOfExact σ q (Rf.obj N')).hom
  let P := (TopCat.Sheaf.pullback C g).map ((DerivedCategory.Plus.homologyFunctor _ q).map φ)
  change (TopCat.Presheaf.stalkFunctor C y).map
      ((DerivedCategory.Plus.homologyFunctor _ q).map φ).hom ≫
      (a' ≫ σ.map (A' ≫ H₀.map β'.hom) ≫ S' ≫ H.map (c.inv.app N' ≫ n.hom.app N')) =
    (a ≫ σ.map (A ≫ H₀.map β.hom) ≫ S ≫ H.map (c.inv.app N ≫ n.hom.app N)) ≫ H.map (RΓ.map ψ)
  have key : P ≫ A' ≫ H₀.map β'.hom = (A ≫ H₀.map β.hom) ≫ H₀.map (Rf.map ψ) :=
    ((Category.assoc _ _ _).symm.trans ((n2 =≫ _).trans (Category.assoc _ _ _))).trans
      ((congrArg (A ≫ ·) n3).trans (Category.assoc _ _ _).symm)
  have core : σ.map P ≫ σ.map (A' ≫ H₀.map β'.hom) =
      σ.map (A ≫ H₀.map β.hom) ≫ σ.map (H₀.map (Rf.map ψ)) :=
    (σ.map_comp _ _).symm.trans ((congrArg σ.map key).trans (σ.map_comp _ _))
  have tail : σ.map (H₀.map (Rf.map ψ)) ≫ S' ≫ H.map (c.inv.app N' ≫ n.hom.app N') =
      S ≫ H.map (c.inv.app N ≫ n.hom.app N) ≫ H.map (RΓ.map ψ) :=
    ((Category.assoc _ _ _).symm.trans ((n4 =≫ _).trans (Category.assoc _ _ _))).trans
      (congrArg (S ≫ ·) n7)
  refine ((Category.assoc _ _ _).symm.trans
    ((n1 =≫ _).trans (Category.assoc _ _ _))).symm.trans ?_
  refine (congrArg (a ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((core =≫ _).trans (Category.assoc _ _ _)))).trans ?_
  refine (congrArg (fun t => a ≫ σ.map (A ≫ H₀.map β.hom) ≫ t) tail).trans ?_
  exact ((Category.assoc a _ (H.map (RΓ.map ψ))).trans (congrArg (a ≫ ·)
    ((Category.assoc (σ.map (A ≫ H₀.map β.hom)) _ (H.map (RΓ.map ψ))).trans
      (congrArg (σ.map (A ≫ H₀.map β.hom) ≫ ·)
        (Category.assoc S (H.map (c.inv.app N ≫ n.hom.app N)) (H.map (RΓ.map ψ))))))).symm

end MMP.Analytic
