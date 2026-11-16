module
public import MMP.RingTheory.RegularLocalRing.FiniteFreeResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineProjectiveCompactification
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange

/-!
# Derived proper base change for topological spaces

Let

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

be a cartesian square of topological spaces in which `f` is proper in the sense of
[Stacks, Tag 005O] (5): separated and universally closed. The canonical base change morphism
`g⁻¹ Rf_* K ⟶ Rf'_* g'⁻¹ K`, the mate of `f_* g'_* = g_* f'_*` descended to
bounded below derived categories, is an isomorphism for every bounded below complex `K` of
abelian sheaves on `X`, and likewise for every bounded below complex of sheaves of modules
over a `ℚ`-algebra `R` (in particular of sheaves of `ℚ`-vector spaces). Taking `Y'` a point
identifies the stalk `(Rf_* K)_y` with the hypercohomology of the fibre `f⁻¹(y)` with
coefficients in the restriction of `K`.

## Main results

* `MMP.isIso_baseChange_of_isProperMap`: the base change morphism is invertible on bounded
  below complexes of abelian sheaves and of sheaves of `R`-modules, `R` a `ℚ`-algebra.

## Implementation notes

For abelian sheaves the base change morphism is
`Stacks.Cohomology.BaseChange.abelianBaseChange`. For sheaves of `R`-modules it is the same
construction, `Stacks.Cohomology.BaseChange.derived` applied to the mate
`Stacks.Cohomology.BaseChange.mate` of the inverse image/direct image adjunctions and to the
identification of the derived inverse image with the degreewise one (inverse image of sheaves
being exact); it is written out in the statement.

## References

* [Stacks Project, Tag 09V6](https://stacks.math.columbia.edu/tag/09V6)
* [SGA4, Exposé V bis, 4.1.1]
-/

section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

variable {X X' Y Y' : TopCat.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)

namespace MMP.Internal.TopologicalProperBaseChange

attribute [local instance] HasDerivedCategory.standard

section Forget

variable (R : Type u) [Ring R]

/-- The forgetful functor from sheaves of `R`-modules to abelian sheaves. -/
private noncomputable abbrev forgetSheaf (X : TopCat.{u}) :
    TopCat.Sheaf (ModuleCat.{u} R) X ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafCompose (Opens.grothendieckTopology X) (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

variable {X Y : TopCat.{u}} (k : X ⟶ Y)

/-- The comparison `g⁻¹ U ⟶ U g⁻¹` of inverse images across the forgetful functor `U`: the mate
of the equality `g_* U = U g_*` of direct images. -/
private noncomputable def forgetPullback :
    forgetSheaf R Y ⋙ TopCat.Sheaf.pullback AddCommGrpCat.{u} k ⟶
      TopCat.Sheaf.pullback (ModuleCat.{u} R) k ⋙ forgetSheaf R X :=
  Stacks.Cohomology.BaseChange.mate
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} k)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) k) (forgetSheaf R Y)
    (forgetSheaf R X) (Iso.refl _)

/-- Transposed across the inverse image/direct image adjunction, the comparison
`forgetPullback` is `U` applied to the unit of the adjunction for sheaves of modules. -/
private theorem forgetPullback_unit (G : TopCat.Sheaf (ModuleCat.{u} R) Y) :
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} k).unit.app
        ((forgetSheaf R Y).obj G) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} k).map ((forgetPullback R k).app G) =
    (forgetSheaf R Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) k).unit.app G) := by
  have := Stacks.Cohomology.BaseChange.unit_comp_map_mate
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} k)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) k) (forgetSheaf R Y)
    (forgetSheaf R X) (Iso.refl _) G
  exact this.trans (Category.comp_id _)

/-- The stalk of the underlying abelian presheaf is the underlying abelian group of the stalk,
`forget₂` preserving colimits. -/
private noncomputable def stalkForgetIso (P : TopCat.Presheaf (ModuleCat.{u} R) X) (x : X) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj (P.stalk x) ≅
      TopCat.Presheaf.stalk (P ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) x :=
  preservesColimitIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) _

/-- `stalkForgetIso` on germs. -/
private theorem germ_stalkForgetIso_inv (P : TopCat.Presheaf (ModuleCat.{u} R) X) (x : X)
    (V : Opens X) (hx : x ∈ V) :
    TopCat.Presheaf.germ (P ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) V x hx ≫
      (stalkForgetIso R P x).inv =
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map (P.germ V x hx) :=
  ι_preservesColimitIso_inv (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
    ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ P) (op ⟨V, hx⟩)

/-- **The stalk of `forgetPullback`.** Up to the stalk comparisons of inverse images
(`Stacks.Topology.ambientStalkHom`) and of `stalkForgetIso`, the stalk at `x` of the comparison
`g⁻¹ U G ⟶ U g⁻¹ G` is the identity of the stalk of `G` at the image point. Checked on germs. -/
private theorem forgetPullback_stalk (G : TopCat.Sheaf (ModuleCat.{u} R) Y) (x : X) :
    Stacks.Topology.ambientStalkHom k ((forgetSheaf R Y).obj G) x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((forgetPullback R k).app G).hom ≫
      (stalkForgetIso R ((TopCat.Sheaf.pullback (ModuleCat.{u} R) k).obj G).presheaf x).inv =
    (stalkForgetIso R G.presheaf ((k : X → Y) x)).inv ≫
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map
        (Stacks.Topology.ambientStalkHom k G x) := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun V hxV => ConcreteCategory.hom_ext _ _ fun s => ?_
  have h1 := Stacks.Topology.germ_ambientSection k ((forgetSheaf R Y).obj G)
    (le_refl ((Opens.map k).obj V)) x hxV s
  have h2 := Stacks.Topology.germ_ambientSection k G
    (le_refl ((Opens.map k).obj V)) x hxV s
  have hsrc := Stacks.Topology.ambientSection_eq_unit k ((forgetSheaf R Y).obj G) V
  have htgt := Stacks.Topology.ambientSection_eq_unit k G V
  have hunit := ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.hom.app (op V)) (forgetPullback_unit R k G)) s
  have e3 := ConcreteCategory.congr_hom (germ_stalkForgetIso_inv R
    ((TopCat.Sheaf.pullback (ModuleCat.{u} R) k).obj G).presheaf x ((Opens.map k).obj V) hxV)
  have e3' := ConcreteCategory.congr_hom (germ_stalkForgetIso_inv R G.presheaf (k x) V hxV) s
  refine (ConcreteCategory.comp_apply _ _ s).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg _ h1.symm).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  refine (congrArg _ (TopCat.Presheaf.stalkFunctor_map_germ_apply _ _ _ _ _)).trans ?_
  refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
  refine (e3 _).trans ?_
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (Category.assoc _ _ _) s)
  refine Eq.trans ?_ (ConcreteCategory.comp_apply _ _ s).symm
  refine Eq.trans ?_ (congrArg _ e3'.symm)
  have hstep : ((forgetPullback R k).app G).hom.app (op ((Opens.map k).obj V))
      (Stacks.Topology.ambientSection k ((forgetSheaf R Y).obj G)
        (le_refl ((Opens.map k).obj V)) s) =
      Stacks.Topology.ambientSection k G (le_refl ((Opens.map k).obj V)) s := by
    refine (congrArg _ (ConcreteCategory.congr_hom hsrc s)).trans ?_
    refine (ConcreteCategory.comp_apply _ _ s).symm.trans ?_
    refine hunit.trans ?_
    exact (ConcreteCategory.congr_hom htgt s).symm
  refine (congrArg _ hstep).trans ?_
  exact h2

/-- `forgetPullback` is invertible: it is so on every stalk. -/
private instance isIso_forgetPullback_app (G : TopCat.Sheaf (ModuleCat.{u} R) Y) :
    IsIso ((forgetPullback R k).app G) := by
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro x
  have := Stacks.Topology.isIso_ambientStalkHom k G x
  have h : IsIso (Stacks.Topology.ambientStalkHom k ((forgetSheaf R Y).obj G) x ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((forgetPullback R k).app G).hom ≫
      (stalkForgetIso R ((TopCat.Sheaf.pullback (ModuleCat.{u} R) k).obj G).presheaf x).inv) := by
    rw [forgetPullback_stalk]
    exact IsIso.comp_isIso' (Iso.isIso_inv _) (Functor.map_isIso _ _)
  have := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _
    (Stacks.Topology.isIso_ambientStalkHom k ((forgetSheaf R Y).obj G) x) h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _
    (stalkForgetIso R ((TopCat.Sheaf.pullback (ModuleCat.{u} R) k).obj G).presheaf x).inv
    (Iso.isIso_inv _) this

private instance isIso_forgetPullback : IsIso (forgetPullback R k) :=
  NatIso.isIso_of_isIso_app _

section Exact

variable (X : TopCat.{u})

private instance : (forgetSheaf R X).ReflectsIsomorphisms :=
  inferInstanceAs ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).ReflectsIsomorphisms)

private instance : (forgetSheaf R X).Faithful :=
  inferInstanceAs ((sheafCompose (Opens.grothendieckTopology X)
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).Faithful)

/-- `U` is left exact: limits of sheaves are computed on presheaves, where `U` is composition
with the limit-preserving `forget₂`. -/
private instance : PreservesFiniteLimits (forgetSheaf R X) := by
  have : PreservesFiniteLimits (forgetSheaf R X ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})))
  have h : ReflectsFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  exact @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _ (forgetSheaf R X)
    (sheafToPresheaf _ _) this h

private instance : (forgetSheaf R X).Additive where
  map_add := rfl

/-- `U` preserves epimorphisms: these are the locally surjective morphisms on both sides, and `U`
does not change the underlying presheaf of sets. -/
private instance : (forgetSheaf R X).PreservesEpimorphisms where
  preserves {F G} φ hφ := by
    have h : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' _ φ).2 hφ
    have h' : Sheaf.IsLocallySurjective ((forgetSheaf R X).map φ) :=
      (Presheaf.isLocallySurjective_iff_whisker_forget _ _).2
        ((Presheaf.isLocallySurjective_iff_whisker_forget _ φ.hom).1 h)
    exact (Sheaf.isLocallySurjective_iff_epi' _ _).1 h'

/-- `U` is right exact, being left exact and preserving epimorphisms. -/
private instance : PreservesFiniteColimits (forgetSheaf R X) := by
  refine ((Functor.preservesFiniteColimits_tfae (forgetSheaf R X)).out 1 4).1 fun S hS => ?_
  have hl : PreservesFiniteLimits (forgetSheaf R X) := inferInstance
  have h41 := (Functor.preservesFiniteLimits_tfae (forgetSheaf R X)).out 4 1
  refine ⟨(h41.1 hl S hS).1, ?_⟩
  have := hS.epi_g
  infer_instance

private instance : (forgetSheaf R X).PreservesHomology :=
  inferInstance

/-- For a `ℚ`-algebra `R`, which is flat over `ℤ`, `R ⊗_ℤ -` preserves monomorphisms. -/
private instance [Algebra ℚ R] : (ModuleCat.extendScalarsFromInt.{u} R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    have := IsAddTorsionFree.of_module_rat (M := R)
    have hinj : Function.Injective f.hom.toIntLinearMap :=
      (AddCommGrpCat.mono_iff_injective f).1 hf
    rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := R) _ hinj

/-- The sheafified `R ⊗_ℤ -` is left adjoint to `U`. -/
private noncomputable def sheafAdj :
    Sheaf.composeAndSheafify (Opens.grothendieckTopology X)
        (ModuleCat.extendScalarsFromInt.{u} R) ⊣
      forgetSheaf R X :=
  Sheaf.adjunction _ (ModuleCat.extendScalarsFromIntAdj.{u} R)

/-- The sheafified `R ⊗_ℤ -` preserves monomorphisms: sheafification is left exact. -/
private instance sheafExtend_preservesMono [Algebra ℚ R] :
    (Sheaf.composeAndSheafify (Opens.grothendieckTopology X)
      (ModuleCat.extendScalarsFromInt.{u} R)).PreservesMonomorphisms where
  preserves {A B} φ hφ := by
    have h1 : Mono φ.hom := (sheafToPresheaf _ _).map_mono φ
    have h2 : Mono (Functor.whiskerRight φ.hom (ModuleCat.extendScalarsFromInt.{u} R)) := by
      have : ∀ U, Mono (φ.hom.app U) := fun U => inferInstance
      exact NatTrans.mono_of_mono_app _
    exact (presheafToSheaf _ _).map_mono _

/-- **`U` preserves injective objects**, its left adjoint preserving monomorphisms. -/
private instance [Algebra ℚ R] : (forgetSheaf R X).PreservesInjectiveObjects :=
  @Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms _ _ _ _ _ _
    (sheafAdj R X) (sheafExtend_preservesMono R X)

end Exact

/-- `U` carries the comparison of direct images along equal maps to the same comparison. -/
private theorem forget_map_eqToIso {X' Y : TopCat.{u}} {k k' : X' ⟶ Y} (hk : k = k')
    (M : TopCat.Sheaf (ModuleCat.{u} R) X') :
    (forgetSheaf R Y).map
        ((eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{u} R)) hk)).hom.app M) =
      (eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u}) hk)).hom.app
        ((forgetSheaf R X').obj M) := by
  subst hk
  rfl

variable {X X' Y Y' : TopCat.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)

/-- The underived base change morphism `g⁻¹ f_* ⟶ f'_* g'⁻¹` of sheaves of `R`-modules. -/
private noncomputable abbrev moduleMate (hw : g' ≫ f = f' ≫ g) :=
  Stacks.Cohomology.BaseChange.mate
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g')
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f)
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f')
    (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{u} R)) hw))

/-- The diagram chase behind `forgetPullback_comp_moduleMate`, with every object and morphism a
variable so that it applies by a single `exact`. -/
private theorem chain_eq {C : Type*} [Category C] {A B C' D E P Q : C}
    (u : A ⟶ B) (b : B ⟶ C') (m : C' ⟶ D) (m' : B ⟶ E) (b' : E ⟶ D) (v : A ⟶ C')
    (w : A ⟶ D) (a : A ⟶ P) (e : P ⟶ E) (c : P ⟶ Q) (e' : Q ⟶ D) (d : A ⟶ Q)
    (X Y : B ⟶ D) (hX : X = b ≫ m) (hY : Y = m' ≫ b')
    (h1 : u ≫ b = v) (h2 : v ≫ m = w) (h3 : u ≫ m' = a ≫ e) (h5 : e ≫ b' = c ≫ e')
    (h4 : a ≫ c = d) (hw : w = d ≫ e') : u ≫ X = u ≫ Y := by
  rw [hX, hY, ← Category.assoc, h1, h2, ← Category.assoc, h3, Category.assoc, h5,
    ← Category.assoc, h4, hw]

/-- **The module base change morphism after `U` is the abelian one**, up to the comparisons
`forgetPullback` of inverse images. Both sides are determined by their transposes across the
adjunction of `g`, which are computed by `Stacks.Cohomology.BaseChange.unit_comp_map_mate`. -/
private theorem forgetPullback_comp_moduleMate (hw : g' ≫ f = f' ≫ g)
    (F : TopCat.Sheaf (ModuleCat.{u} R) X) :
    (forgetPullback R g).app ((TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).obj F) ≫
      (forgetSheaf R Y').map ((moduleMate R f f' g g' hw).app F) =
    (Stacks.Cohomology.BaseChange.abelianSheafBaseChange f f' g g' hw).app
        ((forgetSheaf R X).obj F) ≫
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').map ((forgetPullback R g').app F) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).homEquiv _ _).injective
  refine ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).homEquiv_unit
    _ _ _).trans (Eq.trans ?_
      ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).homEquiv_unit
        _ _ _).symm)
  have h1 := forgetPullback_unit R g ((TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).obj F)
  have h2M := Stacks.Cohomology.BaseChange.unit_comp_map_mate
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g')
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f)
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f')
    (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{u} R)) hw)) F
  have h3 := Stacks.Cohomology.BaseChange.abelianSheafBaseChange_unit f f' g g' hw
    ((forgetSheaf R X).obj F)
  have h4 := forgetPullback_unit R g' F
  have h5 := (eqToIso (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u}) hw)).hom.naturality
    ((forgetPullback R g').app F)
  have h6 := forget_map_eqToIso R hw
    ((TopCat.Sheaf.pullback (ModuleCat.{u} R) g').obj F)
  exact chain_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Functor.map_comp _ _ _) (Functor.map_comp _ _ _)
    h1 (((forgetSheaf R Y).map_comp _ _).symm.trans
      ((congrArg (forgetSheaf R Y).map h2M).trans ((forgetSheaf R Y).map_comp _ _)))
    h3 h5.symm (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map_comp _ _).symm.trans
      (congrArg (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map h4))
    (congrArg _ h6)

end Forget

/-- The underived base change morphism `g⁻¹ f_* ⟶ f'_* g'⁻¹` of sheaves of `R`-modules is an
isomorphism for `f` proper: after the forgetful functor it is the abelian base change morphism,
up to the invertible comparisons of inverse images. -/
private theorem isIso_moduleSheafBaseChange_of_properMap (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y))
    (R : Type u) [Ring R] [Algebra ℚ R] :
    IsIso (Stacks.Cohomology.BaseChange.mate
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g)
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g')
      (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f)
      (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f')
      (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{u} R)) hcart.w))) := by
  have := Stacks.Cohomology.AbelianProperBaseChange.isIso_abelianSheafBaseChange_of_properMap
    f f' g g' hcart hf
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (moduleMate R f f' g g' hcart.w) fun F => ?_
  have : IsIso ((forgetPullback R g).app ((TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).obj F) ≫
      (forgetSheaf R Y').map ((moduleMate R f f' g g' hcart.w).app F)) := by
    rw [forgetPullback_comp_moduleMate]
    exact IsIso.comp_isIso' (NatIso.isIso_app_of_isIso _ _) (Functor.map_isIso _ _)
  have := @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _) this
  exact isIso_of_reflects_iso _ (forgetSheaf R Y')

/-- A faithful additive functor reflects zero objects. -/
private theorem isZero_of_isZero_map {C D : Type*} [Category C] [Preadditive C] [Category D]
    [Preadditive D] (G : C ⥤ D) [G.Additive] [G.Faithful] {M : C} (h : IsZero (G.obj M)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply G.map_injective
  rw [G.map_id, G.map_zero]
  exact h.eq_of_src _ _

/-- The higher direct images `R^p f'_* (g'⁻¹ I)`, `p > 0`, of the inverse image of an injective
sheaf of `R`-modules vanish for `f` proper. -/
private theorem rightAcyclic_pushforward_pullback_of_injective_module
    (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y))
    (R : Type u) [Ring R] [Algebra ℚ R]
    (I : TopCat.Sheaf (ModuleCat.{u} R) X) (hI : Injective I) :
    letI : (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').Additive :=
      (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').additive_of_preserves_binary_products
    letI : EnoughInjectives (TopCat.Sheaf (ModuleCat.{u} R) X') :=
      IsGrothendieckAbelian.enoughInjectives
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').rightAcyclic
      ((TopCat.Sheaf.pullback (ModuleCat.{u} R) g').obj I) := by
  have : (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').Additive :=
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').additive_of_preserves_binary_products
  have : EnoughInjectives (TopCat.Sheaf (ModuleCat.{u} R) X') :=
    IsGrothendieckAbelian.enoughInjectives
  have hpl : PreservesFiniteLimits (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f') :=
    have := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R)
      f').rightAdjoint_preservesLimits
    inferInstance
  have hplA : PreservesFiniteLimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f') :=
    have := (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      f').rightAdjoint_preservesLimits
    inferInstance
  have hAadd : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').Additive :=
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').additive_of_preserves_binary_products
  have hab :=
    Stacks.Cohomology.AbelianProperBaseChange.rightAcyclic_pushforward_pullback_of_injective
      f f' g g' hcart hf ((forgetSheaf R X).obj I) ((forgetSheaf R X).injective_obj I)
  rw [Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived] at hab ⊢
  intro p hp
  apply isZero_of_isZero_map (forgetSheaf R Y')
  refine IsZero.of_iso ?_ ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f') (forgetSheaf R Y')
    (forgetSheaf R X' ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} f') (Iso.refl _) p).app _)
  refine IsZero.of_iso ?_ (Functor.rightDerivedObjIsoOfComp (forgetSheaf R X')
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (forgetSheaf R X' ⋙ TopCat.Sheaf.pushforward AddCommGrpCat.{u} f')
    (fun J hJ => (forgetSheaf R X').injective_obj J) (Iso.refl _) _ p).symm
  refine IsZero.of_iso (hab p hp) ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f').rightDerived
    p |>.mapIso (asIso ((forgetPullback R g').app I))).symm

end MMP.Internal.TopologicalProperBaseChange

namespace MMP

attribute [local instance] HasDerivedCategory.standard

open MMP.Internal.TopologicalProperBaseChange in
/-- **Derived proper base change** ([Stacks, Tag 09V6]). For a cartesian square of topological
spaces with `f` separated and universally closed, the base change morphism
`g⁻¹ Rf_* K ⟶ Rf'_* g'⁻¹ K` is an isomorphism for every bounded below complex `K` of abelian
sheaves on `X`, and for every bounded below complex `K` of sheaves of `R`-modules, `R` any
`ℚ`-algebra (for instance sheaves of `ℚ`-vector spaces). -/
@[mmp "lem_mmp_foundation_topological_proper_base_change"]
public theorem isIso_baseChange_of_isProperMap {X X' Y Y' : TopCat.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (hcart : IsPullback g' f' f g)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (f.hom : X → Y)) :
    (∀ K : DerivedCategory.Plus (TopCat.Sheaf AddCommGrpCat.{u} X),
      IsIso ((Stacks.Cohomology.BaseChange.abelianBaseChange f f' g g' hcart.w).app K)) ∧
    ∀ (R : Type u) [Ring R] [Algebra ℚ R],
      letI : (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).Additive :=
        (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).additive_of_preserves_binary_products
      letI : (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').Additive :=
        (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').additive_of_preserves_binary_products
      letI : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{u} R) g) :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts _
      letI : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{u} R) g') :=
        preservesBinaryBiproducts_of_preservesBinaryCoproducts _
      letI : (TopCat.Sheaf.pullback (ModuleCat.{u} R) g).Additive :=
        Functor.additive_of_preservesBinaryBiproducts _
      letI : (TopCat.Sheaf.pullback (ModuleCat.{u} R) g').Additive :=
        Functor.additive_of_preservesBinaryBiproducts _
      letI : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{u} R) g) :=
        by apply Functor.sheafPullbackConstruction.preservesFiniteLimits
      haveI : IsIso (TopCat.Sheaf.pullback (ModuleCat.{u} R) g).rightDerivedFunctorPlusUnith :=
        Stacks.Cohomology.BaseChange.exactUnit_isIso _
      ∀ K : DerivedCategory.Plus (TopCat.Sheaf (ModuleCat.{u} R) X),
        IsIso ((Stacks.Cohomology.BaseChange.derived
          (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f)
          (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f')
          (TopCat.Sheaf.pullback (ModuleCat.{u} R) g)
          (TopCat.Sheaf.pullback (ModuleCat.{u} R) g')
          (Stacks.Cohomology.BaseChange.mate
            (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g)
            (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g')
            (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f)
            (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f')
            (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{u} R)) hcart.w)))
          (asIso (TopCat.Sheaf.pullback (ModuleCat.{u} R) g).rightDerivedFunctorPlusUnith)).app
            K) := by
  refine ⟨fun K => Stacks.Cohomology.AbelianProperBaseChange.isIso_abelianBaseChange_app
    f f' g g' hcart hf K, ?_⟩
  intro R _ _ K
  have : (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).Additive :=
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f).additive_of_preserves_binary_products
  have : (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').Additive :=
    (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f').additive_of_preserves_binary_products
  have : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{u} R) g) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : PreservesBinaryBiproducts (TopCat.Sheaf.pullback (ModuleCat.{u} R) g') :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have : (TopCat.Sheaf.pullback (ModuleCat.{u} R) g).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : (TopCat.Sheaf.pullback (ModuleCat.{u} R) g').Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{u} R) g) := by
    apply Functor.sheafPullbackConstruction.preservesFiniteLimits
  have : IsIso (TopCat.Sheaf.pullback (ModuleCat.{u} R) g).rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso _
  have _heiX : EnoughInjectives (TopCat.Sheaf (ModuleCat.{u} R) X) :=
    IsGrothendieckAbelian.enoughInjectives
  have _heiX' : EnoughInjectives (TopCat.Sheaf (ModuleCat.{u} R) X') :=
    IsGrothendieckAbelian.enoughInjectives
  have : PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{u} R) g') := by
    apply Functor.sheafPullbackConstruction.preservesFiniteLimits
  have : IsIso (TopCat.Sheaf.pullback (ModuleCat.{u} R) g').rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.BaseChange.exactUnit_isIso _
  have := isIso_moduleSheafBaseChange_of_properMap f f' g g' hcart hf R
  have : IsIso (Stacks.Cohomology.BaseChange.derived
      (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f)
      (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f')
      (TopCat.Sheaf.pullback (ModuleCat.{u} R) g)
      (TopCat.Sheaf.pullback (ModuleCat.{u} R) g')
      (Stacks.Cohomology.BaseChange.mate
        (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g)
        (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) g')
        (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f)
        (TopCat.Sheaf.pushforward (ModuleCat.{u} R) f')
        (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{u} R)) hcart.w)))
      (asIso (TopCat.Sheaf.pullback (ModuleCat.{u} R) g).rightDerivedFunctorPlusUnith)) :=
    Stacks.Cohomology.ProperBaseChange.isIso_baseChangeDerived _ _ _ _ _
      (fun _ _ => inferInstance) _
      (fun M hM => rightAcyclic_pushforward_pullback_of_injective_module f f' g g' hcart hf R M hM)
  infer_instance

end MMP

end

/-!
# Cauchy integral formulas, Osgood's lemma, Laurent expansions and limits

A *standard compact* of `ℂ` is a closed rectangle `[a, b] × [c, d]` (`a < b`, `c < d`), a closed
disc of positive radius, or a closed annulus `{r ≤ |ζ - ζ₀| ≤ R}` with `0 < r < R`. Its boundary
is oriented counterclockwise, except that the inner circle of an annulus is oriented clockwise.
For functions with values in a complex Banach space `E` we prove:

1. the Cauchy integral formula on a standard compact;
2. the iterated Cauchy integral formula on a product `K₁ × ⋯ × Kₙ` of standard compacts, for a
   function that is continuous and separately holomorphic near the product;
3. Osgood's lemma: a continuous, separately holomorphic function on an open subset of `ℂⁿ` is
   holomorphic, and near each point it is the sum of an absolutely convergent multi-index
   power series;
4. the Cauchy estimates on a closed polydisc;
5. the Laurent expansion of a holomorphic function on a product of discs and annuli centred at
   `0`, converging normally on compact subsets, together with all its subseries;
6. a locally uniform limit of holomorphic functions on an open subset of `ℂⁿ` is holomorphic.

## Main results

* `MMP.SeveralComplex.cauchy_osgood_laurent`: the six statements above, as a conjunction.

## Implementation notes

`ℂⁿ` is `Fin n → ℂ`, and "holomorphic" is `DifferentiableOn ℂ`. A function `f` on an open set
`W` is separately holomorphic when `w ↦ f (Function.update ζ j w)` is complex differentiable at
`ζ j` for every `ζ ∈ W` and every `j`. A standard compact is recorded together with its boundary
integral `B : (ℂ → E) → E`: for a rectangle with corners `z`, `w` this is the signed sum of the
four edge integrals, as in `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`; for a
disc it is `∮ ζ in C(c, R), g ζ`; for an annulus it is the outer circle integral minus the inner
one. The iterated integral `∫_{∂K₁} ⋯ ∫_{∂Kₙ}` is the right fold over `List.finRange n` of the
operators integrating the `j`-th variable over `∂Kⱼ`, the innermost being `j = n - 1`.
Taylor coefficients are pinned as the coefficients `a β` of a multi-index expansion
`∑ β, (∏ j, (z j - c j) ^ β j) • a β` of `f` near the centre. Convergence "absolutely and
uniformly on compact subsets" in the Laurent statement is stated in the stronger normal form of
the Weierstrass test: on each compact subset the terms are dominated by a summable family.
-/

section

open Complex Metric MeasureTheory Filter Topology Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace MMP.SeveralComplex.Internal.GagaIteratedCauchy

/-- Cauchy integral formula on a closed disc. -/
private theorem cauchy_disc (c : ℂ) (R : ℝ) (hR : 0 < R) (U : Set ℂ) (f : ℂ → E)
    (_hU : IsOpen U) (hK : closedBall c R ⊆ U) (hf : DifferentiableOn ℂ f U)
    (z : ℂ) (hz : z ∈ interior (closedBall c R)) :
    (2 * π * I : ℂ)⁻¹ • (∮ ζ in C(c, R), (ζ - z)⁻¹ • f ζ) = f z := by
  rw [interior_closedBall c hR.ne'] at hz
  refine DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul ?_ hz
  exact DifferentiableOn.diffContOnCl (by rw [closure_ball c hR.ne']; exact hf.mono hK)

/-- Cauchy integral formula on a closed annulus, the inner circle oriented clockwise. -/
private theorem cauchy_annulus (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r < R) (U : Set ℂ)
    (f : ℂ → E) (hU : IsOpen U) (hK : closedBall c R \ ball c r ⊆ U)
    (hf : DifferentiableOn ℂ f U) (z : ℂ) (hz : z ∈ interior (closedBall c R \ ball c r)) :
    (2 * π * I : ℂ)⁻¹ • ((∮ ζ in C(c, R), (ζ - z)⁻¹ • f ζ) - ∮ ζ in C(c, r), (ζ - z)⁻¹ • f ζ)
      = f z := by
  have hzR : z ∈ ball c R := by
    have := interior_mono (Set.sdiff_subset (s := closedBall c R) (t := ball c r)) hz
    rwa [interior_closedBall c (hr.trans hrR).ne'] at this
  have hzr : z ∉ closedBall c r := by
    have := interior_mono (Set.sdiff_eq_compl_inter ▸ Set.inter_subset_left
      (s := (ball c r)ᶜ) (t := closedBall c R)) hz
    rw [interior_compl, closure_ball c hr.ne'] at this
    exact this
  have hzK : z ∈ closedBall c R \ ball c r :=
    ⟨ball_subset_closedBall hzR, fun h => hzr (ball_subset_closedBall h)⟩
  have hzU : z ∈ U := hK hzK
  set g := dslope f z
  have hgc : ContinuousOn g U :=
    (continuousOn_dslope (hU.mem_nhds hzU)).2
      ⟨hf.continuousOn, hf.differentiableAt (hU.mem_nhds hzU)⟩
  have hgd : ∀ ζ ∈ U, ζ ≠ z → DifferentiableAt ℂ g ζ := fun ζ hζ hne =>
    (differentiableAt_dslope_of_ne hne).2 (hf.differentiableAt (hU.mem_nhds hζ))
  -- the kernel splits off `g` away from `z`
  have hsplit : ∀ ρ : ℝ, 0 < ρ → z ∉ sphere c ρ → sphere c ρ ⊆ U →
      (∮ ζ in C(c, ρ), (ζ - z)⁻¹ • f ζ) = (∮ ζ in C(c, ρ), g ζ) +
        (∮ ζ in C(c, ρ), (ζ - z)⁻¹) • f z := by
    intro ρ hρ hzρ hρU
    have hne : ∀ ζ ∈ sphere c ρ, ζ - z ≠ 0 := fun ζ hζ h =>
      hzρ (sub_eq_zero.1 h ▸ hζ)
    rw [← circleIntegral.integral_smul_const, ← circleIntegral.integral_add]
    · refine circleIntegral.integral_congr hρ.le fun ζ hζ => ?_
      have hζz : ζ ≠ z := sub_ne_zero.1 (hne ζ hζ)
      simp only [g, dslope_of_ne _ hζz, slope_def_module, smul_sub]
      abel
    · exact (hgc.mono hρU).circleIntegrable hρ.le
    · refine ContinuousOn.circleIntegrable hρ.le ?_
      exact ((continuousOn_id.sub continuousOn_const).inv₀ hne).smul continuousOn_const
  have hzRs : z ∉ sphere c R := fun h => (ne_of_lt (mem_ball.1 hzR)) (mem_sphere.1 h)
  have hzrs : z ∉ sphere c r := fun h => hzr (sphere_subset_closedBall h)
  have hRU : sphere c R ⊆ U := fun ζ hζ => hK ⟨sphere_subset_closedBall hζ, by
    simp only [mem_ball, not_lt, (mem_sphere.1 hζ)]; exact hrR.le⟩
  have hrU : sphere c r ⊆ U := fun ζ hζ => hK ⟨closedBall_subset_closedBall hrR.le
    (sphere_subset_closedBall hζ), by simp [mem_ball, (mem_sphere.1 hζ)]⟩
  rw [hsplit R (hr.trans hrR) hzRs hRU, hsplit r hr hzrs hrU,
    circleIntegral.integral_sub_inv_of_mem_ball hzR]
  have hgeq : (∮ ζ in C(c, R), g ζ) = ∮ ζ in C(c, r), g ζ := by
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hrR.le
      (Set.countable_singleton z) (hgc.mono hK) fun ζ hζ => ?_
    refine hgd ζ (hK ⟨ball_subset_closedBall hζ.1.1, fun h => hζ.1.2
      (ball_subset_closedBall h)⟩) hζ.2
  have hzero : (∮ ζ in C(c, r), (ζ - z)⁻¹) = 0 := by
    refine DiffContOnCl.circleIntegral_eq_zero hr.le ?_
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hr.ne']
    intro ζ hζ
    refine ((differentiableAt_id.sub_const z).inv ?_).differentiableWithinAt
    rintro h
    exact hzr (sub_eq_zero.1 h ▸ hζ)
  rw [hgeq, hzero, zero_smul, add_zero, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_smul]

/-- Fundamental theorem of calculus for the logarithm along a segment in the slit plane. -/
private theorem integral_inv_mul_eq_log_sub (a b : ℝ) (p q A B : ℂ)
    (hs : ∀ x ∈ Set.uIcc a b, p + x * q ∈ slitPlane) (hA : p + a * q = A) (hB : p + b * q = B) :
    ∫ x : ℝ in a..b, (p + x * q)⁻¹ * q = log B - log A := by
  rw [← hA, ← hB]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => log (p + x * q))
    (fun x hx => ?_) ?_
  · have h1 : HasDerivAt (fun x : ℝ => p + x * q) q x := by
      simpa using (((hasDerivAt_id x).ofReal_comp).mul_const q).const_add p
    have := h1.clog_real (hs x hx)
    rwa [div_eq_mul_inv, mul_comm] at this
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx h => ?_
    have := hs x hx
    rw [h] at this
    exact slitPlane_ne_zero this rfl

/-- Splitting the Cauchy kernel along a path avoiding the point. -/
private theorem integral_kernel_split (a b : ℝ) (φ : ℝ → ℂ) (hφ : Continuous φ) (z : ℂ)
    (U : Set ℂ) (f : ℂ → E) (hgc : ContinuousOn (dslope f z) U)
    (hU : ∀ x ∈ Set.uIcc a b, φ x ∈ U) (hz : ∀ x ∈ Set.uIcc a b, φ x ≠ z) :
    ∫ x : ℝ in a..b, (φ x - z)⁻¹ • f (φ x) =
      (∫ x : ℝ in a..b, dslope f z (φ x)) + (∫ x : ℝ in a..b, (φ x - z)⁻¹) • f z := by
  rw [← intervalIntegral.integral_smul_const, ← intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr fun x hx => ?_
    simp only [dslope_of_ne _ (hz x hx), slope_def_module, smul_sub]
    abel
  · exact (hgc.comp hφ.continuousOn fun x hx => hU x hx).intervalIntegrable
  · refine ContinuousOn.intervalIntegrable ?_
    exact (ContinuousOn.inv₀ (by fun_prop) fun x hx h => hz x hx (sub_eq_zero.1 h)).smul
      continuousOn_const

private theorem log_sub_log_neg_of_im_pos {x : ℂ} (hx : 0 < x.im) : log x - log (-x) = π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_sub_pi_of_im_pos hx]

private theorem log_neg_sub_log_of_im_neg {x : ℂ} (hx : x.im < 0) :
    log (-x) - log x = π * I := by
  apply Complex.ext <;> simp [log_re, log_im, arg_neg_eq_arg_add_pi_of_im_neg hx]

/-- The boundary integral of the Cauchy kernel around a rectangle containing the point. -/
private theorem rect_kernel (p q z : ℂ) (h1 : p.re < z.re) (h2 : z.re < q.re) (h3 : p.im < z.im)
    (h4 : z.im < q.im) :
    (∫ x : ℝ in p.re..q.re, ((x + p.im * I : ℂ) - z)⁻¹) -
      (∫ x : ℝ in p.re..q.re, ((x + q.im * I : ℂ) - z)⁻¹) +
      I • (∫ y : ℝ in p.im..q.im, ((q.re + y * I : ℂ) - z)⁻¹) -
      I • (∫ y : ℝ in p.im..q.im, ((p.re + y * I : ℂ) - z)⁻¹) = 2 * π * I := by
  set A : ℂ := (p.re + p.im * I : ℂ) - z
  set B : ℂ := (q.re + p.im * I : ℂ) - z
  set C : ℂ := (q.re + q.im * I : ℂ) - z
  set D : ℂ := (p.re + q.im * I : ℂ) - z
  have e1 : (∫ x : ℝ in p.re..q.re, ((x + p.im * I : ℂ) - z)⁻¹) = log B - log A := by
    rw [← integral_inv_mul_eq_log_sub p.re q.re (p.im * I - z) 1 A B _ (by simp only [A]; ring)
      (by simp only [B]; ring)]
    · refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [mul_one]; ring_nf
    · intro x _
      exact mem_slitPlane_iff.2 (Or.inr (by simp; linarith))
  have e2 : (∫ x : ℝ in p.re..q.re, ((x + q.im * I : ℂ) - z)⁻¹) = log C - log D := by
    rw [← integral_inv_mul_eq_log_sub p.re q.re (q.im * I - z) 1 D C _ (by simp only [D]; ring)
      (by simp only [C]; ring)]
    · refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [mul_one]; ring_nf
    · intro x _
      exact mem_slitPlane_iff.2 (Or.inr (by simp; linarith))
  have e3 : I • (∫ y : ℝ in p.im..q.im, ((q.re + y * I : ℂ) - z)⁻¹) = log C - log B := by
    rw [← intervalIntegral.integral_smul,
      ← integral_inv_mul_eq_log_sub p.im q.im (q.re - z) I B C _ (by simp only [B]; ring)
      (by simp only [C]; ring)]
    · refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [smul_eq_mul]; ring_nf
    · intro x _
      exact mem_slitPlane_iff.2 (Or.inl (by simp; linarith))
  have e4 : I • (∫ y : ℝ in p.im..q.im, ((p.re + y * I : ℂ) - z)⁻¹) = log (-D) - log (-A) := by
    rw [← intervalIntegral.integral_smul,
      ← integral_inv_mul_eq_log_sub p.im q.im (z - p.re) (-I) (-A) (-D) _ (by simp only [A]; ring)
      (by simp only [D]; ring)]
    · refine intervalIntegral.integral_congr fun x _ => ?_
      have : (z - p.re + x * -I : ℂ) = -((p.re + x * I : ℂ) - z) := by ring
      simp only [smul_eq_mul, this, inv_neg]; ring
    · intro x _
      exact mem_slitPlane_iff.2 (Or.inl (by simp; linarith))
  rw [e1, e2, e3, e4]
  have hD : 0 < D.im := by simp [D]; linarith
  have hA : A.im < 0 := by simp [A]; linarith
  linear_combination log_sub_log_neg_of_im_pos hD + log_neg_sub_log_of_im_neg hA

/-- Cauchy integral formula on a closed rectangle. -/
private theorem cauchy_rect (p q : ℂ) (hre : p.re < q.re) (him : p.im < q.im) (U : Set ℂ)
    (f : ℂ → E) (hU : IsOpen U) (hK : Set.Icc p.re q.re ×ℂ Set.Icc p.im q.im ⊆ U)
    (hf : DifferentiableOn ℂ f U) (z : ℂ)
    (hz : z ∈ interior (Set.Icc p.re q.re ×ℂ Set.Icc p.im q.im)) :
    (2 * π * I : ℂ)⁻¹ • ((∫ x : ℝ in p.re..q.re, ((x + p.im * I : ℂ) - z)⁻¹ • f (x + p.im * I)) -
      (∫ x : ℝ in p.re..q.re, ((x + q.im * I : ℂ) - z)⁻¹ • f (x + q.im * I)) +
      I • (∫ y : ℝ in p.im..q.im, ((q.re + y * I : ℂ) - z)⁻¹ • f (q.re + y * I)) -
      I • ∫ y : ℝ in p.im..q.im, ((p.re + y * I : ℂ) - z)⁻¹ • f (p.re + y * I)) = f z := by
  rw [interior_reProdIm, interior_Icc, interior_Icc] at hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  have hzU : z ∈ U := hK ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩
  have hgc : ContinuousOn (dslope f z) U :=
    (continuousOn_dslope (hU.mem_nhds hzU)).2
      ⟨hf.continuousOn, hf.differentiableAt (hU.mem_nhds hzU)⟩
  have hreI : Set.uIcc p.re q.re = Set.Icc p.re q.re := Set.uIcc_of_le hre.le
  have himI : Set.uIcc p.im q.im = Set.Icc p.im q.im := Set.uIcc_of_le him.le
  rw [integral_kernel_split _ _ (fun x : ℝ => (x + p.im * I : ℂ)) (by fun_prop) z U f hgc
      (fun x hx => hK (by rw [hreI] at hx; simp [mem_reProdIm, hx.1, hx.2, him.le]))
      (fun x _ h => by have := congrArg im h; simp at this; linarith),
    integral_kernel_split _ _ (fun x : ℝ => (x + q.im * I : ℂ)) (by fun_prop) z U f hgc
      (fun x hx => hK (by rw [hreI] at hx; simp [mem_reProdIm, hx.1, hx.2, him.le]))
      (fun x _ h => by have := congrArg im h; simp at this; linarith),
    integral_kernel_split _ _ (fun y : ℝ => (q.re + y * I : ℂ)) (by fun_prop) z U f hgc
      (fun y hy => hK (by rw [himI] at hy; simp [mem_reProdIm, hy.1, hy.2, hre.le]))
      (fun y _ h => by have := congrArg re h; simp at this; linarith),
    integral_kernel_split _ _ (fun y : ℝ => (p.re + y * I : ℂ)) (by fun_prop) z U f hgc
      (fun y hy => hK (by rw [himI] at hy; simp [mem_reProdIm, hy.1, hy.2, hre.le]))
      (fun y _ h => by have := congrArg re h; simp at this; linarith)]
  have hg0 := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (dslope f z) p q {z} (Set.countable_singleton z)
    (by rw [hreI, himI]; exact hgc.mono hK) (fun ζ hζ => by
      rw [min_eq_left hre.le, max_eq_right hre.le, min_eq_left him.le,
        max_eq_right him.le] at hζ
      have hζU : ζ ∈ U := hK ⟨⟨hζ.1.1.1.le, hζ.1.1.2.le⟩, hζ.1.2.1.le, hζ.1.2.2.le⟩
      exact (differentiableAt_dslope_of_ne hζ.2).2 (hf.differentiableAt (hU.mem_nhds hζU)))
  have hk := rect_kernel p q z h1 h2 h3 h4
  set G1 := ∫ x : ℝ in p.re..q.re, dslope f z (x + p.im * I)
  set G2 := ∫ x : ℝ in p.re..q.re, dslope f z (x + q.im * I)
  set G3 := ∫ y : ℝ in p.im..q.im, dslope f z (q.re + y * I)
  set G4 := ∫ y : ℝ in p.im..q.im, dslope f z (p.re + y * I)
  set K1 := ∫ x : ℝ in p.re..q.re, ((x + p.im * I : ℂ) - z)⁻¹
  set K2 := ∫ x : ℝ in p.re..q.re, ((x + q.im * I : ℂ) - z)⁻¹
  set K3 := ∫ y : ℝ in p.im..q.im, ((q.re + y * I : ℂ) - z)⁻¹
  set K4 := ∫ y : ℝ in p.im..q.im, ((p.re + y * I : ℂ) - z)⁻¹
  have : (G1 + K1 • f z) - (G2 + K2 • f z) + I • (G3 + K3 • f z) - I • (G4 + K4 • f z) =
      (G1 - G2 + I • G3 - I • G4) + (K1 - K2 + I • K3 - I • K4) • f z := by
    simp only [smul_add, add_smul, sub_smul, smul_smul, smul_eq_mul]
    abel
  rw [this, hg0, hk, zero_add, smul_smul,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_smul]

/-- Inserting a coordinate is complex differentiable. -/
private theorem differentiable_update {n : ℕ} (ζ : Fin n → ℂ) (j : Fin n) :
    Differentiable ℂ (fun w : ℂ => Function.update ζ j w) := by
  intro w
  rw [differentiableAt_pi]
  intro i
  by_cases h : i = j
  · subst h; simp only [Function.update_self]; exact differentiableAt_id
  · simp only [Function.update_of_ne h]; exact differentiableAt_const _

/-- A standard compact `K` of `ℂ` together with its boundary integral `B`. -/
private def StdBoundary (K : Set ℂ) (B : (ℂ → E) → E) : Prop :=
  (∃ z w : ℂ, z.re < w.re ∧ z.im < w.im ∧
      K = Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im ∧
      B = fun g => (∫ x : ℝ in z.re..w.re, g (x + z.im * I)) -
        (∫ x : ℝ in z.re..w.re, g (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, g (w.re + y * I)) -
        I • ∫ y : ℝ in z.im..w.im, g (z.re + y * I)) ∨
    (∃ (c : ℂ) (R : ℝ), 0 < R ∧ K = closedBall c R ∧ B = fun g => ∮ ζ in C(c, R), g ζ) ∨
    (∃ (c : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧ K = closedBall c R \ ball c r ∧
      B = fun g => (∮ ζ in C(c, R), g ζ) - ∮ ζ in C(c, r), g ζ)

omit [CompleteSpace E] in
/-- A boundary integral commutes with constant scalars. -/
private theorem StdBoundary.map_smul {K : Set ℂ} {B : (ℂ → E) → E} (h : StdBoundary K B)
    (c : ℂ) (g : ℂ → E) : B (fun w => c • g w) = c • B g := by
  rcases h with ⟨p, q, -, -, -, rfl⟩ | ⟨a, R, -, -, rfl⟩ | ⟨a, r, R, -, -, -, rfl⟩
  · simp only [intervalIntegral.integral_smul]
    module
  · exact circleIntegral.integral_smul c g a R
  · simp only [circleIntegral.integral_smul, smul_sub]

omit [CompleteSpace E] in
/-- A boundary integral only depends on the values on the compact. -/
private theorem StdBoundary.congr {K : Set ℂ} {B : (ℂ → E) → E} (h : StdBoundary K B)
    {g g' : ℂ → E} (hg : Set.EqOn g g' K) : B g = B g' := by
  rcases h with ⟨p, q, hre, him, rfl, rfl⟩ | ⟨a, R, hR, rfl, rfl⟩ |
    ⟨a, r, R, hr, hrR, rfl, rfl⟩
  · have hreI : Set.uIcc p.re q.re = Set.Icc p.re q.re := Set.uIcc_of_le hre.le
    have himI : Set.uIcc p.im q.im = Set.Icc p.im q.im := Set.uIcc_of_le him.le
    dsimp only
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => g' (x + p.im * I)) (fun x hx => hg
        (by rw [hreI] at hx; simp [mem_reProdIm, hx.1, hx.2, him.le])),
      intervalIntegral.integral_congr (g := fun x : ℝ => g' (x + q.im * I)) (fun x hx => hg
        (by rw [hreI] at hx; simp [mem_reProdIm, hx.1, hx.2, him.le])),
      intervalIntegral.integral_congr (g := fun y : ℝ => g' (q.re + y * I)) (fun y hy => hg
        (by rw [himI] at hy; simp [mem_reProdIm, hy.1, hy.2, hre.le])),
      intervalIntegral.integral_congr (g := fun y : ℝ => g' (p.re + y * I)) (fun y hy => hg
        (by rw [himI] at hy; simp [mem_reProdIm, hy.1, hy.2, hre.le]))]
  · exact circleIntegral.integral_congr hR.le (hg.mono sphere_subset_closedBall)
  · dsimp only
    rw [circleIntegral.integral_congr (hr.trans hrR).le (hg.mono
        (show sphere a R ⊆ closedBall a R \ ball a r from fun ζ hζ =>
        ⟨sphere_subset_closedBall hζ, by simp [mem_ball, (mem_sphere.1 hζ), hrR.le]⟩)),
      circleIntegral.integral_congr hr.le (hg.mono
        (show sphere a r ⊆ closedBall a R \ ball a r from fun ζ hζ =>
        ⟨closedBall_subset_closedBall hrR.le (sphere_subset_closedBall hζ),
          by simp [mem_ball, (mem_sphere.1 hζ)]⟩))]

omit [CompleteSpace E] in
/-- Integrating out coordinates other than `j` commutes with a scalar depending on `ζ j`. -/
private theorem foldr_smul_coord {n : ℕ} (B : Fin n → (ℂ → E) → E)
    (hB : ∀ i (c : ℂ) (g : ℂ → E), B i (fun w => c • g w) = c • B i g) (j : Fin n)
    (c : ℂ → ℂ) (F : (Fin n → ℂ) → E) :
    ∀ l : List (Fin n), j ∉ l → ∀ η : Fin n → ℂ,
      l.foldr (fun j F ζ => B j fun w => F (Function.update ζ j w)) (fun ζ' => c (ζ' j) • F ζ') η
        = c (η j) • l.foldr (fun j F ζ => B j fun w => F (Function.update ζ j w)) F η := by
  intro l
  induction l with
  | nil => intro _ η; rfl
  | cons i l ih =>
    intro hj η
    simp only [List.mem_cons, not_or] at hj
    simp only [List.foldr_cons]
    have : (fun w => l.foldr (fun j F ζ => B j fun w => F (Function.update ζ j w))
        (fun ζ' => c (ζ' j) • F ζ') (Function.update η i w)) = fun w => c (η j) •
          l.foldr (fun j F ζ => B j fun w => F (Function.update ζ j w)) F
            (Function.update η i w) := by
      funext w
      rw [ih hj.2, Function.update_of_ne hj.1]
    rw [this, hB]

/-- Part (1): the Cauchy integral formula on a standard compact. -/
private theorem cauchy_standard_compact :
    (∀ (K : Set ℂ) (B : (ℂ → E) → E),
      ((∃ z w : ℂ, z.re < w.re ∧ z.im < w.im ∧
          K = Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im ∧
          B = fun g => (∫ x : ℝ in z.re..w.re, g (x + z.im * I)) -
            (∫ x : ℝ in z.re..w.re, g (x + w.im * I)) +
            I • (∫ y : ℝ in z.im..w.im, g (w.re + y * I)) -
            I • ∫ y : ℝ in z.im..w.im, g (z.re + y * I)) ∨
        (∃ (c : ℂ) (R : ℝ), 0 < R ∧ K = closedBall c R ∧ B = fun g => ∮ ζ in C(c, R), g ζ) ∨
        (∃ (c : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧ K = closedBall c R \ ball c r ∧
          B = fun g => (∮ ζ in C(c, R), g ζ) - ∮ ζ in C(c, r), g ζ)) →
      ∀ (U : Set ℂ) (f : ℂ → E), IsOpen U → K ⊆ U → DifferentiableOn ℂ f U →
      ∀ z ∈ interior K, (2 * π * I : ℂ)⁻¹ • B (fun ζ => (ζ - z)⁻¹ • f ζ) = f z) := by
  intro K B hKB U f hU hKU hf z hz
  rcases hKB with ⟨p, q, hre, him, rfl, rfl⟩ | ⟨c, R, hR, rfl, rfl⟩ | ⟨c, r, R, hr, hrR, rfl, rfl⟩
  · exact cauchy_rect p q hre him U f hU hKU hf z hz
  · exact cauchy_disc c R hR U f hU hKU hf z hz
  · exact cauchy_annulus c r R hr hrR U f hU hKU hf z hz

/-- The iterated Cauchy integral over the coordinates in a list `l`, for a separately
holomorphic function. -/
private theorem foldr_kernel {n : ℕ} (K : Fin n → Set ℂ) (B : Fin n → (ℂ → E) → E)
    (hB : ∀ j, StdBoundary (K j) (B j)) (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E)
    (hW : IsOpen W) (hKW : Set.univ.pi K ⊆ W)
    (hf : ∀ ζ ∈ W, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j)) :
    ∀ l : List (Fin n), l.Nodup → ∀ ζ ∈ Set.univ.pi K, (∀ i ∈ l, ζ i ∈ interior (K i)) →
      l.foldr (fun j F ζ => B j fun w => F (Function.update ζ j w))
        (fun ζ' => (∏ i ∈ l.toFinset, (ζ' i - ζ i)⁻¹) • f ζ') ζ =
        (2 * π * I : ℂ) ^ l.length • f ζ := by
  intro l
  induction l with
  | nil => intro _ ζ _ _; simp
  | cons j l ih =>
    intro hnd ζ hζ hint
    rw [List.nodup_cons] at hnd
    have hjl : j ∉ l.toFinset := by simpa using hnd.1
    simp only [List.foldr_cons]
    have hker : (fun ζ' : Fin n → ℂ => (∏ i ∈ (j :: l).toFinset, (ζ' i - ζ i)⁻¹) • f ζ') =
        fun ζ' => (ζ' j - ζ j)⁻¹ • ((∏ i ∈ l.toFinset, (ζ' i - ζ i)⁻¹) • f ζ') := by
      funext ζ'
      rw [List.toFinset_cons, Finset.prod_insert hjl, mul_smul]
    rw [hker]
    have hinner : Set.EqOn (fun w => l.foldr (fun j F ζ => B j fun w => F (Function.update ζ j w))
        (fun ζ' => (ζ' j - ζ j)⁻¹ • ((∏ i ∈ l.toFinset, (ζ' i - ζ i)⁻¹) • f ζ'))
          (Function.update ζ j w))
        (fun w => (2 * π * I : ℂ) ^ l.length • ((w - ζ j)⁻¹ • f (Function.update ζ j w)))
        (K j) := by
      intro w hw
      dsimp only
      rw [foldr_smul_coord B (fun i => (hB i).map_smul) j (fun t => (t - ζ j)⁻¹) _ l hnd.1,
        Function.update_self]
      have hcen : (fun ζ' : Fin n → ℂ => (∏ i ∈ l.toFinset, (ζ' i - ζ i)⁻¹) • f ζ') =
          fun ζ' => (∏ i ∈ l.toFinset, (ζ' i - Function.update ζ j w i)⁻¹) • f ζ' := by
        funext ζ'
        congr 1
        refine Finset.prod_congr rfl fun i hi => ?_
        have : i ≠ j := fun h => hjl (h ▸ hi)
        rw [Function.update_of_ne this]
      have hmem : Function.update ζ j w ∈ Set.univ.pi K := by
        intro i _
        by_cases h : i = j
        · subst h; simpa using hw
        · simpa [Function.update_of_ne h] using hζ i (Set.mem_univ i)
      rw [hcen, ih hnd.2 _ hmem fun i hi => by
        have : i ≠ j := fun h => hnd.1 (h ▸ hi)
        simpa [Function.update_of_ne this] using hint i (List.mem_cons_of_mem _ hi), smul_comm]
    rw [(hB j).congr hinner, (hB j).map_smul]
    set φ : ℂ → Fin n → ℂ := fun w => Function.update ζ j w
    have hφ : Continuous φ := (differentiable_update ζ j).continuous
    have h1 := cauchy_standard_compact (K j) (B j) (hB j) (φ ⁻¹' W) (fun w => f (φ w))
      (hW.preimage hφ) (fun w hw => hKW (by
        intro i _
        by_cases h : i = j
        · subst h; simpa [φ] using hw
        · simpa [φ, Function.update_of_ne h] using hζ i (Set.mem_univ i)))
      (fun w hw => by
        have := hf (φ w) hw j
        simp only [φ, Function.update_idem, Function.update_self] at this
        exact this.differentiableWithinAt)
      (ζ j) (hint j List.mem_cons_self)
    simp only [φ, Function.update_eq_self] at h1
    rw [← h1, List.length_cons, pow_succ, mul_smul,
      smul_inv_smul₀ (by simp [Real.pi_ne_zero, I_ne_zero] : (2 * π * I : ℂ) ≠ 0)]

/-- Part (2): the iterated Cauchy integral formula on a product of standard compacts. -/
private theorem cauchy_iterated :
    (∀ (n : ℕ) (K : Fin n → Set ℂ) (B : Fin n → (ℂ → E) → E),
      (∀ j, (∃ z w : ℂ, z.re < w.re ∧ z.im < w.im ∧
          K j = Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im ∧
          B j = fun g => (∫ x : ℝ in z.re..w.re, g (x + z.im * I)) -
            (∫ x : ℝ in z.re..w.re, g (x + w.im * I)) +
            I • (∫ y : ℝ in z.im..w.im, g (w.re + y * I)) -
            I • ∫ y : ℝ in z.im..w.im, g (z.re + y * I)) ∨
        (∃ (c : ℂ) (R : ℝ), 0 < R ∧ K j = closedBall c R ∧
          B j = fun g => ∮ ζ in C(c, R), g ζ) ∨
        (∃ (c : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧ K j = closedBall c R \ ball c r ∧
          B j = fun g => (∮ ζ in C(c, R), g ζ) - ∮ ζ in C(c, r), g ζ)) →
      ∀ (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E), IsOpen W → Set.univ.pi K ⊆ W →
      ContinuousOn f W →
      (∀ ζ ∈ W, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j)) →
      ∀ z ∈ interior (Set.univ.pi K),
        f z = ((2 * π * I : ℂ) ^ n)⁻¹ •
          (List.finRange n).foldr (fun j F ζ => B j fun w => F (Function.update ζ j w))
            (fun ζ => (∏ j, (ζ j - z j)⁻¹) • f ζ) z) := by
  intro n K B hB W f hW hKW _ hf z hz
  have hint : z ∈ Set.univ.pi fun j => interior (K j) := by
    rwa [interior_pi_set Set.finite_univ] at hz
  have hzK : z ∈ Set.univ.pi K := interior_subset hz
  have := foldr_kernel K B hB W f hW hKW hf (List.finRange n) (List.nodup_finRange n) z hzK
    (fun i _ => hint i (Set.mem_univ i))
  rw [List.toFinset_finRange, List.length_finRange] at this
  rw [this, inv_smul_smul₀ (pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero]))]

/-! ### Torus integrals and multi-index series -/

private theorem hasSum_pi_prod {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜] {κ : Type*} (n : ℕ) :
    ∀ (g : Fin n → κ → 𝕜) (s : Fin n → 𝕜), (∀ j, HasSum (g j) (s j)) →
      (∀ j, Summable fun k => ‖g j k‖) →
      HasSum (fun β : Fin n → κ => ∏ j, g j (β j)) (∏ j, s j) ∧
        Summable (fun β : Fin n → κ => ‖∏ j, g j (β j)‖) := by
  induction n with
  | zero =>
    intro g s _ _
    simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
    exact ⟨hasSum_unique (fun _ : Fin 0 → κ => (1:𝕜)),
      (hasSum_unique (fun _ : Fin 0 → κ => (1:ℝ))).summable⟩
  | succ n ih =>
    intro g s hg hgn
    obtain ⟨h1, h2⟩ := ih (fun j => g j.succ) (fun j => s j.succ)
      (fun j => hg j.succ) (fun j => hgn j.succ)
    set F : (Fin n → κ) → 𝕜 := fun β => ∏ j, g j.succ (β j) with hF
    have hs : Summable fun x : κ × (Fin n → κ) => g 0 x.1 * F x.2 :=
      summable_mul_of_summable_norm (f := g 0) (g := F) (hgn 0) h2
    have hm : HasSum (fun x : κ × (Fin n → κ) => g 0 x.1 * F x.2) (s 0 * ∏ j : Fin n, s j.succ) :=
      HasSum.mul (f := g 0) (g := F) (hg 0) h1 hs
    have hmn : Summable fun x : κ × (Fin n → κ) => ‖g 0 x.1 * F x.2‖ :=
      Summable.mul_norm (f := g 0) (g := F) (hgn 0) h2
    rw [Fin.prod_univ_succ]
    rw [← (Fin.consEquiv fun _ => κ).hasSum_iff, ← (Fin.consEquiv fun _ => κ).summable_iff]
    refine ⟨?_, ?_⟩
    · convert hm using 1
      funext p
      simp [F, Fin.prod_univ_succ]
    · convert hmn using 1
      funext p
      simp [F, Fin.prod_univ_succ]

private theorem norm_torus_jac {n : ℕ} (R : Fin n → ℝ) (θ : Fin n → ℝ) :
    ‖(∏ i, (R i : ℂ) * exp (θ i * I) * I)‖ = ∏ i, |R i| := by
  rw [norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, norm_I, Complex.norm_real, Real.norm_eq_abs]
  ring

omit [CompleteSpace E] in
private theorem torusIntegral_eq_zero_of_radius {n : ℕ} (f : (Fin n → ℂ) → E) (c : Fin n → ℂ)
    (R : Fin n → ℝ) (h : ∃ i, R i = 0) : (∯ ζ in T(c, R), f ζ) = 0 := by
  obtain ⟨i, hi⟩ := h
  simp only [torusIntegral]
  refine (integral_congr_ae (Eventually.of_forall fun θ => ?_)).trans (integral_zero _ _)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), zero_smul]

omit [NormedSpace ℂ E] [CompleteSpace E] in
private theorem torusIntegrable_of_continuous {n : ℕ} {f : (Fin n → ℂ) → E} {c : Fin n → ℂ}
    {R : Fin n → ℝ} (hf : Continuous fun θ => f (torusMap c R θ)) : TorusIntegrable f c R :=
  hf.integrableOn_Icc

omit [CompleteSpace E] in
private theorem hasSum_torusIntegral {ι : Type*} [Countable ι] {n : ℕ} {c : Fin n → ℂ}
    {R : Fin n → ℝ} (F : ι → (Fin n → ℂ) → E) (g : (Fin n → ℂ) → E) (u : ι → ℝ)
    (hF : ∀ i, Continuous fun θ => F i (torusMap c R θ)) (hu : Summable u)
    (hb : ∀ i θ, ‖F i (torusMap c R θ)‖ ≤ u i)
    (hs : ∀ θ, HasSum (fun i => F i (torusMap c R θ)) (g (torusMap c R θ))) :
    HasSum (fun i => ∯ ζ in T(c, R), F i ζ) (∯ ζ in T(c, R), g ζ) := by
  simp only [torusIntegral]
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * π)) :=
    isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
  refine hasSum_integral_of_dominated_convergence (fun i _ => (∏ j, |R j|) * u i)
    (fun i => ?_) (fun i => Eventually.of_forall fun θ => ?_)
    (Eventually.of_forall fun θ => hu.mul_left _) (integrable_const _)
    (Eventually.of_forall fun θ => (hs θ).const_smul _)
  · exact (Continuous.smul (by fun_prop) (hF i)).aestronglyMeasurable
  · rw [norm_smul, norm_torus_jac]
    exact mul_le_mul_of_nonneg_left (hb i θ) (Finset.prod_nonneg fun j _ => abs_nonneg _)

private theorem torusMap_sub_ne {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 < R j)
    (θ : Fin n → ℝ) (j : Fin n) : torusMap c R θ j - c j ≠ 0 := by
  simp [torusMap, (hR j).ne', Complex.exp_ne_zero]

private theorem torusIntegral_monomial (n : ℕ) : ∀ (c : Fin n → ℂ) (R : Fin n → ℝ), (∀ j, 0 < R j) →
    ∀ (m : Fin n → ℤ) (v : E),
    (∯ ζ in T(c, R), (∏ j, (ζ j - c j) ^ m j) • v) =
      if (∀ j, m j = -1) then (2 * π * I : ℂ) ^ n • v else 0 := by
  induction n with
  | zero => intro c R _ m v; simp
  | succ n ih =>
    intro c R hR m v
    rw [torusIntegral_succ]
    · simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_smul]
      have hin : ∀ x : ℂ, (∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
          (x - c 0) ^ m 0 • (∏ j : Fin n, (y j - c j.succ) ^ m j.succ) • v) =
          (x - c 0) ^ m 0 • (if (∀ j : Fin n, m j.succ = -1) then (2 * π * I : ℂ) ^ n • v
            else 0) := by
        intro x
        rw [torusIntegral_smul]
        congr 1
        exact ih (c ∘ Fin.succ) (R ∘ Fin.succ) (fun j => hR j.succ) (m ∘ Fin.succ) v
      simp only [hin, circleIntegral.integral_smul_const, Fin.forall_fin_succ]
      by_cases h0 : m 0 = -1
      · rw [h0]
        simp only [zpow_neg, zpow_one]
        rw [circleIntegral.integral_sub_center_inv _ (hR 0).ne']
        by_cases h1 : ∀ j : Fin n, m j.succ = -1
        · simp only [h1, implies_true, and_self, ite_true, smul_smul, pow_succ, mul_comm]
        · simp [h1]
      · rw [circleIntegral.integral_sub_zpow_of_ne h0]
        simp [h0]
    · refine torusIntegrable_of_continuous ?_
      refine Continuous.smul ?_ continuous_const
      refine continuous_finsetProd _ fun j _ => ?_
      refine Continuous.zpow₀ (by simp only [torusMap]; fun_prop) _ fun θ => Or.inl ?_
      exact torusMap_sub_ne c R hR θ j

omit [CompleteSpace E] in
private theorem circleIntegral_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℂ → E) (c : ℂ) (R : ℝ)
    (hg : ∀ i ∈ s, CircleIntegrable (g i) c R) :
    (∮ x in C(c, R), ∑ i ∈ s, g i x) = ∑ i ∈ s, ∮ x in C(c, R), g i x := by
  simp only [circleIntegral, Finset.smul_sum]
  exact intervalIntegral.integral_finsetSum fun i hi => (hg i hi).out

private theorem continuous_circle_inv (c z : ℂ) (R : ℝ) (hR : 0 ≤ R) (h : R = 0 ∨ ‖z - c‖ ≠ R) :
    Continuous fun θ : ℝ => (circleMap c R θ - z)⁻¹ := by
  rcases h with h | h
  · subst h; simp only [circleMap_zero_radius, Function.const_apply]; exact continuous_const
  · refine Continuous.inv₀ (by fun_prop) fun θ heq => h ?_
    have : z - c = R * exp (θ * I) := by
      simp only [circleMap] at heq; linear_combination -heq
    rw [this, norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hR, mul_one]

private theorem circleMap_mem_shell (c : ℂ) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (e : Bool)
    (θ : ℝ) :
    circleMap c (if e then b else a) θ ∈ closedBall c b \ ball c a := by
  have hn : ‖circleMap c (if e then b else a) θ - c‖ = if e then b else a := by
    rw [circleMap_sub_center, norm_circleMap_zero]
    cases e <;> simp [abs_of_nonneg ha, abs_of_nonneg (ha.trans hab.le)]
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, hn]; cases e <;> simp [hab.le]
  · rw [mem_ball, dist_eq_norm, hn, not_lt]; cases e <;> simp [hab.le]

private theorem shell_radius_cond (c z : ℂ) (a b : ℝ)
    (hz : (a = 0 ∨ a < ‖z - c‖) ∧ ‖z - c‖ < b) (e : Bool) :
    (if e then b else a) = 0 ∨ ‖z - c‖ ≠ (if e then b else a) := by
  cases e
  · rcases hz.1 with h | h
    · exact Or.inl (by simp [h])
    · exact Or.inr (by simpa only [Bool.false_eq_true, ite_false] using h.ne')
  · exact Or.inr (by simpa only [ite_true] using hz.2.ne)

/-- One-variable Cauchy formula on a shell (a disc if `a = 0`). -/
private theorem cauchy_shell1 (c z : ℂ) (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) (U : Set ℂ) (g : ℂ → E)
    (hU : IsOpen U) (hK : closedBall c b \ ball c a ⊆ U) (hg : DifferentiableOn ℂ g U)
    (hz : (a = 0 ∨ a < ‖z - c‖) ∧ ‖z - c‖ < b) :
    ∑ e : Bool, (if e then (1:ℂ) else -1) • ∮ x in C(c, if e then b else a), (x - z)⁻¹ • g x =
      (2 * π * I : ℂ) • g z := by
  have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, one_smul, neg_smul,
    ← sub_eq_add_neg]
  obtain ⟨hz1, hzb⟩ := hz
  by_cases ha0 : a = 0
  · subst ha0
    rw [circleIntegral.integral_radius_zero, sub_zero]
    have hb : 0 < b := hab
    have := cauchy_disc c b hb U g hU (by simpa using hK) hg z
      (by rw [interior_closedBall c hb.ne']; simpa [mem_ball, dist_eq_norm] using hzb)
    rw [← this, smul_inv_smul₀ h2]
  · have h : a < ‖z - c‖ := hz1.resolve_left ha0
    have hzi : z ∈ interior (closedBall c b \ ball c a) := by
      refine interior_maximal (t := {w | a < ‖w - c‖ ∧ ‖w - c‖ < b}) ?_ ?_
        (show z ∈ {w | a < ‖w - c‖ ∧ ‖w - c‖ < b} from ⟨h, hzb⟩)
      · intro w hw
        exact ⟨by simpa [mem_closedBall, dist_eq_norm] using hw.2.le,
          by simpa [mem_ball, dist_eq_norm] using hw.1.le⟩
      · exact (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
          (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
    have := cauchy_annulus c a b (lt_of_le_of_ne ha (Ne.symm ha0)) hab U g hU hK hg z hzi
    rw [← this, smul_inv_smul₀ h2]

private theorem mem_shell_of (c z : ℂ) (a b : ℝ)
    (hz : (a = 0 ∨ a < ‖z - c‖) ∧ ‖z - c‖ < b) : z ∈ closedBall c b \ ball c a := by
  refine ⟨by rw [mem_closedBall, dist_eq_norm]; exact hz.2.le, ?_⟩
  rw [mem_ball, dist_eq_norm, not_lt]
  rcases hz.1 with h | h
  · rw [h]; exact norm_nonneg _
  · exact h.le

private theorem sphere_subset_shell (c : ℂ) (a b : ℝ) (hab : a < b) (e : Bool) :
    sphere c (if e then b else a) ⊆ closedBall c b \ ball c a := by
  intro x hx
  rw [mem_sphere] at hx
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall, hx]; cases e <;> simp [hab.le]
  · rw [mem_ball, hx, not_lt]; cases e <;> simp [hab.le]

private theorem torusMap_mem_of_shell {n : ℕ} (c : Fin n → ℂ) (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j < b j) (ε : Fin n → Bool) (θ : Fin n → ℝ) (j : Fin n) :
    torusMap c (fun j => if ε j then b j else a j) θ j ∈
      closedBall (c j) (b j) \ ball (c j) (a j) :=
  circleMap_mem_shell (c j) (a j) (b j) (ha j) (hab j) (ε j) (θ j)

private theorem continuous_torusMap' {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) :
    Continuous (torusMap c R) :=
  continuous_pi fun i => by simp only [torusMap]; fun_prop

private theorem continuous_kernel_torus {n : ℕ} (c z : Fin n → ℂ) (a b : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j < b j)
    (hz : ∀ j, (a j = 0 ∨ a j < ‖z j - c j‖) ∧ ‖z j - c j‖ < b j) (ε : Fin n → Bool) :
    Continuous fun θ : Fin n → ℝ =>
      ∏ j, (torusMap c (fun j => if ε j then b j else a j) θ j - z j)⁻¹ := by
  refine continuous_finsetProd _ fun j _ => ?_
  have := continuous_circle_inv (c j) (z j) (if ε j then b j else a j)
    (by cases ε j <;> simp [ha j, (ha j).trans (hab j).le])
    (shell_radius_cond (c j) (z j) (a j) (b j) (hz j) (ε j))
  exact this.comp (continuous_apply j)

/-- The Cauchy formula on a product of shells, as a signed sum of `2 ^ n` torus integrals. -/
private theorem torus_cauchy_shell (n : ℕ) : ∀ (c : Fin n → ℂ) (a b : Fin n → ℝ), (∀ j, 0 ≤ a j) →
    (∀ j, a j < b j) → ∀ (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E), IsOpen W →
    (∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) → ζ ∈ W) →
    ContinuousOn f W →
    (∀ ζ ∈ W, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j)) →
    ∀ z : Fin n → ℂ, (∀ j, (a j = 0 ∨ a j < ‖z j - c j‖) ∧ ‖z j - c j‖ < b j) →
    ∑ ε : Fin n → Bool, (∏ j, if ε j then (1:ℂ) else -1) •
      (∯ ζ in T(c, fun j => if ε j then b j else a j), (∏ j, (ζ j - z j)⁻¹) • f ζ) =
      (2 * π * I : ℂ) ^ n • f z := by
  induction n with
  | zero =>
    intro c a b _ _ W f _ _ _ _ z _
    simp [Subsingleton.elim z c]
  | succ n ih =>
    intro c a b ha hab W f hW hK hf hsep z hz
    have hmemW : ∀ x ∈ closedBall (c 0) (b 0) \ ball (c 0) (a 0), ∀ y : Fin n → ℂ,
        (∀ j, y j ∈ closedBall (c j.succ) (b j.succ) \ ball (c j.succ) (a j.succ)) →
        (Fin.cons x y : Fin (n + 1) → ℂ) ∈ W := by
      intro x hx y hy
      apply hK
      intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hx
      · simpa using hy j
    set r0 : Bool → ℝ := fun e => if e then b 0 else a 0 with hr0
    have hr0nn : ∀ e, 0 ≤ r0 e := fun e => by
      cases e <;> simp [r0, ha 0, (ha 0).trans (hab 0).le]
    set I' : (Fin n → Bool) → ℂ → E := fun ε' x =>
      ∯ y in T(c ∘ Fin.succ, fun j => if ε' j then b j.succ else a j.succ),
        (∏ j, (y j - z j.succ)⁻¹) • f (Fin.cons x y) with hI'
    -- the induction hypothesis on the circles
    have hIH : ∀ e : Bool, ∀ x ∈ sphere (c 0) (r0 e),
        ∑ ε' : Fin n → Bool, (∏ j, if ε' j then (1:ℂ) else -1) • I' ε' x =
          (2 * π * I : ℂ) ^ n • f (Fin.cons x (Fin.tail z)) := by
      intro e x hx
      have hx' := sphere_subset_shell (c 0) (a 0) (b 0) (hab 0) e hx
      have hc : Continuous fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ) :=
        continuous_const.finCons continuous_id
      exact ih (c ∘ Fin.succ) (a ∘ Fin.succ) (b ∘ Fin.succ) (fun j => ha j.succ)
        (fun j => hab j.succ) ((fun y => (Fin.cons x y : Fin (n + 1) → ℂ)) ⁻¹' W)
        (fun y => f (Fin.cons x y)) (hW.preimage hc) (fun y hy => hmemW x hx' y hy)
        (hf.comp hc.continuousOn fun y hy => hy)
        (fun y hy j => by
          have := hsep _ hy j.succ
          simp only [Fin.cons_succ] at this
          simpa only [Fin.cons_update] using this)
        (Fin.tail z) (fun j => hz j.succ)
    -- continuity of the inner integrals along the circles
    have hIc : ∀ (e : Bool) (ε' : Fin n → Bool),
        Continuous fun θ : ℝ => I' ε' (circleMap (c 0) (r0 e) θ) := by
      intro e ε'
      simp only [I', torusIntegral]
      refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
      refine Continuous.smul (by fun_prop) (Continuous.smul ?_ ?_)
      · exact (continuous_kernel_torus (c ∘ Fin.succ) (Fin.tail z) (a ∘ Fin.succ)
          (b ∘ Fin.succ) (fun j => ha j.succ) (fun j => hab j.succ) (fun j => hz j.succ) ε').comp
          continuous_snd
      · refine hf.comp_continuous ?_ fun p => hmemW _ ?_ _ fun j => ?_
        · exact ((continuous_circleMap _ _).comp continuous_fst).finCons
            ((continuous_torusMap' _ _).comp continuous_snd)
        · exact circleMap_mem_shell (c 0) (a 0) (b 0) (ha 0) (hab 0) e p.1
        · exact torusMap_mem_of_shell (c ∘ Fin.succ) (a ∘ Fin.succ) (b ∘ Fin.succ)
            (fun j => ha j.succ) (fun j => hab j.succ) ε' p.2 j
    have hTint : ∀ ε : Fin (n + 1) → Bool, TorusIntegrable (fun ζ => (∏ j, (ζ j - z j)⁻¹) • f ζ) c
        (fun j => if ε j then b j else a j) := by
      intro ε
      refine torusIntegrable_of_continuous ?_
      refine (continuous_kernel_torus c z a b ha hab hz ε).smul ?_
      exact hf.comp_continuous (continuous_torusMap' _ _) fun θ =>
        hK _ fun j => torusMap_mem_of_shell c a b ha hab ε θ j
    have hsplit : ∀ (e : Bool) (ε' : Fin n → Bool),
        (∏ j, if (Fin.cons e ε' : Fin (n + 1) → Bool) j then (1:ℂ) else -1) •
          (∯ ζ in T(c, fun j => if (Fin.cons e ε' : Fin (n + 1) → Bool) j then b j else a j),
            (∏ j, (ζ j - z j)⁻¹) • f ζ) =
        ((if e then (1:ℂ) else -1) * ∏ j, if ε' j then (1:ℂ) else -1) •
          ∮ x in C(c 0, r0 e), (x - z 0)⁻¹ • I' ε' x := by
      intro e ε'
      rw [Fin.prod_univ_succ, torusIntegral_succ (hTint _)]
      simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_def]
      congr 1
      congr 1
      funext x
      simp only [I', ← torusIntegral_smul]
      congr 1
      funext y
      rw [Fin.prod_univ_succ, mul_smul]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have hint : ∀ (e : Bool) (ε' : Fin n → Bool) (s : ℂ),
        CircleIntegrable (fun x => s • ((x - z 0)⁻¹ • I' ε' x)) (c 0) (r0 e) := by
      intro e ε' s
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_const.smul ((continuous_circle_inv (c 0) (z 0) (r0 e) (hr0nn e)
        (shell_radius_cond (c 0) (z 0) (a 0) (b 0) (hz 0) e)).smul (hIc e ε'))
    have hstep : ∀ e : Bool, ∑ ε' : Fin n → Bool,
        ((if e then (1:ℂ) else -1) * ∏ j, if ε' j then (1:ℂ) else -1) •
          (∮ x in C(c 0, r0 e), (x - z 0)⁻¹ • I' ε' x) =
        (2 * π * I : ℂ) ^ n • (if e then (1:ℂ) else -1) •
          ∮ x in C(c 0, r0 e), (x - z 0)⁻¹ • f (Fin.cons x (Fin.tail z)) := by
      intro e
      calc _ = (if e then (1:ℂ) else -1) • ∑ ε' : Fin n → Bool,
            ∮ x in C(c 0, r0 e), (∏ j, if ε' j then (1:ℂ) else -1) • ((x - z 0)⁻¹ • I' ε' x) := by
            rw [Finset.smul_sum]
            simp only [mul_smul, circleIntegral.integral_smul]
        _ = (if e then (1:ℂ) else -1) • ∮ x in C(c 0, r0 e), ∑ ε' : Fin n → Bool,
            (∏ j, if ε' j then (1:ℂ) else -1) • ((x - z 0)⁻¹ • I' ε' x) := by
            rw [circleIntegral_finset_sum _ _ _ _ (fun ε' _ => hint e ε' _)]
        _ = (if e then (1:ℂ) else -1) • ∮ x in C(c 0, r0 e),
            (x - z 0)⁻¹ • (2 * π * I : ℂ) ^ n • f (Fin.cons x (Fin.tail z)) := by
            congr 1
            refine circleIntegral.integral_congr (hr0nn e) fun x hx => ?_
            rw [← hIH e x hx, Finset.smul_sum]
            refine Finset.sum_congr rfl fun ε' _ => ?_
            rw [smul_comm]
        _ = _ := by
            have : (fun x => (x - z 0)⁻¹ • (2 * π * I : ℂ) ^ n • f (Fin.cons x (Fin.tail z))) =
                fun x => (2 * π * I : ℂ) ^ n • ((x - z 0)⁻¹ • f (Fin.cons x (Fin.tail z))) :=
              funext fun x => smul_comm _ _ _
            rw [this, circleIntegral.integral_smul, smul_comm]
    have hc0 : Continuous fun x : ℂ => (Fin.cons x (Fin.tail z) : Fin (n + 1) → ℂ) :=
      Continuous.finCons (f := fun x : ℂ => x) (g := fun _ => Fin.tail z) continuous_id
        continuous_const
    have h1 := cauchy_shell1 (c 0) (z 0) (a 0) (b 0) (ha 0) (hab 0)
      ((fun x => (Fin.cons x (Fin.tail z) : Fin (n + 1) → ℂ)) ⁻¹' W)
      (fun x => f (Fin.cons x (Fin.tail z))) (hW.preimage hc0)
      (fun x hx => hmemW x hx _ fun j => mem_shell_of _ _ _ _ (hz j.succ))
      (fun x hx => by
        have := hsep _ hx 0
        simp only [Fin.update_cons_zero, Fin.cons_zero] at this
        exact this.differentiableWithinAt) (hz 0)
    rw [← (Fin.consEquiv fun _ => Bool).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, hsplit, hstep]
    rw [← Finset.smul_sum]
    simp only [r0] at h1 ⊢
    rw [h1, Fin.cons_self_tail, smul_smul, pow_succ]

private theorem kernel_hasSum (c z ζ : ℂ) (R : ℝ) (hR : 0 < R) (hζ : ‖ζ - c‖ = R) (e : Bool)
    (hz : if e then ‖z - c‖ < R else R < ‖z - c‖) :
    HasSum (fun k : ℤ => if (0 ≤ k ↔ e = true) then (z - c) ^ k * (ζ - c) ^ (-k - 1) else 0)
      ((if e then (1:ℂ) else -1) * (ζ - z)⁻¹) := by
  have hζc : ζ - c ≠ 0 := by rw [← norm_ne_zero_iff, hζ]; exact hR.ne'
  cases e
  · simp only [Bool.false_eq_true, ite_false] at hz ⊢
    have hzc : z - c ≠ 0 := by
      rw [← norm_ne_zero_iff]; exact (hR.trans hz).ne'
    have hq : ‖(ζ - c) / (z - c)‖ < 1 := by
      rw [norm_div, hζ, div_lt_one (hR.trans hz)]; exact hz
    have hzζ : z - ζ ≠ 0 := by
      intro h
      have : z = ζ := sub_eq_zero.1 h
      rw [this, hζ] at hz; exact lt_irrefl _ hz
    have h2 := (hasSum_geometric_of_norm_lt_one hq).mul_right (z - c)⁻¹
    have h3 := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ =>
      if (0 ≤ k ↔ False) then (z - c) ^ k * (ζ - c) ^ (-k - 1) else 0)
      (hasSum_zero.congr_fun fun n => by simp) (h2.congr_fun fun n => ?_)
    · convert h3 using 1
      rw [zero_add]
      have : (1 - (ζ - c) / (z - c)) = (z - ζ) / (z - c) := by field_simp; ring
      rw [this, inv_div, div_mul_eq_mul_div, mul_inv_cancel₀ hzc]
      have hζz : ζ - z ≠ 0 := fun h => hzζ (by rw [← neg_sub, h, neg_zero])
      field_simp
      ring
    · have hn : (0 ≤ -((n : ℤ) + 1) ↔ False) := by simp; omega
      simp only [hn, ite_true]
      rw [show (- -((n:ℤ) + 1) - 1) = (n:ℤ) by ring, zpow_natCast, zpow_neg,
        show ((n:ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, div_pow, pow_succ]
      field_simp
  · simp only [ite_true] at hz ⊢
    have hq : ‖(z - c) / (ζ - c)‖ < 1 := by
      rw [norm_div, hζ, div_lt_one hR]; exact hz
    have hζz : ζ - z ≠ 0 := by
      intro h
      have : ζ = z := sub_eq_zero.1 h
      rw [← this, hζ] at hz; exact lt_irrefl _ hz
    have h2 := (hasSum_geometric_of_norm_lt_one hq).mul_right (ζ - c)⁻¹
    have h3 := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ =>
      if (0 ≤ k ↔ True) then (z - c) ^ k * (ζ - c) ^ (-k - 1) else 0)
      (h2.congr_fun fun n => ?_) (hasSum_zero.congr_fun fun n => ?_)
    · convert h3 using 1
      rw [add_zero]
      have : (1 - (z - c) / (ζ - c)) = (ζ - z) / (ζ - c) := by field_simp; ring
      rw [this, inv_div, div_mul_eq_mul_div, mul_inv_cancel₀ hζc]
      simp
    · simp only [Nat.cast_nonneg, ite_true]
      rw [zpow_natCast, show (-(n:ℤ) - 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast, div_pow, pow_succ]
      field_simp
    · have hn : ¬ (0 ≤ -((n : ℤ) + 1)) := by omega
      simp only [hn, iff_true, ite_false]

private theorem kernel_summable (t R : ℝ) (hR : 0 < R) (ht : 0 ≤ t) (e : Bool)
    (hz : if e then t < R else R < t) :
    Summable (fun k : ℤ => if (0 ≤ k ↔ e = true) then t ^ k * R ^ (-k - 1) else 0) := by
  have h := Complex.hasSum_re (kernel_hasSum 0 (t : ℂ) (R : ℂ) R hR
    (by simp [abs_of_pos hR]) e (by simpa [abs_of_nonneg ht] using hz))
  refine h.summable.congr fun k => ?_
  split_ifs <;> simp [← Complex.ofReal_zpow, ← Complex.ofReal_mul]

private theorem norm_torusMap_sub_center {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) (hR : ∀ j, 0 ≤ R j)
    (θ : Fin n → ℝ) (j : Fin n) : ‖torusMap c R θ j - c j‖ = R j := by
  change ‖circleMap (c j) (R j) (θ j) - c j‖ = R j
  rw [circleMap_sub_center, norm_circleMap_zero, abs_of_nonneg (hR j)]

omit [CompleteSpace E] in
/-- One sector of the expansion of a torus integral of the Cauchy kernel. -/
private theorem shell_sector_hasSum {n : ℕ} (c z : Fin n → ℂ) (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j < b j) (hz : ∀ j, (a j = 0 ∨ a j < ‖z j - c j‖) ∧ ‖z j - c j‖ < b j)
    (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E) (hf : ContinuousOn f W)
    (hK : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) → ζ ∈ W)
    (M : ℝ) (hM : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) →
      ‖f ζ‖ ≤ M) (ε : Fin n → Bool) :
    HasSum (fun β : Fin n → ℤ => if (∀ j, (0 ≤ β j ↔ ε j = true)) then
        (∏ j, (z j - c j) ^ β j) • ∯ ζ in T(c, fun j => if ε j then b j else a j),
          (∏ j, (ζ j - c j) ^ (-β j - 1)) • f ζ else 0)
      ((∏ j, if ε j then (1:ℂ) else -1) • ∯ ζ in T(c, fun j => if ε j then b j else a j),
          (∏ j, (ζ j - z j)⁻¹) • f ζ) := by
  set r : Fin n → ℝ := fun j => if ε j then b j else a j with hr_def
  have hr0 : ∀ j, 0 ≤ r j := fun j => by
    simp only [r]; split_ifs; exacts [(ha j).trans (hab j).le, ha j]
  by_cases h0 : ∃ j, r j = 0
  · rw [torusIntegral_eq_zero_of_radius _ _ _ h0, smul_zero]
    convert hasSum_zero with β
    rw [torusIntegral_eq_zero_of_radius _ _ _ h0]
    simp
  push Not at h0
  have hr : ∀ j, 0 < r j := fun j => lt_of_le_of_ne (hr0 j) (h0 j).symm
  have hzr : ∀ j, if ε j then ‖z j - c j‖ < r j else r j < ‖z j - c j‖ := by
    intro j
    have h0j := h0 j
    simp only [r] at h0j ⊢
    cases hε : ε j
    · simp only [hε, Bool.false_eq_true, ite_false] at h0j ⊢
      exact (hz j).1.resolve_left h0j
    · simp only [ite_true]; exact (hz j).2
  set g : Fin n → ℤ → ℂ → ℂ := fun j k ζj =>
    if (0 ≤ k ↔ ε j = true) then (z j - c j) ^ k * (ζj - c j) ^ (-k - 1) else 0 with hg_def
  set w : Fin n → ℤ → ℝ := fun j k =>
    if (0 ≤ k ↔ ε j = true) then ‖z j - c j‖ ^ k * r j ^ (-k - 1) else 0 with hw_def
  have hws : ∀ j, Summable (w j) := fun j =>
    kernel_summable _ _ (hr j) (norm_nonneg _) (ε j) (hzr j)
  have hw0 : ∀ j k, 0 ≤ w j k := fun j k => by
    simp only [w]; split_ifs
    · exact mul_nonneg (zpow_nonneg (norm_nonneg _) _) (zpow_nonneg (hr0 j) _)
    · exact le_rfl
  have hwn : ∀ j k (ζj : ℂ), ‖ζj - c j‖ = r j → ‖g j k ζj‖ = w j k := by
    intro j k ζj hζj
    simp only [g, w]; split_ifs
    · rw [norm_mul, norm_zpow, norm_zpow, hζj]
    · exact norm_zero
  have hwpi := (hasSum_pi_prod (𝕜 := ℝ) _ w (fun j => ∑' k, w j k) (fun j => (hws j).hasSum)
    (fun j => (hws j).congr fun k => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 j k)])).2
  have hmemT : ∀ θ, torusMap c r θ ∈ W := fun θ =>
    hK _ fun j => torusMap_mem_of_shell c a b ha hab ε θ j
  have hfT : Continuous fun θ => f (torusMap c r θ) :=
    hf.comp_continuous (continuous_torusMap' _ _) hmemT
  have key : HasSum (fun β : Fin n → ℤ => ∯ ζ in T(c, r), (∏ j, g j (β j) (ζ j)) • f ζ)
      (∯ ζ in T(c, r), (∏ j, ((if ε j then (1:ℂ) else -1) * (ζ j - z j)⁻¹)) • f ζ) := by
    refine hasSum_torusIntegral _ _ (fun β => ‖∏ j, w j (β j)‖ * M) (fun β => ?_)
      (hwpi.mul_right M) (fun β θ => ?_) (fun θ => ?_)
    · refine Continuous.smul (continuous_finsetProd _ fun j _ => ?_) hfT
      simp only [g]
      split_ifs
      · refine continuous_const.mul (Continuous.zpow₀ ?_ _ fun θ => Or.inl ?_)
        · exact ((continuous_apply j).comp (continuous_torusMap' c r)).sub continuous_const
        · exact torusMap_sub_ne c r hr θ j
      · exact continuous_const
    · rw [norm_smul, norm_prod]
      rw [Finset.prod_congr rfl fun j _ => hwn j (β j) _ (norm_torusMap_sub_center c r hr0 θ j)]
      exact mul_le_mul (Real.le_norm_self _)
        (hM _ fun j => torusMap_mem_of_shell c a b ha hab ε θ j)
        (norm_nonneg _) (norm_nonneg _)
    · refine HasSum.smul_const ?_ _
      refine (hasSum_pi_prod (𝕜 := ℂ) _ (fun j k => g j k (torusMap c r θ j))
        (fun j => (if ε j then (1:ℂ) else -1) * (torusMap c r θ j - z j)⁻¹) (fun j => ?_)
        (fun j => ?_)).1
      · exact kernel_hasSum (c j) (z j) _ (r j) (hr j) (norm_torusMap_sub_center c r hr0 θ j)
          (ε j) (hzr j)
      · exact (hws j).congr fun k => (hwn j k _ (norm_torusMap_sub_center c r hr0 θ j)).symm
  convert key using 1
  · funext β
    simp only [g, Finset.prod_ite_zero]
    by_cases hS : ∀ j, (0 ≤ β j ↔ ε j = true)
    · simp only [hS, implies_true, ite_true, Finset.prod_mul_distrib, mul_smul,
        torusIntegral_smul]
    · simp only [hS, ite_false]
      have hS' : ¬ ∀ i ∈ Finset.univ, (0 ≤ β i ↔ ε i = true) := by simpa using hS
      simp only [torusIntegral]
      refine (integral_eq_zero_of_ae (Eventually.of_forall fun θ => ?_)).symm
      rw [ite_eq_right hS', zero_smul, smul_zero]; rfl
  · simp only [Finset.prod_mul_distrib, mul_smul, torusIntegral_smul]

/-- The Laurent coefficients attached to a product of shells. -/
private noncomputable def shellCoef {n : ℕ} (c : Fin n → ℂ) (a b : Fin n → ℝ) (f : (Fin n → ℂ) → E)
    (β : Fin n → ℤ) : E :=
  ((2 * π * I : ℂ) ^ n)⁻¹ • ∯ ζ in T(c, fun j => if 0 ≤ β j then b j else a j),
    (∏ j, (ζ j - c j) ^ (-β j - 1)) • f ζ

private theorem shell_expansion {n : ℕ} (c : Fin n → ℂ) (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j < b j) (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E) (hW : IsOpen W)
    (hK : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) → ζ ∈ W)
    (hf : ContinuousOn f W)
    (hsep : ∀ ζ ∈ W, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j))
    (M : ℝ) (hM : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) →
      ‖f ζ‖ ≤ M)
    (z : Fin n → ℂ) (hz : ∀ j, (a j = 0 ∨ a j < ‖z j - c j‖) ∧ ‖z j - c j‖ < b j) :
    HasSum (fun β => (∏ j, (z j - c j) ^ β j) • shellCoef c a b f β) (f z) := by
  have hA := torus_cauchy_shell n c a b ha hab W f hW hK hf hsep z hz
  have hS := hasSum_sum (s := Finset.univ)
    (fun ε _ => shell_sector_hasSum c z a b ha hab hz W f hf hK M hM ε)
  rw [hA] at hS
  have h2 : ((2 * π * I : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have := hS.const_smul ((2 * π * I : ℂ) ^ n)⁻¹
  rw [inv_smul_smul₀ h2] at this
  convert this using 1
  funext β
  have hiff : ∀ ε : Fin n → Bool, (∀ j, (0 ≤ β j ↔ ε j = true)) ↔
      ε = fun j => decide (0 ≤ β j) := by
    intro ε
    constructor
    · intro h; funext j; rw [Bool.eq_iff_iff, decide_eq_true_iff]; exact (h j).symm
    · rintro rfl j; simp
  simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, ite_true, decide_eq_true_eq,
    shellCoef]
  rw [smul_comm]

omit [CompleteSpace E] in
private theorem norm_shellCoef_le {n : ℕ} (c : Fin n → ℂ) (a b : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j < b j) (f : (Fin n → ℂ) → E)
    (M : ℝ) (hM : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) →
      ‖f ζ‖ ≤ M) (β : Fin n → ℤ) :
    ‖shellCoef c a b f β‖ ≤ M * ∏ j, (if 0 ≤ β j then b j else a j) ^ (-β j) := by
  set r : Fin n → ℝ := fun j => if 0 ≤ β j then b j else a j with hr_def
  have hr0 : ∀ j, 0 ≤ r j := fun j => by
    simp only [r]; split_ifs; exacts [(ha j).trans (hab j).le, ha j]
  have hmem : ∀ θ j, torusMap c r θ j ∈ closedBall (c j) (b j) \ ball (c j) (a j) := by
    intro θ j
    have := torusMap_mem_of_shell c a b ha hab (fun j => decide (0 ≤ β j)) θ j
    simpa only [decide_eq_true_eq] using this
  have hb : ∀ θ, ‖(∏ j, (torusMap c r θ j - c j) ^ (-β j - 1)) • f (torusMap c r θ)‖ ≤
      (∏ j, r j ^ (-β j - 1)) * M := by
    intro θ
    rw [norm_smul, norm_prod]
    simp only [norm_zpow, norm_torusMap_sub_center c r hr0]
    exact mul_le_mul_of_nonneg_left (hM _ (hmem θ))
      (Finset.prod_nonneg fun j _ => zpow_nonneg (hr0 j) _)
  have hT := norm_torusIntegral_le_of_norm_le_const
    (f := fun ζ => (∏ j, (ζ j - c j) ^ (-β j - 1)) • f ζ) (c := c) (R := r) hb
  have hrj : ∀ j, |r j| * r j ^ (-β j - 1) = r j ^ (-β j) := by
    intro j
    rw [abs_of_nonneg (hr0 j)]
    by_cases h : r j = 0
    · have hβ : β j < 0 := by
        by_contra hβ
        push Not at hβ
        simp only [r, hβ, ite_true] at h
        exact (lt_of_le_of_lt (ha j) (hab j)).ne' h
      rw [h, zero_mul, zero_zpow _ (by omega)]
    · rw [← zpow_one_add₀ h]; ring_nf
  simp only [shellCoef]
  rw [norm_smul, norm_inv, norm_pow]
  have h2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2]
  calc ((2 * π) ^ n)⁻¹ * ‖∯ ζ in T(c, r), (∏ j, (ζ j - c j) ^ (-β j - 1)) • f ζ‖
      ≤ ((2 * π) ^ n)⁻¹ * (((2 * π) ^ n * ∏ i, |r i|) * ((∏ j, r j ^ (-β j - 1)) * M)) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = M * ∏ j, (|r j| * r j ^ (-β j - 1)) := by
        rw [Finset.prod_mul_distrib]
        field_simp
    _ = _ := by simp only [hrj, r]

omit [CompleteSpace E] in
private theorem torusIntegral_congr' {n : ℕ} {f g : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (h : ∀ θ, f (torusMap c R θ) = g (torusMap c R θ)) :
    (∯ ζ in T(c, R), f ζ) = ∯ ζ in T(c, R), g ζ := by
  simp only [torusIntegral, h]

/-- Uniqueness of Laurent coefficients: an absolutely convergent Laurent series vanishing on a
torus has zero coefficients. -/
private theorem coeff_eq_zero_of_hasSum_zero {n : ℕ} (c : Fin n → ℂ) (ρ : Fin n → ℝ)
    (hρ : ∀ j, 0 < ρ j) (d : (Fin n → ℤ) → E)
    (hsum : ∀ θ, HasSum (fun β => (∏ j, (torusMap c ρ θ j - c j) ^ β j) • d β) 0)
    (hs : Summable fun β => (∏ j, ρ j ^ β j) * ‖d β‖) (γ : Fin n → ℤ) : d γ = 0 := by
  have hρ0 : ∀ j, 0 ≤ ρ j := fun j => (hρ j).le
  have key := hasSum_torusIntegral (c := c) (R := ρ)
    (fun β ζ => (∏ j, (ζ j - c j) ^ (-γ j - 1)) • (∏ j, (ζ j - c j) ^ β j) • d β)
    (fun _ => 0) (fun β => (∏ j, ρ j ^ (-γ j - 1)) * ((∏ j, ρ j ^ β j) * ‖d β‖))
    (fun β => ?_) (hs.mul_left _) (fun β θ => ?_) (fun θ => ?_)
  · have hmono : ∀ β : Fin n → ℤ, (∯ ζ in T(c, ρ),
        (∏ j, (ζ j - c j) ^ (-γ j - 1)) • (∏ j, (ζ j - c j) ^ β j) • d β) =
        if β = γ then (2 * π * I : ℂ) ^ n • d γ else 0 := by
      intro β
      rw [torusIntegral_congr' (g := fun ζ => (∏ j, (ζ j - c j) ^ (β j - γ j - 1)) • d β)
        fun θ => ?_]
      · rw [torusIntegral_monomial n c ρ hρ]
        by_cases h : β = γ
        · subst h; simp
        · have : ¬ ∀ j, β j - γ j - 1 = -1 := fun h' => h (funext fun j => by
            have := h' j; omega)
          rw [ite_eq_right this, ite_eq_right h]
      · rw [smul_smul, ← Finset.prod_mul_distrib]
        congr 1
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← zpow_add₀ (torusMap_sub_ne c ρ hρ θ j)]
        ring_nf
    have hz0 : (∯ ζ in T(c, ρ), (0 : E)) = 0 := by simp [torusIntegral]
    simp only [hmono] at key
    rw [hz0] at key
    have h2 := hasSum_ite_eq γ ((2 * π * I : ℂ) ^ n • d γ)
    have := h2.unique key
    rwa [smul_eq_zero, or_iff_right (pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero]))] at this
  · have hcz : ∀ m : Fin n → ℤ, Continuous fun θ => ∏ j, (torusMap c ρ θ j - c j) ^ m j :=
      fun m => continuous_finsetProd _ fun j _ =>
        (((continuous_apply j).comp (continuous_torusMap' c ρ)).sub continuous_const).zpow₀ _
          fun θ => Or.inl (torusMap_sub_ne c ρ hρ θ j)
    exact (hcz _).smul ((hcz _).smul continuous_const)
  · rw [norm_smul, norm_smul, norm_prod, norm_prod]
    simp only [norm_zpow, norm_torusMap_sub_center c ρ hρ0]
    exact le_rfl
  · simpa using (hsum θ).const_smul (∏ j, (torusMap c ρ θ j - c j) ^ (-γ j - 1))

omit [CompleteSpace E] in
private theorem sep_of_differentiableOn {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → E}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ∀ ζ ∈ U, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j) := by
  intro ζ hζ j
  have h1 : DifferentiableAt ℂ f (Function.update ζ j (ζ j)) := by
    rw [Function.update_eq_self]; exact hf.differentiableAt (hU.mem_nhds hζ)
  exact h1.comp (ζ j) (differentiable_update ζ j (ζ j))

omit [CompleteSpace E] in
private theorem shellCoef_eq_zero {n : ℕ} (c : Fin n → ℂ) (a b : Fin n → ℝ) (f : (Fin n → ℂ) → E)
    (β : Fin n → ℤ) (h : ∃ j, β j < 0 ∧ a j = 0) : shellCoef c a b f β = 0 := by
  obtain ⟨j, hj, haj⟩ := h
  simp only [shellCoef]
  rw [torusIntegral_eq_zero_of_radius _ _ _ ⟨j, by simp [not_le.2 hj, haj]⟩, smul_zero]

private theorem mem_range_natCast_iff {n : ℕ} (x : Fin n → ℤ) :
    x ∈ Set.range (fun (β : Fin n → ℕ) j => (β j : ℤ)) ↔ ∀ j, 0 ≤ x j := by
  constructor
  · rintro ⟨β, rfl⟩ j; exact Int.natCast_nonneg _
  · intro h; exact ⟨fun j => (x j).toNat, funext fun j => Int.toNat_of_nonneg (h j)⟩

private theorem natCast_injective' {n : ℕ} :
    Function.Injective (fun (β : Fin n → ℕ) j => (β j : ℤ)) := by
  intro β γ h; funext j; have := congrFun h j; simp only at this; exact_mod_cast this

/-- The power series expansion on an open polydisc, with coefficients the Cauchy integrals. -/
private theorem polydisc_hasSum {n : ℕ} (c : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j)
    (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E) (hW : IsOpen W)
    (hK : Set.univ.pi (fun j => closedBall (c j) (ρ j)) ⊆ W) (hf : ContinuousOn f W)
    (hsep : ∀ ζ ∈ W, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j))
    (M : ℝ) (hM : ∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)), ‖f z‖ ≤ M)
    (z : Fin n → ℂ) (hz : z ∈ Set.univ.pi (fun j => ball (c j) (ρ j))) :
    HasSum (fun β : Fin n → ℕ => (∏ j, (z j - c j) ^ β j) •
      shellCoef c 0 ρ f (fun j => (β j : ℤ))) (f z) := by
  have hK' : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (ρ j) \ ball (c j) ((0 : Fin n → ℝ) j)) →
      ζ ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)) := fun ζ hζ j _ => (hζ j).1
  have h := shell_expansion c 0 ρ (fun _ => le_rfl) hρ W f hW (fun ζ hζ => hK (hK' ζ hζ)) hf hsep
    M (fun ζ hζ => hM ζ (hK' ζ hζ)) z (fun j => ⟨Or.inl rfl, by
      have := hz j (Set.mem_univ j); rwa [mem_ball, dist_eq_norm] at this⟩)
  rw [← natCast_injective'.hasSum_iff] at h
  · convert h using 1
    funext β
    simp [zpow_natCast]
  · intro x hx
    rw [mem_range_natCast_iff] at hx
    push Not at hx
    obtain ⟨j, hj⟩ := hx
    rw [shellCoef_eq_zero c 0 ρ f x ⟨j, hj, rfl⟩, smul_zero]

omit [CompleteSpace E] in
private theorem norm_polydiscCoef_le {n : ℕ} (c : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j)
    (f : (Fin n → ℂ) → E)
    (M : ℝ) (hM : ∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)), ‖f z‖ ≤ M)
    (β : Fin n → ℕ) :
    ‖shellCoef c 0 ρ f (fun j => (β j : ℤ))‖ ≤ M / ∏ j, ρ j ^ β j := by
  have h := norm_shellCoef_le c 0 ρ (fun _ => le_rfl) hρ f M
    (fun ζ hζ => hM ζ fun j _ => (hζ j).1) (fun j => (β j : ℤ))
  simp only [Int.natCast_nonneg, ite_true, zpow_neg, zpow_natCast] at h
  rwa [Finset.prod_inv_distrib, ← div_eq_mul_inv] at h

private theorem summable_half_int :
    Summable (fun k : ℤ => if 0 ≤ k then ((1:ℝ) / 2) ^ k else 0) := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine summable_geometric_two.congr fun n => ?_
    simp [zpow_natCast]
  · refine summable_zero.congr fun n => ?_
    have : ¬ (0 ≤ -((n : ℤ) + 1)) := by omega
    rw [ite_eq_right this]

/-- The coefficients of any power series expansion of `f` at the centre of a polydisc are the
Cauchy integrals. -/
private theorem coeff_eq_polydiscCoef {n : ℕ} (c : Fin n → ℂ) (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j)
    (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E) (hW : IsOpen W)
    (hK : Set.univ.pi (fun j => closedBall (c j) (ρ j)) ⊆ W) (hf : ContinuousOn f W)
    (hsep : ∀ ζ ∈ W, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j))
    (M : ℝ) (hM : ∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)), ‖f z‖ ≤ M)
    (a : (Fin n → ℕ) → E)
    (ha : ∀ᶠ z in 𝓝 c, HasSum (fun β => (∏ j, (z j - c j) ^ β j) • a β) (f z))
    (β : Fin n → ℕ) : a β = shellCoef c 0 ρ f (fun j => (β j : ℤ)) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 ha
  set r : Fin n → ℝ := fun j => min (δ / 4) (ρ j / 4) with hr_def
  have hr : ∀ j, 0 < r j := fun j => lt_min (by linarith) (by linarith [hρ j])
  have hr1 : ∀ j, 2 * r j < δ := fun j => by
    have := min_le_left (δ / 4) (ρ j / 4); simp only [r]; linarith
  have hr2 : ∀ j, 2 * r j < ρ j := fun j => by
    have := min_le_right (δ / 4) (ρ j / 4); simp only [r]; linarith [hρ j]
  set ã : (Fin n → ℤ) → E := fun β' => if (∀ j, 0 ≤ β' j) then a (fun j => (β' j).toNat)
    else 0 with hã
  set d : (Fin n → ℤ) → E := fun β' => ã β' - shellCoef c 0 ρ f β' with hd_def
  have hd0 : ∀ β', (∃ j, β' j < 0) → d β' = 0 := by
    rintro β' ⟨j, hj⟩
    have : ¬ ∀ j, 0 ≤ β' j := fun h => absurd (h j) (not_le.2 hj)
    simp only [d, ã, ite_eq_right this, shellCoef_eq_zero c 0 ρ f β' ⟨j, hj, rfl⟩, sub_zero]
  have hzS : ∀ z : Fin n → ℂ, (∀ j, ‖z j - c j‖ ≤ 2 * r j) →
      HasSum (fun β' => (∏ j, (z j - c j) ^ β' j) • d β') 0 := by
    intro z hz
    have h1 := hball (y := z) (by
      rw [dist_pi_lt_iff hδ]
      intro j; rw [dist_eq_norm]; exact (hz j).trans_lt (hr1 j))
    have h1' : HasSum (fun β' : Fin n → ℤ => (∏ j, (z j - c j) ^ β' j) • ã β') (f z) := by
      rw [← natCast_injective'.hasSum_iff]
      · convert h1 using 1
        funext β
        simp [ã, zpow_natCast]
      · intro x hx
        rw [mem_range_natCast_iff] at hx
        simp only [ã, ite_eq_right hx, smul_zero]
    have h2 := shell_expansion c 0 ρ (fun _ => le_rfl) hρ W f hW
      (fun ζ hζ => hK fun j _ => (hζ j).1) hf hsep M (fun ζ hζ => hM ζ fun j _ => (hζ j).1)
      z (fun j => ⟨Or.inl rfl, (hz j).trans_lt (hr2 j)⟩)
    have := h1'.sub h2
    rw [sub_self] at this
    simpa only [d, smul_sub] using this
  -- absolute convergence on the smaller torus
  set zs : Fin n → ℂ := fun j => c j + ((2 * r j : ℝ) : ℂ) with hzs
  have hzsn : ∀ j, ‖zs j - c j‖ = 2 * r j := fun j => by
    simp only [zs, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by linarith [hr j])
  have hsz := (hzS zs fun j => (hzsn j).le).summable
  obtain ⟨K, hK'⟩ := hsz.tendsto_cofinite_zero.norm.bddAbove_range_of_cofinite
  have hKb : ∀ β', (∏ j, (2 * r j) ^ β' j) * ‖d β'‖ ≤ K := by
    intro β'
    have := hK' ⟨β', rfl⟩
    simp only [norm_smul, norm_prod, norm_zpow, hzsn] at this
    exact this
  have hK0 : 0 ≤ K := (mul_nonneg (Finset.prod_nonneg fun j _ =>
    zpow_nonneg (by linarith [hr j]) _) (norm_nonneg _)).trans (hKb 0)
  have hs : Summable fun β' => (∏ j, r j ^ β' j) * ‖d β'‖ := by
    have hpi := (hasSum_pi_prod (𝕜 := ℝ) n (fun _ k => if 0 ≤ k then ((1:ℝ) / 2) ^ k else 0)
      (fun _ => ∑' k : ℤ, if 0 ≤ k then ((1:ℝ) / 2) ^ k else 0)
      (fun _ => summable_half_int.hasSum) (fun _ => summable_half_int.congr fun k => by
        split_ifs <;> simp)).2
    refine Summable.of_nonneg_of_le (fun β' => mul_nonneg (Finset.prod_nonneg fun j _ =>
      zpow_nonneg (hr j).le _) (norm_nonneg _)) (fun β' => ?_) (hpi.of_norm.mul_left K)
    by_cases hneg : ∃ j, β' j < 0
    · rw [hd0 β' hneg, norm_zero, mul_zero]
      exact mul_nonneg hK0 (Finset.prod_nonneg fun j _ => by split_ifs <;> positivity)
    · push Not at hneg
      simp only [hneg, ite_true]
      have : (∏ j, r j ^ β' j) = (∏ j, ((1:ℝ) / 2) ^ β' j) * ∏ j, (2 * r j) ^ β' j := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [← mul_zpow]; congr 1; ring
      rw [this, mul_assoc, mul_comm K]
      exact mul_le_mul_of_nonneg_left (hKb β') (Finset.prod_nonneg fun j _ => by positivity)
  have hd := coeff_eq_zero_of_hasSum_zero c r hr d (fun θ => hzS _ fun j => by
    rw [norm_torusMap_sub_center c r (fun j => (hr j).le)]; linarith [hr j]) hs
    (fun j => (β j : ℤ))
  simp only [d, ã, sub_eq_zero, Int.natCast_nonneg, implies_true, ite_true,
    Int.toNat_natCast] at hd
  exact hd

/-- The monomial `v ↦ ∏ᵢ vᵢ (σ i)` of multidegree `β` as a continuous multilinear map. -/
private noncomputable def monoML {n m : ℕ} (β : Fin n → ℕ) (h : ∑ j, β j = m) :
    ContinuousMultilinearMap ℂ (fun _ : Fin m => Fin n → ℂ) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin m) ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (finSigmaFinEquiv.symm (Fin.cast h.symm i)).1)

private theorem monoML_apply {n m : ℕ} (β : Fin n → ℕ) (h : ∑ j, β j = m) (v : Fin m → Fin n → ℂ) :
    monoML β h v = ∏ i, v i (finSigmaFinEquiv.symm (Fin.cast h.symm i)).1 := by
  simp [monoML]

private theorem monoML_apply_const {n m : ℕ} (β : Fin n → ℕ) (h : ∑ j, β j = m) (y : Fin n → ℂ) :
    monoML β h (fun _ => y) = ∏ j, y j ^ β j := by
  rw [monoML_apply]
  subst h
  simp only [Fin.cast_eq_self]
  rw [show (∏ i : Fin (∑ j, β j), y (finSigmaFinEquiv.symm i).1) =
      ∏ p : (Σ j, Fin (β j)), y p.1 from
    Fintype.prod_equiv finSigmaFinEquiv.symm _ _ fun _ => rfl]
  rw [Fintype.prod_sigma]
  simp

private theorem norm_monoML_le {n m : ℕ} (β : Fin n → ℕ) (h : ∑ j, β j = m) : ‖monoML β h‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun v => ?_
  rw [monoML_apply, norm_prod, one_mul]
  exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => norm_le_pi_norm (v i) _

omit [CompleteSpace E] in
/-- An absolutely convergent multi-index power series defines an analytic function. -/
private theorem analyticAt_of_multiHasSum {n : ℕ} (f : (Fin n → ℂ) → E) (c : Fin n → ℂ)
    (A : (Fin n → ℕ) → E) (r : ℝ) (hr : 0 < r)
    (hsumm : Summable fun β => ‖A β‖ * r ^ (∑ j, β j))
    (hsum : ∀ y : Fin n → ℂ, ‖y‖ < r →
      HasSum (fun β => (∏ j, y j ^ β j) • A β) (f (c + y))) : AnalyticAt ℂ f c := by
  let p : FormalMultilinearSeries ℂ (Fin n → ℂ) E := fun m =>
    ∑ β : Finset.Nat.antidiagonalTuple n m,
      (monoML β.1 (Finset.Nat.mem_antidiagonalTuple.1 β.2)).smulRight (A β.1)
  have hp : ∀ m (y : Fin n → ℂ), p m (fun _ => y) =
      ∑ β : Finset.Nat.antidiagonalTuple n m, (∏ j, y j ^ β.1 j) • A β.1 := by
    intro m y
    simp only [p, sum_apply, ContinuousMultilinearMap.smulRight_apply,
      monoML_apply_const]
  have hpn : ∀ m, ‖p m‖ ≤ ∑ β : Finset.Nat.antidiagonalTuple n m, ‖A β.1‖ := by
    intro m
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
    rw [ContinuousMultilinearMap.norm_smulRight]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_monoML_le _ _)
  let r' : NNReal := ⟨r, hr.le⟩
  have hrad : (r' : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_bound (∑' β, ‖A β‖ * r ^ (∑ j, β j)) fun m => ?_
    calc ‖p m‖ * (r' : ℝ) ^ m ≤ (∑ β : Finset.Nat.antidiagonalTuple n m, ‖A β.1‖) * r ^ m :=
          mul_le_mul_of_nonneg_right (hpn m) (pow_nonneg hr.le _)
      _ = ∑ β ∈ Finset.Nat.antidiagonalTuple n m, ‖A β‖ * r ^ (∑ j, β j) := by
          rw [Finset.sum_mul, ← Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple n m)]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [Finset.Nat.mem_antidiagonalTuple.1 β.2]
      _ ≤ _ := hsumm.sum_le_tsum _ fun β _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _)
  refine ⟨p, r', hrad, ENNReal.coe_pos.2 (show (0 : NNReal) < r' from hr), fun {y} hy => ?_⟩
  have hy' : ‖y‖ < r := by
    rw [Metric.mem_eball, edist_zero_right] at hy
    exact_mod_cast hy
  have h1 := hsum y hy'
  rw [← (Finset.Nat.sigmaAntidiagonalTupleEquivTuple n).hasSum_iff] at h1
  refine h1.sigma fun m => ?_
  rw [hp]
  exact hasSum_fintype _

private theorem summable_prod_geometric {n : ℕ} (q : Fin n → ℝ) (hq0 : ∀ j, 0 ≤ q j)
    (hq1 : ∀ j, q j < 1) : Summable fun β : Fin n → ℕ => ∏ j, q j ^ β j := by
  have h := (hasSum_pi_prod (𝕜 := ℝ) n (fun j k => q j ^ k) (fun j => ∑' k, q j ^ k)
    (fun j => (summable_geometric_of_lt_one (hq0 j) (hq1 j)).hasSum)
    (fun j => (summable_geometric_of_lt_one (hq0 j) (hq1 j)).congr fun k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hq0 j) k)])).2
  exact h.of_norm

private theorem osgood_at {n : ℕ} (Ω : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E) (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω)
    (hsep : ∀ ζ ∈ Ω, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j))
    (c : Fin n → ℂ) (hc : c ∈ Ω) :
    AnalyticAt ℂ f c ∧ ∃ a : (Fin n → ℕ) → E, ∀ᶠ z in 𝓝 c,
      Summable (fun β => ‖(∏ j, (z j - c j) ^ β j) • a β‖) ∧
      HasSum (fun β => (∏ j, (z j - c j) ^ β j) • a β) (f z) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ c hc
  have hε2 : 0 < ε / 2 := half_pos hε
  have hK : Set.univ.pi (fun j => closedBall (c j) (ε / 2)) ⊆ Ω := by
    intro z hz
    refine hball ?_
    rw [mem_ball]
    refine lt_of_le_of_lt ((dist_pi_le_iff hε2.le).2 fun j => ?_) (by linarith)
    exact mem_closedBall.1 (hz j (Set.mem_univ j))
  obtain ⟨M, hM⟩ := (isCompact_univ_pi fun j =>
    isCompact_closedBall (c j) (ε / 2)).exists_bound_of_continuousOn
    (hf.mono hK)
  set A : (Fin n → ℕ) → E := fun β => shellCoef c 0 (fun _ => ε / 2) f (fun j => (β j : ℤ))
  have hA : ∀ β, ‖A β‖ ≤ M / ∏ j, (ε / 2) ^ β j := fun β =>
    norm_polydiscCoef_le c (fun _ => ε / 2) (fun _ => hε2) f M hM β
  have hexp : ∀ z ∈ Set.univ.pi (fun j => ball (c j) (ε / 2)),
      HasSum (fun β => (∏ j, (z j - c j) ^ β j) • A β) (f z) := fun z hz =>
    polydisc_hasSum c (fun _ => ε / 2) (fun _ => hε2) Ω f hΩ hK hf hsep M hM z hz
  have hnorm : ∀ z ∈ Set.univ.pi (fun j => ball (c j) (ε / 2)),
      Summable (fun β => ‖(∏ j, (z j - c j) ^ β j) • A β‖) := by
    intro z hz
    have ht : ∀ j, ‖z j - c j‖ < ε / 2 := fun j => by
      have := hz j (Set.mem_univ j); rwa [mem_ball, dist_eq_norm] at this
    refine Summable.of_nonneg_of_le (fun β => norm_nonneg _) (fun β => ?_)
      ((summable_prod_geometric (fun j => ‖z j - c j‖ / (ε / 2))
        (fun j => div_nonneg (norm_nonneg _) hε2.le)
        (fun j => (div_lt_one hε2).2 (ht j))).mul_left M)
    rw [norm_smul, norm_prod]
    simp only [norm_pow]
    calc (∏ j, ‖z j - c j‖ ^ β j) * ‖A β‖ ≤ (∏ j, ‖z j - c j‖ ^ β j) * (M / ∏ j, (ε / 2) ^ β j) :=
          mul_le_mul_of_nonneg_left (hA β) (Finset.prod_nonneg fun j _ => by positivity)
      _ = M * ∏ j, (‖z j - c j‖ / (ε / 2)) ^ β j := by
          simp only [div_pow, Finset.prod_div_distrib]
          ring
  have hU : Set.univ.pi (fun j => ball (c j) (ε / 2)) ∈ 𝓝 c :=
    (isOpen_set_pi Set.finite_univ fun j _ => isOpen_ball).mem_nhds
      fun j _ => mem_ball_self hε2
  refine ⟨?_, A, Filter.mem_of_superset hU fun z hz => ⟨hnorm z hz, hexp z hz⟩⟩
  have hε4 : 0 < ε / 4 := by linarith
  have hz0 : (fun j => c j + ((ε / 4 : ℝ) : ℂ)) ∈ Set.univ.pi (fun j => ball (c j) (ε / 2)) := by
    intro j _
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε4]
    linarith
  refine analyticAt_of_multiHasSum f c A (ε / 4) hε4 ?_ fun y hy => ?_
  · refine (hnorm _ hz0).congr fun β => ?_
    rw [norm_smul, norm_prod]
    simp only [add_sub_cancel_left, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hε4, Finset.prod_pow_eq_pow_sum]
    ring
  · have hcy : c + y ∈ Set.univ.pi (fun j => ball (c j) (ε / 2)) := by
      intro j _
      rw [mem_ball, dist_eq_norm, Pi.add_apply, add_sub_cancel_left]
      exact (norm_le_pi_norm y j).trans_lt (by linarith)
    simpa only [Pi.add_apply, add_sub_cancel_left] using hexp (c + y) hcy

/-- Part (3): Osgood's lemma. -/
private theorem osgood :
    (∀ (n : ℕ) (Ω : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E), IsOpen Ω → ContinuousOn f Ω →
      (∀ ζ ∈ Ω, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j)) →
      DifferentiableOn ℂ f Ω ∧ AnalyticOnNhd ℂ f Ω ∧
      ∀ c ∈ Ω, ∃ a : (Fin n → ℕ) → E, ∀ᶠ z in 𝓝 c,
        Summable (fun β => ‖(∏ j, (z j - c j) ^ β j) • a β‖) ∧
        HasSum (fun β => (∏ j, (z j - c j) ^ β j) • a β) (f z)) := by
  intro n Ω f hΩ hf hsep
  have han : AnalyticOnNhd ℂ f Ω := fun c hc => (osgood_at Ω f hΩ hf hsep c hc).1
  exact ⟨han.differentiableOn, han, fun c hc => (osgood_at Ω f hΩ hf hsep c hc).2⟩

private theorem summable_shell_majorant1 (a b tp tn : ℝ) (ha : 0 ≤ a) (htp : 0 ≤ tp)
    (hn : a = 0 ∨ a < tn) (hp : tp < b) :
    Summable fun k : ℤ =>
      (if 0 ≤ k then tp else tn) ^ k * (if 0 ≤ k then b else a) ^ (-k) := by
  have hb : 0 < b := htp.trans_lt hp
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (summable_geometric_of_lt_one (div_nonneg htp hb.le)
      ((div_lt_one hb).2 hp)).congr fun m => ?_
    simp only [Nat.cast_nonneg, ite_true, zpow_natCast, zpow_neg, div_pow]
    rw [div_eq_mul_inv]
  · have hneg : ∀ m : ℕ, ¬ (0 ≤ -((m : ℤ) + 1)) := fun m => by omega
    have heq : ∀ m : ℕ, (if 0 ≤ -((m : ℤ) + 1) then tp else tn) ^ (-((m : ℤ) + 1)) *
        (if 0 ≤ -((m : ℤ) + 1) then b else a) ^ (-(-((m : ℤ) + 1))) = (a / tn) ^ (m + 1) := by
      intro m
      rw [ite_eq_right (hneg m), ite_eq_right (hneg m), neg_neg, div_pow,
        show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        zpow_natCast, div_eq_mul_inv, mul_comm]
    simp only [heq]
    rcases hn with h | h
    · subst h; simp only [zero_div, ne_eq, add_eq_zero, one_ne_zero, and_false,
        not_false_eq_true, zero_pow]; exact summable_zero
    · have hpos : 0 < tn := ha.trans_lt h
      refine ((summable_geometric_of_lt_one (div_nonneg ha hpos.le)
        ((div_lt_one hpos).2 h)).mul_left (a / tn)).congr fun m => ?_
      rw [pow_succ]; ring

private theorem summable_shell_majorant {n : ℕ} (a b tp tn : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (htn : ∀ j, 0 ≤ tn j) (htp : ∀ j, 0 ≤ tp j) (hn : ∀ j, a j = 0 ∨ a j < tn j)
    (hp : ∀ j, tp j < b j) :
    Summable fun β : Fin n → ℤ => ∏ j,
      ((if 0 ≤ β j then tp j else tn j) ^ β j * (if 0 ≤ β j then b j else a j) ^ (-β j)) := by
  have hnn : ∀ j (k : ℤ),
      0 ≤ (if 0 ≤ k then tp j else tn j) ^ k * (if 0 ≤ k then b j else a j) ^ (-k) :=
    fun j k => mul_nonneg (zpow_nonneg (by split_ifs; exacts [htp j, htn j]) _)
      (zpow_nonneg (by split_ifs; exacts [(htp j).trans (hp j).le, ha j]) _)
  have h := (hasSum_pi_prod (𝕜 := ℝ) n
    (fun j k => (if 0 ≤ k then tp j else tn j) ^ k * (if 0 ≤ k then b j else a j) ^ (-k)) _
    (fun j => (summable_shell_majorant1 (a j) (b j) (tp j) (tn j) (ha j) (htp j) (hn j)
      (hp j)).hasSum)
    (fun j => (summable_shell_majorant1 (a j) (b j) (tp j) (tn j) (ha j) (htp j) (hn j)
      (hp j)).congr fun k => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn j k)])).2
  exact h.of_norm

/-- Two products of shells with a common torus inside both give the same coefficients. -/
private theorem shellCoef_eq_of_common {n : ℕ} (c : Fin n → ℂ) (a b a' b' : Fin n → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j < b j) (ha' : ∀ j, 0 ≤ a' j) (hab' : ∀ j, a' j < b' j)
    (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E) (hW : IsOpen W)
    (hK : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) → ζ ∈ W)
    (hK' : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b' j) \ ball (c j) (a' j)) → ζ ∈ W)
    (hf : ContinuousOn f W)
    (hsep : ∀ ζ ∈ W, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j))
    (M : ℝ) (hM : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) →
      ‖f ζ‖ ≤ M)
    (M' : ℝ) (hM' : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b' j) \ ball (c j) (a' j)) →
      ‖f ζ‖ ≤ M')
    (ρ : Fin n → ℝ) (hρ : ∀ j, 0 < ρ j) (h1 : ∀ j, (a j = 0 ∨ a j < ρ j) ∧ ρ j < b j)
    (h2 : ∀ j, (a' j = 0 ∨ a' j < ρ j) ∧ ρ j < b' j) :
    shellCoef c a b f = shellCoef c a' b' f := by
  funext γ
  rw [← sub_eq_zero]
  refine coeff_eq_zero_of_hasSum_zero c ρ hρ (fun β => shellCoef c a b f β - shellCoef c a' b' f β)
    (fun θ => ?_) ?_ γ
  · have hn := norm_torusMap_sub_center c ρ (fun j => (hρ j).le) θ
    have e1 := shell_expansion c a b ha hab W f hW hK hf hsep M hM (torusMap c ρ θ)
      (fun j => by rw [hn j]; exact h1 j)
    have e2 := shell_expansion c a' b' ha' hab' W f hW hK' hf hsep M' hM' (torusMap c ρ θ)
      (fun j => by rw [hn j]; exact h2 j)
    simpa only [smul_sub, sub_self] using e1.sub e2
  · have s1 := (summable_shell_majorant a b ρ ρ ha (fun j => (hρ j).le) (fun j => (hρ j).le)
      (fun j => (h1 j).1) (fun j => (h1 j).2)).mul_left M
    have s2 := (summable_shell_majorant a' b' ρ ρ ha' (fun j => (hρ j).le) (fun j => (hρ j).le)
      (fun j => (h2 j).1) (fun j => (h2 j).2)).mul_left M'
    refine Summable.of_nonneg_of_le (fun β => mul_nonneg (Finset.prod_nonneg fun j _ =>
      zpow_nonneg (hρ j).le _) (norm_nonneg _)) (fun β => ?_) (s1.add s2)
    have hP : 0 ≤ ∏ j, ρ j ^ β j := Finset.prod_nonneg fun j _ => zpow_nonneg (hρ j).le _
    simp only [ite_self]
    calc (∏ j, ρ j ^ β j) * ‖shellCoef c a b f β - shellCoef c a' b' f β‖
        ≤ (∏ j, ρ j ^ β j) * (‖shellCoef c a b f β‖ + ‖shellCoef c a' b' f β‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hP
      _ ≤ (∏ j, ρ j ^ β j) * (M * ∏ j, (if 0 ≤ β j then b j else a j) ^ (-β j) +
            M' * ∏ j, (if 0 ≤ β j then b' j else a' j) ^ (-β j)) :=
          mul_le_mul_of_nonneg_left (add_le_add (norm_shellCoef_le c a b ha hab f M hM β)
            (norm_shellCoef_le c a' b' ha' hab' f M' hM' β)) hP
      _ = _ := by
          rw [mul_add, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
          ring

omit [NormedSpace ℂ E] [CompleteSpace E] in
private theorem exists_bound_shell {n : ℕ} (c : Fin n → ℂ) (a b : Fin n → ℝ) (W : Set (Fin n → ℂ))
    (f : (Fin n → ℂ) → E)
    (hK : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) → ζ ∈ W)
    (hf : ContinuousOn f W) :
    ∃ M, ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (c j) (b j) \ ball (c j) (a j)) →
      ‖f ζ‖ ≤ M := by
  have hc : IsCompact (Set.univ.pi fun j => closedBall (c j) (b j) \ ball (c j) (a j)) :=
    isCompact_univ_pi fun j => (isCompact_closedBall _ _).diff isOpen_ball
  obtain ⟨M, hM⟩ := hc.exists_bound_of_continuousOn
    (hf.mono fun ζ hζ => hK ζ fun j => hζ j (Set.mem_univ j))
  exact ⟨M, fun ζ hζ => hM ζ fun j _ => hζ j⟩

private theorem exists_shell {n : ℕ} (s : Set (Fin n)) (r : Fin n → ℝ) (R : Fin n → ENNReal)
    (hr : ∀ j ∉ s, 0 ≤ r j ∧ ENNReal.ofReal (r j) < R j) (L : Set (Fin n → ℂ))
    (hL : L ⊆ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j})
    (hLc : IsCompact L) (hLn : L.Nonempty) :
    ∃ a b α γ : Fin n → ℝ, (∀ j, 0 ≤ a j) ∧ (∀ j, a j < b j) ∧ (∀ j ∈ s, a j = 0) ∧
      (∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall (0 : ℂ) (b j) \ ball (0 : ℂ) (a j)) →
        ζ ∈ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}) ∧
      (∀ j, 0 ≤ α j ∧ (a j = 0 ∨ a j < α j) ∧ γ j < b j) ∧
      (∀ z ∈ L, ∀ j, α j ≤ ‖z j‖ ∧ ‖z j‖ ≤ γ j) := by
  classical
  have hmin : ∀ j, ∃ zm ∈ L, IsMinOn (fun z : Fin n → ℂ => ‖z j‖) L zm := fun j =>
    hLc.exists_isMinOn hLn (by fun_prop)
  have hmax : ∀ j, ∃ zm ∈ L, IsMaxOn (fun z : Fin n → ℂ => ‖z j‖) L zm := fun j =>
    hLc.exists_isMaxOn hLn (by fun_prop)
  choose zmin hzmin hmin using hmin
  choose zmax hzmax hmax using hmax
  have hbex : ∀ j, ∃ t : ℝ, ‖zmax j j‖ < t ∧ ENNReal.ofReal t < R j := by
    intro j
    have h := (hL (hzmax j) j (Set.mem_univ j)).2
    obtain ⟨t, ht0, h1, h2⟩ := ENNReal.lt_iff_exists_real_btwn.1 h
    refine ⟨t, ?_, h2⟩
    rw [← ofReal_norm] at h1
    exact (ENNReal.ofReal_lt_ofReal_iff'.1 h1).1
  choose b hb1 hb2 using hbex
  have hrα : ∀ j ∉ s, r j < ‖zmin j j‖ := fun j hj =>
    ((hL (hzmin j) j (Set.mem_univ j)).1).resolve_left hj
  have hαγ : ∀ j, ‖zmin j j‖ ≤ ‖zmax j j‖ := fun j => hmin j (hzmax j)
  refine ⟨fun j => if j ∈ s then 0 else (r j + ‖zmin j j‖) / 2, b, fun j => ‖zmin j j‖,
    fun j => ‖zmax j j‖, fun j => ?_, fun j => ?_, fun j hj => by simp [hj], fun ζ hζ => ?_,
    fun j => ?_, fun z hz j => ⟨hmin j hz, hmax j hz⟩⟩
  · dsimp only
    split_ifs with hj
    · exact le_rfl
    · linarith [(hr j hj).1, hrα j hj]
  · dsimp only
    split_ifs with hj
    · exact (norm_nonneg _).trans_lt ((hαγ j).trans_lt (hb1 j))
    · linarith [(hr j hj).1, hrα j hj, hαγ j, hb1 j]
  · intro j _
    have h1 := (hζ j).1
    have h2 := (hζ j).2
    rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_ball, dist_zero_right, not_lt] at h2
    refine ⟨?_, ?_⟩
    · by_cases hj : j ∈ s
      · exact Or.inl hj
      · right
        simp only [hj, ite_false] at h2
        linarith [(hr j hj).1, hrα j hj]
    · rw [← ofReal_norm]
      exact (ENNReal.ofReal_le_ofReal h1).trans_lt (hb2 j)
  · refine ⟨norm_nonneg _, ?_, hb1 j⟩
    by_cases hj : j ∈ s
    · left; simp [hj]
    · right; simp only [hj, ite_false]; linarith [hrα j hj]

omit [CompleteSpace E] in
private theorem norm_term_le_majorant {n : ℕ} (a b α γ : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hab : ∀ j, a j < b j) (hαγ : ∀ j, 0 ≤ α j ∧ (a j = 0 ∨ a j < α j) ∧ γ j < b j)
    (f : (Fin n → ℂ) → E) (M : ℝ)
    (hM : ∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall ((0 : Fin n → ℂ) j) (b j) \
      ball ((0 : Fin n → ℂ) j) (a j)) → ‖f ζ‖ ≤ M)
    (z : Fin n → ℂ) (hz : ∀ j, α j ≤ ‖z j‖ ∧ ‖z j‖ ≤ γ j) (β : Fin n → ℤ) :
    ‖(∏ j, z j ^ β j) • shellCoef 0 a b f β‖ ≤
      M * ∏ j, ((if 0 ≤ β j then γ j else α j) ^ β j *
        (if 0 ≤ β j then b j else a j) ^ (-β j)) := by
  have hM0 : 0 ≤ M := by
    refine (norm_nonneg _).trans (hM (fun j => (b j : ℂ)) fun j => ?_)
    have hb0 : 0 < b j := (ha j).trans_lt (hab j)
    refine ⟨?_, ?_⟩
    · rw [Pi.zero_apply, mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hb0]
    · rw [Pi.zero_apply, mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hb0, not_lt]
      exact (hab j).le
  rw [norm_smul, norm_prod]
  simp only [norm_zpow]
  calc (∏ j, ‖z j‖ ^ β j) * ‖shellCoef 0 a b f β‖
      ≤ (∏ j, ‖z j‖ ^ β j) * (M * ∏ j, (if 0 ≤ β j then b j else a j) ^ (-β j)) :=
        mul_le_mul_of_nonneg_left (norm_shellCoef_le 0 a b ha hab f M hM β)
          (Finset.prod_nonneg fun j _ => zpow_nonneg (norm_nonneg _) _)
    _ = M * ∏ j, (‖z j‖ ^ β j * (if 0 ≤ β j then b j else a j) ^ (-β j)) := by
        rw [Finset.prod_mul_distrib]; ring
    _ ≤ _ := by
      have hr0 : ∀ j, 0 ≤ (if 0 ≤ β j then b j else a j) := fun j => by
        split_ifs
        · exact (ha j).trans (hab j).le
        · exact ha j
      refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun j _ => mul_nonneg
        (zpow_nonneg (norm_nonneg _) _) (zpow_nonneg (hr0 j) _)) fun j _ => ?_) hM0
      by_cases hβ : 0 ≤ β j
      · simp only [hβ, ite_true]
        exact mul_le_mul_of_nonneg_right (zpow_le_zpow_left₀ hβ (norm_nonneg _) (hz j).2)
          (zpow_nonneg ((ha j).trans (hab j).le) _)
      · simp only [hβ, ite_false]
        rcases (hαγ j).2.1 with h0 | h0
        · rw [h0, zero_zpow (-β j) (by omega), mul_zero, mul_zero]
        · have hα : 0 < α j := (ha j).trans_lt h0
          refine mul_le_mul_of_nonneg_right ?_ (zpow_nonneg (ha j) _)
          have e : ∀ x : ℝ, x ^ β j = (x ^ (-β j))⁻¹ := fun x => by rw [zpow_neg, inv_inv]
          rw [e, e]
          exact inv_anti₀ (zpow_pos hα _)
            (zpow_le_zpow_left₀ (show (0:ℤ) ≤ -β j by omega) hα.le (hz j).1)

/-- The Laurent expansion on a product of discs and annuli centred at `0`, with a summable
majorant on every compact subset. -/
private theorem laurent_core :
    (∀ (n : ℕ) (s : Set (Fin n)) (r : Fin n → ℝ) (R : Fin n → ENNReal) (f : (Fin n → ℂ) → E),
      (∀ j ∉ s, 0 ≤ r j ∧ ENNReal.ofReal (r j) < R j) →
      DifferentiableOn ℂ f
        (Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}) →
      ∃ c : (Fin n → ℤ) → E, (∀ β, (∃ j ∈ s, β j < 0) → c β = 0) ∧
        (∀ z ∈ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j},
          HasSum (fun β => (∏ j, z j ^ β j) • c β) (f z)) ∧
        (∀ L ⊆ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}, IsCompact L →
          ∃ u : (Fin n → ℤ) → ℝ, Summable u ∧ ∀ β, ∀ z ∈ L, ‖(∏ j, z j ^ β j) • c β‖ ≤ u β)) := by
  classical
  intro n s r R f hr hf
  set D := Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j} with hD
  have hDo : IsOpen D := by
    refine isOpen_set_pi Set.finite_univ fun j _ => ?_
    rw [Set.ofPred_and, Set.ofPred_or]
    exact (isOpen_const.union (isOpen_lt continuous_const continuous_norm)).inter
      (isOpen_lt continuous_enorm continuous_const)
  have hcont := hf.continuousOn
  have hsep := sep_of_differentiableOn hDo hf
  by_cases hDn : D.Nonempty
  swap
  · refine ⟨0, fun _ _ => rfl, fun z hz => absurd ⟨z, hz⟩ hDn, fun L hL _ =>
      ⟨0, summable_zero, fun β z hz => absurd ⟨z, hL hz⟩ hDn⟩⟩
  obtain ⟨z0, hz0⟩ := hDn
  obtain ⟨a0, b0, α0, γ0, ha0, hab0, has0, hK0, hαγ0, hL0⟩ :=
    exists_shell s r R hr {z0} (Set.singleton_subset_iff.2 hz0) isCompact_singleton
      (Set.singleton_nonempty z0)
  obtain ⟨M0, hM0⟩ := exists_bound_shell 0 a0 b0 D f hK0 hcont
  have hcommon : ∀ L ⊆ D, IsCompact L → L.Nonempty → ∃ a b α γ : Fin n → ℝ, ∃ M : ℝ,
      (∀ j, 0 ≤ a j) ∧ (∀ j, a j < b j) ∧
      (∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall ((0 : Fin n → ℂ) j) (b j) \
        ball ((0 : Fin n → ℂ) j) (a j)) → ζ ∈ D) ∧
      (∀ j, 0 ≤ α j ∧ (a j = 0 ∨ a j < α j) ∧ γ j < b j) ∧
      (∀ z ∈ L, ∀ j, α j ≤ ‖z j‖ ∧ ‖z j‖ ≤ γ j) ∧
      (∀ ζ : Fin n → ℂ, (∀ j, ζ j ∈ closedBall ((0 : Fin n → ℂ) j) (b j) \
        ball ((0 : Fin n → ℂ) j) (a j)) → ‖f ζ‖ ≤ M) ∧
      shellCoef 0 a b f = shellCoef 0 a0 b0 f := by
    intro L hL hLc hLn
    obtain ⟨a, b, α, γ, ha, hab, has, hK, hαγ, hLb⟩ :=
      exists_shell s r R hr (L ∪ {z0}) (Set.union_subset hL (Set.singleton_subset_iff.2 hz0))
        (hLc.union isCompact_singleton) (hLn.mono Set.subset_union_left)
    obtain ⟨M, hM⟩ := exists_bound_shell 0 a b D f hK hcont
    refine ⟨a, b, α, γ, M, ha, hab, hK, hαγ, fun z hz => hLb z (Or.inl hz), hM, ?_⟩
    set ρ : Fin n → ℝ := fun j => if j ∈ s then min (b j) (b0 j) / 2 else ‖z0 j‖ with hρ_def
    have hz0b := hLb z0 (Or.inr rfl)
    have hz0b0 := hL0 z0 rfl
    have hb : ∀ j, 0 < b j := fun j => (ha j).trans_lt (hab j)
    have hb0 : ∀ j, 0 < b0 j := fun j => (ha0 j).trans_lt (hab0 j)
    have hρ : ∀ j, 0 < ρ j := by
      intro j
      by_cases hj : j ∈ s
      · simpa only [ρ, hj, ite_true] using half_pos (lt_min (hb j) (hb0 j))
      · simp only [ρ, hj, ite_false]
        exact lt_of_le_of_lt (hr j hj).1 (((hz0 j (Set.mem_univ j)).1).resolve_left hj)
    have hside : ∀ (a' b' α' γ' : Fin n → ℝ), (∀ j ∈ s, a' j = 0) → (∀ j, 0 < b' j) →
        (∀ j, 0 ≤ α' j ∧ (a' j = 0 ∨ a' j < α' j) ∧ γ' j < b' j) →
        (∀ j, α' j ≤ ‖z0 j‖ ∧ ‖z0 j‖ ≤ γ' j) →
        (∀ j, j ∈ s → min (b j) (b0 j) ≤ b' j) →
        ∀ j, (a' j = 0 ∨ a' j < ρ j) ∧ ρ j < b' j := by
      intro a' b' α' γ' has' hb' hαγ' hz' hmin j
      by_cases hj : j ∈ s
      · simp only [ρ, hj, ite_true]
        refine ⟨Or.inl (has' j hj), ?_⟩
        have := hmin j hj
        linarith [lt_min (hb j) (hb0 j)]
      · simp only [ρ, hj, ite_false]
        refine ⟨?_, (hz' j).2.trans_lt (hαγ' j).2.2⟩
        rcases (hαγ' j).2.1 with h | h
        · exact Or.inl h
        · exact Or.inr (h.trans_le (hz' j).1)
    exact shellCoef_eq_of_common 0 a b a0 b0 ha hab ha0 hab0 D f hDo hK hK0 hcont hsep M hM M0
      hM0 ρ hρ (hside a b α γ has hb hαγ hz0b fun j _ => min_le_left _ _)
      (hside a0 b0 α0 γ0 has0 hb0 hαγ0 hz0b0 fun j _ => min_le_right _ _)
  refine ⟨shellCoef 0 a0 b0 f, fun β ⟨j, hj, hβ⟩ => shellCoef_eq_zero 0 a0 b0 f β
    ⟨j, hβ, has0 j hj⟩, fun z hz => ?_, fun L hL hLc => ?_⟩
  · obtain ⟨a, b, α, γ, M, ha, hab, hK, hαγ, hLb, hM, heq⟩ :=
      hcommon {z} (Set.singleton_subset_iff.2 hz) isCompact_singleton (Set.singleton_nonempty z)
    rw [← heq]
    have hzb := hLb z rfl
    have := shell_expansion 0 a b ha hab D f hDo hK hcont hsep M hM z fun j => by
      simp only [Pi.zero_apply, sub_zero]
      refine ⟨?_, (hzb j).2.trans_lt (hαγ j).2.2⟩
      rcases (hαγ j).2.1 with h | h
      · exact Or.inl h
      · exact Or.inr (h.trans_le (hzb j).1)
    simpa only [Pi.zero_apply, sub_zero] using this
  · rcases L.eq_empty_or_nonempty with hLe | hLn
    · exact ⟨0, summable_zero, fun β z hz => by
        rw [hLe] at hz; exact absurd hz (Set.notMem_empty z)⟩
    obtain ⟨a, b, α, γ, M, ha, hab, hK, hαγ, hLb, hM, heq⟩ := hcommon L hL hLc hLn
    obtain ⟨zL, hzL⟩ := hLn
    refine ⟨fun β => M * ∏ j, ((if 0 ≤ β j then γ j else α j) ^ β j *
        (if 0 ≤ β j then b j else a j) ^ (-β j)),
      (summable_shell_majorant a b γ α ha (fun j => (hαγ j).1)
        (fun j => (norm_nonneg _).trans (hLb zL hzL j).2) (fun j => (hαγ j).2.1)
        (fun j => (hαγ j).2.2)).mul_left M, fun β z hz => ?_⟩
    rw [← heq]
    exact norm_term_le_majorant a b α γ ha hab hαγ f M hM z (hLb z hz) β

/-- The Cauchy estimate for the coefficients of a power series expansion at the centre of a
closed polydisc on which `f` is holomorphic and bounded by `M`. -/
private theorem norm_coeff_le_of_polydisc {n : ℕ} (c : Fin n → ℂ) (ρ : Fin n → ℝ) (M : ℝ)
    (U : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E) (hρ : ∀ j, 0 < ρ j) (hU : IsOpen U)
    (hKU : Set.univ.pi (fun j => closedBall (c j) (ρ j)) ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hM : ∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)), ‖f z‖ ≤ M)
    (a : (Fin n → ℕ) → E)
    (ha : ∀ᶠ z in 𝓝 c, HasSum (fun β => (∏ j, (z j - c j) ^ β j) • a β) (f z)) (β : Fin n → ℕ) :
    ‖a β‖ ≤ M / ∏ j, ρ j ^ β j := by
  rw [coeff_eq_polydiscCoef c ρ hρ U f hU hKU hf.continuousOn (sep_of_differentiableOn hU hf) M hM
    a ha β]
  exact norm_polydiscCoef_le c ρ hρ f M hM β

omit [CompleteSpace E] in
/-- The Cauchy estimate for the first partial derivatives on the polydisc of half the
polyradius: the one-variable estimate on the disc of radius `ρ j / 2` in the `j`-th
coordinate. -/
private theorem norm_fderiv_single_le_of_polydisc {n : ℕ} (c : Fin n → ℂ) (ρ : Fin n → ℝ)
    (M : ℝ) (U : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E) (hρ : ∀ j, 0 < ρ j) (hU : IsOpen U)
    (hKU : Set.univ.pi (fun j => closedBall (c j) (ρ j)) ⊆ U) (hf : DifferentiableOn ℂ f U)
    (hM : ∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)), ‖f z‖ ≤ M) :
    ∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j / 2)), ∀ j,
      ‖fderiv ℂ f z (Pi.single j 1)‖ ≤ 2 ^ (n + 1) * M / ⨅ i, ρ i := by
  intro z hz j
  have hzK : z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)) := fun i _ =>
    closedBall_subset_closedBall (by linarith [hρ i]) (hz i (Set.mem_univ i))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hzK)
  set φ : ℂ → Fin n → ℂ := fun w => Function.update z j w
  have hφ : ∀ w, HasDerivAt φ (Pi.single j 1) w := fun w => hasDerivAt_update z j w
  have hball : ∀ w ∈ closedBall (z j) (ρ j / 2),
      φ w ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)) := by
    intro w hw i _
    by_cases h : i = j
    · subst h
      simp only [φ, Function.update_self, mem_closedBall]
      have := hz i (Set.mem_univ i)
      rw [mem_closedBall] at this hw
      linarith [dist_triangle w (z i) (c i)]
    · simpa [φ, Function.update_of_ne h] using hzK i (Set.mem_univ i)
  have hderiv : fderiv ℂ f z (Pi.single j 1) = deriv (f ∘ φ) (z j) := by
    have hfz : HasFDerivAt f (fderiv ℂ f z) (φ (z j)) := by
      simpa [φ] using (hf.differentiableAt (hU.mem_nhds (hKU hzK))).hasFDerivAt
    have := hfz.comp_hasDerivAt (z j) (hφ (z j))
    exact this.deriv.symm
  rw [hderiv]
  have hdc : DiffContOnCl ℂ (f ∘ φ) (ball (z j) (ρ j / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ (by linarith [hρ j])]
    intro w hw
    exact ((hf.differentiableAt (hU.mem_nhds (hKU (hball w hw)))).comp w
      (hφ w).differentiableAt).differentiableWithinAt
  have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by linarith [hρ j]) hdc
    (fun w hw => hM _ (hball w (sphere_subset_closedBall hw)))
  have : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i0, hi0⟩ := exists_eq_ciInf_of_finite (f := ρ)
  have hm : 0 < ⨅ i, ρ i := hi0 ▸ hρ i0
  have hmj : (⨅ i, ρ i) ≤ ρ j := ciInf_le (Set.finite_range ρ).bddBelow j
  refine h1.trans ?_
  rw [div_div_eq_mul_div, div_le_div_iff₀ (hρ j) hm]
  have h2 : (2:ℝ) ≤ 2 ^ (n + 1) := by
    calc (2:ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n+1) := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith [mul_le_mul_of_nonneg_left hmj hM0,
    mul_le_mul_of_nonneg_right h2 (mul_nonneg hM0 (hρ j).le)]

/-- Part (4): the Cauchy estimates on a closed polydisc. -/
private theorem cauchy_estimates :
    (∀ (n : ℕ) (c : Fin n → ℂ) (ρ : Fin n → ℝ) (M : ℝ) (U : Set (Fin n → ℂ))
      (f : (Fin n → ℂ) → E), (∀ j, 0 < ρ j) → IsOpen U →
      Set.univ.pi (fun j => closedBall (c j) (ρ j)) ⊆ U → DifferentiableOn ℂ f U →
      (∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)), ‖f z‖ ≤ M) →
      (∀ a : (Fin n → ℕ) → E,
        (∀ᶠ z in 𝓝 c, HasSum (fun β => (∏ j, (z j - c j) ^ β j) • a β) (f z)) →
        ∀ β, ‖a β‖ ≤ M / ∏ j, ρ j ^ β j) ∧
      ∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j / 2)), ∀ j,
        ‖fderiv ℂ f z (Pi.single j 1)‖ ≤ 2 ^ (n + 1) * M / ⨅ i, ρ i) :=
  fun _ c ρ M U f hρ hU hKU hf hM =>
    ⟨norm_coeff_le_of_polydisc c ρ M U f hρ hU hKU hf hM,
      norm_fderiv_single_le_of_polydisc c ρ M U f hρ hU hKU hf hM⟩

/-- Part (5): the Laurent expansion on a product of discs and annuli centred at `0`. Every
subseries converges uniformly on compact subsets by the Weierstrass test. -/
private theorem laurent :
    (∀ (n : ℕ) (s : Set (Fin n)) (r : Fin n → ℝ) (R : Fin n → ENNReal) (f : (Fin n → ℂ) → E),
      (∀ j ∉ s, 0 ≤ r j ∧ ENNReal.ofReal (r j) < R j) →
      DifferentiableOn ℂ f
        (Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}) →
      ∃ c : (Fin n → ℤ) → E, (∀ β, (∃ j ∈ s, β j < 0) → c β = 0) ∧
        (∀ z ∈ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j},
          HasSum (fun β => (∏ j, z j ^ β j) • c β) (f z)) ∧
        (∀ L ⊆ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}, IsCompact L →
          ∃ u : (Fin n → ℤ) → ℝ, Summable u ∧ ∀ β, ∀ z ∈ L, ‖(∏ j, z j ^ β j) • c β‖ ≤ u β) ∧
        (∀ T : Set (Fin n → ℤ),
          ∀ L ⊆ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}, IsCompact L →
          TendstoUniformlyOn
            (fun (S : Finset (Fin n → ℤ)) z =>
              ∑ β ∈ S, T.indicator (fun β => (∏ j, z j ^ β j) • c β) β)
            (fun z => ∑' β, T.indicator (fun β => (∏ j, z j ^ β j) • c β) β) atTop L)) := by
  intro n s r R f hr hf
  obtain ⟨c, hc0, hsum, hmaj⟩ := laurent_core n s r R f hr hf
  refine ⟨c, hc0, hsum, hmaj, fun T L hL hLc => ?_⟩
  obtain ⟨u, hu, hub⟩ := hmaj L hL hLc
  refine tendstoUniformlyOn_tsum hu fun β z hz => ?_
  exact (norm_indicator_le_norm_self _ _).trans (hub β z hz)

/-- Part (6): a locally uniform limit of holomorphic functions is holomorphic. -/
private theorem differentiableOn_of_tendstoLocallyUniformlyOn :
    (∀ (n : ℕ) {ι : Type*} (l : Filter ι) [l.NeBot] (Ω : Set (Fin n → ℂ))
      (F : ι → (Fin n → ℂ) → E) (f : (Fin n → ℂ) → E), IsOpen Ω →
      (∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω) → TendstoLocallyUniformlyOn F f l Ω →
      DifferentiableOn ℂ f Ω) := by
  intro n ι l _ Ω F f hΩ hF hFf
  have hcont : ContinuousOn f Ω :=
    hFf.continuousOn (hF.mono fun i hi => hi.continuousOn).frequently
  refine (osgood n Ω f hΩ hcont fun ζ hζ j => ?_).1
  set φ : ℂ → Fin n → ℂ := fun w => Function.update ζ j w
  have hφ : Continuous φ := by fun_prop
  have hV : IsOpen (φ ⁻¹' Ω) := hΩ.preimage hφ
  have hζV : ζ j ∈ φ ⁻¹' Ω := by simpa [φ] using hζ
  have hlim : TendstoLocallyUniformlyOn (fun i => F i ∘ φ) (f ∘ φ) l (φ ⁻¹' Ω) :=
    hFf.comp φ (fun w hw => hw) hφ.continuousOn
  have hd : DifferentiableOn ℂ (f ∘ φ) (φ ⁻¹' Ω) :=
    hlim.differentiableOn (hF.mono fun i hi =>
      hi.comp (fun w _ => (differentiable_update ζ j w).differentiableWithinAt) fun w hw => hw) hV
  exact hd.differentiableAt (hV.mem_nhds hζV)

end MMP.SeveralComplex.Internal.GagaIteratedCauchy

namespace MMP.SeveralComplex

open MMP.SeveralComplex.Internal.GagaIteratedCauchy in
/-- **Cauchy integral formulas, Osgood's lemma, Cauchy estimates, Laurent expansions and
locally uniform limits** in several complex variables, for functions with values in a complex
Banach space. -/
@[mmp "lem_mmp_gaga_iterated_cauchy"]
public theorem cauchy_osgood_laurent (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] :
    -- (1) Cauchy integral formula on a standard compact
    (∀ (K : Set ℂ) (B : (ℂ → E) → E),
      ((∃ z w : ℂ, z.re < w.re ∧ z.im < w.im ∧
          K = Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im ∧
          B = fun g => (∫ x : ℝ in z.re..w.re, g (x + z.im * I)) -
            (∫ x : ℝ in z.re..w.re, g (x + w.im * I)) +
            I • (∫ y : ℝ in z.im..w.im, g (w.re + y * I)) -
            I • ∫ y : ℝ in z.im..w.im, g (z.re + y * I)) ∨
        (∃ (c : ℂ) (R : ℝ), 0 < R ∧ K = closedBall c R ∧ B = fun g => ∮ ζ in C(c, R), g ζ) ∨
        (∃ (c : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧ K = closedBall c R \ ball c r ∧
          B = fun g => (∮ ζ in C(c, R), g ζ) - ∮ ζ in C(c, r), g ζ)) →
      ∀ (U : Set ℂ) (f : ℂ → E), IsOpen U → K ⊆ U → DifferentiableOn ℂ f U →
      ∀ z ∈ interior K, (2 * π * I : ℂ)⁻¹ • B (fun ζ => (ζ - z)⁻¹ • f ζ) = f z) ∧
    -- (2) iterated Cauchy integral formula on a product of standard compacts
    (∀ (n : ℕ) (K : Fin n → Set ℂ) (B : Fin n → (ℂ → E) → E),
      (∀ j, (∃ z w : ℂ, z.re < w.re ∧ z.im < w.im ∧
          K j = Set.Icc z.re w.re ×ℂ Set.Icc z.im w.im ∧
          B j = fun g => (∫ x : ℝ in z.re..w.re, g (x + z.im * I)) -
            (∫ x : ℝ in z.re..w.re, g (x + w.im * I)) +
            I • (∫ y : ℝ in z.im..w.im, g (w.re + y * I)) -
            I • ∫ y : ℝ in z.im..w.im, g (z.re + y * I)) ∨
        (∃ (c : ℂ) (R : ℝ), 0 < R ∧ K j = closedBall c R ∧
          B j = fun g => ∮ ζ in C(c, R), g ζ) ∨
        (∃ (c : ℂ) (r R : ℝ), 0 < r ∧ r < R ∧ K j = closedBall c R \ ball c r ∧
          B j = fun g => (∮ ζ in C(c, R), g ζ) - ∮ ζ in C(c, r), g ζ)) →
      ∀ (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E), IsOpen W → Set.univ.pi K ⊆ W →
      ContinuousOn f W →
      (∀ ζ ∈ W, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j)) →
      ∀ z ∈ interior (Set.univ.pi K),
        f z = ((2 * π * I : ℂ) ^ n)⁻¹ •
          (List.finRange n).foldr (fun j F ζ => B j fun w => F (Function.update ζ j w))
            (fun ζ => (∏ j, (ζ j - z j)⁻¹) • f ζ) z) ∧
    -- (3) Osgood's lemma
    (∀ (n : ℕ) (Ω : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → E), IsOpen Ω → ContinuousOn f Ω →
      (∀ ζ ∈ Ω, ∀ j, DifferentiableAt ℂ (fun w => f (Function.update ζ j w)) (ζ j)) →
      DifferentiableOn ℂ f Ω ∧ AnalyticOnNhd ℂ f Ω ∧
      ∀ c ∈ Ω, ∃ a : (Fin n → ℕ) → E, ∀ᶠ z in 𝓝 c,
        Summable (fun β => ‖(∏ j, (z j - c j) ^ β j) • a β‖) ∧
        HasSum (fun β => (∏ j, (z j - c j) ^ β j) • a β) (f z)) ∧
    -- (4) Cauchy estimates
    (∀ (n : ℕ) (c : Fin n → ℂ) (ρ : Fin n → ℝ) (M : ℝ) (U : Set (Fin n → ℂ))
      (f : (Fin n → ℂ) → E), (∀ j, 0 < ρ j) → IsOpen U →
      Set.univ.pi (fun j => closedBall (c j) (ρ j)) ⊆ U → DifferentiableOn ℂ f U →
      (∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j)), ‖f z‖ ≤ M) →
      (∀ a : (Fin n → ℕ) → E,
        (∀ᶠ z in 𝓝 c, HasSum (fun β => (∏ j, (z j - c j) ^ β j) • a β) (f z)) →
        ∀ β, ‖a β‖ ≤ M / ∏ j, ρ j ^ β j) ∧
      ∀ z ∈ Set.univ.pi (fun j => closedBall (c j) (ρ j / 2)), ∀ j,
        ‖fderiv ℂ f z (Pi.single j 1)‖ ≤ 2 ^ (n + 1) * M / ⨅ i, ρ i) ∧
    -- (5) Laurent expansion on a product of discs and annuli centred at `0`
    (∀ (n : ℕ) (s : Set (Fin n)) (r : Fin n → ℝ) (R : Fin n → ENNReal) (f : (Fin n → ℂ) → E),
      (∀ j ∉ s, 0 ≤ r j ∧ ENNReal.ofReal (r j) < R j) →
      DifferentiableOn ℂ f
        (Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}) →
      ∃ c : (Fin n → ℤ) → E, (∀ β, (∃ j ∈ s, β j < 0) → c β = 0) ∧
        (∀ z ∈ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j},
          HasSum (fun β => (∏ j, z j ^ β j) • c β) (f z)) ∧
        (∀ L ⊆ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}, IsCompact L →
          ∃ u : (Fin n → ℤ) → ℝ, Summable u ∧ ∀ β, ∀ z ∈ L, ‖(∏ j, z j ^ β j) • c β‖ ≤ u β) ∧
        (∀ T : Set (Fin n → ℤ),
          ∀ L ⊆ Set.univ.pi fun j => {w : ℂ | (j ∈ s ∨ r j < ‖w‖) ∧ ‖w‖ₑ < R j}, IsCompact L →
          TendstoUniformlyOn
            (fun (S : Finset (Fin n → ℤ)) z =>
              ∑ β ∈ S, T.indicator (fun β => (∏ j, z j ^ β j) • c β) β)
            (fun z => ∑' β, T.indicator (fun β => (∏ j, z j ^ β j) • c β) β) atTop L)) ∧
    -- (6) locally uniform limits of holomorphic functions
    (∀ (n : ℕ) {ι : Type*} (l : Filter ι) [l.NeBot] (Ω : Set (Fin n → ℂ))
      (F : ι → (Fin n → ℂ) → E) (f : (Fin n → ℂ) → E), IsOpen Ω →
      (∀ᶠ i in l, DifferentiableOn ℂ (F i) Ω) → TendstoLocallyUniformlyOn F f l Ω →
      DifferentiableOn ℂ f Ω) :=
  ⟨cauchy_standard_compact, cauchy_iterated, osgood, cauchy_estimates, laurent,
    differentiableOn_of_tendstoLocallyUniformlyOn⟩

end MMP.SeveralComplex

end

/-!
# Prime divisors of the product of a variety with a line

Let `Z` be a variety over a field `k` and `L` the affine line `𝔸¹_k = Spec k[s]` or the
projective line `ℙ¹_k`, and let `pr : Z ×_k L ⟶ Z` be the first projection. For every prime
divisor `Γ` of `Z`, the preimage `Γ × L = pr⁻¹(Γ)` is (the support of) a prime divisor of
`Z ×_k L`. Conversely every prime divisor `D` of `Z ×_k L` either is `Γ × L` for a prime divisor
`Γ` of `Z` with support `closure (pr(D))`, or dominates `Z`, that is, `pr(D)` is dense in `Z`.
When `L = ℙ¹` the projection is proper, so a dominating prime divisor surjects onto `Z`.

The first two assertions hold for any smooth geometrically irreducible curve `L` over `k`. Such
an `L` is geometrically integral, so `W ×_k L` is a variety of dimension `dim W + 1` for every
variety `W`; hence `pr⁻¹` of an irreducible closed subset is irreducible and raises codimension by
at most one, and an irreducible closed subset of codimension one which does not dominate `Z` is
the preimage of the closure of its image.

## Main results

* `MMP.primeDivisor_pullback_eq_preimage_or_dense_of_smooth`: the classification for a smooth
  geometrically irreducible curve `L`.
* `MMP.primeDivisor_pullback_line_eq_preimage_or_dense`: the cases `L = 𝔸¹_k` and `L = ℙ¹_k`,
  with surjectivity of dominating prime divisors for `ℙ¹_k`.

## Implementation notes

* The product `Z × L` is the fibre product over `Spec k`; the affine line is `Spec k[X]` over
  `Spec k` through `Polynomial.C`, and the projective line is `AlgebraicGeometry.projectiveLine k`.
* A prime divisor is an `MMP.Mori.PrimeDivisor`, an integral closed subscheme of codimension one;
  being integral, it is determined by its support, so the equalities of prime divisors are
  stated as equalities of supports `D.idealSheaf.support`, as subsets of the underlying space.
-/

section

universe u

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace MMP

namespace MMP.Internal.IndexbProductPrimeDivisors

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

private theorem one_le_codimension_iff (T : IrreducibleCloseds Y) :
    1 ≤ codimension T ↔ ¬ IsMax T := by
  rw [codimension_eq_coheight, ENat.one_le_iff_ne_zero, Ne, Order.coheight_eq_zero]

private theorem isMax_iff [IrreducibleSpace Y] (T : IrreducibleCloseds Y) :
    IsMax T ↔ (T : Set Y) = Set.univ := by
  constructor
  · intro h
    let U : IrreducibleCloseds Y := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ Y, isClosed_univ⟩
    exact Set.eq_univ_of_univ_subset (h (show T ≤ U from fun _ _ => trivial))
  · intro h S _
    show (S : Set Y) ⊆ T
    rw [h]
    exact Set.subset_univ _

variable (π : X → Y) (hc : Continuous π) (hs : Function.Surjective π)
  (hirr : ∀ T : IrreducibleCloseds Y, IsIrreducible (π ⁻¹' T))

/-- preimage as an irreducible closed. -/
private def pre (T : IrreducibleCloseds Y) : IrreducibleCloseds X :=
  ⟨π ⁻¹' T, hirr T, T.isClosed.preimage hc⟩

include hc hs hirr in
private theorem pre_strictMono : StrictMono (pre π hc hirr) := by
  intro T T' h
  rw [← SetLike.coe_ssubset_coe] at h ⊢
  change π ⁻¹' T ⊂ π ⁻¹' T'
  exact ⟨Set.preimage_mono h.1, fun h2 => h.2 (hs.preimage_subset_preimage_iff.mp h2)⟩

include hc hs hirr in
private theorem codimension_le_pre (T : IrreducibleCloseds Y) :
    codimension T ≤ codimension (pre π hc hirr T) :=
  Order.coheight_le_coheight_apply_of_strictMono _ (pre_strictMono π hc hs hirr) T

include hc hs hirr in
private theorem codimension_pre_eq_one [IrreducibleSpace Y]
    (hcod : ∀ T : IrreducibleCloseds Y, codimension T = 1 → codimension (pre π hc hirr T) ≤ 1)
    (T : IrreducibleCloseds Y) (hT : codimension T = 1) :
    codimension (pre π hc hirr T) = 1 :=
  le_antisymm (hcod T hT) (hT ▸ codimension_le_pre π hc hs hirr T)

include hc hs hirr in
private theorem exists_eq_pre_of_not_dense [IrreducibleSpace Y]
    (W : IrreducibleCloseds X) (hW : codimension W = 1) (hd : ¬ Dense (π '' W)) :
    ∃ T : IrreducibleCloseds Y, codimension T = 1 ∧ (T : Set Y) = closure (π '' W) ∧
      (W : Set X) = π ⁻¹' T := by
  let T : IrreducibleCloseds Y :=
    ⟨closure (π '' W), (W.isIrreducible.image π hc.continuousOn).closure, isClosed_closure⟩
  have hTne : ¬ IsMax T := fun h => hd (dense_iff_closure_eq.mpr ((isMax_iff T).mp h))
  have hpne : ¬ IsMax (pre π hc hirr T) := by
    obtain ⟨U, hU⟩ := not_isMax_iff.mp hTne
    exact not_isMax_of_lt (pre_strictMono π hc hs hirr hU)
  have hle : W ≤ pre π hc hirr T := fun x hx => subset_closure ⟨x, hx, rfl⟩
  have hWeq : W = pre π hc hirr T := by
    by_contra hne
    have hlt : W < pre π hc hirr T := hle.lt_of_ne hne
    have h1 : 1 ≤ codimension (pre π hc hirr T) := (one_le_codimension_iff _).mpr hpne
    have h2 : codimension (pre π hc hirr T) + 1 ≤ codimension W := by
      rw [codimension_eq_coheight, codimension_eq_coheight]
      exact Order.coheight_add_one_le hlt
    rw [hW] at h2
    have : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h1 le_rfl).trans h2
    norm_num at this
  refine ⟨T, le_antisymm ?_ ((one_le_codimension_iff _).mpr hTne), rfl, ?_⟩
  · rw [← hW, hWeq]; exact codimension_le_pre π hc hs hirr T
  · rw [hWeq]; rfl

end Topology

section PrimeDivisor

variable {X : Scheme.{u}}

/-- The closure of the image of the generic point of an integral closed subscheme is its
support. -/
private theorem closure_subschemeι_genericPoint (I : X.IdealSheafData)
    [IsIntegral I.subscheme] :
    closure {I.subschemeι (genericPoint I.subscheme)} = (I.support : Set X) := by
  rw [← Set.image_singleton, I.subschemeι.isClosedEmbedding.closure_image_eq,
    (genericPoint_spec I.subscheme).def, Set.image_univ, Scheme.IdealSheafData.range_subschemeι]

/-- The support of a prime divisor, as an irreducible closed subset. -/
private def supportIC (D : MMP.Mori.PrimeDivisor X) : IrreducibleCloseds X :=
  letI := D.integral
  ⟨D.idealSheaf.support, by
    rw [← closure_subschemeι_genericPoint]; exact isIrreducible_singleton.closure,
    D.idealSheaf.support.isClosed⟩

private theorem codimension_supportIC (D : MMP.Mori.PrimeDivisor X) :
    codimension (supportIC D) = 1 := by
  letI := D.integral
  have := D.codimension_one
  convert this using 2
  ext1
  exact (closure_subschemeι_genericPoint D.idealSheaf).symm

/-- An irreducible closed subset of codimension one is the support of a prime divisor. -/
private theorem exists_primeDivisor (T : IrreducibleCloseds X) (hT : codimension T = 1) :
    ∃ D : MMP.Mori.PrimeDivisor X, (D.idealSheaf.support : Set X) = T := by
  letI := StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible
    (⟨T, T.isClosed⟩ : Closeds X) T.isIrreducible
  refine ⟨⟨Scheme.IdealSheafData.vanishingIdeal ⟨T, T.isClosed⟩, inferInstance, ?_⟩, rfl⟩
  convert hT using 2
  ext1
  exact closure_subschemeι_genericPoint _

end PrimeDivisor

section Line

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsVariety k f]

private theorem surjective_of_nonempty {L : Scheme.{u}} (l : L ⟶ Spec (.of k)) [Nonempty L] :
    Surjective l := by
  refine ⟨fun y => ?_⟩
  obtain ⟨x⟩ := ‹Nonempty L›
  exact ⟨x, Subsingleton.elim _ _⟩

/-- In an integral scheme locally of finite type over a field, an irreducible closed subset of
codimension one has dimension `dim X - 1`; the dimension of `X` is finite. -/
private theorem exists_dim_eq_le_height_add_one (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [IsIntegral X]
    (T : IrreducibleCloseds X) (hT : codimension T = 1) :
    ∃ n : ℕ, topologicalKrullDim X = n ∧ (n : ℕ∞) ≤ Order.height T + 1 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight f
    T.isIrreducible.genericPoint
  rw [← MMP.Flips.codimension_eq_coheight_genericPoint, hT,
    T.isIrreducible.isGenericPoint_genericPoint_closure.def, T.isClosed.closure_eq] at h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, topologicalKrullDim (closure {T.isIrreducible.genericPoint}) = m :=
    ⟨_, Stacks.Chow.topologicalKrullDim_closure_singleton_eq k f T.isIrreducible.genericPoint⟩
  rw [T.isIrreducible.isGenericPoint_genericPoint_closure.def, T.isClosed.closure_eq] at hm
  have h2 := topologicalKrullDim_coe_eq_height T
  rw [hm] at h2 h
  have h3 : (m : ℕ∞) = Order.height T := by exact_mod_cast h2
  refine ⟨m + 1, by rw [← h]; rfl, ?_⟩
  rw [← h3]; norm_cast

/-- The preimage of an irreducible closed subset `T` under the first projection is the image of
an embedding of `G ×_k L`, for `G` the reduced induced subscheme on `T`, a variety with
the same dimension as `T`. -/
private theorem exists_embedding_pullback {L : Scheme.{u}} (l : L ⟶ Spec (.of k))
    (T : IrreducibleCloseds Z) :
    ∃ (G : Scheme.{u}) (g : G ⟶ Spec (.of k)) (_ : IsVariety k g)
      (φ : pullback g l ⟶ pullback f l), Topology.IsEmbedding φ.base ∧
      Set.range φ.base = (pullback.fst f l).base ⁻¹' (T : Set Z) ∧
      topologicalKrullDim G = topologicalKrullDim (T : Set Z) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, T.isClosed⟩ : Closeds Z)
  haveI : IsIntegral I.subscheme :=
    StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _ T.isIrreducible
  have hv : IsVariety k (I.subschemeι ≫ f) :=
    (MMP.Mori.isVariety_iff k _).mpr ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  let e := pullbackRightPullbackFstIso f l I.subschemeι
  have hrange : Set.range (pullback.snd I.subschemeι (pullback.fst f l)).base =
      (pullback.fst f l).base ⁻¹' (T : Set Z) := by
    rw [Scheme.Pullback.range_snd, Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hsurj : Function.Surjective e.inv.base := (inferInstance : Surjective e.inv).surj
  refine ⟨I.subscheme, I.subschemeι ≫ f, hv, e.inv ≫ pullback.snd I.subschemeι (pullback.fst f l),
    (e.inv ≫ pullback.snd I.subschemeι (pullback.fst f l)).isClosedEmbedding.isEmbedding, ?_, ?_⟩
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ,
      hrange]
  · have h := I.subschemeι.isClosedEmbedding.isEmbedding
    rw [(h.toHomeomorph).isHomeomorph.topologicalKrullDim_eq,
      Scheme.IdealSheafData.range_subschemeι]
    rfl

/-- The preimage of an irreducible closed subset under the first projection is irreducible,
provided base change along `l` takes varieties to varieties. -/
private theorem isIrreducible_preimage_fst {L : Scheme.{u}} (l : L ⟶ Spec (.of k))
    (hline : ∀ {W : Scheme.{u}} (g : W ⟶ Spec (.of k)), IsVariety k g →
      IsVariety k (pullback.snd g l ≫ l) ∧
        topologicalKrullDim (pullback g l : Scheme.{u}) = topologicalKrullDim W + 1)
    (T : IrreducibleCloseds Z) :
    IsIrreducible ((pullback.fst f l).base ⁻¹' (T : Set Z)) := by
  obtain ⟨G, g, hv, φ, -, hφ, -⟩ := exists_embedding_pullback f l T
  haveI := (hline _ hv).1.toIsIntegral
  rw [← hφ, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ φ.base.hom.continuous.continuousOn

/-- The preimage of an irreducible closed subset of codimension one under the first projection
has codimension at most one, provided base change along `l` takes varieties to
varieties of one more dimension. -/
private theorem codimension_preimage_fst_le_one {L : Scheme.{u}} (l : L ⟶ Spec (.of k))
    (hline : ∀ {W : Scheme.{u}} (g : W ⟶ Spec (.of k)), IsVariety k g →
      IsVariety k (pullback.snd g l ≫ l) ∧
        topologicalKrullDim (pullback g l : Scheme.{u}) = topologicalKrullDim W + 1)
    (T : IrreducibleCloseds Z) (hT : codimension T = 1) :
    codimension (pre (pullback.fst f l).base (pullback.fst f l).base.hom.continuous
      (isIrreducible_preimage_fst f l hline) T) ≤ 1 := by
  obtain ⟨G, g, hv, φ, hφe, hφ, hG⟩ := exists_embedding_pullback f l T
  obtain ⟨n, hn, hnT⟩ := exists_dim_eq_le_height_add_one Z f T hT
  set W := pre (pullback.fst f l).base (pullback.fst f l).base.hom.continuous
    (isIrreducible_preimage_fst f l hline) T
  have hW : topologicalKrullDim (W : Set (pullback f l : Scheme.{u})) =
      (Order.height T : WithBot ℕ∞) + 1 := by
    have : (W : Set (pullback f l : Scheme.{u})) = Set.range φ.base := hφ.symm
    rw [this, (hφe.toHomeomorph).isHomeomorph.topologicalKrullDim_eq.symm, (hline g hv).2, hG,
      topologicalKrullDim_coe_eq_height]
  have hle := topologicalKrullDim_add_codimension_le W
  rw [hW, (hline f inferInstance).2, hn] at hle
  have hle' : Order.height T + 1 + codimension W ≤ (n : ℕ∞) + 1 := by exact_mod_cast hle
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (show Order.height T ≠ ⊤ by
    intro h; rw [h] at hle'; simp at hle')
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (show codimension W ≠ ⊤ by
    intro h; rw [h] at hle'; simp at hle')
  rw [← hm, ← hc] at hle'
  rw [← hm] at hnT
  rw [← hc]
  have h1 : m + 1 + c ≤ n + 1 := by exact_mod_cast hle'
  have h2 : n ≤ m + 1 := by exact_mod_cast hnT
  exact_mod_cast (show c ≤ 1 by omega)

/-- The affine line over a field has dimension one. -/
private theorem topologicalKrullDim_affineLine :
    topologicalKrullDim (Spec (.of (Polynomial k))) = 1 := by
  change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  rfl

/-- The product of a variety `W` with a smooth geometrically irreducible curve `L` over `k` is a
variety of dimension `dim W + 1`: `L` is geometrically integral, so the product is integral. -/
private theorem isVariety_and_topologicalKrullDim_pullback_line {W L : Scheme.{u}}
    (g : W ⟶ Spec (.of k)) [IsVariety k g] (l : L ⟶ Spec (.of k)) [IsVariety k l] [Smooth l]
    [GeometricallyIrreducible l] (hL : topologicalKrullDim L = 1) :
    IsVariety k (pullback.snd g l ≫ l) ∧
      topologicalKrullDim (pullback g l : Scheme.{u}) = topologicalKrullDim W + 1 := by
  have : GeometricallyReduced l := geometricallyReduced_of_smooth l
  have : GeometricallyIntegral l :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible l
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  exact ⟨{}, by rw [topologicalKrullDim_pullback k g l, hL]⟩

private theorem primeDivisor_pullback_eq_preimage_or_dense_of_isVariety_pullback {L : Scheme.{u}}
    (l : L ⟶ Spec (.of k)) [Nonempty L]
    (hline : ∀ {W : Scheme.{u}} (g : W ⟶ Spec (.of k)), IsVariety k g →
      IsVariety k (pullback.snd g l ≫ l) ∧
        topologicalKrullDim (pullback g l : Scheme.{u}) = topologicalKrullDim W + 1) :
    (∀ Γ : MMP.Mori.PrimeDivisor Z, ∃ D : MMP.Mori.PrimeDivisor (pullback f l),
        (D.idealSheaf.support : Set (pullback f l : Scheme.{u})) =
          (pullback.fst f l).base ⁻¹' (Γ.idealSheaf.support : Set Z)) ∧
      ∀ D : MMP.Mori.PrimeDivisor (pullback f l),
        (∃ Γ : MMP.Mori.PrimeDivisor Z,
          (Γ.idealSheaf.support : Set Z) =
            closure ((pullback.fst f l).base '' (D.idealSheaf.support : Set _)) ∧
          (D.idealSheaf.support : Set (pullback f l : Scheme.{u})) =
            (pullback.fst f l).base ⁻¹' (Γ.idealSheaf.support : Set Z)) ∨
        Dense ((pullback.fst f l).base '' (D.idealSheaf.support : Set _)) := by
  have : Surjective l := surjective_of_nonempty l
  have hs : Function.Surjective (pullback.fst f l).base :=
    (inferInstance : Surjective (pullback.fst f l)).surj
  have hc := (pullback.fst f l).base.hom.continuous
  have hirr := isIrreducible_preimage_fst f l hline
  refine ⟨fun Γ => ?_, fun D => ?_⟩
  · have h1 := codimension_pre_eq_one _ hc hs hirr
      (codimension_preimage_fst_le_one f l hline) (supportIC Γ) (codimension_supportIC Γ)
    obtain ⟨D, hD⟩ := exists_primeDivisor _ h1
    exact ⟨D, hD⟩
  · by_cases hd : Dense ((pullback.fst f l).base '' (D.idealSheaf.support : Set _))
    · exact Or.inr hd
    · obtain ⟨T, hT, hTc, hDT⟩ := exists_eq_pre_of_not_dense _ hc hs hirr (supportIC D)
        (codimension_supportIC D) hd
      obtain ⟨Γ, hΓ⟩ := exists_primeDivisor T hT
      exact Or.inl ⟨Γ, hΓ.trans hTc, hDT.trans (by rw [hΓ])⟩

end Line

end MMP.Internal.IndexbProductPrimeDivisors

namespace MMP

open MMP.Internal.IndexbProductPrimeDivisors in
/-- For a variety `Z` over a field `k` and a smooth geometrically irreducible curve `L` over `k`,
with first projection `pr : Z ×_k L ⟶ Z`: the preimage of every prime divisor of `Z` is a prime
divisor of `Z ×_k L`, and every prime divisor `D` of `Z ×_k L` is either the preimage of the
prime divisor `closure (pr(D))` of `Z`, or has dense image `pr(D)`. -/
public theorem primeDivisor_pullback_eq_preimage_or_dense_of_smooth {k : Type u} [Field k]
    {Z L : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsVariety k f] (l : L ⟶ Spec (.of k))
    [IsVariety k l] [Smooth l] [GeometricallyIrreducible l] (hL : topologicalKrullDim L = 1) :
    (∀ Γ : Mori.PrimeDivisor Z, ∃ D : Mori.PrimeDivisor (pullback f l),
        (D.idealSheaf.support : Set (pullback f l : Scheme.{u})) =
          (pullback.fst f l).base ⁻¹' (Γ.idealSheaf.support : Set Z)) ∧
      ∀ D : Mori.PrimeDivisor (pullback f l),
        (∃ Γ : Mori.PrimeDivisor Z,
          (Γ.idealSheaf.support : Set Z) =
            closure ((pullback.fst f l).base '' (D.idealSheaf.support : Set _)) ∧
          (D.idealSheaf.support : Set (pullback f l : Scheme.{u})) =
            (pullback.fst f l).base ⁻¹' (Γ.idealSheaf.support : Set Z)) ∨
        Dense ((pullback.fst f l).base '' (D.idealSheaf.support : Set _)) :=
  primeDivisor_pullback_eq_preimage_or_dense_of_isVariety_pullback f l fun g _ =>
    isVariety_and_topologicalKrullDim_pullback_line g l hL

open MMP.Internal.IndexbProductPrimeDivisors in
/-- For a variety `Z` over a field `k` and `L` the affine or the projective line, with first
projection `pr : Z ×_k L ⟶ Z`: the preimage of every prime divisor of `Z` is a prime divisor of
`Z ×_k L`; every prime divisor `D` of `Z ×_k L` is either the preimage of the prime divisor
`closure (pr(D))` of `Z`, or has dense image `pr(D)`; and for `L = ℙ¹`, a prime divisor with
dense image surjects onto `Z`. -/
@[mmp "lem_mmp_indexb_product_prime_divisors"]
public theorem primeDivisor_pullback_line_eq_preimage_or_dense
    {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [IsVariety k f] :
    let a : Spec (.of (Polynomial k)) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    let p := projectiveLine k ↘ Spec (.of k)
    let IsGoodLine : ∀ {L : Scheme.{u}} (_ : L ⟶ Spec (.of k)), Prop := fun {L} l =>
      (∀ Γ : Mori.PrimeDivisor Z, ∃ D : Mori.PrimeDivisor (pullback f l),
        (D.idealSheaf.support : Set (pullback f l : Scheme.{u})) =
          (pullback.fst f l).base ⁻¹' (Γ.idealSheaf.support : Set Z)) ∧
      ∀ D : Mori.PrimeDivisor (pullback f l),
        (∃ Γ : Mori.PrimeDivisor Z,
          (Γ.idealSheaf.support : Set Z) =
            closure ((pullback.fst f l).base '' (D.idealSheaf.support : Set _)) ∧
          (D.idealSheaf.support : Set (pullback f l : Scheme.{u})) =
            (pullback.fst f l).base ⁻¹' (Γ.idealSheaf.support : Set Z)) ∨
        Dense ((pullback.fst f l).base '' (D.idealSheaf.support : Set _))
    IsGoodLine a ∧ IsGoodLine p ∧
    ∀ D : Mori.PrimeDivisor (pullback f p),
      Dense ((pullback.fst f p).base '' (D.idealSheaf.support : Set _)) →
        (pullback.fst f p).base '' (D.idealSheaf.support : Set _) = Set.univ := by
  intro a p IsGoodLine
  have : Smooth a := projectiveLineAffineStructureMorphism_smooth k
  have : GeometricallyIrreducible a := Algebra.isGeometricallyIrreducible_polynomial k
  have : IsVariety k a := {}
  have : GeometricallyIrreducible p := geometricallyIrreducible_projectiveLine k
  refine ⟨primeDivisor_pullback_eq_preimage_or_dense_of_smooth f a topologicalKrullDim_affineLine,
    primeDivisor_pullback_eq_preimage_or_dense_of_smooth f p
      (topologicalKrullDim_projectiveLine k), fun D hD => ?_⟩
  have : UniversallyClosed p := projectiveLine_universallyClosed k
  have hcl := ((pullback.fst f p).isClosedMap) _ D.idealSheaf.support.isClosed
  rw [← hcl.closure_eq]
  exact hD.closure_eq

end MMP

end

/-!
# Small threefold programme steps form a sequence of flips

Let `L ∈ {1, 2, …} ∪ {∞}` and let `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k + 1 < L`, be
threefold step diagrams (`MMP.Fourfold.IsThreefoldStepDiagram`) in which every `g_k : V_k ⟶ T_k`
is small and is the contraction of a `(K_{V_k} + Θ_k)`-negative extremal ray `R_k` of `NE̅(V_k)`
spanned by the class of an integral curve. Then the pairs `(V_k, Θ_k)_{k < L}`, with the
morphisms `g_k` and `g_k⁺`, form a sequence of flips for `(V_0, Θ_0)`
(`MMP.Flips.SequenceOfFlips`).

## Main results

* `MMP.Fourfold.exists_sequenceOfFlips_of_isThreefoldStepDiagram`: the sequence of flips.
* `MMP.Fourfold.IsThreefoldStepDiagram.exists_isFlip`: a single small step contracting a
  negative extremal ray spanned by a curve is a flip `(f⁺)⁻¹ ∘ f`, carrying the boundary to its
  strict transform.
* `MMP.Fourfold.IsThreefoldStepDiagram.isNegativeExtremalContraction_of_isContractionOfRay`,
  `MMP.Fourfold.relativePicardNumber_eq_one_of_isContractionOfRay`,
  `MMP.Fourfold.IsSmallMorphism.isSmall`,
  `MMP.Fourfold.IsThreefoldStepDiagram.exists_isModificationOf` and
  `MMP.Fourfold.IsThreefoldStepDiagram.transformDivisor_eq_flipTransform_of_isModificationOf`:
  the ingredients of that flip.
* `MMP.Fourfold.exists_isModificationOf_of_isBirationalMorphism` and
  `MMP.Fourfold.transformDivisor_eq_flipTransform_of_isModificationOf`: the last two for any
  birational `f`, `f⁺` over a separated base, the second when both exceptional sets have
  codimension at least two.

## Implementation notes

The models, canonical divisors, boundaries, bases and morphisms are given for every `k : ℕ` and
constrained only for `k < L` (models) and `k + 1 < L` (steps). The canonical divisors are cut out
by one rational top form: `K_{k+1} = (g_k⁺)⁻¹_* (g_k)_* K_k`, as in
`MMP.Fourfold.IsThreefoldStepDiagram`, and likewise `Θ_{k+1} = (g_k⁺)⁻¹_* (g_k)_* Θ_k`. The
initial pair `(V_0, Θ_0)` is assumed to be a pair on a normal threefold; for `L ≥ 2` this is part
of the first step diagram, for `L = 1` it is what makes `(V_0, Θ_0)` a model at all. The sequence
of flips produced has these models for `k < L`, and these bases, contractions `φ_k = g_k` and
flips `φ_k⁺ = g_k⁺` for `k + 1 < L`; beyond the length the data of the sequence are not those
given, since a sequence of flips carries a rational map `X_k ⤏ X_{k+1}` for every `k`, which need
not exist between the unconstrained `V_k`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.10
-/

section

open CategoryTheory AlgebraicGeometry
open MMP MMP.Fourfold MMP.Mori

namespace MMP.Fourfold.Internal.IndexcSmallStepsAreFaFlips

section Divisors

variable {X Y : Scheme.{0}}

/-- If `L = m D` with `m ≠ 0`, then `D = m⁻¹ L` as `ℝ`-divisors. -/
private theorem toRDivisor_eq_inv_smul {D : QDivisor X} {m : ℤ} (hm : m ≠ 0) {L : Divisor X}
    (hL : Divisor.toQDivisor L = m • D) :
    QDivisor.toRDivisor D = ((m : ℝ)⁻¹) • Divisor.toRDivisor L := by
  ext E
  have h := congrArg (fun D : QDivisor X => D.coeff E) hL
  simp only [Divisor.coeff_toQDivisor] at h
  simp only [QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at h
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp
  rw [mul_comm]
  exact_mod_cast h.symm

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor [IsLocallyNoetherian X] [IsNormal X]
    {D : QDivisor X} (h : D.IsQCartier) : Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
    rw [Fin.sum_univ_one]; exact toRDivisor_eq_inv_smul hm hL⟩

/-- Relative ampleness of an invertible sheaf, checked on an affine open cover of the target,
holds over every affine open of the target. -/
private theorem isRelativelyAmpleCartier_of_isRelativelyAmple [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Y} [QuasiCompact f]
    {L : Divisor X} (hL : L.IsCartier) (h : L.IsRelativelyAmple f hL) :
    Flips.IsRelativelyAmpleCartier f L := by
  have := hL.isInvertibleModule_divisorialSheaf
  exact ⟨hL, fun U hU =>
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance h).2 U hU⟩

/-- A `ℚ`-divisor with an `f`-ample Cartier multiple is `f`-ample as an `ℝ`-divisor. -/
private theorem isRelativelyAmple_toRDivisor [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] {f : X ⟶ Y} [QuasiCompact f] {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) : Flips.IsRelativelyAmple f (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  refine ⟨1, fun _ => ((m : ℤ) : ℝ)⁻¹, fun _ => L, le_rfl, fun _ => by positivity,
    fun _ => isRelativelyAmpleCartier_of_isRelativelyAmple hL hamp, ?_⟩
  rw [Fin.sum_univ_one]
  exact toRDivisor_eq_inv_smul (by exact_mod_cast hm.ne') hLD

private theorem logCanonicalDivisor_eq (K : Divisor X) (B : QDivisor X) :
    Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + B) := by
  rw [Flips.logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {R S : Type*} [AddCommMonoid R]
    [AddCommMonoid S] (φ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y)) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with changing coefficients. -/
private theorem flipTransform_mapCoeffsAddMonoidHom {X' : Scheme.{0}} {R S : Type*}
    [AddCommMonoid R] [AddCommMonoid S] (fm : X ⟶ Y) (fp : X' ⟶ Y) (f : R →+ S)
    (D : DivisorWithCoeffs R X) :
    flipTransform fm fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom f D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom f (flipTransform fm fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

end Divisors

section Transforms

variable {X Y Z : Scheme.{0}}

private theorem isSeparated_toTerminal {s : X ⟶ Spec (.of ℂ)} [IsSeparated s] :
    IsSeparated (X ↘ ⊤_ Scheme) := by
  have : (X ↘ ⊤_ Scheme) = s ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
  rw [this]
  infer_instance

/-- A morphism whose exceptional set has codimension at least two is biregular over the image of
the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus' {f : X ⟶ Y}
    (h2 : 2 ≤ closedsCodimension (exceptionalSet f)) (P : Mori.PrimeDivisor X) :
    f P.genericPoint ∈ biregularLocus f := by
  by_contra h
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 (x := P.genericPoint) h
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- Extending a composite `φ₂ ∘ φ₁` of partial maps on prime divisors linearly is composing the
linear extensions. -/
private theorem mapPrimeDivisors_bind {R : Type*} [AddCommMonoid R]
    (φ₁ : Mori.PrimeDivisor X → Option (Mori.PrimeDivisor Y))
    (φ₂ : Mori.PrimeDivisor Y → Option (Mori.PrimeDivisor Z)) (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors (fun P => (φ₁ P).bind φ₂) D =
      DivisorWithCoeffs.mapPrimeDivisors φ₂ (DivisorWithCoeffs.mapPrimeDivisors φ₁ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    rw [DivisorWithCoeffs.mapPrimeDivisors_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ₁ E with
    | none => simp
    | some E' => simp [DivisorWithCoeffs.mapPrimeDivisors_single]

private theorem coe_transform_eq_closure_singleton [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rw [Scheme.Opens.ι_apply]; exact hq')
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If a representative `g'` of `φ` is defined at `η_P` and `φ_* P = E`, then `g'(η_P) = η_E`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- If a representative `g'` of `φ` sends `η_P` to `η_E`, then `φ_* P = E`. -/
private theorem transformPrimeDivisor_eq_some_of_genericPoint_eq [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ)
    (hP : P.genericPoint ∈ g'.domain) (hE : E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩) :
    Mori.RationalMap.transformPrimeDivisor φ P = some E := by
  refine Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr
    ⟨Mori.RationalMap.definedAt_iff.mpr ⟨g', hP, hg'⟩, ?_⟩
  have h1 : Mori.RationalMap.transform φ P.idealSheaf.support = E.idealSheaf.support := by
    apply SetLike.coe_injective
    rw [coe_transform_eq_closure_singleton g' hg' P hP, ← hE]
    exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure E).symm
  have := E.integral
  rw [Mori.RationalMap.transformIdeal, h1, MMP.Positivity.vanishingIdeal_support_of_isReduced]

/-- Over the biregular locus, a morphism reflects specialization. -/
private theorem specializes_of_map_specializes {f : X ⟶ Y} {x y : X}
    (hx : f x ∈ biregularLocus f) (hy : f y ∈ biregularLocus f) (h : f x ⤳ f y) : x ⤳ y := by
  set V := biregularLocus f
  have : IsIso (f ∣_ V) := isBiregular_biregularLocus f
  let p : (f ⁻¹ᵁ V).toScheme := ⟨x, hx⟩
  let q : (f ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have hp : ((f ∣_ V) ≫ V.ι) p = f x := by rw [morphismRestrict_ι]; rfl
  have hq : ((f ∣_ V) ≫ V.ι) q = f y := by rw [morphismRestrict_ι]; rfl
  have hpq : p ⤳ q := by
    rwa [← ((f ∣_ V) ≫ V.ι).isOpenEmbedding.isInducing.specializes_iff, hp, hq]
  exact hpq.map (f ⁻¹ᵁ V).ι.continuous

/-- If `g` maps `η_E` to `η_D` inside its biregular locus, then `g⁻¹_* D = E`. -/
private theorem inverseTransformPrimeDivisor_eq_some_of_map_genericPoint {g : X ⟶ Y}
    {D : Mori.PrimeDivisor Y} {E : Mori.PrimeDivisor X}
    (hη : g E.genericPoint = D.genericPoint) (hV : g E.genericPoint ∈ biregularLocus g) :
    inverseTransformPrimeDivisor g D = some E := by
  have hDmem : D.genericPoint ∈ D.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have hEmem : E.genericPoint ∈ (g ⁻¹' ((D.idealSheaf.support : Set Y) ∩ biregularLocus g)) :=
    ⟨hη ▸ hDmem, hV⟩
  have hsupp : E.idealSheaf.support = inverseTransform g D.idealSheaf.support := by
    apply TopologicalSpace.Closeds.ext
    change (E.support : Set X) = closure _
    apply subset_antisymm
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact closure_mono (Set.singleton_subset_iff.mpr hEmem)
    · rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_minimal ?_ isClosed_closure
      rintro w ⟨hwD, hwV⟩
      have hDw : D.genericPoint ⤳ g w := by
        have : g w ∈ D.support := hwD
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
        exact specializes_iff_mem_closure.mpr this
      rw [← hη] at hDw
      exact specializes_iff_mem_closure.mp
        (specializes_of_map_specializes hV hwV hDw)
  refine inverseTransformPrimeDivisor_eq_some_iff.mpr ⟨⟨D.genericPoint, hDmem, hη ▸ hV⟩, ?_⟩
  have := E.integral
  exact Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ hsupp

/-- A representative `ψ` of a rational map `φ` over `f` and `g` satisfies `ψ ≫ g = f`. -/
private theorem hom_comp_eq_of_isOver [IsReduced X] [IsSeparated (Z ↘ ⊤_ Scheme)]
    {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y} (hφ : Flips.RationalMap.IsOver f g φ)
    (ψ : X.PartialMap Y) (hψ : ψ.toRationalMap = φ) : ψ.hom ≫ g = ψ.domain.ι ≫ f := by
  have h1 : (ψ.compHom g).toRationalMap = f.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hψ]
    exact hφ
  exact (Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp h1)

private theorem hom_apply_eq_of_comp_eq {ψ : X.PartialMap Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : ψ.hom ≫ g = ψ.domain.ι ≫ f) (x : ψ.domain) : g (ψ.hom x) = f x.1 :=
  congrArg (fun k : ψ.domain.toScheme ⟶ Z => k x) h

/-- Two morphisms with the same composite with `g`, both landing over the biregular locus of `g`,
are equal. -/
private theorem eq_of_comp_eq_of_mem_biregularLocus {W : Scheme.{0}} (g : Y ⟶ Z) {a b : W ⟶ Y}
    {h : W ⟶ Z} (ha' : a ≫ g = h) (hb' : b ≫ g = h) (hh : ∀ w, h w ∈ biregularLocus g) :
    a = b := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  have hab : a ≫ g = b ≫ g := ha'.trans hb'.symm
  have ha : ∀ w, g (a w) ∈ biregularLocus g := fun w => by
    rw [← Scheme.Hom.comp_apply, ha']; exact hh w
  have hb : ∀ w, g (b w) ∈ biregularLocus g := fun w => by
    rw [← Scheme.Hom.comp_apply, hb']; exact hh w
  have hra : Set.range a ⊆ Set.range (g ⁻¹ᵁ biregularLocus g).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ha w
  have hrb : Set.range b ⊆ Set.range (g ⁻¹ᵁ biregularLocus g).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hb w
  rw [← IsOpenImmersion.lift_fac (g ⁻¹ᵁ biregularLocus g).ι a hra,
    ← IsOpenImmersion.lift_fac (g ⁻¹ᵁ biregularLocus g).ι b hrb]
  congr 1
  rw [← cancel_mono (g ∣_ biregularLocus g), ← cancel_mono (biregularLocus g).ι]
  simp only [Category.assoc, morphismRestrict_ι]
  rw [IsOpenImmersion.lift_fac_assoc, IsOpenImmersion.lift_fac_assoc, hab]

/-- The partial map `g⁻¹ ∘ f`, defined on `f⁻¹(V_g)` for the biregular locus `V_g` of `g`. -/
private noncomputable def partialMapOverBiregularLocus [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty) :
    X.PartialMap Y where
  domain := f ⁻¹ᵁ biregularLocus g
  dense_domain := (f ⁻¹ᵁ biregularLocus g).2.dense hne
  hom := haveI : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
    (f ∣_ biregularLocus g) ≫ inv (g ∣_ biregularLocus g) ≫ (g ⁻¹ᵁ biregularLocus g).ι

private theorem partialMapOverBiregularLocus_hom_comp [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty) :
    (partialMapOverBiregularLocus f g hne).hom ≫ g =
      (partialMapOverBiregularLocus f g hne).domain.ι ≫ f := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  change ((f ∣_ biregularLocus g) ≫ inv (g ∣_ biregularLocus g) ≫
    (g ⁻¹ᵁ biregularLocus g).ι) ≫ g = (f ⁻¹ᵁ biregularLocus g).ι ≫ f
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc,
    morphismRestrict_ι]

private theorem partialMapOverBiregularLocus_hom_mem [IrreducibleSpace X] (f : X ⟶ Z)
    (g : Y ⟶ Z) (hne : ((f ⁻¹ᵁ biregularLocus g : X.Opens) : Set X).Nonempty)
    (x : (partialMapOverBiregularLocus f g hne).domain) :
    (partialMapOverBiregularLocus f g hne).hom x ∈ g ⁻¹ᵁ biregularLocus g := by
  have : IsIso (g ∣_ biregularLocus g) := isBiregular_biregularLocus g
  exact (inv (g ∣_ biregularLocus g) ((f ∣_ biregularLocus g) x)).2

end Transforms

end MMP.Fourfold.Internal.IndexcSmallStepsAreFaFlips

namespace MMP.Fourfold

open MMP.Fourfold.Internal.IndexcSmallStepsAreFaFlips

section General

variable {X Z X' : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
  {sX' : X' ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- Two birational morphisms `f : X ⟶ Z` and `f⁺ : X' ⟶ Z` from reduced schemes to a separated
`ℂ`-scheme `Z` admit a modification `φ : X ⤏ X'` of `f` into `f⁺` (namely `(f⁺)⁻¹ ∘ f`). -/
public theorem exists_isModificationOf_of_isBirationalMorphism [IsReduced X] [IsReduced X']
    [IsSeparated sZ] (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) :
    ∃ φ : X.RationalMap X', Flips.IsModificationOf f fp φ := by
  obtain ⟨em, hm⟩ := hf
  obtain ⟨ep, hp⟩ := hfp
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 Z) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 Z) hp
  simp only [Category.comp_id] at h1 h2
  set e := em.trans ep.symm
  have H : e.IsOver f fp := h1.trans h2.symm
  refine ⟨e.toRationalMap, ⟨e, rfl⟩, ?_⟩
  rw [Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, H]
  simp

/-- If `f : X ⟶ Z` and `f⁺ : X' ⟶ Z` have exceptional sets of codimension at least two, with `Z`
and `X'` separated, the birational transform of divisors under a modification `φ` of `f` into
`f⁺` is the strict transform `(f⁺)⁻¹_* f_*`: both send a prime divisor `P` to the prime divisor
of `X'` over the image of the generic point of `P`, when `f⁺` is biregular there, and to `0`
otherwise. -/
public theorem transformDivisor_eq_flipTransform_of_isModificationOf [IsIntegral X]
    [IsSeparated sZ] [IsSeparated sX'] (hf : 2 ≤ closedsCodimension (exceptionalSet f))
    (hfp : 2 ≤ closedsCodimension (exceptionalSet fp)) {φ : X.RationalMap X'}
    (hφ : Flips.IsModificationOf f fp φ) {R : Type} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    Mori.RationalMap.transformDivisor φ D = flipTransform f fp D := by
  have : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sZ)
  have : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal (s := sX')
  have hpt : ∀ P : Mori.PrimeDivisor X, Mori.RationalMap.transformPrimeDivisor φ P =
      (Mori.RationalMap.transformPrimeDivisor (X := X) f.toRationalMap P).bind
        (inverseTransformPrimeDivisor fp) := by
    intro P
    have hcoh : Order.coheight (f P.genericPoint) = 1 := by
      rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f
        (map_genericPoint_mem_biregularLocus' hf P),
        P.coheight_genericPoint]
    set Q : Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
    have hQ : f P.genericPoint = Q.genericPoint :=
      (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hQ,
      Option.bind_some]
    by_cases hV : Q.genericPoint ∈ biregularLocus fp
    · have hPU : P.genericPoint ∈ f ⁻¹ᵁ biregularLocus fp :=
        show f P.genericPoint ∈ biregularLocus fp from hQ ▸ hV
      set g' := partialMapOverBiregularLocus f fp ⟨_, hPU⟩
      have hg' : g'.toRationalMap = φ := by
        obtain ⟨ψ, rfl⟩ := Scheme.PartialMap.toRationalMap_surjective φ
        have hψ := hom_comp_eq_of_isOver hφ.2 ψ rfl
        have hg := partialMapOverBiregularLocus_hom_comp f fp ⟨_, hPU⟩
        rw [Scheme.PartialMap.toRationalMap_eq_iff]
        refine ⟨g'.domain ⊓ ψ.domain,
          g'.dense_domain.inter_of_isOpen_left ψ.dense_domain g'.domain.2, inf_le_left,
          inf_le_right, ?_⟩
        have key : ∀ (U : X.Opens) (hWU : g'.domain ⊓ ψ.domain ≤ U) (c : U.toScheme ⟶ X'),
            c ≫ fp = U.ι ≫ f → (X.homOfLE hWU ≫ c) ≫ fp = (g'.domain ⊓ ψ.domain).ι ≫ f :=
          fun U hWU c hc => by rw [Category.assoc, hc, Scheme.homOfLE_ι_assoc]
        refine eq_of_comp_eq_of_mem_biregularLocus fp (key _ inf_le_left _ hg)
          (key _ inf_le_right _ hψ) fun w => w.2.1
      set y := g'.hom ⟨P.genericPoint, hPU⟩
      have hyQ : fp y = Q.genericPoint :=
        (hom_apply_eq_of_comp_eq (partialMapOverBiregularLocus_hom_comp f fp ⟨_, hPU⟩)
          ⟨P.genericPoint, hPU⟩).trans hQ
      have hyV : y ∈ fp ⁻¹ᵁ biregularLocus fp := partialMapOverBiregularLocus_hom_mem _ _ _ _
      have hcy : Order.coheight y = 1 := by
        rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp hyV, hyQ,
          Q.coheight_genericPoint]
      set P' : Mori.PrimeDivisor X' := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcy
      have hP' : y = P'.genericPoint :=
        (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcy).symm
      rw [inverseTransformPrimeDivisor_eq_some_of_map_genericPoint (E := P') (hP' ▸ hyQ)
        (hP' ▸ hyV)]
      exact transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hPU hP'.symm
    · have hnone : inverseTransformPrimeDivisor fp Q = none := by
        rw [inverseTransformPrimeDivisor_eq_none_iff]
        rintro ⟨⟨z, hzQ, hzV⟩, -⟩
        have hz : Q.genericPoint ⤳ z := by
          have : z ∈ Q.support := hzQ
          rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
          exact specializes_iff_mem_closure.mpr this
        exact hV (hz.mem_open (biregularLocus fp).2 hzV)
      rw [hnone, Mori.RationalMap.transformPrimeDivisor_eq_none_iff]
      rintro ⟨hdef, E, hE⟩
      have hsome : Mori.RationalMap.transformPrimeDivisor φ P = some E :=
        Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mpr ⟨hdef, hE⟩
      obtain ⟨ψ, hPψ, hψ⟩ := Mori.RationalMap.definedAt_iff.mp hdef
      have hηE := genericPoint_eq_of_transformPrimeDivisor_eq_some hsome ψ hψ hPψ
      have h1 : fp E.genericPoint = Q.genericPoint := by
        rw [hηE]
        exact (hom_apply_eq_of_comp_eq (hom_comp_eq_of_isOver hφ.2 ψ hψ)
          ⟨P.genericPoint, hPψ⟩).trans hQ
      exact hV (h1 ▸ map_genericPoint_mem_biregularLocus' hfp E)
  change DivisorWithCoeffs.mapPrimeDivisors _ D = inverseTransformDivisor fp
    (Mori.RationalMap.transformDivisor (X := X) f.toRationalMap D)
  rw [funext hpt]
  exact mapPrimeDivisors_bind _ _ D

end General

section Step

variable {Xm Xp Z : Scheme.{0}} [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm]
  [IsNormal Xm] [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
  {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
  {K : Divisor Xm} {B : QDivisor Xm} {fm : Xm ⟶ Z} {fp : Xp ⟶ Z}
  {R : Set (NumericalCurveClasses sXm)}

/-- The contraction of a negative extremal ray spanned by the class of an integral curve `C₀`
has relative Picard number one: `N ↦ N · C₀` identifies `N¹(X/Z)` with `ℝ`. -/
public theorem relativePicardNumber_eq_one_of_isContractionOfRay
    (hneg : IsNegativeExtremalRayOf sXm (Divisor.toQDivisor K + B) R)
    (hspan : ∃ C : ProperCurve sXm,
      R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u})
    (hcontr : IsContractionOfRay sXm sZ R fm) :
    Flips.relativePicardNumber sXm fm = 1 := by
  obtain ⟨C₀, rfl⟩ := hspan
  obtain ⟨-, ⟨-, v, hv, hRv⟩, -⟩ := hneg
  have hC₀R : OneCycle.numericalClass sXm (C₀.cycle ℝ) ∈
      {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C₀.cycle ℝ) = u} :=
    ⟨1, zero_le_one, one_smul _ _⟩
  have hne : OneCycle.numericalClass sXm (C₀.cycle ℝ) ≠ 0 := by
    intro h0
    have hvR : v ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := ⟨1, zero_le_one, one_smul _ _⟩
    rw [← hRv] at hvR
    obtain ⟨c, -, hc⟩ := hvR
    rw [h0, smul_zero] at hc
    exact hv hc.symm
  have hC₀ : C₀.IsContractedBy fm := (hcontr.isContractedBy_iff C₀).mpr hC₀R
  let φ : KCartierDivisor ℝ Xm →ₗ[ℝ] ℝ :=
    (OneCycle.intersectionPairing (sX := sXm)).flip (C₀.cycle ℝ)
  have hφ : ∀ D, φ D = (C₀.cycle ℝ).intersectionNumber D := fun _ => rfl
  have hker : LinearMap.ker φ = Flips.relativeNumericallyTrivialDivisors sXm fm := by
    ext D
    rw [LinearMap.mem_ker, Flips.mem_relativeNumericallyTrivialDivisors, hφ]
    refine ⟨fun hD C hC => ?_, fun h => h C₀ hC₀⟩
    obtain ⟨c, -, hc⟩ := (hcontr.isContractedBy_iff C).mp hC
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, ← hc, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, hD, smul_zero]
  have hsurj : Function.Surjective φ := by
    obtain ⟨L, _, hL⟩ : ∃ (L : Xm.Modules) (_ : SheafOfModules.IsInvertible Xm.presheaf
        Xm.ringCatSheaf.2 L), OneCycle.degree ℝ sXm L (C₀.cycle ℝ) ≠ 0 := by
      by_contra h
      push Not at h
      exact hne ((Submodule.Quotient.mk_eq_zero _).mpr
        (OneCycle.mem_numericallyTrivial.mpr fun L _ => h L inferInstance))
    obtain ⟨E, ⟨e⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L
    have hE : φ (KCartierDivisor.ofCartier ℝ E) ≠ 0 := by
      rw [hφ, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
        OneCycle.degree_cycle]
      rw [OneCycle.degree_cycle] at hL
      unfold ProperCurve.degree at hL ⊢
      rwa [← degreeOn_eq_of_iso ℂ sXm C₀.ι C₀.dim_le e]
    intro r
    exact ⟨(r / φ (KCartierDivisor.ofCartier ℝ E)) • KCartierDivisor.ofCartier ℝ E, by
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hE]⟩
  rw [Flips.relativePicardNumber,
    ((Submodule.quotEquivOfEq _ _ hker.symm).trans
      (φ.quotKerEquivOfSurjective hsurj)).rank_eq, Module.rank_self]
  simp

omit [IsIntegral Xp] in
/-- The negative side of a step diagram contracting a negative extremal ray spanned by an
integral curve is a `(K + B)`-negative extremal contraction. -/
public theorem IsThreefoldStepDiagram.isNegativeExtremalContraction_of_isContractionOfRay
    (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hneg : IsNegativeExtremalRayOf sXm (Divisor.toQDivisor K + B) R)
    (hspan : ∃ C : ProperCurve sXm,
      R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u})
    (hcontr : IsContractionOfRay sXm sZ R fm) :
    Flips.IsNegativeExtremalContraction ℂ sXm sZ
      (Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) fm := by
  have := isProper_of_isProjectiveMorphism fm hD.isProjectiveMorphism_minus
  rw [logCanonicalDivisor_eq]
  exact
    { isNormalVariety_source := hD.isNormalVariety_minus
      isNormalVariety_target := hD.isNormalVariety_target
      isCartierCombination := isCartierCombination_toRDivisor hD.isQCartier_minus
      isContraction :=
        { isVariety_target := hD.isNormalVariety_target.1
          isVariety_source := hD.isNormalVariety_minus.1
          comp_eq := hD.comp_eq_minus
          isProper := inferInstance
          isIso_app := hD.isIso_app_minus }
      isRelativelyAntiAmple := by
        rw [Flips.IsRelativelyAntiAmple, ← map_neg]
        exact isRelativelyAmple_toRDivisor hD.hasRelativelyAmpleMultiple_minus
      relativePicardNumber_eq_one :=
        relativePicardNumber_eq_one_of_isContractionOfRay hneg hspan hcontr }

/-- A small morphism (exceptional set of codimension `≥ 2`) with `𝒪_Z ≅ f_* 𝒪_X` is a small
birational contraction. -/
public theorem IsSmallMorphism.isSmall {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    (happ : ∀ U : Z.Opens, IsIso (f.app U)) : Flips.IsSmall ℂ sZ sX f := by
  have := hf.isNormalVariety_target.2
  have := hf.isProper
  have := hf.isNormalVariety_source.1
  have := hf.isNormalVariety_target.1
  have hbc : Flips.IsBirationalContraction ℂ sZ sX f :=
    { isVariety_target := hf.isNormalVariety_target.1
      isVariety_source := hf.isNormalVariety_source.1
      comp_eq := hf.comp_eq
      isProper := hf.isProper
      isIso_app := happ
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX
        hf.isBirationalMorphism).symm }
  refine (Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
  have h := hf.two_le_codimension
  rw [Flips.le_closedsCodimension_iff_le_coheight] at h ⊢
  intro x hx
  refine h x fun hx' => hx ⟨f ⁻¹ᵁ biregularLocus f, by simpa [exceptionalSet] using hx', ?_⟩
  have : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  rw [← morphismRestrict_ι]
  infer_instance

omit [IsIntegral Xm] [IsIntegral Xp] in
/-- A step diagram admits a modification `φ` of `f` into `f⁺` (the birational map
`(f⁺)⁻¹ ∘ f`). -/
public theorem IsThreefoldStepDiagram.exists_isModificationOf
    (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) :
    ∃ φ : Xm.RationalMap Xp, Flips.IsModificationOf fm fp φ := by
  have : IsSeparated sZ := hD.isProjectiveVariety_target.1.toIsSeparated
  exact exists_isModificationOf_of_isBirationalMorphism (sZ := sZ)
    hD.isBirationalMorphism_minus hD.isSmallMorphism_plus.isBirationalMorphism

omit [IsIntegral Xp] in
/-- For a step diagram with small `f`, the birational transform of divisors under a modification
`φ` of `f` into `f⁺` is the strict transform `(f⁺)⁻¹_* f_*`. -/
public theorem IsThreefoldStepDiagram.transformDivisor_eq_flipTransform_of_isModificationOf
    (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp) (hsmall : IsSmallMorphism sXm sZ fm)
    {φ : Xm.RationalMap Xp} (hφ : Flips.IsModificationOf fm fp φ)
    {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R Xm) :
    Mori.RationalMap.transformDivisor φ D = flipTransform fm fp D := by
  have : IsSeparated sZ := hD.isProjectiveVariety_target.1.toIsSeparated
  have : IsSeparated sXp := hD.isNormalVariety_plus.1.toIsSeparated
  exact MMP.Fourfold.transformDivisor_eq_flipTransform_of_isModificationOf (sZ := sZ)
    (sX' := sXp) hsmall.two_le_codimension hD.isSmallMorphism_plus.two_le_codimension hφ D

omit [IsIntegral Xp] in
/-- A step diagram with small `f`, contracting a `(K + B)`-negative extremal ray spanned by a
curve, admits a flip `φ` of `f` with respect to `K + B` (the map `(f⁺)⁻¹ ∘ f`) carrying `B` to its
strict transform. -/
public theorem IsThreefoldStepDiagram.exists_isFlip
    (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hsmall : IsSmallMorphism sXm sZ fm)
    (hneg : IsNegativeExtremalRayOf sXm (Divisor.toQDivisor K + B) R)
    (hspan : ∃ C : ProperCurve sXm,
      R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u})
    (hcontr : IsContractionOfRay sXm sZ R fm) :
    ∃ φ : Xm.RationalMap Xp,
      Flips.IsFlip ℂ sXm sZ sXp (Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) fm fp φ ∧
        flipTransform fm fp B = Mori.RationalMap.transformDivisor φ B := by
  obtain ⟨φ, hmod⟩ := hD.exists_isModificationOf
  have hE := hD.isNegativeExtremalContraction_of_isContractionOfRay hneg hspan hcontr
  have := hD.isSmallMorphism_plus.isProper
  have htrE : Mori.RationalMap.transformDivisor φ
      (Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) =
        QDivisor.toRDivisor
          (Divisor.toQDivisor (flipTransform fm fp K) + flipTransform fm fp B) := by
    rw [hD.transformDivisor_eq_flipTransform_of_isModificationOf hsmall hmod,
      logCanonicalDivisor_eq, map_add, map_add]
    simp only [QDivisor.toRDivisor, Divisor.toQDivisor, flipTransform_mapCoeffsAddMonoidHom]
    exact (map_add _ _ _).symm
  refine ⟨φ,
    { isNormalVariety_source := hD.isNormalVariety_minus
      isNormalVariety_target := hD.isNormalVariety_target
      isNormalVariety_flip := hD.isNormalVariety_plus
      isContraction := hE.isContraction
      isCartierCombination := hE.isCartierCombination
      isRelativelyAntiAmple := hE.isRelativelyAntiAmple
      isProper := inferInstance
      isModificationOf := hmod
      isMorphismInCodimOne :=
        Flips.RationalMap.isMorphismInCodimOne_of_isOver hD.isNormalVariety_minus fm fp φ hmod.2
      isSmall := hD.isSmallMorphism_plus.isSmall hD.isIso_app_plus
      isCartierCombination_transform := by
        rw [htrE]; exact isCartierCombination_toRDivisor hD.isQCartier_plus
      isRelativelyAmple_transform := by
        rw [htrE]; exact isRelativelyAmple_toRDivisor hD.hasRelativelyAmpleMultiple_plus
      isSmall_source := hsmall.isSmall hD.isIso_app_minus },
    (hD.transformDivisor_eq_flipTransform_of_isModificationOf hsmall hmod B).symm⟩

end Step

end MMP.Fourfold

namespace MMP.Fourfold.Internal.IndexcSmallStepsAreFaFlips

/-- The clamping index: `ι k = k` below the length, and constant from the last index on. -/
private theorem exists_clamp (L : ℕ∞) (hL : 1 ≤ L) :
    ∃ ι : ℕ → ℕ, (∀ k : ℕ, (k : ℕ∞) < L → ι k = k) ∧
      (∀ k : ℕ, ¬ ((k + 1 : ℕ) : ℕ∞) < L → ι (k + 1) = ι k) := by
  classical
  refine ⟨fun k => if (k : ℕ∞) < L then k else L.toNat - 1, fun k hk => by simp [hk], ?_⟩
  intro k hk
  have hLtop : L ≠ ⊤ := fun h => hk (h ▸ ENat.natCast_lt_top _)
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hLtop
  simp only [Nat.cast_lt, not_lt] at hk ⊢
  simp only [ENat.toNat_natCast]
  split_ifs <;> omega

end MMP.Fourfold.Internal.IndexcSmallStepsAreFaFlips

namespace MMP.Fourfold

open MMP.Fourfold.Internal.IndexcSmallStepsAreFaFlips in
/-- Threefold step diagrams `(V_k, Θ_k) → T_k ← (V_{k+1}, Θ_{k+1})`, `k + 1 < L`, whose negative
sides `g_k` are small contractions of `(K_{V_k} + Θ_k)`-negative extremal rays `R_k` of
`NE̅(V_k)` spanned by integral curves, form a sequence of flips for `(V_0, Θ_0)` of length `L`,
with models `(V_k, Θ_k)`, contractions `g_k` and flips `g_k⁺`. -/
@[mmp "lem_mmp_indexc_small_steps_are_fa_flips"]
public theorem exists_sequenceOfFlips_of_isThreefoldStepDiagram
    (L : ℕ∞) (hL : 1 ≤ L)
    (V : ℕ → Scheme.{0}) (sV : ∀ k, V k ⟶ Spec (.of ℂ))
    [∀ k, IsIntegral (V k)] [∀ k, CompactSpace (V k)] [∀ k, IsLocallyNoetherian (V k)]
    [∀ k, IsNormal (V k)]
    (K : ∀ k, Divisor (V k)) (Θ : ∀ k, QDivisor (V k))
    (T : ℕ → Scheme.{0}) (sT : ∀ k, T k ⟶ Spec (.of ℂ))
    (g : ∀ k, V k ⟶ T k) (gp : ∀ k, V (k + 1) ⟶ T k)
    (R : ∀ k, Set (NumericalCurveClasses (sV k)))
    (h₀ : IsNormalVariety ℂ (sV 0) ∧ (K 0).IsCanonicalDivisor (sV 0) 3 ∧
      (Divisor.toQDivisor (K 0) + Θ 0).IsQCartier)
    (hstep : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L →
      IsThreefoldStepDiagram (sV k) (sT k) (sV (k + 1)) (K k) (Θ k) (g k) (gp k))
    (K_eq : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L → K (k + 1) = flipTransform (g k) (gp k) (K k))
    (Θ_eq : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L → Θ (k + 1) = flipTransform (g k) (gp k) (Θ k))
    (hsmall : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L → IsSmallMorphism (sV k) (sT k) (g k))
    (hneg : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L →
      IsNegativeExtremalRayOf (sV k) (Divisor.toQDivisor (K k) + Θ k) (R k))
    (hspan : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L → ∃ C : ProperCurve (sV k),
      R k = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u})
    (hcontr : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L → IsContractionOfRay (sV k) (sT k) (R k) (g k)) :
    ∃ S : Flips.SequenceOfFlips (sV 0) 3 (K 0) (Θ 0),
      S.length = L ∧ (∀ k : ℕ, (k : ℕ∞) < L → S.model k = ⟨V k, sV k, K k, Θ k⟩) ∧
        ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L → S.base k = T k ∧ HEq (S.baseStr k) (sT k) ∧
          HEq (S.contraction k) (g k) ∧ HEq (S.flip k) (gp k) := by
  obtain ⟨ι, hι, hιsucc⟩ := exists_clamp L hL
  have hlt : ∀ k : ℕ, ((k + 1 : ℕ) : ℕ∞) < L → (k : ℕ∞) < L := fun k hk =>
    lt_of_le_of_lt (by exact_mod_cast k.le_succ) hk
  have step : ∀ i : ℕ, ∃ (Z : Scheme.{0}) (sZ : Z ⟶ Spec (.of ℂ)) (c : V (ι i) ⟶ Z)
      (f : V (ι (i + 1)) ⟶ Z) (φ : (V (ι i)).RationalMap (V (ι (i + 1)))),
      ((i + 1 : ℕ) : ℕ∞) < L →
        (Flips.IsNegativeExtremalContraction ℂ (sV (ι i)) sZ
            (Flips.logCanonicalDivisor (K (ι i)) (QDivisor.toRDivisor (Θ (ι i)))) c ∧
          Flips.IsSmall ℂ sZ (sV (ι i)) c ∧
          Flips.IsFlip ℂ (sV (ι i)) sZ (sV (ι (i + 1)))
            (Flips.logCanonicalDivisor (K (ι i)) (QDivisor.toRDivisor (Θ (ι i)))) c f φ ∧
          Θ (ι (i + 1)) = Mori.RationalMap.transformDivisor φ (Θ (ι i))) ∧
        Z = T i ∧ HEq sZ (sT i) ∧ HEq c (g i) ∧ HEq f (gp i) := by
    intro i
    by_cases h : ((i + 1 : ℕ) : ℕ∞) < L
    · rw [hι i (hlt i h), hι (i + 1) h]
      obtain ⟨φ, hφ, hφΘ⟩ := (hstep i h).exists_isFlip (hsmall i h) (hneg i h) (hspan i h)
        (hcontr i h)
      exact ⟨T i, sT i, g i, gp i, φ, fun _ =>
        ⟨⟨(hstep i h).isNegativeExtremalContraction_of_isContractionOfRay (hneg i h)
            (hspan i h) (hcontr i h),
          (hsmall i h).isSmall (hstep i h).isIso_app_minus, hφ,
          (Θ_eq i h).trans hφΘ⟩,
          rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩⟩
    · rw [hιsucc i h]
      exact ⟨V (ι i), sV (ι i), 𝟙 _, 𝟙 _, Scheme.Hom.toRationalMap (𝟙 (V (ι i))),
        fun h' => absurd h' h⟩
  choose Z sZ c f φ hφ using step
  have hmodel : ∀ k : ℕ, (k : ℕ∞) < L →
      (⟨V (ι k), sV (ι k), K (ι k), Θ (ι k)⟩ : Flips.FlipModel ℂ) = ⟨V k, sV k, K k, Θ k⟩ := by
    intro k hk
    rw [hι k hk]
  have h0 : ((0 : ℕ) : ℕ∞) < L := lt_of_lt_of_le (by simp) hL
  refine ⟨{
    isNormalVariety := h₀.1
    isCanonicalDivisor := ⟨inferInstance, inferInstance, h₀.2.1⟩
    isQCartier := ⟨inferInstance, inferInstance, h₀.2.2⟩
    length := L
    one_le_length := hL
    model := fun k => ⟨V (ι k), sV (ι k), K (ι k), Θ (ι k)⟩
    model_zero := hmodel 0 h0
    isNormalVariety_model := fun i hi => ?_
    isLocallyNoetherian_model := fun _ => inferInstance
    isNormal_model := fun _ => inferInstance
    compactSpace_model := fun _ => inferInstance
    isCanonicalDivisor_model := fun i hi => ?_
    base := Z
    baseStr := sZ
    contraction := c
    flip := f
    flipMap := φ
    isNegativeExtremalContraction := fun i hi => (hφ i hi).1.1
    isSmall := fun i hi => (hφ i hi).1.2.1
    isFlip := fun i hi => (hφ i hi).1.2.2.1
    transform_eq := fun i hi => (hφ i hi).1.2.2.2 }, rfl, hmodel, fun k hk => (hφ k hk).2⟩
  · change IsNormalVariety ℂ (sV (ι i))
    rw [hι i hi]
    rcases i with _ | j
    · exact h₀.1
    · exact (hstep j hi).isNormalVariety_plus
  · change (K (ι i)).IsCanonicalDivisor (sV (ι i)) 3
    rw [hι i hi]
    rcases i with _ | j
    · exact h₀.2.1
    · obtain ⟨m, hm⟩ := (hstep j hi).isCanonicalDivisor_plus
      rw [← K_eq j hi] at hm
      have hdim := hm.topologicalKrullDim_eq
      rw [(hstep j hi).dim_plus] at hdim
      have hm3 : m = 3 := by exact_mod_cast hdim.symm
      exact hm3 ▸ hm

end MMP.Fourfold

end

/-!
# A reduced curve has finitely many singular points

Let `k` be a field and `X` a reduced scheme of finite type over `k` all of whose irreducible
components have dimension one. Then only finitely many points `x` of `X` have a local ring
`𝒪_{X,x}` which is not regular. The regular locus is open (schemes of finite type over a field are
excellent), it contains every generic point of an irreducible component (the local ring there is
a reduced Artinian local ring, hence a field), so its complement is a closed subset of dimension
zero of a Noetherian space, hence finite. No perfectness of `k` is needed.

## Main results

* `MMP.finite_setOf_not_isRegularLocalRing_stalk`: the set of nonregular points is finite.

## Implementation notes

A point `x` is regular when `IsRegularLocalRing (X.presheaf.stalk x)`. "Finite type over `k`" is
`LocallyOfFiniteType f` together with `QuasiCompact f` for the structure morphism
`f : X ⟶ Spec k`; pure dimension one says that every `Z ∈ irreducibleComponents X` has
`topologicalKrullDim Z = 1`.

## References

* [Stacks, Tag 07P7], [Stacks, Tag 07QW]
* [Kollár, *Lectures on resolution of singularities*]
-/

section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Internal.ResolutionCurveSingularPointsFinite

/-- On a reduced locally Noetherian scheme whose irreducible components have dimension at most
one, a nonregular point is closed: a proper specialization `z ⤳ y` of it, together with the
(regular) generic point `w` of a component through `z`, would give a chain `w ⤳ z ⤳ y` of
distinct points in that component. -/
private lemma isClosed_singleton_of_not_isRegularLocalRing {X : Scheme.{u}} [IsReduced X]
    [IsLocallyNoetherian X] (hdim : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z ≤ 1)
    {z : X} (hz : ¬ IsRegularLocalRing (X.presheaf.stalk z)) : IsClosed ({z} : Set X) := by
  refine closure_subset_iff_isClosed.mp fun y hy => ?_
  by_contra hne
  obtain ⟨W, hW, hzW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := z)).closure
  obtain ⟨w, hw⟩ := QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)
  have hwz : w ≠ z := fun h => hz <| h ▸ MMP.Flips.isRegularLocalRing_of_isField
    (isField_stalk_of_closure_mem_irreducibleComponents X w (hw.def ▸ hW))
  have hzW' := hzW (subset_closure rfl)
  have h2 := MMP.Flips.two_le_topologicalKrullDim_of_specializes hw.mem hzW' (hzW hy)
    (hw.specializes hzW') (specializes_iff_mem_closure.mpr hy) hwz (Ne.symm hne)
  exact absurd (h2.trans (hdim W hW)) (by decide)

end MMP.Internal.ResolutionCurveSingularPointsFinite

namespace MMP

open MMP.Internal.ResolutionCurveSingularPointsFinite in
/-- A reduced scheme of finite type over a field, of pure dimension one, has only finitely many
points whose local ring is not regular. -/
@[mmp "lem_mmp_resolution_curve_singular_points_finite"]
public theorem finite_setOf_not_isRegularLocalRing_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X]
    (hdim : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = 1) :
    {x : X | ¬ IsRegularLocalRing (X.presheaf.stalk x)}.Finite := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  exact finite_of_isClosed_of_forall_isClosed_singleton
    (MMP.Flips.isOpen_regularLocus_of_locallyOfFiniteType f).isClosed_compl
    fun z hz => isClosed_singleton_of_not_isRegularLocalRing (fun Z hZ => (hdim Z hZ).le) hz

end MMP

end

/-!
# The norm functor on invertible sheaves along a finite locally free morphism

Let `f : X ⟶ Y` be a finite locally free morphism of schemes, of possibly varying (and possibly
zero) rank, and let `N_f = Stacks.Norm.finiteLocallyFreeNorm f` be its determinant norm on
functions. Gluing the norms of the transition units of local frames gives the norm
`Nm_f L = Stacks.Divisors.normInvertible f N_f L` of an invertible `𝒪_X`-module `L`, and
multiplication by the norm of the local coefficient gives the norm
`Stacks.Divisors.normMapOfCover` of a morphism of invertible modules. We show:

* `Nm_f` is a functor from invertible `𝒪_X`-modules to invertible `𝒪_Y`-modules;
* there are isomorphisms `Nm_f (L ⊗ M) ≅ Nm_f L ⊗ Nm_f M`, natural in `L` and `M`, and
  `Nm_f 𝒪_X ≅ 𝒪_Y`;
* for every cartesian square `X' = X ×_Y Y'`, with no flatness assumption on `Y' ⟶ Y`, there
  are isomorphisms `g^* (Nm_f L) ≅ Nm_{f'} (g'^* L)`, natural in `L`.

## Main results

* `MMP.exists_normInvertible_tensorIso_unitIso_pullbackIso`.

## Implementation notes

The rank of `f` is not assumed constant: the statement is for the class
`Stacks.Morphisms.IsFiniteLocallyFree`, and covers the open and closed strata of every rank,
including the rank zero stratum, where the source is empty and the norm is the trivial module.
Invertibility is `Stacks.SheafOfModules.IsInvertible` in the spelling of
`Stacks.Divisors.pullbackNormInvertibleIso`; trivializing target covers for invertible modules
are supplied by `Stacks.Divisors.hasTrivializingTargetCover_of_isFinite`, and for their pullbacks
along `X' ⟶ X` by `Stacks.Divisors.hasTrivializingTargetCover_of_isInvertible`. The base-change
clause is stated for any cartesian square `IsPullback g' f' f g`, not only for the chosen
pullback, and pullback of modules is `RingedSpaceModuleAdjunction.modulePullback`.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

section

universe u

open Stacks.Divisors Stacks.SheafOfModules Stacks.SheafOfModules.Tensor
open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace
open Stacks.Norm (MorphismNormMap)
open Stacks.SheafOfModules.UnitTransitionCocycle
open RingedSpaceModuleAdjunction

namespace MMP.Internal.FiniteLocallyFreeLineBundleNorm

section Generic

/-- A morphism out of a module is determined by its values on a family of local generators
whose opens cover the space. -/
private theorem hom_ext_of_generators {Z : Scheme.{u}} {P M : Z.Modules} (ψ₁ ψ₂ : P ⟶ M)
    {ι : Type u} (V : ι → Z.Opens) (g : ∀ i, GeneratorSections Z.toRingedSpace P (V i))
    (hV : ∀ z : Z, ∃ i, z ∈ V i)
    (h : ∀ i, ψ₁.val.app (op (V i)) (g i).val = ψ₂.val.app (op (V i)) (g i).val) :
    ψ₁ = ψ₂ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  refine section_eq_of_locally_eq (X := Z.toRingedSpace) M (fun i : ι => V i ⊓ U.unop) U.unop
    (fun _ => inf_le_right) ?_ _ _ ?_
  · intro y hy
    obtain ⟨i, hi⟩ := hV y
    exact Opens.mem_iSup.mpr ⟨i, hi, hy⟩
  · intro i
    let W := V i ⊓ U.unop
    let g' := generatorRestrict (X := Z.toRingedSpace) P (inf_le_left : W ≤ V i) (g i)
    obtain ⟨r, hr⟩ := (g'.property W le_rfl).surjective
      (P.val.map (homOfLE (inf_le_right : W ≤ U.unop)).op m)
    have hg := generator_restrict_self (X := Z.toRingedSpace) P W g'
    simp only [] at hr
    rw [hg] at hr
    have n₁ := congrArg (fun φ => φ m) (congrArg ModuleCat.Hom.hom
      (ψ₁.val.naturality (homOfLE (inf_le_right : W ≤ U.unop)).op))
    have n₂ := congrArg (fun φ => φ m) (congrArg ModuleCat.Hom.hom
      (ψ₂.val.naturality (homOfLE (inf_le_right : W ≤ U.unop)).op))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n₁ n₂
    change _ = _ at n₁ n₂
    rw [← n₁, ← n₂, ← hr]
    change (ψ₁.val.app (op W)).hom (r • g'.val) = (ψ₂.val.app (op W)).hom (r • g'.val)
    rw [(ψ₁.val.app (op W)).hom.map_smul, (ψ₂.val.app (op W)).hom.map_smul]
    refine congrArg (r • ·) ?_
    have k₁ := congrArg (fun φ => φ (g i).val) (congrArg ModuleCat.Hom.hom
      (ψ₁.val.naturality (homOfLE (inf_le_left : W ≤ V i)).op))
    have k₂ := congrArg (fun φ => φ (g i).val) (congrArg ModuleCat.Hom.hom
      (ψ₂.val.naturality (homOfLE (inf_le_left : W ≤ V i)).op))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at k₁ k₂
    change (ψ₁.val.app (op W)).hom (P.val.map (homOfLE (inf_le_left : W ≤ V i)).op (g i).val) =
      (ψ₂.val.app (op W)).hom (P.val.map (homOfLE (inf_le_left : W ≤ V i)).op (g i).val)
    change _ = _ at k₁ k₂
    exact k₁.trans ((congrArg (fun z => (M.val.map (homOfLE (inf_le_left : W ≤ V i)).op).hom z)
      (h i)).trans k₂.symm)

/-- The isomorphism `Stacks.SheafOfModules.isoOfChartGenerators` carries each chart generator of
the source to the corresponding chart generator of the target. -/
private theorem isoOfChartGenerators_hom_app {Z : RingedSpace.{u}} {ι : Type u}
    {U : ι → Opens Z.carrier} (P Q : _root_.SheafOfModules.{u} (structureSheafRing Z))
    (p : ∀ i, GeneratorSections Z P (U i)) (q : ∀ i, GeneratorSections Z Q (U i))
    (hpq : ∀ (i j : ι) (A : Opens Z.carrier) (hi : A ≤ U i) (hj : A ≤ U j),
      generatorRatioUnit Q A (generatorRestrict Q hj (q j)) (generatorRestrict Q hi (q i)) =
        generatorRatioUnit P A (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i)))
    (hU : (⊤ : Opens Z.carrier) ≤ ⨆ i, U i) (i : ι) :
    (isoOfChartGenerators P Q p q hpq hU).hom.val.app (op (U i)) (p i).val = (q i).val := by
  let D := cocycleOfChartGenerators p
  have key : (UnitTransitionCocycle.glueHom D q hpq).val.app (op (U i)) (q i).val =
      (UnitTransitionCocycle.glueHom D p (fun _ _ _ _ _ => rfl)).val.app (op (U i)) (p i).val := by
    apply (D.chartLinearEquiv i le_rfl).injective
    erw [UnitTransitionCocycle.chartLinearEquiv_glueSection D q hpq,
      UnitTransitionCocycle.chartLinearEquiv_glueSection D p (fun _ _ _ _ _ => rfl)]
    have e₁ := generatorCoordOfLE_generator (X := Z) (q i) (le_refl (U i))
    have e₂ := generatorCoordOfLE_generator (X := Z) (p i) (le_refl (U i))
    rw [show homOfLE (le_refl (U i)) = 𝟙 _ from rfl, CategoryTheory.op_id] at e₁ e₂
    simp only [PresheafOfModules.map_id] at e₁ e₂
    exact e₁.trans e₂.symm
  haveI := UnitTransitionCocycle.isIso_glueHom D q hpq hU
  change (inv (UnitTransitionCocycle.glueHom D q hpq)).val.app (op (U i))
    ((UnitTransitionCocycle.glueHom D p (fun _ _ _ _ _ => rfl)).val.app (op (U i)) (p i).val) = _
  rw [← key]
  change ((UnitTransitionCocycle.glueHom D q hpq ≫
    inv (UnitTransitionCocycle.glueHom D q hpq)).val.app (op (U i))) (q i).val = _
  exact congrArg (fun φ => (φ.val.app (op (U i))).hom (q i).val)
    (IsIso.hom_inv_id (UnitTransitionCocycle.glueHom D q hpq))

/-- The isomorphism `Stacks.SheafOfModules.isoOfChartGenerators` carries each restricted chart
generator of the source to the corresponding restricted chart generator of the target. -/
private theorem isoOfChartGenerators_hom_app_restrict {Z : RingedSpace.{u}} {ι : Type u}
    {U : ι → Opens Z.carrier} (P Q : _root_.SheafOfModules.{u} (structureSheafRing Z))
    (p : ∀ i, GeneratorSections Z P (U i)) (q : ∀ i, GeneratorSections Z Q (U i))
    (hpq : ∀ (i j : ι) (A : Opens Z.carrier) (hi : A ≤ U i) (hj : A ≤ U j),
      generatorRatioUnit Q A (generatorRestrict Q hj (q j)) (generatorRestrict Q hi (q i)) =
        generatorRatioUnit P A (generatorRestrict P hj (p j)) (generatorRestrict P hi (p i)))
    (hU : (⊤ : Opens Z.carrier) ≤ ⨆ i, U i) (i : ι) {B : Opens Z.carrier} (hB : B ≤ U i) :
    (isoOfChartGenerators P Q p q hpq hU).hom.val.app (op B) (generatorRestrict P hB (p i)).val =
      (generatorRestrict Q hB (q i)).val := by
  have k := congrArg (fun φ => φ (p i).val) (congrArg ModuleCat.Hom.hom
    ((isoOfChartGenerators P Q p q hpq hU).hom.val.naturality (homOfLE hB).op))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at k
  change _ = _ at k
  change ((isoOfChartGenerators P Q p q hpq hU).hom.val.app (op B)).hom
      (P.val.map (homOfLE hB).op (p i).val) = Q.val.map (homOfLE hB).op (q i).val
  exact k.trans (congrArg (fun z => (Q.val.map (homOfLE hB).op).hom z)
    (isoOfChartGenerators_hom_app P Q p q hpq hU i))

/-- Tensoring two morphisms acts on elementary tensors of sections factorwise. -/
private theorem sheafTensor_map_toTensorSheafSection (Z : RingedSpace.{u})
    {L L' M M' : _root_.SheafOfModules.{u} (structureSheafRing Z)} (φ : L ⟶ L') (ψ : M ⟶ M')
    (U : (Opens Z.carrier)ᵒᵖ) (x : L.val.obj U) (y : M.val.obj U) :
    (((sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩).map φ).app M ≫
      ((sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩).obj L').map ψ).val.app U
        (TensorStalkRingedSpace.toTensorSheafSection Z L M U (x ⊗ₜ y)) =
      TensorStalkRingedSpace.toTensorSheafSection Z L' M' U (φ.val.app U x ⊗ₜ ψ.val.app U y) := by
  have h₁ := congrArg (fun k => (k.app U).hom (x ⊗ₜ y))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing Z).obj)).unit.naturality
      (((PresheafOfModules.tensorBifunctor _).map φ.val).app M.val))
  have h₂ := congrArg (fun k => (k.app U).hom (φ.val.app U x ⊗ₜ y))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureSheafRing Z).obj)).unit.naturality
      (((PresheafOfModules.tensorBifunctor _).obj L'.val).map ψ.val))
  exact (congrArg
    (fun z => ((((sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩).obj L').map ψ).val.app U).hom z)
    h₁.symm).trans h₂.symm

/-- The elementary tensor of two scaled sections is the product of the scalars times the
elementary tensor. -/
private theorem toTensorSheafSection_smul_tmul_smul (Z : RingedSpace.{u})
    (L M : _root_.SheafOfModules.{u} (structureSheafRing Z)) (U : (Opens Z.carrier)ᵒᵖ)
    (r r' : Z.presheaf.obj U) (x : L.val.obj U) (y : M.val.obj U) :
    letI : Module (Z.presheaf.obj U)
        ((((sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩).obj L).obj M).val.obj U) :=
      Tensor.ringSheafSectionModule ⟨Z.presheaf, Z.IsSheaf⟩ U _
    TensorStalkRingedSpace.toTensorSheafSection Z L M U ((r • x) ⊗ₜ (r' • y)) =
      (r * r') • TensorStalkRingedSpace.toTensorSheafSection Z L M U (x ⊗ₜ y) := by
  letI : Module (Z.presheaf.obj U)
      ((((sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩).obj L).obj M).val.obj U) :=
    Tensor.ringSheafSectionModule ⟨Z.presheaf, Z.IsSheaf⟩ U _
  have key : (r • x) ⊗ₜ[Z.presheaf.obj U] (r' • y) = (r * r') • (x ⊗ₜ[Z.presheaf.obj U] y) :=
    (TensorProduct.smul_tmul_smul r r' x y)
  rw [key]
  exact ((TensorStalkRingedSpace.sheafifyUnit Z (PresheafOfModules.tensorObj (O := Z.presheaf)
    L.val M.val)).app U).hom.map_smul _ _

end Generic

section Ext

variable {X Y : Scheme.{u}}

/-- Two maps out of the norm of `L` agree once they agree on the norms of the local frames
of `L` over the members of a family of target opens which is closed under shrinking and
covers the target. -/
private theorem normInvertible_hom_ext (f : X ⟶ Y) (N : MorphismNormMap f) {L : X.Modules}
    (hL : HasTrivializingTargetCover f L) {M : Y.Modules} (ψ₁ ψ₂ : normInvertible f N L ⟶ M)
    (P : Y.Opens → Prop) (hPle : ∀ {V W : Y.Opens}, W ≤ V → P V → P W)
    (hPcov : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ P V)
    (h : ∀ (V : Y.Opens), P V → ∀ (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V)),
      ψ₁.val.app (op V) (normGenerator f N L hL V s).val =
        ψ₂.val.app (op V) (normGenerator f N L hL V s).val) : ψ₁ = ψ₂ := by
  refine hom_ext_of_generators ψ₁ ψ₂
    (ι := Σ V : {V : Y.Opens // P V}, GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ V.1))
    (fun i => i.1.1) (fun i => normGenerator f N L hL i.1.1 i.2) (fun y => ?_)
    (fun i => h _ i.1.2 i.2)
  obtain ⟨V, hyV, ⟨s⟩⟩ := exists_generatorSections_near_point f L hL y
  obtain ⟨V', hyV', hP⟩ := hPcov y
  exact ⟨⟨⟨V ⊓ V', hPle inf_le_right hP⟩,
    generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).monotone inf_le_left) s⟩,
    hyV, hyV'⟩

end Ext

section Functor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : MorphismNormMap f)

/-- The norm of the identity of an invertible module is the identity. -/
private theorem normMapOfCover_id (L : X.Modules) (hL : HasTrivializingTargetCover f L) :
    normMapOfCover f N L L hL hL (𝟙 L) = 𝟙 _ := by
  refine normInvertible_hom_ext f N hL _ _ (fun _ => True) (fun _ _ => trivial)
    (fun _ => ⟨⊤, trivial, trivial⟩) ?_
  intro V _ s
  have h1 : (𝟙 L : L ⟶ L).val.app (op (f ⁻¹ᵁ V)) s.val =
      @SMul.smul ((structureSheaf X.sheaf).obj.obj (op (f ⁻¹ᵁ V)))
        (L.val.obj (op (f ⁻¹ᵁ V))) _ 1 s.val :=
    (one_smul (X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ V))) s.val).symm
  rw [normMapOfCover_generator f N L L hL hL (𝟙 L) V s s 1 h1, map_one]
  exact one_smul (Y.ringCatSheaf.obj.obj (op V)) _

/-- The norm of a composite is the composite of the norms. -/
private theorem normMapOfCover_comp {L L' L'' : X.Modules} (hL : HasTrivializingTargetCover f L)
    (hL' : HasTrivializingTargetCover f L') (hL'' : HasTrivializingTargetCover f L'')
    (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    normMapOfCover f N L L'' hL hL'' (φ ≫ ψ) =
      normMapOfCover f N L L' hL hL' φ ≫ normMapOfCover f N L' L'' hL' hL'' ψ := by
  refine normInvertible_hom_ext f N hL _ _
    (fun V => Nonempty (GeneratorSections X.toRingedSpace L' (f ⁻¹ᵁ V)) ∧
      Nonempty (GeneratorSections X.toRingedSpace L'' (f ⁻¹ᵁ V))) ?_ ?_ ?_
  · rintro V W hWV ⟨⟨t⟩, ⟨u⟩⟩
    exact ⟨⟨generatorRestrict (X := X.toRingedSpace) L' ((Opens.map f.base).monotone hWV) t⟩,
      ⟨generatorRestrict (X := X.toRingedSpace) L'' ((Opens.map f.base).monotone hWV) u⟩⟩
  · intro y
    obtain ⟨V₁, h₁, ⟨t⟩⟩ := exists_generatorSections_near_point f L' hL' y
    obtain ⟨V₂, h₂, ⟨u⟩⟩ := exists_generatorSections_near_point f L'' hL'' y
    exact ⟨V₁ ⊓ V₂, ⟨h₁, h₂⟩,
      ⟨generatorRestrict (X := X.toRingedSpace) L' ((Opens.map f.base).monotone inf_le_left) t⟩,
      ⟨generatorRestrict (X := X.toRingedSpace) L'' ((Opens.map f.base).monotone inf_le_right)
        u⟩⟩
  · rintro V ⟨⟨t⟩, ⟨u⟩⟩ s
    have ha := generatorCoefficient_spec (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ V) s t
    have hb := generatorCoefficient_spec (X := X.toRingedSpace) L' L'' ψ (f ⁻¹ᵁ V) t u
    set a := generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ V) s t
    set b := generatorCoefficient (X := X.toRingedSpace) L' L'' ψ (f ⁻¹ᵁ V) t u
    have hab : (φ ≫ ψ).val.app (op (f ⁻¹ᵁ V)) s.val = (a * b) • u.val := by
      change (ψ.val.app (op (f ⁻¹ᵁ V))).hom ((φ.val.app (op (f ⁻¹ᵁ V))).hom s.val) = _
      rw [ha, (ψ.val.app (op (f ⁻¹ᵁ V))).hom.map_smul, hb, mul_smul]
    rw [normMapOfCover_generator f N L L'' hL hL'' (φ ≫ ψ) V s u (a * b) hab]
    change _ = ((normMapOfCover f N L' L'' hL' hL'' ψ).val.app (op V)).hom
      (((normMapOfCover f N L L' hL hL' φ).val.app (op V)).hom _)
    rw [normMapOfCover_generator f N L L' hL hL' φ V s t a ha]
    have e1 := ((normMapOfCover f N L' L'' hL' hL'' ψ).val.app (op V)).hom.map_smul
      (N.app V a) (normGenerator f N L' hL' V t).val
    have e2 := normMapOfCover_generator f N L' L'' hL' hL'' ψ V t u b hb
    refine Eq.trans ?_ e1.symm
    refine Eq.trans ?_ (congrArg
      (fun z => @id (Y.ringCatSheaf.obj.obj (op V) : Type u) (N.app V a) • z) e2).symm
    exact (congrArg (fun c : (Y.ringCatSheaf.obj.obj (op V) : Type u) =>
      c • (normGenerator f N L'' hL'' V u).val) (map_mul (N.app V) a b)).trans (mul_smul _ _ _)

end Functor

section Unit

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : MorphismNormMap f)

/-- The norm of the structure sheaf is trivial: the norm of the frame `1` is a global frame. -/
private theorem nonempty_normInvertible_unitModule_iso
    (hcov : HasTrivializingTargetCover f (Stacks.Ample.unitModule X)) :
    Nonempty (normInvertible f N (Stacks.Ample.unitModule X) ≅ Stacks.Ample.unitModule Y) := by
  let M := normInvertible f N (Stacks.Ample.unitModule X)
  let g := normGenerator f N (Stacks.Ample.unitModule X) hcov ⊤
    (Stacks.SheafOfModules.unitGenerator X (f ⁻¹ᵁ ⊤))
  refine ⟨(isoOfBijective (X := Y.toRingedSpace) (Stacks.SheafOfModules.unitHom M g.val)
    fun W => ?_).symm⟩
  have h1 := Stacks.SheafOfModules.unitHom_app_one M g.val W
  have key : ∀ r : (Y.ringCatSheaf.obj.obj (op W) : Type u),
      (Stacks.SheafOfModules.unitHom M g.val).val.app (op W) r =
      r • M.val.restrictₛₗ (homOfLE (le_top : W ≤ ⊤)).op g.val := by
    intro r
    have e := ((Stacks.SheafOfModules.unitHom M g.val).val.app (op W)).hom.map_smul r
      (1 : (Y.ringCatSheaf.obj.obj (op W) : Type u))
    refine Eq.trans ?_ (e.trans (congrArg (r • ·) h1))
    exact congrArg _ (mul_one r).symm
  have hb := g.property W le_top
  exact (funext key ▸ hb : _)

end Unit

section ChartGeneratorRatio

attribute [local instance] UnitTransitionCocycle.sectionsProductModule

variable {Z : RingedSpace.{u, u}} {ι : Type u} {U : ι → Opens Z.carrier}

/-- The scalar action on a compatible family of local coordinates multiplies each coordinate by
the restricted scalar. -/
private theorem sections_smul_val (D : UnitTransitionCocycle Z U) {V : Opens Z.carrier}
    (r : Z.presheaf.obj (op V)) (s : D.sectionsSubmodule V) (k : ι) :
    (r • s).val k =
      Z.presheaf.map (homOfLE (inf_le_left : V ⊓ U k ≤ V)).op r * s.val k := rfl

/-- **The transition unit of two chart generators of a glued cocycle is the transition unit of
the cocycle.** Over an open `V` inside both charts, the `i`-th chart generator is `u_{ij}` times
the `j`-th: in the `k`-th coordinate that equation is `u_{ik} = u_{ij} u_{jk}`, which is the
cocycle identity. -/
private theorem generatorRatioUnit_chartGenerator (D : UnitTransitionCocycle Z U)
    (hU : (⊤ : Opens Z.carrier) ≤ ⨆ i, U i) (i j : ι) {V : Opens Z.carrier}
    (hi : V ≤ U i) (hj : V ≤ U j) :
    generatorRatioUnit D.glue V (generatorRestrict D.glue hj (D.chartGenerator hU j))
        (generatorRestrict D.glue hi (D.chartGenerator hU i)) =
      D.transition i j V hi hj := by
  refine generatorRatioUnit_eq _ _ _ _ _ ?_
  change (D.sectionsMap hi (D.chartSection i) : D.sectionsSubmodule V) =
    (D.transition i j V hi hj).val • D.sectionsMap hj (D.chartSection j)
  refine Subtype.ext (funext fun k => ?_)
  rw [sectionsMap_val, sections_smul_val, sectionsMap_val]
  have hVk : V ⊓ U k ≤ V := inf_le_left
  have hki : V ⊓ U k ≤ U i := hVk.trans hi
  have hkj : V ⊓ U k ≤ U j := hVk.trans hj
  have hkk : V ⊓ U k ≤ U k := inf_le_right
  have e1 : Z.presheaf.map (homOfLE (inf_le_inf_right (U k) hi)).op
        ((D.chartSection i).val k) = (D.transition i k (V ⊓ U k) hki hkk).val :=
    congrArg Units.val (D.restrict (i := i) (j := k) (inf_le_left : U i ⊓ U k ≤ U i)
      (inf_le_right : U i ⊓ U k ≤ U k) (inf_le_inf_right (U k) hi))
  have e2 : Z.presheaf.map (homOfLE (inf_le_inf_right (U k) hj)).op
        ((D.chartSection j).val k) = (D.transition j k (V ⊓ U k) hkj hkk).val :=
    congrArg Units.val (D.restrict (i := j) (j := k) (inf_le_left : U j ⊓ U k ≤ U j)
      (inf_le_right : U j ⊓ U k ≤ U k) (inf_le_inf_right (U k) hj))
  have e3 : Z.presheaf.map (homOfLE hVk).op (D.transition i j V hi hj).val =
      (D.transition i j (V ⊓ U k) hki hkj).val :=
    congrArg Units.val (D.restrict (i := i) (j := j) hi hj hVk)
  rw [e1, e2, e3, ← D.cocycle i j k (V ⊓ U k) hki hkj hkk, Units.val_mul, mul_comm]

end ChartGeneratorRatio

section BaseChangeIso

variable {X Y X' Y' : Scheme.{u}}

/-- The norm of a local generator, restricted, is the norm of the restricted generator. -/
private theorem generatorRestrict_normGenerator' (f : X ⟶ Y) (N : MorphismNormMap f) (L : X.Modules)
    (hL : HasTrivializingTargetCover f L) {W V : Y.Opens} (h : V ≤ W)
    (s : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ W)) :
    generatorRestrict (X := Y.toRingedSpace) (normInvertible f N L) h
        (normGenerator f N L hL W s) =
      normGenerator f N L hL V
        (generatorRestrict (X := X.toRingedSpace) L ((Opens.map f.base).map (homOfLE h)).le s) :=
  (Subtype.ext (normGenerator_restrict f N L hL h s)).symm

/-- The preimage under `f'` of the preimage under `g` lies in the preimage under `g'` of the
preimage under `f`, around a commutative square. -/
private theorem preimage_le_preimage_of_comp_eq {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    {g : Y' ⟶ Y}
    (w : g' ≫ f = f' ≫ g) {U : Y.Opens} {A : Y'.Opens} (hA : A ≤ g ⁻¹ᵁ U) :
    f' ⁻¹ᵁ A ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U) := by
  intro x hx
  change f (g' x) ∈ U
  rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  exact hA hx

/-- The transition unit of two pulled-back generators over an open inside the preimage is the
`AlgebraicGeometry.Scheme.Hom.appLE` of the transition unit upstairs. -/
private theorem generatorRatioUnit_restrict_pullbackGenerator' (f : X ⟶ Y) (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    {U : Y.Opens} {A : X.Opens} (h : A ≤ f ⁻¹ᵁ U) (s t : GeneratorSections Y.toRingedSpace L U) :
    generatorRatioUnit ((modulePullback f.toLRSHom.toShHom).obj L) A
        (generatorRestrict _ h (pullbackGenerator f L hL U s))
        (generatorRestrict _ h (pullbackGenerator f L hL U t)) =
      Units.map (f.appLE U A h).hom.toMonoidHom (generatorRatioUnit L U s t) :=
  (generatorRatioUnit_restrict _ h (pullbackGenerator f L hL U s)
      (pullbackGenerator f L hL U t)).trans
    ((congrArg (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom)
      (generatorRatioUnit_pullbackGenerator f L hL U s t)).trans rfl)

/-- The norm of an invertible module commutes with base change, for norms compatible around a
cartesian square: `g^*(Norm_f ℒ) ≅ Norm_{f'}(g'^*ℒ)`. The compatibility `hN` says that the norm of
a pulled-back function is the pullback of the norm. -/
private noncomputable def pullbackNormInvertibleIso (f : X ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (g : Y' ⟶ Y)
    (w : g' ≫ f = f' ≫ g) (N : MorphismNormMap f) (N' : MorphismNormMap f')
    (hN : ∀ (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)),
      N'.app (g ⁻¹ᵁ U) (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U))
        (preimage_le_preimage_of_comp_eq w le_rfl) s) = g.app U (N.app U s))
    (L : X.Modules)
    (hLinv : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
    (hL : HasTrivializingTargetCover f L)
    (hL' : HasTrivializingTargetCover f' ((modulePullback g'.toLRSHom.toShHom).obj L)) :
    (modulePullback g.toLRSHom.toShHom).obj (normInvertible f N L) ≅
      normInvertible f' N' ((modulePullback g'.toLRSHom.toShHom).obj L) := by
  classical
  have hNinv : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property
      (normInvertible f N L) :=
    isInvertible_normInvertible f N L hL
  have hcov : (⊤ : Y.Opens) ≤ ⨆ i : NormChart f L, i.val := normChart_cover hL
  have hcov' : (⊤ : Y'.Opens) ≤ ⨆ i : NormChart f L, g ⁻¹ᵁ (i.val : Y.Opens) := by
    intro x _
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov (show g.base x ∈ (⊤ : Y.Opens) from trivial))
    exact Opens.mem_iSup.2 ⟨i, hi⟩
  let L' := (modulePullback g'.toLRSHom.toShHom).obj L
  -- the generator of `g'^*ℒ` over `f'⁻¹(g⁻¹U)` coming from a chart `U` of `ℒ`
  let s' : ∀ i : NormChart f L, GeneratorSections X'.toRingedSpace L'
      (f' ⁻¹ᵁ (g ⁻¹ᵁ (i.val : Y.Opens))) := fun i =>
    generatorRestrict _ (preimage_le_preimage_of_comp_eq w le_rfl)
      (pullbackGenerator g' L hLinv (f ⁻¹ᵁ (i.val : Y.Opens)) (normChartSourceGenerator f L i))
  refine isoOfChartGenerators _ _
    (fun i : NormChart f L => pullbackGenerator g (normInvertible f N L) hNinv
      (i.val : Y.Opens) ((normTransitionCocycle f N L).chartGenerator hcov i))
    (fun i : NormChart f L => normGenerator f' N' L' hL' (g ⁻¹ᵁ (i.val : Y.Opens)) (s' i))
    ?_ hcov'
  intro i j A hi hj
  let W : Y.Opens := i.val ⊓ j.val
  have hiW : W ≤ i.val := inf_le_left
  have hjW : W ≤ j.val := inf_le_right
  have hAB : A ≤ g ⁻¹ᵁ W := by
    change A ≤ g ⁻¹ᵁ (i.val ⊓ j.val)
    rw [Scheme.Hom.preimage_inf]; exact le_inf hi hj
  have hBi : g ⁻¹ᵁ W ≤ g ⁻¹ᵁ (i.val : Y.Opens) := ((Opens.map g.base).map (homOfLE hiW)).le
  have hBj : g ⁻¹ᵁ W ≤ g ⁻¹ᵁ (j.val : Y.Opens) := ((Opens.map g.base).map (homOfLE hjW)).le
  -- the pulled-back side
  have hP : generatorRatioUnit
        ((modulePullback g.toLRSHom.toShHom).obj (normInvertible f N L)) A
        (generatorRestrict _ hj (pullbackGenerator g (normInvertible f N L) hNinv
          (j.val : Y.Opens) ((normTransitionCocycle f N L).chartGenerator hcov j)))
        (generatorRestrict _ hi (pullbackGenerator g (normInvertible f N L) hNinv
          (i.val : Y.Opens) ((normTransitionCocycle f N L).chartGenerator hcov i))) =
      Units.map (g.appLE W A hAB).hom.toMonoidHom
        (normUnitsMap f N W
          (generatorRatioUnit L (f ⁻¹ᵁ W)
            (normChartGeneratorOver f L j W hjW) (normChartGeneratorOver f L i W hiW))) :=
    (congrArg₂ (generatorRatioUnit _ A)
        ((generatorRestrict_trans _ hBj hAB _).symm.trans
          (congrArg (generatorRestrict _ hAB)
            (pullbackGenerator_restrict g (normInvertible f N L) hNinv hjW
              ((normTransitionCocycle f N L).chartGenerator hcov j))))
        ((generatorRestrict_trans _ hBi hAB _).symm.trans
          (congrArg (generatorRestrict _ hAB)
            (pullbackGenerator_restrict g (normInvertible f N L) hNinv hiW
              ((normTransitionCocycle f N L).chartGenerator hcov i))))).trans
      ((generatorRatioUnit_restrict_pullbackGenerator' g (normInvertible f N L) hNinv hAB
          _ _).trans
        (congrArg (Units.map (g.appLE W A hAB).hom.toMonoidHom)
          (generatorRatioUnit_chartGenerator (normTransitionCocycle f N L) hcov i j hiW hjW)))
  -- the normed side: restrict the normed generators to `A`
  have hkA : f' ⁻¹ᵁ A ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ W) := preimage_le_preimage_of_comp_eq w hAB
  have hs'A : ∀ (k : NormChart f L) (hkW : W ≤ k.val) (hk : A ≤ g ⁻¹ᵁ (k.val : Y.Opens)),
      generatorRestrict (X := X'.toRingedSpace) L' ((Opens.map f'.base).map (homOfLE hk)).le
          (s' k) =
        generatorRestrict _ hkA
          (pullbackGenerator g' L hLinv (f ⁻¹ᵁ W) (normChartGeneratorOver f L k W hkW)) := by
    intro k hkW hk
    have hle : f ⁻¹ᵁ W ≤ f ⁻¹ᵁ (k.val : Y.Opens) := ((Opens.map f.base).map (homOfLE hkW)).le
    calc _ = generatorRestrict L' (le_trans ((Opens.map f'.base).map (homOfLE hk)).le
            (preimage_le_preimage_of_comp_eq w le_rfl))
          (pullbackGenerator g' L hLinv (f ⁻¹ᵁ (k.val : Y.Opens))
            (normChartSourceGenerator f L k)) := generatorRestrict_trans _ _ _ _
      _ = generatorRestrict L' hkA (generatorRestrict L'
            ((Opens.map g'.base).map (homOfLE hle)).le
            (pullbackGenerator g' L hLinv (f ⁻¹ᵁ (k.val : Y.Opens))
              (normChartSourceGenerator f L k))) := (generatorRestrict_trans _ _ _ _).symm
      _ = _ := congrArg (generatorRestrict L' hkA)
            (pullbackGenerator_restrict g' L hLinv hle (normChartSourceGenerator f L k))
  have hQ : generatorRatioUnit (normInvertible f' N' L') A
        (generatorRestrict _ hj (normGenerator f' N' L' hL' (g ⁻¹ᵁ (j.val : Y.Opens)) (s' j)))
        (generatorRestrict _ hi (normGenerator f' N' L' hL' (g ⁻¹ᵁ (i.val : Y.Opens)) (s' i))) =
      normUnitsMap f' N' A
        (Units.map (g'.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ A) hkA).hom.toMonoidHom
          (generatorRatioUnit L (f ⁻¹ᵁ W)
            (normChartGeneratorOver f L j W hjW) (normChartGeneratorOver f L i W hiW))) :=
    (congrArg₂ (generatorRatioUnit _ A)
        (generatorRestrict_normGenerator' f' N' L' hL' hj (s' j))
        (generatorRestrict_normGenerator' f' N' L' hL' hi (s' i))).trans
      ((generatorRatioUnit_normGenerator f' N' L' hL' A _ _).trans
        (congrArg (normUnitsMap f' N' A)
          ((congrArg₂ (generatorRatioUnit L' (f' ⁻¹ᵁ A)) (hs'A j hjW hj) (hs'A i hiW hi)).trans
            (generatorRatioUnit_restrict_pullbackGenerator' g' L hLinv hkA _ _))))
  refine hQ.trans (Eq.trans ?_ hP.symm)
  -- the compatibility of the two norms, restricted from `g⁻¹W` to `A`
  refine Units.ext ?_
  change N'.app A ((g'.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ A) hkA).hom _) =
    (g.appLE W A hAB).hom (N.app W _)
  set x := (generatorRatioUnit L (f ⁻¹ᵁ W)
    (normChartGeneratorOver f L j W hjW) (normChartGeneratorOver f L i W hiW)).val
  have h1 : ∀ y : Γ(X, f ⁻¹ᵁ W), (g'.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ A) hkA).hom y =
      (X'.presheaf.map ((Opens.map f'.base).map (homOfLE hAB)).op).hom
        ((g'.appLE (f ⁻¹ᵁ W) (f' ⁻¹ᵁ (g ⁻¹ᵁ W))
          (preimage_le_preimage_of_comp_eq w le_rfl)).hom y) := fun y => by
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  refine (congrArg (N'.app A) (h1 x)).trans ?_
  rw [N'.naturality]
  refine (congrArg (fun z => (Y'.presheaf.map (homOfLE hAB).op).hom z) (hN W x)).trans ?_
  change (g.app W ≫ Y'.presheaf.map (homOfLE hAB).op).hom (N.app W x) = _
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

end BaseChangeIso

section Tensor

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : MorphismNormMap f)

/-- The tensor product of two modules on a scheme. -/
private noncomputable abbrev tensorObj {Z : Scheme.{u}} (L M : Z.Modules) : Z.Modules :=
  ((sheafTensor ⟨Z.toRingedSpace.presheaf, Z.toRingedSpace.IsSheaf⟩).obj L).obj M

/-- The chart generator of the norm of the tensor product: the norm of the elementary tensor of
the two chart generators. -/
private noncomputable def normTmulGenerator (f : X ⟶ Y) (N : MorphismNormMap f) {L M : X.Modules}
    (hLM : HasTrivializingTargetCover f (tensorObj L M))
    (c : TensorChart f L M) {A : Y.Opens} (h : A ≤ tensorChartOpen c) :
    GeneratorSections Y.toRingedSpace
      (normInvertible f N (tensorObj L M)) A :=
  normGenerator f N (tensorObj L M) hLM A
    (tmulGenerator (tensorChartGenFst c h) (tensorChartGenSnd c h))

/-- The chart generator of the tensor product of the norms: the elementary tensor of the norms of
the two chart generators. -/
private noncomputable def tmulNormGenerator (f : X ⟶ Y) (N : MorphismNormMap f) {L M : X.Modules}
    (hL : HasTrivializingTargetCover f L) (hM : HasTrivializingTargetCover f M)
    (c : TensorChart f L M) {A : Y.Opens} (h : A ≤ tensorChartOpen c) :
    GeneratorSections Y.toRingedSpace
      (tensorObj (normInvertible f N L) (normInvertible f N M)) A :=
  tmulGenerator (normGenerator f N L hL A (tensorChartGenFst c h))
    (normGenerator f N M hM A (tensorChartGenSnd c h))

private theorem generatorRestrict_normTmulGenerator (f : X ⟶ Y) (N : MorphismNormMap f)
    {L M : X.Modules} (hLM : HasTrivializingTargetCover f (tensorObj L M))
    (c : TensorChart f L M) {A B : Y.Opens} (h : A ≤ tensorChartOpen c) (k : B ≤ A) :
    generatorRestrict (X := Y.toRingedSpace)
        (normInvertible f N (tensorObj L M)) k
        (normTmulGenerator f N hLM c h) =
      normTmulGenerator f N hLM c (k.trans h) := by
  refine (generatorRestrict_normGenerator' f N (tensorObj L M) hLM k
    (tmulGenerator (tensorChartGenFst c h) (tensorChartGenSnd c h))).trans ?_
  refine congrArg
    (normGenerator f N (tensorObj L M) hLM B) ?_
  refine (tmulGenerator_restrict (X := X.toRingedSpace) (tensorChartGenFst c h)
    (tensorChartGenSnd c h) ((Opens.map f.base).map (homOfLE k)).le).trans ?_
  exact congrArg₂ (fun (a : GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ B))
      (b : GeneratorSections X.toRingedSpace M (f ⁻¹ᵁ B)) => tmulGenerator a b)
    (generatorRestrict_tensorChartGenFst c h k) (generatorRestrict_tensorChartGenSnd c h k)

private theorem generatorRestrict_tmulNormGenerator (f : X ⟶ Y) (N : MorphismNormMap f)
    {L M : X.Modules} (hL : HasTrivializingTargetCover f L)
    (hM : HasTrivializingTargetCover f M)
    (c : TensorChart f L M) {A B : Y.Opens} (h : A ≤ tensorChartOpen c) (k : B ≤ A) :
    generatorRestrict (X := Y.toRingedSpace)
        (tensorObj (normInvertible f N L) (normInvertible f N M)) k
        (tmulNormGenerator f N hL hM c h) =
      tmulNormGenerator f N hL hM c (k.trans h) := by
  refine (tmulGenerator_restrict (X := Y.toRingedSpace)
    (normGenerator f N L hL A (tensorChartGenFst c h))
    (normGenerator f N M hM A (tensorChartGenSnd c h)) k).trans ?_
  refine congrArg₂
    (fun (a : GeneratorSections Y.toRingedSpace (normInvertible f N L) B)
      (b : GeneratorSections Y.toRingedSpace (normInvertible f N M) B) =>
      tmulGenerator a b)
    ?_ ?_
  · exact (generatorRestrict_normGenerator' f N L hL k (tensorChartGenFst c h)).trans
      (congrArg (normGenerator f N L hL B)
        (generatorRestrict_tensorChartGenFst c h k))
  · exact (generatorRestrict_normGenerator' f N M hM k (tensorChartGenSnd c h)).trans
      (congrArg (normGenerator f N M hM B)
        (generatorRestrict_tensorChartGenSnd c h k))

/-- **The transition units of the two chart generator families agree**, by multiplicativity of
the generator ratio across a tensor product and multiplicativity of the norm. -/
private theorem generatorRatioUnit_tmulNormGenerator (f : X ⟶ Y) (N : MorphismNormMap f)
    {L M : X.Modules} (hL : HasTrivializingTargetCover f L)
    (hM : HasTrivializingTargetCover f M)
    (hLM : HasTrivializingTargetCover f (tensorObj L M))
    (c₁ c₂ : TensorChart f L M) (A : Y.Opens)
    (h₁ : A ≤ tensorChartOpen c₁) (h₂ : A ≤ tensorChartOpen c₂) :
    generatorRatioUnit (X := Y.toRingedSpace)
        (tensorObj (normInvertible f N L) (normInvertible f N M)) A
        (tmulNormGenerator f N hL hM c₂ h₂) (tmulNormGenerator f N hL hM c₁ h₁) =
      generatorRatioUnit (X := Y.toRingedSpace)
        (normInvertible f N (tensorObj L M)) A
        (normTmulGenerator f N hLM c₂ h₂) (normTmulGenerator f N hLM c₁ h₁) := by
  refine Eq.symm ?_
  refine (generatorRatioUnit_normGenerator f N
    (tensorObj L M) hLM A
    (tmulGenerator (tensorChartGenFst c₂ h₂) (tensorChartGenSnd c₂ h₂))
    (tmulGenerator (tensorChartGenFst c₁ h₁) (tensorChartGenSnd c₁ h₁))).trans ?_
  refine ((congrArg (normUnitsMap f N A)
    (generatorRatioUnit_tmulGenerator (X := X.toRingedSpace) (tensorChartGenFst c₂ h₂)
      (tensorChartGenFst c₁ h₁) (tensorChartGenSnd c₂ h₂) (tensorChartGenSnd c₁ h₁))).trans
    (map_mul (normUnitsMap f N A) _ _)).trans ?_
  refine Eq.trans ?_ (generatorRatioUnit_tmulGenerator (X := Y.toRingedSpace)
    (normGenerator f N L hL A (tensorChartGenFst c₂ h₂))
    (normGenerator f N L hL A (tensorChartGenFst c₁ h₁))
    (normGenerator f N M hM A (tensorChartGenSnd c₂ h₂))
    (normGenerator f N M hM A (tensorChartGenSnd c₁ h₁))).symm
  exact congrArg₂ (fun y z : (Γ(Y, A))ˣ => y * z)
    (generatorRatioUnit_normGenerator f N L hL A (tensorChartGenFst c₂ h₂)
      (tensorChartGenFst c₁ h₁)).symm
    (generatorRatioUnit_normGenerator f N M hM A (tensorChartGenSnd c₂ h₂)
      (tensorChartGenSnd c₁ h₁)).symm

/-- The norm of a tensor product is the tensor product of the norms, for a norm of varying
degree. -/
private noncomputable def normInvertibleTensorIsoOfCover (f : X ⟶ Y) (N : MorphismNormMap f)
    {L M : X.Modules} (hL : HasTrivializingTargetCover f L)
    (hM : HasTrivializingTargetCover f M)
    (hLM : HasTrivializingTargetCover f (tensorObj L M)) :
    normInvertible f N (tensorObj L M) ≅
      (tensorObj (normInvertible f N L) (normInvertible f N M)) :=
  isoOfChartGenerators (X := Y.toRingedSpace)
    (normInvertible f N (tensorObj L M))
    (tensorObj (normInvertible f N L) (normInvertible f N M))
    (fun c => normTmulGenerator f N hLM c le_rfl)
    (fun c => tmulNormGenerator f N hL hM c le_rfl)
    (fun i j A hi hj =>
      ((congrArg₂ (generatorRatioUnit (X := Y.toRingedSpace)
            (tensorObj (normInvertible f N L) (normInvertible f N M)) A)
          (generatorRestrict_tmulNormGenerator f N hL hM j le_rfl hj)
          (generatorRestrict_tmulNormGenerator f N hL hM i le_rfl hi)).trans
        (generatorRatioUnit_tmulNormGenerator f N hL hM hLM i j A hi hj)).trans
      (congrArg₂ (generatorRatioUnit (X := Y.toRingedSpace)
            (normInvertible f N (tensorObj L M)) A)
          (generatorRestrict_normTmulGenerator f N hLM j le_rfl hj)
          (generatorRestrict_normTmulGenerator f N hLM i le_rfl hi)).symm)
    (tensorChart_cover hL hM)

/- The norm of a tensor product of invertible modules is the tensor product of the norms,
naturally in both variables: on frames `s ⊗ t` the transition units are products and the norm
is multiplicative. -/
private theorem exists_normInvertible_tensorIso_natural
    (cov : ∀ L : X.Modules,
      IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L →
      HasTrivializingTargetCover f L) :
    let Inv : X.Modules → Prop := fun L =>
      IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L
    let TX := sheafTensor ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩
    let TY := sheafTensor ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩
    ∃ e : ∀ (L M : X.Modules), Inv L → Inv M →
        (normInvertible f N ((TX.obj L).obj M) ≅
          (TY.obj (normInvertible f N L)).obj (normInvertible f N M)),
      ∀ (L L' M M' : X.Modules) (hL : Inv L) (hL' : Inv L') (hM : Inv M) (hM' : Inv M')
        (φ : L ⟶ L') (ψ : M ⟶ M'),
        normMapOfCover f N _ _
            (cov _ (Stacks.Cohomology.Generators.isInvertible_tensorSheaf_of_isInvertible
              X.toRingedSpace L M hL hM))
            (cov _ (Stacks.Cohomology.Generators.isInvertible_tensorSheaf_of_isInvertible
              X.toRingedSpace L' M' hL' hM'))
            ((TX.map φ).app M ≫ (TX.obj L').map ψ) ≫ (e L' M' hL' hM').hom =
          (e L M hL hM).hom ≫
            ((TY.map (normMapOfCover f N L L' (cov L hL) (cov L' hL') φ)).app
                (normInvertible f N M) ≫
              (TY.obj (normInvertible f N L')).map
                (normMapOfCover f N M M' (cov M hM) (cov M' hM') ψ)) := by
  intro Inv TX TY
  refine ⟨fun L M hL hM => normInvertibleTensorIsoOfCover f N (cov L hL) (cov M hM)
    (cov _ (Stacks.Cohomology.Generators.isInvertible_tensorSheaf_of_isInvertible
      X.toRingedSpace L M hL hM)), ?_⟩
  intro L L' M M' hL hL' hM hM' φ ψ
  have hLM := cov _ (Stacks.Cohomology.Generators.isInvertible_tensorSheaf_of_isInvertible
      X.toRingedSpace L M hL hM)
  have hLM' := cov _ (Stacks.Cohomology.Generators.isInvertible_tensorSheaf_of_isInvertible
      X.toRingedSpace L' M' hL' hM')
  refine hom_ext_of_generators _ _ (ι := TensorChart f L M × TensorChart f L' M')
    (fun i => tensorChartOpen i.1 ⊓ tensorChartOpen i.2)
    (fun i => normTmulGenerator f N hLM i.1 inf_le_left) ?_ ?_
  · intro y
    obtain ⟨c, hc⟩ := Opens.mem_iSup.mp
      (tensorChart_cover (cov L hL) (cov M hM) (show y ∈ (⊤ : Y.Opens) from trivial))
    obtain ⟨c', hc'⟩ := Opens.mem_iSup.mp
      (tensorChart_cover (cov L' hL') (cov M' hM') (show y ∈ (⊤ : Y.Opens) from trivial))
    exact ⟨(c, c'), hc, hc'⟩
  · rintro ⟨c, c'⟩
    dsimp only
    have h : tensorChartOpen c ⊓ tensorChartOpen c' ≤ tensorChartOpen c := inf_le_left
    have h' : tensorChartOpen c ⊓ tensorChartOpen c' ≤ tensorChartOpen c' := inf_le_right
    set A := tensorChartOpen c ⊓ tensorChartOpen c' with hA
    have ha := generatorCoefficient_spec (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ A)
      (tensorChartGenFst c h) (tensorChartGenFst c' h')
    have hb := generatorCoefficient_spec (X := X.toRingedSpace) M M' ψ (f ⁻¹ᵁ A)
      (tensorChartGenSnd c h) (tensorChartGenSnd c' h')
    set a := generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ A)
      (tensorChartGenFst c h) (tensorChartGenFst c' h')
    set b := generatorCoefficient (X := X.toRingedSpace) M M' ψ (f ⁻¹ᵁ A)
      (tensorChartGenSnd c h) (tensorChartGenSnd c' h')
    have hφψ : ((TX.map φ).app M ≫ (TX.obj L').map ψ).val.app (op (f ⁻¹ᵁ A))
        (tmulGenerator (tensorChartGenFst c h) (tensorChartGenSnd c h)).val =
        SMul.smul (a * b)
          (tmulGenerator (tensorChartGenFst c' h') (tensorChartGenSnd c' h')).val :=
      (sheafTensor_map_toTensorSheafSection X.toRingedSpace φ ψ _ _ _).trans
        ((congrArg₂ (fun u v => TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace L' M'
          (op (f ⁻¹ᵁ A)) (u ⊗ₜ v)) ha hb).trans
          (toTensorSheafSection_smul_tmul_smul X.toRingedSpace L' M' _ a b _ _))
    have L1 := normMapOfCover_generator f N _ _ hLM hLM' _ A
      (tmulGenerator (tensorChartGenFst c h) (tensorChartGenSnd c h))
      (tmulGenerator (tensorChartGenFst c' h') (tensorChartGenSnd c' h')) (a * b) hφψ
    have E : ∀ {L M : X.Modules} (hL : HasTrivializingTargetCover f L)
        (hM : HasTrivializingTargetCover f M)
        (hLM : HasTrivializingTargetCover f ((TX.obj L).obj M)) (c : TensorChart f L M)
        (h : A ≤ tensorChartOpen c),
        (normInvertibleTensorIsoOfCover f N hL hM hLM).hom.val.app (op A)
          (normTmulGenerator f N hLM c h).val = (tmulNormGenerator f N hL hM c h).val := by
      intro L M hL hM hLM c h
      rw [← generatorRestrict_normTmulGenerator f N hLM c le_rfl h,
        ← generatorRestrict_tmulNormGenerator f N hL hM c le_rfl h]
      exact isoOfChartGenerators_hom_app_restrict _ _ _ _ _ _ c h
    have R1 := sheafTensor_map_toTensorSheafSection Y.toRingedSpace
      (normMapOfCover f N L L' (cov L hL) (cov L' hL') φ)
      (normMapOfCover f N M M' (cov M hM) (cov M' hM') ψ) (op A)
      (normGenerator f N L (cov L hL) A (tensorChartGenFst c h)).val
      (normGenerator f N M (cov M hM) A (tensorChartGenSnd c h)).val
    have R2 := R1.trans ((congrArg₂ (fun u v => TensorStalkRingedSpace.toTensorSheafSection
        Y.toRingedSpace (normInvertible f N L') (normInvertible f N M') (op A) (u ⊗ₜ v))
        (normMapOfCover_generator f N L L' (cov L hL) (cov L' hL') φ A _ _ a ha)
        (normMapOfCover_generator f N M M' (cov M hM) (cov M' hM') ψ A _ _ b hb)).trans
      (toTensorSheafSection_smul_tmul_smul Y.toRingedSpace _ _ _ (N.app A a) (N.app A b) _ _))
    refine (congrArg (fun z => ((normInvertibleTensorIsoOfCover f N (cov L' hL') (cov M' hM')
      hLM').hom.val.app (op A)).hom z) L1).trans ?_
    refine (((normInvertibleTensorIsoOfCover f N (cov L' hL') (cov M' hM')
      hLM').hom.val.app (op A)).hom.map_smul _ _).trans ?_
    erw [E (cov L' hL') (cov M' hM') hLM' c' h']
    refine Eq.trans ?_ (congrArg (fun z => (((TY.map (normMapOfCover f N L L' (cov L hL)
      (cov L' hL') φ)).app (normInvertible f N M) ≫ (TY.obj (normInvertible f N L')).map
      (normMapOfCover f N M M' (cov M hM) (cov M' hM') ψ)).val.app (op A)).hom z)
      (E (cov L hL) (cov M hM) hLM c h)).symm
    refine Eq.trans ?_ R2.symm
    erw [map_mul]
    rfl

end Tensor

section BaseChange

/-- The chart generator of the glued norm over a chart is the norm of the chart frame. -/
private theorem chartGenerator_eq_normGenerator {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : MorphismNormMap f) (L : X.Modules) (hL : HasTrivializingTargetCover f L)
    (i : NormChart f L) :
    (normTransitionCocycle f N L).chartGenerator (normChart_cover hL) i =
      normGenerator f N L hL i.val (normChartGeneratorOver f L i i.val le_rfl) := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  exact congrArg (fun z => (normGeneratorRatio f N L _
      (normChartGeneratorOver f L j _ inf_le_right) z).val)
    (normChartGeneratorOver_restrict f L i le_rfl inf_le_left).symm

/-- The base-change isomorphism `Stacks.Divisors.pullbackNormInvertibleIso` carries the pullback
of the norm of a chart frame to the norm of the pulled-back chart frame. -/
private theorem pullbackNormInvertibleIso_hom_app {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y) (w : g' ≫ f = f' ≫ g) (N : MorphismNormMap f)
    (N' : MorphismNormMap f')
    (hN : ∀ (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)),
      N'.app (g ⁻¹ᵁ U) (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U))
        (preimage_le_preimage_of_comp_eq w le_rfl) s) = g.app U (N.app U s))
    (L : X.Modules)
    (hLinv : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L)
    (hL : HasTrivializingTargetCover f L)
    (hL' : HasTrivializingTargetCover f' ((RingedSpaceModuleAdjunction.modulePullback
      g'.toLRSHom.toShHom).obj L))
    (i : NormChart f L) {A : Y.Opens} (hiA : A ≤ i.val) :
    (pullbackNormInvertibleIso f f' g' g w N N' hN L hLinv hL hL').hom.val.app (op (g ⁻¹ᵁ A))
        (pullbackGenerator g (normInvertible f N L) (isInvertible_normInvertible f N L hL) A
          (normGenerator f N L hL A (normChartGeneratorOver f L i A hiA))).val =
      (normGenerator f' N' _ hL' (g ⁻¹ᵁ A)
        (generatorRestrict (X := X'.toRingedSpace) _ (preimage_le_preimage_of_comp_eq w le_rfl)
          (pullbackGenerator g' L hLinv (f ⁻¹ᵁ A) (normChartGeneratorOver f L i A hiA)))).val := by
  have hB : g ⁻¹ᵁ A ≤ g ⁻¹ᵁ i.val := ((Opens.map g.base).map (homOfLE hiA)).le
  have step1 : pullbackGenerator g (normInvertible f N L) (isInvertible_normInvertible f N L hL) A
      (normGenerator f N L hL A (normChartGeneratorOver f L i A hiA)) =
      generatorRestrict (X := Y'.toRingedSpace) _ hB
        (pullbackGenerator g (normInvertible f N L) (isInvertible_normInvertible f N L hL) i.val
          ((normTransitionCocycle f N L).chartGenerator (normChart_cover hL) i)) := by
    refine ((pullbackGenerator_restrict g _ _ hiA _).trans
      (congrArg (pullbackGenerator g _ (isInvertible_normInvertible f N L hL) A) ?_)).symm
    exact (congrArg (generatorRestrict (X := Y.toRingedSpace) _ hiA)
        (chartGenerator_eq_normGenerator f N L hL i)).trans
      ((generatorRestrict_normGenerator' f N L hL hiA _).trans
        (congrArg (normGenerator f N L hL A) (normChartGeneratorOver_restrict f L i le_rfl hiA)))
  have hle : f ⁻¹ᵁ A ≤ f ⁻¹ᵁ i.val := ((Opens.map f.base).map (homOfLE hiA)).le
  let L' := (RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom).obj L
  have step2 : generatorRestrict (X := X'.toRingedSpace) L' ((Opens.map f'.base).map
        (homOfLE hB)).le (generatorRestrict (X := X'.toRingedSpace) L'
          (preimage_le_preimage_of_comp_eq w le_rfl)
          (pullbackGenerator g' L hLinv (f ⁻¹ᵁ i.val) (normChartSourceGenerator f L i))) =
      generatorRestrict (X := X'.toRingedSpace) L' (preimage_le_preimage_of_comp_eq w le_rfl)
        (pullbackGenerator g' L hLinv (f ⁻¹ᵁ A) (normChartGeneratorOver f L i A hiA)) := by
    calc _ = generatorRestrict (X := X'.toRingedSpace) L'
          (le_trans ((Opens.map f'.base).map (homOfLE hB)).le
            (preimage_le_preimage_of_comp_eq w le_rfl))
          (pullbackGenerator g' L hLinv (f ⁻¹ᵁ i.val) (normChartSourceGenerator f L i)) :=
          generatorRestrict_trans _ _ _ _
      _ = generatorRestrict (X := X'.toRingedSpace) L'
            (preimage_le_preimage_of_comp_eq w le_rfl)
            (generatorRestrict (X := X'.toRingedSpace) L' ((Opens.map g'.base).map (homOfLE hle)).le
              (pullbackGenerator g' L hLinv (f ⁻¹ᵁ i.val) (normChartSourceGenerator f L i))) :=
          (generatorRestrict_trans _ _ _ _).symm
      _ = _ := congrArg (generatorRestrict (X := X'.toRingedSpace) L'
            (preimage_le_preimage_of_comp_eq w le_rfl))
          (pullbackGenerator_restrict g' L hLinv hle (normChartSourceGenerator f L i))
  rw [step1]
  refine (isoOfChartGenerators_hom_app_restrict _ _ _ _ _ _ i hB).trans ?_
  exact congrArg Subtype.val ((generatorRestrict_normGenerator' f' N' _ hL' hB _).trans
    (congrArg (normGenerator f' N' _ hL' (g ⁻¹ᵁ A)) step2))

/- The norm commutes with arbitrary base change, naturally in the module: the pulled-back
frames form a target-trivializing cover, and the determinant base-change identity
`Stacks.Norm.finiteLocallyFreeNorm_baseChange` identifies the normed transition units and the
normed coefficients of a morphism. -/
private theorem exists_pullback_normInvertible_iso_natural
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f] :
    let N := (Stacks.Norm.finiteLocallyFreeNorm f).toMorphismNormMap
    let Inv : ∀ {Z : Scheme.{u}}, Z.Modules → Prop := fun {Z} L =>
      IsInvertible Z.presheaf (structureSheafRing Z.toRingedSpace).property L
    let cov : ∀ {L : X.Modules}, Inv L → HasTrivializingTargetCover f L := fun {L} hL =>
      @hasTrivializingTargetCover_of_isFinite X Y f
        (Stacks.Morphisms.IsFiniteLocallyFree.isFinite f) L hL
    let Nm : ∀ {L L' : X.Modules} (hL : Inv L) (hL' : Inv L'),
        (L ⟶ L') → (normInvertible f N L ⟶ normInvertible f N L') :=
      fun {L L'} hL hL' φ => normMapOfCover f N L L' (cov hL) (cov hL') φ
    (∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
      (_ : IsPullback g' f' f g) [Stacks.Morphisms.IsFiniteLocallyFree f'],
      let N' := (Stacks.Norm.finiteLocallyFreeNorm f').toMorphismNormMap
      let pullX := RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom
      let cov' : ∀ {L : X.Modules}, Inv L → HasTrivializingTargetCover f' (pullX.obj L) :=
        fun {L} hL => @hasTrivializingTargetCover_of_isInvertible X' Y' f'
          (Stacks.Morphisms.IsFiniteLocallyFree.isFinite f') (pullX.obj L)
          (Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback g' L
            ((isInvertible_iff_algebraicGeometry _ _ L).mp hL))
      let pullY := RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom
      ∃ e : ∀ (L : X.Modules), Inv L →
          (pullY.obj (normInvertible f N L) ≅ normInvertible f' N' (pullX.obj L)),
        ∀ (L L' : X.Modules) (hL : Inv L) (hL' : Inv L') (φ : L ⟶ L'),
          pullY.map (Nm hL hL' φ) ≫ (e L' hL').hom =
            (e L hL).hom ≫
              normMapOfCover f' N' _ _
                (cov' hL) (cov' hL')
                (pullX.map φ)) := by
  intro N Inv cov Nm X' Y' f' g' g sq _ N' pullX cov' pullY
  have w : g' ≫ f = f' ≫ g := sq.w
  have hN : ∀ (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)),
      N'.app (g ⁻¹ᵁ U) (g'.appLE (f ⁻¹ᵁ U) (f' ⁻¹ᵁ (g ⁻¹ᵁ U))
        (preimage_le_preimage_of_comp_eq w le_rfl) s) = g.app U (N.app U s) := by
    obtain ⟨_, h⟩ := Stacks.Norm.finiteLocallyFreeNorm_baseChange f f' g' g sq
    exact h
  refine ⟨fun L hL => pullbackNormInvertibleIso f f' g' g w N N' hN L hL (cov hL) (cov' hL), ?_⟩
  intro L L' hL hL' φ
  refine hom_ext_of_generators _ _ (ι := NormChart f L × NormChart f L')
    (fun k => g ⁻¹ᵁ (k.1.val ⊓ k.2.val))
    (fun k => pullbackGenerator g (normInvertible f N L)
      (isInvertible_normInvertible f N L (cov hL)) _
      (normGenerator f N L (cov hL) _ (normChartGeneratorOver f L k.1 _ inf_le_left))) ?_ ?_
  · intro y
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
      (normChart_cover (cov hL) (show g.base y ∈ (⊤ : Y.Opens) from trivial))
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp
      (normChart_cover (cov hL') (show g.base y ∈ (⊤ : Y.Opens) from trivial))
    exact ⟨(i, j), hi, hj⟩
  · rintro ⟨i, j⟩
    dsimp only
    have hi : i.val ⊓ j.val ≤ i.val := inf_le_left
    have hj : i.val ⊓ j.val ≤ j.val := inf_le_right
    set A := i.val ⊓ j.val with hA
    have ha := generatorCoefficient_spec (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ A)
      (normChartGeneratorOver f L i A hi) (normChartGeneratorOver f L' j A hj)
    set a := generatorCoefficient (X := X.toRingedSpace) L L' φ (f ⁻¹ᵁ A)
      (normChartGeneratorOver f L i A hi) (normChartGeneratorOver f L' j A hj)
    have hkA : f' ⁻¹ᵁ (g ⁻¹ᵁ A) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ A) := preimage_le_preimage_of_comp_eq w le_rfl
    have hφ' : (pullX.map φ).val.app (op (f' ⁻¹ᵁ (g ⁻¹ᵁ A)))
        (generatorRestrict (X := X'.toRingedSpace) _ hkA
          (pullbackGenerator g' L hL (f ⁻¹ᵁ A) (normChartGeneratorOver f L i A hi))).val =
        SMul.smul (g'.appLE (f ⁻¹ᵁ A) (f' ⁻¹ᵁ (g ⁻¹ᵁ A)) hkA a)
          (generatorRestrict (X := X'.toRingedSpace) _ hkA
            (pullbackGenerator g' L' hL' (f ⁻¹ᵁ A) (normChartGeneratorOver f L' j A hj))).val := by
      have nat := congrArg (fun k => k (Stacks.RingedSpace.pullbackUnit g'.toLRSHom.toShHom L
          (op (f ⁻¹ᵁ A)) (normChartGeneratorOver f L i A hi).val))
        (congrArg ModuleCat.Hom.hom ((pullX.map φ).val.naturality (homOfLE hkA).op))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at nat
      change _ = _ at nat
      refine nat.trans ?_
      have h1 := congrArg (fun k => (k.val.app (op (f ⁻¹ᵁ A))).hom
          (normChartGeneratorOver f L i A hi).val)
        ((Stacks.RingedSpace.pullbackAdjunction g'.toLRSHom.toShHom).unit.naturality φ)
      refine (congrArg (fun z => ((pullX.obj L').val.map (homOfLE hkA).op).hom z) h1.symm).trans ?_
      refine (congrArg (fun z => ((pullX.obj L').val.map (homOfLE hkA).op).hom
        ((((Stacks.RingedSpace.pullbackAdjunction g'.toLRSHom.toShHom).unit.app L').val.app
          (op (f ⁻¹ᵁ A))).hom z)) ha).trans ?_
      refine (congrArg (fun z => ((pullX.obj L').val.map (homOfLE hkA).op).hom z)
        ((((Stacks.RingedSpace.pullbackAdjunction g'.toLRSHom.toShHom).unit.app L').val.app
          (op (f ⁻¹ᵁ A))).hom.map_smul _ _)).trans ?_
      exact PresheafOfModules.map_smul _ _ _ _
    have R := normMapOfCover_generator f' N' _ _ (cov' hL) (cov' hL') (pullX.map φ) (g ⁻¹ᵁ A)
      _ _ _ hφ'
    have hpb : (pullY.map (Nm hL hL' φ)).val.app (op (g ⁻¹ᵁ A))
        (pullbackGenerator g _ (isInvertible_normInvertible f N L (cov hL)) A
          (normGenerator f N L (cov hL) A (normChartGeneratorOver f L i A hi))).val =
        SMul.smul (g.app A (N.app A a))
          (pullbackGenerator g _ (isInvertible_normInvertible f N L' (cov hL')) A
            (normGenerator f N L' (cov hL') A (normChartGeneratorOver f L' j A hj))).val := by
      have h1 := congrArg (fun k => (k.val.app (op A)).hom
          (normGenerator f N L (cov hL) A (normChartGeneratorOver f L i A hi)).val)
        ((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.naturality (Nm hL hL' φ))
      refine h1.symm.trans ?_
      refine (congrArg (fun z => (((Stacks.RingedSpace.pullbackAdjunction
        g.toLRSHom.toShHom).unit.app (normInvertible f N L')).val.app (op A)).hom z)
        (normMapOfCover_generator f N L L' (cov hL) (cov hL') φ A _ _ a ha)).trans ?_
      exact (((Stacks.RingedSpace.pullbackAdjunction g.toLRSHom.toShHom).unit.app
        (normInvertible f N L')).val.app (op A)).hom.map_smul _ _
    refine (congrArg (fun z => ((pullbackNormInvertibleIso f f' g' g w N N' hN L' hL' (cov hL')
      (cov' hL')).hom.val.app (op (g ⁻¹ᵁ A))).hom z) hpb).trans ?_
    refine (((pullbackNormInvertibleIso f f' g' g w N N' hN L' hL' (cov hL')
      (cov' hL')).hom.val.app (op (g ⁻¹ᵁ A))).hom.map_smul _ _).trans ?_
    erw [pullbackNormInvertibleIso_hom_app f f' g' g w N N' hN L' hL' (cov hL') (cov' hL') j hj]
    refine Eq.trans ?_ (congrArg (fun z => ((normMapOfCover f' N' _ _ (cov' hL) (cov' hL')
      (pullX.map φ)).val.app (op (g ⁻¹ᵁ A))).hom z)
      (pullbackNormInvertibleIso_hom_app f f' g' g w N N' hN L hL (cov hL) (cov' hL) i hi)).symm
    refine Eq.trans ?_ R.symm
    erw [hN]
    rfl

end BaseChange

end MMP.Internal.FiniteLocallyFreeLineBundleNorm

namespace MMP

open MMP.Internal.FiniteLocallyFreeLineBundleNorm in
/-- **The norm functor of a finite locally free morphism.** For a finite locally free
`f : X ⟶ Y` (of arbitrary, possibly varying or zero, rank) with determinant norm
`N = Stacks.Norm.finiteLocallyFreeNorm f`, the norm `Stacks.Divisors.normInvertible f N` of
invertible modules, acting on morphisms by `Stacks.Divisors.normMapOfCover`,
1. preserves identities and composition, and takes invertible modules to invertible modules;
2. admits isomorphisms `Nm (L ⊗ M) ≅ Nm L ⊗ Nm M` natural in `L` and `M`;
3. takes `𝒪_X` to a module isomorphic to `𝒪_Y`;
4. commutes with arbitrary base change: for every cartesian square `g' ≫ f = f' ≫ g` there are
   isomorphisms `g^* (Nm_f L) ≅ Nm_{f'} (g'^* L)`, natural in `L`. -/
@[mmp "thm_mmp_finite_locally_free_line_bundle_norm"]
public theorem exists_normInvertible_tensorIso_unitIso_pullbackIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Stacks.Morphisms.IsFiniteLocallyFree f] :
    let N := (Stacks.Norm.finiteLocallyFreeNorm f).toMorphismNormMap
    let Inv : ∀ {Z : Scheme.{u}}, Z.Modules → Prop := fun {Z} L =>
      IsInvertible Z.presheaf (structureSheafRing Z.toRingedSpace).property L
    let cov : ∀ {L : X.Modules}, Inv L → HasTrivializingTargetCover f L := fun {L} hL =>
      @hasTrivializingTargetCover_of_isFinite X Y f
        (Stacks.Morphisms.IsFiniteLocallyFree.isFinite f) L hL
    let Nm : ∀ {L L' : X.Modules} (hL : Inv L) (hL' : Inv L'),
        (L ⟶ L') → (normInvertible f N L ⟶ normInvertible f N L') :=
      fun {L L'} hL hL' φ => normMapOfCover f N L L' (cov hL) (cov hL') φ
    let TX := sheafTensor ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩
    let TY := sheafTensor ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩
    -- (1) functoriality, and invertibility of the norm
    (∀ (L : X.Modules) (hL : Inv L), Nm hL hL (𝟙 L) = 𝟙 _) ∧
    (∀ (L L' L'' : X.Modules) (hL : Inv L) (hL' : Inv L') (hL'' : Inv L'')
      (φ : L ⟶ L') (ψ : L' ⟶ L''), Nm hL hL'' (φ ≫ ψ) = Nm hL hL' φ ≫ Nm hL' hL'' ψ) ∧
    (∀ (L : X.Modules), Inv L → Inv (normInvertible f N L)) ∧
    -- (2) the tensor isomorphism, natural in both variables
    (∃ e : ∀ (L M : X.Modules), Inv L → Inv M →
        (normInvertible f N ((TX.obj L).obj M) ≅
          (TY.obj (normInvertible f N L)).obj (normInvertible f N M)),
      ∀ (L L' M M' : X.Modules) (hL : Inv L) (hL' : Inv L') (hM : Inv M) (hM' : Inv M')
        (φ : L ⟶ L') (ψ : M ⟶ M'),
        Nm (Stacks.Cohomology.Generators.isInvertible_tensorSheaf_of_isInvertible X.toRingedSpace
              L M hL hM)
            (Stacks.Cohomology.Generators.isInvertible_tensorSheaf_of_isInvertible X.toRingedSpace
              L' M' hL' hM')
            ((TX.map φ).app M ≫ (TX.obj L').map ψ) ≫ (e L' M' hL' hM').hom =
          (e L M hL hM).hom ≫
            ((TY.map (Nm hL hL' φ)).app (normInvertible f N M) ≫
              (TY.obj (normInvertible f N L')).map (Nm hM hM' ψ))) ∧
    -- (3) the unit isomorphism
    Nonempty (normInvertible f N (SheafOfModules.unit (structureSheafRing X.toRingedSpace)) ≅
      SheafOfModules.unit (structureSheafRing Y.toRingedSpace)) ∧
    -- (4) arbitrary base change, natural in the module
    (∀ {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (g' : X' ⟶ X) (g : Y' ⟶ Y)
      (_ : IsPullback g' f' f g) [Stacks.Morphisms.IsFiniteLocallyFree f'],
      let N' := (Stacks.Norm.finiteLocallyFreeNorm f').toMorphismNormMap
      let pullX := RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom
      let cov' : ∀ {L : X.Modules}, Inv L → HasTrivializingTargetCover f' (pullX.obj L) :=
        fun {L} hL => @hasTrivializingTargetCover_of_isInvertible X' Y' f'
          (Stacks.Morphisms.IsFiniteLocallyFree.isFinite f') (pullX.obj L)
          (Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback g' L
            ((isInvertible_iff_algebraicGeometry _ _ L).mp hL))
      let pullY := RingedSpaceModuleAdjunction.modulePullback g.toLRSHom.toShHom
      ∃ e : ∀ (L : X.Modules), Inv L →
          (pullY.obj (normInvertible f N L) ≅ normInvertible f' N' (pullX.obj L)),
        ∀ (L L' : X.Modules) (hL : Inv L) (hL' : Inv L') (φ : L ⟶ L'),
          pullY.map (Nm hL hL' φ) ≫ (e L' hL').hom =
            (e L hL).hom ≫
              normMapOfCover f' N' _ _
                (cov' hL) (cov' hL')
                (pullX.map φ)) := by
  intro N Inv cov Nm TX TY
  refine ⟨fun L hL => normMapOfCover_id f N L (cov hL),
    fun L L' L'' hL hL' hL'' φ ψ => normMapOfCover_comp f N (cov hL) (cov hL') (cov hL'') φ ψ,
    fun L hL => isInvertible_normInvertible f N L (cov hL), ?_, ?_, ?_⟩
  · exact exists_normInvertible_tensorIso_natural f N (fun _ hL => cov hL)
  · exact nonempty_normInvertible_unitModule_iso f N
      (cov (Stacks.SheafOfModules.isInvertible_unit _ _))
  · exact exists_pullback_normInvertible_iso_natural f

end MMP

end

