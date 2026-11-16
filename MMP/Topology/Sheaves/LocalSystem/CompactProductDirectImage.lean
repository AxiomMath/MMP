module

public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsFromInt
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.ModuleGuitartBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianProperBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalSectionsDerived
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationGlobal

/-!
# Higher direct images from a compact product over a planar domain

Let `F` be a compact Hausdorff space, `D ⊆ ℂ` a connected open set and `p : F × D → D` the
second projection. Cohomology here is cohomology of the constant sheaf: `H^q(F; ℚ)` is the
`q`-th right derived functor of global sections evaluated on the constant sheaf `ℚ_F`, and
`R^q p_* ℚ` is the `q`-th right derived functor of the direct image `p_*` evaluated on
`ℚ_{F × D}`. For every `q`, pulling classes back along the first projection and passing to
global sections of the higher direct image gives a map
`H^q(F; ℚ) ⟶ H^q(F × D; ℚ) ⟶ Γ(D, R^q p_* ℚ)`. The morphism of sheaves
`H^q(F; ℚ)_D ⟶ R^q p_* ℚ` it corresponds to under the adjunction between the constant sheaf
functor and global sections is an isomorphism. In particular, when `H^q(F; ℚ)` is
finite-dimensional, `R^q p_* ℚ` is a local system.

## Main results

* `MMP.Fourfold.isIso_constantSheaf_higherDirectImage_snd`: the constant sheaf `H^q(F; ℚ)_D`
  is isomorphic to `R^q p_* ℚ` through the pullback along the first projection, and
  `R^q p_* ℚ` is a local system when `H^q(F; ℚ)` is finite-dimensional.

## Implementation notes

* `F × D` is the categorical product `F ⨯ D` in `TopCat`, with projections `prod.fst` and
  `prod.snd`; its underlying space is the product space (`TopCat.prodIsoProd`).
* Sheaf cohomology is `CategoryTheory.Functor.rightDerived` of the sections functor
  `(sheafSections _ _).obj (op ⊤)`, and `R^q p_*` is `Functor.rightDerived` of the direct image
  `(Opens.map p).sheafPushforwardContinuous`, both on sheaves of `ℚ`-vector spaces.
* The pullback `H^q(F; ℚ) ⟶ H^q(F × D; ℚ)` is the map induced by the unit
  `ℚ_F ⟶ pr_{F*} ℚ_{F × D}` (adjoint to the unit `ℚ ⟶ Γ(F × D, ℚ)`), followed by the edge map
  `H^q(F, pr_{F*} -) ⟶ H^q(F × D, -)` of the composite `Γ(F, -) ∘ pr_{F*} = Γ(F × D, -)`
  (`Stacks.Cohomology.RightDerivedEdge.edge`). The map `H^q(F × D; ℚ) ⟶ Γ(D, R^q p_* ℚ)` is the
  edge map of the composite `Γ(D, -) ∘ p_* = Γ(F × D, -)`
  (`Stacks.Cohomology.RightDerivedCoEdge.secondEdge`).
* The map `Γ(D, -)`-adjoint to a map `E ⟶ Γ(D, 𝒢)` is
  `(constantSheafAdj _ _ Limits.isTerminalTop).homEquiv`, read backwards.

The comparison is made on resolutions rather than on stalks
(`Proof_lem_mmp_curvels_compact_product`). The square `F × D ⟶ F`, `F × D ⟶ D` over the point
is cartesian and `F ⟶ pt` is proper, so proper base change shows that `p_* pr_F⁻¹ G` is the
constant sheaf `Γ(F, G)_D` and that the higher direct images of `pr_F⁻¹ G` vanish for injective
`G`. For an injective resolution `I` of `ℚ_F`, `pr_F⁻¹ I` is then a `p_*`-acyclic resolution of
`ℚ_{F × D}` with `p_* pr_F⁻¹ I ≅ Γ(F, I)_D`, and the comparison morphism is the cohomology of
this isomorphism of complexes.

## References

* [B. Iversen, *Cohomology of sheaves*], III.1, IV.1 and VII.1.
-/

@[expose] public section

namespace Proof_lem_mmp_curvels_compact_product

open CategoryTheory TopologicalSpace Opposite Limits MMP.Fourfold

section ProperBaseChange

universe u

variable {X X' Y Y' : TopCat.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)

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

/-- For a `ℚ`-algebra `R`, which is flat over `ℤ`, `R ⊗_ℤ -` preserves monomorphisms. -/
private instance [Algebra ℚ R] : (ModuleCat.extendScalarsFromInt.{u} R).PreservesMonomorphisms where
  preserves {M N} f hf := by
    have := IsAddTorsionFree.of_module_rat R
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

/-- A faithful functor preserving zero morphisms reflects zero objects. -/
private theorem isZero_of_isZero_map {C D : Type*} [Category C] [HasZeroMorphisms C]
    [Category D] [HasZeroMorphisms D] (G : C ⥤ D) [G.PreservesZeroMorphisms] [G.Faithful]
    {M : C} (h : IsZero (G.obj M)) : IsZero M := by
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

end ProperBaseChange

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {X Y : TopCat.{0}}

/-- Global sections of a pushforward are global sections. -/
private def pushforwardTopIso (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        (sheafSections (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj (op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (op ⊤) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The inverse image of a constant sheaf is constant. -/
private def pullbackConstIso (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ≅
      constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) :=
  (((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)).ofNatIsoRight
      (pushforwardTopIso f)).leftAdjointUniq (constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop)

/-- A sheaf isomorphic to the constant sheaf of a finite-dimensional space is a local system. -/
private theorem isLocalSystem_of_iso_constantSheaf {G : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    {E : ModuleCat.{0} ℚ} [FiniteDimensional ℚ E]
    (e : (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj E ≅ G) :
    IsLocalSystem G := fun _ =>
  ⟨⊤, trivial, E, inferInstance, ⟨(TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) _).mapIso e.symm ≪≫
    (pullbackConstIso (⊤ : Opens X).inclusion').app E⟩⟩

section Homology

open Stacks.Cohomology.RightDerivedCoEdge

/-- For an adjunction `L ⊣ R` with `L` and `R` left exact, let `b : C ⟶ R E` and
`b' : L C ⟶ E` be morphisms of cochain complexes that are adjoint in every degree. Then the
transpose of `H^q(b)` followed by `H^q(R E) ⟶ R(H^q E)` is `H^q(b')`, read through
`H^q(L C) ⟶ L(H^q C)`. -/
private theorem homologyToMapHomology_comp_homEquiv_symm {A B : Type*} [Category A] [Category B]
    [Abelian A] [Abelian B] {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteLimits R]
    {C : CochainComplex A ℕ} {E : CochainComplex B ℕ}
    (b : C ⟶ (R.mapHomologicalComplex _).obj E) (b' : (L.mapHomologicalComplex _).obj C ⟶ E)
    (h : ∀ k, adj.homEquiv _ _ (b'.f k) = b.f k) (q : ℕ) :
    homologyToMapHomology L C q ≫ (adj.homEquiv _ _).symm
      (HomologicalComplex.homologyMap b q ≫ homologyToMapHomology R E q) =
      HomologicalComplex.homologyMap b' q := by
  rw [← cancel_epi (((L.mapHomologicalComplex _).obj C).homologyπ q),
    homologyπ_comp_homologyToMapHomology_assoc, HomologicalComplex.homologyπ_naturality,
    ← Adjunction.homEquiv_naturality_left_symm, HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_comp_homologyToMapHomology, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm, Iso.inv_comp_eq, mapCyclesIso_hom,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono (E.iCycles q), Category.assoc,
    HomologicalComplex.cyclesMap_i, ← Adjunction.homEquiv_naturality_right_symm,
    Category.assoc]
  have h1 : (mapCyclesIso R E q).inv ≫ R.map (E.iCycles q) =
      ((R.mapHomologicalComplex _).obj E).iCycles q := by
    rw [Iso.inv_comp_eq, mapCyclesIso_hom, mapCycles_i]
  rw [h1, HomologicalComplex.cyclesMap_i, Adjunction.homEquiv_naturality_left_symm,
    mapCycles_i_assoc, ← h, Equiv.symm_apply_apply]

/-- Bracket shuffling for the computation of the comparison map, over variable objects. -/
private theorem comp_comp_hom_inv_comp_eq_of_comp_eq {C : Type*} [Category C]
    {T₀ T₁ T₂ T₃ T₄ T₅ T₆ : C} (a : T₀ ⟶ T₁) (x : T₁ ⟶ T₂) (y : T₂ ⟶ T₃) (k : T₃ ⟶ T₄)
    (k' : T₄ ⟶ T₃) (z : T₃ ⟶ T₅)
    (w : T₅ ⟶ T₆) (hb : T₁ ⟶ T₅) (hk : k ≫ k' = 𝟙 _) (h : x ≫ y ≫ z = hb) :
    a ≫ x ≫ (y ≫ k) ≫ k' ≫ z ≫ w = a ≫ hb ≫ w := by
  simp only [Category.assoc, reassoc_of% hk, ← reassoc_of% h]

/-- The transpose of `i ≫ a` read through an invertible transpose `e` of `u`, when
`i ≫ a = u ≫ P.map k`. -/
private theorem inv_comp_map_comp_homEquiv_symm {A B : Type*} [Category A] [Category B]
    {L : A ⥤ B} {P : B ⥤ A} (adj : L ⊣ P) {M X₀ : A} {N K₀ : B} (e : L.obj M ⟶ N) [IsIso e]
    (i : M ⟶ X₀) (a : X₀ ⟶ P.obj K₀) (u : M ⟶ P.obj N) (k : N ⟶ K₀)
    (he : (adj.homEquiv _ _).symm u = e) (h : i ≫ a = u ≫ P.map k) :
    inv e ≫ L.map i ≫ (adj.homEquiv _ _).symm a = k := by
  rw [← adj.homEquiv_naturality_left_symm, h, adj.homEquiv_naturality_right_symm, he,
    IsIso.inv_hom_id_assoc]

open Stacks.Cohomology Stacks.RightDerivedComp in
/-- **The comparison map is invertible, abstractly.** Let `L ⊣ P` with `L` exact, let
`c ⊣ ΓD` with `c` exact, and let `κ : c ∘ ΓF ⟶ p ∘ L` be invertible and adjoint to `ΓF` of the
unit of `L ⊣ P`, read through `τ : ΓF ∘ P ⟶ ΓD ∘ p`. If `L` carries injectives to `p`-acyclic
objects and the transpose of `u : M ⟶ P N` is invertible, then the morphism
`c (Rᵠ ΓF M) ⟶ Rᵠ p N` adjoint to `Rᵠ ΓF (u)` followed by the edge maps is invertible.

On resolutions `I` of `M` and `K` of `N`, `L I` resolves `N` by `p`-acyclic objects, and the map
is the cohomology of `c ΓF I ≅ p L I ⟶ p K`. -/
private theorem isIso_homEquiv_symm_comparison
    {A B C V : Type*} [Category A] [Category B] [Category C] [Category V]
    [Abelian A] [Abelian B] [Abelian C] [Abelian V]
    [HasInjectiveResolutions A] [HasInjectiveResolutions B] [EnoughInjectives B]
    (P : B ⥤ A) [P.Additive] [P.PreservesInjectiveObjects]
    {L : A ⥤ B} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adjF : L ⊣ P)
    (ΓF : A ⥤ V) [ΓF.Additive]
    (p : B ⥤ C) [p.Additive] [PreservesFiniteLimits p]
    (ΓD : C ⥤ V) [ΓD.Additive] [PreservesFiniteLimits ΓD]
    {c : V ⥤ C} [c.Additive] [PreservesFiniteLimits c] [PreservesFiniteColimits c] (adjD : c ⊣ ΓD)
    (τ : P ⋙ ΓF ⟶ p ⋙ ΓD) (κ : ΓF ⋙ c ⟶ L ⋙ p) (hκiso : ∀ G, IsIso (κ.app G))
    (hκ : ∀ G, adjD.homEquiv _ _ (κ.app G) = ΓF.map (adjF.unit.app G) ≫ τ.app (L.obj G))
    (hacyc : ∀ G : A, Injective G → ∀ n, 0 < n → IsZero ((p.rightDerived n).obj (L.obj G)))
    {M : A} {N : B} (u : M ⟶ P.obj N) [IsIso ((adjF.homEquiv _ _).symm u)] (q : ℕ) :
    IsIso ((adjD.homEquiv _ _).symm ((ΓF.rightDerived q).map u ≫
      (RightDerivedEdge.edge P ΓF q).app N ≫ (NatTrans.rightDerived τ q).app N ≫
      (RightDerivedCoEdge.secondEdge p ΓD q).app N)) := by
  let I := injectiveResolution M
  let K := injectiveResolution N
  let J := injectiveResolution (P.obj N)
  let α : I.cocomplex ⟶ (P.mapHomologicalComplex _).obj K.cocomplex :=
    InjectiveResolution.desc u J I ≫ RightDerivedEdge.resolutionComparison P N
  have hα : I.ι.f 0 ≫ α.f 0 = u ≫ P.map (K.ι.f 0) := by
    rw [HomologicalComplex.comp_f, ← Category.assoc, InjectiveResolution.desc_commutes_zero]
    exact (Category.assoc _ _ _).trans
      (congrArg (u ≫ ·) (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P N))
  let b : (ΓF.mapHomologicalComplex _).obj I.cocomplex ⟶
      (ΓD.mapHomologicalComplex _).obj ((p.mapHomologicalComplex _).obj K.cocomplex) :=
    (ΓF.mapHomologicalComplex _).map α ≫
      (NatTrans.mapHomologicalComplex τ _).app K.cocomplex
  have hθ : (ΓF.rightDerived q).map u ≫
      (RightDerivedEdge.edge P ΓF q).app N ≫ (NatTrans.rightDerived τ q).app N ≫
      (RightDerivedCoEdge.secondEdge p ΓD q).app N =
      (I.isoRightDerivedObj ΓF q).hom ≫ HomologicalComplex.homologyMap b q ≫
        homologyToMapHomology ΓD ((p.mapHomologicalComplex _).obj K.cocomplex) q ≫
        ΓD.map (K.isoRightDerivedObj p q).inv := by
    have e1 := Functor.rightDerived_map_eq ΓF q u (InjectiveResolution.desc u J I)
      (InjectiveResolution.desc_commutes u J I)
    have e2 := RightDerivedEdge.edge_app_eq P ΓF q K J
      (RightDerivedEdge.resolutionComparison P N)
      (RightDerivedEdge.ι_f_zero_comp_resolutionComparison P N)
    have e3 := RightDerivedCoEdge.isoRightDerivedObjComp_inv_comp_secondEdgeApp p ΓD q K
    have e5 := InjectiveResolution.rightDerived_app_eq τ K q
    change _ ≫ _ ≫ _ ≫ RightDerivedCoEdge.secondEdgeApp p ΓD q N = _
    rw [e1, e2, e5]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    erw [e3]
    have hb : HomologicalComplex.homologyMap ((ΓF.mapHomologicalComplex _).map
          (InjectiveResolution.desc u J I)) q ≫
        HomologicalComplex.homologyMap ((ΓF.mapHomologicalComplex _).map
          (RightDerivedEdge.resolutionComparison P N)) q ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex τ _).app K.cocomplex) q =
        HomologicalComplex.homologyMap b q := by
      simp only [b, α, Functor.map_comp, HomologicalComplex.homologyMap_comp, Category.assoc]
    exact comp_comp_hom_inv_comp_eq_of_comp_eq _ _ _ _ _ _ _ _ (Iso.inv_hom_id _) hb
  rw [hθ]
  -- the transpose `β : L I ⟶ K` of `α`
  let β : (L.mapHomologicalComplex _).obj I.cocomplex ⟶ K.cocomplex :=
    { f := fun k => (adjF.homEquiv _ _).symm (α.f k)
      comm' := fun i j _ => by
        change _ = L.map (I.cocomplex.d i j) ≫ _
        rw [← adjF.homEquiv_naturality_left_symm, ← adjF.homEquiv_naturality_right_symm]
        exact congrArg _ (α.comm i j) }
  let κI : (c.mapHomologicalComplex _).obj ((ΓF.mapHomologicalComplex _).obj I.cocomplex) ⟶
      (p.mapHomologicalComplex _).obj ((L.mapHomologicalComplex _).obj I.cocomplex) :=
    { f := fun k => κ.app (I.cocomplex.X k)
      comm' := fun i j _ => (κ.naturality (I.cocomplex.d i j)).symm }
  have : IsIso κI := by
    have : ∀ k, IsIso (κI.f k) := fun k => hκiso _
    exact HomologicalComplex.Hom.isIso_of_components _
  let b' := κI ≫ (p.mapHomologicalComplex _).map β
  have h : ∀ k, adjD.homEquiv _ _ (b'.f k) = b.f k := fun k => by
    change adjD.homEquiv _ _ (κ.app (I.cocomplex.X k) ≫ p.map (β.f k)) =
      ΓF.map (α.f k) ≫ τ.app (K.cocomplex.X k)
    rw [adjD.homEquiv_naturality_right, hκ, Category.assoc]
    erw [← τ.naturality (β.f k)]
    rw [← Category.assoc, Functor.comp_map, ← ΓF.map_comp]
    congr 2
    exact (adjF.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hb' := homologyToMapHomology_comp_homEquiv_symm adjD b b' h q
  -- the augmentation `N[0] ⟶ L I`
  let e := (adjF.homEquiv _ _).symm u
  have hA : ∀ n, 0 < n → IsZero ((L.rightDerived n).obj M) := fun n hn => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ((L.map_isZero (isZero_homology_succ I m)).of_iso
      (asIso (homologyToMapHomology L I.cocomplex (m + 1)))).of_iso
      (I.isoRightDerivedObj L (m + 1))
  have := quasiIso_mapι L I hA
  let ε := (CochainComplex.single₀ B).map (inv e) ≫ mapι L I
  have hβ : ε ≫ β = K.ι := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [ε, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero, mapι_f_zero]
    exact (Category.assoc _ _ _).trans (inv_comp_map_comp_homEquiv_symm adjF e (I.ι.f 0) (α.f 0)
      u (K.ι.f 0) rfl hα)
  have hIK : ∀ n, acyclic p (((L.mapHomologicalComplex _).obj I.cocomplex).X n) :=
    fun n => hacyc _ (I.injective n)
  have hIJ : ∀ n, acyclic p (K.cocomplex.X n) := fun n =>
    have := K.injective n
    acyclic_of_injective p _
  have hpβ := InjectiveResolution.isIso_homologyMap_map_of_desc p (acyclic p)
    (exists_mono_acyclic p) (fun S hS h₁ h₂ => acyclic_shortExact p S hS h₁ h₂) K ε β hβ hIK hIJ q
  have hb'iso : IsIso (HomologicalComplex.homologyMap b' q) := by
    rw [HomologicalComplex.homologyMap_comp]
    infer_instance
  let hcI := @asIso _ _ _ _
    (homologyToMapHomology c ((ΓF.mapHomologicalComplex _).obj I.cocomplex) q)
    (isIso_homologyToMapHomology c ((ΓF.mapHomologicalComplex _).obj I.cocomplex) q)
  have hX : (adjD.homEquiv _ _).symm (HomologicalComplex.homologyMap b q ≫
      homologyToMapHomology ΓD ((p.mapHomologicalComplex _).obj K.cocomplex) q) =
      hcI.inv ≫ HomologicalComplex.homologyMap b' q :=
    hcI.eq_inv_comp.2 hb'
  have hfin : (adjD.homEquiv _ _).symm ((I.isoRightDerivedObj ΓF q).hom ≫
      HomologicalComplex.homologyMap b q ≫
        homologyToMapHomology ΓD ((p.mapHomologicalComplex _).obj K.cocomplex) q ≫
        ΓD.map (K.isoRightDerivedObj p q).inv) =
      c.map (I.isoRightDerivedObj ΓF q).hom ≫
        (hcI.inv ≫ HomologicalComplex.homologyMap b' q) ≫
          (K.isoRightDerivedObj p q).inv := by
    refine (adjD.homEquiv_naturality_left_symm _ _).trans (congrArg (c.map _ ≫ ·) ?_)
    refine (congrArg _ (Category.assoc _ _ _).symm).trans ?_
    exact (adjD.homEquiv_naturality_right_symm _ _).trans (congrArg (· ≫ _) hX)
  rw [hfin]
  exact IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' (IsIso.comp_isIso' (Iso.isIso_inv hcI) hb'iso) (Iso.isIso_inv _))

end Homology

section Point

/-- On the point, a covering sieve of `⊤` contains the identity. -/
private theorem sieve_id_mem_of_mem_punit {S : Sieve (⊤ : Opens (TopCat.of PUnit.{1}))}
    (hS : S ∈ Opens.grothendieckTopology (TopCat.of PUnit.{1}) ⊤) : S (𝟙 ⊤) := by
  obtain ⟨V, f, hf, hV⟩ := hS PUnit.unit trivial
  have : V = ⊤ := by
    ext x
    cases x
    simpa using hV
  subst this
  rwa [Subsingleton.elim f (𝟙 _)] at hf

/-- On the point, sheafification does not change sections over `⊤`: `toSheafify` is locally
bijective, and the only covering sieve of `⊤` is the maximal one. -/
private theorem isIso_toSheafify_app_top (P : (Opens (TopCat.of PUnit.{1}))ᵒᵖ ⥤ ModuleCat.{0} ℚ) :
    IsIso ((toSheafify (Opens.grothendieckTopology (TopCat.of PUnit.{1})) P).app (op ⊤)) := by
  suffices h : IsIso ((forget (ModuleCat ℚ)).map
      ((toSheafify (Opens.grothendieckTopology (TopCat.of PUnit.{1})) P).app (op ⊤))) from
    isIso_of_reflects_iso _ (forget (ModuleCat ℚ))
  rw [isIso_iff_bijective]
  constructor
  · intro x y h
    have := sieve_id_mem_of_mem_punit (Presheaf.equalizerSieve_mem
      (Opens.grothendieckTopology (TopCat.of PUnit.{1})) (toSheafify _ P) x y h)
    simpa using this
  · intro s
    obtain ⟨t, ht⟩ := sieve_id_mem_of_mem_punit (Presheaf.imageSieve_mem
      (Opens.grothendieckTopology (TopCat.of PUnit.{1})) (toSheafify _ P) s)
    exact ⟨t, by simpa using ht⟩

/-- **Every sheaf on the point is constant**: the counit of the constant sheaf adjunction is
invertible. Over `⊥` both sides are terminal; over `⊤` it is inverse to the unit, which is
`toSheafify` over `⊤`. -/
private theorem isIso_constantSheafAdj_counit_app_punit
    (H : Sheaf (Opens.grothendieckTopology (TopCat.of PUnit.{1})) (ModuleCat.{0} ℚ)) :
    IsIso ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of PUnit.{1})) (ModuleCat.{0} ℚ)
      isTerminalTop).counit.app H) := by
  have hunit : ∀ M, IsIso ((constantSheafAdj (Opens.grothendieckTopology (TopCat.of PUnit.{1}))
      (ModuleCat.{0} ℚ) isTerminalTop).unit.app M) := fun M => by
    have := isIso_toSheafify_app_top ((Functor.const _).obj M)
    simp only [constantSheafAdj, Adjunction.comp_unit_app]
    refine IsIso.comp_isIso' ?_ ?_
    · exact inferInstanceAs (IsIso ((Functor.constCompEvaluationObj _ _).hom.app M))
    · simp only [sheafificationAdjunction_unit_app, evaluation_obj_map]
      exact this
  have htop : IsIso (((constantSheafAdj (Opens.grothendieckTopology (TopCat.of PUnit.{1}))
      (ModuleCat.{0} ℚ) isTerminalTop).counit.app H).hom.app (op ⊤)) :=
    IsIso.of_isIso_fac_left ((constantSheafAdj _ _ isTerminalTop).right_triangle_components H)
  suffices h : IsIso ((sheafToPresheaf _ _).map ((constantSheafAdj
      (Opens.grothendieckTopology (TopCat.of PUnit.{1})) (ModuleCat.{0} ℚ)
      isTerminalTop).counit.app H)) from isIso_of_reflects_iso _ (sheafToPresheaf _ _)
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun U => ?_
  obtain ⟨V⟩ := U
  rcases V.eq_bot_or_top with rfl | rfl
  · have h1 := TopCat.Sheaf.isTerminalOfEmpty (C := ModuleCat.{0} ℚ) H
    have h2 := TopCat.Sheaf.isTerminalOfEmpty (C := ModuleCat.{0} ℚ)
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of PUnit.{1})) (ModuleCat.{0} ℚ)).obj
        (((sheafSections _ _).obj (op ⊤)).obj H))
    exact ⟨h2.from _, h2.hom_ext _ _, h1.hom_ext _ _⟩
  · exact htop

end Point

/-- Let `m : g⁻¹ f_* G ⟶ p_* L G` be a base change morphism, transposing to `f_*` of the unit of
`L ⊣ L_*` read through `e`, and let `κ : c_D (Γ_pt (f_* G)) ⟶ p_* L G` transpose to `Γ_pt` of the
same map. If `m` and the counit of `c_pt ⊣ Γ_pt` at `f_* G` are invertible, so is `κ`: it is
`m` after `g⁻¹` of that counit and the comparison `c_D ≅ c_pt ⋙ g⁻¹` of left adjoints. -/
private theorem isIso_of_mate_of_isIso_counit {A B P Dc V : Type*} [Category A] [Category B]
    [Category P] [Category Dc] [Category V]
    {fs : A ⥤ P} {gi : P ⥤ Dc} {gs : Dc ⥤ P} (aG : gi ⊣ gs)
    {Li : A ⥤ B} {Ls : B ⥤ A} (aF : Li ⊣ Ls) {ps : B ⥤ Dc}
    (e : Ls ⋙ fs ≅ ps ⋙ gs)
    {cP : V ⥤ P} {ΓP : P ⥤ V} (aP : cP ⊣ ΓP) {cD : V ⥤ Dc} {ΓD : Dc ⥤ V} (aD : cD ⊣ ΓD)
    (eD : gs ⋙ ΓP ≅ ΓD) (G : A) (m : gi.obj (fs.obj G) ⟶ ps.obj (Li.obj G))
    (hm : aG.unit.app (fs.obj G) ≫ gs.map m = fs.map (aF.unit.app G) ≫ e.hom.app (Li.obj G))
    (hmiso : IsIso m) (hε : IsIso (aP.counit.app (fs.obj G)))
    (κ : cD.obj (ΓP.obj (fs.obj G)) ⟶ ps.obj (Li.obj G))
    (hκ : aD.homEquiv _ _ κ =
      ΓP.map (fs.map (aF.unit.app G) ≫ e.hom.app (Li.obj G)) ≫ eD.hom.app _) :
    IsIso κ := by
  let adj1 := (aP.comp aG).ofNatIsoRight eD
  have key : κ = (aD.leftAdjointUniq adj1).hom.app _ ≫
      gi.map (aP.counit.app (fs.obj G)) ≫ m := by
    apply (aD.homEquiv _ _).injective
    rw [hκ, aD.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    simp only [adj1, Adjunction.ofNatIsoRight]
    have h2 : aG.unit.app (cP.obj (ΓP.obj (fs.obj G))) ≫
        gs.map (gi.map (aP.counit.app (fs.obj G)) ≫ m) =
        aP.counit.app _ ≫ fs.map (aF.unit.app G) ≫ e.hom.app _ := by
      rw [gs.map_comp, ← Category.assoc, ← Functor.comp_map gi gs, ← aG.unit.naturality,
        Category.assoc]
      exact congrArg (aP.counit.app _ ≫ ·) hm
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
      Category.assoc]
    rw [← eD.hom.naturality, Functor.comp_map, ← ΓP.map_comp_assoc, h2]
    simp
  rw [key]
  infer_instance

section Product

variable (F D' : TopCat.{0})

/-- The product `F × D'` is the fibre product of `F` and `D'` over the point. -/
private theorem isPullback_prod :
    IsPullback (prod.fst : F ⨯ D' ⟶ F) prod.snd (TopCat.isTerminalPUnit.from F)
      (TopCat.isTerminalPUnit.from D') :=
  IsPullback.of_is_product' (prodIsProd F D') TopCat.isTerminalPUnit

/-- A compact Hausdorff space maps properly to the point. -/
private theorem isProperMap_toPUnit [CompactSpace F] [T2Space F] :
    StacksDraft.Topology.IsProperMap.{0, 0, 0} (TopCat.isTerminalPUnit.from F).hom :=
  ⟨T2Space.isSeparatedMap _,
    ((TopCat.isTerminalPUnit.from F).hom.continuous.isProperMap).isUniversallyClosedMap⟩

/-- The comparison `Γ(F, G)_{D'} ⟶ p_* pr_F⁻¹ G` of sheaves on `D'`, transpose of the pullback
`Γ(F, G) ⟶ Γ(F × D', pr_F⁻¹ G)` of sections. -/
private def constBaseChange :
    (sheafSections (Opens.grothendieckTopology F) (ModuleCat.{0} ℚ)).obj (op ⊤) ⋙
        constantSheaf (Opens.grothendieckTopology D') (ModuleCat.{0} ℚ) ⟶
      TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (prod.fst : F ⨯ D' ⟶ F) ⋙
        TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (prod.snd : F ⨯ D' ⟶ D') where
  app G := ((constantSheafAdj (Opens.grothendieckTopology D') (ModuleCat.{0} ℚ)
      isTerminalTop).homEquiv _ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)
        (prod.snd : F ⨯ D' ⟶ D')).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (prod.fst : F ⨯ D' ⟶ F)).obj G))).symm
    (((sheafSections (Opens.grothendieckTopology F) (ModuleCat.{0} ℚ)).obj (op ⊤)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ)
        (prod.fst : F ⨯ D' ⟶ F)).unit.app G))
  naturality G G' φ := by
    apply ((constantSheafAdj (Opens.grothendieckTopology D') (ModuleCat.{0} ℚ)
      isTerminalTop).homEquiv _ _).injective
    refine ((constantSheafAdj (Opens.grothendieckTopology D') (ModuleCat.{0} ℚ)
      isTerminalTop).homEquiv_naturality_left _ _).trans ?_
    refine (congrArg (_ ≫ ·) (Equiv.apply_symm_apply _ _)).trans (Eq.trans ?_
      (((constantSheafAdj (Opens.grothendieckTopology D') (ModuleCat.{0} ℚ)
        isTerminalTop).homEquiv_naturality_right _ _).trans
          (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _))).symm)
    exact ((Functor.map_comp _ _ _).symm.trans (congrArg _
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ)
        (prod.fst : F ⨯ D' ⟶ F)).unit.naturality φ))).trans (Functor.map_comp _ _ _)

private theorem homEquiv_constBaseChange_app (G : TopCat.Sheaf (ModuleCat.{0} ℚ) F) :
    (constantSheafAdj (Opens.grothendieckTopology D') (ModuleCat.{0} ℚ)
      isTerminalTop).homEquiv _ _ ((constBaseChange F D').app G) =
    ((sheafSections (Opens.grothendieckTopology F) (ModuleCat.{0} ℚ)).obj (op ⊤)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ)
        (prod.fst : F ⨯ D' ⟶ F)).unit.app G) :=
  Equiv.apply_symm_apply _ _

/-- For compact Hausdorff `F`, the comparison `constBaseChange F D'` is an isomorphism at every
sheaf `G` on `F` (underived proper base change for `F × D' ⟶ D'`). -/
private theorem isIso_constBaseChange_app [CompactSpace F] [T2Space F]
    (G : TopCat.Sheaf (ModuleCat.{0} ℚ) F) : IsIso ((constBaseChange F D').app G) := by
  have hcart := isPullback_prod F D'
  let mt := Stacks.Cohomology.BaseChange.mate
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (TopCat.isTerminalPUnit.from D'))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (prod.fst : F ⨯ D' ⟶ F))
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (TopCat.isTerminalPUnit.from F))
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (prod.snd : F ⨯ D' ⟶ D'))
    (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)) hcart.w))
  have hm : IsIso mt := isIso_moduleSheafBaseChange_of_properMap (TopCat.isTerminalPUnit.from F)
    prod.snd (TopCat.isTerminalPUnit.from D') prod.fst hcart (isProperMap_toPUnit F) ℚ
  refine isIso_of_mate_of_isIso_counit
    (fs := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (TopCat.isTerminalPUnit.from F))
    (ps := TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (prod.snd : F ⨯ D' ⟶ D'))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (TopCat.isTerminalPUnit.from D'))
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (prod.fst : F ⨯ D' ⟶ F))
    (eqToIso (congrArg (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)) hcart.w))
    (constantSheafAdj (Opens.grothendieckTopology (TopCat.of PUnit.{1})) (ModuleCat.{0} ℚ)
      isTerminalTop)
    (constantSheafAdj (Opens.grothendieckTopology D') (ModuleCat.{0} ℚ) isTerminalTop)
    (pushforwardTopIso (TopCat.isTerminalPUnit.from D')) G (mt.app G)
    (Stacks.Cohomology.BaseChange.unit_comp_map_mate _ _ _ _ _ G)
    (NatIso.isIso_app_of_isIso mt G) (isIso_constantSheafAdj_counit_app_punit _) _ ?_
  refine (homEquiv_constBaseChange_app F D' G).trans ?_
  rfl

/-- The inverse image along `pr_F` of an injective sheaf is acyclic for the direct image along
`p : F × D' ⟶ D'`: proper base change along `F ⟶ pt`. -/
private theorem isZero_rightDerived_pushforward_snd_pullback_fst [CompactSpace F] [T2Space F]
    (G : TopCat.Sheaf (ModuleCat.{0} ℚ) F) (hG : Injective G) (n : ℕ) (hn : 0 < n) :
    letI : (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (prod.snd : F ⨯ D' ⟶ D')).Additive :=
      (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) _).additive_of_preserves_binary_products
    IsZero (((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (prod.snd : F ⨯ D' ⟶ D')).rightDerived
      n).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (prod.fst : F ⨯ D' ⟶ F)).obj G)) := by
  have : (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (prod.snd : F ⨯ D' ⟶ D')).Additive :=
    (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) _).additive_of_preserves_binary_products
  have : EnoughInjectives (TopCat.Sheaf (ModuleCat.{0} ℚ) (F ⨯ D')) :=
    IsGrothendieckAbelian.enoughInjectives
  have hpl : PreservesFiniteLimits (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ)
      (prod.snd : F ⨯ D' ⟶ D')) :=
    have := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ)
      (prod.snd : F ⨯ D' ⟶ D')).rightAdjoint_preservesLimits
    inferInstance
  exact (Stacks.Cohomology.LerayDegreewise.rightAcyclic_iff_isZero_rightDerived _ _).1
    (rightAcyclic_pushforward_pullback_of_injective_module (TopCat.isTerminalPUnit.from F)
      prod.snd (TopCat.isTerminalPUnit.from D') prod.fst (isPullback_prod F D')
      (isProperMap_toPUnit F) ℚ G hG) n hn

end Product

/-- For adjunctions `F ⊣ G`, `H ⊣ I`, `K ⊣ Γ` and `e : I ⋙ G ≅ Γ`, the comparison
`H F ≅ K` of left adjoints of `Γ` is, at `x`, the double transpose of the unit of `K ⊣ Γ`. -/
private theorem homEquiv_symm_eq_leftAdjointUniq {C D E : Type*} [Category C] [Category D]
    [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} {K : C ⥤ E} {Γ : E ⥤ C}
    (a₁ : F ⊣ G) (a₂ : H ⊣ I) (e : I ⋙ G ≅ Γ) (a : K ⊣ Γ) (x : C)
    (u : x ⟶ G.obj (I.obj (K.obj x))) (hu : u ≫ e.hom.app _ = a.unit.app x) :
    (a₂.homEquiv _ _).symm ((a₁.homEquiv _ _).symm u) =
      (((a₁.comp a₂).ofNatIsoRight e).leftAdjointUniq a).hom.app x := by
  apply (((a₁.comp a₂).ofNatIsoRight e).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, ← hu]
  simp only [Adjunction.ofNatIsoRight, Adjunction.homEquiv_unit, NatTrans.comp_app,
    Adjunction.comp_unit_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← e.hom.naturality, Functor.comp_map, ← G.map_comp_assoc, ← a₂.homEquiv_unit,
    Equiv.apply_symm_apply, ← Category.assoc, ← a₁.homEquiv_unit, Equiv.apply_symm_apply]

/-- The transpose along `f⁻¹ ⊣ f_*` of the canonical map `ℚ_Y ⟶ f_* ℚ_X` is invertible. -/
private theorem isIso_homEquiv_symm_constUnit (f : X ⟶ Y) (M : ModuleCat.{0} ℚ) :
    IsIso (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).homEquiv _ _).symm
      (((constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) isTerminalTop).homEquiv
        _ ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f).obj
          ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj M))).symm
        ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) isTerminalTop).unit.app
          M))) := by
  have h := homEquiv_symm_eq_leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) isTerminalTop)
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f) (pushforwardTopIso f)
    (constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) isTerminalTop) M
    ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) isTerminalTop).unit.app M)
    (Category.comp_id _)
  exact (congrArg IsIso h).mpr (Iso.isIso_hom ((pullbackConstIso f).app M))

end

open Stacks.Cohomology in
/-- For compact Hausdorff `F`, the morphism `H^q(F; ℚ)_D ⟶ R^q p_* ℚ` adjoint to the pullback
along `pr_F` followed by the edge map to `Γ(D, R^q p_* ℚ)` is an isomorphism. -/
private theorem isIso_comparison (F : TopCat.{0}) [CompactSpace F] [T2Space F] (D : TopCat.{0})
    (q : ℕ) :
    let p : F ⨯ D ⟶ D := prod.snd
    let prF : F ⨯ D ⟶ F := prod.fst
    let ℚF := (constantSheaf (Opens.grothendieckTopology F) (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)
    let ℚX := (constantSheaf (Opens.grothendieckTopology ↑(F ⨯ D)) (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)
    let ΓF := (sheafSections (Opens.grothendieckTopology F) (ModuleCat.{0} ℚ)).obj (op ⊤)
    let ΓD := (sheafSections (Opens.grothendieckTopology D) (ModuleCat.{0} ℚ)).obj
      (op ⊤)
    letI : (Opens.map p).IsContinuous (Opens.grothendieckTopology D)
        (Opens.grothendieckTopology ↑(F ⨯ D)) :=
      Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map p)
        (coverPreserving_opens_map p)
    let prF_ := (Opens.map prF).sheafPushforwardContinuous (ModuleCat.{0} ℚ)
      (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ D))
    let p_ := (Opens.map p).sheafPushforwardContinuous (ModuleCat.{0} ℚ)
      (Opens.grothendieckTopology D) (Opens.grothendieckTopology ↑(F ⨯ D))
    letI : prF_.PreservesInjectiveObjects :=
      haveI : PreservesFiniteLimits ((Opens.map prF).sheafPullback (ModuleCat.{0} ℚ)
          (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ D))) := by
        apply Functor.sheafPullbackConstruction.preservesFiniteLimits
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        ((Opens.map prF).sheafAdjunctionContinuous (ModuleCat.{0} ℚ)
          (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ D)))
    let u : ℚF ⟶ prF_.obj ℚX :=
      ((constantSheafAdj _ _ isTerminalTop).homEquiv _ _).symm
        ((constantSheafAdj (Opens.grothendieckTopology ↑(F ⨯ D)) _ isTerminalTop).unit.app
          (ModuleCat.of ℚ ℚ))
    let θ : (ΓF.rightDerived q).obj ℚF ⟶ ΓD.obj ((p_.rightDerived q).obj ℚX) :=
      (ΓF.rightDerived q).map u ≫ (RightDerivedEdge.edge prF_ ΓF q).app ℚX ≫
        (RightDerivedCoEdge.secondEdge p_ ΓD q).app ℚX
    IsIso (((constantSheafAdj (Opens.grothendieckTopology D) (ModuleCat.{0} ℚ)
        isTerminalTop).homEquiv _ _).symm θ) := by
  intro p prF ℚF ℚX ΓF ΓD prF_ p_ u θ
  let : (Opens.map p).IsContinuous (Opens.grothendieckTopology D)
      (Opens.grothendieckTopology ↑(F ⨯ D)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map p)
      (coverPreserving_opens_map p)
  have : PreservesFiniteLimits ((Opens.map prF).sheafPullback (ModuleCat.{0} ℚ)
      (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ D))) := by
    apply Functor.sheafPullbackConstruction.preservesFiniteLimits
  have : prF_.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      ((Opens.map prF).sheafAdjunctionContinuous (ModuleCat.{0} ℚ)
        (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ D)))
  let adjF := (Opens.map prF).sheafAdjunctionContinuous (ModuleCat.{0} ℚ)
    (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ D))
  let adjD := constantSheafAdj (Opens.grothendieckTopology D) (ModuleCat.{0} ℚ)
    isTerminalTop
  have : PreservesFiniteColimits ((Opens.map prF).sheafPullback (ModuleCat.{0} ℚ)
      (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ D))) :=
    have := adjF.leftAdjoint_preservesColimits
    inferInstance
  have : PreservesFiniteColimits (constantSheaf (Opens.grothendieckTopology D)
      (ModuleCat.{0} ℚ)) :=
    have := adjD.leftAdjoint_preservesColimits
    inferInstance
  have : p_.IsRightAdjoint := ((Opens.map p).sheafAdjunctionContinuous (ModuleCat.{0} ℚ)
      (Opens.grothendieckTopology D)
      (Opens.grothendieckTopology ↑(F ⨯ D))).isRightAdjoint
  have : PreservesFiniteLimits p_ := inferInstance
  have : ((Opens.map prF).sheafPullback (ModuleCat.{0} ℚ) (Opens.grothendieckTopology F)
      (Opens.grothendieckTopology ↑(F ⨯ D))).Additive :=
    Functor.additive_of_preserves_binary_products _
  let τ₀ : prF_ ⋙ ΓF ⟶ p_ ⋙ ΓD := 𝟙 (prF_ ⋙ ΓF)
  have hκ : ∀ G, adjD.homEquiv _ _ ((constBaseChange F D).app G) =
      ΓF.map (adjF.unit.app G) ≫ τ₀.app _ := fun G =>
    (homEquiv_constBaseChange_app F D G).trans (Category.comp_id _).symm
  have hacyc : ∀ G : TopCat.Sheaf (ModuleCat.{0} ℚ) F, Injective G → ∀ n, 0 < n →
      IsZero ((p_.rightDerived n).obj (((Opens.map prF).sheafPullback (ModuleCat.{0} ℚ)
        (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ D))).obj G)) :=
    fun G hG => isZero_rightDerived_pushforward_snd_pullback_fst F D G hG
  have : IsIso ((adjF.homEquiv _ _).symm u) :=
    isIso_homEquiv_symm_constUnit prF (ModuleCat.of ℚ ℚ)
  have key := isIso_homEquiv_symm_comparison prF_ adjF ΓF p_ ΓD adjD
    τ₀ (constBaseChange F D) (isIso_constBaseChange_app F _) hκ hacyc u q
  have hτ : (NatTrans.rightDerived τ₀ q).app ℚX = 𝟙 _ :=
    congrArg (fun t => t.app ℚX) (NatTrans.rightDerived_id (prF_ ⋙ ΓF) q)
  rw [hτ] at key
  exact (congrArg (fun t => IsIso ((adjD.homEquiv _ _).symm ((ΓF.rightDerived q).map u ≫
    (RightDerivedEdge.edge prF_ ΓF q).app ℚX ≫ t)))
      (Category.id_comp ((RightDerivedCoEdge.secondEdge p_ ΓD q).app ℚX))).mp key

end Proof_lem_mmp_curvels_compact_product

open CategoryTheory TopologicalSpace Opposite Limits
open Proof_lem_mmp_curvels_compact_product

namespace MMP.Fourfold

open Stacks.Cohomology in
/-- **Higher direct images from a compact product.** Let `F` be a compact Hausdorff space,
`D ⊆ ℂ` a connected open set, and `p : F × D → D` the projection. For every `q`, the morphism
`H^q(F; ℚ)_D ⟶ R^q p_* ℚ` of sheaves of `ℚ`-vector spaces adjoint to the composite of the
pullback `H^q(F; ℚ) ⟶ H^q(F × D; ℚ)` along the first projection with
`H^q(F × D; ℚ) ⟶ Γ(D, R^q p_* ℚ)` is an isomorphism; consequently `R^q p_* ℚ` is a local
system whenever `H^q(F; ℚ)` is finite-dimensional. Here `H^q` is cohomology of the constant
sheaf `ℚ` and `R^q p_*` the `q`-th right derived functor of `p_*`. -/
@[mmp "lem_mmp_curvels_compact_product"]
public theorem isIso_constantSheaf_higherDirectImage_snd (F : TopCat.{0}) [CompactSpace F]
    [T2Space F] (D : Opens ℂ) (_hD : IsConnected (D : Set ℂ)) (q : ℕ) :
    let p : F ⨯ TopCat.of D ⟶ TopCat.of D := prod.snd
    let prF : F ⨯ TopCat.of D ⟶ F := prod.fst
    let ℚF := (constantSheaf (Opens.grothendieckTopology F) (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)
    let ℚX := (constantSheaf (Opens.grothendieckTopology ↑(F ⨯ TopCat.of D)) (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)
    let ΓF := (sheafSections (Opens.grothendieckTopology F) (ModuleCat.{0} ℚ)).obj (op ⊤)
    let ΓD := (sheafSections (Opens.grothendieckTopology (TopCat.of D)) (ModuleCat.{0} ℚ)).obj
      (op ⊤)
    letI : (Opens.map p).IsContinuous (Opens.grothendieckTopology (TopCat.of D))
        (Opens.grothendieckTopology ↑(F ⨯ TopCat.of D)) :=
      Functor.isContinuous_of_coverPreserving (compatiblePreserving_opens_map p)
        (coverPreserving_opens_map p)
    let prF_ := (Opens.map prF).sheafPushforwardContinuous (ModuleCat.{0} ℚ)
      (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ TopCat.of D))
    let p_ := (Opens.map p).sheafPushforwardContinuous (ModuleCat.{0} ℚ)
      (Opens.grothendieckTopology (TopCat.of D)) (Opens.grothendieckTopology ↑(F ⨯ TopCat.of D))
    letI : prF_.PreservesInjectiveObjects :=
      haveI : PreservesFiniteLimits ((Opens.map prF).sheafPullback (ModuleCat.{0} ℚ)
          (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ TopCat.of D))) := by
        apply Functor.sheafPullbackConstruction.preservesFiniteLimits
      Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
        ((Opens.map prF).sheafAdjunctionContinuous (ModuleCat.{0} ℚ)
          (Opens.grothendieckTopology F) (Opens.grothendieckTopology ↑(F ⨯ TopCat.of D)))
    let u : ℚF ⟶ prF_.obj ℚX :=
      ((constantSheafAdj _ _ isTerminalTop).homEquiv _ _).symm
        ((constantSheafAdj (Opens.grothendieckTopology ↑(F ⨯ TopCat.of D)) _ isTerminalTop).unit.app
          (ModuleCat.of ℚ ℚ))
    let θ : (ΓF.rightDerived q).obj ℚF ⟶ ΓD.obj ((p_.rightDerived q).obj ℚX) :=
      (ΓF.rightDerived q).map u ≫ (RightDerivedEdge.edge prF_ ΓF q).app ℚX ≫
        (RightDerivedCoEdge.secondEdge p_ ΓD q).app ℚX
    IsIso (((constantSheafAdj (Opens.grothendieckTopology (TopCat.of D)) (ModuleCat.{0} ℚ)
        isTerminalTop).homEquiv _ _).symm θ) ∧
      (FiniteDimensional ℚ ((ΓF.rightDerived q).obj ℚF) →
        IsLocalSystem ((p_.rightDerived q).obj ℚX)) := by
  intro p prF ℚF ℚX ΓF ΓD prF_ p_ u θ
  have h := isIso_comparison F (TopCat.of D) q
  refine ⟨h, fun _ => ?_⟩
  exact isLocalSystem_of_iso_constantSheaf (@asIso _ _ _ _ _ h)

end MMP.Fourfold

end
