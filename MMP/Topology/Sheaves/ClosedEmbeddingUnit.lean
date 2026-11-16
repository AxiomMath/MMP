module

public import StacksFrontier.Topology.Sheaves.Functors.Pullback.UnitOnSections
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# The unit `F ⟶ i_* i⁻¹ F` of a closed embedding

Let `i : Z → X` be a closed embedding and `F` a sheaf of `R`-modules on `X`. The unit
`F ⟶ i_* i⁻¹ F` of the inverse-image/direct-image adjunction is an isomorphism on the stalks at
the points of `i(Z)`, and the stalks of `i_* i⁻¹ F` vanish off `i(Z)`. Hence the unit is an
epimorphism, and a morphism `a : F ⟶ G` whose stalks vanish at every point off `i(Z)` factors
through it: `a` kills the kernel of the unit, whose stalks vanish on `i(Z)`, because a morphism of
sheaves all of whose stalks vanish is zero.

For the constant sheaf `F = R_X` this says that a section of `G` over `X` which vanishes off `Z`
defines a morphism `i_* R_Z ⟶ G`; this is how a class with supports in `Z` is turned into a
morphism out of `i_* R_Z`.

## Main results

* `MMP.Topology.isIso_stalkFunctor_map_unit`: at `i z` the stalk of the unit is invertible, for
  any inducing map `i`.
* `MMP.Topology.isZero_stalk_pushforward_of_notMem_range`: the stalks of `i_* G` vanish off the
  closed set `i(Z)`.
* `MMP.Topology.epi_unit_of_isClosedEmbedding`: the unit is an epimorphism.
* `MMP.Topology.exists_unit_comp_eq_of_isClosedEmbedding`: a morphism `F ⟶ G` whose stalks
  vanish off `i(Z)` factors through the unit.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace Opposite

universe u

namespace MMP.Topology

variable {R : Type u} [Ring R] {X Z : TopCat.{u}}

/-- On the stalk at `i z`, the unit `F ⟶ i_* i⁻¹ F` followed by the comparison
`(i_* G)_{i z} ⟶ G_z` is the stalk comparison `F_{i z} ⟶ (i⁻¹ F)_z`. -/
lemma stalkFunctor_map_unit_comp_stalkPushforward (i : Z ⟶ X) (F : X.Sheaf (ModuleCat.{u} R))
    (z : Z) :
    (TopCat.Presheaf.stalkFunctor _ (i z)).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) i).unit.app F).hom ≫
      TopCat.Presheaf.stalkPushforward _ i
        ((TopCat.Sheaf.pullback (ModuleCat.{u} R) i).obj F).presheaf z =
      Stacks.Topology.ambientStalkHom i F z := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  ext s
  have h := TopCat.Presheaf.stalkPushforward_germ_apply (ModuleCat.{u} R) i
    ((TopCat.Sheaf.pullback (ModuleCat.{u} R) i).obj F).presheaf U z hU
  have h3 := TopCat.Presheaf.stalkFunctor_map_germ_apply U (i z) hU
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) i).unit.app F).hom s
  exact (congrArg (TopCat.Presheaf.stalkPushforward _ i
    ((TopCat.Sheaf.pullback (ModuleCat.{u} R) i).obj F).presheaf z) h3).trans
      ((h _).trans (Stacks.Topology.germ_unit_app i F U z hU s))

/-- For an inducing map `i`, the unit `F ⟶ i_* i⁻¹ F` is invertible on the stalks at the points
of the image of `i`. -/
theorem isIso_stalkFunctor_map_unit {i : Z ⟶ X} (hi : Topology.IsInducing i)
    (F : X.Sheaf (ModuleCat.{u} R)) (z : Z) :
    IsIso ((TopCat.Presheaf.stalkFunctor _ (i z)).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) i).unit.app F).hom) := by
  have hp := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing (ModuleCat.{u} R)
    hi ((TopCat.Sheaf.pullback (ModuleCat.{u} R) i).obj F).presheaf z
  have hc := Stacks.Topology.isIso_ambientStalkHom i F z
  rw [← stalkFunctor_map_unit_comp_stalkPushforward] at hc
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hp hc

/-- The stalks of a direct image `i_* G` vanish at the points off the closed image of `i`. -/
theorem isZero_stalk_pushforward_of_notMem_range {i : Z ⟶ X} (hi : IsClosed (Set.range i))
    (G : Z.Sheaf (ModuleCat.{u} R)) {x : X} (hx : x ∉ Set.range i) :
    IsZero (((TopCat.Sheaf.pushforward (ModuleCat.{u} R) i).obj G).presheaf.stalk x) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun a b => ?_⟩
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ a
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ b
  let W : Opens X := U ⊓ V ⊓ ⟨(Set.range i)ᶜ, hi.isOpen_compl⟩
  have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hx⟩
  have hW : (Opens.map i).obj W = ⊥ := by
    ext z
    exact ⟨fun hz => (hz.2 ⟨z, rfl⟩).elim, fun h => h.elim⟩
  have hsub : Subsingleton (ToType (G.presheaf.obj (op ((Opens.map i).obj W)))) := by
    rw [hW]
    exact ModuleCat.isZero_iff_subsingleton.mp G.isTerminalOfEmpty.isZero
  rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left.trans inf_le_left : W ≤ U)) x hxW,
    ← TopCat.Presheaf.germ_res_apply _ (homOfLE (inf_le_left.trans inf_le_right : W ≤ V)) x hxW]
  exact congrArg _ (hsub.elim _ _)

/-- For a closed embedding `i`, the unit `F ⟶ i_* i⁻¹ F` is an epimorphism of sheaves. -/
theorem epi_unit_of_isClosedEmbedding {i : Z ⟶ X} (hi : Topology.IsClosedEmbedding i)
    (F : X.Sheaf (ModuleCat.{u} R)) :
    Epi ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) i).unit.app F) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  refine (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr fun x => ?_
  by_cases hx : x ∈ Set.range i
  · obtain ⟨z, rfl⟩ := hx
    have := isIso_stalkFunctor_map_unit hi.isInducing F z
    exact (ConcreteCategory.bijective_of_isIso _).2
  · exact fun _ => ⟨0, (ModuleCat.isZero_iff_subsingleton.mp
      (isZero_stalk_pushforward_of_notMem_range hi.isClosed_range _ hx)).elim _ _⟩

/-- A morphism of sheaves all of whose stalk maps vanish is zero. -/
lemma eq_zero_of_stalkFunctor_map_eq_zero {F G : X.Sheaf (ModuleCat.{u} R)} (a : F ⟶ G)
    (ha : ∀ x : X, (TopCat.Presheaf.stalkFunctor _ x).map a.hom = 0) : a = 0 := by
  apply Sheaf.hom_ext
  ext U s
  refine TopCat.Presheaf.section_ext G (unop U) _ _ fun x hx => ?_
  have h := TopCat.Presheaf.stalkFunctor_map_germ_apply (unop U) x hx a.hom s
  rw [ha x] at h
  exact h.symm.trans (map_zero _).symm

/-- For a closed embedding `i`, a morphism `a : F ⟶ G` whose stalks vanish at every point off
`i(Z)` factors through the unit `F ⟶ i_* i⁻¹ F`. -/
theorem exists_unit_comp_eq_of_isClosedEmbedding {i : Z ⟶ X} (hi : Topology.IsClosedEmbedding i)
    {F G : X.Sheaf (ModuleCat.{u} R)} (a : F ⟶ G)
    (ha : ∀ x ∉ Set.range i, (TopCat.Presheaf.stalkFunctor _ x).map a.hom = 0) :
    ∃ b, (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) i).unit.app F ≫ b = a := by
  let η := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} R) i).unit.app F
  have := epi_unit_of_isClosedEmbedding hi F
  have hk : kernel.ι η ≫ a = 0 := by
    refine eq_zero_of_stalkFunctor_map_eq_zero _ fun x => ?_
    refine (TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙
      TopCat.Presheaf.stalkFunctor _ x).map_comp _ _ |>.trans ?_
    change (TopCat.Presheaf.stalkFunctor _ x).map (kernel.ι η).hom ≫
      (TopCat.Presheaf.stalkFunctor _ x).map a.hom = 0
    by_cases hx : x ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hx
      have := isIso_stalkFunctor_map_unit hi.isInducing F z
      have h0 := (TopCat.Sheaf.forget (ModuleCat.{u} R) X ⋙
        TopCat.Presheaf.stalkFunctor _ (i z)).congr_map (kernel.condition η)
      rw [Functor.map_comp, Functor.map_zero] at h0
      have h1 : (TopCat.Presheaf.stalkFunctor _ (i z)).map (kernel.ι η).hom = 0 :=
        (cancel_mono ((TopCat.Presheaf.stalkFunctor _ (i z)).map η.hom)).mp
          (h0.trans zero_comp.symm)
      rw [h1, zero_comp]
    · rw [ha x hx, comp_zero]
  exact ⟨Abelian.epiDesc η a hk, Abelian.comp_epiDesc η a hk⟩

end MMP.Topology
