module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import MMP.Algebra.Category.ModuleCat.Sheaf.PullbackStalk
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Vanishing of sheaves of modules on stalks

Let `R` be a sheaf of commutative rings on a topological space `X`. A sheaf of `R`-modules all of
whose stalks vanish is zero. For a sheaf of modules `M` of finite type, the set of points where
the stalk of `M` vanishes is open: finitely many sections generate `M` near a point `z`, and if
their germs at `z` vanish, they vanish on a neighbourhood of `z`, where `M` is then zero.

For a pullback along a morphism of ringed spaces whose stalk maps are faithfully flat, the stalk
formula `(F N)_x ≅ R_x ⊗_{R'_{g x}} N_{g x}` shows that `F N = 0` forces `N_{g x} = 0`.

## Main results

* `MMP.ModuleSkyscraper.isZero_of_forall_subsingleton_stalk`: a sheaf of modules with zero
  stalks is zero.
* `MMP.ModuleSkyscraper.eventually_subsingleton_stalk_of_isFiniteType`: for a sheaf of modules of
  finite type, the vanishing of the stalk at a point propagates to a neighbourhood.
* `MMP.ModuleSkyscraper.subsingleton_stalk_of_isZero_of_faithfullyFlat`: if the stalk map
  `R'_{g x} → R_x` is faithfully flat and the pullback `F N` vanishes, then `N_{g x}` vanishes.

## References

* [Stacks Project, Tag 01B4](https://stacks.math.columbia.edu/tag/01B4)
* [Stacks Project, Tag 01BN](https://stacks.math.columbia.edu/tag/01BN)
-/

public section

open CategoryTheory Limits TopologicalSpace Opposite Topology

universe u

namespace MMP.ModuleSkyscraper

section Support

variable {X : TopCat.{u}} (Rc : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- A sheaf of modules all of whose stalks vanish is zero. -/
theorem isZero_of_forall_subsingleton_stalk (M : SheafOfModules.{u} (ringSheaf Rc))
    (h : ∀ x, Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x)) :
    IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  apply (SheafOfModules.toSheaf.{u} (ringSheaf Rc)).map_injective
  refine (CategoryTheory.Functor.map_id _ _).trans
    (Eq.trans ?_ (CategoryTheory.Functor.map_zero _ _ _).symm)
  ext U s
  exact TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf.{u} (ringSheaf Rc)).obj M) U.unop
    _ _ fun x hx => @Subsingleton.elim _ (h x) _ _

/-- For a sheaf of modules of finite type, the vanishing of the stalk at a point `z` propagates
to a neighbourhood of `z`. -/
theorem eventually_subsingleton_stalk_of_isFiniteType (M : SheafOfModules.{u} (ringSheaf Rc))
    [M.IsFiniteType] (z : X)
    (hz : Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z)) :
    ∀ᶠ x in 𝓝 z, Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x) := by
  obtain ⟨LP⟩ := Stacks.SheafOfModules.nonempty_localGenerators M z
  let M' : PresheafOfModules.{u} (Rc.obj ⋙ forget₂ CommRingCat RingCat.{u}) := M.val
  have hk : ∀ k, ∀ᶠ x in 𝓝 z, ∀ hx : x ∈ LP.nhd,
      TopCat.Presheaf.germ M'.presheaf LP.nhd x hx (LP.gens k) = 0 := by
    intro k
    obtain ⟨W, hzW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq M'.presheaf z LP.mem_nhd LP.mem_nhd
      (LP.gens k) 0 (@Subsingleton.elim _ hz _ _)
    filter_upwards [W.isOpen.mem_nhds hzW] with x hxW hx
    exact (TopCat.Presheaf.germ_res_apply M'.presheaf iU x hxW (LP.gens k)).symm.trans
      ((congrArg _ (hW.trans (map_zero _))).trans (map_zero _))
  filter_upwards [Filter.eventually_all.2 hk, LP.nhd.isOpen.mem_nhds LP.mem_nhd] with x hx hxN
  suffices ∀ a : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M'.presheaf x, a = 0 from
    ⟨fun a b => (this a).trans (this b).symm⟩
  intro a
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.germ_exist M'.presheaf a
  obtain ⟨W, g, hxW, c, hc⟩ := LP.generates (homOfLE (inf_le_right : V ⊓ LP.nhd ≤ LP.nhd))
    (M'.presheaf.map (homOfLE (inf_le_left : V ⊓ LP.nhd ≤ V)).op t) x ⟨hxV, hxN⟩
  have h1 := TopCat.Presheaf.germ_res_apply M'.presheaf (homOfLE (inf_le_left : V ⊓ LP.nhd ≤ V))
    x ⟨hxV, hxN⟩ t
  have h2 := TopCat.Presheaf.germ_res_apply M'.presheaf g x hxW
    (M'.presheaf.map (homOfLE (inf_le_left : V ⊓ LP.nhd ≤ V)).op t)
  rw [← h1, ← h2]
  have hc' : M'.presheaf.map g.op (M'.presheaf.map (homOfLE (inf_le_left : V ⊓ LP.nhd ≤ V)).op t)
      = ∑ k, (show ((Rc.obj ⋙ forget₂ CommRingCat RingCat.{u}).obj (op W)) from c k) •
        M'.map (g ≫ homOfLE inf_le_right).op (LP.gens k) := hc
  refine (congrArg _ hc').trans ((map_sum _ _ _).trans (Finset.sum_eq_zero fun k _ => ?_))
  refine (PresheafOfModules.germ_smul M' x W hxW _ _).trans ?_
  have h3 := TopCat.Presheaf.germ_res_apply M'.presheaf (g ≫ homOfLE inf_le_right) x hxW
    (LP.gens k)
  exact (congrArg _ (h3.trans (hx k hxN))).trans (smul_zero _)

end Support

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
  {F : SheafOfModules.{u} (ringSheaf R') ⥤ SheafOfModules.{u} (ringSheaf R)}
  (adj : F ⊣ SheafOfModules.pushforward.{u} φ)

include hψ adj in
/-- If the stalk map `R'_{g x} → R_x` is faithfully flat and the pullback `F N` vanishes, then
the stalk of `N` at `g x` vanishes. -/
theorem subsingleton_stalk_of_isZero_of_faithfullyFlat (hff : ψ.FaithfullyFlat)
    (N : SheafOfModules.{u} (ringSheaf R')) (hN : IsZero (F.obj N)) :
    Subsingleton (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf (g x)) := by
  have : (sheafStalkFunctor R x).IsLeftAdjoint := (sheafStalkSkyAdjunction R x).isLeftAdjoint
  have h1 : IsZero ((ModuleCat.extendScalars ψ).obj ((sheafStalkFunctor R' (g x)).obj N)) :=
    ((sheafStalkFunctor R x).map_isZero hN).of_iso ((stalkIso g φ x ψ hψ adj).app N)
  have h2 := ModuleCat.subsingleton_of_isZero h1
  have : Module.FaithfullyFlat (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R'.obj (g x))
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of _
        (TopCat.Presheaf.stalk (C := CommRingCat.{u}) R.obj x))) := hff
  have h3 := (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _ _).1 h2
  exact h3

end Pushforward

end MMP.ModuleSkyscraper

end
