module
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BranchCounts
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.IndexBound.ClosedFibreLineBundles
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartConnected
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.RegularPartDense
import MMP.AlgebraicGeometry.Singularities.EtaleNeighbourhoodTerminal
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurveRankShrinking
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.AdaptedOpen
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurvePuncturedRestrictionSurjective
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# A punctured-independent family pulled back from the closed fibre

Let `(Y, π, y)` be a threefold point setting (`MMP.Fourfold.IsThreefoldPointSetting`), and
consider the product `Y × ℙ¹` (over `Spec ℂ`) with the resolution `π × id : Ỹ × ℙ¹ ⟶ Y × ℙ¹`
and the curve `T_y = {y} × ℙ¹` (`MMP.Fourfold.pointSettingCurve`). Let `b = b_{T_y}` be the rank
of the punctured local system of `T_y` (`MMP.Fourfold.curveLocalSystemRank`). Then there are
line bundles `M_1, …, M_b` on the scheme fibre `F_y = Ỹ ×_Y Spec κ(y)` whose pullbacks `L_i` to
the generic scheme fibre `F_{η_{T_y}} = F_y ×_ℂ Spec K_{T_y}` of `π × id` form a
punctured-independent family (`MMP.Fourfold.IsPuncturedIndependent`).

## Main results

* `MMP.Fourfold.IsThreefoldPointSetting.exists_isPuncturedIndependent_pullback`: the family
  `M_1, …, M_b` exists.

## Implementation notes

* `Y × ℙ¹` is the pull-back of `s_Y : Y ⟶ Spec ℂ` and `ℙ¹_ℂ ⟶ Spec ℂ`, a complex scheme through
  its first projection; `Ỹ × ℙ¹` is formed in the same way from `π ≫ s_Y`, and `π × id` is the
  induced morphism `pullback.map`.
* `T_y` is an irreducible closed subset of `Y × ℙ¹` with underlying set
  `MMP.Fourfold.pointSettingCurve s_Y y`. The integer `b_{T_y}` does not depend on the
  local-system open on which it is computed, so the result is stated for every local-system open
  `T°` of `T_y`, with `b = curveLocalSystemRank T°`.
* The map `F_{η_{T_y}} ⟶ F_y` along which the `M_i` are pulled back is the morphism of fibre
  products induced by the first projection `Ỹ × ℙ¹ ⟶ Ỹ` and by the residue field map
  `κ(y) ⟶ κ(η_{T_y})` of the first projection `Y × ℙ¹ ⟶ Y`, which sends `η_{T_y}` to `y`.
  This is the projection `F_y ×_ℂ Spec K_{T_y} ⟶ F_y` of the source.
* That `π × id` is an isomorphism over the smooth locus of `Y × ℙ¹`, which the definition of
  punctured independence uses, is part of the conclusion.
-/

@[expose] public noncomputable section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite

namespace Proof_lem_mmp_indexb_product_punctured_family

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

/-! ### Stalks of inverse images and of higher direct images -/

section Stalks

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)

/-- The section of `f^* F` over `f⁻¹(W)` attached to a section of `F` over `W`. -/
private def unitSec {W : Opens Y} (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) :
    ToType (((TopCat.Sheaf.forget _ X).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).obj
      (op ((Opens.map f).obj W))) :=
  (((TopCat.Sheaf.forget _ Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
      (op W)).hom r

private theorem stalkToPullbackStalk_germ {W : Opens Y}
    (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (x : X) (hx : f x ∈ W) :
    (stalkToPullbackStalk f F x).hom (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx r) =
      ((TopCat.Sheaf.forget _ X).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ
        ((Opens.map f).obj W) x hx (unitSec f F r) := by
  have h : ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx ≫ stalkToPullbackStalk f F x =
      ((TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
          (op W) ≫ ((TopCat.Sheaf.forget _ X).obj
            ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ ((Opens.map f).obj W) x
              hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun φ => φ.hom r) h

omit F in
/-- Naturality of `stalkPushforward` in the presheaf. -/
private theorem stalkPushforward_naturality {F G : X.Presheaf (ModuleCat.{0} ℚ)}
    (φ : F ⟶ G) (x : X) :
    (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map φ) ≫
        G.stalkPushforward _ f x =
      F.stalkPushforward _ f x ≫ (TopCat.Presheaf.stalkFunctor _ x).map φ := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ,
    TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

omit F in
private lemma stalkPushforward_comp_naturality
    {F' : TopCat.Presheaf (ModuleCat.{0} ℚ) Y} {G G' : TopCat.Presheaf (ModuleCat.{0} ℚ) X}
    (u : F' ⟶ (TopCat.Presheaf.pushforward _ f).obj G) (v : G ⟶ G') (x : X) :
    ((TopCat.Presheaf.stalkFunctor _ (f x)).map u ≫ TopCat.Presheaf.stalkPushforward _ f G x) ≫
        (TopCat.Presheaf.stalkFunctor _ x).map v =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map (u ≫ (TopCat.Presheaf.pushforward _ f).map v) ≫
        TopCat.Presheaf.stalkPushforward _ f G' x := by
  refine (Category.assoc _ _ _).trans ?_
  erw [← stalkPushforward_naturality f v x, Functor.map_comp, Category.assoc]
  rfl

/-- The canonical map `F_{f(x)} ⟶ (f⁻¹F)_x` is an isomorphism. -/
private lemma isIso_stalkToPullbackStalk (x : X) : IsIso (stalkToPullbackStalk f F x) := by
  let ι := (TopCat.Sheaf.pullbackIso (ModuleCat.{0} ℚ) f).app F
  have hunit : (TopCat.Sheaf.forget _ Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F ≫
      (TopCat.Sheaf.pushforward _ f).map ι.hom) =
      (TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.forget _ Y).obj F) ≫
        (TopCat.Presheaf.pushforward _ f).map (toSheafify _ _) := by
    have := Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f) (ModuleCat.{0} ℚ)
        _ _) F
    have h2 := (sheafToPresheaf _ _).congr_map this
    erw [h2]
    unfold Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    erw [Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Adjunction.comp_unit_app, Iso.refl_hom, NatTrans.id_app, Functor.map_id,
      Category.comp_id]
    rfl
  have hst : stalkToPullbackStalk f F x ≫
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ι.hom) =
      TopCat.Presheaf.stalkPullbackHom _ f ((TopCat.Sheaf.forget _ Y).obj F) x ≫
        (TopCat.Presheaf.stalkFunctor _ x).map (toSheafify _ _) := by
    have hunit' : (TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F) ≫
        (TopCat.Presheaf.pushforward _ f).map ((TopCat.Sheaf.forget _ X).map ι.hom) =
        (TopCat.Presheaf.pullbackPushforwardAdjunction _ f).unit.app
          ((TopCat.Sheaf.forget _ Y).obj F) ≫
        (TopCat.Presheaf.pushforward _ f).map (toSheafify _ _) := by
      rw [← hunit, Functor.map_comp]
      rfl
    unfold stalkToPullbackStalk TopCat.Presheaf.stalkPullbackHom
    refine (stalkPushforward_comp_naturality _ _ _ x).trans
      (Eq.trans ?_ (stalkPushforward_comp_naturality _ _ _ x).symm)
    exact congrArg (fun g ↦ (TopCat.Presheaf.stalkFunctor _ (f x)).map g ≫
      TopCat.Presheaf.stalkPushforward _ f _ x) hunit'
  have h1 : IsIso (TopCat.Presheaf.stalkPullbackHom _ f ((TopCat.Sheaf.forget _ Y).obj F) x) :=
    (TopCat.Presheaf.stalkPullbackIso _ f ((TopCat.Sheaf.forget _ Y).obj F) x).isIso_hom
  have h2 := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ)
    ((TopCat.Presheaf.pullback _ f).obj ((TopCat.Sheaf.forget _ Y).obj F))
  have h3 : IsIso ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ι.hom)) :=
    ((TopCat.Presheaf.stalkFunctor _ x).mapIso ((TopCat.Sheaf.forget _ X).mapIso ι)).isIso_hom
  have : IsIso (stalkToPullbackStalk f F x ≫
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map ι.hom)) := by
    rw [hst]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h3 this

private theorem bijective_stalkToPullbackStalk (x : X) :
    Function.Bijective (stalkToPullbackStalk f F x).hom := by
  have := isIso_stalkToPullbackStalk f F x
  exact ConcreteCategory.bijective_of_isIso (stalkToPullbackStalk f F x)

omit F in
/-- Naturality of `stalkToPullbackStalk` in the sheaf. -/
private theorem stalkToPullbackStalk_naturality
    {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y} (φ : F ⟶ G) (x : X) :
    stalkToPullbackStalk f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map
        ((TopCat.Sheaf.forget _ X).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ)) =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Sheaf.forget _ Y).map φ) ≫
        stalkToPullbackStalk f G x := by
  have hn := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.naturality φ
  have hn' : (TopCat.Sheaf.forget _ Y).map φ ≫ (TopCat.Sheaf.forget _ Y).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app G) =
      (TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F) ≫
        (TopCat.Presheaf.pushforward _ f).map ((TopCat.Sheaf.forget _ X).map
          ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ)) := by
    have := congrArg (fun m ↦ (TopCat.Sheaf.forget _ Y).map m) hn
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at this
    exact this
  unfold stalkToPullbackStalk
  erw [Category.assoc, ← stalkPushforward_naturality f, ← Category.assoc,
    ← CategoryTheory.Functor.map_comp, ← hn', CategoryTheory.Functor.map_comp, Category.assoc]

omit f F in
private theorem higherDirectImageGerm_apply (f : X ⟶ Y) (q : ℕ) {V : Opens Y} (y : Y)
    (hy : y ∈ V) (c : rationalCohomology (preimageSpace f V) q) :
    (higherDirectImageGerm f q y hy).hom c =
      (TopCat.Presheaf.stalkFunctor _ y).map
        (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q))
        ((directImagePresheaf f q).germ V y hy c) := rfl

omit f F in
/-- The germ of a class is the germ of the section of `R^q f_* ℚ` it defines. -/
private theorem higherDirectImageGerm_eq_germ (f : X ⟶ Y) (q : ℕ) {V : Opens Y} (y : Y)
    (hy : y ∈ V) (c : rationalCohomology (preimageSpace f V) q) :
    (higherDirectImageGerm f q y hy).hom c =
      ((TopCat.Sheaf.forget _ Y).obj (higherDirectImage f q)).germ V y hy
        (((toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q)).app (op V)).hom
          c) := by
  rw [higherDirectImageGerm_apply]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply (F := directImagePresheaf f q) V y hy
    (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q)) c

omit f F in
/-- The germ of a restricted class is the germ of the class. -/
private theorem higherDirectImageGerm_res (f : X ⟶ Y) (q : ℕ) {V W : Opens Y} (hWV : W ≤ V)
    (y : Y) (hy : y ∈ W) (c : rationalCohomology (preimageSpace f V) q) :
    (higherDirectImageGerm f q y hy).hom
        ((rationalCohomologyMap (preimageInclusion f hWV) q).hom c) =
      (higherDirectImageGerm f q y (hWV hy)).hom c := by
  rw [higherDirectImageGerm_apply, higherDirectImageGerm_apply]
  congr 1
  exact TopCat.Presheaf.germ_res_apply (directImagePresheaf f q) (homOfLE hWV) y hy c

omit f F in
/-- Every germ of `R^q f_* ℚ` is the germ of a class on some `f⁻¹(V)`. -/
private theorem exists_higherDirectImageGerm_eq (f : X ⟶ Y) (q : ℕ) (y : Y)
    (w : ToType (((TopCat.Sheaf.forget _ Y).obj (higherDirectImage f q)).stalk y)) :
    ∃ (V : Opens Y) (hy : y ∈ V) (c : rationalCohomology (preimageSpace f V) q),
      (higherDirectImageGerm f q y hy).hom c = w := by
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (C := ModuleCat.{0} ℚ)
    (𝓕 := directImagePresheaf f q) (p₀ := y)
  obtain ⟨w', rfl⟩ := (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor _ y).map
    (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q)))).2 w
  obtain ⟨V, hy, c, rfl⟩ := (directImagePresheaf f q).exists_germ_eq w'
  exact ⟨V, hy, c, rfl⟩

omit f F in
/-- The map on stalks induced by the sheafification of a morphism of the presheaves
`V ↦ H^q(f⁻¹(V); ℚ)`, on germs of classes. -/
private theorem stalkFunctor_map_presheafToSheaf_germ {X X' : TopCat.{0}} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (q : ℕ) (ψ : directImagePresheaf p q ⟶ directImagePresheaf p' q)
    {V : Opens Y} (y : Y) (hy : y ∈ V) (c : rationalCohomology (preimageSpace p V) q) :
    (TopCat.Presheaf.stalkFunctor _ y).map ((TopCat.Sheaf.forget _ Y).map
        ((presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).map ψ))
        ((higherDirectImageGerm p q y hy).hom c) =
      (higherDirectImageGerm p' q y hy).hom (ψ.app (Opposite.op V) c) := by
  have hm : higherDirectImageGerm p q y hy ≫ (TopCat.Presheaf.stalkFunctor _ y).map
      ((TopCat.Sheaf.forget _ Y).map
        ((presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).map ψ)) =
      ψ.app (Opposite.op V) ≫ higherDirectImageGerm p' q y hy := by
    unfold higherDirectImageGerm
    have h := toSheafify_naturality (Opens.grothendieckTopology Y) ψ
    erw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← h, CategoryTheory.Functor.map_comp,
      ← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ, Category.assoc]
  exact ConcreteCategory.congr_hom hm c

end Stalks

/-- The restriction map `r_t` on the germ at `t` of a class on `π⁻¹(V)` is the germ of its
restriction to `π⁻¹(V) ∩ π⁻¹(Y_reg) ≅ j⁻¹(V)`. -/
private theorem localSystemRestrictionFibre_germ {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (hπ : IsBiregular π (smoothLocus sY))
    (To : (curveScheme T).Opens) (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    (localSystemRestrictionFibre sY hπ To t).hom
        ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
          t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)) =
      (stalkToPullbackStalk (curveOpenInclusion sY To) (regularHigherDirectImage sY 2) t).hom
        ((higherDirectImageGerm (regularInclusion sY) 2 _ hV).hom
          ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
            (analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]))
            (regularSection_analyticMap_comp sY hπ) V) 2).hom α)) := by
  have h := ConcreteCategory.congr_hom (stalkToPullbackStalk_naturality
    (curveOpenInclusion sY To) (resolutionRestriction sY hπ 2) t)
    ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  unfold localSystemRestrictionFibre localSystemRestriction
  erw [h]
  exact congrArg (fun z ↦ (stalkToPullbackStalk (curveOpenInclusion sY To)
    (regularHigherDirectImage sY 2) t).hom z)
    (stalkFunctor_map_presheafToSheaf_germ _ _ 2 _ _ hV α)

/-! ### Sections of local systems -/

section ConstantSheafGerms

variable {V : TopCat.{0}} (E : ModuleCat.{0} ℚ)

/-- The constant section `e` of the constant sheaf with value `E`. -/
private def constSection (e : E) :
    ToType (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).obj (op ⊤)) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology V)
    ((Functor.const (Opens V)ᵒᵖ).obj E)).app (op ⊤)).hom e

private theorem constSection_zero : constSection (V := V) E 0 = 0 :=
  map_zero _

/-- Every germ of a constant sheaf is the germ of a constant section. -/
private theorem constantSheaf_exists_constSection_germ (p : V)
    (c : ToType (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ
          ⊤ p (Opens.mem_top p) (constSection E e) = c := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) V := (Functor.const (Opens V)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) p).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K))).2 c
  obtain ⟨U, hU, e, rfl⟩ := K.exists_germ_eq c'
  refine ⟨e, ?_⟩
  have this : K.germ U p hU e = K.germ ⊤ p (Opens.mem_top p) e :=
    TopCat.Presheaf.germ_res_apply K (homOfLE (le_top : U ≤ ⊤)) p hU e
  rw [← hc', this]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K) e).symm

/-- A constant section with vanishing germ is zero. -/
private theorem eq_zero_of_germ_constSection {e : E} (p : V)
    (h : ((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ
        ⊤ p (Opens.mem_top p) (constSection E e) = 0) : e = 0 := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) V := (Functor.const (Opens V)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K) e
  have h2 : K.germ ⊤ p (Opens.mem_top p) e = K.germ ⊤ p (Opens.mem_top p) 0 := by
    apply (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor
      (ModuleCat.{0} ℚ) p).map (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K))).1
    refine e1.trans (h.trans ?_)
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  obtain ⟨_, -, _, _, he⟩ := K.germ_eq p (Opens.mem_top p) (Opens.mem_top p) e 0 h2
  exact he

/-- Near every point, a section of a constant sheaf has the germs of a constant section. -/
private theorem constantSheaf_exists_constSection {U : Opens V}
    (sec : ToType (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).obj (op U)))
    (p : V) (hp : p ∈ U) :
    ∃ (e : E) (N : Opens V) (_ : p ∈ N) (hNU : N ≤ U), ∀ v (hv : v ∈ N),
      ((TopCat.Sheaf.forget _ V).obj
        ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ U v
          (hNU hv) sec =
        ((TopCat.Sheaf.forget _ V).obj
          ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ ⊤ v
            (Opens.mem_top v) (constSection E e) := by
  obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E p
    (((TopCat.Sheaf.forget _ V).obj
      ((constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E)).germ U p hp sec)
  obtain ⟨W, hW, iU, iT, hWe⟩ := TopCat.Presheaf.germ_eq _ p hp (Opens.mem_top p) sec
    (constSection E e) he.symm
  refine ⟨e, W, hW, iU.le, fun v hv => ?_⟩
  exact (TopCat.Presheaf.germ_res_apply _ iU v hv sec).symm.trans
    ((congrArg _ hWe).trans (TopCat.Presheaf.germ_res_apply _ iT v hv _))

end ConstantSheafGerms

section LocalSystem

variable {Z : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z}

/-- **The support of a section of a local system is open.** -/
private theorem exists_germ_ne_zero (hF : IsLocalSystem F) {W : Opens Z}
    (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W))) (z₀ : Z) (hz₀ : z₀ ∈ W)
    (h : ((TopCat.Sheaf.forget _ Z).obj F).germ W z₀ hz₀ r ≠ 0) :
    ∃ (N : Opens Z) (_ : z₀ ∈ N) (hNW : N ≤ W), ∀ z (hz : z ∈ N),
      ((TopCat.Sheaf.forget _ Z).obj F).germ W z (hNW hz) r ≠ 0 := by
  obtain ⟨V, hz₀V, E, -, ⟨φ⟩⟩ := hF z₀
  let ι := V.inclusion'
  let C := (TopCat.Sheaf.forget _ _).obj
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat Z).obj V))
      (ModuleCat.{0} ℚ)).obj E)
  let ρ := unitSec ι F r
  let sec : ToType (C.obj (op ((Opens.map ι).obj W))) :=
    (((TopCat.Sheaf.forget _ _).map φ.hom).app (op ((Opens.map ι).obj W))).hom ρ
  let M := fun v : (Opens.toTopCat Z).obj V =>
    ((TopCat.Presheaf.stalkFunctor _ v).mapIso ((TopCat.Sheaf.forget _ _).mapIso φ)).hom.hom
  have hg : ∀ (v : (Opens.toTopCat Z).obj V) (hv : ι v ∈ W),
      C.germ _ v hv sec = M v ((stalkToPullbackStalk ι F v).hom
        (((TopCat.Sheaf.forget _ Z).obj F).germ W (ι v) hv r)) := by
    intro v hv
    rw [stalkToPullbackStalk_germ]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply _ v hv _ ρ).symm
  have hinj : ∀ v : (Opens.toTopCat Z).obj V,
      Function.Injective (M v ∘ (stalkToPullbackStalk ι F v).hom) := fun v =>
    ((TopCat.Presheaf.stalkFunctor _ v).mapIso
      ((TopCat.Sheaf.forget _ _).mapIso φ)).toLinearEquiv.injective.comp
      (bijective_stalkToPullbackStalk ι F v).1
  let v₀ : (Opens.toTopCat Z).obj V := ⟨z₀, hz₀V⟩
  obtain ⟨e, N, hv₀N, hNU, hloc⟩ := constantSheaf_exists_constSection E sec v₀ hz₀
  have he : e ≠ 0 := by
    rintro rfl
    apply h
    apply hinj v₀
    have h1 := (hg v₀ hz₀).symm.trans (hloc v₀ hv₀N)
    rw [constSection_zero, map_zero] at h1
    exact h1.trans ((congrArg (M v₀) (map_zero _)).trans (map_zero _)).symm
  refine ⟨⟨Subtype.val '' (N : Set ((Opens.toTopCat Z).obj V)),
    V.isOpen.isOpenMap_subtype_val _ N.isOpen⟩, ⟨v₀, hv₀N, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hNU hv
  · rintro _ ⟨v, hv, rfl⟩ h0
    apply he
    apply eq_zero_of_germ_constSection (V := (Opens.toTopCat Z).obj V) E v
    have h1 := (hloc v hv).symm.trans (hg v (hNU hv))
    have h0' : ((TopCat.Sheaf.forget _ Z).obj F).germ W (ι v) (hNU hv) r = 0 := h0
    exact h1.trans ((congrArg (fun y => M v ((stalkToPullbackStalk ι F v).hom y)) h0').trans
      ((congrArg (M v) (map_zero _)).trans (map_zero _)))

/-- **Independence of sections of a local system spreads over a connected space.** If the germs
at one point of finitely many sections of a local system over the whole of a connected space are
linearly independent, then so are their germs at every point: the vanishing locus of a section
of a local system is open and closed. -/
private theorem linearIndependent_germ_of_linearIndependent_germ [ConnectedSpace Z]
    (hF : IsLocalSystem F) {ι : Type} [Fintype ι] {W : Opens Z} (hW : ∀ z, z ∈ W)
    (u : ι → ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W))) (z₀ z : Z)
    (h : LinearIndependent ℚ fun i ↦ ((TopCat.Sheaf.forget _ Z).obj F).germ W z₀ (hW z₀) (u i)) :
    LinearIndependent ℚ fun i ↦ ((TopCat.Sheaf.forget _ Z).obj F).germ W z (hW z) (u i) := by
  classical
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  set s := ∑ i, g i • u i with hs
  have hgerm : ∀ x, ((TopCat.Sheaf.forget _ Z).obj F).germ W x (hW x) s =
      ∑ i, g i • ((TopCat.Sheaf.forget _ Z).obj F).germ W x (hW x) (u i) := fun x ↦ by
    rw [hs, map_sum]
    simp only [map_smul]
  let A : Set Z := {x | ((TopCat.Sheaf.forget _ Z).obj F).germ W x (hW x) s = 0}
  have hAo : IsOpen A := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨N, hxN, i₁, i₂, e⟩ := ((TopCat.Sheaf.forget _ Z).obj F).germ_eq x (hW x) (hW x) s 0
      (hx.trans (map_zero _).symm)
    refine ⟨N, fun x' hx' ↦ ?_, N.isOpen, hxN⟩
    change ((TopCat.Sheaf.forget _ Z).obj F).germ W x' (hW x') s = 0
    rw [← TopCat.Presheaf.germ_res_apply _ i₁ x' hx', e, map_zero, map_zero]
  have hAc : IsOpen Aᶜ := by
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨N, hxN, hNW, hN⟩ := exists_germ_ne_zero hF s x (hW x) hx
    exact ⟨N, hN, N.isOpen, hxN⟩
  have hzA : z ∈ A := (hgerm z).trans hg
  have hA : A = Set.univ := IsClopen.eq_univ ⟨isOpen_compl_iff.1 hAc, hAo⟩ ⟨z, hzA⟩
  have hz₀ : z₀ ∈ A := hA ▸ Set.mem_univ z₀
  exact h g ((hgerm z₀).symm.trans hz₀)

end LocalSystem

/-! ### Linear algebra -/

/-- A spanning set of `V` contains `dim (V / K)` linearly independent vectors. -/
private theorem exists_linearIndependent_fin_finrank_quotient {V : Type*} [AddCommGroup V]
    [Module ℚ V] (K : Submodule ℚ V) {S : Set V} (hS : Submodule.span ℚ S = ⊤) :
    ∃ v : Fin (Module.finrank ℚ (V ⧸ K)) → V, (∀ i, v i ∈ S) ∧ LinearIndependent ℚ v := by
  classical
  by_cases hfin : Module.Finite ℚ (V ⧸ K)
  · have hS' : Submodule.span ℚ (K.mkQ '' S) = ⊤ := by
      rw [Submodule.span_image, hS, Submodule.map_top, Submodule.range_mkQ]
    obtain ⟨B, hBS, hBspan, hBli⟩ := exists_linearIndependent ℚ (K.mkQ '' S)
    have hBfin : B.Finite := hBli.setFinite
    haveI : Fintype B := hBfin.fintype
    have hcard : Fintype.card B = Module.finrank ℚ (V ⧸ K) := by
      have h1 := finrank_span_set_eq_card hBli
      rw [hBspan, hS', finrank_top] at h1
      rw [h1, Set.toFinset_card]
    let eB : Fin (Module.finrank ℚ (V ⧸ K)) ≃ B := (Fintype.equivFinOfCardEq hcard).symm
    have hpre : ∀ b : B, ∃ s ∈ S, K.mkQ s = b := fun b ↦ hBS b.2
    choose s hsS hs using hpre
    refine ⟨fun i ↦ s (eB i), fun i ↦ hsS _, ?_⟩
    refine LinearIndependent.of_comp K.mkQ ?_
    have : (K.mkQ ∘ fun i ↦ s (eB i)) = (fun b : B ↦ (b : V ⧸ K)) ∘ eB := by
      funext i
      exact hs (eB i)
    rw [this]
    exact hBli.comp eB eB.injective
  · rw [Module.finrank_of_not_finite hfin]
    exact ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, linearIndependent_empty_type⟩

/-! ### Complex points and the realization -/

section Realization

/-- The change of coefficients `H^n(-; ℤ) ⟶ H^n(-; ℚ)` commutes with pullbacks. -/
private theorem mapCoeff_map {Y' Y : TopCat.{0}} (g : Y' ⟶ Y) (n : ℕ)
    (x : singularCohomology ℤ Y n) :
    singularCohomology.mapCoeff (Int.castRingHom ℚ) n
      ((MMP.relativeSingularCohomology.map ℤ (ModuleCat.of ℤ ℤ) g (A' := Set.univᶜ)
        (A := Set.univᶜ) (fun _ hx ↦ (hx (Set.mem_univ _)).elim) n).hom x) =
    (rationalCohomologyMap g n).hom (singularCohomology.mapCoeff (Int.castRingHom ℚ) n x) := by
  have k : ∀ {Z : TopCat.{0}} (y : singularCohomology ℤ Z n),
      MMP.SingularCochain.relativeSingularCohomologyEquiv ℚ (Set.univᶜ : Set Z) n
        (singularCohomology.mapCoeff (Int.castRingHom ℚ) n y) =
      singularCohomology.relCohomologyMap (Int.castRingHom ℚ) Set.univᶜ n
        (MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ Set.univᶜ n y) :=
    fun y => LinearEquiv.apply_symm_apply _ _
  have h₁ := MMP.SingularCochain.relativeSingularCohomologyEquiv_map (R := ℚ) g
    (A' := (Set.univᶜ : Set Y')) (A := (Set.univᶜ : Set Y))
    (fun _ hx ↦ (hx (Set.mem_univ _)).elim) n (singularCohomology.mapCoeff (Int.castRingHom ℚ) n x)
  have h₂ := MMP.SingularCochain.relativeSingularCohomologyEquiv_map (R := ℤ) g
    (A' := (Set.univᶜ : Set Y')) (A := (Set.univᶜ : Set Y))
    (fun _ hx ↦ (hx (Set.mem_univ _)).elim) n x
  apply (MMP.SingularCochain.relativeSingularCohomologyEquiv ℚ
    (Set.univᶜ : Set Y') n).injective
  refine (k _).trans (Eq.trans ?_ h₁.symm)
  refine (congrArg _ h₂).trans ?_
  rw [k x]
  generalize MMP.SingularCochain.relativeSingularCohomologyEquiv ℤ _ n x = y
  induction y using Submodule.Quotient.induction_on
  rfl

private lemma analyticMap_congr {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} {g g' : X ⟶ Y} (h : g = g') (hg : g ≫ sY = sX)
    (hg' : g' ≫ sY = sX) : analyticMap g hg = analyticMap g' hg' := by
  subst h
  rfl

private lemma analyticMap_id {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) :
    analyticMap (𝟙 X) (Category.id_comp sX) = 𝟙 _ := by
  ext x
  change x.hom ≫ 𝟙 X = x.hom
  exact Category.comp_id _

/-- A complex variety has a complex point. -/
private lemma nonempty_complexPoints {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sX] : Nonempty (ComplexPoints sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety ℂ sX›.toIsIntegral
  have : CompactSpace X :=
    ⟨QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := X) isClosed_univ Set.univ_nonempty
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := show LocallyOfFiniteType sX from inferInstance
  obtain ⟨p⟩ : Nonempty (MMP.UnderlyingSpace ℂ X) :=
    ⟨(MMP.UnderlyingSpace.equivClosedPoints X).symm ⟨x, hx⟩⟩
  exact ⟨(ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm p⟩

variable {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}

/-- A local-system open of a curve on a complex variety is a complex variety with connected
complex realization. -/
private lemma isLocalSystemOpen_facts (hY : MMP.Mori.IsVariety ℂ sY)
    {W : (curveScheme T).Opens} (hW : IsLocalSystemOpen sY W) :
    AlgebraicGeometry.IsVariety ℂ (W.ι ≫ curveι T ≫ sY) ∧
      ConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  haveI : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  haveI : CompactSpace (curveScheme T) :=
    QuasiCompact.compactSpace_of_compactSpace (curveι T ≫ sY)
  haveI : IsNoetherian (curveScheme T) := ⟨⟩
  haveI : Smooth (W.ι ≫ curveι T ≫ sY) := hW.smooth
  haveI : ConnectedSpace W := hW.connectedSpace
  haveI : IsIntegral W :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (W.ι ≫ curveι T ≫ sY)
  haveI hV : AlgebraicGeometry.IsVariety ℂ (W.ι ≫ curveι T ≫ sY) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  exact ⟨hV, connectedSpace_analyticSpace _⟩

end Realization

/-! ### Closed points -/

section ClosedPoint

/-- A morphism from a reduced scheme whose image is a closed point `y` factors through
`Spec κ(y)`. -/
private theorem exists_comp_fromSpecResidueField_eq {X Y : Scheme.{0}} [IsReduced X]
    (g : X ⟶ Y) {y : Y} (hy : IsClosed ({y} : Set Y)) (hg : Set.range g ⊆ {y}) :
    ∃ l : X ⟶ Spec (Y.residueField y), l ≫ Y.fromSpecResidueField y = g := by
  have : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have H : (Y.fromSpecResidueField y).ker ≤ g.ker := by
    rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range g,
      ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal, Closeds.closure_le]
    intro z hz
    refine (Y.fromSpecResidueField y).range_subset_ker_support ?_
    rw [Scheme.range_fromSpecResidueField]
    exact hg hz
  exact ⟨IsClosedImmersion.lift _ g H, IsClosedImmersion.lift_fac _ _ H⟩

variable {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sY] (π : Yt ⟶ Y)
  {y : Y} (hy : IsClosed ({y} : Set Y))

/-- The `ℂ`-point of a closed point. -/
private abbrev closedComplexPoint : ComplexPoints sY :=
  ⟨pointOfClosedPoint sY y hy, pointOfClosedPoint_comp sY y hy⟩

/-- `Spec κ(y) ⟶ Y ⟶ Spec ℂ ⟶ Y` is `Spec κ(y) ⟶ Y`, the last map being the `ℂ`-point `y`. -/
private lemma fromSpecResidueField_comp_pointOfClosedPoint :
    Y.fromSpecResidueField y ≫ sY ≫ pointOfClosedPoint sY y hy = Y.fromSpecResidueField y := by
  rw [pointOfClosedPoint, ← Category.assoc, ← SpecMap_residueFieldIsoBase_inv sY y hy,
    ← Category.assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

/-- The scheme fibre `F_y` is the fibre of `π` over the `ℂ`-point `y`. -/
private theorem isPullback_pointSettingFibre :
    IsPullback (pullback.fst π (Y.fromSpecResidueField y))
      (pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY) π (pointOfClosedPoint sY y hy) := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback π (Y.fromSpecResidueField y)) (Iso.refl _)
    (Iso.refl _) (asIso (Spec.map (residueFieldIsoBase sY y hy).inv)) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp only [asIso_hom, SpecMap_residueFieldIsoBase_inv, Iso.refl_hom, Category.id_comp]
    rw [pullback.condition_assoc]
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, asIso_hom, pointOfClosedPoint, ← Category.assoc,
      ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

end ClosedPoint

/-! ### The family over an open of the curve and the closed fibre -/

section Family

variable {Y Yt Y' Yt' : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {Φ : Yt' ⟶ Y'}
  {p : Y' ⟶ Y} {pt : Yt' ⟶ Yt} (hP : IsPullback pt Φ π p) {y : Y}
  {T : IrreducibleCloseds Y'} {T₁ : (curveScheme T).Opens}
  {l : (T₁ : Scheme.{0}) ⟶ Spec (Y.residueField y)}
  (hl : l ≫ Y.fromSpecResidueField y = T₁.ι ≫ curveι T ≫ p)

include hP hl in
/-- The map `Ỹ' ×_{Y'} T¹ ⟶ F_y` from the family over `T¹` to the closed fibre. -/
private def familyMap : adaptedFamily Φ T₁ ⟶ pointSettingFibre π y :=
  pullback.lift (pullback.fst _ _ ≫ pt) (pullback.snd _ _ ≫ l) (by
    rw [Category.assoc, hP.w, pullback.condition_assoc, Category.assoc, Category.assoc, hl])

private lemma familyMap_fst :
    familyMap hP hl ≫ pullback.fst π (Y.fromSpecResidueField y) = pullback.fst _ _ ≫ pt :=
  pullback.lift_fst _ _ _

private lemma familyMap_snd :
    familyMap hP hl ≫ pullback.snd π (Y.fromSpecResidueField y) = pullback.snd _ _ ≫ l :=
  pullback.lift_snd _ _ _

include hP in
private lemma pt_comp_structure : pt ≫ π ≫ sY = Φ ≫ p ≫ sY := by
  rw [← Category.assoc, hP.w, Category.assoc]

/-- The generic fibre of the family maps to `F_y` as the generic fibre `F_{η_T} ⟶ F_y`. -/
private theorem curveOpenFibreToFamily_familyMap (ξ : (T₁ : Scheme.{0}))
    (e : (T₁.ι ≫ curveι T).base ξ = localSettingGenericPoint T)
    (hη : y = p.base (localSettingGenericPoint T)) :
    curveOpenFibreToFamily Φ T₁ ξ ≫ familyMap hP hl =
      curveOpenFibreToGenericFibre Φ T₁ ξ e ≫
        pullback.map _ _ π (Y.fromSpecResidueField y) pt
          (Spec.map (p.residueFieldMap (localSettingGenericPoint T)) ≫
            Spec.map (Y.residueFieldCongr hη).hom) p hP.w.symm
          (by rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
            Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]) := by
  apply pullback.hom_ext
  · simp [familyMap_fst, curveOpenFibreToFamily, curveOpenFibreToGenericFibre]
  · rw [Category.assoc, familyMap_snd, Category.assoc, pullback.lift_snd]
    simp only [curveOpenFibreToFamily, curveOpenFibreToGenericFibre, pullback.lift_snd_assoc,
      Category.assoc]
    congr 1
    rw [← cancel_mono (Y.fromSpecResidueField y), Category.assoc, hl]
    simp only [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
      Scheme.residueFieldCongr_fromSpecResidueField_assoc,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]

/-- The map `F_t ⟶ F_y` from the fibre over a complex point `t ∈ T¹`. -/
private def fibreToClosedFibre (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    pointFibre (p ≫ sY) Φ T₁ t ⟶ pointSettingFibre π y :=
  pointFibreToFamily (p ≫ sY) Φ T₁ t ≫ familyMap hP hl

private lemma pointFibreToFamily_fst (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    pointFibreToFamily (p ≫ sY) Φ T₁ t ≫ pullback.fst Φ (T₁.ι ≫ curveι T) =
      pointFibreFst (p ≫ sY) Φ T₁ t :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private lemma fibreToClosedFibre_fst (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    fibreToClosedFibre hP hl t ≫ pullback.fst π (Y.fromSpecResidueField y) =
      pointFibreFst (p ≫ sY) Φ T₁ t ≫ pt := by
  rw [fibreToClosedFibre, Category.assoc, familyMap_fst, ← Category.assoc,
    pointFibreToFamily_fst]

private lemma fibreToClosedFibre_structure (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    fibreToClosedFibre hP hl t ≫ pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY =
      pointFibre (p ≫ sY) Φ T₁ t ↘ Spec (.of ℂ) := by
  rw [← Category.assoc, fibreToClosedFibre_fst, Category.assoc, pt_comp_structure hP]
  exact pointFibreFst_comp_structure (p ≫ sY) Φ T₁ t

/-- The realization `F_t(ℂ) ⟶ F_y(ℂ)`. -/
private abbrev fibreToClosedFibreAn (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    analyticSpace (pointFibre (p ≫ sY) Φ T₁ t ↘ Spec (.of ℂ)) ⟶
      analyticSpace (pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY) :=
  analyticMap (fibreToClosedFibre hP hl t) (fibreToClosedFibre_structure hP hl t)

variable [LocallyOfFiniteType sY] (hy : IsClosed ({y} : Set Y))

include hl in
/-- A complex point of `T¹` lies over the `ℂ`-point `y` of `Y`. -/
private lemma point_comp_eq (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    t.hom ≫ T₁.ι ≫ curveι T ≫ p = pointOfClosedPoint sY y hy := by
  have h1 : t.hom ≫ l = Spec.map (residueFieldIsoBase sY y hy).hom := by
    rw [← cancel_mono (Spec.map (residueFieldIsoBase sY y hy).inv), ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.assoc, SpecMap_residueFieldIsoBase_inv,
      ← Category.assoc l, hl]
    simpa only [Category.assoc] using t.hom_comp_structure
  rw [← hl, ← Category.assoc, h1]
  rfl

include hP hl hy in
/-- The section `F_y ⟶ F_t` of `F_t ⟶ F_y`. -/
private def closedFibreToFibre (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    pointSettingFibre π y ⟶ pointFibre (p ≫ sY) Φ T₁ t :=
  pullback.lift
    (hP.lift (pullback.fst π _) ((pullback.fst π _ ≫ π ≫ sY) ≫ t.hom ≫ T₁.ι ≫ curveι T) (by
      simp only [Category.assoc]
      rw [point_comp_eq hl hy t, pullback.condition_assoc,
        fromSpecResidueField_comp_pointOfClosedPoint, pullback.condition]))
    (pullback.fst π _ ≫ π ≫ sY) (by rw [hP.lift_snd])

omit [LocallyOfFiniteType sY] in
private lemma pointFibre_hom_ext (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) {Z : Scheme.{0}}
    {f g : Z ⟶ pointFibre (p ≫ sY) Φ T₁ t}
    (h₁ : f ≫ pointFibreFst (p ≫ sY) Φ T₁ t = g ≫ pointFibreFst (p ≫ sY) Φ T₁ t)
    (h₂ : f ≫ pointFibreSnd (p ≫ sY) Φ T₁ t = g ≫ pointFibreSnd (p ≫ sY) Φ T₁ t) : f = g :=
  pullback.hom_ext h₁ h₂

private lemma closedFibreToFibre_fst (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    closedFibreToFibre hP hl hy t ≫ pointFibreFst (p ≫ sY) Φ T₁ t =
      hP.lift (pullback.fst π _) ((pullback.fst π _ ≫ π ≫ sY) ≫ t.hom ≫ T₁.ι ≫ curveι T) (by
        simp only [Category.assoc]
        rw [point_comp_eq hl hy t, pullback.condition_assoc,
          fromSpecResidueField_comp_pointOfClosedPoint, pullback.condition]) :=
  pullback.lift_fst _ _ _

private lemma closedFibreToFibre_snd (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    closedFibreToFibre hP hl hy t ≫ pointFibreSnd (p ≫ sY) Φ T₁ t =
      pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY :=
  pullback.lift_snd _ _ _

private lemma fibreToClosedFibre_closedFibreToFibre
    (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    fibreToClosedFibre hP hl t ≫ closedFibreToFibre hP hl hy t = 𝟙 _ := by
  apply pointFibre_hom_ext t
  · rw [Category.assoc, closedFibreToFibre_fst, Category.id_comp]
    apply hP.hom_ext
    · rw [Category.assoc, hP.lift_fst, fibreToClosedFibre_fst]
    · rw [Category.assoc, hP.lift_snd, ← Category.assoc, fibreToClosedFibre_structure]
      exact (pointFibreFst_comp (p ≫ sY) Φ T₁ t).symm
  · rw [Category.assoc, closedFibreToFibre_snd, Category.id_comp, fibreToClosedFibre_structure]
    rfl

private lemma closedFibreToFibre_structure (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    closedFibreToFibre hP hl hy t ≫ (pointFibre (p ≫ sY) Φ T₁ t ↘ Spec (.of ℂ)) =
      pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY :=
  closedFibreToFibre_snd hP hl hy t

/-- Pullback along `F_t(ℂ) ⟶ F_y(ℂ)` is a left inverse of pullback along `F_y(ℂ) ⟶ F_t(ℂ)`. -/
private lemma rationalCohomologyMap_fibreToClosedFibreAn_section
    (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) (q : ℕ)
    (x : rationalCohomology (analyticSpace (pointFibre (p ≫ sY) Φ T₁ t ↘ Spec (.of ℂ))) q) :
    (rationalCohomologyMap (fibreToClosedFibreAn hP hl t) q).hom
      ((rationalCohomologyMap (analyticMap (closedFibreToFibre hP hl hy t)
        (closedFibreToFibre_structure hP hl hy t)) q).hom x) = x := by
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, analyticMap_comp,
    analyticMap_congr (fibreToClosedFibre_closedFibreToFibre hP hl hy t) _ (Category.id_comp _),
    analyticMap_id, rationalCohomologyMap_id]
  rfl

/-! #### Tubes -/

include hP in
private lemma mem_tubeMap {V₀ : Opens (analyticSpace sY)}
    (x : preimageSpace (resolutionAnalyticMap (p ≫ sY) Φ)
      ((Opens.map (analyticMap p rfl)).obj V₀)) :
    analyticMap pt (pt_comp_structure hP) x.1 ∈
      (analyticMap π (sY := sY) rfl) ⁻¹' (V₀ : Set (analyticSpace sY)) := by
  have : analyticMap π (sY := sY) rfl (analyticMap pt (pt_comp_structure hP) x.1) =
      analyticMap p rfl (resolutionAnalyticMap (p ≫ sY) Φ x.1) := by
    ext1
    change (x.1.hom ≫ pt) ≫ π = (x.1.hom ≫ Φ) ≫ p
    rw [Category.assoc, Category.assoc, hP.w]
  rw [Set.mem_preimage, this]
  exact x.2

/-- The map `(π')⁻¹(p⁻¹(V₀)) ⟶ π⁻¹(V₀)` of tubes induced by `Ỹ' ⟶ Ỹ`. -/
private def tubeMap (V₀ : Opens (analyticSpace sY)) :
    preimageSpace (resolutionAnalyticMap (p ≫ sY) Φ) ((Opens.map (analyticMap p rfl)).obj V₀) ⟶
      preimageSpace (analyticMap π (sY := sY) rfl) V₀ :=
  TopCat.ofHom ⟨fun x ↦ ⟨analyticMap pt (pt_comp_structure hP) x.1, mem_tubeMap hP x⟩,
    ((analyticMap pt (pt_comp_structure hP)).hom.continuous.comp
      continuous_subtype_val).subtype_mk _⟩

private lemma tubeMap_preimageInclusion {V₀ W₀ : Opens (analyticSpace sY)} (h : W₀ ≤ V₀) :
    preimageInclusion (resolutionAnalyticMap (p ≫ sY) Φ)
        ((Opens.map (analyticMap p rfl)).monotone h) ≫ tubeMap hP V₀ =
      tubeMap hP W₀ ≫ preimageInclusion (analyticMap π (sY := sY) rfl) h :=
  rfl

include hl in
private lemma mem_tube (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY))
    {V₀ : Opens (analyticSpace sY)} (hV₀ : closedComplexPoint sY hy ∈ V₀) :
    curveOpenInclusion (p ≫ sY) T₁ t ∈ (Opens.map (analyticMap p rfl)).obj V₀ := by
  change analyticMap p rfl (curveOpenInclusion (p ≫ sY) T₁ t) ∈ V₀
  convert hV₀ using 1
  ext1
  change (t.hom ≫ T₁.ι ≫ curveι T) ≫ p = pointOfClosedPoint sY y hy
  rw [Category.assoc, Category.assoc, point_comp_eq hl hy t]

/-- On the fibre `F_t`, the tube map is the composite `F_t ⟶ F_y ⟶ π⁻¹(V₀)`. -/
private lemma pointFibreInclusion_tubeMap (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY))
    {V₀ : Opens (analyticSpace sY)} (hV₀ : closedComplexPoint sY hy ∈ V₀) :
    pointFibreInclusion (p ≫ sY) Φ T₁ t (mem_tube hl hy t hV₀) ≫ tubeMap hP V₀ =
      fibreToClosedFibreAn hP hl t ≫
        fibreIncl π sY (closedComplexPoint sY hy) (pullback.fst π _)
          (pullback.fst π _ ≫ π ≫ sY) (isPullback_pointSettingFibre sY π hy).w hV₀ := by
  refine TopCat.ext fun x ↦ Subtype.ext ?_
  ext1
  change (x.hom ≫ pointFibreFst (p ≫ sY) Φ T₁ t) ≫ pt =
    (x.hom ≫ fibreToClosedFibre hP hl t) ≫ pullback.fst π _
  rw [Category.assoc, Category.assoc, fibreToClosedFibre_fst]

/-- **The Chern class on the fibre `F_t`.** If `β` on `π⁻¹(V₀)` restricts to `c₁(N)` on `F_y`,
its pullback to the tube around `T¹` restricts to `c₁` of the pullback of `N` on every `F_t`. -/
private theorem rationalCohomologyMap_tubeMap_eq_pointFibreChernClass
    (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) (N : (pointSettingFibre π y).Modules)
    [hN : SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
      (pointSettingFibre π y).ringCatSheaf.2 N]
    {V₀ : Opens (analyticSpace sY)} (hV₀ : closedComplexPoint sY hy ∈ V₀)
    (β : rationalCohomology (preimageSpace (analyticMap π (sY := sY) rfl) V₀) 2)
    (hβ : letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
        ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
      (rationalCohomologyMap (fibreIncl π sY (closedComplexPoint sY hy) (pullback.fst π _)
          (pullback.fst π _ ≫ π ≫ sY) (isPullback_pointSettingFibre sY π hy).w hV₀) 2).hom β =
        singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N)) :
    ∃ _ : SheafOfModules.IsInvertible (pointFibre (p ≫ sY) Φ T₁ t).presheaf
        (pointFibre (p ≫ sY) Φ T₁ t).ringCatSheaf.2
        ((Scheme.Modules.pullback (pointFibreToFamily (p ≫ sY) Φ T₁ t)).obj
          ((Scheme.Modules.pullback (familyMap hP hl)).obj N)),
      (rationalCohomologyMap (pointFibreInclusion (p ≫ sY) Φ T₁ t (mem_tube hl hy t hV₀)) 2).hom
          ((rationalCohomologyMap (tubeMap hP V₀) 2).hom β) =
        pointFibreChernClass (p ≫ sY) Φ T₁ t
          ((Scheme.Modules.pullback (pointFibreToFamily (p ≫ sY) Φ T₁ t)).obj
            ((Scheme.Modules.pullback (familyMap hP hl)).obj N)) := by
  letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
    ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
  haveI : SheafOfModules.IsInvertible (pointFibre (p ≫ sY) Φ T₁ t).presheaf
      (pointFibre (p ≫ sY) Φ T₁ t).ringCatSheaf.2
      ((Scheme.Modules.pullback (fibreToClosedFibre hP hl t)).obj N) :=
    MMP.Mori.isInvertible_pullback_obj _ _
  haveI : SheafOfModules.IsInvertible (pointFibre (p ≫ sY) Φ T₁ t).presheaf
      (pointFibre (p ≫ sY) Φ T₁ t).ringCatSheaf.2
      ((Scheme.Modules.pullback (pointFibreToFamily (p ≫ sY) Φ T₁ t ≫ familyMap hP hl)).obj N) :=
    MMP.Mori.isInvertible_pullback_obj _ _
  haveI : SheafOfModules.IsInvertible (adaptedFamily Φ T₁).presheaf
      (adaptedFamily Φ T₁).ringCatSheaf.2 ((Scheme.Modules.pullback (familyMap hP hl)).obj N) :=
    MMP.Mori.isInvertible_pullback_obj _ _
  haveI : SheafOfModules.IsInvertible (pointFibre (p ≫ sY) Φ T₁ t).presheaf
      (pointFibre (p ≫ sY) Φ T₁ t).ringCatSheaf.2
      ((Scheme.Modules.pullback (pointFibreToFamily (p ≫ sY) Φ T₁ t)).obj
          ((Scheme.Modules.pullback (familyMap hP hl)).obj N)) :=
    MMP.Mori.isInvertible_pullback_obj _ _
  refine ⟨inferInstance, ?_⟩
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp,
    pointFibreInclusion_tubeMap hP hl hy t hV₀, rationalCohomologyMap_comp, ModuleCat.comp_apply,
    hβ]
  unfold pointFibreChernClass
  have e : (Scheme.Modules.pullback (pointFibreToFamily (p ≫ sY) Φ T₁ t)).obj
      ((Scheme.Modules.pullback (familyMap hP hl)).obj N) ≅
      (Scheme.Modules.pullback (pointFibreToFamily (p ≫ sY) Φ T₁ t ≫ familyMap hP hl)).obj N :=
    (Scheme.Modules.pullbackComp _ _).app N
  rw [algebraicFirstChernClass_eq_of_iso e,
    algebraicFirstChernClass_pullback (pointFibreToFamily (p ≫ sY) Φ T₁ t ≫ familyMap hP hl)
      (fibreToClosedFibreAn hP hl t) (fun _ ↦ rfl) N]
  exact (mapCoeff_map _ 2 _).symm

end Family

/-! ### Germs of classes in the punctured local system -/

section Germs

variable {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
  (hπ : IsBiregular π (smoothLocus sY)) (To : (curveScheme T).Opens)

/-- The vector `r_t(α_t) ∈ 𝒱_{T,t}` attached to a class `α` on a tube `π⁻¹(V)` around `t`. -/
private def germVec (t : analyticSpace (To.ι ≫ curveι T ≫ sY)) {V : Opens (analyticSpace sY)}
    (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    curveLocalSystemFibre sY To t :=
  (localSystemRestrictionFibre sY hπ To t).hom
    ((stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2) t).hom
      ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α))

private lemma germVec_add (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V)
    (α β : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    germVec sY hπ To t hV (α + β) = germVec sY hπ To t hV α + germVec sY hπ To t hV β := by
  simp only [germVec, map_add]
  exact map_add _ _ _

private lemma germVec_smul (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V) (c : ℚ)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    germVec sY hπ To t hV (c • α) = c • germVec sY hπ To t hV α := by
  simp only [germVec, map_smul]
  exact map_smul _ _ _

private lemma germVec_zero (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To t ∈ V) :
    germVec sY hπ To t hV (0 : rationalCohomology
      (preimageSpace (resolutionAnalyticMap sY π) V) 2) = 0 := by
  simp only [germVec, map_zero]
  exact map_zero _

private lemma germVec_res (t : analyticSpace (To.ι ≫ curveι T ≫ sY))
    {V W : Opens (analyticSpace sY)} (hWV : W ≤ V) (hW : curveOpenInclusion sY To t ∈ W)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    germVec sY hπ To t hW ((rationalCohomologyMap (preimageInclusion _ hWV) 2).hom α) =
      germVec sY hπ To t (hWV hW) α := by
  simp only [germVec, higherDirectImageGerm_res]

/-- Classes on a tube containing the whole of `T°(ℂ)` give sections of the punctured local
system whose germs are the vectors `r_t(α_t)`. -/
private theorem exists_section_germ_eq_germVec {V : Opens (analyticSpace sY)}
    (hall : ∀ t, curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    ∃ u : ToType (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (curveOpenInclusion sY To)).obj (regularHigherDirectImage sY 2))).obj
          (op ((Opens.map (curveOpenInclusion sY To)).obj V))),
      ∀ t, ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (curveOpenInclusion sY To)).obj (regularHigherDirectImage sY 2))).germ _ t (hall t) u =
        germVec sY hπ To t (hall t) α := by
  refine ⟨unitSec _ _ (((toSheafify (Opens.grothendieckTopology _)
    (directImagePresheaf (regularInclusion sY) 2)).app (op V)).hom
      ((rationalCohomologyMap (preimageRestrict (resolutionAnalyticMap sY π)
        (analyticMap (regularSection sY hπ) (by rw [← Category.assoc, regularSection_comp]))
        (regularSection_analyticMap_comp sY hπ) V) 2).hom α)), fun t ↦ ?_⟩
  rw [germVec, localSystemRestrictionFibre_germ, higherDirectImageGerm_eq_germ]
  exact (stalkToPullbackStalk_germ _ _ _ t (hall t)).symm

end Germs

/-! ### Germs are detected on the fibre -/

/-- **Germs are detected on the fibre.** For a proper `f : X ⟶ B` and a `ℂ`-point `b` of `B`, two
classes on tubes `f⁻¹(V)` and `f⁻¹(V')` around `b` with the same restriction to the fibre
`F_b(ℂ)` have the same germ in `(R^q f_* ℚ)_b`. -/
private theorem higherDirectImageGerm_eq_of_fibreIncl_eq {X B Fb : Scheme.{0}} (f : X ⟶ B)
    (sB : B ⟶ Spec (.of ℂ)) [IsProper f] [LocallyOfFiniteType sB] [IsSeparated sB]
    (b : ComplexPoints sB) (i : Fb ⟶ X) (sF : Fb ⟶ Spec (.of ℂ)) (H : IsPullback i sF f b.hom)
    (q : ℕ) {V V' : Opens (analyticSpace sB)} (hV : b ∈ V) (hV' : b ∈ V')
    (α : rationalCohomology (preimageSpace (analyticMap f (sY := sB) rfl) V) q)
    (α' : rationalCohomology (preimageSpace (analyticMap f (sY := sB) rfl) V') q)
    (h : (rationalCohomologyMap (fibreIncl f sB b i sF H.w hV) q).hom α =
      (rationalCohomologyMap (fibreIncl f sB b i sF H.w hV') q).hom α') :
    (higherDirectImageGerm (analyticMap f (sY := sB) rfl) q b hV).hom α =
      (higherDirectImageGerm (analyticMap f (sY := sB) rfl) q b hV').hom α' := by
  obtain ⟨W, hWle, hbW, hW0⟩ := (fibre_comparison f sB b i sF H q).2 _ (Opens.mem_inf.2 ⟨hV, hV'⟩)
    ((rationalCohomologyMap (preimageInclusion _ (inf_le_left : V ⊓ V' ≤ V)) q).hom α -
      (rationalCohomologyMap (preimageInclusion _ (inf_le_right : V ⊓ V' ≤ V')) q).hom α') (by
    rw [map_sub, ← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, ← ModuleCat.comp_apply,
      ← rationalCohomologyMap_comp, sub_eq_zero]
    exact h)
  have := congrArg (higherDirectImageGerm (analyticMap f (sY := sB) rfl) q b hbW).hom hW0
  rwa [map_zero, map_sub, map_sub, higherDirectImageGerm_res, higherDirectImageGerm_res,
    higherDirectImageGerm_res, higherDirectImageGerm_res, sub_eq_zero] at this

/-! ### The vectors attached to line bundles on the closed fibre span -/

section Span

variable {Y Yt Y' Yt' : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {Φ : Yt' ⟶ Y'}
  {p : Y' ⟶ Y} {pt : Yt' ⟶ Yt} (hP : IsPullback pt Φ π p) {y : Y}
  {T : IrreducibleCloseds Y'} {T₁ : (curveScheme T).Opens}
  {l : (T₁ : Scheme.{0}) ⟶ Spec (Y.residueField y)}
  (hl : l ≫ Y.fromSpecResidueField y = T₁.ι ≫ curveι T ≫ p)
  [LocallyOfFiniteType sY] (hy : IsClosed ({y} : Set Y))

private lemma fibreIncl_preimageInclusion {V₀ W₀ : Opens (analyticSpace sY)} (h : W₀ ≤ V₀)
    (hW₀ : closedComplexPoint sY hy ∈ W₀)
    (β : rationalCohomology (preimageSpace (analyticMap π (sY := sY) rfl) V₀) 2) :
    (rationalCohomologyMap (fibreIncl π sY (closedComplexPoint sY hy) (pullback.fst π _)
        (pullback.fst π _ ≫ π ≫ sY) (isPullback_pointSettingFibre sY π hy).w hW₀) 2).hom
        ((rationalCohomologyMap (preimageInclusion _ h) 2).hom β) =
      (rationalCohomologyMap (fibreIncl π sY (closedComplexPoint sY hy) (pullback.fst π _)
        (pullback.fst π _ ≫ π ≫ sY) (isPullback_pointSettingFibre sY π hy).w (h hW₀)) 2).hom β := by
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp]
  rfl

private lemma germVec_tubeMap_res (hπ : IsBiregular Φ (smoothLocus (p ≫ sY)))
    (t : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) {V₀ W₀ : Opens (analyticSpace sY)}
    (h : W₀ ≤ V₀) (hW₀ : closedComplexPoint sY hy ∈ W₀)
    (β : rationalCohomology (preimageSpace (analyticMap π (sY := sY) rfl) V₀) 2) :
    germVec (p ≫ sY) hπ T₁ t (mem_tube hl hy t hW₀)
        ((rationalCohomologyMap (tubeMap hP W₀) 2).hom
          ((rationalCohomologyMap (preimageInclusion _ h) 2).hom β)) =
      germVec (p ≫ sY) hπ T₁ t (mem_tube hl hy t (h hW₀))
        ((rationalCohomologyMap (tubeMap hP V₀) 2).hom β) := by
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, ← tubeMap_preimageInclusion hP h,
    rationalCohomologyMap_comp, ModuleCat.comp_apply, germVec_res]

variable [IsSeparated sY] [IsProper π] [LocallyOfFiniteType (p ≫ sY)] [IsSeparated (p ≫ sY)]
  [IsProper Φ]

include hP hl in
/-- **Extension to a tube.** If the vectors of the classes on tubes around `y` restricting to
`c₁(N)` on `F_y` lie in `P`, then every class on `F_y` extends to a tube with its vector in `P`. -/
private theorem exists_fibreIncl_eq_germVec_mem (hπ : IsBiregular Φ (smoothLocus (p ≫ sY)))
    (hspan : letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
        ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
      Submodule.span ℚ
        {c : analyticSingularCohomology ℚ (pointSettingFibre π y ↘ Spec (.of ℂ)) 2 |
          ∃ (M : (pointSettingFibre π y).Modules)
            (_ : SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
              (pointSettingFibre π y).ringCatSheaf.2 M),
            c = singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M)} =
        ⊤)
    (t₀ : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY))
    (P : Submodule ℚ (curveLocalSystemFibre (p ≫ sY) T₁ t₀))
    (hmem : letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
        ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
      ∀ (N : (pointSettingFibre π y).Modules)
        (_ : SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
          (pointSettingFibre π y).ringCatSheaf.2 N)
        (V₀ : Opens (analyticSpace sY)) (hV₀ : closedComplexPoint sY hy ∈ V₀)
        (β : rationalCohomology (preimageSpace (analyticMap π (sY := sY) rfl) V₀) 2),
        (rationalCohomologyMap (fibreIncl π sY (closedComplexPoint sY hy) (pullback.fst π _)
          (pullback.fst π _ ≫ π ≫ sY) (isPullback_pointSettingFibre sY π hy).w hV₀) 2).hom β =
            singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N) →
        germVec (p ≫ sY) hπ T₁ t₀ (mem_tube hl hy t₀ hV₀)
          ((rationalCohomologyMap (tubeMap hP V₀) 2).hom β) ∈ P)
    (x : rationalCohomology
      (analyticSpace (pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY)) 2) :
    ∃ (V₀ : Opens (analyticSpace sY)) (hV₀ : closedComplexPoint sY hy ∈ V₀)
      (β : rationalCohomology (preimageSpace (analyticMap π (sY := sY) rfl) V₀) 2),
      (rationalCohomologyMap (fibreIncl π sY (closedComplexPoint sY hy) (pullback.fst π _)
        (pullback.fst π _ ≫ π ≫ sY) (isPullback_pointSettingFibre sY π hy).w hV₀) 2).hom β = x ∧
      germVec (p ≫ sY) hπ T₁ t₀ (mem_tube hl hy t₀ hV₀)
        ((rationalCohomologyMap (tubeMap hP V₀) 2).hom β) ∈ P := by
  letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
    ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
  have hcmpπ := fibre_comparison π sY (closedComplexPoint sY hy) _ _
    (isPullback_pointSettingFibre sY π hy) 2
  have hx := (Submodule.eq_top_iff'.1 hspan) x
  induction hx using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨N, hN, rfl⟩ := hc
    obtain ⟨V₀, hV₀, β, hβ⟩ := hcmpπ.1
      (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N))
    exact ⟨V₀, hV₀, β, hβ, hmem N hN V₀ hV₀ β hβ⟩
  | zero =>
    refine ⟨⊤, Opens.mem_top _, 0, map_zero _, ?_⟩
    rw [map_zero, germVec_zero]
    exact zero_mem _
  | add a b _ _ ha hb =>
    obtain ⟨V₁, h₁, β₁, e₁, s₁⟩ := ha
    obtain ⟨V₂, h₂, β₂, e₂, s₂⟩ := hb
    refine ⟨V₁ ⊓ V₂, Opens.mem_inf.2 ⟨h₁, h₂⟩,
      (rationalCohomologyMap (preimageInclusion _ (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) 2).hom β₁ +
        (rationalCohomologyMap (preimageInclusion _ (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) 2).hom β₂,
      ?_, ?_⟩
    · rw [map_add, fibreIncl_preimageInclusion hy inf_le_left (Opens.mem_inf.2 ⟨h₁, h₂⟩),
        fibreIncl_preimageInclusion hy inf_le_right (Opens.mem_inf.2 ⟨h₁, h₂⟩), e₁, e₂]
      rfl
    · rw [map_add, germVec_add,
        germVec_tubeMap_res hP hl hy hπ t₀ inf_le_left (Opens.mem_inf.2 ⟨h₁, h₂⟩),
        germVec_tubeMap_res hP hl hy hπ t₀ inf_le_right (Opens.mem_inf.2 ⟨h₁, h₂⟩)]
      exact add_mem s₁ s₂
  | smul c a _ ha =>
    obtain ⟨V₁, h₁, β₁, e₁, s₁⟩ := ha
    refine ⟨V₁, h₁, c • β₁, ?_, ?_⟩
    · rw [map_smul, e₁]
      rfl
    · rw [map_smul, germVec_smul]
      exact Submodule.smul_mem _ c s₁

include hP hl in
/-- **Spanning at a closed point.** The vectors `r_{t₀}(α_{t₀})`, `α` the pullback to the tube
around `T¹` of a class `β` on a tube around `y` which restricts to `c₁(N)` on `F_y`, `N` a line
bundle on `F_y`, span `𝒱_{T,t₀}`. -/
private theorem span_germVec_eq_top (hπ : IsBiregular Φ (smoothLocus (p ≫ sY)))
    (hsurj : ∀ t, Function.Surjective (localSystemRestrictionFibre (p ≫ sY) hπ T₁ t).hom)
    (hspan : letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
        ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
      Submodule.span ℚ
        {c : analyticSingularCohomology ℚ (pointSettingFibre π y ↘ Spec (.of ℂ)) 2 |
          ∃ (M : (pointSettingFibre π y).Modules)
            (_ : SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
              (pointSettingFibre π y).ringCatSheaf.2 M),
            c = singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass M)} =
        ⊤)
    (t₀ : ComplexPoints (T₁.ι ≫ curveι T ≫ p ≫ sY)) :
    letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
      ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
    Submodule.span ℚ {v : curveLocalSystemFibre (p ≫ sY) T₁ t₀ |
      ∃ (N : (pointSettingFibre π y).Modules)
        (_ : SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
          (pointSettingFibre π y).ringCatSheaf.2 N)
        (V₀ : Opens (analyticSpace sY)) (hV₀ : closedComplexPoint sY hy ∈ V₀)
        (β : rationalCohomology (preimageSpace (analyticMap π (sY := sY) rfl) V₀) 2),
        (rationalCohomologyMap (fibreIncl π sY (closedComplexPoint sY hy) (pullback.fst π _)
          (pullback.fst π _ ≫ π ≫ sY) (isPullback_pointSettingFibre sY π hy).w hV₀) 2).hom β =
            singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N) ∧
        v = germVec (p ≫ sY) hπ T₁ t₀ (mem_tube hl hy t₀ hV₀)
          ((rationalCohomologyMap (tubeMap hP V₀) 2).hom β)} = ⊤ := by
  letI : (pointSettingFibre π y).Over (Spec (.of ℂ)) :=
    ⟨pullback.fst π (Y.fromSpecResidueField y) ≫ π ≫ sY⟩
  set S := {v : curveLocalSystemFibre (p ≫ sY) T₁ t₀ |
      ∃ (N : (pointSettingFibre π y).Modules)
        (_ : SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
          (pointSettingFibre π y).ringCatSheaf.2 N)
        (V₀ : Opens (analyticSpace sY)) (hV₀ : closedComplexPoint sY hy ∈ V₀)
        (β : rationalCohomology (preimageSpace (analyticMap π (sY := sY) rfl) V₀) 2),
        (rationalCohomologyMap (fibreIncl π sY (closedComplexPoint sY hy) (pullback.fst π _)
          (pullback.fst π _ ≫ π ≫ sY) (isPullback_pointSettingFibre sY π hy).w hV₀) 2).hom β =
            singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass N) ∧
        v = germVec (p ≫ sY) hπ T₁ t₀ (mem_tube hl hy t₀ hV₀)
          ((rationalCohomologyMap (tubeMap hP V₀) 2).hom β)}
  have key := exists_fibreIncl_eq_germVec_mem hP hl hy hπ hspan t₀ (Submodule.span ℚ S)
    fun N hN V₀ hV₀ β hβ ↦ Submodule.subset_span ⟨N, hN, V₀, hV₀, β, hβ, rfl⟩
  have Ht : IsPullback (pointFibreFst (p ≫ sY) Φ T₁ t₀) (pointFibreSnd (p ≫ sY) Φ T₁ t₀) Φ
      (curveOpenInclusion (p ≫ sY) T₁ t₀).hom :=
    IsPullback.of_hasPullback _ _
  rw [eq_top_iff]
  rintro v -
  obtain ⟨w, rfl⟩ := hsurj t₀ v
  obtain ⟨w', rfl⟩ := (bijective_stalkToPullbackStalk (curveOpenInclusion (p ≫ sY) T₁)
    (resolutionHigherDirectImage (p ≫ sY) Φ 2) t₀).2 w
  obtain ⟨V', hV', α', rfl⟩ :=
    exists_higherDirectImageGerm_eq (resolutionAnalyticMap (p ≫ sY) Φ) 2 _ w'
  obtain ⟨V₀, hV₀, β, hβ, hmem⟩ := key ((rationalCohomologyMap
    (analyticMap (closedFibreToFibre hP hl hy t₀) (closedFibreToFibre_structure hP hl hy t₀))
      2).hom ((rationalCohomologyMap (pointFibreInclusion (p ≫ sY) Φ T₁ t₀ hV') 2).hom α'))
  have hfib : (rationalCohomologyMap
      (pointFibreInclusion (p ≫ sY) Φ T₁ t₀ (mem_tube hl hy t₀ hV₀)) 2).hom
        ((rationalCohomologyMap (tubeMap hP V₀) 2).hom β) =
      (rationalCohomologyMap (pointFibreInclusion (p ≫ sY) Φ T₁ t₀ hV') 2).hom α' := by
    rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp,
      pointFibreInclusion_tubeMap hP hl hy t₀ hV₀, rationalCohomologyMap_comp, ModuleCat.comp_apply,
      hβ, rationalCohomologyMap_fibreToClosedFibreAn_section]
  change germVec (p ≫ sY) hπ T₁ t₀ hV' α' ∈ _
  convert hmem using 1
  exact congrArg (fun z ↦ (localSystemRestrictionFibre (p ≫ sY) hπ T₁ t₀).hom
    ((stalkToPullbackStalk (curveOpenInclusion (p ≫ sY) T₁)
      (resolutionHigherDirectImage (p ≫ sY) Φ 2) t₀).hom z))
    (higherDirectImageGerm_eq_of_fibreIncl_eq Φ (p ≫ sY) _ _ _ Ht 2 hV' (mem_tube hl hy t₀ hV₀)
      α' _ hfib.symm)

end Span

/-! ### The product with `ℙ¹` -/

/-- `q × id_L : Y₁ × L ⟶ Y × L` is the base change of `q : Y₁ ⟶ Y` along the projection
`Y × L ⟶ Y`. -/
private theorem isPullback_map_fst {S Y L Y₁ : Scheme.{0}} (sY : Y ⟶ S) (sL : L ⟶ S)
    (q : Y₁ ⟶ Y) :
    IsPullback (pullback.map (q ≫ sY) sL sY sL q (𝟙 L) (𝟙 _) (by simp) (by simp))
      (pullback.fst (q ≫ sY) sL) (pullback.fst sY sL) q := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback sY sL).flip
  simpa using (IsPullback.of_hasPullback (q ≫ sY) sL).flip

private lemma range_curveι_base {Y : Scheme.{0}} (T : IrreducibleCloseds Y) :
    Set.range (curveι T).base = (T : Set Y) := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- The image of the generic point of a dense open of the curve `T` is the generic point of
`T`. -/
private theorem base_genericPoint_eq_localSettingGenericPoint {Y : Scheme.{0}}
    {T : IrreducibleCloseds Y} (T₁ : (curveScheme T).Opens) [IrreducibleSpace T₁]
    (hT₁ : Dense (T₁ : Set (curveScheme T))) :
    (T₁.ι ≫ curveι T).base (genericPoint T₁) = localSettingGenericPoint T := by
  have hrT := range_curveι_base T
  have hgen : IsGenericPoint ((T₁.ι ≫ curveι T).base (genericPoint T₁)) (T : Set Y) := by
    refine subset_antisymm ?_ ?_
    · refine T.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 ?_)
      rw [← hrT]
      exact ⟨_, rfl⟩
    · have h1 : (T₁ : Set (curveScheme T)) ⊆ closure {T₁.ι.base (genericPoint T₁)} := by
        intro z hz
        have := image_closure_subset_closure_image (f := T₁.ι.base) T₁.ι.base.hom.continuous
          ⟨⟨z, hz⟩, (genericPoint_spec T₁).symm ▸ Set.mem_univ _, rfl⟩
        rwa [Set.image_singleton] at this
      have h2 : Set.univ ⊆ closure {T₁.ι.base (genericPoint T₁)} := by
        rw [← hT₁.closure_eq]
        exact closure_minimal h1 isClosed_closure
      rw [← hrT, ← Set.image_univ]
      refine (Set.image_mono h2).trans ((image_closure_subset_closure_image
        (curveι T).base.hom.continuous).trans ?_)
      rw [Set.image_singleton]
      rfl
  exact hgen.eq (isGenericPoint_localSettingGenericPoint T)

/-! ### The punctured-independent family -/

/-- **A punctured-independent family pulled back from the closed fibre.** Let `(Y, π, y)` be a
threefold point setting, `T_y = {y} × ℙ¹ ⊆ Y × ℙ¹` and `T°` a local-system open of `T_y`, so that
`b = curveLocalSystemRank T°` is the rank `b_{T_y}`. Then `π × id : Ỹ × ℙ¹ ⟶ Y × ℙ¹` is an
isomorphism over the smooth locus, and there are invertible modules `M_1, …, M_b` on
`F_y = Ỹ ×_Y Spec κ(y)` whose pullbacks to the generic scheme fibre
`F_{η_{T_y}} = F_y ×_ℂ Spec K_{T_y}` of `π × id` are punctured-independent. -/
@[mmp "lem_mmp_indexb_product_punctured_family"]
public theorem _root_.MMP.Fourfold.IsThreefoldPointSetting.exists_isPuncturedIndependent_pullback
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {π : Yt ⟶ Y} {y : Y} (h : IsThreefoldPointSetting sY π y)
    (T : IrreducibleCloseds ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ))))
    (hT : (T : Set ↥(pullback sY (projectiveLine ℂ ↘ Spec (.of ℂ)))) = pointSettingCurve sY y)
    (To : (curveScheme T).Opens)
    (hTo : IsLocalSystemOpen (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To) :
    ∃ M : Fin (curveLocalSystemRank
        (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To) →
        (pointSettingFibre π y).Modules,
      (∀ i, SheafOfModules.IsInvertible (pointSettingFibre π y).presheaf
        (pointSettingFibre π y).ringCatSheaf.2 (M i)) ∧
      ∃ hπ : IsBiregular
          (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
            (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp))
          (smoothLocus (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)),
        IsPuncturedIndependent (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) hπ
          (T := T) fun i ↦ (Scheme.Modules.pullback
            (pullback.map _ _ π (Y.fromSpecResidueField y)
              (pullback.fst (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)))
              (Spec.map ((pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).residueFieldMap
                  (localSettingGenericPoint T)) ≫
                Spec.map (Y.residueFieldCongr (show y =
                  (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))).base
                    (localSettingGenericPoint T) from
                  ((Set.ext_iff.1 hT _).1
                    (isGenericPoint_localSettingGenericPoint T).mem).symm)).hom)
              (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))) (by simp)
              (by
                rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
                  Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]) :
              genericFibre _ T ⟶ pointSettingFibre π y)).obj (M i) := by
  classical
  obtain ⟨⟨hI, hLN, hN, T', hT', hLS⟩, -, -, -, -⟩ := h.isLocalSetting_pullback_projectiveLine
  obtain rfl : T = T' := (IrreducibleCloseds.ext (hT'.trans hT.symm)).symm
  haveI := hI
  haveI := hLN
  haveI := hN
  have hP := (isPullback_map_fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) π).flip
  haveI hYv : AlgebraicGeometry.IsVariety ℂ sY := h.isQFactorial.1.1
  haveI hY'v : AlgebraicGeometry.IsVariety ℂ
      (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) := hLS.isQFactorial.1.1
  haveI : IsProper π := isProper_of_isProjectiveMorphism _ h.isResolution.2.2.2.1
  haveI : IsProper (pullback.map (π ≫ sY) (projectiveLine ℂ ↘ Spec (.of ℂ)) sY
      (projectiveLine ℂ ↘ Spec (.of ℂ)) π (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    isProper_of_isProjectiveMorphism _ hLS.isResolution.2.2.2.1
  obtain ⟨⟨T₁, hT₁⟩, -⟩ := hLS.exists_isAdaptedOpen_and_isAdaptedOpen_of_le
  obtain ⟨hT₁v, hT₁c⟩ := isLocalSystemOpen_facts hY'v hT₁.toIsLocalSystemOpen
  haveI := hT₁v
  haveI := hT₁c
  haveI : IsIntegral (T₁ : Scheme.{0}) := hT₁v.toIsIntegral
  obtain ⟨t₀⟩ := nonempty_complexPoints
    (T₁.ι ≫ curveι T ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
  have hy := h.isClosed_singleton
  -- the curve `T¹` maps to the closed point `y`
  have hrT := range_curveι_base T
  haveI : IsReduced (T₁ : Scheme.{0}) := isReduced_of_isOpenImmersion T₁.ι
  obtain ⟨l, hl⟩ := exists_comp_fromSpecResidueField_eq
    (T₁.ι ≫ curveι T ≫ pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ))) hy (by
      rintro _ ⟨z, rfl⟩
      have hz : (curveι T).base (T₁.ι.base z) ∈ (T : Set _) := by
        rw [← hrT]
        exact ⟨_, rfl⟩
      rw [hT, pointSettingCurve, Set.mem_preimage] at hz
      exact hz)
  -- the rank `b`
  obtain ⟨K, hK⟩ : ∃ K : Submodule ℚ (curveLocalSystemFibre
      (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) T₁ t₀),
      curveLocalSystemRank (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) To =
        Module.finrank ℚ (curveLocalSystemFibre
          (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) T₁ t₀ ⧸ K) :=
    ⟨_, ((IsLocalSystemOpen.curveLocalSystemRank_eq hY'v hLS.topologicalKrullDim_eq
      hLS.topologicalKrullDim_curve hLS.subset_singularLocus hTo hT₁.toIsLocalSystemOpen).1).trans
      ((IsLocalSystemOpen.curveLocalSystemRank_eq hY'v hLS.topologicalKrullDim_eq
        hLS.topologicalKrullDim_curve hLS.subset_singularLocus hT₁.toIsLocalSystemOpen
        hT₁.toIsLocalSystemOpen).2 t₀)⟩
  -- spanning at `t₀` and selection of `b` independent vectors
  have hS := span_germVec_eq_top hP hl hy hLS.isBiregular
    (fun t ↦ surjective_localSystemRestrictionFibre hLS hT₁ t)
    (h.subsingleton_cohomologyOverField_two_and_span_firstChernClass).2 t₀
  obtain ⟨v, hvS, hvli⟩ := exists_linearIndependent_fin_finrank_quotient K hS
  simp only [Set.mem_setOf_eq] at hvS
  choose N hNi V₀ hV₀ β hβ hv using hvS
  -- a common tube
  let W₀ : Opens (analyticSpace sY) :=
    ⟨⋂ i, (V₀ i : Set (analyticSpace sY)), isOpen_iInter_of_finite fun i ↦ (V₀ i).isOpen⟩
  have hW₀ : closedComplexPoint sY hy ∈ W₀ := Set.mem_iInter.2 hV₀
  have hW₀le : ∀ i, W₀ ≤ V₀ i := fun i ↦ Set.iInter_subset _ i
  let β' := fun i ↦ (rationalCohomologyMap (preimageInclusion _ (hW₀le i)) 2).hom (β i)
  let c : Fin (curveLocalSystemRank (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY)
    To) → Fin (Module.finrank ℚ (curveLocalSystemFibre
      (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) T₁ t₀ ⧸ K)) := Fin.cast hK
  -- the sections of the punctured local system
  have hsec := fun i ↦ exists_section_germ_eq_germVec
    (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) hLS.isBiregular T₁
    (fun t ↦ mem_tube hl hy t hW₀) ((rationalCohomologyMap (tubeMap hP W₀) 2).hom (β' (c i)))
  choose u hu using hsec
  have hli₀ : LinearIndependent ℚ fun i ↦ ((TopCat.Sheaf.forget _ _).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion
        (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) T₁)).obj
          (regularHigherDirectImage
            (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) 2))).germ _ t₀
      (mem_tube hl hy t₀ hW₀) (u i) := by
    have : (fun i ↦ ((TopCat.Sheaf.forget _ _).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion
          (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) T₁)).obj
            (regularHigherDirectImage
              (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) 2))).germ _ t₀
        (mem_tube hl hy t₀ hW₀) (u i)) = v ∘ c := by
      funext i
      rw [hu, Function.comp_apply, hv,
        germVec_tubeMap_res hP hl hy hLS.isBiregular t₀ (hW₀le (c i)) hW₀]
    rw [this]
    exact hvli.comp c (Fin.cast_injective hK)
  -- the generic point of `T¹`
  have e := base_genericPoint_eq_localSettingGenericPoint T₁ hT₁.dense
  refine ⟨fun i ↦ N (c i), fun i ↦ hNi (c i), hLS.isBiregular, ?_⟩
  unfold IsPuncturedIndependent
  refine ⟨T₁, hT₁, fun i ↦ (Scheme.Modules.pullback (familyMap hP hl)).obj (N (c i)),
    fun i ↦ MMP.Mori.isInvertible_pullback_obj (hL := hNi (c i)) _ _,
    ⟨genericPoint T₁, e, fun i ↦ ⟨(Scheme.Modules.pullbackComp _ _).app _ ≪≫
      (Scheme.Modules.pullbackCongr (curveOpenFibreToFamily_familyMap hP hl _ e _)).app _ ≪≫
      ((Scheme.Modules.pullbackComp _ _).app _).symm⟩⟩,
    fun t ↦ ⟨_, mem_tube hl hy t hW₀,
      fun i ↦ (rationalCohomologyMap (tubeMap hP W₀) 2).hom (β' (c i)), fun i ↦ ?_, ?_⟩⟩
  · haveI := hNi (c i)
    exact rationalCohomologyMap_tubeMap_eq_pointFibreChernClass hP hl hy t (N (c i)) hW₀
      (β' (c i)) (by
        rw [fibreIncl_preimageInclusion hy (hW₀le (c i)) hW₀]
        exact hβ (c i))
  · have := linearIndependent_germ_of_linearIndependent_germ
      (F := (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion
        (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) T₁)).obj
          (regularHigherDirectImage (pullback.fst sY (projectiveLine ℂ ↘ Spec (.of ℂ)) ≫ sY) 2))
      hT₁.isLocalSystem (fun t ↦ mem_tube hl hy t hW₀) u t₀ t hli₀
    rwa [funext fun i ↦ hu i t] at this

end Proof_lem_mmp_indexb_product_punctured_family

end
