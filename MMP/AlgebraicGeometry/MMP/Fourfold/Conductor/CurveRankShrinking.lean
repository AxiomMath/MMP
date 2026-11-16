module
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.Topology.Sheaves.LocalSystem.ParallelTransport
import MMP.AlgebraicGeometry.Analytic.Curve.TopCompactCohomology
import MMP.AlgebraicGeometry.Analytic.SmoothHolomorphicCharts
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Basic

/-!
# The rank of the punctured local system does not depend on the open

Let `Y` be a normal complex fourfold, `j : Y_reg ↪ Y` the inclusion of the smooth locus and
`T ⊆ Sing Y` an irreducible curve. For a local-system open `T° ⊆ T`
(`MMP.Fourfold.IsLocalSystemOpen`) the rank `b_T = dim_ℚ H²_c(T°, 𝒱_T)`
(`MMP.Fourfold.curveLocalSystemRank`) of the punctured local system `𝒱_T`
(`MMP.Fourfold.curveLocalSystem`) is the dimension of the monodromy coinvariants of the fibre
`𝒱_{T,t}` at any point `t ∈ T°(ℂ)`, the quotient of `𝒱_{T,t}` by the span of the vectors
`w - γ·w` for `γ` a loop at `t`. Two local-system opens give the same rank: their intersection
is again one, the local system on it is the restriction, and the fundamental group of a dense
Zariski-open of a smooth connected curve surjects onto that of the curve, so the monodromy
coinvariants agree.

## Main results

* `MMP.Fourfold.IsLocalSystemOpen.curveLocalSystemRank_eq`: `b_T` is the same for any two
  local-system opens, and equals the dimension of the monodromy coinvariants of every fibre.

## Implementation notes

The action of a loop `γ` at `t` on `𝒱_{T,t}` is parallel transport: `γ·w = v` exactly when some
global section of the inverse image `γ^* 𝒱_T` on `[0, 1]` has germ `w` at `0` and germ `v` at
`1`, fibres of `γ^* 𝒱_T` being identified with those of `𝒱_T` by
`MMP.Fourfold.stalkToPullbackStalk`. Loops are taken as paths rather than homotopy classes;
transport depends only on the class, so the span of the differences is the same.

The proof reads the coinvariants of `T°` and of `T°'` at a point of `T° ∩ T°'`, in the stalk of
the one sheaf `R²j_* ℚ` on `Y^an` of which all three local systems are inverse images. A loop in
the intersection is a loop in the larger open, and conversely every loop in `T°` is homotopic to
one in `T° ∩ T°'`; parallel transport depends only on the homotopy class. The complex
realization of a local-system open is connected because the regular part of an integral complex
variety is connected and dense in it.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Abstract

variable {A B Z : TopCat.{0}} (V : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

private lemma stalkPushforward_naturality (f : A ⟶ B)
    {F G : TopCat.Presheaf (ModuleCat.{0} ℚ) A} (g : F ⟶ G) (x : A) :
    TopCat.Presheaf.stalkPushforward _ f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map g =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map g) ≫
        TopCat.Presheaf.stalkPushforward _ f G x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
  rfl

private lemma stalkPushforward_comp_naturality (f : A ⟶ B)
    {F' : TopCat.Presheaf (ModuleCat.{0} ℚ) B} {G G' : TopCat.Presheaf (ModuleCat.{0} ℚ) A}
    (u : F' ⟶ (TopCat.Presheaf.pushforward _ f).obj G) (v : G ⟶ G') (x : A) :
    ((TopCat.Presheaf.stalkFunctor _ (f x)).map u ≫ TopCat.Presheaf.stalkPushforward _ f G x) ≫
        (TopCat.Presheaf.stalkFunctor _ x).map v =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map (u ≫ (TopCat.Presheaf.pushforward _ f).map v) ≫
        TopCat.Presheaf.stalkPushforward _ f G' x := by
  refine (Category.assoc _ _ _).trans ?_
  erw [stalkPushforward_naturality f v x, Functor.map_comp, Category.assoc]
  rfl

/-- The adjunction for the composite pullback, with right adjoint the pushforward along the
composite. -/
private noncomputable def compAdj (p : A ⟶ B) (g : B ⟶ Z) :
    TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) p ⊣
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (p ≫ g) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) p)).ofNatIsoRight
      (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- The comparison of the pullback along a composite with the composite of pullbacks. -/
private noncomputable def sheafPullbackCompIso (p : A ⟶ B) (g : B ⟶ Z) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (p ≫ g)).obj V ≅
      (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) p).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj V) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (p ≫ g)).leftAdjointUniq
    (compAdj p g)).app V

private lemma sheafPullbackCompIso_stalk (p : A ⟶ B) (g : B ⟶ Z) (x : A)
    (w : ((TopCat.Sheaf.forget _ Z).obj V).stalk (g (p x))) :
    (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ A).map
        (sheafPullbackCompIso V p g).hom) ((stalkToPullbackStalk (p ≫ g) V x).hom w) =
      (stalkToPullbackStalk p ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj V) x).hom
        ((stalkToPullbackStalk g V (p x)).hom w) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) (p ≫ g)) (compAdj p g) V
  have hu' := (TopCat.Sheaf.forget _ Z).congr_map hu
  have key : stalkToPullbackStalk (p ≫ g) V x ≫ (TopCat.Presheaf.stalkFunctor _ x).map
      ((TopCat.Sheaf.forget _ A).map (sheafPullbackCompIso V p g).hom) =
      stalkToPullbackStalk g V (p x) ≫
        stalkToPullbackStalk p ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj V) x := by
    unfold stalkToPullbackStalk
    refine (stalkPushforward_comp_naturality (p ≫ g) _ _ x).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ _) (stalkPushforward_comp_naturality g _ _ (p x))).symm
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    erw [← TopCat.Presheaf.stalkPushforward.comp]
    congr 2
  exact congrArg (fun φ => φ.hom w) key

private theorem bijective_stalkToPullbackStalk (f : A ⟶ B)
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) B) (x : A) :
    Function.Bijective (stalkToPullbackStalk f F x).hom :=
  have := isIso_stalkToPullbackStalk f F x
  ConcreteCategory.bijective_of_isIso (stalkToPullbackStalk f F x)

private lemma stalkCongr_of_eq_apply {X : TopCat.{0}} (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X)
    {x y : X} (h : x = y) (e : (ToType (F.stalk x)) = ToType (F.stalk y)) (w : F.stalk x) :
    (F.stalkCongr (.of_eq h)).hom.hom w = cast e w := by
  subst h
  change (F.stalkSpecializes (specializes_refl x)).hom w = w
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

private lemma stalkCongr_rfl_apply {X : TopCat.{0}} (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X)
    {x : X} (h : x = x) (w : F.stalk x) :
    (F.stalkCongr (.of_eq h)).hom.hom w = w :=
  stalkCongr_of_eq_apply F h rfl w

/-- `w` and `v` are the end germs of a global section of the inverse image of `V` along the
path `p` of the unit interval. -/
private def TransportRel (p : TopCat.of unitInterval ⟶ Z) {z₀ z₁ : Z} (h₀ : z₀ = p 0)
    (h₁ : z₁ = p 1) (w : ((TopCat.Sheaf.forget _ Z).obj V).stalk z₀)
    (v : ((TopCat.Sheaf.forget _ Z).obj V).stalk z₁) : Prop :=
  ∃ s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) p).obj V).obj.obj (op ⊤)),
    (stalkToPullbackStalk p V 0).hom
        ((((TopCat.Sheaf.forget _ Z).obj V).stalkCongr (.of_eq h₀)).hom.hom w) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) p).obj V)).germ
        ⊤ 0 trivial).hom s ∧
    (stalkToPullbackStalk p V 1).hom
        ((((TopCat.Sheaf.forget _ Z).obj V).stalkCongr (.of_eq h₁)).hom.hom v) =
      (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) p).obj V)).germ
        ⊤ 1 trivial).hom s

private lemma transportRel_congr {p p' : TopCat.of unitInterval ⟶ Z} (hp : p = p') {z₀ z₁ : Z}
    {h₀ : z₀ = p 0} {h₁ : z₁ = p 1} {h₀' : z₀ = p' 0} {h₁' : z₁ = p' 1}
    {w : ((TopCat.Sheaf.forget _ Z).obj V).stalk z₀}
    {v : ((TopCat.Sheaf.forget _ Z).obj V).stalk z₁} :
    TransportRel V p h₀ h₁ w v → TransportRel V p' h₀' h₁' w v := by
  subst hp
  exact id

private lemma germ_map_hom {X : TopCat.{0}} {P Q : TopCat.Sheaf (ModuleCat.{0} ℚ) X} (Ψ : P ⟶ Q)
    (x : X) (s : ToType (P.obj.obj (op ⊤))) :
    (((TopCat.Sheaf.forget _ X).obj Q).germ ⊤ x trivial).hom
        ((((TopCat.Sheaf.forget _ X).map Ψ).app (op ⊤)).hom s) =
      (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ)
        ((((TopCat.Sheaf.forget _ X).obj P).germ ⊤ x trivial).hom s) :=
  (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial _ s).symm

private lemma stalk_inv_hom_apply {X : TopCat.{0}} {P Q : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (Ψ : P ≅ Q) (x : X) (a : ((TopCat.Sheaf.forget _ X).obj P).stalk x) :
    (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ.inv)
      ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ X).map Ψ.hom) a) = a :=
  ((TopCat.Presheaf.stalkFunctor _ x).mapIso
    ((TopCat.Sheaf.forget _ X).mapIso Ψ)).hom_inv_id_apply a

private lemma transportRel_pullback_iff (p : TopCat.of unitInterval ⟶ B) (g : B ⟶ Z)
    {b₀ b₁ : B} (h₀ : b₀ = p 0) (h₁ : b₁ = p 1)
    (w : ((TopCat.Sheaf.forget _ Z).obj V).stalk (g b₀))
    (v : ((TopCat.Sheaf.forget _ Z).obj V).stalk (g b₁)) :
    TransportRel ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj V) p h₀ h₁
        ((stalkToPullbackStalk g V b₀).hom w) ((stalkToPullbackStalk g V b₁).hom v) ↔
      TransportRel V (p ≫ g) (congrArg g h₀) (congrArg g h₁) w v := by
  subst h₀ h₁
  unfold TransportRel
  simp only [stalkCongr_rfl_apply]
  let Ψ := sheafPullbackCompIso V p g
  constructor
  · rintro ⟨s', h0, h1⟩
    refine ⟨(((TopCat.Sheaf.forget _ _).map Ψ.inv).app (op ⊤)).hom s', ?_, ?_⟩
    · rw [germ_map_hom, ← h0, ← sheafPullbackCompIso_stalk, stalk_inv_hom_apply]
    · rw [germ_map_hom, ← h1, ← sheafPullbackCompIso_stalk, stalk_inv_hom_apply]
  · rintro ⟨s, h0, h1⟩
    refine ⟨(((TopCat.Sheaf.forget _ _).map Ψ.hom).app (op ⊤)).hom s, ?_, ?_⟩
    · rw [germ_map_hom, ← h0, sheafPullbackCompIso_stalk]
    · rw [germ_map_hom, ← h1, sheafPullbackCompIso_stalk]

/-- The differences `w - v` of the end germs of global sections of the pullback of `L` along
loops `γ` at `t`. -/
private def pathRel {X : TopCat.{0}} (L : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (t : X) :
    Set (((TopCat.Sheaf.forget _ X).obj L).stalk t) :=
  {u | ∃ (γ : Path t t) (w v : ((TopCat.Sheaf.forget _ X).obj L).stalk t),
    TransportRel L (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
      γ.source.symm γ.target.symm w v ∧ u = w - v}

/-- The differences `w - v` of the end germs, in the stalk of `V` at `g t`, of global sections
of the pullback of `V` along `γ ≫ g` for loops `γ` at `t`. -/
private def pushRel {X : TopCat.{0}} (g : X ⟶ Z) (t : X) :
    Set (((TopCat.Sheaf.forget _ Z).obj V).stalk (g t)) :=
  {u | ∃ (γ : Path t t) (w v : ((TopCat.Sheaf.forget _ Z).obj V).stalk (g t)),
    TransportRel V (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap ≫ g)
      (congrArg g γ.source.symm) (congrArg g γ.target.symm) w v ∧ u = w - v}

private lemma pathRel_pullback (g : B ⟶ Z) (t : B) :
    pathRel ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj V) t =
      (stalkToPullbackStalk g V t).hom '' pushRel V g t := by
  have hb := bijective_stalkToPullbackStalk g V t
  ext u
  constructor
  · rintro ⟨γ, w', v', hR, rfl⟩
    obtain ⟨w, rfl⟩ := hb.2 w'
    obtain ⟨v, rfl⟩ := hb.2 v'
    exact ⟨w - v, ⟨γ, w, v, (transportRel_pullback_iff V _ g _ _ w v).1 hR, rfl⟩, map_sub _ _ _⟩
  · rintro ⟨_, ⟨γ, w, v, hR, rfl⟩, rfl⟩
    exact ⟨γ, _, _, (transportRel_pullback_iff V _ g _ _ w v).2 hR, map_sub _ _ _⟩

private lemma finrank_pathRel_pullback (g : B ⟶ Z) (t : B) :
    Module.finrank ℚ (((TopCat.Sheaf.forget _ B).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj V)).stalk t ⧸
        Submodule.span ℚ (pathRel ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj V) t)) =
      Module.finrank ℚ (((TopCat.Sheaf.forget _ Z).obj V).stalk (g t) ⧸
        Submodule.span ℚ (pushRel V g t)) := by
  let e := LinearEquiv.ofBijective (stalkToPullbackStalk g V t).hom
    (bijective_stalkToPullbackStalk g V t)
  have hspan : (Submodule.span ℚ (pushRel V g t)).map (e : _ →ₗ[ℚ] _) =
      Submodule.span ℚ (pathRel ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj V) t) := by
    rw [pathRel_pullback, ← Submodule.span_image]
    rfl
  exact (LinearEquiv.finrank_eq (Submodule.Quotient.equiv _ _ e hspan)).symm

/-- A sheaf isomorphic to a constant sheaf has a global section with any prescribed germ. -/
private lemma exists_global_germ_eq {W : TopCat.{0}} {P : TopCat.Sheaf (ModuleCat.{0} ℚ) W}
    {E : ModuleCat.{0} ℚ}
    (φ : P ≅ (constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E) (x : W)
    (c : ((TopCat.Sheaf.forget _ W).obj P).stalk x) :
    ∃ s : ToType (P.obj.obj (op ⊤)),
      c = (((TopCat.Sheaf.forget _ W).obj P).germ ⊤ x trivial).hom s := by
  obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E x
    ((TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ W).map φ.hom) c)
  refine ⟨(((TopCat.Sheaf.forget _ _).map φ.inv).app (op ⊤)).hom (constSection E e), ?_⟩
  exact (stalk_inv_hom_apply φ x c).symm.trans ((congrArg _ he.symm).trans
    (germ_map_hom φ.inv x _).symm)

private lemma pushRel_comp {X X'' : TopCat.{0}} [LocallyPathConnectedSpace X] (c : X ⟶ Z)
    (i : X'' ⟶ X) (t'' : X'')
    (hL : IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c).obj V))
    (hloop : ∀ γ : Path (i t'') (i t''), ∃ γ'' : Path t'' t'',
      γ.Homotopic (γ''.map i.hom.continuous)) :
    pushRel V c (i t'') = pushRel V (i ≫ c) t'' := by
  have hmap : ∀ γ'' : Path t'' t'',
      TopCat.ofHom (X := TopCat.of unitInterval) (γ''.map i.hom.continuous).toContinuousMap ≫ c =
        TopCat.ofHom (X := TopCat.of unitInterval) γ''.toContinuousMap ≫ (i ≫ c) := fun _ => rfl
  have hinj : ∀ {a b : X} (h : a = b), Function.Injective
      (((TopCat.Sheaf.forget _ X).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c).obj V)).stalkCongr (.of_eq h)).hom.hom :=
    fun h => (ConcreteCategory.bijective_of_isIso (C := ModuleCat.{0} ℚ) _).1
  ext u
  constructor
  · rintro ⟨γ, w, v, hR, rfl⟩
    obtain ⟨γ'', hγ⟩ := hloop γ
    let δ := γ''.map i.hom.continuous
    have hTγ : (hL.parallelTransport (Path.Homotopic.Quotient.mk γ)).hom
        ((stalkToPullbackStalk c V _).hom w) =
        (stalkToPullbackStalk c V _).hom v := by
      obtain ⟨s, h0, h1⟩ := (transportRel_pullback_iff V _ c γ.source.symm γ.target.symm w v).2 hR
      have key := hL.parallelTransport_germ γ s ((stalkToPullbackStalk c V _).hom w)
        (by rw [← stalkCongr_of_eq_apply _ γ.source.symm]; exact h0)
      rw [← stalkCongr_of_eq_apply _ γ.target.symm] at key
      exact hinj γ.target.symm ((bijective_stalkToPullbackStalk _ _ 1).1 (key.trans h1.symm))
    have hTδ : hL.parallelTransport (Path.Homotopic.Quotient.mk γ) =
        hL.parallelTransport (Path.Homotopic.Quotient.mk δ) :=
      congrArg hL.parallelTransport (Path.Homotopic.Quotient.eq.2 hγ)
    obtain ⟨φ⟩ := hL.nonempty_pullback_path_iso_constantSheaf δ
    obtain ⟨s, h0⟩ := exists_global_germ_eq φ 0
      ((stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) δ.toContinuousMap)
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c).obj V) 0).hom
          ((((TopCat.Sheaf.forget _ X).obj
            ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c).obj V)).stalkCongr
              (.of_eq δ.source.symm)).hom.hom ((stalkToPullbackStalk c V _).hom w)))
    have h1 := hL.parallelTransport_germ δ s ((stalkToPullbackStalk c V _).hom w)
      (by rw [← stalkCongr_of_eq_apply _ δ.source.symm]; exact h0)
    rw [← stalkCongr_of_eq_apply _ δ.target.symm, ← hTδ, hTγ] at h1
    have hRδ : TransportRel ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c).obj V)
        (TopCat.ofHom (X := TopCat.of unitInterval) δ.toContinuousMap) δ.source.symm
        δ.target.symm ((stalkToPullbackStalk c V _).hom w)
        ((stalkToPullbackStalk c V _).hom v) := ⟨s, h0, h1⟩
    exact ⟨γ'', w, v, transportRel_congr V (hmap γ'')
      ((transportRel_pullback_iff V _ c _ _ w v).1 hRδ), rfl⟩
  · rintro ⟨γ'', w, v, hR, rfl⟩
    exact ⟨γ''.map i.hom.continuous, w, v, transportRel_congr V (hmap γ'').symm hR, rfl⟩

private lemma pathRel_eq {X : TopCat.{0}} (L : TopCat.Sheaf (ModuleCat.{0} ℚ) X) (t : X) :
    {u | ∃ (γ : Path t t)
        (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L).obj.obj (op ⊤)))
        (w v : ((TopCat.Sheaf.forget _ _).obj L).stalk t),
        (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
            L 0).hom
          ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.source.symm)).hom.hom w) =
          (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L)).germ
              ⊤ 0 trivial).hom s ∧
        (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
            L 1).hom
          ((((TopCat.Sheaf.forget _ _).obj L).stalkCongr (.of_eq γ.target.symm)).hom.hom v) =
          (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj L)).germ
              ⊤ 1 trivial).hom s ∧
        u = w - v} = pathRel L t := by
  ext u
  constructor
  · rintro ⟨γ, s, w, v, h0, h1, rfl⟩
    exact ⟨γ, w, v, ⟨s, h0, h1⟩, rfl⟩
  · rintro ⟨γ, w, v, ⟨s, h0, h1⟩, rfl⟩
    exact ⟨γ, s, w, v, h0, h1, rfl⟩

/-- **Shrinking the space does not change the coinvariants.** If every loop at `i t''` is
homotopic to the image of a loop at `t''`, the coinvariant spaces of `c^* V` at `i t''` and of
`(i ≫ c)^* V` at `t''` have the same dimension. -/
private lemma finrank_coinvariants_eq {X X'' : TopCat.{0}} [LocallyPathConnectedSpace X]
    (c : X ⟶ Z) (i : X'' ⟶ X) (c'' : X'' ⟶ Z) (hc : i ≫ c = c'') (t'' : X'')
    (hL : IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c).obj V))
    (hloop : ∀ γ : Path (i t'') (i t''), ∃ γ'' : Path t'' t'',
      γ.Homotopic (γ''.map i.hom.continuous)) :
    Module.finrank ℚ (((TopCat.Sheaf.forget _ X).obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c).obj V)).stalk (i t'') ⧸
        Submodule.span ℚ (pathRel ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c).obj V) (i t''))) =
      Module.finrank ℚ (((TopCat.Sheaf.forget _ X'').obj
        ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c'').obj V)).stalk t'' ⧸
        Submodule.span ℚ (pathRel ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) c'').obj V) t'')) := by
  subst hc
  rw [finrank_pathRel_pullback, finrank_pathRel_pullback, pushRel_comp V c i t'' hL hloop]
  rfl

end Abstract

section Topology

/-- Loop lifting along `i` transfers along a factorisation `j = i ∘ k`. -/
private lemma loop_lift_of_comp {X₃ X₂ X : Type*} [TopologicalSpace X₃] [TopologicalSpace X₂]
    [TopologicalSpace X] (k : C(X₃, X₂)) (i : C(X₂, X)) (j : C(X₃, X))
    (hj : ∀ y, i (k y) = j y) (u : X₃)
    (H : ∀ γ : Path (j u) (j u), ∃ δ : Path u u, γ.Homotopic (δ.map j.continuous)) :
    ∀ γ : Path (i (k u)) (i (k u)), ∃ γ'' : Path (k u) (k u),
      γ.Homotopic (γ''.map i.continuous) := by
  intro γ
  obtain ⟨δ, hδ⟩ := H (γ.cast (hj u).symm (hj u).symm)
  refine ⟨δ.map k.continuous, ?_⟩
  have h := hδ.pathCast (hj u) (hj u)
  have e1 : (γ.cast (hj u).symm (hj u).symm).cast (hj u) (hj u) = γ := by ext; rfl
  have e2 : (δ.map j.continuous).cast (hj u) (hj u) = (δ.map k.continuous).map i.continuous := by
    ext x
    exact (hj (δ x)).symm
  rwa [e1, e2] at h

/-- Surjectivity on fundamental groups gives loop lifting up to homotopy. -/
private lemma loop_lift_of_surjective {X₂ X : Type*} [TopologicalSpace X₂] [TopologicalSpace X]
    (i : C(X₂, X)) (u : X₂) (hi : Function.Surjective (FundamentalGroup.map i u)) :
    ∀ γ : Path (i u) (i u), ∃ γ'' : Path u u, γ.Homotopic (γ''.map i.continuous) := by
  intro γ
  obtain ⟨g, hg⟩ := hi (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
  obtain ⟨γ'', hγ''⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  refine ⟨γ'', ?_⟩
  have : FundamentalGroup.map i u (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ'')) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (γ''.map i.continuous)) := rfl
  have h2 : FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ'') = g :=
    congrArg FundamentalGroup.fromPath hγ''
  rw [h2, hg] at this
  exact Path.Homotopic.Quotient.eq.1 (congrArg CategoryTheory.End.asHom this)

end Topology

section Geometry

/-- The complex realization of an integral scheme of finite type over `ℂ` is connected. -/
theorem connectedSpace_analyticSpace {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsIntegral X] [LocallyOfFiniteType sX] [QuasiCompact sX] :
    ConnectedSpace (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  haveI : QuasiCompact (X ↘ Spec (.of ℂ)) := ‹QuasiCompact sX›
  have hconn : IsConnected (MMP.UnderlyingSpace.regularPart ℂ X) := by
    simpa using MMP.UnderlyingSpace.isConnected_regularPart_diff (X := X)
      isClosed_empty (Set.empty_ne_univ (α := X))
  have huniv : IsConnected (Set.univ : Set (MMP.UnderlyingSpace ℂ X)) := by
    rw [← MMP.UnderlyingSpace.dense_regularPart.closure_eq]
    exact hconn.closure
  haveI : ConnectedSpace (MMP.UnderlyingSpace ℂ X) :=
    connectedSpace_iff_univ.mpr huniv
  exact (homeomorphUnderlyingSpace (X := X)).symm.surjective.connectedSpace
    (homeomorphUnderlyingSpace (X := X)).symm.continuous

/-- The complex realization of a scheme locally of finite type over `ℂ` is locally path
connected. -/
theorem locallyPathConnectedSpace_analyticSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] :
    LocallyPathConnectedSpace (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  have hb := MMP.UnderlyingSpace.hasOpenContractibleBasis X
  haveI : LocallyPathConnectedSpace (MMP.UnderlyingSpace ℂ X) :=
    LocallyPathConnectedSpace.of_bases hb fun x V hV => by
      change IsPathConnected V
      haveI : ContractibleSpace V := hV.2.2
      exact isPathConnected_iff_pathConnectedSpace.2 inferInstance
  exact (homeomorphUnderlyingSpace (X := X)).isOpenEmbedding.locallyPathConnectedSpace

/-- A complex variety has a complex point. -/
private lemma nonempty_complexPoints {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [AlgebraicGeometry.IsVariety ℂ sX] : Nonempty (ComplexPoints sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety ℂ sX›.toIsIntegral
  have : CompactSpace X :=
    ⟨QuasiCompact.isCompact_preimage (f := sX) Set.univ isOpen_univ isCompact_univ⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton (X := X) isClosed_univ Set.univ_nonempty
  have : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := show LocallyOfFiniteType sX from inferInstance
  exact ⟨(ComplexPoints.homeomorphUnderlyingSpace (X := X)).symm
    ((MMP.UnderlyingSpace.equivClosedPoints X).symm ⟨x, hx⟩)⟩

private lemma analyticMap_congr {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} {g g' : X ⟶ Y} (h : g = g') (hg : g ≫ sY = sX)
    (hg' : g' ≫ sY = sX) : analyticMap g hg = analyticMap g' hg' := by
  subst h
  rfl

variable {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}

/-- The curve `T` with its reduced structure is irreducible, Noetherian and of dimension one. -/
private lemma curveScheme_facts (hY : MMP.Mori.IsVariety ℂ sY)
    (hT : topologicalKrullDim (T : Set Y) = 1) :
    IrreducibleSpace (curveScheme T) ∧ topologicalKrullDim (curveScheme T) = 1 ∧
      IsNoetherian (curveScheme T) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  have hrange : Set.range (curveι T) = (T : Set Y) := by
    simp [Scheme.IdealSheafData.range_subschemeι]
  let e : curveScheme T ≃ₜ (T : Set Y) :=
    (curveι T).isClosedEmbedding.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  haveI : IrreducibleSpace (T : Set Y) := Subtype.irreducibleSpace T.isIrreducible
  haveI : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  haveI : CompactSpace (curveScheme T) :=
    QuasiCompact.compactSpace_of_compactSpace (curveι T ≫ sY)
  exact ⟨e.symm.surjective.irreducibleSpace e.symm.continuous,
    (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans hT, ⟨⟩⟩

/-- A local-system open is a smooth curve over `ℂ` with connected, locally path connected
complex realization. -/
private lemma isLocalSystemOpen_facts (hY : MMP.Mori.IsVariety ℂ sY)
    (hT : topologicalKrullDim (T : Set Y) = 1) {W : (curveScheme T).Opens}
    (hW : IsLocalSystemOpen sY W) :
    AlgebraicGeometry.IsVariety ℂ (W.ι ≫ curveι T ≫ sY) ∧
      SmoothOfRelativeDimension 1 (W.ι ≫ curveι T ≫ sY) ∧
      ConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) ∧
      LocallyPathConnectedSpace (analyticSpace (W.ι ≫ curveι T ≫ sY)) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  obtain ⟨hirr, hdim, hnoeth⟩ := curveScheme_facts hY hT
  haveI : Smooth (W.ι ≫ curveι T ≫ sY) := hW.smooth
  haveI : ConnectedSpace W := hW.connectedSpace
  haveI : IsIntegral W :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (W.ι ≫ curveι T ≫ sY)
  haveI hV : AlgebraicGeometry.IsVariety ℂ (W.ι ≫ curveι T ≫ sY) :=
    { toIsIntegral := inferInstance, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  obtain ⟨w⟩ := hW.connectedSpace.toNonempty
  have hdimW : topologicalKrullDim W = 1 :=
    (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ (curveScheme T) (curveι T ≫ sY)
      (W : Set (curveScheme T)) W.isOpen ⟨w.1, w.2⟩).symm.trans hdim
  exact ⟨hV, MMP.Intersection.smoothOfRelativeDimension_of_isVariety _ 1 hdimW,
    connectedSpace_analyticSpace _, locallyPathConnectedSpace_analyticSpace _⟩

/-- On a local-system open `W`, the rank `b_T` is the dimension of the monodromy coinvariants
of the fibre of `𝒱_T` at any point. -/
private lemma curveLocalSystemRank_eq_finrank_coinvariants (hY : MMP.Mori.IsVariety ℂ sY)
    (hT : topologicalKrullDim (T : Set Y) = 1) {W : (curveScheme T).Opens}
    (hW : IsLocalSystemOpen sY W) (t : analyticSpace (W.ι ≫ curveι T ≫ sY)) :
    curveLocalSystemRank sY W = Module.finrank ℚ
      (((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY W)).stalk t ⧸
        Submodule.span ℚ (pathRel (curveLocalSystem sY W) t)) := by
  obtain ⟨hV, hsm, hconn, -⟩ := isLocalSystemOpen_facts hY hT hW
  obtain ⟨e⟩ := nonempty_compactSupportCohomology_two_linearEquiv_coinvariants
    (W.ι ≫ curveι T ≫ sY) (curveLocalSystem sY W) hW.isLocalSystem t
  rw [← pathRel_eq]
  exact LinearEquiv.finrank_eq e

/-- If `U'` is a dense open of a scheme and `U` an irreducible open, then `U ∩ U'` is a nonempty
dense open of `U`. -/
private lemma nonempty_dense_preimage_ι {X : Scheme.{0}} {U U' : X.Opens}
    [IrreducibleSpace U.toScheme] (hU' : Dense (U' : Set X)) :
    Nonempty (U.ι ⁻¹ᵁ U' : U.toScheme.Opens) ∧
      Dense ((U.ι ⁻¹ᵁ U' : U.toScheme.Opens) : Set U.toScheme) := by
  obtain ⟨x, hxU, hxU'⟩ := hU'.inter_open_nonempty (U : Set X) U.isOpen
    (Set.nonempty_coe_sort.1 (IrreducibleSpace.toNonempty (X := U.toScheme)))
  have h : ((U.ι ⁻¹ᵁ U' : U.toScheme.Opens) : Set U.toScheme).Nonempty := ⟨⟨x, hxU⟩, hxU'⟩
  exact ⟨h.to_subtype, (U.ι ⁻¹ᵁ U').isOpen.dense h⟩

/-- For opens `U`, `U'` of a scheme, the inclusion of `U' ∩ U` into `U` factors through
`U ∩ U'`, compatibly with the inclusions into the ambient scheme. -/
private lemma exists_lift_preimage_ι {X : Scheme.{0}} (U U' : X.Opens) :
    ∃ ψ : ((U'.ι ⁻¹ᵁ U : U'.toScheme.Opens) : Scheme) ⟶ (U.ι ⁻¹ᵁ U' : U.toScheme.Opens),
      ψ ≫ U.ι.resLE U' (U.ι ⁻¹ᵁ U') le_rfl = (U'.ι ⁻¹ᵁ U).ι ∧
      ψ ≫ (U.ι ⁻¹ᵁ U').ι ≫ U.ι = (U'.ι ⁻¹ᵁ U).ι ≫ U'.ι := by
  have hχ : U'.ι.resLE U (U'.ι ⁻¹ᵁ U) le_rfl ≫ U.ι = (U'.ι ⁻¹ᵁ U).ι ≫ U'.ι :=
    Scheme.Hom.resLE_comp_ι _ _
  have hrange : Set.range (U'.ι.resLE U (U'.ι ⁻¹ᵁ U) le_rfl) ⊆ Set.range (U.ι ⁻¹ᵁ U').ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change U.ι (U'.ι.resLE U (U'.ι ⁻¹ᵁ U) le_rfl y) ∈ U'
    rw [← Scheme.Hom.comp_apply, hχ, Scheme.Hom.comp_apply]
    have hmem := Set.mem_range_self (f := U'.ι) ((U'.ι ⁻¹ᵁ U).ι y)
    rwa [Scheme.Opens.range_ι] at hmem
  have hψ : IsOpenImmersion.lift _ _ hrange ≫ (U.ι ⁻¹ᵁ U').ι = _ :=
    IsOpenImmersion.lift_fac _ _ hrange
  refine ⟨IsOpenImmersion.lift _ _ hrange, ?_, by rw [← Category.assoc, hψ, hχ]⟩
  rw [← cancel_mono U'.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, hψ, hχ]

/-- **The rank does not depend on the local-system open.** Both coinvariant spaces are computed
at a point of `T° ∩ T°'`, where they agree with the coinvariants on the intersection. -/
private lemma curveLocalSystemRank_eq_of_isLocalSystemOpen (hY : MMP.Mori.IsVariety ℂ sY)
    (hT : topologicalKrullDim (T : Set Y) = 1) {To To' : (curveScheme T).Opens}
    (hTo : IsLocalSystemOpen sY To) (hTo' : IsLocalSystemOpen sY To') :
    curveLocalSystemRank sY To = curveLocalSystemRank sY To' := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hY
  obtain ⟨hV, -, -, hlpc⟩ := isLocalSystemOpen_facts hY hT hTo
  obtain ⟨hV', -, -, hlpc'⟩ := isLocalSystemOpen_facts hY hT hTo'
  obtain ⟨-, -, hnoeth⟩ := curveScheme_facts hY hT
  set sT := To.ι ≫ curveι T ≫ sY
  set sT' := To'.ι ≫ curveι T ≫ sY
  haveI : Smooth sT := hTo.smooth
  haveI : Smooth sT' := hTo'.smooth
  haveI : ConnectedSpace To := hTo.connectedSpace
  haveI : ConnectedSpace To' := hTo'.connectedSpace
  haveI : IsIntegral To := hV.toIsIntegral
  haveI : IsIntegral To' := hV'.toIsIntegral
  let U₁ : (To : Scheme).Opens := To.ι ⁻¹ᵁ To'
  let U₂ : (To' : Scheme).Opens := To'.ι ⁻¹ᵁ To
  obtain ⟨hn₁, hU₁d⟩ := nonempty_dense_preimage_ι (U := To) hTo'.dense
  obtain ⟨hn₂, hU₂d⟩ := nonempty_dense_preimage_ι (U := To') hTo.dense
  let φ : (U₁ : Scheme) ⟶ (To' : Scheme) := To.ι.resLE To' U₁ le_rfl
  have hφ : φ ≫ To'.ι = U₁.ι ≫ To.ι := Scheme.Hom.resLE_comp_ι _ _
  obtain ⟨ψ, hψφ, hψ⟩ := exists_lift_preimage_ι To To'
  have hφs : φ ≫ sT' = U₁.ι ≫ sT := (reassoc_of% hφ) (curveι T ≫ sY)
  have hψs : ψ ≫ U₁.ι ≫ sT = U₂.ι ≫ sT' := (reassoc_of% hψ) (curveι T ≫ sY)
  haveI hV₂ : AlgebraicGeometry.IsVariety ℂ (U₂.ι ≫ sT') :=
    { toIsIntegral := isIntegral_of_isOpenImmersion U₂.ι, toIsSeparated := inferInstance,
      toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance }
  obtain ⟨u₂⟩ := nonempty_complexPoints (U₂.ι ≫ sT')
  let i₁ := analyticMap U₁.ι (sY := sT) rfl
  let i₂ := analyticMap φ hφs
  let k := analyticMap ψ hψs
  let j := analyticMap U₂.ι (sY := sT') rfl
  have hj : ∀ y, i₂ (k y) = j y := fun y => by
    ext1
    change (y.hom ≫ ψ) ≫ φ = y.hom ≫ U₂.ι
    rw [Category.assoc, hψφ]
  have hloop₁ := loop_lift_of_surjective i₁.hom (k u₂)
    (surjective_fundamentalGroupMap_realize_ι_of_dense sT hV U₁ hU₁d (k u₂))
  have hloop₂ := loop_lift_of_comp k.hom i₂.hom j.hom hj u₂
    (loop_lift_of_surjective j.hom u₂
      (surjective_fundamentalGroupMap_realize_ι_of_dense sT' hV' U₂ hU₂d u₂))
  let V := regularHigherDirectImage sY 2
  let c := curveOpenInclusion sY To
  let c' := curveOpenInclusion sY To'
  have hc' : i₂ ≫ c' = i₁ ≫ c := by
    simp only [i₁, i₂, c, c', curveOpenInclusion, analyticMap_comp]
    exact analyticMap_congr (by rw [← Category.assoc, hφ, Category.assoc]) _ _
  calc curveLocalSystemRank sY To
      = _ := curveLocalSystemRank_eq_finrank_coinvariants hY hT hTo (i₁ (k u₂))
    _ = _ := finrank_coinvariants_eq V c i₁ (i₁ ≫ c) rfl (k u₂) hTo.isLocalSystem hloop₁
    _ = _ := (finrank_coinvariants_eq V c' i₂ (i₁ ≫ c) hc' (k u₂) hTo'.isLocalSystem hloop₂).symm
    _ = curveLocalSystemRank sY To' :=
      (curveLocalSystemRank_eq_finrank_coinvariants hY hT hTo' (i₂ (k u₂))).symm

end Geometry

/-- **The rank of the punctured local system does not depend on the open.** Let `Y` be a normal
complex fourfold and `T ⊆ Sing Y` an irreducible curve. For any two local-system opens `T°`,
`T°'` of `T`, the ranks `b_T = dim_ℚ H²_c(T°, 𝒱_T)` agree, and for every `t ∈ T°(ℂ)` the rank is
the dimension of the quotient of the fibre `𝒱_{T,t}` by the span of all `w - v`, where `v` is
the parallel transport of `w` along a loop at `t`: the monodromy coinvariants of `π₁(T°, t)`. -/
@[mmp "lem_oai4_c2_curve_rank_shrinking"]
public theorem IsLocalSystemOpen.curveLocalSystemRank_eq
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} (hY : MMP.Mori.IsVariety ℂ sY) [IsNormal Y]
    (hdim : topologicalKrullDim Y = 4) {T : IrreducibleCloseds Y}
    (hT : topologicalKrullDim (T : Set Y) = 1) (hTsing : (T : Set Y) ⊆ singularLocus sY)
    {To To' : (curveScheme T).Opens} (hTo : IsLocalSystemOpen sY To)
    (hTo' : IsLocalSystemOpen sY To') :
    curveLocalSystemRank sY To = curveLocalSystemRank sY To' ∧
      ∀ t : analyticSpace (To.ι ≫ curveι T ≫ sY),
        curveLocalSystemRank sY To = Module.finrank ℚ
          (((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY To)).stalk t ⧸ Submodule.span ℚ
            {u | ∃ (γ : Path t t)
                (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
                  (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                    (curveLocalSystem sY To)).obj.obj (op ⊤)))
                (w v : ((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY To)).stalk t),
                (stalkToPullbackStalk
                    (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
                    (curveLocalSystem sY To) 0).hom
                  ((((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY To)).stalkCongr
                    (.of_eq γ.source.symm)).hom.hom w) =
                  (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
                    (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                      (curveLocalSystem sY To))).germ ⊤ 0 trivial).hom s ∧
                (stalkToPullbackStalk
                    (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
                    (curveLocalSystem sY To) 1).hom
                  ((((TopCat.Sheaf.forget _ _).obj (curveLocalSystem sY To)).stalkCongr
                    (.of_eq γ.target.symm)).hom.hom v) =
                  (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
                    (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
                      (curveLocalSystem sY To))).germ ⊤ 1 trivial).hom s ∧
                u = w - v}) := by
  refine ⟨curveLocalSystemRank_eq_of_isLocalSystemOpen hY hT hTo hTo', fun t => ?_⟩
  rw [pathRel_eq]
  exact curveLocalSystemRank_eq_finrank_coinvariants hY hT hTo t

end MMP.Fourfold
