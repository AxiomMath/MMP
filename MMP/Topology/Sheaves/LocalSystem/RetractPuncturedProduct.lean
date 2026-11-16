module
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem

/-!
# Local systems on curves: direct summands and punctured products

Two local facts about local systems of finite-dimensional `ℚ`-vector spaces.

*Direct summands.* On a locally connected space, a retract of a local system is again a local
system: near every point the local system is constant on a connected open set, on which the
constant sheaf functor is fully faithful (a global section of a constant sheaf on a connected
space is constant); the idempotent `ρ ≫ ι` is then a constant idempotent `e₀` of the fibre, and
the retract is the constant sheaf on the image of `e₀`.

*Punctured products.* Let `V` be a metrizable space and `x ∈ V` a point such that every point of
`V ∖ {x}` has arbitrarily small contractible open neighbourhoods, and let `Δ = B(c, r) ⊆ ℂ` be an
open disk. Write `j : (V ∖ {x}) × Δ ⟶ V × Δ` for the inclusion and `i : Δ ⟶ V × Δ`,
`s ↦ (x, s)`, for the inclusion of `A = {x} × Δ`. The *link cohomology* of `x` is
`L^q_x = colim_{V' ∋ x} H^q(V' ∖ {x}; ℚ)`, the colimit over the open neighbourhoods of `x`
under restriction. Pulling classes back along the first projection
`(V' ∖ {x}) × Δ ⟶ V' ∖ {x}` identifies the stalk of `R^q j_* ℚ` at every point `(x, s)` of `A`
with `L^q_x`, and the restriction `i⁻¹ R^q j_* ℚ` with the constant sheaf `(L^q_x)_A`; in
particular `i⁻¹ R^q j_* ℚ` is a local system on `Δ` when `L^q_x` is finite-dimensional.
The proof: pullback along `(V' ∖ {x}) × D ⟶ V' ∖ {x}` is an isomorphism for every convex open
`D ⊆ Δ` by homotopy invariance, and the boxes `V' × D` are cofinal among the neighbourhoods of
`(x, s)`; the comparison map from the constant sheaf is the adjoint of the map
`L ⟶ Γ(Δ, i⁻¹ R^q j_* ℚ)` sending the germ of `c` to the restriction of `pr₁^* c`, and it is an
isomorphism on stalks because the stalks of an inverse image are the stalks of the sheaf.

## Main results

* `MMP.Fourfold.IsLocalSystem.of_retract`: a retract (in the category of sheaves of
  `ℚ`-vector spaces) of a local system on a locally connected space is a local system.
* `MMP.Fourfold.exists_iso_constantSheaf_pullback_higherDirectImage_prod_ball`: the stalk
  isomorphisms `L^q_x ≅ (R^q j_* ℚ)_{(x,s)}` and the isomorphism
  `(L^q_x)_Δ ≅ i⁻¹ R^q j_* ℚ`, both characterised on germs by pullback along the first
  projection, and the local system property when `L^q_x` is finite-dimensional.

## Implementation notes

* `R^q j_* ℚ` is `MMP.Fourfold.higherDirectImage j q`, the sheaf associated to
  `W ↦ H^q(j⁻¹(W); ℚ)`, and `H^q(-; ℚ)` is `MMP.Fourfold.rationalCohomology`. For an open
  `V' ⊆ V` the space `V' ∖ {x}` is `j'⁻¹(V')` for the inclusion `j' : V ∖ {x} ⟶ V`, so
  `L^q_x` is the stalk at `x` of the presheaf `MMP.Fourfold.directImagePresheaf j' q`, which is
  by definition the colimit over the open neighbourhoods of `x`.
* The neighbourhoods `V' × Δ = pr₁⁻¹(V')` of `A` carry the comparison: a class
  `c ∈ H^q(V' ∖ {x}; ℚ)` is pulled back to `j⁻¹(V' × Δ) = (V' ∖ {x}) × Δ`. The two
  isomorphisms are pinned by their values on such germs: the stalk isomorphism sends the germ
  of `c` at `x` to the germ of `pr₁^* c` at `(x, s)`, and the sheaf isomorphism sends the
  constant section `c` to the section whose germ at `s` is the image of that germ under
  `MMP.Fourfold.stalkToPullbackStalk`.
* Under the standing hypotheses every open subset of `(V ∖ {x}) × Δ` is metrizable with a
  basis of contractible open sets, so its singular cohomology is the cohomology of the
  constant sheaf `ℚ`; in particular `R^q j_* ℚ` and `L^q_x` here are the derived direct image
  and the colimit of sheaf cohomology groups.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
* [B. Iversen, *Cohomology of sheaves*], III.1 and IV.1.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits

namespace MMP.Fourfold

section ConstantSheaf

variable {X Y Z : TopCat.{0}}

local notation "J" X => Opens.grothendieckTopology X

/-- On a nonempty open, the map from a constant presheaf to its sheafification is injective. -/
private theorem toSheafify_const_app_injective (E : ModuleCat.{0} ℚ) {W : Opens X}
    (hW : (W : Set X).Nonempty) :
    Function.Injective ((toSheafify (J X) ((Functor.const (Opens X)ᵒᵖ).obj E)).app (op W)) := by
  intro a b hab
  obtain ⟨x, hx⟩ := hW
  obtain ⟨V, f, hf, -⟩ := Presheaf.equalizerSieve_mem (J X)
    (toSheafify (J X) ((Functor.const (Opens X)ᵒᵖ).obj E)) a b hab x hx
  simpa using hf

/-- Restriction of the image of a constant section is the image of the same constant. -/
private theorem toSheafify_const_app_restrict (E : ModuleCat.{0} ℚ) {V U : Opens X} (i : V ⟶ U)
    (a : E) :
    (sheafify (J X) ((Functor.const (Opens X)ᵒᵖ).obj E)).map i.op
        ((toSheafify (J X) ((Functor.const (Opens X)ᵒᵖ).obj E)).app (op U) a) =
      (toSheafify (J X) ((Functor.const (Opens X)ᵒᵖ).obj E)).app (op V) a := by
  simpa using (ConcreteCategory.congr_hom
    ((toSheafify (J X) ((Functor.const (Opens X)ᵒᵖ).obj E)).naturality i.op) a).symm

/-- On a connected space, every global section of a constant sheaf is constant. -/
private theorem toSheafify_const_app_top_surjective [ConnectedSpace X] (E : ModuleCat.{0} ℚ) :
    Function.Surjective
      ((toSheafify (J X) ((Functor.const (Opens X)ᵒᵖ).obj E)).app (op ⊤)) := by
  set P := (Functor.const (Opens X)ᵒᵖ).obj E
  set φ := toSheafify (J X) P
  intro s
  have hS := Presheaf.imageSieve_mem (J X) φ s
  choose V f hV hxV using fun x : X => hS x trivial
  choose e he using hV
  have key : ∀ x, ∀ y ∈ V x, e y = e x := by
    intro x y hy
    apply toSheafify_const_app_injective E (W := V x ⊓ V y) ⟨y, hy, hxV y⟩
    have h1 := toSheafify_const_app_restrict E (homOfLE (inf_le_left : V x ⊓ V y ≤ V x)) (e x)
    have h2 := toSheafify_const_app_restrict E (homOfLE (inf_le_right : V x ⊓ V y ≤ V y)) (e y)
    rw [← h1, ← h2, he, he, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  let g : X → E := e
  have hloc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    exact ⟨V x, (V x).isOpen, hxV x, fun y hy => key x y hy⟩
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  refine ⟨g x₀, ?_⟩
  let F : TopCat.Sheaf (ModuleCat.{0} ℚ) X := (presheafToSheaf (J X) _).obj P
  refine (TopCat.Sheaf.eq_of_locally_eq' F V ⊤ f
    (fun x _ => Opens.mem_iSup.2 ⟨x, hxV x⟩) _ _ fun x => ?_)
  change (sheafify (J X) P).map (f x).op (φ.app (op ⊤) (g x₀)) =
    (sheafify (J X) P).map (f x).op s
  rw [toSheafify_const_app_restrict, ← he x, hloc.apply_eq_of_preconnectedSpace x₀ x]

/-- The unit of the constant sheaf adjunction is the sheafification map on global sections. -/
private theorem constantSheafAdj_unit_app (E : ModuleCat.{0} ℚ) :
    (constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop).unit.app E =
      (toSheafify (J X) ((Functor.const (Opens X)ᵒᵖ).obj E)).app (op ⊤) := by
  simp only [Functor.id_obj, Functor.comp_obj, Functor.flip_obj_obj, ObjectProperty.ι_obj,
    constantSheafAdj, Adjunction.comp_unit_app, evaluation_obj_obj, Functor.const_obj_obj,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app, evaluation_obj_map,
    Category.id_comp]
  rfl

/-- On a connected space, the constant sheaf functor is fully faithful. -/
private def fullyFaithfulConstantSheaf [ConnectedSpace X] :
    (constantSheaf (J X) (ModuleCat.{0} ℚ)).FullyFaithful :=
  haveI : ∀ E, IsIso ((constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop).unit.app E) :=
    fun E => by
      obtain ⟨x⟩ := (inferInstance : Nonempty X)
      rw [constantSheafAdj_unit_app]
      exact (ConcreteCategory.isIso_iff_bijective _).2
        ⟨toSheafify_const_app_injective E ⟨x, trivial⟩, toSheafify_const_app_top_surjective E⟩
  haveI := NatIso.isIso_of_isIso_app
    (constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop).unit
  (constantSheafAdj (J X) (ModuleCat.{0} ℚ) isTerminalTop).fullyFaithfulLOfIsIsoUnit

/-- On a connected space, a retract of the constant sheaf of a finite-dimensional space is the
constant sheaf of a finite-dimensional space. -/
private theorem exists_iso_constantSheaf_of_retract [ConnectedSpace X]
    {A : Sheaf (J X) (ModuleCat.{0} ℚ)} {E : ModuleCat.{0} ℚ} [FiniteDimensional ℚ E]
    (h : Retract A ((constantSheaf (J X) (ModuleCat.{0} ℚ)).obj E)) :
    ∃ E' : ModuleCat.{0} ℚ, FiniteDimensional ℚ E' ∧
      Nonempty (A ≅ (constantSheaf (J X) (ModuleCat.{0} ℚ)).obj E') := by
  set L := constantSheaf (J X) (ModuleCat.{0} ℚ)
  let hL : L.FullyFaithful := fullyFaithfulConstantSheaf
  set f := hL.preimage (h.r ≫ h.i)
  have hf : L.map f = h.r ≫ h.i := hL.map_preimage _
  have hff : f ≫ f = f := hL.map_injective (by
    rw [L.map_comp, hf, Category.assoc, h.retract_assoc])
  have hff' : ∀ v, f.hom (f.hom v) = f.hom v := fun v =>
    congrArg (fun g : E ⟶ E => g.hom v) hff
  let E' : ModuleCat.{0} ℚ := ModuleCat.of ℚ (LinearMap.range f.hom)
  let i' : E' ⟶ E := ModuleCat.ofHom (LinearMap.range f.hom).subtype
  let r' : E ⟶ E' := ModuleCat.ofHom f.hom.rangeRestrict
  have hri : r' ≫ i' = f := by
    ext v
    rfl
  have hir' : ∀ v : E', r'.hom (i'.hom v) = v := fun ⟨_, w, rfl⟩ => Subtype.ext (hff' w)
  have hir : i' ≫ r' = 𝟙 E' := by
    ext v
    exact congrArg Subtype.val (hir' v)
  refine ⟨E', inferInstance, ⟨
    { hom := h.i ≫ L.map r'
      inv := L.map i' ≫ h.r
      hom_inv_id := ?_
      inv_hom_id := ?_ }⟩⟩
  · rw [Category.assoc, ← L.map_comp_assoc, hri, hf, Category.assoc, h.retract_assoc,
      h.retract]
  · rw [Category.assoc, ← Category.assoc h.r, ← hf, ← L.map_comp, ← L.map_comp, ← L.map_id,
      ← hri, Category.assoc, reassoc_of% hir, hir]

/-- Global sections of a pushforward are global sections. -/
private def pushforwardTopIso (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        (sheafSections (J Y) (ModuleCat.{0} ℚ)).obj (op ⊤) ≅
      (sheafSections (J X) (ModuleCat.{0} ℚ)).obj (op ⊤) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The inverse image of a constant sheaf is constant. -/
private def pullbackConstIso (f : X ⟶ Y) :
    constantSheaf (J Y) (ModuleCat.{0} ℚ) ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ≅
      constantSheaf (J X) (ModuleCat.{0} ℚ) :=
  (((constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)).ofNatIsoRight
      (pushforwardTopIso f)).leftAdjointUniq (constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop)

/-- Direct images compose. -/
private def pushforwardCompIso (g : X ⟶ Y) (f : Y ⟶ Z) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ≅
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (g ≫ f) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Inverse images compose. -/
private def pullbackCompIso (g : X ⟶ Y) (f : Y ⟶ Z) :
    TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (g ≫ f) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g)).ofNatIsoRight
      (pushforwardCompIso g f)).leftAdjointUniq
        (TopCat.Sheaf.pullbackPushforwardAdjunction _ (g ≫ f))

end ConstantSheaf

/-- On a locally connected space `W`, a retract `𝒜` of a local system `ℒ` of
finite-dimensional `ℚ`-vector spaces (morphisms `ι : 𝒜 ⟶ ℒ`, `ρ : ℒ ⟶ 𝒜` with `ι ≫ ρ = 𝟙 𝒜`)
is a local system. -/
@[mmp "lem_mmp_curvels_direct_summand"]
public theorem IsLocalSystem.of_retract {W : TopCat.{0}} [LocallyConnectedSpace W]
    {𝒜 ℒ : TopCat.Sheaf (ModuleCat.{0} ℚ) W} (h : Retract 𝒜 ℒ) (hL : IsLocalSystem ℒ) :
    IsLocalSystem 𝒜 := by
  intro x
  obtain ⟨V, hxV, E, hE, ⟨e⟩⟩ := hL x
  let U : Opens W := ⟨connectedComponentIn V x, V.isOpen.connectedComponentIn⟩
  have : ConnectedSpace ((Opens.toTopCat W).obj U) :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponentIn_iff.mpr hxV)
  let g : (Opens.toTopCat W).obj U ⟶ (Opens.toTopCat W).obj V :=
    (Opens.toTopCat W).map (homOfLE (connectedComponentIn_subset _ _))
  let P := TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) U.inclusion'
  -- `U.inclusion' = g ≫ V.inclusion'` holds by `rfl`, so `ℒ|_U` is the pullback of `ℒ|_V ≅ E_V`.
  let e' : P.obj ℒ ≅ (constantSheaf (Opens.grothendieckTopology _) (ModuleCat.{0} ℚ)).obj E :=
    (pullbackCompIso g V.inclusion').symm.app ℒ ≪≫
      (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).mapIso e ≪≫ (pullbackConstIso g).app E
  exact ⟨U, mem_connectedComponentIn hxV,
    exists_iso_constantSheaf_of_retract ((h.map P).trans (Retract.ofIso e'))⟩

/-- A map with a section `σ` such that `σ ∘ p` is homotopic to the identity induces an
isomorphism on rational cohomology. -/
private lemma isIso_rationalCohomologyMap_of_homotopy {Z Y : TopCat.{0}} (p : Z ⟶ Y)
    (σ : Y ⟶ Z) (h₁ : σ ≫ p = 𝟙 Y) (H : TopCat.Homotopy (p ≫ σ) (𝟙 Z)) (q : ℕ) :
    IsIso (rationalCohomologyMap p q) := by
  refine ⟨⟨rationalCohomologyMap σ q, ?_, ?_⟩⟩
  · rw [← rationalCohomologyMap_comp, h₁, rationalCohomologyMap_id]
  · rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_id]
    unfold rationalCohomologyMap
    exact MMP.relativeSingularCohomology.map_eq_of_homotopy ℚ H
      (fun _ hy _ ↦ absurd (Set.mem_univ _) hy) _ _ _

/-- `stalkPushforward` is natural in the presheaf. -/
private lemma stalkPushforward_naturality {X Y : TopCat.{0}} (f : X ⟶ Y)
    {F G : TopCat.Presheaf (ModuleCat.{0} ℚ) X} (g : F ⟶ G) (x : X) :
    TopCat.Presheaf.stalkPushforward _ f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map g =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map g) ≫
        TopCat.Presheaf.stalkPushforward _ f G x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
  rfl

/-- `stalkPushforward` absorbs a morphism into the pushforward on either side. -/
private lemma stalkPushforward_comp_naturality {X Y : TopCat.{0}} {f : X ⟶ Y}
    {F' : TopCat.Presheaf (ModuleCat.{0} ℚ) Y} {G G' : TopCat.Presheaf (ModuleCat.{0} ℚ) X}
    (u : F' ⟶ (TopCat.Presheaf.pushforward _ f).obj G) (v : G ⟶ G') (x : X) :
    ((TopCat.Presheaf.stalkFunctor _ (f x)).map u ≫ TopCat.Presheaf.stalkPushforward _ f G x) ≫
        (TopCat.Presheaf.stalkFunctor _ x).map v =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map (u ≫ (TopCat.Presheaf.pushforward _ f).map v) ≫
        TopCat.Presheaf.stalkPushforward _ f G' x := by
  refine (Category.assoc _ _ _).trans ?_
  erw [stalkPushforward_naturality f v x, Functor.map_comp, Category.assoc]
  rfl

/-- The canonical map `F_{f(x)} ⟶ (f⁻¹F)_x` is an isomorphism. -/
private lemma isIso_stalkToPullbackStalk {X Y : TopCat.{0}} (f : X ⟶ Y)
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) (x : X) : IsIso (stalkToPullbackStalk f F x) := by
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
    simp only [Adjunction.comp_unit_app, Iso.refl_hom, NatTrans.id_app]
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
    refine (stalkPushforward_comp_naturality _ _ x).trans
      (Eq.trans ?_ (stalkPushforward_comp_naturality _ _ x).symm)
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

/-- The image in `(i⁻¹R)_s` of a germ of `F` mapped to `R` is the germ of its pulled-back
section. -/
private lemma germ_comp_stalkToPullbackStalk {Y Z : TopCat.{0}} (i : Z ⟶ Y)
    (F : TopCat.Presheaf (ModuleCat.{0} ℚ) Y) (R : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)
    (t : F ⟶ (TopCat.Sheaf.forget _ Y).obj R) (U : Opens Y) (s : Z) (hs : i s ∈ U) :
    F.germ U (i s) hs ≫ (TopCat.Presheaf.stalkFunctor _ (i s)).map t ≫
        stalkToPullbackStalk i R s =
      t.app (op U) ≫ ((TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) i).unit.app R)).app (op U) ≫
        ((TopCat.Sheaf.forget _ Z).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj R)).germ
          ((Opens.map i).obj U) s hs := by
  unfold stalkToPullbackStalk
  erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ_assoc,
    TopCat.Presheaf.stalkPushforward_germ]
  rfl

/-- A morphism `f` of `ℚ`-modules is an isomorphism once `u ≫ f` is, for `u` surjective. -/
private lemma isIso_of_isIso_comp_of_surjective {A B C : ModuleCat.{0} ℚ} (u : A ⟶ B)
    (f : B ⟶ C) (hu : Function.Surjective u) (_ : IsIso (u ≫ f)) : IsIso f := by
  have h : Function.Bijective (f ∘ u) := ConcreteCategory.bijective_of_isIso (u ≫ f)
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨h.1.of_comp_right hu, h.2.of_comp⟩

/-- Every germ of a constant sheaf is the germ of a constant global section. -/
private lemma surjective_constantSheaf_germ {X : TopCat.{0}} (E : ModuleCat.{0} ℚ) (s : X) :
    Function.Surjective ((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)
      isTerminalTop).unit.app E ≫
        ((TopCat.Sheaf.forget _ X).obj ((constantSheaf _ _).obj E)).germ ⊤ s trivial) := by
  intro y
  let P0 : TopCat.Presheaf (ModuleCat.{0} ℚ) X := (Functor.const (Opens X)ᵒᵖ).obj E
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso s (ModuleCat.{0} ℚ) P0
  obtain ⟨z, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor _ s).map (toSheafify (Opens.grothendieckTopology X) P0))).2 y
  obtain ⟨U, hU, l, rfl⟩ := TopCat.Presheaf.exists_germ_eq P0 z
  refine ⟨l, ?_⟩
  have h0 := P0.germ_res (homOfLE le_top) s hU
  rw [Functor.const_obj_map] at h0
  have h0' : P0.germ U s hU = P0.germ ⊤ s trivial := (Category.id_comp _).symm.trans h0
  have h1 := TopCat.Presheaf.stalkFunctor_map_germ ⊤ s trivial
    (toSheafify (Opens.grothendieckTopology X) P0)
  rw [h0']
  refine (ConcreteCategory.congr_hom h1 l).symm.trans ?_
  exact ConcreteCategory.comp_apply _ _ _

/-- Boxes `O × E`, with `O ∋ x` open in `O₀` and `E ∋ s` convex open in `B(c, r)`, are cofinal
among the open neighbourhoods of `(x, s)` in `V × B(c, r)`. -/
public theorem exists_box_subset {V : Type*} [TopologicalSpace V] {c : ℂ} {r : ℝ} {x : V}
    {s : Metric.ball c r} {N : Set (V × Metric.ball c r)} (hN : IsOpen N) (hxs : (x, s) ∈ N)
    {O₀ : Opens V} (hO₀ : x ∈ O₀) :
    ∃ O : Opens V, x ∈ O ∧ O ≤ O₀ ∧ ∃ E : Set ℂ, IsOpen E ∧ Convex ℝ E ∧ (s : ℂ) ∈ E ∧
      E ⊆ Metric.ball c r ∧ {p : V × Metric.ball c r | p.1 ∈ O ∧ (p.2 : ℂ) ∈ E} ⊆ N := by
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 (hN.mem_nhds hxs)
  obtain ⟨u', hu'u, hu'o, hxu'⟩ := mem_nhds_iff.1 hu
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhds_iff.1 hv
  refine ⟨⟨u', hu'o⟩ ⊓ O₀, ⟨hxu', hO₀⟩, inf_le_right, Metric.ball (s : ℂ) ε ∩ Metric.ball c r,
    Metric.isOpen_ball.inter Metric.isOpen_ball, (convex_ball _ _).inter (convex_ball _ _),
    ⟨Metric.mem_ball_self hε, s.2⟩, Set.inter_subset_right, ?_⟩
  rintro p ⟨hp1, hp2⟩
  exact huv ⟨hu'u hp1.1, hεv hp2.1⟩

/-- **Punctured direct images along a product with a disk.** Let `V` be a metrizable space,
`x ∈ V` a point every other point of which has arbitrarily small contractible open
neighbourhoods, `Δ = B(c, r) ⊆ ℂ`, `j : (V ∖ {x}) × Δ ⟶ V × Δ` the inclusion and
`i : Δ ⟶ V × Δ`, `s ↦ (x, s)`. Let `L = colim_{V' ∋ x} H^q(V' ∖ {x}; ℚ)`, the stalk at `x` of
`V' ↦ H^q(V' ∖ {x}; ℚ)`. Then
* for every `s ∈ Δ` there is an isomorphism `L ≅ (R^q j_* ℚ)_{(x,s)}` sending the germ of a
  class `c ∈ H^q(V' ∖ {x}; ℚ)` to the germ of its pullback `pr₁^* c ∈ H^q((V' ∖ {x}) × Δ; ℚ)`;
* there is an isomorphism `L_Δ ≅ i⁻¹ R^q j_* ℚ` from the constant sheaf, sending the constant
  section with value the germ of `c` to the section of `i⁻¹ R^q j_* ℚ` whose germ at every `s`
  is the image of the germ of `pr₁^* c` at `(x, s)`;
* if `L` is finite-dimensional, `i⁻¹ R^q j_* ℚ` is a local system. -/
@[mmp "lem_mmp_curvels_punctured_product"]
public theorem exists_iso_constantSheaf_pullback_higherDirectImage_prod_ball
    (V : TopCat.{0}) [MetrizableSpace V] (x : V)
    (_hV : ∀ y : V, y ≠ x → ∀ U ∈ nhds y,
      ∃ W : Set V, IsOpen W ∧ y ∈ W ∧ W ⊆ U ∧ ContractibleSpace W)
    (c : ℂ) (r : ℝ) (q : ℕ) :
    let P := TopCat.of (V × Metric.ball c r)
    let j : TopCat.of (({x}ᶜ : Set V) × Metric.ball c r) ⟶ P :=
      TopCat.ofHom ⟨fun w ↦ (w.1.1, w.2), by fun_prop⟩
    let i : TopCat.of (Metric.ball c r) ⟶ P := TopCat.ofHom ⟨fun s ↦ (x, s), by fun_prop⟩
    let j' : TopCat.of ({x}ᶜ : Set V) ⟶ V := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let pr₁ : P ⟶ V := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
    let pr : ∀ V' : Opens V, preimageSpace j ((Opens.map pr₁).obj V') ⟶ preimageSpace j' V' :=
      fun V' ↦ TopCat.ofHom ⟨fun w ↦ ⟨w.1.1, w.2⟩, by fun_prop⟩
    let L := (directImagePresheaf j' q).stalk x
    let R := higherDirectImage j q
    (∀ s : Metric.ball c r, ∃ e : L ≅ ((TopCat.Sheaf.forget _ P).obj R).stalk (x, s),
      ∀ (V' : Opens V) (hx : x ∈ V'),
        (directImagePresheaf j' q).germ V' x hx ≫ e.hom =
          rationalCohomologyMap (pr V') q ≫
            higherDirectImageGerm j q (V := (Opens.map pr₁).obj V') (x, s) hx) ∧
    (∃ φ : (constantSheaf (Opens.grothendieckTopology (TopCat.of (Metric.ball c r)))
          (ModuleCat.{0} ℚ)).obj L ≅ (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj R,
      ∀ (V' : Opens V) (hx : x ∈ V') (s : Metric.ball c r),
        (directImagePresheaf j' q).germ V' x hx ≫
          (constantSheafAdj _ (ModuleCat.{0} ℚ) isTerminalTop).unit.app L ≫
            ((TopCat.Sheaf.forget _ _).map φ.hom).app (op ⊤) ≫
              ((TopCat.Sheaf.forget _ _).obj
                ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj R)).germ ⊤ s trivial =
        rationalCohomologyMap (pr V') q ≫
          higherDirectImageGerm j q (V := (Opens.map pr₁).obj V') (x, s) hx ≫
            stalkToPullbackStalk i R s) ∧
    (FiniteDimensional ℚ L →
      IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj R)) := by
  intro P j i j' pr₁ pr L R
  let F := directImagePresheaf j q
  let Fv := directImagePresheaf j' q
  let α : Fv ⟶ (TopCat.Presheaf.pushforward _ pr₁).obj F :=
    { app := fun V' ↦ rationalCohomologyMap (pr V'.unop) q
      naturality := by
        intro V W h
        dsimp [Fv, F, directImagePresheaf]
        rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_comp]
        rfl }
  let β : ∀ s : Metric.ball c r, L ⟶ F.stalk (x, s) := fun s ↦
    (TopCat.Presheaf.stalkFunctor _ x).map α ≫ TopCat.Presheaf.stalkPushforward _ pr₁ F (x, s)
  have hβ : ∀ (s : Metric.ball c r) (V' : Opens V) (hx : x ∈ V'),
      Fv.germ V' x hx ≫ β s = rationalCohomologyMap (pr V') q ≫
        F.germ ((Opens.map pr₁).obj V') (x, s) hx := by
    intro s V' hx
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
    exact congrArg (α.app (op V') ≫ ·)
      (TopCat.Presheaf.stalkPushforward_germ (ModuleCat.{0} ℚ) pr₁ F V' ((x, s) : P) hx)
  -- the boxes `O × E` around `(x, s)`, with `E ⊆ Δ` open and convex
  let box : Opens V → (E : Set ℂ) → IsOpen E → Opens P := fun O E hE ↦
    ⟨{p | p.1 ∈ O ∧ (p.2 : ℂ) ∈ E}, (O.isOpen.preimage continuous_fst).inter
      (hE.preimage (continuous_subtype_val.comp continuous_snd))⟩
  let prD : ∀ (O : Opens V) (E : Set ℂ) (hE : IsOpen E),
      preimageSpace j (box O E hE) ⟶ preimageSpace j' O := fun O E hE ↦
    TopCat.ofHom ⟨fun w ↦ ⟨w.1.1, w.2.1⟩,
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _)⟩
  have hprD : ∀ (O : Opens V) (E : Set ℂ) (hE : IsOpen E), Convex ℝ E → ∀ s0 ∈ E,
      E ⊆ Metric.ball c r → IsIso (rationalCohomologyMap (prD O E hE) q) := by
    intro O E hE hconv s0 hs0 hEb
    let σ : preimageSpace j' O ⟶ preimageSpace j (box O E hE) :=
      TopCat.ofHom ⟨fun y ↦ ⟨(y.1, ⟨s0, hEb hs0⟩), ⟨y.2, hs0⟩⟩,
        ((continuous_subtype_val.prodMk continuous_const).subtype_mk _)⟩
    refine isIso_rationalCohomologyMap_of_homotopy (prD O E hE) σ rfl
      { toFun := fun tw ↦ ⟨(tw.2.1.1, ⟨(1 - (tw.1 : ℝ)) • s0 + (tw.1 : ℝ) • (tw.2.1.2 : ℂ),
            hEb (hconv hs0 tw.2.2.2 (unitInterval.one_minus_nonneg tw.1) tw.1.2.1
              (sub_add_cancel 1 _))⟩),
          ⟨tw.2.2.1, hconv hs0 tw.2.2.2 (unitInterval.one_minus_nonneg tw.1) tw.1.2.1
              (sub_add_cancel 1 _)⟩⟩
        continuous_toFun := by
          refine Continuous.subtype_mk (Continuous.prodMk ?_ (Continuous.subtype_mk ?_ _)) _
          · exact continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
          · fun_prop
        map_zero_left := fun w ↦ by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            simp [σ, prD]
        map_one_left := fun w ↦ by
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            simp } q
  -- restriction of the pullback along `pr₁` to a box
  have hres : ∀ (O O' : Opens V) (E : Set ℂ) (hE : IsOpen E) (h : box O' E hE ≤
      (Opens.map pr₁).obj O) (h' : O' ≤ O),
      rationalCohomologyMap (pr O) q ≫ F.map (homOfLE h).op =
        Fv.map (homOfLE h').op ≫ rationalCohomologyMap (prD O' E hE) q := by
    intro O O' E hE h h'
    change rationalCohomologyMap _ q ≫ rationalCohomologyMap (preimageInclusion j h) q =
      rationalCohomologyMap (preimageInclusion j' h') q ≫ _
    rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_comp]
    rfl
  have hβbij : ∀ s, Function.Bijective (β s) := by
    intro s
    have hβa : ∀ (O : Opens V) (hx : x ∈ O) (d : Fv.obj (op O)),
        β s (Fv.germ O x hx d) = F.germ ((Opens.map pr₁).obj O) (x, s) hx
          (rationalCohomologyMap (pr O) q d) := fun O hx d ↦
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom (hβ s O hx) d).trans (ConcreteCategory.comp_apply _ _ _))
    have hresa : ∀ (O O' : Opens V) (E : Set ℂ) (hE : IsOpen E) (h : box O' E hE ≤
        (Opens.map pr₁).obj O) (h' : O' ≤ O) (d : Fv.obj (op O)),
        F.map (homOfLE h).op (rationalCohomologyMap (pr O) q d) =
          rationalCohomologyMap (prD O' E hE) q (Fv.map (homOfLE h').op d) := fun O O' E hE h h' d ↦
      (ConcreteCategory.comp_apply _ _ _).symm.trans
        ((ConcreteCategory.congr_hom (hres O O' E hE h h') d).trans
          (ConcreteCategory.comp_apply _ _ _))
    refine ⟨(injective_iff_map_eq_zero (β s).hom).2 fun l hl ↦ ?_, fun t ↦ ?_⟩
    · obtain ⟨O, hxO, d, rfl⟩ := TopCat.Presheaf.exists_germ_eq Fv l
      rw [hβa] at hl
      obtain ⟨W, hW, iU, iV, hWd⟩ := TopCat.Presheaf.germ_eq F (U := (Opens.map pr₁).obj O)
        (V := (Opens.map pr₁).obj O) ((x, s) : P) hxO hxO _ 0
        (hl.trans (map_zero _).symm)
      rw [map_zero] at hWd
      obtain ⟨O', hxO', hO'O, E, hE, hconv, hsE, hEb, (hle : box O' E hE ≤ W)⟩ :=
        exists_box_subset W.isOpen hW hxO
      have := hprD O' E hE hconv s hsE hEb
      have h1 : box O' E hE ≤ (Opens.map pr₁).obj O := hle.trans iU.le
      have h2 := hresa O O' E hE h1 hO'O d
      have h3 : F.map (homOfLE h1).op (rationalCohomologyMap (pr O) q d) = 0 := by
        rw [show (homOfLE h1).op = iU.op ≫ (homOfLE hle).op from rfl, Functor.map_comp]
        exact (ConcreteCategory.comp_apply _ _ _).trans ((congrArg _ hWd).trans (map_zero _))
      rw [h3] at h2
      have h4 : Fv.map (homOfLE hO'O).op d = 0 :=
        (injective_iff_map_eq_zero (rationalCohomologyMap (prD O' E hE) q).hom).1
          (ConcreteCategory.bijective_of_isIso _).1 _ h2.symm
      rw [← TopCat.Presheaf.germ_res_apply Fv (homOfLE hO'O) x hxO', h4, map_zero]
    · obtain ⟨N, hN, c0, rfl⟩ := TopCat.Presheaf.exists_germ_eq F t
      obtain ⟨O, hxO, -, E, hE, hconv, hsE, hEb, (hle : box O E hE ≤ N)⟩ :=
        exists_box_subset (O₀ := ⊤) N.isOpen hN trivial
      have := hprD O E hE hconv s hsE hEb
      obtain ⟨d, hd⟩ := (ConcreteCategory.bijective_of_isIso
        (rationalCohomologyMap (prD O E hE) q)).2 (F.map (homOfLE hle).op c0)
      refine ⟨Fv.germ O x hxO d, ?_⟩
      have hO : box O E hE ≤ (Opens.map pr₁).obj O := fun p hp ↦ hp.1
      have h2 := hresa O O E hE hO le_rfl d
      rw [show (homOfLE (le_refl O)).op = 𝟙 (op O) from rfl, Fv.map_id] at h2
      refine (hβa O hxO d).trans ((TopCat.Presheaf.germ_res_apply F (homOfLE hO) ((x, s) : P)
        ⟨hxO, hsE⟩ _).symm.trans ?_)
      exact (congrArg (F.germ (box O E hE) ((x, s) : P) ⟨hxO, hsE⟩) (h2.trans hd)).trans
        (TopCat.Presheaf.germ_res_apply F (homOfLE hle) ((x, s) : P) ⟨hxO, hsE⟩ c0)
  have he : ∀ s : Metric.ball c r, ∃ e : L ≅ ((TopCat.Sheaf.forget _ P).obj R).stalk (x, s),
      ∀ (V' : Opens V) (hx : x ∈ V'),
        (directImagePresheaf j' q).germ V' x hx ≫ e.hom =
          rationalCohomologyMap (pr V') q ≫
            higherDirectImageGerm j q (V := (Opens.map pr₁).obj V') (x, s) hx := by
    intro s
    have : IsIso (β s) := (ConcreteCategory.isIso_iff_bijective _).2 (hβbij s)
    let y : P := (x, s)
    let τ : F.stalk y ⟶ ((TopCat.Sheaf.forget _ P).obj R).stalk y :=
      (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) y).map
        (toSheafify (Opens.grothendieckTopology P) F)
    have : IsIso τ := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y (ModuleCat.{0} ℚ) F
    refine ⟨asIso (β s ≫ τ), fun V' hx ↦ ?_⟩
    rw [asIso_hom, ← Category.assoc, hβ s V' hx]
    exact Category.assoc _ _ _
  let G := (TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).obj R)
  let γ : Fv ⟶ (TopCat.Presheaf.pushforward _ pr₁).obj ((TopCat.Presheaf.pushforward _ i).obj G) :=
    α ≫ (TopCat.Presheaf.pushforward _ pr₁).map (toSheafify (Opens.grothendieckTopology P) F ≫
      (TopCat.Sheaf.forget _ P).map ((TopCat.Sheaf.pullbackPushforwardAdjunction _ i).unit.app R))
  let H := (TopCat.Presheaf.pushforward _ pr₁).obj ((TopCat.Presheaf.pushforward _ i).obj G)
  let ψ : H.stalk x ⟶ G.obj (op ⊤) :=
    colimit.desc ((OpenNhds.inclusion x).op ⋙ H)
      { pt := G.obj (op ⊤)
        ι :=
          { app := fun U ↦ G.map (homOfLE (fun _ _ ↦ U.unop.2 :
              (⊤ : Opens (Metric.ball c r)) ≤ (Opens.map i).obj ((Opens.map pr₁).obj U.unop.1))).op
            naturality := by
              intro U W h
              exact (G.map_comp _ _).symm.trans (Category.comp_id _).symm } }
  let θ : L ⟶ G.obj (op ⊤) := (TopCat.Presheaf.stalkFunctor _ x).map γ ≫ ψ
  let adj := constantSheafAdj (Opens.grothendieckTopology (TopCat.of (Metric.ball c r)))
    (ModuleCat.{0} ℚ) isTerminalTop
  let φhom := (adj.homEquiv L ((TopCat.Sheaf.pullback _ i).obj R)).symm θ
  have hφθ : ∀ s : Metric.ball c r, adj.unit.app L ≫
      ((TopCat.Sheaf.forget _ _).map φhom).app (op ⊤) ≫ G.germ ⊤ s trivial =
        θ ≫ G.germ ⊤ s trivial := fun s ↦
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ G.germ ⊤ s trivial)
      ((adj.homEquiv_unit L _ φhom).symm.trans ((adj.homEquiv _ _).apply_symm_apply θ)))
  have hpin : ∀ (V' : Opens V) (hx : x ∈ V') (s : Metric.ball c r),
      Fv.germ V' x hx ≫ θ ≫ G.germ ⊤ s trivial =
        rationalCohomologyMap (pr V') q ≫
          higherDirectImageGerm j q (V := (Opens.map pr₁).obj V') (x, s) hx ≫
            stalkToPullbackStalk i R s := by
    intro V' hx s
    have h1 : Fv.germ V' x hx ≫ θ = γ.app (op V') ≫
        G.map (homOfLE (fun _ _ ↦ hx : (⊤ : Opens (Metric.ball c r)) ≤
          (Opens.map i).obj ((Opens.map pr₁).obj V'))).op := by
      erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc]
      exact congrArg (γ.app (op V') ≫ ·) (colimit.ι_desc _ _)
    rw [← Category.assoc, h1, Category.assoc]
    erw [TopCat.Presheaf.germ_res]
    refine Eq.trans ?_ (congrArg (rationalCohomologyMap (pr V') q ≫ ·)
      ((Category.assoc _ _ _).trans
        (germ_comp_stalkToPullbackStalk i F R (toSheafify _ F) _ s hx))).symm
    simp only [γ]
    rfl
  have hiso : ∀ s, IsIso ((TopCat.Presheaf.stalkFunctor _ s).map φhom.1) := by
    intro s
    obtain ⟨e, he'⟩ := he s
    let CL := (TopCat.Sheaf.forget _ _).obj
      ((constantSheaf (Opens.grothendieckTopology (TopCat.of (Metric.ball c r)))
        (ModuleCat.{0} ℚ)).obj L)
    let u : L ⟶ CL.stalk s := adj.unit.app L ≫ CL.germ ⊤ s trivial
    have hu : u ≫ (TopCat.Presheaf.stalkFunctor _ s).map φhom.1 =
        e.hom ≫ stalkToPullbackStalk i R s := by
      refine TopCat.Presheaf.stalk_hom_ext Fv (fun V' hx ↦ ?_)
      have h2 := TopCat.Presheaf.stalkFunctor_map_germ ⊤ s trivial φhom.1
      refine Eq.trans ?_ ((hpin V' hx s).trans ?_)
      · refine congrArg (Fv.germ V' x hx ≫ ·) ?_
        exact (congrArg (adj.unit.app L ≫ ·) h2).trans (hφθ s)
      · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ stalkToPullbackStalk i R s)
          (he' V' hx).symm).trans (Category.assoc _ _ _))
    have := isIso_stalkToPullbackStalk i R s
    exact isIso_of_isIso_comp_of_surjective u _ (surjective_constantSheaf_germ L s)
      (hu ▸ @IsIso.comp_isIso _ _ _ _ _ _ _ e.isIso_hom this)
  have : IsIso φhom := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso φhom
  refine ⟨he, ⟨asIso φhom, fun V' hx s ↦ ?_⟩, fun hL s ↦ ?_⟩
  · exact (congrArg (Fv.germ V' x hx ≫ ·) (hφθ s)).trans (hpin V' hx s)
  · exact ⟨⊤, trivial, L, hL, ⟨(TopCat.Sheaf.pullback _ (Opens.inclusion' ⊤)).mapIso
      (asIso φhom).symm ≪≫ (pullbackConstIso _).app L⟩⟩

end MMP.Fourfold
