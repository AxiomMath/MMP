module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.CurvePuncturedRestrictionSurjective
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.FiniteMonodromy

/-!
# lem mmp conductor curve punctured restriction split

Chain fold of: `lem_mmp_conductor_curve_punctured_restriction_split`.
-/

/-! ### `lem_mmp_conductor_curve_punctured_restriction_split` -/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.Fold06.LemMmpConductorCurvePuncturedRestrictionSplit

open MMP.Fourfold

section Stalks

variable {X : TopCat.{0}}

/-- Stalks of a presheaf at equal points, identified by `cast`, see `stalkCongr`. -/
private lemma stalkCongr_apply_eq_cast (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X) {x y : X}
    (h : x = y) (e : ToType (F.stalk x) = ToType (F.stalk y)) (w : F.stalk x) :
    (F.stalkCongr (.of_eq h)).hom.hom w = cast e w := by
  subst h
  change (F.stalkSpecializes (specializes_refl x)).hom w = w
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

private lemma cast_germ (F : TopCat.Presheaf (ModuleCat.{0} ℚ) X) (U : Opens X) {x y : X}
    (h : x = y) (hx : x ∈ U) (hy : y ∈ U) (u : ToType (F.obj (op U)))
    (e : ToType (F.stalk x) = ToType (F.stalk y)) :
    cast e (F.germ U x hx u) = F.germ U y hy u := by
  subst h
  rfl

end Stalks

section Pullback

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

private lemma stalkPushforward_naturality
    {F G : TopCat.Presheaf (ModuleCat.{0} ℚ) X} (g : F ⟶ G) (x : X) :
    TopCat.Presheaf.stalkPushforward _ f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map g =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Presheaf.pushforward _ f).map g) ≫
        TopCat.Presheaf.stalkPushforward _ f G x := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦ ?_
  erw [TopCat.Presheaf.stalkPushforward_germ_assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
  rfl

private lemma stalkPushforward_comp_naturality
    {F' : TopCat.Presheaf (ModuleCat.{0} ℚ) Y} {G G' : TopCat.Presheaf (ModuleCat.{0} ℚ) X}
    (u : F' ⟶ (TopCat.Presheaf.pushforward _ f).obj G) (v : G ⟶ G') (x : X) :
    ((TopCat.Presheaf.stalkFunctor _ (f x)).map u ≫ TopCat.Presheaf.stalkPushforward _ f G x) ≫
        (TopCat.Presheaf.stalkFunctor _ x).map v =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map (u ≫ (TopCat.Presheaf.pushforward _ f).map v) ≫
        TopCat.Presheaf.stalkPushforward _ f G' x := by
  refine (Category.assoc _ _ _).trans ?_
  erw [stalkPushforward_naturality f v x, Functor.map_comp, Category.assoc]
  rfl

/-- The comparison `F_{f x} ⟶ (f⁻¹ F)_x` is natural in the sheaf `F`. -/
private lemma stalkToPullbackStalk_naturality {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) Y}
    (φ : F ⟶ G) (x : X) :
    stalkToPullbackStalk f F x ≫ (TopCat.Presheaf.stalkFunctor _ x).map
        ((TopCat.Sheaf.forget _ X).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ)) =
      (TopCat.Presheaf.stalkFunctor _ (f x)).map ((TopCat.Sheaf.forget _ Y).map φ) ≫
        stalkToPullbackStalk f G x := by
  unfold stalkToPullbackStalk
  refine (stalkPushforward_comp_naturality f _ _ x).trans ?_
  have := (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.naturality φ
  have h : (TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F) ≫
      (TopCat.Presheaf.pushforward _ f).map
        ((TopCat.Sheaf.forget _ X).map ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).map φ)) =
      (TopCat.Sheaf.forget _ Y).map φ ≫ (TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app G) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg _ this.symm).trans (Functor.map_comp _ _ _))
  refine (congrArg (fun g ↦ (TopCat.Presheaf.stalkFunctor _ (f x)).map g ≫
    TopCat.Presheaf.stalkPushforward _ f _ x) h).trans ?_
  exact (congrArg (· ≫ _) (Functor.map_comp _ _ _)).trans (Category.assoc _ _ _)

/-- The comparison `F_{f x} ⟶ (f⁻¹ F)_x` is injective: it is the inverse of
`Stacks.SheafifyStalk.stalkSheafPullbackIso`. -/
private lemma injective_stalkToPullbackStalk (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) (x : X) :
    Function.Injective (stalkToPullbackStalk f F x) := by
  rw [show stalkToPullbackStalk f F x = (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).inv
    from (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq _ f F x).symm]
  exact (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).symm.toLinearEquiv.injective

/-- On germs, the comparison `F_{f x} ⟶ (f⁻¹ F)_x` is the germ of the unit section. -/
private lemma stalkToPullbackStalk_germ (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) {W : Opens Y}
    (u : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (x : X) (hx : f x ∈ W) :
    stalkToPullbackStalk f F x (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx u) =
      ((TopCat.Sheaf.forget _ X).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ
        ((Opens.map f).obj W) x hx
        ((((TopCat.Sheaf.forget _ Y).map
          ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
            (op W)) u) := by
  have h : ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx ≫ stalkToPullbackStalk f F x =
      ((TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
          (op W) ≫ ((TopCat.Sheaf.forget _ X).obj
            ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F)).germ ((Opens.map f).obj W) x
              hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun φ => φ.hom u) h

end Pullback

section ConstantSheaf

/-- A sheaf isomorphic to a constant sheaf has a global section with any prescribed germ. -/
private lemma exists_global_germ_eq {W : TopCat.{0}} {P : TopCat.Sheaf (ModuleCat.{0} ℚ) W}
    {E : ModuleCat.{0} ℚ}
    (φ : P ≅ (constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E) (x : W)
    (c : ((TopCat.Sheaf.forget _ W).obj P).stalk x) :
    ∃ s : ToType (((TopCat.Sheaf.forget _ W).obj P).obj (op ⊤)),
      ((TopCat.Sheaf.forget _ W).obj P).germ ⊤ x trivial s = c := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) W := (Functor.const (Opens W)ᵒᵖ).obj E
  let c₁ := (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ W).map φ.hom) c
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ) K
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso
    ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology W) K))).2 c₁
  obtain ⟨U, hU, e, rfl⟩ := K.exists_germ_eq c'
  let e' := ((CategoryTheory.toSheafify (Opens.grothendieckTopology W) K).app (op ⊤)).hom e
  refine ⟨(((TopCat.Sheaf.forget _ W).map φ.inv).app (op ⊤)) e', ?_⟩
  have h1 : K.germ U x hU e = K.germ ⊤ x trivial e :=
    TopCat.Presheaf.germ_res_apply K (homOfLE (le_top : U ≤ ⊤)) x hU e
  have h2 : ((TopCat.Sheaf.forget _ W).obj
      ((constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj E)).germ ⊤ x trivial
        e' = c₁ := by
    rw [← hc', h1]
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ x trivial
      (CategoryTheory.toSheafify (Opens.grothendieckTopology W) K) e).symm
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ x trivial _ e').symm.trans ?_
  refine (congrArg (fun a ↦ (TopCat.Presheaf.stalkFunctor _ x).map
    ((TopCat.Sheaf.forget _ W).map φ.inv) a) h2).trans ?_
  exact ((TopCat.Presheaf.stalkFunctor _ x).mapIso
    ((TopCat.Sheaf.forget _ W).mapIso φ)).hom_inv_id_apply c

end ConstantSheaf

section Transport

variable {M : TopCat.{0}}

/-- The stalk `𝓛_x` of a sheaf of `ℚ`-vector spaces. -/
private noncomputable abbrev stalkOf (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M) (x : M) :
    ModuleCat.{0} ℚ :=
  ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x

/-- The stalk map `φ_x` of a morphism of sheaves. -/
private noncomputable abbrev stMap {𝓕 𝓖 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (φ : 𝓕 ⟶ 𝓖) (x : M) :
    stalkOf 𝓕 x ⟶ stalkOf 𝓖 x :=
  (TopCat.Presheaf.stalkFunctor _ x).map ((TopCat.Sheaf.forget _ M).map φ)

/-- A parallel transport of `𝓛`, with the first three properties of
`MMP.Fourfold.IsLocalSystem.exists_parallelTransport` (satisfied by
`MMP.Fourfold.IsLocalSystem.parallelTransport`). -/
private structure IsTransport (𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M)
    (T : ∀ {x y : M}, Path.Homotopic.Quotient x y → (stalkOf 𝓛 x ≅ stalkOf 𝓛 y)) : Prop where
  const : ∀ {x y : M} (γ : Path x y),
    Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)) : TopCat.of unitInterval ⟶ M)).obj 𝓛 ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of unitInterval))
        (ModuleCat.{0} ℚ)).obj (((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x))
  germ : ∀ {x y : M} (γ : Path x y)
    (s : ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)) : TopCat.of unitInterval ⟶ M)).obj 𝓛)).obj
          (op ⊤))
    (v : ((TopCat.Sheaf.forget _ M).obj 𝓛).stalk x),
    stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (0 : unitInterval)
        (cast (by simp) v) =
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (0 : unitInterval)
          (Opens.mem_top _) s →
    stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (1 : unitInterval)
        (cast (by simp) ((T (Path.Homotopic.Quotient.mk γ)).hom v)) =
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (1 : unitInterval)
          (Opens.mem_top _) s
  trans : ∀ {x y z : M} (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z),
    T (γ.trans δ) = T γ ≪≫ T δ

private lemma exists_isTransport [LocallyPathConnectedSpace M]
    {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (h𝓛 : IsLocalSystem 𝓛) :
    ∃ T : ∀ {x y : M}, Path.Homotopic.Quotient x y → (stalkOf 𝓛 x ≅ stalkOf 𝓛 y), IsTransport 𝓛 T :=
  ⟨h𝓛.parallelTransport, ⟨h𝓛.nonempty_pullback_path_iso_constantSheaf,
    h𝓛.parallelTransport_germ, h𝓛.parallelTransport_trans⟩⟩

variable {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}
  {T : ∀ {x y : M}, Path.Homotopic.Quotient x y → (stalkOf 𝓛 x ≅ stalkOf 𝓛 y)}

/-- Every germ at the source of a path extends to a global section of the inverse image. -/
private lemma IsTransport.exists_section (hT : IsTransport 𝓛 T) {x y : M} (γ : Path x y)
    (v : stalkOf 𝓛 x) :
    ∃ s : ToType (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)) : TopCat.of unitInterval ⟶ M)).obj 𝓛)).obj
          (op ⊤)),
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (0 : unitInterval)
          (Opens.mem_top _) s =
        stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (0 : unitInterval)
          (cast (by simp) v) := by
  obtain ⟨φ⟩ := hT.const γ
  exact exists_global_germ_eq φ 0 _

/-- Transport along `γ` is read off from a global section `s` of `γ⁻¹ 𝓛`: if `v` is the germ
of `s` at `0` and `w` the germ of `s` at `1`, then `T γ v = w`. -/
private lemma IsTransport.hom_eq_of_germ (hT : IsTransport 𝓛 T) {x y : M} (γ : Path x y)
    (s : ToType (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)) : TopCat.of unitInterval ⟶ M)).obj 𝓛)).obj
          (op ⊤)))
    (v : stalkOf 𝓛 x) (w : stalkOf 𝓛 y)
    (h0 : stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (0 : unitInterval)
        (cast (by simp) v) =
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (0 : unitInterval)
          (Opens.mem_top _) s)
    (h1 : stalkToPullbackStalk (TopCat.ofHom (γ : C(unitInterval, M))) 𝓛 (1 : unitInterval)
        (cast (by simp) w) =
      ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (γ : C(unitInterval, M)))).obj 𝓛)).germ ⊤ (1 : unitInterval)
          (Opens.mem_top _) s) :
    (T (Path.Homotopic.Quotient.mk γ)).hom v = w :=
  (cast_inj _).1 (injective_stalkToPullbackStalk _ 𝓛 1 ((hT.germ γ s v h0).trans h1.symm))

private lemma IsTransport.refl (hT : IsTransport 𝓛 T) (x : M) :
    T (Path.Homotopic.Quotient.refl x) = Iso.refl _ := by
  have h := congrArg Iso.hom (hT.trans (Path.Homotopic.Quotient.refl x)
    (Path.Homotopic.Quotient.refl x))
  rw [Path.Homotopic.Quotient.refl_trans] at h
  ext1
  exact (cancel_epi (T (Path.Homotopic.Quotient.refl x)).hom).1
    ((Category.comp_id _).trans h).symm

private lemma IsTransport.symm (hT : IsTransport 𝓛 T) {x y : M}
    (q : Path.Homotopic.Quotient x y) : (T q.symm).hom = (T q).inv := by
  have h := congrArg Iso.hom (hT.trans q q.symm)
  rw [Path.Homotopic.Quotient.trans_symm, hT.refl] at h
  exact ((T q).inv_ext h.symm).symm

/-- **Sections are flat.** Transport along a path inside the domain of a section carries its
germ at the source to its germ at the target. -/
private lemma IsTransport.germ_section (hT : IsTransport 𝓛 T) {U : Opens M}
    (u : ToType (((TopCat.Sheaf.forget _ M).obj 𝓛).obj (op U))) {x y : M} (γ : Path x y)
    (hγ : ∀ a, γ a ∈ U) (hx : x ∈ U) (hy : y ∈ U) :
    (T (Path.Homotopic.Quotient.mk γ)).hom (((TopCat.Sheaf.forget _ M).obj 𝓛).germ U x hx u) =
      ((TopCat.Sheaf.forget _ M).obj 𝓛).germ U y hy u := by
  let g : TopCat.of unitInterval ⟶ M := TopCat.ofHom (γ : C(unitInterval, M))
  have hU : (⊤ : Opens (TopCat.of unitInterval)) ≤ (Opens.map g).obj U := fun a _ => hγ a
  let s := ((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj
    𝓛)).map (homOfLE hU).op ((((TopCat.Sheaf.forget _ M).map
      ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g).unit.app 𝓛)).app
        (op U)) u)
  have hs : ∀ a : unitInterval, ((TopCat.Sheaf.forget _ _).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj 𝓛)).germ ⊤ a (Opens.mem_top _) s =
      stalkToPullbackStalk g 𝓛 a (((TopCat.Sheaf.forget _ M).obj 𝓛).germ U (g a) (hγ a) u) := by
    intro a
    rw [stalkToPullbackStalk_germ]
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE hU) a (Opens.mem_top _) _
  refine hT.hom_eq_of_germ γ s _ _ ?_ ?_
  · rw [hs, cast_germ _ U γ.source.symm hx (hγ 0)]
    rfl
  · rw [hs, cast_germ _ U γ.target.symm hy (hγ 1)]
    rfl

private lemma cast_stMap {𝓕 𝓖 : TopCat.Sheaf (ModuleCat.{0} ℚ) M} (φ : 𝓕 ⟶ 𝓖) {a b : M}
    (h : a = b) (w : stalkOf 𝓕 a) (e₁ : ToType (stalkOf 𝓕 a) = ToType (stalkOf 𝓕 b))
    (e₂ : ToType (stalkOf 𝓖 a) = ToType (stalkOf 𝓖 b)) :
    stMap φ b (cast e₁ w) = cast e₂ (stMap φ a w) := by
  subst h
  rfl

/-- **Transport commutes with morphisms of sheaves.** -/
private lemma IsTransport.comm {𝓕 𝓖 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}
    {TF : ∀ {x y : M}, Path.Homotopic.Quotient x y → (stalkOf 𝓕 x ≅ stalkOf 𝓕 y)}
    {TG : ∀ {x y : M}, Path.Homotopic.Quotient x y → (stalkOf 𝓖 x ≅ stalkOf 𝓖 y)}
    (hF : IsTransport 𝓕 TF) (hG : IsTransport 𝓖 TG) (φ : 𝓕 ⟶ 𝓖) {x y : M}
    (q : Path.Homotopic.Quotient x y) :
    (TF q).hom ≫ stMap φ y = stMap φ x ≫ (TG q).hom := by
  induction q using Path.Homotopic.Quotient.ind with | mk γ => ?_
  ext w
  let g : TopCat.of unitInterval ⟶ M := TopCat.ofHom (γ : C(unitInterval, M))
  obtain ⟨s, hs⟩ := hF.exists_section γ w
  let s' := (((TopCat.Sheaf.forget _ _).map
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).map φ)).app (op ⊤)) s
  have nat : ∀ (a : unitInterval) (c : stalkOf 𝓕 (g a)),
      stMap ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).map φ) a
        (stalkToPullbackStalk g 𝓕 a c) = stalkToPullbackStalk g 𝓖 a (stMap φ (g a) c) :=
    fun a c => congrArg (fun m => m.hom c) (stalkToPullbackStalk_naturality g φ a)
  have hgerm : ∀ a : unitInterval, ((TopCat.Sheaf.forget _ _).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj 𝓖)).germ ⊤ a (Opens.mem_top _) s' =
      stMap ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).map φ) a
        (((TopCat.Sheaf.forget _ _).obj
          ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).obj 𝓕)).germ ⊤ a (Opens.mem_top _) s) :=
    fun a => (TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ a (Opens.mem_top _) _ s).symm
  refine (hG.hom_eq_of_germ γ s' _ _ ?_ ?_).symm
  · rw [hgerm, hs, nat, cast_stMap φ (b := g 0) γ.source.symm]
    rfl
  · rw [hgerm, ← hF.germ γ s w hs.symm, nat, cast_stMap φ (b := g 1) γ.target.symm]
    rfl

end Transport

section Gluing

variable {M : TopCat.{0}} {𝓕 𝓖 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}

/-- A family of stalk maps which is locally realized by sections: every section of `𝓖` is,
near every point of its domain, carried to a section of `𝓕`. -/
private def IsLocallyRealized (σ : ∀ x, stalkOf 𝓖 x ⟶ stalkOf 𝓕 x) : Prop :=
  ∀ (U : Opens M) (s : ToType (((TopCat.Sheaf.forget _ M).obj 𝓖).obj (op U))) (y : M)
    (_ : y ∈ U), ∃ (N : Opens M) (_ : y ∈ N) (hNU : N ≤ U)
      (t : ToType (((TopCat.Sheaf.forget _ M).obj 𝓕).obj (op N))), ∀ z (hz : z ∈ N),
        ((TopCat.Sheaf.forget _ M).obj 𝓕).germ N z hz t =
          σ z (((TopCat.Sheaf.forget _ M).obj 𝓖).germ U z (hNU hz) s)

/-- A locally realized family of stalk maps carries every section to a section. -/
private lemma IsLocallyRealized.exists_section {σ : ∀ x, stalkOf 𝓖 x ⟶ stalkOf 𝓕 x}
    (hσ : IsLocallyRealized σ) (U : Opens M)
    (s : ToType (((TopCat.Sheaf.forget _ M).obj 𝓖).obj (op U))) :
    ∃ t : ToType (((TopCat.Sheaf.forget _ M).obj 𝓕).obj (op U)), ∀ z (hz : z ∈ U),
      ((TopCat.Sheaf.forget _ M).obj 𝓕).germ U z hz t =
        σ z (((TopCat.Sheaf.forget _ M).obj 𝓖).germ U z hz s) := by
  choose N hyN hNU t ht using fun y : U => hσ U s y.1 y.2
  obtain ⟨t', ht', -⟩ := 𝓕.existsUnique_gluing' N U (fun y => homOfLE (hNU y))
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hyN ⟨z, hz⟩⟩) t (by
      intro y y'
      refine TopCat.Presheaf.section_ext 𝓕 _ _ _ fun z hz => ?_
      change ((TopCat.Sheaf.forget _ M).obj 𝓕).germ _ z hz
          (((TopCat.Sheaf.forget _ M).obj 𝓕).map _ (t y)) =
        ((TopCat.Sheaf.forget _ M).obj 𝓕).germ _ z hz
          (((TopCat.Sheaf.forget _ M).obj 𝓕).map _ (t y'))
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht, ht])
  refine ⟨t', fun z hz => ?_⟩
  refine (TopCat.Presheaf.germ_res_apply ((TopCat.Sheaf.forget _ M).obj 𝓕)
    (homOfLE (hNU ⟨z, hz⟩)) z (hyN ⟨z, hz⟩) t').symm.trans ?_
  exact (congrArg _ (ht' ⟨z, hz⟩)).trans (ht _ z _)

/-- **Gluing stalk maps.** A locally realized family of stalk maps is the family of stalks of a
morphism of sheaves. -/
private lemma IsLocallyRealized.exists_hom {σ : ∀ x, stalkOf 𝓖 x ⟶ stalkOf 𝓕 x}
    (hσ : IsLocallyRealized σ) : ∃ φ : 𝓖 ⟶ 𝓕, ∀ x, stMap φ x = σ x := by
  choose t ht using hσ.exists_section
  have hext : ∀ (U : Opens M) (a b : ToType (((TopCat.Sheaf.forget _ M).obj 𝓕).obj (op U))),
      (∀ z (hz : z ∈ U), ((TopCat.Sheaf.forget _ M).obj 𝓕).germ U z hz a =
        ((TopCat.Sheaf.forget _ M).obj 𝓕).germ U z hz b) → a = b :=
    fun U a b h => TopCat.Presheaf.section_ext 𝓕 U a b h
  let app : ∀ U : (Opens M)ᵒᵖ, ((TopCat.Sheaf.forget _ M).obj 𝓖).obj U ⟶
      ((TopCat.Sheaf.forget _ M).obj 𝓕).obj U := fun U => ModuleCat.ofHom
    { toFun := t U.unop
      map_add' := fun a b => hext _ _ _ fun z hz => by
        rw [map_add, ht, ht, ht, map_add, map_add]
      map_smul' := fun c a => hext _ _ _ fun z hz => by
        rw [map_smul, ht, ht, map_smul, map_smul]
        rfl }
  let φ : 𝓖 ⟶ 𝓕 := ⟨{
    app := app
    naturality := fun U V i => by
      ext a
      refine hext _ _ _ fun z hz => ?_
      change ((TopCat.Sheaf.forget _ M).obj 𝓕).germ _ z hz
          (t V.unop (((TopCat.Sheaf.forget _ M).obj 𝓖).map i a)) =
        ((TopCat.Sheaf.forget _ M).obj 𝓕).germ _ z hz
          (((TopCat.Sheaf.forget _ M).obj 𝓕).map i (t U.unop a))
      rw [ht]
      refine (congrArg (σ z) (TopCat.Presheaf.germ_res_apply'
        ((TopCat.Sheaf.forget _ M).obj 𝓖) i z hz a)).trans ?_
      exact ((TopCat.Presheaf.germ_res_apply' _ i z hz _).trans (ht _ a z _)).symm }⟩
  refine ⟨φ, fun x => TopCat.Presheaf.stalk_hom_ext _ fun U hx => ?_⟩
  ext a
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx _ a).trans ?_
  exact ht U a x hx

end Gluing

section Average

variable {A B : Type} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]

/-- **Averaging a right inverse.** Let `ρ : A → B` be a surjective linear map and `H` a finite
group of pairs `(a, c)` of automorphisms with `ρ ∘ a = c ∘ ρ`. Averaging `a ∘ s₀ ∘ c⁻¹` over `H`
for a linear right inverse `s₀` of `ρ` gives an `H`-equivariant right inverse of `ρ`. -/
private lemma exists_equivariant_rightInverse (ρ : A →ₗ[ℚ] B) (hρ : Function.Surjective ρ)
    (H : Subgroup ((A ≃ₗ[ℚ] A) × (B ≃ₗ[ℚ] B))) [Finite H]
    (hH : ∀ h ∈ H, ρ ∘ₗ (h.1 : A →ₗ[ℚ] A) = (h.2 : B →ₗ[ℚ] B) ∘ₗ ρ) :
    ∃ s : B →ₗ[ℚ] A, ρ ∘ₗ s = LinearMap.id ∧
      ∀ h ∈ H, (h.1 : A →ₗ[ℚ] A) ∘ₗ s = s ∘ₗ (h.2 : B →ₗ[ℚ] B) := by
  obtain ⟨s₀, hs₀⟩ := ρ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hρ)
  haveI := Fintype.ofFinite H
  let f : H → (B →ₗ[ℚ] A) := fun k =>
    (k.1.1 : A →ₗ[ℚ] A) ∘ₗ s₀ ∘ₗ ((k.1.2⁻¹ : B ≃ₗ[ℚ] B) : B →ₗ[ℚ] B)
  have hn : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card H : ℚ)⁻¹ • ∑ k, f k, ?_, ?_⟩
  · have hf : ∀ (k : H) (b : B), ρ (f k b) = b := by
      intro k b
      have h1 := congrArg (fun m => m (s₀ ((k.1.2⁻¹ : B ≃ₗ[ℚ] B) b))) (hH k.1 k.2)
      have h2 := congrArg (fun m => m ((k.1.2⁻¹ : B ≃ₗ[ℚ] B) b)) hs₀
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at h1 h2
      simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [h1, h2, ← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    ext b
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum, hf, Finset.sum_const, Finset.card_univ, LinearMap.id_apply]
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  · intro h hh
    have key : ∀ (k : H) (b : B), h.1 (f k b) = f (⟨h, hh⟩ * k) (h.2 b) := by
      intro k b
      simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, Subgroup.coe_mul, Prod.fst_mul,
        Prod.snd_mul, mul_inv_rev, LinearEquiv.mul_apply]
      rw [← LinearEquiv.mul_apply h.2⁻¹, inv_mul_cancel]
      rfl
    ext b
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum, LinearEquiv.coe_coe, key]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : H)) _ _ (fun _ => rfl)

end Average

section Splitting

variable {M : TopCat.{0}} {𝓕 𝓖 : TopCat.Sheaf (ModuleCat.{0} ℚ) M}
  {TF : ∀ {x y : M}, Path.Homotopic.Quotient x y → (stalkOf 𝓕 x ≅ stalkOf 𝓕 y)}
  {TG : ∀ {x y : M}, Path.Homotopic.Quotient x y → (stalkOf 𝓖 x ≅ stalkOf 𝓖 y)}

/-- At a base point `b` with finite monodromy of `𝓕`, the stalk map `r_b` has a right inverse
commuting with the monodromy of `𝓕` and `𝓖`. -/
private lemma exists_equivariant_splitting_at (hF : IsTransport 𝓕 TF)
    (hG : IsTransport 𝓖 TG) (r : 𝓕 ⟶ 𝓖) (b : M) (hr : Function.Surjective (stMap r b))
    (hfin : {g | ∃ q : Path.Homotopic.Quotient b b, (TF q).toLinearEquiv = g}.Finite) :
    ∃ s : stalkOf 𝓖 b ⟶ stalkOf 𝓕 b, s ≫ stMap r b = 𝟙 _ ∧
      ∀ q : Path.Homotopic.Quotient b b, s ≫ (TF q).hom = (TG q).hom ≫ s := by
  let ρ : Path.Homotopic.Quotient b b →
      (stalkOf 𝓕 b ≃ₗ[ℚ] stalkOf 𝓕 b) × (stalkOf 𝓖 b ≃ₗ[ℚ] stalkOf 𝓖 b) :=
    fun q => ((TF q).toLinearEquiv, (TG q).toLinearEquiv)
  have hmul : ∀ q q', ρ q * ρ q' = ρ (q'.trans q) := fun q q' => by
    refine Prod.ext (LinearEquiv.ext fun a => ?_) (LinearEquiv.ext fun a => ?_) <;>
      simp [ρ, hF.trans, hG.trans]
  have hone : ρ (Path.Homotopic.Quotient.refl b) = 1 := by
    refine Prod.ext (LinearEquiv.ext fun a => ?_) (LinearEquiv.ext fun a => ?_) <;>
      simp [ρ, hF.refl, hG.refl]
  have hinv : ∀ q, (ρ q)⁻¹ = ρ q.symm := fun q => by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [hmul, Path.Homotopic.Quotient.trans_symm, hone]
  have hcomm : ∀ q : Path.Homotopic.Quotient b b,
      (stMap r b).hom ∘ₗ ((TF q).toLinearEquiv : stalkOf 𝓕 b →ₗ[ℚ] stalkOf 𝓕 b) =
      ((TG q).toLinearEquiv : stalkOf 𝓖 b →ₗ[ℚ] stalkOf 𝓖 b) ∘ₗ (stMap r b).hom := fun q =>
    LinearMap.ext fun a => ConcreteCategory.congr_hom (hF.comm hG r q) a
  let H : Subgroup ((stalkOf 𝓕 b ≃ₗ[ℚ] stalkOf 𝓕 b) × (stalkOf 𝓖 b ≃ₗ[ℚ] stalkOf 𝓖 b)) :=
    { carrier := Set.range ρ
      mul_mem' := by
        rintro _ _ ⟨q, rfl⟩ ⟨q', rfl⟩
        exact ⟨q'.trans q, (hmul q q').symm⟩
      one_mem' := ⟨_, hone⟩
      inv_mem' := by
        rintro _ ⟨q, rfl⟩
        exact ⟨q.symm, (hinv q).symm⟩ }
  have hinj : Set.InjOn Prod.fst (Set.range ρ) := by
    rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ h
    refine Prod.ext h (LinearEquiv.ext fun c => ?_)
    obtain ⟨a, rfl⟩ := hr c
    have h1 := LinearMap.congr_fun (hcomm q) a
    have h2 := LinearMap.congr_fun (hcomm q') a
    have h3 : (TF q).toLinearEquiv a = (TF q').toLinearEquiv a := LinearEquiv.congr_fun h a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1 h2
    change (TG q).toLinearEquiv _ = (TG q').toLinearEquiv _
    rw [← h1, ← h2, h3]
  have hfinH : (Set.range ρ).Finite :=
    Set.Finite.of_finite_image (hfin.subset (by rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩; exact ⟨q, rfl⟩))
      hinj
  haveI : Finite H := hfinH.to_subtype
  obtain ⟨s, hs, heq⟩ := exists_equivariant_rightInverse (stMap r b).hom hr H
    (by rintro _ ⟨q, rfl⟩; exact hcomm q)
  refine ⟨ModuleCat.ofHom s, ?_, fun q => ?_⟩
  · ext c
    exact LinearMap.congr_fun hs c
  · ext c
    exact LinearMap.congr_fun (heq (ρ q) ⟨q, rfl⟩) c

/-- Stalk maps commuting with parallel transport are locally realized by sections. -/
private lemma IsLocallyRealized.of_transport [LocallyPathConnectedSpace M]
    (hF : IsTransport 𝓕 TF) (hG : IsTransport 𝓖 TG) {σ : ∀ x, stalkOf 𝓖 x ⟶ stalkOf 𝓕 x}
    (htr : ∀ {x y : M} (γ : Path x y), (TG (Path.Homotopic.Quotient.mk γ)).hom ≫ σ y =
      σ x ≫ (TF (Path.Homotopic.Quotient.mk γ)).hom) :
    IsLocallyRealized σ := by
  intro U a y hy
  obtain ⟨U', hyU', t', ht'⟩ := ((TopCat.Sheaf.forget _ M).obj 𝓕).exists_germ_eq
    (σ y (((TopCat.Sheaf.forget _ M).obj 𝓖).germ U y hy a))
  let W : Opens M := U ⊓ U'
  let N : Opens M := ⟨pathComponentIn (W : Set M) y, W.isOpen.pathComponentIn y⟩
  have hNW : N ≤ W := fun z hz => pathComponentIn_subset hz
  have hyN : y ∈ N := mem_pathComponentIn_self ⟨hy, hyU'⟩
  refine ⟨N, hyN, hNW.trans inf_le_left, ((TopCat.Sheaf.forget _ M).obj 𝓕).map
    (homOfLE (hNW.trans inf_le_right)).op t', fun z hz => ?_⟩
  let γ : Path y z := (hz : JoinedIn (W : Set M) y z).somePath
  have hγ : ∀ a, γ a ∈ W := (hz : JoinedIn (W : Set M) y z).somePath_mem
  rw [TopCat.Presheaf.germ_res_apply,
    ← hF.germ_section t' γ (fun a => (hγ a).2) hyU' (hNW hz).2, ht',
    ← hG.germ_section a γ (fun a => (hγ a).1) hy (hNW hz).1]
  exact (ConcreteCategory.congr_hom (htr γ) _).symm

/-- A morphism whose stalk maps are right inverses of those of `r` is a right inverse of `r`. -/
private lemma comp_eq_id_of_stMap {φ : 𝓖 ⟶ 𝓕} {r : 𝓕 ⟶ 𝓖}
    (h : ∀ x, stMap φ x ≫ stMap r x = 𝟙 _) : φ ≫ r = 𝟙 _ := by
  apply Sheaf.hom_ext
  ext U a
  refine TopCat.Presheaf.section_ext 𝓖 _ _ _ fun z hz => ?_
  refine (TopCat.Presheaf.stalkFunctor_map_germ_apply _ z hz
    ((TopCat.Sheaf.forget _ M).map (φ ≫ r)) a).symm.trans ?_
  rw [Functor.map_comp, Functor.map_comp]
  change (stMap φ z ≫ stMap r z) _ = _
  rw [h]
  rfl

/-- **The splitting.** A stalkwise surjective morphism `r : 𝓕 ⟶ 𝓖` of sheaves with parallel
transports on a locally path-connected space, such that the monodromy of `𝓕` at every point is
finite, is a split epimorphism. -/
private theorem isSplitEpi_of_transport [LocallyPathConnectedSpace M] (hF : IsTransport 𝓕 TF)
    (hG : IsTransport 𝓖 TG) (r : 𝓕 ⟶ 𝓖) (hr : ∀ x, Function.Surjective (stMap r x))
    (hfin : ∀ b : M,
      {g | ∃ q : Path.Homotopic.Quotient b b, (TF q).toLinearEquiv = g}.Finite) :
    IsSplitEpi r := by
  choose s hs₁ hs₂ using fun b => exists_equivariant_splitting_at hF hG r b (hr b) (hfin b)
  let base : M → M := fun x => Quotient.out (Quotient.mk (pathSetoid M) x)
  have hbase : ∀ x, Joined (base x) x := fun x =>
    Quotient.exact (s := pathSetoid M) (Quotient.out_eq (Quotient.mk (pathSetoid M) x))
  have hbase_eq : ∀ {x y : M}, Joined x y → base x = base y := fun h =>
    congrArg Quotient.out (Quotient.sound h)
  let σ' : ∀ (b : M) {x : M}, Path.Homotopic.Quotient b x → (stalkOf 𝓖 x ⟶ stalkOf 𝓕 x) :=
    fun b _ q => (TG q).inv ≫ s b ≫ (TF q).hom
  have hindep : ∀ (b : M) {x : M} (q q' : Path.Homotopic.Quotient b x), σ' b q = σ' b q' := by
    intro b x q q'
    have e := hs₂ b (q.trans q'.symm)
    rw [hF.trans, hG.trans, Iso.trans_hom, Iso.trans_hom, hF.symm, hG.symm] at e
    calc (TG q).inv ≫ s b ≫ (TF q).hom
        = (TG q).inv ≫ (s b ≫ (TF q).hom ≫ (TF q').inv) ≫ (TF q').hom := by simp
      _ = (TG q).inv ≫ (((TG q).hom ≫ (TG q').inv) ≫ s b) ≫ (TF q').hom := by rw [e]
      _ = (TG q').inv ≫ s b ≫ (TF q').hom := by simp
  let σ : ∀ x, stalkOf 𝓖 x ⟶ stalkOf 𝓕 x := fun x =>
    σ' (base x) (Path.Homotopic.Quotient.mk (hbase x).somePath)
  have hσ : ∀ {x : M} (b : M) (q : Path.Homotopic.Quotient b x), base x = b → σ x = σ' b q := by
    rintro x b q rfl
    exact hindep _ _ _
  have htr : ∀ {x y : M} (γ : Path x y), (TG (Path.Homotopic.Quotient.mk γ)).hom ≫ σ y =
      σ x ≫ (TF (Path.Homotopic.Quotient.mk γ)).hom := by
    intro x y γ
    rw [hσ (base x) ((Path.Homotopic.Quotient.mk (hbase x).somePath).trans
      (Path.Homotopic.Quotient.mk γ)) (hbase_eq ⟨γ.symm⟩)]
    simp only [σ, σ', hF.trans, hG.trans, Iso.trans_hom, Iso.trans_inv, Category.assoc,
      Iso.hom_inv_id_assoc]
  have hsplit : ∀ x, σ x ≫ stMap r x = 𝟙 _ := by
    intro x
    simp only [σ, σ', Category.assoc, hF.comm hG r]
    rw [reassoc_of% (hs₁ (base x)), Iso.inv_hom_id]
  obtain ⟨φ, hφ⟩ := (IsLocallyRealized.of_transport hF hG htr).exists_hom
  exact ⟨⟨⟨φ, comp_eq_id_of_stMap fun x => by rw [hφ, hsplit]⟩⟩⟩

end Splitting

section LocalSetting

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

/-- The monodromy relation of the finite-monodromy statement, along a loop `γ`, is the graph of
the parallel transport along `γ`. -/
private lemma transportRel_transport {Z : TopCat.{0}} {𝓛 : TopCat.Sheaf (ModuleCat.{0} ℚ) Z}
    {T : ∀ {x y : Z}, Path.Homotopic.Quotient x y → (stalkOf 𝓛 x ≅ stalkOf 𝓛 y)}
    (hT : IsTransport 𝓛 T)
    {t : Z} (γ : Path t t) (w : stalkOf 𝓛 t) :
    ∃ s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛).obj.obj (op ⊤)),
      (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          𝓛 0).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.source.symm)).hom.hom w) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛)).germ
            ⊤ 0 trivial).hom s ∧
      (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
          𝓛 1).hom
        ((((TopCat.Sheaf.forget _ _).obj 𝓛).stalkCongr (.of_eq γ.target.symm)).hom.hom
          ((T (Path.Homotopic.Quotient.mk γ)).hom w)) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj 𝓛)).germ
            ⊤ 1 trivial).hom s := by
  obtain ⟨s, hs⟩ := hT.exists_section γ w
  refine ⟨s, ?_, ?_⟩
  · rw [stalkCongr_apply_eq_cast _ γ.source.symm (by simp)]
    exact hs.symm
  · rw [stalkCongr_apply_eq_cast _ γ.target.symm (by simp)]
    exact hT.germ γ s w hs.symm

end LocalSetting

end MMP.Fold06.LemMmpConductorCurvePuncturedRestrictionSplit

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open MMP.Fold06.LemMmpConductorCurvePuncturedRestrictionSplit

/-- In a local setting `(Y, Θ, T, π)`, for every `π`-adapted open `T° ⊆ T`, the restriction map
`r : (R²π_* ℚ_Ỹ)|_{T°} ⟶ (R²j_* ℚ_{Y_reg})|_{T°}` is a split epimorphism: some morphism
`σ : (R²j_* ℚ_{Y_reg})|_{T°} ⟶ (R²π_* ℚ_Ỹ)|_{T°}` satisfies `σ ≫ r = 𝟙`. -/
@[mmp "lem_mmp_conductor_curve_punctured_restriction_split"]
public theorem isSplitEpi_localSystemRestriction {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
    (hLS : IsLocalSetting sY Θ T π) {To : (curveScheme T).Opens} (hTo : IsAdaptedOpen sY π To) :
    IsSplitEpi (localSystemRestriction sY hLS.isBiregular To) := by
  haveI : Smooth (To.ι ≫ curveι T ≫ sY) := hTo.smooth
  haveI := locallyPathConnectedSpace_analyticSpace (To.ι ≫ curveι T ≫ sY)
  obtain ⟨TF, hF⟩ := exists_isTransport hTo.isLocalSystem_resolution
  obtain ⟨TG, hG⟩ := exists_isTransport hTo.isLocalSystem
  refine isSplitEpi_of_transport hF hG _ (fun x =>
    surjective_localSystemRestrictionFibre hLS hTo x) fun b => ?_
  refine (hLS.finite_range_resolutionMonodromy hTo b).subset ?_
  rintro _ ⟨q, rfl⟩
  induction q using Path.Homotopic.Quotient.ind with | mk γ => ?_
  refine ⟨Path.Homotopic.Quotient.mk γ, LinearEquiv.ext fun w => ?_⟩
  exact (hLS.isTransportOf_iff_resolutionMonodromy_apply_eq hTo γ w _).1
    (transportRel_transport hF γ w)

end MMP.Fourfold
