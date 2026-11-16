module

public import MMP.Topology.Sheaves.Godement
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The Godement resolution along an open embedding

Let `f : T' ⟶ T` be an open embedding and `F` a sheaf of abelian groups on `T`. The comparison
`G^•(F) ⟶ f_* G^•(f⁻¹ F)` of Godement resolutions (`MMP.Analytic.godementResolutionPullback`) is
bijective on the sections over every open `U ⊆ f(T')`: the Godement resolution of the restriction
`f⁻¹ F` is the restriction of the Godement resolution of `F`.

The proof goes through the stalk maps `A_{f y} ⟶ (f_* B)_{f y} ⟶ B_y` of maps `φ : A ⟶ f_* B`.
For the unit `F ⟶ f_* f⁻¹ F` they are bijective; the lift `G(A) ⟶ f_* G(B)` of a map with
bijective stalk maps is bijective on sections over `U ⊆ f(T')`, since there it is the product of
the stalk maps reindexed along the bijection `f⁻¹ U ≃ U`; and the stalk maps of the induced map
of cokernels are bijective because taking stalks preserves cokernels.

## Main results

* `MMP.Analytic.isIso_stalkMap_pullbackPushforwardAdjunction_unit`: the stalk maps
  `F_{f y} ⟶ (f⁻¹ F)_y` of the unit of the inverse image adjunction are isomorphisms.
* `MMP.Analytic.godementResolutionPullback_app_bijective`: for an open embedding `f`, the
  comparison of Godement resolutions is bijective on sections over opens contained in the image
  of `f`.

## References

* [R. Godement, *Topologie algébrique et théorie des faisceaux*]
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace Opposite TopCat TopCat.Presheaf

universe u

namespace MMP.Analytic

variable {T T' : TopCat.{u}} (f : T' ⟶ T)

/-- The stalk map `A_{f y} ⟶ (f_* B)_{f y} ⟶ B_y` of a map `φ : A ⟶ f_* B`. -/
abbrev stalkMap {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) (y : T') :
    A.presheaf.stalk (f y) ⟶ B.presheaf.stalk y :=
  (stalkFunctor AddCommGrpCat.{u} (f y)).map φ.hom ≫
    B.presheaf.stalkPushforward AddCommGrpCat.{u} f y

/-- The stalk map of `φ ≫ f_* b` is the stalk map of `φ` followed by the stalk map of `b`. -/
lemma stalkMap_comp_pushforward {A : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B B' : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) (b : B ⟶ B') (y : T') :
    stalkMap f (φ ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map b) y =
      stalkMap f φ y ≫ (stalkFunctor AddCommGrpCat.{u} y).map b.hom :=
  (congrArg (· ≫ B'.presheaf.stalkPushforward AddCommGrpCat.{u} f y)
    ((stalkFunctor _ (f y)).map_comp φ.hom ((Presheaf.pushforward _ f).map b.hom))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (stalkFunctor_map_pushforward_comp_stalkPushforward f b.hom y)).trans
        (Category.assoc _ _ _).symm))

/-- The stalk map of `a ≫ φ` is the stalk map of `a` at `f y` followed by the stalk map of `φ`. -/
lemma stalkMap_precomp {A A' : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B : TopCat.Sheaf AddCommGrpCat.{u} T'} (a : A' ⟶ A)
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B) (y : T') :
    stalkMap f (a ≫ φ) y = (stalkFunctor AddCommGrpCat.{u} (f y)).map a.hom ≫ stalkMap f φ y :=
  (congrArg (· ≫ B.presheaf.stalkPushforward AddCommGrpCat.{u} f y)
    ((stalkFunctor _ (f y)).map_comp a.hom φ.hom)).trans (Category.assoc _ _ _)

/-- The stalk maps `F_{f y} ⟶ (f⁻¹ F)_y` of the unit `F ⟶ f_* f⁻¹ F` are isomorphisms. -/
lemma isIso_stalkMap_pullbackPushforwardAdjunction_unit (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (y : T') :
    IsIso (stalkMap f ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F)
      y) := by
  let adjS := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f
  let adjC := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (Opens.map f)
    AddCommGrpCat.{u} (Opens.grothendieckTopology T) (Opens.grothendieckTopology T')
  have hC : (adjC.unit.app F).hom =
      (Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F.obj ≫
        (Presheaf.pushforward AddCommGrpCat.{u} f).map (CategoryTheory.toSheafify _ _) := by
    simp [adjC, Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      Presheaf.pullbackPushforwardAdjunction, Adjunction.restrictFullyFaithful, Adjunction.comp,
      Functor.FullyFaithful.homEquiv, Adjunction.homEquiv_unit]
    rfl
  have e := Adjunction.unit_leftAdjointUniq_hom_app adjC adjS F
  change IsIso (stalkMap f (adjS.unit.app F) y)
  rw [← e]
  erw [stalkMap_comp_pushforward]
  have h1 : stalkMap f (adjC.unit.app F) y = stalkPullbackHom AddCommGrpCat.{u} f F.obj y ≫
      (stalkFunctor AddCommGrpCat.{u} y).map (CategoryTheory.toSheafify _ _) :=
    (congrArg (fun g => (stalkFunctor _ (f y)).map g ≫ _) hC).trans
      ((congrArg (· ≫ _) ((stalkFunctor _ (f y)).map_comp _ _)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (stalkFunctor_map_pushforward_comp_stalkPushforward f _ y)).trans
            (Category.assoc _ _ _).symm)))
  rw [h1]
  have i1 : IsIso (stalkPullbackHom AddCommGrpCat.{u} f F.obj y) :=
    (stalkPullbackIso AddCommGrpCat.{u} f F.obj y).isIso_hom
  have i2 := stalkFunctor_map_unit_toSheafify_isIso y AddCommGrpCat.{u}
    ((Presheaf.pullback AddCommGrpCat.{u} f).obj F.obj)
  have i3 : IsIso ((adjC.leftAdjointUniq adjS).hom.app F).hom :=
    ((sheafToPresheaf _ _).mapIso ((adjC.leftAdjointUniq adjS).app F)).isIso_hom
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ i1 i2)
    (@Functor.map_isIso _ _ _ _ _ _ _ _ i3)

/-- A map of presheaves bijective on the sections over every open contained in `O` is bijective
on the stalks at the points of `O`. -/
lemma stalkFunctor_map_bijective_of_app_bijective {X : TopCat.{u}}
    {F G : X.Presheaf AddCommGrpCat.{u}} (α : F ⟶ G) (O : Opens X)
    (hα : ∀ U ≤ O, Function.Bijective (α.app (op U))) (x : X) (hx : x ∈ O) :
    Function.Bijective ((stalkFunctor _ x).map α) := by
  constructor
  · intro s t hst
    obtain ⟨U₁, hxU₁, s, rfl⟩ := F.exists_germ_eq s
    obtain ⟨U₂, hxU₂, t, rfl⟩ := F.exists_germ_eq t
    rw [stalkFunctor_map_germ_apply, stalkFunctor_map_germ_apply] at hst
    obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst
    let i : W ⊓ O ⟶ W := homOfLE inf_le_left
    have hxWO : x ∈ W ⊓ O := ⟨hxW, hx⟩
    have heq' := congrArg (G.map i.op) heq
    simp only [← ConcreteCategory.comp_apply, ← G.map_comp, ← op_comp] at heq'
    simp only [ConcreteCategory.comp_apply, ← α.naturality_apply] at heq'
    replace heq' := (hα _ inf_le_right).1 heq'
    have := congrArg (F.germ (W ⊓ O) x hxWO) heq'
    simp only [germ_res_apply] at this
    exact this
  · intro t
    obtain ⟨U, hxU, t, rfl⟩ := G.exists_germ_eq t
    obtain ⟨s, hs⟩ := (hα (U ⊓ O) inf_le_right).2 (G.map (homOfLE inf_le_left).op t)
    have hxUO : x ∈ U ⊓ O := ⟨hxU, hx⟩
    refine ⟨F.germ (U ⊓ O) x hxUO s, ?_⟩
    rw [stalkFunctor_map_germ_apply, hs, germ_res_apply]

/-- In a commutative diagram of abelian groups whose rows `A₁ ⟶ A₂ ⟶ C₁ ⟶ 0` and
`B₁ ⟶ B₂ ⟶ C₂ ⟶ 0` are exact, bijectivity of `A₁ ⟶ B₁` and `A₂ ⟶ B₂` gives bijectivity of
`C₁ ⟶ C₂`. -/
lemma bijective_of_cokernel_rows {A₁ A₂ C₁ B₁ B₂ C₂ : AddCommGrpCat.{u}} (dA : A₁ ⟶ A₂)
    (pA : A₂ ⟶ C₁) (dB : B₁ ⟶ B₂) (pB : B₂ ⟶ C₂) (a : A₁ ⟶ B₁) (b : A₂ ⟶ B₂) (c : C₁ ⟶ C₂)
    (hA : Function.Surjective pA) (hB : Function.Surjective pB)
    (hBex : ∀ z, pB z = 0 → ∃ w, dB w = z)
    (hA0 : dA ≫ pA = 0) (sq₁ : dA ≫ b = a ≫ dB) (sq₂ : pA ≫ c = b ≫ pB)
    (ha : Function.Bijective a) (hb : Function.Bijective b) : Function.Bijective c := by
  have e₁ : ∀ w, b (dA w) = dB (a w) := fun w => ConcreteCategory.congr_hom sq₁ w
  have e₂ : ∀ z, c (pA z) = pB (b z) := fun z => ConcreteCategory.congr_hom sq₂ z
  have e₀ : ∀ w, pA (dA w) = 0 := fun w => ConcreteCategory.congr_hom hA0 w
  constructor
  · refine (injective_iff_map_eq_zero c.hom).2 fun u hu => ?_
    obtain ⟨z, rfl⟩ := hA u
    obtain ⟨w, hw⟩ := hBex (b z) ((e₂ z).symm.trans hu)
    obtain ⟨w₀, rfl⟩ := ha.2 w
    obtain rfl := hb.1 ((e₁ w₀).trans hw)
    exact e₀ w₀
  · intro v
    obtain ⟨z', rfl⟩ := hB v
    obtain ⟨z, rfl⟩ := hb.2 z'
    exact ⟨pA z, e₂ z⟩

/-- A left adjoint to abelian groups maps cokernel sequences to exact sequences with surjective
second map. -/
lemma surjective_and_exact_map_cokernel {C : Type*} [Category C] [Abelian C]
    (G : C ⥤ AddCommGrpCat.{u}) [G.IsLeftAdjoint] {X Y : C} (d : X ⟶ Y) :
    Function.Surjective (G.map (cokernel.π d)) ∧
      ∀ z, G.map (cokernel.π d) z = 0 → ∃ w, G.map d w = z := by
  have hc := CokernelCofork.mapIsColimit _ (cokernelIsCokernel d) G
  constructor
  · rw [← AddCommGrpCat.epi_iff_surjective]
    infer_instance
  · have hex := ShortComplex.exact_of_g_is_cokernel (ShortComplex.mk (G.map d)
      (G.map (cokernel.π d)) (by rw [← G.map_comp, cokernel.condition, G.map_zero])) hc
    rwa [ShortComplex.ab_exact_iff] at hex

/-- The stalk maps of a map of cokernels induced by maps with bijective stalk maps are
bijective. -/
lemma stalkMap_cokernel_bijective {A₁ A₂ : TopCat.Sheaf AddCommGrpCat.{u} T}
    {B₁ B₂ : TopCat.Sheaf AddCommGrpCat.{u} T'} (dA : A₁ ⟶ A₂) (dB : B₁ ⟶ B₂)
    (a : A₁ ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B₁)
    (b : A₂ ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B₂)
    (c : cokernel dA ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (cokernel dB))
    (sq₁ : dA ≫ b = a ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map dB)
    (sq₂ : cokernel.π dA ≫ c = b ≫ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map
      (cokernel.π dB))
    (ha : ∀ y, Function.Bijective (stalkMap f a y)) (hb : ∀ y, Function.Bijective (stalkMap f b y))
    (y : T') : Function.Bijective (stalkMap f c y) := by
  obtain ⟨hA, -⟩ := surjective_and_exact_map_cokernel
    (TopCat.Sheaf.forget AddCommGrpCat.{u} T ⋙ stalkFunctor AddCommGrpCat.{u} (f y)) dA
  obtain ⟨hB, hBex⟩ := surjective_and_exact_map_cokernel
    (TopCat.Sheaf.forget AddCommGrpCat.{u} T' ⋙ stalkFunctor AddCommGrpCat.{u} y) dB
  refine bijective_of_cokernel_rows
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} T ⋙ stalkFunctor AddCommGrpCat.{u} (f y)).map dA)
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} T ⋙ stalkFunctor AddCommGrpCat.{u} (f y)).map
      (cokernel.π dA))
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} T' ⋙ stalkFunctor AddCommGrpCat.{u} y).map dB)
    ((TopCat.Sheaf.forget AddCommGrpCat.{u} T' ⋙ stalkFunctor AddCommGrpCat.{u} y).map
      (cokernel.π dB))
    (stalkMap f a y) (stalkMap f b y) (stalkMap f c y) hA hB hBex ?_ ?_ ?_ (ha y) (hb y)
  · rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  · refine ((stalkMap_precomp f dA b y).symm.trans ?_).trans (stalkMap_comp_pushforward f a dB y)
    exact congrArg (fun g => stalkMap f g y) sq₁
  · refine ((stalkMap_precomp f (cokernel.π dA) c y).symm.trans ?_).trans
      (stalkMap_comp_pushforward f b (cokernel.π dB) y)
    exact congrArg (fun g => stalkMap f g y) sq₂

variable {f}

/-- Along an inducing map, the stalk pushforward maps `(f_* B)_{f y} ⟶ B_y` are bijective. -/
lemma bijective_stalkPushforward_of_isInducing (hf : Topology.IsInducing f)
    (B : T'.Presheaf AddCommGrpCat.{u}) (y : T') :
    Function.Bijective (B.stalkPushforward AddCommGrpCat.{u} f y) :=
  have := TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u}
    hf B y
  ConcreteCategory.bijective_of_isIso _

/-- A map with bijective stalk maps lifts to a map `G(A) ⟶ f_* G(B)` bijective on the sections
over every open contained in the image of `f`, for `f` injective. -/
lemma godementLiftHom_app_bijective (hf : Function.Injective f)
    {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (hφ : ∀ y, Function.Bijective (stalkMap f φ y)) (U : Opens T)
    (hU : (U : Set T) ⊆ Set.range f) :
    Function.Bijective ((godementLiftHom f φ).hom.app (op U)) := by
  let e : (Opens.map f).obj U ≃ U := Equiv.ofBijective (fun y => ⟨f y, y.2⟩)
    ⟨fun y y' h => Subtype.ext (hf (congrArg Subtype.val h)), fun x => by
      obtain ⟨y, hy⟩ := hU x.2
      exact ⟨⟨y, show f y ∈ U from hy ▸ x.2⟩, Subtype.ext hy⟩⟩
  let P : U → Type u := fun x => A.presheaf.stalk x.1
  have key : ⇑((godementLiftHom f φ).hom.app (op U)) =
      (fun (s : ∀ y : (Opens.map f).obj U, P (e y)) (y : (Opens.map f).obj U) =>
        stalkMap f φ y.1 (s y)) ∘ (Equiv.piCongrLeft P e).symm := by
    funext s y
    rfl
  rw [key]
  exact Function.Bijective.comp ⟨fun s t h => funext fun y => (hφ y.1).1 (congrFun h y),
    fun t => ⟨fun y => Function.surjInv (hφ y.1).2 (t y),
      funext fun y => Function.surjInv_eq (hφ y.1).2 _⟩⟩ (Equiv.bijective _)

/-- For an open embedding `f`, a map `A ⟶ f_* B` bijective on sections over the opens contained
in the image of `f` has bijective stalk maps. -/
lemma stalkMap_bijective_of_app_bijective (hf : Topology.IsOpenEmbedding f)
    {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (hφ : ∀ U : Opens T, (U : Set T) ⊆ Set.range f → Function.Bijective (φ.hom.app (op U)))
    (y : T') : Function.Bijective (stalkMap f φ y) := by
  have h1 := stalkFunctor_map_bijective_of_app_bijective φ.hom ⟨Set.range f, hf.isOpen_range⟩
    hφ (f y) ⟨y, rfl⟩
  change Function.Bijective (⇑(B.presheaf.stalkPushforward AddCommGrpCat.{u} f y) ∘
    ⇑((stalkFunctor AddCommGrpCat.{u} (f y)).map φ.hom))
  exact (bijective_stalkPushforward_of_isInducing hf.isInducing B.presheaf y).comp h1

/-- For an open embedding `f`, a map `A ⟶ f_* B` with bijective stalk maps is bijective on the
sections over every open contained in the image of `f`. -/
lemma app_bijective_of_stalkMap_bijective (hf : Topology.IsOpenEmbedding f)
    {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (φ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (hφ : ∀ y, Function.Bijective (stalkMap f φ y)) (U : Opens T)
    (hU : (U : Set T) ⊆ Set.range f) : Function.Bijective (φ.hom.app (op U)) := by
  refine app_bijective_of_stalkFunctor_map_bijective φ U fun x hx => ?_
  obtain ⟨y, rfl⟩ := hU hx
  have h := hφ y
  change Function.Bijective (⇑(B.presheaf.stalkPushforward AddCommGrpCat.{u} f y) ∘
    ⇑((stalkFunctor AddCommGrpCat.{u} (f y)).map φ.hom)) at h
  exact (Function.Bijective.of_comp_iff'
    (bijective_stalkPushforward_of_isInducing hf.isInducing B.presheaf y) _).1 h

/-- The maps of stages of the Godement resolutions induced by a map with bijective stalk maps
along an open embedding have bijective stalk maps. -/
lemma stageHom_godementPullbackLift_stalkMap_bijective (hf : Topology.IsOpenEmbedding f)
    {F : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
    (φ : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B)
    (hφ : ∀ y, Function.Bijective (stalkMap f φ y)) (n : ℕ) :
    (∀ y, Function.Bijective (stalkMap f
      (CokernelCoresolution.stageHom (godementPullbackLift f) φ n).1 y)) ∧
    (∀ y, Function.Bijective (stalkMap f
      (CokernelCoresolution.stageHom (godementPullbackLift f) φ n).2.1 y)) := by
  have lift : ∀ {A : TopCat.Sheaf AddCommGrpCat.{u} T} {B : TopCat.Sheaf AddCommGrpCat.{u} T'}
      (ψ : A ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj B),
      (∀ y, Function.Bijective (stalkMap f ψ y)) →
        ∀ y, Function.Bijective (stalkMap f (godementLiftHom f ψ) y) := fun ψ hψ =>
    stalkMap_bijective_of_app_bijective hf _ fun U hU =>
      godementLiftHom_app_bijective hf.injective ψ hψ U hU
  induction n with
  | zero => exact ⟨hφ, lift φ hφ⟩
  | succ n ih =>
    refine ⟨ih.2, lift _ ?_⟩
    let p := CokernelCoresolution.stageHom (godementPullbackLift f) φ n
    exact stalkMap_cokernel_bijective f _ _ p.1 p.2.1 (CokernelCoresolution.cokerDesc p) p.2.2
      (CokernelCoresolution.π_cokerDesc p) ih.1 ih.2

/-- **The Godement resolution along an open embedding.** For an open embedding `f : T' ⟶ T`,
the comparison `G^•(F) ⟶ f_* G^•(f⁻¹ F)` is bijective on the sections over every open
`U ⊆ f(T')`. -/
theorem godementResolutionPullback_app_bijective (hf : Topology.IsOpenEmbedding f)
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) (n : ℕ) (U : Opens T)
    (hU : (U : Set T) ⊆ Set.range f) :
    Function.Bijective (((godementResolutionPullback f F).f n).hom.app (op U)) :=
  app_bijective_of_stalkMap_bijective hf _
    (stageHom_godementPullbackLift_stalkMap_bijective hf _
      (fun y => @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _
        (stalkMap f ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f).unit.app F)
          y) (isIso_stalkMap_pullbackPushforwardAdjunction_unit f F y)) n).2 U hU

end MMP.Analytic
