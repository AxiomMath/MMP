module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CompletionStalkLimit
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Stalk

/-!
# The theorem on formal functions in degree zero, normalised on germs

Let `f : X ⟶ Y` be a proper morphism with `Y` locally Noetherian, `ℱ` a coherent `𝒪_X`-module and
`y` a point of `Y`, with local ring `A = 𝒪_{Y,y}` and maximal ideal `𝔪`. Write `X_n` for the
infinitesimal neighbourhoods of the fibre and `ℱ_n` for the restrictions of `ℱ`. A section `s` of
`ℱ` over `f ⁻¹ U`, for `U` an open neighbourhood of `y`, restricts to a global section of `ℱ_n` on
`X_n`. The theorem on formal functions in degree zero says that the induced map

`((f_* ℱ)_y)^∧ ⟶ lim_n Γ(X_n, ℱ_n)`

is an isomorphism of `A`-modules.

The proof is the one of [Stacks, Tag 02OD] in degree zero. With `X' = X ×_Y Spec A`,
`ℱ'` the pullback of `ℱ` and `𝓘 = 𝔪 𝒪_{X'}`:

* degree-zero flat base change identifies `(f_* ℱ)_y` with `Γ(X', ℱ')`, compatibly with germs;
* the affine theorem on formal functions over `Spec A` identifies the completion of
  `H⁰(X', ℱ')` with the limit of `H⁰(X', ℱ'/𝓘ⁿℱ')`, compatibly with the projections;
* `ℱ'/𝓘ⁿℱ'` is the direct image of `ℱ_n` along `X_n ⟶ X'`, so its global sections are
  `Γ(X_n, ℱ_n)`; under this identification the projections are the restrictions of sections
  and the transition maps are the restrictions along `X_m ⟶ X_n`.

The last point rests on the transitivity of restriction along a tower of factorizations,
`MMP.FormalFunctions.restrictAlong_comp`.

## Main results

* `MMP.FormalFunctions.restrictAlong_comp`: restricting along `i` and then along `t` is
  restricting along `t ≫ i`.
* `MMP.FormalFunctions.restriction_formula_eq_drop`: the restriction maps of the tower
  `Γ(X_n, ℱ_n)` are the global sections of the transition morphisms of the direct images.
* `MMP.FormalFunctions.nonempty_adicCompletion_pushforwardStalk_linearEquiv_towerLimit_germ`:
  the theorem on formal functions in degree zero, normalised on germs.

## References

* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace MMP.FormalFunctions

/-! ### Restriction along a factorization -/

section Factorization

/-- Naturality of a morphism of modules, on elements. -/
theorem app_presheaf_map {W : Scheme.{u}} {M N : W.Modules} (φ : M ⟶ N) {U V : W.Opens}
    (i : U ⟶ V) (x : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

/-- A restriction map of a module along an endomorphism of an open is the identity. -/
theorem presheaf_map_endo {W : Scheme.{u}} (M : W.Modules) {U : W.Opens} (e : U ⟶ U)
    (x : Γ(M, U)) : M.presheaf.map e.op x = x := by
  rw [Subsingleton.elim e (𝟙 U), op_id, CategoryTheory.Functor.map_id]
  rfl

/-- For `a ≫ b = c`, the identification `a ^* b ^* M ≅ c ^* M`. -/
noncomputable def pullbackCompCongr {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) {c : A ⟶ C}
    (hw : a ≫ b = c) (M : C.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M) ≅
      (Scheme.Modules.pullback c).obj M :=
  (Scheme.Modules.pullbackComp a b).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M

/-- For `a ≫ b = c`, the morphism `b ^* M ⟶ a_* c ^* M` restricting a section of `b ^* M` along
`a`. -/
noncomputable def restrictAlong {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) {c : A ⟶ C}
    (hw : a ≫ b = c) (M : C.Modules) :
    (Scheme.Modules.pullback b).obj M ⟶
      (Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback c).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app ((Scheme.Modules.pullback b).obj M) ≫
    (Scheme.Modules.pushforward a).map (pullbackCompCongr a b hw M).hom

/-- Restricting along `b` and then along `a` is restricting along `c = a ≫ b`. -/
theorem unit_comp_restrictAlong {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) {c : A ⟶ C}
    (hw : a ≫ b = c) (M : C.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M ≫
        (Scheme.Modules.pushforward b).map (restrictAlong a b hw M) ≫
          (Scheme.Modules.pushforwardComp a b).hom.app ((Scheme.Modules.pullback c).obj M) ≫
            (Scheme.Modules.pushforwardCongr hw).hom.app ((Scheme.Modules.pullback c).obj M) =
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M :=
  Stacks.Algebraization.unit_comp_pushforwardSectionComparison a b hw M

/-- **Restriction along a tower of factorizations is transitive.** For `t ≫ i = k` over
`i ≫ ι = c`, restricting `ι ^* M` along `i` and then along `t` is restricting it along `k`. -/
theorem restrictAlong_comp {Z Z' W X : Scheme.{u}} (t : Z ⟶ Z') (i : Z' ⟶ W) (ι : W ⟶ X)
    {c : Z' ⟶ X} {c' : Z ⟶ X} {k : Z ⟶ W} (hn : i ≫ ι = c) (hm : t ≫ c = c')
    (hk : t ≫ i = k) (hkc : k ≫ ι = c') (M : X.Modules) :
    restrictAlong i ι hn M ≫ (Scheme.Modules.pushforward i).map (restrictAlong t c hm M) ≫
        (Scheme.Modules.pushforwardComp t i).hom.app ((Scheme.Modules.pullback c').obj M) ≫
          (Scheme.Modules.pushforwardCongr hk).hom.app ((Scheme.Modules.pullback c').obj M) =
      restrictAlong k ι hkc M := by
  subst hn hm hk
  apply ((Scheme.Modules.pullbackPushforwardAdjunction ι).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← cancel_mono ((Scheme.Modules.pushforwardComp (t ≫ i) ι).app
      ((Scheme.Modules.pullback (t ≫ i ≫ ι)).obj M) ≪≫
    (Scheme.Modules.pushforwardCongr hkc).app ((Scheme.Modules.pullback (t ≫ i ≫ ι)).obj M)).hom]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
  rw [unit_comp_restrictAlong (t ≫ i) ι hkc M, ← unit_comp_restrictAlong t (i ≫ ι) rfl M,
    ← reassoc_of% (unit_comp_restrictAlong i ι rfl M)]
  have key : ∀ φ : (Scheme.Modules.pullback (i ≫ ι)).obj M ⟶
      (Scheme.Modules.pushforward t).obj ((Scheme.Modules.pullback (t ≫ i ≫ ι)).obj M),
      (Scheme.Modules.pushforward ι).map ((Scheme.Modules.pushforward i).map φ) ≫
        (Scheme.Modules.pushforward ι).map ((Scheme.Modules.pushforwardComp t i).hom.app _) ≫
        (Scheme.Modules.pushforward ι).map ((Scheme.Modules.pushforwardCongr rfl).hom.app _) ≫
        (Scheme.Modules.pushforwardComp (t ≫ i) ι).hom.app _ ≫
        (Scheme.Modules.pushforwardCongr hkc).hom.app _ =
      (Scheme.Modules.pushforwardComp i ι).hom.app _ ≫
        (Scheme.Modules.pushforwardCongr rfl).hom.app _ ≫
        (Scheme.Modules.pushforward (i ≫ ι)).map φ ≫
        (Scheme.Modules.pushforwardComp t (i ≫ ι)).hom.app _ ≫
        (Scheme.Modules.pushforwardCongr rfl).hom.app _ := by
    intro φ
    ext V x
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
      Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
      Category.id_comp, Category.comp_id]
    erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.id_apply,
      ConcreteCategory.id_apply, ConcreteCategory.id_apply, ConcreteCategory.id_apply,
      presheaf_map_endo, presheaf_map_endo, presheaf_map_endo, presheaf_map_endo]
    rfl
  rw [key]

/-- Two successive restriction maps of a module are one restriction map. -/
theorem presheaf_map_map {W : Scheme.{u}} (M : W.Modules) {U V V' : W.Opens} (a : U ⟶ V)
    (b : V ⟶ V') (c : U ⟶ V') (x : Γ(M, V')) :
    M.presheaf.map a.op (M.presheaf.map b.op x) = M.presheaf.map c.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Subsingleton.elim (a ≫ b) c]

/-- `pullbackCompCongr` on sections, in the spelling of a composite of two morphisms. -/
theorem pullbackCompCongr_hom_app {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) {c : A ⟶ C}
    (hw : a ≫ b = c) (M : C.Modules) (U : A.Opens)
    (z : Γ((Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback b).obj M), U)) :
    (pullbackCompCongr a b hw M).hom.app U z =
      ((Scheme.Modules.pullbackComp a b).hom.app M ≫
        (Scheme.Modules.pullbackCongr hw).hom.app M).app U z :=
  rfl

/-- The pushforward of a restriction along a factorization, on global sections. -/
theorem restrictAlong_pushforward_app_top {Z Z' W X : Scheme.{u}} (t : Z ⟶ Z') (i : Z' ⟶ W)
    (c : Z' ⟶ X) {c' : Z ⟶ X} {k : Z ⟶ W} (hm : t ≫ c = c') (hk : t ≫ i = k) (M : X.Modules)
    (x : Γ((Scheme.Modules.pullback c).obj M, ⊤)) :
    ((Scheme.Modules.pushforward i).map (restrictAlong t c hm M) ≫
        (Scheme.Modules.pushforwardComp t i).hom.app ((Scheme.Modules.pullback c').obj M) ≫
          (Scheme.Modules.pushforwardCongr hk).hom.app ((Scheme.Modules.pullback c').obj M)).app ⊤
        x =
      (pullbackCompCongr t c hm M).hom.app ⊤
        (((Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback c).obj M)).presheaf.map
          (homOfLE (Stacks.FormalFunctions.top_le_preimage_top t)).op
          (((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app
            ((Scheme.Modules.pullback c).obj M)).app ⊤ x)) := by
  subst hk
  erw [app_presheaf_map, presheaf_map_endo]

/-- `Scheme.Modules.pullbackSection` as a restriction map of the abelian presheaf. -/
theorem pullbackSection_eq {A C : Scheme.{u}} (b : A ⟶ C) (M : C.Modules) (U : C.Opens)
    (V : A.Opens) (h : V ≤ b ⁻¹ᵁ U) (s : Γ(M, U)) :
    Scheme.Modules.pullbackSection b M U V h s =
      ((Scheme.Modules.pullback b).obj M).presheaf.map (homOfLE h).op
        (((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app M).app U s) :=
  rfl

/-- **Restricting the pullback of a section along a factorization.** For `a ≫ b = c` and a
section `s` of `M` over `U`, restricting the pullback of `s` along `b` further along `a` is the
pullback of `s` along `c`. -/
theorem restrictAlong_app_pullbackSection {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    {c : A ⟶ C} (hw : a ≫ b = c) (M : C.Modules) (U : C.Opens) (h₁ : ⊤ ≤ b ⁻¹ᵁ U)
    (h₂ : ⊤ ≤ c ⁻¹ᵁ U) (s : Γ(M, U)) :
    (restrictAlong a b hw M).app ⊤ (Scheme.Modules.pullbackSection b M U ⊤ h₁ s) =
      ((Scheme.Modules.pullback c).obj M).presheaf.map (homOfLE h₂).op
        (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app U s) := by
  have key := ConcreteCategory.congr_hom
    (congrArg (fun φ => Scheme.Modules.Hom.app φ U) (unit_comp_restrictAlong a b hw M)) s
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardCongr_hom_app_app]
    at key
  rw [← key]
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply]
  rw [pullbackSection_eq]
  exact (app_presheaf_map (restrictAlong a b hw M) (homOfLE h₁) _).trans
    (presheaf_map_map ((Scheme.Modules.pullback c).obj M) _ _ _ _).symm

/-- Pulling back a section and restricting it to an open is compatible with restricting the
section first. -/
theorem pullback_unit_restrict {A C : Scheme.{u}} (c : A ⟶ C) (M : C.Modules) {U W : C.Opens}
    (j : W ⟶ U) (h : ⊤ ≤ c ⁻¹ᵁ U) (h' : ⊤ ≤ c ⁻¹ᵁ W) (s : Γ(M, U)) :
    ((Scheme.Modules.pullback c).obj M).presheaf.map (homOfLE h').op
        (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app W
          (M.presheaf.map j.op s)) =
      ((Scheme.Modules.pullback c).obj M).presheaf.map (homOfLE h).op
        (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app U s) :=
  (congrArg (fun z => ((Scheme.Modules.pullback c).obj M).presheaf.map (homOfLE h').op z)
    (app_presheaf_map ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M) j s)).trans
    (presheaf_map_map ((Scheme.Modules.pullback c).obj M) _ _ _ _)

end Factorization

/-! ### Linear maps out of a stalk -/

section Stalk

/-- **Two linear maps out of the stalk of a quasi-coherent module agree as soon as they agree on
the germs of sections over one affine neighbourhood**, the stalk being a localisation of those
sections. -/
theorem linearMap_stalk_ext {Y : Scheme.{u}} (G : Y.Modules) [G.IsQuasicoherent] (y : Y)
    {U₀ : Y.Opens} (hU₀ : IsAffineOpen U₀) (hy : y ∈ U₀) {N : Type*} {_ : AddCommGroup N}
    {_ : Module (Y.presheaf.stalk y) N}
    (r r' : G.presheaf.stalk y →ₗ[Y.presheaf.stalk y] N)
    (h : ∀ a, r (G.presheaf.germ U₀ y hy a) = r' (G.presheaf.germ U₀ y hy a)) : r = r' := by
  letI := affineStalkModule G U₀ y hy
  letI : Algebra Γ(Y, U₀) (Y.presheaf.stalk y) := (Y.presheaf.germ U₀ y hy).hom.toAlgebra
  letI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU₀.isLocalization_stalk ⟨y, hy⟩
  haveI := affineGerm_isLocalized G U₀ hU₀ y hy
  ext x
  obtain ⟨⟨a, m⟩, hx⟩ := IsLocalizedModule.surj (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
    (affineGerm G U₀ y hy) x
  have hu : IsUnit ((Y.presheaf.germ U₀ y hy).hom m.1) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff
      (Y.presheaf.stalk y) (hU₀.primeIdealOf ⟨y, hy⟩).asIdeal m.1).mpr m.2
  have hx' : (Y.presheaf.germ U₀ y hy).hom m.1 • x = G.presheaf.germ U₀ y hy a := hx
  apply hu.smul_left_cancel.mp
  rw [← map_smul, ← map_smul, hx', h a]

end Stalk

/-! ### Assembling the comparison -/

section Assembly

open Stacks.IntertwinedFiltration

/-- **Transport of a normalised comparison with a tower limit.** An isomorphism
`M' ^∧ ≅ lim T` normalised by maps `π n : M' ⟶ T n`, an isomorphism of `M'` with `M`, and an
isomorphism of towers `T ≅ H` give an isomorphism `M ^∧ ≅ lim H`, normalised by the transported
maps. -/
theorem exists_adicCompletion_linearEquiv_towerLimit {A : Type*} [CommRing A] (I : Ideal A)
    {M M' : Type*} {_ : AddCommGroup M} {_ : Module A M} {_ : AddCommGroup M'}
    {_ : Module A M'} {T H : ℕ → Type*} {_ : ∀ n, AddCommGroup (T n)}
    {_ : ∀ n, Module A (T n)} {_ : ∀ n, AddCommGroup (H n)} {_ : ∀ n, Module A (H n)}
    (τ : ∀ m n, m ≤ n → T n →ₗ[A] T m) (ψ : ∀ m n, m ≤ n → H n →ₗ[A] H m)
    (e : AdicCompletion I M' ≃ₗ[A] towerLimit T τ) (π : ∀ n, M' →ₗ[A] T n)
    (he : ∀ n x, towerLimit.proj n (e (AdicCompletion.of I M' x)) = π n x)
    (θ : ∀ n, T n ≃ₗ[A] H n) (hθ : ∀ m n h x, ψ m n h (θ n x) = θ m (τ m n h x))
    (E : M' ≃ₗ[A] M) :
    ∃ Φ : AdicCompletion I M ≃ₗ[A] towerLimit H ψ,
      ∀ n x, towerLimit.proj n (Φ (AdicCompletion.of I M (E x))) = θ n (π n x) := by
  let C : AdicCompletion I M' ≃ₗ[A] AdicCompletion I M :=
    (AdicCompletion.congr I E).restrictScalars A
  refine ⟨C.symm ≪≫ₗ e ≪≫ₗ Stacks.AdicTowerComparison.towerLimitCongr T H τ ψ θ hθ,
    fun n x => ?_⟩
  have hC : C.symm (AdicCompletion.of I M (E x)) = AdicCompletion.of I M' x := by
    rw [LinearEquiv.symm_apply_eq]
    exact (AdicCompletion.map_of I E.toLinearMap x).symm
  simp only [LinearEquiv.trans_apply, hC, Stacks.AdicTowerComparison.towerLimitCongr_proj, he]

end Assembly

/-! ### The restriction maps to the infinitesimal neighbourhoods -/

section Infinitesimal

open Stacks.FormalFunctions

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (y : Y)

/-- The canonical restriction of `ℱ'` to `X_n` is `restrictAlong` for the factorization of
`X_n ⟶ X` through `X' ⟶ X`. -/
theorem infinitesimalRestriction_eq_restrictAlong [F.IsQuasicoherent] (n : ℕ) :
    infinitesimalRestriction f F y n =
      restrictAlong (infinitesimalιBaseChange f y n) (stalkBaseChangeι f y)
        (infinitesimalιBaseChange_comp_ι f y n) F := by
  have h1 := Stacks.Algebraization.idealQuotientPushforwardMap_π
    (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y)
    (infinitesimalιBaseChange f y n) (ker_infinitesimalιBaseChange f y n)
  have h2 : infinitesimalRestriction f F y n =
      (cokernel.π (C := (stalkBaseChange f y).Modules)
        (Stacks.Algebraization.idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
          (stalkBaseChangeModule f F y)).ι ≫
        Stacks.Algebraization.idealQuotientPushforwardMap
          (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y)
          (infinitesimalιBaseChange f y n) (ker_infinitesimalιBaseChange f y n)) ≫
        (Scheme.Modules.pushforward (infinitesimalιBaseChange f y n)).map
          (infinitesimalModulePullbackIso f F y n).hom := by
    rw [infinitesimalRestriction, infinitesimalPushforwardIso, Iso.trans_hom,
      Stacks.Algebraization.idealQuotientPushforwardIso_hom, Functor.mapIso_hom, Category.assoc]
  have h3 : infinitesimalModulePullbackIso f F y n =
      pullbackCompCongr (infinitesimalιBaseChange f y n) (stalkBaseChangeι f y)
        (infinitesimalιBaseChange_comp_ι f y n) F := rfl
  rw [h2, h1, h3]
  rfl

/-- For `m ≤ n`, the transition morphism between the direct images to `X'` of `ℱ_n` and `ℱ_m` is
the direct image of `restrictAlong` for the factorization of `X_m ⟶ X` through `X_n`. -/
theorem infinitesimalPushforwardDrop_eq [F.IsQuasicoherent] {m n : ℕ} (h : m ≤ n) :
    infinitesimalPushforwardDrop f F y h =
      (Scheme.Modules.pushforward (infinitesimalιBaseChange f y n)).map
          (restrictAlong (infinitesimalTransition f y h) (infinitesimalι f y n)
            (infinitesimalTransition_ι f y h) F) ≫
        (Scheme.Modules.pushforwardComp (infinitesimalTransition f y h)
          (infinitesimalιBaseChange f y n)).hom.app (infinitesimalModule f F y m) ≫
        (Scheme.Modules.pushforwardCongr
          (infinitesimalTransition_comp_ιBaseChange f y h)).hom.app
            (infinitesimalModule f F y m) := by
  haveI : Epi (infinitesimalRestriction f F y n) := by
    rw [infinitesimalRestriction]
    infer_instance
  rw [← cancel_epi (infinitesimalRestriction f F y n), infinitesimalRestriction_comp_drop,
    infinitesimalRestriction_eq_restrictAlong, infinitesimalRestriction_eq_restrictAlong]
  exact (restrictAlong_comp _ _ _ _ _ _ _ F).symm

/-- **The transition map on global sections**, in the spelling of the restriction along the
transition morphism `X_m ⟶ X_n`. -/
theorem infinitesimalPushforwardDrop_app_top [F.IsQuasicoherent] {m n : ℕ} (h : m ≤ n)
    (x : Γ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F, ⊤)) :
    (infinitesimalPushforwardDrop f F y h).app ⊤ x =
      (pullbackCompCongr (infinitesimalTransition f y h) (infinitesimalι f y n)
          (infinitesimalTransition_ι f y h) F).hom.app ⊤
        (((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
            ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F)).presheaf.map
          (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op
          (((Scheme.Modules.pullbackPushforwardAdjunction
            (infinitesimalTransition f y h)).unit.app
              ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F)).app ⊤ x)) := by
  rw [infinitesimalPushforwardDrop_eq]
  exact restrictAlong_pushforward_app_top (infinitesimalTransition f y h)
    (infinitesimalιBaseChange f y n) (infinitesimalι f y n) (infinitesimalTransition_ι f y h)
    (infinitesimalTransition_comp_ιBaseChange f y h) F x

/-- The restriction formula, from the spelling with `infinitesimalModule` to the spelling with
the pullback it abbreviates. -/
theorem restriction_formula_eq_pullback {m n : ℕ} (h : m ≤ n) (x : Γ(infinitesimalModule f F y n, ⊤)) :
    ((Scheme.Modules.pullbackComp (infinitesimalTransition f y h)
          (infinitesimalι f y n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f y h)).hom.app F).app ⊤
      ((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
          (infinitesimalModule f F y n) |>.presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (infinitesimalTransition f y h)).unit.app (infinitesimalModule f F y n)).app ⊤
            x)) =
    ((Scheme.Modules.pullbackComp (infinitesimalTransition f y h)
          (infinitesimalι f y n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f y h)).hom.app F).app ⊤
      ((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
          ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F) |>.presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (infinitesimalTransition f y h)).unit.app ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F)).app ⊤
            x)) := by
  have e1 : ((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalTransition f y h)).unit.app
        (infinitesimalModule f F y n)).app ⊤ x =
      ((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalTransition f y h)).unit.app
        ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F)).app ⊤ x := rfl
  have e2 : ∀ z, ((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
          (infinitesimalModule f F y n)).presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op z =
      ((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
          ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F)).presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op z := fun z => rfl
  exact (congrArg (fun w => ((Scheme.Modules.pullbackComp (infinitesimalTransition f y h)
          (infinitesimalι f y n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f y h)).hom.app F).app ⊤
      (((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
          (infinitesimalModule f F y n)).presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op w)) e1).trans
    (congrArg (fun w => ((Scheme.Modules.pullbackComp (infinitesimalTransition f y h)
          (infinitesimalι f y n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f y h)).hom.app F).app ⊤ w)
      (e2 _))

/-- The transition maps of the theorem on formal functions in degree zero, in the spelling of
its statement, are `infinitesimalPushforwardDrop` on global sections. -/
theorem restriction_formula_eq_drop [F.IsQuasicoherent] {m n : ℕ} (h : m ≤ n)
    (x : Γ(infinitesimalModule f F y n, ⊤)) :
    ((Scheme.Modules.pullbackComp (infinitesimalTransition f y h)
          (infinitesimalι f y n)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f y h)).hom.app F).app ⊤
      ((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
          (infinitesimalModule f F y n) |>.presheaf.map
        (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (infinitesimalTransition f y h)).unit.app (infinitesimalModule f F y n)).app ⊤
            x)) =
      (infinitesimalPushforwardDrop f F y h).app ⊤ x :=
  (restriction_formula_eq_pullback f F y h x).trans
    ((infinitesimalPushforwardDrop_app_top f F y h x).trans
      (pullbackCompCongr_hom_app _ _ _ F ⊤ _)).symm

/-- Restricting a section of `ℱ_n`, in the two spellings of `ℱ_n`. -/
theorem presheaf_map_congr_module (n : ℕ) {U : (infinitesimalNeighbourhood f y n).Opens}
    (j : (⊤ : (infinitesimalNeighbourhood f y n).Opens) ⟶ U)
    (z : Γ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F, U)) :
    ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F).presheaf.map j.op z =
      (infinitesimalModule f F y n).presheaf.map j.op z :=
  rfl

/-- The pullback of a section to the base change, over the preimage of `⊤` and over `⊤`. -/
theorem pullbackSection_structure_top_eq (U : Y.Opens) (hy : y ∈ U) (s : Γ(F, f ⁻¹ᵁ U)) :
    (Scheme.Modules.pullbackSection (stalkBaseChangeι f y) F (f ⁻¹ᵁ U)
          ((stalkBaseChangeStructure f y) ⁻¹ᵁ ⊤) (top_le_preimage_pullbackFst f y U hy) s :
        Γ(stalkBaseChangeModule f F y, ⊤)) =
      Scheme.Modules.pullbackSection (stalkBaseChangeι f y) F (f ⁻¹ᵁ U)
          ⊤ (top_le_preimage_pullbackFst f y U hy) s :=
  rfl

/-- The canonical restriction to `X_n`, applied to the pullback to `X'` of a section `s` of `ℱ`
over `f ⁻¹ U`, is the restriction to `⊤` of the image of `s` in the pullback of `ℱ` to `X_n`. -/
theorem infinitesimalRestriction_app_pullbackSection_eq_pullback_map [F.IsQuasicoherent] (n : ℕ)
    (U : Y.Opens) (hy : y ∈ U) (s : Γ(F, f ⁻¹ᵁ U)) :
    (infinitesimalRestriction f F y n).app ⊤
        (Scheme.Modules.pullbackSection (stalkBaseChangeι f y) F (f ⁻¹ᵁ U)
          ⊤ (top_le_preimage_pullbackFst f y U hy) s) =
      ((Scheme.Modules.pullback (infinitesimalι f y n)).obj F).presheaf.map
        (homOfLE (top_le_preimage_infinitesimalι f y n U hy)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f y n)).unit.app F).app
          (f ⁻¹ᵁ U) s) := by
  rw [infinitesimalRestriction_eq_restrictAlong]
  exact restrictAlong_app_pullbackSection _ _ (infinitesimalιBaseChange_comp_ι f y n) F
    (f ⁻¹ᵁ U) (top_le_preimage_pullbackFst f y U hy) (top_le_preimage_infinitesimalι f y n U hy) s

end Infinitesimal

/-! ### Degree zero: the tower of global sections -/

section Tower

open Stacks.FormalFunctions Stacks.Cohomology.FormalFunctions Stacks.Algebraization

/-- A commutative square of modules, after restricting scalars, on elements. -/
theorem restrictScalars_map_square {A R : Type u} [CommRing A] [CommRing R] (ρ : A →+* R)
    {P P' Q Q' : ModuleCat.{u} R} {d : P ⟶ P'} {q' : P' ⟶ Q'} {q : P ⟶ Q} {D : Q ⟶ Q'}
    (hsq : d ≫ q' = q ≫ D) (x : (ModuleCat.restrictScalars ρ).obj P) :
    ((ModuleCat.restrictScalars ρ).map q').hom (((ModuleCat.restrictScalars ρ).map d).hom x) =
      ((ModuleCat.restrictScalars ρ).map D).hom (((ModuleCat.restrictScalars ρ).map q).hom x) :=
  ConcreteCategory.congr_hom hsq x

/-- The global sections of a direct image `i_* G`, with scalars restricted along `α`, are the
global sections of `G` with scalars acting through `β`, for `i.appTop ∘ α = β`. -/
noncomputable def pushforwardSectionsEquiv {A : Type u} [CommRing A] {Z W : Scheme.{u}}
    (i : Z ⟶ W) (G : Z.Modules) (α : A →+* Γ(W, ⊤)) (β : A →+* Γ(Z, ⊤))
    (h : ∀ a, i.appTop.hom (α a) = β a) :
    letI := Module.compHom Γ(G, ⊤) β
    (ModuleCat.restrictScalars α).obj ((Stacks.Cohomology.AffineBase.moduleGlobalSections W).obj
        ((Scheme.Modules.pushforward i).obj G)) ≃ₗ[A] Γ(G, ⊤) :=
  letI := Module.compHom Γ(G, ⊤) β
  { toFun := fun x => x
    map_add' := fun _ _ => rfl
    map_smul' := fun a x => by
      change (i.appTop.hom (α a)) • (show Γ(G, ⊤) from x) = β a • (show Γ(G, ⊤) from x)
      rw [h]
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Composing `Iso.toLinearEquiv` of an isomorphism `q` with `pushforwardSectionsEquiv` sends `x`
to `pushforwardSectionsEquiv` of `q.hom x`. -/
theorem toLinearEquiv_trans_pushforwardSectionsEquiv_apply {A : Type u} [CommRing A]
    {Z W : Scheme.{u}} (i : Z ⟶ W) (G : Z.Modules) (α : A →+* Γ(W, ⊤)) (β : A →+* Γ(Z, ⊤))
    (h : ∀ a, i.appTop.hom (α a) = β a) {P : ModuleCat.{u} Γ(W, ⊤)}
    (q : P ≅ (Stacks.Cohomology.AffineBase.moduleGlobalSections W).obj
      ((Scheme.Modules.pushforward i).obj G)) (x : (ModuleCat.restrictScalars α).obj P) :
    letI := Module.compHom Γ(G, ⊤) β
    (((ModuleCat.restrictScalars α).mapIso q).toLinearEquiv.trans
        (pushforwardSectionsEquiv i G α β h)) x =
      pushforwardSectionsEquiv i G α β h (((ModuleCat.restrictScalars α).map q.hom).hom x) :=
  rfl

/-- `pushforwardSectionsEquiv` intertwines a morphism of direct images with its global
sections. -/
theorem pushforwardSectionsEquiv_map {A : Type u} [CommRing A] {Z Z' W : Scheme.{u}}
    (i : Z ⟶ W) (i' : Z' ⟶ W) (G : Z.Modules) (G' : Z'.Modules) (α : A →+* Γ(W, ⊤))
    (β : A →+* Γ(Z, ⊤)) (β' : A →+* Γ(Z', ⊤)) (h : ∀ a, i.appTop.hom (α a) = β a)
    (h' : ∀ a, i'.appTop.hom (α a) = β' a)
    (D : (Scheme.Modules.pushforward i).obj G ⟶ (Scheme.Modules.pushforward i').obj G')
    (z : (ModuleCat.restrictScalars α).obj ((Stacks.Cohomology.AffineBase.moduleGlobalSections
      W).obj ((Scheme.Modules.pushforward i).obj G))) :
    letI := Module.compHom Γ(G, ⊤) β
    letI := Module.compHom Γ(G', ⊤) β'
    pushforwardSectionsEquiv i' G' α β' h'
        (((ModuleCat.restrictScalars α).map
          ((Stacks.Cohomology.AffineBase.moduleGlobalSections W).map D)).hom z) =
      D.app ⊤ (pushforwardSectionsEquiv i G α β h z) :=
  rfl

/-- `pushforwardSectionsEquiv` turns the global sections of a morphism into a direct image into
the morphism on global sections. -/
theorem pushforwardSectionsEquiv_map_of {A : Type u} [CommRing A] {Z W : Scheme.{u}}
    (i : Z ⟶ W) (G : Z.Modules) (M : W.Modules) (α : A →+* Γ(W, ⊤))
    (β : A →+* Γ(Z, ⊤)) (h : ∀ a, i.appTop.hom (α a) = β a)
    (ρ : M ⟶ (Scheme.Modules.pushforward i).obj G)
    (z : (ModuleCat.restrictScalars α).obj
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections W).obj M)) :
    letI := Module.compHom Γ(G, ⊤) β
    pushforwardSectionsEquiv i G α β h
        (((ModuleCat.restrictScalars α).map
          ((Stacks.Cohomology.AffineBase.moduleGlobalSections W).map ρ)).hom z) =
      ρ.app ⊤ (show Γ(M, ⊤) from z) :=
  rfl

/-- Degree-zero cohomology is global sections. -/
noncomputable def h0Sections (W : Scheme.{u}) (G : W.Modules) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections W).rightDerived 0).obj G ≅
      (Stacks.Cohomology.AffineBase.moduleGlobalSections W).obj G :=
  (moduleGlobalSectionsRightDerivedZeroIso W).app G

/-- The isomorphism `h0Sections` is natural in the module. -/
theorem h0Sections_naturality {W : Scheme.{u}} {G G' : W.Modules} (φ : G ⟶ G') :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections W).rightDerived 0).map φ ≫
        (h0Sections W G').hom =
      (h0Sections W G).hom ≫ (Stacks.Cohomology.AffineBase.moduleGlobalSections W).map φ :=
  (moduleGlobalSectionsRightDerivedZeroIso W).hom.naturality φ

/-- The global sections of a direct image to `Spec R` are the degree-zero cohomology upstairs, as
`R`-modules. -/
noncomputable def sectionsCohomologyZeroEquiv (R : CommRingCat.{u}) {W : Scheme.{u}}
    (g : W ⟶ Spec R) (G : W.Modules) :
    letI := Module.compHom Γ((Scheme.Modules.pushforward g).obj G, ⊤) (Scheme.ΓSpecIso R).inv.hom
    Γ((Scheme.Modules.pushforward g).obj G, ⊤) ≃ₗ[R]
      (ModuleCat.restrictScalars (@baseRingHom R inferInstance _ g)).obj
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections W).rightDerived 0).obj G) :=
  letI := Module.compHom Γ((Scheme.Modules.pushforward g).obj G, ⊤) (Scheme.ΓSpecIso R).inv.hom
  ({ toFun := fun x => x
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl
     invFun := fun x => x
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
      Γ((Scheme.Modules.pushforward g).obj G, ⊤) ≃ₗ[R]
        (ModuleCat.restrictScalars (@baseRingHom R inferInstance _ g)).obj
          ((Stacks.Cohomology.AffineBase.moduleGlobalSections W).obj G)).trans
    ((ModuleCat.restrictScalars (@baseRingHom R inferInstance _ g)).mapIso
      (h0Sections W G).symm).toLinearEquiv

/-- `h0Sections` sends `sectionsCohomologyZeroEquiv w` back to `w`. -/
theorem h0Sections_hom_sectionsCohomologyZeroEquiv (R : CommRingCat.{u}) {W : Scheme.{u}}
    (g : W ⟶ Spec R) (G : W.Modules) (w : Γ((Scheme.Modules.pushforward g).obj G, ⊤)) :
    letI := Module.compHom Γ((Scheme.Modules.pushforward g).obj G, ⊤) (Scheme.ΓSpecIso R).inv.hom
    ((ModuleCat.restrictScalars (@baseRingHom R inferInstance _ g)).map
        (h0Sections W G).hom).hom
      (sectionsCohomologyZeroEquiv R g G w) = w :=
  ConcreteCategory.congr_hom
    ((ModuleCat.restrictScalars (@baseRingHom R inferInstance _ g)).mapIso
      (h0Sections W G)).inv_hom_id w

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (y : Y) [F.IsQuasicoherent]

/-- `H⁰(X', ℱ' / 𝓘 ⁿ ℱ') ≅ Γ(X', (i_n)_* ℱ_n)`, over `Γ(X', 𝒪)`. -/
noncomputable def quotientSectionsIso (n : ℕ) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj
        (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y)) ≅
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).obj
        ((Scheme.Modules.pushforward (infinitesimalιBaseChange f y n)).obj
          (infinitesimalModule f F y n)) :=
  h0Sections (stalkBaseChange f y) _ ≪≫
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).mapIso
      (infinitesimalPushforwardIso f F y n)

/-- The projection of the affine tower, carried to `Γ(X', (i_n)_* ℱ_n)`, is the canonical
restriction. -/
theorem quotientSectionsIso_proj (n : ℕ) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
        (cokernel.π (C := (stalkBaseChange f y).Modules)
          (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
            (stalkBaseChangeModule f F y)).ι) ≫ (quotientSectionsIso f F y n).hom =
      (h0Sections (stalkBaseChange f y) (stalkBaseChangeModule f F y)).hom ≫
        (Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).map
          (infinitesimalRestriction f F y n) := by
  rw [quotientSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    ← Category.assoc, h0Sections_naturality, Category.assoc, ← Functor.map_comp,
    infinitesimalRestriction]

/-- The transition of the affine tower, carried to `Γ(X', (i_n)_* ℱ_n)`, is
`infinitesimalPushforwardDrop`. -/
theorem quotientSectionsIso_drop {m n : ℕ} (h : m ≤ n) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
        (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
          (stalkBaseChangeModule f F y)) ≫ (quotientSectionsIso f F y m).hom =
      (quotientSectionsIso f F y n).hom ≫
        (Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).map
          (infinitesimalPushforwardDrop f F y h) := by
  rw [quotientSectionsIso, quotientSectionsIso, Iso.trans_hom, Iso.trans_hom,
    Functor.mapIso_hom, Functor.mapIso_hom, infinitesimalPushforwardDrop,
    ← Category.assoc, h0Sections_naturality, Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    Iso.hom_inv_id_assoc]

/-- The transition of the affine tower, carried to `Γ(X', (i_n)_* ℱ_n)`, on elements. -/
theorem quotientSectionsIso_drop_apply {m n : ℕ} (h : m ≤ n)
    (x : (ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).obj
      (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n
        (stalkBaseChangeModule f F y)))) :
    ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _
        (stalkBaseChangeStructure f y))).map (quotientSectionsIso f F y m).hom).hom
      (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
        (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
          (stalkBaseChangeModule f F y)))).hom x) =
    ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _
        (stalkBaseChangeStructure f y))).map
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).map
        (infinitesimalPushforwardDrop f F y h))).hom
      (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _
        (stalkBaseChangeStructure f y))).map (quotientSectionsIso f F y n).hom).hom x) :=
  restrictScalars_map_square _ (quotientSectionsIso_drop f F y h) x

/-- The projection of the affine tower, carried to `Γ(X', (i_n)_* ℱ_n)`, on elements. -/
theorem quotientSectionsIso_proj_apply (n : ℕ)
    (x : (ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).obj (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj (stalkBaseChangeModule f F y))) :
    ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _
        (stalkBaseChangeStructure f y))).map (quotientSectionsIso f F y n).hom).hom
      (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
        (cokernel.π (C := (stalkBaseChange f y).Modules)
          (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
            (stalkBaseChangeModule f F y)).ι))).hom x) =
    ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _
        (stalkBaseChangeStructure f y))).map
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).map
        (infinitesimalRestriction f F y n))).hom
      (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _
        (stalkBaseChangeStructure f y))).map
          (h0Sections (stalkBaseChange f y) (stalkBaseChangeModule f F y)).hom).hom x) :=
  restrictScalars_map_square _ (quotientSectionsIso_proj f F y n) x

end Tower

open Stacks.FormalFunctions Stacks.Cohomology.FormalFunctions in
/-- `appTop_infinitesimalιBaseChange_baseRingHom`, with the canonical `CommRing` instance on the
stalk. -/
theorem appTop_baseRingHom_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ)
    (a : Y.presheaf.stalk y) :
    (infinitesimalιBaseChange f y n).appTop.hom
        (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y) a) =
      infinitesimalBaseRingHom f y n a :=
  appTop_infinitesimalιBaseChange_baseRingHom f y n a

open Stacks.FormalFunctions Stacks.Cohomology.FormalFunctions Stacks.Algebraization in
/-- The degree-zero comparison on an element of `Γ(X', ℱ')`, carried to `X_n`. -/
theorem towerSections_sectionsCohomologyZeroEquiv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [F.IsQuasicoherent] (y : Y) (n : ℕ)
    (w : Γ((Scheme.Modules.pushforward (stalkBaseChangeStructure f y)).obj
      (stalkBaseChangeModule f F y), ⊤)) :
    (pushforwardSectionsEquiv (infinitesimalιBaseChange f y n) (infinitesimalModule f F y n)
      (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y)) (infinitesimalBaseRingHom f y n) (appTop_baseRingHom_eq f y n))
      (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (quotientSectionsIso f F y n).hom).hom
        (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
          (cokernel.π (C := (stalkBaseChange f y).Modules)
            (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
              (stalkBaseChangeModule f F y)).ι))).hom
          (sectionsCohomologyZeroEquiv (Y.presheaf.stalk y) (stalkBaseChangeStructure f y)
            (stalkBaseChangeModule f F y) w))) =
      (infinitesimalRestriction f F y n).app ⊤ w :=
  (congrArg (pushforwardSectionsEquiv (infinitesimalιBaseChange f y n) (infinitesimalModule f F y n)
      (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y)) (infinitesimalBaseRingHom f y n) (appTop_baseRingHom_eq f y n)) (quotientSectionsIso_proj_apply f F y n _)).trans
    ((pushforwardSectionsEquiv_map_of (infinitesimalιBaseChange f y n)
      (infinitesimalModule f F y n) (stalkBaseChangeModule f F y) (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))
      (infinitesimalBaseRingHom f y n) (appTop_baseRingHom_eq f y n)
      (infinitesimalRestriction f F y n) _).trans
      (congrArg (fun z => (infinitesimalRestriction f F y n).app ⊤ z)
        (h0Sections_hom_sectionsCohomologyZeroEquiv (Y.presheaf.stalk y)
          (stalkBaseChangeStructure f y) (stalkBaseChangeModule f F y) w)))

open Stacks.FormalFunctions Stacks.Cohomology.FormalFunctions Stacks.Algebraization in
/-- The canonical restriction of the pullback of a section, over the preimage of `⊤`. -/
theorem infinitesimalRestriction_app_pullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) [F.IsQuasicoherent] (y : Y) (n : ℕ) (W : Y.Opens) (hyW : y ∈ W)
    (a : Γ(F, f ⁻¹ᵁ W)) :
    (infinitesimalRestriction f F y n).app ⊤
        (Scheme.Modules.pullbackSection (stalkBaseChangeι f y) F (f ⁻¹ᵁ W)
          ((stalkBaseChangeStructure f y) ⁻¹ᵁ ⊤) (top_le_preimage_pullbackFst f y W hyW) a) =
      (infinitesimalModule f F y n).presheaf.map
        (homOfLE (top_le_preimage_infinitesimalι f y n W hyW)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f y n)).unit.app F).app
          (f ⁻¹ᵁ W) a) :=
  (congrArg (fun z => (infinitesimalRestriction f F y n).app ⊤ z)
    (pullbackSection_structure_top_eq f F y W hyW a)).trans
    ((infinitesimalRestriction_app_pullbackSection_eq_pullback_map f F y n W hyW a).trans
      (presheaf_map_congr_module f F y n _ _))

open Stacks.FormalFunctions Stacks.Cohomology.FormalFunctions Stacks.Algebraization in
/-- The normalisation of the degree-zero comparison on the pullback of a section. -/
theorem towerSections_pullbackSection {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] (y : Y) (n : ℕ) (W : Y.Opens) (hyW : y ∈ W)
    (a : Γ(F, f ⁻¹ᵁ W)) :
    (pushforwardSectionsEquiv (infinitesimalιBaseChange f y n) (infinitesimalModule f F y n)
      (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y)) (infinitesimalBaseRingHom f y n) (appTop_baseRingHom_eq f y n))
      (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (quotientSectionsIso f F y n).hom).hom
        (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
          (cokernel.π (C := (stalkBaseChange f y).Modules)
            (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
              (stalkBaseChangeModule f F y)).ι))).hom
          (sectionsCohomologyZeroEquiv (Y.presheaf.stalk y) (stalkBaseChangeStructure f y)
            (stalkBaseChangeModule f F y)
            (Scheme.Modules.pullbackSection (stalkBaseChangeι f y) F (f ⁻¹ᵁ W)
              ((stalkBaseChangeStructure f y) ⁻¹ᵁ ⊤) (top_le_preimage_pullbackFst f y W hyW)
              a)))) =
      (infinitesimalModule f F y n).presheaf.map
        (homOfLE (top_le_preimage_infinitesimalι f y n W hyW)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f y n)).unit.app F).app
          (f ⁻¹ᵁ W) a) :=
  (towerSections_sectionsCohomologyZeroEquiv f F y n _).trans
    (infinitesimalRestriction_app_pullbackSection f F y n W hyW a)

open Stacks.FormalFunctions in
/-- The restriction of a section to `X_n` does not change when the section is first restricted to
a smaller neighbourhood of `y`. -/
theorem infinitesimalModule_map_unit_app_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (y : Y) (n : ℕ) {U V : Y.Opens} (hVU : V ≤ U) (hyV : y ∈ V) (s : Γ(F, f ⁻¹ᵁ U)) :
    (infinitesimalModule f F y n).presheaf.map
        (homOfLE (top_le_preimage_infinitesimalι f y n V hyV)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f y n)).unit.app F).app
          (f ⁻¹ᵁ V) (((Scheme.Modules.pushforward f).obj F).presheaf.map (homOfLE hVU).op s)) =
      (infinitesimalModule f F y n).presheaf.map
        (homOfLE (top_le_preimage_infinitesimalι f y n U (hVU hyV))).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f y n)).unit.app F).app
          (f ⁻¹ᵁ U) s) :=
  ((presheaf_map_congr_module f F y n _ _).symm.trans
    (pullback_unit_restrict (infinitesimalι f y n) F ((TopologicalSpace.Opens.map f.base).map
      (homOfLE hVU)) _ _ s)).trans (presheaf_map_congr_module f F y n _ _)

/-! ### The theorem on formal functions in degree zero -/

section Main

open Stacks.FormalFunctions Stacks.Cohomology.FormalFunctions Stacks.Algebraization
  Stacks.IntertwinedFiltration

/-- The comparison of the theorem on formal functions in degree zero, normalised on the germs of
sections over one affine neighbourhood `W` of `y`. -/
theorem exists_linearEquiv_towerLimit_germ_of_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [IsProper f] (F : X.Modules) [F.IsCoherent] (y : Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hyW : y ∈ W) :
    letI H : ℕ → Type u := fun n => Γ(infinitesimalModule f F y n, ⊤)
    letI : ∀ n, Module (Y.presheaf.stalk y) (H n) := fun n =>
      Module.compHom _ (infinitesimalBaseRingHom f y n)
    letI res : ∀ (n : ℕ) (U : Y.Opens), y ∈ U → Γ(F, f ⁻¹ᵁ U) → H n := fun n U hy s =>
      (infinitesimalModule f F y n).presheaf.map
        (homOfLE (top_le_preimage_infinitesimalι f y n U hy)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f y n)).unit.app F).app
          (f ⁻¹ᵁ U) s)
    ∀ (ψ : ∀ m n, m ≤ n → H n →ₗ[Y.presheaf.stalk y] H m),
      (∀ m n (h : m ≤ n) (x : H n), ψ m n h x =
        ((Scheme.Modules.pullbackComp (infinitesimalTransition f y h)
              (infinitesimalι f y n)).hom.app F ≫
            (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f y h)).hom.app F).app ⊤
          ((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
              (infinitesimalModule f F y n) |>.presheaf.map
            (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op
            (((Scheme.Modules.pullbackPushforwardAdjunction
              (infinitesimalTransition f y h)).unit.app (infinitesimalModule f F y n)).app ⊤
                x))) →
      ∃ Φ : AdicCompletion (stalkMaximalIdeal y)
          (((Scheme.Modules.pushforward f).obj F).presheaf.stalk y) ≃ₗ[Y.presheaf.stalk y]
            towerLimit H ψ,
        ∀ n (a : Γ(F, f ⁻¹ᵁ W)),
          towerLimit.proj n (Φ (AdicCompletion.of _ _
            (((Scheme.Modules.pushforward f).obj F).presheaf.germ W y hyW a))) =
            res n W hyW a := by
  intro ψ hψ
  have hA : IsNoetherianRing ↥(Y.presheaf.stalk y) := inferInstance
  have : (stalkBaseChangeModule f F y).IsCoherent := isCoherent_pullback _ F
  have hcoh : Stacks.SheafOfModules.IsCoherent (stalkBaseChangeModule f F y) :=
    Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent inferInstance
  obtain ⟨-, e₂, he₂⟩ : ∃ _ : ℕ, ∃ e : AdicCompletion (stalkMaximalIdeal y)
        ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).obj (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj (stalkBaseChangeModule f F y))) ≃ₗ[
          Y.presheaf.stalk y]
        towerLimit (fun n => ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).obj (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj
            (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n
              (stalkBaseChangeModule f F y))) : Type u))
          (fun m n h => ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
            (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
              (stalkBaseChangeModule f F y)))).hom),
      ∀ (n : ℕ) (x : (ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).obj (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj
          (stalkBaseChangeModule f F y))),
        towerLimit.proj n (e (AdicCompletion.of _ _ x)) =
          ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
            (cokernel.π (C := (stalkBaseChange f y).Modules)
              (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
                (stalkBaseChangeModule f F y)).ι))).hom x :=
    @exists_formalFunctionsEquiv_of_02O8 ↥(Y.presheaf.stalk y) inferInstance hA _
      (stalkBaseChangeStructure f y) inferInstance (stalkMaximalIdeal y)
      (stalkBaseChangeModule f F y) hcoh 0 isReesFinite_cohomologyIdealPowerSystem
  letI : Module (Y.presheaf.stalk y)
      Γ((Scheme.Modules.pushforward (stalkBaseChangeStructure f y)).obj
        (stalkBaseChangeModule f F y), ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
  obtain ⟨e₁, he₁⟩ :
      ∃ e : Γ((Scheme.Modules.pushforward (stalkBaseChangeStructure f y)).obj (stalkBaseChangeModule f F y), ⊤) ≃ₗ[(Y.presheaf.stalk y)] ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y,
        ∀ a : Γ((Scheme.Modules.pushforward f).obj F, W),
          e (Scheme.Modules.pullbackSection (stalkBaseChangeι f y) F (f ⁻¹ᵁ W)
            ((stalkBaseChangeStructure f y) ⁻¹ᵁ ⊤) (top_le_preimage_pullbackFst f y W hyW) a) =
            ((Scheme.Modules.pushforward f).obj F).presheaf.germ W y hyW a :=
    Stacks.AlgebraicGeometry.FlatBaseChange.exists_linearEquiv_pushforwardStalk_stalkBaseChange
      f F y hW hyW
  obtain ⟨θ, hθdef⟩ : ∃ θ : (∀ n,
      letI := Module.compHom Γ(infinitesimalModule f F y n, ⊤) (infinitesimalBaseRingHom f y n)
      (ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).obj (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y))) ≃ₗ[(Y.presheaf.stalk y)]
        Γ(infinitesimalModule f F y n, ⊤)),
      ∀ n (z : (ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).obj (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj (idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n (stalkBaseChangeModule f F y)))),
        θ n z = (pushforwardSectionsEquiv (infinitesimalιBaseChange f y n) (infinitesimalModule f F y n)
          (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y)) (infinitesimalBaseRingHom f y n)
          (appTop_baseRingHom_eq f y n))
          (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (quotientSectionsIso f F y n).hom).hom z) :=
    ⟨fun n => ((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).mapIso
        (quotientSectionsIso f F y n)).toLinearEquiv.trans (pushforwardSectionsEquiv (infinitesimalιBaseChange f y n) (infinitesimalModule f F y n)
          (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y)) (infinitesimalBaseRingHom f y n)
          (appTop_baseRingHom_eq f y n)),
      fun n z => toLinearEquiv_trans_pushforwardSectionsEquiv_apply _ _ _ _ _ _ z⟩
  have hθ : ∀ m n (h : m ≤ n) x, ψ m n h (θ n x) = θ m
      (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
        (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h (stalkBaseChangeModule f F y)))).hom x) := by
    intro m n h x
    rw [hθdef, hθdef]
    exact ((hψ m n h _).trans (restriction_formula_eq_drop f F y h _)).trans
      ((pushforwardSectionsEquiv_map (infinitesimalιBaseChange f y n)
        (infinitesimalιBaseChange f y m) (infinitesimalModule f F y n)
        (infinitesimalModule f F y m) (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y)) (infinitesimalBaseRingHom f y n)
        (infinitesimalBaseRingHom f y m)
        (appTop_baseRingHom_eq f y n)
        (appTop_baseRingHom_eq f y m) (infinitesimalPushforwardDrop f F y h)
        _).symm.trans
        (congrArg (pushforwardSectionsEquiv (infinitesimalιBaseChange f y m) (infinitesimalModule f F y m)
          (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y)) (infinitesimalBaseRingHom f y m)
          (appTop_baseRingHom_eq f y m))
          (quotientSectionsIso_drop_apply f F y h x).symm))
  obtain ⟨E, hE⟩ : ∃ E : (ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).obj (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).obj (stalkBaseChangeModule f F y)) ≃ₗ[(Y.presheaf.stalk y)] ((Scheme.Modules.pushforward f).obj F).presheaf.stalk y,
      ∀ a : Γ((Scheme.Modules.pushforward f).obj F, W),
        E.symm (((Scheme.Modules.pushforward f).obj F).presheaf.germ W y hyW a) =
          sectionsCohomologyZeroEquiv (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) (stalkBaseChangeModule f F y) (Scheme.Modules.pullbackSection (stalkBaseChangeι f y) F (f ⁻¹ᵁ W)
            ((stalkBaseChangeStructure f y) ⁻¹ᵁ ⊤) (top_le_preimage_pullbackFst f y W hyW) a) :=
    ⟨(sectionsCohomologyZeroEquiv (Y.presheaf.stalk y) (stalkBaseChangeStructure f y) (stalkBaseChangeModule f F y)).symm.trans e₁, fun a => by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
      congr 1
      exact (LinearEquiv.symm_apply_eq e₁).mpr (he₁ a).symm⟩
  obtain ⟨Φ, hΦ⟩ := exists_adicCompletion_linearEquiv_towerLimit (stalkMaximalIdeal y) _ ψ e₂ _ he₂ θ hθ E
  have key : ∀ n (a : Γ(F, f ⁻¹ᵁ W)), θ n (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
          (cokernel.π (C := (stalkBaseChange f y).Modules)
            (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
              (stalkBaseChangeModule f F y)).ι))).hom (E.symm (((Scheme.Modules.pushforward f).obj F).presheaf.germ W y hyW a))) =
      (infinitesimalModule f F y n).presheaf.map
        (homOfLE (top_le_preimage_infinitesimalι f y n W hyW)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f y n)).unit.app F).app
          (f ⁻¹ᵁ W) a) := by
    intro n a
    refine (hθdef n _).trans ?_
    refine (congrArg (fun x => (pushforwardSectionsEquiv (infinitesimalιBaseChange f y n)
        (infinitesimalModule f F y n) (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y)) (infinitesimalBaseRingHom f y n)
        (appTop_baseRingHom_eq f y n))
        (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (quotientSectionsIso f F y n).hom).hom
          (((ModuleCat.restrictScalars (@baseRingHom (Y.presheaf.stalk y) inferInstance _ (stalkBaseChangeStructure f y))).map (((Stacks.Cohomology.AffineBase.moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
            (cokernel.π (C := (stalkBaseChange f y).Modules)
              (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
                (stalkBaseChangeModule f F y)).ι))).hom x))) (hE a)).trans (towerSections_pullbackSection f F y n W hyW a)
  refine ⟨Φ, fun n a => ?_⟩
  have h₁ := hΦ n (E.symm (((Scheme.Modules.pushforward f).obj F).presheaf.germ W y hyW a))
  rw [LinearEquiv.apply_symm_apply] at h₁
  exact h₁.trans (key n a)

/-- **The theorem on formal functions in degree zero, normalised on germs** [Stacks, Tag 02OD].
Let `f : X ⟶ Y` be proper with `Y` locally Noetherian, `ℱ` a coherent `𝒪_X`-module and `y : Y`.
There is an `𝒪_{Y,y}`-linear isomorphism `Φ` from the `𝔪_y`-adic completion of `(f_* ℱ)_y` to the
limit of the tower `Γ(X_n, ℱ_n)` (along the restriction maps `ψ`) whose `n`-th component sends the
class of the germ of a section `s` over `f ⁻¹ U` to the restriction of `s` to `X_n`. -/
public theorem nonempty_adicCompletion_pushforwardStalk_linearEquiv_towerLimit_germ {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [IsProper f] (F : X.Modules) [F.IsCoherent] (y : Y) :
    letI H : ℕ → Type u := fun n => Γ(infinitesimalModule f F y n, ⊤)
    letI : ∀ n, Module (Y.presheaf.stalk y) (H n) := fun n =>
      Module.compHom _ (infinitesimalBaseRingHom f y n)
    letI res : ∀ (n : ℕ) (U : Y.Opens), y ∈ U → Γ(F, f ⁻¹ᵁ U) → H n := fun n U hy s =>
      (infinitesimalModule f F y n).presheaf.map
        (homOfLE (top_le_preimage_infinitesimalι f y n U hy)).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (infinitesimalι f y n)).unit.app F).app
          (f ⁻¹ᵁ U) s)
    ∀ (ψ : ∀ m n, m ≤ n → H n →ₗ[Y.presheaf.stalk y] H m),
      (∀ m n (h : m ≤ n) (x : H n), ψ m n h x =
        ((Scheme.Modules.pullbackComp (infinitesimalTransition f y h)
              (infinitesimalι f y n)).hom.app F ≫
            (Scheme.Modules.pullbackCongr (infinitesimalTransition_ι f y h)).hom.app F).app ⊤
          ((Scheme.Modules.pullback (infinitesimalTransition f y h)).obj
              (infinitesimalModule f F y n) |>.presheaf.map
            (homOfLE (top_le_preimage_top (infinitesimalTransition f y h))).op
            (((Scheme.Modules.pullbackPushforwardAdjunction
              (infinitesimalTransition f y h)).unit.app (infinitesimalModule f F y n)).app ⊤
                x))) →
      ∃ Φ : AdicCompletion (stalkMaximalIdeal y)
          (((Scheme.Modules.pushforward f).obj F).presheaf.stalk y) ≃ₗ[Y.presheaf.stalk y]
            towerLimit H ψ,
        ∀ n (U : Y.Opens) (hy : y ∈ U) (s : Γ(F, f ⁻¹ᵁ U)),
          towerLimit.proj n (Φ (AdicCompletion.of _ _
            (((Scheme.Modules.pushforward f).obj F).presheaf.germ U y hy s))) = res n U hy s := by
  intro ψ hψ
  letI : ∀ n, Module (Y.presheaf.stalk y) Γ(infinitesimalModule f F y n, ⊤) := fun n =>
    Module.compHom _ (infinitesimalBaseRingHom f y n)
  haveI : ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.FlatBaseChange.isQuasicoherent_pushforward_of_qcqs f F
  obtain ⟨U₀, hU₀, hyU₀, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) (Set.mem_univ _)
  obtain ⟨Φ, hΦ⟩ := exists_linearEquiv_towerLimit_germ_of_isAffineOpen f F y hU₀ hyU₀ ψ hψ
  refine ⟨Φ, fun n U hy s => ?_⟩
  obtain ⟨W, hW, hyW, hWsub⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y) (U := U ⊓ U₀) ⟨hy, hyU₀⟩
  have hWU : W ≤ U := fun z hz => (hWsub hz).1
  have hWU₀ : W ≤ U₀ := fun z hz => (hWsub hz).2
  obtain ⟨Φ', hΦ'⟩ := exists_linearEquiv_towerLimit_germ_of_isAffineOpen f F y hW hyW ψ hψ
  have hr : ((towerLimit.proj n).comp Φ.toLinearMap).comp
        (AdicCompletion.of (stalkMaximalIdeal y)
          (((Scheme.Modules.pushforward f).obj F).presheaf.stalk y)) =
      ((towerLimit.proj n).comp Φ'.toLinearMap).comp
        (AdicCompletion.of (stalkMaximalIdeal y)
          (((Scheme.Modules.pushforward f).obj F).presheaf.stalk y)) := by
    refine linearMap_stalk_ext ((Scheme.Modules.pushforward f).obj F) y hU₀ hyU₀ _ _
      fun a => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    refine (hΦ n a).trans ?_
    refine Eq.trans ?_ (congrArg (fun g => towerLimit.proj n (Φ' (AdicCompletion.of _ _ g)))
      (TopCat.Presheaf.germ_res_apply ((Scheme.Modules.pushforward f).obj F).presheaf
        (homOfLE hWU₀) y hyW a))
    exact ((infinitesimalModule_map_unit_app_restrict f F y n hWU₀ hyW a).symm.trans
      (hΦ' n _).symm)
  have h₂ := congrArg (fun r => r (((Scheme.Modules.pushforward f).obj F).presheaf.germ W y hyW
    (((Scheme.Modules.pushforward f).obj F).presheaf.map (homOfLE hWU).op s))) hr
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h₂
  have e₁ := congrArg (fun g => towerLimit.proj n (Φ (AdicCompletion.of _ _ g)))
    (TopCat.Presheaf.germ_res_apply ((Scheme.Modules.pushforward f).obj F).presheaf
      (homOfLE hWU) y hyW s)
  exact e₁.symm.trans (h₂.trans ((hΦ' n _).trans
    (infinitesimalModule_map_unit_app_restrict f F y n hWU hyW s)))

end Main

end MMP.FormalFunctions
