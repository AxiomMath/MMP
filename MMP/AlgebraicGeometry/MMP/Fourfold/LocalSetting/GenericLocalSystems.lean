module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
import MMP.Topology.Sheaves.LocalSystem.CompactProductDirectImage
import MMP.Topology.Sheaves.LocalSystem.RetractPuncturedProduct
import MMP.AlgebraicGeometry.MMP.Fourfold.LocalSetting.GenericTopologicalTriviality
import MMP.AlgebraicGeometry.Analytic.IsolatedPointLink
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicGeometry.Analytic.ClosedSubschemeOrientation
import MMP.AlgebraicGeometry.CycleMap.Stacks.PointsOverClosed
import MMP.AlgebraicGeometry.Analytic.RationalSingularComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.VeryGeneralFibreLineBundles
import MMP.AlgebraicGeometry.Resolution.Blowup.SmoothGeometry
import StacksFrontier.AlgebraicGeometry.Blowup.TwoStepTower
import MMP.AlgebraicGeometry.Analytic.BlowupRetraction.SmoothCentre

/-!
# Generic local systems along a singular curve

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`), and let
`j : Y_reg ↪ Y` be the inclusion of the smooth locus. Then there is a nonempty Zariski open
`T° ⊆ T` inside the smooth locus of `T` with the following property. On every Zariski open
`U ⊆ T°` and in every degree `q`, the restrictions to `U^an` of `R^q π_* ℚ_Ỹ` and of
`R^q j_* ℚ_{Y_reg}` are local systems. Moreover, the stalk of the first at `x` is
`H^q(π⁻¹(x); ℚ)`, through restriction of classes.

## Main results

* `MMP.Fourfold.IsLocalSetting.exists_isLocalSystem_higherDirectImage`.

## Implementation notes

* Direct images are `MMP.Fourfold.higherDirectImage`, the sheafification of
  `V ↦ H^q(f⁻¹(V); ℚ)` (singular cohomology). `T°` is an open of the reduced curve
  `MMP.Fourfold.curveScheme T`. Restriction to an open `U ⊆ T°` is the inverse image along
  `MMP.Fourfold.curveOpenInclusion`.
* The stalk statement gives an isomorphism of the stalk at `x ∈ U^an` with
  `H^q(π⁻¹(y); ℚ)`, `y` the image of `x` in `Y^an`. It is pinned by asking that, for every open
  `V ∋ y`, it carry the germ of a class on `π⁻¹(V)` to the restriction of that class to
  `π⁻¹(y)`.
* "Inherited by every nonempty open subset" is stated by quantifying over all opens `U ≤ T°`.
  The empty open satisfies the conclusion trivially.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][kollarmori1998]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints MMP.Resolution

namespace Proof_thm_mmp_curvels_generic_local_systems

section SheafLemmas

variable {X Y Z : TopCat.{0}}

/-- Global sections of a pushforward are global sections. -/
private noncomputable def pushforwardTopIso (f : X ⟶ Y) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ⋙
        (sheafSections (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤) ≅
      (sheafSections (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).obj (Opposite.op ⊤) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The inverse image of a constant sheaf is constant. -/
private noncomputable def pullbackConstIso (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ≅
      constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) :=
  (((constantSheafAdj _ (ModuleCat.{0} ℚ) Limits.isTerminalTop).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f)).ofNatIsoRight
      (pushforwardTopIso f)).leftAdjointUniq
        (constantSheafAdj _ (ModuleCat.{0} ℚ) Limits.isTerminalTop)

/-- Direct images compose. -/
private noncomputable def pushforwardCompIso (g : X ⟶ Y) (f : Y ⟶ Z) :
    TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) g ⋙ TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) f ≅
      TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) (g ≫ f) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Inverse images compose. -/
private noncomputable def pullbackCompIso (g : X ⟶ Y) (f : Y ⟶ Z) :
    TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (g ≫ f) :=
  (((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) g)).ofNatIsoRight
      (pushforwardCompIso g f)).leftAdjointUniq
        (TopCat.Sheaf.pullbackPushforwardAdjunction _ (g ≫ f))

/-- The inverse image of a local system along a continuous map is a local system. -/
private theorem isLocalSystem_pullback (f : X ⟶ Y) {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y}
    (hF : IsLocalSystem F) :
    IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F) := by
  intro x
  obtain ⟨V, hxV, E, hE, ⟨e⟩⟩ := hF (f x)
  let V' : Opens X := (Opens.map f).obj V
  let g : (Opens.toTopCat X).obj V' ⟶ (Opens.toTopCat Y).obj V :=
    TopCat.ofHom ⟨fun v ↦ ⟨f v.1, v.2⟩, by fun_prop⟩
  have hw : V'.inclusion' ≫ f = g ≫ V.inclusion' := rfl
  refine ⟨V', hxV, E, hE, ⟨?_⟩⟩
  exact (pullbackCompIso V'.inclusion' f).app F ≪≫ eqToIso (by rw [hw]) ≪≫
    (pullbackCompIso g V.inclusion').symm.app F ≪≫
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).mapIso e ≪≫ (pullbackConstIso g).app E

/-- A sheaf isomorphic to a local system is a local system. -/
private theorem isLocalSystem_of_iso {F G : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (hF : IsLocalSystem F) (e : F ≅ G) : IsLocalSystem G := by
  intro x
  obtain ⟨V, hxV, E, hE, ⟨φ⟩⟩ := hF x
  exact ⟨V, hxV, E, hE, ⟨(TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) V.inclusion').mapIso e.symm ≪≫ φ⟩⟩

/-- Being a local system is local: a sheaf whose inverse images along a cover by open
embeddings are local systems is a local system. -/
private theorem isLocalSystem_of_isOpenEmbedding_cover {F : TopCat.Sheaf (ModuleCat.{0} ℚ) X}
    (h : ∀ x : X, ∃ (Z : TopCat.{0}) (e : Z ⟶ X), IsOpenEmbedding e ∧ x ∈ Set.range e ∧
      IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) e).obj F)) :
    IsLocalSystem F := by
  intro x
  obtain ⟨Z, e, he, ⟨z, rfl⟩, hZ⟩ := h x
  obtain ⟨W, hzW, E, hE, ⟨φ⟩⟩ := hZ z
  let V : Opens X := he.isOpenMap.functor.obj W
  let g : (Opens.toTopCat X).obj V ⟶ (Opens.toTopCat Z).obj W :=
    TopCat.ofHom ⟨fun v ↦ ⟨(he.isEmbedding.toHomeomorph).symm ⟨v.1, by
        obtain ⟨w, -, hw⟩ := v.2; exact ⟨w, hw⟩⟩, by
        obtain ⟨w, hwW, hw⟩ := v.2
        have : (he.isEmbedding.toHomeomorph).symm ⟨v.1, ⟨w, hw⟩⟩ = w := by
          rw [Homeomorph.symm_apply_eq]; exact Subtype.ext hw.symm
        change _ ∈ (W : Set Z)
        convert hwW⟩, by
      refine Continuous.subtype_mk ?_ _
      exact (he.isEmbedding.toHomeomorph).symm.continuous.comp
        (continuous_subtype_val.subtype_mk _)⟩
  have hw : V.inclusion' = g ≫ W.inclusion' ≫ e := by
    ext v
    change (v.1 : X) = e ((he.isEmbedding.toHomeomorph).symm _)
    have := (he.isEmbedding.toHomeomorph).apply_symm_apply ⟨v.1, by
        obtain ⟨w, -, hw⟩ := v.2; exact ⟨w, hw⟩⟩
    exact (congrArg Subtype.val this).symm
  refine ⟨V, ⟨z, hzW, rfl⟩, E, hE, ⟨?_⟩⟩
  exact eqToIso (by rw [hw]) ≪≫ (pullbackCompIso g (W.inclusion' ≫ e)).symm.app F ≪≫
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).mapIso
      ((pullbackCompIso W.inclusion' e).symm.app F ≪≫ φ) ≪≫ (pullbackConstIso g).app E

/-- The isomorphism on rational cohomology induced by a homeomorphism. -/
private noncomputable def rationalCohomologyIsoOfHomeomorph {X X' : TopCat.{0}} (h : X ≃ₜ X')
    (q : ℕ) :
    rationalCohomology X' q ≅ rationalCohomology X q where
  hom := rationalCohomologyMap (TopCat.ofHom ⟨h, h.continuous⟩) q
  inv := rationalCohomologyMap (TopCat.ofHom ⟨h.symm, h.symm.continuous⟩) q
  hom_inv_id := by
    rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_id]
    congr 1
    ext x
    simp
  inv_hom_id := by
    rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_id]
    congr 1
    ext x
    simp

/-- Sheafification commutes with pullback. -/
private noncomputable def pullbackSheafifyIso {X Y : TopCat.{0}} (e : X ⟶ Y) :
    presheafToSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} ℚ) ⋙
        TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) e ≅
      TopCat.Presheaf.pullback (ModuleCat.{0} ℚ) e ⋙
        presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ) :=
  ((sheafificationAdjunction _ _).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction _ e)).leftAdjointUniq
    ((TopCat.Presheaf.pullbackPushforwardAdjunction _ e).comp (sheafificationAdjunction _ _))

/-- For an open embedding `e : M ⟶ Y`, a map `j : A ⟶ Y` and `j' : A' ⟶ M` identified with the
restriction of `j` over `e(M)` by an embedding `k : A' ⟶ A`, the presheaf
`V ↦ H^q(j⁻¹(e V); ℚ)` on `M` is `V ↦ H^q(j'⁻¹(V); ℚ)`. -/
private noncomputable def directImagePresheafIso {M Y A A' : TopCat.{0}} (e : M ⟶ Y)
    (he : IsOpenEmbedding e)
    (j : A ⟶ Y) (k : A' ⟶ A) (hk : IsEmbedding k) (j' : A' ⟶ M) (w : j' ≫ e = k ≫ j)
    (hrange : Set.range k = j ⁻¹' Set.range e) (q : ℕ) :
    he.isOpenMap.functor.op ⋙ directImagePresheaf j q ≅ directImagePresheaf j' q := by
  have hw : ∀ a, e (j' a) = j (k a) := fun a ↦ ConcreteCategory.congr_hom w a
  have hpre : ∀ b : A, j b ∈ Set.range e → ∃ a, k a = b := fun b hb ↦ hrange.ge hb
  let kinv : ∀ b : A, j b ∈ Set.range e → A' := fun b hb ↦ (hpre b hb).choose
  have hkinv : ∀ b hb, k (kinv b hb) = b := fun b hb ↦ (hpre b hb).choose_spec
  let hV : ∀ V : Opens M, (preimageSpace j' V) ≃ₜ preimageSpace j (he.isOpenMap.functor.obj V) :=
    fun V ↦
    { toFun := fun a ↦ ⟨k a.1, by
        change j (k a.1) ∈ e '' (V : Set M)
        exact ⟨j' a.1, a.2, hw a.1⟩⟩
      invFun := fun b ↦ ⟨kinv b.1 (Set.image_subset_range _ _ b.2), by
          have hb := b.2
          obtain ⟨m, hm, hmb⟩ := hb
          change j' _ ∈ (V : Set M)
          have : e (j' (kinv b.1 (Set.image_subset_range _ _ b.2))) = e m := by
            rw [hw, hkinv _ (Set.image_subset_range _ _ b.2), hmb]
          rw [he.injective this]; exact hm⟩
      left_inv := fun a ↦ Subtype.ext (hk.injective (hkinv _ ⟨j' a.1, hw a.1⟩))
      right_inv := fun b ↦ Subtype.ext (hkinv _ (Set.image_subset_range _ _ b.2))
      continuous_toFun := by fun_prop
      continuous_invFun := by
        refine Continuous.subtype_mk ?_ _
        rw [hk.continuous_iff]
        have : (fun b : preimageSpace j (he.isOpenMap.functor.obj V) ↦
            k (kinv b.1 (Set.image_subset_range _ _ b.2))) = fun b ↦ b.1 := by
          funext b; exact hkinv _ (Set.image_subset_range _ _ b.2)
        rw [Function.comp_def, this]; fun_prop }
  exact NatIso.ofComponents (fun V ↦ rationalCohomologyIsoOfHomeomorph (hV V.unop) q) (by
      intro V W i
      change rationalCohomologyMap _ q ≫ rationalCohomologyMap _ q =
        rationalCohomologyMap _ q ≫ rationalCohomologyMap _ q
      rw [← rationalCohomologyMap_comp, ← rationalCohomologyMap_comp]
      rfl)

/-- Restriction of `R^q j_* ℚ` to an open `e : M ⟶ Y` is `R^q j'_* ℚ` for the restriction `j'`
of `j` over `M`. -/
private noncomputable def higherDirectImagePullbackIso {M Y A A' : TopCat.{0}} (e : M ⟶ Y)
    (he : IsOpenEmbedding e)
    (j : A ⟶ Y) (k : A' ⟶ A) (hk : IsEmbedding k) (j' : A' ⟶ M) (w : j' ≫ e = k ≫ j)
    (hrange : Set.range k = j ⁻¹' Set.range e) (q : ℕ) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) e).obj (higherDirectImage j q) ≅
      higherDirectImage j' q :=
  (pullbackSheafifyIso e).app _ ≪≫
    (presheafToSheaf _ _).mapIso ((he.isOpenMap.pullbackIso (C := ModuleCat.{0} ℚ)).app _ ≪≫
      directImagePresheafIso e he j k hk j' w hrange q)

/-- The local punctured cohomology `colim_{V ∋ m} H^q(V ∖ {m}; ℚ)` is local: along an open
embedding `e : M ⟶ P` it is that of `P` at `e m`. -/
private noncomputable def puncturedStalkIsoOfIsOpenEmbedding {M P : TopCat.{0}} (e : M ⟶ P)
    (he : IsOpenEmbedding e) (m : M) (q : ℕ) :
    (directImagePresheaf (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ({e m}ᶜ : Set P) ⟶ P) q).stalk (e m) ≅
      (directImagePresheaf (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
        TopCat.of ({m}ᶜ : Set M) ⟶ M) q).stalk m :=
  let k : TopCat.of ({m}ᶜ : Set M) ⟶ TopCat.of ({e m}ᶜ : Set P) :=
    TopCat.ofHom ⟨fun v ↦ ⟨e v.1, fun h ↦ v.2 (he.injective h)⟩, by fun_prop⟩
  have hk : IsEmbedding k := by
    refine IsEmbedding.of_comp (by fun_prop) continuous_subtype_val ?_
    exact he.isEmbedding.comp IsEmbedding.subtypeVal
  have hrange : Set.range k = (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ :
      TopCat.of ({e m}ᶜ : Set P) ⟶ P) ⁻¹' Set.range e := by
    ext b
    refine ⟨?_, fun hb ↦ ?_⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, rfl⟩
    · obtain ⟨a, ha⟩ := hb
      have ha' : a ≠ m := fun h ↦ b.2 (by subst h; exact ha.symm)
      exact ⟨⟨a, ha'⟩, Subtype.ext ha⟩
  TopCat.Presheaf.stalkPullbackIso _ e _ m ≪≫
    (TopCat.Presheaf.stalkFunctor _ m).mapIso
      ((he.isOpenMap.pullbackIso (C := ModuleCat.{0} ℚ)).app _ ≪≫
        directImagePresheafIso e he _ k hk _ rfl hrange q)

/-- The stalk of an inverse image is the stalk: `stalkToPullbackStalk` is an isomorphism. -/
private theorem isIso_stalkToPullbackStalk (f : X ⟶ Y)
    (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y) (x : X) : IsIso (stalkToPullbackStalk f F x) := by
  have h : stalkToPullbackStalk f F x =
      (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).inv :=
    (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq _ f F x).symm
  rw [h]
  exact ⟨⟨_, (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).inv_hom_id,
    (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).hom_inv_id⟩⟩

/-- A morphism of presheaves of `ℚ`-vector spaces which is bijective on all stalks becomes an
isomorphism after sheafification. -/
private theorem isIso_presheafToSheaf_map_of_bijective {P Q : TopCat.Presheaf (ModuleCat.{0} ℚ) X}
    (μ : P ⟶ Q) (hμ : ∀ x : X, Function.Bijective ((TopCat.Presheaf.stalkFunctor _ x).map μ).hom) :
    IsIso ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).map μ) := by
  have hst : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).map μ).1) := by
    intro x
    haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ) P
    haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ) Q
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map μ) :=
      (ConcreteCategory.isIso_iff_bijective _).2 (hμ x)
    have hnat := congrArg (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      (toSheafify_naturality (Opens.grothendieckTopology X) μ)
    rw [Functor.map_comp, Functor.map_comp] at hnat
    have : (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
        ((presheafToSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℚ)).map μ).1 =
        inv ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
          (toSheafify (Opens.grothendieckTopology X) P)) ≫
          (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map μ ≫
          (TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
            (toSheafify (Opens.grothendieckTopology X) Q) := by
      rw [hnat, IsIso.inv_hom_id_assoc]
    rw [this]
    infer_instance
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

/-- On a contractible space the identity is homotopic to every constant map. -/
private theorem homotopic_id_const {D : Type} [TopologicalSpace D] [ContractibleSpace D]
    (d : D) : (ContinuousMap.id D).Homotopic (ContinuousMap.const D d) := by
  obtain ⟨y, hy⟩ := id_nullhomotopic D
  have h2 : (ContinuousMap.const D d).Homotopic (ContinuousMap.const D y) := by
    simpa using hy.comp (ContinuousMap.Homotopic.refl (ContinuousMap.const D d))
  exact hy.trans h2.symm

/-- **Tautness of a product family.** For the projection `p : K × W ⟶ W`, where points of `W`
have arbitrarily small contractible open neighbourhoods, a class on a tube `p⁻¹(V)` vanishing
on the fibre `p⁻¹(w) = K × {w}` vanishes on a smaller tube. -/
private theorem taut_prod_snd (K W : TopCat.{0})
    (hW : ∀ (w : W) (V : Set W), IsOpen V → w ∈ V →
      ∃ D : Set W, IsOpen D ∧ w ∈ D ∧ D ⊆ V ∧ ContractibleSpace D) (q : ℕ) (w : W) :
    let pW : TopCat.of (K × W) ⟶ W := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
    ∀ (V : Opens W) (hV : w ∈ V) (α : rationalCohomology (preimageSpace pW V) q),
      (rationalCohomologyMap (TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono
          (Set.singleton_subset_iff.2 hV)), continuous_inclusion _⟩) q).hom α = 0 →
      ∃ (V' : Opens W) (hV'V : V' ≤ V), w ∈ V' ∧
        (rationalCohomologyMap (preimageInclusion pW hV'V) q).hom α = 0 := by
  intro pW V hV α hα
  let r : ∀ V : Opens W, preimageSpace pW V ⟶ TopCat.of (pW ⁻¹' {w}) := fun V ↦
    TopCat.ofHom ⟨fun y ↦ ⟨(y.1.1, w), rfl⟩, by fun_prop⟩
  obtain ⟨D, hD, hwD, hDV, hc⟩ := hW w V V.isOpen hV
  let Dop : Opens W := ⟨D, hD⟩
  have hDV' : Dop ≤ V := hDV
  obtain ⟨H⟩ := homotopic_id_const (⟨w, hwD⟩ : D)
  let G : TopCat.Homotopy (preimageInclusion pW hDV')
      (r Dop ≫ TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono
        (Set.singleton_subset_iff.2 hV)), continuous_inclusion _⟩) :=
    { toContinuousMap :=
        ⟨fun ty ↦ ⟨(ty.2.1.1, (H (ty.1, ⟨ty.2.1.2, ty.2.2⟩)).1),
            hDV (H (ty.1, ⟨ty.2.1.2, ty.2.2⟩)).2⟩, by fun_prop⟩
      map_zero_left := fun y ↦ by
        refine Subtype.ext (Prod.ext rfl ?_)
        change ((H (0, _)) : W) = y.1.2
        rw [H.apply_zero]; rfl
      map_one_left := fun y ↦ by
        refine Subtype.ext (Prod.ext rfl ?_)
        change ((H (1, _)) : W) = w
        rw [H.apply_one]; rfl }
  have hmap : rationalCohomologyMap (preimageInclusion pW hDV') q =
      rationalCohomologyMap (r Dop ≫ TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono
        (Set.singleton_subset_iff.2 hV)), continuous_inclusion _⟩) q :=
    MMP.relativeSingularCohomology.map_eq_of_homotopy ℚ G
      (fun y hy ↦ absurd (Set.mem_univ y) hy) _ _ q
  refine ⟨Dop, hDV', hwD, ?_⟩
  rw [hmap, rationalCohomologyMap_comp, ModuleCat.comp_apply, hα, map_zero]

/-- Pullback of classes along a composite. -/
private theorem rationalCohomologyMap_apply_apply {A B C : TopCat.{0}} (g : A ⟶ B) (f : B ⟶ C)
    (q : ℕ) (x : rationalCohomology C q) :
    (rationalCohomologyMap g q).hom ((rationalCohomologyMap f q).hom x) =
      (rationalCohomologyMap (g ≫ f) q).hom x := by
  rw [rationalCohomologyMap_comp]; rfl

/-- **Direct images along a product projection.** If points of `W` have arbitrarily small
contractible open neighbourhoods, the higher direct image of `ℚ` along `K × W ⟶ W` is the
constant sheaf `H^q(K; ℚ)`, through pullback of classes along the first projection. -/
private theorem nonempty_iso_constantSheaf_higherDirectImage_snd (K W : TopCat.{0})
    (hW : ∀ (w : W) (V : Set W), IsOpen V → w ∈ V →
      ∃ D : Set W, IsOpen D ∧ w ∈ D ∧ D ⊆ V ∧ ContractibleSpace D) (q : ℕ) :
    Nonempty (higherDirectImage (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
        TopCat.of (K × W) ⟶ W) q ≅
      (constantSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).obj
        (rationalCohomology K q)) := by
  let pW : TopCat.of (K × W) ⟶ W := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
  let P := directImagePresheaf pW q
  let E := rationalCohomology K q
  let prK : ∀ V : Opens W, preimageSpace pW V ⟶ K := fun V ↦
    TopCat.ofHom ⟨fun y ↦ y.1.1, by fun_prop⟩
  let C0 : TopCat.Presheaf (ModuleCat.{0} ℚ) W := (Functor.const (Opens W)ᵒᵖ).obj E
  let μ : C0 ⟶ P :=
    { app := fun V ↦ rationalCohomologyMap (prK V.unop) q
      naturality := fun V V' i ↦ by
        change 𝟙 _ ≫ _ = _ ≫ rationalCohomologyMap _ q
        rw [Category.id_comp, ← rationalCohomologyMap_comp]
        rfl }
  have hμ : ∀ w : W, Function.Bijective ((TopCat.Presheaf.stalkFunctor _ w).map μ).hom := by
    intro w
    have hker := taut_prod_snd K W hW q w
    let fib : ∀ (V : Opens W) (hV : w ∈ V), TopCat.of (pW ⁻¹' {w}) ⟶ preimageSpace pW V :=
      fun V hV ↦ TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono
        (Set.singleton_subset_iff.2 hV)), continuous_inclusion _⟩
    let sec : K ⟶ TopCat.of (pW ⁻¹' {w}) := TopCat.ofHom ⟨fun a ↦ ⟨(a, w), rfl⟩, by fun_prop⟩
    have hA : ∀ V hV, sec ≫ fib V hV ≫ prK V = 𝟙 K := fun V hV ↦ TopCat.ext fun _ ↦ rfl
    have hB : ∀ V hV, fib V hV ≫ prK V ≫ sec = 𝟙 _ := fun V hV ↦
      TopCat.ext fun y ↦ Subtype.ext (Prod.ext rfl y.2.symm)
    refine ⟨?_, fun t ↦ ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro t ht0
      obtain ⟨V, hV, c, rfl⟩ := C0.germ_exist t
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ht0
      have h0 : P.germ V w hV ((μ.app (Opposite.op V)).hom c) = P.germ V w hV 0 :=
        ht0.trans (map_zero _).symm
      obtain ⟨V', hV', iU, iV, hE⟩ := P.germ_eq w hV hV _ _ h0
      rw [map_zero] at hE
      have hnat : (P.map iU.op).hom ((μ.app (Opposite.op V)).hom c) =
          (μ.app (Opposite.op V')).hom c := by
        rw [← ModuleCat.comp_apply, ← μ.naturality iU.op]
        rfl
      rw [hnat] at hE
      have hc : c = 0 := by
        have h1 : (rationalCohomologyMap (sec ≫ fib V' hV') q).hom
            ((rationalCohomologyMap (prK V') q).hom c) = 0 := by
          rw [show (rationalCohomologyMap (prK V') q).hom c = 0 from hE, map_zero]
        rwa [rationalCohomologyMap_apply_apply, Category.assoc, hA V' hV',
          rationalCohomologyMap_id] at h1
      rw [hc]
      exact map_zero _
    · obtain ⟨V, hV, α, rfl⟩ := P.germ_exist t
      let c : E := (rationalCohomologyMap (sec ≫ fib V hV) q).hom α
      refine ⟨C0.germ V w hV c, ?_⟩
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      let a : rationalCohomology (preimageSpace pW V) q := α
      let m : rationalCohomology (preimageSpace pW V) q := (rationalCohomologyMap (prK V) q).hom c
      have hδ : (rationalCohomologyMap (fib V hV) q).hom (m - a) = 0 := by
        rw [map_sub, sub_eq_zero]
        change (rationalCohomologyMap (fib V hV) q).hom ((rationalCohomologyMap (prK V) q).hom
          ((rationalCohomologyMap (sec ≫ fib V hV) q).hom a)) = _
        have hB2 : (fib V hV ≫ prK V) ≫ sec ≫ fib V hV = fib V hV := by
          rw [← Category.assoc, Category.assoc (fib V hV), hB V hV, Category.id_comp]
        rw [rationalCohomologyMap_apply_apply, rationalCohomologyMap_apply_apply, hB2]
      obtain ⟨V', hV'V, hwV', hres⟩ := hker V hV _ hδ
      have h1 : (P.germ V w hV).hom (m - a) = 0 := by
        have := P.germ_res_apply (homOfLE hV'V) w hwV' (m - a)
        refine this.symm.trans ?_
        change (P.germ V' w hwV').hom
          ((rationalCohomologyMap (preimageInclusion pW hV'V) q).hom (m - a)) = 0
        rw [hres]
        exact LinearMap.map_zero _
      exact sub_eq_zero.1 ((map_sub (P.germ V w hV).hom m a).symm.trans h1)
  haveI := isIso_presheafToSheaf_map_of_bijective μ hμ
  exact ⟨(asIso ((presheafToSheaf (Opens.grothendieckTopology W) (ModuleCat.{0} ℚ)).map μ)).symm⟩

/-- Germs of classes exhaust the stalks of a higher direct image. -/
private theorem exists_higherDirectImageGerm_eq {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ) (y : Y)
    (t : ((TopCat.Sheaf.forget _ _).obj (higherDirectImage f q)).stalk y) :
    ∃ (V : Opens Y) (hy : y ∈ V) (α : rationalCohomology (preimageSpace f V) q),
      (higherDirectImageGerm f q y hy).hom α = t := by
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y (ModuleCat.{0} ℚ)
    (directImagePresheaf f q)
  obtain ⟨s, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 this).2 t
  obtain ⟨V, hy, α, rfl⟩ := (directImagePresheaf f q).germ_exist s
  exact ⟨V, hy, α, rfl⟩

/-- A germ of a class vanishes exactly when the class vanishes on a smaller tube. -/
private theorem exists_le_of_higherDirectImageGerm_eq_zero {X Y : TopCat.{0}} (f : X ⟶ Y)
    (q : ℕ) {y : Y} {V : Opens Y} (hy : y ∈ V) (α : rationalCohomology (preimageSpace f V) q)
    (h : (higherDirectImageGerm f q y hy).hom α = 0) :
    ∃ (V' : Opens Y) (hV' : V' ≤ V), y ∈ V' ∧
      (rationalCohomologyMap (preimageInclusion f hV') q).hom α = 0 := by
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso y (ModuleCat.{0} ℚ)
    (directImagePresheaf f q)
  have h0 : (directImagePresheaf f q).germ V y hy α = (directImagePresheaf f q).germ V y hy 0 := by
    refine ((ConcreteCategory.isIso_iff_bijective _).1 this).1 ?_
    exact h.trans ((map_zero _).symm.trans (congrArg _ (map_zero _).symm))
  obtain ⟨V', hV', iU, iV, hE⟩ := (directImagePresheaf f q).germ_eq y hy hy _ _ h0
  refine ⟨V', iU.le, hV', ?_⟩
  exact hE.trans (map_zero _)

/-- Germs of classes are compatible with restriction to smaller tubes. -/
private theorem higherDirectImageGerm_res {X Y : TopCat.{0}} (f : X ⟶ Y) (q : ℕ) {y : Y}
    {V V' : Opens Y} (hV' : V' ≤ V) (hy : y ∈ V') (α : rationalCohomology (preimageSpace f V) q) :
    (higherDirectImageGerm f q y hy).hom
        ((rationalCohomologyMap (preimageInclusion f hV') q).hom α) =
      (higherDirectImageGerm f q y (hV' hy)).hom α :=
  congrArg (fun z ↦ ((TopCat.Presheaf.stalkFunctor _ y).map
    (toSheafify (Opens.grothendieckTopology Y) (directImagePresheaf f q))).hom z)
    ((directImagePresheaf f q).germ_res_apply (homOfLE hV') y hy α)

/-- The base change morphism `ι^* R^q p_* ℚ ⟶ R^q p'_* ℚ` for a commutative square
`g ≫ p = p' ≫ ι`, induced by pullback of classes along `g`. -/
private noncomputable def higherDirectImageBaseChange {P S W P' : TopCat.{0}} (p : P ⟶ S)
    (ι : W ⟶ S) (g : P' ⟶ P) (p' : P' ⟶ W) (w : g ≫ p = p' ≫ ι) (q : ℕ) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) ι).obj (higherDirectImage p q) ⟶
      higherDirectImage p' q :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) ι).homEquiv _ _).symm
    ⟨sheafifyLift (Opens.grothendieckTopology S)
      (directImageRestriction p g w q ≫ (TopCat.Presheaf.pushforward _ ι).map
        (toSheafify (Opens.grothendieckTopology W) (directImagePresheaf p' q)))
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) ι).obj (higherDirectImage p' q)).property⟩

/-- The base change morphism on germs: the germ of a class `α` on `p⁻¹(V)` goes to the germ of
its pullback along `g`. -/
private theorem higherDirectImageBaseChange_germ {P S W P' : TopCat.{0}} (p : P ⟶ S)
    (ι : W ⟶ S) (g : P' ⟶ P) (p' : P' ⟶ W) (w : g ≫ p = p' ≫ ι) (q : ℕ) (x : W)
    (V : Opens S) (hx : ι x ∈ V) :
    higherDirectImageGerm p q (ι x) hx ≫ stalkToPullbackStalk ι (higherDirectImage p q) x ≫
        (TopCat.Presheaf.stalkFunctor _ x).map (higherDirectImageBaseChange p ι g p' w q).1 =
      rationalCohomologyMap (preimageRestrict p g w V) q ≫
        higherDirectImageGerm p' q (V := (Opens.map ι).obj V) x hx := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) ι
  let F := higherDirectImage p q
  let θ := higherDirectImageBaseChange p ι g p' w q
  let η := directImageRestriction p g w q ≫ (TopCat.Presheaf.pushforward _ ι).map
    (toSheafify (Opens.grothendieckTopology W) (directImagePresheaf p' q))
  let φ : F ⟶ (TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) ι).obj (higherDirectImage p' q) :=
    ⟨sheafifyLift (Opens.grothendieckTopology S) η
      ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) ι).obj (higherDirectImage p' q)).property⟩
  have hφ' : (adj.homEquiv _ _) θ = φ := (adj.homEquiv _ _).apply_symm_apply φ
  rw [Adjunction.homEquiv_unit] at hφ'
  have hval : (adj.unit.app F).1.app (Opposite.op V) ≫
      θ.1.app (Opposite.op ((Opens.map ι).obj V)) = φ.1.app (Opposite.op V) := by
    rw [← hφ']; rfl
  have hlift : (toSheafify (Opens.grothendieckTopology S) (directImagePresheaf p q)).app
      (Opposite.op V) ≫ φ.1.app (Opposite.op V) = η.app (Opposite.op V) :=
    congrArg (fun m ↦ m.app (Opposite.op V))
      (toSheafify_sheafifyLift (Opens.grothendieckTopology S) η
        ((TopCat.Sheaf.pushforward (ModuleCat.{0} ℚ) ι).obj (higherDirectImage p' q)).property)
  let H := higherDirectImage p' q
  have e1 : higherDirectImageGerm p q (ι x) hx =
      (toSheafify (Opens.grothendieckTopology S) (directImagePresheaf p q)).app (Opposite.op V) ≫
        ((TopCat.Sheaf.forget _ S).obj F).germ V (ι x) hx :=
    TopCat.Presheaf.stalkFunctor_map_germ _ _ _ _
  have e1' : higherDirectImageGerm p' q (V := (Opens.map ι).obj V) x hx =
      (toSheafify (Opens.grothendieckTopology W) (directImagePresheaf p' q)).app
          (Opposite.op ((Opens.map ι).obj V)) ≫
        ((TopCat.Sheaf.forget _ W).obj H).germ ((Opens.map ι).obj V) x hx :=
    TopCat.Presheaf.stalkFunctor_map_germ _ _ _ _
  have e2 : ((TopCat.Sheaf.forget _ S).obj F).germ V (ι x) hx ≫ stalkToPullbackStalk ι F x =
      ((TopCat.Sheaf.forget _ S).map (adj.unit.app F)).app (Opposite.op V) ≫
        ((TopCat.Sheaf.forget _ W).obj ((TopCat.Sheaf.pullback _ ι).obj F)).germ
          ((Opens.map ι).obj V) x hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  have e3 : ((TopCat.Sheaf.forget _ W).obj ((TopCat.Sheaf.pullback _ ι).obj F)).germ
        ((Opens.map ι).obj V) x hx ≫ (TopCat.Presheaf.stalkFunctor _ x).map θ.1 =
      θ.1.app (Opposite.op ((Opens.map ι).obj V)) ≫
        ((TopCat.Sheaf.forget _ W).obj H).germ ((Opens.map ι).obj V) x hx :=
    TopCat.Presheaf.stalkFunctor_map_germ _ _ _ _
  let T := (toSheafify (Opens.grothendieckTopology S) (directImagePresheaf p q)).app
    (Opposite.op V)
  let Fg := ((TopCat.Sheaf.forget _ S).obj F).germ V (ι x) hx
  let U := ((TopCat.Sheaf.forget _ S).map (adj.unit.app F)).app (Opposite.op V)
  let Pg := ((TopCat.Sheaf.forget _ W).obj ((TopCat.Sheaf.pullback _ ι).obj F)).germ
    ((Opens.map ι).obj V) x hx
  let sθ := (TopCat.Presheaf.stalkFunctor _ x).map θ.1
  let θa := θ.1.app (Opposite.op ((Opens.map ι).obj V))
  let Hg := ((TopCat.Sheaf.forget _ W).obj H).germ ((Opens.map ι).obj V) x hx
  have e2' : Fg ≫ stalkToPullbackStalk ι F x ≫ sθ = U ≫ Pg ≫ sθ :=
    (Category.assoc Fg _ sθ).symm.trans ((congrArg (· ≫ sθ) e2).trans (Category.assoc U Pg sθ))
  exact (congrArg (· ≫ stalkToPullbackStalk ι F x ≫ sθ) e1).trans <|
    (Category.assoc T Fg _).trans <|
    (congrArg (T ≫ ·) e2').trans <|
    (congrArg (fun m ↦ T ≫ U ≫ m) e3).trans <|
    (congrArg (T ≫ ·) (Category.assoc U θa Hg).symm).trans <|
    (congrArg (fun m ↦ T ≫ m ≫ Hg) hval).trans <|
    (Category.assoc T _ Hg).symm.trans <|
    (congrArg (· ≫ Hg) hlift).trans <|
    (Category.assoc (rationalCohomologyMap (preimageRestrict p g w V) q) _ Hg).trans <|
    congrArg (rationalCohomologyMap (preimageRestrict p g w V) q ≫ ·) e1'.symm

/-- The inclusion `f⁻¹(y) ⟶ f⁻¹(V)` of a fibre into a tube. -/
private abbrev tubeFibreInclusion {X Y : TopCat.{0}} (f : X ⟶ Y) {y : Y} {V : Opens Y}
    (hy : y ∈ V) : TopCat.of (f ⁻¹' {y}) ⟶ preimageSpace f V :=
  TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono (Set.singleton_subset_iff.2 hy)),
    continuous_inclusion _⟩

/-- The map of fibres `p'⁻¹(x) ⟶ p⁻¹(ι x)` induced by `g`, for `g ≫ p = p' ≫ ι`. -/
private def baseChangeFibreMap {P S W P' : TopCat.{0}} (p : P ⟶ S) (ι : W ⟶ S) (g : P' ⟶ P)
    (p' : P' ⟶ W) (w : g ≫ p = p' ≫ ι) (x : W) :
    TopCat.of (p' ⁻¹' {x}) ⟶ TopCat.of (p ⁻¹' {ι x}) :=
  TopCat.ofHom ⟨fun y ↦ ⟨g y.1, (ConcreteCategory.congr_hom w y.1).trans (congrArg ι y.2)⟩,
    (g.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The map of tubes `p'⁻¹(ι⁻¹ V) ⟶ p⁻¹(V)` induced by `g`, for `g ≫ p = p' ≫ ι`. -/
private def baseChangeTubeMap {P S W P' : TopCat.{0}} (p : P ⟶ S) (ι : W ⟶ S) (g : P' ⟶ P)
    (p' : P' ⟶ W) (w : g ≫ p = p' ≫ ι) (V : Opens S) :
    preimageSpace p' ((Opens.map ι).obj V) ⟶ preimageSpace p V :=
  preimageRestrict p g w V

/-- **Base change of higher direct images, stalkwise.** For `g ≫ p = p' ≫ ι`, if the stalks of
`R^q p_* ℚ` along `ι` are the cohomology of the fibres, `p'` is taut, and `g` induces
isomorphisms on the cohomology of the fibres, then the base change morphism
`ι^* R^q p_* ℚ ⟶ R^q p'_* ℚ` is an isomorphism. -/
private theorem isIso_higherDirectImageBaseChange {P S W P' : TopCat.{0}} (p : P ⟶ S)
    (ι : W ⟶ S) (g : P' ⟶ P) (p' : P' ⟶ W) (w : g ≫ p = p' ≫ ι) (q : ℕ)
    (hp : ∀ x : W, ∃ e : ((TopCat.Sheaf.forget _ _).obj (higherDirectImage p q)).stalk (ι x) ≅
        rationalCohomology (TopCat.of (p ⁻¹' {ι x})) q,
      ∀ (V : Opens S) (hx : ι x ∈ V),
        higherDirectImageGerm p q (ι x) hx ≫ e.hom =
          rationalCohomologyMap (tubeFibreInclusion p hx) q)
    (htaut : ∀ (x : W) (V : Opens W) (hV : x ∈ V) (α : rationalCohomology (preimageSpace p' V) q),
      (rationalCohomologyMap (tubeFibreInclusion p' hV) q).hom α = 0 →
      ∃ (V' : Opens W) (hV'V : V' ≤ V), x ∈ V' ∧
        (rationalCohomologyMap (preimageInclusion p' hV'V) q).hom α = 0)
    (hfib : ∀ x : W,
      Function.Bijective (rationalCohomologyMap (baseChangeFibreMap p ι g p' w x) q).hom) :
    IsIso (higherDirectImageBaseChange p ι g p' w q) := by
  have hst : ∀ x : W, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
      (higherDirectImageBaseChange p ι g p' w q).1) := by
    intro x
    obtain ⟨e, he⟩ := hp x
    haveI := isIso_stalkToPullbackStalk ι (higherDirectImage p q) x
    have hσ := (ConcreteCategory.isIso_iff_bijective
      (stalkToPullbackStalk ι (higherDirectImage p q) x)).1 inferInstance
    have KF : ∀ (V : Opens S) (hx : ι x ∈ V) (α : rationalCohomology (preimageSpace p V) q),
        ((TopCat.Presheaf.stalkFunctor _ x).map (higherDirectImageBaseChange p ι g p' w q).1).hom
          ((stalkToPullbackStalk ι (higherDirectImage p q) x).hom
            ((higherDirectImageGerm p q (ι x) hx).hom α)) =
        (higherDirectImageGerm p' q (V := (Opens.map ι).obj V) x hx).hom
          ((rationalCohomologyMap (baseChangeTubeMap p ι g p' w V) q).hom α) := fun V hx α ↦
      ConcreteCategory.congr_hom (higherDirectImageBaseChange_germ p ι g p' w q x V hx) α
    have hfibα : ∀ (V : Opens S) (hx : ι x ∈ V) (α : rationalCohomology (preimageSpace p V) q),
        (rationalCohomologyMap (tubeFibreInclusion p' (V := (Opens.map ι).obj V) hx) q).hom
          ((rationalCohomologyMap (baseChangeTubeMap p ι g p' w V) q).hom α) =
        (rationalCohomologyMap (baseChangeFibreMap p ι g p' w x) q).hom
          ((rationalCohomologyMap (tubeFibreInclusion p hx) q).hom α) := by
      intro V hx α
      rw [rationalCohomologyMap_apply_apply, rationalCohomologyMap_apply_apply]
      rfl
    have he' : ∀ (V : Opens S) (hx : ι x ∈ V) (α : rationalCohomology (preimageSpace p V) q),
        e.hom ((higherDirectImageGerm p q (ι x) hx).hom α) =
          (rationalCohomologyMap (tubeFibreInclusion p hx) q).hom α := fun V hx α ↦
      ConcreteCategory.congr_hom (he V hx) α
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, fun τ ↦ ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro t ht
      obtain ⟨u, rfl⟩ := hσ.2 t
      obtain ⟨V, hx, α, rfl⟩ := exists_higherDirectImageGerm_eq p q (ι x) u
      rw [KF] at ht
      obtain ⟨V', hV', hxV', h0⟩ := exists_le_of_higherDirectImageGerm_eq_zero p' q hx _ ht
      have h2 : (rationalCohomologyMap (tubeFibreInclusion p' (V := (Opens.map ι).obj V) hx)
          q).hom ((rationalCohomologyMap (baseChangeTubeMap p ι g p' w V) q).hom α) = 0 := by
        have : tubeFibreInclusion p' (V := (Opens.map ι).obj V) hx =
            tubeFibreInclusion p' hxV' ≫ preimageInclusion p' hV' := TopCat.ext fun _ ↦ rfl
        rw [this, ← rationalCohomologyMap_apply_apply, h0, map_zero]
      rw [hfibα] at h2
      have h3 : (rationalCohomologyMap (tubeFibreInclusion p hx) q).hom α = 0 :=
        (injective_iff_map_eq_zero _).1 (hfib x).1 _ h2
      have h4 : (higherDirectImageGerm p q (ι x) hx).hom α = 0 :=
        e.toLinearEquiv.injective ((he' V hx α).trans (h3.trans (map_zero _).symm))
      rw [h4]
      exact map_zero _
    · obtain ⟨V0, hx0, β0, rfl⟩ := exists_higherDirectImageGerm_eq p' q x τ
      obtain ⟨c, hc⟩ := (hfib x).2 ((rationalCohomologyMap (tubeFibreInclusion p' hx0) q).hom β0)
      obtain ⟨V, hx, α, hα⟩ := exists_higherDirectImageGerm_eq p q (ι x) (e.inv c)
      have hαc : (rationalCohomologyMap (tubeFibreInclusion p hx) q).hom α = c := by
        rw [← he', hα]
        exact ConcreteCategory.congr_hom e.inv_hom_id c
      refine ⟨(stalkToPullbackStalk ι (higherDirectImage p q) x).hom
        ((higherDirectImageGerm p q (ι x) hx).hom α), ?_⟩
      rw [KF]
      let V1 : Opens W := (Opens.map ι).obj V ⊓ V0
      have hx1 : x ∈ V1 := ⟨hx, hx0⟩
      let β : rationalCohomology (preimageSpace p' ((Opens.map ι).obj V)) q :=
        (rationalCohomologyMap (baseChangeTubeMap p ι g p' w V) q).hom α
      let δ : rationalCohomology (preimageSpace p' V1) q :=
        (rationalCohomologyMap (preimageInclusion p' (inf_le_left : V1 ≤ _)) q).hom β -
          (rationalCohomologyMap (preimageInclusion p' (inf_le_right : V1 ≤ V0)) q).hom β0
      have e1 : tubeFibreInclusion p' hx1 ≫ preimageInclusion p' (inf_le_left : V1 ≤ _) =
          tubeFibreInclusion p' (V := (Opens.map ι).obj V) hx := TopCat.ext fun _ ↦ rfl
      have e2 : tubeFibreInclusion p' hx1 ≫ preimageInclusion p' (inf_le_right : V1 ≤ V0) =
          tubeFibreInclusion p' hx0 := TopCat.ext fun _ ↦ rfl
      have hδ : (rationalCohomologyMap (tubeFibreInclusion p' hx1) q).hom δ = 0 := by
        rw [map_sub, sub_eq_zero]
        refine (rationalCohomologyMap_apply_apply _ _ q β).trans ?_
        rw [e1]
        refine (hfibα V hx α).trans ?_
        rw [hαc, hc, rationalCohomologyMap_apply_apply, e2]
      obtain ⟨V2, hV2, hx2, h0⟩ := htaut x V1 hx1 δ hδ
      have h0' : (rationalCohomologyMap (preimageInclusion p' hV2) q).hom
            ((rationalCohomologyMap (preimageInclusion p' (inf_le_left : V1 ≤ _)) q).hom β) =
          (rationalCohomologyMap (preimageInclusion p' hV2) q).hom
            ((rationalCohomologyMap (preimageInclusion p' (inf_le_right : V1 ≤ V0)) q).hom β0) :=
        sub_eq_zero.1 ((map_sub _ _ _).symm.trans h0)
      have e3 : preimageInclusion p' (le_trans hV2 (inf_le_left : V1 ≤ _)) =
          preimageInclusion p' hV2 ≫ preimageInclusion p' (inf_le_left : V1 ≤ _) :=
        TopCat.ext fun _ ↦ rfl
      have e4 : preimageInclusion p' (le_trans hV2 (inf_le_right : V1 ≤ V0)) =
          preimageInclusion p' hV2 ≫ preimageInclusion p' (inf_le_right : V1 ≤ V0) :=
        TopCat.ext fun _ ↦ rfl
      have hβ := higherDirectImageGerm_res p' q (le_trans hV2 (inf_le_left : V1 ≤ _)) hx2 β
      have hβ0 := higherDirectImageGerm_res p' q (le_trans hV2 (inf_le_right : V1 ≤ V0)) hx2 β0
      rw [e3, ← rationalCohomologyMap_apply_apply] at hβ
      rw [e4, ← rationalCohomologyMap_apply_apply] at hβ0
      change (higherDirectImageGerm p' q x hx).hom β = _
      exact hβ.symm.trans ((congrArg (higherDirectImageGerm p' q x hx2).hom h0').trans hβ0)
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

end SheafLemmas

section ComplexPointLemmas

/-- The realization of a closed immersion `i : Z ⟶ W` is a closed embedding onto the
`ℂ`-points lying over the image of `i`. -/
private theorem realize_closedImmersion {Z W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} (i : Z ⟶ W)
    [IsClosedImmersion i] :
    IsClosedEmbedding (realize (sX := i ≫ sW) i rfl) ∧
      Set.range (realize (sX := i ≫ sW) i rfl) = {p | p.toScheme ∈ Set.range i} := by
  letI : W.Over (Spec (.of ℂ)) := ⟨sW⟩
  letI : Z.Over (Spec (.of ℂ)) := ⟨i ≫ sW⟩
  haveI : i.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have h : realize (sX := i ≫ sW) i rfl = (homeomorphUnderlyingSpace (X := W)).symm ∘
      MMP.UnderlyingSpace.map (K := ℂ) i ∘ homeomorphUnderlyingSpace (X := Z) :=
    rfl
  refine ⟨?_, ?_⟩
  · rw [h]
    exact (homeomorphUnderlyingSpace (X := W)).symm.isClosedEmbedding.comp
      ((MMP.UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion
        (K := ℂ) i).comp (homeomorphUnderlyingSpace (X := Z)).isClosedEmbedding)
  · ext p
    refine ⟨?_, fun hp ↦ ?_⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.toScheme, rfl⟩
    · have hp' : p ∈ (homeomorphUnderlyingSpace (X := W)) ⁻¹'
          Set.range (MMP.UnderlyingSpace.map (K := ℂ) i) := by
        rw [preimage_homeomorphUnderlyingSpace_range_map i]; exact hp
      obtain ⟨z, hz⟩ := hp'
      refine ⟨(homeomorphUnderlyingSpace (X := Z)).symm z, ?_⟩
      rw [h]
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply, hz]
      exact Homeomorph.symm_apply_apply _ _

/-- On a scheme locally of finite type over `ℂ`, a `ℂ`-point is determined by its image. -/
private theorem toScheme_injective {W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sW] : Function.Injective (toScheme : ComplexPoints sW → W) := by
  letI : W.Over (Spec (.of ℂ)) := ⟨sW⟩
  haveI : LocallyOfFiniteType (W ↘ Spec (.of ℂ)) := ‹_›
  intro a b hab
  have hab' : a.hom (IsLocalRing.closedPoint ℂ) = b.hom (IsLocalRing.closedPoint ℂ) := by
    have e1 : ∀ c : ComplexPoints sW, c.hom (IsLocalRing.closedPoint ℂ) = c.toScheme := fun c ↦
      congrArg c.hom (Subsingleton.elim _ _)
    rw [e1, e1, hab]
  have := (MMP.UnderlyingSpace.equivClosedPoints (K := ℂ) W).injective
    (a₁ := homeomorphUnderlyingSpace a) (a₂ := homeomorphUnderlyingSpace b)
    (Subtype.ext (by
      rw [MMP.UnderlyingSpace.equivClosedPoints_apply,
        MMP.UnderlyingSpace.equivClosedPoints_apply]
      exact hab'))
  exact (homeomorphUnderlyingSpace (X := W)).injective this

/-- A space openly embedded in a space with bases of open contractible neighbourhoods has such
bases. -/
private theorem hasOpenContractibleBasis_of_isOpenEmbedding {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (hB : MMP.HasOpenContractibleBasis B) {f : A → B}
    (hf : IsOpenEmbedding f) : MMP.HasOpenContractibleBasis A := by
  intro a
  refine ⟨fun t ↦ ⟨fun ht ↦ ?_, fun ⟨W, ⟨hW, haW, _⟩, hWt⟩ ↦
    Filter.mem_of_superset (hW.mem_nhds haW) hWt⟩⟩
  have ht' : f '' t ∈ 𝓝 (f a) := by
    rw [← hf.map_nhds_eq]; exact Filter.image_mem_map ht
  obtain ⟨W, ⟨hW, haW, hc⟩, hWt⟩ := (hB (f a)).mem_iff.1 ht'
  have hWr : W ⊆ Set.range f := hWt.trans (Set.image_subset_range _ _)
  refine ⟨f ⁻¹' W, ⟨hW.preimage hf.continuous, haW, ?_⟩, ?_⟩
  · haveI := hc
    exact ((hf.isEmbedding.homeomorphImage (f ⁻¹' W)).trans
      (Homeomorph.setCongr (Set.image_preimage_eq_of_subset hWr))).contractibleSpace
  · intro y hy
    obtain ⟨z, hz, hzy⟩ := hWt hy
    rwa [← hf.injective hzy]

/-- Points of `ℂ` have bases of open contractible neighbourhoods: small balls. -/
private theorem hasOpenContractibleBasis_complex : MMP.HasOpenContractibleBasis ℂ :=
  fun x ↦ Metric.nhds_basis_ball.to_hasBasis
    (fun ε hε ↦ ⟨Metric.ball x ε, ⟨Metric.isOpen_ball, Metric.mem_ball_self hε,
      (convex_ball x ε).contractibleSpace (Metric.nonempty_ball.2 hε)⟩, le_rfl⟩)
    (fun V ⟨hV, hxV, _⟩ ↦ by
      obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV x hxV
      exact ⟨ε, hε, hεV⟩)

/-- On a scheme locally of finite type over `ℂ`, the image of a `ℂ`-point is a closed point. -/
private theorem isClosed_singleton_toScheme {B : Scheme.{0}} (sB : B ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sB] (b : ComplexPoints sB) : IsClosed ({b.toScheme} : Set B) := by
  letI : B.Over (Spec (.of ℂ)) := ⟨sB⟩
  haveI : LocallyOfFiniteType (B ↘ Spec (.of ℂ)) := ‹_›
  have hpt : b.hom (IsLocalRing.closedPoint ℂ) = b.toScheme :=
    congrArg b.hom (Subsingleton.elim _ _)
  have := (MMP.UnderlyingSpace.equivClosedPoints (K := ℂ) B
    (homeomorphUnderlyingSpace b)).2
  rw [MMP.UnderlyingSpace.equivClosedPoints_apply] at this
  rw [← hpt]
  exact this

/-- For a morphism `t : X ⟶ B` of schemes locally of finite type over `ℂ` and a `ℂ`-point `b`
of `B`, the fibre `(t^an)⁻¹(b)` has bases of open contractible neighbourhoods: it is the set of
`ℂ`-points of the closed subset `t⁻¹(b)` of `X`. -/
private theorem hasOpenContractibleBasis_preimage_singleton {X B : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sB : B ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sB] (t : X ⟶ B) (ht : t ≫ sB = sX) (b : ComplexPoints sB) :
    MMP.HasOpenContractibleBasis (realize t ht ⁻¹' {b}) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : B.Over (Spec (.of ℂ)) := ⟨sB⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹_›
  haveI : LocallyOfFiniteType (B ↘ Spec (.of ℂ)) := ‹_›
  have hpt : ∀ {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} (c : ComplexPoints sW),
      c.hom (IsLocalRing.closedPoint ℂ) = c.toScheme := fun c ↦
    congrArg c.hom (Subsingleton.elim _ _)
  have hb := isClosed_singleton_toScheme sB b
  let Tb : Closeds X := ⟨t ⁻¹' {b.toScheme}, hb.preimage t.continuous⟩
  have h1 := MMP.Chow.hasOpenContractibleBasis_setOf_mem_closeds X Tb
  refine h1.of_homeomorph ((homeomorphUnderlyingSpace (X := X)).subtype ?_).symm
  intro p
  change realize t ht p = b ↔ (p.hom (IsLocalRing.closedPoint ℂ)) ∈ t ⁻¹' {b.toScheme}
  rw [hpt p]
  constructor
  · rintro rfl; rfl
  · intro hp; exact toScheme_injective sB hp

end ComplexPointLemmas

/-- The conclusion of `MMP.Fourfold.IsLocalSetting.exists_generic_trivializations` for a fixed
Zariski open `X`. -/
private def GenericTrivializationData {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (X : Y.Opens) : Prop :=
    ∃ (B : Scheme.{0}) (sB : B ⟶ Spec (.of ℂ)) (t : (X : Scheme.{0}) ⟶ B)
      (ht : t ≫ sB = X.ι ≫ sY) (β : ClosedBlowupSequence.{0} (π ⁻¹ᵁ X : Scheme.{0})),
      let sX : (X : Scheme.{0}) ⟶ Spec (.of ℂ) := X.ι ≫ sY
      let To : (curveScheme T).Opens := curveι T ⁻¹ᵁ X
      let iT : (To : Scheme.{0}) ⟶ X := curveι T ∣_ X
      let f : β.target ⟶ X := β.toBase ≫ π ∣_ X
      let Tc : Y.Opens := ⟨(T : Set Y)ᶜ, T.isClosed.isOpen_compl⟩
      let fan : analyticSpace (f ≫ sX) ⟶ analyticSpace sX := analyticMap f rfl
      let iTan : analyticSpace (iT ≫ sX) ⟶ analyticSpace sX := analyticMap iT rfl
      let tan : analyticSpace sX ⟶ analyticSpace sB := analyticMap t ht
      -- `B` is a smooth curve and `Z` a smooth variety, projective over `X`
      (MMP.Mori.IsVariety ℂ sB ∧ IsSmoothScheme sB ∧ topologicalKrullDim B = 1) ∧
      (MMP.Mori.IsVariety ℂ (f ≫ sX) ∧ IsSmoothScheme (f ≫ sX) ∧ IsProjectiveMorphism f) ∧
      -- (1)
      ((To : Set (curveScheme T)).Nonempty ∧ To ≤ smoothLocus (curveι T ≫ sY) ∧
        IsFinite (iT ≫ t) ∧ Etale (iT ≫ t) ∧
        (X : Set Y) ∩ smoothLocus sY = (X : Set Y) \ T) ∧
      -- (2)
      (β.IsSmooth (π ∣_ X ≫ sX) ∧ IsBiregular f (X.ι ⁻¹ᵁ Tc)) ∧
      -- (3)
      (∀ x : ComplexPoints (iT ≫ sX), ∃ W : Set (ComplexPoints (iT ≫ sX)),
        IsOpen W ∧ x ∈ W ∧ Nonempty (W ≃ₜ Metric.ball (0 : ℂ) 1) ∧
        ∃ Φ : (fan ⁻¹' {iTan x}) × W ≃ₜ (fan ⁻¹' (iTan '' W)),
          ∀ p, fan (Φ p) = iTan p.2) ∧
      -- (4)
      (∀ x : ComplexPoints (iT ≫ sX), ∃ N : Set (ComplexPoints sX), IsOpen N ∧ iTan x ∈ N ∧
        ∃ V : Set (ComplexPoints sX),
          (∃ O : Set (ComplexPoints sX), IsOpen O ∧ V = O ∩ tan ⁻¹' {tan (iTan x)}) ∧
          iTan x ∈ V ∧ V ∩ Set.range iTan = {iTan x} ∧
          ∃ Φ : N ≃ₜ V × Metric.ball (0 : ℂ) 1,
            ∀ n : N, (n : ComplexPoints sX) ∈ Set.range iTan ↔
              ((Φ n).1 : ComplexPoints sX) = iTan x) ∧
      -- (5)
      (∀ b : ComplexPoints sB,
        let Xb : Set Y := X.ι '' (t ⁻¹' {b.toScheme})
        let I := Scheme.IdealSheafData.vanishingIdeal ⟨closure Xb, isClosed_closure⟩
        let sP : I.subscheme ⟶ Spec (.of ℂ) := I.subschemeι ≫ sY
        IsReduced I.subscheme ∧ IsProjective sP ∧
        ∃ S : Closeds I.subscheme,
          (S : Set I.subscheme) = I.subschemeι ⁻¹' (Xbᶜ ∪ ((T : Set Y) ∩ Xb)) ∧
          singularLocus sP ≤ S ∧
          (∀ C ∈ irreducibleComponents I.subscheme, ¬ C ⊆ (S : Set I.subscheme)) ∧
          ∀ x : ComplexPoints sP, I.subschemeι x.toScheme ∈ (T : Set Y) ∩ Xb →
            x.toScheme ∈ S ∧
              𝓝[ComplexPoints.toScheme ⁻¹' (S : Set I.subscheme) \ {x}] x = ⊥)

/-- **The blowup retraction.** For the blowup `b : V' ⟶ V` of a smooth complex variety along a
smooth centre, and any continuous `p : V^an ⟶ T`, pullback of classes along `b` makes
`R^q p_* ℚ` a retract of `R^q (p ∘ b)_* ℚ`. -/
private theorem nonempty_retract_higherDirectImage_blowUp {V : Scheme.{0}} [IsIntegral V]
    (s : V ⟶ Spec (.of ℂ)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (Z : V.IdealSheafData) (hZ0 : Z ≠ ⊥) (hs : MMP.Mori.IsSmoothScheme s)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ s)) {T : TopCat.{0}} (p : analyticSpace s ⟶ T)
    (q : ℕ) :
    Nonempty (Retract (higherDirectImage p q)
      (higherDirectImage (analyticMap (sY := s) (blowUpToBase Z) rfl ≫ p) q)) := by
  obtain ⟨r⟩ := MMP.Fourfold.nonempty_retract_directImagePresheaf_blowUp s Z hZ0 hs hZ q
  exact ⟨(r.map (TopCat.Presheaf.pushforward (ModuleCat.{0} ℚ) p)).map
    (presheafToSheaf (Opens.grothendieckTopology T) (ModuleCat.{0} ℚ))⟩

/-- Along a smooth blowup sequence `β`, `R^q p_* ℚ` is a retract of `R^q (p ∘ β)_* ℚ`. -/
private theorem nonempty_retract_higherDirectImage_toBase : ∀ {V : Scheme.{0}} [IsIntegral V]
    (s : V ⟶ Spec (.of ℂ)) [IsSeparated s] [LocallyOfFiniteType s] [QuasiCompact s]
    (β : ClosedBlowupSequence.{0} V), β.IsSmooth s → Nonempty β.target →
    ∀ (s' : β.target ⟶ Spec (.of ℂ)) (hs' : β.toBase ≫ s = s') {T : TopCat.{0}}
      (p : analyticSpace s ⟶ T) (q : ℕ),
      Nonempty (Retract (higherDirectImage p q)
        (higherDirectImage (analyticMap β.toBase hs' ≫ p) q))
  | V, _, s, _, _, _, .nil _, _, _, s', hs', T, p, q => by
      obtain rfl : s' = s := hs'.symm.trans (Category.id_comp s)
      have hid : analyticMap (ClosedBlowupSequence.nil V).toBase hs' = 𝟙 _ := by
        ext x
        change x.hom ≫ 𝟙 V = x.hom
        exact Category.comp_id _
      rw [hid]
      exact ⟨Retract.ofIso (eqToIso (congrArg (higherDirectImage · q) (Category.id_comp p).symm))⟩
  | V, _, s, _, _, _, .cons Z B, hβ, hne, s', hs', T, p, q => by
      obtain ⟨hs, hZ, hB⟩ := hβ
      have hZ0 : Z ≠ ⊥ := by
        rintro rfl
        exact (isEmpty_blowUp_bot V).false (B.toBase hne.some)
      haveI : IsIntegral (blowUp Z) := isIntegral_blowUp Z hZ0
      haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian s
      haveI : IsProper (blowUpToBase Z) := AlgebraicGeometry.TwoStepTower.isProper_blowUpToBase
        (AlgebraicGeometry.TwoStepTower.isFiniteType_of_isLocallyNoetherian Z)
      obtain ⟨r1⟩ := nonempty_retract_higherDirectImage_blowUp s Z hZ0 hs hZ p q
      have hs'' : B.toBase ≫ (blowUpToBase Z ≫ s) = s' := by
        rwa [← Category.assoc]
      obtain ⟨r2⟩ := nonempty_retract_higherDirectImage_toBase (blowUpToBase Z ≫ s) B hB hne s' hs''
        (analyticMap (sY := s) (blowUpToBase Z) rfl ≫ p) q
      have hcomp : analyticMap B.toBase hs'' ≫ analyticMap (sY := s) (blowUpToBase Z) rfl ≫ p =
          analyticMap (ClosedBlowupSequence.cons Z B).toBase hs' ≫ p :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (analyticMap_comp _ _ _ _))
      rw [← hcomp]
      exact ⟨r1.trans r2⟩

/-- `R^q π_* ℚ`, restricted to `X`, is a direct summand of `R^q f_* ℚ` for `f = π ∘ β`: the
pullback along `β` has a retraction. -/
private theorem nonempty_retract_higherDirectImage {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {π : Yt ⟶ Y} (X : Y.Opens) (β : ClosedBlowupSequence.{0} (π ⁻¹ᵁ X : Scheme.{0}))
    [IsIntegral (π ⁻¹ᵁ X : Scheme.{0})] (hne : Nonempty β.target)
    (hβ : β.IsSmooth (π ∣_ X ≫ X.ι ≫ sY)) (hπ : MMP.Mori.IsSmoothScheme (π ≫ sY))
    (hπp : IsProjectiveMorphism π) [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    (q : ℕ) :
    Nonempty (Retract ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (analyticMap X.ι rfl)).obj
        (resolutionHigherDirectImage sY π q))
      (higherDirectImage (analyticMap (sY := X.ι ≫ sY) (β.toBase ≫ π ∣_ X) rfl) q)) := by
  let s0 : (π ⁻¹ᵁ X : Scheme.{0}) ⟶ Spec (.of ℂ) := π ∣_ X ≫ X.ι ≫ sY
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hπp
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsSeparated s0 := by dsimp only [s0]; infer_instance
  haveI : LocallyOfFiniteType s0 := by dsimp only [s0]; infer_instance
  haveI : QuasiCompact s0 := by dsimp only [s0]; infer_instance
  let pX : analyticSpace s0 ⟶ analyticSpace (X.ι ≫ sY) := analyticMap (π ∣_ X) rfl
  have hk : (π ⁻¹ᵁ X).ι ≫ π ≫ sY = s0 := by
    simp only [s0, ← Category.assoc, morphismRestrict_ι]
  let k : analyticSpace s0 ⟶ analyticSpace (π ≫ sY) := analyticMap (π ⁻¹ᵁ X).ι hk
  have hkemb : IsOpenEmbedding k := isOpenEmbedding_realize_of_isOpenImmersion _ hk
  have hXan : IsOpenEmbedding (analyticMap (sY := sY) X.ι rfl) := isOpenEmbedding_realize_ι X
  have w : pX ≫ analyticMap (sY := sY) X.ι rfl = k ≫ resolutionAnalyticMap sY π := by
    ext x
    change x.hom ≫ π ∣_ X ≫ X.ι = x.hom ≫ (π ⁻¹ᵁ X).ι ≫ π
    rw [morphismRestrict_ι]
  have hrange : Set.range k = resolutionAnalyticMap sY π ⁻¹'
      Set.range (analyticMap (sY := sY) X.ι rfl) := by
    change Set.range (realize _ hk) = _
    rw [range_realize_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
    ext a
    change a.toScheme ∈ π ⁻¹ᵁ X ↔ realize π rfl a ∈ Set.range (realize (sX := X.ι ≫ sY) X.ι rfl)
    rw [range_realize_ι]
    rfl
  let e := higherDirectImagePullbackIso (analyticMap (sY := sY) X.ι rfl) hXan
    (resolutionAnalyticMap sY π) k hkemb.isEmbedding pX w hrange q
  have hs' : β.toBase ≫ s0 = (β.toBase ≫ π ∣_ X) ≫ X.ι ≫ sY := by
    simp only [s0, Category.assoc]
  obtain ⟨r⟩ := nonempty_retract_higherDirectImage_toBase s0 β hβ hne _ hs' pX q
  have hcomp : analyticMap β.toBase hs' ≫ pX =
      analyticMap (sY := X.ι ≫ sY) (β.toBase ≫ π ∣_ X) rfl := by
    rw [analyticMap_comp]
  rw [← hcomp]
  exact ⟨(Retract.ofIso e).trans r⟩

/-- On the disks of part (3), the inverse image of `R^q f_* ℚ` is a local system. -/
private theorem exists_isLocalSystem_higherDirectImage_disk {X B To : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] [IsSeparated sX] (f : B ⟶ X)
    (hf : IsProjectiveMorphism f) (iT : To ⟶ X)
    [IsClosedImmersion iT] (q : ℕ) (x : ComplexPoints (iT ≫ sX))
    (h3 : ∃ W : Set (ComplexPoints (iT ≫ sX)),
        IsOpen W ∧ x ∈ W ∧ Nonempty (W ≃ₜ Metric.ball (0 : ℂ) 1) ∧
        ∃ Φ : (analyticMap (sY := sX) f rfl ⁻¹' {analyticMap (sY := sX) iT rfl x}) × W ≃ₜ
            (analyticMap (sY := sX) f rfl ⁻¹' (analyticMap (sY := sX) iT rfl '' W)),
          ∀ p, analyticMap (sY := sX) f rfl (Φ p) = analyticMap (sY := sX) iT rfl p.2) :
    ∃ W : Opens (analyticSpace (iT ≫ sX)), x ∈ W ∧
      LocallyConnectedSpace ((Opens.toTopCat _).obj W) ∧
      IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
        (W.inclusion' ≫ analyticMap (sY := sX) iT rfl)).obj
          (higherDirectImage (analyticMap (sY := sX) f rfl) q)) := by
  obtain ⟨W, hWo, hxW, ⟨ψ⟩, Φ, hΦ⟩ := h3
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf
  let p := analyticMap (sY := sX) f rfl
  let j := analyticMap (sY := sX) iT rfl
  have hj : Function.Injective j := (realize_closedImmersion (sW := sX) iT).1.injective
  let Wop : Opens (analyticSpace (iT ≫ sX)) := ⟨W, hWo⟩
  let Wt : TopCat.{0} := (Opens.toTopCat _).obj Wop
  let ψ' : Wt ≃ₜ Metric.ball (0 : ℂ) 1 := ψ
  haveI : LocallyConnectedSpace (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.locallyConnectedSpace
  have hlc : LocallyConnectedSpace Wt := ψ'.locallyConnectedSpace
  have hB : MMP.HasOpenContractibleBasis Wt :=
    (hasOpenContractibleBasis_of_isOpenEmbedding hasOpenContractibleBasis_complex
      Metric.isOpen_ball.isOpenEmbedding_subtypeVal).of_homeomorph ψ'.symm
  have hW : ∀ (w : Wt) (V : Set Wt), IsOpen V → w ∈ V →
      ∃ D : Set Wt, IsOpen D ∧ w ∈ D ∧ D ⊆ V ∧ ContractibleSpace D := by
    intro w V hV hwV
    obtain ⟨D, ⟨hD, hwD, hc⟩, hDV⟩ := (hB w).mem_iff.1 (hV.mem_nhds hwV)
    exact ⟨D, hD, hwD, hDV, hc⟩
  let K : TopCat.{0} := TopCat.of (p ⁻¹' {j x})
  let p' : TopCat.of (K × Wt) ⟶ Wt := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
  let ι : Wt ⟶ analyticSpace sX := Wop.inclusion' ≫ j
  let g : TopCat.of (K × Wt) ⟶ analyticSpace (f ≫ sX) :=
    TopCat.ofHom ⟨fun z ↦ (Φ z).1, continuous_subtype_val.comp Φ.continuous⟩
  have w : g ≫ p = p' ≫ ι := TopCat.ext fun z ↦ hΦ z
  have hfib : ∀ y : Wt,
      Function.Bijective (rationalCohomologyMap (baseChangeFibreMap p ι g p' w y) q).hom := by
    intro y
    have hmem : ∀ z : p ⁻¹' {ι y}, (z : analyticSpace (f ≫ sX)) ∈ p ⁻¹' (j '' W) := fun z ↦
      ⟨y.1, y.2, z.2.symm⟩
    have hsnd : ∀ z : p ⁻¹' {ι y}, (Φ.symm ⟨z.1, hmem z⟩).2 = y := by
      intro z
      apply Subtype.ext
      apply hj
      have := hΦ (Φ.symm ⟨z.1, hmem z⟩)
      rw [Homeomorph.apply_symm_apply] at this
      exact this.symm.trans z.2
    let inv : TopCat.of (p ⁻¹' {ι y}) ⟶ TopCat.of (p' ⁻¹' {y}) :=
      TopCat.ofHom ⟨fun z ↦ ⟨((Φ.symm ⟨z.1, hmem z⟩).1, y), rfl⟩, by
        refine Continuous.subtype_mk ?_ _
        exact (continuous_fst.comp (Φ.symm.continuous.comp
          ((continuous_subtype_val).subtype_mk _))).prodMk continuous_const⟩
    have h1 : baseChangeFibreMap p ι g p' w y ≫ inv = 𝟙 _ := by
      refine TopCat.ext fun u ↦ Subtype.ext (Prod.ext ?_ u.2.symm)
      change (Φ.symm ⟨(Φ u.1).1, _⟩).1 = u.1.1
      exact congrArg Prod.fst (Φ.symm_apply_apply u.1)
    have h2 : inv ≫ baseChangeFibreMap p ι g p' w y = 𝟙 _ := by
      refine TopCat.ext fun z ↦ Subtype.ext ?_
      change (Φ ((Φ.symm ⟨z.1, hmem z⟩).1, y)).1 = z.1
      have : ((Φ.symm ⟨z.1, hmem z⟩).1, y) = Φ.symm ⟨z.1, hmem z⟩ :=
        Prod.ext rfl (hsnd z).symm
      exact (congrArg (fun t ↦ (Φ t).1) this).trans
        (congrArg Subtype.val (Φ.apply_symm_apply ⟨z.1, hmem z⟩))
    refine Function.bijective_iff_has_inverse.2 ⟨(rationalCohomologyMap inv q).hom, ?_, ?_⟩
    · intro c
      rw [rationalCohomologyMap_apply_apply, h2, rationalCohomologyMap_id]
      rfl
    · intro c
      rw [rationalCohomologyMap_apply_apply, h1, rationalCohomologyMap_id]
      rfl
  have hiso := isIso_higherDirectImageBaseChange p ι g p' w q
    (fun y ↦ exists_stalk_higherDirectImage_iso f sX (ι y) q)
    (fun y V hV α hα ↦ taut_prod_snd K Wt hW q y V hV α hα) hfib
  obtain ⟨e2⟩ := nonempty_iso_constantSheaf_higherDirectImage_snd K Wt hW q
  have hfd : FiniteDimensional ℚ (rationalCohomology K q) :=
    finiteDimensional_rationalCohomology_preimage_singleton f sX hf (j x) q
  refine ⟨Wop, hxW, hlc, fun y ↦ ⟨⊤, trivial, rationalCohomology K q, hfd, ⟨?_⟩⟩⟩
  exact (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (⊤ : Opens Wt).inclusion').mapIso
      (asIso (higherDirectImageBaseChange p ι g p' w q) ≪≫ e2) ≪≫
    (pullbackConstIso _).app _

/-- The local-system half of part (a) on an open `U ≤ T ∩ X`: near each point, `R^q π_* ℚ` is a
retract of `R^q f_* ℚ` (`nonempty_retract_higherDirectImage`), which is a local system on the
disks of part (3) (`exists_isLocalSystem_higherDirectImage_disk`); a retract of a local system on
a locally connected space is one (`MMP.Fourfold.IsLocalSystem.of_retract`). -/
private theorem isLocalSystem_resolution_clause {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (h : IsLocalSetting sY Θ T π)
    (X : Y.Opens)
    (hX : GenericTrivializationData (sY := sY) (π := π) (T := T) X)
    (U : (curveScheme T).Opens) (hU : U ≤ curveι T ⁻¹ᵁ X) (q : ℕ) :
    IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY U)).obj
      (resolutionHigherDirectImage sY π q)) := by
  obtain ⟨B, sB, t, ht, β, -, ⟨hfvar, -, hfp⟩, -, ⟨hβ, -⟩, h3, -, -⟩ := hX
  haveI : IsIntegral β.target := hfvar.toIsIntegral
  have hne : Nonempty β.target := inferInstance
  haveI : IsIntegral Yt := h.isResolution.2.1.toIsIntegral
  haveI : Nonempty (π ⁻¹ᵁ X : Scheme.{0}) := ⟨β.toBase hne.some⟩
  let sX : (X : Scheme.{0}) ⟶ Spec (.of ℂ) := X.ι ≫ sY
  let iT : (curveι T ⁻¹ᵁ X : Scheme.{0}) ⟶ X := curveι T ∣_ X
  let iTan : analyticSpace (iT ≫ sX) ⟶ analyticSpace sX := analyticMap iT rfl
  let Xan : analyticSpace sX ⟶ analyticSpace sY := analyticMap X.ι rfl
  have hκ : (curveScheme T).homOfLE hU ≫ iT ≫ sX = U.ι ≫ curveι T ≫ sY := by
    simp only [iT, sX, ← Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
  let κ : analyticSpace (U.ι ≫ curveι T ≫ sY) ⟶ analyticSpace (iT ≫ sX) := analyticMap _ hκ
  have hcoi : curveOpenInclusion sY U = κ ≫ iTan ≫ Xan := by
    ext z
    change z.hom ≫ U.ι ≫ curveι T = z.hom ≫ (curveScheme T).homOfLE hU ≫ iT ≫ X.ι
    simp only [iT, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  haveI : AlgebraicGeometry.IsVariety ℂ sY := h.isProjectiveVariety.toIsVariety
  obtain ⟨r⟩ := nonempty_retract_higherDirectImage (sY := sY) X β hne hβ
    h.isResolution.2.2.1 h.isResolution.2.2.2.1 q
  apply isLocalSystem_of_isOpenEmbedding_cover
  intro z
  haveI : LocallyOfFiniteType sX := by dsimp only [sX]; infer_instance
  haveI : IsSeparated sX := by dsimp only [sX]; infer_instance
  obtain ⟨W, hzW, hWlc, hWls⟩ := exists_isLocalSystem_higherDirectImage_disk (sX := sX)
    (β.toBase ≫ π ∣_ X) hfp iT q (κ z) (h3 (κ z))
  haveI := hWlc
  have hR : IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (W.inclusion' ≫ iTan)).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) Xan).obj (resolutionHigherDirectImage sY π q))) :=
    IsLocalSystem.of_retract (r.map (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) _)) hWls
  let Z : TopCat.{0} := TopCat.of (κ ⁻¹' (W : Set (analyticSpace (iT ≫ sX))))
  let e : Z ⟶ analyticSpace (U.ι ≫ curveι T ≫ sY) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have he : IsOpenEmbedding e :=
    (W.isOpen.preimage κ.hom.continuous).isOpenEmbedding_subtypeVal
  let g : Z ⟶ (Opens.toTopCat _).obj W :=
    TopCat.ofHom ⟨fun y ↦ ⟨κ y.1, y.2⟩, by fun_prop⟩
  have hfac : e ≫ curveOpenInclusion sY U = g ≫ (W.inclusion' ≫ iTan) ≫ Xan := by
    rw [hcoi]; rfl
  refine ⟨Z, e, he, ⟨⟨z, hzW⟩, rfl⟩, ?_⟩
  exact isLocalSystem_of_iso (isLocalSystem_pullback g hR)
    ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) g).mapIso
        ((pullbackCompIso (W.inclusion' ≫ iTan) Xan).app _) ≪≫
      (pullbackCompIso g ((W.inclusion' ≫ iTan) ≫ Xan)).app _ ≪≫ eqToIso (by rw [hfac]) ≪≫
      (pullbackCompIso e (curveOpenInclusion sY U)).symm.app _)

/-- Part (a) on an open `U ≤ T ∩ X`: the local system, and the stalk formula, which is
`MMP.Fourfold.exists_stalk_higherDirectImage_iso` transported along the stalk of the inverse
image. -/
private theorem resolution_clause {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (h : IsLocalSetting sY Θ T π)
    (X : Y.Opens)
    (hX : GenericTrivializationData (sY := sY) (π := π) (T := T) X)
    (U : (curveScheme T).Opens) (hU : U ≤ curveι T ⁻¹ᵁ X) (q : ℕ) :
        (IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY U)).obj
            (resolutionHigherDirectImage sY π q)) ∧
          ∀ x : analyticSpace (U.ι ≫ curveι T ≫ sY),
            let y := curveOpenInclusion sY U x
            ∃ e : ((TopCat.Sheaf.forget _ _).obj
                ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY U)).obj
                  (resolutionHigherDirectImage sY π q))).stalk x ≅
                rationalCohomology (TopCat.of (resolutionAnalyticMap sY π ⁻¹' {y})) q,
              ∀ (V : Opens (analyticSpace sY)) (hy : y ∈ V),
                higherDirectImageGerm (resolutionAnalyticMap sY π) q y hy ≫
                    stalkToPullbackStalk (curveOpenInclusion sY U)
                      (resolutionHigherDirectImage sY π q) x ≫ e.hom =
                  rationalCohomologyMap
                    (TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono
                      (Set.singleton_subset_iff.2 hy)), continuous_inclusion _⟩) q) := by
  refine ⟨isLocalSystem_resolution_clause h X hX U hU q, fun x ↦ ?_⟩
  haveI : AlgebraicGeometry.IsVariety ℂ sY := h.isProjectiveVariety.toIsVariety
  haveI : IsProper π := isProper_of_isProjectiveMorphism _ h.isResolution.2.2.2.1
  obtain ⟨e, he⟩ : ∃ e : ((TopCat.Sheaf.forget _ _).obj
        (resolutionHigherDirectImage sY π q)).stalk (curveOpenInclusion sY U x) ≅
      rationalCohomology (TopCat.of (resolutionAnalyticMap sY π ⁻¹'
        {curveOpenInclusion sY U x})) q,
      ∀ (V : Opens (analyticSpace sY)) (hy : curveOpenInclusion sY U x ∈ V),
        higherDirectImageGerm (resolutionAnalyticMap sY π) q _ hy ≫ e.hom =
          rationalCohomologyMap (TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono
            (Set.singleton_subset_iff.2 hy)), continuous_inclusion _⟩) q :=
    exists_stalk_higherDirectImage_iso π sY (curveOpenInclusion sY U x) q
  haveI := isIso_stalkToPullbackStalk (curveOpenInclusion sY U)
    (resolutionHigherDirectImage sY π q) x
  refine ⟨(asIso (stalkToPullbackStalk (curveOpenInclusion sY U)
    (resolutionHigherDirectImage sY π q) x)).symm ≪≫ e, fun V hy ↦ ?_⟩
  simpa only [Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc] using he V hy

/-- A point of `X` lies in the range of the restriction of `T ⟶ Y` over `X` iff its image in
`Y` lies in `T`. -/
private theorem mem_range_curveι_restrict_iff {Y : Scheme.{0}} (T : IrreducibleCloseds Y)
    (X : Y.Opens) (p : (X : Scheme.{0})) :
    p ∈ Set.range (curveι T ∣_ X) ↔ X.ι p ∈ (T : Set Y) := by
  have hrangeT : Set.range (curveι T) = (T : Set Y) := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hiTpt : ∀ y, X.ι ((curveι T ∣_ X) y) = curveι T ((curveι T ⁻¹ᵁ X).ι y) := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro ⟨y, rfl⟩
    rw [hiTpt, ← hrangeT]
    exact ⟨_, rfl⟩
  · rw [← hrangeT] at hp
    obtain ⟨c, hc⟩ := hp
    have hcX : c ∈ Set.range (curveι T ⁻¹ᵁ X).ι := by
      rw [Scheme.Opens.range_ι]
      change curveι T c ∈ (X : Set Y)
      rw [hc, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    obtain ⟨y, rfl⟩ := hcX
    refine ⟨y, X.ι.isOpenEmbedding.injective ?_⟩
    rw [hiTpt]
    exact hc

/-- Part (b) on an open `U ≤ T ∩ X`: near a point `x`, the product chart `N ≃ V × Δ` of part (4)
carries `R^q j_* ℚ_{Y_reg}` to the direct image along `(V ∖ {x}) × Δ ⟶ V × Δ`, which is constant
along `{x} × Δ` by `MMP.Fourfold.exists_iso_constantSheaf_pullback_higherDirectImage_prod_ball`.
Its local contractibility hypothesis holds since `V` is open in the analytic fibre `t⁻¹(b)`, and
its finiteness hypothesis is `MMP.Fourfold.exists_cofinal_isIso_punctured_cohomology_of_isolated`
on the projective closure `P_b` of part (5), into which `V` embeds openly. -/
private theorem regular_clause {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (h : IsLocalSetting sY Θ T π)
    (X : Y.Opens)
    (hX : GenericTrivializationData (sY := sY) (π := π) (T := T) X)
    (U : (curveScheme T).Opens) (hU : U ≤ curveι T ⁻¹ᵁ X) (q : ℕ) :
        IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY U)).obj
          (regularHigherDirectImage sY q)) := by
  obtain ⟨B, sB, t, ht, β, ⟨hBvar, -, -⟩, -, ⟨-, -, -, -, hreg⟩, -, -, h4, h5⟩ := hX
  let sX : (X : Scheme.{0}) ⟶ Spec (.of ℂ) := X.ι ≫ sY
  haveI : AlgebraicGeometry.IsVariety ℂ sY := h.isProjectiveVariety.toIsVariety
  haveI : LocallyOfFiniteType sB := hBvar.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX := by dsimp only [sX]; infer_instance
  let iT : (curveι T ⁻¹ᵁ X : Scheme.{0}) ⟶ X := curveι T ∣_ X
  let iTan : analyticSpace (iT ≫ sX) ⟶ analyticSpace sX := analyticMap iT rfl
  let Xan : analyticSpace sX ⟶ analyticSpace sY := analyticMap X.ι rfl
  have hκ : (curveScheme T).homOfLE hU ≫ iT ≫ sX = U.ι ≫ curveι T ≫ sY := by
    simp only [iT, sX, ← Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
  let κ : analyticSpace (U.ι ≫ curveι T ≫ sY) ⟶ analyticSpace (iT ≫ sX) := analyticMap _ hκ
  have hcoi : curveOpenInclusion sY U = κ ≫ iTan ≫ Xan := by
    ext z
    change z.hom ≫ U.ι ≫ curveι T = z.hom ≫ (curveScheme T).homOfLE hU ≫ iT ≫ X.ι
    simp only [iT, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  have hXan : IsOpenEmbedding Xan := isOpenEmbedding_realize_ι X
  have hiTan := realize_closedImmersion (sW := sX) iT
  have hsmooth : ∀ n : ComplexPoints sX,
      (Xan n).toScheme ∈ smoothLocus sY ↔ n ∉ Set.range iTan := by
    intro n
    have hrange' : n ∈ Set.range iTan ↔ X.ι n.toScheme ∈ (T : Set Y) := by
      change n ∈ Set.range (realize iT rfl) ↔ _
      rw [hiTan.2]
      exact mem_range_curveι_restrict_iff T X _
    rw [hrange']
    change X.ι n.toScheme ∈ smoothLocus sY ↔ _
    have hXn : X.ι n.toScheme ∈ (X : Set Y) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    exact ⟨fun hs ↦ (hreg.le ⟨hXn, hs⟩).2, fun hs ↦ (hreg.ge ⟨hXn, hs⟩).2⟩
  apply isLocalSystem_of_isOpenEmbedding_cover
  intro x
  obtain ⟨N, hN, hxN, V, hVO, hxV, hVT, Φ, hΦ⟩ := h4 (κ x)
  let VT : TopCat.{0} := TopCat.of V
  let x0 : VT := ⟨iTan (κ x), hxV⟩
  haveI : MetrizableSpace VT := by
    have := (metrizableSpace_and_stronglyLocallyContractibleSpace sY).1
    exact (hXan.isEmbedding.comp IsEmbedding.subtypeVal).metrizableSpace
  obtain ⟨O, hO, hVO⟩ := hVO
  have hVc : ∀ y : VT, y ≠ x0 → ∀ W ∈ 𝓝 y,
      ∃ W' : Set VT, IsOpen W' ∧ y ∈ W' ∧ W' ⊆ W ∧ ContractibleSpace W' := by
    let F : Set (ComplexPoints sX) := realize t ht ⁻¹' {realize t ht (iTan (κ x))}
    have hF : MMP.HasOpenContractibleBasis F :=
      hasOpenContractibleBasis_preimage_singleton t ht _
    have hVF : V ⊆ F := by rw [hVO]; exact Set.inter_subset_right
    have hemb : IsOpenEmbedding (Set.inclusion hVF) := ⟨IsEmbedding.inclusion hVF, by
      rw [Set.range_inclusion]
      have : {y : F | (y : ComplexPoints sX) ∈ V} = Subtype.val ⁻¹' O := by
        ext y
        rw [hVO]
        exact ⟨fun hy ↦ hy.1, fun hy ↦ ⟨hy, y.2⟩⟩
      rw [this]
      exact hO.preimage continuous_subtype_val⟩
    have hVT := hasOpenContractibleBasis_of_isOpenEmbedding hF hemb
    intro y _ W hW
    obtain ⟨W', ⟨hW', hyW', hc⟩, hW'W⟩ := (hVT y).mem_iff.1 hW
    exact ⟨W', hW', hyW', hW'W, hc⟩
  let j0 : TopCat.of ({x0}ᶜ : Set VT) ⟶ VT := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hfin : FiniteDimensional ℚ ((directImagePresheaf j0 q).stalk x0) := by
    let b : ComplexPoints sB := realize t ht (iTan (κ x))
    obtain ⟨hred, hproj, S, -, hSing, hcomp, hiso⟩ := h5 b
    let Xb : Set Y := X.ι '' (t ⁻¹' {b.toScheme})
    let I := Scheme.IdealSheafData.vanishingIdeal (⟨closure Xb, isClosed_closure⟩ : Closeds Y)
    let sP : I.subscheme ⟶ Spec (.of ℂ) := I.subschemeι ≫ sY
    haveI : IsReduced I.subscheme := hred
    have hXb : ∀ p : (X : Scheme.{0}), X.ι p ∈ closure Xb → t p = b.toScheme := by
      intro p hp
      have hcl : IsClosed (t ⁻¹' {b.toScheme}) :=
        (isClosed_singleton_toScheme sB b).preimage t.continuous
      have := X.ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
        (t ⁻¹' {b.toScheme})
      rw [hcl.closure_eq] at this
      exact this.ge hp
    have hrangeI : Set.range I.subschemeι = closure Xb := by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hρ := realize_closedImmersion (sW := sY) I.subschemeι
    let ρ := realize (sX := I.subschemeι ≫ sY) I.subschemeι rfl
    have hVF : ∀ v ∈ V, t v.toScheme = b.toScheme := fun v hv ↦ by
      have hv' : v ∈ O ∩ _ := hVO ▸ hv
      exact congrArg ComplexPoints.toScheme hv'.2
    have hmem : ∀ v : VT, Xan v.1 ∈ Set.range ρ := fun v ↦ by
      rw [hρ.2]
      show (Xan v.1).toScheme ∈ Set.range I.subschemeι
      rw [hrangeI]
      exact subset_closure ⟨v.1.toScheme, hVF v.1 v.2, rfl⟩
    let E := hρ.1.isEmbedding.toHomeomorph
    let e : VT ⟶ Analytification.space sP :=
      TopCat.ofHom ⟨fun v ↦ E.symm ⟨Xan v.1, hmem v⟩,
        E.symm.continuous.comp ((Xan.hom.continuous.comp continuous_subtype_val).subtype_mk _)⟩
    have heρ : ∀ v : VT, ρ (e v) = Xan v.1 := fun v ↦
      congrArg Subtype.val (E.apply_symm_apply ⟨Xan v.1, hmem v⟩)
    have he : IsOpenEmbedding e := by
      refine ⟨?_, ?_⟩
      · rw [← hρ.1.isEmbedding.of_comp_iff]
        have : ρ ∘ e = Xan ∘ Subtype.val := funext heρ
        rw [this]
        exact hXan.isEmbedding.comp IsEmbedding.subtypeVal
      · have : Set.range e = ρ ⁻¹' (Xan '' O) := by
          ext p
          refine ⟨?_, fun hp ↦ ?_⟩
          · rintro ⟨v, rfl⟩
            have hVO' : ∀ y, y ∈ V → y ∈ O := fun y hy ↦ by rw [hVO] at hy; exact hy.1
            exact ⟨v.1, hVO' _ v.2, (heρ v).symm⟩
          · obtain ⟨o, ho, hop⟩ := hp
            have hoF : t o.toScheme = b.toScheme := by
              apply hXb
              have h1 : (ρ p).toScheme ∈ Set.range I.subschemeι := ⟨p.toScheme, rfl⟩
              rwa [hrangeI, ← hop] at h1
            have hoV : o ∈ V := by
              rw [hVO]
              exact ⟨ho, toScheme_injective sB hoF⟩
            exact ⟨⟨o, hoV⟩, hρ.1.injective ((heρ _).trans hop)⟩
        rw [this]
        exact (hXan.isOpenMap O hO).preimage hρ.1.continuous
    have hp0 : I.subschemeι (e x0).toScheme ∈ (T : Set Y) ∩ Xb := by
      have h1 : I.subschemeι (e x0).toScheme = X.ι x0.1.toScheme :=
        congrArg ComplexPoints.toScheme (heρ x0)
      rw [h1]
      exact ⟨(mem_range_curveι_restrict_iff T X _).1 ⟨(κ x).toScheme, rfl⟩, x0.1.toScheme,
        rfl, rfl⟩
    obtain ⟨hxS, hx⟩ := hiso (e x0) hp0
    obtain ⟨-, -, -, -, hfd⟩ := exists_cofinal_isIso_punctured_cohomology_of_isolated sP hproj S
      hSing hcomp (e x0) hxS hx
    haveI := hfd q
    exact LinearEquiv.finiteDimensional
      (puncturedStalkIsoOfIsOpenEmbedding e he x0 q).toLinearEquiv
  let M : TopCat.{0} := TopCat.of (VT × Metric.ball (0 : ℂ) 1)
  let eM : M ⟶ analyticSpace sY := TopCat.ofHom ⟨fun m ↦ Xan (Φ.symm m).1,
    Xan.hom.continuous.comp (continuous_subtype_val.comp Φ.symm.continuous)⟩
  have heM : IsOpenEmbedding eM :=
    hXan.comp (hN.isOpenEmbedding_subtypeVal.comp Φ.symm.isOpenEmbedding)
  let jreg := regularInclusion sY
  have hjreg : IsOpenEmbedding jreg := isOpenEmbedding_realize_ι _
  have hjrange : Set.range jreg = {y | y.toScheme ∈ smoothLocus sY} := range_realize_ι _
  let A' : TopCat.{0} := TopCat.of (({x0}ᶜ : Set VT) × Metric.ball (0 : ℂ) 1)
  let j' : A' ⟶ M := TopCat.ofHom ⟨fun w ↦ (w.1.1, w.2), by fun_prop⟩
  have hNreg : ∀ n : N, (Xan n).toScheme ∈ smoothLocus sY ↔ (Φ n).1 ≠ x0 := by
    intro n
    rw [hsmooth, not_iff_not, hΦ n]
    exact ⟨fun h' ↦ Subtype.ext h', fun h' ↦ congrArg Subtype.val h'⟩
  have hmem : ∀ w : A', eM (j' w) ∈ Set.range jreg := by
    intro w
    rw [hjrange]
    change (Xan (Φ.symm (w.1.1, w.2)).1).toScheme ∈ smoothLocus sY
    rw [hNreg, Homeomorph.apply_symm_apply]
    exact w.1.2
  let k : A' ⟶ analyticSpace ((smoothLocus sY).ι ≫ sY) :=
    TopCat.ofHom ⟨fun w ↦ hjreg.isEmbedding.toHomeomorph.symm ⟨eM (j' w), hmem w⟩,
      hjreg.isEmbedding.toHomeomorph.symm.continuous.comp
        ((eM.hom.continuous.comp j'.hom.continuous).subtype_mk _)⟩
  have hkj : ∀ w : A', jreg (k w) = eM (j' w) := fun w ↦
    congrArg Subtype.val (hjreg.isEmbedding.toHomeomorph.apply_symm_apply ⟨eM (j' w), hmem w⟩)
  have hw : j' ≫ eM = k ≫ jreg := TopCat.ext fun w ↦ (hkj w).symm
  have hk : IsEmbedding k := by
    rw [← hjreg.isEmbedding.of_comp_iff]
    have : (jreg ∘ k) = eM ∘ j' := funext hkj
    rw [this]
    exact heM.isEmbedding.comp (IsEmbedding.subtypeVal.prodMap IsEmbedding.id)
  have hrange : Set.range k = jreg ⁻¹' Set.range eM := by
    ext a
    refine ⟨?_, fun ha ↦ ?_⟩
    · rintro ⟨w, rfl⟩
      exact ⟨j' w, (hkj w).symm⟩
    · obtain ⟨m, hm⟩ := ha
      have ha' : jreg a ∈ Set.range jreg := ⟨a, rfl⟩
      rw [hjrange, ← hm] at ha'
      have hm1 : m.1 ≠ x0 := by
        have := (hNreg (Φ.symm m)).1 ha'
        rwa [Homeomorph.apply_symm_apply] at this
      refine ⟨(⟨m.1, hm1⟩, m.2), hjreg.injective ?_⟩
      rw [hkj]
      exact hm
  have hpp := (exists_iso_constantSheaf_pullback_higherDirectImage_prod_ball VT x0 hVc 0 1 q).2.2
    hfin
  let i : TopCat.of (Metric.ball (0 : ℂ) 1) ⟶ M := TopCat.ofHom ⟨fun s ↦ (x0, s), by fun_prop⟩
  have hG : IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (i ≫ eM)).obj
      (regularHigherDirectImage sY q)) :=
    isLocalSystem_of_iso hpp ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) i).mapIso
      (higherDirectImagePullbackIso eM heM jreg k hk j' hw hrange q).symm ≪≫
        (pullbackCompIso i eM).app _)
  let Z : TopCat.{0} := TopCat.of ((κ ≫ iTan) ⁻¹' (N : Set (ComplexPoints sX)))
  let e : Z ⟶ analyticSpace (U.ι ≫ curveι T ≫ sY) :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have he : IsOpenEmbedding e :=
    (hN.preimage (κ ≫ iTan).hom.continuous).isOpenEmbedding_subtypeVal
  let g : Z ⟶ TopCat.of (Metric.ball (0 : ℂ) 1) :=
    TopCat.ofHom ⟨fun z ↦ (Φ ⟨iTan (κ z.1), z.2⟩).2, by
      refine continuous_snd.comp (Φ.continuous.comp ?_)
      exact ((κ ≫ iTan).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  have hfac : e ≫ curveOpenInclusion sY U = g ≫ i ≫ eM := by
    refine TopCat.ext fun z ↦ ?_
    let n : N := ⟨iTan (κ z.1), z.2⟩
    have hn : ((x0, (Φ n).2) : VT × Metric.ball (0 : ℂ) 1) = Φ n :=
      Prod.ext (Subtype.ext ((hΦ n).1 ⟨κ z.1, rfl⟩).symm) rfl
    change curveOpenInclusion sY U z.1 = Xan (Φ.symm (x0, (Φ n).2)).1
    rw [hn, Homeomorph.symm_apply_apply, hcoi]
    rfl
  refine ⟨Z, e, he, ⟨⟨x, hxN⟩, rfl⟩, ?_⟩
  exact isLocalSystem_of_iso (isLocalSystem_pullback g hG)
    ((pullbackCompIso g (i ≫ eM)).app _ ≪≫ eqToIso (by rw [hfac]) ≪≫
      (pullbackCompIso e (curveOpenInclusion sY U)).symm.app _)

end Proof_thm_mmp_curvels_generic_local_systems

end

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints

/-- **Generic local systems along a singular curve.** For a local setting `(Y, Θ, T, π)` there
is a nonempty Zariski open `T°` of the curve `T`, inside its smooth locus, such that for every
Zariski open `U ≤ T°` and every `q`:
* `(R^q π_* ℚ_Ỹ)|_U` is a local system on `U^an`, and its stalk at `x` maps isomorphically to
  `H^q(π⁻¹(x); ℚ)` by restriction of classes;
* `(R^q j_* ℚ_{Y_reg})|_U` is a local system on `U^an`. -/
@[mmp "thm_mmp_curvels_generic_local_systems"]
public theorem IsLocalSetting.exists_isLocalSystem_higherDirectImage {Y Yt : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {sY : Y ⟶ Spec (.of ℂ)}
    {Θ : QDivisor Y} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} (h : IsLocalSetting sY Θ T π) :
    ∃ To : (curveScheme T).Opens,
      (To : Set (curveScheme T)).Nonempty ∧ To ≤ smoothLocus (curveι T ≫ sY) ∧
      ∀ U : (curveScheme T).Opens, U ≤ To → ∀ q : ℕ,
        (IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY U)).obj
            (resolutionHigherDirectImage sY π q)) ∧
          ∀ x : analyticSpace (U.ι ≫ curveι T ≫ sY),
            let y := curveOpenInclusion sY U x
            ∃ e : ((TopCat.Sheaf.forget _ _).obj
                ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY U)).obj
                  (resolutionHigherDirectImage sY π q))).stalk x ≅
                rationalCohomology (TopCat.of (resolutionAnalyticMap sY π ⁻¹' {y})) q,
              ∀ (V : Opens (analyticSpace sY)) (hy : y ∈ V),
                higherDirectImageGerm (resolutionAnalyticMap sY π) q y hy ≫
                    stalkToPullbackStalk (curveOpenInclusion sY U)
                      (resolutionHigherDirectImage sY π q) x ≫ e.hom =
                  rationalCohomologyMap
                    (TopCat.ofHom ⟨Set.inclusion (Set.preimage_mono
                      (Set.singleton_subset_iff.2 hy)), continuous_inclusion _⟩) q) ∧
        IsLocalSystem ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) (curveOpenInclusion sY U)).obj
          (regularHigherDirectImage sY q)) := by
  obtain ⟨X, hX⟩ := h.exists_generic_trivializations
  have hX' : Proof_thm_mmp_curvels_generic_local_systems.GenericTrivializationData
      (sY := sY) (π := π) (T := T) X := hX
  obtain ⟨B, sB, t, ht, β, -, -, ⟨hne, hsm, -⟩, -⟩ := hX
  exact ⟨curveι T ⁻¹ᵁ X, hne, hsm, fun U hU q ↦
    ⟨Proof_thm_mmp_curvels_generic_local_systems.resolution_clause h X hX' U hU q,
      Proof_thm_mmp_curvels_generic_local_systems.regular_clause h X hX' U hU q⟩⟩

end MMP.Fourfold
