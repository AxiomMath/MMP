module
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LargeModuleUniverse
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.AmpleRestrict
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilySubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorListGenerator
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.CechDerivedSupportImmersion

/-!
# Norms along a finite étale cover average first Chern classes

Let `(Y, Θ, T, π)` be a local setting (`MMP.Fourfold.IsLocalSetting`), `T° ⊆ T` a `π`-adapted
open (`MMP.Fourfold.IsAdaptedOpen`) with family `𝓕 = Ỹ ×_Y T° ⟶ T°`, and `t ∈ T°(ℂ)`. Let `G` be
the monodromy image of `π₁(T°, t)` in `GL(𝒲_t)`, `𝒲` the resolution local system, and assume `G`
finite. Let `φ : T' ⟶ T°` be a connected finite étale cover, `t' ∈ T'(ℂ)` over `t`, and `𝓛'` a
line bundle on `𝓕' = 𝓕 ×_{T°} T'` whose restriction to the sheet `F_t × {t'}` has first Chern
class `c ∈ 𝒲_t`. Then the norm `Nm 𝓛'` along the finite locally free projection `𝓕' ⟶ 𝓕`
satisfies
`c₁((Nm 𝓛')|_{F_t}) = d · Av_G(c)`, `Av_G(c) = |G|⁻¹ ∑_{g ∈ G} g c`,
where `d = [π₁(T°, t) : H]` is the number of sheets of `φ` over `t`.

## Main definitions

* `MMP.Fourfold.IsRealized`: a class on `F_t` and a germ in `𝒲_t` come from one class on a
  neighbourhood of `F_t`.

## Main results

* `MMP.Fourfold.pointFibreChernClass_normInvertible_eq_smul_average`.
* `MMP.Fourfold.finite_sections`: a finite scheme over `ℂ` has finitely many `ℂ`-points.
* `MMP.Fourfold.isRealized_zero`, `MMP.Fourfold.IsRealized.add`, `MMP.Fourfold.IsRealized.smul`:
  realized pairs form a `ℚ`-subspace; `MMP.Fourfold.IsRealized.unique`: the class on `F_t`
  determines the germ.

## Implementation notes

* The norm is `Stacks.Divisors.normInvertible` for the canonical determinant norm
  `Stacks.Norm.finiteLocallyFreeNorm` of the finite locally free projection `𝓕' ⟶ 𝓕`.
* The monodromy image `G` is described by parallel transport: an endomorphism `g` of `𝒲_t` lies
  in `G` when it is the transport along some loop `γ` at `t`, that is, whenever a global section
  of the pullback `γ^* 𝒲` to `[0, 1]` has germ `w` at `0` and germ `v` at `1`, then `g w = v`.
  The set of transports is closed under inverses, so the convention for the action of a loop does
  not affect `G` nor the average.
* The index `d = [Γ : H]` of the stabilizer of the sheet `t'` is the cardinality of the fibre of
  `φ` over `t`, the fibre of a connected covering being a transitive `Γ`-set with stabilizer `H`.
* A class in `𝒲_t` is attached to a line bundle on `F_t` as for
  `MMP.Fourfold.IsPuncturedIndependent`: it is the germ of a class `α ∈ H²(π⁻¹(V); ℚ)`, on a
  neighbourhood `V` of `t`, restricting to the first Chern class on `F_t`. By proper base change
  the restriction `𝒲_t ⟶ H²(F_t; ℚ)` is an isomorphism, so this is the source's identification.
* The sheet `F_t × {t'}` is `F_t`, mapped into `𝓕'` by the morphism `ι` whose components are the
  inclusion `F_t ⟶ 𝓕` and `F_t ⟶ Spec ℂ ⟶ T'` through `t'`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Opposite
open MMP.Mori MMP.Analytic MMP.Analytic.ComplexPoints
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open TensorProduct Topology
open MMP MMP.UnderlyingSpace

namespace MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### The averaging identity -/

/-- **Orbit averaging.** Let `G` be a finite set of surjective endomorphisms of a `ℚ`-vector
space `W`, closed under composition, acting on a finite set `S` compatibly with a map
`e : S → W` (each `g ∈ G` is realized by a permutation `σ` of `S` with `e ∘ σ = g ∘ e`), and
suppose that every value of `e` lies in the orbit `G • c`. Then `∑_{s ∈ S} e s` is
`|S| • |G|⁻¹ • ∑_{g ∈ G} g c`. -/
private theorem finsum_eq_card_smul_average {W : Type*} [AddCommGroup W] [Module ℚ W]
    (G : Set (Module.End ℚ W)) (hGfin : G.Finite)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) (hsurj : ∀ h ∈ G, Function.Surjective h)
    {S : Type*} [Finite S] (e : S → W) (c : W)
    (horb : ∀ s, ∃ h ∈ G, e s = h c)
    (hinv : ∀ g ∈ G, ∃ σ : S ≃ S, ∀ s, e (σ s) = g (e s)) :
    ∑ᶠ s, e s = (Nat.card S : ℚ) • ((Nat.card G : ℚ)⁻¹ • ∑ᶠ g ∈ G, g c) := by
  classical
  have := Fintype.ofFinite S
  set F := hGfin.toFinset with hF
  rw [finsum_eq_sum_of_fintype, finsum_mem_eq_finite_toFinset_sum _ hGfin, ← hF,
    Nat.card_eq_card_finite_toFinset hGfin, ← hF, Nat.card_eq_fintype_card]
  have hmemF : ∀ g, g ∈ F ↔ g ∈ G := fun g ↦ Set.Finite.mem_toFinset hGfin
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · simp
  obtain ⟨h₀, hh₀, -⟩ := horb s₀
  have hFpos : (F.card : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨h₀, (hmemF h₀).2 hh₀⟩).ne'
  set x := ∑ s, e s with hx
  have hfix : ∀ g ∈ G, g x = x := by
    intro g hg
    obtain ⟨σ, hσ⟩ := hinv g hg
    rw [hx, map_sum]
    simp_rw [← hσ]
    exact Equiv.sum_comp σ e
  have hshift : ∀ h ∈ G, ∑ g ∈ F, (g * h) c = ∑ g ∈ F, g c := by
    intro h hh
    have hinj : Set.InjOn (fun g : Module.End ℚ W ↦ g * h) F := by
      intro g _ g' _ hgg'
      refine LinearMap.ext fun w ↦ ?_
      obtain ⟨u, rfl⟩ := hsurj h hh w
      exact LinearMap.congr_fun hgg' u
    have himg : F.image (fun g ↦ g * h) = F := by
      refine Finset.eq_of_subset_of_card_le ?_ ?_
      · intro k hk
        obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hk
        exact (hmemF _).2 (hmul g ((hmemF g).1 hg) h hh)
      · rw [Finset.card_image_of_injOn hinj]
    calc ∑ g ∈ F, (g * h) c = ∑ k ∈ F.image (fun g ↦ g * h), k c :=
          (Finset.sum_image (f := fun k : Module.End ℚ W ↦ k c) hinj).symm
      _ = ∑ g ∈ F, g c := by rw [himg]
  have key : (F.card : ℚ) • x = (Fintype.card S : ℚ) • ∑ g ∈ F, g c := by
    calc (F.card : ℚ) • x = ∑ g ∈ F, g x := by
          rw [Finset.sum_congr rfl fun g hg ↦ hfix g ((hmemF g).1 hg), Finset.sum_const,
            Nat.cast_smul_eq_nsmul]
      _ = ∑ s, ∑ g ∈ F, g (e s) := by
          rw [hx]
          simp_rw [map_sum]
          exact Finset.sum_comm
      _ = ∑ _s : S, ∑ g ∈ F, g c := by
          refine Finset.sum_congr rfl fun s _ ↦ ?_
          obtain ⟨h, hh, hs⟩ := horb s
          rw [hs, ← hshift h hh]
          rfl
      _ = (Fintype.card S : ℚ) • ∑ g ∈ F, g c := by
          rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  calc x = (F.card : ℚ)⁻¹ • ((F.card : ℚ) • x) := by
        rw [smul_smul, inv_mul_cancel₀ hFpos, one_smul]
    _ = _ := by rw [key, smul_comm]

/-! ### Classes on neighbourhoods of the fibre -/

section Good

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y} {π : Yt ⟶ Y}
  {To : (curveScheme T).Opens} {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)}

/-- A pair `(x, y)` of a class `x ∈ H²(F_t; ℚ)` and a germ `y ∈ 𝒲_t` is *realized* when some
class `α ∈ H²(π⁻¹(V); ℚ)` on a neighbourhood `V` of `t` restricts to `x` on `F_t` and has germ
`y` at `t`. -/
def IsRealized
    (x : rationalCohomology (analyticSpace (pointFibre sY π To t ↘ Spec (.of ℂ))) 2)
    (y : resolutionLocalSystemFibre sY π To t) : Prop :=
  ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2),
    (rationalCohomologyMap (pointFibreInclusion sY π To t hV) 2).hom α = x ∧
    (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
      t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α) = y

/-- Restricting a class to a smaller neighbourhood does not change its restriction to `F_t`. -/
theorem rationalCohomologyMap_pointFibreInclusion_preimageInclusion
    {V W : Opens (analyticSpace sY)} (h : V ≤ W) (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) W) 2) :
    (rationalCohomologyMap (pointFibreInclusion sY π To t hV) 2).hom
        ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY π) h) 2).hom α) =
      (rationalCohomologyMap (pointFibreInclusion sY π To t (h hV)) 2).hom α := by
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp]
  rfl

/-- Restricting a class to a smaller neighbourhood does not change its germ. -/
theorem higherDirectImageGerm_preimageInclusion
    {V W : Opens (analyticSpace sY)} (h : V ≤ W) (hV : curveOpenInclusion sY To t ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) W) 2) :
    (higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom
        ((rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY π) h) 2).hom α) =
      (higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ (h hV)).hom α := by
  have e := (directImagePresheaf (resolutionAnalyticMap sY π) 2).germ_res (homOfLE h) _ hV
  unfold higherDirectImageGerm
  rw [← e]
  rfl

/-- The zero class is realized by the zero germ. -/
theorem isRealized_zero : IsRealized (sY := sY) (π := π) (To := To) (t := t) 0 0 :=
  ⟨⊤, trivial, 0, map_zero _, by rw [map_zero, map_zero]; rfl⟩

/-- Realized pairs are closed under addition. -/
theorem IsRealized.add {x x' y y'} (h : IsRealized (sY := sY) (π := π) (To := To) (t := t) x y)
    (h' : IsRealized (sY := sY) (π := π) (To := To) (t := t) x' y') :
    IsRealized (sY := sY) (π := π) (To := To) (t := t) (x + x') (y + y') := by
  obtain ⟨V, hV, α, hα, hα'⟩ := h
  obtain ⟨V', hV', β, hβ, hβ'⟩ := h'
  refine ⟨V ⊓ V', ⟨hV, hV'⟩,
    (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY π) inf_le_left) 2).hom α +
    (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY π) inf_le_right) 2).hom β,
    ?_, ?_⟩
  · rw [map_add,
      rationalCohomologyMap_pointFibreInclusion_preimageInclusion inf_le_left ⟨hV, hV'⟩ α,
      rationalCohomologyMap_pointFibreInclusion_preimageInclusion inf_le_right ⟨hV, hV'⟩ β, hα, hβ]
  · rw [map_add, higherDirectImageGerm_preimageInclusion inf_le_left ⟨hV, hV'⟩ α,
      higherDirectImageGerm_preimageInclusion inf_le_right ⟨hV, hV'⟩ β, map_add, hα',
      hβ']
    rfl

/-- Realized pairs are closed under rational multiples. -/
theorem IsRealized.smul {x y} (c : ℚ)
    (h : IsRealized (sY := sY) (π := π) (To := To) (t := t) x y) :
    IsRealized (sY := sY) (π := π) (To := To) (t := t) (c • x) (c • y) := by
  obtain ⟨V, hV, α, hα, hα'⟩ := h
  exact ⟨V, hV, c • α, by rw [map_smul, hα], by rw [map_smul, map_smul, hα']; rfl⟩

private theorem isRealized_finsum {S : Type*} [Finite S] (x : S → _) (y : S → _)
    (h : ∀ s, IsRealized (sY := sY) (π := π) (To := To) (t := t) (x s) (y s)) :
    IsRealized (sY := sY) (π := π) (To := To) (t := t) (∑ᶠ s, x s) (∑ᶠ s, y s) := by
  classical
  have := Fintype.ofFinite S
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  induction (Finset.univ : Finset S) using Finset.induction_on with
  | empty => simpa using isRealized_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

end Good

/-! ### Germs of inverse images, and parallel transport -/

section ConstantSheafGerms

/-- The constant sheaf with value `E`, as a sheaf on the space `V`. -/
private def cSh (V : TopCat.{0}) (E : ModuleCat.{0} ℚ) : TopCat.Sheaf (ModuleCat.{0} ℚ) V :=
  (constantSheaf (Opens.grothendieckTopology V) (ModuleCat.{0} ℚ)).obj E

variable {V : TopCat.{0}} (E : ModuleCat.{0} ℚ)

/-- The constant section `e` of the constant sheaf with value `E`. -/
private def constSection (e : E) :
    ToType (((TopCat.Sheaf.forget _ V).obj (cSh V E)).obj (op ⊤)) :=
  ((CategoryTheory.toSheafify (Opens.grothendieckTopology V)
    ((Functor.const (Opens V)ᵒᵖ).obj E)).app (op ⊤)).hom e

private theorem constSection_zero :
    constSection (V := V) E 0 = 0 :=
  map_zero _

/-- Every germ of a constant sheaf is the germ of a constant section. -/
private theorem constantSheaf_exists_constSection_germ (p : V)
    (c : ToType (((TopCat.Sheaf.forget _ V).obj (cSh V E)).stalk p)) :
    ∃ e : E, ((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ
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
    (h : ((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ ⊤ p (Opens.mem_top p)
        (constSection E e) = 0) : e = 0 := by
  let K : TopCat.Presheaf (ModuleCat.{0} ℚ) V := (Functor.const (Opens V)ᵒᵖ).obj E
  have hiso := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso p (ModuleCat.{0} ℚ) K
  have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply (F := K) ⊤ p (Opens.mem_top p)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K) e
  have h2 : K.germ ⊤ p (Opens.mem_top p) e = K.germ ⊤ p (Opens.mem_top p) 0 := by
    apply (ConcreteCategory.bijective_of_isIso ((TopCat.Presheaf.stalkFunctor
      (ModuleCat.{0} ℚ) p).map (CategoryTheory.toSheafify (Opens.grothendieckTopology V) K))).1
    refine e1.trans (h.trans ?_)
    exact ((congrArg _ (map_zero _)).trans (map_zero _)).symm
  obtain ⟨W, -, i₁, i₂, he⟩ := K.germ_eq p (Opens.mem_top p) (Opens.mem_top p) e 0 h2
  exact he

/-- Near every point, a section of a constant sheaf has the germs of a constant section. -/
private theorem constantSheaf_exists_constSection {U : Opens V}
    (σ : ToType (((TopCat.Sheaf.forget _ V).obj (cSh V E)).obj (op U)))
    (p : V) (hp : p ∈ U) :
    ∃ (e : E) (N : Opens V) (_ : p ∈ N) (hNU : N ≤ U), ∀ v (hv : v ∈ N),
      ((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ U v (hNU hv) σ =
        ((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ ⊤ v (Opens.mem_top v)
          (constSection E e) := by
  obtain ⟨e, he⟩ := constantSheaf_exists_constSection_germ E p
    (((TopCat.Sheaf.forget _ V).obj (cSh V E)).germ U p hp σ)
  obtain ⟨W, hW, iU, iT, hWe⟩ := TopCat.Presheaf.germ_eq _ p hp (Opens.mem_top p) σ
    (constSection E e) he.symm
  refine ⟨e, W, hW, iU.le, fun v hv => ?_⟩
  exact (TopCat.Presheaf.germ_res_apply _ iU v hv σ).symm.trans
    ((congrArg _ hWe).trans (TopCat.Presheaf.germ_res_apply _ iT v hv _))

end ConstantSheafGerms

section Transport

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Y)

/-- The pullback sheaf `f^* F`. -/
private abbrev pullbackSheaf : TopCat.Sheaf (ModuleCat.{0} ℚ) X :=
  (TopCat.Sheaf.pullback (ModuleCat.{0} ℚ) f).obj F

/-- The section of `f^* F` over `f⁻¹(W)` attached to a section of `F` over `W`. -/
private def unitSec {W : Opens Y} (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) :
    ToType (((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).obj (op ((Opens.map f).obj W))) :=
  (((TopCat.Sheaf.forget _ Y).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
      (op W)).hom r

private theorem stalkToPullbackStalk_germ {W : Opens Y}
    (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (x : X) (hx : f x ∈ W) :
    (stalkToPullbackStalk f F x).hom (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx r) =
      ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ ((Opens.map f).obj W) x hx
        (unitSec f F r) := by
  have h : ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) hx ≫ stalkToPullbackStalk f F x =
      ((TopCat.Sheaf.forget _ Y).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} ℚ) f).unit.app F)).app
          (op W) ≫ ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ
            ((Opens.map f).obj W) x hx := by
    unfold stalkToPullbackStalk
    erw [TopCat.Presheaf.stalkFunctor_map_germ_assoc, TopCat.Presheaf.stalkPushforward_germ]
    rfl
  exact congrArg (fun φ => φ.hom r) h

private theorem bijective_stalkToPullbackStalk (x : X) :
    Function.Bijective (stalkToPullbackStalk f F x).hom := by
  rw [show stalkToPullbackStalk f F x = _ from
    (Stacks.SheafifyStalk.stalkSheafPullbackIso_inv_eq _ f F x).symm]
  exact (Stacks.SheafifyStalk.stalkSheafPullbackIso _ f F x).symm.toLinearEquiv.bijective

/-- Every section of `f^* F` is, near each point, the image of a section of `F`. -/
private theorem exists_local_germ {U : Opens X}
    (s : ToType (((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).obj (op U))) (x₀ : X)
    (hx₀ : x₀ ∈ U) :
    ∃ (W : Opens Y) (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W))) (N : Opens X)
      (_ : x₀ ∈ N) (hNU : N ≤ U) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ U x (hNU hx) s =
        (stalkToPullbackStalk f F x).hom
          (((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) (hNW hx) r) := by
  obtain ⟨y, hy⟩ := (bijective_stalkToPullbackStalk f F x₀).2
    (((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ U x₀ hx₀ s)
  obtain ⟨W, hW, r, rfl⟩ := ((TopCat.Sheaf.forget _ Y).obj F).exists_germ_eq y
  rw [stalkToPullbackStalk_germ] at hy
  obtain ⟨N, hN, iW, iU, e⟩ :=
    ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ_eq x₀ _ _ _ _ hy
  refine ⟨W, r, N, hN, iU.le, iW.le, fun x hx => ?_⟩
  rw [← TopCat.Presheaf.germ_res_apply _ iU x hx, ← e, TopCat.Presheaf.germ_res_apply]
  exact (stalkToPullbackStalk_germ f F r x _).symm

/-- A family of germs of `F` along `f` which is locally given by sections of `F` is the family
of germs of a global section of `f^* F`. -/
private theorem exists_section_of_local
    (y : ∀ x : X, ToType (((TopCat.Sheaf.forget _ Y).obj F).stalk (f x)))
    (hy : ∀ x₀ : X, ∃ (W : Opens Y) (r : ToType (((TopCat.Sheaf.forget _ Y).obj F).obj (op W)))
      (N : Opens X) (_ : x₀ ∈ N) (hNW : N ≤ (Opens.map f).obj W),
      ∀ x (hx : x ∈ N), y x = ((TopCat.Sheaf.forget _ Y).obj F).germ W (f x) (hNW hx) r) :
    ∃ s : ToType (((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).obj (op ⊤)), ∀ x,
      ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)).germ ⊤ x trivial s =
        (stalkToPullbackStalk f F x).hom (y x) := by
  choose W r N hN hNW hloc using hy
  set P := (TopCat.Sheaf.forget _ X).obj (pullbackSheaf f F)
  let sf : ∀ i : X, ToType (P.obj (op (N i))) := fun i =>
    P.map (homOfLE (hNW i)).op (unitSec f F (r i))
  have hgerm : ∀ i x (hx : x ∈ N i), P.germ (N i) x hx (sf i) =
      (stalkToPullbackStalk f F x).hom (y x) := by
    intro i x hx
    rw [TopCat.Presheaf.germ_res_apply, hloc i x hx]
    exact (stalkToPullbackStalk_germ f F (r i) x _).symm
  have hcompat : TopCat.Presheaf.IsCompatible P N sf := by
    intro i j
    refine TopCat.Presheaf.section_ext (pullbackSheaf f F) _ _ _ fun x hx => ?_
    change P.germ _ x hx _ = P.germ _ x hx _
    rw [TopCat.Presheaf.germ_res_apply P ((N i).infLELeft (N j)) x hx (sf i),
      TopCat.Presheaf.germ_res_apply P ((N i).infLERight (N j)) x hx (sf j), hgerm, hgerm]
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (pullbackSheaf f F) N ⊤
    (fun i => homOfLE le_top) (fun x _ => Opens.mem_iSup.2 ⟨x, hN x⟩) sf hcompat
  refine ⟨s, fun x => ?_⟩
  rw [← hgerm x x (hN x), ← hs x]
  exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm

omit F in
private theorem stalkCongr_germ (P : TopCat.Presheaf (ModuleCat.{0} ℚ) Y) {p q : Y}
    (e : Inseparable p q)
    {U : Opens Y} (hp : p ∈ U) (hq : q ∈ U) (r : ToType (P.obj (op U))) :
    (P.stalkCongr e).hom.hom (P.germ U p hp r) = P.germ U q hq r :=
  TopCat.Presheaf.germ_stalkSpecializes_apply P hp e.ge r

omit F in
private theorem stalkCongr_stalkCongr (P : TopCat.Presheaf (ModuleCat.{0} ℚ) Y) {p q u : Y}
    (e : Inseparable p q) (e' : Inseparable q u) (y : ToType (P.stalk p)) :
    (P.stalkCongr e').hom.hom ((P.stalkCongr e).hom.hom y) =
      (P.stalkCongr (e.trans e')).hom.hom y :=
  TopCat.Presheaf.stalkSpecializes_comp_apply P e'.ge e.ge y

omit F in
private theorem stalkCongr_self (P : TopCat.Presheaf (ModuleCat.{0} ℚ) Y) {p : Y}
    (e : Inseparable p p) (y : ToType (P.stalk p)) : (P.stalkCongr e).hom.hom y = y := by
  change (P.stalkSpecializes e.ge).hom y = y
  rw [show e.ge = specializes_refl p from rfl, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- **Reparametrization.** For `γ' = γ ∘ a`, a section of `γ^* F` induces a section of `γ'^* F`
with the transported germs. -/
private theorem exists_section_reparam {X' : TopCat.{0}} (γ : X ⟶ Y) (γ' : X' ⟶ Y) (a : C(X', X))
    (h : ∀ x, γ (a x) = γ' x)
    (s : ToType (((TopCat.Sheaf.forget _ X).obj (pullbackSheaf γ F)).obj (op ⊤))) :
    ∃ s' : ToType (((TopCat.Sheaf.forget _ X').obj (pullbackSheaf γ' F)).obj (op ⊤)),
      ∀ x p (hp : a x = p) (y : ToType (((TopCat.Sheaf.forget _ Y).obj F).stalk (γ p))),
        (stalkToPullbackStalk γ F p).hom y =
            ((TopCat.Sheaf.forget _ X).obj (pullbackSheaf γ F)).germ ⊤ p trivial s →
          (stalkToPullbackStalk γ' F x).hom
              ((((TopCat.Sheaf.forget _ Y).obj F).stalkCongr
                (Inseparable.of_eq (hp ▸ h x))).hom.hom y) =
            ((TopCat.Sheaf.forget _ X').obj (pullbackSheaf γ' F)).germ ⊤ x trivial s' := by
  set P := (TopCat.Sheaf.forget _ Y).obj F
  have hsurj := fun p => (bijective_stalkToPullbackStalk γ F p).2
  choose yy hyy using fun p =>
    hsurj p (((TopCat.Sheaf.forget _ X).obj (pullbackSheaf γ F)).germ ⊤ p trivial s)
  let z : ∀ x : X', ToType (P.stalk (γ' x)) := fun x =>
    (P.stalkCongr (Inseparable.of_eq (h x))).hom.hom (yy (a x))
  obtain ⟨s', hs'⟩ := exists_section_of_local γ' F z (fun x₀ => by
    obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ γ F s (a x₀) trivial
    refine ⟨W, r, ⟨a ⁻¹' N, N.isOpen.preimage a.continuous⟩, hN, fun x hx => ?_, fun x hx => ?_⟩
    · change γ' x ∈ W
      rw [← h x]
      exact hNW hx
    · have e : yy (a x) = P.germ W (γ (a x)) (hNW hx) r :=
        (bijective_stalkToPullbackStalk γ F (a x)).1 ((hyy (a x)).trans (hloc (a x) hx))
      change (P.stalkCongr _).hom.hom (yy (a x)) = _
      rw [e]
      exact stalkCongr_germ P _ _ _ r)
  refine ⟨s', fun x p hp y hy => ?_⟩
  subst hp
  have e : y = yy (a x) := (bijective_stalkToPullbackStalk γ F (a x)).1 (hy.trans (hyy _).symm)
  subst e
  exact (hs' x).symm

section ParallelTransport

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

/-- `g` is the parallel transport of `F` along the loop `γ`. -/
private def IsTransport {t : Z} (γ : Path t t)
    (g : Module.End ℚ (((TopCat.Sheaf.forget _ _).obj F).stalk t)) : Prop :=
  ∀ (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj F).obj.obj (op ⊤)))
      (w v : ((TopCat.Sheaf.forget _ _).obj F).stalk t),
      (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap) F 0).hom
          ((((TopCat.Sheaf.forget _ _).obj F).stalkCongr (.of_eq γ.source.symm)).hom.hom w) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj F)).germ
            ⊤ 0 trivial).hom s →
      (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap) F 1).hom
          ((((TopCat.Sheaf.forget _ _).obj F).stalkCongr (.of_eq γ.target.symm)).hom.hom v) =
        (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj F)).germ
            ⊤ 1 trivial).hom s →
      g w = v

private theorem half_mem (x : unitInterval) : (x : ℝ) / 2 ∈ unitInterval := by
  constructor <;> linarith [x.2.1, x.2.2]

private theorem half_add_mem (x : unitInterval) : ((x : ℝ) + 1) / 2 ∈ unitInterval := by
  constructor <;> linarith [x.2.1, x.2.2]

/-- The first half `x ↦ x / 2` of the unit interval. -/
private def halfLeft : C(unitInterval, unitInterval) :=
  ⟨fun x => ⟨(x : ℝ) / 2, half_mem x⟩,
    (continuous_subtype_val.div_const 2).subtype_mk half_mem⟩

/-- The second half `x ↦ (x + 1) / 2` of the unit interval. -/
private def halfRight : C(unitInterval, unitInterval) :=
  ⟨fun x => ⟨((x : ℝ) + 1) / 2, half_add_mem x⟩,
    ((continuous_subtype_val.add continuous_const).div_const 2).subtype_mk half_add_mem⟩

private theorem coe_halfLeft (x : unitInterval) : (halfLeft x : ℝ) = x / 2 := rfl

private theorem coe_halfRight (x : unitInterval) : (halfRight x : ℝ) = (x + 1) / 2 := rfl

private theorem trans_halfLeft {t : Z} (γ₁ γ₂ : Path t t) (x : unitInterval) :
    (γ₂.trans γ₁) (halfLeft x) = γ₂ x := by
  rw [Path.trans_apply, dif_pos (by rw [coe_halfLeft]; linarith [x.2.2])]
  congr 1
  ext
  simp only [coe_halfLeft]
  ring

private theorem trans_halfRight {t : Z} (γ₁ γ₂ : Path t t) (x : unitInterval) :
    (γ₂.trans γ₁) (halfRight x) = γ₁ x := by
  rw [Path.trans_apply]
  split_ifs with h
  · rw [coe_halfRight] at h
    have hx' : x = 0 := Subtype.ext (by
      change (x : ℝ) = 0
      linarith [x.2.1])
    subst hx'
    rw [γ₁.source]
    convert γ₂.target using 2
    ext
    simp only [coe_halfRight]
    norm_num
  · congr 1
    ext
    simp only [coe_halfRight]
    ring

private theorem halfLeft_one : halfLeft 1 = halfRight 0 := by
  ext
  rw [coe_halfLeft, coe_halfRight]
  norm_num

private theorem halfLeft_zero : halfLeft 0 = 0 := by
  ext
  rw [coe_halfLeft]
  norm_num

private theorem halfRight_one : halfRight 1 = 1 := by
  ext
  rw [coe_halfRight]
  norm_num

/-- **Transport along a concatenation.** -/
private theorem IsTransport.trans {t : Z} {γ₁ γ₂ : Path t t} {g h : Module.End ℚ
    (((TopCat.Sheaf.forget _ _).obj F).stalk t)} (hg : IsTransport F γ₁ g)
    (hh : IsTransport F γ₂ h) : IsTransport F (γ₂.trans γ₁) (g * h) := by
  intro s w v hw hv
  let P := (TopCat.Sheaf.forget _ Z).obj F
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) (γ₂.trans γ₁).toContinuousMap
  obtain ⟨s₂, hs₂⟩ := exists_section_reparam F Γ
    (TopCat.ofHom (X := TopCat.of unitInterval) γ₂.toContinuousMap) halfLeft
    (trans_halfLeft γ₁ γ₂) s
  obtain ⟨s₁, hs₁⟩ := exists_section_reparam F Γ
    (TopCat.ofHom (X := TopCat.of unitInterval) γ₁.toContinuousMap) halfRight
    (trans_halfRight γ₁ γ₂) s
  obtain ⟨yq, hyq⟩ := (bijective_stalkToPullbackStalk Γ F (halfLeft 1)).2
    (((TopCat.Sheaf.forget _ _).obj (pullbackSheaf Γ F)).germ ⊤ (halfLeft 1) trivial s)
  have hq : Γ (halfLeft 1) = t := (trans_halfLeft γ₁ γ₂ 1).trans γ₂.target
  let u := (P.stalkCongr (Inseparable.of_eq hq)).hom.hom yq
  have h1 : h w = u := by
    refine hh s₂ w u ?_ ?_
    · have := hs₂ 0 0 halfLeft_zero _ hw
      rwa [stalkCongr_stalkCongr] at this
    · rw [stalkCongr_stalkCongr]
      exact hs₂ 1 (halfLeft 1) rfl yq hyq
  have h2 : g u = v := by
    refine hg s₁ u v ?_ ?_
    · rw [stalkCongr_stalkCongr]
      exact hs₁ 0 (halfLeft 1) halfLeft_one.symm yq hyq
    · have := hs₁ 1 1 halfRight_one _ hv
      rwa [stalkCongr_stalkCongr] at this
  rw [Module.End.mul_apply, h1, h2]

end ParallelTransport

section LocalSystem

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

/-- Every germ at a point of `V` extends to a family of germs over `V` which is locally given by
sections of `F`. -/
private def GermExtendable (V : Opens Z) : Prop :=
  ∀ z' ∈ V, ∀ y' : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z'),
    ∃ Y : ∀ z : Z, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z), Y z' = y' ∧
      ∀ z₀ ∈ V, ∃ (W : Opens Z) (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W)))
        (N : Opens Z) (_ : z₀ ∈ N) (hNW : N ≤ W), ∀ z (hz : z ∈ N),
          Y z = ((TopCat.Sheaf.forget _ Z).obj F).germ W z (hNW hz) r

/-- A local system is germ-extendable near every point. -/
private theorem exists_germExtendable (hF : IsLocalSystem F) (z : Z) :
    ∃ V : Opens Z, z ∈ V ∧ GermExtendable F V := by
  obtain ⟨V, hz, E, -, ⟨φ⟩⟩ := hF z
  classical
  refine ⟨V, hz, fun z' hz' y' => ?_⟩
  let ι := V.inclusion'
  let P := (TopCat.Sheaf.forget _ Z).obj F
  let Q := (TopCat.Sheaf.forget _ _).obj (pullbackSheaf ι F)
  let pt : (Opens.toTopCat Z).obj V := ⟨z', hz'⟩
  let y'' := (stalkToPullbackStalk ι F pt).hom y'
  obtain ⟨e₀, hσc⟩ := constantSheaf_exists_constSection_germ E pt
    (((TopCat.Presheaf.stalkFunctor _ pt).map ((TopCat.Sheaf.forget _ _).map φ.hom)).hom y'')
  let σ : ToType (Q.obj (op ⊤)) :=
    (((TopCat.Sheaf.forget _ _).map φ.inv).app (op ⊤)).hom (constSection E e₀)
  have hσ : Q.germ ⊤ pt trivial σ = y'' := by
    have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply ⊤ pt trivial
      ((TopCat.Sheaf.forget _ _).map φ.inv) (constSection E e₀)
    refine e1.symm.trans ?_
    erw [hσc, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      φ.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  have hbij := fun (v : (Opens.toTopCat Z).obj V) => bijective_stalkToPullbackStalk ι F v
  let Y : ∀ z : Z, ToType (P.stalk z) := fun z => if h : z ∈ V then
    (Equiv.ofBijective _ (hbij ⟨z, h⟩)).symm (Q.germ ⊤ ⟨z, h⟩ trivial σ) else 0
  have hY : ∀ z (h : z ∈ V), (stalkToPullbackStalk ι F ⟨z, h⟩).hom (Y z) =
      Q.germ ⊤ ⟨z, h⟩ trivial σ := by
    intro z h
    have e : Y z = (Equiv.ofBijective _ (hbij ⟨z, h⟩)).symm (Q.germ ⊤ ⟨z, h⟩ trivial σ) :=
      dif_pos h
    rw [e]
    exact (Equiv.ofBijective _ (hbij ⟨z, h⟩)).apply_symm_apply _
  refine ⟨Y, (hbij pt).1 ((hY z' hz').trans hσ), fun z₀ hz₀ => ?_⟩
  obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ ι F σ ⟨z₀, hz₀⟩ trivial
  have hNopen : IsOpen (Subtype.val '' (SetLike.coe N : Set V)) :=
    V.isOpen.isOpenMap_subtype_val (SetLike.coe N : Set V) N.isOpen
  refine ⟨W, r, ⟨_, hNopen⟩, ⟨_, hN, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hNW hv
  · rintro _ ⟨v, hv, rfl⟩
    refine (hbij v).1 ((hY v.1 v.2).trans ?_)
    exact (hloc v hv).trans rfl

end LocalSystem

section Interval

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z) (γ : TopCat.of unitInterval ⟶ Z)

/-- A family of germs along `γ` is given near `x₀` by a section of `F`. -/
private def LocGerm (Y : ∀ x : unitInterval, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x)))
    (x₀ : unitInterval) : Prop :=
  ∃ (W : Opens Z) (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W)))
    (N : Opens (TopCat.of unitInterval)) (_ : x₀ ∈ N) (hNW : N ≤ (Opens.map γ).obj W),
    ∀ x (hx : x ∈ N), Y x = ((TopCat.Sheaf.forget _ Z).obj F).germ W (γ x) (hNW hx) r

/-- Every germ at `γ q` extends to a family along `γ` given locally by sections up to `q`. -/
private def Reach (q : unitInterval) : Prop :=
  ∀ y : ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ q)),
    ∃ Y : ∀ x : unitInterval, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x)),
      Y q = y ∧ ∀ x₀ ≤ q, LocGerm F γ Y x₀

variable {F γ}

private theorem LocGerm.congr {Y Y' : ∀ x : unitInterval,
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x))} {x₀ : unitInterval}
    (h : LocGerm F γ Y x₀) (S : Set unitInterval) (hS : IsOpen S) (hx₀ : x₀ ∈ S)
    (hYY : ∀ x ∈ S, Y' x = Y x) : LocGerm F γ Y' x₀ := by
  obtain ⟨W, r, N, hN, hNW, hloc⟩ := h
  refine ⟨W, r, N ⊓ ⟨S, hS⟩, ⟨hN, hx₀⟩, fun x hx => hNW hx.1, fun x hx => ?_⟩
  rw [hYY x hx.2]
  exact hloc x hx.1

private theorem LocGerm.of_germExtendable {V : Opens Z} {Zf : ∀ z : Z,
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk z)}
    (hZ : ∀ z₀ ∈ V, ∃ (W : Opens Z) (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W)))
        (N : Opens Z) (_ : z₀ ∈ N) (hNW : N ≤ W), ∀ z (hz : z ∈ N),
          Zf z = ((TopCat.Sheaf.forget _ Z).obj F).germ W z (hNW hz) r)
    {x₀ : unitInterval} (hx₀ : γ x₀ ∈ V) : LocGerm F γ (fun x => Zf (γ x)) x₀ := by
  obtain ⟨W, r, N, hN, hNW, hloc⟩ := hZ (γ x₀) hx₀
  exact ⟨W, r, (Opens.map γ).obj N, hN, fun x hx => hNW hx, fun x hx => hloc (γ x) hx⟩

private theorem LocGerm.glue {Y₁ Y₂ : ∀ x : unitInterval,
    ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x))} {q : unitInterval}
    (h₁ : LocGerm F γ Y₁ q) (h₂ : LocGerm F γ Y₂ q) (h : Y₁ q = Y₂ q) :
    LocGerm F γ (fun x => if x ≤ q then Y₁ x else Y₂ x) q := by
  classical
  obtain ⟨W₁, r₁, N₁, hN₁, hNW₁, hloc₁⟩ := h₁
  obtain ⟨W₂, r₂, N₂, hN₂, hNW₂, hloc₂⟩ := h₂
  let P := (TopCat.Sheaf.forget _ Z).obj F
  have e := (hloc₁ q hN₁).symm.trans (h.trans (hloc₂ q hN₂))
  obtain ⟨W, hW, iU, iV, he⟩ := P.germ_eq (γ q) (hNW₁ hN₁) (hNW₂ hN₂) r₁ r₂ e
  refine ⟨W, P.map iU.op r₁, N₁ ⊓ N₂ ⊓ (Opens.map γ).obj W, ⟨⟨hN₁, hN₂⟩, hW⟩,
    fun x hx => hx.2, fun x hx => ?_⟩
  beta_reduce
  split_ifs
  · rw [hloc₁ x hx.1.1]
    exact (TopCat.Presheaf.germ_res_apply P iU (γ x) hx.2 r₁).symm
  · rw [hloc₂ x hx.1.2, he]
    exact (TopCat.Presheaf.germ_res_apply P iV (γ x) hx.2 r₂).symm

private theorem reach_zero {V : Opens Z} (hV : GermExtendable F V) (h0 : γ 0 ∈ V) :
    Reach F γ 0 := by
  intro y
  obtain ⟨Zf, hZf, hloc⟩ := hV (γ 0) h0 y
  refine ⟨fun x => Zf (γ x), hZf, fun x₀ hx₀ => ?_⟩
  have : x₀ = 0 := le_antisymm hx₀ (unitInterval.nonneg x₀)
  subst this
  exact LocGerm.of_germExtendable hloc h0

private theorem Reach.propagate {q q' : unitInterval} (hq : Reach F γ q) (hqq' : q ≤ q')
    {V : Opens Z}
    (hV : GermExtendable F V) (hγ : ∀ x, q ≤ x → x ≤ q' → γ x ∈ V) : Reach F γ q' := by
  classical
  intro y'
  obtain ⟨Zf, hZf, hloc⟩ := hV (γ q') (hγ q' hqq' le_rfl) y'
  obtain ⟨Y₁, hY₁, hl₁⟩ := hq (Zf (γ q))
  refine ⟨fun x => if x ≤ q then Y₁ x else Zf (γ x), ?_, fun x₀ hx₀ => ?_⟩
  · beta_reduce
    split_ifs with h
    · have : q' = q := le_antisymm h hqq'
      subst this
      exact hY₁.trans hZf
    · exact hZf
  · rcases lt_trichotomy x₀ q with h | rfl | h
    · refine (hl₁ x₀ h.le).congr {x | x < q} (isOpen_lt continuous_id continuous_const) h ?_
      intro x hx
      simp only [if_pos (le_of_lt (show x < q from hx))]
    · exact LocGerm.glue (hl₁ x₀ le_rfl) (LocGerm.of_germExtendable hloc (hγ x₀ le_rfl hqq'))
        hY₁
    · refine (LocGerm.of_germExtendable hloc (hγ x₀ h.le hx₀)).congr {x | q < x}
        (isOpen_lt continuous_const continuous_id) h ?_
      intro x hx
      simp only [if_neg (not_le.2 (show q < x from hx))]

private theorem reach_one (hF : IsLocalSystem F) : Reach F γ 1 := by
  choose V hV hext using fun z => exists_germExtendable F hF z
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (s := Set.univ)
    (c := fun z => γ ⁻¹' (V z : Set Z)) isCompact_univ
    (fun z => (V z).isOpen.preimage γ.hom.continuous)
    (fun x _ => Set.mem_iUnion.2 ⟨γ x, hV (γ x)⟩)
  let q : ℕ → unitInterval := fun n => ⟨min 1 (n * (δ / 2)), le_min zero_le_one
    (by positivity), min_le_left _ _⟩
  have hq : ∀ n, Reach F γ (q n) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨z, hz⟩ := hball 0 trivial
      have h0 : q 0 = 0 := by ext; simp [q]
      rw [h0]
      exact reach_zero (hext z) (hz (Metric.mem_ball_self hδ))
    | succ n ih =>
      obtain ⟨z, hz⟩ := hball (q n) trivial
      refine ih.propagate ?_ (hext z) fun x hx hx' => hz ?_
      · change min 1 (n * (δ / 2)) ≤ min 1 ((n + 1 : ℕ) * (δ / 2))
        gcongr
        exact_mod_cast Nat.le_succ n
      · rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq, abs_lt]
        have h1 : ((x : unitInterval) : ℝ) ≤ min 1 ((n + 1 : ℕ) * (δ / 2)) := hx'
        have h2 : min 1 (n * (δ / 2)) ≤ ((x : unitInterval) : ℝ) := hx
        have h3 : min 1 ((n + 1 : ℕ) * (δ / 2)) ≤ min 1 (n * (δ / 2)) + δ / 2 := by
          push_cast
          rcases le_total 1 (n * (δ / 2)) with h | h
          · rw [min_eq_left h, min_eq_left (by nlinarith)]
            linarith
          · rw [min_eq_right h]
            exact (min_le_right _ _).trans (by nlinarith)
        change -δ < (x : ℝ) - min 1 (n * (δ / 2)) ∧ (x : ℝ) - min 1 (n * (δ / 2)) < δ
        constructor <;> linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (2 / δ)
  have : q n = 1 := by
    ext
    change min 1 (n * (δ / 2)) = 1
    refine min_eq_left ?_
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  rw [← this]
  exact hq n

end Interval

section Surjective

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

/-- **Parallel transports of a local system are surjective.** -/
private theorem IsTransport.surjective (hF : IsLocalSystem F) {t : Z} {γ : Path t t}
    {h : Module.End ℚ (((TopCat.Sheaf.forget _ _).obj F).stalk t)} (hh : IsTransport F γ h) :
    Function.Surjective h := by
  intro v
  let P := (TopCat.Sheaf.forget _ Z).obj F
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  obtain ⟨Y, hY1, hloc⟩ := reach_one (F := F) (γ := Γ) hF
    ((P.stalkCongr (Inseparable.of_eq γ.target.symm)).hom.hom v)
  obtain ⟨s, hs⟩ := exists_section_of_local Γ F Y (fun x₀ => hloc x₀ (unitInterval.le_one x₀))
  refine ⟨(P.stalkCongr (Inseparable.of_eq γ.source)).hom.hom (Y 0), hh s _ v ?_ ?_⟩
  · rw [stalkCongr_stalkCongr, stalkCongr_self]
    exact (hs 0).symm
  · rw [← hY1]
    exact (hs 1).symm

end Surjective

end Transport

/-! ### Uniqueness and existence of parallel transport -/

section TransportExistence

variable {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)

/-- **The support of a section of a local system is open.** -/
private theorem exists_germ_ne_zero (hF : IsLocalSystem F) {W : Opens Z}
    (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W))) (z₀ : Z) (hz₀ : z₀ ∈ W)
    (h : ((TopCat.Sheaf.forget _ Z).obj F).germ W z₀ hz₀ r ≠ 0) :
    ∃ (N : Opens Z) (_ : z₀ ∈ N) (hNW : N ≤ W), ∀ z (hz : z ∈ N),
      ((TopCat.Sheaf.forget _ Z).obj F).germ W z (hNW hz) r ≠ 0 := by
  obtain ⟨V, hz₀V, E, -, ⟨φ₀⟩⟩ := hF z₀
  let ι := V.inclusion'
  let φ : pullbackSheaf ι F ≅ cSh ((Opens.toTopCat Z).obj V) E := φ₀
  let C := (TopCat.Sheaf.forget _ _).obj (cSh ((Opens.toTopCat Z).obj V) E)
  let ρ := unitSec ι F r
  let σ : ToType (C.obj (op ((Opens.map ι).obj W))) :=
    (((TopCat.Sheaf.forget _ _).map φ.hom).app (op ((Opens.map ι).obj W))).hom ρ
  let M := fun v : (Opens.toTopCat Z).obj V =>
    ((TopCat.Presheaf.stalkFunctor _ v).mapIso ((TopCat.Sheaf.forget _ _).mapIso φ)).hom.hom
  have hg : ∀ (v : (Opens.toTopCat Z).obj V) (hv : ι v ∈ W),
      C.germ _ v hv σ = M v ((stalkToPullbackStalk ι F v).hom
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
  obtain ⟨e, N, hv₀N, hNU, hloc⟩ := constantSheaf_exists_constSection E σ v₀ hz₀
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

/-- **Uniqueness of flat families along a path.** A locally sectional family of germs of a local
system along a path vanishing at one point vanishes everywhere. -/
private theorem LocGerm.eq_zero (hF : IsLocalSystem F) {γ : TopCat.of unitInterval ⟶ Z}
    {Y : ∀ x : unitInterval, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (γ x))}
    (hY : ∀ x, LocGerm F γ Y x) {x₀ : unitInterval} (h0 : Y x₀ = 0) (x : unitInterval) :
    Y x = 0 := by
  let P := (TopCat.Sheaf.forget _ Z).obj F
  have hA : IsClopen {x | Y x = 0} := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨W, r, N, hN, hNW, hloc⟩ := hY x
      have hne : P.germ W (γ x) (hNW hN) r ≠ 0 := by
        rw [← hloc x hN]
        exact hx
      obtain ⟨N', hN', hN'W, hne'⟩ := exists_germ_ne_zero F hF r (γ x) (hNW hN) hne
      refine ⟨(N ⊓ (Opens.map γ).obj N' : Opens (TopCat.of unitInterval)), fun x' hx' => ?_,
        (N ⊓ (Opens.map γ).obj N').isOpen, ⟨hN, hN'⟩⟩
      change Y x' ≠ 0
      rw [hloc x' hx'.1]
      exact hne' _ hx'.2
    · rw [isOpen_iff_forall_mem_open]
      intro x hx
      obtain ⟨W, r, N, hN, hNW, hloc⟩ := hY x
      have h0' : P.germ W (γ x) (hNW hN) r = P.germ W (γ x) (hNW hN) 0 := by
        rw [← hloc x hN, map_zero]
        exact hx
      obtain ⟨W', hW', iU, iV, he⟩ := P.germ_eq (γ x) (hNW hN) (hNW hN) r 0 h0'
      refine ⟨(N ⊓ (Opens.map γ).obj W' : Opens (TopCat.of unitInterval)), fun x' hx' => ?_,
        (N ⊓ (Opens.map γ).obj W').isOpen, ⟨hN, hW'⟩⟩
      change Y x' = 0
      rw [hloc x' hx'.1, ← TopCat.Presheaf.germ_res_apply P iU (γ x') hx'.2 r, he, map_zero,
        map_zero]
  exact Set.eq_univ_iff_forall.1 (hA.eq_univ ⟨x₀, h0⟩) x

/-- **Existence of parallel transport.** Along every loop of a local system there is a linear
parallel transport. -/
private theorem exists_isTransport (hF : IsLocalSystem F) {t : Z} (γ : Path t t) :
    ∃ g, IsTransport F γ g := by
  classical
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let PF := (TopCat.Sheaf.forget _ Z).obj F
  let P := (TopCat.Sheaf.forget _ _).obj (pullbackSheaf Γ F)
  let L0 : ToType (P.obj (op ⊤)) →ₗ[ℚ] ToType (P.stalk 0) := (P.germ ⊤ 0 trivial).hom
  let L1 : ToType (P.obj (op ⊤)) →ₗ[ℚ] ToType (P.stalk 1) := (P.germ ⊤ 1 trivial).hom
  have hbij := fun x => bijective_stalkToPullbackStalk Γ F x
  let iso0 : ToType (PF.stalk t) ≃ₗ[ℚ] ToType (P.stalk 0) :=
    (PF.stalkCongr (.of_eq γ.source.symm)).toLinearEquiv.trans
      (LinearEquiv.ofBijective (stalkToPullbackStalk Γ F 0).hom (hbij 0))
  let iso1 : ToType (PF.stalk t) ≃ₗ[ℚ] ToType (P.stalk 1) :=
    (PF.stalkCongr (.of_eq γ.target.symm)).toLinearEquiv.trans
      (LinearEquiv.ofBijective (stalkToPullbackStalk Γ F 1).hom (hbij 1))
  have hL0 : Function.Bijective L0 := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro s hs
      let Y : ∀ x : unitInterval, ToType (PF.stalk (Γ x)) := fun x =>
        (Equiv.ofBijective _ (hbij x)).symm (P.germ ⊤ x trivial s)
      have hYs : ∀ x, (stalkToPullbackStalk Γ F x).hom (Y x) = P.germ ⊤ x trivial s := fun x =>
        (Equiv.ofBijective _ (hbij x)).apply_symm_apply _
      have hY : ∀ x, LocGerm F Γ Y x := by
        intro x₀
        obtain ⟨W, r, N, hN, _hNU, hNW, hloc⟩ := exists_local_germ Γ F s x₀ trivial
        exact ⟨W, r, N, hN, hNW, fun x hx => (hbij x).1 ((hYs x).trans (hloc x hx))⟩
      have hY0 : Y 0 = 0 := (hbij 0).1 ((hYs 0).trans (hs.trans (map_zero _).symm))
      refine TopCat.Presheaf.section_ext (pullbackSheaf Γ F) ⊤ s 0 fun x _ => ?_
      change P.germ ⊤ x trivial s = P.germ ⊤ x trivial 0
      rw [map_zero, ← hYs x, LocGerm.eq_zero F hF hY hY0 x, map_zero]
    · intro z
      obtain ⟨y₀, rfl⟩ := (hbij 0).2 z
      let Γs := TopCat.ofHom (X := TopCat.of unitInterval) γ.symm.toContinuousMap
      have hs1 : Γ 0 = Γs 1 := by
        change γ 0 = γ (unitInterval.symm 1)
        rw [unitInterval.symm_one]
      obtain ⟨Y', hY'1, hloc'⟩ := reach_one (F := F) (γ := Γs) hF
        ((PF.stalkCongr (.of_eq hs1)).hom.hom y₀)
      obtain ⟨s', hs'⟩ := exists_section_of_local Γs F Y' (fun x₀ => hloc' x₀
        (unitInterval.le_one x₀))
      obtain ⟨s, hs⟩ := exists_section_reparam F Γs Γ
        ⟨unitInterval.symm, unitInterval.continuous_symm⟩ (fun x => by
        change γ (unitInterval.symm (unitInterval.symm x)) = γ x
        rw [unitInterval.symm_symm]) s'
      refine ⟨s, ?_⟩
      have := hs 0 1 unitInterval.symm_zero (Y' 1) (hs' 1).symm
      rw [hY'1, stalkCongr_stalkCongr, stalkCongr_self] at this
      exact this.symm
  let e0 := LinearEquiv.ofBijective L0 hL0
  refine ⟨iso1.symm.toLinearMap ∘ₗ L1 ∘ₗ e0.symm.toLinearMap ∘ₗ iso0.toLinearMap,
    fun s w v hw hv => ?_⟩
  let s' : ToType (P.obj (op ⊤)) := s
  have h1 : e0.symm (iso0 w) = s' := by
    rw [LinearEquiv.symm_apply_eq]
    exact hw
  change iso1.symm (L1 (e0.symm (iso0 w))) = v
  rw [h1, LinearEquiv.symm_apply_eq]
  exact hv.symm

variable {F} in
/-- **Transport along a lifted loop.** Let `p : E ⟶ Z` be continuous and `Ef` a family of germs of
`F` along `p` which is locally given by sections of `F`. If `g` is the transport of `F` along a
loop `γ` at `t`, then `g` carries the value of `Ef` at the start of any lift `Γ'` of `γ` to its
value at the end. -/
private theorem IsTransport.apply_lift {E : TopCat.{0}} {p : E ⟶ Z}
    (Ef : ∀ e : E, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (p e)))
    (hEf : ∀ e₀, ∃ (W : Opens Z) (r : ToType (((TopCat.Sheaf.forget _ Z).obj F).obj (op W)))
      (N : Opens E) (_ : e₀ ∈ N) (hNW : N ≤ (Opens.map p).obj W), ∀ e (he : e ∈ N),
        Ef e = ((TopCat.Sheaf.forget _ Z).obj F).germ W (p e) (hNW he) r)
    {t : Z} {γ : Path t t} {g : Module.End ℚ (((TopCat.Sheaf.forget _ _).obj F).stalk t)}
    (hg : IsTransport F γ g) (Γ' : C(unitInterval, E)) (hΓ' : ∀ x, p (Γ' x) = γ x)
    (h0 : p (Γ' 0) = t) (h1 : p (Γ' 1) = t) :
    g ((((TopCat.Sheaf.forget _ Z).obj F).stalkCongr (.of_eq h0)).hom.hom (Ef (Γ' 0))) =
      (((TopCat.Sheaf.forget _ Z).obj F).stalkCongr (.of_eq h1)).hom.hom (Ef (Γ' 1)) := by
  let PF := (TopCat.Sheaf.forget _ Z).obj F
  let Γ := TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap
  let Y : ∀ x : unitInterval, ToType (PF.stalk (Γ x)) := fun x =>
    (PF.stalkCongr (.of_eq (hΓ' x))).hom.hom (Ef (Γ' x))
  obtain ⟨s, hs⟩ := exists_section_of_local Γ F Y (fun x₀ => by
    obtain ⟨W, r, N, hN, hNW, hloc⟩ := hEf (Γ' x₀)
    refine ⟨W, r, ⟨Γ' ⁻¹' N, N.isOpen.preimage Γ'.continuous⟩, hN, fun x hx => ?_,
      fun x hx => ?_⟩
    · change γ x ∈ W
      rw [← hΓ' x]
      exact hNW hx
    · change (PF.stalkCongr _).hom.hom (Ef (Γ' x)) = _
      rw [hloc (Γ' x) hx]
      exact stalkCongr_germ PF _ _ _ r)
  refine hg s _ _ ?_ ?_
  · rw [stalkCongr_stalkCongr]
    exact (hs 0).symm
  · rw [stalkCongr_stalkCongr]
    exact (hs 1).symm

end TransportExistence

/-! ### Sheets of the cover over `t` -/

/-- The sheet `F_t × {t''} ⟶ 𝓕' = 𝓕 ×_{T°} T'` over a `ℂ`-point `t''` of `T'` above `t`: its
components are the inclusion `F_t ⟶ 𝓕` and `F_t ⟶ Spec ℂ ⟶ T'` through `t''`. -/
private def sheetι {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}
    {π : Yt ⟶ Y} {To : (curveScheme T).Opens} {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)}
    {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}
    (t'' : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}) :
    pointFibre sY π To t ⟶ pullback (pullback.snd π (To.ι ≫ curveι T)) φ :=
  pullback.lift (pointFibreToFamily sY π To t) (pointFibreSnd sY π To t ≫ t''.1.hom) (by
    rw [Category.assoc, t''.2]
    exact pullback.lift_snd _ _ _)

/-! ### The geometric inputs

The remaining inputs are geometric: the finiteness of the fibre of `φ` over `t`, the group
structure of the monodromy image `G`, the splitting of the norm over the fibre `F_t`, and the
flatness of the class of `𝓛'` along the cover. -/

/-- A finite scheme over `ℂ` has finitely many `ℂ`-points (sections of its structure
morphism). -/
theorem finite_sections {P : Scheme.{0}} (q : P ⟶ Spec (.of ℂ)) [IsFinite q] :
    Finite {σ : Spec (.of ℂ) ⟶ P // σ ≫ q = 𝟙 _} := by
  haveI : IsAffine P := isAffine_of_isAffineHom q
  have hP : Finite P := Set.finite_univ_iff.1
    ((q.finite_preimage_singleton (IsLocalRing.closedPoint ℂ)).subset
      fun _ _ ↦ Subsingleton.elim _ _)
  have hSpec : Finite (PrimeSpectrum Γ(P, ⊤)) :=
    Finite.of_surjective _ (P.isoSpec.hom.homeomorph.surjective)
  let κ : {σ : Spec (.of ℂ) ⟶ P // σ ≫ q = 𝟙 _} → PrimeSpectrum Γ(P, ⊤) :=
    fun σ ↦ ⟨RingHom.ker σ.1.appTop.hom, RingHom.ker_isPrime _⟩
  refine Finite.of_injective κ ?_
  rintro ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩ hk
  have hk' : RingHom.ker σ₁.appTop.hom = RingHom.ker σ₂.appTop.hom :=
    congrArg PrimeSpectrum.asIdeal hk
  have key : ∀ σ : Spec (.of ℂ) ⟶ P, σ ≫ q = 𝟙 _ → ∀ r, σ.appTop.hom (q.appTop.hom r) = r :=
    fun σ hσ r ↦ by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hσ]
      rfl
  refine Subtype.ext (ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun a ↦ ?_)))
  have hmem : a - q.appTop.hom (σ₁.appTop.hom a) ∈ RingHom.ker σ₁.appTop.hom := by
    rw [RingHom.mem_ker, map_sub, key σ₁ h₁, sub_self]
  rw [hk', RingHom.mem_ker, map_sub, key σ₂ h₂, sub_eq_zero] at hmem
  exact hmem.symm

/-- The fibre of the finite morphism `φ` over the `ℂ`-point `t` has finitely many `ℂ`-points:
they are sections of the finite `Spec ℂ ×_{T°} T' ⟶ Spec ℂ`. -/
private theorem finite_sheets {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} (To : (curveScheme T).Opens)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    {T' : Scheme.{0}} (φ : T' ⟶ (To : Scheme.{0})) [IsFinite φ] :
    Finite {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom} := by
  haveI := finite_sections (pullback.fst t.hom φ)
  refine Finite.of_injective
    (fun t'' ↦ (⟨pullback.lift (𝟙 _) t''.1.hom (by rw [Category.id_comp, t''.2]),
      pullback.lift_fst _ _ _⟩ : {σ : Spec (.of ℂ) ⟶ pullback t.hom φ //
        σ ≫ pullback.fst t.hom φ = 𝟙 _})) ?_
  intro a b hab
  have := congrArg (fun σ ↦ σ.1 ≫ pullback.snd t.hom φ) hab
  simp only [pullback.lift_snd] at this
  exact Subtype.ext (ComplexPoints.ext this)

/-- **The monodromy image is closed under composition**: the transport along the concatenation
of two loops is the composite of the transports. -/
private theorem monodromy_mul_mem {Z : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z) {t : Z}
    {G : Set (Module.End ℚ (((TopCat.Sheaf.forget _ _).obj F).stalk t))}
    (hG : ∀ g, g ∈ G ↔ ∃ γ : Path t t, IsTransport F γ g) :
    ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G := by
  intro g hg h hh
  obtain ⟨γ₁, hγ₁⟩ := (hG g).1 hg
  obtain ⟨γ₂, hγ₂⟩ := (hG h).1 hh
  exact (hG _).2 ⟨γ₂.trans γ₁, hγ₁.trans F hγ₂⟩

/-- **Parallel transports of a local system along loops are surjective.** -/
private theorem monodromy_surjective {Z : TopCat.{0}} {F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z}
    (hF : IsLocalSystem F) {t : Z}
    {G : Set (Module.End ℚ (((TopCat.Sheaf.forget _ _).obj F).stalk t))}
    (hG : ∀ g, g ∈ G ↔ ∃ γ : Path t t, IsTransport F γ g) :
    ∀ h ∈ G, Function.Surjective h := by
  intro h hh
  obtain ⟨γ, hγ⟩ := (hG h).1 hh
  exact IsTransport.surjective F hF hγ

/-! ### The norm along a split cover

Over the fibre `F_t` the cover `𝓕' ⟶ 𝓕` is split by the sheets `F_t × {t''}`. If the norm of a
function, restricted to `F_t`, is the product of its restrictions to the sheets, then the
restriction of the norm of `𝓛'` is the tensor product of the restrictions of `𝓛'` to the sheets
(recognition of two invertible modules with the same transition units), and `c₁` of a tensor
product of a list of invertible modules is the sum of the `c₁` of the factors. -/

section SplitNormBlock

variable {X : Scheme.{0}}

/-- The ratio of two restricted generators over a smaller open is the restriction of their
ratio. -/
private theorem generatorRatioUnit_restrict_of_le (M : X.Modules) {U₁ U₂ A B : X.Opens}
    (x : GeneratorSections X.toRingedSpace M U₁) (y : GeneratorSections X.toRingedSpace M U₂)
    (hAB : A ≤ B) (hB₁ : B ≤ U₁) (hB₂ : B ≤ U₂) :
    generatorRatioUnit M A (generatorRestrict M (hAB.trans hB₁) x)
        (generatorRestrict M (hAB.trans hB₂) y) =
      Units.map (RingCat.Hom.hom ((structureSheaf X.sheaf).obj.map (homOfLE hAB).op))
        (generatorRatioUnit M B (generatorRestrict M hB₁ x) (generatorRestrict M hB₂ y)) := by
  refine Eq.trans ?_ (generatorRatioUnit_restrict M hAB _ _)
  exact congrArg₂ (generatorRatioUnit M A) (generatorRestrict_trans M hB₁ hAB x).symm
    (generatorRestrict_trans M hB₂ hAB y).symm

section SplitNorm

variable {Y Z : Scheme.{0}} (p : X ⟶ Y) [IsFinite p] [Stacks.Morphisms.IsFiniteLocallyFree p]
  (ι : Z ⟶ Y) {S : Type} (σ : S → (Z ⟶ X)) (hσ : ∀ s, σ s ≫ p = ι) (L : X.Modules)
  [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]

include hσ in
private theorem preimage_le_sheet (s : S) (W : Y.Opens) : ι ⁻¹ᵁ W ≤ σ s ⁻¹ᵁ (p ⁻¹ᵁ W) := by
  rw [← hσ s, Scheme.Hom.comp_preimage]

/-- The generator of `σ^* L` over `ι⁻¹(V)` attached to a chart of the norm. -/
private def sheetGen (i : Stacks.Divisors.NormChart p L) (s : S) :
    GeneratorSections Z.toRingedSpace ((Scheme.Modules.pullback (σ s)).obj L) (ι ⁻¹ᵁ i.val) :=
  generatorRestrict _ (preimage_le_sheet p ι σ hσ s i.val)
    (pullbackGenerator (σ s) L
          Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
      (p ⁻¹ᵁ i.val) (Stacks.Divisors.normChartSourceGenerator p L i))

/-- The generating section of the chart `i` of `L` on `p⁻¹(i)`. -/
private abbrev chartGen (i : Stacks.Divisors.NormChart p L) :
    GeneratorSections X.toRingedSpace L (p ⁻¹ᵁ i.val) :=
  Stacks.Divisors.normChartSourceGenerator p L i

/-- The transition unit upstairs of two chart generators over `p⁻¹(i ⊓ j)`. -/
private abbrev chartRatio (i j : Stacks.Divisors.NormChart p L) : (Γ(X, p ⁻¹ᵁ (i.val ⊓ j.val)))ˣ :=
  generatorRatioUnit L (p ⁻¹ᵁ (i.val ⊓ j.val))
    (generatorRestrict L (p.preimage_mono inf_le_right) (chartGen p L j))
    (generatorRestrict L (p.preimage_mono inf_le_left) (chartGen p L i))

include hσ in
private theorem sheetGen_restrict (j : Stacks.Divisors.NormChart p L) (s : S) {V : Y.Opens}
    (h : V ≤ j.val) :
    generatorRestrict _ (ι.preimage_mono h) (sheetGen p ι σ hσ L j s) =
      generatorRestrict _ (preimage_le_sheet p ι σ hσ s V)
        (pullbackGenerator (σ s) L
          Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
          (p ⁻¹ᵁ V) (generatorRestrict L (p.preimage_mono h) (chartGen p L j))) := by
  have e := pullbackGenerator_restrict (σ s) L
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
    (p.preimage_mono h) (chartGen p L j)
  exact (generatorRestrict_trans _ _ _ _).trans
    ((generatorRestrict_trans _ _ _ _).symm.trans (congrArg (generatorRestrict _ _) e))

include hσ in
private theorem generatorRatioUnit_sheetGen (i j : Stacks.Divisors.NormChart p L) (s : S) :
    generatorRatioUnit _ (ι ⁻¹ᵁ (i.val ⊓ j.val))
        (generatorRestrict _ (ι.preimage_mono inf_le_right) (sheetGen p ι σ hσ L j s))
        (generatorRestrict _ (ι.preimage_mono inf_le_left) (sheetGen p ι σ hσ L i s)) =
      Units.map ((σ s).appLE (p ⁻¹ᵁ (i.val ⊓ j.val)) (ι ⁻¹ᵁ (i.val ⊓ j.val))
          (preimage_le_sheet p ι σ hσ s (i.val ⊓ j.val))).hom.toMonoidHom
        (chartRatio p L i j) :=
  (congrArg₂ (generatorRatioUnit _ (ι ⁻¹ᵁ (i.val ⊓ j.val)))
      (sheetGen_restrict p ι σ hσ L j s inf_le_right)
      (sheetGen_restrict p ι σ hσ L i s inf_le_left)).trans
    ((generatorRatioUnit_restrict _ _ _ _).trans
      ((congrArg _ (generatorRatioUnit_pullbackGenerator _ _ _ _ _ _)).trans (Units.ext rfl)))

/-- The norm of `L` along `p`. -/
private abbrev nmL : Y.Modules :=
  Stacks.Divisors.normInvertible p (Stacks.Norm.finiteLocallyFreeNorm p).toMorphismNormMap L

private theorem hasTrivializingTargetCover_L : Stacks.Divisors.HasTrivializingTargetCover p L :=
  @Stacks.Divisors.hasTrivializingTargetCover_of_isFinite _ _ p _ L
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible

/-- The generator of `ι^* Nm(L)` over `ι⁻¹(i)` attached to a chart of the norm. -/
private def normPullbackGen (i : Stacks.Divisors.NormChart p L) :
    GeneratorSections Z.toRingedSpace ((Scheme.Modules.pullback ι).obj (nmL p L))
      (ι ⁻¹ᵁ i.val) :=
  pullbackGenerator ι (nmL p L)
    (Stacks.Divisors.isInvertible_normInvertible p _ L (hasTrivializingTargetCover_L p L))
    i.val (Stacks.Divisors.normGenerator p _ L (hasTrivializingTargetCover_L p L) i.val
      (chartGen p L i))

private theorem normPullbackGen_restrict (j : Stacks.Divisors.NormChart p L) {V : Y.Opens}
    (h : V ≤ j.val) :
    generatorRestrict _ (ι.preimage_mono h) (normPullbackGen p ι L j) =
      pullbackGenerator ι (nmL p L)
        (Stacks.Divisors.isInvertible_normInvertible p _ L (hasTrivializingTargetCover_L p L))
        V (Stacks.Divisors.normGenerator p _ L (hasTrivializingTargetCover_L p L)
          V (generatorRestrict L (p.preimage_mono h) (chartGen p L j))) := by
  refine (pullbackGenerator_restrict ι (nmL p L) _ h _).trans ?_
  congr 1
  exact Subtype.ext (Stacks.Divisors.normGenerator_restrict p _ L _ h _).symm

private theorem generatorRatioUnit_normPullbackGen (i j : Stacks.Divisors.NormChart p L) :
    generatorRatioUnit _ (ι ⁻¹ᵁ (i.val ⊓ j.val))
        (generatorRestrict _ (ι.preimage_mono inf_le_right) (normPullbackGen p ι L j))
        (generatorRestrict _ (ι.preimage_mono inf_le_left) (normPullbackGen p ι L i)) =
      Units.map (ι.app (i.val ⊓ j.val)).hom.toMonoidHom
        (Units.map ((Stacks.Norm.finiteLocallyFreeNorm p).app (i.val ⊓ j.val))
          (chartRatio p L i j)) :=
  (congrArg₂ (generatorRatioUnit _ (ι ⁻¹ᵁ (i.val ⊓ j.val)))
      (normPullbackGen_restrict p ι L j inf_le_right)
      (normPullbackGen_restrict p ι L i inf_le_left)).trans
    ((generatorRatioUnit_pullbackGenerator _ _ _ _ _ _).trans
      (congrArg _ (Stacks.Divisors.generatorRatioUnit_normGenerator _ _ _ _ _ _ _)))

/-- **The norm along a split cover.** If the norm of a function along `p`, pulled back along
`ι`, is the product of its pullbacks along the sheets `σ s`, then `ι^* Nm(L)` is the tensor product
of the `σ_s^* L`. -/
private def splitNormIso (l : List S)
    (hstar : ∀ (W : Y.Opens) (r : Γ(X, p ⁻¹ᵁ W)),
      ι.app W ((Stacks.Norm.finiteLocallyFreeNorm p).app W r) =
        (l.map fun s => (σ s).appLE (p ⁻¹ᵁ W) (ι ⁻¹ᵁ W) (preimage_le_sheet p ι σ hσ s W) r).prod) :
    (Scheme.Modules.pullback ι).obj (nmL p L) ≅
      schemeTensorList Z (fun s => (Scheme.Modules.pullback (σ s)).obj L) l :=
  isoOfChartGenerators (U := fun i : Stacks.Divisors.NormChart p L => ι ⁻¹ᵁ i.val)
    ((Scheme.Modules.pullback ι).obj (nmL p L))
    (schemeTensorList Z (fun s => (Scheme.Modules.pullback (σ s)).obj L) l)
    (normPullbackGen p ι L)
    (fun i => tensorListGenerator Z (fun s => (Scheme.Modules.pullback (σ s)).obj L)
      (fun s => sheetGen p ι σ hσ L i s) l)
    (fun i j A hi hj => by
      have hAB : A ≤ ι ⁻¹ᵁ (i.val ⊓ j.val) := fun x hx => ⟨hi hx, hj hx⟩
      refine (generatorRatioUnit_restrict_of_le (X := Z)
        (schemeTensorList Z (fun s => (Scheme.Modules.pullback (σ s)).obj L) l) _ _ hAB
          (ι.preimage_mono inf_le_right) (ι.preimage_mono inf_le_left)).trans ?_
      rw [generatorRatioUnit_restrict_of_le _ _ _ hAB (ι.preimage_mono inf_le_right)
          (ι.preimage_mono inf_le_left)]
      congr 1
      refine (congrArg₂ (generatorRatioUnit
          (schemeTensorList Z (fun s => (Scheme.Modules.pullback (σ s)).obj L) l) _)
        (tensorListGenerator_restrict Z _ (ι.preimage_mono inf_le_right) _ l)
        (tensorListGenerator_restrict Z _ (ι.preimage_mono inf_le_left) _ l)).trans ?_
      refine (generatorRatioUnit_tensorListGenerator Z _ _ _ _ l).trans ?_
      rw [generatorRatioUnit_normPullbackGen]
      refine Units.ext ?_
      have e := hstar (i.val ⊓ j.val) (chartRatio p L i j).val
      refine Eq.trans ?_ e.symm
      refine (map_list_prod (Units.coeHom _) _).trans ?_
      rw [List.map_map]
      exact (congrArg List.prod (List.map_congr_left fun s _ =>
        congrArg Units.val (generatorRatioUnit_sheetGen p ι σ hσ L i j s))))
    (fun x _ => by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (Stacks.Divisors.normChart_cover
        (hasTrivializingTargetCover_L p L) (show ι.base x ∈ (⊤ : Y.Opens) from trivial))
      exact Opens.mem_iSup.2 ⟨i, hi⟩)

end SplitNorm

variable [X.Over (Spec (.of ℂ))]

private theorem algebraicFirstChernClass_unit
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (_root_.SheafOfModules.unit X.ringCatSheaf)] :
    algebraicFirstChernClass (_root_.SheafOfModules.unit X.ringCatSheaf) = 0 := by
  have : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (schemeTensor X (_root_.SheafOfModules.unit X.ringCatSheaf)
        (_root_.SheafOfModules.unit X.ringCatSheaf)) :=
    @Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible _ _ _ _ _ _
      (isInvertible_schemeTensor X _ _ (isInvertible_unit X.presheaf X.ringCatSheaf.2)
        (isInvertible_unit X.presheaf X.ringCatSheaf.2))
  let e := isoOfChartGenerators (U := fun _ : PUnit.{1} => (⊤ : X.Opens))
    (_root_.SheafOfModules.unit X.ringCatSheaf)
    (schemeTensor X (_root_.SheafOfModules.unit X.ringCatSheaf)
        (_root_.SheafOfModules.unit X.ringCatSheaf))
    (fun _ => generatorOfIso (X := X.toRingedSpace) _ (Iso.refl _))
    (fun _ => tmulGenerator (generatorOfIso (X := X.toRingedSpace) _ (Iso.refl _))
      (generatorOfIso (X := X.toRingedSpace) _ (Iso.refl _)))
    (fun _ _ _ _ _ => (generatorRatioUnit_self _ _ _).trans (generatorRatioUnit_self _ _ _).symm)
    (le_iSup (fun _ : PUnit.{1} => (⊤ : X.Opens)) PUnit.unit)
  have h1 := (algebraicFirstChernClass_eq_of_iso e).trans
    (algebraicFirstChernClass_sheafTensor _ _)
  exact add_left_cancel (h1.symm.trans (add_zero _).symm)

private theorem algebraicFirstChernClass_tensorList {ι : Type*} (E : ι → X.Modules)
    [hE : ∀ i, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (E i)] (l : List ι) :
    @algebraicFirstChernClass X _ (schemeTensorList X E l)
        (@Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible _ _ _ _ _ _
          (isInvertible_schemeTensorList X E (fun i =>
            @Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
              _ _ _ _ _ _ (hE i)) l)) =
      (l.map fun i => algebraicFirstChernClass (E i)).sum := by
  have hT : ∀ l : List ι,
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (schemeTensorList X E l) :=
    fun l => @Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible
      _ _ _ _ _ _ (isInvertible_schemeTensorList X E (fun i =>
        @Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
          _ _ _ _ _ _ (hE i)) l)
  induction l with
  | nil => exact @algebraicFirstChernClass_unit X _ (hT [])
  | cons i l ih =>
    exact (@algebraicFirstChernClass_sheafTensor X _ (E i) (schemeTensorList X E l) _ (hT l)
      (hT (i :: l))).trans (by rw [List.map_cons, List.sum_cons, ← ih])

end SplitNormBlock

/-! ### The norm along a split cover over `ℂ`

A finite étale scheme `T₀` over `ℂ` is split: its functions are the functions on its `ℂ`-points.
If `q : P ⟶ F` is the base change of `T₀ ⟶ Spec ℂ`, the norm along `q` of a function is then the
product of its restrictions along the sections of `q` induced by the `ℂ`-points of `T₀`. -/

section SplitOverComplex

private theorem appLE_eq_of_eq {A B : Scheme.{0}} {a b : A ⟶ B} (h : a = b) (U : B.Opens)
    (V : A.Opens) (e : V ≤ a ⁻¹ᵁ U) : a.appLE U V e = b.appLE U V (h ▸ e) := by
  subst h
  rfl

private theorem norm_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → R) :
    Algebra.norm R f = ∏ i, f i := by
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun R ι)]
  have : Algebra.leftMulMatrix (Pi.basisFun R ι) f = Matrix.diagonal f := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.diagonal_apply]
    simp [Pi.single_apply, eq_comm]
  rw [this, Matrix.det_diagonal]

private theorem projectiveNorm_eq_prod_of_isPushout {k R B A : CommRingCat.{0}}
    {α : k ⟶ R} {β : k ⟶ B} {γ : R ⟶ A} {δ : B ⟶ A} (H : IsPushout α β γ δ)
    {S : Type} [Fintype S] [DecidableEq S] (χ : S → (B ⟶ k)) (hχ : ∀ s, β ≫ χ s = 𝟙 k)
    (hbij : Function.Bijective fun (b : B) (s : S) => χ s b)
    (ε : S → (A ⟶ R)) (hεγ : ∀ s, γ ≫ ε s = 𝟙 R) (hεδ : ∀ s, δ ≫ ε s = χ s ≫ α) :
    letI := γ.hom.toAlgebra
    ∃ (_ : Module.Free R A) (_ : Module.Finite R A),
      ∀ a : A, Algebra.norm R a = ∏ s, ε s a := by
  letI := α.hom.toAlgebra
  letI := β.hom.toAlgebra
  letI := γ.hom.toAlgebra
  let χa : B →ₐ[k] (S → k) :=
    { toRingHom := Pi.ringHom fun s => (χ s).hom
      commutes' := fun c => funext fun s => congr($(hχ s) c) }
  let χe : B ≃ₐ[k] (S → k) := AlgEquiv.ofBijective χa hbij
  let hT := CommRingCat.isPushout_tensorProduct k R B
  let e := hT.isoIsPushout R B H
  let e' : R ⊗[k] B ≃ₐ[R] A :=
    { __ := e.commRingCatIsoToRingEquiv
      commutes' r := congr($(hT.inl_isoIsPushout_hom R B H) r) }
  have he' : ∀ b : B, e' ((1 : R) ⊗ₜ[k] b) = δ b := fun b =>
    congr($(hT.inr_isoIsPushout_hom R B H) b)
  let F : R ⊗[k] B ≃ₐ[R] (S → R) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl χe).trans
      ((Algebra.TensorProduct.piRight k R R (fun _ : S => k)).trans
        (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid k R R))
  let E : A ≃ₐ[R] (S → R) := e'.symm.trans F
  have hE : ∀ s a, E a s = ε s a := by
    intro s
    have key : CommRingCat.ofHom ((Pi.evalRingHom (fun _ : S => R) s).comp E.toRingHom) =
        ε s := by
      refine H.hom_ext ?_ ?_
      · ext r
        change E (γ r) s = (γ ≫ ε s) r
        rw [hεγ s]
        change E (algebraMap R A r) s = r
        rw [E.commutes]
        rfl
      · ext b
        change E (δ b) s = (δ ≫ ε s) b
        rw [hεδ s, ← he' b]
        change F (e'.symm (e' _)) s = _
        rw [AlgEquiv.symm_apply_apply]
        simp [F, χe, χa, Algebra.TensorProduct.piRight_tmul]
        rw [Algebra.smul_def, mul_one]
        rfl
    exact fun a => congr($key a)
  haveI : Module.Finite R A := Module.Finite.equiv E.symm.toLinearEquiv
  haveI : Module.Free R A := Module.Free.of_equiv E.symm.toLinearEquiv
  haveI : Module.Projective R A := Module.Projective.of_equiv E.symm.toLinearEquiv
  refine ⟨inferInstance, inferInstance, fun a => ?_⟩
  rw [← Algebra.projectiveNorm_eq_norm_of_free,
    ← Algebra.projectiveNorm_algEquiv (R := R) E a, Algebra.projectiveNorm_eq_norm_of_free, norm_pi]
  exact Finset.prod_congr rfl fun s _ => hE s a

private theorem bijective_eval_of_isFiniteSplit {K B : Type*} [Field K] [CommRing B] [Algebra K B]
    [Algebra.IsFiniteSplit K B] {S : Type*} [Fintype S] (Ψ : S → (B →ₐ[K] K))
    (hΨ : Function.Bijective Ψ) :
    Function.Bijective fun (b : B) (s : S) => Ψ s b := by
  let L : B →ₗ[K] (S → K) := LinearMap.pi fun s => (Ψ s).toLinearMap
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have hmem : ∀ p : PrimeSpectrum B, b ∈ p.asIdeal := by
      intro p
      obtain ⟨s, hs⟩ := hΨ.2 ((Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K B).symm p)
      have hker : RingHom.ker (Ψ s) = p.asIdeal := by
        rw [hs]
        exact congrArg PrimeSpectrum.asIdeal
          ((Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K B).apply_symm_apply p)
      rw [← hker, RingHom.mem_ker]
      exact congrFun hb s
    have hnil : IsNilpotent b := by
      rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
      intro J hJ
      exact hmem ⟨J, hJ⟩
    haveI := Algebra.FormallyUnramified.isReduced_of_field K B
    exact hnil.eq_zero
  have hrank : Module.finrank K B = Module.finrank K (S → K) := by
    rw [Module.finrank_pi, ← Algebra.IsFiniteSplit.natCard_algHom_eq_finrank (K := K),
      Nat.card_eq_fintype_card.symm, Nat.card_congr (Equiv.ofBijective Ψ hΨ).symm]
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj⟩

/-- Sections of an étale affine scheme over `ℂ` separate its `ℂ`-points. -/
private theorem bijective_appTop_sections {T₀ : Scheme.{0}} [IsAffine T₀] (g : T₀ ⟶ Spec (.of ℂ))
    [Etale g] {S : Type} [Fintype S] (τ : S → (Spec (.of ℂ) ⟶ T₀))
    (hτg : ∀ s, τ s ≫ g = 𝟙 _) (hτinj : Function.Injective τ)
    (hτsurj : ∀ τ' : Spec (.of ℂ) ⟶ T₀, τ' ≫ g = 𝟙 _ → ∃ s, τ s = τ') :
    Function.Bijective fun (b : Γ(T₀, ⊤)) (s : S) => (τ s).appTop b := by
  let θ := Scheme.ΓSpecIso (CommRingCat.of ℂ)
  letI : Algebra ℂ Γ(T₀, ⊤) := (θ.inv ≫ g.appTop).hom.toAlgebra
  have hgτ : ∀ s, g.appTop ≫ (τ s).appTop = 𝟙 _ := fun s => by
    rw [← Scheme.Hom.comp_appTop, hτg s]
    rfl
  let Ψ : S → (Γ(T₀, ⊤) →ₐ[ℂ] ℂ) := fun s =>
    { toRingHom := ((τ s).appTop ≫ θ.hom).hom
      commutes' := fun c => by
        change ((θ.inv ≫ g.appTop) ≫ (τ s).appTop ≫ θ.hom) c = c
        rw [Category.assoc, reassoc_of% (hgτ s), Iso.inv_hom_id]
        rfl }
  have hetale : RingHom.Etale (θ.inv ≫ g.appTop).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso θ.inv))
      (HasRingHomProperty.appTop @Etale g inferInstance)
  haveI : Algebra.Etale ℂ Γ(T₀, ⊤) := hetale
  have hΨ : Function.Bijective Ψ := by
    constructor
    · intro s s' hss'
      apply hτinj
      apply ext_of_isAffine
      exact (cancel_mono θ.hom).1 (CommRingCat.hom_ext (congrArg AlgHom.toRingHom hss'))
    · intro f
      let ψ : Γ(T₀, ⊤) ⟶ Γ(Spec (.of ℂ), ⊤) := CommRingCat.ofHom f.toRingHom ≫ θ.inv
      let τ' : Spec (.of ℂ) ⟶ T₀ :=
        (Spec (.of ℂ)).isoSpec.hom ≫ Spec.map ψ ≫ T₀.isoSpec.inv
      have hτ' : τ'.appTop = ψ := by
        apply Spec.map_injective
        have e2 : τ' ≫ T₀.isoSpec.hom = (Spec (.of ℂ)).isoSpec.hom ≫ Spec.map ψ := by
          simp [τ']
        exact (cancel_epi (Spec (.of ℂ)).isoSpec.hom).1
          ((Scheme.isoSpec_hom_naturality τ').trans e2)
      have hτ'g : τ' ≫ g = 𝟙 _ := by
        apply ext_of_isAffine
        rw [Scheme.Hom.comp_appTop, hτ']
        ext c
        change θ.inv (f (g.appTop c)) = c
        have hf := f.commutes (θ.hom c)
        change f ((θ.inv ≫ g.appTop) (θ.hom c)) = θ.hom c at hf
        rw [CommRingCat.comp_apply, ← CommRingCat.comp_apply θ.hom θ.inv, Iso.hom_inv_id] at hf
        rw [show g.appTop c = g.appTop ((𝟙 _ : Γ(Spec (.of ℂ), ⊤) ⟶ _) c) from rfl, hf]
        exact congrArg (fun m => m c) θ.hom_inv_id
      obtain ⟨s, hs⟩ := hτsurj τ' hτ'g
      refine ⟨s, AlgHom.ext fun b => ?_⟩
      change θ.hom ((τ s).appTop b) = f b
      rw [hs, hτ']
      change θ.hom (θ.inv (f b)) = f b
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
      rfl
  have hθ : Function.Bijective fun (v : S → ℂ) (s : S) => θ.inv (v s) :=
    (Equiv.piCongrRight fun _ => θ.symm.commRingCatIsoToRingEquiv.toEquiv).bijective
  convert hθ.comp (bijective_eval_of_isFiniteSplit Ψ hΨ) using 1
  funext b s
  change _ = θ.inv (θ.hom ((τ s).appTop b))
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
  rfl

private theorem id_appLE_self {A : Scheme.{0}} (U : A.Opens) (e : U ≤ (𝟙 A) ⁻¹ᵁ U) :
    Scheme.Hom.appLE (𝟙 A) U U e = 𝟙 _ := by
  ext x
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact congrArg (fun m => m x) (A.presheaf.map_id (Opposite.op U))

private theorem finiteLocallyFreeNorm_eq_prod_of_split_of_isAffineOpen
    {F T₀ P : Scheme.{0}} (h : F ⟶ Spec (.of ℂ)) (g : T₀ ⟶ Spec (.of ℂ)) [IsAffine T₀]
    [Etale g] (q : P ⟶ F) (r : P ⟶ T₀) (H : IsPullback q r h g)
    [Stacks.Morphisms.IsFiniteLocallyFree q] [IsAffineHom q]
    {S : Type} [Fintype S] [DecidableEq S] (τ : S → (Spec (.of ℂ) ⟶ T₀))
    (hτg : ∀ s, τ s ≫ g = 𝟙 _) (hτinj : Function.Injective τ)
    (hτsurj : ∀ τ' : Spec (.of ℂ) ⟶ T₀, τ' ≫ g = 𝟙 _ → ∃ s, τ s = τ')
    (σ : S → (F ⟶ P)) (hσq : ∀ s, σ s ≫ q = 𝟙 _) (hσr : ∀ s, σ s ≫ r = h ≫ τ s)
    (W : F.Opens) (hW : IsAffineOpen W) (hle : ∀ s, W ≤ σ s ⁻¹ᵁ (q ⁻¹ᵁ W))
    (a : Γ(P, q ⁻¹ᵁ W)) :
    (Stacks.Norm.finiteLocallyFreeNorm q).app W a = ∏ s, (σ s).appLE (q ⁻¹ᵁ W) W (hle s) a := by
  have hiso := isIso_pushoutSection_of_isAffineOpen H (US := ⊤) (UT := ⊤) (UX := W)
    (UY := q ⁻¹ᵁ W) le_top le_top (by simp) (isAffineOpen_top _) (isAffineOpen_top _) hW
  have H' := (isIso_pushoutSection_iff H le_top le_top (by simp)).1 hiso
  have hγ : q.appLE W (q ⁻¹ᵁ W) le_rfl = q.app W := (Scheme.Hom.app_eq_appLE q).symm
  rw [hγ] at H'
  have hbij : Function.Bijective fun (b : Γ(T₀, ⊤)) (s : S) => (τ s).appLE ⊤ ⊤ le_top b := by
    convert bijective_appTop_sections g τ hτg hτinj hτsurj using 1
    funext b s
    simp only [Scheme.Hom.appLE, Opens.map_top, homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
    rfl
  obtain ⟨hfin, hproj, hnorm⟩ := projectiveNorm_eq_prod_of_isPushout H'
    (fun s => (τ s).appLE ⊤ ⊤ le_top)
    (fun s => (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      ((appLE_eq_of_eq (hτg s) _ _ _).trans (id_appLE_self _ _)))
    hbij
    (fun s => (σ s).appLE (q ⁻¹ᵁ W) W (hle s))
    (fun s => by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq (hσq s),
        id_appLE_self])
    (fun s => (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans
      ((appLE_eq_of_eq (hσr s) _ _ _).trans (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm))
  rw [(Stacks.Norm.finiteLocallyFreeNorm q).isDeterminantNorm W hW (hW.preimage q) hfin hproj a]
  exact hnorm a

private theorem finiteLocallyFreeNorm_eq_prod_of_split
    {F T₀ P : Scheme.{0}} (h : F ⟶ Spec (.of ℂ)) (g : T₀ ⟶ Spec (.of ℂ)) [IsAffine T₀]
    [Etale g] (q : P ⟶ F) (r : P ⟶ T₀) (H : IsPullback q r h g)
    [Stacks.Morphisms.IsFiniteLocallyFree q] [IsAffineHom q]
    {S : Type} [Fintype S] (τ : S → (Spec (.of ℂ) ⟶ T₀))
    (hτg : ∀ s, τ s ≫ g = 𝟙 _) (hτinj : Function.Injective τ)
    (hτsurj : ∀ τ' : Spec (.of ℂ) ⟶ T₀, τ' ≫ g = 𝟙 _ → ∃ s, τ s = τ')
    (σ : S → (F ⟶ P)) (hσq : ∀ s, σ s ≫ q = 𝟙 _) (hσr : ∀ s, σ s ≫ r = h ≫ τ s)
    (V : F.Opens) (hle : ∀ s, V ≤ σ s ⁻¹ᵁ (q ⁻¹ᵁ V)) (a : Γ(P, q ⁻¹ᵁ V)) :
    (Stacks.Norm.finiteLocallyFreeNorm q).app V a = ∏ s, (σ s).appLE (q ⁻¹ᵁ V) V (hle s) a := by
  classical
  refine Stacks.Norm.section_eq_of_affine_restrictions V _ _ fun W i => ?_
  have hleW : ∀ s, W.1 ≤ σ s ⁻¹ᵁ (q ⁻¹ᵁ W.1) := fun s => by
    rw [← Scheme.Hom.comp_preimage, hσq s]; exact le_rfl
  rw [← (Stacks.Norm.finiteLocallyFreeNorm q).naturality i a,
    finiteLocallyFreeNorm_eq_prod_of_split_of_isAffineOpen h g q r H τ hτg hτinj hτsurj σ hσq
      hσr W.1 W.2 hleW, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

end SplitOverComplex

/-- The sheet `F_t × {t''}` lies over the inclusion `F_t ⟶ 𝓕`. -/
private theorem sheetι_comp_fst {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {To : (curveScheme T).Opens}
    {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)} {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}
    (s : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}) :
    sheetι s ≫ pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ = pointFibreToFamily sY π To t :=
  pullback.lift_fst _ _ _

/-- The sheet `F_t × {t''}`, as a section of the base change `F_t ×_𝓕 𝓕' ⟶ F_t` of the cover. -/
private def fibreSheet {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}
    {π : Yt ⟶ Y} {To : (curveScheme T).Opens} {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)}
    {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}
    (s : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}) :
    pointFibre sY π To t ⟶
      pullback (pointFibreToFamily sY π To t) (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) :=
  pullback.lift (𝟙 _) (sheetι s) (by rw [Category.id_comp, sheetι_comp_fst])

private theorem fibreSheet_comp_fst {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {To : (curveScheme T).Opens}
    {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)} {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}
    (s : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}) :
    fibreSheet (π := π) s ≫ pullback.fst (pointFibreToFamily sY π To t)
      (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) = 𝟙 _ :=
  pullback.lift_fst _ _ _

private theorem fibreSheet_comp_snd {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {To : (curveScheme T).Opens}
    {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)} {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}
    (s : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}) :
    fibreSheet (π := π) s ≫ pullback.snd (pointFibreToFamily sY π To t)
      (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) = sheetι s :=
  pullback.lift_snd _ _ _

private theorem fibreSheet_preimage_le {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    {T : IrreducibleCloseds Y} {π : Yt ⟶ Y} {To : (curveScheme T).Opens}
    {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)} {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}
    (s : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom})
    (V : (pointFibre sY π To t).Opens) :
    V ≤ fibreSheet (π := π) s ⁻¹ᵁ (pullback.fst (pointFibreToFamily sY π To t)
      (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, fibreSheet_comp_fst]
  exact le_rfl

/-- **The norm along the split cover of the fibre.** Over `F_t`, the base change
`F_t ×_𝓕 𝓕' ⟶ F_t` of the cover is the disjoint union of the sheets `F_t × {t''}` (the fibre of the
finite étale `φ` over the `ℂ`-point `t` is a disjoint union of copies of `Spec ℂ`, one for each
`ℂ`-point `t''` above `t`), so the determinant of multiplication by a function `a` is the product
of the restrictions of `a` to the sheets. -/
private theorem finiteLocallyFreeNorm_fibre_eq_prod
    {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (T : IrreducibleCloseds Y) (π : Yt ⟶ Y)
    (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    {T' : Scheme.{0}} (φ : T' ⟶ (To : Scheme.{0})) [IsFinite φ] [Etale φ]
    [Stacks.Morphisms.IsFiniteLocallyFree (pullback.fst (pointFibreToFamily sY π To t)
      (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ))]
    [Fintype {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}]
    (V : (pointFibre sY π To t).Opens)
    (a : Γ(pullback (pointFibreToFamily sY π To t)
      (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ),
      pullback.fst (pointFibreToFamily sY π To t)
        (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) ⁻¹ᵁ V)) :
    (Stacks.Norm.finiteLocallyFreeNorm (pullback.fst (pointFibreToFamily sY π To t)
        (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ))).app V a =
      ∏ s, (fibreSheet s).appLE _ V (fibreSheet_preimage_le s V) a := by
  classical
  have hjf : pointFibreToFamily sY π To t ≫ pullback.snd π (To.ι ≫ curveι T) =
      pointFibreSnd sY π To t ≫ t.hom := by
    unfold pointFibreToFamily pointFibreSnd
    exact pullback.lift_snd _ _ _
  have hr : (pullback.fst (pointFibreToFamily sY π To t)
        (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) ≫ pointFibreSnd sY π To t) ≫ t.hom =
      (pullback.snd (pointFibreToFamily sY π To t)
        (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) ≫
          pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ) ≫ φ := by
    rw [Category.assoc, ← hjf, pullback.condition_assoc, pullback.condition, Category.assoc]
  let r := pullback.lift _ _ hr
  have hbig := ((IsPullback.of_hasPullback (pointFibreToFamily sY π To t)
      (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)).flip.paste_horiz
    (IsPullback.of_hasPullback (pullback.snd π (To.ι ≫ curveι T)) φ).flip)
  rw [hjf, ← pullback.lift_snd _ _ hr] at hbig
  have H := (hbig.of_right (pullback.lift_fst _ _ hr)
    (IsPullback.of_hasPullback t.hom φ).flip).flip
  let τ : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom} →
      (Spec (.of ℂ) ⟶ pullback t.hom φ) := fun s =>
    pullback.lift (𝟙 _) s.1.hom (by rw [Category.id_comp]; exact s.2.symm)
  refine finiteLocallyFreeNorm_eq_prod_of_split (pointFibreSnd sY π To t)
    (pullback.fst t.hom φ) _ r H τ (fun s => pullback.lift_fst _ _ _) ?_ ?_ fibreSheet
    fibreSheet_comp_fst ?_ V
    (fun s => fibreSheet_preimage_le s V) a
  · intro a b hab
    have := congrArg (fun σ => σ ≫ pullback.snd t.hom φ) hab
    simp only [τ, pullback.lift_snd] at this
    exact Subtype.ext (ComplexPoints.ext this)
  · intro τ' hτ'
    have h2 : (τ' ≫ pullback.snd t.hom φ) ≫ φ = t.hom := by
      rw [Category.assoc, ← pullback.condition, reassoc_of% hτ']
    refine ⟨⟨⟨τ' ≫ pullback.snd t.hom φ, ?_⟩, h2⟩, ?_⟩
    · change (τ' ≫ pullback.snd t.hom φ) ≫ φ ≫ To.ι ≫ curveι T ≫ sY = 𝟙 _
      rw [← Category.assoc _ φ, h2]
      exact t.2
    · apply pullback.hom_ext
      · simp only [τ, pullback.lift_fst, hτ']
      · simp only [τ, pullback.lift_snd]
  · intro s
    apply pullback.hom_ext
    · simp only [r, τ, Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [← Category.assoc, fibreSheet_comp_fst, Category.id_comp]
    · simp only [r, τ, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, fibreSheet_comp_snd]
      unfold sheetι
      exact pullback.lift_snd _ _ _

/-- **The norm over the fibre is the product over the sheets.** For a function `r` on the inverse
image in `𝓕' = 𝓕 ×_{T°} T'` of an open `W ⊆ 𝓕`, the restriction to `F_t` of its norm along the
finite locally free `𝓕' ⟶ 𝓕` is the product of the restrictions of `r` to the sheets
`F_t × {t''}`: the norm commutes with the base change to `F_t`, along which it is the product over
the sheets (`finiteLocallyFreeNorm_fibre_eq_prod`). -/
private theorem pointFibreToFamily_app_norm_eq_prod
    {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (T : IrreducibleCloseds Y) (π : Yt ⟶ Y)
    (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    {T' : Scheme.{0}} (φ : T' ⟶ (To : Scheme.{0})) [IsFinite φ] [Etale φ]
    [Stacks.Morphisms.IsFiniteLocallyFree (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)]
    [Fintype {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}]
    (W : (pullback π (To.ι ≫ curveι T)).Opens)
    (r : Γ(pullback (pullback.snd π (To.ι ≫ curveι T)) φ,
      pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ ⁻¹ᵁ W)) :
    (pointFibreToFamily sY π To t).app W
        ((Stacks.Norm.finiteLocallyFreeNorm (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)).app
          W r) =
      ∏ s, (sheetι s).appLE _ _ (preimage_le_sheet _ (pointFibreToFamily sY π To t) sheetι
        sheetι_comp_fst s W) r := by
  obtain ⟨h', hbc⟩ := Stacks.Norm.finiteLocallyFreeNorm_baseChange
    (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)
    (pullback.fst (pointFibreToFamily sY π To t)
      (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ))
    (pullback.snd _ _) (pointFibreToFamily sY π To t) (IsPullback.of_hasPullback _ _).flip
  rw [← hbc W r, finiteLocallyFreeNorm_fibre_eq_prod sY T π To t φ]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_eq (fibreSheet_comp_snd s)]

/-- **Norms over the fibre.** Over `F_t` the cover `𝓕' ⟶ 𝓕` splits as the disjoint union of the
sheets `F_t × {t''}`, `t''` running over the `ℂ`-points of `T'` above `t` (the fibre of the finite
étale `φ` over a `ℂ`-point is reduced and consists of `ℂ`-points). As norms commute with base
change and the norm along a split cover is the tensor product of the restrictions to the sheets,
and `c₁` is additive under tensor products and natural under pullback, the first Chern class
of `(Nm 𝓛')|_{F_t}` is the sum of the first Chern classes of the restrictions of `𝓛'` to the
sheets. -/
private theorem pointFibreChernClass_pullback_normInvertible_eq_finsum
    {Y Yt : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (T : IrreducibleCloseds Y) (π : Yt ⟶ Y)
    (To : (curveScheme T).Opens) (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    {T' : Scheme.{0}} (φ : T' ⟶ (To : Scheme.{0})) [IsFinite φ] [Etale φ]
    [Stacks.Morphisms.IsFiniteLocallyFree (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L']
    [Finite {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}] :
    ∃ _ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
        (pointFibre sY π To t).ringCatSheaf.2
        ((Scheme.Modules.pullback (pointFibreToFamily sY π To t)).obj
          (Stacks.Divisors.normInvertible
            (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)
            (Stacks.Norm.finiteLocallyFreeNorm
              (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)).toMorphismNormMap L')),
      pointFibreChernClass sY π To t
          ((Scheme.Modules.pullback (pointFibreToFamily sY π To t)).obj
            (Stacks.Divisors.normInvertible
              (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)
              (Stacks.Norm.finiteLocallyFreeNorm
                (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)).toMorphismNormMap L')) =
        ∑ᶠ s : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom},
          pointFibreChernClass sY π To t ((Scheme.Modules.pullback (sheetι s)).obj L') := by
  classical
  haveI := Fintype.ofFinite {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom}
  have hstar : ∀ (W : (pullback π (To.ι ≫ curveι T)).Opens)
      (r : Γ(pullback (pullback.snd π (To.ι ≫ curveι T)) φ,
        pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ ⁻¹ᵁ W)),
      (pointFibreToFamily sY π To t).app W
          ((Stacks.Norm.finiteLocallyFreeNorm
            (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)).app W r) =
        (Finset.univ.toList.map fun s => (sheetι s).appLE _ _ (preimage_le_sheet _
          (pointFibreToFamily sY π To t) sheetι sheetι_comp_fst s W) r).prod := fun W r =>
    (pointFibreToFamily_app_norm_eq_prod sY T π To t φ W r).trans (Finset.prod_map_toList _ _).symm
  let e := splitNormIso _ (pointFibreToFamily sY π To t) sheetι sheetι_comp_fst L'
    Finset.univ.toList hstar
  haveI : SheafOfModules.IsInvertible (pullback π (To.ι ≫ curveι T)).presheaf
      (pullback π (To.ι ≫ curveι T)).ringCatSheaf.2
        (nmL (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) L') :=
    @Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible _ _ _ _ _ _
      (Stacks.Divisors.isInvertible_normInvertible _ _ L'
        (hasTrivializingTargetCover_L (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) L'))
  haveI : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
      (pointFibre sY π To t).ringCatSheaf.2
      (Stacks.SheafOfModules.schemeTensorList _ (fun s => (Scheme.Modules.pullback (sheetι
        (sY := sY) (T := T) (π := π) (To := To) (t := t) (φ := φ) s)).obj L')
        Finset.univ.toList) :=
    @Stacks.InvertibleBridge.algebraicGeometryIsInvertible_of_stacksIsInvertible _ _ _ _ _ _
      (Stacks.SheafOfModules.isInvertible_schemeTensorList _ _ (fun _ =>
        @Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
          _ _ _ _ _ _ _) _)
  refine ⟨inferInstance, ?_⟩
  unfold pointFibreChernClass
  have h := (algebraicFirstChernClass_eq_of_iso e).trans
    (algebraicFirstChernClass_tensorList (fun s => (Scheme.Modules.pullback (sheetι
      (sY := sY) (T := T) (π := π) (To := To) (t := t) (φ := φ) s)).obj L') Finset.univ.toList)
  refine (congrArg (singularCohomology.mapCoeff (Int.castRingHom ℚ) 2) h).trans ?_
  rw [map_list_sum, List.map_map, finsum_eq_sum_of_fintype, ← Finset.sum_map_toList]
  rfl

/-! ### Analytic inputs: the cover on complex points

The realization `T'^an ⟶ T°^an` of the finite étale cover is a finite covering map, and
`T'^an` is connected. -/

section AnalyticInputs

open Polynomial

private theorem isOpenEmbedding_restrict_of_section {E B : Type*} [TopologicalSpace E]
    [TopologicalSpace B] {f : E → B} (hf : Continuous f) {N : Set E} (hN : IsOpen N)
    {O : Set B} (hO : IsOpen O) {s : B → E} (hs : ContinuousOn s O)
    (hfs : ∀ b ∈ O, f (s b) = b) (hsf : ∀ e ∈ N, f e ∈ O ∧ s (f e) = e) :
    IsOpenEmbedding (N.restrict f) := by
  refine .of_continuous_injective_isOpenMap (hf.comp continuous_subtype_val) ?_ ?_
  · rintro ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ h
    change f e₁ = f e₂ at h
    apply Subtype.ext
    change e₁ = e₂
    calc e₁ = s (f e₁) := (hsf e₁ h₁).2.symm
      _ = s (f e₂) := by rw [h]
      _ = e₂ := (hsf e₂ h₂).2
  · intro V hV
    have hV' : IsOpen (Subtype.val '' V : Set E) := hN.isOpenMap_subtype_val V hV
    have : N.restrict f '' V = O ∩ s ⁻¹' (Subtype.val '' V) := by
      ext b
      constructor
      · rintro ⟨⟨e, he⟩, heV, rfl⟩
        exact ⟨(hsf e he).1, ⟨e, he⟩, heV, (hsf e he).2.symm⟩
      · rintro ⟨hb, ⟨e, he⟩, heV, hse⟩
        refine ⟨⟨e, he⟩, heV, ?_⟩
        change f e = b
        have hse' : e = s b := hse
        rw [hse', hfs b hb]
    rw [this]
    exact hs.isOpen_inter_preimage hO hV'

private theorem continuousOn_eval_map {Z A : Type*} [TopologicalSpace Z] [CommRing A]
    (ev : Z → A →+* ℂ) (hev : ∀ a, Continuous fun z => ev z a) {O : Set Z} {t : Z → ℂ}
    (ht : ContinuousOn t O) (q : A[X]) :
    ContinuousOn (fun z => (q.map (ev z)).eval (t z)) O := by
  have : ∀ z, (q.map (ev z)).eval (t z) =
      ∑ i ∈ Finset.range (q.natDegree + 1), ev z (q.coeff i) * t z ^ i := fun z => by
    rw [eval_eq_sum_range' (natDegree_map_le.trans_lt (Nat.lt_succ_self _))]
    simp only [coeff_map]
  simp_rw [this]
  exact continuousOn_finset_sum _ fun i _ => ((hev _).continuousOn).mul (ht.pow i)

set_option backward.isDefEq.respectTransparency false in
private theorem mk_C_eq_aeval {A : Type*} [CommRing A] (P : StandardEtalePair A) (q : A[X]) :
    (Ideal.Quotient.mk _ (C q) : P.Ring) = aeval P.X q := by
  have : aeval (R := A) P.X = (Ideal.Quotient.mkₐ A _).comp Polynomial.CAlgHom := by
    ext; simp [StandardEtalePair.Ring, StandardEtalePair.X]
  rw [this]
  rfl

/-- The ring map `R[X][Y]/⟨f, Yg - 1⟩ → ℂ` over `ev : R → ℂ` sending `X` to a root `t` of `f`
at which `g` does not vanish. -/
private def pairLift {A : Type*} [CommRing A] (P : StandardEtalePair A) (ev : A →+* ℂ) (t : ℂ)
    (h : (P.f.map ev).eval t = 0 ∧ (P.g.map ev).eval t ≠ 0) : P.Ring →+* ℂ :=
  letI := ev.toAlgebra
  (P.lift t ⟨by rw [aeval_def, RingHom.algebraMap_toAlgebra, ← Polynomial.eval_map]; exact h.1,
    isUnit_iff_ne_zero.mpr (by
      rw [aeval_def, RingHom.algebraMap_toAlgebra, ← Polynomial.eval_map]; exact h.2)⟩).toRingHom

private theorem pairLift_algebraMap {A : Type*} [CommRing A] (P : StandardEtalePair A)
    (ev : A →+* ℂ) (t : ℂ) (h : (P.f.map ev).eval t = 0 ∧ (P.g.map ev).eval t ≠ 0) (a : A) :
    pairLift P ev t h (algebraMap A P.Ring a) = ev a := by
  letI := ev.toAlgebra
  exact (AlgHom.commutes _ a).trans (RingHom.algebraMap_toAlgebra ev ▸ rfl)

private theorem pairLift_X {A : Type*} [CommRing A] (P : StandardEtalePair A)
    (ev : A →+* ℂ) (t : ℂ) (h : (P.f.map ev).eval t = 0 ∧ (P.g.map ev).eval t ≠ 0) :
    pairLift P ev t h P.X = t := by
  letI := ev.toAlgebra
  exact P.lift_X _ _

private theorem ringHom_ext_pair {A : Type*} [CommRing A] (P : StandardEtalePair A)
    {χ₁ χ₂ : P.Ring →+* ℂ}
    (h₁ : χ₁.comp (algebraMap A P.Ring) = χ₂.comp (algebraMap A P.Ring))
    (h₂ : χ₁ P.X = χ₂ P.X) : χ₁ = χ₂ := by
  letI := (χ₁.comp (algebraMap A P.Ring)).toAlgebra
  let e₁ : P.Ring →ₐ[A] ℂ := { χ₁ with commutes' := fun a => rfl }
  let e₂ : P.Ring →ₐ[A] ℂ :=
    { χ₂ with commutes' := fun a => (RingHom.congr_fun h₁ a).symm }
  have := P.hom_ext (f := e₁) (g := e₂) h₂
  ext r
  exact congrArg (fun e : P.Ring →ₐ[A] ℂ => e r) this

private theorem ringHom_aeval_X {A : Type*} [CommRing A] (P : StandardEtalePair A)
    (χ : P.Ring →+* ℂ) (q : A[X]) :
    χ (aeval P.X q) = (q.map (χ.comp (algebraMap A P.Ring))).eval (χ P.X) := by
  rw [aeval_def, Polynomial.hom_eval₂, Polynomial.eval_map]

private theorem continuous_pairRingHom_apply {A Z : Type*} [CommRing A] [TopologicalSpace Z]
    (P : StandardEtalePair A) (χ : Z → P.Ring →+* ℂ)
    (h₁ : ∀ a, Continuous fun z => χ z (algebraMap A P.Ring a))
    (h₂ : Continuous fun z => χ z P.X) (h₃ : ∀ z, χ z (aeval P.X P.g) ≠ 0) (r : P.Ring) :
    Continuous fun z => χ z r := by
  have hpoly : ∀ q : A[X], Continuous fun z => χ z (aeval P.X q) := by
    intro q
    refine Polynomial.induction_on q (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
    · simpa using h₁ a
    · simp only [map_add]; exact hp.add hq
    · simp only [map_mul, map_pow, aeval_C, aeval_X]; exact (h₁ a).mul (h₂.pow (n + 1))
  let yY : P.Ring := Ideal.Quotient.mk _ Polynomial.X
  have hY : ∀ z, χ z yY = (χ z (aeval P.X P.g))⁻¹ := fun z => by
    have h := congrArg (χ z) P.aeval_X_g_mul_mk_X
    exact (inv_eq_of_mul_eq_one_right ((map_mul (χ z) _ _).symm.trans (h.trans (map_one _)))).symm
  have hYc : Continuous fun z => χ z yY := by
    simp_rw [hY]
    exact (hpoly P.g).inv₀ h₃
  let mkP : A[X][X] →+* P.Ring := Ideal.Quotient.mk _
  obtain ⟨Q, rfl⟩ : ∃ Q, mkP Q = r := Ideal.Quotient.mk_surjective r
  refine Polynomial.induction_on Q (fun q => ?_) (fun p q hp hq => ?_) (fun n q _ => ?_)
  · have : mkP (C q) = aeval P.X q := mk_C_eq_aeval P q
    simp only [this]
    exact hpoly q
  · simp only [map_add]; exact hp.add hq
  · have : mkP (C q) = aeval P.X q := mk_C_eq_aeval P q
    have hX : mkP Polynomial.X = yY := rfl
    simp only [map_mul, map_pow, this, hX]
    exact (hpoly q).mul (hYc.pow (n + 1))

/-- An étale morphism of affine schemes over `ℂ` induces a local homeomorphism on `ℂ`-points. -/
private theorem isLocalHomeomorph_mapFun_of_etale_of_isAffine {U V : Scheme.{0}}
    [U.Over (Spec (.of ℂ))] [V.Over (Spec (.of ℂ))] [IsAffine U] [IsAffine V] (h : U ⟶ V)
    [h.IsOver (Spec (.of ℂ))] [Etale h] :
    IsLocalHomeomorph (mapFun (K := ℂ) h) := by
  classical
  set A := Γ(V, ⊤)
  set B := Γ(U, ⊤)
  letI : Algebra A B := h.appTop.hom.toAlgebra
  letI : Algebra ℂ B := (structureRingHom ℂ U).toAlgebra
  letI : Algebra ℂ A := (structureRingHom ℂ V).toAlgebra
  have hEt : RingHom.Etale h.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp ‹_›
  haveI : Algebra.Etale A B := hEt
  have halg : ∀ a : A, algebraMap A B a = h.appTop.hom a := fun _ => rfl
  rw [isLocalHomeomorph_iff_isOpenEmbedding_restrict]
  intro x
  -- the prime of `B` at `x` and a standard étale neighbourhood
  let Q : Ideal B := RingHom.ker (evalTopRingHom (K := ℂ) x)
  haveI : Q.IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hfQ, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  have hfx : evalTop x f ≠ 0 := fun h0 => hfQ (RingHom.mem_ker.mpr h0)
  let Pr : StandardEtalePresentation A (Localization.Away f) :=
    hstd.nonempty_standardEtalePresentation.some
  let P := Pr.P
  let eqv : Localization.Away f ≃ₐ[A] P.Ring := Pr.equivRing
  set NV := nonvanishingLocus ℂ (X := U) f
  -- the ring map `P.Ring → ℂ` at a point of `NV`
  let χ : NV → P.Ring →+* ℂ := fun q =>
    (awayEval q).comp (eqv.symm : P.Ring →+* Localization.Away f)
  have hχA : ∀ q a, χ q (algebraMap A P.Ring a) = evalTop (mapFun h q.1) a := by
    intro q a
    simp only [χ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.commutes]
    rw [IsScalarTower.algebraMap_apply A B (Localization.Away f), awayEval_algebraMap, halg,
      GenericCovering.evalTop_appTop]
  have hχX : ∀ q, χ q P.X = awayEval q Pr.x := fun q => by
    simp only [χ, RingHom.comp_apply, RingHom.coe_coe]
    congr 1
    exact Pr.equivRing_symm_X
  have hχeqv : ∀ q r, χ q (eqv r) = awayEval q r := fun q r => by
    simp only [χ, RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply]
  have hχcomp : ∀ q, (χ q).comp (algebraMap A P.Ring) = evalTopRingHom (mapFun h q.1) :=
    fun q => RingHom.ext fun a => hχA q a
  -- the coordinate `τ = x_P` on `NV`
  let τ : UnderlyingSpace ℂ U → ℂ := fun q => if hq : q ∈ NV then χ ⟨q, hq⟩ P.X else 0
  have hNV : IsOpen NV := isOpen_nonvanishingLocus f
  have hτ : ContinuousOn τ NV := by
    rw [continuousOn_iff_continuous_restrict]
    have : NV.domRestrict τ = fun q : NV => awayEval q Pr.x := funext fun q => by
      change τ q.1 = _
      rw [show τ q.1 = χ q P.X from dif_pos q.2]
      exact hχX q
    rw [this]
    exact continuous_awayEval_apply _
  -- the coefficients of `f_P` as coordinates on `V(ℂ)`
  set d := P.f.natDegree
  let z : UnderlyingSpace ℂ V → (Fin (d + 1) → ℂ) := fun w i => evalTop w (P.f.coeff i)
  have hz : Continuous z := continuous_pi fun i => continuous_evalTop_apply _
  let Ft : (Fin (d + 1) → ℂ) × ℂ → ℂ := fun v => ∑ i : Fin (d + 1), v.1 i * v.2 ^ (i : ℕ)
  have hFt : ∀ w t, Ft (z w, t) = (P.f.map (evalTopRingHom w)).eval t := by
    intro w t
    rw [eval_eq_sum_range' (n := d + 1) (natDegree_map_le.trans_lt (Nat.lt_succ_self _))]
    simp only [Ft, z, coeff_map]
    exact (Fin.sum_univ_eq_sum_range (fun i => evalTop w (P.f.coeff i) * t ^ i) (d + 1))
  have hFtc : ContDiff ℂ 1 Ft := by
    simp only [Ft]
    fun_prop
  -- the base point
  let x₀ : NV := ⟨x, hfx⟩
  set y := mapFun h x
  set t₀ := χ x₀ P.X
  let u : (Fin (d + 1) → ℂ) × ℂ := (z y, t₀)
  have hFu : Ft u = 0 := by
    change Ft (z y, t₀) = 0
    rw [hFt, ← hχcomp x₀, ← ringHom_aeval_X, P.hasMap_X.1, map_zero]
  have hderiv : HasDerivAt (fun t => Ft (u.1, t))
      ((P.f.map (evalTopRingHom y)).derivative.eval t₀) u.2 := by
    have : (fun t => Ft (u.1, t)) = fun t => (P.f.map (evalTopRingHom y)).eval t :=
      funext fun t => hFt y t
    rw [this]
    exact Polynomial.hasDerivAt _ _
  have hc0 : (P.f.map (evalTopRingHom y)).derivative.eval t₀ ≠ 0 := by
    rw [Polynomial.derivative_map, ← hχcomp x₀, ← ringHom_aeval_X]
    exact ((P.hasMap_X.isUnit_derivative_f).map (χ x₀)).ne_zero
  have cdf : ContDiffAt ℂ 1 Ft u := hFtc.contDiffAt
  have hd : HasDerivAt (fun t ↦ Ft (u.1, t)) (fderiv ℂ Ft u (0, 1)) u.2 := by
    have h1 : HasDerivAt (fun t : ℂ ↦ (u.1, t)) ((0 : Fin (d + 1) → ℂ), (1 : ℂ)) u.2 :=
      (hasDerivAt_const u.2 u.1).prodMk (hasDerivAt_id u.2)
    have h2 : HasFDerivAt Ft (fderiv ℂ Ft u) (u.1, u.2) :=
      (hFtc.differentiable one_ne_zero u).hasFDerivAt
    exact h2.comp_hasDerivAt u.2 h1
  have hcd := hderiv.unique hd
  have if₂ : (fderiv ℂ Ft u ∘L .inr ℂ (Fin (d + 1) → ℂ) ℂ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hc0),
      ContinuousLinearMap.ext_ring ?_⟩
    simp [ContinuousLinearEquiv.unitsEquivAut_apply, ← hcd, Polynomial.derivative_map]
  set ψ := cdf.implicitFunction one_ne_zero if₂
  have hψ0 : ψ u.1 = u.2 := cdf.implicitFunction_apply_self _ _
  obtain ⟨W₁, hW₁, hW₁o, huW₁⟩ := eventually_nhds_iff.mp
    ((cdf.eventually_apply_implicitFunction one_ne_zero if₂).and
      ((cdf.contDiffAt_implicitFunction one_ne_zero if₂).eventually (by simp)))
  obtain ⟨W₂, hW₂, hW₂o, huW₂⟩ := eventually_nhds_iff.mp
    (cdf.eventually_apply_eq_iff_implicitFunction one_ne_zero if₂)
  -- the open set `O ⊆ V(ℂ)` over which the root `ψ ∘ z` is defined
  let O₁ := z ⁻¹' W₁
  have hO₁ : IsOpen O₁ := hW₁o.preimage hz
  have hψz : ContinuousOn (fun w => ψ (z w)) O₁ := fun w hw =>
    ((hW₁ _ hw).2.continuousAt.comp hz.continuousAt).continuousWithinAt
  let Gt : UnderlyingSpace ℂ V → ℂ := fun w => (P.g.map (evalTopRingHom w)).eval (ψ (z w))
  have hGt : ContinuousOn Gt O₁ :=
    continuousOn_eval_map evalTopRingHom continuous_evalTop_apply hψz P.g
  let O := O₁ ∩ Gt ⁻¹' {0}ᶜ
  have hO : IsOpen O := hGt.isOpen_inter_preimage hO₁ isOpen_compl_singleton
  have hroot : ∀ w ∈ O, (P.f.map (evalTopRingHom w)).eval (ψ (z w)) = 0 ∧
      (P.g.map (evalTopRingHom w)).eval (ψ (z w)) ≠ 0 := fun w hw =>
    ⟨by rw [← hFt, (hW₁ _ hw.1).1, hFu], hw.2⟩
  -- the section `s : O → U(ℂ)`
  let ρ : ∀ w ∈ O, P.Ring →+* ℂ := fun w hw => pairLift P (evalTopRingHom w) (ψ (z w)) (hroot w hw)
  let ψB : ∀ w ∈ O, B →+* ℂ := fun w hw =>
    ((ρ w hw).comp (eqv : Localization.Away f →+* P.Ring)).comp (algebraMap B (Localization.Away f))
  have hψBA : ∀ w hw a, ψB w hw (h.appTop.hom a) = evalTop w a := by
    intro w hw a
    simp only [ψB, RingHom.comp_apply, RingHom.coe_coe]
    rw [← halg, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
    exact pairLift_algebraMap _ _ _ _ a
  have hψB : ∀ w hw c, ψB w hw (structureRingHom ℂ U c) = c := by
    intro w hw c
    rw [GenericCovering.structureRingHom_eq_appTop h, hψBA w hw, evalTop_structureRingHom]
  let s : UnderlyingSpace ℂ V → UnderlyingSpace ℂ U := fun w =>
    if hw : w ∈ O then ofRingHom (ψB w hw) (hψB w hw) else x
  have hsval : ∀ w (hw : w ∈ O) b, evalTop (s w) b = ψB w hw b := fun w hw b => by
    simp only [s, dif_pos hw, evalTop_ofRingHom]
  have hfs : ∀ w ∈ O, mapFun h (s w) = w := by
    intro w hw
    refine eq_of_forall_evalTop_eq fun a => ?_
    rw [← GenericCovering.evalTop_appTop, hsval w hw, hψBA w hw]
  -- the open set `N ⊆ U(ℂ)`
  let Φ : UnderlyingSpace ℂ U → (Fin (d + 1) → ℂ) × ℂ := fun q => (z (mapFun h q), τ q)
  have hΦ : ContinuousOn Φ NV :=
    ((hz.comp (continuous_mapFun h)).continuousOn).prodMk hτ
  let N := (NV ∩ mapFun h ⁻¹' O) ∩ Φ ⁻¹' W₂
  have hN : IsOpen N :=
    (hΦ.mono Set.inter_subset_left).isOpen_inter_preimage
      (hNV.inter (hO.preimage (continuous_mapFun h))) hW₂o
  have hτx : τ x = t₀ := dif_pos hfx
  have hyO : y ∈ O := by
    refine ⟨huW₁, ?_⟩
    change (P.g.map (evalTopRingHom y)).eval (ψ (z y)) ≠ 0
    rw [show z y = u.1 from rfl, hψ0, ← hχcomp x₀, ← ringHom_aeval_X]
    exact (P.hasMap_X.2.map (χ x₀)).ne_zero
  have hxN : x ∈ N := ⟨⟨hfx, hyO⟩, by simpa [Φ, hτx] using huW₂⟩
  have hsf : ∀ e ∈ N, mapFun h e ∈ O ∧ s (mapFun h e) = e := by
    rintro e ⟨⟨heNV, heO⟩, heW⟩
    refine ⟨heO, ?_⟩
    let e₀ : NV := ⟨e, heNV⟩
    have hτe : τ e = χ e₀ P.X := dif_pos heNV
    have hFe : Ft (Φ e) = Ft u := by
      rw [hFu]
      change Ft (z (mapFun h e), τ e) = 0
      rw [hFt, hτe, ← hχcomp e₀, ← ringHom_aeval_X, P.hasMap_X.1, map_zero]
    have hψe : ψ (z (mapFun h e)) = τ e := ((hW₂ _ heW).mp hFe)
    have hρ : ρ (mapFun h e) heO = χ e₀ := by
      refine ringHom_ext_pair P (RingHom.ext fun a => ?_) ?_
      · simp only [RingHom.comp_apply, ρ]
        rw [pairLift_algebraMap, hχA]
        rfl
      · simp only [ρ]
        rw [pairLift_X, hψe, hτe]
    refine eq_of_forall_evalTop_eq fun b => ?_
    rw [hsval _ heO]
    simp only [ψB, RingHom.comp_apply, RingHom.coe_coe, hρ, hχeqv]
    exact awayEval_algebraMap e₀ b
  have hs : ContinuousOn s O := by
    rw [isInducing_evalTop.continuousOn_iff, continuousOn_pi]
    intro b
    rw [continuousOn_iff_continuous_restrict]
    have : O.domRestrict (fun w => (evalTop ∘ s) w b) =
        fun w : O => ρ w.1 w.2 (eqv (algebraMap B (Localization.Away f) b)) := funext fun w => by
      change evalTop (s w.1) b = _
      rw [hsval w.1 w.2]
      rfl
    rw [this]
    refine continuous_pairRingHom_apply P (fun w : O => ρ w.1 w.2) (fun a => ?_) ?_ (fun w => ?_) _
    · simp only [ρ, pairLift_algebraMap]
      exact (continuous_evalTop_apply a).comp continuous_subtype_val
    · simp only [ρ, pairLift_X]
      exact (continuousOn_iff_continuous_restrict.mp (hψz.mono fun w hw => hw.1))
    · rw [ringHom_aeval_X]
      have h1 : (ρ w.1 w.2).comp (algebraMap A P.Ring) = evalTopRingHom w.1 :=
        RingHom.ext fun a => pairLift_algebraMap _ _ _ (hroot w.1 w.2) a
      rw [h1]
      simp only [ρ, pairLift_X]
      exact (hroot w.1 w.2).2
  exact ⟨N, hN.mem_nhds hxN,
    isOpenEmbedding_restrict_of_section (continuous_mapFun h) hN hO hs hfs hsf⟩

/-- An étale morphism of schemes over `ℂ` induces a local homeomorphism on `ℂ`-points. -/
private theorem isLocalHomeomorph_mapFun_of_etale {X Y : Scheme.{0}}
    [X.Over (Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))] (φ : X ⟶ Y) [φ.IsOver (Spec (.of ℂ))]
    [Etale φ] : IsLocalHomeomorph (mapFun (K := ℂ) φ) := by
  rw [isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
  intro p _
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := φ (p.toHom (IsLocalRing.closedPoint ℂ))) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (x := p.toHom (IsLocalRing.closedPoint ℂ)) (U := φ ⁻¹ᵁ V) hxV
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ X ↘ Spec (.of ℂ)⟩
  letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ Y ↘ Spec (.of ℂ)⟩
  haveI : U.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : V.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsAffine U := hU
  haveI : IsAffine V := hV
  let h : U.toScheme ⟶ V.toScheme := φ.resLE V U hUV
  have hι : h ≫ V.ι = U.ι ≫ φ := Scheme.Hom.resLE_comp_ι _ _
  haveI : Etale (h ≫ V.ι) := by rw [hι]; infer_instance
  haveI : Etale h := Etale.of_comp h V.ι
  haveI : h.IsOver (Spec (.of ℂ)) := ⟨by
    change h ≫ V.ι ≫ Y ↘ Spec (.of ℂ) = U.ι ≫ X ↘ Spec (.of ℂ)
    rw [← Category.assoc, hι, Category.assoc, comp_over]⟩
  have hcomm : mapFun (K := ℂ) φ ∘ mapFun (K := ℂ) U.ι =
      mapFun (K := ℂ) V.ι ∘ mapFun (K := ℂ) h := by
    funext q
    refine UnderlyingSpace.ext ?_
    simp only [Function.comp_apply, toHom_mapFun, Category.assoc, hι]
  have hUo : IsOpenEmbedding (mapFun (K := ℂ) U.ι) := isOpenEmbedding_map_of_isOpenImmersion U.ι
  have hVo : IsOpenEmbedding (mapFun (K := ℂ) V.ι) := isOpenEmbedding_map_of_isOpenImmersion V.ι
  have h1 : IsLocalHomeomorph (mapFun (K := ℂ) φ ∘ mapFun (K := ℂ) U.ι) := by
    rw [hcomm]
    exact hVo.isLocalHomeomorph.comp (isLocalHomeomorph_mapFun_of_etale_of_isAffine h)
  have h2 := (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp h1).of_comp_right
    (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hUo.isLocalHomeomorph)
  have hp : p ∈ Set.range (mapFun (K := ℂ) U.ι) := by
    rw [range_mapFun_of_isOpenImmersion, Scheme.Opens.opensRange_ι]
    exact (top_le_preimage_iff p U).mpr hxU
  obtain ⟨q, rfl⟩ := hp
  exact h2 _ ⟨q, trivial, rfl⟩

/-- **Finite étale maps are finite coverings on `ℂ`-points.** For a finite étale morphism
`φ : T' ⟶ T` of schemes over `ℂ`, with `T` separated and locally of finite type over `ℂ`, the
realization `T'^an ⟶ T^an` is a covering map with finite fibres: it is a local homeomorphism
(étale), proper (finite) and has discrete compact, hence finite, fibres. -/
private theorem isCoveringMap_analyticMap_of_isFinite_of_etale {T T' : Scheme.{0}}
    (sT : T ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sT] [IsSeparated sT]
    (φ : T' ⟶ T) [IsFinite φ] [Etale φ] :
    IsCoveringMap (analyticMap φ (sY := sT) rfl) ∧
      ∀ y, (analyticMap φ (sY := sT) rfl ⁻¹' {y}).Finite := by
  letI : T.Over (Spec (.of ℂ)) := ⟨sT⟩
  letI : T'.Over (Spec (.of ℂ)) := ⟨φ ≫ sT⟩
  haveI : φ.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : LocallyOfFiniteType (T ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sT›
  haveI : IsSeparated (T' ↘ Spec (.of ℂ)) := inferInstanceAs (IsSeparated (φ ≫ sT))
  haveI : T2Space (UnderlyingSpace ℂ T') := t2Space_of_isSeparated T'
  let eT := homeomorphUnderlyingSpace (X := T)
  let eT' := homeomorphUnderlyingSpace (X := T')
  have hfun : (analyticMap φ (sY := sT) rfl : analyticSpace (φ ≫ sT) → analyticSpace sT) =
      eT.symm ∘ mapFun (K := ℂ) φ ∘ eT' := by
    funext x
    apply eT.injective
    refine UnderlyingSpace.ext ?_
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    rfl
  have hloc : IsLocalHomeomorph (eT.symm ∘ mapFun (K := ℂ) φ ∘ eT') :=
    eT.symm.isLocalHomeomorph.comp
      ((isLocalHomeomorph_mapFun_of_etale φ).comp eT'.isLocalHomeomorph)
  have hφp : IsProperMap (mapFun (K := ℂ) φ) := isProperMap_map (K := ℂ) φ
  have hprop : IsProperMap (eT.symm ∘ mapFun (K := ℂ) φ ∘ eT') :=
    eT.symm.isProperMap.comp (hφp.comp eT'.isProperMap)
  haveI : T2Space (ComplexPoints (T' ↘ Spec (.of ℂ))) := eT'.isEmbedding.t2Space
  rw [hfun]
  have hfin : ∀ y, ((eT.symm ∘ mapFun (K := ℂ) φ ∘ eT') ⁻¹' {y}).Finite := fun y =>
    (hprop.isCompact_preimage isCompact_singleton).finite
      (((isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hloc).mono
        (Set.subset_univ _)).isDiscrete_of_image
        ((Set.subsingleton_singleton.anti (Set.image_preimage_subset _ _)).isDiscrete))
  refine ⟨isCoveringMap_iff_isCoveringMapOn_univ.mpr ?_, hfin⟩
  refine hprop.isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (fun y _ => hfin y) ?_
  exact isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mp hloc

/-- **The complex realization of an integral scheme of finite type over `ℂ` is connected.**
Its regular points form a connected subset of `X(ℂ)`, dense for the classical topology. -/
private theorem connectedSpace_analyticSpace {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
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

/-- The structure morphism of a Zariski-open `T°` of the curve `T` of a local setting is locally of
finite type, quasi-compact and separated. -/
private theorem curveOpen_structure {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (Θ : QDivisor Y) (T : IrreducibleCloseds Y)
    (π : Yt ⟶ Y) (hS : IsLocalSetting sY Θ T π) (To : (curveScheme T).Opens) :
    LocallyOfFiniteType (To.ι ≫ curveι T ≫ sY) ∧ QuasiCompact (To.ι ≫ curveι T ≫ sY) ∧
      IsSeparated (To.ι ≫ curveι T ≫ sY) := by
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsLocallyNoetherian (curveScheme T) :=
    LocallyOfFiniteType.isLocallyNoetherian (curveι T ≫ sY)
  haveI : CompactSpace (curveScheme T) :=
    QuasiCompact.compactSpace_of_compactSpace (curveι T ≫ sY)
  haveI : IsNoetherian (curveScheme T) := ⟨⟩
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **The cover `φ : T' ⟶ T°` is a finite covering on complex points.** In a local setting, the
realization `T'^an ⟶ T°^an` of a finite étale `φ : T' ⟶ T°` is a covering map with finite
fibres. -/
private theorem isCoveringMap_analyticMap_cover {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (Θ : QDivisor Y)
    (T : IrreducibleCloseds Y) (π : Yt ⟶ Y) (hS : IsLocalSetting sY Θ T π)
    (To : (curveScheme T).Opens) {T' : Scheme.{0}} (φ : T' ⟶ (To : Scheme.{0})) [IsFinite φ]
    [Etale φ] :
    IsCoveringMap (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl) ∧
      ∀ y, (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl ⁻¹' {y}).Finite := by
  obtain ⟨h₁, -, h₃⟩ := curveOpen_structure sY Θ T π hS To
  exact isCoveringMap_analyticMap_of_isFinite_of_etale _ φ

/-- **The connected cover `T'` has connected complex realization.** In a local setting, for a
finite étale `φ : T' ⟶ T°` onto an adapted open `T°`, with `T'` connected: `T'` is smooth over
`ℂ`, hence integral, so `T'^an` is connected. -/
private theorem connectedSpace_analyticSpace_cover {Y Yt : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of ℂ)) (Θ : QDivisor Y)
    (T : IrreducibleCloseds Y) (π : Yt ⟶ Y) (hS : IsLocalSetting sY Θ T π)
    (To : (curveScheme T).Opens) (hTo : IsAdaptedOpen sY π To) {T' : Scheme.{0}}
    (φ : T' ⟶ (To : Scheme.{0})) [IsFinite φ] [Etale φ] [ConnectedSpace T'] :
    ConnectedSpace (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY)) := by
  obtain ⟨-, h₂, -⟩ := curveOpen_structure sY Θ T π hS To
  haveI : Smooth (To.ι ≫ curveι T ≫ sY) := hTo.smooth
  haveI : Smooth (φ ≫ To.ι ≫ curveι T ≫ sY) := inferInstance
  haveI : IsIntegral T' := Stacks.Chow.isIntegral_of_connectedSpace_of_smooth
    (φ ≫ To.ι ≫ curveι T ≫ sY)
  exact connectedSpace_analyticSpace _

end AnalyticInputs

/-! ### Covering spaces: path connectedness and monodromy permutations -/

section CoveringInputs

/-- **Monodromy permutations.** For a covering map `p : E → Z` and a loop `γ` at `t`, lifting `γ`
defines a permutation `σ` of the fibre `p⁻¹{t}`: for every `e` there is a lift of `γ` from `e` to
`σ e`. -/
private theorem exists_perm_lift {E Z : Type*} [TopologicalSpace E] [TopologicalSpace Z]
    {p : E → Z} (cov : IsCoveringMap p) {t : Z} (γ : Path t t) :
    ∃ σ : (p ⁻¹' {t}) ≃ (p ⁻¹' {t}), ∀ e, ∃ Γ' : C(unitInterval, E),
      (∀ x, p (Γ' x) = γ x) ∧ Γ' 0 = e.1 ∧ Γ' 1 = (σ e).1 :=
  ⟨cov.monodromyPerm t (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)), fun e =>
    ⟨cov.liftPath γ.toContinuousMap e.1 (γ.source.trans e.2.symm), fun x =>
      congrFun (cov.liftPath_lifts γ.toContinuousMap e.1 _) x, cov.liftPath_zero _ _ _, rfl⟩⟩

/-- The complex realization of a scheme locally of finite type over `ℂ` is locally path
connected: its points have bases of contractible open neighbourhoods. -/
private theorem locallyPathConnectedSpace_analyticSpace {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] :
    LocallyPathConnectedSpace (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  have hb := MMP.UnderlyingSpace.hasOpenContractibleBasis X
  haveI : LocallyPathConnectedSpace (MMP.UnderlyingSpace ℂ X) :=
    LocallyPathConnectedSpace.of_bases hb fun x V hV => by
      show IsPathConnected V
      haveI : ContractibleSpace V := hV.2.2
      exact isPathConnected_iff_pathConnectedSpace.2 inferInstance
  exact (homeomorphUnderlyingSpace (X := X)).isOpenEmbedding.locallyPathConnectedSpace

end CoveringInputs

/-! ### Deformation of tubes onto proper fibres -/

section TubeDeformation

open unitInterval

/-- An open subspace of a space with bases of open contractible neighbourhoods has such bases. -/
private theorem hasOpenContractibleBasis_of_isOpenEmbedding {T Y : Type*} [TopologicalSpace T]
    [TopologicalSpace Y] {j : T → Y} (hj : IsOpenEmbedding j)
    (hY : MMP.HasOpenContractibleBasis Y) :
    MMP.HasOpenContractibleBasis T := by
  intro t
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨V, ⟨hVo, htV, _⟩, hVs⟩ ↦
    Filter.mem_of_superset (hVo.mem_nhds htV) hVs⟩⟩
  have hs' : j '' s ∈ 𝓝 (j t) := by
    rw [← hj.map_nhds_eq]; exact Filter.image_mem_map hs
  obtain ⟨V, ⟨hVo, hjV, hVc⟩, hVs⟩ := (hY (j t)).mem_iff.1 hs'
  have hVr : V ⊆ Set.range j := hVs.trans (Set.image_subset_range _ _)
  refine ⟨j ⁻¹' V, ⟨hVo.preimage hj.continuous, hjV, ?_⟩, ?_⟩
  · have e : (j ⁻¹' V) ≃ₜ V :=
      ((hj.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict V
        (fun x ↦ x.2)).toHomeomorphOfSurjective (by
          rintro ⟨v, hv⟩
          obtain ⟨u, rfl⟩ := hVr hv
          exact ⟨⟨u, hv⟩, rfl⟩)
    haveI := hVc
    exact e.contractibleSpace
  · intro u hu
    obtain ⟨u', hu', he⟩ := hVs hu
    exact hj.injective he ▸ hu'

/-- **Deformation of a tube onto a fibre.** -/
private theorem exists_tube_deformation {Y B T : Type*} [TopologicalSpace Y] [TopologicalSpace B]
    [TopologicalSpace T] {p : Y → B} (hp : Continuous p) (hpc : IsClosedMap p) {b : B}
    (hb : IsClosed ({b} : Set B)) {j : T → Y} (hj : IsOpenEmbedding j)
    (hZj : p ⁻¹' {b} ⊆ Set.range j) {n : ℕ} {E : T → EuclideanSpace ℝ (Fin n)}
    (hE : IsClosedEmbedding E) (hY : MMP.HasOpenContractibleBasis Y)
    (hZ : MMP.HasOpenContractibleBasis (p ⁻¹' {b})) {V : Set B} (hV : IsOpen V)
    (hbV : b ∈ V) :
    ∃ W : Set B, IsOpen W ∧ b ∈ W ∧ W ⊆ V ∧ ∃ ρ : C(p ⁻¹' W, p ⁻¹' {b}),
      (∀ y : p ⁻¹' W, p y = b → (ρ y : Y) = y) ∧
      ∃ H : C(I × p ⁻¹' W, p ⁻¹' V), (∀ y, (H (0, y) : Y) = y) ∧
        ∀ y, (H (1, y) : Y) = ρ y := by
  set Z : Set Y := p ⁻¹' {b}
  set ZT : Set T := (p ∘ j) ⁻¹' {b} with hZT
  have hZTc : IsClosed ZT := hb.preimage (hp.comp hj.continuous)
  -- `ZT ≃ₜ Z`
  have eZ : ZT ≃ₜ Z :=
    ((hj.isEmbedding.comp IsEmbedding.subtypeVal).codRestrict Z
      (fun x ↦ x.2)).toHomeomorphOfSurjective (by
        rintro ⟨z, hz⟩
        obtain ⟨u, rfl⟩ := hZj hz
        exact ⟨⟨u, hz⟩, rfl⟩)
  have hZT : MMP.HasOpenContractibleBasis ZT := hZ.of_homeomorph eZ.symm
  have hT : MMP.HasOpenContractibleBasis T :=
    hasOpenContractibleBasis_of_isOpenEmbedding hj hY
  have hM : (p ∘ j) ⁻¹' V ∈ 𝓝ˢ ZT :=
    (hV.preimage (hp.comp hj.continuous)).mem_nhdsSet.2 fun t ht ↦ by
      have : p (j t) = b := ht
      change p (j t) ∈ V
      rw [this]; exact hbV
  obtain ⟨N, -, hZN, -, r, -, hrfix, G, -, hG0, hG1, -, hGM⟩ :=
    MMP.exists_isClosed_isProperMap_retraction_homotopy hE hZTc hZT hT hM
  set O : Set Y := j '' interior N with hOdef
  have hO : IsOpen O := hj.isOpenMap _ isOpen_interior
  have hZO : Z ⊆ O := fun z hz ↦ by
    obtain ⟨u, rfl⟩ := hZj hz
    exact ⟨u, hZN (show p (j u) = b from hz), rfl⟩
  refine ⟨V ∩ (p '' Oᶜ)ᶜ, hV.inter (hpc _ hO.isClosed_compl).isOpen_compl,
    ⟨hbV, ?_⟩, Set.inter_subset_left, ?_⟩
  · rintro ⟨y, hy, hyb⟩
    exact hy (hZO hyb)
  have hWO : ∀ y : p ⁻¹' (V ∩ (p '' Oᶜ)ᶜ), (y : Y) ∈ O := fun y ↦ by
    by_contra h
    exact y.2.2 ⟨y, h, rfl⟩
  have hrange : ∀ y : p ⁻¹' (V ∩ (p '' Oᶜ)ᶜ), (y : Y) ∈ Set.range j := fun y ↦ by
    obtain ⟨u, -, hu⟩ := hWO y
    exact ⟨u, hu⟩
  let e := hj.isEmbedding.toHomeomorph
  let sec : p ⁻¹' (V ∩ (p '' Oᶜ)ᶜ) → T := fun y ↦ e.symm ⟨y, hrange y⟩
  have hsecc : Continuous sec :=
    e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hjsec : ∀ y, j (sec y) = y := fun y ↦
    congrArg Subtype.val (e.apply_symm_apply ⟨y, hrange y⟩)
  have hsecN : ∀ y, sec y ∈ N := fun y ↦ by
    obtain ⟨u, hu, hju⟩ := hWO y
    have : sec y = u := hj.injective ((hjsec y).trans hju.symm)
    exact this ▸ interior_subset hu
  let secN : p ⁻¹' (V ∩ (p '' Oᶜ)ᶜ) → N := fun y ↦ ⟨sec y, hsecN y⟩
  have hsecNc : Continuous secN := hsecc.subtype_mk _
  have hrZ : ∀ x : N, p (j (r x)) = b := fun x ↦ (r x).2
  let ρ : C(p ⁻¹' (V ∩ (p '' Oᶜ)ᶜ), Z) :=
    ⟨fun y ↦ ⟨j (r (secN y)), hrZ _⟩,
      ((hj.continuous.comp continuous_subtype_val).comp (r.continuous.comp hsecNc)).subtype_mk _⟩
  refine ⟨ρ, fun y hy ↦ ?_, ?_⟩
  · change j (r (secN y)) = y
    have hsecZ : ((secN y : N) : T) ∈ ZT := by
      change p (j (sec y)) = b
      rw [hjsec]; exact hy
    rw [hrfix (secN y) hsecZ]
    exact hjsec y
  · have hGV : ∀ q : N × I, p (j (G q)) ∈ V := fun q ↦ hGM q
    refine ⟨⟨fun q ↦ ⟨j (G (secN q.2, q.1)), hGV _⟩, ?_⟩, fun y ↦ ?_, fun y ↦ ?_⟩
    · exact (hj.continuous.comp (G.continuous.comp
        ((hsecNc.comp continuous_snd).prodMk continuous_fst))).subtype_mk _
    · change j (G (secN y, 0)) = y
      rw [hG0]; exact hjsec y
    · change j (G (secN y, 1)) = j (r (secN y))
      rw [hG1]

end TubeDeformation

section RealizationInputs

/-- The underlying space of a compact scheme separated and locally of finite type over `ℂ` has
a closed imbedding in some `ℝᴺ`. -/
private theorem exists_isClosedEmbedding_euclideanSpace' (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [IsSeparated (X ↘ Spec (.of ℂ))]
    [CompactSpace X] :
    ∃ (N : ℕ) (F : UnderlyingSpace ℂ X → EuclideanSpace ℝ (Fin N)), IsClosedEmbedding F := by
  haveI : QuasiCompact (X ↘ Spec (.of ℂ)) := inferInstance
  haveI : T2Space (UnderlyingSpace ℂ X) := t2Space_of_isSeparated X
  have hV : ∀ x : X, ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V := fun x ↦ by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
    exact ⟨V, hV, hxV⟩
  choose V hVa hxV using hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (V x : Set X))
    (fun x ↦ (V x).2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxV x⟩)
  letI (x : X) : (V x).toScheme.Over (Spec (.of ℂ)) := ⟨(V x).ι ≫ X ↘ Spec (.of ℂ)⟩
  haveI (x : X) : (V x).ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI (x : X) : IsAffine (V x) := hVa x
  haveI (x : X) : LocallyOfFiniteType ((V x).toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType ((V x).ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  choose n m f φ using fun x : X ↦ exists_homeomorph_zeroLocus (V x)
  let U : t → Set (UnderlyingSpace ℂ X) := fun x ↦ Set.range (map (K := ℂ) (V x.1).ι)
  let g : ∀ x : t, U x → (Fin (n x.1) → ℂ) := fun x ↦
    Subtype.val ∘ (φ x.1).some ∘
      (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) (V x.1).ι).isEmbedding.toHomeomorph.symm
  have hg : ∀ x, IsClosedEmbedding (g x) := fun x ↦
    (isClosed_zeroLocus (f x.1)).isClosedEmbedding_subtypeVal.comp
      ((φ x.1).some.isClosedEmbedding.comp (Homeomorph.isClosedEmbedding _))
  have hcov : ⋃ x, U x = Set.univ := by
    refine Set.eq_univ_of_forall fun p ↦ ?_
    obtain ⟨x, hx, hpx⟩ :=
      Set.mem_iUnion₂.mp (ht (Set.mem_univ (p.toHom (IsLocalRing.closedPoint ℂ))))
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_range_map_ι (V x) p hpx⟩
  obtain ⟨F, hF⟩ := exists_isClosedEmbedding_of_finite_cover U
    (fun x ↦ (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) (V x.1).ι).isOpen_range) hcov g hg
  let T := (t → ℝ) × (∀ x : t, Fin (n x.1) → ℂ)
  let e : T ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ T)) :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin).symm
  exact ⟨_, e ∘ F, e.toHomeomorph.isClosedEmbedding.comp hF⟩

/-- A compact subset of the underlying space of a scheme separated and locally of finite type
over `ℂ` lies in the image of an open imbedding of a space with a closed imbedding in some
`ℝᴺ`: the underlying space of a quasi-compact open subscheme. -/
private theorem exists_isOpenEmbedding_of_isCompact (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] [IsSeparated (X ↘ Spec (.of ℂ))]
    {K : Set (UnderlyingSpace ℂ X)} (hK : IsCompact K) :
    ∃ (T : Type) (_ : TopologicalSpace T) (j : T → UnderlyingSpace ℂ X) (N : ℕ)
      (E : T → EuclideanSpace ℝ (Fin N)), IsOpenEmbedding j ∧ K ⊆ Set.range j ∧
        IsClosedEmbedding E := by
  have hV : ∀ p : UnderlyingSpace ℂ X, ∃ V : X.Opens, IsAffineOpen V ∧
      p.toHom (IsLocalRing.closedPoint ℂ) ∈ V := fun p ↦ by
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := p.toHom (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
    exact ⟨V, hV, hxV⟩
  choose V hVa hpV using hV
  have hopen : ∀ p : UnderlyingSpace ℂ X, IsOpen {q : UnderlyingSpace ℂ X |
      q.toHom (IsLocalRing.closedPoint ℂ) ∈ V p} := fun p ↦ by
    letI : (V p).toScheme.Over (Spec (.of ℂ)) := ⟨(V p).ι ≫ X ↘ Spec (.of ℂ)⟩
    haveI : (V p).ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
    convert (isOpenEmbedding_map_of_isOpenImmersion (K := ℂ) (V p).ι).isOpen_range using 1
    ext q
    refine ⟨fun hq ↦ mem_range_map_ι (V p) q hq, ?_⟩
    rintro ⟨r, rfl⟩
    change (V p).ι (r.toHom (IsLocalRing.closedPoint ℂ)) ∈ V p
    exact (Scheme.Opens.ι_apply (V p) _).symm ▸ Subtype.prop _
  obtain ⟨s, hsK, hs⟩ := hK.elim_nhds_subcover (fun p ↦ {q : UnderlyingSpace ℂ X |
      q.toHom (IsLocalRing.closedPoint ℂ) ∈ V p}) (fun p _ ↦ (hopen p).mem_nhds (hpV p))
  let U : X.Opens := ⨆ p ∈ s, V p
  have hUc : IsCompact (U : Set X) := by
    have : (U : Set X) = ⋃ p ∈ s, (V p : Set X) := by simp [U]
    rw [this]
    exact s.isCompact_biUnion fun p _ ↦ (hVa p).isCompact
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ X ↘ Spec (.of ℂ)⟩
  haveI : U.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : LocallyOfFiniteType (U.toScheme ↘ Spec (.of ℂ)) := by
    change LocallyOfFiniteType (U.ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  haveI : IsSeparated (U.toScheme ↘ Spec (.of ℂ)) := by
    change IsSeparated (U.ι ≫ X ↘ Spec (.of ℂ))
    infer_instance
  obtain ⟨N, E, hE⟩ := exists_isClosedEmbedding_euclideanSpace' U
  refine ⟨UnderlyingSpace ℂ U, inferInstance, map (K := ℂ) U.ι, N, E,
    isOpenEmbedding_map_of_isOpenImmersion _, fun q hq ↦ ?_, hE⟩
  obtain ⟨p, hp, hqp⟩ := Set.mem_iUnion₂.mp (hs hq)
  refine mem_range_map_ι U q ?_
  have : V p ≤ U := le_iSup₂_of_le p hp le_rfl
  exact this hqp

/-- The realization of a morphism of schemes over `ℂ`, read on Fulton's underlying spaces. -/
private theorem analyticMap_eq_mapFun {X Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (g : X ⟶ Y) :
    letI : X.Over (Spec (.of ℂ)) := ⟨g ≫ sY⟩
    letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
    haveI : g.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
    ((analyticMap g (sY := sY) rfl : analyticSpace (g ≫ sY) → analyticSpace sY)) =
      (homeomorphUnderlyingSpace (X := Y)).symm ∘ mapFun (K := ℂ) g ∘
        homeomorphUnderlyingSpace (X := X) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨g ≫ sY⟩
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : g.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  funext x
  apply (homeomorphUnderlyingSpace (X := Y)).injective
  refine UnderlyingSpace.ext ?_
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  rfl

/-- The realization of a proper morphism to a scheme locally of finite type over `ℂ` is
proper. -/
private theorem isProperMap_analyticMap {X B : Scheme.{0}} (f : X ⟶ B) (sB : B ⟶ Spec (.of ℂ))
    [IsProper f] [LocallyOfFiniteType sB] :
    IsProperMap (analyticMap f (sY := sB) rfl) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨f ≫ sB⟩
  letI : B.Over (Spec (.of ℂ)) := ⟨sB⟩
  haveI : f.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : LocallyOfFiniteType (B ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sB›
  have h := (homeomorphUnderlyingSpace (X := B)).symm.isProperMap.comp
    ((isProperMap_map (K := ℂ) f).comp (homeomorphUnderlyingSpace (X := X)).isProperMap)
  rw [analyticMap_eq_mapFun sB f]
  exact h

private theorem t2Space_analyticSpace {B : Scheme.{0}} (sB : B ⟶ Spec (.of ℂ)) [IsSeparated sB] :
    T2Space (analyticSpace sB) := by
  letI : B.Over (Spec (.of ℂ)) := ⟨sB⟩
  haveI : IsSeparated (B ↘ Spec (.of ℂ)) := ‹IsSeparated sB›
  haveI := t2Space_of_isSeparated (K := ℂ) B
  exact (homeomorphUnderlyingSpace (X := B)).isEmbedding.t2Space

private theorem hasOpenContractibleBasis_analyticSpace {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] : HasOpenContractibleBasis (analyticSpace sX) := by
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
  exact (UnderlyingSpace.hasOpenContractibleBasis X).of_homeomorph
    (homeomorphUnderlyingSpace (X := X)).symm

end RealizationInputs

/-! ### Change of coefficients and the fibre comparison -/

section FibreComparison

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

private theorem fibreIncl_w {X B Fb : Scheme.{0}} (f : X ⟶ B) (sB : B ⟶ Spec (.of ℂ))
    (b : ComplexPoints sB) (i : Fb ⟶ X) (sF : Fb ⟶ Spec (.of ℂ)) (hi : i ≫ f = sF ≫ b.hom) :
    i ≫ f ≫ sB = sF := by
  rw [← Category.assoc, hi, Category.assoc, b.hom_comp_structure, Category.comp_id]

private theorem fibreIncl_mem {X B Fb : Scheme.{0}} (f : X ⟶ B) (sB : B ⟶ Spec (.of ℂ))
    (b : ComplexPoints sB) (i : Fb ⟶ X) (sF : Fb ⟶ Spec (.of ℂ)) (hi : i ≫ f = sF ≫ b.hom)
    (x : analyticSpace sF) :
    analyticMap f (sY := sB) rfl (analyticMap i (fibreIncl_w f sB b i sF hi) x) = b := by
  ext1
  change (x.hom ≫ i) ≫ f = b.hom
  rw [Category.assoc, hi, ← Category.assoc, x.hom_comp_structure, Category.id_comp]

/-- The inclusion `F_b(ℂ) ⟶ f⁻¹(V)` of the realization of a scheme `F_b` over `b`, for `b ∈ V`. -/
private def fibreIncl {X B Fb : Scheme.{0}} (f : X ⟶ B) (sB : B ⟶ Spec (.of ℂ))
    (b : ComplexPoints sB) (i : Fb ⟶ X) (sF : Fb ⟶ Spec (.of ℂ)) (hi : i ≫ f = sF ≫ b.hom)
    {V : Opens (analyticSpace sB)} (hV : b ∈ V) :
    analyticSpace sF ⟶ preimageSpace (analyticMap f (sY := sB) rfl) V :=
  TopCat.ofHom ⟨fun x ↦ ⟨analyticMap i (fibreIncl_w f sB b i sF hi) x, by
      rw [Set.mem_preimage, fibreIncl_mem f sB b i sF hi x]
      exact hV⟩,
    ((analyticMap i (fibreIncl_w f sB b i sF hi)).hom.continuous).subtype_mk _⟩

/-- The realization of the fibre `F_b ⟶ X` of `f` over a `ℂ`-point `b` is a topological
imbedding onto `f^an⁻¹(b)`. -/
private theorem isEmbedding_analyticMap_fibre {X B Fb : Scheme.{0}} (f : X ⟶ B)
    (sB : B ⟶ Spec (.of ℂ))
    (b : ComplexPoints sB) (i : Fb ⟶ X) (sF : Fb ⟶ Spec (.of ℂ)) (H : IsPullback i sF f b.hom) :
    IsEmbedding (analyticMap i (fibreIncl_w f sB b i sF H.w)) ∧
      Set.range (analyticMap i (fibreIncl_w f sB b i sF H.w)) =
        analyticMap f (sY := sB) rfl ⁻¹' {b} := by
  letI : X.Over (Spec (.of ℂ)) := ⟨f ≫ sB⟩
  letI : Fb.Over (Spec (.of ℂ)) := ⟨sF⟩
  letI : (Spec (.of ℂ)).Over (Spec (.of ℂ)) := ⟨𝟙 _⟩
  haveI : i.IsOver (Spec (.of ℂ)) := ⟨fibreIncl_w f sB b i sF H.w⟩
  haveI : sF.IsOver (Spec (.of ℂ)) := ⟨Category.comp_id _⟩
  haveI : Unique (UnderlyingSpace ℂ (Spec (.of ℂ))) :=
    { default := ⟨𝟙 _, Category.comp_id _⟩
      uniq := fun a ↦ UnderlyingSpace.ext ((Category.comp_id _).symm.trans a.toHom_comp_over) }
  have hP := isEmbedding_prodMap_of_isPullback (K := ℂ) H
  have hi : IsEmbedding (mapFun (K := ℂ) i) :=
    (Homeomorph.prodUnique _ _).isEmbedding.comp hP
  have e : (analyticMap i (fibreIncl_w f sB b i sF H.w) : analyticSpace sF → analyticSpace (f ≫ sB))
      = (homeomorphUnderlyingSpace (X := X)).symm ∘ mapFun (K := ℂ) i ∘
        homeomorphUnderlyingSpace (X := Fb) := by
    funext x
    apply (homeomorphUnderlyingSpace (X := X)).injective
    refine UnderlyingSpace.ext ?_
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    rfl
  refine ⟨?_, ?_⟩
  · rw [e]
    exact (homeomorphUnderlyingSpace (X := X)).symm.isEmbedding.comp
      (hi.comp (homeomorphUnderlyingSpace (X := Fb)).isEmbedding)
  · ext x
    refine ⟨?_, fun hx ↦ ?_⟩
    · rintro ⟨y, rfl⟩
      exact fibreIncl_mem f sB b i sF H.w y
    · have hx' : x.hom ≫ f = (𝟙 _) ≫ b.hom := by
        rw [Category.id_comp]
        exact congrArg ComplexPoints.hom hx
      refine ⟨⟨H.lift x.hom (𝟙 _) hx', H.lift_snd _ _ _⟩, ?_⟩
      ext1
      exact H.lift_fst _ _ _

/-- **The fibre comparison for proper morphisms.** Let `f : X ⟶ B` be a proper morphism of
schemes, with `B` separated and locally of finite type over `ℂ`, let `b ∈ B(ℂ)` and let `F_b` be
the fibre of `f` over `b`. Then the restriction maps `H^q(f^an⁻¹(V); ℚ) ⟶ H^q(F_b(ℂ); ℚ)`,
`V` running over the open neighbourhoods of `b` in `B(ℂ)`, induce a bijection from their colimit:
every class on `F_b(ℂ)` extends to some `f^an⁻¹(V)`, and a class on `f^an⁻¹(V)` vanishing on
`F_b(ℂ)` vanishes on `f^an⁻¹(W)` for some smaller neighbourhood `W` of `b`. -/
private theorem fibre_comparison {X B Fb : Scheme.{0}} (f : X ⟶ B) (sB : B ⟶ Spec (.of ℂ))
    [IsProper f] [LocallyOfFiniteType sB] [IsSeparated sB]
    (b : ComplexPoints sB) (i : Fb ⟶ X) (sF : Fb ⟶ Spec (.of ℂ)) (H : IsPullback i sF f b.hom)
    (q : ℕ) :
    (∀ x : rationalCohomology (analyticSpace sF) q,
      ∃ (V : Opens (analyticSpace sB)) (hV : b ∈ V)
        (α : rationalCohomology (preimageSpace (analyticMap f (sY := sB) rfl) V) q),
        (rationalCohomologyMap (fibreIncl f sB b i sF H.w hV) q).hom α = x) ∧
    (∀ (V : Opens (analyticSpace sB)) (hV : b ∈ V)
      (α : rationalCohomology (preimageSpace (analyticMap f (sY := sB) rfl) V) q),
      (rationalCohomologyMap (fibreIncl f sB b i sF H.w hV) q).hom α = 0 →
      ∃ (W : Opens (analyticSpace sB)) (hWV : W ≤ V), b ∈ W ∧
        (rationalCohomologyMap (preimageInclusion _ hWV) q).hom α = 0) := by
  set p := analyticMap f (sY := sB) rfl with hpdef
  obtain ⟨hemb, hrange⟩ := isEmbedding_analyticMap_fibre f sB b i sF H
  let ψ : analyticSpace sF ≃ₜ (p ⁻¹' {b}) :=
    hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hψ : ∀ y, ((ψ y : p ⁻¹' {b}) : analyticSpace (f ≫ sB)) =
      analyticMap i (fibreIncl_w f sB b i sF H.w) y := fun _ ↦ rfl
  have hprop := isProperMap_analyticMap f sB
  haveI := t2Space_analyticSpace sB
  haveI : LocallyOfFiniteType sF := MorphismProperty.of_isPullback H
    (inferInstance : LocallyOfFiniteType f)
  have hZ : HasOpenContractibleBasis (p ⁻¹' {b}) :=
    (hasOpenContractibleBasis_analyticSpace sF).of_homeomorph ψ
  have hY := hasOpenContractibleBasis_analyticSpace (f ≫ sB)
  letI : X.Over (Spec (.of ℂ)) := ⟨f ≫ sB⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := inferInstanceAs (LocallyOfFiniteType (f ≫ sB))
  haveI : IsSeparated (X ↘ Spec (.of ℂ)) := inferInstanceAs (IsSeparated (f ≫ sB))
  let hX := homeomorphUnderlyingSpace (X := X)
  obtain ⟨T, _, j, n, E, hj, hKj, hE⟩ := exists_isOpenEmbedding_of_isCompact X
    ((hprop.isCompact_preimage isCompact_singleton).image hX.continuous)
  have hj' : IsOpenEmbedding (hX.symm ∘ j) := hX.symm.isOpenEmbedding.comp hj
  have hKj' : p ⁻¹' {b} ⊆ Set.range (hX.symm ∘ j) := fun y hy ↦ by
    obtain ⟨t, ht⟩ := hKj ⟨y, hy, rfl⟩
    exact ⟨t, (congrArg hX.symm ht).trans (hX.symm_apply_apply y)⟩
  have tube := fun (V : Set (analyticSpace sB)) (hV : IsOpen V) (hbV : b ∈ V) ↦
    exists_tube_deformation (p := p) p.hom.continuous hprop.isClosedMap isClosed_singleton hj'
      hKj' hE hY hZ hV hbV
  -- the retraction, read on `F_b(ℂ)`
  have retr : ∀ {W : Set (analyticSpace sB)} (ρ : C(p ⁻¹' W, p ⁻¹' {b})),
      (∀ y : p ⁻¹' W, p y = b → (ρ y : analyticSpace (f ≫ sB)) = y) →
      ∀ (hWo : IsOpen W) (hbW : b ∈ W),
        fibreIncl f sB b i sF H.w (V := ⟨W, hWo⟩) hbW ≫
          TopCat.ofHom ⟨fun y ↦ ψ.symm (ρ y), ψ.symm.continuous.comp ρ.continuous⟩ = 𝟙 _ := by
    intro W ρ hρ hWo hbW
    refine TopCat.ext fun y ↦ ?_
    change ψ.symm (ρ _) = y
    rw [Homeomorph.symm_apply_eq]
    apply Subtype.ext
    rw [hρ _ (fibreIncl_mem f sB b i sF H.w y), hψ]
    rfl
  refine ⟨fun x ↦ ?_, fun V hV α hα ↦ ?_⟩
  · obtain ⟨W, hWo, hbW, -, ρ, hρ, -⟩ := tube Set.univ isOpen_univ (Set.mem_univ _)
    refine ⟨⟨W, hWo⟩, hbW, (rationalCohomologyMap (TopCat.ofHom
      ⟨fun y ↦ ψ.symm (ρ y), ψ.symm.continuous.comp ρ.continuous⟩) q).hom x, ?_⟩
    rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, retr ρ hρ hWo hbW,
      rationalCohomologyMap_id]
    rfl
  · obtain ⟨W, hWo, hbW, hWV, ρ, hρ, G, hG0, hG1⟩ := tube V V.isOpen hV
    let r : preimageSpace p ⟨W, hWo⟩ ⟶ analyticSpace sF :=
      TopCat.ofHom ⟨fun y ↦ ψ.symm (ρ y), ψ.symm.continuous.comp ρ.continuous⟩
    have hWV' : (⟨W, hWo⟩ : Opens (analyticSpace sB)) ≤ V := hWV
    let Hh : TopCat.Homotopy (preimageInclusion p hWV') (r ≫ fibreIncl f sB b i sF H.w hV) :=
      { toContinuousMap := G
        map_zero_left := fun y ↦ Subtype.ext (hG0 y)
        map_one_left := fun y ↦ Subtype.ext ((hG1 y).trans (by
          change _ = analyticMap i (fibreIncl_w f sB b i sF H.w) (ψ.symm (ρ y))
          rw [← hψ, Homeomorph.apply_symm_apply])) }
    have hmap : rationalCohomologyMap (preimageInclusion p hWV') q =
        rationalCohomologyMap (r ≫ fibreIncl f sB b i sF H.w hV) q :=
      MMP.relativeSingularCohomology.map_eq_of_homotopy ℚ Hh
        (fun y hy ↦ absurd (Set.mem_univ y) hy) _ _ q
    refine ⟨⟨W, hWo⟩, hWV', hbW, ?_⟩
    rw [hmap, rationalCohomologyMap_comp, ModuleCat.comp_apply, hα, map_zero]

end FibreComparison

/-! ### The sheet classes form a flat family over the cover -/

section SheetFamily

variable {Y Yt : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} {T : IrreducibleCloseds Y}
  {To : (curveScheme T).Opens} {T' : Scheme.{0}} {φ : T' ⟶ (To : Scheme.{0})}

/-- The point `φ(u') ∈ T°(ℂ)` under a point `u' ∈ T'(ℂ)`. -/
private abbrev coverPt (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    ComplexPoints (To.ι ≫ curveι T ≫ sY) :=
  analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl u'

/-- The sheet `F_{φ(u')} × {u'} ⟶ 𝓕' = 𝓕 ×_{T°} T'` through a point `u' ∈ T'(ℂ)`. -/
private abbrev sheetAt (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    pointFibre sY π To (coverPt u') ⟶ pullback (pullback.snd π (To.ι ≫ curveι T)) φ :=
  sheetι (t := coverPt u') ⟨u', rfl⟩

private theorem sheetAt_fst_fst (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    sheetAt π u' ≫ pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T) =
      pointFibreFst sY π To (coverPt u') := by
  rw [← Category.assoc, sheetι_comp_fst]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

private theorem sheetAt_snd (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    sheetAt π u' ≫ pullback.snd _ φ = pointFibreSnd sY π To (coverPt u') ≫ u'.hom :=
  pullback.lift_snd _ _ _

private theorem fam_comm (π : Yt ⟶ Y) :
    (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ ≫ pullback.fst π (To.ι ≫ curveι T)) ≫ π =
      pullback.snd _ φ ≫ φ ≫ To.ι ≫ curveι T := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]

/-- The fibre `F_{φ(u')}` is the fibre of `𝓕' ⟶ T'` over `u'`, through the sheet at `u'`. -/
private theorem isPullback_sheetAt (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    IsPullback (sheetAt π u') (pointFibreSnd sY π To (coverPt u'))
      (pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ) u'.hom := by
  have t := (IsPullback.of_hasPullback (pullback.snd π (To.ι ≫ curveι T)) φ).paste_horiz
    (IsPullback.of_hasPullback π (To.ι ≫ curveι T))
  have e2 : (coverPt u').hom ≫ To.ι ≫ curveι T = u'.hom ≫ φ ≫ To.ι ≫ curveι T :=
    Category.assoc _ _ _
  have s : IsPullback (sheetAt π u' ≫ pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T))
      (pointFibreSnd sY π To (coverPt u')) π (u'.hom ≫ φ ≫ To.ι ≫ curveι T) := by
    rw [sheetAt_fst_fst, ← e2]
    exact IsPullback.of_hasPullback _ _
  exact s.of_right (sheetAt_snd π u') t

private theorem sheetAt_w (π : Yt ⟶ Y) (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    sheetAt π u' ≫ pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ ≫
      φ ≫ To.ι ≫ curveι T ≫ sY = pointFibreSnd sY π To (coverPt u') :=
  fibreIncl_w _ _ u' _ _ (isPullback_sheetAt π u').w

/-- The class `c₁(𝓛') ∈ H²(𝓕'(ℂ); ℚ)`. -/
private def famClass (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0}))
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L'] :
    rationalCohomology (analyticSpace (pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ ≫
      φ ≫ To.ι ≫ curveι T ≫ sY)) 2 :=
  letI : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Over (Spec (.of ℂ)) :=
    ⟨pullback.snd _ φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY⟩
  singularCohomology.mapCoeff (Int.castRingHom ℚ) 2 (algebraicFirstChernClass L')

/-- The class of `𝓛'` restricts on each sheet to the class of the restriction of `𝓛'`. -/
private theorem rationalCohomologyMap_famClass (π : Yt ⟶ Y)
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L']
    (u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    (rationalCohomologyMap (analyticMap (sheetAt π u') (sheetAt_w π u')) 2).hom
        (famClass π φ L') =
      pointFibreChernClass sY π To (coverPt u')
        ((Scheme.Modules.pullback (sheetAt π u')).obj L') := by
  letI : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Over (Spec (.of ℂ)) :=
    ⟨pullback.snd _ φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY⟩
  unfold pointFibreChernClass
  rw [algebraicFirstChernClass_pullback (sheetAt π u')
    (analyticMap (sheetAt π u') (sheetAt_w π u')) (fun _ => rfl) L']
  exact (mapCoeff_map _ 2 _).symm

/-- The germ in `𝒲_u` of a class on `π⁻¹(V)`, for `V ∋ u`. -/
private abbrev germOf (π : Yt ⟶ Y) (u : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    {V : Opens (analyticSpace sY)} (hV : curveOpenInclusion sY To u ∈ V)
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2) :
    resolutionLocalSystemFibre sY π To u :=
  (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2) u).hom
    ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α)

/-- The germ of a class is the germ of the section of `𝒲` it defines. -/
private theorem germOf_eq_germ (π : Yt ⟶ Y) {V : Opens (analyticSpace sY)}
    (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2)
    (u : ComplexPoints (To.ι ≫ curveι T ≫ sY)) (hV : curveOpenInclusion sY To u ∈ V) :
    germOf π u hV α = ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).germ
      ((Opens.map (curveOpenInclusion sY To)).obj V) u hV
      (unitSec (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
        (((CategoryTheory.toSheafify _ (directImagePresheaf (resolutionAnalyticMap sY π) 2)).app
          (op V)).hom α)) := by
  have h1 : (higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α =
      ((TopCat.Sheaf.forget _ _).obj (resolutionHigherDirectImage sY π 2)).germ V _ hV
        (((CategoryTheory.toSheafify _
          (directImagePresheaf (resolutionAnalyticMap sY π) 2)).app (op V)).hom α) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply
      (F := directImagePresheaf (resolutionAnalyticMap sY π) 2) V _ hV
      (CategoryTheory.toSheafify _ (directImagePresheaf (resolutionAnalyticMap sY π) 2)) α
  exact (congrArg (stalkToPullbackStalk (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY π 2) u).hom h1).trans
    (stalkToPullbackStalk_germ (curveOpenInclusion sY To)
    (resolutionHigherDirectImage sY π 2) (((CategoryTheory.toSheafify _
      (directImagePresheaf (resolutionAnalyticMap sY π) 2)).app (op V)).hom α) u hV)

/-- **Realizing germs are unique.** Two germs realizing the same class on `F_t` agree. -/
theorem IsRealized.unique {π : Yt ⟶ Y} [IsProper π] [LocallyOfFiniteType sY]
    [IsSeparated sY] {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)} {x y y'}
    (h : IsRealized (sY := sY) (π := π) (To := To) (t := t) x y)
    (h' : IsRealized (sY := sY) (π := π) (To := To) (t := t) x y') : y = y' := by
  obtain ⟨V, hV, α, hα, rfl⟩ := h
  obtain ⟨V', hV', α', hα', rfl⟩ := h'
  have hW : curveOpenInclusion sY To t ∈ V ⊓ V' := ⟨hV, hV'⟩
  let a := (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY π)
    (inf_le_left : V ⊓ V' ≤ V)) 2).hom α
  let a' := (rationalCohomologyMap (preimageInclusion (resolutionAnalyticMap sY π)
    (inf_le_right : V ⊓ V' ≤ V')) 2).hom α'
  have hδ : (rationalCohomologyMap (pointFibreInclusion sY π To t hW) 2).hom (a - a') = 0 := by
    rw [map_sub, rationalCohomologyMap_pointFibreInclusion_preimageInclusion inf_le_left hW α,
      rationalCohomologyMap_pointFibreInclusion_preimageInclusion inf_le_right hW α',
      hα, hα', sub_self]
  obtain ⟨W, hWV, hW', hzero⟩ := (fibre_comparison π sY (curveOpenInclusion sY To t)
    (pointFibreFst sY π To t) (pointFibreSnd sY π To t) (IsPullback.of_hasPullback _ _) 2).2
      (V ⊓ V') hW (a - a') hδ
  have e : (rationalCohomologyMap (preimageInclusion _ hWV) 2).hom a =
      (rationalCohomologyMap (preimageInclusion _ hWV) 2).hom a' := by
    rw [← sub_eq_zero, ← map_sub]
    exact hzero
  have g1 := higherDirectImageGerm_preimageInclusion (sY := sY) (π := π) (To := To) (t := t)
    hWV hW' a
  have g2 := higherDirectImageGerm_preimageInclusion (sY := sY) (π := π) (To := To) (t := t)
    (inf_le_left : V ⊓ V' ≤ V) (hWV hW') α
  have g3 := higherDirectImageGerm_preimageInclusion (sY := sY) (π := π) (To := To) (t := t)
    hWV hW' a'
  have g4 := higherDirectImageGerm_preimageInclusion (sY := sY) (π := π) (To := To) (t := t)
    (inf_le_right : V ⊓ V' ≤ V') (hWV hW') α'
  exact congrArg _ (g2.symm.trans (g1.symm.trans ((congrArg _ e).trans (g3.trans g4))))

/-- The family `𝓕' = 𝓕 ×_{T°} T' ⟶ T'`. -/
private abbrev famMap (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) :
    pullback (pullback.snd π (To.ι ≫ curveι T)) φ ⟶ T' :=
  pullback.snd (pullback.snd π (To.ι ≫ curveι T)) φ

/-- The inverse image in `T'(ℂ)` of an open `V ⊆ Y(ℂ)`. -/
private abbrev coverOpen (φ : T' ⟶ (To : Scheme.{0})) (V : Opens (analyticSpace sY)) :
    Opens (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY)) :=
  (Opens.map (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl ≫ curveOpenInclusion sY To)).obj V

private theorem famToRes_w (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) :
    (pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T)) ≫ π ≫ sY =
      famMap π φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY := by
  rw [← Category.assoc _ π sY, fam_comm]
  simp only [Category.assoc]

/-- The realization `𝓕'(ℂ) ⟶ Ỹ(ℂ)` of `𝓕' ⟶ Ỹ`. -/
private abbrev famToResolution (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) :
    analyticSpace (famMap π φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY) ⟶ analyticSpace (π ≫ sY) :=
  analyticMap (pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T)) (famToRes_w π φ)

private theorem famToResolution_mem (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0}))
    (V : Opens (analyticSpace sY))
    (x : preimageSpace (analyticMap (famMap π φ) (sY := φ ≫ To.ι ≫ curveι T ≫ sY) rfl)
      (coverOpen φ V)) :
    famToResolution π φ x.1 ∈ resolutionAnalyticMap sY π ⁻¹' (V : Set (analyticSpace sY)) := by
  have e : resolutionAnalyticMap sY π (famToResolution π φ x.1) =
      curveOpenInclusion sY To (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl
        (analyticMap (famMap π φ) (sY := φ ≫ To.ι ≫ curveι T ≫ sY) rfl x.1)) := by
    ext1
    change (x.1.hom ≫ (pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T))) ≫ π =
      ((x.1.hom ≫ famMap π φ) ≫ φ) ≫ To.ι ≫ curveι T
    rw [Category.assoc, fam_comm]
    simp only [Category.assoc]
  rw [Set.mem_preimage, e]
  exact x.2

/-- The map `𝓕'(ℂ) ⊇ f'⁻¹(O) ⟶ π⁻¹(V)` induced by `𝓕' ⟶ Ỹ`, `O` the inverse image of `V`. -/
private def famToRes (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) (V : Opens (analyticSpace sY)) :
    preimageSpace (analyticMap (famMap π φ) (sY := φ ≫ To.ι ≫ curveι T ≫ sY) rfl)
      (coverOpen φ V) ⟶ preimageSpace (resolutionAnalyticMap sY π) V :=
  TopCat.ofHom ⟨fun x => ⟨famToResolution π φ x.1, famToResolution_mem π φ V x⟩,
    ((famToResolution π φ).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The inclusion `f'⁻¹(O) ⟶ 𝓕'(ℂ)`. -/
private def famIncl (π : Yt ⟶ Y) (φ : T' ⟶ (To : Scheme.{0})) (V : Opens (analyticSpace sY)) :
    preimageSpace (analyticMap (famMap π φ) (sY := φ ≫ To.ι ≫ curveι T ≫ sY) rfl)
      (coverOpen φ V) ⟶ analyticSpace (famMap π φ ≫ φ ≫ To.ι ≫ curveι T ≫ sY) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- **Local flatness of the sheet classes.** Near every point `u₀ ∈ T'(ℂ)` the classes of the
restrictions of `𝓛'` to the sheets are the restrictions of one class on a neighbourhood of the
fibre in `Ỹ(ℂ)`: a class realizing the sheet class at `u₀` (proper base change for `π`) and the
class of `𝓛'` agree on `F_{u₀}`, hence (proper base change for `𝓕' ⟶ T'`) on the part of `𝓕'` over
a neighbourhood of `u₀`. -/
private theorem exists_local_class (π : Yt ⟶ Y) [IsProper π] [LocallyOfFiniteType sY]
    [IsSeparated sY] [IsProper (famMap π φ)]
    [LocallyOfFiniteType (φ ≫ To.ι ≫ curveι T ≫ sY)] [IsSeparated (φ ≫ To.ι ≫ curveι T ≫ sY)]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L']
    (u₀ : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) :
    ∃ (V : Opens (analyticSpace sY))
      (β : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2)
      (N : Opens (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY))) (hN : N ≤ coverOpen φ V), u₀ ∈ N ∧
      ∀ u' (hu' : u' ∈ N), (rationalCohomologyMap (pointFibreInclusion sY π To (coverPt u')
          (hN hu')) 2).hom β =
        pointFibreChernClass sY π To (coverPt u')
          ((Scheme.Modules.pullback (sheetAt π u')).obj L') := by
  obtain ⟨V, hV, β, hβ⟩ := (fibre_comparison π sY (curveOpenInclusion sY To (coverPt u₀))
    (pointFibreFst sY π To (coverPt u₀)) (pointFibreSnd sY π To (coverPt u₀))
    (IsPullback.of_hasPullback _ _) 2).1
    (pointFibreChernClass sY π To (coverPt u₀) ((Scheme.Modules.pullback (sheetAt π u₀)).obj L'))
  have hu₀ : u₀ ∈ coverOpen φ V := hV
  let δ := (rationalCohomologyMap (famToRes π φ V) 2).hom β -
    (rationalCohomologyMap (famIncl π φ V) 2).hom (famClass π φ L')
  have key : ∀ u' (hu' : u' ∈ coverOpen φ V),
      (rationalCohomologyMap (fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu')
          2).hom δ =
      (rationalCohomologyMap (pointFibreInclusion sY π To (coverPt u') hu') 2).hom β -
        pointFibreChernClass sY π To (coverPt u')
          ((Scheme.Modules.pullback (sheetAt π u')).obj L') := by
    intro u' hu'
    have e1 : fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu' ≫
          famToRes π φ V = pointFibreInclusion sY π To (coverPt u') hu' := by
      ext x
      change x.hom ≫ sheetAt π u' ≫ pullback.fst _ φ ≫ pullback.fst π (To.ι ≫ curveι T) =
        x.hom ≫ pointFibreFst sY π To (coverPt u')
      rw [sheetAt_fst_fst]
    have e2 : fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu' ≫
          famIncl π φ V = analyticMap (sheetAt π u') (sheetAt_w π u') := rfl
    have k1 := congrArg (fun m => (rationalCohomologyMap m 2).hom β) e1
    have k2 := congrArg (fun m => (rationalCohomologyMap m 2).hom (famClass π φ L')) e2
    simp only [rationalCohomologyMap_comp, ModuleCat.comp_apply] at k2
    rw [rationalCohomologyMap_famClass] at k2
    refine (map_sub _ _ _).trans (congrArg₂ (· - ·) ?_ k2)
    refine Eq.trans ?_ k1
    exact (congrArg (fun m : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2 ⟶
        rationalCohomology (analyticSpace (pointFibreSnd sY π To (coverPt u'))) 2 => m.hom β)
      (rationalCohomologyMap_comp (fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu')
        (famToRes π φ V) 2)).symm
  have h0 : (rationalCohomologyMap (fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u₀
      (sheetAt π u₀) (pointFibreSnd sY π To (coverPt u₀)) (isPullback_sheetAt π u₀).w hu₀)
        2).hom δ = 0 :=
    (key u₀ hu₀).trans (sub_eq_zero.2 hβ)
  obtain ⟨W, hWV, hW0, hz⟩ := (fibre_comparison (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u₀
    (sheetAt π u₀) (pointFibreSnd sY π To (coverPt u₀)) (isPullback_sheetAt π u₀) 2).2
      (coverOpen φ V) hu₀ δ h0
  refine ⟨V, β, W, hWV, hW0, fun u' hu' => ?_⟩
  have e3 : fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
      (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w (hWV hu') =
      fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
        (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w hu' ≫
          preimageInclusion _ hWV := rfl
  have hz' : (rationalCohomologyMap (fibreIncl (famMap π φ) (φ ≫ To.ι ≫ curveι T ≫ sY) u'
      (sheetAt π u') (pointFibreSnd sY π To (coverPt u')) (isPullback_sheetAt π u').w
        (hWV hu')) 2).hom δ = 0 := by
    rw [e3, rationalCohomologyMap_comp, ModuleCat.comp_apply, hz, map_zero]
  exact sub_eq_zero.1 ((key u' (hWV hu')).symm.trans hz')

/-- **The flat family of sheet classes.** The germs in `𝒲` realizing the classes of `𝓛'` on the
sheets through the points of `T'(ℂ)` form a family along `T'(ℂ) ⟶ T°(ℂ)` which is locally given by
sections of `𝒲`. -/
private theorem exists_flat_family (π : Yt ⟶ Y) [IsProper π] [LocallyOfFiniteType sY]
    [IsSeparated sY] [IsProper (famMap π φ)]
    [LocallyOfFiniteType (φ ≫ To.ι ≫ curveι T ≫ sY)] [IsSeparated (φ ≫ To.ι ≫ curveι T ≫ sY)]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L'] :
    ∃ Ef : ∀ u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY),
        resolutionLocalSystemFibre sY π To (coverPt u'),
      (∀ u', IsRealized (sY := sY) (π := π) (To := To) (t := coverPt u')
        (pointFibreChernClass sY π To (coverPt u')
          ((Scheme.Modules.pullback (sheetAt π u')).obj L')) (Ef u')) ∧
      ∀ e₀, ∃ (W : Opens (analyticSpace (To.ι ≫ curveι T ≫ sY)))
        (r : ToType (((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).obj (op W)))
        (N : Opens (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY))) (_ : e₀ ∈ N)
        (hNW : N ≤ (Opens.map (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl)).obj W),
        ∀ e (he : e ∈ N), Ef e =
          ((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).germ W
            (analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl e) (hNW he) r := by
  have hex : ∀ u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY), ∃ y,
      IsRealized (sY := sY) (π := π) (To := To) (t := coverPt u')
        (pointFibreChernClass sY π To (coverPt u')
          ((Scheme.Modules.pullback (sheetAt π u')).obj L')) y := by
    intro u'
    obtain ⟨V, hV, α, hα⟩ := (fibre_comparison π sY (curveOpenInclusion sY To (coverPt u'))
      (pointFibreFst sY π To (coverPt u')) (pointFibreSnd sY π To (coverPt u'))
      (IsPullback.of_hasPullback _ _) 2).1 (pointFibreChernClass sY π To (coverPt u')
        ((Scheme.Modules.pullback (sheetAt π u')).obj L'))
    exact ⟨_, V, hV, α, hα, rfl⟩
  choose Ef hEf using hex
  refine ⟨Ef, hEf, fun e₀ => ?_⟩
  obtain ⟨V, β, N, hN, he₀, hloc⟩ := exists_local_class π L' e₀
  refine ⟨(Opens.map (curveOpenInclusion sY To)).obj V,
    unitSec (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
      (((CategoryTheory.toSheafify _ (directImagePresheaf (resolutionAnalyticMap sY π) 2)).app
        (op V)).hom β), N, he₀, hN, fun e he => ?_⟩
  exact ((hEf e).unique ⟨V, hN he, β, hloc e he, rfl⟩).trans (germOf_eq_germ π β _ (hN he))

private theorem isRealized_transport {π : Yt ⟶ Y}
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    [SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L']
    {u' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)}
    {y : resolutionLocalSystemFibre sY π To (coverPt u')}
    (hy : IsRealized (sY := sY) (π := π) (To := To) (t := coverPt u')
      (pointFibreChernClass sY π To (coverPt u')
        ((Scheme.Modules.pullback (sheetAt π u')).obj L')) y)
    {t : ComplexPoints (To.ι ≫ curveι T ≫ sY)} (h : coverPt u' = t) (h' : u'.hom ≫ φ = t.hom) :
    IsRealized (sY := sY) (π := π) (To := To) (t := t)
      (pointFibreChernClass sY π To t ((Scheme.Modules.pullback (sheetι (π := π) ⟨u', h'⟩)).obj L'))
      ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
        (.of_eq h)).hom.hom y) := by
  subst h
  rw [stalkCongr_self]
  exact hy

private theorem stalkCongr_congr_point {Z E : TopCat.{0}} (F : TopCat.Sheaf (ModuleCat.{0} ℚ) Z)
    (p : E ⟶ Z) (Ef : ∀ e : E, ToType (((TopCat.Sheaf.forget _ Z).obj F).stalk (p e)))
    {e₁ e₂ : E} (he : e₁ = e₂) {t : Z} (h₁ : p e₁ = t) (h₂ : p e₂ = t) :
    (((TopCat.Sheaf.forget _ Z).obj F).stalkCongr (.of_eq h₁)).hom.hom (Ef e₁) =
      (((TopCat.Sheaf.forget _ Z).obj F).stalkCongr (.of_eq h₂)).hom.hom (Ef e₂) := by
  subst he
  rfl

end SheetFamily

/-- **The class of `𝓛'` is flat along the cover.** For each `ℂ`-point `t''` of `T'` above `t`,
the first Chern class of `𝓛'` on the sheet `F_t × {t''}` is the restriction to `F_t` of a class
on a neighbourhood of `F_t` in `Ỹ^an`, with germ `e t'' ∈ 𝒲_t` (proper base change). The class of
`𝓛'` is a flat section of `φ^* 𝒲`, so `e t''` is the transport of `c = e t'` along the image of
a path from `t'` to `t''` in the connected `T'^an`, and the transport `g ∈ G` along a loop `γ`
at `t` carries `e t''` to `e (σ t'')`, `σ` the monodromy permutation of the fibre along `γ`. -/
private theorem exists_sheetClass
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (Θ : QDivisor Y) (T : IrreducibleCloseds Y) (π : Yt ⟶ Y)
    (hS : IsLocalSetting sY Θ T π)
    (To : (curveScheme T).Opens) (hTo : IsAdaptedOpen sY π To)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (G : Set (Module.End ℚ (resolutionLocalSystemFibre sY π To t)))
    (hG : ∀ g, g ∈ G ↔ ∃ γ : Path t t,
      ∀ (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
            (resolutionLocalSystem sY π To)).obj.obj (op ⊤)))
        (w v : resolutionLocalSystemFibre sY π To t),
        (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
            (resolutionLocalSystem sY π To) 0).hom
            ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
              (.of_eq γ.source.symm)).hom.hom w) =
          (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (resolutionLocalSystem sY π To))).germ ⊤ 0 trivial).hom s →
        (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
            (resolutionLocalSystem sY π To) 1).hom
            ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
              (.of_eq γ.target.symm)).hom.hom v) =
          (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (resolutionLocalSystem sY π To))).germ ⊤ 1 trivial).hom s →
        g w = v)
    (hGfin : G.Finite)
    {T' : Scheme.{0}} (φ : T' ⟶ (To : Scheme.{0})) [IsFinite φ] [Etale φ] [ConnectedSpace T']
    (t' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) (ht' : t'.hom ≫ φ = t.hom)
    [Stacks.Morphisms.IsFiniteLocallyFree (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)]
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    (hL' : SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L')
    (ι : pointFibre sY π To t ⟶ pullback (pullback.snd π (To.ι ≫ curveι T)) φ)
    (hι₁ : ι ≫ pullback.fst _ _ = pointFibreToFamily sY π To t)
    (hι₂ : ι ≫ pullback.snd _ _ = pointFibreSnd sY π To t ≫ t'.hom)
    (c : resolutionLocalSystemFibre sY π To t)
    (hc : ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2),
      (∃ _ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
          (pointFibre sY π To t).ringCatSheaf.2 ((Scheme.Modules.pullback ι).obj L'),
        (rationalCohomologyMap (pointFibreInclusion sY π To t hV) 2).hom α =
          pointFibreChernClass sY π To t ((Scheme.Modules.pullback ι).obj L')) ∧
      (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
          t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α) = c) :
    haveI := hL'
    ∃ e : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom} →
        resolutionLocalSystemFibre sY π To t,
      (∀ s, IsRealized (sY := sY) (π := π) (To := To) (t := t)
        (pointFibreChernClass sY π To t ((Scheme.Modules.pullback (sheetι s)).obj L')) (e s)) ∧
      (∀ s, ∃ h ∈ G, e s = h c) ∧
      (∀ g ∈ G, ∃ σ : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom} ≃
        {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom},
        ∀ s, e (σ s) = g (e s)) := by
  classical
  haveI := hL'
  obtain ⟨hlft, -, hsep⟩ := curveOpen_structure sY Θ T π hS To
  haveI : AlgebraicGeometry.IsVariety ℂ sY := hS.isProjectiveVariety.toIsVariety
  haveI : IsProper π := isProper_of_isProjectiveMorphism π hS.isResolution.2.2.2.1
  haveI : IsProper (pullback.snd π (To.ι ≫ curveι T)) :=
    isProper_of_isProjectiveMorphism _ hTo.isProjectiveMorphism
  haveI : IsProper (famMap π φ) := inferInstance
  haveI : LocallyOfFiniteType (φ ≫ To.ι ≫ curveι T ≫ sY) := inferInstance
  haveI : IsSeparated (φ ≫ To.ι ≫ curveι T ≫ sY) := inferInstance
  obtain ⟨Ef, hEf, hloc⟩ := exists_flat_family (sY := sY) (To := To) (φ := φ) π L'
  set p := analyticMap φ (sY := To.ι ≫ curveι T ≫ sY) rfl with hp
  set Wt := resolutionLocalSystem sY π To
  set PW := (TopCat.Sheaf.forget _ _).obj Wt
  have hcov : ∀ s : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom},
      p s.1 = t := fun s => ComplexPoints.ext s.2
  let e : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom} →
      resolutionLocalSystemFibre sY π To t := fun s =>
    (PW.stalkCongr (.of_eq (hcov s))).hom.hom (Ef s.1)
  have hreal : ∀ s, IsRealized (sY := sY) (π := π) (To := To) (t := t)
      (pointFibreChernClass sY π To t ((Scheme.Modules.pullback (sheetι s)).obj L')) (e s) :=
    fun s => isRealized_transport L' (hEf s.1) (hcov s) s.2
  -- the given class `c` is the germ on the sheet through `t'`
  have hι : ι = sheetι (π := π) ⟨t', ht'⟩ := pullback.hom_ext
    (hι₁.trans (sheetι_comp_fst _).symm) (hι₂.trans (pullback.lift_snd _ _ _).symm)
  subst hι
  have hc' : e ⟨t', ht'⟩ = c := by
    obtain ⟨V, hV, α, ⟨_, h₁⟩, h₂⟩ := hc
    exact (hreal ⟨t', ht'⟩).unique ⟨V, hV, α, h₁, h₂⟩
  refine ⟨e, hreal, fun s => ?_, fun g hg => ?_⟩
  · -- a path from `t'` to the sheet `s` in the connected `T'(ℂ)`
    haveI : ConnectedSpace (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY)) :=
      connectedSpace_analyticSpace_cover sY Θ T π hS To hTo φ
    haveI := locallyPathConnectedSpace_analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY)
    haveI : PathConnectedSpace (analyticSpace (φ ≫ To.ι ≫ curveι T ≫ sY)) :=
      pathConnectedSpace_iff_connectedSpace.2 inferInstance
    let δ : Path t' s.1 := PathConnectedSpace.somePath t' s.1
    have h0 : p t' = t := hcov ⟨t', ht'⟩
    let γ : Path t t := (δ.map p.hom.continuous).cast h0.symm (hcov s).symm
    obtain ⟨g, hg⟩ := exists_isTransport Wt hTo.isLocalSystem_resolution γ
    refine ⟨g, (hG g).2 ⟨γ, hg⟩, ?_⟩
    have hδ0 : p (δ.toContinuousMap 0) = t := by
      change p (δ 0) = t
      rw [δ.source]
      exact h0
    have hδ1 : p (δ.toContinuousMap 1) = t := by
      change p (δ 1) = t
      rw [δ.target]
      exact hcov s
    have key := IsTransport.apply_lift (F := Wt) (p := p) Ef hloc hg δ.toContinuousMap
      (fun x => rfl) hδ0 hδ1
    rw [← hc']
    refine (stalkCongr_congr_point Wt p Ef δ.target.symm (hcov s) hδ1).trans (key.symm.trans ?_)
    exact congrArg g (stalkCongr_congr_point Wt p Ef δ.source hδ0 h0)
  · obtain ⟨γ, hγ⟩ := (hG g).1 hg
    have hγ' : IsTransport Wt γ g := hγ
    have cov := (isCoveringMap_analyticMap_cover sY Θ T π hS To φ).1
    obtain ⟨σ, hσ⟩ := exists_perm_lift cov γ
    let eqv : {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom} ≃
        (p ⁻¹' {t}) :=
      { toFun := fun s => ⟨s.1, hcov s⟩
        invFun := fun u => ⟨u.1, congrArg ComplexPoints.hom u.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    refine ⟨eqv.trans (σ.trans eqv.symm), fun s => ?_⟩
    obtain ⟨Γ', hΓ', h0, h1⟩ := hσ (eqv s)
    have hΓ0 : p (Γ' 0) = t := by rw [h0]; exact hcov s
    have hΓ1 : p (Γ' 1) = t := by rw [h1]; exact (σ (eqv s)).2
    have key := IsTransport.apply_lift (F := Wt) (p := p) Ef hloc hγ' Γ' hΓ' hΓ0 hΓ1
    refine (stalkCongr_congr_point Wt p Ef h1.symm (σ (eqv s)).2 hΓ1).trans (key.symm.trans ?_)
    exact congrArg g (stalkCongr_congr_point Wt p Ef h0 hΓ0 (hcov s))

/-- **Norms average first Chern classes.** For a local setting `(Y, Θ, T, π)`, a `π`-adapted
open `T°`, a point `t ∈ T°(ℂ)` with finite monodromy image `G ⊆ GL(𝒲_t)`, a connected finite
étale cover `φ : T' ⟶ T°` with a point `t'` over `t`, and an invertible module `𝓛'` on
`𝓕' = 𝓕 ×_{T°} T'` whose restriction to the sheet `F_t × {t'}` has class `c ∈ 𝒲_t`, the first
Chern class of the restriction to `F_t` of the norm of `𝓛'` along `𝓕' ⟶ 𝓕` is `d • Av_G(c)`,
`d` the number of sheets of `φ` over `t`. -/
@[mmp "lem_oai4_c2_norm_chern_average"]
public theorem pointFibreChernClass_normInvertible_eq_smul_average
    {Y Yt : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sY : Y ⟶ Spec (.of ℂ)) (Θ : QDivisor Y) (T : IrreducibleCloseds Y) (π : Yt ⟶ Y)
    (hS : IsLocalSetting sY Θ T π)
    (To : (curveScheme T).Opens) (hTo : IsAdaptedOpen sY π To)
    (t : ComplexPoints (To.ι ≫ curveι T ≫ sY))
    (G : Set (Module.End ℚ (resolutionLocalSystemFibre sY π To t)))
    (hG : ∀ g, g ∈ G ↔ ∃ γ : Path t t,
      ∀ (s : ToType (((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
          (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
            (resolutionLocalSystem sY π To)).obj.obj (op ⊤)))
        (w v : resolutionLocalSystemFibre sY π To t),
        (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
            (resolutionLocalSystem sY π To) 0).hom
            ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
              (.of_eq γ.source.symm)).hom.hom w) =
          (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (resolutionLocalSystem sY π To))).germ ⊤ 0 trivial).hom s →
        (stalkToPullbackStalk (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)
            (resolutionLocalSystem sY π To) 1).hom
            ((((TopCat.Sheaf.forget _ _).obj (resolutionLocalSystem sY π To)).stalkCongr
              (.of_eq γ.target.symm)).hom.hom v) =
          (((TopCat.Sheaf.forget _ _).obj ((TopCat.Sheaf.pullback (ModuleCat.{0} ℚ)
            (TopCat.ofHom (X := TopCat.of unitInterval) γ.toContinuousMap)).obj
              (resolutionLocalSystem sY π To))).germ ⊤ 1 trivial).hom s →
        g w = v)
    (hGfin : G.Finite)
    {T' : Scheme.{0}} (φ : T' ⟶ (To : Scheme.{0})) [IsFinite φ] [Etale φ] [ConnectedSpace T']
    (t' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY)) (ht' : t'.hom ≫ φ = t.hom)
    (L' : (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).Modules)
    (hL' : SheafOfModules.IsInvertible (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).presheaf
      (pullback (pullback.snd π (To.ι ≫ curveι T)) φ).ringCatSheaf.2 L')
    (ι : pointFibre sY π To t ⟶ pullback (pullback.snd π (To.ι ≫ curveι T)) φ)
    (hι₁ : ι ≫ pullback.fst _ _ = pointFibreToFamily sY π To t)
    (hι₂ : ι ≫ pullback.snd _ _ = pointFibreSnd sY π To t ≫ t'.hom)
    (c : resolutionLocalSystemFibre sY π To t)
    (hc : ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2),
      (∃ _ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
          (pointFibre sY π To t).ringCatSheaf.2 ((Scheme.Modules.pullback ι).obj L'),
        (rationalCohomologyMap (pointFibreInclusion sY π To t hV) 2).hom α =
          pointFibreChernClass sY π To t ((Scheme.Modules.pullback ι).obj L')) ∧
      (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
          t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α) = c) :
    haveI : Stacks.Morphisms.IsFiniteLocallyFree
        (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) :=
      (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
        ⟨inferInstance, inferInstance, inferInstance⟩
    ∃ (V : Opens (analyticSpace sY)) (hV : curveOpenInclusion sY To t ∈ V)
        (α : rationalCohomology (preimageSpace (resolutionAnalyticMap sY π) V) 2),
      (∃ _ : SheafOfModules.IsInvertible (pointFibre sY π To t).presheaf
          (pointFibre sY π To t).ringCatSheaf.2
          ((Scheme.Modules.pullback (pointFibreToFamily sY π To t)).obj
            (Stacks.Divisors.normInvertible
              (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)
              (Stacks.Norm.finiteLocallyFreeNorm
                (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)).toMorphismNormMap L')),
        (rationalCohomologyMap (pointFibreInclusion sY π To t hV) 2).hom α =
          pointFibreChernClass sY π To t
            ((Scheme.Modules.pullback (pointFibreToFamily sY π To t)).obj
              (Stacks.Divisors.normInvertible
                (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)
                (Stacks.Norm.finiteLocallyFreeNorm
                  (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ)).toMorphismNormMap
                L'))) ∧
      (stalkToPullbackStalk (curveOpenInclusion sY To) (resolutionHigherDirectImage sY π 2)
          t).hom ((higherDirectImageGerm (resolutionAnalyticMap sY π) 2 _ hV).hom α) =
        (Nat.card {t'' : ComplexPoints (φ ≫ To.ι ≫ curveι T ≫ sY) // t''.hom ≫ φ = t.hom} : ℚ) •
          ((Nat.card G : ℚ)⁻¹ • ∑ᶠ g ∈ G, g c) := by
  classical
  have : Stacks.Morphisms.IsFiniteLocallyFree
      (pullback.fst (pullback.snd π (To.ι ≫ curveι T)) φ) :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  haveI := hL'
  haveI := finite_sheets To t φ
  obtain ⟨e, hreal, horb, hperm⟩ :=
    exists_sheetClass sY Θ T π hS To hTo t G hG hGfin φ t' ht' L' hL' ι hι₁ hι₂ c hc
  obtain ⟨instN, hN⟩ := pointFibreChernClass_pullback_normInvertible_eq_finsum sY T π To t φ L'
  have hsum := finsum_eq_card_smul_average G hGfin
    (monodromy_mul_mem _ hG) (monodromy_surjective hTo.isLocalSystem_resolution hG) e c horb
    hperm
  obtain ⟨V, hV, α, h₁, h₂⟩ := isRealized_finsum _ _ hreal
  exact ⟨V, hV, α, ⟨instN, h₁.trans hN.symm⟩, h₂.trans hsum⟩

end MMP.Fourfold

end
