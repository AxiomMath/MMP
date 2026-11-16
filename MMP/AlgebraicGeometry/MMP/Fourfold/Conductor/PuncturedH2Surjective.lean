module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.PuncturedLocalSystem
public import MMP.AlgebraicGeometry.Analytic.Analytification
public import MMP.AlgebraicGeometry.Resolution.Basic
public import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ThreefoldLocalOddForm
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.DualityAntiampleFibre
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.SncFibreHomologyThree
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.Analytic.ComplexPoints.UnderlyingSpaceProperMap
import MMP.AlgebraicGeometry.Analytic.AnalyticMapOpenSubscheme
import MMP.AlgebraicTopology.SingularCohomology.PairSequence.Supports
import MMP.AlgebraicTopology.SingularCohomology.Relative.Excision
import MMP.AlgebraicTopology.FundamentalClass.Exists
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import MMP.AlgebraicGeometry.Variety.Subvariety
public import MMP.AlgebraicGeometry.ReducedSubschemeOver
public import MMP.AlgebraicGeometry.SubschemeOver
import MMP.AlgebraicGeometry.Morphisms.SmoothStalkDimension
import MMP.AlgebraicGeometry.Chow.CycleClassGenericPoint
import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionPushPull
import MMP.AlgebraicGeometry.SpecOverSpecSelf

/-!
# Punctured `H²` restriction at an isolated threefold singularity

Let `S` be a normal quasi-projective complex threefold, `x` an isolated singular point and
`f₀ : W₀ ⟶ S` a projective resolution which is an isomorphism over `V = U ∖ {x}`. Restriction
along the section `s : V ⟶ W₀` induces a surjection `(R²f₀_* ℚ)_x ⟶ (R²j_* ℚ)_x` of stalks.

## Main results

* `MMP.Fourfold.surjective_stalk_higherDirectImageRestriction_two`
-/

open CategoryTheory AlgebraicGeometry MMP MMP.Analytic MMP.Analytic.ComplexPoints
  MMP.Fourfold MMP.Mori
open scoped MMP.SubschemeOver

namespace MMP.Fold06.ThmMmpConductorThreefoldPuncturedH2Surjective

/-! ### Extending classes across a closed set -/

section Topology

/-- Restriction to `E` (forget the supports, then restrict) is injective on `H^q_E(Y)`. -/
private def RestrictInj (Y : TopCat.{0}) (E : Set Y) (q : ℕ) : Prop :=
  ∀ c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y E q,
    (rationalCohomologyMap (subspaceInclusion Y E) q).hom
      ((cohomologyWithSupports.toCohomology ℚ _ Y E q).hom c) = 0 → c = 0

/-- Functoriality of relative cohomology, against any factorisation `g ≫ f = k`. -/
private lemma map_comp_eq {Y'' Y' Y : TopCat.{0}} {g : Y'' ⟶ Y'} {f : Y' ⟶ Y} {k : Y'' ⟶ Y}
    (hk : g ≫ f = k) {A'' : Set Y''} {A' : Set Y'} {A : Set Y} (hg : A'' ⊆ g ⁻¹' A')
    (hf : A' ⊆ f ⁻¹' A) (hk' : A'' ⊆ k ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f hf j ≫
        relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) g hg j =
      relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) k hk' j := by
  subst hk; exact (relativeSingularCohomology.map_comp _ _ g f hg hf j).symm

/-- Two factorisations of the same map induce the same map on relative cohomology. -/
private lemma map_comp_eq_comp {Y'' Y₁ Y₂ Y : TopCat.{0}} {g₁ : Y'' ⟶ Y₁} {f₁ : Y₁ ⟶ Y}
    {g₂ : Y'' ⟶ Y₂} {f₂ : Y₂ ⟶ Y} (hk : g₁ ≫ f₁ = g₂ ≫ f₂) {A'' : Set Y''} {A₁ : Set Y₁}
    {A₂ : Set Y₂} {A : Set Y} (hg₁ : A'' ⊆ g₁ ⁻¹' A₁) (hf₁ : A₁ ⊆ f₁ ⁻¹' A)
    (hg₂ : A'' ⊆ g₂ ⁻¹' A₂) (hf₂ : A₂ ⊆ f₂ ⁻¹' A) (j : ℤ) :
    relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f₁ hf₁ j ≫
        relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) g₁ hg₁ j =
      relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) f₂ hf₂ j ≫
        relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) g₂ hg₂ j :=
  (map_comp_eq hk hg₁ hf₁ (fun _ hx ↦ hf₂ (hg₂ hx)) j).trans
    (map_comp_eq rfl hg₂ hf₂ (fun _ hx ↦ hf₂ (hg₂ hx)) j).symm

/-- Forgetting supports commutes with pullback. -/
private lemma pullback_toCohomology {Y' Y : TopCat.{0}} (φ : Y' ⟶ Y) (E : Set Y) (q : ℕ) :
    cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) φ E q ≫
      cohomologyWithSupports.toCohomology ℚ _ Y' (φ ⁻¹' E) q =
    cohomologyWithSupports.toCohomology ℚ _ Y E q ≫ rationalCohomologyMap φ q :=
  map_comp_eq_comp (by rfl) _ _ _ _ _

/-- Restricting a pulled-back supported class to `φ⁻¹(E)` is restricting it to `E` and pulling
back along `φ⁻¹(E) → E`. -/
private lemma restrict_pullback {Y' Y : TopCat.{0}} (φ : Y' ⟶ Y) (E : Set Y) (q : ℕ)
    (c : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) Y E q) :
    (rationalCohomologyMap (subspaceInclusion Y' (φ ⁻¹' E)) q).hom
      ((cohomologyWithSupports.toCohomology ℚ _ Y' (φ ⁻¹' E) q).hom
        ((cohomologyWithSupports.pullback ℚ _ φ E q).hom c)) =
    (rationalCohomologyMap (subspaceRestrict φ (A' := φ ⁻¹' E) (A := E) subset_rfl) q).hom
      ((rationalCohomologyMap (subspaceInclusion Y E) q).hom
        ((cohomologyWithSupports.toCohomology ℚ _ Y E q).hom c)) := by
  have key : cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) φ E q ≫
      cohomologyWithSupports.toCohomology ℚ _ Y' (φ ⁻¹' E) q ≫
        rationalCohomologyMap (subspaceInclusion Y' (φ ⁻¹' E)) q =
      cohomologyWithSupports.toCohomology ℚ _ Y E q ≫
        rationalCohomologyMap (subspaceInclusion Y E) q ≫
          rationalCohomologyMap (subspaceRestrict φ (A' := φ ⁻¹' E) (A := E) subset_rfl) q := by
    rw [← Category.assoc, pullback_toCohomology, Category.assoc, ← rationalCohomologyMap_comp,
      ← rationalCohomologyMap_comp, subspaceRestrict_comp_subspaceInclusion]
  exact congrArg (fun m ↦ m.hom c) key

/-- Transfer of `RestrictInj` up a map whose pullback on supported cohomology is onto. -/
private lemma restrictInj_preimage {Y' Y : TopCat.{0}} (φ : Y' ⟶ Y) (E : Set Y) (q : ℕ)
    (hsurj : Function.Surjective (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) φ E q).hom)
    (hinj : Function.Injective
      (rationalCohomologyMap (subspaceRestrict φ (A' := φ ⁻¹' E) (A := E) subset_rfl) q).hom)
    (h : RestrictInj Y E q) : RestrictInj Y' (φ ⁻¹' E) q := by
  intro c' hc'
  obtain ⟨c, rfl⟩ := hsurj c'
  rw [restrict_pullback] at hc'
  rw [h c (hinj (hc'.trans (map_zero _).symm)), map_zero]

/-- Transfer of `RestrictInj` down a map whose pullback on supported cohomology is injective. -/
private lemma restrictInj_of_preimage {Y' Y : TopCat.{0}} (φ : Y' ⟶ Y) (E : Set Y) (q : ℕ)
    (hinj : Function.Injective
      (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) φ E q).hom)
    (h : RestrictInj Y' (φ ⁻¹' E) q) : RestrictInj Y E q := by
  intro c hc
  refine hinj ((h _ ?_).trans (map_zero _).symm)
  rw [restrict_pullback, hc, map_zero]

/-- If restriction to `E` is injective on `H³_E(Y)`, every class on `Y - E` of degree two
extends to `Y`. -/
private lemma exists_restrictCompl_eq (Y : TopCat.{0}) (E : Set Y) (h : RestrictInj Y E (2 + 1))
    (β : cohomologyWithSupports ℚ (ModuleCat.of ℚ ℚ) (TopCat.of ↥Eᶜ) Set.univ (2 : ℕ)) :
    ∃ α, (cohomologyWithSupports.restrictCompl ℚ Y E (2 : ℕ)).hom α = β := by
  have h0 : (cohomologyWithSupports.toCohomology ℚ _ Y E ((2 + 1 : ℕ) : ℤ)).hom
      (cohomologyWithSupports.delta ℚ Y E 2 β) = 0 :=
    (cohomologyWithSupports.exact_delta_toCohomology ℚ Y E 2 _).2 ⟨β, rfl⟩
  exact (cohomologyWithSupports.exact_restrictCompl_delta ℚ Y E 2 β).1 (h _ (by rw [h0, map_zero]))

/-- A map with a section induces an injection on rational cohomology. -/
private lemma injective_rationalCohomologyMap_of_comp_eq_id {A B : TopCat.{0}} (k : A ⟶ B)
    (l : B ⟶ A)
    (h : l ≫ k = 𝟙 B) (q : ℕ) : Function.Injective (rationalCohomologyMap k q).hom := by
  refine Function.LeftInverse.injective (g := (rationalCohomologyMap l q).hom) fun a ↦ ?_
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, h, rationalCohomologyMap_id]
  rfl

/-- A homeomorphism induces a bijection on cohomology with supports. -/
private lemma bijective_pullback_of_comp_eq_id {Y' Y : TopCat.{0}} (f : Y' ⟶ Y) (g : Y ⟶ Y')
    (hfg : f ≫ g = 𝟙 Y') (hgf : g ≫ f = 𝟙 Y) (X : Set Y) (j : ℤ) :
    Function.Bijective (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f X j).hom := by
  have hX : Xᶜ ⊆ g ⁻¹' (f ⁻¹' X)ᶜ := fun y hy hy' ↦ hy (by
    have : f (g y) = y := congrArg (fun m ↦ m y) hgf
    simpa [this] using hy')
  let ψ := relativeSingularCohomology.map ℚ (ModuleCat.of ℚ ℚ) g hX j
  have h1 : cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f X j ≫ ψ = 𝟙 _ :=
    (map_comp_eq hgf _ _ (fun _ h ↦ h) j).trans (relativeSingularCohomology.map_id _ _ _ _ _)
  have h2 : ψ ≫ cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ) f X j = 𝟙 _ :=
    (map_comp_eq hfg _ _ (fun _ h ↦ h) j).trans (relativeSingularCohomology.map_id _ _ _ _ _)
  refine ⟨Function.LeftInverse.injective (g := ψ.hom) fun a ↦ ?_,
    Function.RightInverse.surjective (g := ψ.hom) fun a ↦ ?_⟩
  · rw [← ModuleCat.comp_apply, h1]; rfl
  · rw [← ModuleCat.comp_apply, h2]; rfl

/-- `RestrictInj` passes to an open subset containing `E`, along an open embedding. -/
private lemma restrictInj_of_isOpenEmbedding {Y' Y : TopCat.{0}} (φ : Y' ⟶ Y)
    (hφ : Topology.IsOpenEmbedding φ)
    (E : Set Y) (hE : IsClosed E) (hEφ : E ⊆ Set.range φ) (q : ℕ) (h : RestrictInj Y E q) :
    RestrictInj Y' (φ ⁻¹' E) q := by
  set V : Set Y := Set.range φ
  have hV : IsOpen V := hφ.isOpen_range
  -- excision to `V`
  have h₁ : RestrictInj (TopCat.of V) (subspaceInclusion Y V ⁻¹' E) q := by
    refine restrictInj_preimage _ E q ?_ ?_ h
    · haveI := cohomologyWithSupports.isIso_pullback_subspaceInclusion ℚ hV hE hEφ q
      exact ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).2
    · refine injective_rationalCohomologyMap_of_comp_eq_id _
        (TopCat.ofHom ⟨fun e ↦ ⟨⟨e.1, hEφ e.2⟩, e.2⟩, by fun_prop⟩) ?_ q
      rfl
  -- the homeomorphism `Y' ≃ V`
  let e := hφ.isEmbedding.toHomeomorph
  let f : Y' ⟶ TopCat.of V := TopCat.ofHom ⟨e, e.continuous⟩
  let g : TopCat.of V ⟶ Y' := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hfg : f ≫ g = 𝟙 Y' := TopCat.ext fun y ↦ e.symm_apply_apply y
  have hgf : g ≫ f = 𝟙 _ := TopCat.ext fun y ↦ e.apply_symm_apply y
  have h₂ := restrictInj_preimage f _ q
    (bijective_pullback_of_comp_eq_id f g hfg hgf _ _).2
    (injective_rationalCohomologyMap_of_comp_eq_id _
      (TopCat.ofHom ⟨fun a ↦ ⟨g a.1, Set.mem_preimage.2 (by
        rw [show f (g a.1) = a.1 from congrArg (fun m ↦ m a.1) hgf]
        exact a.2)⟩, (g.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩)
      (TopCat.ext fun a ↦ Subtype.ext (congrArg (fun m ↦ m a.1) hgf)) q) h₁
  exact h₂

end Topology

/-! ### Injectivity of the restriction to the fibre -/

section Duality

/-- The local ring at a `ℂ`-point of an algebraic scheme smooth of relative dimension `d` over
`ℂ` has dimension `d`. -/
private theorem ringKrullDim_stalk_eq_of_smoothOfRelativeDimension {U : Scheme.{0}}
    [U.Over (Spec (.of ℂ))] [LocallyOfFiniteType (U ↘ Spec (.of ℂ))]
    [QuasiCompact (U ↘ Spec (.of ℂ))] (d : ℕ)
    [SmoothOfRelativeDimension d (U ↘ Spec (.of ℂ))] [IsSeparated (U ↘ Spec (.of ℂ))]
    (p : UnderlyingSpace ℂ U) :
    ringKrullDim (U.presheaf.stalk (p.toHom (IsLocalRing.closedPoint ℂ))) = d := by
  haveI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of ℂ))
  haveI : IsClosedImmersion (p.toHom ≫ U ↘ Spec (.of ℂ)) := by
    rw [p.toHom_comp_over]; infer_instance
  haveI : IsClosedImmersion p.toHom := IsClosedImmersion.of_comp p.toHom (U ↘ Spec (.of ℂ))
  have h := MMP.ringKrullDim_stalk_eq_add_of_smoothOfRelativeDimension p.toHom
    (U ↘ Spec (.of ℂ)) (n := d) (IsLocalRing.closedPoint ℂ)
  have h0 : ∀ x : Spec (.of ℂ), ringKrullDim ((Spec (.of ℂ)).presheaf.stalk x) = 0 := by
    intro x
    haveI : x.asIdeal.IsPrime := x.isPrime
    rw [ringKrullDim_eq_of_ringEquiv (Spec.stalkIso (.of ℂ) x).commRingCatIsoToRingEquiv,
      IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal, Ideal.eq_bot_of_prime x.asIdeal]
    simp
  rw [h0] at h
  simpa using h

/-- An open `V` of a scheme over `ℂ` on which `appLE` is standard smooth of relative
dimension `n` is smooth of relative dimension `n` over `ℂ`. -/
private theorem smoothOfRelativeDimension_opens_of_appLE {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    (U : (Spec (.of ℂ)).Opens) (hU : IsAffineOpen U) (V : W.Opens) (hV : IsAffineOpen V)
    (e : V ≤ (W ↘ Spec (.of ℂ)) ⁻¹ᵁ U) {n : ℕ}
    (hr : RingHom.IsStandardSmoothOfRelativeDimension n ((W ↘ Spec (.of ℂ)).appLE U V e).hom) :
    letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ W ↘ Spec (.of ℂ)⟩
    SmoothOfRelativeDimension n (V.toScheme ↘ Spec (.of ℂ)) := by
  letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ W ↘ Spec (.of ℂ)⟩
  haveI : IsAffine V.toScheme := hV
  constructor
  intro y
  have e' : (⊤ : V.toScheme.Opens) ≤ (V.ι ≫ W ↘ Spec (.of ℂ)) ⁻¹ᵁ U := fun z _ ↦ e z.2
  refine ⟨U, hU, ⊤, isAffineOpen_top _, trivial, e', ?_⟩
  have e'' : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun z _ ↦ z.2
  change RingHom.IsStandardSmoothOfRelativeDimension n
    ((V.ι ≫ W ↘ Spec (.of ℂ)).appLE U ⊤ e').hom
  rw [← Scheme.Hom.appLE_comp_appLE V.ι (W ↘ Spec (.of ℂ)) U V ⊤ e e'']
  haveI : IsIso (V.ι.appLE V ⊤ e'') := by
    rw [Scheme.Opens.ι_appLE]
    have h1 : (homOfLE (Set.image_subset_iff.mpr e'') : V.ι ''ᵁ ⊤ ⟶ V) =
        eqToHom V.ι_image_top := Subsingleton.elim _ _
    rw [h1]
    exact (W.presheaf.mapIso (eqToIso V.ι_image_top).op).isIso_hom
  exact ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso
    (n := n)).cancel_right_isIso
    ((W ↘ Spec (.of ℂ)).appLE U V e) (V.ι.appLE V ⊤ e'')).2 hr

/-- A smooth quasi-projective complex threefold is smooth of relative dimension three. -/
private theorem smoothOfRelativeDimension_three {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (W ↘ Spec (.of ℂ))] [QuasiCompact (W ↘ Spec (.of ℂ))] [IsIntegral W]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ)))
    (hdim : topologicalKrullDim W = 3)
    (hWqp : Stacks.HProjective.IsQuasiProjective (W ↘ Spec (.of ℂ))) :
    SmoothOfRelativeDimension 3 (W ↘ Spec (.of ℂ)) := by
  haveI : IsSeparated (W ↘ Spec (.of ℂ)) := AlgebraicGeometry.IsQuasiProjective.isSeparated hWqp
  haveI : Smooth (W ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hst⟩ := Smooth.exists_isStandardSmooth (W ↘ Spec (.of ℂ)) x
  letI := ((W ↘ Spec (.of ℂ)).appLE U V e).hom.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hst.out
  have hr : RingHom.IsStandardSmoothOfRelativeDimension P.dimension
      ((W ↘ Spec (.of ℂ)).appLE U V e).hom := ⟨ι, σ, inferInstance, inferInstance, P, rfl⟩
  refine ⟨U, hU, V, hV, hx, e, ?_⟩
  suffices hr3 : P.dimension = 3 by rwa [← hr3]
  -- the open `V` as a scheme, smooth of relative dimension `P.dimension`
  letI : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ W ↘ Spec (.of ℂ)⟩
  haveI hVo : V.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  haveI : IsAffine V.toScheme := hV
  haveI : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ W ↘ Spec (.of ℂ)))
  haveI : QuasiCompact (V.toScheme ↘ Spec (.of ℂ)) :=
    (quasiCompact_iff_compactSpace _).mpr inferInstance
  haveI : IsSeparated (V.toScheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (IsSeparated (V.ι ≫ W ↘ Spec (.of ℂ)))
  haveI := smoothOfRelativeDimension_opens_of_appLE U hU V hV e hr
  -- a `ℂ`-point of `V`
  haveI : CompactSpace V.toScheme := inferInstance
  obtain ⟨y, -, hy⟩ := isClosed_univ.exists_closed_singleton
    (⟨⟨x, hx⟩, trivial⟩ : (Set.univ : Set V.toScheme).Nonempty)
  let p : UnderlyingSpace ℂ V.toScheme :=
    (UnderlyingSpace.equivClosedPoints V.toScheme).symm ⟨y, hy⟩
  have hp : p.toHom (IsLocalRing.closedPoint ℂ) = y := by
    rw [← UnderlyingSpace.equivClosedPoints_apply, Equiv.apply_symm_apply]
  have h1 := ringKrullDim_stalk_eq_of_smoothOfRelativeDimension P.dimension p
  have h2 := UnderlyingSpace.ringKrullDim_stalk_eq_dimension (UnderlyingSpace.map V.ι p)
  rw [UnderlyingSpace.toHom_map] at h2
  change ringKrullDim (W.presheaf.stalk (V.ι (p.toHom (IsLocalRing.closedPoint ℂ)))) = _ at h2
  rw [hp] at h1 h2
  have h3 : ringKrullDim (V.toScheme.presheaf.stalk y) =
      ringKrullDim (W.presheaf.stalk (V.ι y)) :=
    ringKrullDim_eq_of_ringEquiv (V.stalkIso y).commRingCatIsoToRingEquiv
  rw [h3, h2] at h1
  change topologicalKrullDim W = _ at h1
  rw [hdim] at h1
  exact_mod_cast h1.symm

/-- A smooth quasi-projective complex threefold is a complex scheme: it is a smooth variety,
closed in itself. -/
private theorem isComplexScheme_of_isSmoothScheme {W : Scheme.{0}} [W.Over (Spec (.of ℂ))]
    [IsIntegral W] (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ)))
    (hWqp : Stacks.HProjective.IsQuasiProjective (W ↘ Spec (.of ℂ))) : IsComplexScheme W := by
  haveI : LocallyOfFiniteType (W ↘ Spec (.of ℂ)) := hWqp.locallyOfFiniteType
  haveI : QuasiCompact (W ↘ Spec (.of ℂ)) := hWqp.quasiCompact
  haveI : IsSeparated (W ↘ Spec (.of ℂ)) := AlgebraicGeometry.IsQuasiProjective.isSeparated hWqp
  haveI : Smooth (W ↘ Spec (.of ℂ)) := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI : IsSmoothVariety ℂ (W ↘ Spec (.of ℂ)) := { }
  exact IsComplexScheme.of_isSmoothVariety W

/-- An integral scheme quasi-projective over `ℂ` is a quasi-projective variety. -/
private theorem isQuasiProjectiveVariety_of_isQuasiProjective {Y : Scheme.{0}}
    [Y.Over (Spec (.of ℂ))] [IsIntegral Y]
    (hYqp : Stacks.HProjective.IsQuasiProjective (Y ↘ Spec (.of ℂ))) :
    IsQuasiProjectiveVariety ℂ (Y ↘ Spec (.of ℂ)) :=
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYqp.locallyOfFiniteType
  haveI : QuasiCompact (Y ↘ Spec (.of ℂ)) := hYqp.quasiCompact
  haveI : IsSeparated (Y ↘ Spec (.of ℂ)) := AlgebraicGeometry.IsQuasiProjective.isSeparated hYqp
  haveI : AlgebraicGeometry.IsVariety ℂ (Y ↘ Spec (.of ℂ)) := {}
  ⟨hYqp⟩

/-- A dominant morphism of complex threefolds has finite nonzero residue degree at the generic
point. -/
private theorem residueDegree_genericPoint_ne_zero {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [IsIntegral X] [IsIntegral Y] (hXd : topologicalKrullDim X = 3)
    (hXqp : Stacks.HProjective.IsQuasiProjective (X ↘ Spec (.of ℂ)))
    (hYd : topologicalKrullDim Y = 3)
    (hYqp : Stacks.HProjective.IsQuasiProjective (Y ↘ Spec (.of ℂ)))
    (g : X ⟶ Y) [g.IsOver (Spec (.of ℂ))] [LocallyOfFiniteType g] [IsDominant g] :
    g.residueDegree (genericPoint X) ≠ 0 := by
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := hXqp.locallyOfFiniteType
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYqp.locallyOfFiniteType
  have hδ : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (g ≫ (Y ↘ Spec (.of ℂ))) (genericPoint X) =
      Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
        (Y ↘ Spec (.of ℂ)) (g.base (genericPoint X)) := by
    rw [comp_over, map_genericPoint_of_isDominant,
      MMP.Chow.relativeDimension_genericPoint_eq ℂ (X ↘ Spec (.of ℂ)) (n := 3)
        (by exact_mod_cast hXd),
      MMP.Chow.relativeDimension_genericPoint_eq ℂ (Y ↘ Spec (.of ℂ)) (n := 3)
        (by exact_mod_cast hYd)]
  have := Stacks.Chow.finiteDimensional_residueField_of_relativeDimension_eq
    (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction (Y ↘ Spec (.of ℂ)) g (genericPoint X) hδ
  letI := (g.residueFieldMap (genericPoint X)).hom.toAlgebra
  exact (Module.finrank_pos (R := Y.residueField (g.base (genericPoint X)))
    (M := X.residueField (genericPoint X))).ne'

/-- **Descent along a proper dominant morphism.** For a proper dominant morphism
`g : X ⟶ Y` of smooth quasi-projective complex threefolds and a closed `Z ⊆ Y` proper over `ℂ`,
if restriction `H³_{g⁻¹Z}(X) → H³(g⁻¹Z)` is injective then so is `H³_Z(Y) → H³(Z)`. -/
private theorem restrictInj_of_isBirationalMorphism {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))]
    [Y.Over (Spec (.of ℂ))] [IsIntegral X] [IsIntegral Y]
    (hXs : IsSmoothScheme (X ↘ Spec (.of ℂ))) (hXd : topologicalKrullDim X = 3)
    (hXqp : Stacks.HProjective.IsQuasiProjective (X ↘ Spec (.of ℂ)))
    (hYs : IsSmoothScheme (Y ↘ Spec (.of ℂ))) (hYd : topologicalKrullDim Y = 3)
    (hYqp : Stacks.HProjective.IsQuasiProjective (Y ↘ Spec (.of ℂ)))
    (g : X ⟶ Y) [g.IsOver (Spec (.of ℂ))] [IsProper g] [IsDominant g]
    (Z : TopologicalSpace.Closeds Y)
    (hZ : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫ (Y ↘ Spec (.of ℂ))))
    (h : RestrictInj (TopCat.of (UnderlyingSpace ℂ X))
      (UnderlyingSpace.pointsOver (K := ℂ) (g.base ⁻¹' (Z : Set Y))) 3) :
    RestrictInj (TopCat.of (UnderlyingSpace ℂ Y)) (UnderlyingSpace.pointsOver (K := ℂ) (Z : Set Y))
      3 := by
  classical
  haveI : IsComplexScheme X := isComplexScheme_of_isSmoothScheme hXs hXqp
  haveI : IsComplexScheme Y := isComplexScheme_of_isSmoothScheme hYs hYqp
  haveI := smoothOfRelativeDimension_three hXs hXd hXqp
  haveI := smoothOfRelativeDimension_three hYs hYd hYqp
  haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := hXqp.locallyOfFiniteType
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYqp.locallyOfFiniteType
  have hηX := MMP.Chow.relativeDimension_genericPoint_eq ℂ (X ↘ Spec (.of ℂ)) (n := 3)
    (by exact_mod_cast hXd)
  have hηY := MMP.Chow.relativeDimension_genericPoint_eq ℂ (Y ↘ Spec (.of ℂ)) (n := 3)
    (by exact_mod_cast hYd)
  have hδ' : Stacks.Chow.relativeDimension (Stacks.Chow.fieldChowSituation ℂ).dimensionFunction
      (Y ↘ Spec (.of ℂ)) (g.base (genericPoint X)) = 3 := by
    rwa [map_genericPoint_of_isDominant]
  -- the classes `[X]` and `[Y]` of the generic points
  let μX : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ X))
      (2 * 3 : ℕ) := MMP.Chow.pointCycleClass ℚ (genericPoint X) hηX
  let μY : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Y))
      (2 * 3 : ℕ) := MMP.Chow.pointCycleClass ℚ (g.base (genericPoint X)) hδ'
  have hμY : MMP.Chow.pointCycleClass ℚ (genericPoint Y) hηY = μY := by
    have hcongr : ∀ {p q : Y} (_ : p = q) hp hq,
        MMP.Chow.pointCycleClass ℚ (k := 3) p hp = MMP.Chow.pointCycleClass ℚ q hq := by
      rintro p q rfl hp hq; rfl
    exact hcongr (by rw [map_genericPoint_of_isDominant]) _ _
  -- `g_* [X] = d [Y]` with `d ≥ 1`
  have hrd := residueDegree_genericPoint_ne_zero hXd hXqp hYd hYqp g
  have hpush : (borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g))
        (UnderlyingSpace.isProperMap_map (K := ℂ) g) ((2 * 3 : ℕ) : ℤ)).hom μX =
      ((g.residueDegree (genericPoint X) : ℕ) : ℚ) • μY := by
    have e := MMP.Chow.pushforward_pointCycleClass ℚ g (genericPoint X) hηX
    rw [MMP.Chow.pointCycleClassOrZero] at e
    rw [← Int.cast_natCast (R := ℚ) (g.residueDegree (genericPoint X)), Int.cast_smul_eq_zsmul]
    split_ifs at e with h
    · exact e
    · exact absurd (by exact_mod_cast hδ') h
  -- duality
  have hZc : IsClosed (UnderlyingSpace.pointsOver (K := ℂ) (Z : Set Y)) :=
    UnderlyingSpace.isClosed_pointsOver Z.isClosed
  have hZd := UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver Y Z
  have hZ'd : HasProperNeighbourhoodDeformations
      ((TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g)) ⁻¹'
        UnderlyingSpace.pointsOver (K := ℂ) (Z : Set Y)) :=
    UnderlyingSpace.hasProperNeighbourhoodDeformations_pointsOver X
      ⟨g.base ⁻¹' Z, Z.isClosed.preimage g.base.hom.continuous⟩
  have hD := (bijective_dualityMap_of_isQuasiProjectiveVariety
    (isQuasiProjectiveVariety_of_isQuasiProjective hYqp)
    (μ := μY) hμY Z hZ 3).1.1
  refine restrictInj_of_preimage (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g)) _ 3 ?_ h
  rw [injective_iff_map_eq_zero]
  intro c hc
  apply hD
  rw [map_zero, borelMooreHomology.dualityMap_apply]
  have hc' : (cohomologyWithSupports.pullback ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g))
      (UnderlyingSpace.pointsOver (K := ℂ) (Z : Set Y)) (((2 * 3 : ℕ) : ℤ) - 3)).hom c = 0 := hc
  have key : borelMooreHomology.capProductSupport ℚ (TopCat.of (UnderlyingSpace ℂ Y)) hZc hZd
      (((2 * 3 : ℕ) : ℤ) - 3) ((2 * 3 : ℕ) : ℤ) c
      ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ)
        (TopCat.ofHom (UnderlyingSpace.map (K := ℂ) g))
        (UnderlyingSpace.isProperMap_map (K := ℂ) g) ((2 * 3 : ℕ) : ℤ)).hom μX) = 0 := by
    rw [← borelMooreHomology.pushforward_restrictPreimage_capProductSupportPullback ℚ _
      (UnderlyingSpace.isProperMap_map (K := ℂ) g) hZc hZd hZ'd (((2 * 3 : ℕ) : ℤ) - 3)
      ((2 * 3 : ℕ) : ℤ) c μX,
      borelMooreHomology.capProductSupportPullback_apply, hc', map_zero, LinearMap.zero_apply,
      map_zero]
  rw [hpush, map_smul] at key
  rw [(smul_eq_zero.1 key).resolve_left (by exact_mod_cast hrd), map_zero]

/-- At a closed point `y` of a smooth quasi-projective complex threefold, `H³_y(Y) = 0`. -/
private theorem restrictInj_pointsOver_singleton {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))]
    [IsIntegral Y] (hYs : IsSmoothScheme (Y ↘ Spec (.of ℂ))) (hYd : topologicalKrullDim Y = 3)
    (hYqp : Stacks.HProjective.IsQuasiProjective (Y ↘ Spec (.of ℂ))) (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    RestrictInj (TopCat.of (UnderlyingSpace ℂ Y)) (UnderlyingSpace.pointsOver (K := ℂ) {y}) 3 := by
  classical
  haveI : IsComplexScheme Y := isComplexScheme_of_isSmoothScheme hYs hYqp
  haveI := smoothOfRelativeDimension_three hYs hYd hYqp
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYqp.locallyOfFiniteType
  let μY : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ) (TopCat.of (UnderlyingSpace ℂ Y))
      (2 * 3 : ℕ) := MMP.Chow.pointCycleClass ℚ (genericPoint Y)
    (MMP.Chow.relativeDimension_genericPoint_eq ℂ (Y ↘ Spec (.of ℂ)) (n := 3)
      (by exact_mod_cast hYd))
  let Z : TopologicalSpace.Closeds Y := ⟨{y}, hy⟩
  set I := Scheme.IdealSheafData.vanishingIdeal Z
  have hrange : Set.range I.subschemeι = {y} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  haveI : LocallyOfFiniteType (Y ↘ Spec (.of ℂ)) := hYqp.locallyOfFiniteType
  have hZ : IsProper (I.subschemeι ≫ (Y ↘ Spec (.of ℂ))) :=
    MMP.Mori.isProper_comp_of_range_subset_singleton (Y ↘ Spec (.of ℂ)) I.subschemeι hy
      hrange.subset
  have hD := (bijective_dualityMap_of_isQuasiProjectiveVariety
    (isQuasiProjectiveVariety_of_isQuasiProjective hYqp)
    (μ := μY) rfl Z hZ 3).1.1
  -- `H₃` of the point vanishes
  haveI : IsComplexScheme I.subscheme := IsComplexScheme.of_isClosedImmersion I.subschemeι
  haveI : Subsingleton I.subscheme := ⟨fun a b ↦ I.subschemeι.isClosedEmbedding.injective (by
    have ha : I.subschemeι a ∈ Set.range I.subschemeι := ⟨a, rfl⟩
    have hb : I.subschemeι b ∈ Set.range I.subschemeι := ⟨b, rfl⟩
    rw [hrange] at ha hb
    exact ha.trans hb.symm)⟩
  haveI : DiscreteTopology I.subscheme := Subsingleton.discreteTopology
  have hdim0 : topologicalKrullDim I.subscheme < ((1 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_zero_of_discreteTopology I.subscheme).trans_lt (by norm_num)
  have hZ0 := IsComplexScheme.isZero_borelMooreHomology_of_dimension_lt ℚ I.subscheme hdim0
    (j := 3) (by norm_num)
  haveI := ModuleCat.isZero_iff_subsingleton.1 hZ0
  have he := UnderlyingSpace.isClosedEmbedding_map_of_isClosedImmersion (K := ℂ) I.subschemeι
  have hr : Set.range (UnderlyingSpace.map (K := ℂ) I.subschemeι) =
      UnderlyingSpace.pointsOver (K := ℂ) (Z : Set Y) := by
    rw [UnderlyingSpace.range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let e := he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)
  let E : TopCat.of (UnderlyingSpace ℂ I.subscheme) ⟶
      TopCat.of (UnderlyingSpace.pointsOver (K := ℂ) (Z : Set Y)) := TopCat.ofHom ⟨e, e.continuous⟩
  let E' : TopCat.of (UnderlyingSpace.pointsOver (K := ℂ) (Z : Set Y)) ⟶
      TopCat.of (UnderlyingSpace ℂ I.subscheme) := TopCat.ofHom ⟨e.symm, e.symm.continuous⟩
  have hEE : E' ≫ E = 𝟙 _ := TopCat.ext fun p ↦ e.apply_symm_apply p
  have hBM : ∀ b : borelMooreHomology ℚ (ModuleCat.of ℚ ℚ)
      (TopCat.of (UnderlyingSpace.pointsOver (K := ℂ) (Z : Set Y))) 3, b = 0 := by
    intro b
    rw [← borelMooreHomology.pushforward_id_apply' ℚ (E' ≫ E) (by rw [hEE]; exact isProperMap_id)
      hEE 3 b, ← borelMooreHomology.pushforward_comp_apply ℚ E' E e.symm.isProperMap
      e.isProperMap _ 3 b]
    rw [Subsingleton.elim ((borelMooreHomology.pushforward ℚ (ModuleCat.of ℚ ℚ) E'
      e.symm.isProperMap 3).hom b) 0, map_zero]
  intro c _
  exact hD ((hBM _).trans (hBM _).symm)

/-- For the antiample snc model `f : W ⟶ S` the restriction `H³_E(W) → H³(E)` to the fibre
`E = f⁻¹(x)` is injective. -/
private theorem restrictInj_of_isRelativelyAmple {W S : Scheme.{0}}
    [W.Over (Spec (.of ℂ))] [S.Over (Spec (.of ℂ))]
    [IsLocallyNoetherian W] [IsNormal W] [IsNormal S] [IsIntegral W] [IsIntegral S]
    (hsm : IsSmoothScheme (W ↘ Spec (.of ℂ))) (hdim : topologicalKrullDim W = 3)
    (hWqp : Stacks.HProjective.IsQuasiProjective (W ↘ Spec (.of ℂ)))
    (hSdim : topologicalKrullDim S = 3)
    (hSqp : Stacks.HProjective.IsQuasiProjective (S ↘ Spec (.of ℂ)))
    (f : W ⟶ S) [f.IsOver (Spec (.of ℂ))] (hf : IsProjectiveMorphism f)
    (x : S) (hx : IsClosed {x})
    (hiso : IsIso (f ∣_ ⟨{x}ᶜ, hx.isOpen_compl⟩))
    (D : Divisor W) (hD : ∀ P, 0 ≤ D.coeff P) (hsnc : D.IsSNC (W ↘ Spec (.of ℂ)))
    (hfibre : (D.supp : Set W) = f.base ⁻¹' {x})
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hample : IsRelativelyAmple f (-D).divisorialSheaf) :
    RestrictInj (TopCat.of (UnderlyingSpace ℂ W))
      (UnderlyingSpace.pointsOver (K := ℂ) (f.base ⁻¹' {x})) 3 := by
  haveI : IsComplexScheme W := isComplexScheme_of_isSmoothScheme hsm hWqp
  have hb := bijective_toCohomology_comp_rationalCohomologyMap_three hsm hdim hWqp hSdim hSqp f
    hf x hx hiso D hD hsnc hfibre hample
  set ι := D.suppIdeal.subschemeι
  have hEc : Set.range (UnderlyingSpace.map (K := ℂ) ι) =
      UnderlyingSpace.pointsOver (K := ℂ) (D.supp : Set W) := by
    have hsupp : (D.suppIdeal.support : Set W) = D.supp :=
      Scheme.IdealSheafData.coe_support_vanishingIdeal _
    rw [UnderlyingSpace.range_map_of_isClosedImmersion, Scheme.IdealSheafData.range_subschemeι,
      hsupp]
  have h1 : RestrictInj (TopCat.of (UnderlyingSpace ℂ W))
      (Set.range (UnderlyingSpace.map (K := ℂ) ι)) 3 := by
    intro c hc
    apply hb.1
    rw [map_zero]
    let e : TopCat.of (UnderlyingSpace ℂ D.suppIdeal.subscheme) ⟶
        TopCat.of (Set.range (UnderlyingSpace.map (K := ℂ) ι)) :=
      TopCat.ofHom ⟨Set.rangeFactorization _,
        (UnderlyingSpace.map (K := ℂ) ι).continuous.subtype_mk _⟩
    have hfac : TopCat.ofHom (UnderlyingSpace.map (K := ℂ) ι) =
        e ≫ subspaceInclusion (TopCat.of (UnderlyingSpace ℂ W))
          (Set.range (UnderlyingSpace.map (K := ℂ) ι)) := rfl
    rw [ModuleCat.comp_apply, hfac, rationalCohomologyMap_comp, ModuleCat.comp_apply]
    erw [hc]
    exact map_zero _
  rwa [hEc, hfibre] at h1

end Duality

/-! ### The open subscheme over `U` -/

section Geometry

/-- `Spec ℂ` carries an ample invertible sheaf. -/
private lemma exists_isAmple_spec_complex :
    ∃ (M : (Spec (.of ℂ)).Modules) (hM : Stacks.Ample.IsInvertibleModule _ M),
      letI : Stacks.Ample.IsInvertibleModule _ M := hM
      Stacks.Ample.IsAmple _ M :=
  ⟨_, inferInstance, Stacks.Ample.isAmple_unitModule_of_isAffine _⟩

/-- An integral open subscheme of a complex variety, quasi-projective over `ℂ`, is a
quasi-projective variety. -/
private theorem isQuasiProjectiveVariety_ι_comp {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hXv : AlgebraicGeometry.IsVariety ℂ sX) (hXqp : Stacks.HProjective.IsQuasiProjective sX)
    (O : X.Opens) [IsIntegral O.toScheme]
    (hOqp : Stacks.HProjective.IsQuasiProjective (O.ι ≫ sX)) :
    IsQuasiProjectiveVariety ℂ (O.ι ≫ sX) := by
  haveI : LocallyOfFiniteType sX := hXqp.locallyOfFiniteType
  haveI : QuasiCompact sX := hXqp.quasiCompact
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsSeparated sX := hXv.toIsSeparated
  haveI : IsNoetherian X := ⟨⟩
  haveI : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (O : Set X))
  exact (isQuasiProjectiveVariety_iff ℂ _).2 ⟨{}, hOqp⟩

/-- A non-empty open subscheme of a quasi-projective complex threefold is an integral
quasi-projective complex threefold. -/
private theorem opens_props {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    (hXv : AlgebraicGeometry.IsVariety ℂ sX) (hXd : topologicalKrullDim X = 3)
    (hXqp : Stacks.HProjective.IsQuasiProjective sX) (O : X.Opens) (hO : (O : Set X).Nonempty) :
    IsIntegral O.toScheme ∧ topologicalKrullDim O.toScheme = 3 ∧
      Stacks.HProjective.IsQuasiProjective (O.ι ≫ sX) := by
  haveI : IsIntegral X := hXv.toIsIntegral
  haveI : LocallyOfFiniteType sX := hXqp.locallyOfFiniteType
  haveI : QuasiCompact sX := hXqp.quasiCompact
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : IsNoetherian X := ⟨⟩
  haveI : Nonempty O := ⟨⟨hO.some, hO.some_mem⟩⟩
  refine ⟨isIntegral_of_isOpenImmersion O.ι, ?_, ?_⟩
  · letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
    haveI : LocallyOfFiniteType (X ↘ Spec (.of ℂ)) := ‹LocallyOfFiniteType sX›
    exact (AlgebraicGeometry.topologicalKrullDim_eq_of_isOpen ℂ _ (_ ↘ Spec (.of ℂ)) _
      (TopologicalSpace.Opens.isOpen O) hO).symm.trans hXd
  · haveI : IsQuasiAffineHom O.ι := ⟨fun W hW ↦ by
      haveI : IsAffine W.toScheme := hW
      haveI : TopologicalSpace.NoetherianSpace O.toScheme :=
        TopologicalSpace.NoetherianSpace.set (O : Set X)
      haveI : CompactSpace (O.ι ⁻¹ᵁ W).toScheme := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact ((O.ι ⁻¹ᵁ W : O.toScheme.Opens) :
          Set O.toScheme))
      exact Scheme.IsQuasiAffine.of_isImmersion (O.ι ∣_ W)⟩
    exact isQuasiProjective_comp_of_exists_isAmple O.ι sX exists_isAmple_spec_complex
      (Stacks.HProjective.isQuasiProjective_of_isQuasiAffineHom O.ι inferInstance) hXqp

/-- An open subscheme inside the smooth locus is smooth. -/
private theorem isSmoothScheme_ι_comp {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (O : X.Opens) (hO : O ≤ smoothLocus sX) :
    IsSmoothScheme (O.ι ≫ sX) := by
  rw [isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  rw [smoothLocus_eq_smoothLocus] at hO
  exact eq_top_iff.2 fun z _ ↦ hO z.2

/-- A quasi-affine scheme which is universally closed over an affine scheme is affine. -/
private theorem isAffine_of_isQuasiAffine_of_universallyClosed {X Y : Scheme.{0}} (g : X ⟶ Y)
    [X.IsQuasiAffine] [IsAffine Y] [UniversallyClosed g] : IsAffine X := by
  have hfac : X.toSpecΓ ≫ (Spec.map g.appTop ≫ Y.isoSpec.inv) = g := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
  have : UniversallyClosed (X.toSpecΓ ≫ (Spec.map g.appTop ≫ Y.isoSpec.inv)) := by
    rw [hfac]; infer_instance
  have : UniversallyClosed X.toSpecΓ :=
    UniversallyClosed.of_comp_of_isSeparated _ (Spec.map g.appTop ≫ Y.isoSpec.inv)
  have : IsClosedImmersion X.toSpecΓ :=
    IsClosedImmersion.of_isPreimmersion _ X.toSpecΓ.isClosedMap.isClosed_range
  exact isAffine_of_isAffineHom X.toSpecΓ

/-- Relative ampleness from ampleness over the whole base. -/
private theorem isRelativelyAmple_of_isAmpleOver_top {X Y : Scheme.{0}} (f : X ⟶ Y)
    [QuasiCompact f] (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (h : MMP.Mori.IsAmpleOver f L ⊤) : MMP.Mori.IsRelativelyAmple f L := by
  have hS := Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple (f ∣_ ⊤) _
    inferInstance h
  haveI : IsIso (f ⁻¹ᵁ ⊤).ι := by
    change IsIso (⊤ : X.Opens).ι
    exact (Scheme.topIso X).isIso_hom
  haveI : IsIso (⊤ : Y.Opens).ι := (Scheme.topIso Y).isIso_hom
  have hsq : IsPullback (inv (f ⁻¹ᵁ ⊤).ι) f (f ∣_ ⊤) (inv (⊤ : Y.Opens).ι) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.eq_comp_inv, Category.assoc, morphismRestrict_ι, IsIso.inv_hom_id_assoc]⟩
  have h2 := Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback hsq _ hS
  exact MMP.Mori.IsRelativelyAmple.of_stacks f L
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _
      (Stacks.AmpleThickeningDevissage.pullbackModuleInvIso (f ⁻¹ᵁ ⊤).ι L)).mp h2)

/-- **A proper birational morphism with a relatively ample divisor is an isomorphism away from
its support.** If `-D` is `f`-ample and `O` misses the image of `Supp D`, then `f` is an
isomorphism over `O`: over an affine `A ⊆ O` the preimage carries the ample trivial bundle, so it
is quasi-affine, hence affine, so `f` is finite over `A` and birational onto a normal base. -/
private theorem isIso_morphismRestrict_of_isRelativelyAmple {W Y : Scheme.{0}} [IsIntegral W]
    [IsIntegral Y] [IsNormal Y] [CompactSpace W] [IsLocallyNoetherian W] [IsNormal W]
    (f : W ⟶ Y) [IsProper f] (hf : IsBirational f) (D : Divisor W)
    [Stacks.Ample.IsInvertibleModule W (-D).divisorialSheaf]
    (hamp : MMP.Mori.IsRelativelyAmple f (-D).divisorialSheaf) (O : Y.Opens)
    (hO : ∀ P : MMP.Mori.PrimeDivisor W, D.coeff P ≠ 0 → ∀ w ∈ P.support, f w ∉ O) :
    IsIso (f ∣_ O) := by
  have hS := Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
    inferInstance hamp
  change MMP.Mori.IsBiregular f O
  rw [MMP.Mori.isBiregular_iff_le_biregularLocus]
  intro y hy
  obtain ⟨A, hA, hyA, hAO⟩ := exists_isAffineOpen_mem_and_subset hy
  have hloc : (-D).IsLocalEquation (f ⁻¹ᵁ A) 1 := by
    rintro E ⟨w, hwE, hwA⟩
    have h0 : D.coeff E = 0 := by
      by_contra h
      exact hO E h w hwE (hAO hwA)
    rw [DivisorWithCoeffs.coeff_neg, h0, neg_zero]
    simp
  have e := MMP.Threefold.Resolution.modulePullbackIsoRestrict' (f ⁻¹ᵁ A) (-D).divisorialSheaf ≪≫
    hloc.restrictDivisorialSheafIso
  haveI : (f ⁻¹ᵁ A).toScheme.IsQuasiAffine :=
    (Stacks.RelativeVeryAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule _ _ e).mpr
      (hS.isAmple_preimage f _ A hA)
  haveI : IsAffine A.toScheme := hA
  haveI : IsAffine (f ⁻¹ᵁ A).toScheme := isAffine_of_isQuasiAffine_of_universallyClosed (f ∣_ A)
  haveI : IsIntegralHom (f ∣_ A) :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  haveI : Nonempty A := ⟨⟨y, hyA⟩⟩
  haveI : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion A.ι
  haveI : IsNormal A.toScheme := isNormal_of_flat_preimmersion A.ι
  haveI : Nonempty (f ⁻¹ᵁ A) := by
    have hηX : genericPoint W ∈ genericPoints W := by simp [genericPoints_eq_singleton]
    have heq : f (genericPoint W) = genericPoint Y := by
      simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hf.bijOn.1 hηX
    refine ⟨⟨genericPoint W, ?_⟩⟩
    change f (genericPoint W) ∈ A
    rw [heq]
    exact ((genericPoint_spec Y).mem_open_set_iff A.isOpen).2 ⟨y, Set.mem_univ _, hyA⟩
  haveI : IsIntegral (f ⁻¹ᵁ A).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ A).ι
  haveI : IsIso (f ∣_ A) :=
    isIso_of_isIntegralHom_of_isBirational_of_isNormal _ (birational_morphismRestrict f hf A)
  exact MMP.Mori.le_biregularLocus (show MMP.Mori.IsBiregular f A from
    (inferInstance : IsIso (f ∣_ A))) hyA

/-- In a scheme of positive dimension, the complement of a point is non-empty. -/
private theorem nonempty_compl_singleton_of_topologicalKrullDim_pos {X : Scheme.{0}} (x : X)
    (hX : 0 < topologicalKrullDim X) : ({x}ᶜ : Set X).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hne
  haveI : Subsingleton X := ⟨fun a b ↦ by
    have ha : a ∈ ({x} : Set X) := hne ▸ Set.mem_univ a
    have hb : b ∈ ({x} : Set X) := hne ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]⟩
  haveI : DiscreteTopology X := Subsingleton.discreteTopology
  exact hX.not_ge (topologicalKrullDim_zero_of_discreteTopology X)

/-- If `r ≫ g` is dominant and the dominant `g` is an isomorphism over a non-empty open, then `r`
is dominant. -/
private theorem isDominant_of_isIso_morphismRestrict {W Y U : Scheme.{0}} [IsIntegral W]
    [IsIntegral Y] [IsIntegral U] (r : W ⟶ Y) (g : Y ⟶ U) [IsDominant (r ≫ g)] [IsDominant g]
    (V : U.Opens) (hV : (V : Set U).Nonempty) [IsIso (g ∣_ V)] : IsDominant r := by
  have h1 : (r ≫ g).base (genericPoint W) = genericPoint U := map_genericPoint_of_isDominant _
  have h2 : g.base (genericPoint Y) = genericPoint U := map_genericPoint_of_isDominant _
  obtain ⟨v, hv⟩ := hV
  have hηV : genericPoint U ∈ V :=
    ((genericPoint_spec U).mem_open_set_iff V.isOpen).2 ⟨v, Set.mem_univ _, hv⟩
  have h3 : r.base (genericPoint W) = genericPoint Y :=
    MMP.Resolution.Bridges.subsingleton_preimage_of_isIso_morphismRestrict g V hηV
      (show r.base (genericPoint W) ∈ g.base ⁻¹' {genericPoint U} from h1) h2
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  refine Set.eq_univ_of_univ_subset ?_
  rw [← genericPoint_spec Y]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, h3⟩)

/-- The reduced fibre of a proper morphism `g : X ⟶ Y` over a closed point of `Y` is proper over
`ℂ`. -/
private theorem isProper_subschemeι_preimage_singleton {X Y : Scheme.{0}}
    (sX : X ⟶ Spec (.of ℂ)) (sY : Y ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sY] (g : X ⟶ Y)
    [IsProper g] (hgs : g ≫ sY = sX) {y : Y} (hy : IsClosed ({y} : Set Y)) :
    IsProper ((Scheme.IdealSheafData.vanishingIdeal
      (⟨g.base ⁻¹' {y}, hy.preimage g.base.hom.continuous⟩ :
        TopologicalSpace.Closeds X)).subschemeι ≫ sX) := by
  set I := Scheme.IdealSheafData.vanishingIdeal
    (⟨g.base ⁻¹' {y}, hy.preimage g.base.hom.continuous⟩ : TopologicalSpace.Closeds X)
  have hg : Set.range (I.subschemeι ≫ g) ⊆ {y} := by
    rintro _ ⟨z, rfl⟩
    have hz : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal] at hz
  haveI : IsReduced I.subscheme := by
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance
  have := MMP.Mori.isProper_comp_of_range_subset_singleton sY (I.subschemeι ≫ g) hy hg
  rwa [Category.assoc, hgs] at this

/-- **The fibre over the singular point of a resolved threefold.** Let `g : X ⟶ Y` be a
resolution of a normal quasi-projective complex threefold whose singular locus is the closed point
`y`, biregular off `y`. Then restriction `H³_E(X) → H³(E)` to the fibre `E = g⁻¹(y)` is
injective. -/
private theorem restrictInj_preimage_of_isResolution {X Y : Scheme.{0}} [IsNormal Y]
    [IsIntegral X] [IsIntegral Y] (sY : Y ⟶ Spec (.of ℂ)) [AlgebraicGeometry.IsVariety ℂ sY]
    (hY : IsQuasiProjectiveVariety ℂ sY) (hYd : topologicalKrullDim Y = 3)
    (hYqp : Stacks.HProjective.IsQuasiProjective sY)
    (sX : X ⟶ Spec (.of ℂ)) (hXs : IsSmoothScheme sX) (hXd : topologicalKrullDim X = 3)
    (hXqp : Stacks.HProjective.IsQuasiProjective sX)
    (g : X ⟶ Y) (hgs : g ≫ sY = sX) (hres : MMP.Intersection.IsResolution sY g)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hsing : (singularLocus sY : Set Y) ∩ ((⊤ : Y.Opens) : Set Y) = {y})
    (hbir : ((⊤ : Y.Opens) : Set Y) \ {y} ⊆ MMP.Mori.biregularLocus g)
    (V : Y.Opens) (hV : (V : Set Y).Nonempty) [IsIso (g ∣_ V)] :
    letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
    RestrictInj (TopCat.of (UnderlyingSpace ℂ X))
      (UnderlyingSpace.pointsOver (K := ℂ) (g.base ⁻¹' {y})) 3 := by
  classical
  letI : X.Over (Spec (.of ℂ)) := ⟨sX⟩
  letI : Y.Over (Spec (.of ℂ)) := ⟨sY⟩
  haveI : LocallyOfFiniteType sY := hYqp.locallyOfFiniteType
  obtain ⟨W, _, _, _, r, hres', hqp', -, E, -, hEsnc, hEsupp, -, D, hDpos, hDzero, hc,
    hamp⟩ := MMP.Threefold.exists_isResolution_comp_isSNC_isAmpleOver_neg_and_subset_biregularLocus
      hY hYd hres y ⊤ trivial hsing hbir
  obtain ⟨-, -, -, hgproj, hgbir⟩ := hres
  haveI : IsProper g := isProper_of_isProjectiveMorphism _ hgproj
  obtain ⟨-, hWvar, hWsm, hfproj, hfbir⟩ := hres'
  haveI : IsIntegral W := hWvar.toIsIntegral
  letI : W.Over (Spec (.of ℂ)) := ⟨r ≫ sX⟩
  have hWeq : (r ≫ g) ≫ sY = r ≫ sX := by rw [Category.assoc, hgs]
  have hWeq' : r ≫ g ≫ sY = r ≫ sX := by rw [hgs]
  haveI : (r ≫ g).IsOver (Spec (.of ℂ)) := ⟨hWeq⟩
  haveI : r.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have hWs : IsSmoothScheme (W ↘ Spec (.of ℂ)) := by
    change IsSmoothScheme (r ≫ sX)
    rwa [← hWeq]
  have hWd : topologicalKrullDim W = 3 := by
    haveI := hWvar
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sY
      ((r ≫ g) ≫ sY) hfbir]
    exact hYd
  have hWqp : Stacks.HProjective.IsQuasiProjective (W ↘ Spec (.of ℂ)) := by
    change Stacks.HProjective.IsQuasiProjective (r ≫ sX)
    rw [← hWeq']
    exact hqp'.isQuasiProjective
  haveI : IsProper (r ≫ g) := isProper_of_isProjectiveMorphism _ hfproj
  haveI := hc.isInvertibleModule_divisorialSheaf
  have hamp' : MMP.Mori.IsRelativelyAmple (r ≫ g) (-D).divisorialSheaf :=
    isRelativelyAmple_of_isAmpleOver_top _ _ hamp
  have hsupp : D.support = E.support := by
    ext P
    exact ⟨fun h ↦ by_contra fun hP ↦ Finsupp.mem_support_iff.1 h (hDzero P hP),
      fun h ↦ Finsupp.mem_support_iff.2 (hDpos P h).ne'⟩
  have hDsupp : (D.supp : Set W) = (r ≫ g).base ⁻¹' {y} := by
    have : D.supp = E.supp := by
      change D.support.sup _ = E.support.sup _
      rw [hsupp]
    rwa [this]
  have hD0 : ∀ P, 0 ≤ D.coeff P := fun P ↦
    if h : P ∈ E.support then (hDpos P h).le else (hDzero P h).ge
  have hDsnc : D.IsSNC (W ↘ Spec (.of ℂ)) := by
    have h := hEsnc.of_support_subset (D' := D) (hsupp ▸ subset_rfl)
    change DivisorWithCoeffs.IsSNC (r ≫ sX) D
    rwa [← hWeq']
  have hiso : IsIso ((r ≫ g) ∣_ ⟨{y}ᶜ, hy.isOpen_compl⟩) :=
    isIso_morphismRestrict_of_isRelativelyAmple (r ≫ g)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfbir) D hamp' _
      (fun P hP w hw ↦ by
        have hw' : w ∈ (D.supp : Set W) := DivisorWithCoeffs.support_subset_supp hP hw
        rw [hDsupp] at hw'
        exact fun h ↦ h hw')
  have hinj := restrictInj_of_isRelativelyAmple hWs hWd hWqp hYd hYqp (r ≫ g) hfproj y hy
    hiso D hD0 hDsnc hDsupp hamp'
  let Z : TopologicalSpace.Closeds X := ⟨g.base ⁻¹' {y}, hy.preimage g.base.hom.continuous⟩
  have hZ : IsProper ((Scheme.IdealSheafData.vanishingIdeal Z).subschemeι ≫
      (X ↘ Spec (.of ℂ))) := isProper_subschemeι_preimage_singleton sX sY g hgs hy
  haveI : IsProper r := IsProper.of_comp r g
  haveI : IsDominant (r ≫ g) := hfbir.isDominant
  haveI : IsDominant g := hgbir.isDominant
  haveI : IsDominant r := isDominant_of_isIso_morphismRestrict r g V hV
  exact restrictInj_of_isBirationalMorphism (X := W) (Y := X) hWs hWd hWqp hXs hXd hXqp r Z hZ
    hinj

/-- A point of an open subscheme `U` which is closed in the ambient scheme is closed in `U`. -/
private theorem isClosed_singleton_opens {X : Scheme.{0}} {U : X.Opens} (x : U.toScheme)
    (hx : IsClosed ({x.1} : Set X)) : IsClosed ({x} : Set U.toScheme) := by
  have : ({x} : Set U.toScheme) = U.ι.base ⁻¹' {x.1} := by
    ext z
    rw [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext h⟩
  rw [this]
  exact hx.preimage U.ι.base.hom.continuous

/-- If `f` is an isomorphism over `V ≤ U`, then `f ∣_ U` is an isomorphism over `U.ι ⁻¹ᵁ V`. -/
private theorem isIso_morphismRestrict_restrict {X Y : Scheme.{0}} (f : X ⟶ Y) {U V : Y.Opens}
    (hVU : V ≤ U) [IsIso (f ∣_ V)] : IsIso ((f ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := by
  have e := morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V)
  rw [show U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU] at e
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff e).2 (by
    change IsIso (f ∣_ V)
    infer_instance)

/-- A morphism of irreducible schemes which is an isomorphism over a non-empty open is a
birational morphism. -/
private theorem isBirationalMorphism_of_isIso_morphismRestrict {X Y : Scheme.{0}}
    [IrreducibleSpace X] [IrreducibleSpace Y] (g : X ⟶ Y) (V : Y.Opens)
    (hV : (V : Set Y).Nonempty) [IsIso (g ∣_ V)] : MMP.Mori.IsBirationalMorphism g := by
  haveI : IsIso (g.resLE V (g ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  obtain ⟨v, hv⟩ := hV
  exact MMP.Flips.isBirationalMorphism_of_isIso_resLE g (g ⁻¹ᵁ V) V
    ⟨_, ((inv (g ∣_ V)).base ⟨v, hv⟩).2⟩ ⟨v, hv⟩ le_rfl inferInstance

/-- If `U ∖ {x}` is smooth and the point `x` of `U` is singular, then the singular locus
of `U` is `{x}`. -/
private theorem singularLocus_inter_top_eq_singleton {S : Scheme.{0}} (sS : S ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sS] (U V : S.Opens) (x : U.toScheme)
    (hV : (V : Set S) = (U : Set S) \ {x.1}) (hsm : V ≤ smoothLocus sS)
    (hxs : x.1 ∉ smoothLocus sS) :
    (singularLocus (U.ι ≫ sS) : Set U.toScheme) ∩ ((⊤ : U.toScheme.Opens) : Set U.toScheme) =
      {x} := by
  have hsmU : ∀ z : U.toScheme, z ∈ smoothLocus (U.ι ≫ sS) ↔ U.ι z ∈ smoothLocus sS := by
    intro z
    rw [smoothLocus_eq_smoothLocus, smoothLocus_eq_smoothLocus,
      ← Scheme.Hom.preimage_smoothLocus_eq]
    rfl
  ext z
  rw [Set.mem_inter_iff, Set.mem_singleton_iff]
  change (z ∉ smoothLocus (U.ι ≫ sS) ∧ True) ↔ _
  rw [hsmU, and_true]
  refine ⟨fun h ↦ by_contra fun hz ↦ h (hsm ?_), by rintro rfl; exact hxs⟩
  change z.1 ∈ (V : Set S)
  rw [hV]
  exact ⟨z.2, fun h' ↦ hz (Subtype.ext h')⟩

/-- At a singular point `x`: restriction to the fibre over `x` is injective on `H³` with
supports, on `f₀⁻¹(U)`. -/
private theorem restrictInj_preimage_of_notMem_smoothLocus {S W₀ : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) [IsNormal S] (hSdim : topologicalKrullDim S = 3)
    (hSqp : Stacks.HProjective.IsQuasiProjective sS)
    (f₀ : W₀ ⟶ S) (hf₀ : MMP.Resolution.IsResolutionOfVariety sS f₀)
    (x : ComplexPoints sS) (U : S.Opens) (hxU : x.toScheme ∈ U)
    (V : S.Opens) (hV : (V : Set S) = (U : Set S) \ {x.toScheme})
    (hsm : V ≤ smoothLocus sS) (hbir : IsBiregular f₀ V) (hxs : x.toScheme ∉ smoothLocus sS) :
    letI : (f₀ ⁻¹ᵁ U).toScheme.Over (Spec (.of ℂ)) := ⟨(f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS⟩
    RestrictInj (TopCat.of (UnderlyingSpace ℂ (f₀ ⁻¹ᵁ U)))
      (UnderlyingSpace.pointsOver (K := ℂ) (((f₀ ⁻¹ᵁ U).ι ≫ f₀).base ⁻¹' {x.toScheme})) 3 := by
  classical
  letI : (f₀ ⁻¹ᵁ U).toScheme.Over (Spec (.of ℂ)) := ⟨(f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS⟩
  letI : U.toScheme.Over (Spec (.of ℂ)) := ⟨U.ι ≫ sS⟩
  have hSv := hf₀.isVariety
  have hWv := hf₀.isVariety_source
  haveI : IsIntegral S := hSv.toIsIntegral
  haveI : IsIntegral W₀ := hWv.toIsIntegral
  haveI : LocallyOfFiniteType sS := hSqp.locallyOfFiniteType
  haveI : QuasiCompact sS := hSqp.quasiCompact
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian sS
  haveI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace sS
  haveI : IsProper f₀ := hf₀.isProjective.isProper
  haveI : IsDominant f₀ := hf₀.isBirationalMorphism.isDominant
  have hWd : topologicalKrullDim W₀ = 3 := by
    haveI := hSv
    haveI := hWv
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sS (f₀ ≫ sS)
      hf₀.isBirationalMorphism]
    exact hSdim
  have hWqp : Stacks.HProjective.IsQuasiProjective (f₀ ≫ sS) :=
    isQuasiProjective_comp_of_exists_isAmple f₀ sS exists_isAmple_spec_complex
      (isQuasiProjective_of_isProjective hf₀.isProjective) hSqp
  haveI : LocallyOfFiniteType (f₀ ≫ sS) := hWqp.locallyOfFiniteType
  -- the point `x` of `U`
  let xU : U.toScheme := ⟨x.toScheme, hxU⟩
  have hxUc := isClosed_singleton_opens xU (isClosed_singleton_toScheme x)
  obtain ⟨w₀, hw₀⟩ := f₀.surjective x.toScheme
  obtain ⟨hUi, hUd, hUqp⟩ := opens_props sS hSv hSdim hSqp U ⟨_, hxU⟩
  obtain ⟨hW'i, hW'd, hW'qp⟩ := opens_props (f₀ ≫ sS) hWv hWd hWqp (f₀ ⁻¹ᵁ U)
    ⟨w₀, show f₀ w₀ ∈ U from hw₀ ▸ hxU⟩
  haveI := hUi
  haveI := hW'i
  haveI : IsNormal U.toScheme := isNormal_of_flat_preimmersion U.ι
  have hW's : IsSmoothScheme ((f₀ ⁻¹ᵁ U).toScheme ↘ Spec (.of ℂ)) :=
    isSmoothScheme_ι_comp (f₀ ≫ sS) (f₀ ⁻¹ᵁ U) (le_top.trans_eq hf₀.isSmoothScheme.symm)
  -- the restriction `g₀ : f₀⁻¹(U) ⟶ U`
  set g₀ := f₀ ∣_ U with hg₀
  have hg₀ι : g₀ ≫ U.ι = (f₀ ⁻¹ᵁ U).ι ≫ f₀ := morphismRestrict_ι f₀ U
  have hg₀s : g₀ ≫ U.ι ≫ sS = (f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS := by
    rw [← Category.assoc, hg₀ι, Category.assoc]
  -- `g₀` is an isomorphism over `V' = U ∖ {x}`
  let V' : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hVU : V ≤ U := fun z hz ↦ by
    have : z ∈ (V : Set S) := hz
    rw [hV] at this
    exact this.1
  haveI : IsIso (f₀ ∣_ V) := hbir
  haveI hV'iso : IsIso (g₀ ∣_ V') := isIso_morphismRestrict_restrict f₀ hVU
  have hV'set : (V' : Set U.toScheme) = {xU}ᶜ := by
    ext z
    change z.1 ∈ (V : Set S) ↔ _
    rw [hV, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun h hz ↦ h.2 (hz ▸ rfl), fun h ↦ ⟨z.2, fun hz ↦ h (Subtype.ext hz)⟩⟩
  have hV'ne : (V' : Set U.toScheme).Nonempty := by
    rw [hV'set]
    exact nonempty_compl_singleton_of_topologicalKrullDim_pos xU (by rw [hUd]; decide)
  have hg₀bir := isBirationalMorphism_of_isIso_morphismRestrict g₀ V' hV'ne
  have hsing := singularLocus_inter_top_eq_singleton sS U V xU hV hsm hxs
  have hbirU : ((⊤ : U.toScheme.Opens) : Set U.toScheme) \ {xU} ⊆
      MMP.Mori.biregularLocus g₀ := by
    intro z hz
    have hzV : z ∈ V' := by
      rw [← SetLike.mem_coe, hV'set]
      exact hz.2
    exact MMP.Mori.le_biregularLocus (show MMP.Mori.IsBiregular g₀ V' from hV'iso) hzV
  have hS := isQuasiProjectiveVariety_ι_comp sS hSv hSqp U hUqp
  have hW' := isQuasiProjectiveVariety_ι_comp (f₀ ≫ sS) hWv hWqp (f₀ ⁻¹ᵁ U) hW'qp
  rw [← hg₀s] at hW'
  haveI := hS
  haveI := hW'
  have hg₀proj : IsProjectiveMorphism g₀ :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety (g₀ ≫ U.ι ≫ sS) (U.ι ≫ sS)
      g₀ rfl
  have hres : MMP.Intersection.IsResolution (U.ι ≫ sS) g₀ :=
    ⟨((isQuasiProjectiveVariety_iff ℂ _).1 hS).1, ((isQuasiProjectiveVariety_iff ℂ _).1 hW').1,
      by rw [hg₀s]; exact hW's, hg₀proj, hg₀bir⟩
  have hdesc := restrictInj_preimage_of_isResolution (U.ι ≫ sS) hS hUd hUqp
    ((f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS) hW's hW'd hW'qp g₀ hg₀s hres xU hxUc hsing hbirU V' hV'ne
  have hset : ((f₀ ⁻¹ᵁ U).ι ≫ f₀).base ⁻¹' {x.toScheme} = g₀.base ⁻¹' {xU} := by
    ext w
    change ((f₀ ⁻¹ᵁ U).ι ≫ f₀).base w = x.toScheme ↔ g₀.base w = xU
    rw [← hg₀ι]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  exact hset ▸ hdesc

/-- At a smooth point `x`: restriction to `x` is injective on `H³_x(U)`, read on `𝟙⁻¹(U)`. -/
private theorem restrictInj_preimage_id_of_mem_smoothLocus {S : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) (hSv : AlgebraicGeometry.IsVariety ℂ sS)
    (hSdim : topologicalKrullDim S = 3) (hSqp : Stacks.HProjective.IsQuasiProjective sS)
    (x : ComplexPoints sS) (U : S.Opens) (hxU : x.toScheme ∈ U)
    (V : S.Opens) (hV : (V : Set S) = (U : Set S) \ {x.toScheme})
    (hsm : V ≤ smoothLocus sS) (hxs : x.toScheme ∈ smoothLocus sS) :
    letI : ((𝟙 S) ⁻¹ᵁ U).toScheme.Over (Spec (.of ℂ)) := ⟨((𝟙 S) ⁻¹ᵁ U).ι ≫ 𝟙 S ≫ sS⟩
    RestrictInj (TopCat.of (UnderlyingSpace ℂ ((𝟙 S) ⁻¹ᵁ U)))
      (UnderlyingSpace.pointsOver (K := ℂ) ((((𝟙 S) ⁻¹ᵁ U).ι ≫ 𝟙 S).base ⁻¹' {x.toScheme})) 3 := by
  classical
  letI : ((𝟙 S) ⁻¹ᵁ U).toScheme.Over (Spec (.of ℂ)) := ⟨((𝟙 S) ⁻¹ᵁ U).ι ≫ 𝟙 S ≫ sS⟩
  haveI : LocallyOfFiniteType sS := hSqp.locallyOfFiniteType
  have hxO : x.toScheme ∈ (𝟙 S) ⁻¹ᵁ U := hxU
  obtain ⟨hOi, hOd, hOqp⟩ := opens_props sS hSv hSdim hSqp ((𝟙 S) ⁻¹ᵁ U) ⟨_, hxO⟩
  haveI := hOi
  have hOle : (𝟙 S) ⁻¹ᵁ U ≤ smoothLocus sS := fun z hz ↦ by
    by_cases hzx : z = x.toScheme
    · rw [hzx]; exact hxs
    · exact hsm (show z ∈ V by rw [← SetLike.mem_coe, hV]; exact ⟨hz, hzx⟩)
  have hOs : IsSmoothScheme (((𝟙 S) ⁻¹ᵁ U).toScheme ↘ Spec (.of ℂ)) := by
    change IsSmoothScheme (((𝟙 S) ⁻¹ᵁ U).ι ≫ 𝟙 S ≫ sS)
    rw [Category.id_comp]
    exact isSmoothScheme_ι_comp sS _ hOle
  have hOqp' : Stacks.HProjective.IsQuasiProjective
      (((𝟙 S) ⁻¹ᵁ U).toScheme ↘ Spec (.of ℂ)) := by
    change Stacks.HProjective.IsQuasiProjective (((𝟙 S) ⁻¹ᵁ U).ι ≫ 𝟙 S ≫ sS)
    rwa [Category.id_comp]
  let y : ((𝟙 S) ⁻¹ᵁ U).toScheme := ⟨x.toScheme, hxO⟩
  have hset : (((𝟙 S) ⁻¹ᵁ U).ι ≫ 𝟙 S).base ⁻¹' {x.toScheme} = {y} := by
    ext z
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_singleton_iff]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ h ▸ rfl⟩
  have hy : IsClosed ({y} : Set ((𝟙 S) ⁻¹ᵁ U).toScheme) := by
    rw [← hset]
    exact (isClosed_singleton_toScheme x).preimage
      (((𝟙 S) ⁻¹ᵁ U).ι ≫ 𝟙 S).base.hom.continuous
  rw [hset]
  exact restrictInj_pointsOver_singleton hOs hOd hOqp' y hy

end Geometry

/-! ### Germs -/

section Stalk

/-- The map on stalks induced by the sheafification of a morphism of the presheaves
`V ↦ H^q(f⁻¹(V); ℚ)`, on germs of classes. -/
private theorem stalkFunctor_map_presheafToSheaf_germ {X X' Y : TopCat.{0}} (p : X ⟶ Y)
    (p' : X' ⟶ Y) (q : ℕ) (ψ : directImagePresheaf p q ⟶ directImagePresheaf p' q)
    {V : TopologicalSpace.Opens Y} (y : Y) (hy : y ∈ V)
    (c : rationalCohomology (preimageSpace p V) q) :
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

/-- Restriction to the fibre over `x` is injective on `H³` with supports on the preimage of an
open `B ∋ x` of `S^an` inside `U`, by excision from `f₀⁻¹(U)`. -/
private theorem restrictInj_preimageSpace {S W₀ : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sS] (f₀ : W₀ ⟶ S)
    (x : ComplexPoints sS) (U : S.Opens)
    (key : letI : (f₀ ⁻¹ᵁ U).toScheme.Over (Spec (.of ℂ)) := ⟨(f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS⟩
      RestrictInj (TopCat.of (UnderlyingSpace ℂ (f₀ ⁻¹ᵁ U)))
        (UnderlyingSpace.pointsOver (K := ℂ) (((f₀ ⁻¹ᵁ U).ι ≫ f₀).base ⁻¹' {x.toScheme})) 3)
    (B : TopologicalSpace.Opens (analyticSpace sS)) (hxB : x ∈ B)
    (hBU : ∀ p ∈ B, p.toScheme ∈ U) :
    RestrictInj (preimageSpace (analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS)) B)
      {t | (analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS) t.1).toScheme = x.toScheme} (2 + 1) := by
  classical
  let F := analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS)
  let T := preimageSpace F B
  let E : Set T := {t | (F t.1).toScheme = x.toScheme}
  letI : (f₀ ⁻¹ᵁ U).toScheme.Over (Spec (.of ℂ)) := ⟨(f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS⟩
  have hR := isOpenEmbedding_realize_ι (sX := f₀ ≫ sS) (f₀ ⁻¹ᵁ U)
  have hRr := range_realize_ι (sX := f₀ ≫ sS) (f₀ ⁻¹ᵁ U)
  set R := realize (sX := (f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS) (f₀ ⁻¹ᵁ U).ι rfl
  have hTR : ∀ t : T, t.1 ∈ Set.range R := fun t ↦ by
    rw [hRr]; exact hBU _ t.2
  let eR := hR.isEmbedding.toHomeomorph
  let g : T → ComplexPoints ((f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS) := fun t ↦ eR.symm ⟨t.1, hTR t⟩
  have hRg : ∀ t, R (g t) = t.1 := fun t ↦
    congrArg Subtype.val (eR.apply_symm_apply ⟨t.1, hTR t⟩)
  have hgc : Continuous g := eR.symm.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hg : Topology.IsOpenEmbedding g := by
    refine (Topology.IsOpenEmbedding.of_comp_iff g hR).1 ?_
    have : R ∘ g = Subtype.val := funext hRg
    rw [this]
    exact (B.isOpen.preimage F.hom.continuous).isOpenEmbedding_subtypeVal
  let φT : T ⟶ TopCat.of (UnderlyingSpace ℂ (f₀ ⁻¹ᵁ U)) :=
    TopCat.ofHom ⟨fun t ↦ homeomorphUnderlyingSpace (X := (f₀ ⁻¹ᵁ U).toScheme) (g t),
      (homeomorphUnderlyingSpace (X := (f₀ ⁻¹ᵁ U).toScheme)).continuous.comp hgc⟩
  have hφT : Topology.IsOpenEmbedding φT :=
    (homeomorphUnderlyingSpace (X := (f₀ ⁻¹ᵁ U).toScheme)).isOpenEmbedding.comp hg
  set EU := UnderlyingSpace.pointsOver (K := ℂ)
    (((f₀ ⁻¹ᵁ U).ι ≫ f₀).base ⁻¹' {x.toScheme})
  have hEUc : IsClosed EU := UnderlyingSpace.isClosed_pointsOver
    ((isClosed_singleton_toScheme x).preimage ((f₀ ⁻¹ᵁ U).ι ≫ f₀).base.hom.continuous)
  have hpre : φT ⁻¹' EU = E := by
    ext t
    have h1 : (F t.1).toScheme = ((f₀ ⁻¹ᵁ U).ι ≫ f₀).base ((g t).toScheme) := by
      change f₀.base t.1.toScheme = f₀.base ((f₀ ⁻¹ᵁ U).ι.base (g t).toScheme)
      rw [← congrArg ComplexPoints.toScheme (hRg t)]
      rfl
    change ((f₀ ⁻¹ᵁ U).ι ≫ f₀).base ((g t).hom (IsLocalRing.closedPoint ℂ)) ∈
      ({x.toScheme} : Set S) ↔ _
    rw [Subsingleton.elim (IsLocalRing.closedPoint ℂ) (default : Spec (.of ℂ)),
      Set.mem_singleton_iff]
    change _ ↔ (F t.1).toScheme = x.toScheme
    rw [h1]
    rfl
  have hEU : EU ⊆ Set.range φT := by
    intro w hw
    set u := (homeomorphUnderlyingSpace (X := (f₀ ⁻¹ᵁ U).toScheme)).symm w
    have hu : u.hom = w.toHom := by
      rw [← homeomorphUnderlyingSpace_apply, Homeomorph.apply_symm_apply]
    have hFu : F (R u) = x := by
      apply toScheme_injective
      have hw' : ((f₀ ⁻¹ᵁ U).ι ≫ f₀).base (w.toHom (IsLocalRing.closedPoint ℂ)) =
          x.toScheme := hw
      rwa [← hu, Subsingleton.elim (IsLocalRing.closedPoint ℂ) (default : Spec (.of ℂ))] at hw'
    refine ⟨⟨R u, show F (R u) ∈ B from hFu ▸ hxB⟩, ?_⟩
    change homeomorphUnderlyingSpace (X := (f₀ ⁻¹ᵁ U).toScheme) (eR.symm ⟨R u, _⟩) = w
    rw [show eR.symm ⟨R u, hTR ⟨R u, show F (R u) ∈ B from hFu ▸ hxB⟩⟩ = u from
      eR.symm_apply_apply u]
    exact Homeomorph.apply_symm_apply _ w
  have h3 := restrictInj_of_isOpenEmbedding φT hφT EU hEUc hEU 3 key
  rwa [hpre] at h3

/-- **Extension across the fibre.** For an open `B ∋ x` of `S^an` inside `U`, every class of
degree two on `B ∖ {x}`, read on `j⁻¹(B)`, is the pullback along the section `s` of a class on
`f₀⁻¹(B)`. -/
private theorem exists_rationalCohomologyMap_preimageRestrict_eq {S W₀ : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sS] (f₀ : W₀ ⟶ S)
    (x : ComplexPoints sS) (U : S.Opens) (V : S.Opens)
    (hV : (V : Set S) = (U : Set S) \ {x.toScheme})
    (s : (V : Scheme.{0}) ⟶ W₀) (hσ : s ≫ f₀ ≫ sS = V.ι ≫ sS)
    (hJ : analyticMap s hσ ≫ analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS) = analyticMap V.ι rfl)
    (key : letI : (f₀ ⁻¹ᵁ U).toScheme.Over (Spec (.of ℂ)) := ⟨(f₀ ⁻¹ᵁ U).ι ≫ f₀ ≫ sS⟩
      RestrictInj (TopCat.of (UnderlyingSpace ℂ (f₀ ⁻¹ᵁ U)))
        (UnderlyingSpace.pointsOver (K := ℂ) (((f₀ ⁻¹ᵁ U).ι ≫ f₀).base ⁻¹' {x.toScheme})) 3)
    (B : TopologicalSpace.Opens (analyticSpace sS)) (hxB : x ∈ B)
    (hBU : ∀ p ∈ B, p.toScheme ∈ U)
    (β : rationalCohomology (preimageSpace (analyticMap V.ι rfl) B) 2) :
    ∃ α : rationalCohomology (preimageSpace (analyticMap f₀ rfl) B) 2,
      (rationalCohomologyMap (preimageRestrict (analyticMap f₀ rfl) (analyticMap s hσ) hJ B)
        2).hom α = β := by
  classical
  let F := analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS)
  let J := analyticMap (sX := V.ι ≫ sS) V.ι rfl
  let σ := analyticMap s hσ
  let T := preimageSpace F B
  let E : Set T := {t | (F t.1).toScheme = x.toScheme}
  -- injectivity of the restriction to `E` on `T`, by excision from `f₀⁻¹(U)`
  have hE : RestrictInj T E (2 + 1) := restrictInj_preimageSpace sS f₀ x U key B hxB hBU
  -- the section identifies `j⁻¹(B)` with `T ∖ E`
  have hRV := isOpenEmbedding_realize_ι (sX := sS) V
  have hRVr := range_realize_ι (sX := sS) V
  set RV := realize (sX := V.ι ≫ sS) V.ι rfl
  have hJV : ∀ p : ComplexPoints (V.ι ≫ sS), (J p).toScheme ∈ V := fun p ↦ by
    have : RV p ∈ Set.range RV := Set.mem_range_self p
    rwa [hRVr] at this
  have hxV : x.toScheme ∉ V := by
    rw [← SetLike.mem_coe, hV]; exact fun h ↦ h.2 rfl
  let A : Set T := Eᶜ
  have hJσ : ∀ p, F (σ p) = J p := fun p ↦ congrArg (fun m ↦ m p) hJ
  have hk : ∀ p : preimageSpace J B, (preimageRestrict F σ hJ B p) ∈ A := by
    intro p h
    apply hxV
    have h' : (F (σ p.1)).toScheme = x.toScheme := h
    rw [← h', hJσ]
    exact hJV p.1
  let k : preimageSpace J B ⟶ TopCat.of A := TopCat.ofHom ⟨fun p ↦ ⟨_, hk p⟩,
    (preimageRestrict F σ hJ B).hom.continuous.subtype_mk _⟩
  have hA : ∀ t : A, (F t.1.1).toScheme ∈ V := fun t ↦ by
    rw [← SetLike.mem_coe, hV]; exact ⟨hBU _ t.1.2, t.2⟩
  let eV := hRV.isEmbedding.toHomeomorph
  let gfun : A → ComplexPoints (V.ι ≫ sS) := fun t ↦
    eV.symm ⟨F t.1.1, by rw [hRVr]; exact hA t⟩
  have hRVg : ∀ t, RV (gfun t) = F t.1.1 := fun t ↦
    congrArg Subtype.val (eV.apply_symm_apply _)
  have hgB : ∀ t, gfun t ∈ J ⁻¹' B := fun t ↦ by
    change RV (gfun t) ∈ B; rw [hRVg]; exact t.1.2
  let g : TopCat.of A ⟶ preimageSpace J B := TopCat.ofHom ⟨fun t ↦ ⟨gfun t, hgB t⟩,
    (eV.symm.continuous.comp ((F.hom.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)).subtype_mk _⟩
  have hkg : k ≫ g = 𝟙 _ := by
    refine TopCat.ext fun p ↦ ?_
    apply Subtype.ext
    apply hRV.injective
    change RV (gfun (k p)) = RV p.1
    rw [hRVg]
    exact hJσ p.1
  -- extend
  obtain ⟨α, hα⟩ := exists_restrictCompl_eq T E hE ((rationalCohomologyMap g 2).hom β)
  refine ⟨α, ?_⟩
  have hfac : k ≫ subspaceInclusion T A = preimageRestrict F σ hJ B := rfl
  rw [← hfac, rationalCohomologyMap_comp, ModuleCat.comp_apply]
  change (rationalCohomologyMap k 2).hom
    ((cohomologyWithSupports.restrictCompl ℚ T E (2 : ℕ)).hom α) = β
  rw [hα, ← ModuleCat.comp_apply, ← rationalCohomologyMap_comp, hkg, rationalCohomologyMap_id]
  rfl

/-- Surjectivity of the stalk map from the extension of classes on the punctured neighbourhoods
`B ∖ {x}`, `B ⊆ U`, to `f₀⁻¹(B)`. -/
private theorem surjective_of_lift {S W₀ : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) (f₀ : W₀ ⟶ S)
    (x : ComplexPoints sS) (U : S.Opens) (hxU : x.toScheme ∈ U) (V : S.Opens)
    (s : (V : Scheme.{0}) ⟶ W₀) (hs : s ≫ f₀ = V.ι)
    (hlift : ∀ (hσ : s ≫ f₀ ≫ sS = V.ι ≫ sS)
      (hJ : analyticMap s hσ ≫ analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS) = analyticMap V.ι rfl)
      (B : TopologicalSpace.Opens (analyticSpace sS)), x ∈ B → (∀ p ∈ B, p.toScheme ∈ U) →
      ∀ β : rationalCohomology (preimageSpace (analyticMap V.ι rfl) B) 2,
        ∃ α : rationalCohomology (preimageSpace (analyticMap f₀ rfl) B) 2,
          (rationalCohomologyMap (preimageRestrict (analyticMap f₀ rfl) (analyticMap s hσ) hJ B)
            2).hom α = β) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
        ((TopCat.Sheaf.forget _ _).map
          (higherDirectImageRestriction (j := analyticMap V.ι rfl) (analyticMap f₀ rfl)
            (analyticMap s (by rw [← Category.assoc, hs]))
            (by
              ext y
              change (y.hom ≫ s) ≫ f₀ = y.hom ≫ V.ι
              rw [Category.assoc, hs]) 2))).hom := by
  have hσ : s ≫ f₀ ≫ sS = V.ι ≫ sS := by rw [← Category.assoc, hs]
  have hJ : analyticMap s hσ ≫ analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS) =
      analyticMap V.ι rfl := by
    ext y
    change (y.hom ≫ s) ≫ f₀ = y.hom ≫ V.ι
    rw [Category.assoc, hs]
  set J := analyticMap (sX := V.ι ≫ sS) V.ι rfl
  set P := directImagePresheaf J 2
  intro y
  -- `y` is the germ of a class on `j⁻¹(B)`
  haveI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{0} ℚ) P
  obtain ⟨y', rfl⟩ := ((ConcreteCategory.isIso_iff_bijective
    ((TopCat.Presheaf.stalkFunctor _ x).map (toSheafify (Opens.grothendieckTopology _) P))).1
      inferInstance).2 y
  obtain ⟨B, hxB, β, rfl⟩ := P.germ_exist y'
  let Uan : TopologicalSpace.Opens (analyticSpace sS) :=
    ⟨{p | p.toScheme ∈ U}, isOpen_setOf_toScheme_mem U.isOpen⟩
  have hxB' : x ∈ B ⊓ Uan := ⟨hxB, hxU⟩
  obtain ⟨α, hα⟩ := hlift hσ hJ (B ⊓ Uan) hxB' (fun p hp ↦ hp.2)
    (P.map (homOfLE inf_le_left).op β)
  refine ⟨higherDirectImageGerm (analyticMap f₀ rfl) 2 x hxB' α, ?_⟩
  refine (stalkFunctor_map_presheafToSheaf_germ (analyticMap f₀ rfl) J 2
    (directImageRestriction (analyticMap f₀ rfl) (analyticMap s hσ) hJ 2) x hxB' α).trans ?_
  change (TopCat.Presheaf.stalkFunctor _ x).map (toSheafify _ P) (P.germ _ x hxB'
    ((rationalCohomologyMap (preimageRestrict (analyticMap f₀ rfl) (analyticMap s hσ) hJ
      (B ⊓ Uan)) 2).hom α)) = _
  rw [hα, TopCat.Presheaf.germ_res_apply]

/-- At a smooth point the extension of classes on `B ∖ {x}` already happens on `B`; pull back
along `f₀`. -/
private theorem lift_of_lift_id {S W₀ : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) (f₀ : W₀ ⟶ S) (x : ComplexPoints sS) (U : S.Opens) (V : S.Opens)
    (s : (V : Scheme.{0}) ⟶ W₀) (hs : s ≫ f₀ = V.ι)
    (hσ₁ : V.ι ≫ 𝟙 S ≫ sS = V.ι ≫ sS)
    (hJ₁ : analyticMap V.ι hσ₁ ≫ analyticMap (𝟙 S) (rfl : 𝟙 S ≫ sS = 𝟙 S ≫ sS) =
      analyticMap V.ι rfl)
    (hlift₁ : ∀ (B : TopologicalSpace.Opens (analyticSpace sS)), x ∈ B →
      (∀ p ∈ B, p.toScheme ∈ U) →
      ∀ β : rationalCohomology (preimageSpace (analyticMap V.ι rfl) B) 2,
        ∃ α : rationalCohomology (preimageSpace (analyticMap (𝟙 S) rfl) B) 2,
          (rationalCohomologyMap (preimageRestrict (analyticMap (𝟙 S) rfl)
            (analyticMap V.ι hσ₁) hJ₁ B) 2).hom α = β)
    (hσ : s ≫ f₀ ≫ sS = V.ι ≫ sS)
    (hJ : analyticMap s hσ ≫ analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS) = analyticMap V.ι rfl)
    (B : TopologicalSpace.Opens (analyticSpace sS)) (hxB : x ∈ B) (hBU : ∀ p ∈ B, p.toScheme ∈ U)
    (β : rationalCohomology (preimageSpace (analyticMap V.ι rfl) B) 2) :
    ∃ α : rationalCohomology (preimageSpace (analyticMap f₀ rfl) B) 2,
      (rationalCohomologyMap (preimageRestrict (analyticMap f₀ rfl) (analyticMap s hσ) hJ B)
        2).hom α = β := by
  obtain ⟨α', hα'⟩ := hlift₁ B hxB hBU β
  have hf₁ : f₀ ≫ 𝟙 S ≫ sS = f₀ ≫ sS := by rw [Category.id_comp]
  let ρ : preimageSpace (analyticMap f₀ (rfl : f₀ ≫ sS = f₀ ≫ sS)) B ⟶
      preimageSpace (analyticMap (𝟙 S) (rfl : 𝟙 S ≫ sS = 𝟙 S ≫ sS)) B :=
    TopCat.ofHom ⟨fun t ↦ ⟨analyticMap f₀ hf₁ t.1, t.2⟩,
      ((analyticMap f₀ hf₁).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  refine ⟨(rationalCohomologyMap ρ 2).hom α', ?_⟩
  rw [← ModuleCat.comp_apply, ← rationalCohomologyMap_comp]
  have hc : preimageRestrict (analyticMap f₀ rfl) (analyticMap s hσ) hJ B ≫ ρ =
      preimageRestrict (analyticMap (𝟙 S) rfl) (analyticMap V.ι hσ₁) hJ₁ B := by
    refine TopCat.ext fun p ↦ Subtype.ext (ComplexPoints.ext ?_)
    change (p.1.hom ≫ s) ≫ f₀ = p.1.hom ≫ V.ι
    rw [Category.assoc, hs]
  rwa [hc]

end Stalk

end MMP.Fold06.ThmMmpConductorThreefoldPuncturedH2Surjective

open CategoryTheory AlgebraicGeometry MMP.Analytic MMP.Analytic.ComplexPoints

namespace MMP.Fourfold

open MMP.Mori

open MMP.Fold06.ThmMmpConductorThreefoldPuncturedH2Surjective in
/-- **Degree-two punctured restriction at an isolated threefold singularity.** Let `S` be a
normal quasi-projective complex threefold, `x` a `ℂ`-point of `S` with an open neighbourhood `U`
such that `V = U ∖ {x}` is smooth, and `f₀ : W₀ ⟶ S` a projective resolution which is an
isomorphism over `V`, with section `s : V ⟶ W₀`. Then restriction of classes along `s` induces a
surjection `(R²f₀_* ℚ_{W₀})_x ⟶ (R²j_* ℚ_V)_x` of stalks at `x`, for `j : V^an ⟶ S^an`. -/
@[mmp "thm_mmp_conductor_threefold_punctured_h2_surjective"]
public theorem surjective_stalk_higherDirectImageRestriction_two {S W₀ : Scheme.{0}}
    (sS : S ⟶ Spec (.of ℂ)) [IsNormal S] (hSdim : topologicalKrullDim S = 3)
    (hSqp : Stacks.HProjective.IsQuasiProjective sS)
    (f₀ : W₀ ⟶ S) (hf₀ : MMP.Resolution.IsResolutionOfVariety sS f₀)
    (x : ComplexPoints sS) (U : S.Opens) (hxU : x.toScheme ∈ U)
    (V : S.Opens) (hV : (V : Set S) = (U : Set S) \ {x.toScheme})
    (hsm : V ≤ smoothLocus sS) (hbir : IsBiregular f₀ V)
    (s : (V : Scheme.{0}) ⟶ W₀) (hs : s ≫ f₀ = V.ι) :
    Function.Surjective
      ((TopCat.Presheaf.stalkFunctor (ModuleCat.{0} ℚ) x).map
        ((TopCat.Sheaf.forget _ _).map
          (higherDirectImageRestriction (j := analyticMap V.ι rfl) (analyticMap f₀ rfl)
            (analyticMap s (by rw [← Category.assoc, hs]))
            (by
              ext y
              change (y.hom ≫ s) ≫ f₀ = y.hom ≫ V.ι
              rw [Category.assoc, hs]) 2))).hom := by
  haveI : LocallyOfFiniteType sS := hSqp.locallyOfFiniteType
  refine surjective_of_lift sS f₀ x U hxU V s hs fun hσ hJ B hxB hBU β ↦ ?_
  by_cases hxs : x.toScheme ∈ smoothLocus sS
  · have hσ₁ : V.ι ≫ 𝟙 S ≫ sS = V.ι ≫ sS := by rw [Category.id_comp]
    have hJ₁ : analyticMap V.ι hσ₁ ≫ analyticMap (𝟙 S) (rfl : 𝟙 S ≫ sS = 𝟙 S ≫ sS) =
        analyticMap V.ι rfl := by
      ext y
      change (y.hom ≫ V.ι) ≫ 𝟙 S = y.hom ≫ V.ι
      rw [Category.comp_id]
    exact lift_of_lift_id sS f₀ x U V s hs hσ₁ hJ₁ (fun B' hxB' hB'U β' ↦
      exists_rationalCohomologyMap_preimageRestrict_eq sS (𝟙 S) x U V hV V.ι hσ₁ hJ₁
        (restrictInj_preimage_id_of_mem_smoothLocus sS hf₀.isVariety hSdim hSqp x U hxU V hV hsm
          hxs) B' hxB' hB'U β') hσ hJ B hxB hBU β
  · exact exists_rationalCohomologyMap_preimageRestrict_eq sS f₀ x U V hV s hσ hJ
      (restrictInj_preimage_of_notMem_smoothLocus sS hSdim hSqp f₀ hf₀ x U hxU V hV hsm hbir hxs)
      B hxB hBU β

end MMP.Fourfold
