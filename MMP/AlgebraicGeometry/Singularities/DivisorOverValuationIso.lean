module

public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.LocalIsomorphism

/-!
# Equal valuations and local isomorphisms (KM Rem. 2.23)

For divisors `(Y, f, E)` and `(Y', f', E')` over a variety `X`, `v(E, Y) = v(E', Y')` if and only
if `φ = f'^{-1} ∘ f : Y ⇢ Y'` is defined at `η_E`, sends it to `η_{E'}`, and restricts to an
isomorphism of an open neighbourhood of `η_E` onto one of `η_{E'}`.

## Main results

* `MMP.Positivity.DivisorOver.valuation_eq_iff_exists_iso`, with its two directions
  `MMP.Positivity.DivisorOver.exists_iso_of_valuation_eq` and
  `MMP.Positivity.DivisorOver.valuation_eq_of_iso`

## Implementation notes

The rational map `φ = f'^{-1} ∘ f` is encoded through its graph: an isomorphism `e : U ≅ V` of
open neighbourhoods `U ∋ η_E`, `V ∋ η_{E'}` with `f' ∘ e = f` on `U` is exactly `φ` restricted to
`U` (as `f'` is birational, `f'^{-1} ∘ f` is determined by `f' ∘ φ = f`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Positivity.DivisorOver

open MMP.Mori

open scoped WithZero

/-! ### Function fields and stalks -/

section Schemes

/-- An open immersion with nonempty source into an irreducible scheme is dominant. -/
theorem isDominant_of_isOpenImmersion {W Y : Scheme.{u}} [IrreducibleSpace Y] (a : W ⟶ Y)
    [IsOpenImmersion a] [Nonempty W] : IsDominant a :=
  ⟨a.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- Equal dominant morphisms of integral schemes induce equal maps of function fields. -/
theorem functionFieldMap_congr {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B] {a b : A ⟶ B}
    [IsDominant a] [IsDominant b] (h : a = b) : functionFieldMap a = functionFieldMap b := by
  subst h; rfl

/-- The extension of function fields of a composition is the composition of the extensions. -/
theorem functionFieldMap_functionFieldMap_apply {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] (a : A ⟶ B) (b : B ⟶ C) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)]
    (t : C.functionField) :
    functionFieldMap a (functionFieldMap b t) = functionFieldMap (a ≫ b) t := by
  suffices h : CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) =
      CommRingCat.ofHom (functionFieldMap (a ≫ b)) from
    congrArg (fun φ => φ.hom t) h
  apply Spec.map_injective
  apply (cancel_mono (C.fromSpecStalk (genericPoint C))).mp
  rw [functionFieldMap_fromSpecStalk (a ≫ b)]
  have hof : CommRingCat.ofHom ((functionFieldMap a).comp (functionFieldMap b)) =
      CommRingCat.ofHom (functionFieldMap b) ≫ CommRingCat.ofHom (functionFieldMap a) := rfl
  rw [hof, Spec.map_comp, Category.assoc, functionFieldMap_fromSpecStalk b,
    ← Category.assoc (Spec.map (CommRingCat.ofHom (functionFieldMap a))),
    functionFieldMap_fromSpecStalk a, Category.assoc]

/-- **Transfer of local rings along a common open neighbourhood.** Let `a : W ⟶ Y` be an open
immersion and `b : W ⟶ Y'` dominant, with `b ≫ f' = a ≫ f`. If `f'^* g` lies in `𝒪_{Y', b(w)}`,
then `f^* g` lies in `𝒪_{Y, a(w)}`. -/
theorem functionFieldMap_mem_range_of_comp_eq {X W Y Y' : Scheme.{u}} [IsIntegral X]
    [IsIntegral W] [IsIntegral Y] [IsIntegral Y'] (a : W ⟶ Y) (b : W ⟶ Y') [IsOpenImmersion a]
    [IsDominant a] [IsDominant b] (f : Y ⟶ X) (f' : Y' ⟶ X) [IsDominant f] [IsDominant f']
    (h : b ≫ f' = a ≫ f) (w : W) (g : X.functionField)
    (hg : functionFieldMap f' g ∈ (algebraMap (Y'.presheaf.stalk (b w)) Y'.functionField).range) :
    functionFieldMap f g ∈ (algebraMap (Y.presheaf.stalk (a w)) Y.functionField).range := by
  obtain ⟨c, hc⟩ := hg
  obtain ⟨c', hc'⟩ := (ConcreteCategory.bijective_of_isIso (a.stalkMap w)).2 ((b.stalkMap w).hom c)
  refine ⟨c', (functionFieldMap a).injective ?_⟩
  rw [functionFieldMap_algebraMap_stalk, hc', ← functionFieldMap_algebraMap_stalk b w c, hc,
    functionFieldMap_functionFieldMap_apply, functionFieldMap_functionFieldMap_apply,
    functionFieldMap_congr h]

/-- If `p = q` and the stalk map of `f` at `q` is an isomorphism, so is the stalk map at `p`. -/
theorem isIso_stalkMap_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) {p q : X} (h : p = q)
    [IsIso (f.stalkMap q)] : IsIso (f.stalkMap p) := by
  subst h; infer_instance

/-- If `f₁ = f₂ : Spec R ⟶ X` and `stalkClosedPointTo f₁` is an isomorphism, so is
`stalkClosedPointTo f₂`. -/
theorem isIso_stalkClosedPointTo_of_eq {R : CommRingCat.{u}} [IsLocalRing R] {X : Scheme.{u}}
    {f₁ f₂ : Spec R ⟶ X} (h : f₁ = f₂) [IsIso (Scheme.stalkClosedPointTo f₁)] :
    IsIso (Scheme.stalkClosedPointTo f₂) := by
  subst h; infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- For an isomorphism of local rings `φ : 𝒪_{X, x} ⟶ R`, the map
`Spec.map φ ≫ X.fromSpecStalk x` induces an isomorphism on the stalk at the closed point. -/
theorem isIso_stalkClosedPointTo_SpecMap_fromSpecStalk {R : CommRingCat.{u}} [IsLocalRing R]
    {X : Scheme.{u}} (x : X) (φ : X.presheaf.stalk x ⟶ R) [IsIso φ] :
    IsIso (Scheme.stalkClosedPointTo (Spec.map φ ≫ X.fromSpecStalk x)) := by
  rw [Scheme.stalkClosedPointTo_comp]
  have h1 : IsIso (Scheme.stalkClosedPointTo (Spec.map φ)) := by
    have : IsIso ((Spec.map φ).stalkMap (IsLocalRing.closedPoint R)) :=
      IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
    unfold Scheme.stalkClosedPointTo; exact IsIso.comp_isIso
  have h2 : IsIso ((X.fromSpecStalk x).stalkMap
      (IsLocalRing.closedPoint (X.presheaf.stalk x))) := by
    have h3 : IsIso (Scheme.stalkClosedPointTo (X.fromSpecStalk x)) := by
      rw [Scheme.stalkClosedPointTo_fromSpecStalk]; infer_instance
    unfold Scheme.stalkClosedPointTo at h3
    exact IsIso.of_isIso_comp_right _ (stalkClosedPointIso _).hom
  have := isIso_stalkMap_of_eq (X.fromSpecStalk x)
    (Spec_closedPoint (f := φ) : Spec.map φ (IsLocalRing.closedPoint R) = _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- A spread-out of the spectrum of an isomorphism of local rings sends the point to the point
and induces an isomorphism of local rings there. -/
theorem apply_eq_and_isIso_stalkMap_of_spread {Y Y' : Scheme.{u}} {U : Y.Opens} {y : Y}
    (hy : y ∈ U) {y' : Y'} (φ : Y'.presheaf.stalk y' ⟶ Y.presheaf.stalk y) [IsIso φ]
    (g : U.toScheme ⟶ Y')
    (h : Spec.map φ ≫ Y'.fromSpecStalk y' = U.fromSpecStalkOfMem y hy ≫ g) :
    g ⟨y, hy⟩ = y' ∧ IsIso (g.stalkMap ⟨y, hy⟩) := by
  have : IsIso (U.ι.stalkMap ⟨y, hy⟩) := IsOpenImmersion.instIsIsoCommRingCatStalkMap _ _
  have hc : (U.fromSpecStalkOfMem y hy) (IsLocalRing.closedPoint _) = ⟨y, hy⟩ := by
    rw [Scheme.Opens.fromSpecStalkOfMem, Scheme.Hom.comp_apply, Spec_closedPoint,
      Scheme.fromSpecStalk_closedPoint]
  refine ⟨?_, ?_⟩
  · have := congrArg (fun m => m (IsLocalRing.closedPoint (Y.presheaf.stalk y))) h
    simp only [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint] at this
    rw [this, hc]
  · have := isIso_stalkClosedPointTo_SpecMap_fromSpecStalk y' φ
    have h4 := isIso_stalkClosedPointTo_of_eq h
    rw [Scheme.stalkClosedPointTo_comp] at h4
    have : IsIso (Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem y hy)) :=
      isIso_stalkClosedPointTo_SpecMap_fromSpecStalk _ _
    have := IsIso.of_isIso_comp_right (g.stalkMap _)
      (Scheme.stalkClosedPointTo (U.fromSpecStalkOfMem y hy))
    exact isIso_stalkMap_of_eq g hc.symm

end Schemes

/-- Let `α : A → K` and `α' : A' → K'` be injective, `μ : L → K` surjective and `μ' : L → K'`
bijective. If `μ g ∈ range α ↔ μ' g ∈ range α'` for every `g`, then there is a bijective ring
map `φ : A' → A` with `α (φ b) = μ g` whenever `α' b = μ' g`. -/
theorem exists_bijective_ringHom {A A' K K' L : Type*} [CommRing A] [CommRing A'] [Field K]
    [Field K'] [Field L] (α : A →+* K) (α' : A' →+* K') (μ : L →+* K) (μ' : L →+* K')
    (hα : Function.Injective α) (hα' : Function.Injective α') (hμ : Function.Surjective μ)
    (hμ' : Function.Bijective μ') (H : ∀ g, μ g ∈ α.range ↔ μ' g ∈ α'.range) :
    ∃ φ : A' →+* A, Function.Bijective φ ∧ ∀ b g, α' b = μ' g → α (φ b) = μ g := by
  let e' := RingEquiv.ofBijective μ' hμ'
  have hσ' : ∀ g, e'.symm (μ' g) = g := e'.symm_apply_apply
  let eα : A ≃+* α.range :=
    RingEquiv.ofBijective α.rangeRestrict
      ⟨fun a b hab => hα (congrArg Subtype.val hab), α.rangeRestrict_surjective⟩
  let φ0 : A' →+* α.range :=
    ((μ.comp e'.symm.toRingHom).comp α').codRestrict α.range
      (fun b => (H _).2 ⟨b, (e'.apply_symm_apply _).symm⟩)
  let φ : A' →+* A := eα.symm.toRingHom.comp φ0
  have key : ∀ b, α (φ b) = μ (e'.symm (α' b)) := fun b =>
    congrArg Subtype.val (eα.apply_symm_apply (φ0 b))
  refine ⟨φ, ⟨fun b b' hbb => ?_, fun a => ?_⟩, fun b g hb => by rw [key, hb, hσ']⟩
  · have := congrArg α hbb
    rw [key, key] at this
    exact hα' (e'.symm.injective (μ.injective this))
  · obtain ⟨g, hg⟩ := hμ (α a)
    obtain ⟨b, hb⟩ := (H g).1 ⟨a, hg.symm⟩
    exact ⟨b, hα (by rw [key, hb, hσ', hg])⟩

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]

/-! ### Divisors over `X` with the same local ring -/

/-- Two divisors over `X` whose valuations have the same elements of value at most `1` have the
same valuation. -/
theorem valuation_eq_of_forall_le_one_iff (D D' : MMP.Mori.DivisorOver k sX)
    (H : ∀ g, D.valuation g ≤ 1 ↔ D'.valuation g ≤ 1) : D.valuation = D'.valuation := by
  have := D'.isIntegral
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isDominant
  have := D'.E.isDiscreteValuationRing_localRing
  let μ' := RingEquiv.ofBijective (functionFieldMap D'.f)
    D'.isBirationalMorphism.functionFieldMap_bijective
  have hD' : ∀ g, D'.valuation g = D'.E.divisorialValuation (μ' g) := fun g => rfl
  have hle : ∀ r : D'.E.localRing,
      D.valuation (μ'.symm (algebraMap D'.E.localRing D'.Y.functionField r)) ≤ 1 := by
    intro r
    rw [H, hD', RingEquiv.apply_symm_apply, MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    exact ⟨r, rfl⟩
  have key : D.valuation.comap μ'.symm.toRingHom = D'.E.divisorialValuation := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible D'.E.localRing
    refine valuation_eq_of_isDiscreteValuationRing (R := D'.E.localRing) hle
      (fun r hr => ?_) ?_ (fun r => ?_) (fun r hr => ?_)
      ⟨_, D'.E.divisorialValuation_algebraMap_of_irreducible hϖ⟩
    · change D.valuation (μ'.symm (algebraMap D'.E.localRing D'.Y.functionField r)) < 1
      refine (Valuation.isEquiv_iff_val_lt_one.1 (Valuation.isEquiv_iff_val_le_one.2 (H _))).2 ?_
      rw [hD', RingEquiv.apply_symm_apply]
      exact (MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff _ r).2 hr
    · obtain ⟨g, hg⟩ := exists_valuation_eq_exp_neg_one D
      refine ⟨μ' g, ?_⟩
      change D.valuation (μ'.symm (μ' g)) = _
      rw [RingEquiv.symm_apply_apply, hg]
    · rw [MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
      exact ⟨r, rfl⟩
    · exact (MMP.Mori.PrimeDivisor.divisorialValuation_algebraMap_lt_one_iff _ r).2 hr
  ext g
  have := congrArg (fun w : Valuation D'.Y.functionField ℤᵐ⁰ => w (μ' g)) key
  change D.valuation (μ'.symm (μ' g)) = D'.E.divisorialValuation (μ' g) at this
  rw [RingEquiv.symm_apply_apply] at this
  rw [this, hD']

set_option backward.isDefEq.respectTransparency false in
/-- **KM Rem. 2.23, `⇐`.** An isomorphism `e : U ≅ V` over `X` between open neighbourhoods of
`η_E` and `η_{E'}` with `e(η_E) = η_{E'}` forces `v(E, Y) = v(E', Y')`. -/
theorem valuation_eq_of_iso (D D' : MMP.Mori.DivisorOver k sX) (U : D.Y.Opens) (V : D'.Y.Opens)
    (hU : D.E.genericPoint ∈ U) (hV : D'.E.genericPoint ∈ V) (e : U.toScheme ≅ V.toScheme)
    (h1 : e.hom ≫ V.ι ≫ D'.f = U.ι ≫ D.f)
    (h2 : e.hom ⟨D.E.genericPoint, hU⟩ = ⟨D'.E.genericPoint, hV⟩) :
    D.valuation = D'.valuation := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isDominant
  have : Nonempty U := ⟨⟨_, hU⟩⟩
  have : IsDominant U.ι := isDominant_of_isOpenImmersion _
  have : IsDominant (e.hom ≫ V.ι) := isDominant_of_isOpenImmersion _
  have hw : (e.hom ≫ V.ι) ⟨_, hU⟩ = D'.E.genericPoint := by
    rw [Scheme.Hom.comp_apply, h2]
    rfl
  have hw' : U.ι ⟨_, hU⟩ = D.E.genericPoint := rfl
  have hc : (e.hom ≫ V.ι) ≫ D'.f = U.ι ≫ D.f := by rw [Category.assoc, h1]
  refine valuation_eq_of_forall_le_one_iff D D' fun g => ?_
  change D.E.divisorialValuation (functionFieldMap D.f g) ≤ 1 ↔
    D'.E.divisorialValuation (functionFieldMap D'.f g) ≤ 1
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
    MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
  constructor
  · intro hg
    have := functionFieldMap_mem_range_of_comp_eq (e.hom ≫ V.ι) U.ι D'.f D.f hc.symm ⟨_, hU⟩ g
      (by rwa [hw'])
    rwa [hw] at this
  · intro hg
    have := functionFieldMap_mem_range_of_comp_eq U.ι (e.hom ≫ V.ι) D.f D'.f hc ⟨_, hU⟩ g
      (by rwa [hw])
    rwa [hw'] at this

set_option backward.isDefEq.respectTransparency false in
/-- **KM Rem. 2.23, `⇒`.** If `v(E, Y) = v(E', Y')`, there are open neighbourhoods `U ∋ η_E` and
`V ∋ η_{E'}` and an isomorphism `e : U ≅ V` over `X` with `e(η_E) = η_{E'}`. -/
theorem exists_iso_of_valuation_eq (hX : MMP.Mori.IsVariety k sX)
    (D D' : MMP.Mori.DivisorOver k sX) (hv : D.valuation = D'.valuation) :
    ∃ (U : D.Y.Opens) (V : D'.Y.Opens) (hU : D.E.genericPoint ∈ U)
      (hV : D'.E.genericPoint ∈ V) (e : U.toScheme ≅ V.toScheme),
      e.hom ≫ V.ι ≫ D'.f = U.ι ≫ D.f ∧ e.hom ⟨D.E.genericPoint, hU⟩ = ⟨D'.E.genericPoint, hV⟩ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isDominant
  have : LocallyOfFiniteType (D'.f ≫ sX) := D'.isNormalVariety.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType D'.f := locallyOfFiniteType_of_comp D'.f sX
  have he : D.f D.E.genericPoint = D'.f D'.E.genericPoint :=
    map_genericPoint_eq_of_valuation_eq hX hv
  have H : ∀ g, functionFieldMap D.f g ∈ (algebraMap D.E.localRing D.Y.functionField).range ↔
      functionFieldMap D'.f g ∈ (algebraMap D'.E.localRing D'.Y.functionField).range := by
    intro g
    rw [← MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
      ← MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff]
    change D.valuation g ≤ 1 ↔ D'.valuation g ≤ 1
    rw [hv]
  obtain ⟨φ, hφbij, hφ⟩ := exists_bijective_ringHom (algebraMap D.E.localRing D.Y.functionField)
    (algebraMap D'.E.localRing D'.Y.functionField) (functionFieldMap D.f) (functionFieldMap D'.f)
    (IsFractionRing.injective _ _) (IsFractionRing.injective _ _)
    D.isBirationalMorphism.functionFieldMap_bijective.2
    D'.isBirationalMorphism.functionFieldMap_bijective H
  let Φ : D'.Y.presheaf.stalk D'.E.genericPoint ⟶ D.Y.presheaf.stalk D.E.genericPoint :=
    CommRingCat.ofHom φ
  have : IsIso Φ := (ConcreteCategory.isIso_iff_bijective Φ).2 hφbij
  have hcompat : D'.f.stalkMap D'.E.genericPoint ≫ Φ =
      X.presheaf.stalkSpecializes (Inseparable.of_eq he).specializes ≫
        D.f.stalkMap D.E.genericPoint := by
    ext a
    apply IsFractionRing.injective D.E.localRing D.Y.functionField
    change algebraMap D.E.localRing D.Y.functionField (φ ((D'.f.stalkMap _).hom a)) =
      algebraMap D.E.localRing D.Y.functionField
        ((D.f.stalkMap _).hom ((X.presheaf.stalkSpecializes _).hom a))
    rw [hφ _ (algebraMap (X.presheaf.stalk (D'.f D'.E.genericPoint)) X.functionField a)
      (functionFieldMap_algebraMap_stalk D'.f _ a).symm,
      ← functionFieldMap_algebraMap_stalk,
      MMP.Mori.algebraMap_stalkSpecializes (Inseparable.of_eq he).specializes]
  obtain ⟨U, hyU, g, hgφ, hgf⟩ := spread_out_of_isGermInjective D.f D'.f he Φ hcompat
  obtain ⟨hgy, hiso⟩ := apply_eq_and_isIso_stalkMap_of_spread hyU Φ g hgφ
  have : LocallyOfFiniteType g := by
    have : g ≫ D'.f ≫ sX = U.ι ≫ D.f ≫ sX := by rw [← Category.assoc, hgf, Category.assoc]
    have : LocallyOfFiniteType (g ≫ D'.f ≫ sX) := by rw [this]; infer_instance
    exact locallyOfFiniteType_of_comp g (D'.f ≫ sX)
  obtain ⟨A, hA, hAimm⟩ := exists_isOpenImmersion_res_of_isIso_stalkMap g ⟨_, hyU⟩
    (by rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _) hiso
  have hU₀ : D.E.genericPoint ∈ U.ι ''ᵁ A := ⟨⟨_, hyU⟩, hA, rfl⟩
  have hV₀ : D'.E.genericPoint ∈ (A.ι ≫ g).opensRange := ⟨⟨⟨_, hyU⟩, hA⟩, hgy⟩
  refine ⟨U.ι ''ᵁ A, (A.ι ≫ g).opensRange, hU₀, hV₀,
    (U.ι.isoImage A).symm ≪≫ (A.ι ≫ g).isoOpensRange, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι_assoc, hgf, Scheme.Hom.isoImage_inv_ι_assoc]
  · have hp : ((U.ι.isoImage A).inv ≫ A.ι) ⟨_, hU₀⟩ = ⟨_, hyU⟩ := by
      apply U.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.isoImage_inv_ι]
      rfl
    apply Subtype.ext
    change ((U.ι.isoImage A).inv ≫ (A.ι ≫ g).isoOpensRange.hom ≫
      (A.ι ≫ g).opensRange.ι) ⟨_, hU₀⟩ = _
    rw [Scheme.Hom.isoOpensRange_hom_ι, ← Category.assoc, Scheme.Hom.comp_apply, hp, hgy]

/-- **KM Rem. 2.23.** Let `f : Y → X` and `f' : Y' → X` be birational morphisms from normal
varieties, `E ⊂ Y` and `E' ⊂ Y'` prime divisors, and `φ = f'^{-1} ∘ f : Y ⇢ Y'`. Then
`v(E, Y) = v(E', Y')` if and only if `φ` is defined at `η_E`, `φ(η_E) = η_{E'}`, and `φ` restricts
to an isomorphism of an open neighbourhood of `η_E` onto an open neighbourhood of `η_{E'}`. -/
@[mmp "lem_km2b_same_valuation_iff_isomorphic_at_generic_points"]
theorem valuation_eq_iff_exists_iso (hX : MMP.Mori.IsVariety k sX)
    (D D' : MMP.Mori.DivisorOver k sX) :
    D.valuation = D'.valuation ↔
      ∃ (U : D.Y.Opens) (V : D'.Y.Opens) (hU : D.E.genericPoint ∈ U)
        (hV : D'.E.genericPoint ∈ V) (e : U.toScheme ≅ V.toScheme),
        e.hom ≫ V.ι ≫ D'.f = U.ι ≫ D.f ∧ e.hom ⟨D.E.genericPoint, hU⟩ = ⟨D'.E.genericPoint, hV⟩ :=
  ⟨exists_iso_of_valuation_eq hX D D', fun ⟨U, V, hU, hV, e, h1, h2⟩ =>
    valuation_eq_of_iso D D' U V hU hV e h1 h2⟩

end MMP.Positivity.DivisorOver
