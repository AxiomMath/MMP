module

public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
public import MMP.AlgebraicGeometry.Morphisms.ValuativeSeparated
public import MMP.AlgebraicGeometry.MMP.Fourfold.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.AffineBaseRegularGeneration
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Positivity.SerreAmpleCartier
public import MMP.AlgebraicGeometry.Morphisms.HProjective

/-!
# Foundations: valuative centres, approximation, Bertini, ampleness, blow-ups, constructibility

Six groups of independent foundational facts used throughout the minimal model program.

* **Centres of valuations.** For a proper morphism `f : V ⟶ W` of varieties over `k`, a
  valuation ring of `k(V)` dominating a local ring of `W` dominates the local ring of a unique
  point of `V` (the valuative criteria of universal closedness and separatedness). In particular
  every divisor over `W` has a unique centre on `V` when `f` is birational.
* **Approximation.** On a normal variety the orders of a rational function along finitely many
  prime divisors can be prescribed independently: the local rings at the divisors are pairwise
  distinct discrete valuation rings of the function field.
* **Bertini.** On a smooth variety over an algebraically closed field of characteristic zero, a
  general member of a free system is smooth, shares no component with a given snc divisor `G`,
  and is snc together with `G`; a very ample divisor has a non-zero section with smooth zero
  scheme.
* **Ampleness.** If `H` is `f`-ample and `A` is `g`-ample, then `H + c f^*A` is `(f ≫ g)`-ample
  for `c ≫ 0` (EGA II 4.6.13); over a field this says that an `f`-ample divisor plus a large
  multiple of the pull-back of an ample divisor is ample.
* **Blow-ups.** A finite sequence of blow-ups of a Noetherian scheme is projective.
* **Constructible sets.** (Chevalley) The image of a constructible set under a quasi-compact
  morphism locally of finite presentation into a quasi-compact quasi-separated scheme is
  constructible; and in a preirreducible space, in particular an irreducible scheme, a dense
  constructible set contains a dense open set.

## Main results

* `MMP.existsUnique_center_of_isProper`
* `MMP.Mori.PrimeDivisor.exists_ord_eq`
* `MMP.Threefold.Bridges.exists_dense_open_smooth_zeroScheme_isSNC_add`
* `MMP.Foundations.isRelativelyAmpleQ_add_smul_pullback`
* `MMP.Foundations.isAmple_add_zsmul_pullback`
* `MMP.Intersection.exists_ne_zero_smooth_zeroScheme_of_isVeryAmpleDivisor`
* `MMP.Resolution.ClosedBlowupSequence.isProjective_toBase`
* `Topology.IsConstructible.exists_isOpen_dense_subset`
* `MMP.isConstructible_image_and_exists_isOpen_dense_subset`

## Implementation notes

* Domination of a local ring `𝒪_x` by a valuation `ν` is written out: `ν ≤ 1` on `𝒪_x` and
  `ν < 1` on its maximal ideal. The centre on `W` is any specialization of the image of the
  generic point of `V`, so that `𝒪_{W,w}` maps to `k(V)`.
* Cartier divisors need not pull back along an arbitrary morphism, while their invertible sheaves
  do; the pull-back `f^*A` is any Cartier divisor `B` with `𝒪(B) ≅ f^*𝒪(A)`.
* A linear system is presented by spanning sections `s₀, …, s_N`, and the space of sections by
  the coefficient space `𝔸ᴺ⁺¹_k` (`MMP.Threefold.Bridges.coefficientSpace`).
* Chevalley's theorem is Mathlib's `AlgebraicGeometry.Scheme.Hom.isConstructible_image`, which
  needs `f` quasi-compact and locally of finite presentation and the target qcqs: without such
  finiteness hypotheses the image of a constructible set need not be constructible.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 1.45, 2.41,
  §5, 5.17
* [EGA II, 4.6.13]
* [R. Hartshorne, *Algebraic geometry*][Hartshorne], III.10.9
* [Kollár, *Lectures on resolution of singularities*], Def. 3.29
* [R. Lazarsfeld, *Positivity in algebraic geometry I*][Lazarsfeld]
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-! ### Centres of valuations under a proper morphism -/

section

open MMP.Mori

open scoped WithZero

namespace MMP

variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- **A dominated stalk gives a `Spec` of the valuation ring.** If `ψ : 𝒪_{X,z} → K` sends the
local ring into the valuation ring of `ν` and its maximal ideal into the maximal ideal, then
`Spec 𝒪_ν ⟶ X` through `Spec 𝒪_{X,z}` extends `Spec ψ` and sends the closed point to `z`. -/
private theorem exists_specValuationSubring_hom {K : Type u} [Field K] (ν : Valuation K Γ)
    {X : Scheme.{u}} (z : X) (ψ : X.presheaf.stalk z ⟶ CommRingCat.of K)
    (h1 : ∀ a, ν (ψ.hom a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z), ν (ψ.hom a) < 1) :
    ∃ l : Spec (.of ν.valuationSubring) ⟶ X,
      Spec.map (CommRingCat.ofHom (algebraMap ν.valuationSubring K)) ≫ l =
        Spec.map ψ ≫ X.fromSpecStalk z ∧
      l (IsLocalRing.closedPoint ν.valuationSubring) = z := by
  let φ : X.presheaf.stalk z →+* ν.valuationSubring :=
    ψ.hom.codRestrict ν.valuationSubring fun a => (ν.mem_valuationSubring_iff _).2 (h1 a)
  haveI : IsLocalHom (CommRingCat.ofHom φ).hom := ⟨fun a ha => by_contra fun hna =>
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.2
      (h2 a ((IsLocalRing.mem_maximalIdeal _).2 hna)) ha⟩
  refine ⟨Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk z, by rw [← Spec.map_comp_assoc]; rfl,
    ?_⟩
  change X.fromSpecStalk z (Spec.map (CommRingCat.ofHom φ) _) = z
  rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- Two points of an integral scheme separated over `Spec k` whose local rings are both
dominated by the valuation ring of `w` are equal. -/
private theorem eq_of_dominates {X : Scheme.{u}} [IsIntegral X] {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [IsSeparated sX] (w : Valuation X.functionField Γ) {x x' : X}
    (h1 : ∀ a : X.presheaf.stalk x, w (algebraMap _ X.functionField a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      w (algebraMap _ X.functionField a) < 1)
    (h1' : ∀ a : X.presheaf.stalk x', w (algebraMap _ X.functionField a) ≤ 1)
    (h2' : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x'),
      w (algebraMap _ X.functionField a) < 1) : x = x' := by
  have hη (y : X) : genericPoint X ⤳ y := (genericPoint_spec X).specializes trivial
  obtain ⟨l, hl, rfl⟩ :=
    exists_specValuationSubring_hom w x (X.presheaf.stalkSpecializes (hη x)) h1 h2
  obtain ⟨l', hl', rfl⟩ :=
    exists_specValuationSubring_hom w x' (X.presheaf.stalkSpecializes (hη x')) h1' h2'
  rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk] at hl hl'
  let α := CommRingCat.ofHom (algebraMap w.valuationSubring X.functionField)
  have key : ∀ g g' : Spec (.of w.valuationSubring) ⟶ Spec (.of k),
      Spec.map α ≫ g = Spec.map α ≫ g' → g = g' := by
    intro g g' h
    obtain ⟨p, rfl⟩ : ∃ p, Spec.map p = g := ⟨_, Spec.map_preimage g⟩
    obtain ⟨p', rfl⟩ : ∃ p, Spec.map p = g' := ⟨_, Spec.map_preimage g'⟩
    rw [← Spec.map_comp, ← Spec.map_comp] at h
    congr 1
    ext c
    exact congrArg (fun q => q.hom c) (Spec.map_injective h)
  let S : ValuativeCommSq sX :=
    { R := w.valuationSubring
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := l ≫ sX
      commSq := ⟨by rw [← hl, Category.assoc]⟩ }
  have := IsSeparated.valuativeCriterion sX S
  have hll : l' ≫ sX = l ≫ sX := key _ _ (by rw [← Category.assoc, ← Category.assoc, hl, hl'])
  have := congrArg CommSq.LiftStruct.l
    (Subsingleton.elim (⟨l, hl, rfl⟩ : S.commSq.LiftStruct) ⟨l', hl', hll⟩)
  exact congrArg (fun m : Spec (.of w.valuationSubring) ⟶ X =>
    m (IsLocalRing.closedPoint w.valuationSubring)) this

/-- **Existence of a centre under a universally closed morphism.** If the valuation ring of `ν`
dominates `𝒪_{W,w}` for a specialization `w` of `f(η_V)`, it dominates `𝒪_{V,v}` for a point
`v` over `w`. -/
private theorem exists_dominates_of_universallyClosed {V W : Scheme.{u}} [IsIntegral V]
    (f : V ⟶ W) [UniversallyClosed f] (ν : Valuation V.functionField Γ) (w : W)
    (hw : f (genericPoint V) ⤳ w)
    (h1 : ∀ a : W.presheaf.stalk w,
      ν ((W.presheaf.stalkSpecializes hw ≫ f.stalkMap (genericPoint V)).hom a) ≤ 1)
    (h2 : ∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk w),
      ν ((W.presheaf.stalkSpecializes hw ≫ f.stalkMap (genericPoint V)).hom a) < 1) :
    ∃ v : V, f v = w ∧
      (∀ a : V.presheaf.stalk v, ν (algebraMap _ V.functionField a) ≤ 1) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk v),
        ν (algebraMap _ V.functionField a) < 1) := by
  obtain ⟨l, hl, hlw⟩ := exists_specValuationSubring_hom ν w _ h1 h2
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk] at hl
  let S : ValuativeCommSq f :=
    { R := ν.valuationSubring
      K := V.functionField
      i₁ := V.fromSpecStalk (genericPoint V)
      i₂ := l
      commSq := ⟨hl.symm⟩ }
  have hE : ValuativeCriterion.Existence f := by
    have : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact this.1
  obtain ⟨⟨L⟩⟩ := hE S
  set v := L.l (IsLocalRing.closedPoint ν.valuationSubring)
  refine ⟨v, ?_, ?_⟩
  · change (L.l ≫ f) _ = w
    rw [L.fac_right]
    exact hlw
  set ρ := Scheme.stalkClosedPointTo L.l
  have hη : genericPoint V ⤳ v := (genericPoint_spec V).specializes trivial
  have hρ : ρ ≫ CommRingCat.ofHom (algebraMap ν.valuationSubring V.functionField) =
      V.presheaf.stalkSpecializes hη := by
    apply Spec.map_injective
    rw [← cancel_mono (V.fromSpecStalk v), Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, L.fac_left,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hρa (a : V.presheaf.stalk v) :
      algebraMap _ V.functionField a = ((ρ.hom a : ν.valuationSubring) : V.functionField) :=
    (congrArg (fun q => q.hom a) hρ).symm
  refine ⟨fun a => ?_, fun a ha => ?_⟩
  · rw [hρa]
    exact (ν.mem_valuationSubring_iff _).1 (ρ.hom a).2
  · rw [hρa]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1
      ((IsLocalRing.mem_maximalIdeal _).1 (map_nonunit ρ.hom a ha))

/-- The extension of function fields of a dominant morphism, applied to an element of the local
ring at a specialization `w` of `f(η_V)`, is the map `𝒪_{W,w} → 𝒪_{W,f(η_V)} → k(V)`. -/
private theorem functionFieldMap_algebraMap_stalkSpecializes {V W : Scheme.{u}} [IsIntegral V]
    [IsIntegral W] (f : V ⟶ W) [IsDominant f] (w : W) (hw : f (genericPoint V) ⤳ w)
    (a : W.presheaf.stalk w) :
    functionFieldMap f (algebraMap _ W.functionField a) =
      (W.presheaf.stalkSpecializes hw ≫ f.stalkMap (genericPoint V)).hom a := by
  have hW : genericPoint W ⤳ w := (genericPoint_spec W).specializes trivial
  change ((W.presheaf.stalkCongr (Inseparable.of_eq (map_genericPoint_of_isDominant f).symm)).hom ≫
    f.stalkMap (genericPoint V)).hom ((W.presheaf.stalkSpecializes hW).hom a) = _
  rw [← CommRingCat.comp_apply, ← Category.assoc]
  congr 3
  rw [TopCat.Presheaf.stalkCongr_hom]
  exact TopCat.Presheaf.stalkSpecializes_comp ..

/-- **A valuation ring centred on the target of a proper morphism has a unique centre on the
source.** Let `f : V ⟶ W` be a proper morphism of varieties over `k` and `R` a valuation subring
of `k(V)` containing `k`, which dominates the local ring of a point `w` of `W` specializing from
`f(η_V)`. Then `R` dominates the local ring of a unique point `v` of `V`, and `f v = w`.
Moreover, if `f` is birational, the valuation of every divisor `D` over `W` dominates the local
ring of a unique point of `V`. -/
@[mmp "lem_mmp_foundation_km3c_proper_valuative_center"]
public theorem existsUnique_center_of_isProper {k : Type u} [Field k] {V W : Scheme.{u}}
    {sV : V ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} (hV : Mori.IsVariety k sV)
    (hW : Mori.IsVariety k sW) (f : V ⟶ W) [IsProper f] (hf : f ≫ sW = sV) :
    haveI : IsIntegral V := hV.toIsIntegral
    haveI : IsIntegral W := hW.toIsIntegral
    (∀ (R : ValuationSubring V.functionField),
      (letI := functionFieldAlgebra sV; ∀ c : k, algebraMap k V.functionField c ∈ R) →
      ∀ (w : W) (hw : f (genericPoint V) ⤳ w),
      (∀ a : W.presheaf.stalk w,
        R.valuation ((W.presheaf.stalkSpecializes hw ≫ f.stalkMap (genericPoint V)).hom a) ≤ 1) →
      (∀ a ∈ IsLocalRing.maximalIdeal (W.presheaf.stalk w),
        R.valuation ((W.presheaf.stalkSpecializes hw ≫ f.stalkMap (genericPoint V)).hom a) < 1) →
      ∃ v : V, f v = w ∧
        (∀ a : V.presheaf.stalk v, R.valuation (algebraMap _ V.functionField a) ≤ 1) ∧
        (∀ a ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk v),
          R.valuation (algebraMap _ V.functionField a) < 1) ∧
        ∀ v' : V,
          (∀ a : V.presheaf.stalk v', R.valuation (algebraMap _ V.functionField a) ≤ 1) →
          (∀ a ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk v'),
            R.valuation (algebraMap _ V.functionField a) < 1) → v' = v) ∧
    (∀ (hb : IsBirationalMorphism f) (D : DivisorOver k sW),
      haveI : IsDominant f := hb.isDominant
      ∃! v : V,
        (∀ (a : V.presheaf.stalk v) (g : W.functionField),
          functionFieldMap f g = algebraMap _ V.functionField a → D.valuation g ≤ 1) ∧
        (∀ a ∈ IsLocalRing.maximalIdeal (V.presheaf.stalk v), ∀ g : W.functionField,
          functionFieldMap f g = algebraMap _ V.functionField a → D.valuation g < 1)) := by
  haveI : IsIntegral V := hV.toIsIntegral
  haveI : IsIntegral W := hW.toIsIntegral
  haveI : IsSeparated sV := hV.toIsSeparated
  refine ⟨fun R _ w hw h1 h2 => ?_, fun hb D => ?_⟩
  · obtain ⟨v, hfv, hv1, hv2⟩ :=
      exists_dominates_of_universallyClosed f R.valuation w hw h1 h2
    exact ⟨v, hfv, hv1, hv2, fun v' h1' h2' =>
      eq_of_dominates sV R.valuation h1' h2' hv1 hv2⟩
  · haveI : IsDominant f := hb.isDominant
    let E : W.functionField ≃+* V.functionField :=
      RingEquiv.ofBijective (functionFieldMap f) hb.functionFieldMap_bijective
    let ν : Valuation V.functionField ℤᵐ⁰ := D.valuation.comap (E.symm : V.functionField →+* _)
    have hν : ∀ x : V.functionField, ν x = D.valuation (E.symm x) := fun _ => rfl
    have hiff : ∀ (x : V.functionField) (P : ℤᵐ⁰ → Prop),
        (∀ g, functionFieldMap f g = x → P (D.valuation g)) ↔ P (ν x) := by
      intro x P
      refine ⟨fun h => h _ (E.apply_symm_apply x), fun h g hg => ?_⟩
      rwa [← hg, hν, show E.symm (functionFieldMap f g) = g from E.symm_apply_apply g] at h
    have hw : f (genericPoint V) ⤳ D.f D.E.genericPoint := by
      rw [map_genericPoint_of_isDominant f]
      exact (genericPoint_spec W).specializes trivial
    have hψ : ∀ a : W.presheaf.stalk (D.f D.E.genericPoint),
        ν ((W.presheaf.stalkSpecializes hw ≫ f.stalkMap (genericPoint V)).hom a) =
          D.valuation (algebraMap _ W.functionField a) := by
      intro a
      rw [hν, ← functionFieldMap_algebraMap_stalkSpecializes f _ hw a]
      exact congrArg D.valuation (E.symm_apply_apply _)
    obtain ⟨v, -, hv1, hv2⟩ := exists_dominates_of_universallyClosed f ν _ hw
      (fun a => by
        rw [hψ]
        exact Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl a)
      (fun a ha => by
        rw [hψ]
        exact Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl a ha)
    refine ⟨v, ⟨fun a => (hiff _ (· ≤ 1)).2 (hv1 a),
      fun a ha => (hiff _ (· < 1)).2 (hv2 a ha)⟩, fun v' ⟨h1', h2'⟩ => ?_⟩
    exact eq_of_dominates sV ν (fun a => (hiff _ (· ≤ 1)).1 (h1' a))
      (fun a ha => (hiff _ (· < 1)).1 (h2' a ha)) hv1 hv2

end MMP

end

/-! ### Prescribed orders along finitely many prime divisors -/

section

open IsDedekindDomain
open scoped WithZero

namespace MMP

section Algebra

variable (A F : Type*) [CommRing A] [IsDomain A] [ValuationRing A] [Field F] [Algebra A F]
  [IsFractionRing A F]

/-- The image of a valuation ring `A` in its fraction field `F`, as a valuation subring of `F`. -/
private def rangeValuationSubring : ValuationSubring F where
  toSubring := (algebraMap A F).range
  mem_or_inv_mem' x := by
    rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨a, ha⟩

variable {A F}

/-- A valuation subring of `F` whose underlying set is the image of `A` is isomorphic to `A`. -/
private noncomputable def equivOfCoeEq (V : ValuationSubring F)
    (hV : (V : Set F) = Set.range (algebraMap A F)) : A ≃+* V :=
  RingEquiv.ofBijective
    ((algebraMap A F).codRestrict V fun a => by rw [← SetLike.mem_coe, hV]; exact ⟨a, rfl⟩)
    ⟨fun a b h => IsFractionRing.injective A F (congrArg Subtype.val h), fun r => by
      obtain ⟨a, ha⟩ : (r : F) ∈ Set.range (algebraMap A F) := hV ▸ r.2
      exact ⟨a, Subtype.ext ha⟩⟩

private theorem coe_equivOfCoeEq (V : ValuationSubring F)
    (hV : (V : Set F) = Set.range (algebraMap A F)) (a : A) :
    ((equivOfCoeEq V hV a : V) : F) = algebraMap A F a := rfl

/-- In a discrete valuation subring `V` of `F`, an element of normalized valuation `1` is a
unit of `V`. -/
private theorem exists_isUnit_of_valuation_eq_one (V : ValuationSubring F)
    [IsDiscreteValuationRing V] {u : F}
    (hu : (IsDiscreteValuationRing.maximalIdeal V).valuation F u = 1) :
    ∃ r : V, IsUnit r ∧ (r : F) = u := by
  have key : ∀ r : V, (IsDiscreteValuationRing.maximalIdeal V).valuation F (r : F) = 1 →
      IsUnit r := by
    intro r hr
    by_contra hnu
    have hmem : r ∈ (IsDiscreteValuationRing.maximalIdeal V).asIdeal :=
      (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem,
      ← HeightOneSpectrum.valuation_of_algebraMap (K := F)] at hmem
    exact (ne_of_lt hmem) hr
  rcases V.mem_or_inv_mem u with h | h
  · exact ⟨⟨u, h⟩, key _ hu, rfl⟩
  · have hu' : (IsDiscreteValuationRing.maximalIdeal V).valuation F u⁻¹ = 1 := by
      rw [map_inv₀, hu, inv_one]
    obtain ⟨w, hw⟩ := key ⟨u⁻¹, h⟩ hu'
    refine ⟨(w⁻¹ : Vˣ), (w⁻¹).isUnit, ?_⟩
    have h1 : ((w : V) : F) * (((w⁻¹ : Vˣ) : V) : F) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    rw [hw] at h1
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    exact ((inv_mul_eq_one₀ hu0).1 h1).symm

/-- The unequal-valuation step: if `V ≅ A` is the image of `A` in `F`, `ϖ` a uniformizer of `A`
and `v(x - ϖⁿ) ≥ n + 1` for the normalized valuation `v` of `V`, then `x = ϖⁿ a` with `a` a unit
of `A`. -/
private theorem exists_isUnit_eq_zpow_mul (V : ValuationSubring F) [IsDiscreteValuationRing V]
    (hV : (V : Set F) = Set.range (algebraMap A F)) {ϖ : A} (hϖ : Irreducible ϖ) (n : ℤ) {x : F}
    (hx : (IsDiscreteValuationRing.maximalIdeal V).valuation F (x - algebraMap A F ϖ ^ n) ≤
      WithZero.exp (-(n + 1))) :
    ∃ a : A, IsUnit a ∧ x = algebraMap A F ϖ ^ n * algebraMap A F a := by
  set e := equivOfCoeEq V hV
  set w := (IsDiscreteValuationRing.maximalIdeal V).valuation F
  set t := algebraMap A F ϖ
  have hϖV : Irreducible (e ϖ) := (MulEquiv.irreducible_iff e.toMulEquiv).2 hϖ
  have ht : w t = WithZero.exp (-1) := by
    rw [show t = algebraMap V F (e ϖ) from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_singleton _ hϖV.ne_zero
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖV)
  have htn : w (t ^ n) = WithZero.exp (-n) := by
    rw [map_zpow₀, ht, ← WithZero.exp_zsmul]
    simp
  have hlt : w (x - t ^ n) < w (t ^ n) :=
    hx.trans_lt (by rw [htn]; exact WithZero.exp_lt_exp.2 (by omega))
  have hwx : w x = WithZero.exp (-n) := by
    have := Valuation.map_add_eq_of_lt_left w hlt
    rwa [add_sub_cancel, htn] at this
  have ht0 : t ^ n ≠ 0 := by
    intro h; rw [h, map_zero] at htn; exact WithZero.exp_ne_zero htn.symm
  have hu : w (x * (t ^ n)⁻¹) = 1 := by
    rw [map_mul, map_inv₀, hwx, htn, mul_inv_cancel₀ WithZero.exp_ne_zero]
  obtain ⟨r, hr, hru⟩ := exists_isUnit_of_valuation_eq_one V hu
  refine ⟨e.symm r, hr.map e.symm, ?_⟩
  rw [← coe_equivOfCoeEq V hV, show equivOfCoeEq V hV = e from rfl, e.apply_symm_apply, hru]
  field_simp

end Algebra

section Geometry

variable {X : Scheme.{u}}

/-- On an irreducible scheme the generic point of every irreducible component is the generic
point of `X`. -/
private theorem componentGenericPoint_eq_genericPoint [IrreducibleSpace X]
    (Z : irreducibleComponents X) : MMP.Mori.componentGenericPoint X Z = genericPoint X := by
  have h : ∀ S ∈ irreducibleComponents X, S = Set.univ := by
    rw [irreducibleComponents_eq_singleton]; exact fun S hS => hS
  have hZ : (Z : Set X) = Set.univ := h _ Z.2
  exact (MMP.Mori.isGenericPoint_componentGenericPoint X Z).eq (hZ ▸ genericPoint_spec X)

/-- The morphism `Spec V → X` induced by an isomorphism of `𝒪_{X,x}` onto a subring `V` of the
function field. -/
private noncomputable def specTo [IsIntegral X] (V : ValuationSubring X.functionField) (x : X)
    (e : X.presheaf.stalk x ≃+* V) : Spec (.of V) ⟶ X :=
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk x

private theorem specTo_closedPoint [IsIntegral X] (V : ValuationSubring X.functionField) (x : X)
    (e : X.presheaf.stalk x ≃+* V) :
    specTo V x e (IsLocalRing.closedPoint (CommRingCat.of V)) = x := by
  haveI : IsLocalHom (CommRingCat.ofHom e.toRingHom).hom := ⟨fun a ha => (isUnit_map_iff e a).1 ha⟩
  exact (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg (X.fromSpecStalk x) Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)

private theorem specTo_generic [IsIntegral X] (V : ValuationSubring X.functionField) (x : X)
    (e : X.presheaf.stalk x ≃+* V)
    (he : ∀ a, ((e a : V) : X.functionField) = algebraMap _ X.functionField a) :
    Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ specTo V x e =
      X.fromSpecStalk (genericPoint X) := by
  rw [specTo, ← Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom (algebraMap V X.functionField) =
      X.presheaf.stalkSpecializes (genericPoint_specializes x) := by
    ext a
    exact he a
  rw [this, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- On a separated integral scheme, two points whose local rings are valuation rings with the
same image in the function field are equal. -/
private theorem eq_of_range_algebraMap_eq (k : Type u) [Field k] [IsIntegral X]
    [X.Over (Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))] {x y : X}
    [ValuationRing (X.presheaf.stalk x)] [ValuationRing (X.presheaf.stalk y)]
    (h : Set.range (algebraMap (X.presheaf.stalk x) X.functionField) =
      Set.range (algebraMap (X.presheaf.stalk y) X.functionField)) : x = y := by
  set V := rangeValuationSubring (X.presheaf.stalk x) X.functionField
  have hx : (V : Set X.functionField) = Set.range (algebraMap _ _) := rfl
  have hy : (V : Set X.functionField) = Set.range (algebraMap (X.presheaf.stalk y) _) := h
  have hl := MMP.ext_of_isSeparated_of_valuationRing (L := X.functionField) k
    (specTo V x (equivOfCoeEq V hx)) (specTo V y (equivOfCoeEq V hy))
    ((specTo_generic V x _ (coe_equivOfCoeEq V hx)).trans
      (specTo_generic V y _ (coe_equivOfCoeEq V hy)).symm)
  rw [← specTo_closedPoint V x (equivOfCoeEq V hx), hl, specTo_closedPoint]

/-- The function field of an integral scheme, embedded diagonally in the rational functions
`∏_Z 𝒪_{X,η_Z}` (there is a single component, whose generic point is that of `X`). -/
private noncomputable def toRationalFunctions [IsIntegral X] :
    X.functionField →+* MMP.Mori.RationalFunctions X :=
  Pi.ringHom fun Z => (X.presheaf.stalkCongr
    (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z))).inv.hom

private theorem toRationalFunctions_algebraMap [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (D : MMP.Mori.PrimeDivisor X) (b : D.localRing) :
    toRationalFunctions (algebraMap _ X.functionField b) D.component = D.toComponent.hom b := by
  change (X.presheaf.stalkSpecializes (genericPoint_specializes D.genericPoint) ≫
    X.presheaf.stalkSpecializes
      (specializes_of_eq (componentGenericPoint_eq_genericPoint D.component))).hom b = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  rfl

/-- A function `ϖⁿ a` with `ϖ` a uniformizer and `a` a unit of `𝒪_{X,D}` has order `n`
along `D`. -/
private theorem ord_toRationalFunctions [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] (D : MMP.Mori.PrimeDivisor X) [IsDiscreteValuationRing D.localRing]
    {x : X.functionField} (hx : x ≠ 0) {ϖ a : D.localRing} (hϖ : Irreducible ϖ) (ha : IsUnit a)
    (n : ℤ) (hxa : x = algebraMap _ _ ϖ ^ n * algebraMap _ _ a) :
    D.ord ((Ne.isUnit hx).map toRationalFunctions).unit = n := by
  let val : X.functionField →*₀ ℤᵐ⁰ := D.valuation.comp
    ((Pi.evalRingHom _ D.component).comp toRationalFunctions).toMonoidWithZeroHom
  have hv : val x = WithZero.exp n := by
    rw [hxa, map_mul, map_zpow₀]
    simp only [val, MonoidWithZeroHom.comp_apply, RingHom.toMonoidWithZeroHom_eq_coe,
      RingHom.comp_apply, Pi.evalRingHom_apply,
      toRationalFunctions_algebraMap, D.valuation_toComponent_of_irreducible hϖ,
      D.valuation_toComponent_of_isUnit ha, ← WithZero.exp_zsmul, smul_eq_mul, mul_one]
  have h := D.valuation_component ((Ne.isUnit hx).map toRationalFunctions).unit
  rw [IsUnit.unit_spec] at h
  exact WithZero.exp_injective (h.symm.trans hv)

end Geometry

end MMP

namespace MMP.Mori.PrimeDivisor

/-- On a normal variety, the orders of vanishing of a rational function along finitely many
distinct prime divisors can be prescribed arbitrarily. -/
@[mmp "lem_mmp_foundation_km5b_krull_approximation"]
public theorem exists_ord_eq (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hX : IsVariety k f) [IsLocallyNoetherian X] [IsNormal X]
    (s : Finset (PrimeDivisor X)) (n : PrimeDivisor X → ℤ) :
    ∃ φ : (RationalFunctions X)ˣ, ∀ D ∈ s, D.ord φ = n D := by
  haveI : IsIntegral X := hX.toIsIntegral
  letI : X.Over (Spec (.of k)) := ⟨f⟩
  haveI : IsSeparated (X ↘ Spec (.of k)) := hX.toIsSeparated
  haveI : ∀ D : MMP.Mori.PrimeDivisor X, IsDiscreteValuationRing D.localRing :=
    fun D => D.isDiscreteValuationRing_localRing
  set F := X.functionField
  let V : s → ValuationSubring F := fun D =>
    rangeValuationSubring (X.presheaf.stalk D.1.genericPoint) F
  haveI : ∀ D, IsDiscreteValuationRing (V D) := fun D =>
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (equivOfCoeEq (A := X.presheaf.stalk D.1.genericPoint) (V D) rfl)
  have hVinj : Function.Injective V := fun D D' h => Subtype.ext
    (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_range_algebraMap_eq k (congrArg (fun W : ValuationSubring F => (W : Set F)) h)))
  choose ϖ hϖ using fun D : MMP.Mori.PrimeDivisor X =>
    IsDiscreteValuationRing.exists_irreducible D.localRing
  obtain ⟨x, hx⟩ := MMP.exists_forall_valuation_sub_le_of_injective V hVinj
    (fun D => algebraMap _ F (ϖ D.1) ^ n D.1) (fun D => n D.1 + 1)
  have key : ∀ D : s, ∃ a : D.1.localRing, IsUnit a ∧
      x = algebraMap _ F (ϖ D.1) ^ n D.1 * algebraMap _ F a :=
    fun D => exists_isUnit_eq_zpow_mul (V D) rfl (hϖ D.1) (n D.1) (hx D)
  rcases s.eq_empty_or_nonempty with rfl | ⟨D₀, hD₀⟩
  · exact ⟨1, by simp⟩
  have hx0 : x ≠ 0 := by
    obtain ⟨a, ha, hxa⟩ := key ⟨D₀, hD₀⟩
    rw [hxa]
    exact mul_ne_zero (zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective _ F)).2
      (hϖ D₀).ne_zero)) ((map_ne_zero_iff _ (IsFractionRing.injective _ F)).2 ha.ne_zero)
  refine ⟨((Ne.isUnit hx0).map toRationalFunctions).unit, fun D hD => ?_⟩
  obtain ⟨a, ha, hxa⟩ := key ⟨D, hD⟩
  exact ord_toRationalFunctions D hx0 (hϖ D) ha (n D) hxa

end MMP.Mori.PrimeDivisor

end

/-! ### Bertini for simple normal crossings in the space of sections -/

section

open TopologicalSpace MMP.Resolution

namespace MMP.Threefold.Bridges

open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (globalSectionsModule)
open Stacks.NonvanishingOpen (nonvanishingOpen)

attribute [local instance] globalSectionsModule

/-- The components of an snc divisor form an snc family. -/
private theorem isSNCFamily_idealSheaf_of_isSNC {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} {R : Type*} [Zero R] {D : MMP.Mori.DivisorWithCoeffs R X}
    (hD : D.IsSNC f) : IsSNCFamily f (fun E : D.support => E.1.idealSheaf) := by
  refine ⟨fun E => ⟨?_, isPureCodimOne_support_primeDivisor E.1, hD.1 E.1 E.2⟩, fun x => ?_⟩
  · haveI := E.1.integral
    infer_instance
  · obtain ⟨n, z, j, hz, hj, hI⟩ := hD.2 x
    refine ⟨n, z, fun E => j ⟨E.1.1, E.1.2, E.2⟩, hz, fun E => hI ⟨E.1.1, E.1.2, E.2⟩,
      fun E E' h => ?_⟩
    exact Subtype.ext (Subtype.ext (Subtype.mk.inj (hj h)))

/-- An irreducible component of a closed subset of pure codimension one is the closure of a
point of coheight one. -/
private theorem exists_coheight_eq_one_of_mem_componentsOf {X : Scheme.{u}}
    {Z : X.IdealSheafData} (hZ : MMP.Mori.IsPureCodimOne Z.support) {V : Set X}
    (hV : V ∈ componentsOf (Z.support : Set X)) :
    ∃ ξ : X, V = closure {ξ} ∧ Order.coheight ξ = 1 := by
  obtain ⟨ξ, -, hξ⟩ := Aux.exists_eq_closure_of_mem_componentsOf Z.support.isClosed hV
  refine ⟨ξ, hξ, ?_⟩
  rw [coheight_eq_codimension_closureSingleton]
  apply hZ
  refine ⟨?_, fun W' hW' hle => ?_⟩
  · change closure {ξ} ⊆ (Z.support : Set X)
    rw [← hξ]
    exact hV.1.2
  · have : (W' : Set X) ⊆ V := hV.2 ⟨W'.isIrreducible, hW'⟩ (by rw [hξ]; exact hle)
    change (W' : Set X) ⊆ closure {ξ}
    rw [← hξ]
    exact this

/-- Where a closed subscheme `Z` is cut out by one member `z m` of a regular system of
parameters, its irreducible components through the point are cut out by the same parameter, and
there is only one of them: the stalk of each such component is the prime `(z m)`, which pins
down its generic point. -/
private theorem stalk_componentsFamily_eq_span_and_unique {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] (Z : Y.IdealSheafData) {x : Y} {n : ℕ}
    {z : Fin n → Y.presheaf.stalk x} {m : Fin n} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    (hZx : IdealSheafData.stalk Z x = Ideal.span {z m}) (V : componentsOf (Z.support : Set Y))
    (hxV : x ∈ (V : Set Y)) :
    IdealSheafData.stalk (componentsFamily (Z.support : Set Y) V) x = Ideal.span {z m} ∧
      ∀ V' : componentsOf (Z.support : Set Y), x ∈ (V' : Set Y) → V' = V := by
  have hTy : Y.fromSpecStalk x ⁻¹' (Z.support : Set Y) =
      ⋃ t ∈ ({m} : Finset (Fin n)), PrimeSpectrum.zeroLocus {z t} := by
    haveI : Nonempty {i : Unit // x ∈ Z.support} := ⟨⟨(), V.2.1.2 hxV⟩⟩
    simpa only [Set.iUnion_const, Finset.set_biUnion_singleton] using
      preimage_fromSpecStalk_iUnion_support (fun _ : Unit => Z) x z (fun _ => m) (fun _ => hZx)
  obtain ⟨c, hc, hst, q, hq, hqc⟩ :=
    exists_stalk_componentsFamily_eq_span Z.support.isClosed hz hTy V hxV
  rw [Finset.mem_singleton] at hc
  refine ⟨hc ▸ hst, fun V' hxV' => ?_⟩
  obtain ⟨c', hc', -, q', hq', hqc'⟩ :=
    exists_stalk_componentsFamily_eq_span Z.support.isClosed hz hTy V' hxV'
  rw [Finset.mem_singleton] at hc'
  have hqq : q' = q := PrimeSpectrum.ext (by rw [hqc, hqc', hc, hc'])
  exact Subtype.ext (by rw [hq, hq', hqq])

variable {k : Type u} [Field k] {N : ℕ} {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
  {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L]

/-- The invertibility of `L` in the spelling the zero scheme takes. -/
local instance : SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L :=
  (inferInstance : Stacks.Ample.IsInvertibleModule Y L)

open Classical in
/-- **Bertini's theorem for simple normal crossings, in the space of sections.** Let `Y` be a
smooth variety over an algebraically closed field `k` of characteristic zero, `s₀, …, s_N`
global sections generating an invertible sheaf `L`, and `G` a simple normal crossing divisor on
`Y`. Then there is a dense open `U` of `𝔸ᴺ⁺¹_k` such that for every coefficient vector `c` with
`c ∈ U`, the zero scheme `Z` of `∑ᵢ cᵢ sᵢ` is smooth over `k`, and there is a finite set `T` of
prime divisors, whose supports are exactly the irreducible components of `Z`, none of them a
component of `G`, such that the reduced divisor with components `T` and those of `G` is simple
normal crossing. -/
@[mmp "lem_mmp_foundation_km5b_snc_bertini"]
public theorem exists_dense_open_smooth_zeroScheme_isSNC_add [IsAlgClosed k] [CharZero k]
    [IsSmoothVariety k (Y ↘ Spec (.of k))] {R : Type*} [Zero R]
    (s : Fin (N + 1) → Γ(L, ⊤))
    (hs : ⨆ c : Fin (N + 1) → k, nonvanishingOpen Y L (systemSection s c) = ⊤)
    (G : Mori.DivisorWithCoeffs R Y)
    (hG : G.IsSNC (Y ↘ Spec (.of k))) :
    ∃ U : (coefficientSpace k N).Opens, Dense (U : Set (coefficientSpace k N)) ∧
      ∀ c : Fin (N + 1) → k, coefficientPoint c ∈ U →
        Smooth ((zeroScheme Y L (systemSection s c)).subschemeι ≫ Y ↘ Spec (.of k)) ∧
        ∃ T : Finset (Mori.PrimeDivisor Y),
          (∀ Z : Set Y, Maximal (fun W : Set Y => IsIrreducible W ∧
              W ⊆ (zeroScheme Y L (systemSection s c)).support) Z ↔ ∃ E ∈ T, E.support = Z) ∧
          Disjoint T G.support ∧
          (∑ E ∈ T ∪ G.support, Finsupp.single E (1 : ℤ) : Mori.Divisor Y).IsSNC
            (Y ↘ Spec (.of k)) := by
  classical
  haveI : Smooth (𝟙 Y ≫ Y ↘ Spec (.of k)) := by rw [Category.id_comp]; infer_instance
  haveI : NoetherianSpace Y := Aux.noetherianSpace_of_finiteType (Y ↘ Spec (.of k))
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of k))
  have hfam : IsSNCFamily (𝟙 Y ≫ Y ↘ Spec (.of k)) (fun E : G.support => E.1.idealSheaf) := by
    rw [Category.id_comp]; exact isSNCFamily_idealSheaf_of_isSNC hG
  obtain ⟨⟨U, hU, hUc⟩, -⟩ := exists_dense_open_isSNCFamily_zeroScheme s hs (𝟙 Y) _ hfam
  refine ⟨U, hU, fun c hcU => ?_⟩
  obtain ⟨hsm, havoid, hsnc⟩ := hUc c hcU
  set Z := zeroScheme Y L (systemSection s c)
  simp only [Scheme.IdealSheafData.comap_id, Category.id_comp] at hsm havoid hsnc
  rw [Scheme.IdealSheafData.comap_id] at hsm
  have hZpure : MMP.Mori.IsPureCodimOne Z.support := (hsnc.1 none).2.1
  set C := componentsOf (Z.support : Set Y)
  have hfin : C.Finite := (Aux.finite_and_cover_componentsOf Z.support.isClosed).1
  haveI : Fintype C := hfin.fintype
  choose ξ hξV hξ1 using fun V : C => exists_coheight_eq_one_of_mem_componentsOf hZpure V.2
  let P : C → MMP.Mori.PrimeDivisor Y := fun V => PrimeDivisor.ofCoheightOne (ξ V) (hξ1 V)
  have hPsupp : ∀ V : C, (P V).support = V := fun V => by
    change ((Stacks.Chow.integralComponentAt (ξ V)).support : Set Y) = V
    rw [Stacks.Chow.coe_support_integralComponentAt, ← hξV]
  have hPideal : ∀ V : C, (P V).idealSheaf = componentsFamily (Z.support : Set Y) V := by
    intro V
    change Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({ξ V} : Set Y)) =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (V : Set Y))
    congr 1
    ext1
    rw [Closeds.coe_closure, Closeds.coe_closure, hξV V, closure_closure]
  let T : Finset (MMP.Mori.PrimeDivisor Y) := Finset.univ.image P
  have hTsub : ∀ E ∈ T, E.support ⊆ (Z.support : Set Y) := by
    intro E hE
    obtain ⟨V, -, rfl⟩ := Finset.mem_image.1 hE
    rw [hPsupp]
    exact V.2.1.2
  -- the stalk of a component of `Z` is that of `Z`, and only one component passes through
  have hloc : ∀ (x : Y) {n : ℕ} (z : Fin n → Y.presheaf.stalk x) (m : Fin n),
      MMP.Mori.IsRegularSystemOfParameters z →
      IdealSheafData.stalk Z x = Ideal.span {z m} → ∀ V : C, x ∈ (V : Set Y) →
      IdealSheafData.stalk (P V).idealSheaf x = Ideal.span {z m} ∧
        ∀ V' : C, x ∈ (V' : Set Y) → V' = V := fun x n z m hz hZx V hxV => by
    rw [hPideal]
    exact stalk_componentsFamily_eq_span_and_unique Z hz hZx V hxV
  refine ⟨hsm, T, fun W => ?_, ?_, ?_⟩
  · constructor
    · intro hW
      exact ⟨P ⟨W, hW⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hPsupp _⟩
    · rintro ⟨E, hE, rfl⟩
      obtain ⟨V, -, rfl⟩ := Finset.mem_image.1 hE
      rw [hPsupp]
      exact V.2
  · rw [Finset.disjoint_left]
    intro E hET hED
    have hirr : IsIrreducible E.support := by
      rw [PrimeDivisor.support_eq_closure]; exact isIrreducible_singleton.closure
    have hcomp : E.support ∈ componentsOf (⋂ i ∈ ({⟨E, hED⟩} : Set G.support),
        ((i.1.idealSheaf.support : Set Y))) := by
      simp only [Set.mem_singleton_iff, Set.iInter_iInter_eq_left]
      exact ⟨⟨hirr, le_rfl⟩, fun W hW _ => hW.2⟩
    exact havoid _ _ hcomp (hTsub E hET)
  · have hsupp : (∑ E ∈ T ∪ G.support, Finsupp.single E (1 : ℤ) :
        MMP.Mori.Divisor Y).support = T ∪ G.support := by
      ext E
      rw [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
      simp [Finsupp.single_apply]
      tauto
    rw [MMP.Mori.DivisorWithCoeffs.IsSNC, hsupp]
    refine ⟨fun E hE => ?_, fun x => ?_⟩
    · rcases Finset.mem_union.1 hE with hET | hED
      · obtain ⟨V, -, rfl⟩ := Finset.mem_image.1 hET
        refine isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ fun y hy => ?_
        have hyV : y ∈ (V : Set Y) := by rw [← hPsupp V]; exact hy
        obtain ⟨n, z, c, hz, hc, -⟩ := hsnc.2 y
        let i : {o : Option G.support //
            y ∈ ((fun o : Option G.support => o.elim Z fun E => E.1.idealSheaf) o).support} :=
          ⟨none, V.2.1.2 hyV⟩
        exact ⟨n, z, c i, hz, (hloc y z (c i) hz (hc i) V hyV).1⟩
      · exact hG.1 E hED
    · obtain ⟨n, z, c, hz, hc, hinj⟩ := hsnc.2 x
      have hmemT : ∀ E : {E : MMP.Mori.PrimeDivisor Y // E ∈ T ∪ G.support ∧ x ∈ E.support},
          E.1 ∉ G.support → E.1 ∈ T :=
        fun E h => (Finset.mem_union.1 E.2.1).resolve_right h
      have hcomp : ∀ E : {E : MMP.Mori.PrimeDivisor Y // E ∈ T ∪ G.support ∧ x ∈ E.support},
          E.1 ∉ G.support → ∃ V : C, x ∈ (V : Set Y) ∧ P V = E.1 := by
        intro E h
        obtain ⟨V, -, hV⟩ := Finset.mem_image.1 (hmemT E h)
        refine ⟨V, ?_, hV⟩
        rw [← hPsupp V, hV]
        exact E.2.2
      let j : {E : MMP.Mori.PrimeDivisor Y // E ∈ T ∪ G.support ∧ x ∈ E.support} → Fin n :=
        fun E => if h : E.1 ∈ G.support then c ⟨some ⟨E.1, h⟩, E.2.2⟩
          else c ⟨none, hTsub _ (hmemT E h) E.2.2⟩
      refine ⟨n, z, j, hz, fun E E' hEE' => ?_, fun E => ?_⟩
      · by_cases hE : E.1 ∈ G.support <;> by_cases hE' : E'.1 ∈ G.support
        · have h := hinj (show c _ = c _ from (dif_pos hE).symm.trans (hEE'.trans (dif_pos hE')))
          have h' := congrArg Subtype.val h
          simp only [Option.some.injEq] at h'
          exact Subtype.ext (Subtype.mk.inj h')
        · have h := hinj (show c _ = c _ from (dif_pos hE).symm.trans (hEE'.trans (dif_neg hE')))
          exact absurd (congrArg Subtype.val h) (by simp)
        · have h := hinj (show c _ = c _ from (dif_neg hE).symm.trans (hEE'.trans (dif_pos hE')))
          exact absurd (congrArg Subtype.val h) (by simp)
        · obtain ⟨V, hxV, hV⟩ := hcomp E hE
          obtain ⟨V', hxV', hV'⟩ := hcomp E' hE'
          have hZx := hc ⟨none, hTsub _ (hmemT E hE) E.2.2⟩
          have := (hloc x z _ hz hZx V hxV).2 V' hxV'
          subst this
          exact Subtype.ext (hV.symm.trans hV')
      · by_cases hE : E.1 ∈ G.support
        · have hjE : j E = c ⟨some ⟨E.1, hE⟩, E.2.2⟩ := dif_pos hE
          rw [hjE]
          exact hc ⟨some ⟨E.1, hE⟩, E.2.2⟩
        · have hjE : j E = c ⟨none, hTsub _ (hmemT E hE) E.2.2⟩ := dif_neg hE
          rw [hjE]
          obtain ⟨V, hxV, hV⟩ := hcomp E hE
          have := (hloc x z _ hz (hc ⟨none, hTsub _ (hmemT E hE) E.2.2⟩) V hxV).1
          rwa [hV] at this

end MMP.Threefold.Bridges

end

/-! ### A relatively ample divisor plus a large pull-back -/

section

open Filter

namespace MMP.Foundations

open MMP.Mori MMP.Fourfold

/-- The Cartier case: `𝒪_Z(H + cB)` is `(f ≫ g)`-ample for all large integers `c`.
This is Stacks Tag 0C4K, transported along `𝒪_Z(H + cB) ≅ 𝒪_Z(H) ⊗ f^*(𝒪_Y(A)^{⊗ c})`. -/
private theorem isRelativelyAmple_add_zsmul_of_cartier {Z Y S : Scheme.{u}} [IsNoetherian S]
    {f : Z ⟶ Y} {g : Y ⟶ S} (hf : IsProjective f) (hg : IsProjective g)
    {H : Z.CartierDivisor} (hH : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf H))
    {A : Y.CartierDivisor} (hA : MMP.Mori.IsRelativelyAmple g (MMP.CartierDivisor.sheaf A))
    {B : Z.CartierDivisor}
    (hB : Nonempty (MMP.CartierDivisor.sheaf B ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A))) :
    ∀ᶠ c : ℤ in atTop,
      MMP.Mori.IsRelativelyAmple (f ≫ g) (MMP.CartierDivisor.sheaf (H + c • B)) := by
  have hfqc : QuasiCompact f := by haveI := hf.isProper; infer_instance
  have hgqc : QuasiCompact g := by haveI := hg.isProper; infer_instance
  have hL : Stacks.RelativeAmple.IsRelativelyAmple f (MMP.CartierDivisor.sheaf H) :=
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover f _
      hfqc).mpr hH
  have hM : Stacks.RelativeAmple.IsRelativelyAmple g (MMP.CartierDivisor.sheaf A) :=
    (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_iff_exists_affine_isAmple_cover g _
      hgqc).mpr hA
  obtain ⟨n, hn⟩ := Stacks.AmplePullbackDatum.exists_threshold_isRelativelyAmple_comp f g _ _ hL hM
  refine eventually_atTop.mpr ⟨n, fun c hc => ?_⟩
  lift c to ℕ using (Int.natCast_nonneg n).trans hc
  have hc' : n ≤ c := by exact_mod_cast hc
  obtain ⟨eB⟩ := hB
  obtain ⟨eC⟩ := MMP.Fourfold.nonempty_lineBundle_int_smul_iso B (c : ℤ)
  have e : Stacks.AmplePullbackPart1.tensorPullbackPowModule f (MMP.CartierDivisor.sheaf H)
      (MMP.CartierDivisor.sheaf A) c ≅ MMP.CartierDivisor.sheaf (H + (c : ℤ) • B) :=
    Stacks.RelativeVeryAmple.tensorModulesMapIso Z (Iso.refl _)
        (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso f _ c ≪≫
          Stacks.RelativeVeryAmple.tensorPowModuleIsoOfIso Z _ _ eB.symm c ≪≫ eC.symm) ≪≫
      MMP.CartierDivisorSheaf.sheafMulIso H ((c : ℤ) • B)
  exact MMP.Mori.IsRelativelyAmple.of_stacks _ _
    ((Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ e).mp (hn c hc'))

/-- A `ℚ`-Cartier divisor with integral coefficients is the image of its integer floor. -/
private theorem eq_mapRange_floor {X : Scheme.{u}} {c : KCartierDivisor ℚ X}
    (hc : ∀ D, ∃ n : ℤ, c D = n) :
    c = (c.mapRange Int.floor (by simp)).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
  ext D
  obtain ⟨n, hn⟩ := hc D
  simp [hn]

/-- The realization of an integral `ℚ`-Cartier divisor is computed by any integral lift. -/
private theorem realization_eq_of_eq_mapRange {X : Scheme.{u}} {c : KCartierDivisor ℚ X}
    (hc : ∀ D, ∃ n : ℤ, c D = n) {n : X.CartierDivisor →₀ ℤ}
    (hn : c = n.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero) :
    MMP.Mori.KCartierDivisor.realization c hc = n.sum fun D k => k • D := by
  subst hn
  exact MMP.Mori.KCartierDivisor.realization_eq_sum n

/-- Realization is additive on integral `ℚ`-Cartier divisors. -/
private theorem realization_add {X : Scheme.{u}} {c c' : KCartierDivisor ℚ X}
    (hc : ∀ D, ∃ n : ℤ, c D = n) (hc' : ∀ D, ∃ n : ℤ, c' D = n)
    (h : ∀ D, ∃ n : ℤ, (c + c') D = n) :
    MMP.Mori.KCartierDivisor.realization (c + c') h =
      MMP.Mori.KCartierDivisor.realization c hc +
        MMP.Mori.KCartierDivisor.realization c' hc' := by
  rw [realization_eq_of_eq_mapRange hc (eq_mapRange_floor hc),
    realization_eq_of_eq_mapRange hc' (eq_mapRange_floor hc'),
    realization_eq_of_eq_mapRange h (n := c.mapRange Int.floor (by simp) +
      c'.mapRange Int.floor (by simp)) (by
        rw [Finsupp.mapRange_add (by simp)]
        exact congrArg₂ (· + ·) (eq_mapRange_floor hc) (eq_mapRange_floor hc')),
    Finsupp.sum_add_index' (h := fun (D : X.CartierDivisor) (k : ℤ) => k • D)
      (fun _ => zero_smul ℤ _) (fun _ _ _ => add_smul _ _ _)]

/-- `k • D`, for an integer `k`, is the image of the integral divisor `k • D`. -/
private theorem intCast_smul_ofCartier {X : Scheme.{u}} (k : ℤ) (D : X.CartierDivisor) :
    (k : ℚ) • KCartierDivisor.ofCartier ℚ D =
      (Finsupp.single D k).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
  simp [KCartierDivisor.ofCartier, Finsupp.smul_single]

/-- The realization of `k • D`, for an integer `k` and a Cartier divisor `D`, is `k • D`. -/
private theorem realization_intCast_smul_ofCartier {X : Scheme.{u}} (k : ℤ) (D : X.CartierDivisor)
    (h : ∀ E, ∃ n : ℤ, ((k : ℚ) • KCartierDivisor.ofCartier ℚ D) E = n) :
    MMP.Mori.KCartierDivisor.realization _ h = k • D := by
  rw [realization_eq_of_eq_mapRange h (intCast_smul_ofCartier k D),
    Finsupp.sum_single_index (h := fun (D : X.CartierDivisor) (k : ℤ) => k • D) (zero_smul ℤ _)]

/-- Let `S` be Noetherian, `f : Z ⟶ Y` and `g : Y ⟶ S` projective, `H` an `f`-ample `ℚ`-Cartier
divisor on `Z` and `A` a `g`-ample Cartier divisor on `Y`. If `B` is a Cartier divisor on `Z`
with `𝒪_Z(B) ≅ f^*𝒪_Y(A)`, then `H + c B` is `(f ≫ g)`-ample for all sufficiently large integers
`c`. -/
@[mmp "lem_mmp_foundation_relative_ample_plus_pullback_ample"]
public theorem isRelativelyAmpleQ_add_smul_pullback {Z Y S : Scheme.{u}} [IsNoetherian S]
    {f : Z ⟶ Y} {g : Y ⟶ S} (hf : IsProjective f) (hg : IsProjective g)
    {H : KCartierDivisor ℚ Z} (hH : KCartierDivisor.IsRelativelyAmpleQ f H)
    {A : Y.CartierDivisor} (hA : MMP.Mori.IsRelativelyAmple g (MMP.CartierDivisor.sheaf A))
    {B : Z.CartierDivisor}
    (hB : Nonempty (MMP.CartierDivisor.sheaf B ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf A))) :
    ∀ᶠ c : ℤ in atTop,
      KCartierDivisor.IsRelativelyAmpleQ (f ≫ g) (H + (c : ℚ) • KCartierDivisor.ofCartier ℚ B) := by
  obtain ⟨m, hm, hint, hamp⟩ := hH
  obtain ⟨N, hN⟩ := eventually_atTop.mp (isRelativelyAmple_add_zsmul_of_cartier hf hg hamp hA hB)
  refine eventually_atTop.mpr ⟨max N 0, fun c hc => ?_⟩
  have hmc : N ≤ m * c := le_trans (le_of_max_le_left hc)
    (le_mul_of_one_le_left (le_of_max_le_right hc) (by exact_mod_cast hm))
  have hsplit : (m : ℚ) • (H + (c : ℚ) • KCartierDivisor.ofCartier ℚ B) =
      (m : ℚ) • H + ((m * c : ℤ) : ℚ) • KCartierDivisor.ofCartier ℚ B := by
    rw [smul_add, smul_smul]; push_cast; rfl
  have hB' : ∀ E, ∃ n : ℤ, (((m * c : ℤ) : ℚ) • KCartierDivisor.ofCartier ℚ B) E = n := fun E =>
    ⟨_, by rw [intCast_smul_ofCartier]; rfl⟩
  have hsum : ∀ E, ∃ n : ℤ,
      ((m : ℚ) • H + ((m * c : ℤ) : ℚ) • KCartierDivisor.ofCartier ℚ B) E = n :=
    fun E => ⟨_, by rw [Finsupp.add_apply, (hint E).choose_spec, (hB' E).choose_spec,
      Int.cast_add]⟩
  refine ⟨m, hm, hsplit ▸ hsum, ?_⟩
  have hR := realization_add hint hB' hsum
  rw [realization_intCast_smul_ofCartier] at hR
  convert hN _ hmc using 3
  rw [← hR]
  congr 1

end MMP.Foundations

end

/-! ### An `f`-ample divisor plus a large ample pull-back is ample -/

section

open Filter
open Limits

namespace MMP.Foundations

/-- A morphism of projective `k`-varieties is projective. -/
private theorem isProjective_of_comp_eq {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX) : IsProjective f := by
  have : IsSeparated sY := hY.toIsVariety.toIsSeparated
  let γ : X ⟶ pullback sX sY := pullback.lift (𝟙 X) f (by simp [hf])
  have : IsClosedImmersion γ :=
    MorphismProperty.of_postcomp (W := @IsClosedImmersion) (W' := @IsSeparated) γ
      (pullback.fst sX sY) inferInstance (by simp only [γ, pullback.lift_fst]; infer_instance)
  have hγ : γ ≫ pullback.snd sX sY = f := pullback.lift_snd _ _ _
  rw [← hγ]
  exact ((MMP.isProjectiveMorphism_of_isClosedImmersion γ).comp
    (hX.isProjective.baseChange sY)).isProjective

/-- Relative ampleness of `𝒪_X(D)` depends only on the Cartier divisor `D`, whatever proof of
invertibility the instance argument carries. -/
private theorem isRelativelyAmple_lineBundle_congr {X Y : Scheme.{u}} {f : X ⟶ Y}
    {D D' : X.CartierDivisor} (e : D = D')
    [Stacks.Ample.IsInvertibleModule X (MMP.CartierDivisor.sheaf D)]
    [Stacks.Ample.IsInvertibleModule X (MMP.CartierDivisor.sheaf D')]
    (h : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf D)) :
    MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf D') := by
  subst e; exact h

/-- A `ℚ`-Cartier divisor with integral coefficients `n` is relatively ample exactly when some
positive multiple of the Cartier divisor `∑ n_D D` is. -/
private theorem isRelativelyAmpleQ_mapRange_intCast_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : X.CartierDivisor →₀ ℤ) :
    MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ f
        (n.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero) ↔
      ∃ m : ℕ, 0 < m ∧ MMP.Mori.IsRelativelyAmple f
        (MMP.CartierDivisor.sheaf (m • Finsupp.linearCombination ℤ id n)) := by
  have hc (m : ℕ) : (m : ℚ) • n.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero =
      ((m : ℤ) • n).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
    ext D; simp
  have key (m : ℕ)
      (h : ∀ E, ∃ k : ℤ, ((m : ℚ) • n.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero) E = k) :
      MMP.Mori.KCartierDivisor.realization _ h =
      m • Finsupp.linearCombination ℤ id n := by
    rw [realization_eq_of_eq_mapRange h (hc m), ← natCast_zsmul,
      ← map_smul (Finsupp.linearCombination ℤ id), Finsupp.linearCombination_apply]
    rfl
  refine ⟨fun ⟨m, hm, h, hA⟩ => ⟨m, hm, isRelativelyAmple_lineBundle_congr (key m h) hA⟩,
    fun ⟨m, hm, hA⟩ => ?_⟩
  have h : ∀ E, ∃ k : ℤ, ((m : ℚ) • n.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero) E = k :=
    fun E => ⟨((m : ℤ) • n) E, by rw [hc, Finsupp.mapRange_apply]⟩
  exact ⟨m, hm, h, isRelativelyAmple_lineBundle_congr (key m h).symm hA⟩

/-- Over the spectrum of a field, relative ampleness is ampleness. -/
private theorem isAmple_of_isRelativelyAmple {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (N : X.Modules) [Stacks.Ample.IsInvertibleModule X N]
    (h : MMP.Mori.IsRelativelyAmple s N) : Stacks.Ample.IsAmple X N := by
  obtain ⟨V, -, hyV, hA⟩ := h (IsLocalRing.closedPoint _)
  have hV : V = ⊤ := TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun z => by
    rw [Subsingleton.elim z (IsLocalRing.closedPoint _)]; exact hyV)
  subst hV
  have : IsIso (s ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens)).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact Stacks.RelativeAmpleAffineBase.isAmple_of_isAmple_modulePullback _ N hA

/-- Let `f : X ⟶ Y` be a morphism of projective `k`-varieties, `M` an ample Cartier divisor on
`Y` and `L` an `f`-ample Cartier divisor on `X`. If `B` is a Cartier divisor on `X` with
`𝒪_X(B) ≅ f^*𝒪_Y(M)`, then `L + ν B` is ample for all sufficiently large integers `ν`. -/
@[mmp "lem_mmp_foundation_km_relative_ample_plus_pullback"]
public theorem isAmple_add_zsmul_pullback (k : Type u) [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hY : MMP.Mori.IsProjectiveVariety k sY)
    {f : X ⟶ Y} (hf : f ≫ sY = sX)
    {M : Y.CartierDivisor} (hM : Stacks.Ample.IsAmple Y (MMP.CartierDivisor.sheaf M))
    {L : X.CartierDivisor} (hL : MMP.Mori.IsRelativelyAmple f (MMP.CartierDivisor.sheaf L))
    {B : X.CartierDivisor}
    (hB : Nonempty (MMP.CartierDivisor.sheaf B ≅
      (Scheme.Modules.pullback f).obj (MMP.CartierDivisor.sheaf M))) :
    ∀ᶠ ν : ℤ in atTop, Stacks.Ample.IsAmple X (MMP.CartierDivisor.sheaf (L + ν • B)) := by
  have : QuasiCompact sY := hY.toIsVariety.toQuasiCompact
  have hfp := isProjective_of_comp_eq hX hY hf
  have hgp : IsProjective sY := hY.isProjective.isProjective
  have hA : MMP.Mori.IsRelativelyAmple sY (MMP.CartierDivisor.sheaf M) :=
    MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sY _ hM
  have hH : MMP.Fourfold.KCartierDivisor.IsRelativelyAmpleQ f
      (MMP.Mori.KCartierDivisor.ofCartier ℚ L) := by
    have := (isRelativelyAmpleQ_mapRange_intCast_iff f (Finsupp.single L 1)).mpr
      ⟨1, one_pos, by simpa using hL⟩
    simpa [MMP.Mori.KCartierDivisor.ofCartier] using this
  filter_upwards [MMP.Foundations.isRelativelyAmpleQ_add_smul_pullback hfp hgp hH hA hB] with ν hν
  have e : MMP.Mori.KCartierDivisor.ofCartier ℚ L +
      (ν : ℚ) • MMP.Mori.KCartierDivisor.ofCartier ℚ B =
      (Finsupp.single L 1 + Finsupp.single B ν).mapRange (Int.cast : ℤ → ℚ) Int.cast_zero := by
    simp [MMP.Mori.KCartierDivisor.ofCartier, Finsupp.mapRange_add]
  rw [e, isRelativelyAmpleQ_mapRange_intCast_iff] at hν
  obtain ⟨m, hm, hamp⟩ := hν
  refine (MMP.Resolution.Bridges.isAmple_lineBundle_iff_nsmul _ m hm).mpr
    (isAmple_of_isRelativelyAmple (f ≫ sY) _ ?_)
  simpa using hamp

end MMP.Foundations

end

/-! ### A smooth member of a very ample linear system -/

section

open MMP.Threefold.Bridges

namespace MMP.Intersection

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.globalSectionsModule

/-- A dense open of the coefficient space `𝔸ᴺ⁺¹_k` over an infinite field contains a `k`-point
`c` at which a given nonzero polynomial does not vanish. -/
private theorem exists_coefficientPoint_mem_and_eval_ne_zero {k : Type u} [Field k] [Infinite k]
    {N : ℕ} (U : (coefficientSpace k N).Opens) (hU : Dense (U : Set (coefficientSpace k N)))
    {g : MvPolynomial (Fin (N + 1)) k} (hg : g ≠ 0) :
    ∃ c : Fin (N + 1) → k, coefficientPoint c ∈ U ∧ MvPolynomial.eval c g ≠ 0 := by
  haveI : Nonempty (coefficientSpace k N) := ⟨coefficientPoint 0⟩
  obtain ⟨p, hp⟩ := hU.nonempty
  obtain ⟨_, ⟨f, rfl⟩, hpf, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp U.2
  have hf : f ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hpf (Submodule.zero_mem _)
  obtain ⟨c, hc⟩ : ∃ c, MvPolynomial.eval c (f * g) ≠ 0 := by
    by_contra h
    push Not at h
    exact mul_ne_zero hf hg (MvPolynomial.funext fun c => by simpa using h c)
  rw [map_mul] at hc
  refine ⟨c, hfU ?_, right_ne_zero_of_mul hc⟩
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr fun h => left_ne_zero_of_mul hc h

/-- For a nonzero `k`-linear map `φ` out of `kᴺ⁺¹` there is a nonzero polynomial (a linear form
vanishing on the kernel of `φ`) whose non-vanishing forces `φ c ≠ 0`. -/
private theorem exists_polynomial_ne_zero_of_linearMap_ne_zero {k : Type u} [Field k] {N : ℕ}
    {M : Type*} [AddCommGroup M] [Module k M] (φ : (Fin (N + 1) → k) →ₗ[k] M) (hφ : φ ≠ 0) :
    ∃ ℓ : MvPolynomial (Fin (N + 1)) k, ℓ ≠ 0 ∧
      ∀ c, MvPolynomial.eval c ℓ ≠ 0 → φ c ≠ 0 := by
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, φ c₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  obtain ⟨ψ, hψc, hψK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
    (p := LinearMap.ker φ) (x := c₀) (by simpa using hc₀) inferInstance
  set ℓ : MvPolynomial (Fin (N + 1)) k :=
    ∑ j, MvPolynomial.C (ψ (Pi.single j 1)) * MvPolynomial.X j
  have hev : ∀ c, MvPolynomial.eval c ℓ = ψ c := by
    intro c
    conv_rhs => rw [pi_eq_sum_univ c]
    simp only [ℓ, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_smul,
      smul_eq_mul, mul_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  refine ⟨ℓ, fun h => hψc (by rw [← hev, h, map_zero]), fun c hc hφc => hc ?_⟩
  rw [hev]
  have : ψ c ∈ (LinearMap.ker φ).map ψ := ⟨c, hφc, rfl⟩
  rw [hψK] at this
  exact this

/-- A very ample line bundle is generated by finitely many global sections: the pullbacks of the
homogeneous coordinates `T₀, …, T_N` along the embedding `X ↪ ℙᴺ_k`, since `Tⱼ` does not vanish on
`D₊(Tⱼ)` and these opens cover `ℙᴺ_k`. -/
private theorem exists_sections_cover_of_isVeryAmple {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] {L : X.Modules} (hL : IsVeryAmple k L) :
    ∃ (N : ℕ) (σ : Fin (N + 1) → Γ(L, ⊤)),
      ∀ x : X, ∃ j, x ∈ Stacks.Ample.nonvanishingLocus L (σ j) := by
  obtain ⟨N, ι, -, -, ⟨e⟩⟩ := hL
  set 𝒮 := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (N + 1))) k
  have hwhere : Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible 𝒮 1 = ⊤ :=
    (Stacks.AlgebraicGeometry.GoodOpenClose.whereInvertible_eq_ratioLocus 𝒮 1).trans
      (Stacks.AlgebraicGeometry.ProjShared.ratioLocus_eq_top_of_adjoin_degree_one 𝒮
        (Stacks.AlgebraicGeometry.TwistFlatness.adjoin_degree_one_homogeneousSubmodule _ k) 1)
  let t := fun j : Fin (N + 1) => ProjectiveSpectrum.Proj.degreeSection 𝒮 (1 * 1)
      ⟨MvPolynomial.X (ULift.up j), Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one _⟩
  refine ⟨N, fun j => e.inv.app ⊤ (pullbackGlobalSections ι (ProjSpace.twistOne k _) (t j)),
    fun x => ?_⟩
  have hx : ι.base x ∈ (⨆ i : ULift.{u} (Fin (N + 1)),
      Proj.basicOpen 𝒮 (MvPolynomial.X i)) := by
    rw [Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top]; trivial
  obtain ⟨⟨j⟩, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have h := (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    𝒮 1 1 ⟨MvPolynomial.X (ULift.up j), Stacks.SymmetricAway.X_mem_homogeneousSubmodule_one _⟩
    (x := ι.base x) (by rw [hwhere]; trivial)).mpr hj
  exact ⟨j, Stacks.Ample.nonvanishingLocus_congr e.symm
    (pullbackGlobalSections ι (ProjSpace.twistOne k _) (t j)) ▸
      Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections ι _ _ h⟩

/-- **A smooth member of a very ample system.** Let `X` be a smooth projective variety over an
algebraically closed field `k` of characteristic zero and `A` a very ample Cartier divisor on `X`.
Then there is a non-zero `s ∈ H⁰(X, 𝒪_X(A))` whose zero scheme is smooth over `k`. -/
@[mmp "lem_mmp_foundation_km_very_ample_smooth_member"]
public theorem exists_ne_zero_smooth_zeroScheme_of_isVeryAmpleDivisor (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsSmoothVariety k (X ↘ Spec (.of k))] [IsProjectiveVariety k (X ↘ Spec (.of k))]
    (A : X.CartierDivisor) (hA : IsVeryAmpleDivisor k A) :
    ∃ s : H0 k (MMP.CartierDivisor.sheaf A), s ≠ 0 ∧
      Smooth ((@zeroScheme X (MMP.CartierDivisor.sheaf A)
          (MMP.CartierDivisor.isInvertibleModule_sheaf A) s).subschemeι ≫
        X ↘ Spec (.of k)) := by
  haveI : Infinite k := IsAlgClosed.instInfinite
  obtain ⟨N, σ, hcov⟩ := exists_sections_cover_of_isVeryAmple hA
  have hsingle : ∀ j, systemSection (k := k) σ (Pi.single j 1) = σ j := fun j => by
    simp [systemSection, Fintype.linearCombination_apply_single]
  have hs : ⨆ c : Fin (N + 1) → k, Stacks.NonvanishingOpen.nonvanishingOpen X
      (MMP.CartierDivisor.sheaf A)
      (systemSection σ c) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨j, hj⟩ := hcov x
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨Pi.single j 1, ?_⟩
    rwa [Stacks.NonvanishingOpen.mem_nonvanishingOpen, hsingle]
  have hφ : systemSection (k := k) σ ≠ 0 := by
    intro h0
    obtain ⟨j, hj⟩ := hcov (Classical.arbitrary X)
    rwa [← hsingle j, h0, LinearMap.zero_apply, Stacks.Ample.nonvanishingLocus_zero] at hj
  -- Bertini with no auxiliary subvarieties to keep transverse to
  let ιY : (i : PEmpty.{u + 1}) → (i.elim : Scheme.{u}) ⟶ X := fun i => i.elim
  haveI : ∀ i, IsImmersion (ιY i) := fun i => i.elim
  haveI : ∀ i, Smooth (ιY i ≫ X ↘ Spec (.of k)) := fun i => i.elim
  obtain ⟨⟨U, hUd, hU⟩, -⟩ := exists_dense_open_smooth_zeroScheme σ hs ιY
  obtain ⟨ℓ, hℓ, hℓφ⟩ := exists_polynomial_ne_zero_of_linearMap_ne_zero _ hφ
  obtain ⟨c, hcU, hc⟩ := exists_coefficientPoint_mem_and_eval_ne_zero U hUd hℓ
  exact ⟨systemSection σ c, hℓφ c hc, (hU c hcU).1 inferInstance⟩

end MMP.Intersection

end

/-! ### Finite blow-up sequences are projective -/

section

namespace MMP.Resolution.ClosedBlowupSequence

/-- The blow-down map of a Noetherian scheme is projective. -/
private theorem isProjective_blowUpToBase {Y : Scheme.{u}} [hY : IsNoetherian Y]
    (W : Y.IdealSheafData) : IsProjective (blowUpToBase W) :=
  have := hY.toIsLocallyNoetherian
  Stacks.Blowup.isProjective_blowUpToBase W (TwoStepTower.isFiniteType_of_isLocallyNoetherian W)

/-- The blow-up of a Noetherian scheme is Noetherian: it is proper over the base. -/
private theorem isNoetherian_blowUp {Y : Scheme.{u}} [hY : IsNoetherian Y]
    (W : Y.IdealSheafData) : IsNoetherian (blowUp W) :=
  have := hY.toIsLocallyNoetherian
  have := hY.toCompactSpace
  have := (isProper_blowUpToBase (I := W)).toLocallyOfFiniteType
  @AlgebraicGeometry.IsNoetherian.mk _ (LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase W))
    (QuasiCompact.compactSpace_of_compactSpace (blowUpToBase W))

/-- The composite `Π = B.toBase : X_r ⟶ X` of a blow-up sequence starting with a Noetherian
scheme `X` is projective. -/
@[mmp "lem_mmp_foundation_kr_finite_blowup_sequence_projective"]
public theorem isProjective_toBase {X : Scheme.{u}} [IsNoetherian X]
    (B : ClosedBlowupSequence X) : IsProjective B.toBase :=
  match X, ‹IsNoetherian X›, B with
  | X, _, .nil _ => (MMP.isProjectiveMorphism_of_isClosedImmersion (𝟙 X)).isProjective
  | X, hX, .cons Z B =>
    have := hX.toIsLocallyNoetherian
    have := hX.toCompactSpace
    (@isProjective_toBase _ (isNoetherian_blowUp Z) B).comp (isProjective_blowUpToBase Z)

end MMP.Resolution.ClosedBlowupSequence

end

/-! ### Dense constructible sets -/

section

namespace MMP

open Set

/-- In a preirreducible space, a constructible set or its complement has dense interior. -/
private lemma dense_interior_or_dense_interior_compl {X : Type*} [TopologicalSpace X]
    [PreirreducibleSpace X] {s : Set X} (hs : Topology.IsConstructible s) :
    Dense (interior s) ∨ Dense (interior sᶜ) := by
  induction hs using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    rcases U.eq_empty_or_nonempty with h | h
    · right; simp [h]
    · left; rw [hU.interior_eq]; exact hU.dense h
  | union s _ t _ hs' ht' =>
    rcases hs' with h | h
    · exact .inl (h.mono (interior_mono subset_union_left))
    rcases ht' with h' | h'
    · exact .inl (h'.mono (interior_mono subset_union_right))
    right
    rw [compl_union, interior_inter]
    exact h.inter_of_isOpen_left h' isOpen_interior
  | compl s _ hs' => rw [compl_compl]; exact hs'.symm

/-- In a preirreducible space, a dense constructible set contains a dense open set. -/
public theorem _root_.Topology.IsConstructible.exists_isOpen_dense_subset {X : Type*}
    [TopologicalSpace X] [PreirreducibleSpace X] {s : Set X} (hs : Topology.IsConstructible s)
    (hd : Dense s) :
    ∃ U : Set X, IsOpen U ∧ Dense U ∧ U ⊆ s := by
  refine ⟨interior s, isOpen_interior, ?_, interior_subset⟩
  rcases dense_interior_or_dense_interior_compl hs with h | h
  · exact h
  · rw [interior_compl, hd.closure_eq, compl_univ] at h
    exact h.mono (empty_subset _)

/-- **Chevalley's theorem and dense constructible sets.** The image of a constructible set under
a quasi-compact morphism locally of finite presentation into a quasi-compact quasi-separated
scheme is constructible; and a dense constructible subset of an irreducible scheme contains a
dense open subset. -/
@[mmp "lem_mmp_foundation_laz_chevalley_constructible"]
public theorem isConstructible_image_and_exists_isOpen_dense_subset :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [QuasiCompact f]
        [CompactSpace Y] [QuasiSeparatedSpace Y] {s : Set X},
        Topology.IsConstructible s → Topology.IsConstructible (f '' s)) ∧
    (∀ (X : Scheme.{u}) [IrreducibleSpace X] {s : Set X},
        Topology.IsConstructible s → Dense s → ∃ U : Set X, IsOpen U ∧ Dense U ∧ U ⊆ s) :=
  ⟨fun f _ _ _ _ _ hs ↦ f.isConstructible_image hs,
    fun _ _ _ hs hd ↦ hs.exists_isOpen_dense_subset hd⟩

end MMP

end
