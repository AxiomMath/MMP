/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Resolution.DisjoiningSequence
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Functor
public import MMP.AlgebraicGeometry.Resolution.SNCFieldChange
public import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct

/-!
# Functoriality of the principalization construction (Kollár, *Resolution*, 3.72)

Let `𝓑` be a blow-up sequence functor on the marked triples `(X, I, 1, E)` of marking `1`, and
`𝓑𝓟_𝓑` the construction of Kollár 3.72: the disjoining sequence of `(X, E)`, ending in
`π : X' → X` with ordered divisor `E_{X'}`, followed by `𝓑(X', π^*I, 1, E_{X'})`, with empty
blow-ups deleted. We show that `𝓑𝓟_𝓑` commutes with smooth morphisms when `𝓑` does, and with
change of fields when `𝓑` commutes with isomorphisms and with change of fields; this is part (4)
of the principalization theorem 3.35 for `𝓑𝓟_𝓑`.

Both proofs are one argument applied to a morphism `h : Y → X` that is flat, universally open,
and has reduced base changes to reduced schemes (`IsReducedFlatBaseChange`): smooth morphisms
and the projections `X_L → X` of a field extension of a perfect field are of this kind. Blowing
up commutes with flat base change ([Stacks, Tag 0805]), so the canonical lifts of `h` along the
blow-ups are base changes of `h`, again of this kind. For such `h` the inverse image of a reduced
closed subscheme is the reduced subscheme on the inverse image, and, `h` being open, the inverse
image of a closure is the closure of the inverse image. Hence the centre `Z_j` of each step of
the disjoining sequence, the transforms `π_j⁻¹(E_i^{(j)} ∖ Z_j)‾`, `π_j⁻¹(F^{l,(j)} ∖ Z_j)‾`, the
exceptional divisor `π_j⁻¹(Z_j)` and the reduced union `E^0` pull back to the corresponding
objects for `(Y, h⁻¹E)`: the disjoining sequence of `(Y, h⁻¹E)` is the pull-back of that of
`(X, E)` and `E_{Y'} = h'⁻¹E_{X'}`, `h' : Y' → X'` the last morphism of the pull-back
(`disjoiningSequence_comap`). The `𝓑` parts then compare through the hypothesis on `𝓑`, and
pulling back commutes with concatenation and, up to deleting empty blow-ups, with reduction.

## Main definitions

* `MMP.Resolution.IsReducedFlatBaseChange`: flat, universally open morphisms with reduced base
  changes to reduced schemes.
* `MMP.Resolution.DisjoiningStage.pullback`: the pull-back of a stage of the disjoining
  construction.
* `MMP.Resolution.principalizationConstructionOnTriples`: `𝓑𝓟_𝓑` on the triples of 3.64.

## Main results

* `MMP.Resolution.disjoiningSequence_comap`: the disjoining sequence commutes with flat base
  change with reduced base changes.
* `MMP.Resolution.principalizationConstruction_comap`: the common part of the two
  functoriality statements.
* `MMP.Resolution.commutesWithSmoothOn_principalizationConstruction`: `𝓑𝓟_𝓑` commutes with
  smooth morphisms.
* `MMP.Resolution.commutesWithFieldChangeOn_principalizationConstruction_of_iso`: `𝓑𝓟_𝓑`
  commutes with change of fields when `𝓑` commutes with isomorphisms and change of fields.
* `MMP.Resolution.commutesWithFieldChangeOn_principalizationConstruction`: `𝓑𝓟_𝓑` commutes with
  change of fields when `𝓑` commutes with smooth morphisms and change of fields.

## Implementation notes

The construction `𝓑𝓟_𝓑` applies `𝓑` only when `(X', π^*I, 1, E_{X'})` is a marked triple, which
asks `X'` to be equidimensional, and returns the disjoining sequence otherwise. Both results are
therefore stated on the triples of 3.64 (`MMP.Resolution.triples`), the snc triples with `X`
equidimensional (`MMP.Resolution.mem_triples_iff`). On all snc triples the smooth statement
fails: for `X = 𝔸¹`, `I` the ideal of a point and `E = ()`, the smooth surjection
`Y = 𝔸¹ ⊔ 𝔸² → 𝔸¹` (the identity and a projection) has `Y` not equidimensional, so
`𝓑𝓟_𝓑(Y, h^*I, ()) = ()`, while `𝓑𝓟_𝓑(X, I, ()) = 𝓑(X, I, 1, ())` is nonempty for every order
reduction functor `𝓑`, and so is its pull-back.

The disjoining sequence counts the entries of the ordered divisor, and the inverse image `h⁻¹E`
has the same entries as `E`, possibly empty; no level of the disjoining sequence is shifted, and
the hypothesis that `𝓑` ignores empty entries is not needed. In the field-change statement
`X'_L` and the end of the disjoining sequence of `(X_L, E_L)` are isomorphic but different
schemes (the second is `B_{Z_L}X_L`, the first `(B_ZX)_L`), so `𝓑` is assumed to commute with
isomorphisms, as it does when it commutes with smooth morphisms.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.34, 3.35, 3.72]
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Pull-backs and reductions of blow-up sequences -/

namespace ClosedBlowupSequence

/-- The pull-back of a concatenation is the concatenation of the pull-backs. -/
theorem append_pullback : ∀ {X Y : Scheme.{u}} (D : ClosedBlowupSequence X)
    (C : ClosedBlowupSequence D.target) (h : Y ⟶ X),
    (D.append C).pullback h = (D.pullback h).append (C.pullback (D.pullbackHom h))
  | _, _, nil _, _, _ => rfl
  | _, _, cons Z D, C, h => by
    change cons _ ((D.append C).pullback _) = cons _ ((D.pullback _).append _)
    rw [append_pullback D C]
    rfl

/-- `eqToHom` along `Z' = Z` followed by `blowUpToBase Z` is `blowUpToBase Z'`. -/
theorem eqToHom_comp_blowUpToBase {X : Scheme.{u}} {Z Z' : X.IdealSheafData} (e : Z' = Z) :
    eqToHom (congrArg blowUp e) ≫ blowUpToBase Z = blowUpToBase Z' := by
  subst e; simp

/-- The canonical lift of a composite is the composite of the canonical lifts. -/
theorem canonicalLift_comp_canonicalLift {X W Y : Scheme.{u}} (g : W ⟶ X) (h : Y ⟶ W)
    (Z : X.IdealSheafData) :
    canonicalLift h (Z.comap g) ≫ canonicalLift g Z =
      eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z h g).symm) ≫
        canonicalLift (h ≫ g) Z := by
  have hc : Stacks.Blowup.IsCartierOver Z
      (Over.mk (blowUpToBase ((Z.comap g).comap h) ≫ h ≫ g)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor
      (Z.comap (blowUpToBase ((Z.comap g).comap h) ≫ h ≫ g))
    rw [← Category.assoc, Scheme.IdealSheafData.comap_comp]
    exact isCartierOver_blowUpToBase_comp h (Z.comap g)
  rw [blowUpLift_unique Z _ hc (canonicalLift h (Z.comap g) ≫ canonicalLift g Z) (by
      rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
        canonicalLift_comp_blowUpToBase, Category.assoc]),
    blowUpLift_unique Z _ hc (eqToHom _ ≫ canonicalLift (h ≫ g) Z) (by
      rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc,
        eqToHom_comp_blowUpToBase (Scheme.IdealSheafData.comap_comp Z h g).symm])]

/-- `blowUpLift` along the empty centre `(Z.comap g).comap h`, followed by `canonicalLift g Z`,
is `blowUpLift` along `Z.comap (h ≫ g)`. -/
theorem blowUpLift_comp_canonicalLift {X W Y : Scheme.{u}} (g : W ⟶ X) (h : Y ⟶ W)
    (Z : X.IdealSheafData) (hZ : (Z.comap g).comap h = ⊤) (hZ' : Z.comap (h ≫ g) = ⊤) :
    blowUpLift (Z.comap g) h (isCartierOver_of_comap_eq_top h _ hZ) ≫ canonicalLift g Z =
      blowUpLift Z (h ≫ g) (isCartierOver_of_comap_eq_top _ _ hZ') :=
  blowUpLift_unique _ _ _ _ (by
    rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, blowUpLift_comp])

/-- `pullbackReduced` along `h` after `pullbackReduced` along `g` is `pullbackReduced` along
`h ≫ g`. -/
theorem pullbackReduced_pullbackReduced_heq {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    ∀ {W Y Y' : Scheme.{u}} (g : W ⟶ X) (h : Y ⟶ W) (k : Y' ⟶ X) (e : Y = Y'),
      eqToHom e ≫ k = h ≫ g → (S.pullbackReduced g).pullbackReduced h ≍ S.pullbackReduced k := by
  induction S with
  | nil X => intro W Y Y' g h k e _; subst e; rfl
  | cons Z S ih =>
    intro W Y Y' g h k e hk
    subst e
    simp only [eqToHom_refl, Category.id_comp] at hk
    subst hk
    by_cases hg : Z.comap g = ⊤
    · have hk : Z.comap (h ≫ g) = ⊤ := by
        rw [Scheme.IdealSheafData.comap_comp, hg, Scheme.IdealSheafData.comap_top]
      simp only [pullbackReduced, hg, hk, dite_true]
      exact ih _ _ _ rfl (by
        rw [eqToHom_refl, Category.id_comp]
        exact (blowUpLift_unique _ _ _ _ (by rw [Category.assoc, blowUpLift_comp])).symm)
    · by_cases hgh : (Z.comap g).comap h = ⊤
      · have hk : Z.comap (h ≫ g) = ⊤ := by rw [Scheme.IdealSheafData.comap_comp, hgh]
        simp only [pullbackReduced, hg, hgh, hk, dite_true, dite_false]
        exact ih _ _ _ rfl (by
          rw [eqToHom_refl, Category.id_comp, blowUpLift_comp_canonicalLift g h Z hgh hk])
      · have hk : Z.comap (h ≫ g) ≠ ⊤ := by rw [Scheme.IdealSheafData.comap_comp]; exact hgh
        simp only [pullbackReduced, hg, hgh, hk, dite_false]
        refine heq_of_eq (cons_eq_cons_iff.2 ⟨(Scheme.IdealSheafData.comap_comp Z h g).symm, ?_⟩)
        exact ih _ _ _ (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z h g).symm)
          (canonicalLift_comp_canonicalLift g h Z).symm

/-- `pullbackReduced` along `h` after the pull-back along `g` is `pullbackReduced` along
`h ≫ g`. -/
theorem pullback_pullbackReduced_heq {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    ∀ {W Y Y' : Scheme.{u}} (g : W ⟶ X) (h : Y ⟶ W) (k : Y' ⟶ X) (e : Y = Y'),
      eqToHom e ≫ k = h ≫ g → (S.pullback g).pullbackReduced h ≍ S.pullbackReduced k := by
  induction S with
  | nil X => intro W Y Y' g h k e _; subst e; rfl
  | cons Z S ih =>
    intro W Y Y' g h k e hk
    subst e
    simp only [eqToHom_refl, Category.id_comp] at hk
    subst hk
    by_cases hgh : (Z.comap g).comap h = ⊤
    · have hk : Z.comap (h ≫ g) = ⊤ := by rw [Scheme.IdealSheafData.comap_comp, hgh]
      simp only [pullback, pullbackReduced, hgh, hk, dite_true]
      exact ih _ _ _ rfl (by
        rw [eqToHom_refl, Category.id_comp, blowUpLift_comp_canonicalLift g h Z hgh hk])
    · have hk : Z.comap (h ≫ g) ≠ ⊤ := by rw [Scheme.IdealSheafData.comap_comp]; exact hgh
      simp only [pullback, pullbackReduced, hgh, hk, dite_false]
      refine heq_of_eq (cons_eq_cons_iff.2 ⟨(Scheme.IdealSheafData.comap_comp Z h g).symm, ?_⟩)
      exact ih _ _ _ (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z h g).symm)
        (canonicalLift_comp_canonicalLift g h Z).symm

/-- The pull-back along `h` after the pull-back along `g` is the pull-back along `h ≫ g`. -/
theorem pullback_pullback_heq {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    ∀ {W Y Y' : Scheme.{u}} (g : W ⟶ X) (h : Y ⟶ W) (k : Y' ⟶ X) (e : Y = Y'),
      eqToHom e ≫ k = h ≫ g → (S.pullback g).pullback h ≍ S.pullback k := by
  induction S with
  | nil X => intro W Y Y' g h k e _; subst e; rfl
  | cons Z S ih =>
    intro W Y Y' g h k e hk
    subst e
    simp only [eqToHom_refl, Category.id_comp] at hk
    subst hk
    simp only [pullback]
    refine heq_of_eq (cons_eq_cons_iff.2 ⟨(Scheme.IdealSheafData.comap_comp Z h g).symm, ?_⟩)
    exact ih _ _ _ (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z h g).symm)
      (canonicalLift_comp_canonicalLift g h Z).symm

/-- `(h^*𝐁)^{red}` is the pull-back of `𝐁` along `h` with empty blow-ups deleted. -/
theorem reduction_pullback {X Y : Scheme.{u}} (S : ClosedBlowupSequence X) (h : Y ⟶ X) :
    (S.pullback h).reduction = S.pullbackReduced h :=
  eq_of_heq (S.pullback_pullbackReduced_heq h (𝟙 Y) h rfl (by simp))

/-- `pullbackReduced` along `h` only depends on the reduction. -/
theorem pullbackReduced_reduction {X Y : Scheme.{u}} (S : ClosedBlowupSequence X)
    (h : Y ⟶ X) : S.reduction.pullbackReduced h = S.pullbackReduced h :=
  eq_of_heq (S.pullbackReduced_pullbackReduced_heq (𝟙 X) h h rfl (by simp))

/-- `((𝐁^{red})^* h)^{red} = (h^*𝐁)^{red}`: deleting empty blow-ups before or after pulling back
gives the same result. -/
theorem reduction_pullback_reduction {X Y : Scheme.{u}} (S : ClosedBlowupSequence X)
    (h : Y ⟶ X) : (S.reduction.pullback h).reduction = (S.pullback h).reduction := by
  rw [reduction_pullback, reduction_pullback, pullbackReduced_reduction]

/-- The reduction of a reduction is itself. -/
theorem reduction_reduction {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    S.reduction.reduction = S.reduction :=
  reduction_eq_self (hasNoEmptyBlowups_reduction S)

/-- Concatenations with sequences of equal reductions have equal `pullbackReduced`. -/
theorem pullbackReduced_append_congr : ∀ {X Y : Scheme.{u}} (D : ClosedBlowupSequence X)
    {C C' : ClosedBlowupSequence D.target}, C.reduction = C'.reduction → ∀ (f : Y ⟶ X),
    (D.append C).pullbackReduced f = (D.append C').pullbackReduced f
  | _, _, nil _, C, C', hC, f =>
    (pullbackReduced_reduction C f).symm.trans
      ((congrArg (fun S => pullbackReduced S f) hC).trans (pullbackReduced_reduction C' f))
  | _, _, cons Z D, C, C', hC, f => by
    change (cons Z (D.append C)).pullbackReduced f = (cons Z (D.append C')).pullbackReduced f
    by_cases hZ : Z.comap f = ⊤
    · simp only [pullbackReduced, hZ, dite_true]
      exact pullbackReduced_append_congr D hC _
    · simp only [pullbackReduced, hZ, dite_false]
      rw [pullbackReduced_append_congr D hC]

/-- `(𝐃 ⋅ 𝐂^{red})^{red} = (𝐃 ⋅ 𝐂)^{red}`. -/
theorem reduction_append_congr {X : Scheme.{u}} (D : ClosedBlowupSequence X)
    {C C' : ClosedBlowupSequence D.target} (hC : C.reduction = C'.reduction) :
    (D.append C).reduction = (D.append C').reduction :=
  pullbackReduced_append_congr D hC _

/-- The pull-back of a blow-up sequence without empty blow-ups along a flat surjective morphism
has no empty blow-ups. -/
theorem hasNoEmptyBlowups_pullback {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    S.HasNoEmptyBlowups → ∀ {Y : Scheme.{u}} (h : Y ⟶ X) [Flat h] [Surjective h],
      (S.pullback h).HasNoEmptyBlowups := by
  induction S with
  | nil X => intros; trivial
  | cons Z S ih =>
    intro hS Y h _ _
    refine ⟨fun hZ => hS.1 ?_, ?_⟩
    · rw [← Scheme.IdealSheafData.support_eq_bot_iff] at hZ ⊢
      refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨y, rfl⟩ := h.surjective x
      have : y ∈ ((Z.comap h).support : Set Y) := by
        rw [Scheme.IdealSheafData.support_comap]; exact hx
      rw [hZ] at this
      exact this
    · have := Kollar.flat_canonicalLift h Z
      have : Surjective (canonicalLift h Z) :=
        MorphismProperty.of_isPullback (P := @Surjective)
          (Kollar.isPullback_canonicalLift_of_flat h Z) ‹_›
      exact ih hS.2 _

end ClosedBlowupSequence

/-! ### Flat morphisms with reduced base changes -/

/-- `IsReducedFlatBaseChange h` says that `h : Y → X` is flat and universally open and that
every base change of `h` to a reduced scheme is reduced. Smooth morphisms
(`IsReducedFlatBaseChange.of_smooth`) and the projections `X_L → X` of a field extension `L/K`
of a perfect field (`IsReducedFlatBaseChange.fieldChange`) are of this kind, and the class is
stable under base change (`IsReducedFlatBaseChange.of_isPullback`). -/
structure IsReducedFlatBaseChange {X Y : Scheme.{u}} (h : Y ⟶ X) : Prop where
  /-- The morphism `h` is flat. -/
  flat : Flat h
  /-- The morphism `h` is universally open. -/
  universallyOpen : UniversallyOpen h
  /-- Every base change of `h` along a morphism from a reduced scheme is reduced. -/
  isReduced : ∀ {T P : Scheme.{u}} (a : T ⟶ X) (p₁ : P ⟶ T) (p₂ : P ⟶ Y),
    IsPullback p₁ p₂ a h → IsReduced T → IsReduced P

namespace IsReducedFlatBaseChange

variable {X Y : Scheme.{u}} {h : Y ⟶ X}

/-- A base change of a flat morphism with reduced base changes is one. -/
theorem of_isPullback {X' Y' : Scheme.{u}} {h' : Y' ⟶ X'} {f : X' ⟶ X} {f' : Y' ⟶ Y}
    (sq : IsPullback f' h' h f) (hh : IsReducedFlatBaseChange h) :
    IsReducedFlatBaseChange h' where
  flat := have := hh.flat; MorphismProperty.of_isPullback (P := @Flat) sq ‹_›
  universallyOpen := have := hh.universallyOpen
    MorphismProperty.of_isPullback (P := @UniversallyOpen) sq ‹_›
  isReduced a p₁ p₂ hp hT := hh.isReduced (a ≫ f) p₁ (p₂ ≫ f') (hp.paste_vert sq.flip) hT

/-- A smooth morphism is flat with reduced base changes. -/
theorem of_smooth (h : Y ⟶ X) [Smooth h] : IsReducedFlatBaseChange h where
  flat := inferInstance
  universallyOpen := UniversallyOpen.of_flat h
  isReduced a p₁ p₂ hp _ :=
    have : Smooth p₁ := MorphismProperty.of_isPullback (P := @Smooth) hp.flip ‹_›
    isReduced_of_smooth p₁

/-- `Spec L → Spec K` is flat with reduced base changes for a field extension of a perfect
field `K`. -/
theorem specMap {K L : Type u} [Field K] [PerfectField K] [Field L] (σ : K →+* L) :
    IsReducedFlatBaseChange (Spec.map (CommRingCat.ofHom σ)) where
  flat := inferInstance
  universallyOpen := inferInstance
  isReduced a _ _ hp _ :=
    have := isReduced_pullback_over_perfectField a (Spec.map (CommRingCat.ofHom σ))
    isReduced_of_isOpenImmersion hp.isoPullback.hom

/-- The projection `X_L → X` of the base change along a field extension `L/K` of a perfect field
is flat with reduced base changes. -/
theorem fieldChange {K L : Type u} [Field K] [PerfectField K] [Field L]
    (sX : X ⟶ Spec (.of K)) (σ : K →+* L) :
    IsReducedFlatBaseChange (pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) :=
  of_isPullback (IsPullback.of_hasPullback sX _).flip (specMap σ)

/-- The canonical lift of a flat morphism with reduced base changes is one. -/
theorem canonicalLift (hh : IsReducedFlatBaseChange h) (Z : X.IdealSheafData) :
    IsReducedFlatBaseChange (canonicalLift h Z) :=
  have := hh.flat
  of_isPullback (Kollar.isPullback_canonicalLift_of_flat h Z) hh

/-- The last morphism `h_r` of the pull-back of a blow-up sequence along a flat morphism with
reduced base changes is one. -/
theorem pullbackHom (hh : IsReducedFlatBaseChange h) (S : ClosedBlowupSequence X) :
    IsReducedFlatBaseChange (S.pullbackHom h) :=
  have := hh.flat
  of_isPullback (Kollar.isPullback_pullback_toBase_of_flat S h) hh

/-- The inverse image of a reduced closed subscheme along a flat morphism with reduced base
changes is the reduced closed subscheme on the inverse image. -/
theorem comap_vanishingIdeal (hh : IsReducedFlatBaseChange h) (T : Closeds X) (T' : Closeds Y)
    (hT : (T' : Set Y) = h ⁻¹' T) :
    (Scheme.IdealSheafData.vanishingIdeal T).comap h = Scheme.IdealSheafData.vanishingIdeal T' := by
  set S := Scheme.IdealSheafData.vanishingIdeal T
  have : IsReduced (pullback h S.subschemeι) :=
    hh.isReduced S.subschemeι (pullback.snd _ _) (pullback.fst _ _)
      (IsPullback.of_hasPullback h S.subschemeι).flip inferInstance
  have : IsReduced (S.comap h).subscheme := isReduced_of_isOpenImmersion (S.comapIso h).hom
  refine Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme _ _ ?_
  refine Closeds.ext ?_
  rw [hT, Scheme.IdealSheafData.support_comap]
  change h ⁻¹' (S.support : Set X) = _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]

end IsReducedFlatBaseChange

/-! ### Pull-back of the disjoining sequence -/

namespace DisjoiningStage

variable {k j : ℕ}

/-- The pull-back `(Y, (h⁻¹E_i^{(j)}), (h⁻¹F^{l,(j)}))` of a stage of the disjoining
construction along `h : Y → X_j`. -/
abbrev pullback (st : DisjoiningStage.{u} k j) {Y : Scheme.{u}} (h : Y ⟶ st.X) :
    DisjoiningStage.{u} k j :=
  ⟨Y, fun i => (st.Es i).comap h, fun l => (st.Fs l).comap h⟩

/-- The next stage, from the families and a centre. -/
def stepOf {Y : Scheme.{u}} (Es : Fin k → Y.IdealSheafData) (Fs : Fin j → Y.IdealSheafData)
    (c : Y.IdealSheafData) : DisjoiningStage.{u} k (j + 1) where
  X := blowUp c
  Es i := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (blowUpToBase c ⁻¹' (((Es i).support : Set Y) \ (c.support : Set Y))))
  Fs := Fin.snoc (α := fun _ => (blowUp c).IdealSheafData)
    (fun l => Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      (blowUpToBase c ⁻¹' (((Fs l).support : Set Y) \ (c.support : Set Y)))))
    (c.comap (blowUpToBase c))

/-- The next stage is `stepOf` of the families and the centre. -/
theorem step_eq_stepOf (st : DisjoiningStage.{u} k j) : st.step = stepOf st.Es st.Fs st.center :=
  rfl

variable (st : DisjoiningStage.{u} k j) {Y : Scheme.{u}} {h : Y ⟶ st.X}

/-- The centre of the pulled-back stage is the inverse image of the centre. -/
theorem center_pullback (hh : IsReducedFlatBaseChange h) :
    (st.pullback h).center = st.center.comap h := by
  symm
  refine hh.comap_vanishingIdeal _ _ ?_
  have e1 := coe_support_center (st.pullback h)
  have e2 := coe_support_center st
  unfold center at e1 e2
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at e1 e2
  refine e1.trans ?_
  rw [e2]
  simp only [Set.preimage_iUnion, Set.preimage_iInter]
  refine Set.iUnion_congr fun S => Set.iInter_congr fun i => Set.iInter_congr fun _ => ?_
  change (((st.Es i).comap h).support : Set Y) = _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- The reduced divisor `⋃_i h⁻¹E_i^{(j)}` is the inverse image of `⋃_i E_i^{(j)}`. -/
theorem unionEs_pullback (hh : IsReducedFlatBaseChange h) :
    (st.pullback h).unionEs = st.unionEs.comap h := by
  symm
  refine hh.comap_vanishingIdeal _ _ ?_
  have e1 := coe_support_unionEs (st.pullback h)
  have e2 := coe_support_unionEs st
  unfold unionEs at e1 e2
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at e1 e2
  refine e1.trans ?_
  rw [e2, Set.preimage_iUnion]
  refine Set.iUnion_congr fun i => ?_
  change (((st.Es i).comap h).support : Set Y) = _
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- The transform `π⁻¹(D ∖ Z)‾` commutes with flat base change with reduced base changes. -/
theorem transform_comap_canonicalLift (hh : IsReducedFlatBaseChange h)
    (c : st.X.IdealSheafData) (D : st.X.IdealSheafData) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      (blowUpToBase c ⁻¹' ((D.support : Set st.X) \ (c.support : Set st.X))))).comap
        (canonicalLift h c) =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        (blowUpToBase (c.comap h) ⁻¹' (((D.comap h).support : Set Y) \
          ((c.comap h).support : Set Y)))) := by
  have hl := hh.canonicalLift c
  have := hl.universallyOpen
  refine hl.comap_vanishingIdeal _ _ ?_
  rw [Closeds.coe_closure, Closeds.coe_closure,
    ((canonicalLift h c).isOpenMap).preimage_closure_eq_closure_preimage
      (canonicalLift h c).continuous]
  congr 1
  rw [← Set.preimage_comp]
  change _ = ⇑(canonicalLift h c ≫ blowUpToBase c) ⁻¹' _
  rw [canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  congr 1
  rw [Set.preimage_sdiff, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.support_comap]
  rfl

/-- The next stage of the pulled-back stage is the pull-back of the next stage along the
canonical lift. -/
theorem step_pullback (hh : IsReducedFlatBaseChange h) :
    (st.pullback h).step = st.step.pullback (canonicalLift h st.center) := by
  rw [step_eq_stepOf (st.pullback h), center_pullback st hh]
  simp only [stepOf, pullback, step, transform]
  congr 1
  · funext i
    exact (transform_comap_canonicalLift st hh _ _).symm
  · funext l
    induction l using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        canonicalLift_comp_blowUpToBase]
    | cast l =>
      simp only [Fin.snoc_castSucc]
      exact (transform_comap_canonicalLift st hh _ _).symm

/-- Equal stages have equal sequences and end divisors. -/
theorem heq_sequence_divisor_of_eq {j' : ℕ} {s s' : DisjoiningStage.{u} k j'} (e : s = s')
    (n : ℕ) :
    (⟨s.sequence n, s.divisor n⟩ : Σ D : ClosedBlowupSequence s.X, OrderedDivisor D.target) ≍
      (⟨s'.sequence n, s'.divisor n⟩ :
        Σ D : ClosedBlowupSequence s'.X, OrderedDivisor D.target) := by
  subst e; rfl

/-- Blow-up sequences with equal first centres and equal remaining data are equal. -/
theorem sigma_cons_eq {Y : Scheme.{u}} {c c' : Y.IdealSheafData} (hc : c = c')
    {B : ClosedBlowupSequence (blowUp c)} {B' : ClosedBlowupSequence (blowUp c')}
    {E : OrderedDivisor B.target} {E' : OrderedDivisor B'.target}
    (hB : (⟨B, E⟩ : Σ D : ClosedBlowupSequence (blowUp c), OrderedDivisor D.target) ≍
      (⟨B', E'⟩ : Σ D : ClosedBlowupSequence (blowUp c'), OrderedDivisor D.target)) :
    (⟨.cons c B, E⟩ : Σ D : ClosedBlowupSequence Y, OrderedDivisor D.target) =
      ⟨.cons c' B', E'⟩ := by
  subst hc
  cases eq_of_heq hB
  rfl

/-- **The disjoining construction commutes with flat base change with reduced base changes**,
from an arbitrary stage: the next `n` blow-ups of the pulled-back stage are the pull-back of
the next `n` blow-ups, and the ordered divisor at the end is the inverse image of the ordered
divisor at the end. -/
theorem sequence_pullback (n : ℕ) : ∀ {j : ℕ} (st : DisjoiningStage.{u} k j) {Y : Scheme.{u}}
    (h : Y ⟶ st.X), IsReducedFlatBaseChange h →
    (⟨(st.pullback h).sequence n, (st.pullback h).divisor n⟩ :
        Σ D : ClosedBlowupSequence Y, OrderedDivisor D.target) =
      ⟨(st.sequence n).pullback h, (st.divisor n).comap ((st.sequence n).pullbackHom h)⟩ := by
  induction n with
  | zero =>
    intro j st Y h hh
    refine Sigma.ext rfl (heq_of_eq ?_)
    change OrderedDivisor.mk (j + 1) _ = OrderedDivisor.mk (j + 1) _
    congr 1
    funext i
    induction i using Fin.cases with
    | zero => exact unionEs_pullback st hh
    | succ l => rfl
  | succ n ih =>
    intro j st Y h hh
    refine sigma_cons_eq (center_pullback st hh) ?_
    exact (heq_sequence_divisor_of_eq (step_pullback st hh) n).trans
      (heq_of_eq (ih st.step (canonicalLift h st.center) (hh.canonicalLift _)))

end DisjoiningStage

section Disjoining

variable {X Y : Scheme.{u}}

/-- The initial stage of `(Y, h⁻¹E)` is the pull-back of the initial stage of `(X, E)`. -/
theorem disjoiningStart_comap (E : OrderedDivisor X) (h : Y ⟶ X) :
    disjoiningStart (E.comap h) = (disjoiningStart E).pullback h := by
  simp only [disjoiningStart, DisjoiningStage.pullback, OrderedDivisor.comap]
  congr 1
  funext l
  exact l.elim0

/-- **The disjoining sequence commutes with flat base change with reduced base changes**: for
such `h : Y → X` (e.g. smooth, or a change of perfect base field), the disjoining sequence of
`(Y, h⁻¹E)` is the pull-back of that of `(X, E)`, and its ordered divisor is the inverse image
`h'⁻¹E_{X'}` along `h' : Y' → X'`. -/
theorem disjoiningSequence_comap (E : OrderedDivisor X) (h : Y ⟶ X)
    (hh : IsReducedFlatBaseChange h) :
    (⟨disjoiningSequence Y (E.comap h), disjoiningDivisor Y (E.comap h)⟩ :
        Σ D : ClosedBlowupSequence Y, OrderedDivisor D.target) =
      ⟨(disjoiningSequence X E).pullback h,
        (disjoiningDivisor X E).comap ((disjoiningSequence X E).pullbackHom h)⟩ := by
  obtain ⟨s, E⟩ := E
  match s, E with
  | 0, E =>
    refine Sigma.ext rfl (heq_of_eq ?_)
    change OrderedDivisor.mk 0 _ = OrderedDivisor.mk 0 _
    congr 1
    funext i
    exact i.elim0
  | 1, E => rfl
  | k + 2, E =>
    exact eq_of_heq ((DisjoiningStage.heq_sequence_divisor_of_eq
      (disjoiningStart_comap (⟨k + 2, E⟩ : OrderedDivisor X) h) (k + 1)).trans
      (heq_of_eq ((disjoiningStart (X := X) ⟨k + 2, E⟩).sequence_pullback (k + 1) h hh)))

end Disjoining

/-! ### The principalization construction under flat base change -/

section Construction

/-- A triple `(X, I, E)` is a triple of Kollár 3.64 exactly when it is an snc triple of 3.35
on an equidimensional scheme. -/
theorem mem_triples_iff {t : FieldBlowupTriple.{u}} :
    t ∈ triples ↔ t ∈ sncTriples ∧ Equidimensional t.X := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨h1, h2, h3, h4, h6, h7, h8⟩, h5⟩
  · rintro ⟨⟨h1, h2, h3, h4, h6, h7, h8⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A triple of 3.64 is an snc triple. -/
theorem mem_sncTriples_of_mem_triples {t : FieldBlowupTriple.{u}} (ht : t ∈ triples) :
    t ∈ sncTriples :=
  (mem_triples_iff.1 ht).1

/-- The marked triple `(X', π^*I, 1, E')` at the end `π : X' → X` of a blow-up sequence, with
an ordered divisor `E'` on `X'`. -/
def constructionTriple {X : Scheme.{u}} (I : X.IdealSheafData) {k : Type u} [Field k]
    (s : X ⟶ Spec (.of k)) (p : Σ D : ClosedBlowupSequence X, OrderedDivisor D.target) :
    MarkedTriple.{u} :=
  ⟨⟨⟨p.1.target, I.comap p.1.toBase, p.2⟩, k, p.1.toBase ≫ s⟩, 1⟩

open Classical in
/-- The construction of `principalizationConstruction` from a blow-up sequence `𝐃` with an
ordered divisor `E'` at its end: `(𝐃 ⋅ 𝓑(X', π^*I, 1, E'))^{red}` if `(X', π^*I, 1, E')` is a
marked triple, `𝐃^{red}` otherwise. -/
def constructionAux
    (B : BlowupSequenceFunctor MarkedTriple.toTriple (markedTriplesOfMarking.{u} 1))
    {X : Scheme.{u}} (I : X.IdealSheafData) {k : Type u} [Field k] (s : X ⟶ Spec (.of k))
    (p : Σ D : ClosedBlowupSequence X, OrderedDivisor D.target) : ClosedBlowupSequence X :=
  if h : constructionTriple I s p ∈ markedTriplesOfMarking 1 then
    (p.1.append (B _ h)).reduction
  else p.1.reduction

variable (B : BlowupSequenceFunctor MarkedTriple.toTriple (markedTriplesOfMarking.{u} 1))

/-- `𝓑𝓟_𝓑` is `constructionAux` on the disjoining sequence. -/
theorem principalizationConstruction_eq (t : FieldBlowupTriple.{u}) (ht : t ∈ sncTriples) :
    principalizationConstruction B t ht =
      constructionAux B t.I t.sX ⟨disjoiningSequence t.X t.E, disjoiningDivisor t.X t.E⟩ :=
  rfl

/-- `constructionAux` when the end is a marked triple. -/
theorem constructionAux_of_mem {X : Scheme.{u}} (I : X.IdealSheafData) {k : Type u} [Field k]
    (s : X ⟶ Spec (.of k)) (p : Σ D : ClosedBlowupSequence X, OrderedDivisor D.target)
    (hp : constructionTriple I s p ∈ markedTriplesOfMarking 1) :
    constructionAux B I s p = (p.1.append (B _ hp)).reduction := by
  simp only [constructionAux, hp, ↓reduceDIte]

/-- `𝓑𝓟_𝓑(X, I, E)` has no empty blow-ups. -/
theorem hasNoEmptyBlowups_principalizationConstruction (t : FieldBlowupTriple.{u})
    (ht : t ∈ sncTriples) : (principalizationConstruction B t ht).HasNoEmptyBlowups := by
  rw [principalizationConstruction_eq]
  unfold constructionAux
  split_ifs <;> exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _

/-- For a triple `(X, I, E)` of 3.64, `(X', π^*I, 1, E_{X'})` is a marked triple. -/
theorem constructionTriple_mem {t : FieldBlowupTriple.{u}} (ht : t ∈ triples) :
    constructionTriple t.I t.sX ⟨disjoiningSequence t.X t.E, disjoiningDivisor t.X t.E⟩ ∈
      markedTriplesOfMarking 1 := by
  obtain ⟨h1, -, h3, h4, h5, h6, -, h8⟩ := ht
  exact ⟨isTriple_disjoiningSequence t.sX h5 t.I h6 t.E h8, rfl⟩

/-- For equal marked triples `a = b` of marking `1`, the reductions of `𝓑 a` and `𝓑 b` are
heterogeneously equal. -/
theorem heq_reduction_of_eq_triple {a b : MarkedTriple.{u}} (e : a = b)
    (ha : a ∈ markedTriplesOfMarking 1) (hb : b ∈ markedTriplesOfMarking 1) :
    (B a ha).reduction ≍ (B b hb).reduction := by
  subst e; rfl

/-- The disjoining sequence of a triple. -/
local macro "𝐃[" t:term "]" : term => `(disjoiningSequence ($t).X ($t).E)
/-- The ordered divisor at the end of the disjoining sequence of a triple. -/
local macro "𝐄[" t:term "]" : term => `(disjoiningDivisor ($t).X ($t).E)
/-- The marked triple `(X', π^*I, 1, E_{X'})` of a triple. -/
local macro "𝐭'[" t:term "]" : term =>
  `(constructionTriple ($t).I ($t).sX ⟨disjoiningSequence ($t).X ($t).E,
    disjoiningDivisor ($t).X ($t).E⟩)
/-- The projection `X_L → X` of a field change. -/
local macro "𝐩[" t:term ", " σ:term "]" : term => `(FieldBlowupTriple.fieldChangeProj $t $σ)

/-- **The principalization construction under flat base change** (the common part of Kollár
3.72 ⇒ 3.35(4)). Let `(X, I, E)` and `(Y, I_Y, E_Y)` be triples of 3.64 and `h : Y → X` flat
with reduced base changes, with `E_Y = h⁻¹E`. Let `π : X' → X` be the end of
the disjoining sequence of `(X, E)` and `h' : Y' → X'` the last morphism of its pull-back. If
`𝓑(Y', π_Y^*I_Y, 1, h'⁻¹E_{X'})` and `h'^*𝓑(X', π^*I, 1, E_{X'})` have the same reduction, then
`𝓑𝓟_𝓑(Y, I_Y, E_Y) = (h^*𝓑𝓟_𝓑(X, I, E))^{red}`. -/
theorem principalizationConstruction_comap {t tY : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    (htY : tY ∈ triples) (h : tY.X ⟶ t.X) (hh : IsReducedFlatBaseChange h)
    (hE : tY.E = t.E.comap h)
    (hB : ∀ (hX : 𝐭'[t] ∈ markedTriplesOfMarking 1)
      (hY : constructionTriple tY.I tY.sX
        ⟨𝐃[t].pullback h, 𝐄[t].comap (𝐃[t].pullbackHom h)⟩ ∈ markedTriplesOfMarking 1),
      (B _ hY).reduction = ((B _ hX).pullback (𝐃[t].pullbackHom h)).reduction) :
    principalizationConstruction B tY (mem_sncTriples_of_mem_triples htY) =
      ((principalizationConstruction B t (mem_sncTriples_of_mem_triples ht)).pullback
        h).reduction := by
  have hs : (⟨disjoiningSequence tY.X tY.E, disjoiningDivisor tY.X tY.E⟩ :
      Σ D : ClosedBlowupSequence tY.X, OrderedDivisor D.target) =
      ⟨𝐃[t].pullback h, 𝐄[t].comap (𝐃[t].pullbackHom h)⟩ := by
    rw [hE]
    exact disjoiningSequence_comap t.E h hh
  have hmY := constructionTriple_mem htY
  have hm := constructionTriple_mem ht
  rw [principalizationConstruction_eq, principalizationConstruction_eq]
  rw [hs] at hmY ⊢
  rw [constructionAux_of_mem _ _ _ _ hmY, constructionAux_of_mem _ _ _ _ hm,
    ClosedBlowupSequence.reduction_pullback_reduction]
  exact (ClosedBlowupSequence.reduction_append_congr _ (hB hm hmY)).trans
    (congrArg ClosedBlowupSequence.reduction (ClosedBlowupSequence.append_pullback _ _ h).symm)

/-- Marked triples on the same scheme over the same field with equal data are equal. -/
theorem markedTriple_mk_congr {X : Scheme.{u}} {I I' : X.IdealSheafData}
    {E E' : OrderedDivisor X} {k : Type u} [Field k] {s s' : X ⟶ Spec (.of k)} {m : ℕ}
    (hI : I = I') (hE : E = E') (hs : s = s') :
    (⟨⟨⟨X, I, E⟩, k, s⟩, m⟩ : MarkedTriple.{u}) = ⟨⟨⟨X, I', E'⟩, k, s'⟩, m⟩ := by
  subst hI hE hs; rfl

/-- `𝓑𝓟_𝓑` restricted to the triples of 3.64. -/
abbrev principalizationConstructionOnTriples :
    BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple triples.{u} :=
  fun t ht => principalizationConstruction B t (mem_sncTriples_of_mem_triples ht)

/-- The smooth case: for smooth `h`, `𝓑𝓟_𝓑(Y, h^*I, h⁻¹E) = (h^*𝓑𝓟_𝓑(X, I, E))^{red}`. -/
theorem principalizationConstruction_pullback_of_smooth
    (hB : ∀ (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfMarking 1) (Y : Scheme.{u})
      (h : Y ⟶ t.X), Smooth h → LocallyOfFiniteType (h ≫ t.sX) → QuasiCompact (h ≫ t.sX) →
        ∀ hY : t.pullback h ∈ markedTriplesOfMarking 1,
          B (t.pullback h) hY = ((B t ht).pullback h).reduction)
    {t : FieldBlowupTriple.{u}} (ht : t ∈ triples) {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h]
    (hY : t.pullback h ∈ triples) :
    principalizationConstructionOnTriples B (t.pullback h) hY =
      ((principalizationConstructionOnTriples B t ht).pullback h).reduction := by
  refine principalizationConstruction_comap B ht hY h (.of_smooth h) rfl fun hX hY' => ?_
  have hsq := Kollar.isPullback_pullback_toBase_of_flat 𝐃[t] h
  have hsm : Smooth (𝐃[t].pullbackHom h) := MorphismProperty.of_isPullback (P := @Smooth) hsq ‹_›
  have e2 : (𝐃[t].pullback h).toBase ≫ h ≫ t.sX = (𝐃[t].pullbackHom h) ≫ 𝐃[t].toBase ≫ t.sX := by
    rw [← Category.assoc, ← Category.assoc, Kollar.pullbackHom_toBase_comm]
  have e : constructionTriple (t.pullback h).I (t.pullback h).sX
      ⟨𝐃[t].pullback h, 𝐄[t].comap (𝐃[t].pullbackHom h)⟩ =
      𝐭'[t].pullback (𝐃[t].pullbackHom h) := by
    have e1 : (t.I.comap h).comap (𝐃[t].pullback h).toBase =
        (t.I.comap 𝐃[t].toBase).comap (𝐃[t].pullbackHom h) := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        Kollar.pullbackHom_toBase_comm]
    exact markedTriple_mk_congr e1 rfl e2
  have hY'' : 𝐭'[t].pullback (𝐃[t].pullbackHom h) ∈ markedTriplesOfMarking 1 := e ▸ hY'
  have hlft : LocallyOfFiniteType ((𝐃[t].pullbackHom h) ≫ 𝐃[t].toBase ≫ t.sX) := by
    rw [← e2]; exact hY'.1.2.2.1
  have hqc : QuasiCompact ((𝐃[t].pullbackHom h) ≫ 𝐃[t].toBase ≫ t.sX) := by
    rw [← e2]; exact hY'.1.2.2.2.1
  have hA := heq_reduction_of_eq_triple B e hY' hY''
  have hC := (congrArg ClosedBlowupSequence.reduction
    (hB _ hX _ (𝐃[t].pullbackHom h) hsm hlft hqc hY'')).trans
      (ClosedBlowupSequence.reduction_reduction _)
  exact eq_of_heq (hA.trans ((heq_of_eq hC).trans
    (@HEq.refl (ClosedBlowupSequence (𝐃[t].pullback h).target) _)))

/-- **Kollár 3.72 ⇒ 3.35(4), smooth morphisms.** Let `𝓑` be a blow-up sequence functor on the
marked triples of marking `1` commuting with smooth morphisms. Then `𝓑𝓟_𝓑` commutes with smooth
morphisms on the triples of 3.64: for a triple `(X, I, E)`, a smooth `h : Y → X` with `Y` of
finite type over `k` and `(Y, h^*I, h⁻¹E)` a triple, `𝓑𝓟_𝓑(Y, h^*I, h⁻¹E) = h^*𝓑𝓟_𝓑(X, I, E)`
if `h` is surjective and `𝓑𝓟_𝓑(Y, h^*I, h⁻¹E) = (h^*𝓑𝓟_𝓑(X, I, E))^{red}` in general. -/
@[mmp "lem_kr3c_bp_construction_smooth_functorial"]
theorem commutesWithSmoothOn_principalizationConstruction
    (hB : CommutesWithSmoothOnMarked _ B) :
    CommutesWithSmoothOn triples (principalizationConstructionOnTriples B) := by
  refine ⟨fun t ht Y h hsm hsurj _ _ hY => ?_, fun t ht Y h hsm _ _ hY =>
    principalizationConstruction_pullback_of_smooth B hB.2 ht h hY⟩
  rw [principalizationConstruction_pullback_of_smooth B hB.2 ht h hY]
  exact ClosedBlowupSequence.reduction_eq_self
    (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
      (hasNoEmptyBlowups_principalizationConstruction B t _) h)

/-- **Kollár 3.72 ⇒ 3.35(4), change of fields.** Let `𝓑` be a blow-up sequence functor on the
marked triples of marking `1` commuting with isomorphisms and with change of fields. Then
`𝓑𝓟_𝓑` commutes with change of fields on the triples of 3.64:
`𝓑𝓟_𝓑(X_L, I_L, E_L) = 𝓑𝓟_𝓑(X, I, E)_L` whenever both are triples. -/
theorem commutesWithFieldChangeOn_principalizationConstruction_of_iso
    (hiso : ∀ (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfMarking 1) (Y : Scheme.{u})
      (e : Y ⟶ t.X) [IsIso e] (hY : t.pullback e ∈ markedTriplesOfMarking 1),
        B (t.pullback e) hY = (B t ht).pullback e)
    (hB : CommutesWithFieldChangeOnMarked _ B) :
    CommutesWithFieldChangeOn triples (principalizationConstructionOnTriples B) := by
  intro t ht L _ σ hL
  have : CharZero t.k := ht.1
  have hp := IsReducedFlatBaseChange.fieldChange t.sX σ
  have : Flat 𝐩[t, σ] := hp.flat
  have : Surjective 𝐩[t, σ] :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback _ _).flip
      inferInstance
  refine (principalizationConstruction_comap B ht hL 𝐩[t, σ] hp rfl ?_).trans
    (ClosedBlowupSequence.reduction_eq_self
      (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
        (hasNoEmptyBlowups_principalizationConstruction B t _) 𝐩[t, σ]))
  intro hX hY
  have hsq : IsPullback (𝐃[t].pullbackHom 𝐩[t, σ])
      ((𝐃[t].pullback 𝐩[t, σ]).toBase ≫ Limits.pullback.snd _ _)
      (𝐃[t].toBase ≫ t.sX) (Spec.map (CommRingCat.ofHom σ)) :=
    (Kollar.isPullback_pullback_toBase_of_flat 𝐃[t] 𝐩[t, σ]).flip.paste_vert
      (IsPullback.of_hasPullback _ _)
  have ef : hsq.isoPullback.hom ≫ Limits.pullback.fst _ _ = (𝐃[t].pullbackHom 𝐩[t, σ]) :=
    hsq.isoPullback_hom_fst
  have es : hsq.isoPullback.hom ≫ Limits.pullback.snd _ _ =
      (𝐃[t].pullback 𝐩[t, σ]).toBase ≫ Limits.pullback.snd _ _ :=
    hsq.isoPullback_hom_snd
  have eq : constructionTriple (t.fieldChange σ).I (t.fieldChange σ).sX
      ⟨𝐃[t].pullback 𝐩[t, σ], 𝐄[t].comap (𝐃[t].pullbackHom 𝐩[t, σ])⟩ =
      (𝐭'[t].fieldChange σ).pullback hsq.isoPullback.hom := by
    have e1 : (t.I.comap 𝐩[t, σ]).comap (𝐃[t].pullback 𝐩[t, σ]).toBase =
        ((t.I.comap 𝐃[t].toBase).comap (Limits.pullback.fst _ _)).comap hsq.isoPullback.hom := by
      rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
        ← Scheme.IdealSheafData.comap_comp, ef, Kollar.pullbackHom_toBase_comm]
    have e3 : 𝐄[t].comap (𝐃[t].pullbackHom 𝐩[t, σ]) =
        (𝐄[t].comap (Limits.pullback.fst _ _)).comap hsq.isoPullback.hom := by
      simp only [OrderedDivisor.comap, ← Scheme.IdealSheafData.comap_comp, ef]
    exact markedTriple_mk_congr e1 e3 es.symm
  have hL' : 𝐭'[t].fieldChange σ ∈ markedTriplesOfMarking 1 := by
    refine ⟨mem_triples_iff.2 ⟨fieldChange_mem_sncTriples
      (mem_sncTriples_of_mem_triples hX.1) σ, ?_⟩, rfl⟩
    exact Equidimensional.of_homeomorph hsq.isoPullback.inv.homeomorph (mem_triples_iff.1 hY.1).2
  have hY' : (𝐭'[t].fieldChange σ).pullback hsq.isoPullback.hom ∈
      markedTriplesOfMarking 1 := eq ▸ hY
  have hA := heq_reduction_of_eq_triple B eq hY hY'
  have h2 : B _ hY' = (B 𝐭'[t] hX).pullback (𝐃[t].pullbackHom 𝐩[t, σ]) := by
    rw [@hiso _ hL' _ hsq.isoPullback.hom (Iso.isIso_hom _) hY', hB 𝐭'[t] hX L σ hL']
    refine (eq_of_heq (ClosedBlowupSequence.pullback_pullback_heq _ _ hsq.isoPullback.hom
      (hsq.isoPullback.hom ≫ Limits.pullback.fst _ _) rfl
      (by rw [eqToHom_refl, Category.id_comp]; rfl))).trans ?_
    exact congrArg (ClosedBlowupSequence.pullback _) ef
  exact eq_of_heq (hA.trans ((heq_of_eq (congrArg ClosedBlowupSequence.reduction h2)).trans
    (@HEq.refl (ClosedBlowupSequence (𝐃[t].pullback 𝐩[t, σ]).target) _)))

/-- **Kollár 3.72 ⇒ 3.35(4), change of fields.** Let `𝓑` be a blow-up sequence functor on the
marked triples of marking `1` commuting with smooth morphisms and with change of fields. Then
`𝓑𝓟_𝓑` commutes with change of fields on the triples of 3.64. -/
@[mmp "lem_kr3c_bp_construction_field_change"]
theorem commutesWithFieldChangeOn_principalizationConstruction
    (hBs : CommutesWithSmoothOnMarked _ B) (hB : CommutesWithFieldChangeOnMarked _ B) :
    CommutesWithFieldChangeOn triples (principalizationConstructionOnTriples B) := by
  refine commutesWithFieldChangeOn_principalizationConstruction_of_iso B
    (fun t ht Y e _ hY => ?_) hB
  obtain ⟨-, -, hlft, hqc, -⟩ := ht.1
  have : LocallyOfFiniteType t.sX := hlft
  have : QuasiCompact t.sX := hqc
  exact hBs.1 t ht Y e inferInstance inferInstance inferInstance inferInstance hY

end Construction

end MMP.Resolution
