module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientPowers
import MMP.AlgebraicGeometry.Resolution.Surface.SncPointsCompletions
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MarkedStepOne
import MMP.AlgebraicGeometry.Resolution.TransformRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialSmoothPullback
import MMP.AlgebraicGeometry.Resolution.MaximalContact.DerivativeIdealTransform
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MixedIdealMonomialReduction
import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MarkedMixedIdealStep
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained

/-!
# `𝓑𝓜𝓞_{d,m}[𝓑]` commutes with smooth morphisms

Let `𝓑` be an order-reduction family on dimensions `a, …, b` each of whose members ignores
empty entries of the divisor, and let `m ≥ 1`. On the class of marked
triples `(X, I, m, E)` of marking `m` with `a ≤ dim X ≤ b`, the assignment
`(X, I, m, E) ↦ 𝓑𝓜𝓞_{dim X, m}[𝓑](X, I, m, E)` commutes with smooth morphisms: for a smooth
`h : Y → X` with both marked triples in the class, `𝓑𝓜𝓞(Y, h^*I, m, h⁻¹E)` is the pull-back of
`𝓑𝓜𝓞(X, I, m, E)` with its empty blow-ups deleted, and nothing is deleted when `h` is surjective.
This holds with the per-component monomial part; with one coefficient per member of `E` it fails.

Orders are preserved by smooth pull-back, and `A(h^*I) = h^*A(I)`, so `N(h^*I) = h^*N(I)` and
`K_s(h^*I, m) = h^*K_s(I, m)`; the invariants `maxord N` and `s` can only drop on `Y`. A round of
Step 1 (or Step 2) on `X` of value `μ` either has the same value on `Y`, and then the `Y`-round is
its reduced pull-back by (2a) of the family, or a smaller one, and then its reduced pull-back is
empty and the configuration on `Y` does not change. Along the reduced pull-back the marked
transform pulls back, and the total transform pulls back up to empty entries, which the members
of the family ignore. Step 3 is the monomial order reduction, which commutes with smooth
morphisms, and the extension by closure commutes with the reduced pull-back.

## Main results

* `MMP.Resolution.commutesWithSmoothOnMarked_bmoFunctor`.

## Implementation notes

The configuration on `Y` is compared with the one on `X` along the last morphism
`h' : Y' → X'` of the reduced pull-back, the divisors being equal after their empty entries are
deleted (equivalently, their lists of nonempty entries agree). Each recursion of Steps 1 and 2 is
compared with its own fuel on each side, both being larger than the invariant. In Step 3 the
monomial data on `Y` are the pull-back of those on `X` only up to empty entries of the divisor;
the monomial order reduction depends on the divisor only through its nonempty entries, in their
order, since a stratum containing an empty entry is empty.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.107 (2) and its proof in 3.111]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

open Aux

/-! ### Empty entries of ordered divisors -/

section Flat

variable {X : Scheme.{u}}

open Classical in
/-- The list of the nonempty entries of an ordered divisor, in their order. -/
private noncomputable def flat (E : OrderedDivisor X) : List X.IdealSheafData :=
  (List.ofFn E.E).filter fun D => D ≠ ⊤

open Classical in
/-- The indices of the nonempty entries. -/
private noncomputable def flatIdx (E : OrderedDivisor X) : List (Fin E.s) :=
  (List.finRange E.s).filter fun i => E.E i ≠ ⊤

private theorem exists_flatIdx_get (E : OrderedDivisor X) (i : Fin E.s) (hi : E.E i ≠ ⊤) :
    ∃ j, (flatIdx E).get j = i :=
  List.mem_iff_get.1 (by simp [flatIdx, hi])

private theorem ofFn_deleteEmpty (E : OrderedDivisor X) :
    List.ofFn E.deleteEmpty.E = flat E := by
  show List.ofFn (E.E ∘ (flatIdx E).get) = flat E
  rw [← List.map_ofFn, List.ofFn_get, flatIdx, flat, List.ofFn_eq_map (f := E.E),
    List.filter_map]
  rfl

private theorem eq_of_ofFn_eq {E F : OrderedDivisor X} (h : List.ofFn E.E = List.ofFn F.E) :
    E = F := by
  obtain ⟨s, e⟩ := E
  obtain ⟨t, f⟩ := F
  rw [List.ofFn_inj'] at h
  cases h
  rfl

private theorem deleteEmpty_eq_iff {E F : OrderedDivisor X} :
    E.deleteEmpty = F.deleteEmpty ↔ flat E = flat F := by
  refine ⟨fun h => ?_, fun h => eq_of_ofFn_eq ?_⟩
  · rw [← ofFn_deleteEmpty, ← ofFn_deleteEmpty, h]
  · rw [ofFn_deleteEmpty, ofFn_deleteEmpty, h]

private theorem mem_support_iff (E : OrderedDivisor X) (x : X) :
    x ∈ E.support ↔ ∃ D ∈ flat E, x ∈ D.support := by
  simp only [OrderedDivisor.support, Set.mem_iUnion, flat, List.mem_filter, List.mem_ofFn,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨E.E i, ⟨⟨i, rfl⟩, fun h => by simp [h] at hi⟩, hi⟩
  · rintro ⟨D, ⟨⟨i, rfl⟩, -⟩, hi⟩
    exact ⟨i, hi⟩

private theorem support_eq_of_flat_eq {E F : OrderedDivisor X} (h : flat E = flat F) :
    E.support = F.support := by
  ext x
  rw [mem_support_iff, mem_support_iff, h]

/-- If `T` maps values failing `p` to values failing `p`, then the filtered image of a list
under `T` depends only on the filtered list. -/
private theorem filter_map_eq_of_filter_eq {α β : Type*} (p : α → Bool) (q : β → Bool)
    (T : α → β) (hT : ∀ a, p a = false → q (T a) = false) {l l' : List α}
    (h : l.filter p = l'.filter p) : (l.map T).filter q = (l'.map T).filter q := by
  have key : ∀ l : List α, (l.map T).filter q = ((l.filter p).map T).filter q := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        simp [List.filter_cons, ha', hT a ha', ih]
  rw [key l, key l', h]

/-- The birational transform `π⁻¹_*D` of an entry, as in `OrderedDivisor.totalTransform`. -/
private noncomputable def entryTransform (Z : X.IdealSheafData) (D : X.IdealSheafData) :
    (blowUp Z).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (blowUpToBase Z ⁻¹' ((D.support : Set X) \ componentsOfCodimAtLeastTwo (Z.support : Set X))))

private theorem entryTransform_top (Z : X.IdealSheafData) : entryTransform Z ⊤ = ⊤ := by
  have : (Closeds.closure (blowUpToBase Z ⁻¹' (((⊤ : X.IdealSheafData).support : Set X) \
      componentsOfCodimAtLeastTwo (Z.support : Set X)))) = ⊥ := by
    ext x
    simp [Scheme.IdealSheafData.support_top]
  rw [entryTransform, this, Scheme.IdealSheafData.vanishingIdeal_bot]

/-- The last entry of `π⁻¹_tot(E)`; it depends only on the support of `E`. -/
private noncomputable def lastEntry (Z : X.IdealSheafData) (S : Set X) :
    (blowUp Z).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
    (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X)) (_ : W ∉ componentsOf S),
      blowUpToBase Z ⁻¹' W))

open Classical in
private theorem flat_totalTransform (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    flat (E.totalTransform Z) =
      ((List.ofFn E.E).map (entryTransform Z)).filter (fun D => D ≠ ⊤) ++
        [lastEntry Z E.support].filter (fun D => D ≠ ⊤) := by
  have h : List.ofFn (E.totalTransform Z).E = List.ofFn (n := E.s + 1)
      (Fin.snoc (α := fun _ => (blowUp Z).IdealSheafData) (fun i => entryTransform Z (E.E i))
        (lastEntry Z E.support)) := rfl
  rw [flat, h, List.ofFn_succ', List.concat_eq_append, List.filter_append, List.map_ofFn]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

open Classical in
private theorem flat_totalTransform_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (Z : X.IdealSheafData) : flat (E.totalTransform Z) = flat (F.totalTransform Z) := by
  rw [flat_totalTransform, flat_totalTransform, support_eq_of_flat_eq h]
  congr 1
  refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) h
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
  rw [hD, entryTransform_top]

open Classical in
private theorem flat_comap_eq {Y : Scheme.{u}} {E F : OrderedDivisor X} (h : flat E = flat F)
    (f : Y ⟶ X) : flat (E.comap f) = flat (F.comap f) := by
  have hE : List.ofFn (E.comap f).E = (List.ofFn E.E).map (·.comap f) := by
    rw [List.map_ofFn]; rfl
  have hF : List.ofFn (F.comap f).E = (List.ofFn F.E).map (·.comap f) := by
    rw [List.map_ofFn]; rfl
  rw [flat, flat, hE, hF]
  refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) h
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
  rw [hD, Scheme.IdealSheafData.comap_top]

private theorem notMem_componentsOf_top (W : Set X) :
    W ∉ componentsOf (((⊤ : X.IdealSheafData).support : Set X)) := by
  intro h
  obtain ⟨⟨hirr, hsub⟩, -⟩ := h
  obtain ⟨x, hx⟩ := hirr.nonempty
  simpa [Scheme.IdealSheafData.support_top] using hsub hx

private theorem isComponent_iff {E F : OrderedDivisor X} (h : flat E = flat F)
    (D : AlgebraicGeometry.PrimeDivisor X) : E.IsComponent D ↔ F.IsComponent D := by
  have key : ∀ E : OrderedDivisor X, E.IsComponent D ↔
      ∃ D' ∈ flat E, D.support ∈ componentsOf (D'.support : Set X) := by
    intro E
    simp only [OrderedDivisor.IsComponent, flat, List.mem_filter, List.mem_ofFn,
      decide_eq_true_eq]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨E.E i, ⟨⟨i, rfl⟩, fun ht => notMem_componentsOf_top _ (ht ▸ hi)⟩, hi⟩
    · rintro ⟨_, ⟨⟨i, rfl⟩, -⟩, hi⟩
      exact ⟨i, hi⟩
  rw [key, key, h]

private theorem monomialPartCoeff_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (I : X.IdealSheafData) : monomialPartCoeff I E = monomialPartCoeff I F := by
  funext D
  have := isComponent_iff h D
  unfold monomialPartCoeff
  split_ifs <;> first | rfl | (exfalso; tauto)

private theorem nonmonomialPart_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (I : X.IdealSheafData) : nonmonomialPart I E = nonmonomialPart I F := by
  simp only [nonmonomialPart, monomialPart, monomialPartCoeff_eq h I]

private theorem mixedIdeal_eq {E F : OrderedDivisor X} (h : flat E = flat F)
    (I : X.IdealSheafData) (m s : ℕ) : mixedIdeal I E m s = mixedIdeal I F m s := by
  simp only [mixedIdeal, nonmonomialPart_eq h I]

end Flat

/-! ### Irreducible components under flat base change -/

section Components

/-- The stalk of the vanishing ideal of a closed set `T` at a point of `T` with no proper
generalization in `T` is the maximal ideal. -/
private theorem stalk_vanishingIdeal_eq_maximalIdeal {Y : Scheme.{u}} (T : Closeds Y)
    {y : Y} (hy : y ∈ T) (hmax : ∀ y', y' ⤳ y → y' ∈ T → y' = y) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) y =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  set S := Scheme.IdealSheafData.vanishingIdeal T with hS
  have hsupp : (S.support : Set Y) = T := by
    rw [hS, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨z, rfl⟩ : y ∈ Set.range S.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι, hsupp]
  have hz : IsMax z := by
    intro b hb
    have hb' : b ⤳ z := hb
    have : S.subschemeι b = S.subschemeι z :=
      hmax _ (hb'.map S.subschemeι.continuous) (by
        have hb2 : S.subschemeι b ∈ (S.support : Set Y) := by
          rw [← Scheme.IdealSheafData.range_subschemeι]
          exact ⟨b, rfl⟩
        rwa [hsupp] at hb2)
    have := S.subschemeι.isClosedEmbedding.injective this
    rw [this]
  have hdim : ringKrullDim (S.subscheme.presheaf.stalk z) = 0 := by
    rw [ringKrullDim_stalk_eq_coheight, Order.coheight_eq_zero.2 hz]; rfl
  have : Ring.KrullDimLE 0 (S.subscheme.presheaf.stalk z) :=
    Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
  have hbot : IsLocalRing.maximalIdeal (S.subscheme.presheaf.stalk z) = ⊥ := by
    rw [← Ring.KrullDimLE.nilradical_eq_maximalIdeal, nilradical_eq_zero]; rfl
  rw [← Stacks.Divisors.kernel_stalkMap_subscheme_eq_idealStalk, RingHom.ker_eq_comap_bot, ← hbot]
  exact IsLocalRing.maximalIdeal_comap _

/-- A flat local homomorphism of noetherian local rings whose closed fibre is the residue field
of the target preserves the Krull dimension. -/
private theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [Module.Flat A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) = IsLocalRing.maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  have : Algebra.HasGoingDown A B := Algebra.HasGoingDown.of_flat
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  rw [hmax, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h]

variable {X Y : Scheme.{u}}

/-- A point `η` whose closure is a component of `h⁻¹(\overline{ξ})` has no proper generalization
in `h⁻¹(\overline{ξ})`. -/
private theorem eq_of_specializes_of_mem_componentsOf {h : Y ⟶ X} (ξ : X) {η : Y}
    (hW : closure {η} ∈ componentsOf (h ⁻¹' closure {ξ})) :
    ∀ y', y' ⤳ η → h y' ∈ closure ({ξ} : Set X) → y' = η := by
  intro y' hy' hy'Z
  have hTcl : IsClosed (h ⁻¹' closure ({ξ} : Set X)) := isClosed_closure.preimage h.continuous
  have hcl : closure {y'} ⊆ h ⁻¹' closure ({ξ} : Set X) :=
    closure_minimal (Set.singleton_subset_iff.2 hy'Z) hTcl
  have hsub := hW.2 ⟨isIrreducible_singleton.closure, hcl⟩
    (closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hy'))
      isClosed_closure)
  have : η ⤳ y' := specializes_iff_mem_closure.2 (hsub (subset_closure rfl))
  exact (hy'.antisymm this).eq

/-- **Generic points of the components of an inverse image.** For `h` flat with reduced base
changes between locally noetherian schemes, the generic point `η` of a component of
`h⁻¹(\overline{ξ})` lies over `ξ` and has the same coheight. -/
private theorem map_eq_and_coheight_eq [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h) (ξ : X) {η : Y}
    (hW : closure {η} ∈ componentsOf (h ⁻¹' closure {ξ})) :
    h η = ξ ∧ Order.coheight η = Order.coheight ξ := by
  haveI := hh.flat
  have hmaxT := eq_of_specializes_of_mem_componentsOf ξ hW
  have hηT : h η ∈ closure ({ξ} : Set X) := hW.1.2 (subset_closure rfl)
  obtain ⟨y'', hy''η, hy''ξ⟩ := Flat.generalizingMap h (specializes_iff_mem_closure.2 hηT)
  have hy'' : y'' = η := hmaxT y'' hy''η (by rw [hy''ξ]; exact subset_closure rfl)
  have hhη : h η = ξ := hy'' ▸ hy''ξ
  refine ⟨hhη, ?_⟩
  set T : Closeds X := Closeds.closure {ξ}
  have hξT : ξ ∈ T := subset_closure rfl
  have hmξ : IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T) (h η) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (h η)) := by
    refine stalk_vanishingIdeal_eq_maximalIdeal T (hhη ▸ hξT) fun y' hy' hy'T => ?_
    have h1 : h η ⤳ y' := by rwa [hhη, specializes_iff_mem_closure]
    exact (hy'.antisymm h1).eq
  have hcomap : (Scheme.IdealSheafData.vanishingIdeal T).comap h =
      Scheme.IdealSheafData.vanishingIdeal (T.preimage h.continuous) :=
    hh.comap_vanishingIdeal T _ rfl
  have hm : (IsLocalRing.maximalIdeal (X.presheaf.stalk (h η))).map (h.stalkMap η).hom =
      IsLocalRing.maximalIdeal (Y.presheaf.stalk η) := by
    rw [← hmξ, ← IdealSheafData.stalk_comap, hcomap]
    exact stalk_vanishingIdeal_eq_maximalIdeal _ hηT fun y' hy' hy'T => hmaxT y' hy' hy'T
  letI : Algebra (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) := (h.stalkMap η).hom.toAlgebra
  haveI : Module.Flat (X.presheaf.stalk (h η)) (Y.presheaf.stalk η) := Flat.stalkMap h η
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (h η)) (Y.presheaf.stalk η)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap η).hom)
  have hd := ringKrullDim_eq_of_flat_of_map_maximalIdeal_eq
    (A := X.presheaf.stalk (h η)) (B := Y.presheaf.stalk η) hm
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hhη] at hd
  exact_mod_cast hd

/-- An irreducible subset of a closed subset of a scheme lies in one of its components. -/
private theorem exists_mem_componentsOf_subset {D C : Set Y} (hD : IsClosed D)
    (hC : IsIrreducible C) (hCD : C ⊆ D) : ∃ W ∈ componentsOf D, C ⊆ W := by
  obtain ⟨c, hc⟩ := QuasiSober.sober hC.closure isClosed_closure
  have hcD : c ∈ D := (closure_minimal hCD hD) hc.mem
  obtain ⟨W, hW, hcW⟩ := exists_mem_componentsOf hcD
  refine ⟨W, hW, subset_closure.trans ?_⟩
  rw [← hc.def]
  exact closure_minimal (Set.singleton_subset_iff.2 hcW) (Aux.isClosed_of_mem_componentsOf hD hW)

/-- **The components of an inverse image.** For `h` flat with reduced base changes between
locally noetherian schemes and `Z` closed, the components of `h⁻¹Z` are the components of the
`h⁻¹Z_j`, `Z_j = \overline{ξ}` the components of `Z`. -/
private theorem mem_componentsOf_preimage_iff [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h) {Z : Set X} (hZ : IsClosed Z) {W' : Set Y} :
    W' ∈ componentsOf (h ⁻¹' Z) ↔
      ∃ ξ : X, closure {ξ} ∈ componentsOf Z ∧ W' ∈ componentsOf (h ⁻¹' closure {ξ}) := by
  have hZ' : IsClosed (h ⁻¹' Z) := hZ.preimage h.continuous
  have fwd : ∀ {W'}, W' ∈ componentsOf (h ⁻¹' Z) →
      ∃ ξ : X, closure {ξ} ∈ componentsOf Z ∧ W' ∈ componentsOf (h ⁻¹' closure {ξ}) := by
    intro W' hW'
    obtain ⟨η, hηZ, rfl⟩ := exists_eq_closure_of_mem_componentsOf hZ' hW'
    obtain ⟨W, hW, hηW⟩ := exists_mem_componentsOf (show h η ∈ Z from hηZ)
    obtain ⟨ξ, -, rfl⟩ := exists_eq_closure_of_mem_componentsOf hZ hW
    refine ⟨ξ, hW, ⟨⟨isIrreducible_singleton.closure, closure_minimal
      (Set.singleton_subset_iff.2 hηW) (isClosed_closure.preimage h.continuous)⟩, ?_⟩⟩
    intro C hC hle
    exact hW'.2 ⟨hC.1, hC.2.trans (Set.preimage_mono hW.1.2)⟩ hle
  refine ⟨fwd, ?_⟩
  rintro ⟨ξ, hξ, hW'⟩
  refine ⟨⟨hW'.1.1, hW'.1.2.trans (Set.preimage_mono hξ.1.2)⟩, ?_⟩
  intro C hC hle
  obtain ⟨W'', hW'', hCW''⟩ := exists_mem_componentsOf_subset hZ' hC.1 hC.2
  obtain ⟨ξ₂, hξ₂, hW''₂⟩ := fwd hW''
  obtain ⟨η', -, rfl⟩ := exists_eq_closure_of_mem_componentsOf
    (isClosed_closure.preimage h.continuous) hW'
  obtain ⟨η'', -, rfl⟩ := exists_eq_closure_of_mem_componentsOf
    (isClosed_closure.preimage h.continuous) hW''₂
  have e1 := (map_eq_and_coheight_eq hh ξ hW').1
  have e2 := (map_eq_and_coheight_eq hh ξ₂ hW''₂).1
  have hsp : η'' ⤳ η' := specializes_iff_mem_closure.2 (hCW'' (hle (subset_closure rfl)))
  have hsp' : ξ₂ ⤳ ξ := by rw [← e1, ← e2]; exact hsp.map h.continuous
  have hle' : closure ({ξ} : Set X) ⊆ closure {ξ₂} :=
    closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp'))
      isClosed_closure
  have hge : closure ({ξ₂} : Set X) ⊆ closure {ξ} := hξ.2 hξ₂.1 hle'
  have hW''sub : closure {η''} ⊆ h ⁻¹' closure ({ξ} : Set X) :=
    hW''₂.1.2.trans (Set.preimage_mono hge)
  exact hCW''.trans (hW'.2 ⟨hW''₂.1.1, hW''sub⟩ (hle.trans hCW''))

/-- The codimension of the closure of a point is its coheight. -/
private theorem codimension_irreducibleClosure_closure (ξ : X)
    (hW : IsIrreducible (closure ({ξ} : Set X))) :
    codimension (irreducibleClosure hW) = Order.coheight ξ := by
  rw [coheight_eq_codimension_closureSingleton]
  congr 1
  ext1
  change closure (closure {ξ}) = closure {ξ}
  exact closure_closure

/-- Components of codimension `≥ 2` pull back. -/
private theorem componentsOfCodimAtLeastTwo_preimage [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [NoetherianSpace Y] {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h)
    {Z : Set X} (hZ : IsClosed Z) :
    componentsOfCodimAtLeastTwo (h ⁻¹' Z) = h ⁻¹' componentsOfCodimAtLeastTwo Z := by
  ext y
  simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨W', hW', hcod, hyW'⟩
    obtain ⟨ξ, hξ, hW'ξ⟩ := (mem_componentsOf_preimage_iff hh hZ).1 hW'
    obtain ⟨η, -, rfl⟩ := exists_eq_closure_of_mem_componentsOf
      (isClosed_closure.preimage h.continuous) hW'ξ
    have hc := (map_eq_and_coheight_eq hh ξ hW'ξ).2
    refine ⟨closure {ξ}, hξ, ?_, hW'ξ.1.2 hyW'⟩
    rw [codimension_irreducibleClosure_closure] at hcod ⊢
    rwa [← hc]
  · rintro ⟨W, hW, hcod, hyW⟩
    obtain ⟨ξ, -, rfl⟩ := exists_eq_closure_of_mem_componentsOf hZ hW
    obtain ⟨W', hW', hyW'⟩ := exists_mem_componentsOf (show y ∈ h ⁻¹' closure {ξ} from hyW)
    have hW'Z := (mem_componentsOf_preimage_iff hh hZ).2 ⟨ξ, hW, hW'⟩
    obtain ⟨η, -, rfl⟩ := exists_eq_closure_of_mem_componentsOf
      (isClosed_closure.preimage h.continuous) hW'
    have hc := (map_eq_and_coheight_eq hh ξ hW').2
    refine ⟨closure {η}, hW'Z, ?_, hyW'⟩
    rw [codimension_irreducibleClosure_closure] at hcod ⊢
    rwa [hc]

/-- A component `W'` of `h⁻¹\overline{ξ}`, `\overline{ξ}` a component of `Z`, is a component of
`h⁻¹D` exactly when `\overline{ξ}` is a component of `D`. -/
private theorem mem_componentsOf_preimage_iff_of_mem [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h) {D : Set X}
    (hD : IsClosed D) (ξ : X) {W' : Set Y} (hW' : W' ∈ componentsOf (h ⁻¹' closure {ξ})) :
    W' ∈ componentsOf (h ⁻¹' D) ↔ closure {ξ} ∈ componentsOf D := by
  refine ⟨fun hD' => ?_, fun hξ => (mem_componentsOf_preimage_iff hh hD).2 ⟨ξ, hξ, hW'⟩⟩
  obtain ⟨ξ₂, hξ₂, hW'₂⟩ := (mem_componentsOf_preimage_iff hh hD).1 hD'
  obtain ⟨η, -, rfl⟩ := exists_eq_closure_of_mem_componentsOf
    (isClosed_closure.preimage h.continuous) hW'
  rw [← (map_eq_and_coheight_eq hh ξ hW').1, (map_eq_and_coheight_eq hh ξ₂ hW'₂).1]
  exact hξ₂

/-- The union of the components of `Z` that are not components of `D` pulls back. -/
private theorem iUnion_componentsOf_not_preimage [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h)
    {Z D : Set X} (hZ : IsClosed Z) (hD : IsClosed D) :
    (⋃ (W : Set Y) (_ : W ∈ componentsOf (h ⁻¹' Z)) (_ : W ∉ componentsOf (h ⁻¹' D)), W) =
      h ⁻¹' ⋃ (W : Set X) (_ : W ∈ componentsOf Z) (_ : W ∉ componentsOf D), W := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨W', hW', hnD, hyW'⟩
    obtain ⟨ξ, hξ, hW'ξ⟩ := (mem_componentsOf_preimage_iff hh hZ).1 hW'
    exact ⟨closure {ξ}, hξ, fun h' => hnD ((mem_componentsOf_preimage_iff_of_mem hh hD ξ
      hW'ξ).2 h'), hW'ξ.1.2 hyW'⟩
  · rintro ⟨W, hW, hnD, hyW⟩
    obtain ⟨ξ, -, rfl⟩ := exists_eq_closure_of_mem_componentsOf hZ hW
    obtain ⟨W', hW', hyW'⟩ := exists_mem_componentsOf (show y ∈ h ⁻¹' closure {ξ} from hyW)
    exact ⟨W', (mem_componentsOf_preimage_iff hh hZ).2 ⟨ξ, hW, hW'⟩,
      fun h' => hnD ((mem_componentsOf_preimage_iff_of_mem hh hD ξ hW').1 h'), hyW'⟩

/-- **The total transform under flat base change with reduced base changes.** The total
transform of `h⁻¹E` along `h⁻¹Z` is the inverse image of `π⁻¹_tot E` under `canonicalLift h Z`. -/
private theorem totalTransform_comap_of_isReducedFlatBaseChange [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] [NoetherianSpace Y] {h : Y ⟶ X} (hh : IsReducedFlatBaseChange h)
    (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    (E.comap h).totalTransform (Z.comap h) = (E.totalTransform Z).comap (canonicalLift h Z) := by
  have hsupp : ((Z.comap h).support : Set Y) = h ⁻¹' (Z.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hEcl : IsClosed E.support := by
    simp only [OrderedDivisor.support]
    exact isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
  refine (Kollar.totalTransform_comap_canonicalLift hh E Z ?_ ?_).symm
  · rw [hsupp]; exact componentsOfCodimAtLeastTwo_preimage hh Z.support.isClosed
  · rw [hsupp, Kollar.support_comap]
    exact iUnion_componentsOf_not_preimage hh Z.support.isClosed hEcl

end Components

/-! ### Transforms along the reduced pull-back -/

section Transforms

/-- The scheme of a triple `(X, I, E)` over a field is noetherian. -/
private theorem isNoetherian_of_isTriple {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E) :
    AlgebraicGeometry.IsNoetherian X :=
  haveI : LocallyOfFiniteType s := h.2.2.1
  haveI : QuasiCompact s := h.2.2.2.1
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  {}

/-- The blow-up of a noetherian scheme is noetherian. -/
private theorem isNoetherian_blowUp {Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y]
    (W : Y.IdealSheafData) : AlgebraicGeometry.IsNoetherian (blowUp W) :=
  have : IsLocallyNoetherian (blowUp W) := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase W)
  have : CompactSpace (blowUp W) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase W)
  {}

/-- Appending an empty entry does not change the nonempty entries. -/
private theorem flat_snoc_top {Y : Scheme.{u}} (E : OrderedDivisor Y) :
    flat (⟨E.s + 1, Fin.snoc (α := fun _ => Y.IdealSheafData) E.E ⊤⟩ : OrderedDivisor Y) =
      flat E := by
  classical
  have h : List.ofFn (⟨E.s + 1, Fin.snoc (α := fun _ => Y.IdealSheafData) E.E ⊤⟩ :
      OrderedDivisor Y).E = List.ofFn (n := E.s + 1)
        (Fin.snoc (α := fun _ => Y.IdealSheafData) E.E ⊤) := rfl
  rw [flat, h, List.ofFn_succ', List.concat_eq_append, List.filter_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  simp [flat]

/-- The lift `Y → B_ZX` of a morphism `h` with `h⁻¹Z = ∅` is again flat with reduced base
changes. -/
private theorem isReducedFlatBaseChange_blowUpLift {X Y : Scheme.{u}} {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (Z : X.IdealSheafData) (hZ : Z.comap h = ⊤) :
    IsReducedFlatBaseChange
      (blowUpLift Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZ)) := by
  have := Kollar.isIso_blowUpToBase_comap_of_eq_top h Z hZ
  rw [Kollar.blowUpLift_eq_inv_comp_canonicalLift h Z hZ]
  exact IsReducedFlatBaseChange.of_isPullback
    (IsPullback.of_horiz_isIso (fst := inv (blowUpToBase (Z.comap h)))
      (snd := inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z) (f := canonicalLift h Z)
      (g := 𝟙 _) ⟨by simp⟩) (hh.canonicalLift Z)

/-- **The marked transform along a blow-up whose centre has empty inverse image.** If
`ord_Z I ≥ m` and `h⁻¹Z = ∅`, the inverse image of `π⁻¹_{Z*}(I, m)` along the lift `Y → B_ZX`
of `h` is `h^*I`. -/
private theorem comap_blowUpLift_birationalTransform {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (h : Y ⟶ X)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hcodim : HasComponentsOfPositiveCodim (Z.support : Set X)) (a : MarkedIdeal X)
    (ha : OrderAlongGE a.I (Z.support : Set X) a.m) (hZh : Z.comap h = ⊤) :
    (a.birationalTransform Z).I.comap
        (blowUpLift Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZh)) =
      a.I.comap h := by
  have h2 := congrArg
    (fun J => J.comap (blowUpLift Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZh)))
    (MarkedIdeal.birationalTransform_mul_eq sX hX Z hZ hcodim a ha)
  rw [Stacks.IdealSheaf.comap_mul, Stacks.IdealSheaf.comap_pow,
    ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, blowUpLift_comp,
    hZh] at h2
  have htop : (⊤ : Y.IdealSheafData) = 1 := rfl
  rwa [htop, one_pow, mul_one] at h2

open ClosedBlowupSequence in
/-- **Marked and total transforms along the reduced pull-back.** Along a smooth blow-up sequence
`𝐁` of order `≥ m` starting with `(X, I, m, E)` and a morphism `h : Y → X` flat with reduced
base changes, the marked transform of `(h^*I, m)` along `(h^*𝐁)^red` is the inverse image of
that of `(I, m)` along `𝐁` under the last morphism `h'`, and for `E'` agreeing with `h⁻¹E` up
to empty entries, the total transform of `E'` agrees with `h'⁻¹` of that of `E` up to empty
entries. -/
private theorem transforms_pullbackReducedWithHom {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), S.IsOrderGeMarkedTripleSeq s a E →
      ∀ {Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y] (h : Y ⟶ X),
        IsReducedFlatBaseChange h → ∀ E' : OrderedDivisor Y, flat E' = flat (E.comap h) →
        ((S.pullbackReducedWithHom h).1.markedTransform ⟨a.I.comap h, a.m⟩).I =
            (S.markedTransform a).I.comap (S.pullbackReducedWithHom h).2 ∧
          flat ((S.pullbackReducedWithHom h).1.orderedTotalTransform E') =
            flat ((S.orderedTotalTransform E).comap (S.pullbackReducedWithHom h).2)
  | _, .nil _, _, _, _, _, _, _, _, _, _, hE' => ⟨rfl, hE'⟩
  | X, .cons Z S, s, a, E, hS, Y, _, h, hh, E', hE' => by
    obtain ⟨hI, hZsm, hcod, -, hord, hS'⟩ := hS
    haveI := isNoetherian_of_isTriple hI
    by_cases hZ : Z.comap h = ⊤
    · rw [pullbackReducedWithHom_cons_of_eq_top Z S h hZ]
      have hL := isReducedFlatBaseChange_blowUpLift hh Z hZ
      have hbt := comap_blowUpLift_birationalTransform s hI.2.1 h Z hZsm hcod a hord hZ
      have hEt : flat E' = flat ((E.totalTransform Z).comap
          (blowUpLift Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZ))) := by
        rw [Kollar.totalTransform_comap_blowUpLift hh E
          (fun i => (hI.2.2.2.2.2.2.1 i).1) Z hZ, hE']
        exact (flat_snoc_top (E.comap h)).symm
      have ih := transforms_pullbackReducedWithHom S _ _ _ hS'
        (blowUpLift Z h (ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZ)) hL E' hEt
      rw [hbt] at ih
      exact ih
    · rw [pullbackReducedWithHom_cons_of_ne_top Z S h hZ]
      have ha : a.I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a.m :=
        comap_le_comap_pow_of_stalk_le _ _ _ _
          (stalk_le_pow_of_orderAlongGE s hI.2.1 Z hZsm a.I a.m hord)
      have hb := Kollar.birationalTransform_comap_eq_comap_canonicalLift h Z a ha
      haveI := isNoetherian_blowUp (Z.comap h)
      have hEt : flat (E'.totalTransform (Z.comap h)) =
          flat ((E.totalTransform Z).comap (canonicalLift h Z)) := by
        rw [flat_totalTransform_eq hE' (Z.comap h),
          totalTransform_comap_of_isReducedFlatBaseChange hh E Z]
      have ih := transforms_pullbackReducedWithHom S _ _ _ hS' (canonicalLift h Z)
        (hh.canonicalLift Z) _ hEt
      change ((S.pullbackReducedWithHom (canonicalLift h Z)).1.markedTransform
          ((⟨a.I.comap h, a.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h))).I = _ ∧
        flat ((S.pullbackReducedWithHom (canonicalLift h Z)).1.orderedTotalTransform
          (E'.totalTransform (Z.comap h))) = _
      rw [hb]
      exact ih

end Transforms

/-! ### Orders under smooth pull-back -/

section Orders

/-- The points of a subspace `T` lying over an irreducible `Z ⊆ T` form an irreducible set. -/
private theorem isIrreducible_preimage_val {X : Type*} [TopologicalSpace X] {T Z : Set X}
    (hZ : IsIrreducible Z) (hZT : Z ⊆ T) : IsIrreducible (Subtype.val ⁻¹' Z : Set T) := by
  obtain ⟨z, hz⟩ := hZ.nonempty
  refine ⟨⟨⟨z, hZT hz⟩, hz⟩, ?_⟩
  rintro U V hU hV ⟨a, haZ, haU⟩ ⟨b, hbZ, hbV⟩
  obtain ⟨U', hU', rfl⟩ := isOpen_induced_iff.1 hU
  obtain ⟨V', hV', rfl⟩ := isOpen_induced_iff.1 hV
  obtain ⟨c, hcZ, hcU, hcV⟩ := hZ.2 U' V' hU' hV' ⟨a.1, haZ, haU⟩ ⟨b.1, hbZ, hbV⟩
  exact ⟨⟨c, hZT hcZ⟩, hcZ, hcU, hcV⟩

/-- The unit ideal has order `0`. -/
private theorem idealOrder_top {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊤ : Ideal R) = 0 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_) bot_le
  rcases j with _ | j
  · simp
  · exact absurd (top_le_iff.1 (hj.trans (Ideal.pow_le_self (Nat.succ_ne_zero j))))
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top

/-- The zero ideal has infinite order. -/
private theorem idealOrder_bot {R : Type*} [CommRing R] [IsLocalRing R] :
    idealOrder (⊥ : Ideal R) = ⊤ := by
  refine eq_top_iff.2 (le_trans (le_of_eq ENat.iSup_natCast.symm) (iSup_le fun j => ?_))
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : (⊥ : Ideal R) ≤ IsLocalRing.maximalIdeal R ^ j) =>
    (j : ℕ∞)) j bot_le le_rfl

/-- On an equidimensional scheme some irreducible component of which has dimension `0`, every
point is the generic point of an irreducible component. -/
private theorem closure_mem_irreducibleComponents_of_not_pos {X : Scheme.{u}}
    (hX : Equidimensional X)
    (hd : ¬ ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z) (x : X) :
    closure {x} ∈ irreducibleComponents X := by
  push Not at hd
  obtain ⟨Z₀, hZ₀, hZ₀d⟩ := hd
  obtain ⟨C, hC, hxC⟩ :=
    exists_mem_irreducibleComponents_subset_of_isIrreducible (closure ({x} : Set X))
      isIrreducible_singleton.closure
  by_contra hne
  have hne' : closure {x} ≠ C := fun e => hne (e ▸ hC)
  obtain ⟨c, hcC, hcx⟩ : ∃ c ∈ C, c ∉ closure ({x} : Set X) := by
    by_contra hall
    push Not at hall
    exact hne' (le_antisymm hxC hall)
  have hpos : 0 < topologicalKrullDim C := by
    rw [topologicalKrullDim, Order.krullDim_pos_iff]
    refine ⟨⟨Subtype.val ⁻¹' closure {x}, isIrreducible_preimage_val
      isIrreducible_singleton.closure hxC, isClosed_closure.preimage continuous_subtype_val⟩,
      ⟨Set.univ, by
        simpa using isIrreducible_preimage_val hC.1 (subset_refl C), isClosed_univ⟩, ?_⟩
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) fun e => ?_
    have : (⟨c, hcC⟩ : C) ∈ (Subtype.val ⁻¹' closure {x} : Set C) := by
      have h2 := congrArg (fun T : IrreducibleCloseds C => (⟨c, hcC⟩ : C) ∈ (T : Set C)) e
      simp only [IrreducibleCloseds.coe_mk, Set.mem_univ, eq_iff_iff, iff_true] at h2
      exact h2
    exact hcx this
  rw [hX C hC Z₀ hZ₀] at hpos
  exact absurd hZ₀d (not_le.2 hpos)

/-- **Orders are preserved by smooth pull-back** (Kollár 3.111): for a triple `(X, I, E)` and a
smooth `h : Y → X`, `ord_y h^*J = ord_{h(y)} J` for every ideal sheaf `J` on `X`. -/
private theorem multAt_comap_of_smooth {k : Type u} [Field k] {X Y : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X}
    (hT : IsTriple sX I E) (h : Y ⟶ X) [Smooth h] (J : X.IdealSheafData) (y : Y) :
    multAt (J.comap h) y = multAt J (h y) := by
  obtain ⟨hchar, hsm, hlft, -, he, -, -⟩ := hT
  haveI := hchar
  haveI : LocallyOfFiniteType sX := hlft
  haveI : Smooth sX := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  by_cases hd : ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z
  · have hD : ∀ j, higherDerivativeIdeal (h ≫ sX) (J.comap h) j =
        (higherDerivativeIdeal sX J j).comap h := by
      intro j
      induction j with
      | zero => rfl
      | succ r ih =>
        rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih,
          derivativeIdeal_comap_of_smooth sX (h ≫ sX) h rfl hd]
    have key (n : ℕ) : (n : ℕ∞) ≤ multAt (J.comap h) y ↔ (n : ℕ∞) ≤ multAt J (h y) := by
      cases n with
      | zero => simp
      | succ n =>
        rw [succ_le_multAt_iff_forall_mem_support (h ≫ sX),
          succ_le_multAt_iff_forall_mem_support sX]
        exact forall₂_congr fun j _ => hD j ▸ mem_support_comap_iff h _ y
    exact le_antisymm (ENat.forall_natCast_le_iff_le.mp fun n => (key n).1)
      (ENat.forall_natCast_le_iff_le.mp fun n => (key n).2)
  · haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x =>
      haveI := isRegularLocalRing_stalk_of_smooth_over_field sX x
      haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
      inferInstance
    haveI : IsReduced X := isReduced_of_isReduced_stalk _
    have hF := isField_stalk_of_closure_mem_irreducibleComponents X (h y)
      (closure_mem_irreducibleComponents_of_not_pos he hd (h y))
    letI := hF.toField
    rw [multAt, multAt, IdealSheafData.stalk_comap]
    rcases Ideal.eq_bot_or_top (IdealSheafData.stalk J (h y)) with h0 | h0 <;> rw [h0]
    · rw [Ideal.map_bot, idealOrder_bot, idealOrder_bot]
    · rw [Ideal.map_top, idealOrder_top, idealOrder_top]

variable {k : Type u} [Field k] {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {I : X.IdealSheafData} {E : OrderedDivisor X}

/-- The maximal order along `h⁻¹Z` of a smooth pull-back is at most the maximal order along
`Z`. -/
private theorem maxOrderAlong_comap_le_of_smooth (hT : IsTriple sX I E) (h : Y ⟶ X) [Smooth h]
    (J : X.IdealSheafData) (Z : Set X) :
    maxOrderAlong (J.comap h) (h ⁻¹' Z) ≤ maxOrderAlong J Z := by
  refine iSup₂_le fun y hy => ?_
  rw [multAt_comap_of_smooth hT h J y]
  exact le_iSup₂ (f := fun x (_ : x ∈ Z) => multAt J x) (h y) hy

/-- The maximal order of a smooth pull-back is at most the maximal order. -/
private theorem maxOrder_comap_le_of_smooth (hT : IsTriple sX I E) (h : Y ⟶ X) [Smooth h]
    (J : X.IdealSheafData) : maxOrder (J.comap h) ≤ maxOrder J := by
  have := maxOrderAlong_comap_le_of_smooth hT h J Set.univ
  rwa [Set.preimage_univ] at this

/-- The cosupport of a marked ideal pulls back along a smooth morphism. -/
private theorem cosupport_comap_of_smooth (hT : IsTriple sX I E) (h : Y ⟶ X) [Smooth h]
    (J : X.IdealSheafData) (m : ℕ) :
    (⟨J.comap h, m⟩ : MarkedIdeal Y).cosupport = h ⁻¹' (⟨J, m⟩ : MarkedIdeal X).cosupport := by
  ext y
  simp only [MarkedIdeal.cosupport, Set.mem_setOf_eq, Set.mem_preimage,
    multAt_comap_of_smooth hT h J y]

/-- The pull-back of a triple along a smooth morphism from an equidimensional scheme
quasi-compact over the field is a triple. -/
private theorem isTriple_comap_of_smooth (hT : IsTriple sX I E) (h : Y ⟶ X) [Smooth h]
    [QuasiCompact (h ≫ sX)] (hY : Equidimensional Y) :
    IsTriple (h ≫ sX) (I.comap h) (E.comap h) := by
  let t : FieldBlowupTriple.{u} := ⟨⟨X, I, E⟩, k, sX⟩
  have ht : t ∈ triples := hT
  show t.pullback h ∈ triples
  exact mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht) h, hY⟩

/-- For an effective Cartier divisor `B`, `idealColon A B` is the ideal-sheaf quotient. -/
private theorem idealColon_eq_colon {X : Scheme.{u}} (A B : X.IdealSheafData)
    (hB : Stacks.Divisors.IsEffectiveCartierDivisor B) :
    idealColon A B = A.colon B (fg_ideal_of_isEffectiveCartierDivisor B hB) :=
  Scheme.IdealSheafData.ofIdeals_ideal (A.colon B _)

/-- Dividing a product by an effective Cartier divisor: `(D · J : D) = J`. -/
private theorem idealColon_mul_cancel_left {X : Scheme.{u}} (D J : X.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) : idealColon (D * J) D = J := by
  rw [idealColon_eq_colon _ _ hD]
  choose U hU hxU b hb hgen using
    fun x : X => Stacks.Divisors.exists_affineOpen_ideal_eq_span_of_isEffectiveCartierDivisor D hD x
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun x : X => (⟨U x, hU x⟩ : X.affineOpens))
    (top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hxU z⟩) fun x => ?_
  rw [Scheme.IdealSheafData.ideal_colon, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, hgen x]
  ext d
  rw [Ideal.colon_span, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton_mul]
  exact ⟨fun ⟨z, hz, hzd⟩ => ((hb x).left (show b x * d = b x * z by rw [hzd]; ring)) ▸ hz,
    fun hd => ⟨d, hd, mul_comm _ _⟩⟩

/-- `𝒪_X(-A)` is the finite product `∏_{a_D ≠ 0} I_D^{a_D}` when `A` has finite support. -/
private theorem divisorIdeal_eq_prod {X : Scheme.{u}} (A : AlgebraicGeometry.PrimeDivisor X → ℕ)
    (hfin : (Function.support A).Finite) :
    divisorIdeal A = ∏ D ∈ hfin.toFinset, D.idealSheaf ^ A D :=
  finprod_eq_prod_of_mulSupport_subset _ fun D hD => by
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro h0
    exact hD (by show D.idealSheaf ^ A D = 1; rw [h0, pow_zero])

/-- On a triple the monomial part is an effective Cartier divisor. -/
private theorem isEffectiveCartierDivisor_monomialPart {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X}
    (h : IsTriple sX I E) : Stacks.Divisors.IsEffectiveCartierDivisor (monomialPart I E) := by
  classical
  obtain ⟨-, hsm, hlft, hqc, -⟩ := h
  haveI : LocallyOfFiniteType sX := hlft
  haveI : QuasiCompact sX := hqc
  set A := monomialPartCoeff I E with hAdef
  have hfin : (Function.support A).Finite := by
    refine (finite_primeDivisor_of_isComponent sX E.E).subset fun D hD => ?_
    by_contra hnc
    exact hD (by simp [hAdef, monomialPartCoeff, OrderedDivisor.IsComponent] at hnc ⊢; simp_all)
  rw [monomialPart, divisorIdeal_eq_prod A hfin]
  exact Stacks.Divisors.isEffectiveCartierDivisor_prod _ _ _
    fun D _ => isEffectiveCartierDivisor_idealSheaf sX hsm D

/-- **`N(h^*I) = h^*N(I)`** for a smooth `h`, by `A(h^*I) = h^*A(I)`. -/
private theorem nonmonomialPart_comap_of_smooth (hT : IsTriple sX I E) (h : Y ⟶ X) [Smooth h]
    (hT' : IsTriple (h ≫ sX) (I.comap h) (E.comap h)) :
    nonmonomialPart (I.comap h) (E.comap h) = (nonmonomialPart I E).comap h := by
  haveI : LocallyOfFiniteType (h ≫ sX) := hT'.2.2.1
  haveI : QuasiCompact (h ≫ sX) := hT'.2.2.2.1
  have hM := monomialPart_comap sX hT (h ≫ sX) hT'.2.1 h (IsReducedFlatBaseChange.of_smooth h)
  have hcart := isEffectiveCartierDivisor_monomialPart hT'
  have e1 := monomialPart_mul_nonmonomialPart (h ≫ sX) (I.comap h) (E.comap h) hT'
  have e2 : monomialPart (I.comap h) (E.comap h) * (nonmonomialPart I E).comap h =
      I.comap h := by
    rw [hM, ← Stacks.IdealSheaf.comap_mul, monomialPart_mul_nonmonomialPart sX I E hT]
  calc nonmonomialPart (I.comap h) (E.comap h)
      = idealColon (monomialPart (I.comap h) (E.comap h) *
          nonmonomialPart (I.comap h) (E.comap h)) (monomialPart (I.comap h) (E.comap h)) :=
        (idealColon_mul_cancel_left _ _ hcart).symm
    _ = idealColon (monomialPart (I.comap h) (E.comap h) * (nonmonomialPart I E).comap h)
          (monomialPart (I.comap h) (E.comap h)) := by rw [e1, e2]
    _ = _ := idealColon_mul_cancel_left _ _ hcart

/-- `K_s(h^*I, m) = h^*K_s(I, m)` for a smooth `h`. -/
private theorem mixedIdeal_comap_of_smooth (hT : IsTriple sX I E) (h : Y ⟶ X) [Smooth h]
    (hT' : IsTriple (h ≫ sX) (I.comap h) (E.comap h)) (m s : ℕ) :
    mixedIdeal (I.comap h) (E.comap h) m s = (mixedIdeal I E m s).comap h := by
  rw [mixedIdeal, mixedIdeal, nonmonomialPart_comap_of_smooth hT h hT']
  change _ = (nonmonomialPart I E ^ m ⊔ I ^ s).comap h
  rw [(Scheme.IdealSheafData.map_gc h).l_sup, Stacks.IdealSheaf.comap_pow,
    Stacks.IdealSheaf.comap_pow]
  rfl

end Orders

/-! ### The monomial order reduction ignores empty entries -/

section Monomial

variable {X : Scheme.{u}}

/-- Monomial data with the divisor replaced. -/
private abbrev withEm (C : MonomialData X) (E : OrderedDivisor X) : MonomialData X :=
  { C with E := E }

private theorem strictMono_flatIdx_get (E : OrderedDivisor X) : StrictMono (flatIdx E).get :=
  List.SortedLT.strictMono_get ((List.sortedLT_finRange _).pairwise.filter _).sortedLT

private theorem map_lt_map_of_lex {n s : ℕ} {g : Fin n → Fin s} (hg : StrictMono g)
    {l₁ l₂ : List (Fin n)} (h : List.Lex (· < ·) l₁ l₂) :
    List.Lex (· < ·) (l₁.map g) (l₂.map g) := by
  induction h with
  | nil => exact List.Lex.nil
  | cons h ih => exact List.Lex.cons ih
  | rel h => exact List.Lex.rel (hg h)

private theorem map_le_map_of_le {n s : ℕ} {g : Fin n → Fin s} (hg : StrictMono g)
    {l₁ l₂ : List (Fin n)} (h : l₁ ≤ l₂) : l₁.map g ≤ l₂.map g := by
  rcases le_iff_lt_or_eq.1 h with h | rfl
  · exact le_of_lt (List.lex_lt.1 (map_lt_map_of_lex hg (List.lex_lt.2 h)))
  · exact le_rfl

open Classical in
private theorem stepIndex_spec (D : MonomialData X) (r : ℕ) (h : ∃ J P, D.IsMaxPiece r J P) :
    (∃ P, D.IsMaxPiece r (D.stepIndex r) P) ∧
      ∀ J P, D.IsMaxPiece r J P → (D.stepIndex r).sort (· ≤ ·) ≤ J.sort (· ≤ ·) := by
  unfold MonomialData.stepIndex
  dsimp only
  split
  · next hS =>
    obtain ⟨h1, h2⟩ :=
      (Finset.exists_min_image _ (fun J : Finset (Fin D.E.s) => J.sort (· ≤ ·)) hS).choose_spec
    exact ⟨(Finset.mem_filter.1 h1).2,
      fun J P hP => h2 J (Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hP⟩)⟩
  · next hS =>
    obtain ⟨J, P, hP⟩ := h
    exact absurd ⟨J, Finset.mem_filter.2 ⟨Finset.mem_univ _, P, hP⟩⟩ hS

open Classical in
private theorem stepIndex_of_not (D : MonomialData X) (r : ℕ) (h : ¬ ∃ J P, D.IsMaxPiece r J P) :
    D.stepIndex r = ∅ := by
  unfold MonomialData.stepIndex
  dsimp only
  split
  · next hS =>
    obtain ⟨J, hJ⟩ := hS
    exact absurd ⟨J, (Finset.mem_filter.1 hJ).2⟩ h
  · rfl

section Reindex

variable (C : MonomialData X) {n : ℕ} {g : Fin n → Fin C.E.s} (hg : StrictMono g)
  (hgr : ∀ i, C.E.E i ≠ ⊤ → ∃ j, g j = i)

/-- The monomial data with the entries of the divisor reindexed along `g`. -/
private abbrev reindex (g : Fin n → Fin C.E.s) : MonomialData X := withEm C ⟨n, C.E.E ∘ g⟩

include hg in
private theorem reindex_stratum (J : Finset (Fin n)) :
    (reindex C g).stratum J = C.stratum (J.map ⟨g, hg.injective⟩) := by
  ext x
  simp [MonomialData.stratum]

include hg in
private theorem reindex_stratumWeight (J : Finset (Fin n)) (x : X) :
    (reindex C g).stratumWeight J x = C.stratumWeight (J.map ⟨g, hg.injective⟩) x := by
  simp only [MonomialData.stratumWeight, Finset.sum_map]
  rfl

include hg hgr in
private theorem exists_map_eq_of_mem_stratum {J : Finset (Fin C.E.s)} {x : X}
    (hx : x ∈ C.stratum J) : ∃ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ = J := by
  classical
  refine ⟨Finset.univ.filter fun j => g j ∈ J, ?_⟩
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact hj
  · intro hi
    have hxi : x ∈ ((C.E.E i).support : Set X) := by
      simp only [MonomialData.stratum, Set.mem_iInter] at hx
      exact hx i hi
    obtain ⟨j, rfl⟩ := hgr i fun h => by
      rw [h, Scheme.IdealSheafData.support_top] at hxi
      exact hxi
    exact ⟨j, hi, rfl⟩

include hg hgr in
private theorem reindex_maxStratumWeight (r : ℕ) :
    (reindex C g).maxStratumWeight r = C.maxStratumWeight r := by
  let F : Finset (Fin C.E.s) → ℕ := fun J =>
    ⨆ (_ : J.card = r) (x : X) (_ : x ∈ C.stratum J), C.stratumWeight J x
  have hF : ∀ J' : Finset (Fin n),
      (⨆ (_ : J'.card = r) (x : X) (_ : x ∈ (reindex C g).stratum J'),
        (reindex C g).stratumWeight J' x) = F (J'.map ⟨g, hg.injective⟩) := by
    intro J'
    simp only [F, Finset.card_map, reindex_stratum C hg, reindex_stratumWeight C hg]
  have h0 : ∀ J, (∀ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ ≠ J) → F J = 0 := by
    intro J hJ
    refine Nat.eq_zero_of_le_zero (ciSup_le' fun _ => ciSup_le' fun x => ciSup_le' fun hx => ?_)
    obtain ⟨J', hJ'⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
    exact absurd hJ' (hJ J')
  show (⨆ J' : Finset (Fin n), ⨆ (_ : J'.card = r) (x : X) (_ : x ∈ (reindex C g).stratum J'),
      (reindex C g).stratumWeight J' x) = ⨆ J, F J
  simp only [hF]
  refine le_antisymm (ciSup_le' fun J' => le_ciSup (Finite.bddAbove_range F) _)
    (ciSup_le' fun J => ?_)
  by_cases hJ : ∃ J' : Finset (Fin n), J'.map ⟨g, hg.injective⟩ = J
  · obtain ⟨J', rfl⟩ := hJ
    exact le_ciSup (Finite.bddAbove_range
      (fun J' : Finset (Fin n) => F (J'.map ⟨g, hg.injective⟩))) J'
  · push Not at hJ
    rw [h0 J hJ]
    exact Nat.zero_le _

include hg hgr in
private theorem reindex_isMaxPiece (r : ℕ) (J : Finset (Fin n)) (P : Set X) :
    (reindex C g).IsMaxPiece r J P ↔ C.IsMaxPiece r (J.map ⟨g, hg.injective⟩) P := by
  simp only [MonomialData.IsMaxPiece, Finset.card_map, reindex_stratum C hg,
    reindex_stratumWeight C hg, reindex_maxStratumWeight C hg hgr]

include hg hgr in
private theorem reindex_stepIndex (r : ℕ) :
    C.stepIndex r = ((reindex C g).stepIndex r).map ⟨g, hg.injective⟩ := by
  have hsort : ∀ J' : Finset (Fin n), (J'.map ⟨g, hg.injective⟩).sort (· ≤ ·) =
      (J'.sort (· ≤ ·)).map g := fun J' =>
    (Finset.map_sort _ _ _ _ fun a _ b _ => hg.le_iff_le.symm).symm
  by_cases h : ∃ J P, (reindex C g).IsMaxPiece r J P
  · have h' : ∃ J P, C.IsMaxPiece r J P := by
      obtain ⟨J, P, hP⟩ := h
      exact ⟨_, P, (reindex_isMaxPiece C hg hgr r J P).1 hP⟩
    obtain ⟨⟨P₀, hP₀⟩, h₀⟩ := stepIndex_spec (reindex C g) r h
    obtain ⟨⟨P₁, hP₁⟩, h₁⟩ := stepIndex_spec C r h'
    obtain ⟨x, hx, -⟩ := hP₁.2.1
    obtain ⟨J₁', hJ₁'⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
    have ha := h₁ _ P₀ ((reindex_isMaxPiece C hg hgr r _ P₀).1 hP₀)
    have hb := h₀ J₁' P₁ ((reindex_isMaxPiece C hg hgr r J₁' P₁).2 (hJ₁' ▸ hP₁))
    have hb' := map_le_map_of_le hg hb
    rw [← hsort, ← hsort, hJ₁'] at hb'
    have heq := le_antisymm ha hb'
    classical
    have := congrArg List.toFinset heq
    rwa [Finset.sort_toFinset, Finset.sort_toFinset] at this
  · have h' : ¬ ∃ J P, C.IsMaxPiece r J P := by
      rintro ⟨J, P, hP⟩
      obtain ⟨x, hx, -⟩ := hP.2.1
      obtain ⟨J', rfl⟩ := exists_map_eq_of_mem_stratum C hg hgr hx
      exact h ⟨J', P, (reindex_isMaxPiece C hg hgr r J' P).2 hP⟩
    rw [stepIndex_of_not C r h', stepIndex_of_not _ r h, Finset.map_empty]

include hg hgr in
private theorem reindex_stepCenter (r : ℕ) :
    (reindex C g).stepCenter r = C.stepCenter r := by
  unfold MonomialData.stepCenter
  have : {P | (reindex C g).IsMaxPiece r ((reindex C g).stepIndex r) P} =
      {P | C.IsMaxPiece r (C.stepIndex r) P} := by
    ext P
    rw [reindex_stepIndex C hg hgr r]
    exact reindex_isMaxPiece C hg hgr r _ P
  rw [this]

end Reindex

private theorem deleteEmpty_stepCenter (C : MonomialData X) (r : ℕ) :
    (withEm C C.E.deleteEmpty).stepCenter r = C.stepCenter r :=
  reindex_stepCenter C (strictMono_flatIdx_get C.E) (exists_flatIdx_get C.E) r

private theorem deleteEmpty_maxStratumWeight (C : MonomialData X) (r : ℕ) :
    (withEm C C.E.deleteEmpty).maxStratumWeight r = C.maxStratumWeight r :=
  reindex_maxStratumWeight C (strictMono_flatIdx_get C.E) (exists_flatIdx_get C.E) r

/-- The centre of a Step-3.`r` blow-up only sees the nonempty entries of the divisor. -/
private theorem stepCenter_congr (C : MonomialData X) (E : OrderedDivisor X)
    (h : flat E = flat C.E) (r : ℕ) : (withEm C E).stepCenter r = C.stepCenter r := by
  rw [← deleteEmpty_stepCenter (withEm C E), ← deleteEmpty_stepCenter C]
  show (withEm C E.deleteEmpty).stepCenter r = (withEm C C.E.deleteEmpty).stepCenter r
  rw [deleteEmpty_eq_iff.2 h]

/-- `m_r(E, A)` only sees the nonempty entries of the divisor. -/
private theorem maxStratumWeight_congr (C : MonomialData X) (E : OrderedDivisor X)
    (h : flat E = flat C.E) (r : ℕ) : (withEm C E).maxStratumWeight r = C.maxStratumWeight r := by
  rw [← deleteEmpty_maxStratumWeight (withEm C E), ← deleteEmpty_maxStratumWeight C]
  show (withEm C E.deleteEmpty).maxStratumWeight r = (withEm C C.E.deleteEmpty).maxStratumWeight r
  rw [deleteEmpty_eq_iff.2 h]

/-- The Step-3.`r` blow-up of `C` along a given centre `Z`. -/
private noncomputable def stepAt (C : MonomialData X) (m : ℕ) (Z : X.IdealSheafData) :
    MonomialData (blowUp Z) where
  k := C.k
  sX := blowUpToBase Z ≫ C.sX
  E := C.E.totalTransform Z
  A D' :=
    (multAt ((divisorIdeal C.A).comap (blowUpToBase Z)) D'.genericPoint).toNat -
      m * (multAt (Z.comap (blowUpToBase Z)) D'.genericPoint).toNat

private theorem step_eq_stepAt (C : MonomialData X) (m r : ℕ) :
    C.step m r = stepAt C m (C.stepCenter r) := rfl

private theorem iterate_maxStratumWeight_congr (m r : ℕ) : ∀ (N : ℕ) {X : Scheme.{u}}
    (C : MonomialData X) (E : OrderedDivisor X), flat E = flat C.E →
      ((withEm C E).iterate m r N).2.maxStratumWeight r = (C.iterate m r N).2.maxStratumWeight r
  | 0, _, C, E, h => maxStratumWeight_congr C E h r
  | N + 1, _, C, E, h => by
    simp only [MonomialData.iterate]
    rw [step_eq_stepAt, step_eq_stepAt, stepCenter_congr C E h r]
    exact iterate_maxStratumWeight_congr m r N (stepAt C m (C.stepCenter r)) _
      (flat_totalTransform_eq h _)

private theorem stepPhase_congr (m r : ℕ)
    (K : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y)
    (hK : ∀ {Y : Scheme.{u}} (D : MonomialData Y) (E : OrderedDivisor Y), flat E = flat D.E →
      K (withEm D E) = K D) : ∀ (q : ℕ) {X : Scheme.{u}}
    (C : MonomialData X) (E : OrderedDivisor X), flat E = flat C.E →
      MonomialData.stepPhase m r K q (withEm C E) = MonomialData.stepPhase m r K q C
  | 0, _, C, E, h => hK C E h
  | q + 1, _, C, E, h => by
    simp only [MonomialData.stepPhase]
    rw [step_eq_stepAt, step_eq_stepAt, stepCenter_congr C E h r]
    exact congrArg _ (stepPhase_congr m r K hK q (stepAt C m (C.stepCenter r)) _
      (flat_totalTransform_eq h _))

private theorem monomialOrderReductionFrom_congr (m : ℕ) : ∀ (j r : ℕ) {X : Scheme.{u}}
    (C : MonomialData X) (E : OrderedDivisor X), flat E = flat C.E →
      MonomialData.monomialOrderReductionFrom m j r (withEm C E) =
        MonomialData.monomialOrderReductionFrom m j r C
  | 0, _, _, _, _, _ => rfl
  | j + 1, r, _, C, E, h => by
    have hiter : ∀ N, ((withEm C E).iterate m r N).2.maxStratumWeight r =
        (C.iterate m r N).2.maxStratumWeight r :=
      fun N => iterate_maxStratumWeight_congr m r N C E h
    have hK := fun {Y : Scheme.{u}} (D : MonomialData Y) (E : OrderedDivisor Y)
      (hD : flat E = flat D.E) => monomialOrderReductionFrom_congr m j (r + 1) D E hD
    have hp : ∀ {N}, ((withEm C E).iterate m r N).2.maxStratumWeight r < m ↔
        (C.iterate m r N).2.maxStratumWeight r < m := by
      intro N; rw [hiter N]
    simp only [MonomialData.monomialOrderReductionFrom]
    by_cases hex : ∃ N, (C.iterate m r N).2.maxStratumWeight r < m
    · have hex' : ∃ N, ((withEm C E).iterate m r N).2.maxStratumWeight r < m :=
        hex.imp fun _ => hp.2
      rw [dif_pos hex, dif_pos hex', Nat.find_congr' hp]
      exact stepPhase_congr m r _ hK _ C E h
    · have hex' : ¬ ∃ N, ((withEm C E).iterate m r N).2.maxStratumWeight r < m :=
        fun ⟨N, hN⟩ => hex ⟨N, hp.1 hN⟩
      rw [dif_neg hex, dif_neg hex']
      exact hK C E h

/-- The monomial order reduction only sees the nonempty entries of the divisor. -/
private theorem monomialOrderReduction_congr (C : MonomialData X)
    (E : OrderedDivisor X) (h : flat E = flat C.E) (m : ℕ) :
    MonomialData.monomialOrderReduction ({ C with E := E } : MonomialData X) m =
      C.monomialOrderReduction m :=
  monomialOrderReductionFrom_congr m _ 1 C E h

end Monomial

/-! ### Facts about the rounds of Steps 1 and 2 -/

section RoundFacts

/-- For a sequence of order `≥ m` starting with a marked triple, the end of the sequence, with the
marked and total transforms, is a triple. -/
private theorem isTriple_end {k : Type u} [Field k] {X : Scheme.{u}} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), S.IsOrderGeMarkedTripleSeq s a E →
      IsTriple (S.toBase ≫ s) (S.markedTransform a).I (S.orderedTotalTransform E)
  | .nil X, s, a, E, h => by
    show IsTriple (𝟙 X ≫ s) a.I E
    rwa [Category.id_comp]
  | .cons Z S, s, a, E, h => by
    have := isTriple_end S _ _ _ h.2.2.2.2.2
    show IsTriple ((S.toBase ≫ blowUpToBase Z) ≫ s) _ _
    rwa [Category.assoc]

/-- One round: a sequence of order `μ ≥ m` for `(X, N(I), E)` is of order `≥ m` for
`(X, I, m, E)`, and the nonmonomial parts of the transforms of `(I, m)` are the controlled
transforms of `N(I)`. -/
private theorem isOrderGe_of_isOrderM {k : Type u} [Field k] {m μ : ℕ} (hm : 1 ≤ m)
    (hmμ : m ≤ μ) {X : Scheme.{u}} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
      (E : OrderedDivisor X), IsTriple s I E →
      S.IsOrderMTripleSeq s (nonmonomialPart I E) E μ →
      S.IsOrderGeMarkedTripleSeq s ⟨I, m⟩ E ∧
        nonmonomialPart (S.markedTransform ⟨I, m⟩).I (S.orderedTotalTransform E) =
          S.controlledTransform (nonmonomialPart I E)
  | .nil _, s, I, E, hI, _ => ⟨hI, rfl⟩
  | .cons Z S, s, I, E, hI, hS => by
    obtain ⟨-, hZsm, hZcod, hZsnc, hZord, hS'⟩ := hS
    have hN : OrderAlongGE (nonmonomialPart I E) (Z.support : Set X) m := fun W hW => by
      rw [hZord W hW]; exact_mod_cast hmμ
    obtain ⟨hIZ, heq⟩ := nonmonomialPart_birationalTransform s hI hm hZsm hZsnc hN
    have hI' := isTriple_birationalTransform_totalTransform (⟨I, m⟩ : MarkedIdeal X) hI hZsnc
    rw [← heq] at hS'
    have ih := isOrderGe_of_isOrderM hm hmμ S (blowUpToBase Z ≫ s)
      ((⟨I, m⟩ : MarkedIdeal X).birationalTransform Z).I
      (E.totalTransform Z) hI' hS'
    exact ⟨⟨hI, hZsm, hZcod, hZsnc, hIZ, ih.1⟩, ih.2.trans (congrArg S.controlledTransform heq)⟩

/-- A nonempty scheme carrying a triple has Krull dimension `dimNat X`. -/
private theorem topologicalKrullDim_eq_dimNat {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    [Nonempty X] : topologicalKrullDim X = ((dimNat X : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨-, -, hlft, hqc, -⟩ := h
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType k s
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    unfold topologicalKrullDim
    rw [Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  unfold dimNat
  generalize topologicalKrullDim X = e at htop hbot ⊢
  induction e using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe e =>
    induction e using WithTop.recTopCoe with
    | top => exact absurd rfl htop
    | coe n => rfl

/-- A generic point of `X` lies off a closed subscheme all of whose components have positive
codimension. -/
private theorem notMem_supportSet_of_mem_genericPoints {X : Scheme.{u}}
    {Z : X.IdealSheafData} (hZ : HasComponentsOfPositiveCodim (Z.support : Set X)) {ξ : X}
    (hξ : ξ ∈ genericPoints X) : ξ ∉ Z.supportSet := by
  intro h
  have h' : ξ ∈ (Z.support : Set X) := Scheme.IdealSheafData.mem_supportSet_iff_mem_support.1 h
  obtain ⟨W, hW, hξW⟩ := exists_mem_componentsOf h'
  have hD : closure {ξ} ∈ irreducibleComponents X := hξ
  have hDW : closure {ξ} ⊆ closure W := closure_mono (Set.singleton_subset_iff.2 hξW)
  have hcod := hZ W hW
  rw [codimension_eq_coheight] at hcod
  have hmax : IsMax (irreducibleClosure hW.1.1) := fun C hC => by
    have hC' : closure W ⊆ (C : Set X) := hC
    have : (C : Set X) ⊆ closure {ξ} := hD.2 C.isIrreducible (hDW.trans hC')
    exact this.trans hDW
  rw [Order.coheight_eq_zero.2 hmax] at hcod
  exact absurd hcod (by norm_num)

/-- The blow-up of an equidimensional scheme locally of finite type over a field along a closed
subscheme all of whose components have positive codimension has the same dimension. -/
private theorem topologicalKrullDim_blowUp {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] (hX : TopologicalSpace.Equidimensional X)
    (Z : X.IdealSheafData) (hZ : HasComponentsOfPositiveCodim (Z.support : Set X)) :
    topologicalKrullDim (blowUp Z) = topologicalKrullDim X := by
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents (blowUp Z),
    topologicalKrullDim_eq_iSup_irreducibleComponents X]
  apply le_antisymm
  · refine iSup₂_le fun C hC => ?_
    obtain ⟨D, hD, h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp s Z hC
    rw [h]
    exact le_iSup₂ (f := fun D (_ : D ∈ irreducibleComponents X) => topologicalKrullDim D) D hD
  · refine iSup₂_le fun D hD => ?_
    have hgen := hD.1.isGenericPoint_genericPoint_closure
    rw [(isClosed_of_mem_irreducibleComponents D hD).closure_eq] at hgen
    have hξ : hD.1.genericPoint ∈ genericPoints X := by
      change closure {_} ∈ irreducibleComponents X
      rwa [hgen.def]
    obtain ⟨η, hη, -⟩ := (bijOn_genericPoints_blowUpToBase Z).2.2
      ⟨hξ, notMem_supportSet_of_mem_genericPoints hZ hξ⟩
    have hC : closure {η} ∈ irreducibleComponents (blowUp Z) := hη
    obtain ⟨D', hD', h⟩ := exists_topologicalKrullDim_eq_of_mem_irreducibleComponents_blowUp s Z hC
    rw [hX D hD D' hD', ← h]
    exact le_iSup₂ (f := fun C (_ : C ∈ irreducibleComponents (blowUp Z)) =>
      topologicalKrullDim C) _ hC

/-- The end of a smooth blow-up sequence of order `≥ m` starting with a marked triple has the
dimension of its start. -/
private theorem topologicalKrullDim_target_of_isOrderGe {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E →
      topologicalKrullDim B.target = topologicalKrullDim X
  | _, .nil _, _, _, _, _ => rfl
  | _, .cons Z B, s, a, E, hB => by
    obtain ⟨⟨-, -, hlft, -, hequi, -, -⟩, -, hc, -, -, hB'⟩ := hB
    haveI : LocallyOfFiniteType s := hlft
    exact (topologicalKrullDim_target_of_isOrderGe B _ _ _ hB').trans
      (topologicalKrullDim_blowUp s hequi Z hc)

/-- The end of a smooth blow-up sequence of order `≥ m` has the `dimNat` of its start. -/
private theorem dimNat_target_of_isOrderGe {k : Type u} [Field k] {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
    (E : OrderedDivisor X) (hB : B.IsOrderGeMarkedTripleSeq s a E) :
    dimNat B.target = dimNat X := by
  simp only [dimNat, topologicalKrullDim_target_of_isOrderGe B s a E hB]

/-- Replacing the ideal of a triple by its nonmonomial part `N(I)` gives a triple. -/
private theorem isTriple_nonmonomialPart {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E) :
    IsTriple s (nonmonomialPart I E) E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun η hη hbot => h6 η hη (eq_bot_iff.2 ?_), h7⟩
  rw [← hbot]
  exact stalk_le_stalk_of_le (le_idealColon _ _) η

private theorem nonempty_of_one_le_maxOrder {X : Scheme.{u}} {I : X.IdealSheafData}
    (h : 1 ≤ maxOrder I) : Nonempty X := by
  by_contra hX
  rw [not_nonempty_iff] at hX
  simp [maxOrder, maxOrderAlong] at h

/-- For a triple, the maximal order of `N(I)` along a set is finite. -/
private theorem maxOrderAlong_nonmonomialPart_ne_top {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    (Z : Set X) : maxOrderAlong (nonmonomialPart I E) Z ≠ ⊤ := by
  rcases Z.eq_empty_or_nonempty with rfl | hZ
  · simp [maxOrderAlong]
  have hN := (isTriple_nonmonomialPart h).2.2.2.2.2.1
  obtain ⟨-, hsm, hlft, hqc, -, -, -⟩ := h
  haveI : LocallyOfFiniteType s := hlft
  haveI : QuasiCompact s := hqc
  haveI : Smooth s := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x =>
    haveI := isRegularLocalRing_stalk_of_smooth_over_field s x
    haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk x)
    inferInstance
  haveI : IsReduced X := isReduced_of_isReduced_stalk _
  refine (exists_multAt_eq_maxOrderAlong s _ ?_ hZ).1
  intro W hW hsub
  have hgen := (QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)).choose_spec
  set η := (QuasiSober.sober hW.1 (isClosed_of_mem_irreducibleComponents W hW)).choose
  have hη : closure ({η} : Set X) ∈ irreducibleComponents X := by
    rwa [hgen.def]
  have hF := isField_stalk_of_closure_mem_irreducibleComponents X η hη
  have hbot := hN η hη
  have htop : IdealSheafData.stalk (nonmonomialPart I E) η ≠ ⊤ := fun h =>
    (IdealSheafData.stalk_eq_top_iff_notMem_support _ η).1 h (hsub hgen.mem)
  letI := hF.toField
  exact (Ideal.eq_bot_or_top _).elim hbot htop

/-- Replacing the ideal of a triple by `K_s(I, m) = N(I)^m + I^s` gives a triple. -/
private theorem isTriple_mixedIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    (m n : ℕ) : IsTriple s (mixedIdeal I E m n) E := by
  have hN := (isTriple_nonmonomialPart h).2.2.2.2.2.1
  obtain ⟨h1, hsm, hlft, h4, h5, h6, h7⟩ := h
  refine ⟨h1, hsm, hlft, h4, h5, fun η hη h0 => ?_, h7⟩
  haveI : LocallyOfFiniteType s := hlft
  haveI : Smooth s := (MMP.Mori.isSmoothScheme_iff _).1 hsm
  haveI := isRegularLocalRing_stalk_of_smooth_over_field s η
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk η)
  have h1 := stalk_le_stalk_of_le
    (show nonmonomialPart I E ^ m ≤ mixedIdeal I E m n from le_self_add) η
  rw [h0, Aux.stalk_pow, le_bot_iff] at h1
  exact hN η hη (eq_zero_of_pow_eq_zero h1)

/-- Every blow-up sequence is one of its truncations. -/
private theorem exists_truncate_eq {X : Scheme.{u}} :
    ∀ S : ClosedBlowupSequence X, ∃ i, S.truncate i = S
  | .nil _ => ⟨0, rfl⟩
  | .cons Z S => by
    obtain ⟨i, hi⟩ := exists_truncate_eq S
    exact ⟨i + 1, by rw [ClosedBlowupSequence.truncate, hi]⟩

/-- The true branch of an `if` of blow-up sequences, for any `Decidable` instance and with the
branches typed only up to defeq. -/
private theorem ite_pos_eq {X : Scheme.{u}} {p : Prop} {_ : Decidable p}
    (x y : ClosedBlowupSequence X) (hp : p) : (if p then x else y) = x := by
  rw [if_pos hp]

end RoundFacts

/-! ### Reduced pull-backs -/

section ReducedPullback

open ClosedBlowupSequence

/-- A reduced pull-back has no empty blow-ups. -/
private theorem hasNoEmptyBlowups_pullbackReduced {X : Scheme.{u}} (S : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (h : Y ⟶ X), (S.pullbackReduced h).HasNoEmptyBlowups := by
  induction S with
  | nil X => intro Y h; trivial
  | cons Z S ih =>
    intro Y h
    by_cases hZ : Z.comap h = ⊤
    · simpa only [pullbackReduced, hZ, dite_true] using ih _
    · simp only [pullbackReduced, hZ, dite_false]
      exact ⟨hZ, ih _⟩

/-- A concatenation of sequences without empty blow-ups has none. -/
private theorem hasNoEmptyBlowups_append {X : Scheme.{u}} (D : ClosedBlowupSequence X) :
    ∀ (C : ClosedBlowupSequence D.target), D.HasNoEmptyBlowups → C.HasNoEmptyBlowups →
      (D.append C).HasNoEmptyBlowups := by
  induction D with
  | nil X => exact fun _ _ hC => hC
  | cons Z D ih => exact fun C hD hC => ⟨hD.1, ih C hD.2 hC⟩

/-- A smooth blow-up sequence of order `μ` without empty blow-ups starting with an ideal of
maximal order `< μ` is empty. -/
private theorem eq_nil_of_maxOrder_lt {k : Type u} [Field k] {X : Scheme.{u}}
    (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (J : X.IdealSheafData)
    (E : OrderedDivisor X) (μ : ℕ) (hS : S.IsOrderMTripleSeq s J E μ)
    (hne : S.HasNoEmptyBlowups) (hlt : maxOrder J < μ) : S = .nil X := by
  cases S with
  | nil => rfl
  | cons Z S =>
    exfalso
    obtain ⟨-, -, -, -, hord, -⟩ := hS
    obtain ⟨x, hx⟩ : ((Z.support : Set X)).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h0
      exact hne.1 ((Scheme.IdealSheafData.support_eq_bot_iff Z).1 (Closeds.ext h0))
    obtain ⟨W, hW, -⟩ := exists_mem_componentsOf hx
    have h2 : orderAlong J hW.1.1 ≤ maxOrder J :=
      le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt J z) _ (Set.mem_univ _)
    rw [hord W hW] at h2
    exact lt_irrefl _ (h2.trans_lt hlt)

/-- The reduced pull-back of a concatenation whose first part pulls back to the empty
sequence. -/
private theorem append_pullbackReduced_of_eq_nil {Y T : Scheme.{u}} (C : ClosedBlowupSequence T)
    (p : Σ C' : ClosedBlowupSequence Y, C'.target ⟶ T) (e : p.1 = nil Y) :
    p.1.append (C.pullbackReduced p.2) =
      C.pullbackReduced (eqToHom (congrArg target e.symm) ≫ p.2) := by
  obtain ⟨C', f⟩ := p
  dsimp only at e ⊢
  subst e
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-- The structure morphism of the reduced pull-back, followed by `h`, factors through the last
morphism and the end of `𝐒`. -/
private theorem toBase_comp_comp_eq {X Y Z : Scheme.{u}} (S : ClosedBlowupSequence X)
    (h : Y ⟶ X) (s : X ⟶ Z) :
    (S.pullbackReduced h).toBase ≫ h ≫ s = S.pullbackReducedHom h ≫ S.toBase ≫ s := by
  rw [← Category.assoc, pullbackReducedHom_toBase_comm, Category.assoc]

/-- If the reduced pull-back of `𝐒` along `h` is empty, `h` itself factors through the last
morphism `Y → X_r` and the end of `𝐒`. -/
private theorem comp_eq_of_pullbackReduced_eq_nil {X Y Z : Scheme.{u}}
    (S : ClosedBlowupSequence X) (h : Y ⟶ X) (e : S.pullbackReduced h = nil Y) (s : X ⟶ Z) :
    h ≫ s = (eqToHom (congrArg target e.symm) ≫ S.pullbackReducedHom h) ≫ S.toBase ≫ s := by
  have key : ∀ (C : ClosedBlowupSequence Y) (f : C.target ⟶ S.target) (e : C = nil Y),
      C.toBase ≫ h = f ≫ S.toBase →
        h ≫ s = (eqToHom (congrArg target e.symm) ≫ f) ≫ S.toBase ≫ s := by
    rintro C f rfl hf
    rw [eqToHom_refl, Category.id_comp, ← Category.assoc, ← hf]
    exact (Category.id_comp _).symm
  exact key _ _ e (S.pullbackReducedHom_toBase_comm h)

/-- The last morphism of an empty reduced pull-back of `𝐒` along a smooth `h` is smooth. -/
private theorem smooth_eqToHom_comp_pullbackReducedHom {X Y : Scheme.{u}}
    (S : ClosedBlowupSequence X) (h : Y ⟶ X) [Smooth h] (e : S.pullbackReduced h = nil Y) :
    Smooth (eqToHom (congrArg target e.symm) ≫ S.pullbackReducedHom h) :=
  haveI := Kollar.smooth_pullbackReducedHom S h
  haveI : IsOpenImmersion (eqToHom (congrArg target e.symm)) := IsOpenImmersion.of_isIso _
  inferInstance

/-- `transforms_pullbackReducedWithHom` in terms of the reduced pull-back and its last
morphism. -/
private theorem transforms_pullbackReduced {k : Type u} [Field k] {X : Scheme.{u}}
    (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
    (E : OrderedDivisor X) (hS : S.IsOrderGeMarkedTripleSeq s a E) {Y : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian Y] (h : Y ⟶ X) (hh : IsReducedFlatBaseChange h)
    (E' : OrderedDivisor Y) (hE' : flat E' = flat (E.comap h)) :
    ((S.pullbackReduced h).markedTransform ⟨a.I.comap h, a.m⟩).I =
        (S.markedTransform a).I.comap (S.pullbackReducedHom h) ∧
      flat ((S.pullbackReduced h).orderedTotalTransform E') =
        flat ((S.orderedTotalTransform E).comap (S.pullbackReducedHom h)) := by
  have H := transforms_pullbackReducedWithHom S s a E hS h hh E' hE'
  rw [S.pullbackReducedWithHom_eq h] at H
  exact H

/-- If the reduced pull-back of `𝐒` is empty, `(h^*I, m)` and `E'` are the inverse images of the
transforms along `𝐒` under the induced morphism `Y → X_r`. -/
private theorem transforms_of_pullbackReduced_eq_nil {k : Type u} [Field k] {X : Scheme.{u}}
    (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
    (E : OrderedDivisor X) (hS : S.IsOrderGeMarkedTripleSeq s a E) {Y : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian Y] (h : Y ⟶ X) (hh : IsReducedFlatBaseChange h)
    (E' : OrderedDivisor Y) (hE' : flat E' = flat (E.comap h))
    (e : S.pullbackReduced h = .nil Y) :
    a.I.comap h = (S.markedTransform a).I.comap
        (eqToHom (congrArg ClosedBlowupSequence.target e.symm) ≫ S.pullbackReducedHom h) ∧
      flat E' = flat ((S.orderedTotalTransform E).comap
        (eqToHom (congrArg ClosedBlowupSequence.target e.symm) ≫ S.pullbackReducedHom h)) := by
  have key : ∀ (C : ClosedBlowupSequence Y) (f : C.target ⟶ S.target) (e : C = .nil Y),
      (C.markedTransform ⟨a.I.comap h, a.m⟩).I = (S.markedTransform a).I.comap f ∧
        flat (C.orderedTotalTransform E') = flat ((S.orderedTotalTransform E).comap f) →
      a.I.comap h = (S.markedTransform a).I.comap
          (eqToHom (congrArg ClosedBlowupSequence.target e.symm) ≫ f) ∧
        flat E' = flat ((S.orderedTotalTransform E).comap
          (eqToHom (congrArg ClosedBlowupSequence.target e.symm) ≫ f)) := by
    rintro C f rfl H
    simp only [eqToHom_refl, Category.id_comp]
    exact H
  exact key _ _ e (transforms_pullbackReduced S s a E hS h hh E' hE')

end ReducedPullback

/-! ### One round of Steps 1 and 2 along a smooth morphism -/

section Round

/-- A scheme of Krull dimension `n` has `dimNat` equal to `n`. -/
private theorem dimNat_eq_of_topologicalKrullDim {X : Scheme.{u}} {n : ℕ}
    (h : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞)) : dimNat X = n := by
  simp [dimNat, h]

/-- The class of triples of dimension `d` and maximal order `≤ μ` lies in the class of triples
of dimension in `[a, b]` and maximal order `≤ μ` when `d ∈ [a, b]`. -/
private theorem mem_idealTriplesOfDim_Icc {a b d μ : ℕ} (hd : d ∈ Set.Icc a b)
    {τ : FieldBlowupTriple.{u}} (hτ : τ ∈ idealTriplesOfDim {d} μ) :
    τ ∈ idealTriplesOfDim (Set.Icc a b) μ := by
  obtain ⟨h1, ⟨n, hn, h2⟩, h3⟩ := hτ
  rw [Set.mem_singleton_iff] at hn
  subst hn
  exact ⟨h1, ⟨n, hd, h2⟩, h3⟩

/-- A triple of dimension `d` has `dimNat` equal to `d`. -/
private theorem dimNat_of_mem_idealTriplesOfDim {d μ : ℕ} {τ : FieldBlowupTriple.{u}}
    (hτ : τ ∈ idealTriplesOfDim {d} μ) : dimNat τ.X = d := by
  obtain ⟨-, ⟨n, hn, hdim⟩, -⟩ := hτ
  rw [Set.mem_singleton_iff] at hn
  subst hn
  exact dimNat_eq_of_topologicalKrullDim hdim

/-- **One round along a smooth morphism.** Let `τ = (X, J, E)` be a triple of dimension in
`[a, b]` and maximal order `≤ μ`, `h : Y → X` smooth, and `E'` a divisor on `Y` with the same
nonempty entries as `h⁻¹E`. If `(Y, h^*J, h⁻¹E)` and `(Y, h^*J, E')` are triples of dimension
`d'` and maximal order `≤ μ`, then `𝓑_{d', μ}(Y, h^*J, E') = (h^*𝓑_{dim X, μ}(X, J, E))^red`: by
the hypothesis that `𝓑_{d', μ}` ignores empty entries, and by (2a). -/
private theorem round_eq_pullbackReduced {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B)
    (hBe : ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t))
    {μ : ℕ} (hμ : 1 ≤ μ) {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (J : X.IdealSheafData) (E : OrderedDivisor X) (h : Y ⟶ X) [Smooth h]
    [LocallyOfFiniteType (h ≫ sX)] [QuasiCompact (h ≫ sX)] (E' : OrderedDivisor Y)
    (hE' : flat E' = flat (E.comap h)) {d' : ℕ} (hd' : d' ∈ Set.Icc a b)
    (hτ : (⟨⟨X, J, E⟩, k, sX⟩ : FieldBlowupTriple.{u}) ∈ idealTriplesOfDim (Set.Icc a b) μ)
    (hP : (⟨⟨Y, J.comap h, E.comap h⟩, k, h ≫ sX⟩ : FieldBlowupTriple.{u}) ∈
      idealTriplesOfDim {d'} μ)
    (hY : (⟨⟨Y, J.comap h, E'⟩, k, h ≫ sX⟩ : FieldBlowupTriple.{u}) ∈ idealTriplesOfDim {d'} μ) :
    B d' μ ⟨⟨Y, J.comap h, E'⟩, k, h ≫ sX⟩ =
      (B (dimNat X) μ ⟨⟨X, J, E⟩, k, sX⟩).pullbackReduced h := by
  obtain ⟨F, hFB, -, hsm, -⟩ := hB μ hμ
  obtain ⟨_, e1⟩ := hBe d' hd' μ hμ _ hY
  obtain ⟨_, e2⟩ := hBe d' hd' μ hμ _ hP
  have e1' : B d' μ ⟨⟨Y, J.comap h, E'.deleteEmpty⟩, k, h ≫ sX⟩ =
      B d' μ ⟨⟨Y, J.comap h, E'⟩, k, h ≫ sX⟩ := e1
  have e2' : B d' μ ⟨⟨Y, J.comap h, (E.comap h).deleteEmpty⟩, k, h ≫ sX⟩ =
      B d' μ ⟨⟨Y, J.comap h, E.comap h⟩, k, h ≫ sX⟩ := e2
  have hP' := mem_idealTriplesOfDim_Icc hd' hP
  have hdY : dimNat Y = d' := dimNat_of_mem_idealTriplesOfDim hP
  have hc := hsm.2 ⟨⟨X, J, E⟩, k, sX⟩ hτ Y h inferInstance inferInstance inferInstance hP'
  rw [hFB] at hc
  have hc' : B (dimNat Y) μ ⟨⟨Y, J.comap h, E.comap h⟩, k, h ≫ sX⟩ =
      ((B (dimNat X) μ ⟨⟨X, J, E⟩, k, sX⟩).pullback h).reduction :=
    (hFB _ hP').symm.trans hc
  rw [← e1', deleteEmpty_eq_iff.2 hE', e2', ← hdY, hc', ClosedBlowupSequence.reduction_pullback]

/-- **An empty round.** If moreover `maxord h^*J < μ`, the reduced pull-back of the round
`𝓑_{dim X, μ}(X, J, E)` is empty: it is `𝓑_{d', μ}(Y, h^*J, h⁻¹E)`, a sequence of order `μ`
without empty blow-ups starting with an ideal of maximal order `< μ`. -/
private theorem round_pullbackReduced_eq_nil {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B)
    (hBe : ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t))
    {μ : ℕ} (hμ : 1 ≤ μ) {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    (J : X.IdealSheafData) (E : OrderedDivisor X) (h : Y ⟶ X) [Smooth h]
    [LocallyOfFiniteType (h ≫ sX)] [QuasiCompact (h ≫ sX)] {d' : ℕ} (hd' : d' ∈ Set.Icc a b)
    (hτ : (⟨⟨X, J, E⟩, k, sX⟩ : FieldBlowupTriple.{u}) ∈ idealTriplesOfDim (Set.Icc a b) μ)
    (hP : (⟨⟨Y, J.comap h, E.comap h⟩, k, h ≫ sX⟩ : FieldBlowupTriple.{u}) ∈
      idealTriplesOfDim {d'} μ)
    (hlt : maxOrder (J.comap h) < μ) :
    (B (dimNat X) μ ⟨⟨X, J, E⟩, k, sX⟩).pullbackReduced h = .nil Y := by
  rw [← round_eq_pullbackReduced hB hBe hμ sX J E h (E.comap h) rfl hd' hτ hP hP]
  obtain ⟨F, hFB, -⟩ := hB μ hμ
  have hP' := mem_idealTriplesOfDim_Icc hd' hP
  have h1 := F.isOrderMTripleSeq _ hP'
  have h2 := F.hasNoEmptyBlowups _ hP'
  rw [hFB] at h1 h2
  change ClosedBlowupSequence.IsOrderMTripleSeq (h ≫ sX) (J.comap h) (E.comap h) μ
    (B (dimNat Y) μ ⟨⟨Y, J.comap h, E.comap h⟩, k, h ≫ sX⟩) at h1
  change (B (dimNat Y) μ ⟨⟨Y, J.comap h, E.comap h⟩, k, h ≫ sX⟩).HasNoEmptyBlowups at h2
  rw [dimNat_of_mem_idealTriplesOfDim hP] at h1 h2
  exact eq_nil_of_maxOrder_lt _ _ _ _ _ h1 h2 hlt

end Round

/-! ### The invariant of Step 2 along a smooth morphism -/

section StepTwoOrder

/-- In `ℕ∞`, `a < n` gives `a ≤ n - 1`. -/
private theorem le_natCast_sub_one_of_lt {a : ℕ∞} {n : ℕ} (h : a < n) :
    a ≤ ((n - 1 : ℕ) : ℕ∞) := by
  induction a using ENat.recTopCoe with
  | top => exact absurd h (not_lt.2 le_top)
  | coe a =>
    have := ENat.coe_lt_coe.1 h
    exact_mod_cast (by omega : a ≤ n - 1)

/-- **`maxord K_s(I, m) < m·s` when `s` exceeds the invariant.** For a marked triple
`(X, I, m, E)` with `m, s ≥ 1` and `maxord_{cosupp(I, m)} N(I) < s`, the ideal
`K_s(I, m) = N(I)^m + I^s` has maximal order `< m·s`: at a point of the cosupport its order is at
most `m · ord N(I) ≤ m(s - 1)`, elsewhere at most `s · ord I ≤ s(m - 1)`. -/
private theorem maxOrder_mixedIdeal_lt {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (m s : ℕ)
    (hT : IsTriple sX I E) (hm : 1 ≤ m) (hs1 : 1 ≤ s)
    (hs : maxOrderAlong (nonmonomialPart I E) (MarkedIdeal.cosupport ⟨I, m⟩) < s) :
    maxOrder (mixedIdeal I E m s) < ((m * s : ℕ) : ℕ∞) := by
  obtain ⟨-, hsm, hlft, -⟩ := hT
  haveI : LocallyOfFiniteType sX := hlft
  haveI : Smooth sX := Aux.smooth_of_isSmoothScheme' sX hsm
  have hms : 1 ≤ m * s := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hA : m * (s - 1) ≤ m * s - 1 := by rw [Nat.mul_sub_one]; omega
  have hB' : s * (m - 1) ≤ m * s - 1 := by rw [Nat.mul_sub_one, Nat.mul_comm s m]; omega
  have key : ∀ x : X, multAt (mixedIdeal I E m s) x ≤ ((m * s - 1 : ℕ) : ℕ∞) := by
    intro x
    haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
      isRegularLocalRing_stalk_of_smooth_over_field sX x
    have hpow : ∀ {J K : X.IdealSheafData} {n : ℕ}, J ^ n ≤ K → multAt K x ≤ n * multAt J x :=
      fun h => (Kollar.multAt_antitone h x).trans_eq (multAt_pow x _ _)
    by_cases hx : (m : ℕ∞) ≤ multAt I x
    · have hN : multAt (nonmonomialPart I E) x < s :=
        lt_of_le_of_lt (le_iSup₂ (f := fun z (_ : z ∈ MarkedIdeal.cosupport ⟨I, m⟩) =>
          multAt (nonmonomialPart I E) z) x hx) hs
      calc _ ≤ m * multAt (nonmonomialPart I E) x := hpow le_sup_left
        _ ≤ (m : ℕ∞) * ((s - 1 : ℕ) : ℕ∞) := by gcongr; exact le_natCast_sub_one_of_lt hN
        _ = ((m * (s - 1) : ℕ) : ℕ∞) := by push_cast; rfl
        _ ≤ _ := by exact_mod_cast hA
    · calc _ ≤ s * multAt I x := hpow le_sup_right
        _ ≤ (s : ℕ∞) * ((m - 1 : ℕ) : ℕ∞) := by
          gcongr; exact le_natCast_sub_one_of_lt (not_le.1 hx)
        _ = ((s * (m - 1) : ℕ) : ℕ∞) := by push_cast; rfl
        _ ≤ _ := by exact_mod_cast hB'
  exact (iSup₂_le fun x _ => key x).trans_lt (by exact_mod_cast (by omega : m * s - 1 < m * s))

/-- In `ℕ∞`, `a < n` gives `a.toNat < n`. -/
private theorem toNat_lt_of_lt {a : ℕ∞} {n : ℕ} (h : a < n) : a.toNat < n := by
  induction a using ENat.recTopCoe with
  | top => exact absurd h (not_lt.2 le_top)
  | coe a => simpa using h

end StepTwoOrder

/-- `h⁻¹(g⁻¹E) = (h ≫ g)⁻¹E`. -/
private theorem OrderedDivisor.comap_comap {X Y Z : Scheme.{u}} (E : OrderedDivisor X)
    (g : Y ⟶ X) (h : Z ⟶ Y) : (E.comap g).comap h = E.comap (h ≫ g) := by
  simp only [OrderedDivisor.comap, Scheme.IdealSheafData.comap_comp]

/-! ### The extension by closure under reduced pull-back -/

section ExtendByClosure

open ClosedBlowupSequence

/-- The reduced pull-back along a morphism precomposed with an `eqToHom`. -/
private theorem pullbackReduced_eqToHom_comp_heq {X Y Y' : Scheme.{u}}
    (S : ClosedBlowupSequence X) (e : Y = Y') (f : Y' ⟶ X) :
    S.pullbackReduced (eqToHom e ≫ f) ≍ S.pullbackReduced f := by
  subst e
  simp

/-- For flat `ι : U → X`, `B_WU` with `W = ι⁻¹Z'` is the base change of `B_{Z'}X` along `ι`. -/
private theorem isPullback_canonicalLift_of_comap_eq {U X : Scheme.{u}} (ι : U ⟶ X) [Flat ι]
    (Z' : X.IdealSheafData) (W : U.IdealSheafData) (e : Z'.comap ι = W) :
    IsPullback (eqToHom (congrArg blowUp e.symm) ≫ canonicalLift ι Z') (blowUpToBase W)
      (blowUpToBase Z') ι := by
  subst e
  simpa using (Kollar.isPullback_canonicalLift_of_flat ι Z').flip

/-- **The extension by closure commutes with reduced flat base change.** Let `U_Y → Y`,
`U_Y → U` over `g : Y → X`, `ι : U → X` be a cartesian square with `ι` (hence `U_Y → Y`) a
quasi-compact open immersion and `g` flat with reduced base changes, and let `𝐁` be a blow-up
sequence starting with `U` with reduced centres. Then the reduced pull-back along `g` of the
extension by closure of `𝐁` along `ι` is the extension by closure of `(g_U^*𝐁)^red`. A centre
`Z` of `𝐁` has empty inverse image in `U_Y` exactly when its closure has empty inverse image in
`Y`, and then both steps are skipped. -/
private theorem extendByClosure_pullbackReduced {U : Scheme.{u}} (B : ClosedBlowupSequence U)
    (hB : B.HasReducedCentres) : ∀ {X Y UY : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
      [QuasiCompact ι] (g : Y ⟶ X) (_ : IsReducedFlatBaseChange g) (ιY : UY ⟶ Y)
      [IsOpenImmersion ιY] [QuasiCompact ιY] (gU : UY ⟶ U) (_ : IsPullback ιY gU g ι),
      (B.extendByClosure ι).pullbackReduced g = (B.pullbackReduced gU).extendByClosure ιY := by
  induction B with
  | nil U => intros; rfl
  | cons Z B ih =>
    intro X Y UY ι _ _ g hg ιY _ _ gU sq
    have := hB.1
    have := hg.flat
    have hc := comap_map_eq_of_isOpenImmersion ι Z
    have eY := Kollar.comap_map_eq_map_comap_of_isPullback sq hg Z
    have hcY := comap_map_eq_of_isOpenImmersion ιY (Z.comap gU)
    rw [extendByClosure_cons_of_comap_map_eq Z B ι hc]
    have : IsOpenImmersion (canonicalLift ι (Z.map ι)) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (Kollar.isPullback_canonicalLift_of_flat ι (Z.map ι)) ‹_›
    have : QuasiCompact (canonicalLift ι (Z.map ι)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (Kollar.isPullback_canonicalLift_of_flat ι (Z.map ι)) ‹_›
    by_cases hZ : Z.comap gU = ⊤
    · have hZ' : (Z.map ι).comap g = ⊤ := by rw [eY, hZ, Scheme.IdealSheafData.map_top]
      have h1 : (cons (Z.map ι) (B.extendByClosure
          (eqToHom (congrArg blowUp hc.symm) ≫ canonicalLift ι (Z.map ι)))).pullbackReduced g =
          (B.extendByClosure (eqToHom (congrArg blowUp hc.symm) ≫
            canonicalLift ι (Z.map ι))).pullbackReduced
              (blowUpLift (Z.map ι) g (isCartierOver_of_comap_eq_top g _ hZ')) := dif_pos hZ'
      have h2 : (cons Z B).pullbackReduced gU =
          B.pullbackReduced (blowUpLift Z gU (isCartierOver_of_comap_eq_top gU Z hZ)) :=
        dif_pos hZ
      rw [h1, h2]
      have hlow := isPullback_canonicalLift_of_comap_eq ι (Z.map ι) Z hc
      have hg' := isReducedFlatBaseChange_blowUpLift hg (Z.map ι) hZ'
      have hcart : Stacks.Blowup.IsCartierOver (Z.map ι) (Over.mk (ιY ≫ g)) :=
        isCartierOver_of_comap_eq_top _ _ (by
          rw [Scheme.IdealSheafData.comap_comp, hZ', Scheme.IdealSheafData.comap_top])
      have hp : ιY ≫ blowUpLift (Z.map ι) g (isCartierOver_of_comap_eq_top g _ hZ') =
          blowUpLift Z gU (isCartierOver_of_comap_eq_top gU Z hZ) ≫
            (eqToHom (congrArg blowUp hc.symm) ≫ canonicalLift ι (Z.map ι)) := by
        refine Kollar.blowUpLift_ext hcart ?_ ?_
        · rw [Category.assoc, blowUpLift_comp]
        · rw [Category.assoc, hlow.w, ← Category.assoc, blowUpLift_comp]
          exact sq.w.symm
      have hs : IsPullback ιY (blowUpLift Z gU (isCartierOver_of_comap_eq_top gU Z hZ) ≫
          blowUpToBase Z) (blowUpLift (Z.map ι) g (isCartierOver_of_comap_eq_top g _ hZ') ≫
            blowUpToBase (Z.map ι)) ι := by
        rw [blowUpLift_comp, blowUpLift_comp]
        exact sq
      exact ih hB.2 _ _ hg' ιY _ (IsPullback.of_bot hs hp hlow)
    · have hZ' : (Z.map ι).comap g ≠ ⊤ := by
        rw [eY]
        intro h
        apply hZ
        rw [← hcY, h, Scheme.IdealSheafData.comap_top]
      have h1 : (cons (Z.map ι) (B.extendByClosure
          (eqToHom (congrArg blowUp hc.symm) ≫ canonicalLift ι (Z.map ι)))).pullbackReduced g =
          cons ((Z.map ι).comap g) ((B.extendByClosure (eqToHom (congrArg blowUp hc.symm) ≫
            canonicalLift ι (Z.map ι))).pullbackReduced (canonicalLift g (Z.map ι))) :=
        dif_neg hZ'
      have h2 : (cons Z B).pullbackReduced gU =
          cons (Z.comap gU) (B.pullbackReduced (canonicalLift gU Z)) := dif_neg hZ
      rw [h1, h2, extendByClosure_cons_of_comap_map_eq _ _ ιY hcY]
      refine cons_eq_cons_iff.2 ⟨eY, ?_⟩
      have sq' := Kollar.isPullback_canonicalLift_of_isPullback sq (Z.map ι) Z hc _ eY hcY
      have hg1 := Kollar.isReducedFlatBaseChange_eqToHom_comp (congrArg blowUp eY.symm)
        (hg.canonicalLift (Z.map ι))
      have : IsOpenImmersion (canonicalLift ιY ((Z.comap gU).map ιY)) :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion)
          (Kollar.isPullback_canonicalLift_of_flat ιY ((Z.comap gU).map ιY)) ‹_›
      have : QuasiCompact (canonicalLift ιY ((Z.comap gU).map ιY)) :=
        MorphismProperty.of_isPullback (P := @QuasiCompact)
          (Kollar.isPullback_canonicalLift_of_flat ιY ((Z.comap gU).map ιY)) ‹_›
      have key := ih hB.2 _ _ hg1 _ _ sq'
      exact (pullbackReduced_eqToHom_comp_heq _ _ _).symm.trans (heq_of_eq key)

end ExtendByClosure

/-! ### Step 3 along a smooth morphism -/

section StepThree

variable {X : Scheme.{u}}

/-- In a discrete valuation ring the order of `𝔪ⁿ` is `n`. -/
private theorem idealOrder_maximalIdeal_pow {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (n : ℕ) :
    idealOrder (IsLocalRing.maximalIdeal R ^ n) = n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have key : ∀ j : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ IsLocalRing.maximalIdeal R ^ j ↔ j ≤ n := by
    intro j
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow,
      Ideal.span_singleton_le_span_singleton]
    exact pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit
  refine le_antisymm (iSup₂_le fun j hj => by exact_mod_cast (key j).1 hj) ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : IsLocalRing.maximalIdeal R ^ n ≤
    IsLocalRing.maximalIdeal R ^ j) => (j : ℕ∞)) n le_rfl le_rfl

private theorem genericPoint_mem_support (D : AlgebraicGeometry.PrimeDivisor X) :
    D.genericPoint ∈ D.support := by
  have : D.genericPoint ∈ closure ({D.genericPoint} : Set X) := subset_closure rfl
  rwa [← support_eq_closure_genericPoint] at this

/-- On a smooth scheme over a field, the local ring at the generic point of a prime divisor is a
discrete valuation ring. -/
private theorem isDiscreteValuationRing_stalk_genericPoint {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    ∃ _ : IsDomain (X.presheaf.stalk D.genericPoint),
      IsDiscreteValuationRing (X.presheaf.stalk D.genericPoint) := by
  haveI := smooth_of_isSmoothScheme' sX h
  haveI := isRegularLocalRing_stalk_of_smooth_over_field sX D.genericPoint
  haveI := IsRegularLocalRing.isDomain (X.presheaf.stalk D.genericPoint)
  obtain ⟨π, hπ, hπD⟩ := exists_prime_stalk_idealSheaf sX h D (genericPoint_mem_support D)
  rw [stalk_idealSheaf_genericPoint] at hπD
  refine ⟨inferInstance, ?_⟩
  have hnf : ¬ IsField (X.presheaf.stalk D.genericPoint) := by
    intro hf
    have h0 := IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
    rw [h0, eq_comm, Ideal.span_singleton_eq_bot] at hπD
    exact hπ.ne_zero hπD
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 5 1).mp
    (show Submodule.IsPrincipal (IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint)) from
      ⟨⟨π, hπD⟩⟩)

/-- The generic point of a prime divisor `D` lies on no other prime divisor. -/
private theorem genericPoint_notMem_support {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    {D D' : AlgebraicGeometry.PrimeDivisor X} (hne : D ≠ D') :
    D.genericPoint ∉ D'.support := by
  intro hx
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_genericPoint sX h D
  obtain ⟨π, hπ, hπD⟩ := exists_prime_stalk_idealSheaf sX h D' hx
  have hp : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hb : Ideal.span {π} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero
  have hm := IsLocalRing.eq_maximalIdeal (hp.isMaximal hb)
  refine hne (eq_of_stalk_idealSheaf_eq sX h D D' (genericPoint_mem_support D) hx ?_)
  rw [stalk_idealSheaf_genericPoint, hπD, hm]

/-- The stalk of `∏_{D'} I_{D'}^{A D'}` at the generic point of `D` is `𝔪^{A D}`. -/
private theorem stalk_prod_genericPoint {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (F : Finset (AlgebraicGeometry.PrimeDivisor X))
    (hF : ∀ D', A D' ≠ 0 → D' ∈ F) (D : AlgebraicGeometry.PrimeDivisor X) :
    IdealSheafData.stalk (∏ D' ∈ F, D'.idealSheaf ^ A D') D.genericPoint =
      IsLocalRing.maximalIdeal (X.presheaf.stalk D.genericPoint) ^ A D := by
  rw [Aux.stalk_prod]
  simp only [Aux.stalk_pow]
  have htop : ∀ D' ∈ F, D' ≠ D →
      IdealSheafData.stalk D'.idealSheaf D.genericPoint ^ A D' = 1 := by
    intro D' _ hne
    rw [(IdealSheafData.stalk_eq_top_iff_notMem_support _ _).2
      (genericPoint_notMem_support sX h (Ne.symm hne)), ← Ideal.one_eq_top, one_pow]
  by_cases hD : D ∈ F
  · rw [Finset.prod_eq_single D htop (fun h' => absurd hD h'), stalk_idealSheaf_genericPoint]
  · have h0 : A D = 0 := by
      by_contra h0; exact hD (hF D h0)
    rw [h0, pow_zero]
    exact Finset.prod_eq_one fun D' hD' => htop D' hD' (fun e => hD (e ▸ hD'))

/-- The order of `𝒪_X(-A)` at the generic point of a prime divisor `D` is `a_D`. -/
private theorem multAt_divisorIdeal_genericPoint {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (h : MMP.Mori.IsSmoothScheme sX)
    (A : AlgebraicGeometry.PrimeDivisor X → ℕ) (hfin : (Function.support A).Finite)
    (D : AlgebraicGeometry.PrimeDivisor X) :
    multAt (divisorIdeal A) D.genericPoint = A D := by
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_genericPoint sX h D
  rw [multAt, divisorIdeal_eq_prod A hfin,
    stalk_prod_genericPoint sX h A _ (fun D' hD' => by simpa using hD') D,
    idealOrder_maximalIdeal_pow]

/-- On an equidimensional scheme locally of finite type over a field, the local dimension at
every point is the dimension of any irreducible component. -/
private theorem topologicalKrullDimAt_eq_of_equidimensional (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : Equidimensional X) {C : Set X} (hC : C ∈ irreducibleComponents X)
    (x : X) : topologicalKrullDimAt X x = topologicalKrullDim C := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s x]
  refine le_antisymm (iSup₂_le fun D hD => (hX D hD.1 C hC).le) ?_
  exact (hX _ (irreducibleComponent_mem_irreducibleComponents x) C hC).symm.le.trans
    (le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents X ∧ x ∈ D}) =>
      topologicalKrullDim D) _ ⟨irreducibleComponent_mem_irreducibleComponents x,
        mem_irreducibleComponent⟩)

/-- The dimension of an irreducible component is the local dimension at its generic point. -/
private theorem exists_topologicalKrullDimAt_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) :
    ∃ η ∈ Z, topologicalKrullDimAt X η = topologicalKrullDim Z := by
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ.1 (isClosed_of_mem_irreducibleComponents Z hZ)
  refine ⟨η, hη.mem, ?_⟩
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s η]
  refine le_antisymm (iSup₂_le fun Z' hZ' => ?_)
    (le_iSup₂ (f := fun Z' (_ : Z' ∈ {Z' | Z' ∈ irreducibleComponents X ∧ η ∈ Z'}) =>
      topologicalKrullDim Z') Z ⟨hZ, hη.mem⟩)
  have hle : Z ⊆ Z' := by
    rw [← (show closure {η} = Z from hη)]
    exact (isClosed_of_mem_irreducibleComponents Z' hZ'.1).closure_subset_iff.2
      (Set.singleton_subset_iff.2 hZ'.2)
  rw [(hZ.2 hZ'.1.1 hle).antisymm hle]

/-- The restriction `(U, I|_U, E|_U)` of a triple to an open `U` is a triple. -/
private theorem isTriple_comap_opens {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E)
    (U : X.Opens) : IsTriple (U.ι ≫ s) (I.comap U.ι) (E.comap U.ι) := by
  let t : FieldBlowupTriple.{u} := ⟨⟨X, I, E⟩, k, s⟩
  have ht : t ∈ triples := h
  haveI : LocallyOfFiniteType s := h.2.2.1
  haveI : QuasiCompact s := h.2.2.2.1
  haveI := isNoetherian_of_isTriple h
  show t.pullback U.ι ∈ triples
  refine mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht) U.ι, ?_⟩
  intro W hW W' hW'
  obtain ⟨η, -, hη⟩ := exists_topologicalKrullDimAt_eq k (U.ι ≫ s) hW
  obtain ⟨η', -, hη'⟩ := exists_topologicalKrullDimAt_eq k (U.ι ≫ s) hW'
  have hC := irreducibleComponent_mem_irreducibleComponents (U.ι η)
  refine hη.symm.trans (Eq.trans ?_ hη')
  rw [← U.ι.isOpenEmbedding.topologicalKrullDimAt_eq η,
    ← U.ι.isOpenEmbedding.topologicalKrullDimAt_eq η',
    topologicalKrullDimAt_eq_of_equidimensional k s h.2.2.2.2.1 hC,
    topologicalKrullDimAt_eq_of_equidimensional k s h.2.2.2.2.1 hC]

/-- The restriction of a triple to an open `U` is a triple, and `(U, E|_U, A(I|_U))` is monomial
data on `U`. -/
private theorem isMonomialData_restrict {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (ht : IsTriple s I E)
    (U : X.Opens) :
    IsTriple (U.ι ≫ s) (I.comap U.ι) (E.comap U.ι) ∧
    (⟨k, U.ι ≫ s, E.comap U.ι, monomialPartCoeff (I.comap U.ι) (E.comap U.ι)⟩ :
      MonomialData U).IsMonomialData := by
  have htU := isTriple_comap_opens s ht U
  have hdec := (isMonomialDecomposition_iff _ htU _ _).2 ⟨rfl, rfl⟩
  exact ⟨htU, htU.2.1, htU.2.2.1, htU.2.2.2.1, htU.2.2.2.2.2.2, hdec.finite_support,
    hdec.isComponent_of_ne_zero⟩

/-- The coefficients of the monomial part are read off its orders along prime divisors. -/
private theorem monomialPartCoeff_eq_multAt {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) {I : X.IdealSheafData} {E : OrderedDivisor X} (ht : IsTriple s I E) :
    monomialPartCoeff I E =
      fun D => (multAt (divisorIdeal (monomialPartCoeff I E)) D.genericPoint).toNat := by
  have hdec := (isMonomialDecomposition_iff _ ht _ _).2 ⟨rfl, rfl⟩
  haveI : LocallyOfFiniteType s := ht.2.2.1
  funext D
  rw [multAt_divisorIdeal_genericPoint s ht.2.1 _ hdec.finite_support D, ENat.toNat_coe]

/-- The centres of a Step-3.`r` phase are reduced. -/
private theorem hasReducedCentres_stepPhase (m r : ℕ)
    (K : ∀ {Y : Scheme.{u}}, MonomialData Y → ClosedBlowupSequence Y)
    (hK : ∀ {Y : Scheme.{u}} (D : MonomialData Y), (K D).HasReducedCentres) :
    ∀ (q : ℕ) {Y : Scheme.{u}} (C : MonomialData Y),
      (MonomialData.stepPhase m r K q C).HasReducedCentres
  | 0, _, C => hK C
  | q + 1, _, C => by
    refine ⟨?_, hasReducedCentres_stepPhase m r K hK q _⟩
    change IsReduced (Scheme.IdealSheafData.vanishingIdeal _).subscheme
    infer_instance

/-- The centres of the monomial order reduction are reduced. -/
private theorem hasReducedCentres_monomialOrderReductionFrom (m : ℕ) :
    ∀ (j r : ℕ) {Y : Scheme.{u}} (C : MonomialData Y),
      (MonomialData.monomialOrderReductionFrom m j r C).HasReducedCentres
  | 0, _, _, _ => trivial
  | j + 1, r, _, C => by
    rw [MonomialData.monomialOrderReductionFrom]
    split_ifs
    · exact hasReducedCentres_stepPhase m r _
        (fun D => hasReducedCentres_monomialOrderReductionFrom m j (r + 1) D) _ C
    · exact hasReducedCentres_monomialOrderReductionFrom m j (r + 1) C

/-- The monomial data `(U, E|_U, A(I|_U))` of a triple on an open `U`. -/
private noncomputable abbrev restrictData (t : MarkedTriple.{u}) (U : t.X.Opens) : MonomialData U :=
  ⟨t.k, U.ι ≫ t.sX, t.E.comap U.ι, monomialPartCoeff (t.I.comap U.ι) (t.E.comap U.ι)⟩

/-- **Step 3 along a smooth morphism.** Let `(X, I, m, E)` be a marked triple, `h : Y → X` smooth,
`(Y, h^*I, m', E')` a marked triple with `E'` agreeing with `h⁻¹E` up to empty entries, and
`U ⊆ X` open. The extension by closure of the monomial order reduction of the monomial data on
`h⁻¹U` is the reduced pull-back of the one on `U`: the monomial data on `h⁻¹U` are the pull-back
of those on `U` up to empty entries, which the monomial order reduction ignores. -/
private theorem extendByClosure_monomialOrderReduction_pullbackReduced (t : MarkedTriple.{u})
    (ht : t ∈ markedTriples) {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h] (E' : OrderedDivisor Y)
    (hE' : flat E' = flat (t.E.comap h)) (m' : ℕ)
    (hT' : IsTriple (h ≫ t.sX) (t.I.comap h) E') (m : ℕ) (U : t.X.Opens) (V : Y.Opens)
    (hV : V = h ⁻¹ᵁ U) :
    ((restrictData ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m'⟩ V).monomialOrderReduction
        m).extendByClosure V.ι =
      (((restrictData t U).monomialOrderReduction m).extendByClosure U.ι).pullbackReduced h := by
  subst hV
  have hT : IsTriple t.sX t.I t.E := ht
  haveI : QuasiCompact (h ≫ t.sX) := hT'.2.2.2.1
  have hTP : IsTriple (h ≫ t.sX) (t.I.comap h) (t.E.comap h) :=
    isTriple_comap_of_smooth hT h hT'.2.2.2.2.1
  haveI := isNoetherian_of_isTriple hT
  haveI := isNoetherian_of_isTriple hT'
  haveI : CharZero t.k := ht.1
  have hh := IsReducedFlatBaseChange.of_smooth h
  have sqU := isPullback_morphismRestrict h U
  have hhU : IsReducedFlatBaseChange (h ∣_ U) := hh.of_isPullback sqU.flip
  haveI : Smooth (h ∣_ U) := MorphismProperty.of_isPullback (P := @Smooth) sqU.flip inferInstance
  obtain ⟨htU, hC⟩ := isMonomialData_restrict t.sX t.I t.E hT U
  have htV := isTriple_comap_opens (h ≫ t.sX) hTP (h ⁻¹ᵁ U)
  have hcomp : (h ∣_ U) ≫ U.ι = (h ⁻¹ᵁ U).ι ≫ h := morphismRestrict_ι h U
  have hIV : (t.I.comap U.ι).comap (h ∣_ U) = (t.I.comap h).comap (h ⁻¹ᵁ U).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp, Scheme.IdealSheafData.comap_comp]
  have hEV : (t.E.comap U.ι).comap (h ∣_ U) = (t.E.comap h).comap (h ⁻¹ᵁ U).ι := by
    rw [OrderedDivisor.comap_comap, hcomp, ← OrderedDivisor.comap_comap]
  haveI : LocallyOfFiniteType ((h ⁻¹ᵁ U).ι ≫ h ≫ t.sX) := htV.2.2.1
  haveI : QuasiCompact ((h ⁻¹ᵁ U).ι ≫ h ≫ t.sX) := htV.2.2.2.1
  have hM := monomialPart_comap (U.ι ≫ t.sX) htU ((h ⁻¹ᵁ U).ι ≫ h ≫ t.sX) htV.2.1 (h ∣_ U) hhU
  rw [hIV, hEV] at hM
  have hqc : QuasiCompact ((h ∣_ U) ≫ (restrictData t U).sX) := by
    change QuasiCompact ((h ∣_ U) ≫ U.ι ≫ t.sX)
    rw [← Category.assoc, hcomp, Category.assoc]
    infer_instance
  let D₀ : MonomialData (h ⁻¹ᵁ U) := ⟨t.k, (h ⁻¹ᵁ U).ι ≫ h ≫ t.sX,
    (t.E.comap h).comap (h ⁻¹ᵁ U).ι,
    monomialPartCoeff ((t.I.comap h).comap (h ⁻¹ᵁ U).ι) ((t.E.comap h).comap (h ⁻¹ᵁ U).ι)⟩
  have hD : (restrictData ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m'⟩
      (h ⁻¹ᵁ U)).monomialOrderReduction m = D₀.monomialOrderReduction m := by
    have hf : flat (E'.comap (h ⁻¹ᵁ U).ι) = flat D₀.E := flat_comap_eq hE' _
    rw [← monomialOrderReduction_congr D₀ (E'.comap (h ⁻¹ᵁ U).ι) hf m]
    change MonomialData.monomialOrderReduction ⟨t.k, (h ⁻¹ᵁ U).ι ≫ h ≫ t.sX,
      E'.comap (h ⁻¹ᵁ U).ι, monomialPartCoeff ((t.I.comap h).comap (h ⁻¹ᵁ U).ι)
        (E'.comap (h ⁻¹ᵁ U).ι)⟩ m = MonomialData.monomialOrderReduction ⟨t.k,
      (h ⁻¹ᵁ U).ι ≫ h ≫ t.sX, E'.comap (h ⁻¹ᵁ U).ι, monomialPartCoeff
        ((t.I.comap h).comap (h ⁻¹ᵁ U).ι) ((t.E.comap h).comap (h ⁻¹ᵁ U).ι)⟩ m
    rw [monomialPartCoeff_eq hf]
  have key := MonomialData.monomialOrderReduction_eq_pullback_reduction (restrictData t U) hC
    ‹_› (h ∣_ U) (Or.inl ⟨inferInstance, hqc⟩) D₀ hEV.symm (by
      change monomialPartCoeff _ _ = fun D' => (multAt ((monomialPart _ _).comap _) _).toNat
      rw [← hM]
      exact monomialPartCoeff_eq_multAt _ htV) m
  rw [ClosedBlowupSequence.reduction_pullback] at key
  rw [hD, key]
  exact (extendByClosure_pullbackReduced _ (hasReducedCentres_monomialOrderReductionFrom m _ _ _)
    U.ι h hh (h ⁻¹ᵁ U).ι (h ∣_ U) sqU.flip).symm

end StepThree

/-! ### Steps 1 and 2 along a smooth morphism -/

section Steps

open ClosedBlowupSequence

/-- **Step 1 along a smooth morphism.** Let `(X, I, m, E)` be a marked triple, `h : Y → X` smooth
and `(Y, h^*I, m', E')` a marked triple with `E'` agreeing with `h⁻¹E` up to empty entries. Then
the Step-1 recursion on `Y` is the reduced pull-back of the one on `X`, each run with fuel larger
than its invariant `maxord N`. A round of value `μ` on `X` is either a round of value `μ` on `Y`,
pulled back, or pulls back to the empty sequence, `maxord N` being smaller on `Y`. -/
private theorem bmoStepOneAux_pullbackReduced {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B)
    (hBe : ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t))
    {m : ℕ} (hm : 1 ≤ m) {d d' : ℕ} (hd : d ∈ Set.Icc a b) (hd' : d' ∈ Set.Icc a b) :
    ∀ (q : ℕ) (t : MarkedTriple.{u}), t ∈ markedTriples → dimNat t.X = d →
      (maxOrder (nonmonomialPart t.I t.E)).toNat < q →
      ∀ (q' : ℕ) {Y : Scheme.{u}} (h : Y ⟶ t.X), Smooth h → ∀ (I' : Y.IdealSheafData)
        (E' : OrderedDivisor Y) (s' : Y ⟶ Spec (.of t.k)) (m' : ℕ),
        I' = t.I.comap h → s' = h ≫ t.sX → flat E' = flat (t.E.comap h) → IsTriple s' I' E' →
        topologicalKrullDim Y = ((d' : ℕ∞) : WithBot ℕ∞) →
        (maxOrder (nonmonomialPart I' E')).toNat < q' →
        bmoStepOneAux B d' m q' ⟨⟨⟨Y, I', E'⟩, t.k, s'⟩, m'⟩ =
          (bmoStepOneAux B d m q t).pullbackReduced h
  | 0, _, _, _, hq, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hq (Nat.not_lt_zero _)
  | q + 1, t, ht, hdt, hq, q', Y, h, hsm, I', E', s', m', hI', hs', hE', hT', hdY, hq' => by
    subst hI' hs'
    haveI := hsm
    have hT : IsTriple t.sX t.I t.E := ht
    haveI : LocallyOfFiniteType (h ≫ t.sX) := hT'.2.2.1
    haveI : QuasiCompact (h ≫ t.sX) := hT'.2.2.2.1
    haveI := isNoetherian_of_isTriple hT'
    have hh := IsReducedFlatBaseChange.of_smooth h
    have hTP : IsTriple (h ≫ t.sX) (t.I.comap h) (t.E.comap h) :=
      isTriple_comap_of_smooth hT h hT'.2.2.2.2.1
    have hN : nonmonomialPart (t.I.comap h) E' = (nonmonomialPart t.I t.E).comap h :=
      (nonmonomialPart_eq hE' _).trans (nonmonomialPart_comap_of_smooth hT h hTP)
    have hle : maxOrder ((nonmonomialPart t.I t.E).comap h) ≤ maxOrder (nonmonomialPart t.I t.E) :=
      maxOrder_comap_le_of_smooth hT h _
    rw [bmoStepOneAux]
    by_cases h0 : maxOrder (nonmonomialPart t.I t.E) < m
    · rw [if_pos h0]
      obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      rw [bmoStepOneAux, if_pos (by rw [hN]; exact hle.trans_lt h0)]
      rfl
    rw [if_neg h0]
    have hNt := isTriple_nonmonomialPart hT
    have hfin : maxOrder (nonmonomialPart t.I t.E) ≠ ⊤ :=
      maxOrderAlong_nonmonomialPart_ne_top hT _
    have hμ : maxOrder (nonmonomialPart t.I t.E) =
        ((maxOrder (nonmonomialPart t.I t.E)).toNat : ℕ∞) := (ENat.coe_toNat hfin).symm
    have hmμ : m ≤ (maxOrder (nonmonomialPart t.I t.E)).toNat := by
      have := not_lt.1 h0
      rw [hμ] at this
      exact_mod_cast this
    have hne : Nonempty t.X :=
      nonempty_of_one_le_maxOrder (le_trans (by exact_mod_cast hm) (not_lt.1 h0))
    have hτ : (⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩ : FieldBlowupTriple.{u}) ∈
        idealTriplesOfDim (Set.Icc a b) (maxOrder (nonmonomialPart t.I t.E)).toNat :=
      ⟨hNt, ⟨d, hd, by rw [← hdt]; exact topologicalKrullDim_eq_dimNat hT⟩, hμ.le⟩
    have hNP := isTriple_nonmonomialPart hTP
    rw [nonmonomialPart_comap_of_smooth hT h hTP] at hNP
    have hNY := isTriple_nonmonomialPart hT'
    rw [hN] at hNY
    have hP : (⟨⟨Y, (nonmonomialPart t.I t.E).comap h, t.E.comap h⟩, t.k, h ≫ t.sX⟩ :
        FieldBlowupTriple.{u}) ∈
        idealTriplesOfDim {d'} (maxOrder (nonmonomialPart t.I t.E)).toNat :=
      ⟨hNP, ⟨d', rfl, hdY⟩, hle.trans hμ.le⟩
    have hPY : (⟨⟨Y, (nonmonomialPart t.I t.E).comap h, E'⟩, t.k, h ≫ t.sX⟩ :
        FieldBlowupTriple.{u}) ∈
        idealTriplesOfDim {d'} (maxOrder (nonmonomialPart t.I t.E)).toNat :=
      ⟨hNY, ⟨d', rfl, hdY⟩, hle.trans hμ.le⟩
    obtain ⟨F, hFB, hF1, -⟩ := hB _ (hm.trans hmμ)
    have hS := F.isOrderMTripleSeq _ hτ
    have hlast := hF1 _ hτ
    rw [hFB] at hS hlast
    change ClosedBlowupSequence.IsOrderMTripleSeq t.sX (nonmonomialPart t.I t.E) t.E _
      (B (dimNat t.X) _ ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩) at hS
    change maxOrder ((B (dimNat t.X) _ ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k,
      t.sX⟩).controlledTransform
      (nonmonomialPart t.I t.E)) < _ at hlast
    rw [hdt] at hS hlast
    set S : ClosedBlowupSequence t.X := B d (maxOrder (nonmonomialPart t.I t.E)).toNat
      ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩ with hSdef
    obtain ⟨hS1, hS2⟩ := isOrderGe_of_isOrderM hm hmμ S t.sX t.I t.E hT hS
    have he1 : t.endOf m S ∈ markedTriples := isTriple_end _ _ _ _ hS1
    have hd1 : dimNat (t.endOf m S).X = d := (dimNat_target_of_isOrderGe _ _ _ _ hS1).trans hdt
    have hq1 : (maxOrder (nonmonomialPart (t.endOf m S).I (t.endOf m S).E)).toNat < q := by
      change (maxOrder (nonmonomialPart (S.markedTransform ⟨t.I, m⟩).I
        (S.orderedTotalTransform t.E))).toNat < q
      rw [hS2]
      have := toNat_lt_of_lt hlast
      omega
    dsimp only
    rw [append_pullbackReduced]
    by_cases hν : maxOrder ((nonmonomialPart t.I t.E).comap h) < maxOrder (nonmonomialPart t.I t.E)
    · have e := round_pullbackReduced_eq_nil hB hBe (hm.trans hmμ) t.sX _ t.E h hd' hτ hP
        (hν.trans_eq hμ)
      rw [hdt, ← hSdef] at e
      rw [append_pullbackReduced_of_eq_nil _ ⟨S.pullbackReduced h, S.pullbackReducedHom h⟩ e]
      obtain ⟨hI1, hE1⟩ := transforms_of_pullbackReduced_eq_nil S t.sX ⟨t.I, m⟩ t.E hS1 h hh E'
        hE' e
      exact (bmoStepOneAux_pullbackReduced hB hBe hm hd hd' q (t.endOf m S) he1 hd1 hq1 q' _
        (smooth_eqToHom_comp_pullbackReducedHom S h e) (t.I.comap h) E' (h ≫ t.sX) m' hI1
        (comp_eq_of_pullbackReduced_eq_nil S h e _) hE1 hT' hdY hq').trans
        (congrArg (fun T => ClosedBlowupSequence.pullbackReduced T
          (eqToHom (congrArg ClosedBlowupSequence.target e.symm) ≫ S.pullbackReducedHom h))
          (ite_pos_eq _ _ he1).symm)
    · have hνeq : maxOrder ((nonmonomialPart t.I t.E).comap h) =
          maxOrder (nonmonomialPart t.I t.E) := le_antisymm hle (not_lt.1 hν)
      obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      rw [bmoStepOneAux, if_neg (by rwa [hN, hνeq])]
      dsimp only
      have hround := round_eq_pullbackReduced hB hBe (hm.trans hmμ) t.sX _ t.E h E' hE' hd' hτ
        hP hPY
      rw [hdt, ← hSdef] at hround
      have hPY' := mem_idealTriplesOfDim_Icc hd' hPY
      have hSY := F.isOrderMTripleSeq _ hPY'
      have hlastY := hF1 _ hPY'
      rw [hFB] at hSY hlastY
      change ClosedBlowupSequence.IsOrderMTripleSeq (h ≫ t.sX) ((nonmonomialPart t.I t.E).comap h)
        E' _ (B (dimNat Y) _ ⟨⟨Y, (nonmonomialPart t.I t.E).comap h, E'⟩, t.k, h ≫ t.sX⟩) at hSY
      change maxOrder ((B (dimNat Y) _ ⟨⟨Y, (nonmonomialPart t.I t.E).comap h, E'⟩, t.k,
        h ≫ t.sX⟩).controlledTransform ((nonmonomialPart t.I t.E).comap h)) < _ at hlastY
      rw [dimNat_of_mem_idealTriplesOfDim hPY, hround, ← hN] at hSY hlastY
      rw [hN, hνeq, hround]
      congr 1
      obtain ⟨hS1Y, hS2Y⟩ := isOrderGe_of_isOrderM hm hmμ (S.pullbackReduced h) (h ≫ t.sX)
        (t.I.comap h) E' hT' hSY
      have he1Y := isTriple_end _ _ _ _ hS1Y
      obtain ⟨hI1, hE1⟩ := transforms_pullbackReduced S t.sX ⟨t.I, m⟩ t.E hS1 h hh E' hE'
      have hdY1 : topologicalKrullDim (S.pullbackReduced h).target = ((d' : ℕ∞) : WithBot ℕ∞) :=
        (topologicalKrullDim_target_of_isOrderGe _ _ _ _ hS1Y).trans hdY
      have hqY : (maxOrder (nonmonomialPart ((S.pullbackReduced h).markedTransform
          ⟨t.I.comap h, m⟩).I ((S.pullbackReduced h).orderedTotalTransform E'))).toNat < q'' := by
        rw [hS2Y]
        have hq'' := hq'
        rw [hN, hνeq] at hq''
        have := toNat_lt_of_lt hlastY
        omega
      exact (ite_pos_eq _ _ he1Y).trans ((bmoStepOneAux_pullbackReduced hB hBe hm hd hd' q
        (t.endOf m S) he1 hd1 hq1 q'' (S.pullbackReducedHom h)
        (Kollar.smooth_pullbackReducedHom S h) _ _ _ m hI1 (toBase_comp_comp_eq S h _) hE1 he1Y hdY1
        hqY).trans (congrArg (fun T => ClosedBlowupSequence.pullbackReduced T
          (S.pullbackReducedHom h)) (ite_pos_eq _ _ he1).symm))

/-- **Step 2 along a smooth morphism.** As `bmoStepOneAux_pullbackReduced`, with the invariant
`s = maxord_{cosupp(I, m)} N(I)`, the ideals `K_s(I, m)` and the rounds `𝓑_{·, ms}`. -/
private theorem bmoStepTwoAux_pullbackReduced {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B)
    (hBe : ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t))
    {m : ℕ} (hm : 1 ≤ m) {d d' : ℕ} (hd : d ∈ Set.Icc a b) (hd' : d' ∈ Set.Icc a b) :
    ∀ (q : ℕ) (t : MarkedTriple.{u}), t ∈ markedTriples → dimNat t.X = d →
      bmoStepTwoOrder m t < q →
      ∀ (q' : ℕ) {Y : Scheme.{u}} (h : Y ⟶ t.X), Smooth h → ∀ (I' : Y.IdealSheafData)
        (E' : OrderedDivisor Y) (s' : Y ⟶ Spec (.of t.k)) (m' : ℕ),
        I' = t.I.comap h → s' = h ≫ t.sX → flat E' = flat (t.E.comap h) → IsTriple s' I' E' →
        topologicalKrullDim Y = ((d' : ℕ∞) : WithBot ℕ∞) →
        bmoStepTwoOrder m ⟨⟨⟨Y, I', E'⟩, t.k, s'⟩, m'⟩ < q' →
        bmoStepTwoAux B d' m q' ⟨⟨⟨Y, I', E'⟩, t.k, s'⟩, m'⟩ =
          (bmoStepTwoAux B d m q t).pullbackReduced h
  | 0, _, _, _, hq, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => absurd hq (Nat.not_lt_zero _)
  | q + 1, t, ht, hdt, hq, q', Y, h, hsm, I', E', s', m', hI', hs', hE', hT', hdY, hq' => by
    subst hI' hs'
    haveI := hsm
    have hT : IsTriple t.sX t.I t.E := ht
    haveI : LocallyOfFiniteType (h ≫ t.sX) := hT'.2.2.1
    haveI : QuasiCompact (h ≫ t.sX) := hT'.2.2.2.1
    haveI := isNoetherian_of_isTriple hT'
    have hh := IsReducedFlatBaseChange.of_smooth h
    have hTP : IsTriple (h ≫ t.sX) (t.I.comap h) (t.E.comap h) :=
      isTriple_comap_of_smooth hT h hT'.2.2.2.2.1
    have hN : nonmonomialPart (t.I.comap h) E' = (nonmonomialPart t.I t.E).comap h :=
      (nonmonomialPart_eq hE' _).trans (nonmonomialPart_comap_of_smooth hT h hTP)
    have hsY : maxOrderAlong (nonmonomialPart (t.I.comap h) E')
        (⟨t.I.comap h, m⟩ : MarkedIdeal Y).cosupport ≤
        maxOrderAlong (nonmonomialPart t.I t.E) (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport := by
      rw [hN, cosupport_comap_of_smooth hT h t.I m]
      exact maxOrderAlong_comap_le_of_smooth hT h _ _
    have hσ : maxOrderAlong (nonmonomialPart t.I t.E) (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport =
        (bmoStepTwoOrder m t : ℕ∞) :=
      (ENat.coe_toNat (maxOrderAlong_nonmonomialPart_ne_top hT _)).symm
    have hσY : maxOrderAlong (nonmonomialPart (t.I.comap h) E')
        (⟨t.I.comap h, m⟩ : MarkedIdeal Y).cosupport =
        (bmoStepTwoOrder m ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m'⟩ : ℕ∞) :=
      (ENat.coe_toNat (maxOrderAlong_nonmonomialPart_ne_top hT' _)).symm
    have hsle : bmoStepTwoOrder m ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m'⟩ ≤
        bmoStepTwoOrder m t := by
      have := hsY
      rw [hσ, hσY] at this
      exact_mod_cast this
    rw [bmoStepTwoAux]
    by_cases h0 : bmoStepTwoOrder m t = 0
    · rw [if_pos h0]
      obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      rw [bmoStepTwoAux, if_pos (by omega)]
      rfl
    rw [if_neg h0]
    have hσ1 : 1 ≤ bmoStepTwoOrder m t := Nat.one_le_iff_ne_zero.2 h0
    haveI : Nonempty t.X := by
      by_contra hX
      rw [not_nonempty_iff] at hX
      have : maxOrderAlong (nonmonomialPart t.I t.E) (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport =
        0 := by simp [maxOrderAlong]
      rw [hσ, Nat.cast_eq_zero] at this
      exact h0 this
    have hK := maxOrder_mixedIdeal_le t.sX t.I t.E m _ hT hm hσ hσ1
    have hmσ : 1 ≤ m * bmoStepTwoOrder m t := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hdimX : topologicalKrullDim t.X = ((d : ℕ∞) : WithBot ℕ∞) := by
      rw [← hdt]; exact topologicalKrullDim_eq_dimNat hT
    have hτ : (⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩ :
        FieldBlowupTriple.{u}) ∈ idealTriplesOfDim (Set.Icc a b) (m * bmoStepTwoOrder m t) :=
      ⟨isTriple_mixedIdeal hT m _, ⟨d, hd, hdimX⟩, hK⟩
    have hMI : mixedIdeal (t.I.comap h) E' m (bmoStepTwoOrder m t) =
        (mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h :=
      (mixedIdeal_eq hE' _ m _).trans (mixedIdeal_comap_of_smooth hT h hTP m _)
    have hleK : maxOrder ((mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h) ≤
        maxOrder (mixedIdeal t.I t.E m (bmoStepTwoOrder m t)) :=
      maxOrder_comap_le_of_smooth hT h _
    have hKP := isTriple_mixedIdeal hTP m (bmoStepTwoOrder m t)
    rw [mixedIdeal_comap_of_smooth hT h hTP] at hKP
    have hKY := isTriple_mixedIdeal hT' m (bmoStepTwoOrder m t)
    rw [hMI] at hKY
    have hP : (⟨⟨Y, (mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h, t.E.comap h⟩, t.k,
        h ≫ t.sX⟩ : FieldBlowupTriple.{u}) ∈ idealTriplesOfDim {d'} (m * bmoStepTwoOrder m t) :=
      ⟨hKP, ⟨d', rfl, hdY⟩, hleK.trans hK⟩
    have hPY : (⟨⟨Y, (mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h, E'⟩, t.k,
        h ≫ t.sX⟩ : FieldBlowupTriple.{u}) ∈ idealTriplesOfDim {d'} (m * bmoStepTwoOrder m t) :=
      ⟨hKY, ⟨d', rfl, hdY⟩, hleK.trans hK⟩
    obtain ⟨F, hFB, -, -⟩ := hB _ hmσ
    have hS := F.isOrderMTripleSeq _ hτ
    rw [hFB] at hS
    change ClosedBlowupSequence.IsOrderMTripleSeq t.sX (mixedIdeal t.I t.E m (bmoStepTwoOrder m t))
      t.E _ (B (dimNat t.X) _
        ⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩) at hS
    rw [hdt] at hS
    set S : ClosedBlowupSequence t.X := B d (m * bmoStepTwoOrder m t)
      ⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩ with hSdef
    obtain ⟨i, hi⟩ := exists_truncate_eq S
    have hS1 := (isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal
      t.sX t.I t.E m _ hT hm hσ1 hK _ hS i).1
    rw [hi] at hS1
    have he1 : t.endOf m S ∈ markedTriples := isTriple_end _ _ _ _ hS1
    have hd1 : dimNat (t.endOf m S).X = d := (dimNat_target_of_isOrderGe _ _ _ _ hS1).trans hdt
    have hq1 : bmoStepTwoOrder m (t.endOf m S) < q := by
      have hdec := maxOrderAlong_nonmonomialPart_endOf_mixedIdeal_lt B hB
        ⟨t.toFieldBlowupTriple, m⟩ ht hdimX hd.1 hd.2 hm hσ hσ1
      have := toNat_lt_of_lt hdec
      change bmoStepTwoOrder m (t.endOf m S) < _ at this
      omega
    dsimp only
    rw [append_pullbackReduced]
    by_cases hν : bmoStepTwoOrder m ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m'⟩ <
      bmoStepTwoOrder m t
    · have hlt : maxOrder ((mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h) <
          ((m * bmoStepTwoOrder m t : ℕ) : ℕ∞) := by
        rw [← mixedIdeal_comap_of_smooth hT h hTP]
        refine maxOrder_mixedIdeal_lt _ _ _ m _ hTP hm hσ1 ?_
        rw [← nonmonomialPart_eq hE', hσY]
        exact_mod_cast hν
      have e := round_pullbackReduced_eq_nil hB hBe hmσ t.sX _ t.E h hd' hτ hP hlt
      rw [hdt, ← hSdef] at e
      rw [append_pullbackReduced_of_eq_nil _ ⟨S.pullbackReduced h, S.pullbackReducedHom h⟩ e]
      obtain ⟨hI1, hE1⟩ := transforms_of_pullbackReduced_eq_nil S t.sX ⟨t.I, m⟩ t.E hS1 h hh E'
        hE' e
      exact (bmoStepTwoAux_pullbackReduced hB hBe hm hd hd' q (t.endOf m S) he1 hd1 hq1 q' _
        (smooth_eqToHom_comp_pullbackReducedHom S h e) (t.I.comap h) E' (h ≫ t.sX) m' hI1
        (comp_eq_of_pullbackReduced_eq_nil S h e _) hE1 hT' hdY hq').trans
        (congrArg (fun T => ClosedBlowupSequence.pullbackReduced T
          (eqToHom (congrArg ClosedBlowupSequence.target e.symm) ≫ S.pullbackReducedHom h))
          (ite_pos_eq _ _ he1).symm)
    · have hνeq : bmoStepTwoOrder m ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m'⟩ =
          bmoStepTwoOrder m t := le_antisymm hsle (not_lt.1 hν)
      have hσY' : maxOrderAlong (nonmonomialPart (t.I.comap h) E')
          (⟨t.I.comap h, m⟩ : MarkedIdeal Y).cosupport = (bmoStepTwoOrder m t : ℕ∞) := by
        rw [hσY, hνeq]
      obtain ⟨q'', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      rw [bmoStepTwoAux, if_neg (by rwa [hνeq])]
      dsimp only
      have hround := round_eq_pullbackReduced hB hBe hmσ t.sX _ t.E h E' hE' hd' hτ hP hPY
      rw [hdt, ← hSdef] at hround
      have hPY' := mem_idealTriplesOfDim_Icc hd' hPY
      have hSY := F.isOrderMTripleSeq _ hPY'
      rw [hFB] at hSY
      change ClosedBlowupSequence.IsOrderMTripleSeq (h ≫ t.sX)
        ((mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h) E' _
        (B (dimNat Y) _ ⟨⟨Y, (mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h, E'⟩, t.k,
          h ≫ t.sX⟩) at hSY
      rw [dimNat_of_mem_idealTriplesOfDim hPY, hround, ← hMI] at hSY
      have hK' : maxOrder (mixedIdeal (t.I.comap h) E' m (bmoStepTwoOrder m t)) ≤
          ((m * bmoStepTwoOrder m t : ℕ) : ℕ∞) := by
        rw [hMI]; exact hleK.trans hK
      obtain ⟨i', hi'⟩ := exists_truncate_eq (S.pullbackReduced h)
      have hS1Y := (isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal
        (h ≫ t.sX) (t.I.comap h) E' m _ hT' hm hσ1 hK' _ hSY i').1
      rw [hi'] at hS1Y
      have he1Y := isTriple_end _ _ _ _ hS1Y
      have hqY : bmoStepTwoOrder m (MarkedTriple.endOf ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m'⟩
          m (S.pullbackReduced h)) < q'' := by
        have hdY' : topologicalKrullDim Y = ((d' : ℕ∞) : WithBot ℕ∞) := hdY
        have hdec := maxOrderAlong_nonmonomialPart_endOf_mixedIdeal_lt B hB
          ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m⟩ hT' hdY' hd'.1 hd'.2 hm hσY' hσ1
        dsimp only at hdec
        rw [hMI, hround] at hdec
        have := toNat_lt_of_lt hdec
        change bmoStepTwoOrder m (MarkedTriple.endOf ⟨⟨⟨Y, t.I.comap h, E'⟩, t.k, h ≫ t.sX⟩, m'⟩
          m (S.pullbackReduced h)) < _ at this
        rw [hνeq] at hq'
        omega
      rw [hνeq, hMI, hround]
      congr 1
      obtain ⟨hI1, hE1⟩ := transforms_pullbackReduced S t.sX ⟨t.I, m⟩ t.E hS1 h hh E' hE'
      have hdY1 : topologicalKrullDim (S.pullbackReduced h).target = ((d' : ℕ∞) : WithBot ℕ∞) :=
        (topologicalKrullDim_target_of_isOrderGe _ _ _ _ hS1Y).trans hdY
      exact (ite_pos_eq _ _ he1Y).trans ((bmoStepTwoAux_pullbackReduced hB hBe hm hd hd' q
        (t.endOf m S) he1 hd1 hq1 q'' (S.pullbackReducedHom h)
        (Kollar.smooth_pullbackReducedHom S h) _ _ _ m hI1 (toBase_comp_comp_eq S h _) hE1 he1Y hdY1
        hqY).trans (congrArg (fun T => ClosedBlowupSequence.pullbackReduced T
          (S.pullbackReducedHom h)) (ite_pos_eq _ _ he1).symm))

end Steps

/-! ### The functor `𝓑𝓜𝓞` along a smooth morphism -/

section Main

open ClosedBlowupSequence

/-- The dimension of a scheme in `markedTriplesOfDim N m` lies in `N`. -/
private theorem dimNat_mem_of_mem_markedTriplesOfDim {N : Set ℕ} {m : ℕ} {t : MarkedTriple.{u}}
    (ht : t ∈ markedTriplesOfDim N m) : dimNat t.X ∈ N := by
  obtain ⟨-, -, n, hn, h⟩ := ht
  rwa [dimNat_eq_of_topologicalKrullDim h]

/-- A scheme in `markedTriplesOfDim N m` has Krull dimension `dimNat`. -/
private theorem topologicalKrullDim_of_mem_markedTriplesOfDim {N : Set ℕ} {m : ℕ}
    {t : MarkedTriple.{u}} (ht : t ∈ markedTriplesOfDim N m) :
    topologicalKrullDim t.X = ((dimNat t.X : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨-, -, n, -, h⟩ := ht
  rw [dimNat_eq_of_topologicalKrullDim h, h]

/-- Step 3 of `𝓑𝓜𝓞` for a marked triple `(X, I, m, E)`: the extension by closure of the
monomial order reduction of the monomial data on `U = X ∖ cosupp N(I)`. -/
private noncomputable abbrev stepThree (m : ℕ) (u : MarkedTriple.{u}) : ClosedBlowupSequence u.X :=
  let U : u.X.Opens := (nonmonomialPart u.I u.E).support.compl
  ((restrictData u U).monomialOrderReduction m).extendByClosure U.ι

/-- `𝓑𝓜𝓞` as the reduction of the concatenation of its three steps, when the input and the end
of Step 1 are marked triples. -/
private theorem bmoFunctor_eq_of_mem (B : UnmarkedFamily.{u}) (d m : ℕ) (u : MarkedTriple.{u})
    (hu : u ∈ markedTriples) (hu1 : u.endOf m (bmoStepOne B d m u) ∈ markedTriples) :
    bmoFunctor B d m u = ((bmoStepOne B d m u).append
      ((bmoStepTwo B d m (u.endOf m (bmoStepOne B d m u))).append
        (stepThree m ((u.endOf m (bmoStepOne B d m u)).endOf m
          (bmoStepTwo B d m (u.endOf m (bmoStepOne B d m u))))))).reduction := by
  unfold bmoFunctor
  dsimp only
  rw [if_pos hu, if_pos hu1]
  rfl

/-- Three reduced pull-backs, concatenated, are the reduced pull-back of the concatenation. -/
private theorem reduction_append_append_eq {X Y : Scheme.{u}} (h : Y ⟶ X)
    (S₁ : ClosedBlowupSequence X) (S₂ : ClosedBlowupSequence S₁.target)
    (S₃ : ClosedBlowupSequence S₂.target) (A₁ : ClosedBlowupSequence Y)
    (A₂ : ClosedBlowupSequence A₁.target) (A₃ : ClosedBlowupSequence A₂.target)
    (e₁ : A₁ = S₁.pullbackReduced h)
    (e₂ : A₂ ≍ S₂.pullbackReduced (S₁.pullbackReducedHom h))
    (e₃ : A₃ ≍ S₃.pullbackReduced (S₂.pullbackReducedHom (S₁.pullbackReducedHom h))) :
    (A₁.append (A₂.append A₃)).reduction =
      ((S₁.append (S₂.append S₃)).reduction.pullback h).reduction := by
  subst e₁
  obtain rfl := eq_of_heq e₂
  obtain rfl := eq_of_heq e₃
  rw [reduction_pullback, pullbackReduced_reduction, append_pullbackReduced,
    append_pullbackReduced]
  exact reduction_eq_self (hasNoEmptyBlowups_append _ _ (hasNoEmptyBlowups_pullbackReduced _ _)
    (hasNoEmptyBlowups_append _ _ (hasNoEmptyBlowups_pullbackReduced _ _)
      (hasNoEmptyBlowups_pullbackReduced _ _)))

/-- **Kollár 3.107 (2), the general case.** For a smooth `h : Y → X` between members of the class,
`𝓑𝓜𝓞(Y, h^*I, m, h⁻¹E) = (h^*𝓑𝓜𝓞(X, I, m, E))^red`. Steps 1 and 2 on `Y` are the reduced
pull-backs of those on `X`, along the last morphisms of the reduced pull-backs, and Step 3 is the
reduced pull-back by `extendByClosure_monomialOrderReduction_pullbackReduced`. -/
private theorem bmoFunctor_pullback_eq_reduction {a b m : ℕ} (B : UnmarkedFamily.{u})
    (hB : IsOrderReductionFamily a b B)
    (hBe : ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t))
    (hm : 1 ≤ m) (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfDim (Set.Icc a b) m)
    {Y : Scheme.{u}} (h : Y ⟶ t.X) [Smooth h]
    (hY : t.pullback h ∈ markedTriplesOfDim (Set.Icc a b) m) :
    bmoFunctor B (dimNat (t.pullback h).X) m (t.pullback h) =
      ((bmoFunctor B (dimNat t.X) m t).pullback h).reduction := by
  have hd := dimNat_mem_of_mem_markedTriplesOfDim ht
  have hd' := dimNat_mem_of_mem_markedTriplesOfDim hY
  have hdY := topologicalKrullDim_of_mem_markedTriplesOfDim hY
  have htm : t ∈ markedTriples := ht.1
  have hYm : t.pullback h ∈ markedTriples := hY.1
  have hT' : IsTriple (h ≫ t.sX) (t.I.comap h) (t.E.comap h) := hYm
  haveI := isNoetherian_of_isTriple hT'
  have hh := IsReducedFlatBaseChange.of_smooth h
  set tY : MarkedTriple.{u} := ⟨⟨⟨Y, t.I.comap h, t.E.comap h⟩, t.k, h ≫ t.sX⟩, t.m⟩ with htYdef
  change bmoFunctor B (dimNat Y) m tY = _
  -- Step 1
  set S₁ := bmoStepOne B (dimNat t.X) m t with hS₁def
  have hS1 : bmoStepOne B (dimNat Y) m tY = S₁.pullbackReduced h :=
    bmoStepOneAux_pullbackReduced hB hBe hm hd hd' _ t htm rfl (Nat.lt_succ_self _) _ h
      inferInstance (t.I.comap h) (t.E.comap h) (h ≫ t.sX) t.m rfl rfl rfl hT' hdY
      (Nat.lt_succ_self _)
  have hG1 := (isOrderGeMarkedTripleSeq_bmoStepOne hB hm htm hd).1
  have hG1' := (isOrderGeMarkedTripleSeq_bmoStepOne hB hm hYm hd').1
  change ClosedBlowupSequence.IsOrderGeMarkedTripleSeq (h ≫ t.sX) ⟨t.I.comap h, m⟩ (t.E.comap h)
    (bmoStepOne B (dimNat Y) m tY) at hG1'
  rw [hS1] at hG1'
  have he1 : t.endOf m S₁ ∈ markedTriples := isTriple_end _ _ _ _ hG1
  have he1' : tY.endOf m (S₁.pullbackReduced h) ∈ markedTriples := isTriple_end _ _ _ _ hG1'
  have hd1 : dimNat (t.endOf m S₁).X = dimNat t.X := dimNat_target_of_isOrderGe S₁ _ _ _ hG1
  have hd1' : dimNat (tY.endOf m (S₁.pullbackReduced h)).X = dimNat Y :=
    dimNat_target_of_isOrderGe _ _ _ _ hG1'
  have hdY1 : topologicalKrullDim (tY.endOf m (S₁.pullbackReduced h)).X =
      ((dimNat Y : ℕ∞) : WithBot ℕ∞) :=
    (topologicalKrullDim_target_of_isOrderGe _ _ _ _ hG1').trans hdY
  obtain ⟨hI1, hE1⟩ := transforms_pullbackReduced S₁ t.sX ⟨t.I, m⟩ t.E hG1 h hh (t.E.comap h) rfl
  have hs1 := toBase_comp_comp_eq S₁ h t.sX
  -- Step 2
  haveI : Smooth (S₁.pullbackReducedHom h) := Kollar.smooth_pullbackReducedHom S₁ h
  set S₂ : ClosedBlowupSequence S₁.target := bmoStepTwo B (dimNat t.X) m (t.endOf m S₁)
    with hS₂def
  have hS2 : bmoStepTwo B (dimNat Y) m (tY.endOf m (S₁.pullbackReduced h)) =
      S₂.pullbackReduced (S₁.pullbackReducedHom h) :=
    bmoStepTwoAux_pullbackReduced hB hBe hm hd hd' _ (t.endOf m S₁) he1 hd1 (Nat.lt_succ_self _)
      _ (S₁.pullbackReducedHom h) (Kollar.smooth_pullbackReducedHom S₁ h) _ _ _ m hI1 hs1 hE1
      he1' hdY1 (Nat.lt_succ_self _)
  have hG2 := (isOrderGeMarkedTripleSeq_bmoStepTwo hB hm he1 (hd1 ▸ hd)).1
  rw [hd1] at hG2
  have hG2' := (isOrderGeMarkedTripleSeq_bmoStepTwo hB hm he1' (hd1' ▸ hd')).1
  rw [hd1', hS2] at hG2'
  have he2 : (t.endOf m S₁).endOf m S₂ ∈ markedTriples := isTriple_end _ _ _ _ hG2
  have he2' : (tY.endOf m (S₁.pullbackReduced h)).endOf m
      (S₂.pullbackReduced (S₁.pullbackReducedHom h)) ∈ markedTriples :=
    isTriple_end _ _ _ _ hG2'
  have hh1 := IsReducedFlatBaseChange.of_smooth (S₁.pullbackReducedHom h)
  haveI : AlgebraicGeometry.IsNoetherian (S₁.pullbackReduced h).target :=
    isNoetherian_of_isTriple (show IsTriple _ _ _ from he1')
  obtain ⟨hI2, hE2⟩ := transforms_pullbackReduced S₂ (t.endOf m S₁).sX ⟨(t.endOf m S₁).I, m⟩
    (t.endOf m S₁).E hG2 (S₁.pullbackReducedHom h) hh1 _ hE1
  have hI2' : ((S₂.pullbackReduced (S₁.pullbackReducedHom h)).markedTransform
      ⟨((S₁.pullbackReduced h).markedTransform ⟨t.I.comap h, m⟩).I, m⟩).I =
      ((t.endOf m S₁).endOf m S₂).I.comap
        (S₂.pullbackReducedHom (S₁.pullbackReducedHom h)) := by
    have e : (⟨((S₁.pullbackReduced h).markedTransform ⟨t.I.comap h, m⟩).I, m⟩ :
        MarkedIdeal (S₁.pullbackReduced h).target) =
        ⟨(t.endOf m S₁).I.comap (S₁.pullbackReducedHom h), m⟩ := by
      rw [hI1]
      rfl
    rw [e]
    exact hI2
  -- Step 3
  set X₂ : MarkedTriple.{u} := (t.endOf m S₁).endOf m S₂ with hX₂def
  set Y₂ : Scheme.{u} := (S₂.pullbackReduced (S₁.pullbackReducedHom h)).target with hY₂def
  set E₂ : OrderedDivisor Y₂ := (S₂.pullbackReduced (S₁.pullbackReducedHom h)).orderedTotalTransform
    ((S₁.pullbackReduced h).orderedTotalTransform (t.E.comap h)) with hE₂def
  set g : Y₂ ⟶ X₂.X := S₂.pullbackReducedHom (S₁.pullbackReducedHom h) with hgdef
  have hsmg : Smooth g := Kollar.smooth_pullbackReducedHom S₂ _
  have hE2g : flat E₂ = flat (X₂.E.comap g) := hE2
  have hI2g : ((S₂.pullbackReduced (S₁.pullbackReducedHom h)).markedTransform
      ⟨((S₁.pullbackReduced h).markedTransform ⟨t.I.comap h, m⟩).I, m⟩).I = X₂.I.comap g := hI2'
  have hT₂ : IsTriple X₂.sX X₂.I X₂.E := he2
  have hs2 : (S₂.pullbackReduced (S₁.pullbackReducedHom h)).toBase ≫
      (S₁.pullbackReduced h).toBase ≫ h ≫ t.sX = g ≫ X₂.sX := by
    rw [hs1, ← Category.assoc, pullbackReducedHom_toBase_comm, Category.assoc]
    rfl
  have hY2 : (tY.endOf m (S₁.pullbackReduced h)).endOf m
      (S₂.pullbackReduced (S₁.pullbackReducedHom h)) =
      ⟨⟨⟨Y₂, X₂.I.comap g, E₂⟩, t.k, g ≫ X₂.sX⟩, m⟩ :=
    markedTriple_mk_congr hI2g rfl hs2
  have hT₂' : IsTriple (g ≫ X₂.sX) (X₂.I.comap g) E₂ := by
    have := he2'
    rw [hY2] at this
    exact this
  haveI := hsmg
  haveI : QuasiCompact (g ≫ X₂.sX) := hT₂'.2.2.2.1
  have hTP₂ := isTriple_comap_of_smooth hT₂ g hT₂'.2.2.2.2.1
  have hV : (nonmonomialPart (X₂.I.comap g) E₂).support.compl =
      g ⁻¹ᵁ (nonmonomialPart X₂.I X₂.E).support.compl := by
    rw [nonmonomialPart_eq hE2g, nonmonomialPart_comap_of_smooth hT₂ g hTP₂]
    ext x
    exact not_congr (mem_support_comap_iff _ _ x)
  have h3 := extendByClosure_monomialOrderReduction_pullbackReduced X₂ he2 g E₂ hE2g m hT₂' m _ _
    hV
  -- assembly
  have hu1 : tY.endOf m (bmoStepOne B (dimNat Y) m tY) ∈ markedTriples := by
    rwa [hS1]
  rw [bmoFunctor_eq_of_mem B (dimNat Y) m tY hYm hu1, bmoFunctor_eq_of_mem B (dimNat t.X) m t htm
    he1]
  refine reduction_append_append_eq h S₁ S₂ (stepThree m X₂) _ _ _ hS1
    ?_ ?_
  · rw [hS1]
    exact heq_of_eq hS2
  · rw [hS1, hS2]
    exact (congr_arg_heq (stepThree m) hY2).trans (heq_of_eq h3)

end Main

/-- **Kollár, Thm. 3.107 (2), smooth morphisms.** Let `𝓑` be an order-reduction family on
dimensions `a, …, b` (`IsOrderReductionFamily`), each `𝓑_{d,μ}` ignoring empty entries
(`IgnoresEmptyEntries`), and `m ≥ 1`. On the class of marked triples
`(X, I, m, E)` with `a ≤ dim X ≤ b`, the functor
`(X, I, m, E) ↦ bmoFunctor B (dim X) m (X, I, m, E)` commutes with smooth morphisms
(`CommutesWithSmoothOnMarked`). -/
@[mmp "thm_kr3e_order_reduction_marked_commutes_smooth"]
theorem commutesWithSmoothOnMarked_bmoFunctor {a b m : ℕ} (B : UnmarkedFamily.{u})
    (hB : IsOrderReductionFamily a b B)
    (hBe : ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t))
    (hm : 1 ≤ m) :
    CommutesWithSmoothOnMarked (markedTriplesOfDim (Set.Icc a b) m)
      (fun t _ => bmoFunctor B (dimNat t.X) m t) :=
  ⟨fun t ht _ h _ _ _ _ hY => (bmoFunctor_pullback_eq_reduction B hB hBe hm t ht h hY).trans
      (ClosedBlowupSequence.reduction_eq_self (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
        (ClosedBlowupSequence.hasNoEmptyBlowups_reduction _) h)),
    fun t ht _ h _ _ _ hY => bmoFunctor_pullback_eq_reduction B hB hBe hm t ht h hY⟩

end MMP.Resolution
