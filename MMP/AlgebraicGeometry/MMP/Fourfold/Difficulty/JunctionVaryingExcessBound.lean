module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.ThreefoldBranchInequality
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.EchoSetting
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.WeightSupportFinite
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison

/-!
# The varying branch excess at a junction of a prepared chain

Let `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, be a junction of a prepared chain, with labels
`S_h`, and let `Q ⊆ Y_i` be the varying union, the union of the varying labels on `Y_i`. The
excess `∑_{C ⊆ Q} (r_C^var - 1)` of the varying branch numbers over the irreducible closed
curves `C ⊆ Q` is paid by positive terms of the difficulty:
`∑_{C ⊆ Q} (r_C^var - 1) ≤ ∑_{h varying} d_h ρ^□(S_h^ν) + ∑_v w_v(Y_i, Θ_i)`,
the last sum over the normalized divisorial valuations `v` exceptional over `Y_i` whose centre
on `Y_i` is a closed point.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.varyingBranchExcess_le`: the inequality, together
  with the finiteness of the support of its left side.

## Implementation notes

* As in `MMP.Fourfold.StabilizedTail.PreparedChain.IsDifficulty`, varying branch numbers,
  defaults, boxed ranks and weights are predicates on their values, so the statement takes
  functions `r`, `d`, `ρ`, `w` satisfying them on the terms that are summed. The irreducible
  closed curves of `Y_i` are the proper curves `MMP.Mori.ProperCurve`, recorded by their generic
  points; such a curve lies in `Q` when its closure does.
* The sums are finitely supported sums `∑ᶠ`. That the left side has finite support is part of
  the conclusion, so that the convention `∑ᶠ = 0` on an infinite support cannot make the
  inequality vacuous.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold MMP.Fourfold.StabilizedTail
  MMP.Mori

namespace Proof_lem_mmp_indexb_varying_excess_bound

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Centres of labels at a junction are unique -/

/-- Restriction of valuations along a surjective ring map is injective. -/
private theorem comap_injective_of_surjective {A B Γ : Type*} [CommRing A] [CommRing B]
    [LinearOrderedCommMonoidWithZero Γ] {φ : A →+* B} (hφ : Function.Surjective φ) :
    Function.Injective (fun v : Valuation B Γ => v.comap φ) := by
  intro v v' h
  ext b
  obtain ⟨a, rfl⟩ := hφ b
  exact congrArg (fun u : Valuation A Γ => u a) h

/-- An element `x` with `v x < 1` lies in the maximal ideal of the valuation subring of `v`. -/
private theorem mem_nonunits_valuationSubring {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {x : K} (h : v x < 1) :
    x ∈ v.valuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff]
  have := Valuation.isEquiv_valuation_valuationSubring v 1 x
  simp only [map_one] at this
  exact lt_of_not_ge fun h' => (not_le.2 h) (this.2 h')

/-- On a normal integral scheme separated over a field, a prime divisor is determined by its
divisorial valuation. -/
private theorem divisorialValuation_injective {k : Type} [Field k] {Y : Scheme.{0}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] :
    Function.Injective (fun P : MMP.Mori.PrimeDivisor Y => P.divisorialValuation) := by
  intro P P' h
  simp only at h
  apply AlgebraicGeometry.PrimeDivisor.genericPoint_injective
  refine MMP.Flips.eq_of_isLocal_le_valuationSubring sY P.divisorialValuation.valuationSubring
    ?_ ?_ ?_ ?_
  · intro a
    exact (P.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩
  · intro a ha
    exact mem_nonunits_valuationSubring _ ((P.divisorialValuation_algebraMap_lt_one_iff a).2 ha)
  · intro a
    rw [Valuation.mem_valuationSubring_iff, h]
    exact (P'.divisorialValuation_le_one_iff _).2 ⟨a, rfl⟩
  · intro a ha
    rw [h]
    exact mem_nonunits_valuationSubring _ ((P'.divisorialValuation_algebraMap_lt_one_iff a).2 ha)

/-- Through a birational morphism `f : Y ⟶ X`, a prime divisor of `Y` is determined by its
valuation regarded as a valuation of `k(X)`. -/
private theorem valuationOver_injective {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y] [IsNormal Y] (sY : Y ⟶ Spec (.of k))
    [IsSeparated sY] {f : Y ⟶ X} (hf : IsBirationalMorphism f) [IsDominant f] :
    Function.Injective (fun P : MMP.Mori.PrimeDivisor Y => P.valuationOver f) :=
  fun _ _ h => divisorialValuation_injective sY
    (comap_injective_of_surjective hf.functionFieldMap_bijective.2 h)

/-- The transport of a valuation of `k(X_i)` to `k(X_{i+1})` is unique. -/
private theorem isTransportedValuation_right_unique {T : StabilizedTail} {i : ℕ}
    {u : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))}
    (h : T.IsTransportedValuation i u w) (h' : T.IsTransportedValuation i u w') : w = w' := by
  have hd := T.isThreefoldStepDiagram i
  haveI : IsIntegral (T.Z i) := hd.isNormalVariety_target.1.toIsIntegral
  haveI := hd.isBirationalMorphism_minus.isDominant
  haveI := hd.isSmallMorphism_plus.isBirationalMorphism.isDominant
  have h1 : w.comap (functionFieldMap (T.fp i)) = u.comap (functionFieldMap (T.f i)) := h
  have h2 : w'.comap (functionFieldMap (T.fp i)) = u.comap (functionFieldMap (T.f i)) := h'
  exact comap_injective_of_surjective
    hd.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2 (h1.trans h2.symm)

/-- The transport of a valuation of `k(X_0)` to `k(X_i)` is unique. -/
private theorem isTransportedValuationFrom_right_unique {T : StabilizedTail} : ∀ (i : ℕ)
    {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
    {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
    T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨_, hu, huw⟩, ⟨_, hu', huw'⟩ => by
    obtain rfl := isTransportedValuationFrom_right_unique i hu hu'
    exact isTransportedValuation_right_unique huw huw'

/-- The centre of a label on a junction of a terminal chain is unique. -/
private theorem isLabelCentre_junction_unique {T : StabilizedTail} (C : TerminalChain T)
    {i : ℕ} {S : C.Label} {P P' : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)}
    (h : C.IsLabelCentre S ⟨i, none⟩ P) (h' : C.IsLabelCentre S ⟨i, none⟩ P') : P = P' := by
  haveI := (C.junction i).isBirationalMorphism.isDominant
  have hproj : AlgebraicGeometry.IsProjectiveVariety ℂ ((C.junction i).p ≫ T.sX i) :=
    (C.junction i).isProjectiveVariety
  haveI : IsSeparated ((C.junction i).p ≫ T.sX i) := hproj.toIsVariety.toIsSeparated
  obtain ⟨w, hw, hP⟩ := h
  obtain ⟨w', hw', hP'⟩ := h'
  obtain rfl := isTransportedValuationFrom_right_unique i hw hw'
  exact valuationOver_injective (f := (C.junction i).p) ((C.junction i).p ≫ T.sX i)
    (C.junction i).isBirationalMorphism (hP.trans hP'.symm)

/-! ### Finitely supported sums of natural numbers -/

/-- A finitely supported sum of natural numbers over a subset is at most the sum over the whole
set, when the latter has finite support. -/
private theorem finsum_mem_le_finsum_mem_of_subset {α : Type*} {f : α → ℕ} {s t : Set α}
    (hst : s ⊆ t) (ht : (t ∩ Function.support f).Finite) :
    ∑ᶠ a ∈ s, f a ≤ ∑ᶠ a ∈ t, f a :=
  (finsum_mem_add_sdiff' hst ht).symm ▸ Nat.le_add_right _ _

/-- Transport of a finitely supported sum along an injective map. -/
private theorem finsum_mem_comp_le {α β : Type*} {g : β → ℕ} {e : α → β} (he : Function.Injective e)
    {s : Set α} {t : Set β} (hst : Set.MapsTo e s t) (ht : (t ∩ Function.support g).Finite) :
    ∑ᶠ a ∈ s, g (e a) ≤ ∑ᶠ b ∈ t, g b := by
  rw [← finsum_mem_image he.injOn]
  exact finsum_mem_le_finsum_mem_of_subset hst.image_subset ht

/-- The cast to `ℤ` of a finitely supported sum of natural numbers with finite support. -/
private theorem natCast_finsum_mem {α : Type*} {f : α → ℕ} {s : Set α}
    (hs : (s ∩ Function.support f).Finite) :
    ((∑ᶠ a ∈ s, f a : ℕ) : ℤ) = ∑ᶠ a ∈ s, (f a : ℤ) := by
  rw [finsum_mem_eq_sum_of_subset f (t := hs.toFinset) (fun a ha => hs.mem_toFinset.2 ha)
      (fun a ha => (hs.mem_toFinset.1 ha).1),
    finsum_mem_eq_sum_of_subset (fun a => (f a : ℤ)) (t := hs.toFinset) ?_
      (fun a ha => (hs.mem_toFinset.1 ha).1)]
  · push_cast; rfl
  · rintro a ⟨ha, hfa⟩
    exact hs.mem_toFinset.2 ⟨ha, fun h => hfa (by simp [h])⟩

/-- If `s` is carried injectively into `t` by `e`, with `r = g ∘ e` on `s` and `g ≥ 1` on `t`, and
only finitely many `b ∈ t` have `g b > 1`, then the integer excesses `r a - 1` over `s` have finite
support and sum to at most the natural excesses `g b - 1` over `t`. -/
private theorem finsum_mem_intCast_sub_one_le {α β : Type*} {r : α → ℕ} {g : β → ℕ} {e : α → β}
    (he : Function.Injective e) {s : Set α} {t : Set β} (hst : Set.MapsTo e s t)
    (hr : ∀ a ∈ s, r a = g (e a)) (hg : ∀ b ∈ t, 1 ≤ g b) (ht : {b | b ∈ t ∧ 1 < g b}.Finite) :
    (Function.support fun a : s => (r a : ℤ) - 1).Finite ∧
      ∑ᶠ a ∈ s, ((r a : ℤ) - 1) ≤ ((∑ᶠ b ∈ t, (g b - 1) : ℕ) : ℤ) := by
  have hr1 : ∀ a ∈ s, 1 ≤ r a := fun a ha => hr a ha ▸ hg _ (hst ha)
  have hsupp : (s ∩ Function.support fun a => r a - 1).Finite := by
    refine (ht.preimage he.injOn).subset fun a ⟨ha, h1⟩ => ⟨hst ha, ?_⟩
    rw [Function.mem_support, hr a ha] at h1
    omega
  refine ⟨(hsupp.preimage Subtype.val_injective.injOn).subset fun a h => ⟨a.2, ?_⟩, ?_⟩
  · have := hr1 a a.2
    simp only [Set.mem_preimage, Function.mem_support] at h ⊢
    omega
  · rw [finsum_mem_congr rfl fun a ha => (by have := hr1 a ha; omega :
      ((r a : ℤ) - 1) = ((r a - 1 : ℕ) : ℤ)), ← natCast_finsum_mem hsupp, Nat.cast_le]
    rw [finsum_mem_congr rfl fun a ha => by rw [hr a ha]]
    exact finsum_mem_comp_le (g := fun b => g b - 1) he hst
      (ht.subset fun b ⟨hb, h1⟩ => ⟨hb, by rw [Function.mem_support] at h1; omega⟩)

/-- A set on which a natural weight is at least `1` has cardinality at most the finitely supported
sum of the weight over any superset. -/
private theorem encard_le_finsum_mem {α : Type*} {w : α → ℕ} {s t : Set α} (hst : s ⊆ t)
    (ht : (t ∩ Function.support w).Finite) (hw : ∀ a ∈ s, 1 ≤ w a) :
    s.encard ≤ ((∑ᶠ a ∈ t, w a : ℕ) : ℕ∞) := by
  have hs : s.Finite := ht.subset fun a ha => ⟨hst ha, Nat.one_le_iff_ne_zero.1 (hw a ha)⟩
  rw [hs.encard_eq_coe_toFinset_card, Nat.cast_le, Finset.card_eq_sum_ones]
  exact (Finset.sum_le_sum fun a ha => hw a (hs.mem_toFinset.1 ha)).trans
    ((finsum_mem_eq_finite_toFinset_sum w hs).symm.trans_le
      (finsum_mem_le_finsum_mem_of_subset hst ht))

/-! ### Weights and defaults -/

/-- At a positive scale, the weight of a positive number is at least `1`. -/
private theorem one_le_difficultyWeight {N : ℕ} (hN : 0 < N) {u : ℝ} (hu : 0 < u) :
    1 ≤ difficultyWeight N u :=
  Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.ceil_pos.2
    (mul_pos (Nat.cast_pos.2 hN) (lt_max_iff.2 (Or.inl hu)))))

/-- At a positive scale, the default `d(b)` of a coefficient `0 < b < 1` is at least `1`: its
summand of order `j = 1` is the weight `w(b) ≥ 1`. -/
private theorem one_le_defaultWeight {N : ℕ} (hN : 0 < N) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    1 ≤ defaultWeight N b := by
  have h1 : ∑ᶠ j ∈ ({1} : Set ℕ), difficultyWeight N (1 - j * (1 - b)) ≤
      ∑ᶠ j ∈ {j : ℕ | 1 ≤ j}, difficultyWeight N (1 - j * (1 - b)) :=
    finsum_mem_le_finsum_mem_of_subset (by simp)
      ((finite_support_difficultyWeight N hb1).subset Set.inter_subset_right)
  rw [finsum_mem_singleton] at h1
  have h2 : 1 ≤ difficultyWeight N (1 - ((1 : ℕ) : ℝ) * (1 - b)) := by
    refine one_le_difficultyWeight hN ?_
    simpa using hb0
  exact h2.trans h1

/-! ### Curves and points on a threefold -/

/-- The closure of the generic point of a proper curve has dimension one: it is the image of the
closed embedding of the curve. -/
private theorem topologicalKrullDim_closure_point {k : Type*} [Field k] {X : Scheme}
    {sX : X ⟶ Spec (.of k)} (C : MMP.Mori.ProperCurve sX) :
    topologicalKrullDim (closure {C.point} : Set X) = 1 := by
  have hr : Set.range C.ι = closure {C.point} := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hr, ← C.dim_eq]
  exact (IsHomeomorph.topologicalKrullDim_eq _
    C.ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph).symm

/-- On an integral scheme of dimension three, locally of finite type over a field, a divisorial
valuation whose centre is a closed point is exceptional. -/
private theorem isExceptionalValuation_of_isCentre_singleton {k : Type} [Field k]
    {Y : Scheme.{0}} [IsIntegral Y] {sY : Y ⟶ Spec (.of k)} [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 3) {Z : IrreducibleCloseds Y} {y : Y}
    (hZ : (Z : Set Y) = {y}) {v : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hv : MMP.Intersection.IsCentre k sY v Z) :
    MMP.Intersection.IsExceptionalValuation k sY v := by
  obtain ⟨D, hD, hDv, rfl⟩ := hv
  refine ⟨D, hD, hDv, ?_⟩
  have hcl : closure ({y} : Set Y) = {y} := by rw [← hZ]; exact D.center.isClosed.closure_eq
  have hy : D.center.isIrreducible.genericPoint = y := by
    have h := D.center.isIrreducible.closure_genericPoint D.center.isClosed
    have hmem : D.center.isIrreducible.genericPoint ∈ (D.center : Set Y) :=
      h.subset (subset_closure rfl)
    exact (Set.ext_iff.1 hZ _).1 hmem
  rw [MMP.Flips.codimension_eq_coheight_genericPoint, hy]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY y
  rw [hcl, hdim] at h
  have h0 : topologicalKrullDim ({y} : Set Y) ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
  generalize topologicalKrullDim ({y} : Set Y) = a at h h0
  generalize Order.coheight y = c at h ⊢
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe a =>
    have ha : a = 0 := by
      have : (a : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := h0
      exact le_antisymm (WithBot.coe_le_coe.1 this) zero_le
    subst ha
    have hc : c = 3 := by
      have h' : ((0 + c : ℕ∞) : WithBot ℕ∞) = ((3 : ℕ∞) : WithBot ℕ∞) := by
        push_cast
        exact h
      simpa using WithBot.coe_injective h'
    rw [hc]
    decide

/-- At a junction of a prepared chain, a divisorial valuation centred at a closed point, with log
discrepancy `< 2`, is exceptional with that closed point as centre, and its weight is at least
`1`. -/
private theorem isExceptionalValuation_and_one_le_weight {T : StabilizedTail} (Q : PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i)
    {w : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → ℕ}
    (hw : ∀ v, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v →
      (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}) →
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v))
    {U : Set (Q.chain.model ⟨i, none⟩)}
    {v : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ))}
    (hv : (∃ (Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩)) (y : Q.chain.model ⟨i, none⟩),
        (Z : Set (Q.chain.model ⟨i, none⟩)) = {y} ∧ y ∈ U ∧
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z) ∧
      ∃ a : ℝ, IsValuationLogDiscrepancy (Q.chain.modelStructure ⟨i, none⟩)
        (Q.chain.modelBoundary ⟨i, none⟩) v a ∧ a < 2) :
    (MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
      ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}) ∧ 1 ≤ w v := by
  obtain ⟨⟨Z, y, hZy, -, hcent⟩, a, ⟨n, D, -, hDv, hD⟩, ha2⟩ := hv
  obtain ⟨-, hproj, -, hdim, -⟩ := Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  haveI : LocallyOfFiniteType (Q.chain.modelStructure ⟨i, none⟩) :=
    hproj.toIsVariety.toLocallyOfFiniteType
  have hexc := isExceptionalValuation_of_isCentre_singleton hdim hZy hcent
  have hcl : IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) := hZy ▸ Z.isClosed
  refine ⟨⟨hexc, Z, hcent, y, hcl, hZy⟩, ?_⟩
  obtain ⟨-, a', ⟨n', D', -, hDv', hD'⟩, hwv⟩ := hw v hexc ⟨Z, hcent, y, hcl, hZy⟩
  obtain rfl : a = a' := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hD hD'
    (hDv.trans hDv'.symm)
  rw [hwv]
  exact one_le_difficultyWeight Q.isAdmissibleScale.pos (by linarith)

private theorem solution : ∀ {T : StabilizedTail} (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i)
    (r : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) → ℕ)
    (hr : ∀ γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩),
      closure {γ.point} ⊆ Q.chain.varyingUnion i →
        Q.chain.IsVaryingBranchNumber ⟨i, none⟩ γ (r γ))
    (d ρ : Q.chain.Label → ℕ)
    (hd : ∀ S, Q.chain.IsVaryingLabel S → Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ (d S))
    (hρ : ∀ S, Q.chain.IsVaryingLabel S → Q.chain.IsLabelBoxedRank S ⟨i, none⟩ (ρ S))
    (w : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v →
      (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}) →
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)),
    (Function.support fun γ : {γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) //
        closure {γ.point} ⊆ Q.chain.varyingUnion i} => ((r γ.1 : ℤ) - 1)).Finite ∧
    ∑ᶠ (γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩))
        (_ : closure {γ.point} ⊆ Q.chain.varyingUnion i), ((r γ : ℤ) - 1) ≤
      ((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), d S * ρ S : ℕ) : ℤ) +
        ((∑ᶠ (v) (_ : MMP.Intersection.IsExceptionalValuation ℂ
            (Q.chain.modelStructure ⟨i, none⟩) v ∧
          ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
            MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
              ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
                (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}), w v : ℕ) : ℤ) := by
  intro T Q i hi r hr d ρ hd hρ w hw
  classical
  obtain ⟨hterm, hproj, hQf, hdim, ⟨c, hcinj, hc, hsupp, hc01⟩, -⟩ :=
    Q.echoSetting_model ⟨⟨i, none⟩, hi⟩
  have hcu : ∀ S P, Q.chain.IsLabelCentre S ⟨i, none⟩ P → P = c S :=
    fun S _ h => isLabelCentre_junction_unique Q.chain h (hc S)
  haveI := Q.chain.finite_label
  have hVfin : {S : Q.chain.Label | Q.chain.IsVaryingLabel S}.Finite := Set.toFinite _
  set V := hVfin.toFinset
  set QF : Finset (MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩)) := V.image c
  have hmemQF : ∀ P, P ∈ QF ↔ ∃ S, Q.chain.IsVaryingLabel S ∧ c S = P := by
    simp [QF, V]
  have hunion : (⋃ P ∈ QF, (P.support : Set (Q.chain.model ⟨i, none⟩))) =
      Q.chain.varyingUnion i := by
    ext y
    simp only [Set.mem_iUnion, hmemQF, exists_prop]
    constructor
    · rintro ⟨P, ⟨S, hS, rfl⟩, hy⟩
      exact ⟨S, hS, c S, hc S, hy⟩
    · rintro ⟨S, hS, P, hP, hy⟩
      exact ⟨P, ⟨S, hS, (hcu S P hP).symm⟩, hy⟩
  have hcoeff_pos : ∀ S, Q.chain.IsVaryingLabel S →
      0 < (Q.chain.modelBoundary ⟨i, none⟩).coeff (c S) := by
    intro S hS
    obtain ⟨b, ⟨P, hP, hPb⟩, hb⟩ := Q.pos_of_isVaryingLabel i hi S hS
    rw [← hcu S P hP, hPb]
    exact hb
  have hΘ0 : 0 ≤ Q.chain.modelBoundary ⟨i, none⟩ := by
    refine Finsupp.le_def.2 fun P => ?_
    by_cases hP : (Q.chain.modelBoundary ⟨i, none⟩).coeff P = 0
    · exact hP.ge
    · obtain ⟨S, rfl⟩ := hsupp P hP
      exact (hc01 S).1
  obtain ⟨h1, h2, h3⟩ := sum_boundaryBranchCount_sub_one_le_of_threefold
    (X := T.X i) (Y := Q.chain.model ⟨i, none⟩) (T.sX i) (Q.chain.modelStructure ⟨i, none⟩)
    (T.isThreefoldStepDiagram i).isNormalVariety_minus (T.isProjectiveVariety i) (T.dim_eq i)
    (Q.chain.junction i).p rfl
    (Q.chain.junction i).isProjectiveMorphism (Q.chain.junction i).isBirationalMorphism
    hproj hdim hQf (Q.chain.modelBoundary ⟨i, none⟩) hΘ0 hterm QF
    (fun P hP => by obtain ⟨S, hS, rfl⟩ := (hmemQF P).1 hP; exact hcoeff_pos S hS)
    (by rw [hunion]; exact Q.finite_image_varyingUnion hi)
  -- curves: a proper curve `γ` is the irreducible closed subset `closure {γ.point}`
  let Cl : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) →
      IrreducibleCloseds (Q.chain.model ⟨i, none⟩) :=
    fun γ => ⟨closure {γ.point}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hCl_inj : Function.Injective Cl := fun γ γ' h => ProperCurve.ext
    (inseparable_iff_closure_eq.2
      (congrArg (SetLike.coe : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) → _) h)).eq
  have hcount : ∀ γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩),
      closure {γ.point} ⊆ Q.chain.varyingUnion i → r γ = boundaryBranchCount QF (Cl γ) := by
    intro γ hγ
    have hpos := h1 (Cl γ) (topologicalKrullDim_closure_point γ) (hunion ▸ hγ)
    have hfinσ : {P : (S : QF) × MMP.Mori.PrimeDivisor
        (primeDivisorNormalizationScheme (S : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩))) |
        primeDivisorNormalization (P.1 : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩)) ''
          P.2.support = closure {γ.point}}.Finite :=
      Set.finite_of_ncard_ne_zero (Nat.one_le_iff_ne_zero.1 hpos)
    change r γ = boundaryBranchCount QF (closure {γ.point})
    rw [boundaryBranchCount_eq_sum (fun S hS => hfinσ.preimage
      (Set.injOn_of_injective (f := fun P => (⟨⟨S, hS⟩, P⟩ : (S : QF) × _)) sigma_mk_injective)),
      Finset.sum_image (fun S _ S' _ h => hcinj h)]
    obtain ⟨r', hr', hreq⟩ := hr γ hγ
    rw [hreq]
    refine (finsum_mem_eq_finite_toFinset_sum r' hVfin).trans (Finset.sum_congr rfl fun S hS => ?_)
    obtain ⟨P, hP, hPr⟩ := hr' S (hVfin.mem_toFinset.1 hS)
    rw [hPr, hcu S P hP]
  have hcurve := finsum_mem_intCast_sub_one_le
    (g := fun C : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) =>
      boundaryBranchCount QF C)
    hCl_inj (fun γ hγ => ⟨topologicalKrullDim_closure_point γ, hunion ▸ hγ⟩)
    (t := {C : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) |
      topologicalKrullDim (C : Set (Q.chain.model ⟨i, none⟩)) = 1 ∧
        (C : Set (Q.chain.model ⟨i, none⟩)) ⊆
          ⋃ S ∈ QF, (S.support : Set (Q.chain.model ⟨i, none⟩))})
    hcount (fun C hC => h1 C hC.1 hC.2) (h2.subset fun C ⟨⟨hC1, hC2⟩, hC3⟩ => ⟨hC1, hC2, hC3⟩)
  refine ⟨hcurve.1, hcurve.2.trans ?_⟩
  -- the boxed ranks: every default `d_h` of a varying label is at least `1`
  have hρle : (∑ S ∈ QF,
        letI := primeDivisorNormalizationOver (Q.chain.modelStructure ⟨i, none⟩) S
        haveI := isComplexScheme_primeDivisorNormalizationScheme
          (Q.chain.modelStructure ⟨i, none⟩) hproj S
        boxedSurfaceRank (primeDivisorNormalizationScheme S) : ℕ) ≤
      ∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), d S * ρ S := by
    refine (Finset.sum_image (fun S _ S' _ h => hcinj h)).trans_le
      ((Finset.sum_le_sum fun S hS => ?_).trans_eq (finsum_mem_eq_finite_toFinset_sum _ hVfin).symm)
    have hS' := hVfin.mem_toFinset.1 hS
    obtain ⟨P, hP, hρP⟩ := hρ S hS'
    obtain rfl := hcu S P hP
    obtain ⟨b, ⟨P', hP', hP'b⟩, hdb⟩ := hd S hS'
    obtain rfl := hcu S P' hP'
    rw [← hρP]
    refine Nat.le_mul_of_pos_left _ ?_
    rw [hdb, ← hP'b]
    exact one_le_defaultWeight Q.isAdmissibleScale.pos (by exact_mod_cast hcoeff_pos S hS')
      (by exact_mod_cast (hc01 S).2)
  -- the valuations: each is exceptional with weight at least `1`
  have hEfin : ({v | MMP.Intersection.IsExceptionalValuation ℂ
        (Q.chain.modelStructure ⟨i, none⟩) v ∧
      ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}} ∩ Function.support w).Finite := by
    refine (Q.finite_setOf_isCentre_singleton ⟨⟨i, none⟩, hi⟩).subset ?_
    rintro v ⟨⟨hexc, Z, hcent, y, hcl, hZy⟩, hwv⟩
    exact ⟨⟨Z, y, hcent, hZy⟩, w v, hw v hexc ⟨Z, hcent, y, hcl, hZy⟩, hwv⟩
  have hfinal := h3.trans (add_le_add (Nat.cast_le.2 hρle)
    (encard_le_finsum_mem (fun v hv => (isExceptionalValuation_and_one_le_weight Q hi hw hv).1)
      hEfin fun v hv => (isExceptionalValuation_and_one_le_weight Q hi hw hv).2))
  exact_mod_cast (Nat.cast_le (α := ℕ∞)).1 (by exact_mod_cast hfinal)

end Proof_lem_mmp_indexb_varying_excess_bound

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

namespace StabilizedTail

namespace PreparedChain

variable {T : StabilizedTail}

/-- At a junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, of a prepared chain, with varying
union `Q`, the varying branch excess is paid by positive terms:
`∑_{C ⊆ Q} (r_C^var - 1) ≤ ∑_{h varying} d_h ρ^□(S_h^ν) + ∑_v w_v(Y_i, Θ_i)`, where `C` runs over
the irreducible closed curves of `Y_i` contained in `Q`, with varying branch numbers `r_C^var`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsVaryingBranchNumber`); `h` over the varying labels,
with defaults `d_h` (`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelDefault`) at the
admissible scale and boxed ranks `ρ^□(S_h^ν)`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBoxedRank`); and `v` over the normalized
divisorial valuations of `ℂ(Y_i)` exceptional over `Y_i` whose centre is a closed point, with
weights `w_v` (`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`). The left side has
finite support. -/
@[mmp "lem_mmp_indexb_varying_excess_bound"]
public theorem varyingBranchExcess_le (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i)
    (r : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) → ℕ)
    (hr : ∀ γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩),
      closure {γ.point} ⊆ Q.chain.varyingUnion i →
        Q.chain.IsVaryingBranchNumber ⟨i, none⟩ γ (r γ))
    (d ρ : Q.chain.Label → ℕ)
    (hd : ∀ S, Q.chain.IsVaryingLabel S → Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ (d S))
    (hρ : ∀ S, Q.chain.IsVaryingLabel S → Q.chain.IsLabelBoxedRank S ⟨i, none⟩ (ρ S))
    (w : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v →
      (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
            (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}) →
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)) :
    (Function.support fun γ : {γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩) //
        closure {γ.point} ⊆ Q.chain.varyingUnion i} => ((r γ.1 : ℤ) - 1)).Finite ∧
    ∑ᶠ (γ : ProperCurve (Q.chain.modelStructure ⟨i, none⟩))
        (_ : closure {γ.point} ⊆ Q.chain.varyingUnion i), ((r γ : ℤ) - 1) ≤
      ((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), d S * ρ S : ℕ) : ℤ) +
        ((∑ᶠ (v) (_ : MMP.Intersection.IsExceptionalValuation ℂ
            (Q.chain.modelStructure ⟨i, none⟩) v ∧
          ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
            MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
              ∃ y : Q.chain.model ⟨i, none⟩, IsClosed ({y} : Set (Q.chain.model ⟨i, none⟩)) ∧
                (Z : Set (Q.chain.model ⟨i, none⟩)) = {y}), w v : ℕ) : ℤ) :=
                  by revert Q i hi r hr d ρ hd hρ w hw; first | exact Proof_lem_mmp_indexb_varying_excess_bound.solution | exact Proof_lem_mmp_indexb_varying_excess_bound.solution _ | exact Proof_lem_mmp_indexb_varying_excess_bound.solution _ _ | exact Proof_lem_mmp_indexb_varying_excess_bound.solution _ _ _ | exact Proof_lem_mmp_indexb_varying_excess_bound.solution _ _ _ _

end PreparedChain

end StabilizedTail

end MMP.Fourfold
