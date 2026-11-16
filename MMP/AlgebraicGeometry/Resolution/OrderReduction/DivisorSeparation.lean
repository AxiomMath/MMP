module
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
import MMP.AlgebraicGeometry.Resolution.OrderReduction.BdFunctorSmoothPullback
import MMP.AlgebraicGeometry.Resolution.OrderReduction.EmptyEntriesInert
import MMP.AlgebraicGeometry.Intersection.CartierRestriction

/-!
# The divisor separation sequence

Fix `N ≥ 1`, a marked order-reduction family `𝓜` on dimensions `0, …, N - 1` and `m ≥ 1`. Let
`(X, I, E)` be a triple with `1 ≤ dim X ≤ N`, `maxord I ≤ m` and `E = (E^1, …, E^s)`. The divisor
separation sequence `Π_{(s)}` of `(X, I, E)` concatenates the sequences `𝓑𝓓_{dim X, m, j}`
applied successively to the ends `(X_{(j)}, I_{(j)}, E_{(j)})`; let `(X', I', E')` be its end.

* Each `𝓑𝓓` step is a smooth blow-up sequence of order `m`, and along such a sequence the ends
  stay triples of the same dimension with `maxord ≤ m`; so `Π_{(s)}` is a smooth blow-up sequence
  of order `m` starting with `(X, I, E)`.
* Every `E'^i`, `i = 1, …, s` (the birational transform of `E^i`) is disjoint from
  `cosupp(I', m)`: the step `𝓑𝓓_{j}` separates `E^j`, and a later sequence of order `m` maps the
  new cosupport into the old one while `E'^i` lies over `E^i`.
* If `maxord I = m` and `H` is an MC-hypersurface for `I`, the birational transform `H'` of `H`
  followed by the exceptional members `E'^{s+1}, …, E'^{s'}` is an ordered snc divisor. The
  sequence is of order `≥ 1` for `(MC(I), 1)`, so every centre lies in the transform of `H`, and
  one blow-up along a smooth centre `Z ⊆ H_l` having snc with `E_l` keeps `H_l` together with
  the new members ordered snc.

## Main results

* `MMP.Resolution.divisorSeparationSequence_isOrderMTripleSeq`: `Π_{(s)}` has order `m`.
* `MMP.Resolution.disjoint_cosupport_divisorSeparationSequence`: `E'^i ∩ cosupp(I', m) = ∅`.
* `MMP.Resolution.isOrderedSNC_divisorSeparationSequence`: `(H', E'^{s+1}, …, E'^{s'})` is
  ordered snc.

## Implementation notes

Indices of ordered divisors are `0`-based. The source splits a blow-up inside `H_l` into two
cases: a centre all of whose components have codimension `≥ 2`, and a centre containing
components of `H_l`, which are then removed from `H_l` while nothing new is appended. Both are
treated at once here: for a smooth centre `Z ⊆ H_l` having snc with `(H_l, D_l)` the total
transform of `(H_l, D_l)` is ordered snc, and near every point of the blow-up it is cut out by
the same coordinates as `(H_{l+1}, D_{l+1})`, after exchanging, over the components of `Z` which
are components of `H_l`, the transform of `H_l` with the last member. The components of the
smooth schemes `H_l` and `Z` are disjoint, which makes the exchange local.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.103 proof Step 2.1 and
  3.104 Step 2.1.`j`, Step 2.1.`s` and the two bullets after it]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-! ### Smooth blow-up sequences of order `m` -/

/-- A concatenation of smooth blow-up sequences of order `m` is one. -/
private theorem isOrderMTripleSeq_append {k : Type u} [Field k] (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (C : ClosedBlowupSequence B.target)
      (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X),
      B.IsOrderMTripleSeq s I E m →
      C.IsOrderMTripleSeq (B.toBase ≫ s) (B.controlledTransform I) (B.orderedTotalTransform E) m →
      (B.append C).IsOrderMTripleSeq s I E m
  | _, .nil _, C, s, I, E, _, hC => by
    change C.IsOrderMTripleSeq (𝟙 _ ≫ s) I E m at hC
    rwa [Category.id_comp] at hC
  | _, .cons Z B, C, s, I, E, hB, hC => by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hB
    refine ⟨h1, h2, h3, h4, h5, isOrderMTripleSeq_append m B C _ _ _ h6 ?_⟩
    change C.IsOrderMTripleSeq ((B.toBase ≫ blowUpToBase Z) ≫ s) _ _ m at hC
    rwa [Category.assoc] at hC

/-- A generic point of `X` lies off a closed subscheme all of whose components have positive
codimension. -/
private theorem notMem_supportSet_of_mem_genericPoints {X : Scheme}
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
  simp [Order.coheight_eq_zero.2 hmax] at hcod

/-- The blow-up of an equidimensional scheme locally of finite type over a field along a closed
subscheme all of whose components have positive codimension has the same dimension. -/
private theorem topologicalKrullDim_blowUp {k : Type u} [Field k] {X : Scheme}
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

/-- Along a smooth blow-up sequence of order `m` starting with a triple with `maxord ≤ m`, the
end keeps the dimension, has `maxord ≤ m`, and its ordered divisor is at least as long. -/
private theorem end_of_isOrderMTripleSeq {k : Type u} [Field k] (m : ℕ) (d : WithBot ℕ∞) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X),
      B.IsOrderMTripleSeq s I E m → maxOrder I ≤ m → topologicalKrullDim X = d →
      topologicalKrullDim B.target = d ∧ maxOrder (B.controlledTransform I) ≤ m ∧
        E.s ≤ (B.orderedTotalTransform E).s
  | _, .nil _, _, _, _, _, hmax, hd => ⟨hd, hmax, le_rfl⟩
  | _, .cons Z B, s, I, E, hB, hmax, hd => by
    obtain ⟨hT, hZ, hc, -, hEq, hB'⟩ := hB
    obtain ⟨-, hX, hlft, hqc, hequi, hI, -⟩ := hT
    have hmax' : maxOrder (MMP.Resolution.controlledTransform Z I) ≤ m := by
      haveI := hX.smooth
      haveI := hZ.smooth
      refine (maxOrder_controlledTransform_le s Z hc I hI fun W hW => le_antisymm ?_
        (hmax.trans (hEq W hW).ge)).trans hmax
      exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) _ (Set.mem_univ _)
    obtain ⟨h1, h2, h3⟩ := end_of_isOrderMTripleSeq m d B _ _ _ hB' hmax'
      ((topologicalKrullDim_blowUp s hequi Z hc).trans hd)
    exact ⟨h1, h2, (Nat.le_succ _).trans h3⟩

/-- The end of a concatenation is the end of the second sequence started at the end of the
first. -/
private theorem append_end_iff (P : ∀ Y : Scheme.{u}, Y.IdealSheafData → OrderedDivisor Y → Prop) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (C : ClosedBlowupSequence B.target)
      (I : X.IdealSheafData) (E : OrderedDivisor X),
      P (B.append C).target ((B.append C).controlledTransform I)
          ((B.append C).orderedTotalTransform E) ↔
        P C.target (C.controlledTransform (B.controlledTransform I))
          (C.orderedTotalTransform (B.orderedTotalTransform E))
  | _, .nil _, _, _, _ => Iff.rfl
  | _, .cons _ B, C, _, _ => append_end_iff P B C _ _

/-- The end of a smooth blow-up sequence of order `m` starting with a triple is a triple. -/
private theorem isTriple_end {k : Type u} [Field k] (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X), B.IsOrderMTripleSeq s I E m →
      IsTriple (B.toBase ≫ s) (B.controlledTransform I) (B.orderedTotalTransform E)
  | _, .nil _, s, I, E, h => by
    change IsTriple (𝟙 _ ≫ s) I E
    rwa [Category.id_comp]
  | _, .cons Z B, s, I, E, h => by
    have := isTriple_end m B _ _ _ h.2.2.2.2.2
    change IsTriple ((B.toBase ≫ blowUpToBase Z) ≫ s) _ _
    rwa [Category.assoc]

/-- Truncating a sequence at its length gives the whole sequence. -/
private theorem truncate_length :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X), B.truncate B.length = B
  | _, .nil _ => rfl
  | _, .cons Z B => congrArg (ClosedBlowupSequence.cons Z) (truncate_length B)

/-! ### The divisor separation sequence has order `m` -/

/-- **Kollár 3.104, Step 2.1.`j`.** Let `𝓜` be a marked order-reduction family on dimensions
`0, …, N - 1` (`IsMarkedOrderReductionFamily`), `(X, I, E)` a triple of dimension `n` with
`1 ≤ n ≤ N`, and `m ≥ 1` with `maxord I ≤ m`. Then the divisor separation sequence
`divisorSeparationSequence M m (X, I, E)` is a smooth blow-up sequence of order `m` starting with
`(X, I, E)` (`ClosedBlowupSequence.IsOrderMTripleSeq`). -/
@[mmp "lem_kr3e_divisor_separation_is_order_m"]
public theorem divisorSeparationSequence_isOrderMTripleSeq {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I ≤ m) :
    (divisorSeparationSequence M m t).IsOrderMTripleSeq t.sX t.I t.E m := by
  have hdn : dimNat t.X = n := by simp [dimNat, hdim]
  suffices h : ∀ j, j ≤ t.E.s → (divisorSeparationAux M m t j).IsOrderMTripleSeq t.sX t.I t.E m from
    h _ le_rfl
  intro j
  induction j with
  | zero => exact fun _ => ht
  | succ j ih =>
    intro hj
    have hP := ih (by omega)
    simp only [divisorSeparationAux]
    split_ifs with hT
    · obtain ⟨hd, hmx, hs⟩ := end_of_isOrderMTripleSeq m _ _ t.sX t.I t.E hP hmax hdim
      rw [hdn]
      exact isOrderMTripleSeq_append m _ _ _ _ _ hP
        (bdFunctor_isOrderMTripleSeq (j := j) M hN hM (t.endOf (divisorSeparationAux M m t j))
          hT hd hn hnN hm hmx
          (by change j < (ClosedBlowupSequence.orderedTotalTransform _ _).s; omega)).1
    · exact hP

/-! ### The divisors are separated from the cosupport -/

/-- The birational transform of `E^i` under one blow-up lies over `E^i`. -/
private theorem support_totalTransform_castSucc_subset {X : Scheme.{u}} (E : OrderedDivisor X)
    (Z : X.IdealSheafData) (i : Fin E.s) :
    (((E.totalTransform Z).E (Fin.castSucc i)).support : Set (blowUp Z)) ⊆
      blowUpToBase Z ⁻¹' ((E.E i).support : Set X) := by
  rw [support_entry_totalTransform, totalTransformSet, Fin.snoc_castSucc]
  exact closure_minimal (Set.preimage_mono Set.diff_subset)
    (((E.E i).support.isClosed).preimage (blowUpToBase Z).continuous)

/-- The `i`-th member of the ordered total transform lies over the `i`-th member of `E`. -/
private theorem support_orderedTotalTransform_subset (i : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (E : OrderedDivisor X) (hi : i < E.s),
      ∃ h : i < (B.orderedTotalTransform E).s,
        (((B.orderedTotalTransform E).E ⟨i, h⟩).support : Set B.target) ⊆
          B.toBase ⁻¹' ((E.E ⟨i, hi⟩).support : Set X)
  | _, .nil _, _, hi => ⟨hi, fun _ hx => hx⟩
  | _, .cons Z B, E, hi => by
    obtain ⟨h, hsub⟩ := support_orderedTotalTransform_subset i B (E.totalTransform Z)
      (show i < E.s + 1 by omega)
    exact ⟨h, hsub.trans fun _ hx => support_totalTransform_castSucc_subset E Z ⟨i, hi⟩ hx⟩

/-- Along a smooth blow-up sequence of order `m` starting with a triple `(X, I, E)` with
`maxord I = m`, the cosupport of `(I_r, m)` lies over that of `(I, m)`. -/
private theorem cosupport_controlledTransform_subset {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (hI : IsTriple s I E)
    (m : ℕ) (hm : maxOrder I = m) (B : ClosedBlowupSequence X)
    (hB : B.IsOrderMTripleSeq s I E m) :
    (⟨B.controlledTransform I, m⟩ : MarkedIdeal B.target).cosupport ⊆
      B.toBase ⁻¹' (⟨I, m⟩ : MarkedIdeal X).cosupport := by
  obtain ⟨hiff, hct⟩ := ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq
    s I E hI m hm B
  have h := ClosedBlowupSequence.cosupport_markedTransform_truncate_subset s _ E B
    (hiff.2 hB) B.length
  have he : B.markedTransform ⟨I, m⟩ = ⟨B.controlledTransform I, m⟩ :=
    congrArg₂ MarkedIdeal.mk (hct hB) (B.markedTransform_m _)
  rwa [truncate_length, he] at h

/-- One step of the induction: a sequence of order `m` (or the empty one) keeps the `i`-th
member of the divisor disjoint from the cosupport. -/
private theorem disjoint_step {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (hI : IsTriple s I E)
    (m i : ℕ) (C : ClosedBlowupSequence X) (hC : C.IsOrderMTripleSeq s I E m)
    (hnil : maxOrder I ≠ m → C = .nil X)
    (h : ∃ hi : i < E.s,
      Disjoint (⟨I, m⟩ : MarkedIdeal X).cosupport ((E.E ⟨i, hi⟩).support : Set X)) :
    ∃ hi : i < (C.orderedTotalTransform E).s,
      Disjoint (⟨C.controlledTransform I, m⟩ : MarkedIdeal C.target).cosupport
        (((C.orderedTotalTransform E).E ⟨i, hi⟩).support : Set C.target) := by
  by_cases hm : maxOrder I = m
  · obtain ⟨hi, hd⟩ := h
    obtain ⟨hi', hsub⟩ := support_orderedTotalTransform_subset i C E hi
    exact ⟨hi', Set.disjoint_of_subset (cosupport_controlledTransform_subset s I E hI m hm C hC)
      hsub (hd.preimage _)⟩
  · obtain rfl := hnil hm
    exact h

/-- **Kollár 3.104, Step 2.1.`s`.** Let `𝓜` be a marked order-reduction family on dimensions
`0, …, N - 1`, `(X, I, E)` a triple of dimension `n` with `1 ≤ n ≤ N`, and `m ≥ 1` with
`maxord I ≤ m`. Let `(X', I', E')` be the end of the divisor separation sequence
`divisorSeparationSequence M m (X, I, E)`. Then for every index `i` of `E`, the `i`-th member of
`E'` is disjoint from the cosupport of the marked ideal `(I', m)`. -/
@[mmp "lem_kr3e_divisor_separation_disjoint"]
public theorem disjoint_cosupport_divisorSeparationSequence {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I ≤ m) (i : ℕ) (hi : i < t.E.s) :
    let tr := t.endOf (divisorSeparationSequence M m t)
    ∃ hir : i < tr.E.s,
      Disjoint (⟨tr.I, m⟩ : MarkedIdeal tr.X).cosupport
        ((tr.E.E ⟨i, hir⟩).support : Set tr.X) := by
  have hdn : dimNat t.X = n := by simp [dimNat, hdim]
  let Q : ℕ → ∀ Y : Scheme.{u}, Y.IdealSheafData → OrderedDivisor Y → Prop := fun i Y I E =>
    ∃ hir : i < E.s, Disjoint (⟨I, m⟩ : MarkedIdeal Y).cosupport ((E.E ⟨i, hir⟩).support : Set Y)
  suffices h : ∀ j, j ≤ t.E.s →
      (divisorSeparationAux M m t j).IsOrderMTripleSeq t.sX t.I t.E m ∧
      ∀ i < j, Q i _ ((divisorSeparationAux M m t j).controlledTransform t.I)
        ((divisorSeparationAux M m t j).orderedTotalTransform t.E) from
    (h _ le_rfl).2 i hi
  intro j
  induction j with
  | zero => exact fun _ => ⟨ht, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ j ih =>
    intro hj
    obtain ⟨hP, hQ⟩ := ih (by omega)
    have hT := isTriple_end m _ t.sX t.I t.E hP
    obtain ⟨hd, hmx, hs⟩ := end_of_isOrderMTripleSeq m _ _ t.sX t.I t.E hP hmax hdim
    have hjs : j < (t.endOf (divisorSeparationAux M m t j)).E.s := by
      change j < (ClosedBlowupSequence.orderedTotalTransform _ _).s; omega
    have hC := (bdFunctor_isOrderMTripleSeq (j := j) M hN hM
      (t.endOf (divisorSeparationAux M m t j)) hT hd hn hnN hm hmx hjs).1
    have key : divisorSeparationAux M m t (j + 1) = (divisorSeparationAux M m t j).append
        (bdFunctor M n m j (t.endOf (divisorSeparationAux M m t j))) := by
      rw [← hdn]
      exact if_pos hT
    rw [key]
    refine ⟨isOrderMTripleSeq_append m _ _ _ _ _ hP hC, fun i' hi' => ?_⟩
    refine (append_end_iff (Q i') (divisorSeparationAux M m t j)
      (bdFunctor M n m j (t.endOf (divisorSeparationAux M m t j))) t.I t.E).2 ?_
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
    · exact disjoint_step _ _ _ hT m i' _ hC (fun hne => dif_neg fun h => hne h.1) (hQ i' hlt)
    · exact disjoint_cosupport_bdFunctor M hN hM (t.endOf (divisorSeparationAux M m t i')) hT hd hn
        hnN hm hmx hjs

/-! ### The transform of an MC-hypersurface and the new divisors are snc -/

section SNC

open ClosedBlowupSequence

/-- Every blow-up of a sequence appends one member to the iterated total transform. -/
private theorem orderedTotalTransform_s : ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X)
    (E : OrderedDivisor X), (B.orderedTotalTransform E).s = E.s + B.length
  | _, .nil _, _ => rfl
  | _, .cons Z B, E => by
    rw [ClosedBlowupSequence.orderedTotalTransform, orderedTotalTransform_s B,
      ClosedBlowupSequence.length]
    change E.s + 1 + B.length = _
    omega

/-- The ordered divisor `(H, E^{s₀+1}, …, E^s)`: `H` followed by the members of `E` of
(`0`-based) index at least `s₀`. -/
private abbrev consTail {X : Scheme.{u}} (H : X.IdealSheafData) (E : OrderedDivisor X)
    (s₀ : ℕ) : OrderedDivisor X :=
  ⟨E.s - s₀ + 1, Fin.cons (α := fun _ => X.IdealSheafData) H
    fun i => E.E ⟨s₀ + i, by have := i.isLt; omega⟩⟩

/-! ### Transforms of a hypersurface along a sequence of order `≥ 1` -/

/-- An ideal sheaf contained in one of order `≥ 1` along a smooth centre `Z` of a smooth scheme
is contained in the ideal sheaf of `Z`. -/
private theorem le_of_le_of_orderAlongGE_one {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (hX : MMP.Mori.IsSmoothScheme sX) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) {K I : X.IdealSheafData} (hKI : K ≤ I)
    (hI : OrderAlongGE I (Z.support : Set X) ((1 : ℕ) : ℕ∞)) : K ≤ Z := by
  refine hKI.trans (IdealSheafData.le_of_stalk_le _ _ fun x => ?_)
  simpa using stalk_le_pow_of_orderAlongGE sX hX Z hZ I 1 hI x

/-- An effective Cartier divisor can be cancelled from an inclusion: `A·D ≤ B·D` forces
`A ≤ B`. -/
private theorem le_of_mul_le_mul_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    {A B D : X.IdealSheafData} (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (h : A * D ≤ B * D) : A ≤ B := by
  refine IdealSheafData.le_of_stalk_le _ _ fun y => ?_
  obtain ⟨g, hg, hgs⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor D hD y
  have hy := MMP.Resolution.stalk_le_stalk_of_le h y
  simp only [IdealSheafData.stalk_mul, hgs] at hy
  intro x hx
  have hxg : x * g ∈ IdealSheafData.stalk B y * Ideal.span {g} :=
    hy (Ideal.mul_mem_mul hx (Ideal.mem_span_singleton_self g))
  obtain ⟨b, hb, hbg⟩ := Ideal.mem_mul_span_singleton.mp hxg
  rw [hg.2 hbg] at hb
  exact hb

/-- The canonical lift of a closed immersion `j` has the same ideal sheaf as the canonical lift
of the closed immersion of the subscheme cut out by `ker j`. -/
private theorem ker_canonicalLift_eq {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (Z : X.IdealSheafData) :
    (canonicalLift j Z).ker = (canonicalLift j.ker.subschemeι Z).ker := by
  have hiso : IsIso j.toImage :=
    IsClosedImmersion.isIso_of_ker_eq j j.imageι j.toImage j.toImage_imageι (by simp)
  have key : ∀ (t : S ⟶ j.image) [IsIso t] (g : j.image ⟶ X),
      (canonicalLift (t ≫ g) Z).ker = (canonicalLift g Z).ker := by
    intro t _ g
    have : IsIso (canonicalLift t (Z.comap g)) := MMP.Resolution.Kollar.isIso_canonicalLift t _
    rw [← Scheme.Hom.ker_comp_of_isIso (eqToHom (congrArg blowUp
        (Scheme.IdealSheafData.comap_comp Z t g).symm)),
      ← canonicalLift_comp_canonicalLift, Scheme.Hom.ker_comp_of_isIso]
  conv_lhs => rw [← j.toImage_imageι]
  exact key j.toImage j.imageι

/-- A smooth blow-up sequence of order `≥ m` starting with a marked triple is one starting with
the underlying marked ideal. -/
private theorem isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq sX a E → IsOrderGePlainSeq sX a B
  | _, nil _, _, _, _, h => ⟨h.2.1, h.2.2.2.2.2.1⟩
  | _, cons _ B, _, _, _, h =>
    ⟨h.1.2.1, h.1.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.1,
      isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq B _ _ _ h.2.2.2.2.2⟩

/-- An equidimensional space of dimension `≥ 1` has only positive-dimensional irreducible
components. -/
private theorem pos_of_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    (hX : Equidimensional X) (hdim : 1 ≤ topologicalKrullDim X) :
    ∀ Z ∈ irreducibleComponents X, 0 < topologicalKrullDim Z := by
  intro Z hZ
  by_contra h
  push Not at h
  have : topologicalKrullDim X ≤ 0 :=
    MMP.Flips.topologicalKrullDim_le_of_forall_mem_irreducibleComponents fun W hW =>
      (hX W hW Z hZ).le.trans h
  exact absurd (hdim.trans this) (by decide)

/-- If `maxord K = m`, the maximal-contact ideal of `K` is `D^{m-1}K`. -/
private theorem maximalContactIdeal_eq_of_maxOrder_eq {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) {K : Y.IdealSheafData} {m : ℕ}
    (hK : maxOrder K = m) : maximalContactIdeal s K = higherDerivativeIdeal s K (m - 1) := by
  rw [maximalContactIdeal, hK, ENat.toNat_natCast]

/-! ### Ordered snc divisors from coordinates -/

/-- An ordered divisor on a scheme locally of finite type over a perfect field is ordered snc as
soon as at every point some regular system of parameters cuts out the members through it by
distinct parameters. -/
private theorem isOrderedSNC_of_coords {k : Type u} [Field k] [PerfectField k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (D : OrderedDivisor Y)
    (h : ∀ y : Y, ∃ (n : ℕ) (w : Fin n → Y.presheaf.stalk y)
      (c : {i // y ∈ (D.E i).support} → Fin n), MMP.Mori.IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (D.E i.1) y = Ideal.span {w (c i)}) ∧ Function.Injective c) :
    D.IsOrderedSNC sY := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have hpar : ∀ i, ∀ y ∈ (D.E i).support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y)
      (j : Fin m), MMP.Mori.IsRegularSystemOfParameters w ∧
        IdealSheafData.stalk (D.E i) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨N, w, c, hw, hc, -⟩ := h y
    exact ⟨N, w, c ⟨i, hy⟩, hw, hc ⟨i, hy⟩⟩
  exact ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ (hpar i)⟩,
    ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
      isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
      isSmoothScheme_subscheme_of_stalk_eq_span_parameter _ _ (hpar i)⟩, h⟩⟩

/-- Simple normal crossings with a family passes to a subfamily. -/
private theorem hasSNCWith_comp {X : Scheme.{u}} {Λ Λ' : Type*} {F : Λ → X.IdealSheafData}
    {Z : X.IdealSheafData} (h : HasSNCWith F Z) {σ : Λ' → Λ} (hσ : Function.Injective σ) :
    HasSNCWith (F ∘ σ) Z := by
  intro x hx
  obtain ⟨n, z, c, J, hz, hc, hinj, hJ⟩ := h x hx
  exact ⟨n, z, fun i => c ⟨σ i.1, i.2⟩, J, hz, fun i => hc ⟨σ i.1, i.2⟩,
    fun i i' h => Subtype.ext (hσ (congrArg Subtype.val (hinj h))), hJ⟩

/-- Let `H` be a closed subset of pure codimension one of a noetherian scheme and `Z ⊆ H` a closed
subset. Every irreducible component of `Z` which is not an irreducible component of `H` has
codimension at least two. -/
private theorem two_le_codimension_of_mem_componentsOf {X : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace X]
    {H Z : TopologicalSpace.Closeds X} (hH1 : MMP.Mori.IsPureCodimOne H)
    (hZH : (Z : Set X) ⊆ H) {W : Set X} (hW : W ∈ componentsOf (Z : Set X))
    (hWH : W ∉ componentsOf (H : Set X)) : 2 ≤ codimension (irreducibleClosure hW.1.1) := by
  classical
  have hWc : IsClosed W := Aux.isClosed_of_mem_componentsOf Z.isClosed hW
  obtain ⟨hfin, hcov⟩ := Aux.finite_and_cover_componentsOf H.isClosed
  obtain ⟨H', hH'mem, hWH'⟩ : ∃ H' ∈ componentsOf (H : Set X), W ⊆ H' := by
    obtain ⟨z, hz, hWz⟩ := isIrreducible_iff_sUnion_isClosed.mp hW.1.1 hfin.toFinset
      (fun z hz => Aux.isClosed_of_mem_componentsOf H.isClosed (hfin.mem_toFinset.mp hz))
      (by rw [hfin.coe_toFinset]; exact hW.1.2.trans (hZH.trans hcov))
    exact ⟨z, hfin.mem_toFinset.mp hz, hWz⟩
  have hne : W ≠ H' := fun h => hWH (h ▸ hH'mem)
  have hH'c : IsClosed H' := Aux.isClosed_of_mem_componentsOf H.isClosed hH'mem
  let C' : TopologicalSpace.IrreducibleCloseds X := ⟨H', hH'mem.1.1, hH'c⟩
  have hC' : codimension C' = 1 :=
    hH1 C' ⟨hH'mem.1.2, fun W' hW' hle => hH'mem.2 ⟨W'.isIrreducible, hW'⟩ hle⟩
  have hlt : irreducibleClosure hW.1.1 < C' := by
    refine lt_of_le_of_ne ?_ ?_
    · change closure W ⊆ H'
      rw [hWc.closure_eq]
      exact hWH'
    · intro h
      apply hne
      have := congrArg (fun C : TopologicalSpace.IrreducibleCloseds X => (C : Set X)) h
      simpa [irreducibleClosure, hWc.closure_eq, C'] using this
  have := Order.coheight_add_one_le hlt
  rw [codimension_eq_coheight] at hC' ⊢
  rw [hC'] at this
  exact le_trans (by norm_num) this

/-- Two sets agreeing on an open set have closures agreeing on it. -/
private theorem closure_inter_eq_of_inter_eq {T : Type*} [TopologicalSpace T] {A B U : Set T}
    (hU : IsOpen U) (h : A ∩ U = B ∩ U) : closure A ∩ U = closure B ∩ U := by
  have key : ∀ {A B : Set T}, A ∩ U = B ∩ U → closure A ∩ U ⊆ closure B ∩ U := by
    intro A B h x ⟨hxA, hxU⟩
    refine ⟨?_, hxU⟩
    have : x ∈ closure (A ∩ U) := by simpa [Set.inter_comm] using hU.inter_closure ⟨hxU, hxA⟩
    rw [h] at this
    exact closure_mono Set.inter_subset_left this
  exact subset_antisymm (key h) (key h.symm)

/-- The reduced closed subschemes cut out by the closures of two sets agreeing on an open
neighbourhood of `y` contain `y` together and have the same stalk at `y`. -/
private theorem vanishingIdeal_closure_local {Y : Scheme.{u}} {A B : Set Y} (U : Y.Opens)
    {y : Y} (hy : y ∈ U) (h : A ∩ U = B ∩ U) :
    (y ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A)).support →
      y ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure B)).support) ∧
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A)) y =
        IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure B)) y := by
  have hc := closure_inter_eq_of_inter_eq U.isOpen h
  have hc' : (Closeds.closure A : Set Y) ∩ U = (Closeds.closure B : Set Y) ∩ U := by
    simpa only [Closeds.coe_closure] using hc
  refine ⟨fun hyA => ?_, MMP.Mori.stalk_vanishingIdeal_eq_of_inter_eq _ _ hy hc'⟩
  have h1 : y ∈ (Closeds.closure A : Set Y) := by
    rwa [← Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have h2 : y ∈ (Closeds.closure B : Set Y) ∩ U := by
    rw [← hc']
    exact ⟨h1, hy⟩
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact h2.1

/-- The reduced closed subscheme cut out by the closure of a set meeting an open neighbourhood
of `y` in nothing does not contain `y`. -/
private theorem notMem_support_vanishingIdeal_closure {Y : Scheme.{u}} {A : Set Y} (U : Y.Opens)
    {y : Y} (hy : y ∈ U) (h : A ∩ U = (∅ : Set Y) ∩ U) :
    y ∉ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A)).support := by
  intro hyA
  have := (vanishingIdeal_closure_local U hy h).1 hyA
  rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
    closure_empty] at this
  exact this

/-- Coordinates at `y` adapted to a family `F` give coordinates adapted to a family `G` each of
whose members through `y` has the stalk at `y` of a member of `F` through `y`, distinct members
of `G` through `y` going to distinct members of `F`. -/
private theorem coords_of_coords_comp {Y : Scheme.{u}} {Λ Λ' : Type*}
    (F : Λ → Y.IdealSheafData) (G : Λ' → Y.IdealSheafData) (y : Y) (σ : Λ' → Λ)
    (hmem : ∀ i, y ∈ (G i).support → y ∈ (F (σ i)).support ∧
      IdealSheafData.stalk (G i) y = IdealSheafData.stalk (F (σ i)) y)
    (hinj : ∀ i j, y ∈ (G i).support → y ∈ (G j).support → σ i = σ j → i = j)
    (h : ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y) (c : {i // y ∈ (F i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (F i.1) y = Ideal.span {z (c i)}) ∧ Function.Injective c) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y) (c : {i // y ∈ (G i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (G i.1) y = Ideal.span {z (c i)}) ∧ Function.Injective c := by
  obtain ⟨n, z, c, hz, hc, hci⟩ := h
  exact ⟨n, z, fun i => c ⟨σ i.1, (hmem i.1 i.2).1⟩, hz,
    fun i => (hmem i.1 i.2).2.trans (hc ⟨σ i.1, (hmem i.1 i.2).1⟩),
    fun i j hij => Subtype.ext (hinj i.1 j.1 i.2 j.2 (congrArg Subtype.val (hci hij)))⟩

/-- The reindexing used in `isOrderedSNC_consTail_blowUp`, read on values, is injective on
`[0, d + 2)` provided it never meets `0` twice. -/
private theorem eq_of_reindex_eq (P : Prop) [Decidable P] {d i j : ℕ} (hi : i < d + 2)
    (hj : j < d + 2) (hP : P → i ≠ 0 ∧ j ≠ 0)
    (h : (if i = 0 then 0 else if i ≤ d then i else if P then 0 else d + 1) =
      if j = 0 then 0 else if j ≤ d then j else if P then 0 else d + 1) : i = j := by
  by_cases hp : P
  · have := hP hp
    split_ifs at h <;> omega
  · split_ifs at h <;> omega

/-- The reindexing used in `isOrderedSNC_consTail_blowUp`: `0` goes to `0`, the members of index
`< d` of the tail move up by one, and the others go to `0` or to the last member according to
`P`. -/
private def reindex (d e : ℕ) (P : Prop) [Decidable P] : Fin (e + 1) → Fin (d + 1 + 1) :=
  Fin.cases (Fin.castSucc 0) fun i => if h : (i : ℕ) < d then
    Fin.castSucc (Fin.succ ⟨i, h⟩) else if P then Fin.castSucc 0 else Fin.last _

private theorem reindex_zero (d e : ℕ) (P : Prop) [Decidable P] :
    reindex d e P 0 = Fin.castSucc 0 := rfl

private theorem reindex_succ_of_lt {d e : ℕ} (P : Prop) [Decidable P] {i : Fin e}
    (h : (i : ℕ) < d) : reindex d e P i.succ = Fin.castSucc (Fin.succ ⟨i, h⟩) :=
  dif_pos h

private theorem reindex_succ_of_not_lt {d e : ℕ} (P : Prop) [Decidable P] {i : Fin e}
    (h : ¬ (i : ℕ) < d) :
    reindex d e P i.succ = if P then Fin.castSucc 0 else Fin.last _ :=
  dif_neg h

private theorem reindex_val (d e : ℕ) (P : Prop) [Decidable P] (i : Fin (e + 1)) :
    ((reindex d e P i : ℕ) =
      if (i : ℕ) = 0 then 0 else if (i : ℕ) ≤ d then (i : ℕ) else if P then 0 else d + 1) := by
  refine Fin.cases rfl (fun i' => ?_) i
  by_cases h : (i' : ℕ) < d
  · rw [reindex_succ_of_lt P h]
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  · rw [reindex_succ_of_not_lt P h]
    have h₁ : ((i'.succ : Fin _) : ℕ) ≠ 0 := by simp
    have h₂ : ¬ ((i'.succ : Fin _) : ℕ) ≤ d := by
      simp only [Fin.val_succ]
      omega
    rw [ite_eq_right h₁, ite_eq_right h₂]
    by_cases hP : P
    · rw [ite_eq_left hP, ite_eq_left hP]
      rfl
    · rw [ite_eq_right hP, ite_eq_right hP]
      rfl

private theorem reindex_injective {d e : ℕ} (he : e ≤ d + 1) (P : Prop) [Decidable P]
    {i j : Fin (e + 1)} (hP : P → (i : ℕ) ≠ 0 ∧ (j : ℕ) ≠ 0)
    (h : reindex d e P i = reindex d e P j) : i = j := by
  have hval := congrArg Fin.val h
  rw [reindex_val, reindex_val] at hval
  have hi := i.isLt
  have hj := j.isLt
  exact Fin.ext (eq_of_reindex_eq P (by omega) (by omega) hP hval)

/-- Coordinates at `y` for `F = (F₀, D, L)` give coordinates for `G = (G₀, D, L')` when, near
`y`, the first member `G₀` is empty and the last member `L'` is empty or agrees with `F₀`. -/
private theorem coords_reindex_true {Y : Scheme.{u}} {d e : ℕ} (he : e ≤ d + 1)
    (F : Fin (d + 1 + 1) → Y.IdealSheafData) (G : Fin (e + 1) → Y.IdealSheafData) {y : Y}
    {A₀ A₁ A₂ : Set Y} (U : Y.Opens) (hyU : y ∈ U)
    (hG0 : G 0 = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A₀))
    (hF0 : F (Fin.castSucc 0) = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A₁))
    (hGD : ∀ (i : Fin e) (h : (i : ℕ) < d), G i.succ = F (Fin.castSucc (Fin.succ ⟨i, h⟩)))
    (hGL : ∀ i : Fin e, ¬ (i : ℕ) < d →
      G i.succ = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A₂))
    (hA₀ : A₀ ∩ U = (∅ : Set Y) ∩ U) (hA₂ : A₂ ∩ U = (∅ : Set Y) ∩ U ∨ A₂ ∩ U = A₁ ∩ U)
    (hF : ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y) (c : {i // y ∈ (F i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (F i.1) y = Ideal.span {z (c i)}) ∧ Function.Injective c) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y) (c : {i // y ∈ (G i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (G i.1) y = Ideal.span {z (c i)}) ∧ Function.Injective c := by
  have h₀ : y ∉ (G 0).support := by
    rw [hG0]
    exact notMem_support_vanishingIdeal_closure U hyU hA₀
  refine coords_of_coords_comp F G y (reindex d e True) (fun i => ?_)
    (fun i j hi hj hij => ?_) hF
  · refine Fin.cases (fun hy => absurd hy h₀) (fun i' hy => ?_) i
    by_cases h : (i' : ℕ) < d
    · rw [reindex_succ_of_lt _ h, ← hGD i' h]
      exact ⟨hy, rfl⟩
    · rw [reindex_succ_of_not_lt _ h, if_pos trivial, hF0]
      rw [hGL i' h] at hy ⊢
      rcases hA₂ with hA₂ | hA₂
      · exact absurd hy (notMem_support_vanishingIdeal_closure U hyU hA₂)
      · exact ⟨(vanishingIdeal_closure_local U hyU hA₂).1 hy,
          (vanishingIdeal_closure_local U hyU hA₂).2⟩
  · have hi₀ : (i : ℕ) ≠ 0 := fun h => h₀ (by obtain rfl : i = 0 := Fin.ext h; exact hi)
    have hj₀ : (j : ℕ) ≠ 0 := fun h => h₀ (by obtain rfl : j = 0 := Fin.ext h; exact hj)
    exact reindex_injective he True (fun _ => ⟨hi₀, hj₀⟩) hij

/-- Coordinates at `y` for `F = (F₀, D, L)` give coordinates for `G = (G₀, D, L')` when, near
`y`, the first member `G₀` agrees with `F₀` and the last member `L'` agrees with `L`. -/
private theorem coords_reindex_false {Y : Scheme.{u}} {d e : ℕ} (he : e ≤ d + 1)
    (F : Fin (d + 1 + 1) → Y.IdealSheafData) (G : Fin (e + 1) → Y.IdealSheafData) {y : Y}
    {A₀ A₁ A₂ A₃ : Set Y} (U : Y.Opens) (hyU : y ∈ U)
    (hG0 : G 0 = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A₀))
    (hF0 : F (Fin.castSucc 0) = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A₁))
    (hFL : F (Fin.last _) = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A₃))
    (hGD : ∀ (i : Fin e) (h : (i : ℕ) < d), G i.succ = F (Fin.castSucc (Fin.succ ⟨i, h⟩)))
    (hGL : ∀ i : Fin e, ¬ (i : ℕ) < d →
      G i.succ = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure A₂))
    (hA₀ : A₀ ∩ U = A₁ ∩ U) (hA₂ : A₂ ∩ U = A₃ ∩ U)
    (hF : ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y) (c : {i // y ∈ (F i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (F i.1) y = Ideal.span {z (c i)}) ∧ Function.Injective c) :
    ∃ (n : ℕ) (z : Fin n → Y.presheaf.stalk y) (c : {i // y ∈ (G i).support} → Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧
        (∀ i, IdealSheafData.stalk (G i.1) y = Ideal.span {z (c i)}) ∧ Function.Injective c := by
  refine coords_of_coords_comp F G y (reindex d e False) (fun i => ?_)
    (fun i j _ _ hij => reindex_injective he False (fun h => h.elim) hij) hF
  refine Fin.cases (fun hy => ?_) (fun i' hy => ?_) i
  · rw [reindex_zero, hF0]
    rw [hG0] at hy ⊢
    exact ⟨(vanishingIdeal_closure_local U hyU hA₀).1 hy,
      (vanishingIdeal_closure_local U hyU hA₀).2⟩
  · by_cases h : (i' : ℕ) < d
    · rw [reindex_succ_of_lt _ h, ← hGD i' h]
      exact ⟨hy, rfl⟩
    · rw [reindex_succ_of_not_lt _ h, if_neg not_false, hFL]
      rw [hGL i' h] at hy ⊢
      exact ⟨(vanishingIdeal_closure_local U hyU hA₂).1 hy,
        (vanishingIdeal_closure_local U hyU hA₂).2⟩

/-- The members of index `≥ s₀` of the total transform of `E` which come from members of `E` are
the members of the total transform of `(H, E^{s₀+1}, …, E^s)` other than the first. -/
private theorem totalTransform_eq_totalTransform_consTail {X : Scheme.{u}}
    (H : X.IdealSheafData) (E : OrderedDivisor X) (s₀ : ℕ) (Z : X.IdealSheafData)
    (i : Fin ((E.totalTransform Z).s - s₀)) (h : (i : ℕ) < E.s - s₀) :
    (E.totalTransform Z).E ⟨s₀ + i, by have := i.isLt; omega⟩ =
      ((consTail H E s₀).totalTransform Z).E (Fin.castSucc (Fin.succ ⟨i, h⟩)) := by
  have e : (⟨s₀ + i, by have := i.isLt; omega⟩ : Fin (E.totalTransform Z).s) =
      Fin.castSucc (⟨s₀ + i, by omega⟩ : Fin E.s) := rfl
  rw [e]
  simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc]
  rfl

/-- The member of index `≥ s₀` of the total transform of `E` which does not come from `E` is the
last one. -/
private theorem totalTransform_eq_of_not_lt {X : Scheme.{u}} (E : OrderedDivisor X) (s₀ : ℕ)
    (Z : X.IdealSheafData) (i : Fin ((E.totalTransform Z).s - s₀)) (h : ¬ (i : ℕ) < E.s - s₀) :
    (E.totalTransform Z).E ⟨s₀ + i, by have := i.isLt; omega⟩ =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X)) (_ : W ∉ componentsOf E.support),
          blowUpToBase Z ⁻¹' W)) := by
  have hi := i.isLt
  have hs : (E.totalTransform Z).s = E.s + 1 := rfl
  have e : (⟨s₀ + i, by omega⟩ : Fin (E.totalTransform Z).s) = Fin.last E.s :=
    Fin.ext (by simp only [Fin.val_last]; omega)
  rw [e]
  simp only [OrderedDivisor.totalTransform, Fin.snoc_last]

/-- A point of `S` off every component of `S` other than `W₁` lies on `W₁`. -/
private theorem mem_of_notMem_sUnion_componentsOf {T : Type*} [TopologicalSpace T]
    {S W₁ : Set T} {x : T} (hx : x ∈ S) (h : x ∉ ⋃₀ {C | C ∈ componentsOf S ∧ C ≠ W₁}) :
    x ∈ W₁ := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_componentsOf hx
  by_contra hxW
  exact h ⟨C, ⟨hC, fun h => hxW (h ▸ hxC)⟩, hxC⟩

/-- For `Z ⊆ H` with `H` of pure codimension one, the components of `Z` of codimension `≥ 2`
are those which are not components of `H`. -/
private theorem mem_componentsOfCodimAtLeastTwo_iff {X : Scheme.{u}} [IsNoetherian X]
    {H Z : X.IdealSheafData} (hH : MMP.Mori.IsPureCodimOne H.support)
    (hZH : (Z.support : Set X) ⊆ H.support) (x : X) :
    x ∈ componentsOfCodimAtLeastTwo (Z.support : Set X) ↔
      ∃ W ∈ componentsOf (Z.support : Set X), W ∉ componentsOf (H.support : Set X) ∧ x ∈ W := by
  have hHp : ∀ i, MMP.Mori.IsPureCodimOne
      ((⟨1, fun _ => H⟩ : OrderedDivisor X).E i).support := fun _ => hH
  have hHsupp : (⟨1, fun _ => H⟩ : OrderedDivisor X).support = (H.support : Set X) := by
    change (⋃ _ : Fin 1, (H.support : Set X)) = _
    exact Set.iUnion_const _
  rw [mem_componentsOfCodimAtLeastTwo]
  constructor
  · rintro ⟨W, hW, h2, hx⟩
    refine ⟨W, hW, fun hWH => ?_, hx⟩
    rw [← hHsupp] at hWH
    exact OrderedDivisor.not_two_le_codimension_of_mem_componentsOf _ hHp hWH h2
  · rintro ⟨W, hW, hWH, hx⟩
    exact ⟨W, hW, two_le_codimension_of_mem_componentsOf hH hZH hW hWH, hx⟩

/-- Near a point of `B_ZX` over a component `W₁` of `Z` which is a component of `H`, the
transform of `H` is empty, and the transform of the components of `Z` off `E` is empty or
agrees with the transform of `H` off the components of `Z` of codimension `≥ 2`. -/
private theorem exists_opens_of_mem_componentsOf_inter {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX] [IsNoetherian X]
    (E : OrderedDivisor X) (H : X.IdealSheafData) (hH : IsSmoothHypersurface sX H)
    (Z : X.IdealSheafData) (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX))
    (hZH : (Z.support : Set X) ⊆ H.support) {W₁ : Set X}
    (hW₁Z : W₁ ∈ componentsOf (Z.support : Set X)) (hW₁H : W₁ ∈ componentsOf (H.support : Set X))
    {y : blowUp Z} (hyW₁ : blowUpToBase Z y ∈ W₁) :
    ∃ U : (blowUp Z).Opens, y ∈ U ∧
      blowUpToBase Z ⁻¹' ((H.support : Set X) \ (Z.support : Set X)) ∩ U =
        (∅ : Set (blowUp Z)) ∩ U ∧
      ((⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W) ∩ U =
          (∅ : Set (blowUp Z)) ∩ U ∨
        (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W) ∩ U =
          blowUpToBase Z ⁻¹' ((H.support : Set X) \
            componentsOfCodimAtLeastTwo (Z.support : Set X)) ∩ U) := by
  set R : Set X := ⋃₀ {C | C ∈ componentsOf (H.support : Set X) ∧ C ≠ W₁} ∪
    ⋃₀ {W | W ∈ componentsOf (Z.support : Set X) ∧ W ≠ W₁} with hRdef
  have hRc : IsClosed R :=
    (Aux.isClosed_sUnion_of_subset_componentsOf sX H _ fun C hC => hC.1).union
      (Aux.isClosed_sUnion_of_subset_componentsOf sX Z _ fun C hC => hC.1)
  have hyR : blowUpToBase Z y ∉ R := by
    rintro (⟨C, ⟨hC, hne⟩, hyC⟩ | ⟨C, ⟨hC, hne⟩, hyC⟩)
    · exact hne (Aux.eq_of_mem_componentsOf_of_isSmoothScheme sX H hH.1 hC hW₁H hyC hyW₁)
    · exact hne (Aux.eq_of_mem_componentsOf_of_isSmoothScheme sX Z hZ hC hW₁Z hyC hyW₁)
  have f₁ : ∀ x ∈ (H.support : Set X), x ∉ R → x ∈ W₁ := fun x hx hxR =>
    mem_of_notMem_sUnion_componentsOf hx fun h => hxR (Or.inl h)
  have f₂ : ∀ x ∈ (Z.support : Set X), x ∉ R → x ∈ W₁ := fun x hx hxR =>
    mem_of_notMem_sUnion_componentsOf hx fun h => hxR (Or.inr h)
  have f₃ : ∀ x ∉ R, x ∉ componentsOfCodimAtLeastTwo (Z.support : Set X) := by
    intro x hxR hx2
    obtain ⟨W, hW, hWH, hxW⟩ := (mem_componentsOfCodimAtLeastTwo_iff hH.2 hZH x).1 hx2
    exact hxR (Or.inr ⟨W, ⟨hW, fun h => hWH (h ▸ hW₁H)⟩, hxW⟩)
  refine ⟨blowUpToBase Z ⁻¹ᵁ (⟨Rᶜ, hRc.isOpen_compl⟩ : X.Opens), hyR, ?_, ?_⟩
  · ext y'
    simp only [Set.empty_inter, Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff,
      not_and, Set.mem_preimage, Set.mem_sdiff]
    rintro ⟨hH', hZ'⟩ hU'
    exact hZ' (hW₁Z.1.2 (f₁ _ hH' hU'))
  by_cases hW₁E : W₁ ∈ componentsOf E.support
  · left
    ext y'
    simp only [Set.empty_inter, Set.mem_empty_iff_false, iff_false, Set.mem_inter_iff,
      not_and, Set.mem_iUnion, Set.mem_preimage]
    rintro ⟨W, hW, hWE, hy'W⟩ hU'
    have hWW : W = W₁ := Aux.eq_of_mem_componentsOf_of_isSmoothScheme sX Z hZ hW hW₁Z hy'W
      (f₂ _ (hW.1.2 hy'W) hU')
    exact hWE (hWW ▸ hW₁E)
  · right
    ext y'
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨W, hW, -, hy'W⟩, hU'⟩
      exact ⟨⟨hW₁H.1.2 (f₂ _ (hW.1.2 hy'W) hU'), f₃ _ hU'⟩, hU'⟩
    · rintro ⟨⟨hH', -⟩, hU'⟩
      exact ⟨⟨W₁, hW₁Z, hW₁E, f₁ _ hH' hU'⟩, hU'⟩

/-- Off the components of `Z ⊆ H` which are components of `H`, the preimage of a component of `Z`
lies in a member of the total transform of a divisor `F` of pure codimension one exactly when it
is not a component of `H`. -/
private theorem mem_iUnion_preimage_componentsOf_iff {X : Scheme.{u}} [IsNoetherian X]
    {H Z : X.IdealSheafData} (hH : MMP.Mori.IsPureCodimOne H.support)
    (hZH : (Z.support : Set X) ⊆ H.support) (F : OrderedDivisor X)
    (hF : ∀ i, MMP.Mori.IsPureCodimOne (F.E i).support) {y : blowUp Z}
    (hy : blowUpToBase Z y ∉ ⋃₀ {W | W ∈ componentsOf (Z.support : Set X) ∧
      W ∈ componentsOf (H.support : Set X)}) :
    y ∈ (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf F.support), blowUpToBase Z ⁻¹' W) ↔
      ∃ W ∈ componentsOf (Z.support : Set X), W ∉ componentsOf (H.support : Set X) ∧
        blowUpToBase Z y ∈ W := by
  simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]
  constructor
  · rintro ⟨W, hW, -, hyW⟩
    exact ⟨W, hW, fun hWH => hy ⟨W, ⟨hW, hWH⟩, hyW⟩, hyW⟩
  · rintro ⟨W, hW, hWH, hyW⟩
    exact ⟨W, hW, fun hWF => F.not_two_le_codimension_of_mem_componentsOf hF hWF
      (two_le_codimension_of_mem_componentsOf hH hZH hW hWH), hyW⟩

/-- Near a point of `B_ZX` off the components of `Z ⊆ H` which are components of `H`, the
transform of `H` agrees with the transform of `H` off the components of `Z` of codimension
`≥ 2`, and the last members of the total transforms of any two divisors of pure codimension one
agree. -/
private theorem exists_opens_of_notMem_sUnion_componentsOf_inter {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    [IsNoetherian X] {H Z : X.IdealSheafData} (hH : MMP.Mori.IsPureCodimOne H.support)
    (hZH : (Z.support : Set X) ⊆ H.support) (F₁ F₂ : OrderedDivisor X)
    (h₁ : ∀ i, MMP.Mori.IsPureCodimOne (F₁.E i).support)
    (h₂ : ∀ i, MMP.Mori.IsPureCodimOne (F₂.E i).support) {y : blowUp Z}
    (hy : blowUpToBase Z y ∉ ⋃₀ {W | W ∈ componentsOf (Z.support : Set X) ∧
      W ∈ componentsOf (H.support : Set X)}) :
    ∃ U : (blowUp Z).Opens, y ∈ U ∧
      blowUpToBase Z ⁻¹' ((H.support : Set X) \ (Z.support : Set X)) ∩ U =
        blowUpToBase Z ⁻¹' ((H.support : Set X) \
          componentsOfCodimAtLeastTwo (Z.support : Set X)) ∩ U ∧
      (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf F₁.support), blowUpToBase Z ⁻¹' W) ∩ U =
        (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf F₂.support), blowUpToBase Z ⁻¹' W) ∩ U := by
  have hZ1c : IsClosed (⋃₀ {W | W ∈ componentsOf (Z.support : Set X) ∧
      W ∈ componentsOf (H.support : Set X)}) :=
    Aux.isClosed_sUnion_of_subset_componentsOf sX Z _ fun W hW => hW.1
  refine ⟨blowUpToBase Z ⁻¹ᵁ (⟨_, hZ1c.isOpen_compl⟩ : X.Opens), hy, ?_, ?_⟩
  · ext y'
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff]
    constructor
    · rintro ⟨⟨hH', hZ'⟩, hU'⟩
      refine ⟨⟨hH', fun h => hZ' ?_⟩, hU'⟩
      obtain ⟨W, hW, -, hxW⟩ := (mem_componentsOfCodimAtLeastTwo_iff hH hZH _).1 h
      exact hW.1.2 hxW
    · rintro ⟨⟨hH', h2⟩, hU'⟩
      refine ⟨⟨hH', fun hZ' => ?_⟩, hU'⟩
      obtain ⟨W, hW, hxW⟩ := exists_mem_componentsOf hZ'
      by_cases hWH : W ∈ componentsOf (H.support : Set X)
      · exact hU' ⟨W, ⟨hW, hWH⟩, hxW⟩
      · exact h2 ((mem_componentsOfCodimAtLeastTwo_iff hH hZH _).2 ⟨W, hW, hWH, hxW⟩)
  · ext y'
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨h, hU'⟩
      exact ⟨(mem_iUnion_preimage_componentsOf_iff hH hZH F₂ h₂ hU').2
        ((mem_iUnion_preimage_componentsOf_iff hH hZH F₁ h₁ hU').1 h), hU'⟩
    · rintro ⟨h, hU'⟩
      exact ⟨(mem_iUnion_preimage_componentsOf_iff hH hZH F₁ h₁ hU').2
        ((mem_iUnion_preimage_componentsOf_iff hH hZH F₂ h₂ hU').1 h), hU'⟩

/-! ### One blow-up -/

/-- **One blow-up inside the hypersurface.** Let `X` be smooth over `k`, `E` an ordered snc
divisor, `H` a smooth hypersurface with `(H, E^{s₀+1}, …, E^s)` ordered snc, and `Z ⊆ H` a smooth
centre having snc with `E`. Then the birational transform of `H` together with the members of
index `≥ s₀` of the total transform of `E` is ordered snc on `B_ZX`.

The total transform of `(H, E^{s₀+1}, …, E^s)` itself is ordered snc. It differs from the divisor
in question only along the components `W` of `Z` which are components of `H`: there the
transform of `H` loses `π⁻¹W`, which the last member of the total transform of `E` may gain.
Since the components of the smooth `H` and `Z` are disjoint, near `π⁻¹W` both divisors are cut
out by the same coordinates. -/
private theorem isOrderedSNC_consTail_blowUp {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] [QuasiCompact sX]
    (E : OrderedDivisor X) (hE : E.IsOrderedSNC sX)
    (H : X.IdealSheafData) (hH : IsSmoothHypersurface sX H) (s₀ : ℕ)
    (hHD : (consTail H E s₀).IsOrderedSNC sX) (Z : X.IdealSheafData)
    (hZ : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ sX)) (hZE : HasSNCWith E.E Z)
    (hHZ : H ≤ Z) :
    (consTail (canonicalLift H.subschemeι Z).ker (E.totalTransform Z) s₀).IsOrderedSNC
      (blowUpToBase Z ≫ sX) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  let D : OrderedDivisor X := ⟨E.s - s₀, fun i => E.E ⟨s₀ + i, by have := i.isLt; omega⟩⟩
  have hZD : HasSNCWith D.E Z :=
    hasSNCWith_comp hZE (σ := fun i : Fin (E.s - s₀) => (⟨s₀ + i, by omega⟩ : Fin E.s))
      (fun i i' h => Fin.ext (by have := congrArg Fin.val h; simp at this; omega))
  have hGZ : HasSNCWith (consTail H E s₀).E Z :=
    Kollar.hasSNCWith_cons_of_hasSNCWith sX D H hHD.2 Z hHZ hZD
  have hT := isOrderedSNC_totalTransform sX hHD.2 hGZ
  have hHred : IsReduced H.subscheme := (hHD.1 0).1
  have hZH : (Z.support : Set X) ⊆ H.support := Scheme.IdealSheafData.support_antitone hHZ
  have he : (E.totalTransform Z).s - s₀ ≤ E.s - s₀ + 1 := by
    change E.s + 1 - s₀ ≤ _
    omega
  have hGt0 : ((consTail H E s₀).totalTransform Z).E (Fin.castSucc 0) =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (blowUpToBase Z ⁻¹'
        ((H.support : Set X) \ componentsOfCodimAtLeastTwo (Z.support : Set X)))) := by
    simp only [OrderedDivisor.totalTransform, Fin.snoc_castSucc]
    rfl
  have hGtL : ((consTail H E s₀).totalTransform Z).E (Fin.last _) =
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf (consTail H E s₀).support), blowUpToBase Z ⁻¹' W)) := by
    simp only [OrderedDivisor.totalTransform, Fin.snoc_last]
  have hT0 := ker_restrictHom_cons_nil_eq_vanishingIdeal H Z
  refine isOrderedSNC_of_coords (blowUpToBase Z ≫ sX) _ fun y => ?_
  by_cases hyZ1 : blowUpToBase Z y ∈ ⋃₀ {W | W ∈ componentsOf (Z.support : Set X) ∧
    W ∈ componentsOf (H.support : Set X)}
  · obtain ⟨W₁, ⟨hW₁Z, hW₁H⟩, hyW₁⟩ := hyZ1
    obtain ⟨U, hyU, hA0, hAE⟩ :=
      exists_opens_of_mem_componentsOf_inter sX E H hH Z hZ hZH hW₁Z hW₁H hyW₁
    exact coords_reindex_true he _ _ U hyU hT0 hGt0
      (totalTransform_eq_totalTransform_consTail H E s₀ Z) (totalTransform_eq_of_not_lt E s₀ Z)
      hA0 hAE (hT.2.2 y)
  · obtain ⟨U, hyU, hA0, hAE⟩ := exists_opens_of_notMem_sUnion_componentsOf_inter sX hH.2 hZH
      E (consTail H E s₀) (fun i => (hE.2.1 i).2.1) (fun i => (hHD.2.1 i).2.1) hyZ1
    exact coords_reindex_false he _ _ U hyU hT0 hGt0 hGtL
      (totalTransform_eq_totalTransform_consTail H E s₀ Z) (totalTransform_eq_of_not_lt E s₀ Z)
      hA0 hAE (hT.2.2 y)

/-! ### The induction along the sequence -/

/-- Along a smooth blow-up sequence of order `m` starting with `(X, I, E)` which is also of
order `≥ 1` for a marked ideal `(b, 1)` containing the hypersurface `ker j`, the transform of
`ker j` together with the members of index `≥ s₀` of the total transform of `E` stays ordered
snc. -/
private theorem isOrderedSNC_consTail_pullbackHom {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k)) (b : MarkedIdeal X)
    (hb : b.m = 1) (hB₁ : IsOrderGePlainSeq sX b B) (I : X.IdealSheafData)
    (E : OrderedDivisor X) (m : ℕ) (hBE : B.IsOrderMTripleSeq sX I E m)
    {S : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (hH : IsSmoothHypersurface sX j.ker) (hle : j.ker ≤ b.I) (s₀ : ℕ)
    (hHD : (consTail j.ker E s₀).IsOrderedSNC sX) :
    (consTail (B.pullbackHom j).ker (B.orderedTotalTransform E) s₀).IsOrderedSNC
      (B.toBase ≫ sX) := by
  induction B generalizing S with
  | nil X =>
    change (consTail j.ker E s₀).IsOrderedSNC (𝟙 X ≫ sX)
    rwa [Category.id_comp]
  | cons Z₀ B'' ih =>
    obtain ⟨hX, -, hZ₀, hcodim, hord, hB''⟩ := hB₁
    obtain ⟨hT, -, -, hZE, -, hBE''⟩ := hBE
    obtain ⟨-, -, hlft, hqc, -, -, hE⟩ := hT
    have := hlft; have := hqc
    have hK : j.ker ≤ Z₀ := le_of_le_of_orderAlongGE_one sX hX Z₀ hZ₀ hle (hb ▸ hord)
    have hlift := MMP.Resolution.ker_canonicalLift_subschemeι_mul_comap_eq_comap sX hX j.ker Z₀
      hH hZ₀ hK
    have : IsClosedImmersion (canonicalLift j Z₀) :=
      MMP.Resolution.Bridges.isClosedImmersion_canonicalLift j Z₀
    have hbt := MarkedIdeal.birationalTransform_mul_eq sX hX Z₀ hZ₀ hcodim b hord
    rw [hb, pow_one] at hbt
    have h := ih _ (b.birationalTransform Z₀) hb hB'' _ _ hBE'' (canonicalLift j Z₀)
      (by rw [ker_canonicalLift_eq]; exact hlift.2.2)
      (le_of_mul_le_mul_of_isEffectiveCartierDivisor
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal Z₀)
        (by rw [hbt, ker_canonicalLift_eq, hlift.2.1]
            exact Scheme.IdealSheafData.comap_mono _ hle))
      (by
        rw [ker_canonicalLift_eq]
        exact isOrderedSNC_consTail_blowUp sX E hE j.ker hH s₀ hHD Z₀ hZ₀ hZE hK)
    change (consTail (B''.pullbackHom (canonicalLift j Z₀)).ker
      (B''.orderedTotalTransform (E.totalTransform Z₀)) s₀).IsOrderedSNC
        ((B''.toBase ≫ blowUpToBase Z₀) ≫ sX)
    rw [Category.assoc]
    exact h

open MMP.Flips.ResolutionInputs in
/-- At a point of a smooth hypersurface `H` of a smooth scheme, the stalk of `H` is generated by
one member of a regular system of parameters. -/
private theorem exists_parameter_of_isSmoothHypersurface {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (hX : MMP.Mori.IsSmoothScheme sX) (H : X.IdealSheafData) (hH : IsSmoothHypersurface sX H)
    {x : X} (hx : x ∈ H.support) :
    ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (a : Fin n),
      MMP.Mori.IsRegularSystemOfParameters z ∧ IdealSheafData.stalk H x = Ideal.span {z a} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : Smooth sX := hX.smooth
  have hreg := isRegularLocalRing_quotient_stalk sX H hH.1 hx
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    (smooth_iff_forall_isRegularLocalRing_stalk sX).mp inferInstance x
  have : IsDomain (X.presheaf.stalk x ⧸ IdealSheafData.stalk H x) :=
    IsRegularLocalRing.isDomain _
  have : (IdealSheafData.stalk H x).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp this
  have hht := height_stalk_eq_one_of_isPureCodimOne H hH.2 (x := x)
  have hIdim := ringKrullDim_quotient_add_one_of_height_eq_one _ hht
  have hJdim := (IsRegularLocalRing.spanFinrank_maximalIdeal
    (R := X.presheaf.stalk x ⧸ IdealSheafData.stalk H x)).symm
  set m := Submodule.spanFinrank
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x ⧸ IdealSheafData.stalk H x))
  have hR : ringKrullDim (X.presheaf.stalk x) = ((1 + m : ℕ) : WithBot ℕ∞) := by
    rw [← hIdim, hJdim, add_comm]; push_cast; rfl
  obtain ⟨y, z, hz, -, hI⟩ :=
    exists_flag_isRegularSystemOfParameters le_rfl hreg hIdim hreg le_rfl hR hJdim
  exact ⟨1 + m, Fin.append y z, Fin.castAdd m 0, hz, by rw [hI, Fin.append_left]; rfl⟩

/-- A smooth hypersurface is, on its own, an ordered snc divisor. -/
private theorem isOrderedSNC_single {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (hX : MMP.Mori.IsSmoothScheme sX)
    (H : X.IdealSheafData) (hH : IsSmoothHypersurface sX H) (E : OrderedDivisor X) :
    (consTail H E E.s).IsOrderedSNC sX := by
  have hDE : ∀ i, (consTail H E E.s).E i = H := by
    intro i
    refine Fin.cases rfl (fun i => ?_) i
    exact absurd i.isLt (by omega)
  refine isOrderedSNC_of_coords sX _ fun y => ?_
  by_cases hy : y ∈ H.support
  · obtain ⟨n, z, a, hz, hza⟩ := exists_parameter_of_isSmoothHypersurface sX hX H hH hy
    refine ⟨n, z, fun _ => a, hz, fun i => by rw [hDE]; exact hza, fun i i' _ => ?_⟩
    have h1 := i.1.isLt; have h2 := i'.1.isLt
    exact Subtype.ext (Fin.ext (by simp only [consTail] at h1 h2; omega))
  · have : Smooth sX := hX.smooth
    have : IsRegularLocalRing (X.presheaf.stalk y) :=
      (MMP.Flips.ResolutionInputs.smooth_iff_forall_isRegularLocalRing_stalk sX).mp
        inferInstance y
    obtain ⟨n, z, hz⟩ := MMP.Mori.exists_isRegularSystemOfParameters (X.presheaf.stalk y)
    have hem : IsEmpty {i // y ∈ ((consTail H E E.s).E i).support} :=
      ⟨fun i => hy (hDE i.1 ▸ i.2)⟩
    exact ⟨n, z, isEmptyElim, hz, isEmptyElim, isEmptyElim⟩

/-- **Kollár 3.104, Step 2.1.`s`.** Let `𝓜` be a marked order-reduction family on dimensions
`0, …, N - 1`, `(X, I, E)` a triple of dimension `n` with `1 ≤ n ≤ N`, `m ≥ 1` with
`maxord I = m`, and `H` an MC-hypersurface for `I` (`IsMCHypersurface`). Let `B` be the divisor
separation sequence `divisorSeparationSequence M m (X, I, E)` and `(X', I', E')` its end. Then
`E'` has at least as many members as `E`, and the ordered divisor whose first member is the
birational transform `ker (B.restrictHom H)` of `H` and whose remaining members are the members
of `E'` of index at least the length of `E` is an ordered snc divisor on `X'`. -/
@[mmp "lem_kr3e_divisor_separation_snc"]
public theorem isOrderedSNC_divisorSeparationSequence {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H : t.X.IdealSheafData}
    (hH : IsMCHypersurface t.sX t.I H) :
    let B := divisorSeparationSequence M m t
    let tr := t.endOf B
    t.E.s ≤ tr.E.s ∧
      OrderedDivisor.IsOrderedSNC tr.sX
        (⟨tr.E.s - t.E.s + 1, Fin.cons (α := fun _ => tr.X.IdealSheafData) (B.restrictHom H).ker
          fun i => tr.E.E ⟨t.E.s + i, by have := i.isLt; omega⟩⟩ : OrderedDivisor tr.X) := by
  intro B tr
  have hs : t.E.s ≤ tr.E.s := by
    change t.E.s ≤ (B.orderedTotalTransform t.E).s
    rw [orderedTotalTransform_s]; omega
  refine ⟨hs, ?_⟩
  change (consTail (B.restrictHom H).ker tr.E t.E.s).IsOrderedSNC tr.sX
  have hB : B.IsOrderMTripleSeq t.sX t.I t.E m :=
    divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le
  have hT : IsTriple t.sX t.I t.E := ht
  obtain ⟨hchar, hX, hlft, hqc, hequi, hnz, -⟩ := id hT
  have := hchar; have := hlft; have := hqc
  have hdim1 : 1 ≤ topologicalKrullDim t.X := by
    rw [hdim]; exact_mod_cast hn
  have hdim' := pos_of_mem_irreducibleComponents hequi hdim1
  have hiff := isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq t.sX t.I t.E hT m hmax B
  have hplain : IsOrderGePlainSeq t.sX ⟨t.I, m⟩ B :=
    isOrderGePlainSeq_of_isOrderGeMarkedTripleSeq B t.sX _ t.E (hiff.1.2 hB)
  obtain ⟨hB₁, -⟩ := isOrderGePlainSeq_higherDerivativeIdeal t.sX hequi hdim' ⟨t.I, m⟩ hnz B
    hplain (m - 1) (Nat.sub_le _ _)
  exact isOrderedSNC_consTail_pullbackHom B t.sX
    ⟨higherDerivativeIdeal t.sX t.I (m - 1), m - (m - 1)⟩ (by change m - (m - 1) = 1; omega) hB₁
    t.I t.E m hB H.subschemeι (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hH.1)
    (by
      rw [Scheme.IdealSheafData.ker_subschemeι,
        ← maximalContactIdeal_eq_of_maxOrder_eq t.sX hmax]
      exact hH.2)
    t.E.s
    (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact isOrderedSNC_single t.sX hX H hH.1 t.E)

end SNC

end MMP.Resolution
