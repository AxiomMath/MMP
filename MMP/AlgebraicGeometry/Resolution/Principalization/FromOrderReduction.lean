module
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
public import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.OrderOnePullback

/-!
# Principalization from order reduction of marked ideals of order one

Let `𝓑𝓜𝓞_1` be a smooth blow-up sequence functor of order `≥ 1` on the marked triples
`(X, I, 1, E)` whose restriction to the marked triples of finite dimension is an order reduction
functor for marked ideals of order `1` (the last ideal has maximal order `< 1`, and the functor
commutes with smooth morphisms and with change of fields), which has the closed embedding
property of (3.71.2) and ignores empty entries of the ordered divisor. Then the construction
`𝓑𝓟_{𝓑𝓜𝓞_1}` of Kollár 3.72 (first make the divisor disjoint, then apply `𝓑𝓜𝓞_1`) is a
principalization functor away from the double locus `E^{(2)}` on the triples `(X, I, E)` of
3.64, that is, with `X` equidimensional: it has no empty blow-ups, it is a smooth blow-up
sequence whose centers have simple normal crossings with `E`, it pulls `I` back to a monomial
ideal, its centers lie over `cosupp I ∪ E^{(2)}`, it commutes with smooth morphisms and with
change of fields, and it commutes with closed embeddings for triples with `E = ∅`.

## Main results

* `MMP.Resolution.isPrincipalizationFunctorAwayFromDoubleLocus_principalizationConstruction`.

## Implementation notes

`MMP.Resolution.IsPrincipalizationFunctorAwayFromDoubleLocus` quantifies over all snc triples;
for `X` not equidimensional the pull-back of `I` to the end of the disjoining sequence is not a
marked triple, the construction is only the disjoining sequence, and (2) fails. The conclusion
is therefore the conjunction of the clauses (0)–(5) with every triple ranging over `triples`
(Kollár Notation 3.64), where `MMP.Resolution.principalizationConstructionOnTriples` is the
construction on that class.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.64, 3.69, 3.71, 3.72]
-/

open CategoryTheory AlgebraicGeometry

namespace MMP.Resolution

universe u

/-- On an empty scheme every ideal sheaf is the unit ideal. -/
private theorem idealSheafData_eq_top_of_isEmpty {X : Scheme.{u}} (hX : IsEmpty X)
    (Z : X.IdealSheafData) : Z = ⊤ := by
  ext U x
  have : Subsingleton Γ(X, U) := by
    have : (U : X.Opens) = ⊥ := Subsingleton.elim _ _
    rw [this]; infer_instance
  simp [Subsingleton.elim x 0]

/-- On an empty scheme a blow-up sequence without empty blow-ups has length `0`. -/
private theorem eq_nil_of_isEmpty {X : Scheme.{u}} (hX : IsEmpty X)
    (B : ClosedBlowupSequence X) (hB : B.HasNoEmptyBlowups) : B = .nil X := by
  cases B with
  | nil => rfl
  | cons Z B => exact absurd (idealSheafData_eq_top_of_isEmpty hX Z) hB.1

/-- A marked triple of marking `1` on a nonempty scheme has finite dimension. -/
private theorem mem_markedTriplesOfDim {t : MarkedTriple.{u}}
    (ht : t ∈ markedTriplesOfMarking 1) (hne : Nonempty t.X) :
    t ∈ markedTriplesOfDim Set.univ 1 := by
  refine ⟨ht.1, ht.2, ?_⟩
  obtain ⟨-, -, hlft, hqc, -⟩ := ht.1
  have : LocallyOfFiniteType t.sX := hlft
  have : QuasiCompact t.sX := hqc
  have : CompactSpace t.X := QuasiCompact.compactSpace_of_compactSpace t.sX
  have htop := topologicalKrullDim_ne_top_of_locallyOfFiniteType t.k t.sX
  obtain ⟨x⟩ := hne
  have : Nonempty (TopologicalSpace.IrreducibleCloseds t.X) :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hbot : topologicalKrullDim t.X ≠ ⊥ := Order.krullDim_ne_bot_iff.2 inferInstance
  generalize hd : topologicalKrullDim t.X = d at htop hbot
  induction d using WithBot.recBotCoe with
  | bot => exact absurd rfl hbot
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact absurd rfl htop
    | coe n => exact ⟨n, trivial, hd⟩

/-- An order reduction functor on the marked triples of finite dimension, extended to the marked
triples of marking `1`, commutes with smooth morphisms. -/
private theorem commutesWithSmoothOnMarked
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking 1))
    (hB : CommutesWithSmoothOnMarked (markedTriplesOfDim Set.univ 1)
      (fun t ht => B.toFun t ⟨ht.1, ht.2.1⟩)) :
    CommutesWithSmoothOnMarked _ B.toFun := by
  refine ⟨fun t ht Y h hsm hsurj hlft hqc hY => ?_, fun t ht Y h hsm hlft hqc hY => ?_⟩
  · by_cases hne : Nonempty Y
    · have hXne : Nonempty t.X := ⟨h hne.some⟩
      exact hB.1 t (mem_markedTriplesOfDim ht hXne) Y h hsm hsurj hlft hqc
        (mem_markedTriplesOfDim hY hne)
    · have hYe : IsEmpty Y := not_nonempty_iff.1 hne
      have hXe : IsEmpty t.X := ⟨fun x => hYe.elim (hsurj.surj x).choose⟩
      rw [eq_nil_of_isEmpty hYe _ (B.hasNoEmptyBlowups _ hY),
        eq_nil_of_isEmpty hXe _ (B.hasNoEmptyBlowups _ ht)]
      rfl
  · by_cases hne : Nonempty Y
    · have hXne : Nonempty t.X := ⟨h hne.some⟩
      exact hB.2 t (mem_markedTriplesOfDim ht hXne) Y h hsm hlft hqc
        (mem_markedTriplesOfDim hY hne)
    · have hYe : IsEmpty Y := not_nonempty_iff.1 hne
      exact (eq_nil_of_isEmpty hYe _ (B.hasNoEmptyBlowups _ hY)).trans
        (eq_nil_of_isEmpty hYe _ (ClosedBlowupSequence.hasNoEmptyBlowups_reduction _)).symm

/-- An order reduction functor on the marked triples of finite dimension, extended to the marked
triples of marking `1`, commutes with change of fields. -/
private theorem commutesWithFieldChangeOnMarked
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking 1))
    (hB : CommutesWithFieldChangeOnMarked (markedTriplesOfDim Set.univ 1)
      (fun t ht => B.toFun t ⟨ht.1, ht.2.1⟩)) :
    CommutesWithFieldChangeOnMarked _ B.toFun := by
  intro t ht L _ σ hL
  by_cases hne : Nonempty t.X
  · have hsurj : Surjective (t.toFieldBlowupTriple.fieldChangeProj σ) :=
      MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback _ _).flip
        inferInstance
    have hLne : Nonempty (t.fieldChange σ).X :=
      ⟨(hsurj.surj hne.some).choose⟩
    exact hB t (mem_markedTriplesOfDim ht hne) L σ (mem_markedTriplesOfDim hL hLne)
  · have hXe : IsEmpty t.X := not_nonempty_iff.1 hne
    have hLe : IsEmpty (t.fieldChange σ).X :=
      ⟨fun x => hXe.elim (t.toFieldBlowupTriple.fieldChangeProj σ x)⟩
    rw [eq_nil_of_isEmpty hLe _ (B.hasNoEmptyBlowups _ hL),
      eq_nil_of_isEmpty hXe _ (B.hasNoEmptyBlowups _ ht)]
    rfl

/-- An order reduction functor on the marked triples of finite dimension, extended to the marked
triples of marking `1`, reduces the maximal order below `1`. -/
private theorem maxOrder_lt_one
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking 1))
    (hB : ∀ (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfDim Set.univ 1),
      maxOrder ((B.toFun t ⟨ht.1, ht.2.1⟩).markedTransform t.markedIdeal).I < 1)
    (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfMarking 1) :
    maxOrder ((B.toFun t ht).markedTransform t.markedIdeal).I < 1 := by
  by_cases hne : Nonempty t.X
  · exact hB t (mem_markedTriplesOfDim ht hne)
  · have hXe : IsEmpty t.X := not_nonempty_iff.1 hne
    rw [eq_nil_of_isEmpty hXe _ (B.hasNoEmptyBlowups _ ht)]
    change maxOrder t.markedIdeal.I < 1
    rw [maxOrder, maxOrderAlong, iSup_of_empty]
    exact bot_lt_iff_ne_bot.mpr one_ne_zero

/-- **Kollár 3.72: (3.69) and (3.71.2) imply (3.35).** Let `B` be a smooth blow-up sequence
functor of order `≥ 1` on the marked triples of marking `1` whose restriction to the marked
triples of finite dimension is an order reduction functor for marked ideals of order `1`, which
has the closed embedding property of (3.71.2) and ignores empty entries. Then
`principalizationConstruction B.toFun` is a principalization functor away from `E^{(2)}` on the
triples `(X, I, E)` with `X` equidimensional: (0) it has no empty blow-ups; (1) it is a smooth
blow-up sequence whose centers have simple normal crossings with `E`; (2) the pull-back of `I` is
monomial; (3″) its centers lie over `cosupp I ∪ E^{(2)}`; (4) it commutes with smooth morphisms
and with change of fields; (5) it commutes with closed embeddings for triples with `E = ∅`. -/
@[mmp "thm_kr3c_principalization_from_marked_order_reduction"]
public theorem isPrincipalizationFunctorAwayFromDoubleLocus_principalizationConstruction
    (B : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfMarking 1))
    (hB : IsOrderReductionFunctorMarked 1 Set.univ
      ⟨fun t ht => B.toFun t ⟨ht.1, ht.2.1⟩,
        fun t ht => B.isOrderGeMarkedTripleSeq t ⟨ht.1, ht.2.1⟩,
        fun t ht => B.hasNoEmptyBlowups t ⟨ht.1, ht.2.1⟩⟩)
    (hCE : HasClosedEmbeddingProperty B.toFun)
    (hEmpty : IgnoresEmptyEntriesMarked _ B.toFun) :
    (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (principalizationConstructionOnTriples B.toFun t ht).HasNoEmptyBlowups) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (principalizationConstructionOnTriples B.toFun t ht).IsSmooth t.sX ∧
          (principalizationConstructionOnTriples B.toFun t ht).CentersHaveSNCWith t.sX
            t.E.support) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        IsMonomialIdeal (t.I.comap (principalizationConstructionOnTriples B.toFun t ht).toBase)) ∧
      (∀ (t : FieldBlowupTriple.{u}) (ht : t ∈ triples),
        (principalizationConstructionOnTriples B.toFun t ht).CentersLieOver (𝟙 t.X)
          ((t.I.support : Set t.X) ∪ t.E.doubleLocus)) ∧
      CommutesWithSmoothOn triples (principalizationConstructionOnTriples B.toFun) ∧
      CommutesWithFieldChangeOn triples (principalizationConstructionOnTriples B.toFun) ∧
      ∀ d : ClosedEmbeddingData.{u}, d.E.s = 0 →
        ∀ (hX : d.ambientTriple ∈ triples) (hY : d.embeddedTriple ∈ triples),
          ClosedBlowupSequence.IsPushforward d.j
            (principalizationConstructionOnTriples B.toFun d.embeddedTriple hY)
            (principalizationConstructionOnTriples B.toFun d.ambientTriple hX) := by
  have hS := commutesWithSmoothOnMarked B hB.2.1
  have hF := commutesWithFieldChangeOnMarked B hB.2.2
  refine ⟨fun t ht => hasNoEmptyBlowups_principalizationConstruction B.toFun t _,
    fun t ht => isSmooth_principalizationConstruction_and_centersHaveSNCWith B t _,
    fun t ht => isMonomialIdeal_comap_principalizationConstruction B (maxOrder_lt_one B hB.1)
      t _ ht.2.2.2.2.1,
    fun t ht => centersLieOver_principalizationConstruction B t _,
    commutesWithSmoothOn_principalizationConstruction B.toFun hS,
    commutesWithFieldChangeOn_principalizationConstruction B.toFun hS hF,
    fun d hd hX hY => commutesWithClosedEmbeddings_principalizationConstruction B hCE d
      ⟨hd, iff_of_true hX.2.2.2.2.1 hY.2.2.2.2.1⟩ _ _⟩

end MMP.Resolution
