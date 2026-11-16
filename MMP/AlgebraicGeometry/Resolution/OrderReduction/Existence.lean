module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MarkedMixedIdealStep
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.MarkedSmoothPullback
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialReducesOrder
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialSmoothPullback
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientIdeal
import MMP.AlgebraicGeometry.Resolution.MaximalOrderAttained
import MMP.AlgebraicGeometry.Resolution.TransformRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupChartClosedImmersion
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalCurveNegativity
import MMP.AlgebraicGeometry.Resolution.OrderReduction.EmptyEntriesInert
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialPart
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MarkedStepOne
import MMP.AlgebraicGeometry.Resolution.OrderUpperSemicontinuous
import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MixedIdealMonomialReduction

/-!
# Order reduction for ideals and marked ideals (Kollár 3.68–3.70)

Kollár proves order reduction for ideals (Theorem 3.68) and for marked ideals (Theorem 3.69)
together, by induction on the dimension (3.70). The canonical families `boFamily` (the functors
`𝓑𝓞_{d,μ}`) and `bmoFamily` (the functors `𝓑𝓜𝓞_{d,μ}`) are defined by recursion on the
dimension; this file proves that they are order reduction functors.

The marked functor `bmoFunctor B d m` built from a family `B` of order reduction functors for
ideals runs three steps: Step 1 reduces the order of the nonmonomial part `N(I)` below `m`,
Step 2 separates the cosupport of `(I, m)` from that of `N(I)` with the mixed ideals
`K_s(I, m) = N(I)^m + I^s`, and Step 3 extends the monomial order reduction on the complement of
`cosupp N(I)` by closure. We show that if `B` is an order-reduction family on dimensions
`a, …, b`, then `bmoFunctor B` reduces the order below the marking (Kollár 3.107 (1)) and
commutes with change of fields (3.107 (2)); together with the compatibility with smooth
morphisms this is the second inductive step 3.70.2. The joint induction then shows that
`bmoFamily` is a marked order-reduction family on dimensions `0, …, n` for every `n`, and that
every `boFamily d μ` ignores empty entries. Reading the conditions on all dimensions off those on
`0, …, n` gives Theorems 3.68 and 3.69.

## Main results

* `MMP.Resolution.maxOrder_markedTransform_bmoFunctor_lt`: `bmoFunctor B d m` ends with a marked
  ideal of maximal order `< m`.
* `MMP.Resolution.commutesWithFieldChangeOnMarked_bmoFunctor`: `bmoFunctor B` commutes with
  change of fields.
* `MMP.Resolution.isMarkedOrderReductionFamily_bmoFunctor`: the second inductive step.
* `MMP.Resolution.isMarkedOrderReductionFamily_bmoFamily`: `bmoFamily` is a marked
  order-reduction family on dimensions `0, …, n`.
* `MMP.Resolution.ignoresEmptyEntriesMarked_bmoFamily`: `𝓑𝓜𝓞_m` ignores empty entries.
* `MMP.Resolution.exists_isOrderReductionFunctorIdeals_boFamily`: Kollár's Theorem 3.68.
* `MMP.Resolution.exists_isOrderReductionFunctorMarked_bmoFamily`: Kollár's Theorem 3.69.

## Implementation notes

The compatibility with change of fields is proved for any `h : X' → X` forming a cartesian
square with `X → Spec k` and `Spec k' → Spec k` (`k → k'` a field extension), with `I' = h^*I`
and `E' = h⁻¹E`. The ends of the rounds on `X'` are again of this form over the ends on `X`, the
last morphism of the pulled-back sequence being the comparison map. The projection is flat and
surjective, preserves orders and dimension, and `A(h^*I) = h^*A(I)`, so the invariants driving
Steps 1 and 2 agree on `X'` and on `X`. The irreducible components of `h⁻¹Z` are the components
of the `h⁻¹Z_j`, `Z_j` the components of `Z`, with the same codimension, so the total transform
of an ordered divisor pulls back along each blow-up.

The comparison of the families in the induction rests on two locality statements:
`bmoFunctor B d` only reads `B d`, and `boFunctor M n` only reads `M (n - 1)`.

## References

* [J. Kollár, *Lectures on resolution of singularities*, 3.68–3.72, Thm. 3.107, 3.111]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Resolution

/-- A scheme of Krull dimension `n` has `dimNat X = n`. -/
private theorem dimNat_eq_of_topologicalKrullDim_eq {X : Scheme.{u}} {n : ℕ}
    (h : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞)) : dimNat X = n := by
  simp [dimNat, h]

/-- A scheme of dimension in `N` has dimension `dimNat X`, which lies in `N`. -/
private theorem dimNat_mem_of_hasDimensionIn {X : Scheme.{u}} {N : Set ℕ}
    (h : HasDimensionIn X N) : dimNat X ∈ N := by
  obtain ⟨n, hn, hX⟩ := h
  rwa [dimNat_eq_of_topologicalKrullDim_eq hX]

/-- A scheme of dimension in `N` has dimension `dimNat X`. -/
private theorem hasDimensionIn_dimNat {X : Scheme.{u}} {N : Set ℕ} (h : HasDimensionIn X N) :
    HasDimensionIn X {dimNat X} := by
  obtain ⟨n, -, hX⟩ := h
  exact ⟨n, (dimNat_eq_of_topologicalKrullDim_eq hX).symm, hX⟩

/-! ### Generalities on triples and blow-up sequences -/

/-- A nonempty quasi-compact scheme locally of finite type over a field has Krull dimension
`dimNat X`. -/
private theorem krullDim_eq_dimNat {k : Type u} [Field k] {X : Scheme.{u}} [Nonempty X]
    (sX : X ⟶ Spec (.of k)) (h1 : LocallyOfFiniteType sX) (h2 : QuasiCompact sX) :
    topologicalKrullDim X = ((dimNat X : ℕ∞) : WithBot ℕ∞) := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hne := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    rw [topologicalKrullDim, ne_eq, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.1 hbot
  have ha' : a ≠ ⊤ := by rintro rfl; exact hne ha.symm
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 ha'
  simp [dimNat, ← ha]

/-- The order is invariant under a bijective ring map of local rings. -/
private theorem idealOrder_map_of_bijective {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) (hφ : Function.Bijective φ) (J : Ideal R) :
    idealOrder (J.map φ) = idealOrder J := by
  let e : R ≃+* S := RingEquiv.ofBijective φ hφ
  have hm : (IsLocalRing.maximalIdeal R).map e = IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have key : ∀ j : ℕ, J.map φ ≤ IsLocalRing.maximalIdeal S ^ j ↔
      J ≤ IsLocalRing.maximalIdeal R ^ j := by
    intro j
    change J.map e ≤ _ ↔ _
    rw [← hm, ← Ideal.map_pow, Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _
      e.bijective]
  simp only [idealOrder, key]

/-- The order of an ideal sheaf is preserved by pull-back along an open immersion. -/
private theorem multAt_comap_of_isOpenImmersion {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)
    [IsOpenImmersion f] (J : Y.IdealSheafData) (y : Y') :
    multAt (J.comap f) y = multAt J (f y) := by
  rw [multAt, IdealSheafData.stalk_comap,
    idealOrder_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]
  rfl

/-- The end of a sequence of order `≥ m` starting with a marked triple is a marked triple. -/
private theorem isTriple_end {k : Type u} [Field k] {X : Scheme.{u}} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), S.IsOrderGeMarkedTripleSeq s a E →
      IsTriple (S.toBase ≫ s) (S.markedTransform a).I (S.orderedTotalTransform E)
  | .nil X, s, a, E, h => by
    show IsTriple (𝟙 X ≫ s) a.I E
    rwa [Category.id_comp]
  | .cons Z S, s, a, E, h => by
    show IsTriple ((S.toBase ≫ blowUpToBase Z) ≫ s) _ _
    rw [Category.assoc]
    exact isTriple_end S _ _ _ h.2.2.2.2.2

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
private theorem dimNat_target_of_isOrderGe {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E → dimNat B.target = dimNat X
  | _, .nil _, _, _, _, _ => rfl
  | _, .cons Z B, s, a, E, hB => by
    obtain ⟨⟨-, -, hlft, -, hequi, -, -⟩, -, hc, -, -, hB'⟩ := hB
    haveI : LocallyOfFiniteType s := hlft
    refine (dimNat_target_of_isOrderGe B _ _ _ hB').trans ?_
    simp only [dimNat, topologicalKrullDim_blowUp s hequi Z hc]

/-- A scheme of finite type and quasi-compact over a field is noetherian. -/
private theorem isNoetherian_of_isTriple {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E) :
    AlgebraicGeometry.IsNoetherian X :=
  haveI : LocallyOfFiniteType s := h.2.2.1
  haveI : QuasiCompact s := h.2.2.2.1
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  {}

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

/-- The monomial data on an open `U` of a triple. -/
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

/-! ### The order is reduced below the marking -/

/-- `maxord I < m` exactly when `cosupp(I, m)` is empty. -/
private theorem maxOrder_lt_iff_cosupport_eq_empty {X : Scheme.{u}} (a : MarkedIdeal X)
    (hm : 1 ≤ a.m) :
    maxOrder a.I < a.m ↔ a.cosupport = ∅ := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a.m = n + 1 := ⟨a.m - 1, by omega⟩
  have key : ∀ x : ℕ∞, x < (a.m : ℕ∞) ↔ ¬ (a.m : ℕ∞) ≤ x := fun x => not_le.symm
  rw [Set.eq_empty_iff_forall_notMem, key]
  simp only [MarkedIdeal.cosupport, Set.mem_setOf_eq, maxOrder, maxOrderAlong, Set.mem_univ,
    iSup_true]
  rw [hn, Nat.cast_add, Nat.cast_one, ENat.add_one_le_iff (ENat.coe_ne_top n), lt_iSup_iff]
  simp only [not_exists]
  exact forall_congr' fun x => by rw [ENat.add_one_le_iff (ENat.coe_ne_top n)]

/-- The maximal order of a marked transform along a concatenation `S.append T` is that of `T`
started at the end of `S`. -/
private theorem maxOrder_markedTransform_append {X : Scheme.{u}} :
    ∀ (S : ClosedBlowupSequence X) (T : ClosedBlowupSequence S.target) (a : MarkedIdeal X),
      maxOrder ((S.append T).markedTransform a).I =
        maxOrder (T.markedTransform (S.markedTransform a)).I
  | .nil _, _, _ => rfl
  | .cons Z S, T, a => maxOrder_markedTransform_append S T (a.birationalTransform Z)

/-- The marked transform keeps the marking. -/
private theorem markedTransform_eq_mk {X : Scheme.{u}} (S : ClosedBlowupSequence X)
    (a : MarkedIdeal X) : S.markedTransform a = ⟨(S.markedTransform a).I, a.m⟩ := by
  cases h : S.markedTransform a
  have := S.markedTransform_m a
  rw [h] at this
  subst this
  rfl

/-- `J ≤ (A : D)` exactly when `J · D ≤ A`. -/
private theorem le_idealColon_iff {X : Scheme.{u}} (A D J : X.IdealSheafData) :
    J ≤ idealColon A D ↔ J * D ≤ A := by
  unfold idealColon
  rw [Scheme.IdealSheafData.le_ofIdeals_iff, Scheme.IdealSheafData.le_def]
  refine forall_congr' fun V => ?_
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.mul_le]
  refine ⟨fun h r hr t ht => ?_, fun h r hr => ?_⟩
  · exact Submodule.mem_colon.1 (h hr) t ht
  · exact Submodule.mem_colon.2 fun t ht => h r hr t ht

/-- The ideal quotient commutes with pull-back along an isomorphism. -/
private theorem idealColon_comap_of_isIso {X Y : Scheme.{u}} (c : Y ⟶ X) [IsIso c]
    (A D : X.IdealSheafData) :
    idealColon (A.comap c) (D.comap c) = (idealColon A D).comap c := by
  have back : ∀ J : X.IdealSheafData, (J.comap c).comap (inv c) = J := fun J => by
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have fwd : ∀ J : Y.IdealSheafData, (J.comap (inv c)).comap c = J := fun J => by
    rw [← Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  have iffY : ∀ J K : Y.IdealSheafData, J.comap (inv c) ≤ K.comap (inv c) ↔ J ≤ K :=
    fun J K => ⟨fun h => fwd J ▸ fwd K ▸ Scheme.IdealSheafData.comap_mono c h,
      fun h => Scheme.IdealSheafData.comap_mono (inv c) h⟩
  have iffX : ∀ J K : X.IdealSheafData, J.comap c ≤ K.comap c ↔ J ≤ K :=
    fun J K => ⟨fun h => back J ▸ back K ▸ Scheme.IdealSheafData.comap_mono (inv c) h,
      fun h => Scheme.IdealSheafData.comap_mono c h⟩
  refine eq_of_forall_le_iff fun J => ?_
  rw [le_idealColon_iff, ← iffY, Stacks.IdealSheaf.comap_mul, back, back, ← le_idealColon_iff,
    ← iffX, fwd]

/-- The birational transform commutes with pull-back along an isomorphism. -/
private theorem birationalTransform_comap_of_isIso {X Y : Scheme.{u}} (h : Y ⟶ X) [IsIso h]
    (Z : X.IdealSheafData) (a : MarkedIdeal X) :
    (⟨a.I.comap h, a.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h) =
      ⟨(a.birationalTransform Z).I.comap (canonicalLift h Z), (a.birationalTransform Z).m⟩ := by
  haveI := Kollar.isIso_canonicalLift h Z
  have hc := canonicalLift_comp_blowUpToBase h Z
  show (⟨idealColon _ _, a.m⟩ : MarkedIdeal _) = ⟨(idealColon _ _).comap _, a.m⟩
  rw [← idealColon_comap_of_isIso]
  dsimp only
  simp only [← Scheme.IdealSheafData.comap_comp, hc, Stacks.IdealSheaf.comap_pow]

/-- Blowing up the empty subscheme does not change a marked ideal. -/
private theorem birationalTransform_top_comap {X Y : Scheme.{u}} (h : Y ⟶ X)
    (hc : Stacks.Blowup.IsCartierOver (⊤ : X.IdealSheafData) (Over.mk h)) (a : MarkedIdeal X) :
    (⟨a.I.comap h, a.m⟩ : MarkedIdeal Y) =
      ⟨(a.birationalTransform ⊤).I.comap (blowUpLift ⊤ h hc), (a.birationalTransform ⊤).m⟩ := by
  have hcol : ∀ A : (blowUp (⊤ : X.IdealSheafData)).IdealSheafData, idealColon A ⊤ = A :=
    fun A => eq_of_forall_le_iff fun J => by
      rw [le_idealColon_iff, Scheme.IdealSheafData.mul_top]
  show (⟨_, a.m⟩ : MarkedIdeal _) = ⟨(idealColon _ _).comap _, a.m⟩
  have hp : ((⊤ : (blowUp (⊤ : X.IdealSheafData)).IdealSheafData) ^ a.m) = ⊤ :=
    one_pow (M := (blowUp (⊤ : X.IdealSheafData)).IdealSheafData) a.m
  rw [Scheme.IdealSheafData.comap_top, hp, hcol, ← Scheme.IdealSheafData.comap_comp,
    blowUpLift_comp]

/-- The maximal order is invariant under pull-back along an isomorphism. -/
private theorem maxOrder_comap_of_isIso {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsIso g]
    (J : Y.IdealSheafData) : maxOrder (J.comap g) = maxOrder J := by
  simp only [maxOrder, maxOrderAlong, Set.mem_univ, iSup_true, multAt_comap_of_isOpenImmersion]
  exact g.surjective.iSup_comp (multAt J)

/-- Pulling back along an isomorphism and deleting empty blow-ups changes the last marked ideal
only by an isomorphism of the last schemes. -/
private theorem exists_isIso_markedTransform_pullbackReduced {X : Scheme.{u}}
    (S : ClosedBlowupSequence X) :
    ∀ {Y : Scheme.{u}} (h : Y ⟶ X) [IsIso h] (a : MarkedIdeal X),
      ∃ g : (S.pullbackReduced h).target ⟶ S.target, IsIso g ∧
        ((S.pullbackReduced h).markedTransform ⟨a.I.comap h, a.m⟩).I =
          (S.markedTransform a).I.comap g := by
  induction S with
  | nil X => exact fun h hh a => ⟨h, hh, rfl⟩
  | cons Z S ih =>
    intro Y h _ a
    by_cases hZ : Z.comap h = ⊤
    · have hc := ClosedBlowupSequence.isCartierOver_of_comap_eq_top h Z hZ
      have hZ' : Z = ⊤ := (Kollar.comap_eq_top_iff_of_isIso h Z).1 hZ
      have key : (ClosedBlowupSequence.cons Z S).pullbackReduced h =
          S.pullbackReduced (blowUpLift Z h hc) := by
        simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_true]
      rw [key]
      subst hZ'
      haveI := Kollar.isIso_blowUpLift_of_eq_top rfl h hc
      rw [birationalTransform_top_comap h hc a]
      exact ih (blowUpLift ⊤ h hc) (a.birationalTransform ⊤)
    · have key : (ClosedBlowupSequence.cons Z S).pullbackReduced h =
          .cons (Z.comap h) (S.pullbackReduced (canonicalLift h Z)) := by
        simp only [ClosedBlowupSequence.pullbackReduced, hZ, dite_false]
      rw [key]
      haveI := Kollar.isIso_canonicalLift h Z
      change ∃ g, IsIso g ∧ ((S.pullbackReduced (canonicalLift h Z)).markedTransform
        ((⟨a.I.comap h, a.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h))).I = _
      rw [birationalTransform_comap_of_isIso h Z a]
      exact ih (canonicalLift h Z) (a.birationalTransform Z)

/-- Deleting empty blow-ups does not change the maximal order of the last marked ideal. -/
private theorem maxOrder_markedTransform_reduction {X : Scheme.{u}}
    (S : ClosedBlowupSequence X) (a : MarkedIdeal X) :
    maxOrder (S.reduction.markedTransform a).I = maxOrder (S.markedTransform a).I := by
  obtain ⟨g, hg, e⟩ := exists_isIso_markedTransform_pullbackReduced S (𝟙 X) a
  have ha : (⟨a.I.comap (𝟙 X), a.m⟩ : MarkedIdeal X) = a := by
    rw [Scheme.IdealSheafData.comap_id]
  rw [ha] at e
  rw [ClosedBlowupSequence.reduction, e, maxOrder_comap_of_isIso]

/-- The statement proved by induction along a sequence `B` on `U`: for every quasi-compact open
immersion `j : U → X` whose image contains `cosupp a`, if the last marked ideal of `B` starting
with `j^*a` has maximal order `< a.m`, so has that of its extension by closure. -/
private def ClaimLt {k : Type u} [Field k] {U : Scheme.{u}} (B : ClosedBlowupSequence U) : Prop :=
  ∀ {X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X),
    1 ≤ a.m → IsTriple s a.I E → a.cosupport ⊆ Set.range j →
    B.IsOrderGeMarkedTripleSeq (j ≫ s) ⟨a.I.comap j, a.m⟩ (E.comap j) →
    maxOrder (B.markedTransform ⟨a.I.comap j, a.m⟩).I < a.m →
    maxOrder ((B.extendByClosure j).markedTransform a).I < a.m

/-- The inductive step of `ClaimLt`: a centre `Z ⊆ U` whose image `W` has support in `j(U)`. -/
private theorem claimLt_cons {k : Type u} [Field k] {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X) (hm : 1 ≤ a.m)
    (ht : IsTriple s a.I E) (hcos : a.cosupport ⊆ Set.range j) (W : X.IdealSheafData)
    (Z : U.IdealSheafData) (h : W.comap j = Z) (hsupp : (W.support : Set X) ⊆ Set.range j)
    (B : ClosedBlowupSequence (blowUp Z)) (ih : ClaimLt (k := k) B)
    (htU : IsTriple (j ≫ s) (a.I.comap j) (E.comap j))
    (hZsm : MMP.Mori.IsSmoothScheme (Z.subschemeι ≫ j ≫ s))
    (hZcod : HasComponentsOfPositiveCodim (Z.support : Set U))
    (hZsnc : HasSNCWith (E.comap j).E Z)
    (hZord : OrderAlongGE (a.I.comap j) (Z.support : Set U) a.m)
    (hB' : B.IsOrderGeMarkedTripleSeq (blowUpToBase Z ≫ j ≫ s)
      ((⟨a.I.comap j, a.m⟩ : MarkedIdeal U).birationalTransform Z)
      ((E.comap j).totalTransform Z))
    (hlt : maxOrder (B.markedTransform
      ((⟨a.I.comap j, a.m⟩ : MarkedIdeal U).birationalTransform Z)).I < a.m) :
    maxOrder ((ClosedBlowupSequence.cons W (B.extendByClosure
      (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift j W))).markedTransform a).I < a.m := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  have hsnc := hasSNCWith_of_comap j E W hsupp hZsnc
  have hWsm : MMP.Mori.IsSmoothScheme (W.subschemeι ≫ s) :=
    isSmoothScheme_of_hasSNCWith ⟨⟨X, a.I, E⟩, k, s⟩ ht W hsnc
  have hcod := hasComponentsOfPositiveCodim_of_comap j W hsupp hZcod
  have hord := orderAlongGE_of_comap j W hsupp a.I a.m hZord
  have sq := Kollar.isPullback_canonicalLift_of_flat j W
  haveI : IsOpenImmersion (canonicalLift j W) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›
  haveI : QuasiCompact (canonicalLift j W) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq ‹_›
  have hbt := birationalTransform_comap j s ht.2.1 W hWsm hcod a hord htU.2.1 hZsm hZcod hZord
  refine ih (canonicalLift j W) (blowUpToBase W ≫ s) (a.birationalTransform W)
    (E.totalTransform W) hm (isTriple_birationalTransform_totalTransform a ht hsnc) ?_ ?_ ?_
  · have hB1 : (ClosedBlowupSequence.cons W (.nil _)).IsOrderGeMarkedTripleSeq s a E :=
      ⟨ht, hWsm, hcod, hsnc, hord, isTriple_birationalTransform_totalTransform a ht hsnc⟩
    have := ClosedBlowupSequence.cosupport_markedTransform_truncate_subset s a E _ hB1 1
    refine this.trans ?_
    rw [range_canonicalLift]
    intro x hx
    simp only [ClosedBlowupSequence.truncate, ClosedBlowupSequence.toBase, Category.id_comp,
      Set.mem_preimage] at hx
    exact hcos hx
  · rw [← hbt, ← totalTransform_comap j E W hsupp, ← Category.assoc,
      canonicalLift_comp_blowUpToBase, Category.assoc]
    exact hB'
  · rw [← hbt]
    exact hlt

/-- `ClaimLt` holds for every blow-up sequence. -/
private theorem claimLt {k : Type u} [Field k] {U : Scheme.{u}} (B : ClosedBlowupSequence U) :
    ClaimLt (k := k) B := by
  induction B with
  | nil U =>
    intro X j _ _ s a E hm _ hcos _ hlt
    change maxOrder a.I < a.m
    change maxOrder (a.I.comap j) < a.m at hlt
    rw [maxOrder_lt_iff_cosupport_eq_empty a hm]
    rw [maxOrder_lt_iff_cosupport_eq_empty ⟨a.I.comap j, a.m⟩ hm] at hlt
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨y, rfl⟩ := hcos hx
    have hy : y ∈ (⟨a.I.comap j, a.m⟩ : MarkedIdeal U).cosupport := by
      change (a.m : ℕ∞) ≤ multAt (a.I.comap j) y
      rw [multAt_comap_of_isOpenImmersion]
      exact hx
    rw [hlt] at hy
    exact hy
  | cons Z B ih =>
    intro X j _ _ s a E hm ht hcos hB hlt
    obtain ⟨htU, hZsm, hZcod, hZsnc, hZord, hB'⟩ := hB
    rw [ClosedBlowupSequence.extendByClosure,
      dif_pos (ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion j Z)]
    have hsupp : ((Z.map j).support : Set X) ⊆ Set.range j := by
      haveI : CharZero k := ht.1
      haveI : LocallyOfFiniteType s := ht.2.2.1
      haveI : Smooth s := (MMP.Mori.isSmoothScheme_iff s).mp ht.2.1
      rw [Scheme.IdealSheafData.support_map, TopologicalSpace.Closeds.coe_closure]
      exact (closure_minimal (image_subset_cosupport j s htU.2.1 Z hZsm a hZord)
        (isClosed_setOf_le_multAt s a.I a.m)).trans hcos
    exact claimLt_cons j s a E hm ht hcos (Z.map j) Z
      (ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion j Z) hsupp B ih htU hZsm hZcod
      hZsnc hZord hB' hlt

/-- Along the extension by closure along a quasi-compact open immersion `j` whose image contains
`cosupp a`, the last marked ideal has maximal order `< a.m` if it does over `U`. -/
private theorem maxOrder_markedTransform_extendByClosure_lt {k : Type u} [Field k]
    {U X : Scheme.{u}} (B : ClosedBlowupSequence U) (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X) (E : OrderedDivisor X)
    (hm : 1 ≤ a.m) (ht : IsTriple s a.I E) (hcos : a.cosupport ⊆ Set.range j)
    (hB : B.IsOrderGeMarkedTripleSeq (j ≫ s) ⟨a.I.comap j, a.m⟩ (E.comap j))
    (hlt : maxOrder (B.markedTransform ⟨a.I.comap j, a.m⟩).I < a.m) :
    maxOrder ((B.extendByClosure j).markedTransform a).I < a.m :=
  claimLt B j s a E hm ht hcos hB hlt

/-- On `U = X ∖ cosupp N(I)` the ideal `I` is its monomial part. -/
private theorem comap_eq_monomialIdeal {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (ht : IsTriple s I E)
    (U : X.Opens) (hU : U = (nonmonomialPart I E).support.compl) :
    I.comap U.ι = divisorIdeal (monomialPartCoeff (I.comap U.ι) (E.comap U.ι)) := by
  have hsm := ht.2.1
  have hlft := ht.2.2.1
  have hqc := ht.2.2.2.1
  haveI : LocallyOfFiniteType s := hlft
  haveI : QuasiCompact s := hqc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : Smooth s := (MMP.Mori.isSmoothScheme_iff s).1 hsm
  have hsmU : MMP.Mori.IsSmoothScheme (U.ι ≫ s) := (MMP.Mori.isSmoothScheme_iff _).2 inferInstance
  have hN : (nonmonomialPart I E).comap U.ι = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext x
    simp only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
      Set.mem_preimage, TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
    intro hx
    have hxU := x.2
    subst hU
    exact hxU hx
  have hM := monomialPart_comap s ht (U.ι ≫ s) hsmU U.ι (IsReducedFlatBaseChange.of_smooth U.ι)
  calc I.comap U.ι = (monomialPart I E * nonmonomialPart I E).comap U.ι := by
        rw [monomialPart_mul_nonmonomialPart s I E ht]
    _ = monomialPart (I.comap U.ι) (E.comap U.ι) := by
        rw [Stacks.IdealSheaf.comap_mul, hN, hM,
          show (⊤ : (U : Scheme).IdealSheafData) = 1 from rfl, mul_one]
    _ = _ := rfl

/-- **Kollár, Thm. 3.107 (1).** Let `𝓑` be an order-reduction family on dimensions `a, …, b`
(`IsOrderReductionFamily`), `m ≥ 1`, and `(X, I, m, E)` a marked triple with `dim X = d`,
`a ≤ d ≤ b` (`markedTriplesOfDim`). Then the last ideal `I_r` of `bmoFunctor B d m (X, I, m, E)`,
the birational transform of the marked ideal `(I, m)`, has `maxOrder I_r < m`. -/
@[mmp "thm_kr3e_order_reduction_marked_reduces_order"]
public theorem maxOrder_markedTransform_bmoFunctor_lt {a b d m : ℕ} (B : UnmarkedFamily.{u})
    (hB : IsOrderReductionFamily a b B) (hm : 1 ≤ m) (hd : d ∈ Set.Icc a b)
    (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfDim {d} m) :
    maxOrder ((bmoFunctor B d m t).markedTransform t.markedIdeal).I < m := by
  have hdt : dimNat t.X = d := dimNat_mem_of_hasDimensionIn ht.2.2
  obtain ⟨htm, htmm, -⟩ := ht
  have hmi : t.markedIdeal = ⟨t.I, m⟩ := by rw [MarkedTriple.markedIdeal, htmm]
  rw [hmi]
  -- Step 1
  obtain ⟨h1, -⟩ := isOrderGeMarkedTripleSeq_bmoStepOne hB hm htm (hdt ▸ hd)
  rw [hdt] at h1
  set S₁ := bmoStepOne B d m t
  set t₁ := t.endOf m S₁
  have ht₁m : t₁ ∈ markedTriples := isTriple_end S₁ t.sX _ t.E h1
  have hd₁ : dimNat t₁.X = d := (dimNat_target_of_isOrderGe S₁ t.sX _ t.E h1).trans hdt
  -- Step 2
  obtain ⟨h2, hdisj⟩ := isOrderGeMarkedTripleSeq_bmoStepTwo hB hm ht₁m (hd₁ ▸ hd)
  rw [hd₁] at h2 hdisj
  set S₂ := bmoStepTwo B d m t₁
  set t₂ := t₁.endOf m S₂
  have ht₂m : IsTriple t₂.sX t₂.I t₂.E := isTriple_end S₂ t₁.sX _ t₁.E h2
  -- Step 3
  set U : t₂.X.Opens := (nonmonomialPart t₂.I t₂.E).support.compl
  set C : MonomialData U :=
    ⟨t₂.k, U.ι ≫ t₂.sX, t₂.E.comap U.ι, monomialPartCoeff (t₂.I.comap U.ι) (t₂.E.comap U.ι)⟩
  obtain ⟨htU, hCm⟩ := isMonomialData_restrict t₂.sX t₂.I t₂.E ht₂m U
  have hIU : t₂.I.comap U.ι = C.monomialIdeal := comap_eq_monomialIdeal t₂.sX t₂.I t₂.E ht₂m U rfl
  obtain ⟨h3, hlt3⟩ := MonomialData.isOrderGeMarkedTripleSeq_monomialOrderReduction C hCm ht₂m.1
    htU.2.2.2.2.1 hm
  rw [← hIU] at h3 hlt3
  haveI : LocallyOfFiniteType t₂.sX := ht₂m.2.2.1
  haveI : IsLocallyNoetherian t₂.X := LocallyOfFiniteType.isLocallyNoetherian t₂.sX
  have hcos : (⟨t₂.I, m⟩ : MarkedIdeal t₂.X).cosupport ⊆ Set.range U.ι := by
    intro x hx
    rw [Scheme.Opens.range_ι]
    exact hdisj.notMem_of_mem_left hx
  have hext := maxOrder_markedTransform_extendByClosure_lt (C.monomialOrderReduction m) U.ι
    t₂.sX ⟨t₂.I, m⟩ t₂.E hm ht₂m hcos h3 hlt3
  set Ext := (C.monomialOrderReduction m).extendByClosure U.ι
  have hm₁ : S₁.markedTransform ⟨t.I, m⟩ = ⟨t₁.I, m⟩ := markedTransform_eq_mk S₁ _
  have hm₂ : S₂.markedTransform ⟨t₁.I, m⟩ = ⟨t₂.I, m⟩ := markedTransform_eq_mk S₂ _
  have hbmo : bmoFunctor B d m t = (S₁.append (S₂.append Ext)).reduction := by
    classical
    have e₁ : (if t ∈ markedTriples then bmoStepOne B d m t else .nil t.X) = S₁ := if_pos htm
    have e₂ : (if t₁ ∈ markedTriples then bmoStepTwo B d m t₁ else .nil t₁.X) = S₂ :=
      if_pos ht₁m
    unfold bmoFunctor
    rw [e₁]
    dsimp only
    rw [e₂]
    rfl
  rw [hbmo, maxOrder_markedTransform_reduction]
  calc maxOrder ((S₁.append (S₂.append Ext)).markedTransform ⟨t.I, m⟩).I
      = maxOrder ((S₂.append Ext).markedTransform (S₁.markedTransform ⟨t.I, m⟩)).I :=
        maxOrder_markedTransform_append _ _ _
    _ = maxOrder ((S₂.append Ext).markedTransform ⟨t₁.I, m⟩).I :=
        congrArg (fun x => maxOrder ((S₂.append Ext).markedTransform x).I) hm₁
    _ = maxOrder (Ext.markedTransform (S₂.markedTransform ⟨t₁.I, m⟩)).I :=
        maxOrder_markedTransform_append _ _ _
    _ = maxOrder (Ext.markedTransform ⟨t₂.I, m⟩).I :=
        congrArg (fun x => maxOrder (Ext.markedTransform x).I) hm₂
    _ < m := hext

section FieldChange

open Aux

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
          rw [← Scheme.IdealSheafData.range_subschemeι]; exact ⟨b, rfl⟩
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
    have h1 : h η ⤳ y' := by
      rwa [hhη, specializes_iff_mem_closure]
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

/-- **The total transform under flat base change with reduced base changes.** -/
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

/-! ### Transforms along a pulled-back blow-up sequence -/

section Transforms

/-- The blow-up of a noetherian scheme is noetherian. -/
private theorem isNoetherian_blowUp {Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y]
    (W : Y.IdealSheafData) : AlgebraicGeometry.IsNoetherian (blowUp W) :=
  have : IsLocallyNoetherian (blowUp W) := LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase W)
  have : CompactSpace (blowUp W) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase W)
  {}

/-- **Marked and total transforms under flat base change with reduced base changes.** Along a
smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, the marked transform of
`(h^*I, m)` and the total transform of `h⁻¹E` along `h^*𝐁` are the inverse images of those along
`𝐁` under the last morphism of `h^*𝐁`. -/
private theorem transforms_pullback {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E : OrderedDivisor X), S.IsOrderGeMarkedTripleSeq s a E →
      ∀ {Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian Y] (h : Y ⟶ X),
        IsReducedFlatBaseChange h →
        (S.pullback h).markedTransform ⟨a.I.comap h, a.m⟩ =
            ⟨(S.markedTransform a).I.comap (S.pullbackHom h), a.m⟩ ∧
          (S.pullback h).orderedTotalTransform (E.comap h) =
            (S.orderedTotalTransform E).comap (S.pullbackHom h)
  | _, .nil _, _, _, _, _, _, _, _, _ => ⟨rfl, rfl⟩
  | X, .cons Z S, s, a, E, hS, Y, _, h, hh => by
    obtain ⟨hI, hZsm, -, -, hord, hS'⟩ := hS
    haveI := isNoetherian_of_isTriple hI
    have ha : a.I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a.m :=
      comap_le_comap_pow_of_stalk_le _ _ _ _
        (stalk_le_pow_of_orderAlongGE s hI.2.1 Z hZsm a.I a.m hord)
    have hb := Kollar.birationalTransform_comap_eq_comap_canonicalLift h Z a ha
    have hE := totalTransform_comap_of_isReducedFlatBaseChange hh E Z
    haveI := isNoetherian_blowUp (Z.comap h)
    have ih := transforms_pullback S _ _ _ hS' (canonicalLift h Z) (hh.canonicalLift Z)
    change (S.pullback (canonicalLift h Z)).markedTransform
        ((⟨a.I.comap h, a.m⟩ : MarkedIdeal Y).birationalTransform (Z.comap h)) = _ ∧
      (S.pullback (canonicalLift h Z)).orderedTotalTransform
        ((E.comap h).totalTransform (Z.comap h)) = _
    rw [hb, hE]
    exact ih

end Transforms

/-! ### Field changes up to isomorphism -/

/-- `t'` is a field change of `t` along `σ : k → k'` through `h : X' → X`: the square
`X' → X`, `X' → Spec k'`, `X → Spec k`, `Spec k' → Spec k` is cartesian, `I' = h^*I` and
`E' = h⁻¹E`. -/
private structure FCRel (t t' : MarkedTriple.{u}) (h : t'.X ⟶ t.X) (σ : t.k →+* t'.k) :
    Prop where
  sq : IsPullback h t'.sX t.sX (Spec.map (CommRingCat.ofHom σ))
  hI : t'.I = t.I.comap h
  hE : t'.E = t.E.comap h

/-- The comparison morphism of a field change of a triple of characteristic zero is flat with
reduced base changes. -/
private theorem FCRel.isReducedFlatBaseChange {t t' : MarkedTriple.{u}} {h : t'.X ⟶ t.X}
    {σ : t.k →+* t'.k} (hR : FCRel t t' h σ) (ht : t ∈ markedTriples) :
    IsReducedFlatBaseChange h :=
  haveI : CharZero t.k := ht.1
  IsReducedFlatBaseChange.of_isPullback hR.sq.flip (IsReducedFlatBaseChange.specMap σ)

/-- The comparison morphism of a field change is surjective. -/
private theorem FCRel.surjective {t t' : MarkedTriple.{u}} {h : t'.X ⟶ t.X}
    {σ : t.k →+* t'.k} (hR : FCRel t t' h σ) : Function.Surjective h :=
  (MorphismProperty.of_isPullback (P := @Surjective) hR.sq.flip inferInstance).surj

/-- The ends of a sequence of order `≥ m` and of its pull-back are again field changes. -/
private theorem FCRel.endOf_pullback {t t' : MarkedTriple.{u}} {h : t'.X ⟶ t.X} {σ : t.k →+* t'.k}
    (hR : FCRel t t' h σ) (ht : t ∈ markedTriples) (ht' : t' ∈ markedTriples) (m : ℕ)
    (S : ClosedBlowupSequence t.X) (hS : S.IsOrderGeMarkedTripleSeq t.sX ⟨t.I, m⟩ t.E) :
    FCRel (t.endOf m S) (t'.endOf m (S.pullback h)) (S.pullbackHom h) σ := by
  have hh := hR.isReducedFlatBaseChange ht
  haveI := hh.flat
  haveI := isNoetherian_of_isTriple (show IsTriple t'.sX t'.I t'.E from ht')
  obtain ⟨hT1, hT2⟩ := transforms_pullback S t.sX ⟨t.I, m⟩ t.E hS h hh
  obtain ⟨⟨⟨X', I', E'⟩, k', s'⟩, m'⟩ := t'
  obtain ⟨hsq, hI, hE⟩ := hR
  dsimp only at hI hE h σ hsq hT1 hT2 ⊢
  subst hI hE
  refine ⟨?_, ?_, ?_⟩
  · exact (Kollar.isPullback_pullback_toBase_of_flat S h).flip.paste_vert hsq
  · exact congrArg MarkedIdeal.I hT1
  · exact hT2

/-! ### Orders and the invariants of Steps 1 and 2 under a field change -/

section Orders

/-- The higher derivative ideals commute with the pull-back along `X_L ⟶ X`. -/
private theorem higherDerivativeIdeal_comap_pullback_fst {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX]
    (I : X.IdealSheafData) (r : ℕ) :
    higherDerivativeIdeal (Limits.pullback.snd sX (Spec.map (CommRingCat.ofHom σ)))
        (I.comap (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ)))) r =
      (higherDerivativeIdeal sX I r).comap
        (Limits.pullback.fst sX (Spec.map (CommRingCat.ofHom σ))) := by
  letI := σ.toAlgebra
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [higherDerivativeIdeal_succ, higherDerivativeIdeal_succ, ih]
    exact (derivativeIdeal_comap_pullback_fst (L := L) sX).2 _

/-- A morphism of smooth schemes over fields of characteristic zero that commutes with all
higher derivative ideals of `I` preserves the order of `I` pointwise. -/
private theorem multAt_comap_eq_of_higherDerivativeIdeal {k K : Type u} [Field k] [CharZero k]
    [Field K] [CharZero K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of K))
    [Smooth sX] [Smooth sY] (f : Y ⟶ X) (I : X.IdealSheafData)
    (hD : ∀ j, higherDerivativeIdeal sY (I.comap f) j = (higherDerivativeIdeal sX I j).comap f)
    (y : Y) : multAt (I.comap f) y = multAt I (f y) := by
  have key (n : ℕ) : (n : ℕ∞) ≤ multAt (I.comap f) y ↔ (n : ℕ∞) ≤ multAt I (f y) := by
    cases n with
    | zero => simp
    | succ n =>
      rw [succ_le_multAt_iff_forall_mem_support sY, succ_le_multAt_iff_forall_mem_support sX]
      exact forall₂_congr fun j _ => hD j ▸ mem_support_comap_iff f _ y
  exact le_antisymm (ENat.forall_natCast_le_iff_le.mp fun n => (key n).1)
    (ENat.forall_natCast_le_iff_le.mp fun n => (key n).2)

/-- The structure morphism of a triple is smooth. -/
private theorem smooth_of_isTriple {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E) :
    Smooth s := by
  have : LocallyOfFiniteType s := h.2.2.1
  have : LocallyOfFinitePresentation s :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := s)).mpr this
  exact (MMP.Mori.isSmoothScheme_iff _).1 h.2.1

variable {t t' : MarkedTriple.{u}} {h : t'.X ⟶ t.X} {σ : t.k →+* t'.k}

/-- **Orders are preserved by a field change.** -/
private theorem FCRel.multAt_comap (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (J : t.X.IdealSheafData) (y : t'.X) : multAt (J.comap h) y = multAt J (h y) := by
  have hT : IsTriple t.sX t.I t.E := ht
  haveI : CharZero t.k := ht.1
  haveI : CharZero t'.k := charZero_of_injective_ringHom σ.injective
  haveI := smooth_of_isTriple hT
  haveI : Smooth (Limits.pullback.snd t.sX (Spec.map (CommRingCat.ofHom σ))) :=
    MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback _ _) ‹_›
  set e := hR.sq.isoPullback.hom
  have he : e ≫ Limits.pullback.fst _ _ = h := hR.sq.isoPullback_hom_fst
  rw [← he, Scheme.IdealSheafData.comap_comp, multAt_comap_of_isOpenImmersion e,
    multAt_comap_eq_of_higherDerivativeIdeal t.sX
      (Limits.pullback.snd t.sX (Spec.map (CommRingCat.ofHom σ))) _ J
      (higherDerivativeIdeal_comap_pullback_fst σ t.sX J)]
  rfl

/-- The maximal order along a set is preserved by a field change. -/
private theorem FCRel.maxOrderAlong_comap (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (J : t.X.IdealSheafData) (Z : Set t.X) :
    maxOrderAlong (J.comap h) (h ⁻¹' Z) = maxOrderAlong J Z := by
  simp only [maxOrderAlong, Set.mem_preimage, hR.multAt_comap ht]
  exact hR.surjective.iSup_comp (fun x => ⨆ (_ : x ∈ Z), multAt J x)

/-- The maximal order is preserved by a field change. -/
private theorem FCRel.maxOrder_comap (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (J : t.X.IdealSheafData) : maxOrder (J.comap h) = maxOrder J := by
  have := hR.maxOrderAlong_comap ht J Set.univ
  rwa [Set.preimage_univ] at this

/-- The cosupport of a marked ideal is compatible with a field change. -/
private theorem FCRel.cosupport_comap (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (J : t.X.IdealSheafData) (m : ℕ) :
    (⟨J.comap h, m⟩ : MarkedIdeal t'.X).cosupport = h ⁻¹' (⟨J, m⟩ : MarkedIdeal t.X).cosupport := by
  ext y
  simp only [MarkedIdeal.cosupport, Set.mem_setOf_eq, Set.mem_preimage, hR.multAt_comap ht]

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
private theorem isEffectiveCartierDivisor_monomialPart {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
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

/-- **The nonmonomial part is compatible with a field change** (via `A(h^*I) = h^*A(I)`). -/
private theorem FCRel.nonmonomialPart_eq (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (ht' : t' ∈ markedTriples) :
    nonmonomialPart t'.I t'.E = (nonmonomialPart t.I t.E).comap h := by
  have hT : IsTriple t.sX t.I t.E := ht
  have hT' : IsTriple t'.sX t'.I t'.E := ht'
  haveI : LocallyOfFiniteType t'.sX := hT'.2.2.1
  haveI : QuasiCompact t'.sX := hT'.2.2.2.1
  have hM := monomialPart_comap t.sX hT t'.sX hT'.2.1 h (hR.isReducedFlatBaseChange ht)
  rw [← hR.hI, ← hR.hE] at hM
  have hcart := isEffectiveCartierDivisor_monomialPart t'.sX t'.I t'.E hT'
  have e2 : monomialPart t'.I t'.E * (nonmonomialPart t.I t.E).comap h = t'.I := by
    rw [hM, ← Stacks.IdealSheaf.comap_mul, monomialPart_mul_nonmonomialPart t.sX t.I t.E hT,
      hR.hI]
  calc nonmonomialPart t'.I t'.E
      = idealColon (monomialPart t'.I t'.E * nonmonomialPart t'.I t'.E) (monomialPart t'.I t'.E) :=
        (idealColon_mul_cancel_left _ _ hcart).symm
    _ = idealColon (monomialPart t'.I t'.E * (nonmonomialPart t.I t.E).comap h)
          (monomialPart t'.I t'.E) := by
        rw [monomialPart_mul_nonmonomialPart t'.sX t'.I t'.E hT', e2]
    _ = _ := idealColon_mul_cancel_left _ _ hcart

/-- The maximal order of the nonmonomial part is preserved by a field change. -/
private theorem FCRel.maxOrder_nonmonomialPart_eq (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (ht' : t' ∈ markedTriples) :
    maxOrder (nonmonomialPart t'.I t'.E) = maxOrder (nonmonomialPart t.I t.E) := by
  rw [hR.nonmonomialPart_eq ht ht', hR.maxOrder_comap ht]

/-- The ideal `K_s(I, m)` is compatible with a field change. -/
private theorem FCRel.mixedIdeal_eq (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (ht' : t' ∈ markedTriples) (m s : ℕ) :
    mixedIdeal t'.I t'.E m s = (mixedIdeal t.I t.E m s).comap h := by
  rw [mixedIdeal, mixedIdeal, hR.nonmonomialPart_eq ht ht', hR.hI]
  change _ = (nonmonomialPart t.I t.E ^ m ⊔ t.I ^ s).comap h
  rw [(Scheme.IdealSheafData.map_gc h).l_sup, Stacks.IdealSheaf.comap_pow,
    Stacks.IdealSheaf.comap_pow]
  rfl

/-- The invariant `s(X, I)` of Step 2 is preserved by a field change. -/
private theorem FCRel.bmoStepTwoOrder_eq (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (ht' : t' ∈ markedTriples) (m : ℕ) : bmoStepTwoOrder m t' = bmoStepTwoOrder m t := by
  unfold bmoStepTwoOrder
  rw [hR.nonmonomialPart_eq ht ht']
  conv_lhs => rw [show (⟨t'.I, m⟩ : MarkedIdeal t'.X) = ⟨t.I.comap h, m⟩ from by rw [hR.hI]]
  rw [hR.cosupport_comap ht, hR.maxOrderAlong_comap ht]

end Orders

/-! ### One round of Steps 1 and 2 under a field change -/

section Round

/-- Triples on the same scheme over the same field with equal data are equal. -/
private theorem fieldBlowupTriple_mk_congr {X : Scheme.{u}} {I I' : X.IdealSheafData}
    {E E' : OrderedDivisor X} {k : Type u} [Field k] {s s' : X ⟶ Spec (.of k)}
    (hI : I = I') (hE : E = E') (hs : s = s') :
    (⟨⟨X, I, E⟩, k, s⟩ : FieldBlowupTriple.{u}) = ⟨⟨X, I', E'⟩, k, s'⟩ := by
  subst hI hE hs; rfl

/-- `h⁻¹(g⁻¹E) = (h ≫ g)⁻¹E`. -/
private theorem OrderedDivisor.comap_comap {X Y Z : Scheme.{u}} (E : OrderedDivisor X)
    (g : Y ⟶ X) (h : Z ⟶ Y) : (E.comap g).comap h = E.comap (h ≫ g) := by
  simp only [OrderedDivisor.comap, Scheme.IdealSheafData.comap_comp]

/-- `𝟙⁻¹E = E`. -/
private theorem OrderedDivisor.comap_id {X : Scheme.{u}} (E : OrderedDivisor X) :
    E.comap (𝟙 X) = E := by
  simp only [OrderedDivisor.comap, Scheme.IdealSheafData.comap_id]

/-- The class of triples of given dimensions and bounded maximal order is stable under
isomorphisms. -/
private theorem pullback_mem_idealTriplesOfDim_of_isIso {N : Set ℕ} {μ : ℕ}
    {τ : FieldBlowupTriple.{u}} (hτ : τ ∈ idealTriplesOfDim N μ) {Y : Scheme.{u}}
    (e : Y ⟶ τ.X) [IsIso e] : τ.pullback e ∈ idealTriplesOfDim N μ := by
  obtain ⟨htr, ⟨n, hn, hdim⟩, hmax⟩ := hτ
  haveI : QuasiCompact τ.sX := htr.2.2.2.1
  refine ⟨mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples htr) e,
    TopologicalSpace.Equidimensional.of_homeomorph e.homeomorph (mem_triples_iff.1 htr).2⟩,
    ⟨n, hn, ?_⟩, ?_⟩
  · change topologicalKrullDim Y = _
    rw [IsHomeomorph.topologicalKrullDim_eq e e.homeomorph.isHomeomorph]
    exact hdim
  · change maxOrder (τ.I.comap e) ≤ μ
    rwa [maxOrder_comap_of_isIso]

/-- Values of a blow-up sequence functor at equal members are `HEq`. -/
private theorem toFun_heq {𝒞 : Set FieldBlowupTriple.{u}}
    (F : BlowupSequenceFunctor FieldBlowupTriple.toBlowupTriple 𝒞) {τ₁ τ₂ : FieldBlowupTriple.{u}}
    (e : τ₁ = τ₂) (h₁ : τ₁ ∈ 𝒞) (h₂ : τ₂ ∈ 𝒞) : F τ₁ h₁ ≍ F τ₂ h₂ := by
  subst e; rfl

variable {t t' : MarkedTriple.{u}} {h : t'.X ⟶ t.X} {σ : t.k →+* t'.k}

/-- **One round under a field change.** If `(X, J, E)` and `(X', h^*J, E')` are both in the class
of triples of dimension in `[a, b]` and maximal order `≤ μ`, the round
`𝓑_{dim X', μ}(X', h^*J, E')` is the pull-back of `𝓑_{dim X, μ}(X, J, E)`. -/
private theorem FCRel.round_eq {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B) (hR : FCRel t t' h σ) (ht' : t' ∈ markedTriples)
    {μ : ℕ} (hμ : 1 ≤ μ) (J : t.X.IdealSheafData)
    (hτ : (⟨⟨t.X, J, t.E⟩, t.k, t.sX⟩ : FieldBlowupTriple.{u}) ∈ idealTriplesOfDim (Set.Icc a b) μ)
    (hτ' : (⟨⟨t'.X, J.comap h, t'.E⟩, t'.k, t'.sX⟩ : FieldBlowupTriple.{u}) ∈
      idealTriplesOfDim (Set.Icc a b) μ) :
    B (dimNat t'.X) μ ⟨⟨t'.X, J.comap h, t'.E⟩, t'.k, t'.sX⟩ =
      (B (dimNat t.X) μ ⟨⟨t.X, J, t.E⟩, t.k, t.sX⟩).pullback h := by
  obtain ⟨F, hFB, -, hsm, hfc⟩ := hB μ hμ
  set τ : FieldBlowupTriple.{u} := ⟨⟨t.X, J, t.E⟩, t.k, t.sX⟩ with hτdef
  set τ' : FieldBlowupTriple.{u} := ⟨⟨t'.X, J.comap h, t'.E⟩, t'.k, t'.sX⟩ with hτ'def
  have h1 := hFB τ hτ
  have h2 := hFB τ' hτ'
  change F.toFun τ hτ = B (dimNat t.X) μ τ at h1
  change F.toFun τ' hτ' = B (dimNat t'.X) μ τ' at h2
  rw [← h1, ← h2]
  set e := hR.sq.isoPullback.hom with hedef
  have he : e ≫ Limits.pullback.fst _ _ = h := hR.sq.isoPullback_hom_fst
  have hes : e ≫ Limits.pullback.snd _ _ = t'.sX := hR.sq.isoPullback_hom_snd
  have e1 : (τ.fieldChange σ).pullback e = τ' := by
    change (⟨⟨t'.X, (J.comap (Limits.pullback.fst _ _)).comap e,
      (t.E.comap (Limits.pullback.fst _ _)).comap e⟩, t'.k, e ≫ Limits.pullback.snd _ _⟩ :
        FieldBlowupTriple.{u}) = _
    refine fieldBlowupTriple_mk_congr ?_ ?_ hes
    · rw [← Scheme.IdealSheafData.comap_comp, he]
    · rw [OrderedDivisor.comap_comap, he, hR.hE]
  haveI : IsIso e := Iso.isIso_hom _
  have hinv : inv e ≫ h = Limits.pullback.fst _ _ := by rw [← he, IsIso.inv_hom_id_assoc]
  have e2 : τ'.pullback (inv e) = τ.fieldChange σ := by
    change (⟨⟨_, (J.comap h).comap (inv e), t'.E.comap (inv e)⟩, t'.k, inv e ≫ t'.sX⟩ :
        FieldBlowupTriple.{u}) =
      ⟨⟨_, J.comap (Limits.pullback.fst _ _), t.E.comap (Limits.pullback.fst _ _)⟩, t'.k,
        Limits.pullback.snd _ _⟩
    refine fieldBlowupTriple_mk_congr ?_ ?_ ?_
    · rw [← Scheme.IdealSheafData.comap_comp, hinv]
    · rw [hR.hE, OrderedDivisor.comap_comap, hinv]
    · rw [← hes, IsIso.inv_hom_id_assoc]
  have hL : τ.fieldChange σ ∈ idealTriplesOfDim (Set.Icc a b) μ :=
    e2 ▸ pullback_mem_idealTriplesOfDim_of_isIso hτ' (inv e)
  have hY : (τ.fieldChange σ).pullback e ∈ idealTriplesOfDim (Set.Icc a b) μ := e1 ▸ hτ'
  have hT' : IsTriple t'.sX t'.I t'.E := ht'
  have hlft : LocallyOfFiniteType (e ≫ (τ.fieldChange σ).sX) := by
    change LocallyOfFiniteType (e ≫ Limits.pullback.snd _ _)
    rw [hes]; exact hT'.2.2.1
  have hqc : QuasiCompact (e ≫ (τ.fieldChange σ).sX) := by
    change QuasiCompact (e ≫ Limits.pullback.snd _ _)
    rw [hes]; exact hT'.2.2.2.1
  have hA := toFun_heq F.toFun e1.symm hτ' hY
  have hC := hsm.1 (τ.fieldChange σ) hL t'.X e
    (show Smooth (e : t'.X ⟶ Limits.pullback t.sX (Spec.map (CommRingCat.ofHom σ))) from
      inferInstance)
    (show Surjective (e : t'.X ⟶ Limits.pullback t.sX (Spec.map (CommRingCat.ofHom σ))) from
      inferInstance) hlft hqc hY
  rw [hfc τ hτ t'.k σ hL] at hC
  refine eq_of_heq (hA.trans ((heq_of_eq hC).trans ?_))
  refine (ClosedBlowupSequence.pullback_pullback_heq _ _ e h rfl ?_)
  rw [eqToHom_refl, Category.id_comp, ← he]

end Round

/-! ### Facts about the rounds of Steps 1 and 2 -/

section RoundFacts

/-- One round of Step 1: a sequence of order `μ ≥ m` for `(X, N(I), E)` is of order `≥ m` for
`(X, I, m, E)`. -/
private theorem isOrderGe_of_isOrderM {k : Type u} [Field k] {m μ : ℕ} (hm : 1 ≤ m)
    (hmμ : m ≤ μ) {X : Scheme.{u}} :
    ∀ (S : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
      (E : OrderedDivisor X), IsTriple s I E →
      S.IsOrderMTripleSeq s (nonmonomialPart I E) E μ →
      S.IsOrderGeMarkedTripleSeq s ⟨I, m⟩ E
  | .nil _, s, I, E, hI, _ => hI
  | .cons Z S, s, I, E, hI, hS => by
    obtain ⟨-, hZsm, hZcod, hZsnc, hZord, hS'⟩ := hS
    have hN : OrderAlongGE (nonmonomialPart I E) (Z.support : Set X) m := fun W hW => by
      rw [hZord W hW]; exact_mod_cast hmμ
    obtain ⟨hIZ, heq⟩ := nonmonomialPart_birationalTransform s hI hm hZsm hZsnc hN
    have hI' := isTriple_birationalTransform_totalTransform (⟨I, m⟩ : MarkedIdeal X) hI hZsnc
    rw [← heq] at hS'
    exact ⟨hI, hZsm, hZcod, hZsnc, hIZ,
      isOrderGe_of_isOrderM hm hmμ S (blowUpToBase Z ≫ s)
        ((⟨I, m⟩ : MarkedIdeal X).birationalTransform Z).I (E.totalTransform Z) hI' hS'⟩

/-- The nonmonomial part of the ideal of a triple is nonzero at the generic points. -/
private theorem isTriple_nonmonomialPart {k : Type u} [Field k] {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (h : IsTriple s I E) :
    IsTriple s (nonmonomialPart I E) E := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun η hη hbot => h6 η hη (eq_bot_iff.2 ?_), h7⟩
  rw [← hbot]
  exact stalk_le_stalk_of_le (le_idealColon _ _) η

/-- A scheme carrying an ideal of positive maximal order is nonempty. -/
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

/-- `K_s(I, m) = N(I)^m + I^s` is nonzero at the generic points of a triple. -/
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

end RoundFacts

/-! ### Steps 1 and 2 under a field change -/

section Steps

/-- The true branch of an `if` of blow-up sequences, for any `Decidable` instance and with the
branches typed only up to defeq. -/
private theorem ite_pos_eq {X : Scheme.{u}} {p : Prop} {_ : Decidable p}
    (x y : ClosedBlowupSequence X) (hp : p) : (if p then x else y) = x := by
  rw [if_pos hp]

/-- **Step 1 under a field change.** Every round of the Step-1 recursion on `X'` is the
pull-back of the round on `X`, the invariant `maxord N` being the same on both. -/
private theorem bmoStepOneAux_fieldChange {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B) {m : ℕ} (hm : 1 ≤ m) {d d' : ℕ} (hd : d ∈ Set.Icc a b)
    (hd' : d' ∈ Set.Icc a b) :
    ∀ (q : ℕ) (t t' : MarkedTriple.{u}) (h : t'.X ⟶ t.X) (σ : t.k →+* t'.k), FCRel t t' h σ →
      t ∈ markedTriples → t' ∈ markedTriples → dimNat t.X = d → dimNat t'.X = d' →
      bmoStepOneAux B d' m q t' = (bmoStepOneAux B d m q t).pullback h
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | q + 1, t, t', h, σ, hR, ht, ht', hdt, hdt' => by
    have hT : IsTriple t.sX t.I t.E := ht
    have hT' : IsTriple t'.sX t'.I t'.E := ht'
    have hN := hR.nonmonomialPart_eq ht ht'
    have hmax := hR.maxOrder_nonmonomialPart_eq ht ht'
    rw [bmoStepOneAux, bmoStepOneAux]
    by_cases h0 : maxOrder (nonmonomialPart t.I t.E) < m
    · rw [if_pos (hmax ▸ h0), if_pos h0]; rfl
    rw [if_neg (hmax ▸ h0), if_neg h0]
    have hNt := isTriple_nonmonomialPart hT
    have hNt' := isTriple_nonmonomialPart hT'
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
    have hne' : Nonempty t'.X :=
      nonempty_of_one_le_maxOrder (le_trans (by exact_mod_cast hm) (hmax ▸ not_lt.1 h0))
    have hτ : (⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩ : FieldBlowupTriple.{u}) ∈
        idealTriplesOfDim (Set.Icc a b) (maxOrder (nonmonomialPart t.I t.E)).toNat :=
      ⟨hNt, ⟨d, hd, by rw [← hdt]; exact krullDim_eq_dimNat _ hT.2.2.1 hT.2.2.2.1⟩, hμ.le⟩
    have hτ' : (⟨⟨t'.X, (nonmonomialPart t.I t.E).comap h, t'.E⟩, t'.k, t'.sX⟩ :
        FieldBlowupTriple.{u}) ∈
        idealTriplesOfDim (Set.Icc a b) (maxOrder (nonmonomialPart t.I t.E)).toNat :=
      ⟨hN ▸ hNt', ⟨d', hd', by rw [← hdt']; exact krullDim_eq_dimNat _ hT'.2.2.1 hT'.2.2.2.1⟩,
        by rw [hR.maxOrder_comap ht]; exact hμ.le⟩
    have hround := hR.round_eq hB ht' (hm.trans hmμ) _ hτ hτ'
    rw [hdt, hdt'] at hround
    obtain ⟨F, hFB, -, -⟩ := hB _ (hm.trans hmμ)
    have hS := F.isOrderMTripleSeq _ hτ
    have hS' := F.isOrderMTripleSeq _ hτ'
    rw [hFB] at hS hS'
    change ClosedBlowupSequence.IsOrderMTripleSeq t.sX (nonmonomialPart t.I t.E) t.E _
      (B (dimNat t.X) _ ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩) at hS
    change ClosedBlowupSequence.IsOrderMTripleSeq t'.sX ((nonmonomialPart t.I t.E).comap h) t'.E _
      (B (dimNat t'.X) _ ⟨⟨t'.X, (nonmonomialPart t.I t.E).comap h, t'.E⟩, t'.k, t'.sX⟩) at hS'
    rw [hdt] at hS
    rw [hdt', hround, ← hN] at hS'
    have hS1 := isOrderGe_of_isOrderM hm hmμ _ t.sX t.I t.E hT hS
    have hS1' := isOrderGe_of_isOrderM hm hmμ _ t'.sX t'.I t'.E hT' hS'
    dsimp only
    rw [hmax, hN, hround, ClosedBlowupSequence.append_pullback]
    congr 1
    set S : ClosedBlowupSequence t.X := B d (maxOrder (nonmonomialPart t.I t.E)).toNat
      ⟨⟨t.X, nonmonomialPart t.I t.E, t.E⟩, t.k, t.sX⟩ with hSdef
    have he1 : t.endOf m S ∈ markedTriples := isTriple_end _ _ _ _ hS1
    have he1' : t'.endOf m (S.pullback h) ∈ markedTriples := isTriple_end _ _ _ _ hS1'
    have ih := bmoStepOneAux_fieldChange hB hm hd hd' q (t.endOf m S) (t'.endOf m (S.pullback h))
      (S.pullbackHom h) σ (hR.endOf_pullback ht ht' m S hS1) he1
      he1' ((dimNat_target_of_isOrderGe _ _ _ _ hS1).trans hdt)
      ((dimNat_target_of_isOrderGe _ _ _ _ hS1').trans hdt')
    exact (ite_pos_eq _ _ he1').trans (ih.trans
      (congrArg (fun T => ClosedBlowupSequence.pullback T (S.pullbackHom h))
        (ite_pos_eq _ _ he1).symm))

/-- **Step 2 under a field change.** Every round of the Step-2 recursion on `X'` is the pull-back
of the round on `X`, the invariant `s` being the same on both. -/
private theorem bmoStepTwoAux_fieldChange {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B) {m : ℕ} (hm : 1 ≤ m) {d d' : ℕ} (hd : d ∈ Set.Icc a b)
    (hd' : d' ∈ Set.Icc a b) :
    ∀ (q : ℕ) (t t' : MarkedTriple.{u}) (h : t'.X ⟶ t.X) (σ : t.k →+* t'.k), FCRel t t' h σ →
      t ∈ markedTriples → t' ∈ markedTriples → dimNat t.X = d → dimNat t'.X = d' →
      bmoStepTwoAux B d' m q t' = (bmoStepTwoAux B d m q t).pullback h
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | q + 1, t, t', h, σ, hR, ht, ht', hdt, hdt' => by
    have hT : IsTriple t.sX t.I t.E := ht
    have hT' : IsTriple t'.sX t'.I t'.E := ht'
    have hσeq := hR.bmoStepTwoOrder_eq ht ht' m
    rw [bmoStepTwoAux, bmoStepTwoAux]
    by_cases h0 : bmoStepTwoOrder m t = 0
    · rw [if_pos (by rw [hσeq]; exact h0), if_pos h0]; rfl
    rw [if_neg (by rw [hσeq]; exact h0), if_neg h0]
    have hσ : maxOrderAlong (nonmonomialPart t.I t.E) (⟨t.I, m⟩ : MarkedIdeal t.X).cosupport =
        (bmoStepTwoOrder m t : ℕ∞) :=
      (ENat.coe_toNat (maxOrderAlong_nonmonomialPart_ne_top hT _)).symm
    have hσ' : maxOrderAlong (nonmonomialPart t'.I t'.E) (⟨t'.I, m⟩ : MarkedIdeal t'.X).cosupport =
        (bmoStepTwoOrder m t : ℕ∞) := by
      rw [← hσeq]; exact (ENat.coe_toNat (maxOrderAlong_nonmonomialPart_ne_top hT' _)).symm
    have hσ1 : 1 ≤ bmoStepTwoOrder m t := Nat.one_le_iff_ne_zero.2 h0
    have hne : ∀ {X : Scheme.{u}} (N : X.IdealSheafData) (Z : Set X),
        maxOrderAlong N Z = (bmoStepTwoOrder m t : ℕ∞) → Nonempty X := by
      intro X N Z hZ
      by_contra hX
      rw [not_nonempty_iff] at hX
      have : maxOrderAlong N Z = 0 := by simp [maxOrderAlong]
      rw [hZ, Nat.cast_eq_zero] at this
      exact h0 this
    haveI := hne _ _ hσ
    haveI := hne _ _ hσ'
    have hK := maxOrder_mixedIdeal_le t.sX t.I t.E m _ hT hm hσ hσ1
    have hK' := maxOrder_mixedIdeal_le t'.sX t'.I t'.E m _ hT' hm hσ' hσ1
    have hmσ : 1 ≤ m * bmoStepTwoOrder m t := Nat.one_le_iff_ne_zero.2 (by positivity)
    have hMI := hR.mixedIdeal_eq ht ht' m (bmoStepTwoOrder m t)
    have hτ : (⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩ :
        FieldBlowupTriple.{u}) ∈ idealTriplesOfDim (Set.Icc a b) (m * bmoStepTwoOrder m t) :=
      ⟨isTriple_mixedIdeal hT m _,
        ⟨d, hd, by rw [← hdt]; exact krullDim_eq_dimNat _ hT.2.2.1 hT.2.2.2.1⟩, hK⟩
    have hτ' : (⟨⟨t'.X, (mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h, t'.E⟩, t'.k,
        t'.sX⟩ : FieldBlowupTriple.{u}) ∈
          idealTriplesOfDim (Set.Icc a b) (m * bmoStepTwoOrder m t) :=
      ⟨hMI ▸ isTriple_mixedIdeal hT' m _,
        ⟨d', hd', by rw [← hdt']; exact krullDim_eq_dimNat _ hT'.2.2.1 hT'.2.2.2.1⟩, hMI ▸ hK'⟩
    have hround := hR.round_eq hB ht' hmσ _ hτ hτ'
    rw [hdt, hdt'] at hround
    obtain ⟨F, hFB, -, -⟩ := hB _ hmσ
    have hS := F.isOrderMTripleSeq _ hτ
    have hS' := F.isOrderMTripleSeq _ hτ'
    rw [hFB] at hS hS'
    change ClosedBlowupSequence.IsOrderMTripleSeq t.sX (mixedIdeal t.I t.E m (bmoStepTwoOrder m t))
      t.E _ (B (dimNat t.X) _
        ⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩) at hS
    change ClosedBlowupSequence.IsOrderMTripleSeq t'.sX
      ((mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h) t'.E _ (B (dimNat t'.X) _
        ⟨⟨t'.X, (mixedIdeal t.I t.E m (bmoStepTwoOrder m t)).comap h, t'.E⟩, t'.k, t'.sX⟩) at hS'
    rw [hdt] at hS
    rw [hdt', hround, ← hMI] at hS'
    set S : ClosedBlowupSequence t.X := B d (m * bmoStepTwoOrder m t)
      ⟨⟨t.X, mixedIdeal t.I t.E m (bmoStepTwoOrder m t), t.E⟩, t.k, t.sX⟩ with hSdef
    obtain ⟨i, hi⟩ := exists_truncate_eq S
    have hS1 :=
      (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal t.sX
        t.I t.E m _ hT hm hσ1 hK _ hS i).1
    rw [hi] at hS1
    obtain ⟨i', hi'⟩ := exists_truncate_eq (S.pullback h)
    have hS1' :=
      (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_truncate_of_isOrderMTripleSeq_mixedIdeal t'.sX
        t'.I t'.E m _ hT' hm hσ1 hK' _ hS' i').1
    rw [hi'] at hS1'
    dsimp only
    rw [hσeq, hMI, hround, ClosedBlowupSequence.append_pullback]
    congr 1
    have he1 : t.endOf m S ∈ markedTriples := isTriple_end _ _ _ _ hS1
    have he1' : t'.endOf m (S.pullback h) ∈ markedTriples := isTriple_end _ _ _ _ hS1'
    have ih := bmoStepTwoAux_fieldChange hB hm hd hd' q (t.endOf m S) (t'.endOf m (S.pullback h))
      (S.pullbackHom h) σ (hR.endOf_pullback ht ht' m S hS1) he1
      he1' ((dimNat_target_of_isOrderGe _ _ _ _ hS1).trans hdt)
      ((dimNat_target_of_isOrderGe _ _ _ _ hS1').trans hdt')
    exact (ite_pos_eq _ _ he1').trans (ih.trans
      (congrArg (fun T => ClosedBlowupSequence.pullback T (S.pullbackHom h))
        (ite_pos_eq _ _ he1).symm))

end Steps

/-! ### Step 3 under a field change -/

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

/-- A prime divisor contains its generic point. -/
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
      by_contra h0
      exact hD (hF D h0)
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

/-- A monomial order reduction sequence has no empty blow-ups (it is its own reduction, by the
smooth case of `MonomialData.monomialOrderReduction_eq_pullback_reduction` along `𝟙`). -/
private theorem hasNoEmptyBlowups_monomialOrderReduction (t : MarkedTriple.{u})
    (ht : t ∈ markedTriples) (U : t.X.Opens) (m : ℕ) :
    ((restrictData t U).monomialOrderReduction m).HasNoEmptyBlowups := by
  have hT : IsTriple t.sX t.I t.E := ht
  obtain ⟨htU, hC⟩ := isMonomialData_restrict t.sX t.I t.E hT U
  haveI : CharZero t.k := ht.1
  have hqc : QuasiCompact (𝟙 (U : Scheme.{u}) ≫ (restrictData t U).sX) := by
    rw [Category.id_comp]; exact hC.2.2.1
  have key := MonomialData.monomialOrderReduction_eq_pullback_reduction (restrictData t U) hC
    ‹_› (𝟙 _) (Or.inl ⟨inferInstance, hqc⟩) (restrictData t U)
    (OrderedDivisor.comap_id _).symm (by
      change monomialPartCoeff _ _ = _
      simp only [Scheme.IdealSheafData.comap_id]
      exact monomialPartCoeff_eq_multAt _ htU) m
  rw [ClosedBlowupSequence.reduction_pullback] at key
  change _ = ClosedBlowupSequence.reduction _ at key
  rw [key]
  exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _

/-- **Step 3 under a field change.** If `V = h⁻¹U`, the extension by closure of the monomial
order reduction on `V` is the pull-back of the one on `U`. -/
private theorem extendByClosure_monomialOrderReduction_fieldChange {t t' : MarkedTriple.{u}}
    {h : t'.X ⟶ t.X} {σ : t.k →+* t'.k} (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (ht' : t' ∈ markedTriples) (m : ℕ) (U : t.X.Opens) (V : t'.X.Opens) (hV : V = h ⁻¹ᵁ U) :
    ((restrictData t' V).monomialOrderReduction m).extendByClosure V.ι =
      (((restrictData t U).monomialOrderReduction m).extendByClosure U.ι).pullback h := by
  subst hV
  have hT : IsTriple t.sX t.I t.E := ht
  have hT' : IsTriple t'.sX t'.I t'.E := ht'
  haveI := isNoetherian_of_isTriple hT
  haveI := isNoetherian_of_isTriple hT'
  haveI : CharZero t.k := ht.1
  have hh := hR.isReducedFlatBaseChange ht
  have sqU := isPullback_morphismRestrict h U
  have hhU : IsReducedFlatBaseChange (h ∣_ U) := hh.of_isPullback sqU.flip
  haveI := hhU.flat
  haveI : Surjective h := ⟨hR.surjective⟩
  haveI : Surjective (h ∣_ U) :=
    MorphismProperty.of_isPullback (P := @Surjective) sqU.flip inferInstance
  obtain ⟨htU, hC⟩ := isMonomialData_restrict t.sX t.I t.E hT U
  obtain ⟨htV, -⟩ := isMonomialData_restrict t'.sX t'.I t'.E hT' (h ⁻¹ᵁ U)
  have hcomp : (h ∣_ U) ≫ U.ι = (h ⁻¹ᵁ U).ι ≫ h := morphismRestrict_ι h U
  have hIV : (t.I.comap U.ι).comap (h ∣_ U) = t'.I.comap (h ⁻¹ᵁ U).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, hcomp, Scheme.IdealSheafData.comap_comp, ← hR.hI]
  have hEV : (t.E.comap U.ι).comap (h ∣_ U) = t'.E.comap (h ⁻¹ᵁ U).ι := by
    rw [OrderedDivisor.comap_comap, hcomp, ← OrderedDivisor.comap_comap, ← hR.hE]
  have hsq : IsPullback (h ∣_ U) ((h ⁻¹ᵁ U).ι ≫ t'.sX) (U.ι ≫ t.sX)
      (Spec.map (CommRingCat.ofHom σ)) := sqU.paste_vert hR.sq
  haveI : LocallyOfFiniteType ((h ⁻¹ᵁ U).ι ≫ t'.sX) := htV.2.2.1
  haveI : QuasiCompact ((h ⁻¹ᵁ U).ι ≫ t'.sX) := htV.2.2.2.1
  have hM := monomialPart_comap (U.ι ≫ t.sX) htU ((h ⁻¹ᵁ U).ι ≫ t'.sX) htV.2.1 (h ∣_ U) hhU
  rw [hIV, hEV] at hM
  have key := MonomialData.monomialOrderReduction_eq_pullback_reduction (restrictData t U) hC
    ‹_› (h ∣_ U) (Or.inr ⟨t'.k, inferInstance, σ, _, hsq⟩) (restrictData t' (h ⁻¹ᵁ U))
    hEV.symm (by
      change monomialPartCoeff _ _ = fun D' => (multAt ((monomialPart _ _).comap _) _).toNat
      rw [← hM]
      exact monomialPartCoeff_eq_multAt _ htV) m
  rw [ClosedBlowupSequence.reduction_eq_self (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
    (hasNoEmptyBlowups_monomialOrderReduction t ht U m) (h ∣_ U))] at key
  rw [key]
  exact (Kollar.extendByClosure_pullback _ (hasReducedCentres_monomialOrderReductionFrom m _ _ _)
    U.ι h hh (h ⁻¹ᵁ U).ι (h ∣_ U) sqU.flip).symm

end StepThree

/-! ### The functor `𝓑𝓜𝓞` under a field change -/

section Main

/-- **`𝓑𝓜𝓞` under a field change up to isomorphism.** -/
private theorem bmoFunctor_eq_pullback_of_fcRel {a b m : ℕ} {B : UnmarkedFamily.{u}}
    (hB : IsOrderReductionFamily a b B) (hm : 1 ≤ m) {t t' : MarkedTriple.{u}}
    {h : t'.X ⟶ t.X} {σ : t.k →+* t'.k} (hR : FCRel t t' h σ) (ht : t ∈ markedTriples)
    (ht' : t' ∈ markedTriples) (hd : dimNat t.X ∈ Set.Icc a b)
    (hd' : dimNat t'.X ∈ Set.Icc a b) :
    bmoFunctor B (dimNat t'.X) m t' = (bmoFunctor B (dimNat t.X) m t).pullback h := by
  have hmax := hR.maxOrder_nonmonomialPart_eq ht ht'
  have hS1 : bmoStepOne B (dimNat t'.X) m t' = (bmoStepOne B (dimNat t.X) m t).pullback h := by
    unfold bmoStepOne
    rw [hmax]
    exact bmoStepOneAux_fieldChange hB hm hd hd' _ t t' h σ hR ht ht' rfl rfl
  have hG1 := (isOrderGeMarkedTripleSeq_bmoStepOne hB hm ht hd).1
  have hG1' := (isOrderGeMarkedTripleSeq_bmoStepOne hB hm ht' hd').1
  rw [hS1] at hG1'
  unfold bmoFunctor
  dsimp only
  rw [if_pos ht, if_pos ht', hS1]
  set S₁ := bmoStepOne B (dimNat t.X) m t with hS₁def
  have R1 := hR.endOf_pullback ht ht' m S₁ hG1
  have he1 : t.endOf m S₁ ∈ markedTriples := isTriple_end _ _ _ _ hG1
  have he1' : t'.endOf m (S₁.pullback h) ∈ markedTriples := isTriple_end _ _ _ _ hG1'
  have hd1 : dimNat (t.endOf m S₁).X = dimNat t.X := dimNat_target_of_isOrderGe S₁ _ _ _ hG1
  have hd1' : dimNat (t'.endOf m (S₁.pullback h)).X = dimNat t'.X :=
    dimNat_target_of_isOrderGe _ _ _ _ hG1'
  have hS2 : bmoStepTwo B (dimNat t'.X) m (t'.endOf m (S₁.pullback h)) =
      (bmoStepTwo B (dimNat t.X) m (t.endOf m S₁)).pullback (S₁.pullbackHom h) := by
    unfold bmoStepTwo
    rw [R1.bmoStepTwoOrder_eq he1 he1' m]
    exact bmoStepTwoAux_fieldChange hB hm hd hd' _ _ _ _ σ R1 he1 he1' hd1 hd1'
  have hG2 := (isOrderGeMarkedTripleSeq_bmoStepTwo hB hm he1 (hd1 ▸ hd)).1
  rw [hd1] at hG2
  have hG2' := (isOrderGeMarkedTripleSeq_bmoStepTwo hB hm he1' (hd1' ▸ hd')).1
  rw [hd1', hS2] at hG2'
  rw [if_pos he1, if_pos he1', hS2]
  set S₂ := bmoStepTwo B (dimNat t.X) m (t.endOf m S₁) with hS₂def
  have R2 := R1.endOf_pullback he1 he1' m S₂ hG2
  have he2 : (t.endOf m S₁).endOf m S₂ ∈ markedTriples := isTriple_end _ _ _ _ hG2
  have he2' : (t'.endOf m (S₁.pullback h)).endOf m (S₂.pullback (S₁.pullbackHom h)) ∈
      markedTriples := isTriple_end _ _ _ _ hG2'
  have hV : (nonmonomialPart ((t'.endOf m (S₁.pullback h)).endOf m
        (S₂.pullback (S₁.pullbackHom h))).I ((t'.endOf m (S₁.pullback h)).endOf m
        (S₂.pullback (S₁.pullbackHom h))).E).support.compl =
      (S₂.pullbackHom (S₁.pullbackHom h)) ⁻¹ᵁ
        (nonmonomialPart ((t.endOf m S₁).endOf m S₂).I
          ((t.endOf m S₁).endOf m S₂).E).support.compl := by
    rw [R2.nonmonomialPart_eq he2 he2']
    ext x
    exact not_congr (mem_support_comap_iff _ _ x)
  have h3 := extendByClosure_monomialOrderReduction_fieldChange R2 he2 he2' m _ _ hV
  haveI := (hR.isReducedFlatBaseChange ht).flat
  haveI : Surjective h := ⟨hR.surjective⟩
  refine Eq.trans ?_ (ClosedBlowupSequence.reduction_eq_self
    (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _
      (ClosedBlowupSequence.hasNoEmptyBlowups_reduction _) h))
  refine Eq.trans ?_ (ClosedBlowupSequence.reduction_pullback_reduction _ h).symm
  refine Eq.trans ?_ (congrArg ClosedBlowupSequence.reduction
    ((ClosedBlowupSequence.append_pullback S₁ _ h).trans
      (congrArg (ClosedBlowupSequence.append (S₁.pullback h))
        (ClosedBlowupSequence.append_pullback S₂ _ (S₁.pullbackHom h)))).symm)
  exact congrArg (fun T => ((S₁.pullback h).append
    ((S₂.pullback (S₁.pullbackHom h)).append T)).reduction) h3

end Main

/-- **Kollár, Thm. 3.107 (2), change of fields.** Let `𝓑` be an order-reduction family on
dimensions `a, …, b` (`IsOrderReductionFamily`) and `m ≥ 1`. On the class of marked triples
`(X, I, m, E)` with `a ≤ dim X ≤ b`, the functor
`(X, I, m, E) ↦ bmoFunctor B (dim X) m (X, I, m, E)` commutes with change of fields
(`CommutesWithFieldChangeOnMarked`). -/
@[mmp "thm_kr3e_order_reduction_marked_commutes_field_change"]
public theorem commutesWithFieldChangeOnMarked_bmoFunctor {a b m : ℕ} (B : UnmarkedFamily.{u})
    (hB : IsOrderReductionFamily a b B) (hm : 1 ≤ m) :
    CommutesWithFieldChangeOnMarked (markedTriplesOfDim (Set.Icc a b) m)
      (fun t _ => bmoFunctor B (dimNat t.X) m t) := by
  intro t ht L _ σ hL
  exact bmoFunctor_eq_pullback_of_fcRel hB hm ⟨IsPullback.of_hasPullback _ _, rfl, rfl⟩ ht.1 hL.1
    (dimNat_mem_of_hasDimensionIn ht.2.2) (dimNat_mem_of_hasDimensionIn hL.2.2)

end FieldChange

/-! ### The second inductive step -/

/-- A marked triple of marking `m` and dimension in `N` is one of dimension `dimNat t.X`. -/
private theorem mem_markedTriplesOfDim_singleton_dimNat {t : MarkedTriple.{u}} {N : Set ℕ}
    {m : ℕ} (ht : t ∈ markedTriplesOfDim N m) :
    dimNat t.X ∈ N ∧ t ∈ markedTriplesOfDim {dimNat t.X} m :=
  ⟨dimNat_mem_of_hasDimensionIn ht.2.2, ht.1, ht.2.1, hasDimensionIn_dimNat ht.2.2⟩

/-- The class of triples of dimension in `N` grows with `N`. -/
private theorem idealTriplesOfDim_mono {N N' : Set ℕ} (h : N ⊆ N') {m : ℕ} :
    idealTriplesOfDim.{u} N m ⊆ idealTriplesOfDim N' m :=
  fun _ ⟨ht, ⟨n, hn, hX⟩, hI⟩ => ⟨ht, ⟨n, h hn, hX⟩, hI⟩

/-- If `B` is an order-reduction family on dimensions `a, …, b` whose members ignore empty
entries, then `(d, μ) ↦ bmoFunctor B d μ` is a marked order-reduction family on them. -/
private theorem isMarkedOrderReductionFamily_bmoFunctor_of_ignoresEmptyEntries {a b : ℕ}
    (B : UnmarkedFamily.{u}) (hB : IsOrderReductionFamily a b B)
    (hBe : ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t)) :
    IsMarkedOrderReductionFamily a b (fun d μ => bmoFunctor B d μ) := by
  intro μ hμ
  have seq (t : MarkedTriple.{u}) (ht : t ∈ markedTriplesOfDim (Set.Icc a b) μ) :=
    bmoFunctor_isOrderGeMarkedTripleSeq B hB hμ (mem_markedTriplesOfDim_singleton_dimNat ht).1 t
      (mem_markedTriplesOfDim_singleton_dimNat ht).2
  exact ⟨⟨fun t _ => bmoFunctor B (dimNat t.X) μ t, fun t ht => (seq t ht).1,
      fun t ht => (seq t ht).2⟩, fun _ _ => rfl,
    fun t ht => maxOrder_markedTransform_bmoFunctor_lt B hB hμ
      (mem_markedTriplesOfDim_singleton_dimNat ht).1 t
      (mem_markedTriplesOfDim_singleton_dimNat ht).2,
    commutesWithSmoothOnMarked_bmoFunctor B hB hBe hμ,
    commutesWithFieldChangeOnMarked_bmoFunctor B hB hμ⟩

/-- Order reduction functors `𝓑𝓞_μ` for ideals on dimensions `a, …, b` that ignore empty
entries assemble into an order-reduction family `𝓑_{d,μ} := 𝓑𝓞_μ` each of whose members, restricted
to a single dimension `d ∈ [a, b]`, ignores empty entries. -/
private theorem exists_isOrderReductionFamily {a b : ℕ}
    (hF : ∀ μ : ℕ, 1 ≤ μ →
      ∃ F : OrderBlowupSequenceFunctor.{u} μ (idealTriplesOfDim (Set.Icc a b) μ),
        IsOrderReductionFunctorIdeals μ _ F ∧
          IgnoresEmptyEntries (idealTriplesOfDim (Set.Icc a b) μ) F.toFun) :
    ∃ B : UnmarkedFamily.{u}, IsOrderReductionFamily a b B ∧
      ∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
        IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t) := by
  choose F hF hFe using hF
  classical
  let B : UnmarkedFamily.{u} := fun _ μ t =>
    if h : 1 ≤ μ ∧ t ∈ idealTriplesOfDim (Set.Icc a b) μ then (F μ h.1).toFun t h.2
    else .nil t.X
  refine ⟨B, fun μ hμ => ⟨F μ hμ, fun t ht => by simp [B, hμ, ht], hF μ hμ⟩,
    fun d' hd' μ hμ t ht => ?_⟩
  have ht' := idealTriplesOfDim_mono (Set.singleton_subset_iff.mpr hd') ht
  obtain ⟨hde, heq⟩ := hFe μ hμ t ht'
  exact ⟨⟨hde.1, ht.2.1, hde.2.2⟩, by simpa [B, hμ, ht', hde] using heq⟩
/-- **Kollár 3.70.2.** Let `a ≤ b`. If `B` is an order-reduction family on dimensions `a, …, b`
(`IsOrderReductionFamily`) and each `B d μ` ignores empty entries (`IgnoresEmptyEntries`),
then the marked family `(d, μ) ↦ bmoFunctor B d μ` is a marked
order-reduction family on dimensions `a, …, b` (`IsMarkedOrderReductionFamily`). In particular,
if for every `μ ≥ 1` there is an order reduction functor for ideals of order `μ` on dimensions
`Set.Icc a b` (`IsOrderReductionFunctorIdeals`) ignoring empty entries, then for every `μ ≥ 1`
there is an order reduction functor for marked ideals of order `μ` on dimensions `Set.Icc a b`
(`IsOrderReductionFunctorMarked`). -/
@[mmp "thm_kr3e_main_inductive_step_two"]
public theorem isMarkedOrderReductionFamily_bmoFunctor {a b : ℕ} (hab : a ≤ b) :
    (∀ B : UnmarkedFamily.{u}, IsOrderReductionFamily a b B →
      (∀ d' ∈ Set.Icc a b, ∀ μ : ℕ, 1 ≤ μ →
        IgnoresEmptyEntries (idealTriplesOfDim {d'} μ) (fun t _ => B d' μ t)) →
      IsMarkedOrderReductionFamily a b (fun d μ => bmoFunctor B d μ)) ∧
    ((∀ μ : ℕ, 1 ≤ μ →
        ∃ F : OrderBlowupSequenceFunctor.{u} μ (idealTriplesOfDim (Set.Icc a b) μ),
          IsOrderReductionFunctorIdeals μ _ F ∧
            IgnoresEmptyEntries (idealTriplesOfDim (Set.Icc a b) μ) F.toFun) →
      ∀ μ : ℕ, 1 ≤ μ →
        ∃ G : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim (Set.Icc a b) μ),
          IsOrderReductionFunctorMarked μ _ G) := by
  refine ⟨isMarkedOrderReductionFamily_bmoFunctor_of_ignoresEmptyEntries, fun hF μ hμ => ?_⟩
  obtain ⟨B, hB, hBe⟩ := exists_isOrderReductionFamily hF
  obtain ⟨G, -, hG⟩ := isMarkedOrderReductionFamily_bmoFunctor_of_ignoresEmptyEntries B hB hBe μ hμ
  exact ⟨G, hG⟩

/-! ### Deleting the empty entries of an ordered divisor -/

section Reindex

variable {X : Scheme.{u}}

open Classical in
/-- The indices of the nonempty entries. -/
private noncomputable def flatIdx (E : OrderedDivisor X) : List (Fin E.s) :=
  (List.finRange E.s).filter fun i => E.E i ≠ ⊤

/-- Distinct positions of `flatIdx E` are distinct indices. -/
private theorem injective_flatIdx_get (E : OrderedDivisor X) :
    Function.Injective (flatIdx E).get :=
  List.nodup_iff_injective_get.1 ((List.nodup_finRange _).filter _)

/-- Every index of a nonempty entry occurs in `flatIdx E`. -/
private theorem exists_flatIdx_get (E : OrderedDivisor X) (i : Fin E.s) (hi : E.E i ≠ ⊤) :
    ∃ j, (flatIdx E).get j = i :=
  List.mem_iff_get.1 (by simp [flatIdx, hi])

variable {Λ Λ' : Type*} (E : Λ → X.IdealSheafData) (g : Λ' → Λ)

/-- A property of all entries may be checked on the nonempty ones. -/
private theorem forall_iff_forall_comp (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i)
    (R : X.IdealSheafData → Prop) (hR : R ⊤) :
    (∀ i, R (E i)) ↔ ∀ j, R (E (g j)) := by
  refine ⟨fun h j => h _, fun h i => ?_⟩
  by_cases hi : E i = ⊤
  · rwa [hi]
  · obtain ⟨j, rfl⟩ := hg i hi
    exact h j

/-- The coordinate assignment of an snc family at a point may be taken over the nonempty
entries. -/
private theorem exists_coord_iff (hginj : Function.Injective g)
    (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) (x : X) {n : ℕ} (z : Fin n → X.presheaf.stalk x) :
    (∃ c : {i // x ∈ (E i).support} → Fin n,
        (∀ i, IdealSheafData.stalk (E i.1) x = Ideal.span {z (c i)}) ∧ Function.Injective c) ↔
      ∃ c : {j // x ∈ (E (g j)).support} → Fin n,
        (∀ j, IdealSheafData.stalk (E (g j.1)) x = Ideal.span {z (c j)}) ∧
          Function.Injective c := by
  let φ : {j // x ∈ (E (g j)).support} → {i // x ∈ (E i).support} := fun j => ⟨g j.1, j.2⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => Subtype.ext (hginj (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨j, hj⟩ := hg i.1 fun h => by
      have := i.2
      rw [h, Scheme.IdealSheafData.support_top] at this
      exact this
    exact ⟨⟨j, hj ▸ i.2⟩, Subtype.ext hj⟩
  let e := Equiv.ofBijective φ hφ
  constructor
  · rintro ⟨c, hc, hinj⟩
    exact ⟨c ∘ φ, fun j => hc (φ j), hinj.comp hφ.1⟩
  · rintro ⟨c, hc, hinj⟩
    refine ⟨c ∘ e.symm, fun i => ?_, hinj.comp e.symm.injective⟩
    have h := hc (e.symm i)
    have hi : g (e.symm i).1 = i.1 := congrArg Subtype.val (e.apply_symm_apply i)
    rwa [hi] at h

/-- Whether a family is snc may be checked on its nonempty entries. -/
private theorem isSNCFamily_iff_comp {k : Type u} [Field k] (sX : X ⟶ Spec (.of k))
    (hginj : Function.Injective g) (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i) :
    IsSNCFamily sX E ↔ IsSNCFamily sX (E ∘ g) := by
  refine and_congr (forall_iff_forall_comp E g hg (fun D => IsReduced D.subscheme ∧
      MMP.Mori.IsPureCodimOne D.support ∧ MMP.Mori.IsSmoothScheme (D.subschemeι ≫ sX))
      ⟨?_, ?_, ?_⟩)
    (forall_congr' fun x => exists_congr fun n => exists_congr fun z => ?_)
  · exact isReduced_of_isAffine_isReduced _
  · intro W hW
    have h := hW.prop
    rw [Scheme.IdealSheafData.support_top] at h
    obtain ⟨w, hw⟩ := W.isIrreducible.nonempty
    exact (h hw).elim
  · unfold MMP.Mori.IsSmoothScheme
    ext x
    exact isEmptyElim x
  · simp only [exists_and_left]
    exact and_congr_right' (exists_coord_iff E g hginj hg x z)

end Reindex

/-- Deleting the empty entries does not change whether `E` is an ordered snc divisor. -/
private theorem isOrderedSNC_deleteEmpty_iff {X : Scheme.{u}} (E : OrderedDivisor X)
    {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) :
    E.IsOrderedSNC sX ↔ E.deleteEmpty.IsOrderedSNC sX :=
  and_congr
    (forall_iff_forall_comp E.E _ (exists_flatIdx_get E)
      (fun D => IsReduced D.subscheme ∧ Stacks.Divisors.IsEffectiveCartierDivisor D)
      ⟨isReduced_of_isAffine_isReduced _, Stacks.Divisors.isEffectiveCartierDivisor_top⟩)
    (isSNCFamily_iff_comp E.E _ sX (injective_flatIdx_get E) (exists_flatIdx_get E))

/-- `(X, I, E^♭)` lies in every class `idealTriplesOfDim N μ` that `(X, I, E)` lies in. -/
private theorem deleteEmpty_mem_idealTriplesOfDim {N : Set ℕ} {μ : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim N μ) : t.deleteEmpty ∈ idealTriplesOfDim N μ := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hd, hm⟩ := ht
  exact ⟨⟨h1, h2, h3, h4, h5, h6, (isOrderedSNC_deleteEmpty_iff t.E t.sX).1 h7⟩, hd, hm⟩

/-! ### Locality of the functors in the family -/

/-- The Step-1 recursion in dimension `d` only reads `B d`. -/
private theorem bmoStepOneAux_congr {B B' : UnmarkedFamily.{u}} {d : ℕ} (h : B d = B' d)
    (m : ℕ) : bmoStepOneAux B d m = bmoStepOneAux B' d m := by
  funext q
  induction q with
  | zero =>
    funext t
    simp only [bmoStepOneAux]
  | succ q ih =>
    funext t
    simp only [bmoStepOneAux]
    rw [h, ih]

/-- The Step-2 recursion in dimension `d` only reads `B d`. -/
private theorem bmoStepTwoAux_congr {B B' : UnmarkedFamily.{u}} {d : ℕ} (h : B d = B' d)
    (m : ℕ) : bmoStepTwoAux B d m = bmoStepTwoAux B' d m := by
  funext q
  induction q with
  | zero =>
    funext t
    simp only [bmoStepTwoAux]
  | succ q ih =>
    funext t
    simp only [bmoStepTwoAux]
    rw [h, ih]

/-- `bmoFunctor B d` only reads `B d`. -/
private theorem bmoFunctor_congr {B B' : UnmarkedFamily.{u}} {d : ℕ} (h : B d = B' d) :
    bmoFunctor B d = bmoFunctor B' d := by
  funext m t
  have h₁ : bmoStepOne B d m = bmoStepOne B' d m := by
    funext t
    unfold bmoStepOne
    rw [bmoStepOneAux_congr h]
  have h₂ : bmoStepTwo B d m = bmoStepTwo B' d m := by
    funext t
    unfold bmoStepTwo
    rw [bmoStepTwoAux_congr h]
  unfold bmoFunctor
  rw [h₁, h₂]

/-- `bdFunctor M n` only reads `M (n - 1)`. -/
private theorem bdFunctor_congr {M M' : MarkedFamily.{u}} {n : ℕ} (h : M (n - 1) = M' (n - 1)) :
    bdFunctor M n = bdFunctor M' n := by
  funext m j t
  simp only [bdFunctor]
  rw [h]

/-- The divisor separation recursion on `t` only reads `M (dimNat t.X - 1)`. -/
private theorem divisorSeparationAux_congr {M M' : MarkedFamily.{u}} (m : ℕ)
    (t : FieldBlowupTriple.{u}) (h : M (dimNat t.X - 1) = M' (dimNat t.X - 1)) :
    divisorSeparationAux M m t = divisorSeparationAux M' m t := by
  funext j
  induction j with
  | zero => simp only [divisorSeparationAux]
  | succ j ih =>
    simp only [divisorSeparationAux]
    rw [ih, bdFunctor_congr h]

open Classical in
/-- `boMaximalContact M m t` only reads `M (dimNat t.X - 1)`. -/
private theorem boMaximalContact_congr {M M' : MarkedFamily.{u}} (m : ℕ)
    (t : FieldBlowupTriple.{u}) (h : M (dimNat t.X - 1) = M' (dimNat t.X - 1)) :
    boMaximalContact M m t = boMaximalContact M' m t := by
  funext H
  have h₁ : divisorSeparationSequence M m t = divisorSeparationSequence M' m t := by
    unfold divisorSeparationSequence
    rw [divisorSeparationAux_congr m t h]
  exact congrArg₂ (fun (P : ClosedBlowupSequence t.X)
      (bd : ℕ → (v : FieldBlowupTriple.{u}) → ClosedBlowupSequence v.X) =>
    let t' := t.endOf P
    let H' : t'.X.IdealSheafData := (P.restrictHom H).ker
    let V : t'.X.Opens :=
      (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
    let EV : OrderedDivisor V :=
      ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
        fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩
    let tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, EV⟩, t'.k, V.ι ≫ t'.sX⟩
    let BV : ClosedBlowupSequence V :=
      if (V : Set t'.X).Nonempty ∧ IsTriple tV.sX tV.I tV.E then bd 0 tV else .nil _
    (P.append (BV.extendByClosure V.ι)).reduction) h₁ (congrFun (bdFunctor_congr h) m)

/-- `boLocal M m t` only reads `M (dimNat t.X - 1)`. -/
private theorem boLocal_congr {M M' : MarkedFamily.{u}} (m : ℕ) (t : FieldBlowupTriple.{u})
    (h : M (dimNat t.X - 1) = M' (dimNat t.X - 1)) : boLocal M m t = boLocal M' m t := by
  unfold boLocal
  rw [boMaximalContact_congr (M' := M') m.factorial
    ⟨⟨t.X, wellTunedIdeal t.sX t.I, t.E⟩, t.k, t.sX⟩ h]

open Classical in
/-- A choice made from equal predicates is the same. -/
private theorem dite_exists_choose_congr {α : Sort*} {p q : α → Prop} (h : p = q) (a : α) :
    (if h : ∃ x, p x then h.choose else a) = (if h : ∃ x, q x then h.choose else a) := by
  subst h; rfl

/-- `boFunctor M n` only reads `M (n - 1)`. -/
private theorem boFunctor_congr {M M' : MarkedFamily.{u}} {n : ℕ} (h : M (n - 1) = M' (n - 1)) :
    boFunctor M n = boFunctor M' n := by
  funext m t
  unfold boFunctor
  refine dite_exists_choose_congr (funext fun B => propext ?_) _
  refine forall_congr' fun X' => forall_congr' fun g => forall_congr' fun _ =>
    forall_congr' fun _ => forall_congr' fun hl => ?_
  obtain ⟨k, hk, hX⟩ := hl.2.1
  have hdim : dimNat (t.pullback g).X = n := by
    rw [Set.mem_singleton_iff] at hk; subst hk; simp [dimNat, hX]
  rw [boLocal_congr m _ (hdim ▸ h)]

/-! ### The canonical families -/

/-- The marked family from which `boFamily (n + 1)` is built agrees with `bmoFamily` in
dimensions `≤ n`. -/
private theorem bmoFamilyOf_boFamilyUpTo {n d : ℕ} (hd : d ≤ n) :
    bmoFamilyOf (boFamilyUpTo.{u} n) n d = bmoFamily.{u} d := by
  have h : (boFamilyUpTo.{u} n).truncate d = (boFamilyUpTo.{u} d).truncate d := by
    funext d' μ t
    simp only [UnmarkedFamily.truncate]
    split_ifs with h'
    · rw [boFamilyUpTo_of_le (h'.trans hd), boFamilyUpTo_of_le h']
    · rfl
  funext μ t
  simp only [bmoFamilyOf, if_pos hd, h, bmoFamily]

/-- `boFamily (n + 1)` is `boFunctor` of the marked family built from `boFamily` up to
`n`. -/
private theorem boFamily_succ (n : ℕ) :
    boFamily.{u} (n + 1) = boFunctor (bmoFamilyOf (boFamilyUpTo.{u} n) n) (n + 1) := by
  funext μ t
  simp [boFamily, boFamilyUpTo]

/-- In dimensions `≤ n + 1`, the functor `boFunctor` of the marked family from which
`boFamily (n + 1)` is built is `boFamily`. -/
private theorem boFunctor_bmoFamilyOf_boFamilyUpTo {n d : ℕ} (hd : d ≤ n) :
    boFunctor (bmoFamilyOf (boFamilyUpTo.{u} n) n) (d + 1) = boFamily.{u} (d + 1) := by
  rw [boFamily_succ d]
  refine boFunctor_congr ?_
  simp only [Nat.add_sub_cancel]
  rw [bmoFamilyOf_boFamilyUpTo hd, bmoFamilyOf_boFamilyUpTo le_rfl]

/-- `bmoFamily d` is `bmoFunctor B d` for any family `B` with `B d = boFamily d`. -/
private theorem bmoFamily_eq {B : UnmarkedFamily.{u}} {d : ℕ} (h : B d = boFamily.{u} d) :
    bmoFamily.{u} d = bmoFunctor B d := by
  refine bmoFunctor_congr ?_
  rw [h]
  funext μ t
  simp [UnmarkedFamily.truncate, boFamily]
/-- Being a marked order-reduction family on dimensions `a, …, b` only depends on the members
in those dimensions. -/
private theorem isMarkedOrderReductionFamily_congr {a b : ℕ} {M M' : MarkedFamily.{u}}
    (hM : IsMarkedOrderReductionFamily a b M) (h : ∀ d ∈ Set.Icc a b, M d = M' d) :
    IsMarkedOrderReductionFamily a b M' := by
  intro μ hμ
  obtain ⟨F, hF, hF'⟩ := hM μ hμ
  refine ⟨F, fun t ht => ?_, hF'⟩
  rw [hF, h _ (dimNat_mem_of_hasDimensionIn ht.2.2)]

/-- Transfer of the marked order-reduction property to `bmoFamily`. -/
private theorem isMarkedOrderReductionFamily_bmoFamily_of {a b : ℕ} {B : UnmarkedFamily.{u}}
    (hB : ∀ d ∈ Set.Icc a b, B d = boFamily.{u} d)
    (h : IsMarkedOrderReductionFamily a b (fun d μ => bmoFunctor B d μ)) :
    IsMarkedOrderReductionFamily.{u} a b bmoFamily.{u} :=
  isMarkedOrderReductionFamily_congr h fun d hd => (bmoFamily_eq (hB d hd)).symm

/-- `bmoFamily d` ignores empty entries once every `boFamily d μ` does. -/
private theorem ignoresEmptyEntriesMarked_bmoFamily_of {d : ℕ}
    (hB : ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d} μ) (fun t _ => boFamily.{u} d μ t))
    {m : ℕ} (hm : 1 ≤ m) :
    IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} m) (fun t _ => bmoFamily.{u} d m t) := by
  rw [bmoFamily_eq (B := boFamily.{u}) rfl]
  refine ignoresEmptyEntriesMarked_bmoFunctor (a := d) (b := d) _ (fun d' hd' μ hμ => ?_) hm
    ⟨le_rfl, le_rfl⟩
  obtain rfl : d' = d := le_antisymm hd'.2 hd'.1
  exact hB μ hμ

/-- The joint induction: every `boFamily d μ`, `d ≤ n`, ignores empty entries, and `bmoFamily`
is a marked order-reduction family on dimensions `0, …, n`. -/
private theorem ignoresEmptyEntries_boFamily_and_isMarkedOrderReductionFamily_bmoFamily (n : ℕ) :
    (∀ d ≤ n, ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {d} μ) (fun t _ => boFamily.{u} d μ t)) ∧
    IsMarkedOrderReductionFamily.{u} 0 n bmoFamily.{u} := by
  induction n with
  | zero =>
    have hE : ∀ d ≤ 0, ∀ μ : ℕ, 1 ≤ μ →
        IgnoresEmptyEntries (idealTriplesOfDim {d} μ) (fun t _ => boFamily.{u} d μ t) := by
      intro d hd μ _ t ht
      obtain rfl : d = 0 := by omega
      exact ⟨deleteEmpty_mem_idealTriplesOfDim ht, rfl⟩
    refine ⟨hE, ?_⟩
    have hB0 : IsOrderReductionFamily 0 0 boFamily.{u} := by
      intro μ hμ
      rw [Set.Icc_self]
      obtain ⟨F, hF, hF'⟩ := (isOrderReductionFunctor_identity_dim_zero.{u} μ hμ).1
      refine ⟨F, fun t ht => ?_, hF'⟩
      have hd : dimNat t.X = 0 := dimNat_mem_of_hasDimensionIn ht.2.1
      rw [hF, hd]
      rfl
    have hB : ∀ d ∈ Set.Icc 0 0, boFamily.{u} d = boFamily d := fun _ _ => rfl
    exact isMarkedOrderReductionFamily_bmoFamily_of hB
      ((isMarkedOrderReductionFamily_bmoFunctor (le_refl 0)).1 _ hB0
        fun d hd μ hμ => hE d hd.2 μ hμ)
  | succ n ih =>
    obtain ⟨ihE, ihM⟩ := ih
    set M := bmoFamilyOf (boFamilyUpTo.{u} n) n
    have hM : IsMarkedOrderReductionFamily 0 n M :=
      isMarkedOrderReductionFamily_congr ihM fun _ hd => (bmoFamilyOf_boFamilyUpTo hd.2).symm
    have hMe : ∀ d ∈ Set.Icc 0 (n + 1 - 1), ∀ ν : ℕ, 1 ≤ ν →
        IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} ν) (fun t _ => M d ν t) := by
      intro d hd ν hν
      have hd' : d ≤ n := by simpa using hd.2
      simp only [M]
      rw [bmoFamilyOf_boFamilyUpTo hd']
      exact ignoresEmptyEntriesMarked_bmoFamily_of (ihE d hd') hν
    have hE : ∀ d ≤ n + 1, ∀ μ : ℕ, 1 ≤ μ →
        IgnoresEmptyEntries (idealTriplesOfDim {d} μ) (fun t _ => boFamily.{u} d μ t) := by
      intro d hd μ hμ
      rcases Nat.lt_or_ge n d with h | h
      · obtain rfl : d = n + 1 := by omega
        rw [boFamily_succ]
        exact ignoresEmptyEntries_boFunctor _ (by omega) hM hMe hμ
      · exact ihE d h μ hμ
    refine ⟨hE, ?_⟩
    let B₁ : UnmarkedFamily.{u} := fun d μ t => if d = 0 then .nil t.X else boFunctor M d μ t
    have hB₁ : IsOrderReductionFamily 0 (n + 1) B₁ :=
      (isOrderReductionFamily_boFunctor (n := n + 1) (by omega)).1 M hM hMe
    have hB : ∀ d ∈ Set.Icc 0 (n + 1), B₁ d = boFamily.{u} d := by
      intro d hd
      rcases d with _ | e
      · funext μ t; rfl
      · funext μ t
        simp only [B₁, Nat.add_one_ne_zero, ↓reduceIte]
        exact congr_fun₂ (boFunctor_bmoFamilyOf_boFamilyUpTo (by have := hd.2; omega)) μ t
    refine isMarkedOrderReductionFamily_bmoFamily_of hB
      ((isMarkedOrderReductionFamily_bmoFunctor (Nat.zero_le (n + 1))).1 B₁ hB₁
        fun d hd μ hμ => ?_)
    rw [hB d hd]
    exact hE d hd.2 μ hμ
/-- **Kollár 3.70.** For every `n`, the canonical marked family `bmoFamily` is a marked
order-reduction family on dimensions `0, …, n` (`IsMarkedOrderReductionFamily`). -/
@[mmp "lem_kr3e_order_reduction_families_induction"]
public theorem isMarkedOrderReductionFamily_bmoFamily (n : ℕ) :
    IsMarkedOrderReductionFamily.{u} 0 n bmoFamily.{u} :=
  (ignoresEmptyEntries_boFamily_and_isMarkedOrderReductionFamily_bmoFamily n).2

/-! ### The canonical families ignore empty entries -/

/-- Every `𝓑𝓞_{n,μ}` ignores empty entries. -/
private theorem ignoresEmptyEntries_boFamily (n : ℕ) :
    ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntries (idealTriplesOfDim {n} μ) (fun t _ => boFamily.{u} n μ t) :=
  (ignoresEmptyEntries_boFamily_and_isMarkedOrderReductionFamily_bmoFamily n).1 n le_rfl

/-- A blow-up sequence without empty blow-ups starting with an empty scheme is empty. -/
private theorem eq_nil_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (B : ClosedBlowupSequence X)
    (hB : B.HasNoEmptyBlowups) : B = .nil X := by
  cases B with
  | nil => rfl
  | cons Z B =>
    refine (hB.1 ?_).elim
    rw [← Scheme.IdealSheafData.support_eq_bot_iff]
    ext x
    exact isEmptyElim x

/-- **The canonical `𝓑𝓜𝓞_m` ignores empty entries.** For `m ≥ 1`, the assignment
`t ↦ bmoFamily (dimNat t.X) m t` on the marked triples of marking `m`
(`markedTriplesOfMarking m`) ignores empty entries (`IgnoresEmptyEntriesMarked`): for each such
`t`, `t.deleteEmpty` is again a marked triple of marking `m` and is assigned the same blow-up
sequence. -/
@[mmp "thm_kr3e_bmo_ignores_empty_entries"]
public theorem ignoresEmptyEntriesMarked_bmoFamily {m : ℕ} (hm : 1 ≤ m) :
    IgnoresEmptyEntriesMarked (markedTriplesOfMarking.{u} m)
      (fun t _ => bmoFamily (dimNat t.X) m t) := by
  intro t ht
  obtain ⟨htr, htm⟩ := ht
  have hdel : t.deleteEmpty ∈ markedTriplesOfMarking m := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := htr
    exact ⟨⟨h1, h2, h3, h4, h5, h6, (isOrderedSNC_deleteEmpty_iff t.E t.sX).1 h7⟩, htm⟩
  refine ⟨hdel, ?_⟩
  by_cases hX : IsEmpty t.X
  · haveI : IsEmpty t.deleteEmpty.X := hX
    exact (eq_nil_of_isEmpty _ (ClosedBlowupSequence.hasNoEmptyBlowups_reduction _)).trans
      (eq_nil_of_isEmpty _ (ClosedBlowupSequence.hasNoEmptyBlowups_reduction _)).symm
  · rw [not_isEmpty_iff] at hX
    have hdim : HasDimensionIn t.X {dimNat t.X} :=
      ⟨_, rfl, krullDim_eq_dimNat t.sX htr.2.2.1 htr.2.2.2.1⟩
    exact (ignoresEmptyEntriesMarked_bmoFamily_of (ignoresEmptyEntries_boFamily _) hm t
      ⟨htr, htm, hdim⟩).2

/-! ### Order reduction on all dimensions -/

/-- Being an order-reduction family on dimensions `a, …, b` only depends on the members in
those dimensions. -/
private theorem isOrderReductionFamily_congr {a b : ℕ} {B B' : UnmarkedFamily}
    (h : ∀ d, a ≤ d → d ≤ b → B d = B' d) (hB : IsOrderReductionFamily a b B) :
    IsOrderReductionFamily a b B' := by
  intro μ hμ
  obtain ⟨F, hF, hF'⟩ := hB μ hμ
  refine ⟨F, fun t ht => ?_, hF'⟩
  obtain ⟨h1, h2⟩ := dimNat_mem_of_hasDimensionIn ht.2.1
  rw [hF, h _ h1 h2]

/-- `boFamily` is an order-reduction family on dimensions `0, …, n + 1`. -/
private theorem isOrderReductionFamily_boFamily (n : ℕ) :
    IsOrderReductionFamily 0 (n + 1) boFamily := by
  refine isOrderReductionFamily_congr (fun d _ hd => ?_)
    ((isOrderReductionFamily_boFunctor (Nat.succ_pos n)).1 bmoFamily
      (isMarkedOrderReductionFamily_bmoFamily n)
      fun _ _ _ hμ => ignoresEmptyEntriesMarked_bmoFamily_of (ignoresEmptyEntries_boFamily _) hμ)
  rcases d with _ | e
  · funext μ t; rfl
  · funext μ t
    simp only [Nat.add_one_ne_zero, ↓reduceIte, boFamily, boFamilyUpTo,
      show ¬ e + 1 ≤ e by omega]
    rw [boFunctor_congr (M' := bmoFamilyOf (boFamilyUpTo e) e)]
    funext μ' t'
    simp [bmoFamilyOf, bmoFamily]

/-- A triple of any dimension `≤ n` lies in the class of dimensions `0, …, n`. -/
private theorem mem_idealTriplesOfDim_Icc {m n : ℕ} {t : FieldBlowupTriple.{u}}
    (ht : t ∈ idealTriplesOfDim Set.univ m) (hn : dimNat t.X ≤ n) :
    t ∈ idealTriplesOfDim (Set.Icc 0 n) m := by
  obtain ⟨h1, ⟨k, -, hk⟩, h3⟩ := ht
  have : dimNat t.X = k := dimNat_mem_of_hasDimensionIn (N := {k}) ⟨k, rfl, hk⟩
  exact ⟨h1, ⟨k, ⟨Nat.zero_le _, this ▸ hn⟩, hk⟩, h3⟩
/-- **Kollár Thm. 3.68.** For every `m ≥ 1`, the assignment `(X, I, E) ↦ boFamily (dim X) m
(X, I, E)` is an order reduction functor for ideals of order `m` on all triples with
`maxord I ≤ m` (`IsOrderReductionFunctorIdeals` on dimensions `Set.univ`). -/
@[mmp "thm_kr3e_order_reduction_ideals"]
public theorem exists_isOrderReductionFunctorIdeals_boFamily (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : OrderBlowupSequenceFunctor.{u} m (idealTriplesOfDim Set.univ m),
      (∀ t ht, F.toFun t ht = boFamily.{u} (dimNat t.X) m t) ∧
        IsOrderReductionFunctorIdeals m Set.univ F := by
  choose F hF hFR using fun n => isOrderReductionFamily_boFamily.{u} n m hm
  let G : OrderBlowupSequenceFunctor.{u} m (idealTriplesOfDim Set.univ m) :=
    { toFun := fun t _ => boFamily (dimNat t.X) m t
      isOrderMTripleSeq := fun t ht => by
        have h := (F (dimNat t.X)).isOrderMTripleSeq t
          (mem_idealTriplesOfDim_Icc ht (Nat.le_succ _))
        rwa [hF] at h
      hasNoEmptyBlowups := fun t ht => by
        have h := (F (dimNat t.X)).hasNoEmptyBlowups t
          (mem_idealTriplesOfDim_Icc ht (Nat.le_succ _))
        rwa [hF] at h }
  refine ⟨G, fun _ _ => rfl, fun t ht => ?_, ⟨?_, ?_⟩, ?_⟩
  · have h := (hFR (dimNat t.X)).1 t (mem_idealTriplesOfDim_Icc ht (Nat.le_succ _))
    rwa [hF] at h
  · intro t ht Y h hs hsurj hlft hqc hY
    have key := (hFR (max (dimNat t.X) (dimNat (t.pullback h).X))).2.1.1 t
      (mem_idealTriplesOfDim_Icc ht (by omega)) Y h hs hsurj hlft hqc
      (mem_idealTriplesOfDim_Icc hY (by omega))
    rwa [hF, hF] at key
  · intro t ht Y h hs hlft hqc hY
    have key := (hFR (max (dimNat t.X) (dimNat (t.pullback h).X))).2.1.2 t
      (mem_idealTriplesOfDim_Icc ht (by omega)) Y h hs hlft hqc
      (mem_idealTriplesOfDim_Icc hY (by omega))
    rwa [hF, hF] at key
  · intro t ht L _ σ hL
    have key := (hFR (max (dimNat t.X) (dimNat (t.fieldChange σ).X))).2.2 t
      (mem_idealTriplesOfDim_Icc ht (by omega)) L σ
      (mem_idealTriplesOfDim_Icc hL (by omega))
    rwa [hF, hF] at key

/-- A marked triple of any dimension `≤ n` lies in the class of dimensions `0, …, n`. -/
private theorem mem_markedTriplesOfDim_Icc {m n : ℕ} {t : MarkedTriple.{u}}
    (ht : t ∈ markedTriplesOfDim Set.univ m) (hn : dimNat t.X ≤ n) :
    t ∈ markedTriplesOfDim (Set.Icc 0 n) m := by
  obtain ⟨h1, h2, ⟨k, -, hk⟩⟩ := ht
  have : dimNat t.X = k := by simp [dimNat, hk]
  exact ⟨h1, h2, ⟨k, ⟨Nat.zero_le _, this ▸ hn⟩, hk⟩⟩

/-- A marked family that is a marked order-reduction family on dimensions `0, …, n` for every
`n` defines, by `t ↦ M (dim X) m t`, an order reduction functor for marked ideals of order `m`
on all dimensions. -/
private theorem exists_isOrderReductionFunctorMarked_univ {M : MarkedFamily.{u}}
    (hM : ∀ n, IsMarkedOrderReductionFamily 0 n M) (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim Set.univ m),
      (∀ t ht, F.toFun t ht = M (dimNat t.X) m t) ∧
        IsOrderReductionFunctorMarked m Set.univ F := by
  choose F hF hFR using fun n => hM n m hm
  refine ⟨{ toFun := fun t _ => M (dimNat t.X) m t
            isOrderGeMarkedTripleSeq := fun t ht => hF _ t (mem_markedTriplesOfDim_Icc ht le_rfl) ▸
              (F _).isOrderGeMarkedTripleSeq t (mem_markedTriplesOfDim_Icc ht le_rfl)
            hasNoEmptyBlowups := fun t ht => hF _ t (mem_markedTriplesOfDim_Icc ht le_rfl) ▸
              (F _).hasNoEmptyBlowups t (mem_markedTriplesOfDim_Icc ht le_rfl) },
    fun _ _ => rfl, fun t ht => ?_, ⟨fun t ht Y h hs hsurj hlft hqc hY => ?_,
      fun t ht Y h hs hlft hqc hY => ?_⟩, fun t ht L _ σ hL => ?_⟩
  · have := (hFR (dimNat t.X)).1 t (mem_markedTriplesOfDim_Icc ht le_rfl)
    rwa [hF] at this
  · simpa [hF] using (hFR (max (dimNat t.X) (dimNat (t.pullback h).X))).2.1.1 t
      (mem_markedTriplesOfDim_Icc ht (le_max_left ..)) Y h hs hsurj hlft hqc
      (mem_markedTriplesOfDim_Icc hY (le_max_right ..))
  · simpa [hF] using (hFR (max (dimNat t.X) (dimNat (t.pullback h).X))).2.1.2 t
      (mem_markedTriplesOfDim_Icc ht (le_max_left ..)) Y h hs hlft hqc
      (mem_markedTriplesOfDim_Icc hY (le_max_right ..))
  · simpa [hF] using (hFR (max (dimNat t.X) (dimNat (t.fieldChange σ).X))).2.2 t
      (mem_markedTriplesOfDim_Icc ht (le_max_left ..)) L σ
      (mem_markedTriplesOfDim_Icc hL (le_max_right ..))
/-- **Kollár Thm. 3.69.** For every `m ≥ 1`, the assignment
`(X, I, m, E) ↦ bmoFamily (dim X) m (X, I, m, E)` is an order reduction functor for marked ideals
of order `m` on all marked triples of marking `m` (`IsOrderReductionFunctorMarked` on dimensions
`Set.univ`). -/
@[mmp "thm_kr3e_order_reduction_marked_ideals"]
public theorem exists_isOrderReductionFunctorMarked_bmoFamily (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : OrderGeBlowupSequenceFunctor.{u} (markedTriplesOfDim Set.univ m),
      (∀ t ht, F.toFun t ht = bmoFamily.{u} (dimNat t.X) m t) ∧
        IsOrderReductionFunctorMarked m Set.univ F :=
  exists_isOrderReductionFunctorMarked_univ isMarkedOrderReductionFamily_bmoFamily m hm

end MMP.Resolution

end
