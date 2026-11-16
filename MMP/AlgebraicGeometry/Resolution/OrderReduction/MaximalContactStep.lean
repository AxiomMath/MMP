module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.Resolution.OrderReduction.Functor
import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.GenericPointCoheight
import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinCompletedCap
import MMP.AlgebraicGeometry.Resolution.Blowup.Charts
import MMP.AlgebraicGeometry.Divisor.SNC
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.Resolution.DivisorialPart
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.ConstructionFunctorial
import MMP.AlgebraicGeometry.Resolution.SNCFieldChange
import MMP.AlgebraicGeometry.Resolution.SNCPullback
import MMP.AlgebraicGeometry.Resolution.SNCRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatPullback
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatDescent
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.FlatBaseChange
import MMP.AlgebraicGeometry.Resolution.MarkedIdeal.Cosupport
import MMP.AlgebraicGeometry.Resolution.OrderRestriction
import MMP.AlgebraicGeometry.Resolution.BlowupSequence.Restriction
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MonomialStepTermination
import MMP.AlgebraicGeometry.Resolution.MaximalContact.AlongBlowupSequence
import MMP.AlgebraicGeometry.Resolution.MaximalContact.MaximalCoefficientIdeal
import MMP.AlgebraicGeometry.Resolution.MaximalContact.GoingUpUniqueness
import MMP.AlgebraicGeometry.Resolution.OrderReduction.DivisorSeparation
import MMP.AlgebraicGeometry.Resolution.OrderReduction.BdFunctorFieldChange
import MMP.AlgebraicGeometry.Resolution.OrderReduction.BdFunctorSmoothPullback
import MMP.AlgebraicGeometry.Morphisms.SmoothHypersurfaceFlag
import MMP.AlgebraicGeometry.Resolution.TransformRestriction
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MaxOrderControlledTransform
import MMP.AlgebraicGeometry.Resolution.OrderReduction.TuningOfIdeals
import MMP.AlgebraicGeometry.Resolution.LinearBlowupCharts
import MMP.AlgebraicGeometry.Resolution.OrderReduction.OrderMSequenceCosupport
import MMP.AlgebraicGeometry.Resolution.OrderReduction.MixedIdealMonomialReduction

/-!
# The maximal-contact step `𝓑𝓞^H_m` of order reduction

Fix `N ≥ 1` and a marked order-reduction family `𝓜` on dimensions `0, …, N - 1`. Let
`(X, J, E)` be a triple with `1 ≤ dim X ≤ N` and `maxord J = m ≥ 1`, and `H` an MC-hypersurface
for `J`: a smooth hypersurface with `𝒪_X(-H) ⊆ MC(J)`. The blow-up sequence `𝓑𝓞^H_m(X, J, E)`
is the divisor separation sequence `Π_sep`, ending with `(X', J', E')`, followed by the extension
by closure of `𝓑𝓓_{dim X, m, 1}` applied on the open `V = X' ∖ ⋃_{i < s} E'^i` to the triple
`(V, J'|_V, (H' ∩ V, E'^s ∩ V, …))`, `H'` the birational transform of `H`, with empty blow-ups
deleted.

This file proves the properties of `𝓑𝓞^H_m` used to build the order-reduction functor.

* It is a smooth blow-up sequence of order `m`: neither piece has an empty blow-up, `Π_sep` is
  of order `m`, and so is the extension by closure, its centres lying over
  `cosupp(J', m) ⊆ V`.
* It reduces the maximal order. If the end `(X_r, J_r, E_r)` had `maxord J_r = m`, the
  birational transform `H_r` of `H` would be an MC-hypersurface for `J_r`, so
  `cosupp(J_r, m) ⊆ H_r`. But over `V` the sequence is `𝓑𝓓`, which separates the cosupport from
  the first divisor, and `H_r` lies in that divisor there.
* It does not depend on `H`. Only `H' ∩ V` involves `H`, and the two `𝓑𝓓` pieces agree after
  pull-back to a finite affine cover `Y → V`. There uniqueness of maximal contact (Kollár,
  Thm. 3.97) for the MC-invariant `W_{m!}(J')` makes them étale equivalent, hence equal.
* It commutes with smooth morphisms up to deleting empty blow-ups, and with change of the base
  field. Blow-ups and birational and total transforms commute with flat base change, so each
  piece of the construction pulls back.

## Main results

* `MMP.Resolution.boMaximalContact_isOrderMTripleSeq`
* `MMP.Resolution.maxOrder_endOf_boMaximalContact_lt`
* `MMP.Resolution.boMaximalContact_eq_of_isMCHypersurface`
* `MMP.Resolution.boMaximalContact_pullback`
* `MMP.Resolution.boMaximalContact_fieldChange`

## Implementation notes

Over a non-surjective smooth `g` a centre may have empty preimage, and the pulled-back sequence
then contains empty blow-ups. `boMaximalContact_pullback` therefore compares with the
`ClosedBlowupSequence.reduction` of the pull-back, which deletes them, and it assumes that every
member of `𝓜` ignores empty entries of the ordered divisor, or that `g` is surjective. For a
surjective `g`, in particular the projection of a field change, no blow-up is empty, the reduction
is the pull-back itself, and the ordered total transforms on the two sides agree exactly, so the
assumption on `𝓜` is not needed.

The ordered total transforms on the two sides of a smooth pull-back agree only up to empty
entries after the first `s`; `AgreeUpToEmpty` records this, and `𝓑𝓓` does not see such entries.

In the independence proof, the affine cover `Y = ⊔ U_i → V` is an open immersion on each piece,
so it preserves dimension, equidimensionality and maximal order, which puts the pulled-back
triples in the class on which `𝓑𝓓` commutes with smooth morphisms.

## References

* [J. Kollár, *Lectures on resolution of singularities*, Thm. 3.103 and 3.104]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral CategoryTheory.catToReflQuiver

universe u

namespace MMP.Resolution

/-! ### Orders and dimensions -/

/-- The order of an ideal does not drop under a local homomorphism. -/
private theorem idealOrder_le_idealOrder_map {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (φ : R →+* S) [IsLocalHom φ] (I : Ideal R) :
    idealOrder I ≤ idealOrder (I.map φ) := by
  unfold idealOrder
  refine iSup₂_mono' fun j hj => ⟨j, (Ideal.map_mono hj).trans ?_, le_rfl⟩
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap φ).ge) j

/-- Along an open immersion, `ord_u (j^*I) = ord_{j u} I`. -/
private theorem multAt_comap_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (K : X.IdealSheafData) (y : Y) : multAt (K.comap f) y = multAt K (f y) := by
  unfold multAt
  rw [IdealSheafData.stalk_comap]
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  have he : ((f.stalkMap y).hom : _ →+* _) = e.toRingHom := rfl
  rw [he]
  haveI : IsLocalHom e.toRingHom := ⟨fun a ha => by simpa using ha.map e.symm.toRingHom⟩
  haveI : IsLocalHom e.symm.toRingHom := ⟨fun a ha => by simpa using ha.map e.toRingHom⟩
  refine le_antisymm ?_ (idealOrder_le_idealOrder_map _ _)
  have hss : ((IdealSheafData.stalk K (f y)).map e.toRingHom).map e.symm.toRingHom =
      IdealSheafData.stalk K (f y) := by
    rw [Ideal.map_map]
    simp
  exact (idealOrder_le_idealOrder_map _ _).trans_eq (congrArg idealOrder hss)

/-- Along an open immersion, `maxord (j^*I) ≤ maxord I`. -/
private theorem maxOrder_comap_le {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (K : X.IdealSheafData) : maxOrder (K.comap f) ≤ maxOrder K :=
  iSup₂_le fun y _ => by
    rw [multAt_comap_of_isOpenImmersion f]
    exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt K z) _ (Set.mem_univ _)

/-- The dimension of an irreducible component of a scheme locally of finite type over a field is
the local dimension at its generic point. -/
private theorem topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint {k : Type u} [Field k]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] {Z : Set Y}
    (hZ : Z ∈ irreducibleComponents Y) :
    topologicalKrullDim Z = topologicalKrullDimAt Y hZ.1.genericPoint := by
  have hZc := isClosed_of_mem_irreducibleComponents Z hZ
  have hη := hZ.1.isGenericPoint_genericPoint_closure
  rw [hZc.closure_eq] at hη
  have hηZ : hZ.1.genericPoint ∈ Z := hη.mem
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k Y s]
  refine le_antisymm
    (le_iSup₂ (f := fun Z' (_ : Z' ∈ {Z' | Z' ∈ irreducibleComponents Y ∧
      hZ.1.genericPoint ∈ Z'}) => topologicalKrullDim Z') Z ⟨hZ, hηZ⟩) (iSup₂_le fun Z' hZ' => ?_)
  have hle : Z ⊆ Z' := by
    rw [← (show closure {hZ.1.genericPoint} = Z from hη)]
    exact (isClosed_of_mem_irreducibleComponents Z' hZ'.1).closure_subset_iff.2
      (Set.singleton_subset_iff.2 hZ'.2)
  rw [(hZ.2 hZ'.1.1 hle).antisymm hle]

/-- In an equidimensional scheme locally of finite type over a field, the local dimension at
every point is the dimension of every irreducible component. -/
private theorem topologicalKrullDimAt_eq_of_mem_irreducibleComponents {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : TopologicalSpace.Equidimensional X) (x : X) {C : Set X}
    (hC : C ∈ irreducibleComponents X) : topologicalKrullDimAt X x = topologicalKrullDim C := by
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X s x]
  refine le_antisymm (iSup₂_le fun D hD => (hX D hD.1 C hC).le) ?_
  exact (hX _ (irreducibleComponent_mem_irreducibleComponents x) C hC).symm.le.trans
    (le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ irreducibleComponents X ∧ x ∈ D}) =>
      topologicalKrullDim D) _ ⟨irreducibleComponent_mem_irreducibleComponents x,
        mem_irreducibleComponent⟩)

/-- A space with the dimension of all its irreducible components equal to `d` has dimension `d`
when nonempty. -/
private theorem topologicalKrullDim_eq_of_forall_components {Y : Type*} [TopologicalSpace Y] (y : Y)
    {d : WithBot ℕ∞} (h : ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z = d) :
    topologicalKrullDim Y = d := by
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents Y]
  refine le_antisymm (iSup₂_le fun Z hZ => (h Z hZ).le) ?_
  rw [← h _ (irreducibleComponent_mem_irreducibleComponents y)]
  exact le_iSup₂ (f := fun Z (_ : Z ∈ irreducibleComponents Y) => topologicalKrullDim Z) _
    (irreducibleComponent_mem_irreducibleComponents y)

/-- An open subscheme of an equidimensional scheme locally of finite type over a field is
equidimensional. -/
private theorem equidimensional_opens {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : TopologicalSpace.Equidimensional X) (U : X.Opens) :
    TopologicalSpace.Equidimensional U := by
  have key : ∀ Z ∈ irreducibleComponents U, ∀ C ∈ irreducibleComponents X,
      topologicalKrullDim Z = topologicalKrullDim C := fun Z hZ C hC =>
    (topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint (U.ι ≫ s) hZ).trans <|
      (U.2.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq _).symm.trans
        (topologicalKrullDimAt_eq_of_mem_irreducibleComponents s hX _ hC)
  intro Z hZ W hW
  have hC := irreducibleComponent_mem_irreducibleComponents hZ.1.nonempty.some.1
  rw [key Z hZ _ hC, key W hW _ hC]

private theorem topologicalKrullDim_opens_of_equidimensional {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hX : TopologicalSpace.Equidimensional X) (U : X.Opens) (hU : (U : Set X).Nonempty) :
    topologicalKrullDim U = topologicalKrullDim X := by
  obtain ⟨x, hx⟩ := hU
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hX' : topologicalKrullDim X ≤ topologicalKrullDim C :=
    (topologicalKrullDim_eq_of_forall_components x fun D hD => hX D hD C hC).le
  refine le_antisymm (topologicalKrullDim_subspace_le X (U : Set X)) (hX'.trans ?_)
  have h1 : topologicalKrullDim C ≤ topologicalKrullDimAt X x :=
    (topologicalKrullDimAt_eq_of_mem_irreducibleComponents s hX x hC).ge
  have h2 : topologicalKrullDimAt X x = topologicalKrullDimAt (U : Set X) ⟨x, hx⟩ :=
    U.2.isOpenEmbedding_subtypeVal.topologicalKrullDimAt_eq ⟨x, hx⟩
  exact h1.trans (h2 ▸ _root_.topologicalKrullDimAt_le_topologicalKrullDim _)

private theorem dimNat_eq_of_topologicalKrullDim_eq {X Y : Scheme.{u}}
    (h : topologicalKrullDim X = topologicalKrullDim Y) : dimNat X = dimNat Y := by
  unfold dimNat
  rw [h]

private theorem dimNat_eq_of_eq {X : Scheme.{u}} {n : ℕ}
    (hd : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞)) : dimNat X = n := by
  simp [dimNat, hd]

/-! ### Sequences of order `m` -/

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

/-- Blowing up an equidimensional scheme locally of finite type over a field along a closed
subscheme all of whose components have positive codimension keeps the dimension. -/
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

/-- Along a smooth blow-up sequence of order `m` starting with a triple with `maxord ≤ m`, the
end keeps the dimension, has `maxord ≤ m`, and its ordered divisor is at least as long. -/
private theorem end_of_isOrderMTripleSeq {k : Type u} [Field k] (m : ℕ) (d : WithBot ℕ∞) :
    ∀ {X : Scheme} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X),
      B.IsOrderMTripleSeq s I E m → maxOrder I ≤ m → topologicalKrullDim X = d →
      topologicalKrullDim B.target = d ∧ maxOrder (B.controlledTransform I) ≤ m ∧
        E.s ≤ (B.orderedTotalTransform E).s
  | _, .nil _, _, _, _, _, hmax, hd => ⟨hd, hmax, le_rfl⟩
  | _, .cons Z B, s, I, E, hB, hmax, hd => by
    obtain ⟨hT, hZ, hc, -, hEq, hB'⟩ := hB
    obtain ⟨-, hX, hlft, hqc, hequi, hI, -⟩ := hT
    have hmax' : maxOrder (MMP.Resolution.controlledTransform Z I) ≤ m := by
      haveI := Aux.smooth_of_isSmoothScheme' s hX
      haveI := Aux.smooth_of_isSmoothScheme' _ hZ
      refine (maxOrder_controlledTransform_le s Z hc I hI fun W hW => le_antisymm ?_
        (hmax.trans (hEq W hW).ge)).trans hmax
      exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) _ (Set.mem_univ _)
    obtain ⟨h1, h2, h3⟩ := end_of_isOrderMTripleSeq m d B _ _ _ hB' hmax'
      ((topologicalKrullDim_blowUp s hequi Z hc).trans hd)
    exact ⟨h1, h2, (Nat.le_succ _).trans h3⟩

/-- The first `j ≤ s` steps of the divisor separation sequence are of order `m`. -/
private theorem isOrderMTripleSeq_divisorSeparationAux {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I ≤ m) (j : ℕ) (hj : j ≤ t.E.s) :
    (divisorSeparationAux M m t j).IsOrderMTripleSeq t.sX t.I t.E m := by
  have hP := divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax
  obtain ⟨C, hC⟩ := ClosedBlowupSequence.exists_divisorSeparationAux_add_eq_append M m t j
    (t.E.s - j)
  rw [Nat.add_sub_cancel' hj] at hC
  unfold divisorSeparationSequence at hP
  rw [hC] at hP
  exact ((ClosedBlowupSequence.isOrderMTripleSeq_append_iff m _ _ _ _ _).1 hP).1

/-- A nonempty centre along which `I` has order `≥ m` forces `m ≤ maxord I`. -/
private theorem le_maxOrder_of_orderAlongGE {X : Scheme} (I Z : X.IdealSheafData) (hZ : Z ≠ ⊤)
    (m : ℕ) (h : OrderAlongGE I (Z.support : Set X) m) : (m : ℕ∞) ≤ maxOrder I := by
  obtain ⟨x, hx⟩ := TopologicalSpace.Closeds.coe_nonempty.2
    (mt (Scheme.IdealSheafData.support_eq_bot_iff Z).1 hZ)
  obtain ⟨W, hW, -⟩ := exists_mem_componentsOf hx
  exact (h W hW).trans (le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) _
    (Set.mem_univ _))

/-- The start of a smooth blow-up sequence of order `m` is a triple. -/
private theorem isTriple_of_isOrderMTripleSeq {k : Type u} [Field k] {m : ℕ}
    {X : Scheme.{u}} {B : ClosedBlowupSequence X} {s : X ⟶ Spec (.of k)}
    {I : X.IdealSheafData} {E : OrderedDivisor X} (h : B.IsOrderMTripleSeq s I E m) :
    IsTriple s I E := by
  cases B with
  | nil => exact h
  | cons => exact h.1

/-- For an MC-hypersurface `H`, the restriction `(V, J'|_V, (H' ∩ V, E_-))` to `V` of the end of
the divisor separation sequence, `H'` the birational transform of `H`, is a triple. -/
private theorem isTriple_restrict_divisorSeparationSequence {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H : t.X.IdealSheafData}
    (hH : IsMCHypersurface t.sX t.I H) :
    let P := divisorSeparationSequence M m t
    let t' := t.endOf P
    let V : t'.X.Opens :=
      (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
    let tV : t'.X.IdealSheafData → FieldBlowupTriple.{u} := fun H' =>
      ⟨⟨V, t'.I.comap V.ι,
        ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData)
          (H'.comap V.ι) fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩⟩, t'.k, V.ι ≫ t'.sX⟩
    (V : Set t'.X).Nonempty →
      IsTriple (tV (P.restrictHom H).ker).sX (tV (P.restrictHom H).ker).I
        (tV (P.restrictHom H).ker).E := by
  intro P t' V tV hV
  have hP := divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le
  have htr : IsTriple t'.sX t'.I t'.E :=
    ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m P _ _ _ hP
  obtain ⟨hs, hsnc⟩ := isOrderedSNC_divisorSeparationSequence M hN hM t ht hdim hn hnN hm hmax hH
  let t'' : FieldBlowupTriple.{u} :=
    ⟨⟨t'.X, t'.I, ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => t'.X.IdealSheafData)
      (P.restrictHom H).ker fun i => t'.E.E ⟨t.E.s + i, by omega⟩⟩⟩, t'.k, t'.sX⟩
  have h'' : t'' ∈ sncTriples :=
    ⟨htr.1, htr.2.1, htr.2.2.1, htr.2.2.2.1, htr.2.2.2.2.2.1, hsnc.1, hsnc.2⟩
  haveI : LocallyOfFiniteType t'.sX := htr.2.2.1
  haveI : QuasiCompact t'.sX := htr.2.2.2.1
  haveI : IsLocallyNoetherian t'.X := LocallyOfFiniteType.isLocallyNoetherian t'.sX
  haveI : CompactSpace t'.X := QuasiCompact.compactSpace_of_compactSpace t'.sX
  haveI : IsNoetherian t'.X := ⟨⟩
  haveI : QuasiCompact (V.ι ≫ t'.sX) := inferInstance
  have hpb := pullback_mem_sncTriples h'' V.ι
  have hE : (tV (P.restrictHom H).ker).E = (t''.pullback V.ι).E := by
    change (⟨_, _⟩ : OrderedDivisor V) = ⟨_, _⟩
    congr 1
    funext i
    refine Fin.cases rfl (fun i => rfl) i
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpb
  refine ⟨h1, h2, h3, h4, equidimensional_opens t'.sX htr.2.2.2.2.1 V, h5, ?_⟩
  rw [hE]
  exact ⟨h6, h7⟩

/-- The open `V = X' ∖ ⋃_{i < s} E'^i`. -/
private def tailOpen (u : FieldBlowupTriple.{u}) (s : ℕ) : u.X.Opens :=
  (⨆ i : Fin u.E.s, if (i : ℕ) < s then (u.E.E i).support else ⊥).compl

private theorem bdFunctor_heq_of_eq (M : MarkedFamily.{u}) (n m j : ℕ)
    {t t' : FieldBlowupTriple.{u}} (h : t = t') : bdFunctor M n m j t ≍ bdFunctor M n m j t' := by
  subst h; rfl

/-! ### Empty blow-ups -/

/-- A concatenation of sequences without empty blow-ups has none. -/
private theorem hasNoEmptyBlowups_append :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (C : ClosedBlowupSequence B.target),
      B.HasNoEmptyBlowups → C.HasNoEmptyBlowups → (B.append C).HasNoEmptyBlowups
  | _, .nil _, _, _, hC => hC
  | _, .cons _ B, C, hB, hC => ⟨hB.1, hasNoEmptyBlowups_append B C hB.2 hC⟩

/-- The extension by closure of a sequence without empty blow-ups has none. -/
private theorem hasNoEmptyBlowups_extendByClosure :
    ∀ {U X : Scheme.{u}} (B : ClosedBlowupSequence U) (ι : U ⟶ X),
      B.HasNoEmptyBlowups → (B.extendByClosure ι).HasNoEmptyBlowups
  | _, _, .nil _, _, _ => trivial
  | _, _, .cons Z B, ι, hB => by
    rw [ClosedBlowupSequence.extendByClosure]
    split_ifs with h
    · refine ⟨fun h' => hB.1 ?_, hasNoEmptyBlowups_extendByClosure B _ hB.2⟩
      rw [← h, h']; simp
    · trivial

/-- `𝓑𝓓` has no empty blow-ups. -/
private theorem hasNoEmptyBlowups_bdFunctor (M : MarkedFamily.{u}) (n m j : ℕ)
    (t : FieldBlowupTriple.{u}) : (bdFunctor M n m j t).HasNoEmptyBlowups := by
  rw [bdFunctor]
  split_ifs
  · exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _
  · trivial

/-- The partial divisor separation sequences have no empty blow-ups. -/
private theorem hasNoEmptyBlowups_divisorSeparationAux (M : MarkedFamily.{u}) (m : ℕ)
    (t : FieldBlowupTriple.{u}) (j : ℕ) :
    (divisorSeparationAux M m t j).HasNoEmptyBlowups := by
  induction j with
  | zero => trivial
  | succ j ih =>
    rw [divisorSeparationAux]
    split_ifs
    · exact hasNoEmptyBlowups_append _ _ ih (hasNoEmptyBlowups_bdFunctor ..)
    · exact ih

/-! ### Components under flat base change -/

section Components

variable {T : Type*} [TopologicalSpace T] [QuasiSober T] [T0Space T]

/-- The closure of a point is an irreducible component of a closed set `D` iff the point lies in
`D` and has no proper generization in `D`. -/
private theorem closure_mem_componentsOf_iff {D : Set T} (hD : IsClosed D) (η : T) :
    closure {η} ∈ componentsOf D ↔ η ∈ D ∧ ∀ z, z ⤳ η → z ∈ D → z = η := by
  constructor
  · intro h
    refine ⟨h.1.2 (subset_closure rfl), fun z hz hzD => ?_⟩
    have h1 : closure {z} ⊆ closure {η} :=
      h.2 ⟨isIrreducible_singleton.closure,
        closure_minimal (Set.singleton_subset_iff.2 hzD) hD⟩ hz.closure_subset
    exact (hz.antisymm (specializes_iff_mem_closure.2 (h1 (subset_closure rfl)))).eq
  · rintro ⟨hηD, hmax⟩
    refine ⟨⟨isIrreducible_singleton.closure,
      closure_minimal (Set.singleton_subset_iff.2 hηD) hD⟩, fun W hW hle => ?_⟩
    have hcW : IsIrreducible (closure W) := hW.1.closure
    obtain ⟨ζ, hζ⟩ := QuasiSober.sober hcW isClosed_closure
    have hζD : ζ ∈ D := closure_minimal hW.2 hD (hζ.mem)
    have hηW : η ∈ closure W := subset_closure (hle (subset_closure rfl))
    have hζη : ζ ⤳ η := by
      rwa [specializes_iff_mem_closure, hζ.def]
    have := hmax ζ hζη hζD
    subst this
    calc W ⊆ closure W := subset_closure
      _ = closure {ζ} := hζ.def.symm

/-- Every component of a closed set is the closure of a point. -/
private theorem exists_eq_closure_of_mem_componentsOf' {D : Set T} (hD : IsClosed D)
    {W : Set T} (hW : W ∈ componentsOf D) : ∃ ξ : T, W = closure {ξ} := by
  have hcl : IsClosed W := by
    have h1 : IsIrreducible (closure W) := hW.1.1.closure
    have h2 : closure W ⊆ D := closure_minimal hW.1.2 hD
    exact closure_subset_iff_isClosed.mp (hW.2 ⟨h1, h2⟩ subset_closure)
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hW.1.1 hcl
  exact ⟨ξ, hξ.def.symm⟩

variable {T' : Type*} [TopologicalSpace T'] [QuasiSober T'] [T0Space T']
  {g : T' → T} (hc : Continuous g) (hgen : GeneralizingMap g)

include hc hgen

/-- The image of the generic point of a component of `g⁻¹S` is the generic point of a component
of `S`, for a generalizing map `g`. -/
private theorem closure_image_mem_componentsOf {S : Set T} (hS : IsClosed S) {η : T'}
    (hη : closure {η} ∈ componentsOf (g ⁻¹' S)) :
    closure {g η} ∈ componentsOf S := by
  rw [closure_mem_componentsOf_iff (hS.preimage hc)] at hη
  rw [closure_mem_componentsOf_iff hS]
  refine ⟨hη.1, fun z hz hzS => ?_⟩
  obtain ⟨η', hη', rfl⟩ := hgen hz
  rw [hη.2 η' hη' hzS]

/-- A component `closure {η}` of `g⁻¹S` lying over the component `closure {g η}` of `S` is a
component of `g⁻¹T` iff `closure {g η}` is a component of `T`, for any closed `T`. -/
private theorem closure_mem_componentsOf_preimage_iff {S T₀ : Set T} (hS : IsClosed S)
    (hT : IsClosed T₀) {η : T'} (hη : closure {η} ∈ componentsOf (g ⁻¹' S)) :
    closure {η} ∈ componentsOf (g ⁻¹' T₀) ↔ closure {g η} ∈ componentsOf T₀ := by
  have hηS := (closure_mem_componentsOf_iff (hS.preimage hc) η).1 hη
  rw [closure_mem_componentsOf_iff (hT.preimage hc), closure_mem_componentsOf_iff hT]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun z hz hzT => ?_⟩
    obtain ⟨η', hη', rfl⟩ := hgen hz
    rw [h2 η' hη' hzT]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun z hz hzT => ?_⟩
    have hgz : g z = g η := h2 (g z) (hz.map hc) hzT
    exact hηS.2 z hz (show g z ∈ S by rw [hgz]; exact hηS.1)

/-- Over a component `closure {ξ}` of `S`, every point of `g⁻¹(closure {ξ})` lies on a component
`closure {η}` of `g⁻¹S` with `g η = ξ`. -/
private theorem exists_closure_mem_componentsOf_preimage {S : Set T} (hS : IsClosed S) {ξ : T}
    (hξ : closure {ξ} ∈ componentsOf S) {y : T'}
    (hy : g y ∈ closure {ξ}) :
    ∃ η, closure {η} ∈ componentsOf (g ⁻¹' S) ∧ y ∈ closure {η} ∧ g η = ξ := by
  have hξS := (closure_mem_componentsOf_iff hS ξ).1 hξ
  obtain ⟨ζ, hζ, hgζ⟩ := hgen (specializes_iff_mem_closure.2 hy)
  have hζS : ζ ∈ g ⁻¹' S := by rw [Set.mem_preimage, hgζ]; exact hξS.1
  obtain ⟨V, hV, hζV⟩ := exists_mem_componentsOf hζS
  obtain ⟨η, rfl⟩ := exists_eq_closure_of_mem_componentsOf' (hS.preimage hc) hV
  refine ⟨η, hV, ?_, ?_⟩
  · exact (specializes_iff_mem_closure.1 (specializes_iff_mem_closure.2 hζV |>.trans hζ))
  · have hη := (closure_mem_componentsOf_iff hS (g η)).1
      (closure_image_mem_componentsOf hc hgen hS hV)
    have h1 : g η ⤳ ξ := by
      rw [← hgζ]; exact (specializes_iff_mem_closure.2 hζV).map hc
    exact (hξS.2 _ h1 hη.1)

/-- **Unions of components under a generalizing map.** For closed `S` and predicates on the
components of `g⁻¹S` and of `S` that agree along `η ↦ g η`, the union of the selected
components of `g⁻¹S` is the inverse image of the union of the selected components of `S`. -/
private theorem iUnion_componentsOf_preimage {S : Set T} (hS : IsClosed S)
    (PY : (V : Set T') → V ∈ componentsOf (g ⁻¹' S) → Prop)
    (PX : (W : Set T) → W ∈ componentsOf S → Prop)
    (hP : ∀ η (hη : closure {η} ∈ componentsOf (g ⁻¹' S)),
      PY _ hη ↔ PX _ (closure_image_mem_componentsOf hc hgen hS hη)) :
    (⋃ (V : Set T') (hV : V ∈ componentsOf (g ⁻¹' S)) (_ : PY V hV), V) =
      g ⁻¹' ⋃ (W : Set T) (hW : W ∈ componentsOf S) (_ : PX W hW), W := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨V, hV, hPV, hyV⟩
    obtain ⟨η, rfl⟩ := exists_eq_closure_of_mem_componentsOf' (hS.preimage hc) hV
    exact ⟨_, closure_image_mem_componentsOf hc hgen hS hV, (hP η hV).1 hPV,
      (specializes_iff_mem_closure.2 hyV).map hc |> specializes_iff_mem_closure.1⟩
  · rintro ⟨W, hW, hPW, hyW⟩
    obtain ⟨ξ, rfl⟩ := exists_eq_closure_of_mem_componentsOf' hS hW
    obtain ⟨η, hη, hyη, rfl⟩ := exists_closure_mem_componentsOf_preimage hc hgen hS hW hyW
    exact ⟨_, hη, (hP η hη).2 hPW, hyη⟩

end Components

section SchemeComponents

variable {X Y : Scheme.{u}}

private theorem irreducibleClosure_closure_singleton (η : X)
    (hη : IsIrreducible (closure {η})) :
    irreducibleClosure hη = IrreducibleCloseds.closureSingleton η := by
  ext1
  change closure (closure {η}) = closure {η}
  exact closure_closure

private theorem codimension_closureSingleton' (x : X) :
    codimension (IrreducibleCloseds.closureSingleton x) = Order.coheight x := by
  rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton x =
    (irreducibleSetEquivPoints (α := X)).symm x from rfl, Order.coheight_orderIso]

/-- A point of a flat morphism of locally Noetherian schemes with no proper generization in its
fibre has the coheight of its image: it is a generic point of its fibre, so Stacks'
`coheight_eq_coheight_base_of_asFiber_mem_genericPoints` applies. -/
private theorem coheight_eq_coheight_of_flat (f : X ⟶ Y) [Flat f] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (x : X) (hx : ∀ z, z ⤳ x → f z = f x → z = x) :
    Order.coheight x = Order.coheight (f x) := by
  refine coheight_eq_coheight_base_of_asFiber_mem_genericPoints f ?_
  rw [Stacks.Chow.mem_genericPoints_iff_coheight_eq_zero, Order.coheight_eq_zero]
  intro b hb
  have hsp : b ⤳ f.asFiber x := hb
  have h1 : f.fiberι _ b ⤳ x := by
    simpa [Scheme.Hom.fiberι_asFiber] using hsp.map (f.fiberι (f x)).continuous
  have h2 : f (f.fiberι _ b) = f x := by
    have : f.fiberι (f x) b ∈ Set.range (f.fiberι (f x)) := ⟨b, rfl⟩
    rwa [Scheme.Hom.range_fiberι] at this
  have h3 : b = f.asFiber x := (f.fiberι (f x)).isEmbedding.injective
    (by rw [Scheme.Hom.fiberι_asFiber]; exact hx _ h1 h2)
  exact h3 ▸ le_rfl

/-- **Components of codimension `≥ 2` under a flat morphism.** For flat `h : Y → X` of locally
noetherian schemes and a closed subscheme `Z ⊆ X`, `(h⁻¹Z)^{≥2} = h⁻¹(Z^{≥2})`. -/
private theorem componentsOfCodimAtLeastTwo_comap (h : Y ⟶ X) [Flat h] [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (Z : X.IdealSheafData) :
    componentsOfCodimAtLeastTwo ((Z.comap h).support : Set Y) =
      h ⁻¹' componentsOfCodimAtLeastTwo (Z.support : Set X) := by
  have hS : IsClosed (Z.support : Set X) := Z.support.isClosed
  have hcS : IsClosed (h ⁻¹' (Z.support : Set X)) := hS.preimage h.continuous
  have key : ∀ S' : Set Y, S' = h ⁻¹' (Z.support : Set X) →
      componentsOfCodimAtLeastTwo S' = h ⁻¹' componentsOfCodimAtLeastTwo (Z.support : Set X) := by
    rintro _ rfl
    refine iUnion_componentsOf_preimage h.continuous (Flat.generalizingMap h) hS _ _ ?_
    intro η hη
    rw [irreducibleClosure_closure_singleton, irreducibleClosure_closure_singleton,
      codimension_closureSingleton', codimension_closureSingleton',
      coheight_eq_coheight_of_flat h η]
    intro z hz hzη
    exact ((closure_mem_componentsOf_iff hcS η).1 hη).2 z hz
      (show h z ∈ (Z.support : Set X) by
        rw [hzη]; exact ((closure_mem_componentsOf_iff hcS η).1 hη).1)
  exact key _ (by rw [Scheme.IdealSheafData.support_comap]; rfl)

/-- **Components of the centre off the divisor under a generalizing morphism.** For
`h : Y → X` generalizing (e.g. flat), the union of the components of `h⁻¹Z` that are not
components of `Supp h⁻¹E` is the inverse image of the union of the components of `Z` that are
not components of `Supp E`. -/
private theorem iUnion_componentsOf_notMem_comap (h : Y ⟶ X) (hgen : GeneralizingMap h)
    (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    (⋃ (W : Set Y) (_ : W ∈ componentsOf ((Z.comap h).support : Set Y))
        (_ : W ∉ componentsOf (E.comap h).support), W) =
      h ⁻¹' ⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf E.support), W := by
  have hS : IsClosed (Z.support : Set X) := Z.support.isClosed
  have hT : IsClosed E.support := isClosed_iUnion_of_finite fun i => (E.E i).support.isClosed
  have key : ∀ S' : Set Y, S' = h ⁻¹' (Z.support : Set X) →
      (⋃ (W : Set Y) (_ : W ∈ componentsOf S') (_ : W ∉ componentsOf (h ⁻¹' E.support)), W) =
      h ⁻¹' ⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
        (_ : W ∉ componentsOf E.support), W := by
    rintro _ rfl
    refine iUnion_componentsOf_preimage h.continuous hgen hS (fun V _ => V ∉ _)
      (fun W _ => W ∉ _) ?_
    intro η hη
    exact not_congr (closure_mem_componentsOf_preimage_iff h.continuous hgen hS hT hη)
  rw [Kollar.support_comap]
  exact key _ (by rw [Scheme.IdealSheafData.support_comap]; rfl)

end SchemeComponents

/-! ### `𝓑𝓞^H_m` is of order `m` -/

/-- Deleting the empty blow-ups of a sequence that has none changes nothing. -/
private theorem isOrderMTripleSeq_reduction {k : Type u} [Field k] {m : ℕ} {X : Scheme.{u}}
    {B : ClosedBlowupSequence X} {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData}
    {E : OrderedDivisor X} (hB : B.HasNoEmptyBlowups) (h : B.IsOrderMTripleSeq s I E m) :
    B.reduction.IsOrderMTripleSeq s I E m := by
  rwa [ClosedBlowupSequence.reduction_eq_self hB]

/-- For a sequence without empty blow-ups starting with a triple `(X, I, E)` with `maxord I ≤ m`,
being of order `≥ m` for `(X, I, m, E)` and of order `m` for `(X, I, E)` agree. -/
private theorem isOrderGeMarkedTripleSeq_iff_of_maxOrder_le {k : Type u} [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
    (ht : IsTriple s I E) (m : ℕ) (hmax : maxOrder I ≤ m) (B : ClosedBlowupSequence X)
    (hB : B.HasNoEmptyBlowups) :
    B.IsOrderGeMarkedTripleSeq s ⟨I, m⟩ E ↔ B.IsOrderMTripleSeq s I E m := by
  cases B with
  | nil => exact Iff.rfl
  | cons Z B =>
    have key := fun h => (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq s I
      E ht m (le_antisymm hmax h) (.cons Z B)).1
    constructor
    · intro h
      exact (key (le_maxOrder_of_orderAlongGE I Z hB.1 m h.2.2.2.2.1)).1 h
    · intro h
      exact (key (le_maxOrder_of_orderAlongGE I Z hB.1 m fun W hW =>
        (h.2.2.2.2.1 W hW).ge)).2 h

section DivisorChange

open MMP.Mori

/-- Two closed sets with the same points on `Spec 𝒪_{Y,y}` have reduced ideals with the same
stalk at `y`. -/
private theorem stalk_vanishingIdeal_eq_of_fromSpecStalk_iff {Y : Scheme} (T₁ T₂ : Closeds Y)
    (y : Y) (h : ∀ p : PrimeSpectrum (Y.presheaf.stalk y),
      Y.fromSpecStalk y p ∈ (T₁ : Set Y) ↔ Y.fromSpecStalk y p ∈ (T₂ : Set Y)) :
    IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T₁) y =
      IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T₂) y := by
  have hzl : PrimeSpectrum.zeroLocus
      (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T₁) y :
        Set (Y.presheaf.stalk y)) =
      PrimeSpectrum.zeroLocus
      (IdealSheafData.stalk (Scheme.IdealSheafData.vanishingIdeal T₂) y : Set _) := by
    rw [← preimage_fromSpecStalk_support, ← preimage_fromSpecStalk_support,
      Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    ext p
    exact h p
  rw [← (isRadical_stalk_vanishingIdeal T₁ y).radical,
    ← (isRadical_stalk_vanishingIdeal T₂ y).radical,
    ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
    ← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hzl]

/-- Two members of a regular system of parameters generating the same ideal are equal. -/
private theorem eq_of_span_eq_of_isRegularSystemOfParameters {R : Type*} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] {m : ℕ} {w : Fin m → R}
    (hw : IsRegularSystemOfParameters w) {a b : Fin m}
    (h : Ideal.span {w a} = Ideal.span {w b}) : a = b := by
  by_contra hab
  exact notMem_span_singleton_of_ne_of_isRegularSystemOfParameters hw hab
    (h ▸ Ideal.subset_span rfl)

/-- The members of `E₂` through a point have, at that point, the stalks of members of `E₁`. -/
private def StalkRel {X : Scheme} (E₁ E₂ : OrderedDivisor X) : Prop :=
  ∀ (x : X) (j : Fin E₂.s), x ∈ (E₂.E j).support →
    ∃ i : Fin E₁.s, IdealSheafData.stalk (E₂.E j) x = IdealSheafData.stalk (E₁.E i) x

/-- A centre with snc with `E₁` has snc with `E₂` when the members of `E₂` have the stalks of
members of `E₁` and `E₂` is snc. -/
private theorem hasSNCWith_of_stalkRel {k : Type*} [Field k] {X : Scheme} [IsLocallyNoetherian X]
    {sX : X ⟶ Spec (.of k)}
    {E₁ E₂ : OrderedDivisor X} (hR : StalkRel E₁ E₂) (h₂ : E₂.IsSNC sX) {Z : X.IdealSheafData}
    (hZ : HasSNCWith E₁.E Z) : HasSNCWith E₂.E Z := by
  intro x hx
  obtain ⟨n, z, c, J, hz, hc, hinj, hJ⟩ := hZ x hx
  have hσ : ∀ j : {j // x ∈ (E₂.E j).support}, ∃ i : {i // x ∈ (E₁.E i).support},
      IdealSheafData.stalk (E₂.E j.1) x = IdealSheafData.stalk (E₁.E i.1) x := by
    rintro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := hR x j hj
    refine ⟨⟨i, by_contra fun h => ?_⟩, hi⟩
    exact (IdealSheafData.stalk_eq_top_iff_notMem_support _ x).1
      (hi.trans ((IdealSheafData.stalk_eq_top_iff_notMem_support _ x).2 h)) hj
  choose σ hσ using hσ
  obtain ⟨n', z', c', hz', hc', hinj'⟩ := h₂.2 x
  refine ⟨n, z, fun j => c (σ j), J, hz, fun j => (hσ j).trans (hc _), fun j₁ j₂ h => ?_, hJ⟩
  have h1 := hinj h
  have h2 : IdealSheafData.stalk (E₂.E j₁.1) x = IdealSheafData.stalk (E₂.E j₂.1) x := by
    rw [hσ, hσ, h1]
  rw [hc', hc'] at h2
  exact hinj' (eq_of_span_eq_of_isRegularSystemOfParameters hz' h2)

/-- The members of a total transform `π⁻¹_tot E₂` have, at every point, the stalks of members of
`π⁻¹_tot E₁`, when this holds for `E₂` and `E₁`, the centre has snc with `E₁` and the members of
`E₁` are of pure codimension one. -/
private theorem stalkRel_totalTransform {X : Scheme} [IsLocallyNoetherian X] [CompactSpace X]
    {E₁ E₂ : OrderedDivisor X} (hR : StalkRel E₁ E₂) {Z : X.IdealSheafData}
    (hZ : HasSNCWith E₁.E Z) (hpure : ∀ i, IsPureCodimOne (E₁.E i).support) :
    StalkRel (E₁.totalTransform Z) (E₂.totalTransform Z) := by
  classical
  have : IsNoetherian X := {}
  intro x' (j : Fin (E₂.s + 1)) hj
  set π := blowUpToBase Z
  set x := π x'
  set φ := (π.stalkMap x').hom
  set f' := (blowUp Z).fromSpecStalk x'
  have key : ∀ (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
      π (f' p) = X.fromSpecStalk x (PrimeSpectrum.comap φ p) :=
    fun p => apply_fromSpecStalk π x' p
  have hZ2c : IsClosed (componentsOfCodimAtLeastTwo (Z.support : Set X)) :=
    isClosed_componentsOfCodimAtLeastTwo Z.support.isClosed
  have mS : ∀ (K : X.IdealSheafData) (q : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
      π (f' q) ∈ (K.support : Set X) ↔
      IdealSheafData.stalk K x ≤ (PrimeSpectrum.comap φ q).asIdeal := fun K q => by
    rw [key]; exact fromSpecStalk_mem_support_iff_stalk_le K x _
  have hCL : ∀ (E : OrderedDivisor X) (i : Fin E.s)
      (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
      f' p ∈ closure (totalTransformSet E Z (Fin.castSucc i)) ↔
        ∃ q : PrimeSpectrum ((blowUp Z).presheaf.stalk x'), q.asIdeal ≤ p.asIdeal ∧
          π (f' q) ∈ ((E.E i).support : Set X) ∧
            π (f' q) ∉ componentsOfCodimAtLeastTwo (Z.support : Set X) := by
    intro E i p
    simp only [totalTransformSet, Fin.snoc_castSucc]
    exact fromSpecStalk_mem_closure_preimage_diff_iff x' (E.E i).support.isClosed hZ2c p
  have hsupp : ∀ (E : OrderedDivisor X) (i : Fin (E.s + 1)),
      (((E.totalTransform Z).E i).support : Set (blowUp Z)) =
        closure (totalTransformSet E Z i) := by
    intro E i
    rw [totalTransform_E_eq, Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
  have hgoal : ∀ (E E' : OrderedDivisor X) (i : Fin (E.s + 1)) (i' : Fin (E'.s + 1)),
      (∀ (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        f' p ∈ closure (totalTransformSet E Z i) ↔
        f' p ∈ closure (totalTransformSet E' Z i')) →
      IdealSheafData.stalk ((E.totalTransform Z).E i) x' =
        IdealSheafData.stalk ((E'.totalTransform Z).E i') x' := by
    intro E E' i i' h
    rw [totalTransform_E_eq, totalTransform_E_eq]
    exact stalk_vanishingIdeal_eq_of_fromSpecStalk_iff _ _ x'
      (by simpa only [Closeds.coe_closure] using h)
  have hj' : x' ∈ closure (totalTransformSet E₂ Z j) := by rwa [← hsupp]
  induction j using Fin.lastCases with
  | cast j =>
    have hxj : x ∈ (E₂.E j).support := by
      have hsub : totalTransformSet E₂ Z (Fin.castSucc j) ⊆
          π ⁻¹' ((E₂.E j).support : Set X) := by
        simp only [totalTransformSet, Fin.snoc_castSucc]
        exact Set.preimage_mono Set.diff_subset
      exact closure_minimal hsub ((E₂.E j).support.isClosed.preimage π.continuous) hj'
    obtain ⟨i, hi⟩ := hR x j hxj
    refine ⟨Fin.castSucc i, hgoal _ _ _ _ fun p => ?_⟩
    rw [hCL, hCL]
    refine exists_congr fun q => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [mS, mS, hi]
  | last =>
    have hLZ : totalTransformSet E₂ Z (Fin.last E₂.s) ⊆ π ⁻¹' (Z.support : Set X) := by
      intro y hy
      simp only [totalTransformSet, Fin.snoc_last, Set.mem_iUnion] at hy
      obtain ⟨W, hW, -, hyW⟩ := hy
      exact hW.1.2 hyW
    have hx : x ∈ (Z.support : Set X) :=
      closure_minimal hLZ (Z.support.isClosed.preimage π.continuous) hj'
    obtain ⟨n, z, c, J, hz, hc, hinj, hJ⟩ := hZ x hx
    have hJ' : IdealSheafData.stalk Z x = (coordPrime hz J).asIdeal := hJ
    set g := X.fromSpecStalk x (coordPrime hz J)
    set W₀ := closure {g}
    have mL : ∀ (E : OrderedDivisor X) (p : PrimeSpectrum ((blowUp Z).presheaf.stalk x')),
        f' p ∈ closure (totalTransformSet E Z (Fin.last E.s)) ↔
          W₀ ∉ componentsOf E.support ∧
            (coordPrime hz J).asIdeal ≤ (PrimeSpectrum.comap φ p).asIdeal := by
      intro E p
      have hLeq : totalTransformSet E Z (Fin.last E.s) = π ⁻¹'
          (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
            (_ : W ∉ componentsOf E.support), W) := by
        simp only [totalTransformSet, Fin.snoc_last, Set.preimage_iUnion]
        rfl
      have hLc : IsClosed (totalTransformSet E Z (Fin.last E.s)) := by
        rw [hLeq]
        exact (isClosed_biUnion_componentsOf Z.support.isClosed _).preimage π.continuous
      rw [hLc.closure_eq, hLeq, Set.mem_preimage, key,
        fromSpecStalk_mem_biUnion_componentsOf_iff hz hJ' hx _ _]
    have hb₂ : W₀ ∉ componentsOf E₂.support := by
      have h0 : f' (IsLocalRing.closedPoint _) ∈
          closure (totalTransformSet E₂ Z (Fin.last E₂.s)) := by
        simp only [f', Scheme.fromSpecStalk_closedPoint]; exact hj'
      exact ((mL E₂ _).1 h0).1
    by_cases hb₁ : W₀ ∈ componentsOf E₁.support
    · -- `W₀` is a component of a member `E₁^i`, whose stalk at `x` is `I_{Z,x}`
      have hgS : g ∈ E₁.support := hb₁.1.2 (subset_closure rfl)
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hgS
      have hxi : x ∈ (E₁.E i).support :=
        (fromSpecStalk_specializes_self x _).mem_closed (E₁.E i).support.isClosed hi
      have hle : IdealSheafData.stalk (E₁.E i) x ≤ (coordPrime hz J).asIdeal :=
        (fromSpecStalk_mem_support_iff_stalk_le _ x _).1 hi
      let q₁ : PrimeSpectrum (X.presheaf.stalk x) :=
        ⟨IdealSheafData.stalk (E₁.E i) x, by
          rw [hc ⟨i, hxi⟩]; exact span_singleton_isPrime_of_isRegularSystemOfParameters hz _⟩
      have hq₁S : closure {X.fromSpecStalk x q₁} ⊆ ((E₁.E i).support : Set X) :=
        closure_minimal (Set.singleton_subset_iff.2
          ((fromSpecStalk_mem_support_iff_stalk_le _ x _).2 le_rfl)) (E₁.E i).support.isClosed
      have hWq₁ : W₀ ⊆ closure {X.fromSpecStalk x q₁} :=
        closure_minimal (Set.singleton_subset_iff.2
          ((fromSpecStalk_mem_closure_iff x q₁ _).2 hle)) isClosed_closure
      have hq₁W : closure {X.fromSpecStalk x q₁} ⊆ W₀ :=
        hb₁.2 ⟨isIrreducible_singleton.closure,
          hq₁S.trans (Set.subset_iUnion (fun i => ((E₁.E i).support : Set X)) i)⟩ hWq₁
      have hEi : IdealSheafData.stalk (E₁.E i) x = (coordPrime hz J).asIdeal :=
        le_antisymm hle ((fromSpecStalk_mem_closure_iff x _ q₁).1 (hq₁W (subset_closure rfl)))
      -- `W₀` has codimension one
      let W₀c : IrreducibleCloseds X := ⟨W₀, isIrreducible_singleton.closure, isClosed_closure⟩
      have hW₀S : W₀ ⊆ ((E₁.E i).support : Set X) :=
        closure_minimal (Set.singleton_subset_iff.2 hi) (E₁.E i).support.isClosed
      have hcod : codimension W₀c = 1 := by
        refine hpure i W₀c ⟨hW₀S, fun W' hW' hle' => ?_⟩
        exact hb₁.2 ⟨W'.isIrreducible,
          hW'.trans (Set.subset_iUnion (fun i => ((E₁.E i).support : Set X)) i)⟩ hle'
      have hnb : ¬ ∃ hW : IsIrreducible W₀, 2 ≤ codimension (irreducibleClosure hW) := by
        rintro ⟨hW, h2⟩
        have he : irreducibleClosure hW = W₀c := by
          ext1; exact closure_closure
        rw [he, hcod] at h2
        exact absurd h2 (by norm_num)
      refine ⟨Fin.castSucc i, hgoal _ _ _ _ fun p => ?_⟩
      rw [mL, hCL]
      constructor
      · rintro ⟨-, hp⟩
        refine ⟨p, le_rfl, by rw [mS, hEi]; exact hp, fun h => hnb ?_⟩
        rw [key, componentsOfCodimAtLeastTwo_eq,
          fromSpecStalk_mem_biUnion_componentsOf_iff hz hJ' hx _ _] at h
        exact h.1
      · rintro ⟨q, hqp, hq, -⟩
        rw [mS, hEi] at hq
        exact ⟨hb₂, hq.trans (Ideal.comap_mono hqp)⟩
    · refine ⟨Fin.last _, hgoal _ _ _ _ fun p => ?_⟩
      rw [mL, mL]
      exact and_congr_left fun _ => iff_of_true hb₂ hb₁

/-- An ordered divisor whose members through every point are matched injectively, stalk for
stalk, with members of an snc divisor through it is an ordered snc divisor. -/
private theorem isOrderedSNC_of_injective {k : Type*} [Field k] [CharZero k] {X : Scheme}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {E₁ E₂ : OrderedDivisor X}
    (h₁ : E₁.IsSNC sX)
    (hR : ∀ x, ∃ σ : {j // x ∈ (E₂.E j).support} → {i // x ∈ (E₁.E i).support},
      Function.Injective σ ∧
        ∀ j, IdealSheafData.stalk (E₂.E j.1) x = IdealSheafData.stalk (E₁.E (σ j).1) x) :
    E₂.IsOrderedSNC sX := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have hcoord : ∀ x : X, ∃ (n : ℕ) (w : Fin n → X.presheaf.stalk x)
      (c : {i // x ∈ (E₂.E i).support} → Fin n),
      IsRegularSystemOfParameters w ∧
        (∀ i, IdealSheafData.stalk (E₂.E i.1) x = Ideal.span {w (c i)}) ∧
          Function.Injective c := by
    intro x
    obtain ⟨n, z, c, hz, hc, hinj⟩ := h₁.2 x
    obtain ⟨σ, hσ, hσs⟩ := hR x
    exact ⟨n, z, fun j => c (σ j), hz, fun j => (hσs j).trans (hc _), hinj.comp hσ⟩
  have hpar : ∀ i, ∀ y ∈ (E₂.E i).support,
      ∃ (m : ℕ) (w : Fin m → X.presheaf.stalk y) (j : Fin m),
        IsRegularSystemOfParameters w ∧
          IdealSheafData.stalk (E₂.E i) y = Ideal.span {w j} := by
    intro i y hy
    obtain ⟨N, w, c, hw, hc, -⟩ := hcoord y
    exact ⟨N, w, c ⟨i, hy⟩, hw, hc ⟨i, hy⟩⟩
  exact ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
    isEffectiveCartierDivisor_of_stalk_eq_span_parameter _ (hpar i)⟩,
    ⟨fun i => ⟨isReduced_subscheme_of_stalk_eq_span_parameter _ (hpar i),
      isPureCodimOne_support_of_stalk_eq_span_parameter _ (hpar i),
      isSmoothScheme_subscheme_of_stalk_eq_span_parameter sX _ (hpar i)⟩, hcoord⟩⟩

/-- A smooth blow-up sequence of order `≥ m` for `(X, a, E₁)` is one for `(X, a, E₂)` when the
members of `E₂` have, at every point, the stalks of members of `E₁` and `E₂` is ordered snc. -/
private theorem isOrderGeMarkedTripleSeq_of_stalkRel {k : Type u} [Field k] :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k)) (a : MarkedIdeal X)
      (E₁ E₂ : OrderedDivisor X), StalkRel E₁ E₂ → E₂.IsOrderedSNC s →
      B.IsOrderGeMarkedTripleSeq s a E₁ → B.IsOrderGeMarkedTripleSeq s a E₂
  | _, .nil _, _, _, _, _, _, h₂, h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h₂⟩
  | _, .cons Z B, s, a, E₁, E₂, hR, h₂, h => by
    obtain ⟨hT, hZs, hcod, hsnc, hord, hB⟩ := h
    haveI : CharZero k := hT.1
    haveI : LocallyOfFiniteType s := hT.2.2.1
    haveI : QuasiCompact s := hT.2.2.2.1
    haveI : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian s
    haveI : CompactSpace _ := QuasiCompact.compactSpace_of_compactSpace s
    have hsnc₂ := hasSNCWith_of_stalkRel hR h₂.2 hsnc
    exact ⟨⟨hT.1, hT.2.1, hT.2.2.1, hT.2.2.2.1, hT.2.2.2.2.1, hT.2.2.2.2.2.1, h₂⟩, hZs, hcod,
      hsnc₂, hord, isOrderGeMarkedTripleSeq_of_stalkRel B _ _ _ _
        (stalkRel_totalTransform hR hsnc fun i => (hT.2.2.2.2.2.2.2.1 i).2.1)
        (isOrderedSNC_totalTransform s h₂.2 hsnc₂) hB⟩

/-- The start of a smooth blow-up sequence of order `≥ m` is a triple. -/
private theorem isTriple_of_isOrderGeMarkedTripleSeq {k : Type u} [Field k]
    {X : Scheme.{u}} {B : ClosedBlowupSequence X} {s : X ⟶ Spec (.of k)}
    {a : MarkedIdeal X} {E : OrderedDivisor X} (h : B.IsOrderGeMarkedTripleSeq s a E) :
    IsTriple s a.I E := by
  cases B with
  | nil => exact h
  | cons => exact h.1

/-- Kollár 3.104 Step 2.2, the change of divisor on `V`: a smooth blow-up sequence of order
`≥ m` on `V` for `(V, J'|_V, m, E^V)` is one for `(V, J'|_V, m, E'|_V)`. The members `E'^i`,
`i < s`, do not meet `V`, and the others are the members of `E^V` other than the first. -/
private theorem isOrderGeMarkedTripleSeq_comap_of_divisorSeparation {m : ℕ}
    (t : FieldBlowupTriple.{u}) (H : t.X.IdealSheafData) (P : ClosedBlowupSequence t.X) :
    let t' := t.endOf P
    let H' : t'.X.IdealSheafData := (P.restrictHom H).ker
    let V : t'.X.Opens :=
      (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
    let EV : OrderedDivisor V :=
      ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
        fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩
    let tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, EV⟩, t'.k, V.ι ≫ t'.sX⟩
    ∀ BV : ClosedBlowupSequence V,
    t.E.s ≤ t'.E.s → IsTriple t'.sX t'.I t'.E →
    BV.IsOrderGeMarkedTripleSeq tV.sX ⟨tV.I, m⟩ tV.E →
      BV.IsOrderGeMarkedTripleSeq (V.ι ≫ t'.sX) ⟨t'.I.comap V.ι, m⟩ (t'.E.comap V.ι) := by
  intro t' H' V EV tV BV hs htr hBV
  have hlow : ∀ (x : V) (j : Fin t'.E.s), x ∈ ((t'.E.E j).comap V.ι).support →
      t.E.s ≤ (j : ℕ) := by
    intro x j hj
    refine not_lt.1 fun hjs => ?_
    have hj := (mem_support_comap_iff V.ι _ x).1 hj
    have hmem : V.ι x ∈ ((⨆ i : Fin t'.E.s,
        if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥ : Closeds t'.X) : Set t'.X) := by
      refine le_iSup (fun i : Fin t'.E.s =>
        if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥) j ?_
      rwa [if_pos hjs]
    have hV : V.ι x ∈ (V : Set t'.X) := by rw [← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩
    exact hV hmem
  have hidx : ∀ (j : Fin t'.E.s) (h' : (j : ℕ) - t.E.s < t'.E.s - t.E.s), t.E.s ≤ (j : ℕ) →
      EV.E (Fin.succ ⟨j - t.E.s, h'⟩) = (t'.E.E j).comap V.ι := by
    intro j h' hj
    simp only [EV, Fin.cons_succ]
    congr 2
    ext
    simp only
    omega
  have hT := isTriple_of_isOrderGeMarkedTripleSeq hBV
  haveI : CharZero t'.k := hT.1
  haveI : LocallyOfFiniteType (V.ι ≫ t'.sX) := hT.2.2.1
  have hss : (t'.E.comap V.ι).s = t'.E.s := rfl
  have hsnc : (t'.E.comap V.ι).IsOrderedSNC (V.ι ≫ t'.sX) := by
    refine isOrderedSNC_of_injective _ hT.2.2.2.2.2.2.2 fun x => ?_
    refine ⟨fun j => ⟨Fin.succ (⟨j.1 - t.E.s, by
      have := j.1.isLt; have := hlow x j.1 j.2; omega⟩ : Fin (t'.E.s - t.E.s)), by
      rw [hidx j.1 _ (hlow x j.1 j.2)]; exact j.2⟩, fun j₁ j₂ h => ?_, fun j => by
      rw [hidx j.1 _ (hlow x j.1 j.2)]; rfl⟩
    have h2 := congrArg (fun i => ((Subtype.val i : Fin (t'.E.s - t.E.s + 1)) : ℕ)) h
    have l1 := hlow x j₁.1 j₁.2
    have l2 := hlow x j₂.1 j₂.2
    simp only [Fin.val_succ] at h2
    exact Subtype.ext (Fin.ext (by omega))
  exact isOrderGeMarkedTripleSeq_of_stalkRel BV _ _ EV _
    (fun x j hj => ⟨Fin.succ (⟨j - t.E.s, by
      have := j.isLt; have := hlow x j hj; omega⟩ : Fin (t'.E.s - t.E.s)), by
      rw [hidx j _ (hlow x j hj)]; rfl⟩) hsnc hBV

end DivisorChange

/-- Kollár 3.104 Step 2.2, the extension by closure: a smooth blow-up sequence of order `m` on
`V` for `(V, J'|_V, E^V)` extends by closure to one on `X'` for `(X', J', E')`, given that
`cosupp(J', m)` misses the old divisors `E'^i`, `i < s`, whose complement is `V`. -/
private theorem extendByClosure_isOrderMTripleSeq {m : ℕ} (t : FieldBlowupTriple.{u})
    (H : t.X.IdealSheafData) (P : ClosedBlowupSequence t.X) :
    let t' := t.endOf P
    let H' : t'.X.IdealSheafData := (P.restrictHom H).ker
    let V : t'.X.Opens :=
      (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
    let EV : OrderedDivisor V :=
      ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
        fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩
    let tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, EV⟩, t'.k, V.ι ≫ t'.sX⟩
    ∀ BV : ClosedBlowupSequence V,
    t.E.s ≤ t'.E.s → IsTriple t'.sX t'.I t'.E → maxOrder t'.I ≤ m → 1 ≤ m →
    (∀ (i : ℕ) (hi : i < t.E.s), ∃ hir : i < t'.E.s,
      Disjoint (⟨t'.I, m⟩ : MarkedIdeal t'.X).cosupport ((t'.E.E ⟨i, hir⟩).support : Set t'.X)) →
    BV.HasNoEmptyBlowups → BV.IsOrderMTripleSeq tV.sX tV.I tV.E m →
      (BV.extendByClosure V.ι).IsOrderMTripleSeq t'.sX t'.I t'.E m := by
  intro t' H' V EV tV BV hs htr hmax hm hdisj hNE hBV
  haveI : LocallyOfFiniteType t'.sX := htr.2.2.1
  haveI : QuasiCompact t'.sX := htr.2.2.2.1
  haveI : IsLocallyNoetherian t'.X := LocallyOfFiniteType.isLocallyNoetherian t'.sX
  haveI : CompactSpace t'.X := QuasiCompact.compactSpace_of_compactSpace t'.sX
  haveI : IsNoetherian t'.X := ⟨⟩
  have hGeV : BV.IsOrderGeMarkedTripleSeq tV.sX ⟨tV.I, m⟩ tV.E :=
    (isOrderGeMarkedTripleSeq_iff_of_maxOrder_le tV.sX tV.I tV.E
      (isTriple_of_isOrderMTripleSeq hBV) m ((maxOrder_comap_le V.ι t'.I).trans hmax) BV hNE).2
      hBV
  have hcos : (⟨t'.I, m⟩ : MarkedIdeal t'.X).cosupport ⊆ Set.range V.ι := by
    intro x hx
    rw [Scheme.Opens.range_ι]
    change x ∉ ((⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥ :
      TopologicalSpace.Closeds t'.X) : Set t'.X)
    rw [← Finset.sup_univ_eq_iSup, TopologicalSpace.Closeds.coe_finset_sup]
    intro hx'
    rw [Finset.sup_set_eq_biUnion] at hx'
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.1 hx'
    simp only [Function.comp_apply] at hi
    split_ifs at hi with h
    · obtain ⟨hir, hd⟩ := hdisj i h
      exact Set.disjoint_left.1 hd hx hi
    · exact hi
  have hGe := ClosedBlowupSequence.isOrderGeMarkedTripleSeq_extendByClosure_of_cosupport_subset BV
    V.ι t'.sX ⟨t'.I, m⟩ t'.E hm htr hcos
    (isOrderGeMarkedTripleSeq_comap_of_divisorSeparation t H P BV hs htr hGeV)
  exact (isOrderGeMarkedTripleSeq_iff_of_maxOrder_le t'.sX t'.I t'.E htr m hmax _
    (hasNoEmptyBlowups_extendByClosure BV V.ι hNE)).1 hGe

/-- The obligation of Kollár 3.104 Step 2.2: the extension by closure of `𝓑𝓓` on `V` is of order
`m` for the end of `Π_sep`. -/
private theorem extendByClosure_bdFunctor_isOrderMTripleSeq {N n m : ℕ}
    (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (H : t.X.IdealSheafData)
    (hH : IsMCHypersurface t.sX t.I H) :
    let P := divisorSeparationSequence M m t
    let t' := t.endOf P
    let H' : t'.X.IdealSheafData := (P.restrictHom H).ker
    let V : t'.X.Opens :=
      (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
    let EV : OrderedDivisor V :=
      ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
        fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩
    let tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, EV⟩, t'.k, V.ι ≫ t'.sX⟩
    (V : Set t'.X).Nonempty → IsTriple tV.sX tV.I tV.E →
      ((bdFunctor M (dimNat t.X) m 0 tV).extendByClosure V.ι).IsOrderMTripleSeq
        t'.sX t'.I t'.E m := by
  intro P t' H' V EV tV hV htV
  have hP := divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le
  have hend := end_of_isOrderMTripleSeq m _ P t.sX t.I t.E hP hmax.le hdim
  have htr : IsTriple t'.sX t'.I t'.E :=
    ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m P _ _ _ hP
  haveI : LocallyOfFiniteType t'.sX := htr.2.2.1
  have hdimV : topologicalKrullDim tV.X = ((n : ℕ∞) : WithBot ℕ∞) :=
    (topologicalKrullDim_opens_of_equidimensional t'.sX htr.2.2.2.2.1 V hV).trans hend.1
  have hmaxV : maxOrder tV.I ≤ m := (maxOrder_comap_le V.ι t'.I).trans hend.2.1
  have hdN : dimNat t.X = n := dimNat_eq_of_eq hdim
  rw [hdN]
  have hBD := (bdFunctor_isOrderMTripleSeq M hN hM tV htV hdimV hn hnN hm hmaxV (j := 0)
    (Nat.succ_pos _)).1
  exact extendByClosure_isOrderMTripleSeq t H P _
    (isOrderedSNC_divisorSeparationSequence M hN hM t ht hdim hn hnN hm hmax hH).1 htr hend.2.1 hm
    (fun i hi => disjoint_cosupport_divisorSeparationSequence M hN hM t ht hdim hn hnN hm
      hmax.le i hi) (hasNoEmptyBlowups_bdFunctor ..) hBD

/-- **Kollár, Thm. 3.103 (opening clause), maximal contact case.** Let `𝓜` be a marked
order-reduction family on dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`), `(X, J, E)`
a triple of dimension `n` with `1 ≤ n ≤ N`, `m ≥ 1` with `maxord J = m`, and `H` an
MC-hypersurface for `J` (`IsMCHypersurface`). Then `boMaximalContact M m (X, J, E) H` is a smooth
blow-up sequence of order `m` starting with `(X, J, E)`
(`ClosedBlowupSequence.IsOrderMTripleSeq`). -/
@[mmp "lem_kr3e_bo_maximal_contact_is_order_m"]
public theorem boMaximalContact_isOrderMTripleSeq {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (H : t.X.IdealSheafData)
    (hH : IsMCHypersurface t.sX t.I H) :
    (boMaximalContact M m t H).IsOrderMTripleSeq t.sX t.I t.E m := by
  have hP := divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le
  have hext := extendByClosure_bdFunctor_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax H hH
  rw [boMaximalContact]
  refine isOrderMTripleSeq_reduction (hasNoEmptyBlowups_append _ _
    (hasNoEmptyBlowups_divisorSeparationAux M m t t.E.s) (hasNoEmptyBlowups_extendByClosure _ _ ?_))
    ((ClosedBlowupSequence.isOrderMTripleSeq_append_iff m _ _ _ _ _).2 ⟨hP, ?_⟩)
  · split_ifs
    · exact hasNoEmptyBlowups_bdFunctor ..
    · trivial
  · split_ifs with hc
    · exact hext hc.1 hc.2
    · exact ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m _ _ _ _ hP

/-! ### `𝓑𝓞^H_m` reduces the maximal order -/

/-- Transport of a property of the last controlled transform and the last restriction along a
concatenation. -/
private theorem append_transport
    (F : ∀ {T : Scheme.{u}}, T.IdealSheafData → T.IdealSheafData → Prop) :
    ∀ {X S : Scheme.{u}} (B : ClosedBlowupSequence X) (C : ClosedBlowupSequence B.target)
      (I : X.IdealSheafData) (h : S ⟶ X),
      F ((B.append C).controlledTransform I) ((B.append C).pullbackHom h).ker ↔
        F (C.controlledTransform (B.controlledTransform I)) (C.pullbackHom (B.pullbackHom h)).ker
  | _, _, .nil _, _, _, _ => Iff.rfl
  | _, _, .cons Z B, C, I, h => append_transport F B C _ (canonicalLift h Z)

/-- A blow-up sequence truncated at its length is itself. -/
private theorem truncate_length :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X), B.truncate B.length = B
  | _, .nil _ => rfl
  | _, .cons Z B => by
    change ClosedBlowupSequence.cons Z (B.truncate B.length) = _
    rw [truncate_length B]

/-- Along any morphism, `ord_{f y} I ≥ m` gives `ord_y (f^*I) ≥ m`. -/
private theorem le_multAt_comap {X Y : Scheme.{u}} (f : Y ⟶ X) (I : X.IdealSheafData)
    (y : Y) {m : ℕ} (h : (m : ℕ∞) ≤ multAt I (f y)) : (m : ℕ∞) ≤ multAt (I.comap f) y := by
  unfold multAt at h ⊢
  rw [IdealSheafData.stalk_comap]
  rw [natCast_le_idealOrder_iff'] at h ⊢
  refine (Ideal.map_mono h).trans ?_
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono
    (Ideal.map_le_iff_le_comap.2 (IsLocalRing.maximalIdeal_comap _).ge) m

/-- The complement of an effective Cartier divisor is dense. -/
private theorem dense_compl_support_of_isEffectiveCartierDivisor {Y : Scheme.{u}}
    (D : Y.IdealSheafData) (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) :
    Dense (D.support.compl : Set Y) := by
  have : IsAffineHom (Scheme.Opens.ι D.support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor D hD
  have : IsSchemeTheoreticallyDominant (Scheme.Opens.ι D.support.compl) :=
    (Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant
      D.support.compl).mp
      (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor D hD)
  have hdense := (Scheme.Opens.ι D.support.compl).denseRange
  rwa [DenseRange, Scheme.Opens.range_ι] at hdense

/-- The image of the canonical lift `B_{f⁻¹Z}S → B_ZX` lies in the closure of
`π⁻¹(f(S) ∖ Z)`: off the exceptional divisor, which is dense in `B_{f⁻¹Z}S`, it maps there. -/
private theorem range_canonicalLift_subset_closure {X S : Scheme.{u}} (f : S ⟶ X)
    (Z : X.IdealSheafData) :
    Set.range (canonicalLift f Z) ⊆
      closure (blowUpToBase Z ⁻¹' (Set.range f \ (Z.support : Set X))) := by
  set W := Z.comap f
  have hD := dense_compl_support_of_isEffectiveCartierDivisor (W.comap (blowUpToBase W))
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal W)
  have hsq : ∀ v, blowUpToBase Z (canonicalLift f Z v) = f (blowUpToBase W v) := fun v => by
    rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]
  rintro _ ⟨y, rfl⟩
  have hy : y ∈ closure ((W.comap (blowUpToBase W)).support.compl : Set (blowUp W)) := by
    rw [hD.closure_eq]; trivial
  have h1 := image_closure_subset_closure_image (canonicalLift f Z).continuous ⟨y, hy, rfl⟩
  refine closure_mono ?_ h1
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v ∉ ((W.comap (blowUpToBase W)).support : Set (blowUp W)) := by simpa using hv
  refine ⟨⟨blowUpToBase W v, (hsq v).symm⟩, fun hz => hv' ?_⟩
  rwa [SetLike.mem_coe, mem_support_comap_iff, mem_support_comap_iff, ← hsq]

/-- The iterated set-theoretic strict transform `T_{i+1} = (π_i⁻¹(T_i ∖ Z_i))‾` of `T ⊆ X`. -/
private def strictSet : {X : Scheme.{u}} → (B : ClosedBlowupSequence X) → Set X →
    Set B.target
  | _, .nil _, T => T
  | _, .cons Z B, T => strictSet B (closure (blowUpToBase Z ⁻¹' (T \ (Z.support : Set _))))

/-- The image of the last morphism of a pull-back lies in the strict transform of any set
containing the image of the morphism pulled back along. -/
private theorem range_pullbackHom_subset_strictSet :
    ∀ {X S : Scheme.{u}} (B : ClosedBlowupSequence X) (f : S ⟶ X) (T : Set X),
      Set.range f ⊆ T → Set.range (B.pullbackHom f) ⊆ strictSet B T
  | _, _, .nil _, _, _, hT => hT
  | _, _, .cons Z B, f, T, hT =>
    range_pullbackHom_subset_strictSet B (canonicalLift f Z) _
      ((range_canonicalLift_subset_closure f Z).trans
        (closure_mono (Set.preimage_mono (Set.diff_subset_diff_left hT))))

/-- The canonical lift of an open immersion is an open immersion. -/
private theorem isOpenImmersion_canonicalLift {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (Z : X.IdealSheafData) : IsOpenImmersion (canonicalLift j Z) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (Kollar.isPullback_canonicalLift_of_flat j Z) ‹_›

/-- The strict transform commutes with restriction to an open. -/
private theorem preimage_strictSet_pullbackHom :
    ∀ {X U : Scheme.{u}} (B : ClosedBlowupSequence X) (j : U ⟶ X) [IsOpenImmersion j]
      (T : Set X), B.pullbackHom j ⁻¹' strictSet B T = strictSet (B.pullback j) (j ⁻¹' T)
  | _, _, .nil _, _, _, _ => rfl
  | _, _, .cons Z B, j, _, T => by
    haveI := isOpenImmersion_canonicalLift j Z
    change B.pullbackHom (canonicalLift j Z) ⁻¹' strictSet B _ =
      strictSet (B.pullback (canonicalLift j Z)) _
    rw [preimage_strictSet_pullbackHom B (canonicalLift j Z)]
    congr 1
    rw [(canonicalLift j Z).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      (canonicalLift j Z).continuous]
    congr 1
    ext v
    simp only [Set.mem_preimage, Set.mem_diff, SetLike.mem_coe, mem_support_comap_iff]
    rw [← Scheme.Hom.comp_apply, canonicalLift_comp_blowUpToBase, Scheme.Hom.comp_apply]

/-- The strict transform of a subset of a member of `E` lies in the corresponding member of the
total transform. -/
private theorem strictSet_subset_support_orderedTotalTransform :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (E : OrderedDivisor X) (i : ℕ)
      (hi : i < E.s) (T : Set X), T ⊆ ((E.E ⟨i, hi⟩).support : Set X) →
      ∀ hi' : i < (B.orderedTotalTransform E).s,
        strictSet B T ⊆ (((B.orderedTotalTransform E).E ⟨i, hi'⟩).support : Set B.target)
  | _, .nil _, _, _, _, _, hT, _ => hT
  | _, .cons Z B, E, i, hi, T, hT, hi' => by
    refine strictSet_subset_support_orderedTotalTransform B (E.totalTransform Z) i
      (Nat.lt_succ_of_lt hi) _ ?_ hi'
    have he : (⟨i, Nat.lt_succ_of_lt hi⟩ : Fin (E.s + 1)) = Fin.castSucc ⟨i, hi⟩ := rfl
    change _ ⊆ ((Fin.snoc (α := fun _ => (blowUp Z).IdealSheafData) _ _
      (⟨i, Nat.lt_succ_of_lt hi⟩ : Fin (E.s + 1))).support : Set (blowUp Z))
    rw [he, Fin.snoc_castSucc, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure]
    refine closure_mono (Set.preimage_mono fun x hx => ⟨hT hx.1, fun hx2 => hx.2 ?_⟩)
    simp only [componentsOfCodimAtLeastTwo, Set.mem_iUnion] at hx2
    obtain ⟨W, hW, -, hxW⟩ := hx2
    exact hW.1.2 hxW

private theorem pullback_eqToHom_comp_heq {X Y Y' : Scheme.{u}} (D : ClosedBlowupSequence X)
    (e : Y = Y') (f : Y' ⟶ X) : D.pullback (eqToHom e ≫ f) ≍ D.pullback f := by
  subst e; simp

/-- Restricting the extension by closure along a quasi-compact open immersion gives back the
sequence. -/
private theorem pullback_extendByClosure :
    ∀ {U X : Scheme.{u}} (B : ClosedBlowupSequence U) (j : U ⟶ X) [IsOpenImmersion j]
      [QuasiCompact j], (B.extendByClosure j).pullback j = B
  | _, _, .nil _, _, _, _ => rfl
  | _, _, .cons Z B, j, _, _ => by
    have h := ClosedBlowupSequence.comap_map_eq_of_isOpenImmersion j Z
    rw [ClosedBlowupSequence.extendByClosure, dif_pos h]
    change ClosedBlowupSequence.cons _
      ((B.extendByClosure _).pullback (canonicalLift j (Z.map j))) = _
    refine ClosedBlowupSequence.cons_eq_cons_iff.2 ⟨h, ?_⟩
    have sq := Kollar.isPullback_canonicalLift_of_flat j (Z.map j)
    haveI : IsOpenImmersion (canonicalLift j (Z.map j)) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq ‹_›
    haveI : QuasiCompact (canonicalLift j (Z.map j)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) sq ‹_›
    have ih := pullback_extendByClosure B
      (eqToHom (congrArg blowUp h.symm) ≫ canonicalLift j (Z.map j))
    exact (pullback_eqToHom_comp_heq _ _ _).symm.trans (heq_of_eq ih)

/-- The last morphism of the pull-back along an open immersion is an open immersion. -/
private theorem isOpenImmersion_pullbackHom {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) [IsOpenImmersion h] : IsOpenImmersion (B.pullbackHom h) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (Kollar.isPullback_pullback_toBase_of_flat B h) ‹_›

/-- The image of the last morphism of the pull-back along an open immersion `h` is the inverse
image of the image of `h`. -/
private theorem range_pullbackHom {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (h : Y ⟶ X) [IsOpenImmersion h] :
    Set.range (B.pullbackHom h) = B.toBase ⁻¹' Set.range h := by
  have sq := Kollar.isPullback_pullback_toBase_of_flat B h
  have hs : Function.Surjective sq.isoPullback.hom := sq.isoPullback.hom.surjective
  rw [← sq.isoPullback_hom_snd, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    hs.range_eq, Set.image_univ, IsOpenImmersion.range_pullbackSnd]
  rfl

/-- The marked transform commutes with pull-back along any morphism, for a smooth sequence of
order `≥ m`. -/
private theorem markedTransform_pullback {k : Type u} [Field k] :
    ∀ {X Y : Scheme.{u}} (B : ClosedBlowupSequence X) (j : Y ⟶ X) (s : X ⟶ Spec (.of k))
      (a : MarkedIdeal X) (E : OrderedDivisor X), B.IsOrderGeMarkedTripleSeq s a E →
      ((B.pullback j).markedTransform ⟨a.I.comap j, a.m⟩).I =
        (B.markedTransform a).I.comap (B.pullbackHom j)
  | _, _, .nil _, _, _, _, _, _ => rfl
  | _, _, .cons Z B, j, s, a, E, h => by
    obtain ⟨hT, hZ, hcod, -, hord, hB⟩ := h
    have ha : a.I.comap (blowUpToBase Z) ≤ Z.comap (blowUpToBase Z) ^ a.m := by
      rw [← MarkedIdeal.birationalTransform_mul_eq s hT.2.1 Z hZ hcod a hord]
      exact fun _ => Ideal.mul_le_right
    have key := Kollar.birationalTransform_comap_eq_comap_canonicalLift j Z a ha
    change ((B.pullback (canonicalLift j Z)).markedTransform
      (MarkedIdeal.birationalTransform (Z.comap j) ⟨a.I.comap j, a.m⟩)).I =
        (B.markedTransform (a.birationalTransform Z)).I.comap (B.pullbackHom (canonicalLift j Z))
    rw [key]
    exact markedTransform_pullback B _ _ _ _ hB

/-- A smooth sequence of order `m` without empty blow-ups starting with a triple with
`maxord ≤ m` is of order `≥ m` for the marked triple, with the same ideals. -/
private theorem isOrderGe_and_markedTransform_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (m : ℕ)
    (hmax : maxOrder I ≤ m) (B : ClosedBlowupSequence X) (hB : B.HasNoEmptyBlowups)
    (h : B.IsOrderMTripleSeq s I E m) :
    B.IsOrderGeMarkedTripleSeq s ⟨I, m⟩ E ∧
      (B.markedTransform ⟨I, m⟩).I = B.controlledTransform I := by
  cases B with
  | nil => exact ⟨h, rfl⟩
  | cons Z B =>
    have hm := le_maxOrder_of_orderAlongGE I Z hB.1 m fun W hW => (h.2.2.2.2.1 W hW).ge
    have key := ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq s I E
      h.1 m (le_antisymm hmax hm) (.cons Z B)
    exact ⟨key.1.2 h, key.2 h⟩

/-! ### Dimensions and orders -/

/-- On an equidimensional space all irreducible components have one common dimension. -/
private theorem exists_forall_topologicalKrullDim_eq {X : Type*} [TopologicalSpace X]
    (h : Equidimensional X) :
    ∃ n : ℕ∞, ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = n := by
  by_cases hc : ∃ Z₀, Z₀ ∈ irreducibleComponents X
  · obtain ⟨Z₀, hZ₀⟩ := hc
    have hne : topologicalKrullDim Z₀ ≠ ⊥ := by
      have : IrreducibleSpace Z₀ := isIrreducible_iff_irreducibleSpace.mp hZ₀.1
      rw [topologicalKrullDim, Ne, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
      exact ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
    exact ⟨(topologicalKrullDim Z₀).unbot hne, fun Z hZ => by
      rw [WithBot.coe_unbot]; exact h Z hZ Z₀ hZ₀⟩
  · exact ⟨0, fun Z hZ => (hc ⟨Z, hZ⟩).elim⟩

/-- If `maxord I = m` is a natural number `≥ 1`, then `cosupp(I, m)` is nonempty. -/
private theorem cosupport_nonempty_of_maxOrder_eq {X : Scheme.{u}} {I : X.IdealSheafData}
    {m : ℕ} (hm : 1 ≤ m) (hmax : maxOrder I = m) :
    (⟨I, m⟩ : MarkedIdeal X).cosupport.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have hlt : ∀ x, multAt I x < m := fun x => by
    by_contra h
    exact (Set.eq_empty_iff_forall_notMem.1 hne x) (not_lt.1 h)
  have hle : ∀ x, multAt I x ≤ (m - 1 : ℕ) := fun x => by
    have := hlt x
    lift multAt I x to ℕ using ne_top_of_lt this with a
    exact_mod_cast Nat.le_sub_one_of_lt (by exact_mod_cast this)
  have : maxOrder I ≤ (m - 1 : ℕ) := iSup₂_le fun x _ => hle x
  rw [hmax] at this
  exact absurd (ENat.coe_le_coe.1 this) (by omega)

/-! ### The triple on `V` -/

/-- The triple `(V, J'|_V, E^V)` is a triple, `E^V` the restriction of the ordered snc divisor
`(H', E'^{s+1}, …)`. -/
private theorem isTriple_restrict_open (t' : FieldBlowupTriple.{u})
    (ht' : IsTriple t'.sX t'.I t'.E) (s : ℕ) (hs : s ≤ t'.E.s) (H' : t'.X.IdealSheafData)
    (hsnc : OrderedDivisor.IsOrderedSNC t'.sX
      (⟨t'.E.s - s + 1, Fin.cons (α := fun _ => t'.X.IdealSheafData) H'
        fun i => t'.E.E ⟨s + i, by have := i.isLt; omega⟩⟩ : OrderedDivisor t'.X))
    (V : t'.X.Opens) :
    IsTriple (V.ι ≫ t'.sX) (t'.I.comap V.ι)
      ⟨t'.E.s - s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
        fun i => (t'.E.E ⟨s + i, by have := i.isLt; omega⟩).comap V.ι⟩ := by
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hI, -⟩ := ht'
  haveI := hlft
  haveI := hqc
  haveI : IsLocallyNoetherian t'.X := LocallyOfFiniteType.isLocallyNoetherian t'.sX
  let t₀ : FieldBlowupTriple.{u} := ⟨⟨t'.X, t'.I, ⟨t'.E.s - s + 1,
    Fin.cons (α := fun _ => t'.X.IdealSheafData) H'
      fun i => t'.E.E ⟨s + i, by have := i.isLt; omega⟩⟩⟩, t'.k, t'.sX⟩
  have ht₀ : t₀ ∈ sncTriples := ⟨hchar, hsm, hlft, hqc, hI, hsnc.1, hsnc.2⟩
  have h := pullback_mem_sncTriples ht₀ V.ι
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hE : (t₀.pullback V.ι).E =
      ⟨t'.E.s - s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
        fun i => (t'.E.E ⟨s + i, by have := i.isLt; omega⟩).comap V.ι⟩ := by
    change OrderedDivisor.mk _ _ = OrderedDivisor.mk _ _
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [hE] at h6 h7
  exact ⟨h1, h2, h3, h4, equidimensional_opens t'.sX hequi V, h5, h6, h7⟩

/-! ### The proof -/

/-! ### The cosupport misses the birational transform of `H` -/

open Classical in
/-- The heart of Kollár 3.103 Step 2.2: if `maxord J_r = m`, then `cosupp(J_r, m)` is disjoint
from the birational transform `H_r` of `H`. The cosupport lies over the open `V` off the old
divisors, over which the sequence is `𝓑𝓓` of `(V, J'|_V, E^V)`; there `H_r` lies in the first
member of the total transform of `E^V`, which `𝓑𝓓` separates from the cosupport. -/
private theorem disjoint_cosupport_support_ker_restrictHom {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (H : t.X.IdealSheafData)
    (hH : IsMCHypersurface t.sX t.I H)
    (hr : maxOrder (t.endOf (boMaximalContact M m t H)).I = m) :
    Disjoint (⟨(t.endOf (boMaximalContact M m t H)).I, m⟩ :
        MarkedIdeal (t.endOf (boMaximalContact M m t H)).X).cosupport
      (((boMaximalContact M m t H).restrictHom H).ker.support :
        Set (boMaximalContact M m t H).target) := by
  have hBall := boMaximalContact_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax H hH
  set P := divisorSeparationSequence M m t with hPdef
  set t' := t.endOf P with ht'def
  set H' : t'.X.IdealSheafData := (P.restrictHom H).ker with hH'def
  set V : t'.X.Opens :=
    (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl with hVdef
  set EV : OrderedDivisor V :=
    ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
      fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩ with hEVdef
  set tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, EV⟩, t'.k, V.ι ≫ t'.sX⟩ with htVdef
  obtain ⟨BV, hBV⟩ : ∃ BV : ClosedBlowupSequence V, BV =
      if (V : Set t'.X).Nonempty ∧ IsTriple tV.sX tV.I tV.E then bdFunctor M (dimNat t.X) m 0 tV
      else .nil _ := ⟨_, rfl⟩
  have hBVne : BV.HasNoEmptyBlowups := by
    rw [hBV]; split_ifs
    · exact hasNoEmptyBlowups_bdFunctor ..
    · trivial
  have hne : (P.append (BV.extendByClosure V.ι)).HasNoEmptyBlowups :=
    hasNoEmptyBlowups_append _ _ (hasNoEmptyBlowups_divisorSeparationAux M m t t.E.s)
      (hasNoEmptyBlowups_extendByClosure _ _ hBVne)
  have hPC : boMaximalContact M m t H = P.append (BV.extendByClosure V.ι) := by
    rw [← ClosedBlowupSequence.reduction_eq_self hne, hBV]; rfl
  rw [hPC] at hr hBall ⊢
  have hrC : maxOrder ((BV.extendByClosure V.ι).controlledTransform t'.I) = m :=
    (append_transport (fun J _ => maxOrder J = (m : ℕ∞)) P (BV.extendByClosure V.ι) t.I
      H.subschemeι).1 hr
  refine (append_transport (fun J K => Disjoint (MarkedIdeal.cosupport ⟨J, m⟩)
    (K.support : Set _)) P (BV.extendByClosure V.ι) t.I H.subschemeι).2 ?_
  obtain ⟨hP, hC⟩ := (ClosedBlowupSequence.isOrderMTripleSeq_append_iff m P
    (BV.extendByClosure V.ι) t.sX t.I t.E).1 hBall
  have htr : IsTriple t'.sX t'.I t'.E := isTriple_of_isOrderMTripleSeq hC
  have hend := end_of_isOrderMTripleSeq m _ P t.sX t.I t.E hP hmax.le hdim
  haveI : LocallyOfFiniteType t'.sX := htr.2.2.1
  haveI : QuasiCompact t'.sX := htr.2.2.2.1
  haveI : IsLocallyNoetherian t'.X := LocallyOfFiniteType.isLocallyNoetherian t'.sX
  haveI : CompactSpace t'.X := QuasiCompact.compactSpace_of_compactSpace t'.sX
  haveI : IsNoetherian t'.X := ⟨⟩
  have hdisj : ∀ (i : ℕ) (hi : i < t.E.s), ∃ hir : i < t'.E.s,
      Disjoint (⟨t'.I, m⟩ : MarkedIdeal t'.X).cosupport ((t'.E.E ⟨i, hir⟩).support : Set t'.X) :=
    fun i hi => disjoint_cosupport_divisorSeparationSequence M hN hM t ht hdim hn hnN hm
      hmax.le i hi
  have hcosV : (⟨t'.I, m⟩ : MarkedIdeal t'.X).cosupport ⊆ (V : Set t'.X) := by
    intro x hx
    change x ∉ ((⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥ :
      TopologicalSpace.Closeds t'.X) : Set t'.X)
    rw [← Finset.sup_univ_eq_iSup, TopologicalSpace.Closeds.coe_finset_sup]
    intro hx'
    rw [Finset.sup_set_eq_biUnion] at hx'
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.1 hx'
    simp only [Function.comp_apply] at hi
    split_ifs at hi with h
    · obtain ⟨hir, hd⟩ := hdisj i h
      exact Set.disjoint_left.1 hd hx hi
    · exact hi
  have hsnc := isOrderedSNC_divisorSeparationSequence M hN hM t ht hdim hn hnN hm hmax hH
  have htV : IsTriple tV.sX tV.I tV.E := isTriple_restrict_open t' htr t.E.s hsnc.1 H' hsnc.2 V
  by_cases hVne : (V : Set t'.X).Nonempty
  swap
  · rw [if_neg fun h => hVne h.1] at hBV
    subst hBV
    refine Set.disjoint_left.2 fun x hx _ => hVne ⟨x, hcosV hx⟩
  rw [if_pos ⟨hVne, htV⟩] at hBV
  have hdN : dimNat t.X = n := dimNat_eq_of_eq hdim
  rw [hdN] at hBV
  have hdimV : topologicalKrullDim tV.X = ((n : ℕ∞) : WithBot ℕ∞) :=
    (topologicalKrullDim_opens_of_equidimensional t'.sX htr.2.2.2.2.1 V hVne).trans hend.1
  have hmaxV : maxOrder tV.I ≤ m := (maxOrder_comap_le V.ι t'.I).trans hend.2.1
  have h0 : 0 < tV.E.s := Nat.succ_pos _
  have hBVo := (bdFunctor_isOrderMTripleSeq M hN hM tV htV hdimV hn hnN hm hmaxV h0).1
  have hsep := disjoint_cosupport_bdFunctor M hN hM tV htV hdimV hn hnN hm hmaxV h0
  rw [← hBV] at hBVo hsep
  have hDmk := (isOrderGe_and_markedTransform_eq tV.sX tV.I tV.E m hmaxV BV hBVne hBVo).2
  have e := pullback_extendByClosure BV V.ι
  rw [← e] at hsep hDmk
  obtain ⟨hCge, hCmk⟩ := isOrderGe_and_markedTransform_eq t'.sX t'.I t'.E m hend.2.1 _
    (hasNoEmptyBlowups_extendByClosure BV V.ι hBVne) hC
  set C := BV.extendByClosure V.ι with hCdef
  have bridge : ((C.pullback V.ι).markedTransform ⟨tV.I, m⟩).I =
      (C.markedTransform ⟨t'.I, m⟩).I.comap (C.pullbackHom V.ι) :=
    markedTransform_pullback C V.ι t'.sX ⟨t'.I, m⟩ t'.E hCge
  haveI := isOpenImmersion_pullbackHom C V.ι
  have hrange := range_pullbackHom C V.ι
  have hcosC : (⟨C.controlledTransform t'.I, m⟩ : MarkedIdeal C.target).cosupport ⊆
      C.toBase ⁻¹' (⟨t'.I, m⟩ : MarkedIdeal t'.X).cosupport := by
    have h := ClosedBlowupSequence.cosupport_markedTransform_truncate_subset t'.sX ⟨t'.I, m⟩ t'.E
      C hCge C.length
    rw [truncate_length] at h
    intro x hx
    apply h
    change ((C.markedTransform ⟨t'.I, m⟩).m : ℕ∞) ≤ multAt (C.markedTransform ⟨t'.I, m⟩).I x
    rwa [ClosedBlowupSequence.markedTransform_m, hCmk]
  haveI : IsClosedImmersion (P.restrictHom H) :=
    Kollar.isClosedImmersion_pullbackHom P H.subschemeι
  haveI : IsClosedImmersion (C.pullbackHom (P.restrictHom H)) :=
    @Kollar.isClosedImmersion_pullbackHom _ _ C (P.restrictHom H)
      (Kollar.isClosedImmersion_pullbackHom P H.subschemeι)
  obtain ⟨hjr, hd⟩ := hsep
  refine Set.disjoint_left.2 fun x hx hxH => ?_
  have hxV : x ∈ Set.range (C.pullbackHom V.ι) := by
    rw [hrange, Scheme.Opens.range_ι]
    exact hcosV (hcosC hx)
  obtain ⟨u, rfl⟩ := hxV
  have hu1 : u ∈ (⟨(C.pullback V.ι).controlledTransform tV.I, m⟩ :
      MarkedIdeal (C.pullback V.ι).target).cosupport := by
    change (m : ℕ∞) ≤ multAt _ u
    rw [← hDmk, bridge, hCmk]
    exact le_multAt_comap _ _ u hx
  have hu2 : u ∈ ((((C.pullback V.ι).orderedTotalTransform tV.E).E ⟨0, hjr⟩).support :
      Set (C.pullback V.ι).target) := by
    have h1 : C.pullbackHom V.ι u ∈ closure (strictSet C (Set.range (P.restrictHom H))) := by
      have : C.pullbackHom V.ι u ∈ closure (Set.range (C.pullbackHom (P.restrictHom H))) := by
        rwa [← Scheme.Hom.support_ker]
      exact closure_mono (range_pullbackHom_subset_strictSet C _ _ subset_rfl) this
    have h2 : u ∈ closure (strictSet (C.pullback V.ι) (V.ι ⁻¹' Set.range (P.restrictHom H))) := by
      rw [← preimage_strictSet_pullbackHom,
        ← (C.pullbackHom V.ι).isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
          (C.pullbackHom V.ι).continuous]
      exact h1
    have hT : V.ι ⁻¹' Set.range (P.restrictHom H) ⊆ ((tV.E.E ⟨0, h0⟩).support : Set V) := by
      intro v hv
      change v ∈ ((H'.comap V.ι).support : Set V)
      rw [SetLike.mem_coe, mem_support_comap_iff]
      have hk : ((P.restrictHom H).ker.support : Set P.target) =
          closure (Set.range (P.restrictHom H)) := Scheme.Hom.support_ker _
      show V.ι v ∈ ((P.restrictHom H).ker.support : Set P.target)
      rw [hk]
      exact subset_closure hv
    exact closure_minimal (strictSet_subset_support_orderedTotalTransform _ tV.E 0 h0 _ hT hjr)
      (TopologicalSpace.Closeds.isClosed _) h2
  exact Set.disjoint_left.1 hd hu1 hu2

/-- **Kollár, Thm. 3.103 Step 2.2.** Let `𝓜` be a marked order-reduction family on dimensions
`0, …, N - 1` (`IsMarkedOrderReductionFamily`), `(X, J, E)` a triple of dimension `n` with
`1 ≤ n ≤ N`, `m ≥ 1` with `maxord J = m`, and `H` an MC-hypersurface for `J`
(`IsMCHypersurface`). Then the last ideal `J_r` of the end of `boMaximalContact M m (X, J, E) H`
(`FieldBlowupTriple.endOf`) has `maxord J_r < m`. -/
@[mmp "lem_kr3e_bo_maximal_contact_reduces_order"]
public theorem maxOrder_endOf_boMaximalContact_lt {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) (H : t.X.IdealSheafData)
    (hH : IsMCHypersurface t.sX t.I H) :
    maxOrder (t.endOf (boMaximalContact M m t H)).I < m := by
  set B := boMaximalContact M m t H with hBdef
  have hB := boMaximalContact_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax H hH
  refine lt_of_le_of_ne (end_of_isOrderMTripleSeq m _ B _ _ _ hB hmax.le rfl).2.1 fun hr => ?_
  haveI := (isTriple_of_isOrderMTripleSeq hB).1
  have hHr := hB.isMCHypersurface_ker_restrictHom (by rw [hdim]; exact_mod_cast hn) hm hmax hH hr
  have hdisj := disjoint_cosupport_support_ker_restrictHom M hN hM t ht hdim hn hnN hm hmax H hH hr
  replace hr : maxOrder (B.controlledTransform t.I) = m := hr
  obtain ⟨hchar, hXr, hlft, hqc, hequi, hIr, -⟩ :=
    ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m B _ _ _ hB
  haveI := hchar; haveI := hlft; haveI := hqc
  haveI := Aux.smooth_of_isSmoothScheme' _ hXr
  have hcos : (⟨B.controlledTransform t.I, m⟩ : MarkedIdeal B.target).cosupport ⊆
      ((B.restrictHom H).ker.support : Set B.target) := by
    have hsupp := support_maximalContactIdeal (B.toBase ≫ t.sX)
      (exists_forall_topologicalKrullDim_eq hequi) hIr (by rw [hr]; exact_mod_cast hm)
    rw [hr, ENat.toNat_coe] at hsupp
    rw [← hsupp]
    exact Scheme.IdealSheafData.support_antitone hHr.2
  obtain ⟨x, hx⟩ := cosupport_nonempty_of_maxOrder_eq hm hr
  exact Set.disjoint_left.1 hdisj hx (hcos hx)

/-! ### `𝓑𝓞^H_m` does not depend on `H` -/

/-! ### Orders and dimensions along the inclusions of the pieces of a cover -/

/-- A morphism `g : Y → X` every point of whose source lies in the image of an open immersion
`ι : Z → Y` with `ι ≫ g` an open immersion: `⊔ U_i → X` for an open cover `(U_i)` of `X`. -/
private def IsLocallyOpenImmersion {X Y : Scheme.{u}} (g : Y ⟶ X) : Prop :=
  ∀ y : Y, ∃ (Z : Scheme.{u}) (ι : Z ⟶ Y) (z : Z),
    IsOpenImmersion ι ∧ IsOpenImmersion (ι ≫ g) ∧ ι z = y

private theorem IsLocallyOpenImmersion.multAt_comap {X Y : Scheme.{u}} {g : Y ⟶ X}
    (hg : IsLocallyOpenImmersion g) (K : X.IdealSheafData) (y : Y) :
    multAt (K.comap g) y = multAt K (g y) := by
  obtain ⟨Z, ι, z, h1, h2, rfl⟩ := hg y
  rw [← multAt_comap_of_isOpenImmersion ι, ← Scheme.IdealSheafData.comap_comp,
    multAt_comap_of_isOpenImmersion (ι ≫ g), Scheme.Hom.comp_apply]

private theorem IsLocallyOpenImmersion.maxOrder_comap_le {X Y : Scheme.{u}} {g : Y ⟶ X}
    (hg : IsLocallyOpenImmersion g) (K : X.IdealSheafData) :
    maxOrder (K.comap g) ≤ maxOrder K := by
  refine iSup₂_le fun y _ => ?_
  rw [hg.multAt_comap]
  exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt K z) _ (Set.mem_univ _)

private theorem IsLocallyOpenImmersion.topologicalKrullDimAt_eq {X Y : Scheme.{u}}
    {g : Y ⟶ X} (hg : IsLocallyOpenImmersion g) (y : Y) :
    topologicalKrullDimAt Y y = topologicalKrullDimAt X (g y) := by
  obtain ⟨Z, ι, z, h1, h2, rfl⟩ := hg y
  rw [← Scheme.Hom.comp_apply, ι.isOpenEmbedding.topologicalKrullDimAt_eq z,
    (ι ≫ g).isOpenEmbedding.topologicalKrullDimAt_eq z]

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-compact scheme has a smooth surjection from an affine scheme which is locally an open
immersion: `⊔ U_i → X` for a finite affine open cover `(U_i)`. -/
private theorem exists_affine_cover (X : Scheme.{u}) [CompactSpace X] :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), IsAffine Y ∧ Smooth g ∧ Surjective g ∧
      IsLocallyOpenImmersion g := by
  let 𝒰 := X.affineCover.finiteSubcover
  refine ⟨∐ 𝒰.X, Limits.Sigma.desc 𝒰.f, inferInstance,
    IsZariskiLocalAtSource.sigmaDesc (P := @Smooth.{u}) (fun i => inferInstance), ⟨fun x => ?_⟩,
    fun y => ?_⟩
  · obtain ⟨i, z, hz⟩ := 𝒰.exists_eq x
    exact ⟨Limits.Sigma.ι 𝒰.X i z, by rw [← hz, ← Scheme.Hom.comp_apply, Limits.Sigma.ι_desc]⟩
  · obtain ⟨⟨i, z⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk 𝒰.X).surjective y
    refine ⟨𝒰.X i, Limits.Sigma.ι 𝒰.X i, z, inferInstance, ?_,
      (AlgebraicGeometry.sigmaMk_mk _ i z).symm⟩
    rw [Limits.Sigma.ι_desc]
    infer_instance

/-- The source of a surjection which is locally an open immersion onto an equidimensional scheme
locally of finite type over a field is equidimensional of the same dimension. -/
private theorem IsLocallyOpenImmersion.equidimensional {k : Type u} [Field k]
    {X Y : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] {g : Y ⟶ X}
    [LocallyOfFiniteType (g ≫ s)] (hg : IsLocallyOpenImmersion g) (hgs : Surjective g)
    (hX : TopologicalSpace.Equidimensional X) :
    TopologicalSpace.Equidimensional Y ∧ topologicalKrullDim Y = topologicalKrullDim X := by
  have key : ∀ Z ∈ irreducibleComponents Y, ∀ C ∈ irreducibleComponents X,
      topologicalKrullDim Z = topologicalKrullDim C := fun Z hZ C hC => by
    rw [topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint (g ≫ s) hZ,
      hg.topologicalKrullDimAt_eq, topologicalKrullDimAt_eq_of_mem_irreducibleComponents s hX _ hC]
  refine ⟨fun Z hZ W hW => ?_, ?_⟩
  · obtain ⟨η⟩ : Nonempty Y := ⟨hZ.1.genericPoint⟩
    have hC := irreducibleComponent_mem_irreducibleComponents (g η)
    rw [key Z hZ _ hC, key W hW _ hC]
  · by_cases hY : Nonempty Y
    · obtain ⟨y⟩ := hY
      have hC := irreducibleComponent_mem_irreducibleComponents (g y)
      rw [topologicalKrullDim_eq_of_forall_components y fun Z hZ => key Z hZ _ hC,
        topologicalKrullDim_eq_of_forall_components (g y) fun D hD => hX D hD _ hC]
    · have hX' : ¬ Nonempty X := fun ⟨x⟩ => hY ⟨(hgs.surj x).choose⟩
      have e1 : irreducibleComponents Y = ∅ :=
        Set.eq_empty_of_forall_notMem fun Z hZ => hY ⟨hZ.1.nonempty.some⟩
      have e2 : irreducibleComponents X = ∅ :=
        Set.eq_empty_of_forall_notMem fun Z hZ => hX' ⟨hZ.1.nonempty.some⟩
      rw [topologicalKrullDim_eq_iSup_irreducibleComponents Y,
        topologicalKrullDim_eq_iSup_irreducibleComponents X, e1, e2]
      simp

/-! ### The local-to-global step -/

/-! ### The affine case -/

/-- An snc family stays one after reindexing along an injective map. -/
private theorem isSNCFamily_comp {k : Type u} [Field k] {X : Scheme.{u}} {s : X ⟶ Spec (.of k)}
    {Λ Λ' : Type*} {E : Λ → X.IdealSheafData} (h : IsSNCFamily s E) (g : Λ' → Λ)
    (hg : Function.Injective g) : IsSNCFamily s (E ∘ g) := by
  refine ⟨fun i => h.1 (g i), fun x => ?_⟩
  obtain ⟨n, z, c, hz, hc, hinj⟩ := h.2 x
  exact ⟨n, z, fun i => c ⟨g i.1, i.2⟩, hz, fun i => hc ⟨g i.1, i.2⟩,
    fun i j hij => Subtype.ext (hg (congrArg Subtype.val (hinj hij)))⟩

/-- The pull-back along a flat morphism `h` of a sequence without empty blow-ups whose centres lie
over a set covered by the image of `h` has no empty blow-ups. -/
private theorem hasNoEmptyBlowups_pullback_of_centersLieOver :
    ∀ {X Y X₀ : Scheme.{u}} (B : ClosedBlowupSequence X) (h : Y ⟶ X) [Flat h] (f : X ⟶ X₀)
      (S : Set X₀), (∀ x, f x ∈ S → x ∈ Set.range h) → B.HasNoEmptyBlowups →
      B.CentersLieOver f S → (B.pullback h).HasNoEmptyBlowups
  | _, _, _, .nil _, _, _, _, _, _, _, _ => trivial
  | _, _, _, .cons Z B, h, _, f, S, hS, hB, hc => by
    refine ⟨fun htop => ?_, ?_⟩
    · obtain ⟨x, hx⟩ : ∃ x, x ∈ Z.support := by
        by_contra hne
        push Not at hne
        exact hB.1 ((Scheme.IdealSheafData.support_eq_bot_iff _).1
          (Closeds.ext (Set.eq_empty_of_forall_notMem hne)))
      obtain ⟨y, rfl⟩ := hS x (hc.1 ⟨x, hx, rfl⟩)
      have hy : y ∈ ((Z.comap h).support : Set _) := by
        rwa [Scheme.IdealSheafData.support_comap]
      rwa [htop, Scheme.IdealSheafData.support_top] at hy
    · have := Kollar.flat_canonicalLift h Z
      refine hasNoEmptyBlowups_pullback_of_centersLieOver B (canonicalLift h Z)
        (blowUpToBase Z ≫ f) S (fun x hx => ?_) hB.2 hc.2
      obtain ⟨y, hy⟩ := hS _ hx
      have hP := Kollar.isPullback_canonicalLift_of_flat h Z
      obtain ⟨z, -, hz2⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := h) (g := blowUpToBase Z) y x hy
      refine ⟨hP.isoPullback.inv z, ?_⟩
      rw [← Scheme.Hom.comp_apply, hP.isoPullback_inv_snd, hz2]

/-- An ideal sheaf of finite order at every generic point is nonzero there. -/
private theorem isNonzeroAtGenericPoints_of_multAt_ne_top {X : Scheme.{u}} {I : X.IdealSheafData}
    (h : ∀ x, multAt I x ≠ ⊤) : IsNonzeroAtGenericPoints I := by
  intro η _ hη
  apply h η
  unfold multAt
  rw [hη]
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  exact le_iSup₂_of_le (f := fun (j : ℕ) (_ : (⊥ : Ideal _) ≤ IsLocalRing.maximalIdeal _ ^ j) =>
    (j : ℕ∞)) n bot_le le_rfl

/-- `MC(I) ⊆ W_1(I)`: the summand of `W_1(I)` at the unit vector `e_{m-1}` is `D^{m-1}(I)`. -/
private theorem maximalContactIdeal_le_maximalCoefficientIdeal_one {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
    (hm : 1 ≤ (maxOrder I).toNat) :
    maximalContactIdeal sX I ≤ maximalCoefficientIdeal sX I 1 := by
  unfold maximalCoefficientIdeal maximalContactIdeal
  generalize (maxOrder I).toNat = m at hm ⊢
  let j : Fin (m + 1) := ⟨m - 1, by omega⟩
  convert le_iSup₂ (f := fun (c : Fin (m + 1) → ℕ) (_ : (1 : ℤ) ≤ coefficientWeight m c) =>
    ∏ i : Fin (m + 1), higherDerivativeIdeal sX I (i : ℕ) ^ c i) (Pi.single j 1) ?_
  · rw [Finset.prod_eq_single j (fun b _ hb => by simp [hb]) (by simp)]; simp [j]
  · simp [coefficientWeight, Pi.single_apply, j]; omega

/-- A smooth blow-up sequence of order `m` starting with a triple `(X, I, E)` is one starting with
`(X, I)`. -/
private theorem isOrderMPlainSeq_of_isOrderMTripleSeq {k : Type u} [Field k] (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X), B.IsOrderMTripleSeq s I E m →
      B.IsOrderMPlainSeq s I m
  | _, .nil _, _, _, _, h => ⟨h.2.1, h.2.2.2.2.2.1⟩
  | _, .cons _ B, _, _, _, h =>
    ⟨h.1.2.1, h.1.2.2.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2.1,
      isOrderMPlainSeq_of_isOrderMTripleSeq m B _ _ _ h.2.2.2.2.2⟩

/-- A smooth blow-up sequence of order `m` starting with a triple is a smooth blow-up
sequence. -/
private theorem isSmooth_of_isOrderMTripleSeq {k : Type u} [Field k] (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (s : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X), B.IsOrderMTripleSeq s I E m →
      B.IsSmooth s
  | _, .nil _, _, _, _, _ => trivial
  | _, .cons _ B, _, _, _, h =>
    ⟨h.1.2.1, h.2.1, isSmooth_of_isOrderMTripleSeq m B _ _ _ h.2.2.2.2.2⟩

/-- `𝓑𝓓` depends on the ideal `I` only through `maxord I` and `W_{m!}(I)`. -/
private theorem bdFunctor_congr (M : MarkedFamily.{u}) (n m j : ℕ) {k : Type u} [Field k]
    {X : Scheme.{u}} (sX sX' : X ⟶ Spec (.of k)) (hs : sX = sX') (I I' : X.IdealSheafData)
    (E E' : OrderedDivisor X) (hE : E = E') (hI : maxOrder I = maxOrder I')
    (hW : maximalCoefficientIdeal sX I (m.factorial : ℤ) =
      maximalCoefficientIdeal sX I' (m.factorial : ℤ)) :
    bdFunctor M n m j ⟨⟨X, I, E⟩, k, sX⟩ = bdFunctor M n m j ⟨⟨X, I', E'⟩, k, sX'⟩ := by
  subst hs hE
  unfold bdFunctor
  by_cases h : maxOrder I = m ∧ j < E.s
  · rw [dite_cond_eq_true (eq_true h), dite_cond_eq_true (eq_true (hI ▸ h))]
    dsimp only
    rw [hW]
  · rw [dite_cond_eq_false (eq_false h), dite_cond_eq_false (eq_false (hI ▸ h))]

/-- Orders are unchanged along an étale morphism of smooth schemes over a field. -/
private theorem multAt_comap_of_etale {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (φ : Y ⟶ X) [Etale φ] (I : X.IdealSheafData) (y : Y) :
    multAt (I.comap φ) y = multAt I (φ y) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (φ ≫ sX)
  refine MMP.Flips.ResolutionInputs.multAt_comap_eq φ
    (isRegularLocalRing_stalk_of_smooth_over_field sX)
    (isRegularLocalRing_stalk_of_smooth_over_field (φ ≫ sX))
    (fun y => AlgebraicGeometry.isRegularLocalRing_closedFibre_of_smooth φ y) I y

/-- An étale scheme over an equidimensional scheme smooth over a field is equidimensional of the
same dimension. -/
private theorem equidimensional_of_etale {k : Type u} [Field k] {X U : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [Smooth sX] (φ : U ⟶ X) [Etale φ] [QuasiCompact (φ ≫ sX)]
    (hX : TopologicalSpace.Equidimensional X) {n : ℕ}
    (hdim : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞)) (hU : Nonempty U) :
    TopologicalSpace.Equidimensional U ∧ topologicalKrullDim U = ((n : ℕ∞) : WithBot ℕ∞) := by
  have hcompX : ∀ C ∈ irreducibleComponents X,
      topologicalKrullDim C = ((n : ℕ∞) : WithBot ℕ∞) := by
    intro C hC
    apply le_antisymm
    · rw [← hdim]; exact topologicalKrullDim_subspace_le X C
    · rw [← hdim, topologicalKrullDim_eq_iSup_irreducibleComponents X]
      exact iSup₂_le fun D hD => (hX D hD C hC).le
  have hU' : ∀ u : U, topologicalKrullDimAt U u = ((n : ℕ∞) : WithBot ℕ∞) := fun u =>
    (topologicalKrullDimAt_eq_of_etale φ u).trans
      ((topologicalKrullDimAt_eq_of_mem_irreducibleComponents sX hX (φ u)
        (irreducibleComponent_mem_irreducibleComponents (φ u))).trans
        (hcompX _ (irreducibleComponent_mem_irreducibleComponents (φ u))))
  have hcompU : ∀ Z ∈ irreducibleComponents U,
      topologicalKrullDim Z = ((n : ℕ∞) : WithBot ℕ∞) := fun Z hZ =>
    (topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint (φ ≫ sX) hZ).trans (hU' _)
  refine ⟨fun Z hZ W hW => (hcompU Z hZ).trans (hcompU W hW).symm, ?_⟩
  obtain ⟨u⟩ := hU
  exact topologicalKrullDim_eq_of_forall_components u hcompU

/-- **The affine case.** On an affine `Y`, for two smooth hypersurfaces `H₁, H₂ ⊆ W_1(J)` making
`(Y, J, (H_a, E))` triples, the sequences `𝓑𝓓_{dim Y, m, 1}(Y, J, (H_a, E))` agree: by uniqueness
of maximal contact for the MC-invariant `W = W_{m!}(J)` they are étale equivalent, and `Y` is
separated. -/
private theorem bdFunctor_eq_of_isAffine {N m n : ℕ} (M : MarkedFamily.{u}) (hN : 1 ≤ N)
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnN : n ≤ N)
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsAffine Y] (sY : Y ⟶ Spec (.of k))
    (J : Y.IdealSheafData) (E : OrderedDivisor Y) (H₁ H₂ : Y.IdealSheafData)
    (hdim : topologicalKrullDim Y = ((n : ℕ∞) : WithBot ℕ∞)) (hJ : maxOrder J = m)
    (hT₁ : IsTriple sY J ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H₁ E.E⟩)
    (hT₂ : IsTriple sY J ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H₂ E.E⟩)
    (hH₁ : H₁ ≤ maximalCoefficientIdeal sY J 1) (hH₂ : H₂ ≤ maximalCoefficientIdeal sY J 1) :
    bdFunctor M (dimNat Y) m 0
        ⟨⟨Y, J, ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H₁ E.E⟩⟩, k, sY⟩ =
      bdFunctor M (dimNat Y) m 0
        ⟨⟨Y, J, ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H₂ E.E⟩⟩, k, sY⟩ := by
  have hμ1 : 1 ≤ m.factorial := Nat.factorial_pos m
  obtain ⟨hchar, hsm, hlft, hqc, hequi, hJnz, hEsnc₁⟩ := hT₁
  have hEsnc₂ := hT₂.2.2.2.2.2.2
  have := hchar
  have := hlft
  have := hqc
  have : Smooth sY := Aux.smooth_of_isSmoothScheme' sY hsm
  have hcomp : ∀ Z ∈ irreducibleComponents Y,
      topologicalKrullDim Z = ((n : ℕ∞) : WithBot ℕ∞) := by
    intro Z hZ
    apply le_antisymm
    · rw [← hdim]; exact topologicalKrullDim_subspace_le Y Z
    · rw [← hdim, topologicalKrullDim_eq_iSup_irreducibleComponents Y]
      exact iSup₂_le fun W hW => (hequi W hW Z hZ).le
  have hdimpos : ∀ Z ∈ irreducibleComponents Y, 0 < topologicalKrullDim Z := by
    intro Z hZ
    rw [hcomp Z hZ]
    exact_mod_cast hn
  have hdim1 : 1 ≤ topologicalKrullDim Y := by
    rw [hdim]; exact_mod_cast hn
  have hJn : (maxOrder J).toNat = m := by rw [hJ]; rfl
  have hmJ : 1 ≤ (maxOrder J).toNat := hJn ▸ hm
  set W := maximalCoefficientIdeal sY J (m.factorial : ℤ) with hWdef
  have hWmax : maxOrder W = m.factorial :=
    Kollar.maxOrder_maximalCoefficientIdeal sY hsm hequi hdim1 J hmJ hμ1
  have hWn : (maxOrder W).toNat = m.factorial := by rw [hWmax]; rfl
  have hMCW : maximalContactIdeal sY W = maximalCoefficientIdeal sY J 1 :=
    Kollar.maximalContactIdeal_maximalCoefficientIdeal sY hequi hdim1 J hmJ hμ1
  have hWmc : IsMCInvariant sY W := by
    obtain ⟨s, hs⟩ : ∃ s : ℕ, m.factorial = s + 1 := ⟨m.factorial - 1, by omega⟩
    rw [IsMCInvariant, hMCW, hWdef]
    have hsz : ((m.factorial : ℕ) : ℤ) = (s : ℤ) + 1 := by rw [hs]; push_cast; rfl
    rw [hsz, Kollar.derivativeIdeal_maximalCoefficientIdeal_succ sY hequi hdim1 J hmJ s,
      add_comm]
    exact Kollar.maximalCoefficientIdeal_mul_le sY J 1 s
  have hJle : ∀ x, multAt J x ≤ m := fun x =>
    hJ ▸ le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt J z) x (Set.mem_univ _)
  have hord := fun x => multAt_maximalCoefficientIdeal sY hequi hdimpos hJnz hm hJ hμ1 x
  have hWnz : IsNonzeroAtGenericPoints W := by
    refine isNonzeroAtGenericPoints_of_multAt_ne_top fun x => ?_
    rcases (hJle x).lt_or_eq with h | h
    · rw [(hord x).2 h]; exact ENat.zero_ne_top
    · rw [(hord x).1 h]; exact ENat.natCast_ne_top _
  obtain ⟨x₀, hx₀⟩ : ∃ x, multAt J x = m := by
    by_contra hne
    push Not at hne
    have hle : maxOrder J ≤ ((m - 1 : ℕ) : ℕ∞) := iSup₂_le fun x _ => by
      have hlt := (hJle x).lt_of_ne (hne x)
      obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_lt hlt)
      rw [← ha] at hlt ⊢
      have := ENat.natCast_lt_natCast.1 hlt
      exact ENat.natCast_le_natCast.2 (by omega)
    rw [hJ] at hle
    have := ENat.natCast_le_natCast.1 hle
    omega
  have hx₀W : x₀ ∈ (⟨W, m.factorial⟩ : MarkedIdeal Y).cosupport := ((hord x₀).1 hx₀).ge
  have hEo : E.IsOrderedDivisor := fun i => hEsnc₁.1 i.succ
  have hEs : E.IsSNC sY := by
    have h := isSNCFamily_comp hEsnc₁.2 Fin.succ (Fin.succ_injective _)
    exact h
  have hHs₁ : IsSmoothHypersurface sY H₁ := ⟨(hEsnc₁.2.1 0).2.2, (hEsnc₁.2.1 0).2.1⟩
  have hHs₂ : IsSmoothHypersurface sY H₂ := ⟨(hEsnc₂.2.1 0).2.2, (hEsnc₂.2.1 0).2.1⟩
  obtain ⟨U, sU, ψ, ψ', hψ, hHH, hEE⟩ := areEtaleEquivalentHypersurfaces_of_le_maximalContactIdeal
    sY hequi hdimpos hWmc hWnz hμ1 hWmax hEo hEs hHs₁ hHs₂ (hMCW ▸ hH₁) (hMCW ▸ hH₂) hEsnc₁.2
    hEsnc₂.2
  have hdn : dimNat Y = n := dimNat_eq_of_eq hdim
  have hsub : ∀ {φ : U ⟶ Y}, (⟨W, (maxOrder W).toNat⟩ : MarkedIdeal Y).cosupport ⊆
      Set.range φ → (⟨W, m.factorial⟩ : MarkedIdeal Y).cosupport ⊆ Set.range φ := by
    intro φ h; rwa [hWn] at h
  have hc := hsub hψ.cosupport_subset
  have hc' := hsub hψ.cosupport_subset'
  have hUne : Nonempty U := ⟨(hc hx₀W).choose⟩
  have := hψ.locallyOfFiniteType
  have := hψ.quasiCompact
  have := hψ.etale
  have := hψ.etale'
  have hqcψ : QuasiCompact (ψ ≫ sY) := by rw [hψ.comp_eq]; infer_instance
  obtain ⟨hUe, hUd⟩ := equidimensional_of_etale sY ψ hequi hdim hUne
  have hmaxU : ∀ φ : U ⟶ Y, Etale φ → (⟨W, m.factorial⟩ : MarkedIdeal Y).cosupport ⊆
      Set.range φ → maxOrder (J.comap φ) = m := by
    intro φ _ hφ
    refine le_antisymm (iSup₂_le fun u _ => ?_) ?_
    · rw [multAt_comap_of_etale sY φ]; exact hJle _
    · obtain ⟨u, hu⟩ := hφ hx₀W
      rw [← hx₀, ← hu, ← multAt_comap_of_etale sY φ]
      exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt (J.comap φ) z) u (Set.mem_univ _)
  have key : ∀ H : Y.IdealSheafData,
      IsTriple sY J ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H E.E⟩ →
      (bdFunctor M (dimNat Y) m 0
        ⟨⟨Y, J, ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H E.E⟩⟩, k,
          sY⟩).IsOrderMPlainSeq sY W m.factorial := by
    intro H hT
    have hB := (bdFunctor_isOrderMTripleSeq (j := 0) M hN hM
      ⟨⟨Y, J, ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H E.E⟩⟩, k, sY⟩ hT hdim hn hnN hm
      hJ.le (Nat.succ_pos _)).1
    rw [hdn]
    have hsm' := isSmooth_of_isOrderMTripleSeq m _ _ _ _ hB
    have h1 := (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq sY J _ hT m
      hJ _).1.2 hB
    have h2 := ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_maximalCoefficientIdeal_of_dvd
      sY J _ hT hdimpos hmJ m.factorial hμ1 (by rw [hJn]; exact Nat.dvd_factorial hm le_rfl) _ hsm'
    rw [hJn] at h2
    have hTW : IsTriple sY W ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H E.E⟩ :=
      ⟨hchar, hsm, hlft, hqc, hequi, hWnz, hT.2.2.2.2.2.2⟩
    have h3 := (ClosedBlowupSequence.isOrderGeMarkedTripleSeq_iff_isOrderMTripleSeq sY W _ hTW
      m.factorial hWmax _).1.1 (h2.1 h1)
    exact isOrderMPlainSeq_of_isOrderMTripleSeq _ _ _ _ _ h3
  have hpb : ∀ H : Y.IdealSheafData,
      IsTriple sY J ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H E.E⟩ →
      ∀ (φ : U ⟶ Y) [Etale φ], φ ≫ sY = sU →
        (⟨W, m.factorial⟩ : MarkedIdeal Y).cosupport ⊆ Set.range φ →
        bdFunctor M (dimNat U) m 0
          ((⟨⟨Y, J, ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H E.E⟩⟩, k, sY⟩ :
            FieldBlowupTriple.{u}).pullback φ) =
        (bdFunctor M (dimNat Y) m 0
          ⟨⟨Y, J, ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H E.E⟩⟩, k, sY⟩).pullback
            φ := by
    intro H hT φ _ hφs hφc
    let t : FieldBlowupTriple.{u} :=
      ⟨⟨Y, J, ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H E.E⟩⟩, k, sY⟩
    have hmemV : t ∈ {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ 0 < t.E.s} :=
      ⟨⟨hT, ⟨n, ⟨hn, hnN⟩, hdim⟩, hJ.le⟩, Nat.succ_pos _⟩
    have : QuasiCompact (φ ≫ t.sX) := by
      change QuasiCompact (φ ≫ sY); rw [hφs]; infer_instance
    have : Smooth φ := inferInstance
    have hTt : t ∈ triples := hT
    have hsn : t.pullback φ ∈ sncTriples :=
      pullback_mem_sncTriples (t := t) (mem_sncTriples_of_mem_triples hTt) φ
    have hmemU : t.pullback φ ∈ {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ 0 < t.E.s} :=
      ⟨⟨mem_triples_iff.2 ⟨hsn, hUe⟩,
        ⟨n, ⟨hn, hnN⟩, hUd⟩, (hmaxU φ inferInstance hφc).le⟩, Nat.succ_pos _⟩
    have h := (commutesWithSmoothOn_bdFunctor (j := 0) M hN hM hm).2 t hmemV U φ inferInstance
      inferInstance inferInstance hmemU
    refine h.trans (ClosedBlowupSequence.reduction_eq_self ?_)
    exact hasNoEmptyBlowups_pullback_of_centersLieOver _ φ (𝟙 Y) _ (fun x hx => hφc hx)
      (hasNoEmptyBlowups_bdFunctor _ _ _ _ _)
      (ClosedBlowupSequence.centersLieOver_cosupport_of_isOrderMPlainSeq sY hsm hequi W hWnz
        m.factorial hμ1 hWmax.le _ (key H hT))
  have hT₁ : IsTriple sY J ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) H₁ E.E⟩ :=
    ⟨hchar, hsm, hlft, hqc, hequi, hJnz, hEsnc₁⟩
  refine ClosedBlowupSequence.eq_of_areEtaleEquivalent sY hequi hdimpos hWnz hμ1 hWmax
    (key H₁ hT₁) (key H₂ hT₂) ⟨U, sU, ψ, ψ', hψ, ?_⟩
  rw [← hpb H₁ hT₁ ψ hψ.comp_eq hc, ← hpb H₂ hT₂ ψ' hψ.comp_eq' hc']
  have hUsm : MMP.Mori.IsSmoothScheme (ψ ≫ sY) := (MMP.Mori.isSmoothScheme_iff _).2 inferInstance
  have hW₁ := Kollar.maximalCoefficientIdeal_comap_of_smooth sY (ψ ≫ sY) hsm hUsm hequi hUe hdim1
    ψ rfl J hmJ ((hmaxU ψ inferInstance hc).trans hJ.symm) (m.factorial : ℤ)
  have hW₂ := Kollar.maximalCoefficientIdeal_comap_of_smooth sY (ψ ≫ sY) hsm hUsm hequi hUe hdim1
    ψ' (hψ.comp_eq'.trans hψ.comp_eq.symm) J hmJ ((hmaxU ψ' inferInstance hc').trans hJ.symm)
    (m.factorial : ℤ)
  refine bdFunctor_congr M _ m 0 (ψ ≫ sY) (ψ' ≫ sY) (hψ.comp_eq.trans hψ.comp_eq'.symm) _ _ _ _
    ?_ ((hmaxU ψ inferInstance hc).trans (hmaxU ψ' inferInstance hc').symm)
    (hW₁.trans (hψ.comap_eq.trans hW₂.symm))
  change (⟨_, _⟩ : OrderedDivisor U) = ⟨_, _⟩
  congr 1
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact hHH
  · exact hEE i

/-- Along a surjection which is locally an open immersion the maximal order is unchanged. -/
private theorem IsLocallyOpenImmersion.maxOrder_comap_eq {X Y : Scheme.{u}} {g : Y ⟶ X}
    (hg : IsLocallyOpenImmersion g) (hs : Surjective g) (K : X.IdealSheafData) :
    maxOrder (K.comap g) = maxOrder K := by
  refine le_antisymm (hg.maxOrder_comap_le K) (iSup₂_le fun x _ => ?_)
  obtain ⟨y, rfl⟩ := hs.surj x
  rw [← hg.multAt_comap]
  exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt (K.comap g) z) _ (Set.mem_univ _)

/-- The affine case, for the restriction to an open `V ⊆ X` of a triple `(X, I, (K_a, F))` with
`K_a ⊆ MC(I)`, pulled back along a smooth surjection `g : Y → V` from an affine scheme which is
locally an open immersion. -/
private theorem bdFunctor_pullback_eq_aux {N m n : ℕ} (M : MarkedFamily.{u}) (hN : 1 ≤ N)
    (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m) (hn : 1 ≤ n) (hnN : n ≤ N)
    {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (hXs : MMP.Mori.IsSmoothScheme sX) (hXe : TopologicalSpace.Equidimensional X)
    (hXdim : topologicalKrullDim X = ((n : ℕ∞) : WithBot ℕ∞))
    (I : X.IdealSheafData) (hmax : maxOrder I = m) (V : X.Opens)
    (hJV : maxOrder (I.comap V.ι) = m) (s : ℕ)
    (F : Fin s → X.IdealSheafData) (K₁ K₂ : X.IdealSheafData)
    (hK₁ : K₁ ≤ maximalContactIdeal sX I) (hK₂ : K₂ ≤ maximalContactIdeal sX I)
    (d : ℕ) {Y : Scheme.{u}} (g : Y ⟶ V) [IsAffine Y] [Smooth g] [Surjective g]
    [QuasiCompact (g ≫ V.ι ≫ sX)]
    (hgl : IsLocallyOpenImmersion g) (hYe : TopologicalSpace.Equidimensional Y)
    (hdimY : topologicalKrullDim Y = ((n : ℕ∞) : WithBot ℕ∞)) (hd : dimNat Y = d)
    (hA₁ : IsTriple (V.ι ≫ sX) (I.comap V.ι) ⟨s + 1, Fin.cons
      (α := fun _ => (V : Scheme.{u}).IdealSheafData) (K₁.comap V.ι) fun i => (F i).comap V.ι⟩)
    (hA₂ : IsTriple (V.ι ≫ sX) (I.comap V.ι) ⟨s + 1, Fin.cons
      (α := fun _ => (V : Scheme.{u}).IdealSheafData) (K₂.comap V.ι) fun i => (F i).comap V.ι⟩) :
    @Eq (ClosedBlowupSequence Y)
      (bdFunctor M d m 0 ((⟨⟨V, I.comap V.ι, ⟨s + 1, Fin.cons
        (α := fun _ => (V : Scheme.{u}).IdealSheafData) (K₁.comap V.ι)
          fun i => (F i).comap V.ι⟩⟩, k, V.ι ≫ sX⟩ : FieldBlowupTriple.{u}).pullback g))
      (bdFunctor M d m 0 ((⟨⟨V, I.comap V.ι, ⟨s + 1, Fin.cons
        (α := fun _ => (V : Scheme.{u}).IdealSheafData) (K₂.comap V.ι)
          fun i => (F i).comap V.ι⟩⟩, k, V.ι ≫ sX⟩ : FieldBlowupTriple.{u}).pullback g)) := by
  let tV : X.IdealSheafData → FieldBlowupTriple.{u} := fun K =>
    ⟨⟨V, I.comap V.ι, ⟨s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData)
      (K.comap V.ι) fun i => (F i).comap V.ι⟩⟩, k, V.ι ≫ sX⟩
  let E : OrderedDivisor Y := ⟨s, fun i => ((F i).comap V.ι).comap g⟩
  have hE : ∀ K : X.IdealSheafData, ((tV K).pullback g).E =
      ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) ((K.comap V.ι).comap g) E.E⟩ := by
    intro K
    change (⟨_, _⟩ : OrderedDivisor Y) = ⟨_, _⟩
    congr 1
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  have hmem : ∀ K : X.IdealSheafData, IsTriple (tV K).sX (tV K).I (tV K).E →
      IsTriple (g ≫ V.ι ≫ sX) ((I.comap V.ι).comap g)
        ⟨E.s + 1, Fin.cons (α := fun _ => Y.IdealSheafData) ((K.comap V.ι).comap g) E.E⟩ := by
    intro K hA
    have hsnc := pullback_mem_sncTriples (mem_sncTriples_of_mem_triples
      (show tV K ∈ triples from hA)) g
    have h : IsTriple (g ≫ V.ι ≫ sX) ((I.comap V.ι).comap g) ((tV K).pullback g).E :=
      mem_triples_iff.2 ⟨hsnc, hYe⟩
    rwa [hE K] at h
  have : CharZero k := hA₁.1
  have hT₁ := hmem K₁ hA₁
  have hJ : maxOrder ((I.comap V.ι).comap g) = m := (hgl.maxOrder_comap_eq ‹_› _).trans hJV
  have hmI : 1 ≤ (maxOrder I).toNat := by rwa [hmax]
  have hdimX1 : 1 ≤ topologicalKrullDim X := by rw [hXdim]; exact_mod_cast hn
  have hJf : (I.comap V.ι).comap g = I.comap (g ≫ V.ι) :=
    (Scheme.IdealSheafData.comap_comp I g V.ι).symm
  have hW := Kollar.maximalCoefficientIdeal_comap_of_smooth sX (g ≫ V.ι ≫ sX) hXs hT₁.2.1 hXe hYe
    hdimX1 (g ≫ V.ι) (Category.assoc _ _ _) I hmI (by rw [← hJf, hJ, hmax]) 1
  have hH : ∀ K : X.IdealSheafData, K ≤ maximalContactIdeal sX I →
      (K.comap V.ι).comap g ≤ maximalCoefficientIdeal (g ≫ V.ι ≫ sX) ((I.comap V.ι).comap g) 1 := by
    intro K hK
    rw [hJf, hW, ← Scheme.IdealSheafData.comap_comp]
    exact Scheme.IdealSheafData.comap_mono _
      (hK.trans (maximalContactIdeal_le_maximalCoefficientIdeal_one sX I hmI))
  change bdFunctor M d m 0 ⟨⟨Y, (I.comap V.ι).comap g, ((tV K₁).pullback g).E⟩, k,
      g ≫ V.ι ≫ sX⟩ = bdFunctor M d m 0 ⟨⟨Y, (I.comap V.ι).comap g, ((tV K₂).pullback g).E⟩, k,
      g ≫ V.ι ≫ sX⟩
  rw [hE K₁, hE K₂, ← hd]
  exact bdFunctor_eq_of_isAffine M hN hM hm hn hnN (g ≫ V.ι ≫ sX) ((I.comap V.ι).comap g) E _ _
    hdimY hJ hT₁ (hmem K₂ hA₂) (hH K₁ hK₁) (hH K₂ hK₂)

/-- On an affine scheme `Y` with a smooth surjection `g : Y → V` which is locally an open
immersion, the pulled-back `𝓑𝓓` pieces `𝓑𝓓_{dim X, m, 1}(Y, g^*J'|_V, g⁻¹(H'_a ∩ V, E_-))`,
`a = 1, 2`, agree: `H'_a` is an MC-hypersurface for `J'`
(`IsOrderMTripleSeq.isMCHypersurface_ker_restrictHom`), and `bdFunctor_pullback_eq_aux`
applies. -/
private theorem bdFunctor_pullback_eq_of_isAffine {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H₁ H₂ : t.X.IdealSheafData}
    (hH₁ : IsMCHypersurface t.sX t.I H₁) (hH₂ : IsMCHypersurface t.sX t.I H₂) :
    let P := divisorSeparationSequence M m t
    let t' := t.endOf P
    let V : t'.X.Opens :=
      (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
    let tV : t'.X.IdealSheafData → FieldBlowupTriple.{u} := fun H' =>
      ⟨⟨V, t'.I.comap V.ι,
        ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData)
          (H'.comap V.ι) fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩⟩, t'.k, V.ι ≫ t'.sX⟩
    ∀ K₁ K₂ : t'.X.IdealSheafData, (P.restrictHom H₁).ker = K₁ → (P.restrictHom H₂).ker = K₂ →
    (V : Set t'.X).Nonempty →
      IsTriple (tV K₁).sX (tV K₁).I (tV K₁).E → IsTriple (tV K₂).sX (tV K₂).I (tV K₂).E →
      maxOrder (t'.I.comap V.ι) = m →
      ∀ {Y : Scheme.{u}} (g : Y ⟶ V), IsAffine Y → Smooth g → Surjective g →
        IsLocallyOpenImmersion g → TopologicalSpace.Equidimensional Y →
        topologicalKrullDim Y = ((n : ℕ∞) : WithBot ℕ∞) →
        @Eq (ClosedBlowupSequence Y) (bdFunctor M (dimNat t.X) m 0 ((tV K₁).pullback g))
          (bdFunctor M (dimNat t.X) m 0 ((tV K₂).pullback g)) := by
  intro P t' V tV K₁ K₂ hK₁ hK₂ _ hA₁ hA₂ hJ Y g hYa hgs hgsurj hgl hYe hdimY
  have hP := divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le
  have htr : IsTriple t'.sX t'.I t'.E :=
    ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m P _ _ _ hP
  obtain ⟨hdimX', hmaxle, -⟩ := end_of_isOrderMTripleSeq m _ P t.sX t.I t.E hP hmax.le hdim
  have hmax' : maxOrder t'.I = m :=
    le_antisymm hmaxle (hJ ▸ maxOrder_comap_le V.ι t'.I)
  have hdim1 : 1 ≤ topologicalKrullDim t.X := by rw [hdim]; exact_mod_cast hn
  have hMC : ∀ {H : t.X.IdealSheafData}, IsMCHypersurface t.sX t.I H →
      (P.restrictHom H).ker ≤ maximalContactIdeal t'.sX t'.I := fun hH =>
    (ClosedBlowupSequence.IsOrderMTripleSeq.isMCHypersurface_ker_restrictHom hdim1 hm hmax hH hP
      hmax').2
  have hK₁' := hK₁ ▸ hMC hH₁
  have hK₂' := hK₂ ▸ hMC hH₂
  have : LocallyOfFiniteType t'.sX := htr.2.2.1
  have : QuasiCompact t'.sX := htr.2.2.2.1
  have : IsLocallyNoetherian t'.X := LocallyOfFiniteType.isLocallyNoetherian t'.sX
  have : CompactSpace t'.X := QuasiCompact.compactSpace_of_compactSpace t'.sX
  have : IsNoetherian t'.X := ⟨⟩
  have : QuasiCompact (V.ι ≫ t'.sX) := inferInstance
  have := hYa
  have := hgs
  have := hgsurj
  have : QuasiCompact (g ≫ V.ι ≫ t'.sX) := inferInstance
  exact bdFunctor_pullback_eq_aux M hN hM hm hn hnN t'.sX htr.2.1 htr.2.2.2.2.1 hdimX' t'.I hmax'
    V hJ _ (fun i => t'.E.E ⟨t.E.s + i, by omega⟩) K₁ K₂ hK₁' hK₂' (dimNat t.X) g hgl hYe hdimY
    (dimNat_eq_of_topologicalKrullDim_eq (hdimY.trans hdim.symm)) hA₁ hA₂

/-- The two sequences `𝓑𝓓_{dim X, m, 1}(V, J'|_V, (H'_a ∩ V, E_-))`, `a = 1, 2`, agree: both
commute with the smooth surjection `g : Y = ⊔ U_i → V` of a finite affine open cover
(`commutesWithSmoothOn_bdFunctor`), their pull-backs agree on the affine `Y`
(`bdFunctor_pullback_eq_of_isAffine`), and a sequence is determined by its pull-back along a flat
surjection (`Kollar.eq_of_pullback_eq_of_flat_of_surjective`). -/
private theorem bdFunctor_restrict_eq {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H₁ H₂ : t.X.IdealSheafData}
    (hH₁ : IsMCHypersurface t.sX t.I H₁) (hH₂ : IsMCHypersurface t.sX t.I H₂) :
    let P := divisorSeparationSequence M m t
    let t' := t.endOf P
    let V : t'.X.Opens :=
      (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
    let tV : t'.X.IdealSheafData → FieldBlowupTriple.{u} := fun H' =>
      ⟨⟨V, t'.I.comap V.ι,
        ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData)
          (H'.comap V.ι) fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩⟩, t'.k, V.ι ≫ t'.sX⟩
    (V : Set t'.X).Nonempty →
      IsTriple (tV (P.restrictHom H₁).ker).sX (tV (P.restrictHom H₁).ker).I
        (tV (P.restrictHom H₁).ker).E →
      IsTriple (tV (P.restrictHom H₂).ker).sX (tV (P.restrictHom H₂).ker).I
        (tV (P.restrictHom H₂).ker).E →
      bdFunctor M (dimNat t.X) m 0 (tV (P.restrictHom H₁).ker) =
        bdFunctor M (dimNat t.X) m 0 (tV (P.restrictHom H₂).ker) := by
  intro P t' V tV hV hA₁ hA₂
  have hcore := bdFunctor_pullback_eq_of_isAffine M hN hM t ht hdim hn hnN hm hmax hH₁ hH₂ _ _
    rfl rfl hV hA₁ hA₂
  generalize (P.restrictHom H₁).ker = K₁ at *
  generalize (P.restrictHom H₂).ker = K₂ at *
  by_cases hJ : maxOrder (t'.I.comap V.ι) = m
  swap
  · rw [bdFunctor, dif_neg (fun h => hJ h.1), bdFunctor, dif_neg (fun h => hJ h.1)]
  have hP := divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le
  have htr : IsTriple t'.sX t'.I t'.E :=
    ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m P _ _ _ hP
  obtain ⟨hdimX', -, -⟩ := end_of_isOrderMTripleSeq m _ P t.sX t.I t.E hP hmax.le hdim
  haveI : LocallyOfFiniteType t'.sX := htr.2.2.1
  haveI : QuasiCompact t'.sX := htr.2.2.2.1
  haveI : IsLocallyNoetherian t'.X := LocallyOfFiniteType.isLocallyNoetherian t'.sX
  haveI : CompactSpace t'.X := QuasiCompact.compactSpace_of_compactSpace t'.sX
  haveI : IsNoetherian t'.X := ⟨⟩
  haveI : QuasiCompact (V.ι ≫ t'.sX) := inferInstance
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (V.ι ≫ t'.sX)
  have hdimV : topologicalKrullDim V = ((n : ℕ∞) : WithBot ℕ∞) :=
    (topologicalKrullDim_opens_of_equidimensional t'.sX htr.2.2.2.2.1 V hV).trans hdimX'
  obtain ⟨Y, g, hYa, hgs, hgsurj, hgl⟩ := exists_affine_cover V
  haveI := hgs
  haveI := hgsurj
  haveI : LocallyOfFiniteType (g ≫ V.ι ≫ t'.sX) := inferInstance
  haveI : QuasiCompact (g ≫ V.ι ≫ t'.sX) := inferInstance
  obtain ⟨hYe, hdimY⟩ := hgl.equidimensional (V.ι ≫ t'.sX) hgsurj
    (equidimensional_opens t'.sX htr.2.2.2.2.1 V)
  have hdimY' : topologicalKrullDim Y = ((n : ℕ∞) : WithBot ℕ∞) := hdimY.trans hdimV
  have hmemV : ∀ K, IsTriple (tV K).sX (tV K).I (tV K).E →
      tV K ∈ {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ 0 < t.E.s} :=
    fun K hK => ⟨⟨hK, ⟨n, ⟨hn, hnN⟩, hdimV⟩, hJ.le⟩, Nat.succ_pos _⟩
  have hmemY : ∀ K, IsTriple (tV K).sX (tV K).I (tV K).E →
      (tV K).pullback g ∈ {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ 0 < t.E.s} := by
    intro K hK
    haveI : QuasiCompact (g ≫ (tV K).sX) := ‹QuasiCompact (g ≫ V.ι ≫ t'.sX)›
    have hsnc := pullback_mem_sncTriples (mem_sncTriples_of_mem_triples
      (show tV K ∈ triples from hK)) g
    exact ⟨⟨mem_triples_iff.2 ⟨hsnc, hYe⟩, ⟨n, ⟨hn, hnN⟩, hdimY'⟩,
      (hgl.maxOrder_comap_le _).trans hJ.le⟩, Nat.succ_pos _⟩
  have e : ∀ K, IsTriple (tV K).sX (tV K).I (tV K).E →
      bdFunctor M (dimNat t.X) m 0 ((tV K).pullback g) =
        (bdFunctor M (dimNat t.X) m 0 (tV K)).pullback g := by
    intro K hK
    have := (commutesWithSmoothOn_bdFunctor (j := 0) M hN hM hm).1 (tV K) (hmemV K hK) Y g hgs
      hgsurj ‹LocallyOfFiniteType (g ≫ V.ι ≫ t'.sX)› ‹QuasiCompact (g ≫ V.ι ≫ t'.sX)›
      (hmemY K hK)
    have h1 : dimNat ((tV K).pullback g).X = dimNat t.X :=
      dimNat_eq_of_topologicalKrullDim_eq (hdimY'.trans hdim.symm)
    have h2 : dimNat (tV K).X = dimNat t.X :=
      dimNat_eq_of_topologicalKrullDim_eq (hdimV.trans hdim.symm)
    dsimp only at this
    rwa [h1, h2] at this
  apply MMP.Resolution.Kollar.eq_of_pullback_eq_of_flat_of_surjective g
  rw [← e K₁ hA₁, ← e K₂ hA₂]
  exact hcore hJ g hYa hgs hgsurj hgl hYe hdimY'

open Classical in
/-- The `𝓑𝓓` piece of `𝓑𝓞^H_m`, as a function of the birational transform `H'` of `H`, takes
the same value at the transforms of two MC-hypersurfaces. -/
private theorem bdPiece_eq {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H₁ H₂ : t.X.IdealSheafData}
    (hH₁ : IsMCHypersurface t.sX t.I H₁) (hH₂ : IsMCHypersurface t.sX t.I H₂) :
    let P := divisorSeparationSequence M m t
    let t' := t.endOf P
    let V : t'.X.Opens :=
      (⨆ i : Fin t'.E.s, if (i : ℕ) < t.E.s then (t'.E.E i).support else ⊥).compl
    let tV : t'.X.IdealSheafData → FieldBlowupTriple.{u} := fun H' =>
      ⟨⟨V, t'.I.comap V.ι,
        ⟨t'.E.s - t.E.s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData)
          (H'.comap V.ι) fun i => (t'.E.E ⟨t.E.s + i, by omega⟩).comap V.ι⟩⟩, t'.k, V.ι ≫ t'.sX⟩
    let BV : t'.X.IdealSheafData → ClosedBlowupSequence V := fun H' =>
      if (V : Set t'.X).Nonempty ∧ IsTriple (tV H').sX (tV H').I (tV H').E then
        bdFunctor M (dimNat t.X) m 0 (tV H')
      else .nil _
    BV (P.restrictHom H₁).ker = BV (P.restrictHom H₂).ker := by
  intro P t' V tV BV
  have hA₁ := isTriple_restrict_divisorSeparationSequence M hN hM t ht hdim hn hnN hm hmax hH₁
  have hA₂ := isTriple_restrict_divisorSeparationSequence M hN hM t ht hdim hn hnN hm hmax hH₂
  have hB := bdFunctor_restrict_eq M hN hM t ht hdim hn hnN hm hmax hH₁ hH₂
  by_cases hV : (V : Set t'.X).Nonempty
  · exact (if_pos ⟨hV, hA₁ hV⟩).trans ((hB hV (hA₁ hV) (hA₂ hV)).trans (if_pos ⟨hV, hA₂ hV⟩).symm)
  · simp only [BV, hV, false_and, if_false]

/-- **Kollár, Thm. 3.104 Step 2.3 (independence of `H`).** Let `𝓜` be a marked order-reduction
family on dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`), `(X, J, E)` a triple of
dimension `n` with `1 ≤ n ≤ N`, `m ≥ 1` with `maxord J = m`, and `H₁`, `H₂` two
MC-hypersurfaces for `J` (`IsMCHypersurface`). Then
`boMaximalContact M m (X, J, E) H₁ = boMaximalContact M m (X, J, E) H₂`. -/
@[mmp "lem_kr3e_bo_maximal_contact_independent"]
public theorem boMaximalContact_eq_of_isMCHypersurface {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H₁ H₂ : t.X.IdealSheafData}
    (hH₁ : IsMCHypersurface t.sX t.I H₁) (hH₂ : IsMCHypersurface t.sX t.I H₂) :
    boMaximalContact M m t H₁ = boMaximalContact M m t H₂ := by
  have h := bdPiece_eq M hN hM t ht hdim hn hnN hm hmax hH₁ hH₂
  unfold boMaximalContact
  dsimp only at h ⊢
  rw [h]

/-! ### `𝓑𝓞^H_m` commutes with smooth morphisms -/

section Rel

variable {X Y : Scheme.{u}}

private theorem ofFn_comap_E (E : OrderedDivisor X) (f : Y ⟶ X) :
    List.ofFn (E.comap f).E = (List.ofFn E.E).map (·.comap f) := by
  rw [List.map_ofFn]
  rfl

open Classical in
/-- `E` and `F` agree in their first `s` entries and, after these, up to empty entries. -/
private def AgreeUpToEmpty (s : ℕ) (E F : OrderedDivisor X) : Prop :=
  ∃ A B B' : List X.IdealSheafData, List.ofFn E.E = A ++ B ∧ List.ofFn F.E = A ++ B' ∧
    A.length = s ∧ B.filter (fun D => decide (D ≠ ⊤)) = B'.filter (fun D => decide (D ≠ ⊤))

private theorem agreeUpToEmpty_refl (s : ℕ) (E : OrderedDivisor X) (hs : s ≤ E.s) :
    AgreeUpToEmpty s E E :=
  ⟨(List.ofFn E.E).take s, (List.ofFn E.E).drop s, (List.ofFn E.E).drop s,
    (List.take_append_drop _ _).symm, (List.take_append_drop _ _).symm, by simp [hs], rfl⟩

open Classical in
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

/-- Entries before `s` agree. -/
private theorem AgreeUpToEmpty.entry_eq {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) (j : ℕ) (hj : j < s) (hE : j < E.s) (hF : j < F.s) :
    E.E ⟨j, hE⟩ = F.E ⟨j, hF⟩ := by
  obtain ⟨A, B, B', hEA, hFA, hA, -⟩ := h
  have h1 : (List.ofFn E.E)[j]'(by simpa using hE) = (List.ofFn F.E)[j]'(by simpa using hF) := by
    simp only [hEA, hFA]
    rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]
  simpa using h1

private theorem AgreeUpToEmpty.le_left {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) : s ≤ E.s := by
  obtain ⟨A, B, B', hEA, -, hA, -⟩ := h
  have := congrArg List.length hEA
  simp at this; omega

private theorem AgreeUpToEmpty.le_right {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) : s ≤ F.s := by
  obtain ⟨A, B, B', -, hFA, hA, -⟩ := h
  have := congrArg List.length hFA
  simp at this; omega

open Classical in
/-- The nonempty entries agree. -/
private theorem AgreeUpToEmpty.filter_eq {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) :
    (List.ofFn E.E).filter (fun D => decide (D ≠ ⊤)) =
      (List.ofFn F.E).filter (fun D => decide (D ≠ ⊤)) := by
  obtain ⟨A, B, B', hEA, hFA, -, hB⟩ := h
  rw [hEA, hFA, List.filter_append, List.filter_append, hB]

private theorem AgreeUpToEmpty.comap {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) (f : Y ⟶ X) : AgreeUpToEmpty s (E.comap f) (F.comap f) := by
  classical
  obtain ⟨A, B, B', hEA, hFA, hA, hB⟩ := h
  refine ⟨A.map (·.comap f), B.map (·.comap f), B'.map (·.comap f), ?_, ?_, by simp [hA], ?_⟩
  · rw [ofFn_comap_E, hEA, List.map_append]
  · rw [ofFn_comap_E, hFA, List.map_append]
  · refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) hB
    simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
    rw [hD, Scheme.IdealSheafData.comap_top]

private theorem AgreeUpToEmpty.snoc_top {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) :
    AgreeUpToEmpty s E ⟨F.s + 1, Fin.snoc (α := fun _ => X.IdealSheafData) F.E ⊤⟩ := by
  classical
  obtain ⟨A, B, B', hEA, hFA, hA, hB⟩ := h
  refine ⟨A, B, B' ++ [⊤], hEA, ?_, hA, ?_⟩
  · rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append]
    rw [show (List.ofFn fun i : Fin F.s => F.E i) = List.ofFn F.E from rfl, hFA,
      List.append_assoc]
  · rw [List.filter_append, ← hB]
    simp

open Classical in
/-- The support only depends on the nonempty entries. -/
private theorem support_eq_of_filter_eq {E F : OrderedDivisor X}
    (h : (List.ofFn E.E).filter (fun D => decide (D ≠ ⊤)) =
      (List.ofFn F.E).filter (fun D => decide (D ≠ ⊤))) : E.support = F.support := by
  have key : ∀ G : OrderedDivisor X, G.support =
      ⋃ D ∈ (List.ofFn G.E).filter (fun D => decide (D ≠ ⊤)), (D.support : Set X) := by
    intro G
    ext x
    simp only [OrderedDivisor.support, Set.mem_iUnion, List.mem_filter, List.mem_ofFn,
      decide_eq_true_eq, exists_prop]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨G.E i, ⟨⟨i, rfl⟩, fun ht => ?_⟩, hi⟩
      rwa [ht, Scheme.IdealSheafData.support_top] at hi
    · rintro ⟨D, ⟨⟨i, rfl⟩, -⟩, hi⟩
      exact ⟨i, hi⟩
  rw [key E, key F, h]

private theorem birationalEntry_top (Z : X.IdealSheafData) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
      (blowUpToBase Z ⁻¹' (((⊤ : X.IdealSheafData).support : Set X) \
        componentsOfCodimAtLeastTwo (Z.support : Set X)))) = ⊤ := by
  have : (Closeds.closure (blowUpToBase Z ⁻¹' (((⊤ : X.IdealSheafData).support : Set X) \
      componentsOfCodimAtLeastTwo (Z.support : Set X)))) = ⊥ := by
    ext x
    simp [Scheme.IdealSheafData.support_top]
  rw [this, Scheme.IdealSheafData.vanishingIdeal_bot]

private theorem ofFn_totalTransform (E : OrderedDivisor X) (Z : X.IdealSheafData) :
    List.ofFn (E.totalTransform Z).E = (List.ofFn E.E).map (fun D =>
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        (blowUpToBase Z ⁻¹' ((D.support : Set X) \
          componentsOfCodimAtLeastTwo (Z.support : Set X))))) ++
      [Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        (⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf E.support), blowUpToBase Z ⁻¹' W))] := by
  have e1 := List.ofFn_succ' (n := E.s) (E.totalTransform Z).E
  refine e1.trans ?_
  simp only [Kollar.totalTransform_E_castSucc, List.concat_eq_append, List.map_ofFn]
  rw [Kollar.totalTransform_E_last]
  rfl

private theorem AgreeUpToEmpty.totalTransform {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) (Z : X.IdealSheafData) :
    AgreeUpToEmpty s (E.totalTransform Z) (F.totalTransform Z) := by
  classical
  have hsupp := support_eq_of_filter_eq h.filter_eq
  obtain ⟨A, B, B', hEA, hFA, hA, hB⟩ := h
  rw [AgreeUpToEmpty, ofFn_totalTransform, ofFn_totalTransform, hEA, hFA, hsupp]
  refine ⟨A.map _, B.map _ ++ _, B'.map _ ++ _, by rw [List.map_append, List.append_assoc],
    by rw [List.map_append, List.append_assoc], by simp [hA], ?_⟩
  rw [List.filter_append, List.filter_append]
  congr 1
  refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) hB
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
  rw [hD]
  exact birationalEntry_top Z

end Rel

section Transport

open ClosedBlowupSequence

/-- **The ordered total transform along the reduced pull-back**, as a pair: for smooth `h` and
`𝐁` of order `m` starting with `(X, I, E)`, if `E_Y` agrees with `h⁻¹E` up to empty entries
after the first `s`, then so do the ordered total transform of `E_Y` along `(h^*𝐁)^red` and the
inverse image of that of `E` along the last morphism. -/
private theorem agreeUpToEmpty_pullbackReducedWithHom (s : ℕ) {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) : ∀ {Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h] {k : Type u}
      [Field k] (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (m : ℕ)
      (EY : OrderedDivisor Y), B.IsOrderMTripleSeq sX I E m → AgreeUpToEmpty s EY (E.comap h) →
      AgreeUpToEmpty s ((B.pullbackReducedWithHom h).1.orderedTotalTransform EY)
        ((B.orderedTotalTransform E).comap (B.pullbackReducedWithHom h).2) := by
  induction B with
  | nil X =>
    intro Y h _ k _ sX I E m EY _ hrel
    exact hrel
  | cons Z B ih =>
    intro Y h _ k _ sX I E m EY hX hrel
    obtain ⟨⟨-, -, hlft, -, -, -, hEo⟩, -, -, -, -, hB⟩ := hX
    have := hlft
    have := LocallyOfFiniteType.isLocallyNoetherian sX
    have := LocallyOfFiniteType.isLocallyNoetherian h
    by_cases hZh : Z.comap h = ⊤
    · rw [pullbackReducedWithHom_cons_of_eq_top Z B h hZh]
      have : Smooth (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZh)) :=
        MorphismProperty.of_isPullback (P := @Smooth) (Kollar.isPullback_blowUpLift_of_flat h Z hZh)
          ‹_›
      refine ih _ _ _ _ m EY hB ?_
      rw [Kollar.totalTransform_comap_blowUpLift (IsReducedFlatBaseChange.of_smooth h) E
        (fun i => (hEo.1 i).1) Z hZh]
      exact hrel.snoc_top
    · rw [pullbackReducedWithHom_cons_of_ne_top Z B h hZh]
      have : Smooth (canonicalLift h Z) :=
        MorphismProperty.of_isPullback (P := @Smooth)
          (Kollar.isPullback_canonicalLift_of_flat h Z) ‹_›
      refine ih _ _ _ _ m (EY.totalTransform (Z.comap h)) hB ?_
      rw [Kollar.totalTransform_comap_canonicalLift (IsReducedFlatBaseChange.of_smooth h) E Z
        (componentsOfCodimAtLeastTwo_comap h Z)
        (iUnion_componentsOf_notMem_comap h (Flat.generalizingMap h) E Z)]
      exact hrel.totalTransform _

/-- **The ordered total transform along the reduced pull-back.** -/
private theorem agreeUpToEmpty_pullbackReduced (s : ℕ) {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) (h : Y ⟶ X) [Smooth h] {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (m : ℕ)
    (hB : B.IsOrderMTripleSeq sX I E m) (hs : s ≤ E.s) :
    AgreeUpToEmpty s ((B.pullbackReduced h).orderedTotalTransform (E.comap h))
      ((B.orderedTotalTransform E).comap (B.pullbackReducedHom h)) := by
  have key := agreeUpToEmpty_pullbackReducedWithHom s B h sX I E m (E.comap h) hB
    (agreeUpToEmpty_refl s _ hs)
  rwa [B.pullbackReducedWithHom_eq h] at key

/-- **The ordered total transform along a surjective pull-back**, as a pair: for smooth surjective
`h` and `𝐁` of order `m` starting with `(X, I, E)` without empty blow-ups, no pulled-back centre is
empty, the last morphism of `(h^*𝐁)^red` is surjective, and if `E_Y = h⁻¹E` then the ordered total
transform of `E_Y` along `(h^*𝐁)^red` is the inverse image of that of `E`. -/
private theorem orderedTotalTransform_pullbackReducedWithHom_of_surjective {X : Scheme.{u}}
    (B : ClosedBlowupSequence X) : ∀ {Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h] [Surjective h]
      {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X)
      (m : ℕ) (EY : OrderedDivisor Y), B.IsOrderMTripleSeq sX I E m → B.HasNoEmptyBlowups →
      EY = E.comap h →
      Surjective (B.pullbackReducedWithHom h).2 ∧
        (B.pullbackReducedWithHom h).1.orderedTotalTransform EY =
          (B.orderedTotalTransform E).comap (B.pullbackReducedWithHom h).2 := by
  induction B with
  | nil X =>
    intro Y h _ _ k _ sX I E m EY _ _ hrel
    exact ⟨‹_›, hrel⟩
  | cons Z B ih =>
    intro Y h _ _ k _ sX I E m EY hX hne hrel
    obtain ⟨⟨-, -, hlft, -, -, -, hEo⟩, -, -, -, -, hB⟩ := hX
    have := hlft
    have := LocallyOfFiniteType.isLocallyNoetherian sX
    have := LocallyOfFiniteType.isLocallyNoetherian h
    have hZh : Z.comap h ≠ ⊤ := by
      intro hZ
      refine hne.1 ?_
      rw [← Scheme.IdealSheafData.support_eq_bot_iff] at hZ ⊢
      refine eq_bot_iff.2 fun x hx => ?_
      obtain ⟨y, rfl⟩ := h.surjective x
      have : y ∈ ((Z.comap h).support : Set Y) := by
        rwa [Scheme.IdealSheafData.support_comap]
      rwa [hZ] at this
    rw [pullbackReducedWithHom_cons_of_ne_top Z B h hZh]
    have : Smooth (canonicalLift h Z) :=
      MorphismProperty.of_isPullback (P := @Smooth)
        (Kollar.isPullback_canonicalLift_of_flat h Z) ‹_›
    have : Surjective (canonicalLift h Z) := Kollar.surjective_canonicalLift h Z
    refine ih _ _ _ _ m (EY.totalTransform (Z.comap h)) hB hne.2 ?_
    rw [Kollar.totalTransform_comap_canonicalLift (IsReducedFlatBaseChange.of_smooth h) E Z
      (componentsOfCodimAtLeastTwo_comap h Z)
      (iUnion_componentsOf_notMem_comap h (Flat.generalizingMap h) E Z), hrel]

/-- **The ordered total transform along a surjective pull-back.** For smooth surjective `h` and
`𝐁` of order `m` without empty blow-ups, the ordered total transform of `h⁻¹E` along
`(h^*𝐁)^red` is the inverse image of that of `E` along the last morphism, which is surjective. -/
private theorem orderedTotalTransform_pullbackReduced_of_surjective {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) (h : Y ⟶ X) [Smooth h] [Surjective h] {k : Type u} [Field k]
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) (E : OrderedDivisor X) (m : ℕ)
    (hB : B.IsOrderMTripleSeq sX I E m) (hne : B.HasNoEmptyBlowups) :
    Surjective (B.pullbackReducedHom h) ∧
      (B.pullbackReduced h).orderedTotalTransform (E.comap h) =
        (B.orderedTotalTransform E).comap (B.pullbackReducedHom h) := by
  have key := orderedTotalTransform_pullbackReducedWithHom_of_surjective B h sX I E m
    (E.comap h) hB hne rfl
  rwa [B.pullbackReducedWithHom_eq h] at key

end Transport

section EmptyEntries

variable {X : Scheme.{u}}

open Classical in
/-- The list of the nonempty entries of an ordered divisor, in their order. -/
private noncomputable def flat (E : OrderedDivisor X) : List X.IdealSheafData :=
  (List.ofFn E.E).filter fun D => D ≠ ⊤

open Classical in
private theorem ofFn_deleteEmpty (E : OrderedDivisor X) :
    List.ofFn E.deleteEmpty.E = flat E := by
  show List.ofFn (E.E ∘ ((List.finRange E.s).filter fun i => E.E i ≠ ⊤).get) = flat E
  rw [← List.map_ofFn, List.ofFn_get, flat, List.ofFn_eq_map (f := E.E), List.filter_map]
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

private theorem deleteEmpty_comap_eq {Y : Scheme.{u}} {E F : OrderedDivisor X}
    (h : E.deleteEmpty = F.deleteEmpty) (f : Y ⟶ X) :
    (E.comap f).deleteEmpty = (F.comap f).deleteEmpty := by
  classical
  rw [deleteEmpty_eq_iff] at h ⊢
  rw [flat, flat, ofFn_comap_E, ofFn_comap_E]
  refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) h
  simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
  rw [hD, Scheme.IdealSheafData.comap_top]

open Classical in
private noncomputable def flatIdx (E : OrderedDivisor X) : List (Fin E.s) :=
  (List.finRange E.s).filter fun i => E.E i ≠ ⊤

private theorem injective_flatIdx_get (E : OrderedDivisor X) :
    Function.Injective (flatIdx E).get :=
  List.nodup_iff_injective_get.1 ((List.nodup_finRange _).filter _)

private theorem exists_flatIdx_get (E : OrderedDivisor X) (i : Fin E.s) (hi : E.E i ≠ ⊤) :
    ∃ j, (flatIdx E).get j = i :=
  List.mem_iff_get.1 (by simp [flatIdx, hi])

private theorem map_filter_finRange_ne {α : Type*} (n : ℕ) (f : Fin n → α) (j : ℕ) :
    ((List.finRange n).filter (fun i => i.val ≠ j)).map f = (List.ofFn f).eraseIdx j := by
  induction n generalizing j with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.ofFn_succ]
    rcases j with _ | j
    · simp [List.filter_map, Function.comp_def, List.map_map, List.ofFn_eq_map]
    · simp [List.filter_map, Function.comp_def, List.map_map, ← ih]

private theorem ofFn_deleteIndex (E : OrderedDivisor X) (j : ℕ) :
    List.ofFn (E.deleteIndex j).E = (List.ofFn E.E).eraseIdx j := by
  show List.ofFn (E.E ∘ ((List.finRange E.s).filter fun i : Fin E.s => i.val ≠ j).get) = _
  rw [← List.map_ofFn, List.ofFn_get, map_filter_finRange_ne]

/-- Deleting an entry before `s` keeps the agreement up to empty entries. -/
private theorem AgreeUpToEmpty.flat_deleteIndex {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) (j : ℕ) (hj : j < s) :
    flat (E.deleteIndex j) = flat (F.deleteIndex j) := by
  classical
  obtain ⟨A, B, B', hEA, hFA, hA, hB⟩ := h
  rw [flat, flat, ofFn_deleteIndex, ofFn_deleteIndex, hEA, hFA,
    List.eraseIdx_append_of_lt_length (by omega), List.eraseIdx_append_of_lt_length (by omega),
    List.filter_append, List.filter_append]
  congr 1

private theorem AgreeUpToEmpty.deleteEmpty_eq {s : ℕ} {E F : OrderedDivisor X}
    (h : AgreeUpToEmpty s E F) : E.deleteEmpty = F.deleteEmpty := by
  classical
  rw [deleteEmpty_eq_iff, flat, flat]
  exact h.filter_eq

end EmptyEntries

section Reindex

variable {X : Scheme.{u}} {Λ Λ' : Type*} (E : Λ → X.IdealSheafData) (g : Λ' → Λ)

private theorem forall_iff_forall_comp (hg : ∀ i, E i ≠ ⊤ → ∃ j, g j = i)
    (R : X.IdealSheafData → Prop) (hR : R ⊤) :
    (∀ i, R (E i)) ↔ ∀ j, R (E (g j)) := by
  refine ⟨fun h j => h _, fun h i => ?_⟩
  by_cases hi : E i = ⊤
  · rwa [hi]
  · obtain ⟨j, rfl⟩ := hg i hi
    exact h j

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
      have := i.2; rw [h, Scheme.IdealSheafData.support_top] at this; exact this
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
  · have key := exists_coord_iff E g hginj hg x z
    constructor
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.1 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩
    · rintro ⟨c, h1, h2, h3⟩
      obtain ⟨c', h2', h3'⟩ := key.2 ⟨c, h2, h3⟩
      exact ⟨c', h1, h2', h3'⟩

end Reindex

private theorem isOrderedSNC_deleteEmpty_iff {X : Scheme.{u}} (E : OrderedDivisor X)
    {k : Type u} [Field k] (sX : X ⟶ Spec (.of k)) :
    E.IsOrderedSNC sX ↔ E.deleteEmpty.IsOrderedSNC sX :=
  and_congr
    (forall_iff_forall_comp E.E _ (exists_flatIdx_get E)
      (fun D => IsReduced D.subscheme ∧ Stacks.Divisors.IsEffectiveCartierDivisor D)
      ⟨isReduced_of_isAffine_isReduced _, Stacks.Divisors.isEffectiveCartierDivisor_top⟩)
    (isSNCFamily_iff_comp E.E _ sX (injective_flatIdx_get E) (exists_flatIdx_get E))

/-- `(X, I, E)` is a triple iff `(X, I, E')` is, for `E^♭ = E'^♭`. -/
private theorem isTriple_iff_of_deleteEmpty_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (I : X.IdealSheafData) {E E' : OrderedDivisor X}
    (h : E.deleteEmpty = E'.deleteEmpty) : IsTriple sX I E ↔ IsTriple sX I E' := by
  unfold IsTriple
  rw [isOrderedSNC_deleteEmpty_iff E, h, ← isOrderedSNC_deleteEmpty_iff E']

section BD

/-- The divisor `S = π⁻¹E^j` on which `𝓑𝓓` applies the marked family. -/
private noncomputable abbrev bdDivisor (u : FieldBlowupTriple.{u}) (m : ℕ)
    (D : u.X.IdealSheafData) :
    (blowUp (divisorComponentCentre
      (⟨maximalCoefficientIdeal u.sX u.I m.factorial, m.factorial⟩ : MarkedIdeal u.X)
        D)).IdealSheafData :=
  D.comap (blowUpToBase (divisorComponentCentre
    (⟨maximalCoefficientIdeal u.sX u.I m.factorial, m.factorial⟩ : MarkedIdeal u.X) D))

/-- `𝓑𝓓_{n,m,j}(X, I, E)` and `𝓑𝓓_{n,m,j}(X, I, E')` agree when `E` and `E'` agree up to empty
entries after the first `s > j`, provided `𝓜_{n-1,m!}` ignores empty entries (or `E = E'`) and the
divisor `S` has dimension `n - 1` when nonempty. -/
private theorem bdFunctor_congr_of_agree (M : MarkedFamily.{u}) (n m : ℕ)
    (u : FieldBlowupTriple.{u}) (E E' : OrderedDivisor u.X) (s j : ℕ) (hjs : j < s)
    (hag : AgreeUpToEmpty s E E')
    (hdimS : ∀ hj : j < E.s, Nonempty (bdDivisor u m (E.E ⟨j, hj⟩)).subscheme →
      HasDimensionIn (bdDivisor u m (E.E ⟨j, hj⟩)).subscheme {n - 1})
    (hMe : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n - 1} m.factorial)
      (fun t _ => M (n - 1) m.factorial t) ∨ E = E') :
    bdFunctor M n m j { u with E := E } = bdFunctor M n m j { u with E := E' } := by
  obtain hMe | rfl := hMe
  swap
  · rfl
  have hjE : j < E.s := lt_of_lt_of_le hjs hag.le_left
  have hjE' : j < E'.s := lt_of_lt_of_le hjs hag.le_right
  have hD := hag.entry_eq j hjs hjE hjE'
  have hflat := hag.flat_deleteIndex j hjs
  unfold bdFunctor
  by_cases h : maxOrder u.I = m
  · rw [dif_pos ⟨h, hjE⟩, dif_pos ⟨h, hjE'⟩]
    dsimp only
    have hdim := hdimS hjE
    rw [hD] at hdim ⊢
    generalize E'.E ⟨j, hjE'⟩ = D at hdim ⊢
    congr 3
    set Z := divisorComponentCentre
      ({ I := maximalCoefficientIdeal u.sX u.I m.factorial, m := m.factorial } : MarkedIdeal u.X) D
    set S := D.comap (blowUpToBase Z)
    have hdel : (((E.comap (blowUpToBase Z)).deleteIndex j).comap S.subschemeι).deleteEmpty =
        (((E'.comap (blowUpToBase Z)).deleteIndex j).comap S.subschemeι).deleteEmpty :=
      deleteEmpty_comap_eq (deleteEmpty_comap_eq (deleteEmpty_eq_iff.2 hflat) _) _
    have hiff := fun (I' : S.subscheme.IdealSheafData) =>
      isTriple_iff_of_deleteEmpty_eq (S.subschemeι ≫ blowUpToBase Z ≫ u.sX) I' hdel
    split_ifs with h1 h2 h2
    · have hne : Nonempty S.subscheme := by
        obtain ⟨x, hx⟩ := h1.1
        rw [← S.range_subschemeι] at hx
        obtain ⟨s, -⟩ := hx
        exact ⟨s⟩
      have hmem := hdim hne
      obtain ⟨_, e1⟩ := hMe _ ⟨h1.2, rfl, hmem⟩
      obtain ⟨_, e2⟩ := hMe _ ⟨h2.2, rfl, hmem⟩
      beta_reduce at e1 e2
      rw [← e1, ← e2]
      unfold MarkedTriple.deleteEmpty
      dsimp only
      rw [hdel]
    · exact (h2 ⟨h1.1, (hiff _).1 h1.2⟩).elim
    · exact (h1 ⟨h2.1, (hiff _).2 h2.2⟩).elim
    · rfl
  · rw [dif_neg (fun h' => h h'.1), dif_neg (fun h' => h h'.1)]

end BD

section Dimension

open MMP.Mori

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y]

private theorem exists_ringKrullDim_stalk_subscheme (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    (s : D.subscheme) : ∃ m : ℕ, ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) = m ∧
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((m - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hz : D.subschemeι s ∈ D.support := by
    rw [← SetLike.mem_coe, ← D.range_subschemeι]; exact ⟨s, rfl⟩
  obtain ⟨m, w, j, hw, hy⟩ := hD _ hz
  haveI := isRegularLocalRing_of_isRegularSystemOfParameters hw
  refine ⟨m, hw.2, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv D s), hy]
  exact ringKrullDim_quotient_span_singleton_of_isRegularSystemOfParameters hw j

private theorem topologicalKrullDim_subscheme {k : Type u} [Field k]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (he : Equidimensional Y) {d : ℕ}
    (hd : topologicalKrullDim Y = ((d : ℕ∞) : WithBot ℕ∞)) (D : Y.IdealSheafData)
    (hD : ∀ y ∈ D.support, ∃ (m : ℕ) (w : Fin m → Y.presheaf.stalk y) (j : Fin m),
      IsRegularSystemOfParameters w ∧ IdealSheafData.stalk D y = Ideal.span {w j})
    [CompactSpace D.subscheme] [Nonempty D.subscheme] :
    topologicalKrullDim D.subscheme = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  have hle : ∀ s, ringKrullDim (D.subscheme.presheaf.stalk s) ≤
      (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s
    obtain ⟨m, hm, hs⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have h1 : ringKrullDim (Y.presheaf.stalk (D.subschemeι s)) ≤ topologicalKrullDim Y := by
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      exact le_iSup (fun y => ringKrullDim (Y.presheaf.stalk y)) _
    rw [hm, hd] at h1
    have h2 : m ≤ d := by exact_mod_cast h1
    rw [hs]
    exact WithBot.coe_le_coe.2 (by exact_mod_cast Nat.sub_le_sub_right h2 1)
  have hcl : ∀ s : D.subscheme, IsClosed ({s} : Set D.subscheme) →
      ringKrullDim (D.subscheme.presheaf.stalk s) = (((d - 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    intro s hs
    obtain ⟨m, hm, hs'⟩ := exists_ringKrullDim_stalk_subscheme D hD s
    have hy : IsClosed ({D.subschemeι s} : Set Y) := by
      simpa using D.subschemeι.isClosedEmbedding.isClosedMap _ hs
    have h1 := topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point sY _ hy
    rw [topologicalKrullDimAt_eq_of_equidimensional k Y sY he
      (d := d) (by rw [hd]; rfl), hm] at h1
    have h2 : m = d := by exact_mod_cast h1.symm
    rw [hs', h2]
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
  obtain ⟨s0, -, hs0⟩ := isClosed_univ.exists_closed_singleton
    (Set.univ_nonempty (α := D.subscheme))
  exact le_antisymm (iSup_le hle) (le_iSup_of_le s0 (hcl s0 hs0).ge)

private theorem hasDimensionIn_comap_of_isIso (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    {n : ℕ} (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (j : ℕ) (hj : j < t.E.s)
    (Z : t.X.IdealSheafData) [IsIso (blowUpToBase Z)]
    (hne : Nonempty ((t.E.E ⟨j, hj⟩).comap (blowUpToBase Z)).subscheme) :
    HasDimensionIn ((t.E.E ⟨j, hj⟩).comap (blowUpToBase Z)).subscheme {n - 1} := by
  have ht' := ht
  obtain ⟨-, -, hlft, hqc, hequi, -, -, -⟩ := ht
  haveI := hlft
  haveI := hqc
  obtain ⟨-, -, hlft0, hqc0, -, -, hE0⟩ :=
    pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht') (blowUpToBase Z)
  replace hE0 : IsSNCFamily (blowUpToBase Z ≫ t.sX)
    (fun i => (t.E.E i).comap (blowUpToBase Z)) := hE0
  haveI : LocallyOfFiniteType (blowUpToBase Z ≫ t.sX) := hlft0
  haveI : QuasiCompact (blowUpToBase Z ≫ t.sX) := hqc0
  haveI : IsLocallyNoetherian (blowUp Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase Z ≫ t.sX)
  haveI : CompactSpace ((t.E.E ⟨j, hj⟩).comap (blowUpToBase Z)).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace
      (((t.E.E ⟨j, hj⟩).comap (blowUpToBase Z)).subschemeι ≫ blowUpToBase Z ≫ t.sX)
  have hdY : topologicalKrullDim (blowUp Z) = ((n : ℕ∞) : WithBot ℕ∞) := by
    rw [← hdim]
    exact IsHomeomorph.topologicalKrullDim_eq _ (blowUpToBase Z).homeomorph.isHomeomorph
  exact ⟨n - 1, rfl, topologicalKrullDim_subscheme (blowUpToBase Z ≫ t.sX)
    (equidimensional_blowUp t.sX Z hequi) hdY _ (hE0.exists_stalk_eq_span_parameter ⟨j, hj⟩)⟩

/-- The divisor `S = π⁻¹E^j` used by `𝓑𝓓` on a triple of dimension `n` has dimension `n - 1`
when nonempty. -/
private theorem hasDimensionIn_bdDivisor (t : FieldBlowupTriple.{u}) (ht : t ∈ triples) {n : ℕ}
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (m j : ℕ) (hj : j < t.E.s)
    (hne : Nonempty (bdDivisor t m (t.E.E ⟨j, hj⟩)).subscheme) :
    HasDimensionIn (bdDivisor t m (t.E.E ⟨j, hj⟩)).subscheme {n - 1} := by
  have hDj := ht.2.2.2.2.2.2.2.1 ⟨j, hj⟩
  haveI := ht.2.2.1
  haveI := isIso_blowUpToBase_divisorComponentCentre t.sX ht.2.1
    (⟨maximalCoefficientIdeal t.sX t.I m.factorial, m.factorial⟩ : MarkedIdeal t.X) _
    hDj.2.2 hDj.2.1
  exact hasDimensionIn_comap_of_isIso t ht hdim j hj _ hne

end Dimension

section ExtendByClosureReduced

open ClosedBlowupSequence

private theorem pullbackReduced_eqToHom_comp_heq {X Y Y' : Scheme.{u}}
    (S : ClosedBlowupSequence X) (e : Y = Y') (f : Y' ⟶ X) :
    S.pullbackReduced (eqToHom e ≫ f) ≍ S.pullbackReduced f := by
  subst e
  simp

private theorem isPullback_eqToHom_canonicalLift {U X : Scheme.{u}} (ι : U ⟶ X) [Flat ι]
    (W : X.IdealSheafData) (Z : U.IdealSheafData) (hc : W.comap ι = Z) :
    IsPullback (eqToHom (congrArg blowUp hc.symm) ≫ canonicalLift ι W) (blowUpToBase Z)
      (blowUpToBase W) ι := by
  subst hc
  simpa using (Kollar.isPullback_canonicalLift_of_flat ι W).flip

private theorem isReducedFlatBaseChange_blowUpLift {X Y : Scheme.{u}} {h : Y ⟶ X}
    (hh : IsReducedFlatBaseChange h) (Z : X.IdealSheafData) (hZ : Z.comap h = ⊤) :
    IsReducedFlatBaseChange (blowUpLift Z h (isCartierOver_of_comap_eq_top h Z hZ)) := by
  have := Kollar.isIso_blowUpToBase_comap_of_eq_top h Z hZ
  rw [Kollar.blowUpLift_eq_inv_comp_canonicalLift h Z hZ]
  exact IsReducedFlatBaseChange.of_isPullback
    (IsPullback.of_horiz_isIso (fst := inv (blowUpToBase (Z.comap h)))
      (snd := inv (blowUpToBase (Z.comap h)) ≫ canonicalLift h Z) (f := canonicalLift h Z)
      (g := 𝟙 _) ⟨by simp⟩) (hh.canonicalLift Z)

/-- **The extension by closure commutes with reduced flat base change.** For a cartesian square
`U_Y → Y`, `U_Y → U` over `g : Y → X`, `ι : U → X`, with `ι` a quasi-compact open immersion and
`g` flat with reduced base changes, and `𝐁` starting with `U` with reduced centres,
`((ι_*𝐁)^*_g)^red = ι_{Y*}((g_U^*𝐁)^red)`. -/
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
    have hgU : IsReducedFlatBaseChange gU := hg.of_isPullback sq
    have hc := comap_map_eq_of_isOpenImmersion ι Z
    have eY := Kollar.comap_map_eq_map_comap_of_isPullback sq hg Z
    have hcY := comap_map_eq_of_isOpenImmersion ιY (Z.comap gU)
    rw [ClosedBlowupSequence.extendByClosure_cons_of_comap_map_eq Z B ι hc]
    have : IsOpenImmersion (canonicalLift ι (Z.map ι)) :=
      MorphismProperty.of_isPullback (P := @IsOpenImmersion)
        (Kollar.isPullback_canonicalLift_of_flat ι (Z.map ι)) ‹_›
    have : QuasiCompact (canonicalLift ι (Z.map ι)) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact)
        (Kollar.isPullback_canonicalLift_of_flat ι (Z.map ι)) ‹_›
    by_cases hZ : Z.comap gU = ⊤
    · have hZX : (Z.map ι).comap g = ⊤ := by rw [eY, hZ, Scheme.IdealSheafData.map_top]
      simp only [pullbackReduced, hZ, hZX, dite_true]
      have sq' : IsPullback ιY (blowUpLift Z gU (isCartierOver_of_comap_eq_top gU Z hZ))
          (blowUpLift (Z.map ι) g (isCartierOver_of_comap_eq_top g _ hZX))
          (eqToHom (congrArg blowUp hc.symm) ≫ canonicalLift ι (Z.map ι)) := by
        refine IsPullback.of_bot ?_ ?_ (isPullback_eqToHom_canonicalLift ι (Z.map ι) Z hc)
        · simpa only [blowUpLift_comp] using sq
        · have hZc : (Z.map ι).comap (ιY ≫ g) = ⊤ := by
            rw [Scheme.IdealSheafData.comap_comp, hZX, Scheme.IdealSheafData.comap_top]
          have hc' := isCartierOver_of_comap_eq_top (ιY ≫ g) _ hZc
          refine (blowUpLift_unique _ _ hc' _ ?_).trans (blowUpLift_unique _ _ hc' _ ?_).symm
          · rw [Category.assoc, blowUpLift_comp]
          · rw [Category.assoc, Category.assoc, canonicalLift_comp_blowUpToBase,
              ← Category.assoc (eqToHom _), eqToHom_comp_blowUpToBase hc.symm, ← Category.assoc,
              blowUpLift_comp, sq.w]
      exact ih hB.2 _ _ (isReducedFlatBaseChange_blowUpLift hg _ hZX) _ _ sq'
    · have hZX : (Z.map ι).comap g ≠ ⊤ := by
        intro h
        apply hZ
        rw [← hcY, ← eY, h, Scheme.IdealSheafData.comap_top]
      simp only [pullbackReduced, hZ, hZX, dite_false]
      rw [ClosedBlowupSequence.extendByClosure_cons_of_comap_map_eq _ _ ιY hcY]
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

/-- Pulling back along a morphism precomposed with an isomorphism changes the end by an
isomorphism over the last morphisms. -/
private theorem exists_iso_pullback_comp_of_isIso {X : Scheme.{u}} (D : ClosedBlowupSequence X) :
    ∀ {W W' : Scheme.{u}} (f : W ⟶ X) (e : W' ⟶ W) [IsIso e],
      ∃ φ : (D.pullback f).target ≅ (D.pullback (e ≫ f)).target,
        φ.hom ≫ D.pullbackHom (e ≫ f) = D.pullbackHom f := by
  induction D with
  | nil X =>
    intro W W' f e _
    exact ⟨(asIso e).symm, by change inv e ≫ e ≫ f = f; simp⟩
  | cons Z D ih =>
    intro W W' f e _
    have hiso : IsIso (canonicalLift e (Z.comap f)) :=
      MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme)
        (Kollar.isPullback_canonicalLift_of_flat e (Z.comap f)) ‹IsIso e›
    have hcl : canonicalLift (e ≫ f) Z =
        (eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_comp Z e f)) ≫
          canonicalLift e (Z.comap f)) ≫ canonicalLift f Z := by
      rw [Category.assoc, canonicalLift_comp_canonicalLift f e Z]
      simp
    show ∃ φ : (D.pullback (canonicalLift f Z)).target ≅
        (D.pullback (canonicalLift (e ≫ f) Z)).target,
      φ.hom ≫ D.pullbackHom (canonicalLift (e ≫ f) Z) = D.pullbackHom (canonicalLift f Z)
    rw [hcl]
    exact ih _ _

/-- The reduced pull-back and the pull-back have isomorphic ends over the last morphisms. -/
private theorem exists_iso_pullbackReducedWithHom {X : Scheme.{u}} (D : ClosedBlowupSequence X) :
    ∀ {W : Scheme.{u}} (ι : W ⟶ X),
      ∃ φ : (D.pullbackReducedWithHom ι).1.target ≅ (D.pullback ι).target,
        φ.hom ≫ D.pullbackHom ι = (D.pullbackReducedWithHom ι).2 := by
  induction D with
  | nil X =>
    intro W ι
    exact ⟨Iso.refl _, by change 𝟙 _ ≫ ι = ι; simp⟩
  | cons Z D ih =>
    intro W ι
    by_cases hZ : Z.comap ι = ⊤
    · rw [pullbackReducedWithHom_cons_of_eq_top Z D ι hZ]
      have := Kollar.isIso_blowUpToBase_comap_of_eq_top ι Z hZ
      have hcl : canonicalLift ι Z = blowUpToBase (Z.comap ι) ≫
          blowUpLift Z ι (isCartierOver_of_comap_eq_top ι Z hZ) := by
        rw [Kollar.blowUpLift_eq_inv_comp_canonicalLift ι Z hZ, IsIso.hom_inv_id_assoc]
      show ∃ φ : _ ≅ (D.pullback (canonicalLift ι Z)).target,
        φ.hom ≫ D.pullbackHom (canonicalLift ι Z) = _
      rw [hcl]
      obtain ⟨φ₁, h₁⟩ := ih (blowUpLift Z ι (isCartierOver_of_comap_eq_top ι Z hZ))
      obtain ⟨φ₂, h₂⟩ := exists_iso_pullback_comp_of_isIso D
        (blowUpLift Z ι (isCartierOver_of_comap_eq_top ι Z hZ)) (blowUpToBase (Z.comap ι))
      exact ⟨φ₁ ≪≫ φ₂, by rw [Iso.trans_hom, Category.assoc, h₂, h₁]⟩
    · rw [pullbackReducedWithHom_cons_of_ne_top Z D ι hZ]
      exact ih (canonicalLift ι Z)

/-- The kernel of the last morphism of the pull-back is that of the reduced pull-back. -/
private theorem ker_pullbackHom_eq {X W : Scheme.{u}} (D : ClosedBlowupSequence X) (ι : W ⟶ X) :
    (D.pullbackHom ι).ker = (D.pullbackReducedWithHom ι).2.ker := by
  obtain ⟨φ, hφ⟩ := exists_iso_pullbackReducedWithHom D ι
  rw [← hφ, Scheme.Hom.ker_comp_of_isIso]

/-- **The reduced pull-back is functorial**: `((h^*𝐁)^red)^*_k)^red = ((k ≫ h)^*𝐁)^red`, with
the composite of the last morphisms. -/
private theorem pullbackReducedWithHom_comp_heq {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {W Y Y' : Scheme.{u}} (h : W ⟶ X) (k : Y ⟶ W) (k' : Y' ⟶ X) (e : Y = Y'),
      eqToHom e ≫ k' = k ≫ h →
      (⟨((B.pullbackReducedWithHom h).1.pullbackReducedWithHom k).1,
          ((B.pullbackReducedWithHom h).1.pullbackReducedWithHom k).2 ≫
            (B.pullbackReducedWithHom h).2⟩ :
          Σ C : ClosedBlowupSequence Y, C.target ⟶ B.target) ≍ B.pullbackReducedWithHom k' := by
  induction B with
  | nil X =>
    intro W Y Y' h k k' e hk
    subst e
    simp only [eqToHom_refl, Category.id_comp] at hk
    subst hk
    rfl
  | cons Z B ih =>
    intro W Y Y' h k k' e hk
    subst e
    simp only [eqToHom_refl, Category.id_comp] at hk
    subst hk
    by_cases hZ : Z.comap h = ⊤
    · have hZ' : Z.comap (k ≫ h) = ⊤ := by
        rw [Scheme.IdealSheafData.comap_comp, hZ, Scheme.IdealSheafData.comap_top]
      rw [pullbackReducedWithHom_cons_of_eq_top Z B h hZ,
        pullbackReducedWithHom_cons_of_eq_top Z B (k ≫ h) hZ']
      refine ih _ k _ rfl ?_
      simp only [eqToHom_refl, Category.id_comp]
      exact (blowUpLift_unique _ _ _ _ (by rw [Category.assoc, blowUpLift_comp])).symm
    · rw [pullbackReducedWithHom_cons_of_ne_top Z B h hZ]
      dsimp only
      by_cases hZk : (Z.comap h).comap k = ⊤
      · have hZ' : Z.comap (k ≫ h) = ⊤ := by rw [Scheme.IdealSheafData.comap_comp, hZk]
        rw [pullbackReducedWithHom_cons_of_eq_top _ _ k hZk,
          pullbackReducedWithHom_cons_of_eq_top Z B (k ≫ h) hZ']
        refine ih _ _ _ rfl ?_
        simp only [eqToHom_refl, Category.id_comp]
        refine (blowUpLift_unique _ _ _ _ ?_).symm
        rw [Category.assoc, canonicalLift_comp_blowUpToBase, ← Category.assoc, blowUpLift_comp]
      · have hZ' : Z.comap (k ≫ h) ≠ ⊤ := by rwa [Scheme.IdealSheafData.comap_comp]
        rw [pullbackReducedWithHom_cons_of_ne_top _ _ k hZk,
          pullbackReducedWithHom_cons_of_ne_top Z B (k ≫ h) hZ']
        have hc : (Z.comap h).comap k = Z.comap (k ≫ h) :=
          (Scheme.IdealSheafData.comap_comp Z k h).symm
        refine heq_of_eq (sigma_cons_eq_of_heq hc ?_)
        refine ih _ _ _ (congrArg blowUp hc) ?_
        rw [canonicalLift_comp_canonicalLift h k Z]

/-- **The birational transform of a closed subscheme under reduced flat base change.** For flat
`g : Y → X`, the kernel of `((g^*𝐁)^red)|_{g⁻¹H} → Y'` is the inverse image along the last
morphism `Y' → X_r` of the kernel of `𝐁|_H → X_r`. -/
private theorem ker_restrictHom_pullbackReduced {X Y : Scheme.{u}} (B : ClosedBlowupSequence X)
    (g : Y ⟶ X) [Flat g] (H : X.IdealSheafData) :
    ((B.pullbackReduced g).restrictHom (H.comap g)).ker =
      (B.restrictHom H).ker.comap (B.pullbackReducedHom g) := by
  have key : ∀ q : Σ C : ClosedBlowupSequence Y, C.target ⟶ B.target,
      q = B.pullbackReducedWithHom g → (q.1.restrictHom (H.comap g)).ker =
        (B.restrictHom H).ker.comap q.2 := by
    rintro q rfl
    have sqH := Kollar.isPullback_comapSubschemeProj g H
    have hγ : Flat (Kollar.comapSubschemeProj g H) :=
      MorphismProperty.of_isPullback (P := @Flat) sqH ‹_›
    have K1 := pullbackReducedWithHom_comp_heq B g (H.comap g).subschemeι
      ((H.comap g).subschemeι ≫ g) rfl (by simp)
    have K2 := pullbackReducedWithHom_comp_heq B H.subschemeι (Kollar.comapSubschemeProj g H)
      ((H.comap g).subschemeι ≫ g) rfl (by simp [sqH.w])
    have hp := eq_of_heq (K1.trans K2.symm)
    have hC := congrArg Sigma.fst hp
    have sq := Kollar.isPullback_of_sigma_eq (Kollar.isPullback_pullbackReducedWithHom_of_flat B g)
      (H.comap g).subschemeι H.subschemeι hC _ _ _ _ hp
      (pullbackReducedWithHom_toBase_comm _ _).symm (pullbackReducedWithHom_toBase_comm _ _).symm
      ((Kollar.isPullback_pullbackReducedWithHom_of_flat _ _).paste_horiz sqH)
    have hcl : IsClosedImmersion (B.pullbackReducedWithHom H.subschemeι).2 := by
      obtain ⟨φ, hφ⟩ := exists_iso_pullbackReducedWithHom B H.subschemeι
      have := Kollar.isClosedImmersion_pullbackHom B H.subschemeι
      rw [← hφ]
      infer_instance
    exact (ker_pullbackHom_eq _ _).trans ((Kollar.ker_eq_comap_of_isPullback sq).trans
      (congrArg (fun J => Scheme.IdealSheafData.comap J _) (ker_pullbackHom_eq _ _).symm))
  have := key _ rfl
  rwa [pullbackReducedWithHom_eq] at this

end ExtendByClosureReduced

/-- The divisor `E^V = (H'|_V, E'^s|_V, …)` on an open `V` of the end `u`. -/
private noncomputable def tailDivisor (u : FieldBlowupTriple.{u}) (s : ℕ) (H' : u.X.IdealSheafData)
    (V : u.X.Opens) : OrderedDivisor V :=
  ⟨u.E.s - s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
    fun i => (u.E.E ⟨s + i, by omega⟩).comap V.ι⟩

/-- The triple `(V, I|_V, E^V)`. -/
private noncomputable def tailTriple (u : FieldBlowupTriple.{u}) (s : ℕ) (H' : u.X.IdealSheafData)
    (V : u.X.Opens) : FieldBlowupTriple.{u} :=
  ⟨⟨V, u.I.comap V.ι, tailDivisor u s H' V⟩, u.k, V.ι ≫ u.sX⟩

open Classical in
/-- `𝐁_V = 𝓑𝓓_{n,m,0}(V, I|_V, E^V)` (empty if `V = ∅` or this is not a triple). -/
private noncomputable def tailSeq (M : MarkedFamily.{u}) (m n s : ℕ) (u : FieldBlowupTriple.{u})
    (H' : u.X.IdealSheafData) (V : u.X.Opens) : ClosedBlowupSequence V :=
  if (V : Set u.X).Nonempty ∧ IsTriple (tailTriple u s H' V).sX (tailTriple u s H' V).I
    (tailTriple u s H' V).E then bdFunctor M n m 0 (tailTriple u s H' V) else .nil _

/-- The part of `boMaximalContact` after a sequence `P` (in `boMaximalContact`, the divisor
separation sequence): the extension by closure to `X'` of `𝓑𝓓_{dim X, m, 0}(V, J'|_V, E^V)`. -/
private noncomputable def boTail (M : MarkedFamily.{u}) (m : ℕ) (t : FieldBlowupTriple.{u})
    (P : ClosedBlowupSequence t.X) (H : t.X.IdealSheafData) : ClosedBlowupSequence P.target :=
  (tailSeq M m (dimNat t.X) t.E.s (t.endOf P) (P.restrictHom H).ker
    (tailOpen (t.endOf P) t.E.s)).extendByClosure (tailOpen (t.endOf P) t.E.s).ι

private theorem boMaximalContact_eq_boTail (M : MarkedFamily.{u}) (m : ℕ)
    (t : FieldBlowupTriple.{u}) (H : t.X.IdealSheafData) :
    boMaximalContact M m t H =
      ((divisorSeparationSequence M m t).append
        (boTail M m t (divisorSeparationSequence M m t) H)).reduction :=
  rfl

private theorem canonicalLift_id_eq_eqToHom {X : Scheme.{u}} (Z : X.IdealSheafData) :
    canonicalLift (𝟙 X) Z = eqToHom (congrArg blowUp (Scheme.IdealSheafData.comap_id Z)) := by
  have key : ∀ (Z' : X.IdealSheafData) (e : Z' = Z),
      eqToHom (congrArg blowUp e) ≫ blowUpToBase Z = blowUpToBase Z' := by
    rintro _ rfl; simp
  symm
  exact blowUpLift_unique _ _ _ _ (by
    rw [key _ (Scheme.IdealSheafData.comap_id Z)]; simp)

private theorem pullbackReduced_append_heq {X : Scheme.{u}} (D : ClosedBlowupSequence X)
    (hD : D.HasNoEmptyBlowups) (C : ClosedBlowupSequence D.target) :
    ∀ {Y : Scheme.{u}} (e : Y = X) (h : Y ⟶ X), h = eqToHom e →
      (D.append C).pullbackReduced h ≍ D.append C.reduction := by
  induction D with
  | nil X =>
    intro Y e h hh
    subst e
    obtain rfl : h = 𝟙 _ := by simpa using hh
    rfl
  | cons Z D ih =>
    intro Y e h hh
    subst e
    obtain rfl : h = 𝟙 _ := by simpa using hh
    have hc : Z.comap (𝟙 _) = Z := Scheme.IdealSheafData.comap_id Z
    have hne : Z.comap (𝟙 _) ≠ ⊤ := by rw [hc]; exact hD.1
    change (ClosedBlowupSequence.cons Z (D.append C)).pullbackReduced (𝟙 _) ≍
      ClosedBlowupSequence.cons Z (D.append C.reduction)
    simp only [ClosedBlowupSequence.pullbackReduced, hne, dite_false]
    refine heq_of_eq (ClosedBlowupSequence.cons_eq_cons_iff.2 ⟨hc, ?_⟩)
    exact ih hD.2 C (congrArg blowUp hc) _ (canonicalLift_id_eq_eqToHom Z)

/-- `(𝐃 ⋅ 𝐂)^red = 𝐃 ⋅ 𝐂^red` for `𝐃` without empty blow-ups. -/
private theorem reduction_append_of_hasNoEmptyBlowups {X : Scheme.{u}}
    (D : ClosedBlowupSequence X) (hD : D.HasNoEmptyBlowups) (C : ClosedBlowupSequence D.target) :
    (D.append C).reduction = D.append C.reduction :=
  eq_of_heq (pullbackReduced_append_heq D hD C rfl _ (by simp))

private theorem hasNoEmptyBlowups_pullbackReduced {X Y : Scheme.{u}}
    (B : ClosedBlowupSequence X) (h : Y ⟶ X) : (B.pullbackReduced h).HasNoEmptyBlowups := by
  rw [← ClosedBlowupSequence.reduction_pullback]
  exact ClosedBlowupSequence.hasNoEmptyBlowups_reduction _

private theorem fieldBlowupTriple_mk_congr {X : Scheme.{u}} {I I' : X.IdealSheafData}
    (E : OrderedDivisor X) (k : Type u) [Field k] {s s' : X ⟶ Spec (.of k)} (hI : I = I')
    (hs : s = s') :
    (⟨⟨X, I, E⟩, k, s⟩ : FieldBlowupTriple.{u}) = ⟨⟨X, I', E⟩, k, s'⟩ := by
  subst hI hs; rfl

/-- **Kollár 3.104 Step 2.1.`j` under smooth morphisms.** The end on
`Y` is the pull-back of the end on `X` along `Π_{(j)}.pullbackReducedHom g` except for the ordered
total transform, which agrees with the inverse image up to empty entries of index `≥ s > j`
(`agreeUpToEmpty_pullbackReduced`); `bdFunctor_congr_of_agree` (with `hMe`) removes them, and
`commutesWithSmoothOn_bdFunctor` gives the reduced pull-back. For surjective `g` there are no such
entries (`orderedTotalTransform_pullbackReduced_of_surjective`), and `hMe` is not needed. -/
private theorem bdFunctor_endOf_divisorSeparationAux_pullbackReduced {N n n' m : ℕ}
    (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m)
    {Y : Scheme.{u}} (g : Y ⟶ t.X) (hg : Smooth g)
    (hMeg : (∀ d ∈ Set.Icc 0 (N - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t)) ∨ Surjective g)
    (hY : t.pullback g ∈ triples)
    (hdimY : topologicalKrullDim Y = ((n' : ℕ∞) : WithBot ℕ∞)) (hn' : 1 ≤ n') (hn'N : n' ≤ N)
    (hmaxY : maxOrder (t.pullback g).I = m)
    (j : ℕ) (hj : j < t.E.s)
    (hP : divisorSeparationAux M m (t.pullback g) j =
      (divisorSeparationAux M m t j).pullbackReduced g) :
    bdFunctor M (dimNat Y) m j
        ((t.pullback g).endOf ((divisorSeparationAux M m t j).pullbackReduced g)) =
      (bdFunctor M (dimNat t.X) m j (t.endOf (divisorSeparationAux M m t j))).pullbackReduced
        ((divisorSeparationAux M m t j).pullbackReducedHom g) := by
  haveI := hg
  have hdn : dimNat t.X = n := dimNat_eq_of_eq hdim
  have hdn' : dimNat Y = n' := dimNat_eq_of_eq hdimY
  have hPX := isOrderMTripleSeq_divisorSeparationAux M hN hM t ht hdim hn hnN hm hmax.le j
    hj.le
  have hPY := isOrderMTripleSeq_divisorSeparationAux M hN hM (t.pullback g) hY hdimY hn' hn'N hm
    hmaxY.le j (by change j ≤ t.E.s; omega)
  rw [hP] at hPY
  have hneP := hasNoEmptyBlowups_divisorSeparationAux M m t j
  generalize divisorSeparationAux M m t j = P at hPX hPY hneP ⊢
  change P.pullbackReduced g |>.IsOrderMTripleSeq (g ≫ t.sX) (t.I.comap g) (t.E.comap g) m
    at hPY
  have hI := Kollar.controlledTransform_pullbackReduced P g t.sX (g ≫ t.sX) t.I t.E
    (t.E.comap g) m hPX hPY
  have hs : (P.pullbackReduced g).toBase ≫ g ≫ t.sX =
      P.pullbackReducedHom g ≫ P.toBase ≫ t.sX := by
    rw [← Category.assoc, ClosedBlowupSequence.pullbackReducedHom_toBase_comm, Category.assoc]
  have hag := agreeUpToEmpty_pullbackReduced t.E.s P g t.sX t.I t.E m hPX le_rfl
  have hsm' : Smooth (P.pullbackReducedHom g) := Kollar.smooth_pullbackReducedHom P g
  obtain ⟨hdX, hmX, hsX⟩ := end_of_isOrderMTripleSeq m _ P t.sX t.I t.E hPX hmax.le hdim
  obtain ⟨hdY, hmY, -⟩ := end_of_isOrderMTripleSeq m _ (P.pullbackReduced g) (g ≫ t.sX)
    (t.I.comap g) (t.E.comap g) hPY hmaxY.le hdimY
  have hTX := ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m P _ _ _ hPX
  have hTY := ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m (P.pullbackReduced g) _ _ _
    hPY
  rw [hs, hI] at hTY
  rw [hI] at hmY
  set g' := P.pullbackReducedHom g with hg'
  set EY := (P.pullbackReduced g).orderedTotalTransform (t.E.comap g) with hEY
  set u := (t.endOf P).pullback g' with hu
  have hTu : IsTriple u.sX u.I u.E :=
    (isTriple_iff_of_deleteEmpty_eq _ _ hag.deleteEmpty_eq).1 hTY
  have hend : (t.pullback g).endOf (P.pullbackReduced g) = { u with E := EY } :=
    fieldBlowupTriple_mk_congr _ _ hI hs
  have hlft : LocallyOfFiniteType (g' ≫ (t.endOf P).sX) := hTu.2.2.1
  have hqc : QuasiCompact (g' ≫ (t.endOf P).sX) := hTu.2.2.2.1
  obtain ⟨-, hcomm⟩ := commutesWithSmoothOn_bdFunctor (N := N) (m := m) (j := j) M hN hM hm
  have hjX : j < (t.endOf P).E.s := lt_of_lt_of_le hj hsX
  have hmemX : t.endOf P ∈ {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s} :=
    ⟨⟨hTX, ⟨n, ⟨hn, hnN⟩, hdX⟩, hmX⟩, hjX⟩
  have hmemY : u ∈ {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s} :=
    ⟨⟨hTu, ⟨n', ⟨hn', hn'N⟩, hdY⟩, hmY⟩, hjX⟩
  have h3 : bdFunctor M (dimNat (P.pullbackReduced g).target) m j u =
      ((bdFunctor M (dimNat P.target) m j (t.endOf P)).pullback g').reduction :=
    hcomm (t.endOf P) hmemX _ g' hsm' hlft hqc hmemY
  rw [dimNat_eq_of_eq hdY, dimNat_eq_of_eq hdX, ← hdn, ← hdn'] at h3
  have hTEY : IsTriple u.sX u.I EY := hTY
  have hMe' : IgnoresEmptyEntriesMarked (markedTriplesOfDim {dimNat Y - 1} m.factorial)
      (fun t _ => M (dimNat Y - 1) m.factorial t) ∨ EY = u.E := by
    refine hMeg.imp (fun hMe => ?_) (fun hsurj => ?_)
    · exact hMe (dimNat Y - 1) ⟨Nat.zero_le _, by omega⟩ m.factorial
        (Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m))
    · haveI := hsurj
      exact (orderedTotalTransform_pullbackReduced_of_surjective P g t.sX t.I t.E m hPX hneP).2
  have e1 : bdFunctor M (dimNat Y) m j ((t.pullback g).endOf (P.pullbackReduced g)) =
      bdFunctor M (dimNat Y) m j { u with E := EY } := eq_of_heq (congr_arg_heq _ hend)
  have e2 : bdFunctor M (dimNat Y) m j { u with E := EY } = bdFunctor M (dimNat Y) m j u :=
    bdFunctor_congr_of_agree M (dimNat Y) m u EY u.E t.E.s j hj hag
      (fun hj' hne => by
        rw [hdn']
        exact hasDimensionIn_bdDivisor { u with E := EY } hTEY hdY m j hj' hne) hMe'
  exact e1.trans (e2.trans (h3.trans (ClosedBlowupSequence.reduction_pullback _ _)))

open Classical in
/-- The first `j ≤ s` steps of the divisor separation sequence commute with smooth morphisms,
up to reduction. -/
private theorem divisorSeparationAux_pullback {N n n' m : ℕ}
    (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m)
    {Y : Scheme.{u}} (g : Y ⟶ t.X) (hg : Smooth g)
    (hMeg : (∀ d ∈ Set.Icc 0 (N - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t)) ∨ Surjective g)
    (hY : t.pullback g ∈ triples)
    (hdimY : topologicalKrullDim Y = ((n' : ℕ∞) : WithBot ℕ∞)) (hn' : 1 ≤ n') (hn'N : n' ≤ N)
    (hmaxY : maxOrder (t.pullback g).I = m) :
    ∀ j ≤ t.E.s, divisorSeparationAux M m (t.pullback g) j =
      (divisorSeparationAux M m t j).pullbackReduced g := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
    have hP := ih (by omega)
    have hbd := bdFunctor_endOf_divisorSeparationAux_pullbackReduced M hN hM t ht hdim hn hnN
      hm hmax g hg hMeg hY hdimY hn' hn'N hmaxY j (by omega) hP
    have hX := ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m _ _ _ _
      (isOrderMTripleSeq_divisorSeparationAux M hN hM t ht hdim hn hnN hm hmax.le j (by omega))
    have hYt := ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m _ _ _ _
      (isOrderMTripleSeq_divisorSeparationAux M hN hM (t.pullback g) hY hdimY hn' hn'N hm
        hmaxY.le j (by change j ≤ t.E.s; omega))
    rw [hP] at hYt
    change (if IsTriple ((t.pullback g).endOf (divisorSeparationAux M m (t.pullback g) j)).sX
        ((t.pullback g).endOf (divisorSeparationAux M m (t.pullback g) j)).I
        ((t.pullback g).endOf (divisorSeparationAux M m (t.pullback g) j)).E then
        (divisorSeparationAux M m (t.pullback g) j).append
          (bdFunctor M (dimNat Y) m j
            ((t.pullback g).endOf (divisorSeparationAux M m (t.pullback g) j)))
      else divisorSeparationAux M m (t.pullback g) j) =
      (if IsTriple (t.endOf (divisorSeparationAux M m t j)).sX
        (t.endOf (divisorSeparationAux M m t j)).I (t.endOf (divisorSeparationAux M m t j)).E then
        (divisorSeparationAux M m t j).append
          (bdFunctor M (dimNat t.X) m j (t.endOf (divisorSeparationAux M m t j)))
      else divisorSeparationAux M m t j).pullbackReduced g
    have e2 : (if IsTriple (t.endOf (divisorSeparationAux M m t j)).sX
        (t.endOf (divisorSeparationAux M m t j)).I (t.endOf (divisorSeparationAux M m t j)).E then
        (divisorSeparationAux M m t j).append
          (bdFunctor M (dimNat t.X) m j (t.endOf (divisorSeparationAux M m t j)))
      else divisorSeparationAux M m t j).pullbackReduced g =
        ((divisorSeparationAux M m t j).pullbackReduced g).append
          ((bdFunctor M (dimNat t.X) m j (t.endOf (divisorSeparationAux M m t j))).pullbackReduced
            ((divisorSeparationAux M m t j).pullbackReducedHom g)) := by
      rw [if_pos]
      · exact ClosedBlowupSequence.append_pullbackReduced _ _ _
      · exact hX
    rw [e2]
    generalize divisorSeparationAux M m (t.pullback g) j = Q at hP ⊢
    subst hP
    exact (if_pos hYt).trans
      (congrArg ((divisorSeparationAux M m t j).pullbackReduced g).append hbd)

/-- **The divisor separation sequence commutes with smooth morphisms** (Kollár 3.104 Step 2.1),
up to reduction, if `𝓜` ignores empty entries or `g` is surjective. -/
private theorem divisorSeparationSequence_pullback {N n n' m : ℕ}
    (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m)
    {Y : Scheme.{u}} (g : Y ⟶ t.X) (hg : Smooth g)
    (hMeg : (∀ d ∈ Set.Icc 0 (N - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t)) ∨ Surjective g)
    (hY : t.pullback g ∈ triples)
    (hdimY : topologicalKrullDim Y = ((n' : ℕ∞) : WithBot ℕ∞)) (hn' : 1 ≤ n') (hn'N : n' ≤ N)
    (hmaxY : maxOrder (t.pullback g).I = m) :
    divisorSeparationSequence M m (t.pullback g) =
      (divisorSeparationSequence M m t).pullbackReduced g :=
  divisorSeparationAux_pullback M hN hM t ht hdim hn hnN hm hmax g hg hMeg hY hdimY hn' hn'N
    hmaxY t.E.s le_rfl

section Tail

open ClosedBlowupSequence

/-- The reduced pull-back to an empty scheme is empty. -/
private theorem pullbackReduced_of_isEmpty {X : Scheme.{u}} (B : ClosedBlowupSequence X) :
    ∀ {W : Scheme.{u}} [IsEmpty W] (h : W ⟶ X), B.pullbackReduced h = .nil W := by
  induction B with
  | nil X => intros; rfl
  | cons Z B ih =>
    intro W _ h
    have hZ : Z.comap h = ⊤ := by
      rw [← Scheme.IdealSheafData.support_eq_bot_iff]
      ext x
      exact isEmptyElim x
    simp only [pullbackReduced, hZ, dite_true]
    exact ih _

/-- The inverse image of `(D, F^0, F^1, …)` is `(h⁻¹D, h⁻¹F^0, …)`. -/
private theorem comap_cons {X Y : Scheme.{u}} {n : ℕ} (D : X.IdealSheafData)
    (F : Fin n → X.IdealSheafData) (h : Y ⟶ X) :
    (⟨n + 1, Fin.cons (α := fun _ => X.IdealSheafData) D F⟩ : OrderedDivisor X).comap h =
      ⟨n + 1, Fin.cons (α := fun _ => Y.IdealSheafData) (D.comap h) fun i => (F i).comap h⟩ := by
  simp only [OrderedDivisor.comap, OrderedDivisor.mk.injEq, heq_eq_eq, true_and]
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- A smooth pull-back of a triple to an equidimensional scheme is a triple. -/
private theorem isTriple_pullback {k : Type u} [Field k] {X Y : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} {I : X.IdealSheafData} {E : OrderedDivisor X} (hT : IsTriple s I E)
    (h : Y ⟶ X) (hh : Smooth h) (hq : QuasiCompact (h ≫ s))
    (hY : TopologicalSpace.Equidimensional Y) :
    IsTriple (h ≫ s) (I.comap h) (E.comap h) := by
  have := hh
  have := hq
  have ht : (⟨⟨X, I, E⟩, k, s⟩ : FieldBlowupTriple.{u}) ∈ triples := hT
  exact mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht) h, hY⟩

private theorem ofFn_tailDivisor (u : FieldBlowupTriple.{u}) (s : ℕ) (H' : u.X.IdealSheafData)
    (V : u.X.Opens) : List.ofFn (tailDivisor u s H' V).E =
      H'.comap V.ι :: ((List.ofFn u.E.E).drop s).map (·.comap V.ι) := by
  change List.ofFn (Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
    fun i => (u.E.E ⟨s + i, by omega⟩).comap V.ι) = _
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- An open immersion into a scheme of finite type over a field is quasi-compact. -/
private theorem quasiCompact_opens_ι {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s] [QuasiCompact s] (U : X.Opens) :
    QuasiCompact U.ι := by
  haveI := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := ⟨⟩
  haveI : TopologicalSpace.NoetherianSpace U := TopologicalSpace.NoetherianSpace.set (U : Set X)
  infer_instance

/-- The triple `(V, I|_V, E^V)` of an open of the end of the separation sequence. -/
private theorem isTriple_tailTriple (u : FieldBlowupTriple.{u}) (hu : u ∈ triples) {n : ℕ}
    (hdu : topologicalKrullDim u.X = ((n : ℕ∞) : WithBot ℕ∞)) (s : ℕ) (hs : s ≤ u.E.s)
    (H' : u.X.IdealSheafData)
    (hsnc : OrderedDivisor.IsOrderedSNC u.sX ⟨u.E.s - s + 1,
      Fin.cons (α := fun _ => u.X.IdealSheafData) H' fun i => u.E.E ⟨s + i, by omega⟩⟩)
    (V : u.X.Opens) :
    IsTriple (tailTriple u s H' V).sX (tailTriple u s H' V).I (tailTriple u s H' V).E := by
  have hlft := hu.2.2.1
  have hqc := hu.2.2.2.1
  have := quasiCompact_opens_ι u.sX V
  have hT : IsTriple u.sX u.I ⟨u.E.s - s + 1,
      Fin.cons (α := fun _ => u.X.IdealSheafData) H' fun i => u.E.E ⟨s + i, by omega⟩⟩ :=
    ⟨hu.1, hu.2.1, hu.2.2.1, hu.2.2.2.1, hu.2.2.2.2.1, hu.2.2.2.2.2.1, hsnc⟩
  have := isTriple_pullback hT V.ι inferInstance inferInstance
    (equidimensional_opens u.sX hu.2.2.2.2.1 V)
  rwa [comap_cons] at this

private theorem tailSeq_of_pos (M : MarkedFamily.{u}) (m n s : ℕ) (u : FieldBlowupTriple.{u})
    (H' : u.X.IdealSheafData) (V : u.X.Opens) (h : (V : Set u.X).Nonempty ∧
      IsTriple (tailTriple u s H' V).sX (tailTriple u s H' V).I (tailTriple u s H' V).E) :
    tailSeq M m n s u H' V = bdFunctor M n m 0 (tailTriple u s H' V) :=
  if_pos h

private theorem tailSeq_of_neg (M : MarkedFamily.{u}) (m n s : ℕ) (u : FieldBlowupTriple.{u})
    (H' : u.X.IdealSheafData) (V : u.X.Opens) (h : ¬ ((V : Set u.X).Nonempty ∧
      IsTriple (tailTriple u s H' V).sX (tailTriple u s H' V).I (tailTriple u s H' V).E)) :
    tailSeq M m n s u H' V = .nil _ :=
  if_neg h

private theorem tailSeq_of_not_nonempty (M : MarkedFamily.{u}) (m n s : ℕ)
    (u : FieldBlowupTriple.{u}) (H' : u.X.IdealSheafData) (V : u.X.Opens)
    (h : ¬ (V : Set u.X).Nonempty) : tailSeq M m n s u H' V = .nil _ :=
  if_neg fun h' => h h'.1

private theorem mem_tailOpen_iff (v : FieldBlowupTriple.{u}) (s : ℕ) (x : v.X) :
    x ∈ tailOpen v s ↔ ∀ (i : ℕ) (hi : i < s) (h : i < v.E.s),
      x ∉ ((v.E.E ⟨i, h⟩).support : Set v.X) := by
  change x ∉ ((⨆ i : Fin v.E.s, if (i : ℕ) < s then (v.E.E i).support else ⊥ :
    TopologicalSpace.Closeds v.X) : Set v.X) ↔ _
  rw [← Finset.sup_univ_eq_iSup, TopologicalSpace.Closeds.coe_finset_sup,
    Finset.sup_set_eq_biUnion]
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, Function.comp_apply, not_exists]
  constructor
  · intro h i hi hiE hx
    refine h ⟨i, hiE⟩ ?_
    rwa [if_pos hi]
  · intro h i hx
    split_ifs at hx with hi
    · exact h i hi i.2 hx
    · exact hx

/-- The open `V_Y` on the end of the reduced pull-back is the inverse image of `V`. -/
private theorem tailOpen_comap (u : FieldBlowupTriple.{u}) (s : ℕ) {Y' : Scheme.{u}}
    (g' : Y' ⟶ u.X) (IY : Y'.IdealSheafData) (EY : OrderedDivisor Y')
    (sY : Y' ⟶ Spec (.of u.k)) (hag : AgreeUpToEmpty s EY (u.E.comap g')) :
    tailOpen ⟨⟨Y', IY, EY⟩, u.k, sY⟩ s = g' ⁻¹ᵁ tailOpen u s := by
  have hsY := hag.le_left
  have hsX : s ≤ u.E.s := hag.le_right
  ext x
  change x ∈ tailOpen ⟨⟨Y', IY, EY⟩, u.k, sY⟩ s ↔ g' x ∈ tailOpen u s
  rw [mem_tailOpen_iff, mem_tailOpen_iff]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  change (∀ h : i < EY.s, _) ↔ ∀ h : i < u.E.s, _
  have he := fun (h₁ : i < EY.s) (h₂ : i < u.E.s) => hag.entry_eq i hi h₁ h₂
  constructor
  · intro H h hx
    refine H (by omega) ?_
    rw [he _ h]
    change x ∈ (((u.E.E ⟨i, h⟩).comap g').support : Set Y')
    rwa [Scheme.IdealSheafData.support_comap]
  · intro H h hx
    refine H (by omega) ?_
    rw [he h (by omega)] at hx
    change x ∈ (((u.E.E ⟨i, _⟩).comap g').support : Set Y') at hx
    rwa [Scheme.IdealSheafData.support_comap] at hx

/-- The divisor `E^{V_Y}` agrees with the inverse image of `E^V` up to empty entries after the
first. -/
private theorem agreeUpToEmpty_tailDivisor (u : FieldBlowupTriple.{u}) (s : ℕ) {Y' : Scheme.{u}}
    (g' : Y' ⟶ u.X) (IY : Y'.IdealSheafData) (EY : OrderedDivisor Y')
    (sY : Y' ⟶ Spec (.of u.k)) (hag : AgreeUpToEmpty s EY (u.E.comap g'))
    (H' : u.X.IdealSheafData) (V : u.X.Opens) :
    AgreeUpToEmpty 1 (tailDivisor ⟨⟨Y', IY, EY⟩, u.k, sY⟩ s (H'.comap g') (g' ⁻¹ᵁ V))
      ((tailDivisor u s H' V).comap (g' ∣_ V)) := by
  classical
  have hc : ∀ D : u.X.IdealSheafData,
      (D.comap g').comap (g' ⁻¹ᵁ V).ι = (D.comap V.ι).comap (g' ∣_ V) := fun D => by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  obtain ⟨A, B, B', hEA, hFA, hA, hB⟩ := hag
  have hdE : (List.ofFn EY.E).drop s = B := by rw [hEA, ← hA, List.drop_left]
  have hdF : ((List.ofFn u.E.E).map (·.comap g')).drop s = B' := by
    rw [← ofFn_comap_E, hFA, ← hA, List.drop_left]
  refine ⟨[(H'.comap g').comap (g' ⁻¹ᵁ V).ι], B.map (·.comap (g' ⁻¹ᵁ V).ι),
    B'.map (·.comap (g' ⁻¹ᵁ V).ι), ?_, ?_, rfl, ?_⟩
  · rw [ofFn_tailDivisor]
    change _ :: ((List.ofFn EY.E).drop s).map _ = _
    rw [hdE]
    rfl
  · rw [ofFn_comap_E, ofFn_tailDivisor, ← hdF, ← List.map_drop, List.map_cons, List.map_map,
      List.map_map, List.singleton_append, hc H']
    congr 1
    exact List.map_congr_left fun D _ => (hc D).symm
  · refine filter_map_eq_of_filter_eq _ _ _ (fun D hD => ?_) hB
    simp only [ne_eq, decide_eq_false_iff_not, not_not] at hD ⊢
    rw [hD, Scheme.IdealSheafData.comap_top]

/-- The divisor `E^{V_Y}` is the inverse image of `E^V` when `E_Y = g'⁻¹E`. -/
private theorem tailDivisor_comap (u : FieldBlowupTriple.{u}) (s : ℕ) {Y' : Scheme.{u}}
    (g' : Y' ⟶ u.X) (IY : Y'.IdealSheafData) (EY : OrderedDivisor Y')
    (sY : Y' ⟶ Spec (.of u.k)) (hEY : EY = u.E.comap g')
    (H' : u.X.IdealSheafData) (V : u.X.Opens) :
    tailDivisor ⟨⟨Y', IY, EY⟩, u.k, sY⟩ s (H'.comap g') (g' ⁻¹ᵁ V) =
      (tailDivisor u s H' V).comap (g' ∣_ V) := by
  subst hEY
  have hc : ∀ D : u.X.IdealSheafData,
      (D.comap g').comap (g' ⁻¹ᵁ V).ι = (D.comap V.ι).comap (g' ∣_ V) := fun D => by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  apply eq_of_ofFn_eq
  rw [ofFn_comap_E, ofFn_tailDivisor, ofFn_tailDivisor, ofFn_comap_E, List.map_cons,
    ← List.map_drop, List.map_map, List.map_map, hc H']
  congr 1
  exact List.map_congr_left fun D _ => hc D

/-- **`𝐁_V` under smooth base change.** -/
private theorem tailSeq_pullback {N n n' m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (hm : 1 ≤ m) (s : ℕ) (u : FieldBlowupTriple.{u}) (hu : u ∈ triples)
    (hdu : topologicalKrullDim u.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hmu : maxOrder u.I ≤ m) (H' : u.X.IdealSheafData) (hs : s ≤ u.E.s)
    (hsnc : OrderedDivisor.IsOrderedSNC u.sX ⟨u.E.s - s + 1,
      Fin.cons (α := fun _ => u.X.IdealSheafData) H' fun i => u.E.E ⟨s + i, by omega⟩⟩)
    {Y' : Scheme.{u}} (g' : Y' ⟶ u.X) (hg' : Smooth g') (EY : OrderedDivisor Y')
    (hag : AgreeUpToEmpty s EY (u.E.comap g'))
    (hMeE : (∀ d ∈ Set.Icc 0 (N - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t)) ∨
        EY = u.E.comap g')
    (hTY : IsTriple (g' ≫ u.sX) (u.I.comap g') EY)
    (hdY : topologicalKrullDim Y' = ((n' : ℕ∞) : WithBot ℕ∞)) (hn' : 1 ≤ n') (hn'N : n' ≤ N)
    (hmY : maxOrder (u.I.comap g') ≤ m) (V : u.X.Opens) :
    tailSeq M m n' s ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ (H'.comap g') (g' ⁻¹ᵁ V) =
      (tailSeq M m n s u H' V).pullbackReduced (g' ∣_ V) := by
  have := hg'
  have hw : (g' ⁻¹ᵁ V).ι ≫ g' = (g' ∣_ V) ≫ V.ι := (morphismRestrict_ι g' V).symm
  by_cases hW : ((g' ⁻¹ᵁ V : Y'.Opens) : Set Y').Nonempty
  swap
  · haveI : IsEmpty (g' ⁻¹ᵁ V) := ⟨fun x => hW ⟨x.1, x.2⟩⟩
    rw [pullbackReduced_of_isEmpty]
    exact tailSeq_of_not_nonempty _ _ _ _ _ _ _ hW
  have hV : (V : Set u.X).Nonempty := by
    obtain ⟨x, hx⟩ := hW
    exact ⟨g' x, hx⟩
  have hTV := isTriple_tailTriple u hu hdu s hs H' hsnc V
  have hsmV : Smooth (g' ∣_ V) :=
    MorphismProperty.of_isPullback (P := @Smooth) (isPullback_morphismRestrict g' V).flip ‹_›
  haveI := hTY.2.2.1
  haveI := hTY.2.2.2.1
  have hqW := quasiCompact_opens_ι (g' ≫ u.sX) (g' ⁻¹ᵁ V)
  have hqcV : QuasiCompact ((g' ∣_ V) ≫ (tailTriple u s H' V).sX) := by
    change QuasiCompact ((g' ∣_ V) ≫ V.ι ≫ u.sX)
    rw [← Category.assoc, ← hw, Category.assoc]
    infer_instance
  have hEqW := equidimensional_opens (g' ≫ u.sX) hTY.2.2.2.2.1 (g' ⁻¹ᵁ V)
  have hTVp := isTriple_pullback hTV (g' ∣_ V) hsmV hqcV hEqW
  have hag1 := agreeUpToEmpty_tailDivisor u s g' (u.I.comap g') EY (g' ≫ u.sX) hag H' V
  have hIW : (u.I.comap g').comap (g' ⁻¹ᵁ V).ι = (u.I.comap V.ι).comap (g' ∣_ V) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hw]
  have hsW : (g' ⁻¹ᵁ V).ι ≫ g' ≫ u.sX = (g' ∣_ V) ≫ V.ι ≫ u.sX := by
    rw [← Category.assoc, hw, Category.assoc]
  have hTu : IsTriple ((g' ∣_ V) ≫ V.ι ≫ u.sX) ((u.I.comap V.ι).comap (g' ∣_ V))
      (tailDivisor ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)) :=
    (isTriple_iff_of_deleteEmpty_eq _ _ hag1.deleteEmpty_eq).2 hTVp
  have hTVY : IsTriple
      (tailTriple ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)).sX
      (tailTriple ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)).I
      (tailTriple ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)).E := by
    change IsTriple ((g' ⁻¹ᵁ V).ι ≫ g' ≫ u.sX) ((u.I.comap g').comap (g' ⁻¹ᵁ V).ι) _
    rwa [hsW, hIW]
  rw [tailSeq_of_pos _ _ _ _ _ _ _ ⟨hW, hTVY⟩, tailSeq_of_pos _ _ _ _ _ _ _ ⟨hV, hTV⟩]
  haveI := hu.2.2.1
  have hdV : topologicalKrullDim V = ((n : ℕ∞) : WithBot ℕ∞) :=
    (topologicalKrullDim_opens_of_equidimensional u.sX hu.2.2.2.2.1 V hV).trans hdu
  have hdW : topologicalKrullDim (g' ⁻¹ᵁ V) = ((n' : ℕ∞) : WithBot ℕ∞) :=
    (topologicalKrullDim_opens_of_equidimensional (g' ≫ u.sX) hTY.2.2.2.2.1 _ hW).trans hdY
  have hmV : maxOrder (u.I.comap V.ι) ≤ m := (maxOrder_comap_le _ _).trans hmu
  have hmW : maxOrder ((u.I.comap V.ι).comap (g' ∣_ V)) ≤ m := by
    rw [← hIW]; exact (maxOrder_comap_le _ _).trans hmY
  obtain ⟨-, hcomm⟩ := commutesWithSmoothOn_bdFunctor (N := N) (m := m) (j := 0) M hN hM hm
  have hmemX : tailTriple u s H' V ∈
      {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ 0 < t.E.s} :=
    ⟨⟨hTV, ⟨n, ⟨hn, hnN⟩, hdV⟩, hmV⟩, Nat.succ_pos _⟩
  have hmemY : (tailTriple u s H' V).pullback (g' ∣_ V) ∈
      {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ 0 < t.E.s} :=
    ⟨⟨hTVp, ⟨n', ⟨hn', hn'N⟩, hdW⟩, hmW⟩, Nat.succ_pos _⟩
  have h3 : bdFunctor M (dimNat (g' ⁻¹ᵁ V)) m 0 ((tailTriple u s H' V).pullback (g' ∣_ V)) =
      ((bdFunctor M (dimNat V) m 0 (tailTriple u s H' V)).pullback (g' ∣_ V)).reduction :=
    hcomm _ hmemX _ (g' ∣_ V) hsmV hTVp.2.2.1 hqcV hmemY
  rw [dimNat_eq_of_eq hdW, dimNat_eq_of_eq hdV] at h3
  have hend : tailTriple ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V) =
      ⟨⟨g' ⁻¹ᵁ V, (u.I.comap V.ι).comap (g' ∣_ V),
        tailDivisor ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)⟩, u.k,
        (g' ∣_ V) ≫ V.ι ≫ u.sX⟩ :=
    fieldBlowupTriple_mk_congr _ _ hIW hsW
  have e1 : bdFunctor M n' m 0
      (tailTriple ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)) =
      bdFunctor M n' m 0 ⟨⟨g' ⁻¹ᵁ V, (u.I.comap V.ι).comap (g' ∣_ V),
        tailDivisor ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)⟩, u.k,
        (g' ∣_ V) ≫ V.ι ≫ u.sX⟩ := eq_of_heq (bdFunctor_heq_of_eq M n' m 0 hend)
  have hMe' : IgnoresEmptyEntriesMarked (markedTriplesOfDim {n' - 1} m.factorial)
      (fun t _ => M (n' - 1) m.factorial t) ∨
      tailDivisor ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V) =
        ((tailTriple u s H' V).pullback (g' ∣_ V)).E := by
    refine hMeE.imp (fun hMe => ?_) (fun hEY => ?_)
    · exact hMe (n' - 1) ⟨Nat.zero_le _, by omega⟩ m.factorial
        (Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m))
    · exact tailDivisor_comap u s g' (u.I.comap g') EY (g' ≫ u.sX) hEY H' V
  have e2 : bdFunctor M n' m 0 ⟨⟨g' ⁻¹ᵁ V, (u.I.comap V.ι).comap (g' ∣_ V),
        tailDivisor ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)⟩, u.k,
        (g' ∣_ V) ≫ V.ι ≫ u.sX⟩ =
      bdFunctor M n' m 0 ((tailTriple u s H' V).pullback (g' ∣_ V)) :=
    bdFunctor_congr_of_agree M n' m ((tailTriple u s H' V).pullback (g' ∣_ V))
      (tailDivisor ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)) _ 1 0
      Nat.one_pos hag1 (fun hj' hne => hasDimensionIn_bdDivisor ⟨⟨g' ⁻¹ᵁ V,
        (u.I.comap V.ι).comap (g' ∣_ V),
        tailDivisor ⟨⟨Y', u.I.comap g', EY⟩, u.k, g' ≫ u.sX⟩ s (H'.comap g') (g' ⁻¹ᵁ V)⟩, u.k,
        (g' ∣_ V) ≫ V.ι ≫ u.sX⟩ hTu hdW m 0 hj' hne) hMe'
  exact e1.trans (e2.trans (h3.trans (ClosedBlowupSequence.reduction_pullback _ _)))

private theorem hasNoEmptyBlowups_tailSeq (M : MarkedFamily.{u}) (m n s : ℕ)
    (u : FieldBlowupTriple.{u}) (H' : u.X.IdealSheafData) (V : u.X.Opens) :
    (tailSeq M m n s u H' V).HasNoEmptyBlowups := by
  by_cases h : (V : Set u.X).Nonempty ∧
      IsTriple (tailTriple u s H' V).sX (tailTriple u s H' V).I (tailTriple u s H' V).E
  · rw [tailSeq_of_pos _ _ _ _ _ _ _ h]
    exact hasNoEmptyBlowups_bdFunctor ..
  · rw [tailSeq_of_neg _ _ _ _ _ _ _ h]
    trivial

private theorem hasReducedCentres_tailSeq {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m) (s : ℕ)
    (u : FieldBlowupTriple.{u}) (hu : u ∈ triples)
    (hdu : topologicalKrullDim u.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hmu : maxOrder u.I ≤ m) (H' : u.X.IdealSheafData) (V : u.X.Opens) :
    (tailSeq M m n s u H' V).HasReducedCentres := by
  by_cases h : (V : Set u.X).Nonempty ∧
      IsTriple (tailTriple u s H' V).sX (tailTriple u s H' V).I (tailTriple u s H' V).E
  · rw [tailSeq_of_pos _ _ _ _ _ _ _ h]
    haveI := hu.2.2.1
    have hdV : topologicalKrullDim V = ((n : ℕ∞) : WithBot ℕ∞) :=
      (topologicalKrullDim_opens_of_equidimensional u.sX hu.2.2.2.2.1 V h.1).trans hdu
    exact ClosedBlowupSequence.hasReducedCentres_of_isOrderMTripleSeq m _ _ _ _
      (bdFunctor_isOrderMTripleSeq M hN hM (tailTriple u s H' V) h.2 hdV hn hnN hm
        ((maxOrder_comap_le V.ι u.I).trans hmu) (j := 0) (Nat.succ_pos _)).1
  · rw [tailSeq_of_neg _ _ _ _ _ _ _ h]
    trivial

private theorem tail_congr_open (M : MarkedFamily.{u}) (m n s : ℕ) (v : FieldBlowupTriple.{u})
    (Hv : v.X.IdealSheafData) {W W' : v.X.Opens} (h : W = W') :
    ((tailSeq M m n s v Hv W).extendByClosure W.ι).reduction =
      ((tailSeq M m n s v Hv W').extendByClosure W'.ι).reduction := by
  subst h; rfl

private theorem tail_heq (M : MarkedFamily.{u}) (m n s : ℕ) {v v' : FieldBlowupTriple.{u}}
    (h : v = v') (Hv : v.X.IdealSheafData) (Hv' : v'.X.IdealSheafData) (hH : Hv ≍ Hv') :
    ((tailSeq M m n s v Hv (tailOpen v s)).extendByClosure (tailOpen v s).ι).reduction ≍
      ((tailSeq M m n s v' Hv' (tailOpen v' s)).extendByClosure (tailOpen v' s).ι).reduction := by
  subst h
  cases eq_of_heq hH
  rfl

end Tail

/-- **Kollár 3.104 Step 2.2 under smooth morphisms.** `V_Y = g'⁻¹V`
(`tailOpen_comap`), `H'_Y = g'⁻¹H'` (`ker_restrictHom_pullbackReduced`), `𝐁_{V_Y}` is the reduced
pull-back of `𝐁_V` (`tailSeq_pullback`, via `commutesWithSmoothOn_bdFunctor` at `j = 0` and
`hMe`, or for surjective `g` the exact identity of ordered total transforms
`orderedTotalTransform_pullbackReduced_of_surjective`; `(V, J'|_V, E^V)` is a triple by
`isOrderedSNC_divisorSeparationSequence`), and the extension by closure commutes with the reduced
pull-back (`extendByClosure_pullbackReduced`). -/
private theorem boTail_pullbackReduced {N n n' m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H : t.X.IdealSheafData}
    (hH : IsMCHypersurface t.sX t.I H)
    {Y : Scheme.{u}} (g : Y ⟶ t.X) (hg : Smooth g)
    (hMeg : (∀ d ∈ Set.Icc 0 (N - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t)) ∨ Surjective g)
    (hY : t.pullback g ∈ triples)
    (hdimY : topologicalKrullDim Y = ((n' : ℕ∞) : WithBot ℕ∞)) (hn' : 1 ≤ n') (hn'N : n' ≤ N)
    (hmaxY : maxOrder (t.pullback g).I = m) :
    (boTail M m (t.pullback g) ((divisorSeparationSequence M m t).pullbackReduced g)
        (H.comap g)).reduction =
      (boTail M m t (divisorSeparationSequence M m t) H).pullbackReduced
        ((divisorSeparationSequence M m t).pullbackReducedHom g) := by
  haveI := hg
  have hdn : dimNat t.X = n := dimNat_eq_of_eq hdim
  have hdn' : dimNat Y = n' := dimNat_eq_of_eq hdimY
  have hA := divisorSeparationSequence_pullback M hN hM t ht hdim hn hnN hm hmax g hg hMeg hY
    hdimY hn' hn'N hmaxY
  have hPX := divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le
  have hPY := divisorSeparationSequence_isOrderMTripleSeq M hN hM (t.pullback g) hY hdimY hn'
    hn'N hm hmaxY.le
  rw [hA] at hPY
  have hsnc := (isOrderedSNC_divisorSeparationSequence M hN hM t ht hdim hn hnN hm hmax hH).2
  rw [boTail, boTail]
  set P := divisorSeparationSequence M m t with hPdef
  change (P.pullbackReduced g).IsOrderMTripleSeq (g ≫ t.sX) (t.I.comap g) (t.E.comap g) m
    at hPY
  have hI := Kollar.controlledTransform_pullbackReduced P g t.sX (g ≫ t.sX) t.I t.E
    (t.E.comap g) m hPX hPY
  have hs : (P.pullbackReduced g).toBase ≫ g ≫ t.sX =
      P.pullbackReducedHom g ≫ P.toBase ≫ t.sX := by
    rw [← Category.assoc, ClosedBlowupSequence.pullbackReducedHom_toBase_comm, Category.assoc]
  have hag := agreeUpToEmpty_pullbackReduced t.E.s P g t.sX t.I t.E m hPX le_rfl
  have hsm' : Smooth (P.pullbackReducedHom g) := Kollar.smooth_pullbackReducedHom P g
  obtain ⟨hdX, hmX, hsX⟩ := end_of_isOrderMTripleSeq m _ P t.sX t.I t.E hPX hmax.le hdim
  obtain ⟨hdY, hmY, -⟩ := end_of_isOrderMTripleSeq m _ (P.pullbackReduced g) (g ≫ t.sX)
    (t.I.comap g) (t.E.comap g) hPY hmaxY.le hdimY
  have hTX := ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m P _ _ _ hPX
  have hTY := ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m (P.pullbackReduced g) _ _ _
    hPY
  rw [hs, hI] at hTY
  rw [hI] at hmY
  have hend : (t.pullback g).endOf (P.pullbackReduced g) =
      ⟨⟨(P.pullbackReduced g).target, (P.controlledTransform t.I).comap (P.pullbackReducedHom g),
        (P.pullbackReduced g).orderedTotalTransform (t.E.comap g)⟩, t.k,
        P.pullbackReducedHom g ≫ P.toBase ≫ t.sX⟩ :=
    fieldBlowupTriple_mk_congr _ _ hI hs
  refine (eq_of_heq (tail_heq M m (dimNat Y) t.E.s hend _ _
    (heq_of_eq (ker_restrictHom_pullbackReduced P g H)))).trans ?_
  refine (tail_congr_open _ _ _ _ _ _
    (tailOpen_comap (t.endOf P) t.E.s (P.pullbackReducedHom g) _ _ _ hag)).trans ?_
  have hdX' : topologicalKrullDim (t.endOf P).X = ((dimNat t.X : ℕ∞) : WithBot ℕ∞) := by
    rwa [hdn]
  have hdY' : topologicalKrullDim (P.pullbackReduced g).target =
      ((dimNat Y : ℕ∞) : WithBot ℕ∞) := by
    rwa [hdn']
  have hMeE := hMeg.imp id fun hsurj => by
    haveI := hsurj
    exact (orderedTotalTransform_pullbackReduced_of_surjective P g t.sX t.I t.E m hPX
      (hasNoEmptyBlowups_divisorSeparationAux M m t t.E.s)).2
  have hcore := tailSeq_pullback M hN hM hm t.E.s (t.endOf P) hTX hdX' (by omega)
    (by omega) hmX (P.restrictHom H).ker hsX hsnc (P.pullbackReducedHom g) hsm'
    ((P.pullbackReduced g).orderedTotalTransform (t.E.comap g)) hag hMeE hTY hdY' (by omega)
    (by omega) hmY (tailOpen (t.endOf P) t.E.s)
  haveI : LocallyOfFiniteType (t.endOf P).sX := hTX.2.2.1
  haveI : QuasiCompact (t.endOf P).sX := hTX.2.2.2.1
  haveI := hTY.2.2.1
  haveI := hTY.2.2.2.1
  have hqV := quasiCompact_opens_ι (t.endOf P).sX (tailOpen (t.endOf P) t.E.s)
  have hqW := quasiCompact_opens_ι (P.pullbackReducedHom g ≫ P.toBase ≫ t.sX)
    (P.pullbackReducedHom g ⁻¹ᵁ tailOpen (t.endOf P) t.E.s)
  refine Eq.trans ?_ (extendByClosure_pullbackReduced _ (hasReducedCentres_tailSeq M hN hM hm
      t.E.s (t.endOf P) hTX hdX' (by omega) (by omega) hmX _ _) (tailOpen (t.endOf P) t.E.s).ι
      (P.pullbackReducedHom g) (@IsReducedFlatBaseChange.of_smooth _ _ _ hsm')
      (P.pullbackReducedHom g ⁻¹ᵁ tailOpen (t.endOf P) t.E.s).ι
      (P.pullbackReducedHom g ∣_ tailOpen (t.endOf P) t.E.s)
      (isPullback_morphismRestrict _ _).flip).symm
  exact (ClosedBlowupSequence.reduction_eq_self
    (hasNoEmptyBlowups_extendByClosure _ _ (hasNoEmptyBlowups_tailSeq ..))).trans
      (congrArg (fun B => ClosedBlowupSequence.extendByClosure B _) hcore)

/-- **Kollár, Thm. 3.104 Step 2.3 (smooth morphisms).** Let `𝓜` be a marked order-reduction
family on dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`), `(X, J, E)` a triple of
dimension `n` with `1 ≤ n ≤ N`, `m ≥ 1` with `maxord J = m`, and `H` an MC-hypersurface for `J`
(`IsMCHypersurface`). Let `g : Y → X` be smooth with `(Y, g^*J, g⁻¹E)` a triple
of dimension `n'`, `1 ≤ n' ≤ N`, and `maxord g^*J = m`, and suppose that every member `𝓜_{d,μ}`
ignores empty entries of the ordered divisor (`IgnoresEmptyEntriesMarked`) or that `g` is
surjective. Then
`boMaximalContact M m (Y, g^*J, g⁻¹E) (g⁻¹H) = (g^* boMaximalContact M m (X, J, E) H)^red`. -/
@[mmp "lem_kr3e_bo_maximal_contact_commutes_smooth"]
public theorem boMaximalContact_pullback {N n n' m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H : t.X.IdealSheafData}
    (hH : IsMCHypersurface t.sX t.I H)
    {Y : Scheme.{u}} (g : Y ⟶ t.X) (hg : Smooth g)
    (hMeg : (∀ d ∈ Set.Icc 0 (N - 1), ∀ μ : ℕ, 1 ≤ μ →
      IgnoresEmptyEntriesMarked (markedTriplesOfDim {d} μ) (fun t _ => M d μ t)) ∨ Surjective g)
    (hY : t.pullback g ∈ triples)
    (hdimY : topologicalKrullDim Y = ((n' : ℕ∞) : WithBot ℕ∞)) (hn' : 1 ≤ n') (hn'N : n' ≤ N)
    (hmaxY : maxOrder (t.pullback g).I = m) :
    boMaximalContact M m (t.pullback g) (H.comap g) =
      ((boMaximalContact M m t H).pullback g).reduction := by
  have hA := divisorSeparationSequence_pullback M hN hM t ht hdim hn hnN hm hmax
    g hg hMeg hY hdimY hn' hn'N hmaxY
  have hB := boTail_pullbackReduced M hN hM t ht hdim hn hnN hm hmax hH g hg hMeg hY hdimY
    hn' hn'N hmaxY
  rw [boMaximalContact_eq_boTail, boMaximalContact_eq_boTail,
    ClosedBlowupSequence.reduction_pullback_reduction, ClosedBlowupSequence.reduction_pullback,
    ClosedBlowupSequence.append_pullbackReduced, ← hB, hA]
  exact reduction_append_of_hasNoEmptyBlowups _ (hasNoEmptyBlowups_pullbackReduced _ _) _

/-! ### `𝓑𝓞^H_m` commutes with change of fields -/

/-! ### The projection of a field change -/

private theorem flat_fieldChangeProj (t : FieldBlowupTriple.{u}) {L : Type u} [Field L]
    (σ : t.k →+* L) : Flat (t.fieldChangeProj σ) := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let : Algebra t.k L := σ.toAlgebra
    exact (inferInstance : Module.Flat t.k L)
  exact (inferInstance : MorphismProperty.IsStableUnderBaseChange @Flat).of_isPullback
    (IsPullback.of_hasPullback _ _).flip ‹_›

private theorem surjective_of_isPullback {k L : Type u} [Field k] [Field L] (σ : k →+* L)
    {X Y : Scheme.{u}} {q : Y ⟶ X} {sY : Y ⟶ Spec (.of L)} {sX : X ⟶ Spec (.of k)}
    (sq : IsPullback q sY sX (Spec.map (CommRingCat.ofHom σ))) : Surjective q := by
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) := by
    constructor
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (.of L)) := inferInstance
    haveI : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    exact ⟨y, Subsingleton.elim _ _⟩
  exact (inferInstance : MorphismProperty.IsStableUnderBaseChange @Surjective).of_isPullback
    sq.flip ‹_›

private theorem surjective_fieldChangeProj (t : FieldBlowupTriple.{u}) {L : Type u} [Field L]
    (σ : t.k →+* L) : Surjective (t.fieldChangeProj σ) :=
  surjective_of_isPullback σ (IsPullback.of_hasPullback _ _)

/-- The projection `p : X_L → X`, with source `(t.fieldChange σ).X`. -/
private noncomputable abbrev fcProj (t : FieldBlowupTriple.{u}) {L : Type u} [Field L]
    (σ : t.k →+* L) :
    (t.fieldChange σ).X ⟶ t.X :=
  t.fieldChangeProj σ

/-! ### Field changes of triples -/

/-- A smooth morphism is smooth of some relative dimension near every point of the source. -/
private theorem exists_smoothOfRelativeDimension_nbhd {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (x : X) : ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    letI := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have hQi := (HasRingHomProperty.isLocal_ringHomProperty
    (@SmoothOfRelativeDimension n)).respectsIso
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hQi
  have h : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  refine ⟨V, hx, n, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

/-- Along a base change `q : Y → X` of `Spec L → Spec k`, `X` smooth over `k`, local dimensions
are preserved: `dim_y Y = dim_{q y} X`. -/
private theorem topologicalKrullDimAt_of_isPullback {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (q : Y ⟶ X)
    (sY : Y ⟶ Spec (.of L)) (sq : IsPullback q sY sX (Spec.map (CommRingCat.ofHom σ))) (y : Y) :
    topologicalKrullDimAt Y y = topologicalKrullDimAt X (q y) := by
  obtain ⟨V, hxV, d, hd⟩ := exists_smoothOfRelativeDimension_nbhd sX (q y)
  have sqV : IsPullback (q ∣_ V) ((q ⁻¹ᵁ V).ι ≫ sY) (V.ι ≫ sX)
      (Spec.map (CommRingCat.ofHom σ)) := (isPullback_morphismRestrict q V).paste_vert sq
  have hdL : SmoothOfRelativeDimension d ((q ⁻¹ᵁ V).ι ≫ sY) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback sqV hd
  obtain ⟨zY, hzY⟩ : y ∈ Set.range (q ⁻¹ᵁ V).ι := by rwa [Scheme.Opens.range_ι]
  obtain ⟨zX, hzX⟩ : q y ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
  rw [← hzX, ← hzY, (q ⁻¹ᵁ V).ι.isOpenEmbedding.topologicalKrullDimAt_eq zY,
    V.ι.isOpenEmbedding.topologicalKrullDimAt_eq zX,
    topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field d ((q ⁻¹ᵁ V).ι ≫ sY) zY,
    topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field d (V.ι ≫ sX) zX]

/-- A base change of `Spec L → Spec k` of an equidimensional scheme smooth over `k` is
equidimensional of the same dimension. -/
private theorem equidimensional_of_isPullback {k L : Type u} [Field k] [Field L]
    (σ : k →+* L) {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [Smooth sX] (q : Y ⟶ X)
    (sY : Y ⟶ Spec (.of L)) (sq : IsPullback q sY sX (Spec.map (CommRingCat.ofHom σ)))
    (hX : TopologicalSpace.Equidimensional X) :
    TopologicalSpace.Equidimensional Y ∧ topologicalKrullDim Y = topologicalKrullDim X := by
  haveI : LocallyOfFiniteType sY :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have hgs : Surjective q := surjective_of_isPullback σ sq
  have key : ∀ Z ∈ irreducibleComponents Y, ∀ C ∈ irreducibleComponents X,
      topologicalKrullDim Z = topologicalKrullDim C := fun Z hZ C hC => by
    rw [topologicalKrullDim_eq_topologicalKrullDimAt_genericPoint sY hZ,
      topologicalKrullDimAt_of_isPullback σ sX q sY sq,
      topologicalKrullDimAt_eq_of_mem_irreducibleComponents sX hX _ hC]
  refine ⟨fun Z hZ W hW => ?_, ?_⟩
  · obtain ⟨η⟩ : Nonempty Y := ⟨hZ.1.genericPoint⟩
    have hC := irreducibleComponent_mem_irreducibleComponents (q η)
    rw [key Z hZ _ hC, key W hW _ hC]
  · by_cases hY : Nonempty Y
    · obtain ⟨y⟩ := hY
      have hC := irreducibleComponent_mem_irreducibleComponents (q y)
      rw [topologicalKrullDim_eq_of_forall_components y fun Z hZ => key Z hZ _ hC,
        topologicalKrullDim_eq_of_forall_components (q y) fun D hD => hX D hD _ hC]
    · have hX' : ¬ Nonempty X := fun ⟨x⟩ => hY ⟨(hgs.surj x).choose⟩
      have e1 : irreducibleComponents Y = ∅ :=
        Set.eq_empty_of_forall_notMem fun Z hZ => hY ⟨hZ.1.nonempty.some⟩
      have e2 : irreducibleComponents X = ∅ :=
        Set.eq_empty_of_forall_notMem fun Z hZ => hX' ⟨hZ.1.nonempty.some⟩
      rw [topologicalKrullDim_eq_iSup_irreducibleComponents Y,
        topologicalKrullDim_eq_iSup_irreducibleComponents X, e1, e2]
      simp

private theorem equidimensional_fieldChange_aux {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    TopologicalSpace.Equidimensional (t.fieldChange σ).X ∧
      topologicalKrullDim (t.fieldChange σ).X = topologicalKrullDim t.X := by
  obtain ⟨-, hsm, hlft, -, hequi, -, -⟩ := ht
  haveI := hlft
  haveI := Aux.smooth_of_isSmoothScheme' t.sX hsm
  exact equidimensional_of_isPullback σ t.sX (t.fieldChangeProj σ) (t.fieldChange σ).sX
    (IsPullback.of_hasPullback _ _) hequi

private theorem equidimensional_fieldChange {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    TopologicalSpace.Equidimensional (t.fieldChange σ).X :=
  (equidimensional_fieldChange_aux ht σ).1

private theorem topologicalKrullDim_fieldChange {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    topologicalKrullDim (t.fieldChange σ).X = topologicalKrullDim t.X :=
  (equidimensional_fieldChange_aux ht σ).2

private theorem fieldChange_mem_triples {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) : t.fieldChange σ ∈ triples :=
  mem_triples_iff.2 ⟨fieldChange_mem_sncTriples (mem_sncTriples_of_mem_triples ht) σ,
    equidimensional_fieldChange ht σ⟩

private theorem maxOrder_comap_of_surjective {X Y : Scheme.{u}} (φ : Y ⟶ X) [Surjective φ]
    (I : X.IdealSheafData) (h : ∀ y, multAt (I.comap φ) y = multAt I (φ y)) :
    maxOrder (I.comap φ) = maxOrder I := by
  refine le_antisymm (iSup₂_le fun y _ => ?_) (iSup₂_le fun x _ => ?_)
  · rw [h]
    exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt I z) _ (Set.mem_univ _)
  · obtain ⟨y, rfl⟩ := φ.surjective x
    rw [← h]
    exact le_iSup₂ (f := fun z (_ : z ∈ Set.univ) => multAt (I.comap φ) z) _ (Set.mem_univ _)

private theorem maxOrder_fieldChange {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    maxOrder (t.fieldChange σ).I = maxOrder t.I := by
  obtain ⟨hchar, hsm, hlft, hqc, -, -, -⟩ := ht
  haveI := hlft
  haveI := hqc
  haveI := hchar
  haveI := Aux.smooth_of_isSmoothScheme' t.sX hsm
  haveI := flat_fieldChangeProj t σ
  haveI := surjective_fieldChangeProj t σ
  obtain ⟨hlftL, hqcL⟩ := t.fieldChange_finiteType σ
  haveI := hlftL
  have hsmL : Smooth (t.fieldChange σ).sX :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange @Smooth).of_isPullback
      (IsPullback.of_hasPullback _ _) ‹Smooth t.sX›
  haveI : IsLocallyNoetherian t.X := LocallyOfFiniteType.isLocallyNoetherian t.sX
  haveI : IsLocallyNoetherian (t.fieldChange σ).X :=
    LocallyOfFiniteType.isLocallyNoetherian (t.fieldChange σ).sX
  refine maxOrder_comap_of_surjective (t.fieldChangeProj σ) t.I fun y =>
    MMP.Flips.ResolutionInputs.multAt_comap_eq (t.fieldChangeProj σ)
      (isRegularLocalRing_stalk_of_smooth_over_field t.sX)
      (@isRegularLocalRing_stalk_of_smooth_over_field _ _ _ (t.fieldChange σ).sX hsmL)
      (fun y => isRegularLocalRing_closedFibre_of_isRegular_fiber _ y
        (isRegular_fiber_pullback_fst t.sX σ _)) _ y

/-- The class on which `𝓑𝓓_{n,m,j}` commutes with smooth morphisms and field changes. -/
private abbrev bdClass (N m j : ℕ) : Set FieldBlowupTriple.{u} :=
  {t | t ∈ idealTriplesOfDim (Set.Icc 1 N) m ∧ j < t.E.s}

private theorem fieldChange_mem_bdClass {N m j : ℕ} {t : FieldBlowupTriple.{u}}
    (h : t ∈ bdClass N m j) {L : Type u} [Field L] (σ : t.k →+* L) :
    t.fieldChange σ ∈ bdClass N m j := by
  obtain ⟨⟨ht, ⟨n, hn, hd⟩, hmax⟩, hj⟩ := h
  exact ⟨⟨fieldChange_mem_triples ht σ, ⟨n, hn, (topologicalKrullDim_fieldChange ht σ).trans hd⟩,
    (maxOrder_fieldChange ht σ).le.trans hmax⟩, hj⟩

private theorem equidimensional_of_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (g : Y ≃ₜ X)
    (hX : TopologicalSpace.Equidimensional X) : TopologicalSpace.Equidimensional Y := by
  have hc : ∀ Z ∈ irreducibleComponents Y, g '' Z ∈ irreducibleComponents X ∧
      topologicalKrullDim Z = topologicalKrullDim (g '' Z) := fun Z hZ =>
    ⟨image_mem_irreducibleComponents_of_isPreirreducible_fiber g g.continuous g.isOpenMap
      (fun _ => (Set.subsingleton_singleton.preimage g.injective).isPreirreducible)
      g.surjective hZ, (g.image Z).isHomeomorph.topologicalKrullDim_eq⟩
  intro Z hZ W hW
  rw [(hc Z hZ).2, (hc W hW).2]
  exact hX _ (hc Z hZ).1 _ (hc W hW).1

private theorem topologicalKrullDim_eq_of_iso {X Y : Scheme.{u}} (e : Y ≅ X) :
    topologicalKrullDim Y = topologicalKrullDim X :=
  (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph.topologicalKrullDim_eq

private theorem pullback_iso_mem_triples {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    {Y : Scheme.{u}} (e : Y ≅ t.X) : t.pullback e.hom ∈ triples := by
  haveI : QuasiCompact t.sX := ht.2.2.2.1
  exact mem_triples_iff.2 ⟨pullback_mem_sncTriples (mem_sncTriples_of_mem_triples ht) e.hom,
    equidimensional_of_homeomorph (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e))
      ht.2.2.2.2.1⟩

private theorem pullback_iso_mem_bdClass {N m j : ℕ} {t : FieldBlowupTriple.{u}}
    (h : t ∈ bdClass N m j) {Y : Scheme.{u}} (e : Y ≅ t.X) :
    t.pullback e.hom ∈ bdClass N m j := by
  obtain ⟨⟨ht, ⟨n, hn, hd⟩, hmax⟩, hj⟩ := h
  exact ⟨⟨pullback_iso_mem_triples ht e,
    ⟨n, hn, (topologicalKrullDim_eq_of_iso e).trans hd⟩,
    (maxOrder_comap_of_surjective e.hom t.I
      (multAt_comap_of_isOpenImmersion e.hom t.I)).le.trans hmax⟩,
    hj⟩

/-! ### Pull-backs of blow-up sequences -/

/-- The pull-back of a pull-back is the pull-back along the composite. -/
private theorem pullback_pullback {X W Y : Scheme.{u}} (S : ClosedBlowupSequence X)
    (h : W ⟶ X) (k : Y ⟶ W) : (S.pullback h).pullback k = S.pullback (k ≫ h) := by
  have := ClosedBlowupSequence.pullback_pullback_sigma_heq S h k (k ≫ h) rfl (by simp)
  exact congrArg Sigma.fst (eq_of_heq this)

/-! ### Triples isomorphic to a field change -/

/-- `u` is, up to an isomorphism over `t'.X`, the field change of `t'` along `σ`, with projection
`q : u.X → t'.X`. -/
private def IsFieldChangeVia (t' : FieldBlowupTriple.{u}) {L : Type u} [Field L]
    (σ : t'.k →+* L) (u : FieldBlowupTriple.{u}) (q : u.X ⟶ t'.X) : Prop :=
  ∃ e : u.X ≅ t'.fieldChangeScheme σ, e.hom ≫ t'.fieldChangeProj σ = q ∧
    u = (t'.fieldChange σ).pullback e.hom

/-- `𝓑𝓓` commutes with field changes up to isomorphism. -/
private theorem bdFunctor_pullback_iso_fieldChange {N m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m)
    {t' : FieldBlowupTriple.{u}} (ht' : t' ∈ bdClass N m j) {L : Type u} [Field L]
    (σ : t'.k →+* L) {Y : Scheme.{u}} (e : Y ≅ t'.fieldChangeScheme σ) :
    bdFunctor M (dimNat Y) m j ((t'.fieldChange σ).pullback e.hom) =
      (bdFunctor M (dimNat t'.X) m j t').pullback (e.hom ≫ t'.fieldChangeProj σ) := by
  have hF := fieldChange_mem_bdClass ht' σ
  have hY := pullback_iso_mem_bdClass hF e
  haveI : LocallyOfFiniteType t'.sX := ht'.1.1.2.2.1
  haveI : QuasiCompact t'.sX := ht'.1.1.2.2.2.1
  obtain ⟨hl, hq⟩ := t'.fieldChange_finiteType σ
  haveI := hl
  haveI := hq
  have hs : Smooth e.hom := inferInstance
  have hsu : Surjective e.hom := inferInstance
  have hl2 : LocallyOfFiniteType (e.hom ≫ (t'.fieldChange σ).sX) :=
    MorphismProperty.comp_mem _ _ _ (inferInstance : LocallyOfFiniteType e.hom) hl
  have hq2 : QuasiCompact (e.hom ≫ (t'.fieldChange σ).sX) :=
    MorphismProperty.comp_mem _ _ _ (inferInstance : QuasiCompact e.hom) hq
  have h1 := (commutesWithSmoothOn_bdFunctor (j := j) M hN hM hm).1 (t'.fieldChange σ) hF _ e.hom
    hs hsu hl2 hq2 hY
  have h2 := commutesWithFieldChangeOn_bdFunctor (j := j) M hN hM hm t' ht' L σ hF
  have hdF : dimNat (t'.fieldChange σ).X = dimNat t'.X :=
    dimNat_eq_of_topologicalKrullDim_eq (topologicalKrullDim_fieldChange ht'.1.1 σ)
  have hdY : dimNat Y = dimNat t'.X :=
    (dimNat_eq_of_topologicalKrullDim_eq (topologicalKrullDim_eq_of_iso e)).trans hdF
  dsimp only at h1 h2
  change bdFunctor M (dimNat Y) m j ((t'.fieldChange σ).pullback e.hom) =
    (bdFunctor M (dimNat (t'.fieldChange σ).X) m j (t'.fieldChange σ)).pullback e.hom at h1
  rw [hdY]
  rw [hdY, hdF] at h1
  rw [hdF] at h2
  rw [h1, h2]
  exact pullback_pullback _ _ _

private theorem bdFunctor_eq_pullback_of_isFieldChangeVia {N m j : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m)
    {t' : FieldBlowupTriple.{u}} (ht' : t' ∈ bdClass N m j) {L : Type u} [Field L]
    (σ : t'.k →+* L) {u : FieldBlowupTriple.{u}} {q : u.X ⟶ t'.X}
    (hu : IsFieldChangeVia t' σ u q) :
    bdFunctor M (dimNat u.X) m j u = (bdFunctor M (dimNat t'.X) m j t').pullback q := by
  obtain ⟨e, rfl, hu⟩ := hu
  rw [← bdFunctor_pullback_iso_fieldChange M hN hM hm ht' σ e]
  exact eq_of_heq (bdFunctor_heq_of_eq M _ m j hu)

/-! ### Total transforms under a field change -/

/-- The two component identities of `Kollar.totalTransform_comap_canonicalLift` for a base
change `h` of `Spec L → Spec k`, `X` locally of finite type over `k`. -/
private theorem componentIdentities_of_isPullback {k L : Type u} [Field k] [CharZero k] [Field L]
    (σ : k →+* L) {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of L)) (h : Y ⟶ X)
    (sq : IsPullback sY h (Spec.map (CommRingCat.ofHom σ)) sX)
    (Z : X.IdealSheafData) (E : OrderedDivisor X) :
    componentsOfCodimAtLeastTwo ((Z.comap h).support : Set Y) =
        h ⁻¹' componentsOfCodimAtLeastTwo (Z.support : Set X) ∧
      (⋃ (W : Set Y) (_ : W ∈ componentsOf ((Z.comap h).support : Set Y))
          (_ : W ∉ componentsOf (E.comap h).support), W) =
        h ⁻¹' ⋃ (W : Set X) (_ : W ∈ componentsOf (Z.support : Set X))
          (_ : W ∉ componentsOf E.support), W := by
  haveI : PerfectField k := PerfectField.ofCharZero
  have hh : IsReducedFlatBaseChange h :=
    IsReducedFlatBaseChange.of_isPullback sq (IsReducedFlatBaseChange.specMap σ)
  haveI : Flat h := hh.flat
  haveI : LocallyOfFiniteType sY :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq.flip ‹_›
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  exact ⟨componentsOfCodimAtLeastTwo_comap h Z,
    iUnion_componentsOf_notMem_comap h (Flat.generalizingMap h) E Z⟩

/-- The total transform of an ordered divisor along a smooth blow-up sequence of order `m`
commutes with field change. -/
private theorem orderedTotalTransform_pullback_of_isPullback {k L : Type u} [Field k]
    [CharZero k] [Field L] (σ : k →+* L) (m : ℕ) :
    ∀ {X : Scheme.{u}} (B : ClosedBlowupSequence X) (sX : X ⟶ Spec (.of k))
      (I : X.IdealSheafData) (E : OrderedDivisor X), B.IsOrderMTripleSeq sX I E m →
      ∀ {Y : Scheme.{u}} (h : Y ⟶ X) (sY : Y ⟶ Spec (.of L)),
        IsPullback sY h (Spec.map (CommRingCat.ofHom σ)) sX →
        (B.pullback h).orderedTotalTransform (E.comap h) =
          (B.orderedTotalTransform E).comap (B.pullbackHom h)
  | _, .nil _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons Z B, sX, I, E, hB, Y, h, sY, sq => by
    obtain ⟨hT, -, -, -, -, hB'⟩ := hB
    haveI : LocallyOfFiniteType sX := hT.2.2.1
    haveI : PerfectField k := PerfectField.ofCharZero
    have hh : IsReducedFlatBaseChange h :=
      IsReducedFlatBaseChange.of_isPullback sq (IsReducedFlatBaseChange.specMap σ)
    haveI : Flat h := hh.flat
    obtain ⟨h2, hlast⟩ := componentIdentities_of_isPullback σ sX sY h sq Z E
    have hstep := Kollar.totalTransform_comap_canonicalLift hh E Z h2 hlast
    change (B.pullback (canonicalLift h Z)).orderedTotalTransform
        ((E.comap h).totalTransform (Z.comap h)) =
      (B.orderedTotalTransform (E.totalTransform Z)).comap (B.pullbackHom (canonicalLift h Z))
    rw [← hstep]
    exact orderedTotalTransform_pullback_of_isPullback σ m B _ _ _ hB' (canonicalLift h Z)
      (blowUpToBase (Z.comap h) ≫ sY) ((Kollar.isPullback_canonicalLift_of_flat h Z).paste_horiz sq)

/-- The controlled and total transforms along the field change of a sequence of order `m`. -/
private theorem transforms_fieldChange {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) (m : ℕ) (B : ClosedBlowupSequence t.X)
    (hB : B.HasNoEmptyBlowups) (hBo : B.IsOrderMTripleSeq t.sX t.I t.E m)
    (hBL : (B.pullback (fcProj t σ)).IsOrderMTripleSeq (t.fieldChange σ).sX
      (t.fieldChange σ).I (t.fieldChange σ).E m) :
    (B.pullback (fcProj t σ)).controlledTransform (t.fieldChange σ).I =
        (B.controlledTransform t.I).comap (B.pullbackHom (fcProj t σ)) ∧
      (B.pullback (fcProj t σ)).orderedTotalTransform (t.fieldChange σ).E =
        (B.orderedTotalTransform t.E).comap (B.pullbackHom (fcProj t σ)) := by
  haveI := flat_fieldChangeProj t σ
  haveI := surjective_fieldChangeProj t σ
  haveI : CharZero t.k := ht.1
  have sq2 : IsPullback (t.fieldChangeProj σ) (t.fieldChange σ).sX t.sX
      (Spec.map (CommRingCat.ofHom σ)) := IsPullback.of_hasPullback _ _
  refine ⟨?_, orderedTotalTransform_pullback_of_isPullback σ m B t.sX t.I t.E hBo
    (t.fieldChangeProj σ) (t.fieldChange σ).sX sq2.flip⟩
  have key := Kollar.controlledTransform_pullbackReducedWithHom B (t.fieldChangeProj σ) t.sX
    (t.fieldChange σ).sX t.I (t.fieldChange σ).I t.E (t.fieldChange σ).E m hBo
  rw [Kollar.pullbackReducedWithHom_eq_of_flat_of_surjective B hB] at key
  exact key hBL rfl

/-- A cartesian square `Y → X` over `Spec L → Spec k` exhibits `(Y, q^*I, q⁻¹E)` over `L` as the
field change of `(X, I, E)`. -/
private theorem isFieldChangeVia_of_isPullback (t' : FieldBlowupTriple.{u}) {L : Type u}
    [Field L] (σ : t'.k →+* L) {Y : Scheme.{u}} (q : Y ⟶ t'.X) (sY : Y ⟶ Spec (.of L))
    (sq : IsPullback q sY t'.sX (Spec.map (CommRingCat.ofHom σ))) :
    IsFieldChangeVia t' σ ⟨⟨Y, t'.I.comap q, t'.E.comap q⟩, L, sY⟩ q := by
  refine ⟨sq.isoPullback, sq.isoPullback_hom_fst, ?_⟩
  simp only [FieldBlowupTriple.pullback, FieldBlowupTriple.fieldChange]
  congr 1
  · congr 1
    · exact ((Scheme.IdealSheafData.comap_comp _ _ _).symm.trans
        (congrArg _ sq.isoPullback_hom_fst)).symm
    · simp only [OrderedDivisor.comap]
      congr 1
      funext i
      exact ((Scheme.IdealSheafData.comap_comp _ _ _).symm.trans
        (congrArg _ sq.isoPullback_hom_fst)).symm
  · exact sq.isoPullback_hom_snd.symm

/-- The end of the field change of a sequence of order `m` is the field change of the end. -/
private theorem isFieldChangeVia_endOf {t : FieldBlowupTriple.{u}} (ht : t ∈ triples)
    {L : Type u} [Field L] (σ : t.k →+* L) (m : ℕ) (B : ClosedBlowupSequence t.X)
    (hB : B.HasNoEmptyBlowups) (hBo : B.IsOrderMTripleSeq t.sX t.I t.E m)
    (hBL : (B.pullback (t.fieldChangeProj σ)).IsOrderMTripleSeq (t.fieldChange σ).sX
      (t.fieldChange σ).I (t.fieldChange σ).E m) :
    IsFieldChangeVia (t.endOf B) σ ((t.fieldChange σ).endOf (B.pullback (t.fieldChangeProj σ)))
      (B.pullbackHom (t.fieldChangeProj σ)) := by
  obtain ⟨hI, hE⟩ := transforms_fieldChange ht σ m B hB hBo hBL
  have h := isFieldChangeVia_of_isPullback (t.endOf B) σ _ _
    ((Kollar.isPullback_pullback_toBase_of_flat B (t.fieldChangeProj σ)).flip.paste_vert
      (IsPullback.of_hasPullback _ _))
  simp only [FieldBlowupTriple.endOf] at h ⊢
  rwa [hI, hE]

/-! ### The divisor separation sequence under a field change -/

private theorem divisorSeparationAux_fieldChange {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I ≤ m) {L : Type u} [Field L] (σ : t.k →+* L) :
    ∀ j, j ≤ t.E.s → divisorSeparationAux M m (t.fieldChange σ) j =
      (divisorSeparationAux M m t j).pullback (fcProj t σ) := by
  intro j
  induction j with
  | zero => intro; rfl
  | succ j ih' =>
    intro hj
    have ih := ih' (by omega)
    have htL := fieldChange_mem_triples ht σ
    have hdimL := (topologicalKrullDim_fieldChange ht σ).trans hdim
    have hmaxL : maxOrder (t.fieldChange σ).I ≤ m := (maxOrder_fieldChange ht σ).le.trans hmax
    have hdn : dimNat (t.fieldChange σ).X = dimNat t.X :=
      dimNat_eq_of_topologicalKrullDim_eq (topologicalKrullDim_fieldChange ht σ)
    have hPo := isOrderMTripleSeq_divisorSeparationAux M hN hM t ht hdim hn hnN hm hmax j
      (by omega)
    have hPLo := isOrderMTripleSeq_divisorSeparationAux M hN hM _ htL hdimL hn hnN hm hmaxL j
      (by change j ≤ t.E.s; omega)
    rw [ih] at hPLo
    have hend := isFieldChangeVia_endOf ht σ m _ (hasNoEmptyBlowups_divisorSeparationAux M m t j)
      hPo hPLo
    have hT := ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m _ _ _ _ hPo
    obtain ⟨hd1, hmx1, hs1⟩ := end_of_isOrderMTripleSeq m _ _ t.sX t.I t.E hPo hmax hdim
    have hcls : t.endOf (divisorSeparationAux M m t j) ∈ bdClass N m j :=
      ⟨⟨hT, ⟨n, ⟨hn, hnN⟩, hd1⟩, hmx1⟩, by
        change j < (ClosedBlowupSequence.orderedTotalTransform _ _).s; omega⟩
    have hTL : (t.fieldChange σ).endOf ((divisorSeparationAux M m t j).pullback
        (t.fieldChangeProj σ)) ∈ triples := by
      obtain ⟨e, -, hu⟩ := hend
      rw [hu]
      exact pullback_iso_mem_triples
        (t := (t.endOf (divisorSeparationAux M m t j)).fieldChange σ)
        (fieldChange_mem_triples (t := t.endOf (divisorSeparationAux M m t j)) hT σ) e
    have hbd := bdFunctor_eq_pullback_of_isFieldChangeVia M hN hM hm hcls σ hend
    obtain ⟨hd2, -, -⟩ := end_of_isOrderMTripleSeq m _ _ _ _ _ hPLo hmaxL hdimL
    have hdA : dimNat ((divisorSeparationAux M m t j).pullback (t.fieldChangeProj σ)).target =
        dimNat t.X := dimNat_eq_of_topologicalKrullDim_eq (hd2.trans hdim.symm)
    have hdB : dimNat (divisorSeparationAux M m t j).target = dimNat t.X :=
      dimNat_eq_of_topologicalKrullDim_eq (hd1.trans hdim.symm)
    change dimNat ((divisorSeparationAux M m t j).pullback (t.fieldChangeProj σ)).target = _ at hdA
    rw [divisorSeparationAux, divisorSeparationAux, ih]
    have h1 : IsTriple ((t.fieldChange σ).endOf ((divisorSeparationAux M m t j).pullback
        (fcProj t σ))).sX ((t.fieldChange σ).endOf ((divisorSeparationAux M m t j).pullback
        (fcProj t σ))).I ((t.fieldChange σ).endOf ((divisorSeparationAux M m t j).pullback
        (fcProj t σ))).E := hTL
    have h2 : IsTriple (t.endOf (divisorSeparationAux M m t j)).sX
        (t.endOf (divisorSeparationAux M m t j)).I (t.endOf (divisorSeparationAux M m t j)).E := hT
    rw [if_pos h1, if_pos h2]
    refine Eq.trans ?_ (ClosedBlowupSequence.append_pullback _ _ _).symm
    have e1 : dimNat (t.fieldChange σ).X =
        dimNat ((t.fieldChange σ).endOf ((divisorSeparationAux M m t j).pullback
          (fcProj t σ))).X := hdn.trans hdA.symm
    have e2 : dimNat t.X = dimNat (t.endOf (divisorSeparationAux M m t j)).X := hdB.symm
    rw [e1, e2]
    exact congrArg _ hbd

/-! ### The tail `𝐁_V` of `𝓑𝓞^H_m` -/

open Classical in
/-- The tail of `𝓑𝓞^H_m` on the end `t' = (X', J', E')` of the divisor separation sequence, for
an open `V ⊆ X'`: the extension by closure of `𝓑𝓓_{n,m,0}(V, J'|_V, (H' ∩ V, E'^{s+1} ∩ V, …))`
(empty if `V = ∅` or this is not a triple). -/
private noncomputable def tailSeqOn (M : MarkedFamily.{u}) (n m s : ℕ) (t' : FieldBlowupTriple.{u})
    (H' : t'.X.IdealSheafData) (V : t'.X.Opens) : ClosedBlowupSequence t'.X :=
  let EV : OrderedDivisor V :=
    ⟨t'.E.s - s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (H'.comap V.ι)
      fun i => (t'.E.E ⟨s + i, by omega⟩).comap V.ι⟩
  let tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, EV⟩, t'.k, V.ι ≫ t'.sX⟩
  let BV : ClosedBlowupSequence V :=
    if (V : Set t'.X).Nonempty ∧ IsTriple tV.sX tV.I tV.E then bdFunctor M n m 0 tV
    else .nil _
  BV.extendByClosure V.ι

private theorem boMaximalContact_eq_append (M : MarkedFamily.{u}) (m : ℕ)
    (t : FieldBlowupTriple.{u}) (H : t.X.IdealSheafData) :
    boMaximalContact M m t H = ((divisorSeparationSequence M m t).append
      (tailSeqOn M (dimNat t.X) m t.E.s (t.endOf (divisorSeparationSequence M m t))
        ((divisorSeparationSequence M m t).restrictHom H).ker
        (tailOpen (t.endOf (divisorSeparationSequence M m t)) t.E.s))).reduction :=
  rfl

private theorem tailSeqOn_congr (M : MarkedFamily.{u}) (n m s : ℕ) {Y : Scheme.{u}}
    {I₁ I₂ : Y.IdealSheafData} {E₁ E₂ : OrderedDivisor Y} {k : Type u} [Field k]
    {sY : Y ⟶ Spec (.of k)} (hI : I₁ = I₂) (hE : E₁ = E₂) (K : Y.IdealSheafData)
    {V₁ V₂ : Y.Opens} (hV : V₁ = V₂) :
    tailSeqOn M n m s ⟨⟨Y, I₁, E₁⟩, k, sY⟩ K V₁ = tailSeqOn M n m s ⟨⟨Y, I₂, E₂⟩, k, sY⟩ K V₂ := by
  subst hI hE hV; rfl

/-- `𝓑𝓓` on a triple given as a field change by a cartesian square. -/
private theorem bdFunctor_fieldChange_of_isPullback {N m j n : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m)
    {t' : FieldBlowupTriple.{u}} (ht' : t' ∈ bdClass N m j) (hn : dimNat t'.X = n)
    {L : Type u} [Field L] (σ : t'.k →+* L) {Y : Scheme.{u}} (q : Y ⟶ t'.X)
    (sY : Y ⟶ Spec (.of L)) (sq : IsPullback q sY t'.sX (Spec.map (CommRingCat.ofHom σ))) :
    bdFunctor M n m j ⟨⟨Y, t'.I.comap q, t'.E.comap q⟩, L, sY⟩ =
      (bdFunctor M n m j t').pullback q := by
  have hu := isFieldChangeVia_of_isPullback t' σ q sY sq
  have h := bdFunctor_eq_pullback_of_isFieldChangeVia M hN hM hm ht' σ hu
  obtain ⟨e, he, -⟩ := hu
  have hdY : dimNat Y = dimNat t'.X := dimNat_eq_of_topologicalKrullDim_eq
    ((topologicalKrullDim_eq_of_iso e).trans (topologicalKrullDim_fieldChange ht'.1.1 σ))
  change bdFunctor M (dimNat Y) m j _ = _ at h
  rwa [hdY, hn] at h

/-! ### The tail under a field change -/

/-- The tail of `𝓑𝓞^H_m` commutes with a field change given by a cartesian square. -/
private theorem tailSeqOn_fieldChange {N n m s : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    {t' : FieldBlowupTriple.{u}} (ht' : t' ∈ triples)
    (hdim : topologicalKrullDim t'.X = ((n : ℕ∞) : WithBot ℕ∞)) (hmax : maxOrder t'.I ≤ m)
    {L : Type u} [Field L] (σ : t'.k →+* L) {Y : Scheme.{u}} (q : Y ⟶ t'.X)
    (sY : Y ⟶ Spec (.of L)) (sq : IsPullback q sY t'.sX (Spec.map (CommRingCat.ofHom σ)))
    (K : t'.X.IdealSheafData) (V : t'.X.Opens)
    (hT : (V : Set t'.X).Nonempty → IsTriple (V.ι ≫ t'.sX) (t'.I.comap V.ι)
      (⟨t'.E.s - s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (K.comap V.ι)
        fun i => (t'.E.E ⟨s + i, by omega⟩).comap V.ι⟩ : OrderedDivisor V)) :
    tailSeqOn M n m s ⟨⟨Y, t'.I.comap q, t'.E.comap q⟩, L, sY⟩ (K.comap q) (q ⁻¹ᵁ V) =
      (tailSeqOn M n m s t' K V).pullback q := by
  haveI : CharZero t'.k := ht'.1
  haveI : PerfectField t'.k := PerfectField.ofCharZero
  have hq : IsReducedFlatBaseChange q :=
    IsReducedFlatBaseChange.of_isPullback sq.flip (IsReducedFlatBaseChange.specMap σ)
  haveI : Flat q := hq.flat
  haveI : Surjective q := surjective_of_isPullback σ sq
  haveI : LocallyOfFiniteType t'.sX := ht'.2.2.1
  haveI : QuasiCompact t'.sX := ht'.2.2.2.1
  haveI : IsLocallyNoetherian t'.X := LocallyOfFiniteType.isLocallyNoetherian t'.sX
  haveI : CompactSpace t'.X := QuasiCompact.compactSpace_of_compactSpace t'.sX
  haveI : IsNoetherian t'.X := ⟨⟩
  haveI : LocallyOfFiniteType sY := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    sq ‹_›
  haveI : QuasiCompact sY := MorphismProperty.of_isPullback (P := @QuasiCompact) sq ‹_›
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsNoetherian Y := ⟨⟩
  have sqV := isPullback_morphismRestrict q V
  have sqVL : IsPullback (q ∣_ V) ((q ⁻¹ᵁ V).ι ≫ sY) (V.ι ≫ t'.sX)
      (Spec.map (CommRingCat.ofHom σ)) := sqV.paste_vert sq
  have hIV : (t'.I.comap q).comap (q ⁻¹ᵁ V).ι = (t'.I.comap V.ι).comap (q ∣_ V) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have hc : ∀ J : t'.X.IdealSheafData,
      (J.comap q).comap (q ⁻¹ᵁ V).ι = (J.comap V.ι).comap (q ∣_ V) := fun J => by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have hEV : (⟨(t'.E.comap q).s - s + 1, Fin.cons (α := fun _ => ((q ⁻¹ᵁ V : Y.Opens) :
        Scheme.{u}).IdealSheafData) ((K.comap q).comap (q ⁻¹ᵁ V).ι)
        fun i => ((t'.E.comap q).E ⟨s + i, by omega⟩).comap (q ⁻¹ᵁ V).ι⟩ :
        OrderedDivisor (q ⁻¹ᵁ V)) =
      (⟨t'.E.s - s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (K.comap V.ι)
        fun i => (t'.E.E ⟨s + i, by omega⟩).comap V.ι⟩ : OrderedDivisor V).comap (q ∣_ V) := by
    simp only [OrderedDivisor.comap]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]; exact hc K
    · simp only [Fin.cons_succ]; exact hc _
  unfold tailSeqOn
  dsimp only
  rw [hIV, hEV]
  by_cases hV : (V : Set t'.X).Nonempty
  · have hTV := hT hV
    have dimV : topologicalKrullDim V = ((n : ℕ∞) : WithBot ℕ∞) :=
      (topologicalKrullDim_opens_of_equidimensional t'.sX ht'.2.2.2.2.1 V hV).trans hdim
    have hdnV : dimNat V = n := dimNat_eq_of_eq dimV
    have maxV : maxOrder (t'.I.comap V.ι) ≤ m :=
      (maxOrder_comap_le V.ι t'.I).trans hmax
    let tV : FieldBlowupTriple.{u} := ⟨⟨V, t'.I.comap V.ι, ⟨t'.E.s - s + 1,
        Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (K.comap V.ι)
          fun i => (t'.E.E ⟨s + i, by omega⟩).comap V.ι⟩⟩, t'.k, V.ι ≫ t'.sX⟩
    have hTV' : tV ∈ triples := hTV
    have hclass : tV ∈ bdClass N m 0 :=
      ⟨⟨hTV', ⟨n, ⟨hn, hnN⟩, dimV⟩, maxV⟩, Nat.succ_pos _⟩
    have hbd := bdFunctor_fieldChange_of_isPullback (j := 0) (t' := tV) M hN hM hm hclass hdnV σ
      (q ∣_ V) _ sqVL
    have hred := ClosedBlowupSequence.hasReducedCentres_of_isOrderMTripleSeq m _ _ _ _
      (bdFunctor_isOrderMTripleSeq (j := 0) M hN hM tV hTV' dimV hn hnN hm maxV
        (Nat.succ_pos _)).1
    have hVL : ((q ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := by
      obtain ⟨x, hx⟩ := hV
      obtain ⟨y, rfl⟩ := q.surjective x
      exact ⟨y, hx⟩
    have hTVL : IsTriple ((q ⁻¹ᵁ V).ι ≫ sY) ((t'.I.comap V.ι).comap (q ∣_ V))
        ((⟨t'.E.s - s + 1, Fin.cons (α := fun _ => (V : Scheme.{u}).IdealSheafData) (K.comap V.ι)
          fun i => (t'.E.E ⟨s + i, by omega⟩).comap V.ι⟩ : OrderedDivisor V).comap (q ∣_ V)) := by
      obtain ⟨e, -, hu⟩ := isFieldChangeVia_of_isPullback tV σ (q ∣_ V) _ sqVL
      have := pullback_iso_mem_triples (t := tV.fieldChange σ) (fieldChange_mem_triples hTV' σ) e
      rwa [← hu] at this
    rw [if_pos ⟨hVL, hTVL⟩, if_pos ⟨hV, hTV⟩,
      Kollar.extendByClosure_pullback _ hred V.ι q hq (q ⁻¹ᵁ V).ι (q ∣_ V) sqV.flip]
    exact congrArg (fun B => ClosedBlowupSequence.extendByClosure B (q ⁻¹ᵁ V).ι) hbd
  · have hVL : ¬ ((q ⁻¹ᵁ V : Y.Opens) : Set Y).Nonempty := fun ⟨y, hy⟩ => hV ⟨q y, hy⟩
    rw [if_neg (fun h => hVL h.1), if_neg (fun h => hV h.1)]
    rfl

/-- The open `V` on a triple over `L` whose ordered divisor is `q⁻¹E'` is `q⁻¹V`. -/
private theorem tailOpen_comap_of_eq (s : ℕ) (t' : FieldBlowupTriple.{u}) {L : Type u} [Field L]
    {Y : Scheme.{u}} (q : Y ⟶ t'.X) (sY : Y ⟶ Spec (.of L)) (I : Y.IdealSheafData)
    (E : OrderedDivisor Y) (hE : E = t'.E.comap q) :
    tailOpen ⟨⟨Y, I, E⟩, L, sY⟩ s = q ⁻¹ᵁ tailOpen t' s := by
  subst hE
  ext x
  simp only [tailOpen, ← Finset.sup_univ_eq_iSup]
  change x ∉ ((Finset.univ.sup _ : Closeds Y) : Set Y) ↔
    q x ∉ ((Finset.univ.sup _ : Closeds t'.X) : Set t'.X)
  rw [Closeds.coe_finset_sup, Closeds.coe_finset_sup]
  simp only [Finset.sup_eq_iSup, Finset.mem_univ, iSup_true, Set.iSup_eq_iUnion, Set.mem_iUnion,
    Function.comp_apply, not_exists]
  refine forall_congr' fun i => ?_
  split_ifs
  · change x ∉ (((t'.E.E i).comap q).support : Set Y) ↔ _
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  · rfl

/-! ### The proof -/

/-- **Kollár, Thm. 3.104 Step 2.3 (change of fields).** Let `𝓜` be a marked order-reduction
family on dimensions `0, …, N - 1` (`IsMarkedOrderReductionFamily`), `(X, J, E)` a triple of
dimension `n` with `1 ≤ n ≤ N`, `m ≥ 1` with `maxord J = m`, and `H` an MC-hypersurface for `J`
(`IsMCHypersurface`). For a field extension `σ : k → L` with projection `p : X_L → X`
(`FieldBlowupTriple.fieldChangeProj`),
`boMaximalContact M m (X_L, p^*J, p⁻¹E) (p⁻¹H) = p^* boMaximalContact M m (X, J, E) H`. -/
@[mmp "lem_kr3e_bo_maximal_contact_commutes_field_change"]
public theorem boMaximalContact_fieldChange {N n m : ℕ} (M : MarkedFamily.{u})
    (hN : 1 ≤ N) (hM : IsMarkedOrderReductionFamily 0 (N - 1) M)
    (t : FieldBlowupTriple.{u}) (ht : t ∈ triples)
    (hdim : topologicalKrullDim t.X = ((n : ℕ∞) : WithBot ℕ∞)) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm : 1 ≤ m) (hmax : maxOrder t.I = m) {H : t.X.IdealSheafData}
    (hH : IsMCHypersurface t.sX t.I H)
    {L : Type u} [Field L] (σ : t.k →+* L) :
    boMaximalContact M m (t.fieldChange σ) (H.comap (t.fieldChangeProj σ)) =
      (boMaximalContact M m t H).pullback (t.fieldChangeProj σ) := by
  haveI : Flat (fcProj t σ) := flat_fieldChangeProj t σ
  haveI : Surjective (fcProj t σ) := surjective_fieldChangeProj t σ
  have hdn : dimNat (t.fieldChange σ).X = dimNat t.X :=
    dimNat_eq_of_topologicalKrullDim_eq (topologicalKrullDim_fieldChange ht σ)
  have hdn0 : dimNat t.X = n := dimNat_eq_of_eq hdim
  have hPo := divisorSeparationSequence_isOrderMTripleSeq M hN hM t ht hdim hn hnN hm hmax.le
  have hnoP : (divisorSeparationSequence M m t).HasNoEmptyBlowups :=
    hasNoEmptyBlowups_divisorSeparationAux M m t t.E.s
  have hPL : divisorSeparationSequence M m (t.fieldChange σ) =
      (divisorSeparationSequence M m t).pullback (fcProj t σ) :=
    divisorSeparationAux_fieldChange M hN hM t ht hdim hn hnN hm hmax.le σ t.E.s le_rfl
  have htL := fieldChange_mem_triples ht σ
  have hdimL := (topologicalKrullDim_fieldChange ht σ).trans hdim
  have hmaxL : maxOrder (t.fieldChange σ).I ≤ m := (maxOrder_fieldChange ht σ).le.trans hmax.le
  have hPLo := divisorSeparationSequence_isOrderMTripleSeq M hN hM _ htL hdimL hn hnN hm hmaxL
  rw [hPL] at hPLo
  have htr := ClosedBlowupSequence.isTriple_end_of_isOrderMTripleSeq m _ _ _ _ hPo
  obtain ⟨hd', hmx', -⟩ := end_of_isOrderMTripleSeq m _ _ t.sX t.I t.E hPo hmax.le hdim
  have hA := isTriple_restrict_divisorSeparationSequence M hN hM t ht hdim hn hnN hm hmax hH
  have sq : IsPullback ((divisorSeparationSequence M m t).pullbackHom (fcProj t σ))
      (((divisorSeparationSequence M m t).pullback (fcProj t σ)).toBase ≫ (t.fieldChange σ).sX)
      (t.endOf (divisorSeparationSequence M m t)).sX (Spec.map (CommRingCat.ofHom σ)) :=
    (Kollar.isPullback_pullback_toBase_of_flat _ (t.fieldChangeProj σ)).flip.paste_vert
      (IsPullback.of_hasPullback _ _)
  have hTail := tailSeqOn_fieldChange (s := t.E.s) (t' := t.endOf (divisorSeparationSequence M m t))
    M hN hM hm hn hnN htr hd' hmx' σ _ _ sq
    ((divisorSeparationSequence M m t).restrictHom H).ker
    (tailOpen (t.endOf (divisorSeparationSequence M m t)) t.E.s) hA
  have hK := Kollar.ker_restrictHom_pullback (divisorSeparationSequence M m t) (fcProj t σ) H
  obtain ⟨hI, hE⟩ := transforms_fieldChange ht σ m _ hnoP hPo hPLo
  have hO := tailOpen_comap_of_eq t.E.s (t.endOf (divisorSeparationSequence M m t))
    ((divisorSeparationSequence M m t).pullbackHom (fcProj t σ))
    (((divisorSeparationSequence M m t).pullback (fcProj t σ)).toBase ≫ (t.fieldChange σ).sX)
    (((divisorSeparationSequence M m t).pullback (fcProj t σ)).controlledTransform
      (t.fieldChange σ).I) _ hE
  have hTL : tailSeqOn M (dimNat (t.fieldChange σ).X) m (t.fieldChange σ).E.s
      ((t.fieldChange σ).endOf ((divisorSeparationSequence M m t).pullback (fcProj t σ)))
      (((divisorSeparationSequence M m t).pullback (fcProj t σ)).restrictHom
        (H.comap (fcProj t σ))).ker
      (tailOpen ((t.fieldChange σ).endOf ((divisorSeparationSequence M m t).pullback
        (fcProj t σ))) (t.fieldChange σ).E.s) =
      (tailSeqOn M (dimNat t.X) m t.E.s (t.endOf (divisorSeparationSequence M m t))
        ((divisorSeparationSequence M m t).restrictHom H).ker
        (tailOpen (t.endOf (divisorSeparationSequence M m t)) t.E.s)).pullback
        ((divisorSeparationSequence M m t).pullbackHom (fcProj t σ)) := by
    rw [hK, hdn, hdn0]
    exact (tailSeqOn_congr M n m t.E.s hI hE _ hO).trans hTail
  have hnoT : (tailSeqOn M (dimNat t.X) m t.E.s (t.endOf (divisorSeparationSequence M m t))
      ((divisorSeparationSequence M m t).restrictHom H).ker
      (tailOpen (t.endOf (divisorSeparationSequence M m t)) t.E.s)).HasNoEmptyBlowups := by
    unfold tailSeqOn
    refine hasNoEmptyBlowups_extendByClosure _ _ ?_
    split_ifs
    · exact hasNoEmptyBlowups_bdFunctor ..
    · trivial
  have hno := hasNoEmptyBlowups_append _ _ hnoP hnoT
  rw [boMaximalContact_eq_append, boMaximalContact_eq_append,
    ClosedBlowupSequence.reduction_eq_self hno]
  generalize hG : divisorSeparationSequence M m (t.fieldChange σ) = PL
  obtain rfl : PL = (divisorSeparationSequence M m t).pullback (fcProj t σ) := hG.symm.trans hPL
  refine (congrArg (fun x => (((divisorSeparationSequence M m t).pullback (fcProj t σ)).append
    x).reduction) hTL).trans ?_
  exact (congrArg ClosedBlowupSequence.reduction (ClosedBlowupSequence.append_pullback _ _ _).symm).trans
    (ClosedBlowupSequence.reduction_eq_self
      (ClosedBlowupSequence.hasNoEmptyBlowups_pullback _ hno (fcProj t σ)))

end MMP.Resolution
