module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PreparedChainTerminal
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes

/-!
# Finitely many weighted deep valuations on a model of a prepared chain

Let `(Y, Θ)` be a model of a prepared chain over a stabilized small klt tail of complex
fourfolds, with its fixed admissible scale `N`. Only finitely many normalized divisorial
valuations `v` of `ℂ(Y)` whose centre `c_Y(v)` has codimension at least three in `Y` have nonzero
weight `w_v(Y, Θ) = w(2 - a(v; Y, Θ))`.

## Main results

* `PreparedChain.finite_setOf_isValuationWeight_ne_zero_of_three_le_codimension`: the
  valuations with centre of codimension at least three and nonzero weight form a finite set.

## Implementation notes

* Weights are a predicate on their values
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`), computed at the
  admissible scale of the prepared chain; "`w_v ≠ 0`" reads: some `w ≠ 0` is the weight of `v`.
  The centre of `v` is `MMP.Intersection.IsCentre`, so the set consists of the valuations having
  an irreducible closed centre `V` with `3 ≤ codimension V`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-- On a model `(Y, Θ)` of a prepared chain, only finitely many normalized divisorial valuations
`v` of `ℂ(Y)` with centre `c_Y(v)` of codimension at least three have nonzero weight `w_v`. -/
@[mmp "lem_oai4_c2_codim_three_support_finite"]
public theorem finite_setOf_isValuationWeight_ne_zero_of_three_le_codimension
    {T : StabilizedSmallKltTail} (Q : PreparedChain T) (x : Q.ModelIndex) :
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) |
      (∃ V : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧ 3 ≤ codimension V) ∧
      ∃ w : ℕ, Q.chain.IsValuationWeight Q.scale x.1 v w ∧ w ≠ 0}.Finite := by
  obtain ⟨hproj, hQ, hdim, hΘ, -, -, -⟩ := Q.isKltTerminalPair_modelBoundary x
  refine (IsKltTerminalPair.finite_setOf_three_le_codimension_centre hproj hQ hdim hΘ
    (L := (Q.chain.modelBoundary x.1).support) subset_rfl).subset ?_
  rintro v ⟨⟨V, hV, hcod⟩, w, hw, hw0⟩
  obtain ⟨a, ⟨n, D, -, hD, hlog⟩, ha⟩ := hw.exists_eq_zero_iff Q.isAdmissibleScale.pos
  exact ⟨hw.isExceptionalValuation, ⟨a, not_le.1 (mt ha.2 hw0), n, D, hD, hlog⟩, V, hV, hcod⟩

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

end
