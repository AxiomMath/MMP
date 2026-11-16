module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PreparedChainTerminal
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes

/-!
# Finitely many weighted valuations at a surface of a model of a prepared chain

Let `(Y, Θ)` be a model of a prepared chain over a stabilized small klt tail of complex
fourfolds, with its fixed admissible scale `N`, and let `V ⊆ Y` be an irreducible surface. Only
finitely many normalized divisorial valuations `v` of `ℂ(Y)` with centre `c_Y(v) = V` have
nonzero weight `w_v(Y, Θ) = w(2 - a(v; Y, Θ))`.

## Main results

* `PreparedChain.finite_setOf_isValuationWeight_ne_zero_of_topologicalKrullDim_eq_two`: the
  valuations with centre a given irreducible surface and nonzero weight form a finite set.

## Implementation notes

* Weights are a predicate on their values
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`), computed at the
  admissible scale of the prepared chain; "`w_v ≠ 0`" reads: some `w ≠ 0` is the weight of `v`.
* An irreducible surface is an irreducible closed subset `V` with `topologicalKrullDim V = 2`,
  and `v` has centre `V` when `MMP.Intersection.IsCentre` holds.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-- On a model `(Y, Θ)` of a prepared chain, for an irreducible surface `V ⊆ Y`, only finitely
many normalized divisorial valuations `v` of `ℂ(Y)` with centre `c_Y(v) = V` have nonzero
weight `w_v`. -/
@[mmp "lem_oai4_c2_surface_support_finite"]
public theorem finite_setOf_isValuationWeight_ne_zero_of_topologicalKrullDim_eq_two
    {T : StabilizedSmallKltTail} (Q : PreparedChain T) (x : Q.ModelIndex)
    (V : IrreducibleCloseds (Q.chain.model x.1))
    (hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2) :
    {v : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) |
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V ∧
      ∃ w : ℕ, Q.chain.IsValuationWeight Q.scale x.1 v w ∧ w ≠ 0}.Finite := by
  obtain ⟨hproj, hQ, hdim, hΘ, -, -, -⟩ := Q.isKltTerminalPair_modelBoundary x
  refine (IsKltTerminalPair.finite_setOf_isCentre_of_hasLogDiscrepancy_lt_two hproj hQ hdim hΘ
    (L := (Q.chain.modelBoundary x.1).support) subset_rfl V hV).subset ?_
  rintro v ⟨hcen, w, hw, hw0⟩
  obtain ⟨a, ⟨n, D, -, hD, hlog⟩, ha⟩ := hw.exists_eq_zero_iff Q.isAdmissibleScale.pos
  exact ⟨hw.isExceptionalValuation, hcen, a, not_le.1 (mt ha.2 hw0), n, D, hD, hlog⟩

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

end
