module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.TerminalBridgeExistence
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.CrepantJunctionExistence
public import MMP.AlgebraicGeometry.MMP.Fourfold.LowDiscrepancySetStabilizes
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv

/-!
# Terminal chains exist

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt tail of fourfolds, with stable
low-discrepancy set `I_∞`. Then it admits a terminal chain: a sequence `(p_i, Θ_i)_{i ≥ 0}` of
crepant junctions of `(X_i, B_i)` extracting `I_∞`, together with a terminal bridge from each
`(p_i, Θ_i)` to `(p_{i+1}, Θ_{i+1})`.

The first junction exists because `I_∞` is a finite set of exceptional valuations over `X_0` of
log discrepancy at most one; each further junction and bridge is produced from the previous
junction by `MMP.Fourfold.StabilizedSmallKltTail.exists_terminalBridge`, and dependent choice
assembles the chain.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.nonempty_terminalChain`: every stabilized small klt tail
  admits a `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain`.
-/

@[expose] public section

section

namespace Proof_prop_oai4_terminal_chain

open AlgebraicGeometry CategoryTheory MMP.Mori MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A crepant junction of `(X_i, B_i)` extracting `I_∞`, packaged with its finite set. -/
private abbrev JunctionAt (T : StabilizedSmallKltTail) (i : ℕ) :=
  Σ' (I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))),
    FourfoldCrepantJunction (T.sX i) (T.B i) I ×' (I : Set _) = T.stableLowDiscrepancySetAt i

/-- The first junction: `I_∞ = I_0` is finite and extracted by a crepant junction of
`(X_0, B_0)`. -/
private noncomputable def junctionZero (T : StabilizedSmallKltTail) : JunctionAt T 0 := by
  have hst := T.isStabilizedSmallKltTail
  have heq : T.lowDiscrepancySetAt 0 = T.stableLowDiscrepancySetAt 0 :=
    hst.lowDiscrepancySetAt_eq 0
  have hfin : (T.stableLowDiscrepancySetAt 0).Finite :=
    (StepSequence.finite_stableLowDiscrepancySet_and_exists_lowDiscrepancySetAt_eq _
      hst.isSmallFrom_zero hst.isKlt).1.subset fun η ⟨ξ, hξ, h⟩ => (h : η = ξ) ▸ hξ
  have hD := T.isFourfoldStepDiagram 0
  refine ⟨hfin.toFinset, Classical.choice ?_, by simp⟩
  refine MMP.Fourfold.nonempty_fourfoldCrepantJunction hD.isProjectiveVariety_minus hD.dim_minus
    (fun P => hD.nonneg P) (hst.isKlt 0) ?_
  simp [← heq]

/-- A terminal bridge out of a junction extracting `I_∞`, together with its target junction. -/
private noncomputable def terminalBridgeFrom (T : StabilizedSmallKltTail) (i : ℕ)
    (J : JunctionAt T i) :
    Σ' (I' : Finset (Valuation (T.X (i + 1)).functionField (WithZero (Multiplicative ℤ))))
      (J' : FourfoldCrepantJunction (T.sX (i + 1)) (T.B (i + 1)) I'), TerminalBridge i J.2.1 J' :=
  Classical.choice <| let ⟨I', J', ⟨b⟩⟩ := exists_terminalBridge T i J.2.1 J.2.2; ⟨⟨I', J', b⟩⟩

/-- The junctions of the chain, by recursion: each is the target of a terminal bridge out of
the previous one. -/
private noncomputable def junctionSeq (T : StabilizedSmallKltTail) : ∀ i, JunctionAt T i
  | 0 => junctionZero T
  | i + 1 =>
    let b := terminalBridgeFrom T i (junctionSeq T i)
    ⟨b.1, b.2.1, b.2.2.coe_target⟩

private theorem solution (T : StabilizedSmallKltTail) : Nonempty (TerminalChain T) :=
  ⟨⟨fun i => (junctionSeq T i).1, fun i => (junctionSeq T i).2.1,
    fun i => (terminalBridgeFrom T i (junctionSeq T i)).2.2⟩⟩

end Proof_prop_oai4_terminal_chain

end

namespace MMP.Fourfold.StabilizedSmallKltTail

/-- Every stabilized small klt tail admits a terminal chain. -/
@[mmp "prop_oai4_terminal_chain"]
public theorem nonempty_terminalChain (T : StabilizedSmallKltTail) :
    Nonempty (TerminalChain T) :=
      by revert T; first | exact Proof_prop_oai4_terminal_chain.solution | exact Proof_prop_oai4_terminal_chain.solution _ | exact Proof_prop_oai4_terminal_chain.solution _ _ | exact Proof_prop_oai4_terminal_chain.solution _ _ _ | exact Proof_prop_oai4_terminal_chain.solution _ _ _ _

end MMP.Fourfold.StabilizedSmallKltTail

