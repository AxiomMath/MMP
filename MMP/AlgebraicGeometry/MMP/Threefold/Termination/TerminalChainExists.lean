module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldTerminalChain
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.TerminalBridgeExistence
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.CrepantJunctionExistence
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.LowDiscrepancyJunction

/-!
# Stabilized threefold tails admit terminal chains

Let `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` be a stabilized small klt threefold tail with common
low-discrepancy set `I_∞ = I(X_0, B_0)`. Then there is a terminal chain over it: a sequence of
crepant junctions `(p_i, Θ_i)` of `(X_i, B_i)` extracting `I_∞`, together with a terminal bridge
from each junction to the next. The junction `(p_0, Θ_0)` exists because `I_∞` is a finite set of
exceptional valuations with log discrepancy at most one, and each bridge produces the next
junction; the chain is obtained by dependent choice.

## Main results

* `MMP.Fourfold.StabilizedTail.TerminalChain.nonempty`: every stabilized tail admits a terminal
  chain.
-/

section

open CategoryTheory AlgebraicGeometry MMP.Fourfold MMP.Fourfold.StabilizedTail

namespace Proof_prop_mmp_indexc_terminal_chain_exists

/-- A junction of `(X_i, B_i)` extracting exactly `I(X_i, B_i)`. -/
private structure Stage (T : StabilizedTail) (i : ℕ) where
  I : Finset (Valuation (T.X i).functionField (WithZero (Multiplicative ℤ)))
  coe_I : (I : Set _) = lowDiscrepancySet (T.sX i) (T.B i)
  J : CrepantJunction (T.sX i) (T.B i) I

/-- Each stage has a successor stage together with a terminal bridge to it. -/
private theorem exists_next (T : StabilizedTail) {i : ℕ} (S : Stage T i) :
    ∃ S' : Stage T (i + 1), Nonempty (TerminalBridge i S.J S'.J) := by
  obtain ⟨I', J', ⟨b⟩⟩ := exists_terminalBridge S.coe_I S.J
  exact ⟨⟨I', b.coe_target, J'⟩, ⟨b⟩⟩

/-- The initial stage: a junction of `(X_0, B_0)` extracting the finite set `I_∞`. -/
private theorem nonempty_stage_zero (T : StabilizedTail) : Nonempty (Stage T 0) := by
  have hfin := (T.isKltPair 0).finite_lowDiscrepancySet
  obtain ⟨J⟩ := CrepantJunction.nonempty (T.isProjectiveVariety 0) (T.dim_eq 0)
    (T.isKltPair 0).1.nonneg (T.isKltPair 0) (I := hfin.toFinset) (by simp)
  exact ⟨⟨hfin.toFinset, by simp, J⟩⟩

/-- The stages of the chain, built by recursion. -/
private noncomputable def stage (T : StabilizedTail) : ∀ i, Stage T i
  | 0 => (nonempty_stage_zero T).some
  | i + 1 => (exists_next T (stage T i)).choose

private theorem solution : ∀ (T : StabilizedTail), Nonempty (TerminalChain T) := fun T =>
  ⟨⟨fun i => (stage T i).I, fun i => (stage T i).J,
    fun i => (exists_next T (stage T i)).choose_spec.some⟩⟩

end Proof_prop_mmp_indexc_terminal_chain_exists

end

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

namespace StabilizedTail

/-- **Every stabilized tail admits a terminal chain.** For a stabilized small klt threefold tail
`T`, there is a sequence of crepant junctions of the pairs `(X_i, B_i)` extracting `I_∞`, linked
by terminal bridges (`MMP.Fourfold.StabilizedTail.TerminalChain`). -/
@[mmp "prop_mmp_indexc_terminal_chain_exists"]
public theorem TerminalChain.nonempty (T : StabilizedTail) : Nonempty (TerminalChain T) :=
  by revert T; exact Proof_prop_mmp_indexc_terminal_chain_exists.solution

end StabilizedTail

end MMP.Fourfold
