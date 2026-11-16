module
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.Monotonicity

/-!
# Weights do not increase under the moves of a prepared chain

Let `(M_n, Θ^{M_n})_{n ≥ 0}` be the models, in order, of the terminal chain of a prepared chain
over a stabilized small klt tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds, and let
`(M_n, Θ^{M_n}) ⤏ (M_{n+1}, Θ^{M_{n+1}})` be a move of a bridge of the prepared chain: a
coefficient decrease or a flip, with `M_n` a model of the prepared chain. For a normalized
divisorial valuation `v` exceptional over both `M_n` and `M_{n+1}`, the weights satisfy
`w_v(M_{n+1}, Θ^{M_{n+1}}) ≤ w_v(M_n, Θ^{M_n})`: log discrepancies do not decrease along the
chain, and `u ↦ ⌈N max{u, 0}⌉` is nondecreasing.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.le_of_isValuationWeight_succ`: weights do
  not increase under the moves of a prepared chain.

## Implementation notes

* The moves of the bridges are exactly the passages from a model `M_n` of the terminal chain to
  the next one `M_{n+1}` (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.modelIndexSeq`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isCoefficientDecrease_or_isFlipMove`); the
  move is one of the prepared chain when `M_n` lies over a junction `Y_i` with `i ≥ i₀`.
* The valuation `v` is a valuation `ξ` of `k(X_0)`, incarnated on each of the two models as in
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.le_of_isValuationLogDiscrepancy_succ`:
  a valuation of the function field of a junction `Y_i` is `ξ` when its restriction to `k(X_i)`
  through `p_i` is `ξ` carried to `k(X_i)`, and a valuation of the function field of the model
  `V_k` of the `i`-th bridge is `ξ` when its restriction to `k(Z_i)` through `V_k ⟶ Z_i` is `ξ`
  carried to `k(Z_i)` through `k(X_i)` and `f_i`.
* Weights are the predicate `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`
  at the fixed admissible scale of the prepared chain, which already contains that the valuation
  is exceptional over the model; the inequality is stated for every pair of values it admits.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][oai4]
-/

@[expose] public section

open scoped WithZero

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail}

/-- **Weights do not increase under moves.** Let `(M_n, Θ^{M_n}) ⤏ (M_{n+1}, Θ^{M_{n+1}})` be a
move between consecutive models of the terminal chain of a prepared chain `Q` (in particular a
move of a bridge of `Q`). Let `ξ` be a valuation of `k(X_0)`, and `v`, `v'` the
valuations of the function fields of `M_n` and `M_{n+1}` that are `ξ` under the identification
of function fields (through `p_i` and `k(X_i)` for a junction `Y_i`, through `π_k : V_k ⟶ Z_i`
and `k(Z_i)` for a model `V_k` of the `i`-th bridge). If `v` and `v'` are exceptional over their
models, with weights `w = w_v(M_n, Θ^{M_n})` and `w' = w_{v'}(M_{n+1}, Θ^{M_{n+1}})`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight` at the admissible scale),
then `w' ≤ w`. -/
@[mmp "lem_oai4_c3_move_weight_monotone"]
public theorem le_of_isValuationWeight_succ (Q : PreparedChain T) (n : ℕ)
    (ξ : Valuation (T.X 0).functionField ℤᵐ⁰)
    (v : Valuation (Q.chain.model (Q.chain.modelIndexSeq n)).functionField ℤᵐ⁰)
    (v' : Valuation (Q.chain.model (Q.chain.modelIndexSeq (n + 1))).functionField ℤᵐ⁰)
    (hv : TerminalChain.IsIncarnation Q.chain ξ (Q.chain.modelIndexSeq n) v)
    (hv' : TerminalChain.IsIncarnation Q.chain ξ (Q.chain.modelIndexSeq (n + 1)) v')
    {w w' : ℕ}
    (hw : Q.chain.IsValuationWeight Q.scale (Q.chain.modelIndexSeq n) v w)
    (hw' : Q.chain.IsValuationWeight Q.scale (Q.chain.modelIndexSeq (n + 1)) v' w') :
    w' ≤ w := by
  obtain ⟨-, a, ha, rfl⟩ := hw
  obtain ⟨-, a', ha', rfl⟩ := hw'
  exact difficultyWeight_mono _ (sub_le_sub_left
    (TerminalChain.le_of_isValuationLogDiscrepancy_succ Q.chain n ξ v v' hv hv' ha ha') 2)

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
