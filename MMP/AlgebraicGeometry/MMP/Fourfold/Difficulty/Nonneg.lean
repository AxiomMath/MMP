module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FourfoldDefs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.DifficultyLocalDeficit
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.VaryingBranchExcess

/-!
# The difficulty is nonnegative at the junctions of a prepared chain

Let `(Y_i, Θ_i)` be a crepant junction of a prepared chain of fourfolds. Its difficulty
`𝒟(Y_i, Θ_i) = ∑_{codim c_Y(v) ≥ 3} w_v + ∑_{dim V = 2} β_V + ∑_h d_h ρ_*(S_h^ν)` is
nonnegative: the brackets of the surfaces can be negative, but their total deficit is bounded by
the contributions of the varying labels and of the deep valuations, so that what remains is the
sum of the terms `d_h ρ_*(S_h^ν)` of the fixed labels.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.nonneg_of_isDifficulty_junction`: the
  difficulty of every junction of a prepared chain is nonnegative.

## Implementation notes

The junction `(Y_i, Θ_i)` is the model `(i, none)` of the prepared chain, for `i` at least the
start of the chain. The difficulty is the predicate
`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty` on its value, so the statement
is that every value `D` of it at a junction satisfies `0 ≤ D`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_prop_oai4_difficulty_i

open MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail
  MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-- A valuation with a centre of codimension at least three is exceptional: the divisor over `X`
witnessing the centre witnesses exceptionality. -/
private lemma isExceptionalValuation_and_iff {k : Type*} [Field k] {X : Scheme} [IsIntegral X]
    (sX : X ⟶ Spec (.of k))
    (v : Valuation X.functionField (WithZero (Multiplicative ℤ))) :
    (MMP.Intersection.IsExceptionalValuation k sX v ∧
      ∃ Z : IrreducibleCloseds X, MMP.Intersection.IsCentre k sX v Z ∧ 3 ≤ codimension Z) ↔
      ∃ Z : IrreducibleCloseds X, MMP.Intersection.IsCentre k sX v Z ∧ 3 ≤ codimension Z := by
  refine and_iff_right_of_imp fun ⟨Z, ⟨E, hE, hv, hZ⟩, h3⟩ => ⟨E, hE, hv, ?_⟩
  exact hZ ▸ le_trans (by norm_num) h3

/-- A sum over the elements satisfying a predicate is at most the sum over all elements. -/
private lemma finsum_cond_le_finsum {α : Type*} [Finite α] (p : α → Prop) (f : α → ℕ) :
    (∑ᶠ (a) (_ : p a), f a) ≤ ∑ᶠ a, f a := by
  classical
  have := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact Finset.sum_le_sum fun a _ => by by_cases h : p a <;> simp [h]

/-- A varying label has a prime divisor as centre at every junction of a prepared chain: without
one its junction coefficient would vanish, contradicting `PreparedChain.pos_of_isVaryingLabel`. -/
private lemma exists_isLabelCentre_of_isVaryingLabel {T : StabilizedSmallKltTail}
    (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i) {S : Q.chain.Label}
    (hS : Q.chain.IsVaryingLabel S) :
    ∃ P : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩), Q.chain.IsLabelCentre S ⟨i, none⟩ P := by
  obtain ⟨b, ⟨P, hP, -⟩ | ⟨-, rfl⟩, hbpos⟩ := Q.pos_of_isVaryingLabel i hi S hS
  · exact ⟨P, hP⟩
  · exact (lt_irrefl _ hbpos).elim

private theorem solution : ∀ {T : MMP.Fourfold.StabilizedSmallKltTail} (Q : PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i) {D : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D), 0 ≤ D := by
  intro T Q i hi D hD
  obtain ⟨w, β, d, ρ, hw, -, hd, hρ, -⟩ := id hD
  choose r hr using fun V => TerminalChain.exists_isVaryingBranchNumber (C := Q.chain) ⟨i, none⟩ V
  obtain ⟨-, -, hle⟩ := hD.le_of_junction hi w hw d ρ hd hρ r fun V _ => hr V
  have hexc := Q.sum_varyingBranchNumber_sub_one_le hi r hr d ρ (fun S _ => hd S)
    (fun S hS => (hρ S).resolve_right fun h =>
      (exists_isLabelCentre_of_isVaryingLabel Q hi hS).elim h.1)
    w fun v hv => hw v hv.2
  simp only [isExceptionalValuation_and_iff] at hexc
  have : Finite Q.chain.Label := TerminalChain.finite_label Q.chain
  have hlab := Nat.cast_le (α := ℤ) |>.2 <|
    finsum_cond_le_finsum Q.chain.IsVaryingLabel fun S => d S * ρ S
  linarith

end Proof_prop_oai4_difficulty_i

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

/-- **Nonnegativity of the difficulty at junctions.** On a prepared chain, the difficulty
`𝒟(Y_i, Θ_i)` of every junction `(Y_i, Θ_i)`, `i ≥ i₀`, is nonnegative. -/
@[mmp "prop_oai4_difficulty_i"]
public theorem nonneg_of_isDifficulty_junction {T : StabilizedSmallKltTail} (Q : PreparedChain T)
    {i : ℕ} (hi : Q.start ≤ i) {D : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D) : 0 ≤ D :=
      by revert T Q i hi D hD; first | exact Proof_prop_oai4_difficulty_i.solution | exact Proof_prop_oai4_difficulty_i.solution _ | exact Proof_prop_oai4_difficulty_i.solution _ _ | exact Proof_prop_oai4_difficulty_i.solution _ _ _ | exact Proof_prop_oai4_difficulty_i.solution _ _ _ _

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

