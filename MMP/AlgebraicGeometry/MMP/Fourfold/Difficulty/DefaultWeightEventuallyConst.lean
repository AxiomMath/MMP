module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainDifficulty
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.DecreasedPair
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.PrimeDivisorPersistence
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.Monotonicity

/-!
# Eventual constancy of the default echo weights along a terminal chain

Let `(p_i, Θ_i)_{i ≥ 0}` be a terminal chain over a stabilized small klt tail of fourfolds.
Each label `S_h` has, at every model `M` of the chain, a coefficient `b_h^M` and a default echo
weight `d_h = d(b_h^M)` at a scale `N`. Along the chain the coefficients are nonincreasing and
lie in `[0, 1)`, so `d_h` is a nonincreasing sequence of natural numbers; it is therefore
eventually constant at the junctions, and on the models of a bridge between `Y_i` and `Y_{i+1}`
every coefficient is its value at `Y_i` or at `Y_{i+1}`. As there are finitely many labels, there
is a single junction `Y_{i₀}` from which every `d_h` is constant on all later models.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.exists_isLabelDefault_const`: for every
  scale `N` there is `i₀` such that every label has the same default echo weight at every
  model `(i, ·)` of the chain with `i₀ ≤ i`.

## Implementation notes

The source fixes `N` to be the admissible scale of the chain; the argument uses only that
`d(b)` is a nondecreasing function of `b` with values in `ℕ`, which holds at every scale, so
the result is stated for every natural number `N`.
-/

@[expose] public section

section

namespace Proof_lem_oai4_difficulty_preparation

open CategoryTheory AlgebraicGeometry MMP.Fourfold MMP.Fourfold.StabilizedSmallKltTail
  MMP.Fourfold.StabilizedSmallKltTail.TerminalChain

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- On a pair `(X, Δ)` over `ℂ`, the log discrepancy of `ord_Q`, `Q` a prime divisor of `X`, is
`1 - coeff_Q Δ`. -/
private theorem isValuationLogDiscrepancy_divisorialValuation {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {Δ : MMP.Mori.QDivisor X}
    (hP : MMP.Mori.IsPair sX Δ) (Q : MMP.Mori.PrimeDivisor X) :
    IsValuationLogDiscrepancy sX Δ Q.divisorialValuation (1 - (Δ.coeff Q : ℝ)) := by
  obtain ⟨hX, n, K, hK, -⟩ := id hP
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK
    (MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hX Q)
  have hneg := ha.eq_neg_coeff_of_ofPrimeDivisor hX
  have h := MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha
    (inferInstanceAs (IsProper (𝟙 X)))
  refine ⟨n, MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hX Q, inferInstanceAs (IsProper (𝟙 X)), ?_, ?_⟩
  · ext g
    exact congrArg Q.divisorialValuation (MMP.Mori.functionFieldMap_id_apply g)
  · rw [hneg] at h
    convert h using 1
    push_cast
    ring

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-- Every boundary coefficient of a model of a terminal chain is less than `1`. -/
private theorem coeff_modelBoundary_lt_one (x : C.ModelIndex)
    (P : MMP.Mori.PrimeDivisor (C.model x)) : (C.modelBoundary x).coeff P < 1 := by
  have hklt := (C.isKltTerminalPair_modelBoundary x).1
  obtain ⟨n, D, -, -, hD⟩ := isValuationLogDiscrepancy_divisorialValuation hklt.1.1.isPair P
  have := hklt.1.2 n D _ hD
  exact_mod_cast (by linarith : ((C.modelBoundary x).coeff P : ℝ) < 1)

/-- The first component of the `n`-th model index is at most `n`. -/
private theorem modelIndexSeq_fst_le (n : ℕ) : (C.modelIndexSeq n).1 ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [modelIndexSeq_succ]
    generalize C.modelIndexSeq n = x at ih
    rcases x with ⟨i, _ | k⟩ <;> simp only [next] <;> split_ifs <;> simp only at ih ⊢ <;> omega

/-- Every model of the chain occurs in the list of its models. -/
private theorem exists_modelIndexSeq_eq (x : C.ModelIndex) : ∃ n, C.modelIndexSeq n = x := by
  have hbridge : ∀ i n, C.modelIndexSeq n = ⟨i, none⟩ → ∀ k : Fin (C.bridge i).P.m,
      C.modelIndexSeq (n + 1 + k.1) = ⟨i, some k⟩ := by
    intro i n hn k
    obtain ⟨k, hk⟩ := k
    induction k with
    | zero =>
      rw [Nat.add_zero, modelIndexSeq_succ, hn]
      simp only [next, hk, ↓reduceDIte]
    | succ k ih =>
      rw [← Nat.add_assoc, modelIndexSeq_succ, ih (by omega)]
      simp only [next, hk, ↓reduceDIte]
  have hjunction : ∀ i, ∃ n, C.modelIndexSeq n = ⟨i, none⟩ := by
    intro i
    induction i with
    | zero => exact ⟨0, rfl⟩
    | succ i ih =>
      obtain ⟨n, hn⟩ := ih
      by_cases h : 0 < (C.bridge i).P.m
      · refine ⟨n + 1 + ((C.bridge i).P.m - 1) + 1, ?_⟩
        rw [modelIndexSeq_succ, hbridge i n hn ⟨(C.bridge i).P.m - 1, by omega⟩]
        have h' : ¬ (C.bridge i).P.m - 1 + 1 < (C.bridge i).P.m := by omega
        simp only [next, h', ↓reduceDIte]
      · refine ⟨n + 1, ?_⟩
        rw [modelIndexSeq_succ, hn]
        simp only [next, h, ↓reduceDIte]
  rcases x with ⟨i, _ | k⟩
  · exact hjunction i
  · obtain ⟨n, hn⟩ := hjunction i
    exact ⟨_, hbridge i n hn k⟩

/-- The centre of `ord_{S_h}` is the centre of the label `S_h`. -/
private theorem isLabelCentre_of_isPrimeDivisorCentre {S : C.Label} {x : C.ModelIndex}
    {Q : MMP.Mori.PrimeDivisor (C.model x)} (h : C.IsPrimeDivisorCentre S.1 x Q) :
    C.IsLabelCentre S x Q := by
  rcases x with ⟨i, _ | k⟩ <;> exact h

private theorem solution :
    ∀ {T : MMP.Fourfold.StabilizedSmallKltTail}
      (C : MMP.Fourfold.StabilizedSmallKltTail.TerminalChain T) (N : ℕ),
      ∃ i₀ : ℕ, ∀ S : C.Label, ∃ d : ℕ,
        ∀ x : C.ModelIndex, i₀ ≤ x.1 → C.IsLabelDefault N S x d := by
  intro T C N
  let e n := C.primeDivisorEquivModel (C.modelIndexSeq n)
  have he n := isPrimeDivisorCentre_iff_primeDivisorEquivModel_eq C (C.modelIndexSeq n)
  let c : C.Label → ℕ → ℚ := fun S n => (C.modelBoundary (C.modelIndexSeq n)).coeff (e n S.1)
  have hanti : ∀ S, Antitone (c S) := fun S n m hnm =>
    C.coeff_modelBoundary_le_of_le S.1 hnm _ _ ((he n S.1 _).mpr rfl) ((he m S.1 _).mpr rfl)
  have hdanti : ∀ S, Antitone fun n => defaultWeight N (c S n) := fun S n m hnm =>
    defaultWeight_le_defaultWeight
      (by exact_mod_cast hanti S hnm) (by exact_mod_cast coeff_modelBoundary_lt_one C _ _)
  choose n hn using fun S => WellFoundedLT.antitone_chain_condition (hdanti S)
  have := C.finite_label
  obtain ⟨i₀, hi₀⟩ := Finite.exists_le n
  refine ⟨i₀, fun S => ⟨defaultWeight N (c S (n S)), fun x hx => ?_⟩⟩
  obtain ⟨m, rfl⟩ := exists_modelIndexSeq_eq C x
  exact ⟨c S m, isLabelCoefficient_of_isLabelCentre
    (isLabelCentre_of_isPrimeDivisorCentre C ((he m S.1 _).mpr rfl)),
    hn S m ((hi₀ S).trans (hx.trans (modelIndexSeq_fst_le C m)))⟩

end Proof_lem_oai4_difficulty_preparation

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.TerminalChain

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-- For every scale `N`, there is an index `i₀` such that for every label `S_h` of the terminal
chain `C`, the default echo weight `d_h` at scale `N` takes one value `d` at every model of the
chain from the junction `Y_{i₀}` on: at every later junction and at every model of every later
bridge. -/
@[mmp "lem_oai4_difficulty_preparation"]
public theorem exists_isLabelDefault_const (N : ℕ) :
    ∃ i₀ : ℕ, ∀ S : C.Label, ∃ d : ℕ,
      ∀ x : C.ModelIndex, i₀ ≤ x.1 → C.IsLabelDefault N S x d :=
  Proof_lem_oai4_difficulty_preparation.solution C N

end MMP.Fourfold.StabilizedSmallKltTail.TerminalChain
