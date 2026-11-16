module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.MoveAntitone
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# Junction difficulties are nonincreasing

On a prepared chain of fourfolds, the junctions `(Y_i, Θ_i)` and `(Y_{i+1}, Θ_{i+1})`, `i ≥ i₀`,
are joined by the moves of the `i`-th bridge: a coefficient decrease followed by finitely many
small terminal flips. The difficulty does not increase along any move, hence
`𝒟(Y_{i+1}, Θ_{i+1}) ≤ 𝒟(Y_i, Θ_i)`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.difficulty_succ_le`: the difficulty of the
  junction `(Y_{i+1}, Θ_{i+1})` is at most that of `(Y_i, Θ_i)`.

## Implementation notes

* Difficulties (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`) are
  predicates on their values; the inequality is stated for all values satisfying them.
* The models of a prepared chain are those of index at least `Q.start`, so "for every `i`"
  ranges over `i ≥ Q.start`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold
  MMP.Fourfold.StabilizedSmallKltTail

namespace Proof_lem_oai4_c3_junction_nonincreasing

variable {T : StabilizedSmallKltTail}

/-- Every model of a terminal chain is a pair, projective of dimension four over `ℂ`. -/
private theorem model_facts (C : TerminalChain T) (x : C.ModelIndex) :
    MMP.Mori.IsPair (C.modelStructure x) (C.modelBoundary x) ∧
      MMP.Mori.IsProjectiveVariety ℂ (C.modelStructure x) ∧
      topologicalKrullDim (C.model x) = 4 := by
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨n, hK⟩ := (C.bridge i).P.isCanonicalDivisor
    refine ⟨⟨(C.junction i).isQFactorial.1, n, (C.bridge i).K, hK, ?_⟩,
      (C.junction i).isProjectiveVariety, (C.junction i).dim_eq⟩
    exact isQCartier_of_isQFactorial _ (C.junction i).isQFactorial _
  · have h := (C.bridge i).P.isFourfoldStepDiagram k k.2
    obtain ⟨n, hK⟩ := h.isCanonicalDivisor
    exact ⟨⟨h.isNormalVariety_minus, n, _, hK, h.isQCartier_minus⟩, h.isProjectiveVariety_minus,
      h.dim_minus⟩

/-- On a model of a terminal chain, every valuation has a weight provided it is the valuation of
a proper divisor over the model whose centre has codimension at least two. -/
private theorem exists_isValuationWeight (C : TerminalChain T) (N : ℕ) (x : C.ModelIndex)
    (v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))) :
    ∃ w, (∃ D : MMP.Mori.DivisorOver ℂ (C.modelStructure x), IsProper D.f ∧ v = D.valuation ∧
      2 ≤ codimension D.center) → C.IsValuationWeight N x v w := by
  by_cases hv : ∃ D : MMP.Mori.DivisorOver ℂ (C.modelStructure x), IsProper D.f ∧
      v = D.valuation ∧ 2 ≤ codimension D.center
  · obtain ⟨hpair, -, -⟩ := model_facts C x
    obtain ⟨D, hDp, rfl, hcod⟩ := hv
    obtain ⟨n, K, hK, -⟩ := hpair.2
    obtain ⟨c, hc⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hpair hK D
    exact ⟨_, fun _ => ⟨⟨D, hDp, rfl, hcod⟩, _, ⟨n, D, hDp, rfl,
      MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy hc hDp⟩, rfl⟩⟩
  · exact ⟨0, fun h => absurd h hv⟩

/-- On an integral scheme locally of finite type over a field, the dimension of an irreducible
closed subset plus its codimension is the dimension of the scheme. -/
private lemma topologicalKrullDim_add_codimension {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] (V : IrreducibleCloseds Y) :
    topologicalKrullDim (V : Set Y) + codimension V = topologicalKrullDim Y := by
  obtain ⟨η, hη⟩ := QuasiSober.sober V.isIrreducible V.isClosed
  obtain rfl : IrreducibleCloseds.closureSingleton η = V := SetLike.coe_injective hη
  rw [MMP.Flips.codimension_closureSingleton]
  exact MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY η

/-- On a fourfold, an irreducible surface has codimension two. -/
private lemma codimension_eq_two {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 4) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 2) : codimension V = 2 := by
  have h := topologicalKrullDim_add_codimension sY V
  rw [hV, hdim] at h
  have h' : 2 + codimension V = 4 := WithBot.coe_injective (by simpa using h)
  cases hc : codimension V with
  | top => simp [hc] at h'
  | coe n => rw [hc] at h'; norm_cast at h' ⊢; omega

/-- Every model of a prepared chain has a difficulty. -/
private theorem exists_isDifficulty (Q : PreparedChain T) (x : Q.ModelIndex) :
    ∃ D, Q.IsDifficulty x D := by
  obtain ⟨-, hproj, hdim⟩ := model_facts Q.chain x.1
  have : LocallyOfFiniteType (Q.chain.modelStructure x.1) := hproj.toLocallyOfFiniteType
  choose w hw using exists_isValuationWeight Q.chain Q.scale x.1
  choose d hd using fun S => TerminalChain.exists_isLabelDefault Q.scale S x.1
  have hcentre : ∀ v (V : IrreducibleCloseds (Q.chain.model x.1)),
      MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v V → 2 ≤ codimension V →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v) := by
    rintro v V ⟨D, hDp, rfl, rfl⟩ hcod
    exact hw _ ⟨D, hDp, rfl, hcod⟩
  have hβ : ∀ V : IrreducibleCloseds (Q.chain.model x.1), ∃ β : ℤ,
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 → Q.IsSurfaceBracket x V β := by
    intro V
    choose r hr using fun S => TerminalChain.exists_isLabelBranchNumber S x.1 V
    refine ⟨_, fun hV => ⟨w, r, d, fun v hv => hcentre v V hv ?_, hr, hd, rfl⟩⟩
    rw [codimension_eq_two (Q.chain.modelStructure x.1) hdim hV]
  choose β hβ using hβ
  have hρ : ∀ S : Q.chain.Label, ∃ ρ : ℕ,
      (∃ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), Q.chain.IsLabelCentre S x.1 P ∧
        letI := primeDivisorNormalizationOver (Q.chain.modelStructure x.1) P
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme P),
          ρ = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme P)) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), ¬ Q.chain.IsLabelCentre S x.1 P) ∧
        ρ = 0) := by
    intro S
    by_cases h : ∃ P, Q.chain.IsLabelCentre S x.1 P
    · obtain ⟨P, hP⟩ := h
      letI := primeDivisorNormalizationOver (Q.chain.modelStructure x.1) P
      haveI := isComplexScheme_primeDivisorNormalizationScheme _ hproj P
      exact ⟨_, Or.inl ⟨P, hP, inferInstance, rfl⟩⟩
    · exact ⟨0, Or.inr ⟨fun P hP => h ⟨P, hP⟩, rfl⟩⟩
  choose ρ hρ using hρ
  refine ⟨_, w, β, d, ρ, ?_, hβ, hd, hρ, rfl⟩
  rintro v ⟨Z, hZ, hcod⟩
  exact hcentre v Z hZ (le_trans (by norm_num) hcod)

/-- Along the `i`-th bridge, every model `(V_k, Θ_k)` has difficulty at most that of the
junction `(Y_i, Θ_i)`. -/
private theorem difficulty_bridge_le (Q : PreparedChain T) {i : ℕ} (hi : Q.start ≤ i) {D : ℤ}
    (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D) :
    ∀ (k : ℕ) (hk : k < (Q.chain.bridge i).P.m) (E : ℤ),
      Q.IsDifficulty ⟨⟨i, some ⟨k, hk⟩⟩, hi⟩ E → E ≤ D := by
  intro k
  induction k with
  | zero =>
    intro hk E hE
    refine Q.difficulty_le_of_eq_next (x := ⟨⟨i, none⟩, hi⟩) (y := ⟨⟨i, some ⟨0, hk⟩⟩, hi⟩)
      ?_ hD hE
    simp only [TerminalChain.next, hk, ↓reduceDIte]
  | succ k ih =>
    intro hk E hE
    have hk' : k < (Q.chain.bridge i).P.m := by omega
    obtain ⟨E', hE'⟩ := exists_isDifficulty Q ⟨⟨i, some ⟨k, hk'⟩⟩, hi⟩
    refine le_trans ?_ (ih hk' E' hE')
    refine Q.difficulty_le_of_eq_next (x := ⟨⟨i, some ⟨k, hk'⟩⟩, hi⟩)
      (y := ⟨⟨i, some ⟨k + 1, hk⟩⟩, hi⟩) ?_ hE' hE
    simp only [TerminalChain.next, hk, ↓reduceDIte]

end Proof_lem_oai4_c3_junction_nonincreasing

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

open Proof_lem_oai4_c3_junction_nonincreasing in
/-- On a prepared chain, the difficulty of consecutive junctions does not increase:
for `i ≥ i₀`, if `D = 𝒟(Y_i, Θ_i)` and `D' = 𝒟(Y_{i+1}, Θ_{i+1})` then `D' ≤ D`. -/
@[mmp "lem_oai4_c3_junction_nonincreasing"]
public theorem difficulty_succ_le {i : ℕ} (hi : Q.start ≤ i) {D D' : ℤ}
    (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (hD' : Q.IsDifficulty ⟨⟨i + 1, none⟩, hi.trans (Nat.le_succ i)⟩ D') :
    D' ≤ D := by
  by_cases hm : 0 < (Q.chain.bridge i).P.m
  · have hk : (Q.chain.bridge i).P.m - 1 < (Q.chain.bridge i).P.m := by omega
    obtain ⟨E, hE⟩ := exists_isDifficulty Q ⟨⟨i, some ⟨_, hk⟩⟩, hi⟩
    refine le_trans ?_ (difficulty_bridge_le Q hi hD _ hk E hE)
    refine Q.difficulty_le_of_eq_next (x := ⟨⟨i, some ⟨_, hk⟩⟩, hi⟩) ?_ hE hD'
    have : ¬ (Q.chain.bridge i).P.m - 1 + 1 < (Q.chain.bridge i).P.m := by omega
    simp only [TerminalChain.next, this, ↓reduceDIte]
  · refine Q.difficulty_le_of_eq_next (x := ⟨⟨i, none⟩, hi⟩) ?_ hD hD'
    simp only [TerminalChain.next, hm, ↓reduceDIte]

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
