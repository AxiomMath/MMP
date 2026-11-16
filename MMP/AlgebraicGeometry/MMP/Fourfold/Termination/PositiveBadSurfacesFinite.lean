module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BadSurface
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.StabilizedTailPreparedChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.JunctionAntitone
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.BadSurfaceStrictDrop
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.TerminalChainExists
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.Nonneg
public import MMP.AlgebraicGeometry.MMP.Fourfold.StabilizedTail.BadSurfacesFinite
public import MMP.AlgebraicGeometry.MMP.Fourfold.BadSurfaceGenericSmooth
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction

/-!
# Positive-side bad surfaces occur finitely often

Let `(X_i, B_i)_{i ≥ 0}` be a stabilized small klt tail of projective complex fourfold pairs with
rational boundary, with step diagrams `X_i → Z_i ← X_{i+1}`. Then only finitely many steps have a
positive-side bad surface, that is, an irreducible surface `V ⊆ W_i⁺ ⊆ X_{i+1}`.

The difficulty of the junctions of a prepared tail of a terminal chain is a nonincreasing
sequence of nonnegative integers, and from some index on it drops strictly at every step that has
a positive-side bad surface.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.finite_setOf_exists_isPositiveBadSurface`: the set of
  indices `i` for which the `i`-th step has a positive-side bad surface is finite.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold
  MMP.Fourfold.StabilizedSmallKltTail

namespace Proof_lem_oai4_c3_finitely_many_positive_bad_steps

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {T : StabilizedSmallKltTail}

/-- Every model of a terminal chain is a pair, projective of dimension four over `ℂ`. -/
private theorem model_facts (C : TerminalChain T) (x : C.ModelIndex) :
    MMP.Mori.IsPair (C.modelStructure x) (C.modelBoundary x) ∧
      MMP.Mori.IsProjectiveVariety ℂ (C.modelStructure x) ∧
      topologicalKrullDim (C.model x) = 4 := by
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨n, hK⟩ := (C.bridge i).P.isCanonicalDivisor
    refine ⟨⟨(C.junction i).isQFactorial.1, n, (C.bridge i).K, hK, ?_⟩, (C.junction i).isProjectiveVariety,
      (C.junction i).dim_eq⟩
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

/-- The local rings at the points of the smooth locus over a field are regular. -/
private lemma isRegularLocalRing_stalk_of_mem_smoothLocus {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of ℂ)) {y : Y} (hy : y ∈ MMP.Mori.smoothLocus sY) :
    IsRegularLocalRing (Y.presheaf.stalk y) := by
  obtain ⟨V, hyV, hV⟩ := MMP.Mori.mem_smoothLocus_iff.1 hy
  haveI : Smooth (V.ι ≫ sY) := hV
  haveI := isRegularLocalRing_stalk_of_smooth_over_field (V.ι ≫ sY) ⟨y, hyV⟩
  exact IsRegularLocalRing.of_ringEquiv (V.stalkIso ⟨y, hyV⟩).commRingCatIsoToRingEquiv

/-- A nonincreasing sequence of nonnegative integers drops strictly only finitely often. -/
private lemma finite_setOf_succ_lt {D : ℕ → ℤ} (h0 : ∀ k, 0 ≤ D k)
    (hD : ∀ k, D (k + 1) ≤ D k) : {k | D (k + 1) < D k}.Finite := by
  have hg : Antitone fun k => (D k).toNat :=
    antitone_nat_of_succ_le fun k => Int.toNat_le_toNat (hD k)
  obtain ⟨m, hm⟩ := WellFoundedLT.antitone_chain_condition hg
  refine (Set.finite_lt_nat m).subset fun k hk => ?_
  by_contra hmk
  have h1 := hm k (not_lt.1 hmk)
  have h2 := hm (k + 1) (by simp at hmk; omega)
  have := h0 k
  have := h0 (k + 1)
  simp only [Set.mem_setOf_eq] at hk
  omega

private theorem solution : ∀ (T : StabilizedSmallKltTail),
    {i : ℕ | ∃ V : IrreducibleCloseds (T.X (i + 1)),
      IsPositiveBadSurface (T.f i) (T.fp i) V}.Finite := by
  intro T
  have hS := T.isStabilizedSmallKltTail
  obtain ⟨C⟩ := T.nonempty_terminalChain
  obtain ⟨Q, -⟩ := C.exists_preparedChain_chain_eq
  obtain ⟨i₁, hmld⟩ := hS.exists_forall_ge_one_lt_minimalLogDiscrepancy
  obtain ⟨i₁', hsm⟩ := hS.exists_forall_ge_genericPoint_mem_smoothLocus
  set n₀ := max (max i₁ i₁') Q.start
  have hstart : ∀ k, Q.start ≤ n₀ + k := fun k => (le_max_right _ _).trans (Nat.le_add_right _ _)
  choose D hD using fun k => exists_isDifficulty Q ⟨⟨n₀ + k, none⟩, hstart k⟩
  have hfin := finite_setOf_succ_lt (fun k => Q.nonneg_of_isDifficulty_junction (hstart k) (hD k))
    fun k => Q.difficulty_succ_le (hstart k) (hD k) (hD (k + 1))
  refine ((Set.finite_lt_nat n₀).union (hfin.image (n₀ + ·))).subset fun i ⟨V, hV⟩ => ?_
  obtain hi | hi := lt_or_ge i n₀
  · exact Or.inl hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hi₁ : i₁ ≤ n₀ + k := by omega
  have hi₁' : i₁' ≤ n₀ + k := by omega
  exact Or.inr ⟨k, Q.difficulty_succ_lt_of_subset_badLocusPlusAt (hstart k) V
    hV.topologicalKrullDim_eq hV.subset
    (isRegularLocalRing_stalk_of_mem_smoothLocus _
      ((hsm _ hi₁').2 V hV.topologicalKrullDim_eq hV.subset))
    ((hmld _ hi₁).2 V hV.topologicalKrullDim_eq hV.subset) (hD k) (hD (k + 1)), rfl⟩

end Proof_lem_oai4_c3_finitely_many_positive_bad_steps

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedSmallKltTail

/-- In a stabilized small klt tail of projective complex fourfold pairs, only finitely many steps
`X_i → Z_i ← X_{i+1}` have a positive-side bad surface `V ⊆ W_i⁺`. -/
@[mmp "lem_oai4_c3_finitely_many_positive_bad_steps"]
public theorem finite_setOf_exists_isPositiveBadSurface (T : StabilizedSmallKltTail) :
    {i : ℕ | ∃ V : IrreducibleCloseds (T.X (i + 1)),
      IsPositiveBadSurface (T.f i) (T.fp i) V}.Finite :=
        by revert T; first | exact Proof_lem_oai4_c3_finitely_many_positive_bad_steps.solution | exact Proof_lem_oai4_c3_finitely_many_positive_bad_steps.solution _ | exact Proof_lem_oai4_c3_finitely_many_positive_bad_steps.solution _ _ | exact Proof_lem_oai4_c3_finitely_many_positive_bad_steps.solution _ _ _ | exact Proof_lem_oai4_c3_finitely_many_positive_bad_steps.solution _ _ _ _

end MMP.Fourfold.StabilizedSmallKltTail

