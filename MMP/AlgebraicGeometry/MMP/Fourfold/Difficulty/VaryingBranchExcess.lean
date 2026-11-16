module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.BadSurface
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.BranchInequality
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PreparedChainTerminal
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Singularities.Terminal.PairSmoothCodimTwo
public import MMP.AlgebraicGeometry.MMP.Fourfold.Echoes
public import MMP.AlgebraicGeometry.Analytic.SmoothHolomorphicCharts

/-!
# The varying branch excess is paid by positive terms

Let `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)` be a crepant junction of a prepared chain of fourfolds,
`i ≥ i₀`, and let `Q ⊆ Y_i` be the varying union, the reduced union of the varying labels on
`Y_i`. Then the excess of the varying branch numbers over the irreducible surfaces of `Q` is
bounded by the positive terms of the difficulty that the varying labels and the valuations with
small centres contribute:
`∑_{V ⊆ Q, dim V = 2} (r_V^var - 1) ≤ ∑_{h varying} d_h ρ_*(S_h^ν) + ∑_{v} w_v(Y_i, Θ_i)`,
the last sum over the normalized divisorial valuations `v` of `ℂ(Y_i)` exceptional over `Y_i`
whose centre has codimension at least three.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.sum_varyingBranchNumber_sub_one_le`: the
  bound.

## Implementation notes

* As for the difficulty, branch numbers, default echo weights and weights are predicates on
  their values, and the inequality is stated for all values satisfying them: `r V = r_V^var`
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsVaryingBranchNumber`), `d S = d_h`
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelDefault`) and `w v = w_v`
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`), at the fixed
  admissible scale of the chain. The divisor cycle rank `ρ S = ρ_*(S_h^ν)` is that of the
  normalization of the centre of the label on `Y_i`, as in
  `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`.
* The varying union is `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.varyingUnion`, and
  `V ⊆ Q` is containment of sets. The sums over surfaces and valuations are finitely supported
  sums `∑ᶠ` (`0` if the support were infinite); the sum over varying labels is finite.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Proof_lem_oai4_c3_varying_branch_excess_bound

open MMP.Fourfold MMP.Mori MMP.Fourfold.StabilizedSmallKltTail

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [CommRing K] [CommRing L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- The valuation of `k(X_i)` corresponding to a valuation of `k(X_0)` is unique. -/
private theorem corresponds_unique (S : StepSequence) {i : ℕ}
    {ξ : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
    {η η' : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))}
    (h : S.Corresponds i ξ η) (h' : S.Corresponds i ξ η') : η = η' := by
  induction i with
  | zero => exact h.trans h'.symm
  | succ i ih =>
    obtain ⟨ζ, hζ, hη⟩ := h
    obtain ⟨ζ', hζ', hη'⟩ := h'
    cases ih hζ hζ'
    haveI := (S.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    have hb := (S.isFourfoldStepDiagram i).isBirationalMorphism_plus
    haveI := hb.isDominant
    exact valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2 (hη.trans hη'.symm)

/-- Distinct valuations of `k(X_0)` correspond to distinct valuations of `k(X_i)`. -/
private theorem corresponds_injective (S : StepSequence) {i : ℕ}
    {ξ ξ' : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
    {η : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))}
    (h : S.Corresponds i ξ η) (h' : S.Corresponds i ξ' η) : ξ = ξ' := by
  induction i with
  | zero => exact h.symm.trans h'
  | succ i ih =>
    obtain ⟨ζ, hζ, hη⟩ := h
    obtain ⟨ζ', hζ', hη'⟩ := h'
    haveI := (S.isFourfoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    have hb := (S.isFourfoldStepDiagram i).isBirationalMorphism_minus
    haveI := hb.isDominant
    have hζζ : ζ = ζ' :=
      valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2 (hη.symm.trans hη')
    subst hζζ
    exact ih hζ hζ'

/-- A prime divisor of a normal variety is determined by its valuation of `k(B)`, for a dominant
morphism `f : Y ⟶ B` inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {Y B : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : MMP.Mori.PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hv : P.divisorialValuation = P'.divisorialValuation := valuation_eq_of_comap_eq hf h
  have hY' : MMP.Mori.IsNormalVariety ℂ (𝟙 Y ≫ sY) := by rwa [Category.id_comp]
  let D : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P⟩
  let D' : MMP.Mori.DivisorOver ℂ sY :=
    ⟨Y, 𝟙 Y, hY', MMP.Mori.isBirationalMorphism_of_isIso (𝟙 Y), P'⟩
  have hD : D.valuation = D'.valuation := by
    change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
    rw [hv]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1 hD)

/-- A label has at most one centre on a junction of a terminal chain. -/
private theorem isLabelCentre_junction_unique {T : StabilizedSmallKltTail}
    (C : T.TerminalChain) {i : ℕ} {S : C.Label} {P P' : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)}
    (h : C.IsLabelCentre S ⟨i, none⟩ P) (h' : C.IsLabelCentre S ⟨i, none⟩ P') : P = P' := by
  obtain ⟨w, hw, hPw⟩ := h
  obtain ⟨w', hw', hPw'⟩ := h'
  cases corresponds_unique T.toStepSequence hw hw'
  have hb := (C.junction i).isBirationalMorphism
  haveI := hb.isDominant
  exact primeDivisor_eq_of_valuationOver_eq (C.junction i).isQFactorial.1 (C.junction i).p
    hb.functionFieldMap_bijective.2 (hPw.trans hPw'.symm)

/-- A prime divisor of a junction of a terminal chain is the centre of at most one label. -/
private theorem label_eq_of_isLabelCentre_junction {T : StabilizedSmallKltTail}
    (C : T.TerminalChain) {i : ℕ} {S S' : C.Label}
    {P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)}
    (h : C.IsLabelCentre S ⟨i, none⟩ P) (h' : C.IsLabelCentre S' ⟨i, none⟩ P) : S = S' := by
  obtain ⟨w, hw, hPw⟩ := h
  obtain ⟨w', hw', hPw'⟩ := h'
  have hww : w = w' := hPw.symm.trans hPw'
  subst hww
  have hl := corresponds_injective T.toStepSequence hw hw'
  have hb := (C.junction 0).isBirationalMorphism
  haveI := hb.isDominant
  exact Subtype.ext (primeDivisor_eq_of_valuationOver_eq (C.junction 0).isQFactorial.1
    (C.junction 0).p hb.functionFieldMap_bijective.2 hl)

/-- At a junction, the label coefficient of a label with centre `P` is the coefficient of the
boundary at `P`. -/
private theorem coeff_eq_of_isLabelCoefficient_junction {T : StabilizedSmallKltTail}
    {C : T.TerminalChain} {i : ℕ} {S : C.Label} {P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)}
    (hP : C.IsLabelCentre S ⟨i, none⟩ P) {b : ℚ} (hb : C.IsLabelCoefficient S ⟨i, none⟩ b) :
    (C.modelBoundary ⟨i, none⟩).coeff P = b := by
  rcases hb with ⟨P', hP', hc⟩ | ⟨hn, -⟩
  · rwa [isLabelCentre_junction_unique C hP hP']
  · exact absurd hP (hn P)

/-- The default echo weight `d(b)` of a coefficient `0 < b < 1` is at least `1` at a positive
scale: its first term is `w(b) = ⌈N b⌉ ≥ 1`. -/
private theorem one_le_defaultWeight {N : ℕ} (hN : 0 < N) {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    1 ≤ defaultWeight N b := by
  have h1 : 1 ≤ difficultyWeight N (1 - ((1 : ℕ) : ℝ) * (1 - b)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, difficultyWeight_eq_zero_iff hN]
    push_cast
    linarith
  refine h1.trans ?_
  have hfin := finite_support_difficultyWeight N hb1
  calc difficultyWeight N (1 - ((1 : ℕ) : ℝ) * (1 - b))
      = ∑ᶠ (_ : 1 ≤ 1), difficultyWeight N (1 - ((1 : ℕ) : ℝ) * (1 - b)) := by
        rw [finsum_eq_if, if_pos le_rfl]
    _ ≤ ∑ᶠ (j : ℕ) (_ : 1 ≤ j), difficultyWeight N (1 - j * (1 - b)) :=
      single_le_finsum (f := fun j : ℕ => ∑ᶠ (_ : 1 ≤ j), difficultyWeight N (1 - j * (1 - b))) 1
        (hfin.subset fun j hj h0 => hj (by
          simp only
          rw [finsum_eq_if]
          split_ifs
          · exact h0
          · rfl))
        (fun _ => Nat.zero_le _)

/-- A finite subset `C` of `S` on which `w ≥ 1` has at most `∑ᶠ v ∈ S, w v` elements, when `w`
has finite support on `S`. -/
private theorem ncard_le_finsum_mem_of_one_le {α : Type*} {C S : Set α} {w : α → ℕ}
    (hC : C.Finite) (hCS : C ⊆ S) (hS : (S ∩ Function.support w).Finite)
    (h1 : ∀ v ∈ C, 1 ≤ w v) : C.ncard ≤ ∑ᶠ v ∈ S, w v := by
  rw [← finsum_mem_add_sdiff' hCS hS, ← finsum_one, finsum_mem_eq_finite_toFinset_sum _ hC,
    finsum_mem_eq_finite_toFinset_sum _ hC]
  exact (Finset.sum_le_sum fun v hv => h1 v (hC.mem_toFinset.1 hv)).trans le_self_add

/-- A finitely supported sum over the elements satisfying `p` is the sum over the subtype. -/
private theorem finsum_cond_eq_sum_subtype {α M : Type*} [AddCommMonoid M] (p : α → Prop)
    [Fintype {a // p a}] (f : α → M) : ∑ᶠ (a) (_ : p a), f a = ∑ a : {a // p a}, f a := by
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]

/-- A valuation whose centre has codimension three is exceptional, with a centre of codimension
at least three. -/
private theorem isExceptionalValuation_and_exists_isCentre_of_codimension_eq_three
    {Y : Scheme.{0}} [IsIntegral Y] {sY : Y ⟶ Spec (.of ℂ)}
    {v : Valuation Y.functionField (WithZero (Multiplicative ℤ))} {Z : IrreducibleCloseds Y}
    (hZ : MMP.Intersection.IsCentre ℂ sY v Z) (hcod : codimension Z = 3) :
    MMP.Intersection.IsExceptionalValuation ℂ sY v ∧
      ∃ Z : IrreducibleCloseds Y, MMP.Intersection.IsCentre ℂ sY v Z ∧ 3 ≤ codimension Z := by
  refine ⟨?_, Z, hZ, hcod.ge⟩
  obtain ⟨D, hD, hv, rfl⟩ := hZ
  exact ⟨D, hD, hv, by rw [hcod]; decide⟩

/-- On a model `(Y, Θ)` of a terminal chain at a positive scale, the valuations with centre of
codimension three and log discrepancy `< 2` are at most as many as the total weight of the
exceptional valuations with centre of codimension at least three: each of them has weight
`w(2 - a) ≥ 1`. -/
private theorem ncard_le_finsum_valuationWeight {T : StabilizedSmallKltTail}
    {C : T.TerminalChain} {N : ℕ} (hN : 0 < N) {x : C.ModelIndex}
    (hproj : MMP.Mori.IsProjectiveVariety ℂ (C.modelStructure x))
    (hQ : IsQFactorial (C.modelStructure x)) (hdim : topologicalKrullDim (C.model x) = 4)
    (hΘ : IsKltTerminalPair (C.modelStructure x) (C.modelBoundary x)) (U : Set (C.model x))
    (w : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v, MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure x) v ∧
        (∃ Z : IrreducibleCloseds (C.model x),
          MMP.Intersection.IsCentre ℂ (C.modelStructure x) v Z ∧ 3 ≤ codimension Z) →
      C.IsValuationWeight N x v (w v)) :
    {v | (∃ Z : IrreducibleCloseds (C.model x),
          MMP.Intersection.IsCentre ℂ (C.modelStructure x) v Z ∧ codimension Z = 3 ∧
            (Z : Set (C.model x)) ⊆ U) ∧
        ∃ a : ℝ, IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a ∧
          a < 2}.ncard ≤
      ∑ᶠ (v) (_ : MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure x) v ∧
          ∃ Z : IrreducibleCloseds (C.model x),
            MMP.Intersection.IsCentre ℂ (C.modelStructure x) v Z ∧ 3 ≤ codimension Z), w v := by
  have hF := IsKltTerminalPair.finite_setOf_three_le_codimension_centre hproj hQ hdim hΘ
    (L := (C.modelBoundary x).support) subset_rfl
  refine ncard_le_finsum_mem_of_one_le (hF.subset ?_) ?_ (hF.subset ?_) ?_
  · rintro v ⟨⟨Z, hZ, hcod, -⟩, a, ⟨n, E, -, hEv, hE⟩, ha2⟩
    exact ⟨(isExceptionalValuation_and_exists_isCentre_of_codimension_eq_three hZ hcod).1,
      ⟨a, ha2, n, E, hEv, hE⟩,
      (isExceptionalValuation_and_exists_isCentre_of_codimension_eq_three hZ hcod).2⟩
  · rintro v ⟨⟨Z, hZ, hcod, -⟩, -⟩
    exact isExceptionalValuation_and_exists_isCentre_of_codimension_eq_three hZ hcod
  · rintro v ⟨hv, hw0⟩
    obtain ⟨a, ⟨n, D, -, hDv, hD⟩, ha⟩ := (hw v hv).exists_eq_zero_iff hN
    exact ⟨hv.1, ⟨a, not_le.1 (mt ha.2 hw0), n, D, hDv, hD⟩, hv.2⟩
  · rintro v ⟨⟨Z, hZ, hcod, -⟩, a, ⟨n, E, -, hEv, hE⟩, ha2⟩
    obtain ⟨a', ⟨n', E', -, hE'v, hE'⟩, ha'⟩ := (hw v
      (isExceptionalValuation_and_exists_isCentre_of_codimension_eq_three hZ hcod)
        ).exists_eq_zero_iff hN
    have haa := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq hE hE'
      (hEv.trans hE'v.symm)
    exact Nat.one_le_iff_ne_zero.2 fun h => by linarith [ha'.1 h]

/-- The centres on a junction of the varying labels of a terminal chain are distinct. -/
private theorem injective_of_isLabelCentre_junction {T : StabilizedSmallKltTail}
    {C : T.TerminalChain} {i : ℕ}
    {P : {S // C.IsVaryingLabel S} → MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)}
    (hP : ∀ S, C.IsLabelCentre S.1 ⟨i, none⟩ (P S)) : Function.Injective P := fun S S' h =>
  Subtype.ext (label_eq_of_isLabelCentre_junction C (hP S) (h ▸ hP S'))

/-- At a junction `Y_i` of a terminal chain, the varying branch number `r_V^var` along an
irreducible surface `V` contained in the varying union is the branch count of the finite set of
centres of the varying labels. -/
private theorem eq_boundaryBranchCount_of_isVaryingBranchNumber {T : StabilizedSmallKltTail}
    {C : T.TerminalChain} {i : ℕ} [Fintype {S // C.IsVaryingLabel S}]
    [DecidableEq (MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩))]
    (hY : MMP.Mori.IsNormalVariety ℂ (C.modelStructure ⟨i, none⟩))
    (hdim : topologicalKrullDim (C.model ⟨i, none⟩) = 4)
    {P : {S // C.IsVaryingLabel S} → MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)}
    (hP : ∀ S, C.IsLabelCentre S.1 ⟨i, none⟩ (P S)) {V : IrreducibleCloseds (C.model ⟨i, none⟩)}
    {r : ℕ} (hr : C.IsVaryingBranchNumber ⟨i, none⟩ V r)
    (hV2 : topologicalKrullDim (V : Set (C.model ⟨i, none⟩)) = 2)
    (hVQ : (V : Set (C.model ⟨i, none⟩)) ⊆ ⋃ D ∈ Finset.univ.image P,
      (D.support : Set (C.model ⟨i, none⟩))) :
    r = boundaryBranchCount (Finset.univ.image P) V := by
  obtain ⟨r', hr', rfl⟩ := hr
  have h1 := (one_le_boundaryBranchCount_and_finite_setOf_one_lt _ hY hdim _).1 V hV2 hVQ
  have hsig := Set.finite_of_ncard_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one h1)
  rw [boundaryBranchCount_eq_sum fun D hD => (hsig.preimage
      (sigma_mk_injective (i := (⟨D, hD⟩ : Finset.univ.image P))).injOn).subset fun _ h => by exact h,
    finsum_cond_eq_sum_subtype, Finset.sum_image (injective_of_isLabelCentre_junction hP).injOn]
  refine Finset.sum_congr rfl fun S _ => ?_
  rcases hr' S.1 S.2 with ⟨P', hP', h⟩ | ⟨hn, -⟩
  · rw [h, isLabelCentre_junction_unique C hP' (hP S)]
  · exact absurd (hP S) (hn _)

private theorem solution : ∀ {T : StabilizedSmallKltTail} (Q : PreparedChain T) {i : ℕ}
    (hi : Q.start ≤ i)
    (r : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) → ℕ)
    (hr : ∀ V, Q.chain.IsVaryingBranchNumber ⟨i, none⟩ V (r V))
    (d ρ : Q.chain.Label → ℕ)
    (hd : ∀ S, Q.chain.IsVaryingLabel S → Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ (d S))
    (hρ : ∀ S, Q.chain.IsVaryingLabel S →
      ∃ P : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩),
        Q.chain.IsLabelCentre S ⟨i, none⟩ P ∧
        letI := primeDivisorNormalizationOver (Q.chain.modelStructure ⟨i, none⟩) P
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme P),
          ρ S = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme P))
    (w : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
        (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
            3 ≤ codimension Z) →
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)),
    ∑ᶠ (V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩))
        (_ : topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 ∧
          (V : Set (Q.chain.model ⟨i, none⟩)) ⊆ Q.chain.varyingUnion i),
        ((r V : ℤ) - 1) ≤
      ((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), d S * ρ S : ℕ) : ℤ) +
        ((∑ᶠ (v) (_ : MMP.Intersection.IsExceptionalValuation ℂ
            (Q.chain.modelStructure ⟨i, none⟩) v ∧
          ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
            MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
              3 ≤ codimension Z), w v : ℕ) : ℤ) := by
  intro T Q i hi r hr d ρ hd hρ w hw
  classical
  obtain ⟨hYproj, hYQ, hYdim, hΘ, hΘ0, -, hcoef⟩ :=
    PreparedChain.isKltTerminalPair_modelBoundary Q ⟨⟨i, none⟩, hi⟩
  haveI : LocallyOfFiniteType (Q.chain.modelStructure ⟨i, none⟩) :=
    hYQ.1.1.toLocallyOfFiniteType
  -- the varying labels and their centres `P S` on `Y_i`; `Qf` is the set of centres
  haveI : Finite Q.chain.Label := Q.chain.finite_label
  let L := {S : Q.chain.Label // Q.chain.IsVaryingLabel S}
  letI : Fintype L := Fintype.ofFinite L
  choose P hP using fun S : L => hρ S.1 S.2
  have hPinj := injective_of_isLabelCentre_junction fun S => (hP S).1
  generalize hQf : Finset.univ.image P = Qf
  have hU : (⋃ D ∈ Qf, (D.support : Set (Q.chain.model ⟨i, none⟩))) =
      Q.chain.varyingUnion i := by
    ext y
    simp only [← hQf, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨D, ⟨S, rfl⟩, hy⟩
      exact ⟨S.1, S.2, P S, (hP S).1, hy⟩
    · rintro ⟨S, hS, P', hP', hy⟩
      refine ⟨P ⟨S, hS⟩, ⟨⟨S, hS⟩, rfl⟩, ?_⟩
      rwa [isLabelCentre_junction_unique Q.chain (hP ⟨S, hS⟩).1 hP']
  -- the coefficient of a varying label is in `(0, 1)`, so its default weight is at least `1`
  have hb : ∀ S : L, 0 < (Q.chain.modelBoundary ⟨i, none⟩).coeff (P S) ∧
      (Q.chain.modelBoundary ⟨i, none⟩).coeff (P S) < 1 := by
    intro S
    obtain ⟨b, hbS, hbpos⟩ := Q.pos_of_isVaryingLabel i hi S.1 S.2
    rw [coeff_eq_of_isLabelCoefficient_junction (hP S).1 hbS]
    exact ⟨hbpos, (hcoef S.1 b hbS).2⟩
  have hd1 : ∀ S : L, 1 ≤ d S.1 := by
    intro S
    obtain ⟨b, hbS, hdb⟩ := hd S.1 S.2
    rw [← coeff_eq_of_isLabelCoefficient_junction (hP S).1 hbS] at hdb
    rw [hdb]
    exact one_le_defaultWeight Q.isAdmissibleScale.pos (by exact_mod_cast (hb S).1)
      (by exact_mod_cast (hb S).2)
  -- `Y_i` is terminal
  have hYt : IsTerminalVariety (Q.chain.modelStructure ⟨i, none⟩) := by
    obtain ⟨-, n, K, hK, -⟩ := hΘ.1.1.isPair
    exact (IsKltTerminalPair.isTerminalVariety_and_three_le_closedsCodimension_singularLocus hΘ
      (isQCartier_of_isQFactorial _ hYQ _) hK (isQCartier_of_isQFactorial _ hYQ _)).1
  have hbr := sum_boundaryBranchCount_sub_one_le (X := T.X i) (Y := Q.chain.model ⟨i, none⟩)
    (T.sX i) (Q.chain.modelStructure ⟨i, none⟩) (T.isFourfoldStepDiagram i).isNormalVariety_minus
    (Q.chain.junction i).isProjectiveVariety_base (Q.chain.junction i).dim_base
    (Q.chain.junction i).p rfl (Q.chain.junction i).isProjectiveMorphism
    (Q.chain.junction i).isBirationalMorphism hYproj hYdim hYQ hYt
    (Q.chain.modelBoundary ⟨i, none⟩) hΘ0 hΘ Qf
    (fun D hD => by
      obtain ⟨S, -, rfl⟩ := Finset.mem_image.mp (hQf ▸ hD)
      exact (hb S).1)
    (by rw [hU]; exact Q.topologicalKrullDim_image_varyingUnion_le hi)
  refine le_trans (le_of_eq ?_) (hbr.trans (add_le_add ?_ (Nat.cast_le.mpr
    (ncard_le_finsum_valuationWeight Q.isAdmissibleScale.pos hYproj hYQ hYdim hΘ _ w hw))))
  · rw [hU]
    refine finsum_congr fun V => finsum_congr fun hV => ?_
    rw [eq_boundaryBranchCount_of_isVaryingBranchNumber hYQ.1 hYdim (fun S => (hP S).1) (hr V)
      hV.1 (by rw [hQf, hU]; exact hV.2), hQf]
  · rw [finsum_cond_eq_sum_subtype, ← hQf, Finset.sum_image hPinj.injOn]
    refine Nat.cast_le.mpr (Finset.sum_le_sum fun S _ => ?_)
    obtain ⟨_, hρS⟩ := (hP S).2
    rw [hρS]
    exact Nat.le_mul_of_pos_left _ (hd1 S)

end Proof_lem_oai4_c3_varying_branch_excess_bound

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

/-- **The varying branch excess is paid by positive terms.** At the junction
`p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)` of a prepared chain, `i ≥ i₀`, with varying union `Q ⊆ Y_i`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.varyingUnion`),
`∑_{V ⊆ Q, dim V = 2} (r_V^var - 1) ≤ ∑_{h varying} d_h ρ_*(S_h^ν) + ∑_v w_v(Y_i, Θ_i)`,
where `r V = r_V^var` is the varying branch number, `d S = d_h` the default echo weight,
`ρ S = ρ_*(S_h^ν)` the divisor cycle rank of the normalization of the label on `Y_i`, and `w v`
the weight of `v`, the last sum running over the normalized divisorial valuations `v` of `ℂ(Y_i)`
exceptional over `Y_i` whose centre has codimension at least three. -/
@[mmp "lem_oai4_c3_varying_branch_excess_bound"]
public theorem sum_varyingBranchNumber_sub_one_le {i : ℕ} (hi : Q.start ≤ i)
    (r : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) → ℕ)
    (hr : ∀ V, Q.chain.IsVaryingBranchNumber ⟨i, none⟩ V (r V))
    (d ρ : Q.chain.Label → ℕ)
    (hd : ∀ S, Q.chain.IsVaryingLabel S → Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ (d S))
    (hρ : ∀ S, Q.chain.IsVaryingLabel S →
      ∃ P : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩),
        Q.chain.IsLabelCentre S ⟨i, none⟩ P ∧
        letI := primeDivisorNormalizationOver (Q.chain.modelStructure ⟨i, none⟩) P
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme P),
          ρ S = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme P))
    (w : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v, MMP.Intersection.IsExceptionalValuation ℂ (Q.chain.modelStructure ⟨i, none⟩) v ∧
        (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
          MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
            3 ≤ codimension Z) →
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v)) :
    ∑ᶠ (V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩))
        (_ : topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 ∧
          (V : Set (Q.chain.model ⟨i, none⟩)) ⊆ Q.chain.varyingUnion i),
        ((r V : ℤ) - 1) ≤
      ((∑ᶠ (S) (_ : Q.chain.IsVaryingLabel S), d S * ρ S : ℕ) : ℤ) +
        ((∑ᶠ (v) (_ : MMP.Intersection.IsExceptionalValuation ℂ
            (Q.chain.modelStructure ⟨i, none⟩) v ∧
          ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
            MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
              3 ≤ codimension Z), w v : ℕ) : ℤ) :=
                by revert i hi r hr d ρ hd hρ w hw; first | exact Proof_lem_oai4_c3_varying_branch_excess_bound.solution | exact Proof_lem_oai4_c3_varying_branch_excess_bound.solution _ | exact Proof_lem_oai4_c3_varying_branch_excess_bound.solution _ _ | exact Proof_lem_oai4_c3_varying_branch_excess_bound.solution _ _ _ | exact Proof_lem_oai4_c3_varying_branch_excess_bound.solution _ _ _ _

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

