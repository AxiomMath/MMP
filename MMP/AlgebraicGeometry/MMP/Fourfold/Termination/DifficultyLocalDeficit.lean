module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.FourfoldDefs
public import MMP.AlgebraicGeometry.MMP.Fourfold.BadSurface
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChain.BracketsCofinite
import MMP.AlgebraicGeometry.MMP.Fourfold.Difficulty.SurfaceCeilingError
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagramBranches
import MMP.AlgebraicGeometry.Divisor.NormalizationBranchesCofinite
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# The local deficit of the difficulty at a junction

Let `(Y, Θ)` be the crepant junction `Y_i` of a prepared chain of fourfolds, with fixed
admissible scale `N` and varying union `Q ⊆ Y`. Its difficulty is bounded below by dropping the
surface brackets, at the cost of the excess varying branch numbers:
`𝒟(Y, Θ) ≥ ∑_{codim c_Y(v) ≥ 3} w_v + ∑_h d_h ρ_*(S_h^ν) - ∑_{V ⊆ Q} (r_V^var - 1)`,
the last sum over the irreducible surfaces `V ⊆ Q`. That sum has finitely many nonzero terms, and
all of its terms are nonnegative, i.e. `r_V^var ≥ 1` for every irreducible surface `V ⊆ Q`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty.le_of_junction`: the local
  deficit bound, with the finiteness and nonnegativity of the deficit terms.

## Implementation notes

The weights `w_v`, default echo weights `d_h`, divisor cycle ranks `ρ_h` and varying branch
numbers `r_V^var` are given as functions pinned by their characterising predicates
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`,
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelDefault`,
`MMP.Analytic.divisorCycleRank`,
`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsVaryingBranchNumber`), in the same form as
in `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`. The junction `Y_i` is the
model `(i, none)` of the chain, for `i` at least the start of the prepared chain; irreducible
surfaces are irreducible closed subsets `V` with `topologicalKrullDim V = 2`, and `V ⊆ Q` is
inclusion in `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.varyingUnion`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Fourfold
  MMP.Fourfold.StabilizedSmallKltTail

namespace Proof_lem_oai4_c2_difficulty_local_deficit

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
    have hb := (S.isFourfoldStepDiagram i).isBirationalMorphism_plus
    haveI := hb.isDominant
    exact valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2 (hη.trans hη'.symm)

/-- The valuation of `k(X_0)` corresponding to a valuation of `k(X_i)` is unique. -/
private theorem corresponds_injective (S : StepSequence) {i : ℕ}
    {ξ ξ' : Valuation (S.X 0).functionField (WithZero (Multiplicative ℤ))}
    {η : Valuation (S.X i).functionField (WithZero (Multiplicative ℤ))}
    (h : S.Corresponds i ξ η) (h' : S.Corresponds i ξ' η) : ξ = ξ' := by
  induction i generalizing ξ ξ' with
  | zero => exact h.symm.trans h'
  | succ i ih =>
    obtain ⟨ζ, hζ, hη⟩ := h
    obtain ⟨ζ', hζ', hη'⟩ := h'
    have hb := (S.isFourfoldStepDiagram i).isBirationalMorphism_minus
    haveI := hb.isDominant
    obtain rfl : ζ = ζ' :=
      valuation_eq_of_comap_eq hb.functionFieldMap_bijective.2 (hη.symm.trans hη')
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

/-- A label has at most one centre on a junction. -/
private theorem isLabelCentre_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {S : C.Label} {i : ℕ} {P P' : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)}
    (h : C.IsLabelCentre S ⟨i, none⟩ P) (h' : C.IsLabelCentre S ⟨i, none⟩ P') : P = P' := by
  obtain ⟨w, hw, hPw⟩ := h
  obtain ⟨w', hw', hPw'⟩ := h'
  cases corresponds_unique T.toStepSequence hw hw'
  have hb := (C.junction i).isBirationalMorphism
  haveI := hb.isDominant
  exact primeDivisor_eq_of_valuationOver_eq (C.junction i).isQFactorial.1 (C.junction i).p
    hb.functionFieldMap_bijective.2 (hPw.trans hPw'.symm)

/-- A prime divisor of a junction is the centre of at most one label. -/
private theorem label_eq_of_isLabelCentre {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {S S' : C.Label} {i : ℕ} {P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)}
    (h : C.IsLabelCentre S ⟨i, none⟩ P) (h' : C.IsLabelCentre S' ⟨i, none⟩ P) : S = S' := by
  obtain ⟨w, hw, hPw⟩ := h
  obtain ⟨w', hw', hPw'⟩ := h'
  obtain rfl : w = w' := hPw.symm.trans hPw'
  have hl := corresponds_injective T.toStepSequence hw hw'
  have hb := (C.junction 0).isBirationalMorphism
  haveI := hb.isDominant
  exact Subtype.ext (primeDivisor_eq_of_valuationOver_eq (C.junction 0).isQFactorial.1
    (C.junction 0).p hb.functionFieldMap_bijective.2 hl)

/-- The weight of a valuation on a model is unique. -/
private theorem isValuationWeight_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {N : ℕ} {x : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))} {w w' : ℕ}
    (h : C.IsValuationWeight N x v w) (h' : C.IsValuationWeight N x v w') : w = w' := by
  obtain ⟨-, a, ⟨n, D, -, hD, ha⟩, rfl⟩ := h
  obtain ⟨-, a', ⟨n', D', -, hD', ha'⟩, rfl⟩ := h'
  rw [MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha ha' (hD.trans hD'.symm)]

/-- The label coefficient of a label on a junction is unique. -/
private theorem isLabelCoefficient_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {S : C.Label} {i : ℕ} {b b' : ℚ} (h : C.IsLabelCoefficient S ⟨i, none⟩ b)
    (h' : C.IsLabelCoefficient S ⟨i, none⟩ b') : b = b' := by
  rcases h with ⟨P, hP, rfl⟩ | ⟨hn, rfl⟩ <;> rcases h' with ⟨P', hP', rfl⟩ | ⟨hn', rfl⟩
  · rw [isLabelCentre_unique hP hP']
  · exact absurd hP (hn' P)
  · exact absurd hP' (hn P')
  · rfl

/-- The default echo weight of a label on a junction is unique. -/
private theorem isLabelDefault_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {N : ℕ} {S : C.Label} {i : ℕ} {d d' : ℕ} (h : C.IsLabelDefault N S ⟨i, none⟩ d)
    (h' : C.IsLabelDefault N S ⟨i, none⟩ d') : d = d' := by
  obtain ⟨b, hb, rfl⟩ := h
  obtain ⟨b', hb', rfl⟩ := h'
  rw [isLabelCoefficient_unique hb hb']

/-- The divisor cycle rank of the normalization of a label on a junction is unique. -/
private theorem divisorCycleRank_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {S : C.Label} {i : ℕ} {ρ ρ' : ℕ}
    (h : (∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P ∧
        letI := primeDivisorNormalizationOver (C.modelStructure ⟨i, none⟩) P
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme P),
          ρ = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme P)) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), ¬ C.IsLabelCentre S ⟨i, none⟩ P) ∧
        ρ = 0))
    (h' : (∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P ∧
        letI := primeDivisorNormalizationOver (C.modelStructure ⟨i, none⟩) P
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme P),
          ρ' = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme P)) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), ¬ C.IsLabelCentre S ⟨i, none⟩ P) ∧
        ρ' = 0)) : ρ = ρ' := by
  rcases h with ⟨P, hP, _, rfl⟩ | ⟨hn, rfl⟩ <;> rcases h' with ⟨P', hP', _, rfl⟩ | ⟨hn', rfl⟩
  · obtain rfl := isLabelCentre_unique hP hP'
    rfl
  · exact absurd hP (hn' P)
  · exact absurd hP' (hn P')
  · rfl

/-- An irreducible closed subset of dimension two of a junction has codimension two. -/
private theorem codimension_eq_two {T : StabilizedSmallKltTail} {C : TerminalChain T} {i : ℕ}
    (V : IrreducibleCloseds (C.model ⟨i, none⟩))
    (hV : topologicalKrullDim (V : Set (C.model ⟨i, none⟩)) = 2) : codimension V = 2 := by
  let _ : (C.model ⟨i, none⟩).Over (Spec (.of ℂ)) := ⟨C.modelStructure ⟨i, none⟩⟩
  have : LocallyOfFiniteType ((C.model ⟨i, none⟩) ↘ Spec (.of ℂ)) :=
    (C.junction i).isProjectiveVariety.toLocallyOfFiniteType
  set η : C.model ⟨i, none⟩ := irreducibleSetEquivPoints V
  have hVη : IrreducibleCloseds.closureSingleton η = V :=
    (irreducibleSetEquivPoints (α := C.model ⟨i, none⟩)).symm_apply_apply V
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim ℂ
    (MMP.Intersection.Scheme.Subvariety.ofPoint η)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint] at h
  have hcl : closure ({η} : Set (C.model ⟨i, none⟩)) = V := congrArg SetLike.coe hVη
  rw [← hVη, Stacks.Divisors.PrimeDivisor.codimension_closureSingleton]
  have h2 : topologicalKrullDim (closure ({η} : Set (C.model ⟨i, none⟩))) = 2 := by
    rwa [hcl]
  have h4 : topologicalKrullDim (C.model ⟨i, none⟩) = 4 := (C.junction i).dim_eq
  rw [MMP.Intersection.Scheme.dimension, h2, h4] at h
  have h' : (2 : ℕ∞) + Order.coheight η = 2 + 2 := by
    rw [← WithBot.coe_inj]
    push_cast
    exact h.trans (by norm_num)
  exact (add_right_inj_of_ne_top (ENat.coe_ne_top 2)).1 h'

/-- Only finitely many prime divisors of the normalization `S^ν` of a prime divisor `S` of a
scheme of finite type over a field map onto a given subset. -/
private theorem finite_setOf_image_support_eq {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y)
    (Z : Set Y) :
    {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      primeDivisorNormalization S '' P.support = Z}.Finite := by
  haveI := S.integral
  haveI : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    isFinite_normalization_of_locallyOfFiniteType S.idealSheaf.subscheme
      (S.idealSheaf.subschemeι ≫ sY) _
  haveI : IsFinite (primeDivisorNormalization S) := by
    unfold primeDivisorNormalization
    infer_instance
  set ν := primeDivisorNormalization S
  have hcl : ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S),
      ν '' P.support = Z → closure {ν P.genericPoint} = Z := by
    intro P hP
    rw [← hP, AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← ν.isClosedMap.closure_image_eq_of_continuous ν.continuous, Set.image_singleton]
  rcases Set.eq_empty_or_nonempty {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      ν '' P.support = Z} with he | ⟨P₀, hP₀⟩
  · rw [he]
    exact Set.finite_empty
  refine Set.Finite.of_finite_image ((ν.finite_preimage_singleton (ν P₀.genericPoint)).subset ?_)
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨P, hP, rfl⟩
  have h1 : IsGenericPoint (ν P.genericPoint) Z := hcl P hP
  have h2 : IsGenericPoint (ν P₀.genericPoint) Z := hcl P₀ hP₀
  exact h1.eq h2

/-- A prime divisor `P` of a junction containing an irreducible surface `V` has a branch over
`V`: `r_V(P) ≥ 1`. -/
private theorem one_le_branchNumber {T : StabilizedSmallKltTail} {C : TerminalChain T} {i : ℕ}
    (P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)) (V : IrreducibleCloseds (C.model ⟨i, none⟩))
    (hV : topologicalKrullDim (V : Set (C.model ⟨i, none⟩)) = 2)
    (hVP : (V : Set (C.model ⟨i, none⟩)) ⊆ P.support) :
    1 ≤ branchNumber P (V : Set (C.model ⟨i, none⟩)) := by
  have hc := codimension_eq_two V hV
  haveI : LocallyOfFiniteType (C.modelStructure ⟨i, none⟩) :=
    (C.junction i).isProjectiveVariety.toLocallyOfFiniteType
  haveI : IsVariety ℂ (C.modelStructure ⟨i, none⟩) := (C.junction i).isQFactorial.1.1
  obtain ⟨-, B, hB⟩ := exists_primeDivisor_image_primeDivisorNormalization_eq
    (C.modelStructure ⟨i, none⟩) (fun _ : Unit => P) V hc
    (fun _ hx => Set.mem_iUnion.2 ⟨(), hVP hx⟩)
  exact (Set.ncard_pos (finite_setOf_image_support_eq (C.modelStructure ⟨i, none⟩) P _)).2
    ⟨B, hB⟩

/-- On a junction, the branch number of a label with centre `P` is the branch number of `P`. -/
private theorem isLabelBranchNumber_eq {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {S : C.Label} {i : ℕ} {V : IrreducibleCloseds (C.model ⟨i, none⟩)}
    {P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩)} {r : ℕ} (hP : C.IsLabelCentre S ⟨i, none⟩ P)
    (h : C.IsLabelBranchNumber S ⟨i, none⟩ V r) :
    r = branchNumber P (V : Set (C.model ⟨i, none⟩)) := by
  rcases h with ⟨P', hP', rfl⟩ | ⟨hn, -⟩
  · rw [isLabelCentre_unique hP' hP]
  · exact absurd hP (hn P)

/-- The branch number of a label on a junction is unique. -/
private theorem isLabelBranchNumber_unique {T : StabilizedSmallKltTail} {C : TerminalChain T}
    {S : C.Label} {i : ℕ} {V : IrreducibleCloseds (C.model ⟨i, none⟩)} {r r' : ℕ}
    (h : C.IsLabelBranchNumber S ⟨i, none⟩ V r) (h' : C.IsLabelBranchNumber S ⟨i, none⟩ V r') :
    r = r' := by
  rcases h with ⟨P, hP, rfl⟩ | ⟨hn, rfl⟩
  · exact (isLabelBranchNumber_eq hP h').symm
  · rcases h' with ⟨P', hP', -⟩ | ⟨-, rfl⟩
    · exact absurd hP' (hn P')
    · rfl

/-- The bracket at an irreducible closed subset of a junction is unique. -/
private theorem isSurfaceBracket_unique {T : StabilizedSmallKltTail} {Q : PreparedChain T}
    {i : ℕ} {hi : Q.start ≤ i} {V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩)} {β β' : ℤ}
    (h : Q.IsSurfaceBracket ⟨⟨i, none⟩, hi⟩ V β) (h' : Q.IsSurfaceBracket ⟨⟨i, none⟩, hi⟩ V β') :
    β = β' := by
  obtain ⟨w, r, d, hw, hr, hd, rfl⟩ := h
  obtain ⟨w', r', d', hw', hr', hd', rfl⟩ := h'
  congr 2
  · exact finsum_congr fun v => finsum_congr fun hv => isValuationWeight_unique (hw v hv) (hw' v hv)
  · exact finsum_congr fun S => by
      rw [isLabelBranchNumber_unique (hr S) (hr' S), isLabelDefault_unique (hd S) (hd' S)]

/-- A finite sum of natural numbers that is at least two has a term at least two, or two
distinct nonzero terms. -/
private theorem exists_of_two_le_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : 2 ≤ ∑ i ∈ s, f i) :
    (∃ i ∈ s, 2 ≤ f i) ∨ ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ f i ≠ 0 ∧ f j ≠ 0 := by
  by_contra hc
  obtain ⟨h1, h2⟩ := not_or.1 hc
  by_cases hex : ∃ i ∈ s, f i ≠ 0
  · obtain ⟨i, hi, hfi⟩ := hex
    rw [Finset.sum_eq_single_of_mem i hi fun j hj hji => by
      by_contra hfj
      exact h2 ⟨i, hi, j, hj, Ne.symm hji, hfi, hfj⟩] at h
    exact h1 ⟨i, hi, h⟩
  · rw [Finset.sum_eq_zero fun i hi => by
      by_contra hfi
      exact hex ⟨i, hi, hfi⟩] at h
    omega

/-- An irreducible closed subset of the varying union `Q ⊆ Y_i` lies on a varying label. -/
private theorem exists_isLabelCentre_of_subset_varyingUnion {T : StabilizedSmallKltTail}
    {C : TerminalChain T} {i : ℕ} {V : IrreducibleCloseds (C.model ⟨i, none⟩)}
    (hV : (V : Set (C.model ⟨i, none⟩)) ⊆ C.varyingUnion i) :
    ∃ S, C.IsVaryingLabel S ∧ ∃ P, C.IsLabelCentre S ⟨i, none⟩ P ∧
      (V : Set (C.model ⟨i, none⟩)) ⊆ P.support := by
  have hcl : closure {irreducibleSetEquivPoints V} = (V : Set (C.model ⟨i, none⟩)) :=
    congrArg SetLike.coe ((irreducibleSetEquivPoints (α := C.model ⟨i, none⟩)).symm_apply_apply V)
  obtain ⟨S, hS, P, hP, hmem⟩ := hV (hcl ▸ subset_closure (Set.mem_singleton _))
  refine ⟨S, hS, P, hP, hcl ▸ closure_minimal (Set.singleton_subset_iff.2 hmem) ?_⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact isClosed_closure

/-- The varying branch number as a finite sum over the varying labels. -/
private theorem eq_sum_of_isVaryingBranchNumber {T : StabilizedSmallKltTail} {C : TerminalChain T}
    [Fintype C.Label] [DecidablePred C.IsVaryingLabel] {x : C.ModelIndex}
    {V : IrreducibleCloseds (C.model x)} {r : ℕ} (h : C.IsVaryingBranchNumber x V r) :
    ∃ r' : C.Label → ℕ, (∀ S, C.IsVaryingLabel S → C.IsLabelBranchNumber S x V (r' S)) ∧
      r = ∑ S ∈ Finset.univ.filter C.IsVaryingLabel, r' S := by
  obtain ⟨r', hr', rfl⟩ := h
  exact ⟨r', hr', finsum_cond_eq_sum_of_cond_iff r' fun _ => by simp⟩

/-- An irreducible surface `V` in the varying union `Q ⊆ Y_i` has `r_V^var ≥ 1`. -/
private theorem one_le_of_isVaryingBranchNumber {T : StabilizedSmallKltTail}
    {C : TerminalChain T} {i : ℕ} {V : IrreducibleCloseds (C.model ⟨i, none⟩)} {r : ℕ}
    (hV : topologicalKrullDim (V : Set (C.model ⟨i, none⟩)) = 2)
    (hVQ : (V : Set (C.model ⟨i, none⟩)) ⊆ C.varyingUnion i)
    (hr : C.IsVaryingBranchNumber ⟨i, none⟩ V r) : 1 ≤ r := by
  classical
  haveI : Fintype C.Label := @Fintype.ofFinite _ C.finite_label
  obtain ⟨S, hS, P, hP, hsub⟩ := exists_isLabelCentre_of_subset_varyingUnion hVQ
  obtain ⟨r', hr', rfl⟩ := eq_sum_of_isVaryingBranchNumber hr
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.2 ⟨Finset.mem_univ S, hS⟩))
  rw [isLabelBranchNumber_eq hP (hr' S hS)]
  exact one_le_branchNumber P V hV hsub

/-- Only finitely many irreducible surfaces `V` in the varying union `Q ⊆ Y_i` have
`r_V^var ≠ 1`: each of them carries two distinct branches of the normalizations of the
(finitely many) varying labels, and only finitely many surfaces do. -/
private theorem finite_setOf_isVaryingBranchNumber_ne_one {T : StabilizedSmallKltTail}
    {C : TerminalChain T} {i : ℕ} (r : IrreducibleCloseds (C.model ⟨i, none⟩) → ℕ)
    (hr : ∀ V : IrreducibleCloseds (C.model ⟨i, none⟩),
      topologicalKrullDim (V : Set (C.model ⟨i, none⟩)) = 2 →
        C.IsVaryingBranchNumber ⟨i, none⟩ V (r V)) :
    {V : IrreducibleCloseds (C.model ⟨i, none⟩) |
      topologicalKrullDim (V : Set (C.model ⟨i, none⟩)) = 2 ∧
        (V : Set (C.model ⟨i, none⟩)) ⊆ C.varyingUnion i ∧ r V ≠ 1}.Finite := by
  classical
  haveI : Fintype C.Label := @Fintype.ofFinite _ C.finite_label
  have hnv := (C.junction i).isQFactorial.1
  haveI : LocallyOfFiniteType (C.modelStructure ⟨i, none⟩) := hnv.1.toLocallyOfFiniteType
  haveI : QuasiCompact (C.modelStructure ⟨i, none⟩) := hnv.1.toQuasiCompact
  have hFfin : {P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩) |
      ∃ S, C.IsVaryingLabel S ∧ C.IsLabelCentre S ⟨i, none⟩ P}.Finite :=
    (Set.finite_iUnion fun S : C.Label =>
      (show {P | C.IsLabelCentre S ⟨i, none⟩ P}.Subsingleton from
        fun _ hP _ hP' => isLabelCentre_unique hP hP').finite).subset
      fun _ ⟨S, _, hS⟩ => Set.mem_iUnion.2 ⟨S, hS⟩
  refine (finite_setOf_nontrivial_normalizationBranches (C.modelStructure ⟨i, none⟩)
    hFfin.toFinset).subset ?_
  rintro V ⟨hV, hVQ, hr1⟩
  have h1 := one_le_of_isVaryingBranchNumber hV hVQ (hr V hV)
  obtain ⟨r', hr', hreq⟩ := eq_sum_of_isVaryingBranchNumber (hr V hV)
  have hcen : ∀ S ∈ Finset.univ.filter C.IsVaryingLabel, r' S ≠ 0 →
      ∃ P, C.IsLabelCentre S ⟨i, none⟩ P ∧ P ∈ hFfin.toFinset ∧
        r' S = branchNumber P (V : Set (C.model ⟨i, none⟩)) := by
    intro S hS h0
    have hSv := (Finset.mem_filter.1 hS).2
    rcases hr' S hSv with ⟨P, hP, h⟩ | ⟨-, h⟩
    · exact ⟨P, hP, hFfin.mem_toFinset.2 ⟨S, hSv, hP⟩, h⟩
    · exact absurd h h0
  rcases exists_of_two_le_sum (Finset.univ.filter C.IsVaryingLabel) r' (by omega) with
    ⟨S, hS, hS2⟩ | ⟨S, hS, S', hS', hne, h0, h0'⟩
  · obtain ⟨P, -, hPF, hrP⟩ := hcen S hS (by omega)
    rw [hrP, branchNumber] at hS2
    obtain ⟨B, hB, B', hB', hBB⟩ := (Set.one_lt_ncard
      (finite_setOf_image_support_eq (C.modelStructure ⟨i, none⟩) P _)).1 hS2
    exact ⟨⟨⟨P, hPF⟩, B⟩, hB, ⟨⟨P, hPF⟩, B'⟩, hB', fun h => hBB (eq_of_heq (Sigma.mk.inj h).2)⟩
  · obtain ⟨P, hP, hPF, hrP⟩ := hcen S hS h0
    obtain ⟨P', hP', hP'F, hrP'⟩ := hcen S' hS' h0'
    obtain ⟨B, hB⟩ := Set.nonempty_of_ncard_ne_zero (hrP ▸ h0)
    obtain ⟨B', hB'⟩ := Set.nonempty_of_ncard_ne_zero (hrP' ▸ h0')
    have hPP : P ≠ P' := fun h => hne (label_eq_of_isLabelCentre hP (h ▸ hP'))
    exact ⟨⟨⟨P, hPF⟩, B⟩, hB, ⟨⟨P', hP'F⟩, B'⟩, hB',
      fun h => hPP (congrArg Subtype.val (Sigma.mk.inj h).1)⟩

/-- The ceiling error bound in terms of the bracket: `β_V ≥ -max{r_V^var - 1, 0}` at an
irreducible surface `V`. -/
private theorem neg_max_le_of_isSurfaceBracket {T : StabilizedSmallKltTail} {Q : PreparedChain T}
    {x : Q.ModelIndex} {V : IrreducibleCloseds (Q.chain.model x.1)}
    (hV : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2) {β : ℤ} {rv : ℕ}
    (hβ : Q.IsSurfaceBracket x V β) (hrv : Q.chain.IsVaryingBranchNumber x.1 V rv) :
    -max ((rv : ℤ) - 1) 0 ≤ β := by
  obtain ⟨w, r, d, hw, hr, hd, rfl⟩ := hβ
  exact PreparedChain.neg_max_le_finsum_valuationWeight_sub Q x V hV w r d rv hw hr hd hrv

/-- Summed over the irreducible surfaces of a junction, the brackets are bounded below by minus
the excess varying branch numbers `∑_{V ⊆ Q} (r_V^var - 1)`. -/
private theorem neg_finsum_le_finsum_isSurfaceBracket {T : StabilizedSmallKltTail}
    {Q : PreparedChain T} {i : ℕ} (hi : Q.start ≤ i)
    {β : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) → ℤ}
    (hβ : ∀ V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
      topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 →
        Q.IsSurfaceBracket ⟨⟨i, none⟩, hi⟩ V (β V))
    (r : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) → ℕ)
    (hr : ∀ V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
      topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 →
        Q.chain.IsVaryingBranchNumber ⟨i, none⟩ V (r V)) :
    -∑ᶠ (V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩))
        (_ : topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 ∧
          (V : Set (Q.chain.model ⟨i, none⟩)) ⊆ Q.chain.varyingUnion i), ((r V : ℤ) - 1) ≤
      ∑ᶠ (V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩))
        (_ : topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2), β V := by
  classical
  simp only [finsum_eq_if]
  rw [neg_le_iff_add_nonneg, ← finsum_add_distrib]
  · refine finsum_nonneg fun V => ?_
    by_cases hV : topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2
    · by_cases hVQ : (V : Set (Q.chain.model ⟨i, none⟩)) ⊆ Q.chain.varyingUnion i
      · have h := neg_max_le_of_isSurfaceBracket (x := ⟨⟨i, none⟩, hi⟩) hV (hβ V hV) (hr V hV)
        have := one_le_of_isVaryingBranchNumber hV hVQ (hr V hV)
        rw [max_eq_left (by omega)] at h
        simp only [hV, hVQ, and_self, if_true]
        linarith
      · have h := neg_max_le_of_isSurfaceBracket (x := ⟨⟨i, none⟩, hi⟩) hV (hβ V hV)
          (TerminalChain.isVaryingBranchNumber_zero_of_not_subset hVQ)
        simp only [hV, hVQ, and_false, if_true, if_false]
        norm_num at h
        linarith
    · rw [if_neg hV, if_neg fun h => hV h.1, add_zero]
  · refine (PreparedChain.finite_setOf_not_isSurfaceBracket_zero Q ⟨⟨i, none⟩, hi⟩).subset
      fun V hV => ?_
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hV
    exact ⟨hV.1, fun h0 => hV.2 (isSurfaceBracket_unique (hβ V hV.1) h0)⟩
  · refine (finite_setOf_isVaryingBranchNumber_ne_one r hr).subset fun V hV => ?_
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hV
    exact ⟨hV.1.1, hV.1.2, fun h1 => hV.2 (by omega)⟩

end Proof_lem_oai4_c2_difficulty_local_deficit

end

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

open Proof_lem_oai4_c2_difficulty_local_deficit in
/-- **Local deficit of the difficulty.** Let `Y = Y_i` be a junction of a prepared chain, with
difficulty `D`, weights `w_v` of the valuations with centre of codimension at least three,
default echo weights `d_h`, divisor cycle ranks `ρ_h = ρ_*(S_h^ν)` and varying branch numbers
`r_V^var`. Then the varying branch number is at least `1` at every irreducible surface `V`
contained in the varying union `Q`, it is different from `1` at only finitely many of them, and
`D ≥ ∑_{codim c_Y(v) ≥ 3} w_v + ∑_h d_h ρ_h - ∑_{V ⊆ Q} (r_V^var - 1)`. -/
@[mmp "lem_oai4_c2_difficulty_local_deficit"]
public theorem IsDifficulty.le_of_junction {T : StabilizedSmallKltTail} {Q : PreparedChain T}
    {i : ℕ} (hi : Q.start ≤ i) {D : ℤ} (hD : Q.IsDifficulty ⟨⟨i, none⟩, hi⟩ D)
    (w : Valuation (Q.chain.model ⟨i, none⟩).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (hw : ∀ v, (∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          3 ≤ codimension Z) →
      Q.chain.IsValuationWeight Q.scale ⟨i, none⟩ v (w v))
    (d ρ : Q.chain.Label → ℕ) (hd : ∀ S, Q.chain.IsLabelDefault Q.scale S ⟨i, none⟩ (d S))
    (hρ : ∀ S, (∃ P : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩),
        Q.chain.IsLabelCentre S ⟨i, none⟩ P ∧
        letI := primeDivisorNormalizationOver (Q.chain.modelStructure ⟨i, none⟩) P
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme P),
          ρ S = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme P)) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (Q.chain.model ⟨i, none⟩),
          ¬ Q.chain.IsLabelCentre S ⟨i, none⟩ P) ∧ ρ S = 0))
    (r : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) → ℕ)
    (hr : ∀ V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
      topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 →
        Q.chain.IsVaryingBranchNumber ⟨i, none⟩ V (r V)) :
    (∀ V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
      topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 →
        (V : Set (Q.chain.model ⟨i, none⟩)) ⊆ Q.chain.varyingUnion i → 1 ≤ r V) ∧
    {V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩) |
      topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 ∧
        (V : Set (Q.chain.model ⟨i, none⟩)) ⊆ Q.chain.varyingUnion i ∧ r V ≠ 1}.Finite ∧
    ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model ⟨i, none⟩),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure ⟨i, none⟩) v Z ∧
          3 ≤ codimension Z), w v : ℕ) : ℤ) +
      ((∑ᶠ S, d S * ρ S : ℕ) : ℤ) -
      ∑ᶠ (V : IrreducibleCloseds (Q.chain.model ⟨i, none⟩))
        (_ : topologicalKrullDim (V : Set (Q.chain.model ⟨i, none⟩)) = 2 ∧
          (V : Set (Q.chain.model ⟨i, none⟩)) ⊆ Q.chain.varyingUnion i), ((r V : ℤ) - 1) ≤ D := by
  refine ⟨fun V hV hVQ => one_le_of_isVaryingBranchNumber hV hVQ (hr V hV),
    finite_setOf_isVaryingBranchNumber_ne_one r hr, ?_⟩
  obtain ⟨w₀, β, d₀, ρ₀, hw₀, hβ, hd₀, hρ₀, rfl⟩ := hD
  rw [finsum_congr fun v => finsum_congr fun hv => isValuationWeight_unique (hw₀ v hv) (hw v hv),
    finsum_congr fun S => show d₀ S * ρ₀ S = d S * ρ S by
      rw [isLabelDefault_unique (hd₀ S) (hd S), divisorCycleRank_unique (hρ₀ S) (hρ S)]]
  linarith [neg_finsum_le_finsum_isSurfaceBracket hi hβ r hr]

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain
