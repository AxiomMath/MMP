module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor

/-!
# Prepared chains, weights of valuations and curve brackets

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized tail
`(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`, with labels `S_h`. A *prepared chain* is the tail of the
terminal chain starting at a junction `Y_{i₀}`, together with an admissible scale `N`, such that

1. every fixed label has constant coefficient, equal to its eventual value, on all models of the
   tail;
2. at every junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, every varying label has positive
   coefficient, and `p_i` maps the union of the varying labels onto a finite set of closed points;
3. every default `d_h` is constant on all models of the tail.

Its models are the models of the terminal chain from `Y_{i₀}` on, and its moves are the passages
between consecutive models: a coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` or a flip of a
bridge, a threefold step diagram `Y⁻ → Z ← Y⁺` with both maps small.

For a model `(Y, Θ)` of a terminal chain and a normalized divisorial valuation `v` of `ℂ(Y)`
exceptional over `Y`, the *weight* of `v` is `w_v = w(2 - a(v; Y, Θ))`, where `w` is the weight
function at the admissible scale; it is nonzero exactly when `a(v; Y, Θ) < 2`.

For a model `(Y, Θ)` of a prepared chain and an irreducible closed curve `C ⊆ Y`, the *bracket*
at `C` is `β_C(Y, Θ) = ∑_{c_Y(v) = C} w_v - ∑_h r_{C,h} d_h`, the first sum running over the
normalized divisorial valuations with centre `C` and the second over the labels, with branch
numbers `r_{C,h}` and defaults `d_h`.

## Main definitions

* `MMP.Fourfold.StabilizedTail.PreparedChain`: prepared chains, with models
  `MMP.Fourfold.StabilizedTail.PreparedChain.ModelIndex`.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`: `w = w_v` on a model of a
  terminal chain.
* `MMP.Fourfold.StabilizedTail.PreparedChain.IsCurveBracket`: `β = β_C(Y, Θ)` on a model of a
  prepared chain.

## Main results

* `MMP.Fourfold.StabilizedTail.TerminalChain.finite_label`: a terminal chain has finitely many
  labels.
* `MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight.exists_eq_zero_iff`: at a positive
  scale, `w_v = 0` if and only if `a(v; Y, Θ) ≥ 2`.

## Implementation notes

* A prepared chain is recorded by the terminal chain, the index `i₀` of its first junction and
  the admissible scale `N`. The models of the tail are the models `(i, ·)` of the chain with
  `i ≥ i₀`; in the lexicographic order of `MMP.Fourfold.StabilizedTail.TerminalChain.ModelIndex`
  these are the models from the junction `(i₀, none)` on. The moves are those of the terminal
  chain between such models, described in `MMP.Fourfold.StabilizedTail.TerminalChain`; they are
  not restated.
* Label coefficients are the predicate
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelCoefficient`
  (the centre of the label on the model is a prime divisor with that coefficient). "Every fixed
  label has constant coefficient equal to its eventual value" reads: there is `c` which is the
  coefficient at all junctions from some index on (its eventual value) and the coefficient at
  every model of the tail. "Every varying label has positive coefficient" reads: its coefficient
  at the junction is some `b > 0`. The union of the varying labels on `Y_i` is the union of the
  supports of their centres on `Y_i`, and "`p_i` maps it onto a finite set of closed points"
  reads: its image is finite and consists of closed points. "Every default is constant" reads:
  there is `d` which is the default of the label at every model of the tail.
* Log discrepancies, branch numbers and defaults on a model are predicates on their values, so
  weights and brackets are too. The weight of `v` at scale `N` is
  `MMP.Fourfold.difficultyWeight N (2 - a)` for `a` the log discrepancy of `v`
  (`MMP.Fourfold.IsValuationLogDiscrepancy`); that `v` is a normalized divisorial valuation
  exceptional over `Y` is `MMP.Intersection.IsExceptionalValuation`. The weight is stated on any
  model of a terminal chain, at any scale; the source takes the fixed admissible scale.
* In the bracket, irreducible closed curves of the projective variety `Y` are recorded as proper
  curves `MMP.Mori.ProperCurve` by their generic points, as for the branch number
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBranchNumber`; a valuation has centre `C`
  when `MMP.Intersection.IsCentre` holds for the irreducible closed set `C`. The first sum is the
  finitely supported sum `∑ᶠ` (`0` if the support were infinite) of chosen weights `w_v` over the
  valuations with centre `C`; the second is the sum over the labels, which are finitely many
  (`MMP.Fourfold.StabilizedTail.TerminalChain.finite_label`), so `∑ᶠ` is the finite sum.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

namespace StabilizedTail

namespace TerminalChain

variable {T : StabilizedTail} (C : TerminalChain T)

/-! ### The models of a terminal chain are normal integral schemes -/

/-- Every model of a terminal chain is an integral scheme. -/
instance model.isIntegral : ∀ x : C.ModelIndex, IsIntegral (C.model x)
  | ⟨i, none⟩ => inferInstanceAs (IsIntegral (C.junction i).Y)
  | ⟨i, some k⟩ => inferInstanceAs (IsIntegral (modelSeq (C.junction i).Y (C.bridge i).P.Y k))

/-- Every model of a terminal chain is a locally noetherian scheme. -/
instance model.isLocallyNoetherian : ∀ x : C.ModelIndex, IsLocallyNoetherian (C.model x)
  | ⟨i, none⟩ => inferInstanceAs (IsLocallyNoetherian (C.junction i).Y)
  | ⟨i, some k⟩ =>
    inferInstanceAs (IsLocallyNoetherian (modelSeq (C.junction i).Y (C.bridge i).P.Y k))

/-- Every model of a terminal chain is a normal scheme. -/
instance model.isNormal : ∀ x : C.ModelIndex, IsNormal (C.model x)
  | ⟨i, none⟩ => inferInstanceAs (IsNormal (C.junction i).Y)
  | ⟨i, some k⟩ => inferInstanceAs (IsNormal (modelSeq (C.junction i).Y (C.bridge i).P.Y k))

/-! ### Finitely many labels -/

/-- A terminal chain has finitely many labels: they are strict transforms of the finitely many
components of `B_0`, or among the finitely many `E_{0,s}`, `s ∈ I_∞`. -/
theorem finite_label : Finite C.Label := by
  have hsub : {S | C.IsLabel S} ⊆
      (⋃ Γ ∈ ((T.B 0).support : Set (MMP.Mori.PrimeDivisor (T.X 0))),
        {S | inverseTransformPrimeDivisor (C.junction 0).p Γ = some S}) ∪
        Set.range (C.junction 0).E := by
    rintro S (⟨Γ, hΓ, hS⟩ | hS)
    · exact Or.inl (Set.mem_biUnion (Finsupp.mem_support_iff.mpr hΓ) hS)
    · exact Or.inr hS
  have hfin : ((⋃ Γ ∈ ((T.B 0).support : Set (MMP.Mori.PrimeDivisor (T.X 0))),
        {S | inverseTransformPrimeDivisor (C.junction 0).p Γ = some S}) ∪
        Set.range (C.junction 0).E).Finite := by
    refine Set.Finite.union ((T.B 0).support.finite_toSet.biUnion fun Γ _ => ?_)
      (Set.finite_range _)
    refine Set.Subsingleton.finite fun S hS S' hS' => ?_
    exact Option.some_injective _ (hS.symm.trans hS')
  exact (hfin.subset hsub).to_subtype

/-! ### Weights of valuations -/

/-- `w` is the *weight* `w_v = w(2 - a(v; Y, Θ))` of a normalized divisorial valuation `v` of
`ℂ(Y)` exceptional over `Y`, for the model `(Y, Θ)` of the terminal chain indexed by `x`, at
scale `N` (the fixed admissible scale): `a = a(v; Y, Θ)` is the log discrepancy of `v` and
`w = w(2 - a)` (`MMP.Fourfold.difficultyWeight`). Only valuations exceptional over `Y` are given
a weight. -/
@[mmp "def_mmp_indexd_valuation_weight"]
def IsValuationWeight (N : ℕ) (x : C.ModelIndex)
    (v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))) (w : ℕ) : Prop :=
  MMP.Intersection.IsExceptionalValuation ℂ (C.modelStructure x) v ∧
    ∃ a : ℝ, IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a ∧
      w = difficultyWeight N (2 - a)

variable {C}

/-- At a positive scale, the weight `w_v` vanishes exactly when the log discrepancy
`a(v; Y, Θ)` it is computed from is at least `2`. -/
theorem IsValuationWeight.exists_eq_zero_iff {N : ℕ} (hN : 0 < N) {x : C.ModelIndex}
    {v : Valuation (C.model x).functionField (WithZero (Multiplicative ℤ))} {w : ℕ}
    (hw : C.IsValuationWeight N x v w) :
    ∃ a : ℝ, IsValuationLogDiscrepancy (C.modelStructure x) (C.modelBoundary x) v a ∧
      (w = 0 ↔ 2 ≤ a) := by
  obtain ⟨-, a, ha, rfl⟩ := hw
  exact ⟨a, ha, by rw [difficultyWeight_eq_zero_iff hN, sub_nonpos]⟩

end TerminalChain

/-! ### Prepared chains -/

/-- A *prepared chain*: the tail, starting at the junction `Y_{i₀}`, of a terminal chain over a
stabilized tail, with an admissible scale `N` (the fixed admissible scale), such that on it

1. every fixed label has constant coefficient, equal to its eventual value, on all models of the
   tail;
2. at every junction `p_i : (Y_i, Θ_i) ⟶ (X_i, B_i)`, `i ≥ i₀`, every varying label has positive
   coefficient, and `p_i` maps the union of the varying labels onto a finite set of closed points;
3. every default `d_h` is constant on all models of the tail.

Its *models* (`MMP.Fourfold.StabilizedTail.PreparedChain.ModelIndex`) are the models of the
terminal chain from `Y_{i₀}` on, and its *moves* are the passages between consecutive models: a
coefficient decrease `(Y_i, Θ_i) ⇝ (Y_i, Θ_i')` or a small terminal flip
`(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` of a bridge, a threefold step diagram `Y⁻ → Z ← Y⁺` with both maps
small. -/
@[mmp "def_mmp_indexd_prepared_chain"]
structure PreparedChain (T : StabilizedTail) where
  /-- The terminal chain. -/
  chain : TerminalChain T
  /-- The index `i₀` of the junction at which the tail starts. -/
  start : ℕ
  /-- The fixed admissible scale `N`. -/
  scale : ℕ
  isAdmissibleScale : chain.IsAdmissibleScale scale
  isLabelCoefficient_of_isFixedLabel : ∀ S : chain.Label, chain.IsFixedLabel S →
    ∃ c : ℚ, (∃ n : ℕ, ∀ i ≥ n, chain.IsJunctionLabelCoefficient S i c) ∧
      ∀ x : chain.ModelIndex, start ≤ x.1 → chain.IsLabelCoefficient S x c
  pos_of_isVaryingLabel : ∀ i ≥ start, ∀ S : chain.Label, chain.IsVaryingLabel S →
    ∃ b : ℚ, chain.IsJunctionLabelCoefficient S i b ∧ 0 < b
  finite_image_varyingLabels : ∀ i ≥ start,
    ((chain.junction i).p ''
      {y : (chain.junction i).Y | ∃ S : chain.Label, chain.IsVaryingLabel S ∧
        ∃ P : MMP.Mori.PrimeDivisor (chain.model ⟨i, none⟩),
          chain.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support}).Finite
  isClosed_of_mem_image_varyingLabels : ∀ i ≥ start, ∀ z ∈ (chain.junction i).p ''
      {y : (chain.junction i).Y | ∃ S : chain.Label, chain.IsVaryingLabel S ∧
        ∃ P : MMP.Mori.PrimeDivisor (chain.model ⟨i, none⟩),
          chain.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support},
    IsClosed ({z} : Set (T.X i))
  isLabelDefault_const : ∀ S : chain.Label, ∃ d : ℕ,
    ∀ x : chain.ModelIndex, start ≤ x.1 → chain.IsLabelDefault scale S x d

namespace PreparedChain

variable {T : StabilizedTail} (Q : PreparedChain T)

/-- The models of a prepared chain: the models of the terminal chain from the junction
`Y_{i₀}` on. -/
abbrev ModelIndex : Type := {x : Q.chain.ModelIndex // Q.start ≤ x.1}

/-- `β` is the *bracket* `β_C(Y, Θ) = ∑_{c_Y(v) = C} w_v - ∑_h r_{C,h} d_h` at an irreducible
closed curve `C` (`γ`) of the model `(Y, Θ)` of the prepared chain indexed by `x`: the first sum,
over the normalized divisorial valuations `v` of `ℂ(Y)` with centre `C` (all exceptional over
`Y`), is the finitely supported sum (`0` if the support were infinite) of their weights `w_v`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsValuationWeight`) at the fixed admissible scale,
and the second runs over the finitely many labels `S_h`, with branch numbers `r_{C,h}`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBranchNumber`) and defaults `d_h`
(`MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelDefault`). -/
@[mmp "def_mmp_indexd_bracket"]
def IsCurveBracket (x : Q.ModelIndex) (γ : ProperCurve (Q.chain.modelStructure x.1)) (β : ℤ) :
    Prop :=
  ∃ (w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (r d : Q.chain.Label → ℕ),
    (∀ v, (∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
          (Z : Set (Q.chain.model x.1)) = closure {γ.point}) →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v)) ∧
    (∀ S, Q.chain.IsLabelBranchNumber S x.1 γ (r S)) ∧
    (∀ S, Q.chain.IsLabelDefault Q.scale S x.1 (d S)) ∧
    β = ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧
          (Z : Set (Q.chain.model x.1)) = closure {γ.point}), w v : ℕ) : ℤ) -
      ((∑ᶠ S, r S * d S : ℕ) : ℤ)

end PreparedChain

end StabilizedTail

end MMP.Fourfold
