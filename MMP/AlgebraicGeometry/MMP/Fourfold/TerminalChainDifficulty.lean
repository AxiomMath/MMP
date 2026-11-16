module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldGraphDivisor
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainLabel

/-!
# Fixed and varying labels, branch numbers, weights and prepared chains of fourfolds

Let `(p_i, Θ_i)_{i ≥ 0}`, `p_i : Y_i ⟶ X_i`, be a terminal chain over a stabilized small klt
tail `(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}` of fourfolds, with labels `S_h` and label coefficients
`b_h^M`. A label is *fixed* if the sequence `(b_h^{(i)})_{i ≥ 0}` of its coefficients at the
junctions is eventually constant, and *varying* otherwise.

An *admissible scale* for the chain is a positive integer `N` with `N c ∈ ℤ` for every
coefficient `c` of `B_0` and for the eventual value `c` of the coefficient of every fixed label.
For a real number `u`, the *weight* is `w(u) = ⌈N max{u, 0}⌉`, and for `b ∈ [0, 1)` the
*default echo weight* is `d(b) = ∑_{j ≥ 1} w(1 - j(1 - b))`; the default echo weight of a label
`S_h` of a model with coefficient `b_h` is `d_h = d(b_h)`.

For a model `(Y, Θ)` of the chain, a label `S_h` and an irreducible surface `V ⊆ Y`, the *branch
number* `r_{V,h}` is the number of prime divisors of the normalization `S_h^ν` mapping onto `V`,
counted as prime divisors of the scheme `S_h^ν` (over `κ(η_V)`, not as geometric sheets); it is
`0` when `V ⊄ S_h`.

A *prepared chain* is a tail of the terminal chain starting at a junction `Y_{i₀}`, such that on
it

1. every fixed label has constant coefficient;
2. at every junction `p_i : Y_i ⟶ X_i`, `i ≥ i₀`, every varying label has positive coefficient,
   and `p_i` maps the reduced union of the varying labels onto a closed set of dimension at most
   one;
3. every default echo weight `d_h` is constant on all models of the tail.

## Main definitions

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsFixedLabel`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsVaryingLabel`: fixed and varying labels.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsAdmissibleScale`: admissible scales.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelBranchNumber`: `r = r_{V,h}` on a
  model.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelDefault`: `d = d_h` on a model.
* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain`: prepared chains, with models
  `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.ModelIndex`.

The weight `w(u)` is `MMP.Fourfold.difficultyWeight`, and `d(b)` is
`MMP.Fourfold.defaultWeight`; both are at an arbitrary scale `N`.

## Main results

* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isFixedLabel_or_isVaryingLabel`: every
  label is fixed or varying.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.isLabelBranchNumber_zero_of_not_subset`:
  `r_{V,h} = 0` when `V ⊄ S_h`.
* `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.exists_isLabelBranchNumber`,
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.exists_isLabelDefault`: every label has a
  branch number and a default echo weight at every model.

## Implementation notes

* Label coefficients are the predicate
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCoefficient`, so a fixed label is one
  for which some `c` is the coefficient at every junction from some index on, and branch numbers
  and default echo weights are predicates on their values.
* On a model `M`, the label `S_h` is its centre `S_h^M`, recorded by
  `MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre` when it is a prime divisor
  `P` of `M`. The branch number is then `MMP.Fourfold.branchNumber P V`, the number of prime
  divisors of the normalization of `P` whose image in `M` is `V`; it vanishes when `V ⊄ P`
  (`MMP.Fourfold.branchNumber_eq_zero_of_not_subset`). When `S_h^M` is not a prime divisor of
  `M`, no surface lies in it as a divisor and the branch number is `0`, as the label coefficient
  is.
* The branch number is defined at every irreducible closed subset `V` of the model; the source
  considers irreducible surfaces, `topologicalKrullDim V = 2`.
* The weight and the default echo weight are defined for every natural number `N` and the
  default for every real `b` (`0` if the finitely supported sum had infinite support); the
  source takes `N` the fixed admissible scale and `b ∈ [0, 1)`. As the prepared chain and the
  default echo weight of a label refer to the fixed admissible scale, a prepared chain carries
  its admissible scale `N` as data.
* A prepared chain is recorded by the terminal chain, the index `i₀` of its first junction and
  the scale. The models of the tail are the models `(i, ·)` of the chain with `i ≥ i₀`. "Every
  fixed label has constant coefficient" reads: there is `c` which is its coefficient at every
  model of the tail. "Every varying label has positive coefficient at `p_i`" reads: its
  coefficient at the junction `Y_i` is some `b > 0`. The reduced union of the varying labels on
  `Y_i` is the union of the supports of their centres on `Y_i`, and "`p_i` maps it onto a closed
  set of dimension at most one" reads: its image in `X_i` is closed, of topological Krull
  dimension at most `1`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

attribute [mmp "def_oai4_weight"] MMP.Fourfold.difficultyWeight
attribute [mmp "def_oai4_default_echo_weight"] MMP.Fourfold.defaultWeight

namespace StabilizedSmallKltTail

namespace TerminalChain

variable {T : StabilizedSmallKltTail} (C : TerminalChain T)

/-! ### Fixed and varying labels -/

/-- A label `S_h` of a terminal chain is *fixed* if the sequence `(b_h^{(i)})_{i ≥ 0}` of its
coefficients at the junctions is eventually constant: there are `c` and `n` with
`b_h^{(i)} = c` for every `i ≥ n`. -/
@[mmp "def_oai4_fixed_label"]
def IsFixedLabel (S : C.Label) : Prop :=
  ∃ (c : ℚ) (n : ℕ), ∀ i ≥ n, C.IsJunctionLabelCoefficient S i c

/-- A label of a terminal chain is *varying* if it is not fixed. -/
@[mmp "def_oai4_varying_label"]
def IsVaryingLabel (S : C.Label) : Prop :=
  ¬ C.IsFixedLabel S

/-- A label is varying if and only if it is not fixed. -/
theorem isVaryingLabel_iff_not_isFixedLabel (S : C.Label) :
    C.IsVaryingLabel S ↔ ¬ C.IsFixedLabel S :=
  Iff.rfl

/-- A label is not varying if and only if it is fixed. -/
theorem not_isVaryingLabel_iff (S : C.Label) : ¬ C.IsVaryingLabel S ↔ C.IsFixedLabel S :=
  not_not

/-- Every label is fixed or varying. -/
theorem isFixedLabel_or_isVaryingLabel (S : C.Label) :
    C.IsFixedLabel S ∨ C.IsVaryingLabel S :=
  em _

/-! ### Admissible scales -/

/-- An *admissible scale* for a terminal chain over a stabilized small klt tail
`(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`: a positive integer `N` such that `N c ∈ ℤ` for every
coefficient `c` of `B_0`, and for the eventual constant value `c` of the coefficient
`b_h^{(i)}` of every fixed label `S_h`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsFixedLabel`). No condition is imposed on
varying labels. -/
@[mmp "def_oai4_admissible_scale"]
def IsAdmissibleScale (N : ℕ) : Prop :=
  0 < N ∧ (∀ P : MMP.Mori.PrimeDivisor (T.X 0), ∃ z : ℤ, (N : ℚ) * (T.B 0).coeff P = z) ∧
    ∀ (S : C.Label) (c : ℚ), (∃ n : ℕ, ∀ i ≥ n, C.IsJunctionLabelCoefficient S i c) →
      ∃ z : ℤ, (N : ℚ) * c = z

variable {C}

/-- An admissible scale is positive. -/
theorem IsAdmissibleScale.pos {N : ℕ} (h : C.IsAdmissibleScale N) : 0 < N :=
  h.1

/-- An admissible scale `N` makes `N c` an integer for every coefficient `c` of `B_0`. -/
theorem IsAdmissibleScale.exists_intCast_eq_coeff {N : ℕ} (h : C.IsAdmissibleScale N)
    (P : MMP.Mori.PrimeDivisor (T.X 0)) : ∃ z : ℤ, (N : ℚ) * (T.B 0).coeff P = z :=
  h.2.1 P

/-- An admissible scale clears the denominator of the eventual coefficient of a fixed label. -/
theorem IsAdmissibleScale.exists_intCast_eq_of_eventually {N : ℕ} (h : C.IsAdmissibleScale N)
    {S : C.Label} {c : ℚ} {n : ℕ} (hc : ∀ i ≥ n, C.IsJunctionLabelCoefficient S i c) :
    ∃ z : ℤ, (N : ℚ) * c = z :=
  h.2.2 S c ⟨n, hc⟩

variable (C)

/-! ### Branch numbers -/

/-- `r` is the *branch number* `r_{V,h}` of a label `S_h` at an irreducible closed subset `V`
(an irreducible surface in the source) of the model `M` indexed by `x`: either the centre
`S_h^M` is a prime divisor `P` of `M` and `r` is the number of prime divisors of the
normalization of `P` mapping onto `V` (`MMP.Fourfold.branchNumber`), which is `0` when `V ⊄ P`
(`MMP.Fourfold.branchNumber_eq_zero_of_not_subset`); or `S_h^M` is not a prime divisor of `M`
and `r = 0`. -/
@[mmp "def_oai4_branch_number"]
def IsLabelBranchNumber (S : C.Label) (x : C.ModelIndex) (V : IrreducibleCloseds (C.model x))
    (r : ℕ) : Prop :=
  (∃ P : MMP.Mori.PrimeDivisor (C.model x),
    C.IsLabelCentre S x P ∧ r = branchNumber P (V : Set (C.model x))) ∨
  ((∀ P : MMP.Mori.PrimeDivisor (C.model x), ¬ C.IsLabelCentre S x P) ∧ r = 0)

variable {C}

/-- The branch number `r_{V,h}` vanishes when `V` lies in no prime divisor `S_h^M`. -/
theorem isLabelBranchNumber_zero_of_not_subset {S : C.Label} {x : C.ModelIndex}
    {V : IrreducibleCloseds (C.model x)}
    (hV : ∀ P : MMP.Mori.PrimeDivisor (C.model x), C.IsLabelCentre S x P →
      ¬ (V : Set (C.model x)) ⊆ P.support) :
    C.IsLabelBranchNumber S x V 0 := by
  by_cases h : ∃ P, C.IsLabelCentre S x P
  · obtain ⟨P, hP⟩ := h
    exact Or.inl ⟨P, hP, (branchNumber_eq_zero_of_not_subset (hV P hP)).symm⟩
  · exact Or.inr ⟨fun P hP => h ⟨P, hP⟩, rfl⟩

/-- Every label has a branch number at every irreducible closed subset of every model. -/
theorem exists_isLabelBranchNumber (S : C.Label) (x : C.ModelIndex)
    (V : IrreducibleCloseds (C.model x)) : ∃ r, C.IsLabelBranchNumber S x V r := by
  by_cases h : ∃ P, C.IsLabelCentre S x P
  · obtain ⟨P, hP⟩ := h
    exact ⟨_, Or.inl ⟨P, hP, rfl⟩⟩
  · exact ⟨0, Or.inr ⟨fun P hP => h ⟨P, hP⟩, rfl⟩⟩

variable (C)

/-! ### Default echo weights of labels -/

/-- `d` is the *default echo weight* `d_h = d(b_h)` of a label `S_h` at the model `M` indexed by
`x`, at scale `N` (the fixed admissible scale of the chain): `b_h` is the label coefficient
`b_h^M` and `d = d(b_h)` (`MMP.Fourfold.defaultWeight`). -/
@[mmp "def_oai4_default_echo_weight"]
def IsLabelDefault (N : ℕ) (S : C.Label) (x : C.ModelIndex) (d : ℕ) : Prop :=
  ∃ b : ℚ, C.IsLabelCoefficient S x b ∧ d = defaultWeight N b

variable {C}

/-- Every label has a default echo weight at every model. -/
theorem exists_isLabelDefault (N : ℕ) (S : C.Label) (x : C.ModelIndex) :
    ∃ d, C.IsLabelDefault N S x d := by
  obtain ⟨b, hb⟩ := C.exists_isLabelCoefficient S x
  exact ⟨_, b, hb, rfl⟩

end TerminalChain

/-! ### Prepared chains -/

/-- A *prepared chain*: the tail, starting at the junction `Y_{i₀}`, of a terminal chain over a
stabilized small klt tail, with an admissible scale `N` (the fixed admissible scale), such that
on it

1. every fixed label has constant coefficient on all models of the tail;
2. at every junction `p_i : Y_i ⟶ X_i`, `i ≥ i₀`, every varying label has positive coefficient,
   and `p_i` maps the reduced union of the varying labels onto a closed set of dimension at most
   one;
3. every default echo weight `d_h` is constant on all models of the tail.

Its *models* (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.ModelIndex`) are the models of
the terminal chain from `Y_{i₀}` on. -/
@[mmp "def_oai4_prepared_chain"]
structure PreparedChain (T : StabilizedSmallKltTail) where
  /-- The terminal chain. -/
  chain : TerminalChain T
  /-- The index `i₀` of the junction at which the tail starts. -/
  start : ℕ
  /-- The fixed admissible scale `N`. -/
  scale : ℕ
  /-- `scale` is an admissible scale for the chain. -/
  isAdmissibleScale : chain.IsAdmissibleScale scale
  /-- Every fixed label has constant coefficient on all models of the tail. -/
  isLabelCoefficient_const_of_isFixedLabel : ∀ S : chain.Label, chain.IsFixedLabel S →
    ∃ c : ℚ, ∀ x : chain.ModelIndex, start ≤ x.1 → chain.IsLabelCoefficient S x c
  /-- Every varying label has positive coefficient at every junction `Y_i`, `i ≥ i₀`. -/
  pos_of_isVaryingLabel : ∀ i ≥ start, ∀ S : chain.Label, chain.IsVaryingLabel S →
    ∃ b : ℚ, chain.IsJunctionLabelCoefficient S i b ∧ 0 < b
  /-- The image of the varying labels at every junction `Y_i`, `i ≥ i₀`, is closed. -/
  isClosed_image_varyingLabels : ∀ i ≥ start,
    IsClosed ((chain.junction i).p ''
      {y : (chain.junction i).Y | ∃ S : chain.Label, chain.IsVaryingLabel S ∧
        ∃ P : MMP.Mori.PrimeDivisor (chain.model ⟨i, none⟩),
          chain.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support})
  /-- The image of the varying labels at every junction `Y_i`, `i ≥ i₀`, has dimension at most
  one. -/
  topologicalKrullDim_image_varyingLabels_le : ∀ i ≥ start,
    topologicalKrullDim ((chain.junction i).p ''
      {y : (chain.junction i).Y | ∃ S : chain.Label, chain.IsVaryingLabel S ∧
        ∃ P : MMP.Mori.PrimeDivisor (chain.model ⟨i, none⟩),
          chain.IsLabelCentre S ⟨i, none⟩ P ∧ y ∈ P.support}) ≤ 1
  /-- Every default echo weight is constant on all models of the tail. -/
  isLabelDefault_const : ∀ S : chain.Label, ∃ d : ℕ,
    ∀ x : chain.ModelIndex, start ≤ x.1 → chain.IsLabelDefault scale S x d

namespace PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

/-- The models of a prepared chain: the models of the terminal chain from the junction
`Y_{i₀}` on. -/
@[mmp "def_oai4_prepared_chain"]
abbrev ModelIndex : Type := {x : Q.chain.ModelIndex // Q.start ≤ x.1}

end PreparedChain

end StabilizedSmallKltTail

end MMP.Fourfold
