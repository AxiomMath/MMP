module
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainBracket
public import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty

/-!
# The difficulty of a model of a prepared chain of fourfolds

Let `(Y, Θ)` be a model of a prepared chain of fourfolds, with fixed admissible scale `N`,
labels `S_h` and default echo weights `d_h`. The *difficulty* of `(Y, Θ)` is the integer
`𝒟(Y, Θ) = ∑_{codim c_Y(v) ≥ 3} w_v + ∑_{dim V = 2} β_V(Y, Θ) + ∑_h d_h ρ_*(S_h^ν)`:
the first sum runs over the normalized divisorial valuations `v` of `ℂ(Y)` whose centre has
codimension at least three, with weights `w_v = w(2 - a(v; Y, Θ))`; the second over the
irreducible surfaces `V ⊆ Y`, with the brackets `β_V(Y, Θ)` taken at each surface before
summing; the third over the finitely many labels, with `ρ_*(S_h^ν)` the divisor cycle rank of
the normalization of the label on `Y`. The first two sums are finitely supported sums, `0` by
convention if the support were infinite.

## Main definitions

* `MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsDifficulty`: `D = 𝒟(Y, Θ)` on a model
  of a prepared chain.

## Implementation notes

* As for weights and brackets, the difficulty is a predicate on its value: it holds for `D`
  when there are weights `w_v` of the valuations with centre of codimension `≥ 3`
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`, at the fixed
  admissible scale), brackets `β_V` of the irreducible surfaces
  (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsSurfaceBracket`), default echo weights
  `d_h` (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelDefault`) and divisor cycle
  ranks `ρ_h` with `D` the sum. The first two sums are `∑ᶠ`; the third is over the finitely
  many labels.
* Irreducible surfaces of `Y` are the irreducible closed subsets `V` with
  `topologicalKrullDim V = 2`, and the codimension of the centre `Z = c_Y(v)` is the coheight
  `codimension Z` among the irreducible closed subsets of `Y`; that `v` is a normalized
  divisorial valuation with centre `Z` is `MMP.Intersection.IsCentre`.
* The normalization `S_h^ν` of a label is the normalization
  `MMP.Fourfold.primeDivisorNormalizationScheme` of its centre on the model, a prime divisor
  (`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelCentre`), over `ℂ` through the
  normalization morphism to the model (`MMP.Fourfold.primeDivisorNormalizationOver`). The
  divisor cycle rank `MMP.Analytic.divisorCycleRank` is defined on complex schemes
  (`MMP.IsComplexScheme`); the normalization of a prime divisor of a projective
  complex variety is one (`MMP.Fourfold.isComplexScheme_primeDivisorNormalizationScheme`), and
  the predicate asks for that instance. When the label has no prime divisor as centre on the
  model, its term is `0`, as its branch numbers and its coefficient are.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

variable {T : StabilizedSmallKltTail} (Q : PreparedChain T)

/-- `D` is the *difficulty* `𝒟(Y, Θ)` of the model `(Y, Θ)` of the prepared chain indexed by `x`:
`D = ∑_{codim c_Y(v) ≥ 3} w_v + ∑_{dim V = 2} β_V(Y, Θ) + ∑_h d_h ρ_*(S_h^ν)`. The first sum,
over the normalized divisorial valuations `v` of `ℂ(Y)` whose centre has codimension at least
three, is the finitely supported sum (`0` if the support were infinite) of their weights `w_v`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsValuationWeight`) at the fixed admissible
scale; the second, over the irreducible surfaces `V ⊆ Y`, is the finitely supported sum of the
brackets `β_V(Y, Θ)` (`MMP.Fourfold.StabilizedSmallKltTail.PreparedChain.IsSurfaceBracket`); the
third runs over the finitely many labels `S_h`, with default echo weights `d_h`
(`MMP.Fourfold.StabilizedSmallKltTail.TerminalChain.IsLabelDefault`) and the divisor cycle ranks
`ρ_*(S_h^ν)` (`MMP.Analytic.divisorCycleRank`) of the normalizations of their centres on `Y`
(`0` for a label whose centre on `Y` is not a prime divisor). -/
@[mmp "def_oai4_difficulty"]
public def IsDifficulty (x : Q.ModelIndex) (D : ℤ) : Prop :=
  ∃ (w : Valuation (Q.chain.model x.1).functionField (WithZero (Multiplicative ℤ)) → ℕ)
    (β : IrreducibleCloseds (Q.chain.model x.1) → ℤ) (d ρ : Q.chain.Label → ℕ),
    (∀ v, (∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧ 3 ≤ codimension Z) →
      Q.chain.IsValuationWeight Q.scale x.1 v (w v)) ∧
    (∀ V : IrreducibleCloseds (Q.chain.model x.1),
      topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2 → Q.IsSurfaceBracket x V (β V)) ∧
    (∀ S, Q.chain.IsLabelDefault Q.scale S x.1 (d S)) ∧
    (∀ S, (∃ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), Q.chain.IsLabelCentre S x.1 P ∧
        letI := primeDivisorNormalizationOver (Q.chain.modelStructure x.1) P
        ∃ _ : MMP.IsComplexScheme (primeDivisorNormalizationScheme P),
          ρ S = MMP.Analytic.divisorCycleRank (primeDivisorNormalizationScheme P)) ∨
      ((∀ P : MMP.Mori.PrimeDivisor (Q.chain.model x.1), ¬ Q.chain.IsLabelCentre S x.1 P) ∧
        ρ S = 0)) ∧
    D = ((∑ᶠ (v) (_ : ∃ Z : IrreducibleCloseds (Q.chain.model x.1),
        MMP.Intersection.IsCentre ℂ (Q.chain.modelStructure x.1) v Z ∧ 3 ≤ codimension Z),
          w v : ℕ) : ℤ) +
      (∑ᶠ (V : IrreducibleCloseds (Q.chain.model x.1))
        (_ : topologicalKrullDim (V : Set (Q.chain.model x.1)) = 2), β V) +
      ((∑ᶠ S, d S * ρ S : ℕ) : ℤ)

end MMP.Fourfold.StabilizedSmallKltTail.PreparedChain

end
