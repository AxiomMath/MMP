/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Termination.Defs

/-!
# The projective termination levels `T(e)`

For `e ∈ ℕ`, `T(e)` is the statement that every sequence of flips starting from an effective
rational klt pair `(X, B)`, with `X` a normal projective `ℚ`-factorial complex threefold and
`e(X, B) = e`, is finite, provided all models and all contraction targets of the sequence are
projective. Each step of a sequence of flips is the contraction of a `(K + B)`-negative extremal
contraction with relative Picard number one, followed by its flip, and the boundary is the
transform of the fixed initial boundary. Here `e(X, B)` is the number of exceptional divisors of
`k(X)` with center on `X` and discrepancy `a(E, X, B) ≤ 0`; it does not count divisors on `X`.

## Main definitions

* `MMP.Fourfold.ProjectiveKltTerminationLevel`: the property `T(e)`.

## Implementation notes

The number `e(X, B)` is `MMP.Flips.eCount`, which is defined for pairs that are Kawamata log
terminal in the sense of `MMP.Flips.IsKawamataLogTerminal`, computed with the canonical divisor
`K` of dimension `3` that also starts the sequence of flips. The pair is assumed klt both in this
sense and in the sense of `MMP.Fourfold.IsKltPair`; the two notions agree for a `ℚ`-divisor.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.10, 6.6
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **The projective termination level** `T(e)`, for `e ∈ ℕ`: for every normal projective
`ℚ`-factorial complex threefold `X` with canonical divisor `K` and every effective `ℚ`-divisor `B`
such that `(X, B)` is klt and `e(X, B) = e`, every sequence of flips for `(X, B)` whose models
`X_i` and whose contraction targets `Z_i` are all projective terminates. -/
@[mmp "def_mmp_projective_klt_termination_level"]
def ProjectiveKltTerminationLevel (e : ℕ) : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (K : Divisor X) (B : QDivisor X),
    MMP.Mori.IsProjectiveVariety ℂ sX → topologicalKrullDim X = 3 → IsQFactorial sX →
    B.IsEffective → IsKltPair sX B →
    ∀ hB : IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor B),
      eCount sX 3 K (QDivisor.toRDivisor B) hB = e →
      ∀ S : SequenceOfFlips sX 3 K B,
        (∀ i : ℕ, (i : ℕ∞) < S.length → MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1) →
        (∀ i : ℕ, ((i + 1 : ℕ) : ℕ∞) < S.length → MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) →
        S.Terminates

end MMP.Fourfold
