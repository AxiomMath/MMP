module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Abundance.ContractibleChainProjective
public import MMP.AlgebraicGeometry.MMP.Flip.TrivialFlopPullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Threefold.EffectiveDivisorFlopTermination
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.ReductionNoTriviallyConnected

/-!
# Reduction to pairs without trivially connected prime divisors

Let `(X, Δ_X)` satisfy the assumptions of the abundance theorem FA 15.4 and put
`L = K_X + Δ_X`. Either `L` is eventually free and composed of a pencil, or there is a pair
`(X', Δ_{X'})`, again satisfying the assumptions of FA 15.4, on which no prime divisor is
`(K_{X'} + Δ_{X'})`-trivially connected, and such that `L` is eventually free as soon as
`K_{X'} + Δ_{X'}` is. This reduces the abundance theorem for log elliptic threefolds to pairs
without trivially connected prime divisors (FA 15.9).

## Main results

* `SatisfiesAbundanceAssumptions.isEventuallyFreePencil_or_exists_forall_not_isTriviallyConnected`:
  either `K_X + Δ_X` is eventually free and composed of a pencil, or `(X, Δ_X)` reduces to a pair
  satisfying the same assumptions with no trivially connected prime divisor.

## Implementation notes

The statement is over `ℂ`, as in the source. FA's "`(X', Δ_{X'})` is log birational to
`(X, Δ_X)`" is replaced by what the proof of FA 15.13 uses of it: that eventual freeness of
`K_{X'} + Δ_{X'}` implies that of `K_X + Δ_X`. Trivial connectedness is asserted for prime divisors
`E`, as the divisors `Finsupp.single E 1`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.4, 15.6,
  15.9
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Flips MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_fa15_reduce_to_no_trivially_connected

private theorem solution
    {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX]
    {K : Divisor X} {Δ : QDivisor X} (h : SatisfiesAbundanceAssumptions ℂ sX K Δ) :
    IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ) ∨
      ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (_ : IsIntegral X')
        (_ : IsLocallyNoetherian X') (_ : IsNormal X') (_ : CompactSpace X')
        (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX') (K' : Divisor X')
        (Δ' : QDivisor X'),
        SatisfiesAbundanceAssumptions ℂ sX' K' Δ' ∧
          (∀ E : Mori.PrimeDivisor X',
            ¬ IsTriviallyConnected ℂ sX' 3 K' Δ' (Finsupp.single E 1)) ∧
          (IsEventuallyFree ℂ sX' (Divisor.toQDivisor K' + Δ') →
            IsEventuallyFree ℂ sX (Divisor.toQDivisor K + Δ)) :=
  SatisfiesAbundanceAssumptions.isEventuallyFreePencil_or_exists_forall_not_isTriviallyConnected_of_hFlopSequencesTerminate
    MMP.Fourfold.hFlopSequence_length_lt_top h

end Proof_lem_fa15_reduce_to_no_trivially_connected

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori

/-- **Reduction to no trivially connected prime divisors** (FA Cor. 15.9). Let `(X, Δ)`, with
`K` a canonical divisor, satisfy the assumptions of FA 15.4
(`MMP.Flips.SatisfiesAbundanceAssumptions`) over `ℂ`, and let `L = K + Δ`. Then either
* (15.9.1) `L` is eventually free and composed of a pencil (`MMP.Flips.IsEventuallyFreePencil`),
  or
* (15.9.2) there is a pair `(X', Δ')`, with `K'` a canonical divisor, satisfying the assumptions
  of FA 15.4, such that no prime divisor of `X'` is `(K' + Δ')`-trivially connected
  (`MMP.Flips.IsTriviallyConnected`), and such that `L` is eventually free
  (`MMP.Flips.IsEventuallyFree`) if `K' + Δ'` is. -/
@[mmp "lem_fa15_reduce_to_no_trivially_connected"]
public theorem
    SatisfiesAbundanceAssumptions.isEventuallyFreePencil_or_exists_forall_not_isTriviallyConnected
    {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [LocallyOfFiniteType sX] [QuasiCompact sX]
    {K : Divisor X} {Δ : QDivisor X} (h : SatisfiesAbundanceAssumptions ℂ sX K Δ) :
    IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ) ∨
      ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (_ : IsIntegral X')
        (_ : IsLocallyNoetherian X') (_ : IsNormal X') (_ : CompactSpace X')
        (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX') (K' : Divisor X')
        (Δ' : QDivisor X'),
        SatisfiesAbundanceAssumptions ℂ sX' K' Δ' ∧
          (∀ E : Mori.PrimeDivisor X',
            ¬ IsTriviallyConnected ℂ sX' 3 K' Δ' (Finsupp.single E 1)) ∧
          (IsEventuallyFree ℂ sX' (Divisor.toQDivisor K' + Δ') →
            IsEventuallyFree ℂ sX (Divisor.toQDivisor K + Δ)) :=
              by revert X sX K Δ h; first | exact Proof_lem_fa15_reduce_to_no_trivially_connected.solution | exact Proof_lem_fa15_reduce_to_no_trivially_connected.solution _ | exact Proof_lem_fa15_reduce_to_no_trivially_connected.solution _ _ | exact Proof_lem_fa15_reduce_to_no_trivially_connected.solution _ _ _ | exact Proof_lem_fa15_reduce_to_no_trivially_connected.solution _ _ _ _

end MMP.Flips

