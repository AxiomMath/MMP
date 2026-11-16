module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Contraction.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.TriviallyConnectedContractible
public import MMP.AlgebraicGeometry.MMP.Threefold.EffectiveDivisorFlopTermination

/-!
# A trivially connected prime divisor becomes contractible after trivial flops

Let `(X, Δ_X)` satisfy the assumptions of the abundance theorem FA 15.4, and suppose that
`L = K_X + Δ_X` is not eventually free and composed of a pencil. If `D` is an `L`-trivially
connected prime divisor on `X`, then after finitely many flops of `(K + Δ)`-trivial flop data
`X = X₀ ⤏ X₁ ⤏ ⋯ ⤏ X_m` the strict transform `D_m` of `D` is the exceptional locus of a
birational contraction `c : X_m ⟶ X'`. Moreover `K_{X_m} + Δ_m ∼_ℚ c^*(K_{X'} + Δ')` with
`Δ' = c_* Δ_m`, `ρ(X') = ρ(X) - 1`, and `(X', Δ')` again satisfies the assumptions of FA 15.4.

## Main results

* `MMP.Flips.IsTriviallyConnected.exists_isBirationalContraction_of_satisfiesAbundanceAssumptions`

## Implementation notes

The models of the chain follow `MMP.Fourfold.modelSeq`: `X₀ = X` and `X_{i+1} = Y i`, with
structure morphisms `MMP.Fourfold.modelStr` and divisors `MMP.Fourfold.divisorSeq`. Only the
data with index `i < m` (for the flops) and `i = m` (for the contraction) are constrained. Every
divisor on `X_{i+1}` is the birational transform of the one on `X_i` along the flop
`p_i : X_i ⤏ X_{i+1}`: for `Δ` this is `MMP.Flips.flopDivisor`, and the canonical divisor and
the divisor `D` are transformed in the same way. On `X'` the divisors are the birational
transforms along `c`. The `ℚ`-linear equivalence is `MMP.Mori.QDivisor.QLinearlyEquivalent` with
the pull-back `MMP.Mori.QDivisor.IsPullback`. The pull-back is defined because `K_{X'} + Δ'` is
`ℚ`-Cartier, which is part of `MMP.Flips.SatisfiesAbundanceAssumptions`. The Picard drop is
written `ρ(X') + 1 = ρ(X)` in `ℕ∞`, which avoids truncated subtraction.
The statement is over `ℂ`, as in the source.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.9
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Fourfold MMP.Flips

namespace Proof_lem_fa15_trivially_connected_becomes_contractible

private theorem solution
    {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (hA : SatisfiesAbundanceAssumptions ℂ sX K Δ)
    (hL : ¬ IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ))
    {D : Mori.PrimeDivisor X} (hD : IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single D 1)) :
    ∃ (m : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
      (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
      (KY : ∀ i, Divisor (Y i)) (ΔY : ∀ i, QDivisor (Y i)) (DY : ∀ i, Divisor (Y i))
      (T : ℕ → Scheme.{0}) (sT : ∀ i, T i ⟶ Spec (.of ℂ)) (φ : ∀ i, modelSeq X Y i ⟶ T i)
      (φp : ∀ i, Y i ⟶ T i) (p : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i < m, IsTrivialFlop ℂ (modelStr sX sY i) (sY i) (sT i) 3 (divisorSeq K KY i)
          (divisorSeq Δ ΔY i) (φ i) (φp i) (p i) ∧
        KY i = RationalMap.transformDivisor (p i) (divisorSeq K KY i) ∧
        ΔY i = flopDivisor (p i) (divisorSeq Δ ΔY i) ∧
        DY i = RationalMap.transformDivisor (p i)
          (divisorSeq (Finsupp.single D 1 : Divisor X) DY i)) ∧
      ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (c : modelSeq X Y m ⟶ X')
        (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
        (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX'),
        IsBirationalContraction ℂ sX' (modelStr sX sY m) c ∧ IsBirationalMorphism c ∧
        MMP.Flips.exceptionalSet c =
          ((divisorSeq (Finsupp.single D 1 : Divisor X) DY m).supp : Set (modelSeq X Y m)) ∧
        (∃ (hc : ∀ Z : irreducibleComponents (modelSeq X Y m),
            c (componentGenericPoint (modelSeq X Y m) Z) ∉
              (Divisor.toQDivisor (RationalMap.transformDivisor c.toRationalMap
                (divisorSeq K KY m)) +
                RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).supp)
            (B : QDivisor (modelSeq X Y m)),
          (Divisor.toQDivisor (RationalMap.transformDivisor c.toRationalMap (divisorSeq K KY m)) +
              RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).IsPullback c hc B ∧
            (Divisor.toQDivisor (divisorSeq K KY m) + divisorSeq Δ ΔY m).QLinearlyEquivalent B) ∧
        picardNumber sX' + 1 = picardNumber sX ∧
        SatisfiesAbundanceAssumptions ℂ sX'
          (RationalMap.transformDivisor c.toRationalMap (divisorSeq K KY m))
          (RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)) :=
  IsTriviallyConnected.exists_isBirationalContraction_of_hFlopSequencesTerminate
    @MMP.Fourfold.hFlopSequence_length_lt_top hA hL hD

end Proof_lem_fa15_trivially_connected_becomes_contractible

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori MMP.Fourfold

/-- **A trivially connected prime divisor becomes contractible** (FA 15.9). Let `(X, Δ)`
satisfy the assumptions of FA 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`) over `ℂ`,
with `K + Δ` not eventually free and composed of a pencil (`MMP.Flips.IsEventuallyFreePencil`). Let
`D` be a prime divisor on `X`
which is `(K + Δ)`-trivially connected (`MMP.Flips.IsTriviallyConnected`).

Then there are `m : ℕ` and a chain `X = X₀ ⤏ X₁ ⤏ ⋯ ⤏ X_m` of flops `p_i` of
`(K_i + Δ_i)`-trivial flop data (`MMP.Flips.IsTrivialFlop`), with `X_{i+1} = Y i`. Here
`K_{i+1}`, `Δ_{i+1} = MMP.Flips.flopDivisor p_i Δ_i` and `D_{i+1}` are the birational
transforms along `p_i`. There is also a birational contraction `c : X_m ⟶ X'`
(`MMP.Flips.IsBirationalContraction`, so `c_* 𝒪_{X_m} = 𝒪_{X'}`) whose exceptional set
(`MMP.Flips.exceptionalSet`) is `Supp D_m`. With `K' = c_* K_m` and `Δ' = c_* Δ_m`, the following
hold: `K_m + Δ_m` is `ℚ`-linearly equivalent to the pull-back `c^*(K' + Δ')`,
`ρ(X') + 1 = ρ(X)`, and `(X', Δ')` satisfies the assumptions of FA 15.4. -/
@[mmp "lem_fa15_trivially_connected_becomes_contractible"]
public theorem IsTriviallyConnected.exists_isBirationalContraction_of_satisfiesAbundanceAssumptions
    {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [LocallyOfFiniteType sX] [QuasiCompact sX] {K : Divisor X} {Δ : QDivisor X}
    (hA : SatisfiesAbundanceAssumptions ℂ sX K Δ)
    (hL : ¬ IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ))
    {D : Mori.PrimeDivisor X} (hD : IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single D 1)) :
    ∃ (m : ℕ) (Y : ℕ → Scheme.{0}) (sY : ∀ i, Y i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (Y i)) (_ : ∀ i, CompactSpace (Y i))
      (_ : ∀ i, IsLocallyNoetherian (Y i)) (_ : ∀ i, IsNormal (Y i))
      (KY : ∀ i, Divisor (Y i)) (ΔY : ∀ i, QDivisor (Y i)) (DY : ∀ i, Divisor (Y i))
      (T : ℕ → Scheme.{0}) (sT : ∀ i, T i ⟶ Spec (.of ℂ)) (φ : ∀ i, modelSeq X Y i ⟶ T i)
      (φp : ∀ i, Y i ⟶ T i) (p : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i < m, IsTrivialFlop ℂ (modelStr sX sY i) (sY i) (sT i) 3 (divisorSeq K KY i)
          (divisorSeq Δ ΔY i) (φ i) (φp i) (p i) ∧
        KY i = RationalMap.transformDivisor (p i) (divisorSeq K KY i) ∧
        ΔY i = flopDivisor (p i) (divisorSeq Δ ΔY i) ∧
        DY i = RationalMap.transformDivisor (p i)
          (divisorSeq (Finsupp.single D 1 : Divisor X) DY i)) ∧
      ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (c : modelSeq X Y m ⟶ X')
        (_ : IsIntegral X') (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
        (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX'),
        IsBirationalContraction ℂ sX' (modelStr sX sY m) c ∧ IsBirationalMorphism c ∧
        exceptionalSet c =
          ((divisorSeq (Finsupp.single D 1 : Divisor X) DY m).supp : Set (modelSeq X Y m)) ∧
        (∃ (hc : ∀ Z : irreducibleComponents (modelSeq X Y m),
            c (componentGenericPoint (modelSeq X Y m) Z) ∉
              (Divisor.toQDivisor (RationalMap.transformDivisor c.toRationalMap
                (divisorSeq K KY m)) +
                RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).supp)
            (B : QDivisor (modelSeq X Y m)),
          (Divisor.toQDivisor (RationalMap.transformDivisor c.toRationalMap (divisorSeq K KY m)) +
              RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).IsPullback c hc B ∧
            (Divisor.toQDivisor (divisorSeq K KY m) + divisorSeq Δ ΔY m).QLinearlyEquivalent B) ∧
        picardNumber sX' + 1 = picardNumber sX ∧
        SatisfiesAbundanceAssumptions ℂ sX'
          (RationalMap.transformDivisor c.toRationalMap (divisorSeq K KY m))
          (RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)) :=
    by revert X sX K Δ hA hL D hD; first | exact Proof_lem_fa15_trivially_connected_becomes_contractible.solution | exact Proof_lem_fa15_trivially_connected_becomes_contractible.solution _ | exact Proof_lem_fa15_trivially_connected_becomes_contractible.solution _ _ | exact Proof_lem_fa15_trivially_connected_becomes_contractible.solution _ _ _ | exact Proof_lem_fa15_trivially_connected_becomes_contractible.solution _ _ _ _

end MMP.Flips

