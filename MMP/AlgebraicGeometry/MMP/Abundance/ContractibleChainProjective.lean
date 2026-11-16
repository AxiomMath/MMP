module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.TriviallyConnectedContractible
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Threefold.EffectiveDivisorFlopTermination
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.ContractibleChainTargets

/-!
# The contracting chain of FA 15.9 has projective models and flop targets

Let `(X, Δ)` satisfy the assumptions of the abundance theorem FA 15.4, with `L = K + Δ` not
eventually free and composed of a pencil, and let `D` be an `L`-trivially connected prime
divisor. The construction of FA 15.9
(`MMP.Flips.IsTriviallyConnected.exists_isBirationalContraction_of_satisfiesAbundanceAssumptions`)
produces flops `X = X₀ ⤏ X₁ ⤏ ⋯ ⤏ X_m` of `(K_i + Δ_i)`-trivial flop data
`φ_i : X_i ⟶ T_i ⟵ X_{i+1} : φ_i⁺`, followed by a birational contraction `c : X_m ⟶ X'` of the
transform of `D`. The flopping contractions are contractions of extremal rays of projective
varieties, so the chain can be chosen with every model `X_i` and every base `T_i` a normal
projective variety. Then on each base the adjoint `K_{T_i} + Δ_{T_i}` is `ℚ`-Cartier and pulls
back to both `K_i + Δ_i` and `K_{i+1} + Δ_{i+1}`, so eventual freeness, and being eventually free
and composed of a pencil, pass in both directions through every flop.

## Main results

* `exists_isBirationalContraction_isProjectiveVariety_of_satisfiesAbundanceAssumptions` (in the
  namespace `MMP.Flips.IsTriviallyConnected`): the chain of FA 15.9 can be chosen with every model
  and every flop base a normal projective variety, the adjoints of each flop descending to a common
  Cartier divisor on its base, and eventual freeness preserved in both directions through each
  flop.

## Implementation notes

The chain is encoded as in
`MMP.Flips.IsTriviallyConnected.exists_isBirationalContraction_of_satisfiesAbundanceAssumptions`,
through `MMP.Fourfold.modelSeq`, `MMP.Fourfold.modelStr` and `MMP.Fourfold.divisorSeq`, and all of
its conclusions are repeated. The common descent of the two adjoints of the `i`-th flop is a
Cartier divisor `M` on `T_i` with `M = r (φ_{i*} K_i + φ_{i*} Δ_i)` for some `r > 0`, whose
pull-backs (`MMP.Mori.Divisor.IsPullback`) along `φ_i` and `φ_i⁺` are `r (K_i + Δ_i)` and
`r (K_{i+1} + Δ_{i+1})`. The statement is over `ℂ`, as in the source.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.4.4, 15.9
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP MMP.Fourfold MMP.Flips
open MMP.Mori hiding exceptionalSet

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_lem_fourfold_fa15_contractible_chain_projective_targets

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
      (T : ℕ → Scheme.{0}) (sT : ∀ i, T i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (T i)) (_ : ∀ i, CompactSpace (T i))
      (_ : ∀ i, IsLocallyNoetherian (T i)) (_ : ∀ i, IsNormal (T i))
      (φ : ∀ i, modelSeq X Y i ⟶ T i)
      (φp : ∀ i, Y i ⟶ T i) (p : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ m, Mori.IsProjectiveVariety ℂ (modelStr sX sY i)) ∧
      (∀ i < m, IsTrivialFlop ℂ (modelStr sX sY i) (sY i) (sT i) 3 (divisorSeq K KY i)
          (divisorSeq Δ ΔY i) (φ i) (φp i) (p i) ∧
        KY i = RationalMap.transformDivisor (p i) (divisorSeq K KY i) ∧
        ΔY i = flopDivisor (p i) (divisorSeq Δ ΔY i) ∧
        DY i = RationalMap.transformDivisor (p i)
          (divisorSeq (Finsupp.single D 1 : Divisor X) DY i) ∧
        Mori.IsProjectiveVariety ℂ (sT i) ∧
        (∃ r : ℕ, 0 < r ∧ ∃ M : Divisor (T i), M.IsCartier ∧
          Divisor.toQDivisor M = (r : ℤ) •
            (Divisor.toQDivisor (RationalMap.transformDivisor (φ i).toRationalMap
              (divisorSeq K KY i)) + flopBaseDivisor (φ i) (divisorSeq Δ ΔY i)) ∧
          (∃ (MX : Divisor (modelSeq X Y i)) (hB : ∀ Z : irreducibleComponents (modelSeq X Y i),
              φ i (componentGenericPoint (modelSeq X Y i) Z) ∉ M.supp),
            Divisor.toQDivisor MX =
                (r : ℤ) • (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ∧
              M.IsPullback (φ i) hB MX) ∧
          (∃ (MY : Divisor (Y i)) (hB : ∀ Z : irreducibleComponents (Y i),
              φp i (componentGenericPoint (Y i) Z) ∉ M.supp),
            Divisor.toQDivisor MY = (r : ℤ) • (Divisor.toQDivisor (KY i) + ΔY i) ∧
              M.IsPullback (φp i) hB MY)) ∧
        (IsEventuallyFree ℂ (modelStr sX sY i)
            (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ↔
          IsEventuallyFree ℂ (sY i) (Divisor.toQDivisor (KY i) + ΔY i)) ∧
        (IsEventuallyFreePencil ℂ (modelStr sX sY i)
            (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ↔
          IsEventuallyFreePencil ℂ (sY i) (Divisor.toQDivisor (KY i) + ΔY i))) ∧
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
  IsTriviallyConnected.exists_isBirationalContraction_isProjectiveVariety_of_hFlopSequencesTerminate
    MMP.Fourfold.hFlopSequence_length_lt_top hA hL hD

end Proof_lem_fourfold_fa15_contractible_chain_projective_targets

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Flips

open MMP.Mori MMP.Fourfold

/-- **The contracting chain of FA 15.9 with projective flop targets.** Let `(X, Δ)` satisfy the
assumptions of FA 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`) over `ℂ`, with `K + Δ` not
eventually free and composed of a pencil (`MMP.Flips.IsEventuallyFreePencil`), and let `D` be a
`(K + Δ)`-trivially connected prime divisor (`MMP.Flips.IsTriviallyConnected`).

Then the conclusions of
`MMP.Flips.IsTriviallyConnected.exists_isBirationalContraction_of_satisfiesAbundanceAssumptions`
hold for a chain of flops `p_i : X_i ⤏ X_{i+1}` of trivial flop data `φ_i : X_i ⟶ T_i`,
`φ_i⁺ : X_{i+1} ⟶ T_i` (`i < m`) and a contraction `c : X_m ⟶ X'`, in which moreover:
* every model `X_i` (`i ≤ m`) is a normal projective variety, and every base `T_i` (`i < m`) is
  a normal projective variety;
* for each `i < m` there are `r > 0` and a Cartier divisor `M` on `T_i` with
  `M = r (φ_{i*} K_i + φ_{i*} Δ_i)`, `φ_i^* M = r (K_i + Δ_i)` and
  `φ_i⁺^* M = r (K_{i+1} + Δ_{i+1})`;
* for each `i < m`, `K_i + Δ_i` is eventually free (`MMP.Flips.IsEventuallyFree`) iff
  `K_{i+1} + Δ_{i+1}` is, and eventually free and composed of a pencil iff `K_{i+1} + Δ_{i+1}`
  is. -/
@[mmp "lem_fourfold_fa15_contractible_chain_projective_targets"]
public theorem
    IsTriviallyConnected.exists_isBirationalContraction_isProjectiveVariety_of_satisfiesAbundanceAssumptions
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
      (T : ℕ → Scheme.{0}) (sT : ∀ i, T i ⟶ Spec (.of ℂ))
      (_ : ∀ i, IsIntegral (T i)) (_ : ∀ i, CompactSpace (T i))
      (_ : ∀ i, IsLocallyNoetherian (T i)) (_ : ∀ i, IsNormal (T i))
      (φ : ∀ i, modelSeq X Y i ⟶ T i)
      (φp : ∀ i, Y i ⟶ T i) (p : ∀ i, (modelSeq X Y i).RationalMap (Y i)),
      (∀ i ≤ m, Mori.IsProjectiveVariety ℂ (modelStr sX sY i)) ∧
      (∀ i < m, IsTrivialFlop ℂ (modelStr sX sY i) (sY i) (sT i) 3 (divisorSeq K KY i)
          (divisorSeq Δ ΔY i) (φ i) (φp i) (p i) ∧
        KY i = RationalMap.transformDivisor (p i) (divisorSeq K KY i) ∧
        ΔY i = flopDivisor (p i) (divisorSeq Δ ΔY i) ∧
        DY i = RationalMap.transformDivisor (p i)
          (divisorSeq (Finsupp.single D 1 : Divisor X) DY i) ∧
        Mori.IsProjectiveVariety ℂ (sT i) ∧
        (∃ r : ℕ, 0 < r ∧ ∃ M : Divisor (T i), M.IsCartier ∧
          Divisor.toQDivisor M = (r : ℤ) •
            (Divisor.toQDivisor (RationalMap.transformDivisor (φ i).toRationalMap
              (divisorSeq K KY i)) + flopBaseDivisor (φ i) (divisorSeq Δ ΔY i)) ∧
          (∃ (MX : Divisor (modelSeq X Y i)) (hB : ∀ Z : irreducibleComponents (modelSeq X Y i),
              φ i (componentGenericPoint (modelSeq X Y i) Z) ∉ M.supp),
            Divisor.toQDivisor MX =
                (r : ℤ) • (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ∧
              M.IsPullback (φ i) hB MX) ∧
          (∃ (MY : Divisor (Y i)) (hB : ∀ Z : irreducibleComponents (Y i),
              φp i (componentGenericPoint (Y i) Z) ∉ M.supp),
            Divisor.toQDivisor MY = (r : ℤ) • (Divisor.toQDivisor (KY i) + ΔY i) ∧
              M.IsPullback (φp i) hB MY)) ∧
        (IsEventuallyFree ℂ (modelStr sX sY i)
            (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ↔
          IsEventuallyFree ℂ (sY i) (Divisor.toQDivisor (KY i) + ΔY i)) ∧
        (IsEventuallyFreePencil ℂ (modelStr sX sY i)
            (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i) ↔
          IsEventuallyFreePencil ℂ (sY i) (Divisor.toQDivisor (KY i) + ΔY i))) ∧
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
      by revert X sX K Δ hA hL D hD; first | exact Proof_lem_fourfold_fa15_contractible_chain_projective_targets.solution | exact Proof_lem_fourfold_fa15_contractible_chain_projective_targets.solution _ | exact Proof_lem_fourfold_fa15_contractible_chain_projective_targets.solution _ _ | exact Proof_lem_fourfold_fa15_contractible_chain_projective_targets.solution _ _ _ | exact Proof_lem_fourfold_fa15_contractible_chain_projective_targets.solution _ _ _ _

end MMP.Flips

