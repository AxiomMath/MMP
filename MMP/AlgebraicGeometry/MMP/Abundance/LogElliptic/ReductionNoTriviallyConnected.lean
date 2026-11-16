module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Abundance.Defs
public import MMP.AlgebraicGeometry.MMP.Abundance.LogElliptic.ContractibleChainTargets
public import MMP.AlgebraicGeometry.MMP.Flip.TrivialFlopPullback
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Positivity.FreePencilCrepant
import MMP.AlgebraicGeometry.Intersection.N1FiniteDimensionalProjective
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Valuation
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent

/-!
# Reduction to pairs without trivially connected prime divisors

Let `(X, Δ_X)` satisfy the assumptions of the abundance theorem FA 15.4 over `ℂ` and put
`L = K_X + Δ_X`. Granted the termination of `H`-flops, either `L` is eventually free and composed
of a pencil, or there is a pair `(X', Δ_{X'})`, again satisfying the assumptions of FA 15.4, on
which no prime divisor is `(K_{X'} + Δ_{X'})`-trivially connected, and such that `L` is
eventually free as soon as `K_{X'} + Δ_{X'}` is. This reduces the abundance theorem for log
elliptic threefolds to pairs without trivially connected prime divisors (FA 15.9).

The proof is by induction on the Picard number `ρ(X)`, which is finite since `X` is projective.
If `L` is not eventually free and composed of a pencil and `D` is an `L`-trivially connected prime
divisor, a chain of `L`-trivial flops followed by the contraction of the transform of `D` reaches
a pair `(X'', Δ'')` satisfying the assumptions of FA 15.4 with `ρ(X'') = ρ(X) - 1`. Eventual
freeness, and being eventually free and composed of a pencil, pass in both directions through
every flop and through the crepant contraction, so the induction hypothesis for `(X'', Δ'')`
gives the result for `(X, Δ_X)`.

## Main results

* `isEventuallyFreePencil_or_exists_forall_not_isTriviallyConnected_of_hFlopSequencesTerminate`
  (in `MMP.Flips.SatisfiesAbundanceAssumptions`): granted the termination of `H`-flops, either
  `K_X + Δ_X` is eventually free and composed of a pencil, or there is a pair `(X', Δ_{X'})`
  satisfying the assumptions of FA 15.4 with no `(K_{X'} + Δ_{X'})`-trivially connected prime
  divisor, whose eventual freeness implies that of `K_X + Δ_X`.

## Implementation notes

The result is stated over `ℂ`, with the termination of `H`-flops
(`MMP.Flips.HFlopSequencesTerminate`) as a hypothesis; the chain of flops is
`exists_isBirationalContraction_isProjectiveVariety_of_hFlopSequencesTerminate` in
`MMP.Flips.IsTriviallyConnected`. FA's "`(X', Δ_{X'})` is log birational to `(X, Δ_X)`" is
replaced by what the proof of FA 15.13 uses of it: that eventual freeness of `K_{X'} + Δ_{X'}`
implies that of `K_X + Δ_X`. Trivial connectedness is asserted for prime divisors `E`, as the
divisors `Finsupp.single E 1`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 15.4, 15.6,
  15.9
-/

public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori MMP.Fourfold

/-- The conclusion of FA Cor. 15.9 for the pair `(X, Δ)` over `ℂ`. -/
private abbrev ReductionHolds {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ))
    [IsLocallyNoetherian X] [IsNormal X] (K : Divisor X) (Δ : QDivisor X) : Prop :=
  IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ) ∨
    ∃ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of ℂ)) (_ : IsIntegral X')
      (_ : IsLocallyNoetherian X') (_ : IsNormal X') (_ : CompactSpace X')
      (_ : LocallyOfFiniteType sX') (_ : QuasiCompact sX') (K' : Divisor X')
      (Δ' : QDivisor X'),
      SatisfiesAbundanceAssumptions ℂ sX' K' Δ' ∧
        (∀ E : Mori.PrimeDivisor X',
          ¬ IsTriviallyConnected ℂ sX' 3 K' Δ' (Finsupp.single E 1)) ∧
        (IsEventuallyFree ℂ sX' (Divisor.toQDivisor K' + Δ') →
          IsEventuallyFree ℂ sX (Divisor.toQDivisor K + Δ))

/-- A property equivalent at each step `i ↦ i + 1` of a chain of length `m` is equivalent at its
two ends. -/
private theorem iff_of_forall_lt_iff_succ {P : ℕ → Prop} :
    ∀ {m : ℕ}, (∀ i < m, (P i ↔ P (i + 1))) → (P 0 ↔ P m)
  | 0, _ => Iff.rfl
  | m + 1, h => (iff_of_forall_lt_iff_succ fun i hi => h i (by omega)).trans (h m (by omega))

private theorem reductionHolds_of_picardNumber_eq (hterm : HFlopSequencesTerminate) (n : ℕ) :
    ∀ {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
      [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [QuasiCompact sX]
      {K : Divisor X} {Δ : QDivisor X}, SatisfiesAbundanceAssumptions ℂ sX K Δ →
      picardNumber sX = n → ReductionHolds sX K Δ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X sX _ _ _ _ _ _ K Δ h hρ
  by_cases hP : IsEventuallyFreePencil ℂ sX (Divisor.toQDivisor K + Δ)
  · exact Or.inl hP
  right
  by_cases hD : ∃ D : Mori.PrimeDivisor X,
      IsTriviallyConnected ℂ sX 3 K Δ (Finsupp.single D 1)
  swap
  · simp only [not_exists] at hD
    exact ⟨X, sX, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, K, Δ, h, hD, id⟩
  obtain ⟨D, hD⟩ := hD
  obtain ⟨m, Y, sY, _, _, _, _, KY, ΔY, DY, T, sT, _, _, _, _, φ, φp, p, hproj, hflop,
      X'', sX'', c, _, _, _, _, _, _, hc, -, -, ⟨hcB, B, hB, hLB⟩, hρ'', hA''⟩ :=
    IsTriviallyConnected.exists_isBirationalContraction_isProjectiveVariety_of_hFlopSequencesTerminate
      hterm h hP hD
  have hLq : ∀ i ≤ m,
      (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i).IsQCartier := by
    rintro (_ | j) hj
    · exact h.isQCartier
    · obtain ⟨hfl, -, -, -, -, ⟨r, hr, M, hMc, -, -, ⟨MY, hBY, hMY, hpb⟩⟩, -⟩ :=
        hflop j (by omega)
      haveI : IsDominant (φp j) := hfl.1.isBirationalMorphism_flop.isDominant
      exact ⟨r, by exact_mod_cast hr.ne', MY, hMY, isCartier_of_isPullback (φp j) hMc hpb⟩
  have hN := hA''.isQCartier
  have hLN : ∃ hB' : ∀ Z : irreducibleComponents (modelSeq X Y m),
      c (componentGenericPoint (modelSeq X Y m) Z) ∉
        (Divisor.toQDivisor (RationalMap.transformDivisor c.toRationalMap
          (divisorSeq K KY m)) +
          RationalMap.transformDivisor c.toRationalMap (divisorSeq Δ ΔY m)).supp,
      (Divisor.toQDivisor (divisorSeq K KY m) + divisorSeq Δ ΔY m).QLinearlyEquivalent
        (QDivisor.pullback _ hN hB') :=
    ⟨hcB, by rw [hB.pullback_eq hN]; exact hLB⟩
  haveI := hc.isProper
  have hEFc := isEventuallyFree_iff_of_qLinearlyEquivalent_pullback ℂ (modelStr sX sY m) sX''
    ⟨hc.isVariety_source, inferInstance⟩ hA''.isQFactorial.1 c hc.comp_eq hc.isIso_app hN hLN
  have hPc := isEventuallyFreePencil_iff_of_qLinearlyEquivalent_pullback ℂ (modelStr sX sY m)
    sX'' (hproj m le_rfl) hA''.isProjectiveVariety c hc.comp_eq hc.isIso_app (hLq m le_rfl) hN
    hLN
  have hEFf := iff_of_forall_lt_iff_succ (m := m) (P := fun i =>
    IsEventuallyFree ℂ (modelStr sX sY i)
      (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i))
    fun i hi => (hflop i hi).2.2.2.2.2.2.1
  have hPf := iff_of_forall_lt_iff_succ (m := m) (P := fun i =>
    IsEventuallyFreePencil ℂ (modelStr sX sY i)
      (Divisor.toQDivisor (divisorSeq K KY i) + divisorSeq Δ ΔY i))
    fun i hi => (hflop i hi).2.2.2.2.2.2.2
  obtain ⟨n'', hn''⟩ : ∃ n'' : ℕ, (n'' : ℕ∞) = picardNumber sX'' := by
    refine ENat.ne_top_iff_exists.mp fun htop => ?_
    rw [htop, hρ, top_add] at hρ''
    exact ENat.top_ne_coe n hρ''
  have hlt : n'' < n := by
    rw [hρ, ← hn''] at hρ''
    have : n'' + 1 = n := by exact_mod_cast hρ''
    omega
  rcases ih n'' hlt hA'' hn''.symm with
    hP'' | ⟨X', sX', i1, i2, i3, i4, i5, i6, K', Δ', hA', hnot, himp⟩
  · exact absurd (hPf.mpr (hPc.mpr hP'')) hP
  · exact ⟨X', sX', i1, i2, i3, i4, i5, i6, K', Δ', hA', hnot,
      fun hEF => hEFf.mpr (hEFc.mpr (himp hEF))⟩

/-- **Reduction to no trivially connected prime divisors** (FA Cor. 15.9). Assume that sequences
of `H`-flops terminate (`MMP.Flips.HFlopSequencesTerminate`). Let `(X, Δ)`, with `K` a canonical
divisor, satisfy the assumptions of FA 15.4 (`MMP.Flips.SatisfiesAbundanceAssumptions`) over
`ℂ`, and let `L = K + Δ`. Then either
* (15.9.1) `L` is eventually free and composed of a pencil (`MMP.Flips.IsEventuallyFreePencil`),
  or
* (15.9.2) there is a pair `(X', Δ')`, with `K'` a canonical divisor, satisfying the assumptions
  of FA 15.4, such that no prime divisor of `X'` is `(K' + Δ')`-trivially connected
  (`MMP.Flips.IsTriviallyConnected`), and such that `L` is eventually free
  (`MMP.Flips.IsEventuallyFree`) if `K' + Δ'` is. -/
public theorem
    SatisfiesAbundanceAssumptions.isEventuallyFreePencil_or_exists_forall_not_isTriviallyConnected_of_hFlopSequencesTerminate
    (hterm : HFlopSequencesTerminate) {X : Scheme.{0}}
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
            IsEventuallyFree ℂ sX (Divisor.toQDivisor K + Δ)) := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := h.isProjectiveVariety
  have := NumericalCurveClasses.finiteDimensional_of_isProjectiveVariety sX
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = picardNumber sX :=
    ENat.ne_top_iff_exists.mp
      (Cardinal.toENat_lt_top.mpr (Module.rank_lt_aleph0 ℝ _)).ne
  exact reductionHolds_of_picardNumber_eq hterm n h hn.symm

end MMP.Flips
