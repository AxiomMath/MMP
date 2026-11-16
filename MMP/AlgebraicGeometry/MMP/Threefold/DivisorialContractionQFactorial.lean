module

public import MMP.AlgebraicGeometry.MMP.MinimalModel.KltStepQFactorial
public import MMP.AlgebraicGeometry.MMP.Abundance.FiniteRepresentationGeneration

/-!
# The target of a klt divisorial contraction of a `ℚ`-factorial threefold is `ℚ`-factorial

Let `(X, Θ)` be a klt log variety in the sense of Kollár et al. (every log discrepancy of a
divisor with nonempty center on `X` is positive), with `Θ` a `ℚ`-divisor, where `X` is a
projective `ℚ`-factorial threefold over an algebraically closed field of characteristic zero.
Let `K` be a canonical divisor of `X`, `R` a `(K + Θ)`-negative extremal ray of `NE̅(X)` and
`f : X ⟶ Z` the contraction of `R` onto a normal variety `Z`. If `f` is divisorial, that is,
birational with exceptional set a prime divisor of `X`, then `Z` is `ℚ`-factorial.

## Main results

* `MMP.Flips.IsKawamataLogTerminal.isQFactorial_of_isContractionOfRay`.

## Implementation notes

The source works over `ℂ`; the statement is made over any algebraically closed field of
characteristic zero. The klt condition is `MMP.Flips.IsKawamataLogTerminal` of the `ℝ`-divisor
underlying `Θ`; the extremal ray, the contraction and `ℚ`-factoriality are those of
`MMP.Fourfold.IsKltPair.isQFactorial_of_isContractionOfRay`, so that statement applies to the
same data once the two klt conditions are identified.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Ch. 15
* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Prop. 3.36.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori MMP.Fourfold

private lemma isKltPair_of_isKawamataLogTerminal {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [LocallyOfFiniteType sX] {n : ℕ} {K : Divisor X}
    {Θ : QDivisor X} (hklt : IsKawamataLogTerminal sX n K (QDivisor.toRDivisor Θ))
    (hKΘ : (Divisor.toQDivisor K + Θ).IsQCartier) : MMP.Fourfold.IsKltPair sX Θ := by
  have hX : IsNormalVariety k sX := hklt.1.isNormalVariety
  refine (isKltPair_iff_mori_isKltPair sX hklt.2.1 ⟨‹_›, ‹_›, ⟨hX, n, K, hklt.2.1, hKΘ⟩,
    fun P => by simpa [QDivisor.coeff_toRDivisor] using (hklt.1.isBoundary P).1⟩).mpr
    ((isKawamataLogTerminal_iff_isKltPair sX n K Θ hX hklt.2.1 hklt.1.isBoundary hKΘ).mp hklt)

/-- **Divisorial contractions of klt `ℚ`-factorial projective threefolds have `ℚ`-factorial
targets.** Let `X` be a projective `ℚ`-factorial threefold over an algebraically closed field of
characteristic zero, `Θ` a `ℚ`-divisor and `K` a canonical divisor such that `(X, Θ)` is klt
(`MMP.Flips.IsKawamataLogTerminal`). Let `R` be a `(K + Θ)`-negative extremal ray and
`f : X ⟶ Z` its contraction (`MMP.Fourfold.IsContractionOfRay`) onto a normal `Z`. If `f` is
birational and its exceptional set is a prime divisor of `X`, then `Z` is `ℚ`-factorial. -/
@[mmp "lem_fourfold_fa15_projective_divisorial_qfactorial"]
public theorem IsKawamataLogTerminal.isQFactorial_of_isContractionOfRay {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] [LocallyOfFiniteType sX] [IsLocallyNoetherian Z] [IsNormal Z]
    {K : Divisor X} {Θ : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hklt : IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor Θ))
    (hXp : MMP.Mori.IsProjectiveVariety k sX) (hXQ : IsQFactorial sX)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Θ) R)
    (hf : IsContractionOfRay sX sZ R f) (hfb : IsBirationalMorphism f)
    (hE : ∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) :
    IsQFactorial sZ :=
  ((isKltPair_of_isKawamataLogTerminal hklt hR.1).isQFactorial_of_isContractionOfRay hXp hXQ
    ⟨3, hklt.2.1⟩ hR hf hfb).1 hE

end MMP.Flips

end
