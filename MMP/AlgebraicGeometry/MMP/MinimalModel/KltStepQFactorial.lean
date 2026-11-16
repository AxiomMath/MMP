module

public import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
public import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

section

/-!
# Steps of the program from a `ℚ`-factorial klt pair are `ℚ`-factorial

A klt pair with effective boundary is dlt, so the step of a negative extremal ray of a projective
`ℚ`-factorial klt pair is an elementary dlt step, whose output is `ℚ`-factorial. A contraction
whose exceptional set is a prime divisor is not small, so it falls in the divisorial branch of
the elementary step; a flip falls in the small branch.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Cor. 3.44.
-/

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace MMP.Fourfold

/-- A projective `ℚ`-factorial klt pair with rational boundary is a projective `ℚ`-factorial dlt
pair. -/
private theorem isProjectiveQFactorialDltPair_of_isKltPair {k : Type} [Field k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {K : Divisor X} {B : QDivisor X}
    (hB : MMP.Fourfold.IsKltPair sX B) (hXp : MMP.Mori.IsProjectiveVariety k sX)
    (hXQ : IsQFactorial sX) (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) :
    IsProjectiveQFactorialDltPair sX K B := by
  have := hB.1.isAlgClosed
  have := hB.1.charZero
  obtain ⟨n, hn⟩ := hK
  have hkm : MMP.Mori.IsKltPair sX n K B := (isKltPair_iff_mori_isKltPair sX hn hB.1).mp hB
  have hdlt := (MMP.Threefold.Mori.IsKltPair.isDltPair hkm hB.1.nonneg).1
  exact ⟨hXp, hXQ, ⟨n, hn⟩, (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hn B).mpr hdlt⟩

/-- A morphism whose exceptional set is the support of a prime divisor is not small. -/
private theorem not_isSmallMorphism_of_exceptionalSet_eq_support {k : Type} [Field k]
    {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z}
    {E : MMP.Mori.PrimeDivisor X} (hE : (MMP.Mori.exceptionalSet f : Set X) = E.support) :
    ¬ IsSmallMorphism sX sZ f := by
  intro hs
  have hmem : E.genericPoint ∈ (exceptionalSet f : Set X) := by
    rw [hE, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl
  have h2 := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hs.two_le_codimension hmem
  rw [E.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

end MMP.Fourfold

end

section

/-!
# Steps of the program from a `ℚ`-factorial klt pair are `ℚ`-factorial

Let `(X, B)` be a projective `ℚ`-factorial klt pair with a `ℚ`-boundary and canonical divisor
`K`, let `R` be a `(K + B)`-negative extremal ray of `NE̅(X)` and let `f : X ⟶ Z` be the
contraction of `R`, assumed birational. If `f` is divisorial (its exceptional set is a prime
divisor of `X`), then `Z` is `ℚ`-factorial; and if `f⁺ : X⁺ ⟶ Z` is a `(K + B)`-flip of `f`
(so `f` is small), then `X⁺` is `ℚ`-factorial.

## Main results

* `MMP.Fourfold.IsKltPair.isQFactorial_of_isContractionOfRay`.

## Implementation notes

The source works over `ℂ`; the statement is made over any field `k`, the klt condition
`MMP.Fourfold.IsKltPair` already forcing `k` to be algebraically closed of characteristic zero.
The two cases of the step are stated as the two halves of one conjunction: the divisorial case
is the hypothesis that `Ex(f)` is the support of a prime divisor, the flip case quantifies over
all `(K + B)`-flips `MMP.Fourfold.IsFlipOf` of `f`, which carry the smallness of `f`.

## References

* [KM98] J. Kollár, S. Mori, *Birational geometry of algebraic varieties*, Prop. 3.36, 3.37.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **Projective klt steps preserve `ℚ`-factoriality.** Let `(X, B)` be a projective
`ℚ`-factorial klt pair, `K` a canonical divisor of `X`, `R` a `(K + B)`-negative extremal ray of
`NE̅(X)` and `f : X ⟶ Z` its contraction, birational. If `Ex(f)` is a prime divisor of `X`, then
`Z` is `ℚ`-factorial; and the source `X⁺` of every `(K + B)`-flip `f⁺ : X⁺ ⟶ Z` of `f` is
`ℚ`-factorial. -/
@[mmp "lem_fourfold_klt_step_qfactorial"]
public theorem IsKltPair.isQFactorial_of_isContractionOfRay {k : Type} [Field k]
    {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z]
    {K : Divisor X} {B : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hB : IsKltPair sX B) (hXp : MMP.Mori.IsProjectiveVariety k sX) (hXQ : IsQFactorial sX)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hf : IsContractionOfRay sX sZ R f) (hfb : IsBirationalMorphism f) :
    ((∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) →
        IsQFactorial sZ) ∧
      ∀ (X' : Scheme.{0}) (sX' : X' ⟶ Spec (.of k)) [CompactSpace X'] [IsLocallyNoetherian X']
        [IsNormal X'] (fp : X' ⟶ Z), IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp →
          IsQFactorial sX' := by
  have := hB.1.isAlgClosed
  have := hB.1.charZero
  have hP := isProjectiveQFactorialDltPair_of_isKltPair hB hXp hXQ hK
  refine ⟨fun ⟨E, hE⟩ => ?_, fun X' sX' _ _ _ fp hflip => ?_⟩
  · have hns : ¬ IsSmallMorphism sX sZ f := not_isSmallMorphism_of_exceptionalSet_eq_support hE
    have hZ := hf.isNormalVariety_target.1
    have : IsIntegral Z := hZ.toIsIntegral
    have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
    exact (show IsProjectiveElementaryDltStep sX sZ sZ K B R f (𝟙 Z) (flipTransform f (𝟙 Z) B) from
      ⟨hP, hR, hf, hfb, Category.id_comp _, rfl,
        Or.inr ⟨hns, inferInstance⟩⟩).isQFactorial_and_isDltPair.1
  · have : IsIntegral X' := hflip.isSmallMorphism_flip.isNormalVariety_source.1.toIsIntegral
    exact (show IsProjectiveElementaryDltStep sX sZ sX' K B R f fp (flipTransform f fp B) from
      ⟨hP, hR, hf, hfb, hflip.isSmallMorphism_flip.comp_eq, rfl,
        Or.inl ⟨hflip.isSmallMorphism, hflip⟩⟩).isQFactorial_and_isDltPair.1

end MMP.Fourfold

end
