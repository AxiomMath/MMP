module

public import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContraction
public import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary

section

/-!
# Contractions of negative extremal rays of projective `ℚ`-factorial dlt pairs

Let `(U, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field `k` of
characteristic zero, with `Δ` a `ℚ`-divisor and `K` a canonical divisor of `U`. Every
`(K + Δ)`-negative extremal ray `R` of `NE̅(U)` has a contraction: a projective surjective
morphism `f : U ⟶ V` onto a normal projective variety with `f_* 𝒪_U = 𝒪_V`, contracting exactly
the integral curves whose class lies in `R`, with `ρ(U/V) = 1` and `-(K + Δ)` relatively ample
over `V`.

The proof perturbs `Δ` to the klt boundary `Δ - ε⌊Δ⌋`, for which `R` is still negative, applies
the klt contraction theorem `MMP.Fourfold.exists_isContractionOfRay_of_isKltPair`, and recovers
relative ampleness of `-(K + Δ)` from `ρ(U/V) = 1` and the relative Kleiman criterion.

## Main results

* `MMP.Fourfold.IsProjectiveQFactorialDltPair.exists_isContractionOfRay`: the statement above.

## Implementation notes

* The pair is `MMP.Fourfold.IsProjectiveQFactorialDltPair`; the ray is
  `MMP.Fourfold.IsNegativeExtremalRayOf` for the `ℚ`-Cartier divisor `K + Δ`.
* The contraction is `MMP.Fourfold.IsContractionOfRay` (projectivity and surjectivity of `f`,
  normality of `V`, `f_* 𝒪_U = 𝒪_V`), the target is projective
  (`MMP.Mori.IsProjectiveVariety`), the relative Picard number is
  `MMP.Fourfold.relativePicardNumberN1`, and relative ampleness is
  `MMP.Mori.QDivisor.HasRelativelyAmpleMultiple`.
* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero, which contains the complex case.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.7
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

/-- **Contraction of a negative extremal ray of a projective `ℚ`-factorial dlt pair.** Let
`(U, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field of
characteristic zero, with `Δ` a `ℚ`-divisor and `K` a canonical divisor. Every `(K + Δ)`-negative
extremal ray `R` of `NE̅(U)` has a contraction `f : U ⟶ V` onto a normal projective variety `V`
with `f_* 𝒪_U = 𝒪_V`, `ρ(U/V) = 1` and `-(K + Δ)` `f`-ample. -/
@[mmp "lem_oai4_dlt_elementary"]
public theorem IsProjectiveQFactorialDltPair.exists_isContractionOfRay
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {U : Scheme.{0}} [IsIntegral U]
    [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U] {sU : U ⟶ Spec (.of k)}
    {K : Divisor U} {Δ : QDivisor U} (hU : IsProjectiveQFactorialDltPair sU K Δ)
    {R : Set (NumericalCurveClasses sU)}
    (hR : IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R) :
    ∃ (V : Scheme.{0}) (sV : V ⟶ Spec (.of k)) (f : U ⟶ V),
      IsContractionOfRay sU sV R f ∧ MMP.Mori.IsProjectiveVariety k sV ∧
        relativePicardNumberN1 sU f = 1 ∧
        (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f := by
  obtain ⟨ε, -, hklt, hRε⟩ := hU.exists_isKltPair_sub_smul_roundDown hR
  obtain ⟨n, hn⟩ := hU.isCanonicalDivisor
  obtain ⟨-, V, sV, f, hf, hV, hρ, -⟩ :=
    exists_isContractionOfRay_of_isKltPair sU hU.isProjectiveVariety hklt hn hRε
  refine ⟨V, sV, f, hf, hV, hρ, ?_⟩
  obtain ⟨hQ, hext, hneg⟩ := hR
  refine hasRelativelyAmpleMultiple_neg_of_isExtremalRay sU sV hf.isNormalVariety_source
    hU.isProjectiveVariety hV hU.isCanonicalDivisor hQ hext (fun v hv hv0 => ?_) f hf.comp_eq
    (fun C hC => (hf.isContractedBy_iff C).1 hC)
  simpa [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply] using hneg v hv hv0

end MMP.Fourfold

end
