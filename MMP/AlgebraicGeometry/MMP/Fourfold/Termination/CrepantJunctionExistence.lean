module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
public import MMP.AlgebraicGeometry.MMP.Fourfold.Extraction.Projective

/-!
# Existence of crepant junctions

Let `(X, B)` be a projective klt fourfold pair over `ℂ`, with `B` an effective `ℚ`-divisor, and
let `I` be a finite set of normalized divisorial valuations of `k(X)`, exceptional over `X`, with
log discrepancy `a(s; X, B) ≤ 1` for every `s ∈ I`. Then there is a crepant junction of `(X, B)`
extracting `I`: a projective birational morphism `p : Y ⟶ X` from a normal projective
`ℚ`-factorial fourfold whose exceptional prime divisors are exactly the centres `E_s` of the
valuations `s ∈ I`, with the boundary `Θ = p⁻¹_* B + ∑_{s ∈ I} (1 - a(s; X, B)) E_s`.

## Main results

* `MMP.Fourfold.nonempty_fourfoldCrepantJunction`: a crepant junction of `(X, B)` extracting `I`
  exists.

## Implementation notes

The condition on `I` is `I ⊆ I(X, B)` (`MMP.Fourfold.lowDiscrepancySet`). The effectivity of
`B`, part of the convention that the boundary of a pair is effective, is a separate hypothesis
because `MMP.Fourfold.IsKltPair` does not contain it.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][oai4]
-/

@[expose] public section

section

namespace Proof_lem_oai4_c1_junction_exists

open AlgebraicGeometry MMP.Fourfold MMP.Mori

private theorem solution
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {B : QDivisor X} (hB : 0 ≤ B) (hklt : IsKltPair sX B)
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) ⊆ lowDiscrepancySet sX B) :
    Nonempty (FourfoldCrepantJunction sX B I) :=
  (exists_fourfoldCrepantJunction_of_isKltPair hX hdim hB hklt hI).nonempty

end Proof_lem_oai4_c1_junction_exists

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Crepant junctions exist.** Let `(X, B)` be a klt pair, with `B` effective, on a normal
projective complex fourfold, and `I` a finite set of normalized divisorial valuations of `k(X)`
exceptional over `X` with `a(s; X, B) ≤ 1`. Then there is a crepant junction
`MMP.Fourfold.FourfoldCrepantJunction` of `(X, B)` extracting `I`. -/
@[mmp "lem_oai4_c1_junction_exists"]
public theorem nonempty_fourfoldCrepantJunction
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) {B : QDivisor X} (hB : 0 ≤ B) (hklt : IsKltPair sX B)
    {I : Finset (Valuation X.functionField (WithZero (Multiplicative ℤ)))}
    (hI : (I : Set _) ⊆ lowDiscrepancySet sX B) :
    Nonempty (FourfoldCrepantJunction sX B I) :=
      by revert X sX hX hdim B hB hklt I hI; first | exact Proof_lem_oai4_c1_junction_exists.solution | exact Proof_lem_oai4_c1_junction_exists.solution _ | exact Proof_lem_oai4_c1_junction_exists.solution _ _ | exact Proof_lem_oai4_c1_junction_exists.solution _ _ _ | exact Proof_lem_oai4_c1_junction_exists.solution _ _ _ _

end MMP.Fourfold

