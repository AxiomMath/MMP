module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.FloorProgramInputs
public import MMP.AlgebraicGeometry.MMP.Flip.KltFlipFromFloorProgram

/-!
# Flips of projective klt complex fourfolds

Let `(X, B)` be a klt pair, with `B` an effective `ℚ`-divisor, on a `ℚ`-factorial projective
complex variety `X` of dimension four, and let `K` be a canonical divisor of `X`. If
`f : X ⟶ Z` is the contraction of a `(K + B)`-negative extremal ray `R` of `NE̅(X)` and `f` is
small, then the `(K + B)`-flip `f⁺ : X⁺ ⟶ Z` of `f` exists.

The proof reduces the flip, by two programs run globally over the projective base `Z`, to the
minimal model program for threefolds; the inputs of that reduction are known in dimension four.

## Main results

* `MMP.Fourfold.exists_isFlip_of_isKltPair_of_isContractionOfRay`: the statement above.

## Implementation notes

* The klt condition is `MMP.Fourfold.IsKltPair`, whose underlying pair `MMP.Fourfold.IsPair`
  records that `B` is effective. "Rational" means that `B` is a `ℚ`-divisor.
* The contraction is `MMP.Fourfold.IsContractionOfRay` and smallness is
  `MMP.Fourfold.IsSmallMorphism`. The flip is `MMP.Mori.IsFlip`. Its first field,
  `MMP.Mori.IsFlippingContraction`, records that `f` is a `(K + B)`-flipping contraction.
  The boundary and the canonical divisor on `X⁺` are the strict transforms
  `(f⁺)⁻¹_* f_* B` and `(f⁺)⁻¹_* f_* K`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace Proof_thm_fourfold_projective_klt_flip_4

private theorem solution :
    ∀ {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = 4) {B : QDivisor X} (hklt : IsKltPair sX B)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hsmall : IsSmallMorphism sX sZ f),
    ∃ (Xp : Scheme.{0}) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp) (_ : IsNormal Xp)
      (sXp : Xp ⟶ Spec (.of ℂ)) (fp : Xp ⟶ Z), IsFlip sX sZ sXp K B f fp := by
  intro X _ _ _ _ sX hX hQ hdim B hklt n K hK R hR Z sZ f hf hsmall
  exact exists_isFlip_of_projectiveFloorProgramInputs_of_isContractionOfRay
    projectiveFloorProgramInputs_four sX hX hQ (by exact_mod_cast hdim) hklt hK hR sZ hf hsmall

end Proof_thm_fourfold_projective_klt_flip_4

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.Fourfold

/-- **Klt flips in dimension four.** Let `(X, B)` be a klt pair on a `ℚ`-factorial projective
complex fourfold, with `B ≥ 0` a `ℚ`-divisor and `K` a canonical divisor. Let `f : X ⟶ Z` be
the contraction of a `(K + B)`-negative extremal ray `R` of `NE̅(X)`, and suppose `f` is small.
Then the `(K + B)`-flip of `f` exists: there is a normal variety `X⁺` with a proper birational
morphism `f⁺ : X⁺ ⟶ Z` such that `MMP.Mori.IsFlip` holds for `K`, `B`, `f` and `f⁺`. -/
@[mmp "thm_fourfold_projective_klt_flip_4"]
public theorem exists_isFlip_of_isKltPair_of_isContractionOfRay
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = 4) {B : QDivisor X} (hklt : IsKltPair sX B)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hsmall : IsSmallMorphism sX sZ f) :
    ∃ (Xp : Scheme.{0}) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp) (_ : IsNormal Xp)
      (sXp : Xp ⟶ Spec (.of ℂ)) (fp : Xp ⟶ Z), IsFlip sX sZ sXp K B f fp :=
        by revert X sX hX hQ hdim B hklt n K hK R hR Z sZ f hf hsmall; first | exact Proof_thm_fourfold_projective_klt_flip_4.solution | exact Proof_thm_fourfold_projective_klt_flip_4.solution _ | exact Proof_thm_fourfold_projective_klt_flip_4.solution _ _ | exact Proof_thm_fourfold_projective_klt_flip_4.solution _ _ _ | exact Proof_thm_fourfold_projective_klt_flip_4.solution _ _ _ _

end MMP.Fourfold

