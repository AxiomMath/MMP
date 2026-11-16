module
public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.FloorProgramInputs
import MMP.AlgebraicGeometry.MMP.Flip.KltFlipFromFloorProgram

/-!
# thm fourfold projective klt flip 3

Chain fold of: `thm_fourfold_projective_klt_flip_3`.
-/

/-! ### `thm_fourfold_projective_klt_flip_3` -/

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

namespace MMP.Fold06.ThmFourfoldProjectiveKltFlip3

private theorem solution : ∀ {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (K : Divisor X)
    (B : QDivisor X) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 3) (hQ : IsQFactorial sX)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hB : IsKltPair sX B)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (R : Set (NumericalCurveClasses sX))
    (f : X ⟶ Z) (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hfR : IsContractionOfRay sX sZ R f) (hf : IsFlippingContraction sX sZ K B f),
    ∃ (X' : Scheme.{0}) (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z), IsFlip sX sZ sX' K B f fp := by
  intro X _ _ _ _ sX K B hX hdim hQ hK hB Z sZ R f hR hfR hf
  obtain ⟨m, hm⟩ := hK
  exact exists_isFlip_of_projectiveFloorProgramInputs_of_isContractionOfRay
    (n := 3) projectiveFloorProgramInputs_three sX hX hQ (by exact_mod_cast hdim) hB hm hR sZ hfR
    ⟨hf.isNormalVariety_source, hf.isNormalVariety_target, hf.comp_eq, hf.isProper,
      hf.isBirationalMorphism, hf.two_le_codimension⟩

end MMP.Fold06.ThmFourfoldProjectiveKltFlip3

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- **Klt flips exist for projective threefolds.** Let `X` be a `ℚ`-factorial projective
complex threefold with canonical divisor `K` and a klt boundary `B` with rational
coefficients, and let `f : X ⟶ Z` be the contraction of a `(K + B)`-negative extremal ray `R`
which is a `(K + B)`-flipping contraction. Then `f` has a `(K + B)`-flip `f⁺ : X⁺ ⟶ Z`. -/
@[mmp "thm_fourfold_projective_klt_flip_3"]
public theorem exists_isFlip_of_isKltPair {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (K : Divisor X)
    (B : QDivisor X) (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 3) (hQ : IsQFactorial sX)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hB : IsKltPair sX B)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) (R : Set (NumericalCurveClasses sX))
    (f : X ⟶ Z) (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hfR : IsContractionOfRay sX sZ R f) (hf : IsFlippingContraction sX sZ K B f) :
    ∃ (X' : Scheme.{0}) (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z), IsFlip sX sZ sX' K B f fp :=
  MMP.Fold06.ThmFourfoldProjectiveKltFlip3.solution sX K B hX hdim hQ hK hB sZ R f hR hfR hf

end MMP.Fourfold
