module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.MMP.Fourfold.Singularities
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.MMP.Flip.NegativeAdjointTransfer
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.KltFlip
public import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContraction
public import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary
public import MMP.AlgebraicGeometry.MMP.Contraction.VerticalFactorization
public import MMP.AlgebraicGeometry.Resolution.SncPairStratumBlowup
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback

/-!
# Flips of projective dlt complex fourfolds

Let `(X, B)` be a dlt pair, with `B` a `ℚ`-divisor, on a `ℚ`-factorial projective complex
variety `X` of dimension four, and let `K` be a canonical divisor of `X`. If `f : X ⟶ Z` is the
contraction of a `(K + B)`-negative extremal ray `R` of `NE̅(X)` and `f` is small, then the
`(K + B)`-flip `f⁺ : X⁺ ⟶ Z` of `f` exists.

The proof lowers the coefficients of the reduced part `⌊B⌋` by a small rational amount, which
gives a klt boundary still negative on `R`; the klt flip of
`MMP.Fourfold.exists_isFlip_of_isKltPair_of_isContractionOfRay` for that boundary is then the
`(K + B)`-flip, since both adjoint divisors are negative on the same ray.

## Main results

* `MMP.Fourfold.exists_isFlip_of_isDltPair_of_isContractionOfRay`: the statement above.

## Implementation notes

* The dlt condition is `MMP.Intersection.IsDltPair`: it contains log canonicity
  (`MMP.Intersection.IsLogCanonicalPair`), so `B` is effective and `K + B` is `ℚ`-Cartier.
  "Rational" means that `B` is a `ℚ`-divisor.
* The contraction is `MMP.Fourfold.IsContractionOfRay` and smallness is
  `MMP.Fourfold.IsSmallMorphism`. The flip is `MMP.Mori.IsFlip`, whose boundary and canonical
  divisor on `X⁺` are the strict transforms `(f⁺)⁻¹_* f_* B` and `(f⁺)⁻¹_* f_* K`.

## References

* [OpenAI, *Termination for projective log canonical fourfolds with rational boundary*][OAI4]
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace Proof_thm_fourfold_projective_dlt_flip_4

/-- The flip transform commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem flipTransform_toQDivisor {X Y X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    flipTransform f fp (Divisor.toQDivisor D) = Divisor.toQDivisor (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Flips.transformDivisor_toQDivisor,
    MMP.Threefold.Resolution.inverseTransformDivisor_toQDivisor]

/-- The target of the contraction of a negative extremal ray of a projective klt pair is
projective: the contraction theorem gives one contraction of the ray onto a projective variety,
and two contractions of the same ray are isomorphic over the base field. -/
private theorem isProjectiveVariety_of_isContractionOfRay {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {B : QDivisor X} (hklt : IsKltPair sX B)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f) :
    MMP.Mori.IsProjectiveVariety ℂ sZ := by
  obtain ⟨-, Z', sZ', f', hf', hZ', -, -⟩ := exists_isContractionOfRay_of_isKltPair sX hX hklt hK hR
  have hray := hR.2.1
  have hfac {W V : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} {g : X ⟶ W}
      (hg : IsContractionOfRay sX sW R g) {g' : X ⟶ V} (hg' : IsContractionOfRay sX sV R g') :
      ∃! h : V ⟶ W, g' ≫ h = g :=
    existsUnique_comp_eq_of_isContractionOfRay hX hg.isProjectiveMorphism hg.comp_eq hray
      (fun C hC => (hg.isContractedBy_iff C).mpr hC) hg'
  obtain ⟨a, ha, -⟩ := hfac hf' hf
  obtain ⟨b, hb, -⟩ := hfac hf hf'
  have hab : a ≫ b = 𝟙 Z :=
    (hfac hf hf).unique (by rw [← Category.assoc, ha, hb]) (Category.comp_id f)
  have hba : b ≫ a = 𝟙 Z' :=
    (hfac hf' hf').unique (by rw [← Category.assoc, hb, ha]) (Category.comp_id f')
  have hsZ : a ≫ sZ' = sZ :=
    (existsUnique_comp_eq_of_isContractionOfRay hX hX.isProjective (Category.comp_id sX) hray
      (fun C _ x _ => Subsingleton.elim _ _) hf).unique
      (by rw [← Category.assoc, ha, hf'.comp_eq]) hf.comp_eq
  haveI : IsIso a := ⟨b, hab, hba⟩
  refine (AlgebraicGeometry.isProjectiveVariety_iff ℂ sZ).mpr ⟨hf.isNormalVariety_target.1, ?_⟩
  obtain ⟨N, i, hi, hic⟩ := hZ'.isProjective
  haveI := hi
  exact ⟨N, a ≫ i, inferInstance, by rw [Category.assoc, hic, hsZ]⟩

/-- A flip `f⁺ : X⁺ ⟶ Z` onto a projective variety is a projective morphism: it is proper and
carries a relatively ample Cartier divisor. -/
private theorem isProjectiveMorphism_of_isFlip {X Z Xp : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {K : Divisor X} {B : QDivisor X} {f : X ⟶ Z}
    {fp : Xp ⟶ Z} (hfl : IsFlip sX sZ sXp K B f fp) : IsProjectiveMorphism fp := by
  haveI : AlgebraicGeometry.IsVariety ℂ sXp := hfl.isNormalVariety.1
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.toIsVariety
  haveI : IsProper fp := hfl.isProper
  obtain ⟨m, -, L, hL, -, hamp⟩ := hfl.hasRelativelyAmpleMultiple
  have hproj : IsProjective fp :=
    MMP.isProjective_of_isProper_of_divisor_isRelativelyAmple ℂ sXp sZ fp hfl.comp_eq L hL hamp
  obtain ⟨M, hM, hMa⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of ℂ))
  obtain ⟨H, hH, hHa⟩ := exists_isAmple_of_isProjectiveMorphism sZ M hMa hZ.isProjective
  exact ((isProjective_tfae_seven_of_exists_isAmple fp ⟨H, hH, hHa⟩).out 1 2).mp hproj

private theorem solution :
    ∀ {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = 4) {B : QDivisor X}
    (hdlt : MMP.Intersection.IsDltPair sX B)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hsmall : IsSmallMorphism sX sZ f),
    ∃ (Xp : Scheme.{0}) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp) (_ : IsNormal Xp)
      (sXp : Xp ⟶ Spec (.of ℂ)) (fp : Xp ⟶ Z), IsFlip sX sZ sXp K B f fp := by
  intro X _ _ _ _ sX hX hQ hdim B hdlt n K hK R hR Z sZ f hf hsmall
  obtain ⟨ε, -, hklt, hR'⟩ :=
    IsProjectiveQFactorialDltPair.exists_isKltPair_sub_smul_roundDown ⟨hX, hQ, ⟨n, hK⟩, hdlt⟩ hR
  set B' := B - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown B)
  obtain ⟨Xp, _, _, _, sXp, fp, hfl⟩ :=
    exists_isFlip_of_isKltPair_of_isContractionOfRay sX hX hQ hdim hklt hK hR' sZ hf hsmall
  have hfp : IsProjectiveMorphism fp :=
    isProjectiveMorphism_of_isFlip (isProjectiveVariety_of_isContractionOfRay hX hklt hK hR' hf) hfl
  have hflip' : IsFlipOf sX sZ sXp (Divisor.toQDivisor K + B') f fp :=
    { isQCartier := hR'.1
      isContraction := hf.toIsContraction
      isSmallMorphism := hsmall
      hasRelativelyAmpleMultiple := hfl.isFlippingContraction.hasRelativelyAmpleMultiple
      isSmallMorphism_flip := ⟨hfl.isNormalVariety, hsmall.isNormalVariety_target, hfl.comp_eq,
        hfl.isProper, hfl.isBirationalMorphism, hfl.two_le_codimension⟩
      isProjectiveMorphism_flip := hfp
      isQCartier_flip := by rw [map_add, flipTransform_toQDivisor]; exact hfl.isQCartier
      hasRelativelyAmpleMultiple_flip := by
        rw [map_add, flipTransform_toQDivisor]; exact hfl.hasRelativelyAmpleMultiple }
  have hflip := IsFlipOf.of_isNegativeExtremalRayOf hX hQ hklt ⟨n, hK⟩ hR' hf hR hR' hflip'
  have hq := hflip.isQCartier_flip
  have ha := hflip.hasRelativelyAmpleMultiple_flip
  rw [map_add, flipTransform_toQDivisor] at hq ha
  exact ⟨Xp, inferInstance, inferInstance, inferInstance, sXp, fp,
    { isFlippingContraction :=
        ⟨hsmall.isNormalVariety_source, hsmall.isNormalVariety_target, hsmall.comp_eq, ⟨n, hK⟩,
          hR.1, hsmall.isProper, hsmall.isBirationalMorphism, hsmall.two_le_codimension,
          hflip.hasRelativelyAmpleMultiple⟩
      isNormalVariety := hfl.isNormalVariety
      comp_eq := hfl.comp_eq
      isProper := hfl.isProper
      isBirationalMorphism := hfl.isBirationalMorphism
      isQCartier := hq
      hasRelativelyAmpleMultiple := ha
      two_le_codimension := hfl.two_le_codimension }⟩

end Proof_thm_fourfold_projective_dlt_flip_4

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.Fourfold

/-- **Dlt flips in dimension four.** Let `(X, B)` be a dlt pair on a `ℚ`-factorial projective
complex fourfold, with `B` a `ℚ`-divisor and `K` a canonical divisor. Let `f : X ⟶ Z` be the
contraction of a `(K + B)`-negative extremal ray `R` of `NE̅(X)`, and suppose `f` is small. Then
the `(K + B)`-flip of `f` exists: there is a normal variety `X⁺` with a proper birational
morphism `f⁺ : X⁺ ⟶ Z` such that `MMP.Mori.IsFlip` holds for `K`, `B`, `f` and `f⁺`. -/
@[mmp "thm_fourfold_projective_dlt_flip_4"]
public theorem exists_isFlip_of_isDltPair_of_isContractionOfRay
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = 4) {B : QDivisor X}
    (hdlt : MMP.Intersection.IsDltPair sX B)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    {Z : Scheme.{0}} (sZ : Z ⟶ Spec (.of ℂ)) {f : X ⟶ Z} (hf : IsContractionOfRay sX sZ R f)
    (hsmall : IsSmallMorphism sX sZ f) :
    ∃ (Xp : Scheme.{0}) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp) (_ : IsNormal Xp)
      (sXp : Xp ⟶ Spec (.of ℂ)) (fp : Xp ⟶ Z), IsFlip sX sZ sXp K B f fp :=
        by revert X sX hX hQ hdim B hdlt n K hK R hR Z sZ f hf hsmall; first | exact Proof_thm_fourfold_projective_dlt_flip_4.solution | exact Proof_thm_fourfold_projective_dlt_flip_4.solution _ | exact Proof_thm_fourfold_projective_dlt_flip_4.solution _ _ | exact Proof_thm_fourfold_projective_dlt_flip_4.solution _ _ _ | exact Proof_thm_fourfold_projective_dlt_flip_4.solution _ _ _ _

end MMP.Fourfold

