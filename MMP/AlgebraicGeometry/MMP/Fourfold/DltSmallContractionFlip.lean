module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.DltFlip
public import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
public import MMP.AlgebraicGeometry.Modules.CurveFibreLineBundle
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation

/-!
# Flips of small elementary contractions of projective dlt fourfolds

Let `(U, Δ)` be a projective `ℚ`-factorial dlt complex fourfold with rational boundary `Δ` and
canonical divisor `K`, let `R` be a `(K + Δ)`-negative extremal ray of `NE̅(U)` and let
`f : U ⟶ V` be the contraction of `R` onto a normal projective variety, with `f` small,
`ρ(U/V) = 1` and `-(K + Δ)` `f`-ample. Then `f` has a `(K + Δ)`-flip `f⁺ : U⁺ ⟶ V`: a small
projective birational morphism from a normal variety on which the strict transform
`K⁺ + Δ⁺ = (f⁺)⁻¹_* f_* (K + Δ)` is `ℚ`-Cartier and `f⁺`-ample. Moreover `(U⁺, Δ⁺)` is again a
projective `ℚ`-factorial dlt pair, with canonical divisor `K⁺ = (f⁺)⁻¹_* f_* K`.

## Main results

* `MMP.Fourfold.IsProjectiveQFactorialDltPair.exists_isFlipOf_of_isSmallMorphism`: the
  statement above.

## Implementation notes

* The flip is `MMP.Fourfold.IsFlipOf` for the divisor `K + Δ`; its strict transform is
  `MMP.Mori.flipTransform f f⁺ (K + Δ)`, and `Δ⁺` is `MMP.Mori.flipTransform f f⁺ Δ`.
* The contraction is `MMP.Fourfold.IsContractionOfRay`, which includes normality of `V`;
  projectivity of `V` is `MMP.Mori.IsProjectiveVariety`, the relative Picard number is
  `MMP.Fourfold.relativePicardNumberN1`.
* The canonical divisor of `U⁺` is pinned to `MMP.Mori.flipTransform f f⁺ K`, the convention of
  `MMP.Fourfold.IsFourfoldStepDiagram`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace Proof_lem_fourfold_dlt_elementary_step_fourfold

section

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- A proper morphism with an relatively ample `ℚ`-divisor, to a scheme carrying an ample
invertible module, is projective. -/
private theorem isProjectiveMorphism_of_hasRelativelyAmpleMultiple {X Y : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {g : X ⟶ Y} [IsProper g]
    {D : QDivisor X} (hD : D.HasRelativelyAmpleMultiple g) (M : Y.Modules)
    [Stacks.Ample.IsInvertibleModule Y M] (hM : Stacks.Ample.IsAmple Y M) :
    IsProjectiveMorphism g := by
  obtain ⟨m, -, L, hL, -, hamp⟩ := hD
  haveI := hL.isInvertibleModule_divisorialSheaf
  exact isProjectiveMorphism_of_isQuasiProjective g M hM
    ⟨⟨inferInstance, inferInstance⟩, L.divisorialSheaf, inferInstance,
      Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple g _
        inferInstance hamp⟩

/-- Pushing prime divisors forward commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem mapPrimeDivisors_toQDivisor {X Y : Scheme.{0}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toQDivisor D) =
      Divisor.toQDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E n =>
    cases h : φ E <;>
      simp [Divisor.toQDivisor, DivisorWithCoeffs.mapCoeffs,
        DivisorWithCoeffs.mapPrimeDivisors_single, h]

/-- The birational transform commutes with regarding a divisor as a `ℚ`-divisor. -/
private theorem flipTransform_toQDivisor {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Z ⟶ Y)
    (K : Divisor X) :
    flipTransform f g (Divisor.toQDivisor K) = Divisor.toQDivisor (flipTransform f g K) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_toQDivisor]

private theorem solution :
    ∀ {U V : Scheme.{0}} [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sU : U ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} {K : Divisor U} {Δ : QDivisor U}
    (hU : IsProjectiveQFactorialDltPair sU K Δ) (hdim : topologicalKrullDim U = 4)
    {R : Set (NumericalCurveClasses sU)}
    (hR : IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R) {f : U ⟶ V}
    (hf : IsContractionOfRay sU sV R f) (hsmall : IsSmallMorphism sU sV f)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hρ : relativePicardNumberN1 sU f = 1)
    (hamp : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f),
    ∃ (U' : Scheme.{0}) (_ : IsIntegral U') (_ : CompactSpace U') (_ : IsLocallyNoetherian U')
      (_ : IsNormal U') (sU' : U' ⟶ Spec (.of ℂ)) (fp : U' ⟶ V),
      fp ≫ sV = sU' ∧ IsFlipOf sU sV sU' (Divisor.toQDivisor K + Δ) f fp ∧
        IsProjectiveQFactorialDltPair sU' (flipTransform f fp K) (flipTransform f fp Δ) := by
  intro U V _ _ _ _ sU sV K Δ hU hdim R hR f hf hsmall hV hρ hamp
  obtain ⟨m, hK⟩ := hU.isCanonicalDivisor
  obtain ⟨U', _, _, _, sU', fp, hflip⟩ := exists_isFlip_of_isDltPair_of_isContractionOfRay sU
    hU.isProjectiveVariety hU.isQFactorial hdim hU.isDltPair hK hR sV hf hsmall
  haveI : IsIntegral U' := hflip.isNormalVariety.1.toIsIntegral
  haveI : IsProper fp := hflip.isProper
  have hVproj : IsProjectiveMorphism sV := hV.isProjective
  obtain ⟨M₀, hM₀, hM₀a⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of ℂ))
  obtain ⟨M, hM, hMa⟩ := exists_isAmple_of_isProjectiveMorphism sV M₀ hM₀a hVproj
  have hfp : IsProjectiveMorphism fp :=
    isProjectiveMorphism_of_hasRelativelyAmpleMultiple hflip.hasRelativelyAmpleMultiple M hMa
  have hD : flipTransform f fp (Divisor.toQDivisor K + Δ) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp Δ := by
    rw [map_add, flipTransform_toQDivisor]
  have hflipOf : IsFlipOf sU sV sU' (Divisor.toQDivisor K + Δ) f fp :=
    { isQCartier := hflip.isFlippingContraction.isQCartier
      isContraction := hf.toIsContraction
      isSmallMorphism := hsmall
      hasRelativelyAmpleMultiple := hamp
      isSmallMorphism_flip := ⟨hflip.isNormalVariety, hsmall.isNormalVariety_target,
        hflip.comp_eq, hflip.isProper, hflip.isBirationalMorphism, hflip.two_le_codimension⟩
      isProjectiveMorphism_flip := hfp
      isQCartier_flip := hD ▸ hflip.isQCartier
      hasRelativelyAmpleMultiple_flip := hD ▸ hflip.hasRelativelyAmpleMultiple }
  have hstep : IsProjectiveElementaryDltStep sU sV sU' K Δ R f fp (flipTransform f fp Δ) :=
    ⟨hU, hR, hf, hsmall.isBirationalMorphism, hflip.comp_eq, rfl, Or.inl ⟨hsmall, hflipOf⟩⟩
  obtain ⟨hQ, hdlt⟩ := hstep.isQFactorial_and_isDltPair
  refine ⟨U', inferInstance, inferInstance, inferInstance, inferInstance, sU', fp, hflip.comp_eq,
    hflipOf, ⟨?_, hQ, ⟨m, hflip.isCanonicalDivisor_flipTransform hK⟩, hdlt⟩⟩
  refine (AlgebraicGeometry.isProjectiveVariety_iff ℂ sU').2 ⟨hflip.isNormalVariety.1, ?_⟩
  rw [← hflip.comp_eq]
  exact hfp.comp hVproj

end

end Proof_lem_fourfold_dlt_elementary_step_fourfold

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

namespace MMP.Fourfold

/-- **Flips of small elementary contractions of projective dlt fourfolds.** Let `(U, Δ)` be a
projective `ℚ`-factorial dlt complex fourfold with rational boundary and canonical divisor `K`,
`R` a `(K + Δ)`-negative extremal ray of `NE̅(U)`, and `f : U ⟶ V` a small contraction of `R`
onto a normal projective variety with `ρ(U/V) = 1` and `-(K + Δ)` `f`-ample. Then there is a
`(K + Δ)`-flip `f⁺ : U⁺ ⟶ V` of `f` over `ℂ`, and `(U⁺, (f⁺)⁻¹_* f_* Δ)` is a projective
`ℚ`-factorial dlt pair with canonical divisor `(f⁺)⁻¹_* f_* K`. -/
@[mmp "lem_fourfold_dlt_elementary_step_fourfold"]
public theorem IsProjectiveQFactorialDltPair.exists_isFlipOf_of_isSmallMorphism
    {U V : Scheme.{0}} [IsIntegral U] [CompactSpace U] [IsLocallyNoetherian U] [IsNormal U]
    {sU : U ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} {K : Divisor U} {Δ : QDivisor U}
    (hU : IsProjectiveQFactorialDltPair sU K Δ) (hdim : topologicalKrullDim U = 4)
    {R : Set (NumericalCurveClasses sU)}
    (hR : IsNegativeExtremalRayOf sU (Divisor.toQDivisor K + Δ) R) {f : U ⟶ V}
    (hf : IsContractionOfRay sU sV R f) (hsmall : IsSmallMorphism sU sV f)
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (hρ : relativePicardNumberN1 sU f = 1)
    (hamp : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f) :
    ∃ (U' : Scheme.{0}) (_ : IsIntegral U') (_ : CompactSpace U') (_ : IsLocallyNoetherian U')
      (_ : IsNormal U') (sU' : U' ⟶ Spec (.of ℂ)) (fp : U' ⟶ V),
      fp ≫ sV = sU' ∧ IsFlipOf sU sV sU' (Divisor.toQDivisor K + Δ) f fp ∧
        IsProjectiveQFactorialDltPair sU' (flipTransform f fp K) (flipTransform f fp Δ) :=
          by revert U V sU sV K Δ hU hdim R hR f hf hsmall hV hρ hamp; first | exact Proof_lem_fourfold_dlt_elementary_step_fourfold.solution | exact Proof_lem_fourfold_dlt_elementary_step_fourfold.solution _ | exact Proof_lem_fourfold_dlt_elementary_step_fourfold.solution _ _ | exact Proof_lem_fourfold_dlt_elementary_step_fourfold.solution _ _ _ | exact Proof_lem_fourfold_dlt_elementary_step_fourfold.solution _ _ _ _

end MMP.Fourfold

