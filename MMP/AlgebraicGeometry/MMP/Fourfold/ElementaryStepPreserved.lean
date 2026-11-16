module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.KltStepQFactorial
public import MMP.AlgebraicGeometry.MMP.Contraction.NumericallyTrivialDescent
public import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryDlt
public import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Morphisms.HProjective

section

/-!
# Elementary dlt steps preserve projective `ℚ`-factorial dlt pairs

The output `(U⁺, Δ⁺)` of the elementary step of a `(K + Δ)`-negative extremal ray of a projective
`ℚ`-factorial dlt pair `(U, Δ)` is again a projective `ℚ`-factorial dlt pair, with canonical
divisor `(f⁺)⁻¹_* f_* K`. The morphism `f⁺ : U⁺ ⟶ V` is projective (a flip, or an isomorphism),
so `U⁺` is projective over `k` because `V` is. `ℚ`-factoriality and the dlt property are the
preservation theorem `MMP.Fourfold.IsProjectiveElementaryDltStep.isQFactorial_and_isDltPair`.
In the small case `f⁺` is a `(K + Δ)`-flip and the strict transform of `K` is canonical; in the
divisorial case `f⁺` is an isomorphism and `(f⁺)⁻¹_* f_* K` is the push-forward of `K` along the
proper birational morphism `(f⁺)⁻¹ ∘ f`, again canonical.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

namespace MMP.FourfoldProofs.Oai4DltElementaryCProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Under an isomorphism `e : X' ⟶ V`, the inverse transform `e⁻¹_* D` is the push-forward of `D`
along `e⁻¹`. -/
private theorem inverseTransformDivisor_eq_transformDivisor_inv {R : Type*} [AddCommMonoid R]
    {V X' : Scheme.{0}} [IsReduced V] [IsSeparated (X' ↘ ⊤_ Scheme)] (e : X' ⟶ V) [IsIso e]
    (D : DivisorWithCoeffs R V) :
    inverseTransformDivisor e D = RationalMap.transformDivisor (inv e).toRationalMap D := by
  have key : (inverseTransformDivisor e : DivisorWithCoeffs R V →+ DivisorWithCoeffs R X') =
      RationalMap.transformDivisor (inv e).toRationalMap := by
    refine Finsupp.addHom_ext fun Q r => ?_
    have hco : Order.coheight (inv e Q.genericPoint) = 1 := by
      rw [coheight_eq_of_isOpenImmersion (inv e)]
      exact AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Q
    have hP := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    have heP : e (AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco).genericPoint =
        Q.genericPoint := by
      rw [hP, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
      rfl
    have hbir : biregularLocus e = ⊤ :=
      top_le_iff.mp (le_biregularLocus ((isBiregular_top_iff e).mpr inferInstance))
    rw [inverseTransformDivisor_single_of_eq_some
      (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint heP
        (by rw [hbir]; trivial)),
      RationalMap.transformDivisor_single_of_eq_some
        ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff _ _ _).2 hP.symm)]
  exact DFunLike.congr_fun key D

/-- In the small case, the `(K + Δ)`-flip `f⁺` of the elementary step is a flip of the flipping
contraction `f` in the sense of `MMP.Mori.IsFlip`. -/
private theorem isFlip_of_isFlipOf {k : Type} [Field k] {X V X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {K : Divisor X} {Δ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V} {fp : X' ⟶ V} {Δ' : QDivisor X'}
    (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ')
    (hflip : IsFlipOf sX sV sX' (Divisor.toQDivisor K + Δ) f fp) :
    IsFlip sX sV sX' K Δ f fp := by
  have hD : flipTransform f fp (Divisor.toQDivisor K + Δ) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp Δ := by
    rw [map_add, flipTransform_toQDivisor]
  have hsm := hflip.isSmallMorphism_flip
  exact
    { isFlippingContraction :=
        { isNormalVariety_source := h.isContractionOfRay.isNormalVariety_source
          isNormalVariety_target := h.isContractionOfRay.isNormalVariety_target
          comp_eq := h.isContractionOfRay.comp_eq
          isCanonicalDivisor := h.isProjectiveQFactorialDltPair.isCanonicalDivisor
          isQCartier := hflip.isQCartier
          isProper := hflip.isSmallMorphism.isProper
          isBirationalMorphism := h.isBirationalMorphism
          two_le_codimension := hflip.isSmallMorphism.two_le_codimension
          hasRelativelyAmpleMultiple := hflip.hasRelativelyAmpleMultiple }
      isNormalVariety := hsm.isNormalVariety_source
      comp_eq := h.comp_eq
      isProper := hsm.isProper
      isBirationalMorphism := hsm.isBirationalMorphism
      isQCartier := hD ▸ hflip.isQCartier_flip
      hasRelativelyAmpleMultiple := hD ▸ hflip.hasRelativelyAmpleMultiple_flip
      two_le_codimension := hsm.two_le_codimension }

/-- A normal scheme isomorphic over `k` to a normal variety is a normal variety. -/
private theorem isNormalVariety_of_isIso {k : Type} [Field k] {V X' : Scheme.{0}}
    [IsIntegral X'] [IsNormal X'] {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (fp : X' ⟶ V) [IsIso fp]
    (hVn : IsNormalVariety k sV) (hcomp : fp ≫ sV = sX') : IsNormalVariety k sX' := by
  subst hcomp
  haveI := hVn.1
  exact ⟨(MMP.Mori.isVariety_iff k _).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩

/-- **The canonical divisor in the divisorial case.** When `f : X ⟶ V` is a projective
birational morphism of normal varieties and `f⁺ : X' ⟶ V` is an isomorphism over `k`, the
transform `(f⁺)⁻¹_* f_* K` of a canonical divisor `K` of `X` is a canonical divisor of `X'`:
`f_* K` is canonical on `V`, and so is its push-forward along the isomorphism `(f⁺)⁻¹`. -/
private theorem isCanonicalDivisor_flipTransform_of_isIso {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] {X V X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {K : Divisor X} {Δ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V} {fp : X' ⟶ V} {Δ' : QDivisor X'} {m : ℕ}
    [IsIso fp] (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ')
    (hK : Divisor.IsCanonicalDivisor sX m K) :
    Divisor.IsCanonicalDivisor sX' m (flipTransform f fp K) := by
  have hc := h.isContractionOfRay
  have hXn := hc.isNormalVariety_source
  have hVn := hc.isNormalVariety_target
  have hfcomp : f ≫ sV = sX := hc.comp_eq
  have hX'n := isNormalVariety_of_isIso fp hVn h.comp_eq
  haveI : IsIntegral V := hVn.1.toIsIntegral
  haveI : IsNormal V := hVn.2
  haveI : LocallyOfFiniteType sV := hVn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  haveI : QuasiCompact sV := hVn.1.toQuasiCompact
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  haveI : LocallyOfFiniteType sX' := hX'n.1.toLocallyOfFiniteType
  haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal_of_isNormalVariety hX'n
  haveI : MMP.Mori.IsVariety k sV := hVn.1
  haveI : MMP.Mori.IsVariety k sX := hXn.1
  haveI : MMP.Mori.IsVariety k sX' := hX'n.1
  have hdimV : topologicalKrullDim V = m := by
    rw [MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sX
      h.isBirationalMorphism, hK.topologicalKrullDim_eq]
  have hdimX' : topologicalKrullDim X' = m := by
    rw [← hdimV, MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sV sX'
      (isBirationalMorphism_of_isIso fp)]
  -- the push-forward `f_* K` is a canonical divisor of `V`
  obtain ⟨KV, hKV⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sV hVn hdimV
  haveI : IsProper f := isProper_of_isProjectiveMorphism f hc.isProjectiveMorphism
  haveI : IsDominant f := h.isBirationalMorphism.isDominant
  haveI : LocallyOfFiniteType (f ≫ sV) := hfcomp ▸ hXn.1.toLocallyOfFiniteType
  have hpush := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hVn
    (hfcomp ▸ hXn) h.isBirationalMorphism hKV (hfcomp ▸ hK)
  -- and its push-forward along the isomorphism `(f⁺)⁻¹` is a canonical divisor of `X'`
  obtain ⟨KX', hKX'⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sX' hX'n hdimX'
  have hinv : inv fp ≫ sX' = sV := by rw [← h.comp_eq, IsIso.inv_hom_id_assoc]
  haveI : LocallyOfFiniteType (inv fp ≫ sX') := hinv ▸ inferInstance
  have := MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hX'n
    (hinv ▸ hVn) (isBirationalMorphism_of_isIso (inv fp)) hKX' (hinv ▸ hpush)
  change Divisor.IsCanonicalDivisor sX' m
    (inverseTransformDivisor fp (RationalMap.transformDivisor f.toRationalMap K))
  rwa [inverseTransformDivisor_eq_transformDivisor_inv]

end MMP.FourfoldProofs.Oai4DltElementaryCProof

end

section

/-!
# Elementary dlt steps preserve projective `ℚ`-factorial dlt pairs

Let `(U, Δ)` be a projective `ℚ`-factorial dlt pair over an algebraically closed field `k` of
characteristic zero, with `Δ` a `ℚ`-divisor and `K` a canonical divisor of `U`, let `R` be a
`(K + Δ)`-negative extremal ray of `NE̅(U)` and `f : U ⟶ V` a birational contraction of `R` onto a
normal projective variety with `ρ(U/V) = 1` and `-(K + Δ)` `f`-ample. If `(U⁺, Δ⁺)` is an output
of the elementary step of `R` — the flip of `f` when `f` is small, the divisorial contraction
`(V, f_* Δ)` otherwise — then `(U⁺, Δ⁺)` is again a projective `ℚ`-factorial dlt pair with
rational boundary, with canonical divisor the birational transform `(f⁺)⁻¹_* f_* K` of `K`.

## Main results

* `MMP.Fourfold.IsProjectiveElementaryDltStep.isProjectiveQFactorialDltPair_flipTransform`: the
  statement above.

## Implementation notes

* The elementary step is `MMP.Fourfold.IsProjectiveElementaryDltStep`, which already records
  that `(U, Δ)` is a projective `ℚ`-factorial dlt pair, that `R` is `(K + Δ)`-negative, that `f`
  is a contraction of `R` (`MMP.Fourfold.IsContractionOfRay`, which includes normality of `V`)
  and that `f` is birational. The remaining hypotheses are projectivity of `V`, `ρ(U/V) = 1`
  (`MMP.Fourfold.relativePicardNumberN1`) and relative ampleness of `-(K + Δ)`.
* The canonical divisor of `U⁺` is pinned to `MMP.Mori.flipTransform f f⁺ K`, the convention of
  `MMP.Fourfold.IsFourfoldStepDiagram`; the source leaves it implicit.
* The source works over `ℂ`; the statement is over any algebraically closed field of
  characteristic zero, which contains the complex case.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.FourfoldProofs.Oai4DltElementaryCProof in
/-- **Elementary dlt steps preserve projective `ℚ`-factorial dlt pairs.** Let `(X, Δ)` be a
projective `ℚ`-factorial dlt pair with canonical divisor `K` over an algebraically closed field of
characteristic zero, and let `(X', Δ')` be the output of the elementary step of a
`(K + Δ)`-negative extremal ray `R` whose contraction `f : X ⟶ V` is birational, with `V`
projective, `ρ(X/V) = 1` and `-(K + Δ)` `f`-ample. Then `(X', Δ')` is a projective `ℚ`-factorial
dlt pair, with canonical divisor `(f⁺)⁻¹_* f_* K`. -/
@[mmp "lem_oai4_dlt_elementary_c"]
theorem IsProjectiveElementaryDltStep.isProjectiveQFactorialDltPair_flipTransform
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X V X' : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sV : V ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {K : Divisor X} {Δ : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ V} {fp : X' ⟶ V} {Δ' : QDivisor X'}
    (h : IsProjectiveElementaryDltStep sX sV sX' K Δ R f fp Δ')
    (hV : MMP.Mori.IsProjectiveVariety k sV) (hρ : relativePicardNumberN1 sX f = 1)
    (hamp : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f) :
    IsProjectiveQFactorialDltPair sX' (flipTransform f fp K) Δ' := by
  obtain ⟨m, hK⟩ := h.isProjectiveQFactorialDltPair.isCanonicalDivisor
  obtain ⟨hQ, hdlt⟩ := h.isQFactorial_and_isDltPair
  obtain ⟨hfpP, hX'v, hK'⟩ : IsProjectiveMorphism fp ∧ MMP.Mori.IsVariety k sX' ∧
      Divisor.IsCanonicalDivisor sX' m (flipTransform f fp K) := by
    rcases h.flip_or_divisorial with ⟨-, hflip⟩ | ⟨-, hiso⟩
    · exact ⟨hflip.isProjectiveMorphism_flip, hflip.isSmallMorphism_flip.isNormalVariety_source.1,
        (isFlip_of_isFlipOf h hflip).isCanonicalDivisor_flipTransform hK⟩
    · haveI := hiso
      exact ⟨MMP.isProjectiveMorphism_of_isClosedImmersion fp,
        (isNormalVariety_of_isIso fp h.isContractionOfRay.isNormalVariety_target h.comp_eq).1,
        isCanonicalDivisor_flipTransform_of_isIso h hK⟩
  refine ⟨(AlgebraicGeometry.isProjectiveVariety_iff k sX').2 ⟨hX'v, ?_⟩, hQ, ⟨m, hK'⟩, hdlt⟩
  rw [← h.comp_eq]
  exact hfpP.comp hV.isProjective

end MMP.Fourfold

end
