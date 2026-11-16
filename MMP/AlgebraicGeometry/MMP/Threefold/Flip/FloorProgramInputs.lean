module
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.SpecialTermination
import MMP.AlgebraicGeometry.MMP.Surface.BirationalFiniteGeneration
import MMP.AlgebraicGeometry.MMP.Flip.FloorFlipFromPlFlip
import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContraction

/-!
# Projective floor-program inputs in dimension three

This file proves `MMP.Fourfold.ProjectiveFloorProgramInputs 3`: floor flipping contractions of
projective `ℚ`-factorial dlt complex threefold pairs have projective flips, and every sequence of
such flips terminates.
-/

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fold06.ThmFourfoldProjectiveFloorProgramInputs3

/-- A floor flipping contraction of a threefold floor pair has a flip with projective flipped
model. -/
private theorem exists_flip {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} (hX : IsFloorPair sX 3 K B) {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hf : IsFloorFlippingContraction sX sZ K B R f) :
    ∃ (X' : Scheme.{0}) (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z),
      MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsFlip sX sZ sX' K B f fp := by
  obtain ⟨Xp, _, h1, h2, h3, sXp, fp, hp, hfl, -, -⟩ :=
    exists_isFlip_of_birationalFiniteGenerationProperty_of_isFloorFlippingContraction
      (n := 3) le_rfl birationalFiniteGenerationProperty_two hX hf
  exact ⟨Xp, h1, h2, h3, sXp, fp, hp, hfl⟩

/-- A floor contraction together with a flip of it, with projective flipped model, is a flip in
the sense of `MMP.Fourfold.IsFlipOf`. -/
private theorem isFlipOf_of_isFlip {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hf : IsFloorFlippingContraction sX sZ K B R f) (hfl : IsFlip sX sZ sX' K B f fp)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') :
    IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp := by
  have htr : flipTransform f fp (Divisor.toQDivisor K + B) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B := by
    rw [map_add, MMP.Mori.flipTransform_toQDivisor]
  haveI := hf.isProjectiveVariety_target
  exact
    { isQCartier := hfl.isFlippingContraction.isQCartier
      isContraction := hf.isContractionOfRay.toIsContraction
      isSmallMorphism := hf.isSmallMorphism
      hasRelativelyAmpleMultiple := hf.hasRelativelyAmpleMultiple
      isSmallMorphism_flip :=
        { isNormalVariety_source := hfl.isNormalVariety
          isNormalVariety_target := hf.isSmallMorphism.isNormalVariety_target
          comp_eq := hfl.comp_eq
          isProper := hfl.isProper
          isBirationalMorphism := hfl.isBirationalMorphism
          two_le_codimension := hfl.two_le_codimension }
      isProjectiveMorphism_flip :=
        IsProjectiveMorphism.of_comp fp sZ (by rw [hfl.comp_eq]; exact hX'.isProjective)
      isQCartier_flip := htr ▸ hfl.isQCartier
      hasRelativelyAmpleMultiple_flip := htr ▸ hfl.hasRelativelyAmpleMultiple }

/-- The flipped model `X'` of a flip has the same dimension as `X`. -/
private theorem topologicalKrullDim_eq_of_isFlip {X Z X' : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z} (hfl : IsFlip sX sZ sX' K B f fp) :
    topologicalKrullDim X' = topologicalKrullDim X := by
  have hc := hfl.isFlippingContraction
  haveI := hc.isNormalVariety_source.1
  haveI := hc.isNormalVariety_target.1
  haveI := hfl.isNormalVariety.1
  rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism
      sZ sX hc.isBirationalMorphism,
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX'
      hfl.isBirationalMorphism]

/-- The generic point of a proper curve contracted by `f` lies in the exceptional set of `f`. -/
private theorem point_mem_exceptionalSet {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} (C : ProperCurve sX) {f : X ⟶ Y} (hC : C.IsContractedBy f) :
    C.point ∈ (exceptionalSet f : Set X) := by
  by_contra hx
  have hηV : C.point ∈ f ⁻¹ᵁ biregularLocus f := not_not.mp hx
  haveI : IsIso (f ∣_ biregularLocus f) := isBiregular_biregularLocus f
  have hb : Function.Injective (f ∣_ biregularLocus f).base :=
    (f ∣_ biregularLocus f).isOpenEmbedding.injective
  have hinj : ∀ x ∈ closure ({C.point} : Set X), x = C.point := by
    intro x hxc
    have hfx := hC x hxc
    have hxV : x ∈ f ⁻¹ᵁ biregularLocus f := by
      change f x ∈ biregularLocus f
      rw [hfx]
      exact hηV
    exact congrArg Subtype.val (hb (a₁ := ⟨x, hxV⟩) (a₂ := ⟨C.point, hηV⟩)
      (Subtype.ext ((morphismRestrict_base_coe f _ ⟨x, hxV⟩).trans
        (hfx.trans (morphismRestrict_base_coe f _ ⟨C.point, hηV⟩).symm))))
  haveI : Subsingleton (closure ({C.point} : Set X)) :=
    ⟨fun a b => Subtype.ext ((hinj a a.2).trans (hinj b b.2).symm)⟩
  have h1 := C.dim_eq
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq] at h1
  have h0 := topologicalKrullDim_zero_of_discreteTopology (closure ({C.point} : Set X))
  rw [h1] at h0
  exact absurd h0 (by decide)

/-- If the prime divisor `S` has negative degree on a proper curve `C`, then the generic point
of `C` lies in `S`. -/
private theorem point_mem_support_of_curveForm_neg {k : Type} [Field k] {X : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] (S : MMP.Mori.PrimeDivisor X)
    (hS : (Divisor.toQDivisor (Finsupp.single S 1)).IsQCartier) (C : ProperCurve sX)
    (hneg : QDivisor.curveForm sX (Divisor.toQDivisor (Finsupp.single S 1)) hS
      (OneCycle.numericalClass sX (C.cycle ℝ)) < 0) :
    C.point ∈ S.support := by
  have hD := MMP.Threefold.Resolution.toQDivisor_single S 1
  rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at hneg
  by_contra hC
  have h0 : 0 ≤ Divisor.toQDivisor (Finsupp.single S 1) :=
    hD ▸ Finsupp.single_nonneg.mpr (by norm_num)
  have hnn := (intersectionNumber_nonneg_and_eq_zero_iff sX _ hS h0 C
    (fun h => hC (DivisorWithCoeffs.supp_single_le S (1 : ℚ) (hD ▸ h)))).1
  exact hneg.not_ge (by exact_mod_cast hnn)

/-- **A floor contraction meets the reduced boundary.** For a floor flipping contraction `f` of
`(X, B)`, some component `S` of `⌊B⌋` meets the exceptional set of `f`. -/
private theorem exists_coeff_eq_one_not_disjoint_exceptionalSet {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z} (hP : IsProjectiveQFactorialDltPair sX K B)
    (hf : IsFloorFlippingContraction sX sZ K B R f) :
    ∃ S : MMP.Mori.PrimeDivisor X, B.coeff S = 1 ∧
      ¬ Disjoint (S.support : Set X) (exceptionalSet f : Set X) := by
  obtain ⟨S, hS1, hSc, hneg⟩ := hf.isComponentNegative
  obtain ⟨ε, -, hklt, hRε⟩ := hP.exists_isKltPair_sub_smul_roundDown hf.isNegativeExtremalRayOf
  obtain ⟨m, hm⟩ := hP.isCanonicalDivisor
  obtain ⟨⟨C, -, hCR⟩, -⟩ :=
    exists_isContractionOfRay_of_isKltPair sX hP.isProjectiveVariety hklt hm hRε
  have hCmem : OneCycle.numericalClass _ (C.cycle ℝ) ∈ R :=
    hCR ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hCne : OneCycle.numericalClass _ (C.cycle ℝ) ≠ 0 := by
    intro h0
    obtain ⟨-, ⟨-, v, hv, hRv⟩, -⟩ := hf.isNegativeExtremalRayOf
    have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
    rw [hCR] at hvR
    obtain ⟨c, -, hc⟩ := hvR
    rw [h0, smul_zero] at hc
    exact hv hc.symm
  haveI := hP.isProjectiveVariety
  exact ⟨S, hS1, Set.not_disjoint_iff.mpr ⟨C.point,
    point_mem_support_of_curveForm_neg S hSc C (hneg _ hCmem hCne),
    point_mem_exceptionalSet C ((hf.isContractionOfRay.isContractedBy_iff C).mpr hCmem)⟩⟩

end MMP.Fold06.ThmFourfoldProjectiveFloorProgramInputs3

namespace MMP.Fourfold

open MMP.Fold06.ThmFourfoldProjectiveFloorProgramInputs3 in
/-- **The projective floor-program inputs hold in dimension three.** Every floor flipping
contraction of a rational `ℚ`-factorial projective dlt complex threefold has a projective flip.
Every sequence of such flips of a fixed pair, with each boundary the strict transform of the
previous one, is finite. See `ProjectiveFloorProgramInputs`. -/
@[mmp "thm_fourfold_projective_floor_program_inputs_3"]
public theorem projectiveFloorProgramInputs_three : ProjectiveFloorProgramInputs 3 := by
  refine ⟨le_rfl, fun X _ _ _ _ sX K B hX Z sZ R f hf => exists_flip hX hf, ?_⟩
  intro X _ _ _ _ sX K B hX
  rintro ⟨Y, sY, _, _, _, _, KY, BY, Z, sZ, R, f, fp, h⟩
  have hdim : ∀ i, topologicalKrullDim (modelSeq X Y i) = 3 := fun i => by
    induction i with
    | zero => exact hX.2.1
    | succ i ih => exact (topologicalKrullDim_eq_of_isFlip (h i).2.2.1).trans ih
  have hK : ∀ i, Divisor.IsCanonicalDivisor (modelStr sX sY i) 3 (divisorSeq K KY i) := fun i => by
    obtain ⟨m, hm⟩ := (h i).2.2.1.isFlippingContraction.isCanonicalDivisor
    obtain rfl : m = 3 := by exact_mod_cast hm.1.symm.trans (hdim i)
    exact hm
  have hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (modelStr sX sY i)
    | 0 => hX.1
    | i + 1 => (h i).1
  obtain ⟨N, hN⟩ := exists_forall_ge_disjoint_exceptionalSet_of_isFlipOf (X := modelSeq X Y)
    (K := divisorSeq K KY) (B := divisorSeq B BY) (R := R) (f := f) (fp := fp) hproj hX.2.2.1
    hX.2.2.2.2 hK (fun i => (h i).2.1.isNegativeExtremalRayOf)
    (fun i => (h i).2.1.isContractionOfRay)
    (fun i => isFlipOf_of_isFlip (h i).2.1 (h i).2.2.1 (h i).1) (fun i => (h i).2.2.2.2)
  have hP : ∀ i, IsProjectiveQFactorialDltPair (modelStr sX sY i) (divisorSeq K KY i)
      (divisorSeq B BY i) := fun i => by
    induction i with
    | zero => exact ⟨hX.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2⟩
    | succ i ih =>
      have hstep : IsProjectiveElementaryDltStep (modelStr sX sY i) (sZ i) (sY i)
          (divisorSeq K KY i) (divisorSeq B BY i) (R i) (f i) (fp i) (divisorSeq B BY (i + 1)) :=
        ⟨ih, (h i).2.1.isNegativeExtremalRayOf, (h i).2.1.isContractionOfRay,
          (h i).2.1.isSmallMorphism.isBirationalMorphism, (h i).2.2.1.comp_eq, (h i).2.2.2.2,
          Or.inl ⟨(h i).2.1.isSmallMorphism, isFlipOf_of_isFlip (h i).2.1 (h i).2.2.1 (h i).1⟩⟩
      obtain ⟨hQ, hdlt⟩ := hstep.isQFactorial_and_isDltPair
      exact ⟨hproj (i + 1), hQ, ⟨3, hK (i + 1)⟩, hdlt⟩
  obtain ⟨S, hS1, hS⟩ := exists_coeff_eq_one_not_disjoint_exceptionalSet (hP N) (h N).2.1
  exact hS ((hN N le_rfl).1 S hS1.ge)

end MMP.Fourfold
