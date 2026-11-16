module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.FloorFlipFromPlFlip
public import MMP.AlgebraicGeometry.MMP.Threefold.BirationalFiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.SpecialTermination
public import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.KltRayLength
public import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.Analysis.Complex.CauchyOsgoodLaurent
public import MMP.AlgebraicGeometry.MMP.Contraction.SemiampleSupportingDivisor
public import MMP.AlgebraicGeometry.MMP.Contraction.SmallContractionBasics
public import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
public import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
public import MMP.AlgebraicGeometry.Chow.FieldSituation

/-!
# The projective floor-program inputs in dimension four

Existence of flips of floor contractions of rational `ℚ`-factorial projective dlt fourfolds
follows from the birational finite-generation property `F(3)`, by lowering the other reduced
components to obtain a pl-flip. Termination follows from special termination for dlt fourfolds:
a sequence of floor flips is a sequence of flips in the sense of
`MMP.Flips.SequenceOfFlips` (each model stays a projective `ℚ`-factorial dlt pair, so each ray
is spanned by a curve and its contraction has relative Picard number one), and after finitely
many steps its flipping loci `Ex(f_i)` are disjoint from `⌊B_i⌋`. On the other hand a curve
spanning the ray, on which a component `S ⊆ ⌊B_i⌋` is negative, lies both in `S` and in
`Ex(f_i)`.
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold Filter

namespace Proof_thm_fourfold_projective_floor_program_inputs_4

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {X Y : Scheme.{0}} {R S : Type*}
    [AddCommGroup R] [AddCommGroup S]
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (g : R →+ S)
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E r =>
    simp only [DivisorWithCoeffs.mapCoeffsAddMonoidHom, Finsupp.mapRange.addMonoidHom_apply,
      Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [Finsupp.mapRange_single]

/-- The strict transform `(f⁺)⁻¹_* f_*` commutes with changing coefficients. -/
private theorem flipTransform_mapCoeffsAddMonoidHom {X Y X' : Scheme.{0}} {R S : Type*}
    [AddCommGroup R] [AddCommGroup S] (f : X ⟶ Y) (fp : X' ⟶ Y) (g : R →+ S)
    (D : DivisorWithCoeffs R X) :
    flipTransform f fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- The `ℝ`-divisor of the adjoint divisor `K + B`. -/
private theorem logCanonicalDivisor_eq {X : Scheme.{0}} (K : Divisor X) (B : QDivisor X) :
    MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + B) := by
  rw [MMP.Flips.logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

/-- A `ℚ`-Cartier `ℚ`-divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_toRDivisor {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {D : QDivisor X} (h : D.IsQCartier) :
    MMP.Flips.IsCartierCombination (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLc⟩ := h
  exact ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, fun _ => hLc, by
    rw [Fin.sum_univ_one]; exact QDivisor.toRDivisor_eq_inv_smul hm hL⟩

/-- The first clause of `P(4)`: floor contractions of fourfold floor pairs have flips. -/
private theorem exists_flip {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} (hX : IsFloorPair sX 4 K B) {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hf : IsFloorFlippingContraction sX sZ K B R f) :
    ∃ (X' : Scheme.{0}) (_ : CompactSpace X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (sX' : X' ⟶ Spec (.of ℂ)) (fp : X' ⟶ Z),
      MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsFlip sX sZ sX' K B f fp := by
  obtain ⟨Xp, _, h1, h2, h3, sXp, fp, hp, hfl, -, -⟩ :=
    exists_isFlip_of_birationalFiniteGenerationProperty_of_isFloorFlippingContraction
      (n := 4) (by norm_num) birationalFiniteGenerationProperty_three hX hf
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
    rw [map_add, flipTransform_toQDivisor]
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

/-- The source of a flip has the dimension of its flipped model. -/
private theorem topologicalKrullDim_eq_of_isFlip {X Z X' : Scheme.{0}} [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} {f : X ⟶ Z} {fp : X' ⟶ Z} (hfl : IsFlip sX sZ sX' K B f fp) :
    topologicalKrullDim X' = topologicalKrullDim X := by
  have hc := hfl.isFlippingContraction
  haveI := hc.isNormalVariety_source.1
  haveI := hc.isNormalVariety_target.1
  haveI := hfl.isNormalVariety.1
  rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX
    hc.isBirationalMorphism,
    MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX' hfl.isBirationalMorphism]

/-- The ray of a floor contraction of a projective `ℚ`-factorial dlt complex pair is spanned by
a curve: lowering `⌊B⌋` slightly gives a klt pair on which the ray is still negative, and
negative extremal rays of klt pairs are spanned by (rational) curves. -/
private theorem exists_ray_eq {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X}
    {B : QDivisor X} (hX : IsProjectiveQFactorialDltPair sX K B)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R) :
    ∃ C : ProperCurve sX,
      R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u} := by
  obtain ⟨ε, -, hklt, hRε⟩ := hX.exists_isKltPair_sub_smul_roundDown hR
  obtain ⟨m, hm⟩ := hX.isCanonicalDivisor
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX.isProjectiveVariety
  have hkm := (isKltPair_iff_mori_isKltPair sX hm hklt.1).mp hklt
  obtain ⟨T, -, hT, -⟩ := exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf sX hkm
    (fun P => hklt.1.nonneg P) hRε
  exact ⟨T, hT⟩

/-- The class of a curve spanning a nonzero ray is nonzero. -/
private theorem numericalClass_ne_zero_of_ray_eq {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {D : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} (hR : IsNegativeExtremalRayOf sX D R) (C : ProperCurve sX)
    (hCR : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u}) :
    OneCycle.numericalClass _ (C.cycle ℝ) ≠ 0 := by
  intro h0
  obtain ⟨-, ⟨-, v, hv, hRv⟩, -⟩ := hR
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  rw [hCR] at hvR
  obtain ⟨c, -, hc⟩ := hvR
  rw [h0, smul_zero] at hc
  exact hv hc.symm

/-- A proper curve contracted by `f` has its generic point in the exceptional set
`MMP.Flips.exceptionalSet f`: on an open set where `f` is an open immersion, `f` is injective, so
it would meet the curve only in its generic point, which is then locally closed, hence closed
since `X` is Jacobson; but a curve is not a point. -/
private theorem point_mem_exceptionalSet {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX] (C : ProperCurve sX) {f : X ⟶ Y}
    (hC : C.IsContractedBy f) :
    C.point ∈ MMP.Flips.exceptionalSet f := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  by_contra hx
  obtain ⟨V, hxV, hV⟩ := MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet hx
  have hinj : Function.Injective (V.ι ≫ f).base := (V.ι ≫ f).isOpenEmbedding.injective
  have hloc : IsLocallyClosed ({C.point} : Set X) := by
    refine ⟨V, closure {C.point}, V.isOpen, isClosed_closure, ?_⟩
    ext x
    constructor
    · rintro rfl
      exact ⟨hxV, subset_closure rfl⟩
    · rintro ⟨hxV', hxc⟩
      have h := hinj (a₁ := ⟨x, hxV'⟩) (a₂ := ⟨C.point, hxV⟩) (by
        simp only [Scheme.Hom.comp_base, TopCat.comp_app]
        exact hC x hxc)
      exact congrArg Subtype.val h
  have hcl := isClosed_singleton_of_isLocallyClosed_singleton hloc
  haveI : Subsingleton (closure ({C.point} : Set X)) := by
    rw [hcl.closure_eq]
    infer_instance
  have h1 := C.dim_eq
  rw [MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq] at h1
  have h0 := topologicalKrullDim_zero_of_discreteTopology (closure ({C.point} : Set X))
  rw [h1] at h0
  exact absurd h0 (by decide)

/-- A proper curve on which an effective prime divisor `S` has negative degree lies in `S`:
off `S`, the degree of a Cartier multiple of `S` on the curve is that of an effective
divisor. -/
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
a projective `ℚ`-factorial dlt pair `(X, B)`, the exceptional set of `f` meets `Supp ⌊B⌋`: a
curve `C` spanning the ray is contracted by `f`, so lies in `Ex(f)`, and some component `S` of
`⌊B⌋` is negative on it, so it lies in `S`. -/
private theorem not_disjoint_exceptionalSet_supp_roundDown {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z} (hX : IsProjectiveQFactorialDltPair sX K B)
    (hf : IsFloorFlippingContraction sX sZ K B R f) :
    ¬ Disjoint (MMP.Flips.exceptionalSet f)
      ((DivisorWithCoeffs.roundDown B).supp : Set X) := by
  obtain ⟨S, hS1, hSc, hneg⟩ := hf.isComponentNegative
  obtain ⟨C, hCR⟩ := exists_ray_eq hX hf.isNegativeExtremalRayOf
  have hCmem : OneCycle.numericalClass _ (C.cycle ℝ) ∈ R :=
    hCR ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hCne := numericalClass_ne_zero_of_ray_eq hf.isNegativeExtremalRayOf C hCR
  haveI := hX.isProjectiveVariety
  refine Set.not_disjoint_iff.mpr ⟨C.point,
    point_mem_exceptionalSet C ((hf.isContractionOfRay.isContractedBy_iff C).mpr hCmem), ?_⟩
  refine DivisorWithCoeffs.support_subset_supp (E := S) ?_
    (point_mem_support_of_curveForm_neg S hSc C (hneg _ hCmem hCne))
  rw [DivisorWithCoeffs.coeff_roundDown, hS1]
  simp

/-- Along a sequence of floor flips of a floor pair, every model is a projective `ℚ`-factorial
dlt pair of dimension four. -/
private theorem isProjectiveQFactorialDltPair_model {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X} (hX : IsFloorPair sX 4 K B)
    {Y : ℕ → Scheme.{0}} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)} [∀ i, IsIntegral (Y i)]
    [∀ i, CompactSpace (Y i)] [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    {KY : ∀ i, Divisor (Y i)} {BY : ∀ i, QDivisor (Y i)} {Z : ℕ → Scheme.{0}}
    {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)} {R : ∀ i, Set (NumericalCurveClasses (modelStr sX sY i))}
    {f : ∀ i, modelSeq X Y i ⟶ Z i} {fp : ∀ i, Y i ⟶ Z i}
    (h : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sY i) ∧
        IsFloorFlippingContraction (modelStr sX sY i) (sZ i) (divisorSeq K KY i)
          (divisorSeq B BY i) (R i) (f i) ∧
        IsFlip (modelStr sX sY i) (sZ i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
          (f i) (fp i) ∧
        KY i = flipTransform (f i) (fp i) (divisorSeq K KY i) ∧
        BY i = flipTransform (f i) (fp i) (divisorSeq B BY i)) (i : ℕ) :
    IsProjectiveQFactorialDltPair (modelStr sX sY i) (divisorSeq K KY i) (divisorSeq B BY i) ∧
      topologicalKrullDim (modelSeq X Y i) = 4 := by
  induction i with
  | zero => exact ⟨⟨hX.1, hX.2.2.1, hX.2.2.2.1, hX.2.2.2.2⟩, hX.2.1⟩
  | succ i ih =>
    obtain ⟨hpair, hdim⟩ := ih
    obtain ⟨hp, hf, hfl, -, hB⟩ := h i
    have hstep : IsProjectiveElementaryDltStep (modelStr sX sY i) (sZ i) (sY i)
        (divisorSeq K KY i) (divisorSeq B BY i) (R i) (f i) (fp i) (BY i) :=
      { isProjectiveQFactorialDltPair := hpair
        isNegativeExtremalRayOf := hf.isNegativeExtremalRayOf
        isContractionOfRay := hf.isContractionOfRay
        isBirationalMorphism := hf.isSmallMorphism.isBirationalMorphism
        comp_eq := hfl.comp_eq
        eq_flipTransform := hB
        flip_or_divisorial := Or.inl ⟨hf.isSmallMorphism, isFlipOf_of_isFlip hf hfl hp⟩ }
    obtain ⟨hQ, hdlt⟩ := hstep.isQFactorial_and_isDltPair
    exact ⟨⟨hp, hQ, (h (i + 1)).2.2.1.isFlippingContraction.isCanonicalDivisor, hdlt⟩,
      (topologicalKrullDim_eq_of_isFlip hfl).trans hdim⟩

/-- The contraction of a floor flipping contraction whose ray is spanned by a curve is a
`(K + B)`-negative extremal contraction in the sense of `MMP.Flips`. -/
private theorem isNegativeExtremalContraction_of_isFloorFlippingContraction {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z}
    (hf : IsFloorFlippingContraction sX sZ K B R f)
    (hspan : ∃ C : ProperCurve sX,
      R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u}) :
    MMP.Flips.IsNegativeExtremalContraction ℂ sX sZ
      (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) f := by
  have hc := hf.isContractionOfRay.toIsContraction
  have := isProper_of_isProjectiveMorphism f hc.isProjectiveMorphism
  rw [logCanonicalDivisor_eq]
  exact
    { isNormalVariety_source := hc.isNormalVariety_source
      isNormalVariety_target := hc.isNormalVariety_target
      isCartierCombination := isCartierCombination_toRDivisor hf.isNegativeExtremalRayOf.1
      isContraction :=
        { isVariety_target := hc.isNormalVariety_target.1
          isVariety_source := hc.isNormalVariety_source.1
          comp_eq := hc.comp_eq
          isProper := inferInstance
          isIso_app := hc.isIso_app }
      isRelativelyAntiAmple := by
        rw [MMP.Flips.IsRelativelyAntiAmple, ← map_neg]
        exact hf.hasRelativelyAmpleMultiple.isRelativelyAmple_toRDivisor
      relativePicardNumber_eq_one :=
        relativePicardNumber_eq_one_of_isContractionOfRay hf.isNegativeExtremalRayOf hspan
          hf.isContractionOfRay }

/-- A flip `f⁺` of a floor flipping contraction `f` whose ray is spanned by a curve, with
projective flipped model, is a flip in the sense of `MMP.Flips.IsFlip`, for the birational map
`(f⁺)⁻¹ ∘ f`, which carries `B` to its strict transform. -/
private theorem exists_isFlip_of_isFlip {X Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sX' : X' ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X}
    {R : Set (NumericalCurveClasses sX)} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hf : IsFloorFlippingContraction sX sZ K B R f) (hfl : IsFlip sX sZ sX' K B f fp)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX')
    (hspan : ∃ C : ProperCurve sX,
      R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass _ (C.cycle ℝ) = u}) :
    ∃ φ : X.RationalMap X',
      MMP.Flips.IsFlip ℂ sX sZ sX' (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B))
          f fp φ ∧
        flipTransform f fp B = RationalMap.transformDivisor φ B := by
  have hs := hf.isSmallMorphism
  have : IsSeparated sZ := hf.isProjectiveVariety_target.1.toIsSeparated
  have : IsSeparated sX' := hX'.1.toIsSeparated
  have := hfl.isProper
  have := hs.isProper
  obtain ⟨φ, hmod⟩ := exists_isModificationOf_of_isBirationalMorphism (sZ := sZ)
    hs.isBirationalMorphism hfl.isBirationalMorphism
  have htr : ∀ {S : Type} [AddCommMonoid S] (D : DivisorWithCoeffs S X),
      RationalMap.transformDivisor φ D = flipTransform f fp D := fun D =>
    transformDivisor_eq_flipTransform_of_isModificationOf (sZ := sZ) (sX' := sX')
      hs.two_le_codimension hfl.two_le_codimension hmod D
  have hE := isNegativeExtremalContraction_of_isFloorFlippingContraction hf hspan
  have hsp : IsSmallMorphism sX' sZ fp :=
    { isNormalVariety_source := hfl.isNormalVariety
      isNormalVariety_target := hs.isNormalVariety_target
      comp_eq := hfl.comp_eq
      isProper := hfl.isProper
      isBirationalMorphism := hfl.isBirationalMorphism
      two_le_codimension := hfl.two_le_codimension }
  have hiso : ∀ U : Z.Opens, IsIso (fp.app U) :=
    (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sX' sZ
      hfl.isNormalVariety.1 hs.isNormalVariety_target fp hfl.isBirationalMorphism).1
  have htrE : RationalMap.transformDivisor φ
      (MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B)) =
        QDivisor.toRDivisor
          (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B) := by
    rw [htr, logCanonicalDivisor_eq, ← flipTransform_toQDivisor, ← map_add]
    exact flipTransform_mapCoeffsAddMonoidHom f fp _ _
  refine ⟨φ,
    { isNormalVariety_source := hfl.isFlippingContraction.isNormalVariety_source
      isNormalVariety_target := hs.isNormalVariety_target
      isNormalVariety_flip := hfl.isNormalVariety
      isContraction := hE.isContraction
      isCartierCombination := hE.isCartierCombination
      isRelativelyAntiAmple := hE.isRelativelyAntiAmple
      isProper := inferInstance
      isModificationOf := hmod
      isMorphismInCodimOne := MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver
        hfl.isFlippingContraction.isNormalVariety_source f fp φ hmod.2
      isSmall := hsp.isSmall hiso
      isCartierCombination_transform := by
        rw [htrE]; exact isCartierCombination_toRDivisor hfl.isQCartier
      isRelativelyAmple_transform := by
        rw [htrE]; exact hfl.hasRelativelyAmpleMultiple.isRelativelyAmple_toRDivisor
      isSmall_source := hs.isSmall hf.isContractionOfRay.isIso_app },
    (htr B).symm⟩

/-- **Special termination for floor flips.** A sequence of floor flips of a floor fourfold pair
is an infinite sequence of flips in the sense of `MMP.Flips.SequenceOfFlips`, with the same
models, contractions and flips, so eventually its flipping loci are disjoint from the reduced
boundaries. -/
private theorem eventually_disjoint {X : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {B : QDivisor X} (hX : IsFloorPair sX 4 K B)
    {Y : ℕ → Scheme.{0}} {sY : ∀ i, Y i ⟶ Spec (.of ℂ)} [∀ i, IsIntegral (Y i)]
    [∀ i, CompactSpace (Y i)] [∀ i, IsLocallyNoetherian (Y i)] [∀ i, IsNormal (Y i)]
    {KY : ∀ i, Divisor (Y i)} {BY : ∀ i, QDivisor (Y i)} {Z : ℕ → Scheme.{0}}
    {sZ : ∀ i, Z i ⟶ Spec (.of ℂ)} {R : ∀ i, Set (NumericalCurveClasses (modelStr sX sY i))}
    {f : ∀ i, modelSeq X Y i ⟶ Z i} {fp : ∀ i, Y i ⟶ Z i}
    (h : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sY i) ∧
        IsFloorFlippingContraction (modelStr sX sY i) (sZ i) (divisorSeq K KY i)
          (divisorSeq B BY i) (R i) (f i) ∧
        IsFlip (modelStr sX sY i) (sZ i) (sY i) (divisorSeq K KY i) (divisorSeq B BY i)
          (f i) (fp i) ∧
        KY i = flipTransform (f i) (fp i) (divisorSeq K KY i) ∧
        BY i = flipTransform (f i) (fp i) (divisorSeq B BY i)) :
    ∀ᶠ i in atTop, Disjoint (MMP.Flips.exceptionalSet (f i))
      ((DivisorWithCoeffs.roundDown (divisorSeq B BY i)).supp : Set (modelSeq X Y i)) := by
  have hpair := isProjectiveQFactorialDltPair_model hX h
  have hK : ∀ i, Divisor.IsCanonicalDivisor (modelStr sX sY i) 4 (divisorSeq K KY i) :=
      fun i => by
    obtain ⟨m, hm⟩ := (h i).2.2.1.isFlippingContraction.isCanonicalDivisor
    obtain rfl : m = 4 := by exact_mod_cast hm.1.symm.trans (hpair i).2
    exact hm
  have hstep : ∀ i, ∃ φ : (modelSeq X Y i).RationalMap (modelSeq X Y (i + 1)),
      MMP.Flips.IsFlip ℂ (modelStr sX sY i) (sZ i) (sY i)
          (MMP.Flips.logCanonicalDivisor (divisorSeq K KY i)
            (QDivisor.toRDivisor (divisorSeq B BY i))) (f i) (fp i) φ ∧
        flipTransform (f i) (fp i) (divisorSeq B BY i) =
          RationalMap.transformDivisor φ (divisorSeq B BY i) := fun i =>
    exists_isFlip_of_isFlip (h i).2.1 (h i).2.2.1 (h i).1
      (exists_ray_eq (hpair i).1 (h i).2.1.isNegativeExtremalRayOf)
  choose φ hφ using hstep
  haveI : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  let S : MMP.Flips.SequenceOfFlips sX 4 K B :=
    { isNormalVariety := (h 0).2.2.1.isFlippingContraction.isNormalVariety_source
      isCanonicalDivisor := ⟨inferInstance, inferInstance, hK 0⟩
      isQCartier := ⟨inferInstance, inferInstance, (h 0).2.2.1.isFlippingContraction.isQCartier⟩
      length := ⊤
      one_le_length := le_top
      model := fun i => ⟨modelSeq X Y i, modelStr sX sY i, divisorSeq K KY i, divisorSeq B BY i⟩
      model_zero := rfl
      isNormalVariety_model := fun i _ =>
        (h i).2.2.1.isFlippingContraction.isNormalVariety_source
      isLocallyNoetherian_model := fun i => inferInstanceAs (IsLocallyNoetherian (modelSeq X Y i))
      isNormal_model := fun i => inferInstanceAs (IsNormal (modelSeq X Y i))
      compactSpace_model := fun i => inferInstanceAs (CompactSpace (modelSeq X Y i))
      isCanonicalDivisor_model := fun i _ => hK i
      base := Z
      baseStr := sZ
      contraction := f
      flip := fp
      flipMap := φ
      isNegativeExtremalContraction := fun i _ =>
        isNegativeExtremalContraction_of_isFloorFlippingContraction (h i).2.1
          (exists_ray_eq (hpair i).1 (h i).2.1.isNegativeExtremalRayOf)
      isSmall := fun i _ => (h i).2.1.isSmallMorphism.isSmall (h i).2.1.isContractionOfRay.isIso_app
      isFlip := fun i _ => (hφ i).1
      transform_eq := fun i _ => ((h i).2.2.2.2).trans (hφ i).2 }
  have hT := MMP.Fourfold.SequenceOfFlips.eventually_disjoint_exceptionalSet_supp_roundDown
    hX.1 hX.2.1 hX.2.2.1 hX.2.2.2.2 S rfl (fun i => (h i).2.1.isProjectiveVariety_target)
  exact hT.mono fun i hi => hi.1

/-- **The projective floor-program inputs hold in dimension four.** -/
private theorem solution : ProjectiveFloorProgramInputs 4 := by
  refine ⟨by norm_num, fun X _ _ _ _ sX K B hX Z sZ R f hf => exists_flip hX hf, ?_⟩
  intro X _ _ _ _ sX K B hX
  rintro ⟨Y, sY, _, _, _, _, KY, BY, Z, sZ, R, f, fp, h⟩
  obtain ⟨N, hN⟩ := (eventually_disjoint hX h).exists
  exact not_disjoint_exceptionalSet_supp_roundDown
    (isProjectiveQFactorialDltPair_model hX h N).1 (h N).2.1 hN

end Proof_thm_fourfold_projective_floor_program_inputs_4

end

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Fourfold Filter

namespace MMP.Fourfold

/-- **The property `P(4)`**: the projective floor-program inputs
`ProjectiveFloorProgramInputs` hold in dimension four. -/
@[mmp "thm_fourfold_projective_floor_program_inputs_4"]
public theorem projectiveFloorProgramInputs_four :
    ProjectiveFloorProgramInputs 4 :=
      by first | exact Proof_thm_fourfold_projective_floor_program_inputs_4.solution | exact Proof_thm_fourfold_projective_floor_program_inputs_4.solution _ | exact Proof_thm_fourfold_projective_floor_program_inputs_4.solution _ _ | exact Proof_thm_fourfold_projective_floor_program_inputs_4.solution _ _ _ | exact Proof_thm_fourfold_projective_floor_program_inputs_4.solution _ _ _ _

end MMP.Fourfold
