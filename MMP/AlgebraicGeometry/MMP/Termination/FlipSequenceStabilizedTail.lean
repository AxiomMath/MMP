module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.Termination
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Flip.ReducedPartRemoval
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.MMP.Abundance.Curve.AdmissibleSectionsGenerate
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.AlgebraicGeometry.MMP.Fourfold.LowDiscrepancySetNested
import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms

/-!
# An infinite projective flip sequence has a stabilized tail

Let `(X_i, B_i)_{i ≥ 0}` be an infinite sequence of flips of an effective rational klt pair on a
normal projective `ℚ`-factorial complex threefold, as in the termination statements
`MMP.Fourfold.ProjectiveKltTerminationLevel`, with all models `X_i` and all contraction targets
`Z_i` projective. Then some tail `(X_{i₀+i}, B_{i₀+i}, Z_{i₀+i}, f_{i₀+i}, f_{i₀+i}⁺)_{i ≥ 0}` is a
stabilized small klt threefold tail (`MMP.Fourfold.StabilizedTail`).

## Main results

* `MMP.Fourfold.exists_stabilizedTail_of_sequenceOfFlips`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 6.6
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.IndexTailFromSequence

open MMP.Mori MMP.Flips MMP.Fourfold

/-! ### Divisor arithmetic -/

section Divisors

variable {X Y : Scheme.{0}}

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom' {R S : Type*} [AddCommMonoid R]
    [AddCommMonoid S] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    (g : R →+ S) (D : DivisorWithCoeffs R X) :
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
private theorem flipTransform_mapCoeffs {Z X' : Scheme.{0}} {R S : Type*} [AddCommMonoid R]
    [AddCommMonoid S] (f : X ⟶ Z) (fp : X' ⟶ Z) (g : R →+ S) (D : DivisorWithCoeffs R X) :
    flipTransform f fp (DivisorWithCoeffs.mapCoeffsAddMonoidHom g D) =
      DivisorWithCoeffs.mapCoeffsAddMonoidHom g (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapCoeffsAddMonoidHom']

private theorem flipTransform_toQDivisor {Z X' : Scheme.{0}} (f : X ⟶ Z) (fp : X' ⟶ Z)
    (D : Divisor X) :
    flipTransform f fp (Divisor.toQDivisor D) = Divisor.toQDivisor (flipTransform f fp D) :=
  flipTransform_mapCoeffs f fp _ D

private theorem flipTransform_toRDivisor {Z X' : Scheme.{0}} (f : X ⟶ Z) (fp : X' ⟶ Z)
    (D : QDivisor X) :
    flipTransform f fp (QDivisor.toRDivisor D) = QDivisor.toRDivisor (flipTransform f fp D) :=
  flipTransform_mapCoeffs f fp _ D

/-- Pushing prime divisors forward keeps coefficients nonnegative. -/
private theorem mapPrimeDivisors_coeff_nonneg {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y))
    {D : DivisorWithCoeffs R X} (hD : ∀ P, 0 ≤ D P) (Q : MMP.Mori.PrimeDivisor Y) :
    0 ≤ DivisorWithCoeffs.mapPrimeDivisors φ D Q := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P r D hP hr ih =>
    have hDP : D P = 0 := Finsupp.notMem_support_iff.mp hP
    have hr0 : 0 ≤ r := by simpa [hDP] using hD P
    have hD' : ∀ P', 0 ≤ D P' := fun P' => by
      by_cases h : P' = P
      · subst h
        rw [hDP]
      · simpa [Finsupp.single_apply, Ne.symm h] using hD P'
    rw [map_add, Finsupp.add_apply, DivisorWithCoeffs.mapPrimeDivisors_single]
    refine add_nonneg ?_ (ih hD')
    cases φ P with
    | none => simp
    | some P' =>
      by_cases h : P' = Q <;> simp [Finsupp.single_apply, h, hr0]

private theorem flipTransform_coeff_nonneg {Z X' : Scheme.{0}} (f : X ⟶ Z) (fp : X' ⟶ Z)
    {B : QDivisor X} (hB : ∀ P, 0 ≤ B.coeff P) (Q : MMP.Mori.PrimeDivisor X') :
    0 ≤ (flipTransform f fp B).coeff Q :=
  mapPrimeDivisors_coeff_nonneg _ (mapPrimeDivisors_coeff_nonneg _ hB) Q

end Divisors

/-! ### Small contractions and their strict transforms -/

section Small

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- A small birational contraction is small in the sense of exceptional sets: `f` is an
isomorphism over an open `V` over which lie all points of codimension at most one of `X`. -/
private theorem isSmallMorphism_of_isSmall [IsNormal X] (hZ : IsNormalVariety ℂ sZ)
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) : IsSmallMorphism sX sZ f := by
  obtain ⟨V, hV, -, hXV, -⟩ := MMP.Mori.exists_opens_isIso_of_isSmall hf hf
  have hVle : V ≤ biregularLocus f := MMP.Mori.isBiregular_iff_le_biregularLocus.mp hV
  refine
    { isNormalVariety_source := ⟨hf.isVariety_source, inferInstance⟩
      isNormalVariety_target := hZ
      comp_eq := hf.comp_eq
      isProper := hf.isProper
      isBirationalMorphism := hf.isBirationalMorphism
      two_le_codimension := ?_ }
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
  intro x hx
  by_contra h
  have h1 : Order.coheight x ≤ 1 := by
    by_contra h'
    exact h (by simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (not_le.mp h'))
  exact hx (show x ∈ f ⁻¹ᵁ biregularLocus f from hVle (hXV x h1))

private theorem isSeparated_toTerminal_of_isVariety {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
    (h : MMP.Mori.IsVariety ℂ s) : IsSeparated (W ↘ ⊤_ Scheme) := by
  have : IsSeparated s := h.toIsSeparated
  rw [show (W ↘ ⊤_ Scheme) = s ≫ Limits.terminal.from (Spec (.of ℂ)) from Subsingleton.elim _ _]
  infer_instance

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The transform of divisors by a modification of a small `f` into a small `f⁺` is the strict
transform `(f⁺)⁻¹_* f_*`. -/
private theorem transformDivisor_eq_flipTransform (hZ : IsNormalVariety ℂ sZ)
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp)
    {g : X.RationalMap X'} (hg : MMP.Flips.IsModificationOf f fp g) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) :
    MMP.Mori.RationalMap.transformDivisor g D = flipTransform f fp D := by
  obtain ⟨V, hV, hV', hXV, hX'V⟩ := MMP.Mori.exists_opens_isIso_of_isSmall hf hfp
  have := isSeparated_toTerminal_of_isVariety hfp.isVariety_source
  have := hf.isProper
  exact MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZ
    (by rw [hf.comp_eq]; exact ⟨hf.isVariety_source, inferInstance⟩) hf.isBirationalMorphism V
    hXV hX'V hg.2 D

/-- The strict transform of a canonical divisor along two small contractions is canonical. -/
private theorem isCanonicalDivisor_flipTransform [IsIntegral X'] [IsLocallyNoetherian X']
    [IsNormal X'] [CompactSpace X'] (hZ : IsNormalVariety ℂ sZ) (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) :
    MMP.Mori.Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K) := by
  obtain ⟨V, hV, hV', hXV, hX'V⟩ := MMP.Mori.exists_opens_isIso_of_isSmall hf hfp
  have := hf.isProper
  have h := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict hZ
    (by rw [hf.comp_eq]; exact ⟨hf.isVariety_source, inferInstance⟩)
    (by rw [hfp.comp_eq]; exact ⟨hfp.isVariety_source, inferInstance⟩) hf.isBirationalMorphism
    hfp.isBirationalMorphism V hXV hX'V (n := n) (by rw [hf.comp_eq]; exact hK)
  rwa [hfp.comp_eq] at h

end Small

/-! ### Ampleness -/

section Ample

variable {X Y : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sY : Y ⟶ Spec (.of ℂ)}

/-- A `ℚ`-Cartier `ℚ`-divisor which is `f`-ample as an `ℝ`-divisor has an `f`-ample Cartier
multiple. -/
theorem hasRelativelyAmpleMultiple_of_isRelativelyAmple (hX : IsNormalVariety ℂ sX)
    (hY : IsNormalVariety ℂ sY) {f : X ⟶ Y} [IsProper f] (hf : f ≫ sY = sX) {D : QDivisor X}
    (hD : D.IsQCartier) (h : MMP.Flips.IsRelativelyAmple f (QDivisor.toRDivisor D)) :
    D.HasRelativelyAmpleMultiple f := by
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsNormal Y := hY.2
  obtain ⟨m, hm, D', hD', hC⟩ := hD.exists_pos
  obtain ⟨n, r, Ls, hn, hr, hLs, hsum⟩ := h
  have hR : MMP.Flips.IsRelativelyAmple f (Divisor.toRDivisor D') := by
    refine ⟨n, fun j => (m : ℝ) * r j, Ls, hn, fun j => mul_pos (by exact_mod_cast hm) (hr j),
      hLs, ?_⟩
    rw [← QDivisor.toRDivisor_toQDivisor, hD', map_zsmul, hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_natCast]
  obtain ⟨hC', hamp⟩ := (MMP.Flips.relativelyAmple_basics sX sY hX hY f hf).2.2.2.2.1 D' hC hR
  refine ⟨m, hm, D', hC, hD', fun y => ?_⟩
  obtain ⟨V, hV, hyV, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ (⊤ : Y.Opens) from trivial)
  exact ⟨V, hV, hyV, hamp V hV⟩

end Ample

/-! ### A step of the sequence is a threefold step diagram -/

section Step

variable {X X' Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
  {f : X ⟶ Z} {fp : X' ⟶ Z} {g : X.RationalMap X'}

private theorem logCanonicalDivisor_eq' (K : Divisor X) (B : QDivisor X) :
    MMP.Flips.logCanonicalDivisor K (QDivisor.toRDivisor B) =
      QDivisor.toRDivisor (Divisor.toQDivisor K + B) := by
  rw [MMP.Flips.logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor]

omit [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
private theorem isProjectiveMorphism_of_comp_eq (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsVariety ℂ sZ) (h : f ≫ sZ = sX) : IsProjectiveMorphism f := by
  have : IsSeparated sZ := hZ.toIsSeparated
  exact IsProjectiveMorphism.of_comp f sZ (by rw [h]; exact hX.isProjective)

/-- **A flip of the sequence is a threefold step diagram.** If `f : X ⟶ Z` is a small
`(K_S + B)`-negative extremal contraction and `f⁺ : X⁺ ⟶ Z` its flip, for a canonical divisor
`K_S` of `X`, then for every canonical divisor `K` of `X` the datum `(X, B) → Z ← X⁺` is a
threefold step diagram with canonical divisor `K`. -/
private theorem isThreefoldStepDiagram_of_isFlip
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hX' : MMP.Mori.IsProjectiveVariety ℂ sX')
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {KS K : Divisor X} (hKS : KS.IsCanonicalDivisor sX 3) (hK : K.IsCanonicalDivisor sX 3)
    {KS' : Divisor X'} (hKS' : KS'.IsCanonicalDivisor sX' 3)
    {B : QDivisor X} (hB : ∀ P, 0 ≤ B.coeff P)
    (hneg : MMP.Flips.IsNegativeExtremalContraction ℂ sX sZ
      (MMP.Flips.logCanonicalDivisor KS (QDivisor.toRDivisor B)) f)
    (hflip : MMP.Flips.IsFlip ℂ sX sZ sX'
      (MMP.Flips.logCanonicalDivisor KS (QDivisor.toRDivisor B)) f fp g) :
    IsThreefoldStepDiagram sX sZ sX' K B f fp := by
  have hZn := hneg.isNormalVariety_target
  have hXn := hneg.isNormalVariety_source
  have hX'n := hflip.isNormalVariety_flip
  have hf := hflip.isSmall_source
  have hfp := hflip.isSmall
  have := hf.isProper
  have := hfp.isProper
  have hKK : KS.LinearlyEquivalent K :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX hXn hKS hK
  have hK'c := isCanonicalDivisor_flipTransform hZn hf hfp hK
  have hKS'c := isCanonicalDivisor_flipTransform hZn hf hfp hKS
  have hKK' : MMP.Mori.Divisor.LinearlyEquivalent (flipTransform f fp KS) (flipTransform f fp K) :=
    MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'n hKS'c hK'c
  have hEtr : MMP.Mori.RationalMap.transformDivisor g
      (MMP.Flips.logCanonicalDivisor KS (QDivisor.toRDivisor B)) =
      QDivisor.toRDivisor (Divisor.toQDivisor (flipTransform f fp KS) + flipTransform f fp B) := by
    rw [transformDivisor_eq_flipTransform hZn hf hfp hflip.isModificationOf,
      logCanonicalDivisor_eq', flipTransform_toRDivisor, map_add, flipTransform_toQDivisor]
  have hQ : (Divisor.toQDivisor KS + B).IsQCartier :=
    MMP.Flips.QDivisor.isQCartier_of_isCartierCombination
      (logCanonicalDivisor_eq' KS B ▸ hneg.isCartierCombination)
  have hQ' : (Divisor.toQDivisor (flipTransform f fp KS) + flipTransform f fp B).IsQCartier :=
    MMP.Flips.QDivisor.isQCartier_of_isCartierCombination
      (hEtr ▸ hflip.isCartierCombination_transform)
  have hampS : (-(Divisor.toQDivisor KS + B)).HasRelativelyAmpleMultiple f :=
    hasRelativelyAmpleMultiple_of_isRelativelyAmple hXn hZn hf.comp_eq
      (MMP.Fourfold.Oai4C1.isQCartier_neg hQ)
      (by rw [map_neg, ← logCanonicalDivisor_eq']; exact hneg.isRelativelyAntiAmple)
  have hampS' : (Divisor.toQDivisor (flipTransform f fp KS) +
      flipTransform f fp B).HasRelativelyAmpleMultiple fp :=
    hasRelativelyAmpleMultiple_of_isRelativelyAmple hX'n hZn hfp.comp_eq hQ'
      (hEtr ▸ hflip.isRelativelyAmple_transform)
  have hneg_eq : ∀ L : Divisor X, -(Divisor.toQDivisor L + B) = Divisor.toQDivisor (-L) + -B :=
    fun L => by rw [map_neg]; abel
  exact
    { isProjectiveVariety_minus := hX
      isNormalVariety_minus := hXn
      dim_minus := by exact_mod_cast hK.1
      isProjectiveVariety_plus := hX'
      isNormalVariety_plus := hX'n
      dim_plus := by exact_mod_cast hKS'.1
      isProjectiveVariety_target := hZ
      isNormalVariety_target := hZn
      comp_eq_minus := hf.comp_eq
      comp_eq_plus := hfp.comp_eq
      isProjectiveMorphism_minus := isProjectiveMorphism_of_comp_eq hX hZn.1 hf.comp_eq
      isProjectiveMorphism_plus := isProjectiveMorphism_of_comp_eq hX' hZn.1 hfp.comp_eq
      isBirationalMorphism_minus := hf.isBirationalMorphism
      isIso_app_minus := hf.isIso_app
      isIso_app_plus := hfp.isIso_app
      isSmallMorphism_plus := isSmallMorphism_of_isSmall hZn hfp
      isCanonicalDivisor := ⟨3, hK⟩
      isCanonicalDivisor_plus := ⟨3, hK'c⟩
      nonneg := hB
      isQCartier_minus := hQ.add_of_linearlyEquivalent hKK
      isQCartier_plus := hQ'.add_of_linearlyEquivalent hKK'
      hasRelativelyAmpleMultiple_minus := by
        rw [hneg_eq]
        exact MMP.Fourfold.Oai4C1.Main.hasRelativelyAmpleMultiple_add_of_linearlyEquivalent
          (hneg_eq KS ▸ hampS) hKK.neg
      hasRelativelyAmpleMultiple_plus :=
        MMP.Fourfold.Oai4C1.Main.hasRelativelyAmpleMultiple_add_of_linearlyEquivalent hampS' hKK' }

end Step

/-! ### Relative curve classes of an extremal contraction -/

section Ray

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z}

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
/-- The degree of a 1-cycle is an isomorphism invariant of the invertible sheaf. -/
private theorem oneCycle_degree_congr [QuasiCompact sX] {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    OneCycle.degree ℝ sX L = OneCycle.degree ℝ sX L' := by
  rw [OneCycle.degree, OneCycle.degree]
  congr 2
  funext C
  exact congrArg _ (degreeOn_eq_of_iso ℂ sX C.ι C.dim_le e)

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A relative 1-cycle has intersection number zero with every numerically `f`-trivial
divisor. -/
private theorem intersectionNumber_eq_zero_of_mem_relative {T : KCartierDivisor ℝ X}
    (hT : T ∈ MMP.Flips.relativeNumericallyTrivialDivisors sX f) (W : relativeOneCycles sX f) :
    (W : OneCycle ℝ sX).intersectionNumber T = 0 := by
  rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors] at hT
  have hle : relativeOneCycles sX f ≤
      LinearMap.ker (OneCycle.intersectionPairing (sX := sX) T) := by
    rw [relativeOneCycles, Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨C, hC, rfl⟩
    exact LinearMap.mem_ker.mpr (hT C hC)
  exact LinearMap.mem_ker.mp (hle W.2)

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
/-- A morphism with `ρ(X/Z) = 1` contracts some curve. -/
private theorem exists_isContractedBy_of_relativePicardNumber_eq_one
    (h : MMP.Flips.relativePicardNumber sX f = 1) : ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hno
  push Not at hno
  have : Subsingleton (MMP.Flips.RelativeNumericalDivisorClasses sX f) := by
    refine ⟨fun a b => ?_⟩
    induction a using Submodule.Quotient.induction_on
    induction b using Submodule.Quotient.induction_on
    rw [Submodule.Quotient.eq, MMP.Flips.mem_relativeNumericallyTrivialDivisors]
    intro C hC
    exact absurd hC (hno C)
  rw [MMP.Flips.relativePicardNumber, rank_subsingleton'] at h
  simp at h

variable [QuasiCompact sX]

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] in
private theorem intersectionNumber_add (W : OneCycle ℝ sX) (D D' : KCartierDivisor ℝ X) :
    W.intersectionNumber (D + D') = W.intersectionNumber D + W.intersectionNumber D' := by
  simp [OneCycle.intersectionNumber]

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] in
private theorem intersectionNumber_sub (W : OneCycle ℝ sX) (D D' : KCartierDivisor ℝ X) :
    W.intersectionNumber (D - D') = W.intersectionNumber D - W.intersectionNumber D' := by
  simp [OneCycle.intersectionNumber]

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] in
private theorem intersectionNumber_smul (W : OneCycle ℝ sX) (c : ℝ) (D : KCartierDivisor ℝ X) :
    W.intersectionNumber (c • D) = c * W.intersectionNumber D := by
  simp [OneCycle.intersectionNumber]

/-- `(C · E) = deg_C 𝒪_X(E)` for a proper curve `C` and a Cartier divisor `E`. -/
private theorem cycle_intersectionNumber_ofCartier (C : ProperCurve sX) (E : X.CartierDivisor) :
    (C.cycle ℝ).intersectionNumber (KCartierDivisor.ofCartier ℝ E) =
      (C.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ) := by
  rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]

/-- The relative degree of `𝒪_X(L)` on the class of a contracted curve `C` is `(L · C)`. -/
private theorem degree_relativeClass {L : Divisor X} (hL : L.IsCartier)
    [Stacks.Ample.IsInvertibleModule X L.divisorialSheaf] (C : ProperCurve sX)
    (hC : C.IsContractedBy f) :
    RelativeNumericalCurveClasses.degree sX f L.divisorialSheaf (C.relativeClass f hC) =
      (L.degreeOn ℂ sX C.ι C.dim_le hL : ℝ) := by
  change OneCycle.degree ℝ sX L.divisorialSheaf (C.cycle ℝ) = _
  rw [OneCycle.degree_cycle, ProperCurve.degree_divisorialSheaf C L hL]

/-- **`N₁(X/Z)` is a line.** If `ρ(X/Z) = 1` and `L` is a Cartier divisor of positive degree on
every curve contracted by `f`, then every relative class is a multiple of the class of a given
contracted curve `C₀`, the coefficient being read off from the degree of `L`. -/
private theorem eq_smul_relativeClass (h : MMP.Flips.relativePicardNumber sX f = 1) {L : Divisor X}
    (hL : L.IsCartier) [Stacks.Ample.IsInvertibleModule X L.divisorialSheaf]
    (hpos : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 < L.degreeOn ℂ sX C.ι C.dim_le hL)
    {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f) (z : RelativeNumericalCurveClasses sX f) :
    z = (RelativeNumericalCurveClasses.degree sX f L.divisorialSheaf z /
      RelativeNumericalCurveClasses.degree sX f L.divisorialSheaf (C₀.relativeClass f hC₀)) •
        C₀.relativeClass f hC₀ := by
  set φ := RelativeNumericalCurveClasses.degree sX f L.divisorialSheaf
  set v := C₀.relativeClass f hC₀
  have hφv : 0 < φ v := by rw [degree_relativeClass hL]; exact_mod_cast hpos C₀ hC₀
  -- the class of `L` spans `N¹(X/Z)`
  obtain ⟨EL, ⟨eL⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf L.divisorialSheaf
  set D₀ : KCartierDivisor ℝ X := KCartierDivisor.ofCartier ℝ EL
  have hD₀ : ∀ W : OneCycle ℝ sX,
      W.intersectionNumber D₀ = OneCycle.degree ℝ sX L.divisorialSheaf W := by
    intro W
    rw [OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, oneCycle_degree_congr eL]
  have hq₀ :
      Submodule.Quotient.mk (p := MMP.Flips.relativeNumericallyTrivialDivisors sX f) D₀ ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero, MMP.Flips.mem_relativeNumericallyTrivialDivisors]
    intro h0
    have h1 := h0 C₀ hC₀
    rw [hD₀, OneCycle.degree_cycle, ProperCurve.degree_divisorialSheaf C₀ L hL] at h1
    exact (hpos C₀ hC₀).ne' (by exact_mod_cast h1)
  have hfin : Module.finrank ℝ (MMP.Flips.RelativeNumericalDivisorClasses sX f) = 1 := by
    rw [MMP.Flips.relativePicardNumber] at h
    have h1 : Module.rank ℝ (MMP.Flips.RelativeNumericalDivisorClasses sX f) = 1 := by
      exact_mod_cast
        Cardinal.toENat_eq_natCast.mp (h.trans (by norm_num : (1 : ℕ∞) = ((1 : ℕ) : ℕ∞)))
    exact Module.finrank_eq_of_rank_eq (by rw [h1]; norm_num)
  have hspan := (finrank_eq_one_iff_of_nonzero' _ hq₀).mp hfin
  -- `φ` is injective
  have hinj : ∀ w, φ w = 0 → w = 0 := by
    intro w hw
    obtain ⟨W, rfl⟩ := relativeNumericalClass_surjective sX f w
    change Submodule.Quotient.mk W = 0
    rw [Submodule.Quotient.mk_eq_zero, mem_relativeNumericallyTrivial,
      OneCycle.mem_numericallyTrivial]
    intro M _
    obtain ⟨E, ⟨eE⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf M
    obtain ⟨c, hc⟩ := hspan (Submodule.Quotient.mk (KCartierDivisor.ofCartier ℝ E))
    have hT : KCartierDivisor.ofCartier ℝ E - c • D₀ ∈
        MMP.Flips.relativeNumericallyTrivialDivisors sX f := by
      rw [← Submodule.Quotient.eq, ← hc, Submodule.Quotient.mk_smul]
    have h0 := intersectionNumber_eq_zero_of_mem_relative hT W
    rw [intersectionNumber_sub, intersectionNumber_smul, hD₀,
      OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree,
      ← oneCycle_degree_congr eE] at h0
    rwa [show OneCycle.degree ℝ sX L.divisorialSheaf W = 0 from hw, mul_zero, sub_zero] at h0
  exact sub_eq_zero.mp (hinj (z - (φ z / φ v) • v) (by
    rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hφv.ne', sub_self]))

/-- **The negative side of a flip is the contraction of the extremal ray `NE̅(X/Z)`.** Let
`f : X ⟶ Z` be a small birational contraction of normal projective varieties with
`ρ(X/Z) = 1`, and `D` a `ℚ`-Cartier `ℚ`-divisor with `-D` `f`-ample. Then `NE̅(X/Z)` is the ray
spanned by the class of a contracted curve `C₀`; its image `R` in `N₁(X)` is a `D`-negative
extremal ray of `NE̅(X)` and `f` is the contraction of `R`. -/
private theorem exists_isNegativeExtremalRayOf_isContractionOfRay
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hXn : IsNormalVariety ℂ sX) (hZn : IsNormalVariety ℂ sZ)
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {D : QDivisor X} (hD : D.IsQCartier) (hamp : (-D).HasRelativelyAmpleMultiple f) :
    ∃ (R : Set (NumericalCurveClasses sX)) (C₀ : ProperCurve sX), C₀.IsContractedBy f ∧
      R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) = u} ∧
      IsNegativeExtremalRayOf sX D R ∧ IsContractionOfRay sX sZ R f := by
  obtain ⟨C₀, hC₀⟩ := exists_isContractedBy_of_relativePicardNumber_eq_one hρ
  obtain ⟨m, hm, L, hL, hLD, hLamp⟩ := id hamp
  haveI := hL.isInvertibleModule_divisorialSheaf
  have hpos : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 < L.degreeOn ℂ sX C.ι C.dim_le hL := fun C hC =>
    MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hLamp C hC
  set φ := RelativeNumericalCurveClasses.degree sX f L.divisorialSheaf
  set v := C₀.relativeClass f hC₀
  have hφv : 0 < φ v := by rw [degree_relativeClass hL]; exact_mod_cast hpos C₀ hC₀
  have hz := eq_smul_relativeClass hρ hL hpos hC₀
  -- `NE̅(X/Z)` is the ray spanned by `[C₀]`
  have hRrel : {w : RelativeNumericalCurveClasses sX f | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} =
      {w | 0 ≤ φ w} := by
    ext w
    refine ⟨?_, fun hw => ⟨φ w / φ v, div_nonneg hw hφv.le, (hz w).symm⟩⟩
    rintro ⟨c, hc, rfl⟩
    rw [Set.mem_setOf_eq, map_smul, smul_eq_mul]
    exact mul_nonneg hc hφv.le
  have hcone : (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) =
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w} := by
    apply le_antisymm
    · rw [coe_relativeClosedConeOfCurves, hRrel]
      refine closure_minimal ?_ (isClosed_le continuous_const
        (RelativeNumericalCurveClasses.continuous_degree sX f L.divisorialSheaf))
      intro w hw
      change w ∈ Submodule.span _ _ at hw
      refine Submodule.span_induction (p := fun w _ => 0 ≤ φ w) ?_ ?_ ?_ ?_ hw
      · rintro _ ⟨⟨C, hC⟩, rfl⟩
        show 0 ≤ φ (C.relativeClass f hC)
        rw [degree_relativeClass hL]
        exact_mod_cast (hpos C hC).le
      · simp
      · intro a b _ _ ha hb
        rw [map_add]
        exact add_nonneg ha hb
      · intro a w _ hw
        change 0 ≤ φ ((a : ℝ) • w)
        rw [map_smul, smul_eq_mul]
        exact mul_nonneg a.2 hw
    · rintro _ ⟨c, hc, rfl⟩
      have hv : v ∈ relativeClosedConeOfCurves sX f :=
        subset_closure (relativeClass_mem_relativeConeOfCurves hC₀)
      exact (relativeClosedConeOfCurves sX f).smul_mem hc hv
  have hv0 : v ≠ 0 := fun h0 => hφv.ne' (by rw [h0, map_zero])
  have hray : MMP.Mori.IsExtremalRay ℝ
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) := by
    refine ⟨⟨subset_rfl, ⟨(relativeClosedConeOfCurves sX f).zero_mem, fun w hw c hc =>
      (relativeClosedConeOfCurves sX f).smul_mem hc.le hw⟩,
      fun a ha b hb => (relativeClosedConeOfCurves sX f).add_mem ha hb,
      fun a ha b hb _ => ⟨ha, hb⟩⟩, v, hv0, hcone⟩
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  have habs := MMP.Mori.isExtremalRay_image_relativeToAbsolute sX sZ f hf.comp_eq hray
  have hvabs : relativeToAbsolute sX f v = OneCycle.numericalClass sX (C₀.cycle ℝ) := rfl
  set R : Set (NumericalCurveClasses sX) :=
    {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) = u}
  have himage : relativeToAbsolute sX f ''
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) = R := by
    rw [hcone]
    ext u
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, by rw [map_smul, hvabs]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • v, ⟨c, hc, rfl⟩, by rw [map_smul, hvabs]⟩
  rw [himage] at habs
  -- the contraction
  have := hf.isProper
  have hsurj : Function.Surjective f := by
    have : IsDominant f := hf.isBirationalMorphism.isDominant
    have hcl : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
    rw [← Set.range_eq_univ, ← hcl.closure_eq, f.denseRange.closure_range]
  have hsep : IsSeparated sZ := hZ.toIsSeparated
  have hlft : LocallyOfFiniteType sZ := hZ.toLocallyOfFiniteType
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZ
  have hcontr : IsContractionOfRay sX sZ R f :=
    { isNormalVariety_source := hXn
      isNormalVariety_target := hZn
      comp_eq := hf.comp_eq
      isProjectiveMorphism := isProjectiveMorphism_of_comp_eq hX hZn.1 hf.comp_eq
      surjective := hsurj
      isIso_app := hf.isIso_app
      isContractedBy_iff := fun C => by
        constructor
        · intro hC
          rw [← himage]
          exact ⟨C.relativeClass f hC,
            subset_closure (relativeClass_mem_relativeConeOfCurves hC), rfl⟩
        · rintro ⟨c, -, hc⟩
          refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hf.comp_eq H
            hHa C ?_
          have h0 := ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hf.comp_eq C₀ hC₀ H
          have h1 := congrArg (NumericalCurveClasses.degree sX
            ((Scheme.Modules.pullback f).obj H)) hc
          rw [map_smul, NumericalCurveClasses.degree_numericalClass,
            NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle,
            OneCycle.degree_cycle, h0, Int.cast_zero, smul_zero] at h1
          exact_mod_cast h1.symm }
  refine ⟨R, C₀, hC₀, rfl, ⟨hD, habs, fun u hu hu0 => ?_⟩, hcontr⟩
  obtain ⟨c, hc, rfl⟩ := hu
  have hc0 : 0 < c := hc.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))
  have hneg : QDivisor.curveForm sX D hD (OneCycle.numericalClass sX (C₀.cycle ℝ)) < 0 := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
    exact_mod_cast MMP.Fourfold.intersectionNumber_neg_of_isContractedBy hamp C₀ hC₀ hD
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg hc0 hneg

end Ray

/-! ### The relative Picard number of the contraction of the ray -/

section Picard

variable {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {f : X ⟶ Z}

variable [QuasiCompact sX]

/-- The degree along a proper curve, as an additive map on Cartier divisors. -/
private noncomputable def curveDegreeHom (C : ProperCurve sX) :
    Divisor.cartierSubgroup (X := X) →+ ℤ where
  toFun E := (E : Divisor X).degreeOn ℂ sX C.ι C.dim_le (Divisor.mem_cartierSubgroup.mp E.2)
  map_zero' := Divisor.degreeOn_zero' ℂ sX C.ι C.dim_le
  map_add' E E' := Divisor.degreeOn_add ℂ sX C.ι C.dim_le _ _ _ _

private theorem curveDegreeHom_apply (C : ProperCurve sX) (E : Divisor X) (hE : E.IsCartier) :
    curveDegreeHom C ⟨E, Divisor.mem_cartierSubgroup.mpr hE⟩ = E.degreeOn ℂ sX C.ι C.dim_le hE :=
  rfl

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] in
private theorem properCurve_degree_congr (C : ProperCurve sX) {L L' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'] (e : L ≅ L') :
    C.degree ℂ L = C.degree ℂ L' :=
  degreeOn_eq_of_iso ℂ sX C.ι C.dim_le e

/-- **`ρ(X/Z) = 1` for the contraction of a negative extremal ray of a klt pair.** If `f` is the
contraction of a `(K + B)`-negative extremal ray `R` of `NE̅(X)` spanned by the class of a curve
`C₀`, for a klt pair `(X, B)` on a projective variety, then `N¹(X) / f^* N¹(Z)` is a line: the
linear form `D ↦ (D · C₀)` is onto, and a divisor of degree zero on `C₀` is numerically a
combination of pull-backs, since a line bundle of degree zero on the curves of `R` descends to
`Z` (Kollár–Mori 3.7(4)). -/
private theorem relativePicardNumberN1_eq_one (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {n : ℕ} {K : Divisor X} {B : QDivisor X}
    (hklt : MMP.Mori.IsKltPair sX n K B) (hBe : B.IsEffective)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + B) R)
    (hc : IsContractionOfRay sX sZ R f) {C₀ : ProperCurve sX}
    (hRC : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) = u}) :
    relativePicardNumberN1 sX f = 1 := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  have : IsSeparated sZ := hZ.toIsSeparated
  have : LocallyOfFiniteType sZ := hZ.toLocallyOfFiniteType
  obtain ⟨hQ, hray, hneg⟩ := hR
  have hF : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
      (QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2) R :=
    ⟨hray.1, hray.1.2.2.1, fun z hz hz0 => hneg z hz hz0⟩
  have hg : IsContractionOfFace ℂ sX sZ R f :=
    { isProjectiveVariety_source := hX
      isProjectiveVariety_target := hZ
      comp_eq := hc.comp_eq
      isExtremalFace := hray.1
      isContractedBy_iff := hc.isContractedBy_iff
      isIso_app := hc.isIso_app }
  -- line bundles of degree zero on `C₀` descend to `Z`
  have hdesc : ∀ (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L],
      C₀.degree ℂ L = 0 → ∃ LZ : Z.Modules,
        SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 LZ ∧
          Nonempty (L ≅ (Scheme.Modules.pullback f).obj LZ) := by
    intro L _ hL0
    refine MMP.Mori.exists_isInvertible_iso_pullback_of_isContractionOfFace hklt hBe hF hg L
      fun C hC => ?_
    rw [hRC] at hC
    obtain ⟨c, -, hc⟩ := hC
    have h1 := congrArg (NumericalCurveClasses.degree sX L) hc
    rw [map_smul, NumericalCurveClasses.degree_numericalClass,
      NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, OneCycle.degree_cycle,
      hL0, Int.cast_zero, smul_zero] at h1
    exact_mod_cast h1.symm
  -- the linear form `D ↦ (D · C₀)` on `N¹(X)`
  let ψ : NumericalDivisorClasses sX →ₗ[ℝ] ℝ :=
    (numericallyTrivialDivisors sX).liftQ
      ((OneCycle.intersectionPairing (sX := sX)).flip (C₀.cycle ℝ))
      (fun D hD => LinearMap.mem_ker.mpr ((mem_numericallyTrivialDivisors.mp hD) C₀))
  have hψ : ∀ D, ψ (numericalDivisorClass sX D) = (C₀.cycle ℝ).intersectionNumber D :=
    fun D => rfl
  -- the class of `C₀` is nonzero
  have hC₀ne : OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hRv⟩ := hray.2
    have hvR : v ∈ R := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
    rw [hRC] at hvR
    obtain ⟨c, -, hcv⟩ := hvR
    rw [h0, smul_zero] at hcv
    exact hv0 hcv.symm
  obtain ⟨Es, hEs⟩ : ∃ E : X.CartierDivisor,
      (C₀.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ) ≠ 0 := by
    by_contra hno
    push Not at hno
    refine hC₀ne ((Submodule.Quotient.mk_eq_zero _).mpr
      (OneCycle.mem_numericallyTrivial.mpr fun M _ => ?_))
    obtain ⟨E, ⟨e⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf M
    rw [OneCycle.degree_cycle, properCurve_degree_congr C₀ e]
    exact hno E
  set b : ℤ := C₀.degree ℂ (MMP.CartierDivisor.sheaf Es)
  -- the image of `b E - (E · C₀) Es` in `N¹(X)` is a pull-back class
  have hδ : ∀ E : X.CartierDivisor, numericalDivisorClass sX
      ((b : ℝ) • KCartierDivisor.ofCartier ℝ E -
        (C₀.degree ℂ (MMP.CartierDivisor.sheaf E) : ℝ) •
          KCartierDivisor.ofCartier ℝ Es) ∈ pullbackNumericalClasses sX f := by
    intro E
    set a : ℤ := C₀.degree ℂ (MMP.CartierDivisor.sheaf E)
    obtain ⟨WE, hWE, ⟨eE⟩⟩ := exists_isCartier_divisorialSheaf_iso
      (MMP.CartierDivisor.sheaf E)
    obtain ⟨Ws, hWs, ⟨es⟩⟩ := exists_isCartier_divisorialSheaf_iso
      (MMP.CartierDivisor.sheaf Es)
    have hG : (b • WE - a • Ws).IsCartier := (hWE.zsmul b).sub (hWs.zsmul a)
    haveI := hG.isInvertibleModule_divisorialSheaf
    haveI := hWE.isInvertibleModule_divisorialSheaf
    haveI := hWs.isInvertibleModule_divisorialSheaf
    have hdegG : ∀ C : ProperCurve sX, C.degree ℂ (b • WE - a • Ws).divisorialSheaf =
        b * C.degree ℂ (MMP.CartierDivisor.sheaf E) -
          a * C.degree ℂ (MMP.CartierDivisor.sheaf Es) := by
      intro C
      rw [ProperCurve.degree_divisorialSheaf C _ hG, ← properCurve_degree_congr C eE,
        ← properCurve_degree_congr C es, ProperCurve.degree_divisorialSheaf C _ hWE,
        ProperCurve.degree_divisorialSheaf C _ hWs, ← curveDegreeHom_apply C _ hG,
        ← curveDegreeHom_apply C _ hWE, ← curveDegreeHom_apply C _ hWs]
      rw [show (⟨b • WE - a • Ws, Divisor.mem_cartierSubgroup.mpr hG⟩ :
          Divisor.cartierSubgroup (X := X)) =
          b • ⟨WE, Divisor.mem_cartierSubgroup.mpr hWE⟩ -
            a • ⟨Ws, Divisor.mem_cartierSubgroup.mpr hWs⟩ from rfl, map_sub, map_zsmul,
        map_zsmul, smul_eq_mul, smul_eq_mul]
    obtain ⟨LZ, hLZ, ⟨eZ⟩⟩ := hdesc (b • WE - a • Ws).divisorialSheaf
      (by rw [hdegG]; ring)
    obtain ⟨G', ⟨eG'⟩⟩ := exists_nonempty_iso_cartierDivisor_sheaf
      (b • WE - a • Ws).divisorialSheaf
    have hmem : numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ G') ∈
        pullbackNumericalClasses sX f :=
      Submodule.subset_span ⟨G', LZ, hLZ, ⟨eG'.symm ≪≫ eZ⟩, rfl⟩
    convert hmem using 1
    refine (Submodule.Quotient.eq _).mpr (mem_numericallyTrivialDivisors.mpr fun C => ?_)
    simp only [intersectionNumber_sub, intersectionNumber_smul,
      cycle_intersectionNumber_ofCartier]
    rw [← properCurve_degree_congr C eG', hdegG]
    push_cast
    ring
  -- every class of degree zero on `C₀` is a pull-back class
  have hker : LinearMap.ker ψ = pullbackNumericalClasses sX f := by
    apply le_antisymm
    · intro d hd
      obtain ⟨D, rfl⟩ := Submodule.Quotient.mk_surjective _ d
      have hΦ : ∀ D : KCartierDivisor ℝ X, (b : ℝ) • numericalDivisorClass sX D -
          (C₀.cycle ℝ).intersectionNumber D •
            numericalDivisorClass sX (KCartierDivisor.ofCartier ℝ Es) ∈
          pullbackNumericalClasses sX f := by
        intro D
        induction D using Finsupp.induction_linear with
        | zero => simpa [OneCycle.intersectionNumber] using zero_mem _
        | add D₁ D₂ h₁ h₂ =>
          rw [intersectionNumber_add, map_add, smul_add, add_smul]
          convert add_mem h₁ h₂ using 1
          abel
        | single E c =>
          have hs : Finsupp.single E c = c • KCartierDivisor.ofCartier ℝ E := by
            rw [KCartierDivisor.ofCartier, Finsupp.smul_single, smul_eq_mul, mul_one]
          rw [hs]
          rw [intersectionNumber_smul, cycle_intersectionNumber_ofCartier]
          convert Submodule.smul_mem _ c (hδ E) using 1
          simp only [map_sub, map_smul, smul_sub, smul_smul, mul_comm]
      have h := hΦ D
      rw [show (C₀.cycle ℝ).intersectionNumber D = 0 from hd, zero_smul, sub_zero] at h
      have := Submodule.smul_mem _ ((b : ℝ)⁻¹) h
      rwa [smul_smul, inv_mul_cancel₀ hEs, one_smul] at this
    · rw [pullbackNumericalClasses, Submodule.span_le]
      rintro _ ⟨E, M, hM, ⟨e⟩, rfl⟩
      change ψ _ = 0
      rw [hψ, cycle_intersectionNumber_ofCartier, properCurve_degree_congr C₀ e,
        ProperCurve.degree_pullback_eq_zero_of_isContractedBy f hc.comp_eq C₀ ?_ M, Int.cast_zero]
      rw [hc.isContractedBy_iff, hRC]
      exact ⟨1, zero_le_one, one_smul _ _⟩
  have hsurj : Function.Surjective ψ := by
    intro r
    refine ⟨numericalDivisorClass sX
      ((r / (b : ℝ)) • KCartierDivisor.ofCartier ℝ Es), ?_⟩
    rw [hψ, intersectionNumber_smul, cycle_intersectionNumber_ofCartier, div_mul_cancel₀ _ hEs]
  rw [relativePicardNumberN1, ((Submodule.quotEquivOfEq _ _ hker.symm).trans
    (ψ.quotKerEquivOfSurjective hsurj)).rank_eq, Module.rank_self]
  simp

end Picard

/-! ### Klt pairs and flips of step diagrams -/

section Assembly

/-- **A klt pair is dlt**, with the whole of `X` as the exceptional closed subset: all log
discrepancies are positive, and the coefficient `c` of a prime divisor `D` of `X` has
`1 - c = a(ord_D; X, B) > 0`. -/
private theorem isDltPair_of_isKltPair {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {B : QDivisor X} (h : MMP.Fourfold.IsKltPair sX B) :
    MMP.Intersection.IsDltPair sX B := by
  obtain ⟨hP, hpos⟩ := h
  refine ⟨⟨hP.isPair, hP.nonneg, fun n D a ha => (hpos n D a ha).le⟩, fun P => ?_, ⊤, ?_, ?_,
    fun n D _ a ha => hpos n D a ha⟩
  · have hvar := hP.isPair.1
    obtain ⟨n, hn⟩ := MMP.Fourfold.isLogDiscrepancy_ofPrimeDivisor hvar hP.isPair P
    have h1 := hpos n _ _ hn
    have h2 : (B.coeff P : ℝ) < 1 := by linarith
    exact_mod_cast h2.le
  · ext x
    exact (x.2 (Set.mem_univ _)).elim
  · exact ⟨fun E _ => (E.genericPoint.2 (Set.mem_univ _)).elim,
      fun x => (x.2 (Set.mem_univ _)).elim⟩

variable {X X' Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
  {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
  {f : X ⟶ Z} {fp : X' ⟶ Z}

/-- A threefold step diagram whose negative side is a small contraction is a flip of
`K + B`. -/
private theorem isFlipOf_of_isThreefoldStepDiagram {K : Divisor X} {B : QDivisor X}
    (h : IsThreefoldStepDiagram sX sZ sX' K B f fp) (hs : IsSmallMorphism sX sZ f)
    {R : Set (NumericalCurveClasses sX)} (hc : IsContractionOfRay sX sZ R f) :
    IsFlipOf sX sZ sX' (Divisor.toQDivisor K + B) f fp := by
  have htr : flipTransform f fp (Divisor.toQDivisor K + B) =
      Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp B := by
    rw [map_add, flipTransform_toQDivisor]
  exact
    { isQCartier := h.isQCartier_minus
      isContraction := hc.toIsContraction
      isSmallMorphism := hs
      hasRelativelyAmpleMultiple := h.hasRelativelyAmpleMultiple_minus
      isSmallMorphism_flip := h.isSmallMorphism_plus
      isProjectiveMorphism_flip := h.isProjectiveMorphism_plus
      isQCartier_flip := htr ▸ h.isQCartier_plus
      hasRelativelyAmpleMultiple_flip := htr ▸ h.hasRelativelyAmpleMultiple_plus }

end Assembly

end MMP.IndexTailFromSequence

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

open MMP.IndexTailFromSequence in
/-- **An infinite projective flip sequence has a stabilized tail.** Let `S` be an infinite
sequence of flips of an effective rational klt pair `(X, B)` on a normal projective `ℚ`-factorial
complex threefold `X` with canonical divisor `K`, all of whose models and contraction targets are
projective. Then there is `i₀` and a stabilized tail `T` whose `i`-th model, boundary, target,
contraction and flip are those of the `(i₀ + i)`-th step of `S`. -/
@[mmp "lem_mmp_index_tail_from_sequence"]
public theorem exists_stabilizedTail_of_sequenceOfFlips
    (X : Scheme.{0}) [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (K : Divisor X) (B : QDivisor X)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hdim : topologicalKrullDim X = 3)
    (hQ : IsQFactorial sX) (hBeff : B.IsEffective) (hklt : IsKltPair sX B)
    (hB : IsKawamataLogTerminal sX 3 K (QDivisor.toRDivisor B))
    (S : SequenceOfFlips sX 3 K B) (hS : S.length = ⊤)
    (hmodel : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (S.model i).2.1)
    (hbase : ∀ i : ℕ, MMP.Mori.IsProjectiveVariety ℂ (S.baseStr i)) :
    ∃ (i₀ : ℕ) (T : StabilizedTail), ∀ i : ℕ,
      (∃ K' : Divisor (S.model (i₀ + i)).1,
        (⟨T.X i, T.sX i, T.K i, T.B i⟩ : FlipModel ℂ) =
          ⟨(S.model (i₀ + i)).1, (S.model (i₀ + i)).2.1, K', (S.model (i₀ + i)).2.2.2⟩) ∧
      (⟨T.Z i, T.sZ i⟩ : Σ Z : Scheme.{0}, Z ⟶ Spec (.of ℂ)) =
        ⟨S.base (i₀ + i), S.baseStr (i₀ + i)⟩ ∧
      Arrow.mk (T.f i) = Arrow.mk (S.contraction (i₀ + i)) ∧
      Arrow.mk (T.fp i) = Arrow.mk (S.flip (i₀ + i)) := by
  have hlt : ∀ j : ℕ, (j : ℕ∞) < S.length := fun j => by rw [hS]; exact ENat.coe_lt_top j
  have hlt1 : ∀ j : ℕ, ((j + 1 : ℕ) : ℕ∞) < S.length := fun j => hlt (j + 1)
  have hXn : ∀ j, IsNormalVariety ℂ (S.model j).2.1 := fun j => S.isNormalVariety_model j (hlt j)
  haveI hI : ∀ j, IsIntegral (S.model j).1 := fun j => (hXn j).1.toIsIntegral
  haveI := S.isLocallyNoetherian_model
  haveI := S.isNormal_model
  haveI := S.compactSpace_model
  haveI hqc : ∀ j, QuasiCompact (S.model j).2.1 := fun j => (hXn j).1.toQuasiCompact
  -- the data of the steps
  have hneg := fun j => S.isNegativeExtremalContraction j (hlt1 j)
  have hflip := fun j => S.isFlip j (hlt1 j)
  have hcanS := fun j => S.isCanonicalDivisor_model j (hlt j)
  have hZn : ∀ j, IsNormalVariety ℂ (S.baseStr j) := fun j => (hneg j).isNormalVariety_target
  -- the canonical divisors of the tail: strict transforms of the first one
  obtain ⟨KT, hKT0, hKTs⟩ : ∃ KT : ∀ j, Divisor (S.model j).1, KT 0 = (S.model 0).2.2.1 ∧
      ∀ j, KT (j + 1) = flipTransform (S.contraction j) (S.flip j) (KT j) :=
    ⟨fun j => Nat.rec (motive := fun j => Divisor (S.model j).1) (S.model 0).2.2.1
      (fun j KTj => flipTransform (S.contraction j) (S.flip j) KTj) j, rfl, fun _ => rfl⟩
  have hKT : ∀ j, MMP.Mori.Divisor.IsCanonicalDivisor (S.model j).2.1 3 (KT j) := by
    intro j
    induction j with
    | zero => rw [hKT0]; exact hcanS 0
    | succ j ih =>
      rw [hKTs]
      exact isCanonicalDivisor_flipTransform (hZn j) (hflip j).isSmall_source (hflip j).isSmall ih
  -- the boundaries are strict transforms, with nonnegative coefficients
  have hBeq : ∀ j, (S.model (j + 1)).2.2.2 =
      flipTransform (S.contraction j) (S.flip j) (S.model j).2.2.2 := fun j =>
    (S.transform_eq j (hlt1 j)).trans (transformDivisor_eq_flipTransform (hZn j)
      (hflip j).isSmall_source (hflip j).isSmall (hflip j).isModificationOf _)
  have h0 : ∀ m : FlipModel ℂ, m = ⟨X, sX, K, B⟩ → ∀ [IsIntegral m.1] [IsLocallyNoetherian m.1]
      [IsNormal m.1], (∀ P, 0 ≤ m.2.2.2.coeff P) ∧ IsQFactorial m.2.1 ∧
        MMP.Fourfold.IsKltPair m.2.1 m.2.2.2 := by
    rintro m rfl _ _ _
    exact ⟨hBeff, hQ, hklt⟩
  obtain ⟨hB0, hQ0, hklt0⟩ := h0 (S.model 0) S.model_zero
  have hBnn : ∀ j P, 0 ≤ (S.model j).2.2.2.coeff P := by
    intro j
    induction j with
    | zero => exact hB0
    | succ j ih => rw [hBeq]; exact flipTransform_coeff_nonneg _ _ ih
  -- every step is a threefold step diagram with small negative side
  have hstep : ∀ j, IsThreefoldStepDiagram (S.model j).2.1 (S.baseStr j) (S.model (j + 1)).2.1
      (KT j) (S.model j).2.2.2 (S.contraction j) (S.flip j) := fun j =>
    isThreefoldStepDiagram_of_isFlip (hmodel j) (hmodel (j + 1)) (hbase j) (hcanS j) (hKT j)
      (hcanS (j + 1)) (hBnn j) (hneg j) (hflip j)
  have hsmall : ∀ j, IsSmallMorphism (S.model j).2.1 (S.baseStr j) (S.contraction j) := fun j =>
    isSmallMorphism_of_isSmall (hZn j) (hflip j).isSmall_source
  -- the rays
  choose R C₀ hC₀ hRC hRay hCon using fun j =>
    exists_isNegativeExtremalRayOf_isContractionOfRay (hmodel j) (hbase j) (hXn j) (hZn j)
      (hflip j).isSmall_source (hneg j).relativePicardNumber_eq_one (hstep j).isQCartier_minus
      (hstep j).hasRelativelyAmpleMultiple_minus
  -- klt pairs and stabilization of the low-discrepancy sets
  obtain ⟨hkltall, i₀, hi₀⟩ := isKltPair_and_exists_lowDiscrepancySet_eq_of_isSmallMorphism
    (fun j => (S.model j).1) (fun j => (S.model j).2.1) KT (fun j => (S.model j).2.2.2) S.base
    S.baseStr S.contraction S.flip hstep hKTs hBeq hsmall hklt0
  -- `ℚ`-factoriality propagates along the elementary dlt steps
  have hQF : ∀ j, IsQFactorial (S.model j).2.1 := by
    intro j
    induction j with
    | zero => exact hQ0
    | succ j ih =>
      exact (IsProjectiveElementaryDltStep.isQFactorial_and_isDltPair
        { isProjectiveQFactorialDltPair := ⟨hmodel j, ih, ⟨3, hKT j⟩,
            isDltPair_of_isKltPair (hkltall j)⟩
          isNegativeExtremalRayOf := hRay j
          isContractionOfRay := hCon j
          isBirationalMorphism := (hstep j).isBirationalMorphism_minus
          comp_eq := (hstep j).comp_eq_plus
          eq_flipTransform := hBeq j
          flip_or_divisorial := Or.inl ⟨hsmall j,
            isFlipOf_of_isThreefoldStepDiagram (hstep j) (hsmall j) (hCon j)⟩ }).1
  -- the relative Picard numbers
  have hρ : ∀ j, relativePicardNumberN1 (S.model j).2.1 (S.contraction j) = 1 := fun j =>
    relativePicardNumberN1_eq_one (hmodel j) (hbase j)
      ((MMP.Fourfold.isKltPair_iff_mori_isKltPair _ (hKT j) (hkltall j).1).mp (hkltall j))
      (hBnn j) (hRay j) (hCon j) (hRC j)
  refine ⟨i₀,
    { X := fun i => (S.model (i₀ + i)).1
      sX := fun i => (S.model (i₀ + i)).2.1
      isIntegral := fun i => hI (i₀ + i)
      compactSpace := fun i => S.compactSpace_model (i₀ + i)
      isLocallyNoetherian := fun i => S.isLocallyNoetherian_model (i₀ + i)
      isNormal := fun i => S.isNormal_model (i₀ + i)
      K := fun i => KT (i₀ + i)
      B := fun i => (S.model (i₀ + i)).2.2.2
      Z := fun i => S.base (i₀ + i)
      sZ := fun i => S.baseStr (i₀ + i)
      f := fun i => S.contraction (i₀ + i)
      fp := fun i => S.flip (i₀ + i)
      R := fun i => R (i₀ + i)
      isKltPair := fun i => hkltall (i₀ + i)
      isProjectiveVariety := fun i => hmodel (i₀ + i)
      isQFactorial := fun i => hQF (i₀ + i)
      dim_eq := fun i => (hstep (i₀ + i)).dim_minus
      isThreefoldStepDiagram := fun i => hstep (i₀ + i)
      K_eq := fun i => hKTs (i₀ + i)
      B_eq := fun i => hBeq (i₀ + i)
      isSmallMorphism := fun i => hsmall (i₀ + i)
      isNegativeExtremalRayOf := fun i => hRay (i₀ + i)
      isContractionOfRay := fun i => hCon (i₀ + i)
      relativePicardNumber_eq_one := fun i => hρ (i₀ + i)
      lowDiscrepancySet_eq := fun i => hi₀ (i₀ + i) (Nat.le_add_right _ _) },
    fun i => ⟨⟨KT (i₀ + i), rfl⟩, rfl, rfl, rfl⟩⟩

end MMP.Fourfold

end
