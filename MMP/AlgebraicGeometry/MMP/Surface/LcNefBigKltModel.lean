module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDropDlt
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.KltRayLength
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialQFactorial
public import MMP.AlgebraicGeometry.MMP.Contraction.RelativeNegativeRay
public import MMP.AlgebraicGeometry.MMP.Surface.CrepantDltModification
public import MMP.AlgebraicGeometry.MMP.Contraction.DivisorialContractionKlt
public import MMP.AlgebraicGeometry.MMP.Contraction.PicardNumberDrop
public import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
public import MMP.AlgebraicGeometry.Positivity.RelativeNefBigSurface
public import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
public import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.AlgebraicGeometry.Intersection.PicardNumberFiniteComplex
public import MMP.Analysis.Complex.CauchyTransformRungeMontel
public import MMP.AlgebraicGeometry.Resolution.BlowupExceptionalAmple
public import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
public import MMP.AlgebraicGeometry.Morphisms.VarietyFibreDimension
public import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Positivity.BigBirationalTransform
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.Positivity.RelativeKodairaDecomposition
public import MMP.AlgebraicGeometry.Divisor.OrderPullback
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
public import MMP.AlgebraicGeometry.Singularities.Surface.PointBlowupLogDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyBoundaryChange
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleExceptionalCurve
public import MMP.AlgebraicGeometry.ChowForm.AvoidingPair
public import MMP.AlgebraicGeometry.ChowForm.FibreDegreeRank
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.AlgebraicGeometry.Singularities.Adjunction.CartierCodimTwo
public import MMP.AlgebraicGeometry.Morphisms.Birational.BiregularLocusCodimOnePoints
public import MMP.AlgebraicGeometry.Vanishing.CoveringTrick
public import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.Divisor.AlgebraicHartogsUnits
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.Relative
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Fourfold.Program
public import MMP.AlgebraicGeometry.Chow.FieldSituation

section

/-!
# A klt `ε`-model of a nef and big lc adjoint on a projective surface

Let `(X, B)` be an lc pair on a normal projective complex surface, `B ≥ 0`, and `f : X ⟶ Z` a
morphism to a projective variety with `D = K_X + B` relatively nef and big. The model is obtained
by running a surface program over `Z` from a crepant dlt modification `(Y₀, Δ₀)` of `(X, B)`.

At every stage `(Y, B_Y)` the pair is lc and `ℚ`-factorial, `D_Y = K_Y + B_Y` is nef and big over
`Z` with pull-back `D_{Y₀}` to `Y₀`, and `(Y, B_Y - δ⌊B_Y⌋)` is klt for `0 < δ ≤ 1/2`. With `r`
a Cartier index of `D_Y` and `η = 1/(2(1 + 4r))`, either `D_Y - η⌊B_Y⌋` is nef over `Z`, and the
model is final with `ε = η/2`, or there is a `(D_Y - η⌊B_Y⌋)`-negative extremal ray `R` over
`Z`. By the length of extremal rays of the klt pair `(Y, B_Y - ⌊B_Y⌋/2)` a generator `C` of `R`
has `-(D_Y - ⌊B_Y⌋/2) · C ≤ 4`, and integrality of `r D_Y · C` forces `D_Y · C = 0`. Hence `R`
is negative for every `D_Y - δ⌊B_Y⌋`, `δ > 0`; bigness of `D_Y` excludes a contraction of fibre
type and a contracted curve excludes a small one, so the contraction of `R` is divisorial. It
preserves the klt pairs, `ℚ`-factoriality and, since `D_Y` is trivial on `R`, `D_Y` is the
pull-back of its push-forward. The Picard number drops, so the program stops.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

open CategoryTheory AlgebraicGeometry MMP.Mori

namespace MMP.FourfoldProofs.MmpSurfaceProjectiveLcNefBigEpsilonModelProof

/-- A nonnegative combination of relatively nef divisors on a `ℚ`-factorial variety is
relatively nef. -/
private theorem isRelativelyNef_smul_add_smul_of_isQFactorial {k : Type} [Field k]
    {X Y : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] (hQ : MMP.Fourfold.IsQFactorial sX)
    {f : X ⟶ Y} {L M : QDivisor X} (hL : L.IsRelativelyNef sX f) (hM : M.IsRelativelyNef sX f)
    {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a • L + b • M).IsRelativelyNef sX f := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hq := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX (hq _)
    fun C hC => ?_
  rw [QDivisor.intersectionNumber_add' k sX C.ι C.dim_le _ _ (hq _) (hq _) (hq _),
    MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le L (hq L) a (hq _),
    MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le M (hq M) b (hq _)]
  have h1 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hL (hq L) C hC
  have h2 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hM (hq M) C hC
  positivity

/-- For `0 ≤ B ≤ 1` and `0 ≤ δ ≤ 1`, the boundary `B - δ⌊B⌋` is effective. -/
private theorem nonneg_sub_smul_roundDown {X : Scheme.{0}} {B : QDivisor X} (hB : 0 ≤ B)
    (hB1 : ∀ P, B.coeff P ≤ 1) {δ : ℚ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    0 ≤ B - δ • Divisor.toQDivisor B.roundDown := by
  refine Finsupp.le_def.mpr fun P => ?_
  have h0 : 0 ≤ B P := Finsupp.le_def.mp hB P
  have h1 : B P ≤ 1 := hB1 P
  have hfl : (Divisor.toQDivisor B.roundDown) P = (⌊B P⌋ : ℚ) := rfl
  simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, hfl]
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h, Int.floor_one, Int.cast_one]
    linarith
  · rw [Int.floor_eq_zero_iff.mpr ⟨h0, h⟩, Int.cast_zero, mul_zero, sub_zero]
    exact h0

/-- On a `ℚ`-factorial variety, `((K + (B - δT)) · C) = ((K + B) · C) - δ (T · C)`. -/
private theorem intersectionNumber_add_sub_smul {k : Type} [Field k] {X : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] (hq : ∀ G : QDivisor X, G.IsQCartier) (K : Divisor X) (B T : QDivisor X)
    (δ : ℚ) (C : ProperCurve sX) :
    (Divisor.toQDivisor K + (B - δ • T)).intersectionNumber k sX C.ι C.dim_le (hq _) =
      (Divisor.toQDivisor K + B).intersectionNumber k sX C.ι C.dim_le (hq _) -
        δ * T.intersectionNumber k sX C.ι C.dim_le (hq _) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have e : Divisor.toQDivisor K + (B - δ • T) = (Divisor.toQDivisor K + B) + (-δ) • T := by
    rw [neg_smul]
    abel
  rw [MMP.Fourfold.intersectionNumber_congr sX C.ι C.dim_le (hq _) (hq _) e,
    QDivisor.intersectionNumber_add' k sX C.ι C.dim_le _ _ (hq _) (hq _) (hq _),
    MMP.Fourfold.intersectionNumber_smul sX C.ι C.dim_le T (hq T) (-δ) (hq _)]
  ring

/-- **`D` is trivial on the negative ray.** Let `R = ℝ_{≥0}[C₀]` be a `(D - η⌊B⌋)`-negative
extremal ray, `C₀` contracted by `f`, with `D = K + B` `f`-nef, `rD` Cartier and
`η = 1/(2(1 + 4r))`. A rational generator `C` of `R` given by the length of extremal rays of the
klt pair `(X, B - ⌊B⌋/2)` has `-(D - ⌊B⌋/2) · C ≤ 4`; if `D · C > 0` then `D · C ≥ 1/r`, which
contradicts `(D - η⌊B⌋) · C < 0`. Hence `D` vanishes on `R`, and `R` is negative for every
`D - δ⌊B⌋` with `δ > 0`. -/
private theorem curveForm_eq_zero_and_neg_of_ray {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sX] [CompactSpace X]
    (hQ : MMP.Fourfold.IsQFactorial sX) {K : Divisor X} {B : QDivisor X}
    (hklt : IsKltPair sX 2 K (B - (1 / 2 : ℚ) • Divisor.toQDivisor B.roundDown))
    (hB : 0 ≤ B - (1 / 2 : ℚ) • Divisor.toQDivisor B.roundDown) {f : X ⟶ Z}
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f) {r : ℕ} (hr : 0 < r)
    {E : Divisor X} (hE : Divisor.toQDivisor E = (r : ℤ) • (Divisor.toQDivisor K + B))
    (hEc : E.IsCartier) {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy f)
    (hRC₀ : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C₀.cycle ℝ) = w})
    {hη : (Divisor.toQDivisor K +
      (B - (1 / (2 * (1 + 4 * r)) : ℚ) • Divisor.toQDivisor B.roundDown)).IsQCartier}
    (hneg : ∀ u ∈ R, u ≠ 0 → MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K +
      (B - (1 / (2 * (1 + 4 * r)) : ℚ) • Divisor.toQDivisor B.roundDown)) hη u < 0) :
    (∀ u ∈ R, MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + B)
      (MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _) u = 0) ∧
    ∀ δ : ℚ, 0 < δ → ∀ u ∈ R, u ≠ 0 → MMP.Fourfold.QDivisor.curveForm sX
      (Divisor.toQDivisor K + (B - δ • Divisor.toQDivisor B.roundDown))
      (MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _) u < 0 := by
  have hq := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ
  set T : QDivisor X := Divisor.toQDivisor B.roundDown with hT
  set x₀ := OneCycle.numericalClass sX (C₀.cycle ℝ) with hx₀
  -- the curve form along the ray through `x₀` is read off on `C₀`
  have hcf : ∀ (G : QDivisor X) (hG : G.IsQCartier) (c : ℝ),
      MMP.Fourfold.QDivisor.curveForm sX G hG (c • x₀) =
        c * (G.intersectionNumber ℂ sX C₀.ι C₀.dim_le hG : ℝ) := fun G hG c => by
    rw [map_smul, smul_eq_mul, MMP.ProgramBaseChange.curveForm_numericalClass_cycle]
  have hsub := fun δ : ℚ => intersectionNumber_add_sub_smul (k := ℂ) hq K B T δ C₀
  set a : ℚ := (Divisor.toQDivisor K + B).intersectionNumber ℂ sX C₀.ι C₀.dim_le (hq _)
    with ha
  set t : ℚ := T.intersectionNumber ℂ sX C₀.ι C₀.dim_le (hq _) with ht
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  -- `x₀ ≠ 0`, so `(D - ηT) · C₀ < 0`
  obtain ⟨v, hv0, hRv⟩ := hR.2
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul ℝ v⟩
  rw [hRC₀] at hvR
  obtain ⟨c, -, hcv⟩ := hvR
  have hx₀R : x₀ ∈ R := hRC₀ ▸ ⟨1, zero_le_one, one_smul ℝ x₀⟩
  have hx₀0 : x₀ ≠ 0 := fun h => hv0 (by rw [← hcv, h, smul_zero])
  have hat : a - 1 / (2 * (1 + 4 * r)) * t < 0 := by
    have h1 := hneg x₀ hx₀R hx₀0
    rw [← one_smul ℝ x₀, hcf, one_mul, hsub] at h1
    exact_mod_cast h1
  have ha0 : 0 ≤ a :=
    MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef (hq _) C₀ hC₀
  have hη : 0 < (1 / (2 * (1 + 4 * r)) : ℚ) := by positivity
  have hη2 : (1 / (2 * (1 + 4 * r)) : ℚ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have ht0 : 0 < t := by
    by_contra h
    push Not at h
    nlinarith
  -- a point of `R` is `c • x₀` with `c > 0` once it is nonzero
  have hpos_of_mem : ∀ u ∈ R, u ≠ 0 → ∃ c : ℝ, 0 < c ∧ c • x₀ = u := fun u hu hu0 => by
    rw [hRC₀] at hu
    obtain ⟨c, hc, rfl⟩ := hu
    exact ⟨c, lt_of_le_of_ne hc (by rintro rfl; exact hu0 (zero_smul _ _)), rfl⟩
  -- `R` is negative for `D - ⌊B⌋/2`
  have hneg' : MMP.Fourfold.IsNegativeExtremalRayOf sX
      (Divisor.toQDivisor K + (B - (1 / 2 : ℚ) • T)) R := by
    refine ⟨hq _, hR, fun u hu hu0 => ?_⟩
    obtain ⟨c, hc, rfl⟩ := hpos_of_mem u hu hu0
    rw [hcf, hsub]
    refine mul_neg_of_pos_of_neg hc ?_
    have : a - 1 / 2 * t < 0 := by nlinarith
    exact_mod_cast this
  obtain ⟨T₀, -, hRT₀, hpos, hle⟩ :=
    MMP.Fourfold.exists_isRationalCurve_eq_ray_of_isNegativeExtremalRayOf sX hklt hB hneg'
  -- `[T₀] = s • x₀`
  have hT₀R : OneCycle.numericalClass sX (T₀.cycle ℝ) ∈ R :=
    hRT₀ ▸ ⟨1, zero_le_one, one_smul ℝ _⟩
  rw [hRC₀] at hT₀R
  obtain ⟨s, hs, hsx⟩ := hT₀R
  rw [← hsx, hcf, hsub] at hpos hle
  -- integrality: `D · T₀ = deg_{T₀} E / r`
  have hint : (s : ℝ) * (a : ℝ) =
      ((E.degreeOn ℂ sX T₀.ι T₀.dim_le hEc : ℤ) : ℝ) / (r : ℝ) := by
    have h1 := hcf (Divisor.toQDivisor K + B) (hq _) s
    rw [hsx, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_smul ℂ sX T₀.ι T₀.dim_le _ (hq _) hr E hEc hE] at h1
    rw [← h1]
    push_cast
    ring
  have ha_eq : a = 0 := by
    refine le_antisymm ?_ ha0
    by_contra hapos
    push Not at hapos
    have hapos' : (0 : ℝ) < a := by exact_mod_cast hapos
    have hspos : 0 < s := by
      rcases eq_or_lt_of_le hs with h | h
      · rw [← h] at hpos
        simp at hpos
      · exact h
    set n : ℤ := E.degreeOn ℂ sX T₀.ι T₀.dim_le hEc
    have hr'' : (0 : ℝ) < r := by exact_mod_cast hr
    have hn : (0 : ℝ) < n := by
      have : (0 : ℝ) < s * a := mul_pos hspos hapos'
      rw [hint] at this
      exact (div_pos_iff_of_pos_right hr'').mp this
    have hn1 : (1 : ℝ) ≤ n := by
      have : (0 : ℤ) < n := by exact_mod_cast hn
      exact_mod_cast this
    have hsa : 1 ≤ (r : ℝ) * (s * a) := by
      rw [hint, mul_div_cancel₀ _ hr''.ne']
      exact hn1
    have hat' : ((a - 1 / (2 * (1 + 4 * r)) * t : ℚ) : ℝ) < 0 := by exact_mod_cast hat
    push_cast at hat' hle
    have hden : (0 : ℝ) < 2 * (1 + 4 * r) := by positivity
    have h1 : (a : ℝ) * (2 * (1 + 4 * r)) < t := by
      have e : 1 / (2 * (1 + 4 * (r : ℝ))) * t = t / (2 * (1 + 4 * r)) := by ring
      have h0 : (a : ℝ) < t / (2 * (1 + 4 * r)) := by linarith
      rwa [lt_div_iff₀ hden] at h0
    have h2 : s * (a * (2 * (1 + 4 * r))) < s * t := mul_lt_mul_of_pos_left h1 hspos
    nlinarith
  refine ⟨fun u hu => ?_, fun δ hδ u hu hu0 => ?_⟩
  · rw [hRC₀] at hu
    obtain ⟨c, -, rfl⟩ := hu
    rw [hcf, ← ha, ha_eq, Rat.cast_zero, mul_zero]
  · obtain ⟨c, hc, rfl⟩ := hpos_of_mem u hu hu0
    rw [hcf, hsub, ha_eq]
    refine mul_neg_of_pos_of_neg hc ?_
    have : (0 : ℚ) - δ * t < 0 := by nlinarith
    exact_mod_cast this

/-- An ample Cartier divisor on a variety has positive degree on every proper curve. -/
private theorem degreeOn_pos_of_isAmple {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] (hX : MMP.Mori.IsVariety ℂ sX)
    {H : Divisor X} (hH : H.IsCartier) (hamp : H.IsAmple hH) (C : ProperCurve sX) :
    0 < H.degreeOn ℂ sX C.ι C.dim_le hH := by
  haveI := hH.isInvertibleModule_divisorialSheaf
  have hrel := MMP.Threefold.Resolution.isRelativelyAmple_of_isAmple sX H.divisorialSheaf hamp
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple hX sX H.divisorialSheaf hrel C
    fun _ _ => Subsingleton.elim _ _

/-- **The contraction of a `D`-trivial ray is divisorial when `D` is big.** For a `ℚ`-factorial
projective surface `X` over `ℂ` and the contraction `g` of an extremal ray `R` over `Z`
(`g ≫ h = f`), contracting a curve `C₀`: if `D` is `f`-big and trivial on the curves contracted
by `g`, then `g` is not of fibre type (write `D ∼_ℚ H + E - c w` with `H` ample, `E ≥ 0` and `w`
pulled back from `Z`; a contracted curve avoiding `Supp E` and the fibres over the support of
the pulled-back divisor has `D · Γ ≥ H · Γ > 0`), and not small (the generic point of `C₀` lies
in `Ex(g)`, as `g` is injective over its biregular locus and a curve has no locally closed
generic point), hence divisorial. -/
private theorem isDivisorialContraction_of_isRelativelyBig {X V Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sX] [CompactSpace X]
    (hQ : MMP.Fourfold.IsQFactorial sX) {K : Divisor X} (hK : K.IsCanonicalDivisor sX 2)
    {B : QDivisor X} {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {sV : V ⟶ Spec (.of ℂ)} {g : X ⟶ V} (hg : IsContractionOfFace ℂ sX sV R g)
    {sZ : Z ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sZ] {f : X ⟶ Z}
    {h : V ⟶ Z} (hgh : g ≫ h = f) (hf : f ≫ sZ = sX)
    (hbig : (Divisor.toQDivisor K + B).IsRelativelyBig f)
    (hnull : ∀ Γ : ProperCurve sX, Γ.IsContractedBy g →
      (Divisor.toQDivisor K + B).intersectionNumber ℂ sX Γ.ι Γ.dim_le
        (MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _) = 0)
    {C₀ : ProperCurve sX} (hC₀ : C₀.IsContractedBy g) :
    IsDivisorialContraction ℂ sX sV R g := by
  have hq := MMP.Fourfold.isQCartier_of_isQFactorial sX hQ
  have hXv : AlgebraicGeometry.IsVariety ℂ sX := inferInstance
  have hVv : AlgebraicGeometry.IsVariety ℂ sV := hg.isProjectiveVariety_target.toIsVariety
  have : IsProper (g ≫ sV) := hg.comp_eq ▸ inferInstance
  have : IsProper g := IsProper.of_comp g sV
  have : Surjective g := Scheme.Hom.surjective_of_isIso_app g hg.isIso_app
  have : IsProper (f ≫ sZ) := hf ▸ inferInstance
  have : IsProper f := IsProper.of_comp f sZ
  have : LocallyOfFiniteType sX := hXv.toLocallyOfFiniteType
  obtain ⟨htri, -, -, -⟩ := hg.trichotomy_of_isExtremalRay hQ hR
  rcases htri with hfib | hdiv | hsmall
  · -- fibre type is impossible: write `D ∼_ℚ H + E - c w` with `H` ample, `E ≥ 0` and `w` the
    -- Weil divisor of a pull-back from `Z`, and test it on a contracted curve avoiding `Supp E`
    -- and the fibres over `Supp T₀`
    exfalso
    obtain ⟨H, E, hHa, -, hE, c, T₀, T₀', w, hT, hw, ⟨m, hm, φ, hφ⟩⟩ :=
      hbig.exists_qLinearlyEquivalent_add_sub_pullback sX sZ hQ f hf
    set S : Set X := (E.supp : Set X) ∪ f ⁻¹' MMP.Intersection.cartierSupport T₀ with hS
    have hSc : IsClosed S := E.supp.isClosed.union
      ((MMP.Intersection.isClosed_cartierSupport T₀).preimage f.continuous)
    have hηS : genericPoint X ∉ S := by
      rintro (h | h)
      · exact MMP.Fourfold.genericPoint_notMem_supp E h
      · refine hT.1 (genericPoint X) ?_ h
        rw [AlgebraicGeometry.schemeAssociatedPoints_eq_singleton_genericPoint]
        rfl
    obtain ⟨Γ, hΓg, hΓS⟩ :=
      MMP.Fourfold.exists_properCurve_isContractedBy_of_lt hXv hVv g hg.comp_eq hfib.dim_lt hSc hηS
    have hΓf : Γ.IsContractedBy f := fun x hx => by
      rw [← hgh, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hΓg x hx]
    -- the pull-back `T₀'` has no support over the complement of `Supp T₀`
    have hA : ∀ y : X, f y ∉ MMP.Intersection.cartierSupport T₀ →
        y ∉ MMP.Intersection.cartierSupport T₀' := fun y hy => by
      apply MMP.Intersection.notMem_cartierSupport_of_isLocalEquationAt_one
      refine hT.isLocalEquationAt
        (MMP.Intersection.isLocalEquationAt_one_of_notMem_cartierSupport hy)
        (MMP.Intersection.isFraction_one_one_one (f y)) ?_
      rw [map_one]
      exact MMP.Intersection.isFraction_one_one_one y
    -- hence `w` is disjoint from `Γ`
    have hdisj : ∀ x : X, Γ.point ⤳ x → x ∉ (Divisor.toQDivisor w).supp := fun x hx hxw => by
      obtain ⟨P, hP0, hxP⟩ := DivisorWithCoeffs.mem_supp_iff.mp hxw
      have hwP : w.coeff P ≠ 0 := fun h0 => hP0 (by
        rw [Divisor.coeff_toQDivisor, h0, Int.cast_zero])
      have hηP : (MMP.Intersection.primeDivisorSubvariety P).genericPoint ∈
          MMP.Intersection.cartierSupport T₀' := by
        by_contra hη
        exact hwP ((hw P).eq_zero_of_not_subset
          (mt MMP.Intersection.genericPoint_mem_cartierSupport_iff.mpr hη))
      rw [MMP.Intersection.primeDivisorSubvariety_genericPoint] at hηP
      have hxT : x ∈ MMP.Intersection.cartierSupport T₀' := by
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hxP
        exact closure_minimal (Set.singleton_subset_iff.mpr hηP)
          (MMP.Intersection.isClosed_cartierSupport T₀') hxP
      refine hA x ?_ hxT
      rw [hΓf x (specializes_iff_mem_closure.mp hx)]
      exact fun h => hΓS (Or.inr h)
    -- the intersection numbers
    set W : QDivisor X := Divisor.toQDivisor w
    set Pφ : QDivisor X := Divisor.toQDivisor (principalDivisor φ)
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    have e : Divisor.toQDivisor K + B = H + E + (-c) • W + ((m : ℚ)⁻¹) • Pφ := by
      ext P'
      have h1 := congrArg (fun F : QDivisor X => F P') hφ
      simp only [Finsupp.smul_apply, Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply,
        Pi.add_apply, zsmul_eq_mul, smul_eq_mul, Int.cast_natCast] at h1
      change (Divisor.toQDivisor K) P' + B P' = H P' + E P' + -c * W P' + (m : ℚ)⁻¹ * Pφ P'
      field_simp
      linear_combination h1
    have hW0 := MMP.Fourfold.intersectionNumber_eq_zero_of_disjoint sX hQ W (hq _) Γ hdisj
    have hE0 : 0 ≤ E.intersectionNumber ℂ sX Γ.ι Γ.dim_le (hq _) :=
      (MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sX E (hq _)
        (DivisorWithCoeffs.isEffective_iff_nonneg.mp hE) Γ fun h => hΓS (Or.inl h)).1
    obtain ⟨m', hm'0, DH, hDH, hDHc, hDHa⟩ := hHa
    have hH0 : 0 < H.intersectionNumber ℂ sX Γ.ι Γ.dim_le (hq _) := by
      have hm'' : ((m' : ℤ) : ℚ) = (m' : ℚ) := by norm_cast
      rw [QDivisor.intersectionNumber_eq_of_smul ℂ sX Γ.ι Γ.dim_le H (hq _) hm'0 DH hDHc
        (by rw [hDH, ← Int.cast_smul_eq_zsmul ℚ, hm''])]
      have := degreeOn_pos_of_isAmple hXv hDHc hDHa Γ
      positivity
    have hP0 : Pφ.intersectionNumber ℂ sX Γ.ι Γ.dim_le (hq _) = 0 := by
      rw [QDivisor.intersectionNumber_toQDivisor ℂ sX Γ.ι Γ.dim_le _
        (Divisor.isCartier_principalDivisor φ) (hq _)]
      exact_mod_cast MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX Γ.ι Γ.dim_le
        (Divisor.isCartier_principalDivisor φ) ⟨φ, by rw [sub_zero]⟩
    have hD0 := hnull Γ hΓg
    rw [MMP.Fourfold.intersectionNumber_congr sX Γ.ι Γ.dim_le (hq _) (hq _) e,
      QDivisor.intersectionNumber_add' ℂ sX Γ.ι Γ.dim_le _ _ (hq _) (hq _) (hq _),
      QDivisor.intersectionNumber_add' ℂ sX Γ.ι Γ.dim_le _ _ (hq _) (hq _) (hq _),
      QDivisor.intersectionNumber_add' ℂ sX Γ.ι Γ.dim_le _ _ (hq _) (hq _) (hq _),
      MMP.Fourfold.intersectionNumber_smul sX Γ.ι Γ.dim_le _ (hq _) _ (hq _),
      MMP.Fourfold.intersectionNumber_smul sX Γ.ι Γ.dim_le _ (hq _) _ (hq _), hW0, hP0] at hD0
    linarith
  · exact hdiv
  · -- small is impossible: the generic point of `C₀` lies in `Ex(g)`
    exfalso
    have hξ : C₀.point ∈ (exceptionalSet g : Set X) := by
      by_contra hξ
      rw [SetLike.mem_coe, mem_exceptionalSet, not_not] at hξ
      set U := biregularLocus g
      have : IsIso (g ∣_ U) := isBiregular_biregularLocus g
      have hinj : ∀ x ∈ (g ⁻¹ᵁ U : Set X), g x = g C₀.point → x = C₀.point := fun x hx hgx => by
        let p : (g ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
        let p' : (g ⁻¹ᵁ U).toScheme := ⟨C₀.point, hξ⟩
        have hp : ((g ∣_ U) ≫ U.ι) p = g x := by rw [morphismRestrict_ι]; rfl
        have hp' : ((g ∣_ U) ≫ U.ι) p' = g C₀.point := by rw [morphismRestrict_ι]; rfl
        have := ((g ∣_ U) ≫ U.ι).isOpenEmbedding.injective (hp.trans (hgx.trans hp'.symm))
        exact congrArg Subtype.val this
      have hlc : IsLocallyClosed ({C₀.point} : Set X) := by
        have e : ({C₀.point} : Set X) = closure {C₀.point} ∩ (g ⁻¹ᵁ U : Set X) := by
          ext x
          exact ⟨by rintro rfl; exact ⟨subset_closure rfl, hξ⟩,
            fun ⟨hx1, hx2⟩ => hinj x hx2 (hC₀ x hx1)⟩
        rw [e]
        exact isClosed_closure.isLocallyClosed.inter (g ⁻¹ᵁ U).isOpen.isLocallyClosed
      have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
      have hcl := isClosed_singleton_of_isLocallyClosed_singleton hlc
      obtain ⟨w, hw, hne⟩ := MMP.Chow.DeterminantCurveForm.exists_specializes_ne_of_isProperCurve
        sX C₀.point C₀.isProperCurve
      exact hne (hw.mem_closed hcl rfl)
    have h2 := (MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hsmall.two_le_codimension)
      _ hξ
    have hdim := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX C₀.point
    rw [← MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, C₀.isProperCurve.dim_eq,
      hK.topologicalKrullDim_eq] at hdim
    obtain ⟨c, hc⟩ : ∃ c : ℕ∞, Order.coheight C₀.point = c := ⟨_, rfl⟩
    rw [hc] at hdim h2
    have h4 : (1 + c : ℕ∞) = 2 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact hdim)
    have h5 : (1 + 2 : ℕ∞) ≤ 1 + c := add_le_add le_rfl h2
    rw [h4] at h5
    norm_num at h5

/-- The birational transform along a proper birational morphism of normal varieties commutes
with the round-down. -/
private theorem transformDivisor_toQDivisor_roundDown {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {g : X ⟶ Y}
    (hX : IsNormalVariety k (g ≫ sY)) [IsProper g] (hg : IsBirationalMorphism g)
    (B : QDivisor X) :
    RationalMap.transformDivisor g.toRationalMap (Divisor.toQDivisor B.roundDown) =
      Divisor.toQDivisor (RationalMap.transformDivisor g.toRationalMap B).roundDown := by
  ext P
  obtain ⟨E, -, -, hE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hg P
  change _ = ((⌊RationalMap.transformDivisor g.toRationalMap B P⌋ : ℤ) : ℚ)
  rw [DivisorWithCoeffs.coeff_apply, hE, hE]
  rfl

/-- The birational transform along a proper birational morphism preserves `coeff ≤ 1`. -/
private theorem transformDivisor_coeff_le {k : Type} [Field k] {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) {g : X ⟶ Y}
    (hX : IsNormalVariety k (g ≫ sY)) [IsProper g] (hg : IsBirationalMorphism g)
    {B : QDivisor X} (hB : ∀ P, B.coeff P ≤ 1) :
    ∀ P, (RationalMap.transformDivisor g.toRationalMap B).coeff P ≤ 1 := fun P => by
  obtain ⟨E, -, -, hE⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hY hX hg P
  rw [DivisorWithCoeffs.coeff_apply, hE]
  exact hB E

/-- **A null exceptional divisor vanishes.** Let `g : X ⟶ V` be a proper birational morphism of
normal varieties and `H` a `ℚ`-Cartier `ℚ`-divisor on `X` with `g_* H = 0` and `H · Γ = 0` for
every curve `Γ` contracted by `g`. Then `H = 0`: both `H` and `-H` are `g`-nef with effective
push-forward, so both are effective by the negativity lemma. -/
private theorem eq_zero_of_transformDivisor_eq_zero_of_null {X V : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] (hX : IsNormalVariety ℂ sX) (hV : IsNormalVariety ℂ sV) {g : X ⟶ V}
    (hgs : g ≫ sV = sX) [IsProper g] (hg : IsBirationalMorphism g) {H : QDivisor X}
    (hH : H.IsQCartier) (hpush : RationalMap.transformDivisor g.toRationalMap H = 0)
    (hnull : ∀ Γ : ProperCurve sX, Γ.IsContractedBy g →
      H.intersectionNumber ℂ sX Γ.ι Γ.dim_le hH = 0) : H = 0 := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hHn := MMP.Fourfold.Oai4C1.isQCartier_neg hH
  have e : -H = (-1 : ℚ) • H := (neg_one_smul ℚ H).symm
  have hnull' : ∀ Γ : ProperCurve sX, Γ.IsContractedBy g →
      (-H).intersectionNumber ℂ sX Γ.ι Γ.dim_le hHn = 0 := fun Γ hΓ => by
    rw [MMP.Fourfold.intersectionNumber_congr sX Γ.ι Γ.dim_le hHn (e ▸ hHn) e,
      MMP.Fourfold.intersectionNumber_smul sX Γ.ι Γ.dim_le H hH (-1) (e ▸ hHn), hnull Γ hΓ,
      mul_zero]
  have hnef : ∀ (G : QDivisor X) (hG : G.IsQCartier), (∀ Γ : ProperCurve sX,
      Γ.IsContractedBy g → G.intersectionNumber ℂ sX Γ.ι Γ.dim_le hG = 0) →
      G.IsRelativelyNef sX g := fun G hG h0 =>
    MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sX hG
      fun Γ hΓ => (h0 Γ hΓ).ge
  have heff0 : (0 : QDivisor V).IsEffective := DivisorWithCoeffs.isEffective_iff_nonneg.mpr le_rfl
  have h1 : H.IsEffective :=
    QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ sV sX hV hX g
      hgs hg hH (hnef _ hHn hnull') (by rw [hpush]; exact heff0)
  have h2 : (-H).IsEffective :=
    QDivisor.isEffective_of_isEffective_transformDivisor_of_isRelativelyNef_neg ℂ sV sX hV hX g
      hgs hg hHn (by rw [neg_neg]; exact hnef _ hH hnull)
      (by rw [map_neg, hpush, neg_zero]; exact heff0)
  exact le_antisymm (neg_nonneg.mp (DivisorWithCoeffs.isEffective_iff_nonneg.mp h2))
    (DivisorWithCoeffs.isEffective_iff_nonneg.mp h1)

/-- **Descent of a null divisor.** If `g : X ⟶ V` is a proper birational morphism of normal
varieties, `V` is `ℚ`-factorial and the `ℚ`-Cartier `D` is trivial on every curve contracted by
`g`, then `D = g^*(g_* D)`: the difference has push-forward zero and is `g`-numerically trivial,
so it vanishes by the negativity lemma. -/
private theorem isPullback_transformDivisor_of_null {X V : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian V] [IsNormal V]
    {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    (hX : IsNormalVariety ℂ sX) (hV : IsNormalVariety ℂ sV) (hVQ : MMP.Fourfold.IsQFactorial sV)
    {g : X ⟶ V} (hgs : g ≫ sV = sX) [IsProper g] (hg : IsBirationalMorphism g)
    {D : QDivisor X} (hD : D.IsQCartier)
    (hnull : ∀ Γ : ProperCurve sX, Γ.IsContractedBy g →
      D.intersectionNumber ℂ sX Γ.ι Γ.dim_le hD = 0) :
    ∃ hB, QDivisor.IsPullback g (RationalMap.transformDivisor g.toRationalMap D) hB D := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsDominant g := hg.isDominant
  have : IsSeparated sV := hV.1.toIsSeparated
  have : LocallyOfFiniteType sV := hV.1.toLocallyOfFiniteType
  have : QuasiCompact sV := hV.1.toQuasiCompact
  set DV : QDivisor V := RationalMap.transformDivisor g.toRationalMap D with hDVdef
  have hDV : DV.IsQCartier := MMP.Fourfold.isQCartier_of_isQFactorial sV hVQ DV
  have hB : ∀ Z : irreducibleComponents X, g (componentGenericPoint X Z) ∉ DV.supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g DV
  have hG := QDivisor.isPullback_pullback hDV hB
  set G : QDivisor X := QDivisor.pullback DV hDV hB
  have hGq := hG.isQCartier hDV
  have hpush : RationalMap.transformDivisor g.toRationalMap G = DV :=
    MMP.Positivity.transformDivisor_of_isPullback hV (by rw [hgs]; exact hX) hg hDV hB hG
  have hGn : ((-1 : ℚ) • G).IsQCartier := (neg_one_smul ℚ G).symm ▸
    MMP.Fourfold.Oai4C1.isQCartier_neg hGq
  have e : D - G = D + (-1 : ℚ) • G := by rw [neg_one_smul, sub_eq_add_neg]
  have hHq : (D - G).IsQCartier := e ▸ hD.add hGn
  have hzero : D - G = 0 := eq_zero_of_transformDivisor_eq_zero_of_null hX hV hgs hg hHq
    (by rw [map_sub, hpush, sub_self]) fun Γ hΓ => by
      rw [MMP.Fourfold.intersectionNumber_congr sX Γ.ι Γ.dim_le hHq (hD.add hGn) e,
        QDivisor.intersectionNumber_add' ℂ sX Γ.ι Γ.dim_le _ _ hD hGn _,
        MMP.Fourfold.intersectionNumber_smul sX Γ.ι Γ.dim_le G hGq (-1) hGn, hnull Γ hΓ,
        MMP.Fourfold.Oai4C1.intersectionNumber_isPullback_eq_zero g hgs hDV hG Γ hΓ]
      ring
  rw [sub_eq_zero] at hzero
  exact ⟨hB, hzero ▸ hG⟩

/-- **Nefness descends along a proper birational morphism of surfaces.** If `g : X ⟶ V` is a
proper birational surjection onto a normal surface, `g ≫ h = f` and the pull-back `g^* D_V` is
`f`-nef, then `D_V` is `h`-nef: a curve `C'` contracted by `h` lifts to a curve `C` with
`g(C) = C'`, `g` is an isomorphism at the generic point of `C'` (a point of codimension one), so
`(g^* D_V · C) = (D_V · C')` by the projection formula. -/
private theorem isRelativelyNef_of_isPullback {X V Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V]
    {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} [QuasiCompact sX] [QuasiCompact sV]
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sV] [IsSeparated sV] {g : X ⟶ V}
    (hgs : g ≫ sV = sX) [IsProper g] [Surjective g] (hgb : IsBirationalMorphism g)
    (hdimV : topologicalKrullDim V = 2) {DV : QDivisor V} (hDV : DV.IsQCartier)
    {hB : ∀ C : irreducibleComponents X, g (componentGenericPoint X C) ∉ DV.supp}
    {D : QDivisor X} (hP : DV.IsPullback g hB D) {h : V ⟶ Z}
    (hnef : D.IsRelativelyNef sX (g ≫ h)) : DV.IsRelativelyNef sV h := by
  refine MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg sV hDV
    fun C' hC' => ?_
  obtain ⟨C, hCpt, hCim⟩ := MMP.Mori.ProperCurve.exists_map_eq sX sV g hgs C'
  have hCc : C.IsContractedBy (g ≫ h) := fun x hx => by
    have hgx : g x ∈ closure ({C'.point} : Set V) := hCim ▸ ⟨x, hx, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hC' _ hgx, ← hCpt]
  have h1 := MMP.Fourfold.QDivisor.IsRelativelyNef.intersectionNumber_nonneg sX hnef
    (hP.isQCartier hDV) C hCc
  rw [MMP.Fourfold.Oai4C1.intersectionNumber_isPullback_eq_mul g hgs hDV hP C C'
    hCpt.symm] at h1
  have hpos : (0 : ℚ) < residueFieldDegree g C.point := by
    have hcod : Order.coheight C'.point ≤ 1 := by
      have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sV C'.point
      rw [← MMP.Chow.topologicalKrullDim_curveSubschemeAt_eq, C'.isProperCurve.dim_eq,
        hdimV] at hd
      obtain ⟨c, hc⟩ : ∃ c : ℕ∞, Order.coheight C'.point = c := ⟨_, rfl⟩
      rw [hc] at hd ⊢
      have h4 : (1 + c : ℕ∞) = 2 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact hd)
      by_contra hlt
      push Not at hlt
      have h5 : (1 + 2 : ℕ∞) ≤ 1 + c := add_le_add le_rfl (Order.add_one_le_of_lt hlt)
      rw [h4] at h5
      norm_num at h5
    have hreg := MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hgb hcod
    rw [← hCpt] at hreg
    have := MMP.isIso_stalkMap_of_mem_biregularLocus g hreg
    rw [MMP.Flips.residueFieldDegree_eq_one_of_isIso_stalkMap g C.point this]
    norm_num
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

/-- **Bigness pushes forward along a proper birational morphism over the base.** If
`g : X ⟶ V` is a proper birational morphism of normal projective varieties with `g ≫ h = f`,
`V` is `ℚ`-factorial and `D` is `f`-big, then `g_* D` is `h`-big. -/
private theorem isRelativelyBig_transformDivisor_of_isBirationalMorphism {X V Z : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] {sX : X ⟶ Spec (.of ℂ)} {sV : V ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (hXp : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hV : IsNormalVariety ℂ sV) (hVQ : MMP.Fourfold.IsQFactorial sV)
    (hVp : MMP.Mori.IsProjectiveVariety ℂ sV) (hZp : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {g : X ⟶ V} (hgs : g ≫ sV = sX) [IsProper g] (hg : IsBirationalMorphism g) {f : X ⟶ Z}
    {h : V ⟶ Z} (hgh : g ≫ h = f) (hhs : h ≫ sZ = sV) {D : QDivisor X}
    (hbig : D.IsRelativelyBig f) :
    QDivisor.IsRelativelyBig h (RationalMap.transformDivisor g.toRationalMap D) := by
  refine MMP.Fourfold.isRelativelyBig_transformDivisor_of_isBirational sX sV sZ hX hXp hVQ hVp
    hZp f h hhs g.toRationalMap hg ?_ (fun F hF => ?_) D hbig
  · rw [MMP.Flips.RationalMap.IsOver, ← hgh]
    rfl
  · have : IsSeparated sV := hV.1.toIsSeparated
    have : IsSeparated (V ↘ Limits.terminal Scheme) := by
      rw [show (V ↘ Limits.terminal Scheme) = sV ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
        Limits.terminal.hom_ext _ _]
      infer_instance
    obtain ⟨E, hE, -, hE'⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hV (hgs ▸ hX) hg F
    have := hE' (0 : QDivisor X)
    exact hF E ((MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff g E F).mpr hE)

/-- **Log canonicity as a limit of klt.** Let `(X, B)` be a pair with canonical divisor `K` and
`T` a `ℚ`-Cartier `ℚ`-divisor. If `(X, B - δT)` is klt for all `0 < δ ≤ ε`, then `(X, B)` is lc:
for every exceptional `E` over `X`, `a(E, X, B - δT) = a(E, X, B) + δ coeff_E(f^*T) > -1`, and
letting `δ → 0` gives `a(E, X, B) ≥ -1`. -/
private theorem isLcPair_of_forall_isKltPair_sub_smul {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} {K : Divisor X}
    {B T : QDivisor X} (hP : IsPairWith sX n K B) (hT : T.IsQCartier) {ε : ℚ} (hε : 0 < ε)
    (hklt : ∀ δ : ℚ, 0 < δ → δ ≤ ε → IsKltPair sX n K (B - δ • T)) : IsLcPair sX n K B := by
  refine ⟨hP, le_discrep_iff.mpr fun E a hE ha => ?_⟩
  obtain ⟨-, hB, hiff⟩ := hP.isDiscrepancy_add_smul_iff hT E
  have := E.isLocallyNoetherian
  have := E.isNormal
  have : CompactSpace E.Y := by
    have := E.isNormalVariety.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  obtain ⟨B', hB', -⟩ := hT.existsUnique_isPullback hB
  set c := B'.coeff E.E
  have hlt : ∀ δ : ℚ, 0 < δ → δ ≤ ε → -1 < a + δ * c := fun δ h0 h1 => by
    have hd := ((hiff B' hB').2 (-δ) a).mpr ha
    have e1 : B + (-δ) • T = B - δ • T := by rw [neg_smul, ← sub_eq_add_neg]
    have e2 : a - -δ * c = a + δ * c := by ring
    rw [e1, e2] at hd
    have h2 := lt_of_lt_of_le (hklt δ h0 h1).2.1 (discrep_le hE hd)
    have h3 : ((-1 : ℝ) : EReal) < (((a + δ * c : ℚ) : ℝ) : EReal) := by simpa using h2
    exact_mod_cast EReal.coe_lt_coe_iff.mp h3
  have ha1 : -1 ≤ a := by
    by_contra h
    push Not at h
    set δ := min ε ((-1 - a) / (2 * (|c| + 1)))
    have hδ0 : 0 < δ := lt_min hε (div_pos (by linarith) (by positivity))
    have h1 := hlt δ hδ0 (min_le_left _ _)
    have hc : δ * c ≤ δ * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) hδ0.le
    have hc' : δ * |c| ≤ (-1 - a) / 2 := by
      calc δ * |c| ≤ (-1 - a) / (2 * (|c| + 1)) * |c| :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg c)
        _ ≤ (-1 - a) / 2 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [abs_nonneg c]
    linarith
  have h4 : ((-1 : ℝ) : EReal) ≤ ((a : ℝ) : EReal) :=
    EReal.coe_le_coe_iff.mpr (by exact_mod_cast ha1)
  simpa using h4

/-- The invariants of a model `(Y, B_Y)` of the surface program over `Z`, relative to the fixed
starting model `W` (with `pf : W ⟶ Z` and `D_W` on `W`). -/
private structure IsStage {Z W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W]
    [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (sZ : Z ⟶ Spec (.of ℂ)) (pf : W ⟶ Z) (DW : QDivisor W) (sY : Y ⟶ Spec (.of ℂ))
    [QuasiCompact sY] (KY : Divisor Y) (BY : QDivisor Y) (fY : Y ⟶ Z) (q : W ⟶ Y) : Prop where
  comp_eq : fY ≫ sZ = sY
  isQFactorial : MMP.Fourfold.IsQFactorial sY
  isLcPair : IsLcPair sY 2 KY BY
  nonneg : 0 ≤ BY
  coeff_le_one : ∀ P, BY.coeff P ≤ 1
  isKltPair : ∀ δ : ℚ, 0 < δ → δ ≤ 1 / 2 →
    IsKltPair sY 2 KY (BY - δ • Divisor.toQDivisor BY.roundDown)
  isRelativelyNef : (Divisor.toQDivisor KY + BY).IsRelativelyNef sY fY
  isRelativelyBig : (Divisor.toQDivisor KY + BY).IsRelativelyBig fY
  isBirationalMorphism : IsBirationalMorphism q
  comp_eq_pf : q ≫ fY = pf
  isPullback : ∃ hq, (Divisor.toQDivisor KY + BY).IsPullback q hq DW

/-- The conclusion produced by the program from a stage. -/
private def Conclusion {Z W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    (sZ : Z ⟶ Spec (.of ℂ)) (pf : W ⟶ Z) (DW : QDivisor W) : Prop :=
  ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
    (sX' : X' ⟶ Spec (.of ℂ)) (_ : AlgebraicGeometry.IsProjectiveVariety ℂ sX')
    (_ : QuasiCompact sX') (K' : Divisor X') (B' : QDivisor X') (f' : X' ⟶ Z),
    f' ≫ sZ = sX' ∧ MMP.Fourfold.IsQFactorial sX' ∧ IsLcPair sX' 2 K' B' ∧ 0 ≤ B' ∧
    (∃ q : W ⟶ X', IsBirationalMorphism q ∧ q ≫ f' = pf ∧
      ∃ hq, (Divisor.toQDivisor K' + B').IsPullback q hq DW) ∧
    ∃ ε : ℚ, 0 < ε ∧ ∀ δ : ℚ, 0 < δ → δ ≤ ε →
      IsKltPair sX' 2 K' (B' - δ • Divisor.toQDivisor B'.roundDown) ∧
      (Divisor.toQDivisor K' + (B' - δ • Divisor.toQDivisor B'.roundDown)).IsRelativelyNef
        sX' f' ∧
      (Divisor.toQDivisor K' + (B' - δ • Divisor.toQDivisor B'.roundDown)).IsRelativelyBig f'

/-- A final stage: if `D_Y - η⌊B_Y⌋` is nef over `Z` for some `0 < η ≤ 1/2`, the stage gives the
conclusion with `ε = η / 2`. -/
private theorem conclusion_of_isStage_of_isRelativelyNef {Z W Y : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sZ : Z ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sZ]
    {pf : W ⟶ Z} {DW : QDivisor W} {sY : Y ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sY] [QuasiCompact sY] {KY : Divisor Y}
    {BY : QDivisor Y} {fY : Y ⟶ Z} {q : W ⟶ Y} (hS : IsStage sZ pf DW sY KY BY fY q)
    {η : ℚ} (hη : 0 < η) (hη' : η ≤ 1 / 2)
    (hnef : (Divisor.toQDivisor KY + (BY - η • Divisor.toQDivisor BY.roundDown)).IsRelativelyNef
      sY fY) :
    Conclusion sZ pf DW := by
  have hQ := hS.isQFactorial
  set T := Divisor.toQDivisor BY.roundDown
  have hdim : topologicalKrullDim Y = 2 := hS.isLcPair.1.2.1.topologicalKrullDim_eq
  have hcomb : ∀ δ : ℚ, Divisor.toQDivisor KY + (BY - δ • T) =
      (1 - δ / η) • (Divisor.toQDivisor KY + BY) +
        (δ / η) • (Divisor.toQDivisor KY + (BY - η • T)) := fun δ => by
    refine Finsupp.ext fun P => ?_
    simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
    field_simp
    ring
  refine ⟨Y, ‹_›, ‹_›, ‹_›, sY, ‹_›, ‹_›, KY, BY, fY, hS.comp_eq, hQ, hS.isLcPair, hS.nonneg,
    ⟨q, hS.isBirationalMorphism, hS.comp_eq_pf, hS.isPullback⟩, η / 2, by positivity,
    fun δ hδ hδε => ⟨hS.isKltPair δ hδ (by linarith), ?_, ?_⟩⟩
  · have h := isRelativelyNef_smul_add_smul_of_isQFactorial hQ hS.isRelativelyNef hnef
      (a := 1 - δ / η) (b := δ / η) (by rw [sub_nonneg, div_le_one hη]; linarith)
      (by positivity)
    convert h using 1
    exact hcomb δ
  · have h := QDivisor.IsRelativelyBig.smul_add_smul_of_isRelativelyNef sY sZ hQ hdim fY
      hS.comp_eq hS.isRelativelyNef hS.isRelativelyBig hnef
      (a := 1 - δ / η) (b := δ / η) (by rw [sub_pos, div_lt_one hη]; linarith) (by positivity)
    convert h using 1
    exact hcomb δ

/-- One step of the program: a stage which is not final for `η = 1/(2(1 + 4r))`, `r` a Cartier
index of `D_Y`, has a divisorial contraction to a stage of smaller Picard number. -/
private theorem exists_isStage_of_not_isRelativelyNef {Z W Y : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] {sZ : Z ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sZ]
    {pf : W ⟶ Z} {DW : QDivisor W} {sY : Y ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sY] [QuasiCompact sY] {KY : Divisor Y}
    {BY : QDivisor Y} {fY : Y ⟶ Z} {q : W ⟶ Y} (hS : IsStage sZ pf DW sY KY BY fY q)
    {r : ℕ} (hr : 0 < r) {E : Divisor Y}
    (hE : Divisor.toQDivisor E = (r : ℤ) • (Divisor.toQDivisor KY + BY)) (hEc : E.IsCartier)
    (hnef : ¬ (Divisor.toQDivisor KY +
      (BY - (1 / (2 * (1 + 4 * r)) : ℚ) • Divisor.toQDivisor BY.roundDown)).IsRelativelyNef sY fY) :
    ∃ (V : Scheme.{0}) (_ : IsIntegral V) (_ : IsLocallyNoetherian V) (_ : IsNormal V)
      (sV : V ⟶ Spec (.of ℂ)) (_ : AlgebraicGeometry.IsProjectiveVariety ℂ sV)
      (_ : QuasiCompact sV) (KV : Divisor V) (BV : QDivisor V) (fV : V ⟶ Z) (qV : W ⟶ V),
      IsStage sZ pf DW sV KV BV fV qV ∧ picardNumber sV + 1 = picardNumber sY := by
  have hQ := hS.isQFactorial
  have hq := MMP.Fourfold.isQCartier_of_isQFactorial sY hQ
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  have hK : KY.IsCanonicalDivisor sY 2 := hS.isLcPair.1.2.1
  set T : QDivisor Y := Divisor.toQDivisor BY.roundDown with hT
  set η : ℚ := 1 / (2 * (1 + 4 * r)) with hηdef
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hη0 : 0 < η := by positivity
  have hη2 : η ≤ 1 / 2 := by
    rw [hηdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hBδ : ∀ δ : ℚ, 0 ≤ δ → δ ≤ 1 → 0 ≤ BY - δ • T := fun δ h0 h1 =>
    nonneg_sub_smul_roundDown hS.nonneg hS.coeff_le_one h0 h1
  have hkltη := hS.isKltPair η hη0 hη2
  have hklt4 : MMP.Fourfold.IsKltPair sY (BY - η • T) :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sY hK
      ⟨inferInstance, inferInstance, hkltη.isPair, fun P => hBδ η hη0.le (by linarith) P⟩).2
      hkltη
  obtain ⟨R, ⟨hRq, hRext, hRneg⟩, ⟨C₀, hC₀f, hRC₀⟩, V, sV, g, hg, hVp, -, -, -, ⟨h, hgh, hhs⟩,
    -⟩ := MMP.Fourfold.exists_isContractionOfRay_comp_eq_of_not_isRelativelyNef sY
      (inferInstance : MMP.Mori.IsProjectiveVariety ℂ sY) hklt4 hK
      (inferInstance : MMP.Mori.IsProjectiveVariety ℂ sZ) hS.comp_eq hnef
  -- `D_Y` is trivial on `R`, and `R` is negative for every `D_Y - δ⌊B_Y⌋`, `δ > 0`
  obtain ⟨hDR, hTR⟩ := curveForm_eq_zero_and_neg_of_ray hQ
    (hS.isKltPair (1 / 2) (by norm_num) le_rfl) (hBδ (1 / 2) (by norm_num) (by norm_num))
    hS.isRelativelyNef hr hE hEc hRext hC₀f hRC₀ hRneg
  have hneg : ∀ δ : ℚ, 0 < δ → MMP.Fourfold.IsNegativeExtremalRayOf sY
      (Divisor.toQDivisor KY + (BY - δ • T)) R := fun δ hδ =>
    ⟨hq _, hRext, hTR δ hδ⟩
  have hnull : ∀ Γ : ProperCurve sY, Γ.IsContractedBy g →
      (Divisor.toQDivisor KY + BY).intersectionNumber ℂ sY Γ.ι Γ.dim_le (hq _) = 0 :=
    fun Γ hΓ => by
      have h1 := hDR _ ((hg.isContractedBy_iff Γ).mp hΓ)
      rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle] at h1
      exact_mod_cast h1
  -- the contraction is divisorial
  have hYp : MMP.Mori.IsProjectiveVariety ℂ sY := inferInstance
  have hface : IsContractionOfFace ℂ sY sV R g :=
    ⟨hYp, hVp, hg.comp_eq, hRext.1, hg.isContractedBy_iff, hg.isIso_app⟩
  have hdiv : IsDivisorialContraction ℂ sY sV R g :=
    isDivisorialContraction_of_isRelativelyBig hQ hK hRext hface hgh hS.comp_eq
      hS.isRelativelyBig hnull
      ((hg.isContractedBy_iff C₀).mpr (hRC₀ ▸ ⟨1, zero_le_one, one_smul ℝ _⟩))
  -- the target `V`
  have hVn := hg.isNormalVariety_target
  have : IsIntegral V := hVn.1.toIsIntegral
  have : IsNormal V := hVn.2
  have : LocallyOfFiniteType sV := hVn.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian sV
  have : QuasiCompact sV := hVn.1.toQuasiCompact
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace sV
  have : AlgebraicGeometry.IsProjectiveVariety ℂ sV := hVp
  have : IsProper g := isProper_of_isProjectiveMorphism g hg.isProjectiveMorphism
  have hgb : IsBirationalMorphism g := hdiv.isBirationalMorphism
  have hYn : IsNormalVariety ℂ (g ≫ sV) := hg.comp_eq ▸ hg.isNormalVariety_source
  have hVQ : MMP.Fourfold.IsQFactorial sV :=
    isQFactorial_of_isDivisorialContraction hQ hkltη
      (DivisorWithCoeffs.isEffective_iff_nonneg.mpr (hBδ η hη0.le (by linarith)))
      (hneg η hη0).2.2 hdiv
  have hqV := MMP.Fourfold.isQCartier_of_isQFactorial sV hVQ
  -- the transforms `K_V = g_* K_Y`, `B_V = g_* B_Y`
  set KV : Divisor V := RationalMap.transformDivisor g.toRationalMap KY with hKV
  set BV : QDivisor V := RationalMap.transformDivisor g.toRationalMap BY with hBV
  have hTV : RationalMap.transformDivisor g.toRationalMap T = Divisor.toQDivisor BV.roundDown :=
    transformDivisor_toQDivisor_roundDown hVn hYn hgb BY
  have htrδ : ∀ δ : ℚ, RationalMap.transformDivisor g.toRationalMap (BY - δ • T) =
      BV - δ • Divisor.toQDivisor BV.roundDown := fun δ => by
    rw [map_sub, ← RationalMap.transformDivisorₗ_apply ℚ g.toRationalMap (δ • T), map_smul,
      RationalMap.transformDivisorₗ_apply, hTV]
  have hkltV : ∀ δ : ℚ, 0 < δ → δ ≤ 1 / 2 →
      IsKltPair sV 2 KV (BV - δ • Divisor.toQDivisor BV.roundDown) := fun δ h0 h1 => by
    have := IsDivisorialContraction.isKltPair_transformDivisor hQ (hneg δ h0) hdiv
      (Or.inl (hBδ δ h0.le (by linarith))) (hS.isKltPair δ h0 h1)
    rwa [htrδ] at this
  have hKVc : KV.IsCanonicalDivisor sV 2 := (hkltV (1 / 2) (by norm_num) le_rfl).1.2.1
  -- crepancy: `D_Y = g^* D_V`
  have hDV : RationalMap.transformDivisor g.toRationalMap (Divisor.toQDivisor KY + BY) =
      Divisor.toQDivisor KV + BV := by
    rw [map_add, MMP.Flips.transformDivisor_toQDivisor]
  have hpullg : ∃ hB, (Divisor.toQDivisor KV + BV).IsPullback g hB
      (Divisor.toQDivisor KY + BY) := by
    have h := isPullback_transformDivisor_of_null hg.isNormalVariety_source hVn hVQ
      hg.comp_eq hgb (hq _) hnull
    rw [hDV] at h
    exact h
  obtain ⟨hBg, hPg⟩ := hpullg
  -- the stage invariants on `V`
  have : Surjective g := ⟨hg.surjective⟩
  have : IsSeparated sV := hVn.1.toIsSeparated
  have hnefV : (Divisor.toQDivisor KV + BV).IsRelativelyNef sV h :=
    isRelativelyNef_of_isPullback hg.comp_eq hgb hKVc.topologicalKrullDim_eq (hqV _) hPg
      (hgh ▸ hS.isRelativelyNef)
  have hbigV : (Divisor.toQDivisor KV + BV).IsRelativelyBig h := by
    rw [← hDV]
    exact isRelativelyBig_transformDivisor_of_isBirationalMorphism hg.isNormalVariety_source hYp
      hVn hVQ hVp inferInstance hg.comp_eq hgb hgh hhs hS.isRelativelyBig
  have hlcV : IsLcPair sV 2 KV BV :=
    isLcPair_of_forall_isKltPair_sub_smul ⟨hVn, hKVc, hqV _⟩ (hqV _)
      (by norm_num : (0 : ℚ) < 1 / 2) hkltV
  have hBV0 : 0 ≤ BV := RationalMap.transformDivisor_nonneg _ hS.nonneg
  have hBV1 : ∀ P, BV.coeff P ≤ 1 := transformDivisor_coeff_le hVn hYn hgb hS.coeff_le_one
  -- the composite `W ⟶ V`
  have hqVb : IsBirationalMorphism (q ≫ g) :=
    MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_comp hS.isBirationalMorphism hgb
  have : IsDominant (q ≫ g) := hqVb.isDominant
  obtain ⟨hBq, hPq⟩ := hS.isPullback
  have hpullV : ∃ hB, (Divisor.toQDivisor KV + BV).IsPullback (q ≫ g) hB DW :=
    MMP.Fourfold.Oai4C1.TwoEnds.qDivisor_isPullback_comp g q hPg hPq
  have hρ : picardNumber sV + 1 = picardNumber sY :=
    picardNumber_add_one_eq_of_isContractionOfFace hkltη
      (DivisorWithCoeffs.isEffective_iff_nonneg.mpr (hBδ η hη0.le (by linarith))) hRext
      (hneg η hη0).2.2 hface
  exact ⟨V, ‹_›, ‹_›, ‹_›, sV, ‹_›, ‹_›, KV, BV, h, q ≫ g,
    ⟨hhs, hVQ, hlcV, hBV0, hBV1, hkltV, hnefV, hbigV, hqVb,
      by rw [Category.assoc, hgh, hS.comp_eq_pf], hpullV⟩, hρ⟩

/-- **The program terminates.** By induction on the Picard number, every stage leads to the
conclusion. -/
private theorem conclusion_of_isStage {Z W : Scheme.{0}}
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {sZ : Z ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sZ] {pf : W ⟶ Z} {DW : QDivisor W} (n : ℕ) :
    ∀ {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
      {sY : Y ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sY] [QuasiCompact sY]
      {KY : Divisor Y} {BY : QDivisor Y} {fY : Y ⟶ Z} {q : W ⟶ Y},
      IsStage sZ pf DW sY KY BY fY q → picardNumber sY = n → Conclusion sZ pf DW := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y _ _ _ sY _ _ KY BY fY q hS hn
  obtain ⟨hpair, -⟩ := hS.isLcPair
  obtain ⟨r, hr, E, hE, hEc⟩ := hpair.2.2.exists_pos
  by_cases hnef : (Divisor.toQDivisor KY +
      (BY - (1 / (2 * (1 + 4 * r)) : ℚ) • Divisor.toQDivisor BY.roundDown)).IsRelativelyNef sY fY
  · have hr' : (0 : ℚ) < r := by exact_mod_cast hr
    refine conclusion_of_isStage_of_isRelativelyNef hS (by positivity) ?_ hnef
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  · obtain ⟨V, _, _, _, sV, _, _, KV, BV, fV, qV, hSV, hρ⟩ :=
      exists_isStage_of_not_isRelativelyNef hS hr hE hEc hnef
    rw [hn] at hρ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, picardNumber sV = m := by
      have := picardNumber_lt_top_of_isProjectiveVariety sV
      exact ⟨(picardNumber sV).toNat, (ENat.coe_toNat this.ne).symm⟩
    rw [hm] at hρ
    have hmn : m + 1 = n := by exact_mod_cast hρ
    exact ih m (by omega) hSV hm

/-- **A Kollár–Mori lc pair is log canonical in the shared sense.** For an lc pair `(X, B)` of
dimension `n ≥ 2` with `B ≥ 0`, every log discrepancy is `1 + a(E, X, B) ≥ 0`: for exceptional
`E` because `discrep(X, B) ≥ -1`, and for a prime divisor `P` of `X` because
`a(P, X, B) = -coeff_P B ≥ totaldiscrep(X, B) ≥ -1` (Kollár–Mori 2.31(1)). -/
private theorem isLogCanonicalPair_of_isLcPair {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} {n : ℕ} (hn : 2 ≤ n)
    {K : Divisor X} {B : QDivisor X} (hlc : IsLcPair sX n K B) (hB : 0 ≤ B) :
    MMP.Intersection.IsLogCanonicalPair sX B := by
  have hP := hlc.1
  have hK := hP.2.1
  refine ⟨hlc.isPair, fun P => Finsupp.le_def.mp hB P, fun n' D b hb => ?_⟩
  obtain ⟨-, -, -, -, ⟨K', hK', -⟩, -⟩ := id hb
  have hnn : n' = n := by
    have h := hK'.topologicalKrullDim_eq.symm.trans hK.topologicalKrullDim_eq
    exact_mod_cast h
  subst hnn
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hlc.isPair hK D
  rw [MMP.Threefold.Bridges.eq_one_add_of_isDiscrepancy_of_isLogDiscrepancy ha hb]
  have ha1 : (-1 : ℚ) ≤ a := by
    by_cases hE : D.IsExceptional
    · have h1 := hlc.2.trans (discrep_le hE ha)
      have h2 : ((-1 : ℝ) : EReal) ≤ ((a : ℝ) : EReal) := by simpa using h1
      exact_mod_cast EReal.coe_le_coe_iff.mp h2
    · obtain ⟨Pd, -, hPd⟩ := DivisorOver.exists_center_eq_isDiscrepancy_neg_coeff hP D hE
      rw [ha.eq hPd]
      have htot : ¬ totalDiscrep sX n' K B < -1 := fun h => by
        have h1 := hlc.2
        rw [discrep_eq_bot_of_totalDiscrep_lt_neg_one hP hn h] at h1
        exact absurd h1 (by simp; exact EReal.coe_ne_top 1)
      push Not at htot
      have hle := totalDiscrep_le_neg_coeff hP.1
        (MMP.Positivity.IsPair.exists_isDiscrepancy hlc.isPair hK _) (P := Pd)
      have h4 : ((-1 : ℝ) : EReal) ≤ (((-B.coeff Pd : ℚ) : ℝ) : EReal) := by
        simpa using htot.trans hle
      exact_mod_cast EReal.coe_le_coe_iff.mp h4
  have : (-1 : ℝ) ≤ a := by exact_mod_cast ha1
  linarith

/-- The order condition `P.OrdGE n` on the factor `𝒪_{X,η}` of the rational functions is the
inequality `n ≤ ord_P g` on the function field. -/
private theorem ordGE_symm_toFunctionField_iff {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (P : MMP.Mori.PrimeDivisor X) (n : ℤ)
    {g : X.functionField} (hg : g ≠ 0) :
    P.OrdGE n ((MMP.Fourfold.toFunctionField X P.component).symm g) ↔
      n ≤ X.ord g P.genericPoint := by
  have hv := MMP.Fourfold.valuation_symm_toFunctionField P g
  rw [P.divisorialValuation_eq_exp_neg_ord hg, ← WithZero.exp_neg, neg_neg] at hv
  constructor
  · rintro (h0 | h)
    · exact absurd ((MMP.Fourfold.toFunctionField X P.component).symm.injective
        (h0.trans (map_zero _).symm)) hg
    · rwa [hv, WithZero.exp_le_exp] at h
  · exact fun h => Or.inr (by rwa [hv, WithZero.exp_le_exp])

/-- **Bigness pulls back along a proper birational morphism.** If `p : W ⟶ X` is a proper
birational morphism onto a normal variety, `f : X ⟶ Z` a morphism to a projective variety, `D` an
`f`-big `ℚ`-Cartier `ℚ`-divisor and `D_W = p^*D`, then `D_W` is `(p ≫ f)`-big: a rational function
`g` with `div g + mD ≥ 0` over an open of `Z` pulls back to one with `div (p^*g) + p^*(mD) ≥ 0`
(near a point `x`, `g e` is regular for a local equation `e` of `mD`, by normality), so the
relative generic ranks of `𝒪(mD)` do not drop. -/
private theorem isRelativelyBig_of_isPullback {X W Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) (hWp : MMP.Mori.IsProjectiveVariety ℂ sW)
    (hZp : MMP.Mori.IsProjectiveVariety ℂ sZ) {p : W ⟶ X} (hps : p ≫ sX = sW) [IsProper p]
    (hp : IsBirationalMorphism p) {f : X ⟶ Z} (hf : f ≫ sZ = sX) {D : QDivisor X}
    {hB : ∀ C : irreducibleComponents W, p (componentGenericPoint W C) ∉ D.supp}
    {DW : QDivisor W} (hP : D.IsPullback p hB DW) (hbig : D.IsRelativelyBig f) :
    DW.IsRelativelyBig (p ≫ f) := by
  have : IsDominant p := hp.isDominant
  have hXv : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  have hWv : AlgebraicGeometry.IsVariety ℂ sW := hWp.toIsVariety
  have hrange : Set.range p = Set.univ := by
    rw [← p.isClosedMap.isClosed_range.closure_eq, p.denseRange.closure_range]
  obtain ⟨m₀, hm₀, E, hE, hEc, a, b, ha, hb, c, hc, k₀, hk⟩ := hbig
  have hm₀' : ((m₀ : ℤ) : ℚ) = (m₀ : ℚ) := by norm_cast
  obtain ⟨E', hE'q, hpE⟩ := hP m₀ hm₀ E
    (by rw [hE, ← Int.cast_smul_eq_zsmul ℚ, hm₀']) hEc
  have hE'c : E'.IsCartier := hpE.isCartier hEc
  refine ⟨m₀, hm₀, E', by rw [hE'q, ← Int.cast_smul_eq_zsmul ℚ, hm₀'], hE'c, a, b, ?_, ?_, c,
    hc, k₀, fun m hm => (hk m hm).trans_le ?_⟩
  · rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sW hp]
    exact ha
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange, Set.image_univ]
    exact hb
  -- the comparison of relative generic ranks
  have hmE := hEc.zsmul m
  have hmE' := hE'c.zsmul m
  have hBm : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ (m • E).supp :=
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' p _
  have hpm := hpE.zsmul hEc m hBm
  have hη : f (genericPoint X) = (p ≫ f) (genericPoint W) := by
    rw [Scheme.Hom.comp_apply, map_genericPoint_of_isDominant p]
  refine Nat.cast_le.mpr (MMP.Fourfold.relativeGenericRank_le_of_functionFieldTransfer sW sZ hWp
    hZp f (p ≫ f) (by rw [Category.assoc, hf, hps]) hη (m • E) (m • E') hmE'
    (functionFieldMap p) (fun V r hXV hWV => ?_) (fun V g hg Q hQ => ?_))
  · -- germs of functions from the base
    have hWV' : genericPoint W ∈ p ⁻¹ᵁ (f ⁻¹ᵁ V) := hWV
    have e1 : functionFieldMap p (X.presheaf.germ (f ⁻¹ᵁ V) _ hXV (f.app V r)) =
        W.presheaf.germ (p ⁻¹ᵁ (f ⁻¹ᵁ V)) _ hWV' (p.app (f ⁻¹ᵁ V) (f.app V r)) := by
      change (p.stalkMap (genericPoint W)).hom ((X.presheaf.stalkCongr _).hom.hom
        (X.presheaf.germ (f ⁻¹ᵁ V) _ hXV (f.app V r))) = _
      rw [TopCat.Presheaf.stalkCongr_hom]
      erw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact Scheme.Hom.germ_stalkMap_apply p (f ⁻¹ᵁ V) _ hWV' _
    rw [e1, Scheme.Hom.comp_app]
    rfl
  · -- sections of `𝒪_X(mE)` pull back to sections of `𝒪_W(mE')`
    by_cases hg0 : g = 0
    · left
      rw [hg0, map_zero, map_zero]
    have htg : functionFieldMap p g ≠ 0 := (map_ne_zero _).mpr hg0
    rw [ordGE_symm_toFunctionField_iff Q _ htg]
    have hQV : (p ≫ f) Q.genericPoint ∈ V := (Q.genericPoint_mem_iff ((p ≫ f) ⁻¹ᵁ V)).mpr hQ
    set x := p Q.genericPoint with hx
    have hxV : f x ∈ V := hQV
    obtain ⟨U, hxU, φ, hφ⟩ := hmE x
    set Z₀ : irreducibleComponents X := MMP.Mori.pointComponent x
    have hsub : Subsingleton (irreducibleComponents X) :=
      MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents
    set φ₀ := MMP.Threefold.Mori.Helpers.evalFF Z₀ (φ : RationalFunctions X) with hφ₀
    have hφ₀0 : φ₀ ≠ 0 := (φ.isUnit.map (MMP.Threefold.Mori.Helpers.evalFF Z₀)).ne_zero
    have hcoeffX : ∀ Γ : MMP.Mori.PrimeDivisor X, x ∈ Γ.support →
        (m • E).coeff Γ = X.ord φ₀ Γ.genericPoint := fun Γ hΓ => by
      rw [hφ Γ ⟨x, hΓ, hxU⟩, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord,
        Subsingleton.elim Γ.component Z₀]
    -- Hartogs: `g φ₀` is regular at `x`
    obtain ⟨r, hr⟩ := MMP.Threefold.Bridges.exists_algebraMap_stalk_eq_of_forall_zero_le_ord x
      (mul_ne_zero hg0 hφ₀0) fun Γ hΓ => by
        rw [Scheme.ord_mul hg0 hφ₀0, ← hcoeffX Γ hΓ]
        have := (ordGE_symm_toFunctionField_iff Γ _ hg0).mp (hg Γ ⟨x, hΓ, hxV⟩)
        linarith
    -- the coefficient of the pull-back
    have hcoeffW : (m • E').coeff Q = W.ord (functionFieldMap p φ₀) Q.genericPoint :=
      MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hpm hφ Q hxU Z₀
    have hreg : 0 ≤ W.ord (functionFieldMap p (g * φ₀)) Q.genericPoint := by
      have hne : functionFieldMap p (g * φ₀) ≠ 0 :=
        (map_ne_zero _).mpr (mul_ne_zero hg0 hφ₀0)
      have hle : Q.divisorialValuation (functionFieldMap p (g * φ₀)) ≤ 1 := by
        rw [← hr, MMP.Mori.functionFieldMap_algebraMap_stalk p Q.genericPoint r]
        exact (Q.divisorialValuation_le_one_iff _).mpr ⟨_, rfl⟩
      rw [Q.divisorialValuation_eq_exp_neg_ord hne, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at hle
      linarith
    rw [map_mul, Scheme.ord_mul htg ((map_ne_zero _).mpr hφ₀0)] at hreg
    rw [hcoeffW]
    linarith

/-- **The starting stage**: a crepant dlt modification `(W, Δ) ⟶ (X, B)`, `K_W + Δ = p^*(K + B)`,
is a stage of the program over `Z`. -/
private theorem exists_isStage_dltModification {X Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sX] {sZ : Z ⟶ Spec (.of ℂ)}
    [AlgebraicGeometry.IsProjectiveVariety ℂ sZ] {f : X ⟶ Z} (hf : f ≫ sZ = sX) {K : Divisor X}
    {B : QDivisor X} (hlc : IsLcPair sX 2 K B) (hB : 0 ≤ B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hbig : (Divisor.toQDivisor K + B).IsRelativelyBig f) :
    ∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
      (p : W ⟶ X) (sW : W ⟶ Spec (.of ℂ)) (_ : AlgebraicGeometry.IsProjectiveVariety ℂ sW)
      (_ : QuasiCompact sW) (KW : Divisor W) (BW : QDivisor W),
      p ≫ sX = sW ∧ IsBirationalMorphism p ∧
      (∃ hp, (Divisor.toQDivisor K + B).IsPullback p hp (Divisor.toQDivisor KW + BW)) ∧
      IsStage sZ (p ≫ f) (Divisor.toQDivisor KW + BW) sW KW BW (p ≫ f) (𝟙 W) := by
  have hK : K.IsCanonicalDivisor sX 2 := hlc.1.2.1
  have hX : IsNormalVariety ℂ sX := hlc.1.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hKBq : (Divisor.toQDivisor K + B).IsQCartier := hlc.1.2.2
  obtain ⟨W, _, _, _, p, hp, hWQ, Δ, hpp, hWp, hdlt, hcrep, -⟩ :=
    MMP.Threefold.exists_crepant_dltModification_of_surface sX inferInstance
      hK.topologicalKrullDim_eq (isLogCanonicalPair_of_isLcPair le_rfl hlc hB)
  have hWn : IsNormalVariety ℂ (p ≫ sX) := hWQ.1
  have : AlgebraicGeometry.IsProjectiveVariety ℂ (p ≫ sX) := hWp
  have : LocallyOfFiniteType (p ≫ sX) := hWn.1.toLocallyOfFiniteType
  have : QuasiCompact (p ≫ sX) := hWn.1.toQuasiCompact
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have : IsProper p := isProper_of_isProjectiveMorphism p hpp
  have : IsDominant p := hp.isDominant
  have hqW := MMP.Fourfold.isQCartier_of_isQFactorial (p ≫ sX) hWQ
  -- canonical divisors `K = div ω`, `K_W = div (p^*ω)`
  have hdimW : topologicalKrullDim W = (2 : ℕ) := by
    rw [← MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hp]
    exact hK.topologicalKrullDim_eq
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor (p ≫ sX) hWn hdimW
  obtain ⟨KW, hKW, hpush⟩ :=
    MMP.Fourfold.Oai4C1.Main.exists_isCanonicalDivisor_transformDivisor_eq hX hWn hp hK hK₀
  obtain ⟨ω, hω0, hωK, hωKW⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hX hWn hp hK hKW hpush
  -- crepancy: `p^*(K + B) = K_W + Δ`
  have hBp := MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier p hKBq
  have hPpb := QDivisor.isPullback_pullback hKBq hBp
  have hPeq : QDivisor.pullback (f := p) (Divisor.toQDivisor K + B) hKBq hBp =
      Divisor.toQDivisor KW + Δ := by
    subst hωK hωKW
    ext E
    have h1 := MMP.Mori.isDiscrepancy_coeff_divisorOfForm_sub_pullback hX ω hω0 hK B hKBq p hWn
      hp E
    have h2 := h1.eq (hcrep (divisorOfForm ω) hK E)
    rw [DivisorWithCoeffs.coeff_sub] at h2
    change _ = (Divisor.toQDivisor _ + Δ).coeff E
    rw [DivisorWithCoeffs.coeff_add]
    linarith
  have hpull : (Divisor.toQDivisor K + B).IsPullback p hBp (Divisor.toQDivisor KW + Δ) :=
    hPeq ▸ hPpb
  -- the boundary
  have hΔ0 : 0 ≤ Δ := Finsupp.le_def.mpr hdlt.1.2.1
  have hΔ1 : ∀ P, Δ.coeff P ≤ 1 := hdlt.2.1
  have hkltW : ∀ δ : ℚ, 0 < δ → δ ≤ 1 / 2 →
      IsKltPair (p ≫ sX) 2 KW (Δ - δ • Divisor.toQDivisor Δ.roundDown) := fun δ h0 h1 => by
    have hT0 : 0 ≤ Divisor.toQDivisor Δ.roundDown := Finsupp.le_def.mpr fun P => by
      change (0 : ℚ) ≤ ((⌊Δ P⌋ : ℤ) : ℚ)
      exact_mod_cast Int.floor_nonneg.mpr (Finsupp.le_def.mp hΔ0 P)
    have hnn := nonneg_sub_smul_roundDown hΔ0 hΔ1 h0.le (by linarith)
    have hle : Δ - δ • Divisor.toQDivisor Δ.roundDown ≤ Δ :=
      sub_le_self _ (smul_nonneg h0.le hT0)
    have hdlt' := MMP.Intersection.IsDltPair.of_le (p ≫ sX) hdlt hnn hle (hqW _)
    have hlt : ∀ P, (Δ - δ • Divisor.toQDivisor Δ.roundDown).coeff P < 1 := fun P => by
      have hfl : (Divisor.toQDivisor Δ.roundDown) P = (⌊Δ P⌋ : ℚ) := rfl
      change Δ P - δ * (Divisor.toQDivisor Δ.roundDown) P < 1
      rw [hfl]
      rcases eq_or_lt_of_le (hΔ1 P) with h | h
      · change Δ P = 1 at h
        rw [h, Int.floor_one, Int.cast_one]
        linarith
      · rw [Int.floor_eq_zero_iff.mpr ⟨Finsupp.le_def.mp hΔ0 P, h⟩, Int.cast_zero, mul_zero,
          sub_zero]
        exact h
    have hk4 := MMP.Intersection.IsDltPair.isKltPair_of_forall_coeff_lt_one hdlt' hlt
    exact (MMP.Fourfold.isKltPair_iff_mori_isKltPair (p ≫ sX) hKW hk4.1).1 hk4
  refine ⟨W, ‹_›, ‹_›, ‹_›, p, p ≫ sX, ‹_›, ‹_›, KW, Δ, rfl, hp, ⟨hBp, hpull⟩, ?_⟩
  exact
    { comp_eq := by rw [Category.assoc, hf]
      isQFactorial := hWQ
      isLcPair := isLcPair_of_forall_isKltPair_sub_smul ⟨hWn, hKW, hqW _⟩ (hqW _)
        (by norm_num : (0 : ℚ) < 1 / 2) hkltW
      nonneg := hΔ0
      coeff_le_one := hΔ1
      isKltPair := hkltW
      isRelativelyNef := MMP.Fourfold.QDivisor.isRelativelyNef_of_intersectionNumber_nonneg
        (p ≫ sX) (hqW _) fun Γ hΓ =>
          MMP.Fourfold.Oai4C1.intersectionNumber_isPullback_nonneg p rfl f hKBq hnef hpull Γ hΓ
      isRelativelyBig := isRelativelyBig_of_isPullback hX hWp inferInstance rfl hp hf hpull hbig
      isBirationalMorphism := isBirationalMorphism_of_isIso (𝟙 W)
      comp_eq_pf := Category.id_comp _
      isPullback := ⟨_, MMP.Mori.qDivisor_isPullback_id _
        (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier (𝟙 W) (hqW _))⟩ }

end MMP.FourfoldProofs.MmpSurfaceProjectiveLcNefBigEpsilonModelProof

end

section

/-!
# A klt `ε`-model of a nef and big lc adjoint on a projective surface

Let `(X, B)` be an lc pair on a normal projective complex surface, with `B ≥ 0` a `ℚ`-divisor,
and let `f : X ⟶ Z` be a morphism of projective complex varieties such that `K_X + B` is `f`-nef
and `f`-big. Then there are a projective `ℚ`-factorial lc surface pair `(X', B')` with `B' ≥ 0`,
a morphism `f' : X' ⟶ Z`, a normal projective variety `W` with birational morphisms
`p : W ⟶ X`, `q : W ⟶ X'` over `Z` such that `p^*(K_X + B) = q^*(K_{X'} + B')`, and a rational
`ε > 0` such that, with `T' = ⌊B'⌋`, for every rational `0 < δ ≤ ε` the pair `(X', B' - δT')`
is klt and `K_{X'} + B' - δT'` is `f'`-nef and `f'`-big.

The model is obtained from a crepant dlt modification of `(X, B)` by running the surface program
for the perturbed adjoint over `Z`; the length of extremal rays and the integrality of the
Cartier index force every step to be crepant for `K + B`.

## Main results

* `MMP.Mori.IsLcPair.exists_isKltPair_sub_smul_roundDown_of_isRelativelyNef_of_isRelativelyBig`:
  the existence of the model.

## Implementation notes

Pairs are `MMP.Mori.IsLcPair` and `MMP.Mori.IsKltPair` with canonical divisors of dimension `2`,
which also records that the varieties are surfaces; the canonical divisor `K'` of `X'` is part of
the data produced. The equality of the two pull-backs of the adjoints on `W` is the existence of
one `ℚ`-divisor on `W` that is the pull-back (`MMP.Mori.QDivisor.IsPullback`) of both
`K_X + B` along `p` and `K_{X'} + B'` along `q`. The boundaries are effective, as in the source's
convention for pairs. `f'`-nefness and `f'`-bigness are `MMP.Mori.QDivisor.IsRelativelyNef` and
`MMP.Mori.QDivisor.IsRelativelyBig`, and `ℚ`-factoriality is `MMP.Fourfold.IsQFactorial`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- **A klt `ε`-model of a nef and big lc adjoint on a projective surface.** Let `(X, B)` be an
lc pair on a normal projective complex surface, `B ≥ 0` a `ℚ`-divisor and `K` a canonical
divisor, and let `f : X ⟶ Z` be a morphism to a projective complex variety with `K + B` `f`-nef
and `f`-big. Then there are a projective `ℚ`-factorial lc surface pair `(X', B')`, `B' ≥ 0`, with
canonical divisor `K'`, a morphism `f' : X' ⟶ Z`, a normal projective variety `W` with birational
morphisms `p : W ⟶ X` and `q : W ⟶ X'` satisfying `p ≫ f = q ≫ f'` and
`p^*(K + B) = q^*(K' + B')`, and a rational `ε > 0` such that for every rational `0 < δ ≤ ε`,
with `T' = ⌊B'⌋`, the pair `(X', B' - δT')` is klt and `K' + B' - δT'` is `f'`-nef and
`f'`-big. -/
@[mmp "thm_mmp_surface_projective_lc_nef_big_epsilon_model"]
public theorem IsLcPair.exists_isKltPair_sub_smul_roundDown_of_isRelativelyNef_of_isRelativelyBig
    {X Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sX]
    {sZ : Z ⟶ Spec (.of ℂ)} [AlgebraicGeometry.IsProjectiveVariety ℂ sZ]
    {f : X ⟶ Z} (hf : f ≫ sZ = sX) {K : Divisor X} {B : QDivisor X}
    (hlc : IsLcPair sX 2 K B) (hB : 0 ≤ B)
    (hnef : (Divisor.toQDivisor K + B).IsRelativelyNef sX f)
    (hbig : (Divisor.toQDivisor K + B).IsRelativelyBig f) :
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : IsLocallyNoetherian X') (_ : IsNormal X')
      (sX' : X' ⟶ Spec (.of ℂ)) (_ : AlgebraicGeometry.IsProjectiveVariety ℂ sX')
      (_ : QuasiCompact sX') (K' : Divisor X') (B' : QDivisor X') (f' : X' ⟶ Z),
      f' ≫ sZ = sX' ∧ MMP.Fourfold.IsQFactorial sX' ∧ IsLcPair sX' 2 K' B' ∧ 0 ≤ B' ∧
      (∃ (W : Scheme.{0}) (_ : IsIntegral W) (_ : IsLocallyNoetherian W) (_ : IsNormal W)
        (p : W ⟶ X) (q : W ⟶ X'),
        AlgebraicGeometry.IsProjectiveVariety ℂ (p ≫ sX) ∧ IsBirationalMorphism p ∧
        IsBirationalMorphism q ∧ p ≫ f = q ≫ f' ∧
        ∃ (hp : ∀ C : irreducibleComponents W,
              p (componentGenericPoint W C) ∉ (Divisor.toQDivisor K + B).supp)
          (hq : ∀ C : irreducibleComponents W,
              q (componentGenericPoint W C) ∉ (Divisor.toQDivisor K' + B').supp)
          (D : QDivisor W),
          (Divisor.toQDivisor K + B).IsPullback p hp D ∧
            (Divisor.toQDivisor K' + B').IsPullback q hq D) ∧
      ∃ ε : ℚ, 0 < ε ∧ ∀ δ : ℚ, 0 < δ → δ ≤ ε →
        IsKltPair sX' 2 K' (B' - δ • Divisor.toQDivisor B'.roundDown) ∧
        (Divisor.toQDivisor K' + (B' - δ • Divisor.toQDivisor B'.roundDown)).IsRelativelyNef
          sX' f' ∧
        (Divisor.toQDivisor K' + (B' - δ • Divisor.toQDivisor B'.roundDown)).IsRelativelyBig
          f' := by
  obtain ⟨W, _, _, _, p, sW, _, _, KW, BW, hpW, hpb, ⟨hp, hpD⟩, hS⟩ :=
    MMP.FourfoldProofs.MmpSurfaceProjectiveLcNefBigEpsilonModelProof.exists_isStage_dltModification
      hf hlc hB hnef hbig
  obtain ⟨n, hn⟩ : ∃ n : ℕ, picardNumber sW = n :=
    ⟨(picardNumber sW).toNat,
      (ENat.coe_toNat (picardNumber_lt_top_of_isProjectiveVariety sW).ne).symm⟩
  obtain ⟨X', _, _, _, sX', _, _, K', B', f', hf', hQ, hlc', hB', ⟨q, hqb, hqf, hq, hqD⟩,
    hε⟩ :=
    MMP.FourfoldProofs.MmpSurfaceProjectiveLcNefBigEpsilonModelProof.conclusion_of_isStage n hS hn
  have hWp : AlgebraicGeometry.IsProjectiveVariety ℂ (p ≫ sX) := by
    rw [hpW]
    infer_instance
  exact ⟨X', ‹_›, ‹_›, ‹_›, sX', ‹_›, ‹_›, K', B', f', hf', hQ, hlc', hB',
    ⟨W, ‹_›, ‹_›, ‹_›, p, q, hWp, hpb, hqb, hqf.symm, hp, hq, _, hpD, hqD⟩, hε⟩

end MMP.Mori

end
