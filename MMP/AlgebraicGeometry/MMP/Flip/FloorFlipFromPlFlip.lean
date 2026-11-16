module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Flip.PlFlipFromRestrictedAlgebra
public import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
public import MMP.AlgebraicGeometry.Singularities.DltKltShrinkBoundary
public import MMP.AlgebraicGeometry.Singularities.BoundaryLowering
public import MMP.AlgebraicGeometry.Singularities.DltDiscrepancy
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleBasics
public import MMP.AlgebraicGeometry.MMP.Flip.SmallAmpleModel
public import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics

section

/-!
# Flips of floor contractions from pl-flips

Let `(X, Θ)` be a rational `ℚ`-factorial projective dlt complex `n`-fold, `n ≥ 3`, and
`f : X ⟶ W` the small contraction of a `(K + Θ)`-negative extremal ray `R` on which a component
`S` of `⌊Θ⌋` is negative. Assuming `F(n - 1)`, `f` has a `(K + Θ)`-flip.

For a small rational `ε > 0` the lowered boundary `Θ_ε = Θ - ε⌊Θ⌋ + εS` is dlt with
`⌊Θ_ε⌋ = S`, hence plt, and `K + Θ_ε` is still negative on `R`; both `-(K + Θ_ε)` and `-S` are
`f`-ample, so `F(n - 1)` gives the pl-flip `f⁺ : X⁺ ⟶ W` of `K + Θ_ε`. Comparing the degrees of
`D = K + Θ` and `D_ε = K + Θ_ε` on `R` gives positive integers `p, q` with `qD - pD_ε`
numerically trivial over `W`; by descent of line bundles along the contraction of `R` (applied
to the klt pair `(X, Θ - ε⌊Θ⌋)`) a Cartier multiple `G` of it is the pull-back of a Cartier
divisor `N` on `W`. As `f` and `f⁺` are isomorphisms in codimension one over `W`, the strict
transform of `G` is `(f⁺)^* N`, so a multiple of `D⁺` is an `f⁺`-ample multiple of `D_ε⁺` plus a
pull-back from `W`, hence `f⁺`-ample. Thus `f⁺` is also the `(K + Θ)`-flip, and the elementary
dlt step preserves `ℚ`-factoriality and dlt.

## Main results

* `MMP.Fourfold.exists_isFlip_of_birationalFiniteGenerationProperty_of_isFloorFlippingContraction`.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori MMP.Fourfold

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.FourfoldProofs.FourfoldProjectiveFloorFlipFromPlProof

/-! ### Transforms of divisors -/

/-- Regarding a divisor as a `ℚ`-divisor commutes with mapping prime divisors. -/
private theorem toQDivisor_mapPrimeDivisors {X Y : Scheme.{0}}
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : Divisor X) :
    Divisor.toQDivisor (DivisorWithCoeffs.mapPrimeDivisors φ D) =
      DivisorWithCoeffs.mapPrimeDivisors φ (Divisor.toQDivisor D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single E n =>
    rw [MMP.Threefold.Resolution.toQDivisor_single, DivisorWithCoeffs.mapPrimeDivisors_single,
      DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ E <;> simp [MMP.Threefold.Resolution.toQDivisor_single]

/-- Regarding a divisor as a `ℚ`-divisor commutes with the strict transform `(f⁺)⁻¹_* f_*`. -/
private theorem toQDivisor_flipTransform {X Y X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    Divisor.toQDivisor (flipTransform f fp D) = flipTransform f fp (Divisor.toQDivisor D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, inverseTransformDivisor,
    RationalMap.transformDivisor, toQDivisor_mapPrimeDivisors]

/-- **Strict transforms of pull-backs.** Let `f : X ⟶ W` be proper birational and `f⁺ : X⁺ ⟶ W`
small onto a normal variety. If `G = f^* N` for a Cartier divisor `N` on `W`, then the strict
transform `(f⁺)⁻¹_* f_* G` is `(f⁺)^* N`: at a prime divisor `P` of `X⁺` over the prime divisor
`Q` of `W`, both coefficients are the coefficient of `Q` in `N`. -/
private theorem isPullback_flipTransform {X W Xp : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [CompactSpace Xp]
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W]
    {sXp : Xp ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {f : X ⟶ W} {fp : Xp ⟶ W}
    [IsProper f] (hfb : IsBirationalMorphism f) (hfp : IsSmallMorphism sXp sW fp)
    {N : Divisor W} (hN : N.IsCartier)
    {hs : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ N.supp}
    {G : Divisor X} (hG : N.IsPullback f hs G)
    (hs' : ∀ Z : irreducibleComponents Xp, fp (componentGenericPoint Xp Z) ∉ N.supp) :
    N.IsPullback fp hs' (flipTransform f fp G) := by
  have hpb := Divisor.isPullback_pullback (f := fp) hN hs'
  suffices h : flipTransform f fp G = N.pullback hN hs' by rwa [h]
  refine Finsupp.ext fun P => ?_
  have hW := hfp.isNormalVariety_target
  obtain ⟨Pm, Q, -, hPmQ, hPQ⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hW hfb hfp P
  have hPmQ' := map_genericPoint_eq_of_image_eq Pm Q hPmQ
  have hPQ' := map_genericPoint_eq_of_image_eq P Q hPQ
  obtain ⟨Pm', hPm', htr⟩ := exists_eq_genericPoint_flipTransform_apply hfb hfp P Pm.genericPoint
    (hPmQ'.trans hPQ'.symm)
  have hPm'Q : f Pm'.genericPoint = Q.genericPoint := hPm' ▸ hPmQ'
  haveI := isIso_stalkMap_of_map_eq_genericPoint hfb hPm'Q
  haveI := isIso_stalkMap_of_map_eq_genericPoint hfp.isBirationalMorphism hPQ'
  rw [htr]
  exact (MMP.Positivity.coeff_eq_of_isPullback Pm' Q hPm'Q hN hG).trans
    (MMP.Positivity.coeff_eq_of_isPullback P Q hPQ' hN hpb).symm

/-! ### Curve forms -/

section CurveForm

variable {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [QuasiCompact sX]

/-- The curve form depends only on the divisor. -/
private theorem curveForm_congr {D D' : QDivisor X} (e : D = D') (hD : D.IsQCartier)
    (hD' : D'.IsQCartier) : QDivisor.curveForm sX D hD = QDivisor.curveForm sX D' hD' := by
  subst e
  rfl

/-- The curve form is additive in the divisor. -/
private theorem curveForm_add (D D' : QDivisor X) (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDD' : (D + D').IsQCartier) :
    QDivisor.curveForm sX (D + D') hDD' =
      QDivisor.curveForm sX D hD + QDivisor.curveForm sX D' hD' := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.add_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_add' ℂ sX C.ι C.dim_le D D' hD hD' hDD']
  push_cast
  rfl

/-- The curve form is `ℚ`-homogeneous in the divisor. -/
private theorem curveForm_smul (q : ℚ) (D : QDivisor X) (hD : D.IsQCartier)
    (hqD : (q • D).IsQCartier) :
    QDivisor.curveForm sX (q • D) hqD = (q : ℝ) • QDivisor.curveForm sX D hD := by
  refine MMP.ProgramBaseChange.linearMap_ext_numericalClass_cycle sX fun C => ?_
  rw [LinearMap.smul_apply, MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
    QDivisor.intersectionNumber_smul ℂ sX C.ι C.dim_le q D hD hqD]
  push_cast
  rfl

/-- The curve form, evaluated, is the sum over the associated `ℚ`-Cartier divisor. -/
private theorem curveForm_apply (D : QDivisor X) (hD : D.IsQCartier)
    (u : NumericalCurveClasses sX) :
    QDivisor.curveForm sX D hD u = (D.associatedCartier hD).sum fun E c =>
      haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
      (c : ℝ) * NumericalCurveClasses.degree sX (E : Divisor X).divisorialSheaf u := by
  rw [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply, Finsupp.sum]
  rfl

/-- Two `ℚ`-Cartier divisors negative on the nonzero classes of an extremal ray `R` have
proportional degrees on `R`: `q (D · C) = p (D' · C)` for some positive integers `p, q`. -/
theorem exists_mul_curveForm_sub_mul_eq_zero {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {D D' : QDivisor X} (hD : D.IsQCartier) (hD' : D'.IsQCartier)
    (hDn : ∀ u ∈ R, u ≠ 0 → QDivisor.curveForm sX D hD u < 0)
    (hD'n : ∀ u ∈ R, u ≠ 0 → QDivisor.curveForm sX D' hD' u < 0) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ ∀ C : ProperCurve sX,
      OneCycle.numericalClass sX (C.cycle ℝ) ∈ R →
        (q : ℝ) * QDivisor.curveForm sX D hD (OneCycle.numericalClass sX (C.cycle ℝ)) -
          p * QDivisor.curveForm sX D' hD' (OneCycle.numericalClass sX (C.cycle ℝ)) = 0 := by
  by_cases h0 : ∃ C₀ : ProperCurve sX, OneCycle.numericalClass sX (C₀.cycle ℝ) ∈ R ∧
      OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0
  · obtain ⟨C₀, hC₀R, hC₀0⟩ := h0
    have ha := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX _ hD C₀
    have hb := MMP.ProgramBaseChange.curveForm_numericalClass_cycle sX _ hD' C₀
    set a : ℚ := D.intersectionNumber ℂ sX C₀.ι C₀.dim_le hD
    set b : ℚ := D'.intersectionNumber ℂ sX C₀.ι C₀.dim_le hD'
    have ha0 : a < 0 := by
      have := hDn _ hC₀R hC₀0
      rw [ha] at this
      exact_mod_cast this
    have hb0 : b < 0 := by
      have := hD'n _ hC₀R hC₀0
      rw [hb] at this
      exact_mod_cast this
    set c : ℚ := a / b
    have hnum : 0 < c.num := Rat.num_pos.mpr (div_pos_of_neg_of_neg ha0 hb0)
    refine ⟨c.num.toNat, c.den, by omega, c.den_pos, fun C hC => ?_⟩
    obtain ⟨v, -, hRv⟩ := hR.2
    obtain ⟨μ, -, hμv⟩ := hRv ▸ hC
    obtain ⟨l, -, hlv⟩ := hRv ▸ hC₀R
    have hl0 : l ≠ 0 := by
      rintro rfl
      exact hC₀0 (by rw [← hlv, zero_smul])
    have hz : OneCycle.numericalClass sX (C.cycle ℝ) =
        (μ / l) • OneCycle.numericalClass sX (C₀.cycle ℝ) := by
      rw [← hμv, ← hlv, smul_smul, div_mul_cancel₀ _ hl0]
    have hcq : ((c.num.toNat : ℕ) : ℚ) = c * c.den := by
      rw [show ((c.num.toNat : ℕ) : ℚ) = (c.num : ℚ) by
        exact_mod_cast Int.toNat_of_nonneg hnum.le]
      exact (Rat.mul_den_eq_num c).symm
    have hcab : c * b = a := div_mul_cancel₀ a hb0.ne
    have key : (c.den : ℚ) * a - ((c.num.toNat : ℕ) : ℚ) * b = 0 := by
      rw [hcq, ← hcab]
      ring
    have key' : ((c.den : ℕ) : ℝ) * (a : ℝ) - ((c.num.toNat : ℕ) : ℝ) * (b : ℝ) = 0 := by
      exact_mod_cast key
    rw [hz, map_smul, map_smul, ha, hb, smul_eq_mul, smul_eq_mul]
    linear_combination (μ / l) * key'
  · simp only [not_exists, not_and, not_not] at h0
    refine ⟨1, 1, one_pos, one_pos, fun C hC => ?_⟩
    rw [h0 C hC, map_zero, map_zero]
    ring

/-- A Cartier divisor `G = m (qD - pD')` has degree zero on every curve `C` with
`q (D · C) = p (D' · C)`. -/
theorem degree_divisorialSheaf_eq_zero_of_mul_curveForm_sub_mul_eq_zero
    (hq : ∀ E : QDivisor X, E.IsQCartier) {D D' : QDivisor X} {m p q : ℕ} {G : Divisor X}
    (hGc : G.IsCartier) (hGq : Divisor.toQDivisor G = (m : ℤ) • ((q : ℤ) • D - (p : ℤ) • D'))
    (C : ProperCurve sX)
    (hC : (q : ℝ) * QDivisor.curveForm sX D (hq D) (OneCycle.numericalClass sX (C.cycle ℝ)) -
      p * QDivisor.curveForm sX D' (hq D') (OneCycle.numericalClass sX (C.cycle ℝ)) = 0) :
    haveI := hGc.isInvertibleModule_divisorialSheaf
    C.degree ℂ G.divisorialSheaf = 0 := by
  haveI := hGc.isInvertibleModule_divisorialSheaf
  rw [ProperCurve.degree_divisorialSheaf C G hGc]
  have h1 : ((G.degreeOn ℂ sX C.ι C.dim_le hGc : ℤ) : ℝ) =
      QDivisor.curveForm sX (Divisor.toQDivisor G) (hq _)
        (OneCycle.numericalClass sX (C.cycle ℝ)) := by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_toQDivisor ℂ sX C.ι C.dim_le G hGc (hq _)]
    push_cast
    rfl
  have h2 : Divisor.toQDivisor G = (m : ℚ) • ((q : ℚ) • D + (-(p : ℚ)) • D') := by
    rw [hGq]
    refine Finsupp.ext fun P => ?_
    simp only [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.add_apply, smul_eq_mul,
      zsmul_eq_mul, Int.cast_natCast]
    ring
  rw [curveForm_congr sX h2 (hq _) (hq _), curveForm_smul sX _ _ (hq _) (hq _),
    curveForm_add sX _ _ (hq _) (hq _) (hq _), curveForm_smul sX _ _ (hq D) (hq _),
    curveForm_smul sX _ _ (hq D') (hq _)] at h1
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at h1
  have h4 : ((G.degreeOn ℂ sX C.ι C.dim_le hGc : ℤ) : ℝ) = 0 := by
    rw [h1]
    push_cast
    linear_combination (m : ℝ) * hC
  exact_mod_cast h4

end CurveForm

/-! ### Elementary steps -/

/-- A flip of the small contraction of a negative extremal ray of a projective `ℚ`-factorial dlt
pair, with `f⁺` projective, is an elementary dlt step. -/
private theorem isProjectiveElementaryDltStep_of_isFlip {X W Xp : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    {sX : X ⟶ Spec (.of ℂ)} {sW : W ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)}
    {K : Divisor X} {Δ : QDivisor X} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W}
    {fp : Xp ⟶ W} (hP : IsProjectiveQFactorialDltPair sX K Δ)
    (hR : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R)
    (hfR : IsContractionOfRay sX sW R f) (hsmall : IsSmallMorphism sX sW f)
    (hamp : (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f)
    (hfl : IsFlip sX sW sXp K Δ f fp) (hfpP : IsProjectiveMorphism fp) :
    IsProjectiveElementaryDltStep sX sW sXp K Δ R f fp (flipTransform f fp Δ) := by
  refine ⟨hP, hR, hfR, hsmall.isBirationalMorphism, hfl.comp_eq, rfl, Or.inl ⟨hsmall,
    ⟨hR.1, hfR.toIsContraction, hsmall, hamp, ⟨hfl.isNormalVariety,
      hsmall.isNormalVariety_target, hfl.comp_eq, hfl.isProper, hfl.isBirationalMorphism,
      hfl.two_le_codimension⟩, hfpP, ?_, ?_⟩⟩⟩
  · rw [map_add, ← toQDivisor_flipTransform]
    exact hfl.isQCartier
  · rw [map_add, ← toQDivisor_flipTransform]
    exact hfl.hasRelativelyAmpleMultiple

/-! ### Auxiliary results -/

/-- The lowered boundary `Θ_ε = Θ - ε⌊Θ⌋ + εS` of a boundary `0 ≤ Θ ≤ 1` with `Θ S = 1` and
`Θ - ε⌊Θ⌋ ≥ 0` satisfies `0 ≤ Θ_ε ≤ Θ` and `⌊Θ_ε⌋ = S`. -/
theorem loweredBoundary_spec {X : Scheme.{0}} {Θ Δ Θt : QDivisor X}
    {S : MMP.Mori.PrimeDivisor X} {ε : ℚ} (hε : 0 < ε) (hΘ0 : ∀ P, 0 ≤ Θ P)
    (hΘ1 : ∀ P, Θ P ≤ 1) (hS1 : Θ S = 1)
    (hΔ : Δ = Θ - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Θ)) (hΔ0 : ∀ P, 0 ≤ Δ P)
    (hΘt : Θt = Δ + ε • (Finsupp.single S 1 : QDivisor X)) :
    0 ≤ Θt ∧ Θt ≤ Θ ∧ DivisorWithCoeffs.roundDown Θt = Finsupp.single S 1 ∧
      0 ≤ Θt - Finsupp.single S 1 := by
  classical
  have hΔc : ∀ P, Δ P = Θ P - ε * ⌊Θ P⌋ := fun P => by
    simp [hΔ, ← DivisorWithCoeffs.coeff_apply]
  have hΔlt : ∀ P, Δ P < 1 := fun P => by
    rw [hΔc]
    rcases (hΘ1 P).lt_or_eq with h | h
    · rw [Int.floor_eq_zero_iff.mpr ⟨hΘ0 P, h⟩]
      simpa using h
    · rw [h, Int.floor_one, Int.cast_one]
      linarith
  have hΔle : ∀ P, Δ P ≤ Θ P := fun P => by
    rw [hΔc]
    have : (0 : ℚ) ≤ ⌊Θ P⌋ := by exact_mod_cast Int.floor_nonneg.mpr (hΘ0 P)
    nlinarith
  have hΘtS : Θt S = 1 := by
    rw [hΘt, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same, hΔc, hS1,
      Int.floor_one, Int.cast_one, smul_eq_mul]
    ring
  have hΘtP : ∀ P, P ≠ S → Θt P = Δ P := fun P hP => by
    rw [hΘt, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, if_neg (Ne.symm hP),
      smul_zero, add_zero]
  refine ⟨fun P => ?_, fun P => ?_, Finsupp.ext fun P => ?_, fun P => ?_⟩
  · by_cases hPS : P = S
    · subst hPS
      rw [Finsupp.coe_zero, Pi.zero_apply, hΘtS]
      exact zero_le_one
    · rw [Finsupp.coe_zero, Pi.zero_apply, hΘtP P hPS]
      exact hΔ0 P
  · by_cases hPS : P = S
    · subst hPS
      rw [hΘtS, hS1]
    · rw [hΘtP P hPS]
      exact hΔle P
  · rw [← DivisorWithCoeffs.coeff_apply, DivisorWithCoeffs.coeff_roundDown,
      DivisorWithCoeffs.coeff_apply]
    by_cases hPS : P = S
    · subst hPS
      rw [hΘtS, Finsupp.single_eq_same, Int.floor_one]
    · rw [hΘtP P hPS, Finsupp.single_apply, if_neg (Ne.symm hPS)]
      exact Int.floor_eq_zero_iff.mpr ⟨hΔ0 P, hΔlt P⟩
  · rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.sub_apply]
    by_cases hPS : P = S
    · subst hPS
      rw [hΘtS, Finsupp.single_eq_same, sub_self]
    · rw [hΘtP P hPS, Finsupp.single_apply, if_neg (Ne.symm hPS), sub_zero]
      exact hΔ0 P

end MMP.FourfoldProofs.FourfoldProjectiveFloorFlipFromPlProof

end

section

/-!
# Flips of floor contractions from pl-flips

Assume the birational finite-generation property `F(n - 1)` for some `n ≥ 3`. Let `(X, Θ)` be a
rational `ℚ`-factorial projective dlt complex `n`-fold and let `f : X ⟶ W` be the small
contraction, onto a projective variety, of a `(K_X + Θ)`-negative extremal ray `R` of `NE̅(X)` on
which some prime component `S` of `⌊Θ⌋` is negative. Then `f` has a `(K_X + Θ)`-flip
`f⁺ : X⁺ ⟶ W`, with `X⁺` projective and `ℚ`-factorial and `(X⁺, Θ⁺)` dlt, where
`Θ⁺ = (f⁺)⁻¹_* f_* Θ`.

The proof lowers the other reduced components: for small rational `t > 0` the pair
`(X, Θ - t(⌊Θ⌋ - S))` is plt with `⌊·⌋ = S`, so `F(n - 1)` gives its pl-flip; since `ρ(X/W) = 1`,
`K_X + Θ` is a positive multiple of the lowered adjoint up to a pullback from `W`, so the same
model is the `(K_X + Θ)`-flip, and the elementary dlt step preserves `ℚ`-factoriality and dlt.

## Main results

* `MMP.Fourfold.exists_isFlip_of_birationalFiniteGenerationProperty_of_isFloorFlippingContraction`.

## Implementation notes

The pair is `MMP.Fourfold.IsFloorPair` and the contraction is
`MMP.Fourfold.IsFloorFlippingContraction`, as in the first clause of
`MMP.Fourfold.ProjectiveFloorProgramInputs`; the negative prime `S ⊆ ⌊Θ⌋` is its
`MMP.Fourfold.IsComponentNegative` field. The flip is `MMP.Mori.IsFlip`, with boundary on `X⁺`
the birational transform `MMP.Mori.flipTransform f f⁺ Θ`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.FourfoldProofs.FourfoldProjectiveFloorFlipFromPlProof in
/-- **Flips of floor contractions from pl-flips.** Assume `F(n - 1)`
(`MMP.Fourfold.BirationalFiniteGenerationProperty (n - 1)`) with `n ≥ 3`. Let `(X, Θ)` be a
rational `ℚ`-factorial projective dlt complex `n`-fold with canonical divisor `K`, and let
`f : X ⟶ W` be the small contraction onto a projective variety of a `(K + Θ)`-negative extremal
ray `R` on which some prime component of `⌊Θ⌋` is negative. Then there is a projective
`ℚ`-factorial normal variety `X⁺` with a `(K + Θ)`-flip `f⁺ : X⁺ ⟶ W` of `f`, and
`(X⁺, (f⁺)⁻¹_* f_* Θ)` is dlt. -/
@[mmp "lem_fourfold_projective_floor_flip_from_pl"]
public theorem exists_isFlip_of_birationalFiniteGenerationProperty_of_isFloorFlippingContraction
    {n : ℕ} (hn : 3 ≤ n) (hF : BirationalFiniteGenerationProperty (n - 1))
    {X : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {K : Divisor X} {Θ : QDivisor X} (hX : IsFloorPair sX n K Θ)
    {W : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {R : Set (NumericalCurveClasses sX)} {f : X ⟶ W}
    (hf : IsFloorFlippingContraction sX sW K Θ R f) :
    ∃ (Xp : Scheme.{0}) (_ : IsIntegral Xp) (_ : CompactSpace Xp) (_ : IsLocallyNoetherian Xp)
      (_ : IsNormal Xp) (sXp : Xp ⟶ Spec (.of ℂ)) (fp : Xp ⟶ W),
        MMP.Mori.IsProjectiveVariety ℂ sXp ∧ IsFlip sX sW sXp K Θ f fp ∧
          IsQFactorial sXp ∧ MMP.Intersection.IsDltPair sXp (flipTransform f fp Θ) := by
  classical
  obtain ⟨hXp, hdim, hQ, ⟨m₀, hK₀⟩, hdlt⟩ := hX
  have hKn : K.IsCanonicalDivisor sX n := by
    have h := hK₀.topologicalKrullDim_eq
    rw [hdim] at h
    have hm : m₀ = n := by exact_mod_cast h.symm
    exact hm ▸ hK₀
  obtain ⟨⟨hAq, hRay, hAneg⟩, hfR, hsmall, hWp, hfamp, S, hS1, hSq, hSneg⟩ := hf
  have hXv : IsNormalVariety ℂ sX := hQ.1
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
  have hWv : IsNormalVariety ℂ sW := hfR.isNormalVariety_target
  haveI : AlgebraicGeometry.IsVariety ℂ sW := hWv.1
  haveI : IsIntegral W := hWv.1.toIsIntegral
  haveI : IsNormal W := hWv.2
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  haveI : IsProper f := hsmall.isProper
  have hfb : IsBirationalMorphism f := hsmall.isBirationalMorphism
  haveI := hfb.isDominant
  have hq := isQCartier_of_isQFactorial sX hQ
  have hP : IsProjectiveQFactorialDltPair sX K Θ := ⟨hXp, hQ, ⟨n, hKn⟩, hdlt⟩
  have hcontr : ∀ C : ProperCurve sX, C.IsContractedBy f →
      OneCycle.numericalClass sX (C.cycle ℝ) ∈ R := fun C => (hfR.isContractedBy_iff C).mp
  /- The klt perturbation `Δ = Θ - ε⌊Θ⌋` and the lowered boundary `Θ_ε = Δ + εS`. -/
  obtain ⟨ε, hε, hklt, hRε⟩ := hP.exists_isKltPair_sub_smul_roundDown ⟨hAq, hRay, hAneg⟩
  set Δ : QDivisor X := Θ - ε • Divisor.toQDivisor (DivisorWithCoeffs.roundDown Θ) with hΔdef
  set Θt : QDivisor X := Δ + ε • (Finsupp.single S 1 : QDivisor X) with hΘtdef
  obtain ⟨hΘt0, hΘtle, hfloorΘt, hB0⟩ := loweredBoundary_spec hε (fun P => hdlt.1.2.1 P)
    (fun P => hdlt.2.1 P) hS1 hΔdef (fun P => hklt.1.nonneg P) hΘtdef
  set B : QDivisor X := Θt - Finsupp.single S 1
  have hΘtB : Finsupp.single S 1 + B = Θt := add_sub_cancel _ _
  have hfloor : DivisorWithCoeffs.roundDown (Finsupp.single S 1 + B) = Finsupp.single S 1 := by
    rw [hΘtB, hfloorΘt]
  /- `(X, Θ_ε)` is dlt with `⌊Θ_ε⌋ = S`, hence plt. -/
  have hdltt : MMP.Intersection.IsDltPair sX Θt :=
    MMP.Intersection.IsDltPair.of_le sX hdlt hΘt0 hΘtle (hq _)
  have hplt : IsPltPair sX n K Θt := by
    refine ((MMP.Threefold.Bridges.isDltPair_iff_isDltPair sX hKn Θt).mp
      hdltt).isPltPair_of_pairwise_disjoint (by omega) hΘt0 ?_
    refine (Set.subsingleton_singleton (a := S)).anti (fun P hP => ?_) |>.pairwise _
    by_contra hPS
    refine hP ?_
    rw [hfloorΘt, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply,
      if_neg (fun h => hPS (Set.mem_singleton_iff.mpr h.symm))]
  /- `K + Θ_ε` is negative on `R`. -/
  have hSS : Divisor.toQDivisor (Finsupp.single S 1) = (Finsupp.single S 1 : QDivisor X) := by
    rw [MMP.Threefold.Resolution.toQDivisor_single]
    simp
  have hAtq : (Divisor.toQDivisor K + Θt).IsQCartier := hq _
  have hAtneg : ∀ u ∈ R, u ≠ 0 →
      QDivisor.curveForm sX (Divisor.toQDivisor K + Θt) hAtq u < 0 := by
    intro u hu hu0
    rw [curveForm_congr sX (show Divisor.toQDivisor K + Θt = (Divisor.toQDivisor K + Δ) +
        ε • Divisor.toQDivisor (Finsupp.single S 1) by rw [hSS, hΘtdef, add_assoc]) hAtq (hq _),
      curveForm_add sX _ _ hRε.1 (hq _) (hq _), curveForm_smul sX ε _ hSq (hq _),
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    nlinarith [hRε.2.2 u hu hu0, hSneg u hu hu0, (by exact_mod_cast hε : (0 : ℝ) < ε)]
  have hRt : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Θt) R := ⟨hAtq, hRay, hAtneg⟩
  /- `-(K + Θ_ε)` and `-S` are `f`-ample. -/
  have hnegt : (-(Divisor.toQDivisor K + Θt)).HasRelativelyAmpleMultiple f :=
    hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sW hXv hXp hWp ⟨n, hKn⟩ hAtq hRay
      (fun v hv hv0 => by rw [← curveForm_apply]; exact hAtneg v hv hv0) f hfR.comp_eq hcontr
  have hSneg' : QDivisor.HasRelativelyAmpleMultiple (-(Finsupp.single S 1 : QDivisor X)) f := by
    have hSq' : (Divisor.toQDivisor K + ((Finsupp.single S 1 : QDivisor X) -
        Divisor.toQDivisor K)).IsQCartier := hq _
    have h := hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sW hXv hXp hWp ⟨n, hKn⟩ hSq'
      hRay (fun v hv hv0 => by
        rw [← curveForm_apply, curveForm_congr sX (show Divisor.toQDivisor K +
          ((Finsupp.single S 1 : QDivisor X) - Divisor.toQDivisor K) =
            Divisor.toQDivisor (Finsupp.single S 1) by rw [hSS]; abel) hSq' hSq]
        exact hSneg v hv hv0) f hfR.comp_eq hcontr
    rwa [add_sub_cancel] at h
  /- The pl-flip of `K + Θ_ε`. -/
  have hn1 : n - 1 + 1 = n := by omega
  obtain ⟨Xp, _, _, _, sXp, fp, hflt⟩ :=
    exists_isFlip_of_birationalFiniteGenerationProperty_of_isPltPair (d := n - 1) (by omega) hF
      sX hXp hQ (by rw [hdim, ← Nat.cast_one (R := WithBot ℕ∞), ← Nat.cast_add, hn1]) sW hWp
      (by rw [hn1]; exact hKn) hB0 hfloor (by rw [hn1, hΘtB]; exact hplt) hRay hfR hsmall
      (by rwa [hΘtB]) hSneg'
  rw [hΘtB] at hflt
  have hXpv : IsNormalVariety ℂ sXp := hflt.isNormalVariety
  haveI : AlgebraicGeometry.IsVariety ℂ sXp := hXpv.1
  haveI : IsIntegral Xp := hXpv.1.toIsIntegral
  haveI : IsProper fp := hflt.isProper
  have hfps : IsSmallMorphism sXp sW fp := ⟨hXpv, hWv, hflt.comp_eq, hflt.isProper,
    hflt.isBirationalMorphism, hflt.two_le_codimension⟩
  /- `X⁺` is projective and `f⁺` is a projective morphism. -/
  have hXpp : MMP.Mori.IsProjectiveVariety ℂ sXp := by
    refine (AlgebraicGeometry.isProjectiveVariety_iff_isProjective' ℂ sXp).mpr ⟨hXpv.1, ?_⟩
    rw [← hflt.comp_eq]
    exact hflt.isProjective.comp
      ((AlgebraicGeometry.isProjectiveVariety_iff_isProjective' ℂ sW).mp hWp).2
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sXp := hXpp
  haveI := AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sXp
  have hfpP : IsProjectiveMorphism fp :=
    MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sXp sW fp hflt.comp_eq
  /- `X⁺` is `ℚ`-factorial, by the elementary step of `K + Θ_ε`. -/
  have hQp : IsQFactorial sXp :=
    (isProjectiveElementaryDltStep_of_isFlip ⟨hXp, hQ, ⟨n, hKn⟩, hdltt⟩ hRt hfR hsmall hnegt hflt
      hfpP).isQFactorial_and_isDltPair.1
  /- The ray degrees of `D = K + Θ` and `D_ε = K + Θ_ε` are proportional. -/
  obtain ⟨p, q, hp, hq0, hpq⟩ := exists_mul_curveForm_sub_mul_eq_zero sX hRay hAq hAtq hAneg hAtneg
  /- A Cartier multiple `G` of `qD - pD_ε` is the pull-back of a Cartier divisor `N` on `W`. -/
  obtain ⟨m, hm, G, hGq, hGc⟩ :=
    (hq ((q : ℤ) • (Divisor.toQDivisor K + Θ) - (p : ℤ) • (Divisor.toQDivisor K + Θt))).exists_pos
  obtain ⟨N, hNc, hsN, hGpb⟩ : ∃ (N : Divisor W) (hN : N.IsCartier)
      (hsN : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ N.supp),
      N.IsPullback f hsN G := by
    have hkltM : MMP.Mori.IsKltPair sX n K Δ :=
      (isKltPair_iff_mori_isKltPair sX hKn hklt.1).mp hklt
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hXp
    have hFace : IsNegativeExtremalFace ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX))
        (MMP.Fourfold.QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hkltM.1.2.2) R :=
      ⟨hRay.1, hRay.1.2.2.1, hRε.2.2⟩
    have hg : IsContractionOfFace ℂ sX sW R f :=
      ⟨hXp, hWp, hfR.comp_eq, hRay.1, hfR.isContractedBy_iff, hfR.isIso_app⟩
    haveI := hGc.isInvertibleModule_divisorialSheaf
    obtain ⟨LW, hLW, ⟨eG⟩⟩ := exists_isInvertible_iso_pullback_of_isContractionOfFace hkltM
      hklt.1.nonneg hFace hg G.divisorialSheaf fun C hC =>
        degree_divisorialSheaf_eq_zero_of_mul_curveForm_sub_mul_eq_zero sX hq hGc hGq C (hpq C hC)
    obtain ⟨N₀, hN₀c, ⟨eN⟩⟩ := MMP.Mori.exists_isCartier_divisorialSheaf_iso LW
    have hs₀ : ∀ Z : irreducibleComponents X, f (componentGenericPoint X Z) ∉ N₀.supp :=
      MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f N₀
    obtain ⟨ePb⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hN₀c f hs₀
    obtain ⟨ρ, hρ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
      (eG ≪≫ (Scheme.Modules.pullback f).mapIso eN.symm ≪≫ ePb.symm)
    obtain ⟨ψ, hψ, hψρ⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hfb ρ
    have hNc : (N₀ + principalDivisor ψ).IsCartier :=
      hN₀c.add (Divisor.isCartier_principalDivisor ψ)
    have hsN : ∀ Z : irreducibleComponents X,
        f (componentGenericPoint X Z) ∉ (N₀ + principalDivisor ψ).supp :=
      MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant f _
    refine ⟨N₀ + principalDivisor ψ, hNc, hsN, ?_⟩
    have h := (Divisor.isPullback_pullback hN₀c hs₀).add hN₀c (Divisor.isCartier_principalDivisor ψ)
      hsN (Divisor.isPullback_principalDivisor ψ hψ)
    rwa [hψρ, ← hρ, add_sub_cancel] at h
  /- Its strict transform is `(f⁺)^* N`, so `K⁺ + Θ⁺` is `f⁺`-ample. -/
  have hs' : ∀ Z : irreducibleComponents Xp, fp (componentGenericPoint Xp Z) ∉ N.supp := by
    haveI := hfps.isBirationalMorphism.isDominant
    exact MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant fp N
  have hGp := isPullback_flipTransform hfb hfps hNc hGpb hs'
  have hampD : (Divisor.toQDivisor (flipTransform f fp K) +
      flipTransform f fp Θ).HasRelativelyAmpleMultiple fp := by
    obtain ⟨r, hr, Lt, hLtc, hLtq, hLtamp⟩ := hflt.hasRelativelyAmpleMultiple
    haveI := hfps.isBirationalMorphism.isDominant
    have hGpc : Divisor.IsCartier (flipTransform f fp G) :=
      (hGp.pullback_eq hNc) ▸ hNc.isCartier_pullback fp hs'
    have hGpq : Divisor.toQDivisor (flipTransform f fp G) = (m : ℤ) • ((q : ℤ) •
        (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp Θ) - (p : ℤ) •
        (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp Θt)) := by
      rw [toQDivisor_flipTransform, hGq, map_zsmul, map_sub, map_zsmul, map_zsmul, map_add,
        map_add, ← toQDivisor_flipTransform]
    have hbas := MMP.Flips.relativelyAmple_basics sXp sW hXpv hWv fp hflt.comp_eq
    have hLtC : MMP.Flips.IsRelativelyAmpleCartier fp Lt := by
      haveI := hLtc.isInvertibleModule_divisorialSheaf
      exact ⟨hLtc, fun U hU =>
        (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple fp _
          inferInstance hLtamp).2 U hU⟩
    have h1 := (hbas.2.1 Lt hLtC).2 ((m * p : ℕ) : ℤ) (by positivity)
    have hrN := hGp.zsmul hNc (r : ℤ)
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant fp _)
    obtain ⟨hLc, hLamp⟩ := (hbas.2.1 _ h1).1 ((r : ℤ) • N) (hNc.zsmul _) _ _ hrN
    refine ⟨m * q * r, by positivity, _, hLc, ?_, ?_⟩
    · rw [map_add, map_zsmul, map_zsmul, hLtq, hGpq]
      push_cast
      module
    · haveI := hLc.isInvertibleModule_divisorialSheaf
      intro y
      obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
      exact ⟨V, hV, hyV, hLamp V hV⟩
  have hflip : IsFlip sX sW sXp K Θ f fp :=
    { isFlippingContraction :=
        { hflt.isFlippingContraction with isQCartier := hAq, hasRelativelyAmpleMultiple := hfamp }
      isNormalVariety := hXpv
      comp_eq := hflt.comp_eq
      isProper := hflt.isProper
      isBirationalMorphism := hflt.isBirationalMorphism
      isQCartier := isQCartier_of_isQFactorial sXp hQp _
      hasRelativelyAmpleMultiple := hampD
      two_le_codimension := hflt.two_le_codimension }
  have hres := (isProjectiveElementaryDltStep_of_isFlip hP ⟨hAq, hRay, hAneg⟩ hfR hsmall hfamp
    hflip hfpP).isQFactorial_and_isDltPair
  exact ⟨Xp, inferInstance, inferInstance, inferInstance, inferInstance, sXp, fp, hXpp, hflip,
    hres.1, hres.2⟩

end MMP.Fourfold

end
