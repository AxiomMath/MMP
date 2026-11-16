module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
public import MMP.AlgebraicGeometry.MMP.Fourfold.NefLogBirationalModel
public import MMP.AlgebraicGeometry.MMP.Flip.NumericalClassTransport
public import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
public import MMP.AlgebraicGeometry.Singularities.Surface.LogDiscrepancyVector
public import MMP.AlgebraicGeometry.MMP.Fourfold.Flip.DltFlip
public import MMP.AlgebraicGeometry.MMP.Contraction.DltStepPreserved
public import MMP.AlgebraicGeometry.MMP.Contraction.LineBundleDescent
public import MMP.AlgebraicGeometry.MMP.Contraction.KltRayContraction
public import MMP.AlgebraicGeometry.MMP.Flip.NegativeAdjointTransfer
public import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
public import MMP.AlgebraicGeometry.MMP.Contraction.CurveFactorization
public import MMP.AlgebraicGeometry.ProjectiveBundle.UniversalProperty
public import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
public import MMP.Combinatorics.WeightedGraph.ChainDeterminant
public import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
public import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparisonCommonBase
public import MMP.AlgebraicGeometry.MMP.Contraction.RayContractionAntiAmple
public import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
public import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
public import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
public import MMP.AlgebraicGeometry.Intersection.PairingSeparation
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryStepPreserved
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltSmallContractionFlip
public import MMP.AlgebraicGeometry.MMP.Fourfold.ElementaryStepDiagram
public import MMP.AlgebraicGeometry.ChowForm.FibreChowForm
public import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
public import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantDltLiftNotNef
public import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
public import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
public import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
public import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
public import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector

/-!
# Elementary steps of real dlt fourfolds and descent of real null divisors

Let `g : X ⟶ S` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
fourfold with canonical divisor `K`, let `(X, B)` be a dlt pair with real boundary, and let `R`
be a `(K + B)`-negative extremal ray of the relative closed cone `NE̅(X/S)`. Then `R` has a
contraction `f : X ⟶ Z`, `h : Z ⟶ S` over `S`, with `Z` projective, `-(K + B)` `f`-ample and
`ρ(X/Z) = 1`. If `f` is divisorial, `Z` is `ℚ`-factorial and `(Z, f_* B)` is dlt; if `f` is small,
it has a real flip `f⁺ : X⁺ ⟶ Z` with `X⁺` a projective `ℚ`-factorial fourfold and `(X⁺, B⁺)`
dlt for the strict transform `B⁺`.

If `f` is birational, every `ℝ`-Cartier divisor `N` on `X` which is null on `R` is the
pull-back `f^* M` of an `ℝ`-Cartier divisor `M` on `Z`; in the small case `f⁺^* M` is the strict
transform of `N`. In particular, if `(X, B')` is lc, `K + B'` is nef over `S` and null on `R`,
then the transformed pair is lc again with adjoint nef over `S`, on `Z` in the divisorial case
and on `X⁺` in the small case.

## Main results

* `MMP.Fourfold.IsRealDltPair.exists_isRelativeContractionOfFace_of_isExtremalRay`.

## Implementation notes

Real divisors are `MMP.Mori.RDivisor`s and the adjoint is `MMP.Flips.logCanonicalDivisor K B`.
Intersection numbers with curves are `MMP.Flips.IsRIntersectionNumber`, computed with any
presentation by Cartier divisors. A divisor is null on `R` when its intersection number with
every curve `C` contracted by `g` whose class lies in `R` is zero.
The ray `R` is `(K + B)`-negative when `K + B` has a presentation `∑ rⱼ Lⱼ` by Cartier divisors
whose linear form `u ↦ ∑ rⱼ (u · 𝒪_X(Lⱼ))` on `N₁(X/S)` is negative at every `0 ≠ u ∈ R`, as in
`MMP.Fourfold.IsNegativeRelativeExtremalRayOf`; this does not depend on `R` containing curve
classes. An `ℝ`-Cartier divisor is an `MMP.Flips.IsCartierCombination`, and its descent is the
exact equality `N = f^* M` of `MMP.Flips.IsRCartierPullback`. The divisorial case is "`f` is
birational and `Ex(f)` is a prime divisor". The small case is `MMP.Flips.IsSmall`, and the flip is
a step of an extremal real flip sequence, `MMP.Fourfold.IsRealFlipStep`, whose canonical divisor
and boundary are the strict transforms `flipTransform f f⁺ K` and `flipTransform f f⁺ B`. In the
divisorial case the canonical divisor of `Z` is `f_* K`.

Exact descent is asserted only for birational `f`. For a contraction of fibre type it fails
already for principal divisors: on `X = ℙ¹ × ℙ³` with `R` the ray of `ℙ¹ × pt`, the divisor
`div(t) = {0} × ℙ³ - {∞} × ℙ³` is null on `R`, but `{0} × ℙ³` dominates `Z`, so every pull-back
has coefficient `0` along it. For fibre-type contractions descent holds only up to `ℝ`-linear
equivalence.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.25, 3.36,
  3.44
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips MMP.Fourfold

namespace Proof_lem_fourfold_real_dlt_fourfold_elementary_step

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Degrees of `ℝ`-Cartier presentations on `N₁` -/

section Degree

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X]

/-- The linear form `u ↦ ∑ⱼ rⱼ (u · 𝒪_X(Lⱼ))` on `N₁(X)` of a presentation `∑ⱼ rⱼ Lⱼ` by Cartier
divisors. -/
private noncomputable def presDeg (sX : X ⟶ Spec (.of ℂ)) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) : NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  ∑ j, r j • (haveI := (hL j).isInvertibleModule_divisorialSheaf
    NumericalCurveClasses.degree sX (L j).divisorialSheaf)

private theorem presDeg_apply {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (u : NumericalCurveClasses sX) :
    presDeg sX r L hL u = ∑ j, r j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
      NumericalCurveClasses.degree sX (L j).divisorialSheaf u) := by
  simp [presDeg]

private theorem presDeg_numericalClass_cycle [QuasiCompact sX] {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) (C : ProperCurve sX) :
    presDeg sX r L hL (OneCycle.numericalClass sX (C.cycle ℝ)) =
      ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hL j) : ℝ) := by
  rw [presDeg_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  haveI := (hL j).isInvertibleModule_divisorialSheaf
  rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
  rfl

/-- The value of a presentation on a curve is an `ℝ`-intersection number. -/
private theorem isRIntersectionNumber_presDeg [QuasiCompact sX] {D : RDivisor X} {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber ℂ sX D r L C
      (presDeg sX r L hL (OneCycle.numericalClass sX (C.cycle ℝ))) := by
  refine ⟨hL, fun j => (L j).degreeOn ℂ sX C.ι C.dim_le (hL j), hD, fun j =>
    MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sX C (L j) (hL j), ?_⟩
  rw [presDeg_numericalClass_cycle]

/-- Two presentations of one `ℝ`-divisor have the same linear form on `N₁(X)`. -/
private theorem presDeg_congr [QuasiCompact sX] {m m' : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    (hL : ∀ j, (L j).IsCartier) {r' : Fin m' → ℝ} {L' : Fin m' → Divisor X}
    (hL' : ∀ j, (L' j).IsCartier)
    (h : ∑ j, r j • Divisor.toRDivisor (L j) = ∑ j, r' j • Divisor.toRDivisor (L' j)) :
    presDeg sX r L hL = presDeg sX r' L' hL' := by
  have hc : (presDeg sX r L hL).comp (OneCycle.numericalClass sX) =
      (presDeg sX r' L' hL').comp (OneCycle.numericalClass sX) := by
    refine Finsupp.lhom_ext fun C b => ?_
    have hb : (Finsupp.single C b : OneCycle ℝ sX) = b • C.cycle ℝ := by
      simp [ProperCurve.cycle]
    simp only [LinearMap.comp_apply, hb, map_smul, smul_eq_mul]
    congr 1
    exact (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r L r' L' _ _
      (isRIntersectionNumber_presDeg r L hL rfl C)
      (isRIntersectionNumber_presDeg r' L' hL' h C)
  refine LinearMap.ext fun u => ?_
  obtain ⟨Z, rfl⟩ := OneCycle.numericalClass_surjective sX u
  exact LinearMap.congr_fun hc Z

/-- The curve form of a `ℚ`-Cartier `ℚ`-divisor is the linear form of any presentation. -/
private theorem curveForm_eq_presDeg [QuasiCompact sX] (D : QDivisor X) (hD : D.IsQCartier)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (h : QDivisor.toRDivisor D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    QDivisor.curveForm sX D hD = presDeg sX r L hL := by
  set E := D.cartierIndexSMul hD
  have hE : (E : Divisor X).IsCartier := E.2
  have hm : (D.cartierIndex hD : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (QDivisor.cartierIndex_pos hD).ne'
  have h1 : QDivisor.curveForm sX D hD =
      presDeg sX (fun _ : Fin 1 => ((1 / (D.cartierIndex hD : ℚ) : ℚ) : ℝ))
        (fun _ : Fin 1 => (E : Divisor X)) (fun _ => hE) := by
    refine LinearMap.ext fun u => ?_
    rw [presDeg_apply, Fin.sum_univ_one]
    simp only [QDivisor.curveForm, QDivisor.associatedCartier,
      CartierDivisorWithCoeffs.ofCartier, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [Finsupp.sum_single_index (by simp)]
    rfl
  rw [h1]
  refine presDeg_congr _ hL ?_
  rw [Fin.sum_univ_one, ← h]
  have hE' := QDivisor.toQDivisor_cartierIndexSMul D hD
  ext P
  have := congrArg (fun F : QDivisor X => F.coeff P) hE'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
  have this' : (((E : Divisor X).coeff P : ℤ) : ℝ) =
      ((D.cartierIndex hD : ℕ) : ℝ) * ((D.coeff P : ℚ) : ℝ) := by exact_mod_cast this
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [this']
  have hm' : ((D.cartierIndex hD : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
  push_cast
  field_simp

end Degree

/-! ### Relative classes and negativity -/

section Ray

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X]

private theorem presDeg_relativeToAbsolute {S : Scheme.{0}} (g : X ⟶ S) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (u : RelativeNumericalCurveClasses sX g) :
    presDeg sX r L hL (relativeToAbsolute sX g u) = ∑ j, r j *
      (haveI := (hL j).isInvertibleModule_divisorialSheaf
       RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) := by
  rw [presDeg_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX g u
  rfl

/-- A `ℚ`-Cartier divisor negative on the generator of an extremal ray is negative on the ray. -/
private theorem isNegativeExtremalRayOf_of_neg {D : QDivisor X} (hD : D.IsQCartier)
    {R : Set (NumericalCurveClasses sX)}
    (hR : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R)
    {v : NumericalCurveClasses sX} (hv : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w})
    (hneg : QDivisor.curveForm sX D hD v < 0) : IsNegativeExtremalRayOf sX D R := by
  refine ⟨hD, hR, fun u hu hu0 => ?_⟩
  rw [hv] at hu
  obtain ⟨c, hc, rfl⟩ := hu
  have hc0 : 0 < c := hc.lt_of_ne (by rintro rfl; exact hu0 (zero_smul _ _))
  rw [map_smul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg hc0 hneg

end Ray

/-! ### Log discrepancies are affine in the boundary -/

section LogDiscrepancy

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X]

/-- Adding `∑ᵢ tᵢ Lᵢ` (`Lᵢ` Cartier, with pull-backs `L'ᵢ`) to the boundary lowers a log
discrepancy along `E` by `∑ᵢ tᵢ coeff_E L'ᵢ`. -/
private theorem isLogDiscrepancy_add_sum {n : ℕ} {B : RDivisor X} {D : DivisorOver ℂ sX}
    {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n B D a) {k : ℕ} (t : Fin k → ℝ)
    (L : Fin k → Divisor X) (hL : ∀ i, (L i).IsCartier) (L' : Fin k → Divisor D.Y)
    (hL' : ∀ i, haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      ∃ hB, (L i).IsPullback D.f hB (L' i)) :
    MMP.Intersection.IsLogDiscrepancy sX n (B + ∑ i, t i • Divisor.toRDivisor (L i)) D
      (a - ∑ i, t i * ((L' i).coeff D.E : ℝ)) := by
  obtain ⟨hX, hp, ω, hω, hK, m, r, C, C', hC, hsum, hpb, rfl⟩ := ha
  refine ⟨hX, hp, ω, hω, hK, m + k, Fin.append r t, Fin.append C L, Fin.append C' L',
    fun i => ?_, fun Γ => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (motive := fun i => (Fin.append C L i).IsCartier) (fun j => ?_)
      (fun j => ?_) i
    · simpa using hC j
    · simpa using hL j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, DivisorWithCoeffs.coeff_add]
    rw [← hsum Γ]
    have : (∑ i, t i • Divisor.toRDivisor (L i)).coeff Γ = ∑ i, t i * ((L i).coeff Γ : ℝ) := by
      rw [← DivisorWithCoeffs.coeffAddMonoidHom_apply, map_sum]
      simp
    rw [this]
    ring
  · refine Fin.addCases (motive := fun i => haveI := D.isLocallyNoetherian
      haveI := D.isNormal
      ∃ hB, (Fin.append C L i).IsPullback D.f hB (Fin.append C' L' i)) (fun j => ?_)
      (fun j => ?_) i
    · simpa using hpb j
    · simpa using hL' j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    ring

/-- Every Cartier divisor has a pull-back to a divisor over `X`. -/
private theorem exists_pullback_divisorOver (D : DivisorOver ℂ sX) {L : Divisor X}
    (hL : L.IsCartier) :
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    ∃ L' : Divisor D.Y, (∃ hB, L.IsPullback D.f hB L') ∧
      ((∀ P, 0 ≤ L.coeff P) → ∀ P, 0 ≤ L'.coeff P) := by
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI := D.isIntegral
  haveI := D.isDominant
  haveI : CompactSpace D.Y := by
    haveI := D.isNormalVariety.1.toQuasiCompact
    exact QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  obtain ⟨L', hL'⟩ := MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f hL
  refine ⟨L', ⟨_, hL'⟩, fun hL0 P => ?_⟩
  exact MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn hL (V := ⊤) (fun Q _ => hL0 Q)
    hL' P
    ⟨P.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support P, trivial⟩

/-- **Monotonicity of log discrepancies.** Raising the boundary by an effective combination
`∑ᵢ tᵢ Lᵢ` of effective Cartier divisors (`tᵢ ≥ 0`) does not raise log discrepancies. -/
private theorem exists_isLogDiscrepancy_add_sum_le {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n B D a) {k : ℕ}
    (t : Fin k → ℝ) (ht : ∀ i, 0 ≤ t i) (L : Fin k → Divisor X) (hL : ∀ i, (L i).IsCartier)
    (hL0 : ∀ i P, 0 ≤ (L i).coeff P) :
    ∃ b ≤ a, MMP.Intersection.IsLogDiscrepancy sX n (B + ∑ i, t i • Divisor.toRDivisor (L i)) D b
    := by
  choose L' hL' hL'0 using fun i => exists_pullback_divisorOver D (hL i)
  refine ⟨_, ?_, isLogDiscrepancy_add_sum ha t L hL L' hL'⟩
  have : 0 ≤ ∑ i, t i * ((L' i).coeff D.E : ℝ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (ht i) (by exact_mod_cast hL'0 i (hL0 i) D.E)
  linarith

end LogDiscrepancy

/-! ### Perturbations of the boundary in a fixed support -/

section Perturbation

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X]

/-- A positive integer `m` with `m P` Cartier, for a prime divisor `P` of a `ℚ`-factorial `X`. -/
private noncomputable def qfIndex (hXQ : IsQFactorial sX) (P : MMP.Mori.PrimeDivisor X) : ℕ :=
  (hXQ.2 (Finsupp.single P 1)).choose

private theorem qfIndex_pos (hXQ : IsQFactorial sX) (P : MMP.Mori.PrimeDivisor X) :
    0 < qfIndex hXQ P :=
  (hXQ.2 (Finsupp.single P 1)).choose_spec.1

private theorem isCartier_qfIndex (hXQ : IsQFactorial sX) (P : MMP.Mori.PrimeDivisor X) :
    Divisor.IsCartier (((qfIndex hXQ P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor X)) :=
  (hXQ.2 (Finsupp.single P 1)).choose_spec.2

/-- The coefficients of the presentation of `∑_{P ∈ s} c_P P` by the Cartier divisors
`m_P P`. -/
private noncomputable def pertR (hXQ : IsQFactorial sX) (s : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) : Fin s.card → ℝ :=
  fun i => c (s.equivFin.symm i) / (qfIndex hXQ (s.equivFin.symm i) : ℝ)

/-- The Cartier divisors `m_P P`, `P ∈ s`. -/
private noncomputable def pertL (hXQ : IsQFactorial sX) (s : Finset (MMP.Mori.PrimeDivisor X)) :
    Fin s.card → Divisor X :=
  fun i => ((qfIndex hXQ (s.equivFin.symm i) : ℕ) : ℤ) • Finsupp.single (s.equivFin.symm i).1 1

private theorem isCartier_pertL (hXQ : IsQFactorial sX) (s : Finset (MMP.Mori.PrimeDivisor X))
    (i : Fin s.card) : (pertL hXQ s i).IsCartier :=
  isCartier_qfIndex hXQ _

private theorem pertL_nonneg (hXQ : IsQFactorial sX) (s : Finset (MMP.Mori.PrimeDivisor X))
    (i : Fin s.card) (P : MMP.Mori.PrimeDivisor X) : 0 ≤ (pertL hXQ s i).coeff P := by
  classical
  change 0 ≤ ((qfIndex hXQ (s.equivFin.symm i) : ℕ) : ℤ) *
    (Finsupp.single (s.equivFin.symm i).1 (1 : ℤ) P)
  rw [Finsupp.single_apply]
  split_ifs <;> simp

private theorem sum_pert (hXQ : IsQFactorial sX) (s : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) :
    ∑ i, pertR hXQ s c i • Divisor.toRDivisor (pertL hXQ s i) =
      ∑ P ∈ s, c P • Divisor.toRDivisor (Finsupp.single P 1) := by
  rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (qfIndex hXQ (s.equivFin.symm i) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (qfIndex_pos hXQ _).ne'
  simp only [pertR, pertL, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast]
  rw [div_mul_cancel₀ _ hm]

omit [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] in
open Classical in
/-- The coefficient of `∑_{P ∈ s} c_P P` at `Q`. -/
private theorem coeff_sum_smul_single (s : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (Q : MMP.Mori.PrimeDivisor X) :
    (∑ P ∈ s, c P • Divisor.toRDivisor (Finsupp.single P 1)).coeff Q =
      if Q ∈ s then c Q else 0 := by
  rw [← DivisorWithCoeffs.coeffAddMonoidHom_apply, map_sum]
  have h : ∀ P, DivisorWithCoeffs.coeffAddMonoidHom Q
      (c P • Divisor.toRDivisor (Finsupp.single P (1 : ℤ))) = if P = Q then c P else 0 := by
    intro P
    change c P * ((Finsupp.single P (1 : ℤ) Q : ℤ) : ℝ) = _
    rw [Finsupp.single_apply]
    split_ifs <;> simp
  simp only [h]
  rw [Finset.sum_ite_eq']

private theorem presDeg_append {m m' : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X)
    (hL' : ∀ j, (L' j).IsCartier) (hLL : ∀ j, (Fin.append L L' j).IsCartier) :
    presDeg sX (Fin.append r r') (Fin.append L L') hLL =
      presDeg sX r L hL + presDeg sX r' L' hL' := by
  refine LinearMap.ext fun u => ?_
  simp only [presDeg_apply, LinearMap.add_apply, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right]

private theorem isCartier_append {m m' : ℕ} {L : Fin m → Divisor X}
    (hL : ∀ j, (L j).IsCartier) {L' : Fin m' → Divisor X} (hL' : ∀ j, (L' j).IsCartier) :
    ∀ j, (Fin.append L L' j).IsCartier := fun j =>
  Fin.addCases (motive := fun j => (Fin.append L L' j).IsCartier) (fun i => by simpa using hL i)
    (fun i => by simpa using hL' i) j

private theorem sum_append {m m' : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (r' : Fin m' → ℝ)
    (L' : Fin m' → Divisor X) :
    ∑ j, Fin.append r r' j • Divisor.toRDivisor (Fin.append L L' j) =
      ∑ j, r j • Divisor.toRDivisor (L j) + ∑ j, r' j • Divisor.toRDivisor (L' j) := by
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]

/-- The value at `P` of the degree form of `m_P P`, divided by `m_P`: the degree of `P`. -/
private noncomputable def primeDeg (hXQ : IsQFactorial sX) (v : NumericalCurveClasses sX)
    (P : MMP.Mori.PrimeDivisor X) : ℝ :=
  (qfIndex hXQ P : ℝ)⁻¹ * (haveI := (isCartier_qfIndex hXQ P).isInvertibleModule_divisorialSheaf
    NumericalCurveClasses.degree sX
      (Divisor.divisorialSheaf (((qfIndex hXQ P : ℕ) : ℤ) • (Finsupp.single P 1 : Divisor X))) v)

private theorem presDeg_pert (hXQ : IsQFactorial sX) (s : Finset (MMP.Mori.PrimeDivisor X))
    (c : MMP.Mori.PrimeDivisor X → ℝ) (v : NumericalCurveClasses sX) :
    presDeg sX (pertR hXQ s c) (pertL hXQ s) (isCartier_pertL hXQ s) v =
      ∑ P ∈ s, c P * primeDeg hXQ v P := by
  rw [presDeg_apply, ← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pertR, primeDeg, pertL, div_eq_mul_inv]
  ring

/-- **The degree form after perturbing the boundary.** If `Δ = B + ∑_{P ∈ s} c_P P`, the curve
form of `K + Δ` is that of `K + B` plus `∑_{P ∈ s} c_P (P · -)`. -/
private theorem curveForm_eq_add [QuasiCompact sX] (hXQ : IsQFactorial sX) {K : Divisor X}
    {B : RDivisor X} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hKB : logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j))
    (s : Finset (MMP.Mori.PrimeDivisor X)) (c : MMP.Mori.PrimeDivisor X → ℝ) {Δ : QDivisor X}
    (hΔ : QDivisor.toRDivisor Δ = B + ∑ P ∈ s, c P • Divisor.toRDivisor (Finsupp.single P 1))
    (hQ : (Divisor.toQDivisor K + Δ).IsQCartier) (v : NumericalCurveClasses sX) :
    QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hQ v =
      presDeg sX r L hL v + ∑ P ∈ s, c P * primeDeg hXQ v P := by
  have hLL := isCartier_append hL (isCartier_pertL hXQ s)
  have hpres : QDivisor.toRDivisor (Divisor.toQDivisor K + Δ) =
      ∑ j, Fin.append r (pertR hXQ s c) j • Divisor.toRDivisor (Fin.append L (pertL hXQ s) j) := by
    rw [sum_append, sum_pert, ← hKB, map_add, QDivisor.toRDivisor_toQDivisor, hΔ,
      logCanonicalDivisor, add_assoc]
  rw [curveForm_eq_presDeg _ hQ (Fin.append r (pertR hXQ s c)) (Fin.append L (pertL hXQ s)) hLL
    hpres, presDeg_append r L hL _ _ (isCartier_pertL hXQ s), LinearMap.add_apply, presDeg_pert]

end Perturbation

/-! ### Supports of transforms -/

section Support

variable {X Y : Scheme.{0}}

open Classical in
private theorem mapPrimeDivisors_apply {R : Type*} [AddCommMonoid R]
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (D : DivisorWithCoeffs R X)
    (Q : MMP.Mori.PrimeDivisor Y) :
    DivisorWithCoeffs.mapPrimeDivisors φ D Q =
      ∑ P ∈ D.support, if φ P = some Q then D P else 0 := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [DivisorWithCoeffs.mapPrimeDivisors_single]
  cases h : φ P with
  | none => simp
  | some Q' => simp [Finsupp.single_apply]

/-- The transform of an effective divisor has at least the support of the transform of any
divisor whose support lies in its own. -/
private theorem support_mapPrimeDivisors_subset {R : Type*} [AddCommMonoid R]
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) {D : DivisorWithCoeffs R X}
    {D' : RDivisor X} (hD' : ∀ P, 0 ≤ D' P) (h : D.support ⊆ D'.support) :
    (DivisorWithCoeffs.mapPrimeDivisors φ D).support ⊆
      (DivisorWithCoeffs.mapPrimeDivisors φ D').support := by
  classical
  intro Q hQ
  rw [Finsupp.mem_support_iff, mapPrimeDivisors_apply] at hQ ⊢
  obtain ⟨P, hP, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hQ
  have hφ : φ P = some Q := by by_contra hc; simp [hc] at hne
  have hP' := h hP
  intro h0
  have hle : D' P ≤ ∑ P ∈ D'.support, if φ P = some Q then D' P else 0 := by
    have := Finset.single_le_sum (f := fun P => if φ P = some Q then D' P else 0)
      (fun P _ => by split_ifs <;> simp [hD' P]) hP'
    simpa [hφ] using this
  rw [h0] at hle
  exact (Finsupp.mem_support_iff.mp hP') (le_antisymm hle (hD' P))

end Support

/-! ### A klt rational witness -/

section Witness

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- **A klt rational boundary below a real dlt boundary.** If `(X, B)` is dlt with real boundary,
`X` `ℚ`-factorial, and `K + B` is negative on a class `v`, there is a rational boundary
`0 ≤ Δ₀ ≤ B` with all coefficients below one and the support of `B`, such that `(X, Δ₀)` is klt
and `K + Δ₀` is still negative on `v`. -/
private theorem exists_isKltPair_curveForm_neg [QuasiCompact sX] (hXQ : IsQFactorial sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hB : IsRealDltPair sX B) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X}
    (hL : ∀ j, (L j).IsCartier)
    (hKB : logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j))
    (v : NumericalCurveClasses sX) (hv : presDeg sX r L hL v < 0) :
    ∃ Δ₀ : QDivisor X, MMP.Intersection.IsDltPair sX Δ₀ ∧ IsKltPair sX Δ₀ ∧
      ∃ hQ : (Divisor.toQDivisor K + Δ₀).IsQCartier,
      QDivisor.curveForm sX (Divisor.toQDivisor K + Δ₀) hQ v < 0 := by
  classical
  obtain ⟨⟨hXn, hB0, -, hBlc⟩, hB1, Z, hZsm, hZsnc, hZpos⟩ := hB
  set s := B.support
  set M : ℝ := ∑ P ∈ s, |primeDeg hXQ v P| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set η : ℝ := -presDeg sX r L hL v / (2 * (M + 1)) with hη
  have hη0 : 0 < η := div_pos (by linarith) (by positivity)
  have hBpos : ∀ P ∈ s, 0 < B P := fun P hP =>
    (hB0 P).lt_of_ne (Ne.symm (Finsupp.mem_support_iff.mp hP))
  -- rational coefficients slightly below those of `B`
  have hq : ∀ P, ∃ q : ℚ, P ∈ s → (max 0 (B P - η) < q ∧ (q : ℝ) < B P) := by
    intro P
    by_cases hP : P ∈ s
    · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
        (max_lt (hBpos P hP) (by linarith) : max 0 (B P - η) < B P)
      exact ⟨q, fun _ => ⟨hq1, hq2⟩⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose q hq using hq
  set Δ₀ : QDivisor X := ∑ P ∈ s, Finsupp.single P (q P) with hΔ₀
  have hΔ₀coeff : ∀ P, Δ₀.coeff P = if P ∈ s then q P else 0 := by
    intro P
    rw [hΔ₀, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
  have hΔ₀R : QDivisor.toRDivisor Δ₀ =
      B + ∑ P ∈ s, ((q P : ℝ) - B P) • Divisor.toRDivisor (Finsupp.single P 1) := by
    ext P
    rw [DivisorWithCoeffs.coeff_add, coeff_sum_smul_single, QDivisor.coeff_toRDivisor, hΔ₀coeff,
      DivisorWithCoeffs.coeff_apply]
    by_cases hP : P ∈ s
    · simp [hP]
    · simp [hP, Finsupp.notMem_support_iff.mp hP]
  have hBΔ : B = QDivisor.toRDivisor Δ₀ +
      ∑ i, pertR hXQ s (fun P => B P - q P) i • Divisor.toRDivisor (pertL hXQ s i) := by
    rw [sum_pert, hΔ₀R, add_assoc, ← Finset.sum_add_distrib]
    simp only [← add_smul, sub_add_sub_cancel, sub_self, zero_smul, Finset.sum_const_zero,
      add_zero]
  have hpertR : ∀ i, 0 ≤ pertR hXQ s (fun P => B P - q P) i := fun i => by
    simp only [pertR]
    exact div_nonneg (by linarith [(hq _ (s.equivFin.symm i).2).2]) (Nat.cast_nonneg _)
  -- log discrepancies of `Δ₀` dominate those of `B`
  have hcmp : ∀ (n' : ℕ) (D : DivisorOver ℂ sX) (a : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX n' (QDivisor.toRDivisor Δ₀) D a →
        ∃ b ≤ a, MMP.Intersection.IsLogDiscrepancy sX n' B D b := by
    intro n' D a ha
    obtain ⟨b, hb, hb'⟩ := exists_isLogDiscrepancy_add_sum_le ha _ hpertR (pertL hXQ s)
      (isCartier_pertL hXQ s) (pertL_nonneg hXQ s)
    exact ⟨b, hb, by rw [hBΔ]; exact hb'⟩
  have hQ : (Divisor.toQDivisor K + Δ₀).IsQCartier := isQCartier_of_isQFactorial sX hXQ _
  have hcoeff0 : ∀ P, 0 ≤ Δ₀.coeff P := fun P => by
    rw [hΔ₀coeff]; split_ifs with hP
    · exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) (hq P hP).1).le
    · exact le_rfl
  have hcoeff1 : ∀ P, Δ₀.coeff P < 1 := fun P => by
    rw [hΔ₀coeff]; split_ifs with hP
    · exact_mod_cast (hq P hP).2.trans_le (hB1 P)
    · exact zero_lt_one
  have hdlt : MMP.Intersection.IsDltPair sX Δ₀ := by
    refine ⟨⟨⟨hXn, n, K, hK, hQ⟩, hcoeff0, fun n' D a ha => ?_⟩, fun P => (hcoeff1 P).le, Z, hZsm,
      ?_, fun n' D hD a ha => ?_⟩
    · obtain ⟨b, hba, hb⟩ := hcmp n' D a ha
      exact (hBlc n' D b hb).trans hba
    · refine hZsnc.of_support_subset ?_
      refine support_mapPrimeDivisors_subset _ (fun P => ?_) ?_
      · exact hB0 _
      · intro P hP
        have h1 : Δ₀.coeff P ≠ 0 := Finsupp.mem_support_iff.mp hP
        rw [hΔ₀coeff] at h1
        split_ifs at h1 with hPs
        · exact hPs
        · exact absurd rfl h1
    · obtain ⟨b, hba, hb⟩ := hcmp n' D a ha
      exact (hZpos n' D hD b hb).trans_le hba
  refine ⟨Δ₀, hdlt, hdlt.isKltPair_of_forall_coeff_lt_one hcoeff1, hQ, ?_⟩
  rw [curveForm_eq_add hXQ hL hKB s _ hΔ₀R hQ v]
  have hsum : |∑ P ∈ s, ((q P : ℝ) - B P) * primeDeg hXQ v P| ≤ η * M := by
    rw [hM, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun P hP => ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have h1 := (hq P hP).1
    have h2 := (hq P hP).2
    rw [abs_le]
    constructor <;> linarith [le_max_right 0 (B P - η)]
  have hηM : η * M < -presDeg sX r L hL v := by
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith [le_abs_self (∑ P ∈ s, ((q P : ℝ) - B P) * primeDeg hXQ v P)]

end Witness

/-! ### Real boundaries as convex combinations of rational ones -/

section Decomposition

/-- A real vector is a convex combination, with positive weights, of rational vectors within
`η` of it: the vertices of a small rational simplex around it. -/
private theorem exists_rat_convex_combination {ι : Type*} [Fintype ι] (b : ι → ℝ) {η : ℝ}
    (hη : 0 < η) :
    ∃ (q : Option ι → ι → ℚ) (w : Option ι → ℝ), (∀ o, 0 < w o) ∧ ∑ o, w o = 1 ∧
      (∀ o i, |(q o i : ℝ) - b i| < η) ∧ ∀ i, ∑ o, w o * (q o i : ℝ) = b i := by
  classical
  set k := Fintype.card ι
  have hk : (0 : ℝ) < 2 * (k + 1) := by positivity
  have hq₀ : ∀ i, ∃ q : ℚ, b i - η / (2 * (k + 1)) < q ∧ (q : ℝ) < b i := fun i =>
    exists_rat_btwn (by linarith [div_pos hη hk])
  choose q₀ hq₀ using hq₀
  set d : ι → ℝ := fun i => b i - q₀ i with hd
  have hd0 : ∀ i, 0 < d i := fun i => by simp only [hd]; linarith [(hq₀ i).2]
  have hdη : ∀ i, d i < η / (2 * (k + 1)) := fun i => by simp only [hd]; linarith [(hq₀ i).1]
  set D := ∑ i, d i with hD
  have hD0 : 0 ≤ D := Finset.sum_nonneg fun i _ => (hd0 i).le
  have hDη : D < η / 2 := by
    calc D ≤ ∑ _i : ι, η / (2 * (k + 1)) := Finset.sum_le_sum fun i _ => (hdη i).le
      _ = k * (η / (2 * (k + 1))) := by simp [k]
      _ < η / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ hk two_pos]
        nlinarith
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show D < η / 2 from hDη)
  have ht0 : (0 : ℝ) < t := hD0.trans_lt ht1
  refine ⟨fun o i => o.elim (q₀ i) fun j => q₀ i + if i = j then t else 0,
    fun o => o.elim (1 - D / t) fun j => d j / t, fun o => ?_, ?_, fun o i => ?_, fun i => ?_⟩
  · cases o with
    | none => simp only [Option.elim]; rw [sub_pos, div_lt_one ht0]; exact ht1
    | some j => exact div_pos (hd0 j) ht0
  · rw [Fintype.sum_option]
    simp only [Option.elim]
    rw [← Finset.sum_div, ← hD]
    field_simp
    ring
  · have h1 : |(q₀ i : ℝ) - b i| < η / 2 := by
      rw [abs_sub_comm, abs_of_pos (hd0 i)]
      exact (hdη i).trans_le (div_le_div_of_nonneg_left hη.le two_pos (by linarith))
    cases o with
    | none => simp only [Option.elim]; linarith
    | some j =>
      simp only [Option.elim]
      split_ifs
      · push_cast
        calc |(q₀ i : ℝ) + t - b i| ≤ |(q₀ i : ℝ) - b i| + |(t : ℝ)| := by
              rw [show (q₀ i : ℝ) + t - b i = ((q₀ i : ℝ) - b i) + t by ring]
              exact abs_add_le _ _
          _ < η / 2 + η / 2 := by
              rw [abs_of_pos ht0]; linarith
          _ = η := by ring
      · simp only [add_zero]; linarith
  · rw [Fintype.sum_option]
    simp only [Option.elim]
    have h : ∑ j, d j / t * (((q₀ i + if i = j then t else 0 : ℚ)) : ℝ) = D / t * q₀ i + d i := by
      simp only [Rat.cast_add, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero, mul_add, mul_ite,
        mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.sum_mul, ← Finset.sum_div, ← hD]
      field_simp
    rw [h, hd]
    field_simp
    ring

variable {X : Scheme.{0}}

open Classical in
/-- A real divisor is a convex combination, with positive weights, of rational divisors in its
support whose coefficients are within `η` of its own. -/
private theorem exists_rat_decomposition (B : RDivisor X) {η : ℝ} (hη : 0 < η) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (Δ : ι → QDivisor X) (w : ι → ℝ)
      (c : ι → MMP.Mori.PrimeDivisor X → ℝ),
      (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • QDivisor.toRDivisor (Δ i) = B ∧
        (∀ i P, |c i P| < η) ∧ ∀ i, QDivisor.toRDivisor (Δ i) =
          B + ∑ P ∈ B.support, c i P • Divisor.toRDivisor (Finsupp.single P 1) := by
  set s := B.support
  obtain ⟨q, w, hw, hw1, hqη, hqb⟩ := exists_rat_convex_combination (fun P : s => B P) hη
  set Δ : Option s → QDivisor X := fun o => ∑ P : s, Finsupp.single P.1 (q o P) with hΔ
  have hΔcoeff : ∀ o (P : MMP.Mori.PrimeDivisor X),
      (Δ o) P = if h : P ∈ s then q o ⟨P, h⟩ else 0 := by
    intro o P
    simp only [hΔ, Finsupp.finset_sum_apply, Finsupp.single_apply]
    by_cases hP : P ∈ s
    · rw [dif_pos hP, Finset.sum_eq_single ⟨P, hP⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        exact fun h => hb (Subtype.ext h)
      · simp
    · rw [dif_neg hP]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg]
      exact fun h => hP (h ▸ b.2)
  set c : Option s → MMP.Mori.PrimeDivisor X → ℝ :=
    fun o P => if h : P ∈ s then (q o ⟨P, h⟩ : ℝ) - B P else 0 with hc
  refine ⟨Option s, inferInstance, ⟨none⟩, Δ, w, c, hw, hw1, ?_, fun o P => ?_, fun o => ?_⟩
  · ext P
    rw [← DivisorWithCoeffs.coeffAddMonoidHom_apply, map_sum]
    have h : ∀ o, DivisorWithCoeffs.coeffAddMonoidHom P (w o • QDivisor.toRDivisor (Δ o)) =
        w o * ((Δ o P : ℚ) : ℝ) := fun o => rfl
    simp only [h, hΔcoeff]
    by_cases hP : P ∈ s
    · simp only [dif_pos hP]
      exact hqb ⟨P, hP⟩
    · simp only [dif_neg hP, Rat.cast_zero, mul_zero, Finset.sum_const_zero]
      exact (Finsupp.notMem_support_iff.mp hP).symm
  · simp only [hc]
    split_ifs with hP
    · exact hqη o ⟨P, hP⟩
    · simpa using hη
  · ext P
    rw [DivisorWithCoeffs.coeff_add, coeff_sum_smul_single, QDivisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_apply, hΔcoeff, DivisorWithCoeffs.coeff_apply]
    by_cases hP : P ∈ s
    · simp only [dif_pos hP, if_pos hP, hc]
      ring
    · simp only [dif_neg hP, if_neg hP, Rat.cast_zero, Finsupp.notMem_support_iff.mp hP,
        add_zero]

end Decomposition

/-! ### Relative ampleness of real combinations -/

section Ample

variable {X Y : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]

private theorem isRelativelyAmple_add' {f : X ⟶ Y} {A A' : RDivisor X}
    (h : IsRelativelyAmple f A) (h' : IsRelativelyAmple f A') : IsRelativelyAmple f (A + A') := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := h
  obtain ⟨m', r', L', hm', hr', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r r', Fin.append L L', by omega, fun j => ?_, fun j => ?_, ?_⟩
  · exact Fin.addCases (motive := fun j => 0 < Fin.append r r' j) (fun i => by simpa using hr i)
      (fun i => by simpa using hr' i) j
  · exact Fin.addCases (motive := fun j => IsRelativelyAmpleCartier f (Fin.append L L' j))
      (fun i => by simpa using hL i) (fun i => by simpa using hL' i) j
  · rw [Fin.sum_univ_add]
    simp

private theorem isRelativelyAmple_smul' {f : X ⟶ Y} {A : RDivisor X} (h : IsRelativelyAmple f A)
    {c : ℝ} (hc : 0 < c) : IsRelativelyAmple f (c • A) := by
  obtain ⟨m, r, L, hm, hr, hL, rfl⟩ := h
  exact ⟨m, fun j => c * r j, L, hm, fun j => mul_pos hc (hr j), hL,
    by simp [Finset.smul_sum, smul_smul]⟩

/-- A positive combination of relatively ample real divisors is relatively ample. -/
private theorem isRelativelyAmple_sum {ι : Type*} [Fintype ι] [Nonempty ι] {f : X ⟶ Y}
    {A : ι → RDivisor X} (hA : ∀ i, IsRelativelyAmple f (A i)) {w : ι → ℝ} (hw : ∀ i, 0 < w i) :
    IsRelativelyAmple f (∑ i, w i • A i) :=
  Finset.sum_induction_nonempty _ (IsRelativelyAmple f) (fun _ _ => isRelativelyAmple_add')
    Finset.univ_nonempty fun i _ => isRelativelyAmple_smul' (hA i) (hw i)

/-- A `ℚ`-divisor with a relatively ample multiple is relatively ample as a real divisor. -/
private theorem isRelativelyAmple_of_hasRelativelyAmpleMultiple (f : X ⟶ Y) [QuasiCompact f]
    {D : QDivisor X} (h : D.HasRelativelyAmpleMultiple f) :
    IsRelativelyAmple f (QDivisor.toRDivisor D) := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  haveI := hL.isInvertibleModule_divisorialSheaf
  refine ⟨1, fun _ => (m : ℝ)⁻¹, fun _ => L, le_rfl, fun _ => by positivity, fun _ => ⟨hL,
    fun U hU => (Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f _
      inferInstance hamp).2 U hU⟩, ?_⟩
  rw [Fin.sum_univ_one, ← QDivisor.toRDivisor_toQDivisor, hLD, map_zsmul,
    ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hmR, one_smul]

end Ample

/-! ### The contraction over the base -/

section Contraction

variable {X S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X]

private theorem relativeToAbsolute_injective (g : X ⟶ S) :
    Function.Injective (relativeToAbsolute sX g) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX g x
  change OneCycle.numericalClass sX (Z : OneCycle ℝ sX) = 0 at hx
  rw [OneCycle.numericalClass, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  exact (Submodule.Quotient.mk_eq_zero _).mpr (mem_relativeNumericallyTrivial.mpr hx)

/-- The degree of a pull-back from the base vanishes on `N₁(X/S)`. -/
private theorem relativeDegree_pullback_eq_zero {sS : S ⟶ Spec (.of ℂ)} [IsSeparated sS]
    [LocallyOfFiniteType sS] (g : X ⟶ S) (hg : g ≫ sS = sX) (A : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    (u : RelativeNumericalCurveClasses sX g) :
    RelativeNumericalCurveClasses.degree sX g ((Scheme.Modules.pullback g).obj A) u = 0 := by
  obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX g u
  rw [RelativeNumericalCurveClasses.degree_relativeNumericalClass]
  simp only [OneCycle.degree, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_eq_zero fun C hC => ?_
  rw [ProperCurve.degree_pullback_eq_zero_of_isContractedBy g hg C
    (hZ (Finset.mem_coe.mpr hC)) A]
  simp

/-- A curve whose class lies in the image of `N₁(X/S)` is contracted by `g`. -/
private theorem isContractedBy_of_mem_range {sS : S ⟶ Spec (.of ℂ)}
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (g : X ⟶ S) (hg : g ≫ sS = sX) (C : ProperCurve sX)
    {u : RelativeNumericalCurveClasses sX g}
    (hu : relativeToAbsolute sX g u = OneCycle.numericalClass sX (C.cycle ℝ)) :
    C.IsContractedBy g := by
  obtain ⟨A, hAinv, hA⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hS
  haveI := hS.toIsVariety.toIsSeparated
  haveI := hS.toIsVariety.toLocallyOfFiniteType
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero g hg A hA C ?_
  have h1 := relativeDegree_pullback_eq_zero g hg A u
  have h2 : NumericalCurveClasses.degree sX ((Scheme.Modules.pullback g).obj A)
      (relativeToAbsolute sX g u) =
        RelativeNumericalCurveClasses.degree sX g ((Scheme.Modules.pullback g).obj A) u := by
    obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX g u
    rfl
  rw [hu, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, h1] at h2
  exact_mod_cast h2

/-- The relative Picard number of the contraction of the ray spanned by a curve of nonzero class
is one: the divisors numerically trivial over the target are the kernel of `D ↦ (D · C)`, a
nonzero linear form. -/
private theorem relativePicardNumber_eq_one_of_isContractionOfRay [IsIntegral X]
    {V : Scheme.{0}} {sV : V ⟶ Spec (.of ℂ)} {q : X ⟶ V} {C : ProperCurve sX}
    (hq : MMP.Fourfold.IsContractionOfRay sX sV
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (C.cycle ℝ) = w} q)
    (hC : OneCycle.numericalClass sX (C.cycle ℝ) ≠ 0) :
    MMP.Flips.relativePicardNumber sX q = 1 := by
  set ψ := (OneCycle.intersectionPairing (sX := sX)).flip (C.cycle ℝ)
  have hker : MMP.Flips.relativeNumericallyTrivialDivisors sX q = LinearMap.ker ψ := by
    ext D'
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors, LinearMap.mem_ker]
    refine ⟨fun h => h C ((hq.isContractedBy_iff C).mpr ⟨1, zero_le_one, one_smul _ _⟩),
      fun h C' hC' => ?_⟩
    obtain ⟨c, -, hc⟩ := (hq.isContractedBy_iff C').mp hC'
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, ← hc, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, smul_eq_mul]
    change c * ψ D' = 0
    rw [h, mul_zero]
  have hne : (MMP.Fourfold.numericalPairing sX).flip (OneCycle.numericalClass sX (C.cycle ℝ))
      ≠ 0 := fun h0 =>
    hC (MMP.Fourfold.numericalPairing_flip_injective sX (h0.trans (map_zero _).symm))
  obtain ⟨d, hd⟩ := not_forall.mp fun h => hne (LinearMap.ext h)
  obtain ⟨D', rfl⟩ := Submodule.mkQ_surjective _ d
  replace hd : ψ D' ≠ 0 := hd
  have hsurj : Function.Surjective ψ := fun r =>
    ⟨(r / ψ D') • D', by rw [map_smul, smul_eq_mul, div_mul_cancel₀ r hd]⟩
  unfold MMP.Flips.relativePicardNumber MMP.Flips.RelativeNumericalDivisorClasses
  rw [hker, (LinearMap.quotKerEquivOfSurjective ψ hsurj).rank_eq, Module.rank_self]
  simp

variable [QuasiCompact sX]

private theorem curveForm_apply (D : QDivisor X) (hD : D.IsQCartier)
    (u : NumericalCurveClasses sX) :
    QDivisor.curveForm sX D hD u = ((D.associatedCartier hD).sum fun E c =>
      haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
      (c : ℝ) * NumericalCurveClasses.degree sX (E : Divisor X).divisorialSheaf u) := by
  simp only [QDivisor.curveForm, Finsupp.sum, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]

/-- **Negativity is an open condition on the boundary.** Every rational boundary whose
coefficients are close enough to those of `B` in a fixed support keeps `K + Δ` negative on a
class on which `K + B` is negative. -/
private theorem curveForm_neg_of_close (hXQ : IsQFactorial sX) {K : Divisor X} {B : RDivisor X}
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hKB : logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j))
    (s : Finset (MMP.Mori.PrimeDivisor X)) (v : NumericalCurveClasses sX)
    (hv : presDeg sX r L hL v < 0) :
    ∃ η > 0, ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Δ : QDivisor X), (∀ P, |c P| < η) →
      QDivisor.toRDivisor Δ = B + ∑ P ∈ s, c P • Divisor.toRDivisor (Finsupp.single P 1) →
      ∀ hQ : (Divisor.toQDivisor K + Δ).IsQCartier,
        QDivisor.curveForm sX (Divisor.toQDivisor K + Δ) hQ v < 0 := by
  set M : ℝ := ∑ P ∈ s, |primeDeg hXQ v P| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨-presDeg sX r L hL v / (2 * (M + 1)), div_pos (by linarith) (by positivity),
    fun c Δ hc hΔ hQ => ?_⟩
  set η := -presDeg sX r L hL v / (2 * (M + 1)) with hη
  rw [curveForm_eq_add hXQ hL hKB s c hΔ hQ v]
  have hsum : |∑ P ∈ s, c P * primeDeg hXQ v P| ≤ η * M := by
    rw [hM, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun P _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hc P).le (abs_nonneg _)
  have hηM : η * M < -presDeg sX r L hL v := by
    rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith [le_abs_self (∑ P ∈ s, c P * primeDeg hXQ v P)]

end Contraction

/-! ### Descent of divisors null on the ray -/

section Descent

variable {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [CompactSpace X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- The degree of an invertible sheaf along a proper curve only depends on the class of the curve
in `N₁(X)`, linearly. -/
private theorem degree_eq_mul_of_smul_numericalClass (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {C C' : ProperCurve sX} {c : ℝ}
    (h : c • OneCycle.numericalClass sX (C.cycle ℝ) = OneCycle.numericalClass sX (C'.cycle ℝ)) :
    (C'.degree ℂ L : ℝ) = c * C.degree ℂ L := by
  rw [← OneCycle.degree_cycle ℝ L C', ← NumericalCurveClasses.degree_numericalClass, ← h,
    map_smul, NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle, smul_eq_mul]

/-- An invertible module on an integral, locally Noetherian, normal, quasi-compact scheme is the
divisorial sheaf of a Cartier divisor (the divisor of a local frame). -/
private theorem exists_isCartier_divisorialSheaf_iso' [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] (L : Z.Modules)
    [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    ∃ M : Divisor Z, M.IsCartier ∧ Nonempty (M.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Z.toRingedSpace) L
  have : ∀ z : Z.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Z.toRingedSpace z) :=
    fun z => Z.isLocalRing z
  choose W hW a ha using fun z : Z =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Z.toRingedSpace) L z
  obtain ⟨z₀⟩ : Nonempty Z := inferInstance
  let F : MMP.Mori.LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun z V hV => ha z V hV, base := z₀ }
  exact ⟨F.divisor, fun z => ⟨F.W z, F.mem z, _, F.isLocalEquation_divisor z⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- **Exact descent along a birational contraction.** If `f : X ⟶ Z` is proper birational onto a
normal variety and `𝒪_X(E) ≅ f^* L`, then `E = f^* M` for a Cartier divisor `M` on `Z`: `E` is
linearly equivalent to the pull-back of a divisor of `L`, and the principal correction descends
because `k(X) = k(Z)`. -/
private theorem exists_isPullback_of_iso_pullback [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [CompactSpace Z] {f : X ⟶ Z} (hf : IsBirationalMorphism f) {E : Divisor X}
    (L : Z.Modules) [SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L]
    (e : E.divisorialSheaf ≅ (Scheme.Modules.pullback f).obj L) :
    ∃ (M : Divisor Z) (_ : M.IsCartier)
      (hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp),
      M.IsPullback f hB E := by
  have : IsDominant f := hf.isDominant
  obtain ⟨M, hM, ⟨eM⟩⟩ := exists_isCartier_divisorialSheaf_iso' L
  have hB := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f M
  obtain ⟨eP⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hM f hB
  obtain ⟨φ, hφ⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback f).mapIso eM.symm ≪≫ eP.symm)
  obtain ⟨ψ, hψ, rfl⟩ := MMP.Fourfold.exists_pullbackRationalFunction_eq hf φ
  have hB' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f
    (M + principalDivisor ψ)
  refine ⟨M + principalDivisor ψ, hM.add (Divisor.isCartier_principalDivisor ψ), hB', ?_⟩
  have h3 := Divisor.IsPullback.add hM (Divisor.isCartier_principalDivisor ψ) hB'
    (Divisor.isPullback_pullback hM hB) (Divisor.isPullback_principalDivisor ψ hψ)
  have hsum : M.pullback hM hB + (E - M.pullback hM hB) = E := by abel
  rw [← hφ, hsum] at h3
  exact h3

/-- The degree of a Cartier divisor along a curve is the value of any presentation of it. -/
private theorem degreeOn_eq_presDeg [QuasiCompact sX] {E : Divisor X} (hE : E.IsCartier) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (h : Divisor.toRDivisor E = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    (E.degreeOn ℂ sX C.ι C.dim_le hE : ℝ) =
      presDeg sX r L hL (OneCycle.numericalClass sX (C.cycle ℝ)) := by
  have h1 := presDeg_congr (sX := sX) (r := fun _ : Fin 1 => (1 : ℝ)) (L := fun _ => E)
    (r' := r) (L' := L) (fun _ => hE) hL (by simp [h])
  rw [← h1, presDeg_numericalClass_cycle]
  simp

variable [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]

/-- **Integral descent.** A Cartier divisor of degree zero on a curve `T` spanning the contracted
ray descends through the birational contraction: its sheaf is a pull-back by the contraction
theorem for the klt witness, and the descent is exact. -/
private theorem exists_isPullback_of_degreeOn_eq_zero [QuasiCompact sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {Δ₀ : QDivisor X} (hklt : IsKltPair sX Δ₀)
    {R' : Set (NumericalCurveClasses sX)}
    (hΔ₀ : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ₀) R') {T : ProperCurve sX}
    (hRT : R' = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w})
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z}
    (hf : IsContractionOfRay sX sZ R' f) (hbir : IsBirationalMorphism f) {E : Divisor X}
    (hE : E.IsCartier) (h0 : E.degreeOn ℂ sX T.ι T.dim_le hE = 0) :
    ∃ (M : Divisor Z) (_ : M.IsCartier)
      (hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp),
      M.IsPullback f hB E := by
  have hP := hklt.1
  haveI := hP.isAlgClosed
  haveI := hP.charZero
  have hkm : MMP.Mori.IsKltPair sX n K Δ₀ :=
    (MMP.Fourfold.isKltPair_iff_mori_isKltPair sX hK hP).mp hklt
  have hΔ : Δ₀.IsEffective := fun P => hP.nonneg P
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI := hE.isInvertibleModule_divisorialSheaf
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isContractionOfFace hkm hΔ (F := R')
    ⟨hΔ₀.2.1.1, hΔ₀.2.1.1.2.2.1, hΔ₀.2.2⟩
    ⟨hX, hZ, hf.comp_eq, hΔ₀.2.1.1, hf.isContractedBy_iff, hf.isIso_app⟩ E.divisorialSheaf
    (fun C hC => by
      rw [hRT] at hC
      obtain ⟨c, -, hc⟩ := hC
      have h1 := degree_eq_mul_of_smul_numericalClass E.divisorialSheaf hc
      have h2 : T.degree ℂ E.divisorialSheaf = 0 := h0
      have h3 : ((C.degree ℂ E.divisorialSheaf : ℤ) : ℝ) = 0 := by rw [h1, h2]; simp
      exact_mod_cast h3)
  haveI := hM
  exact exists_isPullback_of_iso_pullback hbir M e

/-- **Real descent.** An `ℝ`-Cartier divisor null on `T` is a real combination of Cartier
divisors which are null on `T`, each of which descends exactly. -/
private theorem exists_pullback_presentation_of_null [QuasiCompact sX]
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {Δ₀ : QDivisor X} (hklt : IsKltPair sX Δ₀)
    {R' : Set (NumericalCurveClasses sX)}
    (hΔ₀ : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ₀) R') {T : ProperCurve sX}
    (hRT : R' = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w})
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) {f : X ⟶ Z}
    (hf : IsContractionOfRay sX sZ R' f) (hbir : IsBirationalMorphism f) {N : RDivisor X}
    (hN : IsCartierCombination N)
    (hN0 : ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX N r L T x → x = 0) :
    ∃ (k : ℕ) (c : Fin k → ℝ) (E : Fin k → Divisor X) (M : Fin k → Divisor Z),
      (∀ i, (E i).IsCartier) ∧ (∀ i, (M i).IsCartier) ∧
      (∀ i, ∃ hB, (M i).IsPullback f hB (E i)) ∧ N = ∑ i, c i • Divisor.toRDivisor (E i) := by
  classical
  obtain ⟨m, r, L, hL, hNL⟩ := hN
  simp only [← toRDivisor_eq_mapCoeffs] at hNL
  set d : Fin m → ℤ := fun j => (L j).degreeOn ℂ sX T.ι T.dim_le (hL j) with hd
  have hsum : ∑ j, r j * (d j : ℝ) = 0 :=
    hN0 m r L _ ⟨hL, d, hNL,
      fun j => MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sX T (L j) (hL j),
      rfl⟩
  -- every integral combination of degree zero on `T` descends
  have hdesc : ∀ (E : Divisor X) (hE : E.IsCartier), E.degreeOn ℂ sX T.ι T.dim_le hE = 0 →
      ∃ M : Divisor Z, M.IsCartier ∧ ∃ hB, M.IsPullback f hB E := fun E hE h0 => by
    obtain ⟨M, hM, hB, hMp⟩ :=
      exists_isPullback_of_degreeOn_eq_zero hX hK hklt hΔ₀ hRT hZ hf hbir hE h0
    exact ⟨M, hM, hB, hMp⟩
  by_cases hd0 : ∀ j, d j = 0
  · choose M hM hMp using fun j => hdesc (L j) (hL j) (hd0 j)
    exact ⟨m, r, L, M, hL, hM, hMp, hNL⟩
  · push Not at hd0
    obtain ⟨j₀, hj₀⟩ := hd0
    set E : Fin m → Divisor X := fun j => d j₀ • L j - d j • L j₀ with hE
    have hEc : ∀ j, (E j).IsCartier := fun j => ((hL j).zsmul _).sub ((hL j₀).zsmul _)
    have hEpres : ∀ j, Divisor.toRDivisor (E j) = ∑ i, ((if i = j then (d j₀ : ℝ) else 0) -
        if i = j₀ then (d j : ℝ) else 0) • Divisor.toRDivisor (L i) := fun j => by
      simp only [hE, map_sub, map_zsmul, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Int.cast_smul_eq_zsmul ℝ]
    have hE0 : ∀ j, (E j).degreeOn ℂ sX T.ι T.dim_le (hEc j) = 0 := fun j => by
      have h1 := degreeOn_eq_presDeg (hEc j) _ L hL (hEpres j) T
      rw [presDeg_numericalClass_cycle] at h1
      simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h1
      have : (((E j).degreeOn ℂ sX T.ι T.dim_le (hEc j) : ℤ) : ℝ) = 0 := by
        rw [h1]; change (d j₀ : ℝ) * d j - d j * d j₀ = 0; ring
      exact_mod_cast this
    choose M hM hMp using fun j => hdesc (E j) (hEc j) (hE0 j)
    have hdj₀ : (d j₀ : ℝ) ≠ 0 := by exact_mod_cast hj₀
    refine ⟨m, fun j => r j / d j₀, E, M, hEc, hM, hMp, ?_⟩
    rw [hNL]
    simp only [hEpres, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp only [mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have h1 : ∑ x, r x / (d j₀ : ℝ) * d x = (∑ x, r x * d x) / d j₀ := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    by_cases hi : i = j₀
    · simp only [hi, eq_self_iff_true, if_true]
      rw [div_mul_cancel₀ _ hdj₀, h1, hsum, zero_div, sub_zero]
    · simp only [hi, if_false, Finset.sum_const_zero, sub_zero]
      exact (div_mul_cancel₀ _ hdj₀).symm

end Descent

/-! ### Points, prime divisors and divisors over the base -/

section Points

open TopologicalSpace

variable {X Y : Scheme.{0}}

/-- A point of coheight at most one does not lie in a closed set of codimension at least two. -/
private theorem notMem_of_coheight_le_one' {T : Scheme.{0}} {W : Closeds T}
    (h2 : 2 ≤ closedsCodimension W) {x : T} (hx : Order.coheight x ≤ 1) : x ∉ W := by
  intro hxW
  have hsub : ((irreducibleSetEquivPoints (α := T)).symm x : Set T) ⊆ W :=
    W.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxW)
  have := le_closedsCodimension_iff.mp h2 _ hsub
  rw [codimension_eq_coheight, Order.coheight_orderIso] at this
  exact absurd (this.trans hx) (by decide)

private theorem apply_ι_morphismRestrict' (f : X ⟶ Y) (V : Y.Opens) (p : (f ⁻¹ᵁ V).toScheme) :
    V.ι ((f ∣_ V) p) = f ((f ⁻¹ᵁ V).ι p) := by
  rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]

private theorem eq_of_apply_eq' (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x₁ x₂ : X}
    (h₁ : f x₁ ∈ V) (h₂ : f x₂ ∈ V) (h : f x₁ = f x₂) : x₁ = x₂ := by
  let p₁ : (f ⁻¹ᵁ V).toScheme := ⟨x₁, h₁⟩
  let p₂ : (f ⁻¹ᵁ V).toScheme := ⟨x₂, h₂⟩
  have : (f ∣_ V) p₁ = (f ∣_ V) p₂ :=
    V.ι.isOpenEmbedding.injective ((apply_ι_morphismRestrict' f V p₁).trans
      (h.trans (apply_ι_morphismRestrict' f V p₂).symm))
  exact congrArg Subtype.val ((f ∣_ V).isOpenEmbedding.injective this)

private theorem exists_apply_eq' (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {y : Y}
    (hy : y ∈ V) : ∃ x, f x = y := by
  let q : V.toScheme := ⟨y, hy⟩
  refine ⟨(f ⁻¹ᵁ V).ι (inv (f ∣_ V) q), ?_⟩
  rw [← apply_ι_morphismRestrict', ← Scheme.Hom.comp_apply (inv (f ∣_ V)) (f ∣_ V),
    IsIso.inv_hom_id]
  rfl

private theorem coheight_apply_eq' (f : X ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {x : X}
    (hx : f x ∈ V) : Order.coheight (f x) = Order.coheight x :=
  MMP.Positivity.coheight_map_of_mem_biregularLocus f
    ((isBiregular_iff_le_biregularLocus.mp ‹IsIso (f ∣_ V)›) hx)

/-- Prime divisors correspond over an open `V` over which `f` and `f⁺` are isomorphisms. -/
private theorem exists_primeDivisor_genericPoint_eq' {X' : Scheme.{0}} (f : X ⟶ Y)
    (fp : X' ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (P' : MMP.Mori.PrimeDivisor X') (hP' : fp P'.genericPoint ∈ V) :
    ∃ P : MMP.Mori.PrimeDivisor X, f P.genericPoint = fp P'.genericPoint := by
  obtain ⟨x, hx⟩ := exists_apply_eq' f V hP'
  have hxV : f x ∈ V := hx ▸ hP'
  have hco : Order.coheight x = 1 := by
    rw [← coheight_apply_eq' f V hxV, hx, coheight_apply_eq' fp V hP',
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco,
    (congrArg f (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco)).trans hx⟩

/-- A divisor over `X` whose centre has its generic point outside an open `U` has its whole
centre outside `U`. -/
private theorem center_subset_compl' {sX : X ⟶ Spec (.of ℂ)} (D : DivisorOver ℂ sX)
    {U : X.Opens} (h : D.f D.E.genericPoint ∉ U) : (D.center : Set X) ⊆ (U : Set X)ᶜ := by
  rw [D.center_eq_closure_genericPoint]
  exact closure_minimal (Set.singleton_subset_iff.mpr h) U.isOpen.isClosed_compl

/-- `U ⊆ X` is smooth over the base exactly when it lies in the smooth locus. -/
private theorem isSmoothScheme_ι_iff {S : Scheme.{0}} (s : X ⟶ S) [LocallyOfFinitePresentation s]
    (U : X.Opens) : MMP.Mori.IsSmoothScheme (U.ι ≫ s) ↔ U ≤ s.smoothLocus := by
  rw [MMP.Mori.IsSmoothScheme, MMP.Mori.smoothLocus_eq_smoothLocus,
    ← Scheme.Hom.preimage_smoothLocus_eq]
  constructor
  · intro h x hx
    have : (⟨x, hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ s.smoothLocus := by rw [h]; trivial
    exact this
  · intro h
    ext x
    simp only [Scheme.Opens.ι_preimage_self, TopologicalSpace.Opens.coe_top, Set.mem_univ,
      iff_true]
    exact h x.2

/-- Smoothness is local on the source. -/
private theorem mem_smoothLocus_iff_of_comp_eq' {T X' S : Scheme.{0}} (ι : T ⟶ X) (j : T ⟶ X')
    [IsOpenImmersion ι] [IsOpenImmersion j] (s : X ⟶ S) (s' : X' ⟶ S)
    [LocallyOfFinitePresentation s] [LocallyOfFinitePresentation s'] (h : j ≫ s' = ι ≫ s)
    (t : T) : j t ∈ s'.smoothLocus ↔ ι t ∈ s.smoothLocus := by
  change t ∈ j ⁻¹ᵁ s'.smoothLocus ↔ t ∈ ι ⁻¹ᵁ s.smoothLocus
  rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.preimage_smoothLocus_eq]
  have key : ∀ (g : T ⟶ S) [LocallyOfFinitePresentation g], g = ι ≫ s →
      (t ∈ g.smoothLocus ↔ t ∈ (ι ≫ s).smoothLocus) := by
    rintro g _ rfl; rfl
  exact key _ h

private theorem isIso_ι_restrict_self' (U : X.Opens) : IsIso (U.ι ∣_ U) := by
  have : Surjective (U.ι ∣_ U) := by
    constructor
    intro y
    let x : (U.ι ⁻¹ᵁ U).toScheme := ⟨y, by simp⟩
    refine ⟨x, U.ι.isOpenEmbedding.injective ?_⟩
    have := Scheme.Hom.comp_apply (U.ι ∣_ U) U.ι x
    rw [morphismRestrict_ι] at this
    exact this.symm
  exact isIso_of_mono_of_strongEpi (U.ι ∣_ U)

open MMP.Threefold.Mori.OpenRestriction in
/-- The inverse transform along the inclusion of an open subscheme is the restriction. -/
private theorem inverseTransformDivisor_ι_eq_comapDomain {R : Type*} [AddCommMonoid R]
    (U : X.Opens) (B : DivisorWithCoeffs R X) :
    inverseTransformDivisor U.ι B = Finsupp.comapDomain
      (OpenWeilRestriction.primeDivisorMap U.ι) B
        (OpenWeilRestriction.primeDivisorMap_injective U.ι).injOn := by
  have hbir : ∀ x : U.toScheme, U.ι x ∈ biregularLocus U.ι := fun x =>
    le_biregularLocus (isIso_ι_restrict_self' U)
      (by rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]; exact ⟨x, rfl⟩)
  refine Finsupp.ext fun W => ?_
  refine (MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (E := OpenWeilRestriction.primeDivisorMap U.ι W)
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      (OpenWeilRestriction.genericPoint_primeDivisorMap U.ι W).symm (hbir _))
    (fun E' hE' => ?_) B).trans rfl
  refine AlgebraicGeometry.PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    (MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some hE').1]

open MMP.Threefold.Mori.OpenRestriction in
/-- **Being snc passes to smaller opens.** -/
private theorem isSNC_comapDomain_of_range_subset' {R : Type*} [Zero R] {V₁ V₂ : Scheme.{0}}
    (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    (j₁ : V₁ ⟶ X) (j₂ : V₂ ⟶ X) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (h : Set.range j₁ ⊆ Set.range j₂) (D : DivisorWithCoeffs R X)
    (hD : DivisorWithCoeffs.IsSNC (j₂ ≫ g)
      (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₂) D
        (OpenWeilRestriction.primeDivisorMap_injective j₂).injOn)) :
    DivisorWithCoeffs.IsSNC (j₁ ≫ g)
      (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₁) D
        (OpenWeilRestriction.primeDivisorMap_injective j₁).injOn) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => ?_⟩
  · have hDE : D (OpenWeilRestriction.primeDivisorMap j₁ E₀) ≠ 0 := by
      have := Finsupp.mem_support_iff.mp hE₀; exact this
    refine (isSmoothScheme_comap_iff j₁ g (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf
      E₀.idealSheaf (idealSheaf_comap_primeDivisorMap j₁ E₀)).mpr ?_
    rintro z ⟨u, hu⟩
    obtain ⟨w, hw⟩ := h ⟨u, hu⟩
    have hEsupp : (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf.subschemeι z ∈
        (OpenWeilRestriction.primeDivisorMap j₁ E₀).support := by
      have hr : (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf.subschemeι z ∈
          Set.range (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf.subschemeι :=
        ⟨z, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι] at hr
    obtain ⟨E', hE'⟩ := exists_primeDivisorMap_eq_of_mem_support j₂
      (OpenWeilRestriction.primeDivisorMap j₁ E₀) w (hw ▸ hEsupp)
    have hE'supp : E' ∈ (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j₂) D
        (OpenWeilRestriction.primeDivisorMap_injective j₂).injOn).support := by
      rw [Finsupp.mem_support_iff]
      change D (OpenWeilRestriction.primeDivisorMap j₂ E') ≠ 0
      rw [hE']; exact hDE
    have hsm := hD.1 E' hE'supp
    exact (isSmoothScheme_comap_iff j₂ g
      (OpenWeilRestriction.primeDivisorMap j₁ E₀).idealSheaf E'.idealSheaf
      (by rw [← hE']; exact idealSheaf_comap_primeDivisorMap _ E')).mp hsm z ⟨w, hw⟩
  · obtain ⟨w, hw⟩ := h ⟨x, rfl⟩
    have h1 : SNCStalk D (j₂ w) := (sncStalk_restrict_iff j₂ D w).mp (hD.2 w)
    rw [hw] at h1
    exact (sncStalk_restrict_iff j₁ D x).mpr h1

end Points

/-! ### Divisors over the source and the flip -/

section DivisorsOver

open AlgebraicGeometry hiding PrimeDivisor
open scoped WithZero

/-- Let `D` be a divisor over an integral scheme `X` and `f : X ⟶ Y` dominant. The valuation of
`D`, read on `k(Y)` through `f`, dominates the local ring of `Y` at `f(x)`, where `x` is the
generic point of the center of `D`. -/
private theorem valuation_comap_dominates' {k : Type} [Field k] {X Y : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (D : DivisorOver k sX) :
    (∀ a : Y.presheaf.stalk (f (D.f D.E.genericPoint)),
      D.valuation.comap (functionFieldMap f) (algebraMap _ Y.functionField a) ≤ 1) ∧
    (∀ a ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk (f (D.f D.E.genericPoint))),
      D.valuation.comap (functionFieldMap f) (algebraMap _ Y.functionField a) < 1) := by
  refine ⟨fun a ↦ ?_, fun a ha ↦ ?_⟩
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    exact MMP.Positivity.DivisorOver.valuation_algebraMap_le_one D _ rfl _
  · rw [Valuation.comap_apply, MMP.Mori.functionFieldMap_algebraMap_stalk]
    refine MMP.Positivity.DivisorOver.valuation_algebraMap_lt_one D _ rfl _ ?_
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu ↦
      (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

/-- Divisors `D` over `X` and `D'` over `X'` whose valuations agree on `k(Y)`, read through
dominant morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y` to a separated `Y`, have the same center
on `Y`. -/
private theorem map_genericPoint_eq_of_valuation_comap_eq' {k : Type} [Field k]
    {X X' Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    (sY : Y ⟶ Spec (.of k)) [IsSeparated sY] [IsIntegral X] [IsIntegral X'] [IsIntegral Y]
    (f : X ⟶ Y) (f' : X' ⟶ Y) [IsDominant f] [IsDominant f'] (D : DivisorOver k sX)
    (D' : DivisorOver k sX')
    (h : D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap f')) :
    f (D.f D.E.genericPoint) = f' (D'.f D'.E.genericPoint) := by
  obtain ⟨h1, h2⟩ := valuation_comap_dominates' f D
  obtain ⟨h1', h2'⟩ := valuation_comap_dominates' f' D'
  rw [← h] at h1' h2'
  exact MMP.Positivity.DivisorOver.eq_of_dominates sY _ h1 h2 h1' h2'

/-- **Divisors over `X⁺` are divisors over `X`.** Let `f : X ⟶ Y` be a proper birational
morphism from a normal variety and `f⁺ : X⁺ ⟶ Y` a birational morphism. Every divisor `D⁺` over
`X⁺` has, read on `k(Y)`, the valuation of a divisor `D` over `X`: by the valuative criterion for
`f` the valuation of `D⁺` dominates the local ring of a point of `X`. -/
private theorem exists_divisorOver_valuation_comap_eq' {k : Type} [Field k]
    {X X' Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsIntegral X'] {f : X ⟶ Y}
    {fp : X' ⟶ Y} (hX : IsNormalVariety k (f ≫ sY)) (hf : IsBirationalMorphism f) [IsProper f]
    (hfp : IsBirationalMorphism fp) (D' : DivisorOver k (fp ≫ sY)) :
    haveI : IsIntegral X := hX.1.toIsIntegral
    haveI : IsDominant f := hf.isDominant
    haveI : IsDominant fp := hfp.isDominant
    ∃ D : DivisorOver k (f ≫ sY), IsProper D.f ∧
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsDominant f := hf.isDominant
  have : IsDominant fp := hfp.isDominant
  have hbX := hf.functionFieldMap_bijective
  let e : Y.functionField ≃+* X.functionField := RingEquiv.ofBijective (functionFieldMap f) hbX
  set ξY : Valuation Y.functionField ℤᵐ⁰ := D'.valuation.comap (functionFieldMap fp) with hξY
  let ξ : Valuation X.functionField ℤᵐ⁰ := ξY.comap (e.symm : X.functionField →+* Y.functionField)
  have hξ : ξ.comap (functionFieldMap f) = ξY := by
    ext t
    change ξY (e.symm (functionFieldMap f t)) = ξY t
    rw [show e.symm (functionFieldMap f t) = t from e.symm_apply_apply t]
  obtain ⟨hz1, -⟩ := valuation_comap_dominates' fp D'
  -- `ξ` dominates the local ring of a point of `X` (valuative criterion for `f`)
  obtain ⟨x, h1, h2⟩ : ∃ x : X, (∀ a : X.presheaf.stalk x,
      ξ (algebraMap _ X.functionField a) ≤ 1) ∧
      ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
        ξ (algebraMap _ X.functionField a) < 1 := by
    set z := fp (D'.f D'.E.genericPoint)
    have hw : ∀ b : Y.presheaf.stalk z,
        ξ (functionFieldMap f (algebraMap _ Y.functionField b)) =
          ξY (algebraMap _ Y.functionField b) := by
      intro b
      have := congrArg (fun v => v (algebraMap _ Y.functionField b)) hξ
      simpa only [Valuation.comap_apply] using this
    let R := ξ.valuationSubring
    let φ : Y.presheaf.stalk z →+* R :=
      ((functionFieldMap f).comp (algebraMap (Y.presheaf.stalk z) Y.functionField)).codRestrict R
        fun b => (ξ.mem_valuationSubring_iff _).2 (by
          rw [RingHom.comp_apply, hw]
          exact hz1 b)
    have hgen : genericPoint Y ⤳ z := (genericPoint_spec Y).specializes trivial
    have hex : ValuativeCriterion.Existence f := by
      have h : @IsProper _ _ f := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1.existence
    let S : ValuativeCommSq f :=
      { R := R
        K := X.functionField
        i₁ := X.fromSpecStalk (genericPoint X)
        i₂ := Spec.map (CommRingCat.ofHom φ) ≫ Y.fromSpecStalk z
        commSq := ⟨by
          rw [← functionFieldMap_fromSpecStalk f,
            ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hgen, ← Category.assoc,
            ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
          rfl⟩ }
    obtain ⟨⟨l, hl₁, -⟩⟩ := (hex S).exists_lift
    have hl₁' : Spec.map (CommRingCat.ofHom (algebraMap R X.functionField)) ≫ l =
        X.fromSpecStalk (genericPoint X) := hl₁
    set x := l (IsLocalRing.closedPoint R)
    have hx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
    let g := Scheme.stalkClosedPointTo l
    have hg : g ≫ CommRingCat.ofHom (algebraMap R X.functionField) =
        X.presheaf.stalkSpecializes hx := by
      apply Spec.map_injective
      apply (cancel_mono (X.fromSpecStalk x)).mp
      rw [Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁',
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    have hga : ∀ a : X.presheaf.stalk x,
        algebraMap _ X.functionField a = ((g.hom a : R) : X.functionField) := fun a =>
      (congrArg (fun q => q.hom a) hg).symm
    refine ⟨x, fun a => ?_, fun a ha => ?_⟩
    · rw [hga]; exact (g.hom a).2
    · rw [hga]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
        (fun hu => (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit g.hom a hu))
  -- `ξ` is a divisor of `k(X)`: `ord_E` on `D'.Y`, along `k(X) ≅ k(Y) ≅ k(X⁺) ≅ k(D'.Y)`
  have : AlgebraicGeometry.IsVariety k (f ≫ sY) := hX.1
  have hdiv : MMP.Flips.IsDivisorOfFunctionField k (f ≫ sY) ξ := by
    have := D'.isIntegral
    have := D'.isNormal
    have := D'.isLocallyNoetherian
    have := D'.isDominant
    refine ⟨D'.Y, D'.f ≫ fp ≫ sY, D'.isNormalVariety, D'.E, ?_⟩
    let := MMP.Mori.functionFieldAlgebra sY
    let := MMP.Mori.functionFieldAlgebra (f ≫ sY)
    let := MMP.Mori.functionFieldAlgebra (fp ≫ sY)
    let := MMP.Mori.functionFieldAlgebra (D'.f ≫ fp ≫ sY)
    let eX := MMP.Mori.functionFieldAlgEquiv sY f hbX
    let eX' := MMP.Mori.functionFieldAlgEquiv sY fp hfp.functionFieldMap_bijective
    let eY := MMP.Mori.functionFieldAlgEquiv (fp ≫ sY) D'.f
      D'.isBirationalMorphism.functionFieldMap_bijective
    refine ⟨eX.symm.trans (eX'.trans eY), ?_⟩
    ext t
    obtain ⟨s, rfl⟩ := hbX.2 t
    have h1 : eX.symm (functionFieldMap f s) = s := eX.symm_apply_apply s
    change ξY (e.symm (functionFieldMap f s)) =
      D'.E.divisorialValuation (eY (eX' (eX.symm (functionFieldMap f s))))
    rw [h1, show e.symm (functionFieldMap f s) = s from e.symm_apply_apply s]
    rfl
  obtain ⟨D, -, hv, -⟩ :=
    MMP.Flips.exists_properDivisorOver_isProjective_of_dominates (f ≫ sY) hdiv x h1 h2
  refine ⟨D.toDivisorOver, D.isProper, ?_⟩
  change D.valuation.comap _ = _
  rw [hv, hξ]

end DivisorsOver

/-! ### Real dlt and lc pairs across an isomorphism in codimension one -/

section Transfer

open TopologicalSpace

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- The log discrepancy of a prime divisor `P` of `X` with respect to a real boundary `B` is
`1 - b_P`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor_real (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX P)
      (1 - B.coeff P) := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  choose C' hC' using fun j => (hC j).exists_isPullback (f := 𝟙 X)
    (MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' (𝟙 X) (C j))
  have hcoeff : ∀ j, (C' j).coeff P = (C j).coeff P := fun j =>
    MMP.Positivity.coeff_eq_of_isPullback P P rfl (hC j) (hC' j)
  refine ⟨hX, (inferInstance : IsProper (𝟙 X)), ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C,
    C', hC, fun Γ => ?_, fun j => ⟨_, hC' j⟩, ?_⟩
  · rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
  · have h1 := DivisorOver.ordPullback_ofPrimeDivisor hX hn P ω
    change _ = 1 + ((DivisorOver.ofPrimeDivisor ℂ hX P).ordPullback ω : ℝ) -
      ∑ i, r i * ((C' i).coeff P : ℝ)
    rw [h1, hω P]
    simp only [hcoeff]
    rw [← hsum P, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor]
    ring

variable {X' Z : Scheme.{0}} {sX' : X' ⟶ Spec (.of ℂ)} [IsIntegral X'] [IsLocallyNoetherian X']
  [IsNormal X'] [CompactSpace X'] {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral Z]

open MMP.Threefold.Mori.OpenRestriction in
/-- **Real dlt pairs across an isomorphism in codimension one.** Let `f : X ⟶ Z` and
`f⁺ : X⁺ ⟶ Z` be proper birational, isomorphisms over an open `V ⊆ Z` over which lie the points
of codimension at most one of `X⁺`, and let `(X, B)` be dlt with real boundary. Let `B⁺` be a real
divisor on `X⁺` with the coefficients of `B` at corresponding prime divisors and `K⁺ + B⁺`
`ℝ`-Cartier. If the log discrepancies of `(X⁺, B⁺)` along divisors exceptional over `X⁺` are at
least those of `(X, B)` along divisors with the same valuation, strictly so over `Z ∖ V`, then
`(X⁺, B⁺)` is dlt. -/
private theorem isRealDltPair_of_comparison (hXv : IsNormalVariety ℂ sX)
    (hX'v : IsNormalVariety ℂ sX') (hZv : IsNormalVariety ℂ sZ) {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hfs : f ≫ sZ = sX) (hfs' : fp ≫ sZ = sX') [IsProper f] [IsProper fp]
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) [IsDominant f] [IsDominant fp]
    (V : Z.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {n : ℕ} {K' : Divisor X'}
    (hK' : K'.IsCanonicalDivisor sX' n) {B : RDivisor X} (hB : IsRealDltPair sX B)
    {B' : RDivisor X'}
    (hcoeff : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      f P.genericPoint = fp P'.genericPoint → B'.coeff P' = B.coeff P)
    (hKB' : RDivisor.IsRCartier (Divisor.toRDivisor K' + B'))
    (hexB : ∀ D : DivisorOver ℂ sX, IsProper D.f →
      ∃ (n₀ : ℕ) (a : ℝ), MMP.Intersection.IsLogDiscrepancy sX n₀ B D a)
    (hcmp : ∀ (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX'), IsProper D.f → IsProper D'.f →
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) →
      D'.IsExceptional → ∀ (n₀ n₁ : ℕ) (a a' : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n₀ B D a →
        MMP.Intersection.IsLogDiscrepancy sX' n₁ B' D' a' →
        a ≤ a' ∧ (f (D.f D.E.genericPoint) ∉ V → a < a')) :
    IsRealDltPair sX' B' := by
  classical
  obtain ⟨⟨-, hB0, ⟨n₀, K₀, hK₀, hRC₀⟩, hBlc⟩, hB1, Zc, hZsm, hZsnc, hZpos⟩ := hB
  set U : X.Opens := Zc.compl with hUdef
  have : IsNormal Z := hZv.2
  have : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsSeparated sZ := hZv.1.toIsSeparated
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  have hP'V : ∀ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint ∈ V := fun P' =>
    hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
  have hcorr : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
      f P.genericPoint = fp P'.genericPoint := fun P' =>
    exists_primeDivisor_genericPoint_eq' f fp V P' (hP'V P')
  have hprime' : ∀ P', MMP.Intersection.IsLogDiscrepancy sX' n B'
      (DivisorOver.ofPrimeDivisor ℂ hX'v P') (1 - B'.coeff P') := fun P' =>
    isLogDiscrepancy_ofPrimeDivisor_real hX'v hK' hKB' P'
  have hprime : ∀ P, MMP.Intersection.IsLogDiscrepancy sX n₀ B
      (DivisorOver.ofPrimeDivisor ℂ hXv P) (1 - B.coeff P) := fun P =>
    isLogDiscrepancy_ofPrimeDivisor_real hXv hK₀ hRC₀ P
  -- divisors over `X⁺` are divisors over `X`
  have hlift : ∀ D' : DivisorOver ℂ sX', ∃ D : DivisorOver ℂ sX, IsProper D.f ∧
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) := by
    intro D'
    let D'' : DivisorOver ℂ (fp ≫ sZ) :=
      ⟨D'.Y, D'.f, by rw [hfs']; exact D'.isNormalVariety, D'.isBirationalMorphism, D'.E⟩
    obtain ⟨D₀, hD₀p, hv₀⟩ := exists_divisorOver_valuation_comap_eq'
      (show IsNormalVariety ℂ (f ≫ sZ) by rw [hfs]; exact hXv) hf hfp D''
    exact ⟨⟨D₀.Y, D₀.f, by rw [← hfs]; exact D₀.isNormalVariety, D₀.isBirationalMorphism, D₀.E⟩,
      hD₀p, hv₀⟩
  -- the log discrepancy of a divisor over `X⁺` which is a prime divisor of `X⁺`
  have hnonexc : ∀ (n₁ : ℕ) (D' : DivisorOver ℂ sX') (a' : ℝ), ¬ D'.IsExceptional →
      MMP.Intersection.IsLogDiscrepancy sX' n₁ B' D' a' →
      ∃ P' : MMP.Mori.PrimeDivisor X', D'.f D'.E.genericPoint = P'.genericPoint ∧
        a' = 1 - B'.coeff P' := by
    intro n₁ D' a' hE' ha'
    obtain ⟨P', hP'⟩ :=
      MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX'v D' hE'
    exact ⟨P', MMP.Threefold.Mori.ModelIndependence.center_eq_of_valuation_eq hX'v hP',
      MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha' (hprime' P') hP'⟩
  -- the open `U⁺ ⊆ X⁺` corresponding to `U ∩ f⁻¹(V)`
  set S : X.Opens := U ⊓ f ⁻¹ᵁ V with hS
  let j : S.toScheme ⟶ X' :=
    X.homOfLE (inf_le_right : S ≤ f ⁻¹ᵁ V) ≫ (f ∣_ V) ≫ inv (fp ∣_ V) ≫ (fp ⁻¹ᵁ V).ι
  have hj : j ≫ fp = S.ι ≫ f := by
    simp only [j, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, morphismRestrict_ι,
      Scheme.homOfLE_ι_assoc]
  have hjs : j ≫ sX' = S.ι ≫ sX := by
    rw [← hfs', ← hfs, ← Category.assoc, hj, Category.assoc]
  have hjapp : ∀ s : S.toScheme, fp (j s) = f (S.ι s) := fun s =>
    congrArg (fun g => g.base s) hj
  have hjV : ∀ s : S.toScheme, fp (j s) ∈ V := fun s => by
    rw [hjapp]; exact s.2.2
  have hU' : ∀ (x' : X') (z : X), f z ∈ V → f z = fp x' → z ∈ U → x' ∈ j.opensRange := by
    intro x' z hzV hzx hzU
    let s : S.toScheme := ⟨z, hzU, hzV⟩
    refine ⟨s, eq_of_apply_eq' fp V (hjV s) (hzx ▸ hzV) ((hjapp s).trans hzx)⟩
  set Z' : Closeds X' := ⟨(j.opensRange : Set X')ᶜ, j.opensRange.isOpen.isClosed_compl⟩ with hZ'
  have hZ'c : Z'.compl = j.opensRange := by
    ext x
    simp [Z']
  refine ⟨⟨hX'v, fun P' => ?_, ⟨n, K', hK', hKB'⟩, fun n₁ D' a' ha' => ?_⟩, fun P' => ?_, Z', ?_,
    ?_, fun n₁ D' hcen a' ha' => ?_⟩
  · -- the coefficients of `B⁺` are nonnegative
    obtain ⟨P, hP⟩ := hcorr P'
    rw [hcoeff P P' hP]
    exact hB0 P
  · -- `(X⁺, B⁺)` is lc
    by_cases hE' : D'.IsExceptional
    · obtain ⟨D, hDp, hv⟩ := hlift D'
      obtain ⟨n₂, a, ha⟩ := hexB D hDp
      exact (hBlc n₂ D a ha).trans (hcmp D D' hDp ha'.2.1 hv hE' n₂ n₁ a a' ha ha').1
    · obtain ⟨P', -, rfl⟩ := hnonexc n₁ D' a' hE' ha'
      obtain ⟨P, hP⟩ := hcorr P'
      rw [hcoeff P P' hP]
      linarith [hB1 P]
  · -- the coefficients of `B⁺` are at most one
    obtain ⟨P, hP⟩ := hcorr P'
    rw [hcoeff P P' hP]
    exact hB1 P
  · -- `U⁺` is smooth
    rw [hZ'c, isSmoothScheme_ι_iff]
    have hUsm : U ≤ sX.smoothLocus := (isSmoothScheme_ι_iff sX U).mp hZsm
    rintro _ ⟨s, rfl⟩
    exact (mem_smoothLocus_iff_of_comp_eq' S.ι j sX sX' hjs s).2 (hUsm s.2.1)
  · -- `B⁺|_{U⁺}` is snc
    rw [hZ'c, inverseTransformDivisor_ι_eq_comapDomain]
    have hrange : Set.range j.opensRange.ι = Set.range j := by
      rw [Scheme.Opens.range_ι, Scheme.Hom.coe_opensRange]
    refine isSNC_comapDomain_of_range_subset' sX' j.opensRange.ι j hrange.le _ ?_
    have hcomap : Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) B'
        (OpenWeilRestriction.primeDivisorMap_injective j).injOn =
        Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap S.ι) B
          (OpenWeilRestriction.primeDivisorMap_injective S.ι).injOn := by
      refine Finsupp.ext fun E => ?_
      rw [Finsupp.comapDomain_apply, Finsupp.comapDomain_apply]
      refine hcoeff _ _ ?_
      have e1 : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap S.ι E) =
          S.ι E.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
      have e2 : MMP.Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap j E) =
          j E.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
      rw [e1, e2, hjapp]
    rw [hcomap, hjs]
    have hSU : Set.range S.ι ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact fun x hx => hx.1
    have hUsnc := hZsnc
    rw [inverseTransformDivisor_ι_eq_comapDomain] at hUsnc
    exact isSNC_comapDomain_of_range_subset' sX S.ι U.ι hSU B hUsnc
  · -- the log discrepancies of divisors with centre outside `U⁺`
    set x' := D'.f D'.E.genericPoint with hx'
    have hx'U : x' ∉ j.opensRange := fun hx => by
      have hmem : x' ∈ (D'.center : Set X') := by
        rw [D'.center_eq_closure_genericPoint]; exact subset_closure rfl
      exact hcen hmem hx
    have hnotU : ∀ z : X, f z ∈ V → f z = fp x' → z ∉ U := fun z hzV hzx hzU =>
      hx'U (hU' x' z hzV hzx hzU)
    have hZc : ((U : Set X)ᶜ) = (Zc : Set X) := by
      rw [hUdef, Closeds.coe_compl, compl_compl]
    by_cases hE' : D'.IsExceptional
    · obtain ⟨D, hDp, hv⟩ := hlift D'
      obtain ⟨n₂, a, ha⟩ := hexB D hDp
      have hxx' : f (D.f D.E.genericPoint) = fp x' :=
        map_genericPoint_eq_of_valuation_comap_eq' sZ f fp D D' hv
      have hc := hcmp D D' hDp ha'.2.1 hv hE' n₂ n₁ a a' ha ha'
      by_cases hfV : f (D.f D.E.genericPoint) ∈ V
      · have hcen' : (D.center : Set X) ⊆ Zc := by
          rw [← hZc]; exact center_subset_compl' D (hnotU _ hfV hxx')
        exact (hZpos n₂ D hcen' a ha).trans_le hc.1
      · exact (hBlc n₂ D a ha).trans_lt (hc.2 hfV)
    · obtain ⟨P', hx'P', rfl⟩ := hnonexc n₁ D' a' hE' ha'
      obtain ⟨P, hP⟩ := hcorr P'
      rw [hcoeff P P' hP]
      have hPV : f P.genericPoint ∈ V := hP ▸ hP'V P'
      have hcen' : ((DivisorOver.ofPrimeDivisor ℂ hXv P).center : Set X) ⊆ Zc := by
        rw [← hZc]
        exact center_subset_compl' _ (hnotU _ hPV (hP.trans (congrArg fp hx'P').symm))
      exact hZpos n₀ _ hcen' _ (hprime P)

end Transfer

/-! ### Comparison of real log discrepancies through rational boundaries -/

section Comparison

variable {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y]

/-- **Log discrepancies are affine in the boundary.** If the boundaries `B + ∑ⱼ tᵢⱼ Lⱼ`
(`Lⱼ` Cartier) have log discrepancies `bᵢ` along `E` and `∑ᵢ wᵢ tᵢ = 0` with `∑ᵢ wᵢ = 1`, then
the log discrepancy of `B` along `E` is `∑ᵢ wᵢ bᵢ`. -/
private theorem eq_sum_mul_of_isLogDiscrepancy {n n₀ : ℕ} {B : RDivisor Y}
    {E : DivisorOver ℂ sY} {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw1 : ∑ i, w i = 1) {k : ℕ}
    (L : Fin k → Divisor Y) (hL : ∀ j, (L j).IsCartier) (t : ι → Fin k → ℝ)
    (ht : ∀ j, ∑ i, w i * t i j = 0) (b : ι → ℝ)
    (hb : ∀ i, MMP.Intersection.IsLogDiscrepancy sY n
      (B + ∑ j, t i j • Divisor.toRDivisor (L j)) E (b i)) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sY n₀ B E a) : a = ∑ i, w i * b i := by
  choose L' hL' _ using fun j => exists_pullback_divisorOver E (hL j)
  have hb' : ∀ i, b i = a - ∑ j, t i j * ((L' j).coeff E.E : ℝ) := fun i =>
    MMP.Threefold.Bridges.IsLogDiscrepancy.unique (hb i)
      (isLogDiscrepancy_add_sum ha (t i) L hL L' hL')
  have hz : ∑ i, w i * ∑ j, t i j * ((L' j).coeff E.E : ℝ) = 0 := by
    simp only [Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ht, zero_mul, Finset.sum_const_zero]
  simp only [hb', mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, hz, sub_zero]

/-- A positive integer `m` with `m D` Cartier, for a divisor `D` of a `ℚ`-factorial `Y`. -/
private noncomputable def qfIndexD (hYQ : IsQFactorial sY) (D : Divisor Y) : ℕ :=
  (hYQ.2 D).choose

private theorem qfIndexD_pos (hYQ : IsQFactorial sY) (D : Divisor Y) : 0 < qfIndexD hYQ D :=
  (hYQ.2 D).choose_spec.1

private theorem isCartier_qfIndexD (hYQ : IsQFactorial sY) (D : Divisor Y) :
    Divisor.IsCartier (((qfIndexD hYQ D : ℕ) : ℤ) • D) :=
  (hYQ.2 D).choose_spec.2

/-- **Affine combinations in a fixed family of directions.** Let `Bᵢ = B + ∑_{P ∈ s} cᵢ(P) D_P`
for divisors `D_P` on a `ℚ`-factorial `Y`, with `∑ᵢ wᵢ cᵢ(P) = 0` and `∑ᵢ wᵢ = 1`. Then the log
discrepancy of `B` along `E` is the weighted sum of those of the `Bᵢ`. -/
private theorem eq_sum_mul_of_isLogDiscrepancy_of_eq_add {X₀ : Scheme.{0}} (hYQ : IsQFactorial sY)
    {B : RDivisor Y} {ι : Type*} [Fintype ι] {w : ι → ℝ} (hw1 : ∑ i, w i = 1)
    {s : Finset (MMP.Mori.PrimeDivisor X₀)} (Dfam : MMP.Mori.PrimeDivisor X₀ → Divisor Y)
    {c : ι → MMP.Mori.PrimeDivisor X₀ → ℝ} (hc0 : ∀ P ∈ s, ∑ i, w i * c i P = 0)
    {Bi : ι → RDivisor Y}
    (hBi : ∀ i, Bi i = B + ∑ P ∈ s, c i P • Divisor.toRDivisor (Dfam P))
    {E : DivisorOver ℂ sY} {n n₀ : ℕ} {α : ι → ℝ}
    (hα : ∀ i, MMP.Intersection.IsLogDiscrepancy sY n (Bi i) E (α i)) {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sY n₀ B E a) : a = ∑ i, w i * α i := by
  set e := s.equivFin.symm
  set L : Fin s.card → Divisor Y := fun j => ((qfIndexD hYQ (Dfam (e j)) : ℕ) : ℤ) • Dfam (e j)
  have hL : ∀ j, (L j).IsCartier := fun j => isCartier_qfIndexD hYQ _
  set t : ι → Fin s.card → ℝ := fun i j => c i (e j) / (qfIndexD hYQ (Dfam (e j)) : ℝ)
  have hBi' : ∀ i, Bi i = B + ∑ j, t i j • Divisor.toRDivisor (L j) := by
    intro i
    rw [hBi i]
    congr 1
    rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hm : (qfIndexD hYQ (Dfam (e j)) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (qfIndexD_pos hYQ _).ne'
    simp only [t, L, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast]
    rw [div_mul_cancel₀ _ hm]
  refine eq_sum_mul_of_isLogDiscrepancy w hw1 L hL t (fun j => ?_) α
    (fun i => hBi' i ▸ hα i) ha
  simp only [t, mul_div_assoc', ← Finset.sum_div, hc0 _ (e j).2, zero_div]

end Comparison

/-! ### Relative nefness from relative ampleness -/

section Nef

variable {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [CompactSpace X] [IsLocallyNoetherian X]
  [IsNormal X] [QuasiCompact sX]

/-- A `ℚ`-divisor with a relatively ample Cartier multiple is relatively nef. -/
private theorem isRelativelyNef_of_hasRelativelyAmpleMultiple' {f : X ⟶ Y} {D : QDivisor X}
    (h : D.HasRelativelyAmpleMultiple f) : D.IsRelativelyNef sX f := by
  obtain ⟨m, hm, L, hL, hLD, hamp⟩ := h
  have hq : D.IsQCartier := ⟨m, by exact_mod_cast hm.ne', L, hLD, hL⟩
  refine ⟨hq, fun C hC => ?_⟩
  have h1 : ((D.associatedCartier hq).sum fun E c =>
      (c : ℝ) * ((E : Divisor X).degreeOn ℂ sX C.ι C.dim_le E.2 : ℝ)) =
        QDivisor.curveForm sX D hq (OneCycle.numericalClass sX (C.cycle ℝ)) := by
    rw [curveForm_apply]
    refine Finsupp.sum_congr fun E _ => ?_
    haveI := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
    rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]
    rfl
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hpres : QDivisor.toRDivisor D =
      ∑ _j : Fin 1, (m : ℝ)⁻¹ • Divisor.toRDivisor L := by
    rw [Fin.sum_univ_one, ← QDivisor.toRDivisor_toQDivisor, hLD, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℝ, smul_smul, Int.cast_natCast, inv_mul_cancel₀ hmR, one_smul]
  rw [h1, curveForm_eq_presDeg D hq (fun _ => (m : ℝ)⁻¹) (fun _ => L) (fun _ => hL) hpres,
    presDeg_numericalClass_cycle, Fin.sum_univ_one]
  haveI := hL.isInvertibleModule_divisorialSheaf
  have hpos := MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f
    L.divisorialSheaf hamp C hC
  have : (0 : ℝ) ≤ (L.degreeOn ℂ sX C.ι C.dim_le hL : ℝ) := by
    exact_mod_cast hpos.le
  positivity

end Nef

/-! ### Real log discrepancies along the step, from rational ones -/

section RealComparison

open TopologicalSpace

/-- A prime divisor `E` of a normal scheme `W` is exceptional for a morphism `g : W ⟶ T` to a
separated normal scheme exactly when `g(η_E)` has coheight at least two. -/
private theorem isExceptional_toRationalMap_iff_two_le_coheight' {W T : Scheme.{0}}
    [IsLocallyNoetherian W] [IsNormal W] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (T ↘ ⊤_ Scheme)] (g : W ⟶ T) (E : MMP.Mori.PrimeDivisor W) :
    RationalMap.IsExceptional (X := W) g.toRationalMap E ↔
      2 ≤ Order.coheight (g E.genericPoint) := by
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (g '' (E.idealSheaf.support : Set W)) =
      ⟨((IrreducibleCloseds.closureSingleton (g E.genericPoint) : IrreducibleCloseds T) : Set T),
        (IrreducibleCloseds.closureSingleton (g E.genericPoint)).isClosed⟩ := by
    ext1
    change closure (g '' E.support) = closure {g E.genericPoint}
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    refine le_antisymm ?_ (closure_mono ?_)
    · refine closure_minimal ?_ isClosed_closure
      refine (image_closure_subset_closure_image g.continuous).trans ?_
      rw [Set.image_singleton]
    · rw [Set.singleton_subset_iff]
      exact ⟨E.genericPoint, subset_closure rfl, rfl⟩
  rw [hcl, closedsCodimension_coe, codimension_eq_coheight,
    show IrreducibleCloseds.closureSingleton (g E.genericPoint) =
      (irreducibleSetEquivPoints (α := T)).symm (g E.genericPoint) from rfl,
    Order.coheight_orderIso]

private theorem isSeparated_terminal' {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ))
    [IsSeparated sY] : IsSeparated (Y ↘ ⊤_ Scheme) := by
  have : (Y ↘ ⊤_ Scheme) = sY ≫ Limits.terminal.from (Spec (.of ℂ)) := Subsingleton.elim _ _
  rw [this]
  infer_instance

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z]
  [IsLocallyNoetherian Z] [IsNormal Z]

/-- **Comparison of real log discrepancies.** Let `B = ∑ᵢ wᵢ Δᵢ` be a convex combination of
rational boundaries `Δᵢ = B + ∑_P cᵢ(P) P`, transported to `X⁺` as `Δᵢ⁺ = B⁺ + ∑_P cᵢ(P) D_P`, with
`-(K + Δᵢ)` `f`-ample and `K⁺ + Δᵢ⁺` `f⁺`-nef. Then the log discrepancies of `(X⁺, B⁺)` along
divisors exceptional over `X⁺` are at least those of `(X, B)` (Kollár–Mori 3.38 for each `Δᵢ`),
strictly so over points where `f` or (with `K⁺ + Δᵢ⁺` `f⁺`-ample) `f⁺` is not an isomorphism. -/
private theorem real_logDiscrepancy_comparison (hXv : IsNormalVariety ℂ sX)
    (hX'v : IsNormalVariety ℂ sX') (hZv : IsNormalVariety ℂ sZ) {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hfs : f ≫ sZ = sX) (hfs' : fp ≫ sZ = sX') [IsProper f] [IsProper fp]
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) [IsDominant f] [IsDominant fp]
    (hXQ : IsQFactorial sX) (hX'Q : IsQFactorial sX') {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {K' : Divisor X'} (hK' : K'.IsCanonicalDivisor sX' n)
    {B : RDivisor X} {B' : RDivisor X'} {ι : Type} [Fintype ι] [Nonempty ι] {w : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) {s : Finset (MMP.Mori.PrimeDivisor X)}
    {c : ι → MMP.Mori.PrimeDivisor X → ℝ} (hc0 : ∀ P ∈ s, ∑ i, w i * c i P = 0)
    {Δ : ι → QDivisor X}
    (hΔ : ∀ i, QDivisor.toRDivisor (Δ i) =
      B + ∑ P ∈ s, c i P • Divisor.toRDivisor (Finsupp.single P 1))
    (Dfam : MMP.Mori.PrimeDivisor X → Divisor X') {Δ' : ι → QDivisor X'}
    (hΔ' : ∀ i, QDivisor.toRDivisor (Δ' i) = B' + ∑ P ∈ s, c i P • Divisor.toRDivisor (Dfam P))
    (hpush : ∀ i, RationalMap.transformDivisor (X := X) f.toRationalMap (Δ i) =
      RationalMap.transformDivisor (X := X') fp.toRationalMap (Δ' i))
    (hN : ∀ i, (-(Divisor.toQDivisor K + Δ i)).HasRelativelyAmpleMultiple f)
    (hN' : ∀ i, (Divisor.toQDivisor K' + Δ' i).IsRelativelyNef sX' fp) (V : Z.Opens)
    (hV : ∀ z, z ∉ V → z ∉ biregularLocus f ∨ (z ∉ biregularLocus fp ∧
      ∀ i, (Divisor.toQDivisor K' + Δ' i).HasRelativelyAmpleMultiple fp))
    (hexc : ∀ x' : X', 2 ≤ Order.coheight x' → 2 ≤ Order.coheight (fp x'))
    (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX') (hD : IsProper D.f) (hD' : IsProper D'.f)
    (hv : D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp))
    (hE' : D'.IsExceptional) {n₀ n₁ : ℕ} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n₀ B D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sX' n₁ B' D' a') :
    a ≤ a' ∧ (f (D.f D.E.genericPoint) ∉ V → a < a') := by
  have : QuasiCompact sX := hXv.1.toQuasiCompact
  have : QuasiCompact sX' := hX'v.1.toQuasiCompact
  have : IsSeparated sZ := hZv.1.toIsSeparated
  have : IsSeparated sX' := hX'v.1.toIsSeparated
  have := isSeparated_terminal' sZ
  have := isSeparated_terminal' sX'
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isNormal
  have hz : f (D.f D.E.genericPoint) = fp (D'.f D'.E.genericPoint) :=
    map_genericPoint_eq_of_valuation_comap_eq' sZ f fp D D' hv
  -- `D` is exceptional over `Z`
  have hE : RationalMap.IsExceptional (X := D.Y) (D.f ≫ f).toRationalMap D.E := by
    rw [isExceptional_toRationalMap_iff_two_le_coheight', Scheme.Hom.comp_apply, hz]
    exact hexc _ ((isExceptional_toRationalMap_iff_two_le_coheight' D'.f D'.E).mp hE')
  -- the rational log discrepancies
  have hpair : ∀ i, MMP.Mori.IsPair sX (Δ i) := fun i =>
    ⟨hXv, n, K, hK, isQCartier_of_isQFactorial sX hXQ _⟩
  have hpair' : ∀ i, MMP.Mori.IsPair sX' (Δ' i) := fun i =>
    ⟨hX'v, n, K', hK', isQCartier_of_isQFactorial sX' hX'Q _⟩
  choose α hα using fun i => MMP.Positivity.IsPair.exists_isDiscrepancy (hpair i) hK D
  choose α' hα' using fun i => MMP.Positivity.IsPair.exists_isDiscrepancy (hpair' i) hK' D'
  have hlog : ∀ i, MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor (Δ i)) D
      (1 + (α i : ℝ)) := fun i =>
    (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy (hα i) _).mpr ⟨hD, rfl⟩
  have hlog' : ∀ i, MMP.Intersection.IsLogDiscrepancy sX' n (QDivisor.toRDivisor (Δ' i)) D'
      (1 + (α' i : ℝ)) := fun i =>
    (MMP.Threefold.Bridges.isLogDiscrepancy_iff_of_isDiscrepancy (hα' i) _).mpr ⟨hD', rfl⟩
  have h1 : a = ∑ i, w i * (1 + (α i : ℝ)) :=
    eq_sum_mul_of_isLogDiscrepancy_of_eq_add hXQ hw1 (fun P => Finsupp.single P 1) hc0 hΔ hlog ha
  have h2 : a' = ∑ i, w i * (1 + (α' i : ℝ)) :=
    eq_sum_mul_of_isLogDiscrepancy_of_eq_add hX'Q hw1 Dfam hc0 hΔ' hlog' ha'
  have hle : ∀ i, α i ≤ α' i := fun i =>
    MMP.Mori.isDiscrepancy_le_of_isRelativelyNef hXv hX'v hZv hfs hfs' hf hfp hK hK' (hpush i)
      (isRelativelyNef_of_hasRelativelyAmpleMultiple' (hN i)) (hN' i) D D' hv hE (hα i) (hα' i)
  refine ⟨?_, fun hzV => ?_⟩
  · rw [h1, h2]
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw i).le
    have := hle i
    have : (α i : ℝ) ≤ α' i := by exact_mod_cast this
    linarith
  · have hlt : ∀ i, α i < α' i := by
      intro i
      rcases hV _ hzV with h | ⟨h, hA'⟩
      · exact MMP.Mori.isDiscrepancy_lt_of_neg_hasRelativelyAmpleMultiple hXv hX'v hZv hfs hfs' hf
          hfp hK hK' (hpush i) (isRelativelyNef_of_hasRelativelyAmpleMultiple' (hN i)) (hN' i)
          (hN i) D D' hv hE h (hα i) (hα' i)
      · rw [hz] at h
        exact MMP.Mori.isDiscrepancy_lt_of_hasRelativelyAmpleMultiple_target hXv hX'v hZv hfs
          hfs' hf hfp hK hK' (hpush i) (isRelativelyNef_of_hasRelativelyAmpleMultiple' (hN i))
          (hN' i) D D' hv hE (hA' i) h (hα i) (hα' i)
    rw [h1, h2]
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
      mul_lt_mul_of_pos_left ?_ (hw i)
    have := hlt i
    have : (α i : ℝ) < α' i := by exact_mod_cast this
    linarith

end RealComparison

/-! ### Small contractions, flips and their relative Picard numbers -/

section Small

open TopologicalSpace

variable {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- A proper dominant morphism is surjective. -/
private theorem surjective_of_isProper_of_isDominant (f : X ⟶ Z) [IsProper f] [IsDominant f] :
    Function.Surjective f := fun z => by
  have h : z ∈ closure (Set.range f) := by rw [f.denseRange.closure_range]; trivial
  rwa [f.isClosedMap.isClosed_range.closure_eq] at h

/-- Points with an open neighbourhood on which `f` is an open immersion are biregular. -/
private theorem exceptionalSet_subset' (f : X ⟶ Z) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set X) := by
  intro y hy
  by_contra hyM
  apply hy
  have : IsIso (f ∣_ biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ biregularLocus f, ?_, ?_⟩
  · by_contra h
    exact hyM (MMP.Mori.mem_exceptionalSet.mpr h)
  · rw [← morphismRestrict_ι]
    infer_instance

/-- A small contraction in the sense of *Flips and abundance* is a small morphism. -/
private theorem isSmallMorphism_of_isSmall' [IsIntegral X] [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] (hX : IsNormalVariety ℂ sX) (hZ : IsNormalVariety ℂ sZ) {f : X ⟶ Z}
    (hf : MMP.Flips.IsSmall ℂ sZ sX f) : IsSmallMorphism sX sZ f := by
  have hbc := hf.toIsBirationalContraction
  haveI : IsProper f := hbc.isProper
  have hbir := hf.isBirationalMorphism
  have h2 := (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mp hf
  refine ⟨hX, hZ, hbc.comp_eq, hbc.isProper, hbir, ?_⟩
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at h2 ⊢
  intro x hx
  by_contra hlt
  push Not at hlt
  have hxF : x ∉ MMP.Flips.exceptionalSet f := fun h => absurd (h2 x h) (not_le.mpr hlt)
  have hco := MMP.Flips.coheight_map_of_notMem_exceptionalSet hxF
  have hle : Order.coheight (f x) ≤ 1 := by
    rw [hco]; simpa using hlt
  exact (MMP.Mori.mem_exceptionalSet.mp hx)
    (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hbir hle)

/-- A small morphism with `f_* 𝒪_X = 𝒪_Z` is a small contraction. -/
private theorem isSmall_of_isSmallMorphism' {f : X ⟶ Z} (hf : IsSmallMorphism sX sZ f)
    (happ : ∀ U : Z.Opens, IsIso (f.app U)) : MMP.Flips.IsSmall ℂ sZ sX f := by
  haveI := hf.isProper
  haveI := hf.isNormalVariety_target.2
  haveI := hf.isNormalVariety_source.1
  haveI := hf.isNormalVariety_target.1
  have hbc : MMP.Flips.IsBirationalContraction ℂ sZ sX f :=
    { isVariety_target := hf.isNormalVariety_target.1
      isVariety_source := hf.isNormalVariety_source.1
      comp_eq := hf.comp_eq
      isProper := hf.isProper
      isIso_app := happ
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX
        hf.isBirationalMorphism).symm }
  refine (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
  have h2 := hf.two_le_codimension
  rw [MMP.Flips.le_closedsCodimension_iff_le_coheight] at h2 ⊢
  exact fun x hx => h2 x (exceptionalSet_subset' f hx)

/-- No proper curve is contracted by a morphism which is injective on points. -/
private theorem not_isContractedBy_of_injective (f : X ⟶ Z) (hf : Function.Injective f)
    (C : ProperCurve sX) : ¬ C.IsContractedBy f := by
  intro h
  have hsub : ¬ Subsingleton C.scheme := fun _ => by
    have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
    rw [C.dim_eq] at h0
    exact absurd h0 (by decide)
  refine hsub ⟨fun a b => C.ι.isClosedEmbedding.injective (hf ?_)⟩
  have ha : C.ι a ∈ closure ({C.point} : Set X) := by
    rw [← MMP.Chow.DeterminantCurveForm.range_properCurve_ι]; exact ⟨a, rfl⟩
  have hb : C.ι b ∈ closure ({C.point} : Set X) := by
    rw [← MMP.Chow.DeterminantCurveForm.range_properCurve_ι]; exact ⟨b, rfl⟩
  exact (h _ ha).trans (h _ hb).symm

/-- An isomorphism contracts no proper curve. -/
private theorem not_isContractedBy_of_isIso (f : X ⟶ Z) [IsIso f] (C : ProperCurve sX) :
    ¬ C.IsContractedBy f :=
  not_isContractedBy_of_injective f (fun a b h => by
    have := congrArg (inv f).base h
    simpa [← Scheme.Hom.comp_apply] using this) C

/-- A proper morphism with `f_* 𝒪_X = 𝒪_Z` and a point in its exceptional set contracts a
proper curve. -/
private theorem exists_properCurve_isContractedBy_of_mem_exceptionalSet' [IsProper sX]
    [IsLocallyNoetherian X] {g : X ⟶ Z} [IsProper g] (hO : ∀ U : Z.Opens, IsIso (g.app U))
    {x : X} (hx : x ∈ MMP.Mori.exceptionalSet g) :
    ∃ C : ProperCurve sX, C.IsContractedBy g := by
  by_contra hno
  have hlqf : LocallyQuasiFinite g := by
    by_contra h
    exact hno (MMP.Mori.exists_properCurve_isContractedBy_of_not_locallyQuasiFinite h)
  have : IsFinite g := IsFinite.of_isProper_of_locallyQuasiFinite g
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := g x) (U := ⊤) trivial
  have hbir : IsBiregular g U := (isIso_morphismRestrict_iff_isIso_app g hU).mpr (hO U)
  exact hx (le_biregularLocus hbir hxU)

/-- **A contraction whose contracted curves span one line has relative Picard number one.** -/
private theorem relativePicardNumber_eq_one_of_forall_isContractedBy' [IsIntegral X]
    (c : X ⟶ Z) (C₀ : ProperCurve sX) (hC₀ : C₀.IsContractedBy c)
    (hw₀ : OneCycle.numericalClass sX (C₀.cycle ℝ) ≠ 0)
    (hray : ∀ C : ProperCurve sX, C.IsContractedBy c → ∃ t : ℝ,
      t • OneCycle.numericalClass sX (C₀.cycle ℝ) = OneCycle.numericalClass sX (C.cycle ℝ)) :
    MMP.Flips.relativePicardNumber sX c = 1 := by
  set ψ : KCartierDivisor ℝ X →ₗ[ℝ] ℝ := (OneCycle.intersectionPairing (sX := sX)).flip (C₀.cycle ℝ)
  have hψ (B) : ψ B = (C₀.cycle ℝ).intersectionNumber B := rfl
  have hker : MMP.Flips.relativeNumericallyTrivialDivisors sX c = LinearMap.ker ψ := by
    ext B
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors, LinearMap.mem_ker, hψ]
    refine ⟨fun hB => hB C₀ hC₀, fun hB C hC => ?_⟩
    obtain ⟨t, hzt⟩ := hray C hC
    rw [← NumericalCurveClasses.intersectionNumber_numericalClass, ← hzt, map_smul,
      NumericalCurveClasses.intersectionNumber_numericalClass, hB, smul_zero]
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, ψ B₀ ≠ 0 := by
    have hnt : C₀.cycle ℝ ∉ OneCycle.numericallyTrivial sX := fun hmem =>
      hw₀ ((Submodule.Quotient.mk_eq_zero _).mpr hmem)
    rw [OneCycle.mem_numericallyTrivial] at hnt
    push Not at hnt
    obtain ⟨L', hL', hdeg⟩ := hnt
    obtain ⟨E', ⟨e'⟩⟩ := MMP.Fourfold.exists_nonempty_iso_cartierDivisor_sheaf L'
    refine ⟨KCartierDivisor.ofCartier ℝ E', ?_⟩
    rw [hψ, OneCycle.intersectionNumber_ofCartier, OneCycle.cartierDegree, OneCycle.degree_cycle]
    rw [OneCycle.degree_cycle] at hdeg
    rwa [ProperCurve.degree, ← degreeOn_eq_of_iso ℂ sX C₀.ι C₀.dim_le e']
  have hsurj : Function.Surjective ψ := fun y =>
    ⟨(y / ψ B₀) • B₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hB₀]⟩
  have hrank :=
    ((Submodule.quotEquivOfEq _ _ hker).trans (ψ.quotKerEquivOfSurjective hsurj)).lift_rank_eq
  rw [Module.rank_self, Cardinal.lift_one, Cardinal.lift_eq_one] at hrank
  rw [MMP.Flips.relativePicardNumber, hrank, map_one]

/-- A morphism contracting no proper curve has relative Picard number zero. -/
private theorem relativePicardNumber_eq_zero_of_forall_not_isContractedBy (c : X ⟶ Z)
    (h : ∀ C : ProperCurve sX, ¬ C.IsContractedBy c) :
    MMP.Flips.relativePicardNumber sX c = 0 := by
  have htop : MMP.Flips.relativeNumericallyTrivialDivisors sX c = ⊤ := by
    ext B
    simp only [Submodule.mem_top, iff_true]
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors]
    exact fun C hC => absurd hC (h C)
  unfold MMP.Flips.relativePicardNumber MMP.Flips.RelativeNumericalDivisorClasses
  rw [htop]
  simp

end Small

/-! ### Transforms of real divisors -/

section Transforms

variable {X Y X' : Scheme.{0}}

/-- Transforming prime divisors commutes with changing coefficients along an additive map. -/
private theorem mapPrimeDivisors_mapRange {R S : Type*} [AddCommMonoid R] [AddCommMonoid S]
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (c : R →+ S)
    (D : DivisorWithCoeffs R X) :
    DivisorWithCoeffs.mapPrimeDivisors φ (Finsupp.mapRange c (map_zero c) D) =
      Finsupp.mapRange c (map_zero c) (DivisorWithCoeffs.mapPrimeDivisors φ D) := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' =>
    rw [Finsupp.mapRange_add (map_add c), map_add, map_add, h, h',
      Finsupp.mapRange_add (map_add c)]
  | single P r =>
    rw [Finsupp.mapRange_single, DivisorWithCoeffs.mapPrimeDivisors_single,
      DivisorWithCoeffs.mapPrimeDivisors_single]
    cases φ P <;> simp

/-- The flip transform commutes with changing coefficients along an additive map. -/
private theorem flipTransform_mapRange (f : X ⟶ Y) (fp : X' ⟶ Y) {R S : Type*} [AddCommMonoid R]
    [AddCommMonoid S] (c : R →+ S) (D : DivisorWithCoeffs R X) :
    flipTransform f fp (Finsupp.mapRange c (map_zero c) D) =
      Finsupp.mapRange c (map_zero c) (flipTransform f fp D) := by
  simp only [flipTransform, AddMonoidHom.comp_apply, RationalMap.transformDivisor,
    inverseTransformDivisor, mapPrimeDivisors_mapRange]

private theorem flipTransform_toRDivisor (f : X ⟶ Y) (fp : X' ⟶ Y) (D : Divisor X) :
    flipTransform f fp (Divisor.toRDivisor D) = Divisor.toRDivisor (flipTransform f fp D) :=
  flipTransform_mapRange f fp (Int.castAddHom ℝ) D

private theorem flipTransform_qtoRDivisor (f : X ⟶ Y) (fp : X' ⟶ Y) (D : QDivisor X) :
    flipTransform f fp (QDivisor.toRDivisor D) = QDivisor.toRDivisor (flipTransform f fp D) :=
  flipTransform_mapRange f fp (Rat.castHom ℝ).toAddMonoidHom D

private theorem flipTransform_toQDivisor' (f : X ⟶ Y) (fp : X' ⟶ Y) (D : Divisor X) :
    flipTransform f fp (Divisor.toQDivisor D) = Divisor.toQDivisor (flipTransform f fp D) :=
  flipTransform_mapRange f fp (Int.castAddHom ℚ) D

private theorem flipTransform_smul (f : X ⟶ Y) (fp : X' ⟶ Y) (c : ℝ) (D : RDivisor X) :
    flipTransform f fp (c • D) = c • flipTransform f fp D := by
  simp only [flipTransform, AddMonoidHom.coe_comp, Function.comp_apply,
    RationalMap.transformDivisor, inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_smul]

private theorem flipTransform_sum_smul (f : X ⟶ Y) (fp : X' ⟶ Y) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (D : ι → RDivisor X) :
    flipTransform f fp (∑ i ∈ s, c i • D i) = ∑ i ∈ s, c i • flipTransform f fp (D i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => flipTransform_smul f fp (c i) (D i)

/-- The coefficients of `(f⁺)⁻¹_* f_* D` at corresponding prime divisors over an open where both
morphisms are isomorphisms. -/
private theorem flipTransform_apply_of_mem' [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : X ⟶ Y} {fp : X' ⟶ Y} [IsSeparated f]
    [IsDominant f] (hf : IsBirationalMorphism f) (hs : Function.Surjective fp) (V : Y.Opens)
    [IsIso (fp ∣_ V)] {P : MMP.Mori.PrimeDivisor X} {P' : MMP.Mori.PrimeDivisor X'}
    (hPP : f P.genericPoint = fp P'.genericPoint) (hPV : fp P'.genericPoint ∈ V)
    {R : Type*} [AddCommMonoid R] (D : DivisorWithCoeffs R X) :
    flipTransform f fp D P' = D P := by
  have hco : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [coheight_apply_eq' fp V hPV, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
  have hQ : Q.genericPoint = fp P'.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
  haveI := Stacks.AlgebraicGeometry.UnitsNormalProper.isDiscreteValuationRing_stalk
    (show Order.coheight (AlgebraicGeometry.PrimeDivisor.genericPoint Q) = 1 by
      rw [hQ]; exact hco)
  have hbir : Q.genericPoint ∈ biregularLocus fp := by
    rw [hQ]; exact (isBiregular_iff_le_biregularLocus.mp ‹IsIso (fp ∣_ V)›) hPV
  exact MMP.Fourfold.flipTransform_apply_of_map_genericPoint hf.functionFieldMap_bijective hs
    (hPP.trans hQ.symm) hQ.symm hbir D

/-- The push-forward along the identity is the identity. -/
private theorem transformDivisor_id {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (hZ : IsNormalVariety ℂ sZ) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R Z) :
    RationalMap.transformDivisor (X := Z) (Scheme.Hom.toRationalMap (𝟙 Z)) D = D := by
  refine Finsupp.ext fun P => ?_
  obtain ⟨E, heq, -, htr⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ
    (show IsNormalVariety ℂ (𝟙 Z ≫ sZ) by rw [Category.id_comp]; exact hZ)
    (isBirationalMorphism_of_isIso (𝟙 Z)) P
  rw [htr]
  have : E = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective heq
  rw [this]

/-- On a proper birational morphism `g` onto a normal variety, `g_* g⁻¹_* B = B`. -/
private theorem transformDivisor_inverseTransformDivisor' {Z : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) {g : X ⟶ Z}
    (hX : IsNormalVariety ℂ (g ≫ sZ)) [IsProper g] (hg : IsBirationalMorphism g)
    {R : Type*} [AddCommMonoid R] (B : DivisorWithCoeffs R Z) :
    RationalMap.transformDivisor (X := X) g.toRationalMap (inverseTransformDivisor g B) = B := by
  have : IsIntegral Z := hZ.1.toIsIntegral
  have : IsNormal Z := hZ.2
  have : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have : IsIntegral X := hX.1.toIsIntegral
  refine Finsupp.ext fun Q => ?_
  obtain ⟨E, hEQ, -, htr⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply hZ hX hg Q
  rw [htr]
  have hQV : g E.genericPoint ∈ biregularLocus g := by
    rw [hEQ]
    exact MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal g hg
      Q.coheight_genericPoint.le
  refine MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint hEQ hQV)
    (fun Q' hQ' => ?_) B
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    ((MMP.Threefold.Resolution.map_genericPoint_of_inverseTransformPrimeDivisor_eq_some
      hQ').1.symm.trans hEQ)

end Transforms

/-! ### Existence of real log discrepancies and `ℝ`-Cartier divisors -/

section Existence

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] [CompactSpace X]

/-- A real boundary with `K + B` `ℝ`-Cartier has a log discrepancy along every proper divisor over
`X`. -/
private theorem exists_isLogDiscrepancy_real (hX : IsNormalVariety ℂ sX) {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hKB : RDivisor.IsRCartier (Divisor.toRDivisor K + B)) (D : DivisorOver ℂ sX)
    (hD : IsProper D.f) : ∃ a, MMP.Intersection.IsLogDiscrepancy sX n B D a := by
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hX hK
  obtain ⟨m, r, C, hC, hsum⟩ := hKB
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have := D.isNormalVariety.1.toQuasiCompact
  have : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace (D.f ≫ sX)
  choose C' hC' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant D.f (hC i)
  exact ⟨_, hX, hD, ω, hω0, ⟨K, hK, fun Γ => (hω Γ).symm⟩, m, r, C, C', hC, fun Γ => by
    rw [← hsum Γ, hω Γ, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor],
    fun i => ⟨_, hC' i⟩, rfl⟩

/-- On a `ℚ`-factorial variety every real divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isQFactorial (hXQ : IsQFactorial sX) (G : RDivisor X) :
    RDivisor.IsRCartier G := by
  classical
  have hG : G = ∑ P ∈ G.support, G P • Divisor.toRDivisor (Finsupp.single P 1) := by
    ext P
    rw [coeff_sum_smul_single, DivisorWithCoeffs.coeff_apply]
    by_cases hP : P ∈ G.support
    · rw [if_pos hP]
    · rw [if_neg hP, Finsupp.notMem_support_iff.mp hP]
  rw [hG, ← sum_pert hXQ G.support (fun P => G P)]
  refine ⟨G.support.card, pertR hXQ G.support (fun P => G P), pertL hXQ G.support,
    isCartier_pertL hXQ G.support, fun Γ => ?_⟩
  rw [← DivisorWithCoeffs.coeffAddMonoidHom_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- A presentation of `K + B` by Cartier divisors makes it `ℝ`-Cartier. -/
private theorem isRCartier_of_eq_sum {K : Divisor X} {B : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hKB : logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j)) :
    RDivisor.IsRCartier (Divisor.toRDivisor K + B) := by
  refine ⟨m, r, L, hL, fun Γ => ?_⟩
  rw [← logCanonicalDivisor, hKB, ← DivisorWithCoeffs.coeffAddMonoidHom_apply, map_sum]
  simp [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor]

/-- In a convex decomposition `B = ∑ wᵢ Δᵢ` with `Δᵢ = B + ∑_P cᵢ(P) P`, the corrections average to
zero. -/
private theorem sum_mul_eq_zero_of_decomposition {B : RDivisor X} {ι : Type} [Fintype ι]
    {Δ : ι → QDivisor X} {w : ι → ℝ} {c : ι → MMP.Mori.PrimeDivisor X → ℝ}
    {s : Finset (MMP.Mori.PrimeDivisor X)} (hw1 : ∑ i, w i = 1)
    (hwB : ∑ i, w i • QDivisor.toRDivisor (Δ i) = B)
    (hΔc : ∀ i, QDivisor.toRDivisor (Δ i) =
      B + ∑ P ∈ s, c i P • Divisor.toRDivisor (Finsupp.single P 1)) :
    ∀ P ∈ s, ∑ i, w i * c i P = 0 := by
  classical
  intro P hP
  have h := congrArg (fun G : RDivisor X => G.coeff P) hwB
  simp only [hΔc, smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw1, one_smul,
    DivisorWithCoeffs.coeff_add] at h
  have h2 : (∑ i, w i • ∑ P ∈ s, c i P • Divisor.toRDivisor (Finsupp.single P 1)).coeff P =
      ∑ i, w i * c i P := by
    rw [← DivisorWithCoeffs.coeffAddMonoidHom_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [DivisorWithCoeffs.coeffAddMonoidHom_apply, DivisorWithCoeffs.coeff_smul,
      coeff_sum_smul_single, if_pos hP, smul_eq_mul]
  linarith

end Existence

/-! ### The divisorial case -/

section Divisorial

variable {X Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Z] [IsLocallyNoetherian Z]
  [IsNormal Z] [CompactSpace Z]

/-- **The target of a divisorial contraction of a real dlt pair is dlt.** -/
private theorem isRealDltPair_transformDivisor_of_isBirationalMorphism
    (hXn : IsNormalVariety ℂ sX) (hZn : IsNormalVariety ℂ sZ) (hXQ : IsQFactorial sX)
    (hZQ : IsQFactorial sZ) {f : X ⟶ Z} [IsProper f] (hfs : f ≫ sZ = sX)
    (hbir : IsBirationalMorphism f) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (hKZ : Divisor.IsCanonicalDivisor sZ n
      (RationalMap.transformDivisor (X := X) f.toRationalMap K))
    {B : RDivisor X} (hB : IsRealDltPair sX B) {η : ℝ} (hη : 0 < η)
    (hanti : ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Δ : QDivisor X), (∀ P, |c P| < η) →
      QDivisor.toRDivisor Δ = B + ∑ P ∈ B.support, c P • Divisor.toRDivisor (Finsupp.single P 1) →
      (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f) :
    IsRealDltPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B) := by
  classical
  haveI : IsDominant f := hbir.isDominant
  haveI : IsSeparated (f ≫ sZ) := by rw [hfs]; exact hXn.1.toIsSeparated
  haveI : IsSeparated f := IsSeparated.of_comp f sZ
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI := isSeparated_terminal' sZ
  have hid : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
      flipTransform f (𝟙 Z) D = RationalMap.transformDivisor (X := X) f.toRationalMap D :=
    fun D => MMP.Fourfold.inverseTransformDivisor_id _
  set V := biregularLocus f with hV
  haveI : IsIso (f ∣_ V) := MMP.Mori.isBiregular_biregularLocus f
  have hX'V : ∀ z : Z, Order.coheight z ≤ 1 → (𝟙 Z) z ∈ V := fun z hz =>
    MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hbir hz
  have hcoeff : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor Z),
      f P.genericPoint = (𝟙 Z) P'.genericPoint →
        (RationalMap.transformDivisor (X := X) f.toRationalMap B).coeff P' = B.coeff P := by
    intro P P' hPP
    rw [← hid]
    exact flipTransform_apply_of_mem' hbir (Scheme.Hom.surjective (𝟙 Z)) ⊤ hPP trivial B
  obtain ⟨⟨-, -, ⟨n₀, K₀, hK₀, hRC₀⟩, -⟩, -⟩ := id hB
  obtain ⟨ι, _, _, Δ, w, c, hw, hw1, hwB, hc, hΔc⟩ := exists_rat_decomposition B hη
  have hc0 := sum_mul_eq_zero_of_decomposition hw1 hwB hΔc
  refine isRealDltPair_of_comparison hXn hZn hZn hfs (Category.id_comp sZ) hbir
    (isBirationalMorphism_of_isIso _) V hX'V hKZ hB hcoeff
    (isRCartier_of_isQFactorial hZQ _)
    (fun D hD => ⟨n₀, exists_isLogDiscrepancy_real hXn hK₀ hRC₀ D hD⟩)
    (fun D D' hD hD' hv hE' n₁ n₂ a a' ha ha' => ?_)
  refine real_logDiscrepancy_comparison (Δ' := fun i => flipTransform f (𝟙 Z) (Δ i))
    (B' := flipTransform f (𝟙 Z) B) hXn hZn hZn hfs (Category.id_comp sZ) hbir
    (isBirationalMorphism_of_isIso _) hXQ hZQ hK (K' := flipTransform f (𝟙 Z) K)
    (by rw [hid]; exact hKZ) hw hw1 hc0 hΔc
    (fun P => flipTransform f (𝟙 Z) (Finsupp.single P 1)) (fun i => ?_) (fun i => ?_)
    (fun i => hanti _ _ (hc i) (hΔc i)) (fun i => ?_) V (fun z hz => Or.inl hz)
    (fun x' hx' => hx') D D' hD hD' hv hE' ha (by rw [hid]; exact ha')
  · rw [← flipTransform_qtoRDivisor, hΔc i, map_add, flipTransform_sum_smul]
    simp only [flipTransform_toRDivisor]
  · rw [transformDivisor_id hZn, hid]
  · refine ⟨isQCartier_of_isQFactorial sZ hZQ _, fun C hC => absurd hC ?_⟩
    exact not_isContractedBy_of_isIso (𝟙 Z) C

end Divisorial

/-! ### The small case -/

section Flip

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z]
  [IsLocallyNoetherian Z] [IsNormal Z]

/-- The open of `Z` over which both `f` and `f⁺` are isomorphisms contains the images of the
points of codimension at most one of `X⁺`, and `f⁺` preserves "coheight at least two". -/
private theorem flip_open_props {f : X ⟶ Z} {fp : X' ⟶ Z} [IsProper f] [IsProper fp]
    (hbir : IsBirationalMorphism f) (hfp : IsSmallMorphism sX' sZ fp) :
    (∀ x : X', Order.coheight x ≤ 1 → fp x ∈ biregularLocus f ⊓ biregularLocus fp) ∧
      ∀ x : X', 2 ≤ Order.coheight x → 2 ≤ Order.coheight (fp x) := by
  have hbir' := hfp.isBirationalMorphism
  have hfpb : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ biregularLocus fp := fun x hx =>
    not_not.mp fun h => notMem_of_coheight_le_one' hfp.two_le_codimension hx
      (MMP.Mori.mem_exceptionalSet.mpr h)
  refine ⟨fun x hx => ⟨?_, hfpb x hx⟩, fun x hx => ?_⟩
  · refine MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hbir ?_
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hfpb x hx)]
    exact hx
  · by_contra h
    push Not at h
    have h1 : Order.coheight (fp x) ≤ 1 := by simpa using h
    have := MMP.Positivity.coheight_map_of_mem_biregularLocus fp
      (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal fp hbir' h1)
    rw [this] at h1
    exact absurd (hx.trans h1) (by decide)

/-- **The flip of a real dlt pair is dlt.** -/
private theorem isRealDltPair_flipTransform_of_isSmallMorphism (hXn : IsNormalVariety ℂ sX)
    (hX'n : IsNormalVariety ℂ sX') (hZn : IsNormalVariety ℂ sZ) (hXQ : IsQFactorial sX)
    (hX'Q : IsQFactorial sX') {f : X ⟶ Z} {fp : X' ⟶ Z} [IsProper f] [IsProper fp]
    (hfs : f ≫ sZ = sX) (hfs' : fp ≫ sZ = sX') (hbir : IsBirationalMorphism f)
    (hfp : IsSmallMorphism sX' sZ fp) {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (hK' : Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K)) {B : RDivisor X}
    (hB : IsRealDltPair sX B) {η : ℝ} (hη : 0 < η)
    (hanti : ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Δ : QDivisor X), (∀ P, |c P| < η) →
      QDivisor.toRDivisor Δ = B + ∑ P ∈ B.support, c P • Divisor.toRDivisor (Finsupp.single P 1) →
      (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f)
    (hampl : ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Δ : QDivisor X), (∀ P, |c P| < η) →
      QDivisor.toRDivisor Δ = B + ∑ P ∈ B.support, c P • Divisor.toRDivisor (Finsupp.single P 1) →
      (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp Δ).HasRelativelyAmpleMultiple
        fp) :
    IsRealDltPair sX' (flipTransform f fp B) := by
  classical
  have hbir' := hfp.isBirationalMorphism
  haveI : IsDominant f := hbir.isDominant
  haveI : IsDominant fp := hbir'.isDominant
  haveI : Surjective fp := ⟨surjective_of_isProper_of_isDominant fp⟩
  haveI : IsSeparated (f ≫ sZ) := by rw [hfs]; exact hXn.1.toIsSeparated
  haveI : IsSeparated f := IsSeparated.of_comp f sZ
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI := isSeparated_terminal' sZ
  set V := biregularLocus f ⊓ biregularLocus fp with hV
  haveI : IsIso (f ∣_ V) :=
    isBiregular_iff_le_biregularLocus.mpr (inf_le_left : V ≤ biregularLocus f)
  haveI : IsIso (fp ∣_ V) :=
    isBiregular_iff_le_biregularLocus.mpr (inf_le_right : V ≤ biregularLocus fp)
  obtain ⟨hX'V, hexc⟩ := flip_open_props hbir hfp
  have hcoeff : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      f P.genericPoint = fp P'.genericPoint → (flipTransform f fp B).coeff P' = B.coeff P :=
    fun P P' hPP => flipTransform_apply_of_mem' hbir fp.surjective V hPP
      (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le) B
  obtain ⟨⟨-, -, ⟨n₀, K₀, hK₀, hRC₀⟩, -⟩, -⟩ := id hB
  obtain ⟨ι, _, _, Δ, w, c, hw, hw1, hwB, hc, hΔc⟩ := exists_rat_decomposition B hη
  have hc0 := sum_mul_eq_zero_of_decomposition hw1 hwB hΔc
  have hX'n' : IsNormalVariety ℂ (fp ≫ sZ) := by rw [hfs']; exact hX'n
  refine isRealDltPair_of_comparison hXn hX'n hZn hfs hfs' hbir hbir' V hX'V hK' hB hcoeff
    (isRCartier_of_isQFactorial hX'Q _)
    (fun D hD => ⟨n₀, exists_isLogDiscrepancy_real hXn hK₀ hRC₀ D hD⟩)
    (fun D D' hD hD' hv hE' n₁ n₂ a a' ha ha' => ?_)
  refine real_logDiscrepancy_comparison (Δ' := fun i => flipTransform f fp (Δ i))
    hXn hX'n hZn hfs hfs' hbir hbir' hXQ hX'Q hK hK' hw hw1 hc0 hΔc
    (fun P => flipTransform f fp (Finsupp.single P 1)) (fun i => ?_) (fun i => ?_)
    (fun i => hanti _ _ (hc i) (hΔc i))
    (fun i => isRelativelyNef_of_hasRelativelyAmpleMultiple' (hampl _ _ (hc i) (hΔc i))) V
    (fun z hz => ?_) hexc D D' hD hD' hv hE' ha ha'
  · rw [← flipTransform_qtoRDivisor, hΔc i, map_add, flipTransform_sum_smul]
    simp only [flipTransform_toRDivisor]
  · exact (transformDivisor_inverseTransformDivisor' hZn hX'n' hbir' _).symm
  · by_cases h1 : z ∈ biregularLocus f
    · refine Or.inr ⟨fun h2 => hz ⟨h1, h2⟩, fun i => hampl _ _ (hc i) (hΔc i)⟩
    · exact Or.inl h1

end Flip

/-! ### Nefness and pull-backs from the base of the contraction -/

section Nef

variable {X Z S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
  [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]

open Classical in
/-- The degree of the pull-back of a Cartier divisor along a proper curve, by the projection
formula. -/
private theorem degreeOn_isPullback [QuasiCompact sX] [IsSeparated sZ] [LocallyOfFiniteType sZ]
    {f : X ⟶ Z} [IsDominant f] (hfs : f ≫ sZ = sX) {M : Divisor Z} (hM : M.IsCartier)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp}
    {E : Divisor X} (hE : M.IsPullback f hB E) (hEc : E.IsCartier) (C : ProperCurve sX) :
    E.degreeOn ℂ sX C.ι C.dim_le hEc =
      if h : IsProperCurve sZ (f C.point) then
        haveI := ProperCurve.isProper_ι_comp (⟨f C.point, h⟩ : ProperCurve sZ)
        (residueFieldDegree f C.point : ℤ) *
          M.degreeOn ℂ sZ (⟨f C.point, h⟩ : ProperCurve sZ).ι
            (⟨f C.point, h⟩ : ProperCurve sZ).dim_le hM
      else 0 := by
  haveI := hM.isInvertibleModule_divisorialSheaf
  obtain rfl := hE.pullback_eq hM
  haveI := hEc.isInvertibleModule_divisorialSheaf
  obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hM f hB
  have h1 := ProperCurve.degree_pullback f hfs C M.divisorialSheaf
  have h2 : (M.pullback hM hB).degreeOn ℂ sX C.ι C.dim_le hEc =
      C.degree ℂ ((Scheme.Modules.pullback f).obj M.divisorialSheaf) :=
    degreeOn_eq_of_iso ℂ sX C.ι C.dim_le e
  exact h2.trans h1

/-- A Cartier divisor `M` on `Z` whose pull-back `f^* M` along a contraction of a `g`-nef
divisor is nef over `S` relative to `h` with `f ≫ h = g`. -/
private theorem sum_mul_degreeOn_nonneg_of_isRelativelyNef [QuasiCompact sX]
    {f : X ⟶ Z} {g : X ⟶ S} {h : Z ⟶ S} [IsProper f] [Surjective f] (hZn : IsNormalVariety ℂ sZ)
    (hZp : MMP.Mori.IsProjectiveVariety ℂ sZ) (hfs : f ≫ sZ = sX)
    (hfh : f ≫ h = g) {k : ℕ} (c : Fin k → ℝ) (E : Fin k → Divisor X) (M : Fin k → Divisor Z)
    (hEc : ∀ i, (E i).IsCartier) (hMc : ∀ i, (M i).IsCartier)
    (hpb : ∀ i, ∃ hB, (M i).IsPullback f hB (E i))
    (hnef : IsRelativelyNef ℂ sX g (∑ i, c i • Divisor.toRDivisor (E i)))
    (C' : ProperCurve sZ) (hC' : C'.IsContractedBy h) :
    0 ≤ ∑ i, c i * ((M i).degreeOn ℂ sZ C'.ι C'.dim_le (hMc i) : ℝ) := by
  haveI : IsDominant f := inferInstance
  haveI := hZn.1.toIsSeparated
  haveI := hZn.1.toLocallyOfFiniteType
  haveI := hZn.1.toQuasiCompact
  haveI : LocallyOfFiniteType sX := by rw [← hfs]; infer_instance
  obtain ⟨C, hCpt, hCim⟩ := MMP.Mori.ProperCurve.exists_map_eq sX sZ f hfs C'
  -- `C` is contracted by `g`
  have hCg : C.IsContractedBy g := by
    intro x hx
    have hfx : f x ∈ closure ({C'.point} : Set Z) := hCim ▸ ⟨x, hx, rfl⟩
    rw [← hfh, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC' _ hfx, hCpt]
  have hpc : IsProperCurve sZ (f C.point) := hCpt ▸ C'.isProperCurve
  have hC'eq : (⟨f C.point, hpc⟩ : ProperCurve sZ) = C' := by
    cases C'
    simp only [ProperCurve.mk.injEq]
    exact hCpt
  -- the degrees along `C` are those along `C'`, times the degree of `C ⟶ C'`
  have hdeg : ∀ i, ((E i).degreeOn ℂ sX C.ι C.dim_le (hEc i) : ℝ) =
      (residueFieldDegree f C.point : ℝ) * ((M i).degreeOn ℂ sZ C'.ι C'.dim_le (hMc i) : ℝ) := by
    intro i
    obtain ⟨hB, hp⟩ := hpb i
    rw [degreeOn_isPullback hfs (hMc i) hp (hEc i) C, dif_pos hpc, hC'eq]
    push_cast
    ring
  -- the residue degree is positive, since `C` is not contracted by `f`
  have hd : 0 < residueFieldDegree f C.point := by
    by_contra h0
    push Not at h0
    have h0' : residueFieldDegree f C.point = 0 := Nat.le_zero.mp h0
    obtain ⟨A, hAinv, hA⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hZp
    have hcon := MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero f hfs A hA C
      (by rw [ProperCurve.degree_pullback f hfs C A, dif_pos hpc, h0']; simp)
    have hsub : closure ({C'.point} : Set Z) ⊆ {C'.point} := by
      rw [← hCim]
      rintro _ ⟨x, hx, rfl⟩
      rw [hcon x hx, hCpt]; rfl
    have hsing : ¬ Subsingleton C'.scheme := fun _ => by
      have h0 := topologicalKrullDim_zero_of_discreteTopology C'.scheme
      rw [C'.dim_eq] at h0
      exact absurd h0 (by decide)
    refine hsing ⟨fun a b => C'.ι.isClosedEmbedding.injective ?_⟩
    have ha : C'.ι a ∈ closure ({C'.point} : Set Z) := by
      rw [← MMP.Chow.DeterminantCurveForm.range_properCurve_ι]; exact ⟨a, rfl⟩
    have hb : C'.ι b ∈ closure ({C'.point} : Set Z) := by
      rw [← MMP.Chow.DeterminantCurveForm.range_properCurve_ι]; exact ⟨b, rfl⟩
    exact (hsub ha).trans (hsub hb).symm
  -- the intersection number along `C` is nonnegative
  obtain ⟨m', r', L', hL', hEq, hnn⟩ := hnef
  have hx := hnn C hCg _ (isRIntersectionNumber_presDeg r' L' hL' hEq C)
  have hsame := (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r' L' c E _ _
    (isRIntersectionNumber_presDeg r' L' hL' hEq C)
    (isRIntersectionNumber_presDeg c E hEc rfl C)
  rw [hsame, presDeg_numericalClass_cycle] at hx
  simp only [hdeg] at hx
  have hdR : (0 : ℝ) < residueFieldDegree f C.point := by exact_mod_cast hd
  have hre : ∑ i, c i * ((residueFieldDegree f C.point : ℝ) *
      ((M i).degreeOn ℂ sZ C'.ι C'.dim_le (hMc i) : ℝ)) = (residueFieldDegree f C.point : ℝ) *
        ∑ i, c i * ((M i).degreeOn ℂ sZ C'.ι C'.dim_le (hMc i) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hre] at hx
  exact nonneg_of_mul_nonneg_right hx hdR

end Nef

/-! ### Comparison for boundaries numerically trivial on the ray -/

section Crepant

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z]
  [IsLocallyNoetherian Z] [IsNormal Z]

private theorem presDeg_smul [QuasiCompact sX] {m : ℕ} (c : ℝ) (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    presDeg sX (c • r) L hL = c • presDeg sX r L hL := by
  refine LinearMap.ext fun u => ?_
  simp only [presDeg_apply, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc]

/-- A `ℚ`-Cartier `ℚ`-divisor has a presentation by one Cartier divisor. -/
private theorem exists_presentation_of_isQCartier (D : QDivisor X) (hD : D.IsQCartier) :
    ∃ (r : Fin 1 → ℝ) (L : Fin 1 → Divisor X) (hL : ∀ j, (L j).IsCartier),
      QDivisor.toRDivisor D = ∑ j, r j • Divisor.toRDivisor (L j) := by
  set E := D.cartierIndexSMul hD
  have hm : (D.cartierIndex hD : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (QDivisor.cartierIndex_pos hD).ne'
  refine ⟨fun _ => ((D.cartierIndex hD : ℕ) : ℝ)⁻¹, fun _ => (E : Divisor X), fun _ => E.2, ?_⟩
  rw [Fin.sum_univ_one]
  have hE' := QDivisor.toQDivisor_cartierIndexSMul D hD
  ext P
  have := congrArg (fun F : QDivisor X => F.coeff P) hE'
  simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul] at this
  have this' : (((E : Divisor X).coeff P : ℤ) : ℝ) =
      ((D.cartierIndex hD : ℕ) : ℝ) * ((D.coeff P : ℚ) : ℝ) := by exact_mod_cast this
  simp only [DivisorWithCoeffs.coeff_smul, Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor,
    smul_eq_mul]
  rw [this']
  have hm' : ((D.cartierIndex hD : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
  field_simp

open Classical in
/-- **Affine dependence along a segment.** The log discrepancy of `(1 - s) B' + s Δ` is the
corresponding convex combination of those of `B'` and `Δ`, the difference `Δ - B'` being a
combination of the divisors `D_P`. -/
private theorem isLogDiscrepancy_segment {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (hYQ : IsQFactorial sY) {X₀ : Scheme.{0}}
    (S : Finset (MMP.Mori.PrimeDivisor X₀)) (Dfam : MMP.Mori.PrimeDivisor X₀ → Divisor Y)
    (e : MMP.Mori.PrimeDivisor X₀ → ℝ) {B₁ B₂ : RDivisor Y}
    (hB₂ : B₂ = B₁ + ∑ P ∈ S, e P • Divisor.toRDivisor (Dfam P)) (s : ℝ)
    {E : DivisorOver ℂ sY} {n n₀ : ℕ} {a₁ a₂ a : ℝ}
    (h₁ : MMP.Intersection.IsLogDiscrepancy sY n B₁ E a₁)
    (h₂ : MMP.Intersection.IsLogDiscrepancy sY n B₂ E a₂)
    (h : MMP.Intersection.IsLogDiscrepancy sY n₀ ((1 - s) • B₁ + s • B₂) E a) :
    a = (1 - s) * a₁ + s * a₂ := by
  set G := ∑ P ∈ S, e P • Divisor.toRDivisor (Dfam P) with hG
  have hbase : (1 - s) • B₁ + s • B₂ = B₁ + s • G := by rw [hB₂]; module
  have hneg : ∑ P ∈ S, (-(s * e P)) • Divisor.toRDivisor (Dfam P) = (-s) • G := by
    rw [hG, Finset.smul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [smul_smul]
    ring_nf
  have hpos : ∑ P ∈ S, ((1 - s) * e P) • Divisor.toRDivisor (Dfam P) = (1 - s) • G := by
    rw [hG, Finset.smul_sum]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [smul_smul]
  have key := eq_sum_mul_of_isLogDiscrepancy_of_eq_add (ι := Fin 2) (n := n) hYQ
    (w := ![1 - s, s])
    (by simp [Fin.sum_univ_two]) Dfam (c := ![fun P => -(s * e P), fun P => (1 - s) * e P])
    (s := S) (fun P _ => by simp [Fin.sum_univ_two]; ring) (Bi := ![B₁, B₂]) (fun i => ?_)
    (α := ![a₁, a₂]) (fun i => ?_) h
  · simpa [Fin.sum_univ_two] using key
  · fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [hbase, hneg]
      module
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hbase, hpos, hB₂]
      module
  · fin_cases i
    · simpa using h₁
    · simpa using h₂

end Crepant

/-! ### Comparison for boundaries negative on the ray, and their limits -/

section CmpNeg

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z]
  [IsLocallyNoetherian Z] [IsNormal Z]

/-- **Comparison for a real boundary negative on the ray.** -/
private theorem realCmp_of_negative [QuasiCompact sX] (hXv : IsNormalVariety ℂ sX)
    (hX'v : IsNormalVariety ℂ sX') (hZv : IsNormalVariety ℂ sZ) {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hfs : f ≫ sZ = sX) (hfs' : fp ≫ sZ = sX') [IsProper f] [IsProper fp]
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) [IsDominant f] [IsDominant fp]
    (hXQ : IsQFactorial sX) (hX'Q : IsQFactorial sX') {n : ℕ} {K : Divisor X}
    (hK : K.IsCanonicalDivisor sX n)
    (hK' : Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K))
    {R' : Set (NumericalCurveClasses sX)}
    (hR' : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R')
    {v : NumericalCurveClasses sX} (hR'v : R' = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w})
    (hanti : ∀ Δ : QDivisor X, IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R' →
      (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f)
    (hnefp : ∀ Δ : QDivisor X, IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R' →
      (Divisor.toQDivisor (flipTransform f fp K) + flipTransform f fp Δ).IsRelativelyNef sX' fp)
    (hpush : ∀ Δ : QDivisor X, RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
      RationalMap.transformDivisor (X := X') fp.toRationalMap (flipTransform f fp Δ))
    (V : Z.Opens)
    (hV : ∀ z, z ∉ V → z ∉ biregularLocus f ∨ (z ∉ biregularLocus fp ∧
      ∀ Δ : QDivisor X, IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R' →
        (Divisor.toQDivisor (flipTransform f fp K) +
          flipTransform f fp Δ).HasRelativelyAmpleMultiple fp))
    (hexc : ∀ x' : X', 2 ≤ Order.coheight x' → 2 ≤ Order.coheight (fp x'))
    {B : RDivisor X} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hKB : logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j))
    (hv : presDeg sX r L hL v < 0)
    (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX') (hD : IsProper D.f) (hD' : IsProper D'.f)
    (hvD : D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp))
    (hE' : D'.IsExceptional) {n₀ n₁ : ℕ} {a a' : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy sX n₀ B D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sX' n₁ (flipTransform f fp B) D' a') :
    a ≤ a' ∧ (f (D.f D.E.genericPoint) ∉ V → a < a') := by
  classical
  obtain ⟨η, hη, hηneg⟩ := curveForm_neg_of_close hXQ hL hKB B.support v hv
  have hnegΔ : ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Δ : QDivisor X), (∀ P, |c P| < η) →
      QDivisor.toRDivisor Δ = B + ∑ P ∈ B.support, c P • Divisor.toRDivisor (Finsupp.single P 1) →
      IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R' := fun c Δ hc hΔ =>
    isNegativeExtremalRayOf_of_neg (isQCartier_of_isQFactorial sX hXQ _) hR' hR'v
      (hηneg c Δ hc hΔ _)
  obtain ⟨ι, _, _, Δ, w, c, hw, hw1, hwB, hc, hΔc⟩ := exists_rat_decomposition B hη
  have hc0 := sum_mul_eq_zero_of_decomposition hw1 hwB hΔc
  refine real_logDiscrepancy_comparison (Δ' := fun i => flipTransform f fp (Δ i))
    hXv hX'v hZv hfs hfs' hf hfp hXQ hX'Q hK hK' hw hw1 hc0 hΔc
    (fun P => flipTransform f fp (Finsupp.single P 1)) (fun i => ?_) (fun i => hpush _)
    (fun i => hanti _ (hnegΔ _ _ (hc i) (hΔc i)))
    (fun i => hnefp _ (hnegΔ _ _ (hc i) (hΔc i))) V (fun z hz => ?_) hexc D D' hD hD' hvD hE'
    ha ha'
  · rw [← flipTransform_qtoRDivisor, hΔc i, map_add, flipTransform_sum_smul]
    simp only [flipTransform_toRDivisor]
  · rcases hV z hz with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, fun i => h' _ (hnegΔ _ _ (hc i) (hΔc i))⟩

/-- **Comparison in the limit.** If every real boundary negative on the ray satisfies the
comparison, so does a boundary `B'` with `K + B'` null on the ray: approach `B'` along the
segment towards a negative rational boundary `Δ₀`. -/
private theorem le_of_forall_neg [QuasiCompact sX] (hXv : IsNormalVariety ℂ sX)
    (hX'v : IsNormalVariety ℂ sX') {f : X ⟶ Z} {fp : X' ⟶ Z} (hXQ : IsQFactorial sX)
    (hX'Q : IsQFactorial sX') {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    (hK' : Divisor.IsCanonicalDivisor sX' n (flipTransform f fp K))
    {v : NumericalCurveClasses sX}
    (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX') (hD : IsProper D.f) (hD' : IsProper D'.f)
    (hcmpNeg : ∀ (B : RDivisor X) {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X)
      (hL : ∀ j, (L j).IsCartier), logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j) →
      presDeg sX r L hL v < 0 → ∀ (n₀ n₁ : ℕ) (a a' : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n₀ B D a →
        MMP.Intersection.IsLogDiscrepancy sX' n₁ (flipTransform f fp B) D' a' → a ≤ a')
    {B' : RDivisor X} {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hKB : logCanonicalDivisor K B' = ∑ j, r j • Divisor.toRDivisor (L j))
    (hv0 : presDeg sX r L hL v = 0) {Δ₀ : QDivisor X}
    (hQ₀ : (Divisor.toQDivisor K + Δ₀).IsQCartier)
    (hΔ₀ : QDivisor.curveForm sX (Divisor.toQDivisor K + Δ₀) hQ₀ v < 0)
    {n₀ n₁ : ℕ} {a a' : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n₀ B' D a)
    (ha' : MMP.Intersection.IsLogDiscrepancy sX' n₁ (flipTransform f fp B') D' a') : a ≤ a' := by
  classical
  obtain ⟨r₀, L₀, hL₀, hpres₀⟩ := exists_presentation_of_isQCartier _ hQ₀
  have hv₀ : presDeg sX r₀ L₀ hL₀ v < 0 := by
    rw [← curveForm_eq_presDeg _ hQ₀ r₀ L₀ hL₀ hpres₀]; exact hΔ₀
  set Δ₀R := QDivisor.toRDivisor Δ₀ with hΔ₀R
  -- the segment `B_s = (1 - s) B' + s Δ₀`
  set S : Finset (MMP.Mori.PrimeDivisor X) := B'.support ∪ Δ₀R.support with hS
  set e : MMP.Mori.PrimeDivisor X → ℝ := fun P => Δ₀R P - B' P with he
  have hseg : Δ₀R = B' + ∑ P ∈ S, e P • Divisor.toRDivisor (Finsupp.single P 1) := by
    ext P
    rw [DivisorWithCoeffs.coeff_add, coeff_sum_smul_single]
    by_cases hP : P ∈ S
    · rw [if_pos hP]; simp [he, DivisorWithCoeffs.coeff_apply]
    · rw [if_neg hP]
      simp only [hS, Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not] at hP
      simp [DivisorWithCoeffs.coeff_apply, hP.1, hP.2]
  have hseg' : flipTransform f fp Δ₀R = flipTransform f fp B' +
      ∑ P ∈ S, e P • Divisor.toRDivisor (flipTransform f fp (Finsupp.single P 1)) := by
    rw [hseg, map_add, flipTransform_sum_smul]
    simp only [flipTransform_toRDivisor]
  have hKBs : ∀ s : ℝ, logCanonicalDivisor K ((1 - s) • B' + s • Δ₀R) =
      ∑ j, Fin.append ((1 - s) • r) (s • r₀) j • Divisor.toRDivisor (Fin.append L L₀ j) := by
    intro s
    rw [sum_append]
    simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum, ← hKB, ← hpres₀]
    simp only [logCanonicalDivisor, map_add, QDivisor.toRDivisor_toQDivisor, hΔ₀R]
    module
  have hLL := isCartier_append hL hL₀
  -- log discrepancies along the segment
  have hRC : ∀ G : RDivisor X, RDivisor.IsRCartier (Divisor.toRDivisor K + G) := fun G =>
    isRCartier_of_isQFactorial hXQ _
  have hRC' : ∀ G : RDivisor X', RDivisor.IsRCartier
      (Divisor.toRDivisor (flipTransform f fp K) + G) := fun G => isRCartier_of_isQFactorial hX'Q _
  obtain ⟨a₁, ha₁⟩ := exists_isLogDiscrepancy_real hXv hK (hRC B') D hD
  obtain ⟨a₂, ha₂⟩ := exists_isLogDiscrepancy_real hXv hK (hRC Δ₀R) D hD
  obtain ⟨a₁', ha₁'⟩ := exists_isLogDiscrepancy_real hX'v hK' (hRC' _) D' hD'
  obtain ⟨a₂', ha₂'⟩ := exists_isLogDiscrepancy_real hX'v hK' (hRC' (flipTransform f fp Δ₀R)) D' hD'
  have he₁ : a₁ = a := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha₁ ha
  have he₁' : a₁' = a' := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha₁' ha'
  subst he₁ he₁'
  have hineq : ∀ s : ℝ, 0 < s → s < 1 →
      (1 - s) * a₁ + s * a₂ ≤ (1 - s) * a₁' + s * a₂' := by
    intro s hs0 hs1
    obtain ⟨b, hb⟩ := exists_isLogDiscrepancy_real hXv hK (hRC ((1 - s) • B' + s • Δ₀R)) D hD
    obtain ⟨b', hb'⟩ := exists_isLogDiscrepancy_real hX'v hK'
      (hRC' (flipTransform f fp ((1 - s) • B' + s • Δ₀R))) D' hD'
    have hbs := isLogDiscrepancy_segment hXQ S (fun P => Finsupp.single P 1) e hseg s ha₁ ha₂ hb
    have hfl : flipTransform f fp ((1 - s) • B' + s • Δ₀R) =
        (1 - s) • flipTransform f fp B' + s • flipTransform f fp Δ₀R := by
      rw [map_add, flipTransform_smul, flipTransform_smul]
    rw [hfl] at hb'
    have hbs' := isLogDiscrepancy_segment hX'Q S (fun P => flipTransform f fp (Finsupp.single P 1))
      e hseg' s ha₁' ha₂' hb'
    have hneg : presDeg sX (Fin.append ((1 - s) • r) (s • r₀)) (Fin.append L L₀) hLL v < 0 := by
      rw [presDeg_append _ L hL _ L₀ hL₀, presDeg_smul, presDeg_smul, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.smul_apply, hv0, smul_zero, zero_add, smul_eq_mul]
      exact mul_neg_of_pos_of_neg hs0 hv₀
    have := hcmpNeg _ _ _ hLL (hKBs s) hneg n n b b' hb (by rw [hfl]; exact hb')
    rw [hbs, hbs'] at this
    exact this
  -- let `s → 0`
  by_contra hlt
  push Not at hlt
  set δ := a₁ - a₁' with hδ
  have hδ0 : 0 < δ := by linarith
  set M := |a₂' - a₂| + δ + 1 with hM
  have hM0 : 0 < M := by positivity
  set s := δ / (2 * M) with hs
  have hs0 : 0 < s := by positivity
  have hs1 : s < 1 := by
    rw [hs, div_lt_one (by positivity)]
    linarith [abs_nonneg (a₂' - a₂)]
  have h := hineq s hs0 hs1
  have h1 : s * (a₂' - a₂) ≤ s * |a₂' - a₂| := mul_le_mul_of_nonneg_left (le_abs_self _) hs0.le
  have h2 : s * |a₂' - a₂| < δ / 2 := by
    rw [hs, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [abs_nonneg (a₂' - a₂)]
  have h3 : (1 - s) * δ ≥ δ / 2 := by
    have : s ≤ 1 / 2 := by
      rw [hs, div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg (a₂' - a₂)]
    nlinarith
  have h4 : (1 - s) * δ ≤ s * (a₂' - a₂) := by
    simp only [hδ]
    linarith [h]
  linarith [h1, h2, h3, h4]

end CmpNeg

/-! ### Real lc pairs across an isomorphism in codimension one -/

section LcTransfer

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z]

/-- **Real lc pairs across an isomorphism in codimension one.** -/
private theorem isRealLcPair_of_comparison (hXv : IsNormalVariety ℂ sX)
    (hX'v : IsNormalVariety ℂ sX') (hZv : IsNormalVariety ℂ sZ) {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hfs : f ≫ sZ = sX) (hfs' : fp ≫ sZ = sX') [IsProper f] [IsProper fp]
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) [IsDominant f] [IsDominant fp]
    (V : Z.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {n : ℕ} {K' : Divisor X'}
    (hK' : K'.IsCanonicalDivisor sX' n) {B : RDivisor X} (hB : IsRealLcPair sX B)
    {B' : RDivisor X'}
    (hcoeff : ∀ (P : MMP.Mori.PrimeDivisor X) (P' : MMP.Mori.PrimeDivisor X'),
      f P.genericPoint = fp P'.genericPoint → B'.coeff P' = B.coeff P)
    (hKB' : RDivisor.IsRCartier (Divisor.toRDivisor K' + B'))
    (hcmp : ∀ (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX'), IsProper D.f → IsProper D'.f →
      D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) →
      D'.IsExceptional → ∀ (n₀ n₁ : ℕ) (a a' : ℝ),
        MMP.Intersection.IsLogDiscrepancy sX n₀ B D a →
        MMP.Intersection.IsLogDiscrepancy sX' n₁ B' D' a' → a ≤ a') :
    IsRealLcPair sX' B' := by
  classical
  obtain ⟨-, hB0, ⟨n₀, K₀, hK₀, hRC₀⟩, hBlc⟩ := hB
  have hP'V : ∀ P' : MMP.Mori.PrimeDivisor X', fp P'.genericPoint ∈ V := fun P' =>
    hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
  have hcorr : ∀ P' : MMP.Mori.PrimeDivisor X', ∃ P : MMP.Mori.PrimeDivisor X,
      f P.genericPoint = fp P'.genericPoint := fun P' =>
    exists_primeDivisor_genericPoint_eq' f fp V P' (hP'V P')
  refine ⟨hX'v, fun P' => ?_, ⟨n, K', hK', hKB'⟩, fun n₁ D' a' ha' => ?_⟩
  · obtain ⟨P, hP⟩ := hcorr P'
    rw [hcoeff P P' hP]
    exact hB0 P
  · by_cases hE' : D'.IsExceptional
    · let D'' : DivisorOver ℂ (fp ≫ sZ) :=
        ⟨D'.Y, D'.f, by rw [hfs']; exact D'.isNormalVariety, D'.isBirationalMorphism, D'.E⟩
      obtain ⟨D₀, hD₀p, hv₀⟩ := exists_divisorOver_valuation_comap_eq'
        (show IsNormalVariety ℂ (f ≫ sZ) by rw [hfs]; exact hXv) hf hfp D''
      let D : DivisorOver ℂ sX :=
        ⟨D₀.Y, D₀.f, by rw [← hfs]; exact D₀.isNormalVariety, D₀.isBirationalMorphism, D₀.E⟩
      obtain ⟨a, ha⟩ := exists_isLogDiscrepancy_real hXv hK₀ hRC₀ D hD₀p
      exact (hBlc n₀ D a ha).trans (hcmp D D' hD₀p ha'.2.1 hv₀ hE' n₀ n₁ a a' ha ha')
    · obtain ⟨P', hP'⟩ :=
        MMP.Threefold.Mori.exists_primeDivisor_valuation_eq_of_not_isExceptional hX'v D' hE'
      have hval := MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq ha'
        (isLogDiscrepancy_ofPrimeDivisor_real hX'v hK' hKB' P') hP'
      obtain ⟨P, hP⟩ := hcorr P'
      rw [hval, hcoeff P P' hP]
      have := hBlc n₀ _ _ (isLogDiscrepancy_ofPrimeDivisor_real hXv hK₀ hRC₀ P)
      linarith

end LcTransfer

/-! ### Pull-backs to the flip, and the flip is not an isomorphism -/

section FlipGeometry

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z]
  [IsLocallyNoetherian Z] [IsNormal Z] [CompactSpace Z]

/-- If `f` and `f⁺` are isomorphisms over `V`, over which lie the points of codimension at most one
of `X` and `X⁺`, the strict transform of `f^* M` is `f⁺^* M`. -/
private theorem isPullback_flipTransform (hZn : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hXn : IsNormalVariety ℂ (f ≫ sZ))
    (hX'n : IsNormalVariety ℂ (fp ≫ sZ)) [IsProper f] [IsProper fp] (hf : IsBirationalMorphism f)
    (hfp : IsBirationalMorphism fp) [IsDominant f] [IsDominant fp] [IsSeparated f]
    [IsSeparated (Z ↘ ⊤_ Scheme)]
    (V : Z.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {M : Divisor Z} (hM : M.IsCartier)
    {hB : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ M.supp}
    {E : Divisor X} (hE : M.IsPullback f hB E) :
    ∃ hB', M.IsPullback fp hB' (flipTransform f fp E) := by
  haveI : Surjective fp := ⟨surjective_of_isProper_of_isDominant fp⟩
  have hB' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp M
  obtain ⟨E', hE'⟩ := hM.exists_isPullback hB'
  refine ⟨hB', ?_⟩
  have heq : flipTransform f fp E = E' := by
    refine Finsupp.ext fun P' => ?_
    have hP'V : fp P'.genericPoint ∈ V :=
      hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
    obtain ⟨P, hP⟩ := exists_primeDivisor_genericPoint_eq' f fp V P' hP'V
    rw [flipTransform_apply_of_mem' hf fp.surjective V hP hP'V E]
    have hco : Order.coheight (fp P'.genericPoint) = 1 := by
      rw [coheight_apply_eq' fp V hP'V, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
    have hQ : MMP.Mori.PrimeDivisor.genericPoint Q = fp P'.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    obtain ⟨E₁, hE₁, hiso₁, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZn hXn hf Q
    obtain ⟨E₂, hE₂, hiso₂, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZn hX'n hfp Q
    have h1 : E₁ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq' f V (by rw [hE₁, hQ]; exact hP'V) (by rw [hP]; exact hP'V)
        (by rw [hE₁, hQ, hP]))
    have h2 : E₂ = P' := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq' fp V (by rw [hE₂, hQ]; exact hP'V) hP'V (by rw [hE₂, hQ]))
    subst h1 h2
    haveI := hiso₁
    haveI := hiso₂
    change E E₁ = E' E₂
    rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
      MMP.Positivity.coeff_eq_of_isPullback E₁ Q hE₁ hM hE,
      MMP.Positivity.coeff_eq_of_isPullback E₂ Q hE₂ hM hE']
  rw [heq]
  exact hE'

/-- **A flip is not an isomorphism.** If `f⁺` were an isomorphism, a Cartier multiple `D'` of the
strict transform of `L` pulled back along `(f⁺)⁻¹ ∘ f` would be a Cartier multiple of `L`, of
degree zero on every curve contracted by `f`. -/
private theorem not_isIso_of_isQCartier_flipTransform [QuasiCompact sX]
    (hZn : IsNormalVariety ℂ sZ) {f : X ⟶ Z} {fp : X' ⟶ Z} (hXn : IsNormalVariety ℂ (f ≫ sZ))
    (hfs' : fp ≫ sZ = sX') [IsProper f] [IsProper fp] (hf : IsBirationalMorphism f)
    [IsDominant f] [IsSeparated f] [IsSeparated (Z ↘ ⊤_ Scheme)] [IsSeparated sX']
    [LocallyOfFiniteType sX'] (hfs : f ≫ sZ = sX) (V : Z.Opens) [IsIso (f ∣_ V)]
    [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {L : QDivisor X}
    (hL : L.IsQCartier) (hL' : QDivisor.IsQCartier (flipTransform f fp L)) {T : ProperCurve sX}
    (hT : T.IsContractedBy f)
    (hT0 : QDivisor.curveForm sX L hL (OneCycle.numericalClass sX (T.cycle ℝ)) ≠ 0) :
    ¬ IsIso fp := by
  intro hiso
  haveI : Surjective fp := inferInstance
  set g : X ⟶ X' := f ≫ inv fp with hg
  have hgs : g ≫ sX' = sX := by rw [hg, Category.assoc, ← hfs', IsIso.inv_hom_id_assoc, hfs]
  haveI : IsDominant g := by rw [hg]; infer_instance
  have hfpg : ∀ x, fp (g x) = f x := fun x => by
    rw [← Scheme.Hom.comp_apply, hg, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  obtain ⟨m, hm, D', hD', hD'c⟩ := hL'
  have hBg := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' g D'
  obtain ⟨E, hE⟩ := hD'c.exists_isPullback hBg
  have hEc : E.IsCartier := hE.isCartier hD'c
  -- `E = m L`
  have hEL : Divisor.toQDivisor E = m • L := by
    refine Finsupp.ext fun P => ?_
    show (Divisor.toQDivisor E).coeff P = (m • L).coeff P
    have hPV : f P.genericPoint ∈ V :=
      hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
    obtain ⟨P', hP'⟩ := exists_primeDivisor_genericPoint_eq' fp f V P hPV
    have hP'V : fp P'.genericPoint ∈ V := by rw [hP']; exact hPV
    have hgP : g P.genericPoint = P'.genericPoint :=
      eq_of_apply_eq' fp V (by rw [hfpg]; exact hPV) hP'V (by rw [hfpg, hP'])
    have hco : Order.coheight (f P.genericPoint) = 1 := by
      rw [coheight_apply_eq' f V hPV, AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
    set Q := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hco
    have hQ : MMP.Mori.PrimeDivisor.genericPoint Q = f P.genericPoint :=
      AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hco
    obtain ⟨E₁, hE₁, hiso₁, -⟩ :=
      MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hZn hXn hf Q
    have h1 : E₁ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (eq_of_apply_eq' f V (by rw [hE₁, hQ]; exact hPV) hPV (by rw [hE₁, hQ]))
    subst h1
    haveI := hiso₁
    haveI : IsIso (g.stalkMap E₁.genericPoint) := by
      have h1 : IsIso ((inv fp).stalkMap (f E₁.genericPoint)) :=
        ((isIso_iff_isIso_stalkMap (inv fp)).mp inferInstance).2 _
      rw [hg, Scheme.Hom.stalkMap_comp]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 hiso₁
    have hc := MMP.Positivity.coeff_eq_of_isPullback E₁ P' hgP hD'c hE
    have hc' : (flipTransform f fp L).coeff P' = L.coeff E₁ :=
      flipTransform_apply_of_mem' hf fp.surjective V hP'.symm hP'V L
    rw [Divisor.coeff_toQDivisor, hc, DivisorWithCoeffs.coeff_smul, ← hc']
    have := congrArg (fun F : QDivisor X' => F.coeff P') hD'
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul] at this
    exact this
  -- `E` has degree zero along `T`
  have hTg : T.IsContractedBy g := fun x hx => by
    have e : ∀ y, g y = (inv fp) (f y) := fun y => by rw [hg, Scheme.Hom.comp_apply]
    rw [e, e]
    exact congrArg (inv fp).base (hT x hx)
  haveI := hD'c.isInvertibleModule_divisorialSheaf
  haveI := hEc.isInvertibleModule_divisorialSheaf
  have hdeg : E.degreeOn ℂ sX T.ι T.dim_le hEc = 0 := by
    have h0 := ProperCurve.degree_pullback_eq_zero_of_isContractedBy g hgs T hTg D'.divisorialSheaf
    obtain rfl := hE.pullback_eq hD'c
    obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hD'c g hBg
    exact (degreeOn_eq_of_iso ℂ sX T.ι T.dim_le e).trans h0
  -- but the curve form of `L` along `T` is `(E · T) / m`
  have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hpres : QDivisor.toRDivisor L = ∑ _j : Fin 1, (m : ℝ)⁻¹ • Divisor.toRDivisor E := by
    rw [Fin.sum_univ_one, ← QDivisor.toRDivisor_toQDivisor, hEL, map_zsmul,
      ← Int.cast_smul_eq_zsmul ℝ, smul_smul, inv_mul_cancel₀ hmR, one_smul]
  apply hT0
  rw [curveForm_eq_presDeg L hL (fun _ => (m : ℝ)⁻¹) (fun _ => E) (fun _ => hEc) hpres,
    presDeg_numericalClass_cycle, Fin.sum_univ_one, hdeg]
  simp

end FlipGeometry

/-! ### The relative Picard number of the flip -/

section RhoFlip

variable {X X' Z : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {sZ : Z ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']

/-- The value of an `ℝ`-intersection number of the zero divisor is zero. -/
private theorem isRIntersectionNumber_zero_eq [QuasiCompact sX] {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {C : ProperCurve sX} {x : ℝ}
    (h : IsRIntersectionNumber ℂ sX (0 : RDivisor X) r L C x) : x = 0 :=
  (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r L (Fin.elim0 : Fin 0 → ℝ)
    (Fin.elim0 : Fin 0 → Divisor X) _ _ h
    ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩

/-- **The relative Picard number of the flip is one.** Every Cartier divisor on `X⁺` is the strict
transform of an `ℝ`-Cartier divisor on `X`, numerically equivalent over `Z` to a multiple of
`K + Δ₀`; transporting the equivalence, every Cartier divisor on `X⁺` is numerically equivalent
over `Z` to a multiple of the `f⁺`-ample `K⁺ + Δ₀⁺`, so the curves contracted by `f⁺` have
proportional classes. -/
private theorem relativePicardNumber_flip_eq_one [QuasiCompact sX] [IsProper sX']
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hXQ : IsQFactorial sX)
    (hX' : MMP.Mori.IsProjectiveVariety ℂ sX') (hX'Q : IsQFactorial sX') {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {Δ₀ : QDivisor X} (hklt : IsKltPair sX Δ₀)
    {R' : Set (NumericalCurveClasses sX)}
    (hΔ₀ : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ₀) R') {T : ProperCurve sX}
    (hRT : R' = {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w})
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hf : IsContractionOfRay sX sZ R' f)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hflip : IsFlipOf sX sZ sX' (Divisor.toQDivisor K + Δ₀) f fp) [IsProper fp]
    (happ : ∀ U : Z.Opens, IsIso (fp.app U)) (hni : ¬ IsIso fp) :
    MMP.Flips.relativePicardNumber sX' fp = 1 := by
  classical
  haveI : LocallyOfFiniteType sX' := hX'.toIsVariety.toLocallyOfFiniteType
  haveI : QuasiCompact sX' := hX'.toIsVariety.toQuasiCompact
  -- a curve contracted by `f⁺`
  obtain ⟨z, hz⟩ : ∃ z : Z, z ∉ biregularLocus fp := by
    by_contra h
    push Not at h
    have htop : biregularLocus fp = ⊤ := eq_top_iff.mpr fun z _ => h z
    have := MMP.Mori.isBiregular_biregularLocus fp
    rw [htop] at this
    exact hni ((MMP.Mori.isBiregular_top_iff fp).mp this)
  haveI : IsDominant fp := hflip.isSmallMorphism_flip.isBirationalMorphism.isDominant
  obtain ⟨x, rfl⟩ := surjective_of_isProper_of_isDominant fp z
  obtain ⟨C₀, hC₀⟩ := exists_properCurve_isContractedBy_of_mem_exceptionalSet' (sX := sX') happ
    (MMP.Mori.mem_exceptionalSet.mpr hz)
  -- the `f⁺`-ample Cartier multiple `L₀` of `K⁺ + Δ₀⁺`
  obtain ⟨m₀, hm₀, L₀, hL₀, hL₀D, hL₀a⟩ := hflip.hasRelativelyAmpleMultiple_flip
  haveI := hL₀.isInvertibleModule_divisorialSheaf
  have hpos : ∀ C : ProperCurve sX', C.IsContractedBy fp →
      (0 : ℝ) < (L₀.degreeOn ℂ sX' C.ι C.dim_le hL₀ : ℝ) := fun C hC => by
    exact_mod_cast MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy fp
      L₀.divisorialSheaf hL₀a C hC
  have hdegcls : ∀ C : ProperCurve sX', NumericalCurveClasses.degree sX' L₀.divisorialSheaf
      (OneCycle.numericalClass sX' (C.cycle ℝ)) = (L₀.degreeOn ℂ sX' C.ι C.dim_le hL₀ : ℝ) :=
    fun C => by rw [NumericalCurveClasses.degree_numericalClass, OneCycle.degree_cycle]; rfl
  have hw₀ : OneCycle.numericalClass sX' (C₀.cycle ℝ) ≠ 0 := fun h0 => by
    have := hdegcls C₀
    rw [h0, map_zero] at this
    exact (hpos C₀ hC₀).ne' this.symm
  -- every Cartier divisor on `X⁺` is proportional to `L₀` on curves contracted by `f⁺`
  have hT : OneCycle.numericalClass sX (T.cycle ℝ) ∈ R' := by
    rw [hRT]; exact ⟨1, zero_le_one, one_smul _ _⟩
  have hβ : QDivisor.curveForm sX (Divisor.toQDivisor K + Δ₀) hΔ₀.1
      (OneCycle.numericalClass sX (T.cycle ℝ)) < 0 := by
    refine hΔ₀.2.2 _ hT fun h0 => ?_
    obtain ⟨v, hv0, hRv⟩ := hΔ₀.2.1.2
    have hvR : v ∈ R' := by rw [hRv]; exact ⟨1, zero_le_one, one_smul _ _⟩
    rw [hRT, h0] at hvR
    obtain ⟨c, -, hc⟩ := hvR
    exact hv0 (by rw [← hc, smul_zero])
  have htrans := (IsKltPair.isNumericallyTrivialOver_flipTransform_of_isContractionOfRay hklt
    ⟨n, hK⟩ hX hXQ hX' hX'Q hΔ₀ hf (Or.inr ⟨_, hflip⟩) hZ (Category.id_comp sZ))
  have hKC : ∀ (M' : Divisor X') (hM' : M'.IsCartier), ∃ s : ℝ, ∀ C : ProperCurve sX',
      C.IsContractedBy fp →
      (M'.degreeOn ℂ sX' C.ι C.dim_le hM' : ℝ) = s * (L₀.degreeOn ℂ sX' C.ι C.dim_le hL₀ : ℝ) := by
    intro M' hM'
    obtain ⟨D, hD, hDM⟩ := htrans.2.2.2.1 (Divisor.toRDivisor M')
      ⟨1, fun _ => 1, fun _ => M', fun _ => hM', by simp [toRDivisor_eq_mapCoeffs]⟩
    obtain ⟨k, r, L, hL, hDL⟩ := hD
    simp only [← toRDivisor_eq_mapCoeffs] at hDL
    obtain ⟨r₀, L₀', hL₀', hpres₀⟩ := exists_presentation_of_isQCartier _ hΔ₀.1
    set α := presDeg sX r L hL (OneCycle.numericalClass sX (T.cycle ℝ))
    set β := QDivisor.curveForm sX (Divisor.toQDivisor K + Δ₀) hΔ₀.1
      (OneCycle.numericalClass sX (T.cycle ℝ))
    have hβ' : β = presDeg sX r₀ L₀' hL₀' (OneCycle.numericalClass sX (T.cycle ℝ)) := by
      simp only [β]; rw [curveForm_eq_presDeg _ hΔ₀.1 r₀ L₀' hL₀' hpres₀]
    -- `N = D - (α/β) (K + Δ₀)` is numerically trivial over `Z`
    set N := D - (α / β) • QDivisor.toRDivisor (Divisor.toQDivisor K + Δ₀) with hN
    have hLL := isCartier_append hL hL₀'
    have hNpres : N = ∑ j, Fin.append r (-(α / β) • r₀) j •
        Divisor.toRDivisor (Fin.append L L₀' j) := by
      rw [sum_append, hN, hDL, hpres₀, sub_eq_add_neg, ← neg_smul, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
    have hNtriv : IsNumericallyTrivialOver ℂ sX (f ≫ 𝟙 Z) N := by
      refine ⟨⟨k + 1, Fin.append r (-(α / β) • r₀), Fin.append L L₀', hLL,
        by rw [hNpres]; simp only [toRDivisor_eq_mapCoeffs]⟩,
        ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂
          h₁ h₂ => ?_⟩
      rw [Category.comp_id] at hC
      rw [isRIntersectionNumber_zero_eq h₂]
      have hCR := (hf.isContractedBy_iff C).mp hC
      rw [hRT] at hCR
      obtain ⟨c, -, hc⟩ := hCR
      have h₃ := isRIntersectionNumber_presDeg _ _ hLL hNpres C
      rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ r₁ L₁ _ _ _ _ h₁ h₃, ← hc, map_smul,
        presDeg_append r L hL _ L₀' hL₀', presDeg_smul, LinearMap.add_apply,
        LinearMap.smul_apply, ← hβ', smul_eq_mul, smul_eq_mul]
      have hβ0 : β ≠ 0 := hβ.ne
      field_simp
      ring
    have hN' := htrans.2.2.1 N hNtriv
    -- the strict transform of `N` is `M' - (α / (β m₀)) L₀`
    have hNflip : flipTransform f fp N = Divisor.toRDivisor M' -
        (α / (β * m₀)) • Divisor.toRDivisor L₀ := by
      rw [hN, map_sub, flipTransform_smul, hDM, flipTransform_qtoRDivisor,
        ← QDivisor.toRDivisor_toQDivisor L₀,
        hL₀D, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
      have hm₀R : (m₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm₀.ne'
      congr 2
      push_cast
      field_simp
    refine ⟨α / (β * m₀), fun C hC => ?_⟩
    have hp : IsRIntersectionNumber ℂ sX' (flipTransform f fp N) ![1, -(α / (β * m₀))] ![M', L₀] C
        ((M'.degreeOn ℂ sX' C.ι C.dim_le hM' : ℝ) -
          α / (β * m₀) * (L₀.degreeOn ℂ sX' C.ι C.dim_le hL₀ : ℝ)) := by
      refine ⟨fun j => by fin_cases j <;> simpa, ![M'.degreeOn ℂ sX' C.ι C.dim_le hM',
        L₀.degreeOn ℂ sX' C.ι C.dim_le hL₀], ?_, fun j => ?_, ?_⟩
      · rw [hNflip, Fin.sum_univ_two]
        simp [sub_eq_add_neg, neg_smul]
      · fin_cases j
        · exact MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sX' C M' hM'
        · exact MMP.Flips.isCartierIntersectionNumber_degreeOn ℂ sX' C L₀ hL₀
      · simp [Fin.sum_univ_two]
        ring
    have hz' := hN'.2.2 C (by rw [Category.comp_id]; exact hC) 2 _ _ _ 0 Fin.elim0 Fin.elim0 0 hp
      ⟨fun j => j.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
    linarith
  -- the classes of contracted curves are proportional to that of `C₀`
  refine relativePicardNumber_eq_one_of_forall_isContractedBy' fp C₀ hC₀ hw₀ fun C hC => ?_
  set t := (L₀.degreeOn ℂ sX' C.ι C.dim_le hL₀ : ℝ) / (L₀.degreeOn ℂ sX' C₀.ι C₀.dim_le hL₀ : ℝ)
  refine ⟨t, ?_⟩
  rw [← map_smul]
  refine (Submodule.Quotient.eq _).mpr (OneCycle.mem_numericallyTrivial.mpr fun L hL => ?_)
  obtain ⟨M', hM', ⟨e⟩⟩ := exists_isCartier_divisorialSheaf_iso' L
  haveI := hM'.isInvertibleModule_divisorialSheaf
  obtain ⟨s, hs⟩ := hKC M' hM'
  have hd : ∀ C' : ProperCurve sX', OneCycle.degree ℝ sX' L (C'.cycle ℝ) =
      (M'.degreeOn ℂ sX' C'.ι C'.dim_le hM' : ℝ) := fun C' => by
    rw [OneCycle.degree_cycle]
    exact_mod_cast (degreeOn_eq_of_iso ℂ sX' C'.ι C'.dim_le e).symm
  rw [map_sub, map_smul, hd, hd, hs C hC, hs C₀ hC₀, smul_eq_mul]
  have h0 := (hpos C₀ hC₀).ne'
  simp only [t]
  field_simp
  ring

end RhoFlip

private theorem solution
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {B : RDivisor X} {R : Set (RelativeNumericalCurveClasses sX g)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 4)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hB : IsRealDltPair sX B)
    (hR : IsExtremalRay ℝ
      (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R)
    (hneg : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier),
      logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j) ∧
        ∀ u ∈ R, u ≠ 0 → ∑ j, r j *
          (haveI := (hL j).isInvertibleModule_divisorialSheaf
           RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) < 0) :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (_ : CompactSpace Z) (_ : IsLocallyNoetherian Z)
      (_ : IsNormal Z)
      (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (h : Z ⟶ S),
      IsRelativeContractionOfFace g R f h ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f ∧
        (IsBirationalMorphism f → ∀ N : RDivisor X, IsCartierCombination N →
          (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
              IsRIntersectionNumber ℂ sX N r L C x → x = 0) →
          ∃ M : RDivisor Z, IsRCartierPullback f M N) ∧
        ((IsBirationalMorphism f ∧
            ∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) →
          IsQFactorial sZ ∧
            IsRealDltPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B) ∧
            ∀ B' : RDivisor X, IsRealLcPair sX B' →
              IsRelativelyNef ℂ sX g (logCanonicalDivisor K B') →
              (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
                ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
                  IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B') r L C x → x = 0) →
              IsRealLcPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B') ∧
                IsRelativelyNef ℂ sZ h
                  (logCanonicalDivisor (RationalMap.transformDivisor (X := X) f.toRationalMap K)
                    (RationalMap.transformDivisor (X := X) f.toRationalMap B'))) ∧
        (IsSmall ℂ sZ sX f →
          ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X')
            (_ : IsLocallyNoetherian X') (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ))
            (fp : X' ⟶ Z),
            IsRealFlipStep sX sZ sX' K B (flipTransform f fp K) (flipTransform f fp B) f fp ∧
              MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧
              topologicalKrullDim X' = 4 ∧ IsRealDltPair sX' (flipTransform f fp B) ∧
              (∀ N : RDivisor X, IsCartierCombination N →
                (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
                  ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
                    IsRIntersectionNumber ℂ sX N r L C x → x = 0) →
                ∃ M : RDivisor Z,
                  IsRCartierPullback f M N ∧ IsRCartierPullback fp M (flipTransform f fp N)) ∧
              ∀ B' : RDivisor X, IsRealLcPair sX B' →
                IsRelativelyNef ℂ sX g (logCanonicalDivisor K B') →
                (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
                  ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
                    IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B') r L C x → x = 0) →
                IsRealLcPair sX' (flipTransform f fp B') ∧
                  IsRelativelyNef ℂ sX' (fp ≫ h)
                    (logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B'))) := by
  classical
  obtain ⟨n, hKn⟩ := hK
  obtain ⟨m, r, L, hL, hKB, hnegR⟩ := hneg
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  haveI : QuasiCompact sX := hX.toIsVariety.toQuasiCompact
  -- the extremal ray of `NE̅(X)` underlying `R`
  set R' : Set (NumericalCurveClasses sX) := relativeToAbsolute sX g '' R with hR'def
  have hR' : IsExtremalRay ℝ (closedConeOfCurves sX : Set (NumericalCurveClasses sX)) R' :=
    isExtremalRay_image_relativeToAbsolute sX sS g hg hR
  obtain ⟨w, hw0, hRw⟩ := hR.2
  set v := relativeToAbsolute sX g w with hvdef
  have hR'v : R' = {x | ∃ c : ℝ, 0 ≤ c ∧ c • v = x} := by
    rw [hR'def, hRw]
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨c, hc, by rw [map_smul]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c • w, ⟨c, hc, rfl⟩, map_smul _ _ _⟩
  have hv0 : presDeg sX r L hL v < 0 := by
    rw [presDeg_relativeToAbsolute]
    exact hnegR w (by rw [hRw]; exact ⟨1, zero_le_one, one_smul _ _⟩) hw0
  -- a klt rational witness
  obtain ⟨Δ₀, hdlt₀, hklt, hQ₀, hΔ₀v⟩ := exists_isKltPair_curveForm_neg hXQ hKn hB hL hKB v hv0
  have hΔ₀ : IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ₀) R' :=
    isNegativeExtremalRayOf_of_neg hQ₀ hR' hR'v hΔ₀v
  -- the contraction
  obtain ⟨⟨T, -, hRT⟩, Z, sZ, f, hf, hZ, hρN, hamp⟩ :=
    exists_isContractionOfRay_of_isKltPair sX hX hklt hKn hΔ₀
  have hXn : IsNormalVariety ℂ sX := hB.1.1
  have hZn : IsNormalVariety ℂ sZ := hf.isNormalVariety_target
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper f := isProper_of_isProjectiveMorphism _ hf.isProjectiveMorphism
  haveI : MMP.Mori.IsVariety ℂ sX := hXn.1
  haveI : MMP.Mori.IsVariety ℂ sZ := hZn.1
  have hRg : ∀ C : ProperCurve sX, OneCycle.numericalClass sX (C.cycle ℝ) ∈ R' →
      C.IsContractedBy g := by
    rintro C ⟨u, -, hu⟩
    exact isContractedBy_of_mem_range hS g hg C hu
  obtain ⟨h, hh, hhS⟩ : ∃ h : Z ⟶ S, f ≫ h = g ∧ h ≫ sS = sZ := by
    haveI : Surjective f := ⟨hf.surjective⟩
    haveI : ∀ U, IsIso (f.c.app U) := fun U => hf.isIso_app U.unop
    haveI : IsIso f.c := NatIso.isIso_of_isIso_app _
    obtain ⟨h, hh, -⟩ := MMP.Mori.existsUnique_comp_eq_of_isContractedBy hX hZ hS
      hf.isProjectiveMorphism hf.comp_eq hg fun C hC => hRg C ((hf.isContractedBy_iff C).mp hC)
    exact ⟨h, hh, (MMP.existsUnique_comp_eq_of_isIso_c f sX fun _ _ _ =>
      Subsingleton.elim _ _).unique (by rw [← Category.assoc, hh, hg]) hf.comp_eq⟩
  have hface : IsRelativeContractionOfFace g R f h :=
    { isExtremalFace := hR.1
      isProjectiveMorphism := IsProjectiveMorphism.of_comp h sS (hhS ▸ hZ.isProjective)
      comp_eq := hh
      isIso_app := hf.isIso_app
      isContractedBy_iff := fun C hC => by
        rw [hf.isContractedBy_iff C]
        constructor
        · rintro ⟨u, hu, hEq⟩
          have := relativeToAbsolute_injective g (show relativeToAbsolute sX g u =
            relativeToAbsolute sX g (C.relativeClass g hC) from hEq)
          rwa [this] at hu
        · intro hmem
          exact ⟨_, hmem, rfl⟩ }
  -- the class of `T` spans `R'`
  have hv0' : v ≠ 0 := fun h0 => hw0 (relativeToAbsolute_injective g (h0.trans (map_zero _).symm))
  have hT0 : OneCycle.numericalClass sX (T.cycle ℝ) ≠ 0 := by
    intro h0
    have hvR : v ∈ R' := by rw [hR'v]; exact ⟨1, zero_le_one, one_smul _ _⟩
    rw [hRT, h0] at hvR
    obtain ⟨c, -, hc⟩ := hvR
    exact hv0' (by rw [← hc, smul_zero])
  have hfT : IsContractionOfRay sX sZ
      {w | ∃ c : ℝ, 0 ≤ c ∧ c • OneCycle.numericalClass sX (T.cycle ℝ) = w} f := hRT ▸ hf
  -- rational boundaries close to `B` are negative on `R'`
  obtain ⟨η, hη, hηneg⟩ := curveForm_neg_of_close hXQ hL hKB B.support v hv0
  have hnegΔ : ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Δ : QDivisor X), (∀ P, |c P| < η) →
      QDivisor.toRDivisor Δ = B + ∑ P ∈ B.support, c P • Divisor.toRDivisor (Finsupp.single P 1) →
      IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R' := fun c Δ hc hΔ =>
    isNegativeExtremalRayOf_of_neg (isQCartier_of_isQFactorial sX hXQ _) hR' hR'v
      (hηneg c Δ hc hΔ _)
  have hantiΔ : ∀ Δ : QDivisor X, IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R' →
      (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f := fun Δ hΔ =>
    hasRelativelyAmpleMultiple_neg_of_isExtremalRay sX sZ hXn hX hZ ⟨n, hKn⟩ hΔ.1 hR'
      (fun u hu hu0 => by rw [← curveForm_apply]; exact hΔ.2.2 u hu hu0) f hf.comp_eq
      fun C hC => (hf.isContractedBy_iff C).mp hC
  -- `-(K + B)` is `f`-ample
  have hanti : IsRelativelyAntiAmple f (logCanonicalDivisor K B) := by
    obtain ⟨ι, _, _, Δ, w, c, hw, hw1, hwB, hc, hΔc⟩ := exists_rat_decomposition B hη
    have hsum : -logCanonicalDivisor K B =
        ∑ i, w i • QDivisor.toRDivisor (-(Divisor.toQDivisor K + Δ i)) := by
      simp only [map_neg, map_add, QDivisor.toRDivisor_toQDivisor, smul_neg, smul_add,
        Finset.sum_neg_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, hw1, one_smul, hwB,
        logCanonicalDivisor]
    rw [IsRelativelyAntiAmple, hsum]
    exact isRelativelyAmple_sum (fun i => isRelativelyAmple_of_hasRelativelyAmpleMultiple f
      (hantiΔ _ (hnegΔ _ _ (hc i) (hΔc i)))) hw
  have hcontr : IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f :=
    { isNormalVariety_source := hXn
      isNormalVariety_target := hZn
      isCartierCombination := ⟨m, r, L, hL, by rw [hKB]; simp only [toRDivisor_eq_mapCoeffs]⟩
      isContraction := ⟨hZn.1, hXn.1, hf.comp_eq, inferInstance, hf.isIso_app⟩
      isRelativelyAntiAmple := hanti
      relativePicardNumber_eq_one := relativePicardNumber_eq_one_of_isContractionOfRay hfT hT0 }
  -- the class of `T` lies in `R`
  have hTg : T.IsContractedBy g := hRg T (by rw [hRT]; exact ⟨1, zero_le_one, one_smul _ _⟩)
  have hTR : T.relativeClass g hTg ∈ R := by
    have hmem : relativeToAbsolute sX g (T.relativeClass g hTg) ∈ R' := by
      rw [hRT]; exact ⟨1, zero_le_one, one_smul _ _⟩
    rw [hR'def] at hmem
    obtain ⟨u, hu, hEq⟩ := hmem
    rwa [relativeToAbsolute_injective g hEq] at hu
  have hdescent : IsBirationalMorphism f → ∀ N : RDivisor X, IsCartierCombination N →
      (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
        ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
          IsRIntersectionNumber ℂ sX N r L C x → x = 0) →
      ∃ (k : ℕ) (c : Fin k → ℝ) (E : Fin k → Divisor X) (M : Fin k → Divisor Z),
        (∀ i, (E i).IsCartier) ∧ (∀ i, (M i).IsCartier) ∧
        (∀ i, ∃ hB, (M i).IsPullback f hB (E i)) ∧ N = ∑ i, c i • Divisor.toRDivisor (E i) :=
    fun hbir N hN hnull =>
      exists_pullback_presentation_of_null hX hKn hklt hΔ₀ hRT hZ hf hbir hN (hnull T hTg hTR)
  have hanti' : ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Δ : QDivisor X), (∀ P, |c P| < η) →
      QDivisor.toRDivisor Δ = B + ∑ P ∈ B.support, c P • Divisor.toRDivisor (Finsupp.single P 1) →
      (-(Divisor.toQDivisor K + Δ)).HasRelativelyAmpleMultiple f := fun c Δ hc hΔ =>
    hantiΔ _ (hnegΔ c Δ hc hΔ)
  refine ⟨Z, inferInstance, inferInstance, inferInstance, inferInstance, sZ, f, h, hface, hZ,
    hcontr, ?_, ?_, ?_⟩
  · -- descent of null divisors
    intro hbir N hN hnull
    obtain ⟨k, c, E, M, -, hMc, hpb, hNE⟩ := hdescent hbir N hN hnull
    exact ⟨∑ i, c i • Divisor.toRDivisor (M i), k, c, M, E, hMc, rfl, hpb, hNE⟩
  · -- the divisorial case
    rintro ⟨hbir, E, hE⟩
    have hnsmall : ¬ IsSmallMorphism sX sZ f := fun hs => by
      refine notMem_of_coheight_le_one' hs.two_le_codimension
        (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint E).le ?_
      rw [← SetLike.mem_coe, hE]
      exact MMP.Flips.primeDivisor_genericPoint_mem_support E
    have hstep : IsProjectiveElementaryDltStep sX sZ sZ K Δ₀ R' f (𝟙 Z)
        (flipTransform f (𝟙 Z) Δ₀) :=
      { isProjectiveQFactorialDltPair := ⟨hX, hXQ, ⟨n, hKn⟩, hdlt₀⟩
        isNegativeExtremalRayOf := hΔ₀
        isContractionOfRay := hf
        isBirationalMorphism := hbir
        comp_eq := Category.id_comp _
        eq_flipTransform := rfl
        flip_or_divisorial := Or.inr ⟨hnsmall, inferInstance⟩ }
    have hZpair := IsProjectiveElementaryDltStep.isProjectiveQFactorialDltPair_flipTransform hstep
      hZ hρN hamp
    have hid : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X),
        flipTransform f (𝟙 Z) D = RationalMap.transformDivisor (X := X) f.toRationalMap D :=
      fun D => MMP.Fourfold.inverseTransformDivisor_id _
    have hZQ := hZpair.isQFactorial
    obtain ⟨nZ, hKZ⟩ := hZpair.isCanonicalDivisor
    have hnZ : nZ = n := by
      have h1 := hKZ.topologicalKrullDim_eq
      have h2 := hKn.topologicalKrullDim_eq
      have h3 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hbir
      rw [h1, h2] at h3
      exact_mod_cast h3
    subst nZ
    rw [hid] at hKZ
    refine ⟨hZQ, isRealDltPair_transformDivisor_of_isBirationalMorphism hXn hZn hXQ hZQ
      hf.comp_eq hbir hKn hKZ hB hη hanti', fun B' hB' hnef hnull => ?_⟩
    haveI : IsDominant f := hbir.isDominant
    haveI : Surjective f := ⟨hf.surjective⟩
    haveI : IsSeparated (f ≫ sZ) := by rw [hf.comp_eq]; exact hXn.1.toIsSeparated
    haveI : IsSeparated f := IsSeparated.of_comp f sZ
    haveI : IsSeparated sZ := hZn.1.toIsSeparated
    haveI := isSeparated_terminal' sZ
    haveI : IsIso (f ∣_ biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
    have hXn' : IsNormalVariety ℂ (f ≫ sZ) := by rw [hf.comp_eq]; exact hXn
    have hKZ' : Divisor.IsCanonicalDivisor sZ n (flipTransform f (𝟙 Z) K) := by rw [hid]; exact hKZ
    obtain ⟨m', r', L', hL', hKB', -⟩ := id hnef
    have hv0' : presDeg sX r' L' hL' v = 0 := by
      have h1 := hnull T hTg hTR m' r' L' _ (isRIntersectionNumber_presDeg r' L' hL' hKB' T)
      have hvR : v ∈ R' := by rw [hR'v]; exact ⟨1, zero_le_one, one_smul _ _⟩
      rw [hRT] at hvR
      obtain ⟨c, -, hc⟩ := hvR
      rw [← hc, map_smul, h1, smul_zero]
    have hcmpB' : ∀ (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sZ), IsProper D.f → IsProper D'.f →
        D.valuation.comap (functionFieldMap f) =
          D'.valuation.comap (functionFieldMap (𝟙 Z)) →
        D'.IsExceptional → ∀ (n₀ n₁ : ℕ) (a a' : ℝ),
          MMP.Intersection.IsLogDiscrepancy sX n₀ B' D a →
          MMP.Intersection.IsLogDiscrepancy sZ n₁
            (RationalMap.transformDivisor (X := X) f.toRationalMap B') D' a' → a ≤ a' := by
      intro D D' hD hD' hvD hE' n₀ n₁ a a' ha ha'
      refine le_of_forall_neg hXn hZn hXQ hZQ hKn hKZ' D D' hD hD'
        (fun B₁ m₁ r₁ L₁ hL₁ hKB₁ hv₁ n₂ n₃ a₁ a₁' ha₁ ha₁' =>
          (realCmp_of_negative hXn hZn hZn hf.comp_eq (Category.id_comp sZ) hbir
            (isBirationalMorphism_of_isIso _) hXQ hZQ hKn hKZ' hR' hR'v hantiΔ
            (fun Δ _ => ⟨isQCartier_of_isQFactorial sZ hZQ _, fun C hC =>
              absurd hC (not_isContractedBy_of_isIso (𝟙 Z) C)⟩)
            (fun Δ => by rw [transformDivisor_id hZn, hid]) (biregularLocus f)
            (fun z hz => Or.inl hz) (fun x hx => hx) hL₁ hKB₁ hv₁ D D' hD hD' hvD hE' ha₁
            ha₁').1) hL' hKB' hv0' hQ₀ hΔ₀v ha (by rw [hid]; exact ha')
    have hlc : IsRealLcPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B') :=
      isRealLcPair_of_comparison hXn hZn hZn hf.comp_eq (Category.id_comp sZ) hbir
        (isBirationalMorphism_of_isIso _) (biregularLocus f)
        (fun z hz => MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal f hbir hz)
        hKZ hB' (fun P P' hPP => by
          rw [← hid]
          exact flipTransform_apply_of_mem' hbir (Scheme.Hom.surjective (𝟙 Z)) ⊤ hPP trivial B')
        (isRCartier_of_isQFactorial hZQ _) hcmpB'
    -- nefness over `S`
    obtain ⟨k, c, E, M, hEc, hMc, hpb, hNE⟩ := hdescent hbir (logCanonicalDivisor K B')
      ⟨m', r', L', hL', by rw [hKB']; simp only [toRDivisor_eq_mapCoeffs]⟩ hnull
    have hpush' : logCanonicalDivisor (RationalMap.transformDivisor (X := X) f.toRationalMap K)
        (RationalMap.transformDivisor (X := X) f.toRationalMap B') =
          ∑ i, c i • Divisor.toRDivisor (M i) := by
      rw [← hid, ← hid]
      have : logCanonicalDivisor (flipTransform f (𝟙 Z) K) (flipTransform f (𝟙 Z) B') =
          flipTransform f (𝟙 Z) (logCanonicalDivisor K B') := by
        rw [logCanonicalDivisor, logCanonicalDivisor, map_add, flipTransform_toRDivisor]
      rw [this, hNE, flipTransform_sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      obtain ⟨hB₁, hp⟩ := hpb i
      rw [flipTransform_toRDivisor, hid,
        MMP.Positivity.transformDivisor_of_isPullback_divisor hZn hXn' hbir (hMc i) hp]
    refine ⟨hlc, k, c, M, hMc, hpush', fun C' hC' x hx => ?_⟩
    rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sZ C' c M hMc hpush' hx]
    exact sum_mul_degreeOn_nonneg_of_isRelativelyNef hZn hZ hf.comp_eq hh c E M hEc hMc hpb
      (by rw [← hNE]; exact hnef) C' hC'
  · -- the small case
    intro hsmall
    have hbir : IsBirationalMorphism f := hsmall.isBirationalMorphism
    have hsm : IsSmallMorphism sX sZ f := isSmallMorphism_of_isSmall' hXn hZn hsmall
    obtain ⟨X', _, _, _, _, sX', fp, hfps, hflipOf, hX'pair⟩ :=
      IsProjectiveQFactorialDltPair.exists_isFlipOf_of_isSmallMorphism ⟨hX, hXQ, ⟨n, hKn⟩, hdlt₀⟩
        hdim hΔ₀ hf hsm hZ hρN hamp
    have hX'p := hX'pair.isProjectiveVariety
    have hX'Q := hX'pair.isQFactorial
    obtain ⟨n', hK'⟩ := hX'pair.isCanonicalDivisor
    have hX'n : IsNormalVariety ℂ sX' := ⟨hX'p.toIsVariety, inferInstance⟩
    haveI : MMP.Mori.IsVariety ℂ sX' := hX'n.1
    have hfpsm := hflipOf.isSmallMorphism_flip
    haveI : IsProper fp := hfpsm.isProper
    have hbir' := hfpsm.isBirationalMorphism
    haveI : IsDominant fp := hbir'.isDominant
    haveI : IsDominant f := hbir.isDominant
    haveI : Surjective fp := ⟨surjective_of_isProper_of_isDominant fp⟩
    haveI : IsSeparated (f ≫ sZ) := by rw [hf.comp_eq]; exact hXn.1.toIsSeparated
    haveI : IsSeparated f := IsSeparated.of_comp f sZ
    haveI : IsSeparated sZ := hZn.1.toIsSeparated
    haveI := isSeparated_terminal' sZ
    haveI : IsSeparated sX' := hX'n.1.toIsSeparated
    haveI : LocallyOfFiniteType sX' := hX'n.1.toLocallyOfFiniteType
    haveI : QuasiCompact sX' := hX'n.1.toQuasiCompact
    haveI : IsProper sX' := isProper_of_isProjectiveMorphism _ hX'p.isProjective
    have hnn : n' = n := by
      have h1 := hK'.topologicalKrullDim_eq
      have h2 := hKn.topologicalKrullDim_eq
      have h3 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hbir
      have h4 := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX' hbir'
      rw [h3, h2] at h4
      rw [h1] at h4
      exact_mod_cast h4.symm
    subst hnn
    -- every negative rational boundary has the same flip
    have htrans : ∀ Δ : QDivisor X, IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R' →
        IsFlipOf sX sZ sX' (Divisor.toQDivisor K + Δ) f fp := fun Δ hΔ =>
      IsFlipOf.of_isNegativeExtremalRayOf hX hXQ hklt ⟨n', hKn⟩ hΔ₀ hf hΔ hΔ₀ hflipOf
    have hamplΔ : ∀ Δ : QDivisor X, IsNegativeExtremalRayOf sX (Divisor.toQDivisor K + Δ) R' →
        (Divisor.toQDivisor (flipTransform f fp K) +
          flipTransform f fp Δ).HasRelativelyAmpleMultiple fp := fun Δ hΔ => by
      have := (htrans Δ hΔ).hasRelativelyAmpleMultiple_flip
      rwa [map_add, flipTransform_toQDivisor'] at this
    have hampl' : ∀ (c : MMP.Mori.PrimeDivisor X → ℝ) (Δ : QDivisor X), (∀ P, |c P| < η) →
        QDivisor.toRDivisor Δ =
          B + ∑ P ∈ B.support, c P • Divisor.toRDivisor (Finsupp.single P 1) →
        (Divisor.toQDivisor (flipTransform f fp K) +
          flipTransform f fp Δ).HasRelativelyAmpleMultiple fp := fun c Δ hc hΔ =>
      hamplΔ Δ (hnegΔ c Δ hc hΔ)
    -- the step diagram
    have hstep : IsProjectiveElementaryDltStep sX sZ sX' K Δ₀ R' f fp
        (flipTransform f fp Δ₀) :=
      { isProjectiveQFactorialDltPair := ⟨hX, hXQ, ⟨n', hKn⟩, hdlt₀⟩
        isNegativeExtremalRayOf := hΔ₀
        isContractionOfRay := hf
        isBirationalMorphism := hbir
        comp_eq := hfps
        eq_flipTransform := rfl
        flip_or_divisorial := Or.inl ⟨hsm, hflipOf⟩ }
    have hdiag := IsProjectiveElementaryDltStep.isFourfoldStepDiagram hstep hdim hZ hρN hamp
    -- the open over which both contractions are isomorphisms
    set V := biregularLocus f ⊓ biregularLocus fp with hV
    haveI : IsIso (f ∣_ V) :=
      isBiregular_iff_le_biregularLocus.mpr (inf_le_left : V ≤ biregularLocus f)
    haveI : IsIso (fp ∣_ V) :=
      isBiregular_iff_le_biregularLocus.mpr (inf_le_right : V ≤ biregularLocus fp)
    obtain ⟨hX'V, hexc⟩ := flip_open_props hbir hfpsm
    have hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V := fun x hx => by
      have := (flip_open_props hbir' hsm).1 x hx
      rw [hV, inf_comm]
      exact this
    have hX'n' : IsNormalVariety ℂ (fp ≫ sZ) := by rw [hfps]; exact hX'n
    have hXn' : IsNormalVariety ℂ (f ≫ sZ) := by rw [hf.comp_eq]; exact hXn
    have hTR' : OneCycle.numericalClass sX (T.cycle ℝ) ∈ R' := by
      rw [hRT]; exact ⟨1, zero_le_one, one_smul _ _⟩
    have hTf : T.IsContractedBy f := (hf.isContractedBy_iff T).mpr hTR'
    have hnotiso' : ¬ IsIso fp :=
      not_isIso_of_isQCartier_flipTransform hZn hXn' hfps hbir hf.comp_eq V hXV hX'V hΔ₀.1
        hflipOf.isQCartier_flip hTf (hΔ₀.2.2 _ hTR' hT0).ne
    have hρ' := relativePicardNumber_flip_eq_one hX hXQ hX'p hX'Q hKn hklt hΔ₀ hRT hf hZ
      hflipOf hdiag.isIso_app_plus hnotiso'
    have hdlt' := isRealDltPair_flipTransform_of_isSmallMorphism hXn hX'n hZn hXQ hX'Q
      hf.comp_eq hfps hbir hfpsm hKn hK' hB hη hanti' hampl'
    -- `K⁺ + B⁺` is `f⁺`-ample
    have hamplB : IsRelativelyAmple fp
        (logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B)) := by
      obtain ⟨ι, _, _, Δ, w, c, hw, hw1, hwB, hc, hΔc⟩ := exists_rat_decomposition B hη
      have hsum : logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B) =
          ∑ i, w i • QDivisor.toRDivisor (Divisor.toQDivisor (flipTransform f fp K) +
            flipTransform f fp (Δ i)) := by
        simp only [map_add, QDivisor.toRDivisor_toQDivisor, smul_add, Finset.sum_add_distrib,
          ← Finset.sum_smul, hw1, one_smul, logCanonicalDivisor, ← flipTransform_qtoRDivisor]
        rw [← flipTransform_sum_smul, hwB]
      rw [hsum]
      exact isRelativelyAmple_sum (fun i => isRelativelyAmple_of_hasRelativelyAmpleMultiple fp
        (hampl' _ _ (hc i) (hΔc i))) hw
    refine ⟨X', inferInstance, inferInstance, inferInstance, inferInstance, sX', fp,
      { isQuasiProjectiveVariety_target := by
          haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
          exact AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sZ
        isNegativeExtremalContraction := hcontr
        isSmall := hsmall
        isBirationalMorphism := hbir
        isProjectiveMorphism := hf.isProjectiveMorphism
        not_isIso := fun hiso => by
          haveI := hiso
          exact not_isContractedBy_of_isIso f T hTf
        isCanonicalDivisor_flip := ⟨n', hK'⟩
        isSmall_flip := isSmall_of_isSmallMorphism' hfpsm hdiag.isIso_app_plus
        isBirationalMorphism_flip := hbir'
        isProjectiveMorphism_flip := hflipOf.isProjectiveMorphism_flip
        not_isIso_flip := hnotiso'
        relativePicardNumber_flip := hρ'
        isRelativelyAmple_flip := hamplB
        eq_flipTransform := rfl }, hX'p, hX'Q, hdiag.dim_plus, hdlt', ?_, ?_⟩
    · -- descent to both small models
      intro N hN hnull
      obtain ⟨k, c, E, M, -, hMc, hpb, hNE⟩ := hdescent hbir N hN hnull
      refine ⟨∑ i, c i • Divisor.toRDivisor (M i), ⟨k, c, M, E, hMc, rfl, hpb, hNE⟩,
        k, c, M, fun i => flipTransform f fp (E i), hMc, rfl, fun i => ?_, ?_⟩
      · obtain ⟨hB, hp⟩ := hpb i
        exact isPullback_flipTransform hZn hXn' hX'n' hbir hbir' V hXV hX'V (hMc i) hp
      · rw [hNE, flipTransform_sum_smul]
        simp only [flipTransform_toRDivisor]
    · -- lc and nef transfer
      intro B' hB' hnef hnull
      obtain ⟨m', r', L', hL', hKB', -⟩ := id hnef
      have hv0' : presDeg sX r' L' hL' v = 0 := by
        have h1 := hnull T hTg hTR m' r' L' _ (isRIntersectionNumber_presDeg r' L' hL' hKB' T)
        have hvR : v ∈ R' := by rw [hR'v]; exact ⟨1, zero_le_one, one_smul _ _⟩
        rw [hRT] at hvR
        obtain ⟨c, -, hc⟩ := hvR
        rw [← hc, map_smul, h1, smul_zero]
      have hpush : ∀ Δ : QDivisor X, RationalMap.transformDivisor (X := X) f.toRationalMap Δ =
          RationalMap.transformDivisor (X := X') fp.toRationalMap (flipTransform f fp Δ) :=
        fun Δ => (transformDivisor_inverseTransformDivisor' hZn hX'n' hbir' _).symm
      have hcmpB' : ∀ (D : DivisorOver ℂ sX) (D' : DivisorOver ℂ sX'), IsProper D.f →
          IsProper D'.f →
          D.valuation.comap (functionFieldMap f) = D'.valuation.comap (functionFieldMap fp) →
          D'.IsExceptional → ∀ (n₀ n₁ : ℕ) (a a' : ℝ),
            MMP.Intersection.IsLogDiscrepancy sX n₀ B' D a →
            MMP.Intersection.IsLogDiscrepancy sX' n₁ (flipTransform f fp B') D' a' → a ≤ a' := by
        intro D D' hD hD' hvD hE' n₀ n₁ a a' ha ha'
        refine le_of_forall_neg hXn hX'n hXQ hX'Q hKn hK' D D' hD hD'
          (fun B₁ m₁ r₁ L₁ hL₁ hKB₁ hv₁ n₂ n₃ a₁ a₁' ha₁ ha₁' =>
            (realCmp_of_negative hXn hX'n hZn hf.comp_eq hfps hbir hbir' hXQ hX'Q hKn hK' hR'
              hR'v hantiΔ (fun Δ hΔ => isRelativelyNef_of_hasRelativelyAmpleMultiple'
                (hamplΔ Δ hΔ)) hpush V (fun z hz => by
                  by_cases h1 : z ∈ biregularLocus f
                  · exact Or.inr ⟨fun h2 => hz ⟨h1, h2⟩, hamplΔ⟩
                  · exact Or.inl h1) hexc hL₁ hKB₁ hv₁ D D' hD hD' hvD hE' ha₁ ha₁').1)
          hL' hKB' hv0' hQ₀ hΔ₀v ha ha'
      have hlc : IsRealLcPair sX' (flipTransform f fp B') :=
        isRealLcPair_of_comparison hXn hX'n hZn hf.comp_eq hfps hbir hbir' V hX'V hK' hB'
          (fun P P' hPP => flipTransform_apply_of_mem' hbir fp.surjective V hPP
            (hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le) B')
          (isRCartier_of_isQFactorial hX'Q _) hcmpB'
      -- nefness over `S`
      obtain ⟨k, c, E, M, hEc, hMc, hpb, hNE⟩ := hdescent hbir (logCanonicalDivisor K B')
        ⟨m', r', L', hL', by rw [hKB']; simp only [toRDivisor_eq_mapCoeffs]⟩ hnull
      haveI : Surjective f := ⟨hf.surjective⟩
      have hpbp : ∀ i, ∃ hB, (M i).IsPullback fp hB (flipTransform f fp (E i)) := fun i => by
        obtain ⟨hB₁, hp⟩ := hpb i
        exact isPullback_flipTransform hZn hXn' hX'n' hbir hbir' V hXV hX'V (hMc i) hp
      have hEc' : ∀ i, Divisor.IsCartier (flipTransform f fp (E i)) := fun i => by
        obtain ⟨hB₁, hp⟩ := hpbp i
        exact hp.isCartier (hMc i)
      have hpush' : logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B') =
          ∑ i, c i • Divisor.toRDivisor (flipTransform f fp (E i)) := by
        have : logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B') =
            flipTransform f fp (logCanonicalDivisor K B') := by
          rw [logCanonicalDivisor, logCanonicalDivisor, map_add, flipTransform_toRDivisor]
        rw [this, hNE, flipTransform_sum_smul]
        simp only [flipTransform_toRDivisor]
      refine ⟨hlc, k, c, fun i => flipTransform f fp (E i), hEc', hpush', fun C'' hC'' x hx => ?_⟩
      rw [MMP.Flips.eq_sum_degreeOn_of_isRIntersectionNumber ℂ sX' C'' c _ hEc' hpush' hx]
      have hdeg : ∀ i, (Divisor.degreeOn ℂ sX' C''.ι C''.dim_le (flipTransform f fp (E i))
          (hEc' i) : ℝ) =
          if h : IsProperCurve sZ (fp C''.point) then
            haveI := ProperCurve.isProper_ι_comp (⟨fp C''.point, h⟩ : ProperCurve sZ)
            (residueFieldDegree fp C''.point : ℝ) * ((M i).degreeOn ℂ sZ
              (⟨fp C''.point, h⟩ : ProperCurve sZ).ι
                (⟨fp C''.point, h⟩ : ProperCurve sZ).dim_le (hMc i) : ℝ)
          else 0 := fun i => by
        obtain ⟨hB₁, hp⟩ := hpbp i
        rw [degreeOn_isPullback hfps (hMc i) hp (hEc' i) C'']
        split_ifs <;> push_cast <;> rfl
      by_cases hpc : IsProperCurve sZ (fp C''.point)
      · simp only [hdeg, dif_pos hpc]
        have hC'h : (⟨fp C''.point, hpc⟩ : ProperCurve sZ).IsContractedBy h := by
          intro y hy
          have hcl : closure (fp '' ({C''.point} : Set X')) = fp '' closure {C''.point} :=
            fp.isClosedMap.closure_image_eq_of_continuous fp.continuous _
          rw [Set.image_singleton] at hcl
          rw [hcl] at hy
          obtain ⟨x, hx, rfl⟩ := hy
          have := hC'' x hx
          rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
        have := sum_mul_degreeOn_nonneg_of_isRelativelyNef hZn hZ hf.comp_eq hh c E M hEc hMc hpb
          (by rw [← hNE]; exact hnef) _ hC'h
        have hre : ∑ i, c i * ((residueFieldDegree fp C''.point : ℝ) *
            ((M i).degreeOn ℂ sZ (⟨fp C''.point, hpc⟩ : ProperCurve sZ).ι
              (⟨fp C''.point, hpc⟩ : ProperCurve sZ).dim_le (hMc i) : ℝ)) =
            (residueFieldDegree fp C''.point : ℝ) * ∑ i, c i * ((M i).degreeOn ℂ sZ
              (⟨fp C''.point, hpc⟩ : ProperCurve sZ).ι
                (⟨fp C''.point, hpc⟩ : ProperCurve sZ).dim_le (hMc i) : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
        rw [hre]
        exact mul_nonneg (Nat.cast_nonneg _) this
      · simp only [hdeg, dif_neg hpc, mul_zero, Finset.sum_const_zero, le_refl]

end Proof_lem_fourfold_real_dlt_fourfold_elementary_step

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **Elementary steps of real dlt fourfolds.** Let `g : X ⟶ S` be a morphism of projective
complex varieties, `X` a normal `ℚ`-factorial fourfold with canonical divisor `K`, `(X, B)` a dlt
pair with real boundary, and `R` a `(K + B)`-negative extremal ray of `NE̅(X/S)`. There is a
contraction `f : X ⟶ Z`, `h : Z ⟶ S` of `R` over `S`, with `Z` projective, `-(K + B)` `f`-ample and
`ρ(X/Z) = 1`, such that

* if `f` is birational, every `ℝ`-Cartier divisor `N` on `X` null on `R` is a pull-back `f^* M`
  of an `ℝ`-divisor `M` on `Z`;
* if `f` is divisorial, `Z` is `ℚ`-factorial, `(Z, f_* B)` is dlt, and for every lc pair `(X, B')`
  with `K + B'` nef over `S` and null on `R`, `(Z, f_* B')` is lc and `f_* K + f_* B'` is nef
  over `S`;
* if `f` is small, there is a step of an extremal real flip sequence `X ⟶ Z ⟵ X⁺` with canonical
  divisor `K⁺ = (f⁺)⁻¹_* f_* K`, `X⁺` a projective `ℚ`-factorial fourfold, `(X⁺, B⁺)` dlt for
  `B⁺ = (f⁺)⁻¹_* f_* B`; every `ℝ`-Cartier `N` null on `R` is `f^* M` with `f⁺^* M = N⁺`; and for
  every lc pair `(X, B')` with `K + B'` nef over `S` and null on `R`, `(X⁺, B'⁺)` is lc and
  `K⁺ + B'⁺` is nef over `S`. -/
@[mmp "lem_fourfold_real_dlt_fourfold_elementary_step"]
public theorem IsRealDltPair.exists_isRelativeContractionOfFace_of_isExtremalRay
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {B : RDivisor X} {R : Set (RelativeNumericalCurveClasses sX g)}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 4)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hB : IsRealDltPair sX B)
    (hR : IsExtremalRay ℝ
      (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R)
    (hneg : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier),
      logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j) ∧
        ∀ u ∈ R, u ≠ 0 → ∑ j, r j *
          (haveI := (hL j).isInvertibleModule_divisorialSheaf
           RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) < 0) :
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (_ : CompactSpace Z) (_ : IsLocallyNoetherian Z)
      (_ : IsNormal Z)
      (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (h : Z ⟶ S),
      IsRelativeContractionOfFace g R f h ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f ∧
        (IsBirationalMorphism f → ∀ N : RDivisor X, IsCartierCombination N →
          (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
            ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
              IsRIntersectionNumber ℂ sX N r L C x → x = 0) →
          ∃ M : RDivisor Z, IsRCartierPullback f M N) ∧
        ((IsBirationalMorphism f ∧
            ∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) →
          IsQFactorial sZ ∧
            IsRealDltPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B) ∧
            ∀ B' : RDivisor X, IsRealLcPair sX B' →
              IsRelativelyNef ℂ sX g (logCanonicalDivisor K B') →
              (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
                ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
                  IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B') r L C x → x = 0) →
              IsRealLcPair sZ (RationalMap.transformDivisor (X := X) f.toRationalMap B') ∧
                IsRelativelyNef ℂ sZ h
                  (logCanonicalDivisor (RationalMap.transformDivisor (X := X) f.toRationalMap K)
                    (RationalMap.transformDivisor (X := X) f.toRationalMap B'))) ∧
        (IsSmall ℂ sZ sX f →
          ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X')
            (_ : IsLocallyNoetherian X') (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ))
            (fp : X' ⟶ Z),
            IsRealFlipStep sX sZ sX' K B (flipTransform f fp K) (flipTransform f fp B) f fp ∧
              MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧
              topologicalKrullDim X' = 4 ∧ IsRealDltPair sX' (flipTransform f fp B) ∧
              (∀ N : RDivisor X, IsCartierCombination N →
                (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
                  ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
                    IsRIntersectionNumber ℂ sX N r L C x → x = 0) →
                ∃ M : RDivisor Z,
                  IsRCartierPullback f M N ∧ IsRCartierPullback fp M (flipTransform f fp N)) ∧
              ∀ B' : RDivisor X, IsRealLcPair sX B' →
                IsRelativelyNef ℂ sX g (logCanonicalDivisor K B') →
                (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
                  ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
                    IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B') r L C x → x = 0) →
                IsRealLcPair sX' (flipTransform f fp B') ∧
                  IsRelativelyNef ℂ sX' (fp ≫ h)
                    (logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B'))) :=
                      by revert X S sX sS g K B R hX hS hg hXQ hdim hK hB hR hneg; first | exact Proof_lem_fourfold_real_dlt_fourfold_elementary_step.solution | exact Proof_lem_fourfold_real_dlt_fourfold_elementary_step.solution _ | exact Proof_lem_fourfold_real_dlt_fourfold_elementary_step.solution _ _ | exact Proof_lem_fourfold_real_dlt_fourfold_elementary_step.solution _ _ _ | exact Proof_lem_fourfold_real_dlt_fourfold_elementary_step.solution _ _ _ _

end MMP.Fourfold

