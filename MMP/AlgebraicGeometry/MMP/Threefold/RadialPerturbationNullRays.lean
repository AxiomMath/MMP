module

import MMP.AlgebraicGeometry.MMP.ConeTheorem.CommonRayCurveBound
import MMP.AlgebraicGeometry.MMP.Threefold.PositiveIntersectionGap
public import MMP.AlgebraicGeometry.MMP.Fourfold.CanonicalDifficulty
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.Intersection.ConeOfCurves.RelativeRayAbsolute
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.MMP.Termination.RealCanonicalDifficulty
import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
import MMP.AlgebraicGeometry.Intersection.PairingSeparation
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Singularities.Discrepancy.Uniqueness
import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.MonomialValuationSnc
import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldStabilizedTail
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.CrepantBoundary
import MMP.AlgebraicGeometry.Singularities.DivisorialLogDiscrepancyFormulas
import MMP.AlgebraicGeometry.MMP.Fourfold.PairSingularities
import MMP.AlgebraicGeometry.Singularities.Surface.ReducedBoundaryLc
import MMP.AlgebraicGeometry.Resolution.SncPreservingLogResolution
import MMP.AlgebraicGeometry.Resolution.SNCWeight.FinalModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Singularities.KltSmallDiscrepancyCenters
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Resolution.SmoothBlowupCanonical
import MMP.AlgebraicGeometry.Intersection.ProperCurveDegree
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Divisor.Negativity.FibreSupport
import MMP.AlgebraicGeometry.MMP.MinimalModel.CommonModelNefWeakModels
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.MMP.Flip.RelativeNumericalFlopsLemmas
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.SurfaceMatrix
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.Corollaries
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.Divisor.ExceptionalNullDivisor
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Divisor.Negativity.QCartierProper
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.MMP.Contraction.RelativeLineBundleDescent
import MMP.AlgebraicGeometry.Singularities.KltDiscrepancyBasics
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import MMP.AlgebraicGeometry.MMP.Fourfold.Flip
import MMP.AlgebraicGeometry.Divisor.Pullback
import MMP.AlgebraicGeometry.Singularities.RealKltRationalDecomposition
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
public import Mathlib
public import MMP.Attr

/-!
# Small radial perturbations of a nef real adjoint have only null negative rays

Let `g : X ⟶ S` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
threefold, let `(X, B)` and `(X, C)` be real klt pairs, and suppose `D = K_X + B` is nef over
`S`. Fix rational null-decomposition data for `B`, with weights `rᵢ` and Cartier index `m`, put
`E = K_X + C` and `D_t = (1 - t) D + t E = K_X + (1 - t) B + t C`. There is `ε > 0`, depending
only on the `rᵢ` and `m`, such that for `0 < t < ε` every `D_t`-negative extremal ray of
`NE̅(X/S)` is `D`-null.

Moreover every step of the `D_t`-program over `S` (the contraction `f : X ⟶ Z` over `S` of a
`D_t`-negative extremal ray, followed by the identity of `Z` when `f` is divisorial, or by the
`D_t`-flip when `f` is small) is `D`-null; on the new model the transformed `D` is again nef
over `S`, the transformed rational boundaries are rational null-decomposition data for the
transformed `B` with the same weights and the same `m`, and the transformed `C` is again a real
klt boundary. Since `ε` depends only on the weights and `m`, the same `ε` serves at the next
step, and induction gives the assertion along the whole program.

Let `τ > 0` be the gap of the positive values of `∑ rᵢ nᵢ / m` over integers `nᵢ ≥ -6m`;
the proof takes `ε = τ / (2 (τ + 6))`.

For `0 < t < ε` and a `D_t`-negative extremal ray `R` of `NE̅(X/S)`, `D_t = K_X + (1-t) B + t C`,
the image of `R` in `N₁(X)` is an extremal ray of `NE̅(X)`. Writing
`D_t = (1 - t) ∑ rᵢ (K_X + Bᵢ) + t (K_X + C)`, one of the adjoints `K_X + Bᵢ`, `K_X + C` is
negative on it, so it contains a rational curve `ℓ` with `(K_X + Bᵢ) · ℓ ≥ -6` and
`(K_X + C) · ℓ ≥ -6`. As `(K_X + Bᵢ) · ℓ ∈ m⁻¹ ℤ`, either `D · ℓ = 0` or `D · ℓ ≥ τ`, and in the
second case `D_t · ℓ ≥ (1 - t) τ - 6 t > 0`, which is impossible. So `D` vanishes on `R`.

A step `X ⟶ Z ⟵ X⁺` of the `D_t`-program has `ρ(X/Z) = 1`, so `NE̅(X/Z)` is a single
`D_t`-negative extremal ray, and the first part, applied over `Z`, shows that the step is
`D`-null.

## Main results

* `MMP.Fourfold.exists_pos_forall_isExtremalRay_null_and_isNegativeExtremalContraction`.

## Implementation notes

* The dependence of `ε` on the data only through the weights and `m` is expressed by producing
  `ε` as a function of `(s, r, m)` before the threefold is given; the constant used for data
  `ν` is `ε ν.s ν.weight ν.m`.
* An `ℝ`-divisor is paired with a class of `N₁(X/S)` (or of `N₁(X)`) through a presentation
  `∑ cⱼ Lⱼ` by Cartier divisors, as `∑ cⱼ deg 𝒪_X(Lⱼ)`, computed with
  `MMP.Mori.RelativeNumericalCurveClasses.degree` (or `MMP.Mori.NumericalCurveClasses.degree`).
  The pairing does not depend on the presentation, so negativity is asked of one presentation
  and nullness is asserted for all of them.
* A step of the program is stated through its diagram `X ⟶ Z ⟵ X⁺`: `f` is a birational
  projective `D_t`-negative extremal contraction (`MMP.Flips.IsNegativeExtremalContraction`:
  `-D_t` is `f`-ample and `ρ(X/Z) = 1`) over `S`, and `f⁺ : X⁺ ⟶ Z` is a small projective
  birational contraction from a `ℚ`-factorial projective threefold with the transformed `D_t`
  ample over `Z`. In the divisorial case `f⁺` is the identity of `Z`; in the small case it is the
  `D_t`-flip. All divisors are transported by `MMP.Mori.flipTransform f f⁺`, which in the
  divisorial case is the push-forward `f_*`, and the canonical divisor of `X⁺` is the transform of
  `K_X`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

@[expose] public section

open AlgebraicGeometry hiding IsProjectiveVariety
open CategoryTheory TopologicalSpace MMP.Mori

namespace MMP.Fourfold

section ErasedIntegral

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Pairings of presentations with numerical classes -/

section Pairing

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_curveNormalization (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := Oai4C1.CommonModel.isBirationalMorphism_of_isBirational _
        (Scheme.isBirational_normalization C.scheme hX) }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (MMP.Fourfold.Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

variable [CompactSpace X]

variable (sX) in
/-- The linear form `z ↦ ∑ᵢ cᵢ (z · 𝒪_X(Mᵢ))` on `N₁(X)` of a presentation `∑ᵢ cᵢ Mᵢ` by
Cartier divisors. -/
private noncomputable def absForm {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) : NumericalCurveClasses sX →ₗ[ℝ] ℝ :=
  ∑ i, c i • (haveI := (hM i).isInvertibleModule_divisorialSheaf
    NumericalCurveClasses.degree sX (M i).divisorialSheaf)

private theorem absForm_apply {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (u : NumericalCurveClasses sX) :
    absForm sX c M hM u = ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
      NumericalCurveClasses.degree sX (M i).divisorialSheaf u) := by
  simp [absForm, LinearMap.sum_apply]

/-- On the class of a curve `C`, the form of `∑ᵢ cᵢ Mᵢ` is `∑ᵢ cᵢ deg_C 𝒪_X(Mᵢ)`. -/
private theorem absForm_cycle {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Divisor X)
    (hM : ∀ i, (M i).IsCartier) (C : ProperCurve sX) :
    absForm sX c M hM (OneCycle.numericalClass sX (C.cycle ℝ)) =
      ∑ i, c i * ((M i).degreeOn k sX C.ι C.dim_le (hM i) : ℝ) := by
  rw [absForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (hM i).isInvertibleModule_divisorialSheaf
  exact congrArg (c i * ·) (OneCycle.degree_cycle ℝ _ C)

omit [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- Linear forms on `N₁(X)` which agree on the classes of curves are equal. -/
private theorem linearMap_ext_numericalClass {φ ψ : NumericalCurveClasses sX →ₗ[ℝ] ℝ}
    (h : ∀ C : ProperCurve sX, φ (OneCycle.numericalClass sX (C.cycle ℝ)) =
      ψ (OneCycle.numericalClass sX (C.cycle ℝ))) : φ = ψ := by
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun C => LinearMap.ext_ring ?_)
  exact h C

omit [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- A continuous linear form on `N₁(X/S)` which is nonnegative on the class of every curve
contracted by `g` is nonnegative on `NE̅(X/S)`. -/
private theorem nonneg_of_mem_relativeClosedConeOfCurves {S : Scheme.{0}} {g : X ⟶ S}
    (φ : RelativeNumericalCurveClasses sX g →ₗ[ℝ] ℝ) (hφc : Continuous φ)
    (hφ : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), 0 ≤ φ (C.relativeClass g hC))
    {z : RelativeNumericalCurveClasses sX g}
    (hz : z ∈ (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g))) :
    0 ≤ φ z := by
  have hcone : (relativeConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) ⊆
      {w | 0 ≤ φ w} := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨C, hC⟩, rfl⟩ := hx
      exact hφ C hC
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
      linarith
    | smul a x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [show a • x = (a : ℝ) • x from rfl, map_smul, smul_eq_mul]
      exact mul_nonneg a.2 hx
  rw [coe_relativeClosedConeOfCurves] at hz
  exact closure_minimal hcone (isClosed_le continuous_const hφc) hz

/-- Two presentations of the same `ℝ`-divisor give the same linear form on `N₁(X)`. -/
private theorem absForm_eq_of_eq {n n' : ℕ} {c : Fin n → ℝ} {M : Fin n → Divisor X}
    (hM : ∀ i, (M i).IsCartier) {c' : Fin n' → ℝ} {M' : Fin n' → Divisor X}
    (hM' : ∀ i, (M' i).IsCartier)
    (h : ∑ i, c i • Divisor.toRDivisor (M i) = ∑ i, c' i • Divisor.toRDivisor (M' i)) :
    absForm sX c M hM = absForm sX c' M' hM' := by
  refine linearMap_ext_numericalClass fun C => ?_
  rw [absForm_cycle, absForm_cycle]
  exact (IsRIntersectionNumber.eq_and_linear k sX C).1 _ c M c' M' _ _
    (isRIntersectionNumber_sum_degreeOn hM rfl C) (isRIntersectionNumber_sum_degreeOn hM' h C)

/-- The degree on a relative class is the degree on its image in `N₁(X)`. -/
private theorem relDegree_eq {S : Scheme.{0}} (g : X ⟶ S) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (u : RelativeNumericalCurveClasses sX g) :
    RelativeNumericalCurveClasses.degree sX g L u =
      NumericalCurveClasses.degree sX L (relativeToAbsolute sX g u) := by
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX g u
  rw [isNaturalRelativeMap_relativeToAbsolute sX g Z]
  rfl

/-- The relative pairing of a presentation is its absolute pairing after `N₁(X/S) → N₁(X)`. -/
private theorem relSum_eq {S : Scheme.{0}} (g : X ⟶ S) {n : ℕ} (c : Fin n → ℝ)
    (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier) (u : RelativeNumericalCurveClasses sX g) :
    ∑ i, c i * (haveI := (hM i).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sX g (M i).divisorialSheaf u) =
      absForm sX c M hM (relativeToAbsolute sX g u) := by
  rw [absForm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (hM i).isInvertibleModule_divisorialSheaf
  rw [relDegree_eq]

/-- The pairing of a presentation with `N₁(X/S)` is continuous. -/
private theorem continuous_absForm_comp {S : Scheme.{0}} (g : X ⟶ S) {n : ℕ} (c : Fin n → ℝ)
    (M : Fin n → Divisor X) (hM : ∀ i, (M i).IsCartier) :
    Continuous (absForm sX c M hM ∘ₗ relativeToAbsolute sX g) := by
  refine (continuous_finset_sum _ fun i _ => ?_).congr (relSum_eq g c M hM)
  have := (hM i).isInvertibleModule_divisorialSheaf
  exact continuous_const.mul (RelativeNumericalCurveClasses.continuous_degree sX g _)

end Pairing

/-! ### Presentations by Cartier divisors -/

section Presentation

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X]

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is a real combination of Cartier divisors. -/
private theorem exists_cartierPresentation (hQ : IsQFactorial sX) (D : RDivisor X) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X), (∀ j, (L j).IsCartier) ∧
      D = ∑ j, c j • Divisor.toRDivisor (L j) := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X => hQ.2 (Finsupp.single P 1)
  let e := D.support.equivFin
  let p : Fin D.support.card → MMP.Mori.PrimeDivisor X := fun j => (e.symm j).1
  refine ⟨D.support.card, fun j => D (p j) / m (p j),
    fun j => ((m (p j) : ℕ) : ℤ) • Finsupp.single (p j) 1, fun j => hmC _, ?_⟩
  ext P
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  let F : MMP.Mori.PrimeDivisor X → ℝ := fun Q => if Q = P then D Q else 0
  have hF : ∀ j, D (p j) / m (p j) * ((Divisor.toRDivisor
      (((m (p j) : ℕ) : ℤ) • Finsupp.single (p j) (1 : ℤ))) P) = F (p j) := fun j => by
    have hm0 : ((m (p j) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hm _).ne'
    change D (p j) / m (p j) * (((((m (p j) : ℕ) : ℤ) • Finsupp.single (p j) (1 : ℤ)) P : ℤ) :
      ℝ) = F (p j)
    by_cases hP : p j = P
    · simp only [F, hP, if_true, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul,
        mul_one, Int.cast_natCast]
      rw [← hP]; field_simp
    · simp [F, hP, Finsupp.single_apply]
  rw [Finset.sum_congr rfl fun j _ => hF j]
  rw [show (∑ j, F (p j)) = ∑ Q : D.support, F Q from
    Equiv.sum_comp e.symm (fun Q : D.support => F Q), Finset.sum_coe_sort D.support F]
  rw [Finset.sum_ite_eq' D.support P]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h)

end Presentation

/-! ### The arithmetic gap -/

/-- The arithmetic gap: for positive weights `rᵢ` summing to one and `m > 0`, the positive values
of `∑ rᵢ nᵢ / m` over integer vectors with `nᵢ / m ≥ -6` are bounded below by some `τ > 0`. -/
private theorem exists_pos_le_sum {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hr1 : ∑ i, r i = 1) (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ n : ι → ℤ, (∀ i, -6 ≤ (n i : ℝ) / m) →
      0 < ∑ i, r i * ((n i : ℝ) / m) → τ ≤ ∑ i, r i * ((n i : ℝ) / m) := by
  classical
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set f : (ι → ℤ) → ℝ := fun n => ∑ i, r i * ((n i : ℝ) / m) with hf
  set S : Finset ℝ := ((Fintype.piFinset fun i =>
    Finset.Icc (-6 * (m : ℤ)) ⌊7 * (m : ℝ) / r i⌋).image f).filter (0 < ·)
  have hne : (insert 1 S).Nonempty := Finset.insert_nonempty _ _
  refine ⟨(insert 1 S).min' hne, ?_, fun n hn hpos => ?_⟩
  · rcases Finset.mem_insert.mp (Finset.min'_mem _ hne) with h | h
    · rw [h]; exact one_pos
    · exact (Finset.mem_filter.mp h).2
  have hn' : ∀ j, (0 : ℝ) ≤ n j + 6 * m := fun j => by
    have := hn j; rw [le_div_iff₀ hmR] at this; linarith
  by_cases h1 : f n ≤ 1
  · refine Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨n, Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr
        ⟨by exact_mod_cast (by push_cast; linarith [hn' i] : ((-6 * (m : ℤ) : ℤ) : ℝ) ≤ n i),
          Int.le_floor.mpr ?_⟩, rfl⟩, hpos⟩))
    have hsum : ∑ j, r j * ((n j : ℝ) + 6 * m) = m * f n + 6 * m := by
      simp only [hf, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hr1, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by field_simp
      · ring
    have hle : r i * ((n i : ℝ) + 6 * m) ≤ ∑ j, r j * ((n j : ℝ) + 6 * m) :=
      Finset.single_le_sum (f := fun j => r j * ((n j : ℝ) + 6 * m))
        (fun j _ => mul_nonneg (hr j).le (hn' j)) (Finset.mem_univ i)
    rw [le_div_iff₀ (hr i)]
    nlinarith [hr i, hn' i]
  · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (not_le.mp h1).le

/-- The gap, for arbitrary data: when the weights are positive with sum one and `m > 0` it is the
gap of `exists_pos_le_sum`. -/
private theorem exists_gap (s : ℕ) (r : Fin s → ℝ) (m : ℕ) :
    ∃ τ : ℝ, 0 < τ ∧ ((∀ i, 0 < r i) → ∑ i, r i = 1 → 0 < m →
      ∀ n : Fin s → ℤ, (∀ i, -6 ≤ (n i : ℝ) / m) →
        0 < ∑ i, r i * ((n i : ℝ) / m) → τ ≤ ∑ i, r i * ((n i : ℝ) / m)) := by
  by_cases h : (∀ i, 0 < r i) ∧ ∑ i, r i = 1 ∧ 0 < m
  · obtain ⟨τ, hτ, hg⟩ := exists_pos_le_sum r h.1 h.2.1 m h.2.2
    exact ⟨τ, hτ, fun _ _ _ => hg⟩
  · exact ⟨1, one_pos, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩

/-- The gap `τ(s, r, m)`. -/
private noncomputable def gap (s : ℕ) (r : Fin s → ℝ) (m : ℕ) : ℝ :=
  (exists_gap s r m).choose

private theorem gap_pos (s : ℕ) (r : Fin s → ℝ) (m : ℕ) : 0 < gap s r m :=
  (exists_gap s r m).choose_spec.1

private theorem le_gap (s : ℕ) (r : Fin s → ℝ) (m : ℕ) (hr : ∀ i, 0 < r i)
    (hr1 : ∑ i, r i = 1) (hm : 0 < m) (n : Fin s → ℤ) (hn : ∀ i, -6 ≤ (n i : ℝ) / m)
    (hpos : 0 < ∑ i, r i * ((n i : ℝ) / m)) : gap s r m ≤ ∑ i, r i * ((n i : ℝ) / m) :=
  (exists_gap s r m).choose_spec.2 hr hr1 hm n hn hpos

/-- The radius `ε(s, r, m) = τ / (2 (τ + 6))`. -/
private noncomputable def eps (s : ℕ) (r : Fin s → ℝ) (m : ℕ) : ℝ :=
  gap s r m / (2 * (gap s r m + 6))

private theorem eps_pos (s : ℕ) (r : Fin s → ℝ) (m : ℕ) : 0 < eps s r m := by
  have := gap_pos s r m
  unfold eps
  positivity

private theorem eps_lt_one (s : ℕ) (r : Fin s → ℝ) (m : ℕ) : eps s r m < 1 := by
  have := gap_pos s r m
  unfold eps
  rw [div_lt_one (by positivity)]
  linarith

/-- **The radial gap.** If `a ≥ 0`, `a > 0` forces `a ≥ τ`, `b ≥ -6` and
`(1 - t) a + t b < 0` for some `0 < t < τ / (2 (τ + 6))`, then `a = 0`. -/
private theorem eq_zero_of_radial_gap {τ t a b : ℝ} (hτ : 0 < τ) (ht0 : 0 < t)
    (ht : t < τ / (2 * (τ + 6))) (ha : 0 ≤ a) (hgap : 0 < a → τ ≤ a) (hb : -6 ≤ b)
    (hneg : (1 - t) * a + t * b < 0) : a = 0 := by
  have h1 : t * (2 * (τ + 6)) < τ := (lt_div_iff₀ (by positivity)).mp ht
  refine le_antisymm (not_lt.mp fun hpos => ?_) ha
  have := hgap hpos
  have ht1 : 1 - t > 0 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this ht1.le, mul_le_mul_of_nonneg_left hb ht0.le]

/-! ### Rational klt boundaries -/

/-- On a klt pair every boundary coefficient is `< 1`: the log discrepancy `1 - b_P` of a prime
divisor `P` of `Y` is positive. -/
private theorem coeff_lt_one_of_isKltPair {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    (hΘ : IsKltPair sY Θ) (P : MMP.Mori.PrimeDivisor Y) : Θ.coeff P < 1 := by
  obtain ⟨hvar, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hvar P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hvar P).f := by
    change IsProper (𝟙 Y); infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hvar ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- If `m (K + B) = L` coefficientwise, then `K + B = (1 / m) L` as real divisors. -/
private theorem toRDivisor_add_eq_smul {Y : Scheme.{0}} {K : Divisor Y} {B : QDivisor Y}
    {m : ℕ} (hm : 0 < m) {L : Divisor Y}
    (hBL : ∀ P, (m : ℚ) * ((K.coeff P : ℚ) + B.coeff P) = L.coeff P) :
    Divisor.toRDivisor K + QDivisor.toRDivisor B = (1 / m : ℝ) • Divisor.toRDivisor L := by
  ext P
  have h : (m : ℝ) * ((K.coeff P : ℝ) + (B.coeff P : ℝ)) = L.coeff P := by exact_mod_cast hBL P
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  change (K.coeff P : ℝ) + (B.coeff P : ℝ) = 1 / m * (L.coeff P : ℝ)
  rw [← h]
  field_simp

/-- A rational klt boundary `B` with `m (K + B)` integral Cartier is klt as a real boundary. -/
private theorem isRealKltPair_toRDivisor {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {K : Divisor Y} {n : ℕ}
    (hK : K.IsCanonicalDivisor sY n) {B : QDivisor Y} (hB : IsKltPair sY B) {m : ℕ} (hm : 0 < m)
    {L : Divisor Y} (hL : L.IsCartier)
    (hBL : ∀ P, (m : ℚ) * ((K.coeff P : ℚ) + B.coeff P) = L.coeff P) :
    IsRealKltPair sY (QDivisor.toRDivisor B) :=
  ⟨hB.1.isPair.1, fun P => by
      rw [QDivisor.coeff_toRDivisor]; exact_mod_cast coeff_lt_one_of_isKltPair hB P,
    ⟨n, K, hK, 1, fun _ => 1 / m, fun _ => L, fun _ => hL, fun P => by
      have h := congrArg (·.coeff P) (toRDivisor_add_eq_smul hm hBL)
      simp only [Fin.sum_univ_one]
      exact h⟩, hB.2⟩

/-! ### Negative rays are null -/

/-- A linear form vanishing at a nonzero point of a ray vanishes on the whole ray. -/
private theorem map_eq_zero_of_ray {V : Type*} [AddCommGroup V] [Module ℝ V]
    (φ : V →ₗ[ℝ] ℝ) {v : V} {R : Set V} (hR : R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w})
    {ℓ : V} (hℓR : ℓ ∈ R) (hℓ : ℓ ≠ 0) (h : φ ℓ = 0) : ∀ u ∈ R, φ u = 0 := by
  subst hR
  obtain ⟨a, -, rfl⟩ := hℓR
  rintro _ ⟨b, -, rfl⟩
  have ha : a ≠ 0 := by rintro rfl; exact hℓ (zero_smul _ _)
  rw [map_smul, smul_eq_mul] at h
  rw [map_smul, (mul_eq_zero.mp h).resolve_left ha, smul_zero]

/-- **Negative rays are null** (the first assertion). -/
private theorem ray_null {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (g : X ⟶ S)
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hg : g ≫ sS = sX)
    {K : Divisor X} {B C : RDivisor X} (hK : K.IsCanonicalDivisor sX 3)
    (ν : RationalNullData sX K B) (hC0 : ∀ P, 0 ≤ C.coeff P) (hC : IsRealKltPair sX C)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX g (MMP.Flips.logCanonicalDivisor K B))
    (t : ℝ) (ht0 : 0 < t) (htε : t < eps ν.s ν.weight ν.m)
    (R : Set (RelativeNumericalCurveClasses sX g))
    (hR : IsExtremalRay ℝ
      (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R)
    (hneg : ∃ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
      Divisor.toRDivisor K + ((1 - t) • B + t • C) = ∑ j, c j • Divisor.toRDivisor (L j) ∧
        ∀ u ∈ R, u ≠ 0 →
          ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
            RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) < 0) :
    ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
      Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
      ∀ u ∈ R, ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
        RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) = 0 := by
  classical
  obtain ⟨n, c, M, hM, heq, hneg⟩ := hneg
  intro n' c' M' hM' heq' u hu
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := ν.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sS := hS
  haveI : QuasiCompact sX := inferInstance
  have hR' := isExtremalRay_image_relativeToAbsolute sX sS g hg hR
  set ι := relativeToAbsolute sX g with hι
  set s := ν.s
  set r := ν.weight
  set m := ν.m
  have hmR : (0 : ℝ) < m := by exact_mod_cast ν.m_pos
  -- the rational adjoints `K + Bᵢ = (1 / m) Lᵢ`
  choose L hLC hLeq using ν.isCartier
  have hBi : ∀ i, Divisor.toRDivisor K + QDivisor.toRDivisor (ν.boundary i) =
      ∑ _j : Fin 1, (1 / m : ℝ) • Divisor.toRDivisor (L i) := fun i => by
    rw [Fin.sum_univ_one]; exact toRDivisor_add_eq_smul ν.m_pos (hLeq i)
  let ΦB : Fin s → NumericalCurveClasses sX →ₗ[ℝ] ℝ := fun i =>
    absForm sX (fun _ : Fin 1 => (1 / m : ℝ)) (fun _ => L i) (fun _ => hLC i)
  -- a presentation of `K + C`
  obtain ⟨nE, cE, ME, hME, hKE⟩ := exists_cartierPresentation ν.isQFactorial (Divisor.toRDivisor K + C)
  let ΦE := absForm sX cE ME hME
  let Φt := absForm sX c M hM
  let ΦD := absForm sX c' M' hM'
  -- the decomposition `D = ∑ rᵢ (K + Bᵢ)` and `D_t = (1 - t) D + t (K + C)`
  have hKB : Divisor.toRDivisor K + B =
      ∑ i, (r i / m) • Divisor.toRDivisor (L i) := by
    have : Divisor.toRDivisor K + B =
        ∑ i, r i • (Divisor.toRDivisor K + QDivisor.toRDivisor (ν.boundary i)) := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
      rw [ν.sum_weight, one_smul, ← ν.eq_sum]
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hBi i, Fin.sum_univ_one, smul_smul]
    ring_nf
  let ΦD₀ := absForm sX (fun i => r i / m) L hLC
  have hΦD₀ : ΦD = ΦD₀ := absForm_eq_of_eq hM' hLC (heq'.symm.trans hKB)
  have hΦD : ΦD = ∑ i, r i • ΦB i := by
    rw [hΦD₀]
    refine LinearMap.ext fun w => ?_
    simp only [ΦD₀, ΦB, absForm_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Fin.sum_univ_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hMt : ∀ j, (Fin.append L ME j).IsCartier := fun j =>
    Fin.addCases (motive := fun j => (Fin.append L ME j).IsCartier)
      (fun i => by simpa using hLC i) (fun i => by simpa using hME i) j
  have hΦt : Φt = (1 - t) • ΦD + t • ΦE := by
    have hsum : Divisor.toRDivisor K + ((1 - t) • B + t • C) =
        ∑ j, Fin.append (fun i => (1 - t) * (r i / m)) (t • cE) j •
          Divisor.toRDivisor (Fin.append L ME j) := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul]
      simp_rw [← smul_smul, ← Finset.smul_sum]
      rw [← hKB, ← hKE]
      module
    rw [show Φt = _ from absForm_eq_of_eq hM hMt (heq.symm.trans hsum), hΦD₀]
    refine LinearMap.ext fun w => ?_
    simp only [ΦD₀, ΦE, absForm_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.smul_apply, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      ring
  -- a generator of `R` and its image
  obtain ⟨v, hv0, hRv⟩ := hR.2
  have hvR : v ∈ R := hRv ▸ ⟨1, zero_le_one, one_smul _ _⟩
  have hιv : ι v ≠ 0 := by
    intro h0
    obtain ⟨v', hv'0, hR'v⟩ := hR'.2
    have : v' ∈ ι '' R := hR'v ▸ ⟨1, zero_le_one, one_smul _ _⟩
    obtain ⟨w, hw, rfl⟩ := this
    rw [hRv] at hw
    obtain ⟨a, -, rfl⟩ := hw
    exact hv'0 (by rw [map_smul, h0, smul_zero])
  have hmemR' : ∀ w ∈ ι '' R, ∃ a : ℝ, 0 ≤ a ∧ w = a • ι v := by
    rintro _ ⟨w, hw, rfl⟩
    rw [hRv] at hw
    obtain ⟨a, ha, rfl⟩ := hw
    exact ⟨a, ha, map_smul _ _ _⟩
  have hΦtv : Φt (ι v) < 0 := by
    have := hneg v hvR hv0
    rwa [relSum_eq] at this
  -- some adjoint is negative on the ray
  have hsome : ∃ j : Option (Fin s),
      (j.elim ΦE ΦB) (ι v) < 0 := by
    by_contra! hall
    have h1 : 0 ≤ ΦD (ι v) := by
      rw [hΦD]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (ν.weight_pos i).le (hall (some i))
    have h2 : 0 ≤ ΦE (ι v) := hall none
    have ht1 : t < 1 := htε.trans (eps_lt_one s r m)
    have := hΦtv
    rw [hΦt, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
      smul_eq_mul] at this
    nlinarith
  obtain ⟨j₀, hj₀⟩ := hsome
  -- the common rational curve
  let Bf : Option (Fin s) → RDivisor X := fun o =>
    o.elim C fun i => QDivisor.toRDivisor (ν.boundary i)
  have hBf0 : ∀ j P, 0 ≤ (Bf j).coeff P := by
    rintro (_ | i) P
    · exact hC0 P
    · change (0 : ℝ) ≤ ((ν.boundary i).coeff P : ℝ); exact_mod_cast ν.boundary_nonneg i P
  have hBf : ∀ j, IsRealKltPair sX (Bf j) := by
    rintro (_ | i)
    · exact hC
    · exact isRealKltPair_toRDivisor hK (ν.isKltPair_boundary i) ν.m_pos (hLC i) (hLeq i)
  have hnegj : ∃ (j₀ : Option (Fin s)) (m₀ : ℕ) (r₀ : Fin m₀ → ℝ) (L₀ : Fin m₀ → Divisor X)
      (hL₀ : ∀ i, (L₀ i).IsCartier),
      Divisor.toRDivisor K + Bf j₀ = ∑ i, r₀ i • Divisor.toRDivisor (L₀ i) ∧
      ∀ u ∈ ι '' R, u ≠ 0 →
        ∑ i, r₀ i * (haveI := (hL₀ i).isInvertibleModule_divisorialSheaf
          NumericalCurveClasses.degree sX (L₀ i).divisorialSheaf u) < 0 := by
    have key : ∀ {m₀ : ℕ} (r₀ : Fin m₀ → ℝ) (L₀ : Fin m₀ → Divisor X)
        (hL₀ : ∀ i, (L₀ i).IsCartier), absForm sX r₀ L₀ hL₀ (ι v) < 0 →
        ∀ u ∈ ι '' R, u ≠ 0 →
          ∑ i, r₀ i * (haveI := (hL₀ i).isInvertibleModule_divisorialSheaf
            NumericalCurveClasses.degree sX (L₀ i).divisorialSheaf u) < 0 := by
      intro m₀ r₀ L₀ hL₀ hlt w hw hw0
      obtain ⟨a, ha, rfl⟩ := hmemR' w hw
      have ha0 : a ≠ 0 := by rintro rfl; exact hw0 (zero_smul _ _)
      rw [← absForm_apply r₀ L₀ hL₀, map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg (lt_of_le_of_ne ha (Ne.symm ha0)) hlt
    rcases j₀ with _ | i
    · exact ⟨none, nE, cE, ME, hME, hKE, key cE ME hME hj₀⟩
    · exact ⟨some i, 1, fun _ => 1 / m, fun _ => L i, fun _ => hLC i, hBi i,
      key (fun _ => 1 / m) (fun _ => L i) (fun _ => hLC i) hj₀⟩
  obtain ⟨ℓ, -, hℓR, hℓ0, hbd⟩ :=
    exists_isRationalCurve_numericalClass_mem_and_neg_six_le ν.isQFactorial hK hBf0 hBf hR'
      hnegj
  set z := OneCycle.numericalClass sX (ℓ.cycle ℝ)
  -- the values on `ℓ`
  have hE6 : -6 ≤ ΦE z := by
    have := hbd none nE cE ME hME hKE
    rwa [← absForm_apply] at this
  let N : Fin s → ℤ := fun i => (L i).degreeOn ℂ sX ℓ.ι ℓ.dim_le (hLC i)
  have hBN : ∀ i, ΦB i z = (N i : ℝ) / m := fun i => by
    simp only [ΦB, z, absForm_cycle, Fin.sum_univ_one, N]
    ring
  have hB6 : ∀ i, -6 ≤ (N i : ℝ) / m := fun i => by
    have := hbd (some i) 1 (fun _ => 1 / m) (fun _ => L i) (fun _ => hLC i) (hBi i)
    rw [← hBN i]
    rwa [← absForm_apply] at this
  have hDz : ΦD z = ∑ i, r i * ((N i : ℝ) / m) := by
    rw [hΦD]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hBN]
  -- `ℓ` comes from a relative class of `R`
  obtain ⟨w₁, hw₁R, hw₁⟩ := hℓR
  obtain ⟨a₁, ha₁, hw₁v⟩ := (hRv ▸ hw₁R : w₁ ∈ {w | ∃ c : ℝ, 0 ≤ c ∧ c • v = w})
  have ha₁0 : 0 < a₁ := by
    refine lt_of_le_of_ne ha₁ fun h => hℓ0 ?_
    rw [← hw₁, ← hw₁v, ← h, zero_smul, map_zero]
  -- nefness of `D` on the relative cone
  have hnefz : 0 ≤ ΦD z := by
    obtain ⟨m₀, r₀, L₀, hL₀, hD₀, hD₀nef⟩ := hnef
    have hΦ : ΦD = absForm sX r₀ L₀ hL₀ := absForm_eq_of_eq hM' hL₀ (heq'.symm.trans hD₀)
    rw [hΦ, ← hw₁]
    refine nonneg_of_mem_relativeClosedConeOfCurves (absForm sX r₀ L₀ hL₀ ∘ₗ ι)
      (continuous_absForm_comp g r₀ L₀ hL₀) (fun A hA => ?_) (hR.1.1 hw₁R)
    change 0 ≤ absForm sX r₀ L₀ hL₀ (OneCycle.numericalClass sX (A.cycle ℝ))
    rw [absForm_cycle]
    exact hD₀nef A hA _ (isRIntersectionNumber_sum_degreeOn hL₀ hD₀ A)
  have hΦtz : Φt z < 0 := by
    rw [← hw₁, ← hw₁v, map_smul, map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg ha₁0 hΦtv
  have hzero : ΦD z = 0 := by
    refine eq_zero_of_radial_gap (gap_pos s r m) ht0 htε hnefz (fun hpos => ?_) hE6 ?_
    · rw [hDz] at hpos ⊢
      exact le_gap s r m ν.weight_pos ν.sum_weight ν.m_pos N hB6 hpos
    · have := hΦtz
      rwa [hΦt, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
        smul_eq_mul] at this
  -- `D` vanishes on the whole ray
  have hzR' : z ∈ ι '' R := ⟨w₁, hw₁R, hw₁⟩
  have hR'eq : ι '' R = {w | ∃ c : ℝ, 0 ≤ c ∧ c • ι v = w} := by
    ext w
    constructor
    · intro hw
      obtain ⟨a, ha, rfl⟩ := hmemR' w hw
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a • v, hRv ▸ ⟨a, ha, rfl⟩, map_smul _ _ _⟩
  rw [relSum_eq]
  exact map_eq_zero_of_ray ΦD hR'eq hzR' hℓ0 hzero (ι u) ⟨u, hu, rfl⟩

/-! ### The steps of the program are `D`-null -/

section Step

variable {k : Type} [Field k]

/-- The natural map `N₁(X/Y) → N₁(X)` is injective: a relative 1-cycle numerically trivial on
`X` is relatively numerically trivial, by definition. -/
private theorem relativeToAbsolute_injective {X Y : Scheme.{0}} (sX : X ⟶ Spec (.of k))
    (f : X ⟶ Y) : Function.Injective (relativeToAbsolute sX f) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨Z, rfl⟩ := relativeNumericalClass_surjective sX f z
  rw [LinearMap.mem_ker, isNaturalRelativeMap_relativeToAbsolute sX f Z] at hz
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((Submodule.Quotient.mk_eq_zero (OneCycle.numericallyTrivial sX)).mp hz)

/-- **`ρ(X/Z) = 1` makes `N₁(X/Z)` at most a line.** The pairing embeds `N₁(X/Z)` into the
annihilator of the numerically `f`-trivial divisors, the dual of the line `N¹(X/Z)`; so every
class is a multiple of a nonzero one. -/
private theorem exists_smul_eq_of_relativePicardNumber_eq_one {X Z : Scheme.{0}}
    [IsIntegral X] {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}
    (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {v : RelativeNumericalCurveClasses sX f} (hv : v ≠ 0) (z : RelativeNumericalCurveClasses sX f) :
    ∃ c : ℝ, c • v = z := by
  set W := MMP.Flips.relativeNumericallyTrivialDivisors sX f
  have hrank : Module.finrank ℝ (KCartierDivisor ℝ X ⧸ W) = 1 := by
    have h1 : Module.rank ℝ (KCartierDivisor ℝ X ⧸ W) = 1 := by
      unfold MMP.Flips.relativePicardNumber at hρ
      exact Cardinal.toENat_eq_one.mp hρ
    exact Module.finrank_eq_of_rank_eq (by rw [h1]; simp)
  have : FiniteDimensional ℝ (KCartierDivisor ℝ X ⧸ W) :=
    Module.finite_of_finrank_eq_succ hrank
  have hann : ∀ (z : RelativeNumericalCurveClasses sX f) (D : KCartierDivisor ℝ X), D ∈ W →
      curvePairing sX (relativeToAbsolute sX f z) D = 0 := by
    intro z D hD
    obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX f z
    rw [isNaturalRelativeMap_relativeToAbsolute sX f]
    change OneCycle.intersectionPairing D Z = 0
    rw [MMP.Flips.mem_relativeNumericallyTrivialDivisors] at hD
    rw [relativeOneCycles, Finsupp.mem_supported] at hZ
    rw [← Finsupp.sum_single Z, Finsupp.sum, map_sum]
    refine Finset.sum_eq_zero fun C hC => ?_
    have hs : Finsupp.single C (Z C) = Z C • C.cycle ℝ := by
      rw [ProperCurve.cycle, Finsupp.smul_single_one]
    rw [hs, map_smul]
    rw [show OneCycle.intersectionPairing D (C.cycle ℝ) = 0 from hD C (hZ hC), smul_zero]
  let φ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] W.dualAnnihilator :=
    LinearMap.codRestrict W.dualAnnihilator (curvePairing sX ∘ₗ relativeToAbsolute sX f)
      fun z => (Submodule.mem_dualAnnihilator _).mpr fun D hD => hann z D hD
  let ψ := W.dualQuotEquivDualAnnihilator.symm.toLinearMap ∘ₗ φ
  have hψ : Function.Injective ψ := by
    intro z₁ z₂ h
    have h1 : φ z₁ = φ z₂ := W.dualQuotEquivDualAnnihilator.symm.injective h
    have h2 : curvePairing sX (relativeToAbsolute sX f z₁) =
        curvePairing sX (relativeToAbsolute sX f z₂) := congrArg Subtype.val h1
    refine relativeToAbsolute_injective sX f (numericalPairing_flip_injective sX ?_)
    refine LinearMap.ext fun d => ?_
    obtain ⟨D, rfl⟩ := (numericallyTrivialDivisors sX).mkQ_surjective d
    exact LinearMap.congr_fun h2 D
  have hfin : Module.finrank ℝ (Module.Dual ℝ (KCartierDivisor ℝ X ⧸ W)) = 1 := by
    rw [Subspace.dual_finrank_eq, hrank]
  have := Module.Finite.of_injective ψ hψ
  have hle : Module.finrank ℝ (RelativeNumericalCurveClasses sX f) ≤ 1 :=
    hfin ▸ LinearMap.finrank_le_finrank_of_injective hψ
  have h1 : Module.finrank ℝ (RelativeNumericalCurveClasses sX f) = 1 :=
    le_antisymm hle (Module.finrank_pos_iff_exists_ne_zero.mpr ⟨v, hv⟩)
  exact (finrank_eq_one_iff_of_nonzero' v hv).mp h1 z

/-- **`NE̅(X/Z)` is a ray when `ρ(X/Z) = 1`.** If a continuous linear form `φ` on `N₁(X/Z)` is
negative on the class of every curve contracted by `f`, and some curve is contracted, then
`NE̅(X/Z)` is an extremal ray of itself and `φ` is negative on its nonzero points. -/
private theorem isExtremalRay_relativeClosedConeOfCurves {X Z : Scheme.{0}} [IsIntegral X]
    {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z} (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    (φ : RelativeNumericalCurveClasses sX f →ₗ[ℝ] ℝ) (hφc : Continuous φ)
    (hφ : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f), φ (C.relativeClass f hC) < 0)
    {A : ProperCurve sX} (hA : A.IsContractedBy f) :
    IsExtremalRay ℝ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
        (relativeClosedConeOfCurves sX f) ∧
      ∀ z ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)),
        z ≠ 0 → φ z < 0 := by
  set v := A.relativeClass f hA
  have hφv : φ v < 0 := hφ A hA
  have hv : v ≠ 0 := fun h0 => hφv.ne (by rw [h0, map_zero])
  have hle : ∀ z ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)),
      φ z ≤ 0 := fun z hz => by
    simpa using nonneg_of_mem_relativeClosedConeOfCurves (-φ) hφc.neg
      (fun C hC => by simpa using (hφ C hC).le) hz
  have hvN : v ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) := by
    rw [coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves hA)
  have hray : ∀ z ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)),
      ∃ c : ℝ, 0 ≤ c ∧ c • v = z := by
    intro z hz
    obtain ⟨c, rfl⟩ := exists_smul_eq_of_relativePicardNumber_eq_one hρ hv z
    refine ⟨c, ?_, rfl⟩
    have := hle _ hz
    rw [map_smul, smul_eq_mul] at this
    by_contra hc
    push Not at hc
    nlinarith
  refine ⟨⟨⟨subset_rfl, isCone_coe _,
    fun u hu w hw => (relativeClosedConeOfCurves sX f).add_mem hu hw,
    fun u hu w hw _ => ⟨hu, hw⟩⟩, v, hv, ?_⟩, ?_⟩
  · ext z
    constructor
    · exact hray z
    · rintro ⟨c, hc, rfl⟩
      exact (relativeClosedConeOfCurves sX f).smul_mem hc hvN
  · intro z hz hz0
    obtain ⟨c, hc, rfl⟩ := hray z hz
    have hc0 : c ≠ 0 := by rintro rfl; exact hz0 (zero_smul _ _)
    rw [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg (lt_of_le_of_ne hc (Ne.symm hc0)) hφv

/-- A relatively ample Cartier divisor in the sense of *Flips and abundance* has positive degree
on every contracted proper curve. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] {g : X ⟶ Y} {L : Divisor X}
    (hL : MMP.Flips.IsRelativelyAmpleCartier g L) (C : ProperCurve sX) (hC : C.IsContractedBy g) :
    0 < L.degreeOn ℂ sX C.ι C.dim_le hL.1 := by
  obtain ⟨hLc, hamp⟩ := hL
  haveI := hLc.isInvertibleModule_divisorialSheaf
  have hM : MMP.Mori.IsRelativelyAmple g L.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show y ∈ (⊤ : Y.Opens) from trivial)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy g _ hM C hC

/-- A curve contracted by `f` is contracted by `f ≫ h`. -/
private theorem isContractedBy_comp {X Y W : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {C : ProperCurve sX} {f : X ⟶ Y} (h : Y ⟶ W) (hC : C.IsContractedBy f) :
    C.IsContractedBy (f ≫ h) := fun x hx => by
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]

/-- **The step is `D`-null.** For `0 < t < ε` and a `D_t`-negative extremal contraction
`f : X ⟶ Z` over `S`, every curve contracted by `f` is `D`-null: `NE̅(X/Z)` is a single
`D_t`-negative extremal ray, to which the first assertion applies over `Z`. -/
private theorem step_null {X S Z : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ))
    (g : X ⟶ S) (f : X ⟶ Z) (h : Z ⟶ S) (hfh : f ≫ h = g)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    {K : Divisor X} {B C : RDivisor X} (hK : K.IsCanonicalDivisor sX 3)
    (ν : RationalNullData sX K B) (hC0 : ∀ P, 0 ≤ C.coeff P) (hC : IsRealKltPair sX C)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX g (MMP.Flips.logCanonicalDivisor K B))
    (t : ℝ) (ht0 : 0 < t) (htε : t < eps ν.s ν.weight ν.m)
    (hf : MMP.Flips.IsNegativeExtremalContraction ℂ sX sZ
      (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) f) :
    ∀ A : ProperCurve sX, A.IsContractedBy f →
      ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
        Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
        ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
          NumericalCurveClasses.degree sX (L j).divisorialSheaf
            (OneCycle.numericalClass sX (A.cycle ℝ))) = 0 := by
  intro A hA n c L hL heq
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := ν.isProjectiveVariety
  haveI : QuasiCompact sX := inferInstance
  have hfs : f ≫ sZ = sX := hf.isContraction.comp_eq
  have hnef' : MMP.Flips.IsRelativelyNef ℂ sX f (MMP.Flips.logCanonicalDivisor K B) := by
    obtain ⟨m, r, L₀, hL₀, hD, hn⟩ := hnef
    exact ⟨m, r, L₀, hL₀, hD, fun C hC => hn C (hfh ▸ isContractedBy_comp h hC)⟩
  obtain ⟨m, r, Lt, hm1, hr, hLt, hAt⟩ := hf.isRelativelyAntiAmple
  have hLtc : ∀ j, (Lt j).IsCartier := fun j => (hLt j).1
  have heqt : Divisor.toRDivisor K + ((1 - t) • B + t • C) =
      ∑ j, (-r j) • Divisor.toRDivisor (Lt j) := by
    have := congrArg Neg.neg hAt
    rw [neg_neg] at this
    change MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C) = _
    rw [this, ← Finset.sum_neg_distrib]
    simp [neg_smul]
  let φ := (absForm sX (fun j => -r j) Lt hLtc).comp (relativeToAbsolute sX f)
  have hφc : Continuous φ := continuous_absForm_comp f (fun j => -r j) Lt hLtc
  have hφ : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy f), φ (C.relativeClass f hC) < 0 := by
    intro C hC
    simp only [φ, LinearMap.comp_apply, ProperCurve.relativeClass]
    rw [isNaturalRelativeMap_relativeToAbsolute sX f, absForm_cycle]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_neg_iff_pos]
    exact Finset.sum_pos (fun j _ => mul_pos (hr j)
      (by exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier (hLt j) C hC))
      ⟨⟨0, hm1⟩, Finset.mem_univ _⟩
  obtain ⟨hray, hneg⟩ :=
    isExtremalRay_relativeClosedConeOfCurves hf.relativePicardNumber_eq_one φ hφc hφ hA
  have hAmem : A.relativeClass f hA ∈
      (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)) := by
    rw [coe_relativeClosedConeOfCurves]
    exact subset_closure (relativeClass_mem_relativeConeOfCurves hA)
  have key := ray_null sX sZ f hZ hfs hK ν hC0 hC hnef' t ht0 htε _ hray
    ⟨m, fun j => -r j, Lt, hLtc, heqt, fun u hu hu0 => by rw [relSum_eq]; exact hneg u hu hu0⟩
    n c L hL heq (A.relativeClass f hA) hAmem
  rwa [relSum_eq f c L hL, ProperCurve.relativeClass, isNaturalRelativeMap_relativeToAbsolute sX f,
    absForm_apply c L hL] at key

end Step

end ErasedIntegral

/-! ### Comparison of log discrepancies across a step -/

namespace Transfer

open MMP.Mori MMP.Resolution MMP.Fourfold
open scoped WithZero

section TransferErased

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### The dictionary between the two log discrepancies -/

section Bridge

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sX]

/-- With a presentation of `div(ω) + D` by Cartier divisors, every divisor over `X` (with proper
model) has a discrepancy computed with these choices. -/
private theorem exists_isDiscrepancyWith (hX : IsNormalVariety ℂ sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D : RDivisor X} {ω : RationalPluriForms sX n 1}
    (hω : ω ≠ 0) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hLc : ∀ j, (L j).IsCartier)
    (hsum : Divisor.toRDivisor (divisorOfForm ω) + D = ∑ j, r j • Divisor.toRDivisor (L j))
    (E : MMP.Flips.ProperDivisorOver ℂ sX) : ∃ b, MMP.Flips.IsDiscrepancyWith sX n D ω r L E b := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  have := E.isProper
  have : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose L' hL' using fun j => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hLc j)
  exact ⟨_, hX, hn, hω, hLc, hsum, L', fun j => ⟨_, hL' j⟩, rfl⟩

/-- The valuation of a divisor over `X` with proper model has nonempty center. -/
private theorem hasNonemptyCenter_valuation (E : MMP.Flips.ProperDivisorOver ℂ sX) :
    MMP.Flips.HasNonemptyCenter ℂ sX E.valuation := by
  have := E.isIntegral
  have := E.isNormal
  have := E.isLocallyNoetherian
  have := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-- A log discrepancy is a discrepancy, computed with the form inside it, plus one. -/
private theorem isDiscrepancyWith_of_isLogDiscrepancy {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a) :
    ∃ (ω : RationalPluriForms sX n 1) (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      MMP.Flips.IsDiscrepancyWith sX n B ω r L ⟨D, h.2.1⟩ (a - 1) := by
  obtain ⟨hX, hp, ω, hω, ⟨K, hK, hKc⟩, m, r, C, C', hC, hrel, hpb, ha⟩ := h
  refine ⟨ω, m, r, C, hX, hK.topologicalKrullDim_eq, hω, hC, ?_, C', hpb, ?_⟩
  · refine DivisorWithCoeffs.ext' fun Γ => ?_
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
      MMP.Flips.coeff_sum_smul_toRDivisor]
    exact hrel Γ
  · exact (by linear_combination ha :
      a - 1 = (D.ordPullback ω : ℝ) - ∑ j, r j * ((C' j).coeff D.E : ℝ))

/-- A log discrepancy, against a presentation of `div(ω) + B`, gives the discrepancy `a - 1` of
the valuation in the sense of *Flips and abundance*. -/
private theorem isDiscrepancy_of_isLogDiscrepancy {n : ℕ} {B : RDivisor X}
    {D : DivisorOver ℂ sX} {a : ℝ} (h : MMP.Intersection.IsLogDiscrepancy sX n B D a)
    {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B)) :
    MMP.Flips.IsDiscrepancy sX n (divisorOfForm ω) B D.valuation (a - 1) := by
  obtain ⟨ω', m', r', L', hw'⟩ := isDiscrepancyWith_of_isLogDiscrepancy h
  obtain ⟨m, r, L, hLc, hsum⟩ := hKB
  have hsum' : Divisor.toRDivisor (divisorOfForm ω) + B =
      ∑ j, r j • Divisor.toRDivisor (L j) := by
    simpa only [MMP.Flips.toRDivisor_eq_mapCoeffs] using hsum
  obtain ⟨b, hb⟩ := exists_isDiscrepancyWith h.1 hK.topologicalKrullDim_eq hω hLc hsum'
    ⟨D, h.2.1⟩
  have hab := hb.eq hw' rfl
  refine ⟨hK, ⟨m, r, L, hLc, hsum⟩, hasNonemptyCenter_valuation ⟨D, h.2.1⟩, ⟨D, h.2.1⟩, ω, m, r,
    L, rfl, rfl, ?_⟩
  rwa [hab] at hb

end Bridge

/-- On a smooth birational model `f : Y ⟶ X`, the pull-back `f^*ω` of a rational `n`-form with
canonical divisor `div ω` has canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm_pullback {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {f : Y ⟶ X} [IsDominant f] [LocallyOfFiniteType (f ≫ sX)] (hY : IsNormalVariety ℂ (f ≫ sX))
    (hf : IsBirationalMorphism f) (hYsm : IsSmoothScheme (f ≫ sX)) :
    (divisorOfForm (pullbackRationalPluriForms sX f ω)).IsCanonicalDivisor (f ≫ sX) n := by
  have hn := hK.topologicalKrullDim_eq
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  haveI : AlgebraicGeometry.IsVariety ℂ (f ≫ sX) := hY.1
  obtain ⟨K₀, hK₀⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (f ≫ sX) hYsm
    ((MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (f ≫ sX) hf).symm.trans hn)
  exact hK₀.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hY hK₀
      (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' f
        hf.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hn) hω0)

/-! ### Exceptional and non-exceptional divisors -/

section Exceptional

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- A divisor over a normal variety is exceptional exactly when its centre has codimension at
least two. -/
private theorem isExceptional_iff_two_le_coheight (hX : IsNormalVariety ℂ sX)
    (D : DivisorOver ℂ sX) :
    D.IsExceptional ↔ 2 ≤ Order.coheight (D.f D.E.genericPoint) := by
  have := D.isLocallyNoetherian
  have := D.isNormal
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (X ↘ ⊤_ Scheme) := by
    rw [show (X ↘ ⊤_ Scheme) = sX ≫ (Spec (.of ℂ) ↘ ⊤_ Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hcl : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := Closeds.ext rfl
  rw [hcl, closedsCodimension_coe, MMP.Positivity.DivisorOver.codimension_center]

/-- The valuation of the divisor `(X, 𝟙, Q)` over `X` is `ord_Q`. -/
private theorem valuation_ofPrimeDivisor (hX : IsNormalVariety ℂ sX)
    (Q : MMP.Mori.PrimeDivisor X) :
    (DivisorOver.ofPrimeDivisor ℂ hX Q).valuation = Q.divisorialValuation :=
  Valuation.ext fun φ => by
    change Q.divisorialValuation (functionFieldMap (𝟙 X) φ) = _
    rw [MMP.Mori.functionFieldMap_id_apply]

variable [CompactSpace X] [LocallyOfFiniteType sX]

/-- The log discrepancy of a prime divisor `Q` of `X` is `1 - coeff_Q B`. -/
private theorem isLogDiscrepancy_ofPrimeDivisor (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {B : RDivisor X} {ω : RationalPluriForms sX n 1} (hω : ω ≠ 0)
    (hK : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : MMP.Flips.IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    (Q : MMP.Mori.PrimeDivisor X) :
    MMP.Intersection.IsLogDiscrepancy sX n B (DivisorOver.ofPrimeDivisor ℂ hX Q)
      (1 - B.coeff Q) := by
  have h := MMP.Flips.isDiscrepancy_divisorialValuation hX ω hω hK hKB Q
  have := MMP.Fourfold.isLogDiscrepancy_of_isDiscrepancy h (DivisorOver.ofPrimeDivisor ℂ hX Q)
    (inferInstanceAs (IsProper (𝟙 X))) (valuation_ofPrimeDivisor hX Q)
  rwa [← sub_eq_add_neg] at this

end Exceptional

/-! ### Forms, boundaries and prime divisors of smooth models -/

section PrimeDiscrepancy

open MMP.Flips

/-- **Discrepancies of the prime divisors of a smooth model.** If `π : W ⟶ X` is a smooth
birational model and `div(π^*ω) + D_W = π^*(div ω + B)`, then every prime divisor `P` of `W` has
discrepancy `a(ord_P, X, B) = -coeff_P D_W`. -/
private theorem isDiscrepancy_primeDivisor_of_isRCartierPullback {X W : Scheme.{0}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of ℂ)}
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ} {B : RDivisor X}
    {ω : RationalPluriForms sX n 1} (hω0 : ω ≠ 0) (hKω : (divisorOfForm ω).IsCanonicalDivisor sX n)
    (hKB : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B))
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {π : W ⟶ X} [IsProper π]
    [LocallyOfFiniteType (π ≫ sX)] (hW : IsNormalVariety ℂ (π ≫ sX)) (hπ : IsBirationalMorphism π)
    (hsm : IsSmoothScheme (π ≫ sX)) {DW : RDivisor W}
    (hpb : haveI := hπ.isDominant
      IsRCartierPullback π (Divisor.toRDivisor (divisorOfForm ω) + B)
        (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) + DW))
    (P : MMP.Mori.PrimeDivisor W) :
    IsDiscrepancy sX n (divisorOfForm ω) B (⟨W, π, hW, hπ, P⟩ : DivisorOver ℂ sX).valuation
      (-DW.coeff P) := by
  haveI := hπ.isDominant
  have hKY := isCanonicalDivisor_divisorOfForm_pullback hX hω0 hKω hW hπ hsm
  have hKDY : IsCartierCombination
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX π ω)) + DW) := by
    obtain ⟨m, r, L₀, L, hLc, -, hL, heq⟩ := hpb
    exact ⟨m, r, L, fun j => (hL j).2.isCartier (hLc j), by
      rw [heq]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  let ER : MMP.Flips.ProperDivisorOver ℂ (π ≫ sX) :=
    ⟨DivisorOver.ofPrimeDivisor ℂ hW P, (inferInstance : IsProper (𝟙 W))⟩
  have hER : ER.valuation = P.divisorialValuation := valuation_ofPrimeDivisor hW P
  have h1 := isDiscrepancy_divisorialValuation hW _
    (MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' π
      hπ.functionFieldMap_bijective
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hKω.topologicalKrullDim_eq) hω0)
    hKY hKDY P
  rw [← hER] at h1
  have h2 := (isDiscrepancy_comap_functionFieldMap_iff hX hω0 hKω hKB π hW hπ hpb hKY ER _).mpr h1
  rwa [hER] at h2

end PrimeDiscrepancy

section Small

variable {X Z : Scheme.{0}} [IsIntegral X] {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}

/-- **A small contraction is an isomorphism off codimension two.** For a small birational
contraction `f : X ⟶ Z` there are closed subsets `V ⊆ X` and `W ⊆ Z` of points of coheight at
least two, with `X ∖ V ⊆ f⁻¹(Z ∖ W)`, such that `f` is an isomorphism over `Z ∖ W`: the section of
the separated `f⁻¹(Z ∖ W) ⟶ Z ∖ W` given by `X ∖ V` is a closed immersion, so `X ∖ V` is
open and closed in the irreducible `f⁻¹(Z ∖ W)`. -/
private theorem exists_closeds_isIso_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f) :
    ∃ (V : Closeds X) (W : Closeds Z), (∀ x ∈ (V : Set X), 2 ≤ Order.coheight x) ∧
      (∀ z ∈ (W : Set Z), 2 ≤ Order.coheight z) ∧ V.compl ≤ f ⁻¹ᵁ W.compl ∧
      IsIso (f ∣_ W.compl) := by
  obtain ⟨V, W, hV, hW, h, hiso⟩ := hf.exists_isIso
  have hV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV
  have hW' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW
  refine ⟨V, W, hV', hW', h, ?_⟩
  haveI : IsProper f := hf.isProper
  set U := f ⁻¹ᵁ W.compl
  set g := f ∣_ W.compl
  set j := X.homOfLE h
  have hjg : j ≫ g = f.resLE W.compl V.compl h := rfl
  set s := inv (f.resLE W.compl V.compl h) ≫ j
  have hs : s ≫ g = 𝟙 _ := by simp [s, hjg]
  haveI : IsClosedImmersion (s ≫ g) := by rw [hs]; infer_instance
  haveI : IsClosedImmersion s := IsClosedImmersion.of_comp s g
  have hj : j = f.resLE W.compl V.compl h ≫ s := by simp [s]
  haveI : IsClosedImmersion j := by rw [hj]; infer_instance
  -- `X ∖ V` is nonempty: it contains the generic point
  have hgen : genericPoint X ∈ (V.compl : Set X) := by
    intro hgV
    have := hV' (genericPoint X) hgV
    rw [Order.coheight_eq_zero.mpr (fun z _ => genericPoint_specializes z)] at this
    exact absurd this (by decide)
  haveI : Nonempty U := ⟨⟨_, h hgen⟩⟩
  have hclopen : IsClopen (Set.range j) :=
    ⟨j.isClosedEmbedding.isClosed_range, j.isOpenEmbedding.isOpen_range⟩
  have hne : (Set.range j).Nonempty := ⟨_, ⟨⟨_, hgen⟩, rfl⟩⟩
  have hrange : Set.range j = Set.univ := (isClopen_iff.mp hclopen).resolve_left hne.ne_empty
  haveI : Surjective j := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso j := (isIso_iff_isOpenImmersion_and_surjective j).mpr ⟨inferInstance, inferInstance⟩
  have hg : g = inv j ≫ f.resLE W.compl V.compl h := by rw [← hjg]; simp
  change IsIso g
  rw [hg]
  infer_instance

variable [IsLocallyNoetherian X] [IsNormal X]

/-- Points of coheight at most one of the base lie in the biregular locus of a small
contraction. -/
private theorem mem_biregularLocus_of_isSmall {f : X ⟶ Z} (hf : MMP.Flips.IsSmall ℂ sZ sX f)
    {z : Z} (hz : Order.coheight z ≤ 1) : z ∈ biregularLocus f := by
  obtain ⟨V, W, -, hW, -, hiso⟩ := exists_closeds_isIso_of_isSmall hf
  have hzW : z ∈ (W.compl : Set Z) := fun h => absurd ((hW z h).trans hz) (by decide)
  exact le_biregularLocus hiso hzW

end Small

/-! ### Intersection numbers and nefness of pull-backs -/

section NegHelpers

open MMP MMP.Flips

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type} [Field k] {Y Y' : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_left (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type} [Field k] {Y Y' : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dite_eq_right hc, map_zero]

/-- **Pulling back a divisor nonpositive on contracted curves.** Let `h : Y' ⟶ Y` be proper and
`B = ∑ s_j N_j` a combination of Cartier divisors with `B · C ≤ 0` on every curve contracted by
`f : Y ⟶ X`. Then `-h^*B = -∑ s_j h^*N_j` is `(h ≫ f)`-nef: by the projection formula a curve
`C'` contracted by `h ≫ f` has `h^*B · C' = [k(C') : k(h C')] (B · h C')` if `h(C')` is a curve,
which is then contracted by `f`, and `h^*B · C' = 0` if `h(C')` is a point. -/
private theorem isRelativelyNef_neg_sum_pullback {k : Type} [Field k] {X Y Y' : Scheme.{0}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [IsProper h] [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y']
    (f : Y ⟶ X) {m : ℕ} (s : Fin m → ℝ) (N : Fin m → Divisor Y) (hN : ∀ j, (N j).IsCartier)
    (hNB : ∀ j, ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ (N j).supp)
    (hBC : ∀ C : ProperCurve sY, C.IsContractedBy f →
      ∑ j, s j * ((N j).degreeOn k sY C.ι C.dim_le (hN j) : ℝ) ≤ 0) :
    IsRelativelyNef k (h ≫ sY) (h ≫ f)
      (-∑ j, s j • Divisor.toRDivisor ((N j).pullback (hN j) (hNB j))) := by
  have hN'c : ∀ j, ((N j).pullback (hN j) (hNB j)).IsCartier := fun j =>
    (hN j).isCartier_pullback h (hNB j)
  refine ⟨m, fun j => -s j, _, hN'c, by simp [← Finset.sum_neg_distrib], fun C' hC' x hx => ?_⟩
  have hx0 := isRIntersectionNumber_sum_degreeOn (r := fun j => -s j) hN'c rfl C'
  rw [(IsRIntersectionNumber.eq_and_linear k (h ≫ sY) C').1 _ _ _ _ _ _ _ hx
    (by simpa [← Finset.sum_neg_distrib] using hx0)]
  by_cases hc : IsProperCurve sY (h C'.point)
  · -- `h(C')` is a curve `C`, contracted by `f`
    let C : ProperCurve sY := ⟨_, hc⟩
    have hCf : C.IsContractedBy f := by
      intro y hy
      have hsub : closure ({h C'.point} : Set Y) ⊆ h '' closure ({C'.point} : Set Y') :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
          (h.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      simpa only [Scheme.Hom.comp_apply] using hC' z hz
    simp only [degreeOn_pullback_eq_mul h (hN _) (hNB _) C' C rfl, Int.cast_mul, Int.cast_natCast,
      Finset.sum_neg_distrib, mul_left_comm (s _), ← Finset.mul_sum, neg_nonneg]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hBC C hCf)
  · -- `h(C')` is a point
    simp [degreeOn_pullback_eq_zero h (hN _) (hNB _) C' hc]

/-- A prime divisor `F` of `Y` is exceptional over the normal variety `X` exactly when its image
`g(η_F)` has coheight at least two. -/
private theorem isExceptionalPrimeDivisor_iff_two_le_coheight {k : Type} [Field k]
    {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : IsNormalVariety k (g ≫ sX)) (hg : IsBirationalMorphism g) [IsProper g]
    (F : MMP.Mori.PrimeDivisor Y) :
    IsExceptionalPrimeDivisor sX g F ↔ 2 ≤ Order.coheight (g F.genericPoint) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := Oai4C1.Negativity.exists_topologicalKrullDim_eq_natCast sX
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  constructor
  · rintro ⟨_, _, _, hexc⟩
    unfold ProperDivisorOver.IsExceptional at hexc
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn] at hexc
    exact (Oai4C1.Negativity.withBot_add_two_le_iff hd).mp hexc
  · intro h2
    refine ⟨hY, hg, ‹_›, ?_⟩
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn]
    exact (Oai4C1.Negativity.withBot_add_two_le_iff hd).mpr h2

end NegHelpers

/-! ### Common models -/

section CommonModel

/-- For birational morphisms `f : X ⟶ Y` and `f' : X' ⟶ Y`, the birational map
`φ = f'⁻¹ ∘ f : X ⇢ X'` satisfies `f' ∘ φ = f`. -/
private theorem exists_isBirational_compHom_eq {X X' Y : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y}
    (hf : IsBirationalMorphism f) (hf' : IsBirationalMorphism f') :
    ∃ φ : MMP.Mori.RationalMap X X', φ.IsBirational ∧ φ.compHom f' = f.toRationalMap := by
  obtain ⟨e₁, h₁⟩ := Oai4C1.CommonModel.exists_partialIso_isOver hf
  obtain ⟨e₂, h₂⟩ := Oai4C1.CommonModel.exists_partialIso_isOver hf'
  set e := e₁.trans e₂.symm
  have h : e.IsOver f f' := h₁.trans h₂.symm
  refine ⟨e.toRationalMap, RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨e.source, e.dense_source, le_rfl,
    le_top, ?_⟩
  change X.homOfLE le_rfl ≫ (e.iso.hom ≫ e.target.ι) ≫ f' =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, h]
  simp

section Comp

open MMP.Flips

variable {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {Y : Scheme.{0}} (f : Y ⟶ X) [IsProper f]
  (hf : IsBirationalMorphism f) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]

/-- The divisor `(Y', f ∘ g, E)` over `X` of a divisor `(Y', g, E)` over `Y`. -/
private def compDivisorOver (E : ProperDivisorOver k (f ≫ sX)) :
    ProperDivisorOver k sX where
  Y := E.Y
  f := E.f ≫ f
  isNormalVariety := by
    have h := E.isNormalVariety
    rwa [← Category.assoc] at h
  isBirationalMorphism := by
    haveI := E.isIntegral
    haveI := E.isProper
    exact MMP.Mori.isBirationalMorphism_comp_of_isBirational f E.f
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
      (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism E.isBirationalMorphism)
  E := E.E
  isProper := by
    haveI := E.isProper
    infer_instance

/-- The valuation of the composite divisor over `X` is `ord_E ∘ f^*`. -/
private theorem compDivisorOver_valuation (E : ProperDivisorOver k (f ≫ sX)) :
    haveI : IsDominant f := hf.isDominant
    (compDivisorOver f hf E).valuation = E.valuation.comap (functionFieldMap f) := by
  haveI : IsDominant f := hf.isDominant
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  ext a
  change E.E.divisorialValuation _ = E.E.divisorialValuation _
  congr 1
  exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply E.f f a).symm

end Comp

end CommonModel

/-! ### Forms on birational models -/

section Forms

open MMP.Flips

/-- The pull-back of rational forms along an isomorphism of function fields is surjective. -/
private theorem pullbackForms_surjective {k K K' : Type*} [CommRing k] [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}
    (hbij : Function.Bijective (algebraMap K K')) {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : IsPullbackGenerator K' ω) (m : ℤ) :
    Function.Surjective (pullbackForms (k := k) (K := K) (K' := K') (d := d) m) := by
  intro σ
  set b' := ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m
  set b := ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m
  obtain ⟨c, hc⟩ := hbij.2 (b'.repr σ ())
  refine ⟨c • b (), ?_⟩
  have h1 : b.repr (c • b ()) () = c := by
    simp [Module.Basis.repr_self]
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  change algebraMap K K' (b.repr (c • b ()) ()) • b' () = σ
  rw [h1, hc]
  exact basis_unit_repr_smul b' σ

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of ℂ)}

/-- Every rational top form on a birational model is a pull-back. -/
private theorem exists_pullbackRationalPluriForms_eq [LocallyOfFiniteType sX] (g : Y ⟶ X)
    [IsDominant g] (hg : Function.Bijective (functionFieldMap g)) {n : ℕ}
    (hn : topologicalKrullDim X = n) (σ : RationalPluriForms (g ≫ sX) n 1) :
    ∃ ω : RationalPluriForms sX n 1, pullbackRationalPluriForms sX g ω = σ := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX g hg hd
  exact pullbackForms_surjective hg hω 1 σ

/-- The pull-back of the zero form is zero. -/
private theorem pullbackRationalPluriForms_zero (g : Y ⟶ X) [IsDominant g] {n : ℕ} :
    pullbackRationalPluriForms sX g (0 : RationalPluriForms sX n 1) = 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (g ≫ sX)
  let := functionFieldMapAlgebra g
  have := isScalarTower_functionFieldMap sX g
  have h := pullbackForms_smul (K' := Y.functionField) (k := ℂ) (d := n) (m := 1)
    (0 : X.functionField) (0 : RationalPluriForms sX n 1)
  simp only [zero_smul, map_zero] at h
  exact h

/-- On a normal variety with a canonical divisor, the divisor of every nonzero rational top form
is canonical. -/
private theorem isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {τ : RationalPluriForms sX n 1}
    (hτ : τ ≠ 0) : (divisorOfForm τ).IsCanonicalDivisor sX n :=
  hK.of_linearlyEquivalent <| by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK hτ

end Forms

/-! ### Changing the structure morphism -/

section Structure

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
  {s₁ s₂ : Y ⟶ Spec (.of ℂ)}

private theorem exists_form_divisorOfForm_eq [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (h : s₁ = s₂) {n : ℕ} (τ : RationalPluriForms s₁ n 1) (hτ : τ ≠ 0) :
    ∃ τ' : RationalPluriForms s₂ n 1, τ' ≠ 0 ∧ divisorOfForm τ' = divisorOfForm τ := by
  subst h; exact ⟨τ, hτ, rfl⟩

private theorem isDiscrepancy_of_eq_structure [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (h : s₁ = s₂) {n : ℕ} {K : Divisor Y} {D : RDivisor Y} {v : Valuation Y.functionField ℤᵐ⁰}
    {a : ℝ} (hd : MMP.Flips.IsDiscrepancy s₁ n K D v a) : MMP.Flips.IsDiscrepancy s₂ n K D v a := by
  subst h; exact hd

private theorem isRelativelyNef_of_eq_structure {S : Scheme.{0}} [QuasiCompact s₁]
    [QuasiCompact s₂] (h : s₁ = s₂) {g : Y ⟶ S} {D : RDivisor Y}
    (hd : MMP.Flips.IsRelativelyNef ℂ s₁ g D) : MMP.Flips.IsRelativelyNef ℂ s₂ g D := by
  subst h; exact hd

/-- A proper divisor over `Y`, for another (equal) structure morphism. -/
private def properDivisorOverOfEq (h : s₁ = s₂) (E : MMP.Flips.ProperDivisorOver ℂ s₁) :
    MMP.Flips.ProperDivisorOver ℂ s₂ where
  Y := E.Y
  f := E.f
  isNormalVariety := h ▸ E.isNormalVariety
  isBirationalMorphism := E.isBirationalMorphism
  E := E.E
  isProper := E.isProper

end Structure

/-! ### Positivity and nefness -/

section Positivity

open MMP.Flips

variable {X Y : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]

/-- A sum of nef `ℝ`-divisors over `Y` is nef over `Y`. -/
private theorem isRelativelyNef_add {g : X ⟶ Y} {D₁ D₂ : RDivisor X}
    (h₁ : IsRelativelyNef ℂ sX g D₁) (h₂ : IsRelativelyNef ℂ sX g D₂) :
    IsRelativelyNef ℂ sX g (D₁ + D₂) := by
  obtain ⟨m₁, r₁, L₁, hL₁, rfl, hn₁⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hL₂, rfl, hn₂⟩ := h₂
  have hc : ∀ j, (Fin.append L₁ L₂ j).IsCartier :=
    Fin.addCases (fun j => by simpa using hL₁ j) (fun j => by simpa using hL₂ j)
  refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂, hc, ?_, fun C hC x hx => ?_⟩
  · simp [Fin.sum_univ_add]
  · have hx₁ := isRIntersectionNumber_sum_degreeOn (r := r₁) hL₁ rfl C
    have hx₂ := isRIntersectionNumber_sum_degreeOn (r := r₂) hL₂ rfl C
    have hsum := (IsRIntersectionNumber.eq_and_linear ℂ sX C).2 _ _ r₁ L₁ r₂ L₂ _ _ 1 1 hx₁ hx₂
    simp only [one_smul, one_mul] at hsum
    rw [(IsRIntersectionNumber.eq_and_linear ℂ sX C).1 _ _ _ _ _ _ _ hx hsum]
    exact add_nonneg (hn₁ C hC _ hx₁) (hn₂ C hC _ hx₂)

end Positivity

/-! ### Multiplicities along divisors over a smooth variety -/

/-- An `ℝ`-divisor is the sum of its prime components with their coefficients. -/
private theorem eq_sum_coeff_smul_single {W : Scheme.{0}} (G : RDivisor W) :
    G = ∑ j : Fin G.support.card, G.coeff (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) •
      Divisor.toRDivisor
        (Finsupp.single (G.support.equivFin.symm j : MMP.Mori.PrimeDivisor W) 1) := by
  classical
  have hsumFin : ∀ F : MMP.Mori.PrimeDivisor W → ℝ,
      ∑ j, F (G.support.equivFin.symm j) = ∑ Q ∈ G.support, F Q := fun F => by
    rw [← Finset.sum_coe_sort G.support]
    exact Equiv.sum_comp G.support.equivFin.symm (fun Q => F Q)
  refine DivisorWithCoeffs.ext' fun Q => ?_
  simp only [MMP.Flips.coeff_sum_smul_toRDivisor]
  have key : ∀ R : MMP.Mori.PrimeDivisor W,
      ((DivisorWithCoeffs.coeff (R := ℤ) (Finsupp.single R 1) Q : ℤ) : ℝ) =
        if R = Q then 1 else 0 := fun R => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> simp
  simp only [key, mul_ite, mul_one, mul_zero]
  rw [hsumFin (fun R => if R = Q then G.coeff R else 0), Finset.sum_ite_eq']
  by_cases hQ : Q ∈ G.support
  · simp [hQ]
  · simp only [hQ, if_false]
    rw [DivisorWithCoeffs.coeff_apply]
    exact Finsupp.notMem_support_iff.mp hQ

section Multiplicity

open MMP.Flips

variable {W : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W]
  {sW : W ⟶ Spec (.of ℂ)} [LocallyOfFiniteType sW]

/-- **Multiplicities over a smooth variety.** Every `ℝ`-divisor `G` on a smooth variety has, along
every proper divisor `E` over it, a multiplicity `μ = ∑_P coeff_P(G) coeff_E(P)` computed from its
prime components, and `-G` has multiplicity `-μ`. -/
private theorem exists_isMultiplicityAlong_of_isSmoothScheme (hW : IsNormalVariety ℂ sW)
    (hsm : IsSmoothScheme sW) (G : RDivisor W) (E : MMP.Flips.ProperDivisorOver ℂ sW) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor W) (μ : ℝ),
      IsMultiplicityAlong sW G r L E.valuation E μ ∧
      IsMultiplicityAlong sW (-G) (-r) L E.valuation E (-μ) := by
  classical
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isIntegral
  haveI := E.isDominant
  haveI : CompactSpace E.Y := (E.isNormalVariety.1.toQuasiCompact).compactSpace_of_compactSpace
  set S := G.support
  set e := S.equivFin
  let P : Fin S.card → MMP.Mori.PrimeDivisor W := fun j => (e.symm j : _)
  let r : Fin S.card → ℝ := fun j => G.coeff (P j)
  let L : Fin S.card → Divisor W := fun j => Finsupp.single (P j) 1
  have hLc : ∀ j, (L j).IsCartier := fun j =>
    MMP.Threefold.Mori.isCartier_single_of_isSmoothScheme hsm _
  let L' : Fin S.card → Divisor E.Y := fun j => Divisor.pullback (L j) (hLc j)
    (MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E.f _)
  have hpb : ∀ j, ∃ hB : ∀ Z : irreducibleComponents E.Y,
      E.f (componentGenericPoint E.Y Z) ∉ (L j).supp, (L j).IsPullback E.f hB (L' j) :=
    fun j => ⟨_, Divisor.isPullback_pullback _ _⟩
  have hG : G = ∑ j, r j • Divisor.toRDivisor (L j) := eq_sum_coeff_smul_single G
  have hcenter : HasNonemptyCenter ℂ sW E.valuation := hasNonemptyCenter_valuation E
  exact ⟨S.card, r, L, ∑ j, r j * ((L' j).coeff E.E : ℝ),
    ⟨hW, hcenter, rfl, hLc, hG, L', hpb, rfl⟩,
    ⟨hW, hcenter, rfl, hLc, by rw [hG, ← Finset.sum_neg_distrib]; simp [neg_smul], L', hpb,
      by simp [Finset.sum_neg_distrib, neg_mul]⟩⟩

end Multiplicity

/-- The strict transform `(f⁺)⁻¹_* f_* D` along a birational `f` and a small `f⁺` has, at a prime
divisor `P⁺` of `X⁺` over the image of a prime divisor `P` of `X` of coheight one in `Z`, the
coefficient of `D` at `P`. -/
private theorem flipTransform_apply_of_coheight_eq_one {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} [IsProper f] (hfb : IsBirationalMorphism f)
    (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) {P : MMP.Mori.PrimeDivisor X}
    {P' : MMP.Mori.PrimeDivisor X'} (hz : Order.coheight (f P.genericPoint) = 1)
    (hPP' : fp P'.genericPoint = f P.genericPoint) {R : Type*} [AddCommMonoid R]
    (D : DivisorWithCoeffs R X) : flipTransform f fp D P' = D P := by
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI := hfb.isDominant
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz
  have hQ : f P.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz).symm
  have := Q.isDiscreteValuationRing_localRing
  exact flipTransform_apply_of_map_genericPoint hfb.functionFieldMap_bijective
    hfp.toIsBirationalContraction.surjective_and_isBirational.1.surj hQ (hPP'.trans hQ)
    (mem_biregularLocus_of_isSmall hfp (hQ ▸ hz).le) D

section Comparison

open MMP.Flips

variable {X X' Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Z]
  {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
  {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z}
  {fp : X' ⟶ Z}

/-- **Log discrepancies do not decrease across a step** (FA 2.28). Let `f : X ⟶ Z` be a proper
birational morphism and `f⁺ : X⁺ ⟶ Z` a small contraction of normal complex varieties, `B` an
`ℝ`-divisor on `X` with `-(K + B)` nef over `Z` and `B⁺ = (f⁺)⁻¹_* f_* B` with `K⁺ + B⁺` nef over
`Z`, both presented by Cartier divisors. For every proper divisor `E⁺` over `X⁺` there is a
proper divisor `E` over `X` with `a(E, X, B) ≤ a(E⁺, X⁺, B⁺)`. -/
private theorem comparison (hXv : IsNormalVariety ℂ sX) (hZv : IsNormalVariety ℂ sZ)
    (hfs : f ≫ sZ = sX) [IsProper f] (hfb : IsBirationalMorphism f)
    (hsm' : MMP.Flips.IsSmall ℂ sZ sX' fp)
    (hK : ∃ m, K.IsCanonicalDivisor sX m) (hK' : ∃ m, K'.IsCanonicalDivisor sX' m)
    (hBB : B' = flipTransform f fp B)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hLc : ∀ j, (L j).IsCartier)
    (hA : -logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j))
    (hAn : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hLc j) : ℝ))
    {m' : ℕ} (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X') (hL'c : ∀ j, (L' j).IsCartier)
    (hA' : logCanonicalDivisor K' B' = ∑ j, r' j • Divisor.toRDivisor (L' j))
    (hA'n : ∀ C : ProperCurve sX', C.IsContractedBy fp →
      0 ≤ ∑ j, r' j * ((L' j).degreeOn ℂ sX' C.ι C.dim_le (hL'c j) : ℝ))
    (E' : DivisorOver ℂ sX') (hE'p : IsProper E'.f) :
    ∃ E : DivisorOver ℂ sX, IsProper E.f ∧
      ∀ (n n' : ℕ) (a a' : ℝ), MMP.Intersection.IsLogDiscrepancy sX n B E a →
        MMP.Intersection.IsLogDiscrepancy sX' n' B' E' a' → a ≤ a' := by
  classical
  have hfps : fp ≫ sZ = sX' := hsm'.comp_eq
  have hX'v : IsNormalVariety ℂ sX' := ⟨hsm'.isVariety_source, inferInstance⟩
  haveI : IsProper fp := hsm'.isProper
  have hfpb : IsBirationalMorphism fp :=
    hsm'.toIsBirationalContraction.surjective_and_isBirational.2
  haveI := hfb.isDominant
  haveI := hfpb.isDominant
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  haveI : QuasiCompact sX := hXv.1.toQuasiCompact
  haveI : QuasiCompact sX' := hX'v.1.toQuasiCompact
  haveI : IsSeparated sX := hXv.1.toIsSeparated
  haveI : IsSeparated sX' := hX'v.1.toIsSeparated
  haveI : IsNormal Z := hZv.2
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  -- the common model
  obtain ⟨φ, hφb, hφ⟩ := exists_isBirational_compHom_eq hfb hfpb
  obtain ⟨W, p, q, hWv, hWsm, hpP, hqP, hpb, hqb, -, hcomm⟩ :=
    IsModificationOf.exists_smooth_common_model sX sX' sZ hXv hX'v hZv.1 f fp hfs hfps φ
      ⟨hφb, hφ⟩
  haveI := hpP
  haveI := hqP
  have hpq : q ≫ sX' = p ≫ sX := by
    rw [← hfps, ← Category.assoc, ← hcomm, Category.assoc, hfs]
  haveI : IsIntegral W := hWv.toIsIntegral
  haveI : LocallyOfFiniteType (p ≫ sX) := hWv.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ sX)
  haveI : CompactSpace W := (hWv.toQuasiCompact).compactSpace_of_compactSpace
  haveI : IsNormal W :=
    (MMP.Threefold.Resolution.isLocallyNoetherian_and_isNormal_of_isSmoothScheme hWsm).2
  have hW : IsNormalVariety ℂ (p ≫ sX) := ⟨hWv, inferInstance⟩
  have hWq : IsNormalVariety ℂ (q ≫ sX') := hpq ▸ hW
  haveI : LocallyOfFiniteType (q ≫ sX') := hWq.1.toLocallyOfFiniteType
  haveI := hpb.isDominant
  haveI := hqb.isDominant
  -- the realization of `E⁺` on `W`
  obtain ⟨D₁, hD₁, -⟩ := ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hX'v.1 q
    hWq.1 hqb ⟨E', hE'p⟩
  set D₁p := properDivisorOverOfEq hpq D₁ with hD₁p
  set E := compDivisorOver p hpb D₁p with hE
  have hEv : E.valuation = D₁.valuation.comap (functionFieldMap p) :=
    compDivisorOver_valuation p hpb D₁p
  set E'' := compDivisorOver q hqb D₁ with hE''
  have hE''v : E''.valuation = E'.valuation := (compDivisorOver_valuation q hqb D₁).trans hD₁
  have hcommff : ∀ t, functionFieldMap p (functionFieldMap f t) =
      functionFieldMap q (functionFieldMap fp t) := fun t => by
    haveI : IsDominant (p ≫ f) := hcomm ▸ inferInstance
    rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_congr hcomm]
  have hval : E.valuation.comap (functionFieldMap f) =
      E'.valuation.comap (functionFieldMap fp) := by
    rw [hEv, ← hE''v, compDivisorOver_valuation q hqb D₁]
    ext t
    simp only [Valuation.comap_apply]
    rw [hcommff t]
  have hpt : f (E.f E.E.genericPoint) = fp (E'.f E'.E.genericPoint) := by
    have h1 : E'.f E'.E.genericPoint = E''.f E''.E.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'v.1 hE''v.symm
    rw [h1]
    change f (p (D₁.f D₁.E.genericPoint)) = fp (q (D₁.f D₁.E.genericPoint))
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  refine ⟨E.toDivisorOver, E.isProper, fun n n' a a' ha ha' => ?_⟩
  -- dimensions
  have hdX : topologicalKrullDim X = n :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha
  have hdX' : topologicalKrullDim X' = n' :=
    MMP.Threefold.Bridges.IsLogDiscrepancy.topologicalKrullDim_eq ha'
  have hdXZ : topologicalKrullDim X = topologicalKrullDim Z := by
    haveI : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
    haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZv.1
    exact (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hfb).symm
  have hdX'Z : topologicalKrullDim X' = topologicalKrullDim Z := hsm'.dim_eq
  have hnn : n = n' := by
    have := hdX'.symm.trans (hdX'Z.trans (hdXZ.symm.trans hdX))
    exact_mod_cast this.symm
  subst hnn
  haveI : AlgebraicGeometry.IsVariety ℂ sX := hXv.1
  haveI : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hWv
  have hdW : topologicalKrullDim W = n :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX (p ≫ sX) hpb).symm.trans
      hdX
  -- the forms
  obtain ⟨m₀, hK0⟩ := hK
  have hm₀ : n = m₀ := by
    have := hK0.topologicalKrullDim_eq.symm.trans hdX
    exact_mod_cast this.symm
  subst hm₀
  obtain ⟨m₁, hK'0⟩ := hK'
  have hm₁ : n = m₁ := by
    have := hK'0.topologicalKrullDim_eq.symm.trans hdX'
    exact_mod_cast this.symm
  subst hm₁
  obtain ⟨ω, hω0, hdiv⟩ := MMP.Fourfold.exists_divisorOfForm_eq hXv hK0
  have hKω : (divisorOfForm ω).IsCanonicalDivisor sX n := hdiv ▸ hK0
  set τ := pullbackRationalPluriForms sX p ω with hτ
  have hτ0 : τ ≠ 0 := MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p
    hpb.functionFieldMap_bijective (toNat_trdeg_functionField_of_topologicalKrullDim_eq hdX) hω0
  obtain ⟨τ', hτ'0, hτ'⟩ := exists_form_divisorOfForm_eq hpq.symm τ hτ0
  obtain ⟨ω', hω'⟩ := exists_pullbackRationalPluriForms_eq q hqb.functionFieldMap_bijective hdX' τ'
  have hω'0 : ω' ≠ 0 := by
    rintro rfl
    exact hτ'0 (hω' ▸ pullbackRationalPluriForms_zero q)
  have hK'ω : (divisorOfForm ω').IsCanonicalDivisor sX' n :=
    isCanonicalDivisor_divisorOfForm_of_isCanonicalDivisor hX'v hK'0 hω'0
  -- the presentations of the two adjoint divisors
  obtain ⟨φ₀, hφ₀⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX'v hK'0
    (m := 1) hω'0
  rw [one_smul] at hφ₀
  set N : Divisor X' := divisorOfForm ω' - K' with hN
  have hNc : N.IsCartier := hφ₀ ▸ Divisor.isCartier_principalDivisor φ₀
  have hNlin : N.LinearlyEquivalent 0 := ⟨φ₀, by rw [sub_zero]; exact hφ₀⟩
  set r'' : Fin (m' + 1) → ℝ := Fin.snoc r' 1 with hr''
  set L'' : Fin (m' + 1) → Divisor X' := Fin.snoc L' N with hL''
  have hL''c : ∀ j, (L'' j).IsCartier := fun j => by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [L''] using hNc
    · simpa [L''] using hL'c i
  have hAX : Divisor.toRDivisor (divisorOfForm ω) + B = ∑ j, (-r j) • Divisor.toRDivisor (L j) := by
    rw [hdiv]
    have := congrArg Neg.neg hA
    simp only [neg_neg] at this
    change logCanonicalDivisor K B = _
    rw [this, ← Finset.sum_neg_distrib]
    simp [neg_smul]
  have hKBX : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B) :=
    ⟨m, fun j => -r j, L, hLc, by rw [hAX]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hAX' : Divisor.toRDivisor (divisorOfForm ω') + B' =
      ∑ j, r'' j • Divisor.toRDivisor (L'' j) := by
    rw [Fin.sum_univ_castSucc]
    simp only [r'', L'', Fin.snoc_castSucc, Fin.snoc_last, one_smul]
    rw [← hA']
    simp only [logCanonicalDivisor, N, map_sub]
    abel
  -- pull-backs to the common model
  set GX : RDivisor W := ∑ j, (-r j) • Divisor.toRDivisor ((L j).pullback (hLc j)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p (L j))) with hGX
  set GY : RDivisor W := ∑ j, r'' j • Divisor.toRDivisor ((L'' j).pullback (hL''c j)
    (MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q (L'' j))) with hGY
  have hGXp : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + B) GX :=
    ⟨m, fun j => -r j, L, _, hLc, hAX, fun j => ⟨_, Divisor.isPullback_pullback _ _⟩, rfl⟩
  have hGYp : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ω') + B') GY :=
    ⟨m' + 1, r'', L'', _, hL''c, hAX', fun j => ⟨_, Divisor.isPullback_pullback _ _⟩, rfl⟩
  set KW := divisorOfForm τ with hKW
  set DW : RDivisor W := GX - Divisor.toRDivisor KW with hDW
  set DW' : RDivisor W := GY - Divisor.toRDivisor KW with hDW'
  have hpbW : IsRCartierPullback p (Divisor.toRDivisor (divisorOfForm ω) + B)
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ω)) + DW) := by
    rw [hDW, ← hτ, ← hKW, add_sub_cancel]; exact hGXp
  have hdivq : divisorOfForm (pullbackRationalPluriForms sX' q ω') = KW := by rw [hω', hτ']
  have hpbW' : IsRCartierPullback q (Divisor.toRDivisor (divisorOfForm ω') + B')
      (Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX' q ω')) + DW') := by
    rw [hdivq, hDW', add_sub_cancel]; exact hGYp
  -- canonical divisors on `W`
  have hKWp : (divisorOfForm (pullbackRationalPluriForms sX p ω)).IsCanonicalDivisor
      (p ≫ sX) n := isCanonicalDivisor_divisorOfForm_pullback hXv hω0 hKω hW hpb hWsm
  have hWsm' : IsSmoothScheme (q ≫ sX') := hpq ▸ hWsm
  have hKWq : (divisorOfForm (pullbackRationalPluriForms sX' q ω')).IsCanonicalDivisor
      (q ≫ sX') n := isCanonicalDivisor_divisorOfForm_pullback hX'v hω'0 hK'ω hWq hqb hWsm'
  -- the crepant transfers to `W`
  have hKBX' : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω') + B') :=
    ⟨m' + 1, r'', L'', hL''c, by rw [hAX']; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hFX := isDiscrepancy_of_isLogDiscrepancy ha hω0 hKω hKBX
  have hFX1 : IsDiscrepancy sX n (divisorOfForm ω) B
      (D₁p.valuation.comap (functionFieldMap p)) (a - 1) := by
    have h1 : E.toDivisorOver.valuation = D₁p.valuation.comap (functionFieldMap p) := hEv
    rw [← h1]; exact hFX
  have hFW := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hXv hω0 hKω hKBX p hW hpb
    hpbW hKWp D₁p (a - 1)).mp hFX1
  have hFX' := isDiscrepancy_of_isLogDiscrepancy ha' hω'0 hK'ω hKBX'
  have hFX'1 : IsDiscrepancy sX' n (divisorOfForm ω') B'
      (D₁.valuation.comap (functionFieldMap q)) (a' - 1) := by
    rw [hD₁]; exact hFX'
  have hFW' := (MMP.Flips.isDiscrepancy_comap_functionFieldMap_iff hX'v hω'0 hK'ω hKBX' q hWq hqb
    hpbW' hKWq D₁ (a' - 1)).mp hFX'1
  rw [hdivq] at hFW'
  have hFW'p := isDiscrepancy_of_eq_structure hpq hFW'
  have hvD : D₁p.valuation = D₁.valuation := rfl
  -- the multiplicity of `F = D_W - D_W'` along `D₁`
  obtain ⟨mF, rF, LF, μ, hμ, hμneg⟩ :=
    exists_isMultiplicityAlong_of_isSmoothScheme hW hWsm (DW - DW') D₁p
  have hsubeq : DW' - DW = -(DW - DW') := by abel
  have hFW'' := IsDiscrepancy.sub_of_isMultiplicityAlong hFW (hsubeq ▸ hμneg)
  rw [hvD] at hFW''
  have heq : a - 1 - -μ = a' - 1 := hFW''.eq hFW'p
  -- the negativity lemma for `F = D_W - D_W'` over `Z`
  set h : W ⟶ Z := p ≫ f with hh
  haveI : IsProper h := by rw [hh]; infer_instance
  have hhs : h ≫ sZ = p ≫ sX := by rw [hh, Category.assoc, hfs]
  have hhb : IsBirationalMorphism h := MMP.Mori.isBirationalMorphism_comp_of_isBirational f p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpb)
  have hhq : h = q ≫ fp := hcomm
  have hFc : IsCartierCombination (DW - DW') :=
    ⟨mF, rF, LF, hμ.2.2.2.1, by rw [hμ.2.2.2.2.1]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]⟩
  have hFexc : ∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ h P →
      (DW - DW').coeff P = 0 := by
    intro P hP
    have hdWZ : topologicalKrullDim W = topologicalKrullDim Z := hdW.trans (hdX.symm.trans hdXZ)
    have hcoP : Order.coheight (h P.genericPoint) = 1 := by
      have h2 := (isExceptionalPrimeDivisor_iff_two_le_coheight hZv h (hhs ▸ hW) hhb P).not.mp hP
      have h1 := MMP.Flips.coheight_le_coheight_map sZ (p ≫ sX) hZv.1 hWv h hhs hdWZ
        P.genericPoint
      rw [P.coheight_genericPoint] at h1
      refine le_antisymm (Order.le_of_lt_add_one ?_) h1
      rw [one_add_one_eq_two]; exact not_le.mp h2
    -- the image in `X`
    have hcop : Order.coheight (p P.genericPoint) = 1 := by
      have h1 := MMP.Flips.coheight_le_coheight_map sX (p ≫ sX) hXv.1 hWv p rfl
        (hdW.trans hdX.symm) P.genericPoint
      have h2 := MMP.Flips.coheight_le_coheight_map sZ sX hZv.1 hXv.1 f hfs hdXZ
        (p P.genericPoint)
      rw [P.coheight_genericPoint] at h1
      rw [show f (p P.genericPoint) = h P.genericPoint from rfl, hcoP] at h2
      exact le_antisymm h2 h1
    have hcoq : Order.coheight (q P.genericPoint) = 1 := by
      have h1 := MMP.Flips.coheight_le_coheight_map sX' (q ≫ sX') hX'v.1 hWq.1 q rfl
        (hdW.trans hdX'.symm) P.genericPoint
      have h2 := MMP.Flips.coheight_le_coheight_map sZ sX' hZv.1 hX'v.1 fp hfps hdX'Z
        (q P.genericPoint)
      rw [P.coheight_genericPoint] at h1
      rw [show fp (q P.genericPoint) = h P.genericPoint by
        rw [hhq, Scheme.Hom.comp_apply], hcoP] at h2
      exact le_antisymm h2 h1
    have hnex : ¬ (⟨W, p, hW, hpb, P⟩ : DivisorOver ℂ sX).IsExceptional := by
      rw [isExceptional_iff_two_le_coheight hXv]
      change ¬ 2 ≤ Order.coheight (p P.genericPoint)
      rw [hcop]; decide
    have hnex' : ¬ (⟨W, q, hWq, hqb, P⟩ : DivisorOver ℂ sX').IsExceptional := by
      rw [isExceptional_iff_two_le_coheight hX'v]
      change ¬ 2 ≤ Order.coheight (q P.genericPoint)
      rw [hcoq]; decide
    obtain ⟨Q, hQ⟩ := MMP.Fourfold.exists_valuation_eq_of_not_isExceptional hXv hnex
    obtain ⟨Q', hQ'⟩ := MMP.Fourfold.exists_valuation_eq_of_not_isExceptional hX'v hnex'
    have hpQ : p P.genericPoint = Q.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hXv.1 hQ
    have hqQ : q P.genericPoint = Q'.genericPoint :=
      MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'v.1 hQ'
    have hd1 := isDiscrepancy_primeDivisor_of_isRCartierPullback hXv hω0 hKω hKBX hW hpb hWsm
      hpbW P
    have hd2 := isDiscrepancy_divisorialValuation hXv ω hω0 hKω hKBX Q
    rw [hQ, valuation_ofPrimeDivisor hXv Q] at hd1
    have he1 := hd1.eq hd2
    have hd1' := isDiscrepancy_primeDivisor_of_isRCartierPullback hX'v hω'0 hK'ω hKBX' hWq hqb
      hWsm' hpbW' P
    have hd2' := isDiscrepancy_divisorialValuation hX'v ω' hω'0 hK'ω hKBX' Q'
    rw [hQ', valuation_ofPrimeDivisor hX'v Q'] at hd1'
    have he2 := hd1'.eq hd2'
    have hQQ' : fp Q'.genericPoint = f Q.genericPoint := by
      rw [← hqQ, ← hpQ]
      have := congrArg (fun g : W ⟶ Z => g P.genericPoint) (hh.symm.trans hhq)
      simpa only [Scheme.Hom.comp_apply] using this.symm
    have hcoef : B'.coeff Q' = B.coeff Q := by
      have hfQ : Order.coheight (f Q.genericPoint) = 1 := by
        rw [← hpQ]; exact hcoP
      rw [hBB]
      simp only [DivisorWithCoeffs.coeff_apply]
      exact flipTransform_apply_of_coheight_eq_one hZv hfb hsm' hfQ hQQ' B
    rw [DivisorWithCoeffs.coeff_sub]
    linarith
  -- `-F` is nef over `Z`
  have hNdeg : ∀ C : ProperCurve sX', N.degreeOn ℂ sX' C.ι C.dim_le hNc = 0 := fun C =>
    MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX' C.ι C.dim_le hNc hNlin
  have hGYnef : IsRelativelyNef ℂ (q ≫ sX') (q ≫ fp) GY := by
    have := isRelativelyNef_neg_sum_pullback (k := ℂ) (sY := sX') q fp (fun j => -r'' j) L'' hL''c
      (fun j => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant q (L'' j))
      (fun C hC => by
        rw [Fin.sum_univ_castSucc]
        simp only [r'', L'', Fin.snoc_castSucc, Fin.snoc_last]
        simp only [hNdeg C, Int.cast_zero, mul_zero, add_zero, neg_mul, Finset.sum_neg_distrib,
          neg_nonpos]
        exact hA'n C hC)
    simpa [GY, neg_smul, Finset.sum_neg_distrib] using this
  have hGXnef : IsRelativelyNef ℂ (p ≫ sX) (p ≫ f) (-GX) :=
    isRelativelyNef_neg_sum_pullback (k := ℂ) (sY := sX) p f (fun j => -r j) L hLc
      (fun j => MMP.Flips.map_componentGenericPoint_notMem_supp_of_isDominant p (L j))
      (fun C hC => by
        simp only [neg_mul, Finset.sum_neg_distrib, neg_nonpos, neg_neg]
        exact hAn C hC)
  have hnef : IsRelativelyNef ℂ (p ≫ sX) h (-(DW - DW')) := by
    have h1 := isRelativelyNef_of_eq_structure hpq hGYnef
    rw [← hhq] at h1
    have h2 := isRelativelyNef_add h1 hGXnef
    have : -(DW - DW') = GY + -GX := by simp only [hDW, hDW']; abel
    rwa [this]
  obtain ⟨hFeff, -⟩ :=
    isEffective_and_preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg ℂ sZ
      (p ≫ sX) hZv hW h hhs hhb hFc hFexc hnef
  have hμ0 : 0 ≤ μ :=
    IsMultiplicityAlong.nonneg hμ (DivisorWithCoeffs.isEffective_iff_nonneg.mp hFeff)
  linarith

end Comparison

end TransferErased

end Transfer

/-! ### Descent of null Cartier divisors across the step -/

section Descent

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

variable {k : Type} [Field k]

/-- With no curve contracted by `f`, `N₁(X/Y) = 0`. -/
private theorem eq_zero_of_forall_not_isContractedBy {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    {f : X ⟶ Y} (h : ∀ C : ProperCurve sX, ¬ C.IsContractedBy f)
    (z : RelativeNumericalCurveClasses sX f) : z = 0 := by
  obtain ⟨⟨Z, hZ⟩, rfl⟩ := relativeNumericalClass_surjective sX f z
  have hZ0 : Z = 0 := by
    rw [relativeOneCycles, Finsupp.mem_supported] at hZ
    ext C
    by_contra hne
    exact h C (hZ (Finsupp.mem_support_iff.mpr hne))
  subst hZ0
  exact map_zero _

/-- The pairing of a `ℚ`-Cartier `ℚ`-divisor with `N₁(X/S)` is its pairing with `N₁(X)`
composed with the natural map `N₁(X/S) → N₁(X)`. -/
private theorem relativeCurveForm_eq_comp {X S : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) (f : X ⟶ S)
    (D : QDivisor X) (h : D.IsQCartier) :
    QDivisor.relativeCurveForm sX f D h =
      QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f := by
  refine Submodule.linearMap_qext _ (LinearMap.ext fun Z => ?_)
  simp only [QDivisor.relativeCurveForm, QDivisor.curveForm, Finsupp.sum, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- The pairing of a `ℚ`-Cartier `ℚ`-divisor with `N₁(X/S)` is continuous. -/
private theorem continuous_relativeCurveForm {X S : Scheme.{0}}
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) (f : X ⟶ S)
    (D : QDivisor X) (h : D.IsQCartier) :
    Continuous (QDivisor.relativeCurveForm sX f D h) := by
  unfold QDivisor.relativeCurveForm
  rw [Finsupp.sum, LinearMap.coe_sum, Finset.sum_fn]
  refine continuous_finsetSum _ fun E _ => ?_
  have := (Divisor.mem_cartierSubgroup.mp E.2).isInvertibleModule_divisorialSheaf
  rw [LinearMap.coe_smul]
  exact (RelativeNumericalCurveClasses.continuous_degree sX f _).const_smul _

/-- **The closed relative cone is negative when `ρ(X/Z) = 1`.** If `D` is negative on every curve
contracted by `f` and `ρ(X/Z) = 1`, then `(D · z) < 0` for every nonzero `z ∈ NE̅(X/Z)`: all of
`N₁(X/Z)` is the line through the class `[A]` of a contracted curve, the cone lies in the closed
half-line where `D` is `≤ 0`, and `D` vanishes only at `0` on that line. -/
private theorem curveForm_relativeToAbsolute_neg {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}
    {f : X ⟶ Z}
    (hρ : MMP.Flips.relativePicardNumber sX f = 1) {D : QDivisor X} (h : D.IsQCartier)
    (hD : ∀ A : ProperCurve sX, A.IsContractedBy f →
      QDivisor.curveForm sX D h (OneCycle.numericalClass sX (A.cycle ℝ)) < 0)
    (z : RelativeNumericalCurveClasses sX f)
    (hz : z ∈ (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f)))
    (hz0 : z ≠ 0) : (QDivisor.curveForm sX D h ∘ₗ relativeToAbsolute sX f) z < 0 := by
  by_cases hA : ∃ A : ProperCurve sX, A.IsContractedBy f
  · obtain ⟨A, hA⟩ := hA
    have hc := continuous_relativeCurveForm sX f D h
    rw [relativeCurveForm_eq_comp] at hc
    exact (isExtremalRay_relativeClosedConeOfCurves hρ _ hc (fun C hC => hD C hC) hA).2 z hz hz0
  · push Not at hA
    exact absurd (eq_zero_of_forall_not_isContractedBy hA z) hz0

section Descent

/-- On an integral, locally Noetherian, normal, quasi-compact scheme every invertible module is
`𝒪(D)` for a Cartier divisor `D`: the divisor of a local frame has the inverse transition
functions as local equations. -/
private theorem exists_isCartier_divisorialSheaf_iso {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L] :
    ∃ D : Divisor Y, D.IsCartier ∧ Nonempty (D.divisorialSheaf ≅ L) := by
  have := Stacks.SheafOfModules.isInvertible_of_tensorInvertible (X := Y.toRingedSpace) L
  have : ∀ z : Y.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk Y.toRingedSpace z) :=
    fun z => Y.isLocalRing z
  choose W hW a ha using fun y : Y =>
    Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible (X := Y.toRingedSpace) L y
  obtain ⟨y₀⟩ : Nonempty Y := inferInstance
  let F : MMP.Mori.LocalFrame L :=
    { W := W, mem := hW, a := a, isLocalGenerator := fun y V hV => ha y V hV, base := y₀ }
  exact ⟨F.divisor, fun y => ⟨F.W y, F.mem y, _, F.isLocalEquation_divisor y⟩,
    ⟨(@asIso _ _ _ _ F.toDivisorialSheaf F.isIso_toDivisorialSheaf).symm⟩⟩

/-- **Descent of a numerically trivial Cartier divisor along a klt-negative contraction.** Let
`f : X ⟶ Z` be a birational contraction of projective varieties with `ρ(X/Z) = 1`, `(X, B)` klt
with `K + B` negative on the curves contracted by `f`. A Cartier divisor `D` of degree zero on
these curves is, up to the divisor of a rational function `u` of `Z`, the pull-back of a Cartier
divisor `E` on `Z`: `D - f^* E = div(f^* u)`. -/
private theorem exists_sub_pullback_eq_principalDivisor {k : Type} [Field k] {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {f : X ⟶ Z} (hfC : IsContraction sX sZ f)
    (hfb : IsBirationalMorphism f)
    (hX : MMP.Mori.IsProjectiveVariety k sX) (hZ : MMP.Mori.IsProjectiveVariety k sZ)
    (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B : QDivisor X} (hB : IsKltPair sX B)
    (hKB : ∃ h : (Divisor.toQDivisor K + B).IsQCartier, ∀ A : ProperCurve sX,
      A.IsContractedBy f →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B) h
          (OneCycle.numericalClass sX (A.cycle ℝ)) < 0)
    {D : Divisor X} (hDc : D.IsCartier)
    (hD0 : ∀ A : ProperCurve sX, A.IsContractedBy f → D.degreeOn k sX A.ι A.dim_le hDc = 0) :
    ∃ (E : Divisor Z) (hEc : E.IsCartier)
      (hfE : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ E.supp)
      (u : (RationalFunctions Z)ˣ)
      (hu : ∀ W : irreducibleComponents X,
        f (componentGenericPoint X W) ∉ (principalDivisor u).supp),
      D - E.pullback (f := f) hEc hfE = principalDivisor (pullbackRationalFunction f u hu) := by
  have hP := hB.1
  have := hP.isAlgClosed
  have := hP.charZero
  have : AlgebraicGeometry.IsProjectiveVariety k sX := hX
  have : AlgebraicGeometry.IsProjectiveVariety k sZ := hZ
  have : IsSeparated sZ := inferInstance
  have : QuasiCompact sX := inferInstance
  have hklt : MMP.Mori.IsKltPair sX n K B := (isKltPair_iff_mori_isKltPair sX hK hP).mp hB
  have hset : IsProjectiveSetting k sX sZ f := ⟨‹_›, ‹_›, hX, hZ, hfC.comp_eq⟩
  have hB0 : 0 ≤ B := fun P => hP.nonneg P
  obtain ⟨hKBq, hKBneg⟩ := hKB
  set F := (relativeClosedConeOfCurves sX f : Set (RelativeNumericalCurveClasses sX f))
  have hFace : IsExtremalFace ℝ F F :=
    ⟨subset_rfl, isCone_coe _, fun u hu v hv => add_mem hu hv, fun u hu v hv _ => ⟨hu, hv⟩⟩
  have hF : IsNegativeExtremalFace ℝ F
      ((QDivisor.curveForm sX (Divisor.toQDivisor K + B) hklt.1.2.2).comp
        (relativeToAbsolute sX f)) F :=
    ⟨hFace, fun u hu v hv => add_mem hu hv, fun z hz hz0 =>
      curveForm_relativeToAbsolute_neg hρ _ hKBneg z hz hz0⟩
  have hψ : IsRelativeContractionOfFace f F f (𝟙 Z) :=
    ⟨hFace, isProjectiveMorphism_id _, Category.comp_id f, hfC.isIso_app, fun C hC =>
      ⟨fun _ => subset_closure (relativeClass_mem_relativeConeOfCurves hC), fun _ => hC⟩⟩
  have := hDc.isInvertibleModule_divisorialSheaf
  obtain ⟨LZ, hLZ, ⟨e⟩⟩ := exists_isInvertible_iso_pullback_of_isRelativeContractionOfFace hset
    hklt hB0 hF hψ D.divisorialSheaf (fun C hC _ => hD0 C hC)
  obtain ⟨E, hEc, ⟨e'⟩⟩ := exists_isCartier_divisorialSheaf_iso LZ
  have := hfb.isDominant
  have hfE := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f E
  obtain ⟨e''⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso (f := f) hEc hfE
  obtain ⟨u, hu⟩ := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso
    (e ≪≫ (Scheme.Modules.pullback f).mapIso e'.symm ≪≫ e''.symm)
  obtain ⟨uZ, huZ, rfl⟩ := exists_pullbackRationalFunction_eq hfb u
  exact ⟨E, hEc, hfE, uZ, huZ, hu⟩

end Descent

section SmallMaps

/-- **Prime divisors across two small maps.** Let `f : X ⟶ Z ⟵ X⁺ : f⁺` with `f` proper
birational, `Z` a normal variety and `f⁺` small. Every prime divisor `P⁺` of `X⁺` has a prime
divisor `P` of `X` whose coefficient in any `D` is that of `P⁺` in the strict transform
`(f⁺)⁻¹_* f_* D`, and at which the pull-backs of any Cartier divisor `G` of `Z` along `f` and
along `f⁺` have the same coefficient: both lie over the same prime divisor of `Z`, with
isomorphic local rings. -/
private theorem exists_primeDivisor_flipTransform_apply {k : Type} [Field k]
    {X Z X' : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)} {f : X ⟶ Z} {fp : X' ⟶ Z}
    (hZ : IsNormalVariety k sZ) [IsProper f] (hfb : IsBirationalMorphism f)
    (hfp : IsSmallMorphism sX' sZ fp) (P' : MMP.Mori.PrimeDivisor X') :
    ∃ P : MMP.Mori.PrimeDivisor X,
      (∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X), flipTransform f fp D P' = D P) ∧
      ∀ {G : Divisor Z} {hG : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ G.supp}
        {hG' : ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ G.supp}
        {G₁ : Divisor X} {G₂ : Divisor X'}, G.IsCartier → G.IsPullback f hG G₁ →
          G.IsPullback fp hG' G₂ → G₁.coeff P = G₂.coeff P' := by
  have := hfb.isDominant
  have := hfp.isBirationalMorphism.isDominant
  obtain ⟨P, Q, -, hPQ, hP'Q⟩ :=
    exists_primeDivisor_valuationOver_eq_of_isSmallMorphism hZ hfb hfp P'
  have hP := map_genericPoint_eq_of_image_eq P Q hPQ
  have hP' := map_genericPoint_eq_of_image_eq P' Q hP'Q
  obtain ⟨P₀, hP₀, htr⟩ :=
    exists_eq_genericPoint_flipTransform_apply hfb hfp P' P.genericPoint (hP.trans hP'.symm)
  obtain rfl : P₀ = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hP₀.symm
  have := isIso_stalkMap_of_map_eq_genericPoint hfb hP
  have := isIso_stalkMap_of_map_eq_genericPoint hfp.isBirationalMorphism hP'
  refine ⟨P₀, htr, fun hGc h₁ h₂ => ?_⟩
  rw [MMP.Positivity.coeff_eq_of_isPullback P₀ Q hP hGc h₁,
    MMP.Positivity.coeff_eq_of_isPullback P' Q hP' hGc h₂]

end SmallMaps

end Descent

/-! ### The data on the next model -/

section StepData

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Flips

section Pullback

variable {k : Type} [Field k] {V T : Scheme.{0}} {sV : V ⟶ Spec (.of k)}
  {sT : T ⟶ Spec (.of k)} [IsSeparated sT] [LocallyOfFiniteType sT]

/-- A morphism non-constant on a proper curve has positive residue degree at its generic
point. -/
private theorem residueFieldDegree_pos (u : V ⟶ T) (hu : u ≫ sT = sV) (Γ : ProperCurve sV)
    (h : ¬ Γ.IsContractedBy u) : 0 < residueFieldDegree u Γ.point := by
  have hnc := Oai4C1.not_exists_range_eq_singleton u Γ h
  set φ := Γ.ι ≫ u with hφdef
  have hφ : φ ≫ sT = Γ.ι ≫ sV := by rw [hφdef, Category.assoc, hu]
  have : IsProper (φ ≫ sT) := hφ ▸ inferInstance
  have hP : IsProper φ := IsProper.of_comp _ sT
  have := Γ.isCurve
  have : AlgebraicGeometry.IsCurve k (φ ≫ sT) := hφ ▸ inferInstance
  have hc : AlgebraicGeometry.IsCurve k (φ.imageι ≫ sT) := isCurve_imageι_comp sT φ hnc
  have : IsIntegral φ.image := hc.toIsIntegral
  have hLφ : LocallyOfFiniteType φ := hP.toLocallyOfFiniteType
  have : QuasiCompact φ := instQuasiCompactOfUniversallyClosed φ
  have : LocallyOfFiniteType φ.toImage := by
    have : LocallyOfFiniteType (φ.toImage ≫ φ.imageι) := by
      rw [Scheme.Hom.toImage_imageι]; exact hLφ
    exact locallyOfFiniteType_of_comp _ φ.imageι
  have : IsDominant φ.toImage := Scheme.instIsDominantToImageOfQuasiCompact φ
  have hdeg : residueFieldDegree u Γ.point = degreeOver φ.toImage := by
    have h1 := residueDegree_comp Γ.ι u (genericPoint Γ.scheme)
    rw [Γ.ι_genericPoint, Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion Γ.ι, mul_one]
      at h1
    have h2 := residueDegree_comp φ.toImage φ.imageι (genericPoint Γ.scheme)
    rw [Scheme.Hom.toImage_imageι,
      Stacks.Chow.residueDegree_eq_one_of_isClosedImmersion φ.imageι,
      one_mul, residueDegree_genericPoint_eq_degreeOver φ.toImage] at h2
    exact h1.symm.trans h2
  rw [hdeg]
  letI := (functionFieldMap φ.toImage).toAlgebra
  have hfin : Module.Finite φ.image.functionField Γ.scheme.functionField :=
    finite_functionField_image sT φ hnc
  have heq : functionFieldMap φ.toImage = dominantFunctionFieldMap φ.toImage :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target φ.toImage (genericPoint Γ.scheme)
        (map_genericPoint_of_isDominant φ.toImage))).symm
  rw [degreeOver_eq_finrank φ.toImage heq]
  exact Module.finrank_pos

end Pullback

/-- A small contraction in the sense of FA 2.12 is a small morphism in the sense of the
background: its exceptional locus lies in the closed subset of codimension two off which it is an
isomorphism. -/
private theorem isSmallMorphism_of_isSmall {X' Z : Scheme.{0}} [IsIntegral X']
    [IsLocallyNoetherian X'] [IsNormal X'] {sX' : X' ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    (hZ : IsNormalVariety ℂ sZ) {fp : X' ⟶ Z} (hfp : MMP.Flips.IsSmall ℂ sZ sX' fp) :
    IsSmallMorphism sX' sZ fp := by
  obtain ⟨V, W, hV, -, hle, hiso⟩ := Transfer.exists_closeds_isIso_of_isSmall hfp
  refine ⟨⟨hfp.isVariety_source, inferInstance⟩, hZ, hfp.comp_eq, hfp.isProper,
    hfp.toIsBirationalContraction.surjective_and_isBirational.2, ?_⟩
  refine MMP.Flips.le_closedsCodimension_iff_le_coheight.mpr fun x hx => hV x ?_
  by_contra hxV
  exact hx (le_biregularLocus hiso (hle hxV))

/-- A birational projective extremal contraction is a contraction in the sense of the
background. -/
private theorem isContraction_of_isNegativeExtremalContraction {X Z : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {E : RDivisor X} {f : X ⟶ Z}
    (hf : MMP.Flips.IsNegativeExtremalContraction ℂ sX sZ E f) (hfb : IsBirationalMorphism f)
    (hfp : IsProjectiveMorphism f) : MMP.Fourfold.IsContraction sX sZ f := by
  haveI : IsProper f := hf.isContraction.isProper
  haveI := hfb.isDominant
  have h1 : Set.range f = Set.univ := by
    rw [← f.isClosedMap.isClosed_range.closure_eq, f.denseRange.closure_range]
  exact ⟨hf.isNormalVariety_source, hf.isNormalVariety_target, hf.isContraction.comp_eq, hfp,
    fun z => h1.ge (Set.mem_univ z), hf.isContraction.isIso_app⟩

/-- The strict transform of a prime divisor is a prime divisor or zero. -/
private theorem flipTransform_single_one {X X' Z : Scheme.{0}} (f : X ⟶ Z) (fp : X' ⟶ Z)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ o : Option (MMP.Mori.PrimeDivisor X'),
      flipTransform f fp (Finsupp.single P (1 : ℤ)) = o.elim 0 (Finsupp.single · 1) := by
  unfold flipTransform
  rw [AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor_single]
  rcases MMP.Mori.RationalMap.transformPrimeDivisor f.toRationalMap P with _ | Q
  · exact ⟨none, by simp⟩
  · rw [Option.elim_some, MMP.Mori.inverseTransformDivisor_single]
    exact ⟨MMP.Mori.inverseTransformPrimeDivisor fp Q, rfl⟩

/-- Two prime divisors of `X⁺` at which every strict transform has the coefficient of the same
prime divisor of `X` coincide. -/
private theorem eq_of_flipTransform_apply_eq {X X' Z : Scheme.{0}} {f : X ⟶ Z} {fp : X' ⟶ Z}
    {P₁ P₂ : MMP.Mori.PrimeDivisor X'} {P : MMP.Mori.PrimeDivisor X}
    (h₁ : ∀ D : Divisor X, flipTransform f fp D P₁ = D P)
    (h₂ : ∀ D : Divisor X, flipTransform f fp D P₂ = D P) : P₁ = P₂ := by
  classical
  obtain ⟨o, ho⟩ := flipTransform_single_one f fp P
  have e₁ := h₁ (Finsupp.single P 1)
  have e₂ := h₂ (Finsupp.single P 1)
  rw [ho, Finsupp.single_eq_same] at e₁ e₂
  rcases o with _ | Q
  · simp at e₁
  · simp only [Option.elim_some, Finsupp.single_apply] at e₁ e₂
    split_ifs at e₁ e₂ with ha hb
    · exact ha.symm.trans hb
    all_goals simp at e₁ e₂

/-- The degree of a Cartier divisor along a curve depends only on the divisor. -/
private theorem degreeOn_congr {k : Type} [Field k] {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)}
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] (C : ProperCurve sX)
    {D₁ D₂ : Divisor X} (h : D₁ = D₂) (h₁ : D₁.IsCartier) (h₂ : D₂.IsCartier) :
    D₁.degreeOn k sX C.ι C.dim_le h₁ = D₂.degreeOn k sX C.ι C.dim_le h₂ := by
  subst h; rfl

/-- **Null curves of a rational affine hull.** On a `ℚ`-factorial variety, if `K + B` has degree
zero on a curve `A`, then so has `K + Φ` for every `Φ` in the smallest rational affine hull of `B`:
the degree of `K + G` on `A`, for `G` supported on `Supp B`, is a rational affine function of the
coefficients of `G`, vanishing at `B`. -/
private theorem absForm_cycle_eq_zero_of_isInSmallestRationalAffineHull {X : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] (hQ : IsQFactorial sX) {K : Divisor X}
    {B Φ : RDivisor X} (hΦ : IsInSmallestRationalAffineHull B Φ) (A : ProperCurve sX)
    (hB : ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
      Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
        absForm sX c L hL (OneCycle.numericalClass sX (A.cycle ℝ)) = 0) :
    ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
      Divisor.toRDivisor K + Φ = ∑ j, c j • Divisor.toRDivisor (L j) →
        absForm sX c L hL (OneCycle.numericalClass sX (A.cycle ℝ)) = 0 := by
  classical
  choose mP hmP hmPC using fun P : MMP.Mori.PrimeDivisor X => hQ.2 (Finsupp.single P 1)
  obtain ⟨mK, hmK, hmKC⟩ := hQ.2 K
  set S := B.support
  let e := S.equivFin
  let p : Fin S.card → MMP.Mori.PrimeDivisor X := fun j => (e.symm j).1
  let Lc : Fin (S.card + 1) → Divisor X :=
    Fin.cons ((mK : ℤ) • K) fun j => ((mP (p j) : ℕ) : ℤ) • Finsupp.single (p j) 1
  have hLc : ∀ j, (Lc j).IsCartier := fun j =>
    Fin.cases (motive := fun j => (Lc j).IsCartier) (by simpa [Lc] using hmKC)
      (fun j => by simpa [Lc] using hmPC (p j)) j
  let cG : RDivisor X → Fin (S.card + 1) → ℝ := fun G =>
    Fin.cons (1 / mK) fun j => G (p j) / mP (p j)
  have hsumS : ∀ F : MMP.Mori.PrimeDivisor X → ℝ,
      ∑ j, F (p j) = ∑ Q ∈ S, F Q := fun F => by
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp e.symm (fun Q : S => F Q)
  -- the canonical presentation of `K + G`
  have hpres : ∀ G : RDivisor X, G.support ⊆ S →
      Divisor.toRDivisor K + G = ∑ j, cG G j • Divisor.toRDivisor (Lc j) := by
    intro G hG
    ext P
    rw [MMP.Flips.coeff_sum_smul_toRDivisor, Fin.sum_univ_succ]
    simp only [cG, Lc, Fin.cons_zero, Fin.cons_succ, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor]
    have hmK0 : (mK : ℝ) ≠ 0 := by exact_mod_cast hmK.ne'
    have h1 : (1 / (mK : ℝ)) * ((((mK : ℤ) • K).coeff P : ℤ) : ℝ) = (K.coeff P : ℝ) := by
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul]
      push_cast
      field_simp
      rfl
    have h2 : ∀ j, G (p j) / mP (p j) *
        ((DivisorWithCoeffs.coeff (((mP (p j) : ℕ) : ℤ) • Finsupp.single (p j) (1 : ℤ)) P : ℤ)
          : ℝ) =
        if p j = P then G P else 0 := fun j => by
      have hm0 : ((mP (p j) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hmP _).ne'
      rw [DivisorWithCoeffs.coeff_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs with hj
      · subst hj; push_cast; field_simp
      · simp
    rw [h1]
    simp only [h2]
    rw [hsumS (fun Q => if Q = P then G P else 0), Finset.sum_ite_eq']
    split_ifs with hPS
    · rfl
    · have : G P = 0 := by
        by_contra h0
        exact hPS (hG (Finsupp.mem_support_iff.mpr h0))
      rw [DivisorWithCoeffs.coeff_apply G P, this]
  -- its value on `A`
  let dK : ℤ := ((mK : ℤ) • K).degreeOn ℂ sX A.ι A.dim_le hmKC
  let d : MMP.Mori.PrimeDivisor X → ℤ := fun P =>
    Divisor.degreeOn ℂ sX A.ι A.dim_le (((mP P : ℕ) : ℤ) • Finsupp.single P (1 : ℤ)) (hmPC P)
  have hval : ∀ G : RDivisor X, absForm sX (cG G) Lc hLc (OneCycle.numericalClass sX (A.cycle ℝ))
      = 1 / mK * dK + ∑ j, G (p j) / mP (p j) * d (p j) := by
    intro G
    rw [absForm_cycle, Fin.sum_univ_succ]
    simp only [cG, Lc, Fin.cons_zero, Fin.cons_succ]
    rfl
  -- the rational affine equation
  let cq : MMP.Mori.PrimeDivisor X →₀ ℚ :=
    ∑ j, Finsupp.single (p j) ((d (p j) : ℚ) / mP (p j))
  have hcq : ∀ G : RDivisor X, (cq.sum fun P cP => (cP : ℝ) * G.coeff P) =
      ∑ j, G (p j) / mP (p j) * d (p j) := by
    intro G
    show (∑ j, Finsupp.single (p j) ((d (p j) : ℚ) / mP (p j))).sum _ = _
    rw [← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.sum_single_index (by simp)]
    push_cast
    rw [DivisorWithCoeffs.coeff_apply]
    ring
  set q : ℚ := -((dK : ℚ) / mK)
  have hq : (q : ℝ) = -((dK : ℝ) / mK) := by simp [q]
  have hdK : 1 / (mK : ℝ) * dK = dK / mK := by ring
  have hBq : (cq.sum fun P cP => (cP : ℝ) * B.coeff P) = q := by
    have h0 := hB _ (cG B) Lc hLc (hpres B subset_rfl)
    rw [hval] at h0
    rw [hcq, hq]
    linarith
  have hΦq := hΦ.2 cq q hBq
  rw [hcq] at hΦq
  have hΦ0 : absForm sX (cG Φ) Lc hLc (OneCycle.numericalClass sX (A.cycle ℝ)) = 0 := by
    rw [hval]
    rw [hq] at hΦq
    linarith
  intro n c L hL heq
  rw [absForm_eq_of_eq hL hLc (heq.symm.trans (hpres Φ hΦ.1))]
  exact hΦ0

/-- **Descent and transport of a null Cartier divisor.** A Cartier divisor `D` of degree zero on
the curves contracted by `f` is `f^* E + div(f^* u)` for a Cartier divisor `E` on `Z` and a
rational function `u` of `Z`, and its strict transform on `X⁺` is `(f⁺)^* E + div((f⁺)^* u)`. -/
private theorem exists_eq_pullback_add_principalDivisor {X Z X' : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Z] [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {f : X ⟶ Z} {fp : X' ⟶ Z} (hfC : MMP.Fourfold.IsContraction sX sZ f)
    (hfb : IsBirationalMorphism f)
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n)
    {B₀ : QDivisor X} (hB₀ : IsKltPair sX B₀)
    (hKB₀ : ∃ h : (Divisor.toQDivisor K + B₀).IsQCartier, ∀ A : ProperCurve sX,
      A.IsContractedBy f →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B₀) h
          (OneCycle.numericalClass sX (A.cycle ℝ)) < 0)
    (hfpS : IsSmallMorphism sX' sZ fp) {D : Divisor X} (hDc : D.IsCartier)
    (hD0 : ∀ A : ProperCurve sX, A.IsContractedBy f → D.degreeOn ℂ sX A.ι A.dim_le hDc = 0) :
    ∃ (E : Divisor Z) (hEc : E.IsCartier)
      (hfE : ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ E.supp)
      (hfpE : ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ E.supp)
      (u : (RationalFunctions Z)ˣ)
      (hu : ∀ W : irreducibleComponents X,
        f (componentGenericPoint X W) ∉ (principalDivisor u).supp)
      (hu' : ∀ W : irreducibleComponents X',
        fp (componentGenericPoint X' W) ∉ (principalDivisor u).supp),
      D = E.pullback hEc hfE + principalDivisor (pullbackRationalFunction f u hu) ∧
        flipTransform f fp D =
          E.pullback hEc hfpE + principalDivisor (pullbackRationalFunction fp u hu') := by
  have hZv := hfC.isNormalVariety_target
  haveI : IsProper f := (IsProjectiveMorphism.isProjective hfC.isProjectiveMorphism).isProper
  haveI := hfb.isDominant
  haveI := hfpS.isBirationalMorphism.isDominant
  obtain ⟨E, hEc, hfE, u, hu, hDE⟩ :=
    exists_sub_pullback_eq_principalDivisor hfC hfb hX hZ hρ hK hB₀ hKB₀ hDc hD0
  have hfpE := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp E
  have hu' := MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' fp
    (principalDivisor u)
  have hDm : D = E.pullback hEc hfE + principalDivisor (pullbackRationalFunction f u hu) := by
    rw [← hDE, add_sub_cancel]
  refine ⟨E, hEc, hfE, hfpE, u, hu, hu', hDm, ?_⟩
  refine Finsupp.ext fun P' => ?_
  obtain ⟨P, htr, hcoeff⟩ := exists_primeDivisor_flipTransform_apply hZv hfb hfpS P'
  rw [htr]
  change D.coeff P =
    (E.pullback hEc hfpE + principalDivisor (pullbackRationalFunction fp u hu')).coeff P'
  rw [hDm, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_add,
    hcoeff hEc (Divisor.isPullback_pullback hEc hfE) (Divisor.isPullback_pullback hEc hfpE),
    hcoeff (Divisor.isCartier_principalDivisor u) (Divisor.isPullback_principalDivisor u hu)
      (Divisor.isPullback_principalDivisor u hu')]

/-- **A rational klt witness for the step.** If `K + C` is negative on every curve contracted by
`f` and `ρ(X/Z) = 1`, some rational klt boundary `B₀` in a convex decomposition of `C` has
`K + B₀` negative on every contracted curve. -/
private theorem exists_isKltPair_curveForm_neg {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    [QuasiCompact sX] (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {C : RDivisor X} (hC0 : 0 ≤ C)
    (hC : IsRealKltPair sX C) {f : X ⟶ Z} (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    {nE : ℕ} {cE : Fin nE → ℝ} {ME : Fin nE → Divisor X} (hME : ∀ j, (ME j).IsCartier)
    (hKE : Divisor.toRDivisor K + C = ∑ j, cE j • Divisor.toRDivisor (ME j))
    (hneg : ∀ A : ProperCurve sX, A.IsContractedBy f →
      absForm sX cE ME hME (OneCycle.numericalClass sX (A.cycle ℝ)) < 0) :
    ∃ B₀ : QDivisor X, IsKltPair sX B₀ ∧
      ∃ h : (Divisor.toQDivisor K + B₀).IsQCartier, ∀ A : ProperCurve sX, A.IsContractedBy f →
        QDivisor.curveForm sX (Divisor.toQDivisor K + B₀) h
          (OneCycle.numericalClass sX (A.cycle ℝ)) < 0 := by
  classical
  obtain ⟨s, Bs, r, m, E, hE, hklt, -, hr, hr1, hm, heq, hEeq, -⟩ :=
    exists_convexCombination_isKltPair_of_isRealKltPair sX hX hQ K hK C hC0 hC
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  -- `K + Bᵢ = (1 / m) Eᵢ`, and `K + C = ∑ (rᵢ / m) Eᵢ`
  have hEi : ∀ i, Divisor.toRDivisor K + QDivisor.toRDivisor (Bs i) =
      (1 / m : ℝ) • Divisor.toRDivisor (E i) := fun i => by
    ext P
    have h : ((E i).coeff P : ℚ) = (m : ℚ) * ((K.coeff P : ℚ) + (Bs i).coeff P) := by
      have := DFunLike.congr_fun (hEeq i) P
      simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at this
      exact this
    have h' : ((E i).coeff P : ℝ) = (m : ℝ) * ((K.coeff P : ℝ) + ((Bs i).coeff P : ℝ)) := by
      exact_mod_cast h
    change (K.coeff P : ℝ) + ((Bs i).coeff P : ℝ) = (1 / m : ℝ) * ((E i).coeff P : ℝ)
    rw [h']
    field_simp
  have hKC : Divisor.toRDivisor K + C = ∑ i, (r i / m) • Divisor.toRDivisor (E i) := by
    rw [heq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hEi i, smul_smul]
    ring_nf
  have hEform : absForm sX cE ME hME = absForm sX (fun i => r i / m) E hE :=
    absForm_eq_of_eq hME hE (hKE.symm.trans hKC)
  -- the curve form of `K + Bᵢ`
  have hqc : ∀ i, (Divisor.toQDivisor K + Bs i).IsQCartier := fun i =>
    ⟨m, hmZ, E i, by rw [hEeq i, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast], hE i⟩
  have hcf : ∀ i (A : ProperCurve sX), QDivisor.curveForm sX (Divisor.toQDivisor K + Bs i) (hqc i)
      (OneCycle.numericalClass sX (A.cycle ℝ)) =
      ((E i).degreeOn ℂ sX A.ι A.dim_le (hE i) : ℝ) / m := fun i A => by
    rw [MMP.ProgramBaseChange.curveForm_numericalClass_cycle,
      QDivisor.intersectionNumber_eq_of_smul ℂ sX A.ι A.dim_le _ (hqc i) hm (E i) (hE i)
        (by rw [hEeq i, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast])]
    push_cast
    rfl
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · subst h0; simp at hr1
    · exact h0
  by_cases hA : ∃ A : ProperCurve sX, A.IsContractedBy f
  swap
  · push Not at hA
    exact ⟨Bs ⟨0, hs⟩, hklt _, hqc _, fun A hA' => absurd hA' (hA A)⟩
  obtain ⟨A₀, hA₀⟩ := hA
  -- some `K + Bᵢ` is negative on `A₀`
  have hsum : ∑ i, r i * (((E i).degreeOn ℂ sX A₀.ι A₀.dim_le (hE i) : ℝ) / m) < 0 := by
    have := hneg A₀ hA₀
    rw [hEform, absForm_cycle] at this
    calc _ = ∑ i, r i / m * ((E i).degreeOn ℂ sX A₀.ι A₀.dim_le (hE i) : ℝ) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ < 0 := this
  obtain ⟨i₀, -, hi₀⟩ : ∃ i ∈ Finset.univ,
      r i * (((E i).degreeOn ℂ sX A₀.ι A₀.dim_le (hE i) : ℝ) / m) < 0 := by
    by_contra! hall
    exact absurd (Finset.sum_nonneg hall) (not_le.mpr hsum)
  have hd₀ : ((E i₀).degreeOn ℂ sX A₀.ι A₀.dim_le (hE i₀) : ℝ) / m < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (hr i₀).le h]
  refine ⟨Bs i₀, hklt i₀, hqc i₀, fun A hA => ?_⟩
  -- every contracted class is a positive multiple of `[A₀]`
  let φE := (absForm sX cE ME hME).comp (relativeToAbsolute sX f)
  have hφE : ∀ (A : ProperCurve sX) (hA : A.IsContractedBy f),
      φE (A.relativeClass f hA) = absForm sX cE ME hME (OneCycle.numericalClass sX (A.cycle ℝ)) :=
    fun A hA => by
      simp only [φE, LinearMap.comp_apply, ProperCurve.relativeClass]
      rw [isNaturalRelativeMap_relativeToAbsolute sX f]
  have hv : A₀.relativeClass f hA₀ ≠ 0 := fun h0 => by
    have := hneg A₀ hA₀
    rw [← hφE A₀ hA₀, h0, map_zero] at this
    exact lt_irrefl _ this
  obtain ⟨c, hc⟩ := exists_smul_eq_of_relativePicardNumber_eq_one hρ hv (A.relativeClass f hA)
  have hcpos : 0 < c := by
    have h1 := hneg A hA
    rw [← hφE A hA, ← hc, map_smul, smul_eq_mul, hφE A₀ hA₀] at h1
    by_contra h
    push Not at h
    nlinarith [hneg A₀ hA₀]
  have hcl : OneCycle.numericalClass sX (A.cycle ℝ) =
      c • OneCycle.numericalClass sX (A₀.cycle ℝ) := by
    have := congrArg (relativeToAbsolute sX f) hc
    simp only [map_smul, ProperCurve.relativeClass, isNaturalRelativeMap_relativeToAbsolute sX f]
      at this
    exact this.symm
  rw [hcl, map_smul, smul_eq_mul, hcf]
  exact mul_neg_of_pos_of_neg hcpos hd₀

/-- **Nefness through the base of the step** (the projection formula). For Cartier divisors
`Eᵢ` on `Z` and weights `wᵢ`, if `∑ wᵢ f^*Eᵢ` is nef over `S` then so is `∑ wᵢ (f⁺)^*Eᵢ`: a curve
of `X⁺` over a point of `S` is either contracted by `f⁺`, where every `(f⁺)^*Eᵢ` has degree zero,
or maps onto a curve of `Z` over a point of `S`, which lifts to a curve of `X` over that point. -/
private theorem sum_degreeOn_pullback_nonneg {X Z X' S : Scheme.{0}}
    [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sZ : Z ⟶ Spec (.of ℂ)} [IsSeparated sZ] [LocallyOfFiniteType sZ] [QuasiCompact sZ]
    (f : X ⟶ Z) (fp : X' ⟶ Z) (h : Z ⟶ S) [IsProper f] [Surjective f] [IsProper fp]
    [QuasiCompact (f ≫ sZ)] [QuasiCompact (fp ≫ sZ)]
    {n : ℕ} (w : Fin n → ℝ) (E : Fin n → Divisor Z) (hEc : ∀ i, (E i).IsCartier)
    (hfE : ∀ i, ∀ W : irreducibleComponents X, f (componentGenericPoint X W) ∉ (E i).supp)
    (hfpE : ∀ i, ∀ W : irreducibleComponents X', fp (componentGenericPoint X' W) ∉ (E i).supp)
    (hnef : ∀ A : ProperCurve (f ≫ sZ), A.IsContractedBy (f ≫ h) →
      0 ≤ ∑ i, w i * (((E i).pullback (hEc i) (hfE i)).degreeOn ℂ (f ≫ sZ) A.ι A.dim_le
        ((hEc i).isCartier_pullback f (hfE i)) : ℝ))
    (A' : ProperCurve (fp ≫ sZ)) (hA' : A'.IsContractedBy (fp ≫ h)) :
    0 ≤ ∑ i, w i * (((E i).pullback (hEc i) (hfpE i)).degreeOn ℂ (fp ≫ sZ) A'.ι A'.dim_le
        ((hEc i).isCartier_pullback fp (hfpE i)) : ℝ) := by
  by_cases hc : A'.IsContractedBy fp
  · have h0 : ∀ i, ((E i).pullback (hEc i) (hfpE i)).degreeOn ℂ (fp ≫ sZ) A'.ι A'.dim_le
        ((hEc i).isCartier_pullback fp (hfpE i)) = 0 := fun i =>
      Divisor.degreeOn_pullback_eq_zero_of_isContractedBy fp rfl (hEc i) (hfpE i) A' hc
    simp [h0]
  obtain ⟨AZ, hAZpt⟩ : ∃ AZ : ProperCurve sZ, AZ.point = fp A'.point :=
    ⟨⟨_, Oai4C1.isProperCurve_map fp rfl A' hc⟩, rfl⟩
  have hAZ : AZ.IsContractedBy h := by
    have h1 := Oai4C1.isContractedBy_map fp rfl h A' hc hA'
    have h2 : AZ = ⟨fp A'.point, Oai4C1.isProperCurve_map fp rfl A' hc⟩ := ProperCurve.ext hAZpt
    rw [h2]; exact h1
  obtain ⟨A, hApt, hAimg⟩ := ProperCurve.exists_map_eq (f ≫ sZ) sZ f rfl AZ
  have hAc : A.IsContractedBy (f ≫ h) := by
    intro x hx
    have hfx : f x ∈ closure ({AZ.point} : Set Z) := hAimg ▸ ⟨x, hx, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hAZ _ hfx]
    exact (congrArg h.base hApt).symm
  have hAnc : ¬ A.IsContractedBy f := by
    intro hcon
    have hsing : closure ({AZ.point} : Set Z) = {AZ.point} := by
      rw [← hAimg]
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨A.point, subset_closure rfl, hApt⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      rw [hcon y hy]
      exact hApt
    have : Subsingleton AZ.scheme := ⟨fun a b => AZ.ι.isEmbedding.injective <| by
      have ha : AZ.ι a ∈ Set.range AZ.ι := ⟨a, rfl⟩
      have hb : AZ.ι b ∈ Set.range AZ.ι := ⟨b, rfl⟩
      rw [AZ.range_ι, hsing] at ha hb
      exact ha.trans hb.symm⟩
    have h0 := topologicalKrullDim_zero_of_discreteTopology AZ.scheme
    rw [AZ.dim_eq] at h0
    exact absurd h0 (by decide)
  have hres := residueFieldDegree_pos f rfl A hAnc
  have hres' := residueFieldDegree_pos fp rfl A' hc
  have e1 : ∀ i, ((E i).pullback (hEc i) (hfE i)).degreeOn ℂ (f ≫ sZ) A.ι A.dim_le
      ((hEc i).isCartier_pullback f (hfE i)) =
      (residueFieldDegree f A.point : ℤ) * (E i).degreeOn ℂ sZ AZ.ι AZ.dim_le (hEc i) := fun i =>
    Transfer.degreeOn_pullback_eq_mul f (hEc i) (hfE i) A AZ hApt.symm
  have e2 : ∀ i, ((E i).pullback (hEc i) (hfpE i)).degreeOn ℂ (fp ≫ sZ) A'.ι A'.dim_le
      ((hEc i).isCartier_pullback fp (hfpE i)) =
      (residueFieldDegree fp A'.point : ℤ) * (E i).degreeOn ℂ sZ AZ.ι AZ.dim_le (hEc i) :=
    fun i => Transfer.degreeOn_pullback_eq_mul fp (hEc i) (hfpE i) A' AZ hAZpt
  have h1 := hnef A hAc
  simp only [e1, e2, Int.cast_mul, Int.cast_natCast] at h1 ⊢
  set T := ∑ i, w i * ((E i).degreeOn ℂ sZ AZ.ι AZ.dim_le (hEc i) : ℝ)
  have hT1 : ∑ i, w i * ((residueFieldDegree f A.point : ℝ) *
      ((E i).degreeOn ℂ sZ AZ.ι AZ.dim_le (hEc i) : ℝ)) =
        (residueFieldDegree f A.point : ℝ) * T := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hT2 : ∑ i, w i * ((residueFieldDegree fp A'.point : ℝ) *
      ((E i).degreeOn ℂ sZ AZ.ι AZ.dim_le (hEc i) : ℝ)) =
      (residueFieldDegree fp A'.point : ℝ) * T := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [hT1] at h1
  rw [hT2]
  have hres0 : (0 : ℝ) < residueFieldDegree f A.point := by exact_mod_cast hres
  have hT : 0 ≤ T := nonneg_of_mul_nonneg_right h1 hres0
  exact mul_nonneg (Nat.cast_nonneg _) hT

/-- **Klt is preserved across the step.** With `-(K + B)` nef over `Z` and `K⁺ + B⁺` nef over
`Z`, presented by Cartier divisors, `(X⁺, B⁺)` is klt when `(X, B)` is: every log discrepancy
over `X⁺` dominates one over `X` (`Transfer.comparison`). -/
private theorem isRealKltPair_of_comparison {X X' Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X'] [IsIntegral Z]
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {sX' : X' ⟶ Spec (.of ℂ)}
    {K : Divisor X} {B : RDivisor X} {K' : Divisor X'} {B' : RDivisor X'} {f : X ⟶ Z}
    {fp : X' ⟶ Z} (hXv : IsNormalVariety ℂ sX) (hZv : IsNormalVariety ℂ sZ)
    (hfs : f ≫ sZ = sX) [IsProper f] (hfb : IsBirationalMorphism f)
    (hsm' : MMP.Flips.IsSmall ℂ sZ sX' fp)
    (hK : ∃ m, K.IsCanonicalDivisor sX m) (hK' : ∃ m, K'.IsCanonicalDivisor sX' m)
    (hBB : B' = flipTransform f fp B)
    {m : ℕ} (r : Fin m → ℝ) (L : Fin m → Divisor X) (hLc : ∀ j, (L j).IsCartier)
    (hA : -logCanonicalDivisor K B = ∑ j, r j • Divisor.toRDivisor (L j))
    (hAn : ∀ C : ProperCurve sX, C.IsContractedBy f →
      0 ≤ ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hLc j) : ℝ))
    {m' : ℕ} (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X') (hL'c : ∀ j, (L' j).IsCartier)
    (hA' : logCanonicalDivisor K' B' = ∑ j, r' j • Divisor.toRDivisor (L' j))
    (hA'n : ∀ C : ProperCurve sX', C.IsContractedBy fp →
      0 ≤ ∑ j, r' j * ((L' j).degreeOn ℂ sX' C.ι C.dim_le (hL'c j) : ℝ))
    (hB : IsRealKltPair sX B) : IsRealKltPair sX' B' := by
  have hX'v : IsNormalVariety ℂ sX' := ⟨hsm'.isVariety_source, inferInstance⟩
  haveI : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  haveI : LocallyOfFiniteType sX' := hX'v.1.toLocallyOfFiniteType
  have hpos : ∀ (n : ℕ) (E' : DivisorOver ℂ sX') (a' : ℝ),
      MMP.Intersection.IsLogDiscrepancy sX' n B' E' a' → 0 < a' := by
    intro n E' a' ha'
    obtain ⟨E, hEp, hcmp⟩ := Transfer.comparison hXv hZv hfs hfb hsm' hK hK' hBB r L hLc hA
      hAn r' L' hL'c hA' hA'n E' ha'.2.1
    obtain ⟨m₀, hK0⟩ := hK
    obtain ⟨ω, hω0, hdiv⟩ := MMP.Fourfold.exists_divisorOfForm_eq hXv hK0
    have hKB : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω) + B) := by
      refine ⟨m, fun j => -r j, L, hLc, ?_⟩
      rw [hdiv]
      have := congrArg Neg.neg hA
      rw [neg_neg] at this
      change logCanonicalDivisor K B = _
      rw [this, ← Finset.sum_neg_distrib]
      simp [neg_smul, MMP.Flips.toRDivisor_eq_mapCoeffs]
    obtain ⟨a, ha⟩ := MMP.Fourfold.exists_isLogDiscrepancy hXv hω0 (hdiv ▸ hK0) hKB E hEp
    exact (hB.2.2.2 m₀ E a ha).trans_le (hcmp m₀ n a a' ha ha')
  obtain ⟨m₁, hK'1⟩ := hK'
  obtain ⟨ω', hω'0, hdiv'⟩ := MMP.Fourfold.exists_divisorOfForm_eq hX'v hK'1
  have hKB' : IsCartierCombination (Divisor.toRDivisor (divisorOfForm ω') + B') := by
    refine ⟨m', r', L', hL'c, ?_⟩
    rw [hdiv']
    change logCanonicalDivisor K' B' = _
    rw [hA']
    simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]
  refine ⟨hX'v, fun P => ?_, ⟨m₁, K', hK'1, m', r', L', hL'c, fun Γ => ?_⟩, hpos⟩
  · have := hpos m₁ _ _ (Transfer.isLogDiscrepancy_ofPrimeDivisor hX'v hω'0 (hdiv' ▸ hK'1) hKB' P)
    linarith
  · have := congrArg (fun D : RDivisor X' => D.coeff Γ) hA'
    simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      MMP.Flips.coeff_sum_smul_toRDivisor] at this
    rw [← this]
    rfl

/-- **The step preserves the data.** For a `D`-null step `X ⟶ Z ⟵ X⁺` of the `D_t`-program over
`S`, the transformed `D⁺` is nef over `S`, the transformed rational boundaries are rational
null-decomposition data for `B⁺` with the same weights and the same `m`, and `C⁺` is an effective
klt boundary. -/
private theorem step_rest {X S Z X' : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [CompactSpace X']
    [IsLocallyNoetherian X'] [IsNormal X']
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ))
    (g : X ⟶ S) (f : X ⟶ Z) (h : Z ⟶ S) (fp : X' ⟶ Z) (hfh : f ≫ h = g)
    {K : Divisor X} {B C : RDivisor X} (hK : K.IsCanonicalDivisor sX 3)
    (ν : RationalNullData sX K B) (hC0 : ∀ P, 0 ≤ C.coeff P) (hC : IsRealKltPair sX C)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX g (MMP.Flips.logCanonicalDivisor K B))
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (hf : MMP.Flips.IsNegativeExtremalContraction ℂ sX sZ
      (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) f)
    (hfb : IsBirationalMorphism f) (hfp : IsProjectiveMorphism f)
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ)
    (hX'Q : IsQFactorial sX') (hX' : MMP.Mori.IsProjectiveVariety ℂ sX')
    (hK' : Divisor.IsCanonicalDivisor sX' 3 (flipTransform f fp K : Divisor X'))
    (hfps : MMP.Flips.IsSmall ℂ sZ sX' fp)
    (hamp : MMP.Flips.IsRelativelyAmple fp
      (MMP.Flips.logCanonicalDivisor (flipTransform f fp K)
        (flipTransform f fp ((1 - t) • B + t • C))))
    (hnull : ∀ A : ProperCurve sX, A.IsContractedBy f →
      ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
        Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
        ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
          NumericalCurveClasses.degree sX (L j).divisorialSheaf
            (OneCycle.numericalClass sX (A.cycle ℝ))) = 0) :
    MMP.Flips.IsRelativelyNef ℂ sX' (fp ≫ h)
        (MMP.Flips.logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B)) ∧
      (∃ (ν' : RationalNullData sX' (flipTransform f fp K) (flipTransform f fp B))
          (hs : ν'.s = ν.s),
        ν'.m = ν.m ∧ ∀ i, ν'.weight i = ν.weight (Fin.cast hs i) ∧
          ν'.boundary i = flipTransform f fp (ν.boundary (Fin.cast hs i))) ∧
      (∀ P, 0 ≤ (flipTransform f fp C).coeff P) ∧
      IsRealKltPair sX' (flipTransform f fp C) := by
  classical
  -- the setting
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := ν.isProjectiveVariety
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sZ := hZ
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX' := hX'
  haveI : QuasiCompact sX := inferInstance
  haveI : QuasiCompact sX' := inferInstance
  have hXv : IsNormalVariety ℂ sX := hf.isNormalVariety_source
  have hZv : IsNormalVariety ℂ sZ := hf.isNormalVariety_target
  haveI : IsIntegral Z := hZv.1.toIsIntegral
  haveI : IsNormal Z := hZv.2
  haveI : LocallyOfFiniteType sZ := hZv.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper f := hf.isContraction.isProper
  haveI : IsProper fp := hfps.isProper
  haveI := hfb.isDominant
  have hfs : f ≫ sZ = sX := hf.isContraction.comp_eq
  have hfps' : fp ≫ sZ = sX' := hfps.comp_eq
  have hX'v : IsNormalVariety ℂ sX' := hX'Q.1
  have hfpS := isSmallMorphism_of_isSmall hZv hfps
  have hfC := isContraction_of_isNegativeExtremalContraction hf hfb hfp
  have hρ := hf.relativePicardNumber_eq_one
  haveI : Surjective f := ⟨hfC.surjective⟩
  -- prime divisors of `X⁺` and of `X`
  choose φ hφ hφpb using fun P' => exists_primeDivisor_flipTransform_apply hZv hfb hfpS P'
  have hφinj : Function.Injective φ := fun P₁ P₂ h12 =>
    eq_of_flipTransform_apply_eq (fun D => hφ P₁ D) (fun D => (hφ P₂ D).trans (by rw [h12]))
  have hcoef : ∀ {R : Type} [AddCommMonoid R] (D : DivisorWithCoeffs R X)
      (P' : MMP.Mori.PrimeDivisor X'),
      (flipTransform f fp D).coeff P' = D.coeff (φ P') := fun D P' => hφ P' D
  -- the rational adjoints `Lᵢ = m (K + Bᵢ)` and the presentation of `D`
  set s := ν.s
  set r := ν.weight
  set m := ν.m
  have hmR : (0 : ℝ) < m := by exact_mod_cast ν.m_pos
  choose L hLC hLeq using ν.isCartier
  have hBi : ∀ i, Divisor.toRDivisor K + QDivisor.toRDivisor (ν.boundary i) =
      ∑ _j : Fin 1, (1 / m : ℝ) • Divisor.toRDivisor (L i) := fun i => by
    rw [Fin.sum_univ_one]; exact toRDivisor_add_eq_smul ν.m_pos (hLeq i)
  have hKB : Divisor.toRDivisor K + B = ∑ i, (r i / m) • Divisor.toRDivisor (L i) := by
    have : Divisor.toRDivisor K + B =
        ∑ i, r i • (Divisor.toRDivisor K + QDivisor.toRDivisor (ν.boundary i)) := by
      simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul]
      rw [ν.sum_weight, one_smul, ← ν.eq_sum]
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hBi i, Fin.sum_univ_one, smul_smul]
    ring_nf
  -- the decomposition adjoints are null on the step
  have hLnull : ∀ i (A : ProperCurve sX), A.IsContractedBy f →
      (L i).degreeOn ℂ sX A.ι A.dim_le (hLC i) = 0 := by
    intro i A hA
    have h0 := absForm_cycle_eq_zero_of_isInSmallestRationalAffineHull ν.isQFactorial
      (ν.mem_hull i) A (fun n c L₀ hL₀ heq => by
        rw [absForm_apply]; exact hnull A hA n c L₀ hL₀ heq)
      1 (fun _ => 1 / m) (fun _ => L i) (fun _ => hLC i) (hBi i)
    rw [absForm_cycle, Fin.sum_univ_one] at h0
    have hm0 : (1 / (m : ℝ)) ≠ 0 := by positivity
    exact_mod_cast (mul_eq_zero.mp h0).resolve_left hm0
  -- `-(K + C) = (1 / t) (-D_t) + ((1 - t) / t) D` is nef over `Z`
  obtain ⟨mt, ρ, At, hmt1, hρpos, hAt, hAteq⟩ := hf.isRelativelyAntiAmple
  have hAtc : ∀ j, (At j).IsCartier := fun j => (hAt j).1
  let cC : Fin (mt + s) → ℝ := Fin.append (fun j => ρ j / t) (fun i => (1 - t) / t * (r i / m))
  let LC : Fin (mt + s) → Divisor X := Fin.append At L
  have hLCc : ∀ j, (LC j).IsCartier := fun j =>
    Fin.addCases (motive := fun j => (LC j).IsCartier) (fun j => by simpa [LC] using hAtc j)
      (fun i => by simpa [LC] using hLC i) j
  have hKCneg : -MMP.Flips.logCanonicalDivisor K C = ∑ j, cC j • Divisor.toRDivisor (LC j) := by
    refine DivisorWithCoeffs.ext' fun P => ?_
    have e1 := congrArg (fun D : RDivisor X => D.coeff P) hAteq
    have e2 := congrArg (fun D : RDivisor X => D.coeff P) hKB
    simp only [MMP.Flips.logCanonicalDivisor, MMP.Flips.coeff_sum_smul_toRDivisor,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_smul,
      Divisor.coeff_toRDivisor, smul_eq_mul] at e1 e2 ⊢
    rw [Fin.sum_univ_add]
    simp only [cC, LC, Fin.append_left, Fin.append_right]
    have ht0' : t ≠ 0 := ht0.ne'
    have s1 : ∑ j, ρ j / t * ((At j).coeff P : ℝ) = (∑ j, ρ j * ((At j).coeff P : ℝ)) / t := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
    have s2 : ∑ i, (1 - t) / t * (r i / m) * ((L i).coeff P : ℝ) =
        (1 - t) / t * ∑ i, r i / m * ((L i).coeff P : ℝ) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [s1, s2, ← e1, ← e2]
    field_simp
    ring
  have hKCnn : ∀ A : ProperCurve sX, A.IsContractedBy f →
      0 < ∑ j, cC j * ((LC j).degreeOn ℂ sX A.ι A.dim_le (hLCc j) : ℝ) := by
    intro A hA
    rw [Fin.sum_univ_add]
    simp only [cC, LC, Fin.append_left, Fin.append_right]
    have hpos : 0 < ∑ j, ρ j / t * ((At j).degreeOn ℂ sX A.ι A.dim_le (hAtc j) : ℝ) :=
      Finset.sum_pos (fun j _ => mul_pos (div_pos (hρpos j) ht0)
        (by exact_mod_cast degreeOn_pos_of_isRelativelyAmpleCartier (hAt j) A hA))
        ⟨⟨0, hmt1⟩, Finset.mem_univ _⟩
    have hzero : ∑ i, (1 - t) / t * (r i / m) *
        ((L i).degreeOn ℂ sX A.ι A.dim_le (hLC i) : ℝ) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hLnull i A hA]; simp
    have e : ∀ j : Fin mt, (At j).degreeOn ℂ sX A.ι A.dim_le (by simpa [LC] using hAtc j) =
        (At j).degreeOn ℂ sX A.ι A.dim_le (hAtc j) := fun j => rfl
    simp only [e] at *
    linarith
  -- a rational klt witness negative on the step
  have hKCpres : Divisor.toRDivisor K + C = ∑ j, (-cC j) • Divisor.toRDivisor (LC j) := by
    have := congrArg Neg.neg hKCneg
    rw [neg_neg] at this
    change MMP.Flips.logCanonicalDivisor K C = _
    rw [this, ← Finset.sum_neg_distrib]
    simp [neg_smul]
  obtain ⟨B₀, hB₀, hKB₀⟩ := exists_isKltPair_curveForm_neg ν.isProjectiveVariety ν.isQFactorial
    hK (C := C) (fun P => hC0 P) hC hρ (fun j => hLCc j) hKCpres (fun A hA => by
      rw [absForm_cycle]
      have := hKCnn A hA
      simp only [neg_mul, Finset.sum_neg_distrib, neg_neg_iff_pos]
      exact this)
  -- descent of the `Lᵢ` and their transforms `L⁺ᵢ = m (K⁺ + B⁺ᵢ)`
  choose E hEc hfE hfpE u hu hu' hLE hLE' using fun i =>
    exists_eq_pullback_add_principalDivisor hfC hfb ν.isProjectiveVariety hZ hρ hK hB₀ hKB₀
      (sX' := sX') hfpS (hLC i) (hLnull i)
  let L' : Fin s → Divisor X' := fun i => flipTransform f fp (L i)
  have hEpC : ∀ i, ((E i).pullback (hEc i) (hfpE i) +
      principalDivisor (pullbackRationalFunction fp (u i) (hu' i))).IsCartier := fun i =>
    ((hEc i).isCartier_pullback fp (hfpE i)).add (Divisor.isCartier_principalDivisor _)
  have hL'C : ∀ i, (L' i).IsCartier := fun i => by
    show Divisor.IsCartier (flipTransform f fp (L i))
    rw [hLE' i]; exact hEpC i
  have hL'deg : ∀ i (A' : ProperCurve sX'), (L' i).degreeOn ℂ sX' A'.ι A'.dim_le (hL'C i) =
      ((E i).pullback (hEc i) (hfpE i)).degreeOn ℂ sX' A'.ι A'.dim_le
        ((hEc i).isCartier_pullback fp (hfpE i)) := by
    intro i A'
    rw [degreeOn_congr A' (hLE' i) (hL'C i) (hEpC i),
      Divisor.degreeOn_add ℂ sX' A'.ι A'.dim_le _ _ ((hEc i).isCartier_pullback fp (hfpE i))
        (Divisor.isCartier_principalDivisor _),
      MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX' A'.ι A'.dim_le
        (Divisor.isCartier_principalDivisor _) ⟨_, sub_zero _⟩, add_zero]
  have hLdeg : ∀ i (A : ProperCurve sX), (L i).degreeOn ℂ sX A.ι A.dim_le (hLC i) =
      ((E i).pullback (hEc i) (hfE i)).degreeOn ℂ sX A.ι A.dim_le
        ((hEc i).isCartier_pullback f (hfE i)) := by
    intro i A
    rw [degreeOn_congr A (hLE i) (hLC i)
      (((hEc i).isCartier_pullback f (hfE i)).add (Divisor.isCartier_principalDivisor _)),
      Divisor.degreeOn_add ℂ sX A.ι A.dim_le _ _ ((hEc i).isCartier_pullback f (hfE i))
        (Divisor.isCartier_principalDivisor _),
      MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX A.ι A.dim_le
        (Divisor.isCartier_principalDivisor _) ⟨_, sub_zero _⟩, add_zero]
  have hL'null : ∀ i (A' : ProperCurve sX'), A'.IsContractedBy fp →
      (L' i).degreeOn ℂ sX' A'.ι A'.dim_le (hL'C i) = 0 := by
    intro i A' hA'
    rw [hL'deg]
    exact Divisor.degreeOn_pullback_eq_zero_of_isContractedBy fp hfps' (hEc i) (hfpE i) A' hA'
  have hL'eq : ∀ i P', (m : ℚ) * (((flipTransform f fp K).coeff P' : ℚ) +
      (flipTransform f fp (ν.boundary i)).coeff P') = (L' i).coeff P' := by
    intro i P'
    simp only [L', hcoef]
    exact hLeq i (φ P')
  -- the transformed adjoint `D⁺ = K⁺ + B⁺`
  have hK'B' : Divisor.toRDivisor (flipTransform f fp K) + flipTransform f fp B =
      ∑ i, (r i / m) • Divisor.toRDivisor (L' i) := by
    refine DivisorWithCoeffs.ext' fun P' => ?_
    have := congrArg (fun D : RDivisor X => D.coeff (φ P')) hKB
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
      MMP.Flips.coeff_sum_smul_toRDivisor] at this ⊢
    simp only [L', hcoef]
    exact this
  have hD'deg : ∀ A' : ProperCurve sX', ∀ x : ℝ, MMP.Flips.IsRIntersectionNumber ℂ sX'
      (MMP.Flips.logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B))
      (fun i => r i / m) L' A' x →
      x = ∑ i, r i / m * ((L' i).degreeOn ℂ sX' A'.ι A'.dim_le (hL'C i) : ℝ) := fun A' x hx =>
    (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX' A').1 _ _ _ _ _ _ _ hx
      (isRIntersectionNumber_sum_degreeOn hL'C hK'B' A')
  -- `D⁺` is nef over `S`
  have hnefS : ∀ A' : ProperCurve sX', A'.IsContractedBy (fp ≫ h) →
      0 ≤ ∑ i, r i / m * ((L' i).degreeOn ℂ sX' A'.ι A'.dim_le (hL'C i) : ℝ) := by
    intro A' hA'
    simp only [hL'deg]
    obtain ⟨m₀, r₀, L₀, hL₀, hD₀, hD₀nef⟩ := hnef
    have hnefX : ∀ A : ProperCurve sX, A.IsContractedBy (f ≫ h) →
        0 ≤ ∑ i, r i / m * (((E i).pullback (hEc i) (hfE i)).degreeOn ℂ sX A.ι A.dim_le
          ((hEc i).isCartier_pullback f (hfE i)) : ℝ) := by
      intro A hA
      have hv := hD₀nef A (hfh ▸ hA) _ (isRIntersectionNumber_sum_degreeOn hL₀ hD₀ A)
      have heqp := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX A).1 _ _ _ _ _ _ _
        (isRIntersectionNumber_sum_degreeOn hL₀ hD₀ A)
        (isRIntersectionNumber_sum_degreeOn hLC hKB A)
      simp only [← hLdeg]
      linarith
    subst hfps' hfs
    exact sum_degreeOn_pullback_nonneg f fp h (fun i => r i / m) E hEc hfE hfpE hnefX A' hA'
  have hnef' : MMP.Flips.IsRelativelyNef ℂ sX' (fp ≫ h)
      (MMP.Flips.logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B)) :=
    ⟨s, fun i => r i / m, L', hL'C, hK'B', fun A' hA' x hx => by
      rw [hD'deg A' x hx]; exact hnefS A' hA'⟩
  -- klt of `B⁺`
  have hDneg : -MMP.Flips.logCanonicalDivisor K B =
      ∑ i, (-(r i / m)) • Divisor.toRDivisor (L i) := by
    change -(Divisor.toRDivisor K + B) = _
    rw [hKB, ← Finset.sum_neg_distrib]
    simp [neg_smul]
  have hB'klt : IsRealKltPair sX' (flipTransform f fp B) :=
    isRealKltPair_of_comparison hXv hZv hfs hfb hfps ⟨3, hK⟩ ⟨3, hK'⟩ rfl
      (fun i => -(r i / m)) L hLC hDneg
      (fun A hA => by simp [hLnull _ A hA])
      (fun i => r i / m) L' hL'C hK'B'
      (fun A' hA' => by simp [hL'null _ A' hA'])
      ν.isRealKltPair
  -- klt of the `B⁺ᵢ`
  have hBi'klt :
      ∀ i, IsRealKltPair sX' (QDivisor.toRDivisor (flipTransform f fp (ν.boundary i))) := by
    intro i
    refine isRealKltPair_of_comparison hXv hZv hfs hfb hfps ⟨3, hK⟩ ⟨3, hK'⟩ ?_
      (fun _ : Fin 1 => -(1 / m)) (fun _ => L i) (fun _ => hLC i) ?_
      (fun A hA => by simp [hLnull _ A hA])
      (fun _ : Fin 1 => 1 / m) (fun _ => L' i) (fun _ => hL'C i) ?_
      (fun A' hA' => by simp [hL'null _ A' hA'])
      (isRealKltPair_toRDivisor hK (ν.isKltPair_boundary i) ν.m_pos (hLC i) (hLeq i))
    · refine DivisorWithCoeffs.ext' fun P' => ?_
      simp only [QDivisor.coeff_toRDivisor, hcoef]
    · change -(Divisor.toRDivisor K + QDivisor.toRDivisor (ν.boundary i)) = _
      rw [toRDivisor_add_eq_smul ν.m_pos (hLeq i), Fin.sum_univ_one, neg_smul, ← smul_neg]
    · change Divisor.toRDivisor (flipTransform f fp K) +
        QDivisor.toRDivisor (flipTransform f fp (ν.boundary i)) = _
      rw [toRDivisor_add_eq_smul ν.m_pos (hL'eq i), Fin.sum_univ_one]
  -- klt of `C⁺`
  obtain ⟨mt', ρ', At', hmt'1, hρ'pos, hAt', hAt'eq⟩ := hamp
  have hAt'c : ∀ j, (At' j).IsCartier := fun j => (hAt' j).1
  let cC' : Fin (mt' + s) → ℝ :=
    Fin.append (fun j => ρ' j / t) (fun i => -((1 - t) / t * (r i / m)))
  let LC' : Fin (mt' + s) → Divisor X' := Fin.append At' L'
  have hLC'c : ∀ j, (LC' j).IsCartier := fun j =>
    Fin.addCases (motive := fun j => (LC' j).IsCartier) (fun j => by simpa [LC'] using hAt'c j)
      (fun i => by simpa [LC'] using hL'C i) j
  have hK'C' : MMP.Flips.logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp C) =
      ∑ j, cC' j • Divisor.toRDivisor (LC' j) := by
    refine DivisorWithCoeffs.ext' fun P' => ?_
    have e1 := congrArg (fun D : RDivisor X' => D.coeff P') hAt'eq
    have e2 := congrArg (fun D : RDivisor X' => D.coeff P') hK'B'
    simp only [MMP.Flips.logCanonicalDivisor, MMP.Flips.coeff_sum_smul_toRDivisor,
      DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, hcoef,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul] at e1 e2 ⊢
    rw [Fin.sum_univ_add]
    simp only [cC', LC', Fin.append_left, Fin.append_right]
    have ht0' : t ≠ 0 := ht0.ne'
    have s1 : ∑ j, ρ' j / t * ((At' j).coeff P' : ℝ) =
        (∑ j, ρ' j * ((At' j).coeff P' : ℝ)) / t := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by ring
    have s2 : ∑ i, -((1 - t) / t * (r i / m)) * ((L' i).coeff P' : ℝ) =
        -((1 - t) / t * ∑ i, r i / m * ((L' i).coeff P' : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [s1, s2, ← e1, ← e2]
    field_simp
    ring
  have hK'Cnn : ∀ A' : ProperCurve sX', A'.IsContractedBy fp →
      0 ≤ ∑ j, cC' j * ((LC' j).degreeOn ℂ sX' A'.ι A'.dim_le (hLC'c j) : ℝ) := by
    intro A' hA'
    rw [Fin.sum_univ_add]
    simp only [cC', LC', Fin.append_left, Fin.append_right]
    have hpos : 0 ≤ ∑ j, ρ' j / t * ((At' j).degreeOn ℂ sX' A'.ι A'.dim_le (hAt'c j) : ℝ) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (div_pos (hρ'pos j) ht0).le
        (by exact_mod_cast (degreeOn_pos_of_isRelativelyAmpleCartier (hAt' j) A' hA').le)
    have hzero : ∑ i, -((1 - t) / t * (r i / m)) *
        ((L' i).degreeOn ℂ sX' A'.ι A'.dim_le (hL'C i) : ℝ) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hL'null i A' hA']; simp
    have e : ∀ j : Fin mt', (At' j).degreeOn ℂ sX' A'.ι A'.dim_le
        (by simpa [LC'] using hAt'c j) = (At' j).degreeOn ℂ sX' A'.ι A'.dim_le (hAt'c j) :=
      fun j => rfl
    simp only [e] at *
    linarith
  have hC'klt : IsRealKltPair sX' (flipTransform f fp C) :=
    isRealKltPair_of_comparison hXv hZv hfs hfb hfps ⟨3, hK⟩ ⟨3, hK'⟩ rfl cC LC hLCc hKCneg
      (fun A hA => (hKCnn A hA).le) cC' LC' hLC'c hK'C' hK'Cnn hC
  -- the transformed rational data
  have hB'0 : ∀ P', 0 ≤ (flipTransform f fp B).coeff P' := fun P' => by
    rw [hcoef]; exact ν.nonneg _
  have hmem : ∀ i, IsInSmallestRationalAffineHull (flipTransform f fp B)
      (QDivisor.toRDivisor (flipTransform f fp (ν.boundary i))) := by
    intro i
    obtain ⟨hsupp, hrat⟩ := ν.mem_hull i
    refine ⟨fun P' hP' => ?_, fun c q hcq => ?_⟩
    · have h1 : QDivisor.toRDivisor (ν.boundary i) (φ P') ≠ 0 := by
        have := Finsupp.mem_support_iff.mp hP'
        rwa [← DivisorWithCoeffs.coeff_apply, QDivisor.coeff_toRDivisor, hcoef,
          ← QDivisor.coeff_toRDivisor, DivisorWithCoeffs.coeff_apply] at this
      have h2 := hsupp (Finsupp.mem_support_iff.mpr h1)
      rw [Finsupp.mem_support_iff] at h2 ⊢
      rwa [← DivisorWithCoeffs.coeff_apply, hcoef, DivisorWithCoeffs.coeff_apply]
    · have key : ∀ G : RDivisor X, ((c.mapDomain φ).sum fun P cP => (cP : ℝ) * G.coeff P) =
          c.sum fun P' cP => (cP : ℝ) * G.coeff (φ P') := fun G =>
        Finsupp.sum_mapDomain_index_inj hφinj
      have h1 : ((c.mapDomain φ).sum fun P cP => (cP : ℝ) * B.coeff P) = q := by
        rw [key, ← hcq]
        exact Finsupp.sum_congr fun P' _ => by rw [hcoef]
      have h2 := hrat _ q h1
      rw [key] at h2
      rw [← h2]
      exact Finsupp.sum_congr fun P' _ => by
        rw [QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, hcoef]
  have hqc : ∀ i, (Divisor.toQDivisor (flipTransform f fp K) +
      flipTransform f fp (ν.boundary i)).IsQCartier := fun i =>
    ⟨m, by exact_mod_cast ν.m_pos.ne', L' i, by
      refine DivisorWithCoeffs.ext' fun P' => ?_
      rw [Divisor.coeff_toQDivisor, ← hL'eq i P']
      simp [DivisorWithCoeffs.coeff_apply, mul_add]
      exact Or.inl (Divisor.coeff_toQDivisor _ P').symm, hL'C i⟩
  let ν' : RationalNullData sX' (flipTransform f fp K) (flipTransform f fp B) :=
    { isQFactorial := hX'Q
      isProjectiveVariety := hX'
      isCanonicalDivisor := ⟨3, hK'⟩
      nonneg := hB'0
      isRealKltPair := hB'klt
      s := s
      boundary := fun i => flipTransform f fp (ν.boundary i)
      boundary_nonneg := fun i P' => by rw [hcoef]; exact ν.boundary_nonneg i _
      isKltPair_boundary := fun i =>
        ⟨⟨inferInstance, inferInstance, ⟨hX'v, 3, _, hK', hqc i⟩,
          fun P' => by rw [hcoef]; exact ν.boundary_nonneg i _⟩, (hBi'klt i).2.2.2⟩
      mem_hull := hmem
      weight := r
      weight_pos := ν.weight_pos
      sum_weight := ν.sum_weight
      eq_sum := by
        refine DivisorWithCoeffs.ext' fun P' => ?_
        have := congrArg (fun D : RDivisor X => D.coeff (φ P')) ν.eq_sum
        simp only [hcoef]
        simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_finset_sum, Finset.sum_apply,
          Finsupp.smul_apply, smul_eq_mul] at this ⊢
        rw [this]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← DivisorWithCoeffs.coeff_apply, ← DivisorWithCoeffs.coeff_apply,
          QDivisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor, hcoef]
      m := m
      m_pos := ν.m_pos
      isCartier := fun i => ⟨L' i, hL'C i, hL'eq i⟩ }
  exact ⟨hnef', ⟨ν', rfl, rfl, fun i => ⟨rfl, rfl⟩⟩,
    fun P' => by rw [hcoef]; exact hC0 _, hC'klt⟩

end StepData

section Main

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- **Small radial perturbations have only null negative rays.** There is `ε`, a positive function
of the number `s` of boundaries, the weights `r : Fin s → ℝ` and the Cartier index `m`, with the
following property. Let `g : X ⟶ S` be a morphism of projective complex varieties over
`Spec ℂ`, with canonical divisor `K` of the threefold `X`, let `B` carry rational
null-decomposition data `ν` (`MMP.Fourfold.RationalNullData`), let `C` be an effective real
boundary with `(X, C)` klt, and suppose `D = K + B` is nef over `S`. Let `0 < t < ε`, for
`ε = ε ν.s ν.weight ν.m`, and `D_t = K + (1 - t) B + t C`.
* Every extremal ray `R` of `NE̅(X/S)` on which `D_t` is negative is `D`-null.
* For every step `X ⟶ Z ⟵ X⁺` of the `D_t`-program over `S` (`f ≫ h = g`), every curve
  contracted by `f` is `D`-null; with `K⁺, B⁺, C⁺` the transforms of `K, B, C`, the divisor
  `K⁺ + B⁺` is nef over `S`, the transforms of the `ν.boundary i` are rational
  null-decomposition data for `B⁺` with the same weights and the same `m`, and `C⁺` is an
  effective real boundary with `(X⁺, C⁺)` klt. -/
@[mmp "lem_fourfold_radial_negative_rays_null"]
public theorem exists_pos_forall_isExtremalRay_null_and_isNegativeExtremalContraction :
    ∃ ε : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ, (∀ s r m, 0 < ε s r m) ∧
      ∀ {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
        (sX : X ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (g : X ⟶ S),
        MMP.Mori.IsProjectiveVariety ℂ sS → g ≫ sS = sX →
        ∀ {K : Divisor X} {B C : RDivisor X}, K.IsCanonicalDivisor sX 3 →
        ∀ ν : RationalNullData sX K B, (∀ P, 0 ≤ C.coeff P) → IsRealKltPair sX C →
        MMP.Flips.IsRelativelyNef ℂ sX g (MMP.Flips.logCanonicalDivisor K B) →
        ∀ t : ℝ, 0 < t → t < ε ν.s ν.weight ν.m →
        -- every `D_t`-negative extremal ray of `NE̅(X/S)` is `D`-null
        (∀ R : Set (RelativeNumericalCurveClasses sX g),
          IsExtremalRay ℝ
            (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R →
          (∃ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
            Divisor.toRDivisor K + ((1 - t) • B + t • C) =
                ∑ j, c j • Divisor.toRDivisor (L j) ∧
              ∀ u ∈ R, u ≠ 0 →
                ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
                  RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) < 0) →
          ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
            Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
            ∀ u ∈ R, ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
              RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf u) = 0) ∧
        -- every step of the `D_t`-program over `S` is `D`-null and preserves the data
        (∀ {Z X' : Scheme.{0}} [IsIntegral X'] [CompactSpace X'] [IsLocallyNoetherian X']
          [IsNormal X'] (sZ : Z ⟶ Spec (.of ℂ)) (sX' : X' ⟶ Spec (.of ℂ)) (f : X ⟶ Z)
          (h : Z ⟶ S) (fp : X' ⟶ Z),
          f ≫ h = g → h ≫ sS = sZ →
          MMP.Flips.IsNegativeExtremalContraction ℂ sX sZ
            (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) f →
          IsBirationalMorphism f → IsProjectiveMorphism f →
          MMP.Mori.IsProjectiveVariety ℂ sZ →
          IsQFactorial sX' → MMP.Mori.IsProjectiveVariety ℂ sX' →
          Divisor.IsCanonicalDivisor sX' 3 (flipTransform f fp K : Divisor X') →
          MMP.Flips.IsSmall ℂ sZ sX' fp → IsProjectiveMorphism fp →
          MMP.Flips.IsRelativelyAmple fp
            (MMP.Flips.logCanonicalDivisor (flipTransform f fp K)
              (flipTransform f fp ((1 - t) • B + t • C))) →
          (∀ A : ProperCurve sX, A.IsContractedBy f →
            ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor X) (hL : ∀ j, (L j).IsCartier),
              Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
              ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
                NumericalCurveClasses.degree sX (L j).divisorialSheaf
                  (OneCycle.numericalClass sX (A.cycle ℝ))) = 0) ∧
          MMP.Flips.IsRelativelyNef ℂ sX' (fp ≫ h)
            (MMP.Flips.logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B)) ∧
          (∃ (ν' : RationalNullData sX' (flipTransform f fp K) (flipTransform f fp B))
              (hs : ν'.s = ν.s),
            ν'.m = ν.m ∧ ∀ i, ν'.weight i = ν.weight (Fin.cast hs i) ∧
              ν'.boundary i = flipTransform f fp (ν.boundary (Fin.cast hs i))) ∧
          (∀ P, 0 ≤ (flipTransform f fp C).coeff P) ∧
          IsRealKltPair sX' (flipTransform f fp C)) := by
  refine ⟨eps, eps_pos, ?_⟩
  intro X S _ _ _ _ sX sS g hS hg K B C hK ν hC0 hC hnef t ht0 htε
  refine ⟨ray_null sX sS g hS hg hK ν hC0 hC hnef t ht0 htε, ?_⟩
  intro Z X' _ _ _ _ sZ sX' f h fp hfh hhs hf hfb hfp hZ hX'Q hX' hK' hfps hfpp hamp
  have hnull := step_null sX sZ g f h hfh hZ hK ν hC0 hC hnef t ht0 htε hf
  exact ⟨hnull, step_rest sX sZ sX' g f h fp hfh hK ν hC0 hC hnef t ht0
    (htε.trans (eps_lt_one _ _ _)) hf hfb hfp hZ hX'Q
    hX' hK' hfps hamp hnull⟩

end Main

end MMP.Fourfold

end
