module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.FiniteGeneration
public import MMP.AlgebraicGeometry.MMP.Fourfold.DltProgram
import MMP.AlgebraicGeometry.MMP.Flip.NullStepCartierIndices
import MMP.AlgebraicGeometry.MMP.Threefold.RadialPerturbationNullRays
import MMP.AlgebraicGeometry.MMP.Threefold.Contraction.RealKltElementaryStep
import MMP.AlgebraicGeometry.Singularities.RealKltRationalDecomposition
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.Positivity.Kleiman.RelativeRhoOne
import MMP.AlgebraicGeometry.MMP.Contraction.ExtremalContractionTrichotomy
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Morphisms.ProjectiveFieldExtension
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain
import MMP.AlgebraicGeometry.MMP.Fourfold.StepDiagram
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization

/-!
# Nef thresholds of real klt threefolds and null negative rays

Let `g : X ⟶ S` be a morphism of projective complex varieties, with `X` a normal `ℚ`-factorial
threefold with canonical divisor `K`, and let `B, H ≥ 0` be real divisors and `t₀ > 0` such that
`(X, B + t₀ H)` is klt and `K + B + t₀ H` is `g`-nef while `K + B` is not. Then there are a
threshold `0 < t ≤ t₀` with `K + B + t H` nef over `S` and an extremal ray `R` of the closed
relative cone `NE̅(X/S)` with
`(K + B) · R < 0`, `(K + B + t H) · R = 0` and `H · R > 0`.
The ray has a contraction `f : X ⟶ Z` over `S`. If `f` is birational, it is followed by the
corresponding elementary real step `X ⟶ Z ⟵ X'` (the contraction itself when `f` is divisorial,
the real flip when `f` is small), and on `X'` the transform of `K + B + t H` is again nef over `S`
and the transform of the level boundary `B + t H` is klt.

## Main results

* `MMP.Fourfold.IsRealKltPair.exists_isExtremalRay_of_isRelativelyNef_add_smul`.

## Implementation notes

The degree of a real divisor `D` on the ray `R` is expressed curvewise: `D · R < 0` means that
`D · C < 0` for every curve `C` contracted by `g` whose class lies in `R`, for every presentation
of `D` by Cartier divisors (`MMP.Flips.IsRIntersectionNumber`); since `X` is `ℚ`-factorial, such
presentations exist. Canonical divisors on the models are the transforms of `K`, as for the
fixed rational top-degree form of the pair convention, so the transformed adjoint on `X'` is
`flipTransform f fp K + flipTransform f fp (B + t • H)`; for a divisorial `f` the morphism
`fp : X' ⟶ Z` is an isomorphism.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.25, 3.36,
  3.37
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips MMP.Fourfold

namespace Proof_lem_fourfold_real_nef_threshold_ray

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-! ### Normalizations of proper curves -/

section Normalization

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
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le⟩

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- An integral scheme proper over `k` is a `k`-variety. -/
private theorem isVariety_of_isProper {Y : Scheme.{0}} [IsIntegral Y] (f : Y ⟶ Spec (.of k))
    [hp : IsProper f] : AlgebraicGeometry.IsVariety k f :=
  { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
    toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{0}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have := isVariety_of_isProper (ν ≫ C.ι ≫ sX)
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one_of_isBirationalMorphism {Y Z : Scheme.{0}} [IsIntegral Y]
    [IsIntegral Z] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) [IsDominant f]
    [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    (hf.functionFieldMap_bijective)
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{0}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := C.isCurve
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one_of_isBirationalMorphism ν hν.isBirationalMorphism, Nat.cast_one,
    one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- For a presentation `D = ∑ⱼ rⱼ Lⱼ`, the number `∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)` is a value of `D · C`. -/
private theorem isRIntersectionNumber_sum_degreeOn (D : RDivisor X) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX) :
    IsRIntersectionNumber k sX D r L C (∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j)) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_curveNormalization C
  refine ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), hD, fun j => ?_, rfl⟩
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

end Normalization

/-! ### Curve degrees of real Cartier divisors -/

section Degree

variable {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] [IsLocallyNoetherian X]
  [IsNormal X]

open Classical in
/-- The degree `D · C` of a real divisor on a proper curve, computed from any presentation of `D`
by Cartier divisors (and `0` if there is none). -/
private noncomputable def cdeg (C : ProperCurve sX) (D : RDivisor X) : ℝ :=
  if h : ∃ x : ℝ, ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      IsRIntersectionNumber ℂ sX D r L C x then h.choose else 0

private theorem eq_cdeg {C : ProperCurve sX} {D : RDivisor X} {m : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {x : ℝ} (h : IsRIntersectionNumber ℂ sX D r L C x) :
    x = cdeg C D := by
  have hex : ∃ x : ℝ, ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      IsRIntersectionNumber ℂ sX D r L C x := ⟨x, m, r, L, h⟩
  rw [cdeg, dif_pos hex]
  obtain ⟨m', r', L', h'⟩ := hex.choose_spec
  exact (IsRIntersectionNumber.eq_and_linear ℂ sX C).1 D r L r' L' _ _ h h'

private theorem isRIntersectionNumber_cdeg (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    IsRIntersectionNumber ℂ sX D r L C (cdeg C D) := by
  have h := isRIntersectionNumber_sum_degreeOn D r L hL hD C
  rwa [← eq_cdeg h]

/-- The degree computed from a presentation. -/
private theorem cdeg_eq_sum (C : ProperCurve sX) {D : RDivisor X} {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) :
    cdeg C D = ∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hL j) : ℝ) :=
  (eq_cdeg (isRIntersectionNumber_sum_degreeOn D r L hL hD C)).symm

/-- A presentation of a real Cartier combination by `Divisor.toRDivisor`. -/
private theorem exists_presentation {D : RDivisor X} (hD : IsCartierCombination D) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X), (∀ j, (L j).IsCartier) ∧
      D = ∑ j, r j • Divisor.toRDivisor (L j) := by
  obtain ⟨m, r, L, hL, hD⟩ := hD
  exact ⟨m, r, L, hL, by simpa [MMP.Flips.toRDivisor_eq_mapCoeffs] using hD⟩

private theorem isCartierCombination_of_presentation {D : RDivisor X} {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) : IsCartierCombination D :=
  ⟨m, r, L, hL, by simpa [MMP.Flips.toRDivisor_eq_mapCoeffs] using hD⟩

/-- `cdeg C D` is a value of `D · C` for some presentation of a real Cartier combination `D`. -/
private theorem exists_isRIntersectionNumber_cdeg (C : ProperCurve sX) {D : RDivisor X}
    (hD : IsCartierCombination D) : ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      IsRIntersectionNumber ℂ sX D r L C (cdeg C D) := by
  obtain ⟨m, r, L, hL, hDL⟩ := exists_presentation hD
  exact ⟨m, r, L, isRIntersectionNumber_cdeg C hL hDL⟩

private theorem isRIntersectionNumber_zero (C : ProperCurve sX) :
    IsRIntersectionNumber ℂ sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) C 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

private theorem cdeg_zero (C : ProperCurve sX) : cdeg C (0 : RDivisor X) = 0 :=
  (eq_cdeg (isRIntersectionNumber_zero C)).symm

private theorem cdeg_add_smul (C : ProperCurve sX) {D₁ D₂ : RDivisor X}
    (h₁ : IsCartierCombination D₁) (h₂ : IsCartierCombination D₂) (a b : ℝ) :
    cdeg C (a • D₁ + b • D₂) = a * cdeg C D₁ + b * cdeg C D₂ := by
  obtain ⟨m₁, r₁, L₁, hL₁, hD₁⟩ := exists_presentation h₁
  obtain ⟨m₂, r₂, L₂, hL₂, hD₂⟩ := exists_presentation h₂
  exact (eq_cdeg ((IsRIntersectionNumber.eq_and_linear ℂ sX C).2 D₁ D₂ r₁ L₁ r₂ L₂ _ _ a b
    (isRIntersectionNumber_cdeg C hL₁ hD₁) (isRIntersectionNumber_cdeg C hL₂ hD₂))).symm

/-- Nefness over a base, for a real Cartier combination, in terms of curve degrees. -/
private theorem isRelativelyNef_iff {Y : Scheme.{0}} (g : X ⟶ Y) {D : RDivisor X}
    (hD : IsCartierCombination D) :
    IsRelativelyNef ℂ sX g D ↔ ∀ C : ProperCurve sX, C.IsContractedBy g → 0 ≤ cdeg C D := by
  constructor
  · rintro ⟨m, r, L, hL, hDL, h⟩ C hC
    exact h C hC _ (isRIntersectionNumber_cdeg C hL hDL)
  · intro h
    obtain ⟨m, r, L, hL, hDL⟩ := exists_presentation hD
    exact ⟨m, r, L, hL, hDL, fun C hC x hx => by rw [eq_cdeg hx]; exact h C hC⟩

/-- On a `ℚ`-factorial variety every real divisor is a real Cartier combination. -/
private theorem isCartierCombination_of_isQFactorial [IsIntegral X] (hX : IsQFactorial sX)
    (D : RDivisor X) : IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := hX.isRCartier D
  refine isCartierCombination_of_presentation (r := r) (L := C) hC (Finsupp.ext fun P => ?_)
  have h1 := hD P
  have h2 := MMP.Fourfold.coeff_sum_smul_toRDivisor r C P
  simp only [DivisorWithCoeffs.coeff_apply] at h1 h2
  rw [h1, h2]

variable [CompactSpace X]

/-- The degree of a Cartier divisor on the relative class of a contracted curve. -/
private theorem relDegree_relativeClass {Y : Scheme.{0}} (g : X ⟶ Y) (C : ProperCurve sX)
    (hC : C.IsContractedBy g) (L : Divisor X) (hL : L.IsCartier) :
    haveI := hL.isInvertibleModule_divisorialSheaf
    RelativeNumericalCurveClasses.degree sX g L.divisorialSheaf (C.relativeClass g hC) =
      (L.degreeOn ℂ sX C.ι C.dim_le hL : ℝ) := by
  haveI := hL.isInvertibleModule_divisorialSheaf
  rw [ProperCurve.relativeClass, RelativeNumericalCurveClasses.degree_relativeNumericalClass]
  exact OneCycle.degree_cycle ℝ _ C

private theorem sum_relDegree_relativeClass {Y : Scheme.{0}} (g : X ⟶ Y) {D : RDivisor X}
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX)
    (hC : C.IsContractedBy g) :
    ∑ j, r j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf (C.relativeClass g hC)) =
      cdeg C D := by
  rw [cdeg_eq_sum C hL hD]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [relDegree_relativeClass]

private theorem sum_relDegree_smul_relativeClass {Y : Scheme.{0}} (g : X ⟶ Y) {D : RDivisor X}
    {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} (hL : ∀ j, (L j).IsCartier)
    (hD : D = ∑ j, r j • Divisor.toRDivisor (L j)) (C : ProperCurve sX)
    (hC : C.IsContractedBy g) (c : ℝ) :
    ∑ j, r j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sX g (L j).divisorialSheaf
        (c • C.relativeClass g hC)) = c * cdeg C D := by
  rw [← sum_relDegree_relativeClass g hL hD C hC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]
  ring

/-- The degree on a contracted curve depends only on its relative numerical class. -/
private theorem cdeg_eq_mul_of_relativeClass_eq {Y : Scheme.{0}} (g : X ⟶ Y) {D : RDivisor X}
    (hD : IsCartierCombination D) {C C₀ : ProperCurve sX} {hC : C.IsContractedBy g}
    {hC₀ : C₀.IsContractedBy g} {c : ℝ}
    (h : C.relativeClass g hC = c • C₀.relativeClass g hC₀) :
    cdeg C D = c * cdeg C₀ D := by
  obtain ⟨m, r, L, hL, hDL⟩ := exists_presentation hD
  rw [← sum_relDegree_relativeClass g hL hDL C hC, h,
    sum_relDegree_smul_relativeClass g hL hDL C₀ hC₀ c]

/-- A morphism of relative Picard number one contracts some curve. -/
private theorem exists_isContractedBy_of_relativePicardNumber_eq_one {Y : Scheme.{0}}
    {f : X ⟶ Y} (h : MMP.Flips.relativePicardNumber sX f = 1) :
    ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hne
  push Not at hne
  have htop : relativeNumericallyTrivialDivisors sX f = ⊤ :=
    eq_top_iff.2 fun D _ => (mem_relativeNumericallyTrivialDivisors sX f).2 fun C hC =>
      absurd hC (hne C)
  have : Subsingleton (KCartierDivisor ℝ X ⧸ relativeNumericallyTrivialDivisors sX f) :=
    Submodule.Quotient.subsingleton_iff.2 htop
  rw [MMP.Flips.relativePicardNumber, rank_subsingleton'] at h
  simp at h

/-- An `f`-ample real divisor has positive degree on every curve contracted by `f`. -/
private theorem cdeg_pos_of_isRelativelyAmple {Z : Scheme.{0}} {f : X ⟶ Z} {D : RDivisor X}
    (hD : MMP.Flips.IsRelativelyAmple f D) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < cdeg C D := by
  obtain ⟨m, r, L, hm, hr, hL, hDL⟩ := hD
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  rw [cdeg_eq_sum C hLc hDL]
  have hpos : ∀ j, 0 < ((L j).degreeOn ℂ sX C.ι C.dim_le (hLc j) : ℝ) := fun j => by
    obtain ⟨hL', hamp⟩ := hL j
    haveI := hL'.isInvertibleModule_divisorialSheaf
    have hrel : MMP.Mori.IsRelativelyAmple f (L j).divisorialSheaf := fun y => by
      obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
      exact ⟨V, hV, hyV, hamp V hV⟩
    exact Int.cast_pos.mpr
      (MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC)
  exact Finset.sum_pos (fun j _ => mul_pos (hr j) (hpos j)) ⟨⟨0, hm⟩, Finset.mem_univ _⟩

/-- **Relative Kleiman criterion in Picard number one, curvewise.** A real Cartier combination of
positive degree on every curve contracted by a projective morphism of relative Picard number one
is relatively ample. -/
private theorem isRelativelyAmple_of_forall_pos {Z : Scheme.{0}} {sZ : Z ⟶ Spec (.of ℂ)}
    (hXn : IsNormalVariety ℂ sX) (hZn : IsNormalVariety ℂ sZ) {f : X ⟶ Z} (hf : IsProjective f)
    (hfs : f ≫ sZ = sX) (hρ : MMP.Flips.relativePicardNumber sX f = 1) {D : RDivisor X}
    (hD : IsCartierCombination D)
    (hpos : ∀ C : ProperCurve sX, C.IsContractedBy f → 0 < cdeg C D) :
    MMP.Flips.IsRelativelyAmple f D := by
  obtain ⟨C₀, hC₀⟩ := exists_isContractedBy_of_relativePicardNumber_eq_one hρ
  refine isRelativelyAmple_of_isRelativelyNef_of_relativePicardNumber_eq_one sX sZ hXn hZn f hf
    hfs hρ D hD ((isRelativelyNef_iff f hD).2 fun C hC => (hpos C hC).le) fun htriv => ?_
  obtain ⟨-, -, htriv⟩ := htriv
  obtain ⟨m, r, L, hx⟩ := exists_isRIntersectionNumber_cdeg C₀ hD
  exact (hpos C₀ hC₀).ne' (htriv C₀ hC₀ m r L _ 0 Fin.elim0 Fin.elim0 0 hx
    (isRIntersectionNumber_zero C₀))

variable [IsIntegral X]

/-- Linearly equivalent divisors have the same degree on every curve. -/
private theorem cdeg_toRDivisor_eq_of_linearlyEquivalent (hX : IsQFactorial sX)
    (C : ProperCurve sX) {K K' : Divisor X} (h : K.LinearlyEquivalent K') :
    cdeg C (Divisor.toRDivisor K) = cdeg C (Divisor.toRDivisor K') := by
  obtain ⟨φ, hφ⟩ := h
  have hP : (principalDivisor φ).IsCartier := Divisor.isCartier_principalDivisor φ
  have hK : Divisor.toRDivisor K =
      (1 : ℝ) • Divisor.toRDivisor K' + (1 : ℝ) • Divisor.toRDivisor (principalDivisor φ) := by
    rw [← hφ, one_smul, one_smul, ← map_add]
    congr 1
    abel
  have h0 : cdeg C (Divisor.toRDivisor (principalDivisor φ)) = 0 := by
    rw [cdeg_eq_sum (r := fun _ : Fin 1 => 1) (L := fun _ => principalDivisor φ) C (fun _ => hP)
      (by simp)]
    simp only [Fin.sum_univ_one, one_mul, Int.cast_eq_zero]
    exact MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le _
      (Divisor.linearlyEquivalent_principalDivisor_zero φ)
  rw [hK, cdeg_add_smul C (isCartierCombination_of_isQFactorial hX _)
    (isCartierCombination_of_isQFactorial hX _), h0]
  ring

/-- The degree of `K + D` depends on the canonical divisor `K` only through its degree. -/
private theorem cdeg_logCanonicalDivisor_congr (hX : IsQFactorial sX) (C : ProperCurve sX)
    {K K' : Divisor X} (h : K.LinearlyEquivalent K') (D : RDivisor X) :
    cdeg C (logCanonicalDivisor K D) = cdeg C (logCanonicalDivisor K' D) := by
  have e : ∀ K₀ : Divisor X, logCanonicalDivisor K₀ D =
      (1 : ℝ) • Divisor.toRDivisor K₀ + (1 : ℝ) • D := fun K₀ => by
    rw [one_smul, one_smul]; rfl
  rw [e K, e K', cdeg_add_smul C (isCartierCombination_of_isQFactorial hX _)
    (isCartierCombination_of_isQFactorial hX _), cdeg_add_smul C
    (isCartierCombination_of_isQFactorial hX _) (isCartierCombination_of_isQFactorial hX _),
    cdeg_toRDivisor_eq_of_linearlyEquivalent hX C h]

end Degree

/-! ### The nef threshold -/

/-- The least parameter of a closed family of linear inequalities: if `a i + t₀ b i ≥ 0` for all
`i` but not `a i ≥ 0` for all `i`, then the set of `t ∈ [0, t₀]` with `a i + t b i ≥ 0` for all `i`
has a positive least element. -/
private theorem exists_threshold {ι : Type*} (p : ι → Prop) (a b : ι → ℝ) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (h₀ : ∀ i, p i → 0 ≤ a i + t₀ * b i) (hnot : ¬ ∀ i, p i → 0 ≤ a i) :
    ∃ l : ℝ, 0 < l ∧ l ≤ t₀ ∧ (∀ i, p i → 0 ≤ a i + l * b i) ∧
      ∀ t, 0 ≤ t → t < l → ¬ ∀ i, p i → 0 ≤ a i + t * b i := by
  set T : Set ℝ := Set.Icc 0 t₀ ∩ ⋂ i, ⋂ (_ : p i), {t | 0 ≤ a i + t * b i} with hT
  have hTc : IsClosed T := by
    rw [hT]
    exact isClosed_Icc.inter (isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_const.add (continuous_id.mul continuous_const)))
  have hmem : ∀ t, t ∈ T ↔ (0 ≤ t ∧ t ≤ t₀) ∧ ∀ i, p i → 0 ≤ a i + t * b i := by
    intro t
    rw [hT]
    simp
  have hT0 : t₀ ∈ T := (hmem _).2 ⟨⟨ht₀, le_rfl⟩, h₀⟩
  have hbdd : BddBelow T := ⟨0, fun t ht => ((hmem t).1 ht).1.1⟩
  obtain ⟨⟨hl0, hlt⟩, hl⟩ := (hmem _).1 (hTc.csInf_mem ⟨t₀, hT0⟩ hbdd)
  refine ⟨sInf T, lt_of_le_of_ne hl0 fun h => hnot fun i hi => ?_, hlt, hl,
    fun t ht0 htl ht => ?_⟩
  · have := hl i hi
    rw [← h] at this
    simpa using this
  · exact absurd (csInf_le hbdd ((hmem t).2 ⟨⟨ht0, htl.le.trans hlt⟩, ht⟩)) (not_le.2 htl)

/-! ### Lowering a real klt boundary -/

/-- On a `ℚ`-factorial variety a real divisor coefficientwise below a real klt boundary is a real
klt boundary: removing the effective `ℝ`-Cartier divisor `C - B` raises every log discrepancy by
the coefficient of its effective pull-back. -/
private theorem isRealKltPair_of_le {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] (sX : X ⟶ Spec (.of ℂ)) (hX : IsQFactorial sX)
    {C B : RDivisor X} (hC : IsRealKltPair sX C) (hle : ∀ P, B.coeff P ≤ C.coeff P) :
    IsRealKltPair sX B := by
  classical
  refine ⟨hX.1, fun P => (hle P).trans_lt (hC.2.1 P), ?_, ?_⟩
  · obtain ⟨n, K, hK, -⟩ := hC.2.2.1
    exact ⟨n, K, hK, hX.isRCartier _⟩
  · intro n E a ha
    obtain ⟨hXn, hprop, ω, hω, hKω, m, r, L, L', hL, hsum, hpb, rfl⟩ := ha
    obtain ⟨m₂, s, M, hM, hMsum⟩ := hX.isRCartier (C - B)
    haveI := E.isIntegral
    haveI := E.isLocallyNoetherian
    haveI := E.isNormal
    haveI := E.isDominant
    haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
    choose M' hM' using fun j => (hM j).exists_isPullback
      (MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j))
    have hMpb : ∀ j, ∃ h, (M j).IsPullback E.f h (M' j) := fun j =>
      ⟨MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isDominant E.f (M j), hM' j⟩
    have hpos := hC.2.2.2 n E _ ⟨hXn, hprop, ω, hω, hKω, m + m₂, Fin.append r s, Fin.append L M,
      Fin.append L' M', Fin.addCases (fun i => by simpa using hL i) (fun j => by simpa using hM j),
      fun Γ => ?_, Fin.addCases (fun i => by simpa using hpb i)
        (fun j => by simpa using hMpb j), rfl⟩
    · rw [Fin.sum_univ_add] at hpos
      simp only [Fin.append_left, Fin.append_right] at hpos
      have heff := (isEffective_of_isRCartierPullback E.f ⟨m₂, s, M, hM, hMsum⟩
        fun P => sub_nonneg.mpr (hle P)).2
        (∑ j, s j • Divisor.toRDivisor (M' j))
        ⟨m₂, s, M, M', hM, by ext P; rw [hMsum P, MMP.Fourfold.coeff_sum_smul_toRDivisor],
          hMpb, rfl⟩
      have hE := heff E.E
      rw [show (∑ j, s j • Divisor.toRDivisor (M' j)) E.E =
        (∑ j, s j • Divisor.toRDivisor (M' j)).coeff E.E from rfl,
        MMP.Fourfold.coeff_sum_smul_toRDivisor] at hE
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hE
      linarith
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      have h1 := hsum Γ
      have h2 := hMsum Γ
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_sub, Pi.sub_apply] at h1 h2 ⊢
      linarith

/-! ### Morphisms -/

/-- Morphisms to `Spec ℂ` agreeing after a morphism `f` with `f_* 𝒪 = 𝒪` agree. -/
private theorem eq_of_comp_eq_of_isIso_app {X Z : Scheme.{0}} {f : X ⟶ Z}
    (hf : ∀ U : Z.Opens, IsIso (f.app U)) {a b : Z ⟶ Spec (.of ℂ)} (h : f ≫ a = f ≫ b) :
    a = b := by
  have : IsIso f.appTop := hf ⊤
  refine ext_of_isAffine ?_
  have h2 := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h2
  exact (cancel_mono f.appTop).1 h2

/-- A curve contracted by `f` is contracted by `f ≫ h`. -/
private theorem isContractedBy_comp {X Z S : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {C : ProperCurve sX} {f : X ⟶ Z} (h : Z ⟶ S) (hC : C.IsContractedBy f) :
    C.IsContractedBy (f ≫ h) := fun x hx => by
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC x hx]

/-- The points near which `f` is not an open immersion lie over the complement of the biregular
locus. -/
private theorem exceptionalSet_subset {X Y : Scheme.{0}} (f : Y ⟶ X) :
    MMP.Flips.exceptionalSet f ⊆ (MMP.Mori.exceptionalSet f : Set Y) := by
  intro y hy
  by_contra hyM
  apply hy
  have : IsIso (f ∣_ biregularLocus f) := MMP.Mori.isBiregular_biregularLocus f
  refine ⟨f ⁻¹ᵁ biregularLocus f, ?_, ?_⟩
  · by_contra h
    exact hyM (MMP.Mori.mem_exceptionalSet.mpr h)
  · rw [← morphismRestrict_ι]
    infer_instance

/-- A proper birational morphism onto a normal integral scheme is an isomorphism over every point
with finite fibre. -/
private theorem mem_biregularLocus_of_finite {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z]
    [IsNormal Z] (f : X ⟶ Z) [IsProper f] (hb : IsBirationalMorphism f) {z : Z}
    (hz : (f ⁻¹' {z}).Finite) : z ∈ biregularLocus f := by
  obtain ⟨hU, hiso⟩ := (MMP.Resolution.Bridges.isOpen_finiteFibreLocus_and_isIso f
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hb)).1 inferInstance
  exact le_biregularLocus (V := ⟨_, hU⟩) hiso hz

/-- **The two exceptional sets of a proper birational morphism onto a normal variety agree.** A
point `y` near which `f` is an open immersion is alone in its fibre: the fibre is connected, `y`
is open in it, and `y` is closed in it since a nontrivial specialization `y ⤳ z` inside the fibre
would raise the coheight above `coheight (f y) = coheight y`. -/
private theorem coe_exceptionalSet_eq {X Y : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    {sY : Y ⟶ Spec (.of ℂ)} (hX : IsNormalVariety ℂ sX) (hY : MMP.Mori.IsVariety ℂ sY)
    (f : Y ⟶ X) [IsProper f] (hf : f ≫ sX = sY) (hb : IsBirationalMorphism f) :
    (MMP.Mori.exceptionalSet f : Set Y) = MMP.Flips.exceptionalSet f := by
  haveI := hX.1.toIsIntegral
  haveI := hY.toIsIntegral
  haveI := hX.2
  haveI : MMP.Mori.IsVariety ℂ sX := hX.1
  haveI : MMP.Mori.IsVariety ℂ sY := hY
  haveI : LocallyOfFiniteType sY := hY.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  refine Set.Subset.antisymm (fun y hy => ?_) (exceptionalSet_subset f)
  by_contra hyF
  obtain ⟨U, hyU, hU⟩ := MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet hyF
  have hdim : topologicalKrullDim Y = topologicalKrullDim X :=
    (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sX sY hb).symm
  have hinj : ∀ z ∈ (U : Set Y), f z = f y → z = y := by
    intro z hz hzy
    have := (U.ι ≫ f).isOpenEmbedding.injective (a₁ := ⟨z, hz⟩) (a₂ := ⟨y, hyU⟩) hzy
    exact congrArg Subtype.val this
  have hcl : ∀ z, f z = f y → y ⤳ z → z = y := by
    intro z hzy hyz
    by_contra hne
    have h1 := MMP.Flips.coheight_le_coheight_map sX sY hX.1 hY f hf hdim z
    rw [hzy, MMP.Flips.coheight_map_of_notMem_exceptionalSet hyF] at h1
    exact (coheight_lt_coheight_of_specializes Y hyz (Ne.symm hne)).not_ge h1
  have hconn := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sY sX
    hY hX f hb).2 (f y)
  have hyf : y ∈ f ⁻¹' {f y} := rfl
  have hcov : f ⁻¹' {f y} ⊆ (U : Set Y) ∪ (closure {y})ᶜ := by
    intro z hz
    by_cases hzc : z ∈ closure {y}
    · left
      rw [hcl z hz (specializes_iff_mem_closure.mpr hzc)]
      exact hyU
    · exact Or.inr hzc
  have hdisj : f ⁻¹' {f y} ∩ ((U : Set Y) ∩ (closure {y})ᶜ) = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, Set.mem_compl_iff,
      not_and, not_not]
    intro hz hzU
    rw [hinj z hzU hz]
    exact subset_closure (Set.mem_singleton y)
  have hsub : f ⁻¹' {f y} ⊆ (U : Set Y) := by
    rcases isPreconnected_iff_subset_of_disjoint.mp hconn.isPreconnected U (closure {y})ᶜ
      U.isOpen isClosed_closure.isOpen_compl hcov hdisj with h | h
    · exact h
    · exact absurd (subset_closure (Set.mem_singleton y)) (h hyf)
  have hfin : (f ⁻¹' {f y}).Finite :=
    (Set.finite_singleton y).subset fun z hz => hinj z (hsub hz) hz
  exact MMP.Mori.mem_exceptionalSet.mp hy (mem_biregularLocus_of_finite f hb hfin)

/-- The strict transform `𝟙⁻¹_* f_*` along `f` and the identity is the push-forward `f_*`. -/
private theorem flipTransform_id {R : Type*} [AddCommMonoid R] {X Y : Scheme.{0}} (f : X ⟶ Y)
    (D : DivisorWithCoeffs R X) :
    flipTransform f (𝟙 Y) D = RationalMap.transformDivisor (X := X) f.toRationalMap D := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Fourfold.inverseTransformDivisor_id]

/-- The identity of a normal variety is a small birational contraction. -/
private theorem isSmall_id {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (hX : IsNormalVariety ℂ sX) : MMP.Flips.IsSmall ℂ sX sX (𝟙 X) := by
  haveI := hX.1.toIsIntegral
  haveI := hX.2
  have hbc : MMP.Flips.IsBirationalContraction ℂ sX sX (𝟙 X) :=
    { isVariety_target := hX.1
      isVariety_source := hX.1
      comp_eq := Category.id_comp sX
      isProper := inferInstance
      isIso_app := fun U => inferInstance
      dim_eq := rfl }
  refine (MMP.Flips.isSmall_iff_two_le_closedsCodimension_exceptionalSet hbc).mpr ?_
  rw [le_closedsCodimension_iff]
  intro W hW
  obtain ⟨x, hx⟩ := W.isIrreducible.nonempty
  refine absurd (hW hx) fun hxE => hxE ⟨⊤, by simp, ?_⟩
  rw [Category.comp_id]
  infer_instance

/-- Every Cartier divisor is ample relative to an isomorphism. -/
private theorem isRelativelyAmpleCartier_of_isIso {Y X : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (e : Y ⟶ X) [IsIso e] {L : Divisor Y} (hL : L.IsCartier) :
    IsRelativelyAmpleCartier e L := by
  refine ⟨hL, fun U hU => ?_⟩
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI : IsAffine (e ⁻¹ᵁ U) := hU.preimage e
  haveI : CompactSpace (e ⁻¹ᵁ U) := inferInstance
  have hinv : Stacks.Ample.IsInvertibleModule (e ⁻¹ᵁ U).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (e ⁻¹ᵁ U).ι.toLRSHom.toShHom).obj
        L.divisorialSheaf) := inferInstance
  exact (Stacks.AmpleBridge.isAmple_iff_isAmple _ _).mpr
    (@AlgebraicGeometry.Scheme.Modules.isAmple_of_isAffine_of_isInvertible _ _ _ _ hinv)

/-- A sum of relatively ample real divisors is relatively ample. -/
private theorem isRelativelyAmple_add {Y X : Scheme.{0}} [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] {e : Y ⟶ X} {D₁ D₂ : RDivisor Y} (h₁ : MMP.Flips.IsRelativelyAmple e D₁)
    (h₂ : MMP.Flips.IsRelativelyAmple e D₂) : MMP.Flips.IsRelativelyAmple e (D₁ + D₂) := by
  obtain ⟨m₁, r₁, L₁, hm₁, hr₁, hL₁, rfl⟩ := h₁
  obtain ⟨m₂, r₂, L₂, hm₂, hr₂, hL₂, rfl⟩ := h₂
  refine ⟨m₁ + m₂, Fin.append r₁ r₂, Fin.append L₁ L₂, by omega, fun j => ?_, fun j => ?_, ?_⟩
  · exact Fin.addCases (motive := fun j => 0 < Fin.append r₁ r₂ j)
      (fun i => by simpa using hr₁ i) (fun i => by simpa using hr₂ i) j
  · exact Fin.addCases (motive := fun j => IsRelativelyAmpleCartier e (Fin.append L₁ L₂ j))
      (fun i => by simpa using hL₁ i) (fun i => by simpa using hL₂ i) j
  · simp [Fin.sum_univ_add]

/-- Every real Cartier combination is ample relative to an isomorphism. -/
private theorem isRelativelyAmple_of_isIso {Y X : Scheme.{0}} [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] (e : Y ⟶ X) [IsIso e] {D : RDivisor Y}
    (hD : IsCartierCombination D) : MMP.Flips.IsRelativelyAmple e D := by
  obtain ⟨m, r, L, hL, rfl⟩ := exists_presentation hD
  have h0 : MMP.Flips.IsRelativelyAmple e (0 : RDivisor Y) :=
    ⟨1, fun _ => 1, fun _ => 0, le_rfl, fun _ => one_pos,
      fun _ => isRelativelyAmpleCartier_of_isIso e Divisor.isCartier_zero, by simp⟩
  refine Finset.sum_induction _ (MMP.Flips.IsRelativelyAmple e) (fun a b ha hb =>
    isRelativelyAmple_add ha hb) h0 fun j _ => ?_
  rcases lt_trichotomy (r j) 0 with hneg | hzero | hpos
  · refine ⟨1, fun _ => -r j, fun _ => -L j, le_rfl, fun _ => neg_pos.2 hneg,
      fun _ => isRelativelyAmpleCartier_of_isIso e (hL j).neg, ?_⟩
    simp
  · rw [hzero, zero_smul]
    exact h0
  · exact ⟨1, fun _ => r j, fun _ => L j, le_rfl, fun _ => hpos,
      fun _ => isRelativelyAmpleCartier_of_isIso e (hL j), by simp⟩

/-! ### Transforms of real divisors -/

/-- Pushing prime divisors forward commutes with changing coefficients. -/
private theorem mapPrimeDivisors_mapCoeffsAddMonoidHom {X Y : Scheme.{0}} {R R' : Type*}
    [AddCommGroup R] [AddCommGroup R']
    (φ : MMP.Mori.PrimeDivisor X → Option (MMP.Mori.PrimeDivisor Y)) (g : R →+ R')
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

/-- Regarding a divisor as a real divisor commutes with the strict transform. -/
private theorem flipTransform_toRDivisor {X Y X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y)
    (D : Divisor X) :
    flipTransform f fp (Divisor.toRDivisor D) = Divisor.toRDivisor (flipTransform f fp D) := by
  simp only [Divisor.toRDivisor, flipTransform, AddMonoidHom.comp_apply,
    MMP.Mori.RationalMap.transformDivisor, inverseTransformDivisor,
    mapPrimeDivisors_mapCoeffsAddMonoidHom]

/-- The strict transform of real divisors is `ℝ`-linear. -/
private theorem flipTransform_smul {X Y X' : Scheme.{0}} (f : X ⟶ Y) (fp : X' ⟶ Y) (c : ℝ)
    (D : RDivisor X) : flipTransform f fp (c • D) = c • flipTransform f fp D := by
  simp only [flipTransform, AddMonoidHom.comp_apply, MMP.Mori.RationalMap.transformDivisor,
    inverseTransformDivisor, DivisorWithCoeffs.mapPrimeDivisors_smul]

private theorem flipTransform_logCanonicalDivisor {X Y X' : Scheme.{0}} (f : X ⟶ Y)
    (fp : X' ⟶ Y) (K : Divisor X) (D : RDivisor X) :
    flipTransform f fp (logCanonicalDivisor K D) =
      logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp D) := by
  rw [logCanonicalDivisor, logCanonicalDivisor, map_add, flipTransform_toRDivisor]

/-! ### The base of a flip sees every prime divisor of the flip -/

/-- Two birational morphisms `q : W ⟶ V`, `q' : W' ⟶ V` to a separated scheme give a modification
`q'⁻¹ ∘ q : W ⤏ W'` of `q` into `q'`. -/
private theorem exists_isModificationOf {W V W' : Scheme.{0}} [IsReduced W] [IsReduced W']
    [IsSeparated (V ↘ ⊤_ Scheme)] (q : W ⟶ V) (q' : W' ⟶ V) (hq : IsBirationalMorphism q)
    (hq' : IsBirationalMorphism q') :
    ∃ φ : W.RationalMap W', MMP.Flips.IsModificationOf q q' φ := by
  obtain ⟨em, hm⟩ := hq
  obtain ⟨ep, hp⟩ := hq'
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em q (𝟙 V) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep q' (𝟙 V) hp
  simp only [Category.comp_id] at h1 h2
  set e := em.trans ep.symm
  have H : e.IsOver q q' := h1.trans h2.symm
  refine ⟨e.toRationalMap, ⟨e, rfl⟩, ?_⟩
  rw [MMP.Flips.RationalMap.IsOver, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change W.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ q' =
    W.homOfLE (le_top : e.source ≤ ⊤) ≫ W.topIso.hom ≫ q
  rw [Category.assoc, H]
  simp

/-- If `f : X ⟶ Z` and `f⁺ : X⁺ ⟶ Z` are isomorphisms over an open `V` over which lie the points
of codimension at most one of `X` and `X⁺`, every prime divisor of `X⁺` is the transform, under
`φ = (f⁺)⁻¹ ∘ f`, of a prime divisor of `X`. -/
private theorem exists_transformPrimeDivisor_eq_some {X X' Z : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [IsSeparated (X' ↘ ⊤_ Scheme)] {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ)
    {f : X ⟶ Z} {fp : X' ⟶ Z} [IsProper f] (hf : IsBirationalMorphism f)
    (hX : IsNormalVariety ℂ (f ≫ sZ)) (hfs : Function.Surjective f)
    (hfps : Function.Surjective fp) (V : Z.Opens) [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)]
    (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hX'V : ∀ x : X', Order.coheight x ≤ 1 → fp x ∈ V) {φ : X.RationalMap X'}
    (hφ : φ.compHom fp = f.toRationalMap) (P' : MMP.Mori.PrimeDivisor X') :
    ∃ P : MMP.Mori.PrimeDivisor X, RationalMap.transformPrimeDivisor φ P = some P' := by
  classical
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI := isSeparated_toTerminal_of_isNormalVariety hZ
  haveI := hf.isDominant
  have hVf : V ≤ biregularLocus f := MMP.Mori.le_biregularLocus (f := f) ‹IsIso (f ∣_ V)›
  have hVfp : V ≤ biregularLocus fp := MMP.Mori.le_biregularLocus (f := fp) ‹IsIso (fp ∣_ V)›
  have hP'V : fp P'.genericPoint ∈ V :=
    hX'V _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P').le
  have hz : Order.coheight (fp P'.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hVfp hP'V),
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hz
  have hQ : fp P'.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hz).symm
  obtain ⟨x, hx⟩ := hfs Q.genericPoint
  have hxV : f x ∈ V := by rw [hx, ← hQ]; exact hP'V
  have hxc : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus f (hVf hxV), hx, ← hQ, hz]
  set P : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hxc
  have hPg : P.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hxc
  have hPQ : f P.genericPoint = Q.genericPoint := by rw [hPg, hx]
  have := Q.isDiscreteValuationRing_localRing
  have hcoef : ∀ D : Divisor X, flipTransform f fp D P' = D P := fun D =>
    flipTransform_apply_of_map_genericPoint hf.functionFieldMap_bijective hfps hPQ hQ
      (hQ ▸ hVfp hP'V) D
  have htr := MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZ hX hf V hXV hX'V
    hφ (Finsupp.single P (1 : ℤ))
  have h1 := hcoef (Finsupp.single P (1 : ℤ))
  rw [← htr, RationalMap.transformDivisor_single] at h1
  refine ⟨P, ?_⟩
  cases hE : RationalMap.transformPrimeDivisor φ P with
  | none =>
    rw [hE] at h1
    simp at h1
  | some E =>
    rw [hE] at h1
    simp only [Option.elim, Finsupp.single_eq_same, Finsupp.single_apply] at h1
    split_ifs at h1 with hEP
    · rw [hEP]
    · simp at h1

/-! ### Rays -/

/-- The signs on a null ray: if `a + l b = 0` and `a + (1 - s) l b < 0` with `l, s > 0`, then
`a < 0 < b`. Here `a` is the degree of `K + B`, `b` that of `H`, `K + B + l H` is null and
`K + B + (1 - s) l H` is negative. -/
private theorem neg_and_pos_of_add_mul_eq_zero {a b l s : ℝ} (hl : 0 < l) (hs : 0 < s)
    (h0 : a + l * b = 0) (h : a + (1 - s) * l * b < 0) : a < 0 ∧ 0 < b := by
  have ha : a < 0 := neg_of_mul_neg_right (by linear_combination h - (1 - s) * h0) hs.le
  exact ⟨ha, pos_of_mul_pos_right (by linarith : 0 < l * b) hl.le⟩

/-- In a ray `R = ℝ_{≥0} v`, every element is a nonnegative multiple of a nonzero element. -/
private theorem exists_eq_smul_of_mem_ray {V : Type*} [AddCommGroup V] [Module ℝ V]
    {R : Set V} {v w : V} (hR : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • v = u}) (hw : w ∈ R)
    (hw0 : w ≠ 0) {u : V} (hu : u ∈ R) : ∃ c : ℝ, 0 ≤ c ∧ u = c • w := by
  rw [hR] at hw hu
  obtain ⟨a, ha, rfl⟩ := hw
  obtain ⟨b, hb, rfl⟩ := hu
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hw0 (zero_smul ℝ v)
  refine ⟨b / a, div_nonneg hb ha, ?_⟩
  rw [smul_smul, div_mul_cancel₀ b ha0]

/-- A proper morphism from a projective variety to a normal variety is projective. -/
private theorem isProjectiveMorphism_of_isProjectiveVariety {X Z : Scheme.{0}}
    {sX : X ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} (hX : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) [IsProper f] (hf : f ≫ sZ = sX) :
    IsProjectiveMorphism f := by
  haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hX
  haveI := AlgebraicGeometry.IsProjectiveVariety.isQuasiProjectiveVariety ℂ sX
  haveI : AlgebraicGeometry.IsVariety ℂ sZ := hZ.1
  exact MMP.isProjectiveMorphism_of_isProper_of_isQuasiProjectiveVariety sX sZ f hf

/-! ### The proof -/

private theorem solution
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {B H : RDivisor X} {t₀ : ℝ}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hB0 : 0 ≤ B) (hH0 : 0 ≤ H)
    (hklt : IsRealKltPair sX (B + t₀ • H)) (ht₀ : 0 < t₀)
    (hnef₀ : IsRelativelyNef ℂ sX g (logCanonicalDivisor K (B + t₀ • H)))
    (hnef : ¬ IsRelativelyNef ℂ sX g (logCanonicalDivisor K B)) :
    ∃ t : ℝ, 0 < t ∧ t ≤ t₀ ∧ IsRelativelyNef ℂ sX g (logCanonicalDivisor K (B + t • H)) ∧
    ∃ (R : Set (RelativeNumericalCurveClasses sX g)) (Z : Scheme.{0})
      (_ : IsIntegral Z) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z)
      (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (h : Z ⟶ S),
      IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R ∧
        (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B) r L C x → x < 0) ∧
        (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            IsRIntersectionNumber ℂ sX (logCanonicalDivisor K (B + t • H)) r L C x → x = 0) ∧
        (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            IsRIntersectionNumber ℂ sX H r L C x → 0 < x) ∧
        IsRelativeContractionOfFace g R f h ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f ∧
        (IsBirationalMorphism f →
          ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X')
            (_ : IsLocallyNoetherian X') (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ))
            (fp : X' ⟶ Z),
            (((∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧
                IsIso fp ∧ fp ≫ sZ = sX') ∨
              (IsSmall ℂ sZ sX f ∧
                IsRealFlipStep sX sZ sX' K B (flipTransform f fp K) (flipTransform f fp B)
                  f fp)) ∧
              MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧
              topologicalKrullDim X' = 3 ∧
              IsRelativelyNef ℂ sX' (fp ≫ h)
                (logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp (B + t • H))) ∧
              IsRealKltPair sX' (flipTransform f fp (B + t • H))) := by
  classical
  have hXn : IsNormalVariety ℂ sX := hXQ.1
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  have hcomb : ∀ D : RDivisor X, IsCartierCombination D := isCartierCombination_of_isQFactorial hXQ
  obtain ⟨n, hKn⟩ := hK
  have hn : n = 3 := by
    have h := hKn.topologicalKrullDim_eq
    rw [hdim] at h
    exact_mod_cast (h.symm.trans (rfl : (3 : WithBot ℕ∞) = ((3 : ℕ) : WithBot ℕ∞)))
  subst hn
  /- the nef threshold -/
  have hlcd : ∀ t : ℝ, logCanonicalDivisor K (B + t • H) =
      (1 : ℝ) • logCanonicalDivisor K B + t • H := fun t => by
    simp only [logCanonicalDivisor, one_smul, add_assoc]
  have hdeg : ∀ (t : ℝ) (C : ProperCurve sX), cdeg C (logCanonicalDivisor K (B + t • H)) =
      cdeg C (logCanonicalDivisor K B) + t * cdeg C H := fun t C => by
    rw [hlcd, cdeg_add_smul C (hcomb _) (hcomb _), one_mul]
  have hnef_iff : ∀ t : ℝ, IsRelativelyNef ℂ sX g (logCanonicalDivisor K (B + t • H)) ↔
      ∀ C : ProperCurve sX, C.IsContractedBy g →
        0 ≤ cdeg C (logCanonicalDivisor K B) + t * cdeg C H := fun t => by
    rw [isRelativelyNef_iff g (hcomb _)]
    simp only [hdeg]
  obtain ⟨l, hl0, hlt₀, hlnef, hlmin⟩ :=
    exists_threshold (fun C : ProperCurve sX => C.IsContractedBy g)
      (fun C => cdeg C (logCanonicalDivisor K B)) (fun C => cdeg C H) ht₀.le
    ((hnef_iff t₀).1 hnef₀) (fun h => hnef ((isRelativelyNef_iff g (hcomb _)).2 h))
  /- lowering the boundary -/
  have hkltt : ∀ t : ℝ, 0 ≤ t → t ≤ t₀ → IsRealKltPair sX (B + t • H) := fun t ht ht' =>
    isRealKltPair_of_le sX hXQ hklt fun Q => by
      have h2 : (0 : ℝ) ≤ H Q := hH0 Q
      simp only [DivisorWithCoeffs.coeff_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      nlinarith
  have hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ B + t • H := fun t ht Q => by
    have h1 : (0 : ℝ) ≤ B Q := hB0 Q
    have h2 : (0 : ℝ) ≤ H Q := hH0 Q
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    exact add_nonneg h1 (mul_nonneg ht h2)
  set P := B + l • H with hP
  have hP0 : 0 ≤ P := hnonneg l hl0.le
  have hPklt : IsRealKltPair sX P := hkltt l hl0.le hlt₀
  have hnefP : IsRelativelyNef ℂ sX g (logCanonicalDivisor K P) := (hnef_iff l).2 hlnef
  /- rational null-decomposition data for `P` -/
  obtain ⟨sν, Bs, r, m, E, hE, hBsklt, hhull, hr, hrsum, hm, hdec, hEeq, -⟩ :=
    exists_convexCombination_isKltPair_of_isRealKltPair sX hX hXQ K hKn P hP0 hPklt
  have heq_sum : P = ∑ i, r i • QDivisor.toRDivisor (Bs i) := by
    have h := hdec
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hrsum, one_smul] at h
    exact add_left_cancel h
  have hcart : ∀ i, ∃ D : Divisor X, D.IsCartier ∧
      ∀ Q, (m : ℚ) * ((K.coeff Q : ℚ) + (Bs i).coeff Q) = D.coeff Q := fun i =>
    ⟨E i, hE i, fun Q => by
      have h := DFunLike.congr_fun (hEeq i) Q
      simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at h
      exact h.symm⟩
  let ν : RationalNullData sX K P :=
    { isQFactorial := hXQ
      isProjectiveVariety := hX
      isCanonicalDivisor := ⟨3, hKn⟩
      nonneg := fun Q => hP0 Q
      isRealKltPair := hPklt
      s := sν
      boundary := Bs
      boundary_nonneg := fun i Q => (hBsklt i).1.nonneg Q
      isKltPair_boundary := hBsklt
      mem_hull := hhull
      weight := r
      weight_pos := hr
      sum_weight := hrsum
      eq_sum := heq_sum
      m := m
      m_pos := hm
      isCartier := hcart }
  /- the radial perturbation -/
  obtain ⟨ε, hεpos, hrad⟩ := exists_pos_forall_isExtremalRay_null_and_isNegativeExtremalContraction
  have he := hεpos ν.s ν.weight ν.m
  set s : ℝ := min (ε ν.s ν.weight ν.m / 2) (1 / 2)
  have hs0 : 0 < s := lt_min (half_pos he) (by norm_num)
  have hse : s < ε ν.s ν.weight ν.m := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hBklt : IsRealKltPair sX B := by simpa using hkltt 0 le_rfl ht₀.le
  have hR := hrad sX sS g hS hg (C := B) hKn ν (fun Q => hB0 Q) hBklt hnefP s hs0 hse
  set μ : ℝ := (1 - s) * l with hμ
  have hμ0 : 0 ≤ μ := mul_nonneg (by linarith) hl0.le
  have hμl : μ < l := by rw [hμ]; nlinarith
  have hμt₀ : μ ≤ t₀ := hμl.le.trans hlt₀
  have hBs : (1 - s) • P + s • B = B + μ • H := by
    rw [hP, hμ]
    module
  have hlin_s : logCanonicalDivisor K (B + μ • H) =
      (1 - s) • logCanonicalDivisor K P + s • logCanonicalDivisor K B := by
    simp only [logCanonicalDivisor, hP, hμ]
    module
  /- the elementary step of `K + B + μ H` -/
  have hnot_s : ¬ IsRelativelyNef ℂ sX g (logCanonicalDivisor K (B + μ • H)) := fun h =>
    hlmin μ hμ0 hμl ((hnef_iff μ).1 h)
  obtain ⟨R, Z, iZ, lZ, nZ, sZ, f, h, hRext, hRneg, hcont, hZproj, hNEC, hdiv, hsmall⟩ :=
    IsRealKltPair.exists_isRelativeContractionOfFace_of_not_isRelativelyNef hX hS hg hXQ hdim
      ⟨3, hKn⟩ (hnonneg μ hμ0) (hkltt μ hμ0 hμt₀) hnot_s
  haveI := iZ
  haveI := lZ
  haveI := nZ
  have hfh : f ≫ h = g := hcont.comp_eq
  have hcontr := hNEC.isContraction
  haveI : IsProper f := hcontr.isProper
  have hfs : f ≫ sZ = sX := hcontr.comp_eq
  have hZn : IsNormalVariety ℂ sZ := hNEC.isNormalVariety_target
  have hhs : h ≫ sS = sZ :=
    eq_of_comp_eq_of_isIso_app hcontr.isIso_app (by rw [← Category.assoc, hfh, hg, hfs])
  have hρ := hNEC.relativePicardNumber_eq_one
  have hfR : ∀ C : ProperCurve sX, C.IsContractedBy f →
      ∃ hC : C.IsContractedBy g, C.relativeClass g hC ∈ R := fun C hC => by
    have hCg : C.IsContractedBy g := by rw [← hfh]; exact isContractedBy_comp h hC
    exact ⟨hCg, (hcont.isContractedBy_iff C hCg).1 hC⟩
  obtain ⟨C₀, hC₀f⟩ := exists_isContractedBy_of_relativePicardNumber_eq_one (sX := sX) hρ
  obtain ⟨hC₀g, hC₀R⟩ := hfR C₀ hC₀f
  have hDsneg : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
      cdeg C (logCanonicalDivisor K (B + μ • H)) < 0 := fun C hC hCR => by
    obtain ⟨_, _, _, hx⟩ := exists_isRIntersectionNumber_cdeg C (hcomb _)
    exact hRneg C hC hCR _ _ _ _ hx
  have hw0 : C₀.relativeClass g hC₀g ≠ 0 := fun h0 => (hDsneg C₀ hC₀g hC₀R).ne <| by
    rw [cdeg_eq_mul_of_relativeClass_eq g (hcomb _) (c := 0) (by rw [h0, zero_smul]), zero_mul]
  obtain ⟨v, -, hRv⟩ := hRext.2
  have hprop : ∀ u ∈ R, ∃ c : ℝ, 0 ≤ c ∧ u = c • C₀.relativeClass g hC₀g := fun u hu =>
    exists_eq_smul_of_mem_ray hRv hC₀R hw0 hu
  have hcurve : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ D : RDivisor X, cdeg C D = c * cdeg C₀ D := fun C hC hCR => by
    obtain ⟨c, hc, hCc⟩ := hprop _ hCR
    exact ⟨c, hc, fun D => cdeg_eq_mul_of_relativeClass_eq g (hcomb D) hCc⟩
  /- the ray is `D`-null -/
  have hnull₀ : cdeg C₀ (logCanonicalDivisor K P) = 0 := by
    obtain ⟨n₁, c₁, L₁, hL₁, hD₁⟩ := exists_presentation (hcomb (logCanonicalDivisor K (B + μ • H)))
    obtain ⟨n₂, c₂, L₂, hL₂, hD₂⟩ := exists_presentation (hcomb (logCanonicalDivisor K P))
    have h1 := hR.1 R hRext ⟨n₁, c₁, L₁, hL₁, by rwa [hBs], fun u hu hu0 => by
      obtain ⟨c, hc, rfl⟩ := hprop u hu
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hu0 (zero_smul ℝ _)
      rw [sum_relDegree_smul_relativeClass g hL₁ hD₁ C₀ hC₀g c]
      exact mul_neg_of_pos_of_neg (hc.lt_of_ne' hc0) (hDsneg C₀ hC₀g hC₀R)⟩
      n₂ c₂ L₂ hL₂ hD₂ _ hC₀R
    rwa [sum_relDegree_relativeClass g hL₂ hD₂ C₀ hC₀g] at h1
  have hsigns : ∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
      cdeg C (logCanonicalDivisor K B) < 0 ∧ 0 < cdeg C H := fun C hC hCR => by
    obtain ⟨c, -, hCD⟩ := hcurve C hC hCR
    refine neg_and_pos_of_add_mul_eq_zero hl0 hs0 ?_ ?_
    · rw [← hdeg, ← hP, hCD, hnull₀, mul_zero]
    · rw [← hμ, ← hdeg]
      exact hDsneg C hC hCR
  /- the contraction is `(K + B)`-negative -/
  have hfproj := isProjectiveMorphism_of_isProjectiveVariety hX hZn f hfs
  have hNEC_KB : IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f :=
    { isNormalVariety_source := hNEC.isNormalVariety_source
      isNormalVariety_target := hZn
      isCartierCombination := hcomb _
      isContraction := hcontr
      isRelativelyAntiAmple := isRelativelyAmple_of_forall_pos hXn hZn hfproj.isProjective hfs hρ
        (hcomb _) fun C hC => by
          obtain ⟨hCg, hCR⟩ := hfR C hC
          have h1 := (hsigns C hCg hCR).1
          have e : -logCanonicalDivisor K B =
              (-1 : ℝ) • logCanonicalDivisor K B + (0 : ℝ) • logCanonicalDivisor K B := by simp
          rw [e, cdeg_add_smul C (hcomb _) (hcomb _)]
          linarith
      relativePicardNumber_eq_one := hρ }
  refine ⟨l, hl0, hlt₀, hnefP, R, Z, iZ, lZ, nZ, sZ, f, h, hRext, ?_, ?_, ?_, hcont, hZproj,
    hNEC_KB, ?_⟩
  · intro C hC hCR m₁ r₁ L₁ x hx
    rw [eq_cdeg hx]
    exact (hsigns C hC hCR).1
  · intro C hC hCR m₁ r₁ L₁ x hx
    rw [eq_cdeg hx]
    obtain ⟨c, -, hCD⟩ := hcurve C hC hCR
    rw [hCD, hnull₀, mul_zero]
  · intro C hC hCR m₁ r₁ L₁ x hx
    rw [eq_cdeg hx]
    exact (hsigns C hC hCR).2
  /- the elementary step -/
  intro hbir
  have hBC : IsBirationalContraction ℂ sZ sX f :=
    { toIsContraction := hcontr
      dim_eq := (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hbir).symm }
  have hNEC' : IsNegativeExtremalContraction ℂ sX sZ
      (logCanonicalDivisor K ((1 - s) • P + s • B)) f := by
    rwa [hBs]
  by_cases hsm : IsSmall ℂ sZ sX f
  · /- the small case: the flip of `K + B + μ H` is a `(K + B)`-flip -/
    obtain ⟨X', iX', cX', lX', nX', sX', K', fp, hstep, hX'proj, hX'Q, hX'dim, -⟩ := hsmall hsm
    haveI := iX'
    haveI := cX'
    haveI := lX'
    haveI := nX'
    have hX'n : IsNormalVariety ℂ sX' := hX'Q.1
    haveI : QuasiCompact sX' := hX'n.1.toQuasiCompact
    have hcomb' : ∀ D : RDivisor X', IsCartierCombination D :=
      isCartierCombination_of_isQFactorial hX'Q
    have hfps : fp ≫ sZ = sX' := hstep.isSmall_flip.comp_eq
    haveI : IsProper fp := hstep.isSmall_flip.isProper
    obtain ⟨V, hVf, hVfp, hXV, hX'V⟩ :=
      MMP.Mori.exists_opens_isIso_of_isSmall hsm hstep.isSmall_flip
    haveI := hVf
    haveI := hVfp
    have hK'' : Divisor.IsCanonicalDivisor sX' 3 (flipTransform f fp K) := by
      have := MMP.Mori.isCanonicalDivisor_flipTransform_of_isIso_restrict hZn (f := f) (fp := fp)
        (by rwa [hfs]) (by rwa [hfps]) hbir hstep.isBirationalMorphism_flip
        V hXV hX'V (n := 3) (K := K) (by rwa [hfs])
      rwa [hfps] at this
    obtain ⟨mK, hK'c⟩ := hstep.isCanonicalDivisor_flip
    have hlinK : Divisor.LinearlyEquivalent (flipTransform f fp K) K' :=
      MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor sX' hX'n hK'' hK'c
    have hfpproj : IsProjective fp := hstep.isProjectiveMorphism_flip.isProjective
    have hρ' := hstep.relativePicardNumber_flip
    have hamp_s : MMP.Flips.IsRelativelyAmple fp (logCanonicalDivisor (flipTransform f fp K)
        (flipTransform f fp (B + μ • H))) :=
      isRelativelyAmple_of_forall_pos hX'n hZn hfpproj hfps hρ' (hcomb' _) fun C hC => by
        rw [cdeg_logCanonicalDivisor_congr hX'Q C hlinK]
        exact cdeg_pos_of_isRelativelyAmple hstep.isRelativelyAmple_flip C hC
    have hamp' : MMP.Flips.IsRelativelyAmple fp (logCanonicalDivisor (flipTransform f fp K)
        (flipTransform f fp ((1 - s) • P + s • B))) := by
      rwa [hBs]
    obtain ⟨-, hnef', ⟨ν', -⟩, -, -⟩ := hR.2 sZ sX' f h fp hfh hhs hNEC' hbir hfproj hZproj hX'Q
      hX'proj hK'' hstep.isSmall_flip hstep.isProjectiveMorphism_flip hamp'
    /- `D` stays trivial over the base of the flip -/
    have hGtriv : IsNumericallyTrivialOver ℂ sX f (logCanonicalDivisor K P) := by
      unfold IsNumericallyTrivialOver IsNumericallyEquivalentOver
      refine ⟨hcomb _, hcomb 0, fun C hC m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂ => ?_⟩
      obtain ⟨hCg, hCR⟩ := hfR C hC
      obtain ⟨c, -, hCD⟩ := hcurve C hCg hCR
      rw [eq_cdeg h₁, eq_cdeg h₂, hCD, hnull₀, mul_zero, cdeg_zero]
    haveI : IsSeparated (Z ↘ ⊤_ Scheme) := isSeparated_toTerminal_of_isNormalVariety hZn
    haveI : IsSeparated (X' ↘ ⊤_ Scheme) := isSeparated_toTerminal_of_isNormalVariety hX'n
    obtain ⟨ψ, -, hψ⟩ := exists_isModificationOf f fp hbir hstep.isBirationalMorphism_flip
    have hψP := exists_transformPrimeDivisor_eq_some hZn hbir (by rwa [hfs])
      (Scheme.Hom.surjective_of_isIso_app f hcontr.isIso_app).surj
      (Scheme.Hom.surjective_of_isIso_app fp hstep.isSmall_flip.isIso_app).surj V hXV hX'V hψ
    obtain ⟨-, htriv'⟩ := IsNumericallyTrivialOver.transformDivisor_of_isOver sZ hXn hX'Q hfs hfps
      hbir hstep.isBirationalMorphism_flip hψ hψP (hcomb _) hGtriv
    rw [MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZn (by rwa [hfs])
      hbir V hXV hX'V hψ, flipTransform_logCanonicalDivisor] at htriv'
    have hrelX' : logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp (B + μ • H)) =
        (1 - s) • logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp P) +
          s • logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B) := by
      have := congrArg (fun D => flipTransform f fp D) hlin_s
      simp only [map_add, flipTransform_smul, flipTransform_logCanonicalDivisor] at this
      rwa [map_add, flipTransform_smul]
    have hampKB : MMP.Flips.IsRelativelyAmple fp
        (logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp B)) :=
      isRelativelyAmple_of_forall_pos hX'n hZn hfpproj hfps hρ' (hcomb' _) fun C hC => by
        have h1 := cdeg_pos_of_isRelativelyAmple hamp_s C hC
        have h0 : cdeg C (logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp P)) =
            0 := by
          obtain ⟨-, -, htr⟩ := htriv'
          obtain ⟨m₁, r₁, L₁, hx⟩ := exists_isRIntersectionNumber_cdeg C (hcomb' _)
          exact htr C hC m₁ r₁ L₁ _ 0 Fin.elim0 Fin.elim0 0 hx (isRIntersectionNumber_zero C)
        rw [hrelX', cdeg_add_smul C (hcomb' _) (hcomb' _), h0, mul_zero, zero_add] at h1
        exact pos_of_mul_pos_right h1 hs0.le
    have hflipKB : IsRealFlipStep sX sZ sX' K B (flipTransform f fp K) (flipTransform f fp B)
        f fp :=
      { isQuasiProjectiveVariety_target := hstep.isQuasiProjectiveVariety_target
        isNegativeExtremalContraction := hNEC_KB
        isSmall := hstep.isSmall
        isBirationalMorphism := hstep.isBirationalMorphism
        isProjectiveMorphism := hstep.isProjectiveMorphism
        not_isIso := hstep.not_isIso
        isCanonicalDivisor_flip := ⟨3, hK''⟩
        isSmall_flip := hstep.isSmall_flip
        isBirationalMorphism_flip := hstep.isBirationalMorphism_flip
        isProjectiveMorphism_flip := hstep.isProjectiveMorphism_flip
        not_isIso_flip := hstep.not_isIso_flip
        relativePicardNumber_flip := hstep.relativePicardNumber_flip
        isRelativelyAmple_flip := hampKB
        eq_flipTransform := rfl }
    exact ⟨X', iX', cX', lX', nX', sX', fp, Or.inr ⟨hsm, hflipKB⟩, hX'proj, hX'Q, hX'dim, hnef',
      ν'.isRealKltPair⟩
  · /- the divisorial case: the next model is the base `Z` -/
    obtain ⟨F, hF⟩ :=
      exists_primeDivisor_exceptionalSet_eq_support_of_not_isSmall sX sZ hXQ hZn f hBC hfproj hρ hsm
    have hEM : (MMP.Mori.exceptionalSet f : Set X) = F.support := by
      rw [coe_exceptionalSet_eq hZn hXn.1 f hfs hbir, hF]
    obtain ⟨hZQ, -⟩ := hdiv ⟨hbir, F, hEM⟩
    haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
    haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
    have hcombZ : ∀ D : RDivisor Z, IsCartierCombination D :=
      isCartierCombination_of_isQFactorial hZQ
    have hdimZ : topologicalKrullDim Z = 3 :=
      (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ sX hbir).trans hdim
    have hKZ : Divisor.IsCanonicalDivisor sZ 3 (flipTransform f (𝟙 Z) K) := by
      obtain ⟨KZ, hKZ⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety sZ hZn (n := 3)
        (by rw [hdimZ]; norm_cast)
      haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
      haveI : LocallyOfFiniteType (f ≫ sZ) := by rw [hfs]; exact hXn.1.toLocallyOfFiniteType
      haveI := hbir.isDominant
      rw [flipTransform_id]
      exact MMP.Fourfold.Oai4C1.Main.isCanonicalDivisor_transformDivisor hZn
        (by rwa [hfs]) hbir hKZ (by rwa [hfs])
    have hamp_id : MMP.Flips.IsRelativelyAmple (𝟙 Z) (logCanonicalDivisor (flipTransform f (𝟙 Z) K)
        (flipTransform f (𝟙 Z) ((1 - s) • P + s • B))) :=
      isRelativelyAmple_of_isIso (𝟙 Z) (hcombZ _)
    obtain ⟨-, hnef', ⟨ν', -⟩, -, -⟩ := hR.2 sZ sZ f h (𝟙 Z) hfh hhs hNEC' hbir hfproj hZproj hZQ
      hZproj hKZ (isSmall_id hZn)
      (isProjectiveMorphism_of_isProjectiveVariety hZproj hZn (𝟙 Z) (Category.id_comp _)) hamp_id
    exact ⟨Z, iZ, inferInstance, lZ, nZ, sZ, 𝟙 Z, Or.inl ⟨⟨F, hEM⟩, inferInstance,
      Category.id_comp _⟩, hZproj, hZQ, hdimZ, hnef', ν'.isRealKltPair⟩

end Proof_lem_fourfold_real_nef_threshold_ray

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori MMP.Flips

/-- **A nef threshold gives a null negative ray.** Let `g : X ⟶ S` be a morphism of projective
complex varieties, `X` a normal `ℚ`-factorial threefold with canonical divisor `K`, `B, H ≥ 0` real
divisors and `t₀ > 0` with `(X, B + t₀ H)` klt and `K + B + t₀ H` `g`-nef, but `K + B` not
`g`-nef. Then there are `0 < t ≤ t₀` with `K + B + t H` `g`-nef and an extremal ray `R` of
`NE̅(X/S)` with `(K + B) · R < 0`, `(K + B + t H) · R = 0`, `H · R > 0`, together with its
contraction `f : X ⟶ Z`, `h : Z ⟶ S` over `S`, `-(K + B)` `f`-ample with `ρ(X/Z) = 1`. If `f` is
birational there is the elementary real step `X ⟶ Z ⟵ X'`, `X'` a projective `ℚ`-factorial
threefold: either `f` is divisorial, `fp` an isomorphism, or `fp` is the real `(K + B)`-flip of
`f`. On `X'` the transform of `K + B + t H` is nef over `S` and `(X', fp⁻¹_* f_* (B + t H))` is
klt. -/
@[mmp "lem_fourfold_real_nef_threshold_ray"]
public theorem IsRealKltPair.exists_isExtremalRay_of_isRelativelyNef_add_smul
    {X S : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    {sX : X ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : X ⟶ S} {K : Divisor X}
    {B H : RDivisor X} {t₀ : ℝ}
    (hX : MMP.Mori.IsProjectiveVariety ℂ sX) (hS : MMP.Mori.IsProjectiveVariety ℂ sS)
    (hg : g ≫ sS = sX) (hXQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 3)
    (hK : ∃ n : ℕ, K.IsCanonicalDivisor sX n) (hB0 : 0 ≤ B) (hH0 : 0 ≤ H)
    (hklt : IsRealKltPair sX (B + t₀ • H)) (ht₀ : 0 < t₀)
    (hnef₀ : IsRelativelyNef ℂ sX g (logCanonicalDivisor K (B + t₀ • H)))
    (hnef : ¬ IsRelativelyNef ℂ sX g (logCanonicalDivisor K B)) :
    ∃ t : ℝ, 0 < t ∧ t ≤ t₀ ∧ IsRelativelyNef ℂ sX g (logCanonicalDivisor K (B + t • H)) ∧
    ∃ (R : Set (RelativeNumericalCurveClasses sX g)) (Z : Scheme.{0})
      (_ : IsIntegral Z) (_ : IsLocallyNoetherian Z) (_ : IsNormal Z)
      (sZ : Z ⟶ Spec (.of ℂ)) (f : X ⟶ Z) (h : Z ⟶ S),
      IsExtremalRay ℝ
          (relativeClosedConeOfCurves sX g : Set (RelativeNumericalCurveClasses sX g)) R ∧
        (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B) r L C x → x < 0) ∧
        (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            IsRIntersectionNumber ℂ sX (logCanonicalDivisor K (B + t • H)) r L C x → x = 0) ∧
        (∀ (C : ProperCurve sX) (hC : C.IsContractedBy g), C.relativeClass g hC ∈ R →
          ∀ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
            IsRIntersectionNumber ℂ sX H r L C x → 0 < x) ∧
        IsRelativeContractionOfFace g R f h ∧
        MMP.Mori.IsProjectiveVariety ℂ sZ ∧
        IsNegativeExtremalContraction ℂ sX sZ (logCanonicalDivisor K B) f ∧
        (IsBirationalMorphism f →
          ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (_ : CompactSpace X')
            (_ : IsLocallyNoetherian X') (_ : IsNormal X') (sX' : X' ⟶ Spec (.of ℂ))
            (fp : X' ⟶ Z),
            (((∃ E : MMP.Mori.PrimeDivisor X, (MMP.Mori.exceptionalSet f : Set X) = E.support) ∧
                IsIso fp ∧ fp ≫ sZ = sX') ∨
              (IsSmall ℂ sZ sX f ∧
                IsRealFlipStep sX sZ sX' K B (flipTransform f fp K) (flipTransform f fp B)
                  f fp)) ∧
              MMP.Mori.IsProjectiveVariety ℂ sX' ∧ IsQFactorial sX' ∧
              topologicalKrullDim X' = 3 ∧
              IsRelativelyNef ℂ sX' (fp ≫ h)
                (logCanonicalDivisor (flipTransform f fp K) (flipTransform f fp (B + t • H))) ∧
              IsRealKltPair sX' (flipTransform f fp (B + t • H))) :=
  Proof_lem_fourfold_real_nef_threshold_ray.solution hX hS hg hXQ hdim hK hB0 hH0 hklt ht₀
    hnef₀ hnef

end MMP.Fourfold
