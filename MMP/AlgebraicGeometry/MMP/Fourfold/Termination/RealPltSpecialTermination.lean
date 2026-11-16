module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.WeakModel
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
import MMP.AlgebraicGeometry.MMP.Fourfold.Termination.PltStratumScalingBlock
import MMP.AlgebraicGeometry.Singularities.RealKltExtraction
import MMP.AlgebraicGeometry.Singularities.RealPltAdjunction
import MMP.AlgebraicGeometry.MMP.Termination.PltFlipStratumStabilization
import MMP.AlgebraicGeometry.MMP.Threefold.Termination.RealKltBigScaling
public import Mathlib.AlgebraicGeometry.Scheme
import MMP.AlgebraicGeometry.MMP.MinimalModel.RealKltCompactification
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Intersection.NumericallyTrivialTransform
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import MMP.AlgebraicGeometry.MMP.Flip.ReducedPartRemoval
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantJunction
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Valuation
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.MMP.Flip.FlipLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.Basic
import MMP.Analysis.Complex.CauchyTransformRungeMontel
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.Curves.PluricanonicalSectionsSeparatePoints
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Geometrically.AlgClosedBaseChange.TopForms
import MMP.AlgebraicGeometry.Resolution.SNCWeight.Subtraction
import MMP.AlgebraicGeometry.MMP.MinimalModel.NefWeakModelStep
import MMP.AlgebraicGeometry.MMP.MinimalModel.LcModelNoExtractedDivisor
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueLift
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Positivity.BigBirationalTransform
import MMP.AlgebraicGeometry.Divisor.SectionAlgebra.Cartier
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.LinEquiv
import MMP.AlgebraicGeometry.Vanishing.CoveringTrick
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipBoundaryTransform
import MMP.AlgebraicGeometry.Intersection.ChowVarietyFixedDegree
import MMP.AlgebraicGeometry.MMP.Fourfold.FixedParts
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.Singularities.Adjunction.CyclicQuotientDifferent
import MMP.AlgebraicGeometry.MMP.Threefold.Flip.FloorProgramInputs
import MMP.AlgebraicGeometry.SpreadingOut.CanonicalDivisor
import MMP.AlgebraicGeometry.Positivity.RelativeBigDecomposition
import MMP.AlgebraicGeometry.Positivity.RelativeNefBigSurface
import MMP.AlgebraicGeometry.Positivity.RelativeAmplePullbackTwist
import MMP.AlgebraicGeometry.MMP.Fourfold.Conductor.DualityAntiampleFibre
import MMP.AlgebraicGeometry.Positivity.RelativelyAmple
import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
import MMP.AlgebraicGeometry.SpreadingOut.CartesianFibres
import MMP.AlgebraicGeometry.MMP.MinimalModel.PltReference
import MMP.AlgebraicGeometry.Singularities.Adjunction.ResidueDifferent

/-!
# Special termination for real plt fourfold flips with scaling

Let `X_i ⟶ Z_i ⟵ X_{i+1}` be an infinite sequence of real flips of globally projective
`ℚ`-factorial complex fourfolds `(X_i, B_i)` over a projective variety `Z`, each pair plt, run
with scaling of effective divisors `C_i` (`C_{i+1}` the strict transform of `C_i`) and positive
nonincreasing thresholds `λ_i`: the upper adjoint `K_{X_i} + B_i + λ_i C_i` is nef over `Z`, the
upper pair `(X_i, B_i + λ_i C_i)` is plt, and the upper adjoint is the pull-back of one
`ℝ`-Cartier divisor on `Z_i` to both `X_i` and `X_{i+1}`. Let `S_i` be a retained component of
`⌊B_i⌋` not contained in `Supp C_i`. Suppose that the `S_i` come from a normal prime divisor
`S⁰` of a normal projective reference variety `X⁰` with an effective ample `ℚ`-divisor `A⁰` not
containing `S⁰`, through birational maps `ψ_i : X⁰ ⤏ X_i` sending `S⁰` to `S_i`, whose extracted
primes have their generic points mapped outside `Supp A⁰`, and that `B_i - S_i ≥ (ψ_i)_* A⁰`.
Then for all large `i` the flipping locus of `f_i` is disjoint from `S_i` (and the flipped locus
of `f_i⁺` from `S_{i+1}`).

## Main results

* `MMP.Fourfold.eventually_disjoint_exceptionalSet_of_realPltFlip_scaling`.

## Implementation notes

* A real plt pair `(X, B)` is a normal variety with an `ℝ`-divisor `B` whose coefficients lie in
  `[0, 1]`, `K_X + B` `ℝ`-Cartier, and `a(E; X, B) > 0` for every exceptional divisor `E`
  over `X`.
* "The adjoint descends crepantly through its step" is the existence of an `ℝ`-Cartier divisor
  `D_i` on `Z_i` whose pull-backs (`MMP.Flips.IsRCartierPullback`) along `f_i` and `f_i⁺` are
  `K_{X_i} + B_i + λ_i C_i` and `K_{X_{i+1}} + B_{i+1} + λ_i C_{i+1}`. It makes the upper adjoint
  numerically trivial over `Z_i`; together with nefness over `Z` and the
  `(K_{X_i} + B_i)`-negativity of `f_i`, `λ_i` is then the nef threshold of `C_i`.
* An extracted prime of `ψ_i` is a `ψ_i⁻¹`-exceptional prime divisor `F` of `X_i`
  (`MMP.Flips.RationalMap.IsInverseExceptional`); its valuation has order zero on `A⁰` when the
  inverse map sends the generic point of `F` outside `Supp A⁰`.
* The flipping locus of `f_i` is its exceptional set `MMP.Mori.exceptionalSet`.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 7.4
-/

@[expose] public section

section

open CategoryTheory AlgebraicGeometry

namespace Proof_thm_fourfold_real_plt_special_termination_scaling

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Fourfold MMP.Mori

/-- Every proper curve has a normalization, of dimension at most one. -/
private theorem exists_isCurveNormalization {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (C : ProperCurve sX) :
    ∃ (N : Scheme.{0}) (ν : N ⟶ C.scheme) (_ : MMP.Flips.IsCurveNormalization ν),
      topologicalKrullDim N ≤ 1 := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve ℂ p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType ℂ p
  haveI hvar : AlgebraicGeometry.IsVariety ℂ (normalizationOverField ℂ p ≫ p) :=
    isVariety_normalizationOverField ℂ p
  haveI : IsIntegral (normalizationSchemeOverField ℂ p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField ℂ p) := isFinite_normalizationOverField ℂ p
  have hν : MMP.Flips.IsCurveNormalization (normalizationOverField ℂ p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField ℂ p)) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField ℂ p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact MMP.Flips.isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  exact ⟨_, _, hν, (topologicalKrullDim_normalizationSchemeOverField ℂ p).le.trans C.dim_le⟩

/-- `L · C` is the degree of `𝒪_X(L)` along `C`. -/
private theorem isCartierIntersectionNumber_degreeOn {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    MMP.Flips.IsCartierIntersectionNumber ℂ sX C L hL (L.degreeOn ℂ sX C.ι C.dim_le hL) := by
  obtain ⟨N, ν, hν, hdim⟩ := exists_isCurveNormalization C
  refine ⟨N, ν, hν, hdim, ?_⟩
  have := hν.isFinite
  haveI : IsProper ((ν ≫ C.ι) ≫ sX) := by rw [Category.assoc]; infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (MMP.Fourfold.Oai4C1.Negativity.degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)` for a presentation `D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn {X : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    MMP.Flips.IsRIntersectionNumber ℂ sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn ℂ sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn ℂ sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn sX C (L j) (hL j), rfl⟩

/-- Every `ℝ`-Cartier divisor has an `ℝ`-Cartier class whose pairing with each proper curve is
its intersection number, computed with any presentation. -/
private theorem exists_kCartierDivisor_isRIntersectionNumber
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] {D : RDivisor X}
    (hD : MMP.Flips.IsCartierCombination D) :
    ∃ δ : KCartierDivisor ℝ X,
      (∀ γ : ProperCurve sX, ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
        MMP.Flips.IsRIntersectionNumber ℂ sX D r L γ ((γ.cycle ℝ).intersectionNumber δ)) ∧
      ∀ (γ : ProperCurve sX) (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
        MMP.Flips.IsRIntersectionNumber ℂ sX D r L γ x → x = (γ.cycle ℝ).intersectionNumber δ := by
  obtain ⟨m, r, L, hL, hDe⟩ := hD
  have hDe' : D = ∑ j, r j • Divisor.toRDivisor (L j) := by
    simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]; exact hDe
  choose E hE using fun j => MMP.Flips.exists_cartierDivisor_degree_eq sX (L j) (hL j)
  have hval : ∀ γ : ProperCurve sX, (γ.cycle ℝ).intersectionNumber
        (∑ j, r j • KCartierDivisor.ofCartier ℝ (E j)) =
          ∑ j, r j * ((L j).degreeOn ℂ sX γ.ι γ.dim_le (hL j) : ℝ) := by
      intro γ
      simp only [OneCycle.intersectionNumber, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hE ⊢
      exact Finset.sum_congr rfl fun j _ => by rw [hE j γ]
  have hex : ∀ γ : ProperCurve sX, MMP.Flips.IsRIntersectionNumber ℂ sX D r L γ
      ((γ.cycle ℝ).intersectionNumber (∑ j, r j • KCartierDivisor.ofCartier ℝ (E j))) := by
    intro γ
    rw [hval, hDe']
    exact isRIntersectionNumber_sum_degreeOn sX γ r L hL
  refine ⟨∑ j, r j • KCartierDivisor.ofCartier ℝ (E j), fun γ => ⟨m, r, L, hex γ⟩, ?_⟩
  intro γ m' r' L' x hx
  exact (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX γ).1 D r' L' r L x _ hx (hex γ)

private theorem isCartierCombination_of_isQFactorial {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} (hX : IsQFactorial sX)
    (D : RDivisor X) : MMP.Flips.IsCartierCombination D := by
  obtain ⟨m, r, C, hC, hD⟩ := MMP.Fourfold.IsQFactorial.isRCartier hX D
  refine ⟨m, r, C, hC, ?_⟩
  ext Γ
  rw [hD Γ]
  simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
    smul_eq_mul]
  rfl

private theorem coe_supp_single_one {X : Scheme.{0}} (S : MMP.Mori.PrimeDivisor X) :
    (DivisorWithCoeffs.supp (Finsupp.single S (1 : ℝ) : RDivisor X) : Set X) = (S.support : Set X) := by
  rw [DivisorWithCoeffs.coe_supp, Finsupp.support_single_ne_zero _ one_ne_zero]
  simp

private theorem isRIntersectionNumber_zero_divisor {X : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (γ : ProperCurve sX) :
    MMP.Flips.IsRIntersectionNumber ℂ sX (0 : RDivisor X) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → Divisor X) γ 0 :=
  ⟨fun j => j.elim0, Fin.elim0, by simp, fun j => j.elim0, by simp⟩

/-- An `ℝ`-Cartier divisor positive on a curve has its negative negative on it, for every
presentation of the negative. -/
private theorem neg_of_isRIntersectionNumber_neg {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX]
    {D : RDivisor X} (hD : MMP.Flips.IsCartierCombination D) (γ : ProperCurve sX) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : MMP.Flips.IsRIntersectionNumber ℂ sX (-D) r L γ x) :
    ∃ (m' : ℕ) (r' : Fin m' → ℝ) (L' : Fin m' → Divisor X) (y : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sX D r' L' γ y ∧ x = -y := by
  obtain ⟨δ, hex, -⟩ := exists_kCartierDivisor_isRIntersectionNumber sX hD
  obtain ⟨m', r', L', hy⟩ := hex γ
  obtain ⟨heq, hlin⟩ := MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX γ
  have hl := hlin _ _ _ _ _ _ _ _ (-1) 0 hy hy
  rw [show (-1 : ℝ) • D + (0 : ℝ) • D = -D by simp] at hl
  refine ⟨m', r', L', _, hy, ?_⟩
  rw [heq _ _ _ _ _ _ _ hx hl]
  ring

/-- An `ℝ`-Cartier pull-back along `f` has intersection number zero with every proper curve
contracted by `f`, for a suitable presentation. -/
private theorem isRIntersectionNumber_zero_of_isRCartierPullback
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) {D : RDivisor Z} {G : RDivisor X} (hD : MMP.Flips.IsRCartierPullback f D G)
    (γ : ProperCurve sX) (hγ : γ.IsContractedBy f) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X),
      MMP.Flips.IsRIntersectionNumber ℂ sX G r L γ 0 := by
  haveI : QuasiCompact sX := by rw [← hf]; haveI := hZ.1.toQuasiCompact; infer_instance
  haveI : IsSeparated sZ := hZ.1.toIsSeparated
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : QuasiCompact sZ := hZ.1.toQuasiCompact
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  obtain ⟨m, r, L, L', hLc, -, hpb, hG⟩ := hD
  choose hB hpb using hpb
  have hL'c : ∀ j, (L' j).IsCartier := fun j => by
    rw [← (hpb j).pullback_eq (hLc j)]; exact (hLc j).isCartier_pullback f (hB j)
  refine ⟨m, r, L', ?_⟩
  have h := isRIntersectionNumber_sum_degreeOn sX γ r L' hL'c
  rw [← hG] at h
  convert h using 1
  symm
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 := Divisor.degreeOn_pullback_eq_zero_of_isContractedBy f hf (hLc j) (hB j) γ hγ
  have he : (L j).pullback (hLc j) (hB j) = L' j := (hpb j).pullback_eq (hLc j)
  have key : ∀ (E : Divisor X) (hE : E.IsCartier), E = L' j →
      E.degreeOn ℂ sX γ.ι γ.dim_le hE = 0 →
        (L' j).degreeOn ℂ sX γ.ι γ.dim_le (hL'c j) = 0 := by
    rintro E hE rfl h; exact h
  rw [key _ _ he h0]; simp

/-- An `f`-ample `ℝ`-divisor has positive intersection number with every proper curve contracted
by `f`, for a suitable presentation. -/
private theorem exists_isRIntersectionNumber_pos_of_isRelativelyAmple
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [QuasiCompact sX] (f : X ⟶ Z) {A : RDivisor X}
    (hA : MMP.Flips.IsRelativelyAmple f A) (γ : ProperCurve sX) (hγ : γ.IsContractedBy f) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor X) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sX A r L γ x ∧ 0 < x := by
  obtain ⟨m, r, L, hm, hr, hL, hA⟩ := hA
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  refine ⟨m, r, L, _, hA ▸ isRIntersectionNumber_sum_degreeOn sX γ r L hLc, ?_⟩
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine Finset.sum_pos (fun j _ => mul_pos (hr j) ?_) Finset.univ_nonempty
  exact_mod_cast MMP.Flips.degreeOn_pos_of_isRelativelyAmpleCartier f (hL j) (hLc j) γ hγ

/-- **The scaling divisor is positive on the flipping ray.** If `K + B + λC` (`λ > 0`) is the
pull-back of an `ℝ`-Cartier divisor along `f` and `-(K + B)` is `f`-ample, then `C` is positive on
every proper curve contracted by `f`. -/
private theorem pos_of_isRCartierPullback_of_isRelativelyAntiAmple
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX)
    (K : Divisor X) (B C : RDivisor X) (lam : ℝ) (hlam : 0 < lam) (D : RDivisor Z)
    (hD : MMP.Flips.IsRCartierPullback f D (MMP.Flips.logCanonicalDivisor K (B + lam • C)))
    (hneg : MMP.Flips.IsRelativelyAntiAmple f (MMP.Flips.logCanonicalDivisor K B))
    (γ : ProperCurve sX) (hγ : γ.IsContractedBy f) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) {x : ℝ} (hx : MMP.Flips.IsRIntersectionNumber ℂ sX C r L γ x) :
    0 < x := by
  haveI : QuasiCompact sX := by rw [← hf]; haveI := hZ.1.toQuasiCompact; infer_instance
  obtain ⟨m₁, r₁, L₁, h₁⟩ := isRIntersectionNumber_zero_of_isRCartierPullback sX sZ hZ f hf hD γ hγ
  obtain ⟨m₂, r₂, L₂, p, h₂, hp⟩ :=
    exists_isRIntersectionNumber_pos_of_isRelativelyAmple sX f hneg γ hγ
  obtain ⟨heq, hlin⟩ := MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX γ
  have hU := hlin _ _ _ _ _ _ _ _ 1 1 h₁ h₂
  have hC := hlin _ _ _ _ _ _ _ _ lam 0 hx hx
  have hdiv : (1 : ℝ) • MMP.Flips.logCanonicalDivisor K (B + lam • C) +
      (1 : ℝ) • (-MMP.Flips.logCanonicalDivisor K B) = lam • C + (0 : ℝ) • C := by
    simp only [MMP.Flips.logCanonicalDivisor, one_smul, zero_smul, add_zero]
    abel
  rw [hdiv] at hU
  have := heq _ _ _ _ _ _ _ hU hC
  nlinarith

/-- **A point of the exceptional locus on a closed set without contracted curves.** Let
`f : X ⟶ Z` be a proper birational morphism of normal complex varieties and `W ⊆ X` a closed set
containing no proper curve contracted by `f`. If `W` meets `Ex(f)`, then some proper curve
contracted by `f` meets `W` without lying in it. -/
private theorem exists_properCurve_isContractedBy_of_mem_exceptionalSet
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX] (sZ : Z ⟶ Spec (.of ℂ)) (hX : IsNormalVariety ℂ sX)
    (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX) [IsProper f]
    (hfb : IsBirationalMorphism f) {W : Set X} (hW : IsClosed W)
    (hWc : ∀ γ : ProperCurve sX, closure {γ.point} ⊆ W → ¬ γ.IsContractedBy f)
    (hmeet : ((MMP.Mori.exceptionalSet f : Set X) ∩ W).Nonempty) :
    ∃ γ : ProperCurve sX, γ.IsContractedBy f ∧ ¬ closure {γ.point} ⊆ W ∧
      (closure {γ.point} ∩ W).Nonempty := by
  haveI : IsNoetherian X := ⟨⟩
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  -- a closed point `x` of `Ex(f) ∩ W`
  obtain ⟨x, ⟨hxE, hxW⟩, hxc⟩ :=
    ((MMP.Mori.isClosed_exceptionalSet f).inter hW).exists_closed_singleton hmeet
  set F : Set X := f.base ⁻¹' {f x} with hFdef
  have hyc : IsClosed ({f x} : Set Z) := by
    simpa [Set.image_singleton] using f.isClosedMap _ hxc
  have hF : IsClosed F := hyc.preimage f.continuous
  have hxF : x ∈ F := rfl
  -- a curve through a specialization `η ⤳ p` inside `F`, `p` closed, `η ∉ Z₀` for a closed
  -- `Z₀ ∋ p`
  have curve : ∀ {η p : X} {Z₀ : Set X}, η ∈ F → η ⤳ p → IsClosed ({p} : Set X) →
      IsClosed Z₀ → p ∈ Z₀ → η ∉ Z₀ →
      ∃ γ : ProperCurve sX, γ.IsContractedBy f ∧ closure {γ.point} ⊆ F ∧ γ.point ∉ Z₀ ∧
        p ∈ closure {γ.point} := by
    intro η p Z₀ hηF hηp hp hZ₀ hpZ hηZ
    obtain ⟨y, hηy, hyp, hyZ, hy⟩ := exists_isProperCurve_of_specializes sX hηp hp hZ₀ hpZ hηZ
    have hsub : closure {y} ⊆ F :=
      closure_minimal (Set.singleton_subset_iff.mpr (hηy.mem_closed hF hηF)) hF
    refine ⟨⟨y, hy⟩, fun z hz => ?_, hsub, hyZ, specializes_iff_mem_closure.mp hyp⟩
    have h1 : f z = f x := hsub hz
    have h2 : f y = f x := hsub (subset_closure rfl)
    rw [h1, h2]
  -- the fibre is not contained in `W`
  have hFW : ¬ F ⊆ W := by
    intro hFW
    have hdim : 0 < topologicalKrullDim F := by
      have := (MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hX.1 hZ.1
        f hf (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)).2.1
      have hx : x ∈ (MMP.Mori.exceptionalSet f : Set X) := hxE
      rw [this] at hx
      exact hx
    rw [topologicalKrullDim, Order.krullDim_pos_iff] at hdim
    obtain ⟨A, B, hAB⟩ := hdim
    have hBirr : IsIrreducible (Subtype.val '' (B : Set F)) :=
      B.isIrreducible.image _ continuous_subtype_val.continuousOn
    set η := hBirr.genericPoint
    have hη : closure ({η} : Set X) = closure (Subtype.val '' (B : Set F)) :=
      hBirr.isGenericPoint_genericPoint_closure
    have hBF : closure (Subtype.val '' (B : Set F)) ⊆ F :=
      closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.2) hF
    have hAcl : IsClosed (Subtype.val '' (A : Set F)) :=
      hF.isClosedEmbedding_subtypeVal.isClosedMap _ A.isClosed
    have hAne : (Subtype.val '' (A : Set F)).Nonempty := A.isIrreducible.nonempty.image _
    obtain ⟨x₀, hx₀A, hx₀⟩ := hAcl.exists_closed_singleton hAne
    have hx₀B : x₀ ∈ closure (Subtype.val '' (B : Set F)) :=
      subset_closure (Set.image_mono hAB.le hx₀A)
    have hηx₀ : η ⤳ x₀ := specializes_iff_mem_closure.mpr (hη ▸ hx₀B)
    have hηne : η ∉ ({x₀} : Set X) := by
      intro hη₀
      rw [Set.mem_singleton_iff] at hη₀
      apply hAB.not_ge
      intro z hz
      have hz' : z.1 ∈ closure ({η} : Set X) := hη ▸ subset_closure ⟨z, hz, rfl⟩
      rw [hη₀, hx₀.closure_eq, Set.mem_singleton_iff] at hz'
      obtain ⟨a, ha, ha'⟩ := hx₀A
      have : z = a := Subtype.ext (hz'.trans ha'.symm)
      exact this ▸ ha
    have hηF : η ∈ F := hBF (hη ▸ subset_closure rfl)
    obtain ⟨γ, hγ, hγF, -, -⟩ := curve hηF hηx₀ hx₀ hx₀ (Set.mem_singleton _) hηne
    exact hWc γ (hγF.trans hFW) hγ
  -- a finite cover of `F` by closed irreducible sets
  obtain ⟨Zs, hZfin, hZcl, hZirr, hZeq⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  by_cases hgood : ∃ t ∈ Zs, ¬ t ⊆ W ∧ (t ∩ W).Nonempty
  · obtain ⟨t, ht, htW, htm⟩ := hgood
    obtain ⟨p, hpt, hp⟩ := ((hZcl t ht).inter hW).exists_closed_singleton htm
    obtain ⟨η, hη⟩ := QuasiSober.sober (hZirr t ht) (hZcl t ht)
    have htF : t ⊆ F := hZeq ▸ Set.subset_sUnion_of_mem ht
    have hηW : η ∉ W := fun h => htW (hη ▸ closure_minimal (Set.singleton_subset_iff.mpr h) hW)
    obtain ⟨γ, hγ, -, hγW, hpγ⟩ := curve (htF hη.mem) (hη.specializes hpt.1) hp hW hpt.2 hηW
    refine ⟨γ, hγ, fun h => hγW (h (subset_closure rfl)), p, hpγ, hpt.2⟩
  · exfalso
    push Not at hgood
    have hc := (MMP.Resolution.Bridges.isIso_app_and_isConnected_of_isBirationalMorphism sX sZ
      hX.1 hZ f hfb).2 (f x)
    set T1 := ⋃₀ {t ∈ Zs | t ⊆ W}
    set T2 := ⋃₀ {t ∈ Zs | ¬ t ⊆ W}
    have hT1 : IsClosed T1 :=
      (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
    have hT2 : IsClosed T2 :=
      (hZfin.subset (Set.sep_subset _ _)).isClosed_sUnion fun t ht => hZcl t ht.1
    have hcov : F ⊆ T1 ∪ T2 := by
      intro z hz
      rw [hZeq] at hz
      obtain ⟨t, ht, hzt⟩ := hz
      by_cases htW : t ⊆ W
      · exact Or.inl ⟨t, ⟨ht, htW⟩, hzt⟩
      · exact Or.inr ⟨t, ⟨ht, htW⟩, hzt⟩
    obtain ⟨z, hz, h1, h2⟩ := isPreconnected_closed_iff.mp hc.isPreconnected T1 T2 hT1 hT2 hcov
      (by
        obtain ⟨t, ht, hxt⟩ : x ∈ ⋃₀ Zs := hZeq ▸ hxF
        by_cases htW : t ⊆ W
        · exact ⟨x, hxF, t, ⟨ht, htW⟩, hxt⟩
        · exact (Set.eq_empty_iff_forall_notMem.mp (hgood t ht htW) x ⟨hxt, hxW⟩).elim)
      (by
        obtain ⟨z, hzF, hzW⟩ := Set.not_subset.mp hFW
        obtain ⟨t, ht, hzt⟩ : z ∈ ⋃₀ Zs := hZeq ▸ hzF
        have htW : ¬ t ⊆ W := fun h => hzW (h hzt)
        exact ⟨z, hzF, t, ⟨ht, htW⟩, hzt⟩)
    obtain ⟨t₁, ⟨-, ht₁W⟩, hzt₁⟩ := h1
    obtain ⟨t₂, ⟨ht₂, ht₂W⟩, hzt₂⟩ := h2
    exact Set.eq_empty_iff_forall_notMem.mp (hgood t₂ ht₂ ht₂W) z ⟨hzt₂, ht₁W hzt₁⟩

/-- A scheme separated over `ℂ` is separated. -/
private theorem isSeparated_toTerminal {X : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) [IsSeparated sX] :
    IsSeparated (X ↘ Limits.terminal Scheme) := by
  rw [show (X ↘ Limits.terminal Scheme) = sX ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
    Limits.terminal.hom_ext _ _]
  infer_instance

/-- Two birational morphisms to a reduced separated scheme are related by a birational map. -/
private theorem exists_isBirational_compHom_eq {X Xp Z : Scheme.{0}} [IsReduced X] [IsReduced Xp]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] (f : X ⟶ Z) (fp : Xp ⟶ Z)
    (hf : IsBirationalMorphism f) (hfp : IsBirationalMorphism fp) :
    ∃ ψ : X.RationalMap Xp, MMP.Mori.RationalMap.IsBirational ψ ∧
      ψ.compHom fp = f.toRationalMap := by
  obtain ⟨em, hm⟩ := hf
  obtain ⟨ep, hp⟩ := hfp
  have h1 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq em f (𝟙 Z) hm
  have h2 := MMP.Fourfold.PartialIso.isOver_comp_of_toRationalMap_eq ep fp (𝟙 Z) hp
  simp only [Category.comp_id] at h1 h2
  set e := em.trans ep.symm
  have H : e.IsOver f fp := h1.trans h2.symm
  refine ⟨e.toRationalMap, MMP.Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨e.source, e.dense_source, le_rfl, le_top, ?_⟩
  change X.homOfLE (le_rfl : e.source ≤ e.source) ≫ (e.iso.hom ≫ e.target.ι) ≫ fp =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, H]
  simp

section FlipStep

variable {X Xp Z : Scheme.{0}}

/-- A prime divisor of `X` has a partner on `X⁺` over the same point of `Z`. -/
private theorem exists_primeDivisor_map_genericPoint_eq (f : X ⟶ Z) (fp : Xp ⟶ Z) (V : Z.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (P : MMP.Mori.PrimeDivisor X) :
    ∃ Pp : MMP.Mori.PrimeDivisor Xp, fp Pp.genericPoint = f P.genericPoint := by
  have hy : f P.genericPoint ∈ V :=
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  obtain ⟨p, hp⟩ := (fp ∣_ V).surjective ⟨f P.genericPoint, hy⟩
  set x := (fp ⁻¹ᵁ V).ι p
  have hx : fp x = f P.genericPoint := by
    have e : V.ι ((fp ∣_ V) p) = fp ((fp ⁻¹ᵁ V).ι p) := by
      rw [← Scheme.Hom.comp_apply, morphismRestrict_ι, Scheme.Hom.comp_apply]
    rw [← e, hp]; rfl
  have hVf : V ≤ biregularLocus f := le_biregularLocus (f := f) (V := V) ‹_›
  have hVfp : V ≤ biregularLocus fp := le_biregularLocus (f := fp) (V := V) ‹_›
  have hcoh : Order.coheight x = 1 := by
    rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus fp (hVfp (hx ▸ hy)), hx,
      MMP.Positivity.coheight_map_of_mem_biregularLocus f (hVf hy),
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh, ?_⟩
  convert hx using 2
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh

/-- Partners over `V` are strict transforms of each other. -/
private theorem flipTransformPrimeDivisor_eq_some_of_map_genericPoint_eq [IsReduced X] [IsReduced Xp]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] (f : X ⟶ Z) (fp : Xp ⟶ Z) (V : Z.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    {P : MMP.Mori.PrimeDivisor X} {Pp : MMP.Mori.PrimeDivisor Xp}
    (h : fp Pp.genericPoint = f P.genericPoint) :
    flipTransformPrimeDivisor f fp P = some Pp := by
  have hy : f P.genericPoint ∈ V :=
    hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint P).le
  have hVf : V ≤ biregularLocus f := le_biregularLocus (f := f) (V := V) ‹_›
  have hVfp : V ≤ biregularLocus fp := le_biregularLocus (f := fp) (V := V) ‹_›
  have hcoh : Order.coheight (f P.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus f (hVf hy),
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh
  have hQ : Q.genericPoint = f P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh
  unfold flipTransformPrimeDivisor
  rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff f P Q).mpr hQ.symm,
    Option.bind_some]
  exact (MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' fp Q Pp).mpr
    ⟨hQ ▸ hVfp hy, h.trans hQ.symm⟩

/-- Over `V`, every prime divisor of `X⁺` is the transform of a prime divisor of `X`. -/
private theorem exists_transformPrimeDivisor_eq_some [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsReduced Xp] [IsSeparated (Z ↘ Limits.terminal Scheme)] [IsSeparated (Xp ↘ Limits.terminal Scheme)]
    {sZ : Z ⟶ Spec (.of ℂ)} (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) (fp : Xp ⟶ Z)
    (hX : IsNormalVariety ℂ (f ≫ sZ)) [IsProper f] (hfb : IsBirationalMorphism f) (V : Z.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hXpV : ∀ x : Xp, Order.coheight x ≤ 1 → fp x ∈ V) {ψ : X.RationalMap Xp}
    (hψ : ψ.compHom fp = f.toRationalMap) (Pp : MMP.Mori.PrimeDivisor Xp) :
    ∃ P : MMP.Mori.PrimeDivisor X, MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some Pp := by
  obtain ⟨P, hP⟩ := exists_primeDivisor_map_genericPoint_eq fp f V hXpV Pp
  refine ⟨P, ?_⟩
  have h1 := MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZ hX hfb V hXV hXpV hψ
    (Finsupp.single P (1 : ℤ))
  rw [flipTransform_single_of_eq_some
    (flipTransformPrimeDivisor_eq_some_of_map_genericPoint_eq f fp V hXV hP.symm)] at h1
  rcases h : MMP.Mori.RationalMap.transformPrimeDivisor ψ P with _ | E
  · rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_none h] at h1
    exact absurd h1.symm (Finsupp.single_ne_zero.mpr one_ne_zero)
  · rw [MMP.Mori.RationalMap.transformDivisor_single_of_eq_some h] at h1
    exact congrArg some (Finsupp.single_left_injective one_ne_zero h1)

/-- Over `V`, the strict transform back from `X⁺` undoes the strict transform to `X⁺`. -/
private theorem flipTransform_flipTransform [IsReduced X] [IsReduced Xp]
    [IsSeparated (Z ↘ Limits.terminal Scheme)] (f : X ⟶ Z) (fp : Xp ⟶ Z) (V : Z.Opens)
    [IsIso (f ∣_ V)] [IsIso (fp ∣_ V)] (hXV : ∀ x : X, Order.coheight x ≤ 1 → f x ∈ V)
    (hXpV : ∀ x : Xp, Order.coheight x ≤ 1 → fp x ∈ V) (D : RDivisor X) :
    flipTransform fp f (flipTransform f fp D) = D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D D' h h' => rw [map_add, map_add, h, h']
  | single P r =>
    obtain ⟨Pp, hPp⟩ := exists_primeDivisor_map_genericPoint_eq f fp V hXV P
    rw [flipTransform_single_of_eq_some
      (flipTransformPrimeDivisor_eq_some_of_map_genericPoint_eq f fp V hXV hPp),
      flipTransform_single_of_eq_some
      (flipTransformPrimeDivisor_eq_some_of_map_genericPoint_eq fp f V hXpV hPp.symm)]

/-- A small birational contraction which is not an isomorphism contracts a proper curve. -/
private theorem exists_properCurve_isContractedBy_of_not_isIso [IsIntegral X] [IsLocallyNoetherian X]
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX] (sZ : Z ⟶ Spec (.of ℂ)) (hX : IsNormalVariety ℂ sX)
    (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z) (hf : f ≫ sZ = sX) [IsProper f]
    (hfb : IsBirationalMorphism f) (hfi : ¬ IsIso f) :
    ∃ γ : ProperCurve sX, γ.IsContractedBy f := by
  by_contra hno
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  have hq : LocallyQuasiFinite f := by
    by_contra h
    exact hno (MMP.Fourfold.exists_properCurve_isContractedBy_of_not_locallyQuasiFinite h)
  exact hfi ((MMP.Resolution.Bridges.isIso_finiteFibreLocus_and_exceptionalSet_eq ℂ hX.1 hZ.1 f hf
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hfb)).2.2 hq)

end FlipStep

/-- **Sign transfer through a flip of relative Picard number one.** Let `f : X ⟶ Z` and
`f⁺ : X⁺ ⟶ Z` be proper birational morphisms from `ℚ`-factorial normal complex varieties with
`ρ(X/Z) = 1`, let `ψ : X ⤏ X⁺` be a map over `Z` under which every prime divisor of `X⁺` is a
transform, and suppose `f⁺` contracts some proper curve. Let `C` be an `ℝ`-divisor positive on
every curve contracted by `f` whose transform `ψ_* C` is negative on every curve contracted by
`f⁺`, and let `S` be a prime divisor with `ψ_* S = S⁺`. If a curve contracted by `f` meets `S`
without lying in it, then some curve contracted by `f⁺` lies in `S⁺`: `S ≡_f c C` with `c > 0`,
so `S⁺ ≡_{f⁺} c ψ_* C` is negative on that curve. -/
private theorem exists_properCurve_subset_of_relativePicardNumber_eq_one
    {X Z Xp : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (sXp : Xp ⟶ Spec (.of ℂ))
    [QuasiCompact sX] [QuasiCompact sXp]
    (hQ : IsQFactorial sX) (hQp : IsQFactorial sXp)
    (f : X ⟶ Z) (fp : Xp ⟶ Z) (hf : f ≫ sZ = sX) (hfp : fp ≫ sZ = sXp) [IsProper f]
    [IsProper fp] (hfb : IsBirationalMorphism f) (hfpb : IsBirationalMorphism fp)
    (hρ : MMP.Flips.relativePicardNumber sX f = 1)
    (ψ : X.RationalMap Xp) (hψ : MMP.Flips.RationalMap.IsOver f fp ψ)
    (hψP : ∀ P' : MMP.Mori.PrimeDivisor Xp, ∃ P : MMP.Mori.PrimeDivisor X,
      MMP.Mori.RationalMap.transformPrimeDivisor ψ P = some P')
    (hcurve : ∃ γ : ProperCurve sXp, γ.IsContractedBy fp)
    (C : RDivisor X)
    (hCpos : ∀ γ : ProperCurve sX, γ.IsContractedBy f → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ), MMP.Flips.IsRIntersectionNumber ℂ sX C r L γ x → 0 < x)
    (hCneg : ∀ γ : ProperCurve sXp, γ.IsContractedBy fp → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor Xp) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sXp (MMP.Mori.RationalMap.transformDivisor ψ C) r L γ x →
        x < 0)
    (S : MMP.Mori.PrimeDivisor X) (Sp : MMP.Mori.PrimeDivisor Xp)
    (hS : MMP.Mori.RationalMap.transformDivisor ψ (Finsupp.single S (1 : ℝ)) =
      Finsupp.single Sp 1)
    (γ : ProperCurve sX) (hγ : γ.IsContractedBy f)
    (hγS : ¬ closure {γ.point} ⊆ (S.support : Set X))
    (hγmeet : (closure {γ.point} ∩ (S.support : Set X)).Nonempty) :
    ∃ γp : ProperCurve sXp, γp.IsContractedBy fp ∧ closure {γp.point} ⊆ (Sp.support : Set Xp) := by
  classical
  have hX : IsNormalVariety ℂ sX := hQ.1
  have hfin : Module.finrank ℝ (MMP.Flips.RelativeNumericalDivisorClasses sX f) = 1 :=
    Module.finrank_eq_of_rank_eq (by rw [Cardinal.toENat_eq_one.mp hρ]; rfl)
  set SR : RDivisor X := Finsupp.single S (1 : ℝ)
  have hSRc := isCartierCombination_of_isQFactorial hQ SR
  obtain ⟨δS, hδSex, hδS⟩ := exists_kCartierDivisor_isRIntersectionNumber sX hSRc
  obtain ⟨δC, hδCex, hδC⟩ :=
    exists_kCartierDivisor_isRIntersectionNumber sX (isCartierCombination_of_isQFactorial hQ C)
  have hSReff : SR.IsEffective := fun E => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> norm_num
  -- `S · γ > 0`
  have hσ : 0 < (γ.cycle ℝ).intersectionNumber δS := by
    obtain ⟨m, r, L, h⟩ := hδSex γ
    refine MMP.Flips.IsRIntersectionNumber.pos_of_isEffective ℂ sX hX hSRc hSReff γ ?_ ?_ r L h
    · rw [MMP.Mori.ProperCurve.range_ι, coe_supp_single_one]; exact hγS
    · rw [MMP.Mori.ProperCurve.range_ι, coe_supp_single_one]; exact hγmeet
  have hc0 : 0 < (γ.cycle ℝ).intersectionNumber δC := by
    obtain ⟨m, r, L, h⟩ := hδCex γ
    exact hCpos γ hγ m r L _ h
  obtain ⟨c, hc⟩ :=
    MMP.Flips.exists_intersectionNumber_eq_mul_of_finrank_eq_one f hfin δC δS hγ hc0.ne'
  have hcpos : 0 < c := by
    have := hc γ hγ
    by_contra hle
    push Not at hle
    nlinarith
  -- `S - c C ≡_f 0`
  set G : RDivisor X := (1 : ℝ) • SR + (-c) • C
  have hGc := isCartierCombination_of_isQFactorial hQ G
  have hG : MMP.Flips.IsNumericallyTrivialOver ℂ sX f G := by
    refine ⟨hGc, isCartierCombination_of_isQFactorial hQ 0, ?_⟩
    intro γ' hγ' m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂
    obtain ⟨heq, hlin⟩ := MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX γ'
    obtain ⟨_, _, _, hs⟩ := hδSex γ'
    obtain ⟨_, _, _, hcc⟩ := hδCex γ'
    have h1 := heq _ _ _ _ _ _ _ h₁ (hlin _ _ _ _ _ _ _ _ 1 (-c) hs hcc)
    have h2 := heq _ _ _ _ _ _ _ h₂ (isRIntersectionNumber_zero_divisor sX γ')
    rw [h1, h2, hc γ' hγ']
    ring
  -- its transform `S⁺ - c C⁺` is `≡_{f⁺} 0`
  have hT := (MMP.Flips.IsNumericallyTrivialOver.transformDivisor_of_isOver sZ hX hQp hf hfp hfb
    hfpb hψ hψP hGc hG).2
  have htr : MMP.Mori.RationalMap.transformDivisor ψ G = (1 : ℝ) • Finsupp.single Sp (1 : ℝ) +
      (-c) • MMP.Mori.RationalMap.transformDivisor ψ C := by
    have := (MMP.Mori.RationalMap.transformDivisorₗ ℝ ψ).map_add ((1 : ℝ) • SR) ((-c) • C)
    simp only [MMP.Mori.RationalMap.transformDivisorₗ_apply, LinearMap.map_smul] at this
    rw [show G = (1 : ℝ) • SR + (-c) • C from rfl, this, hS]
  rw [htr] at hT
  obtain ⟨γp, hγp⟩ := hcurve
  refine ⟨γp, hγp, ?_⟩
  by_contra hno
  set SpR : RDivisor Xp := Finsupp.single Sp (1 : ℝ)
  have hSpRc := isCartierCombination_of_isQFactorial hQp SpR
  obtain ⟨δS', hδSex', -⟩ := exists_kCartierDivisor_isRIntersectionNumber sXp hSpRc
  obtain ⟨δC', hδCex', -⟩ := exists_kCartierDivisor_isRIntersectionNumber sXp
    (isCartierCombination_of_isQFactorial hQp (MMP.Mori.RationalMap.transformDivisor ψ C))
  obtain ⟨m₁, r₁, L₁, hs⟩ := hδSex' γp
  obtain ⟨m₂, r₂, L₂, hcc⟩ := hδCex' γp
  have hneg := hCneg γp hγp m₂ r₂ L₂ _ hcc
  have hSpReff : SpR.IsEffective := fun E => by
    rw [DivisorWithCoeffs.coeff_apply, Finsupp.single_apply]; split_ifs <;> norm_num
  have hnn := MMP.Flips.IsRIntersectionNumber.nonneg_of_isEffective ℂ sXp hQp.1 SpR hSpRc hSpReff
    γp (by
      rw [← SetLike.mem_coe, coe_supp_single_one]
      intro hmem
      apply hno
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hmem ⊢
      exact closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure) r₁ L₁ hs
  have hz := hT.2.2 γp hγp _ _ _ _ _ _ _ _
    ((MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sXp γp).2 _ _ _ _ _ _ _ _ 1 (-c) hs hcc)
    (isRIntersectionNumber_zero_divisor sXp γp)
  nlinarith

/-- **The scaling divisor is negative on the flipped ray.** If `K + B + λC` (`λ > 0`) is the
pull-back of an `ℝ`-Cartier divisor along `f` and `K + B` is `f`-ample, then `C` is negative on
every proper curve contracted by `f`. -/
private theorem neg_of_isRCartierPullback_of_isRelativelyAmple
    {X Z : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX)
    (K : Divisor X) (B C : RDivisor X) (lam : ℝ) (hlam : 0 < lam) (D : RDivisor Z)
    (hD : MMP.Flips.IsRCartierPullback f D (MMP.Flips.logCanonicalDivisor K (B + lam • C)))
    (hpos : MMP.Flips.IsRelativelyAmple f (MMP.Flips.logCanonicalDivisor K B))
    (γ : ProperCurve sX) (hγ : γ.IsContractedBy f) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor X) {x : ℝ} (hx : MMP.Flips.IsRIntersectionNumber ℂ sX C r L γ x) :
    x < 0 := by
  haveI : QuasiCompact sX := by rw [← hf]; haveI := hZ.1.toQuasiCompact; infer_instance
  obtain ⟨m₁, r₁, L₁, h₁⟩ := isRIntersectionNumber_zero_of_isRCartierPullback sX sZ hZ f hf hD γ hγ
  obtain ⟨m₂, r₂, L₂, p, h₂, hp⟩ :=
    exists_isRIntersectionNumber_pos_of_isRelativelyAmple sX f hpos γ hγ
  obtain ⟨heq, hlin⟩ := MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX γ
  have hU := hlin _ _ _ _ _ _ _ _ 1 (-1) h₁ h₂
  have hC := hlin _ _ _ _ _ _ _ _ lam 0 hx hx
  have hdiv : (1 : ℝ) • MMP.Flips.logCanonicalDivisor K (B + lam • C) +
      (-1 : ℝ) • MMP.Flips.logCanonicalDivisor K B = lam • C + (0 : ℝ) • C := by
    simp only [MMP.Flips.logCanonicalDivisor, one_smul, zero_smul, add_zero, neg_one_smul]
    abel
  rw [hdiv] at hU
  have := heq _ _ _ _ _ _ _ hU hC
  nlinarith

/-- **A flip whose two strata contain no contracted curve misses them.** Let
`X ⟶ Z ⟵ X⁺` be a real flip step of projective `ℚ`-factorial complex fourfolds run with scaling
of `C ≥ 0` at level `λ > 0`, the upper adjoint `K + B + λC` being the pull-back of one
`ℝ`-Cartier divisor on `Z` to both sides, and let `S` be a prime divisor of `X` with strict
transform `S⁺`. If no proper curve contained in `S` is contracted by `f`, and no proper curve
contained in `S⁺` is contracted by `f⁺`, then the flipping locus misses `S` and the flipped locus
misses `S⁺`. -/
private theorem disjoint_exceptionalSet_of_forall_properCurve_not_contracted
    {X Z Xp : Scheme.{0}} [IsIntegral X] [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Xp] [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp]
    [IsLocallyNoetherian Z] [IsNormal Z]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (sXp : Xp ⟶ Spec (.of ℂ))
    (K : Divisor X) (B : RDivisor X) (Kp : Divisor Xp) (Bp : RDivisor Xp)
    (f : X ⟶ Z) (fp : Xp ⟶ Z)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hprojp : MMP.Mori.IsProjectiveVariety ℂ sXp)
    (hQ : IsQFactorial sX) (hQp : IsQFactorial sXp)
    (hflip : IsRealFlipStep sX sZ sXp K B Kp Bp f fp)
    (C : RDivisor X) (lam : ℝ) (hlam : 0 < lam)
    (hcrep : ∃ D : RDivisor Z,
      MMP.Flips.IsRCartierPullback f D (MMP.Flips.logCanonicalDivisor K (B + lam • C)) ∧
      MMP.Flips.IsRCartierPullback fp D
        (MMP.Flips.logCanonicalDivisor Kp (Bp + lam • flipTransform f fp C)))
    (S : MMP.Mori.PrimeDivisor X) (Sp : MMP.Mori.PrimeDivisor Xp)
    (hS : flipTransformPrimeDivisor f fp S = some Sp)
    (hSc : ∀ γ : ProperCurve sX, closure {γ.point} ⊆ (S.support : Set X) →
      ¬ γ.IsContractedBy f)
    (hSpc : ∀ γ : ProperCurve sXp, closure {γ.point} ⊆ (Sp.support : Set Xp) →
      ¬ γ.IsContractedBy fp) :
    Disjoint (MMP.Mori.exceptionalSet f : Set X) (S.support : Set X) ∧
      Disjoint (MMP.Mori.exceptionalSet fp : Set Xp) (Sp.support : Set Xp) := by
  have hNEC := hflip.isNegativeExtremalContraction
  have hX : IsNormalVariety ℂ sX := hNEC.isNormalVariety_source
  have hZ : IsNormalVariety ℂ sZ := hNEC.isNormalVariety_target
  have hXp : IsNormalVariety ℂ sXp := hQp.1
  have hf : f ≫ sZ = sX := hflip.isSmall.comp_eq
  have hfp : fp ≫ sZ = sXp := hflip.isSmall_flip.comp_eq
  haveI : IsProper f := hflip.isSmall.isProper
  haveI : IsProper fp := hflip.isSmall_flip.isProper
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hproj.isProjective
  haveI : IsProper sXp := isProper_of_isProjectiveMorphism sXp hprojp.isProjective
  have hfb := hflip.isBirationalMorphism
  have hfpb := hflip.isBirationalMorphism_flip
  obtain ⟨D, hD, hDp⟩ := hcrep
  have hCc := isCartierCombination_of_isQFactorial hQ C
  have hCpc := isCartierCombination_of_isQFactorial hQp (flipTransform f fp C)
  have hCpos := fun γ hγ m r L x hx =>
    pos_of_isRCartierPullback_of_isRelativelyAntiAmple sX sZ hZ f hf K B C lam hlam D hD
      hNEC.isRelativelyAntiAmple γ hγ (m := m) r L (x := x) hx
  have hCneg := fun γ hγ m r L x hx =>
    neg_of_isRCartierPullback_of_isRelativelyAmple sXp sZ hZ fp hfp Kp Bp (flipTransform f fp C)
      lam hlam D hDp hflip.isRelativelyAmple_flip γ hγ (m := m) r L (x := x) hx
  -- the open of `Z` over which both contractions are isomorphisms
  obtain ⟨V, hfV, hfpV, hXV, hXpV⟩ := MMP.Fourfold.IsRealFlipStep.exists_opens_isIso hflip
  haveI := hfV
  haveI := hfpV
  haveI := @isSeparated_toTerminal _ sZ hZ.1.toIsSeparated
  haveI := @isSeparated_toTerminal _ sX hX.1.toIsSeparated
  haveI := @isSeparated_toTerminal _ sXp hXp.1.toIsSeparated
  -- the flip `ψ = (f⁺)⁻¹ ∘ f` and its inverse `ψ₂`
  obtain ⟨ψ, -, hψ⟩ := exists_isBirational_compHom_eq f fp hfb hfpb
  obtain ⟨ψ₂, -, hψ₂⟩ := exists_isBirational_compHom_eq fp f hfpb hfb
  have hXZ : IsNormalVariety ℂ (f ≫ sZ) := hf ▸ hX
  have hXpZ : IsNormalVariety ℂ (fp ≫ sZ) := hfp ▸ hXp
  have htr : ∀ D : RDivisor X, MMP.Mori.RationalMap.transformDivisor ψ D = flipTransform f fp D :=
    fun D => MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZ hXZ hfb V hXV hXpV hψ D
  have htr₂ : ∀ D : RDivisor Xp,
      MMP.Mori.RationalMap.transformDivisor ψ₂ D = flipTransform fp f D := fun D =>
    MMP.Mori.transformDivisor_eq_flipTransform_of_isIso_restrict hZ hXpZ hfpb V hXpV hXV hψ₂ D
  have hψP := exists_transformPrimeDivisor_eq_some hZ f fp hXZ hfb V hXV hXpV hψ
  have hψ₂P := exists_transformPrimeDivisor_eq_some hZ fp f hXpZ hfpb V hXpV hXV hψ₂
  have hSgen : fp Sp.genericPoint = f S.genericPoint := by
    obtain ⟨Pp, hPp⟩ := exists_primeDivisor_map_genericPoint_eq f fp V hXV S
    have h := flipTransformPrimeDivisor_eq_some_of_map_genericPoint_eq f fp V hXV hPp
    rw [hS] at h
    cases Option.some.inj h
    exact hPp
  have hS₁ : MMP.Mori.RationalMap.transformDivisor ψ (Finsupp.single S (1 : ℝ)) =
      Finsupp.single Sp 1 := by
    rw [htr, flipTransform_single_of_eq_some hS]
  have hS₂ : MMP.Mori.RationalMap.transformDivisor ψ₂ (Finsupp.single Sp (1 : ℝ)) =
      Finsupp.single S 1 := by
    rw [htr₂, flipTransform_single_of_eq_some
      (flipTransformPrimeDivisor_eq_some_of_map_genericPoint_eq fp f V hXpV hSgen.symm)]
  have hcurvep := exists_properCurve_isContractedBy_of_not_isIso sXp sZ hXp hZ fp hfp hfpb
    hflip.not_isIso_flip
  have hcurve := exists_properCurve_isContractedBy_of_not_isIso sX sZ hX hZ f hf hfb
    hflip.not_isIso
  have hSclosed : IsClosed (S.support : Set X) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  have hSpclosed : IsClosed (Sp.support : Set Xp) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact isClosed_closure
  refine ⟨Set.disjoint_left.2 fun y hyE hyS => ?_, Set.disjoint_left.2 fun y hyE hyS => ?_⟩
  · obtain ⟨γ, hγ, hγS, hγm⟩ := exists_properCurve_isContractedBy_of_mem_exceptionalSet sX sZ hX
      hZ f hf hfb hSclosed hSc ⟨y, hyE, hyS⟩
    obtain ⟨γp, hγp, hγpS⟩ := exists_properCurve_subset_of_relativePicardNumber_eq_one sX sZ sXp
      hQ hQp f fp hf hfp hfb hfpb hNEC.relativePicardNumber_eq_one ψ hψ hψP hcurvep C hCpos
      (fun γ hγ m r L x hx => hCneg γ hγ m r L x (by rwa [htr] at hx)) S Sp hS₁ γ hγ hγS hγm
    exact hSpc γp hγpS hγp
  · obtain ⟨γp, hγp, hγpS, hγpm⟩ := exists_properCurve_isContractedBy_of_mem_exceptionalSet sXp
      sZ hXp hZ fp hfp hfpb hSpclosed hSpc ⟨y, hyE, hyS⟩
    obtain ⟨γ, hγ, hγS⟩ := exists_properCurve_subset_of_relativePicardNumber_eq_one sXp sZ sX
      hQp hQ fp f hfp hf hfpb hfb hflip.relativePicardNumber_flip ψ₂ hψ₂ hψ₂P hcurve
      (-(flipTransform f fp C))
      (fun γ hγ m r L x hx => by
        obtain ⟨_, _, _, y, hy, rfl⟩ := neg_of_isRIntersectionNumber_neg sXp hCpc γ hx
        linarith [hCneg γ hγ _ _ _ _ hy])
      (fun γ hγ m r L x hx => by
        rw [htr₂, map_neg, flipTransform_flipTransform f fp V hXV hXpV C] at hx
        obtain ⟨_, _, _, y, hy, rfl⟩ := neg_of_isRIntersectionNumber_neg sX hCc γ hx
        linarith [hCpos γ hγ _ _ _ _ hy])
      Sp S hS₂ γp hγp hγpS hγpm
    exact hSc γ hγS hγ

/-! ### Curves under a crepant roof -/

/-- The degree of the pull-back of a Cartier divisor on a curve not contracted by `φ` is the
residue degree times the degree on the image curve. -/
private theorem degreeOn_pullback_eq_mul {V T : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V]
    [IsNormal V] [CompactSpace V] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]
    (sV : V ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ)) [IsSeparated sT] [LocallyOfFiniteType sT]
    [QuasiCompact sT] [QuasiCompact sV] (φ : V ⟶ T) (hφ : φ ≫ sT = sV)
    (L : Divisor T) (hL : L.IsCartier)
    (hB : ∀ Z : irreducibleComponents V, φ (componentGenericPoint V Z) ∉ L.supp)
    (c : ProperCurve sV) (c' : ProperCurve sT) (hcc : c'.point = φ c.point) :
    (L.pullback hL hB).degreeOn ℂ sV c.ι c.dim_le (hL.isCartier_pullback φ hB) =
      (residueFieldDegree φ c.point : ℤ) * L.degreeOn ℂ sT c'.ι c'.dim_le hL := by
  obtain ⟨p, hc⟩ := c'
  change p = φ c.point at hcc
  subst hcc
  obtain ⟨e⟩ := Divisor.nonempty_divisorialSheaf_pullback_iso hL φ hB
  haveI := hL.isInvertibleModule_divisorialSheaf
  haveI := (hL.isCartier_pullback φ hB).isInvertibleModule_divisorialSheaf
  have h := ProperCurve.degree_pullback φ hφ c L.divisorialSheaf
  rw [dif_pos hc] at h
  unfold Divisor.degreeOn
  rw [degreeOn_eq_of_iso ℂ sV c.ι c.dim_le e]
  exact h

/-- A morphism to a projective variety has positive residue degree at a curve it does not
contract. -/
private theorem residueFieldDegree_pos_of_not_isContractedBy {V T : Scheme.{0}}
    {sV : V ⟶ Spec (.of ℂ)} {sT : T ⟶ Spec (.of ℂ)} (hT : MMP.Mori.IsProjectiveVariety ℂ sT)
    (φ : V ⟶ T) (hφ : φ ≫ sT = sV) (c : ProperCurve sV) (hc : ¬ c.IsContractedBy φ) :
    0 < residueFieldDegree φ c.point := by
  haveI : IsSeparated sT := hT.1.toIsSeparated
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  obtain ⟨H, hH, hHa⟩ := MMP.ProgramBaseChange.exists_isAmple_of_isProjectiveVariety hT
  refine Nat.pos_of_ne_zero fun h0 => hc ?_
  refine MMP.ProgramBaseChange.isContractedBy_of_degree_pullback_eq_zero φ hφ H hHa c ?_
  rw [c.degree_pullback φ hφ H, dif_pos (MMP.Fourfold.Oai4C1.isProperCurve_map φ hφ c hc), h0]
  simp

/-- On a curve not contracted by `φ`, an `ℝ`-Cartier pull-back has the residue degree times the
intersection number of the divisor on the image curve. -/
private theorem exists_isRIntersectionNumber_of_isRCartierPullback {V T : Scheme.{0}}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsLocallyNoetherian T]
    [IsNormal T] [CompactSpace T] (sV : V ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ))
    [IsSeparated sT] [LocallyOfFiniteType sT] [QuasiCompact sT] [QuasiCompact sV] (φ : V ⟶ T)
    (hφ : φ ≫ sT = sV) {D : RDivisor T} {G : RDivisor V} (hG : MMP.Flips.IsRCartierPullback φ D G)
    (c : ProperCurve sV) (c' : ProperCurve sT) (hcc : c'.point = φ c.point) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor T) (L' : Fin m → Divisor V) (y : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sV G r L' c ((residueFieldDegree φ c.point : ℝ) * y) ∧
      MMP.Flips.IsRIntersectionNumber ℂ sT D r L c' y := by
  obtain ⟨m, r, L, L', hLc, hDe, hpb, hGe⟩ := hG
  choose hB hpb using hpb
  have he : ∀ j, (L j).pullback (hLc j) (hB j) = L' j := fun j => (hpb j).pullback_eq (hLc j)
  have hL'c : ∀ j, (L' j).IsCartier := fun j => by
    rw [← he j]; exact (hLc j).isCartier_pullback φ (hB j)
  refine ⟨m, r, L, L', _, ?_, hDe ▸ isRIntersectionNumber_sum_degreeOn sT c' r L hLc⟩
  have h := isRIntersectionNumber_sum_degreeOn sV c r L' hL'c
  rw [← hGe] at h
  convert h using 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : ∀ (E : Divisor V) (hE : E.IsCartier), E = L' j →
      ((L' j).degreeOn ℂ sV c.ι c.dim_le (hL'c j) : ℝ) =
        (E.degreeOn ℂ sV c.ι c.dim_le hE : ℝ) := by
    rintro E hE rfl; rfl
  rw [key _ ((hLc j).isCartier_pullback φ (hB j)) (he j),
    degreeOn_pullback_eq_mul sV sT φ hφ (L j) (hLc j) (hB j) c c' hcc]
  push_cast
  ring

/-- **Signs of a pull-back on curves over `Z`.** Let `φ : V ⟶ T` be proper with `T` projective
and `G` the pull-back of an `ℝ`-Cartier `D`. If `s · (D · c) > 0` for every curve `c` of `T`
contracted by `u : T ⟶ Z`, then every curve of `V` contracted by `φ ≫ u` has `s · (G · c) ≥ 0`,
strictly when `φ` does not contract it. -/
private theorem exists_isRIntersectionNumber_pullback_sign {V T Z : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral T] [IsLocallyNoetherian T]
    [IsNormal T] [CompactSpace T] (sV : V ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ))
    (hT : MMP.Mori.IsProjectiveVariety ℂ sT) [QuasiCompact sV] (u : T ⟶ Z) (φ : V ⟶ T)
    [IsProper φ] (hφ : φ ≫ sT = sV) {D : RDivisor T} {G : RDivisor V}
    (hG : MMP.Flips.IsRCartierPullback φ D G)
    (s : ℝ) (hD : ∀ c : ProperCurve sT, c.IsContractedBy u → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor T) (x : ℝ), MMP.Flips.IsRIntersectionNumber ℂ sT D r L c x → 0 < s * x)
    (cV : ProperCurve sV) (hcV : cV.IsContractedBy (φ ≫ u)) :
    ∃ (m : ℕ) (r : Fin m → ℝ) (L : Fin m → Divisor V) (x : ℝ),
      MMP.Flips.IsRIntersectionNumber ℂ sV G r L cV x ∧ 0 ≤ s * x ∧
        (¬ cV.IsContractedBy φ → 0 < s * x) := by
  haveI : IsSeparated sT := hT.1.toIsSeparated
  haveI : LocallyOfFiniteType sT := hT.1.toLocallyOfFiniteType
  haveI : QuasiCompact sT := hT.1.toQuasiCompact
  by_cases hc : cV.IsContractedBy φ
  · obtain ⟨m, r, L, h0⟩ := isRIntersectionNumber_zero_of_isRCartierPullback sV sT
      ⟨hT.1, inferInstance⟩ φ hφ hG cV hc
    exact ⟨m, r, L, 0, h0, by simp, fun h => absurd hc h⟩
  · set c' : ProperCurve sT := ⟨_, MMP.Fourfold.Oai4C1.isProperCurve_map φ hφ cV hc⟩
    obtain ⟨m, r, L, L', y, hx, hy⟩ :=
      exists_isRIntersectionNumber_of_isRCartierPullback sV sT φ hφ hG cV c' rfl
    have hc' : c'.IsContractedBy u := by
      intro z hz
      have hz' : z ∈ φ.base '' closure {cV.point} := by
        rw [← φ.isClosedMap.closure_image_eq_of_continuous φ.continuous, Set.image_singleton]
        exact hz
      obtain ⟨w, hw, rfl⟩ := hz'
      have := hcV w hw
      simpa only [Scheme.Hom.comp_apply] using this
    have hsy := hD c' hc' m r L y hy
    have hd := residueFieldDegree_pos_of_not_isContractedBy hT φ hφ cV hc
    have hd' : (0 : ℝ) < residueFieldDegree φ cV.point := by exact_mod_cast hd
    refine ⟨m, r, L', _, hx, ?_, fun _ => ?_⟩
    · nlinarith
    · nlinarith

/-- The generic point of a proper curve is not closed. -/
private theorem ProperCurve.closure_point_ne_singleton {X : Scheme.{0}} {sX : X ⟶ Spec (.of ℂ)}
    (c : ProperCurve sX) (x : X) : closure ({c.point} : Set X) ≠ {x} := by
  intro h
  have hrange := c.range_ι
  rw [h] at hrange
  have : Subsingleton c.scheme := ⟨fun a b => c.ι.isEmbedding.injective (by
    have ha : c.ι a ∈ Set.range c.ι.base := ⟨a, rfl⟩
    have hb : c.ι b ∈ Set.range c.ι.base := ⟨b, rfl⟩
    rw [hrange] at ha hb
    exact ha.trans hb.symm)⟩
  have h0 : topologicalKrullDim c.scheme ≤ 0 := by
    haveI : DiscreteTopology c.scheme := ⟨Subsingleton.elim _ _⟩
    exact topologicalKrullDim_zero_of_discreteTopology _
  rw [c.dim_eq] at h0
  exact absurd h0 (by decide)

/-- **A crepant roof over `Z` has no contracted curve below it.** Let `h : V ⟶ T` and
`h⁺ : V ⟶ T⁺` be proper surjective morphisms of varieties over `Z` (through `u`, `u⁺`) with `T`,
`T⁺` projective, and `G` the pull-back of `D` along `h` and of `D⁺` along `h⁺`. If `D` is negative
on every curve contracted by `u` and `D⁺` positive on every curve contracted by `u⁺`, then neither
`u` nor `u⁺` contracts a proper curve: a contracted curve lifts to a curve of `V` on which `G` is
then both negative and nonnegative. -/
private theorem forall_not_isContractedBy_of_isRCartierPullback {V T Tp Z : Scheme.{0}}
    [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] [IsIntegral T]
    [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T] [IsIntegral Tp] [IsLocallyNoetherian Tp]
    [IsNormal Tp] [CompactSpace Tp] (sV : V ⟶ Spec (.of ℂ)) (sT : T ⟶ Spec (.of ℂ))
    (sTp : Tp ⟶ Spec (.of ℂ)) (hV : IsNormalVariety ℂ sV) (hT : MMP.Mori.IsProjectiveVariety ℂ sT)
    (hTp : MMP.Mori.IsProjectiveVariety ℂ sTp) (u : T ⟶ Z) (up : Tp ⟶ Z) (h : V ⟶ T)
    (hp : V ⟶ Tp) [IsProper h] [IsProper hp] [Surjective h] [Surjective hp]
    (hh : h ≫ sT = sV) (hhp : hp ≫ sTp = sV) (hcomm : h ≫ u = hp ≫ up)
    {G : RDivisor V} {D : RDivisor T} {Dp : RDivisor Tp}
    (hG : MMP.Flips.IsRCartierPullback h D G) (hGp : MMP.Flips.IsRCartierPullback hp Dp G)
    (hneg : ∀ c : ProperCurve sT, c.IsContractedBy u → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor T) (x : ℝ), MMP.Flips.IsRIntersectionNumber ℂ sT D r L c x → x < 0)
    (hpos : ∀ c : ProperCurve sTp, c.IsContractedBy up → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor Tp) (x : ℝ), MMP.Flips.IsRIntersectionNumber ℂ sTp Dp r L c x → 0 < x) :
    (∀ c : ProperCurve sT, ¬ c.IsContractedBy u) ∧
      (∀ c : ProperCurve sTp, ¬ c.IsContractedBy up) := by
  haveI : QuasiCompact sV := hV.1.toQuasiCompact
  have hneg' : ∀ c : ProperCurve sT, c.IsContractedBy u → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor T) (x : ℝ), MMP.Flips.IsRIntersectionNumber ℂ sT D r L c x →
        0 < (-1) * x := fun c hc m r L x hx => by linarith [hneg c hc m r L x hx]
  have hpos' : ∀ c : ProperCurve sTp, c.IsContractedBy up → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor Tp) (x : ℝ), MMP.Flips.IsRIntersectionNumber ℂ sTp Dp r L c x →
        0 < 1 * x := fun c hc m r L x hx => by linarith [hpos c hc m r L x hx]
  -- a lift of a curve of the base along a proper surjection is not contracted by it
  have lift : ∀ {W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ)) (hW : MMP.Mori.IsProjectiveVariety ℂ sW)
      (q : V ⟶ W) [IsProper q] [Surjective q] (hq : q ≫ sW = sV) (c : ProperCurve sW),
      ∃ cV : ProperCurve sV, ¬ cV.IsContractedBy q ∧
        q.base '' closure {cV.point} = closure {c.point} := by
    intro W sW hW q _ _ hq c
    obtain ⟨cV, hcV⟩ := ProperCurve.exists_image_closure_eq_of_surjective hV.1 hW.1 q hq c
    refine ⟨cV, fun hc => ?_, hcV⟩
    apply ProperCurve.closure_point_ne_singleton c (q cV.point)
    rw [← hcV]
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩; exact hc w hw
    · rintro _ rfl; exact ⟨cV.point, subset_closure rfl, rfl⟩
  have contr : ∀ {W : Scheme.{0}} (sW : W ⟶ Spec (.of ℂ)) (q : V ⟶ W) (w : W ⟶ Z)
      (c : ProperCurve sW) (cV : ProperCurve sV), c.IsContractedBy w →
      q.base '' closure {cV.point} = closure {c.point} → cV.IsContractedBy (q ≫ w) := by
    intro W sW q w c cV hc himg z hz
    have h1 : q z ∈ closure {c.point} := himg ▸ ⟨z, hz, rfl⟩
    have h2 : q cV.point ∈ closure {c.point} := himg ▸ ⟨cV.point, subset_closure rfl, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hc _ h1, hc _ h2]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨cV, hnc, himg⟩ := lift sT hT h hh c
    have hcV := contr sT h u c cV hc himg
    obtain ⟨m₁, r₁, L₁, x₁, h₁, -, hs₁⟩ :=
      exists_isRIntersectionNumber_pullback_sign sV sT hT u h hh hG (-1) hneg' cV hcV
    rw [hcomm] at hcV
    obtain ⟨m₂, r₂, L₂, x₂, h₂, hs₂, -⟩ :=
      exists_isRIntersectionNumber_pullback_sign sV sTp hTp up hp hhp hGp 1 hpos' cV hcV
    have := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sV cV).1 _ _ _ _ _ _ _ h₁ h₂
    have := hs₁ hnc
    linarith
  · obtain ⟨cV, hnc, himg⟩ := lift sTp hTp hp hhp c
    have hcV := contr sTp hp up c cV hc himg
    obtain ⟨m₂, r₂, L₂, x₂, h₂, -, hs₂⟩ :=
      exists_isRIntersectionNumber_pullback_sign sV sTp hTp up hp hhp hGp 1 hpos' cV hcV
    rw [← hcomm] at hcV
    obtain ⟨m₁, r₁, L₁, x₁, h₁, hs₁, -⟩ :=
      exists_isRIntersectionNumber_pullback_sign sV sT hT u h hh hG (-1) hneg' cV hcV
    have := (MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sV cV).1 _ _ _ _ _ _ _ h₁ h₂
    have := hs₂ hnc
    linarith

/-- A closed subscheme onto a prime divisor of a complex fourfold has dimension three. -/
private theorem topologicalKrullDim_eq_three {X T : Scheme.{0}} [IsIntegral X]
    (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (hdim : topologicalKrullDim X = 4)
    (S : MMP.Mori.PrimeDivisor X) (ι : T ⟶ X) [IsClosedImmersion ι]
    (hι : Set.range ι.base = (S.support : Set X)) : topologicalKrullDim T = (3 : ℕ) := by
  rw [IsHomeomorph.topologicalKrullDim_eq _
    ι.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph, hι,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX S.genericPoint
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint, hdim] at h
  generalize topologicalKrullDim (closure {S.genericPoint} : Set X) = d at h ⊢
  cases d using WithBot.recBotCoe with
  | bot => exact absurd h (by decide)
  | coe e =>
    cases e using ENat.recTopCoe with
    | top => exact absurd h (by decide)
    | coe d =>
      have h2 : (((d + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((4 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast; exact h
      have h3 := WithBot.coe_injective h2
      have h4 : d + 1 = 4 := by exact_mod_cast h3
      obtain rfl : d = 3 := by omega
      rfl

/-! ### Crepant models and residues -/

section CrepantKlt

open MMP

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)}

/-- **Log discrepancies over a crepant model are log discrepancies over `X`.** If `G` is a
pull-back of `K_X + B` along a proper birational `p : V ⟶ X` and `G = K_V + B_V` for the divisor
`K_V` of the pulled-back form, every log discrepancy of `(V, B_V)` is one of `(X, B)`. -/
private theorem isLogDiscrepancy_of_isRCartierPullback (hX : IsNormalVariety ℂ sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (p : V ⟶ X)
    [IsProper p] (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p)
    {KV : Divisor V} (hKV : KV.IsCanonicalDivisor (p ≫ sX) n)
    (hKVK : RationalMap.transformDivisor p.toRationalMap KV = K) {BV : RDivisor V}
    (hG : MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor K B)
      (MMP.Flips.logCanonicalDivisor KV BV))
    {m : ℕ} {D : DivisorOver ℂ (p ≫ sX)} {a : ℝ}
    (ha : MMP.Intersection.IsLogDiscrepancy (p ≫ sX) m BV D a) :
    MMP.Intersection.IsLogDiscrepancy sX n B (compDivisorOver p hV hp D) a := by
  classical
  have : AlgebraicGeometry.IsVariety ℂ sX := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : AlgebraicGeometry.IsVariety ℂ (p ≫ sX) := hV.1
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have : LocallyOfFiniteType (p ≫ sX) := hV.1.toLocallyOfFiniteType
  have := hp.isDominant
  have hbij := hp.functionFieldMap_bijective
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX)
    hK.topologicalKrullDim_eq
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : IsProper D.f := ha.2.1
  have : AlgebraicGeometry.IsVariety ℂ (D.f ≫ p ≫ sX) := D.isNormalVariety.1
  have : CompactSpace D.Y := QuasiCompact.compactSpace_of_compactSpace (D.f ≫ p ≫ sX)
  have hbijD := D.isBirationalMorphism.functionFieldMap_bijective
  -- compatible forms: `K = div ω`, `K_V = div (p^*ω)`
  obtain ⟨ω, hω0, hωK, hωKV⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hX hV hp hK hKV hKVK
  have hω'0 : pullbackRationalPluriForms sX p ω ≠ 0 :=
    MMP.Fourfold.SNCWeight.SNCModel.pullbackRationalPluriForms_ne_zero' p hbij hd hω0
  -- the presentation and its pull-backs to `D.Y`
  obtain ⟨M, r, L, L', hL, hD, hpb, hG'⟩ := hG
  have hL'c : ∀ i, (L' i).IsCartier := fun i => (hpb i).2.isCartier (hL i)
  have hBL := fun i => MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp D.f (L' i)
  choose L'' hL'' using fun i => (hL'c i).exists_isPullback (hBL i)
  have hBL₂ := fun i =>
    MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp (D.f ≫ p) (L i)
  have hL''₂ : ∀ i, (L i).IsPullback (D.f ≫ p) (hBL₂ i) (L'' i) := fun i =>
    MMP.ProgramBaseChange.divisor_isPullback_comp rfl (hpb i).2 (hL'' i) _
  -- the log discrepancy of `D` for `(V, B_V)` with these choices
  set a'' : ℝ := 1 + (D.ordPullback (pullbackRationalPluriForms sX p ω) : ℝ) -
    ∑ i, r i * ((L'' i).coeff D.E : ℝ) with ha''
  have hrelV : ∀ Γ : Mori.PrimeDivisor V, (Γ.ordForm (pullbackRationalPluriForms sX p ω) : ℝ) +
      BV.coeff Γ = ∑ i, r i * ((L' i).coeff Γ : ℝ) := fun Γ => by
    have := congrArg (DivisorWithCoeffs.coeff · Γ) hG'
    simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor] at this
    rw [← MMP.Flips.coeff_sum_smul_toRDivisor, ← this, ← hωKV]
    rfl
  have hrelX : ∀ Γ : Mori.PrimeDivisor X, (Γ.ordForm ω : ℝ) + B.coeff Γ =
      ∑ i, r i * ((L i).coeff Γ : ℝ) := fun Γ => by
    have := congrArg (DivisorWithCoeffs.coeff · Γ) hD
    simp only [MMP.Flips.logCanonicalDivisor, DivisorWithCoeffs.coeff_add,
      Divisor.coeff_toRDivisor] at this
    rw [← MMP.Flips.coeff_sum_smul_toRDivisor, ← this, ← hωK]
    rfl
  have hV' : MMP.Intersection.IsLogDiscrepancy (p ≫ sX) n BV D a'' :=
    ⟨hV, inferInstance, pullbackRationalPluriForms sX p ω, hω'0,
      ⟨KV, hKV, fun Γ => by rw [← hωKV]; rfl⟩, M, r, L', L'', hL'c, hrelV,
      fun i => ⟨hBL i, hL'' i⟩, rfl⟩
  have haa : a = a'' := MMP.Threefold.Bridges.IsLogDiscrepancy.unique ha hV'
  have hcomp := MMP.Flips.pullbackRationalPluriForms_comp p D.f hbij hbijD hd ω
  refine ⟨hX, show IsProper (D.f ≫ p) from inferInstance, ω, hω0,
    ⟨K, hK, fun Γ => by rw [← hωK]; rfl⟩, M, r, L, L'', hL, hrelX,
    fun i => ⟨hBL₂ i, hL''₂ i⟩, ?_⟩
  rw [haa, ha'']
  change _ = 1 + (D.E.ordForm (pullbackRationalPluriForms sX (D.f ≫ p) ω) : ℝ) - _
  rw [← hcomp]
  rfl

/-- **A crepant model of a klt pair is klt.** If `K_V + B_V` is the pull-back of `K_X + B` along a
proper birational `p : V ⟶ X`, with `p_* K_V = K_X`, and `(X, B)` is klt, so is `(V, B_V)`. -/
private theorem isRealKltPair_of_isRCartierPullback (hX : IsNormalVariety ℂ sX)
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor sX n) {B : RDivisor X}
    (hklt : IsRealKltPair sX B)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] (p : V ⟶ X)
    [IsProper p] (hV : IsNormalVariety ℂ (p ≫ sX)) (hp : IsBirationalMorphism p)
    {KV : Divisor V} (hKV : KV.IsCanonicalDivisor (p ≫ sX) n)
    (hKVK : RationalMap.transformDivisor p.toRationalMap KV = K) {BV : RDivisor V}
    (hG : MMP.Flips.IsRCartierPullback p (MMP.Flips.logCanonicalDivisor K B)
      (MMP.Flips.logCanonicalDivisor KV BV)) :
    IsRealKltPair (p ≫ sX) BV := by
  have : CompactSpace V := by
    have := hV.1
    exact QuasiCompact.compactSpace_of_compactSpace (p ≫ sX)
  have hlog : ∀ {m : ℕ} {D : DivisorOver ℂ (p ≫ sX)} {a : ℝ},
      MMP.Intersection.IsLogDiscrepancy (p ≫ sX) m BV D a → 0 < a := fun ha =>
    hklt.2.2.2 n _ _ (isLogDiscrepancy_of_isRCartierPullback hX hK p hV hp hKV hKVK hG ha)
  have hRC : RDivisor.IsRCartier (Divisor.toRDivisor KV + BV) := by
    obtain ⟨m, r, L, L', hL, -, hpb, hG'⟩ := hG
    refine ⟨m, r, L', fun j => (hpb j).2.isCartier (hL j), fun Γ => ?_⟩
    have := congrArg (DivisorWithCoeffs.coeff · Γ) hG'
    simp only [MMP.Flips.logCanonicalDivisor] at this
    rw [this, MMP.Flips.coeff_sum_smul_toRDivisor]
  refine ⟨hV, fun P => ?_, ⟨n, KV, hKV, hRC⟩, fun m D a ha => hlog ha⟩
  have := hlog (MMP.Fourfold.PltReference.isLogDiscrepancy_ofPrimeDivisor hV hKV hRC P)
  linarith

/-- **The residue of a plt upper level is klt.** Let `S` be a component of `⌊B⌋` with
`coeff_S C = 0` and `(X, B + λ C)` plt on a `ℚ`-factorial fourfold, `T ⟶ X` the normal stratum of
`S`, `Δ` the residue different of `B` and `C_T` a pull-back of `C`. Then `(T, Δ + λ C_T)` is an
effective klt pair. -/
private theorem isRealKltPair_add_smul_of_isPoincareResidue {X T : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (hQ : IsQFactorial sX) (hdim : topologicalKrullDim X = 4)
    (K : Divisor X) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (B C : RDivisor X) (lam : ℝ)
    (hplt_upper : (∀ P, 0 ≤ (B + lam • C).coeff P ∧ (B + lam • C).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + (B + lam • C)) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX n (B + lam • C) E a → 0 < a)
    (S : MMP.Mori.PrimeDivisor X) (hSB : B.coeff S = 1) (hSC : C.coeff S = 0)
    [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T] [IsNormal T] (ι : T ⟶ X)
    [IsClosedImmersion ι] (hι : Set.range ι.base = (S.support : Set X)) (Δ : RDivisor T)
    (hres : ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι ≫ sX) 3 1, IsPoincareResidue sX ι 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback ι (Divisor.toRDivisor (divisorOfForm τ) + B)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ))
    (CS : RDivisor T) (hCS : MMP.Flips.IsRCartierPullback ι C CS) :
    IsNormalVariety ℂ (ι ≫ sX) ∧ (Δ + lam • CS).IsEffective ∧
      IsRealKltPair (ι ≫ sX) (Δ + lam • CS) := by
  set Δ' : RDivisor X := B + lam • C - Finsupp.single S 1 with hΔ'
  have hBC : Finsupp.single S (1 : ℝ) + Δ' = B + lam • C := add_sub_cancel _ _
  have hcoeff : ∀ Q, Δ'.coeff Q = (B + lam • C).coeff Q -
      (Finsupp.single S (1 : ℝ) : RDivisor X) Q := fun Q => rfl
  have hBCS : (B + lam • C).coeff S = 1 := by
    change B.coeff S + lam * C.coeff S = 1
    rw [hSB, hSC]; ring
  have hadj := MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue sX hQ (n := 3)
    (by rw [hdim]; rfl) S Δ' (fun Q => by
      have h := hplt_upper.1 Q
      rw [hcoeff]
      by_cases hQS : Q = S
      · subst hQS
        rw [Finsupp.single_eq_same, hBCS]
        norm_num
      · rw [Finsupp.single_eq_of_ne hQS, sub_zero]
        exact h)
    (by rw [hcoeff, Finsupp.single_eq_same, hBCS, sub_self])
    (by
      obtain ⟨m, hm⟩ := hK
      exact ⟨m, K, hm, by rw [add_assoc, hBC]; exact hplt_upper.2.1⟩)
    (by rw [hBC]; exact fun m E a hE ha => hplt_upper.2.2 m E a hE ha) ι hι
  obtain ⟨-, hTn, -, hall⟩ := hadj
  obtain ⟨heff, ⟨hTv, ⟨m, KT, hKT, hRC⟩, hpos⟩, -⟩ := hall (Δ + lam • CS)
    (fun τ hτ hτS ρ hρ => by
      have h := MMP.Fourfold.isRCartierPullback_add (hres τ hτ hτS ρ hρ)
        (MMP.Fourfold.isRCartierPullback_smul lam hCS)
      rw [add_assoc, hBC]
      simpa only [add_assoc] using h)
  refine ⟨hTv, heff, hTv, fun P => ?_, ⟨m, KT, hKT, hRC⟩, fun n E a ha => hpos n E a ha⟩
  have := hpos _ _ _ (MMP.Fourfold.PltReference.isLogDiscrepancy_ofPrimeDivisor hTv hKT hRC P)
  linarith

/-- `K_X + D - (K_X - K')` is `K' + D`. -/
private theorem logCanonicalDivisor_sub_sub {X : Scheme.{0}} (K K' : Divisor X) (D : RDivisor X) :
    MMP.Flips.logCanonicalDivisor K D - Divisor.toRDivisor (K - K') =
      Divisor.toRDivisor K' + D := by
  ext Γ
  simp only [MMP.Flips.logCanonicalDivisor, Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply,
    Pi.add_apply]
  change ((K Γ : ℤ) : ℝ) + D Γ - (((K - K') Γ : ℤ) : ℝ) = ((K' Γ : ℤ) : ℝ) + D Γ
  rw [Finsupp.sub_apply]
  push_cast
  ring

/-- **The residue of a nef adjoint is nef.** If `K_X + D` is nef over `π` and `K_T + D_T` is the
residue of `K_X + D` along a normal prime divisor `T ⊆ X`, for every form with a simple pole
along `T`, then `K_T + D_T` is nef over `T ⟶ X ⟶ Zb`, for every canonical divisor `K_T`. -/
private theorem isRelativelyNef_of_isPoincareResidue {X T Zb : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) (hdim : topologicalKrullDim X = 4)
    (K : Divisor X) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (D : RDivisor X) (π : X ⟶ Zb)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π (MMP.Flips.logCanonicalDivisor K D))
    (S : MMP.Mori.PrimeDivisor X) [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [IsNormal T] (ι : T ⟶ X) [IsClosedImmersion ι] (hι : Set.range ι.base = (S.support : Set X))
    (hT : IsNormalVariety ℂ (ι ≫ sX)) (DT : RDivisor T)
    (hres : ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι ≫ sX) 3 1, IsPoincareResidue sX ι 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback ι (Divisor.toRDivisor (divisorOfForm τ) + D)
          (Divisor.toRDivisor (divisorOfForm ρ) + DT))
    (KS : Divisor T) (hKS : ∃ m : ℕ, KS.IsCanonicalDivisor (ι ≫ sX) m) :
    MMP.Flips.IsRelativelyNef ℂ (ι ≫ sX) (ι ≫ π) (MMP.Flips.logCanonicalDivisor KS DT) := by
  have : IsSeparated sX := hX.1.toIsSeparated
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have hdimT := topologicalKrullDim_eq_three sX hdim S ι hι
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimT (by norm_num)
  obtain ⟨τ, hτ0, hτS, ρ, hρ, hρ0⟩ := MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue sX hX
    (n := 3) (by rw [hdim]; rfl) ι hT S hι Q
  have h1 := hres τ hτ0 hτS ρ hρ
  obtain ⟨mK, hmK⟩ := hK
  have hdX : topologicalKrullDim X = ((3 + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  -- `div τ ∼ K` and `div ρ ∼ K_T`
  have hτK : (K - divisorOfForm τ).LinearlyEquivalent 0 := by
    have hK' : K.IsCanonicalDivisor sX (3 + 1) := by
      obtain rfl : mK = 3 + 1 := by
        have := hmK.topologicalKrullDim_eq
        rw [hdX] at this
        exact_mod_cast this.symm
      exact hmK
    obtain ⟨φ, hφ⟩ := (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK' hτ0).symm
    exact ⟨φ, by rw [sub_zero, ← hφ, one_smul]⟩
  have hρK : (divisorOfForm ρ - KS).LinearlyEquivalent 0 := by
    obtain ⟨mS, hmS⟩ := hKS
    have hKS' : KS.IsCanonicalDivisor (ι ≫ sX) 3 := by
      obtain rfl : mS = 3 := by
        have := hmS.topologicalKrullDim_eq
        rw [hdimT] at this
        exact_mod_cast this.symm
      exact hmS
    obtain ⟨φ, hφ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hT hKS' hρ0
    exact ⟨φ, by rw [sub_zero, ← hφ, one_smul]⟩
  -- `div τ + D` is nef over `π`, its pull-back `div ρ + D_T` over `ι ≫ π`
  have h2 : MMP.Flips.IsRelativelyNef ℂ sX π (Divisor.toRDivisor (divisorOfForm τ) + D) := by
    rw [← logCanonicalDivisor_sub_sub K]
    exact MMP.Flips.isRelativelyNef_sub_of_linearlyEquivalent_zero hnef hτK
  have h3 : MMP.Flips.IsRelativelyNef ℂ (ι ≫ sX) (ι ≫ π)
      (Divisor.toRDivisor (divisorOfForm ρ) + DT) :=
    MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 Zb) π (ι ≫ π) ι (by simp) h2 h1
  have h4 := MMP.Flips.isRelativelyNef_sub_of_linearlyEquivalent_zero
    (M := MMP.Flips.logCanonicalDivisor (divisorOfForm ρ) DT) h3 hρK
  rw [logCanonicalDivisor_sub_sub] at h4
  exact h4

end CrepantKlt

/-! ### Existence of the different on a `ℚ`-factorial variety -/

section DifferentExistence

open TopologicalSpace Opposite

open MMP.Mori MMP.Flips MMP.Fourfold MMP.Flips.RationalFunctionsSubmodule

section Algebra

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X] [IsNormal X]
  {k : Type u} [Field k] (π : X ⟶ Spec (.of k)) [LocallyOfFiniteType π] {d : ℕ}
  (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)

include π hd

/-- At the generic point the stalk of `𝒪_X(D)` is all of `K(X)`. -/
private theorem stalkSet_sheaf_of_coheight_eq_zero (D : Divisor X) {η : X}
    (hη : Order.coheight η ≤ 1) (hΓ : ∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint ≠ η) :
    (Divisor.toWeilDivisor D).sheaf.stalkSet η = Set.univ := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have hsurj := structureStalkToRationalFunctionsStalk_surjective
    (coheight_eq_zero_of_forall_ne hη hΓ)
  obtain ⟨L, hL⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf π hd (Divisor.toWeilDivisor D)
  rw [WeilDivisor.stalkSet_sheaf_of_coeff_eq_zero hL hη (fun Γ hΓ' => absurd hΓ' (hΓ Γ))]
  ext g
  simp only [Set.mem_range, Set.mem_univ, iff_true, Units.val_one, one_mul]
  exact hsurj g

/-- **A saturated subsheaf with the orders of `D` is `𝒪_X(D)`.** On an integral Noetherian
normal scheme of finite type and pure dimension over a field, a saturated `F ⊆ K(X)` which is
`K(X)` at the generic point and has order `-d_Γ` along every prime divisor `Γ` is `𝒪_X(D)`. -/
private theorem eq_sheaf_of_hasOrderAt {F : RationalFunctionsSubmodule X} (hF : F.IsSaturated)
    (D : Divisor X)
    (hord : ∀ Γ : WeilDivisorPrime X, HasOrderAt F Γ (-(Divisor.toWeilDivisor D Γ)))
    (hgen : ∀ η : X, Order.coheight η ≤ 1 → (∀ Γ : WeilDivisorPrime X, Γ.1.genericPoint ≠ η) →
      F.stalkSet η = Set.univ) :
    F = (Divisor.toWeilDivisor D).sheaf := by
  refine RationalFunctionsSubmodule.eq_of_stalkSet_eq hF (WeilDivisor.isSaturated_sheaf _)
    fun η hη => ?_
  by_cases hΓ : ∃ Γ : WeilDivisorPrime X, Γ.1.genericPoint = η
  · obtain ⟨Γ, rfl⟩ := hΓ
    have h1 := hord Γ
    have h2 := WeilDivisor.hasOrderAt_sheaf π hd (Divisor.toWeilDivisor D) Γ
    rw [hasOrderAt_iff_stalk_eq] at h1 h2
    ext g
    rw [← mem_stalk, ← mem_stalk, h1, h2]
  · push Not at hΓ
    rw [hgen η hη hΓ, stalkSet_sheaf_of_coheight_eq_zero π hd D hη hΓ]

/-- **`𝒪_X(D₁) · 𝒪_X(D₂) = 𝒪_X(D₁ + D₂)`** on a normal scheme, for arbitrary divisors. -/
private theorem sheaf_mul_sheaf (D₁ D₂ : Divisor X) :
    (Divisor.toWeilDivisor D₁).sheaf.mul (Divisor.toWeilDivisor D₂).sheaf =
      (Divisor.toWeilDivisor (D₁ + D₂)).sheaf := by
  refine eq_sheaf_of_hasOrderAt π hd (isSaturated_saturation _) _ (fun Γ => ?_) fun η hη hΓ => ?_
  · have h := (WeilDivisor.hasOrderAt_sheaf π hd (Divisor.toWeilDivisor D₁) Γ).mul
      (WeilDivisor.hasOrderAt_sheaf π hd (Divisor.toWeilDivisor D₂) Γ)
    have e : -(Divisor.toWeilDivisor (D₁ + D₂) Γ) =
        -(Divisor.toWeilDivisor D₁ Γ) + -(Divisor.toWeilDivisor D₂ Γ) := by
      rw [Divisor.toWeilDivisor_apply, Divisor.toWeilDivisor_apply, Divisor.toWeilDivisor_apply,
        DivisorWithCoeffs.coeff_add]
      ring
    rw [e]
    exact h
  · have h1 : ((Divisor.toWeilDivisor D₁).sheaf.mul (Divisor.toWeilDivisor D₂).sheaf).stalk η =
        ⊤ := by
      change (mulImage _ _).saturation.stalk η = ⊤
      rw [stalk_saturation _ hη, stalk_mulImage]
      have e : ∀ D : Divisor X, (Divisor.toWeilDivisor D).sheaf.stalk η = ⊤ := fun D => by
        ext g; rw [mem_stalk, stalkSet_sheaf_of_coheight_eq_zero π hd D hη hΓ]; simp
      rw [e, e]
      refine eq_top_iff.mpr fun g _ => ?_
      simpa using Submodule.mul_mem_mul (Submodule.mem_top (x := g))
        (Submodule.mem_top (x := (1 : (rationalFunctionsPresheaf X).stalk η)))
    ext g
    change g ∈ ((Divisor.toWeilDivisor D₁).sheaf.mul (Divisor.toWeilDivisor D₂).sheaf).stalk η ↔ _
    rw [h1]
    simp

/-- `𝒪_X(D)^[n] = 𝒪_X(nD)` for `n ≥ 1`. -/
private theorem sheaf_reflexivePowNat (D : Divisor X) {n : ℕ} (hn : 1 ≤ n) :
    (Divisor.toWeilDivisor D).sheaf.reflexivePowNat n =
      (Divisor.toWeilDivisor ((n : ℤ) • D)).sheaf := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [Divisor.reflexivePowNat_sheaf_toWeilDivisor π hd D m, natCast_zsmul]

/-- **Sums of classes of `𝒪(D)`.** If `n₃ (n₂ D₁ + n₁ D₂) = n₁ n₂ D₃`, then
`(1/n₁)𝒪(D₁) + (1/n₂)𝒪(D₂) = (1/n₃)𝒪(D₃)` in `WSh(X)_ℚ`. -/
private theorem isSum_divNat_of_sheaf {L₁ L₂ L₃ : WeilDivisorialSubsheaf X} {D₁ D₂ D₃ : Divisor X}
    (hL₁ : L₁.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D₁).sheaf)
    (hL₂ : L₂.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D₂).sheaf)
    (hL₃ : L₃.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D₃).sheaf) {n₁ n₂ n₃ : ℕ+}
    (h : ((n₃ : ℕ) : ℤ) • (((n₂ : ℕ) : ℤ) • D₁ + ((n₁ : ℕ) : ℤ) • D₂) =
      (((n₁ : ℕ) * (n₂ : ℕ) : ℕ) : ℤ) • D₃) :
    QWeilDivisorialSheaf.IsSum (L₁.divNat n₁) (L₂.divNat n₂) (L₃.divNat n₃) := by
  refine ⟨L₁, L₂, L₃, n₁, n₂, n₃, rfl, rfl, rfl, 1, le_rfl, ?_⟩
  simp only [one_mul, RationalFunctionsSubmodule.reflexivePow_natCast]
  rw [hL₁, hL₂, hL₃, sheaf_reflexivePowNat π hd D₁ n₂.pos, sheaf_reflexivePowNat π hd D₂ n₁.pos,
    sheaf_mul_sheaf π hd, sheaf_reflexivePowNat π hd _ n₃.pos,
    sheaf_reflexivePowNat π hd D₃ (Nat.mul_pos n₁.pos n₂.pos), h]

end Algebra

open MMP.Mori MMP.Flips MMP.Fourfold

section Cartier

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]

/-- The section `φ|_U` of `K(X)` over `U` of a rational function. -/
private def secOf (U : X.Opens) (φ : RationalFunctions X) :
    ToType ((rationalFunctionsPresheaf X).obj (op U)) := fun Z => φ Z.1

private theorem secOf_mem_sheaf {D : Divisor X} {U : X.Opens} {φ : (RationalFunctions X)ˣ}
    (hφ : D.IsLocalEquation U φ) :
    secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ∈
      (Divisor.toWeilDivisor D).sheaf.sections U := by
  rw [sheaf_toWeilDivisor_sections]
  intro E hE
  refine Or.inr ?_
  change WithZero.exp _ ≤ E.valuation (((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)
    E.component)
  rw [PrimeDivisor.valuation_component, PrimeDivisor.ord_inv, hφ E hE]

/-- On a Cartier divisor with local equation `φ` on `U`, the stalk of `𝒪_X(D)` at `x ∈ U` is
`φ⁻¹ 𝒪_{X,x}`. -/
private theorem stalkSet_sheaf_of_isLocalEquation {D : Divisor X} {U : X.Opens}
    {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) {x : X} (hx : x ∈ U) :
    (Divisor.toWeilDivisor D).sheaf.stalkSet x = Set.range fun a : X.presheaf.stalk x =>
      (rationalFunctionsPresheaf X).germ U x hx
          (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) *
        (structureStalkToRationalFunctionsStalk X x).hom a := by
  have hsub := MMP.Flips.subsingleton_irreducibleComponents (X := X)
  obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  ext g
  constructor
  · rintro ⟨W, hxW, s, hs, rfl⟩
    have hZW : componentGenericPoint X Z ∈ W := componentGenericPoint_mem_of_nonempty Z ⟨x, hxW⟩
    by_cases h0 : s ⟨Z, hZW⟩ = 0
    · refine ⟨0, ?_⟩
      apply rationalFunctionsStalkEval_injective x Z
      simp only [map_mul, map_zero, mul_zero]
      rw [rationalFunctionsStalkEval_germ]
      exact h0.symm
    obtain ⟨χ, hχ⟩ := exists_units_eq_of_ne_zero ⟨x, hxW⟩ s fun Z' => by
      obtain ⟨Z', h'⟩ := Z'
      obtain rfl : Z' = Z := Subsingleton.elim _ _
      exact h0
    have hxZ : x ∈ Z.1 := by rw [irreducibleComponents_val_eq_univ Z]; trivial
    obtain ⟨r, hr⟩ := exists_stalk_eq_of_forall_zero_le_ord hxZ (χ * φ) fun E hxE => by
      rw [PrimeDivisor.ord_mul, ← hφ E ⟨x, hxE, hx⟩]
      have hsE := (sheaf_toWeilDivisor_sections D W ▸ hs) E ⟨x, hxE, hxW⟩
      obtain rfl : E.component = Z := Subsingleton.elim _ _
      rcases hsE with h | h
      · exact absurd h h0
      · rw [← hχ, PrimeDivisor.valuation_component, WithZero.exp_le_exp] at h
        omega
    refine ⟨r, ?_⟩
    apply rationalFunctionsStalkEval_injective x Z
    rw [map_mul, rationalFunctionsStalkEval_germ, rationalFunctionsStalkEval_structure,
      rationalFunctionsStalkEval_germ]
    change ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) Z *
      (stalkToRationalFunctions X hxZ).hom r = _
    have key : ((φ⁻¹ * (χ * φ) : (RationalFunctions X)ˣ) : RationalFunctions X) = χ := by
      rw [mul_comm χ φ, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hr, ← hχ Z hZW, ← key]
    rfl
  · rintro ⟨a, rfl⟩
    obtain ⟨W, hxW, a', rfl⟩ := X.presheaf.exists_germ_eq a
    have hx' : x ∈ U ⊓ W := ⟨hx, hxW⟩
    refine ⟨U ⊓ W, hx', X.presheaf.map (homOfLE inf_le_right).op a' •
      (rationalFunctionsPresheaf X).map (homOfLE inf_le_left).op
        (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)),
      Submodule.smul_mem _ _ ((Divisor.toWeilDivisor D).sheaf.map_mem _ (secOf_mem_sheaf hφ)), ?_⟩
    rw [germ_smul_rationalFunctions, TopCat.Presheaf.germ_res_apply,
      TopCat.Presheaf.germ_res_apply, mul_comm]

omit [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- `i^w_C 𝓕` is saturated: its stalk conditions are imposed at the points of codimension at most
one only. -/
private theorem isSaturated_weilRestrictionCartier {T : Scheme.{u}} (j : T ⟶ X)
    (F : RationalFunctionsSubmodule X) : (weilRestrictionCartier j F).IsSaturated := by
  refine RationalFunctionsSubmodule.ext fun V =>
    le_antisymm ((weilRestrictionCartier j F).sections_le_saturation V) fun s hs => ?_
  intro P hP hc
  obtain ⟨W, hPW, t, ht, hts⟩ := hs P hP hc
  rw [← hts]
  exact ht P hPW hc

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem secOf_mul (U : X.Opens) (φ ψ : RationalFunctions X) :
    secOf U (φ * ψ) = secOf U φ * secOf U ψ := rfl

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem secOf_one (U : X.Opens) : secOf U (1 : RationalFunctions X) = 1 := rfl

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem map_secOf {U V : X.Opens} (i : V ⟶ U) (φ : RationalFunctions X) :
    (rationalFunctionsPresheaf X).map i.op (secOf U φ) = secOf V φ := rfl

/-- The germ at `x ∈ U` of a unit `φ` of `K(X)`, as a unit of `K(X)_x`. -/
private noncomputable def germUnit {U : X.Opens} {x : X} (hx : x ∈ U) (φ : (RationalFunctions X)ˣ) :
    ((rationalFunctionsPresheaf X).stalk x)ˣ where
  val := (rationalFunctionsPresheaf X).germ U x hx (secOf U (φ : RationalFunctions X))
  inv := (rationalFunctionsPresheaf X).germ U x hx (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) :
    RationalFunctions X))
  val_inv := by
    rw [← map_mul, ← secOf_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, secOf_one,
      map_one]
  inv_val := by
    rw [← map_mul, ← secOf_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, secOf_one,
      map_one]

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
private theorem val_germUnit {U : X.Opens} {x : X} (hx : x ∈ U) (φ : (RationalFunctions X)ˣ) :
    (germUnit hx φ : (rationalFunctionsPresheaf X).stalk x) =
      (rationalFunctionsPresheaf X).germ U x hx (secOf U (φ : RationalFunctions X)) := rfl

attribute [local simp] val_germUnit

section Restriction

variable {T : Scheme.{u}} [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T] [CompactSpace T]

open Classical in
/-- The pull-back `j^*φ ∈ K(T)^×` of a local equation `φ` of `D` on `U`, for `T` integral meeting
`j⁻¹ U`. -/
private noncomputable def pullbackLocalUnit (j : T ⟶ X) {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) :
    (RationalFunctions T)ˣ :=
  (RationalFunctions.unitsEquiv T).symm fun Z =>
    if hZ : j (componentGenericPoint T Z) ∈ U then pullbackComponent j hB hφ Z hZ else 1

open Classical in
private theorem isLocalEquation_pullbackLocalUnit (j : T ⟶ X) {D : Divisor X} (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) :
    (D.pullback hDc hB).IsLocalEquation (j ⁻¹ᵁ U) (pullbackLocalUnit j hB hφ) := by
  intro E hE
  rw [Divisor.isPullback_pullback hDc hB U φ hφ E hE, PrimeDivisor.ord_eq_ordUnit]
  congr 1
  ext
  change _ = (if hZ : j (componentGenericPoint T E.component) ∈ U then
    pullbackComponent j hB hφ E.component hZ else 1).val
  rw [dif_pos (E.map_componentGenericPoint_mem j hE)]

omit [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] in
/-- If `φ_ξ` is the image of a unit `a` of `𝒪_{X,ξ}`, then the germ of `φ⁻¹|_U` at `ξ` is the
image of `a⁻¹`. -/
private theorem structure_inv_eq_germ_secOf_inv {U : X.Opens} {φ : (RationalFunctions X)ˣ} {ξ : X}
    (hξU : ξ ∈ U) {ZX : irreducibleComponents X} (hξ : ξ ∈ ZX.1) (a : (X.presheaf.stalk ξ)ˣ)
    (ha : (stalkToRationalFunctions X hξ).hom a = (φ : RationalFunctions X) ZX) :
    (structureStalkToRationalFunctionsStalk X ξ).hom ((a⁻¹ : (X.presheaf.stalk ξ)ˣ) :
        X.presheaf.stalk ξ) =
      (rationalFunctionsPresheaf X).germ U ξ hξU
        (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) := by
  apply rationalFunctionsStalkEval_injective _ ZX
  rw [rationalFunctionsStalkEval_structure, rationalFunctionsStalkEval_germ]
  change (stalkToRationalFunctions X hξ).hom _ = ((φ⁻¹ : (RationalFunctions X)ˣ) :
    RationalFunctions X) ZX
  have h1 : (stalkToRationalFunctions X hξ).hom ((a⁻¹ : (X.presheaf.stalk ξ)ˣ) :
      X.presheaf.stalk ξ) * (stalkToRationalFunctions X hξ).hom (a : X.presheaf.stalk ξ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have h2 : ((φ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX *
      ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X) ZX = 1 := by
    rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]
  rw [ha] at h1
  exact left_inv_eq_right_inv h1 h2

/-- `φ⁻¹|_U` is regular along `j` when `j` maps the generic point of `T` into `U` off `Supp D`. -/
private theorem isRegularAlong_secOf_inv (j : T ⟶ X) {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ) :
    IsRegularAlong j (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) := by
  obtain ⟨ZX⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  intro Z hZU
  have hξ : j (componentGenericPoint T Z) ∈ ZX.1 := by
    rw [irreducibleComponents_val_eq_univ ZX]; trivial
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZU (hB Z) hξ
  exact ⟨_, structure_inv_eq_germ_secOf_inv hZU hξ a ha⟩

open Classical in
/-- The restriction of `φ⁻¹|_U` along `j` is `(j^*φ)⁻¹|_{j⁻¹U}`. -/
private theorem restrictAlong_secOf_inv (j : T ⟶ X) {D : Divisor X}
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp)
    {U : X.Opens} {φ : (RationalFunctions X)ˣ} (hφ : D.IsLocalEquation U φ)
    (hf : IsRegularAlong j (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X))) :
    restrictAlong j (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)) hf =
      secOf (j ⁻¹ᵁ U) (((pullbackLocalUnit j hB hφ)⁻¹ : (RationalFunctions T)ˣ) :
        RationalFunctions T) := by
  obtain ⟨ZX⟩ : Nonempty (irreducibleComponents X) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  funext Z
  have hZU : j (componentGenericPoint T Z.1) ∈ U := Z.2
  have hξ : j (componentGenericPoint T Z.1) ∈ ZX.1 := by
    rw [irreducibleComponents_val_eq_univ ZX]; trivial
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZU (hB Z.1) hξ
  rw [restrictAlong_apply_of_germ_eq j hf Z _ (structure_inv_eq_germ_secOf_inv hZU hξ a ha)]
  change _ = (((RationalFunctions.unitsEquiv T).symm fun Z =>
    if hZ : j (componentGenericPoint T Z) ∈ U then pullbackComponent j hB hφ Z hZ else 1)⁻¹ :
      (RationalFunctions T)ˣ).val Z.1
  rw [← map_inv]
  change _ = ((fun Z => if hZ : j (componentGenericPoint T Z) ∈ U then
    pullbackComponent j hB hφ Z hZ else 1)⁻¹ Z.1).val
  rw [Pi.inv_apply, dif_pos hZU, pullbackComponent_eq hB hφ hZU hξ a ha, ← map_inv]
  rfl

/-- **The restriction `i^w_C 𝒪_X(D)` of a Cartier divisor is `𝒪_T(j^*D)`.** -/
private theorem weilRestrictionCartier_sheaf_toWeilDivisor (j : T ⟶ X) {D : Divisor X}
    (hDc : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp) :
    weilRestrictionCartier j (Divisor.toWeilDivisor D).sheaf =
      (Divisor.toWeilDivisor (D.pullback hDc hB)).sheaf := by
  refine RationalFunctionsSubmodule.eq_of_stalkSet_eq (isSaturated_weilRestrictionCartier j _)
    (WeilDivisor.isSaturated_sheaf _) fun P hc => ?_
  obtain ⟨U, hU, φ, hφ⟩ := hDc (j P)
  have hf := isRegularAlong_secOf_inv j hB hφ
  let f₀ : ((rationalFunctionsPresheaf X).stalk (j P))ˣ :=
    ⟨(rationalFunctionsPresheaf X).germ U (j P) hU
        (secOf U ((φ⁻¹ : (RationalFunctions X)ˣ) : RationalFunctions X)),
      (rationalFunctionsPresheaf X).germ U (j P) hU
        (secOf U ((φ : (RationalFunctions X)ˣ) : RationalFunctions X)),
      by rw [← map_mul]; convert map_one ((rationalFunctionsPresheaf X).germ U (j P) hU).hom
         using 2; funext Z; exact congrFun (congrArg Units.val (inv_mul_cancel φ)) Z.1,
      by rw [← map_mul]; convert map_one ((rationalFunctionsPresheaf X).germ U (j P) hU).hom
         using 2; funext Z; exact congrFun (congrArg Units.val (mul_inv_cancel φ)) Z.1⟩
  have hP : j P ∈ U := hU
  rw [stalkSet_weilRestrictionCartier j (secOf_mem_sheaf hφ) hf hP hc f₀ rfl
      (stalkSet_sheaf_of_isLocalEquation hφ hU),
    stalkSet_sheaf_of_isLocalEquation (isLocalEquation_pullbackLocalUnit j hDc hB hφ)
      (show P ∈ j ⁻¹ᵁ U from hU), restrictAlong_secOf_inv j hB hφ hf]

end Restriction

/-- A Cartier divisor `D` has `𝒪_X(D)` invertible at every point. -/
private theorem isInvertibleAt_sheaf {D : Divisor X} (hDc : D.IsCartier) (x : X) :
    (Divisor.toWeilDivisor D).sheaf.IsInvertibleAt x := by
  obtain ⟨U, hU, φ, hφ⟩ := hDc x
  exact ⟨germUnit hU φ⁻¹, stalkSet_sheaf_of_isLocalEquation hφ hU⟩

end Cartier

section Gorenstein

open MMP.Mori MMP.Flips MMP.Fourfold

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- On a normal locally Noetherian integral scheme the local rings at the points of codimension at
most one are regular (a field or a discrete valuation ring), hence Gorenstein. -/
private theorem isGorensteinLocalRing_stalk (η : X) (hη : Order.coheight η ≤ 1) :
    ∃ _ : IsNoetherianRing (X.presheaf.stalk η),
      Dualizing.IsGorensteinLocalRing (X.presheaf.stalk η) := by
  refine ⟨inferInstance, ?_⟩
  suffices IsRegularLocalRing (X.presheaf.stalk η) from
    Dualizing.IsRegularLocalRing.isGorensteinLocalRing _
  rcases le_iff_lt_or_eq.mp hη with h | h
  · have h0 : Order.coheight η = 0 := ENat.lt_one_iff_eq_zero.mp h
    obtain ⟨Z⟩ : Nonempty (irreducibleComponents X) :=
      ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
    have hmax : IsMax η := Order.coheight_eq_zero.mp h0
    have hsp : η ⤳ componentGenericPoint X Z :=
      Scheme.le_iff_specializes.mp (hmax (Scheme.le_iff_specializes.mpr
        (componentGenericPoint_specializes Z η)))
    have he : η = genericPoint X := by
      rw [← componentGenericPoint_eq_genericPoint (Z := Z)]
      exact (hsp.antisymm (componentGenericPoint_specializes Z η)).eq
    subst he
    change IsRegularLocalRing X.functionField
    infer_instance
  · have hD := MMP.Mori.PrimeDivisor.isDiscreteValuationRing_localRing
      (AlgebraicGeometry.PrimeDivisor.ofCoheightOne η h)
    have key : ∀ y : X, y = η → IsDiscreteValuationRing (X.presheaf.stalk y) →
        IsRegularLocalRing (X.presheaf.stalk η) := by
      rintro y rfl _; infer_instance
    exact key _ (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne η h) hD

end Gorenstein

section Different

open MMP.Mori MMP.Flips MMP.Fourfold

variable {X T : Scheme.{0}} [IsIntegral X] [IsNoetherian X] [IsNormal X]
  [IsIntegral T] [IsNoetherian T] [IsNormal T]

/-- A closed immersion onto a prime divisor `P` maps the generic point of `T` to that of `P`. -/
private theorem map_componentGenericPoint_eq (j : T ⟶ X) [IsClosedImmersion j]
    (P : MMP.Mori.PrimeDivisor X) (hj : Set.range j.base = (P.support : Set X))
    (Z : irreducibleComponents T) : j (componentGenericPoint T Z) = P.genericPoint := by
  rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint]
  exact MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hj

/-- **`𝒪_X(D)` has good support along `T`** for a `ℚ`-Cartier divisor `D` with `coeff_P D = 0`,
`T` mapping onto `P`. -/
private theorem mem_goodSupportSubsheaves_of_sheaf {k : Type} [Field k] (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] {d : ℕ} (hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d)
    (j : T ⟶ X) [IsClosedImmersion j] (P : MMP.Mori.PrimeDivisor X)
    (hj : Set.range j.base = (P.support : Set X)) {D : Divisor X} (hDP : D.coeff P = 0) {m : ℕ}
    (hm : 0 < m) (hDc : ((m : ℤ) • D).IsCartier) {L : WeilDivisorialSubsheaf X}
    (hL : L.toRationalFunctionsSubmodule = (Divisor.toWeilDivisor D).sheaf) :
    L ∈ goodSupportSubsheaves (closedRange j) := by
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  obtain ⟨ZT⟩ : Nonempty (irreducibleComponents T) :=
    ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
  refine ⟨fun Q _ => ⟨m, hm, ?_⟩, fun ξ hξ hsupp => hsupp ?_⟩
  · rw [RationalFunctionsSubmodule.reflexivePow_natCast, hL,
      sheaf_reflexivePowNat sX hd D hm]
    exact isInvertibleAt_sheaf hDc Q.1
  · have hgen : IsGenericPoint (j (componentGenericPoint T ZT)) (closedRange j : Set X) := by
      have h := (isGenericPoint_componentGenericPoint T ZT).image j.base.hom.continuous
      rw [irreducibleComponents_val_eq_univ ZT, Set.image_univ,
        j.isClosedEmbedding.isClosed_range.closure_eq] at h
      exact h
    have hcl : IsGenericPoint ξ (closedRange j : Set X) :=
      hξ.eq_of_subset ⟨le_rfl, hgen.isIrreducible⟩ hξ.prop.1
    have hξj : ξ = P.genericPoint := (hcl.eq hgen).trans (map_componentGenericPoint_eq j P hj ZT)
    subst hξj
    have hcoh := (MMP.Mori.PrimeDivisor.coheight_genericPoint P).le
    change L.toRationalFunctionsSubmodule.stalkSet _ = _
    rw [RationalFunctionsSubmodule.stalkSet_saturation hcoh, RationalFunctionsSubmodule.stalkSet_unit,
      hL, WeilDivisor.stalkSet_sheaf_of_coeff_eq_zero hL hcoh fun Γ hΓ => by
        rw [Divisor.toWeilDivisor_apply]
        obtain rfl : Γ.1 = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective hΓ
        exact hDP]
    ext g
    simp

end Different

section Embedded

open MMP.Mori MMP.Flips MMP.Fourfold

variable {X T : Scheme.{0}} [IsIntegral X] [IsNoetherian X] [IsNormal X]
  [IsIntegral T] [IsNoetherian T] [IsNormal T]

/-- **The embedded dualizing sheaf is `𝒪_T(div Res_T τ₀)`.** If `ω_X(T) = 𝒪_X(div τ₀ + P)` for a
rational top form `τ₀` with a simple pole along `P` and residue `ρ₀`, then
`Ω_T = 𝒪_T(div ρ₀)`. -/
private theorem embeddedDualizingSheaf_eq_sheaf_divisorOfForm (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (hX : IsNormalVariety ℂ sX) {n : ℕ}
    (hdim : topologicalKrullDim X = n + 1)
    (hdT : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = n)
    (j : T ⟶ X) [IsClosedImmersion j] (hT : IsNormalVariety ℂ (j ≫ sX))
    (P : MMP.Mori.PrimeDivisor X) (hP : Set.range j.base = (P.support : Set X))
    {ωXS : WeilDivisorialSubsheaf X} (hL : ωXS ∈ goodSupportSubsheaves (closedRange j))
    {τ₀ : RationalPluriForms sX (n + 1) 1} (hτ₀0 : τ₀ ≠ 0) (hτ₀P : P.ordForm τ₀ = -1)
    (hωXS : ωXS.toRationalFunctionsSubmodule =
      (Divisor.toWeilDivisor (divisorOfForm τ₀ + Finsupp.single P 1)).sheaf)
    {ρ₀ : RationalPluriForms (j ≫ sX) n 1} (hρ₀0 : ρ₀ ≠ 0)
    (hρ₀ : IsPoincareResidue sX j n 1 τ₀ ρ₀) :
    haveI : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
    embeddedDualizingSheaf j ωXS = (Divisor.toWeilDivisor (divisorOfForm ρ₀)).sheaf := by
  haveI : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have : IsLocallyNoetherian T := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace T := IsNoetherian.toCompactSpace
  have hjT := MMP.CyclicChartDifferent.Aux.map_genericPoint_eq j P hP
  have hS : ∀ Z : irreducibleComponents T, Order.coheight (j.base (componentGenericPoint T Z)) ≤ 1 :=
    fun Z => by
      rw [show j.base (componentGenericPoint T Z) = P.genericPoint from
        map_componentGenericPoint_eq j P hP Z]
      exact (MMP.Mori.PrimeDivisor.coheight_genericPoint P).le
  refine eq_sheaf_of_hasOrderAt (j ≫ sX) hdT (isSaturated_saturation _) _ (fun Γ => ?_)
    fun η hη hΓ => ?_
  · have h := hasOrderAt_embeddedDualizingSheaf sX hX hdim j hT P hP hjT hS hL hωXS hτ₀0
      (fun E => rfl) hτ₀P hρ₀0 hρ₀ Γ.1
    have e1 : PrimeDivisor.toWeilDivisorPrime Γ.1 = Γ := Subtype.ext rfl
    rw [e1] at h
    rw [Divisor.toWeilDivisor_apply, coeff_divisorOfForm]
    exact h
  · obtain ⟨Z⟩ : Nonempty (irreducibleComponents T) :=
      ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
    have h0 := coheight_eq_zero_of_forall_ne hη hΓ
    have hηZ : η = componentGenericPoint T Z := by
      have hmax : IsMax η := Order.coheight_eq_zero.mp h0
      have hsp : η ⤳ componentGenericPoint T Z :=
        Scheme.le_iff_specializes.mp (hmax (Scheme.le_iff_specializes.mpr
          (componentGenericPoint_specializes Z η)))
      exact (hsp.antisymm (componentGenericPoint_specializes Z η)).eq
    subst hηZ
    -- a section `l` of `ω_X(T)` near `x = j(η_T)` with germ `1`
    set x := j.base (componentGenericPoint T Z) with hx
    have hxP : x = P.genericPoint := map_componentGenericPoint_eq j P hP Z
    have hstalk := WeilDivisor.stalkSet_sheaf_of_coeff_eq_zero hωXS (hS Z) fun Γ hΓ => by
      rw [Divisor.toWeilDivisor_apply]
      obtain rfl : Γ.1 = P := AlgebraicGeometry.PrimeDivisor.genericPoint_injective
        (hΓ.trans hxP)
      rw [DivisorWithCoeffs.coeff_add, coeff_divisorOfForm, hτ₀P,
        DivisorWithCoeffs.coeff_single_self]
      norm_num
    have h1 : (1 : (rationalFunctionsPresheaf X).stalk x) ∈
        ωXS.toRationalFunctionsSubmodule.stalkSet x := by
      rw [hωXS, hstalk]
      exact ⟨1, by simp⟩
    obtain ⟨W, hxW, l, hl, hgerm⟩ := h1
    have hlreg : IsRegularAlong j l := isRegularAlong_of_mem hS hL hl
    have hres : (rationalFunctionsPresheaf T).germ (j ⁻¹ᵁ W) (componentGenericPoint T Z) hxW
        (restrictAlong j l hlreg) = 1 := by
      apply rationalFunctionsStalkEval_injective _ Z
      rw [rationalFunctionsStalkEval_germ _ _ (U := j ⁻¹ᵁ W) hxW, map_one,
        restrictAlong_apply_of_germ_eq j hlreg ⟨Z, hxW⟩ 1 (by rw [map_one]; exact hgerm.symm),
        map_one]
    have hsurj := structureStalkToRationalFunctionsStalk_surjective h0
    rw [RationalFunctionsSubmodule.stalkSet_saturation hη]
    refine Set.eq_univ_of_forall fun g => ?_
    obtain ⟨a, rfl⟩ := hsurj g
    have := germ_restrictAlong_mul_mem_stalkSet_restrictionImage j hl hlreg hxW a
    rwa [hres, one_mul] at this

end Embedded

section Existence

open MMP.Mori MMP.Flips MMP.Fourfold

/-- **Existence of an adjunction step on a `ℚ`-factorial variety** (FA 16.5, 16.6). Let `X` be a
`ℚ`-factorial proper normal complex variety of dimension `n + 1`, `j : T ⟶ X` a closed immersion
of a normal variety of dimension `n` onto a prime divisor `P`, and `B` a `ℚ`-divisor with
coefficients in `[0, 1]` and `coeff_P B = 1`. Then the different `Diff_T(B - P)` exists: there is
`B_T` with `(T, B_T)` an adjunction step of `(X, B)`. -/
private theorem exists_isAdjunctionStep_of_isQFactorial {X T : Scheme.{0}} [IsIntegral X]
    [IsNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [IsProper sX]
    (hQ : IsQFactorial sX) {n : ℕ} (hdim : topologicalKrullDim X = n + 1) [IsIntegral T]
    [IsNoetherian T] [IsNormal T] (hdimT : topologicalKrullDim T = n) (j : T ⟶ X)
    [IsClosedImmersion j] (P : MMP.Mori.PrimeDivisor X)
    (hj : Set.range j.base = (P.support : Set X)) (hT : IsNormalVariety ℂ (j ≫ sX))
    (Q₀ : MMP.Mori.PrimeDivisor T) (BV : QDivisor X) (h0 : ∀ Q, 0 ≤ BV.coeff Q)
    (hle : ∀ Q, BV.coeff Q ≤ 1) (hP : BV.coeff P = 1) :
    ∃ BT : QDivisor T, IsAdjunctionStep sX BV j BT := by
  classical
  have : IsLocallyNoetherian X := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace X := IsNoetherian.toCompactSpace
  have : IsLocallyNoetherian T := IsNoetherian.toIsLocallyNoetherian
  have : CompactSpace T := IsNoetherian.toCompactSpace
  have hX : IsNormalVariety ℂ sX := hQ.1
  haveI : LocallyOfFiniteType (j ≫ sX) := hT.1.toLocallyOfFiniteType
  have hdimX : ∀ {Y : Scheme.{0}} [IrreducibleSpace Y] {e : ℕ}, topologicalKrullDim Y = e →
      ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z = e := by
    intro Y _ e he Z hZ
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
    subst hZ
    rw [← he]
    exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph
  have hd : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (n + 1 : ℕ) :=
    hdimX (by rw [hdim]; push_cast; rfl)
  have hdT : ∀ Z ∈ irreducibleComponents T, topologicalKrullDim Z = n := hdimX hdimT
  have hjη := map_componentGenericPoint_eq j P hj
  have hcod : ∀ Z : irreducibleComponents T, Order.coheight (j (componentGenericPoint T Z)) = 1 :=
    fun Z => by rw [hjη]; exact P.coheight_genericPoint
  have hnotsupp : ∀ (D : Divisor X), D.coeff P = 0 →
      ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp := by
    intro D hD Z h
    rw [hjη] at h
    obtain ⟨E, hE, hPE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
    obtain rfl := eq_of_genericPoint_mem_primeDivisor_support hPE
    exact hE hD
  -- a dualizing sheaf `ω₁ = 𝒪_X(K₁)`
  let ω₀ := (Scheme.Modules.restrictFunctor (𝟙 X)).obj
    (Stacks.Duality.dualizingModuleOverField sX ((n + 1 : ℕ) : ℤ))
  have hω₀ : IsDualizingSheaf sX (n + 1) ω₀ :=
    ⟨hd, X, 𝟙 X, inferInstance, sX, inferInstance, Category.id_comp _, ⟨Iso.refl _⟩⟩
  obtain ⟨-, φ, hφ⟩ := hω₀.isCoherent_exists_injective
  obtain ⟨L₀, hL₀⟩ := (hω₀.exists_weilDivisorialSubsheaf_iff φ hφ).mpr
    fun η hη => isGorensteinLocalRing_stalk η hη
  have hω₁ : IsDualizingSheaf sX (n + 1) L₀.toModules :=
    hω₀.of_iso (isoImageSubmodule φ hφ ≪≫ eqToIso (by rw [hL₀]))
  obtain ⟨-, -, K₁, hK₁, -, hL₀K⟩ := IsDualizingSheaf.exists_eq_sheaf_toWeilDivisor hX hω₁
  -- a form `τ₀` with a simple pole along `P`, its residue `ρ₀`, and `ω = 𝒪_X(div τ₀)`
  obtain ⟨τ₀, hτ₀0, hτ₀P, ρ₀, hρ₀, hρ₀0⟩ :=
    exists_ordForm_eq_neg_one_isPoincareResidue sX hX hdim j hT P hj Q₀
  set K₀ : Divisor X := divisorOfForm τ₀ with hK₀
  have hlin : K₁.LinearlyEquivalent K₀ := by
    have h := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK₁ hτ₀0
    rw [one_smul] at h
    exact h.symm
  obtain ⟨ω, hωK⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf sX hd (Divisor.toWeilDivisor K₀)
  have hω : IsDualizingSheaf sX (n + 1) ω.toModules :=
    hω₁.of_iso (eqToIso (by rw [hL₀K, toModules_sheaf_toWeilDivisor]) ≪≫
      hlin.divisorialSheafIso ≪≫ eqToIso (by rw [hωK, toModules_sheaf_toWeilDivisor]))
  -- `ω_X(P) = 𝒪_X(K₀ + P)`
  set KP : Divisor X := K₀ + Finsupp.single P 1 with hKPdef
  have hKPP : KP.coeff P = 0 := by
    rw [hKPdef, DivisorWithCoeffs.coeff_add, hK₀, coeff_divisorOfForm, hτ₀P,
      DivisorWithCoeffs.coeff_single_self]
    norm_num
  obtain ⟨ωXS, hωXS⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf sX hd
    (Divisor.toWeilDivisor KP)
  set DS : MMP.Flips.WeilDivisor X := Divisor.toWeilDivisor (Finsupp.single P 1) with hDS
  obtain ⟨m₁, hm₁, hKPc⟩ := hQ.2 KP
  lift m₁ to ℕ+ using hm₁
  have hm₁ := m₁.pos
  have hgoodω : ωXS ∈ goodSupportSubsheaves (closedRange j) :=
    mem_goodSupportSubsheaves_of_sheaf sX hd j P hj hKPP hm₁ hKPc hωXS
  -- the embedded dualizing sheaf
  have hΩ := embeddedDualizingSheaf_eq_sheaf_divisorOfForm sX hX hdim hdT j hT P hj hgoodω hτ₀0
    hτ₀P hωXS hρ₀0 hρ₀
  obtain ⟨Ω, hΩ'⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf (j ≫ sX) hdT
    (Divisor.toWeilDivisor (divisorOfForm ρ₀))
  -- the class of `Δ = B - P`
  set Δ : QDivisor X := BV - Finsupp.single P 1 with hΔ
  have hΔP : Δ.coeff P = 0 := by
    rw [hΔ, DivisorWithCoeffs.coeff_sub, hP, DivisorWithCoeffs.coeff_single_self, sub_self]
  have hΔ0 : ∀ Q, 0 ≤ Δ.coeff Q := fun Q => by
    rw [hΔ, DivisorWithCoeffs.coeff_sub]
    by_cases hQP : Q = P
    · subst hQP; rw [hP, DivisorWithCoeffs.coeff_single_self]; norm_num
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hQP)]; linarith [h0 Q]
  have hΔ1 : ∀ Q, Δ.coeff Q ≤ 1 := fun Q => by
    rw [hΔ, DivisorWithCoeffs.coeff_sub]
    have : 0 ≤ DivisorWithCoeffs.coeff (Finsupp.single P (1 : ℚ) : QDivisor X) Q := by
      change 0 ≤ (Finsupp.single P (1 : ℚ)) Q
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
    linarith [hle Q]
  obtain ⟨m, hm, hEc⟩ := (isQCartier_of_isQFactorial sX hQ Δ).exists_pos
  lift m to ℕ+ using hm
  have hm := m.pos
  obtain ⟨E, hE, hEcart⟩ := hEc
  have hEP : E.coeff P = 0 := by
    have := congrArg (fun D : QDivisor X => D.coeff P) hE
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, hΔP, smul_zero] at this
    exact_mod_cast this
  obtain ⟨LE, hLE⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf sX hd (Divisor.toWeilDivisor E)
  have hEcart1 : (((1 : ℕ) : ℤ) • E).IsCartier := by rw [Nat.cast_one, one_smul]; exact hEcart
  have hgoodE : LE ∈ goodSupportSubsheaves (closedRange j) :=
    mem_goodSupportSubsheaves_of_sheaf sX hd j P hj hEP one_pos hEcart1 hLE
  -- the restrictions of `E` and of `m₁ (K₀ + P)`
  have hBE := hnotsupp E hEP
  set ET : Divisor T := E.pullback hEcart hBE with hET
  have hKPmP : ((m₁ : ℤ) • KP).coeff P = 0 := by
    rw [DivisorWithCoeffs.coeff_smul, hKPP, smul_zero]
  have hBK := hnotsupp _ hKPmP
  set KT : Divisor T := ((m₁ : ℤ) • KP).pullback hKPc hBK with hKT
  set D₀ : Divisor T := KT - (m₁ : ℤ) • divisorOfForm ρ₀ with hD₀
  set D₃ : Divisor T := (m : ℤ) • D₀ + (m₁ : ℤ) • ET with hD₃
  obtain ⟨NM, hNM⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf (j ≫ sX) hdT
    (Divisor.toWeilDivisor KT)
  obtain ⟨L0, hL0⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf (j ≫ sX) hdT
    (Divisor.toWeilDivisor D₀)
  obtain ⟨NE, hNE⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf (j ≫ sX) hdT
    (Divisor.toWeilDivisor ET)
  obtain ⟨N3, hN3⟩ := WeilDivisor.exists_weilDivisorialSubsheaf_sheaf (j ≫ sX) hdT
    (Divisor.toWeilDivisor D₃)
  -- `i^w ω_X(P) = (1/m₁) 𝒪_T(j^*(m₁(K₀ + P)))`
  have hWR : IsWeilRestriction j ωXS (NM.divNat m₁) := by
    refine ⟨hgoodω, m₁, fun P' _ => ?_, NM, ?_, rfl⟩
    · rw [RationalFunctionsSubmodule.reflexivePow_natCast, hωXS,
        sheaf_reflexivePowNat sX hd KP hm₁]
      exact isInvertibleAt_sheaf hKPc _
    · rw [hNM, RationalFunctionsSubmodule.reflexivePow_natCast, hωXS,
        sheaf_reflexivePowNat sX hd KP hm₁, weilRestrictionCartier_sheaf_toWeilDivisor j hKPc hBK]
  have hSum₁ : QWeilDivisorialSheaf.IsSum (Ω.divNat 1) (L0.divNat m₁) (NM.divNat m₁) := by
    refine isSum_divNat_of_sheaf (j ≫ sX) hdT hΩ' hL0 hNM ?_
    simp only [hD₀, PNat.one_coe, Nat.cast_one, one_smul, one_mul]
    congr 1
    abel
  have hDZ : IsDifferentZero j ωXS (L0.divNat m₁) :=
    ⟨Ω, NM.divNat m₁, hΩ'.trans hΩ.symm, hWR, hSum₁⟩
  -- `i^w 𝒪_X(E) = 𝒪_T(j^*E)`
  have hWRE : IsWeilRestriction j LE (NE.divNat 1) := by
    refine ⟨hgoodE, 1, fun P' _ => ?_, NE, ?_, rfl⟩
    · rw [RationalFunctionsSubmodule.reflexivePow_natCast, hLE, PNat.one_coe,
        sheaf_reflexivePowNat sX hd E le_rfl]
      exact isInvertibleAt_sheaf hEcart1 _
    · rw [hNE, RationalFunctionsSubmodule.reflexivePow_natCast, hLE, PNat.one_coe,
        sheaf_reflexivePowNat sX hd E le_rfl]
      simp only [Nat.cast_one, one_smul]
      rw [weilRestrictionCartier_sheaf_toWeilDivisor j hEcart hBE]
  have hWRQ : IsWeilRestrictionQ j (LE.divNat m) (NE.divNat (m * 1)) :=
    ⟨LE, m, hgoodE, rfl, NE, 1, hWRE, rfl⟩
  have hSum₂ : QWeilDivisorialSheaf.IsSum (L0.divNat m₁) (NE.divNat (m * 1))
      (N3.divNat (m₁ * m)) := by
    refine isSum_divNat_of_sheaf (j ≫ sX) hdT hL0 hNE hN3 ?_
    simp only [hD₃, PNat.mul_coe, PNat.one_coe, mul_one]
  have hDiff : IsDifferent j ωXS (LE.divNat m) (N3.divNat (m₁ * m)) :=
    ⟨⟨LE, m, hgoodE, rfl⟩, L0.divNat m₁, NE.divNat (m * 1), hDZ, hWRQ, hSum₂⟩
  -- the hypotheses `(⋆)`
  have hyp : DifferentHypotheses j sX (n + 1) ω ωXS DS (QDivisor.toQWeilDivisor Δ) :=
    { isNormalVariety := hX
      isReduced := inferInstance
      coheight_eq_one := hcod
      exists_weilDivisorPrime := fun Z => ⟨⟨P, inferInstance,
        P.isDiscreteValuationRing_localRing⟩, (hjη Z).symm⟩
      coeff_divisor := fun Γ => by
        obtain ⟨ZT⟩ : Nonempty (irreducibleComponents T) :=
          ⟨⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
        rw [hDS, Divisor.toWeilDivisor_apply]
        by_cases hΓP : Γ.1 = P
        · rw [hΓP, DivisorWithCoeffs.coeff_single_self, if_pos ⟨ZT, by rw [hjη]⟩]
        · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hΓP), if_neg]
          rintro ⟨Z, hZ⟩
          rw [hjη] at hZ
          exact hΓP (AlgebraicGeometry.PrimeDivisor.genericPoint_injective hZ)
      coeff_nonneg := fun Γ => by rw [QDivisor.toQWeilDivisor_apply]; exact hΔ0 _
      coeff_le_one := fun Γ => by rw [QDivisor.toQWeilDivisor_apply]; exact hΔ1 _
      not_subset := fun Γ hΓ hmem => by
        rw [hj] at hmem
        obtain rfl := eq_of_genericPoint_mem_primeDivisor_support hmem
        exact hΓ (by rw [QDivisor.toQWeilDivisor_apply]; exact hΔP)
      isDualizingSheaf := hω
      twist_eq := by
        rw [hωXS, WeilDivisorialSubsheaf.twist, hωK, hDS, sheaf_mul_sheaf sX hd]
      mem_goodSupportSubsheaves := hgoodω }
  set BT : QDivisor T := ((((m₁ : ℕ) * (m : ℕ) : ℕ) : ℚ)⁻¹) • Divisor.toQDivisor D₃ with hBT
  have hdiff : IsDifferentDivisor j sX (n + 1) ω ωXS DS (QDivisor.toQWeilDivisor Δ)
      (QDivisor.toQWeilDivisor BT) := by
    refine ⟨hyp, LE.divNat m, ⟨m, Divisor.toWeilDivisor E, LE, fun Γ => ?_, hLE, rfl⟩,
      m₁ * m, Divisor.toWeilDivisor D₃, N3, fun Γ => ?_, hN3, hDiff⟩
    · have := congrArg (fun D : QDivisor X => D.coeff Γ.1) hE
      simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
        Int.cast_natCast] at this
      rw [Divisor.toWeilDivisor_apply, QDivisor.toQWeilDivisor_apply, this]
    · rw [Divisor.toWeilDivisor_apply, QDivisor.toQWeilDivisor_apply, hBT,
        DivisorWithCoeffs.coeff_smul, Divisor.coeff_toQDivisor, smul_eq_mul]
      simp only [PNat.mul_coe]
      push_cast
      have h1 : (m₁ : ℚ) ≠ 0 := by exact_mod_cast hm₁.ne'
      have h2 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
  -- `B - P = Δ` is effective, so `(B - P)⁺ = Δ` and `(B - P)⁻ = 0`
  have hΔnn : (0 : QDivisor X) ≤ BV - Finsupp.single P 1 := fun Q => hΔ0 Q
  have hpos : (BV - Finsupp.single P 1)⁺ = Δ := posPart_eq_self.mpr hΔnn
  have hneg : (BV - Finsupp.single P 1)⁻ = 0 := negPart_eq_zero.mpr hΔnn
  have hgen0 : ∀ Z : irreducibleComponents T,
      j (componentGenericPoint T Z) ∉ (BV - Finsupp.single P 1)⁻.supp := by
    rw [hneg, DivisorWithCoeffs.supp_zero]
    exact fun _ h => h
  have hpb0 : ∀ (D : QDivisor X) (_ : D = 0)
      (h : ∀ Z : irreducibleComponents T, j (componentGenericPoint T Z) ∉ D.supp),
      D.IsPullback j h 0 := by
    rintro D rfl h m _ D' hD' _
    obtain rfl : D' = 0 := Divisor.toQDivisor_injective (by rw [hD', smul_zero, map_zero])
    exact ⟨0, by rw [smul_zero, map_zero], Divisor.isPullback_zero _⟩
  refine ⟨BT, isAdjunctionStep_of_isDifferentDivisor (BS' := BT) hT hdim P hP.ge hj
    (by rw [hpos]; exact hdiff) hgen0 (by rw [hneg]; exact QDivisor.isQCartier_zero)
    (by rw [sub_self]; exact hpb0 _ hneg hgen0) τ₀ hτ₀0 hτ₀P ρ₀ hρ₀
    (isQCartier_of_isQFactorial sX hQ _)⟩

end Existence

section Reduced

open MMP.Mori

/-- **A real boundary is a convex combination of reduced rational boundaries.** An `ℝ`-divisor `B`
with coefficients in `[0, 1]` is a positive convex combination of `ℚ`-divisors `B_k` with
coefficients in `{0, 1}`, each with coefficient one wherever `B` has: expand
`∏_P ((1 - b_P) + b_P) = 1` over the components `P` of `B`. -/
private theorem exists_convex_reduced {X : Scheme.{0}} (B : RDivisor X)
    (hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) :
    ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor X),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ B = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      (∀ k P, 0 ≤ (Bk k).coeff P ∧ (Bk k).coeff P ≤ 1) ∧
      ∀ k P, B.coeff P = 1 → (Bk k).coeff P = 1 := by
  classical
  set s := B.support
  let w : s → Bool → ℝ := fun P e => if e then B P else 1 - B P
  have hw0 : ∀ P e, 0 ≤ w P e := fun P e => by
    simp only [w]
    split_ifs
    · exact (hB P).1
    · linarith [(hB P).2, show B P = B.coeff P from rfl]
  let tt : (s → Bool) → ℝ := fun ε => ∏ P, w P (ε P)
  have htt0 : ∀ ε, 0 ≤ tt ε := fun ε => Finset.prod_nonneg fun P _ => hw0 P (ε P)
  let V : (s → Bool) → QDivisor X := fun ε =>
    ∑ P : s, if ε P then Finsupp.single (P : MMP.Mori.PrimeDivisor X) (1 : ℚ) else 0
  have hV : ∀ ε Q, (V ε).coeff Q = if h : Q ∈ s then (if ε ⟨Q, h⟩ then 1 else 0) else 0 := by
    intro ε Q
    simp only [V, DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply]
    by_cases h : Q ∈ s
    · rw [dif_pos h, Finset.sum_eq_single ⟨Q, h⟩]
      · by_cases hε : ε ⟨Q, h⟩ <;> simp [hε]
      · intro P _ hP
        by_cases hε : ε P
        · rw [if_pos hε, Finsupp.single_apply, if_neg]
          exact fun h' => hP (Subtype.ext h')
        · rw [if_neg hε]
          rfl
      · simp
    · rw [dif_neg h]
      refine Finset.sum_eq_zero fun P _ => ?_
      by_cases hε : ε P
      · rw [if_pos hε, Finsupp.single_apply, if_neg]
        rintro rfl
        exact h P.2
      · rw [if_neg hε]
        rfl
  have hsum1 : ∑ ε, tt ε = 1 := by
    simp only [tt]
    rw [← Fintype.prod_sum]
    refine Finset.prod_eq_one fun P _ => ?_
    simp [w, Fintype.univ_bool]
  have hmarg : ∀ Q, ∑ ε, tt ε * ((V ε).coeff Q : ℝ) = B.coeff Q := by
    intro Q
    by_cases h : Q ∈ s
    · set q : s := ⟨Q, h⟩
      let f : s → Bool → ℝ := fun P e => w P e * (if P = q then (if e then 1 else 0) else 1)
      have e : ∀ ε : s → Bool, tt ε * ((V ε).coeff Q : ℝ) = ∏ P, f P (ε P) := by
        intro ε
        rw [Finset.prod_mul_distrib, hV, dif_pos h, Finset.prod_ite_eq' Finset.univ q]
        simp only [Finset.mem_univ, if_true, tt]
        split_ifs <;> simp
      simp only [e]
      rw [← Fintype.prod_sum, Finset.prod_eq_single q]
      · simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
          Finset.sum_insert, Finset.sum_singleton, f, w, if_pos rfl]
        simp
        rfl
      · intro P _ hP
        simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
          Finset.sum_insert, Finset.sum_singleton, f, w, if_neg hP]
        simp
      · simp
    · rw [show B.coeff Q = 0 from Finsupp.notMem_support_iff.mp h]
      refine Finset.sum_eq_zero fun ε _ => ?_
      rw [hV, dif_neg h]
      simp
  -- the positive weights
  let K := Finset.univ.filter fun ε : s → Bool => 0 < tt ε
  let e := Fintype.equivFin K
  have hKpos : ∀ x : K, 0 < tt x.1 := fun x => (Finset.mem_filter.mp x.2).2
  have hsumK : ∀ g : (s → Bool) → ℝ, (∀ ε, tt ε = 0 → g ε = 0) →
      ∑ k : Fin (Fintype.card K), g (e.symm k).1 = ∑ ε, g ε := by
    intro g hg
    rw [Equiv.sum_comp e.symm (fun x : K => g x.1), Finset.sum_coe_sort K g]
    refine Finset.sum_filter_of_ne fun ε _ hε => ?_
    rcases (htt0 ε).lt_or_eq with h | h
    · exact h
    · exact absurd (hg ε h.symm) hε
  refine ⟨Fintype.card K, fun k => tt (e.symm k).1, fun k => V (e.symm k).1,
    fun k => hKpos (e.symm k), ?_, ?_, fun k P => ?_, fun k P hP => ?_⟩
  · rw [hsumK tt (fun ε h => h), hsum1]
  · ext Q
    have := hsumK (fun ε => tt ε * ((V ε).coeff Q : ℝ)) (fun ε h => by simp [h])
    rw [hmarg] at this
    change B.coeff Q = DivisorWithCoeffs.coeff (∑ k, _) Q
    rw [← this]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.finset_sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    rfl
  · rw [hV]
    split_ifs <;> norm_num
  · have hQ : P ∈ s := by
      rw [Finsupp.mem_support_iff]
      change B.coeff P ≠ 0
      rw [hP]; norm_num
    rw [hV, dif_pos hQ]
    have hpos := hKpos (e.symm k)
    by_contra hne
    have hf : (e.symm k).1 ⟨P, hQ⟩ = false := by
      by_contra h'
      simp [h'] at hne
    apply hpos.ne'
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨P, hQ⟩) ?_
    simp only [w, hf]
    change 1 - B.coeff P = 0
    rw [hP]; norm_num

end Reduced

section Convex

open MMP.Mori MMP.Flips MMP.Fourfold

/-- The pull-back of a `ℚ`-Cartier `ℚ`-divisor is an `ℝ`-Cartier pull-back, along any morphism. -/
private theorem isRCartierPullback_of_qIsPullback {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {G : QDivisor X}
    (hG : G.IsQCartier) {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ G.supp}
    {G' : QDivisor Y} (h : G.IsPullback f hB G') :
    IsRCartierPullback f (QDivisor.toRDivisor G) (QDivisor.toRDivisor G') := by
  obtain ⟨m, hm, M, hM, hMc⟩ := hG.exists_pos
  obtain ⟨M', hM', hp⟩ := h m hm M hM hMc
  have key := isRCartierPullback_smul ((m : ℝ)⁻¹) (isRCartierPullback_toRDivisor hMc _ hp)
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have e : ∀ {Z : Scheme.{0}} (A : QDivisor Z) (N : Divisor Z),
      Divisor.toQDivisor N = (m : ℤ) • A →
      QDivisor.toRDivisor A = (m : ℝ)⁻¹ • Divisor.toRDivisor N := by
    intro Z A N hN
    ext E
    have := congrArg (fun D : QDivisor Z => D.coeff E) hN
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, zsmul_eq_mul,
      Int.cast_natCast] at this
    change ((A.coeff E : ℚ) : ℝ) = (m : ℝ)⁻¹ * ((N.coeff E : ℤ) : ℝ)
    rw [show ((N.coeff E : ℤ) : ℝ) = (((N.coeff E : ℤ) : ℚ) : ℝ) by push_cast; rfl, this]
    push_cast
    field_simp
  rw [e G M hM, e G' M' hM']
  exact key

/-- **The residue different as a convex combination of rational differents.** Let `S` be a prime
divisor of a `ℚ`-factorial projective complex fourfold, normal as a subscheme `T`, and `B` an
`ℝ`-divisor with coefficients in `[0, 1]` and `coeff_S B = 1`. Then `B = ∑ t_k B_k` is a positive
convex combination of rational boundaries `B_k` with differents `Δ_k = Diff_T(B_k - S)`, and
`Δ = ∑ t_k Δ_k` is a residue different of `B`: `(div τ + B)|_T = div Res_T τ + Δ`. -/
private theorem exists_convex_isAdjunctionStep {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = 4) (B : RDivisor X)
    (hB : ∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) (S : MMP.Mori.PrimeDivisor X)
    (hSB : B.coeff S = 1)
    [IsIntegral S.idealSheaf.subscheme] [IsLocallyNoetherian S.idealSheaf.subscheme]
    [CompactSpace S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
    (hT : IsNormalVariety ℂ (S.idealSheaf.subschemeι ≫ sX))
    (hdimT : topologicalKrullDim S.idealSheaf.subscheme = (3 : ℕ)) :
    ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor X)
      (Δk : Fin m → QDivisor S.idealSheaf.subscheme),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ B = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      (∀ k, IsAdjunctionStep sX (Bk k) S.idealSheaf.subschemeι (Δk k)) ∧
      ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
        ∀ ρ : RationalPluriForms (S.idealSheaf.subschemeι ≫ sX) 3 1,
          IsPoincareResidue sX S.idealSheaf.subschemeι 3 1 τ ρ →
            MMP.Flips.IsRCartierPullback S.idealSheaf.subschemeι
              (Divisor.toRDivisor (divisorOfForm τ) + B)
              (Divisor.toRDivisor (divisorOfForm ρ) +
                ∑ k, t k • QDivisor.toRDivisor (Δk k)) := by
  classical
  haveI : IsNoetherian X := {}
  haveI : IsNoetherian S.idealSheaf.subscheme := {}
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hproj.isProjective
  have hι : Set.range S.idealSheaf.subschemeι.base = (S.support : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
  have hdim' : topologicalKrullDim X = (3 : ℕ) + 1 := by rw [hdim]; rfl
  obtain ⟨Q₀⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimT (by norm_num)
  obtain ⟨m, t, Bk, ht, hsum, hBeq, h01, h1⟩ := exists_convex_reduced B hB
  choose Δk hΔk using fun k => exists_isAdjunctionStep_of_isQFactorial sX hQ hdim' hdimT
    S.idealSheaf.subschemeι S hι hT Q₀ (Bk k) (fun Q => (h01 k Q).1) (fun Q => (h01 k Q).2)
    (h1 k S hSB)
  refine ⟨m, t, Bk, Δk, ht, hsum, hBeq, hΔk, fun τ hτ hτS ρ hρ => ?_⟩
  have hk : ∀ k, IsRCartierPullback S.idealSheaf.subschemeι
      (Divisor.toRDivisor (divisorOfForm τ) + QDivisor.toRDivisor (Bk k))
      (Divisor.toRDivisor (divisorOfForm ρ) + QDivisor.toRDivisor (Δk k)) := by
    intro k
    obtain ⟨hgen, hp⟩ := (hΔk k).isPullback_divisorOfForm_add_of_isPoincareResidue hdim' S hι τ
      hτ hτS ρ hρ (isQCartier_of_isQFactorial sX hQ _)
    have := isRCartierPullback_of_qIsPullback (isQCartier_of_isQFactorial sX hQ _) hp
    simpa only [map_add, QDivisor.toRDivisor_toQDivisor] using this
  have hall := isRCartierPullback_sum Finset.univ _ _
    (fun k _ => isRCartierPullback_smul (t k) (hk k))
  have e : ∀ {Z : Scheme.{0}} (A : RDivisor Z) (C : Fin m → RDivisor Z),
      ∑ k, t k • (A + C k) = A + ∑ k, t k • C k := by
    intro Z A C
    rw [Finset.sum_congr rfl fun k _ => smul_add (t k) A (C k), Finset.sum_add_distrib,
      ← Finset.sum_smul, hsum, one_smul]
  rw [e, e, ← hBeq] at hall
  exact hall

end Convex

end DifferentExistence

/-! ### Programs with scaling, bundled -/

section Bundled

open MMP.Flips

/-- A model of a program over `Zb`: a normal variety with a map to `Zb`, a canonical divisor, a
boundary and a scaling divisor. -/
private structure PModel (Zb : Scheme.{0}) where
  Y : Scheme.{0}
  [isIntegral : IsIntegral Y]
  [compactSpace : CompactSpace Y]
  [isLocallyNoetherian : IsLocallyNoetherian Y]
  [isNormal : IsNormal Y]
  s : Y ⟶ Spec (.of ℂ)
  π : Y ⟶ Zb
  K : Divisor Y
  B : RDivisor Y
  C : RDivisor Y

attribute [local instance] PModel.isIntegral PModel.compactSpace PModel.isLocallyNoetherian
  PModel.isNormal

/-- The model conditions of a program over `Zb`. -/
private def PModel.Good {Zb : Scheme.{0}} (sZ : Zb ⟶ Spec (.of ℂ)) (M : PModel Zb) : Prop :=
  M.π ≫ sZ = M.s ∧ MMP.Mori.IsProjectiveVariety ℂ M.s ∧ IsQFactorial M.s ∧
    (∃ m : ℕ, Divisor.IsCanonicalDivisor M.s m M.K) ∧ IsRealKltPair M.s M.B

/-- A step of a program between two models. -/
private structure PStep {Zb : Scheme.{0}} (M M' : PModel Zb) where
  W : Scheme.{0}
  sW : W ⟶ Spec (.of ℂ)
  f : M.Y ⟶ W
  g : W ⟶ Zb
  fp : M'.Y ⟶ W
  φ : M.Y.RationalMap M'.Y

/-- The step conditions of a program with scaling, at threshold `lam`. -/
private def PStep.Good {Zb : Scheme.{0}} {M M' : PModel Zb} (st : PStep M M') (lam : ℝ) : Prop :=
  IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ M.s M.π
      (logCanonicalDivisor M.K (M.B + t • M.C))} lam ∧
    MMP.Mori.IsProjectiveVariety ℂ st.sW ∧ st.f ≫ st.g = M.π ∧ st.fp ≫ st.g = M'.π ∧
    IsNegativeExtremalContraction ℂ M.s st.sW (logCanonicalDivisor M.K M.B) st.f ∧
    IsNumericallyTrivialOver ℂ M.s st.f (logCanonicalDivisor M.K (M.B + lam • M.C)) ∧
    ((IsBirationalMorphism st.f ∧
        (∃ E : MMP.Mori.PrimeDivisor M.Y,
          (MMP.Mori.exceptionalSet st.f : Set M.Y) = E.support) ∧
        IsIso st.fp ∧ IsModificationOf st.f st.fp st.φ) ∨
      IsFlip ℂ M.s st.sW M'.s (logCanonicalDivisor M.K M.B) st.f st.fp st.φ) ∧
    M'.B = MMP.Mori.RationalMap.transformDivisor st.φ M.B ∧
    M'.C = MMP.Mori.RationalMap.transformDivisor st.φ M.C

/-- **No infinite program with scaling and big boundary.** An infinite sequence of steps of a
program with scaling over a projective `Zb`, starting from a `ℚ`-factorial projective threefold
with an effective klt boundary containing an effective `ℚ`-divisor big over `Zb`, whose upper
level `K + B + c C` (`c > 0`) is klt and nef, is impossible. -/
private theorem false_of_pStep {Zb : Scheme.{0}} (sZ : Zb ⟶ Spec (.of ℂ))
    (hZ : MMP.Mori.IsProjectiveVariety ℂ sZ) (Mg : ℕ → PModel Zb) (lam : ℕ → ℝ)
    (st : ∀ k, PStep (Mg k) (Mg (k + 1))) (hgood : ∀ k, (Mg k).Good sZ)
    (hstep : ∀ k, (st k).Good (lam k)) (c : ℝ) (hc : 0 < c)
    (hK : (Mg 0).K.IsCanonicalDivisor (Mg 0).s 3)
    (hB : ∀ P, 0 ≤ (Mg 0).B.coeff P) (hC : ∀ P, 0 ≤ (Mg 0).C.coeff P)
    (hklt : IsRealKltPair (Mg 0).s ((Mg 0).B + c • (Mg 0).C))
    (hnef : IsRelativelyNef ℂ (Mg 0).s (Mg 0).π
      (logCanonicalDivisor (Mg 0).K ((Mg 0).B + c • (Mg 0).C)))
    (hA : ∃ A : QDivisor (Mg 0).Y, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig (Mg 0).π ∧
      QDivisor.toRDivisor A ≤ (Mg 0).B) : False := by
  obtain ⟨hπ, hX, hXq, -, -⟩ := hgood 0
  have hcc := isCartierCombination_of_isQFactorial hXq
  have hcC : ∀ P, 0 ≤ (c • (Mg 0).C).coeff P := fun P => by
    change 0 ≤ c * (Mg 0).C.coeff P
    exact mul_nonneg hc.le (hC P)
  have H := (exists_scalingProgram_and_finite_of_isRelativelyBig (Mg 0).s sZ (Mg 0).π hπ hX hZ
    hXq (Mg 0).K hK (Mg 0).B (c • (Mg 0).C) hB hcC (hcc _) (hcc _) hklt hnef hA).2
  -- the step conditions with the scaling divisor `c C` and thresholds `λ / c`
  have hscale : ∀ k, IsLeast {t : ℝ | 0 ≤ t ∧ IsRelativelyNef ℂ (Mg k).s (Mg k).π
      (logCanonicalDivisor (Mg k).K ((Mg k).B + t • (c • (Mg k).C)))} (lam k / c) ∧
      IsNumericallyTrivialOver ℂ (Mg k).s (st k).f
        (logCanonicalDivisor (Mg k).K ((Mg k).B + (lam k / c) • (c • (Mg k).C))) ∧
      c • (Mg (k + 1)).C = MMP.Mori.RationalMap.transformDivisor (st k).φ (c • (Mg k).C) := by
    intro k
    obtain ⟨⟨h1, h2⟩, -, -, -, -, h3, -, -, h4⟩ := hstep k
    have e : ∀ t : ℝ, t • (c • (Mg k).C) = (t * c) • (Mg k).C := fun t => by rw [smul_smul]
    refine ⟨⟨⟨div_nonneg h1.1 hc.le, ?_⟩, fun t ht => ?_⟩, ?_, ?_⟩
    · rw [e, div_mul_cancel₀ _ hc.ne']; exact h1.2
    · have := h2 ⟨mul_nonneg ht.1 hc.le, by rw [← e]; exact ht.2⟩
      rw [div_le_iff₀ hc]; exact this
    · rw [e, div_mul_cancel₀ _ hc.ne']; exact h3
    · rw [h4]
      exact ((MMP.Mori.RationalMap.transformDivisorₗ ℝ (st k).φ).map_smul c (Mg k).C).symm
  refine H ⊤ (fun k => (Mg (k + 1)).Y) (fun k => (Mg (k + 1)).s)
    (fun k => (Mg (k + 1)).π) (fun k => (Mg (k + 1)).K) (fun k => (Mg (k + 1)).B)
    (fun k => c • (Mg (k + 1)).C) (fun k => lam k / c) (fun k => (st k).W) (fun k => (st k).sW)
    (fun k => match k with | 0 => (st 0).f | k + 1 => (st (k + 1)).f)
    (fun k => (st k).g) (fun k => (st k).fp)
    (fun k => match k with | 0 => (st 0).φ | k + 1 => (st (k + 1)).φ) ?_ ?_ rfl
  · intro k _
    cases k with
    | zero => exact (hgood 0).elim fun h1 h2 => ⟨h1, h2⟩
    | succ k => exact (hgood (k + 1)).elim fun h1 h2 => ⟨h1, h2⟩
  · intro k _
    cases k with
    | zero =>
      obtain ⟨-, h5, h6, h7, h8, -, h9, h10, -⟩ := hstep 0
      obtain ⟨s1, s2, s3⟩ := hscale 0
      exact ⟨s1, h5, h6, h7, h8, s2, h9, h10, s3⟩
    | succ k =>
      obtain ⟨-, h5, h6, h7, h8, -, h9, h10, -⟩ := hstep (k + 1)
      obtain ⟨s1, s2, s3⟩ := hscale (k + 1)
      exact ⟨s1, h5, h6, h7, h8, s2, h9, h10, s3⟩

/-- Transport of a step along an equality of its target. -/
private def PStep.castR {Zb : Scheme.{0}} {M M' M'' : PModel Zb} (h : M' = M'')
    (s : PStep M M') : PStep M M'' := h ▸ s

private theorem PStep.good_castR {Zb : Scheme.{0}} {M M' M'' : PModel Zb} (h : M' = M'')
    (s : PStep M M') {lam : ℝ} (hs : s.Good lam) : (s.castR h).Good lam := by
  subst h; exact hs

/-- **Concatenating blocks.** A chain of finite blocks of steps, the last model of each block
being the first model of the next, infinitely many of them nonempty, concatenates to one infinite
sequence of steps. -/
private theorem exists_pStep_of_blocks {Zb : Scheme.{0}} (sZ : Zb ⟶ Spec (.of ℂ))
    (Mb : ℕ → ℕ → PModel Zb) (n : ℕ → ℕ) (hj : ∀ i, Mb (i + 1) 0 = Mb i (n i))
    (sb : ∀ i m, m < n i → PStep (Mb i m) (Mb i (m + 1))) (lam : ℕ → ℝ)
    (hgood : ∀ i m, m ≤ n i → (Mb i m).Good sZ)
    (hsb : ∀ i m (h : m < n i), (sb i m h).Good (lam i))
    (hinf : ∀ N, ∃ i, N ≤ i ∧ 0 < n i) :
    ∃ (j : ℕ) (Mg : ℕ → PModel Zb) (lamg : ℕ → ℝ) (st : ∀ k, PStep (Mg k) (Mg (k + 1))),
      Mg 0 = Mb j 0 ∧ (∀ k, (Mg k).Good sZ) ∧ ∀ k, (st k).Good (lamg k) := by
  classical
  -- the first nonempty block from `N` on
  let nx : ℕ → ℕ := fun N => Nat.find (hinf N)
  have hnx : ∀ N, N ≤ nx N ∧ 0 < n (nx N) := fun N => Nat.find_spec (hinf N)
  have hnx_min : ∀ N l, N ≤ l → l < nx N → n l = 0 := fun N l h1 h2 => by
    by_contra h
    exact Nat.find_min (hinf N) h2 ⟨h1, Nat.pos_of_ne_zero h⟩
  -- through empty blocks the first model does not change
  have hempty : ∀ N d, (∀ l, N ≤ l → l < N + d → n l = 0) → Mb N 0 = Mb (N + d) 0 := by
    intro N d
    induction d with
    | zero => intro; rfl
    | succ d ih =>
      intro h
      rw [ih fun l h1 h2 => h l h1 (by omega), ← add_assoc, hj, h (N + d) (by omega) (by omega)]
  have hnxeq : ∀ N, Mb N 0 = Mb (nx N) 0 := fun N => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hnx N).1
    rw [hd]
    exact hempty N d fun l h1 h2 => hnx_min N l h1 (by omega)
  let next : ℕ × ℕ → ℕ × ℕ := fun p =>
    if p.2 + 1 < n p.1 then (p.1, p.2 + 1) else (nx (p.1 + 1), 0)
  let pos : ℕ → ℕ × ℕ := fun k => Nat.rec (nx 0, 0) (fun _ p => next p) k
  have hpos : ∀ k, (pos k).2 < n (pos k).1 := by
    intro k
    induction k with
    | zero => exact (hnx 0).2
    | succ k ih =>
      change (next (pos k)).2 < n (next (pos k)).1
      simp only [next]
      split_ifs with h
      · exact h
      · exact (hnx _).2
  have heq : ∀ p : ℕ × ℕ, p.2 < n p.1 → Mb p.1 (p.2 + 1) = Mb (next p).1 (next p).2 := by
    rintro ⟨i, m⟩ hm
    simp only [next]
    split_ifs with h
    · rfl
    · have : m + 1 = n i := by simp only at h hm; omega
      simp only
      rw [this, ← hj]
      exact hnxeq (i + 1)
  refine ⟨nx 0, fun k => Mb (pos k).1 (pos k).2, fun k => lam (pos k).1,
    fun k => (sb (pos k).1 (pos k).2 (hpos k)).castR (heq (pos k) (hpos k)), rfl,
    fun k => hgood _ _ (hpos k).le, fun k => PStep.good_castR _ _ (hsb _ _ _)⟩

/-! ### Steps of a program -/

section StepHelpers

variable {k : Type} [Field k]

private theorem compHom_compHom' {X Y Z T : Scheme.{0}} (φ : X.RationalMap Y) (f : Y ⟶ Z)
    (g : Z ⟶ T) : (φ.compHom f).compHom g = φ.compHom (f ≫ g) := by
  obtain ⟨φ, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    ← Scheme.RationalMap.compHom_toRationalMap]
  congr 1

private theorem toRationalMap_compHom' {X Z T : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ T) :
    f.toRationalMap.compHom g = (f ≫ g).toRationalMap := by
  rw [Scheme.Hom.toRationalMap, ← Scheme.RationalMap.compHom_toRationalMap,
    Scheme.Hom.toPartialMap_compHom]

/-- **A step creating no divisor.** Let `ψ : Y ⤏ Y'` lie over `W` (`f = f⁺ ∘ ψ`), with `f`
proper birational onto the normal variety `W`. If `ψ` is defined at the generic point of every
prime divisor of `Y`, and every prime divisor `F` of `Y'` maps onto a prime divisor `Q` of `W`
over whose generic point `f⁺` has the single point `η_F`, then every prime divisor of `Y'` is the
birational transform of a prime divisor of `Y`. -/
private theorem not_isInverseExceptional_of_isOver {Y Y' W : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsLocallyNoetherian W] [IsNormal W]
    [CompactSpace W] {sW : W ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)} [IsSeparated sY']
    (hW : IsNormalVariety ℂ sW) {f : Y ⟶ W} (hY : IsNormalVariety ℂ (f ≫ sW)) [IsProper f]
    (hfb : IsBirationalMorphism f) {fp : Y' ⟶ W} {ψ : Y.RationalMap Y'}
    (hover : ψ.compHom fp = f.toRationalMap)
    (hdef : ∀ P : MMP.Mori.PrimeDivisor Y, MMP.Mori.RationalMap.DefinedAt ψ P.genericPoint)
    (hinj : ∀ F : MMP.Mori.PrimeDivisor Y', ∃ Q : MMP.Mori.PrimeDivisor W,
      fp F.genericPoint = Q.genericPoint ∧ ∀ y : Y', fp y = Q.genericPoint → y = F.genericPoint) :
    ∀ F : MMP.Mori.PrimeDivisor Y', ¬ MMP.Flips.RationalMap.IsInverseExceptional ψ F := by
  have := hW.1
  have := isSeparated_toTerminal sW
  have := isSeparated_toTerminal sY'
  intro F hF
  obtain ⟨Q, hQ, hinjQ⟩ := hinj F
  obtain ⟨P, hPQ, -, -⟩ :=
    MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hW hY hfb Q
  obtain ⟨g', hg'P, hg'⟩ := MMP.Mori.RationalMap.definedAt_iff.mp (hdef P)
  have hrat : (g'.compHom fp).toRationalMap = f.toPartialMap.toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', hover]
  have h1 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq hrat hg'P
    (show P.genericPoint ∈ f.toPartialMap.domain from trivial)
  change (g'.hom ≫ fp) ⟨P.genericPoint, hg'P⟩ = (Y.topIso.hom ≫ f) ⟨P.genericPoint, trivial⟩
    at h1
  have h2 : fp (g'.hom ⟨P.genericPoint, hg'P⟩) = Q.genericPoint := by
    rw [← hPQ]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans (h1.trans rfl)
  exact hF P (MMP.Flips.transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hg'P
    (hinjQ _ h2).symm)

/-- A rational map which is a morphism in codimension one is defined at the generic point of
every prime divisor. -/
private theorem definedAt_of_isMorphismInCodimOne {X Y : Scheme.{0}} {φ : X.RationalMap Y}
    (hφ : MMP.Flips.RationalMap.IsMorphismInCodimOne φ) (P : MMP.Mori.PrimeDivisor X) :
    MMP.Mori.RationalMap.DefinedAt φ P.genericPoint := by
  by_contra hP
  exact MMP.Flips.genericPoint_notMem_of_two_le_closedsCodimension _ hφ P hP

/-- **The steps of a program.** A divisorial contraction or a flip `ψ : Y ⤏ Y'` over `W`, with
`W ⟶ T`, is a birational map over `T` creating no divisor. -/
private theorem step_isBirational_isOver {Y Y' W T : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral Y'] [IsLocallyNoetherian Y']
    [IsNormal Y'] [CompactSpace Y'] {sY : Y ⟶ Spec (.of ℂ)} {sY' : Y' ⟶ Spec (.of ℂ)}
    {sW : W ⟶ Spec (.of ℂ)} (hY' : IsNormalVariety ℂ sY') {E : RDivisor Y} {f : Y ⟶ W}
    {fp : Y' ⟶ W} (gW : W ⟶ T) {ψ : Y.RationalMap Y'}
    (hneg : IsNegativeExtremalContraction ℂ sY sW E f)
    (hcase : (IsBirationalMorphism f ∧
        (∃ Ex : MMP.Mori.PrimeDivisor Y, (MMP.Mori.exceptionalSet f : Set Y) = Ex.support) ∧
        IsIso fp ∧ IsModificationOf f fp ψ) ∨ IsFlip ℂ sY sW sY' E f fp ψ) :
    MMP.Mori.RationalMap.IsBirational ψ ∧ MMP.Flips.RationalMap.IsOver (f ≫ gW) (fp ≫ gW) ψ ∧
      ∀ F : MMP.Mori.PrimeDivisor Y', ¬ MMP.Flips.RationalMap.IsInverseExceptional ψ F := by
  have hW := hneg.isNormalVariety_target
  have hYv : IsNormalVariety ℂ (f ≫ sW) := hneg.isContraction.comp_eq ▸ hneg.isNormalVariety_source
  haveI : IsProper f := hneg.isContraction.isProper
  haveI := hW.1
  haveI : CompactSpace W := (quasiCompact_iff_compactSpace sW).mp inferInstance
  haveI := hW.2
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsSeparated sY' := hY'.1.toIsSeparated
  have key : ∀ (hfb : IsBirationalMorphism f) (hmod : IsModificationOf f fp ψ),
      (∀ P : MMP.Mori.PrimeDivisor Y, MMP.Mori.RationalMap.DefinedAt ψ P.genericPoint) →
      (∀ F : MMP.Mori.PrimeDivisor Y', ∃ Q : MMP.Mori.PrimeDivisor W,
        fp F.genericPoint = Q.genericPoint ∧
          ∀ y : Y', fp y = Q.genericPoint → y = F.genericPoint) →
      MMP.Mori.RationalMap.IsBirational ψ ∧
        MMP.Flips.RationalMap.IsOver (f ≫ gW) (fp ≫ gW) ψ ∧
        ∀ F : MMP.Mori.PrimeDivisor Y', ¬ MMP.Flips.RationalMap.IsInverseExceptional ψ F := by
    intro hfb hmod hdef hinj
    refine ⟨hmod.1, ?_, not_isInverseExceptional_of_isOver (sY' := sY') hW hYv hfb hmod.2 hdef
      hinj⟩
    change ψ.compHom (fp ≫ gW) = (f ≫ gW).toRationalMap
    rw [← compHom_compHom', show ψ.compHom fp = f.toRationalMap from hmod.2,
      toRationalMap_compHom']
  rcases hcase with ⟨hfb, -, hiso, hmod⟩ | hfl
  · have hψ : ψ = (f ≫ inv fp).toRationalMap := by
      calc ψ = ψ.compHom (fp ≫ inv fp) := by
            rw [IsIso.hom_inv_id]
            obtain ⟨φ₀, hφ₀⟩ := ψ.exists_rep
            rw [← hφ₀, ← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]
        _ = (f ≫ inv fp).toRationalMap := by
            rw [← compHom_compHom', show ψ.compHom fp = f.toRationalMap from hmod.2,
              toRationalMap_compHom']
    refine key hfb hmod (fun P => ?_) (fun F => ?_)
    · rw [hψ]
      exact MMP.Mori.RationalMap.definedAt_iff.mpr
        ⟨(f ≫ inv fp).toPartialMap, show _ ∈ (⊤ : Y.Opens) from trivial, rfl⟩
    · haveI : IsIso (fp ∣_ ⊤) := inferInstance
      obtain ⟨Q, hQ⟩ := MMP.Flips.exists_primeDivisor_map_genericPoint_eq fp ⊤ F trivial
      refine ⟨Q, hQ, fun y hy => ?_⟩
      have hinj : Function.Injective fp.base := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
        (asIso fp))).injective
      exact hinj (hy.trans hQ.symm)
  · refine key hfl.isSmall_source.isBirationalMorphism hfl.isModificationOf
      (fun P => definedAt_of_isMorphismInCodimOne hfl.isMorphismInCodimOne P) (fun F => ?_)
    obtain ⟨W', hiso, hD, -⟩ := MMP.Flips.exists_isIso_morphismRestrict_of_isSmall hfl.isSmall
    obtain ⟨Q, hQ⟩ := MMP.Flips.exists_primeDivisor_map_genericPoint_eq fp W' F (hD F)
    refine ⟨Q, hQ, fun y hy => ?_⟩
    have hyF : fp y = fp F.genericPoint := hy.trans hQ.symm
    have hyW : y ∈ fp ⁻¹ᵁ W' := by
      change fp y ∈ W'; rw [hyF]; exact hD F
    have hFW : F.genericPoint ∈ fp ⁻¹ᵁ W' := hD F
    have hinj : Function.Injective (fp ∣_ W').base :=
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (asIso (fp ∣_ W')))).injective
    have := @hinj ⟨y, hyW⟩ ⟨F.genericPoint, hFW⟩ (Subtype.ext
      ((AlgebraicGeometry.morphismRestrict_base_coe fp W' ⟨y, hyW⟩).trans
        (hyF.trans (AlgebraicGeometry.morphismRestrict_base_coe fp W' ⟨F.genericPoint, hFW⟩).symm)))
    exact congrArg Subtype.val this

end StepHelpers

/-- The birational transform of an effective divisor is effective. -/
private theorem transformDivisor_nonneg {X Y : Scheme.{0}} {R : Type*} [AddCommMonoid R]
    [PartialOrder R] [IsOrderedAddMonoid R] (φ : X.RationalMap Y) {D : DivisorWithCoeffs R X}
    (h : 0 ≤ D) : 0 ≤ MMP.Mori.RationalMap.transformDivisor φ D := by
  classical
  intro E
  change 0 ≤ (Finsupp.liftAddHom _ D : DivisorWithCoeffs R Y) E
  rw [Finsupp.liftAddHom_apply, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun P _ => ?_
  dsimp only
  rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
  · simp
  · simp only [Option.elim_some, Finsupp.singleAddHom_apply, Finsupp.single_apply]
    split_ifs
    · exact h P
    · exact le_rfl

/-- The birational transform commutes with regarding a `ℚ`-divisor as an `ℝ`-divisor. -/
private theorem transformDivisor_toRDivisor {X Y : Scheme.{0}} (φ : X.RationalMap Y)
    (A : QDivisor X) : MMP.Mori.RationalMap.transformDivisor φ (QDivisor.toRDivisor A) =
      QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor φ A) := by
  classical
  have e : ∀ (Q : MMP.Mori.PrimeDivisor Y) (q : ℚ),
      QDivisor.toRDivisor (Finsupp.single Q q) = Finsupp.single Q (q : ℝ) := fun Q q => by
    ext Γ
    change ((Finsupp.single Q q Γ : ℚ) : ℝ) = Finsupp.single Q (q : ℝ) Γ
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  have e' : ∀ (P : MMP.Mori.PrimeDivisor X) (q : ℚ),
      QDivisor.toRDivisor (Finsupp.single P q) = Finsupp.single P (q : ℝ) := fun P q => by
    ext Γ
    change ((Finsupp.single P q Γ : ℚ) : ℝ) = Finsupp.single P (q : ℝ) Γ
    rw [Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp
  induction A using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add A A' h h' => rw [map_add, map_add, h, h', map_add, map_add]
  | single P q =>
    rw [e', MMP.Mori.RationalMap.transformDivisor_single,
      MMP.Mori.RationalMap.transformDivisor_single]
    rcases MMP.Mori.RationalMap.transformPrimeDivisor φ P with _ | Q
    · simp
    · simp only [Option.elim_some, e]

/-- Along a step of a program, the scaling divisor stays effective. -/
private theorem PStep.nonneg_C {Zb : Scheme.{0}} {M M' : PModel Zb} (st : PStep M M') {lam : ℝ}
    (hst : st.Good lam) (hC : 0 ≤ M.C) : 0 ≤ M'.C := by
  rw [hst.2.2.2.2.2.2.2.2]
  exact transformDivisor_nonneg _ hC

/-- **The big core survives a step.** Along a step of a program over a projective `Zb`, the
birational transform of an effective `ℚ`-divisor big over `Zb` and contained in the boundary is
effective, big over `Zb` and contained in the new boundary. -/
private theorem PStep.exists_big {Zb : Scheme.{0}} (sZb : Zb ⟶ Spec (.of ℂ))
    (hZb : MMP.Mori.IsProjectiveVariety ℂ sZb) {M M' : PModel Zb} (st : PStep M M') {lam : ℝ}
    (hst : st.Good lam) (hM : M.Good sZb) (hM' : M'.Good sZb) (A : QDivisor M.Y)
    (hA0 : ∀ P, 0 ≤ A.coeff P) (hAbig : A.IsRelativelyBig M.π)
    (hAB : QDivisor.toRDivisor A ≤ M.B) :
    ∃ A' : QDivisor M'.Y, (∀ P, 0 ≤ A'.coeff P) ∧ A'.IsRelativelyBig M'.π ∧
      QDivisor.toRDivisor A' ≤ M'.B := by
  obtain ⟨-, -, hfg, hfpg, hneg, -, hcase, hB, -⟩ := hst
  obtain ⟨hπ, hXp, hXq, -, -⟩ := hM
  obtain ⟨hπ', hYp, hYq, -, -⟩ := hM'
  obtain ⟨hbir, hover, hcontr⟩ := step_isBirational_isOver hYq.1 st.g hneg hcase
  rw [hfg, hfpg] at hover
  obtain ⟨h0, -, hbig⟩ := MMP.Fourfold.isRelativelyBig_transformDivisor_of_isBirationalContraction
    M.s M'.s sZb hXq.1 hXp hYq hYp hZb M.π M'.π hπ hπ' st.φ hbir hover hcontr A
    (fun P => hA0 P) (MMP.Fourfold.isQCartier_of_isQFactorial M.s hXq A) hAbig
  refine ⟨MMP.Mori.RationalMap.transformDivisor st.φ A, fun P => h0 P, hbig, ?_⟩
  rw [hB, ← transformDivisor_toRDivisor, ← sub_nonneg, ← map_sub]
  exact transformDivisor_nonneg _ (sub_nonneg.mpr hAB)

/-! ### Strata and the block of a stratum -/

/-- `C = ∑_P (c_P / n_P) (n_P P)` over the components `P` of `C`. -/
private theorem eq_sum (X : Scheme.{0}) [IsLocallyNoetherian X] [IsNormal X] (C : RDivisor X)
    (n : MMP.Mori.PrimeDivisor X → ℕ) (hn : ∀ P, 0 < n P) :
    C = ∑ j : Fin C.support.card, (C (C.support.equivFin.symm j) /
      (n (C.support.equivFin.symm j) : ℝ)) • Divisor.toRDivisor
        (((n (C.support.equivFin.symm j) : ℕ) : ℤ) • Finsupp.single
          (C.support.equivFin.symm j : MMP.Mori.PrimeDivisor X) (1 : ℤ)) := by
  classical
  refine Finsupp.ext fun Γ => ?_
  show C.coeff Γ = DivisorWithCoeffs.coeff (∑ j : Fin C.support.card, (C (C.support.equivFin.symm j) /
      (n (C.support.equivFin.symm j) : ℝ)) • Divisor.toRDivisor
        (((n (C.support.equivFin.symm j) : ℕ) : ℤ) • Finsupp.single
          (C.support.equivFin.symm j : MMP.Mori.PrimeDivisor X) (1 : ℤ))) Γ
  rw [MMP.Flips.coeff_sum_smul_toRDivisor]
  simp only [DivisorWithCoeffs.coeff, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  let g : C.support → ℝ := fun x => C x / (n x : ℝ) *
    ((((n x : ℕ) : ℤ) * (if (x : MMP.Mori.PrimeDivisor X) = Γ then 1 else 0) : ℤ) : ℝ)
  rw [Equiv.sum_comp C.support.equivFin.symm g]
  rw [Finset.sum_coe_sort C.support (fun x => C x / (n x : ℝ) *
    ((((n x : ℕ) : ℤ) * (if x = Γ then 1 else 0) : ℤ) : ℝ))]
  have h : ∀ x ∈ C.support, C x / (n x : ℝ) *
      ((((n x : ℕ) : ℤ) * (if x = Γ then 1 else 0) : ℤ) : ℝ) = if x = Γ then C x else 0 := by
    intro x _
    have : (n x : ℝ) ≠ 0 := by exact_mod_cast (hn x).ne'
    split_ifs with hx
    · push_cast; field_simp
    · simp
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq']
  split_ifs with hΓ
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hΓ).symm ▸ rfl

/-- **An effective restriction of the scaling divisor.** On a `ℚ`-factorial normal `X`, an
effective `ℝ`-divisor `C` not containing the prime divisor `S` has an effective pull-back to a
closed subscheme `T` onto `S`: each component of `C` has a Cartier multiple not containing `S`. -/
private theorem exists_isRCartierPullback_nonneg {X T : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)}
    (hQ : MMP.Fourfold.IsQFactorial sX) [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T]
    (ι : T ⟶ X) [IsClosedImmersion ι] (S : MMP.Mori.PrimeDivisor X)
    (hι : Set.range ι.base = (S.support : Set X)) (C : RDivisor X) (hC : 0 ≤ C)
    (hSC : C.coeff S = 0) :
    ∃ CS : RDivisor T, MMP.Flips.IsRCartierPullback ι C CS ∧ 0 ≤ CS := by
  classical
  choose n hn hnc using fun P : MMP.Mori.PrimeDivisor X => hQ.2 (Finsupp.single P 1)
  set e := C.support.equivFin
  set L : Fin C.support.card → Divisor X := fun j =>
    ((n (e.symm j) : ℕ) : ℤ) • Finsupp.single (e.symm j : MMP.Mori.PrimeDivisor X) (1 : ℤ) with hL
  have hgen : ι (genericPoint T) = S.genericPoint :=
    MMP.CyclicChartDifferent.Aux.map_genericPoint_eq ι S hι
  have hB : ∀ j, ∀ Z : irreducibleComponents T, ι (componentGenericPoint T Z) ∉ (L j).supp := by
    intro j Z hmem
    rw [MMP.Fourfold.componentGenericPoint_eq_genericPoint, hgen] at hmem
    obtain ⟨E, hE, hEx⟩ := DivisorWithCoeffs.mem_supp_iff.mp hmem
    have hE' : E = (e.symm j : MMP.Mori.PrimeDivisor X) := by
      by_contra h
      apply hE
      simp only [hL, DivisorWithCoeffs.coeff, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
      rw [if_neg (Ne.symm h), mul_zero]
    subst hE'
    have hSE := MMP.Flips.eq_of_genericPoint_mem_primeDivisor_support hEx
    have hmemC := (e.symm j).2
    rw [← hSE] at hmemC
    exact Finsupp.mem_support_iff.mp hmemC hSC
  choose L' hL' using fun j => (hnc (e.symm j)).exists_isPullback (hB j)
  refine ⟨∑ j, (C (e.symm j) / (n (e.symm j) : ℝ)) • Divisor.toRDivisor (L' j),
    ⟨_, fun j => C (e.symm j) / (n (e.symm j) : ℝ), L, L', fun j => hnc _, eq_sum X C n hn,
      fun j => ⟨hB j, hL' j⟩, rfl⟩, ?_⟩
  intro E
  change (0 : ℝ) ≤ DivisorWithCoeffs.coeff (∑ j, (C (e.symm j) / (n (e.symm j) : ℝ)) •
    Divisor.toRDivisor (L' j)) E
  rw [MMP.Flips.coeff_sum_smul_toRDivisor]
  refine Finset.sum_nonneg fun j _ => mul_nonneg (div_nonneg (hC _) (Nat.cast_nonneg _)) ?_
  have h := MMP.Fourfold.coeff_nonneg_of_isPullback_of_isEffectiveOn (hnc (e.symm j)) (V := ⊤)
    (fun P _ => by
      simp only [DivisorWithCoeffs.coeff, Finsupp.smul_apply, Finsupp.single_apply,
        smul_eq_mul]
      split_ifs <;> positivity) (hL' j) E
    ⟨E.genericPoint, MMP.Flips.primeDivisor_genericPoint_mem_support E, trivial⟩
  exact_mod_cast h

/-- A model `h : V ⟶ T` of a stratum `T`, with a canonical divisor, a boundary, the restricted
scaling divisor `C_T` and its pull-back. -/
private structure BState (T : Scheme.{0}) where
  V : Scheme.{0}
  [isIntegral : IsIntegral V]
  [compactSpace : CompactSpace V]
  [isLocallyNoetherian : IsLocallyNoetherian V]
  [isNormal : IsNormal V]
  h : V ⟶ T
  KV : Divisor V
  ΔV : RDivisor V
  CS : RDivisor T
  CV : RDivisor V

attribute [local instance] BState.isIntegral BState.compactSpace BState.isLocallyNoetherian
  BState.isNormal

/-- The model of a program over `Zb` given by a model of a stratum `ι : T ⟶ X`. -/
private noncomputable def BState.model {X T Zb : Scheme.{0}} (sX : X ⟶ Spec (.of ℂ)) (ι : T ⟶ X) (π : X ⟶ Zb)
    (s : BState T) : PModel Zb :=
  ⟨s.V, s.h ≫ ι ≫ sX, s.h ≫ ι ≫ π, s.KV, s.ΔV, s.CV⟩

/-- The conditions on a model of a stratum which start a block: a `ℚ`-factorial projective
crepant model of `(T, Δ)` with klt boundary, containing a big effective `ℚ`-divisor, with the
pull-back of the restricted scaling divisor. -/
private def BState.Good {X T Zb : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    (sX : X ⟶ Spec (.of ℂ)) (ι : T ⟶ X) (π : X ⟶ Zb) (C : RDivisor X) (Δ : RDivisor T)
    (s : BState T) : Prop :=
  IsProjectiveMorphism s.h ∧ IsBirationalMorphism s.h ∧
    MMP.Mori.IsProjectiveVariety ℂ (s.h ≫ ι ≫ sX) ∧ IsQFactorial (s.h ≫ ι ≫ sX) ∧
    s.KV.IsCanonicalDivisor (s.h ≫ ι ≫ sX) 3 ∧ 0 ≤ s.ΔV ∧ IsRealKltPair (s.h ≫ ι ≫ sX) s.ΔV ∧
    (∃ KS : Divisor T, (∃ m : ℕ, KS.IsCanonicalDivisor (ι ≫ sX) m) ∧
      MMP.Mori.RationalMap.transformDivisor s.h.toRationalMap s.KV = KS ∧
      MMP.Flips.IsRCartierPullback s.h (MMP.Flips.logCanonicalDivisor KS Δ)
        (MMP.Flips.logCanonicalDivisor s.KV s.ΔV)) ∧
    MMP.Flips.IsRCartierPullback ι C s.CS ∧ MMP.Flips.IsRCartierPullback s.h s.CS s.CV ∧
    0 ≤ s.CV ∧
    ∃ A : QDivisor s.V, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig (s.h ≫ ι ≫ π) ∧
      QDivisor.toRDivisor A ≤ s.ΔV

/-- **The upper level on a model of a stratum.** On a good model of the stratum `T` of `S`, the
upper boundary `Δ_V + λ C_V` is klt and its adjoint is nef over `Zb`: it is the crepant pull-back
of the residue of the plt nef upper level `K_X + B + λ C`. -/
private theorem BState.Good.upper {X T Zb : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [CompactSpace T] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = 4) (K : Divisor X) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (B C : RDivisor X) (lam : ℝ) (hlam : 0 < lam) (π : X ⟶ Zb)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX π
      (MMP.Flips.logCanonicalDivisor K (B + lam • C)))
    (hplt_upper : (∀ P, 0 ≤ (B + lam • C).coeff P ∧ (B + lam • C).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + (B + lam • C)) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX n (B + lam • C) E a → 0 < a)
    (S : MMP.Mori.PrimeDivisor X) (hSB : B.coeff S = 1) (hSC : C.coeff S = 0)
    (ι : T ⟶ X) [IsClosedImmersion ι] (hι : Set.range ι.base = (S.support : Set X))
    (Δ : RDivisor T)
    (hres : ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι ≫ sX) 3 1, IsPoincareResidue sX ι 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback ι (Divisor.toRDivisor (divisorOfForm τ) + B)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ))
    {s : BState T} (hs : s.Good sX ι π C Δ) :
    IsRealKltPair (s.model sX ι π).s ((s.model sX ι π).B + lam • (s.model sX ι π).C) ∧
      MMP.Flips.IsRelativelyNef ℂ (s.model sX ι π).s (s.model sX ι π).π
        (MMP.Flips.logCanonicalDivisor (s.model sX ι π).K
          ((s.model sX ι π).B + lam • (s.model sX ι π).C)) := by
  obtain ⟨hhproj, hhb, -, hVq, hKV3, -, -, ⟨KS, hKS, hKStr, hcrepV⟩, hCS, hCV, -, -⟩ := hs
  have hX : IsNormalVariety ℂ sX := hQ.1
  obtain ⟨hTv, -, hklt⟩ := isRealKltPair_add_smul_of_isPoincareResidue sX hQ hdim K hK B C lam
    hplt_upper S hSB hSC ι hι Δ hres s.CS hCS
  haveI : IsProper s.h := isProper_of_isProjectiveMorphism s.h hhproj
  have hKS3 : KS.IsCanonicalDivisor (ι ≫ sX) 3 := by
    obtain ⟨m, hm⟩ := hKS
    obtain rfl : m = 3 := by
      have := hm.topologicalKrullDim_eq
      rw [topologicalKrullDim_eq_three sX hdim S ι hι] at this
      exact_mod_cast this.symm
    exact hm
  have hG : MMP.Flips.IsRCartierPullback s.h
      (MMP.Flips.logCanonicalDivisor KS (Δ + lam • s.CS))
      (MMP.Flips.logCanonicalDivisor s.KV (s.ΔV + lam • s.CV)) := by
    have := MMP.Fourfold.isRCartierPullback_add hcrepV
      (MMP.Fourfold.isRCartierPullback_smul lam hCV)
    simpa only [MMP.Flips.logCanonicalDivisor, add_assoc] using this
  refine ⟨isRealKltPair_of_isRCartierPullback hTv hKS3 hklt s.h hVq.1 hhb hKV3 hKStr hG, ?_⟩
  have : IsSeparated sX := hX.1.toIsSeparated
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : QuasiCompact (s.h ≫ ι ≫ sX) := hVq.1.1.toQuasiCompact
  have h2 := isRelativelyNef_of_isPoincareResidue sX hX hdim K hK (B + lam • C) π hnef S ι hι hTv
    (Δ + lam • s.CS) (fun τ hτ hτS ρ hρ => by
      have := MMP.Fourfold.isRCartierPullback_add (hres τ hτ hτS ρ hρ)
        (MMP.Fourfold.isRCartierPullback_smul lam hCS)
      simpa only [add_assoc] using this) KS hKS
  exact MMP.Fourfold.isRelativelyNef_of_isRCartierPullback (𝟙 Zb) (ι ≫ π) (s.h ≫ ι ≫ π) s.h
    (by simp) h2 hG

/-- A pull-back of an `ℝ`-Cartier divisor along `f` is numerically trivial over `f`. -/
private theorem isNumericallyTrivialOver_of_isRCartierPullback {X Z : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian Z] [IsNormal Z]
    (sX : X ⟶ Spec (.of ℂ)) (sZ : Z ⟶ Spec (.of ℂ)) (hZ : IsNormalVariety ℂ sZ) (f : X ⟶ Z)
    (hf : f ≫ sZ = sX) {D : RDivisor Z} {G : RDivisor X} (hD : IsRCartierPullback f D G) :
    IsNumericallyTrivialOver ℂ sX f G := by
  haveI : QuasiCompact sX := by rw [← hf]; haveI := hZ.1.toQuasiCompact; infer_instance
  have hGc : IsCartierCombination G := by
    obtain ⟨m, r, L, L', hLc, -, hpb, hG⟩ := hD
    refine ⟨m, r, L', fun j => (hpb j).2.isCartier (hLc j), ?_⟩
    rw [hG]; simp only [MMP.Flips.toRDivisor_eq_mapCoeffs]
  refine ⟨hGc, ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩, ?_⟩
  intro γ hγ m₁ r₁ L₁ x₁ m₂ r₂ L₂ x₂ h₁ h₂
  obtain ⟨heq, -⟩ := MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX γ
  obtain ⟨m, r, L, h0⟩ := isRIntersectionNumber_zero_of_isRCartierPullback sX sZ hZ f hf hD γ hγ
  rw [heq _ _ _ _ _ _ _ h₁ h0, heq _ _ _ _ _ _ _ h₂ (isRIntersectionNumber_zero_divisor sX γ)]

/-- A birational morphism followed by an isomorphism is birational. -/
private theorem isBirationalMorphism_comp_isIso {X Y Y' : Scheme.{0}} (g : X ⟶ Y) (e : Y ⟶ Y')
    [IsIso e] (hg : IsBirationalMorphism g) : IsBirationalMorphism (g ≫ e) := by
  obtain ⟨U, hU, hUi⟩ :=
    MMP.Fourfold.Oai4C1.CommonModel.exists_isOpenImmersion_of_isBirationalMorphism hg
  haveI := hg.isDominant
  haveI : IsOpenImmersion (U.ι ≫ g ≫ e) := by rw [← Category.assoc]; infer_instance
  exact MMP.Fourfold.Oai4C1.CommonModel.isBirationalMorphism_of_isOpenImmersion (g ≫ e) U hU

/-- **The stratum map of a flip.** For a step `X ⟶ Z ⟵ X⁺` of a real flip sequence retaining the
prime divisor `S` as `S⁺`, the flip induces a birational map `S ⤏ S⁺` over `Z`: both map
birationally onto the common scheme-theoretic image of `S` and `S⁺` in `Z`. -/
private theorem exists_stratum_rationalMap {X Xp Zi : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsLocallyNoetherian Zi] [IsNormal Zi]
    (sX : X ⟶ Spec (.of ℂ)) (sZi : Zi ⟶ Spec (.of ℂ)) (sXp : Xp ⟶ Spec (.of ℂ))
    (K : Divisor X) (B : RDivisor X) (Kp : Divisor Xp) (Bp : RDivisor Xp) (f : X ⟶ Zi)
    (fp : Xp ⟶ Zi) (hflip : IsRealFlipStep sX sZi sXp K B Kp Bp f fp)
    (S : MMP.Mori.PrimeDivisor X) (Sp : MMP.Mori.PrimeDivisor Xp)
    (hS : flipTransformPrimeDivisor f fp S = some Sp) :
    ∃ φ : S.idealSheaf.subscheme.RationalMap Sp.idealSheaf.subscheme,
      MMP.Mori.RationalMap.IsBirational φ ∧
      φ.compHom (Sp.idealSheaf.subschemeι ≫ fp) = (S.idealSheaf.subschemeι ≫ f).toRationalMap := by
  classical
  have hZ : IsNormalVariety ℂ sZi := hflip.isNegativeExtremalContraction.isNormalVariety_target
  haveI : IsProper f := hflip.isSmall.isProper
  haveI : IsProper fp := hflip.isSmall_flip.isProper
  haveI : IsSeparated sZi := hZ.1.toIsSeparated
  haveI := isSeparated_toTerminal sZi
  obtain ⟨V, hfV, hfpV, hXV, hXpV⟩ := MMP.Fourfold.IsRealFlipStep.exists_opens_isIso hflip
  haveI := hfV
  haveI := hfpV
  have hSgen : fp Sp.genericPoint = f S.genericPoint := by
    obtain ⟨Pp, hPp⟩ := exists_primeDivisor_map_genericPoint_eq f fp V hXV S
    have h := flipTransformPrimeDivisor_eq_some_of_map_genericPoint_eq f fp V hXV hPp
    rw [hS] at h
    cases Option.some.inj h
    exact hPp
  haveI := S.integral
  haveI := Sp.integral
  set h₁ := S.idealSheaf.subschemeι ≫ f with hh₁
  set h₂ := Sp.idealSheaf.subschemeι ≫ fp with hh₂
  have hb₁ := MMP.Flips.isBirationalMorphism_toImage_subschemeι_comp f V S
    (hXV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint S).le)
  have hb₂ := MMP.Flips.isBirationalMorphism_toImage_subschemeι_comp fp V Sp
    (hXpV _ (AlgebraicGeometry.PrimeDivisor.coheight_genericPoint Sp).le)
  have hk : h₂.ker = h₁.ker := by
    rw [hh₁, hh₂, MMP.Flips.ker_subschemeι_comp,
      MMP.Flips.ker_subschemeι_comp, hSgen]
  have hk₁ : h₁.imageι.ker = h₁.ker := Scheme.IdealSheafData.ker_subschemeι _
  have hk₂ : h₂.imageι.ker = h₂.ker := Scheme.IdealSheafData.ker_subschemeι _
  have hki : h₂.imageι.ker = h₁.imageι.ker := by rw [hk₁, hk₂, hk]
  -- the two images are identified over `Z`
  set e := IsClosedImmersion.lift h₂.imageι h₁.imageι hki.le with he
  haveI : IsIso e := IsClosedImmersion.isIso_lift h₂.imageι h₁.imageι hki
  have hef : e ≫ h₂.imageι = h₁.imageι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsSeparated (h₂.image ↘ Limits.terminal Scheme) := isSeparated_toTerminal (h₂.imageι ≫ sZi)
  obtain ⟨φ, hφ, hφc⟩ := exists_isBirational_compHom_eq (h₁.toImage ≫ e) h₂.toImage
    (isBirationalMorphism_comp_isIso h₁.toImage e hb₁) hb₂
  refine ⟨φ, hφ, ?_⟩
  calc φ.compHom h₂ = φ.compHom (h₂.toImage ≫ h₂.imageι) := by rw [Scheme.Hom.toImage_imageι]
    _ = (φ.compHom h₂.toImage).compHom h₂.imageι := (compHom_compHom' _ _ _).symm
    _ = (h₁.toImage ≫ e ≫ h₂.imageι).toRationalMap := by
        rw [hφc, toRationalMap_compHom', Category.assoc]
    _ = h₁.toRationalMap := by rw [hef, Scheme.Hom.toImage_imageι]

/-- A proper birational morphism is surjective. -/
private theorem surjective_of_isProper_of_isBirationalMorphism {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsProper f] (hf : IsBirationalMorphism f) : Surjective f := by
  haveI := hf.isDominant
  have hr : Set.range f.base = Set.univ := by
    rw [← f.isClosedMap.isClosed_range.closure_eq]; exact f.denseRange.closure_range
  exact ⟨fun y => hr.ge (Set.mem_univ y)⟩

/-- **The sign of the residue adjoint on a contracted curve of the stratum.** Let `T ⟶ X` be the
normal stratum of a prime divisor `S` of a projective fourfold, with residue different `Δ` of
`B`, and `f : X ⟶ Z`. If `s · ((K_X + B) · γ) > 0` for every proper curve `γ` contracted by `f`
(for some presentation), then `s · ((K_T + Δ) · c) > 0` for every proper curve `c` of `T`
contracted by `T ⟶ Z`, for every canonical divisor `K_T` and every presentation. -/
private theorem pos_mul_of_isPoincareResidue {X T Zi : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] (hproj : MMP.Mori.IsProjectiveVariety ℂ sX)
    (hdim : topologicalKrullDim X = 4) (K : Divisor X) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (B : RDivisor X) (f : X ⟶ Zi) (s : ℝ)
    (hsign : ∀ γ : ProperCurve sX, γ.IsContractedBy f → ∃ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor X) (x : ℝ),
      IsRIntersectionNumber ℂ sX (logCanonicalDivisor K B) r L γ x ∧ 0 < s * x)
    (S : MMP.Mori.PrimeDivisor X) [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T]
    [IsNormal T] (ι : T ⟶ X) [IsClosedImmersion ι] (hι : Set.range ι.base = (S.support : Set X))
    (hT : IsNormalVariety ℂ (ι ≫ sX)) (Δ : RDivisor T)
    (hres : ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι ≫ sX) 3 1, IsPoincareResidue sX ι 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback ι (Divisor.toRDivisor (divisorOfForm τ) + B)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ))
    (KS : Divisor T) (hKS : ∃ m : ℕ, KS.IsCanonicalDivisor (ι ≫ sX) m)
    (c : ProperCurve (ι ≫ sX)) (hc : c.IsContractedBy (ι ≫ f)) {m : ℕ} (r : Fin m → ℝ)
    (L : Fin m → Divisor T) {x : ℝ}
    (hx : IsRIntersectionNumber ℂ (ι ≫ sX) (logCanonicalDivisor KS Δ) r L c x) : 0 < s * x := by
  classical
  haveI : IsSeparated sX := hproj.1.toIsSeparated
  haveI : QuasiCompact sX := hproj.1.toQuasiCompact
  have hX : IsNormalVariety ℂ sX := ⟨hproj.1, inferInstance⟩
  haveI : QuasiCompact (ι ≫ sX) := hT.1.toQuasiCompact
  have hdimT := topologicalKrullDim_eq_three sX hdim S ι hι
  -- a form with a simple pole along `S`, and its residue
  obtain ⟨Q⟩ := MMP.Positivity.nonempty_primeDivisor_of_topologicalKrullDim_eq hdimT (by norm_num)
  obtain ⟨τ, hτ0, hτS, ρ, hρ, hρ0⟩ := MMP.Fourfold.exists_ordForm_eq_neg_one_isPoincareResidue sX
    hX (n := 3) (by rw [hdim]; rfl) ι hT S hι Q
  have hR := hres τ hτ0 hτS ρ hρ
  -- `div τ ∼ K` and `div ρ ∼ K_T`
  obtain ⟨mK, hmK⟩ := hK
  have hdX : topologicalKrullDim X = ((3 + 1 : ℕ) : WithBot ℕ∞) := by rw [hdim]; rfl
  have hK' : K.IsCanonicalDivisor sX (3 + 1) := by
    obtain rfl : mK = 3 + 1 := by
      have := hmK.topologicalKrullDim_eq
      rw [hdX] at this
      exact_mod_cast this.symm
    exact hmK
  have hτK : (divisorOfForm τ - K).LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hX hK' hτ0
    exact ⟨φ, by rw [sub_zero, ← hφ, one_smul]⟩
  have hρK : (KS - divisorOfForm ρ).LinearlyEquivalent 0 := by
    obtain ⟨mS, hmS⟩ := hKS
    have hKS' : KS.IsCanonicalDivisor (ι ≫ sX) 3 := by
      obtain rfl : mS = 3 := by
        have := hmS.topologicalKrullDim_eq
        rw [hdimT] at this
        exact_mod_cast this.symm
      exact hmS
    obtain ⟨φ, hφ⟩ := (MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hT hKS' hρ0).symm
    exact ⟨φ, by rw [sub_zero, ← hφ, one_smul]⟩
  -- the image curve of `c` in `X`, contracted by `f`
  have hcι : ¬ c.IsContractedBy ι := by
    intro h
    apply ProperCurve.closure_point_ne_singleton c c.point
    ext z
    refine ⟨fun hz => ι.isClosedEmbedding.injective (h z hz), fun hz => ?_⟩
    rw [Set.mem_singleton_iff] at hz
    exact hz ▸ subset_closure rfl
  set c' : ProperCurve sX := ⟨ι c.point, MMP.Fourfold.Oai4C1.isProperCurve_map ι rfl c hcι⟩
  have hc' : c'.IsContractedBy f := by
    intro z hz
    have hz' : z ∈ ι.base '' closure {c.point} := by
      rw [← ι.isClosedMap.closure_image_eq_of_continuous ι.continuous, Set.image_singleton]
      exact hz
    obtain ⟨w, hw, rfl⟩ := hz'
    simpa only [Scheme.Hom.comp_apply] using hc w hw
  obtain ⟨m₁, r₁, L₁, L₁', y, hxy, hy⟩ :=
    exists_isRIntersectionNumber_of_isRCartierPullback (ι ≫ sX) sX ι rfl hR c c' rfl
  have hd := residueFieldDegree_pos_of_not_isContractedBy hproj ι rfl c hcι
  -- `(div τ + B) · c' = (K + B) · c'`
  obtain ⟨m₂, r₂, L₂, x₂, h₂, hs₂⟩ := hsign c' hc'
  have hcτ : (divisorOfForm τ - K).IsCartier :=
    Divisor.IsCartier.of_linearlyEquivalent hτK Divisor.isCartier_zero
  have h₃ := isRIntersectionNumber_sum_degreeOn sX c' (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => divisorOfForm τ - K) (fun _ => hcτ)
  rw [show ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor (divisorOfForm τ - K) =
    Divisor.toRDivisor (divisorOfForm τ - K) by simp] at h₃
  have h₃0 := MMP.Flips.eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hτK c' h₃
  obtain ⟨heq, hlin⟩ := MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ sX c'
  have hsum := hlin _ _ _ _ _ _ _ _ 1 1 h₂ h₃
  rw [show (1 : ℝ) • logCanonicalDivisor K B + (1 : ℝ) • Divisor.toRDivisor (divisorOfForm τ - K) =
      Divisor.toRDivisor (divisorOfForm τ) + B by
    simp only [one_smul, logCanonicalDivisor, map_sub]; abel] at hsum
  have hyv := heq _ _ _ _ _ _ _ hy hsum
  -- `(K_T + Δ) · c = (div ρ + Δ) · c`
  have hcρ : (KS - divisorOfForm ρ).IsCartier :=
    Divisor.IsCartier.of_linearlyEquivalent hρK Divisor.isCartier_zero
  have h₄ := isRIntersectionNumber_sum_degreeOn (ι ≫ sX) c (fun _ : Fin 1 => (1 : ℝ))
    (fun _ => KS - divisorOfForm ρ) (fun _ => hcρ)
  rw [show ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor (KS - divisorOfForm ρ) =
    Divisor.toRDivisor (KS - divisorOfForm ρ) by simp] at h₄
  have h₄0 := MMP.Flips.eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hρK c h₄
  obtain ⟨heqT, hlinT⟩ := MMP.Flips.IsRIntersectionNumber.eq_and_linear ℂ (ι ≫ sX) c
  have hsumT := hlinT _ _ _ _ _ _ _ _ 1 1 hxy h₄
  rw [show (1 : ℝ) • (Divisor.toRDivisor (divisorOfForm ρ) + Δ) +
      (1 : ℝ) • Divisor.toRDivisor (KS - divisorOfForm ρ) = logCanonicalDivisor KS Δ by
    simp only [one_smul, logCanonicalDivisor, map_sub]; abel] at hsumT
  have hxv := heqT _ _ _ _ _ _ _ hx hsumT
  rw [hxv, h₄0, hyv, h₃0]
  have hd' : (0 : ℝ) < residueFieldDegree ι c.point := by exact_mod_cast hd
  have := mul_pos hd' hs₂
  nlinarith

/-- **A crepant roof over an empty block.** Let `X ⟶ Z ⟵ X⁺` be a step of a real flip sequence
retaining `S` as `S⁺`, with normal strata `T`, `T⁺` carrying the residue differents `Δ`, `Δ⁺`. If
one model `V` maps crepantly, by projective birational morphisms over `Z`, to both `(T, Δ)` and
`(T⁺, Δ⁺)`, then no proper curve of `S` is contracted by `f` and none of `S⁺` by `f⁺`: on a lift
of such a curve to `V` the common adjoint would be both negative and nonnegative. -/
private theorem forall_not_isContractedBy_of_crepant {X Xp Zi : Scheme.{0}} [IsIntegral X]
    [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsLocallyNoetherian Zi] [IsNormal Zi]
    (sX : X ⟶ Spec (.of ℂ)) (sZi : Zi ⟶ Spec (.of ℂ)) (sXp : Xp ⟶ Spec (.of ℂ))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sXp]
    (K : Divisor X) (B : RDivisor X) (Kp : Divisor Xp) (Bp : RDivisor Xp) (f : X ⟶ Zi)
    (fp : Xp ⟶ Zi) (hflip : IsRealFlipStep sX sZi sXp K B Kp Bp f fp)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hprojp : MMP.Mori.IsProjectiveVariety ℂ sXp)
    (hdim : topologicalKrullDim X = 4) (hdimp : topologicalKrullDim Xp = 4)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hQ : IsQFactorial sX) (hQp : IsQFactorial sXp)
    (S : MMP.Mori.PrimeDivisor X) (Sp : MMP.Mori.PrimeDivisor Xp)
    {T Tp : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T] [IsNormal T]
    [IsIntegral Tp] [IsLocallyNoetherian Tp] [CompactSpace Tp] [IsNormal Tp]
    (ι : T ⟶ X) (ιp : Tp ⟶ Xp) [IsClosedImmersion ι] [IsClosedImmersion ιp]
    (hι : Set.range ι.base = (S.support : Set X)) (hιp : Set.range ιp.base = (Sp.support : Set Xp))
    (Δ : RDivisor T) (Δp : RDivisor Tp)
    (hres : ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι ≫ sX) 3 1, IsPoincareResidue sX ι 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback ι (Divisor.toRDivisor (divisorOfForm τ) + B)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ))
    (hresp : ∀ τ : RationalPluriForms sXp (3 + 1) 1, τ ≠ 0 → Sp.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ιp ≫ sXp) 3 1, IsPoincareResidue sXp ιp 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback ιp (Divisor.toRDivisor (divisorOfForm τ) + Bp)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δp))
    (hTv : IsNormalVariety ℂ (ι ≫ sX)) (hTpv : IsNormalVariety ℂ (ιp ≫ sXp))
    {V : Scheme.{0}} [IsIntegral V] [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V]
    (h : V ⟶ T) (hp : V ⟶ Tp) (hhproj : IsProjectiveMorphism h) (hhb : IsBirationalMorphism h)
    (hpproj : IsProjectiveMorphism hp) (hpb : IsBirationalMorphism hp)
    (hV : IsNormalVariety ℂ (h ≫ ι ≫ sX)) (hcomm : hp ≫ ιp ≫ fp = h ≫ ι ≫ f)
    (KV : Divisor V) (ΔV : RDivisor V)
    (hcr : ∃ KS : Divisor T, (∃ m : ℕ, KS.IsCanonicalDivisor (ι ≫ sX) m) ∧
      IsRCartierPullback h (logCanonicalDivisor KS Δ) (logCanonicalDivisor KV ΔV))
    (hcrp : ∃ KSp : Divisor Tp, (∃ m : ℕ, KSp.IsCanonicalDivisor (ιp ≫ sXp) m) ∧
      IsRCartierPullback hp (logCanonicalDivisor KSp Δp) (logCanonicalDivisor KV ΔV)) :
    (∀ γ : ProperCurve sX, closure {γ.point} ⊆ (S.support : Set X) → ¬ γ.IsContractedBy f) ∧
      ∀ γ : ProperCurve sXp, closure {γ.point} ⊆ (Sp.support : Set Xp) →
        ¬ γ.IsContractedBy fp := by
  classical
  have hX : IsNormalVariety ℂ sX := hQ.1
  have hXp : IsNormalVariety ℂ sXp := hQp.1
  have hfT : f ≫ sZi = sX := hflip.isSmall.comp_eq
  have hfpT : fp ≫ sZi = sXp := hflip.isSmall_flip.comp_eq
  obtain ⟨KS, hKS, hG⟩ := hcr
  obtain ⟨KSp, hKSp, hGp⟩ := hcrp
  haveI : IsProper h := isProper_of_isProjectiveMorphism h hhproj
  haveI : IsProper hp := isProper_of_isProjectiveMorphism hp hpproj
  haveI : Surjective h := surjective_of_isProper_of_isBirationalMorphism h hhb
  haveI : Surjective hp := surjective_of_isProper_of_isBirationalMorphism hp hpb
  have hTproj : MMP.Mori.IsProjectiveVariety ℂ (ι ≫ sX) := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hproj
    exact isProjectiveVariety_comp_of_isFinite sX ι hTv.1
  have hTpproj : MMP.Mori.IsProjectiveVariety ℂ (ιp ≫ sXp) := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sXp := hprojp
    exact isProjectiveVariety_comp_of_isFinite sXp ιp hTpv.1
  have hhp : hp ≫ ιp ≫ sXp = h ≫ ι ≫ sX := by
    rw [← hfpT, ← hfT, reassoc_of% hcomm]
  -- the residue adjoints are negative, resp. positive, on the contracted curves of the strata
  have hnegT : ∀ c : ProperCurve (ι ≫ sX), c.IsContractedBy (ι ≫ f) → ∀ (m : ℕ) (r : Fin m → ℝ)
      (L : Fin m → Divisor T) (x : ℝ),
      IsRIntersectionNumber ℂ (ι ≫ sX) (logCanonicalDivisor KS Δ) r L c x → x < 0 := by
    intro c hc m r L x hx
    have := pos_mul_of_isPoincareResidue sX hproj hdim K hK B f (-1) (fun γ hγ => by
        haveI : QuasiCompact sX := hproj.1.toQuasiCompact
        obtain ⟨m, r, L, p, hp, hp0⟩ := exists_isRIntersectionNumber_pos_of_isRelativelyAmple sX f
          hflip.isNegativeExtremalContraction.isRelativelyAntiAmple γ hγ
        obtain ⟨m', r', L', y, hy, rfl⟩ := neg_of_isRIntersectionNumber_neg sX
          (isCartierCombination_of_isQFactorial hQ _) γ hp
        exact ⟨m', r', L', y, hy, by linarith⟩)
      S ι hι hTv Δ hres KS hKS c hc r L hx
    linarith
  have hposTp : ∀ c : ProperCurve (ιp ≫ sXp), c.IsContractedBy (ιp ≫ fp) → ∀ (m : ℕ)
      (r : Fin m → ℝ) (L : Fin m → Divisor Tp) (x : ℝ),
      IsRIntersectionNumber ℂ (ιp ≫ sXp) (logCanonicalDivisor KSp Δp) r L c x → 0 < x := by
    intro c hc m r L x hx
    have hKp := hflip.isCanonicalDivisor_flip
    have := pos_mul_of_isPoincareResidue sXp hprojp hdimp Kp hKp Bp fp 1 (fun γ hγ => by
        haveI : QuasiCompact sXp := hprojp.1.toQuasiCompact
        obtain ⟨m, r, L, p, hp, hp0⟩ := exists_isRIntersectionNumber_pos_of_isRelativelyAmple sXp
          fp hflip.isRelativelyAmple_flip γ hγ
        exact ⟨m, r, L, p, hp, by linarith⟩)
      Sp ιp hιp hTpv Δp hresp KSp hKSp c hc r L hx
    linarith
  obtain ⟨hnoT, hnoTp⟩ := forall_not_isContractedBy_of_isRCartierPullback (h ≫ ι ≫ sX) (ι ≫ sX)
    (ιp ≫ sXp) hV hTproj hTpproj (ι ≫ f) (ιp ≫ fp) h hp rfl hhp hcomm.symm hG hGp hnegT hposTp
  -- a contracted curve of `S` lifts to the stratum
  have lift : ∀ {Y Tl Zl : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) (j : Tl ⟶ Y) [IsClosedImmersion j]
      (u : Y ⟶ Zl) (P : MMP.Mori.PrimeDivisor Y) (_ : Set.range j.base = (P.support : Set Y)),
      (∀ c : ProperCurve (j ≫ sY), ¬ c.IsContractedBy (j ≫ u)) →
      ∀ γ : ProperCurve sY, closure {γ.point} ⊆ (P.support : Set Y) → ¬ γ.IsContractedBy u := by
    intro Y Tl Zl sY j _ u P hj hno γ hγS hγu
    obtain ⟨t, ht⟩ : γ.point ∈ Set.range j.base := hj ▸ hγS (subset_closure rfl)
    have hc : IsProperCurve (j ≫ sY) t :=
      (MMP.Chow.FixedDegreeCurveCyclesProof.isProperCurve_comp_iff j sY t).mpr
        (by rw [ht]; exact γ.isProperCurve)
    refine hno ⟨t, hc⟩ fun z hz => ?_
    have hz' : j z ∈ closure {γ.point} := by
      rw [← ht, ← Set.image_singleton]
      exact image_closure_subset_closure_image j.continuous ⟨z, hz, rfl⟩
    simp only [Scheme.Hom.comp_apply]
    rw [hγu _ hz', ← ht]
  exact ⟨lift sX ι f S hι hnoT, lift sXp ιp fp Sp hιp hnoTp⟩

/-- Two bundled models with the same underlying scheme and equal data are equal. -/
private theorem PModel.mk_eq {Zb : Scheme.{0}} {Y : Scheme.{0}} [IsIntegral Y] [CompactSpace Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {s s' : Y ⟶ Spec (.of ℂ)} {π π' : Y ⟶ Zb}
    {K K' : Divisor Y} {B B' C C' : RDivisor Y} (hs : s = s') (hπ : π = π') (hK : K = K')
    (hB : B = B') (hC : C = C') :
    (⟨Y, s, π, K, B, C⟩ : PModel Zb) = ⟨Y, s', π', K', B', C'⟩ := by
  subst hs hπ hK hB hC; rfl

/-- **A big divisor is big over every projective base.** On a projective variety `V`, a
`ℚ`-divisor big over the point is big over every morphism `π : V ⟶ Z` to a projective variety:
a multiple is linearly equivalent to an ample plus an effective divisor, and an ample divisor is
`π`-ample. -/
private theorem isRelativelyBig_of_isRelativelyBig_structure {V Zb : Scheme.{0}} [IsIntegral V]
    [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V] (sV : V ⟶ Spec (.of ℂ))
    (hV : MMP.Mori.IsProjectiveVariety ℂ sV) (sZb : Zb ⟶ Spec (.of ℂ))
    (hZb : MMP.Mori.IsProjectiveVariety ℂ sZb) (π : V ⟶ Zb) (hπ : π ≫ sZb = sV)
    {A : QDivisor V} (hA : A.IsRelativelyBig sV) : A.IsRelativelyBig π := by
  obtain ⟨m, hm, D, hDm, hDc, hDbig⟩ := hA
  obtain ⟨Cc, ⟨e⟩⟩ := MMP.Mori.exists_sheaf_iso_divisorialSheaf hDc
  have h1 := (MMP.Mori.Divisor.isRelativelyBig_iff_isRelativelyBigCartier sV hDc e).1 hDbig
  haveI : MMP.Mori.IsProjectiveVariety ℂ sV := hV
  haveI : MMP.Mori.IsProjectiveVariety ℂ sZb := hZb
  haveI : MMP.Mori.IsProjectiveVariety ℂ (𝟙 (Spec (.of ℂ))) :=
    (AlgebraicGeometry.isProjectiveVariety_iff ℂ _).mpr
      ⟨by constructor <;> infer_instance, isProjectiveMorphism_id _⟩
  obtain ⟨m', hm', Am, Em, hAm, hEm, hlin⟩ :=
    (MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sV (𝟙 _) sV
      (Category.comp_id _) Cc).1 h1
  haveI : IsSeparated sZb := hZb.1.toIsSeparated
  haveI : IsProper sV := isProper_of_isProjectiveMorphism sV hV.isProjective
  haveI : IsProper (π ≫ sZb) := hπ ▸ inferInstance
  haveI : IsProper π := IsProper.of_comp π sZb
  haveI : QuasiCompact sV := inferInstance
  have hAmπ : MMP.Mori.IsRelativelyAmple π (MMP.CartierDivisor.sheaf Am) := by
    have h2 := MMP.Mori.IsRelativelyAmple.to_stacks hAm
    rw [← hπ] at h2
    exact MMP.Mori.IsRelativelyAmple.of_stacks π _
      (Stacks.RelativeAmpleComposition.isRelativelyAmple_of_comp_of_isAffine π sZb _ h2
        inferInstance)
  have h3 := (MMP.Mori.isRelativelyBigCartier_iff_exists_linearlyEquivalent_add sV sZb π hπ
    Cc).2 ⟨m', hm', Am, Em, hAmπ, hEm, hlin⟩
  exact ⟨m, hm, D, hDm, hDc, (MMP.Mori.Divisor.isRelativelyBig_iff_isRelativelyBigCartier π hDc
    e).2 h3⟩

/-- A proper birational morphism `p : V ⟶ T` onto a normal scheme which contracts no prime divisor
maps the generic point of every prime divisor of `V` to the generic point of a prime divisor of
`T`. -/
private theorem exists_primeDivisor_map_genericPoint_eq_of_not_isExceptional {V T : Scheme.{0}}
    [IsIntegral V] [IsIntegral T] [IsLocallyNoetherian T] [IsNormal T]
    [IsSeparated (T ↘ Limits.terminal Scheme)] (p : V ⟶ T) [IsProper p]
    (hpb : IsBirationalMorphism p) (F : MMP.Mori.PrimeDivisor V)
    (hF : ¬ MMP.Mori.RationalMap.IsExceptional (X := V) p.toRationalMap F) :
    ∃ Q : MMP.Mori.PrimeDivisor T, p F.genericPoint = Q.genericPoint := by
  classical
  -- the transform of `F` lies in the closure of `p(η_F)`
  have hsub : ((MMP.Mori.RationalMap.transform p.toRationalMap F.idealSheaf.support :
      TopologicalSpace.Closeds T) : Set T) ⊆
      closure {p F.genericPoint} := by
    refine closure_minimal (Set.iUnion_subset fun g => ?_) isClosed_closure
    rintro _ ⟨z, hz, rfl⟩
    have h1 : g.1.hom z = p.toPartialMap.hom ⟨z.1, trivial⟩ :=
      MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
        (g' := p.toPartialMap) g.2 z.2 (show z.1 ∈ p.toPartialMap.domain from trivial)
    rw [h1]
    change p z.1 ∈ closure {p F.genericPoint}
    have hzF : z.1 ∈ closure {F.genericPoint} := by
      rw [← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact hz
    rw [← Set.image_singleton]
    exact image_closure_subset_closure_image p.continuous ⟨z.1, hzF, rfl⟩
  have hle : Order.coheight (p F.genericPoint) ≤ 1 := by
    by_contra h2
    push Not at h2
    apply hF
    refine MMP.Mori.RationalMap.isExceptional_iff.mpr fun _ => ?_
    rw [MMP.Flips.le_closedsCodimension_iff_le_coheight]
    intro x hx
    have hxs : x ≤ p F.genericPoint := specializes_iff_mem_closure.mpr (hsub hx)
    exact (Order.add_one_le_of_lt h2).trans (Order.coheight_anti hxs)
  have hcoh : Order.coheight (p F.genericPoint) = 1 := by
    rw [MMP.Positivity.coheight_map_of_mem_biregularLocus p
      (MMP.Spreading.mem_biregularLocus_of_coheight_le_one_of_isNormal p hpb hle),
      AlgebraicGeometry.PrimeDivisor.coheight_genericPoint]
  exact ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hcoh,
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hcoh).symm⟩

/-- Composing a rational map with the identity. -/
private theorem compHom_id' {X Y : Scheme.{0}} (φ : X.RationalMap Y) : φ.compHom (𝟙 Y) = φ := by
  obtain ⟨φ₀, rfl⟩ := φ.exists_rep
  rw [← Scheme.RationalMap.compHom_toRationalMap, Scheme.PartialMap.compHom_id]

/-- **The big core on a small model of the stratum.** Let `S` be the retained component of a
real plt `ℚ`-factorial projective fourfold, `T` its normal stratum with residue different `Δ`,
and `p : V ⟶ T` a small projective birational morphism from a `ℚ`-factorial projective `V`. The
transform of the reference ample divisor restricts to an effective `ℚ`-divisor on `T`, big and
below `Δ`; its strict transform on `V` is effective, big over `Zb` and below `p⁻¹_* Δ`. -/
private theorem exists_bigCore {X Zb : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = 4) (K : Divisor X) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (B : RDivisor X) (hplt : (∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + B) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX n B E a → 0 < a)
    (π : X ⟶ Zb) (sZb : Zb ⟶ Spec (.of ℂ))
    (hZb : MMP.Mori.IsProjectiveVariety ℂ sZb) (hπ : π ≫ sZb = sX)
    (S : MMP.Mori.PrimeDivisor X) (hSB : B.coeff S = 1)
    [IsIntegral S.idealSheaf.subscheme] [IsLocallyNoetherian S.idealSheaf.subscheme]
    [CompactSpace S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
    (Δ : RDivisor S.idealSheaf.subscheme)
    (hres : ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (S.idealSheaf.subschemeι ≫ sX) 3 1,
        IsPoincareResidue sX S.idealSheaf.subschemeι 3 1 τ ρ →
          MMP.Flips.IsRCartierPullback S.idealSheaf.subschemeι
            (Divisor.toRDivisor (divisorOfForm τ) + B) (Divisor.toRDivisor (divisorOfForm ρ) + Δ))
    (X₀ : Scheme.{0}) [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    (sX₀ : X₀ ⟶ Spec (.of ℂ)) (hX₀ : IsNormalVariety ℂ sX₀)
    (hX₀p : MMP.Mori.IsProjectiveVariety ℂ sX₀)
    (S₀ : MMP.Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (A₀ : QDivisor X₀) (hA₀ : 0 ≤ A₀) (hAamp : A₀.IsAmple) (hAS : A₀.coeff S₀ = 0)
    (ψ : X₀.RationalMap X) (ψinv : X.RationalMap X₀)
    (hψ : MMP.Mori.RationalMap.IsInverse ψ ψinv)
    (hψk : MMP.Flips.RationalMap.IsOver sX₀ sX ψ)
    (hψinvk : MMP.Flips.RationalMap.IsOver sX sX₀ ψinv)
    (hψS : MMP.Mori.RationalMap.transformPrimeDivisor ψ S₀ = some S)
    (hord : ∀ F : MMP.Mori.PrimeDivisor X,
      MMP.Flips.RationalMap.IsInverseExceptional ψ F →
      ∀ q : X.PartialMap X₀, q.toRationalMap = ψinv → ∀ hF : F.genericPoint ∈ q.domain,
        q.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀))
    (hAB : QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor ψ A₀) ≤
      B - Finsupp.single S 1)
    {V : Scheme.{0}} [IsIntegral V] [IsLocallyNoetherian V] [IsNormal V] [CompactSpace V]
    (p : V ⟶ S.idealSheaf.subscheme) (hpproj : IsProjectiveMorphism p)
    (hpb : IsBirationalMorphism p) (hVq : IsQFactorial (p ≫ S.idealSheaf.subschemeι ≫ sX))
    (hVproj : MMP.Mori.IsProjectiveVariety ℂ (p ≫ S.idealSheaf.subschemeι ≫ sX))
    (hsmall : ∀ P : MMP.Mori.PrimeDivisor V,
      ¬ MMP.Mori.RationalMap.IsExceptional (X := V) p.toRationalMap P) :
    ∃ A : QDivisor V, (∀ P, 0 ≤ A.coeff P) ∧
      A.IsRelativelyBig (p ≫ S.idealSheaf.subschemeι ≫ π) ∧
      QDivisor.toRDivisor A ≤ MMP.Mori.inverseTransformDivisor p Δ := by
  classical
  have hι : Set.range S.idealSheaf.subschemeι.base = (S.support : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
  have hX : IsNormalVariety ℂ sX := hQ.1
  haveI : IsProper sX := isProper_of_isProjectiveMorphism sX hproj.isProjective
  -- `ψ` extracts only finitely many primes (FA 2.7)
  have hψb : MMP.Mori.RationalMap.IsBirational ψ := by
    obtain ⟨e, he, -⟩ := hψ
    exact ⟨e, he⟩
  have hfin := (MMP.Flips.RationalMap.finite_setOf_isInverseExceptional hX₀ hX ψ hψb
    (MMP.Flips.RationalMap.isMorphismInCodimOne_of_isOver hX₀ sX₀ sX ψ hψk)).1
  -- the restricted ample core is effective and big on the stratum
  obtain ⟨hB, Bt, hBpb, hBt0, hBtbig⟩ :=
    MMP.Fourfold.isRelativelyBig_pullback_transformDivisor_of_isAmple sX₀ sX hX₀ hX₀p hQ hproj S₀
      A₀ hA₀ hAamp hAS ψ ψinv hψ hψk hψinvk S hψS hfin hord
  -- and lies below the different
  have hBS : Finsupp.single S (1 : ℝ) + (B - Finsupp.single S 1) = B := add_sub_cancel _ _
  have hcoeff : ∀ Q, (B - Finsupp.single S (1 : ℝ)).coeff Q =
      B.coeff Q - (Finsupp.single S (1 : ℝ) : RDivisor X) Q := fun Q => rfl
  obtain ⟨-, hTn, -, hall⟩ := MMP.Fourfold.exists_isNormal_isRCartierPullback_isPoincareResidue sX
    hQ (n := 3) (by rw [hdim]; rfl) S (B - Finsupp.single S 1)
    (fun Q => by
      have h := hplt.1 Q
      rw [hcoeff]
      by_cases hQS : Q = S
      · subst hQS
        rw [Finsupp.single_eq_same, hSB]
        norm_num
      · rw [Finsupp.single_eq_of_ne hQS, sub_zero]
        exact h)
    (by rw [hcoeff, Finsupp.single_eq_same, hSB, sub_self])
    (by
      obtain ⟨m, hm⟩ := hK
      exact ⟨m, K, hm, by rw [add_assoc, hBS]; exact hplt.2.1⟩)
    (by rw [hBS]; exact fun m E a hE ha => hplt.2.2 m E a hE ha)
    S.idealSheaf.subschemeι hι
  obtain ⟨-, ⟨hTv, -, -⟩, -, hcont, -⟩ := hall Δ (fun τ hτ hτS ρ hρ => by
    rw [add_assoc, hBS]; exact hres τ hτ hτS ρ hρ)
  have hA0' : 0 ≤ MMP.Mori.RationalMap.transformDivisor ψ A₀ := transformDivisor_nonneg ψ hA₀
  have hAS0 : (MMP.Mori.RationalMap.transformDivisor ψ A₀).coeff S = 0 := by
    have h1 : ((MMP.Mori.RationalMap.transformDivisor ψ A₀).coeff S : ℝ) ≤ 0 := by
      have := hAB S
      change ((MMP.Mori.RationalMap.transformDivisor ψ A₀ S : ℚ) : ℝ) ≤
        B S - (Finsupp.single S (1 : ℝ) : RDivisor X) S at this
      rw [Finsupp.single_eq_same] at this
      have hB1 : B S = 1 := hSB
      change ((MMP.Mori.RationalMap.transformDivisor ψ A₀ S : ℚ) : ℝ) ≤ 0
      linarith
    have h2 : 0 ≤ (MMP.Mori.RationalMap.transformDivisor ψ A₀).coeff S := hA0' S
    have h1' : (MMP.Mori.RationalMap.transformDivisor ψ A₀).coeff S ≤ 0 := by exact_mod_cast h1
    exact le_antisymm h1' h2
  have hBtΔ : ∀ Q, (Bt.coeff Q : ℝ) ≤ Δ.coeff Q :=
    hcont _ (DivisorWithCoeffs.isEffective_iff_nonneg.mpr hA0')
      (MMP.Fourfold.isQCartier_of_isQFactorial sX hQ _) (fun Q => hAB Q) hAS0 hB Bt hBpb
  -- the core is big over `Zb`
  have hTproj : MMP.Mori.IsProjectiveVariety ℂ (S.idealSheaf.subschemeι ≫ sX) := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hproj
    exact isProjectiveVariety_comp_of_isFinite sX S.idealSheaf.subschemeι hTv.1
  have hBtbig' := isRelativelyBig_of_isRelativelyBig_structure (S.idealSheaf.subschemeι ≫ sX)
    hTproj sZb hZb (S.idealSheaf.subschemeι ≫ π) (by rw [Category.assoc, hπ]) hBtbig
  -- the inverse `φ = p⁻¹` of the small model
  haveI : IsProper p := isProper_of_isProjectiveMorphism p hpproj
  haveI : IsSeparated (S.idealSheaf.subschemeι ≫ sX) := hTv.1.toIsSeparated
  haveI : IsSeparated (p ≫ S.idealSheaf.subschemeι ≫ sX) := hVq.1.1.toIsSeparated
  haveI := isSeparated_toTerminal (S.idealSheaf.subschemeι ≫ sX)
  haveI := isSeparated_toTerminal (p ≫ S.idealSheaf.subschemeι ≫ sX)
  haveI : IsSeparated p := inferInstance
  set φ := MMP.Mori.RationalMap.IsBirational.inverse hpb with hφdef
  have hφb : MMP.Mori.RationalMap.IsBirational φ :=
    MMP.Mori.RationalMap.IsBirational.isBirational_inverse hpb
  have hinv : MMP.Mori.RationalMap.IsInverse p.toRationalMap φ :=
    MMP.Mori.RationalMap.IsBirational.isInverse_inverse hpb
  have hφp : φ.compHom p = Scheme.Hom.toRationalMap (𝟙 S.idealSheaf.subscheme) :=
    MMP.Fourfold.Crepant.compHom_eq_of_isInverse hinv
  have hover : MMP.Flips.RationalMap.IsOver (S.idealSheaf.subschemeι ≫ π)
      (p ≫ S.idealSheaf.subschemeι ≫ π) φ := by
    change φ.compHom (p ≫ S.idealSheaf.subschemeι ≫ π) =
      (S.idealSheaf.subschemeι ≫ π).toRationalMap
    rw [← compHom_compHom', hφp, toRationalMap_compHom', Category.id_comp]
  have hiff := fun (Q : MMP.Mori.PrimeDivisor S.idealSheaf.subscheme)
      (E : MMP.Mori.PrimeDivisor V) (hE : p E.genericPoint = Q.genericPoint) =>
    MMP.Fourfold.transformPrimeDivisor_eq_some_iff_of_isInverse p hpb hinv (𝟙 V) (ψ := φ)
      (compHom_id' φ) Q E hE E
  -- `φ` creates no divisor
  have hcontr : ∀ F : MMP.Mori.PrimeDivisor V,
      ¬ MMP.Flips.RationalMap.IsInverseExceptional φ F := by
    intro F hF
    obtain ⟨Q, hQF⟩ := exists_primeDivisor_map_genericPoint_eq_of_not_isExceptional p hpb F
      (hsmall F)
    exact hF Q ((hiff Q F hQF).mpr rfl)
  -- `φ_*` is the strict transform `p⁻¹_*`
  have hfun : MMP.Mori.RationalMap.transformPrimeDivisor φ =
      MMP.Mori.inverseTransformPrimeDivisor p := by
    funext Q
    obtain ⟨E, hE, -, -⟩ := MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{0, 0} hTv
      hVq.1 hpb Q
    rw [(hiff Q E hE).mpr rfl, ((MMP.ProgramBaseChange.inverseTransformPrimeDivisor_eq_some_iff' p
      Q E).mpr ⟨MMP.Fourfold.Oai4C1.genericPoint_mem_biregularLocus p hpb Q, hE⟩)]
  have heq : ∀ D : RDivisor S.idealSheaf.subscheme,
      MMP.Mori.RationalMap.transformDivisor φ D = MMP.Mori.inverseTransformDivisor p D := by
    intro D
    change MMP.Mori.DivisorWithCoeffs.mapPrimeDivisors
        (MMP.Mori.RationalMap.transformPrimeDivisor φ) D =
      MMP.Mori.DivisorWithCoeffs.mapPrimeDivisors (MMP.Mori.inverseTransformPrimeDivisor p) D
    rw [hfun]
  -- the strict transform of the core
  have hbig := MMP.Fourfold.isRelativelyBig_transformDivisor_of_isBirational
    (S.idealSheaf.subschemeι ≫ sX) (p ≫ S.idealSheaf.subschemeι ≫ sX) sZb hTv hTproj hVq hVproj hZb
    (S.idealSheaf.subschemeι ≫ π) (p ≫ S.idealSheaf.subschemeι ≫ π)
    (by rw [Category.assoc, Category.assoc, hπ]) φ hφb hover hcontr Bt hBtbig'
  refine ⟨MMP.Mori.RationalMap.transformDivisor φ Bt, fun P => transformDivisor_nonneg φ hBt0 P,
    hbig, ?_⟩
  rw [← heq, ← transformDivisor_toRDivisor, ← sub_nonneg, ← map_sub]
  exact transformDivisor_nonneg _ (sub_nonneg.mpr fun Q => hBtΔ Q)

/-- **A good model of the first stratum.** The stratum `T` of the retained component `S` of a
real plt `ℚ`-factorial projective fourfold with scaling has a small `ℚ`-factorial crepant model
`V ⟶ T` (real normal-source extraction with no specified divisor), on which the pull-back of the
restricted scaling divisor is effective and the boundary contains a rational divisor big over
`Zb`. -/
private theorem exists_initial_state {X Zb : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX]
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hQ : IsQFactorial sX)
    (hdim : topologicalKrullDim X = 4) (K : Divisor X) (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m)
    (B C : RDivisor X) (hplt : (∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + B) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX n B E a → 0 < a)
    (hC : 0 ≤ C) (π : X ⟶ Zb) (sZb : Zb ⟶ Spec (.of ℂ))
    (hZb : MMP.Mori.IsProjectiveVariety ℂ sZb) (hπ : π ≫ sZb = sX)
    (S : MMP.Mori.PrimeDivisor X) (hSB : B.coeff S = 1) (hSC : C.coeff S = 0)
    [IsIntegral S.idealSheaf.subscheme] [IsLocallyNoetherian S.idealSheaf.subscheme]
    [CompactSpace S.idealSheaf.subscheme] [IsNormal S.idealSheaf.subscheme]
    (Δ : RDivisor S.idealSheaf.subscheme)
    (hres : ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (S.idealSheaf.subschemeι ≫ sX) 3 1,
        IsPoincareResidue sX S.idealSheaf.subschemeι 3 1 τ ρ →
          MMP.Flips.IsRCartierPullback S.idealSheaf.subschemeι
            (Divisor.toRDivisor (divisorOfForm τ) + B) (Divisor.toRDivisor (divisorOfForm ρ) + Δ))
    (X₀ : Scheme.{0}) [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    (sX₀ : X₀ ⟶ Spec (.of ℂ)) (hX₀ : IsNormalVariety ℂ sX₀)
    (hX₀p : MMP.Mori.IsProjectiveVariety ℂ sX₀)
    (S₀ : MMP.Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (A₀ : QDivisor X₀) (hA₀ : 0 ≤ A₀) (hAamp : A₀.IsAmple) (hAS : A₀.coeff S₀ = 0)
    (ψ : X₀.RationalMap X) (ψinv : X.RationalMap X₀)
    (hψ : MMP.Mori.RationalMap.IsInverse ψ ψinv)
    (hψk : MMP.Flips.RationalMap.IsOver sX₀ sX ψ)
    (hψinvk : MMP.Flips.RationalMap.IsOver sX sX₀ ψinv)
    (hψS : MMP.Mori.RationalMap.transformPrimeDivisor ψ S₀ = some S)
    (hord : ∀ F : MMP.Mori.PrimeDivisor X,
      MMP.Flips.RationalMap.IsInverseExceptional ψ F →
      ∀ q : X.PartialMap X₀, q.toRationalMap = ψinv → ∀ hF : F.genericPoint ∈ q.domain,
        q.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀))
    (hAB : QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor ψ A₀) ≤
      B - Finsupp.single S 1) :
    ∃ s : BState S.idealSheaf.subscheme, s.Good sX S.idealSheaf.subschemeι π C Δ := by
  classical
  have hι : Set.range S.idealSheaf.subschemeι.base = (S.support : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
  obtain ⟨CS, hCS, hCS0⟩ := exists_isRCartierPullback_nonneg hQ S.idealSheaf.subschemeι S hι C hC
    hSC
  -- the stratum pair `(T, Δ)` is an effective klt pair on a normal projective threefold
  have hplt0 : (∀ P, 0 ≤ (B + (0 : ℝ) • C).coeff P ∧ (B + (0 : ℝ) • C).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + (B + (0 : ℝ) • C)) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX n (B + (0 : ℝ) • C) E a → 0 < a := by
    simpa only [zero_smul, add_zero] using hplt
  obtain ⟨hTv, hΔeff, hΔklt⟩ := isRealKltPair_add_smul_of_isPoincareResidue sX hQ hdim K hK B C 0
    hplt0 S hSB hSC S.idealSheaf.subschemeι hι Δ hres CS hCS
  simp only [zero_smul, add_zero] at hΔeff hΔklt
  have hdimT := topologicalKrullDim_eq_three sX hdim S S.idealSheaf.subschemeι hι
  have hTproj : MMP.Mori.IsProjectiveVariety ℂ (S.idealSheaf.subschemeι ≫ sX) := by
    haveI : AlgebraicGeometry.IsProjectiveVariety ℂ sX := hproj
    exact isProjectiveVariety_comp_of_isFinite sX S.idealSheaf.subschemeι hTv.1
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isNormalVariety
    (S.idealSheaf.subschemeι ≫ sX) hTv hdimT
  -- a small `ℚ`-factorial crepant model
  obtain ⟨V, iV1, iV2, iV3, p, hVq, hpb, F, hVproj, hpproj, -, -, hexc, hΔV0, hΔVklt, KV, hKV,
    hKVtr, hcrep⟩ := MMP.Fourfold.exists_isQFactorial_extraction_of_isRealKltPair
      (S.idealSheaf.subschemeι ≫ sX) 3 MMP.Fourfold.projectiveFloorProgramInputs_three hTproj
      hdimT KT hKT Δ (fun P => hΔeff P) hΔklt (E := (Fin.elim0 : Fin 0 → DivisorOver ℂ _))
      (fun a => a.elim0) (fun j => j.elim0) Fin.elim0 (fun j => j.elim0) (fun j => j.elim0)
  haveI := iV1
  haveI := iV2
  haveI := iV3
  haveI : CompactSpace V := by
    have := hVq.1.1
    exact QuasiCompact.compactSpace_of_compactSpace (p ≫ S.idealSheaf.subschemeι ≫ sX)
  haveI : IsDominant p := hpb.isDominant
  -- the pull-back of the restricted scaling divisor
  have hCSrc : RDivisor.IsRCartier CS := by
    obtain ⟨m, r, L, L', hL, -, hpbL, hG'⟩ := hCS
    refine ⟨m, r, L', fun j => (hpbL j).2.isCartier (hL j), fun Γ => ?_⟩
    rw [hG', MMP.Flips.coeff_sum_smul_toRDivisor]
  obtain ⟨⟨CV, hCV⟩, hCVnn⟩ := MMP.Fourfold.isEffective_of_isRCartierPullback p hCSrc hCS0
  -- the big core
  obtain ⟨A, hA0, hAbig, hAB'⟩ : ∃ A : QDivisor V, (∀ P, 0 ≤ A.coeff P) ∧
      A.IsRelativelyBig (p ≫ S.idealSheaf.subschemeι ≫ π) ∧
      QDivisor.toRDivisor A ≤ MMP.Mori.inverseTransformDivisor p Δ +
        ∑ j : Fin 0, Finsupp.single (F j) (1 - Fin.elim0 j) := by
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact exists_bigCore sX hproj hQ hdim K hK B hplt π sZb hZb hπ S hSB Δ hres X₀ sX₀ hX₀ hX₀p S₀
      A₀ hA₀ hAamp hAS ψ ψinv hψ hψk hψinvk hψS hord hAB p hpproj hpb hVq hVproj
      (fun P h => by obtain ⟨j, -⟩ := (hexc P).1 h; exact j.elim0)
  refine ⟨⟨V, p, KV, MMP.Mori.inverseTransformDivisor p Δ +
    ∑ j : Fin 0, Finsupp.single (F j) (1 - Fin.elim0 j), CS, CV⟩, ?_⟩
  unfold BState.Good
  exact ⟨hpproj, hpb, hVproj, hVq, hKV, fun P => hΔV0 P, hΔVklt, ⟨KT, ⟨3, hKT⟩, hKVtr, hcrep⟩,
    hCS, hCV, hCVnn _ hCV, A, hA0, hAbig, hAB'⟩

/-- **The block of one flip.** Let `X ⟶ Z ⟵ X⁺` be a step of the real plt program with scaling,
with stratum `T ⟶ X` of the retained component `S` and stratum `T⁺ ⟶ X⁺` of `S⁺`, after the
stratum maps have stabilized. A good model of `T` starts a finite threefold program with scaling
over `Zb`, all of whose steps have threshold `λ`, ending at a good model of `T⁺`. If the block
is empty, no proper curve of `S` is contracted by `f` and none of `S⁺` by `f⁺`. -/
private theorem exists_block {X Xp Zi Zb : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Xp] [CompactSpace Xp]
    [IsLocallyNoetherian Xp] [IsNormal Xp] [IsLocallyNoetherian Zi] [IsNormal Zi]
    (sX : X ⟶ Spec (.of ℂ)) (sXp : Xp ⟶ Spec (.of ℂ)) (sZi : Zi ⟶ Spec (.of ℂ))
    (sZb : Zb ⟶ Spec (.of ℂ)) [LocallyOfFiniteType sX] [LocallyOfFiniteType sXp]
    (hZb : MMP.Mori.IsProjectiveVariety ℂ sZb) (f : X ⟶ Zi) (fp : Xp ⟶ Zi) (g : Zi ⟶ Zb) (πX : X ⟶ Zb) (πXp : Xp ⟶ Zb)
    (hπ : πX ≫ sZb = sX) (hfg : f ≫ g = πX) (hfpg : fp ≫ g = πXp)
    (K : Divisor X) (B : RDivisor X) (Kp : Divisor Xp) (Bp : RDivisor Xp)
    (hK : ∃ m : ℕ, K.IsCanonicalDivisor sX m) (hKp : ∃ m : ℕ, Kp.IsCanonicalDivisor sXp m)
    (hproj : MMP.Mori.IsProjectiveVariety ℂ sX) (hprojp : MMP.Mori.IsProjectiveVariety ℂ sXp)
    (hQ : IsQFactorial sX) (hQp : IsQFactorial sXp)
    (hdim : topologicalKrullDim X = 4) (hdimp : topologicalKrullDim Xp = 4)
    (hflip : IsRealFlipStep sX sZi sXp K B Kp Bp f fp)
    (hplt : (∀ P, 0 ≤ B.coeff P ∧ B.coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + B) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX n B E a → 0 < a)
    (C : RDivisor X) (Cp : RDivisor Xp) (hC : 0 ≤ C) (hCp : Cp = flipTransform f fp C)
    (lam lamp : ℝ) (hlam : 0 < lam) (hlamp : 0 < lamp) (hlamle : lamp ≤ lam)
    (hnef : MMP.Flips.IsRelativelyNef ℂ sX πX
      (MMP.Flips.logCanonicalDivisor K (B + lam • C)))
    (hnefp : MMP.Flips.IsRelativelyNef ℂ sXp πXp
      (MMP.Flips.logCanonicalDivisor Kp (Bp + lamp • Cp)))
    (hplt_upper : (∀ P, 0 ≤ (B + lam • C).coeff P ∧ (B + lam • C).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor K + (B + lam • C)) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ sX) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sX n (B + lam • C) E a → 0 < a)
    (hplt_upperp : (∀ P, 0 ≤ (Bp + lamp • Cp).coeff P ∧ (Bp + lamp • Cp).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor Kp + (Bp + lamp • Cp)) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ sXp) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy sXp n (Bp + lamp • Cp) E a → 0 < a)
    (hcrep : ∃ D : RDivisor Zi,
      MMP.Flips.IsRCartierPullback f D (MMP.Flips.logCanonicalDivisor K (B + lam • C)) ∧
      MMP.Flips.IsRCartierPullback fp D (MMP.Flips.logCanonicalDivisor Kp (Bp + lam • Cp)))
    (S : MMP.Mori.PrimeDivisor X) (Sp : MMP.Mori.PrimeDivisor Xp)
    (hSB : B.coeff S = 1) (hSC : C.coeff S = 0) (hSBp : Bp.coeff Sp = 1) (hSCp : Cp.coeff Sp = 0)
    (hS : flipTransformPrimeDivisor f fp S = some Sp)
    {T Tp : Scheme.{0}} [IsIntegral T] [IsLocallyNoetherian T] [CompactSpace T] [IsNormal T]
    [IsIntegral Tp] [IsLocallyNoetherian Tp] [CompactSpace Tp] [IsNormal Tp]
    (ι : T ⟶ X) (ιp : Tp ⟶ Xp) [IsClosedImmersion ι] [IsClosedImmersion ιp]
    (hι : Set.range ι.base = (S.support : Set X)) (hιp : Set.range ιp.base = (Sp.support : Set Xp))
    (Δ : RDivisor T) (Δp : RDivisor Tp)
    (hres : ∀ τ : RationalPluriForms sX (3 + 1) 1, τ ≠ 0 → S.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ι ≫ sX) 3 1, IsPoincareResidue sX ι 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback ι (Divisor.toRDivisor (divisorOfForm τ) + B)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δ))
    (hresp : ∀ τ : RationalPluriForms sXp (3 + 1) 1, τ ≠ 0 → Sp.ordForm τ = -1 →
      ∀ ρ : RationalPluriForms (ιp ≫ sXp) 3 1, IsPoincareResidue sXp ιp 3 1 τ ρ →
        MMP.Flips.IsRCartierPullback ιp (Divisor.toRDivisor (divisorOfForm τ) + Bp)
          (Divisor.toRDivisor (divisorOfForm ρ) + Δp))
    (hcvx : ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor X) (Δk : Fin m → QDivisor T),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ B = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      Δ = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧ ∀ k, IsAdjunctionStep sX (Bk k) ι (Δk k))
    (hcvxp : ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor Xp) (Δk : Fin m → QDivisor Tp),
      (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ Bp = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
      Δp = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧ ∀ k, IsAdjunctionStep sXp (Bk k) ιp (Δk k))
    (hstab : ∀ φ : T.RationalMap Tp, MMP.Mori.RationalMap.IsBirational φ →
      φ.compHom (ιp ≫ fp) = (ι ≫ f).toRationalMap →
      (∀ Q : MMP.Mori.PrimeDivisor Tp, ∃ P : MMP.Mori.PrimeDivisor T,
        MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q) ∧
      ∀ (P : MMP.Mori.PrimeDivisor T) (Q : MMP.Mori.PrimeDivisor Tp),
        MMP.Mori.RationalMap.transformPrimeDivisor φ P = some Q → Δ.coeff P = Δp.coeff Q)
    (hφex : ∃ φ : T.RationalMap Tp, MMP.Mori.RationalMap.IsBirational φ ∧
      φ.compHom (ιp ≫ fp) = (ι ≫ f).toRationalMap)
    (s : BState T) (hs : s.Good sX ι πX C Δ) :
    ∃ (n : ℕ) (Mb : ℕ → PModel Zb) (sb : ∀ m, m < n → PStep (Mb m) (Mb (m + 1)))
      (s' : BState Tp), s'.Good sXp ιp πXp Cp Δp ∧ Mb 0 = s.model sX ι πX ∧
      Mb n = s'.model sXp ιp πXp ∧ (∀ m, m ≤ n → (Mb m).Good sZb) ∧
      (∀ m (h : m < n), (sb m h).Good lam) ∧
      (n = 0 → (∀ γ : ProperCurve sX, closure {γ.point} ⊆ (S.support : Set X) →
          ¬ γ.IsContractedBy f) ∧
        ∀ γ : ProperCurve sXp, closure {γ.point} ⊆ (Sp.support : Set Xp) →
          ¬ γ.IsContractedBy fp) := by
  classical
  have hsup := BState.Good.upper sX hQ hdim K hK B C lam hlam πX hnef hplt_upper S hSB hSC ι hι Δ
    hres hs
  obtain ⟨hhproj, hhb, hVproj, hVq, hKV3, hΔV0, hΔVklt, hcrepS, hCS, hCV, hCV0, A, hA0, hAbig,
    hAB⟩ := hs
  have hfT : f ≫ sZi = sX := hflip.isSmall.comp_eq
  have hfpT : fp ≫ sZi = sXp := hflip.isSmall_flip.comp_eq
  have hZi : IsNormalVariety ℂ sZi := hflip.isNegativeExtremalContraction.isNormalVariety_target
  have hgZ : g ≫ sZb = sZi := by
    haveI : IsIntegral Zi := hZi.1.toIsIntegral
    haveI : IsDominant f := hflip.isBirationalMorphism.isDominant
    exact AlgebraicGeometry.ext_of_isDominant f (by rw [reassoc_of% hfg, hπ, hfT])
  obtain ⟨φ, hφ, hφf⟩ := hφex
  obtain ⟨hφP, hφcoeff⟩ := hstab φ hφ hφf
  obtain ⟨D, hD, -⟩ := hcrep
  have hnull := isNumericallyTrivialOver_of_isRCartierPullback sX sZi hZi f hfT hD
  have hnef' : IsRelativelyNef ℂ sX (f ≫ g) (logCanonicalDivisor K (B + lam • C)) := by
    rw [hfg]; exact hnef
  have hA' : ∃ A : QDivisor s.V, (∀ P, 0 ≤ A.coeff P) ∧ A.IsRelativelyBig (s.h ≫ ι ≫ f ≫ g) ∧
      QDivisor.toRDivisor A ≤ s.ΔV := ⟨A, hA0, by rw [hfg]; exact hAbig, hAB⟩
  obtain ⟨n, Y, sY, iI, iC, iL, iN, πY, KY, ΔY, CY, W, sW, fW, gW, fpW, ψ, hmod, hstep, hp,
    hpproj, hpb, hpcomm, hpcrep, CSp, hCSp, hpC⟩ :=
    exists_scalingBlock_of_isRealFlipStep_of_isPlt sX sXp sZi sZb f fp g hfT hfpT hgZ hZb hproj
      hprojp hQ hQp hdim hdimp K Kp hK B Bp hflip hplt C hC lam hlam hnef' hnull S Sp hSB hSC hS
      ι ιp hι hιp Δ Δp hcvx hcvxp φ hφ hφf hφP hφcoeff s.h hhproj hhb hVproj hVq s.KV ⟨3, hKV3⟩
      s.ΔV hΔV0 hΔVklt hcrepS s.CS hCS s.CV hCV hCV0 hsup.1 hA'
  haveI := iI
  haveI := iC
  haveI := iL
  haveI := iN
  have hCSp' : IsRCartierPullback ιp Cp CSp := hCp ▸ hCSp
  have hTv := (isRealKltPair_add_smul_of_isPoincareResidue sX hQ hdim K hK B C lam hplt_upper S
    hSB hSC ι hι Δ hres s.CS hCS).1
  have hTpv := (isRealKltPair_add_smul_of_isPoincareResidue sXp hQp hdimp Kp hKp Bp Cp lamp
    hplt_upperp Sp hSBp hSCp ιp hιp Δp hresp CSp hCSp').1
  -- the models and steps of the block, bundled
  let Mb : ℕ → PModel Zb := fun m => ⟨modelSeq s.V Y m, modelStr (s.h ≫ ι ≫ sX) sY m,
    modelMap (s.h ≫ ι ≫ f) πY m ≫ g, divisorSeq s.KV KY m, divisorSeq s.ΔV ΔY m,
    divisorSeq s.CV CY m⟩
  let sb : ∀ m, m < n → PStep (Mb m) (Mb (m + 1)) := fun m _ =>
    ⟨W m, sW m, fW m, gW m ≫ g, fpW m, ψ m⟩
  have hMgood : ∀ m, m ≤ n → (Mb m).Good sZb := fun m hm => by
    obtain ⟨h1, h2, h3, h4, -, h6⟩ := hmod m hm
    refine ⟨?_, h2, h3, h4, h6⟩
    show (modelMap (s.h ≫ ι ≫ f) πY m ≫ g) ≫ sZb = modelStr (s.h ≫ ι ≫ sX) sY m
    rw [Category.assoc, hgZ]; exact h1
  have hsbgood : ∀ m (hm : m < n), (sb m hm).Good lam := fun m hm => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hstep m hm
    refine ⟨h1, h2, ?_, ?_, h5, h6, h7, h8, h9⟩
    · show fW m ≫ gW m ≫ g = modelMap (s.h ≫ ι ≫ f) πY m ≫ g
      rw [← Category.assoc, h3]
    · show fpW m ≫ gW m ≫ g = πY m ≫ g
      rw [← Category.assoc, h4]
  -- the scaling divisor stays effective and the big core survives
  have hprop : ∀ m, m ≤ n → 0 ≤ (Mb m).C ∧ ∃ A : QDivisor (Mb m).Y, (∀ P, 0 ≤ A.coeff P) ∧
      A.IsRelativelyBig (Mb m).π ∧ QDivisor.toRDivisor A ≤ (Mb m).B := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨hCV0, A, hA0, ?_, hAB⟩
      show A.IsRelativelyBig ((s.h ≫ ι ≫ f) ≫ g)
      rw [Category.assoc, Category.assoc, hfg]; exact hAbig
    | succ m ih =>
      intro hm
      obtain ⟨hC0, A, hA0, hAb, hAB⟩ := ih (by omega)
      exact ⟨PStep.nonneg_C (sb m (by omega)) (hsbgood m (by omega)) hC0,
        PStep.exists_big sZb hZb (sb m (by omega)) (hsbgood m (by omega)) (hMgood m (by omega))
          (hMgood (m + 1) hm) A hA0 hAb hAB⟩
  -- the endpoint
  have hstr : hp ≫ ιp ≫ sXp = modelStr (s.h ≫ ι ≫ sX) sY n := by
    rw [← hfpT, ← (hmod n le_rfl).1, ← hpcomm]
    simp only [Category.assoc]
  have hπstr : hp ≫ ιp ≫ πXp = modelMap (s.h ≫ ι ≫ f) πY n ≫ g := by
    rw [← hfpg, ← hpcomm]
    simp only [Category.assoc]
  have hK3 : Divisor.IsCanonicalDivisor (modelStr (s.h ≫ ι ≫ sX) sY n) 3
      (divisorSeq s.KV KY n) := by
    obtain ⟨m, hm⟩ := (hmod n le_rfl).2.2.2.1
    have hvar : MMP.Mori.IsVariety ℂ (modelStr (s.h ≫ ι ≫ sX) sY n) :=
      (hmod n le_rfl).2.2.1.1.1
    have hvarp : MMP.Mori.IsVariety ℂ (ιp ≫ sXp) := hTpv.1
    have hd := MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism (ιp ≫ sXp)
      (modelStr (s.h ≫ ι ≫ sX) sY n) hpb
    rw [topologicalKrullDim_eq_three sXp hdimp Sp ιp hιp] at hd
    obtain rfl : m = 3 := by
      have := hm.topologicalKrullDim_eq
      rw [← hd] at this
      exact_mod_cast this.symm
    exact hm
  obtain ⟨hCn, An, hAn0, hAnb, hAnB⟩ := hprop n le_rfl
  refine ⟨n, Mb, sb, ⟨modelSeq s.V Y n, hp, divisorSeq s.KV KY n, divisorSeq s.ΔV ΔY n, CSp,
    divisorSeq s.CV CY n⟩, ?_, ?_, ?_, hMgood, hsbgood, ?_⟩
  · unfold BState.Good
    refine ⟨hpproj, hpb, ?_, ?_, ?_, (hmod n le_rfl).2.2.2.2.1, ?_, hpcrep, hCSp', hpC, hCn,
      An, hAn0, ?_, hAnB⟩
    · rw [hstr]; exact (hmod n le_rfl).2.1
    · rw [hstr]; exact (hmod n le_rfl).2.2.1
    · rw [hstr]; exact hK3
    · rw [hstr]; exact (hmod n le_rfl).2.2.2.2.2
    · rw [hπstr]; exact hAnb
  · exact PModel.mk_eq rfl (by
      show (s.h ≫ ι ≫ f) ≫ g = s.h ≫ ι ≫ πX
      rw [Category.assoc, Category.assoc, hfg]) rfl rfl rfl
  · exact PModel.mk_eq hstr.symm hπstr.symm rfl rfl rfl
  · intro hn0
    subst hn0
    obtain ⟨KS, hKS, -, hcrS⟩ := hcrepS
    obtain ⟨KSp, hKSp, -, hcrSp⟩ := hpcrep
    exact forall_not_isContractedBy_of_crepant sX sZi sXp K B Kp Bp f fp hflip hproj hprojp hdim
      hdimp hK hQ hQp S Sp ι ιp hι hιp Δ Δp hres hresp hTv hTpv s.h hp hhproj hhb hpproj hpb hVq.1
      hpcomm s.KV s.ΔV ⟨KS, hKS, hcrS⟩ ⟨KSp, hKSp, hcrSp⟩

end Bundled

private theorem solution
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B C : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) [∀ i, IsLocallyNoetherian (Z i)] [∀ i, IsNormal (Z i)]
    (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (Z₀ : Scheme.{0}) (sZ₀ : Z₀ ⟶ Spec (.of ℂ)) (hZ₀ : MMP.Mori.IsProjectiveVariety ℂ sZ₀)
    (π : ∀ i, X i ⟶ Z₀) (g : ∀ i, Z i ⟶ Z₀)
    (hπ : ∀ i, π i ≫ sZ₀ = sX i) (hfg : ∀ i, f i ≫ g i = π i)
    (hfpg : ∀ i, fp i ≫ g i = π (i + 1))
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (hC : ∀ i, 0 ≤ C i) (hCtr : ∀ i, C (i + 1) = flipTransform (f i) (fp i) (C i))
    (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) (hlam_anti : Antitone lam)
    (hnef : ∀ i, MMP.Flips.IsRelativelyNef ℂ (sX i) (π i)
      (MMP.Flips.logCanonicalDivisor (K i) (B i + lam i • C i)))
    (hplt_upper : ∀ i, (∀ P, 0 ≤ (B i + lam i • C i).coeff P ∧ (B i + lam i • C i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + (B i + lam i • C i)) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i + lam i • C i) E a → 0 < a)
    (hcrep : ∀ i, ∃ D : RDivisor (Z i),
      MMP.Flips.IsRCartierPullback (f i) D
        (MMP.Flips.logCanonicalDivisor (K i) (B i + lam i • C i)) ∧
      MMP.Flips.IsRCartierPullback (fp i) D
        (MMP.Flips.logCanonicalDivisor (K (i + 1)) (B (i + 1) + lam i • C (i + 1))))
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hSB : ∀ i, (B i).coeff (S i) = 1) (hSC : ∀ i, (C i).coeff (S i) = 0)
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (X₀ : Scheme.{0}) [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    (sX₀ : X₀ ⟶ Spec (.of ℂ)) (hX₀ : IsNormalVariety ℂ sX₀)
    (hX₀p : MMP.Mori.IsProjectiveVariety ℂ sX₀)
    (S₀ : MMP.Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (A₀ : QDivisor X₀) (hA₀ : 0 ≤ A₀) (hAamp : A₀.IsAmple) (hAS : A₀.coeff S₀ = 0)
    (ψ : ∀ i, X₀.RationalMap (X i)) (ψinv : ∀ i, (X i).RationalMap X₀)
    (hψ : ∀ i, MMP.Mori.RationalMap.IsInverse (ψ i) (ψinv i))
    (hψk : ∀ i, MMP.Flips.RationalMap.IsOver sX₀ (sX i) (ψ i))
    (hψinvk : ∀ i, MMP.Flips.RationalMap.IsOver (sX i) sX₀ (ψinv i))
    (hψS : ∀ i, MMP.Mori.RationalMap.transformPrimeDivisor (ψ i) S₀ = some (S i))
    (hord : ∀ i, ∀ F : MMP.Mori.PrimeDivisor (X i),
      MMP.Flips.RationalMap.IsInverseExceptional (ψ i) F →
      ∀ q : (X i).PartialMap X₀, q.toRationalMap = ψinv i → ∀ hF : F.genericPoint ∈ q.domain,
        q.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀))
    (hAB : ∀ i, QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor (ψ i) A₀) ≤
      B i - Finsupp.single (S i) 1) :
    ∃ N : ℕ, ∀ i, N ≤ i →
      Disjoint (MMP.Mori.exceptionalSet (f i) : Set (X i)) ((S i).support : Set (X i)) ∧
      Disjoint (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1)))
        ((S (i + 1)).support : Set (X (i + 1))) := by
  -- the termination half: late strata contain no curve contracted by the flip
  have hcurve : ∃ N : ℕ, ∀ i, N ≤ i →
      (∀ γ : ProperCurve (sX i), closure {γ.point} ⊆ ((S i).support : Set (X i)) →
        ¬ γ.IsContractedBy (f i)) ∧
      (∀ γ : ProperCurve (sX (i + 1)), closure {γ.point} ⊆ ((S (i + 1)).support : Set (X (i + 1))) →
        ¬ γ.IsContractedBy (fp i)) := by
    haveI : ∀ i, LocallyOfFiniteType (sX i) := fun i => (hQ i).1.1.toLocallyOfFiniteType
    -- the strata `T i = S i`, with their reduced structure, and their differents
    haveI : ∀ i, IsIntegral (S i).idealSheaf.subscheme := fun i => (S i).integral
    haveI : ∀ i, IsLocallyNoetherian (S i).idealSheaf.subscheme :=
      fun i => (S i).idealSheaf.isLocallyNoetherian_subscheme
    haveI : ∀ i, CompactSpace (S i).idealSheaf.subscheme :=
      fun i => (S i).idealSheaf.subschemeι.isClosedEmbedding.compactSpace
    have hιr : ∀ i, Set.range (S i).idealSheaf.subschemeι.base = ((S i).support : Set (X i)) :=
      fun i => by rw [Scheme.IdealSheafData.range_subschemeι]
    have hBS : ∀ i, Finsupp.single (S i) (1 : ℝ) + (B i - Finsupp.single (S i) 1) = B i :=
      fun i => add_sub_cancel _ _
    have hcoeff : ∀ i Q, (B i - Finsupp.single (S i) (1 : ℝ)).coeff Q =
        (B i).coeff Q - (Finsupp.single (S i) (1 : ℝ) : RDivisor (X i)) Q := fun i Q => rfl
    have hadj := fun i => exists_isNormal_isRCartierPullback_isPoincareResidue (sX i) (hQ i)
      (n := 3) (by rw [hdim i]; rfl) (S i) (B i - Finsupp.single (S i) 1)
      (fun Q => by
        have h := (hplt i).1 Q
        rw [hcoeff]
        by_cases hQS : Q = S i
        · subst hQS
          rw [Finsupp.single_eq_same, hSB]
          norm_num
        · rw [Finsupp.single_eq_of_ne hQS, sub_zero]
          exact h)
      (by rw [hcoeff, Finsupp.single_eq_same, hSB, sub_self])
      (by
        obtain ⟨m, hm⟩ := hK i
        exact ⟨m, K i, hm, by rw [add_assoc, hBS]; exact (hplt i).2.1⟩)
      (by rw [hBS]; exact fun m E a hE ha => (hplt i).2.2 m E a hE ha)
      (S i).idealSheaf.subschemeι (hιr i)
    haveI : ∀ i, IsNormal (S i).idealSheaf.subscheme := fun i => (hadj i).2.choose
    have hTv : ∀ i, IsNormalVariety ℂ ((S i).idealSheaf.subschemeι ≫ sX i) := fun i =>
      ((hadj i).2.choose_spec.2 _ (hadj i).2.choose_spec.1.choose_spec).2.1.1
    -- the residue different as a convex combination of rational differents
    choose mw tw Bw Δw htw hsumw hBw hstepw hresw using fun i =>
      exists_convex_isAdjunctionStep (sX i) (hproj i) (hQ i) (hdim i) (B i)
        (fun P => (hplt i).1 P) (S i) (hSB i) (hTv i)
        (topologicalKrullDim_eq_three (sX i) (hdim i) (S i) _ (hιr i))
    set Δ : ∀ i, RDivisor (S i).idealSheaf.subscheme :=
      fun i => ∑ k, tw i k • QDivisor.toRDivisor (Δw i k) with hΔdef
    have hres : ∀ i, ∀ τ : RationalPluriForms (sX i) (3 + 1) 1, τ ≠ 0 → (S i).ordForm τ = -1 →
        ∀ ρ : RationalPluriForms ((S i).idealSheaf.subschemeι ≫ sX i) 3 1,
          IsPoincareResidue (sX i) (S i).idealSheaf.subschemeι 3 1 τ ρ →
            MMP.Flips.IsRCartierPullback (S i).idealSheaf.subschemeι
              (Divisor.toRDivisor (divisorOfForm τ) + B i)
              (Divisor.toRDivisor (divisorOfForm ρ) + Δ i) := fun i => hresw i
    have hcvx : ∀ i, ∃ (m : ℕ) (t : Fin m → ℝ) (Bk : Fin m → QDivisor (X i))
        (Δk : Fin m → QDivisor (S i).idealSheaf.subscheme),
        (∀ k, 0 < t k) ∧ ∑ k, t k = 1 ∧ B i = ∑ k, t k • QDivisor.toRDivisor (Bk k) ∧
        Δ i = ∑ k, t k • QDivisor.toRDivisor (Δk k) ∧
        ∀ k, IsAdjunctionStep (sX i) (Bk k) (S i).idealSheaf.subschemeι (Δk k) :=
      fun i => ⟨mw i, tw i, Bw i, Δw i, htw i, hsumw i, hBw i, rfl, hstepw i⟩
    set T : ℕ → Scheme.{0} := fun i => (S i).idealSheaf.subscheme with hT
    set ι : ∀ i, T i ⟶ X i := fun i => (S i).idealSheaf.subschemeι with hιdef
    -- after finitely many steps the stratum maps extract no prime and keep the coefficients
    obtain ⟨N₁, hN₁⟩ := eventually_realPltFlip_stratum_divisors_stabilize X sX K B Z sZ f fp hK
      hproj hQ hdim hflip hplt S hS hSB T ι Δ hιr hres
    -- a good model of the first stratum
    obtain ⟨s₀, hs₀⟩ : ∃ s : BState (T N₁), s.Good (sX N₁) (ι N₁) (π N₁) (C N₁) (Δ N₁) :=
      exists_initial_state (sX N₁) (hproj N₁) (hQ N₁) (hdim N₁) (K N₁) (hK N₁) (B N₁) (C N₁)
        (hplt N₁) (hC N₁) (π N₁) sZ₀ hZ₀ (hπ N₁) (S N₁) (hSB N₁) (hSC N₁) (Δ N₁) (hres N₁) X₀ sX₀
        hX₀ hX₀p S₀ A₀ hA₀ hAamp hAS (ψ N₁) (ψinv N₁) (hψ N₁) (hψk N₁) (hψinvk N₁) (hψS N₁)
        (hord N₁) (hAB N₁)
    -- the blocks of the stratum programs
    have hblock := fun i (hi : N₁ ≤ i) => exists_block (sX i) (sX (i + 1)) (sZ i) sZ₀ hZ₀ (f i)
      (fp i) (g i) (π i) (π (i + 1)) (hπ i) (hfg i) (hfpg i) (K i) (B i) (K (i + 1)) (B (i + 1))
      (hK i) (hK (i + 1)) (hproj i) (hproj (i + 1)) (hQ i) (hQ (i + 1)) (hdim i) (hdim (i + 1))
      (hflip i) (hplt i) (C i) (C (i + 1)) (hC i) (hCtr i) (lam i) (lam (i + 1)) (hlam i)
      (hlam (i + 1)) (hlam_anti (Nat.le_succ i)) (hnef i) (hnef (i + 1)) (hplt_upper i)
      (hplt_upper (i + 1)) (hcrep i) (S i) (S (i + 1)) (hSB i) (hSC i) (hSB (i + 1))
      (hSC (i + 1)) (hS i) (ι i) (ι (i + 1)) (hιr i) (hιr (i + 1)) (Δ i) (Δ (i + 1)) (hres i)
      (hres (i + 1)) (hcvx i) (hcvx (i + 1)) (hN₁ i hi)
      (exists_stratum_rationalMap (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
        (f i) (fp i) (hflip i) (S i) (S (i + 1)) (hS i))
    choose nb Mb sb s' hs' hMb0 hMbn hMbg hsbg hcurv using hblock
    -- the good models of the strata `N₁ + k`, one after the other
    let St : ℕ → Type 1 := fun k => {s : BState (T (N₁ + k)) //
      s.Good (sX (N₁ + k)) (ι (N₁ + k)) (π (N₁ + k)) (C (N₁ + k)) (Δ (N₁ + k))}
    let st : ∀ k, St k := fun k => Nat.rec (motive := St) ⟨s₀, hs₀⟩
      (fun k p => ⟨s' (N₁ + k) (Nat.le_add_right _ _) p.1 p.2, hs' _ _ _ _⟩) k
    let n' : ℕ → ℕ := fun k => nb (N₁ + k) (Nat.le_add_right _ _) (st k).1 (st k).2
    let Mb' : ℕ → ℕ → PModel Z₀ := fun k => Mb (N₁ + k) (Nat.le_add_right _ _) (st k).1 (st k).2
    have hj : ∀ k, Mb' (k + 1) 0 = Mb' k (n' k) := fun k =>
      (hMb0 _ _ _ _).trans (hMbn _ _ _ _).symm
    -- all late blocks are empty: otherwise they concatenate to an infinite threefold program
    have hfin : ∃ K₀, ∀ k, K₀ ≤ k → n' k = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨j, Mg, lamg, stg, hMg0, hgood, hstg⟩ := exists_pStep_of_blocks sZ₀ Mb' n' hj
        (fun k m h => sb (N₁ + k) (Nat.le_add_right _ _) (st k).1 (st k).2 m h)
        (fun k => lam (N₁ + k)) (fun k m h => hMbg _ _ _ _ m h) (fun k m h => hsbg _ _ _ _ m h)
        (fun N => let ⟨k, hk, hk'⟩ := hcon N; ⟨k, hk, Nat.pos_of_ne_zero hk'⟩)
      have e : Mg 0 = (st j).1.model (sX (N₁ + j)) (ι (N₁ + j)) (π (N₁ + j)) :=
        hMg0.trans (hMb0 _ _ _ _)
      obtain ⟨hup, hupnef⟩ := BState.Good.upper (sX (N₁ + j)) (hQ _) (hdim _) (K _) (hK _) (B _)
        (C _) (lam _) (hlam _) (π _) (hnef _) (hplt_upper _) (S _) (hSB _) (hSC _) (ι _) (hιr _)
        (Δ _) (hres _) (st j).2
      obtain ⟨-, -, -, -, hK3, hΔ0, -, -, -, -, hCV0, hA⟩ := (st j).2
      refine false_of_pStep sZ₀ hZ₀ Mg lamg stg hgood hstg (lam (N₁ + j)) (hlam _) ?_ ?_ ?_ ?_ ?_
        ?_
      all_goals rw [e]
      · exact hK3
      · exact fun P => hΔ0 P
      · exact fun P => hCV0 P
      · exact hup
      · exact hupnef
      · exact hA
    obtain ⟨K₀, hK₀⟩ := hfin
    refine ⟨N₁ + K₀, fun i hi => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, i = N₁ + k := ⟨i - N₁, by omega⟩
    exact hcurv (N₁ + k) _ (st k).1 (st k).2 (hK₀ k (by omega))
  obtain ⟨N, hN⟩ := hcurve
  exact ⟨N, fun i hi => disjoint_exceptionalSet_of_forall_properCurve_not_contracted (sX i) (sZ i)
    (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1)) (f i) (fp i) (hproj i) (hproj (i + 1)) (hQ i)
    (hQ (i + 1)) (hflip i) (C i) (lam i) (hlam i) (by simpa only [hCtr] using hcrep i) (S i)
    (S (i + 1)) (hS i) (hN i hi).1 (hN i hi).2⟩

end Proof_thm_fourfold_real_plt_special_termination_scaling

end

open CategoryTheory AlgebraicGeometry

namespace MMP.Fourfold

open MMP.Mori

/-- **Special termination for real plt fourfold flips with scaling.** Let
`X_i ⟶ Z_i ⟵ X_{i+1}` be an infinite sequence of real flips (`MMP.Fourfold.IsRealFlipStep`) of
projective `ℚ`-factorial complex fourfolds `(X_i, B_i)` over a projective variety `Z`, with
canonical divisors `K_i`, each `(X_i, B_i)` plt, with scaling of effective `ℝ`-divisors `C_i`,
`C_{i+1}` the strict transform of `C_i`, and positive nonincreasing `λ_i` such that
`K_i + B_i + λ_i C_i` is nef over `Z`, `(X_i, B_i + λ_i C_i)` is plt, and some `ℝ`-Cartier
divisor on `Z_i` pulls back to `K_i + B_i + λ_i C_i` on `X_i` and to
`K_{i+1} + B_{i+1} + λ_i C_{i+1}` on `X_{i+1}`. Let `S_i` be prime divisors of coefficient one in
`B_i` and zero in `C_i`, `S_{i+1}` the strict transform of `S_i`. Let `X⁰` be a normal projective
variety with a normal prime divisor `S⁰`, `A⁰ ≥ 0` an ample `ℚ`-divisor with `S⁰ ⊄ Supp A⁰`, and
`ψ_i : X⁰ ⤏ X_i` birational maps over `ℂ` sending `S⁰` to `S_i`, such that every
`ψ_i⁻¹`-exceptional prime divisor of `X_i` has its generic point sent outside `Supp A⁰`, and
`(ψ_i)_* A⁰ ≤ B_i - S_i`. Then for all large `i`, `Ex(f_i)` is disjoint from `S_i` and
`Ex(f_i⁺)` is disjoint from `S_{i+1}`. -/
@[mmp "thm_fourfold_real_plt_special_termination_scaling"]
public theorem eventually_disjoint_exceptionalSet_of_realPltFlip_scaling
    (X : ℕ → Scheme.{0}) [∀ i, IsIntegral (X i)] [∀ i, CompactSpace (X i)]
    [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
    (sX : ∀ i, X i ⟶ Spec (.of ℂ)) (K : ∀ i, Divisor (X i)) (B C : ∀ i, RDivisor (X i))
    (Z : ℕ → Scheme.{0}) [∀ i, IsLocallyNoetherian (Z i)] [∀ i, IsNormal (Z i)]
    (sZ : ∀ i, Z i ⟶ Spec (.of ℂ))
    (f : ∀ i, X i ⟶ Z i) (fp : ∀ i, X (i + 1) ⟶ Z i)
    (Z₀ : Scheme.{0}) (sZ₀ : Z₀ ⟶ Spec (.of ℂ)) (hZ₀ : MMP.Mori.IsProjectiveVariety ℂ sZ₀)
    (π : ∀ i, X i ⟶ Z₀) (g : ∀ i, Z i ⟶ Z₀)
    (hπ : ∀ i, π i ≫ sZ₀ = sX i) (hfg : ∀ i, f i ≫ g i = π i)
    (hfpg : ∀ i, fp i ≫ g i = π (i + 1))
    (hK : ∀ i, ∃ m : ℕ, (K i).IsCanonicalDivisor (sX i) m)
    (hproj : ∀ i, MMP.Mori.IsProjectiveVariety ℂ (sX i))
    (hQ : ∀ i, IsQFactorial (sX i))
    (hdim : ∀ i, topologicalKrullDim (X i) = 4)
    (hflip : ∀ i, IsRealFlipStep (sX i) (sZ i) (sX (i + 1)) (K i) (B i) (K (i + 1)) (B (i + 1))
      (f i) (fp i))
    (hplt : ∀ i, (∀ P, 0 ≤ (B i).coeff P ∧ (B i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + B i) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i) E a → 0 < a)
    (hC : ∀ i, 0 ≤ C i) (hCtr : ∀ i, C (i + 1) = flipTransform (f i) (fp i) (C i))
    (lam : ℕ → ℝ) (hlam : ∀ i, 0 < lam i) (hlam_anti : Antitone lam)
    (hnef : ∀ i, MMP.Flips.IsRelativelyNef ℂ (sX i) (π i)
      (MMP.Flips.logCanonicalDivisor (K i) (B i + lam i • C i)))
    (hplt_upper : ∀ i, (∀ P, 0 ≤ (B i + lam i • C i).coeff P ∧ (B i + lam i • C i).coeff P ≤ 1) ∧
      RDivisor.IsRCartier (Divisor.toRDivisor (K i) + (B i + lam i • C i)) ∧
      ∀ (n : ℕ) (E : DivisorOver ℂ (sX i)) (a : ℝ), E.IsExceptional →
        MMP.Intersection.IsLogDiscrepancy (sX i) n (B i + lam i • C i) E a → 0 < a)
    (hcrep : ∀ i, ∃ D : RDivisor (Z i),
      MMP.Flips.IsRCartierPullback (f i) D
        (MMP.Flips.logCanonicalDivisor (K i) (B i + lam i • C i)) ∧
      MMP.Flips.IsRCartierPullback (fp i) D
        (MMP.Flips.logCanonicalDivisor (K (i + 1)) (B (i + 1) + lam i • C (i + 1))))
    (S : ∀ i, MMP.Mori.PrimeDivisor (X i))
    (hSB : ∀ i, (B i).coeff (S i) = 1) (hSC : ∀ i, (C i).coeff (S i) = 0)
    (hS : ∀ i, flipTransformPrimeDivisor (f i) (fp i) (S i) = some (S (i + 1)))
    (X₀ : Scheme.{0}) [IsIntegral X₀] [IsLocallyNoetherian X₀] [IsNormal X₀] [CompactSpace X₀]
    (sX₀ : X₀ ⟶ Spec (.of ℂ)) (hX₀ : IsNormalVariety ℂ sX₀)
    (hX₀p : MMP.Mori.IsProjectiveVariety ℂ sX₀)
    (S₀ : MMP.Mori.PrimeDivisor X₀) [IsNormal S₀.idealSheaf.subscheme]
    (A₀ : QDivisor X₀) (hA₀ : 0 ≤ A₀) (hAamp : A₀.IsAmple) (hAS : A₀.coeff S₀ = 0)
    (ψ : ∀ i, X₀.RationalMap (X i)) (ψinv : ∀ i, (X i).RationalMap X₀)
    (hψ : ∀ i, MMP.Mori.RationalMap.IsInverse (ψ i) (ψinv i))
    (hψk : ∀ i, MMP.Flips.RationalMap.IsOver sX₀ (sX i) (ψ i))
    (hψinvk : ∀ i, MMP.Flips.RationalMap.IsOver (sX i) sX₀ (ψinv i))
    (hψS : ∀ i, MMP.Mori.RationalMap.transformPrimeDivisor (ψ i) S₀ = some (S i))
    (hord : ∀ i, ∀ F : MMP.Mori.PrimeDivisor (X i),
      MMP.Flips.RationalMap.IsInverseExceptional (ψ i) F →
      ∀ q : (X i).PartialMap X₀, q.toRationalMap = ψinv i → ∀ hF : F.genericPoint ∈ q.domain,
        q.hom ⟨F.genericPoint, hF⟩ ∉ (A₀.supp : Set X₀))
    (hAB : ∀ i, QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor (ψ i) A₀) ≤
      B i - Finsupp.single (S i) 1) :
    ∃ N : ℕ, ∀ i, N ≤ i →
      Disjoint (MMP.Mori.exceptionalSet (f i) : Set (X i)) ((S i).support : Set (X i)) ∧
      Disjoint (MMP.Mori.exceptionalSet (fp i) : Set (X (i + 1)))
        ((S (i + 1)).support : Set (X (i + 1))) :=
          by revert X sX K B C Z sZ f fp Z₀ sZ₀ hZ₀ π g hπ hfg hfpg hK hproj hQ hdim hflip hplt hC hCtr lam hlam hlam_anti hnef hplt_upper hcrep S hSB hSC hS X₀ sX₀ hX₀ hX₀p S₀ A₀ hA₀ hAamp hAS ψ ψinv hψ hψk hψinvk hψS hord hAB; exact Proof_thm_fourfold_real_plt_special_termination_scaling.solution

end MMP.Fourfold
