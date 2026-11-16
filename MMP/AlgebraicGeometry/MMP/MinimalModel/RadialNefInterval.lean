module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.CanonicalDifficulty
public import MMP.AlgebraicGeometry.MMP.Flip.Defs
public import MMP.AlgebraicGeometry.MMP.Models
import MMP.AlgebraicGeometry.MMP.Threefold.RadialPerturbationNullRays
import MMP.AlgebraicGeometry.MMP.Threefold.Contraction.RealKltElementaryStep
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.ComparisonLemmas
import MMP.AlgebraicGeometry.Curves.NormalizationLiftInvertible
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison

/-!
# One radial nef model works throughout a short open interval

Let `g : Y ⟶ S` be a projective morphism of projective complex varieties, with `Y` a normal
`ℚ`-factorial threefold, let `(Y, B)` and `(Y, C)` be real klt pairs with effective boundaries,
and put `D = K_Y + B`, `E = K_Y + C` and `D_t = (1 - t) D + t E = K_Y + (1 - t) B + t C`.
Suppose `D` is nef over `S` and `B` carries rational null-decomposition data with weights `rᵢ`
and Cartier index `m`, whose intersection gap is `τ > 0` (depending only on the `rᵢ` and `m`),
and put `ε = τ / (2 (τ + 6))`. If `D_{t₀}` is nef over `S` for one `0 < t₀ < ε`, then every
`D_t` with `0 < t < ε` is nef over `S`, and all these `D_t` have the same curves of degree zero
among the curves contracted by `g`.

## Main results

* `MMP.Fourfold.exists_pos_forall_isRelativelyNef_of_isRelativelyNef`.

## Implementation notes

* The gap `τ` depends on the data only through the weights and `m`; this is expressed by
  producing `τ` as a positive function of `(s, r, m)` before the threefold is given, the gap of
  data `ν` being `τ ν.s ν.weight ν.m`.
* Degrees of `ℝ`-divisors on curves are `MMP.Flips.IsRIntersectionNumber`, computed with any
  presentation by Cartier divisors; "the same zero-degree curves" is asserted for every pair of
  presentations.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], §3.7
-/

@[expose] public section

section

open AlgebraicGeometry CategoryTheory TopologicalSpace MMP.Mori MMP.Flips MMP.Fourfold

namespace Proof_lem_fourfold_radial_nef_interval

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

section Intersection

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

/-- Every value of `D · C` computed from a presentation `D = ∑ⱼ rⱼ Lⱼ` is
`∑ⱼ rⱼ deg_C 𝒪_X(Lⱼ)`. -/
private theorem IsRIntersectionNumber.eq_sum_degreeOn {D : RDivisor X} {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {C : ProperCurve sX} {x : ℝ}
    (h : IsRIntersectionNumber k sX D r L C x) (hL : ∀ j, (L j).IsCartier) :
    x = ∑ j, r j * (L j).degreeOn k sX C.ι C.dim_le (hL j) :=
  (IsRIntersectionNumber.eq_and_linear k sX C).1 D r L r L x _ h
    (isRIntersectionNumber_sum_degreeOn hL h.choose_spec.choose_spec.1 C)

/-- On a curve contracted by `f`, an `f`-nef divisor has nonnegative degree, whatever the
presentation computing it. -/
private theorem IsRelativelyNef.nonneg {Y : Scheme.{0}} {f : X ⟶ Y} {D : RDivisor X}
    (hD : IsRelativelyNef k sX f D) {C : ProperCurve sX} (hC : C.IsContractedBy f) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (h : IsRIntersectionNumber k sX D r L C x) : 0 ≤ x := by
  obtain ⟨m', r', L', hL', hD', hnef⟩ := hD
  have h' := isRIntersectionNumber_sum_degreeOn hL' hD' C
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 D r L r' L' x _ h h']
  exact hnef C hC _ h'

end Intersection

/-! ### The linear form of a presentation on relative curve classes -/

section RelativeForm

variable {X Y : Scheme.{0}} [CompactSpace X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {f : X ⟶ Y}

/-- On the class of a contracted curve, the form of a presentation is the value of `D · C`. -/
private theorem sum_degree_relativeClass {n : ℕ} (c : Fin n → ℝ) (L : Fin n → Divisor X)
    (hL : ∀ j, (L j).IsCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sX f (L j).divisorialSheaf (C.relativeClass f hC)) =
      ∑ j, c j * (L j).degreeOn ℂ sX C.ι C.dim_le (hL j) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have := (hL j).isInvertibleModule_divisorialSheaf
  exact congrArg (c j * ·) (by exact_mod_cast OneCycle.degree_cycle ℝ _ C)

end RelativeForm

/-- On a ray `ℝ_{≥0} v`, a linear form negative at one point is negative at every nonzero
point. -/
private theorem forall_neg_of_mem_ray {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ℓ : V →ₗ[ℝ] ℝ) {v w : V} {R : Set V} (hR : R = {u | ∃ c : ℝ, 0 ≤ c ∧ c • v = u})
    (hw : w ∈ R) (hℓw : ℓ w < 0) : ∀ u ∈ R, u ≠ 0 → ℓ u < 0 := by
  intro u hu hu0
  subst hR
  obtain ⟨a, ha, rfl⟩ := hw
  obtain ⟨b, hb, rfl⟩ := hu
  rw [map_smul, smul_eq_mul] at hℓw ⊢
  have ha' : 0 < a := lt_of_le_of_ne ha (by rintro rfl; simp at hℓw)
  have hb' : 0 < b := lt_of_le_of_ne hb (by rintro rfl; simp at hu0)
  have hv : ℓ v < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg ha h]
  exact mul_neg_of_pos_of_neg hb' hv

/-! ### Real divisors on `ℚ`-factorial varieties -/

section QFactorial

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)}

/-- On a `ℚ`-factorial variety every `ℝ`-divisor is `ℝ`-Cartier. -/
private theorem isRCartier_of_isQFactorial (hX : IsQFactorial sX) (Δ : RDivisor X) :
    MMP.Fourfold.RDivisor.IsRCartier Δ := by
  classical
  choose m hm hmC using fun P : MMP.Mori.PrimeDivisor X =>
    hX.2 (Finsupp.single P (1 : ℤ) : Divisor X)
  let e := Δ.support.equivFin
  let F : MMP.Mori.PrimeDivisor X → Divisor X := fun P =>
    (m P : ℤ) • (Finsupp.single P (1 : ℤ) : Divisor X)
  let w : MMP.Mori.PrimeDivisor X → ℝ := fun P => Δ P / m P
  refine ⟨Δ.support.card, fun i => w (e.symm i), fun i => F (e.symm i), fun i => hmC _,
    fun Γ => ?_⟩
  have h1 : ∀ P : MMP.Mori.PrimeDivisor X, w P * (((F P).coeff Γ : ℤ) : ℝ) =
      if P = Γ then Δ P else 0 := by
    intro P
    have hm0 : (m P : ℝ) ≠ 0 := by exact_mod_cast (hm P).ne'
    by_cases hP : P = Γ
    · subst hP
      simp [w, F, DivisorWithCoeffs.coeff_apply]
      field_simp
    · simp [w, F, DivisorWithCoeffs.coeff_apply, Finsupp.single_apply, hP]
  rw [Equiv.sum_comp e.symm (fun P : Δ.support => w P * (((F P).coeff Γ : ℤ) : ℝ)),
    Finset.sum_coe_sort Δ.support (fun P => w P * (((F P).coeff Γ : ℤ) : ℝ))]
  simp_rw [h1]
  rw [Finset.sum_ite_eq']
  split_ifs with hΓ
  · rfl
  · simpa [DivisorWithCoeffs.coeff_apply] using hΓ

/-- Adding a multiple `λ Δ` of an `ℝ`-Cartier divisor to the boundary moves a log discrepancy
affinely in `λ`. -/
private theorem IsLogDiscrepancy.exists_add_smul [CompactSpace X] {n : ℕ} {Θ Δ : RDivisor X}
    {E : DivisorOver k sX} {a : ℝ} (ha : MMP.Intersection.IsLogDiscrepancy sX n Θ E a)
    (hΔ : MMP.Fourfold.RDivisor.IsRCartier Δ) :
    ∃ σ : ℝ, ∀ l : ℝ, MMP.Intersection.IsLogDiscrepancy sX n (Θ + l • Δ) E (a - l * σ) := by
  obtain ⟨hX, hprop, ω, hω, hKω, m, r, Cs, C's, hCc, hsum, hpb, rfl⟩ := ha
  obtain ⟨p, s, M, hM, hΔ⟩ := hΔ
  haveI := E.isIntegral
  haveI := E.isLocallyNoetherian
  haveI := E.isNormal
  haveI := E.isDominant
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace E.f
  choose M' hM' using fun i => MMP.Threefold.Bridges.exists_isPullback_of_isDominant E.f (hM i)
  refine ⟨∑ i, s i * ((M' i).coeff E.E : ℝ), fun l => ⟨hX, hprop, ω, hω, hKω, m + p,
    Fin.append r (l • s), Fin.append Cs M, Fin.append C's M', ?_, ?_, ?_, ?_⟩⟩
  · intro j
    refine Fin.addCases (motive := fun j => (Fin.append Cs M j).IsCartier)
      (fun i => by simpa using hCc i) (fun i => by simpa using hM i) j
  · intro Γ
    simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul,
      DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul]
    have hl : ∑ x, l * s x * ((M x).coeff Γ : ℝ) = l * ∑ x, s x * ((M x).coeff Γ : ℝ) := by
      rw [Finset.mul_sum]; simp_rw [mul_assoc]
    rw [hl, ← hΔ Γ]
    linear_combination hsum Γ
  · intro j
    refine Fin.addCases (motive := fun j => ∃ hC, (Fin.append Cs M j).IsPullback E.f hC
      (Fin.append C's M' j)) (fun i => by simpa using hpb i) (fun i => ?_) j
    simp only [Fin.append_right]
    exact ⟨MMP.Threefold.Bridges.map_componentGenericPoint_notMem_supp E.f (M i), hM' i⟩
  · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    ring

/-- On a `ℚ`-factorial variety, a convex combination of real klt boundaries is a real klt
boundary. -/
private theorem isRealKltPair_convex [CompactSpace X] (hX : IsQFactorial sX) {B C : RDivisor X}
    (hB : IsRealKltPair sX B) (hC : IsRealKltPair sX C) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsRealKltPair sX ((1 - t) • B + t • C) := by
  obtain ⟨hnv, hB1, -, hBld⟩ := hB
  obtain ⟨-, hC1, ⟨n, K₀, hK₀, -⟩, hCld⟩ := hC
  refine ⟨hnv, fun P => ?_, ⟨n, K₀, hK₀, isRCartier_of_isQFactorial hX _⟩, fun n' E a ha => ?_⟩
  · simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    have hb := hB1 P
    have hc := hC1 P
    rcases le_total t (1 / 2) with h | h
    · nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) (sub_pos.2 hb),
        mul_nonneg ht0 (sub_pos.2 hc).le]
    · nlinarith [mul_pos (by linarith : (0 : ℝ) < t) (sub_pos.2 hc),
        mul_nonneg (sub_nonneg.2 ht1) (sub_pos.2 hb).le]
  · obtain ⟨σ, hσ⟩ := IsLogDiscrepancy.exists_add_smul ha (isRCartier_of_isQFactorial hX (B - C))
    have h1 := hBld n' E _ (by
      have := hσ t
      rwa [show (1 - t) • B + t • C + t • (B - C) = B by module] at this)
    have h2 := hCld n' E _ (by
      have := hσ (-(1 - t))
      rwa [show (1 - t) • B + t • C + (-(1 - t)) • (B - C) = C by module] at this)
    rcases le_total t (1 / 2) with h | h
    · nlinarith [mul_nonneg ht0 h2.le]
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht1) h1.le]

end QFactorial

/-- A contraction with `ρ(X/Z) = 1` contracts some curve. -/
private theorem exists_isContractedBy_of_relativePicardNumber_eq_one {k : Type} [Field k]
    {X Z : Scheme.{0}} [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {f : X ⟶ Z}
    (h : MMP.Flips.relativePicardNumber sX f = 1) : ∃ C : ProperCurve sX, C.IsContractedBy f := by
  by_contra hne
  push Not at hne
  have htop : relativeNumericallyTrivialDivisors sX f = ⊤ :=
    eq_top_iff.2 fun D _ => (mem_relativeNumericallyTrivialDivisors sX f).2 fun C hC => absurd hC (hne C)
  have : Subsingleton (RelativeNumericalDivisorClasses sX f) := by
    unfold RelativeNumericalDivisorClasses
    rw [htop]
    infer_instance
  unfold MMP.Flips.relativePicardNumber at h
  rw [rank_subsingleton'] at h
  simp at h

/-- The radial divisors `K + (1 - t) B + t C` are affine in the parameter `t`. -/
private theorem logCanonicalDivisor_affine {X : Scheme.{0}} (K : Divisor X) (B C : RDivisor X)
    {s t u α β : ℝ} (h₁ : α + β = 1) (h₂ : α * s + β * t = u) :
    α • logCanonicalDivisor K ((1 - s) • B + s • C) +
        β • logCanonicalDivisor K ((1 - t) • B + t • C) =
      logCanonicalDivisor K ((1 - u) • B + u • C) := by
  unfold logCanonicalDivisor
  rw [← h₂]
  obtain rfl : β = 1 - α := by linarith
  module

/-- Nefness of `D_u` over `S`, read on a contracted curve `A` along the radial line: if
`u = α s + β t` with `α + β = 1`, then `α (D_s · A) + β (D_t · A) ≥ 0`. -/
private theorem IsRelativelyNef.radial_nonneg {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX] {g : X ⟶ Y} {K : Divisor X}
    {B C : RDivisor X} {s t u α β x y : ℝ}
    (hnef : IsRelativelyNef ℂ sX g (logCanonicalDivisor K ((1 - u) • B + u • C)))
    {A : ProperCurve sX} (hA : A.IsContractedBy g) {m m' : ℕ} {r : Fin m → ℝ}
    {L : Fin m → Divisor X} {r' : Fin m' → ℝ} {L' : Fin m' → Divisor X}
    (hx : IsRIntersectionNumber ℂ sX (logCanonicalDivisor K ((1 - s) • B + s • C)) r L A x)
    (hy : IsRIntersectionNumber ℂ sX (logCanonicalDivisor K ((1 - t) • B + t • C)) r' L' A y)
    (h₁ : α + β = 1) (h₂ : α * s + β * t = u) : 0 ≤ α * x + β * y := by
  have := (IsRIntersectionNumber.eq_and_linear ℂ sX A).2 _ _ r L r' L' x y α β hx hy
  rw [logCanonicalDivisor_affine K B C h₁ h₂] at this
  exact IsRelativelyNef.nonneg hnef hA this

/-- **The radial step.** If `D_{t₀}` is nef over `S` for one `t₀ > 0`, and every
`D_t`-negative extremal ray of `NE̅(Y/S)` is `D`-null, then `D_t` is nef over `S`.

Otherwise the real klt contraction of a `D_t`-negative extremal ray `R` contracts a curve `A`;
then `D · A = 0` and `D_t · A < 0`, so `D_{t₀} · A = (t₀ / t) (D_t · A) < 0`. -/
private theorem isRelativelyNef_of_forall_isExtremalRay_null {Y S : Scheme.{0}} [IsIntegral Y]
    [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {sY : Y ⟶ Spec (.of ℂ)} {sS : S ⟶ Spec (.of ℂ)} {g : Y ⟶ S}
    (hS : MMP.Mori.IsProjectiveVariety ℂ sS) (hg : g ≫ sS = sY)
    {K : Divisor Y} {B C : RDivisor Y} (hK : K.IsCanonicalDivisor sY 3)
    (ν : RationalNullData sY K B) (hC0 : ∀ P, 0 ≤ C.coeff P) (hCklt : IsRealKltPair sY C)
    (hDnef : IsRelativelyNef ℂ sY g (logCanonicalDivisor K B))
    {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hDt₀ : IsRelativelyNef ℂ sY g (logCanonicalDivisor K ((1 - t₀) • B + t₀ • C)))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hray : ∀ R : Set (RelativeNumericalCurveClasses sY g),
      IsExtremalRay ℝ
        (relativeClosedConeOfCurves sY g : Set (RelativeNumericalCurveClasses sY g)) R →
      (∃ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor Y) (hL : ∀ j, (L j).IsCartier),
        Divisor.toRDivisor K + ((1 - t) • B + t • C) =
            ∑ j, c j • Divisor.toRDivisor (L j) ∧
          ∀ u ∈ R, u ≠ 0 →
            ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
              RelativeNumericalCurveClasses.degree sY g (L j).divisorialSheaf u) < 0) →
      ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor Y) (hL : ∀ j, (L j).IsCartier),
        Divisor.toRDivisor K + B = ∑ j, c j • Divisor.toRDivisor (L j) →
        ∀ u ∈ R, ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
          RelativeNumericalCurveClasses.degree sY g (L j).divisorialSheaf u) = 0) :
    IsRelativelyNef ℂ sY g (logCanonicalDivisor K ((1 - t) • B + t • C)) := by
  by_contra hnef
  have hBt0 : 0 ≤ (1 - t) • B + t • C := fun P => by
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (sub_nonneg.2 ht1.le) (ν.nonneg P)) (mul_nonneg ht.le (hC0 P))
  obtain ⟨R, Z, _, _, _, sZ, f, h, hR, hRneg, hcon, -, hneg, -, -⟩ :=
    IsRealKltPair.exists_isRelativeContractionOfFace_of_not_isRelativelyNef
      ν.isProjectiveVariety hS hg ν.isQFactorial hK.topologicalKrullDim_eq ⟨3, hK⟩ hBt0
      (isRealKltPair_convex ν.isQFactorial ν.isRealKltPair hCklt ht.le ht1.le) hnef
  obtain ⟨A, hAf⟩ :=
    exists_isContractedBy_of_relativePicardNumber_eq_one hneg.relativePicardNumber_eq_one
  have hAg : A.IsContractedBy g := by
    intro x hx
    rw [← hcon.comp_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hAf x hx]
  have hAR : A.relativeClass g hAg ∈ R := (hcon.isContractedBy_iff A hAg).1 hAf
  obtain ⟨n, c, L, hL, hDt : logCanonicalDivisor K ((1 - t) • B + t • C) =
    ∑ j, c j • Divisor.toRDivisor (L j)⟩ := hneg.isCartierCombination
  have hxA := hRneg A hAg hAR n c L _ (isRIntersectionNumber_sum_degreeOn hL hDt A)
  let ℓ : RelativeNumericalCurveClasses sY g →ₗ[ℝ] ℝ :=
    ∑ j, c j • (haveI := (hL j).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sY g (L j).divisorialSheaf)
  have hℓ : ∀ u, ℓ u = ∑ j, c j * (haveI := (hL j).isInvertibleModule_divisorialSheaf
      RelativeNumericalCurveClasses.degree sY g (L j).divisorialSheaf u) := fun u => by
    simp [ℓ, LinearMap.sum_apply]
  obtain ⟨m, r, L', hL', hD, -⟩ := hDnef
  have h0 := hray R hR ⟨n, c, L, hL, hDt, fun u hu hu0 => by
    rw [← hℓ]
    refine forall_neg_of_mem_ray ℓ hR.2.choose_spec.2 hAR ?_ u hu hu0
    rwa [hℓ, sum_degree_relativeClass]⟩ m r L' hL' hD _ hAR
  rw [sum_degree_relativeClass r L' hL'] at h0
  have hnn := IsRelativelyNef.radial_nonneg (s := 0) hDt₀ hAg
    (by simpa using isRIntersectionNumber_sum_degreeOn hL' hD A)
    (isRIntersectionNumber_sum_degreeOn hL hDt A) (sub_add_cancel 1 (t₀ / t))
    (by field_simp; ring)
  rw [h0, mul_zero, zero_add] at hnn
  linarith [mul_neg_of_pos_of_neg (div_pos ht₀ ht) hxA]

/-- **Null curves are the same along the interval.** If every `D_t`, `0 < t < ε`, is nef over
`S`, then a contracted curve `A` with `D_t · A = 0` for one such `t` has `D_{t'} · A = 0` for
every such `t'`: the degree is affine in the parameter and nonnegative on the interval, so it
would be negative just beyond `t`, on the side away from `t'`. -/
private theorem eq_zero_of_eq_zero_of_forall_isRelativelyNef {X Y : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of ℂ)} [QuasiCompact sX]
    {g : X ⟶ Y} {K : Divisor X} {B C : RDivisor X} {ε : ℝ}
    (hnef : ∀ t : ℝ, 0 < t → t < ε →
      IsRelativelyNef ℂ sX g (logCanonicalDivisor K ((1 - t) • B + t • C)))
    {t t' : ℝ} (ht : 0 < t) (htε : t < ε) (ht' : 0 < t') (ht'ε : t' < ε)
    {A : ProperCurve sX} (hA : A.IsContractedBy g) {n n' : ℕ} {c : Fin n → ℝ}
    {L : Fin n → Divisor X} {c' : Fin n' → ℝ} {L' : Fin n' → Divisor X} {x x' : ℝ}
    (hx : IsRIntersectionNumber ℂ sX (logCanonicalDivisor K ((1 - t) • B + t • C)) c L A x)
    (hx' : IsRIntersectionNumber ℂ sX (logCanonicalDivisor K ((1 - t') • B + t' • C)) c' L' A x')
    (hx0 : x = 0) : x' = 0 := by
  rcases eq_or_ne t t' with rfl | htt'
  · exact ((IsRIntersectionNumber.eq_and_linear ℂ sX A).1 _ c L c' L' x x' hx hx').symm.trans hx0
  have hx'pos : 0 ≤ x' := IsRelativelyNef.nonneg (hnef t' ht' ht'ε) hA hx'
  -- a parameter `s` beyond `t`, on the side away from `t'`
  obtain ⟨s, hs, hsε, hβ⟩ : ∃ s, 0 < s ∧ s < ε ∧ (t - s) / (t - t') < 0 := by
    rcases lt_or_gt_of_ne htt' with h | h
    · exact ⟨t / 2, by linarith, by linarith, div_neg_of_pos_of_neg (by linarith) (by linarith)⟩
    · exact ⟨(t + ε) / 2, by linarith, by linarith,
        div_neg_of_neg_of_pos (by linarith) (by linarith)⟩
  have hd : t - t' ≠ 0 := sub_ne_zero.mpr htt'
  have hnn := IsRelativelyNef.radial_nonneg (hnef s hs hsε) hA hx hx'
    (α := (s - t') / (t - t')) (β := (t - s) / (t - t')) (by field_simp; ring)
    (by field_simp; ring)
  rw [hx0, mul_zero, zero_add] at hnn
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hβ.le hx'pos]

/-- **One radial nef model works throughout a short open interval.** -/
private theorem solution :
    ∃ τ : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ, (∀ s r m, 0 < τ s r m) ∧
      ∀ {Y S : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
        (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (g : Y ⟶ S),
        IsProjectiveMorphism g → MMP.Mori.IsProjectiveVariety ℂ sS → g ≫ sS = sY →
        ∀ {K : Divisor Y} {B C : RDivisor Y}, K.IsCanonicalDivisor sY 3 →
        ∀ ν : RationalNullData sY K B, (∀ P, 0 ≤ C.coeff P) → IsRealKltPair sY C →
        MMP.Flips.IsRelativelyNef ℂ sY g (MMP.Flips.logCanonicalDivisor K B) →
        ∀ t₀ : ℝ, 0 < t₀ →
          t₀ < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
          MMP.Flips.IsRelativelyNef ℂ sY g
            (MMP.Flips.logCanonicalDivisor K ((1 - t₀) • B + t₀ • C)) →
          (∀ t : ℝ, 0 < t → t < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            MMP.Flips.IsRelativelyNef ℂ sY g
              (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C))) ∧
          (∀ t t' : ℝ, 0 < t → t < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            0 < t' → t' < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            ∀ A : ProperCurve sY, A.IsContractedBy g →
            ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor Y) (x : ℝ)
              (n' : ℕ) (c' : Fin n' → ℝ) (L' : Fin n' → Divisor Y) (x' : ℝ),
              MMP.Flips.IsRIntersectionNumber ℂ sY
                (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) c L A x →
              MMP.Flips.IsRIntersectionNumber ℂ sY
                (MMP.Flips.logCanonicalDivisor K ((1 - t') • B + t' • C)) c' L' A x' →
              (x = 0 ↔ x' = 0)) := by
  obtain ⟨τf, hτf, hnull⟩ :=
    exists_pos_forall_isExtremalRay_null_and_isNegativeExtremalContraction
  refine ⟨τf, hτf, ?_⟩
  intro Y S _ _ _ _ sY sS g hgp hS hg K B C hK ν hC0 hCklt hDnef t₀ ht₀ ht₀ε hDt₀
  set τ := τf ν.s ν.weight ν.m
  have hτ : 0 < τ := hτf _ _ _
  have hεlt : τ / (2 * (τ + 6)) < τ := by rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hε1 : τ / (2 * (τ + 6)) < 1 := by rw [div_lt_iff₀ (by positivity)]; linarith
  have part1 : ∀ t : ℝ, 0 < t → t < τ / (2 * (τ + 6)) →
      IsRelativelyNef ℂ sY g (logCanonicalDivisor K ((1 - t) • B + t • C)) := fun t ht htε =>
    isRelativelyNef_of_forall_isExtremalRay_null hS hg hK ν hC0 hCklt hDnef ht₀ hDt₀ ht
      (htε.trans hε1) (hnull sY sS g hS hg hK ν hC0 hCklt hDnef t ht (htε.trans hεlt)).1
  refine ⟨part1, fun t t' ht htε ht' ht'ε A hA n c L x n' c' L' x' hx hx' => ⟨?_, ?_⟩⟩
  · exact eq_zero_of_eq_zero_of_forall_isRelativelyNef part1 ht htε ht' ht'ε hA hx hx'
  · exact eq_zero_of_eq_zero_of_forall_isRelativelyNef part1 ht' ht'ε ht htε hA hx' hx

end Proof_lem_fourfold_radial_nef_interval

end

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace MMP.Fourfold

open MMP.Mori

/-- **One radial nef model works throughout a short open interval.** There is a positive
function `τ` of the number `s` of boundaries, the weights `r : Fin s → ℝ` and the Cartier index
`m` with the following property. Let `g : Y ⟶ S` be a projective morphism of projective complex
varieties over `Spec ℂ`, with canonical divisor `K` of the threefold `Y`, let `B` carry rational
null-decomposition data `ν` (`MMP.Fourfold.RationalNullData`), let `C` be an effective real
boundary with `(Y, C)` klt, and suppose `D = K + B` is nef over `S`. Put
`ε = τ / (2 (τ + 6))` for `τ = τ ν.s ν.weight ν.m`, and `D_t = K + (1 - t) B + t C`. If
`D_{t₀}` is nef over `S` for some `0 < t₀ < ε`, then every `D_t`, `0 < t < ε`, is nef over `S`,
and for `0 < t, t' < ε` a curve contracted by `g` has `D_t`-degree zero if and only if it has
`D_{t'}`-degree zero. -/
@[mmp "lem_fourfold_radial_nef_interval"]
public theorem exists_pos_forall_isRelativelyNef_of_isRelativelyNef :
    ∃ τ : (s : ℕ) → (Fin s → ℝ) → ℕ → ℝ, (∀ s r m, 0 < τ s r m) ∧
      ∀ {Y S : Scheme.{0}} [IsIntegral Y] [CompactSpace Y] [IsLocallyNoetherian Y] [IsNormal Y]
        (sY : Y ⟶ Spec (.of ℂ)) (sS : S ⟶ Spec (.of ℂ)) (g : Y ⟶ S),
        IsProjectiveMorphism g → MMP.Mori.IsProjectiveVariety ℂ sS → g ≫ sS = sY →
        ∀ {K : Divisor Y} {B C : RDivisor Y}, K.IsCanonicalDivisor sY 3 →
        ∀ ν : RationalNullData sY K B, (∀ P, 0 ≤ C.coeff P) → IsRealKltPair sY C →
        MMP.Flips.IsRelativelyNef ℂ sY g (MMP.Flips.logCanonicalDivisor K B) →
        ∀ t₀ : ℝ, 0 < t₀ →
          t₀ < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
          MMP.Flips.IsRelativelyNef ℂ sY g
            (MMP.Flips.logCanonicalDivisor K ((1 - t₀) • B + t₀ • C)) →
          (∀ t : ℝ, 0 < t → t < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            MMP.Flips.IsRelativelyNef ℂ sY g
              (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C))) ∧
          (∀ t t' : ℝ, 0 < t → t < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            0 < t' → t' < τ ν.s ν.weight ν.m / (2 * (τ ν.s ν.weight ν.m + 6)) →
            ∀ A : ProperCurve sY, A.IsContractedBy g →
            ∀ (n : ℕ) (c : Fin n → ℝ) (L : Fin n → Divisor Y) (x : ℝ)
              (n' : ℕ) (c' : Fin n' → ℝ) (L' : Fin n' → Divisor Y) (x' : ℝ),
              MMP.Flips.IsRIntersectionNumber ℂ sY
                (MMP.Flips.logCanonicalDivisor K ((1 - t) • B + t • C)) c L A x →
              MMP.Flips.IsRIntersectionNumber ℂ sY
                (MMP.Flips.logCanonicalDivisor K ((1 - t') • B + t' • C)) c' L' A x' →
              (x = 0 ↔ x' = 0)) :=
                by exact Proof_lem_fourfold_radial_nef_interval.solution

end MMP.Fourfold
