module

public import MMP.AlgebraicGeometry.MMP.BasepointFree.Nonvanishing
public import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy

/-!
# Non-vanishing of the Euler characteristic function along a ray

Let `Y` be a smooth projective variety over an algebraically closed field `k` of characteristic
zero, `D₁, …, D_k` Cartier divisors and `A` a `ℚ`-divisor on `Y` with simple normal crossing
support and `⌈A⌉ ≥ 0`. If `u ∈ ℤᵏ` is such that `D = ∑ᵢ uᵢ Dᵢ` is nef and `D + A - K_Y` is
ample, then the Euler characteristic function `P(v) = χ(Y, 𝒪_Y(∑ᵢ vᵢ Dᵢ + ⌈A⌉))` satisfies
`P(m u) ≠ 0` for all sufficiently large integers `m`.

By Kawamata–Viehweg vanishing `P(m u) = h⁰(Y, m D + ⌈A⌉)`, and this is nonzero for `m ≫ 0` by the
non-vanishing theorem applied to the klt pair `(Y, -A)`.

## Main results

* `MMP.Mori.Divisor.eventually_eulerPolynomial_zsmul_ne_zero`: the statement above.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.4, Step 2
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Filter MMP.Mori
open scoped Stacks.SmallDerivedModel

namespace MMP.FourfoldProofs.Km3bMultidivisorEulerPolynomialNonzeroProof

/-- If `Hⁱ(X, ℱ) = 0` for every `i > 0`, then `χ(X, ℱ) = h⁰(X, ℱ)`. -/
private theorem eulerCharacteristic_eq_finrank_zero {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] (F : X.Modules) [F.IsCoherent]
    (h : ∀ i : ℤ, 0 < i → Subsingleton (Stacks.Duality.derivedCohomologyOverField sX
      ((DerivedCategory.singleFunctor X.Modules 0).obj F) i)) :
    eulerCharacteristic k sX F = Module.finrank k (cohomologyOverField k sX F 0) := by
  rw [eulerCharacteristic_eq_finsum, finsum_eq_single _ 0 fun j hj => ?_]
  · simp
  · have := h j (by exact_mod_cast Nat.pos_of_ne_zero hj)
    have := (Stacks.Duality.cohomologyOverFieldLinearEquivDerivedCohomologyOverField k sX F
      j).toEquiv.subsingleton
    rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

/-- On a proper scheme over `k`, a nonzero global section of `𝒪_X(E)` makes `h⁰(X, 𝒪_X(E))`
positive. -/
private theorem finrank_pos_of_exists_ne_zero {k : Type} [Field k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [IsProper sX] (E : Divisor X)
    [E.divisorialSheaf.IsCoherent] (h : ∃ σ : E.divisorialSubmodule ⊤, σ ≠ 0) :
    0 < Module.finrank k (cohomologyOverField k sX E.divisorialSheaf 0) := by
  have := finiteDimensional_cohomologyOverField_of_isProper k sX E.divisorialSheaf 0
  rw [Module.finrank_pos_iff_exists_ne_zero]
  obtain ⟨σ, hσ⟩ := h
  let e := (cohomologyOverFieldZeroIsoSections k sX E.divisorialSheaf).toLinearEquiv
  exact ⟨e.symm σ, (LinearEquiv.map_ne_zero_iff e.symm).mpr hσ⟩

/-- If `⌈A⌉ ≥ 0`, then every coefficient of `-A` is `< 1`. -/
private theorem coeff_neg_lt_one_of_isEffective_roundUp {X : Scheme.{0}} {A : QDivisor X}
    (hA : (DivisorWithCoeffs.roundUp A).IsEffective) (P : MMP.Mori.PrimeDivisor X) :
    (-A).coeff P < 1 := by
  have h := (DivisorWithCoeffs.isEffective_iff_nonneg.mp hA) P
  change 0 ≤ (DivisorWithCoeffs.roundUp A).coeff P at h
  rw [DivisorWithCoeffs.coeff_roundUp] at h
  have := Int.lt_ceil.mp (show (-1 : ℤ) < ⌈A.coeff P⌉ by omega)
  rw [DivisorWithCoeffs.coeff_neg]
  push_cast at this
  linarith

/-- Round-up absorbs an integral divisor: `K + ⌈(L - K) + A⌉ = L + ⌈A⌉`. -/
private theorem add_roundUp_toQDivisor_sub_add {X : Scheme.{0}} (K L : Divisor X)
    (A : QDivisor X) :
    K + DivisorWithCoeffs.roundUp (Divisor.toQDivisor (L - K) + A) =
      L + DivisorWithCoeffs.roundUp A := by
  ext P
  change K.coeff P + (DivisorWithCoeffs.roundUp _).coeff P =
    L.coeff P + (DivisorWithCoeffs.roundUp A).coeff P
  simp only [DivisorWithCoeffs.coeff_roundUp, DivisorWithCoeffs.coeff_add,
    Divisor.coeff_toQDivisor, Int.ceil_intCast_add, DivisorWithCoeffs.coeff_sub]
  ring

/-- Along a nef ray: if `E` is nef and Cartier and `E + A - K` is ample, then so is
`mE + A - K = (E + A - K) + (m - 1)E` for every `m ≥ 1`. -/
private theorem isAmple_toQDivisor_zsmul_sub_add {k : Type} [Field k] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of k)) [MMP.Mori.IsProjectiveVariety k f] [IsNormal Y]
    [IsLocallyNoetherian Y] [CompactSpace Y] (hsm : IsSmoothScheme f)
    {E K : Divisor Y} {A : QDivisor Y}
    (hEC : E.IsCartier) (hnef : E.IsNef k f)
    (hamp : (Divisor.toQDivisor E + A - Divisor.toQDivisor K).IsAmple) {m : ℤ} (hm : 1 ≤ m) :
    (Divisor.toQDivisor (m • E - K) + A).IsAmple := by
  refine QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef f
    (Finset.range (m - 1).toNat) (fun _ => Divisor.toQDivisor E) hamp
    (fun _ _ => (QDivisor.isNef_toQDivisor_iff E hEC).mpr hnef) ?_
  rw [show Divisor.toQDivisor (m • E - K) + A = Divisor.toQDivisor E + A - Divisor.toQDivisor K +
      ∑ _i ∈ Finset.range (m - 1).toNat, Divisor.toQDivisor E by
    rw [Finset.sum_const, Finset.card_range, ← natCast_zsmul, Int.toNat_of_nonneg (by omega),
      map_sub, map_zsmul, sub_smul, one_smul]
    abel]
  exact QDivisor.NumericallyEquivalent.refl (MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _)

/-- Kawamata–Viehweg along a nef ray: if `E` is nef and Cartier and `E + A - K_Y` is ample, then
`Hⁱ(Y, 𝒪_Y(mE + ⌈A⌉)) = 0` for all `i > 0` and `m ≥ 1`. -/
private theorem subsingleton_derivedCohomologyOverField_zsmul_add_roundUp {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}} (f : Y ⟶ Spec (.of k))
    [MMP.Mori.IsProjectiveVariety k f] (hsm : IsSmoothScheme f) [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor f n)
    {E : Divisor Y} (hEC : E.IsCartier) (hnef : E.IsNef k f) {A : QDivisor Y} (hA : A.IsSNC f)
    (hamp : (Divisor.toQDivisor E + A - Divisor.toQDivisor K).IsAmple) {m : ℤ} (hm : 1 ≤ m)
    (i : ℤ) (hi : 0 < i) :
    Subsingleton (Stacks.Duality.derivedCohomologyOverField f
      ((DerivedCategory.singleFunctor Y.Modules 0).obj
        (m • E + DivisorWithCoeffs.roundUp A).divisorialSheaf) i) := by
  obtain ⟨hnefm, hbigm⟩ := QDivisor.isNef_and_isBig_of_isAmple f
    (isAmple_toQDivisor_zsmul_sub_add f hsm hEC hnef hamp hm)
  rw [← add_roundUp_toQDivisor_sub_add K]
  exact subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp f hsm
    hK (m • E - K) A hA hnefm hbigm i hi

end MMP.FourfoldProofs.Km3bMultidivisorEulerPolynomialNonzeroProof

open MMP.FourfoldProofs.Km3bMultidivisorEulerPolynomialNonzeroProof

namespace MMP.Mori

namespace Divisor

/-- **The Euler characteristic function does not vanish along a nef ray** (Kollár–Mori 3.4,
Step 2). Let `Y` be a smooth projective variety over an algebraically closed field `k` of
characteristic zero, `K` a canonical divisor of `Y`, `D i` divisors and `A` a
`ℚ`-divisor with simple normal crossing support and `⌈A⌉` effective. If `∑ i, u i • D i` is nef
and `∑ i, u i • D i + A - K` is ample, then `eulerPolynomial k f D A (m • u) ≠ 0` for all
sufficiently large integers `m`. -/
@[mmp "lem_km3b_multidivisor_euler_polynomial_nonzero"]
public theorem eventually_eulerPolynomial_zsmul_ne_zero
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {Y : Scheme.{0}}
    (f : Y ⟶ Spec (.of k)) [IsProjectiveVariety k f] (hsm : IsSmoothScheme f)
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    {n : ℕ} {K : Divisor Y} (hK : K.IsCanonicalDivisor f n)
    {ι : Type*} [Fintype ι] (D : ι → Divisor Y)
    (A : QDivisor Y) (hA : A.IsSNC f) (hAe : (DivisorWithCoeffs.roundUp A).IsEffective)
    (u : ι → ℤ) (hnef : (∑ i, u i • D i).IsNef k f)
    (hamp : (Divisor.toQDivisor (∑ i, u i • D i) + A - Divisor.toQDivisor K).IsAmple) :
    ∀ᶠ m : ℤ in atTop, eulerPolynomial k f D A (m • u) ≠ 0 := by
  set E := ∑ i, u i • D i
  have hV : MMP.Mori.IsVariety k f := inferInstance
  have (F : Divisor Y) : F.divisorialSheaf.IsCoherent :=
    (MMP.Threefold.isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul f hV F 0).1
  have hklt : IsKltPair f n K (-A) := MMP.Mori.isKltPair_of_isSNC f ⟨hV, inferInstance⟩ hsm hK
    (hA.of_support_subset (Finsupp.support_neg _).le)
    (coeff_neg_lt_one_of_isEffective_roundUp hAe)
  obtain ⟨hnef1, hbig1⟩ := QDivisor.isNef_and_isBig_of_isAmple f (by rwa [one_smul] :
    ((1 : ℚ) • Divisor.toQDivisor E + A - Divisor.toQDivisor K).IsAmple)
  obtain ⟨m₀, hm₀⟩ := IsNonvanishingDatum.hasNonvanishingProperty (sX := f)
    { isProperVariety := inferInstance
      isCartier := hnef.1
      isNef := hnef
      isKltPair := hklt
      pos := one_pos
      isQCartier_add := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm _
      isNef_add := hnef1
      isBig_add := hbig1 }
  refine eventually_atTop.mpr ⟨max m₀ 1, fun m hm => ?_⟩
  have hsum : ∑ i, (m • u) i • D i = m • E := by
    simp only [E, Finset.smul_sum, Pi.smul_apply, smul_eq_mul, mul_smul]
  rw [Divisor.eulerPolynomial_eq_eulerCharacteristic, hsum,
    eulerCharacteristic_eq_finrank_zero f _ fun i hi =>
      subsingleton_derivedCohomologyOverField_zsmul_add_roundUp f hsm hK hnef.1 hnef hA hamp
        (le_of_max_le_right hm) i hi]
  exact_mod_cast (finrank_pos_of_exists_ne_zero f _ (hm₀ m (le_of_max_le_left hm))).ne'

end Divisor

end MMP.Mori
