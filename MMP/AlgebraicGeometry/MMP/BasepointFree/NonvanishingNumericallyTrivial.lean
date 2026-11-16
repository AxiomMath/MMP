module

public import MMP.AlgebraicGeometry.Vanishing.KawamataViehwegRoundUp
public import MMP.AlgebraicGeometry.Intersection.EulerCharacteristicNumerical
public import MMP.AlgebraicGeometry.Positivity.AmplePlusNefSum
public import MMP.AlgebraicGeometry.Positivity.AmpleNefBig
public import MMP.AlgebraicGeometry.MMP.BasepointFree.RelativelyFreeTwist
public import MMP.AlgebraicGeometry.Divisor.DivisorialSheafCoherent

@[expose] public section

section

/-!
# Non-vanishing for a numerically trivial divisor

For a smooth non-vanishing datum `(X, D, G, a)` with `D ≡ 0`, Kawamata–Viehweg vanishing for the
round-up gives `Hⁱ(X, mD + ⌈G⌉) = 0` for `i > 0`, so `h⁰(X, mD + ⌈G⌉) = χ(X, mD + ⌈G⌉)`; the
Euler characteristic depends only on the numerical class, so it equals `χ(X, ⌈G⌉) = h⁰(X, ⌈G⌉)`,
which is positive because `⌈G⌉` is effective.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 3.5 Step 1
-/

open CategoryTheory AlgebraicGeometry MMP.Mori
open scoped Stacks.SmallDerivedModel

namespace MMP.FourfoldProofs.Km3aNonvanishingNumericallyTrivialProof

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

/-- On a scheme smooth over a field, a `ℚ`-divisor whose support is an snc divisor is snc. -/
private theorem isSNC_of_isSNCSubset_supp {k : Type} [Field k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [Smooth sX]
    {G : QDivisor X} (h : IsSNCSubset sX G.supp) : G.IsSNC sX := by
  have hgen : ∀ E : MMP.Mori.PrimeDivisor X, E ∈ G.support → E.genericPoint ∈ (G.supp : Set X) :=
    fun E hE => DivisorWithCoeffs.support_subset_supp (D := G) (E := E)
      (by simpa [DivisorWithCoeffs.coeff_apply] using hE)
      (by rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl)
  rcases h with h0 | ⟨s, hs, hsnc⟩
  · refine (DivisorWithCoeffs.isSNC_zero (R := ℤ) sX).of_support_subset fun E hE => ?_
    have := hgen E hE
    rw [h0] at this
    exact this.elim
  · refine hsnc.of_support_subset fun E hE => ?_
    have hmem := hgen E hE
    rw [← hs] at hmem
    obtain ⟨E', hE', hx⟩ := Set.mem_iUnion₂.mp hmem
    obtain rfl := MMP.Threefold.Mori.primeDivisor_eq_of_genericPoint_mem_support E' E hx
    rw [Finsupp.mem_support_iff, Finsupp.finsetSum_apply,
      Finset.sum_eq_single_of_mem E' hE' (fun b _ hb => Finsupp.single_eq_of_ne' hb)]
    simp

/-- Adding a rational multiple of a numerically trivial `ℚ`-divisor does not change the
numerical class. -/
private theorem numericallyEquivalent_add_smul {k : Type} [Field k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {E N : QDivisor X} (hN : N.IsNumericallyTrivial k sX) (hE : E.IsQCartier) (q : ℚ)
    (hqN : (q • N).IsQCartier) :
    (E + q • N).NumericallyEquivalent k sX E := by
  obtain ⟨hN', hN0⟩ := (QDivisor.isNumericallyTrivial_iff N).mp hN
  refine ⟨hE.add hqN, hE, fun C i _ _ _ hC => ?_⟩
  rw [QDivisor.intersectionNumber_add' k sX i hC.le E (q • N) hE hqN,
    QDivisor.intersectionNumber_smul k sX i hC.le q N hN' hqN, hN0 C i hC, mul_zero, add_zero]

/-- On a proper scheme over `k`, `𝒪_X(E)` has a nonzero global section if and only if
`h⁰(X, 𝒪_X(E)) > 0`. -/
private theorem exists_ne_zero_iff_finrank_pos {k : Type} [Field k] {X : Scheme.{0}}
    [IsLocallyNoetherian X] [IsNormal X] (sX : X ⟶ Spec (.of k)) [IsProper sX] (E : Divisor X)
    [E.divisorialSheaf.IsCoherent] :
    (∃ σ : E.divisorialSubmodule ⊤, σ ≠ 0) ↔
      0 < Module.finrank k (cohomologyOverField k sX E.divisorialSheaf 0) := by
  have := finiteDimensional_cohomologyOverField_of_isProper k sX E.divisorialSheaf 0
  rw [Module.finrank_pos_iff_exists_ne_zero]
  let e := (cohomologyOverFieldZeroIsoSections k sX E.divisorialSheaf).toLinearEquiv
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨e.symm σ, (LinearEquiv.map_ne_zero_iff e.symm).mpr hσ⟩
  · rintro ⟨s, hs⟩
    exact ⟨e s, (LinearEquiv.map_ne_zero_iff e).mpr hs⟩

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

/-- On an integral scheme, an effective divisor `E` has the nonzero global section `1` of
`𝒪_X(E)`. -/
private theorem exists_ne_zero_of_nonneg {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] {E : Divisor X} (hE : 0 ≤ E) : ∃ σ : E.divisorialSubmodule ⊤, σ ≠ 0 := by
  have : Nontrivial (RationalFunctions X) := Pi.nontrivial_at
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, fun _ _ _ => Set.subset_univ _⟩
  refine ⟨⟨_, MMP.Fourfold.one_mem_divisorialSections hE⟩, fun h1 => ?_⟩
  have := congrArg (fun σ : E.divisorialSubmodule ⊤ => rationalFunctionsPresheafTopEquiv X σ) h1
  simp at this

/-- **Kawamata–Viehweg for the datum.** For a smooth non-vanishing datum `(X, D, G, a)` with
`D ≡ 0`, the higher cohomology of `𝒪_X(jD + ⌈G⌉)` vanishes for every `j`, because
`jD + G - K_X ≡ aD + G - K_X` is ample; hence `χ(X, jD + ⌈G⌉) = h⁰(X, jD + ⌈G⌉)`. -/
private theorem eulerCharacteristic_eq_finrank_zero_smul_add_roundUp {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ}
    {K D : Divisor X} {G : QDivisor X} {a : ℚ} (h : IsSmoothNonvanishingDatum sX n K D G a)
    (hD : (Divisor.toQDivisor D).IsNumericallyTrivial k sX) (j : ℤ)
    [(j • D + G.roundUp).divisorialSheaf.IsCoherent] :
    haveI : IsProper sX := h.isProperVariety.toIsProper
    eulerCharacteristic k sX (j • D + G.roundUp).divisorialSheaf =
      Module.finrank k (cohomologyOverField k sX (j • D + G.roundUp).divisorialSheaf 0) := by
  have hsm := h.isSmoothScheme
  have : Smooth sX := hsm.smooth
  have : IsProper sX := h.isProperVariety.toIsProper
  have : AlgebraicGeometry.IsProjectiveVariety k sX := h.isProjectiveVariety
  have hQC : ∀ E : QDivisor X, E.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  set A := a • Divisor.toQDivisor D + G - Divisor.toQDivisor K
  have hB : (Divisor.toQDivisor (j • D - K) + G).NumericallyEquivalent k sX
      (A + ∑ i ∈ (∅ : Finset ℕ), (fun _ => (0 : QDivisor X)) i) := by
    rw [Finset.sum_empty, add_zero]
    convert numericallyEquivalent_add_smul hD (hQC A) ((j : ℚ) - a) (hQC _) using 1
    simp only [A, map_sub, map_zsmul, sub_smul, ← Int.cast_smul_eq_zsmul ℚ]
    abel
  obtain ⟨hnef, hbig⟩ := QDivisor.isNef_and_isBig_of_isAmple sX <|
    QDivisor.isAmple_of_numericallyEquivalent_add_sum_of_isNef sX ∅ _ h.isAmple (by simp) hB
  have hround : K + (Divisor.toQDivisor (j • D - K) + G).roundUp = j • D + G.roundUp := by
    ext E
    simp only [DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_roundUp,
      Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_sub]
    rw [Int.ceil_intCast_add]
    ring
  have := subsingleton_derivedCohomologyOverField_divisorialSheaf_canonical_add_roundUp sX hsm
    h.isKltPair.1.2.1 (j • D - K) G (isSNC_of_isSNCSubset_supp h.isSNCSubset) hnef hbig
  rw [hround] at this
  exact eulerCharacteristic_eq_finrank_zero sX _ this

end MMP.FourfoldProofs.Km3aNonvanishingNumericallyTrivialProof

end

section

/-!
# Non-vanishing for a numerically trivial divisor

Let `k` be an algebraically closed field of characteristic 0 and `(X, D, G, a)` a smooth
non-vanishing datum over `k`: `X` is a smooth projective variety, `D` a nef
Cartier divisor, `G` a `ℚ`-divisor with `(X, -G)` klt and `Supp G` an snc divisor, and `a > 0`
with `aD + G - K_X` ample. If `D ≡ 0`, then `H⁰(X, mD + ⌈G⌉) ≠ 0` for every integer `m ≥ 0`:
Kawamata–Viehweg vanishing for the round-up makes `h⁰(X, mD + ⌈G⌉)` the Euler characteristic,
which depends only on the numerical class, and `⌈G⌉` is effective, so `h⁰(X, ⌈G⌉) ≥ 1`.

## Main results

* `MMP.Mori.IsSmoothNonvanishingDatum.exists_ne_zero_of_isNumericallyTrivial`: the
  non-vanishing statement for `D ≡ 0`, for every `m ≥ 0`.

## Implementation notes

`H⁰(X, B) ≠ 0` is the existence of a nonzero global section of `𝒪_X(B)`, as in
`MMP.Mori.HasNonvanishingProperty`; `D ≡ 0` is numerical triviality of the `ℚ`-divisor
associated to `D`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], proof of
  Theorem 3.4, 3.5 Step 1
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Mori

open MMP.FourfoldProofs.Km3aNonvanishingNumericallyTrivialProof in
/-- **Non-vanishing in the numerically trivial case** (Kollár–Mori 3.5, Step 1). If
`(X, D, G, a)` is a smooth non-vanishing datum with `D ≡ 0`, then `H⁰(X, mD + ⌈G⌉) ≠ 0` for every
integer `m ≥ 0`. -/
@[mmp "lem_km3a_nonvanishing_numerically_trivial"]
public theorem IsSmoothNonvanishingDatum.exists_ne_zero_of_isNumericallyTrivial
    {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX]
    {n : ℕ} {K D : Divisor X} {G : QDivisor X} {a : ℚ}
    (h : IsSmoothNonvanishingDatum sX n K D G a)
    (hD : (Divisor.toQDivisor D).IsNumericallyTrivial k sX) {m : ℤ} (_hm : 0 ≤ m) :
    ∃ σ : (m • D + G.roundUp).divisorialSubmodule ⊤, σ ≠ 0 := by
  have hsm := h.isSmoothScheme
  have : IsProper sX := h.isProperVariety.toIsProper
  have : AlgebraicGeometry.IsProjectiveVariety k sX := h.isProjectiveVariety
  have (E : Divisor X) : E.divisorialSheaf.IsCoherent :=
    (MMP.Threefold.isCoherent_divisorialSheaf_and_isIso_divisorialSheafTensorMul sX
      h.isProperVariety.toIsVariety E 0).1
  have hQC : ∀ E : QDivisor X, E.IsQCartier := MMP.Fourfold.isQCartier_of_isSmoothScheme hsm
  have hχ := Divisor.eulerCharacteristic_divisorialSheaf_eq_of_numericallyEquivalent sX hsm
    (D := m • D + G.roundUp) (D' := G.roundUp) <| by
      convert numericallyEquivalent_add_smul hD (hQC (Divisor.toQDivisor G.roundUp)) (m : ℚ)
        (hQC _) using 1
      rw [map_add, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ, add_comm]
  have h0 := eulerCharacteristic_eq_finrank_zero_smul_add_roundUp h hD 0
  rw [zero_smul, zero_add] at h0
  rw [exists_ne_zero_iff_finrank_pos sX, ← Nat.cast_pos (α := ℤ),
    ← eulerCharacteristic_eq_finrank_zero_smul_add_roundUp h hD m, hχ, h0, Nat.cast_pos,
    ← exists_ne_zero_iff_finrank_pos sX]
  exact exists_ne_zero_of_nonneg <| DivisorWithCoeffs.isEffective_iff_nonneg.mp
    (IsKltPair.neg_one_lt_coeff_and_isEffective_roundUp h.isKltPair).2

end MMP.Mori

end
