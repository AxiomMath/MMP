module

public import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupEmbedded
public import MMP.RingTheory.DiscreteValuationRing.Integrality

/-!
# The DVR-normalization of a domain (Kollár 1.23–1.26)

The DVR-normalization `S̄^dvr ⊆ Q(S)` of an integral domain `S` (Kollár Definition 1.23,
`MMP.Resolution.dvrNormalization`) is the set of `z ∈ Q(S)` with `Φ_φ(z) ∈ R` for every DVR `R`
and every injective ring homomorphism `φ : S → R`.

That the elements integral over `S` form a subring containing `S` (Kollár 1.26) is Mathlib's
`integralClosure`, recorded as library coverage and not restated.

## Main statements

* `MMP.Resolution.Kollar.mem_dvrNormalization_of_monic_eval_eq_zero`: an element of `Q(S)`
  satisfying a monic equation over `S` lies in `S̄^dvr` (Lemma 1.25).
* `MMP.Resolution.Kollar.dvrNormalization_eq_range`: for a unique factorization domain `S`,
  `S̄^dvr = S` (Lemma 1.24).
-/

@[expose] public section

universe u

namespace MMP.Resolution.Kollar

variable {S : Type u} [CommRing S]

private lemma map_fractionRing_algebraMap {R : Type u} [CommRing R] [IsDomain R] (φ : S →+* R)
    (hφ : Function.Injective φ) (x : S) :
    IsFractionRing.map (K := FractionRing S) (L := FractionRing R) hφ
        (algebraMap S (FractionRing S) x) = algebraMap R (FractionRing R) (φ x) :=
  IsLocalization.map_eq (M := nonZeroDivisors S) (S := FractionRing S) (Q := FractionRing R)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) x

/-- **Kollár, Lemma 1.25.** Let `S` be an integral domain and `t ∈ Q(S)` an element satisfying
`t^m + s_{m-1} t^{m-1} + ⋯ + s₀ = 0` for some `m ≥ 1` and `s₀, …, s_{m-1} ∈ S`. Then
`t ∈ S̄^dvr`. (The hypothesis `m ≥ 1` is dropped: for `m = 0` the equation reads `1 = 0`.) -/
@[mmp "lem_kr1b_integral_implies_dvr_normalization"]
theorem mem_dvrNormalization_of_monic_eval_eq_zero {t : FractionRing S} {m : ℕ} (s : Fin m → S)
    (ht : t ^ m + ∑ i : Fin m, algebraMap S (FractionRing S) (s i) * t ^ (i : ℕ) = 0) :
    t ∈ MMP.Resolution.dvrNormalization S := by
  intro R _ _ _ φ hφ
  set Φ := IsFractionRing.map (K := FractionRing S) (L := FractionRing R) hφ
  have heq : Φ t ^ m + ∑ i : Fin m, algebraMap R (FractionRing R) (φ (s i)) * Φ t ^ (i : ℕ)
      = 0 := by
    simpa [Φ, map_fractionRing_algebraMap φ hφ] using congrArg Φ ht
  refine IsIntegrallyClosed.algebraMap_eq_of_integral
    ⟨Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (φ (s i)) * Polynomial.X ^ (i : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  simpa [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum] using heq

/-- **Kollár, Lemma 1.24.** Let `S` be a unique factorization domain. Then `S̄^dvr = S`, that is,
the DVR-normalization of `S` is the image of `S` in `Q(S)`. -/
@[mmp "lem_kr1b_ufd_dvr_normal"]
theorem dvrNormalization_eq_range [IsDomain S] [UniqueFactorizationMonoid S] :
    MMP.Resolution.dvrNormalization S = Set.range (algebraMap S (FractionRing S)) := by
  ext z
  refine ⟨fun hz => ?_, ?_⟩
  · refine (exists_eq_iff_forall_prime (FractionRing S) z).mpr fun p hp => ?_
    have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    obtain ⟨hR, -⟩ := isDiscreteValuationRing_localization_span_prime hp
    have hinj : Function.Injective (algebraMap S (Localization.AtPrime (Ideal.span {p}))) :=
      IsLocalization.injective _ (Ideal.span {p}).primeCompl_le_nonZeroDivisors
    obtain ⟨r, hr⟩ := hz (Localization.AtPrime (Ideal.span {p})) _ hinj
    obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {p}).primeCompl r
    refine ⟨a, b, Ideal.mem_span_singleton.not.mp b.2, ?_⟩
    apply (IsFractionRing.map (K := FractionRing S)
      (L := FractionRing (Localization.AtPrime (Ideal.span {p}))) hinj).injective
    rw [map_mul, ← hr, map_fractionRing_algebraMap, map_fractionRing_algebraMap, ← map_mul,
      IsLocalization.mk'_spec]
  · rintro ⟨x, rfl⟩ R _ _ _ φ hφ
    exact ⟨φ x, (map_fractionRing_algebraMap φ hφ x).symm⟩

end MMP.Resolution.Kollar
