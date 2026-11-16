module

public import MMP.Attr
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import StacksFrontier.RingTheory.RegularLocalRing.Basic

/-!
# Integrality and discrete valuation rings (Kollár 1.22–1.32)

Kollár, *Lectures on resolution of singularities*, 1.22–1.32: the determinant trick, discrete
valuation rings (every non-zero element of the fraction field is uniquely `tⁿ u`; regular local
rings of dimension one), and localizations of a unique factorization domain at prime elements.

That `s` is integral over `S` if and only if `S[s]` is a finitely generated `S`-module (Kollár
1.26) is Mathlib's `IsIntegral.fg_adjoin_singleton` and `IsIntegral.of_mem_of_fg`, recorded as
library coverage and not restated.

## Main statements

* `MMP.Resolution.Kollar.isIntegral_of_faithful_fg_submodule`: the determinant trick (1.32).
* `MMP.Resolution.Kollar.existsUnique_zpow_mul_unit`: in a DVR with `𝔪 = tR`, every non-zero
  `z ∈ Q(R)` is uniquely `tⁿ u` with `n ∈ ℤ`, `u ∈ R^×` (1.22).
* `MMP.Resolution.Kollar.isDiscreteValuationRing_of_ringKrullDim_eq_one`: a regular local ring of
  dimension one is a DVR.
* `MMP.Resolution.Kollar.isDiscreteValuationRing_localization_span_prime`: for a prime element `p`
  of a UFD `S`, `S_{(p)}` is a DVR with maximal ideal `p S_{(p)}` (proof of 1.24).
* `MMP.Resolution.Kollar.exists_eq_iff_forall_prime`: a UFD is the intersection of its
  localizations `S_{(p)} = {a / b : p ∤ b}` at prime elements, inside `Q(S)` (proof of 1.24).

## Implementation notes

`Q(S)` is any `S`-algebra `K` with `IsFractionRing S K`. The localization `S_{(p)}` is
`Localization.AtPrime (Ideal.span {p})`; inside `Q(S)` it is described, as in the source, as the
set of fractions `a / b` with `p ∤ b`.
-/

@[expose] public section

namespace MMP.Resolution.Kollar

/-- **Kollár 1.32** (the determinant trick). Let `A ⊆ B` be rings, `z ∈ B`, and `M ⊆ B` a finitely
generated `A`-submodule with `zM ⊆ M` such that the only `b ∈ B` with `bM = 0` is `b = 0`. Then
`z` is integral over `A`. -/
@[mmp "lem_kr1b_determinant_trick"]
theorem isIntegral_of_faithful_fg_submodule {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submodule A B) (hM : M.FG) {z : B} (hz : ∀ m ∈ M, z * m ∈ M)
    (hfaith : ∀ b : B, (∀ m ∈ M, b * m = 0) → b = 0) : IsIntegral A z := by
  have : Module.Finite A M := Module.Finite.iff_fg.mpr hM
  let f : Module.End A M := (LinearMap.mulLeft A z).restrict hz
  obtain ⟨p, hp, h0⟩ := LinearMap.exists_monic_and_aeval_eq_zero A f
  refine ⟨p, hp, hfaith _ fun m hm => ?_⟩
  have hf : ∀ m : M, ((f m : M) : B) = z * (m : B) := fun m => rfl
  have hpow : ∀ n : ℕ, ∀ m : M, (((f ^ n) m : M) : B) = z ^ n * (m : B) := by
    intro n m
    induction n generalizing m with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ih, hf]
      ring
  have key : ∀ q : Polynomial A, ∀ m : M,
      ((Polynomial.aeval f q m : M) : B) = Polynomial.aeval z q * (m : B) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add q r hq hr =>
      intro m
      simp [hq, hr, add_mul]
    | monomial n a =>
      intro m
      simp [Polynomial.aeval_monomial, hpow, Algebra.smul_def, mul_assoc]
  rw [← Polynomial.aeval_def]
  simpa [h0] using (key p ⟨m, hm⟩).symm

section DVR

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] in
private lemma false_of_zpow_mul_unit_lt {t : R} (ht : Irreducible t) {n m : ℤ} (hnm : m < n)
    (u v : Rˣ) (h : algebraMap R K t ^ n * algebraMap R K (u : R) =
      algebraMap R K t ^ m * algebraMap R K (v : R)) : False := by
  have hτ : algebraMap R K t ≠ 0 := by simpa using ht.ne_zero
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n - m = k + 1 := ⟨(n - m - 1).toNat, by omega⟩
  have h1 : algebraMap R K t ^ (k + 1) * algebraMap R K (u : R) = algebraMap R K (v : R) := by
    rw [show n = m + (k + 1 : ℕ) by omega, zpow_add₀ hτ, zpow_natCast, mul_assoc] at h
    exact mul_left_cancel₀ (zpow_ne_zero _ hτ) h
  have h2 : t ^ (k + 1) * (u : R) = (v : R) := by
    apply IsFractionRing.injective R K
    simpa using h1
  exact ht.not_isUnit ((isUnit_pow_iff k.succ_ne_zero).mp
    (IsUnit.mul_iff.mp (h2 ▸ v.isUnit)).1)

/-- **Kollár 1.22.** Let `R` be a DVR whose maximal ideal is `𝔪 = tR`. Then every non-zero
`z ∈ Q(R)` can be written as `z = tⁿ u` with `n ∈ ℤ` and `u` a unit of `R`, and the pair
`(n, u)` is unique. -/
@[mmp "lem_kr1b_dvr_unit_times_power"]
theorem existsUnique_zpow_mul_unit {t : R} (ht : IsLocalRing.maximalIdeal R = Ideal.span {t})
    {z : K} (hz : z ≠ 0) :
    ∃! nu : ℤ × Rˣ, z = algebraMap R K t ^ nu.1 * algebraMap R K (nu.2 : R) := by
  have hirr : Irreducible t := (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr ht
  have hτ : algebraMap R K t ≠ 0 := by simpa using hirr.ne_zero
  obtain ⟨n, u, hz'⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    (K := K) hirr hz
  refine ⟨(n, u), ?_, ?_⟩
  · rw [hz', Units.smul_def, Algebra.smul_def, mul_comm]
  · rintro ⟨m, v⟩ hv
    have h : algebraMap R K t ^ n * algebraMap R K (u : R) =
        algebraMap R K t ^ m * algebraMap R K (v : R) := by
      rw [← hv, hz', Units.smul_def, Algebra.smul_def, mul_comm]
    rcases lt_trichotomy n m with hlt | rfl | hgt
    · exact (false_of_zpow_mul_unit_lt hirr hlt v u h.symm).elim
    · obtain rfl :=
        Units.ext (IsFractionRing.injective R K (mul_left_cancel₀ (zpow_ne_zero _ hτ) h))
      rfl
    · exact (false_of_zpow_mul_unit_lt hirr hgt u v h).elim

end DVR

/-- A regular local ring of dimension one is a DVR (used in Kollár 1.36). Being a DVR includes
being a domain, which is part of the conclusion. -/
@[mmp "lem_kr1b_regular_local_dim_one_dvr"]
theorem isDiscreteValuationRing_of_ringKrullDim_eq_one {A : Type*} [CommRing A]
    [IsRegularLocalRing A] (hA : ringKrullDim A = 1) :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by
  have hd : IsDomain A := IsRegularLocalRing.isDomain A
  refine ⟨hd, ?_⟩
  have hf : ¬ IsField A := fun h => by simp [ringKrullDim_eq_zero_of_isField h] at hA
  have hs := IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)
  rw [hA] at hs
  have h1 : (IsLocalRing.maximalIdeal A).spanFinrank = 1 := by exact_mod_cast hs
  exact ((IsDiscreteValuationRing.TFAE A hf).out 5 1).mp
    ((Submodule.spanFinrank_eq_one_iff _).mp h1).1

section UFD

variable {S : Type*} [CommRing S] [IsDomain S] [UniqueFactorizationMonoid S]

/-- **Kollár, proof of Lemma 1.24.** Let `S` be a unique factorization domain and `p ∈ S` a prime
element. Then the localization `S_{(p)}` is a DVR whose maximal ideal is `p S_{(p)}`. -/
@[mmp "lem_kr1b_ufd_localization_at_prime_element_dvr"]
theorem isDiscreteValuationRing_localization_span_prime {p : S} (hp : Prime p) :
    have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {p})) ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {p})) =
        Ideal.span {algebraMap S (Localization.AtPrime (Ideal.span {p})) p} := by
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime (Ideal.span {p})) =
        Ideal.span {algebraMap S (Localization.AtPrime (Ideal.span {p})) p} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {p}), Ideal.map_span,
      Set.image_singleton]
  refine ⟨?_, hmax⟩
  have : IsDomain (Localization.AtPrime (Ideal.span {p})) :=
    IsLocalization.isDomain_of_atPrime _ (Ideal.span {p})
  have hπ : Prime (algebraMap S (Localization.AtPrime (Ideal.span {p})) p) := by
    have hne : algebraMap S (Localization.AtPrime (Ideal.span {p})) p ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap S (Localization.AtPrime (Ideal.span {p})))]
      exact fun h => hp.ne_zero
        ((IsLocalization.injective _ (Ideal.span {p}).primeCompl_le_nonZeroDivisors) h)
    rw [← Ideal.span_singleton_prime hne, ← hmax]
    exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨_, hπ.irreducible, fun {x} hx => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {p}).primeCompl x
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨n, a', hna, rfl⟩ := WfDvdMonoid.max_power_factor ha hp.irreducible
  obtain ⟨u, hu'⟩ := IsLocalization.map_units (Localization.AtPrime (Ideal.span {p}))
    (⟨a', by rwa [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton]⟩ :
      (Ideal.span {p}).primeCompl)
  obtain ⟨v, hv'⟩ := IsLocalization.map_units (Localization.AtPrime (Ideal.span {p})) s
  refine ⟨n, u * v⁻¹, ?_⟩
  change _ = IsLocalization.mk' (Localization.AtPrime (Ideal.span {p})) (p ^ n * a') s
  rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, map_mul, map_pow, ← hv', ← hu']
  simp [mul_assoc]

/-- **Kollár, proof of Lemma 1.24.** Let `S` be a unique factorization domain. Then
`S = ⋂_p S_{(p)}` inside `Q(S)`, the intersection over all prime elements `p` of `S`, where
`S_{(p)} = {a / b : a, b ∈ S, p ∤ b}` (and the intersection is `Q(S)` if `S` has no prime
element). -/
@[mmp "lem_kr1b_ufd_intersection_localizations"]
theorem exists_eq_iff_forall_prime (K : Type*) [Field K] [Algebra S K] [IsFractionRing S K]
    (x : K) :
    (∃ s : S, algebraMap S K s = x) ↔
      ∀ p : S, Prime p → ∃ a b : S, ¬ p ∣ b ∧ x * algebraMap S K b = algebraMap S K a := by
  constructor
  · rintro ⟨s, rfl⟩ p hp
    exact ⟨s, 1, fun h => hp.not_isUnit (isUnit_of_dvd_one h), by simp⟩
  · intro H
    have key : ∀ b : S, b ≠ 0 → ∀ a : S, x * algebraMap S K b = algebraMap S K a →
        ∃ s : S, algebraMap S K s = x := by
      intro b
      induction b using UniqueFactorizationMonoid.induction_on_prime with
      | h₁ => exact fun h => absurd rfl h
      | h₂ b hb =>
        rintro - a h
        obtain ⟨u, rfl⟩ := hb
        refine ⟨a * ↑u⁻¹, mul_right_cancel₀ (b := algebraMap S K (u : S)) (by simp) ?_⟩
        rw [map_mul, h]
        simp
      | h₃ b q hb hq ih =>
        rintro - a h
        obtain ⟨a1, b1, hb1, h1⟩ := H q hq
        rw [map_mul] at h
        have e : a * b1 = q * b * a1 := by
          apply IsFractionRing.injective S K
          simp only [map_mul]
          rw [← h, ← h1]
          ring
        obtain ⟨a2, rfl⟩ := (hq.dvd_or_dvd ⟨b * a1, by rw [e]; ring⟩).resolve_right hb1
        refine ih hb a2 (mul_left_cancel₀ (a := algebraMap S K q) (by simpa using hq.ne_zero) ?_)
        rw [map_mul] at h
        linear_combination h
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := S) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hb0' : algebraMap S K b ≠ 0 := by simpa using hb0
    exact key b hb0 a (by rw [← hab]; field_simp)

end UFD

end MMP.Resolution.Kollar
