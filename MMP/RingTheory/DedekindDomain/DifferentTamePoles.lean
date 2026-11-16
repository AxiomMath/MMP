module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Traces of elements with tame poles

Let `B / A` be a finite extension of Dedekind domains with separable fraction field extension
`L / K`, and `𝔭 ≠ 0` a maximal ideal of `A`. If `𝔓₁, …, 𝔓ᵣ` are distinct primes of `B` with
`𝔓ᵢ^{eᵢ} ∣ 𝔭 B`, then `∏ 𝔓ᵢ^{eᵢ - 1}` divides the different `𝔇_{B/A}`, so every `x ∈ L` with
`x ∏ 𝔓ᵢ^{eᵢ - 1} ⊆ B` has `Tr_{L/K}(x) ∈ A`: an element of `L` whose poles are at primes over
`𝔭`, each of order less than the ramification index there, has an integral trace.

Applied at the generic points of the branch divisors of a finite cover of smooth varieties in
characteristic zero, this is the regularity of the normalized trace on forms with poles of order
less than the ramification index, which makes the trace a left inverse of the pullback on the
fractional logarithmic complex.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.differentIdeal_le_prod_pow_sub_one`:
  `𝔇_{B/A} ⊆ ∏ 𝔓ᵢ^{eᵢ - 1}`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_algebraMap_eq_trace_of_mem_inv_prod`:
  `Tr_{L/K}(x) ∈ A` for `x ∈ (∏ 𝔓ᵢ^{eᵢ - 1})⁻¹`.

## References

* [J.-P. Serre, *Corps locaux*][Serre1962], Chapitre III, §6
-/

@[expose] public section

open nonZeroDivisors

namespace MMP.FourfoldProofs.FractionalLogComplexProof

variable {A K L B : Type*} [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDedekindDomain A] [IsFractionRing A K] [IsDedekindDomain B] [IsFractionRing B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.IsTorsionFree A B] [Module.Finite A B]

variable (K L) in
include K L in
/-- **The tame part of the different.** For distinct primes `𝔓ᵢ` of `B` with `𝔓ᵢ^{eᵢ} ∣ 𝔭 B`,
`𝔭 ≠ 0` maximal, the different `𝔇_{B/A}` is contained in `∏ 𝔓ᵢ^{eᵢ - 1}`. -/
theorem differentIdeal_le_prod_pow_sub_one {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    {ι : Type*} (s : Finset ι) (P : ι → Ideal B) (e : ι → ℕ)
    (hPp : ∀ i ∈ s, Prime (P i)) (hPinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i ≠ P j)
    (hPe : ∀ i ∈ s, P i ^ e i ∣ p.map (algebraMap A B)) :
    differentIdeal A B ≤ ∏ i ∈ s, P i ^ (e i - 1) := by
  rw [← IsDedekindDomain.inf_pow_eq_prod_of_prime s P (fun i => e i - 1) hPp hPinj]
  refine Finset.le_inf fun i hi => Ideal.le_of_dvd ?_
  by_cases he : e i = 0
  · rw [he, Nat.zero_sub, pow_zero]
    exact one_dvd _
  exact pow_sub_one_dvd_differentIdeal_aux A K L (P i) he hp (hPe i hi)

/-- **Elements with tame poles have integral traces.** For distinct primes `𝔓ᵢ` of `B` with
`𝔓ᵢ^{eᵢ} ∣ 𝔭 B`, `𝔭 ≠ 0` maximal, every `x ∈ L` with `x ∏ 𝔓ᵢ^{eᵢ - 1} ⊆ B` has
`Tr_{L/K}(x) ∈ A`. -/
theorem exists_algebraMap_eq_trace_of_mem_inv_prod {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥)
    {ι : Type*} (s : Finset ι) (P : ι → Ideal B) (e : ι → ℕ)
    (hPp : ∀ i ∈ s, Prime (P i)) (hPinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i ≠ P j)
    (hPe : ∀ i ∈ s, P i ^ e i ∣ p.map (algebraMap A B)) {x : L}
    (hx : x ∈ ((∏ i ∈ s, P i ^ (e i - 1) : Ideal B) : FractionalIdeal B⁰ L)⁻¹) :
    ∃ a : A, algebraMap A K a = Algebra.trace K L x := by
  have hI : (∏ i ∈ s, P i ^ (e i - 1) : Ideal B) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.2 fun i hi => pow_ne_zero _ (hPp i hi).ne_zero
  have h := (differentialIdeal_le_iff (K := K) (L := L) hI).1
    (differentIdeal_le_prod_pow_sub_one K L hp s P e hPp hPinj hPe)
  exact Submodule.mem_one.1 (h ⟨x, hx, rfl⟩)

end MMP.FourfoldProofs.FractionalLogComplexProof
