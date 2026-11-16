module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The factor `z / g₀ h_S` at a prime divisor

Near a point of `V` a local generator `g₀` of `𝒪_V(-M)` satisfies `g₀^N = u v ∏ₖ τₖ^{bₖ}`, with `u`
the given unit on `V ∖ (D ∪ Supp M)`, `v` a unit, `τₖ` local equations of the components of `D`
and `bₖ = Bn(jₖ) < N`; with `h_S = ∏_{k ∈ S} τₖ` the local equation of `S` and `z^N = u` on the
cover, `(z / g₀ h_S)^N = (v ∏ₖ τₖ^{bₖ} h_S^N)⁻¹`. At the generic point of a prime divisor `E`,
with local ring `A` and uniformizer `t`:

* if `E` is none of the `jₖ`, every `τₖ` is a unit and `(v ∏ τₖ^{bₖ} h_S^N)⁻¹ ∈ A`;
* if `E = j_{k₀}` is a component of `Supp Bn` not in `S`, with `τ_{k₀} = t`, then
  `tᴺ (v ∏ τₖ^{bₖ} h_S^N)⁻¹ ∈ 𝔪_A`, since `b_{k₀} < N`;
* if `E = j_{k₀}` is a component of `S`, with `τ_{k₀} = t` and `b_{k₀} = 0`, then
  `tᴺ (v ∏ τₖ^{bₖ} h_S^N)⁻¹ ∈ A`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.inv_mem_range_of_isUnit`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.pow_mul_inv_mem_maximalIdeal_of_lt`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.pow_mul_inv_mem_range_of_mem`: the three cases.
-/

@[expose] public section

open IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

variable {A K : Type*} [CommRing A] [IsDomain A] [IsLocalRing A] [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- The factor `v ∏ₖ τₖ^{bₖ} (∏_{k ∈ T} τₖ)^N`, i.e. `v ∏ τₖ^{bₖ} h_S^N` with `h_S` the product
of the `τₖ` over `T`. -/
def zDenom {r : ℕ} (v : A) (τ : Fin r → A) (b : Fin r → ℕ) (T : Finset (Fin r)) (N : ℕ) : A :=
  v * (∏ k, τ k ^ b k) * (∏ k ∈ T, τ k) ^ N

omit [IsDomain A] [IsLocalRing A] [IsFractionRing A K] in
/-- If `v` and all the `τₖ` are units, then so is `v ∏ τₖ^{bₖ} h_S^N`. -/
theorem isUnit_zDenom {r : ℕ} {v : A} (hv : IsUnit v) {τ : Fin r → A} (hτ : ∀ k, IsUnit (τ k))
    (b : Fin r → ℕ) (T : Finset (Fin r)) (N : ℕ) : IsUnit (zDenom v τ b T N) := by
  unfold zDenom
  exact (hv.mul (IsUnit.prod_univ_iff.2 fun k => (hτ k).pow _)).mul
    ((IsUnit.prod_iff.2 fun k _ => hτ k).pow _)

omit [IsDomain A] [IsLocalRing A] [IsFractionRing A K] in
/-- **Off the divisor**: if `v` and all the `τₖ` are units, then `(v ∏ τₖ^{bₖ} h_S^N)⁻¹ ∈ A`. -/
theorem inv_mem_range_of_isUnit {r : ℕ} {v : A} (hv : IsUnit v) {τ : Fin r → A}
    (hτ : ∀ k, IsUnit (τ k)) (b : Fin r → ℕ) (T : Finset (Fin r)) (N : ℕ) :
    (algebraMap A K (zDenom v τ b T N))⁻¹ ∈ (algebraMap A K).range := by
  obtain ⟨w, hw⟩ := isUnit_zDenom hv hτ b T N
  exact ⟨↑w⁻¹, hw ▸ map_units_inv (algebraMap A K) w⟩

omit [IsDomain A] in
/-- **At a component of `Supp Bn` not in `S`**: `tᴺ (v ∏ τₖ^{bₖ} h_S^N)⁻¹ ∈ 𝔪_A`. -/
theorem pow_mul_inv_mem_maximalIdeal_of_lt {r : ℕ} {v : A} (hv : IsUnit v) {τ : Fin r → A}
    {k₀ : Fin r} {t : A} (htm : t ∈ maximalIdeal A) (ht0 : t ≠ 0) (hτ₀ : τ k₀ = t)
    (hτ : ∀ k, k ≠ k₀ → IsUnit (τ k)) (b : Fin r → ℕ) {T : Finset (Fin r)} (hT : k₀ ∉ T)
    {N : ℕ} (hb : b k₀ < N) :
    ∃ a ∈ maximalIdeal A, algebraMap A K a =
      algebraMap A K t ^ N * (algebraMap A K (zDenom v τ b T N))⁻¹ := by
  classical
  have hT' : IsUnit (∏ k ∈ T, τ k) :=
    IsUnit.prod_iff.2 fun k hk => hτ k fun h => hT (h ▸ hk)
  have hP' : IsUnit (∏ k ∈ Finset.univ.erase k₀, τ k ^ b k) :=
    IsUnit.prod_iff.2 fun k hk => (hτ k (Finset.ne_of_mem_erase hk)).pow _
  obtain ⟨w, hw⟩ := (hv.mul hP').mul (hT'.pow N)
  refine ⟨t ^ (N - b k₀) * ↑w⁻¹, Ideal.mul_mem_right _ _
    (Ideal.pow_mem_of_mem _ htm _ (by omega)), ?_⟩
  have hden : zDenom v τ b T N = t ^ b k₀ * ↑w := by
    unfold zDenom
    rw [hw, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀), hτ₀]
    ring
  have htK : algebraMap A K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht0
  have hpow : algebraMap A K t ^ N = algebraMap A K t ^ (N - b k₀) * algebraMap A K t ^ b k₀ := by
    rw [← pow_add, Nat.sub_add_cancel hb.le]
  rw [hden, map_mul, map_mul, map_pow, map_pow, mul_inv, hpow, mul_assoc,
    ← mul_assoc (algebraMap A K t ^ b k₀), mul_inv_cancel₀ (pow_ne_zero _ htK), one_mul,
    map_units_inv]

omit [IsDomain A] [IsLocalRing A] in
/-- **At a component of `S`**: `tᴺ (v ∏ τₖ^{bₖ} h_S^N)⁻¹ ∈ A`. -/
theorem pow_mul_inv_mem_range_of_mem {r : ℕ} {v : A} (hv : IsUnit v) {τ : Fin r → A}
    {k₀ : Fin r} {t : A} (ht0 : t ≠ 0) (hτ₀ : τ k₀ = t)
    (hτ : ∀ k, k ≠ k₀ → IsUnit (τ k)) (b : Fin r → ℕ) (hb : b k₀ = 0) {T : Finset (Fin r)}
    (hT : k₀ ∈ T) (N : ℕ) :
    algebraMap A K t ^ N * (algebraMap A K (zDenom v τ b T N))⁻¹ ∈ (algebraMap A K).range := by
  classical
  have hT' : IsUnit (∏ k ∈ T.erase k₀, τ k) :=
    IsUnit.prod_iff.2 fun k hk => hτ k (Finset.ne_of_mem_erase hk)
  have hP' : IsUnit (∏ k ∈ Finset.univ.erase k₀, τ k ^ b k) :=
    IsUnit.prod_iff.2 fun k hk => (hτ k (Finset.ne_of_mem_erase hk)).pow _
  obtain ⟨w, hw⟩ := (hv.mul hP').mul (hT'.pow N)
  have hden : zDenom v τ b T N = t ^ N * ↑w := by
    unfold zDenom
    rw [hw, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k₀),
      ← Finset.mul_prod_erase T _ hT, hτ₀, hb, pow_zero, one_mul, mul_pow]
    ring
  have htK : algebraMap A K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 ht0
  refine ⟨↑w⁻¹, ?_⟩
  rw [hden, map_mul, map_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ htK), one_mul]
  exact map_units_inv (algebraMap A K) w

end MMP.FourfoldProofs.FractionalLogComplexProof
