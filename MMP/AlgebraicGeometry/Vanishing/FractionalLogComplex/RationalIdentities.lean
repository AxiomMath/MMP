module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.Retract.Defs

/-!
# The rational identities of the retract

Let `L / K` be a finite separable extension of fields over a field `k` of characteristic zero,
`ψ ∈ K` non-zero and `z ∈ L` with `z^N = ψ`, `N ≥ 1`. Then `dz / z = N⁻¹ dψ / ψ`, and for the
connection `∇β = dβ - N⁻¹ (dψ/ψ) ∧ β` on the forms of `K`:

* `d(z⁻¹ β) = z⁻¹ ∇β` for forms `β` of `K`;
* `[L : K]⁻¹ Tr(z dγ) = ∇([L : K]⁻¹ Tr(z γ))` for forms `γ` of `L`, since the trace commutes with
  `d` and with the wedge by forms of `K`;
* `[L : K]⁻¹ Tr(z z⁻¹ β) = β`.

These are the clauses of `MMP.FourfoldProofs.FractionalLogComplexProof.RatCompat`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.D_eq_smul_of_pow_eq`: `dz = z (N ψ)⁻¹ dψ`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_wedgeLeft_map`: `Tr(a ∧ η) = a ∧ Tr(η)`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.ratCompat_of_pow_eq`: the rational identities.
-/

@[expose] public section

open KaehlerDifferential

namespace MMP.FourfoldProofs.FractionalLogComplexProof

section Trace

variable {k K L : Type} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]

omit [FiniteDimensional K L] in
/-- **The trace commutes with the wedge by a `1`-form of `K`.** -/
theorem formsTrace_wedgeLeft_map (p : ℕ) (a : Ω[K⁄k]) (η : ⋀[L]^p (Ω[L⁄k])) :
    formsTrace k K L (p + 1) (exteriorPower.wedgeLeft (map k k K L a) p η) =
      exteriorPower.wedgeLeft a p (formsTrace k K L p η) := by
  refine smul_mapExteriorPower_induction (k := k) (K := K) (L := L) p
    (P := fun η => formsTrace k K L (p + 1) (exteriorPower.wedgeLeft (map k k K L a) p η) =
      exteriorPower.wedgeLeft a p (formsTrace k K L p η)) ?_ ?_ ?_ η
  · simp only [map_zero]
  · intro b ω
    rw [LinearMap.map_smul, ← mapExteriorPower_wedgeLeft, formsTrace_smul_mapExteriorPower,
      formsTrace_smul_mapExteriorPower, map_smul]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, map_add, map_add]

end Trace

section Compat

variable {k K L : Type} [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra K L] [IsScalarTower k K L]

/-- **`dz = z (N ψ)⁻¹ dψ`** for `z^N = ψ`. -/
theorem D_eq_smul_of_pow_eq {N : ℕ} (hN : N ≠ 0) {ψ : K} {z : L}
    (hz : z ^ N = algebraMap K L ψ) (hz0 : z ≠ 0) :
    KaehlerDifferential.D k L z =
      (z * ((N : L) * algebraMap K L ψ)⁻¹) • map k k K L (KaehlerDifferential.D k K ψ) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  have hNL : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hs : z * ((N : L) * z ^ N)⁻¹ * ((N : L) * z ^ (N - 1)) = 1 := by
    have h1 : z ^ N = z * z ^ (N - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN)]
    have h2 : z ^ (N - 1) ≠ 0 := pow_ne_zero _ hz0
    rw [h1]
    field_simp
  calc KaehlerDifferential.D k L z = (1 : L) • KaehlerDifferential.D k L z := (one_smul _ _).symm
    _ = _ := by
      rw [← hs, map_D, ← hz, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul L, smul_smul,
        smul_smul]
      congr 1
      ring

/-- For `N ψ ≠ 0`, `N ψ β' = N ψ dβ - dψ ∧ β` holds iff `β' = dβ - (N ψ)⁻¹ dψ ∧ β`. -/
theorem smul_eq_connection_iff {N : ℕ} {ψ : K} (hNψ : (N : K) * ψ ≠ 0) (p : ℕ)
    (β : ⋀[K]^p (Ω[K⁄k])) (β' : ⋀[K]^(p + 1) (Ω[K⁄k])) :
    (N • (ψ • (β' : ExteriorAlgebra K Ω[K⁄k])) =
      N • (ψ • (deRhamDifferential (A := k) p β : ExteriorAlgebra K Ω[K⁄k])) -
        ExteriorAlgebra.ι K (KaehlerDifferential.D k K ψ) * (β : ExteriorAlgebra K Ω[K⁄k])) ↔
      β' = deRhamDifferential (A := k) p β -
        ((N : K) * ψ)⁻¹ • exteriorPower.wedgeLeft (KaehlerDifferential.D k K ψ) p β := by
  have e : ∀ x : ⋀[K]^(p + 1) (Ω[K⁄k]), N • (ψ • (x : ExteriorAlgebra K Ω[K⁄k])) =
      ((((N : K) * ψ) • x : ⋀[K]^(p + 1) (Ω[K⁄k])) : ExteriorAlgebra K Ω[K⁄k]) := by
    intro x
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, Submodule.coe_smul]
  rw [e, e, ← exteriorPower.coe_wedgeLeft, ← Submodule.coe_sub, SetLike.coe_eq_coe]
  constructor
  · intro h
    calc β' = ((N : K) * ψ)⁻¹ • (((N : K) * ψ) • β') := (inv_smul_smul₀ hNψ β').symm
      _ = _ := by rw [h, smul_sub, inv_smul_smul₀ hNψ]
  · intro h
    rw [h, smul_sub, smul_inv_smul₀ hNψ]

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- **The rational identities of the retract**: `RatCompat k K L N ψ z` holds when `z ^ N = ψ`
with `N ≠ 0` and `ψ ≠ 0`. -/
theorem ratCompat_of_pow_eq {N : ℕ} (hN : N ≠ 0) {ψ : K} (hψ : ψ ≠ 0) {z : L}
    (hz : z ^ N = algebraMap K L ψ) : RatCompat k K L N ψ z := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap k L).injective
  have hψL : algebraMap K L ψ ≠ 0 := (map_ne_zero _).2 hψ
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hz
    exact hψL hz.symm
  have hNψ : (N : K) * ψ ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hN) hψ
  have hDz := D_eq_smul_of_pow_eq (k := k) hN hz hz0
  have hNψL : algebraMap K L ((N : K) * ψ)⁻¹ = ((N : L) * algebraMap K L ψ)⁻¹ := by
    rw [map_inv₀, map_mul, map_natCast]
  refine ⟨fun p β β' h => ?_, fun p γ => (smul_eq_connection_iff hNψ p _ _).2 ?_, fun p β => ?_⟩
  · -- `d(z⁻¹ β) = z⁻¹ ∇β`
    rw [(smul_eq_connection_iff hNψ p β β').1 h, deRhamDifferential_smul,
      ← mapExteriorPower_deRhamDifferential, map_sub, map_smul, mapExteriorPower_wedgeLeft,
      Derivation.leibniz_inv, hDz, smul_smul, exteriorPower.wedgeLeft_smul, LinearMap.smul_apply,
      ← algebraMap_smul L ((N : K) * ψ)⁻¹, hNψL, smul_sub, smul_smul]
    have hA : z⁻¹ ^ 2 * (z * ((N : L) * algebraMap K L ψ)⁻¹) =
        z⁻¹ * ((N : L) * algebraMap K L ψ)⁻¹ := by
      rw [sq, mul_assoc, ← mul_assoc z⁻¹ z, inv_mul_cancel₀ hz0, one_mul]
    rw [neg_mul, hA, neg_smul]
    abel
  · -- `[L : K]⁻¹ Tr(z dγ) = ∇([L : K]⁻¹ Tr(z γ))`
    set c : K := (Module.finrank K L : K)
    have hc : c⁻¹ = algebraMap k K ((Module.finrank K L : k))⁻¹ := by
      rw [map_inv₀, map_natCast]
    have hdT : deRhamDifferential (A := k) p (formsTrace k K L p (z • γ)) =
        ((N : K) * ψ)⁻¹ • exteriorPower.wedgeLeft (KaehlerDifferential.D k K ψ) p
          (formsTrace k K L p (z • γ)) + formsTrace k K L (p + 1)
            (z • deRhamDifferential (A := k) p γ) := by
      rw [← formsTrace_deRhamDifferential, deRhamDifferential_smul, map_add, hDz,
        exteriorPower.wedgeLeft_smul, LinearMap.smul_apply, ← smul_smul, smul_comm z,
        ← (exteriorPower.wedgeLeft (map k k K L (KaehlerDifferential.D k K ψ)) p).map_smul z γ,
        ← hNψL, algebraMap_smul, (formsTrace k K L (p + 1)).map_smul ((N : K) * ψ)⁻¹,
        formsTrace_wedgeLeft_map]
    rw [hc, deRhamDifferential_algebraMap_smul, ← hc, hdT,
      (exteriorPower.wedgeLeft (KaehlerDifferential.D k K ψ) p).map_smul]
    module
  · -- `[L : K]⁻¹ Tr(z z⁻¹ β) = β`
    have hc0 : (Module.finrank K L : K) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    rw [smul_smul, mul_inv_cancel₀ hz0, one_smul, formsTrace_mapExteriorPower,
      ← Nat.cast_smul_eq_nsmul K, inv_smul_smul₀ hc0]

end Compat

end MMP.FourfoldProofs.FractionalLogComplexProof
