module

public import MMP.AlgebraicGeometry.Vanishing.FractionalLogComplex.AdaptedBases

/-!
# The inputs of the tame trace estimate at a place

Let `A → R` be a local homomorphism of local `k`-algebras with maximal ideals `(t)` and `(s)`,
`t = u sᵉ`, separable residue extension, and fraction fields `K ⊆ L`. Let `ω` be a `p`-form of `L`.

* If `t ω = ρ η` with `ρ ∈ 𝔪_R` and `η` in the wedges of the logarithmic forms
  `s⁻¹ ds, dy₁, …, dyₙ` of `R`, then `t` times every coordinate of `ω` in the pulled-back
  logarithmic adapted basis lies in `𝔪_R`.
* If `ω = ρ η` with `ρ ∈ R` and `η` in the wedges of the regular forms `ds, dy₁, …, dyₙ` of `R`,
  then `t` times every coordinate of `ω` in the pulled-back regular adapted basis lies in `𝔪_R`.

These are the hypotheses, at every point of a cover over a prime divisor, of
`MMP.FourfoldProofs.FractionalLogComplexProof.formsTrace_repr_mem_range_localRing`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_mem_maximalIdeal_mul_repr_logBasis_of_smul`.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_mem_maximalIdeal_mul_repr_regBasis_of_smul`.
-/

@[expose] public section

open KaehlerDifferential IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section Places

variable (k : Type u) [Field k] {A R K L : Type u} [CommRing A] [CommRing R] [Field K] [Field L]
  [Algebra k A] [Algebra k R] [Algebra k K] [Algebra k L]
  [Algebra A R] [Algebra A K] [Algebra A L] [Algebra R L] [Algebra K L]
  [IsScalarTower k A R] [IsScalarTower k R L] [IsScalarTower A R L] [IsScalarTower k A K]
  [IsScalarTower k K L] [IsScalarTower A K L] [IsScalarTower k A L]
  [IsFractionRing A K] [Algebra.IsSeparable K L]
  [IsLocalRing A] [IsLocalRing R] [IsLocalHom (algebraMap A R)]

/-- **The logarithmic input of the tame trace estimate.** If `t • ω = ρ • η` with `ρ ∈ 𝔪_R` and
`η` in the `p`-th wedge span over `R` of the logarithmic forms `s⁻¹ ds, dy₁, …, dyₙ`, then `t` times
every coordinate of `ω` in the pulled-back logarithmic adapted basis lies in the image of `𝔪_R`. -/
theorem exists_mem_maximalIdeal_mul_repr_logBasis_of_smul [CharZero k]
    [Algebra.IsSeparable (ResidueField A) (ResidueField R)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i))
    {s : R} (hmR : maximalIdeal R = Ideal.span {s}) (y : Fin n → R)
    (bR : Module.Basis (Fin (n + 1)) R Ω[R⁄k])
    (hbR : ∀ i, bR i = D k R ((Fin.cons s y : Fin (n + 1) → R) i))
    {u : R} (hu : IsUnit u) {e : ℕ} (he : e ≠ 0) (hts : algebraMap A R t = u * s ^ e)
    (ht : algebraMap A K t ≠ 0) (hs : algebraMap R L s ≠ 0) {p : ℕ} {ω η : ⋀[L]^p (Ω[L⁄k])}
    {ρ : R} (hρ : ρ ∈ maximalIdeal R)
    (hη : η ∈ wedgeSpan R (Submodule.span R (Set.range (Fin.cons
      ((algebraMap R L s)⁻¹ • D k L (algebraMap R L s))
      fun j => D k L (algebraMap R L (y j)) : Fin (n + 1) → Ω[L⁄k]))) p)
    (hω : algebraMap A L t • ω = algebraMap R L ρ • η)
    (S : Set.powersetCard (Fin (n + 1)) p) :
    ∃ r ∈ maximalIdeal R, algebraMap R L r =
      algebraMap A L t *
        ((pullbackBasis (L := L) (logBasis k bA ht)).exteriorPower p).repr ω S := by
  obtain ⟨c, hc⟩ := repr_logBasis_mem_range k hmA x bA hbA hmR y bR hbR hu he hts ht hs hη S
  refine ⟨ρ * c, Ideal.mul_mem_right _ _ hρ, ?_⟩
  have h1 := congrArg (fun w => ((pullbackBasis (L := L) (logBasis k bA ht)).exteriorPower p).repr
    w S) hω
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  rw [map_mul, hc, ← h1]

/-- **The regular input of the tame trace estimate.** If `ω = ρ • η` with `ρ ∈ R` and `η` in the
`p`-th wedge span over `R` of the regular forms `ds, dy₁, …, dyₙ`, then `t` times every coordinate
of `ω` in the pulled-back regular adapted basis lies in the image of `𝔪_R`. -/
theorem exists_mem_maximalIdeal_mul_repr_regBasis_of_smul [CharZero k]
    [Algebra.IsSeparable (ResidueField A) (ResidueField R)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i))
    {s : R} (hmR : maximalIdeal R = Ideal.span {s}) (y : Fin n → R)
    (bR : Module.Basis (Fin (n + 1)) R Ω[R⁄k])
    (hbR : ∀ i, bR i = D k R ((Fin.cons s y : Fin (n + 1) → R) i))
    {u : R} (hu : IsUnit u) {e : ℕ} (he : e ≠ 0) (hts : algebraMap A R t = u * s ^ e)
    (ht : algebraMap A K t ≠ 0) (hs : algebraMap R L s ≠ 0) {p : ℕ} {ω η : ⋀[L]^p (Ω[L⁄k])}
    {ρ : R}
    (hη : η ∈ wedgeSpan R (Submodule.span R (Set.range fun j =>
      D k L (algebraMap R L ((Fin.cons s y : Fin (n + 1) → R) j)))) p)
    (hω : ω = algebraMap R L ρ • η)
    (S : Set.powersetCard (Fin (n + 1)) p) :
    ∃ r ∈ maximalIdeal R, algebraMap R L r =
      algebraMap A L t * ((pullbackBasis (L := L) (regBasis k (K := K) bA)).exteriorPower p).repr
        ω S := by
  obtain ⟨r₀, hr₀, hr₀'⟩ :=
    exists_mem_maximalIdeal_mul_repr_regBasis k hmA x bA hbA hmR y bR hbR hu he hts ht hs hη S
  refine ⟨ρ * r₀, Ideal.mul_mem_left _ _ hr₀, ?_⟩
  rw [hω, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hr₀']
  ring

end Places

end MMP.FourfoldProofs.FractionalLogComplexProof
