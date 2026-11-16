module

public import MMP.RingTheory.Kaehler.WedgeSpan
public import MMP.RingTheory.Kaehler.FormsTraceDVR
public import MMP.AlgebraicGeometry.DeRham.RationalForms.Basic

/-!
# Adapted bases of the rational forms at a prime divisor

Let `A` be a local `k`-algebra with maximal ideal `(t)`, fraction field `K`, and `dt, dx₁, …, dxₙ`
a basis of `Ω_{A/k}`. Its image in `Ω_{K/k} = K ⊗_A Ω_{A/k}` is a `K`-basis, the *regular adapted
basis*, and rescaling its first vector by `t⁻¹` gives the *logarithmic adapted basis*
`t⁻¹ dt, dx₁, …, dxₙ`. For a local homomorphism `A → R` of local `k`-algebras with `𝔪_R = (s)`,
`t = u sᵉ` and separable residue extension, and `L ⊇ K` the fraction field of `R`:

* the `p`-forms of `L` in the wedge lattice of the logarithmic forms `s⁻¹ ds, dy₁, …, dyₙ` of `R`
  have their coordinates in the pulled-back logarithmic adapted basis in `R`;
* for the `p`-forms in the wedge lattice of the regular forms `ds, dy₁, …, dyₙ` of `R`, `t` times
  their coordinates in the pulled-back regular adapted basis lie in the maximal ideal of `R`.

## Main definitions

* `MMP.FourfoldProofs.FractionalLogComplexProof.regBasis`,
  `MMP.FourfoldProofs.FractionalLogComplexProof.logBasis`: the adapted bases of `Ω_{K/k}`.

## Main results

* `MMP.FourfoldProofs.FractionalLogComplexProof.repr_logBasis_mem_range`: the logarithmic case.
* `MMP.FourfoldProofs.FractionalLogComplexProof.exists_mem_maximalIdeal_mul_repr_regBasis`: the
  regular case.
-/

@[expose] public section

open KaehlerDifferential IsLocalRing

namespace MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section AdaptedBases

variable (k : Type u) [Field k] {A K : Type u} [CommRing A] [Field K] [Algebra k A] [Algebra k K]
  [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]

/-- For the fraction field `K` of `A`, the map `Ω_{A/k} → Ω_{K/k}` exhibits `Ω_{K/k}` as the base
change `K ⊗_A Ω_{A/k}`. -/
theorem isBaseChange_kaehler_fractionRing :
    IsBaseChange K (KaehlerDifferential.map k k A K) :=
  have : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors A)
  KaehlerDifferential.isBaseChange_of_formallyEtale k A K

/-- The image in `Ω_{K/k}` of a basis of `Ω_{A/k}`, for the fraction field `K` of `A`. -/
noncomputable def regBasis {n : ℕ} (bA : Module.Basis (Fin n) A Ω[A⁄k]) :
    Module.Basis (Fin n) K Ω[K⁄k] :=
  IsBaseChange.basis bA (isBaseChange_kaehler_fractionRing k)

/-- The `i`-th vector of `regBasis k bA` is the image of `bA i` in `Ω_{K/k}`. -/
theorem regBasis_apply {n : ℕ} (bA : Module.Basis (Fin n) A Ω[A⁄k]) (i : Fin n) :
    regBasis k (K := K) bA i = KaehlerDifferential.map k k A K (bA i) :=
  IsBaseChange.basis_apply _ _ _

/-- The logarithmic adapted basis `t⁻¹ dt, dx₁, …, dxₙ` of `Ω_{K/k}`, from a basis
`dt, dx₁, …, dxₙ` of `Ω_{A/k}` and `t ≠ 0` in `K`. -/
noncomputable def logBasis {n : ℕ} (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k]) {t : A}
    (ht : algebraMap A K t ≠ 0) : Module.Basis (Fin (n + 1)) K Ω[K⁄k] :=
  (regBasis k bA).unitsSMul fun i => if i = 0 then (Units.mk0 _ ht)⁻¹ else 1

/-- The first vector of `logBasis k bA ht` is `t⁻¹` times the image of `bA 0` in `Ω_{K/k}`. -/
theorem logBasis_zero {n : ℕ} (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k]) {t : A}
    (ht : algebraMap A K t ≠ 0) :
    logBasis k bA ht 0 = (algebraMap A K t)⁻¹ • KaehlerDifferential.map k k A K (bA 0) := by
  simp [logBasis, Module.Basis.unitsSMul_apply, regBasis_apply, Units.smul_def]

/-- The vectors of `logBasis k bA ht` after the first are the images of those of `bA` in
`Ω_{K/k}`. -/
theorem logBasis_succ {n : ℕ} (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k]) {t : A}
    (ht : algebraMap A K t ≠ 0) (i : Fin n) :
    logBasis k bA ht i.succ = KaehlerDifferential.map k k A K (bA i.succ) := by
  simp [logBasis, Module.Basis.unitsSMul_apply, regBasis_apply, Fin.succ_ne_zero]

end AdaptedBases

section Places

variable (k : Type u) [Field k] {A R K L : Type u} [CommRing A] [CommRing R] [Field K] [Field L]
  [Algebra k A] [Algebra k R] [Algebra k K] [Algebra k L]
  [Algebra A R] [Algebra A K] [Algebra A L] [Algebra R L] [Algebra K L]
  [IsScalarTower k A R] [IsScalarTower k R L] [IsScalarTower A R L] [IsScalarTower k A K]
  [IsScalarTower k K L] [IsScalarTower A K L] [IsScalarTower k A L]
  [IsFractionRing A K] [Algebra.IsSeparable K L]

/-- The pulled-back regular adapted basis is `dt, dx₁, …, dxₙ` in `Ω_{L/k}`. -/
theorem pullbackBasis_regBasis_apply {n : ℕ} (bA : Module.Basis (Fin n) A Ω[A⁄k]) (i : Fin n) :
    pullbackBasis (L := L) (regBasis k (K := K) bA) i = KaehlerDifferential.map k k A L (bA i) := by
  rw [pullbackBasis_apply, regBasis_apply, map_map_eq]

/-- The pulled-back logarithmic adapted basis is `t⁻¹ dt, dx₁, …, dxₙ` in `Ω_{L/k}`. -/
theorem pullbackBasis_logBasis {n : ℕ} (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k]) {t : A}
    (ht : algebraMap A K t ≠ 0) :
    ⇑(pullbackBasis (L := L) (logBasis k bA ht)) = Fin.cons
      ((algebraMap A L t)⁻¹ • KaehlerDifferential.map k k A L (bA 0))
      fun i => KaehlerDifferential.map k k A L (bA i.succ) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [pullbackBasis_apply, logBasis_zero, map_smul, map_map_eq, Fin.cons_zero,
      ← algebraMap_smul L ((algebraMap A K t)⁻¹), map_inv₀, ← IsScalarTower.algebraMap_apply]
  · rw [pullbackBasis_apply, logBasis_succ, map_map_eq, Fin.cons_succ]

variable [IsLocalRing A] [IsLocalRing R] [IsLocalHom (algebraMap A R)]

/-- **Logarithmic forms at a place.** The `p`-forms of `L` in the wedge lattice of the
logarithmic forms `s⁻¹ ds, dy₁, …, dyₙ` of `R` have their coordinates in the pulled-back
logarithmic adapted basis `t⁻¹ dt, dx₁, …, dxₙ` in `R`. -/
theorem repr_logBasis_mem_range [CharZero k]
    [Algebra.IsSeparable (ResidueField A) (ResidueField R)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i))
    {s : R} (hmR : maximalIdeal R = Ideal.span {s}) (y : Fin n → R)
    (bR : Module.Basis (Fin (n + 1)) R Ω[R⁄k])
    (hbR : ∀ i, bR i = D k R ((Fin.cons s y : Fin (n + 1) → R) i))
    {u : R} (hu : IsUnit u) {e : ℕ} (he : e ≠ 0) (hts : algebraMap A R t = u * s ^ e)
    (ht : algebraMap A K t ≠ 0) (hs : algebraMap R L s ≠ 0) {p : ℕ} {ω : ⋀[L]^p (Ω[L⁄k])}
    (hω : ω ∈ wedgeSpan R (Submodule.span R (Set.range (Fin.cons
      ((algebraMap R L s)⁻¹ • D k L (algebraMap R L s))
      fun j => D k L (algebraMap R L (y j)) : Fin (n + 1) → Ω[L⁄k]))) p)
    (S : Set.powersetCard (Fin (n + 1)) p) :
    ((pullbackBasis (L := L) (logBasis k bA ht)).exteriorPower p).repr ω S ∈
      (algebraMap R L).range := by
  have htL : algebraMap A L t ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact (map_ne_zero _).2 ht
  have hspan := span_log_eq k hmA x bA hbA hmR y bR hbR hu he hts (L := L)
    (inv_mul_cancel₀ hs) (inv_mul_cancel₀ htL)
  have hb : (Fin.cons ((algebraMap A L t)⁻¹ • D k L (algebraMap A L t))
      fun i => D k L (algebraMap A L (x i)) : Fin (n + 1) → Ω[L⁄k]) =
      ⇑(pullbackBasis (L := L) (logBasis k bA ht)) := by
    rw [pullbackBasis_logBasis, hbA, Fin.cons_zero, KaehlerDifferential.map_D]
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    simp only [Fin.cons_succ, hbA, KaehlerDifferential.map_D]
  rw [hspan, hb] at hω
  exact repr_mem_range_of_mem_wedgeSpan _ hω S

/-- **Regular forms at a place.** For a `p`-form `ω` of `L` in the wedge lattice of the regular
forms `ds, dy₁, …, dyₙ` of `R`, `t` times every coordinate of `ω` in the pulled-back regular
adapted basis `dt, dx₁, …, dxₙ` lies in the maximal ideal of `R`. -/
theorem exists_mem_maximalIdeal_mul_repr_regBasis [CharZero k]
    [Algebra.IsSeparable (ResidueField A) (ResidueField R)]
    {n : ℕ} {t : A} (hmA : maximalIdeal A = Ideal.span {t}) (x : Fin n → A)
    (bA : Module.Basis (Fin (n + 1)) A Ω[A⁄k])
    (hbA : ∀ i, bA i = D k A ((Fin.cons t x : Fin (n + 1) → A) i))
    {s : R} (hmR : maximalIdeal R = Ideal.span {s}) (y : Fin n → R)
    (bR : Module.Basis (Fin (n + 1)) R Ω[R⁄k])
    (hbR : ∀ i, bR i = D k R ((Fin.cons s y : Fin (n + 1) → R) i))
    {u : R} (hu : IsUnit u) {e : ℕ} (he : e ≠ 0) (hts : algebraMap A R t = u * s ^ e)
    (ht : algebraMap A K t ≠ 0) (hs : algebraMap R L s ≠ 0) {p : ℕ} {ω : ⋀[L]^p (Ω[L⁄k])}
    (hω : ω ∈ wedgeSpan R (Submodule.span R (Set.range fun j =>
      D k L (algebraMap R L ((Fin.cons s y : Fin (n + 1) → R) j)))) p)
    (S : Set.powersetCard (Fin (n + 1)) p) :
    ∃ r ∈ maximalIdeal R, algebraMap R L r =
      algebraMap A L t * ((pullbackBasis (L := L) (regBasis k (K := K) bA)).exteriorPower p).repr
        ω S := by
  have htL : algebraMap A L t ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A K L]
    exact (map_ne_zero _).2 ht
  have huL : algebraMap R L u ≠ 0 := fun h0 =>
    (hu.map (algebraMap R L)).ne_zero h0
  rw [span_regular_eq k hmA x bA hbA hmR y bR hbR hu he hts (L := L) (inv_mul_cancel₀ htL)] at hω
  set b := pullbackBasis (L := L) (regBasis k (K := K) bA)
  let ν : Lˣ := Units.mk0 (algebraMap R L (u * s) * (algebraMap A L t)⁻¹)
    (mul_ne_zero (by rw [map_mul]; exact mul_ne_zero huL hs) (inv_ne_zero htL))
  have hb : (Fin.cons ((u * s) • ((algebraMap A L t)⁻¹ • D k L (algebraMap A L t)))
      fun i => D k L (algebraMap A L (x i)) : Fin (n + 1) → Ω[L⁄k]) =
      Fin.cons ((ν : L) • b 0) fun i => b i.succ := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero, b, pullbackBasis_regBasis_apply, hbA, KaehlerDifferential.map_D,
        ν, Units.val_mk0]
      rw [← algebraMap_smul L (u * s), smul_smul]
    · simp only [Fin.cons_succ, b, pullbackBasis_regBasis_apply, hbA, KaehlerDifferential.map_D]
  rw [hb] at hω
  have hsm : s ∈ maximalIdeal R := hmR ▸ Ideal.mem_span_singleton_self s
  have htm : algebraMap A R t ∈ maximalIdeal R :=
    map_nonunit (algebraMap A R) t (hmA ▸ Ideal.mem_span_singleton_self t)
  refine exists_mem_maximalIdeal_mul_repr b ν ⟨algebraMap A R t, htm,
    (IsScalarTower.algebraMap_apply A R L t).symm⟩ ⟨u * s, Ideal.mul_mem_left _ _ hsm, ?_⟩ hω S
  simp only [ν, Units.val_mk0]
  field_simp

end Places

end MMP.FourfoldProofs.FractionalLogComplexProof
