module

public import MMP.RingTheory.Presentation.HypersurfacePresentationAlgebra
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Finitely generated complex domains have hypersurface presentations

Let `A` be a domain of finite type over `ℂ`. By Noether normalization `A` is finite over a
polynomial ring `R = ℂ[x₁, …, xₛ] ⊆ A`. The extension of fraction fields is finite and separable,
so it has a primitive element, which can be taken in `A`; its minimal polynomial `f` over `R`
(`R` is integrally closed) is monic irreducible and generates the relations of `y`. Writing
generators of the `R`-module `A` as polynomials in `y` over the fraction field of `R` and clearing
denominators gives a conductor element `c ≠ 0`. Finally `f` is separable over `Frac R`, so
`D = U f + V f'` for some nonzero `D ∈ R`, and `f_x` is separable wherever `D(x) ≠ 0`.

## Main results

* `MMP.SmoothLocusConnected.exists_ne_zero_dvd_algebraMap`: a nonzero element
  integral over a domain `R` divides a nonzero element of `R`.
* `MMP.SmoothLocusConnected.exists_hypersurfacePresentation`: a domain of finite
  type over `ℂ` has a hypersurface presentation with injective `g`, nonzero conductor element and
  generically separable `f`.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §19.1.
-/

@[expose] public section

open Polynomial IntermediateField

namespace MMP.SmoothLocusConnected

/-- A nonzero element `b`, integral over a domain `R`, divides a nonzero element of `R`: the
constant coefficient of its minimal polynomial. -/
theorem exists_ne_zero_dvd_algebraMap {R A : Type*} [CommRing R] [IsDomain R] [CommRing A]
    [IsDomain A] [Algebra R A] {b : A} (hb : IsIntegral R b) (hb0 : b ≠ 0) :
    ∃ r : R, r ≠ 0 ∧ b ∣ algebraMap R A r := by
  set p := minpoly R b
  refine ⟨p.coeff 0, fun h ↦ hb0 ?_, ?_⟩
  · have hX : X ∣ p := X_dvd_iff.mpr h
    have := eq_of_monic_of_associated monic_X (minpoly.monic hb)
      (irreducible_X.associated_of_dvd (minpoly.irreducible hb) hX)
    have h0 := minpoly.aeval R b
    rwa [← this, aeval_X] at h0
  · have h := congrArg (aeval b) (X_mul_divX_add p)
    rw [minpoly.aeval, map_add, map_mul, aeval_X, aeval_C] at h
    exact ⟨-(aeval b p.divX), by linear_combination h⟩

/-- **Generic separability.** If `f ∈ ℂ[x][t]` is separable over the fraction field of `ℂ[x]`,
there is a nonzero `D ∈ ℂ[x]` such that `f_x` is separable wherever `D(x) ≠ 0`. -/
theorem exists_ne_zero_forall_separable {s : ℕ} (K : Type*) [Field K]
    [Algebra (MvPolynomial (Fin s) ℂ) K] [IsFractionRing (MvPolynomial (Fin s) ℂ) K]
    {f : (MvPolynomial (Fin s) ℂ)[X]} (hf : (f.map (algebraMap _ K)).Separable) :
    ∃ D : MvPolynomial (Fin s) ℂ, D ≠ 0 ∧
      ∀ x, MvPolynomial.eval x D ≠ 0 → (f.map (MvPolynomial.eval x)).Separable := by
  set R := MvPolynomial (Fin s) ℂ
  obtain ⟨u, v, huv⟩ := hf
  obtain ⟨b₁, hb₁, hu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) u
  obtain ⟨b₂, hb₂, hv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) v
  set u' := IsLocalization.integerNormalization (nonZeroDivisors R) u
  set v' := IsLocalization.integerNormalization (nonZeroDivisors R) v
  have hinj : Function.Injective (Polynomial.map (algebraMap R K)) :=
    map_injective _ (IsFractionRing.injective R K)
  have key : C b₂ * u' * f + C b₁ * v' * derivative f = C (b₁ * b₂) := by
    apply hinj
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hu, hv, ← derivative_map]
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [Polynomial.algebraMap_apply, map_mul]
    linear_combination (C (algebraMap R K b₁) * C (algebraMap R K b₂)) * huv
  refine ⟨b₁ * b₂, mul_ne_zero (nonZeroDivisors.ne_zero hb₁) (nonZeroDivisors.ne_zero hb₂),
    fun x hx ↦ ?_⟩
  have h := congrArg (Polynomial.map (MvPolynomial.eval x)) key
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map] at h
  refine ⟨C (MvPolynomial.eval x (b₁ * b₂))⁻¹ * C (MvPolynomial.eval x b₂) *
      u'.map (MvPolynomial.eval x),
    C (MvPolynomial.eval x (b₁ * b₂))⁻¹ * C (MvPolynomial.eval x b₁) *
      v'.map (MvPolynomial.eval x), ?_⟩
  have : C (MvPolynomial.eval x (b₁ * b₂))⁻¹ * C (MvPolynomial.eval x (b₁ * b₂)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hx, C_1]
  rw [← this, ← h]
  ring

attribute [local instance] FractionRing.liftAlgebra in
/-- **Hypersurface presentations exist.** A domain `A` of finite type over `ℂ` has a hypersurface
presentation with injective coordinate map, nonzero conductor element, such that every nonzero
`a ∈ A` divides a nonzero element of `ℂ[x]`, and a nonzero `D ∈ ℂ[x]` such that `f_x` is
separable wherever `D(x) ≠ 0`. -/
theorem exists_hypersurfacePresentation (A : Type*) [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] :
    ∃ (s : ℕ) (P : HypersurfacePresentation A s), Function.Injective P.g ∧ P.c ≠ 0 ∧
      (∀ a : A, a ≠ 0 → ∃ r, r ≠ 0 ∧ a ∣ P.g r) ∧
      ∃ D : MvPolynomial (Fin s) ℂ, D ≠ 0 ∧
        ∀ x, MvPolynomial.eval x D ≠ 0 → (P.f.map (MvPolynomial.eval x)).Separable := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  set R := MvPolynomial (Fin s) ℂ
  letI : Algebra R A := g.toRingHom.toAlgebra
  haveI : Module.Finite R A := hfin
  haveI : Module.IsTorsionFree R A := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  haveI : Algebra.IsIntegral R A := inferInstance
  set K := FractionRing R
  set L := FractionRing A
  haveI : IsScalarTower R A L := inferInstance
  haveI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  haveI : FiniteDimensional K L := inferInstance
  haveI : Algebra.IsSeparable K L := inferInstance
  have hAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K L
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A α
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨r, hr0, b', hbb'⟩ := exists_ne_zero_dvd_algebraMap (Algebra.IsIntegral.isIntegral (R := R) b) hb0
  set y := a * b'
  have hyα : algebraMap A L y = algebraMap K L (algebraMap R K r) * α := by
    have hr : algebraMap K L (algebraMap R K r) = algebraMap A L b * algebraMap A L b' := by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A L, hbb', map_mul]
    have : algebraMap A L b ≠ 0 := (map_ne_zero_iff _ hAL).mpr hb0
    rw [hr, ← hab, show y = a * b' from rfl, map_mul, eq_comm, mul_comm, div_mul_eq_mul_div,
      div_eq_iff this]
    ring
  have hrK : algebraMap R K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr0
  have hyint : IsIntegral R y := Algebra.IsIntegral.isIntegral (R := R) y
  have hy'int : IsIntegral R (algebraMap A L y) := hyint.map (IsScalarTower.toAlgHom R A L)
  -- `y` is a primitive element
  have hprim : K⟮algebraMap A L y⟯ = ⊤ := by
    refine eq_top_iff.mpr (hα ▸ IntermediateField.adjoin_simple_le_iff.mpr ?_)
    have hmem : algebraMap A L y ∈ K⟮algebraMap A L y⟯ := IntermediateField.mem_adjoin_simple_self _ _
    have : α = (algebraMap K L (algebraMap R K r))⁻¹ * algebraMap A L y := by
      rw [hyα, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hrK),
        one_mul]
    rw [this]
    exact mul_mem (inv_mem (IntermediateField.algebraMap_mem _ _)) hmem
  set f := minpoly R y
  have hfmon : f.Monic := minpoly.monic hyint
  have hfirr : Irreducible f := minpoly.irreducible hyint
  have hev : ∀ Q : R[X], Q.eval₂ g.toRingHom y = aeval y Q := fun Q ↦ rfl
  -- the conductor
  have hcond : ∃ c : R, c ≠ 0 ∧ ∀ a' : A, ∃ Q : R[X], Q.eval₂ g.toRingHom y = g c * a' := by
    obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := R) (M := A)
    have hgen : ∀ e : A, ∃ Q : R[X], ∃ d : R, d ≠ 0 ∧ aeval y Q = g d * e := by
      intro e
      have he : algebraMap A L e ∈ K⟮algebraMap A L y⟯.toSubalgebra := by rw [hprim]; trivial
      rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic _)] at he
      have he2 : algebraMap A L e ∈ (aeval (R := K) (algebraMap A L y)).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact he
      obtain ⟨p, hp⟩ := he2
      obtain ⟨d, hd, hpd⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) p
      refine ⟨IsLocalization.integerNormalization (nonZeroDivisors R) p, d,
        nonZeroDivisors.ne_zero hd, hAL ?_⟩
      have hp' : aeval (algebraMap A L y) p = algebraMap A L e := hp
      have h1 : aeval (algebraMap A L y) (IsLocalization.integerNormalization (nonZeroDivisors R) p) =
          aeval (algebraMap A L y) ((IsLocalization.integerNormalization (nonZeroDivisors R) p).map
            (algebraMap R K)) := by rw [aeval_map_algebraMap]
      rw [hpd, Algebra.smul_def, Polynomial.algebraMap_apply, map_mul (aeval (algebraMap A L y)),
        aeval_C, hp'] at h1
      rw [← aeval_algebraMap_apply, h1, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R A L]
      rfl
    choose Q d hd hQ using hgen
    classical
    refine ⟨∏ e ∈ S, d e, Finset.prod_ne_zero_iff.mpr fun e _ ↦ hd e, fun a' ↦ ?_⟩
    have ha' : a' ∈ Submodule.span R (S : Set A) := hS ▸ Submodule.mem_top
    induction ha' using Submodule.span_induction with
    | mem e he =>
      refine ⟨C (∏ e' ∈ S.erase e, d e') * Q e, ?_⟩
      rw [hev, map_mul, aeval_C, hQ, ← Finset.mul_prod_erase S d he, map_mul]
      change g (∏ e' ∈ S.erase e, d e') * (g (d e) * e) = _
      ring
    | zero => exact ⟨0, by simp⟩
    | add u w _ _ hu hw =>
      obtain ⟨Qu, hQu⟩ := hu
      obtain ⟨Qw, hQw⟩ := hw
      exact ⟨Qu + Qw, by rw [eval₂_add, hQu, hQw, mul_add]⟩
    | smul t u _ hu =>
      obtain ⟨Qu, hQu⟩ := hu
      refine ⟨C t * Qu, ?_⟩
      rw [eval₂_mul, eval₂_C, hQu, Algebra.smul_def]
      change g t * (g _ * u) = g _ * (g t * u)
      ring
  obtain ⟨c, hc0, hc⟩ := hcond
  -- separability
  have hsepK : (f.map (algebraMap R K)).Separable := by
    have hmin : minpoly K (algebraMap A L y) = f.map (algebraMap R K) := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hy'int]
      congr 1
      exact minpoly.algHom_eq (IsScalarTower.toAlgHom R A L) hAL y
    rw [← hmin]
    exact Algebra.IsSeparable.isSeparable K _
  obtain ⟨D, hD0, hD⟩ := exists_ne_zero_forall_separable K hsepK
  refine ⟨s, ⟨g, y, f, c, hfmon, hfirr, minpoly.aeval R y,
    fun Q hQ ↦ minpoly.isIntegrallyClosed_dvd hyint hQ, hc⟩, hinj, hc0,
    fun a' ha' ↦ exists_ne_zero_dvd_algebraMap (Algebra.IsIntegral.isIntegral (R := R) a') ha',
    D, hD0, hD⟩

end MMP.SmoothLocusConnected
