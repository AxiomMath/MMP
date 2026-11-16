/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import MMP.AlgebraicGeometry.Singularities.Semismooth.Defs
public import MMP.AlgebraicGeometry.Normalization.Completion
public import MMP.AlgebraicGeometry.Resolution.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FibreRegularity
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.RegularLocalRing.Criteria
public import StacksFrontier.RingTheory.RegularLocalRing.UniqueFactorization

/-!
# Semismooth `n`-folds have smooth normalization

FA 12.2.1(2): a semismooth `n`-fold `X` (every closed point smooth, a double normal crossing
point or a pinch point, `MMP.Flips.IsSemismooth`) has smooth normalization.

## Main definitions

* `MMP.Flips.Normalization.PinchRing`: the ring `B⟦s⟧[T]/(T² - s b²)`, and
  `MMP.Flips.Normalization.pinchMap` its embedding into `B⟦u⟧`, `T ↦ u b`, `s ↦ u²`,
  integral and birational for `b ≠ 0`.
* `MMP.Flips.Normalization.pinchModelEquiv`: the pinch point model
  `k[[x₀, …, x_{m+2}]]/(x₀² - x₁x₂²) ≅ PinchRing x₂` over `B = k[[x₂, …, x_{m+2}]]`.
* `MMP.Flips.Normalization.restrictZero`, `MMP.Flips.Normalization.inclZero`:
  restriction to `x₀ = 0` and its section.

## Main results

* `MMP.Flips.IsSemismooth.isSmoothScheme_normalization`: the normalization of a semismooth
  `n`-fold is smooth.
* `MMP.Flips.Normalization.nonempty_algEquiv_of_isIntegrallyClosed_of_birational`: two
  integrally closed domains, integral and birational over the same domain, are isomorphic
  over it.
* `MMP.Flips.Normalization.prime_X`: each variable is prime in `k[[x₀, …, xₙ]]`.

## Implementation notes

Smoothness is open, and `X^ν` is a Jacobson
space, so it suffices to treat closed points `y` of `X^ν`; their images `x` are closed.

* Over a smooth point `x`, a smooth open neighbourhood `U` of `x` is normal, and the normalization
  is an isomorphism over `U`.
* Over a double normal crossing point or a pinch point, the product of the completions
  `𝒪̂_{X^ν,x'}` over the points `x'` over `x` is the normalization of `𝒪̂_{X,x}`
  (`MMP.Resolution.isReduced_adicCompletion_stalk_and_normalization_completion`). Each factor
  `L = 𝒪̂_{X^ν,y}` is a local normal domain receiving `𝒪̂_{X,x}`, integrally and birationally, with
  no non-zero-divisor in the kernel. For the model `k[[x₀, …, xₙ]]/(x₀x₁)` the kernel is `(x₀)`
  or `(x₁)`, and `L ≅ k[[x₁, …, xₙ]]`. For the model `k[[x₀, …, xₙ]]/(x₀² - x₁x₂²)`, the model is
  the domain `B[[s]][T]/(T² - s b²)` (Weierstrass division, `b = x₂`, `B = k[[x₂, …, xₙ]]`), which
  embeds into `B[[u]]` by `T ↦ u b`, `s ↦ u²`, integrally (`u² = s`) and birationally
  (`u = T/b`); two normal domains integral and birational over the same domain are isomorphic,
  so `L ≅ B[[u]] ≅ k[[u, x₂, …, xₙ]]`. In all cases `L` is a regular local ring whose residue
  field is spanned by `k`, so `𝒪_{X^ν,y}` is regular with residue field `k`, and `X^ν` is smooth
  over `k` at `y` (`AlgebraicGeometry.smoothAt_iff_isRegularLocalRing_stalk`; no perfectness of
  `k` is needed, the residue field being `k` itself).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 12.2.1
-/

@[expose] public noncomputable section

universe u

namespace MMP.Flips

open PowerSeries

namespace Normalization

private theorem isFractionRing_fractionRing_of_birational (R L : Type*) [CommRing R] [IsDomain R]
    [CommRing L] [IsDomain L] [Algebra R L] [FaithfulSMul R L]
    (hL : ∀ l : L, ∃ r s : R, s ≠ 0 ∧ algebraMap R L s * l = algebraMap R L r) :
    IsFractionRing R (FractionRing L) := by
  have hinj : Function.Injective (algebraMap R (FractionRing L)) := by
    rw [IsScalarTower.algebraMap_eq R L (FractionRing L)]
    exact (IsFractionRing.injective L _).comp (FaithfulSMul.algebraMap_injective R L)
  have : FaithfulSMul R (FractionRing L) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine IsFractionRing.of_field R (FractionRing L) fun z => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := L) z
  obtain ⟨r1, s1, hs1, h1⟩ := hL a
  obtain ⟨r2, s2, hs2, h2⟩ := hL b
  have hb' : algebraMap L (FractionRing L) b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective L _)).2 (nonZeroDivisors.ne_zero hb)
  have hs1' : algebraMap R (FractionRing L) s1 ≠ 0 := (map_ne_zero_iff _ hinj).2 hs1
  have hs2' : algebraMap R (FractionRing L) s2 ≠ 0 := (map_ne_zero_iff _ hinj).2 hs2
  have e1 := congrArg (algebraMap L (FractionRing L)) h1
  have e2 := congrArg (algebraMap L (FractionRing L)) h2
  simp only [map_mul, ← IsScalarTower.algebraMap_apply] at e1 e2
  have hr2 : algebraMap R (FractionRing L) r2 ≠ 0 := by
    rw [← e2]; exact mul_ne_zero hs2' hb'
  refine ⟨r1 * s2, s1 * r2, ?_⟩
  rw [map_mul, map_mul, ← e1, ← e2]
  field_simp

/-- Two integrally closed domains, integral over a domain `R` and birational over it, are
isomorphic as `R`-algebras. -/
theorem nonempty_algEquiv_of_isIntegrallyClosed_of_birational (R L C : Type*) [CommRing R]
    [IsDomain R] [CommRing L] [IsDomain L] [IsIntegrallyClosed L] [CommRing C] [IsDomain C]
    [IsIntegrallyClosed C] [Algebra R L] [Algebra R C] [FaithfulSMul R L] [FaithfulSMul R C]
    [Algebra.IsIntegral R L] [Algebra.IsIntegral R C]
    (hL : ∀ l : L, ∃ r s : R, s ≠ 0 ∧ algebraMap R L s * l = algebraMap R L r)
    (hC : ∀ c : C, ∃ r s : R, s ≠ 0 ∧ algebraMap R C s * c = algebraMap R C r) :
    Nonempty (L ≃ₐ[R] C) := by
  have := isFractionRing_fractionRing_of_birational R L hL
  have := isFractionRing_fractionRing_of_birational R C hC
  have : IsIntegralClosure L R (FractionRing L) :=
    IsIntegralClosure.of_isIntegrallyClosed L R (FractionRing L)
  have hCc : IsIntegralClosure C R (FractionRing C) :=
    IsIntegralClosure.of_isIntegrallyClosed C R (FractionRing C)
  let e : FractionRing L ≃ₐ[R] FractionRing C :=
    IsLocalization.algEquiv (nonZeroDivisors R) _ _
  let : Algebra C (FractionRing L) :=
    (e.symm.toRingHom.comp (algebraMap C (FractionRing C))).toAlgebra
  have hcomp : ∀ c : C, algebraMap C (FractionRing L) c = e.symm (algebraMap C _ c) :=
    fun _ => rfl
  have : IsScalarTower R C (FractionRing L) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    rw [hcomp, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  have : IsIntegralClosure C R (FractionRing L) := by
    refine ⟨?_, fun {x} => ?_⟩
    · intro a b hab
      rw [hcomp, hcomp] at hab
      exact hCc.algebraMap_injective (e.symm.injective hab)
    · constructor
      · intro hx
        obtain ⟨c, hc⟩ := hCc.isIntegral_iff.mp (hx.map e)
        exact ⟨c, by rw [hcomp, hc, AlgEquiv.symm_apply_apply]⟩
      · rintro ⟨c, rfl⟩
        rw [hcomp]
        exact (hCc.isIntegral_iff.mpr ⟨c, rfl⟩).map e.symm
  exact ⟨IsIntegralClosure.equiv R L (FractionRing L) C⟩

section Pinch

variable {B : Type*} [CommRing B]

private theorem expand_two_add_X_mul_expand_two (f : B⟦X⟧) :
    expand 2 two_ne_zero (mk fun j => coeff (2 * j) f) +
      PowerSeries.X * expand 2 two_ne_zero (mk fun j => coeff (2 * j + 1) f) = f := by
  ext n
  rcases Nat.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [map_add, show j + j = 2 * j by ring, coeff_expand_mul]
    rcases j with _ | j
    · simp
    · rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, coeff_succ_X_mul,
        coeff_expand_of_not_dvd _ _ _ (by omega)]
      simp [show 2 * (j + 1) = (2 * j + 1) + 1 by ring]
  · rw [map_add, coeff_succ_X_mul, coeff_expand_mul, coeff_expand_of_not_dvd _ _ _ (by omega)]
    simp

private theorem eq_zero_of_expand_two_add_X_mul_C_mul_expand_two [IsDomain B] {b : B} (hb : b ≠ 0)
    {f g : B⟦X⟧} (h : expand 2 two_ne_zero f + PowerSeries.X * C b * expand 2 two_ne_zero g = 0) :
    f = 0 ∧ g = 0 := by
  constructor
  · ext j
    have := congrArg (coeff (2 * j)) h
    rcases j with _ | j
    · simpa using this
    · rw [map_add, coeff_expand_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, mul_assoc,
        coeff_succ_X_mul, coeff_C_mul, coeff_expand_of_not_dvd _ _ _ (by omega)] at this
      simpa using this
  · ext j
    have := congrArg (coeff (2 * j + 1)) h
    rw [map_add, mul_assoc, coeff_succ_X_mul, coeff_C_mul, coeff_expand_mul,
      coeff_expand_of_not_dvd _ _ _ (by omega)] at this
    simpa [hb] using this

variable (b : B)

/-- The polynomial `T² - s b²` over `B⟦s⟧`. -/
abbrev pinchPoly : Polynomial B⟦X⟧ :=
  Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X * C (b ^ 2))

/-- The ring `B⟦s⟧[T]/(T² - s b²)`. -/
abbrev PinchRing : Type _ := Polynomial B⟦X⟧ ⧸ Ideal.span {pinchPoly b}

/-- The polynomial `T² - s b²` is monic. -/
theorem pinchPoly_monic : (pinchPoly b).Monic :=
  Polynomial.monic_X_pow_sub_C _ two_ne_zero

/-- Over a nontrivial ring, `T² - s b²` has degree `2`. -/
theorem pinchPoly_natDegree [Nontrivial B] : (pinchPoly b).natDegree = 2 :=
  Polynomial.natDegree_X_pow_sub_C

/-- `T ↦ u b`, `s ↦ u²`. -/
def pinchMap₀ : Polynomial B⟦X⟧ →+* B⟦X⟧ :=
  Polynomial.eval₂RingHom (expand 2 two_ne_zero : B⟦X⟧ →ₐ[B] B⟦X⟧).toRingHom (PowerSeries.X * C b)

/-- The map `T ↦ u b`, `s ↦ u²` sends `T² - s b²` to `0`. -/
theorem pinchMap₀_pinchPoly : pinchMap₀ b (pinchPoly b) = 0 := by
  rw [pinchMap₀, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_C]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_pow, expand_X, expand_C]
  ring

/-- The map `B⟦s⟧[T]/(T² - s b²) → B⟦u⟧`, `T ↦ u b`, `s ↦ u²`. -/
def pinchMap : PinchRing b →+* B⟦X⟧ :=
  Ideal.Quotient.lift _ (pinchMap₀ b) fun p hp => by
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hp
    rw [map_mul, pinchMap₀_pinchPoly, mul_zero]

/-- `pinchMap` on the class of a polynomial `p` is `pinchMap₀ p`. -/
theorem pinchMap_mk (p : Polynomial B⟦X⟧) :
    pinchMap b (Ideal.Quotient.mk _ p) = pinchMap₀ b p := rfl

private theorem exists_eq_mk_C_add_mk_C_mul_mk_X [Nontrivial B] (r : PinchRing b) :
    ∃ a₀ a₁ : B⟦X⟧, r = Ideal.Quotient.mk _ (Polynomial.C a₀) +
      Ideal.Quotient.mk _ (Polynomial.C a₁) * Ideal.Quotient.mk _ Polynomial.X := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hdeg : (p %ₘ pinchPoly b).natDegree ≤ 1 := by
    have := Polynomial.natDegree_modByMonic_lt p (pinchPoly_monic b)
      fun h => by simpa [h] using pinchPoly_natDegree b
    rw [pinchPoly_natDegree] at this
    omega
  refine ⟨(p %ₘ pinchPoly b).coeff 0, (p %ₘ pinchPoly b).coeff 1, ?_⟩
  rw [← map_mul, ← map_add, Ideal.Quotient.eq.mpr]
  rw [Ideal.mem_span_singleton']
  refine ⟨p /ₘ pinchPoly b, ?_⟩
  have hr : Polynomial.C ((p %ₘ pinchPoly b).coeff 0) +
      Polynomial.C ((p %ₘ pinchPoly b).coeff 1) * Polynomial.X = p %ₘ pinchPoly b := by
    conv_rhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
    ring
  rw [hr, Polynomial.modByMonic_eq_sub_mul_div p (pinchPoly b)]
  ring

/-- For `b ≠ 0` in a domain `B`, the map `B⟦s⟧[T]/(T² - s b²) → B⟦u⟧` is injective. -/
theorem pinchMap_injective [IsDomain B] (hb : b ≠ 0) : Function.Injective (pinchMap b) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  obtain ⟨a₀, a₁, rfl⟩ := exists_eq_mk_C_add_mk_C_mul_mk_X b r
  simp only [map_add, map_mul, pinchMap_mk, pinchMap₀, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hr
  obtain ⟨rfl, rfl⟩ := eq_zero_of_expand_two_add_X_mul_C_mul_expand_two hb
    (f := a₀) (g := a₁) (by rw [← hr]; ring)
  simp only [map_zero, zero_add]
  exact zero_mul (M₀ := PinchRing b) _

/-- `pinchMap` sends a constant `a(s)` to `a(u²)`. -/
theorem pinchMap_mk_C (a : B⟦X⟧) :
    pinchMap b (Ideal.Quotient.mk _ (Polynomial.C a)) = expand 2 two_ne_zero a := by
  simp [pinchMap_mk, pinchMap₀]

/-- `pinchMap` sends `T` to `u b`. -/
theorem pinchMap_mk_X :
    pinchMap b (Ideal.Quotient.mk _ Polynomial.X) = PowerSeries.X * C b := by
  simp [pinchMap_mk, pinchMap₀]

/-- Every element of `B⟦u⟧` is integral over `B⟦s⟧[T]/(T² - s b²)` via `pinchMap`. -/
theorem pinchMap_isIntegralElem (f : B⟦X⟧) :
    RingHom.IsIntegralElem (R := PinchRing b) (A := B⟦X⟧) (pinchMap b) f := by
  let := RingHom.toAlgebra (R := PinchRing b) (S := B⟦X⟧) (pinchMap b)
  change IsIntegral (PinchRing b) f
  have hE : ∀ a : B⟦X⟧, expand 2 two_ne_zero a =
      algebraMap (PinchRing b) B⟦X⟧ (Ideal.Quotient.mk _ (Polynomial.C a)) := fun a => by
    rw [RingHom.algebraMap_toAlgebra]; exact (pinchMap_mk_C b a).symm
  have hX : IsIntegral (PinchRing b) (PowerSeries.X : B⟦X⟧) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (Ideal.Quotient.mk _ (Polynomial.C PowerSeries.X)),
      Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, ← hE, expand_X,
      sub_self]
  rw [← expand_two_add_X_mul_expand_two f, hE, hE]
  exact isIntegral_algebraMap.add (hX.mul isIntegral_algebraMap)

/-- For `b ≠ 0`, every `f ∈ B⟦u⟧` is a fraction `pinchMap r / pinchMap s` with
`pinchMap s ≠ 0`. -/
theorem pinchMap_birational {b : B} (hb : b ≠ 0) (f : B⟦X⟧) : ∃ r s : PinchRing b,
    pinchMap b s ≠ 0 ∧ pinchMap b s * f = pinchMap b r := by
  refine ⟨Ideal.Quotient.mk _ (Polynomial.C (C b * mk fun j => coeff (2 * j) f)) +
    Ideal.Quotient.mk _ Polynomial.X *
      Ideal.Quotient.mk _ (Polynomial.C (mk fun j => coeff (2 * j + 1) f)),
    Ideal.Quotient.mk _ (Polynomial.C (C b)), ?_, ?_⟩
  · rw [pinchMap_mk_C, expand_C]
    exact fun h => hb (C_injective (by simpa using h))
  · conv_lhs => rw [← expand_two_add_X_mul_expand_two f]
    simp only [map_add, map_mul, pinchMap_mk_C, pinchMap_mk_X, expand_C]
    ring

end Pinch

section PinchModel

variable (k : Type*) [Field k] (m : ℕ)

/-- Change of coefficients along an algebra isomorphism, on power series. -/
def powerSeriesMapAlgEquiv {R A A' : Type*} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra R A'] (e : A ≃ₐ[R] A') : A⟦X⟧ ≃ₐ[R] A'⟦X⟧ :=
  AlgEquiv.ofAlgHom (mapAlgHom e.toAlgHom) (mapAlgHom e.symm.toAlgHom)
    (by ext f n; simp [mapAlgHom_apply]) (by ext f n; simp [mapAlgHom_apply])

/-- `k[[x₀, …, x_{m+2}]] ≅ (k[[x₂, …, x_{m+2}]][[x₁]])[[x₀]]`. -/
def pinchTowerEquiv :
    MvPowerSeries (Fin (m + 3)) k ≃ₐ[k] (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧ :=
  (MvPowerSeries.finSuccEquiv k (m + 2)).trans
    (powerSeriesMapAlgEquiv (MvPowerSeries.finSuccEquiv k (m + 1)))

/-- `pinchTowerEquiv` sends `x₀² - x₁x₂²` to the polynomial `T² - s b²` with `b = x₂`. -/
theorem pinchTowerEquiv_h :
    pinchTowerEquiv k m (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2) =
      ((pinchPoly (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k) :
        Polynomial (MvPowerSeries (Fin (m + 1)) k)⟦X⟧) :
          (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧) := by
  have e0 : MvPowerSeries.finSuccEquiv k (m + 2) (MvPowerSeries.X 0) = PowerSeries.X :=
    MvPowerSeries.finSuccEquiv_X_zero
  have e1 : MvPowerSeries.finSuccEquiv k (m + 2) (MvPowerSeries.X 1) =
      C (MvPowerSeries.X 0) := MvPowerSeries.finSuccEquiv_X_succ (j := 0)
  have e2 : MvPowerSeries.finSuccEquiv k (m + 2) (MvPowerSeries.X 2) =
      C (MvPowerSeries.X 1) := MvPowerSeries.finSuccEquiv_X_succ (j := 1)
  have f0 : MvPowerSeries.finSuccEquiv k (m + 1) (MvPowerSeries.X 0) = PowerSeries.X :=
    MvPowerSeries.finSuccEquiv_X_zero
  have f1 : MvPowerSeries.finSuccEquiv k (m + 1) (MvPowerSeries.X 1) =
      C (MvPowerSeries.X 0) := MvPowerSeries.finSuccEquiv_X_succ (j := 0)
  simp only [pinchTowerEquiv, AlgEquiv.trans_apply, map_sub, map_pow, map_mul, e0, e1, e2]
  simp only [powerSeriesMapAlgEquiv, AlgEquiv.ofAlgHom_apply, mapAlgHom_apply, map_X, map_C,
    RingHom.coe_coe, pinchPoly, Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X,
    Polynomial.coe_C]
  erw [f0, f1]
  rw [map_mul, map_pow, map_pow]

/-- The polynomial `T² - s b²` is distinguished at the ideal `(s)` of `B⟦s⟧`. -/
theorem pinchPoly_isDistinguishedAt {B : Type*} [CommRing B] [Nontrivial B] (b : B) :
    (pinchPoly b).IsDistinguishedAt (Ideal.span {PowerSeries.X}) := by
  refine ⟨⟨fun {n} hn => ?_⟩, pinchPoly_monic b⟩
  rw [pinchPoly_natDegree] at hn
  interval_cases n
  · simp only [pinchPoly, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_zero]
    simp only [OfNat.zero_ne_ofNat, ite_false, zero_sub, neg_mem_iff]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · simp only [pinchPoly, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
    simp

/-- The Weierstrass isomorphism `A⟦X⟧/(g) ≅ A[X]/(g)` for a distinguished polynomial `g`, as a
ring isomorphism (stated over an arbitrary `A`, where no algebra-instance diamond arises). -/
def distinguishedQuotientEquiv {A : Type*} [CommRing A] {g : Polynomial A}
    {I : Ideal A} (H : g.IsDistinguishedAt I) [IsAdicComplete I A] :
    (A⟦X⟧ ⧸ Ideal.span {(g : A⟦X⟧)}) ≃+* (Polynomial A ⧸ Ideal.span {g}) :=
  H.algEquivQuotient.symm.toRingEquiv

/-- `distinguishedQuotientEquiv` sends the class of a polynomial `p` in `A⟦X⟧/(g)` to its class
in `A[X]/(g)`. -/
theorem distinguishedQuotientEquiv_mk {A : Type*} [CommRing A] {g : Polynomial A}
    {I : Ideal A} (H : g.IsDistinguishedAt I) [IsAdicComplete I A] (p : Polynomial A) :
    distinguishedQuotientEquiv H (Ideal.Quotient.mk _ (p : A⟦X⟧)) = Ideal.Quotient.mk _ p := by
  rw [distinguishedQuotientEquiv, AlgEquiv.coe_ringEquiv,
    AlgEquiv.symm_apply_eq, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]
  rfl

/-- Weierstrass preparation for `T² - s b²`: `B⟦s⟧⟦T⟧/(T² - s b²) ≅ B⟦s⟧[T]/(T² - s b²)`. -/
def pinchWeierstrassEquiv :
    ((MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧ ⧸
      Ideal.span {((pinchPoly (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k) :
        Polynomial (MvPowerSeries (Fin (m + 1)) k)⟦X⟧) :
          (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧)}) ≃+*
      PinchRing (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k) :=
  distinguishedQuotientEquiv (pinchPoly_isDistinguishedAt _)

/-- `pinchWeierstrassEquiv` sends the class of a polynomial `p` to its class. -/
theorem pinchWeierstrassEquiv_mk (p : Polynomial (MvPowerSeries (Fin (m + 1)) k)⟦X⟧) :
    pinchWeierstrassEquiv k m (Ideal.Quotient.mk _ (p : (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧)) =
      Ideal.Quotient.mk _ p := by
  rw [pinchWeierstrassEquiv]
  exact distinguishedQuotientEquiv_mk _ p

/-- `k[[x₀, …, x_{m+2}]]/(x₀² - x₁x₂²) ≅ k[[x₂, …]][[x₁]][T]/(T² - x₁x₂²)`. -/
def pinchModelEquiv :
    (MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k)}) ≃ₐ[k]
      PinchRing (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k) :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotientEquivAlg _
    (Ideal.span {((pinchPoly (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k) :
        Polynomial (MvPowerSeries (Fin (m + 1)) k)⟦X⟧) :
          (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧)}) (pinchTowerEquiv k m)
    (by rw [Ideal.map_span, Set.image_singleton]; erw [pinchTowerEquiv_h])).toRingEquiv.trans
    (pinchWeierstrassEquiv k m))
    (fun c => by
      rw [RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
        AlgEquiv.commutes, ← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap,
        Polynomial.algebraMap_apply]
      have : algebraMap k (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧ c =
          ((Polynomial.C (algebraMap k (MvPowerSeries (Fin (m + 1)) k)⟦X⟧ c) :
            Polynomial (MvPowerSeries (Fin (m + 1)) k)⟦X⟧) :
              (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧) := by
        rw [Polynomial.coe_C, PowerSeries.algebraMap_apply]
      rw [this, pinchWeierstrassEquiv_mk])

/-- `pinchTowerEquiv` sends `x₀` to the outer variable `T`. -/
theorem pinchTowerEquiv_X_zero :
    pinchTowerEquiv k m (MvPowerSeries.X 0) =
      ((Polynomial.X : Polynomial (MvPowerSeries (Fin (m + 1)) k)⟦X⟧) :
        (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧) := by
  simp only [pinchTowerEquiv, AlgEquiv.trans_apply, MvPowerSeries.finSuccEquiv_X_zero,
    powerSeriesMapAlgEquiv, AlgEquiv.ofAlgHom_apply, mapAlgHom_apply, map_X, Polynomial.coe_X]

/-- `pinchTowerEquiv` sends `x₂` to the constant `x₂ ∈ k[[x₂, …, x_{m+2}]]`. -/
theorem pinchTowerEquiv_X_two :
    pinchTowerEquiv k m (MvPowerSeries.X 2) =
      ((Polynomial.C (PowerSeries.C (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k)) :
        Polynomial (MvPowerSeries (Fin (m + 1)) k)⟦X⟧) :
        (MvPowerSeries (Fin (m + 1)) k)⟦X⟧⟦X⟧) := by
  have e2 : MvPowerSeries.finSuccEquiv k (m + 2) (MvPowerSeries.X 2) =
      C (MvPowerSeries.X 1) := MvPowerSeries.finSuccEquiv_X_succ (j := 1)
  have f1 : MvPowerSeries.finSuccEquiv k (m + 1) (MvPowerSeries.X 1) =
      C (MvPowerSeries.X 0) := MvPowerSeries.finSuccEquiv_X_succ (j := 0)
  simp only [pinchTowerEquiv, AlgEquiv.trans_apply, e2, powerSeriesMapAlgEquiv,
    AlgEquiv.ofAlgHom_apply, mapAlgHom_apply, map_C, Polynomial.coe_C]
  erw [f1]

/-- `pinchModelEquiv` sends `x₀` to `T`. -/
theorem pinchModelEquiv_mk_X_zero :
    pinchModelEquiv k m (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) =
      Ideal.Quotient.mk _ Polynomial.X := by
  change pinchWeierstrassEquiv k m
    (Ideal.Quotient.mk _ (pinchTowerEquiv k m (MvPowerSeries.X 0))) = _
  rw [pinchTowerEquiv_X_zero, pinchWeierstrassEquiv_mk]

/-- `pinchModelEquiv` sends `x₂` to `b = x₂ ∈ B`. -/
theorem pinchModelEquiv_mk_X_two :
    pinchModelEquiv k m (Ideal.Quotient.mk _ (MvPowerSeries.X 2)) =
      Ideal.Quotient.mk _ (Polynomial.C (PowerSeries.C (MvPowerSeries.X 0))) := by
  change pinchWeierstrassEquiv k m
    (Ideal.Quotient.mk _ (pinchTowerEquiv k m (MvPowerSeries.X 2))) = _
  rw [pinchTowerEquiv_X_two, pinchWeierstrassEquiv_mk]

private theorem pinchMap_algebraMap (c : k) :
    pinchMap (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k)
      (@algebraMap k (PinchRing (MvPowerSeries.X 0 : MvPowerSeries (Fin (m + 1)) k)) _
        CommSemiring.toSemiring _ c) =
      PowerSeries.C (MvPowerSeries.C c) := by
  rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, pinchMap_mk_C,
    PowerSeries.algebraMap_apply, expand_C]
  rfl

private theorem mem_maximalIdeal_powerSeries_sub (k : Type*) [Field k] (m : ℕ)
    (f : (MvPowerSeries (Fin (m + 1)) k)⟦X⟧) :
    f - PowerSeries.C (MvPowerSeries.C
      (MvPowerSeries.constantCoeff (PowerSeries.constantCoeff f))) ∈
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin (m + 1)) k)⟦X⟧ := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.isUnit_iff_constantCoeff]
  simp

/-- **The completed local ring of the normalization at a point over a pinch point.** Let `L` be a
local normal domain receiving `ψ : k[[x₀, …, x_{m+2}]]/(x₀² - x₁x₂²) → L`, integral and birational
(every element of `L` is a fraction with denominator the image of a non-zero-divisor), with no
non-zero-divisor in its kernel. Then `L ≅ k[[u, x₂, …, x_{m+2}]]`: it is a regular local ring and
its residue field is spanned by `k`. -/
private theorem isRegularLocalRing_and_residue_of_pinch {k : Type*} [Field k] (m : ℕ) {L : Type*}
    [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
    (ψ : (MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k)}) →+* L)
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0) :
    IsRegularLocalRing L ∧
      ∀ l : L, ∃ c : k, l - ψ (algebraMap k _ c) ∈ IsLocalRing.maximalIdeal L := by
  set B := MvPowerSeries (Fin (m + 1)) k
  set b : B := MvPowerSeries.X 0
  have : IsRegularLocalRing B := MvPowerSeries.isRegularLocalRing k (m + 1)
  have : IsDomain B := IsRegularLocalRing.isDomain B
  have hb : b ≠ 0 := fun h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
    simp [b, MvPowerSeries.coeff_X] at this
  set ι := pinchModelEquiv k m
  have : IsDomain (PinchRing b) := (pinchMap_injective b hb).isDomain
  have : IsDomain (MvPowerSeries (Fin (m + 3)) k ⧸ Ideal.span
      {(MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
        MvPowerSeries (Fin (m + 3)) k)}) := ι.toRingEquiv.toMulEquiv.isDomain
  set ψ' : PinchRing b →+* L := ψ.comp ι.symm.toRingEquiv.toRingHom
  have hψ' : ∀ r, ψ' (ι r) = ψ r := fun r => by simp [ψ']
  have hψ'inj : Function.Injective ψ' := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    refine hnz (ι.symm r) ?_ hr
    exact mem_nonZeroDivisors_of_ne_zero (by simpa using hr0)
  let : Algebra (PinchRing b) L := ψ'.toAlgebra
  have hal : ∀ r, algebraMap (PinchRing b) L r = ψ' r := fun r => by
    rw [RingHom.algebraMap_toAlgebra]
  have : FaithfulSMul (PinchRing b) L := (faithfulSMul_iff_algebraMap_injective _ _).2 hψ'inj
  have : Algebra.IsIntegral (PinchRing b) L := ⟨fun l => by
    obtain ⟨p, hp, hpl⟩ := hint l
    refine ⟨p.map ι.toRingEquiv.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hpl using 2
    all_goals try rfl
    ext r
    exact (hal _).trans (hψ' r)⟩
  have hL : ∀ l : L, ∃ r s : PinchRing b, s ≠ 0 ∧
      algebraMap (PinchRing b) L s * l = algebraMap (PinchRing b) L r := fun l => by
    obtain ⟨r, s, hs, h⟩ := hbir l
    refine ⟨ι r, ι s, by simpa using nonZeroDivisors.ne_zero hs, ?_⟩
    rw [hal, hal, hψ', hψ']
    exact h
  let : Algebra (PinchRing b) B⟦X⟧ := (pinchMap b).toAlgebra
  have : FaithfulSMul (PinchRing b) B⟦X⟧ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (pinchMap_injective b hb)
  have : Algebra.IsIntegral (PinchRing b) B⟦X⟧ := ⟨fun f => pinchMap_isIntegralElem b f⟩
  have : IsRegularLocalRing B⟦X⟧ := PowerSeries.isRegularLocalRing B
  have : IsDomain B⟦X⟧ := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid B⟦X⟧ := IsRegularLocalRing.uniqueFactorizationMonoid _
  obtain ⟨σ⟩ := nonempty_algEquiv_of_isIntegrallyClosed_of_birational (PinchRing b) L B⟦X⟧ hL
    (fun f => by
      obtain ⟨r, s, hs, h⟩ := pinchMap_birational hb f
      exact ⟨r, s, fun h0 => hs (by rw [h0, map_zero]), h⟩)
  refine ⟨IsRegularLocalRing.of_ringEquiv σ.symm.toRingEquiv, fun l => ?_⟩
  refine ⟨MvPowerSeries.constantCoeff (PowerSeries.constantCoeff (σ l)), ?_⟩
  have hσ : ∀ c : k, σ (ψ (algebraMap k _ c)) = PowerSeries.C (MvPowerSeries.C c) := fun c => by
    rw [← hψ', AlgEquiv.commutes, ← hal, AlgEquiv.commutes]
    exact pinchMap_algebraMap k m c
  have := mem_maximalIdeal_powerSeries_sub k m (σ l)
  rw [← hσ, ← map_sub] at this
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this ⊢
  exact fun h => this (h.map σ)

end PinchModel

end Normalization

end MMP.Flips

namespace MMP.Flips

namespace Normalization

section DNC

variable {k : Type*} [Field k] {n : ℕ}

/-- Restriction to `x₀ = 0`: `k[[x₀, …, xₙ]] → k[[x₁, …, xₙ]]`. -/
def restrictZero (k : Type*) [Field k] (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) k →+* MvPowerSeries (Fin n) k :=
  PowerSeries.constantCoeff.comp (MvPowerSeries.finSuccEquiv k n).toRingEquiv.toRingHom

/-- The inclusion `k[[x₁, …, xₙ]] → k[[x₀, …, xₙ]]`. -/
def inclZero (k : Type*) [Field k] (n : ℕ) :
    MvPowerSeries (Fin n) k →+* MvPowerSeries (Fin (n + 1)) k :=
  (MvPowerSeries.finSuccEquiv k n).symm.toRingEquiv.toRingHom.comp PowerSeries.C

/-- Restricting to `x₀ = 0` after including `k[[x₁, …, xₙ]]` is the identity. -/
theorem restrictZero_inclZero (b : MvPowerSeries (Fin n) k) :
    restrictZero k n (inclZero k n b) = b := by
  simp [restrictZero, inclZero]

/-- Restriction to `x₀ = 0` sends `x₀` to `0`. -/
theorem restrictZero_X_zero : restrictZero k n (MvPowerSeries.X 0) = 0 := by
  simp [restrictZero, MvPowerSeries.finSuccEquiv_X_zero]

/-- `x₀` divides `f - f|_{x₀ = 0}` in `k[[x₀, …, xₙ]]`. -/
theorem sub_inclZero_restrictZero_mem (f : MvPowerSeries (Fin (n + 1)) k) :
    MvPowerSeries.X 0 ∣ f - inclZero k n (restrictZero k n f) := by
  set e := MvPowerSeries.finSuccEquiv k n
  have : PowerSeries.X ∣ e f - PowerSeries.C (PowerSeries.constantCoeff (e f)) := by
    rw [PowerSeries.X_dvd_iff]; simp
  obtain ⟨q, hq⟩ := this
  refine ⟨e.symm q, e.injective ?_⟩
  simp only [map_sub, map_mul, AlgEquiv.apply_symm_apply, MvPowerSeries.finSuccEquiv_X_zero,
    e] at hq ⊢
  rw [← hq]
  simp [inclZero, restrictZero]

/-- `x₀` divides `f` if and only if the restriction of `f` to `x₀ = 0` vanishes. -/
theorem X_zero_dvd_iff (f : MvPowerSeries (Fin (n + 1)) k) :
    MvPowerSeries.X 0 ∣ f ↔ restrictZero k n f = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [map_mul, restrictZero_X_zero, zero_mul]
  · intro h
    have := sub_inclZero_restrictZero_mem f
    rwa [h, map_zero, sub_zero] at this

/-- The variable `x₀` is prime in `k[[x₀, …, xₙ]]`. -/
theorem prime_X_zero : Prime (MvPowerSeries.X 0 : MvPowerSeries (Fin (n + 1)) k) := by
  have : IsRegularLocalRing (MvPowerSeries (Fin n) k) := MvPowerSeries.isRegularLocalRing k n
  have : IsDomain (MvPowerSeries (Fin n) k) := IsRegularLocalRing.isDomain _
  rw [← Ideal.span_singleton_prime]
  · have hker : RingHom.ker (restrictZero k n) = Ideal.span {MvPowerSeries.X 0} := by
      ext f
      rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_zero_dvd_iff]
    rw [← hker]
    exact RingHom.ker_isPrime _
  · intro h
    have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
    simp [MvPowerSeries.coeff_X] at this

/-- Each variable `xᵢ` is prime in `k[[x₀, …, xₙ]]`. -/
theorem prime_X (i : Fin (n + 1)) :
    Prime (MvPowerSeries.X i : MvPowerSeries (Fin (n + 1)) k) := by
  let e := MvPowerSeries.renameEquiv k (Equiv.swap (0 : Fin (n + 1)) i)
  have he : e (MvPowerSeries.X 0) = MvPowerSeries.X i := by
    simp [e, MvPowerSeries.renameEquiv, MvPowerSeries.rename_X]
  rw [← he]
  exact (MulEquiv.prime_iff e.toMulEquiv).mpr prime_X_zero

/-- The ideal `(x₀x₁)` of `k[[x₀, …, xₙ]]`. -/
private abbrev dncIdeal (k : Type*) [Field k] (n : ℕ) : Ideal (MvPowerSeries (Fin (n + 1)) k) :=
  Ideal.span {(MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (n + 1)) k)}

/-- An element of `k[[x]]/(x₀x₁)` is a non-zero-divisor as soon as a representative is divisible
neither by `x₀` nor by `x₁`. -/
private theorem mk_mem_nonZeroDivisors_of_not_dvd {f : MvPowerSeries (Fin (n + 1)) k}
    (h0 : ¬ MvPowerSeries.X 0 ∣ f) (h1 : ¬ MvPowerSeries.X 1 ∣ f) :
    Ideal.Quotient.mk (dncIdeal k n) f ∈ nonZeroDivisors _ := by
  have : IsRegularLocalRing (MvPowerSeries (Fin (n + 1)) k) :=
    MvPowerSeries.isRegularLocalRing k (n + 1)
  have : IsDomain (MvPowerSeries (Fin (n + 1)) k) := IsRegularLocalRing.isDomain _
  have : UniqueFactorizationMonoid (MvPowerSeries (Fin (n + 1)) k) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have hrel : IsRelPrime (MvPowerSeries.X 0 * MvPowerSeries.X 1) f :=
    ((prime_X 0).irreducible.isRelPrime_iff_not_dvd.mpr h0).mul_left
      ((prime_X 1).irreducible.isRelPrime_iff_not_dvd.mpr h1)
  have key : ∀ g, Ideal.Quotient.mk (dncIdeal k n) (f * g) = 0 →
      Ideal.Quotient.mk (dncIdeal k n) g = 0 := by
    intro g hg
    rw [Ideal.Quotient.eq_zero_iff_dvd] at hg ⊢
    exact hrel.dvd_of_dvd_mul_left hg
  refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact key g (by rwa [map_mul])
  · obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact key g (by rwa [map_mul, mul_comm])

/-- **The dnc model, branch `x₀ = 0`.** -/
private theorem isRegularLocalRing_and_residue_of_dnc_of_zero {L : Type*}
    [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
    (ψ : (MvPowerSeries (Fin (n + 1)) k ⧸ dncIdeal k n) →+* L)
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0)
    (h0 : ψ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) = 0) :
    IsRegularLocalRing L ∧
      ∀ l : L, ∃ c : k, l - ψ (algebraMap k _ c) ∈ IsLocalRing.maximalIdeal L := by
  set B := MvPowerSeries (Fin n) k
  have : IsRegularLocalRing B := MvPowerSeries.isRegularLocalRing k n
  have : IsDomain B := IsRegularLocalRing.isDomain B
  have : UniqueFactorizationMonoid B := IsRegularLocalRing.uniqueFactorizationMonoid _
  set Ψ := ψ.comp (Ideal.Quotient.mk (dncIdeal k n))
  set θ : B →+* L := Ψ.comp (inclZero k n)
  have hΨ : ∀ f, Ψ f = θ (restrictZero k n f) := fun f => by
    obtain ⟨q, hq⟩ := sub_inclZero_restrictZero_mem f
    have := congrArg Ψ hq
    rw [map_sub, map_mul] at this
    have hX : Ψ (MvPowerSeries.X 0) = 0 := h0
    rw [hX, zero_mul, sub_eq_zero] at this
    exact this
  -- the descent of `restrictZero` to the quotient
  set F : (MvPowerSeries (Fin (n + 1)) k ⧸ dncIdeal k n) →+* B :=
    Ideal.Quotient.lift (dncIdeal k n) (restrictZero k n) fun a ha => by
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, map_mul, restrictZero_X_zero, zero_mul, mul_zero]
  have hθF : ∀ r, θ (F r) = ψ r := fun r => by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    exact (hΨ f).symm
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    set d := inclZero k n b
    have hd0 : ¬ MvPowerSeries.X 0 ∣ d := by
      rw [X_zero_dvd_iff, restrictZero_inclZero]; exact hb0
    have hzd : ∀ i : ℕ, 0 < i → MvPowerSeries.X 1 ∣ d + MvPowerSeries.X 0 ^ i := by
      intro i hi
      by_contra h1
      refine hnz _ (mk_mem_nonZeroDivisors_of_not_dvd (f := d + MvPowerSeries.X 0 ^ i) ?_ h1) ?_
      · intro h
        exact hd0 ((dvd_add_left (dvd_pow_self _ hi.ne')).mp h)
      · change Ψ _ = 0
        rw [map_add, map_pow, show Ψ (MvPowerSeries.X 0) = 0 from h0, zero_pow hi.ne', add_zero]
        exact hb
    have h12 := dvd_sub (hzd 1 one_pos) (hzd 2 two_pos)
    rw [add_sub_add_left_eq_sub] at h12
    by_cases h10 : (1 : Fin (n + 1)) = 0
    · have := hzd 1 one_pos
      rw [h10, pow_one] at this
      exact hd0 ((dvd_add_left (dvd_refl _)).mp this)
    · rw [MvPowerSeries.X_dvd_iff] at h12
      have := h12 (Finsupp.single 0 1) (by simp [Ne.symm h10])
      simp [MvPowerSeries.coeff_X_pow, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff] at this
  let : Algebra B L := θ.toAlgebra
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective _ _).2 hθinj
  have : Algebra.IsIntegral B L := ⟨fun l => by
    obtain ⟨p, hp, hpl⟩ := hint l
    refine ⟨p.map F, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap B L).comp F = ψ := RingHom.ext hθF
    rw [this]
    exact hpl⟩
  have hL : ∀ l : L, ∃ r s : B, s ≠ 0 ∧ algebraMap B L s * l = algebraMap B L r := fun l => by
    obtain ⟨r, s, hs, h⟩ := hbir l
    refine ⟨F r, F s, fun h0' => hnz s hs ?_, ?_⟩
    · rw [← hθF, h0', map_zero]
    · change θ (F s) * l = θ (F r)
      rw [hθF, hθF]; exact h
  obtain ⟨σ⟩ := nonempty_algEquiv_of_isIntegrallyClosed_of_birational B L B hL
    (fun c => ⟨c, 1, one_ne_zero, by simp⟩)
  refine ⟨IsRegularLocalRing.of_ringEquiv σ.symm.toRingEquiv, fun l => ?_⟩
  refine ⟨MvPowerSeries.constantCoeff (σ l), ?_⟩
  have hσ : ∀ c : k, σ (ψ (algebraMap k _ c)) = MvPowerSeries.C c := fun c => by
    rw [← hθF]
    change σ (algebraMap B L _) = _
    rw [AlgEquiv.commutes]
    simp [F, ← Ideal.Quotient.mk_algebraMap, restrictZero, MvPowerSeries.algebraMap_apply]
  have hm : σ l - MvPowerSeries.C (MvPowerSeries.constantCoeff (σ l)) ∈
      IsLocalRing.maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  rw [← hσ, ← map_sub] at hm
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm ⊢
  exact fun h => hm (h.map σ)

private theorem map_mem_nonZeroDivisors_of_equiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {s : R} (hs : s ∈ nonZeroDivisors R) : e s ∈ nonZeroDivisors S := by
  rw [← MulEquivClass.map_nonZeroDivisors e]
  exact Submonoid.mem_map_of_mem _ hs

/-- The automorphism of `k[[x]]/(x₀x₁)` exchanging `x₀` and `x₁`. -/
private def dncSwap (k : Type*) [Field k] (n : ℕ) :
    (MvPowerSeries (Fin (n + 1)) k ⧸ dncIdeal k n) ≃ₐ[k]
      (MvPowerSeries (Fin (n + 1)) k ⧸ dncIdeal k n) :=
  Ideal.quotientEquivAlg _ _ (MvPowerSeries.renameEquiv k (Equiv.swap 0 1)) (by
    rw [Ideal.map_span, Set.image_singleton, map_mul]
    simp [MvPowerSeries.renameEquiv, MvPowerSeries.rename_X, mul_comm])

private theorem dncSwap_mk_X_zero :
    dncSwap k n (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) =
      Ideal.Quotient.mk _ (MvPowerSeries.X 1) := by
  simp [dncSwap, MvPowerSeries.renameEquiv, MvPowerSeries.rename_X]

/-- **The completed local ring of the normalization at a point over a double normal crossing
point.** Let `L` be a local normal domain receiving `ψ : k[[x₀, …, xₙ]]/(x₀x₁) → L`, integral and
birational, with no non-zero-divisor in its kernel. Then `L ≅ k[[x₁, …, xₙ]]`, a regular local ring
whose residue field is spanned by `k`. -/
private theorem isRegularLocalRing_and_residue_of_dnc {L : Type*}
    [CommRing L] [IsLocalRing L] [IsDomain L] [IsIntegrallyClosed L]
    (ψ : (MvPowerSeries (Fin (n + 1)) k ⧸ dncIdeal k n) →+* L)
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors _ ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors _, ψ s ≠ 0) :
    IsRegularLocalRing L ∧
      ∀ l : L, ∃ c : k, l - ψ (algebraMap k _ c) ∈ IsLocalRing.maximalIdeal L := by
  have h01 : ψ (Ideal.Quotient.mk _ (MvPowerSeries.X 0)) *
      ψ (Ideal.Quotient.mk _ (MvPowerSeries.X 1)) = 0 := by
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
      map_zero]
  rcases mul_eq_zero.mp h01 with h0 | h1
  · exact isRegularLocalRing_and_residue_of_dnc_of_zero ψ hint hbir hnz h0
  set τ := dncSwap k n
  set ψ' := ψ.comp τ.toRingEquiv.toRingHom
  have hψ' : ∀ r, ψ' (τ.symm r) = ψ r := fun r => by simp [ψ']
  obtain ⟨hreg, hres⟩ := isRegularLocalRing_and_residue_of_dnc_of_zero ψ'
    (fun l => by
      obtain ⟨p, hp, hpl⟩ := hint l
      refine ⟨p.map τ.symm.toRingEquiv.toRingHom, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have : ψ'.comp τ.symm.toRingEquiv.toRingHom = ψ := RingHom.ext hψ'
      rw [this]; exact hpl)
    (fun l => by
      obtain ⟨r, s, hs, h⟩ := hbir l
      exact ⟨τ.symm r, τ.symm s, map_mem_nonZeroDivisors_of_equiv τ.symm.toRingEquiv hs,
        by rw [hψ', hψ']; exact h⟩)
    (fun s hs => by
      have := hnz (τ s) (map_mem_nonZeroDivisors_of_equiv τ.toRingEquiv hs)
      simpa [ψ'] using this)
    (by
      change ψ (τ _) = 0
      rw [show τ = dncSwap k n from rfl, dncSwap_mk_X_zero, h1])
  refine ⟨hreg, fun l => ?_⟩
  obtain ⟨c, hc⟩ := hres l
  refine ⟨c, ?_⟩
  simpa [ψ'] using hc

end DNC

end Normalization

end MMP.Flips

namespace MMP.Flips

open Normalization

section Bridge

/-- **A factor of the normalization of `Ac`.** Let `N` be an `Ac`-algebra (through `j`) embedded
in the total ring of fractions of `Ac` as the integral closure of `Ac`, and `N ≅ ∏ᵢ Lᵢ`. Then the
map `Ac → L_{i₀}` to a nonzero factor is integral and birational, and no non-zero-divisor of `Ac`
lies in its kernel. -/
private theorem factor_of_normalization {Ac N : Type*} [CommRing Ac] [CommRing N] {I : Type*}
    {L : I → Type*} [∀ i, CommRing (L i)] (j : Ac →+* N) (e : N ≃+* ∀ i, L i)
    (g : N →+* FractionRing Ac) (hg : Function.Injective g)
    (hrange : g.range = (integralClosure Ac (FractionRing Ac)).toSubring)
    (hgj : ∀ y, g (j y) = algebraMap Ac (FractionRing Ac) y) (i₀ : I) [Nontrivial (L i₀)] :
    let ψ : Ac →+* L i₀ := (Pi.evalRingHom L i₀).comp (e.toRingHom.comp j)
    (∀ l, ψ.IsIntegralElem l) ∧
      (∀ l, ∃ r s, s ∈ nonZeroDivisors Ac ∧ ψ s * l = ψ r) ∧
      (∀ s ∈ nonZeroDivisors Ac, ψ s ≠ 0) := by
  intro ψ
  classical
  have hψ : ∀ y, ψ y = e (j y) i₀ := fun _ => rfl
  have hgj' : g.comp j = algebraMap Ac (FractionRing Ac) := RingHom.ext hgj
  -- an element of `N` with prescribed component
  have hpre : ∀ l : L i₀, e (e.symm (Pi.single i₀ l)) i₀ = l := fun l => by simp
  refine ⟨fun l => ?_, fun l => ?_, fun s hs h0 => ?_⟩
  · set m := e.symm (Pi.single i₀ l)
    have hm : g m ∈ integralClosure Ac (FractionRing Ac) := by
      have : g m ∈ g.range := ⟨m, rfl⟩
      rw [hrange] at this; exact this
    obtain ⟨p, hp, hpe⟩ := hm
    refine ⟨p, hp, ?_⟩
    have h1 : g (Polynomial.eval₂ j m p) = 0 := by
      rw [Polynomial.hom_eval₂, hgj']; exact hpe
    have h2 : Polynomial.eval₂ j m p = 0 := hg (by rw [h1, map_zero])
    have h3 := Polynomial.hom_eval₂ p j ((Pi.evalRingHom L i₀).comp e.toRingHom) m
    rw [h2, map_zero] at h3
    rw [← hpre l]
    exact h3.symm
  · set m := e.symm (Pi.single i₀ l)
    obtain ⟨x, hab⟩ := IsLocalization.mk'_surjective (nonZeroDivisors Ac) (g m)
    set a := x.1
    set b := x.2
    refine ⟨a, b, b.2, ?_⟩
    have : g (j b * m) = g (j a) := by
      rw [map_mul, hgj, hgj, ← hab, mul_comm]
      exact IsLocalization.mk'_spec (FractionRing Ac) a b
    have := congrArg (fun z => e z i₀) (hg this)
    simp only [map_mul, Pi.mul_apply] at this
    rw [hψ, hψ, ← this, hpre]
  · set m := e.symm (Pi.single i₀ 1)
    have hzero : m * j s = 0 := by
      apply e.injective
      ext i
      rw [map_mul, Pi.mul_apply, map_zero, Pi.zero_apply]
      by_cases hi : i = i₀
      · subst hi
        rw [← hψ, h0, mul_zero]
      · simp [m, hi]
    have hgm : g m = 0 := by
      have := congrArg g hzero
      rw [map_mul, hgj, map_zero] at this
      exact ((IsLocalization.map_units (FractionRing Ac) ⟨s, hs⟩).mul_left_eq_zero).mp this
    have hm0 : m = 0 := hg (by rw [hgm, map_zero])
    have : e m i₀ = 1 := hpre 1
    rw [hm0, map_zero, Pi.zero_apply] at this
    exact zero_ne_one this

end Bridge

end MMP.Flips

namespace MMP.Flips

open Normalization

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

open MMP.Mori

/-- The three properties of `ψ : R → L` used for the models are invariant under an isomorphism
of the source. -/
private theorem props_comp_symm {R R' L : Type*} [CommRing R] [CommRing R'] [CommRing L]
    (ψ : R →+* L) (e : R ≃+* R')
    (hint : ∀ l, ψ.IsIntegralElem l)
    (hbir : ∀ l, ∃ r s, s ∈ nonZeroDivisors R ∧ ψ s * l = ψ r)
    (hnz : ∀ s ∈ nonZeroDivisors R, ψ s ≠ 0) :
    (∀ l, (ψ.comp e.symm.toRingHom).IsIntegralElem l) ∧
      (∀ l, ∃ r s, s ∈ nonZeroDivisors R' ∧
        ψ.comp e.symm.toRingHom s * l = ψ.comp e.symm.toRingHom r) ∧
      (∀ s ∈ nonZeroDivisors R', ψ.comp e.symm.toRingHom s ≠ 0) := by
  refine ⟨fun l => ?_, fun l => ?_, fun s hs => ?_⟩
  · obtain ⟨p, hp, hpl⟩ := hint l
    refine ⟨p.map e.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    convert hpl using 2
    ext r; simp
  · obtain ⟨r, s, hs, h⟩ := hbir l
    exact ⟨e r, e s, map_mem_nonZeroDivisors_of_equiv e hs, by simpa using h⟩
  · simpa using hnz _ (map_mem_nonZeroDivisors_of_equiv e.symm hs)

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- The stalk map of the normalization at `y` is the composite of the structure map of the
pushforward stalk with the canonical map to the stalk at `y`. -/
private theorem canonical_comp_algebraMap_eq_stalkMap
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (y : Scheme.normalizationScheme X hX) (a : X.presheaf.stalk (Scheme.normalization X hX y)) :
    letI := Scheme.normalizationPushforwardStalkAlgebra X hX (Scheme.normalization X hX y)
    (TopCat.Presheaf.stalkSpecializes ((Scheme.normalization X hX).base _*
        (Scheme.normalizationScheme X hX).presheaf)
        (specializes_of_eq (rfl : (Scheme.normalization X hX).base y = _)) ≫
      TopCat.Presheaf.stalkPushforward _ (Scheme.normalization X hX).base
        (Scheme.normalizationScheme X hX).presheaf y).hom
      (algebraMap _ (Scheme.normalizationPushforwardStalk X hX _) a) =
      (Scheme.normalization X hX).stalkMap y a := by
  simp only [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  rfl

/-- The structure map `k → 𝒪_{X,f y}` followed by the stalk map of `f` is the structure map
`k → 𝒪_{Y,y}` of `f ≫ sX`. -/
theorem stalkMap_stalkStructureMap {Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) (c : k) :
    f.stalkMap y (stalkStructureMap sX (f y) c) = stalkStructureMap (f ≫ sX) y c := by
  have h := Scheme.Hom.germ_stalkMap f ⊤ y (show f y ∈ (⊤ : X.Opens) from trivial)
  have key : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
      (X.presheaf.germ ⊤ (f y) (show f y ∈ (⊤ : X.Opens) from trivial) ≫
      f.stalkMap y) = (Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ sX).appTop ≫
        Y.presheaf.germ ⊤ y (show y ∈ (⊤ : Y.Opens) from trivial) := by
    rw [h, Scheme.Hom.comp_appTop, Category.assoc]
    rfl
  exact congrArg (fun φ => φ.hom c) key

/-- The `k`-algebra structure of the residue field `κ(y)` through global sections is the residue
of the structure map `k → 𝒪_{Y,y}`. -/
theorem evaluation_eq_residue_stalkStructureMap {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    (y : Y) (c : k) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation y).hom c =
      Y.residue y (stalkStructureMap sY y c) := by
  rfl

/-- **Regularity and rational residue field at a point of the normalization over a double normal
crossing point or a pinch point.** -/
private theorem isRegularLocalRing_and_residue_of_model [IsReduced X] [LocallyOfFiniteType sX]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (y : Scheme.normalizationScheme X hX)
    (hmodel : (∃ n : ℕ, HasCompletedLocalModel sX (Scheme.normalization X hX y)
        (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (n + 1)) k)) ∨
      (∃ m : ℕ, HasCompletedLocalModel sX (Scheme.normalization X hX y)
        (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 * MvPowerSeries.X 2 ^ 2 :
          MvPowerSeries (Fin (m + 3)) k))) :
    IsRegularLocalRing ((Scheme.normalizationScheme X hX).presheaf.stalk y) ∧
      ∀ a : (Scheme.normalizationScheme X hX).presheaf.stalk y, ∃ c : k,
        a - stalkStructureMap (Scheme.normalization X hX ≫ sX) y c ∈
          maximalIdeal ((Scheme.normalizationScheme X hX).presheaf.stalk y) := by
  obtain ⟨-, ⟨e₁, he₁⟩, g, hg, hrange, hgy⟩ :=
    MMP.Resolution.isReduced_adicCompletion_stalk_and_normalization_completion X sX hX
      (X.normalization hX y)
  let : Algebra (X.presheaf.stalk (X.normalization hX y))
      (Scheme.normalizationPushforwardStalk X hX (X.normalization hX y)) :=
    Scheme.normalizationPushforwardStalkAlgebra X hX (X.normalization hX y)
  have : LocallyOfFiniteType (X.normalization hX ≫ sX) := by
    have : IsFinite (X.normalization hX) := Scheme.isFinite_normalization
      (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
    infer_instance
  have hexc : IsExcellent ((X.normalizationScheme hX).presheaf.stalk y) :=
    AlgebraicGeometry.isExcellent_stalk_of_locallyOfFiniteType_of_isExcellent k
      ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k) (X.normalization hX ≫ sX) y
  have : IsNoetherianRing ((X.normalizationScheme hX).presheaf.stalk y) := hexc.1.1
  have hNormal : IsNormal (X.normalizationScheme hX) := Scheme.isNormal_normalizationScheme X hX
  have hn : IsNormalRing ((X.normalizationScheme hX).presheaf.stalk y) := by
    let : IsDomain ((X.normalizationScheme hX).presheaf.stalk y) := hNormal.stalk_isDomain y
    let : IsIntegrallyClosed ((X.normalizationScheme hX).presheaf.stalk y) := hNormal.stalk_normal y
    exact IsNormalRing.of_isIntegrallyClosed _
  have : IsNormalDomain (AdicCompletion
      (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk y))
      ((X.normalizationScheme hX).presheaf.stalk y)) :=
    AlgebraicGeometry.isNormalDomain_adicCompletion_of_isExcellent _ hexc hn
  have : IsLocalRing (AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk y))
      ((X.normalizationScheme hX).presheaf.stalk y)) :=
    AdicCompletion.isLocalRing_of_fg (IsNoetherian.noetherian _)
  obtain ⟨hint, hbir, hnz⟩ := factor_of_normalization
    (L := fun x' : (X.normalization hX).base ⁻¹' {X.normalization hX y} =>
      AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk x'))
        ((X.normalizationScheme hX).presheaf.stalk x'))
    Algebra.TensorProduct.includeRight.toRingHom e₁ g hg hrange hgy
    (⟨y, rfl⟩ : (X.normalization hX).base ⁻¹' {X.normalization hX y})
  generalize hψ₀ : (Pi.evalRingHom (fun x' : (X.normalization hX).base ⁻¹' {X.normalization hX y} =>
      AdicCompletion (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk x'))
        ((X.normalizationScheme hX).presheaf.stalk x')) ⟨y, rfl⟩).comp
      (e₁.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom) = ψ₀ at hint hbir hnz
  have hψ₀alg : ∀ a : X.presheaf.stalk (X.normalization hX y),
      ψ₀ (algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk (X.normalization hX y)))
        (X.presheaf.stalk (X.normalization hX y))) a) =
      algebraMap ((X.normalizationScheme hX).presheaf.stalk y) _
        ((X.normalization hX).stalkMap y a) := by
    intro a
    rw [← hψ₀]
    simp only [RingHom.comp_apply, Pi.evalRingHom_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← Algebra.algebraMap_eq_smul_one]
    erw [he₁]
    rw [canonical_comp_algebraMap_eq_stalkMap]
  let : Algebra k (X.presheaf.stalk (X.normalization hX y)) :=
    (stalkStructureMap sX (X.normalization hX y)).toAlgebra
  have hkey : IsRegularLocalRing (AdicCompletion
        (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk y))
        ((X.normalizationScheme hX).presheaf.stalk y)) ∧
      ∀ l, ∃ c : k, l - ψ₀ (algebraMap k _ c) ∈ maximalIdeal (AdicCompletion
        (maximalIdeal ((X.normalizationScheme hX).presheaf.stalk y))
        ((X.normalizationScheme hX).presheaf.stalk y)) := by
    rcases hmodel with ⟨n, ⟨e⟩⟩ | ⟨m, ⟨e⟩⟩
    · obtain ⟨h₁, h₂, h₃⟩ := props_comp_symm ψ₀ e.toRingEquiv hint hbir hnz
      obtain ⟨hreg, hres⟩ := isRegularLocalRing_and_residue_of_dnc _ h₁ h₂ h₃
      refine ⟨hreg, fun l => ?_⟩
      obtain ⟨c, hc⟩ := hres l
      refine ⟨c, ?_⟩
      simpa using hc
    · obtain ⟨h₁, h₂, h₃⟩ := props_comp_symm ψ₀ e.toRingEquiv hint hbir hnz
      obtain ⟨hreg, hres⟩ := isRegularLocalRing_and_residue_of_pinch m _ h₁ h₂ h₃
      refine ⟨hreg, fun l => ?_⟩
      obtain ⟨c, hc⟩ := hres l
      refine ⟨c, ?_⟩
      simpa using hc
  obtain ⟨hreg, hres⟩ := hkey
  refine ⟨isRegularLocalRing_iff_adicCompletion_maximalIdeal.mpr hreg, fun a => ?_⟩
  obtain ⟨c, hc⟩ := hres (algebraMap _ _ a)
  refine ⟨c, ?_⟩
  have hk : algebraMap k (AdicCompletion (maximalIdeal (X.presheaf.stalk (X.normalization hX y)))
      (X.presheaf.stalk (X.normalization hX y))) c =
      algebraMap (X.presheaf.stalk (X.normalization hX y)) _
        (algebraMap k (X.presheaf.stalk (X.normalization hX y)) c) := rfl
  rw [hk, hψ₀alg, RingHom.algebraMap_toAlgebra, stalkMap_stalkStructureMap, ← map_sub] at hc
  by_contra hm
  rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hm
  rw [mem_maximalIdeal, mem_nonunits_iff] at hc
  exact hc (hm.map _)

/-- A point of a scheme locally of finite type over `k` whose local ring is regular and whose
residue field is spanned by `k` is a smooth point. -/
theorem mem_smoothLocus_of_isRegularLocalRing {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] [LocallyOfFinitePresentation sY] (y : Y)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hres : ∀ a : Y.presheaf.stalk y, ∃ c : k,
      a - stalkStructureMap sY y c ∈ maximalIdeal (Y.presheaf.stalk y)) :
    y ∈ smoothLocus sY := by
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  have hsurj : Function.Surjective (algebraMap k (Y.residueField y)) := by
    intro z
    obtain ⟨a, rfl⟩ := Y.residue_surjective y z
    obtain ⟨c, hc⟩ := hres a
    refine ⟨c, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, evaluation_eq_residue_stalkStructureMap]
    change IsLocalRing.residue _ _ = IsLocalRing.residue _ a
    exact Ideal.Quotient.eq.mpr (by rw [← neg_sub]; exact neg_mem hc)
  have hsep : Algebra.IsSeparableExtension k (Y.residueField y) :=
    (Algebra.FormallySmooth.iff_isSeparableExtension k _).mp <| .of_equiv <|
      AlgEquiv.ofBijective (Algebra.ofId k _) ⟨(algebraMap k _).injective, hsurj⟩
  have hsm := (smoothAt_iff_isRegularLocalRing_stalk sY y hsep).mpr hreg
  rw [smoothLocus_eq_smoothLocus]
  exact Scheme.Hom.mem_smoothLocus.mpr (hsm.formallySmooth_stalkMap _ _)

/-- **The normalization of a semismooth `n`-fold is smooth** (FA 12.2.1(2)). Let `X` be a
semismooth `n`-fold and `ν : X^ν ⟶ X` its normalization. Then `X^ν` is smooth over `k`. -/
@[mmp "lem_fa12a_semismooth_normalization_smooth"]
theorem IsSemismooth.isSmoothScheme_normalization {n : ℕ} (h : IsSemismooth sX n)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsSmoothScheme (Stacks.AlgebraicGeometry.Normalization.normalization X hX ≫ sX) := by
  obtain ⟨⟨⟨-, hlft, -⟩, hred, -⟩, hpts⟩ := h
  change IsSmoothScheme (X.normalization hX ≫ sX)
  have : IsFinite (X.normalization hX) := Scheme.isFinite_normalization
    (isNagataScheme_of_locallyOfFiniteType_over_field k sX) hX
  have : LocallyOfFiniteType (X.normalization hX ≫ sX) := inferInstance
  have : LocallyOfFinitePresentation (X.normalization hX ≫ sX) :=
    (LocallyOfFinitePresentation.iff_locallyOfFiniteType (f := X.normalization hX ≫ sX)).mpr
      inferInstance
  -- every closed point of `X^ν` is a smooth point
  have hclosed : ∀ y : X.normalizationScheme hX, IsClosed ({y} : Set _) →
      y ∈ smoothLocus (X.normalization hX ≫ sX) := by
    intro y hy
    have hx : IsClosed ({X.normalization hX y} : Set X) := by
      rw [← Set.image_singleton]
      exact (X.normalization hX).isClosedMap _ hy
    rcases hpts _ hx with hs | hd | hp
    · obtain ⟨U, hxU, hU⟩ := mem_smoothLocus_iff.mp hs
      have : IsNormal U.toScheme := isNormal_of_smooth_over_field (U.ι ≫ sX)
      have hiso : IsIso (X.normalization hX ∣_ U) :=
        Scheme.isIso_normalization_restrict_of_isNormal X hX U this
      refine le_smoothLocus (X.normalization hX ≫ sX) (U := X.normalization hX ⁻¹ᵁ U) ?_ hxU
      rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
      infer_instance
    · obtain ⟨hreg, hres⟩ := isRegularLocalRing_and_residue_of_model hX y (Or.inl ⟨n, hd.2.2⟩)
      exact mem_smoothLocus_of_isRegularLocalRing _ y hreg hres
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by have := hp.1; omega⟩
      obtain ⟨hreg, hres⟩ := isRegularLocalRing_and_residue_of_model hX y (Or.inr ⟨m, hp.2.2.2⟩)
      exact mem_smoothLocus_of_isRegularLocalRing _ y hreg hres
  -- closed points are dense in every closed subset (Jacobson)
  have : JacobsonSpace (X.normalizationScheme hX) :=
    LocallyOfFiniteType.jacobsonSpace (X.normalization hX ≫ sX)
  rw [IsSmoothScheme, eq_top_iff]
  intro y _
  by_contra hy
  have hZ : IsClosed ((smoothLocus (X.normalization hX ≫ sX) : Set (X.normalizationScheme hX))ᶜ) :=
    (smoothLocus (X.normalization hX ≫ sX)).isOpen.isClosed_compl
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints ⟨y, hy⟩ hZ.isLocallyClosed
  exact hz (hclosed z hzc)

end MMP.Flips
