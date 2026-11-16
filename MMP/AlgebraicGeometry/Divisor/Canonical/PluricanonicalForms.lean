module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Divisor.Principal
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Rational pluricanonical forms, their divisors, and the sheaves `𝒪_X(mK_X + G)`

Let `X` be a variety of dimension `d` over a field `k`, with function field `k(X)`. For `m ∈ ℤ`
the space of *rational `m`-canonical forms* is the one-dimensional `k(X)`-vector space
`ω^{⊗m}_{k(X)} = (Ω^d_{k(X)/k})^{⊗m}`, the `(-m)`-th tensor power of the dual for `m < 0`. An
extension `u : K → K'` of function fields induces the pull-back `u^* : ω^{⊗m}_K → ω^{⊗m}_{K'}`
through `u^* : Ω^d_{K/k} → Ω^d_{K'/k}`.

For a prime divisor `Γ` of a normal variety the local ring `𝒪_{X,Γ}` is a discrete valuation
ring with fraction field `k(X)`. If `σ` generates `Ω^d_{X,Γ} = Ω^d_{𝒪_{X,Γ}/k}`, the *order*
`ord_Γ(τ)` of a form `τ` is the valuation of `τ / σ^{⊗m} ∈ k(X)`; it does not depend on `σ`, two
generators differing by a unit of `𝒪_{X,Γ}`. The *divisor* of `τ` is
`div(τ) = ∑_Γ ord_Γ(τ) Γ`, a finite sum. For a Weil divisor `G` the sheaf `𝒪_X(mK_X + G)` is the
subsheaf of the constant sheaf `ω^{⊗m}_{k(X)}` of the forms with `ord_Γ(τ) + coeff_Γ(G) ≥ 0` for
every prime divisor `Γ` meeting the open set, and a form *generates `𝒪_X(m(K_X + Δ))` on `U`* when
`ord_Γ(τ) + m·coeff_Γ(Δ) = 0` for every prime divisor `Γ` meeting `U`.

## Main definitions

* `MMP.Mori.ZTensorPower`: the tensor power `L^{⊗m}`, `m ∈ ℤ`, of a module over a field, with the
  basis `MMP.Mori.ZTensorPower.basis` induced by a basis of a line.
* `MMP.Mori.PluriForms`, `MMP.Mori.RationalPluriForms`: `ω^{⊗m}_K` for a field `K` over `k`, and
  `ω^{⊗m}_{k(X)}` for an integral scheme `X` over `k`.
* `MMP.Mori.topFormsMap`: `Ω^d_{A/k} → Ω^d_{K/k}` for an algebra `A → K` over `k`.
* `MMP.Mori.pullbackForms`: the pull-back of forms along an extension of fields.
* `MMP.Mori.ordAt`, `MMP.Mori.PrimeDivisor.ordForm`: the order `v(τ / σ^{⊗m})` along a local
  ring, and `ord_Γ(τ)` along a prime divisor.
* `MMP.Mori.divisorOfForm`: the divisor `div(τ)`.
* `MMP.Mori.pluricanonicalSections`, `MMP.Mori.pluricanonicalPresheaf`,
  `MMP.Mori.pluricanonicalSheaf`: the sheaf `𝒪_X(mK_X + G)` of abelian groups.
* `MMP.Mori.GeneratesOn`: local generators of `𝒪_X(m(K_X + Δ))`.

## Main results

* `MMP.Mori.ordAt_eq`, `MMP.Mori.PrimeDivisor.ordForm_eq`: the order does not depend on the
  generator of `Ω^d_{𝒪_{X,Γ}/k}`.
* `MMP.Mori.pullbackForms_eq`: `u^*(f · ω^{⊗m}) = u(f) · (u^*ω)^{⊗m}`.
* `MMP.Mori.finite_ordForm_ne_zero`: on a Noetherian integral scheme locally of finite type over
  `k`, `ord_Γ(τ) ≠ 0` for only finitely many `Γ`.
* `MMP.Mori.PrimeDivisor.min_ordForm_le_ordForm_add`, `MMP.Mori.PrimeDivisor.ordForm_neg`: the
  order is a valuation on forms.
* `MMP.Mori.isSheaf_pluricanonicalPresheaf`: `𝒪_X(mK_X + G)` is a sheaf.

## Implementation notes

The dimension `d` is a parameter of the forms; the source takes `d = dim X`. The `k`-algebra
structures of the local rings, the function field and the rings of sections come from the
structure morphism `X ⟶ Spec k` and are introduced locally.

The order `ord_Γ(τ)` is defined at every prime divisor of an integral locally Noetherian scheme:
when `Ω^d_{𝒪_{X,Γ}/k}` has a generator whose image in `Ω^d_{k(X)/k}` is nonzero it is
`v_Γ(τ / σ^{⊗m})` for any such generator (`MMP.Mori.PrimeDivisor.ordForm_eq`), and otherwise it
is `0`. On a normal variety of dimension `d` over a field of characteristic zero the generic
point of `Γ` lies in the smooth locus, `Ω^d_{𝒪_{X,Γ}/k}` is free of rank one, and the first case
always applies. The valuation is `AlgebraicGeometry.Scheme.ord`, the valuation of the discrete
valuation ring `𝒪_{X,Γ}` on `k(X)`.

The pull-back is defined by its value on the `m`-th power of a generator `ω` of `Ω^d_{K/k}`
whose image `u^*ω` generates `Ω^d_{K'/k}`. For `m < 0` this is the only definition, since the
dual of `u^*` is inverted; in the source's setting (a dominant morphism of varieties of the same
dimension over a field of characteristic zero) `u^*` is an isomorphism after base change to
`K'`, and such an `ω` exists. Otherwise the pull-back is `0`.

The source describes the sections of `𝒪_X(mK_X)` over `U` as the forms regular on
`U ∩ X_reg`, and equivalently by the order conditions along the prime divisors meeting `U`; the
order conditions are taken as the definition, which also covers the twist by `G`. Over the empty
open set the sections are `0`, as a sheaf requires.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.10–2.12,
  2.25
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Order Topology
open scoped TensorProduct

universe u

namespace MMP.Mori

/-! ### Integral tensor powers of a module -/

section ZTensorPower

/-- For a basis `b` of a line indexed by `Unit`, every vector `x` is `b.repr x () • b ()`. -/
theorem basis_unit_repr_smul {K L : Type*} [Semiring K] [AddCommMonoid L] [Module K L]
    (b : Module.Basis Unit K L) (x : L) : b.repr x () • b () = x := by
  conv_rhs => rw [← b.sum_repr x]
  simp

variable (K : Type*) [Field K] (L : Type*) [AddCommGroup L] [Module K L]

/-- The `m`-th tensor power `L^{⊗m}` of a `K`-module `L`, for `m ∈ ℤ`: the `m`-th tensor power
of `L` for `m ≥ 0`, and the `(-m)`-th tensor power of the dual `L^∨ = Hom_K(L, K)` for `m < 0`. -/
def ZTensorPower : ℤ → Type _
  | .ofNat n => ⨂[K]^n L
  | .negSucc n => ⨂[K]^(n + 1) (Module.Dual K L)

/-- The abelian group structure of `L^{⊗m}`. -/
instance ZTensorPower.instAddCommGroup : (m : ℤ) → AddCommGroup (ZTensorPower K L m)
  | .ofNat n => inferInstanceAs (AddCommGroup (⨂[K]^n L))
  | .negSucc n => inferInstanceAs (AddCommGroup (⨂[K]^(n + 1) (Module.Dual K L)))

/-- The `K`-module structure of `L^{⊗m}`. -/
instance ZTensorPower.instModule : (m : ℤ) → Module K (ZTensorPower K L m)
  | .ofNat n => inferInstanceAs (Module K (⨂[K]^n L))
  | .negSucc n => inferInstanceAs (Module K (⨂[K]^(n + 1) (Module.Dual K L)))

variable {K L}

/-- A basis `b` of a line `L` induces the basis `b^{⊗m}` of `L^{⊗m}`: the tensor power of `b` for
`m ≥ 0`, and the tensor power of the dual basis `b^∨` for `m < 0`. -/
def ZTensorPower.basis (b : Module.Basis Unit K L) :
    (m : ℤ) → Module.Basis Unit K (ZTensorPower K L m)
  | .ofNat n => ((Basis.piTensorProduct fun _ : Fin n => b).reindex
      (Equiv.ofUnique _ _) : Module.Basis Unit K (⨂[K]^n L))
  | .negSucc n => ((Basis.piTensorProduct fun _ : Fin (n + 1) => b.dualBasis).reindex
      (Equiv.ofUnique _ _) : Module.Basis Unit K (⨂[K]^(n + 1) (Module.Dual K L)))

/-- A nonzero vector `ω` spanning `L` is a basis of the line `L`. -/
def basisOfSpanSingleton {ω : L} (hω : Submodule.span K {ω} = ⊤) (h0 : ω ≠ 0) :
    Module.Basis Unit K L :=
  .mk (v := fun _ : Unit => ω) (linearIndependent_unique_iff.mpr h0)
    (by rw [Set.range_const, hω])

/-- The basis vector of `basisOfSpanSingleton hω h0` is `ω`. -/
@[simp]
theorem basisOfSpanSingleton_apply {ω : L} (hω : Submodule.span K {ω} = ⊤) (h0 : ω ≠ 0)
    (i : Unit) : basisOfSpanSingleton hω h0 i = ω :=
  Module.Basis.mk_apply _ _ _

/-- For `m = n ≥ 0`, the basis vector of `b^{⊗n}` is the pure tensor `b ⊗ ⋯ ⊗ b`. -/
theorem ZTensorPower.basis_ofNat (b : Module.Basis Unit K L) (n : ℕ) :
    (basis b (.ofNat n) () : ⨂[K]^n L) = ⨂ₜ[K] _ : Fin n, b () := by
  change ((Basis.piTensorProduct fun _ : Fin n => b).reindex (Equiv.ofUnique _ _)) () = _
  rw [Module.Basis.reindex_apply, Basis.piTensorProduct_apply]

/-- For `m = -(n + 1) < 0`, the basis vector of `b^{⊗m}` is the pure tensor `b^∨ ⊗ ⋯ ⊗ b^∨` of
`n + 1` copies of the dual basis vector. -/
theorem ZTensorPower.basis_negSucc (b : Module.Basis Unit K L) (n : ℕ) :
    (basis b (.negSucc n) () : ⨂[K]^(n + 1) (Module.Dual K L)) =
      ⨂ₜ[K] _ : Fin (n + 1), b.dualBasis () := by
  change ((Basis.piTensorProduct fun _ : Fin (n + 1) => b.dualBasis).reindex
    (Equiv.ofUnique _ _)) () = _
  rw [Module.Basis.reindex_apply, Basis.piTensorProduct_apply]

/-- The pure tensor of `n` copies of `c • x` is `c ^ n` times the pure tensor of `n` copies
of `x`. -/
theorem tprod_const_smul {M : Type*} [AddCommMonoid M] [Module K M] {n : ℕ} (c : K) (x : M) :
    (⨂ₜ[K] _ : Fin n, c • x) = c ^ n • ⨂ₜ[K] _ : Fin n, x := by
  simpa [Finset.prod_const] using
    (PiTensorProduct.tprod K (s := fun _ : Fin n => M)).map_smul_univ (fun _ => c) fun _ => x

/-- If `b' = c • b` then `b'^{⊗m} = c^m • b^{⊗m}`. -/
theorem ZTensorPower.basis_apply_of_eq_smul {b b' : Module.Basis Unit K L} {c : K}
    (h : b' () = c • b ()) (m : ℤ) : basis b' m () = c ^ m • basis b m () := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact b'.ne_zero () (by simpa using h)
  cases m with
  | ofNat n =>
    change (basis b' (.ofNat n) () : ⨂[K]^n L) = c ^ (n : ℤ) • (basis b (.ofNat n) () : ⨂[K]^n L)
    rw [basis_ofNat, basis_ofNat, h, zpow_natCast]
    exact tprod_const_smul c (b ())
  | negSucc n =>
    have hd : b'.dualBasis () = c⁻¹ • b.dualBasis () := by
      have hb : b () = c⁻¹ • b' () := by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
      refine b.ext fun i => ?_
      cases i
      rw [LinearMap.smul_apply, Module.Basis.dualBasis_apply_self, hb, LinearMap.map_smul,
        Module.Basis.dualBasis_apply_self]
    change (basis b' (.negSucc n) () : ⨂[K]^(n + 1) (Module.Dual K L)) =
      c ^ (Int.negSucc n) • (basis b (.negSucc n) () : ⨂[K]^(n + 1) (Module.Dual K L))
    rw [basis_negSucc, basis_negSucc, hd, zpow_negSucc, ← inv_pow]
    exact tprod_const_smul c⁻¹ (b.dualBasis ())

/-- If `b' = c • b`, the coordinate of `τ` along `b'^{⊗m}` is `c^{-m}` times that along
`b^{⊗m}`. -/
theorem ZTensorPower.basis_repr_of_eq_smul {b b' : Module.Basis Unit K L} {c : K}
    (h : b' () = c • b ()) (m : ℤ) (τ : ZTensorPower K L m) :
    (basis b' m).repr τ () = (c ^ m)⁻¹ * (basis b m).repr τ () := by
  have hc : c ^ m ≠ 0 := by
    refine zpow_ne_zero m ?_
    rintro rfl
    exact b'.ne_zero () (by simpa using h)
  have hτ : τ = ((basis b m).repr τ () * (c ^ m)⁻¹) • basis b' m () := by
    rw [basis_apply_of_eq_smul h, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one,
      basis_unit_repr_smul]
  conv_lhs => rw [hτ]
  simp [mul_comm]

end ZTensorPower

/-! ### Top differential forms of an algebra and of its fraction field -/

section TopForms

variable (k : Type*) [CommRing k] (A : Type*) [CommRing A] [Algebra k A] (K : Type*) [CommRing K]
  [Algebra k K] [Algebra A K] [IsScalarTower k A K] (d : ℕ)

/-- The map `Ω^d_{A/k} ⟶ Ω^d_{K/k}` induced by an algebra map `A ⟶ K` over `k`, on
`d`-th exterior powers of Kähler differentials: `da₁ ∧ ⋯ ∧ da_d ↦ da₁ ∧ ⋯ ∧ da_d`. -/
def topFormsMap : ⋀[A]^d Ω[A⁄k] →ₗ[A] ⋀[K]^d Ω[K⁄k] :=
  exteriorPower.alternatingMapLinearEquiv
    (({ ((exteriorPower.ιMulti K d (M := Ω[K⁄k])).toMultilinearMap.restrictScalars A) with
        map_eq_zero_of_eq' := fun v _ _ h hij =>
          (exteriorPower.ιMulti K d (M := Ω[K⁄k])).map_eq_zero_of_eq v h hij } :
        Ω[K⁄k] [⋀^Fin d]→ₗ[A] ⋀[K]^d Ω[K⁄k]).compLinearMap (KaehlerDifferential.map k k A K))

variable {k A K d}

/-- `topFormsMap` sends `v₁ ∧ ⋯ ∧ v_d` to the wedge of the images of the `vᵢ` in `Ω_{K/k}`. -/
@[simp]
theorem topFormsMap_ιMulti (v : Fin d → Ω[A⁄k]) :
    topFormsMap k A K d (exteriorPower.ιMulti A d v) =
      exteriorPower.ιMulti K d (fun i => KaehlerDifferential.map k k A K (v i)) := by
  simp [topFormsMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

variable (k A K d) in
/-- If `K` is a localization of `A`, the image of `Ω^d_{A/k}` spans `Ω^d_{K/k}` over `K`. -/
theorem span_range_topFormsMap (M : Submonoid A) [IsLocalization M K] :
    Submodule.span K (Set.range (topFormsMap k A K d)) = ⊤ := by
  have hs := KaehlerDifferential.span_range_map_derivation_of_isLocalization k A K M
  refine eq_top_iff.mpr ((exteriorPower.ιMulti_span_of_span K d (M := Ω[K⁄k]) hs).symm.le.trans
    (Submodule.span_mono ?_))
  rintro - ⟨a, ha, rfl⟩
  have : ∀ i, ∃ x : A, KaehlerDifferential.map k k A K (KaehlerDifferential.D k A x) = a i :=
    fun i => by simpa using ha (Set.mem_range_self i)
  choose x hx using this
  exact ⟨exteriorPower.ιMulti A d (fun i => KaehlerDifferential.D k A (x i)), by
    simp [topFormsMap_ιMulti, hx]⟩

/-- If `σ` generates `Ω^d_{A/k}` and `K` is a localization of `A`, its image generates
`Ω^d_{K/k}`. -/
theorem span_singleton_topFormsMap (M : Submonoid A) [IsLocalization M K]
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤) :
    Submodule.span K {topFormsMap k A K d σ} = ⊤ := by
  refine eq_top_iff.mpr ((span_range_topFormsMap k A K d M).symm.le.trans ?_)
  rw [Submodule.span_le]
  rintro - ⟨y, rfl⟩
  have hy : y ∈ Submodule.span A {σ} := hσ ▸ Submodule.mem_top
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [map_smul, ← algebraMap_smul K]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

variable (A) in
/-- A generator `σ` of `Ω^d_{A/k}` whose image in `Ω^d_{K/k}` is nonzero gives a basis of the line
`Ω^d_{K/k}`, for `K` the fraction field of `A`. -/
def topFormsBasis {K : Type*} [Field K] [Algebra k K] [Algebra A K] [IsScalarTower k A K]
    [IsFractionRing A K] {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : topFormsMap k A K d σ ≠ 0) : Module.Basis Unit K (⋀[K]^d Ω[K⁄k]) :=
  basisOfSpanSingleton (span_singleton_topFormsMap (nonZeroDivisors A) hσ) h0

/-- The basis vector of `topFormsBasis A hσ h0` is the image of `σ` in `Ω^d_{K/k}`. -/
@[simp]
theorem topFormsBasis_apply {K : Type*} [Field K] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] [IsFractionRing A K] {σ : ⋀[A]^d Ω[A⁄k]}
    (hσ : Submodule.span A {σ} = ⊤) (h0 : topFormsMap k A K d σ ≠ 0) (i : Unit) :
    topFormsBasis A hσ h0 i = topFormsMap k A K d σ :=
  basisOfSpanSingleton_apply _ _ _

end TopForms

/-- For a unit `a` of `A`, `(a ^ m)⁻¹` in `K` is the image of the unit `a ^ (-m)`. -/
theorem inv_zpow_algebraMap_eq {A K : Type*} [CommRing A] [Field K] [Algebra A K] {a : A}
    (ha : IsUnit a) (m : ℤ) : (algebraMap A K a ^ m)⁻¹ = algebraMap A K ↑(ha.unit ^ (-m)) := by
  have hw : ((Units.map (algebraMap A K : A →* K) ha.unit : Kˣ) : K) = algebraMap A K a := by
    simp
  rw [← zpow_neg, ← hw, ← Units.val_zpow_eq_zpow_val, ← map_zpow, Units.coe_map]
  rfl

/-! ### Rational pluricanonical forms of a field and their order along a local ring -/

section PluriForms

variable (k : Type*) [CommRing k] (K : Type*) [Field K] [Algebra k K] (d : ℕ) (m : ℤ)

/-- The space of *rational `m`-canonical forms* `ω_K^{⊗m} = (Ω^d_{K/k})^{⊗m}` of a field `K` over
`k`, for `m ∈ ℤ`: the `m`-th tensor power of the top differential forms `Ω^d_{K/k}` for `m ≥ 0`,
and the `(-m)`-th tensor power of its dual for `m < 0`. -/
abbrev PluriForms : Type _ := ZTensorPower K (⋀[K]^d Ω[K⁄k]) m

variable {k K d m} (A : Type*) [CommRing A] [Algebra k A] [Algebra A K] [IsScalarTower k A K]
  [IsFractionRing A K]

/-- The coordinate `τ / σ^{⊗m} ∈ K` of an `m`-canonical form `τ` along the `m`-th power of a
generator `σ` of `Ω^d_{A/k}`. -/
def formCoeff {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : topFormsMap k A K d σ ≠ 0) (τ : PluriForms k K d m) : K :=
  (ZTensorPower.basis (topFormsBasis A hσ h0) m).repr τ ()

variable {A}

/-- A form `τ` is its coordinate `τ / σ^{⊗m}` times `σ^{⊗m}`. -/
theorem formCoeff_smul_basis {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : topFormsMap k A K d σ ≠ 0) (τ : PluriForms k K d m) :
    formCoeff A hσ h0 τ • ZTensorPower.basis (topFormsBasis A hσ h0) m () = τ :=
  basis_unit_repr_smul _ τ

/-- The coordinate along `σ^{⊗m}` is additive. -/
@[simp]
theorem formCoeff_add {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : topFormsMap k A K d σ ≠ 0) (τ τ' : PluriForms k K d m) :
    formCoeff A hσ h0 (τ + τ') = formCoeff A hσ h0 τ + formCoeff A hσ h0 τ' := by
  simp [formCoeff]

/-- The coordinate of `-τ` along `σ^{⊗m}` is minus that of `τ`. -/
@[simp]
theorem formCoeff_neg {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : topFormsMap k A K d σ ≠ 0) (τ : PluriForms k K d m) :
    formCoeff A hσ h0 (-τ) = -formCoeff A hσ h0 τ := by
  simp [formCoeff]

/-- The coordinate of `f • τ` along `σ^{⊗m}` is `f` times that of `τ`. -/
@[simp]
theorem formCoeff_smul {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : topFormsMap k A K d σ ≠ 0) (f : K) (τ : PluriForms k K d m) :
    formCoeff A hσ h0 (f • τ) = f * formCoeff A hσ h0 τ := by
  simp [formCoeff]

/-- The coordinate of `τ` along `σ^{⊗m}` vanishes if and only if `τ = 0`. -/
@[simp]
theorem formCoeff_eq_zero_iff {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (h0 : topFormsMap k A K d σ ≠ 0) (τ : PluriForms k K d m) :
    formCoeff A hσ h0 τ = 0 ↔ τ = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h, formCoeff]⟩
  rw [← formCoeff_smul_basis hσ h0 τ, h, zero_smul]

/-- Two generators `σ, σ'` of `Ω^d_{A/k}` with nonzero images differ by a unit `a` of `A`. -/
theorem exists_isUnit_of_span_eq_top {σ σ' : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤)
    (hσ' : Submodule.span A {σ'} = ⊤) (h0 : topFormsMap k A K d σ ≠ 0) :
    ∃ a : A, IsUnit a ∧ a • σ = σ' := by
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top (x := σ'))
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hσ' ▸ Submodule.mem_top (x := σ))
  have hab : algebraMap A K (b * a) = algebraMap A K 1 := by
    have : algebraMap A K (b * a) • topFormsMap k A K d σ =
        algebraMap A K 1 • topFormsMap k A K d σ := by
      rw [algebraMap_smul, algebraMap_smul, ← map_smul, mul_smul, ha, hb, one_smul]
    exact smul_left_injective K h0 this
  have hba : b * a = 1 := IsFractionRing.injective A K hab
  exact ⟨a, isUnit_iff_exists_inv'.mpr ⟨b, hba⟩, ha⟩

variable (A) (v : K → ℤ)

open Classical in
/-- The *order* of an `m`-canonical form `τ` along a local ring `A ⊆ K` with fraction field `K`
and valuation `v`: `v(τ / σ^{⊗m})`, for `σ` a generator of `Ω^d_{A/k}` (whose image in
`Ω^d_{K/k}` is nonzero). By `MMP.Mori.ordAt_eq` it does not depend on the generator. When
`Ω^d_{A/k}` has no such generator it takes the value `0`. -/
def ordAt (τ : PluriForms k K d m) : ℤ :=
  if h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0 then
    v (formCoeff A h.choose_spec.1 h.choose_spec.2 τ)
  else 0

variable {A v}

/-- The order `v(τ / σ^{⊗m})` does not depend on the generator `σ` of `Ω^d_{A/k}`, for `v`
multiplicative on `K^×` and trivial on the units of `A`. -/
theorem ordAt_eq (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0) {σ : ⋀[A]^d Ω[A⁄k]}
    (hσ : Submodule.span A {σ} = ⊤) (h0 : topFormsMap k A K d σ ≠ 0)
    (τ : PluriForms k K d m) : ordAt A v τ = v (formCoeff A hσ h0 τ) := by
  have h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0 :=
    ⟨σ, hσ, h0⟩
  rw [ordAt, dite_eq_left h]
  obtain ⟨a, ha, haσ⟩ := exists_isUnit_of_span_eq_top hσ h.choose_spec.1 h0
  have hbasis : topFormsBasis A h.choose_spec.1 h.choose_spec.2 () =
      algebraMap A K a • topFormsBasis A hσ h0 () := by
    simp only [topFormsBasis_apply, ← haσ, map_smul, algebraMap_smul]
  rw [formCoeff, formCoeff, ZTensorPower.basis_repr_of_eq_smul hbasis]
  set r := (ZTensorPower.basis (topFormsBasis A hσ h0) m).repr τ ()
  by_cases hr : r = 0
  · rw [hr, mul_zero]
  have hc : algebraMap A K a ≠ 0 := fun hz => by
    have : algebraMap A K a • topFormsBasis A hσ h0 () = 0 := by rw [hz, zero_smul]
    exact (topFormsBasis A h.choose_spec.1 h.choose_spec.2).ne_zero () (hbasis.trans this)
  rw [hmul _ _ (inv_ne_zero (zpow_ne_zero m hc)) hr, inv_zpow_algebraMap_eq ha m,
    hunit _ (Units.isUnit _), zero_add]

/-- The order is unchanged by `τ ↦ -τ`. -/
theorem ordAt_neg (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0) (τ : PluriForms k K d m) :
    ordAt A v (-τ) = ordAt A v τ := by
  by_cases h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  · obtain ⟨σ, hσ, h0⟩ := h
    rw [ordAt_eq hmul hunit hσ h0, ordAt_eq hmul hunit hσ h0, formCoeff_neg]
    by_cases hr : formCoeff A hσ h0 τ = 0
    · rw [hr, neg_zero]
    have h1 : v (-1) = 0 := by simpa using hunit (-1) isUnit_one.neg
    rw [neg_eq_neg_one_mul, hmul _ _ (neg_ne_zero.mpr one_ne_zero) hr, h1, zero_add]
  · simp [ordAt, h]

/-- The order of a sum is at least the minimum of the orders, for `v` satisfying the
ultrametric inequality. -/
theorem min_ordAt_le_ordAt_add (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hadd : ∀ x y : K, x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)) {τ τ' : PluriForms k K d m}
    (hττ' : τ + τ' ≠ 0) : min (ordAt A v τ) (ordAt A v τ') ≤ ordAt A v (τ + τ') := by
  by_cases h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  · obtain ⟨σ, hσ, h0⟩ := h
    simp only [ordAt_eq hmul hunit hσ h0, formCoeff_add]
    refine hadd _ _ ?_
    rwa [← formCoeff_add, Ne, formCoeff_eq_zero_iff]
  · simp [ordAt, h]

/-- The order of the zero form is `0` when `v 0 = 0`. -/
theorem ordAt_zero (hv : v 0 = 0) : ordAt A v (0 : PluriForms k K d m) = 0 := by
  classical
  unfold ordAt
  split_ifs with h
  · rw [(formCoeff_eq_zero_iff h.choose_spec.1 h.choose_spec.2 _).mpr rfl, hv]
  · rfl

/-- The order of `f • τ` is `v(f)` plus the order of `τ`, when `Ω^d_{A/k}` has a generator. -/
theorem ordAt_smul (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0)
    {f : K} (hf : f ≠ 0) {τ : PluriForms k K d m} (hτ : τ ≠ 0) :
    ordAt A v (f • τ) = v f + ordAt A v τ := by
  obtain ⟨σ, hσ, h0⟩ := h
  rw [ordAt_eq hmul hunit hσ h0, ordAt_eq hmul hunit hσ h0, formCoeff_smul,
    hmul _ _ hf (by rwa [Ne, formCoeff_eq_zero_iff])]

end PluriForms

/-! ### Pull-back of forms along an extension of fields -/

section Pullback

variable {k : Type*} [CommRing k] {K K' : Type*} [Field K] [Field K'] [Algebra k K]
  [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}

variable (K') in
/-- A generator `ω` of `Ω^d_{K/k}` whose image `u^*ω` generates `Ω^d_{K'/k}`, that is, along
which `u^* : Ω^d_{K/k} ⊗_K K' → Ω^d_{K'/k}` is an isomorphism of lines. -/
def IsPullbackGenerator (ω : ⋀[K]^d Ω[K⁄k]) : Prop :=
  Submodule.span K {ω} = ⊤ ∧ Submodule.span K' {topFormsMap k K K' d ω} = ⊤ ∧
    topFormsMap k K K' d ω ≠ 0

/-- A pull-back generator is nonzero. -/
theorem IsPullbackGenerator.ne_zero {ω : ⋀[K]^d Ω[K⁄k]} (h : IsPullbackGenerator K' ω) :
    ω ≠ 0 := fun h0 => h.2.2 (by rw [h0, map_zero])

/-- The pull-back `u^*(τ) = u(τ/ω^{⊗m}) · (u^*ω)^{⊗m}` of an `m`-canonical form along a pull-back
generator `ω`. -/
def pullbackFormsAlong {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) (m : ℤ)
    (τ : PluriForms k K d m) : PluriForms k K' d m :=
  algebraMap K K' ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) •
    ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) m ()

/-- The pull-back along a pull-back generator does not depend on the generator. -/
theorem pullbackFormsAlong_eq {ω ω' : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω)
    (hω' : IsPullbackGenerator K' ω') (m : ℤ) (τ : PluriForms k K d m) :
    pullbackFormsAlong hω' m τ = pullbackFormsAlong hω m τ := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hω.1 ▸ Submodule.mem_top (x := ω'))
  have hc : c ≠ 0 := by
    rintro rfl
    exact hω'.ne_zero (zero_smul _ _)
  have h1 : basisOfSpanSingleton hω'.1 hω'.ne_zero () =
      c • basisOfSpanSingleton hω.1 hω.ne_zero () := by simp
  have h2 : basisOfSpanSingleton hω'.2.1 hω'.2.2 () =
      algebraMap K K' c • basisOfSpanSingleton hω.2.1 hω.2.2 () := by
    simp [map_smul, algebraMap_smul]
  rw [pullbackFormsAlong, pullbackFormsAlong, ZTensorPower.basis_repr_of_eq_smul h1,
    ZTensorPower.basis_apply_of_eq_smul h2, smul_smul, map_mul, map_inv₀, map_zpow₀, mul_comm,
    ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero m ((map_ne_zero _).mpr hc)), one_mul]

open Classical in
/-- The *pull-back* `u^* : ω^{⊗m}_K → ω^{⊗m}_{K'}` of rational `m`-canonical forms along an
extension `u : K → K'` over `k` (for a dominant morphism of varieties of the same dimension,
`K = k(X)`, `K' = k(X')`), induced by `u^* : Ω^d_{K/k} → Ω^d_{K'/k}`: if `ω` generates
`Ω^d_{K/k}` and `u^*ω` generates `Ω^d_{K'/k}`, then `u^*(f · ω^{⊗m}) = u(f) · (u^*ω)^{⊗m}`
(`MMP.Mori.pullbackForms_eq`). It is `0` if `u^*` is not an isomorphism of lines. -/
@[mmp "def_km2a_rational_pluricanonical_forms"]
def pullbackForms (m : ℤ) (τ : PluriForms k K d m) : PluriForms k K' d m :=
  if h : ∃ ω : ⋀[K]^d Ω[K⁄k], IsPullbackGenerator K' ω then
    pullbackFormsAlong h.choose_spec m τ
  else 0

/-- For any pull-back generator `ω`, `u^*(f · ω^{⊗m}) = u(f) · (u^*ω)^{⊗m}`. -/
theorem pullbackForms_eq {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) (m : ℤ)
    (τ : PluriForms k K d m) : pullbackForms (K' := K') m τ = pullbackFormsAlong hω m τ := by
  rw [pullbackForms, dite_eq_left ⟨ω, hω⟩, pullbackFormsAlong_eq hω]

end Pullback

/-! ### Lattices of top forms of a localization of a finitely generated algebra -/

section Lattice

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {d : ℕ}

/-- If `s` generates `B` as a `k`-algebra, the differentials `ds`, `s ∈ s`, span `Ω_{B/k}`. -/
theorem span_range_D_of_adjoin_eq_top {s : Finset B} (hs : Algebra.adjoin k (s : Set B) = ⊤) :
    Submodule.span B (Set.range fun x : s => KaehlerDifferential.D k B x) = ⊤ := by
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
  | algebraMap r => simp
  | add x y _ _ hx hy =>
    rw [SetLike.mem_coe, map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [SetLike.mem_coe, Derivation.leibniz]
    exact add_mem (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ hx)

variable (R : Type*) [CommRing R] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

variable (k) in
/-- The top forms `ds_{I(1)} ∧ ⋯ ∧ ds_{I(d)}` in `Ω^d_{R/k}`, for `I : Fin d → s` and a `B`-algebra
`R`. -/
def topFormsFamily (s : Finset B) (d : ℕ) (I : Fin d → s) : ⋀[R]^d Ω[R⁄k] :=
  exteriorPower.ιMulti R d fun i =>
    KaehlerDifferential.map k k B R (KaehlerDifferential.D k B (I i))

/-- If `s` generates `B` over `k` and `R` is a localization of `B`, the forms
`ds_{I(1)} ∧ ⋯ ∧ ds_{I(d)}` span `Ω^d_{R/k}` over `R`. -/
theorem span_range_topFormsFamily (M : Submonoid B) [IsLocalization M R] {s : Finset B}
    (hs : Algebra.adjoin k (s : Set B) = ⊤) :
    Submodule.span R (Set.range (topFormsFamily k R s d)) = ⊤ := by
  have hΩ := span_eq_top_of_isLocalizedModule R M (KaehlerDifferential.map k k B R)
    (span_range_D_of_adjoin_eq_top hs)
  refine eq_top_iff.mpr ((exteriorPower.ιMulti_span_of_span R d (M := Ω[R⁄k]) hΩ).symm.le.trans
    (Submodule.span_mono ?_))
  rintro - ⟨a, ha, rfl⟩
  have : ∀ i, ∃ x : s, KaehlerDifferential.map k k B R (KaehlerDifferential.D k B x) = a i :=
    fun i => by
      obtain ⟨_, ⟨x, rfl⟩, hx⟩ := ha (Set.mem_range_self i)
      exact ⟨x, hx⟩
  choose I hI using this
  exact ⟨I, by simp only [topFormsFamily, hI]⟩

variable {R}

/-- `topFormsMap` sends the form `ds_{I(1)} ∧ ⋯ ∧ ds_{I(d)}` of `A` to the same form of `K`. -/
theorem topFormsMap_topFormsFamily {A K : Type*} [CommRing A] [CommRing K] [Algebra k A]
    [Algebra B A] [IsScalarTower k B A] [Algebra k K] [Algebra A K] [Algebra B K]
    [IsScalarTower k A K] [IsScalarTower k B K] [IsScalarTower B A K] (s : Finset B)
    (I : Fin d → s) :
    topFormsMap k A K d (topFormsFamily k A s d I) = topFormsFamily k K s d I := by
  simp only [topFormsFamily, topFormsMap_ιMulti, KaehlerDifferential.map_D,
    ← IsScalarTower.algebraMap_apply]

/-- **The order of a form vanishes where everything is regular.** Let `s` generate `B` over `k`,
`A` be a localization of `B` with fraction field `K`, and `b` a basis of the line `Ω^d_{K/k}`.
If the coordinates of the forms `ds_{I(1)} ∧ ⋯ ∧ ds_{I(d)}` along `b`, the coefficients of an
expression of `b` in these forms, and the coordinate of `τ` along `b^{⊗m}` (a unit) all come from
`A`, then the order of `τ` along `A` is `0`. -/
theorem ordAt_eq_zero_of_forall_mem_range {A K : Type*} [CommRing A] [Field K] [Algebra k A]
    [Algebra B A] [IsScalarTower k B A] [Algebra k K] [Algebra A K] [Algebra B K]
    [IsScalarTower k A K] [IsScalarTower k B K] [IsScalarTower B A K] [IsFractionRing A K]
    (M : Submonoid B) [IsLocalization M A] {s : Finset B}
    (hs : Algebra.adjoin k (s : Set B) = ⊤) {m : ℤ} {v : K → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) (l : (Fin d → s) → K)
    (hl : ∑ I, l I • topFormsFamily k K s d I = b ())
    (hc : ∀ I, b.repr (topFormsFamily k K s d I) () ∈ Set.range (algebraMap A K))
    (hl' : ∀ I, l I ∈ Set.range (algebraMap A K)) (τ : PluriForms k K d m)
    (hg : ∃ a : A, IsUnit a ∧ algebraMap A K a = (ZTensorPower.basis b m).repr τ ()) :
    ordAt A v τ = 0 := by
  classical
  by_cases hgen : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  swap
  · simp [ordAt, hgen]
  obtain ⟨σ, hσ, h0⟩ := hgen
  rw [ordAt_eq hmul hunit hσ h0]
  have h1 : ∀ y : ⋀[A]^d Ω[A⁄k], ∃ a : A, topFormsMap k A K d y = algebraMap A K a • b () := by
    intro y
    have hy : y ∈ Submodule.span A (Set.range (topFormsFamily k A s d)) :=
      (span_range_topFormsFamily A M hs) ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨I, rfl⟩ := hy
      obtain ⟨a, ha⟩ := hc I
      exact ⟨a, by rw [topFormsMap_topFormsFamily, ha, basis_unit_repr_smul]⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨a', ha'⟩ := hy
      exact ⟨a + a', by rw [map_add, ha, ha', ← add_smul, ← map_add]⟩
    | smul r x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨r * a, by rw [map_smul, ha, ← algebraMap_smul K r, smul_smul, ← map_mul]⟩
  have h2 : ∃ a' : A, b () = algebraMap A K a' • topFormsMap k A K d σ := by
    have hα : ∀ I, ∃ α : A, α • σ = topFormsFamily k A s d I :=
      fun I => Submodule.mem_span_singleton.mp (hσ ▸ Submodule.mem_top)
    choose α hα using hα
    choose l₀ hl₀ using hl'
    refine ⟨∑ I, l₀ I * α I, ?_⟩
    rw [← hl, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [← topFormsMap_topFormsFamily (A := A), ← hα I, map_smul, map_mul, mul_smul, hl₀ I,
      algebraMap_smul]
  obtain ⟨a, ha⟩ := h1 σ
  obtain ⟨a', ha'⟩ := h2
  have haa' : a * a' = 1 := by
    have : algebraMap A K (a * a') • topFormsMap k A K d σ =
        algebraMap A K 1 • topFormsMap k A K d σ := by
      rw [map_mul, mul_smul, ← ha', ← ha, map_one, one_smul]
    exact IsFractionRing.injective A K (smul_left_injective K h0 this)
  have hunit_a : IsUnit a := isUnit_iff_exists_inv.mpr ⟨a', haa'⟩
  have hb : topFormsBasis A hσ h0 () = algebraMap A K a • b () := by
    rw [topFormsBasis_apply, ha]
  rw [formCoeff, ZTensorPower.basis_repr_of_eq_smul hb]
  obtain ⟨g, hgu, hg⟩ := hg
  rw [← hg, inv_zpow_algebraMap_eq hunit_a, ← map_mul, hunit _ ((Units.isUnit _).mul hgu)]

end Lattice

/-! ### Rational pluricanonical forms on a variety -/

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The `k`-algebra structure of the local ring `𝒪_{X,x}` of a scheme over `k`. -/
@[instance_reducible]
def stalkAlgebra (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x (Opens.mem_top _)).hom.toAlgebra

/-- The `k`-algebra structure of the function field `k(X)` of an integral scheme over `k`. -/
@[instance_reducible]
def functionFieldAlgebra [IsIntegral X] : Algebra k X.functionField :=
  stalkAlgebra sX (genericPoint X)

/-- The `k`-algebra structures of `𝒪_{X,x}` and `k(X)` are compatible with `𝒪_{X,x} → k(X)`. -/
theorem isScalarTower_stalk_functionField [IsIntegral X] (x : X) :
    letI := stalkAlgebra sX x
    letI := functionFieldAlgebra sX
    IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  let := stalkAlgebra sX x
  let := functionFieldAlgebra sX
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) (Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x (Opens.mem_top _)) ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
    simp
  exact congrArg CommRingCat.Hom.hom h

/-- The `k`-algebra structure of the sections `Γ(X, U)` of a scheme over `k`. -/
@[instance_reducible]
def sectionAlgebra (U : X.Opens) : Algebra k Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U (by simp)).hom.toAlgebra

/-- The `k`-algebra structures of `Γ(X, U)` and `𝒪_{X,x}`, for `x ∈ U`, are compatible with the
germ map `Γ(X, U) → 𝒪_{X,x}`. -/
theorem isScalarTower_section_stalk (U : X.Opens) (x : U) :
    letI := sectionAlgebra sX U
    letI := stalkAlgebra sX x
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by
  let := sectionAlgebra sX U
  let := stalkAlgebra sX x
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.presheaf.germ ⊤ x (Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U (by simp)) ≫ X.presheaf.germ U x x.2 := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  exact congrArg CommRingCat.Hom.hom h

/-- The `k`-algebra structures of `Γ(X, U)`, for `U` nonempty, and `k(X)` are compatible with
`Γ(X, U) → k(X)`. -/
theorem isScalarTower_section_functionField [IsIntegral X] (U : X.Opens) [Nonempty U] :
    letI := sectionAlgebra sX U
    letI := functionFieldAlgebra sX
    IsScalarTower k Γ(X, U) X.functionField := by
  let := sectionAlgebra sX U
  let := functionFieldAlgebra sX
  refine IsScalarTower.of_algebraMap_eq' ?_
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) (Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U (by simp)) ≫ X.germToFunctionField U := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, Category.assoc, Scheme.germToFunctionField,
      TopCat.Presheaf.germ_res]
    rfl
  exact congrArg CommRingCat.Hom.hom h

/-- On an affine open `U` of a scheme locally of finite type over `k`, `Γ(X, U)` is a finitely
generated `k`-algebra. -/
theorem finiteType_sectionAlgebra [LocallyOfFiniteType sX] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionAlgebra sX U
    Algebra.FiniteType k Γ(X, U) := by
  let := sectionAlgebra sX U
  change RingHom.FiniteType ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ U (by simp)).hom
  rw [CommRingCat.hom_comp]
  exact (HasRingHomProperty.appLE @LocallyOfFiniteType sX ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
    _).comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv.surjective)

/-- Every element of the function field lies in the local ring `𝒪_{X,x}` for all `x` near the
generic point. -/
theorem eventually_mem_range_algebraMap_stalk [IsIntegral X] (f : X.functionField) :
    ∀ᶠ x in 𝓝 (genericPoint X),
      f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  obtain ⟨V, hV, g, hg⟩ := X.presheaf.exists_germ_eq f
  have : Nonempty V := ⟨⟨_, hV⟩⟩
  filter_upwards [V.isOpen.mem_nhds hV] with x hx
  exact ⟨X.presheaf.germ V x hx g,
    (Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hx g).trans hg⟩

variable [IsIntegral X]

/-- The space of *rational `m`-canonical forms* `ω^{⊗m}_{k(X)} = (Ω^d_{k(X)/k})^{⊗m}` of an
integral scheme `X` over `k` (a variety of dimension `d`), for `m ∈ ℤ`: for `m < 0`, the
`(-m)`-th tensor power of the dual of `Ω^d_{k(X)/k}`. -/
@[mmp "def_km2a_rational_pluricanonical_forms"]
def RationalPluriForms (d : ℕ) (m : ℤ) : Type u :=
  @PluriForms k _ X.functionField _ (functionFieldAlgebra sX) d m

/-- The abelian group structure of `ω^{⊗m}_{k(X)}`. -/
instance (d : ℕ) (m : ℤ) : AddCommGroup (RationalPluriForms sX d m) := by
  unfold RationalPluriForms
  infer_instance

/-- The `k(X)`-vector space structure of `ω^{⊗m}_{k(X)}`. -/
instance (d : ℕ) (m : ℤ) : Module X.functionField (RationalPluriForms sX d m) := by
  unfold RationalPluriForms
  infer_instance

variable {sX} [IsLocallyNoetherian X] {d : ℕ} {m : ℤ}

namespace PrimeDivisor

/-- The *order* `ord_Γ(τ)` of a rational `m`-canonical form `τ` along a prime divisor `Γ`: the
order `v_Γ(τ / σ^{⊗m})` in the discrete valuation ring `𝒪_{X,Γ}`, where `σ` generates
`Ω^d_{X,Γ} = Ω^d_{𝒪_{X,Γ}/k}`. It does not depend on `σ` (`MMP.Mori.PrimeDivisor.ordForm_eq`). -/
@[mmp "def_km2a_divisor_of_form"]
def ordForm (Γ : PrimeDivisor X) (τ : RationalPluriForms sX d m) : ℤ :=
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  ordAt (k := k) Γ.localRing (fun f => X.ord f Γ.genericPoint) τ

/-- The order along `Γ` of a unit of `𝒪_{X,Γ}` is `0`. -/
theorem ord_algebraMap_of_isUnit (Γ : PrimeDivisor X) {a : Γ.localRing} (ha : IsUnit a) :
    X.ord (algebraMap Γ.localRing X.functionField a) Γ.genericPoint = 0 := by
  have hz := Γ.coheight_genericPoint
  have hne : algebraMap Γ.localRing X.functionField a ≠ 0 := (ha.map _).ne_zero
  rw [Scheme.ord_eq_iff hz hne, ofAdd_zero]
  have : Ring.KrullDimLE 1 Γ.localRing := krullDimLE_of_coheight_le hz.le
  exact Ring.ordFrac_of_isUnit ha

/-- The order along `Γ` is additive on nonzero rational functions. -/
theorem ord_mul_of_ne_zero (Γ : PrimeDivisor X) (f g : X.functionField) (hf : f ≠ 0)
    (hg : g ≠ 0) : X.ord (f * g) Γ.genericPoint =
      X.ord f Γ.genericPoint + X.ord g Γ.genericPoint :=
  Scheme.ord_mul hf hg

/-- **The order of a form does not depend on the generator.** For any generator `σ` of
`Ω^d_{𝒪_{X,Γ}/k}` with nonzero image in `Ω^d_{k(X)/k}`, `ord_Γ(τ) = v_Γ(τ / σ^{⊗m})`. -/
@[mmp "def_km2a_divisor_of_form"]
theorem ordForm_eq (Γ : PrimeDivisor X) (τ : RationalPluriForms sX d m) :
    letI := stalkAlgebra sX Γ.genericPoint
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
    ∀ {σ : ⋀[Γ.localRing]^d Ω[Γ.localRing⁄k]} (hσ : Submodule.span Γ.localRing {σ} = ⊤)
      (h0 : topFormsMap k Γ.localRing X.functionField d σ ≠ 0),
      Γ.ordForm τ = X.ord (formCoeff (k := k) Γ.localRing hσ h0 τ) Γ.genericPoint := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  intro σ hσ h0
  exact ordAt_eq (Γ.ord_mul_of_ne_zero) (fun _ ha => Γ.ord_algebraMap_of_isUnit ha) hσ h0 τ

/-- `ord_Γ(-τ) = ord_Γ(τ)`. -/
@[simp]
theorem ordForm_neg (Γ : PrimeDivisor X) (τ : RationalPluriForms sX d m) :
    Γ.ordForm (-τ) = Γ.ordForm τ := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact ordAt_neg (k := k) (Γ.ord_mul_of_ne_zero) (fun _ ha => Γ.ord_algebraMap_of_isUnit ha) τ

/-- On a normal scheme, `min(ord_Γ(τ), ord_Γ(τ')) ≤ ord_Γ(τ + τ')` when `τ + τ' ≠ 0`. -/
theorem min_ordForm_le_ordForm_add [IsNormal X] (Γ : PrimeDivisor X)
    {τ τ' : RationalPluriForms sX d m} (h : τ + τ' ≠ 0) :
    min (Γ.ordForm τ) (Γ.ordForm τ') ≤ Γ.ordForm (τ + τ') := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have := Γ.isDiscreteValuationRing_localRing
  exact min_ordAt_le_ordAt_add (k := k) (Γ.ord_mul_of_ne_zero)
    (fun _ ha => Γ.ord_algebraMap_of_isUnit ha) (fun _ _ hxy => Scheme.ord_add hxy) h

/-- The order of the zero form along any prime divisor is `0`. -/
@[simp]
theorem ordForm_zero (Γ : PrimeDivisor X) :
    Γ.ordForm (0 : RationalPluriForms sX d m) = 0 := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact ordAt_zero (k := k) (by simp)

end PrimeDivisor

/-! ### The divisor of a form -/

/-- **The order of a form vanishes where everything is regular.** Let `U` be an affine open
containing the generic point of `Γ`, with `Γ(X, U)` generated over `k` by a finite set `s`, and `b`
a basis of `Ω^d_{k(X)/k}`. If the coordinates of the forms `ds_{I(1)} ∧ ⋯ ∧ ds_{I(d)}` along `b`,
the coefficients of an expression of `b` in these forms, and the coordinate of `τ` along `b^{⊗m}`
and its inverse all come from `𝒪_{X,Γ}`, then `ord_Γ(τ) = 0`. -/
theorem PrimeDivisor.ordForm_eq_zero_of_mem_range (Γ : PrimeDivisor X) {U : X.Opens}
    [Nonempty U] (hU : IsAffineOpen U) (hΓU : Γ.genericPoint ∈ U)
    (τ : RationalPluriForms sX d m) :
    letI := sectionAlgebra sX U
    letI := functionFieldAlgebra sX
    haveI := isScalarTower_section_functionField sX U
    ∀ {s : Finset Γ(X, U)} (_ : Algebra.adjoin k (s : Set Γ(X, U)) = ⊤)
      (b : Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
      (l : (Fin d → s) → X.functionField)
      (_ : ∑ I, l I • topFormsFamily k X.functionField s d I = b ())
      (_ : ∀ I, b.repr (topFormsFamily k X.functionField s d I) () ∈
        Set.range (algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField))
      (_ : ∀ I, l I ∈ Set.range (algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField))
      (_ : (ZTensorPower.basis b m).repr τ () ≠ 0)
      (_ : (ZTensorPower.basis b m).repr τ () ∈
        Set.range (algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField))
      (_ : ((ZTensorPower.basis b m).repr τ ())⁻¹ ∈
        Set.range (algebraMap (X.presheaf.stalk Γ.genericPoint) X.functionField)),
      Γ.ordForm τ = 0 := by
  let := sectionAlgebra sX U
  let := functionFieldAlgebra sX
  have := isScalarTower_section_functionField sX U
  intro s hs b l hl hc hl' hg0 ⟨p, hp⟩ ⟨q, hq⟩
  let x : U := ⟨Γ.genericPoint, hΓU⟩
  let : Algebra Γ(X, U) Γ.localRing := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  let := stalkAlgebra sX Γ.genericPoint
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have := isScalarTower_section_stalk sX U x
  have : IsScalarTower Γ(X, U) Γ.localRing X.functionField := functionField_isScalarTower X U x
  have := hU.isLocalization_stalk x
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have hpq : p * q = 1 := IsFractionRing.injective (X.presheaf.stalk Γ.genericPoint)
    X.functionField (by rw [map_mul, hp, hq, mul_inv_cancel₀ hg0, map_one])
  exact ordAt_eq_zero_of_forall_mem_range (B := Γ(X, U)) (A := Γ.localRing)
    (hU.primeIdealOf x).asIdeal.primeCompl hs Γ.ord_mul_of_ne_zero
    (fun _ ha => Γ.ord_algebraMap_of_isUnit ha) b l hl hc hl' τ
    ⟨p, isUnit_iff_exists_inv.mpr ⟨q, hpq⟩, hp⟩

/-- **Finiteness of the divisor of a form.** On a Noetherian integral scheme locally of finite
type over `k`, a rational `m`-canonical form `τ` has nonzero order along only finitely many prime
divisors. -/
theorem finite_ordForm_ne_zero [CompactSpace X] [LocallyOfFiniteType sX]
    (τ : RationalPluriForms sX d m) : {Γ : PrimeDivisor X | Γ.ordForm τ ≠ 0}.Finite := by
  classical
  let := functionFieldAlgebra sX
  by_cases hτ : τ = 0
  · subst hτ
    simp
  by_cases hb : Nonempty (Module.Basis Unit X.functionField
    (⋀[X.functionField]^d Ω[X.functionField⁄k]))
  swap
  · convert Set.finite_empty
    ext Γ
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    let := stalkAlgebra sX Γ.genericPoint
    have := isScalarTower_stalk_functionField sX Γ.genericPoint
    have : ¬ ∃ σ : ⋀[Γ.localRing]^d Ω[Γ.localRing⁄k], Submodule.span Γ.localRing {σ} = ⊤ ∧
        topFormsMap k Γ.localRing X.functionField d σ ≠ 0 :=
      fun ⟨σ, hσ, h0⟩ => hb ⟨topFormsBasis Γ.localRing hσ h0⟩
    simp only [PrimeDivisor.ordForm, ordAt, dite_eq_right this]
  obtain ⟨b⟩ := hb
  set g := (ZTensorPower.basis b m).repr τ () with hg_def
  have hg0 : g ≠ 0 := by
    intro h
    apply hτ
    rw [← basis_unit_repr_smul (ZTensorPower.basis b m) τ, ← hg_def, h, zero_smul]
    rfl
  obtain ⟨x₀⟩ : Nonempty X := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hx₀U, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x₀) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨x₀, hx₀U⟩⟩
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  let := sectionAlgebra sX U
  have := isScalarTower_section_functionField sX U
  have := finiteType_sectionAlgebra sX hU'
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k Γ(X, U)).FG)
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU'
  have hspan := span_range_topFormsFamily (k := k) (d := d) X.functionField
    (nonZeroDivisors Γ(X, U)) hs
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun X.functionField).mp
    (hspan ▸ Submodule.mem_top : b () ∈ _)
  have hP : ∀ᶠ x in 𝓝 (genericPoint X), x ∈ U ∧
      (∀ I, b.repr (topFormsFamily k X.functionField s d I) () ∈
        Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) ∧
      (∀ I, l I ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField)) ∧
      g ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) ∧
      g⁻¹ ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) :=
    (show ∀ᶠ x in 𝓝 (genericPoint X), x ∈ U from U.isOpen.mem_nhds hηU).and <|
      (Filter.eventually_all.mpr fun _ => eventually_mem_range_algebraMap_stalk _).and <|
      (Filter.eventually_all.mpr fun _ => eventually_mem_range_algebraMap_stalk _).and <|
      (eventually_mem_range_algebraMap_stalk g).and (eventually_mem_range_algebraMap_stalk g⁻¹)
  obtain ⟨t, htP, ht, hηt⟩ := eventually_nhds_iff.mp hP
  let W : X.Opens := ⟨t, ht⟩
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  refine Set.Finite.of_finite_image
    ((finite_coheight_eq_one_mem_closure_notMem (genericPoint X) W hηt).subset ?_)
    AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
  rintro - ⟨Γ, hΓ, rfl⟩
  refine ⟨by rw [(genericPoint_spec X).def]; trivial, fun hmem => hΓ ?_, Γ.coheight_genericPoint⟩
  obtain ⟨hxU, hc, hl', hgx, hginv⟩ := htP _ hmem
  exact PrimeDivisor.ordForm_eq_zero_of_mem_range Γ hU' hxU τ hs b l hl hc hl' hg0 hgx hginv

/-- The *divisor* `div(τ) = ∑_Γ ord_Γ(τ) Γ` of a rational `m`-canonical form `τ` on a Noetherian
integral scheme locally of finite type over `k`, a finite sum by
`MMP.Mori.finite_ordForm_ne_zero`. -/
@[mmp "def_km2a_divisor_of_form"]
def divisorOfForm [CompactSpace X] [LocallyOfFiniteType sX] (τ : RationalPluriForms sX d m) :
    Divisor X :=
  Finsupp.ofSupportFinite (fun Γ => Γ.ordForm τ) (finite_ordForm_ne_zero τ)

/-- The coefficient of `div(τ)` at `Γ` is `ord_Γ(τ)`. -/
@[simp]
theorem coeff_divisorOfForm [CompactSpace X] [LocallyOfFiniteType sX]
    (τ : RationalPluriForms sX d m) (Γ : PrimeDivisor X) :
    (divisorOfForm τ).coeff Γ = Γ.ordForm τ := rfl

/-! ### The sheaves `𝒪_X(mK_X + G)` -/

section Sheaf

variable [IsNormal X] (sX d m) (G : Divisor X)

/-- The sections of `𝒪_X(mK_X + G)` over an open `U`: the rational `m`-canonical forms `τ` with
`ord_Γ(τ) + coeff_Γ(G) ≥ 0` for every prime divisor `Γ` meeting `U` (with `τ = 0` allowed), and
only `0` over `U = ∅`. -/
@[mmp "def_km2a_pluricanonical_sheaf"]
def pluricanonicalSections (U : X.Opens) : AddSubgroup (RationalPluriForms sX d m) where
  carrier := {τ | (U = ⊥ → τ = 0) ∧ ∀ Γ : PrimeDivisor X, (Γ.support ∩ U).Nonempty → τ ≠ 0 →
    0 ≤ Γ.ordForm τ + G.coeff Γ}
  zero_mem' := ⟨fun _ => rfl, fun _ _ h => (h rfl).elim⟩
  add_mem' {a b} ha hb := by
    refine ⟨fun hU => by rw [ha.1 hU, hb.1 hU, add_zero], fun Γ hΓ hab => ?_⟩
    obtain rfl | ha0 := eq_or_ne a 0
    · rw [zero_add] at hab ⊢
      exact hb.2 Γ hΓ hab
    obtain rfl | hb0 := eq_or_ne b 0
    · rw [add_zero] at hab ⊢
      exact ha.2 Γ hΓ hab
    have := Γ.min_ordForm_le_ordForm_add hab
    have h1 := ha.2 Γ hΓ ha0
    have h2 := hb.2 Γ hΓ hb0
    omega
  neg_mem' {a} ha := by
    refine ⟨fun hU => by rw [ha.1 hU, neg_zero], fun Γ hΓ ha' => ?_⟩
    rw [PrimeDivisor.ordForm_neg]
    exact ha.2 Γ hΓ (fun h => ha' (by rw [h, neg_zero]))

variable {sX d m G}

/-- Membership in `𝒪_X(mK_X + G)(U)`: `τ = 0` if `U = ∅`, and the order condition along every
prime divisor meeting `U`. -/
theorem mem_pluricanonicalSections {U : X.Opens} {τ : RationalPluriForms sX d m} :
    τ ∈ pluricanonicalSections sX d m G U ↔ (U = ⊥ → τ = 0) ∧
      ∀ Γ : PrimeDivisor X, (Γ.support ∩ U).Nonempty → τ ≠ 0 → 0 ≤ Γ.ordForm τ + G.coeff Γ :=
  Iff.rfl

/-- On a nonempty open `U`, membership in `𝒪_X(mK_X + G)(U)` is the order condition. -/
theorem mem_pluricanonicalSections_of_ne_bot {U : X.Opens} (hU : U ≠ ⊥)
    {τ : RationalPluriForms sX d m} :
    τ ∈ pluricanonicalSections sX d m G U ↔
      ∀ Γ : PrimeDivisor X, (Γ.support ∩ U).Nonempty → τ ≠ 0 → 0 ≤ Γ.ordForm τ + G.coeff Γ :=
  ⟨fun h => h.2, fun h => ⟨fun h' => (hU h').elim, h⟩⟩

open Classical in
/-- Restriction of sections of `𝒪_X(mK_X + G)` from `U` to `V ⊆ U`: the identity on forms when
`V ≠ ∅`, and zero when `V = ∅`. -/
def pluricanonicalRestrict {U V : X.Opens} (hVU : V ≤ U) :
    pluricanonicalSections sX d m G U →+ pluricanonicalSections sX d m G V where
  toFun τ := ⟨if V = ⊥ then 0 else τ.1, by
    split_ifs with hV
    · exact zero_mem _
    · exact ⟨fun h => (hV h).elim, fun Γ hΓ hτ =>
        τ.2.2 Γ (hΓ.mono (Set.inter_subset_inter_right _ hVU)) hτ⟩⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; split_ifs <;> simp_all

open Classical in
/-- The restriction of `τ` to `V` is `0` if `V = ∅`, and the form `τ` otherwise. -/
theorem coe_pluricanonicalRestrict {U V : X.Opens} (hVU : V ≤ U)
    (τ : pluricanonicalSections sX d m G U) :
    (pluricanonicalRestrict hVU τ : RationalPluriForms sX d m) = if V = ⊥ then 0 else τ.1 := rfl

/-- On a nonempty open `V`, the restriction of `τ` to `V` is the form `τ`. -/
theorem coe_pluricanonicalRestrict_of_ne_bot {U V : X.Opens} (hVU : V ≤ U) (hV : V ≠ ⊥)
    (τ : pluricanonicalSections sX d m G U) :
    (pluricanonicalRestrict hVU τ : RationalPluriForms sX d m) = τ.1 := by
  classical
  rw [coe_pluricanonicalRestrict, ite_eq_right hV]

/-- Every section of `𝒪_X(mK_X + G)` over the empty open set is `0`. -/
theorem coe_eq_zero_of_eq_bot {U : X.Opens} (hU : U = ⊥) (τ : pluricanonicalSections sX d m G U) :
    (τ : RationalPluriForms sX d m) = 0 := τ.2.1 hU

variable (sX d m G)

/-- The presheaf `𝒪_X(mK_X + G)` of abelian groups, a subpresheaf of the constant presheaf of
rational `m`-canonical forms. -/
@[mmp "def_km2a_pluricanonical_sheaf"]
def pluricanonicalPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (pluricanonicalSections sX d m G U.unop)
  map i := AddCommGrpCat.ofHom (pluricanonicalRestrict i.unop.le)
  map_id U := by
    ext τ
    change (pluricanonicalRestrict (le_refl U.unop) τ : RationalPluriForms sX d m) = τ.1
    rw [coe_pluricanonicalRestrict]
    split_ifs with h
    · exact (coe_eq_zero_of_eq_bot h τ).symm
    · rfl
  map_comp {U V W} i j := by
    ext τ
    change (pluricanonicalRestrict (j.unop.le.trans i.unop.le) τ : RationalPluriForms sX d m) =
      (pluricanonicalRestrict j.unop.le (pluricanonicalRestrict i.unop.le τ) : _)
    simp only [coe_pluricanonicalRestrict]
    split_ifs with h1 h2 <;> try rfl
    exact absurd (eq_bot_iff.mpr (h2 ▸ j.unop.le)) h1

variable {sX d m G} in
open Classical in
/-- The restriction maps of `𝒪_X(mK_X + G)` are `0` onto the empty open set and the identity on
forms otherwise. -/
theorem pluricanonicalPresheaf_map_apply {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (τ : ToType ((pluricanonicalPresheaf sX d m G).obj U)) :
    (((pluricanonicalPresheaf sX d m G).map i).hom τ).1 =
      if V.unop = ⊥ then 0 else (τ : pluricanonicalSections sX d m G U.unop).1 :=
  rfl

variable {sX d m G} in
/-- Two sections of `𝒪_X(mK_X + G)` over `V` are equal when their underlying forms are. -/
theorem pluricanonicalPresheaf_ext {V : X.Opens}
    {a b : ToType ((pluricanonicalPresheaf sX d m G).obj (op V))}
    (h : (a : pluricanonicalSections sX d m G V).1 = (b : pluricanonicalSections sX d m G V).1) :
    a = b :=
  Subtype.ext h

/-- The presheaf `𝒪_X(mK_X + G)` is a sheaf. -/
theorem isSheaf_pluricanonicalPresheaf : (pluricanonicalPresheaf sX d m G).IsSheaf := by
  classical
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro ι U sf hsf
  let val : ι → RationalPluriForms sX d m :=
    fun i => (sf i : pluricanonicalSections sX d m G (U i)).1
  have key : ∀ i j, U i ≠ ⊥ → U j ≠ ⊥ → val i = val j := by
    intro i j hi hj
    have hij : U i ⊓ U j ≠ ⊥ := by
      rw [Opens.ne_bot_iff_nonempty] at hi hj ⊢
      exact nonempty_preirreducible_inter (U i).isOpen (U j).isOpen hi hj
    have := congrArg (fun t => (t : pluricanonicalSections sX d m G (U i ⊓ U j)).1) (hsf i j)
    change (if U i ⊓ U j = ⊥ then 0 else val i) = (if U i ⊓ U j = ⊥ then 0 else val j) at this
    rwa [ite_eq_right hij, ite_eq_right hij] at this
  by_cases hex : ∃ i, U i ≠ ⊥
  · obtain ⟨i₀, hi₀⟩ := hex
    have hsup : iSup U ≠ ⊥ := fun h => hi₀ (eq_bot_iff.mpr (h ▸ le_iSup U i₀))
    have hmem : val i₀ ∈ pluricanonicalSections sX d m G (iSup U) := by
      refine (mem_pluricanonicalSections_of_ne_bot hsup).mpr fun Γ hΓ hτ => ?_
      obtain ⟨x, hxΓ, hxU⟩ := hΓ
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hxU
      have hjb : U j ≠ ⊥ := fun h => by
        rw [h] at hj
        exact hj
      rw [key i₀ j hi₀ hjb] at hτ ⊢
      exact (sf j).2.2 Γ ⟨x, hxΓ, hj⟩ hτ
    refine ⟨⟨val i₀, hmem⟩, fun i => ?_, fun t ht => ?_⟩
    · refine pluricanonicalPresheaf_ext ?_
      change (if U i = ⊥ then 0 else val i₀) = val i
      split_ifs with h
      · exact (coe_eq_zero_of_eq_bot h (sf i)).symm
      · exact key i₀ i hi₀ h
    · refine pluricanonicalPresheaf_ext ?_
      have := congrArg (fun t => (t : pluricanonicalSections sX d m G (U i₀)).1) (ht i₀)
      change (if U i₀ = ⊥ then 0 else (t : pluricanonicalSections sX d m G (iSup U)).1) =
        val i₀ at this
      rwa [ite_eq_right hi₀] at this
  · push Not at hex
    have hsup : iSup U = ⊥ := iSup_eq_bot.mpr hex
    refine ⟨0, fun i => ?_, fun t _ => ?_⟩
    · refine pluricanonicalPresheaf_ext ?_
      change (if U i = ⊥ then 0 else (0 : RationalPluriForms sX d m)) = val i
      rw [ite_self]
      exact (coe_eq_zero_of_eq_bot (hex i) (sf i)).symm
    · exact pluricanonicalPresheaf_ext (coe_eq_zero_of_eq_bot hsup _)

/-- The sheaf `𝒪_X(mK_X + G)` of a Weil divisor `G` on a normal variety `X`: the subsheaf of the
constant sheaf `ω^{⊗m}_{k(X)}` of the forms `τ` with `ord_Γ(τ) + coeff_Γ(G) ≥ 0` for every prime
divisor `Γ` meeting the open set. For `G = 0` this is `𝒪_X(mK_X)`. -/
@[mmp "def_km2a_pluricanonical_sheaf"]
def pluricanonicalSheaf : TopCat.Sheaf AddCommGrpCat.{u} X :=
  ⟨pluricanonicalPresheaf sX d m G, isSheaf_pluricanonicalPresheaf sX d m G⟩

end Sheaf

/-! ### Local generators of `𝒪_X(m(K_X + Δ))` -/

/-- A nonzero rational `m`-canonical form `τ` *generates `𝒪_X(m(K_X + Δ))` on `U`*, for a
`ℚ`-divisor `Δ` and `m : ℕ` (in practice `m > 0` with `mΔ` a divisor):
`ord_Γ(τ) + m·coeff_Γ(Δ) = 0` for every prime divisor `Γ` of `X` meeting `U`. -/
@[mmp "def_km2b_local_generator"]
def GeneratesOn (Δ : QDivisor X) (m : ℕ) (U : X.Opens) (τ : RationalPluriForms sX d m) : Prop :=
  τ ≠ 0 ∧ ∀ Γ : PrimeDivisor X, (Γ.support ∩ U).Nonempty →
    (Γ.ordForm τ : ℚ) + m * Δ.coeff Γ = 0

/-- A form generating `𝒪_X(m(K_X + Δ))` on `U` generates it on every open `V ⊆ U`. -/
theorem GeneratesOn.mono {Δ : QDivisor X} {m : ℕ} {U V : X.Opens} {τ : RationalPluriForms sX d m}
    (h : GeneratesOn Δ m U τ) (hVU : V ≤ U) : GeneratesOn Δ m V τ :=
  ⟨h.1, fun Γ ⟨x, hxΓ, hxV⟩ => h.2 Γ ⟨x, hxΓ, hVU hxV⟩⟩

end Scheme

end MMP.Mori
