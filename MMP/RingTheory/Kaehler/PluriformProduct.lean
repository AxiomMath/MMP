module

public import MMP.AlgebraicGeometry.MMP.Fourfold.CrepantPluriform
public import MMP.AlgebraicGeometry.Divisor.Canonical.TopFormGenerator
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual

/-!
# Products of pluriforms and residues of products

Let `K` be a field over `k` and `L = Ω^d_{K/k}`. For natural numbers `a, b` the tensor powers
`L^{⊗a}` and `L^{⊗b}` multiply to `L^{⊗(a+b)}` by concatenation of tensors,
`(ω₁ ⊗ ⋯ ⊗ ω_a) · (ω'₁ ⊗ ⋯ ⊗ ω'_b) = ω₁ ⊗ ⋯ ⊗ ω_a ⊗ ω'₁ ⊗ ⋯ ⊗ ω'_b`. When `L` is a line with
basis `ω`, this is the multiplication `(f ω^{⊗a}) · (g ω^{⊗b}) = (f g) ω^{⊗(a+b)}` of
coefficients. The product is compatible with pull-back along extensions of fields, and on an
integral scheme the order of forms along a prime divisor is additive under it; so the log
pluricanonical sections `H⁰(X, m(K_X + B))`, `m ∈ ℕ`, form a graded ring, local generators
multiply to local generators, and pull-back along birational maps is multiplicative.

Let `T ⊂ Y` be a closed integral subscheme of a normal variety over a perfect field whose
generic point is that of a prime divisor (for instance an adjunction step), `O = 𝒪_{Y,T}` the
discrete valuation ring of `Y` along `T`, with fraction field `k(Y)` and residue field `k(T)`.
Then `Ω_{O/k}` is free, and for a uniformizer `t` the differential `dt` has a retraction
`r(dt) = 1`, since `k(T)` is formally smooth over `k`. Evaluating a logarithmic form
`t⁻¹ dt ∧ dx₁ ∧ ⋯ ∧ dx_e` against `(t r, D₁, …, D_e)`, `D_a` lifts of functionals on
`Ω_{k(T)/k}`, gives an element of `O` reducing to the evaluation of `dx̄₁ ∧ ⋯ ∧ dx̄_e` on the
functionals; these evaluations separate `(⋀^e Ω_{k(T)/k})^{⊗m}`. Hence the Poincaré residue of an
`m`-fold form is unique, and comparing two logarithmic frames (one is an `O`-multiple of the
other) shows it is multiplicative when `dim Y = e + 1`. The conormal sequence gives
`trdeg_k k(T) + 1 = trdeg_k k(Y)`. By induction along a flag, iterated residues are unique and
multiplicative, and a stratum reached by a flag of length `ℓ` has dimension `dim X - ℓ`.

## Main definitions

* `MMP.Fourfold.formPow`: the tensor power `ω^{⊗a}` of a form.
* `MMP.Fourfold.pluriFormsMul`: the product `ω^{⊗a}_K × ω^{⊗b}_K → ω^{⊗(a+b)}_K`.
* `MMP.Fourfold.RationalPluriForms.mul`: the same product for the rational pluriforms of an
  integral scheme.
* `MMP.Fourfold.logPluriForm`, `MMP.Fourfold.logPluriResidue`: `g (t⁻¹ dt ∧ dx)^{⊗m}` and
  `ḡ (dx̄)^{⊗m}`.
* `MMP.Fourfold.IsIteratedResidueRec`: the iterated residue relation unfolded along the flag.

## Main results

* `MMP.Fourfold.pluriFormsMul_smul_formPow`: `(f ω^{⊗a}) · (g ω^{⊗b}) = (f g) ω^{⊗(a+b)}`.
* `MMP.Fourfold.pullbackForms_pluriFormsMul`: pull-back is multiplicative.
* `MMP.Fourfold.ordAt_pluriFormsMul`, `MMP.Fourfold.ordForm_mul`: orders are additive.
* `MMP.Fourfold.mul_mem_logPluricanonicalSections`: `H⁰(a(K + B)) · H⁰(b(K + B)) ⊆
  H⁰((a + b)(K + B))`.
* `MMP.Fourfold.GeneratesOn.mul`: products of local generators are local generators.
* `MMP.Fourfold.pluriformPullback_mul`, `MMP.Fourfold.pluriformPullback_comp`,
  `MMP.Fourfold.pluriformPullback_one`: pluriform pull-back is multiplicative and functorial.
* `MMP.Fourfold.IsCrepantBirationalMap.trans`, `MMP.Fourfold.IsCrepantBirationalMap.symm`.
* `MMP.Fourfold.logPluriResidue_eq_of_logPluriForm_eq`, `MMP.Fourfold.exists_logPluriForm_mul`:
  uniqueness and multiplicativity of residues of logarithmic pluriforms over a discrete
  valuation ring.
* `MMP.Fourfold.IsPoincareResidue.unique_of_isClosedImmersion`,
  `MMP.Fourfold.IsPoincareResidue.mul_of_isClosedImmersion`,
  `MMP.Fourfold.trdeg_add_one_of_eq_genericPoint`: uniqueness and multiplicativity of Poincaré
  residues, and the transcendence degree, along a closed immersion onto a prime divisor.
* `MMP.Fourfold.IsPoincareResidue.unique`, `MMP.Fourfold.IsPoincareResidue.mul`,
  `MMP.Fourfold.IsAdjunctionStep.trdeg_add_one`: the same along an adjunction step.
* `MMP.Fourfold.IsIteratedResidue.unique`, `MMP.Fourfold.IsIteratedResidue.mul`,
  `MMP.Fourfold.StratumAdjunctionData.dim_add_length`.

## Implementation notes

The product is defined for natural degrees, through `TensorPower.mulEquiv`; for a line `L` it is
commutative, but this is not needed here. A form of degree `a` with respect to a basis `b` of the
line `L` is `c • ω^{⊗a}` with `ω = b ()`, the coordinate along `MMP.Mori.ZTensorPower.basis b a`.

Residues are compared through evaluation against derivations rather than through a basis of
`Ω_{O/k}` adapted to the uniformizer: the functionals `D_a` are lifts, by projectivity of
`Ω_{O/k}`, of arbitrary functionals on `Ω_{k(T)/k}`, and separation uses coordinate functionals of
bases of exterior and tensor powers (`Module.Basis.exteriorPower`, `Basis.piTensorProduct`).
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

/-! ### The product of pluriforms of a field -/

section Field

variable {k : Type*} [CommRing k] {K : Type*} [Field K] [Algebra k K] {d : ℕ}

/-- The tensor power `ω^{⊗a}` of a `d`-form `ω`, a rational `a`-canonical form. -/
def formPow (ω : ⋀[K]^d Ω[K⁄k]) (a : ℕ) : PluriForms k K d a :=
  PiTensorProduct.tprod K fun _ : Fin a => ω

variable (k K d) in
/-- **The product of pluriforms** `ω^{⊗a}_K × ω^{⊗b}_K → ω^{⊗(a+b)}_K`, `a, b ∈ ℕ`, by
concatenation of tensors (`TensorPower.mulEquiv`), a `K`-bilinear map. -/
def pluriFormsMul (a b : ℕ) :
    PluriForms k K d a →ₗ[K] PluriForms k K d b →ₗ[K] PluriForms k K d ((a + b : ℕ) : ℤ) :=
  (TensorProduct.mk K (⨂[K]^a (⋀[K]^d Ω[K⁄k])) (⨂[K]^b (⋀[K]^d Ω[K⁄k]))).compr₂
    (TensorPower.mulEquiv (R := K) (M := ⋀[K]^d Ω[K⁄k]) (n := a) (m := b)).toLinearMap

/-- `ω^{⊗a} · ω^{⊗b} = ω^{⊗(a+b)}`. -/
theorem pluriFormsMul_formPow (ω : ⋀[K]^d Ω[K⁄k]) (a b : ℕ) :
    pluriFormsMul k K d a b (formPow ω a) (formPow ω b) = formPow ω (a + b) := by
  have h := TensorPower.tprod_mul_tprod K (M := ⋀[K]^d Ω[K⁄k]) (fun _ : Fin a => ω)
    (fun _ : Fin b => ω)
  rw [TensorPower.gMul_def] at h
  refine h.trans ?_
  unfold formPow
  congr 1
  funext i
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp

/-- **Multiplication of coefficients.** `(f ω^{⊗a}) · (g ω^{⊗b}) = (f g) ω^{⊗(a+b)}`. -/
theorem pluriFormsMul_smul_formPow (ω : ⋀[K]^d Ω[K⁄k]) (a b : ℕ) (f g : K) :
    pluriFormsMul k K d a b (f • formPow ω a) (g • formPow ω b) = (f * g) • formPow ω (a + b) := by
  rw [LinearMap.map_smul₂, map_smul, pluriFormsMul_formPow, smul_smul, mul_comm]

/-- `b^{⊗a} = (b ())^{⊗a}` for a basis `b` of a line. -/
theorem ZTensorPower.basis_natCast (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) (a : ℕ) :
    (ZTensorPower.basis b a () : PluriForms k K d a) = formPow (b ()) a :=
  ZTensorPower.basis_ofNat b a

/-- A form of degree `a ∈ ℕ` is its coordinate times `ω^{⊗a}`, for `ω` the basis vector of the
line `Ω^d_{K/k}`. -/
theorem eq_repr_smul_formPow (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) {a : ℕ}
    (τ : PluriForms k K d a) :
    τ = (ZTensorPower.basis b a).repr τ () • formPow (b ()) a := by
  rw [← ZTensorPower.basis_natCast, basis_unit_repr_smul]

/-- The coordinate of a product along a basis of the line is the product of the coordinates. -/
theorem repr_pluriFormsMul (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) {a a' : ℕ}
    (τ : PluriForms k K d a) (τ' : PluriForms k K d a') :
    (ZTensorPower.basis b ((a + a' : ℕ) : ℤ)).repr (pluriFormsMul k K d a a' τ τ') () =
      (ZTensorPower.basis b a).repr τ () * (ZTensorPower.basis b a').repr τ' () := by
  conv_lhs => rw [eq_repr_smul_formPow b τ, eq_repr_smul_formPow b τ',
    pluriFormsMul_smul_formPow, ← ZTensorPower.basis_natCast]
  simp

/-- The coordinate of `c ω^{⊗a}` along the basis `b^{⊗a}`, `ω = b ()`, is `c`. -/
theorem repr_smul_formPow (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) (a : ℕ) (c : K) :
    (ZTensorPower.basis b a).repr (c • formPow (b ()) a : PluriForms k K d a) () = c := by
  rw [← ZTensorPower.basis_natCast]
  simp

/-- `(c ω)^{⊗a} = c^a ω^{⊗a}`. -/
theorem formPow_smul (c : K) (ω : ⋀[K]^d Ω[K⁄k]) (a : ℕ) :
    formPow (c • ω) a = c ^ a • formPow ω a :=
  tprod_const_smul c ω

/-- `(g₁ ω^{⊗a}) · (g₂ (c ω)^{⊗b}) = (g₁ g₂ c^b) ω^{⊗(a+b)}`. -/
theorem pluriFormsMul_smul_formPow_frame_right {a b : ℕ} (ω : ⋀[K]^d Ω[K⁄k]) (c g₁ g₂ : K) :
    pluriFormsMul k K d a b (g₁ • formPow ω a) (g₂ • formPow (c • ω) b) =
      (g₁ * (g₂ * c ^ b)) • formPow ω (a + b) := by
  rw [formPow_smul, smul_smul, pluriFormsMul_smul_formPow]

/-- `(g₁ (c ω)^{⊗a}) · (g₂ ω^{⊗b}) = (g₁ c^a g₂) ω^{⊗(a+b)}`. -/
theorem pluriFormsMul_smul_formPow_frame_left {a b : ℕ} (ω : ⋀[K]^d Ω[K⁄k]) (c g₁ g₂ : K) :
    pluriFormsMul k K d a b (g₁ • formPow (c • ω) a) (g₂ • formPow ω b) =
      (g₁ * c ^ a * g₂) • formPow ω (a + b) := by
  rw [formPow_smul, smul_smul, pluriFormsMul_smul_formPow]

/-- On a line, a product of nonzero forms is nonzero. -/
theorem pluriFormsMul_ne_zero (b : Module.Basis Unit K (⋀[K]^d Ω[K⁄k])) {a a' : ℕ}
    {τ : PluriForms k K d a} {τ' : PluriForms k K d a'} (hτ : τ ≠ 0) (hτ' : τ' ≠ 0) :
    pluriFormsMul k K d a a' τ τ' ≠ 0 := by
  intro h
  have h1 := repr_pluriFormsMul b τ τ'
  rw [h, LinearEquiv.map_zero] at h1
  rcases mul_eq_zero.mp h1.symm with h2 | h2
  · exact hτ (by rw [eq_repr_smul_formPow b τ, h2, zero_smul])
  · exact hτ' (by rw [eq_repr_smul_formPow b τ', h2, zero_smul])

/-- **Orders are additive under products.** For `v` multiplicative on `K^×` and trivial on the
units of `A`, the order of a product of nonzero forms along `A` is the sum of their orders. -/
theorem ordAt_pluriFormsMul (A : Type*) [CommRing A] [Algebra k A] [Algebra A K]
    [IsScalarTower k A K] [IsFractionRing A K] {v : K → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0) {a a' : ℕ}
    {τ : PluriForms k K d a} {τ' : PluriForms k K d a'} (hτ : τ ≠ 0) (hτ' : τ' ≠ 0) :
    ordAt A v (pluriFormsMul k K d a a' τ τ') = ordAt A v τ + ordAt A v τ' := by
  by_cases h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  · obtain ⟨σ, hσ, h0⟩ := h
    rw [ordAt_eq hmul hunit hσ h0, ordAt_eq hmul hunit hσ h0, ordAt_eq hmul hunit hσ h0]
    have hc : formCoeff A hσ h0 (pluriFormsMul k K d a a' τ τ') =
        formCoeff A hσ h0 τ * formCoeff A hσ h0 τ' :=
      repr_pluriFormsMul (topFormsBasis A hσ h0) τ τ'
    rw [hc]
    exact hmul _ _ (by rwa [Ne, formCoeff_eq_zero_iff]) (by rwa [Ne, formCoeff_eq_zero_iff])
  · simp [ordAt, h]

end Field

/-! ### Pull-back of products -/

section Pullback

variable {k : Type*} [CommRing k] {K K' : Type*} [Field K] [Field K'] [Algebra k K]
  [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ}

/-- `u^*(c ω^{⊗a}) = u(c) (u^*ω)^{⊗a}` along a pull-back generator `ω`. -/
theorem pullbackForms_smul_formPow {ω : ⋀[K]^d Ω[K⁄k]} (hω : IsPullbackGenerator K' ω) (a : ℕ)
    (c : K) : pullbackForms (K' := K') (a : ℤ) (c • formPow ω a) =
      algebraMap K K' c • formPow (topFormsMap k K K' d ω) a := by
  rw [pullbackForms_eq hω, pullbackFormsAlong]
  have h1 : (formPow ω a : PluriForms k K d a) =
      ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) a () := by
    rw [ZTensorPower.basis_natCast, basisOfSpanSingleton_apply]
  have h2 : (formPow (topFormsMap k K K' d ω) a : PluriForms k K' d a) =
      ZTensorPower.basis (basisOfSpanSingleton hω.2.1 hω.2.2) a () := by
    rw [ZTensorPower.basis_natCast, basisOfSpanSingleton_apply]
  rw [h1, h2]
  simp

/-- **Pull-back is multiplicative**: `u^*(τ · τ') = u^*τ · u^*τ'`. -/
theorem pullbackForms_pluriFormsMul {a a' : ℕ} (τ : PluriForms k K d a)
    (τ' : PluriForms k K d a') :
    pullbackForms (K' := K') ((a + a' : ℕ) : ℤ) (pluriFormsMul k K d a a' τ τ') =
      pluriFormsMul k K' d a a' (pullbackForms (K' := K') a τ)
        (pullbackForms (K' := K') a' τ') := by
  by_cases h : ∃ ω : ⋀[K]^d Ω[K⁄k], IsPullbackGenerator K' ω
  · obtain ⟨ω, hω⟩ := h
    let B := basisOfSpanSingleton hω.1 hω.ne_zero
    have hB : B () = ω := basisOfSpanSingleton_apply _ _ _
    rw [eq_repr_smul_formPow B τ, eq_repr_smul_formPow B τ', pluriFormsMul_smul_formPow, hB,
      pullbackForms_smul_formPow hω, pullbackForms_smul_formPow hω,
      pullbackForms_smul_formPow hω, pluriFormsMul_smul_formPow, map_mul]
  · simp [pullbackForms, h]

end Pullback

/-! ### Products of rational pluriforms of a scheme -/

section Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]

/-- **The product of rational pluriforms** `ω^{⊗a}_{k(X)} × ω^{⊗b}_{k(X)} → ω^{⊗(a+b)}_{k(X)}`
of an integral scheme over `k`, for `a, b ∈ ℕ` (`MMP.Fourfold.pluriFormsMul`). -/
def RationalPluriForms.mul (d a b : ℕ) :
    RationalPluriForms sX d a →ₗ[X.functionField] RationalPluriForms sX d b →ₗ[X.functionField]
      RationalPluriForms sX d ((a + b : ℕ) : ℤ) :=
  letI := functionFieldAlgebra sX
  pluriFormsMul k X.functionField d a b

variable {sX}

/-- `(f ω^{⊗a}) · (g ω^{⊗b}) = (f g) ω^{⊗(a+b)}` for rational pluriforms. -/
theorem RationalPluriForms.mul_smul_formPow {d : ℕ}
    (ω : letI := functionFieldAlgebra sX; ⋀[X.functionField]^d Ω[X.functionField⁄k]) (a b : ℕ)
    (f g : X.functionField) :
    letI := functionFieldAlgebra sX
    RationalPluriForms.mul sX d a b (f • (formPow ω a : RationalPluriForms sX d a))
        (g • (formPow ω b : RationalPluriForms sX d b)) =
      (f * g) • (formPow ω (a + b) : RationalPluriForms sX d ((a + b : ℕ) : ℤ)) := by
  let := functionFieldAlgebra sX
  exact pluriFormsMul_smul_formPow ω a b f g

/-- On a variety of dimension `d` over a perfect field, the line `Ω^d_{k(X)/k}` has a basis. -/
theorem exists_basis_topForms [PerfectField k] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) :
    letI := functionFieldAlgebra sX
    Nonempty (Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k])) := by
  let := functionFieldAlgebra sX
  have := essFiniteType_functionField (sX := sX)
  have hK : Module.finrank X.functionField Ω[X.functionField⁄k] = d :=
    (finrank_kaehlerDifferential_eq_trdeg k X.functionField).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hd)
  have : FiniteDimensional X.functionField Ω[X.functionField⁄k] :=
    (trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k X.functionField).1
  have h1 : Module.finrank X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]) = 1 := by
    rw [exteriorPower.finrank_eq, hK, Nat.choose_self]
  exact ⟨(Module.finBasisOfFinrankEq _ _ h1).reindex (Equiv.ofUnique _ _)⟩

/-- On a variety of dimension `d` over a perfect field, a product of nonzero rational pluriforms
of degree `d` is nonzero. -/
theorem RationalPluriForms.mul_ne_zero [PerfectField k] [LocallyOfFiniteType sX] {d : ℕ}
    (hd : topologicalKrullDim X = d) {a b : ℕ} {τ : RationalPluriForms sX d a}
    {τ' : RationalPluriForms sX d b} (hτ : τ ≠ 0) (hτ' : τ' ≠ 0) :
    RationalPluriForms.mul sX d a b τ τ' ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨B⟩ := exists_basis_topForms (sX := sX) hd
  exact pluriFormsMul_ne_zero B hτ hτ'

variable [IsLocallyNoetherian X]

/-- **The order of a product.** `ord_Γ(τ · τ') = ord_Γ(τ) + ord_Γ(τ')` for nonzero forms. -/
theorem ordForm_mul (Γ : Mori.PrimeDivisor X) {d a b : ℕ} {τ : RationalPluriForms sX d a}
    {τ' : RationalPluriForms sX d b} (hτ : τ ≠ 0) (hτ' : τ' ≠ 0) :
    Γ.ordForm (RationalPluriForms.mul sX d a b τ τ') = Γ.ordForm τ + Γ.ordForm τ' := by
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact ordAt_pluriFormsMul (k := k) Γ.localRing Γ.ord_mul_of_ne_zero
    (fun _ ha => Γ.ord_algebraMap_of_isUnit ha) hτ hτ'

variable [IsNormal X]

/-- **Log pluricanonical sections form a graded ring**:
`H⁰(X, a(K_X + B)) · H⁰(X, b(K_X + B)) ⊆ H⁰(X, (a + b)(K_X + B))`. -/
theorem mul_mem_logPluricanonicalSections {d a b : ℕ} {B : QDivisor X}
    {τ : RationalPluriForms sX d a} {τ' : RationalPluriForms sX d b}
    (hτ : τ ∈ logPluricanonicalSections sX d a B) (hτ' : τ' ∈ logPluricanonicalSections sX d b B) :
    RationalPluriForms.mul sX d a b τ τ' ∈ logPluricanonicalSections sX d (a + b) B := by
  rw [mem_logPluricanonicalSections] at hτ hτ' ⊢
  refine ⟨fun h => by rw [hτ.1 h, map_zero, LinearMap.zero_apply], fun Γ hΓ h0 => ?_⟩
  have hτ0 : τ ≠ 0 := fun h => h0 (by rw [h, map_zero, LinearMap.zero_apply])
  have hτ0' : τ' ≠ 0 := fun h => h0 (by rw [h, map_zero])
  have h1 := hτ.2 Γ hΓ hτ0
  have h2 := hτ'.2 Γ hΓ hτ0'
  rw [ordForm_mul Γ hτ0 hτ0']
  simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_smul] at h1 h2 ⊢
  have h3 := Int.le_floor_add (((a : ℕ) : ℤ) • B.coeff Γ) (((b : ℕ) : ℤ) • B.coeff Γ)
  rw [← add_smul, ← Nat.cast_add] at h3
  omega

omit [IsNormal X] in
/-- **Products of local generators are local generators**: if `τ` generates
`𝒪_X(a(K_X + B))` and `τ'` generates `𝒪_X(b(K_X + B))` on `U`, then `τ · τ'` generates
`𝒪_X((a + b)(K_X + B))` on `U`, for a variety `X` of dimension `d` over a perfect field. -/
theorem GeneratesOn.mul [PerfectField k] [LocallyOfFiniteType sX] {d a b : ℕ}
    (hd : topologicalKrullDim X = d) {B : QDivisor X} {U : X.Opens}
    {τ : RationalPluriForms sX d a} {τ' : RationalPluriForms sX d b}
    (hτ : GeneratesOn B a U τ) (hτ' : GeneratesOn B b U τ') :
    GeneratesOn B (a + b) U (RationalPluriForms.mul sX d a b τ τ') := by
  refine ⟨RationalPluriForms.mul_ne_zero hd hτ.1 hτ'.1, fun Γ hΓ => ?_⟩
  have h1 := hτ.2 Γ hΓ
  have h2 := hτ'.2 Γ hΓ
  rw [ordForm_mul Γ hτ.1 hτ'.1]
  push_cast
  linarith

end Scheme

/-! ### Pluriform pull-back of products, composites and the identity -/

section PluriformPullback

variable {k : Type u} [Field k] {X X' X'' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} {sX'' : X'' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
  [IsIntegral X'']

/-- **Pluriform pull-back is multiplicative**: `φ^*(τ · τ') = φ^*τ · φ^*τ'`. -/
theorem pluriformPullback_mul (φ : FunctionFieldHom sX sX') {d a b : ℕ}
    (τ : RationalPluriForms sX' d a) (τ' : RationalPluriForms sX' d b) :
    pluriformPullback sX sX' φ d ((a + b : ℕ) : ℤ) (RationalPluriForms.mul sX' d a b τ τ') =
      RationalPluriForms.mul sX d a b (pluriformPullback sX sX' φ d a τ)
        (pluriformPullback sX sX' φ d b τ') := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact pullbackForms_pluriFormsMul (K := X'.functionField) (K' := X.functionField) τ τ'

/-- `φ^*(c ω^{⊗a}) = φ(c) (φ^*ω)^{⊗a}` for a pull-back generator `ω`. -/
theorem pluriformPullback_smul_formPow (φ : FunctionFieldHom sX sX') {d : ℕ}
    {ω : letI := functionFieldAlgebra sX'; ⋀[X'.functionField]^d Ω[X'.functionField⁄k]}
    (hω : letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
      letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
      haveI : IsScalarTower k X'.functionField X.functionField :=
        IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
      IsPullbackGenerator X.functionField ω) (a : ℕ) (c : X'.functionField) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    pluriformPullback sX sX' φ d a (c • formPow ω a) =
      φ c • formPow (topFormsMap k X'.functionField X.functionField d ω) a := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  exact pullbackForms_smul_formPow (K := X'.functionField) (K' := X.functionField) hω a c

/-- Function fields of varieties of the same dimension have the same transcendence degree. -/
theorem trdeg_functionField_eq [LocallyOfFiniteType sX] [LocallyOfFiniteType sX'] {d : ℕ}
    (hX : topologicalKrullDim X = d) (hX' : topologicalKrullDim X' = d) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra sX'
    Algebra.trdeg k X.functionField = Algebra.trdeg k X'.functionField := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra sX'
  have := essFiniteType_functionField (sX := sX)
  have := essFiniteType_functionField (sX := sX')
  refine Cardinal.toNat_injOn (Set.mem_Iio.mpr ?_) (Set.mem_Iio.mpr ?_)
    ((toNat_trdeg_functionField_of_topologicalKrullDim_eq hX).trans
      (toNat_trdeg_functionField_of_topologicalKrullDim_eq hX').symm)
  · exact trdeg_lt_aleph0 (K := k) (L := X.functionField)
  · exact trdeg_lt_aleph0 (K := k) (L := X'.functionField)

/-- **Pull-back is functorial**: `φ^*(ψ^* τ) = (φ ∘ ψ)^* τ` for `k`-homomorphisms
`ψ : k(X'') → k(X')`, `φ : k(X') → k(X)` of function fields of varieties of the same dimension `d`
over a field of characteristic zero. -/
theorem pluriformPullback_comp [CharZero k] [LocallyOfFiniteType sX] [LocallyOfFiniteType sX']
    [LocallyOfFiniteType sX''] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hX' : topologicalKrullDim X' = d) (hX'' : topologicalKrullDim X'' = d) (m : ℤ)
    (φ : FunctionFieldHom sX sX') (ψ : FunctionFieldHom sX' sX'')
    (τ : RationalPluriForms sX'' d m) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra sX'
    letI := functionFieldAlgebra sX''
    pluriformPullback sX sX' φ d m (pluriformPullback sX' sX'' ψ d m τ) =
      pluriformPullback sX sX'' (φ.comp ψ) d m τ := by
  let A := functionFieldAlgebra sX
  let A' := functionFieldAlgebra sX'
  let A'' := functionFieldAlgebra sX''
  have := essFiniteType_functionField (sX := sX')
  have := essFiniteType_functionField (sX := sX'')
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX'') hX''
  have hd' := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX') hX'
  let Aψ : Algebra X''.functionField X'.functionField := ψ.toRingHom.toAlgebra
  let Aφ : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  let Aφψ : Algebra X''.functionField X.functionField := (φ.comp ψ).toRingHom.toAlgebra
  have tψ : @IsScalarTower k X''.functionField X'.functionField _ Aψ.toSMul _ := by
    let := Aψ
    exact IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have tφ : @IsScalarTower k X'.functionField X.functionField _ Aφ.toSMul _ := by
    let := Aφ
    exact IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have tφψ : @IsScalarTower k X''.functionField X.functionField _ Aφψ.toSMul _ := by
    let := Aφψ
    exact IsScalarTower.of_algebraMap_eq fun c => ((φ.comp ψ).commutes c).symm
  have t3 : @IsScalarTower X''.functionField X'.functionField X.functionField Aψ.toSMul
      Aφ.toSMul Aφψ.toSMul := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ Aψ Aφ Aφψ fun c => rfl
  obtain ⟨ω, hω⟩ := @exists_isPullbackGenerator k X''.functionField X'.functionField _ _ _ _ A''
    A' Aψ tψ _ (trdeg_functionField_eq hX'' hX') d hd
  obtain ⟨ω', hω'⟩ := @exists_isPullbackGenerator k X'.functionField X.functionField _ _ _ _ A'
    A Aφ tφ _ (trdeg_functionField_eq hX' hX) d hd'
  have h2 := @MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span k _ d X'.functionField
    X.functionField _ _ A' A Aφ tφ ω' _ hω' hω.2.1 hω.2.2
  exact @MMP.Threefold.Mori.Helpers.pullbackForms_comp k _ d m X''.functionField X'.functionField
    X.functionField _ _ _ A'' A' A Aψ Aφ Aφψ tψ tφ tφψ t3 ω hω h2 τ

/-- **Pull-back generators exist along homomorphisms of function fields of varieties of the
same dimension** in characteristic zero: some generator `ω` of the line `Ω^d_{k(X')/k}` pulls back
along `φ : k(X') → k(X)` to a generator of `Ω^d_{k(X)/k}`. -/
theorem exists_isPullbackGenerator_functionFieldHom [CharZero k] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hX' : topologicalKrullDim X' = d) (φ : FunctionFieldHom sX sX') :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    ∃ ω : ⋀[X'.functionField]^d Ω[X'.functionField⁄k], IsPullbackGenerator X.functionField ω := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  have := essFiniteType_functionField (sX := sX')
  exact exists_isPullbackGenerator (trdeg_functionField_eq hX' hX)
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq hX')

/-- Every generator of the line `Ω^d_{k(X')/k}` is a pull-back generator along a homomorphism of
function fields of varieties of the same dimension, in characteristic zero. -/
theorem isPullbackGenerator_functionFieldHom [CharZero k] [LocallyOfFiniteType sX]
    [LocallyOfFiniteType sX'] {d : ℕ} (hX : topologicalKrullDim X = d)
    (hX' : topologicalKrullDim X' = d) (φ : FunctionFieldHom sX sX')
    {ω : letI := functionFieldAlgebra sX'; ⋀[X'.functionField]^d Ω[X'.functionField⁄k]}
    (hω : letI := functionFieldAlgebra sX'; Submodule.span X'.functionField {ω} = ⊤)
    (h0 : ω ≠ 0) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    IsPullbackGenerator X.functionField ω := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_functionFieldHom hX hX' φ
  exact MMP.Threefold.Mori.Helpers.IsPullbackGenerator.of_span hω₀ hω h0

/-- **Pull-back in coordinates.** If `b'` is a basis of the line `Ω^d_{k(X')/k}` whose vector is a
pull-back generator along `φ`, and `b` is the basis of `Ω^d_{k(X)/k}` given by its pull-back,
then `φ^*(c b'^{⊗a}) = φ(c) b^{⊗a}`: the coordinates are transported by `φ`. -/
theorem pluriformPullback_eq_repr_smul_formPow (φ : FunctionFieldHom sX sX') {d : ℕ}
    (b' : letI := functionFieldAlgebra sX'
      Module.Basis Unit X'.functionField (⋀[X'.functionField]^d Ω[X'.functionField⁄k]))
    (hω : letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
      letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
      haveI : IsScalarTower k X'.functionField X.functionField :=
        IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
      IsPullbackGenerator X.functionField (b' ()))
    (b : letI := functionFieldAlgebra sX
      Module.Basis Unit X.functionField (⋀[X.functionField]^d Ω[X.functionField⁄k]))
    (hb : letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
      letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
      haveI : IsScalarTower k X'.functionField X.functionField :=
        IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
      b () = topFormsMap k X'.functionField X.functionField d (b' ()))
    (a : ℕ) (ρ : RationalPluriForms sX' d a) :
    letI := functionFieldAlgebra sX'; letI := functionFieldAlgebra sX
    pluriformPullback sX sX' φ d a ρ =
      (φ ((ZTensorPower.basis b' a).repr ρ ()) • formPow (b ()) a : RationalPluriForms sX d a) := by
  let := functionFieldAlgebra sX'
  let := functionFieldAlgebra sX
  let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
  have : IsScalarTower k X'.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  conv_lhs => rw [eq_repr_smul_formPow b' ρ]
  rw [hb]
  exact pluriformPullback_smul_formPow φ hω a _

/-- The differentials map along the identity is the identity. -/
theorem kaehlerDifferential_map_self {K : Type*} [Field K] [Algebra k K] (w : Ω[K⁄k]) :
    letI : Algebra K K := (RingHom.id K).toAlgebra
    haveI : IsScalarTower k K K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    KaehlerDifferential.map k k K K w = w := by
  let : Algebra K K := (RingHom.id K).toAlgebra
  have : IsScalarTower k K K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hw : w ∈ Submodule.span K (Set.range (KaehlerDifferential.D k K)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    exact (KaehlerDifferential.map_D k k K K x).trans rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [← algebraMap_smul K a x, map_smul, hx]

/-- Top forms map along the identity is the identity. -/
theorem topFormsMap_self {K : Type*} [Field K] [Algebra k K] {d : ℕ} (x : ⋀[K]^d Ω[K⁄k]) :
    letI : Algebra K K := (RingHom.id K).toAlgebra
    haveI : IsScalarTower k K K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    topFormsMap k K K d x = x := by
  let : Algebra K K := (RingHom.id K).toAlgebra
  have : IsScalarTower k K K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hx : x ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K d (M := Ω[K⁄k]))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨v, rfl⟩ := hw
    rw [topFormsMap_ιMulti]
    congr 1
    funext i
    exact kaehlerDifferential_map_self (v i)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul a x _ hx => rw [← algebraMap_smul K a x, map_smul, hx]

/-- **Pull-back along the identity is the identity**, on a variety of dimension `d` over a field
of characteristic zero. -/
theorem pluriformPullback_one [CharZero k] [LocallyOfFiniteType sX] {d : ℕ}
    (hX : topologicalKrullDim X = d) (m : ℤ) (τ : RationalPluriForms sX d m) :
    pluriformPullback sX sX (1 : FunctionFieldEquiv sX sX).toHom d m τ = τ := by
  let A := functionFieldAlgebra sX
  have := essFiniteType_functionField (sX := sX)
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hX
  let A1 : Algebra X.functionField X.functionField := (RingHom.id X.functionField).toAlgebra
  have t1 : @IsScalarTower k X.functionField X.functionField _ A1.toSMul _ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨ω, hω⟩ := @exists_isPullbackGenerator k X.functionField X.functionField _ _ _ _ A A A1
    t1 _ rfl d hd
  have hω' : @topFormsMap k _ X.functionField _ A X.functionField _ A A1 t1 d ω = ω :=
    topFormsMap_self ω
  have key : ∀ y : @PluriForms k _ X.functionField _ A d m,
      @pullbackForms k _ X.functionField X.functionField _ _ A A A1 t1 d m y = y := by
    intro y
    rw [pullbackForms_eq hω, pullbackFormsAlong]
    have hB : basisOfSpanSingleton hω.2.1 hω.2.2 () =
        (1 : X.functionField) • basisOfSpanSingleton hω.1 hω.ne_zero () := by
      rw [basisOfSpanSingleton_apply, basisOfSpanSingleton_apply, hω', one_smul]
    rw [ZTensorPower.basis_apply_of_eq_smul hB, one_zpow, one_smul]
    exact basis_unit_repr_smul _ y
  exact key τ

end PluriformPullback

/-! ### Composites and inverses of crepant birational maps -/

section Crepant

variable {k : Type u} [Field k] {X X' X'' : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  {sX' : X' ⟶ Spec (.of k)} {sX'' : X'' ⟶ Spec (.of k)} [IsIntegral X] [IsIntegral X']
  [IsIntegral X''] [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian X'] [IsNormal X']
  [IsLocallyNoetherian X''] [IsNormal X''] {B : QDivisor X} {B' : QDivisor X'}
  {B'' : QDivisor X''}

/-- **Composites of crepant birational maps are crepant**: for crepant
`σ = φ^* : k(X') ≅ k(X)` and `τ = ψ^* : k(X'') ≅ k(X')`, the composite pull-back
`k(X'') ≅ k(X)` is crepant. -/
theorem IsCrepantBirationalMap.trans {σ : FunctionFieldEquiv sX sX'}
    {τ : FunctionFieldEquiv sX' sX''} (hσ : IsCrepantBirationalMap sX sX' B B' σ)
    (hτ : IsCrepantBirationalMap sX' sX'' B' B'' τ) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra sX'
    letI := functionFieldAlgebra sX''
    IsCrepantBirationalMap sX sX'' B B'' (τ.trans σ) := by
  intro v a
  exact (hσ v a).trans (hτ _ a)

/-- **Inverses of crepant birational maps are crepant.** -/
theorem IsCrepantBirationalMap.symm {σ : FunctionFieldEquiv sX sX'}
    (hσ : IsCrepantBirationalMap sX sX' B B' σ) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra sX'
    IsCrepantBirationalMap sX' sX B' B σ.symm := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra sX'
  intro v a
  have h := hσ (v.comap σ.symm.toRingEquiv.toRingHom) a
  have hv : (v.comap σ.symm.toRingEquiv.toRingHom).comap σ.toRingEquiv.toRingHom = v := by
    ext x
    change v (σ.symm (σ x)) = v x
    rw [AlgEquiv.symm_apply_apply]
  rw [hv] at h
  exact h.symm

end Crepant

/-! ### Evaluating logarithmic forms against derivations -/

section ResidueAlgebra

open exteriorPower

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
  {K : Type*} [Field K] [Algebra k K] [Algebra O K] [IsScalarTower k O K] [IsFractionRing O K]

omit [IsDomain O] in
/-- An `O`-linear functional on `Ω_{O/k}` extends to a `K`-linear functional on `Ω_{K/k}`, for `K`
the fraction field. -/
theorem exists_dual_extend (f : Ω[O⁄k] →ₗ[O] O) :
    ∃ fK : Module.Dual K Ω[K⁄k],
      ∀ w, fK (KaehlerDifferential.map k k O K w) = algebraMap O K (f w) :=
  ⟨IsLocalizedModule.mapExtendScalars (nonZeroDivisors O) (KaehlerDifferential.map k k O K)
      (Algebra.linearMap O K) K f, fun w => by
    rw [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]; rfl⟩

variable {L : Type*} [Field L] [Algebra k L] [Algebra O L] [IsScalarTower k O L]

/-- **The residue of a logarithmic form, evaluated.** Let `t₀ ∈ O` with `π(t₀) = 0`, where
`π : O → L`, and `r : Ω_O → O` with `r(dt₀) = 1`; put `E = t₀ r`. Let `D_a : Ω_O → O` lift
functionals `φ_a` on `Ω_L`. For `t' = u t₀`, `u` a unit, and `x' ∈ O^e`, the evaluation of
`t'^{-1} dt' ∧ dx'_1 ∧ ⋯ ∧ dx'_e` on `(E, D_1, …, D_e)` lies in `O`, and reduces under `π` to the
evaluation of `dπx'_1 ∧ ⋯ ∧ dπx'_e` on `(φ_1, …, φ_e)`. -/
theorem exists_eval_logForm {t₀ : O} (ht₀ : algebraMap O L t₀ = 0) {r : Ω[O⁄k] →ₗ[O] O}
    (hr : r (KaehlerDifferential.D k O t₀) = 1) {rK : Module.Dual K Ω[K⁄k]}
    (hrK : ∀ w, rK (KaehlerDifferential.map k k O K w) = algebraMap O K (r w)) {e : ℕ}
    {Dl : Fin e → (Ω[O⁄k] →ₗ[O] O)} {DlK : Fin e → Module.Dual K Ω[K⁄k]}
    (hDlK : ∀ a w, DlK a (KaehlerDifferential.map k k O K w) = algebraMap O K (Dl a w))
    {φ : Fin e → Module.Dual L Ω[L⁄k]}
    (hφ : ∀ a w, algebraMap O L (Dl a w) = φ a (KaehlerDifferential.map k k O L w))
    {u : O} (hu : IsUnit u) (x' : Fin e → O) :
    ∃ o : O, algebraMap O K o = (algebraMap O K (u * t₀))⁻¹ *
        pairingDual K Ω[K⁄k] (e + 1) (ιMulti K (e + 1)
          (Fin.cons (algebraMap O K t₀ • rK) DlK))
        (ιMulti K (e + 1) (Fin.cons (KaehlerDifferential.D k K (algebraMap O K (u * t₀)))
          fun i => KaehlerDifferential.D k K (algebraMap O K (x' i)))) ∧
      algebraMap O L o = pairingDual L Ω[L⁄k] e (ιMulti L e φ)
        (ιMulti L e fun i => KaehlerDifferential.D k L (algebraMap O L (x' i))) := by
  classical
  set t' := u * t₀
  let vO : Fin (e + 1) → Ω[O⁄k] :=
    Fin.cons (KaehlerDifferential.D k O t') fun i => KaehlerDifferential.D k O (x' i)
  let F : Fin (e + 1) → (Ω[O⁄k] →ₗ[O] O) := Fin.cons r Dl
  let A : Matrix (Fin (e + 1)) (Fin (e + 1)) O := Matrix.of fun i j => F j (vO i)
  have ht₀0 : t₀ ≠ 0 := by
    rintro rfl
    simp at hr
  have hK0 : algebraMap O K t₀ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr ht₀0
  refine ⟨↑hu.unit⁻¹ * A.det, ?_, ?_⟩
  · rw [pairingDual_ιMulti_ιMulti]
    have hM : (Matrix.of fun i j => (Fin.cons (algebraMap O K t₀ • rK) DlK : Fin (e + 1) → _) j
        ((Fin.cons (KaehlerDifferential.D k K (algebraMap O K t'))
          fun i => KaehlerDifferential.D k K (algebraMap O K (x' i)) : Fin (e + 1) → _) i)) =
        A.map (algebraMap O K) * Matrix.diagonal (Fin.cons (algebraMap O K t₀) 1) := by
      ext i j
      rw [Matrix.mul_diagonal]
      have hv : (Fin.cons (KaehlerDifferential.D k K (algebraMap O K t'))
          fun i => KaehlerDifferential.D k K (algebraMap O K (x' i)) : Fin (e + 1) → _) i =
          KaehlerDifferential.map k k O K (vO i) := by
        refine Fin.cases ?_ (fun i => ?_) i <;> simp [vO, KaehlerDifferential.map_D]
      rw [Matrix.of_apply, hv]
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [A, F, hrK, mul_comm, Algebra.smul_def]
      · simp [A, F, hDlK]
    rw [hM, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_cons,
      show (A.map (algebraMap O K)).det = algebraMap O K A.det from (RingHom.map_det _ A).symm]
    simp only [Pi.one_apply, Finset.prod_const_one, mul_one]
    have hu0 : algebraMap O K u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hu.ne_zero
    have hu' : algebraMap O K ↑hu.unit⁻¹ = (algebraMap O K u)⁻¹ := by
      rw [map_units_inv (algebraMap O K) hu.unit, IsUnit.unit_spec]
    rw [map_mul, hu', map_mul]
    field_simp
  · rw [pairingDual_ιMulti_ιMulti, map_mul, RingHom.map_det, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ]
    have hπt' : algebraMap O L t' = 0 := by simp [t', ht₀]
    have h00 : (algebraMap O L).mapMatrix A 0 0 = algebraMap O L u := by
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, A, F, vO, Matrix.of_apply,
        Fin.cons_zero, t', Derivation.leibniz, map_add, map_smul, hr, smul_eq_mul, mul_one]
      simp [ht₀]
    have h0s : ∀ a : Fin e, (algebraMap O L).mapMatrix A 0 a.succ = 0 := fun a => by
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, A, F, vO, Matrix.of_apply,
        Fin.cons_zero, Fin.cons_succ, hφ, KaehlerDifferential.map_D, hπt', map_zero]
    have hsub : ((algebraMap O L).mapMatrix A).submatrix Fin.succ (Fin.succAbove 0) =
        Matrix.of fun i j => φ j (KaehlerDifferential.D k L (algebraMap O L (x' i))) := by
      ext i j
      simp only [Matrix.submatrix_apply, Fin.succAbove_zero, RingHom.mapMatrix_apply,
        Matrix.map_apply, A, F, vO, Matrix.of_apply, Fin.cons_succ, hφ,
        KaehlerDifferential.map_D]
    simp only [h0s, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, h00, hsub,
      Fin.val_zero, pow_zero, one_mul]
    rw [← mul_assoc, ← map_mul, hu.val_inv_mul, map_one, one_mul]

end ResidueAlgebra

section Separation

open exteriorPower

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- **Products of evaluations separate tensor powers of exterior powers**: an element of
`(⋀^e V)^{⊗m}` on which every functional `⊗_c (v ↦ det(φ_{c,j}(v_i)))` vanishes is zero. -/
theorem eq_zero_of_forall_dualDistrib_pairingDual {e m : ℕ} (ρ : ⨂[F]^m (⋀[F]^e V))
    (h : ∀ φ : Fin m → Fin e → Module.Dual F V,
      PiTensorProduct.dualDistrib (⨂ₜ[F] c, pairingDual F V e (ιMulti F e (φ c))) ρ = 0) :
    ρ = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F V
  let : LinearOrder (Module.Basis.ofVectorSpaceIndex F V) := linearOrderOfSTO WellOrderingRel
  let Bx := b.exteriorPower e
  let T := Basis.piTensorProduct fun _ : Fin m => Bx
  have hcoord : ∀ p, T.repr ρ p = PiTensorProduct.dualDistrib
      (⨂ₜ[F] c, pairingDual F V e (ιMulti F e fun j =>
        b.coord (Set.powersetCard.ofFinEmbEquiv.symm (p c) j))) ρ := by
    intro p
    have key : (Finsupp.lapply p) ∘ₗ T.repr.toLinearMap = PiTensorProduct.dualDistrib
        (⨂ₜ[F] c, pairingDual F V e (ιMulti F e fun j =>
          b.coord (Set.powersetCard.ofFinEmbEquiv.symm (p c) j))) := by
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, Finsupp.lapply_apply, T, Basis.piTensorProduct_repr_tprod_apply,
        PiTensorProduct.dualDistrib_apply]
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [exteriorPower.basis_repr_apply]
      rfl
    exact LinearMap.congr_fun key ρ
  refine T.ext_elem fun p => ?_
  rw [hcoord, map_zero, Finsupp.zero_apply]
  exact h _

end Separation

section ResidueUnique

open exteriorPower

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
  {K : Type*} [Field K] [Algebra k K] [Algebra O K] [IsScalarTower k O K] [IsFractionRing O K]
  {L : Type*} [Field L] [Algebra k L] [Algebra O L] [IsScalarTower k O L]

/-- The logarithmic pluriform `g (t^{-1} dt ∧ dx_1 ∧ ⋯ ∧ dx_e)^{⊗m}`, for `g t ∈ O`, `x ∈ O^e`. -/
abbrev logPluriForm (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra O K] (m e : ℕ)
    (g t : O) (x : Fin e → O) : ⨂[K]^m (⋀[K]^(e + 1) Ω[K⁄k]) :=
  algebraMap O K g • ⨂ₜ[K] _ : Fin m, (algebraMap O K t)⁻¹ • ιMulti K (e + 1)
    (Fin.cons (KaehlerDifferential.D k K (algebraMap O K t))
      fun i => KaehlerDifferential.D k K (algebraMap O K (x i)))

/-- The pluriform `ḡ (dx̄_1 ∧ ⋯ ∧ dx̄_e)^{⊗m}` of the reductions of `g` and `x` along `O → L`. -/
abbrev logPluriResidue (k L : Type*) [Field k] [Field L] [Algebra k L] [Algebra O L] (m e : ℕ)
    (g : O) (x : Fin e → O) : ⨂[L]^m (⋀[L]^e Ω[L⁄k]) :=
  algebraMap O L g • ⨂ₜ[L] _ : Fin m, ιMulti L e
    fun i => KaehlerDifferential.D k L (algebraMap O L (x i))

/-- **Uniqueness of residues of logarithmic pluriforms.** Let `Ω_{O/k}` be projective, `π : O → L`
surjective, `t₀ ∈ ker π` with `dt₀` part of a retraction `r(dt₀) = 1`. If
`g₁ (t₁^{-1} dt₁ ∧ dx₁)^{⊗m} = g₂ (t₂^{-1} dt₂ ∧ dx₂)^{⊗m}` with `t_i = u_i t₀`, `u_i` units, then
`ḡ₁ (dx̄₁)^{⊗m} = ḡ₂ (dx̄₂)^{⊗m}`. -/
theorem logPluriResidue_eq_of_logPluriForm_eq [Module.Projective O Ω[O⁄k]]
    (hπ : Function.Surjective (algebraMap O L)) {t₀ : O} (ht₀ : algebraMap O L t₀ = 0)
    {r : Ω[O⁄k] →ₗ[O] O} (hr : r (KaehlerDifferential.D k O t₀) = 1) {e m : ℕ}
    {g₁ g₂ u₁ u₂ : O} (hu₁ : IsUnit u₁) (hu₂ : IsUnit u₂) (x₁ x₂ : Fin e → O)
    (h : logPluriForm (O := O) k K m e g₁ (u₁ * t₀) x₁ =
      logPluriForm (O := O) k K m e g₂ (u₂ * t₀) x₂) :
    logPluriResidue (O := O) k L m e g₁ x₁ = logPluriResidue (O := O) k L m e g₂ x₂ := by
  classical
  obtain ⟨rK, hrK⟩ := exists_dual_extend (K := K) r
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_dualDistrib_pairingDual _ fun φ => ?_
  have hlift : ∀ c a, ∃ D : Ω[O⁄k] →ₗ[O] O, ∀ w,
      algebraMap O L (D w) = φ c a (KaehlerDifferential.map k k O L w) := fun c a => by
    obtain ⟨D, hD⟩ := Module.projective_lifting_property (Algebra.linearMap O L)
      (((φ c a).restrictScalars O) ∘ₗ (KaehlerDifferential.map k k O L)) hπ
    exact ⟨D, fun w => LinearMap.congr_fun hD w⟩
  choose Dl hDl using hlift
  have hext : ∀ c a, ∃ DK : Module.Dual K Ω[K⁄k], ∀ w,
      DK (KaehlerDifferential.map k k O K w) = algebraMap O K (Dl c a w) :=
    fun c a => exists_dual_extend (K := K) (Dl c a)
  choose DlK hDlK using hext
  have hev : ∀ (u : O) (hu : IsUnit u) (x : Fin e → O) (c : Fin m), ∃ o : O,
      algebraMap O K o = (algebraMap O K (u * t₀))⁻¹ *
        pairingDual K Ω[K⁄k] (e + 1) (ιMulti K (e + 1)
          (Fin.cons (algebraMap O K t₀ • rK) (DlK c)))
        (ιMulti K (e + 1) (Fin.cons (KaehlerDifferential.D k K (algebraMap O K (u * t₀)))
          fun i => KaehlerDifferential.D k K (algebraMap O K (x i)))) ∧
      algebraMap O L o = pairingDual L Ω[L⁄k] e (ιMulti L e (φ c))
        (ιMulti L e fun i => KaehlerDifferential.D k L (algebraMap O L (x i))) :=
    fun u hu x c => exists_eval_logForm ht₀ hr hrK (hDlK c) (hDl c) hu x
  choose o ho₁ ho₂ using hev
  let ΨK := PiTensorProduct.dualDistrib (R := K)
    (⨂ₜ[K] c : Fin m, pairingDual K Ω[K⁄k] (e + 1)
      (ιMulti K (e + 1) (Fin.cons (algebraMap O K t₀ • rK) (DlK c))))
  have hK : ∀ (g u : O) (hu : IsUnit u) (x : Fin e → O),
      ΨK (logPluriForm (O := O) k K m e g (u * t₀) x) =
        algebraMap O K (g * ∏ c, o u hu x c) := fun g u hu x => by
    simp only [ΨK, logPluriForm, map_smul, PiTensorProduct.dualDistrib_apply, smul_eq_mul,
      map_mul, map_prod, ho₁]
  have hL : ∀ (g u : O) (hu : IsUnit u) (x : Fin e → O),
      PiTensorProduct.dualDistrib (⨂ₜ[L] c, pairingDual L Ω[L⁄k] e (ιMulti L e (φ c)))
        (logPluriResidue (O := O) k L m e g x) = algebraMap O L (g * ∏ c, o u hu x c) :=
    fun g u hu x => by
      simp only [logPluriResidue, map_smul, PiTensorProduct.dualDistrib_apply, smul_eq_mul,
        map_mul, map_prod, ho₂]
  have hO : g₁ * ∏ c, o u₁ hu₁ x₁ c = g₂ * ∏ c, o u₂ hu₂ x₂ c :=
    IsFractionRing.injective O K ((hK g₁ u₁ hu₁ x₁).symm.trans (h ▸ hK g₂ u₂ hu₂ x₂))
  rw [map_sub, hL g₁ u₁ hu₁ x₁, hL g₂ u₂ hu₂ x₂, hO, sub_self]

end ResidueUnique

section Retraction

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [Algebra k O] {L : Type*} [Field L]
  [Algebra k L] [Algebra O L] [IsScalarTower k O L]

/-- For `O` formally smooth over `k`, `O → L` surjective with `H₁(L_{L/k}) = 0`, and
`t ∈ I = ker(O → L)` with `t ∉ I²`, the differential `1 ⊗ dt` in `L ⊗ Ω_{O/k}` is nonzero. -/
theorem one_tmul_D_ne_zero_of_notMem_sq [Algebra.FormallySmooth k O]
    [Subsingleton (Algebra.H1Cotangent k L)]
    (hπ : Function.Surjective (algebraMap O L)) {t : O} (ht : t ∈ RingHom.ker (algebraMap O L))
    (ht2 : t ∉ RingHom.ker (algebraMap O L) ^ 2) :
    (1 : L) ⊗ₜ[O] KaehlerDifferential.D k O t ≠ 0 := by
  have hinj := (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff (R := k) hπ).mpr
    inferInstance
  have hx : Ideal.toCotangent (RingHom.ker (algebraMap O L)) ⟨t, ht⟩ ≠ 0 := by
    rwa [Ne, Ideal.toCotangent_eq_zero]
  have := (map_ne_zero_iff _ hinj).mpr hx
  rwa [KaehlerDifferential.kerCotangentToTensor_toCotangent] at this

/-- **A retraction of `dt`.** Let `O` be local and formally smooth over `k` with projective
`Ω_{O/k}`, let `O → L` be surjective onto a field with `H₁(L_{L/k}) = 0`, and let
`t ∈ I = ker(O → L)` with `t ∉ I²`. Then there is `r : Ω_{O/k} → O` with `r(dt) = 1`. -/
theorem exists_retraction_D [IsLocalRing O] [Algebra.FormallySmooth k O]
    [Module.Projective O Ω[O⁄k]] [Subsingleton (Algebra.H1Cotangent k L)]
    (hπ : Function.Surjective (algebraMap O L)) {t : O} (ht : t ∈ RingHom.ker (algebraMap O L))
    (ht2 : t ∉ RingHom.ker (algebraMap O L) ^ 2) :
    ∃ r : Ω[O⁄k] →ₗ[O] O, r (KaehlerDifferential.D k O t) = 1 := by
  have hv := one_tmul_D_ne_zero_of_notMem_sq (k := k) hπ ht ht2
  obtain ⟨φ, hφ⟩ :
      ∃ φ : Module.Dual L (L ⊗[O] Ω[O⁄k]), φ (1 ⊗ₜ KaehlerDifferential.D k O t) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv ((Module.forall_dual_apply_eq_zero_iff L _).mp hcon)
  let g : Ω[O⁄k] →ₗ[O] L :=
    ((φ (1 ⊗ₜ KaehlerDifferential.D k O t))⁻¹ • φ).restrictScalars O ∘ₗ
      TensorProduct.mk O L Ω[O⁄k] 1
  obtain ⟨r₁, hr₁⟩ := Module.projective_lifting_property (Algebra.linearMap O L) g hπ
  have h1 : algebraMap O L (r₁ (KaehlerDifferential.D k O t)) = 1 := by
    have := LinearMap.congr_fun hr₁ (KaehlerDifferential.D k O t)
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, g,
      LinearMap.restrictScalars_apply, TensorProduct.mk_apply, LinearMap.smul_apply,
      smul_eq_mul] at this
    rw [this, inv_mul_cancel₀ hφ]
  have hker : RingHom.ker (algebraMap O L) ≤ IsLocalRing.maximalIdeal O :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  have hu : IsUnit (r₁ (KaehlerDifferential.D k O t)) := by
    by_contra hnu
    have hm : r₁ (KaehlerDifferential.D k O t) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hm' : r₁ (KaehlerDifferential.D k O t) - 1 ∈ IsLocalRing.maximalIdeal O :=
      hker (by rw [RingHom.mem_ker, map_sub, h1, map_one, sub_self])
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      simpa using sub_mem hm hm'
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  refine ⟨(↑hu.unit⁻¹ : O) • r₁, ?_⟩
  rw [LinearMap.smul_apply, smul_eq_mul]
  exact hu.val_inv_mul

/-- **Differentials of the residue field.** In the situation of `exists_retraction_D`, with
`ker(O → L) = (t)` and `Ω_{O/k}` finite free, `dim_L Ω_{L/k} + 1 = rank_O Ω_{O/k}`: the conormal
sequence `0 → (t)/(t²) → L ⊗ Ω_{O/k} → Ω_{L/k} → 0` is exact and its first term is a line. -/
theorem finrank_kaehlerDifferential_add_one [IsDomain O] [Algebra.FormallySmooth k O]
    [Module.Free O Ω[O⁄k]] [Module.Finite O Ω[O⁄k]] [Subsingleton (Algebra.H1Cotangent k L)]
    (hπ : Function.Surjective (algebraMap O L)) {t : O}
    (hker : RingHom.ker (algebraMap O L) = Ideal.span {t})
    (ht2 : t ∉ RingHom.ker (algebraMap O L) ^ 2) :
    Module.finrank L Ω[L⁄k] + 1 = Module.finrank O Ω[O⁄k] := by
  have ht : t ∈ RingHom.ker (algebraMap O L) := hker ▸ Ideal.mem_span_singleton_self t
  have hv := one_tmul_D_ne_zero_of_notMem_sq (k := k) hπ ht ht2
  let f := KaehlerDifferential.mapBaseChange k O L
  have hf := KaehlerDifferential.mapBaseChange_surjective k O L hπ
  have hexact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange k O L hπ
  have hkerf : LinearMap.ker f = L ∙ ((1 : L) ⊗ₜ[O] KaehlerDifferential.D k O t) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨z, rfl⟩ := (hexact y).mp hy
      obtain ⟨⟨x, hx⟩, rfl⟩ := Ideal.toCotangent_surjective _ z
      rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
      rw [hker, Ideal.mem_span_singleton'] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        TensorProduct.tmul_smul]
      refine add_mem (Submodule.smul_of_tower_mem _ _ (Submodule.mem_span_singleton_self _)) ?_
      rw [← algebraMap_smul L t, RingHom.mem_ker.mp ht, zero_smul]
      exact zero_mem _
    · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
      exact (hexact _).mpr ⟨Ideal.toCotangent _ ⟨t, ht⟩, rfl⟩
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hkerf, finrank_span_singleton hv,
    Module.finrank_baseChange] at h1
  exact h1

end Retraction

section ResidueMul

open exteriorPower

variable {k : Type*} [Field k] {O : Type*} [CommRing O] [IsDomain O] [Algebra k O]
  {K : Type*} [Field K] [Algebra k K] [Algebra O K] [IsScalarTower k O K] [IsFractionRing O K]
  {L : Type*} [Field L] [Algebra k L] [Algebra O L] [IsScalarTower k O L]

/-- A one-fold tensor `⨂ₜ v` determines `v`. -/
theorem tprod_fin_one_injective {F M : Type*} [CommRing F] [AddCommGroup M] [Module F M] :
    Function.Injective fun v : M => (⨂ₜ[F] _ : Fin 1, v : ⨂[F]^1 M) := fun v w h => by
  have := congrArg (PiTensorProduct.subsingletonEquiv (R := F) (s := fun _ : Fin 1 => M) 0) h
  simpa using this

/-- **Comparison of two logarithmic frames.** On a line `Ω^{e+1}_{K/k}`, for `O` a valuation ring,
one of the logarithmic forms `ω_i = t_i^{-1} dt_i ∧ dx_i` (`t_i = u_i t₀`) is an `O`-multiple
`c ω_j` of the other, and then the residues satisfy `dx̄_i = c̄ dx̄_j`. -/
theorem exists_frame_comparison [Module.Projective O Ω[O⁄k]] [ValuationRing O] {e : ℕ}
    (hline : Module.finrank K (⋀[K]^(e + 1) Ω[K⁄k]) = 1)
    (hπ : Function.Surjective (algebraMap O L)) {t₀ : O} (ht₀ : algebraMap O L t₀ = 0)
    {r : Ω[O⁄k] →ₗ[O] O} (hr : r (KaehlerDifferential.D k O t₀) = 1) {u₁ u₂ : O}
    (hu₁ : IsUnit u₁) (hu₂ : IsUnit u₂) (x₁ x₂ : Fin e → O) :
    let ω : O → (Fin e → O) → ⋀[K]^(e + 1) Ω[K⁄k] := fun t x =>
      (algebraMap O K t)⁻¹ • ιMulti K (e + 1) (Fin.cons (KaehlerDifferential.D k K
        (algebraMap O K t)) fun i => KaehlerDifferential.D k K (algebraMap O K (x i)))
    let v : (Fin e → O) → ⋀[L]^e Ω[L⁄k] := fun x =>
      ιMulti L e fun i => KaehlerDifferential.D k L (algebraMap O L (x i))
    (∃ c : O, ω (u₂ * t₀) x₂ = algebraMap O K c • ω (u₁ * t₀) x₁ ∧
      v x₂ = algebraMap O L c • v x₁) ∨
    (∃ c : O, ω (u₁ * t₀) x₁ = algebraMap O K c • ω (u₂ * t₀) x₂ ∧
      v x₁ = algebraMap O L c • v x₂) := by
  intro ω v
  have key : ∀ {u u' : O} (hu : IsUnit u) (hu' : IsUnit u') (x x' : Fin e → O) (c : O),
      ω (u' * t₀) x' = algebraMap O K c • ω (u * t₀) x → v x' = algebraMap O L c • v x :=
    fun {u u'} hu hu' x x' c h => by
      have h1 : logPluriForm (O := O) k K 1 e 1 (u' * t₀) x' =
          logPluriForm (O := O) k K 1 e c (u * t₀) x := by
        simp only [logPluriForm, map_one, one_smul]
        change (⨂ₜ[K] _ : Fin 1, ω (u' * t₀) x') = algebraMap O K c • ⨂ₜ[K] _ : Fin 1, ω (u * t₀) x
        rw [h, MMP.Mori.tprod_const_smul, pow_one]
      have h2 := logPluriResidue_eq_of_logPluriForm_eq (L := L) hπ ht₀ hr hu' hu x' x h1
      simp only [logPluriResidue, map_one, one_smul] at h2
      apply tprod_fin_one_injective (F := L)
      change (⨂ₜ[L] _ : Fin 1, v x') = ⨂ₜ[L] _ : Fin 1, algebraMap O L c • v x
      rwa [MMP.Mori.tprod_const_smul, pow_one]
  by_cases h0 : ω (u₁ * t₀) x₁ = 0
  · refine Or.inr ⟨0, by rw [h0, map_zero, zero_smul], ?_⟩
    rw [map_zero, zero_smul]
    have := key hu₂ hu₁ x₂ x₁ 0 (by rw [h0, map_zero, zero_smul])
    rwa [map_zero, zero_smul] at this
  · obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ h0).mp hline (ω (u₂ * t₀) x₂)
    by_cases hc0 : c = 0
    · subst hc0
      have e0 : ω (u₂ * t₀) x₂ = algebraMap O K 0 • ω (u₁ * t₀) x₁ := by
        rw [← hc, map_zero]
      exact Or.inl ⟨0, e0, key hu₁ hu₂ x₁ x₂ 0 e0⟩
    · rcases ValuationRing.isInteger_or_isInteger O c with ⟨c₀, hc₀⟩ | ⟨c₀, hc₀⟩
      · have e2 : ω (u₂ * t₀) x₂ = algebraMap O K c₀ • ω (u₁ * t₀) x₁ := by rw [hc₀, hc]
        exact Or.inl ⟨c₀, e2, key hu₁ hu₂ x₁ x₂ c₀ e2⟩
      · have e1 : ω (u₁ * t₀) x₁ = algebraMap O K c₀ • ω (u₂ * t₀) x₂ := by
          rw [hc₀, ← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        exact Or.inr ⟨c₀, e1, key hu₂ hu₁ x₂ x₁ c₀ e1⟩

/-- **Products of logarithmic pluriforms and of their residues.** On a line `Ω^{e+1}_{K/k}`,
the product of two logarithmic pluriforms is a logarithmic pluriform along one of the two frames,
and its residue is the product of the residues. -/
theorem exists_logPluriForm_mul [Module.Projective O Ω[O⁄k]] [ValuationRing O] {e : ℕ}
    (hline : Module.finrank K (⋀[K]^(e + 1) Ω[K⁄k]) = 1)
    (hπ : Function.Surjective (algebraMap O L)) {t₀ : O} (ht₀ : algebraMap O L t₀ = 0)
    {r : Ω[O⁄k] →ₗ[O] O} (hr : r (KaehlerDifferential.D k O t₀) = 1) {a b : ℕ} (g₁ g₂ : O)
    {u₁ u₂ : O} (hu₁ : IsUnit u₁) (hu₂ : IsUnit u₂) (x₁ x₂ : Fin e → O) :
    ∃ (g u : O) (x : Fin e → O), (u = u₁ ∨ u = u₂) ∧
      pluriFormsMul k K (e + 1) a b (logPluriForm (O := O) k K a e g₁ (u₁ * t₀) x₁)
          (logPluriForm (O := O) k K b e g₂ (u₂ * t₀) x₂) =
        logPluriForm (O := O) k K (a + b) e g (u * t₀) x ∧
      pluriFormsMul k L e a b (logPluriResidue (O := O) k L a e g₁ x₁)
          (logPluriResidue (O := O) k L b e g₂ x₂) =
        logPluriResidue (O := O) k L (a + b) e g x := by
  have hω : ∀ (m : ℕ) (g t : O) (x : Fin e → O), logPluriForm (O := O) k K m e g t x =
      algebraMap O K g • formPow ((algebraMap O K t)⁻¹ • ιMulti K (e + 1)
        (Fin.cons (KaehlerDifferential.D k K (algebraMap O K t))
          fun i => KaehlerDifferential.D k K (algebraMap O K (x i)))) m := fun _ _ _ _ => rfl
  have hv : ∀ (m : ℕ) (g : O) (x : Fin e → O), logPluriResidue (O := O) k L m e g x =
      algebraMap O L g • formPow (ιMulti L e
        fun i => KaehlerDifferential.D k L (algebraMap O L (x i))) m := fun _ _ _ => rfl
  rcases exists_frame_comparison (L := L) hline hπ ht₀ hr hu₁ hu₂ x₁ x₂ with
    ⟨c, hcK, hcL⟩ | ⟨c, hcK, hcL⟩
  · beta_reduce at hcK hcL
    refine ⟨g₁ * (g₂ * c ^ b), u₁, x₁, Or.inl rfl, ?_, ?_⟩
    · rw [hω, hω, hω, hcK, pluriFormsMul_smul_formPow_frame_right]
      congr 1
      simp only [map_mul, map_pow]
    · rw [hv, hv, hv, hcL, pluriFormsMul_smul_formPow_frame_right]
      congr 1
      simp only [map_mul, map_pow]
  · beta_reduce at hcK hcL
    refine ⟨g₁ * c ^ a * g₂, u₂, x₂, Or.inr rfl, ?_, ?_⟩
    · rw [hω, hω, hω, hcK, pluriFormsMul_smul_formPow_frame_left]
      congr 1
      simp only [map_mul, map_pow]
    · rw [hv, hv, hv, hcL, pluriFormsMul_smul_formPow_frame_left]
      congr 1
      simp only [map_mul, map_pow]

end ResidueMul

/-! ### Poincaré residues along a prime divisor -/

section PrimeDivisor

variable {k : Type u} [Field k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y}

/-- The local ring of `Y` at the image of the generic point of `T`, when this is the generic
point of a prime divisor `P`, is a discrete valuation ring, formally smooth over `k`, with free
differentials of rank `trdeg_k k(Y)`, at a point of coheight one. -/
theorem stalk_facts_of_eq_genericPoint [PerfectField k] [LocallyOfFiniteType sY]
    (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra sY
    IsDiscreteValuationRing (Y.presheaf.stalk (j (genericPoint T))) ∧
      Module.Free (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] ∧
      Module.Finite (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] ∧
      Algebra.FormallySmooth k (Y.presheaf.stalk (j (genericPoint T))) ∧
      Order.coheight (j (genericPoint T)) = 1 ∧
      Module.finrank (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] = (Algebra.trdeg k Y.functionField).toNat := by
  rw [hP]
  exact ⟨P.isDiscreteValuationRing_localRing, (P.free_kaehlerDifferential_localRing (sX := sY)).1,
    (P.free_kaehlerDifferential_localRing (sX := sY)).2, (P.formallySmooth_localRing (sX := sY)).1,
    P.coheight_genericPoint, P.finrank_kaehlerDifferential_localRing (sX := sY)⟩

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The restriction `𝒪_{Y,T} → k(T)` along a closed immersion is a surjective `k`-algebra map. -/
theorem stalkMap_facts_of_isClosedImmersion [IsClosedImmersion j] :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j (genericPoint T))) T.functionField ∧
      Function.Surjective (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  refine ⟨IsScalarTower.of_algebraMap_eq' ?_, SurjectiveOnStalks.stalkMap_surjective j _⟩
  have h : (Scheme.ΓSpecIso (.of k)).inv ≫ (j ≫ sY).appTop ≫
        T.presheaf.germ ⊤ (genericPoint T) (TopologicalSpace.Opens.mem_top _) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫
        Y.presheaf.germ ⊤ (j (genericPoint T)) (TopologicalSpace.Opens.mem_top _)) ≫
        j.stalkMap (genericPoint T) := by
    simp only [Category.assoc, Scheme.Hom.germ_stalkMap, Scheme.Hom.comp_appTop]
    rfl
  exact congrArg CommRingCat.Hom.hom h

/-- **Uniformizers along a prime divisor**: for a closed immersion `j : T ⟶ Y` sending the generic
point of `T` to that of a prime divisor `P`, a uniformizer `ϖ` of `𝒪_{Y,T}` with a retraction
`r(dϖ) = 1`; every element of order one is a unit multiple of `ϖ`. -/
theorem exists_uniformizer_of_eq_genericPoint [PerfectField k] [LocallyOfFiniteType sY]
    [IsClosedImmersion j] (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    ∃ (ϖ : Y.presheaf.stalk (j (genericPoint T)))
      (r : Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] →ₗ[Y.presheaf.stalk (j (genericPoint T))]
        Y.presheaf.stalk (j (genericPoint T))),
      algebraMap _ T.functionField ϖ = 0 ∧ r (KaehlerDifferential.D k _ ϖ) = 1 ∧
      RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) =
        Ideal.span {ϖ} ∧
      ϖ ∉ RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) ^ 2 ∧
      ∀ t : Y.presheaf.stalk (j (genericPoint T)),
        Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 →
          ∃ u, IsUnit u ∧ t = u * ϖ := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨hdvr, hfree, hfin, hsm, hcoh, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨htow, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sY) (j := j)
  have := essFiniteType_functionField (sX := j ≫ sY)
  obtain ⟨ϖ, hϖ⟩ :=
    IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk (j (genericPoint T)))
  have hker : RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) =
      Ideal.span {ϖ} :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hsurj)).trans
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ)
  have hϖ2 :
      ϖ ∉ RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) ^ 2 := by
    rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    have h1 : ϖ * 1 = ϖ * (ϖ * c) := by rw [mul_one, ← mul_assoc, ← pow_two]; exact hc
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one c (mul_left_cancel₀ hϖ.ne_zero h1).symm)
  obtain ⟨r, hr⟩ := exists_retraction_D (k := k) hsurj (hker ▸ Ideal.mem_span_singleton_self ϖ) hϖ2
  refine ⟨ϖ, r, RingHom.mem_ker.mp (hker ▸ Ideal.mem_span_singleton_self ϖ), hr, hker, hϖ2,
    fun t ht => ?_⟩
  have ht0 : algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField t ≠ 0 := by
    intro h
    rw [h] at ht
    have := congrFun Scheme.ord_zero (j (genericPoint T))
    simp only [Pi.zero_apply] at this
    omega
  have h1 := (Scheme.ord_eq_iff hcoh ht0).mp ht
  have h2 : Ring.ordFrac (Y.presheaf.stalk (j (genericPoint T)))
      (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ) = WithZero.exp 1 :=
    Ring.ordFrac_irreducible hϖ
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := (Y.presheaf.stalk (j (genericPoint T))))
    (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ϖ)
    (algebraMap (Y.presheaf.stalk (j (genericPoint T))) Y.functionField t) (h2.trans h1.symm)
  refine ⟨u, u.isUnit,
    IsFractionRing.injective (Y.presheaf.stalk (j (genericPoint T))) Y.functionField ?_⟩
  rw [← hu, map_mul, Units.smul_def, Algebra.smul_def]

/-- **Uniqueness of the Poincaré residue** along a closed immersion `j : T ⟶ Y` of an integral
scheme sending the generic point of `T` to that of a prime divisor `P` of the normal variety `Y`
over a perfect field: any two residues of the same form agree. -/
theorem IsPoincareResidue.unique_of_isClosedImmersion [PerfectField k] [LocallyOfFiniteType sY]
    [IsClosedImmersion j] (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m} {ρ ρ' : RationalPluriForms (j ≫ sY) n m}
    (h : IsPoincareResidue sY j n m τ ρ) (h' : IsPoincareResidue sY j n m τ ρ') : ρ = ρ' := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, -, -, -, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨htow, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sY) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, -, -, hunif⟩ := exists_uniformizer_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨t₁, g₁, x₁, ht₁, hτ₁, rfl⟩ := h
  obtain ⟨t₂, g₂, x₂, ht₂, hτ₂, rfl⟩ := h'
  obtain ⟨u₁, hu₁, rfl⟩ := hunif t₁ ht₁
  obtain ⟨u₂, hu₂, rfl⟩ := hunif t₂ ht₂
  exact logPluriResidue_eq_of_logPluriForm_eq hsurj hϖ0 hr hu₁ hu₂ x₁ x₂ (hτ₁.symm.trans hτ₂)

/-- **Multiplicativity of the Poincaré residue** along a closed immersion `j : T ⟶ Y` of an
integral scheme sending the generic point of `T` to that of a prime divisor `P` of the normal
variety `Y` of dimension `n + 1` over a perfect field: `Res(τ₁ τ₂) = Res(τ₁) Res(τ₂)`. -/
theorem IsPoincareResidue.mul_of_isClosedImmersion [PerfectField k] [LocallyOfFiniteType sY]
    [IsClosedImmersion j] (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint)
    {n a b : ℕ} (hY : topologicalKrullDim Y = n + 1)
    {τ₁ : RationalPluriForms sY (n + 1) a} {τ₂ : RationalPluriForms sY (n + 1) b}
    {ρ₁ : RationalPluriForms (j ≫ sY) n a} {ρ₂ : RationalPluriForms (j ≫ sY) n b}
    (h₁ : IsPoincareResidue sY j n a τ₁ ρ₁) (h₂ : IsPoincareResidue sY j n b τ₂ ρ₂) :
    IsPoincareResidue sY j n (a + b) (RationalPluriForms.mul sY (n + 1) a b τ₁ τ₂)
      (RationalPluriForms.mul (j ≫ sY) n a b ρ₁ ρ₂) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  have := isScalarTower_stalk_functionField sY (j (genericPoint T))
  obtain ⟨hdvr, hfree, -, -, -, -⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨htow, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sY) (j := j)
  obtain ⟨ϖ, r, hϖ0, hr, -, -, hunif⟩ := exists_uniformizer_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨b₀⟩ := exists_basis_topForms (sX := sY) (by exact_mod_cast hY)
  have hline : Module.finrank Y.functionField (⋀[Y.functionField]^(n + 1) Ω[Y.functionField⁄k]) =
      1 := by rw [Module.finrank_eq_card_basis b₀, Fintype.card_unit]
  obtain ⟨t₁, g₁, x₁, ht₁, hτ₁, rfl⟩ := h₁
  obtain ⟨t₂, g₂, x₂, ht₂, hτ₂, rfl⟩ := h₂
  obtain ⟨u₁, hu₁, rfl⟩ := hunif t₁ ht₁
  obtain ⟨u₂, hu₂, rfl⟩ := hunif t₂ ht₂
  obtain ⟨g, u, x, hu, hK, hL⟩ := exists_logPluriForm_mul (a := a) (b := b) hline hsurj hϖ0 hr
    g₁ g₂ hu₁ hu₂ x₁ x₂
  refine ⟨u * ϖ, g, x, ?_, hτ₁ ▸ hτ₂ ▸ hK, hL.symm ▸ rfl⟩
  rcases hu with rfl | rfl <;> assumption

/-- **Transcendence degree along a prime divisor**: `trdeg_k k(T) + 1 = trdeg_k k(Y)` for a closed
immersion `j : T ⟶ Y` of an integral scheme sending the generic point of `T` to that of a prime
divisor `P` of the normal variety `Y`. -/
theorem trdeg_add_one_of_eq_genericPoint [PerfectField k] [LocallyOfFiniteType sY]
    [IsClosedImmersion j] (P : Mori.PrimeDivisor Y) (hP : j (genericPoint T) = P.genericPoint) :
    (letI := functionFieldAlgebra (j ≫ sY); (Algebra.trdeg k T.functionField).toNat) + 1 =
      (letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat) := by
  let := stalkAlgebra sY (j (genericPoint T))
  let := functionFieldAlgebra sY
  let := functionFieldAlgebra (j ≫ sY)
  let : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
    (j.stalkMap (genericPoint T)).hom.toAlgebra
  obtain ⟨hdvr, hfree, hfin, hsm, -, hrank⟩ := stalk_facts_of_eq_genericPoint (sY := sY) P hP
  obtain ⟨htow, hsurj⟩ := stalkMap_facts_of_isClosedImmersion (sY := sY) (j := j)
  obtain ⟨ϖ, r, -, -, hker, hϖ2, -⟩ := exists_uniformizer_of_eq_genericPoint (sY := sY) P hP
  have := essFiniteType_functionField (sX := j ≫ sY)
  have h := finrank_kaehlerDifferential_add_one (k := k) hsurj hker hϖ2
  rwa [hrank, finrank_kaehlerDifferential_eq_trdeg] at h

end PrimeDivisor

/-! ### Poincaré residues along an adjunction step -/

section AdjunctionStep

variable {k : Type u} [Field k] {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y]
  [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral T] {j : T ⟶ Y} {BY : QDivisor Y}
  {BT : QDivisor T}

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The image of the generic point of an adjunction stratum is the generic point of the prime
divisor it lies on. -/
theorem IsAdjunctionStep.exists_primeDivisor (hj : IsAdjunctionStep sY BY j BT) :
    ∃ P : Mori.PrimeDivisor Y, j (genericPoint T) = P.genericPoint ∧ IsClosedImmersion j := by
  obtain ⟨-, P, -, hrange, hci, -⟩ := hj
  refine ⟨P, ?_, hci⟩
  have h1 : closure ({j (genericPoint T)} : Set Y) = Set.range j.base := by
    apply le_antisymm
    · rw [hrange]
      exact (AlgebraicGeometry.PrimeDivisor.support_eq_closure P ▸
        isClosed_closure).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hrange ▸ Set.mem_range_self _))
    · rintro _ ⟨z, rfl⟩
      have hz : genericPoint T ⤳ z := (genericPoint_spec T).specializes trivial
      exact specializes_iff_mem_closure.mp (hz.map j.continuous)
  have h2 : closure ({j (genericPoint T)} : Set Y) = closure {P.genericPoint} := by
    rw [h1, hrange, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact (inseparable_iff_closure_eq.mpr h2).eq

/-- The local ring of `Y` along an adjunction stratum `T` is a discrete valuation ring, formally
smooth over `k`, with free differentials of rank `trdeg_k k(Y)`, at a point of coheight one. -/
theorem IsAdjunctionStep.stalk_facts [PerfectField k] [LocallyOfFiniteType sY]
    (hj : IsAdjunctionStep sY BY j BT) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra sY
    IsDiscreteValuationRing (Y.presheaf.stalk (j (genericPoint T))) ∧
      Module.Free (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] ∧
      Module.Finite (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] ∧
      Algebra.FormallySmooth k (Y.presheaf.stalk (j (genericPoint T))) ∧
      Order.coheight (j (genericPoint T)) = 1 ∧
      Module.finrank (Y.presheaf.stalk (j (genericPoint T)))
        Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] = (Algebra.trdeg k Y.functionField).toNat :=
  have ⟨P, hP, _⟩ := hj.exists_primeDivisor
  stalk_facts_of_eq_genericPoint P hP

omit [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] in
/-- The restriction `𝒪_{Y,T} → k(T)` along an adjunction stratum is a surjective `k`-algebra
map. -/
theorem IsAdjunctionStep.stalkMap_facts (hj : IsAdjunctionStep sY BY j BT) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    IsScalarTower k (Y.presheaf.stalk (j (genericPoint T))) T.functionField ∧
      Function.Surjective (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) :=
  have ⟨_, _, _⟩ := hj.exists_primeDivisor
  stalkMap_facts_of_isClosedImmersion

/-- **Uniformizers along an adjunction stratum**: a uniformizer `ϖ` of `𝒪_{Y,T}` with a
retraction `r(dϖ) = 1`; every element of order one is a unit multiple of `ϖ`. -/
theorem IsAdjunctionStep.exists_uniformizer [PerfectField k] [LocallyOfFiniteType sY]
    (hj : IsAdjunctionStep sY BY j BT) :
    letI := stalkAlgebra sY (j (genericPoint T))
    letI := functionFieldAlgebra (j ≫ sY)
    letI : Algebra (Y.presheaf.stalk (j (genericPoint T))) T.functionField :=
      (j.stalkMap (genericPoint T)).hom.toAlgebra
    ∃ (ϖ : Y.presheaf.stalk (j (genericPoint T)))
      (r : Ω[(Y.presheaf.stalk (j (genericPoint T)))⁄k] →ₗ[Y.presheaf.stalk (j (genericPoint T))]
        Y.presheaf.stalk (j (genericPoint T))),
      algebraMap _ T.functionField ϖ = 0 ∧ r (KaehlerDifferential.D k _ ϖ) = 1 ∧
      RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) =
        Ideal.span {ϖ} ∧
      ϖ ∉ RingHom.ker (algebraMap (Y.presheaf.stalk (j (genericPoint T))) T.functionField) ^ 2 ∧
      ∀ t : Y.presheaf.stalk (j (genericPoint T)),
        Y.ord (algebraMap _ Y.functionField t) (j (genericPoint T)) = 1 →
          ∃ u, IsUnit u ∧ t = u * ϖ :=
  have ⟨P, hP, _⟩ := hj.exists_primeDivisor
  exists_uniformizer_of_eq_genericPoint P hP

/-- **Uniqueness of the Poincaré residue** along an adjunction step `T ⊂ Y` of a normal variety
over a perfect field: any two residues of the same form agree. -/
theorem IsPoincareResidue.unique [PerfectField k] [LocallyOfFiniteType sY]
    (hj : IsAdjunctionStep sY BY j BT) {n m : ℕ} {τ : RationalPluriForms sY (n + 1) m}
    {ρ ρ' : RationalPluriForms (j ≫ sY) n m} (h : IsPoincareResidue sY j n m τ ρ)
    (h' : IsPoincareResidue sY j n m τ ρ') : ρ = ρ' :=
  have ⟨P, hP, _⟩ := hj.exists_primeDivisor
  unique_of_isClosedImmersion P hP h h'

/-- **Multiplicativity of the Poincaré residue** along an adjunction step `T ⊂ Y`, `Y` a normal
variety of dimension `n + 1` over a perfect field: `Res(τ₁ τ₂) = Res(τ₁) Res(τ₂)`. -/
theorem IsPoincareResidue.mul [PerfectField k] [LocallyOfFiniteType sY]
    (hj : IsAdjunctionStep sY BY j BT) {n a b : ℕ} (hY : topologicalKrullDim Y = n + 1)
    {τ₁ : RationalPluriForms sY (n + 1) a} {τ₂ : RationalPluriForms sY (n + 1) b}
    {ρ₁ : RationalPluriForms (j ≫ sY) n a} {ρ₂ : RationalPluriForms (j ≫ sY) n b}
    (h₁ : IsPoincareResidue sY j n a τ₁ ρ₁) (h₂ : IsPoincareResidue sY j n b τ₂ ρ₂) :
    IsPoincareResidue sY j n (a + b) (RationalPluriForms.mul sY (n + 1) a b τ₁ τ₂)
      (RationalPluriForms.mul (j ≫ sY) n a b ρ₁ ρ₂) :=
  have ⟨P, hP, _⟩ := hj.exists_primeDivisor
  mul_of_isClosedImmersion P hP hY h₁ h₂

/-- **Transcendence degree along an adjunction step**: `trdeg_k k(T) + 1 = trdeg_k k(Y)`. -/
theorem IsAdjunctionStep.trdeg_add_one [PerfectField k] [LocallyOfFiniteType sY]
    (hj : IsAdjunctionStep sY BY j BT) :
    (letI := functionFieldAlgebra (j ≫ sY); (Algebra.trdeg k T.functionField).toNat) + 1 =
      (letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat) :=
  have ⟨P, hP, _⟩ := hj.exists_primeDivisor
  trdeg_add_one_of_eq_genericPoint P hP

end AdjunctionStep

/-! ### Iterated residues: uniqueness, multiplicativity and dimension of strata -/

section IteratedResidue

/-- The dimension of an integral scheme locally of finite type over `k` is the transcendence
degree of its function field, a natural number. -/
theorem topologicalKrullDim_eq_toNat_trdeg {k : Type u} [Field k] {Y : Scheme.{u}}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] :
    topologicalKrullDim Y =
      ((letI := functionFieldAlgebra sY; (Algebra.trdeg k Y.functionField).toNat : ℕ) :
        WithBot ℕ∞) := by
  let := functionFieldAlgebra sY
  have := essFiniteType_functionField (sX := sY)
  rw [← toENat_trdeg_functionField (sX := sY)]
  conv_lhs =>
    rw [← Cardinal.cast_toNat_of_lt_aleph0 (trdeg_lt_aleph0 (K := k) (L := Y.functionField))]
  rw [Cardinal.toENat_nat]
  rfl

/-- **Dimension along an adjunction step**: if `T ⊂ Y` is an adjunction step and `dim T = e`,
then `dim Y = e + 1`. -/
theorem IsAdjunctionStep.topologicalKrullDim_eq_add_one {k : Type u} [Field k] [PerfectField k]
    {Y T : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [IsIntegral T] {j : T ⟶ Y} {BY : QDivisor Y} {BT : QDivisor T}
    [LocallyOfFiniteType sY] [LocallyOfFiniteType (j ≫ sY)] (hj : IsAdjunctionStep sY BY j BT)
    {e : ℕ} (hT : topologicalKrullDim T = e) : topologicalKrullDim Y = (e + 1 : ℕ) := by
  have h2 := topologicalKrullDim_eq_toNat_trdeg (j ≫ sY)
  rw [hT] at h2
  have : e = (letI := functionFieldAlgebra (j ≫ sY)
      (Algebra.trdeg k T.functionField).toNat) := by exact_mod_cast h2
  rw [topologicalKrullDim_eq_toNat_trdeg sY, ← hj.trdeg_add_one, ← this]

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X}

omit [IsIntegral X] in
/-- **The dimension of a stratum**: the final stratum of a flag of length `ℓ` on a variety of
dimension `n` has dimension `n - ℓ`. -/
theorem StratumAdjunctionData.dim_add_length [CharZero k] {n : ℕ} (hX : topologicalKrullDim X = n)
    {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ}, topologicalKrullDim S = e → e + F.length = n := by
  induction F with
  | refl h =>
    intro e hS
    rw [hX] at hS
    simp only [StratumAdjunctionData.length, add_zero]
    exact_mod_cast hS.symm
  | @step S T ι BS F j BT hj ih =>
    intro e hT
    have := F.isIntegral_stratum
    have := F.isNormal_stratum
    have := F.isLocallyNoetherian_stratum
    have : IsIntegral T := hj.1.1.toIsIntegral
    have : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    have : LocallyOfFiniteType (j ≫ ι ≫ sX) := hj.1.1.toLocallyOfFiniteType
    have := ih (hj.topologicalKrullDim_eq_add_one hT)
    simp only [StratumAdjunctionData.length]
    omega

/-- The iterated residue relation, unfolded by recursion on the flag. -/
def IsIteratedResidueRec {n m : ℕ} (τ : RationalPluriForms sX n m) :
    ∀ {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS)
      (e : ℕ), @RationalPluriForms k _ S (ι ≫ sX) F.isIntegral_stratum e m → Prop
  | _, _, _, .refl _, e, ρ => n = e ∧ HEq ρ τ
  | _, _, _, .step (S := S) (T := T) (ι := ι) F j _ hj, e, ρ =>
      ∃ ρ₀ : @RationalPluriForms k _ S (ι ≫ sX) F.isIntegral_stratum (e + 1) m,
        IsIteratedResidueRec τ F (e + 1) ρ₀ ∧
        ∃ ρ' : @RationalPluriForms k _ T (j ≫ ι ≫ sX) hj.1.1.toIsIntegral e m,
          @IsPoincareResidue k _ S T (ι ≫ sX) F.isIntegral_stratum F.isLocallyNoetherian_stratum
            hj.1.1.toIsIntegral j e m ρ₀ ρ' ∧ HEq ρ ρ'

/-- An iterated residue satisfies the relation unfolded along the flag. -/
theorem IsIteratedResidue.rec' {n m : ℕ} {τ : RationalPluriForms sX n m} {S : Scheme.{u}}
    {ι : S ⟶ X} {BS : QDivisor S} [IsIntegral S] {F : StratumAdjunctionData sX B ι BS} {e : ℕ}
    {ρ : RationalPluriForms (ι ≫ sX) e m} (h : IsIteratedResidue sX B τ F e ρ) :
    IsIteratedResidueRec τ F e ρ := by
  induction h with
  | refl hp => exact ⟨rfl, cast_heq _ _⟩
  | step hF hr ih => exact ⟨_, ih, _, hr, cast_heq _ _⟩

/-- The relation unfolded along the flag gives an iterated residue. -/
theorem IsIteratedResidue.of_rec {n m : ℕ} {τ : RationalPluriForms sX n m} {S : Scheme.{u}}
    {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ} {ρ : @RationalPluriForms k _ S (ι ≫ sX) F.isIntegral_stratum e m},
      IsIteratedResidueRec τ F e ρ →
        @IsIteratedResidue k _ X sX _ _ _ B n m τ S ι BS F.isIntegral_stratum F e ρ := by
  induction F with
  | refl hp =>
    rintro e ρ ⟨rfl, h⟩
    have : ρ = cast (by rw [Category.id_comp]) τ := eq_of_heq (h.trans (cast_heq _ τ).symm)
    subst this
    exact IsIteratedResidue.refl hp
  | @step S T ι BS F j BT hj ih =>
    rintro e ρ ⟨ρ₀, h₀, ρ', hr, hρ⟩
    have := F.isIntegral_stratum
    have := F.isLocallyNoetherian_stratum
    have : IsIntegral T := hj.1.1.toIsIntegral
    have h1 := ih h₀
    have : ρ = cast (by rw [Category.assoc]) ρ' := eq_of_heq (hρ.trans (cast_heq _ ρ').symm)
    subst this
    exact IsIteratedResidue.step h1 hr

omit [IsLocallyNoetherian X] [IsNormal X] in
/-- Products of rational pluriforms do not depend on the structure morphism beyond equality. -/
theorem RationalPluriForms.mul_heq {s s' : X ⟶ Spec (.of k)} (h : s = s') {d a b : ℕ}
    {x₁ : RationalPluriForms s d a} {y₁ : RationalPluriForms s' d a}
    {x₂ : RationalPluriForms s d b} {y₂ : RationalPluriForms s' d b} (h₁ : HEq x₁ y₁)
    (h₂ : HEq x₂ y₂) :
    HEq (RationalPluriForms.mul s d a b x₁ x₂) (RationalPluriForms.mul s' d a b y₁ y₂) := by
  subst h
  rw [eq_of_heq h₁, eq_of_heq h₂]

/-- Uniqueness of iterated residues, in the unfolded form. -/
theorem IsIteratedResidueRec.unique [CharZero k] {n m : ℕ} {τ : RationalPluriForms sX n m}
    {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ} {ρ ρ' : @RationalPluriForms k _ S (ι ≫ sX) F.isIntegral_stratum e m},
      IsIteratedResidueRec τ F e ρ → IsIteratedResidueRec τ F e ρ' → ρ = ρ' := by
  induction F with
  | refl hp =>
    rintro e ρ ρ' ⟨-, h⟩ ⟨-, h'⟩
    exact eq_of_heq (h.trans h'.symm)
  | @step S T ι BS F j BT hj ih =>
    rintro e ρ ρ' ⟨ρ₀, h₀, σ, hr, hρ⟩ ⟨ρ₀', h₀', σ', hr', hρ'⟩
    have := F.isIntegral_stratum
    have := F.isNormal_stratum
    have := F.isLocallyNoetherian_stratum
    have : IsIntegral T := hj.1.1.toIsIntegral
    have : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    have h1 := ih h₀ h₀'
    subst h1
    have h2 := IsPoincareResidue.unique hj hr hr'
    subst h2
    exact eq_of_heq (hρ.trans hρ'.symm)

/-- **Uniqueness of iterated residues**: along a flag of strata of a rational pair, a form has
at most one iterated residue. -/
theorem IsIteratedResidue.unique [CharZero k] {n m : ℕ} {τ : RationalPluriForms sX n m}
    {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} [IsIntegral S]
    {F : StratumAdjunctionData sX B ι BS} {e : ℕ} {ρ ρ' : RationalPluriForms (ι ≫ sX) e m}
    (h : IsIteratedResidue sX B τ F e ρ)
    (h' : IsIteratedResidue sX B τ F e ρ') : ρ = ρ' :=
  IsIteratedResidueRec.unique F h.rec' h'.rec'

/-- Multiplicativity of iterated residues, in the unfolded form. -/
theorem IsIteratedResidueRec.mul [CharZero k] {n a b : ℕ} {τ₁ : RationalPluriForms sX n a}
    {τ₂ : RationalPluriForms sX n b} {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S}
    (F : StratumAdjunctionData sX B ι BS) :
    ∀ {e : ℕ} {ρ₁ : @RationalPluriForms k _ S (ι ≫ sX) F.isIntegral_stratum e a}
      {ρ₂ : @RationalPluriForms k _ S (ι ≫ sX) F.isIntegral_stratum e b},
      topologicalKrullDim S = e → IsIteratedResidueRec τ₁ F e ρ₁ →
        IsIteratedResidueRec τ₂ F e ρ₂ →
        IsIteratedResidueRec (RationalPluriForms.mul sX n a b τ₁ τ₂) F e
          (@RationalPluriForms.mul k _ S (ι ≫ sX) F.isIntegral_stratum e a b ρ₁ ρ₂) := by
  induction F with
  | refl hp =>
    rintro e ρ₁ ρ₂ - ⟨he, h₁⟩ ⟨-, h₂⟩
    subst he
    exact ⟨rfl, RationalPluriForms.mul_heq (Category.id_comp sX) h₁ h₂⟩
  | @step S T ι BS F j BT hj ih =>
    rintro e ρ₁ ρ₂ hT ⟨ρ₁₀, h₁₀, σ₁, hr₁, hρ₁⟩ ⟨ρ₂₀, h₂₀, σ₂, hr₂, hρ₂⟩
    have := F.isIntegral_stratum
    have := F.isNormal_stratum
    have := F.isLocallyNoetherian_stratum
    have : IsIntegral T := hj.1.1.toIsIntegral
    have : LocallyOfFiniteType (ι ≫ sX) := F.isNormalVariety.1.toLocallyOfFiniteType
    have : LocallyOfFiniteType (j ≫ ι ≫ sX) := hj.1.1.toLocallyOfFiniteType
    have hS := hj.topologicalKrullDim_eq_add_one hT
    refine ⟨_, ih hS h₁₀ h₂₀, _, IsPoincareResidue.mul hj (by exact_mod_cast hS) hr₁ hr₂, ?_⟩
    exact RationalPluriForms.mul_heq (Category.assoc j ι sX) hρ₁ hρ₂

/-- **Multiplicativity of iterated residues**: along a flag ending at a stratum of dimension `e`,
the iterated residue of a product is the product of the iterated residues. -/
theorem IsIteratedResidue.mul [CharZero k] {n a b : ℕ} {τ₁ : RationalPluriForms sX n a}
    {τ₂ : RationalPluriForms sX n b} {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S}
    [IsIntegral S] {F : StratumAdjunctionData sX B ι BS} {e : ℕ}
    {ρ₁ : RationalPluriForms (ι ≫ sX) e a} {ρ₂ : RationalPluriForms (ι ≫ sX) e b}
    (h₁ : IsIteratedResidue sX B τ₁ F e ρ₁) (h₂ : IsIteratedResidue sX B τ₂ F e ρ₂)
    (hS : topologicalKrullDim S = e) :
    IsIteratedResidue sX B (RationalPluriForms.mul sX n a b τ₁ τ₂) F e
      (RationalPluriForms.mul (ι ≫ sX) e a b ρ₁ ρ₂) :=
  IsIteratedResidue.of_rec F (IsIteratedResidueRec.mul F hS h₁.rec' h₂.rec')

end IteratedResidue

end MMP.Fourfold
