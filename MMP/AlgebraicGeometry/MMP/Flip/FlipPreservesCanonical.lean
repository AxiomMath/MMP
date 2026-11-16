module

public import Mathlib
public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.MMP.MinimalModel.DiscrepancyComparison
import MMP.AlgebraicGeometry.Singularities.DiscrepancyBirationalTransform
import MMP.AlgebraicGeometry.Cohomology.Duality.AdjunctionSequence
import MMP.AlgebraicGeometry.MMP.Abundance.Basic
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.LocalGenerator
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOver
import MMP.AlgebraicGeometry.Positivity.SemiampleDescent
import MMP.AlgebraicGeometry.Positivity.RelativeAmpleContractedCurve
import MMP.AlgebraicGeometry.Resolution.Surface.NegativeDefinite.LogDiscrepancyVector
import MMP.AlgebraicGeometry.Intersection.CurveDegreeProjection
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
import StacksFrontier.AlgebraicGeometry.Algebraization.CurveThroughPoints
import MMP.AlgebraicGeometry.Divisor.DivisorialSheafIso
import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.Divisor.DivisorialPullback
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Singularities.SmallModelCrepant

/-!
# Discrepancies under flips

Let `φ : X ⟶ Z` be a small contraction with `-(K_X + D)` `φ`-ample and `φ⁺ : X⁺ ⟶ Z`, with
birational map `g : X ⤏ X⁺`, a flip of `φ` with respect to `K_X + D`. Put `D⁺ = g_*D` and
`K_{X⁺} = g_*K_X`. This file proves that discrepancies do not decrease across the flip:

* if `(X, D)` is a canonical pair, so is `(X⁺, D⁺)`;
* `K_{X⁺}` is a canonical divisor, `K_{X⁺} + D⁺` is `ℚ`-Cartier, and the set `𝒮_t(X⁺, D⁺)` of
  valuations of log discrepancy below `t` is contained in `𝒮_t(X, D)`, the function fields
  `k(X)` and `k(X⁺)` being identified over `k(Z)`.

Since `φ` and `φ⁺` are isomorphisms in codimension one, `g`, `φ⁻¹` and `(φ⁺)⁻¹` induce
bijections of prime divisors compatible with the divisorial valuations over `k(Z)`, and a divisor
of `k(Z)` is exceptional with nonempty center on `X` exactly when it is so on `X⁺`. The canonical
divisor `g_*K_X` agrees with `K_X` off closed subsets of codimension two, and an isomorphism of
divisorial sheaves on the smooth locus extends across codimension two. The discrepancies are
compared on a common normal model `W` on which the divisor is a prime divisor `P₀`: the
difference of the pull-backs of `K_X + D` and `K_{X⁺} + D⁺` is nef over `Z` and has no component
that is not exceptional over `Z`, so the negativity lemma makes its coefficient along `P₀`
nonnegative.

## Main results

* `MMP.Flips.IsCanonicalPair.of_isFlip`: flips preserve canonical pairs.
* `MMP.Flips.smallLogDiscrepancySet_subset_of_isFlip`: sets of small log discrepancy shrink under
  flips.

## Implementation notes

The valuations in `𝒮_t(X⁺, D⁺)` and `𝒮_t(X, D)` live on the different fields `k(X⁺)` and
`k(X)`. A valuation `ν⁺` of `k(X⁺)` is identified with the valuation `ν` of `k(X)` satisfying
`ν ∘ φ^* = ν⁺ ∘ φ⁺^*` on `k(Z)`; such a `ν` exists, and the inclusion is stated for every such `ν`.

The comparison of discrepancies is proved here over an arbitrary ground field. The discrepancy on
`X` is computed with the form `ω = φ^*ω_Z` for `ω_Z` the form on `Z` with `φ⁺^*ω_Z = ω⁺`, and with
the presentation of `K_X + D` by a Cartier multiple; the order of a pulled-back form along a
divisor, and the multiplicity of a Cartier divisor along it, depend only on the valuation of the
divisor, whether or not `Ω^n` of the local ring is a line. When `Ω^n_{k(Z)/k}` is not a line
every order of a form vanishes, so `K_X = 0` and any nonzero form computes the discrepancy.
Preservation of canonical pairs needs a perfect ground field, over which every normal variety has
a canonical divisor and the divisor of every nonzero top form is canonical.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.28, p. 63,
  4.12.4
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped WithZero

universe u

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Flips

open MMP.Mori MMP.Threefold.Mori.Helpers

section Transport

variable {k : Type*} [CommRing k] {d : ℕ} {m : ℤ}

/-- Along a bijective map of fields over `k`, top forms map injectively. -/
private theorem topFormsMap_injective_of_bijective {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    (h : Function.Bijective (algebraMap K K')) :
    Function.Injective (topFormsMap k K K' d) := by
  let e := RingEquiv.ofBijective (algebraMap K K') h
  letI : Algebra K' K := e.symm.toRingHom.toAlgebra
  have he : ∀ x, algebraMap K' K (algebraMap K K' x) = x := e.symm_apply_apply
  haveI : IsScalarTower k K' K := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k K K' c, he]
  haveI : IsScalarTower K K' K := IsScalarTower.of_algebraMap_eq fun x => (he x).symm
  intro x y hxy
  have := congrArg (topFormsMap k K' K d) hxy
  rw [topFormsMap_comp, topFormsMap_comp] at this
  have hid : ∀ z, topFormsMap k K K d z = z := fun z =>
    MMP.Mori.topFormsMap_eq_self (k := k) (RingHom.id K) (fun _ => rfl) z
  rwa [hid, hid] at this

/-- A ring isomorphism `A ≅ A'` makes `A'` the localization of `A` at `⊥`. -/
private theorem isLocalization_bot_of_bijective {A A' : Type*} [CommRing A] [CommRing A']
    [Algebra A A'] (hA : Function.Bijective (algebraMap A A')) :
    IsLocalization (⊥ : Submonoid A) A' := by
  let e : A ≃ₐ[A] A' := AlgEquiv.ofBijective (Algebra.ofId A A') hA
  exact (IsLocalization.isLocalization_iff_of_algEquiv (⊥ : Submonoid A) e).mp
    (IsLocalization.self (R := A) (M := ⊥) (fun x hx => by
      rw [Submonoid.mem_bot.mp hx]
      exact isUnit_one))

/-- A generator of the line `Ω^d_{K/k}` is a pull-back generator along an isomorphism of fields. -/
private theorem isPullbackGenerator_of_bijective {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    (h : Function.Bijective (algebraMap K K')) {ω : ⋀[K]^d Ω[K⁄k]}
    (hω : Submodule.span K {ω} = ⊤) (h0 : ω ≠ 0) : IsPullbackGenerator K' ω := by
  letI := isLocalization_bot_of_bijective h
  exact ⟨hω, span_singleton_topFormsMap (⊥ : Submonoid K) hω, fun h' =>
    h0 (topFormsMap_injective_of_bijective h (by rw [h', map_zero]))⟩

/-- Along an isomorphism of fields, a line of top forms is carried to a line. -/
private theorem exists_span_eq_top_of_bijective {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    (h : Function.Bijective (algebraMap K K'))
    (hl : ∃ ω : ⋀[K]^d Ω[K⁄k], Submodule.span K {ω} = ⊤ ∧ ω ≠ 0) :
    ∃ ω : ⋀[K']^d Ω[K'⁄k], Submodule.span K' {ω} = ⊤ ∧ ω ≠ 0 := by
  obtain ⟨ω, hω, h0⟩ := hl
  exact ⟨_, (isPullbackGenerator_of_bijective h hω h0).2⟩

/-- Conversely, along an isomorphism of fields, a line of top forms comes from a line. -/
private theorem exists_span_eq_top_of_bijective' {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    (h : Function.Bijective (algebraMap K K'))
    (hl : ∃ ω : ⋀[K']^d Ω[K'⁄k], Submodule.span K' {ω} = ⊤ ∧ ω ≠ 0) :
    ∃ ω : ⋀[K]^d Ω[K⁄k], Submodule.span K {ω} = ⊤ ∧ ω ≠ 0 := by
  let e := RingEquiv.ofBijective (algebraMap K K') h
  letI : Algebra K' K := e.symm.toRingHom.toAlgebra
  have he : ∀ x, algebraMap K' K (algebraMap K K' x) = x := e.symm_apply_apply
  haveI : IsScalarTower k K' K := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k K K' c, he]
  exact exists_span_eq_top_of_bijective e.symm.bijective hl

/-- Along an isomorphism of fields, a nonzero top form maps to a nonzero top form, so a nonzero
`Ω^d_{K'/k}` comes from a nonzero `Ω^d_{K/k}`. -/
private theorem nontrivial_of_bijective' {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    (h : Function.Bijective (algebraMap K K')) (hl : Nontrivial (⋀[K']^d Ω[K'⁄k])) :
    Nontrivial (⋀[K]^d Ω[K⁄k]) := by
  let e := RingEquiv.ofBijective (algebraMap K K') h
  letI : Algebra K' K := e.symm.toRingHom.toAlgebra
  have he : ∀ x, algebraMap K' K (algebraMap K K' x) = x := e.symm_apply_apply
  haveI : IsScalarTower k K' K := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k K K' c, he]
  obtain ⟨x, hx⟩ := exists_ne (0 : ⋀[K']^d Ω[K'⁄k])
  exact ⟨⟨topFormsMap k K' K d x, 0, fun h0 =>
    hx (topFormsMap_injective_of_bijective e.symm.bijective (by rw [h0, map_zero]))⟩⟩

/-- The pull-back of forms sends `0` to `0`. -/
private theorem pullbackForms_zero {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] :
    pullbackForms (K' := K') m (0 : PluriForms k K d m) = 0 := by
  classical
  unfold pullbackForms
  split_ifs with h
  · simp [pullbackFormsAlong]
  · rfl

/-- If `Ω^d_{K/k}` is not a line, the pull-back of forms is zero. -/
private theorem pullbackForms_eq_zero_of_not {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    (hl : ¬ ∃ ω : ⋀[K]^d Ω[K⁄k], Submodule.span K {ω} = ⊤ ∧ ω ≠ 0)
    (τ : PluriForms k K d m) : pullbackForms (K' := K') m τ = 0 := by
  classical
  unfold pullbackForms
  rw [dif_neg]
  rintro ⟨ω, hω⟩
  exact hl ⟨ω, hω.1, hω.ne_zero⟩

/-- **Pull-back of forms along a composite of isomorphisms of fields.** -/
private theorem pullbackForms_comp_of_bijective {K K' K'' : Type*} [Field K] [Field K']
    [Field K''] [Algebra k K] [Algebra k K'] [Algebra k K''] [Algebra K K'] [Algebra K' K'']
    [Algebra K K''] [IsScalarTower k K K'] [IsScalarTower k K' K''] [IsScalarTower k K K'']
    [IsScalarTower K K' K''] (h₁ : Function.Bijective (algebraMap K K'))
    (h₂ : Function.Bijective (algebraMap K' K'')) (τ : PluriForms k K d m) :
    pullbackForms (K' := K'') m (pullbackForms (K' := K') m τ) =
      pullbackForms (K' := K'') m τ := by
  by_cases hl : ∃ ω : ⋀[K]^d Ω[K⁄k], Submodule.span K {ω} = ⊤ ∧ ω ≠ 0
  · obtain ⟨ω, hω, h0⟩ := hl
    have h1 := isPullbackGenerator_of_bijective h₁ hω h0
    exact pullbackForms_comp h1 (isPullbackGenerator_of_bijective h₂ h1.2.1 h1.2.2) τ
  · rw [pullbackForms_eq_zero_of_not hl, pullbackForms_eq_zero_of_not hl, pullbackForms_zero]

/-- Along an isomorphism of fields, the pull-back of a nonzero form is nonzero, when
`Ω^d_{K/k}` is a line. -/
private theorem pullbackForms_ne_zero_of_bijective {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    (h : Function.Bijective (algebraMap K K'))
    (hl : ∃ ω : ⋀[K]^d Ω[K⁄k], Submodule.span K {ω} = ⊤ ∧ ω ≠ 0)
    {τ : PluriForms k K d m} (hτ : τ ≠ 0) : pullbackForms (K' := K') m τ ≠ 0 := by
  obtain ⟨ω, hω, h0⟩ := hl
  have hg := isPullbackGenerator_of_bijective h hω h0
  rw [pullbackForms_eq hg, pullbackFormsAlong]
  refine smul_ne_zero ((map_ne_zero _).mpr fun hc => hτ ?_) ((ZTensorPower.basis _ m).ne_zero ())
  rw [← (ZTensorPower.basis (basisOfSpanSingleton hg.1 hg.ne_zero) m).sum_repr τ]
  simp [hc]

/-- Along an isomorphism of fields, every form is a pull-back, when `Ω^d_{K/k}` is a line. -/
private theorem exists_pullbackForms_eq_of_bijective {K K' : Type*} [Field K] [Field K']
    [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    (h : Function.Bijective (algebraMap K K'))
    (hl : ∃ ω : ⋀[K]^d Ω[K⁄k], Submodule.span K {ω} = ⊤ ∧ ω ≠ 0)
    (τ' : PluriForms k K' d m) : ∃ τ : PluriForms k K d m, pullbackForms (K' := K') m τ = τ' := by
  obtain ⟨ω, hω, h0⟩ := hl
  have hg := isPullbackGenerator_of_bijective h hω h0
  obtain ⟨c, hc⟩ := h.2 ((ZTensorPower.basis (basisOfSpanSingleton hg.2.1 hg.2.2) m).repr τ' ())
  refine ⟨c • ZTensorPower.basis (basisOfSpanSingleton hg.1 hg.ne_zero) m (), ?_⟩
  rw [pullbackForms_eq hg, pullbackFormsAlong]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, hc]
  conv_rhs => rw [← (ZTensorPower.basis (basisOfSpanSingleton hg.2.1 hg.2.2) m).sum_repr τ']
  simp

end Transport

section Order

variable {k : Type*} [CommRing k] {d : ℕ} {m : ℤ}

/-- **Generators of top forms transport along isomorphisms.** Let `A ≅ A'` and `K ≅ K'` be
compatible isomorphisms of `k`-algebras, `K`, `K'` fields. If `σ` generates `Ω^d_{A/k}` with
nonzero image in `Ω^d_{K/k}`, its image generates `Ω^d_{A'/k}` with nonzero image in
`Ω^d_{K'/k}`. -/
private theorem span_topFormsMap_and_ne_zero_of_bijective {A A' K K' : Type*} [CommRing A]
    [CommRing A'] [Field K] [Field K'] [Algebra k A] [Algebra k A'] [Algebra A A']
    [IsScalarTower k A A'] [Algebra k K] [Algebra k K'] [Algebra K K'] [IsScalarTower k K K']
    [Algebra A K] [IsScalarTower k A K] [Algebra A' K'] [IsScalarTower k A' K'] [Algebra A K']
    [IsScalarTower k A K'] [IsScalarTower A A' K'] [IsScalarTower A K K']
    (hA : Function.Bijective (algebraMap A A')) (hK : Function.Bijective (algebraMap K K'))
    {σ : ⋀[A]^d Ω[A⁄k]} (hσ : Submodule.span A {σ} = ⊤) (h0 : topFormsMap k A K d σ ≠ 0) :
    Submodule.span A' {topFormsMap k A A' d σ} = ⊤ ∧
      topFormsMap k A' K' d (topFormsMap k A A' d σ) ≠ 0 := by
  letI := isLocalization_bot_of_bijective hA
  refine ⟨span_singleton_topFormsMap (⊥ : Submonoid A) hσ, ?_⟩
  rw [topFormsMap_comp, ← topFormsMap_comp (B := K) (C := K')]
  exact fun h => h0 (topFormsMap_injective_of_bijective hK (by rw [h, map_zero]))

variable {K K' : Type*} [Field K] [Field K'] [Algebra k K] [Algebra k K'] [Algebra K K']
  [IsScalarTower k K K']
variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra k A] [Algebra k A'] [Algebra A K]
  [IsScalarTower k A K] [IsFractionRing A K] [Algebra A' K'] [IsScalarTower k A' K']
  [IsFractionRing A' K'] [Algebra A A'] [IsScalarTower k A A'] [Algebra A K']
  [IsScalarTower A A' K'] [IsScalarTower A K K'] [IsScalarTower k A K']

/-- If `Ω^d_{A/k}` has no generator with nonzero image in `Ω^d_{K/k}`, neither has `Ω^d_{A'/k}`,
for compatible isomorphisms `A ≅ A'`, `K ≅ K'`. -/
private theorem not_exists_generator_of_bijective (hA : Function.Bijective (algebraMap A A'))
    (hK : Function.Bijective (algebraMap K K'))
    (h : ¬ ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0) :
    ¬ ∃ σ : ⋀[A']^d Ω[A'⁄k], Submodule.span A' {σ} = ⊤ ∧ topFormsMap k A' K' d σ ≠ 0 := by
  rintro ⟨σ, hσ, h0⟩
  let eA := RingEquiv.ofBijective (algebraMap A A') hA
  let eK := RingEquiv.ofBijective (algebraMap K K') hK
  letI : Algebra A' A := eA.symm.toRingHom.toAlgebra
  letI : Algebra K' K := eK.symm.toRingHom.toAlgebra
  letI : Algebra A' K := ((algebraMap K' K).comp (algebraMap A' K')).toAlgebra
  have hA1 : ∀ a, algebraMap A' A (algebraMap A A' a) = a := eA.symm_apply_apply
  have hK1 : ∀ x, algebraMap K' K (algebraMap K K' x) = x := eK.symm_apply_apply
  have hA2 : Function.Bijective (algebraMap A' A) := eA.symm.bijective
  have hK2 : Function.Bijective (algebraMap K' K) := eK.symm.bijective
  haveI : IsScalarTower k A' A := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k A A' c, hA1]
  haveI : IsScalarTower k K' K := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k K K' c, hK1]
  haveI : IsScalarTower A' K' K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k A' K := IsScalarTower.of_algebraMap_eq fun c => by
    change _ = algebraMap K' K (algebraMap A' K' (algebraMap k A' c))
    rw [← IsScalarTower.algebraMap_apply k A' K' c, IsScalarTower.algebraMap_apply k K K' c, hK1]
  haveI : IsScalarTower A' A K := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨a, rfl⟩ := hA.2 x
    change algebraMap K' K (algebraMap A' K' (algebraMap A A' a)) =
      algebraMap A K (algebraMap A' A (algebraMap A A' a))
    rw [hA1, ← IsScalarTower.algebraMap_apply A A' K' a, IsScalarTower.algebraMap_apply A K K' a,
      hK1]
  exact h ⟨_, span_topFormsMap_and_ne_zero_of_bijective hA2 hK2 hσ h0⟩

/-- **The order of a form is invariant under isomorphisms.** For compatible isomorphisms
`A ≅ A'` and `K ≅ K'` of `k`-algebras (`K`, `K'` the fraction fields) and functions `v`, `v'`
on `K`, `K'` that are multiplicative on nonzero elements, trivial on units and match under
`K ≅ K'`, the order of the pull-back of an `m`-canonical form along `A'` is its order along `A`,
whether or not `Ω^d_{A/k}` has a generator. -/
private theorem ordAt_pullbackForms_eq_of_bijective (hA : Function.Bijective (algebraMap A A'))
    (hK : Function.Bijective (algebraMap K K')) {v : K → ℤ} {v' : K' → ℤ}
    (hmul : ∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    (hunit : ∀ a : A, IsUnit a → v (algebraMap A K a) = 0)
    (hmul' : ∀ x y : K', x ≠ 0 → y ≠ 0 → v' (x * y) = v' x + v' y)
    (hunit' : ∀ a : A', IsUnit a → v' (algebraMap A' K' a) = 0)
    (hvv : ∀ x, v' (algebraMap K K' x) = v x) (τ : PluriForms k K d m) :
    ordAt A' v' (pullbackForms (K' := K') m τ) = ordAt A v τ := by
  by_cases h : ∃ σ : ⋀[A]^d Ω[A⁄k], Submodule.span A {σ} = ⊤ ∧ topFormsMap k A K d σ ≠ 0
  · obtain ⟨σ, hσ, h0⟩ := h
    obtain ⟨hσ', h0'⟩ := span_topFormsMap_and_ne_zero_of_bijective hA hK hσ h0
    have hc : topFormsMap k K K' d (topFormsMap k A K d σ) =
        topFormsMap k A' K' d (topFormsMap k A A' d σ) := by
      rw [topFormsMap_comp, topFormsMap_comp]
    refine ordAt_pullbackForms_eq hA hmul hunit hmul' hunit' hvv hσ
      ⟨span_singleton_topFormsMap (nonZeroDivisors A) hσ, ?_, ?_⟩ τ
    · rw [hc]
      exact span_singleton_topFormsMap (nonZeroDivisors A') hσ'
    · rwa [hc]
  · delta ordAt
    rw [dif_neg (not_exists_generator_of_bijective hA hK h), dif_neg h]

omit [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] in
/-- If `Ω^d_{K/k}` is not a line, the order of every form along `A` is `0`. -/
private theorem ordAt_eq_zero_of_not (v : K → ℤ)
    (hl : ¬ ∃ ω : ⋀[K]^d Ω[K⁄k], Submodule.span K {ω} = ⊤ ∧ ω ≠ 0) (τ : PluriForms k K d m) :
    ordAt A v τ = 0 := by
  delta ordAt
  rw [dif_neg]
  rintro ⟨σ, hσ, h0⟩
  exact hl ⟨_, span_singleton_topFormsMap (nonZeroDivisors A) hσ, h0⟩

end Order

section SchemeForms

variable {k : Type u} [Field k]

/-- **Pull-back of rational forms along a composite** of morphisms inducing isomorphisms of
function fields, over any field: `g^*(f^*τ) = (f ∘ g)^*τ`. -/
private theorem pullbackRationalPluriForms_comp_of_bijective {X Y W : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsIntegral W] {sX : X ⟶ Spec (.of k)} (f : Y ⟶ X) (g : W ⟶ Y)
    [IsDominant f] [IsDominant g] (hf : Function.Bijective (functionFieldMap f))
    (hg : Function.Bijective (functionFieldMap g)) {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms sX d m) :
    pullbackRationalPluriForms (f ≫ sX) g (pullbackRationalPluriForms sX f τ) =
      (pullbackRationalPluriForms sX (g ≫ f) τ : RationalPluriForms (g ≫ f ≫ sX) d m) := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldAlgebra (g ≫ f ≫ sX)
  let := functionFieldMapAlgebra f
  let := functionFieldMapAlgebra g
  let := functionFieldMapAlgebra (g ≫ f)
  have := isScalarTower_functionFieldMap sX f
  have := isScalarTower_functionFieldMap (f ≫ sX) g
  have : IsScalarTower k X.functionField W.functionField :=
    isScalarTower_functionFieldMap sX (g ≫ f)
  have : IsScalarTower X.functionField Y.functionField W.functionField :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply g f a).symm
  exact pullbackForms_comp_of_bijective hf hg τ

/-- Through a morphism inducing an isomorphism of function fields, `Ω^d` of one function field is
a line exactly when `Ω^d` of the other is. -/
private theorem exists_span_eq_top_iff_of_bijective {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (sX : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) (d : ℕ) :
    letI := functionFieldAlgebra sX
    letI := functionFieldAlgebra (f ≫ sX)
    (∃ ω : ⋀[X.functionField]^d Ω[X.functionField⁄k], Submodule.span X.functionField {ω} = ⊤ ∧
      ω ≠ 0) ↔
    ∃ ω : ⋀[Y.functionField]^d Ω[Y.functionField⁄k], Submodule.span Y.functionField {ω} = ⊤ ∧
      ω ≠ 0 := by
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  exact ⟨exists_span_eq_top_of_bijective hf, exists_span_eq_top_of_bijective' hf⟩

/-- If `Ω^d_{k(X)/k}` is not a line, every rational form has order `0` along every prime
divisor. -/
private theorem ordForm_eq_zero_of_not {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {sX : X ⟶ Spec (.of k)} {d : ℕ} {m : ℤ}
    (hl : letI := functionFieldAlgebra sX
      ¬ ∃ ω : ⋀[X.functionField]^d Ω[X.functionField⁄k], Submodule.span X.functionField {ω} = ⊤ ∧
        ω ≠ 0) (Γ : Mori.PrimeDivisor X) (τ : RationalPluriForms sX d m) :
    Γ.ordForm τ = 0 := by
  letI := stalkAlgebra sX Γ.genericPoint
  letI := functionFieldAlgebra sX
  haveI := isScalarTower_stalk_functionField sX Γ.genericPoint
  exact ordAt_eq_zero_of_not (A := Γ.localRing) _ hl τ

/-- A bijection `ψ : k(Y₁) ≃ k(Y₂)` carrying the valuation of `E₂` to that of `E₁` restricts to
a bijection of the local rings of `E₁` and `E₂`. -/
private theorem exists_localRing_ringHom_of_valuation_comp {Y₁ Y₂ : Scheme.{u}} [IsIntegral Y₁]
    [IsIntegral Y₂] [IsLocallyNoetherian Y₁] [IsLocallyNoetherian Y₂] [IsNormal Y₁] [IsNormal Y₂]
    (E₁ : Mori.PrimeDivisor Y₁) (E₂ : Mori.PrimeDivisor Y₂)
    (ψ : Y₁.functionField →+* Y₂.functionField) (hψb : Function.Bijective ψ)
    (hval : ∀ y, E₂.divisorialValuation (ψ y) = E₁.divisorialValuation y) :
    ∃ χ : E₁.localRing →+* E₂.localRing, Function.Bijective χ ∧
      ∀ a, algebraMap E₂.localRing Y₂.functionField (χ a) =
        ψ (algebraMap E₁.localRing Y₁.functionField a) := by
  have h12 : ∀ a1 : E₁.localRing, ∃ a2 : E₂.localRing,
      algebraMap E₂.localRing Y₂.functionField a2 =
        ψ (algebraMap E₁.localRing Y₁.functionField a1) := by
    intro a1
    have : E₁.divisorialValuation (algebraMap E₁.localRing Y₁.functionField a1) ≤ 1 :=
      (E₁.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    exact (E₂.divisorialValuation_le_one_iff _).mp this
  have h21 : ∀ a2 : E₂.localRing, ∃ a1 : E₁.localRing,
      ψ (algebraMap E₁.localRing Y₁.functionField a1) =
        algebraMap E₂.localRing Y₂.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := hψb.2 (algebraMap E₂.localRing Y₂.functionField a2)
    have : E₁.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (E₂.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (E₁.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩
  exact MMP.Threefold.Mori.ModelIndependence.exists_ringHom_bijective_of_range ψ h12 h21

/-- A ring map `ψ : k(Y₁) → k(Y₂)` carrying the valuation of `E₂` to that of `E₁` carries the
order along `E₂` to the order along `E₁`. -/
private theorem ord_comp_eq_of_divisorialValuation_comp {Y₁ Y₂ : Scheme.{u}} [IsIntegral Y₁]
    [IsIntegral Y₂] [IsLocallyNoetherian Y₁] [IsLocallyNoetherian Y₂] [IsNormal Y₁] [IsNormal Y₂]
    (E₁ : Mori.PrimeDivisor Y₁) (E₂ : Mori.PrimeDivisor Y₂)
    (ψ : Y₁.functionField →+* Y₂.functionField)
    (hval : ∀ y, E₂.divisorialValuation (ψ y) = E₁.divisorialValuation y) (y : Y₁.functionField) :
    Y₂.ord (ψ y) E₂.genericPoint = Y₁.ord y E₁.genericPoint := by
  by_cases hy : y = 0
  · subst hy
    simp [Scheme.ord_zero]
  · have h1 := hval y
    rw [E₂.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hy),
      E₁.divisorialValuation_eq_exp_neg_ord hy, WithZero.exp_inj] at h1
    omega

/-- **The order of a pulled-back form along a divisor depends only on its valuation.** Let
`h₁ : Y₁ ⟶ Z`, `h₂ : Y₂ ⟶ Z` induce isomorphisms of function fields, and let `E₁`, `E₂` be prime
divisors of `Y₁`, `Y₂` inducing the same valuation of `k(Z)`. Then
`ord_{E₁}(h₁^*ω) = ord_{E₂}(h₂^*ω)` for every rational form `ω` on `Z`, over any field. -/
private theorem ordForm_pullback_eq_of_valuation_eq {Z Y₁ Y₂ : Scheme.{u}} [IsIntegral Z]
    [IsIntegral Y₁] [IsIntegral Y₂] [IsLocallyNoetherian Y₁] [IsLocallyNoetherian Y₂]
    [IsNormal Y₁] [IsNormal Y₂] {sZ : Z ⟶ Spec (.of k)} (h₁ : Y₁ ⟶ Z) (h₂ : Y₂ ⟶ Z)
    [IsDominant h₁] [IsDominant h₂] (hb₁ : Function.Bijective (functionFieldMap h₁))
    (hb₂ : Function.Bijective (functionFieldMap h₂)) (E₁ : Mori.PrimeDivisor Y₁)
    (E₂ : Mori.PrimeDivisor Y₂)
    (hv : E₁.divisorialValuation.comap (functionFieldMap h₁) =
      E₂.divisorialValuation.comap (functionFieldMap h₂)) {d : ℕ} {m : ℤ}
    (ω : RationalPluriForms sZ d m) :
    E₁.ordForm (pullbackRationalPluriForms sZ h₁ ω) =
      E₂.ordForm (pullbackRationalPluriForms sZ h₂ ω) := by
  let e₁ := RingEquiv.ofBijective (functionFieldMap h₁) hb₁
  let ψ : Y₁.functionField →+* Y₂.functionField := (functionFieldMap h₂).comp e₁.symm.toRingHom
  have hψ : ∀ z, ψ (functionFieldMap h₁ z) = functionFieldMap h₂ z := fun z => by
    simp only [ψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact congrArg _ (e₁.symm_apply_apply z)
  have hψb : Function.Bijective ψ := hb₂.comp e₁.symm.bijective
  have hval : ∀ y : Y₁.functionField, E₂.divisorialValuation (ψ y) = E₁.divisorialValuation y := by
    intro y
    obtain ⟨z, rfl⟩ := hb₁.2 y
    rw [hψ]
    exact (congrArg (fun w => w z) hv).symm
  have hord := ord_comp_eq_of_divisorialValuation_comp E₁ E₂ ψ hval
  obtain ⟨χ, hχb, hχ⟩ := exists_localRing_ringHom_of_valuation_comp E₁ E₂ ψ hψb hval
  letI := functionFieldAlgebra sZ
  letI := functionFieldAlgebra (h₁ ≫ sZ)
  letI := functionFieldAlgebra (h₂ ≫ sZ)
  letI := functionFieldMapAlgebra h₁
  letI := functionFieldMapAlgebra h₂
  haveI := isScalarTower_functionFieldMap sZ h₁
  haveI := isScalarTower_functionFieldMap sZ h₂
  letI : Algebra Y₁.functionField Y₂.functionField := ψ.toAlgebra
  have hT : IsScalarTower k Y₁.functionField Y₂.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = ψ (algebraMap k Y₁.functionField c)
    rw [IsScalarTower.algebraMap_apply k Z.functionField Y₁.functionField c,
      IsScalarTower.algebraMap_apply k Z.functionField Y₂.functionField c]
    exact (hψ _).symm
  have hT' : IsScalarTower Z.functionField Y₁.functionField Y₂.functionField :=
    IsScalarTower.of_algebraMap_eq fun z => (hψ z).symm
  have hpull : pullbackForms (K' := Y₂.functionField) m (pullbackRationalPluriForms sZ h₁ ω) =
      pullbackRationalPluriForms sZ h₂ ω :=
    pullbackForms_comp_of_bijective (K := Z.functionField) hb₁ hψb ω
  letI := stalkAlgebra (h₁ ≫ sZ) E₁.genericPoint
  letI := stalkAlgebra (h₂ ≫ sZ) E₂.genericPoint
  haveI := isScalarTower_stalk_functionField (h₁ ≫ sZ) E₁.genericPoint
  haveI := isScalarTower_stalk_functionField (h₂ ≫ sZ) E₂.genericPoint
  letI : Algebra E₁.localRing E₂.localRing := χ.toAlgebra
  letI : Algebra E₁.localRing Y₂.functionField :=
    ((algebraMap E₂.localRing Y₂.functionField).comp χ).toAlgebra
  have hS1 : IsScalarTower k E₁.localRing E₂.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective E₂.localRing Y₂.functionField
    change _ = algebraMap E₂.localRing Y₂.functionField (χ (algebraMap k E₁.localRing c))
    rw [hχ, ← IsScalarTower.algebraMap_apply k E₁.localRing Y₁.functionField c,
      ← IsScalarTower.algebraMap_apply k E₂.localRing Y₂.functionField c]
    exact IsScalarTower.algebraMap_apply k Y₁.functionField Y₂.functionField c
  have hS2 : IsScalarTower E₁.localRing E₂.localRing Y₂.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower E₁.localRing Y₁.functionField Y₂.functionField :=
    IsScalarTower.of_algebraMap_eq hχ
  have hS4 : IsScalarTower k E₁.localRing Y₂.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap E₂.localRing Y₂.functionField (χ (algebraMap k E₁.localRing c))
    rw [IsScalarTower.algebraMap_apply k E₂.localRing Y₂.functionField c,
      IsScalarTower.algebraMap_apply k E₁.localRing E₂.localRing c]
    rfl
  have key := ordAt_pullbackForms_eq_of_bijective (k := k) (K := Y₁.functionField)
    (K' := Y₂.functionField) (A := E₁.localRing) (A' := E₂.localRing)
    (v := fun y => Y₁.ord y E₁.genericPoint) (v' := fun y => Y₂.ord y E₂.genericPoint) hχb hψb
    (fun x y hx hy => E₁.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => E₁.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => E₂.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => E₂.ord_algebraMap_of_isUnit ha) hord (pullbackRationalPluriForms sZ h₁ ω)
  rw [hpull] at key
  exact key.symm

end SchemeForms

section Coefficients

/-- For dominant morphisms `f₁ : Y₁ ⟶ X`, `f₂ : Y₂ ⟶ X` and prime divisors `E₁`, `E₂` of `Y₁`,
`Y₂` inducing the same valuation of `k(X)`, the orders of `f₁^*y` along `E₁` and of `f₂^*y` along
`E₂` agree. -/
private theorem ord_functionFieldMap_eq_of_valuation_eq {X Y₁ Y₂ : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y₁] [IsIntegral Y₂] [IsLocallyNoetherian Y₁] [IsNormal Y₁]
    [IsLocallyNoetherian Y₂] [IsNormal Y₂] (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) [IsDominant f₁]
    [IsDominant f₂] (E₁ : Mori.PrimeDivisor Y₁) (E₂ : Mori.PrimeDivisor Y₂)
    (hv : E₁.divisorialValuation.comap (functionFieldMap f₁) =
      E₂.divisorialValuation.comap (functionFieldMap f₂)) (y : X.functionField) :
    Y₁.ord (functionFieldMap f₁ y) E₁.genericPoint =
      Y₂.ord (functionFieldMap f₂ y) E₂.genericPoint := by
  by_cases hy : y = 0
  · subst hy
    simp [Scheme.ord_zero]
  · have h1 := congrArg (fun w => w y) hv
    simp only [Valuation.comap_apply] at h1
    rw [E₁.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hy),
      E₂.divisorialValuation_eq_exp_neg_ord ((map_ne_zero _).mpr hy), WithZero.exp_inj] at h1
    omega

/-- **Multiplicities of a Cartier divisor along a divisor depend only on its valuation.** For
dominant morphisms `f₁ : Y₁ ⟶ X`, `f₂ : Y₂ ⟶ X`, prime divisors `E₁`, `E₂` with the same center
`f₁(η_{E₁}) = f₂(η_{E₂})` inducing the same valuation of `k(X)`, and a Cartier divisor `L` on `X`
with pull-backs `L₁`, `L₂`, the coefficient of `L₁` along `E₁` is that of `L₂` along `E₂`. -/
private theorem coeff_isPullback_eq_of_valuation_eq {X Y₁ Y₂ : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y₁] [IsIntegral Y₂] [IsLocallyNoetherian Y₁] [IsNormal Y₁]
    [IsLocallyNoetherian Y₂] [IsNormal Y₂] (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) [IsDominant f₁]
    [IsDominant f₂] (E₁ : Mori.PrimeDivisor Y₁) (E₂ : Mori.PrimeDivisor Y₂)
    (hv : E₁.divisorialValuation.comap (functionFieldMap f₁) =
      E₂.divisorialValuation.comap (functionFieldMap f₂))
    (hx : f₁ E₁.genericPoint = f₂ E₂.genericPoint) {L : Divisor X} (hL : L.IsCartier)
    {hB₁ : ∀ Z : irreducibleComponents Y₁, f₁ (componentGenericPoint Y₁ Z) ∉ L.supp}
    {hB₂ : ∀ Z : irreducibleComponents Y₂, f₂ (componentGenericPoint Y₂ Z) ∉ L.supp}
    {L₁ : Divisor Y₁} {L₂ : Divisor Y₂} (h₁ : L.IsPullback f₁ hB₁ L₁)
    (h₂ : L.IsPullback f₂ hB₂ L₂) : L₁.coeff E₁ = L₂.coeff E₂ := by
  obtain ⟨U, hU, φ, hφ⟩ := hL (f₁ E₁.genericPoint)
  let Z := MMP.Mori.pointComponent (f₁ E₁.genericPoint)
  rw [MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h₁ hφ E₁ hU Z,
    MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h₂ hφ E₂ (hx ▸ hU) Z]
  exact ord_functionFieldMap_eq_of_valuation_eq f₁ f₂ E₁ E₂ hv _

/-- **Multiplicities along a divisor with the valuation of a prime divisor.** If a prime divisor
`E` of `Y` maps to the generic point of a prime divisor `P` of `X` under a dominant `f`, and
`ord_E = ord_P` on `k(X)`, the coefficient along `E` of the pull-back of a Cartier divisor `L` is
the coefficient of `L` along `P`. -/
private theorem coeff_isPullback_eq_coeff {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (E : Mori.PrimeDivisor Y) (P : Mori.PrimeDivisor X)
    (hv : E.divisorialValuation.comap (functionFieldMap f) = P.divisorialValuation)
    (hx : f E.genericPoint = P.genericPoint) {L : Divisor X} (hL : L.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y, f (componentGenericPoint Y Z) ∉ L.supp}
    {L' : Divisor Y} (h : L.IsPullback f hB L') : L'.coeff E = L.coeff P := by
  obtain ⟨U, hU, φ, hφ⟩ := hL P.genericPoint
  have h1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF h hφ E (hx ▸ hU)
    (MMP.Mori.pointComponent P.genericPoint)
  have hPU : (P.support ∩ U).Nonempty := (P.genericPoint_mem_iff U).mp hU
  have h2 := hφ P hPU
  rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h2
  have hZ : P.component = MMP.Mori.pointComponent P.genericPoint := Subsingleton.elim
    (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
  rw [hZ] at h2
  rw [h1, h2]
  have hv' : E.divisorialValuation.comap (functionFieldMap f) =
      P.divisorialValuation.comap (functionFieldMap (𝟙 X)) := by
    rw [hv]
    ext y
    rw [Valuation.comap_apply, functionFieldMap_id_apply]
  have := ord_functionFieldMap_eq_of_valuation_eq f (𝟙 X) E P hv'
    (MMP.Threefold.Mori.Helpers.evalFF (MMP.Mori.pointComponent P.genericPoint)
      (φ : MMP.Mori.RationalFunctions X))
  rw [this, functionFieldMap_id_apply]

end Coefficients

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A normalization of a proper curve is not constant. -/
private theorem not_const_of_isCurveNormalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) :
    ¬ ∃ y : C.scheme, ∀ x : C', ν.base x = y := by
  rintro ⟨y, hy⟩
  have := hν.isFinite
  have : IsDominant ν := hν.isBirationalMorphism.isDominant
  have huniv : Set.range ν = Set.univ := by
    rw [← ν.isClosedMap.isClosed_range.closure_eq, ν.denseRange.closure_range]
  have : Subsingleton C.scheme := ⟨fun a b => by
    obtain ⟨x, rfl⟩ := huniv.ge (Set.mem_univ a)
    obtain ⟨x', rfl⟩ := huniv.ge (Set.mem_univ b)
    exact (hy x).trans (hy x').symm⟩
  have h0 := topologicalKrullDim_zero_of_discreteTopology C.scheme
  rw [C.dim_eq] at h0
  exact absurd h0 (by decide)

/-- A normalization of a proper curve is a curve. -/
private theorem isCurve_comp (C : ProperCurve sX) {C' : Scheme.{u}} {ν : C' ⟶ C.scheme}
    (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1) :
    AlgebraicGeometry.IsCurve k (ν ≫ C.ι ≫ sX) := by
  have := hν.isFinite
  have := hν.isIntegral
  have hp : IsProper (ν ≫ C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (ν ≫ C.ι ≫ sX) :=
    { toIsIntegral := ‹_›, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  refine ⟨le_antisymm hdim ?_⟩
  by_contra! h
  refine not_const_of_isCurveNormalization C hν ⟨ν.base (genericPoint C'), fun x => ?_⟩
  by_cases hx : x = genericPoint C'
  · rw [hx]
  · exact absurd (one_le_topologicalKrullDim_of_specializes_of_ne
      (genericPoint_specializes x) (Ne.symm hx)) (not_le.mpr h)

/-- A proper curve is a curve. -/
private theorem isCurve_ι (C : ProperCurve sX) : AlgebraicGeometry.IsCurve k (C.ι ≫ sX) := by
  have hp : IsProper (C.ι ≫ sX) := inferInstance
  have : AlgebraicGeometry.IsVariety k (C.ι ≫ sX) :=
    { toIsIntegral := inferInstance, toIsSeparated := hp.toIsSeparated,
      toLocallyOfFiniteType := hp.toLocallyOfFiniteType, toQuasiCompact := inferInstance }
  exact ⟨C.dim_eq⟩

/-- A birational morphism of integral schemes has degree one. -/
private theorem degreeOver_eq_one {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] (f : Y ⟶ Z)
    (hf : IsBirationalMorphism f) [IsDominant f] [LocallyOfFiniteType f] : degreeOver f = 1 := by
  letI := (functionFieldMap f).toAlgebra
  have heq : functionFieldMap f = dominantFunctionFieldMap f :=
    (congrArg CommRingCat.Hom.hom
      (stalkMap_cast_target f (genericPoint Y) (map_genericPoint_of_isDominant f))).symm
  rw [degreeOver_eq_finrank f heq]
  let e := AlgEquiv.ofBijective (Algebra.ofId Z.functionField Y.functionField)
    hf.functionFieldMap_bijective
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- The degree of an invertible sheaf along a normalization of a proper curve `C` is its degree
along `C`. -/
private theorem degreeOn_normalization (C : ProperCurve sX) {C' : Scheme.{u}}
    {ν : C' ⟶ C.scheme} (hν : IsCurveNormalization ν) (hdim : topologicalKrullDim C' ≤ 1)
    [IsProper ((ν ≫ C.ι) ≫ sX)] (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 M] :
    MMP.Mori.degreeOn k sX (ν ≫ C.ι) hdim M = MMP.Mori.degreeOn k sX C.ι C.dim_le M := by
  have := hν.isFinite
  have := hν.isIntegral
  haveI : IsProper (ν ≫ C.ι ≫ sX) := by rw [← Category.assoc]; infer_instance
  have hc := isCurve_comp C hν hdim
  have hc2 := isCurve_ι (k := k) C
  haveI : IsDominant ν := hν.isBirationalMorphism.isDominant
  have key := curveDegree_pullback_eq_degreeOver_mul k (ν ≫ C.ι ≫ sX) (C.ι ≫ sX) ν rfl
    (not_const_of_isCurveNormalization C hν) ((Scheme.Modules.pullback C.ι).obj M) 1
  rw [degreeOver_eq_one ν hν.isBirationalMorphism, Nat.cast_one, one_mul] at key
  let e : (Scheme.Modules.pullback (ν ≫ C.ι)).obj M ≅
      (Scheme.Modules.pullback ν).obj ((Scheme.Modules.pullback C.ι).obj M) :=
    ((Scheme.Modules.pullbackComp ν C.ι).app M).symm
  rw [MMP.Mori.degreeOn, MMP.Mori.degreeOn,
    invertibleCurveDegree_congr_structure (Category.assoc ν C.ι sX) hdim,
    invertibleCurveDegree_eq_of_iso k _ hdim e,
    invertibleCurveDegree_eq_curveDegree_one, invertibleCurveDegree_eq_curveDegree_one]
  exact key

variable (k sX) [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]

/-- `L · C` is the degree of `𝒪_X(L)` along `C`: every proper curve has a normalization, which is
birational, so of degree one. -/
private theorem isCartierIntersectionNumber_degreeOn (C : ProperCurve sX) (L : Divisor X)
    (hL : L.IsCartier) :
    IsCartierIntersectionNumber k sX C L hL (L.degreeOn k sX C.ι C.dim_le hL) := by
  let p := C.ι ≫ sX
  haveI : AlgebraicGeometry.IsCurve k p := C.isCurve
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  haveI hvar : AlgebraicGeometry.IsVariety k (normalizationOverField k p ≫ p) :=
    isVariety_normalizationOverField k p
  haveI : IsIntegral (normalizationSchemeOverField k p) := hvar.toIsIntegral
  haveI : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hν : IsCurveNormalization (normalizationOverField k p) :=
    { isIntegral := inferInstance
      isNormal := Scheme.isNormal_normalizationScheme C.scheme hX
      isFinite := inferInstance
      isBirationalMorphism := by
        haveI : Finite (irreducibleComponents (normalizationSchemeOverField k p)) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        haveI : Finite (irreducibleComponents C.scheme) := by
          rw [irreducibleComponents_eq_singleton]
          exact Set.finite_singleton _
        obtain ⟨U, V, hUV, hU, hV, hiso⟩ := exists_dense_opens_isIso_resLE_of_isBirational
          (normalizationOverField k p) (Scheme.isBirational_normalization C.scheme hX)
          (Or.inl ⟨inferInstance, inferInstance⟩)
        exact isBirationalMorphism_of_isIso_resLE _ U V hU.nonempty hV.nonempty hUV hiso }
  have hdim := (topologicalKrullDim_normalizationSchemeOverField k p).le.trans C.dim_le
  refine ⟨_, _, hν, hdim, ?_⟩
  haveI : IsProper ((normalizationOverField k p ≫ C.ι) ≫ sX) := by
    rw [Category.assoc]
    infer_instance
  have := QuasiCompact.compactSpace_of_compactSpace sX
  have := hL.isInvertibleModule_divisorialSheaf
  exact (degreeOn_normalization C hν hdim _).symm

/-- `D · C = ∑ r_j (L_j · C)`, computed from the degrees along `C`, for a presentation
`D = ∑ r_j L_j` by Cartier divisors. -/
private theorem isRIntersectionNumber_sum_degreeOn (C : ProperCurve sX) {m : ℕ}
    (r : Fin m → ℝ) (L : Fin m → Divisor X) (hL : ∀ j, (L j).IsCartier) :
    IsRIntersectionNumber k sX (∑ j, r j • Divisor.toRDivisor (L j)) r L C
      (∑ j, r j * ((L j).degreeOn k sX C.ι C.dim_le (hL j) : ℝ)) :=
  ⟨hL, fun j => (L j).degreeOn k sX C.ι C.dim_le (hL j), rfl,
    fun j => isCartierIntersectionNumber_degreeOn k sX C (L j) (hL j), rfl⟩

end Intersection

/-- **Projection formula** for the pull-back of a Cartier divisor `D` along `h : Y' ⟶ Y`: on a
proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`h^*D · C' = [k(C') : k(C)] · (D · C)`. -/
private theorem degreeOn_pullback_eq_mul {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

/-- The pull-back of a Cartier divisor along `h : Y' ⟶ Y` has degree zero on a proper curve
`C' ⊆ Y'` whose image is not a proper curve. -/
private theorem degreeOn_pullback_eq_zero {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    (hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp)
    (C' : ProperCurve (h ≫ sY)) (hc : ¬ IsProperCurve sY (h C'.point)) :
    (D.pullback hD hB).degreeOn k (h ≫ sY) C'.ι C'.dim_le (hD.isCartier_pullback h hB) = 0 := by
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hc, map_zero]

/-- The projection formula for a divisor `L₁` given as a pull-back of `D`. -/
private theorem degreeOn_eq_mul_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (C : ProperCurve sY) (hC : C.point = h C'.point) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc =
      (residueFieldDegree h C'.point : ℤ) * D.degreeOn k sY C.ι C.dim_le hD := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  exact degreeOn_pullback_eq_mul h hD hB C' C hC

/-- A divisor `L₁` given as a pull-back along `h` has degree zero on a proper curve whose image is
not a proper curve. -/
private theorem degreeOn_eq_zero_of_isPullback {k : Type u} [Field k] {Y Y' : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY] [QuasiCompact sY]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral Y'] [IsLocallyNoetherian Y'] [IsNormal Y']
    (h : Y' ⟶ Y) [QuasiCompact (h ≫ sY)] [CompactSpace Y] [CompactSpace Y'] {D : Divisor Y}
    (hD : D.IsCartier)
    {hB : ∀ Z : irreducibleComponents Y', h (componentGenericPoint Y' Z) ∉ D.supp}
    {L₁ : Divisor Y'} (hp : D.IsPullback h hB L₁) (hc : L₁.IsCartier)
    (C' : ProperCurve (h ≫ sY)) (hnc : ¬ IsProperCurve sY (h C'.point)) :
    L₁.degreeOn k (h ≫ sY) C'.ι C'.dim_le hc = 0 := by
  obtain rfl := Divisor.IsPullback.pullback_eq hD hp
  exact degreeOn_pullback_eq_zero h hD hB C' hnc

/-- **Pull-backs of relatively nef divisors are nef over the base.** Let `q : W ⟶ Y` be proper,
`g : Y ⟶ Z`, `N` a `g`-nef `ℝ`-Cartier divisor on `Y` and `G = q^*N`. Then `G · C' ≥ 0` for every
proper curve `C' ⊆ W` contracted by `q ≫ g`, for every presentation of `G`: by the projection
formula, `G · C' = [k(C') : k(q C')] (N · q C')` when `q(C')` is a curve, which is contracted by
`g`, and `G · C' = 0` when `q(C')` is a point. -/
private theorem nonneg_of_isRelativelyNef_of_isRCartierPullback {k : Type u} [Field k]
    {W Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (g : Y ⟶ Z) {h : W ⟶ Z}
    (hqg : q ≫ g = h) {N : RDivisor Y} (hN : IsRelativelyNef k sY g N) {G : RDivisor W}
    (hG : IsRCartierPullback q N G) (C' : ProperCurve sW) (hC' : C'.IsContractedBy h) {m : ℕ}
    {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ}
    (hx : IsRIntersectionNumber k sW G r L C' x) : 0 ≤ x := by
  subst hq hqg
  obtain ⟨m₀, r₀, L₀, L₁, hL₀, hNpres, hpb, rfl⟩ := hG
  have hL₁ : ∀ j, (L₁ j).IsCartier := fun j => by
    rw [← Divisor.IsPullback.pullback_eq (hL₀ j) (hpb j).2]
    exact (hL₀ j).isCartier_pullback q (hpb j).1
  have hx0 := isRIntersectionNumber_sum_degreeOn k (q ≫ sY) C' r₀ L₁ hL₁
  rw [(IsRIntersectionNumber.eq_and_linear k (q ≫ sY) C').1 _ _ _ _ _ _ _ hx hx0]
  by_cases hc : IsProperCurve sY (q C'.point)
  · -- `q(C')` is a curve `C`, contracted by `g`
    obtain ⟨C, hCq⟩ : ∃ C : ProperCurve sY, C.point = q C'.point := ⟨⟨_, hc⟩, rfl⟩
    have hCg : C.IsContractedBy g := by
      intro y hy
      rw [hCq] at hy
      have hsub : closure ({q C'.point} : Set Y) ⊆ q '' closure ({C'.point} : Set W) :=
        closure_minimal (Set.singleton_subset_iff.2 ⟨C'.point, subset_closure rfl, rfl⟩)
          (q.isClosedMap _ isClosed_closure)
      obtain ⟨z, hz, rfl⟩ := hsub hy
      rw [hCq]
      simpa only [Scheme.Hom.comp_apply] using hC' z hz
    obtain ⟨m', r', L', hL', hpres, hall⟩ := hN
    have hy := isRIntersectionNumber_sum_degreeOn k sY C r' L' hL'
    have hy0 := isRIntersectionNumber_sum_degreeOn k sY C r₀ L₀ hL₀
    rw [← hpres] at hy
    rw [← hNpres] at hy0
    have heq := (IsRIntersectionNumber.eq_and_linear k sY C).1 _ _ _ _ _ _ _ hy0 hy
    have hnn := hall C hCg _ hy
    have hdeg : ∀ j, ((L₁ j).degreeOn k (q ≫ sY) C'.ι C'.dim_le (hL₁ j) : ℝ) =
        (residueFieldDegree q C'.point : ℝ) * (L₀ j).degreeOn k sY C.ι C.dim_le (hL₀ j) :=
      fun j => by
        rw [degreeOn_eq_mul_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' C hCq]
        push_cast
        ring
    simp only [hdeg, mul_left_comm (r₀ _), ← Finset.mul_sum]
    exact mul_nonneg (Nat.cast_nonneg _) (heq ▸ hnn)
  · -- `q(C')` is a point
    simp [fun j => degreeOn_eq_zero_of_isPullback q (hL₀ j) (hpb j).2 (hL₁ j) C' hc]

/-- The pull-back of `-N` is the negative of the pull-back of `N`. -/
private theorem isRCartierPullback_neg {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {N : RDivisor X} {G : RDivisor Y}
    (h : IsRCartierPullback f N G) : IsRCartierPullback f (-N) (-G) := by
  obtain ⟨m, r, L, L', hL, rfl, hpb, rfl⟩ := h
  exact ⟨m, fun j => -r j, L, L', hL, by simp [neg_smul, Finset.sum_neg_distrib], hpb,
    by simp [neg_smul, Finset.sum_neg_distrib]⟩

/-- A pull-back of an `ℝ`-Cartier divisor is `ℝ`-Cartier. -/
private theorem isCartierCombination_of_isRCartierPullback {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] {f : Y ⟶ X}
    {N : RDivisor X} {G : RDivisor Y} (h : IsRCartierPullback f N G) : IsCartierCombination G := by
  obtain ⟨m, r, L, L', hL, -, hpb, rfl⟩ := h
  refine ⟨m, r, L', fun j => ?_, by simp only [toRDivisor_eq_mapCoeffs]⟩
  rw [← Divisor.IsPullback.pullback_eq (hL j) (hpb j).2]
  exact (hL j).isCartier_pullback f (hpb j).1

/-- The difference of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_sub {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D - D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r (fun j => -r' j), Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add, neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- **Nefness of `q^*A_Y - p^*A_X`.** If `A_Y` is `g`-nef and `-A_X` is `f`-nef, then for
`p : W ⟶ X`, `q : W ⟶ Y` with `p ≫ f = q ≫ g = h`, the divisor `q^*A_Y - p^*A_X` is `h`-nef. -/
private theorem isRelativelyNef_sub_of_isRCartierPullback {k : Type u} [Field k]
    {W X Y Z : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsSeparated sX] [LocallyOfFiniteType sX]
    [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (p : W ⟶ X) (q : W ⟶ Y) [IsProper p] [IsProper q] (hp : p ≫ sX = sW)
    (hq : q ≫ sY = sW) (f : X ⟶ Z) (g : Y ⟶ Z) {h : W ⟶ Z} (hpf : p ≫ f = h) (hqg : q ≫ g = h)
    {A_X : RDivisor X} {A_Y : RDivisor Y} (hAX : IsRelativelyNef k sX f (-A_X))
    (hAY : IsRelativelyNef k sY g A_Y) {G_X : RDivisor W} {G_Y : RDivisor W}
    (hGX : IsRCartierPullback p A_X G_X) (hGY : IsRCartierPullback q A_Y G_Y) :
    IsRelativelyNef k sW h (G_Y - G_X) := by
  obtain ⟨m, r, L, hL, hpres⟩ := isCartierCombination_sub
    (isCartierCombination_of_isRCartierPullback hGY)
    (isCartierCombination_of_isRCartierPullback hGX)
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C hC x hx => ?_⟩
  obtain ⟨mY, rY, LY, hLY, hYpres⟩ := isCartierCombination_of_isRCartierPullback hGY
  obtain ⟨mX, rX, LX, hLX, hXpres⟩ :=
    isCartierCombination_of_isRCartierPullback (isRCartierPullback_neg hGX)
  simp only [← toRDivisor_eq_mapCoeffs] at hYpres hXpres
  have hY := isRIntersectionNumber_sum_degreeOn k sW C rY LY hLY
  have hX := isRIntersectionNumber_sum_degreeOn k sW C rX LX hLX
  rw [← hYpres] at hY
  rw [← hXpres] at hX
  have hsum := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 1 hY hX
  rw [one_smul, one_smul, ← sub_eq_add_neg] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx hsum]
  have h1 := nonneg_of_isRelativelyNef_of_isRCartierPullback q hq g hqg hAY hGY C hC hY
  have h2 := nonneg_of_isRelativelyNef_of_isRCartierPullback p hp f hpf hAX
    (isRCartierPullback_neg hGX) C hC hX
  linarith

/-- An `f`-ample Cartier divisor has positive degree on every proper curve contracted by `f`. -/
private theorem degreeOn_pos_of_isRelativelyAmpleCartier {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] (f : X ⟶ Z) {D : Divisor X} (hD : IsRelativelyAmpleCartier f D)
    (hDc : D.IsCartier) (C : ProperCurve sX) (hC : C.IsContractedBy f) :
    0 < D.degreeOn k sX C.ι C.dim_le hDc := by
  obtain ⟨hD', hamp⟩ := hD
  haveI := hD'.isInvertibleModule_divisorialSheaf
  have hrel : MMP.Mori.IsRelativelyAmple f D.divisorialSheaf := fun y => by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
    exact ⟨V, hV, hyV, hamp V hV⟩
  exact MMP.Threefold.Resolution.degreeOn_pos_of_isRelativelyAmple_of_isContractedBy f _ hrel C hC

/-- An `f`-ample `ℝ`-Cartier divisor is `f`-nef. -/
private theorem isRelativelyNef_of_isRelativelyAmple {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] {f : X ⟶ Z} {A : RDivisor X} (hA : IsRelativelyAmple f A) :
    IsRelativelyNef k sX f A := by
  obtain ⟨m, r, L, -, hr, hL, rfl⟩ := hA
  have hLc : ∀ j, (L j).IsCartier := fun j => (hL j).1
  refine ⟨m, r, L, hLc, rfl, fun C hC x hx => ?_⟩
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx
    (isRIntersectionNumber_sum_degreeOn k sX C r L hLc)]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hr j).le
    (by exact_mod_cast (degreeOn_pos_of_isRelativelyAmpleCartier f (hL j) (hLc j) C hC).le)

/-- The valuation of `E` over `C` through `a ≫ b` is that over `B` through `a`, restricted along
`b^*`. -/
private theorem comap_valuationOver {A B C : Scheme.{u}} [IsIntegral A] [IsIntegral B]
    [IsIntegral C] [IsLocallyNoetherian A] [IsNormal A] (E : MMP.Mori.PrimeDivisor A) (a : A ⟶ B)
    (b : B ⟶ C)
    [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    (E.valuationOver a).comap (functionFieldMap b) = E.valuationOver (a ≫ b) := by
  ext t
  change E.divisorialValuation (functionFieldMap a (functionFieldMap b t)) =
    E.divisorialValuation (functionFieldMap (a ≫ b) t)
  rw [MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The valuation of `E` over `C` through a morphism depends only on the morphism. -/
private theorem valuationOver_congr {A C : Scheme.{u}} [IsIntegral A] [IsIntegral C]
    [IsLocallyNoetherian A] [IsNormal A] (E : MMP.Mori.PrimeDivisor A) {h₁ h₂ : A ⟶ C} (e : h₁ = h₂)
    [IsDominant h₁] [IsDominant h₂] : E.valuationOver h₁ = E.valuationOver h₂ := by
  subst e
  rfl

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]; exact ENat.natCast_ne_top n
    lift d to ℕ using hd
    lift c to ℕ using hc
    rw [show (n : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) from rfl, ← WithBot.coe_ofNat,
      ← WithBot.coe_add, WithBot.coe_le_coe]
    norm_cast at h ⊢
    omega

/-- A variety over a field has finite dimension. -/
private theorem exists_topologicalKrullDim_eq_natCast {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX] [CompactSpace X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  have h1 := topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX
  induction hd : topologicalKrullDim X using WithBot.recBotCoe with
  | bot =>
    exact ((Order.krullDim_eq_bot_iff.mp hd).false
      (⟨closure {genericPoint X}, isIrreducible_singleton.closure, isClosed_closure⟩ :
        TopologicalSpace.IrreducibleCloseds X)).elim
  | coe d =>
    lift d to ℕ using fun h => h1 (by rw [hd, h]; rfl)
    exact ⟨d, rfl⟩

/-- A prime divisor `F` of `Y` is exceptional over the normal variety `X` exactly when its image
`g(η_F)` has coheight at least two. -/
private theorem isExceptionalPrimeDivisor_iff_two_le_coheight {k : Type u} [Field k]
    {X Y : Scheme.{u}} {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (g : Y ⟶ X)
    (hY : IsNormalVariety k (g ≫ sX)) (hg : IsBirationalMorphism g) [IsProper g]
    (F : MMP.Mori.PrimeDivisor Y) :
    IsExceptionalPrimeDivisor sX g F ↔ 2 ≤ Order.coheight (g F.genericPoint) := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : QuasiCompact sX := hX.1.toQuasiCompact
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_eq_natCast sX
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX (g F.genericPoint)
  rw [hn] at hd
  constructor
  · rintro ⟨_, _, _, hexc⟩
    unfold ProperDivisorOver.IsExceptional at hexc
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn] at hexc
    exact (withBot_add_two_le_iff hd).mp hexc
  · intro h2
    refine ⟨hY, hg, ‹_›, ?_⟩
    unfold ProperDivisorOver.IsExceptional
    rw [ProperDivisorOver.center_eq_toDivisorOver_center,
      DivisorOver.center_eq_closure_genericPoint, hn]
    exact (withBot_add_two_le_iff hd).mpr h2

/-- Let `p : W ⟶ X`, `f : X ⟶ Z` be proper birational morphisms of normal varieties and `P` a
prime divisor of `W` whose image in `Z` is the generic point of a prime divisor `Q`. Then `P` is
not exceptional over `X`: `ord_P` is `ord_{P_X}` for the prime divisor `P_X` of `X` with generic
point `p(η_P)`. -/
private theorem exists_primeDivisor_valuation_eq_of_map_genericPoint_eq {k : Type u} [Field k]
    {W X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {f : X ⟶ Z} [IsProper f] (hX : IsNormalVariety k (f ≫ sZ)) (hf : IsBirationalMorphism f)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {p : W ⟶ X} [IsProper p]
    (hWp : IsNormalVariety k (p ≫ f ≫ sZ)) (hpb : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor Z)
    (hPQ : f (p P.genericPoint) = Q.genericPoint) :
    ∃ P_X : MMP.Mori.PrimeDivisor X,
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
        ProperDivisorOver k (f ≫ sZ)).valuation = P_X.divisorialValuation ∧
      p P.genericPoint = P_X.genericPoint := by
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant p := hpb.isDominant
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Z.presheaf.stalk (f (p P.genericPoint))) := by
    rw [hPQ]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
    (p P.genericPoint)
  have hco : Order.coheight (p P.genericPoint) = 1 := by
    have h1 : ringKrullDim (X.presheaf.stalk (p P.genericPoint)) =
        ringKrullDim (Z.presheaf.stalk (f (p P.genericPoint))) :=
      (ringKrullDim_eq_of_ringEquiv
        (asIso (f.stalkMap (p P.genericPoint))).commRingCatIsoToRingEquiv).symm
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hPQ,
      Q.coheight_genericPoint] at h1
    exact_mod_cast h1
  have hne : ¬ (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
      ProperDivisorOver k (f ≫ sZ)).IsExceptional := fun h => by
    have h2 := (isExceptionalPrimeDivisor_iff_two_le_coheight hX p hWp hpb P).mp
      ⟨hWp, hpb, inferInstance, h⟩
    rw [hco] at h2
    exact absurd h2 (by decide)
  obtain ⟨P_X, -, hη, -, hval⟩ :=
    ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hX _ hne
  exact ⟨P_X, hval, hη⟩

/-- A birational morphism `f : X ⟶ Y` restricts to an isomorphism of a dense open of `X` onto a
dense open of `Y`, under which it is the inclusion of that open. -/
private theorem exists_partialIso_isOver {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) : ∃ e : X.PartialIso Y, e.IsOver f (𝟙 Y) := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨W, hW, hWl, hWr, heq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
  simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom] at heq
  have hWl' : W ≤ e.source := hWl
  refine ⟨e.restrictSource W hW hWl', ?_⟩
  have h1 : (Scheme.Opens.isoOfLE hWl').inv ≫ (e.source.ι ⁻¹ᵁ W).ι = X.homOfLE hWl' := by
    rw [← cancel_mono e.source.ι, Category.assoc, Scheme.Opens.isoOfLE_inv_ι, Scheme.homOfLE_ι]
  have h2 : X.homOfLE hWr ≫ X.topIso.hom = W.ι := by
    simp only [Scheme.topIso_hom]
    exact Scheme.homOfLE_ι X hWr
  change ((Scheme.Opens.isoOfLE hWl').inv ≫ (e.iso.hom.isoImage (e.source.ι ⁻¹ᵁ W)).hom ≫
    (e.target.ι.isoImage (e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W)).hom) ≫
    (e.target.ι ''ᵁ e.iso.hom ''ᵁ e.source.ι ⁻¹ᵁ W).ι ≫ 𝟙 Y = W.ι ≫ f
  rw [Category.comp_id, Category.assoc, Category.assoc, Scheme.Hom.isoImage_hom_ι,
    Scheme.Hom.isoImage_hom_ι_assoc, ← Category.assoc, h1]
  exact heq.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) h2))

/-- For birational morphisms `f : X ⟶ Z` and `g : Y ⟶ Z`, the birational map
`φ = g⁻¹ ∘ f : X ⇢ Y` satisfies `g ∘ φ = f`. -/
private theorem exists_isBirational_compHom_eq {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    ∃ φ : X.RationalMap Y, Mori.RationalMap.IsBirational φ ∧ φ.compHom g = f.toRationalMap := by
  obtain ⟨e₁, h₁⟩ := exists_partialIso_isOver hf
  obtain ⟨e₂, h₂⟩ := exists_partialIso_isOver hg
  set e := e₁.trans e₂.symm
  have h : e.IsOver f g := h₁.trans h₂.symm
  refine ⟨e.toRationalMap, Mori.RationalMap.isBirational_toRationalMap e, ?_⟩
  rw [← Scheme.RationalMap.compHom_toRationalMap]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr ⟨e.source, e.dense_source, le_rfl,
    le_top, ?_⟩
  change X.homOfLE le_rfl ≫ (e.iso.hom ≫ e.target.ι) ≫ g =
    X.homOfLE (le_top : e.source ≤ ⊤) ≫ X.topIso.hom ≫ f
  rw [Category.assoc, h]
  simp

/-- A valuation of `k(Y)` is determined by its restriction to `k(Z)` along a birational
morphism `g : Y ⟶ Z`. -/
private theorem valuation_eq_of_comap_eq {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    {g : Y ⟶ Z} (hg : IsBirationalMorphism g) [IsDominant g]
    {v w : Valuation Y.functionField ℤᵐ⁰}
    (h : v.comap (functionFieldMap g) = w.comap (functionFieldMap g)) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hg.functionFieldMap_bijective.2 t
    exact congrArg (fun u => u s) h

section CanonicalTransport

open MMP.Positivity MMP.Fourfold

/-- An open immersion from a nonempty scheme into an irreducible one is dominant. -/
private theorem isDominant_of_isOpenImmersion' {A Z : Scheme.{u}} (f : A ⟶ Z)
    [IsOpenImmersion f] [Nonempty A] [IrreducibleSpace Z] : IsDominant f :=
  ⟨IsOpen.dense f.isOpenEmbedding.isOpen_range (Set.range_nonempty _)⟩

section Restrict

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- The divisorial valuation of a prime divisor `E'` of an open subscheme `V ⊆ Y` is that of its
closure `E` in `Y`, through the identification `k(Y) ≅ k(V)`. -/
private theorem divisorialValuation_primeDivisorMap {Y V : Scheme.{u}} [IsIntegral Y]
    [IsIntegral V] [IsLocallyNoetherian Y] [IsLocallyNoetherian V] [IsNormal Y] [IsNormal V]
    (j : V ⟶ Y) [IsOpenImmersion j] [IsDominant j] (E' : Mori.PrimeDivisor V) :
    Mori.PrimeDivisor.divisorialValuation (OpenWeilRestriction.primeDivisorMap j E') =
      E'.divisorialValuation.comap (functionFieldMap j) := by
  ext g
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hg' : functionFieldMap j g ≠ 0 := (map_ne_zero _).2 hg
  rw [Valuation.comap_apply, Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg,
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ hg',
    MMP.Positivity.ord_functionFieldMap_of_isIso j E' _
      (OpenWeilRestriction.genericPoint_primeDivisorMap j E').symm]

/-- The restriction `D|_A` of a divisor along an open immersion `j : A ⟶ X`. -/
private noncomputable def restrictDivisorAlong {A : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (D : Divisor X) : Divisor A :=
  Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) D
    (OpenWeilRestriction.primeDivisorMap_injective j).injOn

private theorem coeff_restrictDivisorAlong {A : Scheme.{u}} (j : A ⟶ X) [IsOpenImmersion j]
    (D : Divisor X) (W : Mori.PrimeDivisor A) :
    (restrictDivisorAlong j D).coeff W = D.coeff (OpenWeilRestriction.primeDivisorMap j W) := rfl

private theorem functionFieldMap_bijective_j {A : Scheme.{u}} [IsIntegral A] (j : A ⟶ X)
    [IsOpenImmersion j] [IsDominant j] [Nonempty A] : Function.Bijective (functionFieldMap j) :=
  functionFieldMap_bijective_of_isOpenImmersion j ⊤ ⟨Classical.arbitrary A, trivial⟩

section DivisorialRestrict

/-- On an irreducible scheme every irreducible component is the whole space. -/
private theorem eq_univ_of_irreducibleComponents {Y : Scheme.{u}} [IrreducibleSpace Y]
    (Z : irreducibleComponents Y) : Z.1 = Set.univ :=
  Set.eq_univ_of_univ_subset
    (Z.2.2 (IrreducibleSpace.isIrreducible_univ Y) (Set.subset_univ _))

private theorem index_eq {Y : Scheme.{u}} [IrreducibleSpace Y] {W : Y.Opens}
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Z = Z' :=
  Subtype.ext (Subtype.ext ((eq_univ_of_irreducibleComponents _).trans
    (eq_univ_of_irreducibleComponents _).symm))

private theorem genericPoint_specializes {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : genericPoint Y ⤳ componentGenericPoint Y Z :=
  (genericPoint_spec Y).specializes trivial

private theorem specializes_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) : componentGenericPoint Y Z ⤳ genericPoint Y :=
  (Inseparable.of_eq (componentGenericPoint_eq_genericPoint Z)).specializes

private theorem stalkSpecializes_stalkSpecializes_apply {Y : Scheme.{u}} {x y z : Y}
    (h : x ⤳ y) (h' : y ⤳ z) (h'' : x ⤳ z) (s : Y.presheaf.stalk z) :
    (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.stalkSpecializes h').hom s) =
      (Y.presheaf.stalkSpecializes h'').hom s :=
  TopCat.Presheaf.stalkSpecializes_comp_apply _ h h' s

private theorem stalkSpecializes_self_apply {Y : Scheme.{u}} {x : Y} (h : x ⤳ x)
    (s : Y.presheaf.stalk x) : (Y.presheaf.stalkSpecializes h).hom s = s := by
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  rfl

/-- The value in the function field of a section of `𝒦_Y` over an open set, read at the generic
point of an irreducible component meeting it. -/
private noncomputable def evFF {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) : Y.functionField :=
  (Y.presheaf.stalkSpecializes (genericPoint_specializes Z.1)).hom (φ Z)

private theorem evFF_eq {Y : Scheme.{u}} [IsIntegral Y] {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (Z Z' : {Z : irreducibleComponents Y // componentGenericPoint Y Z ∈ W}) :
    evFF φ Z = evFF φ Z' := by
  obtain rfl := index_eq Z Z'
  rfl

private theorem stalkSpecializes_injective {Y : Scheme.{u}} [IsIntegral Y]
    (Z : irreducibleComponents Y) :
    Function.Injective (Y.presheaf.stalkSpecializes (genericPoint_specializes Z)).hom := by
  intro a b h
  have := congrArg (Y.presheaf.stalkSpecializes (specializes_genericPoint Z)).hom h
  rwa [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply,
    stalkSpecializes_self_apply] at this

/-- `v_E` on the factor `𝒪_{Y,η}` of `𝒦_Y` is the inverse of the divisorial valuation of the
corresponding rational function. -/
private theorem valuation_eq_inv_divisorialValuation {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (E : Mori.PrimeDivisor Y)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.valuation s = (E.divisorialValuation
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹ := by
  rw [MMP.Threefold.Mori.Helpers.valuation_eq_ordFrac,
    Mori.PrimeDivisor.divisorialValuation_eq_inv_ordHom, inv_inv]
  rfl

private theorem ordGE_iff {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (E : Mori.PrimeDivisor Y) (n : ℤ)
    (s : Y.presheaf.stalk (componentGenericPoint Y E.component)) :
    E.OrdGE n s ↔
      ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation
          ((Y.presheaf.stalkSpecializes (genericPoint_specializes E.component)).hom s))⁻¹) := by
  rw [Mori.PrimeDivisor.OrdGE, valuation_eq_inv_divisorialValuation,
    (injective_iff_map_eq_zero' _).1 (stalkSpecializes_injective E.component)]

private theorem ordGE_iff_evFF {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (E : Mori.PrimeDivisor Y) (n : ℤ) {W : Y.Opens}
    (φ : ToType ((rationalFunctionsPresheaf Y).obj (op W)))
    (h : componentGenericPoint Y E.component ∈ W) :
    E.OrdGE n (φ ⟨E.component, h⟩) ↔
      (evFF φ ⟨E.component, h⟩ = 0 ∨
        WithZero.exp n ≤ (E.divisorialValuation (evFF φ ⟨E.component, h⟩))⁻¹) :=
  ordGE_iff E n _

variable {A : Scheme.{u}} [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A] (j : A ⟶ X)
  [IsOpenImmersion j] [IsDominant j] [Nonempty A]

private theorem genericPoint_mem_of_index {V : A.Opens}
    (Z : {Z : irreducibleComponents A // componentGenericPoint A Z ∈ V}) :
    genericPoint A ∈ V := by
  have := Z.2
  rwa [componentGenericPoint_eq_genericPoint] at this

private theorem genericPoint_mem_of_indexX {V : A.Opens}
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ j ''ᵁ V}) :
    genericPoint A ∈ V := by
  have h := Z.2
  rw [componentGenericPoint_eq_genericPoint] at h
  obtain ⟨x, hx, hxe⟩ := h
  have hsp : genericPoint A ⤳ x := (genericPoint_spec A).specializes trivial
  exact hsp.mem_open V.isOpen hx

/-- The unique irreducible component `Set.univ` of an irreducible scheme `Y`. -/
private def topComponent (Y : Scheme.{u}) [IrreducibleSpace Y] : irreducibleComponents Y :=
  ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; rfl⟩

private def indexX {V : A.Opens} (h : genericPoint A ∈ V) :
    {Z : irreducibleComponents X // componentGenericPoint X Z ∈ j ''ᵁ V} :=
  ⟨topComponent X, by
    rw [componentGenericPoint_eq_genericPoint, ← map_genericPoint_of_isDominant j]
    exact ⟨_, h, rfl⟩⟩

private def indexU {V : A.Opens} (h : genericPoint A ∈ V) :
    {Z : irreducibleComponents A // componentGenericPoint A Z ∈ V} :=
  ⟨topComponent A, by rwa [componentGenericPoint_eq_genericPoint]⟩

/-- The restriction `𝒦_X(U ∩ -) → 𝒦_U` of rational functions to an open subscheme, through the
identification `k(X) ≅ k(U)`. -/
private noncomputable def restrictRF (V : A.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V)))) :
    ToType ((rationalFunctionsPresheaf A).obj (op V)) :=
  fun Z => (A.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap j (evFF ψ (indexX j (genericPoint_mem_of_index Z))))

private theorem evFF_restrictRF (V : A.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V))))
    (Z : {Z : irreducibleComponents A // componentGenericPoint A Z ∈ V})
    (Z' : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ j ''ᵁ V}) :
    evFF (restrictRF j V ψ) Z = functionFieldMap j (evFF ψ Z') := by
  rw [evFF, restrictRF, stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl,
    stalkSpecializes_self_apply, evFF_eq ψ _ Z']

private theorem restrictRF_injective (V : A.Opens) :
    Function.Injective (restrictRF j V) := by
  intro ψ₁ ψ₂ h
  funext Z'
  have hV := genericPoint_mem_of_indexX j Z'
  have h1 := congrArg (fun φ => evFF φ (indexU hV)) h
  simp only [evFF_restrictRF j V _ _ Z'] at h1
  exact stalkSpecializes_injective Z'.1 ((functionFieldMap j).injective h1)

private theorem restrictRF_surjective (V : A.Opens) :
    Function.Surjective (restrictRF j V) := by
  intro φ
  let e := RingEquiv.ofBijective (functionFieldMap j) (functionFieldMap_bijective_j j)
  refine ⟨fun Z' => (X.presheaf.stalkSpecializes (specializes_genericPoint Z'.1)).hom
    (e.symm (evFF φ (indexU (genericPoint_mem_of_indexX j Z')))), ?_⟩
  funext Z
  change (A.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (functionFieldMap j ((X.presheaf.stalkSpecializes (genericPoint_specializes _)).hom
      ((X.presheaf.stalkSpecializes (specializes_genericPoint _)).hom (e.symm _)))) = _
  rw [stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]
  change (A.presheaf.stalkSpecializes (specializes_genericPoint Z.1)).hom
    (e (e.symm _)) = _
  rw [RingEquiv.apply_symm_apply, evFF_eq φ _ Z, evFF,
    stalkSpecializes_stalkSpecializes_apply _ _ specializes_rfl, stalkSpecializes_self_apply]

/-- A section of `𝒦_X` over `U ∩ -` is a section of `𝒪_X(D)` exactly when its restriction is a
section of `𝒪_U(D|_U)`: the prime divisors of `U` meeting `V` are the restrictions of those of
`X` meeting `V`, with the same valuations and coefficients. -/
private theorem isDivisorialSection_restrictRF_iff (D : Divisor X) (V : A.Opens)
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V)))) :
    Divisor.IsDivisorialSection (restrictDivisorAlong j D) V (restrictRF j V ψ) ↔
      D.IsDivisorialSection (j ''ᵁ V) ψ := by
  have key : ∀ (E' : Mori.PrimeDivisor A) (hE' : (E'.support ∩ V).Nonempty)
      (hP : ((OpenWeilRestriction.primeDivisorMap j E').support ∩ j ''ᵁ V).Nonempty),
      E'.OrdGE (-(restrictDivisorAlong j D).coeff E')
          (restrictRF j V ψ ⟨E'.component, E'.componentGenericPoint_mem_of_nonempty hE'⟩) ↔
        Mori.PrimeDivisor.OrdGE (OpenWeilRestriction.primeDivisorMap j E')
          (-D.coeff (OpenWeilRestriction.primeDivisorMap j E'))
          (ψ ⟨_, Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
            (OpenWeilRestriction.primeDivisorMap j E') hP⟩) := by
    intro E' hE' hP
    rw [ordGE_iff_evFF, ordGE_iff_evFF]
    rw [evFF_restrictRF j V ψ _ ⟨_, Mori.PrimeDivisor.componentGenericPoint_mem_of_nonempty
        (OpenWeilRestriction.primeDivisorMap j E') hP⟩,
      divisorialValuation_primeDivisorMap, map_eq_zero_iff _ (functionFieldMap j).injective,
      coeff_restrictDivisorAlong]
    rfl
  have hmem : ∀ E' : Mori.PrimeDivisor A, (E'.support ∩ V).Nonempty ↔
      ((OpenWeilRestriction.primeDivisorMap j E').support ∩ j ''ᵁ V).Nonempty := by
    intro E'
    rw [← Mori.PrimeDivisor.genericPoint_mem_iff, ← Mori.PrimeDivisor.genericPoint_mem_iff,
      show Mori.PrimeDivisor.genericPoint (OpenWeilRestriction.primeDivisorMap j E') =
        j E'.genericPoint from OpenWeilRestriction.genericPoint_primeDivisorMap _ _]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨x, hx, hxe⟩
    rwa [j.isOpenEmbedding.injective hxe] at hx
  constructor
  · intro h P hP
    have hPU : P.genericPoint ∈ Set.range j.base := by
      obtain ⟨x, -, hx⟩ := (Mori.PrimeDivisor.genericPoint_mem_iff P _).2 hP
      exact ⟨x, hx⟩
    obtain ⟨E', rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff _ P).2 hPU
    exact (key E' ((hmem E').2 hP) hP).1 (h E' ((hmem E').2 hP))
  · intro h E' hE'
    exact (key E' hE' ((hmem E').1 hE')).2 (h _ ((hmem E').1 hE'))

private theorem functionFieldMap_germ_appIso_inv (V : A.Opens) (r : Γ(A, V))
    (h₁ : genericPoint X ∈ j ''ᵁ V) (h₂ : genericPoint A ∈ V) :
    functionFieldMap j (X.presheaf.germ (j ''ᵁ V) (genericPoint X) h₁
      ((j.appIso V).inv r)) = A.presheaf.germ V (genericPoint A) h₂ r := by
  have h₃ : j (genericPoint A) ∈ j ''ᵁ V := ⟨_, h₂, rfl⟩
  rw [functionFieldMap, CommRingCat.comp_apply, TopCat.Presheaf.stalkCongr_hom]
  erw [TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf h₁ _]
  erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (j.appIso V).inv,
    Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]

private theorem restrictRF_smul (V : A.Opens) (r : Γ(A, V))
    (ψ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V)))) :
    restrictRF j V ((j.appIso V).inv r • ψ) = r • restrictRF j V ψ := by
  funext Z
  rw [rationalFunctions_smul_apply]
  simp only [restrictRF, evFF, rationalFunctions_smul_apply, map_mul]
  congr 1
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply, functionFieldMap_germ_appIso_inv j V r _
    (genericPoint_mem_of_index Z), TopCat.Presheaf.germ_stalkSpecializes_apply]

private theorem restrictRF_zero (V : A.Opens) : restrictRF j V 0 = 0 := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.zero_apply, map_zero, map_zero, map_zero]
  rfl

private theorem restrictRF_add (V : A.Opens)
    (ψ₁ ψ₂ : ToType ((rationalFunctionsPresheaf X).obj (op (j ''ᵁ V)))) :
    restrictRF j V (ψ₁ + ψ₂) = restrictRF j V ψ₁ + restrictRF j V ψ₂ := by
  funext Z
  simp only [restrictRF, evFF]
  erw [Pi.add_apply, map_add, map_add, map_add]
  rfl

/-- The restriction `𝒪_X(D)|_U ⟶ 𝒪_U(D|_U)` of divisorial sections to an open subscheme. -/
private noncomputable def divisorialSheafRestrictHom (D : Divisor X) :
    D.divisorialSheaf.restrict j ⟶ Divisor.divisorialSheaf (restrictDivisorAlong j D) :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun ψ := (⟨restrictRF j V.unop (ψ : D.divisorialSubmodule (j ''ᵁ V.unop)).1,
            (isDivisorialSection_restrictRF_iff j D V.unop _).2
              (ψ : D.divisorialSubmodule (j ''ᵁ V.unop)).2⟩ :
              Divisor.divisorialSubmodule (restrictDivisorAlong j D) V.unop)
          map_zero' := Subtype.ext (restrictRF_zero j V.unop)
          map_add' ψ₁ ψ₂ := Subtype.ext (restrictRF_add j V.unop _ _) }
      naturality V V' i := by ext ψ; rfl }
    fun V r ψ => Subtype.ext (restrictRF_smul j V.unop r _)⟩

private theorem isIso_divisorialSheafRestrictHom (D : Divisor X) :
    IsIso (divisorialSheafRestrictHom j D) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun (ψ₁ ψ₂ : D.divisorialSubmodule (j ''ᵁ V)) h => ?_, fun φ => ?_⟩
  · have h' : restrictRF j V ψ₁.1 = restrictRF j V ψ₂.1 := congrArg Subtype.val h
    exact Subtype.ext (restrictRF_injective j V h')
  · obtain ⟨ψ, hψ⟩ :=
      restrictRF_surjective j V (φ : Divisor.divisorialSubmodule (restrictDivisorAlong j D) V).1
    refine ⟨(⟨ψ, (isDivisorialSection_restrictRF_iff j D V ψ).1
      (hψ ▸ (φ : Divisor.divisorialSubmodule (restrictDivisorAlong j D) V).2)⟩ :
        D.divisorialSubmodule (j ''ᵁ V)), Subtype.ext hψ⟩

/-- The divisorial sheaf of the restriction `D|_U` of a divisor to an open subscheme is the
restriction `𝒪_X(D)|_U` of its divisorial sheaf. -/
private theorem nonempty_divisorialSheaf_restrictDivisorAlong_iso (D : Divisor X) :
    Nonempty (Divisor.divisorialSheaf (restrictDivisorAlong j D) ≅ D.divisorialSheaf.restrict j) :=
  ⟨(@asIso _ _ _ _ _ (isIso_divisorialSheafRestrictHom j D)).symm⟩

end DivisorialRestrict

end Restrict

section Extend

variable {Z A : Scheme.{u}} [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
  [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A] (h : A ⟶ Z) [IsOpenImmersion h]
  [IsDominant h] [Nonempty A] [CompactSpace A] [CompactSpace Z]

/-- Linear equivalence descends across codimension two: if every prime divisor of `Z` has its
generic point in the image of `h`, two divisors of `Z` which are linearly equivalent on `A` are
linearly equivalent. -/
private theorem linearlyEquivalent_of_restrictDivisorAlong
    (hbig : ∀ E : MMP.Mori.PrimeDivisor Z, E.genericPoint ∈ Set.range h)
    {D₁ D₂ : Divisor Z}
    (hlin : (restrictDivisorAlong h D₁).LinearlyEquivalent (restrictDivisorAlong h D₂)) :
    D₁.LinearlyEquivalent D₂ := by
  obtain ⟨φ, hφ⟩ := hlin
  obtain ⟨g, hg0, hg⟩ := exists_ord_eq_of_units φ
  obtain ⟨g0, rfl⟩ := (functionFieldMap_bijective_j h).2 g
  obtain ⟨ψ, hψ⟩ := exists_units_of_ne_zero (X := Z) (g := g0) (by
    rintro rfl
    exact hg0 (map_zero _))
  refine ⟨ψ, ?_⟩
  ext E
  obtain ⟨W, rfl⟩ := (OpenWeilRestriction.mem_range_primeDivisorMap_iff h E).2 (hbig E)
  have := congrArg (fun G : Divisor A => G.coeff W) hφ
  simp only [DivisorWithCoeffs.coeff_sub, coeff_restrictDivisorAlong,
    coeff_principalDivisor] at this
  change D₁.coeff _ - D₂.coeff _ = _
  rw [this, coeff_principalDivisor, hψ, hg]
  have := IsOpenImmersion.instIsIsoCommRingCatStalkMap h W.genericPoint
  exact ord_functionFieldMap_of_isIso h W _
    (OpenWeilRestriction.genericPoint_primeDivisorMap h W).symm g0

omit [CompactSpace A] [CompactSpace Z] in
private theorem restrictDivisorAlong_comp {B : Scheme.{u}} [IsIntegral B] [IsLocallyNoetherian B]
    [IsNormal B] (j : B ⟶ A) [IsOpenImmersion j] (D : Divisor Z) (i : A ⟶ Z)
    [IsOpenImmersion i] [IsDominant i] [IsDominant j] [IsOpenImmersion (j ≫ i)] :
    restrictDivisorAlong (j ≫ i) D = restrictDivisorAlong j (restrictDivisorAlong i D) := by
  refine Finsupp.ext fun W => ?_
  change D.coeff _ = D.coeff _
  congr 1
  refine PrimeDivisor.genericPoint_injective ?_
  rw [OpenWeilRestriction.genericPoint_primeDivisorMap,
    OpenWeilRestriction.genericPoint_primeDivisorMap,
    OpenWeilRestriction.genericPoint_primeDivisorMap]
  rfl

end Extend

section ExtendIso

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]

/-- **The extension of an isomorphism across codimension two, via linear equivalence.** -/
private theorem nonempty_restrict_iso_of_restrictDivisorAlong (S : X.Opens) [Nonempty S]
    [CompactSpace S] {A : Scheme.{u}} [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A]
    [Nonempty A] [CompactSpace A] (h : A ⟶ S.toScheme) [IsOpenImmersion h] [IsDominant h]
    (hbig : ∀ E : MMP.Mori.PrimeDivisor S.toScheme, E.genericPoint ∈ Set.range h)
    (K' : Divisor X) (D : Divisor S.toScheme) (M : S.toScheme.Modules)
    (e1 : D.divisorialSheaf ≅ M)
    (e2 : (restrictDivisorAlong (h ≫ S.ι) K').divisorialSheaf ≅ M.restrict h) :
    Nonempty (K'.divisorialSheaf.restrict S.ι ≅ M) := by
  have := isDominant_of_isOpenImmersion' S.ι
  obtain ⟨eR⟩ := nonempty_divisorialSheaf_restrictDivisorAlong_iso h D
  obtain ⟨eS⟩ := nonempty_divisorialSheaf_restrictDivisorAlong_iso S.ι K'
  have hK : restrictDivisorAlong (h ≫ S.ι) K' =
      restrictDivisorAlong h (restrictDivisorAlong S.ι K') :=
    restrictDivisorAlong_comp h K' S.ι
  have e3 : (restrictDivisorAlong h (restrictDivisorAlong S.ι K')).divisorialSheaf ≅
      (restrictDivisorAlong h D).divisorialSheaf :=
    eqToIso (by rw [← hK]) ≪≫ e2 ≪≫ (Scheme.Modules.restrictFunctor h).mapIso e1.symm ≪≫ eR.symm
  have hlin := MMP.Flips.linearlyEquivalent_of_divisorialSheaf_iso e3
  have hlin' := linearlyEquivalent_of_restrictDivisorAlong h hbig hlin
  exact ⟨eS.symm ≪≫ hlin'.divisorialSheafIso ≪≫ e1⟩

end ExtendIso

section OpenVariety

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}

/-- A nonempty open subscheme of a normal variety is a normal variety. -/
private theorem isNormalVariety_ι
    (h : IsNormalVariety k sX) (V : X.Opens) [Nonempty V] : IsNormalVariety k (V.ι ≫ sX) := by
  have := h.1
  have := h.2
  have : IsIntegral X := h.1.toIsIntegral
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := {}
  exact ⟨⟨⟩, inferInstance⟩

/-- A nonempty open subscheme of a variety has the dimension of the variety. -/
private theorem topologicalKrullDim_opens_eq (hX : IsNormalVariety k sX) (U : X.Opens)
    [Nonempty U] [IsDominant U.ι] : topologicalKrullDim U = topologicalKrullDim X := by
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have := hX.1
  have : IsIntegral X := hX.1.toIsIntegral
  have hbij : Function.Bijective (functionFieldMap U.ι) :=
    functionFieldMap_bijective_of_isOpenImmersion U.ι ⊤ ⟨Classical.arbitrary U, trivial⟩
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (U.ι ≫ sX)
  rw [← toENat_trdeg_functionField (sX := U.ι ≫ sX),
    ← trdeg_functionField_eq_of_bijective sX U.ι hbij, toENat_trdeg_functionField (sX := sX)]

/-- On a nonempty open subscheme of a normal variety, smooth over `k`, the module of relative
`n`-forms is divisorial. -/
private theorem exists_divisorialSheaf_iso_relativeDifferentialForms
    [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) (S : X.Opens)
    [Nonempty S] (hS : Smooth (S.ι ≫ sX)) :
    ∃ D : Divisor S.toScheme,
      Nonempty (D.divisorialSheaf ≅ Scheme.Hom.relativeDifferentialForms (S.ι ≫ sX) n) := by
  have hSv := isNormalVariety_ι hX S
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsDominant S.ι := isDominant_of_isOpenImmersion' S.ι
  have hSd : topologicalKrullDim S.toScheme = n := (topologicalKrullDim_opens_eq hX S).trans hn
  have : AlgebraicGeometry.IsVariety k (S.ι ≫ sX) := hSv.1
  have : IsIntegral S.toScheme := hSv.1.toIsIntegral
  have : CompactSpace S.toScheme := QuasiCompact.compactSpace_of_compactSpace (S.ι ≫ sX)
  have : SmoothOfRelativeDimension n (S.ι ≫ sX) :=
    MMP.Intersection.smoothOfRelativeDimension_of_isVariety (S.ι ≫ sX) n hSd
  have hinv := Stacks.Discriminant.isInvertible_relativeDifferentialForms (S.ι ≫ sX) n
  have hM := Stacks.SheafOfModules.isInvertible_of_tensorInvertible
    (X := S.toScheme.toRingedSpace) (Scheme.Hom.relativeDifferentialForms (S.ι ≫ sX) n) (h := hinv)
  have : AlgebraicGeometry.SheafOfModules.IsInvertible S.toScheme.sheaf.obj
      S.toScheme.ringCatSheaf.property (Scheme.Hom.relativeDifferentialForms (S.ι ≫ sX) n) :=
    hM.toAlgebraicGeometry
  exact exists_divisorialSheaf_iso_of_isInvertible _

/-- Relative differential forms restrict along an open immersion. -/
private theorem nonempty_restrict_relativeDifferentialForms_iso {Y Z S : Scheme.{u}}
    (ψ : Z ⟶ Y) [IsOpenImmersion ψ] (p : Y ⟶ S) (p' : Z ⟶ S) (h : ψ ≫ p = p') (n : ℤ) :
    Nonempty ((Scheme.Hom.relativeDifferentialForms p n).restrict ψ ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  have hc : ψ ≫ p = p' ≫ 𝟙 S := by rw [h, Category.comp_id]
  have := Scheme.Hom.isIso_relativeDifferentialFormsMap_of_etale ψ p p' (𝟙 S) hc n
  exact ⟨(Scheme.Modules.restrictFunctorIsoPullback ψ).app _ ≪≫
    asIso (Scheme.Hom.relativeDifferentialFormsMap ψ p p' (𝟙 S) hc n)⟩

/-- An open immersion smooth over the base lands in the smooth locus. -/
private theorem range_subset_smoothLocus {k : Type u} [Field k] {Y B : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (j : B ⟶ Y) [IsOpenImmersion j] (hs : Smooth (j ≫ sY)) :
    Set.range j ⊆ Set.range (smoothLocus sY).ι := by
  let V := j.opensRange
  have e : j.isoOpensRange.inv ≫ j = V.ι := by
    rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
  have hV : Smooth (V.ι ≫ sY) := by
    rw [← e, Category.assoc]
    infer_instance
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact le_smoothLocus sY hV (show j x ∈ j.opensRange from ⟨x, rfl⟩)

end OpenVariety

section KIso

variable {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
  [IsNormal Y] {sY : Y ⟶ Spec (.of k)}

/-- **A canonical divisor restricts to the canonical sheaf along a smooth open immersion.** -/
private theorem nonempty_restrictDivisorAlong_iso_relativeDifferentialForms {n : ℕ} {K : Divisor Y}
    (hK : K.IsCanonicalDivisor sY n) {B : Scheme.{u}} [IsIntegral B] [IsLocallyNoetherian B]
    [IsNormal B] [Nonempty B] (j : B ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    {p' : B ⟶ Spec (.of k)} (hp : j ≫ sY = p') (hs : Smooth (p')) :
    Nonempty ((restrictDivisorAlong j K).divisorialSheaf ≅
      Scheme.Hom.relativeDifferentialForms p' n) := by
  subst hp
  obtain ⟨eR⟩ := nonempty_divisorialSheaf_restrictDivisorAlong_iso j K
  let S := smoothLocus sY
  let ψ : B ⟶ S.toScheme := IsOpenImmersion.lift S.ι j (range_subset_smoothLocus j hs)
  have hψ : ψ ≫ S.ι = j := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso ψ (S.ι ≫ sY)
    (j ≫ sY) (by rw [← Category.assoc, hψ]) n
  exact ⟨eR ≪≫ (Scheme.Modules.restrictFunctorCongr hψ.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp ψ S.ι).app _ ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso hK.iso ≪≫ e₁⟩

end KIso

private theorem nonempty_iso_of_isEmpty {X : Scheme.{u}} [IsEmpty X] (M N : X.Modules) :
    Nonempty (M ≅ N) := by
  have : IsIso (0 : M ⟶ N) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro U
    rw [ConcreteCategory.isIso_iff_bijective]
    have := Module.subsingleton Γ(X, U) Γ(M, U)
    have := Module.subsingleton Γ(X, U) Γ(N, U)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  exact ⟨asIso (0 : M ⟶ N)⟩

private theorem compactSpace_opens' {Y : Scheme.{u}} [IsLocallyNoetherian Y] [CompactSpace Y]
    (S : Y.Opens) : CompactSpace S := by
  have : IsNoetherian Y := {}
  exact TopologicalSpace.NoetherianSpace.compactSpace (S : Set Y)

end CanonicalTransport

/-! ### Prime divisors under flips -/

section PrimeDivisors

variable {k : Type u} [Field k]

/-- Under a bijection `e` of prime divisors through which `g` transforms each prime divisor, the
coefficient of `g_*B` along `e P` is that of `B` along `P`. -/
private theorem transformDivisor_apply_equiv {X X' : Scheme.{u}} {g : X.RationalMap X'}
    (e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor X')
    (he : ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P)) {R : Type*}
    [AddCommMonoid R] (B : DivisorWithCoeffs R X) (P : Mori.PrimeDivisor X) :
    Mori.RationalMap.transformDivisor g B (e P) = B P :=
  MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq (he P)
    (fun P' h => e.injective (Option.some_injective _ ((he P').symm.trans h))) B

/-- A divisor over a normal variety `X` with valuation `ord_P` has center `P`: `f(η_E) = η_P`. -/
private theorem map_genericPoint_eq_of_valuation_eq' {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) (P : Mori.PrimeDivisor X) (hv : D.valuation = P.divisorialValuation) :
    D.f D.E.genericPoint = P.genericPoint := by
  have hv' : D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation := by
    rw [hv]
    refine Valuation.ext fun y => ?_
    change _ = P.divisorialValuation (functionFieldMap (𝟙 X) y)
    rw [functionFieldMap_id_apply]
  exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv'

/-- On a normal variety a prime divisor is determined by its valuation. -/
private theorem primeDivisor_eq_of_divisorialValuation_eq {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    (hX : IsNormalVariety k sX) {P P' : Mori.PrimeDivisor X}
    (h : P.divisorialValuation = P'.divisorialValuation) : P = P' := by
  have hv : (DivisorOver.ofPrimeDivisor k hX P).valuation = P'.divisorialValuation := by
    rw [← h]
    refine Valuation.ext fun y => ?_
    change P.divisorialValuation (functionFieldMap (𝟙 X) y) = _
    rw [functionFieldMap_id_apply]
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective
    (map_genericPoint_eq_of_valuation_eq' hX _ P' hv)

/-- The identity of a variety is a small contraction. -/
private theorem isSmall_id {k : Type u} [Field k] {Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    (hZ : MMP.Mori.IsVariety k sZ) : IsSmall k sZ sZ (𝟙 Z) where
  isVariety_target := hZ
  isVariety_source := hZ
  comp_eq := Category.id_comp sZ
  isProper := inferInstance
  isIso_app _ := inferInstance
  dim_eq := rfl
  exists_isIso := ⟨⊥, ⊥, le_closedsCodimension_iff_le_coheight.mpr (by simp),
    le_closedsCodimension_iff_le_coheight.mpr (by simp), le_rfl, by
      simp only [Scheme.Hom.resLE_id, Scheme.homOfLE_rfl]
      infer_instance⟩

/-- The inverse `f⁻¹ : Z ⤏ Y` of a birational morphism `f : Y ⟶ Z` to a separated scheme is a map
over `Z`: `f ∘ f⁻¹ = 𝟙_Z`. -/
private theorem isModificationOf_inverse {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [Z.IsSeparated] (f : Y ⟶ Z) (hf : IsBirationalMorphism f) :
    IsModificationOf (𝟙 Z) f (MMP.Mori.RationalMap.IsBirational.inverse hf) := by
  refine ⟨hf.isBirational_inverse, ?_⟩
  obtain ⟨e, he, hinv⟩ := hf.isInverse_inverse
  have key : e.iso.hom ≫ e.target.ι = e.source.ι ≫ f := by
    obtain ⟨W, hW, hWl, hWr, hEq⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp he
    have hWl' : W ≤ e.source := hWl
    have : IsDominant (Y.homOfLE hWl') := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
    refine ext_of_isDominant (Y.homOfLE hWl') ?_
    simp only [Scheme.PartialMap.restrict_hom, Scheme.PartialIso.toPartialMap_hom,
      Scheme.Hom.toPartialMap_hom] at hEq
    refine hEq.trans ?_
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι_assoc]
    exact Scheme.homOfLE_ι_assoc Y (show W ≤ ⊤ from hWr) f
  rw [MMP.Flips.RationalMap.IsOver, ← hinv]
  refine Scheme.PartialMap.toRationalMap_eq_iff.mpr
    ⟨e.target, e.dense_target, le_rfl, le_top, ?_⟩
  change Z.homOfLE le_rfl ≫ (e.iso.inv ≫ e.source.ι) ≫ f = Z.homOfLE _ ≫ Z.topIso.hom ≫ 𝟙 Z
  rw [Category.assoc, ← key, Iso.inv_hom_id_assoc]
  simp

/-- A prime divisor of a normal variety `Y` is determined by its divisorial valuation restricted
along a morphism `f : Y ⟶ Z` with `f^*` surjective on function fields. -/
private theorem primeDivisor_eq_of_comap_eq {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sY : Y ⟶ Spec (.of k)} (hY : IsNormalVariety k sY) [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ Z} [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P Q : MMP.Mori.PrimeDivisor Y}
    (h : P.divisorialValuation.comap (functionFieldMap f) =
      Q.divisorialValuation.comap (functionFieldMap f)) : P = Q := by
  refine primeDivisor_eq_of_divisorialValuation_eq hY (Valuation.ext fun t => ?_)
  obtain ⟨s, rfl⟩ := hf t
  exact congrArg (fun w => w s) h

/-- If a prime divisor `P` of `Y` and a prime divisor `Q` of `Z` induce the same valuation of
`k(Z)` through a birational morphism `f : Y ⟶ Z`, then `f(η_P) = η_Q`. -/
private theorem map_genericPoint_eq_of_comap_eq {k : Type u} [Field k] {Y Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} (hZ : IsNormalVariety k sZ) [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z] {f : Y ⟶ Z}
    (hY : IsNormalVariety k (f ≫ sZ)) (hf : IsBirationalMorphism f) [IsDominant f]
    {P : MMP.Mori.PrimeDivisor Y} {Q : MMP.Mori.PrimeDivisor Z}
    (h : P.divisorialValuation.comap (functionFieldMap f) =
      Q.divisorialValuation.comap (functionFieldMap (𝟙 Z))) :
    f P.genericPoint = Q.genericPoint :=
  MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hZ.1
    (D := ⟨Y, f, hY, hf, P⟩) (D' := DivisorOver.ofPrimeDivisor k hZ Q) h

/-- The smooth locus of a scheme locally of finite type over a field is smooth. -/
private theorem smooth_smoothLocus_ι {Y : Scheme.{u}} (s : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType s] : Smooth ((smoothLocus s).ι ≫ s) := by
  have : LocallyOfFinitePresentation s :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  rw [smoothLocus_eq_smoothLocus]
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq,
    Scheme.Opens.ι_preimage_self]

end PrimeDivisors

/-! ### Flips preserve canonical pairs -/

section Forms

variable {k : Type u} [Field k] [PerfectField k] {Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
  [IsIntegral Y] [IsIntegral Z] [LocallyOfFiniteType sZ] {f : Y ⟶ Z} [IsDominant f]

/-- Along a birational morphism `f : Y ⟶ Z`, every nonzero rational `n`-form on `Y` is the
pull-back of a nonzero one on `Z`. -/
private theorem exists_pullbackRationalPluriForms_eq
    (hf : Function.Bijective (functionFieldMap f)) {n : ℕ} (hn : topologicalKrullDim Z = n)
    {ω : RationalPluriForms (f ≫ sZ) n 1} (hω : ω ≠ 0) :
    ∃ τ : RationalPluriForms sZ n 1, τ ≠ 0 ∧ pullbackRationalPluriForms sZ f τ = ω := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hn
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  obtain ⟨ω₀, hω₀⟩ := exists_isPullbackGenerator_of_bijective sZ f hf hd
  obtain ⟨c, hc⟩ := hf.2 ((ZTensorPower.basis (basisOfSpanSingleton hω₀.2.1 hω₀.2.2) 1).repr ω ())
  let τ : RationalPluriForms sZ n 1 :=
    c • ZTensorPower.basis (basisOfSpanSingleton hω₀.1 hω₀.ne_zero) 1 ()
  have hpull : pullbackRationalPluriForms sZ f τ = ω := by
    change pullbackForms (K := Z.functionField) (K' := Y.functionField) 1 _ = ω
    rw [pullbackForms_eq hω₀, pullbackFormsAlong]
    simp only [τ, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    change functionFieldMap f c • _ = ω
    rw [hc]
    exact basis_unit_repr_smul _ ω
  refine ⟨τ, fun h0 => hω ?_, hpull⟩
  rw [← hpull, h0]
  change pullbackForms (K := Z.functionField) (K' := Y.functionField) 1 0 = 0
  rw [pullbackForms_eq hω₀, pullbackFormsAlong]
  simp

/-- Pulling back along a birational morphism does not kill a nonzero rational `n`-form. -/
private theorem pullbackRationalPluriForms_ne_zero
    (hf : Function.Bijective (functionFieldMap f)) {n : ℕ} (hn : topologicalKrullDim Z = n)
    {τ : RationalPluriForms sZ n 1} (hτ : τ ≠ 0) : pullbackRationalPluriForms sZ f τ ≠ 0 := by
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hn
  let := functionFieldAlgebra sZ
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sZ f hf hd
  let := functionFieldAlgebra (f ≫ sZ)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sZ f
  have hpull : pullbackRationalPluriForms sZ f τ = pullbackFormsAlong hω 1 τ :=
    pullbackForms_eq hω 1 τ
  have hrepr := repr_pullbackFormsAlong hω 1 τ
  intro h0
  have h0' : pullbackFormsAlong hω 1 τ = 0 := hpull ▸ h0
  have h1 : algebraMap Z.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) 1).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ
    ((map_eq_zero_iff _ (algebraMap Z.functionField Y.functionField).injective).mp h1)

variable [IsLocallyNoetherian Y] [IsNormal Y] [IsLocallyNoetherian Z] [IsNormal Z]

/-- `ord_P(f^*τ) = ord_Q(τ)` for a birational morphism `f` with `f(η_P) = η_Q`. -/
private theorem ordForm_pullbackRationalPluriForms_of_map_genericPoint_eq
    (hf : Function.Bijective (functionFieldMap f)) {n : ℕ} (hn : topologicalKrullDim Z = n)
    {P : MMP.Mori.PrimeDivisor Y} {Q : MMP.Mori.PrimeDivisor Z}
    (h : f P.genericPoint = Q.genericPoint) (τ : RationalPluriForms sZ n 1) :
    P.ordForm (pullbackRationalPluriForms sZ f τ) = Q.ordForm τ := by
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Z.presheaf.stalk (f P.genericPoint)) := by rw [h]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing f hf P.genericPoint
  exact MMP.Positivity.ordForm_pullbackRationalPluriForms_of_isIso f hf
    (toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sZ) hn) P Q h τ

end Forms

/-- **A normal variety over a perfect field has a canonical divisor.** On the smooth locus
`T = S_sm`, which contains the generic point, the canonical sheaf is `𝒪_T(K_T)` for a divisor
`K_T` of `T`; its closure `K_S` in `S` restricts to `K_T` on `T`, so
`𝒪_S(K_S)|_T ≅ 𝒪_T(K_T) ≅ ω_T`. -/
private theorem exists_isCanonicalDivisor {K : Type u} [Field K] [PerfectField K]
    {S : Scheme.{u}} (sS : S ⟶ Spec (.of K)) [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] (hS : IsNormalVariety K sS) {n : ℕ} (hn : topologicalKrullDim S = n) :
    ∃ KS : MMP.Mori.Divisor S, KS.IsCanonicalDivisor sS n := by
  haveI : LocallyOfFiniteType sS := hS.1.toLocallyOfFiniteType
  set T := MMP.Mori.smoothLocus sS
  have hTeq : T = sS.smoothLocus := MMP.Mori.smoothLocus_eq_smoothLocus sS
  haveI : Nonempty T := ⟨⟨genericPoint S, hTeq ▸ sS.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  haveI : IsDominant T.ι := isDominant_of_isOpenImmersion' T.ι
  have hTv : IsNormalVariety K (T.ι ≫ sS) := isNormalVariety_ι hS T
  haveI : MMP.Mori.IsVariety K (T.ι ≫ sS) := hTv.1
  haveI : QuasiCompact (T.ι ≫ sS) := hTv.1.toQuasiCompact
  haveI : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T.ι ≫ sS)
  have hsm : MMP.Mori.IsSmoothScheme (T.ι ≫ sS) := by
    rw [MMP.Mori.isSmoothScheme_iff, ← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq, ← hTeq, Scheme.Opens.ι_preimage_self]
  have hdimT : topologicalKrullDim T = n :=
    (topologicalKrullDim_opens_eq hS T).trans hn
  obtain ⟨KT, hKT⟩ := MMP.Mori.exists_isCanonicalDivisor_of_isSmoothScheme (T.ι ≫ sS) hsm hdimT
  classical
  let KS : MMP.Mori.Divisor S := Finsupp.mapDomain (OpenWeilRestriction.primeDivisorMap T.ι) KT
  have hKS : restrictDivisorAlong T.ι KS = KT := by
    ext W
    exact Finsupp.mapDomain_apply_of_injective (OpenWeilRestriction.primeDivisorMap_injective T.ι) KT W
  obtain ⟨e₀⟩ := nonempty_divisorialSheaf_restrictDivisorAlong_iso T.ι KS
  set T' := MMP.Mori.smoothLocus (T.ι ≫ sS)
  obtain ⟨e₁⟩ := nonempty_restrict_relativeDifferentialForms_iso T'.ι
    (T.ι ≫ sS) (T'.ι ≫ T.ι ≫ sS) rfl n
  obtain ⟨e₂⟩ := MMP.Flips.nonempty_iso_of_restrict_iso (M := KT.divisorialSheaf)
    (N := Scheme.Hom.relativeDifferentialForms (T.ι ≫ sS) n) hsm (hKT.iso ≪≫ e₁.symm)
  refine ⟨KS, hn, ⟨e₀.symm ≪≫ ?_ ≪≫ e₂⟩⟩
  rw [hKS]

/-- On a normal variety over a perfect field, the divisor of a nonzero rational top form is a
canonical divisor. -/
private theorem isCanonicalDivisor_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {S : Scheme.{u}} {sS : S ⟶ Spec (.of k)} [IsIntegral S] [IsLocallyNoetherian S] [IsNormal S]
    [CompactSpace S] [LocallyOfFiniteType sS] (hS : IsNormalVariety k sS) {n : ℕ}
    (hn : topologicalKrullDim S = n) {τ : RationalPluriForms sS n 1} (hτ : τ ≠ 0) :
    (divisorOfForm τ).IsCanonicalDivisor sS n := by
  obtain ⟨K₀, hK₀⟩ := exists_isCanonicalDivisor sS hS hn
  exact hK₀.of_linearlyEquivalent (by
    simpa using MMP.Positivity.linearlyEquivalent_divisorOfForm_zsmul hS hK₀ hτ)

/-- Every exceptional divisor `E` over a canonical pair `(X, D)` has a discrepancy
`a(E, X, D) ≥ 0`: the discrepancy computed from a top form `ω` with `div(ω) = K` bounds
`discrep(X, D)` from above. -/
private theorem exists_isDiscrepancy_nonneg_of_isCanonicalPair {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] {n : ℕ}
    {K : MMP.Mori.Divisor X} {D : MMP.Mori.QDivisor X} (hD : MMP.Flips.IsCanonicalPair sX n K D)
    {E : ProperDivisorOver k sX} (hE : E.IsExceptional) :
    ∃ a : ℝ, 0 ≤ a ∧ IsDiscrepancy sX n K (QDivisor.toRDivisor D) E.valuation a := by
  obtain ⟨hXn, hK, -, hKDq, hdisc⟩ := hD
  haveI : QuasiCompact sX := hXn.1.toQuasiCompact
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hK
  have hKDω : (MMP.Mori.Divisor.toQDivisor (divisorOfForm ω) + D).IsQCartier :=
    (DivisorWithCoeffs.ext' hω : divisorOfForm ω = K) ▸ hKDq
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  haveI : QuasiCompact (E.f ≫ sX) := E.isNormalVariety.1.toQuasiCompact
  haveI : CompactSpace E.Y := QuasiCompact.compactSpace_of_compactSpace (E.f ≫ sX)
  have hB : ∀ W : irreducibleComponents E.Y, E.f (componentGenericPoint E.Y W) ∉
      (MMP.Mori.Divisor.toQDivisor (divisorOfForm ω) + D).supp := fun W =>
    MMP.Fourfold.map_componentGenericPoint_notMem_supp_of_isQCartier E.f hKDω W
  have ha : IsQDiscrepancyWith sX n D ω E ((E.toDivisorOver.ordPullback ω : ℚ) -
      ((MMP.Mori.Divisor.toQDivisor (divisorOfForm ω) + D).pullback hKDω hB).coeff E.E) :=
    ⟨hXn, hK.topologicalKrullDim_eq, hω0, hKDω, hB, _,
      MMP.Mori.QDivisor.isPullback_pullback hKDω hB, rfl⟩
  exact ⟨_, EReal.coe_nonneg.mp (hdisc.trans (sInf_le ⟨E, ω, _, hE, ha, rfl⟩)),
    ha.isDiscrepancy hK hKDq hE⟩

/-- **Flips preserve canonical pairs.** Let `(X, D)` be a canonical pair of dimension `n` with
canonical divisor `K`, and let `φ⁺ : X⁺ ⟶ Z` with `g : X ⤏ X⁺` be a flip of the small contraction
`φ : X ⟶ Z` with respect to `K_X + D` (`MMP.Flips.IsFlip`). Then `(X⁺, g_*D)` is a canonical
pair with canonical divisor `g_*K`. -/
@[mmp "lem_fa4_flip_preserves_canonical"]
public theorem IsCanonicalPair.of_isFlip {k : Type u} [Field k] [PerfectField k]
    {X Z X' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX']
    {n : ℕ} {K : Divisor X} {D : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} {g : X.RationalMap X'}
    (hD : IsCanonicalPair sX n K D)
    (hflip : IsFlip k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g) :
    IsCanonicalPair sX' n (Mori.RationalMap.transformDivisor g K)
      (Mori.RationalMap.transformDivisor g D) := by
  obtain ⟨hXn, hK, hDeff, -⟩ := id hD
  have hφs : IsSmall k sZ sX φ := hflip.isSmall_source
  have hφps : IsSmall k sZ sX' φp := hflip.isSmall
  have hZn : IsNormalVariety k sZ := hflip.isNormalVariety_target
  have hX'n : IsNormalVariety k sX' := hflip.isNormalVariety_flip
  have hamp := hflip.isRelativelyAntiAmple
  have hamp' := hflip.isRelativelyAmple_transform
  have hcart := hflip.isCartierCombination_transform
  have hmod := hflip.isModificationOf
  obtain rfl : φ ≫ sZ = sX := hφs.comp_eq
  obtain rfl : φp ≫ sZ = sX' := hφps.comp_eq
  haveI : IsIntegral Z := hZn.1.toIsIntegral
  haveI : IsNormal Z := hZn.2
  haveI : LocallyOfFiniteType sZ := hZn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : QuasiCompact sZ := hZn.1.toQuasiCompact
  haveI : IsSeparated sZ := hZn.1.toIsSeparated
  haveI : Z.IsSeparated := ⟨by rw [← Limits.terminal.comp_from sZ]; infer_instance⟩
  haveI : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace sZ
  haveI : IsProper φ := hφs.isProper
  haveI : IsProper φp := hφps.isProper
  haveI : QuasiCompact (φ ≫ sZ) := hXn.1.toQuasiCompact
  haveI : QuasiCompact (φp ≫ sZ) := hX'n.1.toQuasiCompact
  have hbφ : IsBirationalMorphism φ := hφs.surjective_and_isBirational.2
  have hbφp : IsBirationalMorphism φp := hφps.surjective_and_isBirational.2
  haveI : IsDominant φ := hbφ.isDominant
  haveI : IsDominant φp := hbφp.isDominant
  have hnX : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
  have hnZ : topologicalKrullDim Z = n := hφs.dim_eq.symm.trans hnX
  have hnX' : topologicalKrullDim X' = n := hφps.dim_eq.trans hnZ
  -- the bijections of prime divisors induced by `g`, `φ⁻¹` and `φ⁺⁻¹`
  have he := (exceptional_hasNonemptyCenter_iff_of_isSmall _ _ sZ φ φp hφs hφps).2 g hmod
  set e := primeDivisorEquivOfModification hφs hφps hmod
  have he₂ := (exceptional_hasNonemptyCenter_iff_of_isSmall sZ _ sZ (𝟙 Z) φ
    (isSmall_id hZn.1) hφs).2 _ (isModificationOf_inverse φ hbφ)
  set e₂ := primeDivisorEquivOfModification (isSmall_id hZn.1) hφs (isModificationOf_inverse φ hbφ)
  have he₃ := (exceptional_hasNonemptyCenter_iff_of_isSmall sZ _ sZ (𝟙 Z) φp
    (isSmall_id hZn.1) hφps).2 _ (isModificationOf_inverse φp hbφp)
  set e₃ := primeDivisorEquivOfModification
    (isSmall_id hZn.1) hφps (isModificationOf_inverse φp hbφp)
  have he₃e : ∀ Q, e₃ Q = e (e₂ Q) := fun Q => primeDivisor_eq_of_comap_eq hX'n
    hbφp.functionFieldMap_bijective.2 ((he₃ Q).2.trans ((he (e₂ Q)).2.trans (he₂ Q).2).symm)
  have hgen₂ : ∀ Q, φ (e₂ Q).genericPoint = Q.genericPoint := fun Q =>
    map_genericPoint_eq_of_comap_eq hZn hXn hbφ (he₂ Q).2
  have hgen₃ : ∀ Q, φp (e₃ Q).genericPoint = Q.genericPoint := fun Q =>
    map_genericPoint_eq_of_comap_eq hZn hX'n hbφp (he₃ Q).2
  have hcoeff : ∀ {R : Type} [AddCommMonoid R] (B : MMP.Mori.DivisorWithCoeffs R X) P,
      MMP.Mori.RationalMap.transformDivisor g B (e P) = B P :=
    fun B P => transformDivisor_apply_equiv e (fun P => (he P).1) B P
  -- `g_*D` is effective
  have hD'eff : (MMP.Mori.RationalMap.transformDivisor g D).IsEffective := fun P' => by
    obtain ⟨P, rfl⟩ := e.surjective P'
    change 0 ≤ MMP.Mori.RationalMap.transformDivisor g D (e P)
    rw [hcoeff]
    exact hDeff P
  -- `K = div(φ^*τ)` and `g_*K = div(φ⁺^*τ)` for a rational top form `τ` on `Z`
  obtain ⟨ω, hω0, hω⟩ := MMP.Positivity.IsCanonicalDivisor.exists_ordForm_eq hXn hK
  obtain ⟨τ, hτ0, hτ⟩ := exists_pullbackRationalPluriForms_eq hbφ.functionFieldMap_bijective
    hnZ hω0
  have hdivX : divisorOfForm (pullbackRationalPluriForms sZ φ τ) = K := by
    rw [hτ]
    exact DivisorWithCoeffs.ext' hω
  have hdivX' : divisorOfForm (pullbackRationalPluriForms sZ φp τ) =
      MMP.Mori.RationalMap.transformDivisor g K := by
    refine DivisorWithCoeffs.ext' fun P' => ?_
    obtain ⟨Q, rfl⟩ := e₃.surjective P'
    rw [coeff_divisorOfForm, ordForm_pullbackRationalPluriForms_of_map_genericPoint_eq
      hbφp.functionFieldMap_bijective hnZ (hgen₃ Q) τ]
    change _ = MMP.Mori.RationalMap.transformDivisor g K (e₃ Q)
    rw [he₃e, hcoeff]
    change _ = K.coeff (e₂ Q)
    rw [← hω (e₂ Q), ← hτ,
      ordForm_pullbackRationalPluriForms_of_map_genericPoint_eq
        hbφ.functionFieldMap_bijective hnZ (hgen₂ Q) τ]
  -- `g_*K` is a canonical divisor
  have hK' : MMP.Mori.Divisor.IsCanonicalDivisor (φp ≫ sZ) n
      (MMP.Mori.RationalMap.transformDivisor g K) := hdivX' ▸ isCanonicalDivisor_divisorOfForm
    hX'n hnX' (pullbackRationalPluriForms_ne_zero hbφp.functionFieldMap_bijective hnZ hτ0)
  -- `g_*K + g_*D = g_*(K + D)` is `ℚ`-Cartier
  have hsum : MMP.Mori.QDivisor.toRDivisor (MMP.Mori.Divisor.toQDivisor
      (MMP.Mori.RationalMap.transformDivisor g K) + MMP.Mori.RationalMap.transformDivisor g D) =
      MMP.Mori.RationalMap.transformDivisor g
        (logCanonicalDivisor K (MMP.Mori.QDivisor.toRDivisor D)) := by
    refine Finsupp.ext fun P' => ?_
    obtain ⟨P, rfl⟩ := e.surjective P'
    rw [hcoeff]
    simp only [map_add, MMP.Mori.QDivisor.toRDivisor_toQDivisor, Finsupp.add_apply,
      logCanonicalDivisor]
    change ((MMP.Mori.RationalMap.transformDivisor g K (e P) : ℤ) : ℝ) +
        ((MMP.Mori.RationalMap.transformDivisor g D (e P) : ℚ) : ℝ) =
      ((K P : ℤ) : ℝ) + ((D P : ℚ) : ℝ)
    rw [hcoeff, hcoeff]
  have hKD' : (MMP.Mori.Divisor.toQDivisor (MMP.Mori.RationalMap.transformDivisor g K) +
      MMP.Mori.RationalMap.transformDivisor g D).IsQCartier :=
    MMP.Flips.QDivisor.isQCartier_of_isCartierCombination (hsum ▸ hcart)
  -- the divisor `D_Z` on `Z` with `φ⁻¹_* D_Z = D`, and `φ⁺⁻¹_* D_Z = g_* D`
  let DZ : MMP.Mori.RDivisor Z := Finsupp.equivMapDomain e₂.symm (MMP.Mori.QDivisor.toRDivisor D)
  have hDZ : ∀ Q, DZ Q = MMP.Mori.QDivisor.toRDivisor D (e₂ Q) := fun Q => by
    simp [DZ, Finsupp.equivMapDomain_apply]
  have hbit1 : birationalInverseTransform φ hbφ DZ = MMP.Mori.QDivisor.toRDivisor D := by
    refine Finsupp.ext fun P => ?_
    obtain ⟨Q, rfl⟩ := e₂.surjective P
    exact (transformDivisor_apply_equiv e₂ (fun Q => (he₂ Q).1) DZ Q).trans (hDZ Q)
  have hbit2 : birationalInverseTransform φp hbφp DZ =
      MMP.Mori.QDivisor.toRDivisor (MMP.Mori.RationalMap.transformDivisor g D) := by
    refine Finsupp.ext fun P' => ?_
    obtain ⟨Q, rfl⟩ := e₃.surjective P'
    rw [birationalInverseTransform, transformDivisor_apply_equiv e₃ (fun Q => (he₃ Q).1) DZ Q,
      hDZ, he₃e]
    change _ = ((MMP.Mori.RationalMap.transformDivisor g D (e (e₂ Q)) : ℚ) : ℝ)
    rw [hcoeff]
    rfl
  have hlogX' : logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor g K)
      (birationalInverseTransform φp hbφp DZ + 0) =
      MMP.Mori.RationalMap.transformDivisor g
        (logCanonicalDivisor K (MMP.Mori.QDivisor.toRDivisor D)) := by
    rw [hbit2, add_zero, ← hsum, map_add, MMP.Mori.QDivisor.toRDivisor_toQDivisor]
    rfl
  have hAX : IsRelativelyNef k (φ ≫ sZ) φ
      (-logCanonicalDivisor K (birationalInverseTransform φ hbφ DZ + 0)) := by
    rw [hbit1, add_zero]
    exact isRelativelyNef_of_isRelativelyAmple hamp
  have hAY : IsRelativelyNef k (φp ≫ sZ) φp
      (logCanonicalDivisor (MMP.Mori.RationalMap.transformDivisor g K)
        (birationalInverseTransform φp hbφp DZ + 0)) := by
    rw [hlogX']
    exact isRelativelyNef_of_isRelativelyAmple hamp'
  -- the discrepancies
  refine ⟨hX'n, hK', hD'eff, hKD', le_sInf ?_⟩
  rintro x ⟨E', ω', a, hE', ha, rfl⟩
  have ha' := ha.isDiscrepancy hK' hKD' hE'
  set v := E'.valuation.comap (functionFieldMap φp)
  let eφ := RingEquiv.ofBijective (functionFieldMap φ) hbφ.functionFieldMap_bijective
  let vX : Valuation X.functionField ℤᵐ⁰ := v.comap eφ.symm.toRingHom
  have hvX : vX.comap (functionFieldMap φ) = v :=
    Valuation.ext fun t => congrArg v (eφ.symm_apply_apply t)
  obtain ⟨-, EX, hEXv, hEXe⟩ := ((exceptional_hasNonemptyCenter_iff_of_isSmall _ _ sZ φ φp hφs
    hφps).1 vX E'.valuation hvX).2 ⟨ha'.2.2.1, E', rfl, hE'⟩
  have hvZ : HasNonemptyCenter k sZ v :=
    (((exceptional_hasNonemptyCenter_iff_of_isSmall _ sZ sZ φp (𝟙 Z) hφps (isSmall_id hZn.1)).1
      E'.valuation v (Valuation.ext fun t => by
        change v t = v (functionFieldMap (𝟙 Z) t)
        rw [functionFieldMap_id_apply])).1 ⟨ha'.2.2.1, E', rfl, hE'⟩).1
  obtain ⟨a₀, h0, ha₀'⟩ := exists_isDiscrepancy_nonneg_of_isCanonicalPair hD hEXe
  -- the comparison of discrepancies over `Z`
  have key := (isDiscrepancy_le_of_isRelativelyNef hZn hXn hX'n hbφ hbφp hdivX hdivX'
    (D := DZ) (E_X := 0) (E_Y := 0) (fun _ _ => rfl) (fun _ _ => rfl) hAX hAY hvZ hvX rfl).2.2
    _ _ (by rwa [hbit1, add_zero, ← hEXv]) (by rwa [hbit2, add_zero])
  exact EReal.coe_nonneg.mpr (h0.trans key)

/-! ### Sets of small log discrepancy shrink under flips -/

section Flip

variable {k : Type u} [Field k]

/-- A nonzero top form exists on `k(X)` when one exists on `k(X')`, `X` and `X'` being
birational over `Z`. -/
private theorem exists_ne_zero_of_bijective {X Z X' : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsIntegral X'] [IsIntegral Z] (φ : X ⟶ Z) (φp : X' ⟶ Z) [IsDominant φ]
    [IsDominant φp] (hφ : Function.Bijective (functionFieldMap φ))
    (hφp : Function.Bijective (functionFieldMap φp)) {n : ℕ}
    {ω' : RationalPluriForms (φp ≫ sZ) n 1} (hω' : ω' ≠ 0) :
    ∃ ω : RationalPluriForms (φ ≫ sZ) n 1, ω ≠ 0 := by
  let := functionFieldAlgebra sZ
  let := functionFieldAlgebra (φ ≫ sZ)
  let := functionFieldAlgebra (φp ≫ sZ)
  let := functionFieldMapAlgebra φ
  let := functionFieldMapAlgebra φp
  have := isScalarTower_functionFieldMap sZ φ
  have := isScalarTower_functionFieldMap sZ φp
  let e' : RationalPluriForms (φp ≫ sZ) n 1 ≃ₗ[X'.functionField]
      ⋀[X'.functionField]^n Ω[X'.functionField⁄k] := PiTensorProduct.subsingletonEquiv 0
  let e : RationalPluriForms (φ ≫ sZ) n 1 ≃ₗ[X.functionField]
      ⋀[X.functionField]^n Ω[X.functionField⁄k] := PiTensorProduct.subsingletonEquiv 0
  have h1 : Nontrivial (⋀[X'.functionField]^n Ω[X'.functionField⁄k]) :=
    ⟨⟨e' ω', 0, fun h => hω' (e'.injective (by rw [h, map_zero]))⟩⟩
  have h2 := nontrivial_of_bijective' (K := Z.functionField) hφp h1
  obtain ⟨x, hx⟩ := exists_ne (0 : ⋀[Z.functionField]^n Ω[Z.functionField⁄k])
  have h3 : topFormsMap k Z.functionField X.functionField n x ≠ 0 := fun h =>
    hx (topFormsMap_injective_of_bijective hφ (by rw [h, map_zero]))
  exact ⟨e.symm (topFormsMap k Z.functionField X.functionField n x), fun h =>
    h3 (e.symm.injective (by rw [h, map_zero]))⟩

/-- **Transport of a top form along a flip.** Let `φ : X ⟶ Z`, `φ⁺ : X⁺ ⟶ Z` induce isomorphisms
of function fields, with a bijection `e` of prime divisors compatible with the valuations over
`k(Z)`, and let `K`, `K'` be divisors with `coeff_{e P} K' = coeff_P K`. For a nonzero rational top
form `ω'` on `X⁺` with `div ω' = K'` there is a nonzero rational top form `ω` on `X` with
`div ω = K` whose order along any divisor `P₀` over `X` is the order of `ω'` along any divisor
`E` over `X⁺` inducing the same valuation of `k(Z)`. -/
private theorem exists_form_eq {X Z X' : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
    [CompactSpace X'] [IsIntegral Z] (φ : X ⟶ Z) (φp : X' ⟶ Z) [LocallyOfFiniteType (φ ≫ sZ)]
    [LocallyOfFiniteType (φp ≫ sZ)] [IsDominant φ] [IsDominant φp]
    (hφ : Function.Bijective (functionFieldMap φ))
    (hφp : Function.Bijective (functionFieldMap φp))
    (e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor X')
    (hev : ∀ P, (e P).divisorialValuation.comap (functionFieldMap φp) =
      P.divisorialValuation.comap (functionFieldMap φ))
    {n : ℕ} {K : Divisor X} {K' : Divisor X'} (hKK : ∀ P, K'.coeff (e P) = K.coeff P)
    {ω' : RationalPluriForms (φp ≫ sZ) n 1} (hω'0 : ω' ≠ 0) (hω'K : divisorOfForm ω' = K')
    {W Y : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (p : W ⟶ X) (f : Y ⟶ X') [IsDominant p] [IsDominant f]
    (hp : Function.Bijective (functionFieldMap p)) (hf : Function.Bijective (functionFieldMap f))
    (P₀ : Mori.PrimeDivisor W) (E : Mori.PrimeDivisor Y)
    (hv : P₀.divisorialValuation.comap (functionFieldMap (p ≫ φ)) =
      E.divisorialValuation.comap (functionFieldMap (f ≫ φp))) :
    ∃ ω : RationalPluriForms (φ ≫ sZ) n 1, ω ≠ 0 ∧ divisorOfForm ω = K ∧
      P₀.ordForm (pullbackRationalPluriForms (φ ≫ sZ) p ω) =
        E.ordForm (pullbackRationalPluriForms (φp ≫ sZ) f ω') := by
  have hpφ : Function.Bijective (functionFieldMap (p ≫ φ)) := by
    have h := hp.comp hφ
    convert h using 1
    ext z
    exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply p φ z).symm
  have hfφ : Function.Bijective (functionFieldMap (f ≫ φp)) := by
    have h := hf.comp hφp
    convert h using 1
    ext z
    exact (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply f φp z).symm
  by_cases hl : letI := functionFieldAlgebra sZ
    ∃ ω : ⋀[Z.functionField]^n Ω[Z.functionField⁄k], Submodule.span Z.functionField {ω} = ⊤ ∧
      ω ≠ 0
  · obtain ⟨ωZ, hωZ⟩ : ∃ ωZ : RationalPluriForms sZ n 1,
        pullbackRationalPluriForms sZ φp ωZ = ω' := by
      let := functionFieldAlgebra sZ
      let := functionFieldAlgebra (φp ≫ sZ)
      let := functionFieldMapAlgebra φp
      have := isScalarTower_functionFieldMap sZ φp
      exact exists_pullbackForms_eq_of_bijective (m := 1) hφp hl
        (show PluriForms k X'.functionField n 1 from ω')
    have hωZ0 : ωZ ≠ 0 := by
      rintro rfl
      apply hω'0
      rw [← hωZ]
      let := functionFieldAlgebra sZ
      let := functionFieldAlgebra (φp ≫ sZ)
      let := functionFieldMapAlgebra φp
      have := isScalarTower_functionFieldMap sZ φp
      exact pullbackForms_zero
    refine ⟨pullbackRationalPluriForms sZ φ ωZ, ?_, ?_, ?_⟩
    · let := functionFieldAlgebra sZ
      let := functionFieldAlgebra (φ ≫ sZ)
      let := functionFieldMapAlgebra φ
      have := isScalarTower_functionFieldMap sZ φ
      exact pullbackForms_ne_zero_of_bijective hφ hl hωZ0
    · ext P
      change (divisorOfForm _).coeff P = K.coeff P
      rw [coeff_divisorOfForm, ← hKK, ← hω'K, coeff_divisorOfForm, ← hωZ]
      exact ordForm_pullback_eq_of_valuation_eq φ φp hφ hφp P (e P) (hev P).symm ωZ
    · rw [pullbackRationalPluriForms_comp_of_bijective φ p hφ hp ωZ, ← hωZ,
        pullbackRationalPluriForms_comp_of_bijective φp f hφp hf ωZ]
      exact ordForm_pullback_eq_of_valuation_eq (p ≫ φ) (f ≫ φp) hpφ hfφ P₀ E hv ωZ
  · have hlX' := fun h => hl ((exists_span_eq_top_iff_of_bijective sZ φp hφp n).2 h)
    have hlW := fun h => hl ((exists_span_eq_top_iff_of_bijective sZ (p ≫ φ) hpφ n).2 h)
    have hlY := fun h => hl ((exists_span_eq_top_iff_of_bijective sZ (f ≫ φp) hfφ n).2 h)
    have hK0 : K = 0 := by
      ext P
      change K.coeff P = 0
      rw [← hKK, ← hω'K, coeff_divisorOfForm]
      exact ordForm_eq_zero_of_not hlX' (e P) ω'
    obtain ⟨ω, hω⟩ := exists_ne_zero_of_bijective φ φp hφ hφp hω'0
    subst hK0
    refine ⟨ω, hω, ?_, ?_⟩
    · ext P
      change (divisorOfForm _).coeff P = 0
      rw [coeff_divisorOfForm]
      exact ordForm_eq_zero_of_not
        (fun h => hl ((exists_span_eq_top_iff_of_bijective sZ φ hφ n).2 h)) P ω
    · rw [ordForm_eq_zero_of_not (sX := p ≫ φ ≫ sZ) hlW,
        ordForm_eq_zero_of_not (sX := f ≫ φp ≫ sZ) hlY]

/-- The transform of `K + D` under `g` is `g_*K + g_*D`. -/
private theorem transformDivisor_logCanonicalDivisor {X X' : Scheme.{u}} {g : X.RationalMap X'}
    (e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor X')
    (he : ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P)) (K : Divisor X)
    (D : QDivisor X) :
    Mori.RationalMap.transformDivisor g (logCanonicalDivisor K (QDivisor.toRDivisor D)) =
      Divisor.toRDivisor (Mori.RationalMap.transformDivisor g K) +
        QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D) := by
  ext Q
  obtain ⟨P, rfl⟩ := e.surjective Q
  change (Mori.RationalMap.transformDivisor g _).coeff (e P) = _
  rw [show (Mori.RationalMap.transformDivisor g
      (logCanonicalDivisor K (QDivisor.toRDivisor D))).coeff (e P) =
      (logCanonicalDivisor K (QDivisor.toRDivisor D)).coeff P from
    transformDivisor_apply_equiv e he _ P]
  simp only [logCanonicalDivisor, DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor,
    QDivisor.coeff_toRDivisor]
  rw [show (Mori.RationalMap.transformDivisor g K).coeff (e P) = K.coeff P from
      transformDivisor_apply_equiv e he K P,
    show (Mori.RationalMap.transformDivisor g D).coeff (e P) = D.coeff P from
      transformDivisor_apply_equiv e he D P]

/-- The coefficient of the pull-back `G = f^*N` of an `ℝ`-Cartier divisor along a prime divisor
`E` with center the prime divisor `P` and valuation `ord_P` is the coefficient of `N` along `P`. -/
private theorem coeff_isRCartierPullback_eq_coeff {X Y : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (f : Y ⟶ X) [IsDominant f] (E : Mori.PrimeDivisor Y) (P : Mori.PrimeDivisor X)
    (hv : E.divisorialValuation.comap (functionFieldMap f) = P.divisorialValuation)
    (hx : f E.genericPoint = P.genericPoint) {N : RDivisor X} {G : RDivisor Y}
    (h : IsRCartierPullback f N G) : G.coeff E = N.coeff P := by
  obtain ⟨m, r, L, L', hL, rfl, hpb, rfl⟩ := h
  rw [coeff_sum_smul_toRDivisor, coeff_sum_smul_toRDivisor]
  exact Finset.sum_congr rfl fun j _ => by
    rw [coeff_isPullback_eq_coeff f E P hv hx (hL j) (hpb j).2]

/-- **The negativity lemma, relative form.** Let `h : W ⟶ Z` be a proper birational morphism of
normal varieties and `M` an `h`-nef `ℝ`-Cartier divisor on `W` such that `-M` has nonnegative
coefficients along the prime divisors not exceptional over `Z`. Then `-M` is effective. -/
private theorem isEffective_neg_of_isRelativelyNef {k : Type u} [Field k] {W Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian Z]
    [IsNormal Z] [IsLocallyNoetherian W] [IsNormal W] (hZ : IsNormalVariety k sZ)
    (hW : IsNormalVariety k sW) (h : W ⟶ Z) (hh : h ≫ sZ = sW) [IsProper h]
    (hhb : IsBirationalMorphism h) {M : RDivisor W} (hM : IsCartierCombination M)
    (hMnef : IsRelativelyNef k sW h M)
    (hBG : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ h P → 0 ≤ (-M).coeff P) :
    (-M).IsEffective := by
  have h0 : IsCartierCombination (0 : RDivisor W) :=
    ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
  refine isEffective_of_isNumericallyEquivalentOver_pullback k sZ sW hZ hW h hh hhb (L := 0)
    (L' := 0) ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp⟩
    ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun j => j.elim0, by simp, fun j => j.elim0, by simp⟩
    hM hMnef (by simpa using isCartierCombination_sub h0 hM) hBG ?_
  rw [add_neg_cancel]
  exact ⟨h0, h0, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ hx₁ hx₂ =>
    (IsRIntersectionNumber.eq_and_linear k _ C).1 0 r₁ L₁ r₂ L₂ x₁ x₂ hx₁ hx₂⟩

/-- **Comparison of discrepancies across a flip, over any field.** Let `φ : X ⟶ Z` and
`φ⁺ : X⁺ ⟶ Z` be proper birational morphisms of normal varieties, `g : X ⤏ X⁺` inducing a
bijection `e` of prime divisors compatible with the valuations over `k(Z)`. Let `K` be a canonical
divisor of `X` and `D` a `ℚ`-divisor with `K + D` `ℚ`-Cartier, `-(K + D)` `φ`-nef and
`g_*K + g_*D` `φ⁺`-nef. If `a'` is the discrepancy of `ν'` over `(X⁺, g_*D)` and `ν` is the same
divisor of `k(Z)` seen in `k(X)`, with nonempty center on `X`, then `ν` has a discrepancy
`a ≤ a'` over `(X, D)`. -/
private theorem exists_isDiscrepancy_le {X Z X' : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z]
    {φ : X ⟶ Z} {φp : X' ⟶ Z} [LocallyOfFiniteType (φ ≫ sZ)] [LocallyOfFiniteType (φp ≫ sZ)]
    [IsDominant φ] [IsDominant φp] [IsProper φ] [IsProper φp]
    (hZ : IsNormalVariety k sZ) (hX : IsNormalVariety k (φ ≫ sZ))
    (hX' : IsNormalVariety k (φp ≫ sZ))
    (hφ : IsBirationalMorphism φ) (hφp : IsBirationalMorphism φp)
    {g : X.RationalMap X'} (e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor X')
    (he : ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P))
    (hev : ∀ P, (e P).divisorialValuation.comap (functionFieldMap φp) =
      P.divisorialValuation.comap (functionFieldMap φ))
    {n : ℕ} {K : Divisor X} {D : QDivisor X} (hK : K.IsCanonicalDivisor (φ ≫ sZ) n)
    (hD : (Divisor.toQDivisor K + D).IsQCartier)
    (hAX : IsRelativelyNef k (φ ≫ sZ) φ (-(Divisor.toRDivisor K + QDivisor.toRDivisor D)))
    (hAY : IsRelativelyNef k (φp ≫ sZ) φp
      (Divisor.toRDivisor (Mori.RationalMap.transformDivisor g K) +
        QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D)))
    {ν : Valuation X.functionField ℤᵐ⁰} {ν' : Valuation X'.functionField ℤᵐ⁰}
    (hcen : HasNonemptyCenter k (φ ≫ sZ) ν)
    (hν : ν.comap (functionFieldMap φ) = ν'.comap (functionFieldMap φp)) {a' : ℝ}
    (ha' : IsDiscrepancy (φp ≫ sZ) n (Mori.RationalMap.transformDivisor g K)
      (QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D)) ν' a') :
    ∃ a : ℝ, IsDiscrepancy (φ ≫ sZ) n K (QDivisor.toRDivisor D) ν a ∧ a ≤ a' := by
  classical
  obtain ⟨-, -, -, E₁, ω', m', r', L', hE₁v, hω'K, -, -, hω'0, hL'c, hsum', L'', hpb', rfl⟩ := ha'
  haveI := E₁.isIntegral
  haveI := E₁.isNormal
  haveI := E₁.isLocallyNoetherian
  haveI := E₁.isDominant
  haveI := E₁.isProper
  -- a common normal model `W` of `X` and `X⁺` over `Z` on which `ν'` is a prime divisor `P₀`
  obtain ⟨ψ, hψ, hψS⟩ := exists_isBirational_compHom_eq hφp hφ
  obtain ⟨W, q, p, hWq, hqb, hqP, hpP, hpb, -, hcomm, P₀, hP₀⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX' hX
      φp φ ψ hψ hψS E₁.toDivisorOver
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hWq.1.toIsIntegral
  haveI : IsNormal W := hWq.2
  haveI := hWq.1.toLocallyOfFiniteType
  haveI : QuasiCompact (q ≫ φp ≫ sZ) := hWq.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (q ≫ φp ≫ sZ)
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (q ≫ φp ≫ sZ)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hqs : q ≫ φp ≫ sZ = p ≫ φ ≫ sZ := by
    rw [← Category.assoc, hcomm, Category.assoc]
  have hWp : IsNormalVariety k (p ≫ φ ≫ sZ) := hqs ▸ hWq
  haveI := hWp.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ φ ≫ sZ) := hWp.1.toQuasiCompact
  haveI := hX.1.toQuasiCompact
  haveI := hX'.1.toQuasiCompact
  haveI := hX.1.toIsSeparated
  haveI := hX'.1.toIsSeparated
  -- the valuations
  have hv₀ : P₀.divisorialValuation.comap (functionFieldMap (p ≫ φ)) =
      E₁.E.divisorialValuation.comap (functionFieldMap (E₁.f ≫ φp)) := by
    change P₀.valuationOver (p ≫ φ) = E₁.E.valuationOver (E₁.f ≫ φp)
    rw [valuationOver_congr P₀ hcomm.symm, ← comap_valuationOver, ← comap_valuationOver]
    exact congrArg (fun w => w.comap (functionFieldMap φp)) hP₀
  let EX : ProperDivisorOver k (φ ≫ sZ) := ⟨⟨W, p, hWp, hpb, P₀⟩, hpP⟩
  have hEXv : EX.valuation = ν := by
    refine valuation_eq_of_comap_eq hφ ?_
    change (P₀.valuationOver p).comap (functionFieldMap φ) = _
    rw [comap_valuationOver, hν]
    change P₀.divisorialValuation.comap (functionFieldMap (p ≫ φ)) = _
    rw [hv₀, ← hE₁v]
    exact (comap_valuationOver E₁.E E₁.f φp).symm
  -- the form `ω` on `X`
  obtain ⟨ω, hω0, hωK, hωord⟩ := exists_form_eq φ φp hφ.functionFieldMap_bijective
    hφp.functionFieldMap_bijective e hev (K' := Mori.RationalMap.transformDivisor g K)
    (fun P => transformDivisor_apply_equiv e he K P) hω'0 hω'K p E₁.f
    hpb.functionFieldMap_bijective E₁.isBirationalMorphism.functionFieldMap_bijective P₀ E₁.E hv₀
  -- a presentation of `K + D` by the Cartier divisor `C = m (K + D)`
  obtain ⟨mq, hmq, C, hC, hCc⟩ := hD
  have hpres : Divisor.toRDivisor K + QDivisor.toRDivisor D =
      ∑ _j : Fin 1, (mq : ℝ)⁻¹ • Divisor.toRDivisor C := by
    rw [Fin.sum_univ_one]
    ext P
    have h := congrArg (fun B : QDivisor X => B.coeff P) hC
    simp only [Divisor.coeff_toQDivisor, DivisorWithCoeffs.coeff_smul, DivisorWithCoeffs.coeff_add,
      zsmul_eq_mul] at h
    simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, QDivisor.coeff_toRDivisor,
      DivisorWithCoeffs.coeff_smul, smul_eq_mul]
    have hm' : (mq : ℝ) ≠ 0 := by exact_mod_cast hmq
    have h' : ((C.coeff P : ℚ) : ℝ) = ((mq * ((K.coeff P : ℚ) + D.coeff P) : ℚ) : ℝ) :=
      congrArg _ h
    push_cast at h'
    rw [h']
    field_simp
  have hBX : ∀ Z : irreducibleComponents W, p (componentGenericPoint W Z) ∉ C.supp :=
    map_componentGenericPoint_notMem_supp_of_isDominant p C
  let CW := C.pullback hCc hBX
  have hCW : C.IsPullback p hBX CW := Divisor.isPullback_pullback hCc hBX
  have hcartX : IsCartierCombination (Divisor.toRDivisor K + QDivisor.toRDivisor D) :=
    ⟨1, fun _ => (mq : ℝ)⁻¹, fun _ => C, fun _ => hCc, by
      simpa only [toRDivisor_eq_mapCoeffs] using hpres⟩
  refine ⟨(EX.toDivisorOver.ordPullback ω : ℝ) - ∑ _j : Fin 1, (mq : ℝ)⁻¹ * (CW.coeff P₀ : ℝ),
    ⟨hK, hcartX, hcen, EX, ω, 1, fun _ => (mq : ℝ)⁻¹, fun _ => C, hEXv, hωK,
      hX, hK.1, hω0, fun _ => hCc, by rwa [hωK], fun _ => CW,
      fun _ => ⟨hBX, hCW⟩, rfl⟩, ?_⟩
  -- the pull-backs of the presentation of `K⁺ + D⁺` to `W`
  have hBY : ∀ j, ∀ Z : irreducibleComponents W, q (componentGenericPoint W Z) ∉ (L' j).supp :=
    fun j => map_componentGenericPoint_notMem_supp_of_isDominant q (L' j)
  let LW : Fin m' → Divisor W := fun j => (L' j).pullback (hL'c j) (hBY j)
  have hLW : ∀ j, (L' j).IsPullback q (hBY j) (LW j) := fun j =>
    Divisor.isPullback_pullback (hL'c j) (hBY j)
  have hE₁q : (⟨W, q, hWq, hqb, P₀⟩ : DivisorOver k (φp ≫ sZ)).valuation = E₁.valuation := hP₀
  have hxq : E₁.f E₁.E.genericPoint = q P₀.genericPoint :=
    MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX'.1 hE₁q.symm
  have hcoeffY : ∀ j, (L'' j).coeff E₁.E = (LW j).coeff P₀ := fun j =>
    coeff_isPullback_eq_of_valuation_eq E₁.f q E₁.E P₀ hE₁q.symm hxq (hL'c j) (hpb' j).2 (hLW j)
  have hord : (EX.toDivisorOver.ordPullback ω : ℝ) = (E₁.toDivisorOver.ordPullback ω' : ℝ) := by
    exact_mod_cast hωord
  rw [hord]
  simp only [hcoeffY]
  -- the negativity lemma on `W`
  set GX : RDivisor W := ∑ _j : Fin 1, (mq : ℝ)⁻¹ • Divisor.toRDivisor CW with hGXdef
  set GY : RDivisor W := ∑ j, r' j • Divisor.toRDivisor (LW j) with hGYdef
  have hGX : IsRCartierPullback p (Divisor.toRDivisor K + QDivisor.toRDivisor D) GX :=
    ⟨1, fun _ => (mq : ℝ)⁻¹, fun _ => C, fun _ => CW, fun _ => hCc, hpres,
      fun _ => ⟨hBX, hCW⟩, rfl⟩
  have hsumY : Divisor.toRDivisor (Mori.RationalMap.transformDivisor g K) +
      QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D) =
      ∑ j, r' j • Divisor.toRDivisor (L' j) := by rwa [← hω'K]
  have hGY : IsRCartierPullback q (Divisor.toRDivisor (Mori.RationalMap.transformDivisor g K) +
      QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D)) GY :=
    ⟨m', r', L', LW, hL'c, hsumY, fun j => ⟨hBY j, hLW j⟩, rfl⟩
  have hMnef : IsRelativelyNef k (p ≫ φ ≫ sZ) (p ≫ φ) (GY - GX) :=
    isRelativelyNef_sub_of_isRCartierPullback p q rfl hqs φ φp rfl hcomm hAX hAY hGX hGY
  haveI : IsNormal Z := hZ.2
  haveI := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hhb : IsBirationalMorphism (p ≫ φ) := isBirationalMorphism_comp_of_isBirational φ p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hφ)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpb)
  -- `GX` and `GY` agree along the prime divisors not exceptional over `Z`
  have hBG : ∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ (p ≫ φ) P →
      0 ≤ (-(GY - GX)).coeff P := by
    intro P hP
    have hWZ : IsNormalVariety k ((p ≫ φ) ≫ sZ) := by rwa [Category.assoc]
    obtain ⟨Q, -, hQ, -, -⟩ := ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hZ
      (ProperDivisorOver.mk ⟨W, p ≫ φ, hWZ, hhb, P⟩ inferInstance)
      fun h => hP ⟨hWZ, hhb, inferInstance, h⟩
    obtain ⟨P_X, hvX, hxX⟩ :=
      exists_primeDivisor_valuation_eq_of_map_genericPoint_eq hX hφ hWp hpb P Q hQ
    obtain ⟨P_Y, hvY, hxY⟩ := exists_primeDivisor_valuation_eq_of_map_genericPoint_eq hX' hφp hWq
      hqb P Q (by rwa [← Scheme.Hom.comp_apply, hcomm])
    have hPY : P_Y = e P_X := by
      refine primeDivisor_eq_of_divisorialValuation_eq hX' (valuation_eq_of_comap_eq hφp ?_)
      rw [hev P_X, ← hvY, ← hvX]
      change (P.valuationOver q).comap _ = (P.valuationOver p).comap _
      rw [comap_valuationOver, comap_valuationOver]
      exact valuationOver_congr P hcomm
    rw [neg_sub, DivisorWithCoeffs.coeff_sub, coeff_isRCartierPullback_eq_coeff p P P_X hvX hxX hGX,
      coeff_isRCartierPullback_eq_coeff q P P_Y hvY hxY hGY, hPY,
      ← transformDivisor_logCanonicalDivisor e he K D, sub_nonneg]
    exact (transformDivisor_apply_equiv e he (logCanonicalDivisor K (QDivisor.toRDivisor D)) P_X).le
  have hB := isEffective_neg_of_isRelativelyNef hZ hWp (p ≫ φ) (Category.assoc _ _ _) hhb
    (isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY)
      (isCartierCombination_of_isRCartierPullback hGX)) hMnef hBG P₀
  rw [neg_sub, DivisorWithCoeffs.coeff_sub, hGXdef, hGYdef, coeff_sum_smul_toRDivisor,
    coeff_sum_smul_toRDivisor] at hB
  linarith

/-- A morphism restricting to an isomorphism `U ≅ V` preserves the coheight of points of `U`. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.coheight_apply_eq_of_isIso_resLE {X Y : Scheme.{u}}
    (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens} (hUV : U ≤ f ⁻¹ᵁ V) [IsIso (f.resLE V U hUV)]
    {x : X} (hx : x ∈ U) :
    Order.coheight (f x) = Order.coheight x := by
  let x' : U.toScheme := ⟨x, hx⟩
  have e1 : Order.coheight (U.ι x') = Order.coheight x' :=
    Topology.IsOpenEmbedding.coheight_eq _ U.ι.isOpenEmbedding
  have e2 : Order.coheight ((f.resLE V U hUV) x') = Order.coheight x' :=
    Topology.IsOpenEmbedding.coheight_eq _ (f.resLE V U hUV).isOpenEmbedding
  have e3 : Order.coheight (V.ι ((f.resLE V U hUV) x')) =
      Order.coheight ((f.resLE V U hUV) x') :=
    Topology.IsOpenEmbedding.coheight_eq _ V.ι.isOpenEmbedding
  have e4 : V.ι ((f.resLE V U hUV) x') = f x := by
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.resLE_comp_ι]
    rfl
  rw [← e4, e3, e2, ← e1]
  rfl

/-- **Flips preserve canonical divisors.** For small birational contractions `φ`, `φ⁺` and
`g : X ⤏ X⁺` transforming the prime divisors of `X` bijectively, `g_*K` is a canonical divisor of
`X⁺` whenever `K` is one of `X`. -/
private theorem isCanonicalDivisor_transformDivisor {X Z X' : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X'] [IsIntegral Z]
    {φ : X ⟶ Z} {φp : X' ⟶ Z} [LocallyOfFiniteType (φ ≫ sZ)] [LocallyOfFiniteType (φp ≫ sZ)]
    [IsDominant φ] [IsDominant φp]
    (hs : IsSmall k sZ (φ ≫ sZ) φ) (hs' : IsSmall k sZ (φp ≫ sZ) φp)
    (hX : IsNormalVariety k (φ ≫ sZ)) (hX' : IsNormalVariety k (φp ≫ sZ))
    {g : X.RationalMap X'} (e : Mori.PrimeDivisor X ≃ Mori.PrimeDivisor X')
    (he : ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P))
    (hev : ∀ P, (e P).divisorialValuation.comap (functionFieldMap φp) =
      P.divisorialValuation.comap (functionFieldMap φ))
    {n : ℕ} {K : Divisor X} (hK : K.IsCanonicalDivisor (φ ≫ sZ) n) :
    Divisor.IsCanonicalDivisor (φp ≫ sZ) n (Mori.RationalMap.transformDivisor g K) := by
  classical
  have hφb := hs.isBirationalMorphism
  have hφpb := hs'.isBirationalMorphism
  haveI : AlgebraicGeometry.IsVariety k sZ := hs.isVariety_target
  haveI : AlgebraicGeometry.IsVariety k (φ ≫ sZ) := hX.1
  haveI : AlgebraicGeometry.IsVariety k (φp ≫ sZ) := hX'.1
  have hn : topologicalKrullDim X' = n := by
    rw [← (MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (φp ≫ sZ) hφpb),
      MMP.Intersection.topologicalKrullDim_eq_of_isBirationalMorphism sZ (φ ≫ sZ) hφb]
    exact hK.1
  refine ⟨hn, ?_⟩
  set K' := Mori.RationalMap.transformDivisor g K with hK'def
  by_cases hne : Nonempty (smoothLocus (φp ≫ sZ) : X'.Opens)
  · have hsmooth : Smooth ((smoothLocus (φp ≫ sZ)).ι ≫ φp ≫ sZ) := smooth_smoothLocus_ι _
    set S' := smoothLocus (φp ≫ sZ)
    obtain ⟨Dd, ⟨e1⟩⟩ := exists_divisorialSheaf_iso_relativeDifferentialForms hX' hn S' hsmooth
    -- the isomorphisms off codimension two
    obtain ⟨V, Wc, hV, hW, hVW, hρ⟩ := hs.exists_isIso
    obtain ⟨V', W', hV', hW', hVW', hρ'⟩ := hs'.exists_isIso
    let Vo : X.Opens := V.compl
    let Wo : Z.Opens := Wc.compl
    let V'o : X'.Opens := V'.compl
    let W'o : Z.Opens := W'.compl
    let U' : X'.Opens := V'o ⊓ φp ⁻¹ᵁ Wo
    have hUV' : U' ≤ V'.compl := inf_le_left
    have hgU : U'.ι ≫ φp =
        X'.homOfLE hUV' ≫ φp.resLE W'o V'o hVW' ≫ W'o.ι := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    haveI : IsOpenImmersion (U'.ι ≫ φp) := by rw [hgU]; infer_instance
    have hrange : Set.range (U'.ι ≫ φp) ⊆ Set.range Wo.ι := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact x.2.2
    let l : U'.toScheme ⟶ Wo.toScheme := IsOpenImmersion.lift Wo.ι (U'.ι ≫ φp) hrange
    have hl : l ≫ Wo.ι = U'.ι ≫ φp := IsOpenImmersion.lift_fac _ _ _
    haveI : IsOpenImmersion l := by
      have : IsOpenImmersion (l ≫ Wo.ι) := by rw [hl]; infer_instance
      exact IsOpenImmersion.of_comp l Wo.ι
    let j₀ : U'.toScheme ⟶ X := l ≫ inv (φ.resLE Wo Vo hVW) ≫ Vo.ι
    have hj₀ : j₀ ≫ φ = U'.ι ≫ φp := by
      simp only [j₀, Category.assoc]
      rw [← Scheme.Hom.resLE_comp_ι φ hVW, IsIso.inv_hom_id_assoc, hl]
    let A : X'.Opens := S' ⊓ U'
    have hAS : A ≤ S' := inf_le_left
    have hAU : A ≤ U' := inf_le_right
    -- every prime divisor of `S'` has its generic point in `A`
    have hcoV' := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hV'
    have hcoW := MMP.Flips.le_closedsCodimension_iff_le_coheight.mp hW
    have hmemU : ∀ x : X', Order.coheight x ≤ 1 → x ∈ U' := by
      intro x hx
      have hxV : x ∈ V'o := fun h => absurd ((hcoV' x h).trans hx) (by decide)
      refine ⟨hxV, fun h => ?_⟩
      have h1 := φp.coheight_apply_eq_of_isIso_resLE hVW' hxV
      exact absurd ((hcoW (φp x) h).trans (h1 ▸ hx)) (by decide)
    have hηA : genericPoint X' ∈ A := by
      obtain ⟨x⟩ := hne
      refine ⟨((genericPoint_spec X').mem_open_set_iff S'.isOpen).mpr ⟨x.1, trivial, x.2⟩,
        hmemU _ ?_⟩
      exact (Order.coheight_eq_zero.mpr fun b _ => _root_.genericPoint_specializes b).le.trans
        zero_le_one
    haveI : Nonempty A := ⟨⟨genericPoint X', hηA⟩⟩
    let h : A.toScheme ⟶ S'.toScheme := X'.homOfLE hAS
    have hh : h ≫ S'.ι = A.ι := Scheme.homOfLE_ι _ _
    let jA : A.toScheme ⟶ X := X'.homOfLE hAU ≫ j₀
    haveI : IsOpenImmersion jA := inferInstance
    have : IsDominant jA := isDominant_of_isOpenImmersion' jA
    have : IsDominant h := isDominant_of_isOpenImmersion' h
    haveI : IsDominant (h ≫ S'.ι) := isDominant_of_isOpenImmersion' _
    have hjA : jA ≫ φ = (h ≫ S'.ι) ≫ φp := by
      simp only [jA, Category.assoc, hj₀]
      rw [← Category.assoc, Scheme.homOfLE_ι, ← hh, Category.assoc]
    have hs2 : Smooth (h ≫ S'.ι ≫ φp ≫ sZ) := by
      have : Smooth (S'.ι ≫ φp ≫ sZ) := hsmooth
      infer_instance
    obtain ⟨eK⟩ := nonempty_restrictDivisorAlong_iso_relativeDifferentialForms hK jA
      (p' := h ≫ S'.ι ≫ φp ≫ sZ)
      (by rw [← Category.assoc, hjA, Category.assoc, Category.assoc]) hs2
    have hdiv : restrictDivisorAlong (h ≫ S'.ι) K' = restrictDivisorAlong jA K := by
      refine Finsupp.ext fun W₀ => ?_
      change K'.coeff _ = K.coeff _
      set P' := OpenWeilRestriction.primeDivisorMap (h ≫ S'.ι) W₀
      set P := OpenWeilRestriction.primeDivisorMap jA W₀
      have hPe : P' = e P := by
        refine primeDivisor_eq_of_divisorialValuation_eq hX'
          (valuation_eq_of_comap_eq hφpb ?_)
        rw [hev P, divisorialValuation_primeDivisorMap, divisorialValuation_primeDivisorMap]
        change (W₀.valuationOver (h ≫ S'.ι)).comap _ = (W₀.valuationOver jA).comap _
        rw [comap_valuationOver, comap_valuationOver]
        exact valuationOver_congr W₀ hjA.symm
      rw [hPe, hK'def]
      exact transformDivisor_apply_equiv e he K P
    have e2 : (restrictDivisorAlong (h ≫ S'.ι) K').divisorialSheaf ≅
        (Scheme.Hom.relativeDifferentialForms (S'.ι ≫ φp ≫ sZ) n).restrict h :=
      eqToIso (by rw [hdiv]) ≪≫ eK ≪≫
        (nonempty_restrict_relativeDifferentialForms_iso h (S'.ι ≫ φp ≫ sZ)
          (h ≫ S'.ι ≫ φp ≫ sZ) rfl n).some.symm
    have hbig : ∀ E : MMP.Mori.PrimeDivisor S'.toScheme, E.genericPoint ∈ Set.range h := by
      intro E
      have hgp : (OpenWeilRestriction.primeDivisorMap S'.ι E).genericPoint =
          S'.ι E.genericPoint := OpenWeilRestriction.genericPoint_primeDivisorMap _ _
      have hco : Order.coheight (S'.ι E.genericPoint) = 1 := by
        rw [← hgp]
        exact (OpenWeilRestriction.primeDivisorMap S'.ι E).coheight_genericPoint
      exact ⟨⟨S'.ι E.genericPoint, E.genericPoint.2, hmemU _ hco.le⟩,
        Subtype.ext (by simp [h, Scheme.homOfLE_apply]; rfl)⟩
    have : CompactSpace S' := compactSpace_opens' S'
    have : CompactSpace A := compactSpace_opens' A
    exact nonempty_restrict_iso_of_restrictDivisorAlong S' h hbig K' Dd _ e1 e2
  · have : IsEmpty (smoothLocus (φp ≫ sZ)).toScheme := not_nonempty_iff.mp hne
    exact nonempty_iso_of_isEmpty _ _

end Flip

/-- **Sets of small log discrepancy shrink under flips** (FA 4.12.4). Let `X` be a normal variety
with canonical divisor `K` of dimension `n`, `D` a `ℚ`-divisor with `K_X + D` `ℚ`-Cartier, and
`φ⁺ : X⁺ ⟶ Z` with `g : X ⤏ X⁺` a flip of the small contraction `φ : X ⟶ Z` with respect to
`K_X + D` (`MMP.Flips.IsFlip`). Then `g_*K` is a canonical divisor of `X⁺`, `g_*K + g_*D` is
`ℚ`-Cartier, and for every `t ∈ ℚ` each `ν⁺ ∈ 𝒮_t(X⁺, g_*D)` corresponds to a valuation `ν` of
`k(X)` (with `ν ∘ φ^* = ν⁺ ∘ φ⁺^*`), and every such `ν` lies in `𝒮_t(X, D)`. -/
@[mmp "lem_fa4_small_log_discrepancy_set_shrinks_under_flip"]
public theorem smallLogDiscrepancySet_subset_of_isFlip {k : Type u} [Field k] {X Z X' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sX' : X' ⟶ Spec (.of k)}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]
    [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X'] [CompactSpace X']
    [LocallyOfFiniteType sX'] [IsIntegral Z]
    {n : ℕ} {K : Divisor X} {D : QDivisor X} {φ : X ⟶ Z} {φp : X' ⟶ Z} [IsDominant φ]
    [IsDominant φp] {g : X.RationalMap X'}
    (hX : IsNormalVariety k sX) (hK : K.IsCanonicalDivisor sX n)
    (hD : (Divisor.toQDivisor K + D).IsQCartier)
    (hflip : IsFlip k sX sZ sX' (logCanonicalDivisor K (QDivisor.toRDivisor D)) φ φp g) :
    ∃ (hK' : Divisor.IsCanonicalDivisor sX' n (Mori.RationalMap.transformDivisor g K))
      (hD' : (Divisor.toQDivisor (Mori.RationalMap.transformDivisor g K) +
        Mori.RationalMap.transformDivisor g D).IsQCartier),
      ∀ (t : ℚ) (ν' : Valuation X'.functionField ℤᵐ⁰),
        ν' ∈ smallLogDiscrepancySet sX' n (Mori.RationalMap.transformDivisor g K)
          (Mori.RationalMap.transformDivisor g D) hflip.isNormalVariety_flip hK' hD' t →
        (∃ ν : Valuation X.functionField ℤᵐ⁰,
          ν.comap (functionFieldMap φ) = ν'.comap (functionFieldMap φp)) ∧
        ∀ ν : Valuation X.functionField ℤᵐ⁰,
          ν.comap (functionFieldMap φ) = ν'.comap (functionFieldMap φp) →
          ν ∈ smallLogDiscrepancySet sX n K D hX hK hD t := by
  have hcX : φ ≫ sZ = sX := hflip.isContraction.comp_eq
  have hcX' : φp ≫ sZ = sX' := hflip.isSmall.comp_eq
  subst hcX hcX'
  have hZ := hflip.isNormalVariety_target
  have hX' := hflip.isNormalVariety_flip
  have hs := hflip.isSmall_source
  have hs' := hflip.isSmall
  have hφ := hs.isBirationalMorphism
  have hφp := hs'.isBirationalMorphism
  haveI : IsProper φ := hs.isProper
  haveI : IsProper φp := hs'.isProper
  haveI := hX.1.toQuasiCompact
  haveI := hX'.1.toQuasiCompact
  have hee := (exceptional_hasNonemptyCenter_iff_of_isSmall (φ ≫ sZ) (φp ≫ sZ) sZ φ φp
    hs hs').2 g hflip.isModificationOf
  set e := primeDivisorEquivOfModification hs hs' hflip.isModificationOf
  have he : ∀ P, Mori.RationalMap.transformPrimeDivisor g P = some (e P) := fun P => (hee P).1
  have hev := fun P => (hee P).2
  have hEeq := transformDivisor_logCanonicalDivisor e he K D
  have hK' := isCanonicalDivisor_transformDivisor hs hs' hX hX' e he hev hK
  have hD' : (Divisor.toQDivisor (Mori.RationalMap.transformDivisor g K) +
      Mori.RationalMap.transformDivisor g D).IsQCartier := by
    refine QDivisor.isQCartier_of_isCartierCombination ?_
    rw [map_add, QDivisor.toRDivisor_toQDivisor, ← hEeq]
    exact hflip.isCartierCombination_transform
  refine ⟨hK', hD', fun t ν' hν' => ⟨?_, fun ν hν => ?_⟩⟩
  · let eφ := RingEquiv.ofBijective (functionFieldMap φ) hφ.functionFieldMap_bijective
    refine ⟨ν'.comap ((functionFieldMap φp).comp eφ.symm.toRingHom), ?_⟩
    ext z
    simp only [Valuation.comap_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom]
    exact congrArg _ (congrArg _ (eφ.symm_apply_apply z))
  obtain ⟨hcen', ⟨E', hE'exc, hE'v⟩, b', hb', hb't⟩ := hν'
  obtain ⟨hcen, Ex, hExv, hExexc⟩ := ((exceptional_hasNonemptyCenter_iff_of_isSmall (φ ≫ sZ)
    (φp ≫ sZ) sZ φ φp hs hs').1 ν ν' hν).mpr ⟨hcen', E', hE'v, hE'exc⟩
  obtain ⟨a', ha', rfl⟩ := hb'
  have hAX : IsRelativelyNef k (φ ≫ sZ) φ (-(Divisor.toRDivisor K + QDivisor.toRDivisor D)) :=
    isRelativelyNef_of_isRelativelyAmple hflip.isRelativelyAntiAmple
  have hAY : IsRelativelyNef k (φp ≫ sZ) φp
      (Divisor.toRDivisor (Mori.RationalMap.transformDivisor g K) +
        QDivisor.toRDivisor (Mori.RationalMap.transformDivisor g D)) :=
    isRelativelyNef_of_isRelativelyAmple (hEeq ▸ hflip.isRelativelyAmple_transform)
  obtain ⟨a, ha, hle⟩ := exists_isDiscrepancy_le hZ hX hX' hφ hφp e he hev hK hD hAX hAY hcen hν
    ha'
  exact ⟨hcen, ⟨Ex, hExexc, hExv⟩, 1 + a, ⟨a, ha, rfl⟩, by linarith⟩

end MMP.Flips

end