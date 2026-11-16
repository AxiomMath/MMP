module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.Basic
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyDefs
public import MMP.AlgebraicGeometry.Intersection.RCartierCurveDegree
public import MMP.AlgebraicGeometry.MMP.MinimalModel.LogCanonicalModelDefs
public import MMP.AlgebraicGeometry.MMP.Steps
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.IndependentOfResolution
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.ValuativeLineBundle
import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization
import MMP.AlgebraicGeometry.Singularities.DiscrepancyCommonModel
import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Divisor.Negativity.NegativityLemma
import MMP.AlgebraicGeometry.Singularities.MultiplierIdeal.EffectiveIdealSheaf
import MMP.AlgebraicGeometry.Divisor.Negativity.FibreSupport
import MMP.Combinatorics.WeightedGraph.ChainDeterminant
import MMP.AlgebraicGeometry.MMP.Flip.FiniteGeneration
import MMP.AlgebraicGeometry.Singularities.DivisorOverRealization
import MMP.AlgebraicGeometry.Intersection.CurveProjectionFormula
import MMP.AlgebraicGeometry.MMP.Fourfold.GoodModelFixedParts
import MMP.AlgebraicGeometry.Divisor.BirationalPushforward
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Divisor.Canonical.DivisorOfForm
import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
import MMP.AlgebraicGeometry.Morphisms.SteinFactorization
import MMP.AlgebraicGeometry.Resolution.Surface.ExceptionalLocus
import MMP.AlgebraicGeometry.Divisor.EffectiveRCartierPositivity
import MMP.AlgebraicGeometry.Intersection.OneCyclePushforward
import MMP.AlgebraicGeometry.Intersection.QCartierCurveProjection
import MMP.AlgebraicGeometry.Morphisms.Birational.FiniteFibreLocus
import MMP.AlgebraicGeometry.MMP.Threefold.CurveNegativity
import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization

/-!
# Discrepancies: trivial multiplier ideals and comparisons along models

Three statements read a geometric property off discrepancies.

**Trivial multiplier ideals.** Let `X` be a non-singular variety over a field `k` of
characteristic zero, `D` an effective `ℝ`-divisor on `X` and `μ : X' ⟶ X` a log resolution of
`D`. Then the multiplier ideal `𝒥(X, D)` is `𝒪_X` if and only if every prime divisor `E` of `X'`
has `ord_E(K_{X'/X} - μ^*D) > -1`. With `G = K_{X'/X} - ⌊μ^*D⌋`, so that
`𝒥(X, D) = μ_*𝒪_{X'}(G)`, the condition says exactly that `G` is effective, since for an integer
`b` and a real `r`, `b - ⌊r⌋ ≥ 0` if and only if `b - r > -1`. If `G` is effective,
`𝒪_X ⊆ μ_*𝒪_{X'}(G) = 𝒥(X, D) ⊆ 𝒪_X`; if `ord_E G < 0`, the constant `1` is not a global section
of `μ_*𝒪_{X'}(G)`.

**Comparison over a common base.** Let `f : X ⟶ Z`, `g : Y ⟶ Z` be proper birational morphisms
of normal varieties, `D` an `ℝ`-divisor on `Z` and `E_X`, `E_Y` `ℝ`-divisors on `X`, `Y`
supported on the prime divisors exceptional over `Z`. Put `B_X = f⁻¹_*D + E_X`,
`B_Y = g⁻¹_*D + E_Y`. If `-(K_X + B_X)` is `f`-nef and `K_Y + B_Y` is `g`-nef, then
`a(B, X, B_X) ≤ a(B, Y, B_Y)` for every divisor `B` of `k(Z)` with nonempty center on `Z`.
On a common normal model `p : W ⟶ X`, `q : W ⟶ Y` on which `B = ord_{P₀}` for a prime divisor
`P₀` of `W`, the `ℝ`-divisor
`M = q^*(K_Y + B_Y) - p^*(K_X + B_X) - (div_W(q^*ω_Y) - div_W(p^*ω_X))` has coefficient
`a(P, X, B_X) - a(P, Y, B_Y)` along every prime divisor `P` of `W`. It is nef over `Z` by the
projection formula, the correction term being principal, and its coefficients along the prime
divisors not exceptional over `Z` vanish, since there both discrepancies are `-coeff_Q(D)` for
`Q` the image of `P` in `Z`. The negativity lemma makes `-M` effective, and its coefficient along
`P₀` is `a(B, Y, B_Y) - a(B, X, B_X)`.

**Weak log canonical models.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log canonical model of
`f : (X, D_X) ⟶ Z` through `φ : X ⤏ Y`, and `B` a divisor of `k(X) = k(Y)` with nonempty center
on `X`. Then `B` has nonempty center on `Y` and `a(B, D_{𝓕,Y}) ≥ a(B, D_X)`. The divisor `B` is
a prime divisor `E` of a model `h : W' ⟶ W` of a common model `(W, p, q)` of `φ`, and
`(W', h ≫ p, h ≫ q)` is again a common model. On a common model the `ℝ`-divisor
`Δ = p^*(K_X + D_X) - q^*(K_Y + D_{𝓕,Y}) + (div_W(q^*ω_Y) - div_W(p^*ω_X))` has coefficient
`a(P, D_{𝓕,Y}) - a(P, D_X)` along every prime divisor `P` of `W` (FA (2.23.4)); the divisor
`M = q^*(K_Y + D_{𝓕,Y}) - (div_W(q^*ω_Y) - div_W(p^*ω_X))` is `p`-nef because `p ≫ f = q ≫ g`;
the coefficients of `Δ` along the prime divisors not exceptional over `X` are nonnegative
(FA 2.23.1); and `p^*(K_X + D_X) = M + Δ`. The negativity lemma makes `Δ` effective.

## Main results

* `MMP.Intersection.IsMultiplierIdeal.eq_range_germToFunctionField_iff`: `𝒥(X, D) = 𝒪_X` if and
  only if `ord_E(K_{X'/X} - μ^*D) > -1` for every prime divisor `E` of a log resolution.
* `MMP.Flips.isDiscrepancy_le_of_isRelativelyNef`: the comparison of discrepancies over a common
  base (FA 2.28.2.1, Kollár–Mori 3.38).
* `MMP.Flips.IsWeakLogCanonicalModelOf.isDiscrepancy_le_of_not_isExceptional`: on a common model
  of a weak log canonical model, discrepancies along prime divisors not exceptional over `X` do
  not decrease (FA 2.23.1).
* `MMP.Flips.IsWeakLogCanonicalModelOf.isDiscrepancy_le`: discrepancies do not decrease on a
  weak log canonical model (FA 2.23.3).

## Implementation notes

* `𝒥(X, D)` is any `J` with `MMP.Intersection.IsMultiplierIdeal sX D J`; it is unique
  (`MMP.Intersection.existsUnique_isMultiplierIdeal`), and need not be computed on `μ`. It is
  recorded by its sections over the opens of `X` as subsets of `K(X)`, and `J = 𝒪_X` means that
  over every non-empty open `U` these are the images of the regular functions on `U` under
  `AlgebraicGeometry.Scheme.germToFunctionField` (over the empty open every multiplier ideal has
  the single section `0`). `K_{X'/X}` and `μ^*D` enter through their Weil divisors `wK` and `F`.
  Effectivity of `D` is effectivity of its Weil `ℝ`-divisor. Lazarsfeld states the result for
  `ℚ`-divisors over `ℂ`; the argument uses neither.
* A divisor `B` of a function field is a valuation of it. In
  `MMP.Flips.isDiscrepancy_le_of_isRelativelyNef` the divisor of `k(X)` (resp. `k(Y)`) is the
  valuation `v_X` (resp. `v_Y`) with `v = v_X ∘ f^*` (resp. `v = v_Y ∘ g^*`); in
  `MMP.Flips.IsWeakLogCanonicalModelOf.isDiscrepancy_le` the identification `k(X) = k(Y)` is
  given by a common model `(W, p, q)` of `φ` and a valuation `w` of `k(W)` with `v = w ∘ p^*`
  and `v' = w ∘ q^*`. As in `MMP.Flips.IsDiscrepancy`, "`a` is the discrepancy" is a predicate.
* The discrepancies are computed with forms `ω_X`, `ω_Y` with `div ω_X = K_X`, `div ω_Y = K_Y`,
  which need not satisfy `div_W(p^*ω_X) = div_W(q^*ω_Y)`. Their pull-backs to `W` are nonzero top
  forms, so `div_W(q^*ω_Y) - div_W(p^*ω_X)` is principal: it is Cartier and has degree zero on
  every proper curve, so it changes neither the nefness of `M` nor its coefficients along
  divisors not exceptional over the base. This replaces the compatibility of the canonical
  divisors in the common-model identity `MMP.Flips.pullback_sub_pullback_eq_sum_discrepancy`.
  The source works over `ℂ`; the comparisons are stated over a perfect field, resp. a field of
  characteristic zero.

## References

* [R. Lazarsfeld, *Positivity in Algebraic Geometry II*][lazarsfeld2004], §9.3.B, after
  Def. 9.3.9.
* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.23.3,
  2.28.1–2.28.2.1
* [V. V. Shokurov, *3-fold log flips*][Shokurov91], 1.5.5–1.5.6
* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Lemma 3.38
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped WithZero

namespace MMP.Flips.DiscrepancyComparison

open MMP MMP.Flips MMP.Mori MMP.Threefold.Mori.Helpers

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
  letI : IsLocalization (⊥ : Submonoid A) A' :=
    IsLocalization.of_le_isUnit_of_bijective
      (by rw [Algebra.algebraMapSubmonoid, Submonoid.map_bot]; exact bot_le) hA
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
`K ≅ K'`, the order of the pull-back of an `m`-canonical form along `A'` is its order along `A`.
Unlike `MMP.Threefold.Mori.Helpers.ordAt_pullbackForms_eq`, no generator of `Ω^d_{A/k}` is
assumed. -/
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

end Transport

section Order

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- For a divisor `(Y, f, E)` over `X` with `ord_E = ord_P`, `ord_E(f^*y) = ord_P(y)`. -/
private theorem ord_functionFieldMap_eq_of_valuation_eq (D : DivisorOver k sX)
    (P : Mori.PrimeDivisor X) (hv : D.valuation = P.divisorialValuation) (y : X.functionField) :
    haveI := D.isIntegral
    haveI := D.isLocallyNoetherian
    haveI := D.isNormal
    haveI := D.isDominant
    D.Y.ord (functionFieldMap D.f y) D.E.genericPoint = X.ord y P.genericPoint := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  by_cases hy : y = 0
  · subst hy
    simp [Scheme.ord_zero]
  · have hey : functionFieldMap D.f y ≠ 0 := (map_ne_zero _).mpr hy
    have h1 : D.E.divisorialValuation (functionFieldMap D.f y) = P.divisorialValuation y :=
      congrArg (fun w => w y) hv
    rw [D.E.divisorialValuation_eq_exp_neg_ord hey, P.divisorialValuation_eq_exp_neg_ord hy,
      WithZero.exp_inj] at h1
    omega

/-- A divisor over a normal variety `X` with valuation `ord_P` has center `P`: `f(η_E) = η_P`. -/
private theorem map_genericPoint_eq_of_valuation_eq (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) (P : Mori.PrimeDivisor X) (hv : D.valuation = P.divisorialValuation) :
    D.f D.E.genericPoint = P.genericPoint := by
  have hv' : D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation := by
    rw [hv]
    refine Valuation.ext fun y => ?_
    change _ = P.divisorialValuation (functionFieldMap (𝟙 X) y)
    rw [functionFieldMap_id_apply]
  exact MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv'

/-- **The order of a form along a divisor depends only on its valuation.** Let `(Y, f, E)` be a
divisor over `X` with `ord_E = ord_P` for a prime divisor `P` of `X`. Then
`ord_E(f^*τ) = ord_P(τ)` for every rational `m`-canonical form `τ`, over any field. -/
private theorem ordPullback_eq_ordForm_of_valuation_eq (D : DivisorOver k sX)
    (P : Mori.PrimeDivisor X) (hv : D.valuation = P.divisorialValuation) {d : ℕ} {m : ℤ}
    (τ : RationalPluriForms sX d m) : D.ordPullback τ = P.ordForm τ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (D.f ≫ sX)
  let := functionFieldMapAlgebra D.f
  have hT := isScalarTower_functionFieldMap sX D.f
  have hb : Function.Bijective (functionFieldMap D.f) :=
    D.isBirationalMorphism.functionFieldMap_bijective
  have hval : ∀ y : X.functionField,
      D.E.divisorialValuation (functionFieldMap D.f y) = P.divisorialValuation y :=
    fun y => congrArg (fun w => w y) hv
  have hord := ord_functionFieldMap_eq_of_valuation_eq D P hv
  have h12 : ∀ a1 : P.localRing, ∃ a2 : D.E.localRing,
      algebraMap D.E.localRing D.Y.functionField a2 =
        functionFieldMap D.f (algebraMap P.localRing X.functionField a1) := by
    intro a1
    have : P.divisorialValuation (algebraMap P.localRing X.functionField a1) ≤ 1 :=
      (P.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    exact (D.E.divisorialValuation_le_one_iff _).mp this
  have h21 : ∀ a2 : D.E.localRing, ∃ a1 : P.localRing,
      functionFieldMap D.f (algebraMap P.localRing X.functionField a1) =
        algebraMap D.E.localRing D.Y.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := hb.2 (algebraMap D.E.localRing D.Y.functionField a2)
    have : P.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (D.E.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (P.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩
  obtain ⟨ψ, hψb, hψ⟩ :=
    MMP.Threefold.Mori.ModelIndependence.exists_ringHom_bijective_of_range _ h12 h21
  letI := stalkAlgebra sX P.genericPoint
  letI := stalkAlgebra (D.f ≫ sX) D.E.genericPoint
  haveI := isScalarTower_stalk_functionField sX P.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sX) D.E.genericPoint
  letI : Algebra P.localRing D.E.localRing := ψ.toAlgebra
  letI : Algebra P.localRing D.Y.functionField :=
    ((algebraMap D.E.localRing D.Y.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k P.localRing D.E.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective D.E.localRing D.Y.functionField
    change _ = algebraMap D.E.localRing D.Y.functionField (ψ (algebraMap k P.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k P.localRing X.functionField c,
      ← IsScalarTower.algebraMap_apply k D.E.localRing D.Y.functionField c]
    exact IsScalarTower.algebraMap_apply k X.functionField D.Y.functionField c
  have hS2 : IsScalarTower P.localRing D.E.localRing D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower P.localRing X.functionField D.Y.functionField :=
    IsScalarTower.of_algebraMap_eq hψ
  have hS4 : IsScalarTower k P.localRing D.Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap D.E.localRing D.Y.functionField (ψ (algebraMap k P.localRing c))
    rw [IsScalarTower.algebraMap_apply k D.E.localRing D.Y.functionField c,
      IsScalarTower.algebraMap_apply k P.localRing D.E.localRing c]
    rfl
  exact ordAt_pullbackForms_eq_of_bijective (k := k) (K := X.functionField)
    (K' := D.Y.functionField) (A := P.localRing) (A' := D.E.localRing)
    (v := fun y => X.ord y P.genericPoint) (v' := fun y => D.Y.ord y D.E.genericPoint) hψb hb
    (fun x y hx hy => P.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => P.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => D.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D.E.ord_algebraMap_of_isUnit ha) hord τ

end Order

section Discrepancy

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX]

/-- **FA 2.5.4 over any field.** For a prime divisor `P` of a normal variety `X`, every value
of the discrepancy `a(ord_P, D_X)` is `-coeff_P(D_X)`. -/
private theorem eq_neg_coeff_of_isDiscrepancy {n : ℕ} {K : Divisor X} {D_X : RDivisor X}
    {P : Mori.PrimeDivisor X} {a : ℝ} (h : IsDiscrepancy sX n K D_X P.divisorialValuation a) :
    a = -D_X.coeff P := by
  obtain ⟨-, -, -, E, ω, m, r, L, hEv, -, hX, -, -, hLc, hsum, L', hpb, rfl⟩ := h
  have := E.isIntegral
  have := E.isLocallyNoetherian
  have := E.isNormal
  have := E.isDominant
  have hord : (E.toDivisorOver.ordPullback ω : ℝ) = P.ordForm ω := by
    exact_mod_cast ordPullback_eq_ordForm_of_valuation_eq E.toDivisorOver P hEv ω
  have hη := map_genericPoint_eq_of_valuation_eq hX E.toDivisorOver P hEv
  have hco : ∀ j, ((L' j).coeff E.E : ℝ) = (L j).coeff P := by
    intro j
    obtain ⟨hB, hL'⟩ := hpb j
    obtain ⟨U, hU, φ, hφ⟩ := hLc j P.genericPoint
    have hEU : E.f E.E.genericPoint ∈ U := by
      change E.toDivisorOver.f E.toDivisorOver.E.genericPoint ∈ U
      rwa [hη]
    have h1 := MMP.Threefold.Bridges.coeff_isPullback_eq_ord_evalFF hL' hφ E.E hEU
      (MMP.Mori.pointComponent P.genericPoint)
    have hPU : (P.support ∩ U).Nonempty := (P.genericPoint_mem_iff U).mp hU
    have h2 := hφ P hPU
    rw [MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord] at h2
    have hZ : P.component = MMP.Mori.pointComponent P.genericPoint := Subsingleton.elim
      (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents (X := X)) _ _
    rw [hZ] at h2
    rw [h1, ord_functionFieldMap_eq_of_valuation_eq E.toDivisorOver P hEv] at *
    exact_mod_cast h2.symm
  have hP := congrArg (fun D : RDivisor X => D.coeff P) hsum
  simp only [DivisorWithCoeffs.coeff_add, Divisor.coeff_toRDivisor, coeff_divisorOfForm,
    coeff_sum_smul_toRDivisor] at hP
  simp_rw [hco, hord]
  linarith

end Discrepancy

section CommonModel

/-- The generic point of an irreducible scheme lies in every dense open. -/
private theorem genericPoint_mem_of_dense {X : Scheme.{u}} [IrreducibleSpace X] {U : X.Opens}
    (hU : Dense (U : Set X)) : genericPoint X ∈ U := by
  haveI : Nonempty X := IrreducibleSpace.toNonempty
  exact (_root_.genericPoint_specializes _).mem_open U.2 hU.nonempty.choose_spec

/-- The point `Spec k(X) ⟶ Y` of a partial map defined at the generic point. -/
private theorem partialMap_fromFunctionField_eq {X Y : Scheme.{u}} [IrreducibleSpace X]
    (g : X.PartialMap Y) (hx : genericPoint X ∈ g.domain) :
    g.fromFunctionField = g.domain.fromSpecStalkOfMem (genericPoint X) hx ≫ g.hom := rfl

/-- Two morphisms from an open `U ∋ η_W` of an integral scheme to a separated scheme agree if
they agree on `Spec k(W)`. -/
private theorem hom_eq_of_fromSpecStalkOfMem_eq {W Y : Scheme.{u}} [IsIntegral W]
    [IsSeparated (Y ↘ ⊤_ Scheme)] (U : W.Opens) (hU : genericPoint W ∈ U)
    {f g : U.toScheme ⟶ Y}
    (H : U.fromSpecStalkOfMem (genericPoint W) hU ≫ f =
      U.fromSpecStalkOfMem (genericPoint W) hU ≫ g) : f = g := by
  have hd : Dense (U : Set W) := U.isOpen.dense ⟨_, hU⟩
  let P₁ : W.PartialMap Y := ⟨U, hd, f⟩
  let P₂ : W.PartialMap Y := ⟨U, hd, g⟩
  have heqv : P₁.equiv P₂ := Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq P₁ P₂ hU hU H
  have := (Scheme.PartialMap.equiv_iff_of_isSeparated_of_le (S := ⊤_ Scheme) (f := P₁) (g := P₂)
    hd le_rfl le_rfl).mp heqv
  rwa [Scheme.PartialMap.restrict_id_hom, Scheme.PartialMap.restrict_id_hom] at this

/-- **A morphism agreeing with a rational map at the generic point agrees with each of its
representatives.** Let `a : W ⟶ X` be dominant, `b : W ⟶ Y`, and `χ : X ⤏ Y` with
`χ ∘ a = b` at the generic point of `W`. Then for every representative `g` of `χ`,
`b = g ∘ a` on `a⁻¹(dom g)`. -/
private theorem comp_eq_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] (a : W ⟶ X) [IsDominant a] (b : W ⟶ Y)
    (χ : X.RationalMap Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫ χ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ b)
    (g : X.PartialMap Y) (hg : g.toRationalMap = χ) :
    (a ⁻¹ᵁ g.domain).ι ≫ b = (a ∣_ g.domain) ≫ g.hom := by
  have hx : genericPoint X ∈ g.domain := genericPoint_mem_of_dense g.dense_domain
  have hA : genericPoint W ∈ a ⁻¹ᵁ g.domain := by
    change a (genericPoint W) ∈ g.domain
    rwa [map_genericPoint_of_isDominant]
  refine hom_eq_of_fromSpecStalkOfMem_eq _ hA ?_
  have c1 : Spec.map (CommRingCat.ofHom (functionFieldMap a)) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) hx =
      (a ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint W) hA ≫ (a ∣_ g.domain) := by
    rw [← cancel_mono g.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
    exact functionFieldMap_fromSpecStalk a
  rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, ← Category.assoc, ← c1,
    Category.assoc, ← partialMap_fromFunctionField_eq g hx,
    ← Scheme.RationalMap.fromFunctionField_toRationalMap, hg]
  exact H.symm

/-- A ring isomorphism `θ : k(Y) → k(X)` inducing `m : Spec k(X) ⟶ Y`, read off a pair
`p : A ⟶ X`, `q : A ⟶ Y` inducing isomorphisms of function fields along which `m` is `q`; it
satisfies `p^* ∘ θ = q^*`. -/
private theorem exists_ringHom_of_specMap {X Y A : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral A] (m : Spec X.functionField ⟶ Y) (p : A ⟶ X) (q : A ⟶ Y) [IsDominant p]
    [IsDominant q] (hp : Function.Bijective (functionFieldMap p))
    (hA : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ m =
      A.fromSpecStalk (genericPoint A) ≫ q) :
    ∃ θ : Y.functionField →+* X.functionField, (functionFieldMap p).comp θ = functionFieldMap q ∧
      Spec.map (CommRingCat.ofHom θ) ≫ Y.fromSpecStalk (genericPoint Y) = m := by
  let ep := RingEquiv.ofBijective (functionFieldMap p) hp
  let θ : Y.functionField →+* X.functionField := ep.symm.toRingHom.comp (functionFieldMap q)
  have hθ' : (functionFieldMap p).comp θ = functionFieldMap q :=
    RingHom.ext fun s => ep.apply_symm_apply _
  have : IsIso (CommRingCat.ofHom (functionFieldMap p)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hp
  refine ⟨θ, hθ', ?_⟩
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom (functionFieldMap p))), hA, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hθ']
  exact functionFieldMap_fromSpecStalk q

/-- If `θ` induces `φ` at the generic points and `ψ` is inverse to `φ`, then
`Spec k(X) ⟶ Spec k(Y) ⟶ X` along `θ` and `ψ` is the canonical map. -/
private theorem specMap_comp_fromFunctionField_of_isInverse {X M : Scheme.{u}} [IsIntegral X]
    [IsIntegral M] {φ : X.RationalMap M} {ψ : M.RationalMap X}
    (hinv : Mori.RationalMap.IsInverse φ ψ) (θ : M.functionField →+* X.functionField)
    (hθ : Spec.map (CommRingCat.ofHom θ) ≫ M.fromSpecStalk (genericPoint M) =
      φ.fromFunctionField) :
    Spec.map (CommRingCat.ofHom θ) ≫ ψ.fromFunctionField = X.fromSpecStalk (genericPoint X) := by
  obtain ⟨e, he1, he2⟩ := hinv
  have hx : genericPoint X ∈ e.source := genericPoint_mem_of_dense e.dense_source
  have hy : genericPoint M ∈ e.target := genericPoint_mem_of_dense e.dense_target
  have hφ : φ.fromFunctionField = e.source.fromSpecStalkOfMem (genericPoint X) hx ≫
      e.iso.hom ≫ e.target.ι := by
    rw [← he1, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hx]
    rfl
  have hψ : ψ.fromFunctionField = e.target.fromSpecStalkOfMem (genericPoint M) hy ≫
      e.iso.inv ≫ e.source.ι := by
    rw [← he2, Scheme.RationalMap.fromFunctionField_toRationalMap,
      partialMap_fromFunctionField_eq _ hy]
    rfl
  have c1 : Spec.map (CommRingCat.ofHom θ) ≫ e.target.fromSpecStalkOfMem (genericPoint M) hy =
      e.source.fromSpecStalkOfMem (genericPoint X) hx ≫ e.iso.hom := by
    rw [← cancel_mono e.target.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hθ, hφ,
      Category.assoc]
  rw [hψ, ← Category.assoc, c1, Category.assoc, Iso.hom_inv_id_assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- The composite `p⁻¹(dom φ₀) ⟶ dom φ₀ ⟶ Y` is, at the generic point, `Spec k(W) ⟶ Spec k(X)`
followed by `φ₀`. -/
private theorem fromFunctionField_resLE_comp {W X Y : Scheme.{u}} [IsIntegral W] [IsIntegral X]
    (p : W ⟶ X) [IsDominant p] (φ₀ : X.PartialMap Y)
    (hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W)) :
    (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
      (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).fromFunctionField =
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ₀.fromFunctionField := by
  have hx : genericPoint X ∈ φ₀.domain := genericPoint_mem_of_dense φ₀.dense_domain
  have hW : genericPoint W ∈ p ⁻¹ᵁ φ₀.domain := genericPoint_mem_of_dense hd
  rw [partialMap_fromFunctionField_eq _ hW, partialMap_fromFunctionField_eq _ hx]
  change (p ⁻¹ᵁ φ₀.domain).fromSpecStalkOfMem (genericPoint W) hW ≫
    p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom = _
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  rw [← cancel_mono φ₀.domain.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
    Scheme.Opens.fromSpecStalkOfMem_ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  exact (functionFieldMap_fromSpecStalk p).symm

/-- **A common model, at the generic point.** If `q = φ ∘ p` as maps for a dominant `p`, then
`Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`. -/
private theorem specMap_fromFunctionField_eq_of_comp_eq {W X Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap) :
    Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q := by
  obtain ⟨φ₀, rfl, hd, heq⟩ := H
  have h1 := congrArg Scheme.RationalMap.fromFunctionField heq
  rwa [Scheme.RationalMap.fromFunctionField_toRationalMap, fromFunctionField_resLE_comp,
    MMP.Flips.RationalMap.fromFunctionField_hom] at h1

/-- Along a prime divisor `E` with `f(η_E) = η_P` at which `f` induces an isomorphism of local
rings, `ord_E ∘ f^* = ord_P`. -/
private theorem divisorialValuation_comap_functionFieldMap_eq {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] (f : Y ⟶ X) [IsDominant f] (E : Mori.PrimeDivisor Y)
    (P : Mori.PrimeDivisor X) (heq : f E.genericPoint = P.genericPoint)
    [IsIso (f.stalkMap E.genericPoint)] :
    E.divisorialValuation.comap (functionFieldMap f) = P.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [Valuation.comap_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E P heq t]

/-- For a representative `g` of `φ` defined at `η_P`, the closure of `φ(P)` is the closure of
`g(η_P)`. -/
private theorem coe_transform_eq_closure_singleton {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = φ) (P : Mori.PrimeDivisor X) (hP : P.genericPoint ∈ g'.domain) :
    (Mori.RationalMap.transform φ P.idealSheaf.support : Set Y) =
      closure {g'.hom ⟨P.genericPoint, hP⟩} := by
  have hZ : closure ((P.idealSheaf.support : Set X) ∩ g'.domain) = P.idealSheaf.support := by
    refine le_antisymm ?_ ?_
    · exact closure_minimal Set.inter_subset_left P.idealSheaf.support.isClosed
    · change P.support ⊆ _
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      refine closure_mono (Set.singleton_subset_iff.mpr ⟨?_, hP⟩)
      change P.genericPoint ∈ P.support
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
      exact subset_closure rfl
  rw [← MMP.Positivity.closure_image_eq_transform g' hg' _ hZ, TopologicalSpace.Closeds.coe_closure]
  refine le_antisymm (closure_minimal ?_ isClosed_closure) (closure_mono ?_)
  · rintro _ ⟨q, hq, rfl⟩
    have hq' : P.genericPoint ⤳ g'.domain.ι q := by
      have : g'.domain.ι q ∈ P.support := hq
      rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at this
      exact specializes_iff_mem_closure.mpr this
    have h1 := (g'.domain.ι.isOpenEmbedding.isInducing.specializes_iff (y := q)
      (x := ⟨P.genericPoint, hP⟩)).mp (by rwa [Scheme.Opens.ι_apply])
    exact specializes_iff_mem_closure.mp (h1.map g'.hom.continuous)
  · rw [Set.singleton_subset_iff]
    refine ⟨⟨P.genericPoint, hP⟩, ?_, rfl⟩
    change g'.domain.ι ⟨P.genericPoint, hP⟩ ∈ P.support
    rw [Scheme.Opens.ι_apply, AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact subset_closure rfl

/-- If `φ_*P = E` and `g` is a representative of `φ` defined at `η_P`, then `η_E = g(η_P)`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_eq_some {X Y : Scheme.{u}} [IsReduced X]
    [IsSeparated (Y ↘ ⊤_ Scheme)] {φ : X.RationalMap Y} {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : Mori.RationalMap.transformPrimeDivisor φ P = some E)
    (g' : X.PartialMap Y) (hg' : g'.toRationalMap = φ) (hP : P.genericPoint ∈ g'.domain) :
    E.genericPoint = g'.hom ⟨P.genericPoint, hP⟩ := by
  have h1 := Mori.RationalMap.support_transformPrimeDivisor h
  rw [coe_transform_eq_closure_singleton g' hg' P hP,
    AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h1
  exact (inseparable_iff_closure_eq.2 h1).eq

/-- A scheme separated over `Spec k` is separated over the terminal scheme. -/
private theorem isSeparated_toTerminal {k : Type u} [Field k] {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [IsSeparated s] : IsSeparated (X ↘ ⊤_ Scheme) := by
  rw [show (X ↘ ⊤_ Scheme) = s ≫ (Spec (.of k) ↘ ⊤_ Scheme) from Limits.terminal.hom_ext _ _]
  infer_instance

/-- **A common model maps points compatibly.** If `q = φ ∘ p` at the generic point of `W`, then
for every representative `g` of `φ` defined at `x = p(w)`, `q(w) = g(x)`. -/
private theorem apply_eq_hom_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsDominant p]
    {q : W ⟶ Y} {φ : X.RationalMap Y}
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    (g : X.PartialMap Y) (hg : g.toRationalMap = φ) {w : W} {x : X} (hx : x ∈ g.domain)
    (hp : p w = x) : q w = g.hom ⟨x, hx⟩ := by
  let w' : (p ⁻¹ᵁ g.domain).toScheme := ⟨w, show p w ∈ g.domain from hp ▸ hx⟩
  calc q w = ((p ⁻¹ᵁ g.domain).ι ≫ q) w' := rfl
    _ = g.hom ((p ∣_ g.domain) w') := by
      rw [comp_eq_of_specMap_fromFunctionField_eq p q φ H g hg]
      rfl
    _ = g.hom ⟨x, hx⟩ :=
      congrArg g.hom (Subtype.ext ((morphismRestrict_base_coe p g.domain w').trans hp))

/-- **Strict transforms on a common model.** If `q = φ ∘ p` at the generic point of `W` and
`φ_*Q = Q'`, then every point of `W` over `η_Q` lies over `η_{Q'}`. -/
private theorem apply_eq_genericPoint_of_transformPrimeDivisor_eq_some {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Y ↘ ⊤_ Scheme)] {p : W ⟶ X} [IsDominant p]
    {q : W ⟶ Y} {φ : X.RationalMap Y}
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q)
    {Q : Mori.PrimeDivisor X} {Q' : Mori.PrimeDivisor Y}
    (hT : Mori.RationalMap.transformPrimeDivisor φ Q = some Q') {w : W}
    (hp : p w = Q.genericPoint) : q w = Q'.genericPoint := by
  obtain ⟨g, hQg, hg⟩ := Mori.RationalMap.definedAt_iff.mp
    (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp hT).1
  exact (apply_eq_hom_of_specMap_fromFunctionField_eq H g hg hQg hp).trans
    (genericPoint_eq_of_transformPrimeDivisor_eq_some hT g hg hQg).symm

/-- The stalk of `Y` at the generic point of a prime divisor is a valuation ring. -/
private theorem valuationRing_stalk_of_eq_genericPoint {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (Q : Mori.PrimeDivisor Y) {y : Y}
    (h : y = Q.genericPoint) : ValuationRing (Y.presheaf.stalk y) := by
  have := Q.isDiscreteValuationRing_localRing
  subst h
  infer_instance

/-- A birational morphism mapping `w` to the generic point of a prime divisor is a local
isomorphism at `w`. -/
private theorem isIso_stalkMap_of_apply_eq_genericPoint {W Y : Scheme.{u}} [IsIntegral W]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (q : W ⟶ Y) [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) (Q : Mori.PrimeDivisor Y) {w : W}
    (h : q w = Q.genericPoint) : IsIso (q.stalkMap w) :=
  have := valuationRing_stalk_of_eq_genericPoint Q h
  MMP.Positivity.isIso_stalkMap_of_valuationRing q hq w

/-- A separated birational morphism has at most one point over the generic point of a prime
divisor. -/
private theorem eq_of_apply_eq_genericPoint {W Y : Scheme.{u}} [IsIntegral W] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] (q : W ⟶ Y) [IsSeparated q] [IsDominant q]
    (hq : Function.Bijective (functionFieldMap q)) (Q : Mori.PrimeDivisor Y) {w₁ w₂ : W}
    (h₁ : q w₁ = Q.genericPoint) (h₂ : q w₂ = Q.genericPoint) : w₁ = w₂ :=
  have := valuationRing_stalk_of_eq_genericPoint Q h₁
  have := isIso_stalkMap_of_apply_eq_genericPoint q hq Q h₁
  have := isIso_stalkMap_of_apply_eq_genericPoint q hq Q h₂
  MMP.Positivity.eq_of_isIso_stalkMap q hq (h₂.trans h₁.symm)

end CommonModel

end MMP.Flips.DiscrepancyComparison

namespace MMP.Flips

open DiscrepancyComparison in
/-- **FA 2.23.1.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log canonical model of
`f : (X, D_X) ⟶ Z` with respect to `𝓕` (`MMP.Flips.IsWeakLogCanonicalModelOf`, with
`G = D_{𝓕,Y}`), through the modification `φ : X ⤏ Y`, and let `(W, p, q)` be a common model of `φ`
(`MMP.Flips.IsCommonModel`). Let `P` be a prime divisor of `W` such that the divisor `(W, p, P)`
over `X` is not exceptional. Then `a(ord_P, D_{𝓕,Y}) ≥ a(ord_P, D_X)`, where `ord_P` is the
valuation of `(W, q, P)` over `Y`, resp. of `(W, p, P)` over `X`. -/
@[mmp "lem_fa2_weak_lc_model_zariski_decomposition_target"]
public theorem IsWeakLogCanonicalModelOf.isDiscrepancy_le_of_not_isExceptional {k : Type u}
    [Field k] {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] [QuasiCompact sY] {n : ℕ}
    {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    (P : Mori.PrimeDivisor W) :
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hW.comp_p ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_p, E := P, isProper := hW.isProper_p }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hW.comp_q ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_q, E := P, isProper := hW.isProper_q }
    ¬ EX.IsExceptional →
      ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
        IsDiscrepancy sX n K_X D_X EX.valuation a' → a' ≤ a := by
  open MMP.Mori MMP.Threefold.Mori.Helpers in
  (
    intro EX EY hEX a a' ha ha'
    obtain ⟨-, -, -, hFB, -, -, hexc⟩ := hM
    obtain ⟨hXn, hYn, hφb, -, -, -, Fs, hFs, -, -, hG⟩ := hFB
    have hWn : IsNormalVariety k sW := hW.isNormalVariety
    have : IsIntegral W := hWn.1.toIsIntegral
    have : IsNormal W := hWn.2
    have : LocallyOfFiniteType sW := hWn.1.toLocallyOfFiniteType
    have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
    have hpb := hW.isBirationalMorphism_p
    have hqb := hW.isBirationalMorphism_q
    have : IsDominant p := hpb.isDominant
    have : IsDominant q := hqb.isDominant
    have : IsProper p := hW.isProper_p
    have : IsProper q := hW.isProper_q
    have hpbij := hpb.functionFieldMap_bijective
    have hqbij := hqb.functionFieldMap_bijective
    have : IsSeparated sX := hXn.1.toIsSeparated
    have : IsSeparated sY := hYn.1.toIsSeparated
    have := isSeparated_toTerminal sX
    have := isSeparated_toTerminal sY
    -- `Q = p(P)` is a prime divisor of `X` with `ord_P = ord_Q`.
    obtain ⟨Q, -, hpQ, -, hEXv⟩ :=
      ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hXn EX hEX
    change p P.genericPoint = Q.genericPoint at hpQ
    rw [hEXv] at ha'
    have KF := specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
    rcases hT : Mori.RationalMap.transformPrimeDivisor φ Q with _ | Q'
    · -- `φ_*Q = 0`: the inequality is part of the definition of a weak log canonical model.
      obtain ⟨θ, hθq, hθ⟩ := exists_ringHom_of_specMap _ p q hpbij KF
      have hψθ := specMap_comp_fromFunctionField_of_isInverse hφb.isInverse_inverse θ hθ
      have KF' : Spec.map (CommRingCat.ofHom (functionFieldMap q)) ≫
          hφb.inverse.fromFunctionField = W.fromSpecStalk (genericPoint W) ≫ p := by
        rw [← hθq, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hψθ]
        exact functionFieldMap_fromSpecStalk p
      obtain ⟨g', hg'⟩ := hφb.inverse.exists_rep
      exact hexc hφb Q hT EY a a' ⟨g', p, hpb, hg',
        comp_eq_of_specMap_fromFunctionField_eq q p _ KF' g' hg', hEXv⟩ ha ha'
    · -- `φ_*Q = Q'`: both discrepancies are `-coeff_Q(D_X)`.
      have himg {Q₁ : Mori.PrimeDivisor X}
          (hT₁ : Mori.RationalMap.transformPrimeDivisor φ Q₁ = some Q')
          {w : W} (hw : p w = Q₁.genericPoint) : q w = Q'.genericPoint :=
        apply_eq_genericPoint_of_transformPrimeDivisor_eq_some KF hT₁ hw
      have hqP := himg hT hpQ
      have : IsIso (q.stalkMap P.genericPoint) :=
        isIso_stalkMap_of_apply_eq_genericPoint q hqbij Q' hqP
      rw [show EY.valuation = Q'.divisorialValuation from
        divisorialValuation_comap_functionFieldMap_eq q P Q' hqP] at ha
      -- `Q` is the only prime divisor of `X` with `φ_*Q = Q'`.
      have huniq : ∀ Q₁, Mori.RationalMap.transformPrimeDivisor φ Q₁ = some Q' → Q₁ = Q := by
        intro Q₁ hT₁
        obtain ⟨P₁, hp₁, -, -⟩ :=
          MMP.Positivity.exists_isIso_stalkMap_forall_transformDivisor_apply.{u, 0} hXn
            (hW.comp_p ▸ hWn) hpb Q₁
        have heq := eq_of_apply_eq_genericPoint q hqbij Q' hqP (himg hT₁ hp₁)
        exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective (hp₁.symm.trans (heq ▸ hpQ))
      have hQ'Fs : Q' ∉ Fs := fun h => (hFs Q').mp h Q hT
      have hcoef : G.coeff Q' = D_X.coeff Q := by
        rw [hG]
        change (Mori.RationalMap.transformDivisor φ D_X + ∑ F ∈ Fs, Finsupp.single F (c F)) Q' =
          D_X Q
        rw [Finsupp.add_apply, Finsupp.finset_sum_apply,
          Finset.sum_eq_zero fun F hF =>
            Finsupp.single_eq_of_ne' fun h : F = Q' => hQ'Fs (h ▸ hF),
          add_zero]
        exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq hT huniq D_X
      have h1 := eq_neg_coeff_of_isDiscrepancy ha
      have h2 := eq_neg_coeff_of_isDiscrepancy ha'
      linarith
  )

end MMP.Flips

namespace MMP.Intersection

open MMP.Mori (Divisor RDivisor)

/-- The coefficients of `B - ⌊F⌋` are nonnegative exactly where those of `B - F` exceed `-1`. -/
private theorem coeff_sub_roundDown_nonneg_iff {X' : Scheme.{u}} (B : Divisor X')
    (F : RDivisor X') (E : MMP.Mori.PrimeDivisor X') :
    0 ≤ (B - WeilRDivisor.roundDown F).coeff E ↔ -1 < (B.toRDivisor - F).coeff E := by
  rw [MMP.Mori.DivisorWithCoeffs.coeff_sub, MMP.Mori.DivisorWithCoeffs.coeff_sub,
    WeilRDivisor.coeff_roundDown, MMP.Mori.Divisor.coeff_toRDivisor]
  rw [sub_nonneg, Int.floor_le_iff]
  constructor <;> intro h <;> push_cast at * <;> linarith

section Sections

variable {X X' : Scheme.{u}} [IsIntegral X] [IsIntegral X'] [IsLocallyNoetherian X'] [IsNormal X']
  (μ : X' ⟶ X) [IsDominant μ] (G : Divisor X')

/-- If the constant `1` is a global section of `μ_*𝒪_{X'}(G)`, then `G` is effective. -/
private theorem coeff_nonneg_of_one_mem (h : (1 : X.functionField) ∈ multiplierIdealSections μ G ⊤)
    (E : MMP.Mori.PrimeDivisor X') : 0 ≤ G.coeff E := by
  have := h.2 E (support_inter_nonempty_of_genericPoint_mem E (V := μ ⁻¹ᵁ ⊤) trivial)
  rwa [map_one, ← WithZero.exp_zero, WithZero.exp_le_exp] at this

/-- If `G` is effective, every regular function on a nonempty open `U ⊆ X` is a section of
`μ_*𝒪_{X'}(G)` over `U`. -/
private theorem range_germ_subset (hG : ∀ E, 0 ≤ G.coeff E) (U : X.Opens) [Nonempty U] :
    Set.range (X.germToFunctionField U) ⊆ multiplierIdealSections μ G U := by
  rintro _ ⟨a, rfl⟩
  refine ⟨fun h' => absurd h' ?_, fun P hP => ?_⟩
  · obtain ⟨u⟩ := ‹Nonempty U›
    obtain ⟨_, hx', x', rfl⟩ := μ.denseRange.inter_open_nonempty _ U.isOpen ⟨u.1, u.2⟩
    exact (TopologicalSpace.Opens.ne_bot_iff_nonempty _).mpr ⟨x', hx'⟩
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X)
    (genericPoint_mem_of_support_inter_nonempty P hP)]
  refine le_trans ?_ (WithZero.exp_le_exp.mpr (hG P))
  rw [WithZero.exp_zero, MMP.Mori.PrimeDivisor.valuationOver_apply,
    MMP.Mori.PrimeDivisor.divisorialValuation_le_one_iff,
    MMP.Mori.functionFieldMap_algebraMap_stalk]
  exact ⟨_, rfl⟩

end Sections

/-- **Triviality of the multiplier ideal is read off discrepancies** (Lazarsfeld §9.3.B): for an
effective `ℝ`-divisor `D` on a non-singular variety `X` over a field of characteristic zero and a
log resolution `μ : X' ⟶ X` of `D`, the multiplier ideal `𝒥(X, D)` is `𝒪_X` if and only if
`ord_E(K_{X'/X} - μ^*D) > -1` for every prime divisor `E` of `X'`. -/
@[mmp "lem_p09b_trivial_multiplier_ideal_iff_discrepancy"]
public theorem IsMultiplierIdeal.eq_range_germToFunctionField_iff {k : Type u} [Field k]
    [CharZero k] {X X' : Scheme.{u}} [IsIntegral X] {sX : X ⟶ Spec (.of k)}
    (hX : MMP.Mori.IsVariety k sX) (hXs : MMP.Mori.IsSmoothScheme sX)
    {D : RCartierDivisor X} {wD : RDivisor X} (hw : IsWeilRDivisorOf D wD)
    (hD : WeilRDivisor.IsEffective wD) {μ : X' ⟶ X} (hμ : IsLogResolution sX D μ)
    {K : X'.CartierDivisor} {wK : Divisor X'} {F : RDivisor X'}
    (hK : IsRelativeCanonicalDivisor sX μ K) (hwK : IsWeilDivisorOfCartier K wK)
    (hF : IsWeilPullback μ D F) {J : X.Opens → Set X.functionField}
    (hJ : IsMultiplierIdeal sX D J) :
    (∀ (U : X.Opens) [Nonempty U], J U = Set.range (X.germToFunctionField U)) ↔
      ∀ E : MMP.Mori.PrimeDivisor X', -1 < (MMP.Mori.Divisor.toRDivisor wK - F).coeff E := by
  obtain ⟨-, hb, hv, hs, -⟩ := id hμ
  haveI : MMP.Mori.IsVariety k (μ ≫ sX) := hv
  haveI : IsIntegral X' := AlgebraicGeometry.IsVariety.toIsIntegral (f := μ ≫ sX)
  haveI : LocallyOfFiniteType (μ ≫ sX) := AlgebraicGeometry.IsVariety.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (μ ≫ sX)
  haveI : Smooth (μ ≫ sX) := (MMP.Mori.isSmoothScheme_iff _).mp hs
  haveI : IsNormal X' := isNormal_of_smooth_over_field (μ ≫ sX)
  haveI : IsDominant μ := hb.isDominant
  have hJ₀ : IsMultiplierIdealOn sX D μ (multiplierIdealSections μ (wK - .roundDown F)) :=
    ⟨hμ, inferInstance, inferInstance, inferInstance, inferInstance, K, wK, F, hK, hwK, hF, rfl⟩
  obtain ⟨X'', μ', hJ'⟩ := hJ
  obtain rfl := IsMultiplierIdealOn.unique hX hXs hJ' hJ₀
  simp_rw [← coeff_sub_roundDown_nonneg_iff]
  refine ⟨fun h => coeff_nonneg_of_one_mem μ (wK - .roundDown F) ?_, fun h U _ => subset_antisymm
    ((IsMultiplierIdealOn.exists_idealSheafData hX hXs hw hD hJ₀).1 U)
    (range_germ_subset μ (wK - .roundDown F) h U)⟩
  rw [@h ⊤ ⟨⟨genericPoint X, trivial⟩⟩]
  exact ⟨1, map_one _⟩

end MMP.Intersection

namespace MMP.Flips

open TopologicalSpace MMP.Mori

/-! ### Intersection numbers, pull-backs and rational top forms -/

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
    (hf.functionFieldMap_bijective)
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
    rw [Category.assoc]; infer_instance
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

/-- **Projection formula** for a pull-back `L₁ = h^*D` of a Cartier divisor `D` along
`h : Y' ⟶ Y`: on a proper curve `C' ⊆ Y'` whose image is the proper curve `C ⊆ Y`,
`L₁ · C' = [k(C') : k(C)] · (D · C)`. -/
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
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_pos (hC ▸ C.isProperCurve)]
  have hCe : (⟨h C'.point, hC ▸ C.isProperCurve⟩ : ProperCurve sY) = C := ProperCurve.ext hC.symm
  rw [hCe]
  simp [OneCycle.degree, ProperCurve.degree, Divisor.degreeOn, mul_comm]

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
  rw [Divisor.degreeOn_pullback_eq_degree_pushforward h rfl hD hB C', OneCycle.pushforward_cycle,
    cyclePushforwardOfPoint, dif_neg hnc, map_zero]

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

/-- The sum of two `ℝ`-Cartier divisors is `ℝ`-Cartier. -/
private theorem isCartierCombination_add {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    {D D' : RDivisor X} (h : IsCartierCombination D) (h' : IsCartierCombination D') :
    IsCartierCombination (D + D') := by
  obtain ⟨m, r, L, hL, rfl⟩ := h
  obtain ⟨m', r', L', hL', rfl⟩ := h'
  refine ⟨m + m', Fin.append r r', Fin.append L L',
    Fin.addCases (fun j => by simpa using hL j) (fun j => by simpa using hL' j), ?_⟩
  simp [Fin.sum_univ_add]

/-- A Cartier divisor `L₀` linearly equivalent to `0` is `ℝ`-Cartier, with intersection number `0`
with every proper curve, for every presentation. -/
private theorem eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent {k : Type u} [Field k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {L₀ : Divisor X} (hc : L₀.IsCartier) (h : L₀.LinearlyEquivalent 0)
    (C : ProperCurve sX) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor X} {x : ℝ}
    (hx : IsRIntersectionNumber k sX (Divisor.toRDivisor L₀) r L C x) : x = 0 := by
  have h1 := isRIntersectionNumber_sum_degreeOn k sX C (fun _ : Fin 1 => (1 : ℝ)) (fun _ => L₀)
    (fun _ => hc)
  have e : ∑ _j : Fin 1, (1 : ℝ) • Divisor.toRDivisor L₀ = Divisor.toRDivisor L₀ := by simp
  rw [e] at h1
  rw [(IsRIntersectionNumber.eq_and_linear k sX C).1 _ _ _ _ _ _ _ hx h1]
  simp [MMP.Flips.Divisor.degreeOn_eq_zero_of_linearlyEquivalent sX C.ι C.dim_le hc h]

/-- Two nonzero rational top forms on a normal variety of dimension `n` over a perfect field have
linearly equivalent divisors. -/
private theorem linearlyEquivalent_divisorOfForm {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [LocallyOfFiniteType sX] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {τ τ' : RationalPluriForms sX n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b⟩ := MMP.Positivity.exists_basis_topForms hX hn
  set c := (ZTensorPower.basis b 1).repr τ' () with hc_def
  set e := (ZTensorPower.basis b 1).repr τ () with he_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ'
  have he : e ≠ 0 := repr_ne_zero_of_ne_zero b hτ
  obtain ⟨φ, hφ⟩ := MMP.Positivity.exists_units_of_ne_zero (mul_ne_zero he (inv_ne_zero hc))
  refine ⟨φ, ?_⟩
  ext Γ
  obtain ⟨N, hN⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
  have e1 := hN 1 τ' hτ'
  have e2 := hN 1 τ hτ
  rw [← hc_def] at e1
  rw [← he_def] at e2
  rw [DivisorWithCoeffs.coeff_sub, coeff_principalDivisor, hφ Γ, Scheme.ord_mul he (inv_ne_zero hc),
    ← zpow_neg_one, ord_zpow _ hc, coeff_divisorOfForm, coeff_divisorOfForm, e1, e2]
  ring

/-- The divisors of two nonzero rational top forms on a normal variety `X`, for two equal
structure morphisms, are linearly equivalent. -/
private theorem linearlyEquivalent_divisorOfForm_of_eq {k : Type u} [Field k] [PerfectField k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {s₁ s₂ : X ⟶ Spec (.of k)} (e : s₁ = s₂) [LocallyOfFiniteType s₁] [LocallyOfFiniteType s₂]
    (hX : IsNormalVariety k s₂) {n : ℕ} (hn : topologicalKrullDim X = n)
    {τ : RationalPluriForms s₁ n 1} {τ' : RationalPluriForms s₂ n 1} (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) : (divisorOfForm τ).LinearlyEquivalent (divisorOfForm τ') := by
  subst e
  exact linearlyEquivalent_divisorOfForm hX hn hτ hτ'

/-- The pull-back of a nonzero rational form along a morphism inducing an isomorphism of function
fields is nonzero. -/
private theorem pullbackRationalPluriForms_ne_zero {k : Type u} [Field k] [PerfectField k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] {sX : X ⟶ Spec (.of k)}
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsDominant f]
    (hf : Function.Bijective (functionFieldMap f)) {d : ℕ}
    (hd : letI := functionFieldAlgebra sX; (Algebra.trdeg k X.functionField).toNat = d) {m : ℤ}
    {τ : RationalPluriForms sX d m} (hτ : τ ≠ 0) : pullbackRationalPluriForms sX f τ ≠ 0 := by
  let := functionFieldAlgebra sX
  obtain ⟨ω, hω⟩ := exists_isPullbackGenerator_of_bijective sX f hf hd
  let := functionFieldAlgebra (f ≫ sX)
  let := functionFieldMapAlgebra f
  have := isScalarTower_functionFieldMap sX f
  have hpull : pullbackRationalPluriForms sX f τ = pullbackFormsAlong hω m τ :=
    pullbackForms_eq hω m τ
  have hrepr := repr_pullbackFormsAlong hω m τ
  intro h0
  have h0' : pullbackFormsAlong hω m τ = 0 := hpull ▸ h0
  have h1 : algebraMap X.functionField Y.functionField
      ((ZTensorPower.basis (basisOfSpanSingleton hω.1 hω.ne_zero) m).repr τ ()) = 0 := by
    rw [← hrepr, h0']
    simp
  exact repr_ne_zero_of_ne_zero _ hτ ((map_eq_zero_iff _ (algebraMap _ _).injective).mp h1)

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

/-- A valuation of `k(Y)` is determined by its restriction to `k(Z)` along a birational
morphism `g : Y ⟶ Z`. -/
private theorem valuation_eq_of_comap_eq {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    {g : Y ⟶ Z} (hg : IsBirationalMorphism g) [IsDominant g]
    {v w : Valuation Y.functionField ℤᵐ⁰}
    (h : v.comap (functionFieldMap g) = w.comap (functionFieldMap g)) : v = w :=
  Valuation.ext fun t => by
    obtain ⟨s, rfl⟩ := hg.functionFieldMap_bijective.2 t
    exact congrArg (fun u => u s) h

/-- The valuation of a divisor `(Y, f, E)` over `X` has nonempty center on `X`. -/
private theorem hasNonemptyCenter_valuation {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [IsIntegral X] (E : ProperDivisorOver k sX) :
    HasNonemptyCenter k sX E.valuation := by
  haveI := E.isIntegral
  haveI := E.isNormal
  haveI := E.isLocallyNoetherian
  haveI := E.isDominant
  exact ⟨⟨E.Y, E.f ≫ sX, E.isNormalVariety, E.E,
    functionFieldAlgEquiv sX E.f E.isBirationalMorphism.functionFieldMap_bijective, rfl⟩, E, rfl⟩

/-! ### Comparison over a common base -/

/-- The pull-back of `-N` is the negative of the pull-back of `N`. -/
private theorem isRCartierPullback_neg {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} {N : RDivisor X} {G : RDivisor Y}
    (h : IsRCartierPullback f N G) : IsRCartierPullback f (-N) (-G) := by
  obtain ⟨m, r, L, L', hL, rfl, hpb, rfl⟩ := h
  exact ⟨m, fun j => -r j, L, L', hL, by simp [neg_smul, Finset.sum_neg_distrib], hpb,
    by simp [neg_smul, Finset.sum_neg_distrib]⟩

/-- **Nefness of `q^*A_Y - p^*A_X - N`.** If `A_Y` is `g`-nef and `-A_X` is `f`-nef, then for
`p : W ⟶ X`, `q : W ⟶ Y` with `p ≫ f = q ≫ g = h` and an `ℝ`-Cartier divisor `N` on `W` with
`N · C = 0` for every proper curve `C`, the divisor `q^*A_Y - p^*A_X - N` is `h`-nef. -/
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
    (hGX : IsRCartierPullback p A_X G_X) (hGY : IsRCartierPullback q A_Y G_Y) {N : RDivisor W}
    (hNc : IsCartierCombination N)
    (hN0 : ∀ (C : ProperCurve sW) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW N r L C x → x = 0) :
    IsRelativelyNef k sW h (G_Y - G_X - N) := by
  obtain ⟨m, r, L, hL, hpres⟩ := isCartierCombination_sub
    (isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY)
      (isCartierCombination_of_isRCartierPullback hGX)) hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C hC x hx => ?_⟩
  obtain ⟨mY, rY, LY, hLY, hYpres⟩ := isCartierCombination_of_isRCartierPullback hGY
  obtain ⟨mX, rX, LX, hLX, hXpres⟩ :=
    isCartierCombination_of_isRCartierPullback (isRCartierPullback_neg hGX)
  obtain ⟨mN, rN, LN, hLN, hNpres⟩ := hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hYpres hXpres hNpres
  have hY := isRIntersectionNumber_sum_degreeOn k sW C rY LY hLY
  have hX := isRIntersectionNumber_sum_degreeOn k sW C rX LX hLX
  have hN := isRIntersectionNumber_sum_degreeOn k sW C rN LN hLN
  rw [← hYpres] at hY
  rw [← hXpres] at hX
  rw [← hNpres] at hN
  have hsum := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 1 hY hX
  have hsum' := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hsum hN
  have e : (1 : ℝ) • ((1 : ℝ) • G_Y + (1 : ℝ) • -G_X) + (-1 : ℝ) • N = G_Y - G_X - N := by
    simp only [one_smul, neg_one_smul]
    abel
  rw [e] at hsum'
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx hsum']
  have h1 := nonneg_of_isRelativelyNef_of_isRCartierPullback q hq g hqg hAY hGY C hC hY
  have h2 := nonneg_of_isRelativelyNef_of_isRCartierPullback p hp f hpf hAX
    (isRCartierPullback_neg hGX) C hC hX
  have h3 := hN0 C hN
  rw [h3]
  linarith

/-- The valuation of `E` over `C` through a morphism depends only on the morphism. -/
private theorem valuationOver_congr {A C : Scheme.{u}} [IsIntegral A] [IsIntegral C]
    [IsLocallyNoetherian A] [IsNormal A] (E : MMP.Mori.PrimeDivisor A) {h₁ h₂ : A ⟶ C} (e : h₁ = h₂)
    [IsDominant h₁] [IsDominant h₂] : E.valuationOver h₁ = E.valuationOver h₂ := by
  subst e
  rfl

section InverseTransform

variable {X Y : Scheme.{u}}

private theorem source_ι_comp_eq_of_toRationalMap_eq [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) : e.source.ι ≫ f = e.iso.hom ≫ e.target.ι :=
  ((Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)).mp
    (Scheme.PartialMap.toRationalMap_eq_iff.mp he)).symm

/-- If `e` is a partial isomorphism representing a morphism `f : Y ⟶ X` and `g'` a partial map
representing `e⁻¹`, then `f ∘ g'` is the identity where `g'` is defined. -/
private theorem apply_hom_eq_of_isInverse [IsReduced Y] [IsReduced X]
    [IsSeparated (X ↘ ⊤_ Scheme)] (f : Y ⟶ X) (e : Y.PartialIso X)
    (he : e.toRationalMap = f.toRationalMap) (g' : X.PartialMap Y)
    (hg' : g'.toRationalMap = e.symm.toRationalMap) {x : X} (hx : x ∈ g'.domain) :
    f (g'.hom ⟨x, hx⟩) = x := by
  have h1 : (g'.compHom f).toRationalMap = (Scheme.PartialMap.id X).toRationalMap := by
    rw [Scheme.RationalMap.compHom_toRationalMap, hg', ← Scheme.RationalMap.compHom_toRationalMap,
      Scheme.PartialMap.toRationalMap_eq_iff,
      Scheme.PartialMap.equiv_toPartialMap_iff_of_isSeparated (S := ⊤_ Scheme)]
    change e.iso.inv ≫ e.source.ι ≫ f = e.target.ι ≫ 𝟙 X
    rw [source_ι_comp_eq_of_toRationalMap_eq f e he, Iso.inv_hom_id_assoc, Category.comp_id]
  have h2 := MMP.Positivity.PartialMap.hom_apply_eq_of_toRationalMap_eq
    (g := g'.compHom f) (g' := Scheme.PartialMap.id X) h1 hx trivial
  change (g'.hom ≫ f) ⟨x, hx⟩ = (X.topIso.hom ≫ 𝟙 X) ⟨x, trivial⟩ at h2
  refine (Scheme.Hom.comp_apply _ _ _).symm.trans (h2.trans ?_)
  rw [Category.comp_id, Scheme.topIso_hom]
  rfl

/-- If the strict transform of a prime divisor `P` of `X` under the inverse of a birational
morphism `f : Y ⟶ X` is `E`, then `f` sends the generic point of `E` to that of `P`. -/
private theorem genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some [IsReduced X] [IsReduced Y]
    [IsSeparated (X ↘ ⊤_ Scheme)] [IsSeparated (Y ↘ ⊤_ Scheme)] {f : Y ⟶ X}
    (hf : IsBirationalMorphism f) {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y}
    (h : Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E) :
    f E.genericPoint = P.genericPoint := by
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  obtain ⟨g', hP, hg'⟩ :=
    Mori.RationalMap.definedAt_iff.mp (Mori.RationalMap.transformPrimeDivisor_eq_some_iff.mp h).1
  rw [genericPoint_eq_of_transformPrimeDivisor_eq_some h g' hg' hP]
  exact apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP

/-- Conversely, let `f : Y ⟶ X` be a proper birational morphism of varieties with `X` normal. If
`f` sends the generic point of a prime divisor `E` of `Y` to that of a prime divisor `P` of `X`,
then the strict transform of `P` under `f⁻¹` is `E`: the map `f⁻¹` is defined at `η_P`
(`MMP.Flips.RationalMap.isMorphismInCodimOne_inverse`), and `f` is injective on the points over
`η_P`, whose local ring is a valuation ring. -/
private theorem transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f)
    {P : Mori.PrimeDivisor X} {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    Mori.RationalMap.transformPrimeDivisor (Mori.RationalMap.IsBirational.inverse hf) P =
      some E := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := DiscrepancyComparison.isSeparated_toTerminal sX
  have := DiscrepancyComparison.isSeparated_toTerminal (f ≫ sX)
  have : IsNormal X := hX.2
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsDominant f := hf.isDominant
  have hbij := hf.functionFieldMap_bijective
  obtain ⟨e, he, he'⟩ := hf.isInverse_inverse
  have hdef : Mori.RationalMap.DefinedAt (Mori.RationalMap.IsBirational.inverse hf)
      P.genericPoint := by
    by_contra hnd
    have h2 := le_closedsCodimension_iff.mp (RationalMap.isMorphismInCodimOne_inverse hX f hY hf)
      (IrreducibleCloseds.closureSingleton P.genericPoint)
      (closure_minimal (Set.singleton_subset_iff.mpr hnd)
        (Mori.RationalMap.dom (Mori.RationalMap.IsBirational.inverse hf)).compl.isClosed)
    rw [codimension_eq_coheight, show IrreducibleCloseds.closureSingleton P.genericPoint =
      (irreducibleSetEquivPoints (α := X)).symm P.genericPoint from rfl,
      Order.coheight_orderIso, P.coheight_genericPoint] at h2
    exact absurd h2 (by decide)
  obtain ⟨g', hP, hg'⟩ := Mori.RationalMap.definedAt_iff.mp hdef
  refine transformPrimeDivisor_eq_some_of_genericPoint_eq g' hg' hP ?_
  have hy := apply_hom_eq_of_isInverse f e he g' (hg'.trans he'.symm) hP
  have := P.isDiscreteValuationRing_localRing
  have : ValuationRing (X.presheaf.stalk (f E.genericPoint)) := by rw [h]; infer_instance
  have : ValuationRing (X.presheaf.stalk (f (g'.hom ⟨P.genericPoint, hP⟩))) := by
    rw [hy]; infer_instance
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij E.genericPoint
  have := MMP.Positivity.isIso_stalkMap_of_valuationRing f hbij (g'.hom ⟨P.genericPoint, hP⟩)
  exact MMP.Positivity.eq_of_isIso_stalkMap f hbij (hy.trans h.symm)

/-- For a proper birational morphism `f : Y ⟶ X` of varieties with `X` normal, the coefficient of
`f⁻¹_* D` along a prime divisor `E` of `Y` with `f(η_E) = η_P` is the coefficient of `D`
along `P`. -/
private theorem birationalInverseTransform_apply_of_genericPoint_eq {k : Type u} [Field k]
    {sX : X ⟶ Spec (.of k)} (hX : IsNormalVariety k sX) (f : Y ⟶ X)
    (hY : Mori.IsVariety k (f ≫ sX)) [IsProper f] (hf : IsBirationalMorphism f) {R : Type*}
    [AddCommMonoid R] (D : DivisorWithCoeffs R X) {P : Mori.PrimeDivisor X}
    {E : Mori.PrimeDivisor Y} (h : f E.genericPoint = P.genericPoint) :
    birationalInverseTransform f hf D E = D P := by
  have : IsIntegral X := hX.1.toIsIntegral
  have : IsIntegral Y := hY.toIsIntegral
  have : IsSeparated sX := hX.1.toIsSeparated
  have : IsSeparated (f ≫ sX) := hY.toIsSeparated
  have := DiscrepancyComparison.isSeparated_toTerminal sX
  have := DiscrepancyComparison.isSeparated_toTerminal (f ≫ sX)
  exact MMP.Positivity.mapPrimeDivisors_apply_of_forall_eq
    (transformPrimeDivisor_inverse_eq_some_of_genericPoint_eq hX f hY hf h)
    (fun P' hP' => AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      ((genericPoint_eq_of_transformPrimeDivisor_inverse_eq_some hf hP').symm.trans h)) D

end InverseTransform

/-- For `d + c = n`, the bound `d + 2 ≤ n` is equivalent to `2 ≤ c`. -/
private theorem withBot_add_two_le_iff {d : WithBot ℕ∞} {c : ℕ∞} {n : ℕ} (h : d + c = n) :
    d + 2 ≤ n ↔ 2 ≤ c := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h
  | coe d =>
    rw [← WithBot.coe_add] at h
    have h := WithBot.coe_injective h
    obtain ⟨hd, hc⟩ : d ≠ ⊤ ∧ c ≠ ⊤ := by
      rw [← not_or, ← ENat.add_eq_top, h]
      exact ENat.natCast_ne_top n
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
not exceptional over `X`: `ord_P` is `ord_{P_X}` for a prime divisor `P_X` of `X` lying over `Q`,
which is not exceptional over `Z`. -/
private theorem exists_primeDivisor_valuation_eq_of_map_genericPoint_eq {k : Type u} [Field k]
    {W X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsLocallyNoetherian Z]
    [IsNormal Z] (hZ : IsNormalVariety k sZ) [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    {f : X ⟶ Z} [IsProper f] (hX : IsNormalVariety k (f ≫ sZ)) (hf : IsBirationalMorphism f)
    [IsIntegral W] [IsLocallyNoetherian W] [IsNormal W] {p : W ⟶ X} [IsProper p]
    (hWp : IsNormalVariety k (p ≫ f ≫ sZ)) (hpb : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor Z)
    (hPQ : f (p P.genericPoint) = Q.genericPoint) :
    ∃ P_X : MMP.Mori.PrimeDivisor X,
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
        ProperDivisorOver k (f ≫ sZ)).valuation = P_X.divisorialValuation ∧
      f P_X.genericPoint = Q.genericPoint ∧ ¬ IsExceptionalPrimeDivisor sZ f P_X := by
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
  have hfη : f P_X.genericPoint = Q.genericPoint := by
    rw [← hPQ]
    exact congrArg f hη.symm
  refine ⟨P_X, hval, hfη, fun h => ?_⟩
  have h2 := (isExceptionalPrimeDivisor_iff_two_le_coheight hZ f hX hf P_X).mp h
  rw [hfη, Q.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- **Discrepancies along divisors not exceptional over the base.** Let `p : W ⟶ X`,
`f : X ⟶ Z` be proper birational morphisms of normal varieties, `D` an `ℝ`-divisor on `Z` and
`E_X` an `ℝ`-divisor on `X` supported on the prime divisors exceptional over `Z`. If a prime
divisor `P` of `W` maps to the generic point of a prime divisor `Q` of `Z`, then
`a(P, X, f⁻¹_*D + E_X) = -coeff_Q(D)`. -/
private theorem isDiscrepancy_eq_neg_coeff_of_map_genericPoint_eq {k : Type u} [Field k]
    [PerfectField k] {W X Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (hZ : IsNormalVariety k sZ) [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] {f : X ⟶ Z} [IsProper f]
    [LocallyOfFiniteType (f ≫ sZ)] (hX : IsNormalVariety k (f ≫ sZ))
    (hf : IsBirationalMorphism f) [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] {p : W ⟶ X} [IsProper p]
    (hWp : IsNormalVariety k (p ≫ f ≫ sZ)) (hpb : IsBirationalMorphism p)
    (P : MMP.Mori.PrimeDivisor W) (Q : MMP.Mori.PrimeDivisor Z)
    (hPQ : f (p P.genericPoint) = Q.genericPoint) {D : RDivisor Z} {E_X : RDivisor X}
    (hEX : ∀ P : Mori.PrimeDivisor X, ¬ IsExceptionalPrimeDivisor sZ f P → E_X.coeff P = 0)
    {n : ℕ} {K_X : Divisor X} {a : ℝ}
    (ha : IsDiscrepancy (f ≫ sZ) n K_X (birationalInverseTransform f hf D + E_X)
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
        ProperDivisorOver k (f ≫ sZ)).valuation a) :
    a = -D Q := by
  obtain ⟨P_X, hv, hfP, hnP⟩ :=
    exists_primeDivisor_valuation_eq_of_map_genericPoint_eq hZ hX hf hWp hpb P Q hPQ
  rw [hv] at ha
  rw [ha.eq_neg_coeff, DivisorWithCoeffs.coeff_apply, Finsupp.add_apply,
    birationalInverseTransform_apply_of_genericPoint_eq hZ f hX.1 hf D hfP,
    show E_X P_X = 0 from hEX P_X hnP, add_zero]

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

/-- A divisor `v` of `k(Z)` with nonempty center on `Z` is, through a proper birational morphism
`f : X ⟶ Z`, the valuation of a divisor over `X`. -/
private theorem exists_valuation_eq_of_comap_eq {k : Type u} [Field k] {X Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [IsIntegral X] (hZ : IsNormalVariety k sZ)
    {f : X ⟶ Z} [IsProper f] (hX : IsNormalVariety k (f ≫ sZ)) (hf : IsBirationalMorphism f)
    {v : Valuation Z.functionField ℤᵐ⁰} (hv : HasNonemptyCenter k sZ v)
    {vX : Valuation X.functionField ℤᵐ⁰}
    (hvX : haveI : IsDominant f := hf.isDominant
      vX.comap (functionFieldMap f) = v) :
    ∃ D₁ : ProperDivisorOver k (f ≫ sZ), D₁.valuation = vX := by
  haveI : IsDominant f := hf.isDominant
  obtain ⟨-, DZ, hDZ⟩ := hv
  obtain ⟨D₁, hD₁, -⟩ :=
    ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq hZ.1 f hX.1 hf DZ
  exact ⟨D₁, valuation_eq_of_comap_eq hf (hD₁.trans (hDZ.trans hvX.symm))⟩

/-- **Comparison of discrepancies over a common base** (FA 2.28.2.1, Kollár–Mori 3.38). Let
`f : X ⟶ Z`, `g : Y ⟶ Z` be proper birational morphisms of normal varieties over a perfect field,
`D` an `ℝ`-divisor on `Z`, and `E_X`, `E_Y` `ℝ`-divisors on `X`, `Y` supported on the prime
divisors exceptional over `Z`. Let `K_X = div_X(f^*ω)`, `K_Y = div_Y(g^*ω)` for a rational
`n`-form `ω` on `Z`, and put `B_X = f⁻¹_*D + E_X`, `B_Y = g⁻¹_*D + E_Y`. If `-(K_X + B_X)` is
`ℝ`-Cartier and `f`-nef and `K_Y + B_Y` is `ℝ`-Cartier and `g`-nef, then for every divisor `v`
of `k(Z)` with nonempty center on `Z`, with `v_X`, `v_Y` the same divisor of `k(X)`, `k(Y)`,
`v` has nonempty center on `X` and on `Y`, and `a(v_X, X, B_X) ≤ a(v_Y, Y, B_Y)`. -/
@[mmp "prop_fa2_discrepancy_comparison_relative"]
public theorem isDiscrepancy_le_of_isRelativelyNef {k : Type u} [Field k] [PerfectField k]
    {X Y Z : Scheme.{u}} {sZ : Z ⟶ Spec (.of k)} [IsIntegral Z] [QuasiCompact sZ]
    [LocallyOfFiniteType sZ] [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [CompactSpace X] [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y]
    (hZ : IsNormalVariety k sZ) {f : X ⟶ Z} {g : Y ⟶ Z} [IsProper f] [IsProper g]
    (hX : IsNormalVariety k (f ≫ sZ)) (hY : IsNormalVariety k (g ≫ sZ))
    (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g)
    {n : ℕ} {ω : RationalPluriForms sZ n 1} {K_X : Divisor X} {K_Y : Divisor Y}
    (hKX : haveI : IsDominant f := hf.isDominant
      divisorOfForm (pullbackRationalPluriForms sZ f ω) = K_X)
    (hKY : haveI : IsDominant g := hg.isDominant
      divisorOfForm (pullbackRationalPluriForms sZ g ω) = K_Y)
    {D : RDivisor Z} {E_X : RDivisor X} {E_Y : RDivisor Y}
    (hEX : ∀ P : Mori.PrimeDivisor X, ¬ IsExceptionalPrimeDivisor sZ f P → E_X.coeff P = 0)
    (hEY : ∀ P : Mori.PrimeDivisor Y, ¬ IsExceptionalPrimeDivisor sZ g P → E_Y.coeff P = 0)
    (hAX : IsRelativelyNef k (f ≫ sZ) f
      (-logCanonicalDivisor K_X (birationalInverseTransform f hf D + E_X)))
    (hAY : IsRelativelyNef k (g ≫ sZ) g
      (logCanonicalDivisor K_Y (birationalInverseTransform g hg D + E_Y)))
    {v : Valuation Z.functionField ℤᵐ⁰} (hv : HasNonemptyCenter k sZ v)
    {vX : Valuation X.functionField ℤᵐ⁰} {vY : Valuation Y.functionField ℤᵐ⁰}
    (hvX : haveI : IsDominant f := hf.isDominant
      vX.comap (functionFieldMap f) = v)
    (hvY : haveI : IsDominant g := hg.isDominant
      vY.comap (functionFieldMap g) = v) :
    HasNonemptyCenter k (f ≫ sZ) vX ∧ HasNonemptyCenter k (g ≫ sZ) vY ∧
      ∀ a a' : ℝ, IsDiscrepancy (f ≫ sZ) n K_X (birationalInverseTransform f hf D + E_X) vX a →
        IsDiscrepancy (g ≫ sZ) n K_Y (birationalInverseTransform g hg D + E_Y) vY a' →
          a ≤ a' := by
  haveI : IsDominant f := hf.isDominant
  haveI : IsDominant g := hg.isDominant
  obtain ⟨D₁, hD₁⟩ := exists_valuation_eq_of_comap_eq hZ hX hf hv hvX
  obtain ⟨D₂, hD₂⟩ := exists_valuation_eq_of_comap_eq hZ hY hg hv hvY
  refine ⟨hD₁ ▸ hasNonemptyCenter_valuation D₁, hD₂ ▸ hasNonemptyCenter_valuation D₂, ?_⟩
  intro a a' ha ha'
  -- a common normal model `W` of `X` and `Y` over `Z` on which `B` is a prime divisor `P₀`
  obtain ⟨φ, hφ, hφS⟩ := exists_isBirational_compHom_eq hf hg
  obtain ⟨W, p, q, hWp, hpb, hpP, hqP, hqb, -, hcomm, P₀, hP₀⟩ :=
    MMP.Mori.exists_isNormalVariety_isProper_isBirationalMorphism_primeDivisor_valuation_eq hX hY
      f g φ hφ hφS D₁.toDivisorOver
  haveI := hpP
  haveI := hqP
  haveI : IsIntegral W := hWp.1.toIsIntegral
  haveI : IsNormal W := hWp.2
  haveI := hWp.1.toLocallyOfFiniteType
  haveI : QuasiCompact (p ≫ f ≫ sZ) := hWp.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ f ≫ sZ)
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace (p ≫ f ≫ sZ)
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  have hWq : IsNormalVariety k (q ≫ g ≫ sZ) := by
    rwa [← Category.assoc, ← hcomm, Category.assoc]
  haveI := hWq.1.toLocallyOfFiniteType
  haveI := hX.1.toLocallyOfFiniteType
  haveI := hY.1.toLocallyOfFiniteType
  haveI := hX.1.toQuasiCompact
  haveI := hY.1.toQuasiCompact
  haveI := hX.1.toIsSeparated
  haveI := hY.1.toIsSeparated
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  have hhb : IsBirationalMorphism (p ≫ f) := isBirationalMorphism_comp_of_isBirational f p
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hf)
    (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hpb)
  -- `B` is `ord_{P₀}` on `X` and on `Y`
  have hvalX : (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P₀⟩ inferInstance :
      ProperDivisorOver k (f ≫ sZ)).valuation = vX := hP₀.trans hD₁
  have hvalY : (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P₀⟩ inferInstance :
      ProperDivisorOver k (g ≫ sZ)).valuation = vY := by
    refine valuation_eq_of_comap_eq hg ?_
    rw [hvY, ← hvX, ← hvalX]
    change (P₀.valuationOver q).comap (functionFieldMap g) =
      (P₀.valuationOver p).comap (functionFieldMap f)
    rw [comap_valuationOver, comap_valuationOver]
    exact valuationOver_congr P₀ hcomm.symm
  -- the forms `ω_X`, `ω_Y` with `K_X = div ω_X`, `K_Y = div ω_Y` used in the discrepancies
  obtain ⟨hKXc, hBXc, -, _EX, ωX, _mX, _rX, _LX, -, hωXK, hwX⟩ := id ha
  obtain ⟨hKYc, hBYc, -, _EY, ωY, _mY, _rY, _LY, -, hωYK, hwY⟩ := id ha'
  subst hωXK hωYK
  have hn : topologicalKrullDim X = n := hKXc.topologicalKrullDim_eq
  have htrX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := f ≫ sZ) hn
  have htrY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := g ≫ sZ)
    hKYc.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = n := by
    rw [← toENat_trdeg_functionField (sX := p ≫ f ≫ sZ),
      ← trdeg_functionField_eq_of_bijective (f ≫ sZ) p hpb.functionFieldMap_bijective,
      toENat_trdeg_functionField (sX := f ≫ sZ), hn]
  have hpω := pullbackRationalPluriForms_ne_zero p hpb.functionFieldMap_bijective htrX hwX.2.2.1
  have hqω := pullbackRationalPluriForms_ne_zero q hqb.functionFieldMap_bijective htrY hwY.2.2.1
  -- `L₁ = div_W(q^*ω_Y) - div_W(p^*ω_X)` is principal
  obtain ⟨L₁, hL₁_def⟩ : ∃ L₁ : Divisor W,
      L₁ = divisorOfForm (pullbackRationalPluriForms (g ≫ sZ) q ωY) -
        divisorOfForm (pullbackRationalPluriForms (f ≫ sZ) p ωX) := ⟨_, rfl⟩
  have hL₁ : L₁.LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm_of_eq
      (by rw [← Category.assoc, ← hcomm, Category.assoc]) hWp hnW hqω hpω
    exact ⟨φ, by rwa [sub_zero, hL₁_def]⟩
  have hL₁c : L₁.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hL₁ Divisor.isCartier_zero
  -- `p^*A_X`, `q^*A_Y` and `p^*A_X - q^*A_Y + L₁ = ∑ (a_Y(P) - a_X(P)) P`
  obtain ⟨G_X, hGX, -⟩ := existsUnique_isRCartierPullback p hBXc
  obtain ⟨G_Y, hGY, -⟩ := existsUnique_isRCartierPullback q hBYc
  have haX := fun P => isDiscrepancy_ordPullback_sub_coeff_pullback hX ωX hwX.2.2.1 hKXc hBXc p
    hWp hpb hGX P
  have haY := fun P => isDiscrepancy_ordPullback_sub_coeff_pullback hY ωY hwY.2.2.1 hKYc hBYc q
    hWq hqb hGY P
  obtain ⟨aX, haX_def⟩ : ∃ aX : MMP.Mori.PrimeDivisor W → ℝ, ∀ P, aX P =
      ((ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
        ProperDivisorOver k (f ≫ sZ)).toDivisorOver.ordPullback ωX : ℝ) - G_X.coeff P :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨aY, haY_def⟩ : ∃ aY : MMP.Mori.PrimeDivisor W → ℝ, ∀ P, aY P =
      ((ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance :
        ProperDivisorOver k (g ≫ sZ)).toDivisorOver.ordPullback ωY : ℝ) - G_Y.coeff P :=
    ⟨_, fun _ => rfl⟩
  replace haX := fun P => (haX_def P) ▸ haX P
  replace haY := fun P => (haY_def P) ▸ haY P
  have hX1 : ∀ P, ((ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance :
      ProperDivisorOver k (f ≫ sZ)).toDivisorOver.ordPullback ωX : ℝ) =
      Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms (f ≫ sZ) p ωX)) P :=
    fun _ => rfl
  have hY1 : ∀ P, ((ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance :
      ProperDivisorOver k (g ≫ sZ)).toDivisorOver.ordPullback ωY : ℝ) =
      Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms (g ≫ sZ) q ωY)) P :=
    fun _ => rfl
  have hcoeff : ∀ P, (G_X - G_Y + Divisor.toRDivisor L₁).coeff P = aY P - aX P := by
    intro P
    rw [haX_def, haY_def, hX1, hY1, hL₁_def, map_sub]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  have h1 : a = aX P₀ := ha.eq (hvalX ▸ haX P₀)
  have h2 : a' = aY P₀ := ha'.eq (hvalY ▸ haY P₀)
  -- `M = q^*A_Y - p^*A_X` is nef over `Z`
  have hL₁r : IsCartierCombination (Divisor.toRDivisor L₁) :=
    ⟨1, fun _ => 1, fun _ => L₁, fun _ => hL₁c, by simp [← toRDivisor_eq_mapCoeffs]⟩
  have hMnef : IsRelativelyNef k (p ≫ f ≫ sZ) (p ≫ f) (G_Y - G_X - Divisor.toRDivisor L₁) :=
    isRelativelyNef_sub_of_isRCartierPullback p q rfl (by rw [← Category.assoc, ← hcomm,
      Category.assoc]) f g rfl hcomm.symm hAX hAY hGX hGY hL₁r
      fun C _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₁c hL₁ C hx
  -- the coefficients of `M` along prime divisors not exceptional over `Z` vanish
  have hBG : ∀ P : MMP.Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sZ (p ≫ f) P →
      (G_X - G_Y + Divisor.toRDivisor L₁).coeff P = 0 := by
    intro P hP
    -- `P` lies over a prime divisor `Q` of `Z`
    have hWZ : IsNormalVariety k ((p ≫ f) ≫ sZ) := by rwa [Category.assoc]
    have hne : ¬ (ProperDivisorOver.mk ⟨W, p ≫ f, hWZ, hhb, P⟩ inferInstance :
        ProperDivisorOver k sZ).IsExceptional := fun h => hP ⟨hWZ, hhb, inferInstance, h⟩
    obtain ⟨Q, -, hQ, -, -⟩ := ProperDivisorOver.exists_primeDivisor_of_not_isExceptional hZ _ hne
    have hQX : f (p P.genericPoint) = Q.genericPoint := hQ
    have hQY : g (q P.genericPoint) = Q.genericPoint := by
      rwa [← Scheme.Hom.comp_apply, ← hcomm]
    rw [hcoeff P, isDiscrepancy_eq_neg_coeff_of_map_genericPoint_eq hZ hX hf hWp hpb P Q hQX hEX
      (haX P), isDiscrepancy_eq_neg_coeff_of_map_genericPoint_eq hZ hY hg hWq hqb P Q hQY hEY
      (haY P), sub_self]
  -- the negativity lemma: `-M` is effective
  have hB := (isEffective_and_preimage_singleton_subset_supp_or_disjoint_of_isRelativelyNef_neg k
    sZ (p ≫ f ≫ sZ) hZ hWp (p ≫ f) (Category.assoc _ _ _) hhb
    (isCartierCombination_add (isCartierCombination_sub
      (isCartierCombination_of_isRCartierPullback hGX)
      (isCartierCombination_of_isRCartierPullback hGY)) hL₁r)
    hBG (by convert hMnef using 1; abel)).1 P₀
  rw [hcoeff P₀] at hB
  linarith

/-! ### Weak log canonical models -/

section CommonModel

/-- Conversely, if `Spec k(W) ⟶ Spec k(X) ⟶ Y` along `φ` is `Spec k(W) ⟶ W ⟶ Y`, then
`q = φ ∘ p` as maps. -/
private theorem exists_partialMap_of_specMap_fromFunctionField_eq {W X Y : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] (φ : X.RationalMap Y) (p : W ⟶ X) [IsDominant p] (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    ∃ φ₀ : X.PartialMap Y, φ₀.toRationalMap = φ ∧
      ∃ hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W),
        (Scheme.PartialMap.mk (p ⁻¹ᵁ φ₀.domain) hd
          (p.resLE φ₀.domain (p ⁻¹ᵁ φ₀.domain) le_rfl ≫ φ₀.hom)).toRationalMap =
          q.toRationalMap := by
  obtain ⟨φ₀, rfl⟩ := φ.exists_rep
  have hx := DiscrepancyComparison.genericPoint_mem_of_dense φ₀.dense_domain
  have hW : genericPoint W ∈ p ⁻¹ᵁ φ₀.domain := by
    change p (genericPoint W) ∈ φ₀.domain
    rwa [map_genericPoint_of_isDominant]
  have hd : Dense ((p ⁻¹ᵁ φ₀.domain : W.Opens) : Set W) := (p ⁻¹ᵁ φ₀.domain).isOpen.dense ⟨_, hW⟩
  refine ⟨φ₀, rfl, hd, Scheme.RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
  rwa [Scheme.RationalMap.fromFunctionField_toRationalMap,
    DiscrepancyComparison.fromFunctionField_resLE_comp, MMP.Flips.RationalMap.fromFunctionField_hom]

/-- The generic-point form of `q = φ ∘ p` is stable under precomposition with a dominant
`h : W' ⟶ W`. -/
private theorem specMap_fromFunctionField_comp {W' W X Y : Scheme.{u}} [IsIntegral W']
    [IsIntegral W] [IsIntegral X] (φ : X.RationalMap Y) (h : W' ⟶ W) (p : W ⟶ X) (q : W ⟶ Y)
    [IsDominant h] [IsDominant p]
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    Spec.map (CommRingCat.ofHom (functionFieldMap (h ≫ p))) ≫ φ.fromFunctionField =
      W'.fromSpecStalk (genericPoint W') ≫ h ≫ q := by
  have e : functionFieldMap (h ≫ p) = (functionFieldMap h).comp (functionFieldMap p) :=
    RingHom.ext fun t =>
      (MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply h p t).symm
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, H, ← Category.assoc,
    functionFieldMap_fromSpecStalk h, Category.assoc]

/-- **A common model lies over the base.** If `q = φ ∘ p` at the generic point of `W` and
`g ∘ φ = f`, then `p ≫ f = q ≫ g`, for `W` reduced and `Z` separated. -/
private theorem comp_eq_comp_of_specMap_fromFunctionField_eq {W X Y Z : Scheme.{u}}
    [IsIntegral W] [IsIntegral X] [IsSeparated (Z ↘ ⊤_ Scheme)] {φ : X.RationalMap Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (hφ : φ.compHom g = f.toRationalMap) (p : W ⟶ X) [IsDominant p]
    (q : W ⟶ Y)
    (H : Spec.map (CommRingCat.ofHom (functionFieldMap p)) ≫ φ.fromFunctionField =
      W.fromSpecStalk (genericPoint W) ≫ q) :
    p ≫ f = q ≫ g := by
  have h1 : (p ≫ f).toRationalMap = (q ≫ g).toRationalMap := by
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [MMP.Flips.RationalMap.fromFunctionField_hom, MMP.Flips.RationalMap.fromFunctionField_hom,
      ← Category.assoc, ← functionFieldMap_fromSpecStalk p, Category.assoc,
      ← MMP.Flips.RationalMap.fromFunctionField_hom f, ← hφ,
      MMP.Flips.RationalMap.fromFunctionField_compHom, ← Category.assoc, H, Category.assoc]
  obtain ⟨U, hU, hUl, hUr, e⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp h1
  have : IsDominant U.ι := AlgebraicGeometry.Opens.isDominant_ι hU
  have : Z.IsSeparated := ⟨‹_›⟩
  refine ext_of_isDominant (ι := U.ι) ?_
  simp only [Scheme.PartialMap.restrict_hom, Scheme.Hom.toPartialMap_hom, Scheme.topIso_hom,
    Category.assoc] at e
  exact (Scheme.homOfLE_ι_assoc W hUl _).symm.trans (e.trans (Scheme.homOfLE_ι_assoc W hUr _))

end CommonModel

/-- **Composing a common model with a model of it.** If `(W, p, q)` is a common model of `φ` and
`h : W' ⟶ W` is a proper birational morphism from a normal variety, then `(W', h ≫ p, h ≫ q)` is a
common model of `φ`. -/
private theorem isCommonModel_comp {k : Type u} [Field k] {X Y Z W W' : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)}
    {sW : W ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q) (h : W' ⟶ W)
    [IsProper h] (hh : IsBirationalMorphism h) (hW' : IsNormalVariety k (h ≫ sW)) :
    IsCommonModel k sX sY sZ (h ≫ sW) f g φ (h ≫ p) (h ≫ q) := by
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : IsIntegral W' := hW'.1.toIsIntegral
  haveI := hW.isProper_p
  haveI := hW.isProper_q
  haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
  haveI : IsDominant h := hh.isDominant
  have hhB := MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism hh
  have KF := DiscrepancyComparison.specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
  exact
    { isVariety_X := hW.isVariety_X
      isVariety_Y := hW.isVariety_Y
      isVariety_Z := hW.isVariety_Z
      comp_f := hW.comp_f
      comp_g := hW.comp_g
      isProper_f := hW.isProper_f
      isProper_g := hW.isProper_g
      isModificationOf := hW.isModificationOf
      isNormalVariety := hW'
      comp_p := by rw [Category.assoc, hW.comp_p]
      comp_q := by rw [Category.assoc, hW.comp_q]
      isProper_p := inferInstance
      isProper_q := inferInstance
      isBirationalMorphism_p := isBirationalMorphism_comp_of_isBirational p h
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          hW.isBirationalMorphism_p) hhB
      isBirationalMorphism_q := isBirationalMorphism_comp_of_isBirational q h
        (MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism
          hW.isBirationalMorphism_q) hhB
      comp_eq := exists_partialMap_of_specMap_fromFunctionField_eq φ (h ≫ p) (h ≫ q)
        (specMap_fromFunctionField_comp φ h p q KF) }

/-- Numerical equivalence over a base is reflexive on `ℝ`-Cartier divisors. -/
private theorem isNumericallyEquivalentOver_self {k : Type u} [Field k] {W X : Scheme.{u}}
    {sW : W ⟶ Spec (.of k)} [QuasiCompact sW] [IsLocallyNoetherian W] [IsNormal W]
    {p : W ⟶ X} {D : RDivisor W} (hD : IsCartierCombination D) :
    IsNumericallyEquivalentOver k sW p D D :=
  ⟨hD, hD, fun C _ _ r₁ L₁ x₁ _ r₂ L₂ x₂ hx₁ hx₂ =>
    (IsRIntersectionNumber.eq_and_linear k _ C).1 _ r₁ L₁ r₂ L₂ x₁ x₂ hx₁ hx₂⟩

/-- **Nefness of `q^*A_Y - N` over `X`.** Let `p : W ⟶ X`, `q : W ⟶ Y` with `p ≫ f = q ≫ g`. If
`A_Y` is `g`-nef and `N` is an `ℝ`-Cartier divisor on `W` with `N · C = 0` for every proper curve
`C`, then `q^*A_Y - N` is `p`-nef. -/
private theorem isRelativelyNef_sub_of_isRCartierPullback_of_comp_eq {k : Type u} [Field k]
    {W X Y Z : Scheme.{u}} {sY : Y ⟶ Spec (.of k)} [IsSeparated sY] [LocallyOfFiniteType sY]
    [QuasiCompact sY] [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [IsIntegral W]
    [IsLocallyNoetherian W] [IsNormal W] [CompactSpace W] {sW : W ⟶ Spec (.of k)}
    [QuasiCompact sW] (p : W ⟶ X) (q : W ⟶ Y) [IsProper q] (hq : q ≫ sY = sW) (f : X ⟶ Z)
    (g : Y ⟶ Z) (hcomm : p ≫ f = q ≫ g) {A_Y : RDivisor Y} (hAY : IsRelativelyNef k sY g A_Y)
    {G_Y : RDivisor W} (hGY : IsRCartierPullback q A_Y G_Y) {N : RDivisor W}
    (hNc : IsCartierCombination N)
    (hN0 : ∀ (C : ProperCurve sW) {m : ℕ} {r : Fin m → ℝ} {L : Fin m → Divisor W} {x : ℝ},
      IsRIntersectionNumber k sW N r L C x → x = 0) :
    IsRelativelyNef k sW p (G_Y - N) := by
  obtain ⟨m, r, L, hL, hpres⟩ :=
    isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY) hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hpres
  refine ⟨m, r, L, hL, hpres, fun C hC x hx => ?_⟩
  obtain ⟨mY, rY, LY, hLY, hYpres⟩ := isCartierCombination_of_isRCartierPullback hGY
  obtain ⟨mN, rN, LN, hLN, hNpres⟩ := hNc
  simp only [← toRDivisor_eq_mapCoeffs] at hYpres hNpres
  have hY := isRIntersectionNumber_sum_degreeOn k sW C rY LY hLY
  have hN := isRIntersectionNumber_sum_degreeOn k sW C rN LN hLN
  rw [← hYpres] at hY
  rw [← hNpres] at hN
  have hsum := (IsRIntersectionNumber.eq_and_linear k sW C).2 _ _ _ _ _ _ _ _ 1 (-1) hY hN
  have e : (1 : ℝ) • G_Y + (-1 : ℝ) • N = G_Y - N := by
    simp only [one_smul, neg_one_smul]
    abel
  rw [e] at hsum
  rw [(IsRIntersectionNumber.eq_and_linear k sW C).1 _ _ _ _ _ _ _ hx hsum]
  have hC' : C.IsContractedBy (q ≫ g) := fun z hz => by
    rw [← hcomm, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hC z hz]
  have h1 := nonneg_of_isRelativelyNef_of_isRCartierPullback q hq g rfl hAY hGY C hC' hY
  have h3 := hN0 C hN
  rw [h3]
  linarith

/-- **FA 2.23.3 on a common model.** For a weak log canonical model `g : (Y, D_{𝓕,Y}) ⟶ Z` of
`f : (X, D_X) ⟶ Z`, a common model `(W, p, q)` of `φ` and any prime divisor `P` of `W`,
`a(ord_P, D_{𝓕,Y}) ≥ a(ord_P, D_X)`. -/
private theorem isDiscrepancy_le_of_isCommonModel {k : Type u}
    [Field k] [PerfectField k] {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
    {sY : Y ⟶ Spec (.of k)} {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X]
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY]
    [QuasiCompact sY] {n : ℕ} {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X}
    {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z} {φ : X.RationalMap Y}
    {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    (P₀ : Mori.PrimeDivisor W) :
    let EX : ProperDivisorOver k sX :=
      { Y := W, f := p, isNormalVariety := hW.comp_p ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_p, E := P₀, isProper := hW.isProper_p }
    let EY : ProperDivisorOver k sY :=
      { Y := W, f := q, isNormalVariety := hW.comp_q ▸ hW.isNormalVariety,
        isBirationalMorphism := hW.isBirationalMorphism_q, E := P₀, isProper := hW.isProper_q }
    ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G EY.valuation a →
      IsDiscrepancy sX n K_X D_X EX.valuation a' → a' ≤ a := by
  intro EX EY a a' ha ha'
  obtain ⟨-, -, -, ⟨hXn, hYn, -⟩, -, ⟨-, -, hAY⟩, -⟩ := id hM
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : QuasiCompact sW := hWn.1.toQuasiCompact
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace sW
  have hpb := hW.isBirationalMorphism_p
  have hqb := hW.isBirationalMorphism_q
  haveI := hW.isProper_p
  haveI := hW.isProper_q
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hqb.isDominant
  haveI := hXn.1.toIsSeparated
  haveI := hYn.1.toIsSeparated
  haveI := hYn.1.toQuasiCompact
  haveI := hW.isVariety_Z.toIsSeparated
  haveI := DiscrepancyComparison.isSeparated_toTerminal sZ
  have hWp : IsNormalVariety k (p ≫ sX) := hW.comp_p ▸ hWn
  have hWq : IsNormalVariety k (q ≫ sY) := hW.comp_q ▸ hWn
  have KF := DiscrepancyComparison.specMap_fromFunctionField_eq_of_comp_eq φ p q hW.comp_eq
  have hcomm : p ≫ f = q ≫ g :=
    comp_eq_comp_of_specMap_fromFunctionField_eq hW.isModificationOf.2 p q KF
  -- the forms `ω_X`, `ω_Y` with `K_X = div ω_X`, `K_Y = div ω_Y` used in the discrepancies
  obtain ⟨hKXc, hBXc, -, _EX, ωX, _mX, _rX, _LX, -, hωXK, hwX⟩ := id ha'
  obtain ⟨hKYc, hBYc, -, _EY, ωY, _mY, _rY, _LY, -, hωYK, hwY⟩ := id ha
  subst hωXK hωYK
  have hn : topologicalKrullDim X = n := hKXc.topologicalKrullDim_eq
  have htrX := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have htrY := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sY)
    hKYc.topologicalKrullDim_eq
  have hnW : topologicalKrullDim W = n := by
    rw [← toENat_trdeg_functionField (sX := p ≫ sX),
      ← trdeg_functionField_eq_of_bijective sX p hpb.functionFieldMap_bijective,
      toENat_trdeg_functionField (sX := sX), hn]
  have hpω := pullbackRationalPluriForms_ne_zero p hpb.functionFieldMap_bijective htrX hwX.2.2.1
  have hqω := pullbackRationalPluriForms_ne_zero q hqb.functionFieldMap_bijective htrY hwY.2.2.1
  -- `L₁ = div_W(q^*ω_Y) - div_W(p^*ω_X)` is principal
  obtain ⟨L₁, hL₁_def⟩ : ∃ L₁ : Divisor W,
      L₁ = divisorOfForm (pullbackRationalPluriForms sY q ωY) -
        divisorOfForm (pullbackRationalPluriForms sX p ωX) := ⟨_, rfl⟩
  have hL₁ : L₁.LinearlyEquivalent 0 := by
    obtain ⟨φ, hφ⟩ := linearlyEquivalent_divisorOfForm_of_eq
      (hW.comp_q.trans hW.comp_p.symm) hWp hnW hqω hpω
    exact ⟨φ, by rwa [sub_zero, hL₁_def]⟩
  have hL₁c : L₁.IsCartier := Divisor.IsCartier.of_linearlyEquivalent hL₁ Divisor.isCartier_zero
  -- `p^*(K_X + D_X) - q^*(K_Y + G) + L₁ = ∑ (a_Y(P) - a_X(P)) P`
  obtain ⟨G_X, hGX, -⟩ := existsUnique_isRCartierPullback p hBXc
  obtain ⟨G_Y, hGY, -⟩ := existsUnique_isRCartierPullback q hBYc
  -- `a(P, D_X) = ord_P(p^*ω_X) - coeff_P(G_X)` and likewise over `Y`
  set dX := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sX p ωX))
  set dY := Divisor.toRDivisor (divisorOfForm (pullbackRationalPluriForms sY q ωY))
  have haX : ∀ P, IsDiscrepancy sX n (divisorOfForm ωX) D_X
      (ProperDivisorOver.mk ⟨W, p, hWp, hpb, P⟩ inferInstance).valuation
      (dX.coeff P - G_X.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hXn ωX hwX.2.2.1 hKXc hBXc p hWp hpb hGX P
  have haY : ∀ P, IsDiscrepancy sY n (divisorOfForm ωY) G
      (ProperDivisorOver.mk ⟨W, q, hWq, hqb, P⟩ inferInstance).valuation
      (dY.coeff P - G_Y.coeff P) := fun P =>
    isDiscrepancy_ordPullback_sub_coeff_pullback hYn ωY hwY.2.2.1 hKYc hBYc q hWq hqb hGY P
  have hcoeff : ∀ P, (G_X - G_Y + Divisor.toRDivisor L₁).coeff P =
      (dY.coeff P - G_Y.coeff P) - (dX.coeff P - G_X.coeff P) := by
    intro P
    rw [hL₁_def, map_sub]
    simp only [DivisorWithCoeffs.coeff_apply, Finsupp.add_apply, Finsupp.sub_apply]
    ring
  -- `M = q^*(K_Y + G) - L₁` is `p`-nef
  have hL₁r : IsCartierCombination (Divisor.toRDivisor L₁) :=
    ⟨1, fun _ => 1, fun _ => L₁, fun _ => hL₁c, by simp [← toRDivisor_eq_mapCoeffs]⟩
  have hMnef : IsRelativelyNef k sW p (G_Y - Divisor.toRDivisor L₁) :=
    isRelativelyNef_sub_of_isRCartierPullback_of_comp_eq p q hW.comp_q f g hcomm hAY hGY hL₁r
      fun C _ _ _ _ hx => eq_zero_of_isRIntersectionNumber_of_linearlyEquivalent hL₁c hL₁ C hx
  -- the coefficients along prime divisors not exceptional over `X` are nonnegative
  have hBG : ∀ P : Mori.PrimeDivisor W, ¬ IsExceptionalPrimeDivisor sX p P →
      0 ≤ (G_X - G_Y + Divisor.toRDivisor L₁).coeff P := by
    intro P hP
    rw [hcoeff P, sub_nonneg]
    exact hM.isDiscrepancy_le_of_not_isExceptional hW P
      (fun h => hP ⟨hWp, hpb, inferInstance, h⟩) _ _ (haY P) (haX P)
  have hMc := isCartierCombination_sub (isCartierCombination_of_isRCartierPullback hGY) hL₁r
  have hBc := isCartierCombination_add (isCartierCombination_sub
    (isCartierCombination_of_isRCartierPullback hGX)
    (isCartierCombination_of_isRCartierPullback hGY)) hL₁r
  have hnum : IsNumericallyEquivalentOver k sW p G_X
      ((G_Y - Divisor.toRDivisor L₁) + (G_X - G_Y + Divisor.toRDivisor L₁)) := by
    rw [sub_add_add_cancel, add_sub_cancel]
    exact isNumericallyEquivalentOver_self (isCartierCombination_of_isRCartierPullback hGX)
  -- the negativity lemma
  have hB := isEffective_of_isNumericallyEquivalentOver_pullback k sX sW hXn hWn p hW.comp_p hpb
    hBXc hGX hMc hMnef hBc hBG hnum P₀
  rw [hcoeff P₀, sub_nonneg] at hB
  rwa [ha.eq (haY P₀), ha'.eq (haX P₀)]

/-- **FA 2.23.3, the comparison of discrepancies.** Let `g : (Y, D_{𝓕,Y}) ⟶ Z` be a weak log
canonical model of `f : (X, D_X) ⟶ Z` with respect to `𝓕` (`MMP.Flips.IsWeakLogCanonicalModelOf`,
with `G = D_{𝓕,Y}`), through the modification `φ : X ⤏ Y`, over a field of characteristic zero.
Let `B` be a divisor of `k(X) = k(Y)` with nonempty center on `X`. Here `B` is a valuation `v`
of `k(X)` and a valuation `v'` of `k(Y)`, both induced by one valuation `w` of `k(W)` on a common
model `(W, p, q)` of `φ`. Then `B` has nonempty center on `Y` and `a(B, D_{𝓕,Y}) ≥ a(B, D_X)`. -/
@[mmp "thm_fa2_weak_lc_model_discrepancy_ge"]
public theorem IsWeakLogCanonicalModelOf.isDiscrepancy_le {k : Type u} [Field k] [CharZero k]
    {X Y Z W : Scheme.{u}} {sX : X ⟶ Spec (.of k)} {sY : Y ⟶ Spec (.of k)}
    {sZ : Z ⟶ Spec (.of k)} {sW : W ⟶ Spec (.of k)} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] [LocallyOfFiniteType sX] [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormal Y] [CompactSpace Y] [LocallyOfFiniteType sY] [QuasiCompact sY] {n : ℕ}
    {K_X : Mori.Divisor X} {D_X : Mori.RDivisor X} {K_Y : Mori.Divisor Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {φ : X.RationalMap Y} {c : Mori.PrimeDivisor Y → ℝ} {G : Mori.RDivisor Y}
    (hM : IsWeakLogCanonicalModelOf sY sX n K_X D_X K_Y f g φ c G)
    {p : W ⟶ X} {q : W ⟶ Y} (hW : IsCommonModel k sX sY sZ sW f g φ p q)
    {v : Valuation X.functionField ℤᵐ⁰} (hv : HasNonemptyCenter k sX v)
    {v' : Valuation Y.functionField ℤᵐ⁰} :
    haveI : IsIntegral W := hW.isNormalVariety.1.toIsIntegral
    haveI : IsDominant p := hW.isBirationalMorphism_p.isDominant
    haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
    ∀ w : Valuation W.functionField ℤᵐ⁰, w.comap (functionFieldMap p) = v →
      w.comap (functionFieldMap q) = v' →
      HasNonemptyCenter k sY v' ∧
        ∀ a a' : ℝ, IsDiscrepancy sY n K_Y G v' a → IsDiscrepancy sX n K_X D_X v a' → a' ≤ a := by
  have hWn := hW.isNormalVariety
  haveI : IsIntegral W := hWn.1.toIsIntegral
  haveI : IsNormal W := hWn.2
  haveI := hWn.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian sW
  have hpb := hW.isBirationalMorphism_p
  haveI := hW.isProper_p
  haveI : IsDominant p := hpb.isDominant
  haveI : IsDominant q := hW.isBirationalMorphism_q.isDominant
  intro w hwp hwq
  -- `B` is a prime divisor `E` of a model `h : W' ⟶ W`
  obtain ⟨-, D, rfl⟩ := hv
  obtain ⟨D₁, hD₁, -⟩ := ProperDivisorOver.exists_comap_functionFieldMap_valuation_eq
    hW.isVariety_X p (hW.comp_p ▸ hWn.1) hpb D
  have hw : D₁.valuation = w := valuation_eq_of_comap_eq hpb (hD₁.trans hwp.symm)
  haveI := D₁.isIntegral
  haveI := D₁.isNormal
  haveI := D₁.isLocallyNoetherian
  haveI := D₁.isDominant
  haveI := D₁.isProper
  have hW'n : IsNormalVariety k (D₁.f ≫ sW) := by
    rw [← hW.comp_p]
    exact D₁.isNormalVariety
  have hW' := isCommonModel_comp hW D₁.f D₁.isBirationalMorphism hW'n
  have key := isDiscrepancy_le_of_isCommonModel hM hW' D₁.E
  haveI : IsDominant (D₁.f ≫ p) := inferInstance
  haveI : IsDominant (D₁.f ≫ q) := inferInstance
  -- the valuations of `E` over `X` and over `Y` are `v` and `v'`
  have hEX : (D₁.E.valuationOver (D₁.f ≫ p)) = D.valuation := by
    rw [← comap_valuationOver]
    exact hD₁
  have hEY : (D₁.E.valuationOver (D₁.f ≫ q)) = v' := by
    rw [← comap_valuationOver, ← hwq]
    exact congrArg (fun u => u.comap (functionFieldMap q)) hw
  refine ⟨?_, fun a a' ha ha' => key a a' ?_ ?_⟩
  · rw [← hEY]
    exact hasNonemptyCenter_valuation
      { Y := D₁.Y, f := D₁.f ≫ q, isNormalVariety := hW'.comp_q ▸ hW'.isNormalVariety,
        isBirationalMorphism := hW'.isBirationalMorphism_q, E := D₁.E,
        isProper := hW'.isProper_q }
  · rw [← hEY] at ha
    exact ha
  · rw [← hEX] at ha'
    exact ha'

end MMP.Flips

end
