module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.Basic
public import MMP.AlgebraicGeometry.MMP.Models
public import MMP.AlgebraicGeometry.Divisor.LinearSystem
public import MMP.AlgebraicGeometry.Divisor.Pullback
public import MMP.AlgebraicGeometry.MMP.Threefold.Discrepancy
public import MMP.AlgebraicGeometry.MMP.Threefold.Basic
public import MMP.AlgebraicGeometry.Singularities.DivisorOver
public import MMP.AlgebraicGeometry.Morphisms.Birational.TransformBasics
public import Mathlib.AlgebraicGeometry.Limits
public import MMP.AlgebraicGeometry.MMP.Threefold.DiscrepancyComparison
public import MMP.AlgebraicGeometry.Singularities.LocalGenerator
public import MMP.AlgebraicGeometry.Divisor.Canonical.Compatible
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus

/-!
# Canonical divisors and discrepancies: uniqueness and model independence

## Main results

* `MMP.Threefold.Mori.linearlyEquivalent_of_isCanonicalDivisor`: over a perfect field, any two
  canonical divisors of a normal variety are linearly equivalent (Kollár–Mori 0.4/2.25).
* `MMP.Threefold.Mori.isDiscrepancy_eq_of_valuation_eq`: discrepancies depend only on the
  valuation, not on the model (Kollár–Mori 2.25).
* `MMP.Threefold.Mori.IsKltPair.isDltPair`: a klt pair with effective boundary is dlt
  (Kollár–Mori 2.37).

## Implementation notes

Uniqueness of canonical divisors uses only the abstract isomorphism of the restricted divisorial
sheaves: it acts on sections as multiplication by one rational function, whose orders along the
prime divisors (which all meet the smooth locus over a perfect field) give `K - K'`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori Opposite Order

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Threefold.Mori.ModelIndependence

open MMP.Threefold.Mori.Helpers

section Iso

variable {K1 K2 A1 A2 : Type*} [Field K1] [Field K2] [CommRing A1] [CommRing A2]
  [Algebra A1 K1] [Algebra A2 K2] [IsFractionRing A1 K1] [IsFractionRing A2 K2]

/-- If a ring homomorphism `e : K1 →+* K2` of fraction fields maps the image of `A1` onto the image
of `A2`, then it restricts to a bijective ring homomorphism `A1 →+* A2`. -/
theorem exists_ringHom_bijective_of_range (e : K1 →+* K2)
    (h12 : ∀ a1 : A1, ∃ a2 : A2, algebraMap A2 K2 a2 = e (algebraMap A1 K1 a1))
    (h21 : ∀ a2 : A2, ∃ a1 : A1, e (algebraMap A1 K1 a1) = algebraMap A2 K2 a2) :
    ∃ ψ : A1 →+* A2, Function.Bijective ψ ∧
      ∀ a, algebraMap A2 K2 (ψ a) = e (algebraMap A1 K1 a) := by
  choose ψ hψ using h12
  have inj2 : Function.Injective (algebraMap A2 K2) := IsFractionRing.injective A2 K2
  have inj1 : Function.Injective (algebraMap A1 K1) := IsFractionRing.injective A1 K1
  refine ⟨{ toFun := ψ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, hψ⟩
  · apply inj2; rw [hψ]; simp
  · intro a b; apply inj2; rw [hψ]; simp [hψ]
  · apply inj2; rw [hψ]; simp
  · intro a b; apply inj2; rw [hψ]; simp [hψ]
  · refine ⟨fun a b hab => ?_, fun b => ?_⟩
    · apply inj1
      apply e.injective
      change e (algebraMap A1 K1 a) = e (algebraMap A1 K1 b)
      rw [← hψ, ← hψ]
      exact congrArg _ hab
    · obtain ⟨a, ha⟩ := h21 b
      refine ⟨a, inj2 ?_⟩
      change algebraMap A2 K2 (ψ a) = _
      rw [hψ, ha]

end Iso

section Glue

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)}

/-- Two divisors over `X` with the same valuation have isomorphic function fields and local rings
at their prime divisors, compatibly with `f^*` and with the two divisorial valuations. -/
theorem exists_iso_data_of_valuation_eq {D D' : DivisorOver k sX}
    [IsIntegral D.Y] [IsNormal D.Y] [IsLocallyNoetherian D.Y] [IsDominant D.f]
    [IsIntegral D'.Y] [IsNormal D'.Y] [IsLocallyNoetherian D'.Y] [IsDominant D'.f]
    (hv : D.valuation = D'.valuation) :
    ∃ (e : D.Y.functionField →+* D'.Y.functionField) (ψ : D.E.localRing →+* D'.E.localRing),
      (∀ g : X.functionField, e (functionFieldMap D.f g) = functionFieldMap D'.f g) ∧
      (∀ a, algebraMap D'.E.localRing D'.Y.functionField (ψ a) =
        e (algebraMap D.E.localRing D.Y.functionField a)) ∧ Function.Bijective ψ ∧
      ∀ y, D'.E.divisorialValuation (e y) = D.E.divisorialValuation y := by
  have hb1 := D.isBirationalMorphism.functionFieldMap_bijective
  have hb2 := D'.isBirationalMorphism.functionFieldMap_bijective
  let e : D.Y.functionField →+* D'.Y.functionField :=
    (functionFieldMap D'.f).comp (RingEquiv.ofBijective _ hb1).symm.toRingHom
  have he : ∀ g : X.functionField, e (functionFieldMap D.f g) = functionFieldMap D'.f g := by
    intro g
    simp only [e, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    congr 1
    exact (RingEquiv.ofBijective _ hb1).symm_apply_apply g
  have hesurj : Function.Surjective e := by
    intro z
    obtain ⟨g, rfl⟩ := hb2.2 z
    exact ⟨functionFieldMap D.f g, he g⟩
  have hval : ∀ y : D.Y.functionField,
      D'.E.divisorialValuation (e y) = D.E.divisorialValuation y := by
    intro y
    obtain ⟨g, rfl⟩ := hb1.2 y
    rw [he g]
    exact (congrArg (fun w => w g) hv).symm
  have h12 : ∀ a1 : D.E.localRing, ∃ a2 : D'.E.localRing,
      algebraMap D'.E.localRing D'.Y.functionField a2 =
        e (algebraMap D.E.localRing D.Y.functionField a1) := by
    intro a1
    have : D.E.divisorialValuation (algebraMap D.E.localRing D.Y.functionField a1) ≤ 1 :=
      (D.E.divisorialValuation_le_one_iff _).mpr ⟨a1, rfl⟩
    rw [← hval] at this
    exact (D'.E.divisorialValuation_le_one_iff _).mp this
  have h21 : ∀ a2 : D'.E.localRing, ∃ a1 : D.E.localRing,
      e (algebraMap D.E.localRing D.Y.functionField a1) =
        algebraMap D'.E.localRing D'.Y.functionField a2 := by
    intro a2
    obtain ⟨y, hy⟩ := hesurj (algebraMap D'.E.localRing D'.Y.functionField a2)
    have : D.E.divisorialValuation y ≤ 1 := by
      rw [← hval, hy]
      exact (D'.E.divisorialValuation_le_one_iff _).mpr ⟨a2, rfl⟩
    obtain ⟨a1, ha1⟩ := (D.E.divisorialValuation_le_one_iff _).mp this
    exact ⟨a1, by rwa [ha1]⟩
  obtain ⟨ψ, hψb, hψ⟩ := exists_ringHom_bijective_of_range e h12 h21
  exact ⟨e, ψ, he, hψ, hψb, hval⟩

/-- Two divisors over a normal variety with the same valuation give the same order of the
pull-back of any rational pluri-form. -/
theorem ordPullback_eq_of_valuation_eq [PerfectField k] (hX : IsNormalVariety k sX) {n : ℕ}
    (hn : topologicalKrullDim X = n) {D D' : DivisorOver k sX} (hv : D.valuation = D'.valuation)
    {m : ℤ} (τ : RationalPluriForms sX n m) : D.ordPullback τ = D'.ordPullback τ := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D.f ≫ sX) := D.isNormalVariety.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (D'.f ≫ sX) := D'.isNormalVariety.1.toLocallyOfFiniteType
  let := functionFieldAlgebra sX
  let := functionFieldAlgebra (D.f ≫ sX)
  let := functionFieldAlgebra (D'.f ≫ sX)
  let := functionFieldMapAlgebra D.f
  let := functionFieldMapAlgebra D'.f
  have hT1 := isScalarTower_functionFieldMap sX D.f
  have hT2 := isScalarTower_functionFieldMap sX D'.f
  have hb1 := D.isBirationalMorphism.functionFieldMap_bijective
  have hb2 := D'.isBirationalMorphism.functionFieldMap_bijective
  obtain ⟨e, ψ, he, hψ, hψb, hval⟩ := exists_iso_data_of_valuation_eq hv
  let := e.toAlgebra
  have hT3 : IsScalarTower X.functionField D.Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun g => (he g).symm
  have hT4 : IsScalarTower k D.Y.functionField D'.Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change algebraMap k D'.Y.functionField c = e (algebraMap k D.Y.functionField c)
    rw [IsScalarTower.algebraMap_apply k X.functionField D.Y.functionField c,
      IsScalarTower.algebraMap_apply k X.functionField D'.Y.functionField c]
    exact (he _).symm
  have hord : ∀ y : D.Y.functionField,
      D'.Y.ord (e y) D'.E.genericPoint = D.Y.ord y D.E.genericPoint := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [Scheme.ord_zero]
    · have hey : e y ≠ 0 := (map_ne_zero e).mpr hy
      have h1 := hval y
      rw [D'.E.divisorialValuation_eq_exp_neg_ord hey, D.E.divisorialValuation_eq_exp_neg_ord hy,
        WithZero.exp_inj] at h1
      omega
  have hd : (Algebra.trdeg k X.functionField).toNat = n :=
    toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  have hd1 : (Algebra.trdeg k D.Y.functionField).toNat = n := by
    rwa [← trdeg_functionField_eq_of_bijective sX D.f hb1]
  letI := stalkAlgebra (D.f ≫ sX) D.E.genericPoint
  letI := stalkAlgebra (D'.f ≫ sX) D'.E.genericPoint
  haveI := isScalarTower_stalk_functionField (D.f ≫ sX) D.E.genericPoint
  haveI := isScalarTower_stalk_functionField (D'.f ≫ sX) D'.E.genericPoint
  letI : Algebra D.E.localRing D'.E.localRing := ψ.toAlgebra
  letI : Algebra D.E.localRing D'.Y.functionField :=
    ((algebraMap D'.E.localRing D'.Y.functionField).comp ψ).toAlgebra
  have hS1 : IsScalarTower k D.E.localRing D'.E.localRing := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    apply IsFractionRing.injective D'.E.localRing D'.Y.functionField
    change _ = algebraMap D'.E.localRing D'.Y.functionField (ψ (algebraMap k D.E.localRing c))
    rw [hψ, ← IsScalarTower.algebraMap_apply k D.E.localRing D.Y.functionField c,
      ← IsScalarTower.algebraMap_apply k D'.E.localRing D'.Y.functionField c]
    exact IsScalarTower.algebraMap_apply k D.Y.functionField D'.Y.functionField c
  have hS2 : IsScalarTower D.E.localRing D'.E.localRing D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hS3 : IsScalarTower D.E.localRing D.Y.functionField D'.Y.functionField :=
    IsScalarTower.of_algebraMap_eq hψ
  have hS4 : IsScalarTower k D.E.localRing D'.Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change _ = algebraMap D'.E.localRing D'.Y.functionField (ψ (algebraMap k D.E.localRing c))
    rw [IsScalarTower.algebraMap_apply k D'.E.localRing D'.Y.functionField c,
      IsScalarTower.algebraMap_apply k D.E.localRing D'.E.localRing c]
    rfl
  obtain ⟨ω0, hω0⟩ := exists_isPullbackGenerator_of_bijective sX D.f hb1 hd
  obtain ⟨ω0', hω0'⟩ := exists_isPullbackGenerator_of_bijective sX D'.f hb2 hd
  have hω0_2 : IsPullbackGenerator D'.Y.functionField ω0 :=
    IsPullbackGenerator.of_span hω0' hω0.1 hω0.ne_zero
  have hωb : IsPullbackGenerator D'.Y.functionField
      (topFormsMap k X.functionField D.Y.functionField n ω0) := by
    refine ⟨hω0.2.1, ?_, ?_⟩
    · rw [topFormsMap_comp]; exact hω0_2.2.1
    · rw [topFormsMap_comp]; exact hω0_2.2.2
  obtain ⟨σ, hσ, h0σ⟩ := D.E.exists_topForms_generator (sX := D.f ≫ sX) hd1
  have hωT : IsPullbackGenerator D'.Y.functionField
      (topFormsMap k D.E.localRing D.Y.functionField n σ) :=
    IsPullbackGenerator.of_span hωb (span_singleton_topFormsMap (nonZeroDivisors _) hσ) h0σ
  have key := ordAt_pullbackForms_eq (k := k) (K := D.Y.functionField) (K' := D'.Y.functionField)
    (A := D.E.localRing) (A' := D'.E.localRing) (d := n) (m := m) hψb
    (v := fun y => D.Y.ord y D.E.genericPoint) (v' := fun y => D'.Y.ord y D'.E.genericPoint)
    (fun x y hx hy => D.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D.E.ord_algebraMap_of_isUnit ha)
    (fun x y hx hy => D'.E.ord_mul_of_ne_zero x y hx hy)
    (fun a ha => D'.E.ord_algebraMap_of_isUnit ha)
    hord hσ hωT (pullbackForms (K' := D.Y.functionField) m τ)
  calc D.ordPullback τ
      = ordAt D.E.localRing (fun y => D.Y.ord y D.E.genericPoint)
          (pullbackForms (K' := D.Y.functionField) m τ) := rfl
    _ = ordAt D'.E.localRing (fun y => D'.Y.ord y D'.E.genericPoint)
          (pullbackForms (K' := D'.Y.functionField) m
            (pullbackForms (K' := D.Y.functionField) m τ)) := key.symm
    _ = ordAt D'.E.localRing (fun y => D'.Y.ord y D'.E.genericPoint)
          (pullbackForms (K' := D'.Y.functionField) m τ) := by
        rw [pullbackForms_comp hω0 hωb τ]
    _ = D'.ordPullback τ := rfl

end Glue

section EqOfCenter

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)}

/-- Two discrepancies of divisors with the same valuation and the same center coincide. -/
theorem isDiscrepancy_eq_of_center_eq [PerfectField k] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}
    {D D' : DivisorOver k sX} (hv : D.valuation = D'.valuation)
    (hcen : D.f D.E.genericPoint = D'.f D'.E.genericPoint) {a a' : ℚ}
    (ha : IsDiscrepancy sX n K Δ D a) (ha' : IsDiscrepancy sX n K Δ D' a') : a = a' := by
  obtain ⟨hX, hK, m, hm, -, U, hU, τ, hτ, hτa⟩ := ha
  obtain ⟨-, -, m', hm', -, U', hU', τ', hτ', hτa'⟩ := ha'
  rw [← hcen] at hU'
  have hn := hK.topologicalKrullDim_eq
  rw [← ordPullback_eq_of_valuation_eq hX hn hv τ'] at hτa'
  let := functionFieldAlgebra sX
  have := D.isIntegral
  have := D.isLocallyNoetherian
  have := D.isNormal
  have := D.isDominant
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨b, N, hN⟩ := D.exists_ordPullback_eq hX hn
  set c := (ZTensorPower.basis b m).repr τ ()
  set c' := (ZTensorPower.basis b m').repr τ' ()
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hτ.1
  have hc' : c' ≠ 0 := repr_ne_zero_of_ne_zero b hτ'.1
  set g : X.functionField := c ^ (m' : ℤ) * c' ^ (-(m : ℤ)) with hg_def
  have hg : g ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (zpow_ne_zero _ hc')
  have hord : ∀ Γ : MMP.Mori.PrimeDivisor X, D.f D.E.genericPoint ∈ Γ.support →
      X.ord g Γ.genericPoint = 0 := by
    intro Γ hΓ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    have e1 := hτ.2 Γ ⟨_, hΓ, hU⟩
    have e2 := hτ'.2 Γ ⟨_, hΓ, hU'⟩
    have f1 : (Γ.ordForm τ : ℚ) = (X.ord c Γ.genericPoint : ℚ) + m * NΓ := by
      exact_mod_cast hNΓ m τ hτ.1
    have f2 : (Γ.ordForm τ' : ℚ) = (X.ord c' Γ.genericPoint : ℚ) + m' * NΓ := by
      exact_mod_cast hNΓ m' τ' hτ'.1
    rw [hg_def, Scheme.ord_mul (zpow_ne_zero _ hc) (zpow_ne_zero _ hc'), ord_zpow _ hc,
      ord_zpow _ hc']
    have : ((m' : ℚ) * X.ord c Γ.genericPoint + -(m : ℚ) * X.ord c' Γ.genericPoint) = 0 := by
      linear_combination (m' : ℚ) * e1 - (m : ℚ) * e2 - (m' : ℚ) * f1 + (m : ℚ) * f2
    exact_mod_cast this
  obtain ⟨u, hu, hug⟩ := exists_isUnit_algebraMap_stalk_eq_of_forall_ord_eq_zero _ hg hord
  have hY0 : D.Y.ord (functionFieldMap D.f g) D.E.genericPoint = 0 := by
    rw [← hug, functionFieldMap_algebraMap_stalk]
    exact D.E.ord_algebraMap_of_isUnit (hu.map _)
  have hfc : functionFieldMap D.f c ≠ 0 := (map_ne_zero _).mpr hc
  have hfc' : functionFieldMap D.f c' ≠ 0 := (map_ne_zero _).mpr hc'
  rw [hg_def, map_mul, map_zpow₀, map_zpow₀,
    Scheme.ord_mul (zpow_ne_zero _ hfc) (zpow_ne_zero _ hfc'), ord_zpow _ hfc, ord_zpow _ hfc']
    at hY0
  have hY0' : ((m' : ℚ) * D.Y.ord (functionFieldMap D.f c) D.E.genericPoint +
      -(m : ℚ) * D.Y.ord (functionFieldMap D.f c') D.E.genericPoint) = 0 := by
    exact_mod_cast hY0
  have h1 : (D.ordPullback τ : ℚ) =
      (D.Y.ord (functionFieldMap D.f c) D.E.genericPoint : ℚ) + m * N := by
    exact_mod_cast hN m τ hτ.1
  have h2 : (D.ordPullback τ' : ℚ) =
      (D.Y.ord (functionFieldMap D.f c') D.E.genericPoint : ℚ) + m' * N := by
    exact_mod_cast hN m' τ' hτ'.1
  have key : (m : ℚ) * m' * (a - a') = 0 := by
    linear_combination (m' : ℚ) * hτa - (m : ℚ) * hτa' + (m' : ℚ) * h1 - (m : ℚ) * h2 + hY0'
  have hm0 : (m : ℚ) * m' ≠ 0 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hm0)

end EqOfCenter

section CenterEq2

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  {sX : X ⟶ Spec (.of k)}

/-- **The center of a divisor over `X` depends only on its valuation** (separatedness of `X`). -/
theorem center_eq_of_valuation_eq (hX : IsNormalVariety k sX) {D D' : DivisorOver k sX}
    (hv : D.valuation = D'.valuation) : D.f D.E.genericPoint = D'.f D'.E.genericPoint := by
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := D'.isIntegral
  have := D'.isNormal
  have := D'.isLocallyNoetherian
  have := D'.isDominant
  have : IsSeparated sX := hX.1.toIsSeparated
  obtain ⟨ε, ψ', hε, hψ', hψb, -⟩ := exists_iso_data_of_valuation_eq hv.symm
  have hηE : genericPoint D.Y ⤳ D.E.genericPoint := (genericPoint_spec _).specializes trivial
  have hηE' : genericPoint D'.Y ⤳ D'.E.genericPoint := (genericPoint_spec _).specializes trivial
  let ι : Spec (D.Y.presheaf.stalk (genericPoint D.Y)) ⟶
      Spec (D.Y.presheaf.stalk D.E.genericPoint) :=
    Spec.map (D.Y.presheaf.stalkSpecializes hηE)
  haveI : IsDominant ι :=
    isDominant_Spec_map_of_injective _ (IsFractionRing.injective D.E.localRing D.Y.functionField)
  let ℓ1 : Spec D.E.localRing ⟶ X := D.Y.fromSpecStalk D.E.genericPoint ≫ D.f
  let ℓ2 : Spec D.E.localRing ⟶ X := Spec.map (CommRingCat.ofHom ψ') ≫
    D'.Y.fromSpecStalk D'.E.genericPoint ≫ D'.f
  have key1 : ι ≫ ℓ1 = D.Y.fromSpecStalk (genericPoint D.Y) ≫ D.f := by
    simp only [ι, ℓ1]
    rw [← Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have key2 : ι ≫ ℓ2 = Spec.map (CommRingCat.ofHom ε) ≫
      D'.Y.fromSpecStalk (genericPoint D'.Y) ≫ D'.f := by
    have hcomm : CommRingCat.ofHom ψ' ≫ D.Y.presheaf.stalkSpecializes hηE =
        D'.Y.presheaf.stalkSpecializes hηE' ≫ CommRingCat.ofHom ε := by
      ext a
      exact hψ' a
    have h2 : ι ≫ Spec.map (CommRingCat.ofHom ψ') =
        Spec.map (CommRingCat.ofHom ε) ≫ Spec.map (D'.Y.presheaf.stalkSpecializes hηE') := by
      simp only [ι]
      have := congrArg Spec.map hcomm
      refine (Eq.trans ?_ this).trans (Spec.map_comp _ _)
      exact (Spec.map_comp _ _).symm
    simp only [ℓ2]
    rw [← Category.assoc, h2, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
  have hU : ι ≫ ℓ1 = ι ≫ ℓ2 := by
    rw [key1, key2, ← functionFieldMap_fromSpecStalk D.f, ← functionFieldMap_fromSpecStalk D'.f,
      ← Category.assoc]
    have hring : CommRingCat.ofHom (functionFieldMap D'.f) ≫ CommRingCat.ofHom ε =
        CommRingCat.ofHom (functionFieldMap D.f) := by
      ext g
      exact hε g
    have := congrArg Spec.map hring
    simp only [Spec.map_comp] at this
    rw [this]
  have hs : ℓ1 ≫ sX = ℓ2 ≫ sX := by
    refine ext_of_isDominant_of_isSeparated
      (Limits.terminal.from (Spec (.of k)))
      (Limits.terminal.hom_ext _ _) ι ?_
    simpa only [Category.assoc] using hU =≫ sX
  have hℓ : ℓ1 = ℓ2 := ext_of_isDominant_of_isSeparated sX hs ι hU
  have hloc : IsLocalHom ψ' := by
    refine ⟨fun a ha => ?_⟩
    have h : IsUnit ((RingEquiv.ofBijective ψ' hψb).symm (ψ' a)) :=
      IsUnit.map (RingEquiv.ofBijective ψ' hψb).symm ha
    have h2 : (RingEquiv.ofBijective ψ' hψb).symm (ψ' a) = a :=
      (RingEquiv.ofBijective ψ' hψb).symm_apply_apply a
    rwa [h2] at h
  let cp : Spec (D.Y.presheaf.stalk D.E.genericPoint) :=
    IsLocalRing.closedPoint (D.Y.presheaf.stalk D.E.genericPoint)
  have e1 : ℓ1 cp = D.f D.E.genericPoint := by
    change (D.Y.fromSpecStalk D.E.genericPoint ≫ D.f) _ = _
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  have e2 : ℓ2 cp = D'.f D'.E.genericPoint := by
    change (Spec.map (CommRingCat.ofHom ψ') ≫ D'.Y.fromSpecStalk D'.E.genericPoint ≫ D'.f) _ = _
    have : IsLocalHom (CommRingCat.ofHom ψ').hom := hloc
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Spec_closedPoint,
      Scheme.fromSpecStalk_closedPoint]
  rw [← e1, ← e2, hℓ]

end CenterEq2

end MMP.Threefold.Mori.ModelIndependence

namespace MMP.Threefold.Mori

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
  {Δ : QDivisor X}

/-- **`a(E, X, Δ)` depends only on the valuation of `E`.** If `(Y, f, E)` and `(Y', f', E')` are
divisors over the pair `(X, Δ)` with the same valuation `v(E, Y) = v(E', Y')`, then the
discrepancies computed for `E` and for `E'`, with any data `(m, U, τ)` and `(m', U', τ')`,
coincide. -/
@[mmp "lem_km2b_discrepancy_independent_of_model"]
theorem isDiscrepancy_eq_of_valuation_eq (hΔ : IsPairWith sX n K Δ) {D D' : DivisorOver k sX}
    (hv : D.valuation = D'.valuation) {a a' : ℚ} (ha : IsDiscrepancy sX n K Δ D a)
    (ha' : IsDiscrepancy sX n K Δ D' a') : a = a' :=
  ModelIndependence.isDiscrepancy_eq_of_center_eq hv
    (ModelIndependence.center_eq_of_valuation_eq hΔ.1 hv) ha ha'

end MMP.Threefold.Mori

namespace MMP.Threefold.Mori.CanonUniq

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {U : X.Opens} {D D' : Divisor X}

/-- The additive map on sections of `𝒪_X(D)` over the image of `V` induced by an isomorphism of
the restrictions of `𝒪_X(D)` and `𝒪_X(D')` to `U`. -/
def phi (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    (V : U.toScheme.Opens) :
    D.divisorialSubmodule (U.ι ''ᵁ V) →+ D'.divisorialSubmodule (U.ι ''ᵁ V) :=
  (e.hom.app V).hom

/-- `phi e V` is linear over the sections of `𝒪_X` over the image of `V`. -/
theorem phi_smul (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    (V : U.toScheme.Opens)
    (r : Γ(X, U.ι ''ᵁ V)) (s : D.divisorialSubmodule (U.ι ''ᵁ V)) :
    phi e V (r • s) = r • phi e V s := by
  have h := Scheme.Modules.Hom.app_smul e.hom ((U.ι.appIso V).hom r) (U := V)
    (show Γ(D.divisorialSheaf.restrict U.ι, V) from s)
  have hr : (U.ι.appIso V).inv ((U.ι.appIso V).hom r) = r := Iso.hom_inv_id_apply _ _
  have e1 : ((U.ι.appIso V).hom r • (show Γ(D.divisorialSheaf.restrict U.ι, V) from s) :
      Γ(D.divisorialSheaf.restrict U.ι, V)) = (r • s : D.divisorialSubmodule (U.ι ''ᵁ V)) := by
    conv_rhs => rw [← hr]
    rfl
  have e2 : ((U.ι.appIso V).hom r •
      (e.hom.app V).hom (show Γ(D.divisorialSheaf.restrict U.ι, V) from s) :
      Γ(D'.divisorialSheaf.restrict U.ι, V)) =
      (r • phi e V s : D'.divisorialSubmodule (U.ι ''ᵁ V)) := by
    conv_rhs => rw [← hr]
    rfl
  rwa [e1, e2] at h

/-- `phi e` commutes with restriction of sections from `V` to `V' ≤ V`. -/
theorem phi_res (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    {V V' : U.toScheme.Opens} (h : V' ≤ V) (s : D.divisorialSubmodule (U.ι ''ᵁ V)) :
    phi e V' (D.divisorialRestrict (homOfLE (Scheme.Hom.image_mono _ h)) s) =
      D'.divisorialRestrict (homOfLE (Scheme.Hom.image_mono _ h)) (phi e V s) := by
  have := e.hom.mapPresheaf.naturality (homOfLE h).op
  exact congr($(this) (show Γ(D.divisorialSheaf.restrict U.ι, V) from s))

section Integral

variable [IsIntegral X]

/-- Every irreducible component of an integral scheme is the whole space. -/
theorem component_eq_univ (Z : irreducibleComponents X) : Z.1 = Set.univ :=
  (irreducibleComponents_eq_singleton (X := X) ▸ Z.2 : Z.1 ∈ ({Set.univ} : Set (Set X)))

/-- On an integral scheme, the generic point of any irreducible component lies in every nonempty
open. -/
theorem componentGenericPoint_mem {O : X.Opens} (hO : (O : Set X).Nonempty)
    (Z : irreducibleComponents X) : componentGenericPoint X Z ∈ O := by
  rw [genericPoint_mem_iff, component_eq_univ]
  simpa using hO

end Integral

section Psi

/-- The section `1` of `𝒪_X(D)` over `W`, when `D` has coefficient `0` along every prime divisor
meeting `W`. -/
def oneSection (D : Divisor X) (W : X.Opens)
    (hD : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ (W : Set X)).Nonempty → D.coeff Γ = 0) :
    D.divisorialSubmodule W :=
  ⟨fun _ => 1, fun E h => Or.inr (by
    change WithZero.exp _ ≤ E.valuation 1
    rw [map_one, hD E h, neg_zero, WithZero.exp_zero])⟩

variable [IsIntegral X]

/-- The rational function `ψ` by which the isomorphism acts. -/
def psi (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    (V₀ : U.toScheme.Opens) (hV₀ : (V₀ : Set U).Nonempty)
    (hD : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ ((U.ι ''ᵁ V₀ : X.Opens) : Set X)).Nonempty →
      D.coeff Γ = 0) :
    RationalFunctions X := fun Z =>
  (phi e V₀ (oneSection D _ hD)).1 ⟨Z, componentGenericPoint_mem (by
    obtain ⟨y, hy⟩ := hV₀
    exact ⟨U.ι y, y, hy, rfl⟩) Z⟩

/-- `phi e V` acts on every section of `𝒪_X(D)` as multiplication by the rational function
`psi e V₀ hV₀ hD`. -/
theorem phi_apply_eq (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    (V₀ : U.toScheme.Opens) (hV₀ : (V₀ : Set U).Nonempty)
    (hD : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ ((U.ι ''ᵁ V₀ : X.Opens) : Set X)).Nonempty →
      D.coeff Γ = 0)
    (V : U.toScheme.Opens) (s : D.divisorialSubmodule (U.ι ''ᵁ V))
    (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}) :
    (phi e V s).1 Z = psi e V₀ hV₀ hD Z.1 * s.1 Z := by
  obtain ⟨Z, hZ⟩ := Z
  obtain ⟨y, hyV, hyx⟩ := hZ
  obtain ⟨A, hxA, r, hr⟩ := X.presheaf.exists_germ_eq (s.1 ⟨Z, ⟨y, hyV, hyx⟩⟩)
  obtain ⟨z, hz, hzx⟩ : componentGenericPoint X Z ∈ U.ι ''ᵁ V₀ :=
    componentGenericPoint_mem (by obtain ⟨y0, hy0⟩ := hV₀; exact ⟨U.ι y0, y0, hy0, rfl⟩) Z
  have hzy : z = y := U.ι.isOpenEmbedding.injective (hzx.trans hyx.symm)
  subst hzy
  let V₂ : U.toScheme.Opens := V ⊓ V₀ ⊓ U.ι ⁻¹ᵁ A
  have hyV₂ : z ∈ V₂ := ⟨⟨hyV, hz⟩, by
    change U.ι z ∈ A
    have h : U.ι z = componentGenericPoint X Z := hzx
    rwa [h]⟩
  have h2V : V₂ ≤ V := inf_le_left.trans inf_le_left
  have h20 : V₂ ≤ V₀ := inf_le_left.trans inf_le_right
  have h2A : U.ι ''ᵁ V₂ ≤ A := by
    rintro w ⟨v, hv, rfl⟩
    exact hv.2
  let i1 : U.ι ''ᵁ V₂ ⟶ U.ι ''ᵁ V := homOfLE (Scheme.Hom.image_mono _ h2V)
  let i0 : U.ι ''ᵁ V₂ ⟶ U.ι ''ᵁ V₀ := homOfLE (Scheme.Hom.image_mono _ h20)
  let iA : U.ι ''ᵁ V₂ ⟶ A := homOfLE h2A
  let r₂ : Γ(X, U.ι ''ᵁ V₂) := X.presheaf.map iA.op r
  have hxV₂ : componentGenericPoint X Z ∈ U.ι ''ᵁ V₂ := ⟨z, hyV₂, hzx⟩
  have key : D.divisorialRestrict i1 s = r₂ • D.divisorialRestrict i0 (oneSection D _ hD) := by
    refine Subtype.ext (funext fun Z' => ?_)
    obtain ⟨Z', hZ'⟩ := Z'
    have hZZ : Z' = Z := Subtype.ext (by rw [component_eq_univ, component_eq_univ])
    subst hZZ
    rw [Submodule.coe_smul, rationalFunctions_smul_apply]
    change s.1 ⟨Z', _⟩ = _ * 1
    rw [mul_one]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iA _ hZ' r).trans hr |>.symm
  have h1 := phi_res e h2V s
  have h0 := phi_res e h20 (oneSection D _ hD)
  have h3 : D'.divisorialRestrict i1 (phi e V s) =
      r₂ • D'.divisorialRestrict i0 (phi e V₀ (oneSection D _ hD)) := by
    rw [← h1, key, phi_smul]
    congr 1
  have h4 := congrArg (fun t => t.1 ⟨Z, hxV₂⟩) h3
  simp only [Submodule.coe_smul] at h4
  rw [rationalFunctions_smul_apply] at h4
  have hg : (X.presheaf.germ (U.ι ''ᵁ V₂) (componentGenericPoint X Z) hxV₂).hom r₂ =
      s.1 ⟨Z, ⟨z, hyV, hzx⟩⟩ :=
    (TopCat.Presheaf.germ_res_apply X.presheaf iA _ hxV₂ r).trans hr
  rw [hg] at h4
  exact h4.trans (mul_comm _ _)

end Psi

section Geometry

variable [IsIntegral X]

/-- The generic point of an integral scheme lies on no prime divisor. -/
theorem genericPoint_notMem_support (E : MMP.Mori.PrimeDivisor X) :
    genericPoint X ∉ E.support := by
  intro h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at h
  have h3 : genericPoint X = E.genericPoint :=
    ((genericPoint_specializes _).antisymm (specializes_iff_mem_closure.mpr h)).eq
  have := E.coheight_genericPoint
  rw [← h3, coheight_eq_zero.mpr fun y _ => genericPoint_specializes y] at this
  exact absurd this (by decide)

/-- The generic point of a prime divisor `Γ` does not lie on a different prime divisor `E`. -/
theorem genericPoint_notMem_support_of_ne {Γ E : MMP.Mori.PrimeDivisor X} (h : Γ ≠ E) :
    Γ.genericPoint ∉ E.support := by
  intro hE
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
  have hle : Γ.genericPoint ≤ E.genericPoint := specializes_iff_mem_closure.mpr hE
  by_contra hne
  have hlt : Γ.genericPoint < E.genericPoint := lt_of_le_not_ge hle fun h' =>
    h (AlgebraicGeometry.PrimeDivisor.genericPoint_injective
      (Specializes.antisymm (show Γ.genericPoint ⤳ E.genericPoint from h')
        (show E.genericPoint ⤳ Γ.genericPoint from hle)).eq)
  have h2 := Order.coheight_add_one_le hlt
  rw [AlgebraicGeometry.PrimeDivisor.coheight_genericPoint,
    AlgebraicGeometry.PrimeDivisor.coheight_genericPoint] at h2
  exact absurd h2 (by decide)

/-- For every prime divisor `Γ` and integer `m` there is a unit rational function of order `m`
along `Γ`. -/
theorem exists_unit_ord (Γ : MMP.Mori.PrimeDivisor X) (m : ℤ) :
    ∃ g : (RationalFunctions X)ˣ, Γ.ord g = m := by
  have := Γ.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Γ.localRing
  have hv := Γ.valuation_toComponent_of_irreducible hϖ
  have ha0 : Γ.toComponent.hom ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  have hfield := RationalFunctions.isField_stalk X Γ.component
  obtain ⟨b, hb⟩ := hfield.mul_inv_cancel ha0
  let u : (X.presheaf.stalk (componentGenericPoint X Γ.component))ˣ :=
    ⟨Γ.toComponent.hom ϖ, b, hb, by rw [mul_comm]; exact hb⟩
  have hZ : ∀ Z : irreducibleComponents X, Z = Γ.component := fun Z =>
    Subtype.ext (by rw [component_eq_univ, component_eq_univ])
  let f : ∀ Z : irreducibleComponents X, (X.presheaf.stalk (componentGenericPoint X Z))ˣ :=
    fun Z => Eq.rec (motive := fun Z _ => (X.presheaf.stalk (componentGenericPoint X Z))ˣ) u
      (hZ Z).symm
  let φ : (RationalFunctions X)ˣ := (RationalFunctions.unitsEquiv X).symm f
  have hφ : (φ : RationalFunctions X) Γ.component = Γ.toComponent.hom ϖ := rfl
  have h1 : Γ.ord φ = 1 := Γ.ord_eq_one_of_irreducible hϖ hφ.symm
  exact ⟨φ ^ m, by rw [Γ.ord_zpow, h1]; simp⟩

/-- If `U` contains the generic point of every prime divisor and `phi e` acts as multiplication by
the unit `ψ`, then `D.coeff Γ - D'.coeff Γ ≤ Γ.ord ψ` for every prime divisor `Γ`. -/
theorem ord_ge_of_phi [CompactSpace X]
    (hU : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ U)
    (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    (ψ : (RationalFunctions X)ˣ)
    (hL1 : ∀ (V : U.toScheme.Opens) (s : D.divisorialSubmodule (U.ι ''ᵁ V))
      (Z : {Z : irreducibleComponents X // componentGenericPoint X Z ∈ U.ι ''ᵁ V}),
      (phi e V s).1 Z = (ψ : RationalFunctions X) Z.1 * s.1 Z)
    (Γ : MMP.Mori.PrimeDivisor X) : D.coeff Γ - D'.coeff Γ ≤ Γ.ord ψ := by
  classical
  obtain ⟨g, hg⟩ := exists_unit_ord Γ (-D.coeff Γ)
  let T : Set (MMP.Mori.PrimeDivisor X) := {E | E ≠ Γ ∧ (E.ord g ≠ 0 ∨ D.coeff E ≠ 0)}
  have hTfin : T.Finite := by
    refine ((finite_ord_ne_zero g).union D.support.finite_toSet).subset ?_
    intro E ⟨_, hE⟩
    rcases hE with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [DivisorWithCoeffs.coeff_apply] using h)
  let C : Set X := ⋃ E ∈ T, (E.support : Set X)
  have hC : IsClosed C := hTfin.isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed
  let O : X.Opens := ⟨Cᶜ, hC.isOpen_compl⟩
  let VΓ : U.toScheme.Opens := U.ι ⁻¹ᵁ O
  have hγO : Γ.genericPoint ∈ O := by
    intro hmem
    obtain ⟨E, hET, hE⟩ := Set.mem_iUnion₂.mp hmem
    exact genericPoint_notMem_support_of_ne (Ne.symm hET.1) hE
  have hγV : (⟨Γ.genericPoint, hU Γ⟩ : U) ∈ VΓ := hγO
  have hγW : Γ.genericPoint ∈ U.ι ''ᵁ VΓ := ⟨⟨Γ.genericPoint, hU Γ⟩, hγV, rfl⟩
  have hmem : ∀ E : MMP.Mori.PrimeDivisor X,
      (E.support ∩ ((U.ι ''ᵁ VΓ : X.Opens) : Set X)).Nonempty → E ≠ Γ →
        E.ord g = 0 ∧ D.coeff E = 0 := by
    intro E ⟨x, hxE, hxW⟩ hEΓ
    obtain ⟨v, hv, rfl⟩ := hxW
    by_contra hcon
    have hET : E ∈ T := ⟨hEΓ, by
      by_cases h : E.ord g = 0
      · exact Or.inr fun h' => hcon ⟨h, h'⟩
      · exact Or.inl h⟩
    exact hv (Set.mem_biUnion hET hxE)
  let sec : D.divisorialSubmodule (U.ι ''ᵁ VΓ) :=
    ⟨fun Z => (g : RationalFunctions X) Z.1, fun E h => by
      by_cases hEΓ : E = Γ
      · subst hEΓ
        refine Or.inr ?_
        change WithZero.exp _ ≤ E.valuation ((g : RationalFunctions X) E.component)
        rw [E.valuation_component, hg]
      · obtain ⟨h1, h2⟩ := hmem E h hEΓ
        refine Or.inr ?_
        change WithZero.exp _ ≤ E.valuation ((g : RationalFunctions X) E.component)
        rw [E.valuation_component, h1, h2]
        simp⟩
  have hγE : Γ.genericPoint ∈ Γ.support := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]; exact subset_closure rfl
  have ht := (phi e VΓ sec).2 Γ ⟨Γ.genericPoint, hγE, hγW⟩
  have hL := hL1 VΓ sec ⟨Γ.component, Γ.componentGenericPoint_mem_of_nonempty
    ⟨Γ.genericPoint, hγE, hγW⟩⟩
  rcases ht with h0 | hle
  · exfalso
    change (phi e VΓ sec).1 ⟨Γ.component, _⟩ = 0 at h0
    rw [hL] at h0
    have hu : IsUnit ((ψ * g : (RationalFunctions X)ˣ) : RationalFunctions X) := Units.isUnit _
    have hu' := hu.map (RationalFunctions.component X Γ.component)
    change IsUnit ((ψ : RationalFunctions X) Γ.component *
      (g : RationalFunctions X) Γ.component) at hu'
    exact hu'.ne_zero h0
  · change WithZero.exp _ ≤ Γ.valuation ((phi e VΓ sec).1 ⟨Γ.component, _⟩) at hle
    rw [hL] at hle
    change WithZero.exp _ ≤
      Γ.valuation (((ψ * g : (RationalFunctions X)ˣ) : RationalFunctions X) Γ.component) at hle
    rw [Γ.valuation_component, WithZero.exp_le_exp, PrimeDivisor.ord_mul, hg] at hle
    omega

end Geometry

/-- `phi e.symm V` is a left inverse of `phi e V`. -/
theorem phi_symm_phi (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    (V : U.toScheme.Opens) (s : D.divisorialSubmodule (U.ι ''ᵁ V)) :
    phi e.symm V (phi e V s) = s :=
  congrArg (fun φ => (Scheme.Modules.Hom.app φ V).hom
    (show Γ(D.divisorialSheaf.restrict U.ι, V) from s)) e.hom_inv_id

/-- On an integral scheme, the generic point of any irreducible component is the generic point. -/
theorem componentGenericPoint_eq [IsIntegral X] (Z : irreducibleComponents X) :
    componentGenericPoint X Z = genericPoint X := by
  have h1 := isGenericPoint_componentGenericPoint X Z
  rw [component_eq_univ] at h1
  exact h1.eq (genericPoint_spec X)

/-- The rational functions attached to `e` and to `e.symm` are mutually inverse. -/
theorem psi_mul [IsIntegral X]
    (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι)
    (V₀ : U.toScheme.Opens) (hV₀ : (V₀ : Set U).Nonempty)
    (hD : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ ((U.ι ''ᵁ V₀ : X.Opens) : Set X)).Nonempty →
      D.coeff Γ = 0)
    (hD' : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ ((U.ι ''ᵁ V₀ : X.Opens) : Set X)).Nonempty →
      D'.coeff Γ = 0)
    (Z : irreducibleComponents X) :
    psi e.symm V₀ hV₀ hD' Z * psi e V₀ hV₀ hD Z = 1 := by
  have hm : componentGenericPoint X Z ∈ U.ι ''ᵁ V₀ :=
    componentGenericPoint_mem (by obtain ⟨y, hy⟩ := hV₀; exact ⟨U.ι y, y, hy, rfl⟩) Z
  have h := phi_apply_eq e.symm V₀ hV₀ hD' V₀ (phi e V₀ (oneSection D _ hD)) ⟨Z, hm⟩
  rw [phi_symm_phi] at h
  exact h.symm

/-- If `U` contains the generic point of every prime divisor and the restrictions of `𝒪_X(D)` and
`𝒪_X(D')` to `U` are isomorphic, then `D` and `D'` are linearly equivalent. -/
theorem linearlyEquivalent_of_iso [IsIntegral X] [CompactSpace X]
    (hU : ∀ Γ : MMP.Mori.PrimeDivisor X, Γ.genericPoint ∈ U)
    (e : D.divisorialSheaf.restrict U.ι ≅ D'.divisorialSheaf.restrict U.ι) :
    D.LinearlyEquivalent D' := by
  by_cases hUe : (U : Set X).Nonempty
  swap
  · refine ⟨1, ?_⟩
    ext E
    exact absurd (hU E) (fun h => hUe ⟨_, h⟩)
  obtain ⟨u, hu⟩ := hUe
  have hηU : genericPoint X ∈ U := by
    have hZ : Nonempty (irreducibleComponents X) := ⟨⟨Set.univ, by
      rw [irreducibleComponents_eq_singleton]; rfl⟩⟩
    obtain ⟨Z⟩ := hZ
    rw [← componentGenericPoint_eq Z]
    exact componentGenericPoint_mem ⟨u, hu⟩ Z
  let O₀ : X.Opens := ⟨((D.supp ⊔ D'.supp : TopologicalSpace.Closeds X) : Set X)ᶜ,
    (D.supp ⊔ D'.supp).isClosed.isOpen_compl⟩
  let V₀ : U.toScheme.Opens := U.ι ⁻¹ᵁ O₀
  have hηO : genericPoint X ∉ ((D.supp ⊔ D'.supp : TopologicalSpace.Closeds X) : Set X) := by
    intro h
    have h' : genericPoint X ∈ (D.supp : Set X) ∪ (D'.supp : Set X) := by simpa using h
    rcases h' with h | h
    · obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
      exact genericPoint_notMem_support E hE
    · obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
      exact genericPoint_notMem_support E hE
  have hV₀ : (V₀ : Set U).Nonempty := ⟨⟨genericPoint X, hηU⟩, hηO⟩
  have hDD : ∀ (F : Divisor X), F.supp ≤ D.supp ⊔ D'.supp →
      ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ ((U.ι ''ᵁ V₀ : X.Opens) : Set X)).Nonempty →
        F.coeff Γ = 0 := by
    intro F hF Γ ⟨x, hxΓ, v, hv, hvx⟩
    by_contra hne
    have hxC : x ∈ ((D.supp ⊔ D'.supp : TopologicalSpace.Closeds X) : Set X) :=
      hF (DivisorWithCoeffs.support_subset_supp hne hxΓ)
    have hvC : U.ι v ∈ ((D.supp ⊔ D'.supp : TopologicalSpace.Closeds X) : Set X) := by
      have h : U.ι v = x := hvx
      rwa [h]
    exact hv hvC
  have hD : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ ((U.ι ''ᵁ V₀ : X.Opens) : Set X)).Nonempty →
      D.coeff Γ = 0 :=
    hDD D le_sup_left
  have hD' : ∀ Γ : MMP.Mori.PrimeDivisor X,
      (Γ.support ∩ ((U.ι ''ᵁ V₀ : X.Opens) : Set X)).Nonempty →
      D'.coeff Γ = 0 :=
    hDD D' le_sup_right
  let ψU : (RationalFunctions X)ˣ :=
    ⟨psi e V₀ hV₀ hD, psi e.symm V₀ hV₀ hD', funext fun Z => by
      rw [Pi.mul_apply, mul_comm]; exact psi_mul e V₀ hV₀ hD hD' Z,
      funext fun Z => psi_mul e V₀ hV₀ hD hD' Z⟩
  have hL1 := phi_apply_eq e V₀ hV₀ hD
  have hL1' := phi_apply_eq e.symm V₀ hV₀ hD'
  have h1 := ord_ge_of_phi hU e ψU hL1
  have h2 := ord_ge_of_phi hU e.symm ψU⁻¹ hL1'
  refine ⟨ψU, ?_⟩
  ext Γ
  have a1 := h1 Γ
  have a2 := h2 Γ
  rw [PrimeDivisor.ord_inv] at a2
  rw [coeff_principalDivisor, DivisorWithCoeffs.coeff_sub]
  omega

/-- Over a perfect field, the generic point of every prime divisor of a normal variety lies in its
smooth locus. -/
theorem genericPoint_mem_smoothLocus {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] {f : X ⟶ Spec (.of k)}
    (hf : MMP.Mori.IsVariety k f) (Γ : MMP.Mori.PrimeDivisor X) :
    Γ.genericPoint ∈ smoothLocus f := by
  have : LocallyOfFiniteType f := hf.toLocallyOfFiniteType
  have h := congrArg (Γ.genericPoint ∈ ·) (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k f)
  have hreg : IsRegularLocalRing (X.presheaf.stalk Γ.genericPoint) := by
    have := Γ.isDiscreteValuationRing_localRing
    exact (inferInstance : IsRegularLocalRing Γ.localRing)
  have hs : Γ.genericPoint ∈ {x : X | InfinitesimalLifting.SmoothAt f x} := h.mpr hreg
  rw [smoothLocus_eq_smoothLocus]
  exact Scheme.Hom.mem_smoothLocus.mpr
    (InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f _ hs)

end MMP.Threefold.Mori.CanonUniq

namespace MMP.Threefold.Mori

section Notation

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **`K_X` is well defined up to linear equivalence.** Over a perfect field `k`, any two
canonical divisors `K, K'` of a normal variety `X` are linearly equivalent. -/
@[mmp "lem_km0_canonical_divisor_unique_up_to_linear_equivalence"]
theorem linearlyEquivalent_of_isCanonicalDivisor [PerfectField k] (f : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] (hX : IsNormalVariety k f)
    {n n' : ℕ} {K K' : Divisor X} (hK : K.IsCanonicalDivisor f n)
    (hK' : K'.IsCanonicalDivisor f n') : K.LinearlyEquivalent K' := by
  haveI : IsIntegral X := hX.1.toIsIntegral
  obtain rfl : n = n' := by exact_mod_cast hK.1.symm.trans hK'.1
  exact CanonUniq.linearlyEquivalent_of_iso (U := smoothLocus f)
    (MMP.Positivity.PrimeDivisor.genericPoint_mem_smoothLocus hX) (hK.iso ≪≫ hK'.iso.symm)

end Notation

end MMP.Threefold.Mori

namespace MMP.Threefold.Mori

section Klt

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)}

/-- A non-exceptional divisor over a normal variety `X` has the valuation of a prime divisor
of `X`. -/
theorem exists_primeDivisor_valuation_eq_of_not_isExceptional (hX : IsNormalVariety k sX)
    (D : DivisorOver k sX) (hD : ¬ D.IsExceptional) :
    ∃ P : MMP.Mori.PrimeDivisor X, D.valuation = (DivisorOver.ofPrimeDivisor k hX P).valuation := by
  by_contra hcon
  push Not at hcon
  have h2 := (MMP.Positivity.DivisorOver.two_le_codimension_center_iff hX D).mpr hcon
  apply hD
  haveI := D.isLocallyNoetherian
  haveI := D.isNormal
  haveI : IsSeparated sX := hX.1.toIsSeparated
  have hsep : IsSeparated (X ↘ ⊤_ Scheme) := by
    have : (X ↘ ⊤_ Scheme) = sX ≫ Limits.terminal.from (Spec (.of k)) := Subsingleton.elim _ _
    rw [this]
    infer_instance
  unfold DivisorOver.IsExceptional
  rw [MMP.Positivity.isExceptional_toRationalMap_iff]
  have hc : Closeds.closure (D.f '' (D.E.idealSheaf.support : Set D.Y)) =
      ⟨(D.center : Set X), D.center.isClosed⟩ := by
    refine Closeds.ext ?_
    rw [Closeds.coe_closure]
    exact D.coe_center.symm
  rw [hc]
  change 2 ≤ closedsCodimension (T := X) ⟨(D.center : Set X), D.center.isClosed⟩
  rw [closedsCodimension_coe]
  exact h2

variable [IsAlgClosed k] [CharZero k] {n : ℕ} {K : Divisor X} {Δ : QDivisor X}

/-- **A klt pair with effective boundary is dlt, with `Z = X`.** If `(X, Δ)` is klt and `Δ` is
effective, then `(X, Δ)` is dlt, and `a(E, X, Δ) > -1` for every divisor `E` over `X` (so `Z = X`
satisfies the conditions of the definition). -/
@[mmp "lem_km2b_klt_effective_boundary_is_dlt"]
theorem IsKltPair.isDltPair (h : IsKltPair sX n K Δ) (hΔ : Δ.IsEffective) :
    IsDltPair sX n K Δ ∧
      ∀ (D : DivisorOver k sX) (a : ℚ), IsDiscrepancy sX n K Δ D a → -1 < a := by
  have hco : ∀ P : MMP.Mori.PrimeDivisor X, Δ.coeff P < 1 := roundDown_nonpos_iff.mp h.2.2
  have key : ∀ (D : DivisorOver k sX) (a : ℚ), IsDiscrepancy sX n K Δ D a → -1 < a := by
    intro D a ha
    by_cases hE : D.IsExceptional
    · have h3 : ((-1 : ℝ) : EReal) < ((a : ℝ) : EReal) := by
        simpa using lt_of_lt_of_le h.2.1 (discrep_le hE ha)
      exact_mod_cast EReal.coe_lt_coe_iff.mp h3
    · obtain ⟨P, hv⟩ := exists_primeDivisor_valuation_eq_of_not_isExceptional h.1.1 D hE
      obtain ⟨hX, hK, m, hm, hcart, U, hU, τ, hτ, hmτ⟩ := ha
      have hn : topologicalKrullDim X = n := hK.topologicalKrullDim_eq
      rw [ModelIndependence.ordPullback_eq_of_valuation_eq hX hn hv τ,
        DivisorOver.ordPullback_ofPrimeDivisor hX hn P τ] at hmτ
      have hx : D.f D.E.genericPoint = P.genericPoint :=
        MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hX.1 hv
      have hPU : (P.support ∩ (U : Set X)).Nonempty := by
        refine ⟨P.genericPoint, ?_, hx ▸ hU⟩
        rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
        exact subset_closure rfl
      have e := hτ.2 P hPU
      have hm0 : (m : ℚ) ≠ 0 := by positivity
      have : a = -Δ.coeff P := by
        apply mul_left_cancel₀ hm0
        linear_combination hmτ + e
      rw [this]
      linarith [hco P]
  refine ⟨⟨h.1, fun P => ⟨hΔ P, (hco P).le⟩, ⊥, bot_le, ?_, fun D a _ ha => key D a ha⟩, key⟩
  exact ⟨fun E _ => (E.genericPoint.2 : False).elim, fun x => (x.2 : False).elim⟩

end Klt

end MMP.Threefold.Mori

namespace MMP.Threefold.Mori.OpenRestriction

/-- For an open immersion `j`, the germ at `j v` of a section over `j ''ᵁ U` followed by the
stalk map of `j` is `j^♯` followed by the germ at `v`. -/
theorem germ_comp_stalkMap_openImmersion {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (U : V.Opens) (v : V) (hv : v ∈ U) (hx : j v ∈ j ''ᵁ U) :
    X.presheaf.germ (j ''ᵁ U) (j v) hx ≫ j.stalkMap v =
      (j.appIso U).hom ≫ V.presheaf.germ U v hv := by
  have h1 := Scheme.Hom.germ_stalkMap j (j ''ᵁ U) v hx
  rw [h1, Scheme.Hom.appIso_hom, Category.assoc]
  congr 1
  rw [V.presheaf.germ_res]

/-- The stalk of the pull-back of an ideal sheaf along an open immersion `j` is the image of the
stalk under the isomorphism `j^♯`. -/
theorem stalk_comap_eq_map {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (v : V) :
    IdealSheafData.stalk (I.comap j) v =
      Ideal.map (j.stalkMap v).hom (IdealSheafData.stalk I (j v)) := by
  obtain ⟨U, hU, hvU, -⟩ := exists_isAffineOpen_mem_and_subset (X := V) (x := v) (U := ⊤) trivial
  have hx : j v ∈ j ''ᵁ U := ⟨v, hvU, rfl⟩
  rw [IdealSheafData.stalk_eq_map_germ (I.comap j) v ⟨U, hU⟩ hvU,
    IdealSheafData.stalk_eq_map_germ I (j v) ⟨j ''ᵁ U, hU.image_of_isOpenImmersion j⟩ hx,
    Ideal.map_map, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have h := congrArg CommRingCat.Hom.hom (germ_comp_stalkMap_openImmersion j U v hvU hx)
  simp only [CommRingCat.hom_comp] at h
  rw [h, ← Ideal.map_map]
  congr 1
  exact (Ideal.map_comap_of_equiv (j.appIso U).commRingCatIsoToRingEquiv).symm

/-- Pulling back the ideal sheaf of the prime divisor of `X` induced by `E'` along the open
immersion `j` gives the ideal sheaf of `E'`. -/
theorem idealSheaf_comap_primeDivisorMap {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (E' : MMP.Mori.PrimeDivisor V) :
    (OpenWeilRestriction.primeDivisorMap j E').idealSheaf.comap j = E'.idealSheaf := by
  have h1 : E'.idealSheaf = Stacks.Chow.integralComponentAt E'.genericPoint :=
    (Stacks.Chow.integralComponentAt_genericPointOf E'.idealSheaf E'.integral).symm
  have h2 : (OpenWeilRestriction.primeDivisorMap j E').idealSheaf =
      Stacks.Chow.integralComponentAt (j E'.genericPoint) := rfl
  rw [h2, h1]
  exact Stacks.Chow.comap_integralComponentAt_of_isOpenImmersion j _

/-- `j v` lies on the prime divisor of `X` induced by `E'` if and only if `v` lies on `E'`. -/
theorem mem_support_primeDivisorMap_iff {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (E' : MMP.Mori.PrimeDivisor V) (v : V) :
    j v ∈ (OpenWeilRestriction.primeDivisorMap j E').support ↔ v ∈ E'.support := by
  have h : j v ∈ (OpenWeilRestriction.primeDivisorMap j E').support ↔
      v ∈ ((OpenWeilRestriction.primeDivisorMap j E').idealSheaf.comap j).support := by
    simp only [Scheme.IdealSheafData.support_comap]
    rfl
  rw [h, idealSheaf_comap_primeDivisorMap]
  rfl

/-- A prime divisor of `X` meeting the image of the open immersion `j` is induced by a prime
divisor of `V`. -/
theorem exists_primeDivisorMap_eq_of_mem_support {V X : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (E : MMP.Mori.PrimeDivisor X) (v : V) (hv : j v ∈ E.support) :
    ∃ E' : MMP.Mori.PrimeDivisor V, OpenWeilRestriction.primeDivisorMap j E' = E := by
  have := (OpenWeilRestriction.mem_range_primeDivisorMap_iff j E).mpr
  apply this
  rw [PrimeDivisor.support_eq_closure] at hv
  have hs : E.genericPoint ⤳ j v := specializes_iff_mem_closure.mpr hv
  exact hs.mem_open j.isOpenEmbedding.isOpen_range ⟨v, rfl⟩

/-- The prime divisors of the restriction of `D` to `V` through `v`, as those of `D` through
`j v`. -/
def sncIndexEquiv {R : Type*} [Zero R] {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (D : MMP.Mori.DivisorWithCoeffs R X) (v : V) :
    {E' : MMP.Mori.PrimeDivisor V //
        E' ∈ (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) D
          (OpenWeilRestriction.primeDivisorMap_injective j).injOn).support ∧ v ∈ E'.support} ≃
      {E : MMP.Mori.PrimeDivisor X // E ∈ D.support ∧ j v ∈ E.support} :=
  Equiv.ofBijective
    (fun E' => ⟨OpenWeilRestriction.primeDivisorMap j E'.1, by
      refine ⟨?_, (mem_support_primeDivisorMap_iff j E'.1 v).mpr E'.2.2⟩
      have := E'.2.1
      simpa [Finsupp.mem_support_iff] using this⟩)
    ⟨fun a b h => Subtype.ext
        (OpenWeilRestriction.primeDivisorMap_injective j (congrArg Subtype.val h)), by
      rintro ⟨E, hE1, hE2⟩
      obtain ⟨E', rfl⟩ := exists_primeDivisorMap_eq_of_mem_support j E v hE2
      exact ⟨⟨E', by simpa [Finsupp.mem_support_iff] using hE1,
        (mem_support_primeDivisorMap_iff j E' v).mp hE2⟩, rfl⟩⟩

/-- `sncIndexEquiv j D v` sends `E'` to the prime divisor of `X` it induces. -/
theorem sncIndexEquiv_apply {R : Type*} [Zero R] {V X : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (D : MMP.Mori.DivisorWithCoeffs R X) (v : V) (E') :
    (sncIndexEquiv j D v E').1 = OpenWeilRestriction.primeDivisorMap j E'.1 := rfl

/-- A ring isomorphism `φ : A ≃+* B` of local rings carries a regular system of parameters of `A`
generating the ideals `I s` to one of `B` generating the ideals `I' s' = φ (I (e s'))`. -/
theorem snc_data_transfer {A B S S' : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] (φ : A ≃+* B) (e : S' ≃ S) (I : S → Ideal A) (I' : S' → Ideal B)
    (hI : ∀ s', I' s' = (I (e s')).map φ) :
    (∃ (n : ℕ) (z : Fin n → A) (j : S → Fin n), IsRegularSystemOfParameters z ∧
      Function.Injective j ∧ ∀ s, I s = Ideal.span {z (j s)}) →
    (∃ (n : ℕ) (z : Fin n → B) (j : S' → Fin n), IsRegularSystemOfParameters z ∧
      Function.Injective j ∧ ∀ s', I' s' = Ideal.span {z (j s')}) := by
  rintro ⟨n, z, j, ⟨hz1, hz2⟩, hj, hI'⟩
  refine ⟨n, fun i => φ (z i), fun s' => j (e s'), ⟨?_, ?_⟩, hj.comp e.injective, fun s' => ?_⟩
  · have h1 : Ideal.span (Set.range fun i => φ (z i)) =
        Ideal.map φ (Ideal.span (Set.range z)) := by
      rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [h1, hz1]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv φ)
  · rw [← hz2]
    exact (ringKrullDim_eq_of_ringEquiv φ).symm
  · rw [hI, hI', Ideal.map_span]; simp

/-- Mapping an ideal along a ring isomorphism and then along its inverse gives the ideal back. -/
theorem map_symm_map {A B : Type*} [CommRing A] [CommRing B] (φ : A ≃+* B) (J : Ideal A) :
    Ideal.map φ.symm (Ideal.map φ J) = J :=
  Ideal.map_of_equiv φ

/-- The stalk isomorphism of an open immersion. -/
def stalkEquivOfOpenImmersion {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (v : V) :
    X.presheaf.stalk (j v) ≃+* V.presheaf.stalk v :=
  letI := IsOpenImmersion.instIsIsoCommRingCatStalkMap j v
  (asIso (j.stalkMap v)).commRingCatIsoToRingEquiv

/-- Mapping an ideal along `stalkEquivOfOpenImmersion j v` is mapping it along the stalk map
of `j`. -/
theorem stalkEquivOfOpenImmersion_coe {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (v : V) (J : Ideal (X.presheaf.stalk (j v))) :
    Ideal.map (stalkEquivOfOpenImmersion j v) J = Ideal.map (j.stalkMap v).hom J := rfl

/-- The local snc condition at `v` for the restriction of `D` along an open immersion `j` is the
local snc condition of `D` at `j v`. -/
theorem sncStalk_restrict_iff {R : Type*} [Zero R] {V X : Scheme.{u}} (j : V ⟶ X)
    [IsOpenImmersion j] (D : MMP.Mori.DivisorWithCoeffs R X) (v : V) :
    (∃ (n : ℕ) (z : Fin n → V.presheaf.stalk v) (jj : {E' : MMP.Mori.PrimeDivisor V //
        E' ∈ (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) D
          (OpenWeilRestriction.primeDivisorMap_injective j).injOn).support ∧
          v ∈ E'.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf v = Ideal.span {z (jj E)}) ↔
    (∃ (n : ℕ) (z : Fin n → X.presheaf.stalk (j v)) (jj : {E : MMP.Mori.PrimeDivisor X //
        E ∈ D.support ∧ j v ∈ E.support} → Fin n),
      IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
        ∀ E, IdealSheafData.stalk E.1.idealSheaf (j v) = Ideal.span {z (jj E)}) := by
  have key : ∀ E' : {E' : MMP.Mori.PrimeDivisor V //
        E' ∈ (Finsupp.comapDomain (OpenWeilRestriction.primeDivisorMap j) D
          (OpenWeilRestriction.primeDivisorMap_injective j).injOn).support ∧ v ∈ E'.support},
      IdealSheafData.stalk E'.1.idealSheaf v =
        Ideal.map (stalkEquivOfOpenImmersion j v)
          (IdealSheafData.stalk (sncIndexEquiv j D v E').1.idealSheaf (j v)) := by
    intro E'
    rw [stalkEquivOfOpenImmersion_coe, ← stalk_comap_eq_map, sncIndexEquiv_apply,
      idealSheaf_comap_primeDivisorMap]
  constructor
  · intro h
    refine snc_data_transfer (stalkEquivOfOpenImmersion j v).symm (sncIndexEquiv j D v).symm
      _ _ ?_ h
    intro E
    rw [key, Equiv.apply_symm_apply, map_symm_map]
  · exact snc_data_transfer (stalkEquivOfOpenImmersion j v) (sncIndexEquiv j D v) _ _ key

/-- For an open immersion `j : V ⟶ X` and an ideal sheaf `I` on `X`, the subscheme of the pull-back
of `I` is an open subscheme of the subscheme of `I`, compatibly with `j`, whose image consists of
the points lying over the image of `j`. -/
theorem exists_openImmersion_comap_subscheme {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) :
    ∃ k : (I.comap j).subscheme ⟶ I.subscheme, IsOpenImmersion k ∧
      (I.comap j).subschemeι ≫ j = k ≫ I.subschemeι ∧
      ∀ z : I.subscheme, I.subschemeι z ∈ Set.range j → z ∈ Set.range k := by
  refine ⟨(I.comapIso j).hom ≫ Limits.pullback.snd j I.subschemeι, inferInstance, ?_, ?_⟩
  · rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Limits.pullback.condition,
      Category.assoc]
  · rintro z ⟨v, hv⟩
    obtain ⟨t, -, ht⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := j) (g := I.subschemeι) v z hv
    refine ⟨(I.comapIso j).inv t, ?_⟩
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (I.comapIso j).inv (I.comapIso j).hom]
    simp [ht]

/-- A component of the restriction of a divisor along an open immersion `j` is smooth over `Y`
exactly when the corresponding prime divisor of `X` is smooth at the points over the image of
`j`. -/
theorem isSmoothScheme_comap_iff {V X Y : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j]
    (g : X ⟶ Y) (I : X.IdealSheafData) (J : V.IdealSheafData) (hJ : I.comap j = J)
    [LocallyOfFinitePresentation (I.subschemeι ≫ g)] :
    IsSmoothScheme (J.subschemeι ≫ j ≫ g) ↔
      ∀ z : I.subscheme, I.subschemeι z ∈ Set.range j → z ∈ (I.subschemeι ≫ g).smoothLocus := by
  subst hJ
  obtain ⟨k, hk, hcomm, hrange⟩ := exists_openImmersion_comap_subscheme j I
  have e : (I.comap j).subschemeι ≫ j ≫ g = k ≫ I.subschemeι ≫ g := by
    rw [← Category.assoc, hcomm, Category.assoc]
  rw [e]
  have h2 : (k ≫ I.subschemeι ≫ g).smoothLocus = k ⁻¹ᵁ (I.subschemeι ≫ g).smoothLocus :=
    (Scheme.Hom.preimage_smoothLocus_eq k _).symm
  rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, h2]
  constructor
  · intro h z hz
    obtain ⟨z', rfl⟩ := hrange z hz
    exact (h ▸ trivial : z' ∈ k ⁻¹ᵁ (I.subschemeι ≫ g).smoothLocus)
  · intro h
    rw [eq_top_iff]
    intro z' _
    apply h
    exact ⟨(I.comap j).subschemeι z', congrArg (fun f => f z') hcomm⟩

/-- The local snc condition of a divisor at a point. -/
def SNCStalk {R : Type*} [Zero R] {X : Scheme.{u}} (D : MMP.Mori.DivisorWithCoeffs R X)
    (x : X) : Prop :=
  ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x) (jj : {E : MMP.Mori.PrimeDivisor X //
      E ∈ D.support ∧ x ∈ E.support} → Fin n),
    IsRegularSystemOfParameters z ∧ Function.Injective jj ∧
      ∀ E, IdealSheafData.stalk E.1.idealSheaf x = Ideal.span {z (jj E)}

/-- **Being snc is local on the base for restrictions to open subsets.** If the restriction of `D`
to each `V i` is snc over `g`, and the `V i` cover `U₀`, then so is its restriction to `U₀`. -/
theorem isSNC_restrictOpen_of_cover {R : Type*} [Zero R] {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ E : MMP.Mori.PrimeDivisor X, LocallyOfFinitePresentation (E.idealSheaf.subschemeι ≫ g)]
    {ι : Type*} (V : ι → X.Opens) (U₀ : X.Opens) (hcov : ∀ x ∈ U₀, ∃ i, x ∈ V i)
    (D : MMP.Mori.DivisorWithCoeffs R X)
    (h : ∀ i, (D.restrictOpen (V i)).IsSNC ((V i).ι ≫ g)) :
    (D.restrictOpen U₀).IsSNC (U₀.ι ≫ g) := by
  refine ⟨fun E₀ hE₀ => ?_, fun x => ?_⟩
  · have hDE : D (OpenWeilRestriction.primeDivisorMap U₀.ι E₀) ≠ 0 :=
      (Finsupp.mem_support_iff.mp hE₀ :)
    refine (isSmoothScheme_comap_iff U₀.ι g (OpenWeilRestriction.primeDivisorMap U₀.ι E₀).idealSheaf
      E₀.idealSheaf (idealSheaf_comap_primeDivisorMap U₀.ι E₀)).mpr ?_
    rintro z ⟨u, hu⟩
    have hxU : (OpenWeilRestriction.primeDivisorMap U₀.ι E₀).idealSheaf.subschemeι z ∈ U₀ := by
      rw [← hu]
      exact u.2
    obtain ⟨i, hi⟩ := hcov _ hxU
    have hEsupp : (OpenWeilRestriction.primeDivisorMap U₀.ι E₀).idealSheaf.subschemeι z ∈
        (OpenWeilRestriction.primeDivisorMap U₀.ι E₀).support := by
      have hr : (OpenWeilRestriction.primeDivisorMap U₀.ι E₀).idealSheaf.subschemeι z ∈
          Set.range (OpenWeilRestriction.primeDivisorMap U₀.ι E₀).idealSheaf.subschemeι :=
        ⟨z, rfl⟩
      rwa [Scheme.IdealSheafData.range_subschemeι] at hr
    obtain ⟨E', hE'⟩ := exists_primeDivisorMap_eq_of_mem_support (V i).ι
      (OpenWeilRestriction.primeDivisorMap U₀.ι E₀) (⟨_, hi⟩ : V i) hEsupp
    have hE'supp : E' ∈ (D.restrictOpen (V i)).support := by
      rw [Finsupp.mem_support_iff]
      change D (OpenWeilRestriction.primeDivisorMap (V i).ι E') ≠ 0
      rwa [hE']
    have hsm := (h i).1 E' hE'supp
    exact (isSmoothScheme_comap_iff (V i).ι g
      (OpenWeilRestriction.primeDivisorMap U₀.ι E₀).idealSheaf E'.idealSheaf
      (by rw [← hE']; exact idealSheaf_comap_primeDivisorMap _ E')).mp hsm z ⟨⟨_, hi⟩, rfl⟩
  · obtain ⟨i, hi⟩ := hcov (U₀.ι x) x.2
    let w : V i := ⟨U₀.ι x, hi⟩
    exact (sncStalk_restrict_iff U₀.ι D x).mpr ((sncStalk_restrict_iff (V i).ι D w).mp ((h i).2 w))

/-- The generic point of a prime divisor is not the generic point of the integral scheme. -/
theorem genericPoint_ne_genericPoint_primeDivisor {X : Scheme.{u}} [IsIntegral X]
    (E : MMP.Mori.PrimeDivisor X) : E.genericPoint ≠ genericPoint X := by
  intro h
  have h1 := E.coheight_genericPoint
  rw [h] at h1
  have : IsMax (genericPoint X) := fun y _ => genericPoint_specializes y
  rw [coheight_eq_zero.mpr this] at h1
  simp at h1

/-- The generic point of an integral scheme lies on no prime divisor. -/
theorem genericPoint_notMem_support {X : Scheme.{u}} [IsIntegral X]
    (E : MMP.Mori.PrimeDivisor X) : genericPoint X ∉ E.support := by
  intro hη
  rw [PrimeDivisor.support_eq_closure] at hη
  have h1 : E.genericPoint ⤳ genericPoint X := specializes_iff_mem_closure.mpr hη
  exact genericPoint_ne_genericPoint_primeDivisor E
    (h1.antisymm (genericPoint_specializes _)).eq

/-- Over a perfect field, the generic point of an integral, locally noetherian scheme locally of
finite type lies in its smooth locus. -/
theorem genericPoint_mem_smoothLocus' {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    [IsIntegral X] {f : X ⟶ Spec (.of k)} [LocallyOfFiniteType f] [IsLocallyNoetherian X] :
    genericPoint X ∈ smoothLocus f := by
  have h := congrArg (genericPoint X ∈ ·) (AlgebraicGeometry.smoothAt_locus_eq_regular_locus k f)
  have hreg : IsRegularLocalRing (X.presheaf.stalk (genericPoint X)) :=
    (inferInstance : IsRegularLocalRing X.functionField)
  have hs : genericPoint X ∈ {x : X | InfinitesimalLifting.SmoothAt f x} := h.mpr hreg
  rw [smoothLocus_eq_smoothLocus]
  exact Scheme.Hom.mem_smoothLocus.mpr
    (InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f _ hs)

end MMP.Threefold.Mori.OpenRestriction

namespace MMP.Threefold.Mori.CrepantAux

variable {X Y : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
  [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] {f : Y ⟶ X} [IsDominant f]

/-- **The coefficient of a pull-back is the order of the pulled-back local equation**: if `φ` is
a local equation of the Cartier divisor `C` near `f(η_E)`, then `coeff_E(f^*C) = v_E(f^*φ)`. -/
private theorem coeff_isPullback_eq_ord_evalFF {C : MMP.Mori.Divisor X}
    {hC : ∀ Z : irreducibleComponents Y, f (MMP.Mori.componentGenericPoint Y Z) ∉ C.supp}
    {C' : MMP.Mori.Divisor Y} (h : C.IsPullback f hC C') {U : X.Opens}
    {φ : (MMP.Mori.RationalFunctions X)ˣ} (hφ : C.IsLocalEquation U φ) (E : MMP.Mori.PrimeDivisor Y)
    (hU : f E.genericPoint ∈ U) (Z : irreducibleComponents X) :
    C'.coeff E = Y.ord (functionFieldMap f
      (MMP.Threefold.Mori.Helpers.evalFF Z (φ : MMP.Mori.RationalFunctions X))) E.genericPoint := by
  classical
  have hE : (E.support ∩ f ⁻¹ᵁ U).Nonempty := (E.genericPoint_mem_iff (f ⁻¹ᵁ U)).mp hU
  rw [h U φ hφ E hE]
  have hZp := E.map_componentGenericPoint_mem f hE
  have hW := MMP.Mori.mem_pointComponent (f (MMP.Mori.componentGenericPoint Y E.component))
  obtain ⟨a, ha⟩ := hφ.exists_unit_stalk hZp (hC _) hW
  rw [MMP.Mori.pullbackComponent_eq hC hφ hZp hW a ha]
  set u := Units.map (f.stalkMap (MMP.Mori.componentGenericPoint Y E.component)).hom.toMonoidHom a
  let ψ : (MMP.Mori.RationalFunctions Y)ˣ :=
    (MMP.Mori.RationalFunctions.unitsEquiv Y).symm (Function.update 1 E.component u)
  have hψZ : (ψ : MMP.Mori.RationalFunctions Y) E.component = u := by
    simp [ψ, MMP.Mori.RationalFunctions.unitsEquiv]
  have h1 : E.ordUnit u = E.ord ψ := by
    rw [MMP.Mori.PrimeDivisor.ord_eq_ordUnit]
    congr 1
    exact (Units.ext hψZ).symm
  rw [h1, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
  congr 1
  obtain rfl : Z = MMP.Mori.pointComponent (f (MMP.Mori.componentGenericPoint Y E.component)) :=
    Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
  change (Y.presheaf.stalkSpecializes _).hom ((ψ : MMP.Mori.RationalFunctions Y) E.component) =
    functionFieldMap f ((X.presheaf.stalkSpecializes _).hom
      ((φ : MMP.Mori.RationalFunctions X) _))
  rw [hψZ, ← ha]
  change _ = functionFieldMap f ((MMP.Mori.stalkToRationalFunctions X hW ≫
    X.presheaf.stalkSpecializes _).hom a)
  rw [MMP.Mori.stalkToRationalFunctions, TopCat.Presheaf.stalkSpecializes_comp]
  exact (MMP.Mori.functionFieldMap_algebraMap_stalk f
    (MMP.Mori.componentGenericPoint Y E.component) a.val).symm

end MMP.Threefold.Mori.CrepantAux

namespace MMP.Threefold.Mori

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}
  {Δ : QDivisor X}

/-- **The crepant boundary is characterised by the pull-back formula.** Let `(X, Δ)` be a pair,
`f : Y ⟶ X` a proper birational morphism from a normal variety, `K_Y` a canonical divisor with
`f_* K_Y = K_X`, and `Δ'` a `ℚ`-divisor on `Y` with `K_Y + Δ' = f^*(K_X + Δ)`. Then `Δ'` is the
crepant boundary of `(X, Δ)` on `Y`. -/
@[mmp "lem_km2b_crepant_boundary_characterization"]
theorem isCrepantBoundary_of_add_eq_pullback (hΔ : IsPairWith sX n K Δ) {Y : Scheme.{u}}
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : Y ⟶ X) [IsProper f]
    (hY : IsNormalVariety k (f ≫ sX)) (hf : IsBirationalMorphism f) {KY : Divisor Y}
    (hKY : KY.IsCanonicalDivisor (f ≫ sX) n)
    (hpush : RationalMap.transformDivisor (X := Y) f.toRationalMap KY = K) {Δ' : QDivisor Y}
    (hpull : ∃ hB : ∀ Z : irreducibleComponents Y,
        f (componentGenericPoint Y Z) ∉ (Divisor.toQDivisor K + Δ).supp,
      (Divisor.toQDivisor K + Δ).IsPullback f hB (Divisor.toQDivisor KY + Δ')) :
    IsCrepantBoundary sX n K Δ f hY hf Δ' := by
  intro F
  obtain ⟨hB, hpullQ⟩ := hpull
  obtain ⟨hXv, hK, hQ⟩ := hΔ
  obtain ⟨m, hm0, hmCD⟩ := hQ.exists_pos
  obtain ⟨C, hC, hCart⟩ := hmCD
  obtain ⟨Dp, hDp, hCp⟩ := hpullQ m hm0 C hC hCart
  have : CompactSpace X := by
    have := hXv.1
    exact QuasiCompact.compactSpace_of_compactSpace sX
  have : CompactSpace Y := by
    have := hY.1
    exact QuasiCompact.compactSpace_of_compactSpace (f ≫ sX)
  have : LocallyOfFiniteType sX := hXv.1.toLocallyOfFiniteType
  have : LocallyOfFiniteType (f ≫ sX) := hY.1.toLocallyOfFiniteType
  have hn := hK.topologicalKrullDim_eq
  set D : DivisorOver k sX := ⟨Y, f, hY, hf, F⟩
  haveI : IsDominant f := D.isDominant
  obtain ⟨ω, hω0, hωK, hωKY⟩ :=
    MMP.Positivity.exists_divisorOfForm_eq_of_transformDivisor_eq hXv hY hf hK hKY hpush
  obtain ⟨b, N', hb0⟩ := D.exists_ordPullback_eq hXv hn
  have hb : ∀ (m : ℤ) (τ : RationalPluriForms sX n m), τ ≠ 0 → D.ordPullback τ =
      Y.ord (functionFieldMap f ((ZTensorPower.basis b m).repr τ ())) F.genericPoint + m * N' :=
    hb0
  let := functionFieldAlgebra sX
  have hd := toNat_trdeg_functionField_of_topologicalKrullDim_eq (sX := sX) hn
  obtain ⟨U, hxU, φ, hφ⟩ := hCart (f F.genericPoint)
  let Z0 : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]; simp⟩
  set c := (ZTensorPower.basis b 1).repr ω () with hc_def
  have hc : c ≠ 0 := repr_ne_zero_of_ne_zero b hω0
  set g := MMP.Threefold.Mori.Helpers.evalFF Z0 (φ : RationalFunctions X)
  have hg : g ≠ 0 := (φ.isUnit.map _).ne_zero
  set c'' : X.functionField := c ^ (m : ℤ) * g⁻¹ with hc''_def
  have hc'' : c'' ≠ 0 := mul_ne_zero (zpow_ne_zero _ hc) (inv_ne_zero hg)
  let τ : RationalPluriForms sX n m := c'' • ZTensorPower.basis b (m : ℤ) ()
  have hτr : (ZTensorPower.basis b (m : ℤ)).repr τ () = c'' := by simp [τ]
  have hτ0 : τ ≠ 0 := smul_ne_zero hc'' ((ZTensorPower.basis b (m : ℤ)).ne_zero ())
  have hKcoeff : ∀ Γ : MMP.Mori.PrimeDivisor X, ∃ NΓ : ℤ,
      (K.coeff Γ : ℤ) = X.ord c Γ.genericPoint + NΓ ∧
      (Γ.ordForm τ : ℤ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint + m * NΓ := by
    intro Γ
    obtain ⟨NΓ, hNΓ⟩ := Γ.exists_ordForm_eq_ord_add_mul hd b
    refine ⟨NΓ, ?_, ?_⟩
    · rw [← hωK, coeff_divisorOfForm, hNΓ 1 ω hω0]
      simp [hc_def]
    · rw [hNΓ _ τ hτ0, hτr, hc''_def, Scheme.ord_mul (zpow_ne_zero _ hc) (inv_ne_zero hg),
        MMP.Mori.ord_zpow _ hc]
      have := Scheme.ord_mul (X := X) (x := Γ.genericPoint) hg (inv_ne_zero hg)
      rw [mul_inv_cancel₀ hg] at this
      have h1 : X.ord (1 : X.functionField) Γ.genericPoint = 0 := by
        have := Scheme.ord_mul (X := X) (x := Γ.genericPoint) (one_ne_zero (α := X.functionField))
          one_ne_zero
        rw [mul_one] at this
        omega
      omega
  have hgord : ∀ Γ : MMP.Mori.PrimeDivisor X, (Γ.support ∩ U).Nonempty →
      X.ord g Γ.genericPoint = C.coeff Γ := by
    intro Γ hΓ
    rw [hφ Γ hΓ, MMP.Threefold.Mori.Helpers.ord_eq_scheme_ord]
    have : Γ.component = Z0 :=
      Subsingleton.elim (h := MMP.Threefold.Mori.Helpers.subsingleton_irreducibleComponents) _ _
    rw [this]
  have hCq : ∀ Γ : MMP.Mori.PrimeDivisor X, (C.coeff Γ : ℚ) = m * (K.coeff Γ + Δ.coeff Γ) := by
    intro Γ
    have := congrArg (fun D : QDivisor X => D.coeff Γ) hC
    rw [mul_add]
    simpa [zsmul_eq_mul] using this
  have hgen : GeneratesOn Δ m U τ := by
    refine ⟨hτ0, fun Γ hΓ => ?_⟩
    obtain ⟨NΓ, h1, h2⟩ := hKcoeff Γ
    have h3 := hgord Γ hΓ
    have h1' : (K.coeff Γ : ℚ) = X.ord c Γ.genericPoint + NΓ := by exact_mod_cast h1
    have h2' : (Γ.ordForm τ : ℚ) = m * X.ord c Γ.genericPoint - X.ord g Γ.genericPoint
        + m * NΓ := by exact_mod_cast h2
    have h3' : (X.ord g Γ.genericPoint : ℚ) = C.coeff Γ := by exact_mod_cast h3
    linear_combination h2' - hCq Γ - h3' - (m : ℚ) * h1'
  have hKY : KY.coeff F = Y.ord (functionFieldMap f c) F.genericPoint + N' := by
    have h := hb 1 ω hω0
    have e : D.ordPullback ω = KY.coeff F := by
      rw [← hωKY, coeff_divisorOfForm]
      rfl
    rw [← e, h]
    simp [hc_def]
  have hcoeff : Dp.coeff F = Y.ord (functionFieldMap f g) F.genericPoint :=
    CrepantAux.coeff_isPullback_eq_ord_evalFF hCp hφ F hxU Z0
  have hDpq : (Dp.coeff F : ℚ) = m * (KY.coeff F + Δ'.coeff F) := by
    have := congrArg (fun D : QDivisor Y => D.coeff F) hDp
    rw [mul_add]
    simpa [zsmul_eq_mul] using this
  have hgY : functionFieldMap f g ≠ 0 := (map_ne_zero _).mpr hg
  have hcY : functionFieldMap f c ≠ 0 := (map_ne_zero _).mpr hc
  have hordτ : D.ordPullback τ = m * Y.ord (functionFieldMap f c) F.genericPoint
      - Y.ord (functionFieldMap f g) F.genericPoint + m * N' := by
    rw [hb _ τ hτ0, hτr, hc''_def, map_mul, map_zpow₀, map_inv₀,
      Scheme.ord_mul (zpow_ne_zero _ hcY) (inv_ne_zero hgY), MMP.Mori.ord_zpow _ hcY]
    have := Scheme.ord_mul (X := Y) (x := F.genericPoint) hgY (inv_ne_zero hgY)
    rw [mul_inv_cancel₀ hgY] at this
    have h1 : Y.ord (1 : Y.functionField) F.genericPoint = 0 := by
      have := Scheme.ord_mul (X := Y) (x := F.genericPoint) (one_ne_zero (α := Y.functionField))
        one_ne_zero
      rw [mul_one] at this
      omega
    omega
  refine ⟨hXv, hK, m, hm0, ⟨C, hC, hCart⟩, U, hxU, τ, hgen, ?_⟩
  have e1 : (D.ordPullback τ : ℚ) = m * Y.ord (functionFieldMap f c) F.genericPoint
      - Y.ord (functionFieldMap f g) F.genericPoint + m * N' := by exact_mod_cast hordτ
  have e2 : (KY.coeff F : ℚ) = Y.ord (functionFieldMap f c) F.genericPoint + N' := by
    exact_mod_cast hKY
  have e3 : (Dp.coeff F : ℚ) = Y.ord (functionFieldMap f g) F.genericPoint := by
    exact_mod_cast hcoeff
  rw [e1]
  linear_combination hDpq - e3 + (m : ℚ) * e2

/-- **`a(E, X)` exists** (KM Definition 2.22). Let `X` be a normal variety with `mK_X` Cartier for
some `m > 0` and `(Y, f, E)` an exceptional divisor over `X`. Then there is a number `a(E, X)`
computed as in `MMP.Mori.IsDiscrepancyNoBoundary` from some choice `(m, U, σ)`. That the numbers
computed from any two choices coincide is `MMP.Mori.IsDiscrepancyNoBoundary.eq`, and that they
are `a(E, X, 0)` is `MMP.Threefold.Mori.isDiscrepancyNoBoundary_iff_isDiscrepancy_zero`. -/
@[mmp "lem_km2b_discrepancy_independent_of_index"]
theorem exists_isDiscrepancyNoBoundary (hX : IsNormalVariety k sX)
    (hK : K.IsCanonicalDivisor sX n) (hm : ∃ m : ℕ, 0 < m ∧ ((m : ℤ) • K).IsCartier)
    (D : DivisorOver k sX) (hD : D.IsExceptional) :
    ∃ a : ℚ, IsDiscrepancyNoBoundary sX n K D a := by
  obtain ⟨m, hm0, hmK⟩ := hm
  have hP : IsPair sX (0 : QDivisor X) :=
    ⟨hX, n, K, hK, ⟨m, by omega, by
      rw [add_zero, ← map_zsmul, QDivisor.isCartierDivisor_toQDivisor]; exact hmK⟩⟩
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hP hK D
  exact ⟨a, (isDiscrepancyNoBoundary_iff_isDiscrepancy_zero hD a).mpr ha⟩

/-! **`a(E, X)` is independent of the choices** (KM Definition 2.22): the numbers computed as in
`MMP.Mori.IsDiscrepancyNoBoundary` from any two choices `(m, U, σ)`, `(m', U', σ')` coincide, and
they are the discrepancies `a(E, X, 0)` of the pair `(X, 0)`. -/

attribute [mmp "lem_km2b_discrepancy_independent_of_index"] MMP.Mori.IsDiscrepancyNoBoundary.eq
  isDiscrepancyNoBoundary_iff_isDiscrepancy_zero

/-- **The closed set of a dlt pair may be taken proper.** If `(X, Δ)` is dlt, there is a closed
`Z = X ∖ U ⊊ X` satisfying (1) and (2) of the definition of dlt with `Z ⊆ X ∖ U₀`, where `U₀` is
the union of the opens of `X` that are smooth and on which `Δ` is snc (`U₀ ⊆ U`). -/
@[mmp "lem_km2b_dlt_proper_closed_subset"]
theorem IsDltPair.exists_open_nonempty (h : IsDltPair sX n K Δ) :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ U ≤ smoothLocus sX ∧
      (Δ.restrictOpen U).IsSNC (U.ι ≫ sX) ∧
      (∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
        IsDiscrepancy sX n K Δ D a → -1 < a) ∧
      ∀ V : X.Opens, V ≤ smoothLocus sX → (Δ.restrictOpen V).IsSNC (V.ι ≫ sX) → V ≤ U := by
  obtain ⟨hP, -, U₁, hU₁, hU₁snc, hdisc⟩ := h
  have hX := hP.1
  have : LocallyOfFiniteType sX := hX.1.toLocallyOfFiniteType
  let S : Set X.Opens := {V | V ≤ smoothLocus sX ∧ (Δ.restrictOpen V).IsSNC (V.ι ≫ sX)}
  have hU₁S : U₁ ∈ S := ⟨hU₁, hU₁snc⟩
  have hSle : sSup S ∈ S := by
    refine ⟨sSup_le fun V hV => hV.1, ?_⟩
    refine OpenRestriction.isSNC_restrictOpen_of_cover sX (fun V : S => V.1) (sSup S) ?_ Δ
      fun V => V.2.2
    intro x hx
    obtain ⟨V, hV, hxV⟩ := Opens.mem_sSup.mp hx
    exact ⟨⟨V, hV⟩, hxV⟩
  have hne : ((sSup S : X.Opens) : Set X).Nonempty := by
    let Z : Set X := ⋃ E ∈ Δ.support, (E.support : Set X)
    have hZ : IsClosed Z :=
      (Δ.support.finite_toSet).isClosed_biUnion fun E _ => E.idealSheaf.support.isClosed
    let V : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩ ⊓ smoothLocus sX
    have hηV : genericPoint X ∈ V := by
      refine ⟨?_, OpenRestriction.genericPoint_mem_smoothLocus'⟩
      intro hη
      simp only [Z, Set.mem_iUnion] at hη
      obtain ⟨E, -, hE⟩ := hη
      exact OpenRestriction.genericPoint_notMem_support E hE
    have hVS : V ∈ S := by
      refine ⟨inf_le_right, ?_⟩
      have h0 : Δ.restrictOpen V = 0 := by
        ext W
        by_contra hW
        have hmem : OpenWeilRestriction.primeDivisorMap V.ι W ∈ Δ.support :=
          Finsupp.mem_support_iff.mpr hW
        have hg : (OpenWeilRestriction.primeDivisorMap V.ι W).genericPoint ∈ V := by
          rw [OpenWeilRestriction.genericPoint_primeDivisorMap]
          exact (W.genericPoint).2
        have hg1 : (OpenWeilRestriction.primeDivisorMap V.ι W).genericPoint ∈ Z := by
          simp only [Z, Set.mem_iUnion]
          refine ⟨_, hmem, ?_⟩
          rw [PrimeDivisor.support_eq_closure]
          exact subset_closure rfl
        exact hg.1 hg1
      rw [h0]
      have hsm : IsSmoothScheme (V.ι ≫ sX) := by
        rw [IsSmoothScheme, smoothLocus_eq_smoothLocus, ← Scheme.Hom.preimage_smoothLocus_eq,
          ← smoothLocus_eq_smoothLocus, eq_top_iff]
        intro x _
        exact x.2.2
      exact DivisorWithCoeffs.isSNC_zero_of_isSmoothScheme _ hsm
    exact ⟨_, le_sSup hVS hηV⟩
  have hle : (U₁ : Set X) ⊆ (sSup S : X.Opens) := (le_sSup hU₁S : U₁ ≤ sSup S)
  exact ⟨sSup S, hne, hSle.1, hSle.2,
    fun D a hD ha => hdisc D a (hD.trans (Set.compl_subset_compl.mpr hle)) ha,
    fun V hV hsnc => le_sSup ⟨hV, hsnc⟩⟩

end MMP.Threefold.Mori
